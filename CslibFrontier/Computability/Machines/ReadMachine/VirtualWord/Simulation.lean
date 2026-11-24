/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.ReadMachine.VirtualWord.Evaluator
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible

/-!
# Resuming arbitrary query machines on virtual inputs

The outer machine's encoded state is retained across each translated read. The runtime header
and cursor are loaded once and then preserved. Optional reads distinguish an absent symbol from
`some false`, including past the virtual end. Emission and final-output continuations are those
of the outer machine, without restricting its state type or transition graph.

## Main definitions

* `State`: saved runtime header/cursor paired with the simulated outer state.
* `machine`: uniform header loading and arbitrary outer-machine simulation.
* `symbol`: optional virtual read, distinguishing EOF from a present false bit.

## Main results

* `resume`: exact simulation from any saved outer state with header/cursor preservation.
* `output`: preservation of all emissions and the final output continuation.
* `computableInSpace`: native compiler with an additive saved-state/header/position budget.

This original construction addresses the generic consumer gap in the recomputation argument
for Lemma 3.3, expanded ECCC TR13-047, printed page 6
[GlasserNguyenReitwiessnerSelmanWitek2013]. It does not prepare headers, regenerate answer words,
implement suffix iteration or adaptive-to-tt conversion, or prove Lemma 3.3.
-/

public section

namespace Turing.VirtualWord.Simulation

open MultiTapeTM ComputableInSpace
open QueryMachine (encStateRead)

@[expose] section

/-- Saved runtime header/cursor and unrestricted outer state. -/
@[ext]
structure State (σ : Type) where
  /-- State of the underlying runtime header/bit accessor. -/
  runtime : Runtime.State
  /-- State of the simulated outer query machine. -/
  outer : σ
  deriving DecidableEq

end

variable {σ : Type}

/-- Both the header and the entire outer encoding are charged. -/
enc_structure encState (enc : σ ↪ List Bool) : State σ where
  runtime : Runtime.encState,
  outer : enc

variable (M : QueryMachine σ)

/-- Parameters retained by the initialized runtime accessor. -/
@[expose] def data (s : State σ) : Data := Runtime.decode s.runtime.header.reverse

/-- Restore the outer machine's optional input symbol from one physical tail read. -/
@[expose] def symbol (s : State σ) (b : Option Bool) : Option Bool :=
  if M.query s.outer < Evaluator.width (data s) then
    some (answer ⟨(data s).cut, (data s).suffix, M.query s.outer⟩ (b.getD false))
  else none

/-- One fixed simulator loads the runtime header, then resumes the outer machine. -/
@[expose] def machine : QueryMachine (State σ) where
  init := ⟨Runtime.machine.init, M.init⟩
  query s := if Runtime.machine.halted s.runtime then s.runtime.cursor + M.query s.outer
    else Runtime.machine.query s.runtime
  next := fun (s, b) => if Runtime.machine.halted s.runtime then
      ⟨s.runtime, M.next (s.outer, symbol M s b)⟩
    else ⟨Runtime.machine.next (s.runtime, b), s.outer⟩
  emit := fun (s, b) =>
    if Runtime.machine.halted s.runtime then M.emit (s.outer, symbol M s b) else []
  halted s := Runtime.machine.halted s.runtime && M.halted s.outer
  finish s := M.finish s.outer

/-- Loading never changes the suspended outer state. -/
theorem run_initializing (p : Runtime.Input) {t : ℕ}
    (ht : t ≤ 2 * (encData p.data).length + 2) :
    (machine M).run (Runtime.encInput p) t =
      ⟨Runtime.machine.run (Runtime.encInput p) t, M.init⟩ := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [QueryMachine.run_succ, ih (by omega)]
    have h := (Runtime.first_halt p).2 t (by omega)
    simp only [QueryMachine.step, machine, h, Bool.false_and, Bool.false_eq_true,
      ↓reduceIte, QueryMachine.read, QueryMachine.run_succ]

/-- The loaded simulator queries precisely the unchanged original-input tail. -/
theorem read_loaded (p : Runtime.Input) (s : σ) :
    (machine M).read (Runtime.encInput p) ⟨Evaluator.loaded p, s⟩ = p.original[M.query s]? := by
  change (frame (encData p.data) ++ p.original)[(machine M).query ⟨Evaluator.loaded p, s⟩]? = _
  simp only [machine, Evaluator.loaded, Runtime.machine, Option.isSome_some, ↓reduceIte]
  rw [List.getElem?_append_right (by simp)]
  simp

/-- The translated symbol is the exact optional read, including the virtual end. -/
theorem symbol_loaded (p : Runtime.Input) (hc : p.data.cut ≤ p.original.length) (s : σ) :
    symbol M ⟨Evaluator.loaded p, s⟩ (p.original[M.query s]?) =
      M.read (word p.original p.data.cut p.data.suffix) s := by
  have hd : data ⟨Evaluator.loaded p, s⟩ = p.data := by
    simp only [data, Evaluator.loaded, List.reverse_reverse, Runtime.decode_encData]
  rw [symbol, hd]
  rw [← List.getD_eq_getElem?_getD, answer_eq_getD p.original p.data.cut p.data.suffix _ hc]
  have hl := length_word p.original p.data.cut p.data.suffix hc
  rw [Evaluator.width, ← hl]
  unfold QueryMachine.read
  split <;> rename_i h
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  · dsimp only at h
    simp [List.getElem?_eq_none
      (by omega : (word p.original p.data.cut p.data.suffix).length ≤ M.query s)]

/-- A resumed step preserves the header/cursor and exactly advances the arbitrary outer state. -/
theorem step_loaded (p : Runtime.Input) (hc : p.data.cut ≤ p.original.length) (s : σ) :
    (machine M).step (Runtime.encInput p) ⟨Evaluator.loaded p, s⟩ =
      ⟨Evaluator.loaded p, M.step (word p.original p.data.cut p.data.suffix) s⟩ := by
  have hr : Runtime.machine.halted (Evaluator.loaded p) = true := rfl
  simp only [QueryMachine.step]
  have hh : (machine M).halted ⟨Evaluator.loaded p, s⟩ = M.halted s := by
    simp only [machine, hr, Bool.true_and]
  rw [hh]
  split <;> rename_i h
  · rfl
  · rw [read_loaded]
    change (if Runtime.machine.halted (Evaluator.loaded p) then
      State.mk (Evaluator.loaded p)
        (M.next (s, symbol M ⟨Evaluator.loaded p, s⟩ (p.original[M.query s]?)))
      else State.mk (Runtime.machine.next (Evaluator.loaded p, p.original[M.query s]?)) s) = _
    rw [hr, ite_eq_left rfl, symbol_loaded M p hc]

/-- Any number of resumed steps, from any saved state, preserves the loaded runtime data. -/
theorem resume (p : Runtime.Input) (hc : p.data.cut ≤ p.original.length) (s : σ) (k : ℕ) :
    ((machine M).step (Runtime.encInput p))^[k] ⟨Evaluator.loaded p, s⟩ =
      ⟨Evaluator.loaded p, (M.step (word p.original p.data.cut p.data.suffix))^[k] s⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, step_loaded M p hc,
      Function.iterate_succ_apply']

/-- After initialization the outer run is simulated step for step, even after halting. -/
theorem run_loaded (p : Runtime.Input) (hc : p.data.cut ≤ p.original.length) (k : ℕ) :
    (machine M).run (Runtime.encInput p) (2 * (encData p.data).length + 2 + k) =
      ⟨Evaluator.loaded p, M.run (word p.original p.data.cut p.data.suffix) k⟩ := by
  rw [QueryMachine.run, Nat.add_comm, Function.iterate_add_apply]
  change ((machine M).step (Runtime.encInput p))^[k]
    ((machine M).run (Runtime.encInput p) (2 * (encData p.data).length + 2)) = _
  rw [run_initializing M p le_rfl]
  rcases p with ⟨d, x⟩
  rw [Runtime.run_halted]
  exact resume M ⟨d, x⟩ hc M.init k

/-- Emission resumes the unrestricted outer output continuation with the exact symbol. -/
theorem emit_loaded (p : Runtime.Input) (hc : p.data.cut ≤ p.original.length) (s : σ) :
    (machine M).emit (⟨Evaluator.loaded p, s⟩,
      (machine M).read (Runtime.encInput p) ⟨Evaluator.loaded p, s⟩) =
      M.emit (s, M.read (word p.original p.data.cut p.data.suffix) s) := by
  have hr : Runtime.machine.halted (Evaluator.loaded p) = true := rfl
  rw [read_loaded]
  change (if Runtime.machine.halted (Evaluator.loaded p) then
    M.emit (s, symbol M ⟨Evaluator.loaded p, s⟩ (p.original[M.query s]?)) else []) = _
  rw [hr, ite_eq_left rfl, symbol_loaded M p hc]

/-- Saved outer state adds to the charged header and binary cursor, without a virtual word. -/
theorem length_encState_le (enc : σ ↪ List Bool) (s : State σ) :
    (encState enc s).length ≤ 8 * s.runtime.header.length +
      4 * (encNat s.runtime.cursor).length + (enc s.outer).length + 23 := by
  simp only [encState_apply, encStateFields, length_encPair]
  have := Runtime.length_encState_le s.runtime
  omega

/-- A bound on outer states transfers to resumed physical states additively. -/
theorem length_resume_le (enc : σ ↪ List Bool) (p : Runtime.Input)
    (hc : p.data.cut ≤ p.original.length) (s : σ) (k B : ℕ)
    (hB : (enc ((M.step (word p.original p.data.cut p.data.suffix))^[k] s)).length ≤ B) :
    (encState enc (((machine M).step (Runtime.encInput p))^[k]
      ⟨Evaluator.loaded p, s⟩)).length ≤
        32 * ((encData p.data).length + Nat.log2 (Runtime.encInput p).length + 1) + 1 + B := by
  rw [resume M p hc s k]
  simp only [encState_apply, encStateFields, length_encPair]
  have hr := Runtime.length_run_le p (t := 2 * (encData p.data).length + 2) le_rfl
  rcases p with ⟨d, x⟩
  dsimp only at hr hB ⊢
  rw [Runtime.run_halted] at hr
  dsimp only [Evaluator.loaded] at hr hB ⊢
  omega

/-- Decoding the retained header uses native space linear in the charged state. -/
theorem data_inSpace (enc : σ ↪ List Bool) :
    ComputableInSpace (data (σ := σ)) (encState enc) encData
      (fun s => (encState enc s).length) :=
  budget_comp_linear (f := State.runtime) Runtime.header_inSpace
    (encState_runtime_budget enc (budget_id (.refl _)))

/-- The virtual width is computed without allocating the virtual input. -/
theorem width_inSpace (enc : σ ↪ List Bool) :
    ComputableInSpace (fun s : State σ => Evaluator.width (data s)) (encState enc) encNat
      (fun s => (encState enc s).length) :=
  budget_comp_linear Evaluator.width_data_inSpace (data_inSpace enc)

/-- The optional-read adapter has a native certificate from the outer query certificate alone. -/
theorem symbol_inSpace (enc : σ ↪ List Bool)
    (hq : ComputableInSpace M.query enc encNat (fun s => (enc s).length)) :
    ComputableInSpace (fun p : State σ × Option Bool => symbol M p.1 p.2)
      (encStateRead (encState enc)) (encOption encBool)
      (fun p => (encStateRead (encState enc) p).length) := by
  have hp := fst (encState enc) (encOption encBool)
  have hd := budget_comp_linear (data_inSpace enc) hp
  have hquery := budget_comp_linear hq (encState_outer_budget enc hp)
  have hwidth := budget_comp_linear (width_inSpace enc) hp
  have hb := budget_finite (encC := encBool) (fun b : Option Bool => b.getD false)
    (snd (encState enc) (encOption encBool))
  have ha := budget_comp_linear answer_inSpace
    (budget_prod (encData_mk_budget (encData_cut_budget hd) (encData_suffix_budget hd) hquery) hb)
  simpa only [symbol, decide_eq_true_eq] using budget_ite (budget_natLt hquery hwidth)
    (budget_finite (encC := encOption encBool) some ha) (budget_const none)

/-- Native certificates for every simulator component; all outer continuations are arbitrary.
Only ordinary native outer component certificates are premises, never substitution certificates. -/
theorem components_inSpace (enc : σ ↪ List Bool)
    (hq : ComputableInSpace M.query enc encNat (fun s => (enc s).length))
    (hn : ComputableInSpace M.next (encStateRead enc) enc
      (fun p => (encStateRead enc p).length))
    (he : ComputableInSpace M.emit (encStateRead enc) encBits
      (fun p => (encStateRead enc p).length))
    (hh : ComputableInSpace M.halted enc encBool (fun s => (enc s).length))
    (hf : ComputableInSpace M.finish enc encBits (fun s => (enc s).length)) :
    ComputableInSpace (machine M).query (encState enc) encNat
      (fun s => (encState enc s).length) ∧
    ComputableInSpace (machine M).next (encStateRead (encState enc))
      (encState enc) (fun p => (encStateRead (encState enc) p).length) ∧
    ComputableInSpace (machine M).emit (encStateRead (encState enc))
      encBits (fun p => (encStateRead (encState enc) p).length) ∧
    ComputableInSpace (machine M).halted (encState enc) encBool
      (fun s => (encState enc s).length) ∧
    ComputableInSpace (machine M).finish (encState enc) encBits
      (fun s => (encState enc s).length) := by
  have hid := budget_id (enc := encState enc) (.refl _)
  have hs := encState_runtime_budget enc hid
  have ho := encState_outer_budget enc hid
  have hr := budget_comp_linear Runtime.halted_inSpace hs
  have hcursor := Runtime.encScan_cursor_budget (Runtime.encState_toScan_budget hs)
  have hquery := budget_ite hr (budget_natAdd hcursor (budget_comp_linear hq ho))
    (budget_comp_linear Runtime.query_inSpace hs)
  have hp := fst (encState enc) (encOption encBool)
  have hrt := encState_runtime_budget enc hp
  have hout := encState_outer_budget enc hp
  have hb := snd (encState enc) (encOption encBool)
  have harg := budget_prod hout (symbol_inSpace M enc hq)
  have hready := budget_comp_linear Runtime.halted_inSpace hrt
  have hnext := budget_ite hready
    (encState_mk_budget enc hrt (budget_comp_linear hn harg))
    (encState_mk_budget enc (budget_comp_linear Runtime.next_inSpace (budget_prod hrt hb)) hout)
  have hemit := budget_ite hready (budget_comp_linear he harg) (budget_const [])
  have hfinish := budget_comp_linear hf ho
  exact ⟨hquery, hnext, hemit,
    budget_finite (encC := encBool) (fun p : Bool × Bool => p.1 && p.2)
      (budget_prod hr (budget_comp_linear hh ho)), hfinish⟩

/-- Exact first halt transfers from the outer machine, with only the fixed header-loading delay. -/
theorem first_halt (p : Runtime.Input) (hc : p.data.cut ≤ p.original.length) (T : ℕ)
    (hh : M.halted (M.run (word p.original p.data.cut p.data.suffix) T) = true)
    (hpre : ∀ t < T, M.halted (M.run (word p.original p.data.cut p.data.suffix) t) = false) :
    (machine M).halted ((machine M).run (Runtime.encInput p)
      (2 * (encData p.data).length + 2 + T)) = true ∧
    ∀ t < 2 * (encData p.data).length + 2 + T,
      (machine M).halted ((machine M).run (Runtime.encInput p) t) = false := by
  constructor
  · rw [run_loaded M p hc]
    change true && M.halted (M.run (word p.original p.data.cut p.data.suffix) T) = true
    rw [hh]
    rfl
  · intro t ht
    by_cases hi : t < 2 * (encData p.data).length + 2
    · rw [run_initializing M p (by omega)]
      change (Runtime.machine.halted (Runtime.machine.run (Runtime.encInput p) t) &&
        M.halted M.init) = false
      rw [(Runtime.first_halt p).2 t hi]
      rfl
    · rw [show t = 2 * (encData p.data).length + 2 +
        (t - (2 * (encData p.data).length + 2)) by omega, run_loaded M p hc]
      change (true && M.halted (M.run (word p.original p.data.cut p.data.suffix) _)) = false
      rw [hpre _ (by omega)]
      rfl

/-- The simulator's output is precisely the outer output, including all emissions and finish. -/
theorem output (p : Runtime.Input) (hc : p.data.cut ≤ p.original.length) (T : ℕ) :
    (machine M).output (Runtime.encInput p) (2 * (encData p.data).length + 2 + T) =
      M.output (word p.original p.data.cut p.data.suffix) T := by
  let H := 2 * (encData p.data).length + 2
  have hzero : ∀ i < H, (if (machine M).halted
      ((machine M).run (Runtime.encInput p) i) then [] else
      (machine M).emit ((machine M).run (Runtime.encInput p) i,
        (machine M).read (Runtime.encInput p) ((machine M).run (Runtime.encInput p) i))) = [] := by
    intro i hi
    rw [run_initializing M p (by omega)]
    have hr := (Runtime.first_halt p).2 i hi
    simp only [machine, hr, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  unfold QueryMachine.output
  rw [List.range_add, List.map_append, List.flatten_append]
  have hz : ((List.range H).map fun i => if (machine M).halted
      ((machine M).run (Runtime.encInput p) i) then [] else
      (machine M).emit ((machine M).run (Runtime.encInput p) i,
        (machine M).read (Runtime.encInput p) ((machine M).run (Runtime.encInput p) i))) =
      List.replicate H [] := by
    calc
      _ = (List.range H).map (fun _ => ([] : List Bool)) :=
        List.map_congr_left fun i hi => hzero i (List.mem_range.mp hi)
      _ = _ := by simp
  rw [hz, List.flatten_replicate_nil, List.nil_append, List.map_map]
  congr 1
  · congr 1
    apply List.map_congr_left
    intro i _
    dsimp only [Function.comp_def]
    rw [run_loaded M p hc]
    have hr : Runtime.machine.halted (Evaluator.loaded p) = true := rfl
    have hh : (machine M).halted ⟨Evaluator.loaded p,
        M.run (word p.original p.data.cut p.data.suffix) i⟩ =
        M.halted (M.run (word p.original p.data.cut p.data.suffix) i) := by
      simp only [machine, hr, Bool.true_and]
    rw [hh, emit_loaded M p hc]
  · rw [run_loaded M p hc]
    rfl

/-- Valid cuts give the ordinary prefix/suffix word, with no padded-gap convention. -/
abbrev Input := {p : Runtime.Input // p.data.cut ≤ p.original.length}

/-- Explicit framed runtime input, retaining the original word as its read-only tail. -/
abbrev encInput : Input ↪ List Bool :=
  (Function.Embedding.subtype
    (fun p : Runtime.Input => p.data.cut ≤ p.original.length)).trans Runtime.encInput

/-- All states up to an outer clock satisfy an additive header/position/outer-state bound. -/
theorem length_run_le (enc : σ ↪ List Bool) (p : Input) (T B : ℕ)
    (hB : ∀ k ≤ T,
      (enc (M.run (word p.val.original p.val.data.cut p.val.data.suffix) k)).length ≤ B)
    {t : ℕ} (ht : t ≤ 2 * (encData p.val.data).length + 2 + T) :
    (encState enc ((machine M).run (encInput p) t)).length ≤
      32 * ((encData p.val.data).length + Nat.log2 (encInput p).length + 1) + 1 + B := by
  change (encState enc ((machine M).run (Runtime.encInput p.val) t)).length ≤
    32 * ((encData p.val.data).length + Nat.log2 (Runtime.encInput p.val).length + 1) + 1 + B
  by_cases hi : t ≤ 2 * (encData p.val.data).length + 2
  · rw [run_initializing M p.val hi]
    simp only [encState_apply, encStateFields, length_encPair]
    have hr := Runtime.length_run_le p.val hi
    have hb := hB 0 (Nat.zero_le _)
    rw [QueryMachine.run_zero] at hb
    omega
  · rw [show t = 2 * (encData p.val.data).length + 2 +
        (t - (2 * (encData p.val.data).length + 2)) by omega, run_loaded M p.val p.property]
    simp only [encState_apply, encStateFields, length_encPair]
    have hr := Runtime.length_run_le p.val (t := 2 * (encData p.val.data).length + 2) le_rfl
    have hb := hB (t - (2 * (encData p.val.data).length + 2)) (by omega)
    rcases p with ⟨⟨d, x⟩, hp⟩
    dsimp only at hr hb ⊢
    rw [Runtime.run_halted] at hr
    dsimp only [Evaluator.loaded] at hr hb ⊢
    omega

/-- Generic native virtual-input substitution for a certified query transducer. Constants are
shared across all runtime headers and original inputs. The only semantic premises are the outer
machine's own termination/output and saved-state bound; no oracle or substitution is assumed. -/
theorem computableInSpace (enc : σ ↪ List Bool)
    (hq : ComputableInSpace M.query enc encNat (fun s => (enc s).length))
    (hn : ComputableInSpace M.next (encStateRead enc) enc
      (fun p => (encStateRead enc p).length))
    (he : ComputableInSpace M.emit (encStateRead enc) encBits
      (fun p => (encStateRead enc p).length))
    (hh : ComputableInSpace M.halted enc encBool (fun s => (enc s).length))
    (hf : ComputableInSpace M.finish enc encBits (fun s => (enc s).length))
    {β : Type} (encOut : β ↪ List Bool) (f : Input → β) (T B : Input → ℕ)
    (hhalt : ∀ p, M.halted
      (M.run (word p.val.original p.val.data.cut p.val.data.suffix) (T p)) = true)
    (hpre : ∀ p, ∀ k < T p,
      M.halted (M.run (word p.val.original p.val.data.cut p.val.data.suffix) k) = false)
    (hout : ∀ p, encOut (f p) =
      M.output (word p.val.original p.val.data.cut p.val.data.suffix) (T p))
    (hB : ∀ p, ∀ k ≤ T p,
      (enc (M.run (word p.val.original p.val.data.cut p.val.data.suffix) k)).length ≤ B p) :
    ∃ time c, ComputableInTimeAndSpace f encInput encOut time
      (fun p => c * (B p + (encData p.val.data).length + Nat.log2 (encInput p).length + 1)) := by
  obtain ⟨hq', hn', he', hh', hf'⟩ := components_inSpace M enc hq hn he hh hf
  refine (machine M).computableInSpace (encS := encState enc) (enc := encInput)
    (encOut := encOut) (f := f) hq' hn' he' hh' hf'
    (fun p => 2 * (encData p.val.data).length + 2 + T p)
    (fun p => (first_halt M p.val p.property (T p) (hhalt p) (hpre p)).1)
    (fun p => (first_halt M p.val p.property (T p) (hhalt p) (hpre p)).2)
    (fun p => (hout p).trans (output M p.val p.property (T p)).symm)
    (fun p => B p + (encData p.val.data).length + Nat.log2 (encInput p).length + 1)
    (fun p => by omega) ?_
  refine ⟨33, fun p t ht => ?_⟩
  have h := length_run_le M enc p (T p) (B p) (hB p) ht
  omega

end Turing.VirtualWord.Simulation
