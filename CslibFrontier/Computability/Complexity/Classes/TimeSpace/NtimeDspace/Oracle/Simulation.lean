/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Oracle.SimComp
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Oracle.SimSize
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine
import Mathlib.Data.List.GetD

/-!
# Space-bounded oracle machines with a space-efficient oracle

If the oracle `A` is decidable within linear space, then a deterministic oracle machine working
within space `s(n) ≥ log₂ n + 1`, its query tape included, is simulated by an oracle-free machine
within space `O(s(n))`: `SPACE^A[s] ⊆ SPACE[s]` (`SPACEO_subset_DSPACE`).

The simulation is a Complexitylib query machine (`Turing.QueryMachine`) whose states are a
universal configuration together with the query tape (`OracleTM.simQM`): each step reads the input
bit under the simulated input head, takes a universal step of a description of `M`, and decides the
query when `M` queries (`OracleTM.simNext`). Its parts are computable within linear space
(`Cslib.Complexity.NtimeDspace.Oracle.SimComp`), it follows `M` (`OracleTM.rel_run`), and its states
have size
linear in the space of `M` plus `log₂ n` (`OracleTM.length_encSim_run_le`), so
`Turing.QueryMachine.computableInSpace` runs it within space `O(s)`.

## Main results

* `Cslib.Complexity.NtimeDspace.Oracle.SPACEO_subset_DSPACE`.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Oracle

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.Universal Cslib.Complexity

namespace OracleTM

variable {k : ℕ} {State : Type} [Fintype State] (M : OracleTM k State) (eS : State ↪ ℕ)
  (A : Set (List Bool))

/-- **The simulation of `M` relative to `A`** as a query machine. -/
noncomputable def simQM : QueryMachine (SCfg × List Bool) where
  init := (init (desc eS eBit M.plainTM), [])
  query s := s.1.inputPos - 1
  next := M.simNext eS A
  emit := M.simEmit eS
  halted s := s.1.state.isNone
  finish _ := []

variable {M eS A}

omit [Fintype State] in
lemma output_step_prefix {x : List Bool} (c : OCfg k State x) :
    c.tapes.output <+: (M.step A c).tapes.output := by
  cases hq : c.tapes.state with
  | none => rw [step_of_halted _ _ hq]
  | some q =>
    rw [step_of_state _ _ hq]
    cases M.tr q c.tapes.inputSymbol c.tapes.workTapeSymbols with
    | step a o => simp
    | ask y n => simp

omit [Fintype State] in
lemma workTapePos_step {x : List Bool} (c : OCfg k State x) (i : Fin k) :
    |(M.step A c).tapes.workTapePos i - c.tapes.workTapePos i| ≤ 1 := by
  cases hq : c.tapes.state with
  | none => rw [step_of_halted _ _ hq]; simp
  | some q =>
    rw [step_of_state _ _ hq]
    cases M.tr q c.tapes.inputSymbol c.tapes.workTapeSymbols with
    | step a o => exact workTapePos_apply_le a c.tapes i
    | ask y n => simp

lemma rel_init (x : List Bool) : Rel eS (M.simQM eS A).init (M.toNTM.initCfg x) := by
  have h := toCfg_init (k := k) (d := desc eS eBit M.plainTM) (x := x.map eBit) rfl
  refine ⟨h.2, ?_, rfl⟩
  change (init (desc eS eBit M.plainTM)).toCfg k (x.map eBit) [] = (Cfg.init M.q₀ x).map eS eBit
  rw [h.1, Cfg.map_init]
  rfl

lemma halted_iff {x : List Bool} {p : SCfg × List Bool} {c : OCfg k State x} (h : Rel eS p c) :
    (M.simQM eS A).halted p = true ↔ c.tapes.state = none := by
  change p.1.state.isNone = true ↔ _
  rw [h.state]
  cases c.tapes.state <;> simp

/-- **The simulation follows `M`.** -/
theorem rel_run (x : List Bool) (t : ℕ) :
    Rel eS ((M.simQM eS A).run x t) (M.run A x t) := by
  induction t with
  | zero => exact rel_init x
  | succ t ih =>
    rw [QueryMachine.run_succ, run_succ]
    unfold QueryMachine.step
    cases hq : (M.run A x t).tapes.state with
    | none =>
      rw [ite_eq_left ((halted_iff ih).mpr hq), step_of_halted _ _ hq]
      exact ih
    | some q =>
      rw [ite_eq_right (by rw [halted_iff ih, hq]; simp)]
      exact (rel_simNext ih hq).1

/-- The output of the simulation is the output of `M`. -/
theorem output_run (x : List Bool) (t : ℕ) :
    (M.simQM eS A).output x t = (M.run A x t).tapes.output := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hih : ((List.range t).map fun i => if (M.simQM eS A).halted ((M.simQM eS A).run x i) then
        [] else (M.simQM eS A).emit ((M.simQM eS A).run x i,
          (M.simQM eS A).read x ((M.simQM eS A).run x i))).flatten =
        (M.run A x t).tapes.output := by
      simpa [QueryMachine.output, simQM] using ih
    simp only [QueryMachine.output, List.range_succ, List.map_append, List.flatten_append, hih,
      List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [show (M.simQM eS A).finish ((M.simQM eS A).run x (t + 1)) = [] from rfl, List.append_nil,
      run_succ]
    have hrel := rel_run (M := M) (eS := eS) (A := A) x t
    cases hq : (M.run A x t).tapes.state with
    | none =>
      rw [ite_eq_left ((halted_iff hrel).mpr hq), step_of_halted _ _ hq, List.append_nil]
    | some q =>
      rw [ite_eq_right (by rw [halted_iff hrel, hq]; simp)]
      have h2 := (rel_simNext (M := M) (A := A) hrel hq).2
      rw [List.append_nil] at h2
      change (M.run A x t).tapes.output ++ M.simEmit eS (_, x[_ - 1]?) = _
      rw [h2]
      exact List.prefix_iff_eq_append.mp (output_step_prefix _)

/-! ### The size of the states -/

omit [Fintype State] in
/-- The positions visited by work head `i` in the first `t` steps. -/
noncomputable def visitedAt (M : OracleTM k State) (A : Set (List Bool)) (x : List Bool) (t : ℕ)
    (i : Fin k) : Finset ℤ :=
  Finset.univ.image fun n : Fin (t + 1) => (M.run A x n).tapes.workTapePos i

omit [Fintype State] in
lemma head_of_rel {x : List Bool} {p : SCfg × List Bool} {c : OCfg k State x} (h : Rel eS p c)
    (i : Fin k) : (p.1.workTapes.getD i Universal.Tape.blank).head = c.tapes.workTapePos i := by
  have := congrArg (fun c => Cfg.workTapePos c i) h.2.1
  simpa [SCfg.toCfg] using this

lemma simNext_fst (q : (SCfg × List Bool) × Option Bool) :
    ∃ tm : MultiTapeTM k Bool State,
      (M.simNext eS A q).1 = (stepWith (desc eS eBit tm) q.1.1 (symOf q.1.1 q.2)).1 := by
  unfold simNext
  split_ifs <;> exact ⟨_, rfl⟩

omit [Fintype State] in
lemma getD_bits (as : List TapeAct) (has : ∀ a ∈ as, ∀ o, a.1 = some o → o.getD 0 ≤ 1) (i : ℕ) :
    ∀ o, (as.getD i (none, 0)).1 = some o → o.getD 0 ≤ 1 := by
  rcases Nat.lt_or_ge i as.length with hi | hi
  · rw [List.getD_eq_getElem _ _ hi]
    exact has _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ hi]
    simp

/-- The zippers of the simulation are covered by the visited positions and hold bits. -/
theorem simTapes_run (x : List Bool) (t : ℕ) (i : Fin k) :
    TapeCovered (((M.simQM eS A).run x t).1.workTapes.getD i Universal.Tape.blank)
        (M.visitedAt A x t i) ∧
      TapeBits (((M.simQM eS A).run x t).1.workTapes.getD i Universal.Tape.blank) := by
  induction t with
  | zero =>
    have : ((M.simQM eS A).run x 0).1.workTapes.getD i Universal.Tape.blank =
        Universal.Tape.blank := by
      simp [QueryMachine.run, simQM, init, desc, List.getD_eq_getElem?_getD, Universal.Tape.blank]
    rw [this]
    exact ⟨TapeCovered.blank _, tapeBits_blank⟩
  | succ t ih =>
    have hmono : M.visitedAt A x t i ⊆ M.visitedAt A x (t + 1) i := by
      intro z hz
      obtain ⟨n, -, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_image.mpr ⟨n.castSucc, Finset.mem_univ _, rfl⟩
    have hrel := rel_run (M := M) (eS := eS) (A := A) x t
    have hrel' := rel_run (M := M) (eS := eS) (A := A) x (t + 1)
    rw [QueryMachine.run_succ] at hrel' ⊢
    unfold QueryMachine.step at hrel' ⊢
    split_ifs with hh
    · exact ⟨ih.1.mono hmono, ih.2⟩
    · obtain ⟨tm, htm⟩ := simNext_fst (M := M) (eS := eS) (A := A)
        ((M.simQM eS A).run x t, (M.simQM eS A).read x ((M.simQM eS A).run x t))
      change TapeCovered ((M.simNext eS A _).1.workTapes.getD i Universal.Tape.blank) _ ∧
        TapeBits ((M.simNext eS A _).1.workTapes.getD i Universal.Tape.blank)
      have hhead := head_of_rel hrel' i
      rw [ite_eq_right hh] at hhead
      change ((M.simNext eS A _).1.workTapes.getD i Universal.Tape.blank).head = _ at hhead
      rw [htm] at hhead ⊢
      obtain ⟨as, has, hws⟩ := stepWith_desc_tapes eS tm ((M.simQM eS A).run x t).1
        (symOf ((M.simQM eS A).run x t).1 ((M.simQM eS A).read x ((M.simQM eS A).run x t)))
      have hi : (i : ℕ) < ((M.simQM eS A).run x t).1.workTapes.length := by
        rw [hrel.1.length_workTapes]; exact i.isLt
      rw [hws, getD_applyTapes' _ _ hi] at hhead ⊢
      refine ⟨(ih.1.mono hmono).apply ?_ _ ?_, ih.2.apply _ (getD_bits as has i)⟩
      · rw [head_of_rel hrel i]
        exact hmono (Finset.mem_image.mpr ⟨Fin.last t, Finset.mem_univ _, rfl⟩)
      · rw [hhead]
        exact Finset.mem_image.mpr ⟨Fin.last (t + 1), Finset.mem_univ _, rfl⟩

lemma natAbs_head_lt (x : List Bool) (t : ℕ) (i : Fin k) :
    (((M.simQM eS A).run x t).1.workTapes.getD i Universal.Tape.blank).head.natAbs <
      (M.visitedAt A x t i).card := by
  rw [head_of_rel (rel_run x t) i]
  exact natAbs_lt_card_visited (fun j => (M.run A x j).tapes.workTapePos i) rfl
    (fun j => by
      change |(M.runFrom A _ (j + 1)).tapes.workTapePos i - _| ≤ 1
      rw [runFrom_succ]
      exact workTapePos_step _ i) t

/-- A bound on the encoded states `eS q`. -/
noncomputable def stateBound (eS : State ↪ ℕ) : ℕ := Finset.univ.sup (fun q : State => eS q) + 1

lemma length_eSym_le (o : Option State) : (eSym (o.map eS)).length ≤ stateBound eS := by
  cases o with
  | none => simp
  | some q =>
    simp only [Option.map_some, encOption_some, encUnary_apply, List.length_cons,
      List.length_replicate, stateBound]
    have := Finset.le_sup (f := fun q : State => eS q) (Finset.mem_univ q)
    omega

/-- **The size of the states of the simulation**: linear in the space used by `M`, plus
`log₂ |x|`. -/
theorem length_encSim_run_le (x : List Bool) (t : ℕ) :
    (encSim ((M.simQM eS A).run x t)).length ≤
      (4 * stateBound eS + 2 * k + 100) *
        (OracleNTM.pathSpace (OracleTM.ComputationPath.ofRun M A x t).toRunPath +
          x.length.log2 + 1) := by
  have hrel := rel_run (M := M) (eS := eS) (A := A) x t
  have hcfg := length_eCfg_le ((M.simQM eS A).run x t).1 (M.visitedAt A x t)
    hrel.1.length_workTapes (fun i => (simTapes_run x t i).1) (fun i => natAbs_head_lt x t i)
    (fun i => (simTapes_run x t i).2)
  have hst : (eSym ((M.simQM eS A).run x t).1.state).length ≤ stateBound eS := by
    rw [hrel.state]; exact length_eSym_le _
  have hpos : (encNat ((M.simQM eS A).run x t).1.inputPos).length ≤ x.length.log2 + 2 := by
    rw [hrel.inputPos]
    exact length_encNat_le_log2_add_two (by have := (M.run A x t).tapes.inputPos.isLt; omega)
  have hq : ((M.simQM eS A).run x t).2.length ≤ Finset.univ.sup fun n : Fin (t + 1) =>
      (M.run A x n).query.length := by
    rw [hrel.2.2]
    exact Finset.le_sup (f := fun n : Fin (t + 1) => (M.run A x n).query.length)
      (Finset.mem_univ (Fin.last t))
  have hsp : OracleNTM.pathSpace (OracleTM.ComputationPath.ofRun M A x t).toRunPath =
      (∑ i, (M.visitedAt A x t i).card) +
        Finset.univ.sup fun n : Fin (t + 1) => (M.run A x n).query.length := rfl
  rw [hsp]
  simp only [encSim, length_encPair, encBits_apply]
  generalize (∑ i, (M.visitedAt A x t i).card) = W at hcfg ⊢
  generalize (Finset.univ.sup fun n : Fin (t + 1) => (M.run A x n).query.length) = Q at hq ⊢
  generalize stateBound eS = D at hst ⊢
  generalize x.length.log2 = L at hpos ⊢
  have h3 : 4 * D + 2 * k + 100 * (W + Q + L + 1) ≤ (4 * D + 2 * k + 100) * (W + Q + L + 1) := by
    have := Nat.mul_le_mul_left (4 * D + 2 * k) (show 1 ≤ W + Q + L + 1 by omega)
    rw [Nat.add_mul]
    omega
  omega

end OracleTM

open OracleTM in
/-- **`SPACE^A[s] ⊆ SPACE[s]` for an oracle decidable in linear space.** If membership in `A` is
computable within space linear in the query, then every language decided relative to `A` by a
deterministic oracle machine within space `O(s)`, the query tape included, is in `DSPACE[s]`, for
`s(n) ≥ log₂ n + 1`. -/
theorem SPACEO_subset_DSPACE {A : Set (List Bool)}
    (hA : open scoped Classical in
      ComputableInSpace (fun w => decide (w ∈ A)) encBits encBool fun w => w.length)
    {s : ℕ → ℕ} (hlog : ∀ n, n.log2 + 1 ≤ s n) : SPACEO A s ⊆ DSPACE encBits s := by
  classical
  rintro L ⟨c₁, c₂, k, State, hfin, M, t, hM⟩
  have := Fintype.ofFinite State
  set eS : State ↪ ℕ := (Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding
  have hex : ∀ x, ∃ u, (M.run A x u).tapes.Halted := fun x => by
    obtain ⟨-, -, u, hu, -⟩ := hM x
    exact ⟨u, hu⟩
  have hrel := fun x u => rel_run (M := M) (eS := eS) (A := A) x u
  have hhalt : ∀ x, (M.simQM eS A).halted ((M.simQM eS A).run x (Nat.find (hex x))) = true :=
    fun x => (halted_iff (hrel x _)).mpr (Nat.find_spec (hex x))
  have hpre : ∀ x, ∀ u < Nat.find (hex x), (M.simQM eS A).halted ((M.simQM eS A).run x u) = false :=
    fun x u hu => by
      rw [Bool.eq_false_iff, ne_eq, halted_iff (hrel x u)]
      exact Nat.find_min (hex x) hu
  have hf : ∀ x, encBool (MultiTapeTM.indicator L x) =
      (M.simQM eS A).output (encBits x) (Nat.find (hex x)) := fun x => by
    obtain ⟨-, -, u, hu, hout⟩ := hM x
    rw [encBits_apply, output_run,
      ← M.run_eq_of_halted A (Nat.find_spec (hex x)) (Nat.find_min' (hex x) hu), hout]
    rfl
  have hlog' : ∀ x, Nat.log2 (encBits x).length + 1 ≤ s x.length + 1 := fun x => by
    have := hlog x.length; simp only [encBits_apply]; omega
  have hsize : ∃ C, ∀ x, ∀ u ≤ Nat.find (hex x),
      (encSim ((M.simQM eS A).run (encBits x) u)).length ≤ C * (s x.length + 1) := by
    refine ⟨(4 * stateBound eS + 2 * k + 100) * (c₁ + c₂ + 1), fun x u _ => ?_⟩
    refine (length_encSim_run_le x u).trans ?_
    have hsp : OracleNTM.pathSpace (OracleTM.ComputationPath.ofRun M A x u).toRunPath ≤
        c₁ * s x.length + c₂ := (hM x).2.1 (OracleTM.ComputationPath.ofRun M A x u)
    have hl := hlog x.length
    have hle : OracleNTM.pathSpace (OracleTM.ComputationPath.ofRun M A x u).toRunPath +
        x.length.log2 + 1 ≤ (c₁ + c₂ + 1) * (s x.length + 1) := by
      have : c₁ * s x.length + c₂ + x.length.log2 + 1 ≤ (c₁ + c₂ + 1) * (s x.length + 1) := by
        nlinarith
      omega
    calc _ ≤ (4 * stateBound eS + 2 * k + 100) * ((c₁ + c₂ + 1) * (s x.length + 1)) :=
          Nat.mul_le_mul_left _ hle
      _ = _ := by ring
  obtain ⟨T, c, hc⟩ := QueryMachine.computableInSpace (enc := encBits) (encOut := encBool)
    (M.simQM eS A) simQuery_inSpace (simNext_inSpace M eS hA) (simEmit_inSpace M eS)
    simHalted_inSpace (ComputableInSpace.const []) (f := MultiTapeTM.indicator L)
    (fun x => Nat.find (hex x)) hhalt hpre hf (fun x => s x.length + 1) hlog' hsize
  refine mem_DSPACE_iff.mpr ⟨c, c, T, ?_⟩
  refine hc.mono (fun _ => le_rfl) fun x => ?_
  simp only [encBits_apply]
  ring_nf
  omega

end Cslib.Complexity.NtimeDspace.Oracle
