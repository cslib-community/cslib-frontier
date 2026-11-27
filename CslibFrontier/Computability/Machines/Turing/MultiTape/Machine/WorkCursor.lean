/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ClearWork
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.MarkWork
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.Equivalence
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.Sequential

/-!
# Explicit work-tape cursor tables

These retained effect-free transition tables scan, rewind, mark and clear one work tape. Their
exact execution and head-range theorems establish the same resource formulas as the established
deterministic plumbing machines without extracting a transition function from an opaque relation.

## Main definitions

* `Turing.MultiTapeMachine.forwardWork`: scan to the word frontier.
* `Turing.MultiTapeMachine.rewindWork`: rewind a work-tape head, optionally overwriting cells.
* `Turing.MultiTapeMachine.markWork`: write immediately left of the head.
* `Turing.MultiTapeMachine.clearWork`: scan and erase while rewinding.

## Main results

* `Turing.MultiTapeMachine.runFrom_forwardWork`, `.runFrom_rewindWork`, `.runFrom_markWork`:
  exact completed runs.
* `Turing.MultiTapeMachine.workTapePos_runFrom_forwardWork`,
  `.workTapePos_runFrom_rewindWork`: exact head ranges for every prefix.
* `Turing.MultiTapeMachine.transformsTapes_clearWork`: exact clear semantics, clock and workspace.
-/

public section

namespace Turing.MultiTapeMachine

section WorkCursor

variable {Symbol : Type*}

/-- The explicit transition table that moves a one-tape head to the word frontier. -/
def forwardWork (Symbol : Type*) : MultiTapeMachine 1 Symbol Unit Empty Id :=
  ofTr () fun _ _ work ↦
    match work 0 with
    | some _ => ⟨0, fun _ => (none, 1), none, some ()⟩
    | none => ⟨0, fun _ => (none, 0), none, none⟩

namespace ForwardWork

variable {input : List Symbol} {inpos : Fin (input.length + 2)} {out : List Symbol}

private theorem transition (inputSymbol : Option Symbol) (work : Fin 1 → Option Symbol) :
    (forwardWork Symbol).toTM.tr () inputSymbol work =
      match work 0 with
      | some _ => ⟨0, fun _ => (none, 1), none, some ()⟩
      | none => ⟨0, fun _ => (none, 0), none, none⟩ := by
  simp only [forwardWork, toTM, ofTr, MultiTapeTM.tr_ofTr]
  cases work 0 <;> rfl

private theorem runFrom_walk {w : List Symbol} {p : ℕ} (n : ℕ) (hn : p + n ≤ w.length) :
    (forwardWork Symbol).toTM.runFrom
        ⟨some (), inpos, fun _ => Turing.tapeOfList w, fun _ => (p : ℤ), out⟩ n =
      ⟨some (), inpos, fun _ => Turing.tapeOfList w, fun _ => (p : ℤ) + n, out⟩ := by
  induction n with
  | zero => simp [MultiTapeTM.runFrom]
  | succ n ih =>
    have hsym : Turing.tapeOfList w ((p : ℤ) + n) = some (w[p + n]'(by lia)) := by
      rw [← Nat.cast_add, Turing.tapeOfList_ofNat]
      exact List.getElem?_eq_getElem (by lia)
    rw [MultiTapeTM.runFrom, Function.iterate_succ_apply', ← MultiTapeTM.runFrom,
      ih (by lia), MultiTapeTM.step_of_state rfl]
    simp [transition, Turing.Action.apply, Cfg.workTapeSymbols, hsym, add_assoc]

end ForwardWork

/-- Exact run of the explicit frontier scanner. -/
theorem runFrom_forwardWork {input : List Symbol} (inpos : Fin (input.length + 2))
    (w : List Symbol) (out : List Symbol) {p n : ℕ} (hpn : p + n = w.length) :
    (forwardWork Symbol).toTM.runFrom
        ⟨some (forwardWork Symbol).initial, inpos, fun _ => Turing.tapeOfList w,
          fun _ => (p : ℤ), out⟩ (n + 1) =
      ⟨none, inpos, fun _ => Turing.tapeOfList w, fun _ => (w.length : ℤ), out⟩ := by
  rw [MultiTapeTM.runFrom, Function.iterate_succ_apply', ← MultiTapeTM.runFrom,
    ForwardWork.runFrom_walk _ hpn.le, show (p : ℤ) + n = w.length by lia,
    MultiTapeTM.step_of_state rfl]
  simp [ForwardWork.transition, Turing.Action.apply, Cfg.workTapeSymbols]

/-- Every prefix of the explicit frontier scan keeps its head between the start and frontier. -/
theorem workTapePos_runFrom_forwardWork {input : List Symbol}
    (inpos : Fin (input.length + 2)) (w : List Symbol) (out : List Symbol)
    {p : ℕ} (hp : p ≤ w.length) (steps : ℕ) :
    ((forwardWork Symbol).toTM.runFrom
      ⟨some (forwardWork Symbol).initial, inpos, fun _ => Turing.tapeOfList w,
        fun _ => (p : ℤ), out⟩ steps).workTapePos 0 ∈ Set.Icc (p : ℤ) w.length := by
  rcases Nat.lt_or_ge steps (w.length - p + 1) with hlt | hge
  · rw [ForwardWork.runFrom_walk steps (by lia)]
    simp only [Set.mem_Icc]
    constructor <;> lia
  · have hrun := runFrom_forwardWork (Symbol := Symbol) inpos w out (Nat.add_sub_cancel' hp)
    rw [(forwardWork Symbol).toTM.runFrom_eq_of_halt _ hge (by rw [hrun]), hrun]
    simp [hp]

/-- The explicit transition table that rewinds one work-tape head, optionally overwriting cells. -/
def rewindWork (Symbol : Type*) (write : Option (Option Symbol) := none) :
    MultiTapeMachine 1 Symbol MultiTapeTM.RewindWorkState Empty Id :=
  ofTr .start fun state _ work =>
    match state, work 0 with
    | .start, _ => ⟨0, fun _ => (none, -1), none, some .scan⟩
    | .scan, some _ => ⟨0, fun _ => (write, -1), none, some .scan⟩
    | .scan, none => ⟨0, fun _ => (none, 1), none, none⟩

namespace RewindWork

variable {input : List Symbol} {write : Option (Option Symbol)}
  {ip : Fin (input.length + 2)} {tape : ℤ → Option Symbol} {out : List Symbol} {p : ℤ}

private theorem transition (state : MultiTapeTM.RewindWorkState)
    (inputSymbol : Option Symbol) (work : Fin 1 → Option Symbol) :
    (rewindWork Symbol write).toTM.tr state inputSymbol work =
      match state, work 0 with
      | .start, _ => ⟨0, fun _ => (none, -1), none, some .scan⟩
      | .scan, some _ => ⟨0, fun _ => (write, -1), none, some .scan⟩
      | .scan, none => ⟨0, fun _ => (none, 1), none, none⟩ := by
  simp only [rewindWork, toTM, ofTr, MultiTapeTM.tr_ofTr]
  cases state <;> cases work 0 <;> rfl

private theorem step_start :
    (rewindWork Symbol write).toTM.step
        ⟨some .start, ip, fun _ => tape, fun _ => p, out⟩ =
      ⟨some .scan, ip, fun _ => tape, fun _ => p - 1, out⟩ := by
  rw [MultiTapeTM.step_of_state rfl, transition]
  simp [Turing.Action.apply, sub_eq_add_neg]

private theorem step_scan_some {symbol : Symbol} (hs : tape p = some symbol) :
    (rewindWork Symbol write).toTM.step
        ⟨some .scan, ip, fun _ => tape, fun _ => p, out⟩ =
      ⟨some .scan, ip, fun _ => write.elim tape (Function.update tape p),
        fun _ => p - 1, out⟩ := by
  rw [MultiTapeTM.step_of_state rfl, transition]
  cases write <;> simp [Turing.Action.apply, Cfg.workTapeSymbols, hs, sub_eq_add_neg]

private theorem step_scan_none (hs : tape p = none) :
    (rewindWork Symbol write).toTM.step
        ⟨some .scan, ip, fun _ => tape, fun _ => p, out⟩ =
      ⟨none, ip, fun _ => tape, fun _ => p + 1, out⟩ := by
  rw [MultiTapeTM.step_of_state rfl, transition]
  simp [Turing.Action.apply, Cfg.workTapeSymbols, hs]

private theorem runFrom_scan {w : List Symbol} (hw : tape = Turing.tapeOfList w)
    {l : ℕ} (hl : l ≤ w.length) (n : ℕ) (hn : n ≤ l) :
    (rewindWork Symbol write).toTM.runFrom
        ⟨some .scan, ip, fun _ => tape, fun _ => (l : ℤ) - 1, out⟩ n =
      ⟨some .scan, ip,
        fun _ z => if (l : ℤ) - n ≤ z ∧ z < l then write.getD (tape z) else tape z,
        fun _ => (l : ℤ) - 1 - n, out⟩ := by
  induction n with
  | zero => simp [MultiTapeTM.runFrom, show ∀ z : ℤ, ¬((l : ℤ) ≤ z ∧ z < l) by omega]
  | succ n ih =>
    have hsym : (fun z => if (l : ℤ) - n ≤ z ∧ z < l then write.getD (tape z) else tape z)
        ((l : ℤ) - 1 - n) = some (w[l - 1 - n]'(by omega)) := by
      dsimp only
      rw [ite_eq_right (by omega), hw,
        show (l : ℤ) - 1 - n = ((l - 1 - n : ℕ) : ℤ) by omega,
        Turing.tapeOfList_ofNat]
      exact List.getElem?_eq_getElem (by omega)
    rw [MultiTapeTM.runFrom, Function.iterate_succ_apply', ← MultiTapeTM.runFrom,
      ih (by omega), step_scan_some hsym]
    congr 2
    · cases write with
      | none => simp
      | some cell =>
        funext _ z
        simp only [Option.elim_some, Function.update_apply, Option.getD_some]
        split_ifs <;> first | rfl | omega
    · funext _
      omega

end RewindWork

/-- Exact run of the explicit work-tape rewinder. -/
theorem runFrom_rewindWork {input : List Symbol} (write : Option (Option Symbol))
    (ip : Fin (input.length + 2)) (tape : ℤ → Option Symbol) (out : List Symbol)
    {w : List Symbol} (hw : tape = Turing.tapeOfList w) {p : ℕ} (hp : p ≤ w.length) :
    (rewindWork Symbol write).toTM.runFrom
        ⟨some (rewindWork Symbol write).initial, ip, fun _ => tape, fun _ => (p : ℤ), out⟩
        (p + 2) =
      ⟨none, ip,
        fun _ z => if 0 ≤ z ∧ z < p then write.getD (tape z) else tape z,
        fun _ => 0, out⟩ := by
  rw [show (rewindWork Symbol write).initial = .start from rfl, MultiTapeTM.runFrom,
    Function.iterate_succ_apply, RewindWork.step_start, Function.iterate_succ_apply',
    ← MultiTapeTM.runFrom, RewindWork.runFrom_scan hw hp p le_rfl,
    show (p : ℤ) - 1 - p = -1 by omega,
    RewindWork.step_scan_none (by simp [hw, Turing.tapeOfList]; rfl)]
  simp

/-- Rewinding without writing preserves the tape contents. -/
theorem runFrom_rewindWork_none {input : List Symbol} (ip : Fin (input.length + 2))
    (tape : ℤ → Option Symbol) (out : List Symbol) {w : List Symbol}
    (hw : tape = Turing.tapeOfList w) {p : ℕ} (hp : p ≤ w.length) :
    (rewindWork Symbol).toTM.runFrom
        ⟨some (rewindWork Symbol).initial, ip, fun _ => tape, fun _ => (p : ℤ), out⟩
        (p + 2) = ⟨none, ip, fun _ => tape, fun _ => 0, out⟩ := by
  simpa using runFrom_rewindWork (Symbol := Symbol) none ip tape out hw hp

/-- Rewinding from the frontier while erasing leaves the work tape blank. -/
theorem runFrom_rewindWork_erase {input : List Symbol} (ip : Fin (input.length + 2))
    (tape : ℤ → Option Symbol) (out : List Symbol) {w : List Symbol}
    (hw : tape = Turing.tapeOfList w) :
    (rewindWork Symbol (some none)).toTM.runFrom
        ⟨some (rewindWork Symbol (some none)).initial, ip, fun _ => tape,
          fun _ => (w.length : ℤ), out⟩ (w.length + 2) =
      ⟨none, ip, fun _ _ => none, fun _ => 0, out⟩ := by
  rw [runFrom_rewindWork (Symbol := Symbol) _ ip tape out hw le_rfl]
  congr 2
  funext _ z
  split_ifs with h
  · rfl
  · rw [hw, Turing.tapeOfList_eq_none_iff]
    omega

/-- Every prefix of the explicit rewind stays between the blank before the word and its start. -/
theorem workTapePos_runFrom_rewindWork {input : List Symbol}
    (write : Option (Option Symbol)) (ip : Fin (input.length + 2))
    (tape : ℤ → Option Symbol) (out : List Symbol) {w : List Symbol}
    (hw : tape = Turing.tapeOfList w) {p : ℕ} (hp : p ≤ w.length) (steps : ℕ) :
    ((rewindWork Symbol write).toTM.runFrom
      ⟨some (rewindWork Symbol write).initial, ip, fun _ => tape,
        fun _ => (p : ℤ), out⟩ steps).workTapePos 0 ∈ Set.Icc (-1) (p : ℤ) := by
  rcases steps with _ | steps
  · simp [MultiTapeTM.runFrom]
  rcases Nat.lt_or_ge steps (p + 1) with hlt | hge
  · rw [show (rewindWork Symbol write).initial = .start from rfl, MultiTapeTM.runFrom,
      Function.iterate_succ_apply, RewindWork.step_start, ← MultiTapeTM.runFrom,
      RewindWork.runFrom_scan hw hp steps (by omega)]
    simp only [Set.mem_Icc]
    constructor <;> omega
  · have hrun := runFrom_rewindWork (Symbol := Symbol) write ip tape out hw hp
    rw [(rewindWork Symbol write).toTM.runFrom_eq_of_halt _
      (by omega : p + 2 ≤ steps + 1) (by rw [hrun]), hrun]
    simp

end WorkCursor

variable {Symbol : Type}

/-- The explicit two-step table that writes immediately to the left of a work-tape head. -/
def markWork (Symbol : Type) (write : Option Symbol) :
    MultiTapeMachine 1 Symbol MultiTapeTM.MarkWorkState Empty Id :=
  ofTr .start fun state _ _ =>
    match state with
    | .start => ⟨0, fun _ => (none, -1), none, some .put⟩
    | .put => ⟨0, fun _ => (some write, 1), none, none⟩

private theorem markWork_transition (write : Option Symbol) (state : MultiTapeTM.MarkWorkState)
    (inputSymbol : Option Symbol) (work : Fin 1 → Option Symbol) :
    (markWork Symbol write).toTM.tr state inputSymbol work =
      match state with
      | .start => ⟨0, fun _ => (none, -1), none, some .put⟩
      | .put => ⟨0, fun _ => (some write, 1), none, none⟩ := by
  simp only [markWork, toTM, ofTr, MultiTapeTM.tr_ofTr]
  cases state <;> rfl

/-- The explicit marker writes the cell immediately left of its head in exactly two steps. -/
theorem runFrom_markWork {input : List Symbol} (write : Option Symbol)
    (ip : Fin (input.length + 2)) (tape : ℤ → Option Symbol) (out : List Symbol) (p : ℤ) :
    (markWork Symbol write).toTM.runFrom
        ⟨some (markWork Symbol write).initial, ip, fun _ => tape, fun _ => p, out⟩ 2 =
      ⟨none, ip, fun _ => Function.update tape (p - 1) write, fun _ => p, out⟩ := by
  have hstart : (markWork Symbol write).toTM.step
      ⟨some .start, ip, fun _ => tape, fun _ => p, out⟩ =
      ⟨some .put, ip, fun _ => tape, fun _ => p - 1, out⟩ := by
    rw [MultiTapeTM.step_of_state rfl, markWork_transition]
    simp [Turing.Action.apply, sub_eq_add_neg]
  have hput : (markWork Symbol write).toTM.step
      ⟨some .put, ip, fun _ => tape, fun _ => p - 1, out⟩ =
      ⟨none, ip, fun _ => Function.update tape (p - 1) write, fun _ => p, out⟩ := by
    rw [MultiTapeTM.step_of_state rfl, markWork_transition]
    simp [Turing.Action.apply]
  change (markWork Symbol write).toTM.step
    ((markWork Symbol write).toTM.step
      ⟨some .start, ip, fun _ => tape, fun _ => p, out⟩) = _
  rw [hstart, hput]

/-- The explicit table that scans to the word frontier and erases while rewinding. -/
def clearWork (Symbol : Type) :
    MultiTapeMachine 1 Symbol (Unit ⊕ MultiTapeTM.RewindWorkState) Empty Id :=
  (forwardWork Symbol).seq (rewindWork Symbol (some none))

/-- The explicit clear table erases its work-tape word with the established exact clock and
independent workspace bound. -/
theorem transformsTapes_clearWork (word : List Symbol) :
    MultiTapeTM.TransformsTapes (clearWork Symbol).toTM
      (fun _ tapes => tapes 0 = word)
      (fun _ _ tapes' emitted => tapes' = (fun _ => []) ∧ emitted = [])
      (3 * (word.length + 1)) (word.length + 2) := by
  intro input tapes out htapes
  obtain rfl : tapes = fun _ => word := funext fun i => Fin.fin_one_eq_zero i ▸ htapes
  rw [clearWork, toTM_seq]
  let first := MultiTapeNTM.RunPath.ofDeterministic (forwardWork Symbol).toTM
    (Turing.wordsCfg input (some ()) (fun _ => word) out) (word.length + 1)
  let second := MultiTapeNTM.RunPath.ofDeterministic (rewindWork Symbol (some none)).toTM
    (⟨some (rewindWork Symbol (some none)).initial, 1, fun _ => Turing.tapeOfList word,
      fun _ => word.length, out⟩ : Cfg 1 Symbol MultiTapeTM.RewindWorkState input)
    (word.length + 2)
  have hfirst : first.last = _ := runFrom_forwardWork (Symbol := Symbol) 1 word out (zero_add _)
  have hsecond : second.last = _ :=
    runFrom_rewindWork_erase (Symbol := Symbol) 1 (Turing.tapeOfList word) out rfl
  obtain ⟨path, hhead, hlast, htime, -, hvisited⟩ :=
    MultiTapeTM.exists_runPath_seq (p₀ := first) (p₁ := second) (by rw [hfirst])
      (by rw [hfirst]; rfl)
  refine ⟨fun _ => [], [], ⟨rfl, rfl⟩, path, hhead,
    by rw [hlast, hsecond]; simp [Cfg.mapState, Turing.wordsCfg],
    (show path.length ≤ word.length + 1 + (word.length + 2) from htime).trans (by lia), ?_⟩
  rw [MultiTapeNTM.RunPath.space, Fin.sum_univ_one]
  refine (Finset.card_le_card (t := .Icc (-1 : ℤ) word.length)
    ((hvisited 0).trans (Finset.union_subset ?_ ?_))).trans (by simp) <;>
    refine Finset.image_subset_iff.mpr fun steps _ => Finset.mem_Icc.2 ?_
  · exact Set.Icc_subset_Icc_left (by lia)
      (workTapePos_runFrom_forwardWork (Symbol := Symbol) (input := input)
        1 word out (Nat.zero_le word.length) steps)
  · exact workTapePos_runFrom_rewindWork (Symbol := Symbol) (some none) (input := input)
      1 (Turing.tapeOfList word) out rfl le_rfl steps

end Turing.MultiTapeMachine
