/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.LocalTape

/-!
# The one-interval simulation on numbers

A numeric configuration (`NCfg`) holds the state code, the input position, every
work tape as an `NTape`, every work head as its index `rho` in the window of
`3b` cells of its tape, and the output track code. `nStep` is one coin step on
it, and `CRep` is the relation with Complexitylib's finite storage `LocalCfg`.

* `CRep.step`, `crep_run`: numeric steps track `localCoinStep` while every
  head index stays positive, which holds for `b` steps from the start.
* `stepData_iff`: the interval condition `LocalIntervalStepData` after a replay
  of at most `b` coins is the numeric condition `NCond`.
* `localIntervalCount_eq`: the interval count is the number of `x < 2 ^ b`
  whose bits, as coins, satisfy the numeric condition.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.LocalSim

open Cslib.Turing _root_.Turing _root_.Turing.MultiTapePTM _root_.Turing.MultiTapeNTM.ChoiceTable

variable {k s : ℕ} {State : Type} (e : State ≃ Fin s)

/-! ### Codes of states and tracks -/

/-- The code of a state: `none` is `0`, and `q` is `e q + 1`. -/
def stc (st : Option State) : ℕ := (((Equiv.optionCongr e).trans (finSuccEquiv s).symm) st : ℕ)

/-- The state of a code (`none` past `s`). -/
def stOf (n : ℕ) : Option State := if h : n < s + 1 then stateOfFin e ⟨n, h⟩ else none

theorem stc_lt (st : Option State) : stc e st < s + 1 := Fin.isLt _

theorem stOf_stc (st : Option State) : stOf e (stc e st) = st := by
  unfold stOf stc stateOfFin
  rw [dite_eq_left (Fin.isLt _)]
  simp only [Fin.eta, Equiv.symm_apply_apply]

theorem stc_inj {st st' : Option State} (h : stc e st = stc e st') : st = st' := by
  rw [← stOf_stc e st, h, stOf_stc]

/-- The cell of a code. -/
def cellOf (n : ℕ) : Option Bool := if h : n < 3 then cellEquiv.symm ⟨n, h⟩ else none

theorem cellOf_cc (c : Option Bool) : cellOf (cc c) = c := by
  unfold cellOf cc
  rw [dite_eq_left (Fin.isLt _)]
  simp

/-- The code of an output track. -/
def trc (t : OutputTrack) : ℕ := (OutputTrack.equivFin t : ℕ)

/-- The track of a code. -/
def trOf (n : ℕ) : OutputTrack := OutputTrack.equivFin.symm ⟨n % 3, Nat.mod_lt _ (by norm_num)⟩

theorem trOf_trc (t : OutputTrack) : trOf (trc t) = t := by
  unfold trOf trc
  simp only [Nat.mod_eq_of_lt (Fin.isLt _), Fin.eta, Equiv.symm_apply_apply]

theorem trc_lt (t : OutputTrack) : trc t < 3 := Fin.isLt _

theorem trc_inj {t t' : OutputTrack} (h : trc t = trc t') : t = t' := by
  rw [← trOf_trc t, h, trOf_trc]

/-! ### Numeric configurations -/

/-- A numeric configuration. -/
structure NCfg (k : ℕ) where
  st : ℕ
  ip : ℕ
  tapes : Fin k → NTape
  rho : Fin k → ℕ
  tr : ℕ

/-- A head index after a move. -/
def moveNat (r : ℕ) : SignType → ℕ
  | .neg => r - 1
  | .zero => r
  | .pos => r + 1

variable (machine : MultiTapePTM k Bool State)

/-- **One coin step on numbers.** -/
def nStep (input : List Bool) (n : NCfg k) (bit : Bool) : NCfg k :=
  let a := machine.coinAction (stOf e n.st) (inputAt input n.ip)
    (fun h => cellOf (n.tapes h).1) bit
  { st := stc e a.state
    ip := moveInputPosNat input.length n.ip a.inputTape
    tapes := fun h => (n.tapes h).step (a.workTapes h)
    rho := fun h => moveNat (n.rho h) (a.workTapes h).2
    tr := trc ((trOf n.tr).emit a.output) }

/-- Replaying coins on numbers. -/
def nRun (input : List Bool) (coins : List Bool) (n : NCfg k) : NCfg k :=
  coins.foldl (nStep e machine input) n

/-- A numeric configuration represents finite storage, with the window of tape
`h` starting at cell `b (Jw h - 1)`. -/
structure CRep (b : ℕ) (Jw : Fin k → ℤ) (l : LocalCfg k State) (n : NCfg k) : Prop where
  st : stc e l.state = n.st
  ip : l.inputPos = n.ip
  tapes : ∀ h, Rep (l.workTapes h) (n.tapes h)
  pos : ∀ h, l.workTapePos h = b * (Jw h - 1) + n.rho h
  tr : trc l.track = n.tr

variable {e machine}

theorem CRep.step {b : ℕ} {Jw : Fin k → ℤ} {l : LocalCfg k State} {n : NCfg k}
    (h : CRep e b Jw l n) (hrho : ∀ h, 1 ≤ n.rho h) (input : List Bool) (bit : Bool) :
    CRep e b Jw (machine.localCoinStep input l bit) (nStep e machine input n bit) := by
  have hst : stOf e n.st = l.state := by rw [← h.st, stOf_stc]
  have hwork : (fun h => cellOf (n.tapes h).1) = fun h' => (l.workTapes h').head := by
    funext h'
    have := h.tapes h' 0
    simp only [BiTape.read_zero, NTape.read] at this
    rw [← this, cellOf_cc]
  have htr : trOf n.tr = l.track := by rw [← h.tr, trOf_trc]
  unfold nStep MultiTapePTM.localCoinStep
  rw [hst, hwork, htr, ← h.ip]
  refine ⟨rfl, rfl, fun h' => (h.tapes h').step _, fun h' => ?_, rfl⟩
  simp only
  rw [h.pos h']
  have := hrho h'
  cases (machine.coinAction l.state (inputAt input l.inputPos)
      (fun h => (l.workTapes h).head) bit).workTapes h' |>.2 <;>
    simp only [moveNat, SignType.cast] <;> push_cast [Nat.cast_sub this] <;> ring

theorem crep_run {b : ℕ} {Jw : Fin k → ℤ} (input : List Bool) :
    ∀ (coins : List Bool) (l : LocalCfg k State) (n : NCfg k), CRep e b Jw l n →
      (∀ h, coins.length ≤ n.rho h) →
      CRep e b Jw (machine.localRun input coins l) (nRun e machine input coins n) := by
  intro coins
  induction coins with
  | nil => intro l n h _; exact h
  | cons bit coins ih =>
    intro l n h hrho
    have h1 : ∀ h, 1 ≤ n.rho h := fun h' => by have := hrho h'; simp at this; omega
    refine ih _ _ (h.step h1 input bit) fun h' => ?_
    have := hrho h'
    simp only [List.length_cons] at this
    change coins.length ≤ moveNat (n.rho h') _
    cases ((machine.coinAction (stOf e n.st) (inputAt input n.ip)
      (fun h => cellOf (n.tapes h).1) bit).workTapes h').2 <;> simp only [moveNat] <;> omega

/-! ### The start and the condition -/

variable (e) in
/-- The numeric start of an interval. -/
def nStart (b : ℕ) (input : List Bool) (J : Option (Fin k) → ℤ) (cIn : ControlData k State)
    (wIn : Fin k → List (Option Bool)) : NCfg k where
  st := stc e cIn.1
  ip := (inputPosOfCoord input (b * J none + cIn.2.1 none)).val
  tapes h := NTape.ofCells (wIn h) (b + cIn.2.1 (some h))
  rho h := b + cIn.2.1 (some h)
  tr := trc cIn.2.2

theorem crep_start (b : ℕ) (input : List Bool) (J : Option (Fin k) → ℤ)
    (cIn : ControlData k State) (wIn : Fin k → List (Option Bool)) :
    CRep e b (fun h => J (some h)) (localStartData b input J cIn wIn)
        (nStart e b input J cIn wIn) :=
  ⟨rfl, rfl, fun h => rep_ofCells _ _, fun h => by
    simp only [localStartData, nStart]; push_cast; ring, rfl⟩

variable (e) in
/-- **The numeric interval condition.** -/
def NCond (b : ℕ) (J : Option (Fin k) → ℤ) (δ : Option (Fin k) → SignType)
    (cOut : ControlData k State) (wOut : Fin k → List (Option Bool)) (n : NCfg k) : Prop :=
  n.st = stc e cOut.1 ∧ n.tr = trc cOut.2.2 ∧
    (cOut.2.1 none < b ∧ (n.ip : ℤ) - 1 = b * (J none + δ none) + cOut.2.1 none) ∧
    (∀ h, cOut.2.1 (some h) < b ∧
      (n.rho h : ℤ) = b * (1 + δ (some h)) + cOut.2.1 (some h)) ∧
    ∀ h, (wOut h).length = 3 * b ∧
      ∀ c < 3 * b, cc ((wOut h).getD c none) = (n.tapes h).read ((c : ℤ) - n.rho h)

theorem windowCellsAt_eq_iff {b : ℕ} {Jw : Fin k → ℤ} {l : LocalCfg k State} {n : NCfg k}
    (hr : CRep e b Jw l n) (h : Fin k) (w : List (Option Bool)) :
    l.windowCellsAt b (Jw h) h = w ↔
      w.length = 3 * b ∧ ∀ c < 3 * b, cc (w.getD c none) = (n.tapes h).read
          ((c : ℤ) - n.rho h) := by
  have hcell : ∀ c : ℕ, cc ((l.workTapes h).read (b * (Jw h - 1) + (c : ℤ) - l.workTapePos h)) =
      (n.tapes h).read ((c : ℤ) - n.rho h) := by
    intro c
    rw [hr.tapes h, hr.pos h]
    congr 1; ring
  unfold LocalCfg.windowCellsAt
  constructor
  · rintro rfl
    refine ⟨by simp, fun c hc => ?_⟩
    rw [List.getD_eq_getElem _ _ (by simpa using hc)]
    simp only [List.getElem_map, List.getElem_range]
    exact hcell c
  · rintro ⟨hl, hw⟩
    refine List.ext_getElem (by simp [hl]) fun c h1 h2 => ?_
    simp only [List.getElem_map, List.getElem_range]
    have hc : c < 3 * b := by simpa using h1
    apply cc_inj
    rw [hcell c, ← hw c hc, List.getD_eq_getElem _ _ h2]

/-- **The interval condition is the numeric condition**, for at most `b` coins. -/
theorem stepData_iff (b : ℕ) (input : List Bool) (J : Option (Fin k) → ℤ)
    (δ : Option (Fin k) → SignType) (cIn : ControlData k State)
    (wIn : Fin k → List (Option Bool)) (cOut : ControlData k State)
    (wOut : Fin k → List (Option Bool)) (coins : List Bool) (hc : coins.length ≤ b) :
    machine.LocalIntervalStepData b input J δ cIn wIn cOut wOut coins ↔
      NCond e b J δ cOut wOut (nRun e machine input coins (nStart e b input J cIn wIn)) := by
  have hr := crep_run (machine := machine) input coins _ _ (crep_start (e := e) b input J cIn wIn)
    (fun h => by change coins.length ≤ b + _; omega)
  set l := machine.localRun input coins (localStartData b input J cIn wIn)
  set n := nRun e machine input coins (nStart e b input J cIn wIn)
  unfold LocalIntervalStepData NCond
  rw [← hr.st, ← hr.tr, ← hr.ip]
  have hsome : ∀ h : Fin k, (l.headCoord (some h) = b * (J (some h) + δ (some h)) +
      cOut.2.1 (some h) ↔
      (n.rho h : ℤ) = b * (1 + δ (some h)) + cOut.2.1 (some h)) := by
    intro h
    change l.workTapePos h = _ ↔ _
    rw [hr.pos h]
    constructor <;> intro hh <;> linarith
  constructor
  · rintro ⟨hs, ht, hh, hw⟩
    refine ⟨by rw [hs], by rw [ht], ⟨(hh none).1, (hh none).2⟩,
      fun h => ⟨(hh (some h)).1, (hsome h).mp (hh (some h)).2⟩,
      fun h => (windowCellsAt_eq_iff hr h (wOut h)).mp (hw h)⟩
  · rintro ⟨hs, ht, hn, hh, hw⟩
    refine ⟨stc_inj e hs, trc_inj ht, fun head => ?_,
      fun h => (windowCellsAt_eq_iff hr h (wOut h)).mpr (hw h)⟩
    rcases head with _ | h
    · exact hn
    · exact ⟨(hh h).1, (hsome h).mpr (hh h).2⟩

/-! ### Counting over numbers -/

/-- The coins of a number: its `m` low bits, least significant first. -/
def coinsOf (m x : ℕ) : List Bool := (List.range m).map x.testBit

theorem ofFn_symm_equivFin (m : ℕ) (x : Fin (2 ^ m)) :
    List.ofFn ((Cslib.BitString.equivFin m).symm x) = coinsOf m x := by
  set z := (Cslib.BitString.equivFin m).symm x
  have hx : (x : ℕ) = packDigits 2 (fun i => if h : i < m then (z ⟨i, h⟩).toNat else 0) m := by
    have := Cslib.BitString.val_equivFin_eq_sum z
    rw [show Cslib.BitString.equivFin m z = x by simp [z]] at this
    rw [this, packDigits, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [dite_eq_left i.isLt]
  refine List.ext_getElem (by simp [coinsOf]) fun i h1 h2 => ?_
  have hi : i < m := by simpa using h1
  simp only [List.getElem_ofFn, coinsOf, List.getElem_map, List.getElem_range]
  rw [Nat.testBit_eq_decide_div_mod_eq, hx,
    packDigits_div_pow_mod (by norm_num) _ _ (fun j _ => by split_ifs; simp [Bool.toNat_le])]
  rw [ite_eq_left hi, dite_eq_left hi]
  cases z ⟨i, hi⟩ <;> rfl

theorem countP_range_eq_card (n : ℕ) (f : ℕ → Bool) :
    (List.range n).countP f = ((Finset.range n).filter fun x => f x = true).card := by
  rw [List.countP_eq_length_filter, Finset.card_def, Finset.filter_val, Finset.range_val,
    Multiset.range, Multiset.filter_coe, Multiset.coe_card]
  simp

theorem countP_enumList_eq (m : ℕ) (v : List Bool → Bool) :
    (Cslib.BitString.enumList m).countP v =
      (List.range (2 ^ m)).countP fun x => v (coinsOf m x) := by
  rw [Cslib.BitString.countP_enumList, countP_range_eq_card]
  refine Finset.card_bij (fun word _ => (Cslib.BitString.equivFin m word : ℕ)) ?_ ?_ ?_
  · intro word hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨Fin.isLt _, ?_⟩
    rw [← ofFn_symm_equivFin, Equiv.symm_apply_apply]
    exact hw
  · intro a _ b _ h
    exact (Cslib.BitString.equivFin m).injective (Fin.ext h)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx
    refine ⟨(Cslib.BitString.equivFin m).symm ⟨x, hx.1⟩, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [ofFn_symm_equivFin]
    exact hx.2

/-- **The interval count over numbers.** -/
theorem localIntervalCount_eq [DecidableEq State] (b : ℕ) (input : List Bool)
    (J : Option (Fin k) → ℤ) (δ : Option (Fin k) → SignType) (cIn : ControlData k State)
    (wIn : Fin k → List (Option Bool)) (cOut : ControlData k State)
    (wOut : Fin k → List (Option Bool)) [∀ n, Decidable (NCond e b J δ cOut wOut n)] :
    machine.localIntervalCount b input J δ cIn wIn cOut wOut =
      (List.range (2 ^ b)).countP fun x =>
        decide (NCond e b J δ cOut wOut
          (nRun e machine input (coinsOf b x) (nStart e b input J cIn wIn))) := by
  rw [localIntervalCount, countP_enumList_eq]
  refine List.countP_congr fun x _ => ?_
  simp only [decide_eq_true_eq]
  exact stepData_iff b input J δ cIn wIn cOut wOut _ (by simp [coinsOf])

end Cslib.Complexity.NtimeDspace.LocalSim
