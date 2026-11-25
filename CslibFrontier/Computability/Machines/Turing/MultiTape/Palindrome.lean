/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Deterministic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.TapeLemmas
public import CslibFrontier.Computability.Machines.Turing.SingleTape.Palindrome
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.WordsCfg

/-!
# Palindromes in linear time with one work tape, and the one-tape/two-tape separation

A multi-tape machine with one work tape decides palindromes over `Bool` in `3n + 3` steps
(`Turing.MultiTapeTM.palindromeDecider`). It copies the input onto the work tape, rewinds the work
tape, and then walks the input head from the right end of the input to the left while the work
head walks from the left end of the copy to the right, comparing the two symbols read. It halts
with output `true` when the input head runs off the left end, and with `false` at the first
mismatch.

Together with the quadratic lower bound for single-tape machines
(`Cslib.Turing.SingleTapeTM.palindrome_lower_bound`), this separates the two models: a language
decided in linear time by a machine with an input tape and one work tape needs time `Ω(n²)` on
every single-tape machine (`palindrome_tape_separation`). So no simulation of multi-tape machines
on one tape has subquadratic overhead in general, and the quadratic simulation
`Turing.MultiTapeTM.outputsWithinTime_toSingleTape` is optimal up to the constant. The lower bound
is Hennie's [Hennie1965]; the decider is the standard copy-and-compare algorithm.

## Main definitions

* `Turing.MultiTapeTM.palindromeDecider`: the decider, with states `PalState`.

## Main results

* `Turing.MultiTapeTM.computesInTimeAndSpace_palindromeDecider`: on every input `x`, it outputs
  whether `x` is a palindrome within `3 |x| + 3` steps and `3 |x| + 4` work cells.
* `Turing.MultiTapeTM.decidableInTimeAndSpace_palindrome`: palindromes are decidable in linear
  time and space by a binary multi-tape machine.
* `Turing.MultiTapeTM.palindrome_tape_separation`: the separation from single-tape machines.

## References

* [F. C. Hennie, *One-tape, off-line Turing machine computations*][Hennie1965]
-/

@[expose] public section

namespace Turing.MultiTapeTM

/-- The phases of `palindromeDecider`: copying the input, rewinding the work tape, and comparing. -/
inductive PalState
  /-- Copy the input onto the work tape. -/
  | copy
  /-- Rewind the work head to the start of the copy. -/
  | rewind
  /-- Compare the input, read right to left, with the copy, read left to right. -/
  | cmp
  deriving DecidableEq

instance : Fintype PalState := ⟨{.copy, .rewind, .cmp}, by intro q; cases q <;> simp⟩

/-- The transition table of `palindromeDecider`. -/
def palTr : PalState → Option Bool → (Fin 1 → Option Bool) → Action 1 Bool PalState
  | .copy, some a, _ => ⟨1, fun _ => (some (some a), 1), none, some .copy⟩
  | .copy, none, _ => ⟨-1, fun _ => (none, -1), none, some .rewind⟩
  | .rewind, _, w =>
    match w 0 with
    | none => ⟨0, fun _ => (none, 1), none, some .cmp⟩
    | some _ => ⟨0, fun _ => (none, -1), none, some .rewind⟩
  | .cmp, none, _ => ⟨0, fun _ => (none, 0), some true, none⟩
  | .cmp, some a, w =>
    if w 0 = some a then ⟨-1, fun _ => (none, 1), none, some .cmp⟩
    else ⟨0, fun _ => (none, 0), some false, none⟩

/-- A machine with one work tape deciding palindromes over `Bool` in linear time. -/
noncomputable def palindromeDecider : MultiTapeTM 1 Bool PalState := ofTr .copy palTr

variable {x : List Bool}

/-- The configuration of `palindromeDecider` with the given state, input position, work tape,
work head and output. -/
def palCfg (x : List Bool) (q : Option PalState) (p : Fin (x.length + 2)) (tape : ℤ → Option Bool)
    (pos : ℤ) (out : List Bool) : Cfg 1 Bool PalState x :=
  ⟨q, p, fun _ => tape, fun _ => pos, out⟩

private lemma step_palCfg {q : PalState} {p : Fin (x.length + 2)} {tape : ℤ → Option Bool}
    {pos : ℤ} {out : List Bool} :
    palindromeDecider.step (palCfg x (some q) p tape pos out) =
      (palTr q (palCfg x (some q) p tape pos out).inputSymbol (fun _ => tape pos)).apply
        (palCfg x (some q) p tape pos out) := by
  rw [step_of_state rfl]
  simp only [palindromeDecider, tr_ofTr]
  rfl

private lemma apply_palCfg (a : Action 1 Bool PalState) {q : Option PalState}
    {p : Fin (x.length + 2)} {tape : ℤ → Option Bool} {pos : ℤ} {out : List Bool} :
    a.apply (palCfg x q p tape pos out) = palCfg x a.state (moveInputPos p a.inputTape)
      ((a.workTapes 0).1.elim tape (Function.update tape pos)) (pos + (a.workTapes 0).2)
      (out ++ a.output.toList) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    rw [Fin.fin_one_eq_zero i]
    simp only [Action.apply, palCfg]
    cases (a.workTapes 0).1 <;> rfl
  · funext i
    rw [Fin.fin_one_eq_zero i]
    rfl

private lemma moveInputPos_one_val {n : ℕ} (p : Fin (n + 2)) (h : p.val ≠ n + 1) :
    (moveInputPos p 1).val = p.val + 1 := by
  rw [show (1 : SignType) = .pos from rfl, moveInputPos_pos_of_ne_right p h]

private lemma moveInputPos_neg_one_val {n : ℕ} (p : Fin (n + 2)) (h : p.val ≠ 0) :
    (moveInputPos p (-1)).val = p.val - 1 := by
  rw [show (-1 : SignType) = .neg from rfl,
    moveInputPos_neg_of_ne_left p fun h' => h (by subst h'; rfl)]

private lemma update_tapeOfList_take {i : ℕ} (hi : i < x.length) :
    Function.update (tapeOfList (x.take i)) (i : ℤ) (some x[i]) = tapeOfList (x.take (i + 1)) := by
  funext z
  rcases z with m | m
  · by_cases hm : m = i
    · subst hm
      simp [Function.update]
    · have : (Int.ofNat m) ≠ (i : ℤ) := by simpa using hm
      rw [Function.update_of_ne this]
      change (x.take i)[m]? = (x.take (i + 1))[m]?
      simp only [List.getElem?_take]
      split_ifs <;> first | rfl | omega
  · rfl

private lemma inputSymbol_palCfg {q : Option PalState} {tape : ℤ → Option Bool} {pos : ℤ}
    {out : List Bool} {p : Fin (x.length + 2)} {i : ℕ} (hp : p.val = i + 1) (hi : i < x.length) :
    (palCfg x q p tape pos out).inputSymbol = some x[i] :=
  inputSymbolInner i (by change p.val = 1 + i; omega) hi

private lemma inputSymbol_palCfg_boundary {q : Option PalState} {tape : ℤ → Option Bool}
    {pos : ℤ} {out : List Bool} {p : Fin (x.length + 2)} (hp : p.val = 0 ∨ p.val = x.length + 1) :
    (palCfg x q p tape pos out).inputSymbol = none :=
  inputSymbol_eq_none_of_boundary hp

/-- The copy phase: after `i ≤ |x|` steps, the first `i` symbols are on the work tape. -/
lemma runFrom_copy {i : ℕ} (hi : i ≤ x.length) :
    palindromeDecider.runFrom (palindromeDecider.initCfg x) i =
      palCfg x (some .copy) ⟨i + 1, by omega⟩ (tapeOfList (x.take i)) i [] := by
  induction i with
  | zero =>
    refine Cfg.ext rfl (Fin.ext ?_) ?_ rfl rfl
    · exact (Fin.val_one' _).trans (Nat.mod_eq_of_lt (by omega))
    · funext _ z
      rcases z with _ | _ <;> simp [MultiTapeNTM.initCfg, Cfg.init, palCfg, runFrom]
  | succ i ih =>
    have hi' : i < x.length := by omega
    rw [runFrom_succ, ih hi'.le, step_palCfg, inputSymbol_palCfg rfl hi', apply_palCfg]
    simp only [palTr, Option.elim_some, List.append_nil, Option.toList_none]
    rw [update_tapeOfList_take hi']
    congr 1
    · exact Fin.ext (moveInputPos_one_val _ (by simp; omega))

/-- After the copy, the input head steps back onto the last symbol and the rewind starts. -/
lemma runFrom_copy_end :
    palindromeDecider.runFrom (palindromeDecider.initCfg x) (x.length + 1) =
      palCfg x (some .rewind) ⟨x.length, by omega⟩ (tapeOfList x) ((x.length : ℤ) - 1) [] := by
  rw [runFrom_succ, runFrom_copy le_rfl, step_palCfg,
    inputSymbol_palCfg_boundary (Or.inr rfl), apply_palCfg, List.take_length]
  simp only [palTr, Option.elim_none, List.append_nil, Option.toList_none]
  congr 1
  · exact Fin.ext ((moveInputPos_neg_one_val _ (by simp)).trans (by simp))

/-- The rewind: the work head walks left over the copy. -/
lemma runFrom_rewind {j : ℕ} (hj : j ≤ x.length) :
    palindromeDecider.runFrom
        (palCfg x (some .rewind) ⟨x.length, by omega⟩ (tapeOfList x) ((x.length : ℤ) - 1) []) j =
      palCfg x (some .rewind) ⟨x.length, by omega⟩ (tapeOfList x) ((x.length : ℤ) - 1 - j) [] := by
  induction j with
  | zero => simp [runFrom]
  | succ j ih =>
    rw [runFrom_succ, ih (by omega), step_palCfg, apply_palCfg]
    obtain ⟨a, ha⟩ : ∃ a, tapeOfList x ((x.length : ℤ) - 1 - j) = some a := by
      have : ((x.length : ℤ) - 1 - j) = ((x.length - 1 - j : ℕ) : ℤ) := by omega
      rw [this, tapeOfList_ofNat]
      exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
    simp only [palTr, ha, Option.elim_none, List.append_nil, Option.toList_none, moveInputPos_zero]
    congr 1
    simp only [SignType.coe_neg_one]
    push_cast
    omega

/-- The rewind ends on the blank left of the copy, and the comparison starts at its first cell. -/
lemma runFrom_rewind_end :
    palindromeDecider.runFrom (palindromeDecider.initCfg x) (2 * x.length + 2) =
      palCfg x (some .cmp) ⟨x.length, by omega⟩ (tapeOfList x) 0 [] := by
  rw [show 2 * x.length + 2 = (x.length + 1) + x.length + 1 by omega, runFrom_succ, runFrom_add,
    runFrom_copy_end, runFrom_rewind le_rfl, step_palCfg, apply_palCfg]
  have hw : tapeOfList x ((x.length : ℤ) - 1 - x.length) = none := by
    rw [show (x.length : ℤ) - 1 - x.length = Int.negSucc 0 by omega]
    rfl
  simp only [palTr, hw, Option.elim_none, List.append_nil, Option.toList_none, moveInputPos_zero]
  congr 1
  simp

/-- The comparison: while the symbols agree, the input head walks left and the work head right. -/
lemma runFrom_cmp {i : ℕ} (hi : i ≤ x.length) (hagree : ∀ j < i, x[x.length - 1 - j]? = x[j]?) :
    palindromeDecider.runFrom (palCfg x (some .cmp) ⟨x.length, by omega⟩ (tapeOfList x) 0 []) i =
      palCfg x (some .cmp) ⟨x.length - i, by omega⟩ (tapeOfList x) i [] := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [runFrom_succ, ih (by omega) fun j hj => hagree j (by omega), step_palCfg,
      inputSymbol_palCfg (i := x.length - 1 - i) (by simp; omega) (by omega), apply_palCfg]
    have hw : tapeOfList x (i : ℤ) = some x[x.length - 1 - i] := by
      rw [tapeOfList_ofNat, ← hagree i (by omega), List.getElem?_eq_getElem]
    simp only [palTr, hw, ↓reduceIte, Option.elim_none, List.append_nil, Option.toList_none]
    congr 1
    · exact Fin.ext ((moveInputPos_neg_one_val _ (by simp; omega)).trans (by simp; omega))

private lemma palindrome_iff_agree :
    x.Palindrome ↔ ∀ j < x.length, x[x.length - 1 - j]? = x[j]? := by
  rw [List.Palindrome.iff_reverse_eq]
  constructor
  · intro h j hj
    conv_rhs => rw [← h]
    rw [List.getElem?_reverse hj]
  · intro h
    refine List.ext_getElem? fun j => ?_
    by_cases hj : j < x.length
    · rw [List.getElem?_reverse hj, h j hj]
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

/-- On every input, the decider halts within `3 |x| + 3` steps with output `[true]` on
palindromes and `[false]` otherwise. -/
theorem runFrom_palindromeDecider (x : List Bool) :
    (palindromeDecider.runFrom (palindromeDecider.initCfg x) (3 * x.length + 3)).Halted ∧
      (palindromeDecider.runFrom (palindromeDecider.initCfg x) (3 * x.length + 3)).output =
        [decide x.Palindrome] := by
  -- `i` is the number of agreeing comparisons before the run halts
  obtain ⟨i, hi, hagree, hstop⟩ : ∃ i ≤ x.length, (∀ j < i, x[x.length - 1 - j]? = x[j]?) ∧
      (i = x.length ∨ i < x.length ∧ x[x.length - 1 - i]? ≠ x[i]?) := by
    by_cases hall : ∀ j < x.length, x[x.length - 1 - j]? = x[j]?
    · exact ⟨x.length, le_rfl, hall, Or.inl rfl⟩
    · have hex : ∃ i, i < x.length ∧ x[x.length - 1 - i]? ≠ x[i]? := by
        by_contra hc
        exact hall fun j hj => by_contra fun h => hc ⟨j, hj, h⟩
      refine ⟨Nat.find hex, (Nat.find_spec hex).1.le, fun j hj => ?_, Or.inr (Nat.find_spec hex)⟩
      by_contra h
      exact Nat.find_min hex hj ⟨by have := (Nat.find_spec hex).1; omega, h⟩
  have hrun : palindromeDecider.runFrom (palindromeDecider.initCfg x) (2 * x.length + 2 + i + 1) =
      palCfg x none ⟨x.length - i, by omega⟩ (tapeOfList x) i [decide x.Palindrome] := by
    rw [runFrom_succ, runFrom_add, runFrom_rewind_end, runFrom_cmp hi hagree, step_palCfg]
    rcases hstop with rfl | hne
    · have hpal : x.Palindrome := palindrome_iff_agree.2 hagree
      rw [inputSymbol_palCfg_boundary (Or.inl (by simp)), apply_palCfg]
      simp only [palTr, Option.elim_none, moveInputPos_zero, SignType.coe_zero, add_zero,
        List.nil_append, Option.toList_some, hpal, decide_true]
    · obtain ⟨hi', hne⟩ := hne
      have hnp : ¬ x.Palindrome := fun h => hne (palindrome_iff_agree.1 h i hi')
      have hw : tapeOfList x (i : ℤ) ≠ some x[x.length - 1 - i] := by
        rw [tapeOfList_ofNat, ← List.getElem?_eq_getElem]
        exact Ne.symm hne
      rw [inputSymbol_palCfg (i := x.length - 1 - i) (by simp; omega) (by omega), apply_palCfg]
      simp only [palTr, hw, ↓reduceIte, Option.elim_none, moveInputPos_zero, SignType.coe_zero,
        add_zero, List.nil_append, Option.toList_some, hnp, decide_false]
  have hhalt : (palindromeDecider.runFrom (palindromeDecider.initCfg x)
      (2 * x.length + 2 + i + 1)).state = none := by rw [hrun]; rfl
  rw [runFrom_eq_of_halt _ _ (by omega) hhalt, hrun]
  exact ⟨rfl, rfl⟩

/-- The decider outputs whether its input is a palindrome within `3 |x| + 3` steps and
`3 |x| + 4` work cells. -/
theorem computesInTimeAndSpace_palindromeDecider (x : List Bool) :
    palindromeDecider.ComputesInTimeAndSpace x [decide x.Palindrome] (3 * x.length + 3)
      (3 * x.length + 4) := by
  obtain ⟨hhalt, hout⟩ := runFrom_palindromeDecider x
  refine ⟨⟨_, hhalt, hout⟩, runsInTime_of_halted hhalt, runsInSpace_of_halted hhalt ?_⟩
  exact (MultiTapeNTM.RunPath.space_le_mul_time_add_one
    (.ofDeterministic _ _ (3 * x.length + 3))).trans_eq
      (show 1 * (3 * x.length + 3 + 1) = 3 * x.length + 4 by omega)

/-- Palindromes over `Bool` are decidable in linear time and space by a binary multi-tape
machine (with one work tape). -/
theorem decidableInTimeAndSpace_palindrome :
    DecidableInTimeAndSpace {x : List Bool | x.Palindrome} (Function.Embedding.refl _)
      (fun x => 3 * x.length + 3) (fun x => 3 * x.length + 4) :=
  ⟨1, PalState, inferInstance, palindromeDecider, fun x => by
    have hind : indicator {x : List Bool | x.Palindrome} x = decide x.Palindrome := by
      unfold indicator
      split_ifs with h <;> simp_all
    simpa [hind] using computesInTimeAndSpace_palindromeDecider x⟩

/-- **The one-tape/two-tape time separation.** Palindromes over `Bool` are decided in `3n + 3`
steps by a multi-tape machine with a read-only input tape and one work tape, while every
single-tape machine deciding them (answering under its head, through any letter map) needs
`n² ≤ 64 d T(n)` for all `n ≥ 8 d`, where `d = ⌈log₂ (|Q| + 2)⌉` for its state set `Q`. -/
theorem palindrome_tape_separation :
    (∀ x : List Bool, palindromeDecider.ComputesInTimeAndSpace x [decide x.Palindrome]
      (3 * x.length + 3) (3 * x.length + 4)) ∧
    ∀ {Symbol : Type} [Inhabited Symbol] [Fintype Symbol] (tm : Cslib.Turing.SingleTapeTM Symbol)
      (ι : Bool → Symbol) (yes : Symbol) (T : ℕ → ℕ),
      tm.DecidesByHeadInTime ι {w : List Bool | w.Palindrome} yes T →
      ∀ n, 8 * Nat.clog 2 (Fintype.card tm.State + 2) ≤ n →
        n ^ 2 ≤ 64 * Nat.clog 2 (Fintype.card tm.State + 2) * T n :=
  ⟨computesInTimeAndSpace_palindromeDecider, fun tm _ _ _ hdec _ hn =>
    tm.palindrome_lower_bound hdec hn⟩

end Turing.MultiTapeTM
