/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.EditDistance.Basic

/-!
# Longest common subsequence

The length of a longest common subsequence of two words, computed by the dynamic program of
[CLRS, Section 15.4][CLRS2009] (the same table as [Wagner and Fischer][WagnerFischer1974], with
letter matches rewarded instead of operations charged). A subsequence is a sublist in the sense of
`List.Sublist`: a word obtained by deleting letters, not necessarily consecutive.

`Cslib.Algorithms.Lean.EditDistance.lcsLength x y` is the table entry, and
`Cslib.Algorithms.Lean.EditDistance.isGreatest_lcsLength` proves that it is the greatest length of
a common subsequence; `Cslib.Algorithms.Lean.EditDistance.lcs` reads one off the table. The two
problems are dual: under `Costs.indel` (`1` per insertion or deletion, `2` per replacement by a
different letter) the edit distance is `|x| + |y| - 2 · lcsLength x y`
(`Cslib.Algorithms.Lean.EditDistance.editDist_indel_add_two_mul`). Replacements by a different
letter are allowed, and `optScript Costs.indel` may return them, but splitting each into a deletion
and an insertion keeps the cost, so this is also the least cost of a script without them
(`Cslib.Algorithms.Lean.EditDistance.isLeast_editDist_indel`): the insertion–deletion distance.

## Main definitions

* `Cslib.Algorithms.Lean.EditDistance.lcsLength`: the table entry.
* `Cslib.Algorithms.Lean.EditDistance.lcs`: a longest common subsequence, by traceback.
* `Cslib.Algorithms.Lean.EditDistance.EditScript.kept`: the letters a script keeps.
* `Cslib.Algorithms.Lean.EditDistance.EditScript.IsIndel`: a script with no replacement by a
  different letter; `EditScript.splitSubs` turns a script into one.

## Main results

* `Cslib.Algorithms.Lean.EditDistance.length_le_lcsLength`: every common subsequence has length at
  most `lcsLength x y` (`lcsLength_le_left` and `lcsLength_le_right` bound `lcsLength x y` by `|x|`
  and `|y|`).
* `Cslib.Algorithms.Lean.EditDistance.lcs_spec`: `lcs x y` is a common subsequence of length
  `lcsLength x y`.
* `Cslib.Algorithms.Lean.EditDistance.isGreatest_lcsLength`: `lcsLength x y` is the greatest
  length of a common subsequence.
* `Cslib.Algorithms.Lean.EditDistance.editDist_indel_add_two_mul`:
  `editDist Costs.indel x y + 2 · lcsLength x y = |x| + |y|`.
* `Cslib.Algorithms.Lean.EditDistance.isLeast_editDist_indel`: `editDist Costs.indel x y` is the
  least cost of a script from `x` to `y` with no replacement by a different letter.

Word-RAM running-time bounds for longest-common-subsequence length are proved in
`CslibFrontier.Algorithms.WordRAM.EditDistance`.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
* [R. A. Wagner and M. J. Fischer, *The string-to-string correction problem*][WagnerFischer1974]
-/

public section

namespace Cslib.Algorithms.Lean.EditDistance

open scoped List

variable {α : Type*} [DecidableEq α]

/-- The longest-common-subsequence table, over pairs of suffixes. -/
@[expose] def lcsTable : GridDP α ℕ where
  nilNil := 0
  consNil _ d := d
  nilCons _ d := d
  consCons a b d u l := if a = b then d + 1 else max u l

/-- The length of a longest common subsequence of `x` and `y`: the table entry. -/
@[expose] def lcsLength (x y : List α) : ℕ := lcsTable.value x y

@[simp] theorem lcsLength_nil_left (y : List α) : lcsLength [] y = 0 := by
  induction y with
  | nil => rfl
  | cons b y ih => exact (lcsTable.value_nil_cons b y).trans ih

@[simp] theorem lcsLength_nil_right (x : List α) : lcsLength x [] = 0 := by
  induction x with
  | nil => rfl
  | cons a x ih => exact (lcsTable.value_cons_nil a x).trans ih

/-- The recurrence of [CLRS, Theorem 15.1][CLRS2009]. -/
theorem lcsLength_cons_cons (a b : α) (x y : List α) :
    lcsLength (a :: x) (b :: y) =
      if a = b then lcsLength x y + 1 else max (lcsLength x (b :: y)) (lcsLength (a :: x) y) :=
  lcsTable.value_cons_cons a b x y

/-- Every common subsequence of `x` and `y` has length at most `lcsLength x y`. -/
theorem length_le_lcsLength : ∀ {x y z : List α}, z <+ x → z <+ y → z.length ≤ lcsLength x y
  | [], _, z, hx, _ => by simp [List.sublist_nil.1 hx]
  | _ :: _, [], z, _, hy => by simp [List.sublist_nil.1 hy]
  | a :: x, b :: y, [], _, _ => Nat.zero_le _
  | a :: x, b :: y, c :: z, hx, hy => by
    rw [lcsLength_cons_cons]
    split_ifs with hab
    · subst hab
      have := length_le_lcsLength hx.of_cons_cons hy.of_cons_cons
      rw [List.length_cons]
      omega
    · by_cases hca : c = a
      · subst hca
        exact (length_le_lcsLength hx (hy.of_cons_of_ne hab)).trans (le_max_right _ _)
      · exact (length_le_lcsLength (hx.of_cons_of_ne hca) hy).trans (le_max_left _ _)
termination_by x y => x.length + y.length

/-- A longest common subsequence of `x` and `y`, read off the table. Ties prefer dropping the
first letter of `x`. This is a specification for proofs and `decide`: each choice consults the
entries `lcsLength x' y'` directly instead of a stored table, so it is not the linear-time
traceback, which is not formalized. -/
@[expose] def lcs : List α → List α → List α
  | [], _ => []
  | a :: x, y => lcsAux a x (lcs x) y
where
  /-- The longest common subsequences of `a :: x`, given those of `x`. -/
  lcsAux (a : α) (x : List α) (f : List α → List α) : List α → List α
    | [] => []
    | b :: y =>
      if a = b then a :: f y
      else if lcsLength (a :: x) y ≤ lcsLength x (b :: y) then f (b :: y)
      else lcsAux a x f y

@[simp] theorem lcs_nil_left (y : List α) : lcs [] y = [] := rfl

@[simp] theorem lcs_nil_right (x : List α) : lcs x [] = [] := by
  cases x <;> rfl

theorem lcs_cons_cons (a b : α) (x y : List α) :
    lcs (a :: x) (b :: y) =
      if a = b then a :: lcs x y
      else if lcsLength (a :: x) y ≤ lcsLength x (b :: y) then lcs x (b :: y)
      else lcs (a :: x) y := rfl

/-- `lcs x y` is a common subsequence of `x` and `y` of length `lcsLength x y`. -/
theorem lcs_spec : ∀ x y : List α,
    lcs x y <+ x ∧ lcs x y <+ y ∧ (lcs x y).length = lcsLength x y
  | [], y => ⟨List.nil_sublist _, List.nil_sublist _, (lcsLength_nil_left y).symm⟩
  | a :: x, [] => by
    rw [lcs_nil_right, lcsLength_nil_right]
    exact ⟨List.nil_sublist _, List.nil_sublist _, rfl⟩
  | a :: x, b :: y => by
    rw [lcs_cons_cons, lcsLength_cons_cons]
    split_ifs with hab h
    · subst hab
      obtain ⟨h1, h2, h3⟩ := lcs_spec x y
      exact ⟨h1.cons_cons a, h2.cons_cons a, by rw [List.length_cons, h3]⟩
    · obtain ⟨h1, h2, h3⟩ := lcs_spec x (b :: y)
      exact ⟨h1.cons a, h2, by rw [h3]; omega⟩
    · obtain ⟨h1, h2, h3⟩ := lcs_spec (a :: x) y
      exact ⟨h1, h2.cons b, by rw [h3]; omega⟩
termination_by x y => x.length + y.length

/-- `lcsLength x y` is the greatest length of a common subsequence of `x` and `y`. -/
theorem isGreatest_lcsLength (x y : List α) :
    IsGreatest {k | ∃ z : List α, z <+ x ∧ z <+ y ∧ z.length = k} (lcsLength x y) := by
  refine ⟨⟨lcs x y, lcs_spec x y⟩, ?_⟩
  rintro k ⟨z, hx, hy, rfl⟩
  exact length_le_lcsLength hx hy

theorem lcsLength_le_left (x y : List α) : lcsLength x y ≤ x.length := by
  obtain ⟨hx, _, hlen⟩ := lcs_spec x y
  exact hlen ▸ hx.length_le

theorem lcsLength_le_right (x y : List α) : lcsLength x y ≤ y.length := by
  obtain ⟨_, hy, hlen⟩ := lcs_spec x y
  exact hlen ▸ hy.length_le

/-! ### Insertion–deletion distance -/

open EditScript

namespace EditScript

/-- The letters a script keeps: the targets of its replacements of a letter by itself. -/
def kept : EditScript α → List α
  | [] => []
  | .del _ :: s => kept s
  | .ins _ :: s => kept s
  | .sub a b :: s => if a = b then a :: kept s else kept s

theorem kept_sublist_src : ∀ s : EditScript α, s.kept <+ s.src
  | [] => by rw [kept, src_nil]
  | .del a :: s => by simpa [kept, src_cons, EditOp.src] using (kept_sublist_src s).cons a
  | .ins _ :: s => by simpa [kept, src_cons, EditOp.src] using kept_sublist_src s
  | .sub a b :: s => by
    rw [kept, src_cons]
    split_ifs
    · exact (kept_sublist_src s).cons_cons a
    · exact (kept_sublist_src s).cons a

theorem kept_sublist_tgt : ∀ s : EditScript α, s.kept <+ s.tgt
  | [] => by rw [kept, tgt_nil]
  | .del _ :: s => by simpa [kept, tgt_cons, EditOp.tgt] using kept_sublist_tgt s
  | .ins b :: s => by simpa [kept, tgt_cons, EditOp.tgt] using (kept_sublist_tgt s).cons b
  | .sub a b :: s => by
    rw [kept, tgt_cons]
    split_ifs with h
    · exact h ▸ (kept_sublist_tgt s).cons_cons a
    · exact (kept_sublist_tgt s).cons b

/-- Under `Costs.indel`, a script costs `|src| + |tgt|` less twice the number of letters it
keeps. -/
theorem cost_indel_add_two_mul : ∀ s : EditScript α,
    s.cost Costs.indel + 2 * s.kept.length = s.src.length + s.tgt.length := by
  intro s
  induction s with
  | nil => rw [cost_nil, kept, src_nil, tgt_nil]; rfl
  | cons op s ih =>
    cases op with
    | del a | ins b =>
      simp only [cost_cons, kept, src_cons, tgt_cons, EditOp.cost, EditOp.src, EditOp.tgt,
        Costs.indel_del, Costs.indel_ins, List.length_append, List.length_singleton,
        List.length_nil]
      omega
    | sub a b =>
      simp only [cost_cons, kept, src_cons, tgt_cons, EditOp.cost, EditOp.src, EditOp.tgt,
        Costs.indel_sub, List.length_append, List.length_singleton]
      split_ifs
      · rw [List.length_cons]; omega
      · omega

/-- A script with no replacement by a different letter: each operation is an insertion, a
deletion, or keeps a letter. -/
def IsIndel (s : EditScript α) : Prop := ∀ o ∈ s, ∀ a b, o = .sub a b → a = b

omit [DecidableEq α] in
theorem isIndel_nil : IsIndel ([] : EditScript α) := fun _ h => nomatch h

omit [DecidableEq α] in
theorem isIndel_cons {o : EditOp α} {s : EditScript α} :
    IsIndel (o :: s) ↔ (∀ a b, o = .sub a b → a = b) ∧ IsIndel s :=
  List.forall_mem_cons

/-- Split each replacement by a different letter into a deletion followed by an insertion. -/
def splitSubs : EditScript α → EditScript α
  | [] => []
  | .del a :: s => .del a :: splitSubs s
  | .ins b :: s => .ins b :: splitSubs s
  | .sub a b :: s => if a = b then .sub a b :: splitSubs s else .del a :: .ins b :: splitSubs s

theorem src_splitSubs : ∀ s : EditScript α, (splitSubs s).src = s.src := by
  intro s
  fun_induction splitSubs s <;> simp_all [src_cons, EditOp.src]

theorem tgt_splitSubs : ∀ s : EditScript α, (splitSubs s).tgt = s.tgt := by
  intro s
  fun_induction splitSubs s <;> simp_all [tgt_cons, EditOp.tgt]

/-- Under `Costs.indel`, splitting replacements keeps the cost. -/
theorem cost_indel_splitSubs : ∀ s : EditScript α,
    (splitSubs s).cost Costs.indel = s.cost Costs.indel := by
  intro s
  fun_induction splitSubs s <;>
    simp_all [cost_cons, EditOp.cost, Costs.indel_del, Costs.indel_ins, Costs.indel_sub]
  omega

theorem isIndel_splitSubs : ∀ s : EditScript α, (splitSubs s).IsIndel := by
  intro s
  fun_induction splitSubs s with
  | case1 => exact isIndel_nil
  | case2 _ _ ih | case3 _ _ ih =>
    exact isIndel_cons.2 ⟨fun _ _ h => (nomatch h), ih⟩
  | case4 _ _ ih =>
    exact isIndel_cons.2 ⟨fun _ _ h' => by cases h'; rfl, ih⟩
  | case5 _ _ _ _ ih =>
    exact isIndel_cons.2 ⟨fun _ _ h => (nomatch h),
      isIndel_cons.2 ⟨fun _ _ h => (nomatch h), ih⟩⟩

end EditScript

theorem editDist_indel_nil_right (x : List α) : editDist Costs.indel x [] = x.length := by
  induction x with
  | nil => rfl
  | cons a x ih => rw [editDist_cons_nil, ih, List.length_cons, Nat.add_comm]; rfl

theorem editDist_indel_nil_left (y : List α) : editDist Costs.indel [] y = y.length := by
  induction y with
  | nil => rfl
  | cons b y ih => rw [editDist_nil_cons, ih, List.length_cons, Nat.add_comm]; rfl

/-- Deleting every letter of `x` and inserting every letter of `y`. -/
theorem editDist_indel_le_length_add (x y : List α) :
    editDist Costs.indel x y ≤ x.length + y.length := by
  simpa [Costs.indel] using editDist_le_sum_del_ins (Costs.indel (α := α)) x y

/-- A common subsequence `z` of `x` and `y` gives a script keeping `z`. -/
theorem editDist_indel_add_two_mul_le : ∀ {x y z : List α}, z <+ x → z <+ y →
    editDist Costs.indel x y + 2 * z.length ≤ x.length + y.length
  | [], y, z, hx, _ => by simp [List.sublist_nil.1 hx, editDist_indel_nil_left]
  | a :: x, [], z, _, hy => by simp [List.sublist_nil.1 hy, editDist_indel_nil_right]
  | a :: x, b :: y, [], _, _ => by simpa using editDist_indel_le_length_add (a :: x) (b :: y)
  | a :: x, b :: y, c :: z, hx, hy => by
    by_cases hca : c = a
    · subst hca
      by_cases hcb : c = b
      · subst hcb
        have := editDist_indel_add_two_mul_le hx.of_cons_cons hy.of_cons_cons
        have h' := editDist_cons_cons_le Costs.indel c c x y
        rw [Costs.indel_sub_self] at h'
        simp only [List.length_cons] at this ⊢
        omega
      · have := editDist_indel_add_two_mul_le hx (hy.of_cons_of_ne hcb)
        have h' := editDist_cons_right_le Costs.indel b (c :: x) y
        simp only [Costs.indel_ins, List.length_cons] at this h' ⊢
        omega
    · have := editDist_indel_add_two_mul_le (hx.of_cons_of_ne hca) hy
      have h' := editDist_cons_left_le Costs.indel a x (b :: y)
      simp only [Costs.indel_del, List.length_cons] at this h' ⊢
      omega
termination_by x y => x.length + y.length

/-- Under `Costs.indel`, the edit distance is `|x| + |y| - 2 · lcsLength x y`. By
`isLeast_editDist_indel`, it is also the least number of insertions and deletions in a script
from `x` to `y`. -/
theorem editDist_indel_add_two_mul (x y : List α) :
    editDist Costs.indel x y + 2 * lcsLength x y = x.length + y.length := by
  obtain ⟨h1, h2, h3⟩ := lcs_spec x y
  have hk := (optScript Costs.indel x y).cost_indel_add_two_mul
  have hle := length_le_lcsLength (optScript Costs.indel x y).kept_sublist_src
    (optScript Costs.indel x y).kept_sublist_tgt
  rw [src_optScript, tgt_optScript, cost_optScript] at hk
  rw [src_optScript, tgt_optScript] at hle
  have := h3 ▸ editDist_indel_add_two_mul_le h1 h2
  omega

/-- Under `Costs.indel`, replacements by a different letter gain nothing: `editDist Costs.indel x y`
is the least cost of a script from `x` to `y` with no such replacement, that is, the least number
of insertions and deletions turning `x` into `y`. The witness splits the replacements of
`optScript Costs.indel x y`. -/
theorem isLeast_editDist_indel (x y : List α) :
    IsLeast {c | ∃ s : EditScript α, s.IsIndel ∧ s.src = x ∧ s.tgt = y ∧ s.cost Costs.indel = c}
      (editDist Costs.indel x y) :=
  ⟨⟨splitSubs (optScript Costs.indel x y), isIndel_splitSubs _,
    (src_splitSubs _).trans (src_optScript _ _ _), (tgt_splitSubs _).trans (tgt_optScript _ _ _),
    (cost_indel_splitSubs _).trans (cost_optScript _ _ _)⟩,
    fun _ ⟨s, _, hx, hy, hc⟩ => hc ▸ hx ▸ hy ▸ editDist_le_cost Costs.indel s⟩

end Cslib.Algorithms.Lean.EditDistance
