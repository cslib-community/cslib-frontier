/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Finset.Card
import CslibFrontier.Foundations.Analysis.SpecialFunctions.LogSum
import CslibFrontier.Tactic.LinarithCast
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Complete Binary Tree Cover Bound

This module formalizes the minimal covering set `cover S` of a leaf subset `S` in a complete
binary tree of height `h` (`n = 2 ^ h` leaves) and proves the logarithmic cover-size bound of
[BonehShoup2023], Section 5.6 (Definition 5.4 and Theorem 5.8, pp. 206–207).

## Main definitions

* `Cslib.CompleteBinaryTree.Node`: nodes `(level, index)` in a complete binary tree of height `h`.
* `Cslib.CompleteBinaryTree.Covers`: `Covers W S` holds when the leaves descending from `W` are
  precisely `S`.
* `Cslib.CompleteBinaryTree.cover`: canonical minimal covering set `cover S` of `S`.

## Main results

* `Cslib.CompleteBinaryTree.covers_cover`: `cover S` covers `S`.
* `Cslib.CompleteBinaryTree.card_cover_le_of_covers`: every cover of `S` has cardinality at least
  `(cover S).card`.
* `Cslib.CompleteBinaryTree.card_cover_le`: for `1 ≤ r` and `S.card + r = 2 ^ h`,
  `(cover S).card ≤ r * Real.logb 2 (2 ^ h / r)` (Theorem 5.8).

## Deviations from [BonehShoup2023]

* Theorem 5.8 writes `|S| = n - r` with `1 ≤ r ≤ n`; here the hypothesis is stated as
  `S.card + r = 2 ^ h` together with `1 ≤ r` so `r ≤ 2 ^ h` is built in without natural-number
  subtraction truncation.
* In the `r₁ = 0` branch of the inductive proof of Theorem 5.8 ([BonehShoup2023], p. 207), the
  printed display writes `|cover(S)| = |cover(S₂)|`, omitting the `+ 1` for the full half's root;
  `card_cover_le` accounts for that `+ 1` using `1 ≤ r`.

## References

* [BonehShoup2023] Dan Boneh and Victor Shoup, *A Graduate Course in Applied Cryptography*,
  version 0.6, Section 5.6, Definition 5.4 and Theorem 5.8, pp. 206–207.
-/

public section

namespace Cslib.CompleteBinaryTree

open Finset

/-- A node in the complete binary tree of height `h` (`2 ^ h` leaves).
Nodes at `level` cover `2 ^ level` contiguous leaves; `level = 0` is a leaf and `level = h` is
the root. -/
@[ext]
structure Node (h : ℕ) where
  /-- Height above the leaf layer (`0` at leaves, `h` at the root). -/
  level : ℕ
  /-- Left-to-right index among nodes at `level`. -/
  index : ℕ
  /-- Level is bounded by the tree height. -/
  level_le : level ≤ h
  /-- Index is bounded by the number of nodes at `level`. -/
  index_lt : index < 2 ^ (h - level)
  deriving @[expose] DecidableEq

/-- The root of the complete binary tree of height `h`. -/
@[expose]
def Node.root (h : ℕ) : Node h :=
  ⟨h, 0, le_rfl, by simp⟩

/-- Leaf `i` belongs to the subtree rooted at `v` ([BonehShoup2023], Definition 5.4). -/
@[expose]
def Node.CoversLeaf {h : ℕ} (v : Node h) (i : Fin (2 ^ h)) : Prop :=
  i.val / 2 ^ v.level = v.index

instance {h : ℕ} (v : Node h) (i : Fin (2 ^ h)) : Decidable (v.CoversLeaf i) :=
  inferInstanceAs (Decidable (i.val / 2 ^ v.level = v.index))

private theorem Node.root_coversLeaf {h : ℕ} (i : Fin (2 ^ h)) : (Node.root h).CoversLeaf i := by
  simp [Node.CoversLeaf, Node.root, Nat.div_eq_of_lt i.isLt]

/-- Embedding of the left subtree of height `h` into height `h + 1`. -/
@[expose]
def Node.leftEmb {h : ℕ} : Node h ↪ Node (h + 1) where
  toFun v :=
    ⟨v.level, v.index, v.level_le.trans (Nat.le_succ h),
      v.index_lt.trans_le (Nat.pow_le_pow_right (by omega) (by omega))⟩
  inj' u v hEq := by
    cases u; cases v
    simp only [Node.mk.injEq] at hEq
    rcases hEq with ⟨rfl, rfl⟩
    rfl

/-- Embedding of the right subtree of height `h` into height `h + 1`. -/
@[expose]
def Node.rightEmb {h : ℕ} : Node h ↪ Node (h + 1) where
  toFun v :=
    ⟨v.level, 2 ^ (h - v.level) + v.index, v.level_le.trans (Nat.le_succ h), by
      have hvl : v.level ≤ h := v.level_le
      have hexp : h + 1 - v.level = (h - v.level) + 1 := by omega
      rw [hexp, pow_succ', two_mul]
      exact Nat.add_lt_add_left v.index_lt _⟩
  inj' u v hEq := by
    cases u; cases v
    simp only [Node.mk.injEq] at hEq
    rcases hEq with ⟨rfl, hidx⟩
    simp only [Nat.add_left_cancel_iff] at hidx
    subst hidx
    rfl

@[simp]
private theorem Node.level_leftEmb {h : ℕ} (v : Node h) : (Node.leftEmb v).level = v.level := rfl

@[simp]
private theorem Node.index_leftEmb {h : ℕ} (v : Node h) : (Node.leftEmb v).index = v.index := rfl

@[simp]
private theorem Node.level_rightEmb {h : ℕ} (v : Node h) : (Node.rightEmb v).level = v.level := rfl

@[simp]
private theorem Node.index_rightEmb {h : ℕ} (v : Node h) :
    (Node.rightEmb v).index = 2 ^ (h - v.level) + v.index := rfl

private theorem Node.leftEmb_ne_rightEmb {h : ℕ} (u v : Node h) :
    Node.leftEmb u ≠ Node.rightEmb v := by
  intro hEq
  have hl : u.level = v.level := congrArg (Node.level (h := h + 1)) hEq
  have hi : u.index = 2 ^ (h - v.level) + v.index := congrArg (Node.index (h := h + 1)) hEq
  have hlt := u.index_lt
  rw [hl] at hlt
  omega

private theorem nat_two_pow_add_div {a k h : ℕ} (hk : k ≤ h) :
    (2 ^ h + a) / 2 ^ k = 2 ^ (h - k) + a / 2 ^ k := by
  have hmul : 2 ^ h = 2 ^ k * 2 ^ (h - k) := by
    rw [← pow_add, Nat.add_sub_cancel' hk]
  rw [hmul, Nat.mul_add_div (Nat.pow_pos (by omega))]

private theorem leftEmb_coversLeaf_castAdd {h : ℕ} (v : Node h) (i : Fin (2 ^ h)) :
    (Node.leftEmb v).CoversLeaf
      (Fin.cast (by rw [pow_succ', two_mul]) (Fin.castAdd (2 ^ h) i)) ↔ v.CoversLeaf i := by
  simp [Node.CoversLeaf]

private theorem rightEmb_coversLeaf_natAdd {h : ℕ} (v : Node h) (i : Fin (2 ^ h)) :
    (Node.rightEmb v).CoversLeaf
      (Fin.cast (by rw [pow_succ', two_mul]) (Fin.natAdd (2 ^ h) i)) ↔ v.CoversLeaf i := by
  simp only [Node.CoversLeaf, Node.level_rightEmb, Node.index_rightEmb]
  change (2 ^ h + i.val) / 2 ^ v.level = 2 ^ (h - v.level) + v.index ↔ i.val / 2 ^ v.level = v.index
  rw [nat_two_pow_add_div v.level_le]
  omega

private theorem not_leftEmb_coversLeaf_natAdd {h : ℕ} (v : Node h) (i : Fin (2 ^ h)) :
    ¬ (Node.leftEmb v).CoversLeaf
      (Fin.cast (by rw [pow_succ', two_mul]) (Fin.natAdd (2 ^ h) i)) := by
  intro hcov
  have hval : (2 ^ h + i.val) / 2 ^ v.level = v.index := hcov
  rw [nat_two_pow_add_div v.level_le] at hval
  exact absurd hval (Nat.ne_of_gt (lt_of_lt_of_le v.index_lt (Nat.le_add_right _ _)))

private theorem not_rightEmb_coversLeaf_castAdd {h : ℕ} (v : Node h) (i : Fin (2 ^ h)) :
    ¬ (Node.rightEmb v).CoversLeaf
      (Fin.cast (by rw [pow_succ', two_mul]) (Fin.castAdd (2 ^ h) i)) := by
  simp only [Node.CoversLeaf, Node.level_rightEmb, Node.index_rightEmb]
  change ¬ i.val / 2 ^ v.level = 2 ^ (h - v.level) + v.index
  have hdiv : i.val / 2 ^ v.level < 2 ^ (h - v.level) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by omega)), ← pow_add, Nat.sub_add_cancel v.level_le]
    exact i.isLt
  omega

/-- A set `W` of nodes *covers* a leaf set `S` iff the leaves descending from `W` are
precisely the leaves in `S` ([BonehShoup2023], Definition 5.4). -/
@[expose]
def Covers {h : ℕ} (W : Finset (Node h)) (S : Finset (Fin (2 ^ h))) : Prop :=
  ∀ i : Fin (2 ^ h), i ∈ S ↔ ∃ v ∈ W, v.CoversLeaf i

/-- Left-half restriction of a leaf set `S : Finset (Fin (2 ^ (h + 1)))`. -/
@[expose]
def leftPart {h : ℕ} (S : Finset (Fin (2 ^ (h + 1)))) : Finset (Fin (2 ^ h)) :=
  Finset.univ.filter fun i =>
    Fin.cast (by rw [pow_succ', two_mul]) (Fin.castAdd (2 ^ h) i) ∈ S

/-- Right-half restriction of a leaf set `S : Finset (Fin (2 ^ (h + 1)))`. -/
@[expose]
def rightPart {h : ℕ} (S : Finset (Fin (2 ^ (h + 1)))) : Finset (Fin (2 ^ h)) :=
  Finset.univ.filter fun i =>
    Fin.cast (by rw [pow_succ', two_mul]) (Fin.natAdd (2 ^ h) i) ∈ S

private theorem mem_leftPart {h : ℕ} {S : Finset (Fin (2 ^ (h + 1)))} {i : Fin (2 ^ h)} :
    i ∈ leftPart S ↔ Fin.cast (by rw [pow_succ', two_mul]) (Fin.castAdd (2 ^ h) i) ∈ S := by
  simp [leftPart]

private theorem mem_rightPart {h : ℕ} {S : Finset (Fin (2 ^ (h + 1)))} {i : Fin (2 ^ h)} :
    i ∈ rightPart S ↔ Fin.cast (by rw [pow_succ', two_mul]) (Fin.natAdd (2 ^ h) i) ∈ S := by
  simp [rightPart]

private theorem card_leftPart_add_rightPart {h : ℕ} (S : Finset (Fin (2 ^ (h + 1)))) :
    (leftPart S).card + (rightPart S).card = S.card := by
  have he : 2 ^ h + 2 ^ h = 2 ^ (h + 1) := by rw [pow_succ', two_mul]
  calc (leftPart S).card + (rightPart S).card
      = ∑ i : Fin (2 ^ h + 2 ^ h), if Fin.cast he i ∈ S then 1 else 0 := by
        simp only [leftPart, rightPart, Finset.card_filter, Fin.sum_univ_add]
    _ = ∑ j : Fin (2 ^ (h + 1)), if j ∈ S then 1 else 0 :=
        Fintype.sum_equiv (finCongr he) _ _ fun _ => rfl
    _ = S.card := by simp

/-- The canonical optimal cover `cover S` of a leaf subset `S` in the complete binary tree of
height `h` ([BonehShoup2023], Definition 5.4 and remark before Theorem 5.8). -/
@[expose]
def cover : {h : ℕ} → Finset (Fin (2 ^ h)) → Finset (Node h)
  | 0, S => if S = Finset.univ then {Node.root 0} else ∅
  | h + 1, S =>
      if S = Finset.univ then {Node.root (h + 1)}
      else (cover (leftPart S)).map Node.leftEmb ∪ (cover (rightPart S)).map Node.rightEmb

/-- Covering all leaves yields the singleton root `{Node.root h}`
([BonehShoup2023], Definition 5.4). -/
theorem cover_univ {h : ℕ} : cover (h := h) Finset.univ = {Node.root h} := by
  cases h <;> simp [cover]

private theorem disjoint_map_leftEmb_rightEmb {h : ℕ} (A B : Finset (Node h)) :
    Disjoint (A.map Node.leftEmb) (B.map Node.rightEmb) := by
  simp only [Finset.disjoint_left, Finset.mem_map]
  rintro _ ⟨u, -, rfl⟩ ⟨v, -, hv⟩
  exact Node.leftEmb_ne_rightEmb u v hv.symm

private theorem card_cover_of_ne_univ {h : ℕ} {S : Finset (Fin (2 ^ (h + 1)))}
    (hS : S ≠ Finset.univ) :
    (cover S).card = (cover (leftPart S)).card + (cover (rightPart S)).card := by
  simp only [cover, hS, ↓reduceIte]
  rw [Finset.card_union_of_disjoint (disjoint_map_leftEmb_rightEmb _ _),
    Finset.card_map, Finset.card_map]

/-- A cover split along the two halves covers each half of the leaf set. -/
private theorem covers_map_union_iff {h : ℕ} {A B : Finset (Node h)}
    {S : Finset (Fin (2 ^ (h + 1)))} :
    Covers (A.map Node.leftEmb ∪ B.map Node.rightEmb) S ↔
      Covers A (leftPart S) ∧ Covers B (rightPart S) := by
  have he : 2 ^ h + 2 ^ h = 2 ^ (h + 1) := by rw [pow_succ', two_mul]
  rw [Covers, ← (finCongr he).forall_congr_right, Fin.forall_fin_add]
  simp only [Covers, mem_leftPart, mem_rightPart, finCongr_apply, Finset.mem_union,
    Finset.mem_map, or_and_right, exists_or, exists_exists_and_eq_and, leftEmb_coversLeaf_castAdd,
    not_rightEmb_coversLeaf_castAdd, rightEmb_coversLeaf_natAdd, not_leftEmb_coversLeaf_natAdd,
    and_false, exists_false, or_false, false_or]

/-- `cover S` covers `S` ([BonehShoup2023], Definition 5.4). -/
theorem covers_cover {h : ℕ} (S : Finset (Fin (2 ^ h))) : Covers (cover S) S := by
  have huniv {h : ℕ} : Covers (cover (h := h) Finset.univ) Finset.univ := fun i => by
    simp [cover_univ, Node.root_coversLeaf]
  induction h with
  | zero =>
    have : Subsingleton (Fin (2 ^ 0)) := inferInstanceAs (Subsingleton (Fin 1))
    obtain rfl | hne := S.eq_empty_or_nonempty
    · simp [cover, Covers, (Finset.singleton_nonempty _).ne_empty.symm]
    · exact hne.eq_univ ▸ huniv
  | succ h ih =>
    by_cases hS : S = Finset.univ
    · exact hS ▸ huniv
    · simp only [cover, hS, ↓reduceIte]
      exact covers_map_union_iff.2 ⟨ih _, ih _⟩

private theorem Node.exists_leftEmb_or_rightEmb {h : ℕ} {w : Node (h + 1)}
    (hw : w ≠ Node.root (h + 1)) :
    (∃ u : Node h, Node.leftEmb u = w) ∨ (∃ u : Node h, Node.rightEmb u = w) := by
  have hwl : w.level ≤ h := by
    by_contra hlt
    have hl : w.level = h + 1 := by have := w.level_le; omega
    have hi := w.index_lt
    rw [hl, Nat.sub_self, pow_zero, Nat.lt_one_iff] at hi
    exact hw (Node.ext hl hi)
  have hwidx : w.index < 2 ^ (h - w.level) + 2 ^ (h - w.level) := by
    have := w.index_lt
    rwa [show h + 1 - w.level = (h - w.level) + 1 by omega, pow_succ', two_mul] at this
  by_cases hli : w.index < 2 ^ (h - w.level)
  · exact Or.inl ⟨⟨w.level, w.index, hwl, hli⟩, by ext <;> rfl⟩
  · exact Or.inr ⟨⟨w.level, w.index - 2 ^ (h - w.level), hwl, by omega⟩, by
      ext
      · rfl
      · simp; omega⟩

/-- Every cover of `S` has at least as many nodes as `cover S`, justifying `cover S` as the
smallest covering set ([BonehShoup2023], Definition 5.4). -/
theorem card_cover_le_of_covers {h : ℕ} {W : Finset (Node h)} {S : Finset (Fin (2 ^ h))}
    (hW : Covers W S) : (cover S).card ≤ W.card := by
  have huniv {h : ℕ} {W : Finset (Node h)} (hW : Covers W Finset.univ) :
      (cover (h := h) Finset.univ).card ≤ W.card := by
    obtain ⟨v, hv, -⟩ := (hW ⟨0, Nat.two_pow_pos _⟩).1 (Finset.mem_univ _)
    simpa [cover_univ] using Finset.card_pos.2 ⟨v, hv⟩
  induction h with
  | zero =>
    by_cases hS : S = Finset.univ
    · exact hS ▸ huniv (hS ▸ hW)
    · simp only [cover, hS, ↓reduceIte, Finset.card_empty, zero_le]
  | succ h ih =>
    by_cases hS : S = Finset.univ
    · exact hS ▸ huniv (hS ▸ hW)
    have hnotRoot : Node.root (h + 1) ∉ W := fun hroot =>
      hS (Finset.eq_univ_of_forall fun i => (hW i).2 ⟨_, hroot, Node.root_coversLeaf i⟩)
    obtain ⟨A, B, rfl⟩ : ∃ A B : Finset (Node h),
        W = A.map Node.leftEmb ∪ B.map Node.rightEmb := by
      refine ⟨W.preimage _ Node.leftEmb.injective.injOn,
        W.preimage _ Node.rightEmb.injective.injOn, ?_⟩
      ext w
      simp only [Finset.mem_union, Finset.mem_map, Finset.mem_preimage]
      constructor
      · intro hw
        rcases Node.exists_leftEmb_or_rightEmb (ne_of_mem_of_not_mem hw hnotRoot) with
          ⟨u, rfl⟩ | ⟨u, rfl⟩
        exacts [Or.inl ⟨u, hw, rfl⟩, Or.inr ⟨u, hw, rfl⟩]
      · rintro (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩) <;> exact hu
    obtain ⟨hA, hB⟩ := covers_map_union_iff.1 hW
    rw [card_cover_of_ne_univ hS, Finset.card_union_of_disjoint
      (disjoint_map_leftEmb_rightEmb A B), Finset.card_map, Finset.card_map]
    exact Nat.add_le_add (ih hA) (ih hB)

/-- The binary log-sum inequality `(a + b) log₂ (a + b) ≤ a log₂ a + b log₂ b + (a + b)`. -/
private theorem add_mul_logb_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (a + b) * Real.logb 2 (a + b) ≤ a * Real.logb 2 a + b * Real.logb 2 b + (a + b) := by
  have hsum := Real.sum_mul_log_div_card_le (Finset.univ : Finset Bool)
    (x := fun t => if t then a else b) (fun t _ => by cases t <;> positivity)
  simp only [Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true, Finset.card_univ,
    Fintype.card_bool, Nat.cast_ofNat] at hsum
  rw [Real.log_div (by positivity) two_ne_zero] at hsum
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  calc (a + b) * Real.logb 2 (a + b) = (a + b) * Real.log (a + b) / Real.log 2 := by
        rw [Real.logb]; ring
    _ ≤ (a * Real.log a + b * Real.log b + (a + b) * Real.log 2) / Real.log 2 := by
        gcongr; linarith
    _ = _ := by simp only [Real.logb]; field_simp

private theorem logb_two_pow_div (h : ℕ) {m : ℝ} (hm : 0 < m) :
    Real.logb 2 (2 ^ h / m) = h - Real.logb 2 m := by
  rw [Real.logb_div (by positivity) hm.ne', Real.logb_pow, Real.logb_self_eq_one one_lt_two,
    mul_one]

/-- **Theorem 5.8 ([BonehShoup2023], p. 207):** In a complete binary tree with `n = 2 ^ h` leaves,
for every `1 ≤ r ≤ n` and every subset `S` of `n - r` leaves (written `S.card + r = 2 ^ h` so
`r ≤ 2 ^ h` is built in without natural-number subtraction truncation),
`|cover(S)| ≤ r * log₂(n / r)`. In the `r₁ = 0` case, the printed proof omits the `+ 1` for the
full half's root (`|cover(S)| = |cover(S₂)|`); the bound still holds because `1 ≤ r`. -/
theorem card_cover_le {h r : ℕ} {S : Finset (Fin (2 ^ h))}
    (hr : 1 ≤ r) (hS : S.card + r = 2 ^ h) :
    ((cover S).card : ℝ) ≤ (r : ℝ) * Real.logb 2 ((2 ^ h : ℝ) / r) := by
  induction h generalizing r with
  | zero =>
    obtain rfl : S = ∅ := Finset.card_eq_zero.1 (by omega)
    obtain rfl : r = 1 := by simpa using hS
    simp [cover]
  | succ h ih =>
    have hSne : S ≠ Finset.univ := by
      rintro rfl
      simp only [Finset.card_univ, Fintype.card_fin] at hS
      omega
    obtain ⟨r1, hS1⟩ := Nat.exists_eq_add_of_le (by simpa using (leftPart S).card_le_univ)
    obtain ⟨r2, hS2⟩ := Nat.exists_eq_add_of_le (by simpa using (rightPart S).card_le_univ)
    have hrsum : r1 + r2 = r := by
      have := card_leftPart_add_rightPart S
      have := pow_succ 2 h
      omega
    -- The inductive hypothesis on a half with `m ≥ 1` missing leaves, and on a full half.
    have hhalf {T : Finset (Fin (2 ^ h))} {m : ℕ} (hm : 1 ≤ m) (hT : 2 ^ h = T.card + m) :
        ((cover T).card : ℝ) ≤ m * (h - Real.logb 2 m) := by
      simpa only [logb_two_pow_div _ (by positivity : (0 : ℝ) < m)] using ih hm hT.symm
    have hfull {T : Finset (Fin (2 ^ h))} (hT : 2 ^ h = T.card + 0) : ((cover T).card : ℝ) = 1 := by
      rw [Finset.eq_univ_of_card T (by simpa using hT.symm), cover_univ, Finset.card_singleton,
        Nat.cast_one]
    rw [card_cover_of_ne_univ hSne, Nat.cast_add, logb_two_pow_div _ (by positivity)]
    have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
    push_cast
    rcases Nat.eq_zero_or_pos r1 with rfl | h1
    · obtain rfl : r2 = r := by omega
      linarith [hfull hS1, hhalf hr hS2]
    rcases Nat.eq_zero_or_pos r2 with rfl | h2
    · obtain rfl : r1 = r := by omega
      linarith [hfull hS2, hhalf hr hS1]
    subst hrsum
    have hconv := add_mul_logb_le (Nat.cast_pos.2 h1 : (0 : ℝ) < r1) (Nat.cast_pos.2 h2)
    push_cast
    linarith [hhalf h1 hS1, hhalf h2 hS2]

end Cslib.CompleteBinaryTree

end
