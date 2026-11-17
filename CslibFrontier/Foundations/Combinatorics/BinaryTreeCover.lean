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
  i.1 / 2 ^ v.level = v.index

instance {h : ℕ} (v : Node h) (i : Fin (2 ^ h)) : Decidable (v.CoversLeaf i) :=
  inferInstanceAs (Decidable (i.1 / 2 ^ v.level = v.index))

private theorem Node.root_coversLeaf {h : ℕ} (i : Fin (2 ^ h)) : (Node.root h).CoversLeaf i := by
  simp [Node.CoversLeaf, Node.root, Nat.div_eq_of_lt i.2]

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
  change (2 ^ h + i.1) / 2 ^ v.level = 2 ^ (h - v.level) + v.index ↔ i.1 / 2 ^ v.level = v.index
  rw [nat_two_pow_add_div v.level_le]
  omega

private theorem not_leftEmb_coversLeaf_natAdd {h : ℕ} (v : Node h) (i : Fin (2 ^ h)) :
    ¬ (Node.leftEmb v).CoversLeaf
      (Fin.cast (by rw [pow_succ', two_mul]) (Fin.natAdd (2 ^ h) i)) := by
  intro hcov
  have hval : (2 ^ h + i.1) / 2 ^ v.level = v.index := hcov
  rw [nat_two_pow_add_div v.level_le] at hval
  exact absurd hval (Nat.ne_of_gt (lt_of_lt_of_le v.index_lt (Nat.le_add_right _ _)))

private theorem not_rightEmb_coversLeaf_castAdd {h : ℕ} (v : Node h) (i : Fin (2 ^ h)) :
    ¬ (Node.rightEmb v).CoversLeaf
      (Fin.cast (by rw [pow_succ', two_mul]) (Fin.castAdd (2 ^ h) i)) := by
  simp only [Node.CoversLeaf, Node.level_rightEmb, Node.index_rightEmb]
  change ¬ i.1 / 2 ^ v.level = 2 ^ (h - v.level) + v.index
  have hdiv : i.1 / 2 ^ v.level < 2 ^ (h - v.level) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by omega)), ← pow_add, Nat.sub_add_cancel v.level_le]
    exact i.2
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

private theorem card_cover_of_ne_univ {h : ℕ} {S : Finset (Fin (2 ^ (h + 1)))}
    (hS : S ≠ Finset.univ) :
    (cover S).card = (cover (leftPart S)).card + (cover (rightPart S)).card := by
  dsimp only [cover]
  rw [ite_eq_right_iff.2 (fun h => absurd h hS), Finset.card_union_of_disjoint, Finset.card_map,
    Finset.card_map]
  rw [Finset.disjoint_left]
  intro v hvL hvR
  rw [Finset.mem_map] at hvL hvR
  rcases hvL with ⟨u, _, rfl⟩
  rcases hvR with ⟨w, _, hEq⟩
  exact Node.leftEmb_ne_rightEmb u w hEq.symm

/-- `cover S` covers `S` ([BonehShoup2023], Definition 5.4). -/
theorem covers_cover {h : ℕ} (S : Finset (Fin (2 ^ h))) : Covers (cover S) S := by
  induction h with
  | zero =>
    intro i
    fin_cases i
    by_cases hS : S = Finset.univ
    · rw [hS, cover_univ]
      simp [Node.root_coversLeaf]
    · have hSemp : S = ∅ := by
        ext j
        fin_cases j
        simp only [Finset.notMem_empty, iff_false]
        intro hmem
        apply hS
        ext k; fin_cases k; simpa using hmem
      subst hSemp
      simp [cover]
  | succ h ih =>
    by_cases hS : S = Finset.univ
    · rw [hS, cover_univ]
      intro i
      simp [Node.root_coversLeaf]
    · intro x
      dsimp only [cover]
      rw [ite_eq_right_iff.2 (fun heq => absurd heq hS)]
      by_cases hlt : x.1 < 2 ^ h
      · let i : Fin (2 ^ h) := ⟨x.1, hlt⟩
        have hx : x = Fin.cast (by rw [pow_succ', two_mul]) (Fin.castAdd (2 ^ h) i) := by
          ext; rfl
        rw [hx, ← mem_leftPart, ih (leftPart S) i]
        simp only [Finset.mem_union, Finset.mem_map]
        constructor
        · rintro ⟨v, hv, hvc⟩
          exact ⟨Node.leftEmb v, Or.inl ⟨v, hv, rfl⟩, (leftEmb_coversLeaf_castAdd v i).2 hvc⟩
        · rintro ⟨w, hw, hwc⟩
          rcases hw with ⟨v, hv, rfl⟩ | ⟨v, _, rfl⟩
          · exact ⟨v, hv, (leftEmb_coversLeaf_castAdd v i).1 hwc⟩
          · exact False.elim (not_rightEmb_coversLeaf_castAdd v i hwc)
      · have hx2 : x.1 < 2 ^ h + 2 ^ h := by simpa [pow_succ', two_mul] using x.2
        have hlt2 : x.1 - 2 ^ h < 2 ^ h := by omega
        let i : Fin (2 ^ h) := ⟨x.1 - 2 ^ h, hlt2⟩
        have hx : x = Fin.cast (by rw [pow_succ', two_mul]) (Fin.natAdd (2 ^ h) i) := by
          ext; change x.1 = 2 ^ h + (x.1 - 2 ^ h); omega
        rw [hx, ← mem_rightPart, ih (rightPart S) i]
        simp only [Finset.mem_union, Finset.mem_map]
        constructor
        · rintro ⟨v, hv, hvc⟩
          exact ⟨Node.rightEmb v, Or.inr ⟨v, hv, rfl⟩, (rightEmb_coversLeaf_natAdd v i).2 hvc⟩
        · rintro ⟨w, hw, hwc⟩
          rcases hw with ⟨v, _, rfl⟩ | ⟨v, hv, rfl⟩
          · exact False.elim (not_leftEmb_coversLeaf_natAdd v i hwc)
          · exact ⟨v, hv, (rightEmb_coversLeaf_natAdd v i).1 hwc⟩

private theorem Node.exists_leftEmb_or_rightEmb {h : ℕ} {w : Node (h + 1)} (hwl : w.level ≤ h) :
    (∃ u : Node h, Node.leftEmb u = w) ∨ (∃ u : Node h, Node.rightEmb u = w) := by
  by_cases hli : w.index < 2 ^ (h - w.level)
  · exact Or.inl ⟨⟨w.level, w.index, hwl, hli⟩, by ext <;> rfl⟩
  · have hri : w.index - 2 ^ (h - w.level) < 2 ^ (h - w.level) := by
      have hwidx : w.index < 2 ^ (h + 1 - w.level) := w.index_lt
      have hexp : h + 1 - w.level = (h - w.level) + 1 := by omega
      rw [hexp, pow_succ', two_mul] at hwidx
      omega
    exact Or.inr ⟨⟨w.level, w.index - 2 ^ (h - w.level), hwl, hri⟩, by
      ext
      · rfl
      · simp; omega⟩

/-- Every cover of `S` has at least as many nodes as `cover S`, justifying `cover S` as the
smallest covering set ([BonehShoup2023], Definition 5.4). -/
theorem card_cover_le_of_covers {h : ℕ} {W : Finset (Node h)} {S : Finset (Fin (2 ^ h))}
    (hW : Covers W S) : (cover S).card ≤ W.card := by
  induction h with
  | zero =>
    by_cases hS : S = Finset.univ
    · rw [hS, cover_univ, Finset.card_singleton]
      have hmem : (⟨0, by simp⟩ : Fin (2 ^ 0)) ∈ S := hS ▸ Finset.mem_univ _
      rcases (hW _).1 hmem with ⟨v, hv, _⟩
      exact Finset.card_pos.2 ⟨v, hv⟩
    · dsimp only [cover]
      rw [ite_eq_right_iff.2 (fun heq => absurd heq hS), Finset.card_empty]
      exact Nat.zero_le _
  | succ h ih =>
    by_cases hS : S = Finset.univ
    · rw [hS, cover_univ, Finset.card_singleton]
      have hmem : (⟨0, Nat.pow_pos (by omega)⟩ : Fin (2 ^ (h + 1))) ∈ S := hS ▸ Finset.mem_univ _
      rcases (hW _).1 hmem with ⟨v, hv, _⟩
      exact Finset.card_pos.2 ⟨v, hv⟩
    · have hnotRoot : Node.root (h + 1) ∉ W := by
        intro hroot
        apply hS
        ext i
        simp only [Finset.mem_univ, iff_true]
        exact (hW i).2 ⟨Node.root (h + 1), hroot, Node.root_coversLeaf i⟩
      let WL : Finset (Node h) := W.preimage Node.leftEmb (Node.leftEmb.injective.injOn)
      let WR : Finset (Node h) := W.preimage Node.rightEmb (Node.rightEmb.injective.injOn)
      have hlevel_le {w : Node (h + 1)} (hw : w ∈ W) : w.level ≤ h := by
        have hle := w.level_le
        rcases lt_or_eq_of_le hle with hlt | heq
        · omega
        · exfalso
          have hidx := w.index_lt
          rw [heq, Nat.sub_self, pow_zero] at hidx
          have : w = Node.root (h + 1) := by
            ext
            · exact heq
            · simp [Node.root]; omega
          exact hnotRoot (this ▸ hw)
      have hcovL : Covers WL (leftPart S) := by
        intro i
        rw [mem_leftPart, hW (Fin.cast (by rw [pow_succ', two_mul]) (Fin.castAdd (2 ^ h) i))]
        constructor
        · rintro ⟨w, hw, hwc⟩
          rcases Node.exists_leftEmb_or_rightEmb (hlevel_le hw) with ⟨u, rfl⟩ | ⟨u, rfl⟩
          · exact ⟨u, by simpa [WL] using hw, (leftEmb_coversLeaf_castAdd u i).1 hwc⟩
          · exact False.elim (not_rightEmb_coversLeaf_castAdd u i hwc)
        · rintro ⟨u, hu, huc⟩
          exact ⟨Node.leftEmb u, by simpa [WL] using hu, (leftEmb_coversLeaf_castAdd u i).2 huc⟩
      have hcovR : Covers WR (rightPart S) := by
        intro i
        rw [mem_rightPart, hW (Fin.cast (by rw [pow_succ', two_mul]) (Fin.natAdd (2 ^ h) i))]
        constructor
        · rintro ⟨w, hw, hwc⟩
          rcases Node.exists_leftEmb_or_rightEmb (hlevel_le hw) with ⟨u, rfl⟩ | ⟨u, rfl⟩
          · exact False.elim (not_leftEmb_coversLeaf_natAdd u i hwc)
          · exact ⟨u, by simpa [WR] using hw, (rightEmb_coversLeaf_natAdd u i).1 hwc⟩
        · rintro ⟨u, hu, huc⟩
          exact ⟨Node.rightEmb u, by simpa [WR] using hu, (rightEmb_coversLeaf_natAdd u i).2 huc⟩
      have hcardW : WL.card + WR.card ≤ W.card := by
        rw [← Finset.card_map (f := Node.leftEmb) (s := WL),
            ← Finset.card_map (f := Node.rightEmb) (s := WR)]
        rw [← Finset.card_union_of_disjoint]
        · apply Finset.card_le_card
          intro w hw
          simp only [Finset.mem_union, Finset.mem_map, Finset.mem_preimage, WL, WR] at hw
          rcases hw with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩ <;> exact hu
        · rw [Finset.disjoint_left]
          intro w hwL hwR
          simp only [Finset.mem_map, Finset.mem_preimage, WL, WR] at hwL hwR
          rcases hwL with ⟨u, _, rfl⟩
          rcases hwR with ⟨v, _, hv⟩
          exact Node.leftEmb_ne_rightEmb u v hv.symm
      calc (cover S).card = (cover (leftPart S)).card + (cover (rightPart S)).card :=
            card_cover_of_ne_univ hS
        _ ≤ WL.card + WR.card := Nat.add_le_add (ih hcovL) (ih hcovR)
        _ ≤ W.card := hcardW

private theorem add_mul_logb_two_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (a + b) * Real.logb 2 (a + b) ≤ a * Real.logb 2 (2 * a) + b * Real.logb 2 (2 * b) := by
  have hlogsum := Real.sum_mul_log_div_card_le (Finset.univ : Finset Bool)
    (x := fun t => if t then 2 * a else 2 * b) (fun t _ => by cases t <;> positivity)
  have hcard : (#(Finset.univ : Finset Bool) : ℝ) = 2 := by simp
  have hsum : (∑ t : Bool, if t then 2 * a else 2 * b) = 2 * (a + b) := by
    simp only [Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true]
    ring
  have hrhs : (∑ t : Bool, (if t then 2 * a else 2 * b) * Real.log (if t then 2 * a else 2 * b)) =
      2 * (a * Real.log (2 * a) + b * Real.log (2 * b)) := by
    simp only [Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true]
    ring
  rw [hcard, hsum, hrhs, mul_div_cancel_left₀ _ (by norm_num)] at hlogsum
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hreal : (a + b) * Real.log (a + b) ≤ a * Real.log (2 * a) + b * Real.log (2 * b) := by
    linarith
  simp only [Real.logb]
  have hdiv : (a + b) * Real.log (a + b) / Real.log 2 ≤
      (a * Real.log (2 * a) + b * Real.log (2 * b)) / Real.log 2 :=
    div_le_div_of_nonneg_right hreal hlog2.le
  calc (a + b) * (Real.log (a + b) / Real.log 2)
      = (a + b) * Real.log (a + b) / Real.log 2 := by ring
    _ ≤ (a * Real.log (2 * a) + b * Real.log (2 * b)) / Real.log 2 := hdiv
    _ = a * (Real.log (2 * a) / Real.log 2) + b * (Real.log (2 * b) / Real.log 2) := by ring

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
    have hcard : S.card = 0 := by omega
    have hremp : S = ∅ := Finset.card_eq_zero.1 hcard
    have hr1 : r = 1 := by omega
    subst hremp hr1
    simp [cover]
  | succ h ih =>
    have hSne : S ≠ Finset.univ := by
      intro huniv
      subst huniv
      simp only [Finset.card_univ, Fintype.card_fin] at hS
      omega
    rw [card_cover_of_ne_univ hSne]
    let r1 : ℕ := 2 ^ h - (leftPart S).card
    let r2 : ℕ := 2 ^ h - (rightPart S).card
    have hLcard : (leftPart S).card ≤ 2 ^ h := by
      simpa [Fintype.card_fin] using Finset.card_le_univ (leftPart S)
    have hRcard : (rightPart S).card ≤ 2 ^ h := by
      simpa [Fintype.card_fin] using Finset.card_le_univ (rightPart S)
    have hS1 : (leftPart S).card + r1 = 2 ^ h := Nat.add_sub_of_le hLcard
    have hS2 : (rightPart S).card + r2 = 2 ^ h := Nat.add_sub_of_le hRcard
    have hrsum : r1 + r2 = r := by
      have hpart := card_leftPart_add_rightPart S
      have hpow : 2 ^ (h + 1) = 2 ^ h + 2 ^ h := by rw [pow_succ', two_mul]
      omega
    have hlog_half (m : ℕ) (hm : 0 < m) :
        Real.logb 2 ((2 ^ h : ℝ) / m) = Real.logb 2 ((2 ^ (h + 1) : ℝ) / m) - 1 := by
      have hm0 : (m : ℝ) ≠ 0 := by positivity
      have h2h0 : (2 ^ h : ℝ) ≠ 0 := by positivity
      have heq : (2 ^ (h + 1) : ℝ) / m = 2 * ((2 ^ h : ℝ) / m) := by
        rw [pow_succ']; ring
      rw [heq, Real.logb_mul (by norm_num) (div_ne_zero h2h0 hm0),
        Real.logb_self_eq_one (by norm_num)]
      ring
    rcases Nat.eq_zero_or_pos r1 with hr10 | hr1pos
    · have hr2eq : r2 = r := by omega
      have hLuniv : leftPart S = Finset.univ := by
        apply Finset.eq_univ_of_card
        rw [Fintype.card_fin]
        omega
      rw [hLuniv, cover_univ, Finset.card_singleton]
      have ih2 := ih hr (hr2eq ▸ hS2)
      rw [hlog_half r hr] at ih2
      have hr_ge1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
      push_cast
      linarith
    · rcases Nat.eq_zero_or_pos r2 with hr20 | hr2pos
      · have hr1eq : r1 = r := by omega
        have hRuniv : rightPart S = Finset.univ := by
          apply Finset.eq_univ_of_card
          rw [Fintype.card_fin]
          omega
        rw [hRuniv, cover_univ, Finset.card_singleton]
        have ih1 := ih hr (hr1eq ▸ hS1)
        rw [hlog_half r hr] at ih1
        have hr_ge1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
        push_cast
        linarith
      · have ih1 := ih hr1pos hS1
        have ih2 := ih hr2pos hS2
        have hconv := add_mul_logb_two_le (a := (r1 : ℝ)) (b := (r2 : ℝ))
          (Nat.cast_pos.2 hr1pos) (Nat.cast_pos.2 hr2pos)
        have hsumR : (r1 : ℝ) + (r2 : ℝ) = (r : ℝ) := by exact_mod_cast hrsum
        have hrne : (r : ℝ) ≠ 0 := by positivity
        have hN : (2 ^ (h + 1) : ℝ) = 2 * (2 ^ h : ℝ) := by rw [pow_succ']
        have hsplit_half (m : ℕ) (hm : 0 < m) :
            (m : ℝ) * Real.logb 2 ((2 ^ h : ℝ) / m) =
              (m : ℝ) * Real.logb 2 (2 ^ (h + 1) : ℝ) - (m : ℝ) * Real.logb 2 (2 * (m : ℝ)) := by
          have hm0 : (m : ℝ) ≠ 0 := by positivity
          have hdiv : (2 ^ h : ℝ) / m = (2 ^ (h + 1) : ℝ) / (2 * (m : ℝ)) := by
            rw [hN]; field_simp
          rw [hdiv, Real.logb_div (by positivity) (by positivity)]
          ring
        have hsplit : (r : ℝ) * Real.logb 2 ((2 ^ (h + 1) : ℝ) / r) =
            (r : ℝ) * Real.logb 2 (2 ^ (h + 1) : ℝ) - (r : ℝ) * Real.logb 2 (r : ℝ) := by
          rw [Real.logb_div (by positivity) hrne]
          ring
        have hdistrib : (r1 : ℝ) * Real.logb 2 (2 ^ (h + 1) : ℝ) +
            (r2 : ℝ) * Real.logb 2 (2 ^ (h + 1) : ℝ) =
            (r : ℝ) * Real.logb 2 (2 ^ (h + 1) : ℝ) := by
          rw [← add_mul, hsumR]
        rw [hsplit_half r1 hr1pos] at ih1
        rw [hsplit_half r2 hr2pos] at ih2
        rw [hsumR] at hconv
        rw [hsplit]
        push_cast
        linarith

end Cslib.CompleteBinaryTree

end
