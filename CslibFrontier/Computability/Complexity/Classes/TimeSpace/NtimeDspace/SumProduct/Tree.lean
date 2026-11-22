/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Size
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Sum–product recursions

A sum–product recursion (Definition 3.1 of the paper) is a rooted tree whose
nodes carry a precision `P` and a residue modulo `2^P`. `SPTree` is that tree:
a leaf with a given value, a sum node with index length `w` (children `f i` for
`i < 2^w`), a product node with two children, or a shift node.

* `SPTree.value` is the value of a node, its canonical residue in `[0, 2^P)`.
* `SPTree.cost ℓ` is the largest total cost of a root-to-leaf path, where a sum
  node with index length `w` costs `w + ℓ` and every other inner node costs `ℓ`.
* `SPTree.node t π` is the subtree at a path `π`, written with its deepest
  symbol first, so the child of `π` by `i` is `i :: π`. `SPTree.Valid t π` says
  that every symbol of `π` names an actual child.

Children of a sum or product node may carry any precision; the bitwise
evaluation in `SumProduct.Machine` does not need them to match.

## Main results

* `colCarry_spec`: column addition. Bit `k` of `∑_{j ≤ k} s j * 2^j` is the
  parity of the carry into column `k` plus `s k`.
* `testBit_sum_eq`, `testBit_mul_eq`: the bits of a sum and of a product are
  column additions of the bits of the summands and factors.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.SumProduct

open Finset

/-- A sum–product recursion. -/
inductive SPTree : Type where
  /-- A leaf of precision `P` whose value is `v mod 2^P`. -/
  | leaf (P v : ℕ)
  /-- A sum node of precision `P` with index length `w`; its children are `f i`
  for `i < 2^w`. -/
  | sum (P w : ℕ) (f : ℕ → SPTree)
  /-- A product node of precision `P`. -/
  | prod (P : ℕ) (a b : SPTree)
  /-- A shift node of precision `P`: bit `k` of its value is bit `k + σ` of
  the value of its child. -/
  | shift (P σ : ℕ) (a : SPTree)

namespace SPTree

/-- The precision of a node. -/
def prec : SPTree → ℕ
  | leaf P _ | sum P _ _ | prod P _ _ | shift P _ _ => P

/-- The value of a node, as its canonical residue in `[0, 2^P)`. -/
def value : SPTree → ℕ
  | leaf P v => v % 2 ^ P
  | sum P w f => (∑ i ∈ range (2 ^ w), value (f i)) % 2 ^ P
  | prod P a b => (value a * value b) % 2 ^ P
  | shift P σ a => (value a / 2 ^ σ) % 2 ^ P

/-- The cost of the most expensive root-to-leaf path. -/
def cost (ℓ : ℕ) : SPTree → ℕ
  | leaf _ _ => 0
  | sum _ w f => w + ℓ + (range (2 ^ w)).sup fun i => cost ℓ (f i)
  | prod _ a b => ℓ + max (cost ℓ a) (cost ℓ b)
  | shift _ _ a => ℓ + cost ℓ a

/-- The child of a node by a symbol (junk at a leaf or an invalid symbol). -/
def child : SPTree → ℕ → SPTree
  | leaf P v, _ => leaf P v
  | sum _ _ f, i => f i
  | prod _ a b, i => if i = 0 then a else b
  | shift _ _ a, _ => a

/-- Whether a symbol names a child. -/
def ValidChild : SPTree → ℕ → Prop
  | leaf _ _, _ => False
  | sum _ w _, i => i < 2 ^ w
  | prod _ _ _, i => i < 2
  | shift _ _ _, i => i = 0

/-- The subtree at a path, deepest symbol first. -/
def node (t : SPTree) : List ℕ → SPTree
  | [] => t
  | i :: π => (node t π).child i

/-- Every symbol of the path names a child. -/
def Valid (t : SPTree) : List ℕ → Prop
  | [] => True
  | i :: π => Valid t π ∧ (node t π).ValidChild i

@[simp] theorem node_nil (t : SPTree) : node t [] = t := rfl
@[simp] theorem node_cons (t : SPTree) (i : ℕ) (π : List ℕ) :
    node t (i :: π) = (node t π).child i := rfl
@[simp] theorem valid_nil (t : SPTree) : Valid t [] := trivial
@[simp] theorem valid_cons (t : SPTree) (i : ℕ) (π : List ℕ) :
    Valid t (i :: π) ↔ Valid t π ∧ (node t π).ValidChild i := Iff.rfl

theorem value_lt (t : SPTree) : t.value < 2 ^ t.prec := by
  cases t <;> simp only [value, prec] <;> exact Nat.mod_lt _ (by positivity)

theorem testBit_value_of_le {t : SPTree} {k : ℕ} (h : t.prec ≤ k) : t.value.testBit k = false :=
  Nat.testBit_lt_two_pow ((value_lt t).trans_le (Nat.pow_le_pow_right (by norm_num) h))

theorem node_append (t : SPTree) (ρ π : List ℕ) : node t (ρ ++ π) = node (node t π) ρ := by
  induction ρ with
  | nil => rfl
  | cons i ρ ih => simp [ih]

theorem valid_append (t : SPTree) (ρ π : List ℕ) :
    Valid t (ρ ++ π) ↔ Valid t π ∧ Valid (node t π) ρ := by
  induction ρ with
  | nil => simp
  | cons i ρ ih => simp [ih, node_append, and_assoc]

/-- The numeric kind of a node: `0` leaf, `1` sum, `2` product, `3` shift. -/
def tag : SPTree → ℕ
  | leaf _ _ => 0
  | sum _ _ _ => 1
  | prod _ _ _ => 2
  | shift _ _ _ => 3

/-- The parameter of a node: the index length of a sum node, the shift of a
shift node, and `0` otherwise. Leaf values are reported bit by bit. -/
def param : SPTree → ℕ
  | leaf _ _ => 0
  | sum _ w _ => w
  | prod _ _ _ => 0
  | shift _ σ _ => σ

/-- The cost a node adds to a path through it. -/
def nodeCost (ℓ : ℕ) : SPTree → ℕ
  | leaf _ _ => 0
  | sum _ w _ => w + ℓ
  | prod _ _ _ => ℓ
  | shift _ _ _ => ℓ

theorem cost_child (ℓ : ℕ) {t : SPTree} {i : ℕ} (h : t.ValidChild i) :
    t.nodeCost ℓ + (t.child i).cost ℓ ≤ t.cost ℓ := by
  cases t with
  | leaf => exact h.elim
  | sum P w f =>
    simp only [nodeCost, child, cost]
    have := Finset.le_sup (f := fun i => cost ℓ (f i)) (Finset.mem_range.mpr h)
    omega
  | prod P a b =>
    simp only [nodeCost, child, cost]
    split_ifs <;> omega
  | shift P σ a => simp [nodeCost, child, cost]

/-- The costs of the nodes strictly above the end of a valid path, plus the
cost of the subtree below it, are at most the cost of the tree. -/
theorem pathCost_le (ℓ : ℕ) (t : SPTree) :
    ∀ π : List ℕ, Valid t π →
      ((List.range π.length).map fun m => (node t (π.drop (m + 1))).nodeCost ℓ).sum +
        (node t π).cost ℓ ≤ t.cost ℓ
  | [], _ => by simp
  | i :: π, ⟨hπ, hi⟩ => by
    have ih := pathCost_le ℓ t π hπ
    have hc := cost_child ℓ hi
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
    simp only [List.drop_succ_cons, List.drop_zero, node_cons, Function.comp_def,
        Nat.succ_eq_add_one,
      Nat.add_assoc] at ih ⊢
    omega

/-- All precisions are at most `B`, along valid paths. -/
def PrecLe (B : ℕ) : SPTree → Prop
  | leaf P _ => P ≤ B
  | sum P w f => P ≤ B ∧ ∀ i < 2 ^ w, PrecLe B (f i)
  | prod P a b => P ≤ B ∧ PrecLe B a ∧ PrecLe B b
  | shift P _ a => P ≤ B ∧ PrecLe B a

theorem PrecLe.prec {B : ℕ} {t : SPTree} (h : t.PrecLe B) : t.prec ≤ B := by
  cases t with
  | leaf => exact h
  | sum => exact h.1
  | prod => exact h.1
  | shift => exact h.1

theorem PrecLe.child {B : ℕ} {t : SPTree} {i : ℕ} (h : t.PrecLe B) (hi : t.ValidChild i) :
    (t.child i).PrecLe B := by
  cases t with
  | leaf => exact hi.elim
  | sum P w f => exact h.2 i hi
  | prod P a b =>
    show (if i = 0 then a else b).PrecLe B
    split_ifs; exacts [h.2.1, h.2.2]
  | shift P σ a => exact h.2

theorem PrecLe.node {B : ℕ} {t : SPTree} (h : t.PrecLe B) :
    ∀ {π : List ℕ}, Valid t π → (node t π).PrecLe B
  | [], _ => h
  | _ :: _, ⟨hπ, hi⟩ => (PrecLe.node h hπ).child hi

/-! ### Column addition -/

/-- The carry into column `k` when adding columns with sums `s j`. -/
def colCarry (s : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => (colCarry s j + s j) / 2

/-- The carry is the high part of the partial sum. -/
theorem colCarry_eq (s : ℕ → ℕ) (k : ℕ) :
    colCarry s k = (∑ j ∈ range k, s j * 2 ^ j) / 2 ^ k := by
  induction k with
  | zero => simp [colCarry]
  | succ k ih =>
    rw [colCarry, ih, Finset.sum_range_succ, pow_succ, ← Nat.div_div_eq_div_mul]
    congr 1
    rw [Nat.add_mul_div_right _ _ (by positivity)]

/-- **Column addition.** Bit `k` of the partial sum through column `k` is the
parity of the incoming carry plus the column sum. -/
theorem colCarry_spec (s : ℕ → ℕ) (k : ℕ) :
    (∑ j ∈ range (k + 1), s j * 2 ^ j).testBit k = decide ((colCarry s k + s k) % 2 = 1) := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Finset.sum_range_succ, colCarry_eq,
    Nat.add_mul_div_right _ _ (by positivity)]

theorem colCarry_le (s : ℕ → ℕ) {m : ℕ} (hs : ∀ j, s j ≤ m) (k : ℕ) : colCarry s k ≤ m := by
  induction k with
  | zero => simp [colCarry]
  | succ k ih => have := hs k; simp only [colCarry]; omega

/-- A natural number modulo `2^m` is the sum of its bits below `m`. -/
theorem mod_two_pow_eq_sum (x m : ℕ) :
    x % 2 ^ m = ∑ j ∈ range m, (x.testBit j).toNat * 2 ^ j := by
  induction m with
  | zero => simp [Nat.mod_one]
  | succ m ih =>
    rw [Finset.sum_range_succ, ← ih, Nat.pow_succ, Nat.mod_mul, Nat.testBit_eq_decide_div_mod_eq]
    have h := Nat.mod_two_eq_zero_or_one (x / 2 ^ m)
    rcases h with h | h <;> simp [h]

/-- Bit `k` of `x` depends only on `x mod 2^(k+1)`. -/
theorem testBit_eq_of_mod {x y k : ℕ} (h : x % 2 ^ (k + 1) = y % 2 ^ (k + 1)) :
    x.testBit k = y.testBit k := by
  have := congrArg (fun z => z.testBit k) h
  simpa [Nat.testBit_mod_two_pow] using this

/-- The column sums of a sum of numbers. -/
def sumCol (n : ℕ) (x : ℕ → ℕ) (j : ℕ) : ℕ := ∑ i ∈ range n, ((x i).testBit j).toNat

theorem sumCol_le (n : ℕ) (x : ℕ → ℕ) (j : ℕ) : sumCol n x j ≤ n := by
  unfold sumCol
  calc ∑ i ∈ range n, ((x i).testBit j).toNat ≤ ∑ _i ∈ range n, 1 :=
        Finset.sum_le_sum fun i _ => Bool.toNat_le _
    _ = n := by simp

/-- **Bits of a sum.** -/
theorem testBit_sum_eq (n : ℕ) (x : ℕ → ℕ) (k : ℕ) :
    (∑ i ∈ range n, x i).testBit k =
      decide ((colCarry (sumCol n x) k + sumCol n x k) % 2 = 1) := by
  rw [← colCarry_spec]
  apply testBit_eq_of_mod
  have : ∑ j ∈ range (k + 1), sumCol n x j * 2 ^ j = ∑ i ∈ range n, x i % 2 ^ (k + 1) := by
    simp only [sumCol, Finset.sum_mul, mod_two_pow_eq_sum]
    exact Finset.sum_comm
  rw [this, Finset.sum_nat_mod]

/-- The column sums of a product of two numbers. -/
def prodCol (a b : ℕ) (j : ℕ) : ℕ :=
  ∑ l ∈ range (j + 1), (a.testBit l).toNat * (b.testBit (j - l)).toNat

theorem prodCol_le (a b j : ℕ) : prodCol a b j ≤ j + 1 := by
  unfold prodCol
  calc ∑ l ∈ range (j + 1), (a.testBit l).toNat * (b.testBit (j - l)).toNat
        ≤ ∑ _l ∈ range (j + 1), 1 :=
        Finset.sum_le_sum fun l _ => by
          cases a.testBit l <;> cases b.testBit (j - l) <;> simp
    _ = j + 1 := by simp

theorem colCarry_congr {s s' : ℕ → ℕ} {k : ℕ} (h : ∀ j < k, s j = s' j) :
    colCarry s k = colCarry s' k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [colCarry]
    rw [ih fun j hj => h j (by omega), h k (by omega)]

/-- **Bits of a product.** -/
theorem testBit_mul_eq (a b k : ℕ) :
    (a * b).testBit k = decide ((colCarry (prodCol a b) k + prodCol a b k) % 2 = 1) := by
  set x : ℕ → ℕ := fun l => (a.testBit l).toNat * 2 ^ l * b
  have hmod : a * b % 2 ^ (k + 1) = (∑ l ∈ range (k + 1), x l) % 2 ^ (k + 1) := by
    rw [← Nat.mod_mul_mod, mod_two_pow_eq_sum a (k + 1), Finset.sum_mul]
  have hcol : ∀ j ≤ k, sumCol (k + 1) x j = prodCol a b j := by
    intro j hj
    simp only [sumCol, prodCol, x]
    rw [show k + 1 = (j + 1) + (k - j) by omega, Finset.sum_range_add]
    have hzero : ∑ l ∈ range (k - j),
        (((a.testBit (j + 1 + l)).toNat * 2 ^ (j + 1 + l) * b).testBit j).toNat = 0 := by
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [Nat.mul_assoc, Nat.mul_comm (2 ^ _) b, ← Nat.mul_assoc]
      simp only [Nat.testBit_mul_two_pow]
      simp only [show ¬ (j + 1 + l ≤ j) by omega, decide_false, Bool.false_and, Bool.toNat_false]
    rw [hzero, Nat.add_zero]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hl : l ≤ j := by simp at hl; omega
    rw [Nat.mul_assoc, Nat.mul_comm (2 ^ _) b, ← Nat.mul_assoc]
    cases a.testBit l <;> simp [Nat.testBit_mul_two_pow, hl]
  rw [testBit_eq_of_mod hmod, testBit_sum_eq, hcol k le_rfl,
    colCarry_congr fun j hj => hcol j hj.le]

end SPTree

end Cslib.Complexity.NtimeDspace.SumProduct
