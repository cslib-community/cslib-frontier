/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.SplayTree.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Logb

/-!
# Sleator–Tarjan's Access Lemma, Static Optimality, and Update Bounds

This module formalizes the potential-method amortized analysis of self-adjusting splay trees due to
Sleator and Tarjan ([SleatorTarjan1985b], Sections 2–3, pp. 656–665).

Given any positive weight assignment `w : α → ℝ` (`∀ x, 0 < w x` — a purely analytical parameter
not stored in the tree), each subtree `t` has size `subtreeWeight w t`, binary-logarithm rank
`nodeRank w t = Real.logb 2 (subtreeWeight w t)` ([SleatorTarjan1985b], Section 2, p. 658,
Footnote 1), and tree potential `potential w t` summing `nodeRank w` over all internal subtrees of
`t`. Following [SleatorTarjan1985b], Section 2, p. 658, `splayTime res = max res.rotations 1`
charges one unit when no rotations occur and the exact rotation count otherwise.

## Main definitions

* `subtreeWeight`, `nodeRank`, `potential`: parameterized subtree weight, base-2 logarithmic node
  rank, and rank-sum potential ([SleatorTarjan1985b], Section 2, p. 658).
* `splayTime`, `splaySeq`, `splaySeqTime`, `splaySeqRotations`: single-splay and multi-access
  sequence cost measures.
* `unitWeight`, `unitPotential`: unit-weight specialization (`w = fun _ => 1`) used for the
  Balance Theorem and dynamic dictionary updates ([SleatorTarjan1985b], Section 2, Theorem 1,
  p. 659; Section 3, Lemma 2 and Theorem 6, pp. 663–665).

## Main results

* `splayUp_amortized_le`, `splay_splayTime_amortized_le`, `exists_mem_splay_splayTime_amortized_le`,
  `splay_splayTime_amortized_le_of_mem`: Sleator and Tarjan's **Access Lemma**
  ([SleatorTarjan1985b], Section 2, Lemma 1, p. 658).
* `potential_sub_potential_le_sum_logb`: fixed-weight net potential drop bound
  `Φ(t₁) - Φ(t₂) ≤ ∑_{y ∈ t₁} log₂(W / w(y))` ([SleatorTarjan1985b], Section 2, p. 659), with
  the potential bounds `sum_logb_weight_le_potential` and `potential_le_sum_logb_of_le`.
* `splaySeqTime_le_fixed_weights`: the general fixed-weight access-sequence bound
  `∑ⱼ (3 log₂(W / w(xⱼ)) + 1) + ∑_{y ∈ t} log₂(W / w(y))` for accesses to present items
  ([SleatorTarjan1985b], Section 2, p. 659), from which the static finger bound follows.
* `potential_le_potential_of_le`, `potential_reweight_root_le`: potential change under weight
  reassignment; decreasing weights, or moving weight onto the root key without changing the total,
  does not increase the potential ([SleatorTarjan1985b], Section 2, proof of Theorem 4, p. 660;
  Section 3, Lemma 2, pp. 663–664).
* `splaySeqTime_le_balance`: **Balance Theorem** ([SleatorTarjan1985b], Section 2, Theorem 1,
  p. 659), bounding any sequence of `m` accesses (present or absent) on an `n`-element splay tree
  by `(3m + n) log₂ n + m`.
* `splaySeqTime_le_static_optimality`: **Static Optimality Theorem** ([SleatorTarjan1985b],
  Section 2, Theorem 2, p. 659), bounding `m` accesses to present items (each accessed at least
  once) by `m + 4 ∑_{y ∈ t} q(y) log₂(m / q(y))`.
* `contains_unitPotential_amortized_le`, `split_unitPotential_amortized_le`,
  `join_unitPotential_amortized_le`, `insert_unitPotential_amortized_le`,
  `erase_unitPotential_amortized_le`: unit-weight (`w = 1`) specialization of Sleator and Tarjan's
  **Update Lemma** ([SleatorTarjan1985b], Section 3, Lemma 2, pp. 663–664, where `log₂ 1 = 0`
  eliminates Lemma 2's external-item potential term), extended to total set-idempotent `insert`
  and `erase`.
* `minimum_unitPotential_amortized_le`, `successor_unitPotential_amortized_le`: companion
  unit-weight rotation bounds derived from the Access Lemma ([SleatorTarjan1985b], Section 2,
  Lemma 1, p. 658) for `Cslib.DataStructure.OrderedSet.spec` (`minimum` and `successor` are not
  part of Lemma 2).

## References

* [SleatorTarjan1985b] Daniel Dominic Sleator and Robert Endre Tarjan,
  *Self-Adjusting Binary Search Trees*, Journal of the ACM 32(3), Sections 2–3, pp. 656–665, 1985.
-/

public section

namespace Cslib.DataStructure.SplayTree

open Cslib.DataStructure.SearchTree (elements Ordered mem_elements_node card_elements)

/-! ### Subtree Weights, Node Ranks, and Rank-Sum Potential -/

section Weights

variable {α : Type*}

/-- Sum of item weights `w` over all internal nodes of a `BinaryTree α`
(`s(x)` in [SleatorTarjan1985b], Section 2, p. 658). -/
@[expose] noncomputable def subtreeWeight (w : α → ℝ) : BinaryTree α → ℝ
  | .nil => 0
  | .node a l r => w a + subtreeWeight w l + subtreeWeight w r

@[simp] theorem subtreeWeight_nil (w : α → ℝ) : subtreeWeight w (.nil : BinaryTree α) = 0 := rfl

@[simp] theorem subtreeWeight_node (w : α → ℝ) (a : α) (l r : BinaryTree α) :
    subtreeWeight w (.node a l r) = w a + subtreeWeight w l + subtreeWeight w r := rfl

theorem subtreeWeight_nonneg {w : α → ℝ} (hw : ∀ x, 0 ≤ w x) (t : BinaryTree α) :
    0 ≤ subtreeWeight w t := by
  induction t with
  | nil => exact le_rfl
  | node a _ _ ihl ihr => simp only [subtreeWeight_node]; linarith [hw a]

private theorem subtreeWeight_node_bounds {w : α → ℝ} (hw : ∀ x, 0 ≤ w x)
    (a : α) (l r : BinaryTree α) :
    w a ≤ subtreeWeight w (.node a l r) ∧
    subtreeWeight w l ≤ subtreeWeight w (.node a l r) ∧
    subtreeWeight w r ≤ subtreeWeight w (.node a l r) := by
  rw [subtreeWeight_node]
  have hl := subtreeWeight_nonneg hw l
  have hr := subtreeWeight_nonneg hw r
  exact ⟨(le_add_of_nonneg_right hl).trans (le_add_of_nonneg_right hr),
    (le_add_of_nonneg_left (hw a)).trans (le_add_of_nonneg_right hr),
    le_add_of_nonneg_left (add_nonneg (hw a) hl)⟩

theorem subtreeWeight_pos {w : α → ℝ} (hw : ∀ x, 0 < w x) {t : BinaryTree α} (ht : t ≠ .nil) :
    0 < subtreeWeight w t := by
  cases t with
  | nil => exact (ht rfl).elim
  | node a l r =>
    exact (hw a).trans_le (subtreeWeight_node_bounds (fun x => (hw x).le) a l r).1

theorem subtreeWeight_plug_congr (w : α → ℝ) {t₁ t₂ : BinaryTree α} (ctx : List (Frame α))
    (h : subtreeWeight w t₁ = subtreeWeight w t₂) :
    subtreeWeight w (plug t₁ ctx) = subtreeWeight w (plug t₂ ctx) := by
  induction ctx generalizing t₁ t₂ with
  | nil => exact h
  | cons f _ ih => cases f <;> exact ih (by simp only [subtreeWeight_node, h])

theorem le_subtreeWeight_plug {w : α → ℝ} (hw : ∀ x, 0 ≤ w x) (t : BinaryTree α)
    (ctx : List (Frame α)) :
    subtreeWeight w t ≤ subtreeWeight w (plug t ctx) := by
  induction ctx generalizing t with
  | nil => exact le_rfl
  | cons f _ ih =>
    cases f with
    | left p r => exact (subtreeWeight_node_bounds hw p t r).2.1.trans (ih _)
    | right l p => exact (subtreeWeight_node_bounds hw p l t).2.2.trans (ih _)

theorem subtreeWeight_splayUp (w : α → ℝ) (x : α) (l r : BinaryTree α) (ctx : List (Frame α)) :
    subtreeWeight w (splayUp x l r ctx).tree = subtreeWeight w (plug (.node x l r) ctx) := by
  induction l, r, ctx using splayUp.induct x with
  | case1 => rfl
  | case2 | case3 =>
    simp only [splayUp, plug_left, plug_right, plug_nil, subtreeWeight_node]
    ac_rfl
  | case4 _ _ _ _ _ _ _ ih | case5 _ _ _ _ _ _ _ ih | case6 _ _ _ _ _ _ _ ih
    | case7 _ _ _ _ _ _ _ ih =>
    simp only [splayUp, plug_left, plug_right]
    exact ih.trans (subtreeWeight_plug_congr w _ (by simp only [subtreeWeight_node]; ac_rfl))

@[simp] theorem subtreeWeight_splayMin (w : α → ℝ) (t : BinaryTree α) :
    subtreeWeight w (splayMin t).tree = subtreeWeight w t := by
  simp only [splayMin]
  cases hf : focusMin t [] with
  | none => simp [(focusMin_eq_none_iff t []).mp hf]
  | some f =>
    exact (subtreeWeight_splayUp w f.key f.leftSub f.rightSub f.ctx).trans
      (congrArg (subtreeWeight w) (focusMin_spec hf).1)

@[simp] theorem subtreeWeight_splayMax (w : α → ℝ) (t : BinaryTree α) :
    subtreeWeight w (splayMax t).tree = subtreeWeight w t := by
  simp only [splayMax]
  cases hf : focusMax t [] with
  | none => simp [(focusMax_eq_none_iff t []).mp hf]
  | some f =>
    exact (subtreeWeight_splayUp w f.key f.leftSub f.rightSub f.ctx).trans
      (congrArg (subtreeWeight w) (focusMax_spec hf).1)

/-- Base-2 logarithmic rank `r(x) = log₂ s(x)` of a subtree ([SleatorTarjan1985b], Section 2,
p. 658, Footnote 1). -/
@[expose] noncomputable def nodeRank (w : α → ℝ) (t : BinaryTree α) : ℝ :=
  Real.logb 2 (subtreeWeight w t)

@[simp] theorem nodeRank_nil (w : α → ℝ) : nodeRank w (.nil : BinaryTree α) = 0 := by
  simp [nodeRank]

theorem nodeRank_congr {w : α → ℝ} {t₁ t₂ : BinaryTree α}
    (h : subtreeWeight w t₁ = subtreeWeight w t₂) :
    nodeRank w t₁ = nodeRank w t₂ := by
  simp only [nodeRank, h]

theorem nodeRank_mono {w : α → ℝ} {t₁ t₂ : BinaryTree α}
    (hpos : 0 < subtreeWeight w t₁) (hle : subtreeWeight w t₁ ≤ subtreeWeight w t₂) :
    nodeRank w t₁ ≤ nodeRank w t₂ :=
  Real.logb_le_logb_of_le (by norm_num) hpos hle

/-- Sleator–Tarjan potential `Φ(t) = ∑_x r(x)` summing `nodeRank w` over all internal subtrees of
`t` ([SleatorTarjan1985b], Section 2, p. 658). -/
@[expose] noncomputable def potential (w : α → ℝ) : BinaryTree α → ℝ
  | .nil => 0
  | .node a l r => nodeRank w (.node a l r) + potential w l + potential w r

@[simp] theorem potential_nil (w : α → ℝ) : potential w (.nil : BinaryTree α) = 0 := rfl

@[simp] theorem potential_node (w : α → ℝ) (a : α) (l r : BinaryTree α) :
    potential w (.node a l r) = nodeRank w (.node a l r) + potential w l + potential w r := rfl

/-- Local restructurings that preserve `subtreeWeight` leave the ranks of all proper ancestors in
`ctx` unchanged, so the global potential difference equals the local potential difference. -/
theorem potential_plug_sub_eq (w : α → ℝ) {t₁ t₂ : BinaryTree α} (ctx : List (Frame α))
    (hsw : subtreeWeight w t₁ = subtreeWeight w t₂) :
    potential w (plug t₁ ctx) - potential w (plug t₂ ctx) =
      potential w t₁ - potential w t₂ := by
  induction ctx generalizing t₁ t₂ with
  | nil => rfl
  | cons f ctx ih =>
    have hw := subtreeWeight_plug_congr w [f] hsw
    rw [show f :: ctx = [f] ++ ctx from rfl, plug_append, plug_append, ih hw]
    have hr := nodeRank_congr hw
    cases f <;>
      simp only [plug_left, plug_right, plug_nil] at hr ⊢ <;>
      simp only [potential_node, hr, add_sub_add_left_eq_sub, add_sub_add_right_eq_sub]

/-- Sleator–Tarjan running-time measure for a single splay ([SleatorTarjan1985b], Section 2,
p. 658): the number of rotations performed, or `1` when zero rotations are performed. -/
@[expose] def splayTime (res : SplayResult α) : ℕ :=
  max res.rotations 1

theorem rotations_le_splayTime (res : SplayResult α) : res.rotations ≤ splayTime res :=
  le_max_left _ _

theorem one_le_splayTime (res : SplayResult α) : 1 ≤ splayTime res :=
  le_max_right _ _

/-- An amortized `splayTime` bound gives the same amortized bound on rotations. -/
private theorem rotations_amortized_le {res : SplayResult α} {a c b : ℝ}
    (h : (splayTime res : ℝ) + a - c ≤ b) : (res.rotations : ℝ) + a - c ≤ b := by
  have : (res.rotations : ℝ) ≤ splayTime res := by exact_mod_cast rotations_le_splayTime res
  linarith

/-! ### Elementary AM-GM Binary-Logarithm Inequality and Bottom-Up Access Lemma -/

/-- Elementary AM-GM inequality in base-2 logarithms: for `0 < a`, `0 < b`, and `a + b ≤ s`,
`2 + log₂ a + log₂ b ≤ 2 log₂ s` ([SleatorTarjan1985b], Section 2, proof of Lemma 1, p. 658). -/
private theorem two_add_logb_two_add_le {a b s : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b ≤ s) :
    2 + Real.logb 2 a + Real.logb 2 b ≤ 2 * Real.logb 2 s := by
  have h1 : 0 ≤ (s - (a + b)) * (s + a + b) := mul_nonneg (by linarith) (by linarith)
  have h2 : 0 ≤ (a - b) ^ 2 := sq_nonneg (a - b)
  have hlog : Real.logb 2 (4 * (a * b)) ≤ Real.logb 2 (s ^ 2) :=
    Real.logb_le_logb_of_le (by norm_num) (mul_pos (by norm_num) (mul_pos ha hb)) (by nlinarith)
  have h4 : Real.logb 2 4 = 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.logb_two_pow]; norm_num
  rw [Real.logb_mul (by norm_num) (mul_ne_zero ha.ne' hb.ne'),
    Real.logb_mul ha.ne' hb.ne', h4, Real.logb_pow] at hlog
  norm_num at hlog; linarith

private theorem splayUp_zig_amortized_le {w : α → ℝ} (hw : ∀ y, 0 < w y)
    {u₀ p₁ t₀ t₁ : BinaryTree α} (hu₀_le : subtreeWeight w u₀ ≤ subtreeWeight w t₀)
    (hp₁_le : subtreeWeight w p₁ ≤ subtreeWeight w t₀)
    (hsw : subtreeWeight w t₁ = subtreeWeight w t₀ := by simp only [subtreeWeight_node]; ring)
    (hpot : potential w t₁ - potential w t₀ =
      nodeRank w t₁ - nodeRank w t₀ + nodeRank w p₁ - nodeRank w u₀ := by
        simp only [potential_node]; ring)
    (hu₀ : u₀ ≠ .nil := by simp) (hp₁ : p₁ ≠ .nil := by simp) :
    1 + potential w t₁ - potential w t₀ ≤ 3 * (nodeRank w t₀ - nodeRank w u₀) + 1 := by
  have hr_eq : nodeRank w t₁ = nodeRank w t₀ := nodeRank_congr hsw
  have hr_p₁ : nodeRank w p₁ ≤ nodeRank w t₀ := nodeRank_mono (subtreeWeight_pos hw hp₁) hp₁_le
  have hr_u₀ : nodeRank w u₀ ≤ nodeRank w t₀ := nodeRank_mono (subtreeWeight_pos hw hu₀) hu₀_le
  linarith

private theorem splayUp_double_amortized_le {w : α → ℝ} (hw : ∀ y, 0 < w y)
    {x : α} {l r l' r' p₀ g₀ c₁ c₂ m₁ : BinaryTree α} {ctx : List (Frame α)}
    (ih : ((splayUp x l' r' ctx).rotations : ℝ) +
        potential w (splayUp x l' r' ctx).tree - potential w (plug (.node x l' r') ctx) ≤
      3 * (nodeRank w (plug (.node x l' r') ctx) - nodeRank w (.node x l' r')) +
        if ctx.isEmpty then 0 else 1)
    (hamgm : subtreeWeight w c₁ + subtreeWeight w c₂ ≤ subtreeWeight w (.node x l' r'))
    (hm₁_le : subtreeWeight w m₁ ≤ subtreeWeight w (.node x l' r'))
    (hu₀_le : subtreeWeight w (.node x l r) ≤ subtreeWeight w p₀)
    (hsw : subtreeWeight w (.node x l' r') = subtreeWeight w g₀ := by
      simp only [subtreeWeight_node]; ring)
    (hpot : potential w (.node x l' r') - potential w g₀ =
      nodeRank w (.node x l' r') + nodeRank w c₁ + nodeRank w c₂ + nodeRank w m₁ -
        (nodeRank w g₀ + nodeRank w p₀ + 2 * nodeRank w (.node x l r)) := by
        simp only [potential_node]; ring)
    (hc₁ : c₁ ≠ .nil := by simp) (hc₂ : c₂ ≠ .nil := by simp) (hm₁ : m₁ ≠ .nil := by simp) :
    (((splayUp x l' r' ctx).rotations + 2 : ℕ) : ℝ) +
        potential w (splayUp x l' r' ctx).tree - potential w (plug g₀ ctx) ≤
      3 * (nodeRank w (plug g₀ ctx) - nodeRank w (.node x l r)) + 1 := by
  have hlog : 2 + nodeRank w c₁ + nodeRank w c₂ ≤ 2 * nodeRank w (.node x l' r') :=
    two_add_logb_two_add_le (subtreeWeight_pos hw hc₁) (subtreeWeight_pos hw hc₂) hamgm
  have hr_m₁ := nodeRank_mono (subtreeWeight_pos hw hm₁) hm₁_le
  have hr_u₀ := nodeRank_mono (subtreeWeight_pos hw (by simp)) hu₀_le
  have hr_local := nodeRank_congr hsw
  have hr_root := nodeRank_congr (subtreeWeight_plug_congr w ctx hsw)
  have hpot_plug := potential_plug_sub_eq w ctx hsw
  have hite : (if ctx.isEmpty then (0 : ℝ) else 1) ≤ 1 := by split <;> norm_num
  push_cast; linarith

/-- **Bottom-Up Access Lemma** ([SleatorTarjan1985b], Section 2, Lemma 1, p. 658):
for any positive weights `w`, bottom-up splaying of `(x, l, r)` through `ctx` has amortized
rotation cost at most `3 (r(root) - r(u))` when `ctx = []` and at most `3 (r(root) - r(u)) + 1`
when `ctx ≠ []`. -/
theorem splayUp_amortized_le {w : α → ℝ} (hw : ∀ y, 0 < w y)
    (x : α) (l r : BinaryTree α) (ctx : List (Frame α)) :
    ((splayUp x l r ctx).rotations : ℝ) +
        potential w (splayUp x l r ctx).tree - potential w (plug (.node x l r) ctx) ≤
      3 * (nodeRank w (plug (.node x l r) ctx) - nodeRank w (.node x l r)) +
        if ctx.isEmpty then 0 else 1 := by
  have hw0 : ∀ y, 0 ≤ w y := fun y => (hw y).le
  induction l, r, ctx using splayUp.induct x with
  | case1 => simp [splayUp]
  | case2 l r p c =>
    simp only [splayUp, plug_left, plug_nil, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
      Nat.cast_one]
    exact splayUp_zig_amortized_le hw (p₁ := .node p r c)
      (by simp only [subtreeWeight_node]; linarith [hw p, subtreeWeight_nonneg hw0 c])
      (by simp only [subtreeWeight_node]; linarith [hw x, subtreeWeight_nonneg hw0 l])
  | case3 l r c p =>
    simp only [splayUp, plug_right, plug_nil, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
      Nat.cast_one]
    exact splayUp_zig_amortized_le hw (p₁ := .node p c l)
      (by simp only [subtreeWeight_node]; linarith [hw p, subtreeWeight_nonneg hw0 c])
      (by simp only [subtreeWeight_node]; linarith [hw x, subtreeWeight_nonneg hw0 r])
  | case4 l r p c g d ctx ih =>
    simp only [splayUp, plug_left, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
    exact splayUp_double_amortized_le hw ih (p₀ := .node p (.node x l r) c) (c₁ := .node x l r)
      (c₂ := .node g c d) (m₁ := .node p r (.node g c d))
      (by simp only [subtreeWeight_node]; linarith [hw p])
      (by simp only [subtreeWeight_node]; linarith [hw x, subtreeWeight_nonneg hw0 l])
      (by simp only [subtreeWeight_node]; linarith [hw p, subtreeWeight_nonneg hw0 c])
  | case5 l r c p d g ctx ih =>
    simp only [splayUp, plug_right, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
    exact splayUp_double_amortized_le hw ih (p₀ := .node p c (.node x l r)) (c₁ := .node x l r)
      (c₂ := .node g d c) (m₁ := .node p (.node g d c) l)
      (by simp only [subtreeWeight_node]; linarith [hw p])
      (by simp only [subtreeWeight_node]; linarith [hw x, subtreeWeight_nonneg hw0 r])
      (by simp only [subtreeWeight_node]; linarith [hw p, subtreeWeight_nonneg hw0 c])
  | case6 l r a p g d ctx ih =>
    simp only [splayUp, plug_right, plug_left, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
    exact splayUp_double_amortized_le hw ih (p₀ := .node p a (.node x l r)) (c₁ := .node p a l)
      (c₂ := .node g r d) (m₁ := .node x l r)
      (by simp only [subtreeWeight_node]; linarith [hw x])
      (by simp only [subtreeWeight_node]
          linarith [hw p, hw g, subtreeWeight_nonneg hw0 a, subtreeWeight_nonneg hw0 d])
      (by simp only [subtreeWeight_node]; linarith [hw p, subtreeWeight_nonneg hw0 a])
  | case7 l r p c d g ctx ih =>
    simp only [splayUp, plug_left, plug_right, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
    exact splayUp_double_amortized_le hw ih (p₀ := .node p (.node x l r) c) (c₁ := .node g d l)
      (c₂ := .node p r c) (m₁ := .node x l r)
      (by simp only [subtreeWeight_node]; linarith [hw x])
      (by simp only [subtreeWeight_node]
          linarith [hw p, hw g, subtreeWeight_nonneg hw0 c, subtreeWeight_nonneg hw0 d])
      (by simp only [subtreeWeight_node]; linarith [hw p, subtreeWeight_nonneg hw0 c])

/-- Sleator–Tarjan `splayTime` Access Lemma on `splayUp` ([SleatorTarjan1985b], Section 2, Lemma 1,
p. 658). -/
theorem splayUp_splayTime_amortized_le {w : α → ℝ} (hw : ∀ y, 0 < w y)
    (x : α) (l r : BinaryTree α) (ctx : List (Frame α)) :
    (splayTime (splayUp x l r ctx) : ℝ) +
        potential w (splayUp x l r ctx).tree - potential w (plug (.node x l r) ctx) ≤
      3 * (nodeRank w (plug (.node x l r) ctx) - nodeRank w (.node x l r)) + 1 := by
  have h := splayUp_amortized_le hw x l r ctx
  cases ctx with
  | nil => simp [splayUp, splayTime]
  | cons f ctx' =>
    have hlen : 1 ≤ (splayUp x l r (f :: ctx')).rotations := by simp [rotations_splayUp]
    rw [show splayTime (splayUp x l r (f :: ctx')) = (splayUp x l r (f :: ctx')).rotations from
      max_eq_left hlen]
    simpa using h

/-- Unit weight `w(x) = 1` ([SleatorTarjan1985b], Section 2, Theorem 1, p. 659; Section 3,
Theorem 6, p. 665). -/
@[expose] noncomputable def unitWeight : α → ℝ := fun _ => 1

/-- Rank-sum potential under unit weights (`unitWeight`). -/
@[expose] noncomputable def unitPotential (t : BinaryTree α) : ℝ :=
  potential unitWeight t

@[simp] theorem unitPotential_nil : unitPotential (.nil : BinaryTree α) = 0 := rfl

theorem subtreeWeight_unitWeight_nonneg (t : BinaryTree α) :
    0 ≤ subtreeWeight (unitWeight (α := α)) t :=
  subtreeWeight_nonneg (fun _ => zero_le_one) t

theorem subtreeWeight_unitWeight_pos {t : BinaryTree α} (ht : t ≠ .nil) :
    0 < subtreeWeight (unitWeight (α := α)) t :=
  subtreeWeight_pos (fun _ => zero_lt_one) ht

theorem subtreeWeight_unitWeight_eq_numNodes (t : BinaryTree α) :
    subtreeWeight (unitWeight (α := α)) t = t.numNodes := by
  induction t with
  | nil => simp
  | node a l r ihl ihr =>
    simp only [subtreeWeight_node, unitWeight, ihl, ihr, BinaryTree.numNodes, Nat.cast_add,
      Nat.cast_one]
    ring

private theorem nodeRank_unitWeight_node_nonneg (a : α) (l r : BinaryTree α) :
    0 ≤ nodeRank (unitWeight (α := α)) (.node a l r) := by
  refine Real.logb_nonneg (by norm_num) ?_
  simp only [subtreeWeight_node, unitWeight]
  linarith [subtreeWeight_unitWeight_nonneg l, subtreeWeight_unitWeight_nonneg r]

private theorem nodeRank_unitWeight_nil_left_le (a : α) (l r : BinaryTree α) :
    nodeRank (unitWeight (α := α)) (.node a .nil r) ≤
      nodeRank (unitWeight (α := α)) (.node a l r) := by
  refine nodeRank_mono (subtreeWeight_unitWeight_pos (by simp)) ?_
  simp only [subtreeWeight_node, subtreeWeight_nil]; linarith [subtreeWeight_unitWeight_nonneg l]

private theorem nodeRank_unitWeight_nil_right_le (a : α) (l r : BinaryTree α) :
    nodeRank (unitWeight (α := α)) (.node a l .nil) ≤
      nodeRank (unitWeight (α := α)) (.node a l r) := by
  refine nodeRank_mono (subtreeWeight_unitWeight_pos (by simp)) ?_
  simp only [subtreeWeight_node, subtreeWeight_nil]; linarith [subtreeWeight_unitWeight_nonneg r]

theorem unitPotential_nonneg (t : BinaryTree α) : 0 ≤ unitPotential t := by
  induction t with
  | nil => exact le_rfl
  | node a l r ihl ihr =>
    simp only [unitPotential, potential_node] at ihl ihr ⊢
    linarith [nodeRank_unitWeight_node_nonneg a l r]

end Weights

/-! ### Access Lemma on Search Trees, Balance Theorem, and Static Optimality -/

section OrderedAccess

variable {α : Type*} [LinearOrder α]

@[simp] theorem subtreeWeight_splay (w : α → ℝ) (x : α) (t : BinaryTree α) :
    subtreeWeight w (splay x t).tree = subtreeWeight w t := by
  simp only [splay]
  cases hf : focusSearch x t [] with
  | none => simp [(focusSearch_eq_none_iff x t []).mp hf]
  | some f =>
    exact (subtreeWeight_splayUp w f.key f.leftSub f.rightSub f.ctx).trans
      (congrArg (subtreeWeight w) (focusSearch_toTree_and_length hf).1)

/-- On an `Ordered` search tree, `subtreeWeight w t` equals the Finset sum of `w` over
`elements t`. -/
theorem subtreeWeight_eq_sum_elements (w : α → ℝ) {t : BinaryTree α} (ht : Ordered t) :
    subtreeWeight w t = ∑ x ∈ elements t, w x := by
  induction t with
  | nil => simp [elements]
  | node a l r ihl ihr =>
    simp only [subtreeWeight_node, elements, Finset.sum_insert ht.notMem_elements_union,
      Finset.sum_union ht.disjoint_elements, ihl ht.1, ihr ht.2.1]
    ring

theorem le_subtreeWeight_of_mem {w : α → ℝ} (hw : ∀ y, 0 ≤ w y) {t : BinaryTree α}
    (ht : Ordered t) {x : α} (hx : x ∈ elements t) :
    w x ≤ subtreeWeight w t :=
  (subtreeWeight_eq_sum_elements w ht).symm ▸ Finset.single_le_sum (fun y _ => hw y) hx

/-- **Access Lemma (focused-subtree form)** ([SleatorTarjan1985b], Section 2, Lemma 1, p. 658):
if `focusSearch x t [] = some f`, splaying `t` at `x` has amortized `splayTime` at most
`3 (r(t) - r(f.sub)) + 1`. -/
theorem splay_splayTime_amortized_le {w : α → ℝ} (hw : ∀ y, 0 < w y) {x : α} {t : BinaryTree α}
    {f : Focus α} (hf : focusSearch x t [] = some f) :
    (splayTime (splay x t) : ℝ) + potential w (splay x t).tree - potential w t ≤
      3 * (nodeRank w t - nodeRank w f.sub) + 1 := by
  have htree : plug (.node f.key f.leftSub f.rightSub) f.ctx = t := by
    simpa only [Focus.toTree, Focus.sub, plug_nil] using (focusSearch_toTree_and_length hf).1
  simp only [splay, hf, Focus.sub]
  simpa only [htree] using splayUp_splayTime_amortized_le hw f.key f.leftSub f.rightSub f.ctx

private theorem focus_splayUp_amortized_le {w : α → ℝ} (hw : ∀ y, 0 < w y)
    {t : BinaryTree α} {f : Focus α} (hf : f.toTree = t) :
    f.key ∈ elements t ∧
      (splayTime (splayUp f.key f.leftSub f.rightSub f.ctx) : ℝ) +
          potential w (splayUp f.key f.leftSub f.rightSub f.ctx).tree - potential w t ≤
        3 * Real.logb 2 (subtreeWeight w t / w f.key) + 1 := by
  have htree : plug (.node f.key f.leftSub f.rightSub) f.ctx = t := hf
  have hne : t ≠ .nil := htree ▸ plug_ne_nil_of_ne_nil (by simp) f.ctx
  refine ⟨?_, ?_⟩
  · have he := elements_splayUp f.key f.leftSub f.rightSub f.ctx
    obtain ⟨_, _, hnode⟩ := exists_node_splayUp f.key f.leftSub f.rightSub f.ctx
    rw [htree, hnode] at he; exact he ▸ by simp
  · have hup := htree ▸ splayUp_splayTime_amortized_le hw f.key f.leftSub f.rightSub f.ctx
    have hw_le := (subtreeWeight_node_bounds (fun y => (hw y).le)
      f.key f.leftSub f.rightSub).1
    have hrk_le : Real.logb 2 (w f.key) ≤ nodeRank w (.node f.key f.leftSub f.rightSub) :=
      Real.logb_le_logb_of_le (by norm_num) (hw f.key) hw_le
    have hdiv : Real.logb 2 (subtreeWeight w t / w f.key) = nodeRank w t - Real.logb 2 (w f.key) :=
      Real.logb_div (subtreeWeight_pos hw hne).ne' (hw f.key).ne'
    change _ ≤ 3 * (nodeRank w t - nodeRank w (.node f.key f.leftSub f.rightSub)) + 1 at hup
    linarith

/-- **Access Lemma (general key-weight form)** ([SleatorTarjan1985b], Section 2, Lemma 1, p. 658;
Section 3, p. 664): on any non-empty `Ordered` tree `t` and any query `x` (present or absent),
there exists a key `u ∈ elements t` (equal to `x` if `x ∈ elements t`, and otherwise unspecified)
such that the amortized `splayTime` of `splay x t` is at most `3 log₂(W / w(u)) + 1`. -/
theorem exists_mem_splay_splayTime_amortized_le {w : α → ℝ} (hw : ∀ y, 0 < w y)
    {t : BinaryTree α} (ht : Ordered t) (hne : t ≠ .nil) (x : α) :
    ∃ u ∈ elements t, (x ∈ elements t → u = x) ∧
      (splayTime (splay x t) : ℝ) + potential w (splay x t).tree - potential w t ≤
        3 * Real.logb 2 (subtreeWeight w t / w u) + 1 := by
  cases hf : focusSearch x t [] with
  | none => exact (hne ((focusSearch_eq_none_iff x t []).mp hf)).elim
  | some f =>
    obtain ⟨hmem, hxeq, _⟩ := focusSearch_ordered_spec ht hf
    have hft : f.toTree = t := by simpa only [plug_nil] using (focusSearch_toTree_and_length hf).1
    exact ⟨f.key, hmem, hxeq, by simpa only [splay, hf] using (focus_splayUp_amortized_le hw hft).2⟩

/-- **Access Lemma for present keys** ([SleatorTarjan1985b], Section 2, Lemma 1, p. 658):
when `x ∈ elements t` in an `Ordered` tree `t`, splaying `t` at `x` has amortized `splayTime`
at most `3 log₂(W / w(x)) + 1`. -/
theorem splay_splayTime_amortized_le_of_mem {w : α → ℝ} (hw : ∀ y, 0 < w y)
    {t : BinaryTree α} (ht : Ordered t) {x : α} (hx : x ∈ elements t) :
    (splayTime (splay x t) : ℝ) + potential w (splay x t).tree - potential w t ≤
      3 * Real.logb 2 (subtreeWeight w t / w x) + 1 := by
  obtain ⟨_, _, hux, hbound⟩ := exists_mem_splay_splayTime_amortized_le hw ht
    (fun h => by subst h; simp [elements] at hx) x
  rwa [hux hx] at hbound

/-- Rotation-count corollary of `splay_splayTime_amortized_le_of_mem`. -/
theorem splay_rotations_amortized_le_of_mem {w : α → ℝ} (hw : ∀ y, 0 < w y)
    {t : BinaryTree α} (ht : Ordered t) {x : α} (hx : x ∈ elements t) :
    ((splay x t).rotations : ℝ) + potential w (splay x t).tree - potential w t ≤
      3 * Real.logb 2 (subtreeWeight w t / w x) + 1 :=
  rotations_amortized_le (splay_splayTime_amortized_le_of_mem hw ht hx)

/-- Amortized rotation bound for `splayMin` on a non-empty tree. -/
theorem splayMin_rotations_amortized_le {w : α → ℝ} (hw : ∀ y, 0 < w y)
    {t : BinaryTree α} (hne : t ≠ .nil) :
    ∃ m ∈ elements t,
      ((splayMin t).rotations : ℝ) + potential w (splayMin t).tree - potential w t ≤
        3 * Real.logb 2 (subtreeWeight w t / w m) + 1 := by
  cases hf : focusMin t [] with
  | none => exact (hne ((focusMin_eq_none_iff t []).mp hf)).elim
  | some f =>
    obtain ⟨hmem, hbound⟩ := focus_splayUp_amortized_le hw
      (by simpa only [plug_nil] using (focusMin_spec hf).1)
    exact ⟨f.key, hmem, by simpa only [splayMin, hf] using rotations_amortized_le hbound⟩

/-- Amortized rotation bound for `splayMax` on a non-empty tree. -/
theorem splayMax_rotations_amortized_le {w : α → ℝ} (hw : ∀ y, 0 < w y)
    {t : BinaryTree α} (hne : t ≠ .nil) :
    ∃ m ∈ elements t,
      ((splayMax t).rotations : ℝ) + potential w (splayMax t).tree - potential w t ≤
        3 * Real.logb 2 (subtreeWeight w t / w m) + 1 := by
  cases hf : focusMax t [] with
  | none => exact (hne ((focusMax_eq_none_iff t []).mp hf)).elim
  | some f =>
    obtain ⟨hmem, hbound⟩ := focus_splayUp_amortized_le hw
      (by simpa only [plug_nil] using (focusMax_spec hf).1)
    exact ⟨f.key, hmem, by simpa only [splayMax, hf] using rotations_amortized_le hbound⟩

/-! ### Fixed-Weight Potential Drop, Balance Theorem, and Static Optimality -/

/-- Lower potential bound: each node's rank is at least the logarithm of its own key's weight, so
`∑ y ∈ t, log₂ w(y) ≤ Φ(t)` ([SleatorTarjan1985b], Section 2, p. 659). -/
theorem sum_logb_weight_le_potential {w : α → ℝ} (hw : ∀ y, 0 < w y)
    {t : BinaryTree α} (ht : Ordered t) :
    ∑ y ∈ elements t, Real.logb 2 (w y) ≤ potential w t := by
  induction t with
  | nil => simp [elements]
  | node a l r ihl ihr =>
    have ha_le : Real.logb 2 (w a) ≤ nodeRank w (.node a l r) :=
      Real.logb_le_logb_of_le (by norm_num) (hw a)
        (subtreeWeight_node_bounds (fun y => (hw y).le) a l r).1
    simp only [elements, Finset.sum_insert ht.notMem_elements_union,
      Finset.sum_union ht.disjoint_elements, potential_node]
    linarith [ihl ht.1, ihr ht.2.1]

/-- Upper potential bound: if the total weight is at most `W`, every rank is at most `log₂ W`, so
`Φ(t) ≤ ∑ y ∈ t, log₂ W` ([SleatorTarjan1985b], Section 2, p. 659). -/
theorem potential_le_sum_logb_of_le {w : α → ℝ} (hw : ∀ y, 0 < w y)
    {t : BinaryTree α} (ht : Ordered t) {W : ℝ} (hW : subtreeWeight w t ≤ W) :
    potential w t ≤ ∑ _y ∈ elements t, Real.logb 2 W := by
  induction t with
  | nil => simp [elements]
  | node a l r ihl ihr =>
    obtain ⟨_, hl, hr⟩ := subtreeWeight_node_bounds (fun y => (hw y).le) a l r
    have hrk : nodeRank w (.node a l r) ≤ Real.logb 2 W :=
      Real.logb_le_logb_of_le (by norm_num) (subtreeWeight_pos hw (by simp)) hW
    simp only [elements, Finset.sum_insert ht.notMem_elements_union,
      Finset.sum_union ht.disjoint_elements, potential_node]
    rw [← add_assoc]
    exact add_le_add (add_le_add hrk (ihl ht.1 (hl.trans hW))) (ihr ht.2.1 (hr.trans hW))

/-- **Fixed-Weight Potential Drop Bound** ([SleatorTarjan1985b], Section 2, p. 659):
between any two `Ordered` trees `t₁` and `t₂` representing the same set of keys, if
`0 < W` and `subtreeWeight w t₁ ≤ W`, the net potential decrease satisfies
`potential w t₁ - potential w t₂ ≤ ∑ y ∈ elements t₁, log₂(W / w(y))`. -/
theorem potential_sub_potential_le_sum_logb {w : α → ℝ} (hw : ∀ y, 0 < w y)
    {t₁ t₂ : BinaryTree α} (ht₁ : Ordered t₁) (ht₂ : Ordered t₂)
    (helem : elements t₁ = elements t₂) {W : ℝ} (hWpos : 0 < W) (hW : subtreeWeight w t₁ ≤ W) :
    potential w t₁ - potential w t₂ ≤ ∑ y ∈ elements t₁, Real.logb 2 (W / w y) := by
  have h1 := potential_le_sum_logb_of_le hw ht₁ hW
  have h2 := helem ▸ sum_logb_weight_le_potential hw ht₂
  have hdiff : (∑ _y ∈ elements t₁, Real.logb 2 W) - (∑ y ∈ elements t₁, Real.logb 2 (w y)) =
      ∑ y ∈ elements t₁, Real.logb 2 (W / w y) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y _ => (Real.logb_div hWpos.ne' (hw y).ne').symm
  linarith

/-- Execute a sequence of `splay` operations `xs` starting from `t`, returning the final tree
and the list of per-operation `SplayResult`s. -/
@[expose] def splaySeq : List α → BinaryTree α → BinaryTree α × List (SplayResult α)
  | [], t => (t, [])
  | x :: xs, t =>
      let res := splay x t
      let rest := splaySeq xs res.tree
      (rest.1, res :: rest.2)

/-- Total Sleator–Tarjan splay time (`∑ max rotations 1`) across an access sequence `xs`. -/
@[expose] def splaySeqTime (xs : List α) (t : BinaryTree α) : ℕ :=
  ((splaySeq xs t).2.map splayTime).sum

/-- Total edge rotations across an access sequence `xs`. -/
@[expose] def splaySeqRotations (xs : List α) (t : BinaryTree α) : ℕ :=
  ((splaySeq xs t).2.map SplayResult.rotations).sum

@[simp] theorem splaySeq_nil (t : BinaryTree α) : splaySeq [] t = (t, []) := rfl

@[simp] theorem splaySeqTime_nil (t : BinaryTree α) : splaySeqTime [] t = 0 := rfl

@[simp] theorem splaySeqTime_cons (x : α) (xs : List α) (t : BinaryTree α) :
    splaySeqTime (x :: xs) t = splayTime (splay x t) + splaySeqTime xs (splay x t).tree := rfl

theorem splaySeqRotations_le_splaySeqTime (xs : List α) (t : BinaryTree α) :
    splaySeqRotations xs t ≤ splaySeqTime xs t := by
  induction xs generalizing t with
  | nil => exact le_rfl
  | cons x xs ih =>
    simp only [splaySeqRotations, splaySeqTime, splaySeq, List.map_cons, List.sum_cons]
    exact Nat.add_le_add (rotations_le_splayTime _) (ih _)

theorem splaySeq_ordered_and_elements (xs : List α) {t : BinaryTree α} (ht : Ordered t) :
    Ordered (splaySeq xs t).1 ∧ elements (splaySeq xs t).1 = elements t := by
  induction xs generalizing t with
  | nil => exact ⟨ht, rfl⟩
  | cons x xs ih =>
    simp only [splaySeq]
    obtain ⟨ho, he⟩ := ih (ordered_splay ht x)
    exact ⟨ho, he.trans (elements_splay x t)⟩

@[simp] theorem subtreeWeight_splaySeq (w : α → ℝ) (xs : List α) (t : BinaryTree α) :
    subtreeWeight w (splaySeq xs t).1 = subtreeWeight w t := by
  induction xs generalizing t with
  | nil => rfl
  | cons x xs ih =>
    simp only [splaySeq]
    exact (ih (splay x t).tree).trans (subtreeWeight_splay w x t)

theorem subtreeWeight_unitWeight_eq_card {t : BinaryTree α} (ht : Ordered t) :
    subtreeWeight (unitWeight (α := α)) t = (elements t).card := by
  rw [subtreeWeight_unitWeight_eq_numNodes, card_elements ht]

private theorem splaySeqTime_unit_telescoping (xs : List α) {t : BinaryTree α}
    (ht : Ordered t) (hne : t ≠ .nil) :
    (splaySeqTime xs t : ℝ) + unitPotential (splaySeq xs t).1 - unitPotential t ≤
      xs.length * (3 * Real.logb 2 (elements t).card + 1) := by
  induction xs generalizing t with
  | nil => simp
  | cons x xs ih =>
    have hne' : (splay x t).tree ≠ .nil := fun h => hne ((tree_splay_eq_nil_iff x t).mp h)
    obtain ⟨_, _, _, hstep⟩ := exists_mem_splay_splayTime_amortized_le
      (w := unitWeight) (fun _ => zero_lt_one) ht hne x
    rw [subtreeWeight_unitWeight_eq_card ht, unitWeight, div_one] at hstep
    have hrest := ih (ordered_splay ht x) hne'
    rw [elements_splay x t] at hrest
    simp only [splaySeqTime_cons, splaySeq, List.length_cons, Nat.cast_add, Nat.cast_one]
    change (splayTime (splay x t) : ℝ) + (splaySeqTime xs (splay x t).tree : ℝ) +
        unitPotential (splaySeq xs (splay x t).tree).1 - unitPotential t ≤ _
    change (splayTime (splay x t) : ℝ) + unitPotential (splay x t).tree - unitPotential t ≤ _
      at hstep
    linarith

/-- **Balance Theorem** ([SleatorTarjan1985b], Section 2, Theorem 1, p. 659):
for any non-empty `Ordered` tree `t` of `n = (elements t).card` elements and any sequence `xs`
of `m = xs.length` accesses (whether successful or unsuccessful), the total splay time satisfies
`splaySeqTime xs t ≤ (3m + n) log₂ n + m`. -/
theorem splaySeqTime_le_balance (xs : List α) {t : BinaryTree α} (ht : Ordered t)
    (hne : t ≠ .nil) :
    (splaySeqTime xs t : ℝ) ≤
      (3 * (xs.length : ℝ) + (elements t).card) * Real.logb 2 (elements t).card + xs.length := by
  have htel := splaySeqTime_unit_telescoping xs ht hne
  obtain ⟨ho_end, he_end⟩ := splaySeq_ordered_and_elements xs ht
  have hn_pos : (0 : ℝ) < (elements t).card :=
    (subtreeWeight_unitWeight_eq_card ht).symm ▸ subtreeWeight_pos (fun _ => zero_lt_one) hne
  have hdrop := potential_sub_potential_le_sum_logb (w := unitWeight) (fun _ => zero_lt_one)
    ht ho_end he_end.symm hn_pos (subtreeWeight_unitWeight_eq_card ht).le
  simp only [unitWeight, div_one, Finset.sum_const, nsmul_eq_mul] at hdrop
  change unitPotential t - unitPotential (splaySeq xs t).1 ≤ _ at hdrop
  linarith

private theorem splaySeqTime_present_telescoping {w : α → ℝ} (hw : ∀ y, 0 < w y)
    (xs : List α) {t : BinaryTree α} (ht : Ordered t) (hxs : ∀ x ∈ xs, x ∈ elements t) :
    (splaySeqTime xs t : ℝ) + potential w (splaySeq xs t).1 - potential w t ≤
      (xs.map fun x => 3 * Real.logb 2 (subtreeWeight w t / w x) + 1).sum := by
  induction xs generalizing t with
  | nil => simp
  | cons x xs ih =>
    have hstep := splay_splayTime_amortized_le_of_mem hw ht (hxs x List.mem_cons_self)
    have hrest := ih (ordered_splay ht x)
      (fun y hy => (elements_splay x t).symm ▸ hxs y (List.mem_cons_of_mem x hy))
    rw [subtreeWeight_splay w x t] at hrest
    simp only [splaySeqTime_cons, splaySeq, List.map_cons, List.sum_cons, Nat.cast_add]
    linarith

private theorem list_sum_map_eq_sum_count {s : Finset α} (xs : List α)
    (hxs : ∀ x ∈ xs, x ∈ s) (f : α → ℝ) :
    (xs.map f).sum = ∑ y ∈ s, (xs.count y : ℝ) * f y := by
  have hs : xs.toFinset ⊆ s := fun _ hy => hxs _ (List.mem_toFinset.mp hy)
  rw [Finset.sum_list_map_count, Finset.sum_subset hs]
  · simp only [nsmul_eq_mul]
  · intro y _ hy
    rw [List.count_eq_zero_of_not_mem (mt List.mem_toFinset.mpr hy), zero_nsmul]

/-- **Static Optimality Theorem** ([SleatorTarjan1985b], Section 2, Theorem 2, p. 659):
for any `Ordered` splay tree `t` and any access sequence `xs` of present keys (`∀ x ∈ xs, x ∈ t`)
in which every key in `t` is accessed at least once (`∀ y ∈ elements t, 1 ≤ xs.count y`),
the total splay time is bounded by the empirical Shannon access-frequency sum:
`splaySeqTime xs t ≤ m + 4 ∑ y ∈ elements t, q(y) log₂(m / q(y))`, where `m = xs.length` and
`q(y) = xs.count y`. -/
theorem splaySeqTime_le_static_optimality (xs : List α) {t : BinaryTree α} (ht : Ordered t)
    (hxs : ∀ x ∈ xs, x ∈ elements t) (hq : ∀ y ∈ elements t, 1 ≤ xs.count y) :
    (splaySeqTime xs t : ℝ) ≤ (xs.length : ℝ) +
      4 * ∑ y ∈ elements t, (xs.count y : ℝ) * Real.logb 2 ((xs.length : ℝ) / xs.count y) := by
  cases t with
  | nil =>
    cases xs with
    | nil => simp
    | cons x _ => exact absurd (hxs x List.mem_cons_self) (by simp [elements])
  | node a l r =>
    set s := elements (.node a l r)
    let w : α → ℝ := fun y => if y ∈ s then (xs.count y : ℝ) else 1
    have hw : ∀ y, 0 < w y := fun y => by
      dsimp [w]; split_ifs with hy
      · exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (hq y hy)
      · exact zero_lt_one
    have hcount_sum : (xs.length : ℝ) = ∑ y ∈ s, (xs.count y : ℝ) := by
      simpa using list_sum_map_eq_sum_count xs hxs (fun _ => (1 : ℝ))
    have hW_eq : subtreeWeight w (.node a l r) = (xs.length : ℝ) := by
      rw [subtreeWeight_eq_sum_elements w ht, hcount_sum]
      exact Finset.sum_congr rfl fun y hy => by simp [w, hy]
    have hm_pos : (0 : ℝ) < xs.length := hW_eq ▸ subtreeWeight_pos hw (by simp)
    have htel := splaySeqTime_present_telescoping hw xs ht hxs
    obtain ⟨ho_end, he_end⟩ := splaySeq_ordered_and_elements xs ht
    have hdrop := potential_sub_potential_le_sum_logb hw ht ho_end he_end.symm hm_pos hW_eq.le
    rw [list_sum_map_eq_sum_count xs hxs] at htel
    have hrew_tel :
        ∑ y ∈ s, (xs.count y : ℝ) * (3 * Real.logb 2 (subtreeWeight w (.node a l r) / w y) + 1) =
          (xs.length : ℝ) +
            3 * ∑ y ∈ s, (xs.count y : ℝ) * Real.logb 2 ((xs.length : ℝ) / xs.count y) := by
      calc ∑ y ∈ s, (xs.count y : ℝ) *
              (3 * Real.logb 2 (subtreeWeight w (.node a l r) / w y) + 1)
          = ∑ y ∈ s, ((xs.count y : ℝ) +
              3 * ((xs.count y : ℝ) * Real.logb 2 ((xs.length : ℝ) / xs.count y))) :=
            Finset.sum_congr rfl fun y hy => by simp only [hW_eq, w, hy, ↓reduceIte]; ring
        _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← hcount_sum]
    have hdrop_le :
        ∑ y ∈ s, Real.logb 2 ((xs.length : ℝ) / w y) ≤
          ∑ y ∈ s, (xs.count y : ℝ) * Real.logb 2 ((xs.length : ℝ) / xs.count y) := by
      refine Finset.sum_le_sum fun y hy => ?_
      simp only [w, hy, ↓reduceIte]
      have hcy_ge : (1 : ℝ) ≤ xs.count y := by exact_mod_cast hq y hy
      have hcy_le : (xs.count y : ℝ) ≤ xs.length := by
        exact_mod_cast (List.count_le_length : xs.count y ≤ xs.length)
      have hcy_pos : (0 : ℝ) < xs.count y := zero_lt_one.trans_le hcy_ge
      have hdiv_ge : 1 ≤ (xs.length : ℝ) / xs.count y := (one_le_div hcy_pos).mpr hcy_le
      exact le_mul_of_one_le_left (Real.logb_nonneg (by norm_num) hdiv_ge) hcy_ge
    linarith

/-- **Fixed-weight access-sequence bound** ([SleatorTarjan1985b], Section 2, p. 659; the common
argument behind Theorems 1–3): for any positive weights `w` with total tree weight at most `W`,
a sequence `xs` of accesses to present keys costs at most the summed Access Lemma bounds plus the
net potential drop,
`splaySeqTime xs t ≤ ∑ⱼ (3 log₂(W / w(xⱼ)) + 1) + ∑ y ∈ t, log₂(W / w(y))`. -/
theorem splaySeqTime_le_fixed_weights {w : α → ℝ} (hw : ∀ y, 0 < w y) (xs : List α)
    {t : BinaryTree α} (ht : Ordered t) (hxs : ∀ x ∈ xs, x ∈ elements t) {W : ℝ}
    (hW : subtreeWeight w t ≤ W) :
    (splaySeqTime xs t : ℝ) ≤ (xs.map fun x => 3 * Real.logb 2 (W / w x) + 1).sum +
      ∑ y ∈ elements t, Real.logb 2 (W / w y) := by
  rcases eq_or_ne t .nil with rfl | hne
  · rcases xs with _ | ⟨x, _⟩
    · simp [elements]
    · exact absurd (hxs x List.mem_cons_self) (by simp [elements])
  have hWpos : 0 < W := (subtreeWeight_pos hw hne).trans_le hW
  have htel := splaySeqTime_present_telescoping hw xs ht hxs
  obtain ⟨ho_end, he_end⟩ := splaySeq_ordered_and_elements xs ht
  have hdrop := potential_sub_potential_le_sum_logb hw ht ho_end he_end.symm hWpos hW
  have hmap : (xs.map fun x => 3 * Real.logb 2 (subtreeWeight w t / w x) + 1).sum ≤
      (xs.map fun x => 3 * Real.logb 2 (W / w x) + 1).sum :=
    List.sum_le_sum fun x _ => by
      have hlog : Real.logb 2 (subtreeWeight w t / w x) ≤ Real.logb 2 (W / w x) :=
        Real.logb_le_logb_of_le (by norm_num) (div_pos (subtreeWeight_pos hw hne) (hw x))
          (div_le_div_of_nonneg_right hW (hw x).le)
      linarith
  linarith

/-! ### Weight Changes

The weights in the Access Lemma are analysis parameters, so a proof may change them between
operations at the cost of the resulting potential change ([SleatorTarjan1985b], Section 3,
Lemma 2, pp. 663–664: decreasing the weight of an item takes non-positive amortized time). The
Working Set Theorem ([SleatorTarjan1985b], Section 2, Theorem 4, pp. 659–660) reassigns weights
after each access while the accessed item is at the root; `potential_reweight_root_le` bounds
that potential change. -/

/-- Pointwise smaller weights on the keys of `t` give a smaller total weight. -/
theorem subtreeWeight_le_subtreeWeight {w w' : α → ℝ} {t : BinaryTree α}
    (hle : ∀ y ∈ elements t, w' y ≤ w y) :
    subtreeWeight w' t ≤ subtreeWeight w t := by
  induction t with
  | nil => exact le_rfl
  | node a l r ihl ihr =>
    have ha := hle a (by simp)
    have hl := ihl fun y hy => hle y (by simp [hy])
    have hr := ihr fun y hy => hle y (by simp [hy])
    simp only [subtreeWeight_node]
    linarith

/-- Decreasing weights never increases the potential ([SleatorTarjan1985b], Section 3, Lemma 2,
pp. 663–664): if `0 < w' y ≤ w y` for every key `y` of `t`, then `Φ_{w'}(t) ≤ Φ_w(t)`. -/
theorem potential_le_potential_of_le {w w' : α → ℝ} (hw' : ∀ y, 0 < w' y) {t : BinaryTree α}
    (hle : ∀ y ∈ elements t, w' y ≤ w y) :
    potential w' t ≤ potential w t := by
  induction t with
  | nil => exact le_rfl
  | node a l r ihl ihr =>
    have hl := ihl fun y hy => hle y (by simp [hy])
    have hr := ihr fun y hy => hle y (by simp [hy])
    have hrk : nodeRank w' (.node a l r) ≤ nodeRank w (.node a l r) :=
      Real.logb_le_logb_of_le (by norm_num) (subtreeWeight_pos hw' (by simp))
        (subtreeWeight_le_subtreeWeight hle)
    simp only [potential_node]
    linarith

/-- **Root weight reassignment** ([SleatorTarjan1985b], Section 2, proof of Theorem 4, p. 660):
if the key `x` is at the root of an `Ordered` tree `t`, and new positive weights `w'` keep the total
weight of `t` unchanged while not increasing the weight of any other key of `t`, then the
potential does not increase. The root's size is unchanged, and every other node's subtree avoids
`x`, so its size can only decrease. -/
theorem potential_reweight_root_le {w w' : α → ℝ} (hw' : ∀ y, 0 < w' y) {t : BinaryTree α}
    (ht : Ordered t) {x : α} (hroot : rootKey t = some x)
    (hW : subtreeWeight w' t = subtreeWeight w t) (hle : ∀ y ∈ elements t, y ≠ x → w' y ≤ w y) :
    potential w' t ≤ potential w t := by
  cases t with
  | nil => simp at hroot
  | node a l r =>
    obtain rfl : a = x := by simpa using hroot
    obtain ⟨_, _, hla, har⟩ := ht
    have hl := potential_le_potential_of_le hw' fun y hy => hle y (by simp [hy]) (hla y hy).ne
    have hr := potential_le_potential_of_le hw' fun y hy => hle y (by simp [hy]) (har y hy).ne'
    have hrk : nodeRank w' (.node a l r) = nodeRank w (.node a l r) := by simp only [nodeRank, hW]
    simp only [potential_node]; linarith

/-! ### Unit-Weight Update Lemma Specialization and `OrderedSet` Companion Bounds

Sleator and Tarjan's Update Lemma ([SleatorTarjan1985b], Section 3, Lemma 2, pp. 663–664) states
general positive-weight bounds for `access`, `join`, `split`, `insert` (assuming `x ∉ t`), and
`delete` (assuming `x ∈ t`) under a multi-tree potential incorporating `∑_{i ∉ trees} log₂ w(i)`.
At unit weights (`unitWeight`, where `log₂ 1 = 0`), that external-item potential term vanishes.
Below we prove this unit-weight specialization for `contains`, `split`, `join`, and total
set-idempotent `insert` and `erase`, together with companion unit-weight bounds for `minimum` and
`successor` derived directly from the Access Lemma (`Lemma 1`, p. 658). -/

theorem unitPotential_le_card_mul_logb {t : BinaryTree α} (ht : Ordered t) :
    unitPotential t ≤ (elements t).card * Real.logb 2 ((elements t).card + 1) := by
  have hW : subtreeWeight (unitWeight (α := α)) t ≤ (elements t).card + 1 := by
    rw [subtreeWeight_unitWeight_eq_card ht]; linarith
  have h := potential_le_sum_logb_of_le (w := unitWeight) (fun _ => zero_lt_one) ht hW
  simpa only [unitPotential, Finset.sum_const, nsmul_eq_mul] using h

private theorem logb_two_card_add_one_nonneg (n : ℕ) : 0 ≤ Real.logb 2 ((n : ℝ) + 1) :=
  Real.logb_nonneg (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) n])

private theorem unitPotential_splay_node {t : BinaryTree α} (ht : Ordered t) (hne : t ≠ .nil)
    (x : α) :
    ∃ r' l' R', (splay x t).tree = .node r' l' R' ∧
      Ordered (.node r' l' R') ∧
      subtreeWeight (unitWeight (α := α)) (.node r' l' R') = (elements t).card ∧
      ((splay x t).rotations : ℝ) + unitPotential (.node r' l' R') - unitPotential t ≤
        3 * Real.logb 2 ((elements t).card + 1) + 1 := by
  obtain ⟨_, _, _, hacc⟩ := exists_mem_splay_splayTime_amortized_le
    (w := unitWeight) (fun _ => zero_lt_one) ht hne x
  rw [subtreeWeight_unitWeight_eq_card ht, unitWeight, div_one] at hacc
  have hn_pos : (0 : ℝ) < (elements t).card :=
    (subtreeWeight_unitWeight_eq_card ht).symm ▸ subtreeWeight_unitWeight_pos hne
  have hlog_le : Real.logb 2 (elements t).card ≤ Real.logb 2 ((elements t).card + 1) :=
    Real.logb_le_logb_of_le (by norm_num) hn_pos (by linarith)
  cases hs : (splay x t).tree with
  | nil => exact (hne ((tree_splay_eq_nil_iff x t).mp hs)).elim
  | node r' l' R' =>
    have hsw : subtreeWeight (unitWeight (α := α)) (.node r' l' R') = (elements t).card := by
      rw [← subtreeWeight_unitWeight_eq_card ht, ← subtreeWeight_splay unitWeight x t, hs]
    rw [hs] at hacc
    change (splayTime (splay x t) : ℝ) + unitPotential (.node r' l' R') - unitPotential t ≤ _
      at hacc
    exact ⟨r', l', R', rfl, hs ▸ ordered_splay ht x, hsw, by linarith [rotations_amortized_le hacc]⟩

private theorem unitPotential_splayMin_node {u : BinaryTree α} (hu : u ≠ .nil) {B : ℝ}
    (hB : subtreeWeight (unitWeight (α := α)) u ≤ B) :
    ∃ m rm, (splayMin u).tree = .node m .nil rm ∧
      subtreeWeight (unitWeight (α := α)) (.node m .nil rm) =
        subtreeWeight (unitWeight (α := α)) u ∧
      ((splayMin u).rotations : ℝ) + unitPotential (.node m .nil rm) - unitPotential u ≤
        3 * Real.logb 2 B + 1 := by
  obtain ⟨m, rm, hm⟩ := exists_node_nil_left_splayMin hu
  obtain ⟨_, _, hacc⟩ := splayMin_rotations_amortized_le (w := unitWeight) (fun _ => zero_lt_one) hu
  have hlog : Real.logb 2 (subtreeWeight (unitWeight (α := α)) u) ≤ Real.logb 2 B :=
    Real.logb_le_logb_of_le (by norm_num) (subtreeWeight_unitWeight_pos hu) hB
  rw [unitWeight, div_one, hm] at hacc
  change ((splayMin u).rotations : ℝ) + unitPotential (.node m .nil rm) - unitPotential u ≤ _
    at hacc
  exact ⟨m, rm, hm, by rw [← subtreeWeight_splayMin unitWeight u, hm], by linarith⟩

/-- Unit-weight (`w = 1`) specialization of the `access` bound in [SleatorTarjan1985b], Section 3,
Lemma 2, pp. 663–664, for `contains`. -/
theorem contains_unitPotential_amortized_le {t : BinaryTree α} (ht : Ordered t) (x : α) :
    ((contains x t).rotations : ℝ) + unitPotential (contains x t).tree - unitPotential t ≤
      3 * Real.logb 2 ((elements t).card + 1) + 1 := by
  have hL := logb_two_card_add_one_nonneg (elements t).card
  cases t with
  | nil => simp only [contains, splay_nil, unitPotential_nil, Nat.cast_zero]; linarith
  | node a l r =>
    obtain ⟨r', l', R', hs, -, -, hacc⟩ := unitPotential_splay_node ht (by simp) x
    simp only [contains, hs]; linarith

/-- Companion unit-weight amortized rotation bound for `minimum`, derived from the Access Lemma
([SleatorTarjan1985b], Section 2, Lemma 1, p. 658) via `splayMin_rotations_amortized_le` (`minimum`
is not part of Section 3, Lemma 2). -/
theorem minimum_unitPotential_amortized_le {t : BinaryTree α} (ht : Ordered t) :
    ((minimum t).rotations : ℝ) + unitPotential (minimum t).tree - unitPotential t ≤
      3 * Real.logb 2 ((elements t).card + 1) + 1 := by
  have hL := logb_two_card_add_one_nonneg (elements t).card
  cases t with
  | nil => simp only [minimum, splayMin_nil, unitPotential_nil, Nat.cast_zero]; linarith
  | node a l r =>
    obtain ⟨m, rm, hm, -, hacc⟩ := unitPotential_splayMin_node
      (u := .node a l r) (B := (elements (.node a l r)).card + 1) (by simp)
      (by rw [subtreeWeight_unitWeight_eq_card ht]; linarith)
    simp only [minimum, hm]; linarith

/-- Unit-weight (`w = 1`) specialization of the `split` bound in [SleatorTarjan1985b], Section 3,
Lemma 2, pp. 663–664. -/
theorem split_unitPotential_amortized_le {t : BinaryTree α} (ht : Ordered t) (x : α) :
    ((split x t).rotations : ℝ) +
        unitPotential (split x t).left + unitPotential (split x t).right - unitPotential t ≤
      3 * Real.logb 2 ((elements t).card + 1) + 1 := by
  have hL := logb_two_card_add_one_nonneg (elements t).card
  cases t with
  | nil => simp only [split, splay_nil, unitPotential_nil, Nat.cast_zero]; linarith
  | node a l r =>
    obtain ⟨r', l', R', hs, -, -, hacc⟩ := unitPotential_splay_node ht (by simp) x
    simp only [split, hs]
    split <;> dsimp only <;>
      [have hrk := nodeRank_unitWeight_nil_left_le r' l' R';
       have hrk := nodeRank_unitWeight_nil_right_le r' l' R'] <;>
      (simp only [unitPotential, potential_node, potential_nil] at hacc ⊢; linarith)

/-- Unit-weight (`w = 1`) specialization of the `join` bound in [SleatorTarjan1985b], Section 3,
Lemma 2, pp. 663–664. -/
theorem join_unitPotential_amortized_le {t₁ t₂ : BinaryTree α}
    (ht₁ : Ordered t₁) (ht₂ : Ordered t₂) :
    ((join t₁ t₂).rotations : ℝ) +
        unitPotential (join t₁ t₂).tree - (unitPotential t₁ + unitPotential t₂) ≤
      3 * Real.logb 2 ((elements t₁).card + (elements t₂).card + 1) + 1 := by
  have hn₁_nn : (0 : ℝ) ≤ (elements t₁).card := Nat.cast_nonneg _
  have hn₂_nn : (0 : ℝ) ≤ (elements t₂).card := Nat.cast_nonneg _
  have hL : 0 ≤ Real.logb 2 (((elements t₁).card : ℝ) + (elements t₂).card + 1) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  cases t₁ with
  | nil => simp only [join, unitPotential_nil, Nat.cast_zero]; linarith
  | node a l r =>
    have hne : BinaryTree.node a l r ≠ .nil := by simp
    obtain ⟨m, lm, hm⟩ := exists_node_nil_right_splayMax (t := .node a l r) hne
    obtain ⟨_, _, hacc⟩ := splayMax_rotations_amortized_le
      (w := unitWeight) (fun _ => zero_lt_one) hne
    rw [subtreeWeight_unitWeight_eq_card ht₁, unitWeight, div_one, hm] at hacc
    have hn₁_pos : (0 : ℝ) < (elements (.node a l r)).card :=
      (subtreeWeight_unitWeight_eq_card ht₁).symm ▸ subtreeWeight_unitWeight_pos hne
    have hlog₁ : Real.logb 2 (elements (.node a l r)).card ≤
        Real.logb 2 (((elements (.node a l r)).card : ℝ) + (elements t₂).card + 1) :=
      Real.logb_le_logb_of_le (by norm_num) hn₁_pos (by linarith)
    have hsw_m : subtreeWeight (unitWeight (α := α)) (.node m lm .nil) =
        (elements (.node a l r)).card := by
      rw [← subtreeWeight_unitWeight_eq_card ht₁,
        ← subtreeWeight_splayMax unitWeight (.node a l r), hm]
    have hrk_m : nodeRank (unitWeight (α := α)) (.node m lm .nil) =
        Real.logb 2 (elements (.node a l r)).card := by rw [nodeRank, hsw_m]
    have hrk_join : nodeRank (unitWeight (α := α)) (.node m lm t₂) ≤
        Real.logb 2 (((elements (.node a l r)).card : ℝ) + (elements t₂).card + 1) := by
      refine Real.logb_le_logb_of_le (by norm_num) (subtreeWeight_unitWeight_pos (by simp)) ?_
      have hsw₂ := subtreeWeight_unitWeight_eq_card ht₂
      simp only [subtreeWeight_node, subtreeWeight_nil] at hsw_m ⊢; linarith
    simp only [join, hm, unitPotential, potential_node, potential_nil, hrk_m] at hacc ⊢
    linarith

/-- Unit-weight (`w = 1`) specialization of the `insert` bound in [SleatorTarjan1985b], Section 3,
Lemma 2, pp. 663–664, extended from `x ∉ elements t` to total set-idempotent `insert`. -/
theorem insert_unitPotential_amortized_le {t : BinaryTree α} (ht : Ordered t) (x : α) :
    ((insert x t).rotations : ℝ) + unitPotential (insert x t).tree - unitPotential t ≤
      4 * Real.logb 2 ((elements t).card + 1) + 1 := by
  have hL := logb_two_card_add_one_nonneg (elements t).card
  cases t with
  | nil =>
    have hrk0 : nodeRank (unitWeight (α := α)) (.node x .nil .nil) = 0 := by
      simp [nodeRank, unitWeight]
    simp only [insert, unitPotential, potential_node, potential_nil, hrk0, Nat.cast_zero]; linarith
  | node a l r =>
    obtain ⟨r', l', R', hs, -, hsw, hacc⟩ := unitPotential_splay_node ht (by simp) x
    have hrk_eq : ∀ t₁ t₂ : BinaryTree α,
        subtreeWeight (unitWeight (α := α)) t₁ + subtreeWeight unitWeight t₂ =
          subtreeWeight unitWeight (.node r' l' R') →
        nodeRank (unitWeight (α := α)) (.node x t₁ t₂) =
          Real.logb 2 ((elements (.node a l r)).card + 1) := fun t₁ t₂ h => by
      simp only [nodeRank, subtreeWeight_node, unitWeight] at hsw h ⊢; congr 1; linarith
    simp only [insert, hs]
    split
    · have hrk_sub := nodeRank_unitWeight_nil_left_le r' l' R'
      have hrk_new := hrk_eq l' (.node r' .nil R')
        (by simp only [subtreeWeight_node, subtreeWeight_nil]; ring)
      simp only [unitPotential, potential_node, potential_nil, hrk_new] at hacc ⊢; linarith
    · split <;> dsimp only
      · have hrk_sub := nodeRank_unitWeight_nil_right_le r' l' R'
        have hrk_new := hrk_eq (.node r' l' .nil) R'
          (by simp only [subtreeWeight_node, subtreeWeight_nil]; ring)
        simp only [unitPotential, potential_node, potential_nil, hrk_new] at hacc ⊢; linarith
      · linarith

/-- Unit-weight (`w = 1`) specialization of the `delete` bound in [SleatorTarjan1985b], Section 3,
Lemma 2, pp. 663–664, extended from `x ∈ elements t` to total set-idempotent `erase`. -/
theorem erase_unitPotential_amortized_le {t : BinaryTree α} (ht : Ordered t) (x : α) :
    ((erase x t).rotations : ℝ) + unitPotential (erase x t).tree - unitPotential t ≤
      6 * Real.logb 2 ((elements t).card + 1) + 2 := by
  have hL := logb_two_card_add_one_nonneg (elements t).card
  cases t with
  | nil => simp only [erase, unitPotential_nil, Nat.cast_zero]; linarith
  | node a l r =>
    obtain ⟨r', l', R', hs, ho', hsw, hacc⟩ := unitPotential_splay_node ht (by simp) x
    simp only [erase, hs]
    split <;> dsimp only
    · have hjoin := join_unitPotential_amortized_le ho'.1 ho'.2.1
      have hcard_le : ((elements l').card : ℝ) + (elements R').card + 1 ≤
          (elements (.node a l r)).card + 1 := by
        have hl := subtreeWeight_unitWeight_eq_card ho'.1
        have hR := subtreeWeight_unitWeight_eq_card ho'.2.1
        simp only [subtreeWeight_node, unitWeight] at hsw; linarith
      have hlog_join : Real.logb 2 (((elements l').card : ℝ) + (elements R').card + 1) ≤
          Real.logb 2 ((elements (.node a l r)).card + 1) :=
        Real.logb_le_logb_of_le (by norm_num) (by positivity) hcard_le
      have hrk_nn := nodeRank_unitWeight_node_nonneg r' l' R'
      simp only [unitPotential, potential_node, Nat.cast_add] at hacc hjoin ⊢; linarith
    · linarith

/-- Companion unit-weight amortized rotation bound for `successor` (splaying `x`, followed by
`splayMin` on the right subtree when `root ≤ x`), derived from the Access Lemma
([SleatorTarjan1985b], Section 2, Lemma 1, p. 658; `successor` is not part of Section 3,
Lemma 2). -/
theorem successor_unitPotential_amortized_le {t : BinaryTree α} (ht : Ordered t) (x : α) :
    ((successor x t).rotations : ℝ) + unitPotential (successor x t).tree - unitPotential t ≤
      7 * Real.logb 2 ((elements t).card + 1) + 3 := by
  have hL := logb_two_card_add_one_nonneg (elements t).card
  cases t with
  | nil => simp only [successor, splay_nil, unitPotential_nil, Nat.cast_zero]; linarith
  | node a l r =>
    obtain ⟨r', l', R', hs, -, hsw, hacc⟩ := unitPotential_splay_node ht (by simp) x
    simp only [successor, hs]
    split
    · dsimp only; linarith
    · cases hR_eq : R' with
      | nil => rw [hR_eq] at hacc; linarith
      | node b rl rr =>
        have hsw_R_le : subtreeWeight (unitWeight (α := α)) (.node b rl rr) ≤
            (elements (.node a l r)).card + 1 := by
          rw [hR_eq] at hsw
          simp only [subtreeWeight_node, unitWeight] at hsw ⊢
          linarith [subtreeWeight_unitWeight_nonneg l']
        obtain ⟨m, rm, hm, hsw_m, hacc_R⟩ := unitPotential_splayMin_node (by simp) hsw_R_le
        have hrk_m_nn := nodeRank_unitWeight_node_nonneg m .nil rm
        have hrk_root_eq : nodeRank (unitWeight (α := α)) (.node m (.node r' l' .nil) rm) =
            nodeRank (unitWeight (α := α)) (.node r' l' (.node b rl rr)) :=
          nodeRank_congr (by
            simp only [subtreeWeight_node, subtreeWeight_nil, unitWeight] at hsw_m ⊢; linarith)
        have hrk_left_le : nodeRank (unitWeight (α := α)) (.node r' l' .nil) ≤
            Real.logb 2 ((elements (.node a l r)).card + 1) := by
          refine Real.logb_le_logb_of_le (by norm_num) (subtreeWeight_unitWeight_pos (by simp)) ?_
          rw [hR_eq] at hsw; simp only [subtreeWeight_node, subtreeWeight_nil, unitWeight] at hsw ⊢
          linarith [subtreeWeight_unitWeight_nonneg rl, subtreeWeight_unitWeight_nonneg rr]
        rw [hR_eq] at hacc
        simp only [hm, unitPotential, potential_node, potential_nil, hrk_root_eq, Nat.cast_add,
          Nat.cast_one] at hacc hacc_R ⊢
        linarith

end OrderedAccess

end Cslib.DataStructure.SplayTree
