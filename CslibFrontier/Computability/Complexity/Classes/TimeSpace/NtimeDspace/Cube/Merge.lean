/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.MergeAux
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.RowCut

/-!
# One merge (§6.1, Lemma 6.2)

Fix a clique on the `g × g` grid: budgets `a` and tables `T` on the nodes `node A B` (row `A`,
column `B`). A *choice* `ι` gives every rectangle `R` a grade `k_R` and a split `c_R`.

* `rowChild g a T ι`: the row clique `𝒞^row_ι` of (eq:table). Its nodes are the rows, its budgets
  `rowBudget a k`, and the table of row `A` at the packed labels `Θ` (one for every other row, in
  canonical orientation) is `0` unless every `Θ A'` is valid, and otherwise the sum, over the
  settings `ξ` of the old nodes of row `A` (the copies they hold of their labels, each of exact
  weight), of the product of the old tables, the horizontal tests, the vertical tests against the
  unpacked labels, and one factor `Ψ_R` for every rectangle with `A` among its rows.
* `trBudget`, `trTable`: the transposed clique, on the nodes `node B A`; labels of pairs whose
  order flips (the anti-diagonals) are reversed.
* `colChild g a T ι`: the column clique, the row clique of the transposed clique with the grades
  negated (Lemma 5.3 turns the row cut of the transposed rectangle into the column cut).
* `merge` (Lemma 6.2): `Z(𝒞) = ∑_ι Z(𝒞^{o(ι)}_ι)` for every rule `o` choosing an orientation
  from the grades.

Streams between two rows (or columns): vertical (horizontal) pairs `B ↦ 1 + B`, then rectangles
`(B, B') ↦ 1 + g + pairRank g B B'` in lexicographic order.

The proof (namespace `MergeProof`) follows the paper. `value_eq_copies` writes `Z(𝒞)` as a sum over
all copies, grouped by rows, with one equality test per pair; `value_eq_sum_Zk` turns the
diagonal tests of each rectangle into `∑_k Π_k` (Lemma 5.2 and the grade bound), giving
`Z(𝒞) = ∑_k Z_k`. `Zk_eq_row` expands the tables of the row clique and recovers `Z_k` by the
packing bijection (`sum_valid_unpack`) and the row cut; `Zk_transpose` (Lemma 5.3) reduces the
column orientation to the row orientation of the transposed clique.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cube

open Finset

variable {g : ℕ}

/-! ### Helpers -/

/-- The budget of the pair `{u, v}` (symmetric). -/
def budget {n : ℕ} (a : Fin n → Fin n → ℕ) (u v : Fin n) : ℕ := a (min u v) (max u v)

/-- The views of a stored (canonical) label from its smaller end and from its larger end. -/
def swapLabel (l : Label) : Label := (l.2, l.1)

/-- The lexicographic rank of a pair `B < B'` among the pairs of `Fin g`. -/
def pairRank (g : ℕ) (B B' : Fin g) : ℕ := (∑ b ∈ Finset.range B.val, (g - 1 - b)) +
    (B'.val - B.val - 1)

/-- The stream of the vertical pair in column `B`. -/
def vStream (B : Fin g) : ℕ := 1 + B.val

/-- The stream of the rectangle on columns `B < B'`. -/
def rStream (g : ℕ) (B B' : Fin g) : ℕ := 1 + g + pairRank g B B'

/-- The settings of the old nodes of row `A`: for every column `B` and every other node `u`, the
copy held by `node A B` of the label of the pair, of exact weight. -/
def rowSettings (a : Fin (g * g) → Fin (g * g) → ℕ) (A : Fin g) :
    Finset (Fin g → Fin (g * g) → Label) :=
  Fintype.piFinset fun B => Fintype.piFinset fun u =>
    if u = node A B then {((0 : Multiset ℕ), (0 : Multiset ℕ))} else labelsEq
        (budget a (node A B) u)

/-- The rectangle factor `Ψ_R` in the table of row `A` (§6.1). -/
noncomputable def rowPsi (a : Fin (g * g) → Fin (g * g) → ℕ) (ι : Rect g → ℤ × ℤ) (A : Fin g)
    (Θ : Fin g → Label) (ξ : Fin g → Fin (g * g) → Label) (r : Rect g) : ℤ :=
  let A₁ := r.1.1.1; let A₂ := r.1.1.2; let B := r.1.2.1; let B' := r.1.2.2
  let k := (ι r).1; let c := (ι r).2
  let H : ℤ := diagWt a r
  if A = A₁ then
    let m := unpack (packL g) (Θ A₂) (rStream g B B')
    if (labelWt m : ℤ) ≤ H + k / 2 then
      (nUp (ξ B (node A₂ B')) (ξ B' (node A₂ B)) m).coeff (k - c) else 0
  else if A = A₂ then
    let m := unpack (packL g) (Θ A₁) (rStream g B B')
    if (labelWt m : ℤ) ≤ H + k / 2 then
      (nDown (swapLabel (ξ B (node A₁ B'))) (swapLabel (ξ B' (node A₁ B))) m).coeff c else 0
  else 1

/-- **The table of row `A`** of the row clique (eq:table). -/
noncomputable def rowTable (a : Fin (g * g) → Fin (g * g) → ℕ)
    (T : Fin (g * g) → (Fin (g * g) → Label) → ℤ) (ι : Rect g → ℤ × ℤ) (A : Fin g)
    (Θ : Fin g → Label) : ℤ :=
  if ∀ A', A' ≠ A → validLabel (packL g) (Θ A') then
    ∑ ξ ∈ rowSettings a A,
      (∏ B, T (node A B) (ξ B)) *
      (∏ B, ∏ B', if B < B' ∧ ξ B (node A B') ≠ ξ B' (node A B) then 0 else 1) *
      (∏ A', ∏ B, if A' ≠ A ∧ ξ B (node A' B) ≠ unpack (packL g) (Θ A') (vStream B) then 0 else 1) *
      ∏ r : Rect g, rowPsi a ι A Θ ξ r
  else 0

/-- **The row clique** `𝒞^row_ι`. -/
noncomputable def rowChild (g : ℕ) (a : Fin (g * g) → Fin (g * g) → ℕ)
    (T : Fin (g * g) → (Fin (g * g) → Label) → ℤ) (ι : Rect g → ℤ × ℤ) : Clique where
  q := g
  a := fun A A' => rowBudget a (fun r => (ι r).1) A A'
  T := rowTable a T ι

/-! ### Transposition -/

/-- The transposed node: `node A B ↦ node B A`. -/
def trNode (w : Fin (g * g)) : Fin (g * g) :=
  node (⟨w.val % g, Nat.mod_lt _ (by have := w.isLt; rcases Nat.eq_zero_or_pos g with h | h <;>
    simp_all)⟩ : Fin g) ⟨w.val / g, by
      have := w.isLt
      exact Nat.div_lt_of_lt_mul this⟩

/-- The budgets of the transposed clique. -/
def trBudget (a : Fin (g * g) → Fin (g * g) → ℕ) (u v : Fin (g * g)) : ℕ :=
  budget a (trNode u) (trNode v)

/-- The tables of the transposed clique: the node `trNode w` of the transposed clique has the
table of `w`, with the labels of pairs whose order flips reversed. -/
def trTable (T : Fin (g * g) → (Fin (g * g) → Label) → ℤ) (w : Fin (g * g))
    (Θ : Fin (g * g) → Label) : ℤ :=
  T (trNode w) fun u =>
    if (w < trNode u) ↔ (trNode w < u) then Θ (trNode u) else swapLabel (Θ (trNode u))

/-- The transposed rectangle. -/
def trRect (r : Rect g) : Rect g := ⟨((r.1.2.1, r.1.2.2), (r.1.1.1, r.1.1.2)), r.2.2, r.2.1⟩

/-- **The column clique** `𝒞^col_ι`: the row clique of the transposed clique, with the grades
negated. -/
noncomputable def colChild (g : ℕ) (a : Fin (g * g) → Fin (g * g) → ℕ)
    (T : Fin (g * g) → (Fin (g * g) → Label) → ℤ) (ι : Rect g → ℤ × ℤ) : Clique :=
  rowChild g (trBudget a) (trTable T) fun r => (-(ι (trRect r)).1, (ι (trRect r)).2)

/-! ### The merge -/

/-- The choices: for every rectangle an even grade `|k| ≤ 2H_R` and a split `|c| ≤ 3H_R`. -/
def choices (a : Fin (g * g) → Fin (g * g) → ℕ) : Finset (Rect g → ℤ × ℤ) :=
  Fintype.piFinset fun r =>
    ((Icc (-(2 * (diagWt a r : ℤ))) (2 * diagWt a r)).filter fun k => Even k) ×ˢ
      Icc (-(3 * (diagWt a r : ℤ))) (3 * diagWt a r)

/-! ### Proof of the merge: the grid -/

namespace MergeProof

open Clique

theorem pos_of_fin {w : Fin (g * g)} : 0 < g := by
  rcases Nat.eq_zero_or_pos g with h | h
  · subst h; exact absurd w.isLt (by simp)
  · exact h

/-- The row of a node. -/
def rowOf (w : Fin (g * g)) : Fin g := ⟨w.val / g, Nat.div_lt_of_lt_mul w.isLt⟩

/-- The column of a node. -/
def colOf (w : Fin (g * g)) : Fin g := ⟨w.val % g, Nat.mod_lt _ (pos_of_fin (w := w))⟩

@[simp] theorem node_val (A B : Fin g) : (node A B).val = A.val * g + B.val := rfl

@[simp] theorem rowOf_node (A B : Fin g) : rowOf (node A B) = A := by
  ext
  simp only [rowOf, node_val]
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by have := A.isLt; omega),
    Nat.div_eq_of_lt B.isLt, zero_add]

@[simp] theorem colOf_node (A B : Fin g) : colOf (node A B) = B := by
  ext
  simp only [colOf, node_val]
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt B.isLt]

@[simp] theorem node_rowOf_colOf (w : Fin (g * g)) : node (rowOf w) (colOf w) = w := by
  ext
  simp only [node_val, rowOf, colOf]
  exact Nat.div_add_mod' w.val g

theorem node_eq_node_iff {A B A' B' : Fin g} : node A B = node A' B' ↔ A = A' ∧ B = B' := by
  constructor
  · intro h
    have h1 := congrArg rowOf h
    have h2 := congrArg colOf h
    simp only [rowOf_node, colOf_node] at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem node_lt_node_iff {A B A' B' : Fin g} :
    node A B < node A' B' ↔ A < A' ∨ (A = A' ∧ B < B') := by
  rw [Fin.lt_def, node_val, node_val, Fin.lt_def, Fin.lt_def,
    Fin.ext_iff]
  have hB := B.isLt
  have hB' := B'.isLt
  constructor
  · intro h
    rcases lt_trichotomy A.val A'.val with h1 | h1 | h1
    · exact Or.inl h1
    · right; refine ⟨h1, ?_⟩; rw [h1] at h; omega
    · exfalso
      have : (A'.val + 1) * g ≤ A.val * g := Nat.mul_le_mul_right _ h1
      nlinarith
  · rintro (h1 | ⟨h1, h2⟩)
    · have : (A.val + 1) * g ≤ A'.val * g := Nat.mul_le_mul_right _ h1
      nlinarith
    · rw [h1]; omega

/-- Nodes are pairs (row, column). -/
def nodeEquiv (g : ℕ) : Fin g × Fin g ≃ Fin (g * g) where
  toFun p := node p.1 p.2
  invFun w := (rowOf w, colOf w)
  left_inv p := by simp
  right_inv w := by simp

theorem prod_nodes {M : Type*} [CommMonoid M] (f : Fin (g * g) → M) :
    ∏ w, f w = ∏ A, ∏ B, f (node A B) := by
  rw [← Fintype.prod_prod_type']
  exact (Fintype.prod_equiv (nodeEquiv g) (fun p => f (node p.1 p.2)) f fun _ => rfl).symm

theorem trNode_eq (w : Fin (g * g)) : trNode w = node (colOf w) (rowOf w) := rfl

@[simp] theorem trNode_node (A B : Fin g) : trNode (node A B) = node B A := by
  rw [trNode_eq]; simp

@[simp] theorem trNode_trNode (w : Fin (g * g)) : trNode (trNode w) = w := by
  rw [trNode_eq w]; simp

theorem budget_comm {n : ℕ} (a : Fin n → Fin n → ℕ) (u v : Fin n) : budget a u v =
    budget a v u := by
  simp only [budget, min_comm, max_comm]

theorem budget_of_lt {n : ℕ} (a : Fin n → Fin n → ℕ) {u v : Fin n} (h : u < v) :
    budget a u v = a u v := by
  simp only [budget, min_eq_left h.le, max_eq_right h.le]

theorem budget_trBudget (a : Fin (g * g) → Fin (g * g) → ℕ) (u v : Fin (g * g)) :
    budget (trBudget a) u v = budget a (trNode u) (trNode v) := by
  rcases le_total u v with h | h
  · rw [budget, min_eq_left h, max_eq_right h]; rfl
  · rw [budget, min_eq_right h, max_eq_left h]; exact budget_comm _ _ _

theorem labelWt_swap (l : Label) : labelWt (swapLabel l) = labelWt l := by
  simp only [labelWt, swapLabel, Nat.add_comm]

@[simp] theorem swapLabel_swapLabel (l : Label) : swapLabel (swapLabel l) = l := rfl

theorem labelAt_of_lt {q : ℕ} (θ : Pairs q → Label) {u v : Fin q} (h : u < v) :
    labelAt θ v u = θ ⟨(u, v), h⟩ := dite_eq_left h

theorem labelAt_of_gt {q : ℕ} (θ : Pairs q → Label) {u v : Fin q} (h : v < u) :
    labelAt θ v u = θ ⟨(v, u), h⟩ := by
  rw [labelAt, dite_eq_right (not_lt.mpr h.le), dite_eq_left h]

@[simp] theorem labelAt_self {q : ℕ} (θ : Pairs q → Label) (v : Fin q) : labelAt θ v
    v = (0, 0) := by
  simp [labelAt]

theorem labelAt_comm {q : ℕ} (θ : Pairs q → Label) (u v : Fin q) : labelAt θ v u =
    labelAt θ u v := by
  rcases lt_trichotomy u v with h | rfl | h
  · rw [labelAt_of_lt θ h, labelAt_of_gt θ h]
  · rfl
  · rw [labelAt_of_gt θ h, labelAt_of_lt θ h]

theorem crossing_views (x y u v : Label) :
    crossing (views x y u v) ↔ x = swapLabel v ∧ y = swapLabel u := by
  simp only [crossing, views, swapLabel, Prod.ext_iff]
  tauto

/-! ### Copies, grouped by rows -/

/-- Copies grouped by rows: `X A B u` is the copy held by `node A B` of the label of its pair with
`u` (canonical orientation). -/
abbrev Copies (g : ℕ) := Fin g → Fin g → Fin (g * g) → Label

/-- All copies, each of the exact weight of its pair. -/
def copiesX (a : Fin (g * g) → Fin (g * g) → ℕ) : Finset (Copies g) :=
  Fintype.piFinset fun A => rowSettings a A

theorem mem_copiesX {a : Fin (g * g) → Fin (g * g) → ℕ} {X : Copies g} :
    X ∈ copiesX a ↔ ∀ A B u, X A B u ∈ (if u = node A B then {((0 : Multiset ℕ), (0 : Multiset ℕ))}
      else labelsEq (budget a (node A B) u)) := by
  simp only [copiesX, rowSettings, Fintype.mem_piFinset]

theorem copies_self {a : Fin (g * g) → Fin (g * g) → ℕ} {X : Copies g} (h : X ∈ copiesX a)
    (A B : Fin g) : X A B (node A B) = (0, 0) := by
  have := mem_copiesX.mp h A B (node A B)
  rw [ite_eq_left rfl] at this
  exact Finset.mem_singleton.mp this

theorem copies_wt {a : Fin (g * g) → Fin (g * g) → ℕ} {X : Copies g} (h : X ∈ copiesX a)
    {A B : Fin g} {u : Fin (g * g)} (hu : u ≠ node A B) :
    labelWt (X A B u) = budget a (node A B) u := by
  have := mem_copiesX.mp h A B u
  rw [ite_eq_right hu] at this
  exact mem_labelsEq.mp this

/-- The product of the old tables. -/
def tProd (T : Fin (g * g) → (Fin (g * g) → Label) → ℤ) (X : Copies g) : ℤ :=
  ∏ A, ∏ B, T (node A B) (X A B)

/-- The tests of the horizontal pairs. -/
def horTest (X : Copies g) : ℤ :=
  ∏ A, ∏ B, ∏ B', if B < B' ∧ X A B (node A B') ≠ X A B' (node A B) then 0 else 1

/-- The tests of the vertical pairs. -/
def vertTest (X : Copies g) : ℤ :=
  ∏ p : Pairs g, ∏ B, if X p.1.1 B (node p.1.2 B) = X p.1.2 B (node p.1.1 B) then 1 else 0

/-- The views of a rectangle: the copies of its diagonal labels at its four corners, seen from
their corners. -/
def rectViews (X : Copies g) (r : Rect g) : Corner → Label :=
  views (X r.1.1.1 r.1.2.1 (node r.1.1.2 r.1.2.2)) (X r.1.1.1 r.1.2.2 (node r.1.1.2 r.1.2.1))
    (swapLabel (X r.1.1.2 r.1.2.1 (node r.1.1.1 r.1.2.2)))
    (swapLabel (X r.1.1.2 r.1.2.2 (node r.1.1.1 r.1.2.1)))

/-- The test of the diagonals of all rectangles. -/
def diagTest (X : Copies g) : ℤ := ∏ r, if crossing (rectViews X r) then 1 else 0

/-- The grades allowed in a rectangle. -/
def gradeSet (a : Fin (g * g) → Fin (g * g) → ℕ) (r : Rect g) : Finset ℤ :=
  (Icc (-(2 * (diagWt a r : ℤ))) (2 * diagWt a r)).filter fun k => Even k

/-- The lists of grades. -/
def grades (a : Fin (g * g) → Fin (g * g) → ℕ) : Finset (Rect g → ℤ) :=
  Fintype.piFinset (gradeSet a)

/-- The lists of splits. -/
def splits (a : Fin (g * g) → Fin (g * g) → ℕ) : Finset (Rect g → ℤ) :=
  Fintype.piFinset fun r => Icc (-(3 * (diagWt a r : ℤ))) (3 * diagWt a r)

/-- **`Z_k`**: the sum over all copies of the old tables, the tests of the straight pairs and the
pieces of grades `k`. -/
noncomputable def Zk (a : Fin (g * g) → Fin (g * g) → ℕ)
    (T : Fin (g * g) → (Fin (g * g) → Label) → ℤ) (k : Rect g → ℤ) : ℤ :=
  ∑ X ∈ copiesX a, tProd T X * horTest X * vertTest X * ∏ r, (piece (rectViews X r)).coeff (k r)

theorem mem_grades {a : Fin (g * g) → Fin (g * g) → ℕ} {k : Rect g → ℤ} :
    k ∈ grades a ↔ ∀ r, Even (k r) ∧ |k r| ≤ 2 * diagWt a r := by
  simp only [grades, gradeSet, Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_Icc, abs_le]
  exact forall_congr' fun r => by constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h2, h1⟩

theorem rectViews_wt {a : Fin (g * g) → Fin (g * g) → ℕ} {X : Copies g} (hX : X ∈ copiesX a)
    (r : Rect g) :
    labelWt (rectViews X r .x) = a (node r.1.1.1 r.1.2.1) (node r.1.1.2 r.1.2.2) ∧
    labelWt (rectViews X r .v) = a (node r.1.1.1 r.1.2.1) (node r.1.1.2 r.1.2.2) ∧
    labelWt (rectViews X r .y) = a (node r.1.1.1 r.1.2.2) (node r.1.1.2 r.1.2.1) ∧
    labelWt (rectViews X r .u) = a (node r.1.1.1 r.1.2.2) (node r.1.1.2 r.1.2.1) := by
  have hA : r.1.1.1 < r.1.1.2 := r.2.1
  have h1 : node r.1.1.1 r.1.2.1 < node r.1.1.2 r.1.2.2 := node_lt_node_iff.mpr (Or.inl hA)
  have h2 : node r.1.1.1 r.1.2.2 < node r.1.1.2 r.1.2.1 := node_lt_node_iff.mpr (Or.inl hA)
  simp only [rectViews, views, labelWt_swap]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [copies_wt hX h1.ne', budget_of_lt a h1]
  · rw [copies_wt hX h1.ne, budget_comm, budget_of_lt a h1]
  · rw [copies_wt hX h2.ne', budget_of_lt a h2]
  · rw [copies_wt hX h2.ne, budget_comm, budget_of_lt a h2]

/-! ### Step 1: the value as a sum over copies -/

theorem hor_factor {X : Copies g} (h : horTest X ≠ 0) {A B B' : Fin g} (hB : B < B') :
    X A B (node A B') = X A B' (node A B) := by
  by_contra hne
  exact h (prod_eq_zero (mem_univ A) (prod_eq_zero (mem_univ B)
    (prod_eq_zero (mem_univ B') (ite_eq_left ⟨hB, hne⟩))))

theorem vert_factor {X : Copies g} (h : vertTest X ≠ 0) {A A' B : Fin g} (hA : A < A') :
    X A B (node A' B) = X A' B (node A B) := by
  by_contra hne
  exact h (prod_eq_zero (mem_univ ⟨(A, A'), hA⟩) (prod_eq_zero (mem_univ B) (ite_eq_right hne)))

theorem diag_factor {X : Copies g} (h : diagTest X ≠ 0) (r : Rect g) : crossing
    (rectViews X r) := by
  by_contra hc
  exact h (prod_eq_zero (mem_univ r) (ite_eq_right hc))

theorem consistent_lt {X : Copies g} (hv : vertTest X ≠ 0)
    (hd : diagTest X ≠ 0) {A A' : Fin g} (hA : A < A') (B B' : Fin g) :
    X A B (node A' B') = X A' B' (node A B) := by
  rcases lt_trichotomy B B' with hB | rfl | hB
  · exact ((crossing_views _ _ _ _).mp (diag_factor hd ⟨((A, A'), (B, B')), hA, hB⟩)).1
  · exact vert_factor hv hA
  · exact ((crossing_views _ _ _ _).mp (diag_factor hd ⟨((A, A'), (B', B)), hA, hB⟩)).2

theorem consistent {X : Copies g} (hh : horTest X ≠ 0) (hv : vertTest X ≠ 0)
    (hd : diagTest X ≠ 0) {A B A' B' : Fin g} (hne : node A B ≠ node A' B') :
    X A B (node A' B') = X A' B' (node A B) := by
  rcases lt_trichotomy A A' with hA | rfl | hA
  · exact consistent_lt hv hd hA B B'
  · rcases lt_trichotomy B B' with hB | rfl | hB
    · exact hor_factor hh hB
    · exact absurd rfl hne
    · exact (hor_factor hh hB).symm
  · exact (consistent_lt hv hd hA B' B).symm

theorem value_eq_copies (a : Fin (g * g) → Fin (g * g) → ℕ)
    (T : Fin (g * g) → (Fin (g * g) → Label) → ℤ) :
    (⟨g * g, a, T⟩ : Clique).value =
      ∑ X ∈ copiesX a, tProd T X * horTest X * vertTest X * diagTest X := by
  change ∑ θ ∈ Fintype.piFinset (fun p : Pairs (g * g) => labelsEq (a p.1.1 p.1.2)),
    ∏ v, T v (labelAt θ v) = _
  refine Finset.sum_bij_ne_zero (fun θ _ _ => fun A B u => labelAt θ (node A B) u) ?_ ?_ ?_ ?_
  · intro θ hθ _
    rw [mem_copiesX]
    intro A B u
    split_ifs with hu
    · subst hu; rw [labelAt_self]; exact Finset.mem_singleton_self _
    · rw [mem_labelsEq]
      rcases lt_or_gt_of_ne hu with h | h
      · rw [labelAt_of_lt θ h, budget_comm, budget_of_lt a h]
        exact mem_labelsEq.mp (Fintype.mem_piFinset.mp hθ ⟨(u, node A B), h⟩)
      · rw [labelAt_of_gt θ h, budget_of_lt a h]
        exact mem_labelsEq.mp (Fintype.mem_piFinset.mp hθ ⟨(node A B, u), h⟩)
  · intro θ₁ _ _ θ₂ _ _ h
    funext p
    have := congrFun (congrFun (congrFun h (rowOf p.1.2)) (colOf p.1.2)) p.1.1
    simp only [node_rowOf_colOf] at this
    rwa [labelAt_of_lt θ₁ p.2, labelAt_of_lt θ₂ p.2] at this
  · intro X hX hne
    have hh : horTest X ≠ 0 := by intro h0; apply hne; rw [h0]; ring
    have hv : vertTest X ≠ 0 := by intro h0; apply hne; rw [h0]; ring
    have hd : diagTest X ≠ 0 := by intro h0; apply hne; rw [h0]; ring
    have ht : tProd T X ≠ 0 := by intro h0; apply hne; rw [h0]; ring
    set θ : Pairs (g * g) → Label := fun p => X (rowOf p.1.2) (colOf p.1.2) p.1.1 with hθ
    have heq : (fun A B u => labelAt θ (node A B) u) = X := by
      funext A B u
      rcases lt_trichotomy u (node A B) with h | rfl | h
      · rw [labelAt_of_lt θ h, hθ]; simp
      · rw [labelAt_self, copies_self hX]
      · rw [labelAt_of_gt θ h, hθ]
        have := consistent hh hv hd (A := rowOf u) (B := colOf u) (A' := A) (B' := B)
          (by rw [node_rowOf_colOf]; exact h.ne')
        rw [node_rowOf_colOf] at this
        exact this
    refine ⟨θ, ?_, ?_, heq⟩
    · refine Fintype.mem_piFinset.mpr fun p => mem_labelsEq.mpr ?_
      have hp : p.1.1 ≠ node (rowOf p.1.2) (colOf p.1.2) := by
        rw [node_rowOf_colOf]; exact p.2.ne
      rw [hθ]
      simp only
      rw [copies_wt hX hp, node_rowOf_colOf, budget_comm, budget_of_lt a p.2]
    · rw [prod_nodes]
      have : ∀ A B, T (node A B) (labelAt θ (node A B)) = T (node A B) (X A B) := by
        intro A B; rw [← heq]
      simp only [this]
      exact ht
  · intro θ _ _
    have hcomm : ∀ A B A' B', labelAt θ (node A B) (node A' B') = labelAt θ
        (node A' B') (node A B) :=
      fun A B A' B' => labelAt_comm θ _ _
    have h1 : horTest (fun A B u => labelAt θ (node A B) u) = 1 :=
      prod_eq_one fun A _ => prod_eq_one fun B _ => prod_eq_one fun B' _ =>
        ite_eq_right (fun h => h.2 (hcomm _ _ _ _))
    have h2 : vertTest (fun A B u => labelAt θ (node A B) u) = 1 :=
      prod_eq_one fun p _ => prod_eq_one fun B _ => ite_eq_left (hcomm _ _ _ _)
    have h3 : diagTest (fun A B u => labelAt θ (node A B) u) = 1 :=
      prod_eq_one fun r _ => ite_eq_left ((crossing_views _ _ _ _).mpr
        ⟨by rw [swapLabel_swapLabel]; exact hcomm _ _ _ _,
            by rw [swapLabel_swapLabel]; exact hcomm _ _ _ _⟩)
    rw [h1, h2, h3, tProd, prod_nodes]
    ring

/-! ### Step 2: the crossings as sums of pieces -/

theorem crossing_eq_sum {a : Fin (g * g) → Fin (g * g) → ℕ} {X : Copies g} (hX : X ∈ copiesX a)
    (r : Rect g) :
    (if crossing (rectViews X r) then (1 : ℤ) else 0) =
      ∑ k ∈ gradeSet a r, (piece (rectViews X r)).coeff k := by
  obtain ⟨hx, hv, hy, hu⟩ := rectViews_wt hX r
  rw [← piece_eval_one _ (hx.trans hv.symm)]
  refine eval_one_eq_sum _ _ fun k hk => ?_
  obtain ⟨h1, h2⟩ := piece_grade _ k hk
  have ht : (totalWt (rectViews X r) : ℤ) = 2 * diagWt a r := by
    simp only [totalWt, hx, hv, hy, hu, diagWt]; push_cast; ring
  rw [ht] at h1 h2
  simp only [gradeSet, Finset.mem_filter, Finset.mem_Icc]
  refine ⟨⟨by linarith [neg_abs_le k], by linarith [le_abs_self k]⟩, Int.even_iff.mpr ?_⟩
  rw [h1]; omega

theorem value_eq_sum_Zk (a : Fin (g * g) → Fin (g * g) → ℕ)
    (T : Fin (g * g) → (Fin (g * g) → Label) → ℤ) :
    (⟨g * g, a, T⟩ : Clique).value = ∑ k ∈ grades a, Zk a T k := by
  rw [value_eq_copies]
  unfold Zk
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun X hX => ?_
  rw [← Finset.mul_sum, diagTest, Finset.prod_congr rfl (fun r _ => crossing_eq_sum hX r),
    Finset.prod_univ_sum]
  rfl

theorem pairRank_eq (B B' : Fin g) : pairRank g B B' = pairStart g B.val + (B'.val - B.val - 1) :=
  rfl

theorem pairRank_lt {B B' : Fin g} (h : B < B') : pairRank g B B' < pairStart g (B.val + 1) := by
  rw [pairRank_eq, pairStart_succ]
  have := B'.isLt; have : B.val < B'.val := h
  omega

theorem pairRank_lt_choose {B B' : Fin g} (h : B < B') : pairRank g B B' < g.choose 2 := by
  refine (pairRank_lt h).trans_le ?_
  rw [← pairStart_self]
  exact pairStart_mono g (by have := B.isLt; omega)

theorem pairRank_inj {B₁ B₁' B₂ B₂' : Fin g} (h₁ : B₁ < B₁') (h₂ : B₂ < B₂')
    (h : pairRank g B₁ B₁' = pairRank g B₂ B₂') : B₁ = B₂ ∧ B₁' = B₂' := by
  have key : ∀ {C₁ C₁' C₂ C₂' : Fin g}, C₁ < C₁' → C₁ < C₂ →
      pairRank g C₁ C₁' < pairRank g C₂ C₂' := by
    intro C₁ C₁' C₂ C₂' hc hlt
    refine (pairRank_lt hc).trans_le ?_
    rw [pairRank_eq]
    exact (pairStart_mono g (Nat.succ_le_of_lt hlt)).trans (Nat.le_add_right _ _)
  rcases lt_trichotomy B₁ B₂ with hb | hb | hb
  · exact absurd h (key h₁ hb).ne
  · subst hb
    refine ⟨rfl, ?_⟩
    rw [pairRank_eq, pairRank_eq] at h
    have : B₁.val < B₁'.val := h₁; have : B₁.val < B₂'.val := h₂
    exact Fin.ext (by omega)
  · exact absurd h (key h₂ hb).ne'

/-! ### The streams between two rows -/

/-- The stream of a vertical pair (`inl B`) or of a rectangle (`inr (B, B')`). -/
def streamOf (g : ℕ) : Fin g ⊕ Pairs g → ℕ
  | .inl B => vStream B
  | .inr q => rStream g q.1.1 q.1.2

theorem streamOf_injective (g : ℕ) : Function.Injective (streamOf g) := by
  rintro (B₁ | q₁) (B₂ | q₂) h <;> simp only [streamOf, vStream, rStream] at h
  · exact congrArg _ (Fin.ext (by omega))
  · have := B₁.isLt; omega
  · have := B₂.isLt; omega
  · obtain ⟨h1, h2⟩ := pairRank_inj q₁.2 q₂.2 (by omega)
    exact congrArg _ (Subtype.ext (Prod.ext h1 h2))

theorem streamOf_mem (g : ℕ) (i : Fin g ⊕ Pairs g) : streamOf g i ∈ Ioo 0 (packL g) := by
  rw [Finset.mem_Ioo]
  rcases i with B | q
  · simp only [streamOf, vStream, packL]; have := B.isLt; omega
  · simp only [streamOf, rStream, packL]
    have := pairRank_lt_choose q.2; omega

theorem image_streamOf (g : ℕ) : univ.image (streamOf g) = Ioo 0 (packL g) := by
  refine Finset.eq_of_subset_of_card_le (fun s hs => ?_) ?_
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs
    exact streamOf_mem g i
  · rw [Finset.card_image_of_injective _ (streamOf_injective g), Finset.card_univ,
      Fintype.card_sum, Fintype.card_fin, card_pairs, Nat.card_Ioo, packL]
    omega


/-! ### Step 3: the row merge -/

section Row

variable (a : Fin (g * g) → Fin (g * g) → ℕ) (T : Fin (g * g) → (Fin (g * g) → Label) → ℤ)

/-- The body of the table of row `A` (eq:table), at the settings `ξ`. -/
noncomputable def rowF (ι : Rect g → ℤ × ℤ) (A : Fin g) (Θ : Fin g → Label)
    (ξ : Fin g → Fin (g * g) → Label) : ℤ :=
  (∏ B, T (node A B) (ξ B)) *
    (∏ B, ∏ B', if B < B' ∧ ξ B (node A B') ≠ ξ B' (node A B) then 0 else 1) *
    (∏ A', ∏ B, if A' ≠ A ∧ ξ B (node A' B) ≠ unpack (packL g) (Θ A') (vStream B) then 0 else 1) *
    ∏ r : Rect g, rowPsi a ι A Θ ξ r

theorem rowTable_eq (ι : Rect g → ℤ × ℤ) (A : Fin g) (Θ : Fin g → Label) :
    rowTable a T ι A Θ = ∑ ξ ∈ rowSettings a A,
      if (∀ A', A' ≠ A → validLabel (packL g) (Θ A')) then rowF a T ι A Θ ξ else 0 := by
  by_cases h : ∀ A', A' ≠ A → validLabel (packL g) (Θ A')
  · rw [rowTable, ite_eq_left h]; exact Finset.sum_congr rfl fun _ _ => (ite_eq_left h).symm
  · rw [rowTable, ite_eq_right h]; exact (Finset.sum_eq_zero fun _ _ => ite_eq_right h).symm

omit a T in
theorem allValid_iff (Θ : Pairs g → Label) :
    (∀ A A', A' ≠ A → validLabel (packL g) (labelAt Θ A A')) ↔ ∀ p, validLabel (packL g) (Θ p) := by
  constructor
  · intro h p
    have := h p.1.2 p.1.1 (ne_of_lt p.2)
    rwa [labelAt_of_lt Θ p.2] at this
  · intro h A A' hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · rw [labelAt_of_lt Θ hlt]; exact h _
    · rw [labelAt_of_gt Θ hlt]; exact h _

/-- The labelings of the row clique. -/
def rowLabels (k : Rect g → ℤ) : Finset (Pairs g → Label) :=
  Fintype.piFinset fun p => labelsEq (rowBudget a k p.1.1 p.1.2)

theorem rowChild_value (ι : Rect g → ℤ × ℤ) :
    (rowChild g a T ι).value = ∑ Θ ∈ rowLabels a (fun r => (ι r).1), ∑ X ∈ copiesX a,
      if (∀ p, validLabel (packL g) (Θ p)) then ∏ A, rowF a T ι A (labelAt Θ A) (X A) else 0 := by
  change ∑ Θ ∈ rowLabels a (fun r => (ι r).1), ∏ A : Fin g, rowTable a T ι A (labelAt Θ A) = _
  refine Finset.sum_congr rfl fun Θ _ => ?_
  rw [Finset.prod_congr rfl fun A _ => rowTable_eq a T ι A (labelAt Θ A), Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun X _ => ?_
  rw [Fintype.prod_ite_zero]
  by_cases hv : ∀ p, validLabel (packL g) (Θ p)
  · rw [ite_eq_left ((allValid_iff Θ).mpr hv), ite_eq_left hv]
  · rw [ite_eq_right (fun h => hv ((allValid_iff Θ).mp h)), ite_eq_right hv]

/-- The pair of rows of a rectangle. -/
def rowsOf (r : Rect g) : Pairs g := ⟨r.1.1, r.2.1⟩

/-- The product of the two rectangle factors `Ψ_R` of the rows of `R`, for the message `m`. -/
noncomputable def psiR (X : Copies g) (r : Rect g) (m : Label) (k c : ℤ) : ℤ :=
  if (labelWt m : ℤ) ≤ (diagWt a r : ℤ) + k / 2 then
    (nUp (rectViews X r .x) (rectViews X r .y) m).coeff (k - c) *
      (nDown (rectViews X r .u) (rectViews X r .v) m).coeff c
  else 0

omit T in
theorem prod_rowPsi (ι : Rect g → ℤ × ℤ) (Θ : Pairs g → Label) (X : Copies g) (r : Rect g) :
    ∏ A, rowPsi a ι A (labelAt Θ A) (X A) r =
      psiR a X r (unpack (packL g) (Θ (rowsOf r)) (rStream g r.1.2.1 r.1.2.2)) (ι r).1 (ι r).2 := by
  have hA : r.1.1.1 < r.1.1.2 := r.2.1
  rw [Finset.prod_eq_mul r.1.1.1 r.1.1.2 hA.ne (fun c _ hc => ?_)
    (fun h => absurd (mem_univ _) h) (fun h => absurd (mem_univ _) h)]
  · simp only [rowPsi, ite_true, hA.ne', ite_false]
    rw [labelAt_of_gt Θ hA, labelAt_of_lt Θ hA]
    simp only [ite_zero_mul_ite_zero, and_self]
    rfl
  · simp only [rowPsi, hc.1, hc.2, ite_false]

/-- The vertical tests of all rows against the unpacked labels. -/
def vRow (X : Copies g) (Θ : Pairs g → Label) : ℤ :=
  ∏ A, ∏ A', ∏ B,
    if A' ≠ A ∧ X A B (node A' B) ≠ unpack (packL g) (labelAt Θ A A') (vStream B) then 0 else 1

/-- The message of a rectangle unpacked from the labels of the row clique. -/
def msg (Θ : Pairs g → Label) (r : Rect g) : Label :=
  unpack (packL g) (Θ (rowsOf r)) (rStream g r.1.2.1 r.1.2.2)

theorem prod_rowF (ι : Rect g → ℤ × ℤ) (Θ : Pairs g → Label) (X : Copies g) :
    ∏ A, rowF a T ι A (labelAt Θ A) (X A) =
      tProd T X * horTest X * vRow X Θ * ∏ r, psiR a X r (msg Θ r) (ι r).1 (ι r).2 := by
  unfold rowF
  simp only [Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_comm]
  exact Finset.prod_congr rfl fun r _ => prod_rowPsi a ι Θ X r

/-- The sum over the splits of a rectangle. -/
noncomputable def Q (X : Copies g) (k : Rect g → ℤ) (r : Rect g) (m : Label) : ℤ :=
  ∑ c ∈ Icc (-(3 * (diagWt a r : ℤ))) (3 * diagWt a r), psiR a X r m (k r) c

/-- The weight cap of the message of a rectangle. -/
def cap (k : Rect g → ℤ) (r : Rect g) : ℕ := ((diagWt a r : ℤ) + k r / 2).toNat

theorem Q_support (X : Copies g) (k : Rect g → ℤ) (r : Rect g) (m : Label) (h : Q a X k r m ≠ 0) :
    m ∈ labelsLE (cap a k r) := by
  rw [mem_labelsLE]
  by_contra hm
  apply h
  refine Finset.sum_eq_zero fun c _ => ite_eq_right ?_
  intro hle
  apply hm
  unfold cap
  omega

theorem Q_rowCut {X : Copies g} (hX : X ∈ copiesX a) {k : Rect g → ℤ} (r : Rect g)
    (hk : Even (k r) ∧ |k r| ≤ 2 * diagWt a r) :
    ∑ m ∈ labelsLE (cap a k r), Q a X k r m = (piece (rectViews X r)).coeff (k r) := by
  obtain ⟨hx, hv, hy, hu⟩ := rectViews_wt hX r
  have hH : (diagWt a r : ℤ) = (a (node r.1.1.1 r.1.2.1) (node r.1.1.2 r.1.2.2) : ℤ) +
      a (node r.1.1.1 r.1.2.2) (node r.1.1.2 r.1.2.1) := by
    unfold diagWt; push_cast; ring
  have hk2 := hk.2
  rw [hH] at hk2
  have hk3 := abs_le.mp hk2
  rw [rowCut _ _ _ hx hv hy hu (k r)]
  unfold cap
  rw [hH]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hwm := mem_labelsLE.mp hm
  unfold Q psiR
  rw [hH]
  have hle : (labelWt m : ℤ) ≤ (a (node r.1.1.1 r.1.2.1) (node r.1.1.2 r.1.2.2) : ℤ) +
      a (node r.1.1.1 r.1.2.2) (node r.1.1.2 r.1.2.1) + k r / 2 := by omega
  rw [Finset.sum_congr rfl fun c _ => ite_eq_left hle]
  symm
  apply Finset.sum_subset
  · intro c hc
    rw [Finset.mem_Icc] at hc ⊢
    constructor <;> omega
  · intro c _ hc'
    rw [Finset.mem_Icc] at hc'
    by_cases h1 : c < (labelWt m : ℤ) -
        ((a (node r.1.1.1 r.1.2.1) (node r.1.1.2 r.1.2.2) : ℤ) +
          a (node r.1.1.1 r.1.2.2) (node r.1.1.2 r.1.2.1))
    · have : (nDown (rectViews X r .u) (rectViews X r .v) m).coeff c = 0 := by
        by_contra h0
        have := nDown_lower _ _ _ _ h0
        rw [hu, hv] at this
        omega
      rw [this, mul_zero]
    · have : (nUp (rectViews X r .x) (rectViews X r .y) m).coeff (k r - c) = 0 := by
        by_contra h0
        have := nUp_lower _ _ _ _ h0
        rw [hx, hy] at this
        omega
      rw [this, zero_mul]

omit a T in
theorem vRow_eq (X : Copies g) (Θ : Pairs g → Label) :
    vRow X Θ = ∏ p : Pairs g, ∏ B,
      (if X p.1.1 B (node p.1.2 B) = unpack (packL g) (Θ p) (vStream B) then 1 else 0) *
      (if X p.1.2 B (node p.1.1 B) = unpack (packL g) (Θ p) (vStream B) then 1 else 0) := by
  have h : ∀ A A', (∏ B, if A' ≠ A ∧ X A B (node A' B) ≠
        unpack (packL g) (labelAt Θ A A') (vStream B) then (0 : ℤ) else 1) =
      if A' ≠ A then ∏ B, (if X A B (node A' B) = unpack (packL g) (labelAt Θ A A') (vStream B)
        then 1 else 0) else 1 := by
    intro A A'
    by_cases hA : A' ≠ A
    · rw [ite_eq_left hA]
      refine Finset.prod_congr rfl fun B _ => ?_
      by_cases he : X A B (node A' B) = unpack (packL g) (labelAt Θ A A') (vStream B) <;>
        simp [hA, he]
    · rw [ite_eq_right hA]
      exact Finset.prod_eq_one fun B _ => ite_eq_right fun h => hA h.1
  unfold vRow
  simp only [h]
  rw [prod_offDiag]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [labelAt_of_gt Θ p.2, labelAt_of_lt Θ p.2, ← Finset.prod_mul_distrib]

/-- The factor of the pair of rows `p` at its packed label `l`. -/
noncomputable def G (X : Copies g) (k : Rect g → ℤ) (p : Pairs g) (l : Label) : ℤ :=
  if validLabel (packL g) l then
    (∏ B, (if X p.1.1 B (node p.1.2 B) = unpack (packL g) l (vStream B) then 1 else 0) *
      (if X p.1.2 B (node p.1.1 B) = unpack (packL g) l (vStream B) then 1 else 0)) *
    ∏ q, Q a X k (mkRect p q) (unpack (packL g) l (rStream g q.1.1 q.1.2))
  else 0

theorem split_by_pairs (X : Copies g) (k : Rect g → ℤ) (Θ : Pairs g → Label) :
    (if ∀ p, validLabel (packL g) (Θ p) then vRow X Θ * ∏ r, Q a X k r (msg Θ r) else 0) =
      ∏ p, G a X k p (Θ p) := by
  unfold G
  rw [Fintype.prod_ite_zero, vRow_eq, prod_rect, ← Finset.prod_mul_distrib]
  rfl

theorem sum_rect {M : Type*} [AddCommMonoid M] (f : Rect g → M) :
    ∑ r, f r = ∑ p, ∑ q, f (mkRect p q) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (rectEquiv g) (fun pq => f (mkRect pq.1 pq.2)) f fun _ => rfl).symm

theorem pair_sum (hg : 1 ≤ g) {X : Copies g} (hX : X ∈ copiesX a) {k : Rect g → ℤ}
    (hk : k ∈ grades a) (p : Pairs g) :
    ∑ l ∈ labelsEq (rowBudget a k p.1.1 p.1.2), G a X k p l =
      (∏ B, if X p.1.1 B (node p.1.2 B) = X p.1.2 B (node p.1.1 B) then 1 else 0) *
        ∏ q, (piece (rectViews X (mkRect p q))).coeff (k (mkRect p q)) := by
  have hL : 2 ≤ packL g := by have := hg; unfold packL; omega
  have hlt : ∀ B, node p.1.1 B < node p.1.2 B := fun B => node_lt_node_iff.mpr (Or.inl p.2)
  let S : Fin g ⊕ Pairs g → Finset Label :=
    Sum.elim (fun B => {X p.1.1 B (node p.1.2 B)}) (fun q => labelsLE (cap a k (mkRect p q)))
  let w : Fin g ⊕ Pairs g → ℕ :=
    Sum.elim (fun B => a (node p.1.1 B) (node p.1.2 B)) (fun q => cap a k (mkRect p q))
  let F : Fin g ⊕ Pairs g → Label → ℤ :=
    Sum.elim (fun B m => (if X p.1.1 B (node p.1.2 B) = m then 1 else 0) *
      (if X p.1.2 B (node p.1.1 B) = m then 1 else 0)) (fun q m => Q a X k (mkRect p q) m)
  have hw : ∀ i, ∀ m ∈ S i, labelWt m ≤ w i := by
    rintro (B | q) m hm
    · simp only [S, w, Sum.elim_inl, Finset.mem_singleton] at hm ⊢
      rw [hm, copies_wt hX (hlt B).ne', budget_of_lt a (hlt B)]
    · exact mem_labelsLE.mp hm
  have hF : ∀ i m, F i m ≠ 0 → m ∈ S i := by
    rintro (B | q) m hm
    · simp only [S, F, Sum.elim_inl] at hm ⊢
      rw [Finset.mem_singleton]
      by_contra h
      apply hm
      rw [ite_eq_right (fun e => h e.symm), zero_mul]
    · exact Q_support a X k _ m hm
  have hβ : rowBudget a k p.1.1 p.1.2 = packL g * ∑ i, w i := by
    rw [Fintype.sum_sum_type]
    simp only [w, Sum.elim_inl, Sum.elim_inr]
    unfold rowBudget
    congr 2
    rw [sum_rect, Finset.sum_eq_single p]
    · simp [mkRect, cap]
    · intro p' _ hp'
      refine Finset.sum_eq_zero fun q _ => ite_eq_right ?_
      rintro ⟨h1, h2⟩
      exact hp' (Subtype.ext (Prod.ext h1 h2))
    · intro h; exact absurd (mem_univ p) h
  have key := sum_valid_unpack hL (streamOf g) (streamOf_injective g) (image_streamOf g) S w hw F hF
  rw [hβ]
  convert key using 1
  · refine Finset.sum_congr rfl fun l _ => ?_
    unfold G
    rw [Fintype.prod_sum_type]
    rfl
  · rw [Fintype.prod_sum_type]
    congr 1
    · refine Finset.prod_congr rfl fun B _ => ?_
      simp only [S, F, Sum.elim_inl, Finset.sum_singleton]
      by_cases h : X p.1.1 B (node p.1.2 B) = X p.1.2 B (node p.1.1 B)
      · simp [h]
      · have h' : ¬ X p.1.2 B (node p.1.1 B) = X p.1.1 B (node p.1.2 B) := fun e => h e.symm
        simp [h, h']
    · exact Finset.prod_congr rfl fun q _ => (Q_rowCut a hX _ (mem_grades.mp hk _)).symm

theorem row_fiber (hg : 1 ≤ g) {k : Rect g → ℤ} (hk : k ∈ grades a) {X : Copies g}
    (hX : X ∈ copiesX a) :
    ∑ Θ ∈ rowLabels a k, ∑ c ∈ splits a, (if ∀ p, validLabel (packL g) (Θ p) then
        ∏ A, rowF a T (fun r => (k r, c r)) A (labelAt Θ A) (X A) else 0) =
      tProd T X * horTest X * vertTest X * ∏ r, (piece (rectViews X r)).coeff (k r) := by
  calc _ = ∑ Θ ∈ rowLabels a k, tProd T X * horTest X * ∏ p, G a X k p (Θ p) := by
        refine Finset.sum_congr rfl fun Θ _ => ?_
        simp only [prod_rowF]
        rw [← split_by_pairs]
        by_cases hv : ∀ p, validLabel (packL g) (Θ p)
        · simp only [ite_eq_left hv]
          unfold Q
          rw [Finset.prod_univ_sum, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun c _ => ?_
          ring
        · simp only [ite_eq_right hv, Finset.sum_const_zero, mul_zero]
    _ = tProd T X * horTest X * ∏ p, ∑ l ∈ labelsEq (rowBudget a k p.1.1 p.1.2), G a X k p l := by
        rw [Finset.prod_univ_sum, Finset.mul_sum]
        rfl
    _ = _ := by
        simp only [pair_sum a hg hX hk]
        rw [Finset.prod_mul_distrib, prod_rect]
        unfold vertTest
        ring

theorem Zk_eq_row (hg : 1 ≤ g) {k : Rect g → ℤ} (hk : k ∈ grades a) :
    Zk a T k = ∑ c ∈ splits a, (rowChild g a T fun r => (k r, c r)).value := by
  have e : ∀ f : (Rect g → ℤ) → (Pairs g → Label) → Copies g → ℤ,
      ∑ c ∈ splits a, ∑ Θ ∈ rowLabels a k, ∑ X ∈ copiesX a, f c Θ X =
        ∑ X ∈ copiesX a, ∑ Θ ∈ rowLabels a k, ∑ c ∈ splits a, f c Θ X := by
    intro f
    calc _ = ∑ Θ ∈ rowLabels a k, ∑ c ∈ splits a, ∑ X ∈ copiesX a, f c Θ X := Finset.sum_comm
      _ = ∑ Θ ∈ rowLabels a k, ∑ X ∈ copiesX a, ∑ c ∈ splits a, f c Θ X :=
        Finset.sum_congr rfl fun Θ _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [Finset.sum_congr rfl fun c _ => rowChild_value a T _, e]
  unfold Zk
  exact Finset.sum_congr rfl fun X hX => (row_fiber a T hg hk hX).symm

end Row

/-! ### Step 4: transposition -/

section Transpose

/-- The copies of the transposed clique: `node A B` of the transposed clique holds the copies of
`node B A`, with the labels of pairs whose order flips reversed. -/
def trX (X : Copies g) : Copies g := fun A B u =>
  if (node A B < u ↔ node B A < trNode u) then X B A (trNode u) else swapLabel (X B A (trNode u))

theorem trX_trX (X : Copies g) : trX (trX X) = X := by
  funext A B u
  simp only [trX, trNode_trNode]
  by_cases h : node A B < u ↔ node B A < trNode u
  · have h' : node B A < trNode u ↔ node A B < u := h.symm
    rw [ite_eq_left h, ite_eq_left h']
  · have h' : ¬ (node B A < trNode u ↔ node A B < u) := fun e => h e.symm
    rw [ite_eq_right h, ite_eq_right h', swapLabel_swapLabel]

theorem trX_mem {a a' : Fin (g * g) → Fin (g * g) → ℕ}
    (ha : ∀ w u, budget a' w u = budget a (trNode w) (trNode u)) {X : Copies g}
    (hX : X ∈ copiesX a) : trX X ∈ copiesX a' := by
  rw [mem_copiesX]
  intro A B u
  by_cases hu : u = node A B
  · subst hu
    rw [ite_eq_left rfl]
    simp only [trX, trNode_node, copies_self hX]
    split_ifs <;> exact Finset.mem_singleton_self _
  · rw [ite_eq_right hu, mem_labelsEq, ha, trNode_node]
    have htu : trNode u ≠ node B A := fun e => hu (by rw [← trNode_trNode u, e, trNode_node])
    have hw := copies_wt hX htu
    simp only [trX]
    split_ifs
    · exact hw
    · rw [labelWt_swap]; exact hw

theorem tProd_trX (T : Fin (g * g) → (Fin (g * g) → Label) → ℤ) (X : Copies g) :
    tProd (trTable T) (trX X) = tProd T X := by
  unfold tProd
  conv_lhs => rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun B _ => Finset.prod_congr rfl fun A _ => ?_
  simp only [trTable, trX, trNode_node, trNode_trNode]
  congr 1
  funext u
  by_cases h : node A B < trNode u ↔ node B A < u
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h, swapLabel_swapLabel]

theorem horTest_trX (X : Copies g) : horTest (trX X) = vertTest X := by
  have e : ∀ A B B', trX X A B (node A B') = X B A (node B' A) := by
    intro A B B'
    simp only [trX, trNode_node]
    exact ite_eq_left (by simp [node_lt_node_iff])
  unfold horTest
  simp only [e]
  exact prod_hor_form (fun A B B' => X B A (node B' A) = X B' A (node B A))

theorem vertTest_trX (X : Copies g) : vertTest (trX X) = horTest X := by
  have e1 : ∀ (p : Pairs g) B, trX X p.1.1 B (node p.1.2 B) = X B p.1.1 (node B p.1.2) := by
    intro p B
    simp only [trX, trNode_node]
    exact ite_eq_left (by simp [node_lt_node_iff, p.2])
  have e2 : ∀ (p : Pairs g) B, trX X p.1.2 B (node p.1.1 B) = X B p.1.2 (node B p.1.1) := by
    intro p B
    simp only [trX, trNode_node]
    exact ite_eq_left (by simp [node_lt_node_iff, p.2.ne', not_lt_of_gt p.2])
  unfold vertTest
  simp only [e1, e2]
  unfold horTest
  exact (prod_hor_form (fun A B B' => X A B (node A B') = X A B' (node A B))).symm

theorem trRect_trRect (r : Rect g) : trRect (trRect r) = r := rfl

theorem rectViews_trX (X : Copies g) (r : Rect g) :
    rectViews (trX X) r = transposeView (rectViews X (trRect r)) := by
  have hA : r.1.1.1 < r.1.1.2 := r.2.1
  have hB : r.1.2.1 < r.1.2.2 := r.2.2
  funext c
  cases c <;>
    simp [rectViews, views, transposeView, swapYU, trRect, trX, node_lt_node_iff, hA, hB, hA.ne,
      hB.ne, hA.ne', hB.ne', not_lt_of_gt hA, not_lt_of_gt hB]

theorem diagWt_tr (a : Fin (g * g) → Fin (g * g) → ℕ) (r : Rect g) :
    diagWt (trBudget a) r = diagWt a (trRect r) := by
  have hB : r.1.2.1 < r.1.2.2 := r.2.2
  unfold diagWt trBudget
  simp only [trNode_node, trRect]
  rw [budget_of_lt a (node_lt_node_iff.mpr (Or.inl hB)), budget_comm,
    budget_of_lt a (node_lt_node_iff.mpr (Or.inl hB))]

theorem Zk_transpose (a : Fin (g * g) → Fin (g * g) → ℕ)
    (T : Fin (g * g) → (Fin (g * g) → Label) → ℤ) (k : Rect g → ℤ) :
    Zk a T k = Zk (trBudget a) (trTable T) (fun r => -k (trRect r)) := by
  unfold Zk
  refine Finset.sum_nbij' trX trX (fun X hX => trX_mem (fun w u => budget_trBudget a w u) hX)
    (fun X hX => trX_mem (fun w u => by rw [budget_trBudget, trNode_trNode, trNode_trNode]) hX)
    (fun X _ => trX_trX X) (fun X _ => trX_trX X) (fun X _ => ?_)
  rw [tProd_trX, horTest_trX, vertTest_trX]
  have : ∏ r, (piece (rectViews (trX X) r)).coeff (-k (trRect r)) =
      ∏ r, (piece (rectViews X r)).coeff (k r) := by
    simp only [rectViews_trX, piece_transpose, LaurentPolynomial.invert_apply, neg_neg]
    exact Fintype.prod_equiv ⟨trRect, trRect, trRect_trRect, trRect_trRect⟩ _ _ fun r => rfl
  rw [this]
  ring

end Transpose

end MergeProof

open MergeProof

/-- **Lemma 6.2.** For every rule `o` choosing, from the grades of a choice, the row orientation
(`true`) or the column orientation (`false`),
`Z(𝒞) = ∑_ι Z(𝒞^{o(ι)}_ι)`. -/
theorem merge (hg : 1 ≤ g) (a : Fin (g * g) → Fin (g * g) → ℕ)
    (T : Fin (g * g) → (Fin (g * g) → Label) → ℤ) (o : (Rect g → ℤ) → Bool) :
    (⟨g * g, a, T⟩ : Clique).value =
      ∑ ι ∈ choices a, (if o (fun r => (ι r).1) then rowChild g a T ι else colChild g a
          T ι).value := by
  rw [value_eq_sum_Zk]
  unfold choices
  rw [sum_piFinset_prod]
  refine Finset.sum_congr rfl fun k hk => ?_
  change Zk a T k = ∑ c ∈ splits a, (if o k then rowChild g a T (fun r => (k r, c r))
    else colChild g a T (fun r => (k r, c r))).value
  by_cases h : o k
  · simp only [h, ite_true]
    exact Zk_eq_row a T hg hk
  · simp only [h]
    have hk' : (fun r => -k (trRect r)) ∈ grades (trBudget a) := by
      refine mem_grades.mpr fun r => ⟨(mem_grades.mp hk (trRect r)).1.neg, ?_⟩
      rw [abs_neg, diagWt_tr]
      exact (mem_grades.mp hk _).2
    rw [Zk_transpose, Zk_eq_row (trBudget a) (trTable T) hg hk']
    refine Finset.sum_nbij' (fun c r => c (trRect r)) (fun c r => c (trRect r)) ?_ ?_
      (fun c _ => rfl) (fun c _ => rfl) (fun c _ => rfl)
    · intro c hc
      simp only [splits, Fintype.mem_piFinset] at hc ⊢
      intro r
      have := hc (trRect r)
      rwa [diagWt_tr, trRect_trRect] at this
    · intro c hc
      simp only [splits, Fintype.mem_piFinset] at hc ⊢
      intro r
      rw [diagWt_tr]
      exact hc (trRect r)

end Cslib.Complexity.NtimeDspace.Cube
