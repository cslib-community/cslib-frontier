/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.Basic

/-!
# Cliques, their potential, and packing (Definition 4.2, Lemma 6.1, (eq:pack))

* `Clique`: a clique with `q = 2^h` nodes `Fin q` (names of `h` bits, compared numerically,
  which is the lexicographic order), a budget `a u v` for every pair `u < v`, and a
  table `T v` at every node, a function of the labels on the pairs at `v` (`fun u => label of
  {u, v}`; the entry at `u = v` is ignored). A label on a pair `u < v` is stored in its
  canonical orientation: the first multiset holds what `u` sends to `v`.
* `Clique.value`: `Z(C) = ∑_θ ∏_v T_v(θ_v)`, over one label of weight exactly `a_{uv}` on every
  pair.
* `Clique.potential`: `Φ(C) = (q - 1)^2 ∑_{u<v} a_{uv}`.
* `rowBudget`, `colBudget`: the row and column budgets of a choice of grades (§6.1), and
  `energy_le` (Lemma 6.1): the potentials of the two candidate children add up to at most `Φ(C)`.
* `pack`, `unpack`, `validLabel` and `pack_bijective` ((eq:pack)): `L - 1` streams of labels,
  packed by residues modulo `L` into one label of exact weight, with requests of weight `1`
  (type `0`) as padding in the first direction. In types, a request of type `i` in stream
  `s ∈ {1, …, L - 1}` becomes a request of type `L·i + s`, as in the paper's (eq:pack), and its
  weight `L·i + s + 1` is at most `L(i + 1)`.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cube

open Finset

/-! ### Pairs and cliques -/

/-- The unordered pairs of `Fin q`, as ordered pairs `u < v`. -/
abbrev Pairs (q : ℕ) := {p : Fin q × Fin q // p.1 < p.2}

/-- **A clique** (Definition 4.2). -/
structure Clique where
  /-- The number of nodes (`q = 2^h` for name length `h`). -/
  q : ℕ
  /-- The budget of the pair `u < v` (only `u < v` is used). -/
  a : Fin q → Fin q → ℕ
  /-- The table of a node, at the labels on its pairs (canonical orientation). -/
  T : Fin q → (Fin q → Label) → ℤ

namespace Clique

variable (C : Clique)

/-- The labelings: one label of weight exactly the budget on every pair. -/
def labelings : Finset (Pairs C.q → Label) :=
  Fintype.piFinset fun p => labelsEq (C.a p.1.1 p.1.2)

/-- The label of the pair `{u, v}` under a labeling, seen from `v` (canonical orientation; the
empty label at `u = v`). -/
def labelAt {q : ℕ} (θ : Pairs q → Label) (v u : Fin q) : Label :=
  if h : u < v then θ ⟨(u, v), h⟩ else if h' : v < u then θ ⟨(v, u), h'⟩ else (0, 0)

/-- **The value** `Z(C) = ∑_θ ∏_v T_v(θ_v)`. -/
def value : ℤ := ∑ θ ∈ C.labelings, ∏ v, C.T v (labelAt θ v)

/-- **The potential** `Φ(C) = (q - 1)^2 ∑_{u<v} a_{uv}`. -/
def potential : ℕ := (C.q - 1) ^ 2 * ∑ p : Pairs C.q, C.a p.1.1 p.1.2

end Clique

/-! ### Rows, columns and rectangles of a grid -/

section Grid

variable {g : ℕ}

/-- The node of the grid in row `A` and column `B`: the name with first half `A` and second half
`B`. -/
def node (A B : Fin g) : Fin (g * g) :=
  ⟨A.val * g + B.val, by
    have hA := A.isLt; have hB := B.isLt
    calc A.val * g + B.val < A.val * g + g := by omega
      _ = (A.val + 1) * g := by ring
      _ ≤ g * g := Nat.mul_le_mul_right _ hA⟩

/-- A rectangle: rows `A < A'` and columns `B < B'`. -/
abbrev Rect (g : ℕ) := {r : (Fin g × Fin g) × (Fin g × Fin g) // r.1.1 < r.1.2 ∧ r.2.1 < r.2.2}

end Grid

/-! ### The budgets of a choice and the potential (Lemma 6.1) -/

section Budgets

variable {g : ℕ} (a : Fin (g * g) → Fin (g * g) → ℕ)

/-- The diagonal weight `H_R` of a rectangle: the budgets of its two diagonals `{x, v}` and
`{y, u}`. -/
def diagWt (r : Rect g) : ℕ :=
  a (node r.1.1.1 r.1.2.1) (node r.1.1.2 r.1.2.2) + a (node r.1.1.1 r.1.2.2) (node r.1.1.2 r.1.2.1)

/-- `L = 1 + g + C(g, 2)`. -/
def packL (g : ℕ) : ℕ := 1 + g + g.choose 2

/-- **The row budgets** of a choice of grades `k`. -/
def rowBudget (k : Rect g → ℤ) (A A' : Fin g) : ℕ :=
  packL g * ((∑ B : Fin g, a (node A B) (node A' B)) +
    ∑ r : Rect g, if r.1.1.1 = A ∧ r.1.1.2 = A' then ((diagWt a r : ℤ) + k r / 2).toNat else 0)

/-- **The column budgets** of a choice of grades `k`. -/
def colBudget (k : Rect g → ℤ) (B B' : Fin g) : ℕ :=
  packL g * ((∑ A : Fin g, a (node A B) (node A B')) +
    ∑ r : Rect g, if r.1.2.1 = B ∧ r.1.2.2 = B' then ((diagWt a r : ℤ) - k r / 2).toNat else 0)

theorem node_lt_node {A A' : Fin g} (h : A < A') (B B' : Fin g) : node A B < node A' B' := by
  rw [Fin.lt_def] at h ⊢
  simp only [node]
  have hB := B.isLt
  have : (A.val + 1) * g ≤ A'.val * g := Nat.mul_le_mul_right _ h
  nlinarith

theorem node_lt_node_right (A : Fin g) {B B' : Fin g} (h : B < B') : node A B < node A B' := by
  rw [Fin.lt_def] at h ⊢
  simp only [node]; omega

theorem node_inj {A B A' B' : Fin g} : node A B = node A' B' ↔ A = A' ∧ B = B' := by
  refine ⟨fun h => ?_, fun ⟨h1, h2⟩ => h1 ▸ h2 ▸ rfl⟩
  have h' : A.val * g + B.val = A'.val * g + B'.val := congrArg Fin.val h
  have hB := B.isLt; have hB' := B'.isLt
  have hd : (A.val * g + B.val) / g = (A'.val * g + B'.val) / g := by rw [h']
  have hm : (A.val * g + B.val) % g = (A'.val * g + B'.val) % g := by rw [h']
  have hg : 0 < g := by omega
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hg, Nat.add_comm (A'.val * g),
    Nat.add_mul_div_right _ _ hg, Nat.div_eq_of_lt hB, Nat.div_eq_of_lt hB'] at hd
  rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hB,
    Nat.mod_eq_of_lt hB'] at hm
  exact ⟨Fin.ext (by omega), Fin.ext hm⟩

/-- The straight pairs and the diagonals of the rectangles, as pairs of the grid. -/
private def gridPair : (Pairs g × Fin g) ⊕ (Pairs g × Fin g) ⊕ Rect g ⊕ Rect g → Pairs (g * g)
  | .inl (p, B) => ⟨(node p.1.1 B, node p.1.2 B), node_lt_node p.2 _ _⟩
  | .inr (.inl (p, A)) => ⟨(node A p.1.1, node A p.1.2), node_lt_node_right A p.2⟩
  | .inr (.inr (.inl r)) => ⟨(node r.1.1.1 r.1.2.1, node r.1.1.2 r.1.2.2), node_lt_node r.2.1 _ _⟩
  | .inr (.inr (.inr r)) => ⟨(node r.1.1.1 r.1.2.2, node r.1.1.2 r.1.2.1), node_lt_node r.2.1 _ _⟩

private theorem gridPair_injective : Function.Injective (gridPair (g := g)) := by
  rintro (⟨⟨⟨A₁, A₂⟩, h⟩, B⟩ | ⟨⟨⟨B₁, B₂⟩, h⟩, A⟩ | ⟨⟨⟨A₁, A₂⟩, B₁, B₂⟩, h⟩ |
      ⟨⟨⟨A₁, A₂⟩, B₁, B₂⟩, h⟩)
    (⟨⟨⟨C₁, C₂⟩, h'⟩, D⟩ | ⟨⟨⟨D₁, D₂⟩, h'⟩, C⟩ | ⟨⟨⟨C₁, C₂⟩, D₁, D₂⟩, h'⟩ |
      ⟨⟨⟨C₁, C₂⟩, D₁, D₂⟩, h'⟩) hxy <;>
    simp only [gridPair, Subtype.mk.injEq, Prod.mk.injEq, node_inj] at hxy h h' <;>
    simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, Prod.mk.injEq, Subtype.mk.injEq] <;>
    omega

/-- Every vertical pair, horizontal pair and diagonal is a pair of the grid, and no pair is
counted twice. -/
private theorem straight_diag_le :
    (∑ p : Pairs g, ∑ B : Fin g, a (node p.1.1 B) (node p.1.2 B)) +
        (∑ p : Pairs g, ∑ A : Fin g, a (node A p.1.1) (node A p.1.2)) +
        ∑ r : Rect g, diagWt a r ≤ ∑ p : Pairs (g * g), a p.1.1 p.1.2 := by
  classical
  have e : ∑ x, a (gridPair x).1.1 (gridPair x).1.2 =
      (∑ p : Pairs g, ∑ B : Fin g, a (node p.1.1 B) (node p.1.2 B)) +
        (∑ p : Pairs g, ∑ A : Fin g, a (node A p.1.1) (node A p.1.2)) +
        ∑ r : Rect g, diagWt a r := by
    simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, gridPair, diagWt,
      Finset.sum_add_distrib, add_assoc]
  rw [← e]
  calc ∑ x, a (gridPair x).1.1 (gridPair x).1.2
      = ∑ p ∈ Finset.univ.map ⟨gridPair, gridPair_injective⟩, a p.1.1 p.1.2 :=
        by rw [Finset.sum_map]; rfl
    _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

private theorem sum_pairs_rows (f : Rect g → ℕ) :
    ∑ p : Pairs g, ∑ r : Rect g, (if r.1.1.1 = p.1.1 ∧ r.1.1.2 = p.1.2 then f r else 0) =
      ∑ r, f r := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_eq_single ⟨r.1.1, r.2.1⟩ (fun p _ hp => by
    simp only
        [ite_eq_right_iff]; exact fun h => absurd (Subtype.ext (Prod.ext h.1.symm h.2.symm)) hp)
    (by simp)]
  simp

private theorem sum_pairs_cols (f : Rect g → ℕ) :
    ∑ p : Pairs g, ∑ r : Rect g, (if r.1.2.1 = p.1.1 ∧ r.1.2.2 = p.1.2 then f r else 0) =
      ∑ r, f r := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_eq_single ⟨r.1.2, r.2.2⟩ (fun p _ hp => by
    simp only
        [ite_eq_right_iff]; exact fun h => absurd (Subtype.ext (Prod.ext h.1.symm h.2.symm)) hp)
    (by simp)]
  simp

/-- `2L = g^2 + g + 2 ≤ (g+1)^2`, so `(g-1)^2 · 2L ≤ (g^2-1)^2`. -/
private theorem two_packL_le (g : ℕ) : (g - 1) ^ 2 * (2 * packL g) ≤ (g * g - 1) ^ 2 := by
  rcases g with _ | n
  · simp
  have h2 : 2 * (n + 1).choose 2 ≤ (n + 1) * n := by
    rw [Nat.choose_two_right, Nat.add_sub_cancel]; exact Nat.mul_div_le _ 2
  have e : (n + 1) * (n + 1) - 1 = n * (n + 2) := by
    rw [show (n + 1) * (n + 1) = n * (n + 2) + 1 by ring, Nat.add_sub_cancel]
  rw [e, Nat.add_sub_cancel, mul_pow]
  refine Nat.mul_le_mul_left _ ?_
  unfold packL
  nlinarith

/-- **Lemma 6.1.** For every choice of even grades with `|k_R| ≤ 2 H_R`, the potentials of the
row clique and of the column clique (name length `h/2`, `g` nodes) add up to at most the potential
of the clique: `(g-1)^2 (∑ A^row + ∑ A^col) ≤ (q-1)^2 ∑ a`. -/
theorem energy_le (k : Rect g → ℤ) (hk : ∀ r, Even (k r) ∧ |k r| ≤ 2 * diagWt a r) :
    (g - 1) ^ 2 * ((∑ p : Pairs g, rowBudget a k p.1.1 p.1.2) +
        ∑ p : Pairs g, colBudget a k p.1.1 p.1.2) ≤
      (g * g - 1) ^ 2 * ∑ p : Pairs (g * g), a p.1.1 p.1.2 := by
  simp only [rowBudget, colBudget, ← Finset.mul_sum, Finset.sum_add_distrib, sum_pairs_rows,
    sum_pairs_cols]
  have hsplit : ∑ r : Rect g, ((diagWt a r : ℤ) + k r / 2).toNat +
      ∑ r : Rect g, ((diagWt a r : ℤ) - k r / 2).toNat = ∑ r : Rect g, 2 * diagWt a r := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    obtain ⟨⟨y, hy⟩, hb⟩ := hk r
    rw [abs_le, hy] at hb
    rw [hy]
    omega
  have hle := straight_diag_le a
  have hL := two_packL_le g
  set V := ∑ p : Pairs g, ∑ B : Fin g, a (node p.1.1 B) (node p.1.2 B)
  set Hz := ∑ p : Pairs g, ∑ A : Fin g, a (node A p.1.1) (node A p.1.2)
  set S := ∑ p : Pairs (g * g), a p.1.1 p.1.2
  rw [← Finset.mul_sum] at hsplit
  calc (g - 1) ^ 2 * (packL g * (V + ∑ r : Rect g, ((diagWt a r : ℤ) + k r / 2).toNat) +
        packL g * (Hz + ∑ r : Rect g, ((diagWt a r : ℤ) - k r / 2).toNat))
      = (g - 1) ^ 2 * packL g * (V + Hz + (∑ r : Rect g, ((diagWt a r : ℤ) + k r / 2).toNat +
          ∑ r : Rect g, ((diagWt a r : ℤ) - k r / 2).toNat)) := by ring
    _ ≤ (g - 1) ^ 2 * packL g * (2 * S) := by
        rw [hsplit]; exact Nat.mul_le_mul_left _ (by omega)
    _ = (g - 1) ^ 2 * (2 * packL g) * S := by ring
    _ ≤ (g * g - 1) ^ 2 * S := Nat.mul_le_mul_right _ hL

end Budgets

/-! ### Packing ((eq:pack)) -/

section Pack

variable (L : ℕ)

/-- Pack `L - 1` streams (`streams s` for `s ∈ {1, …, L - 1}`; stream `0` is ignored) of one
direction: a request of type `i` in stream `s` becomes one of type `L i + s`. -/
def packDir (streams : ℕ → Multiset ℕ) : Multiset ℕ :=
  ∑ s ∈ Finset.Ioo 0 L, (streams s).map fun i => L * i + s

/-- Unpack stream `s` of one direction: the types `≡ s (mod L)`, divided by `L`. -/
def unpackDir (τ : Multiset ℕ) (s : ℕ) : Multiset ℕ :=
  (τ.filter fun t => t % L = s).map fun t => t / L

/-- A packed label of exact weight `a`: the first direction packs the first multisets of the
stream labels and is padded with requests of type `0` up to weight `a`; the second packs the
second multisets. -/
def pack (a : ℕ) (streams : ℕ → Label) : Label :=
  let down := packDir L fun s => (streams s).1
  let up := packDir L fun s => (streams s).2
  (down + Multiset.replicate (a - labelWt (down, up)) 0, up)

/-- Unpack stream `s`. -/
def unpack (l : Label) (s : ℕ) : Label := (unpackDir L l.1 s, unpackDir L l.2 s)

/-- A label is valid for packing: no request of the second multiset, and no request other than
type `0` of the first, has type `≡ 0 (mod L)`. -/
def validLabel (l : Label) : Prop :=
  (∀ t ∈ l.1, t % L = 0 → t = 0) ∧ ∀ t ∈ l.2, t % L ≠ 0

instance (l : Label) : Decidable (validLabel L l) := by unfold validLabel; infer_instance

private theorem wt_finsetSum {ι : Type*} (S : Finset ι) (f : ι → Multiset ℕ) :
    wt (∑ s ∈ S, f s) = ∑ s ∈ S, wt (f s) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert x S hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, wt_add, ih]

private theorem wt_map_le (σ : Multiset ℕ) (f : ℕ → ℕ) (c : ℕ) (h : ∀ i, f i + 1 ≤ c * (i + 1)) :
    wt (σ.map f) ≤ c * wt σ := by
  induction σ using Multiset.induction_on with
  | empty => simp
  | cons i σ ih => simp only [Multiset.map_cons, wt_cons]; rw [mul_add]; have := h i; omega

private theorem wt_replicate_zero (n : ℕ) : wt (Multiset.replicate n 0) = n := by
  simp [wt, Multiset.map_replicate, Multiset.sum_replicate]

/-- The weight of the packed requests is at most `L` times the weight of the streams. -/
theorem labelWt_packDir_le (streams : ℕ → Label) :
    labelWt (packDir L (fun s => (streams s).1), packDir L fun s => (streams s).2) ≤
      L * ∑ s ∈ Finset.Ioo 0 L, labelWt (streams s) := by
  unfold labelWt packDir
  rw [wt_finsetSum, wt_finsetSum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun s hs => ?_
  have hs' := (Finset.mem_Ioo.mp hs).2
  rw [mul_add]
  exact add_le_add (wt_map_le _ _ _ fun i => by rw [mul_add, mul_one]; omega)
    (wt_map_le _ _ _ fun i => by rw [mul_add, mul_one]; omega)

private theorem unpackDir_add (τ τ' : Multiset ℕ) (s : ℕ) :
    unpackDir L (τ + τ') s = unpackDir L τ s + unpackDir L τ' s := by
  simp [unpackDir, Multiset.filter_add, Multiset.map_add]

private theorem unpackDir_finsetSum {ι : Type*} (S : Finset ι) (f : ι → Multiset ℕ) (s : ℕ) :
    unpackDir L (∑ x ∈ S, f x) s = ∑ x ∈ S, unpackDir L (f x) s := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [unpackDir]
  | insert x S hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, unpackDir_add, ih]

private theorem unpackDir_map {s s' : ℕ} (hs' : s' < L) (σ : Multiset ℕ) :
    unpackDir L (σ.map fun i => L * i + s') s = if s' = s then σ else 0 := by
  have hL : 0 < L := by omega
  unfold unpackDir
  rw [Multiset.filter_map, Multiset.map_map]
  have hmod : ∀ i, (L * i + s') % L = s' := fun i => by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hs']
  have hdiv : ∀ i, (L * i + s') / L = i := fun i => by
    rw [Nat.mul_add_div hL, Nat.div_eq_of_lt hs', Nat.add_zero]
  split_ifs with h
  · subst h; simp [hmod, hdiv]
  · simp [hmod, h]

private theorem mod_ne_zero_of_mem_packDir {f : ℕ → Multiset ℕ} {t : ℕ} (h : t ∈ packDir L f) :
    t % L ≠ 0 := by
  obtain ⟨s, hs, ht⟩ := Multiset.mem_sum.mp h
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp ht
  rw [Finset.mem_Ioo] at hs
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hs.2]
  omega

/-- Packing the unpacked streams keeps exactly the requests of nonzero residue. -/
private theorem packDir_unpackDir (hL : 1 ≤ L) (τ : Multiset ℕ) :
    packDir L (unpackDir L τ) = τ.filter fun t => t % L ≠ 0 := by
  have e : ∀ s, (unpackDir L τ s).map (fun i => L * i + s) = τ.filter fun t => t % L = s := by
    intro s
    unfold unpackDir
    rw [Multiset.map_map]
    conv_rhs => rw [← Multiset.map_id (τ.filter fun t => t % L = s)]
    refine Multiset.map_congr rfl fun t ht => ?_
    have := (Multiset.mem_filter.mp ht).2
    simp only [Function.comp_apply, id]
    rw [← this]
    exact Nat.div_add_mod t L
  unfold packDir
  simp only [e]
  ext t
  rw [Multiset.count_sum', Multiset.count_filter]
  simp only [Multiset.count_filter]
  rw [Finset.sum_ite_eq]
  have := Nat.mod_lt t (show 0 < L by omega)
  by_cases h : t % L = 0
  · simp [h]
  · simp [Finset.mem_Ioo.mpr ⟨Nat.pos_of_ne_zero h, this⟩, h]

/-- **Packing ((eq:pack)).** For `2 ≤ L`, packing is a bijection from the stream tuples (streams
`1, …, L - 1`) whose packed requests weigh at most `a` onto the valid labels of weight `a`, with
inverse `unpack`. -/
theorem unpack_pack {a : ℕ} (hL : 2 ≤ L) (streams : ℕ → Label)
    (ha : labelWt (packDir L (fun s => (streams s).1), packDir L fun s => (streams s).2) ≤ a)
    {s : ℕ} (hs : s ∈ Finset.Ioo 0 L) : unpack L (pack L a streams) s = streams s := by
  have hs' := Finset.mem_Ioo.mp hs
  have hpk : ∀ f : ℕ → Multiset ℕ, unpackDir L (packDir L f) s = f s := by
    intro f
    unfold packDir
    rw [unpackDir_finsetSum]
    rw [Finset.sum_congr rfl fun s' hs'' => unpackDir_map L (Finset.mem_Ioo.mp hs'').2 (f s')]
    simp [Finset.sum_ite_eq', hs]
  have hz : ∀ n, unpackDir L (Multiset.replicate n 0) s = 0 := by
    intro n
    unfold unpackDir
    rw [Multiset.filter_eq_nil.mpr fun t ht => by
      rw [Multiset.eq_of_mem_replicate ht, Nat.zero_mod]; omega]
    simp
  simp only [unpack, pack, unpackDir_add, hpk, hz, add_zero]

theorem pack_valid {a : ℕ} (hL : 2 ≤ L) (streams : ℕ → Label)
    (ha : labelWt (packDir L (fun s => (streams s).1), packDir L fun s => (streams s).2) ≤ a) :
    validLabel L (pack L a streams) ∧ labelWt (pack L a streams) = a := by
  refine ⟨⟨fun t ht h0 => ?_, fun t ht => mod_ne_zero_of_mem_packDir L ht⟩, ?_⟩
  · rcases Multiset.mem_add.mp ht with ht | ht
    · exact absurd h0 (mod_ne_zero_of_mem_packDir L ht)
    · exact Multiset.eq_of_mem_replicate ht
  · simp only [pack, labelWt, wt_add, wt_replicate_zero] at ha ⊢
    omega

theorem pack_unpack {a : ℕ} (hL : 2 ≤ L) (l : Label) (hv : validLabel L l)
    (hw : labelWt l = a) : pack L a (unpack L l) = l := by
  obtain ⟨hv1, hv2⟩ := hv
  have hU : packDir L (fun s => (unpack L l s).2) = l.2 := by
    rw [show (fun s => (unpack L l s).2) = unpackDir L l.2 from rfl, packDir_unpackDir L (by omega),
      Multiset.filter_eq_self.mpr hv2]
  have hD : packDir L (fun s => (unpack L l s).1) = l.1.filter fun t => t % L ≠ 0 :=
    packDir_unpackDir L (by omega) l.1
  set Z := l.1.filter fun t => ¬ (t % L ≠ 0)
  have hZ : Z = Multiset.replicate (Multiset.card Z) 0 :=
    Multiset.eq_replicate.mpr ⟨rfl, fun t ht => by
      obtain ⟨ht, h⟩ := Multiset.mem_filter.mp ht
      exact hv1 t ht (not_not.mp h)⟩
  have hsplit := Multiset.filter_add_not (fun t => t % L ≠ 0) l.1
  have hwZ : wt Z = Multiset.card Z := by rw [hZ, wt_replicate_zero, Multiset.card_replicate]
  have hw1 : wt l.1 = wt (l.1.filter fun t => t % L ≠ 0) + wt Z := by
    conv_lhs => rw [← hsplit]
    rw [wt_add]
  unfold labelWt at hw
  simp only [pack]
  rw [hU, hD]
  refine Prod.ext ?_ rfl
  simp only [labelWt]
  rw [show a - (wt (l.1.filter fun t => t % L ≠ 0) + wt l.2) = Multiset.card Z by omega, ← hZ,
    hsplit]

end Pack

end Cslib.Complexity.NtimeDspace.Cube
