/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.ClauseSet.Sparsification.Step
import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Positivity

/-!
# Sparsification -- the analysis of one branch

A `Path` records one branch of the sparsification procedure: nodes `ψ₀, ψ₁, …, ψ_L` where each
`ψ_{i+1}` is the heart or the petal child of `ψ_i` for a valid choice. Following Calabro,
Impagliazzo and Paturi [CalabroImpagliazzoPaturi2006], the clauses a step *introduces* (its heart,
or its petals) are new: they occur in no earlier node, survive into the next node, and are distinct
across steps. So the length of a branch is at most the number of introduced clauses.

A new clause of size `c` that does not survive to the last node is *eliminated* by a smaller clause
introduced later. The key estimate ([Calabro, Lemma 5.9][Calabro2009]) is that fewer than
`2 θ (c - h)` new clauses of size `c` containing a fixed clause of size `h < c` can be present at
once. It holds along any valid steps whose new clauses of size at least two are introduced by the
chosen branch (`card_newContaining_lt_of_steps`), so it serves both this procedure
(`Path.card_newContaining_lt`) and counting sparsification, whose steps also add unit clauses.
When the last node is sparse and the variables of the root are among `N` given ones, it has fewer
than `2 N θ (c - 1)` clauses of size `c`. Together these bound the number of introduced clauses of
size `c` by
`2 N θ (c - 1) + ∑_{h < c} 2 θ (c - h) · #(introduced clauses of size h)`
(`card_introducedOfCard_le`). Each petal step with petals of size `j` introduces at least `θ j`
clauses of size `j` (`mul_card_petalSteps_le`).

## Main definitions

* `Cslib.Logic.PL.ClauseSet.Sparsification.Path`,
  `Cslib.Logic.PL.ClauseSet.Sparsification.Path.introAt`,
  `Cslib.Logic.PL.ClauseSet.Sparsification.Path.introduced`,
  `Cslib.Logic.PL.ClauseSet.Sparsification.Path.introducedOfCard`,
  `Cslib.Logic.PL.ClauseSet.Sparsification.Path.newContaining`,
  `Cslib.Logic.PL.ClauseSet.Sparsification.Path.petalSteps`: a branch of the procedure, its
  introduced clauses, new clauses containing a fixed clause, and petal steps of a given size.
* `Cslib.Logic.PL.ClauseSet.Sparsification.Refines`: every clause is contained in another.

## Main results

* `Cslib.Logic.PL.ClauseSet.Sparsification.Path.len_le_card_introduced`: a branch is no longer
  than its number of introduced clauses.
* `Cslib.Logic.PL.ClauseSet.Sparsification.card_newContaining_lt_of_steps`,
  `Cslib.Logic.PL.ClauseSet.Sparsification.Path.card_newContaining_lt`: few new clauses contain a
  fixed clause.
* `Cslib.Logic.PL.ClauseSet.Sparsification.Path.card_introducedOfCard_le`: the recursive bound on
  the introduced clauses.
* `Cslib.Logic.PL.ClauseSet.Sparsification.Path.mul_card_petalSteps_le`: petal steps introduce
  many clauses.

## References

* [R. Impagliazzo, R. Paturi, F. Zane, *Which problems have strongly exponential
  complexity?*][ImpagliazzoPaturiZane2001]
* [C. Calabro, R. Impagliazzo, R. Paturi, *A duality between clause width and clause density for
  SAT*][CalabroImpagliazzoPaturi2006]
* [C. Calabro, *The Exponential Complexity of Satisfiability Problems*][Calabro2009]
-/

@[expose] public section

namespace Cslib.Logic.PL.ClauseSet.Sparsification

open Finset

variable {V : Type*} [DecidableEq V]

/-- One branch of the sparsification procedure, with `len` branching steps. -/
structure Path (θ : ℕ → ℕ) (V : Type*) [DecidableEq V] where
  /-- The number of branching steps. -/
  len : ℕ
  /-- The clause set at each node. -/
  node : ℕ → ClauseSet V
  /-- The clause size of the flower chosen at each node. -/
  size : ℕ → ℕ
  /-- The heart chosen at each node. -/
  heart : ℕ → Finset (Literal V)
  /-- The branch taken at each node: `false` for the heart, `true` for the petals. -/
  dir : ℕ → Bool
  choice : ∀ i < len, Choice θ (node i) (size i) (heart i)
  step : ∀ i < len, node (i + 1) = child (node i) (size i) (heart i) (dir i)
  reduced_zero : Reduced (node 0)

/-- Every clause of `α` is contained in a clause of `β`. -/
def Refines (α β : ClauseSet V) : Prop :=
  ∀ a ∈ α, ∃ b ∈ β, a ⊆ b

omit [DecidableEq V] in
/-- Clause-set refinement `Refines` is transitive. -/
theorem Refines.trans {α β γ : ClauseSet V} (h₁ : Refines α β) (h₂ : Refines β γ) :
    Refines α γ := by
  intro a ha
  obtain ⟨b, hb, hab⟩ := h₁ a ha
  exact (h₂ b hb).imp fun _ ⟨hc, hbc⟩ => ⟨hc, hab.trans hbc⟩

/-- In a sparse clause set, at most `θ (c - 1)` clauses of size `c ≥ 1` contain a given
literal. -/
theorem card_flower_singleton_le_of_sparse {θ : ℕ → ℕ} (hθ : ∀ j, 1 ≤ θ j) {ψ : ClauseSet V}
    (hsparse : Sparse θ ψ) {c : ℕ} (hc : 1 ≤ c) (l : Literal V) :
    (flower ψ c {l}).card ≤ θ (c - 1) := by
  by_cases hc2 : 2 ≤ c
  · have hnot := hsparse c {l}
    simp only [Heavy, card_singleton, le_refl, true_and, not_and, not_le] at hnot
    exact (hnot (by omega)).le
  obtain rfl : c = 1 := by omega
  refine (card_le_card (t := {{l}}) fun C hC => ?_).trans ((card_singleton _).trans_le (hθ 0))
  obtain ⟨-, hcard, hl⟩ := mem_flower.mp hC
  exact mem_singleton.2 (eq_of_subset_of_card_le hl (by rw [hcard, card_singleton])).symm

/-- At most `2 N θ (c - 1)` clauses of size `c ≥ 1` survive in a sparse clause set whose variables
are among `N` given ones. -/
private theorem card_filter_card_eq_le_of_sparse {θ : ℕ → ℕ} (hθ : ∀ j, 1 ≤ θ j) {ψ : ClauseSet V}
    (hsparse : Sparse θ ψ) (U : Finset V) (hU : ∀ C ∈ ψ, ∀ l ∈ C, l.1 ∈ U) {c : ℕ} (hc : 1 ≤ c) :
    (ψ.filter (·.card = c)).card ≤ 2 * U.card * θ (c - 1) := by
  have hflower := card_flower_singleton_le_of_sparse hθ hsparse hc
  have hsub : ψ.filter (·.card = c) ⊆
      (U ×ˢ (univ : Finset Bool)).biUnion fun l => flower ψ c {l} := by
    intro C hC
    obtain ⟨hCψ, hcard⟩ := mem_filter.mp hC
    obtain ⟨l, hl⟩ : C.Nonempty := by rw [← card_pos, hcard]; omega
    exact mem_biUnion.mpr ⟨l, mem_product.mpr ⟨hU C hCψ l hl, mem_univ _⟩,
      mem_flower.mpr ⟨hCψ, hcard, by simpa using hl⟩⟩
  calc (ψ.filter (·.card = c)).card
      ≤ ∑ l ∈ U ×ˢ (univ : Finset Bool), (flower ψ c {l}).card :=
        (card_le_card hsub).trans card_biUnion_le
    _ ≤ ∑ _l ∈ U ×ˢ (univ : Finset Bool), θ (c - 1) := sum_le_sum fun l _ => hflower l
    _ = 2 * U.card * θ (c - 1) := by
      rw [sum_const, card_product, card_univ, Fintype.card_bool, smul_eq_mul, Nat.mul_comm _ 2]

/-- **Few new clauses contain a fixed clause** [Calabro, Lemma 5.9][Calabro2009]. Along clause sets
`ψ 0, …, ψ N`, where each `ψ i` has the valid choice `(c i, H i)` and every clause of width at
least two that is new in `ψ (i + 1)` is introduced by the branch `b i`, fewer than
`2 θ (j - |S|)` clauses of width `j` that are absent from `ψ 0` and contain a fixed literal set `S`
with `1 ≤ |S| < j` are present in any `ψ t`. Both the sparsification step (`child`) and the
counting step, which also adds unit clauses, satisfy the hypothesis. -/
theorem card_newContaining_lt_of_steps {θ : ℕ → ℕ} (hθ : ∀ r, 1 ≤ θ r)
    (N : ℕ) (ψ : ℕ → ClauseSet V) (c : ℕ → ℕ) (H : ℕ → Finset (Literal V)) (b : ℕ → Bool)
    (hchoice : ∀ i < N, Choice θ (ψ i) (c i) (H i))
    (hnew : ∀ i < N, ∀ C ∈ ψ (i + 1), C ∉ ψ i → 2 ≤ C.card → C ∈ intro (ψ i) (c i) (H i) (b i))
    {t j : ℕ} (ht : t ≤ N) {S : Finset (Literal V)} (hS : 1 ≤ S.card) (hSj : S.card < j) :
    ((ψ t).filter fun C => C ∉ ψ 0 ∧ C.card = j ∧ S ⊆ C).card < 2 * θ (j - S.card) := by
  set γ := (ψ t).filter fun C => C ∉ ψ 0 ∧ C.card = j ∧ S ⊆ C
  by_contra hge
  push Not at hge
  have hγ : ∀ C ∈ γ, C ∉ ψ 0 ∧ C.card = j ∧ S ⊆ C := fun C hC => (mem_filter.mp hC).2
  have hex : ∃ m, γ ⊆ ψ m := ⟨t, filter_subset _ _⟩
  set x := Nat.find hex
  have hxsub : γ ⊆ ψ x := Nat.find_spec hex
  have hxle : x ≤ t := Nat.find_min' hex (filter_subset _ _)
  have hγne : γ.Nonempty := by rw [← card_pos]; have := hθ (j - S.card); omega
  have hx0 : x ≠ 0 := fun hx => hγne.elim fun C hC => (hγ C hC).1 (hx ▸ hxsub hC)
  obtain ⟨m, hxm⟩ : ∃ m, x = m + 1 := ⟨x - 1, by omega⟩
  have hm : m < N := by omega
  have hnotsub : ¬ γ ⊆ ψ m := Nat.find_min hex (by omega)
  -- the clauses of `γ` absent from `ψ m` are introduced at step `m`
  have hintro : ∀ C ∈ γ, C ∉ ψ m → C ∈ intro (ψ m) (c m) (H m) (b m) := fun C hC hCm =>
    hnew m hm C (hxm ▸ hxsub hC) hCm (by have := (hγ C hC).2.1; omega)
  -- so the flower size at step `m` exceeds `j`
  obtain ⟨C₀, hC₀γ, hC₀old⟩ := not_subset.mp hnotsub
  have hjc : j < c m :=
    (hγ C₀ hC₀γ).2.1 ▸ (card_of_mem_intro (hchoice m hm).1 (hintro C₀ hC₀γ hC₀old)).2
  -- and `S` is not heavy at `ψ m`
  have hlight : (flower (ψ m) j S).card < θ (j - S.card) := not_le.1 fun hheavy =>
    absurd ((hchoice m hm).2.1 j S ⟨hS, hSj, hheavy⟩) (by omega)
  have hold : (γ ∩ ψ m).card < θ (j - S.card) :=
    (card_le_card fun C hC =>
      mem_flower.2 ⟨(mem_inter.1 hC).2, (hγ C (mem_inter.1 hC).1).2⟩).trans_lt hlight
  let Q := γ \ ψ m
  have hsplit : Q.card + (γ ∩ ψ m).card = γ.card := card_sdiff_add_card_inter _ _
  have hQcard : θ (j - S.card) + 1 ≤ Q.card := by omega
  have hQintro : Q ⊆ intro (ψ m) (c m) (H m) (b m) := fun C hC =>
    hintro C (mem_sdiff.mp hC).1 (mem_sdiff.mp hC).2
  cases hdir : b m with
  | false =>
    have hQone : Q.card ≤ 1 := by
      simpa only [hdir, intro, card_singleton] using card_le_card hQintro
    have := hθ (j - S.card)
    omega
  | true =>
    -- the clauses whose petals lie in `Q` all contain the larger heart `H m ∪ S`
    have hQpetal : ∀ q ∈ Q, q ∈ petals (ψ m) (c m) (H m) := fun q hq => by
      simpa only [hdir, intro] using hQintro hq
    obtain ⟨q₀, hq₀⟩ : Q.Nonempty := by rw [← card_pos]; omega
    obtain ⟨D₀, -, hD₀q⟩ := mem_petals.mp (hQpetal q₀ hq₀)
    have hSq₀ : S ⊆ q₀ := (hγ q₀ (mem_sdiff.mp hq₀).1).2.2
    have hdisj : Disjoint (H m) S := Finset.disjoint_sdiff.mono_right (hD₀q ▸ hSq₀)
    have hcardHS : (H m ∪ S).card = (H m).card + S.card := card_union_of_disjoint hdisj
    have hj : j = c m - (H m).card :=
      (hγ q₀ (mem_sdiff.mp hq₀).1).2.1 ▸ card_of_mem_petals (hQpetal q₀ hq₀)
    have hHc : (H m).card < c m := (hchoice m hm).1.2.1
    have hQle : Q.card ≤ (flower (ψ m) (c m) (H m ∪ S)).card := by
      refine (card_le_card (t := (flower (ψ m) (c m) (H m ∪ S)).image (· \ H m)) ?_).trans
        card_image_le
      intro q hq
      obtain ⟨D, hD, rfl⟩ := mem_petals.mp (hQpetal q hq)
      obtain ⟨hDψ, hDcard, hHD⟩ := mem_flower.mp hD
      have hSD := (hγ _ (mem_sdiff.mp hq).1).2.2
      exact mem_image.2
        ⟨D, mem_flower.2 ⟨hDψ, hDcard, union_subset hHD (hSD.trans sdiff_subset)⟩, rfl⟩
    have hheavy : Heavy θ (ψ m) (c m) (H m ∪ S) := ⟨by omega, by omega, by
      rw [show c m - (H m ∪ S).card = j - S.card by omega]; omega⟩
    have := (hchoice m hm).2.2 (H m ∪ S) hheavy
    omega

namespace Path

variable {θ : ℕ → ℕ} (P : Path θ V)

/-- The clauses introduced by step `i`. -/
def introAt (i : ℕ) : ClauseSet V :=
  intro (P.node i) (P.size i) (P.heart i) (P.dir i)

/-- All clauses introduced along the branch. -/
def introduced : ClauseSet V :=
  (range P.len).biUnion P.introAt

/-- The introduced clauses of size `c`. -/
def introducedOfCard (c : ℕ) : ClauseSet V :=
  P.introduced.filter (·.card = c)

/-- The new clauses of size `c` in node `j` that contain `b`; *new* means absent from the root. -/
def newContaining (j c : ℕ) (b : Finset (Literal V)) : ClauseSet V :=
  (P.node j).filter fun a => a ∉ P.node 0 ∧ a.card = c ∧ b ⊆ a

/-- The petal steps whose petals have size `j`. -/
def petalSteps (j : ℕ) : Finset ℕ :=
  (range P.len).filter fun i => P.dir i = true ∧ P.size i - (P.heart i).card = j

variable {P}

private theorem heavy {i : ℕ} (hi : i < P.len) : Heavy θ (P.node i) (P.size i) (P.heart i) :=
  (P.choice i hi).1

private theorem reduced_node : ∀ i ≤ P.len, Reduced (P.node i)
  | 0, _ => P.reduced_zero
  | i + 1, hi => P.step i hi ▸ reduced_child _ _ _ _

/-- The clause set at node `i + 1` is contained in `P.node i ∪ P.introAt i`. -/
theorem node_succ_subset {i : ℕ} (hi : i < P.len) : P.node (i + 1) ⊆ P.node i ∪ P.introAt i := by
  exact P.step i hi ▸ child_subset _ _ _ _

section

variable (hθ : ∀ j, 1 ≤ θ j)
include hθ

private theorem refines_succ {i : ℕ} (hi : i < P.len) : Refines (P.node (i + 1)) (P.node i) := by
  intro a ha
  rcases mem_union.mp (node_succ_subset hi ha) with ha | ha
  · exact ⟨a, ha, subset_rfl⟩
  · obtain ⟨C, hC, haC⟩ := exists_flower_ssuperset hθ (heavy hi) ha
    exact ⟨C, flower_subset _ _ _ hC, haC.subset⟩

private theorem refines_of_le {i j : ℕ} (hij : i ≤ j) (hj : j ≤ P.len) :
    Refines (P.node j) (P.node i) := by
  induction j, hij using Nat.le_induction with
  | base => exact fun a ha => ⟨a, ha, subset_rfl⟩
  | succ j hij ih => exact (refines_succ hθ hj).trans (ih (by omega))

/-- **Introduced clauses survive.** Every clause introduced at step `i` is in node `i + 1`. -/
private theorem introAt_subset {i : ℕ} (hi : i < P.len) : P.introAt i ⊆ P.node (i + 1) := by
  intro a ha
  rw [P.step i hi, child, mem_reduce]
  refine ⟨mem_union_right _ ha, fun D hD hDa => ?_⟩
  obtain ⟨C, hC, haC⟩ := exists_flower_ssuperset hθ (heavy hi) ha
  rcases mem_union.mp hD with hD | hD
  · exact reduced_node i hi.le C (flower_subset _ _ _ hC) D hD (hDa.trans haC)
  · cases hdir : P.dir i <;> simp only [introAt, hdir, intro, mem_singleton] at ha hD
    · exact lt_irrefl _ (by rwa [ha, hD] at hDa)
    · exact (card_lt_card hDa).ne (by rw [card_of_mem_petals ha, card_of_mem_petals hD])

/-- **Introduced clauses are new.** A clause introduced at step `i` occurs in no node `j ≤ i`. -/
private theorem disjoint_introAt_node {i j : ℕ} (hi : i < P.len) (hji : j ≤ i) :
    Disjoint (P.introAt i) (P.node j) := by
  rw [Finset.disjoint_left]
  intro a ha haj
  obtain ⟨C, hC, haC⟩ := exists_flower_ssuperset hθ (heavy hi) ha
  obtain ⟨D, hD, hCD⟩ := refines_of_le hθ hji hi.le C (flower_subset _ _ _ hC)
  exact reduced_node j (hji.trans hi.le) D hD a haj (haC.trans_subset hCD)

private theorem disjoint_introAt {i j : ℕ} (hij : i < j) (hj : j < P.len) :
    Disjoint (P.introAt i) (P.introAt j) :=
  Finset.disjoint_of_subset_left (introAt_subset hθ (hij.trans hj))
    (disjoint_introAt_node hθ hj hij).symm

private theorem pairwiseDisjoint_introAt :
    ((range P.len : Finset ℕ) : Set ℕ).PairwiseDisjoint P.introAt := by
  intro i hi j hj hne
  simp only [coe_range, Set.mem_Iio] at hi hj
  rcases lt_or_gt_of_ne hne with h | h
  · exact disjoint_introAt hθ h hj
  · exact (disjoint_introAt hθ h hi).symm

/-- **A branch is no longer than its number of introduced clauses.** -/
theorem len_le_card_introduced : P.len ≤ P.introduced.card := by
  rw [introduced, card_biUnion (pairwiseDisjoint_introAt hθ)]
  calc P.len = ∑ _i ∈ range P.len, 1 := by simp
    _ ≤ ∑ i ∈ range P.len, (P.introAt i).card :=
        sum_le_sum fun i hi => card_pos.mpr (intro_nonempty hθ (heavy (mem_range.mp hi)) _)

private theorem notMem_node_zero_of_mem_introduced {a : Finset (Literal V)}
    (ha : a ∈ P.introduced) : a ∉ P.node 0 := by
  obtain ⟨i, hi, hai⟩ := mem_biUnion.mp ha
  exact disjoint_left.mp (disjoint_introAt_node hθ (mem_range.mp hi) (Nat.zero_le i)) hai

/-- **Few new clauses contain a fixed clause** [Calabro, Lemma 5.9][Calabro2009]. Fewer than
`2 θ (c - |b|)` new clauses of size `c` containing a fixed clause `b` with `1 ≤ |b| < c` are
present in any node. -/
theorem card_newContaining_lt {j c : ℕ} (hj : j ≤ P.len) {b : Finset (Literal V)}
    (hb1 : 1 ≤ b.card) (hbc : b.card < c) :
    (P.newContaining j c b).card < 2 * θ (c - b.card) :=
  card_newContaining_lt_of_steps hθ P.len P.node P.size P.heart P.dir P.choice
    (fun _ hi _ hC hCi _ => (mem_union.mp (node_succ_subset hi hC)).resolve_left hCi) hj hb1 hbc

/-- **Counting introduced clauses.** If the last node is sparse and the variables of the root are
among the `N` variables of `U`, the introduced clauses of size `c ≥ 1` number at most
`2 N θ (c - 1) + ∑_{1 ≤ h < c} 2 θ (c - h) · #(introduced, size h)`. -/
theorem card_introducedOfCard_le (hleaf : Sparse θ (P.node P.len)) (U : Finset V)
    (hU : ∀ C ∈ P.node 0, ∀ l ∈ C, l.1 ∈ U) {c : ℕ} (hc : 1 ≤ c) :
    (P.introducedOfCard c).card ≤
      2 * U.card * θ (c - 1) +
        ∑ h ∈ Ico 1 c, 2 * θ (c - h) * (P.introducedOfCard h).card := by
  -- every introduced clause of size `c` survives to the leaf or is eliminated later
  have hcover : P.introducedOfCard c ⊆ (P.node P.len).filter (·.card = c) ∪
      (range P.len).biUnion fun m =>
        ((P.introAt m).filter (·.card < c)).biUnion fun b => P.newContaining m c b := by
    intro a ha
    obtain ⟨haI, hac⟩ := mem_filter.mp ha
    obtain ⟨i, hi, hai⟩ := mem_biUnion.mp haI
    have hi' := mem_range.mp hi
    have hnew := notMem_node_zero_of_mem_introduced hθ haI
    by_cases hleafa : a ∈ P.node P.len
    · exact mem_union_left _ (mem_filter.mpr ⟨hleafa, hac⟩)
    · refine mem_union_right _ ?_
      have hex : ∃ m, i + 1 ≤ m ∧ a ∉ P.node m := ⟨P.len, hi', hleafa⟩
      set m₀ := Nat.find hex
      obtain ⟨hm₀i, hm₀a⟩ : i + 1 ≤ m₀ ∧ a ∉ P.node m₀ := Nat.find_spec hex
      have hm₀le : m₀ ≤ P.len := Nat.find_min' hex ⟨hi', hleafa⟩
      have hm₀ne : m₀ ≠ i + 1 := fun h => hm₀a (h ▸ introAt_subset hθ hi' hai)
      obtain ⟨m, hm⟩ : ∃ m, m₀ = m + 1 := ⟨m₀ - 1, by omega⟩
      have hma : a ∈ P.node m := Decidable.byContradiction fun hna =>
        Nat.find_min hex (m.lt_succ_self.trans_eq hm.symm) ⟨by omega, hna⟩
      have hmlen : m < P.len := by omega
      have hstep : a ∉ child (P.node m) (P.size m) (P.heart m) (P.dir m) := by
        rwa [← P.step m hmlen, ← hm]
      obtain ⟨b, hb, hba⟩ := exists_ssubset_of_notMem_reduce (reduced_node m hmlen.le) hma hstep
      exact mem_biUnion.mpr ⟨m, mem_range.mpr hmlen, mem_biUnion.mpr ⟨b,
        mem_filter.mpr ⟨hb, hac ▸ card_lt_card hba⟩,
        mem_filter.mpr ⟨hma, hnew, hac, hba.subset⟩⟩⟩
  have hmaps : ∀ b ∈ P.introduced.filter (·.card < c), b.card ∈ Ico 1 c := by
    intro b hb
    obtain ⟨hbI, hbc⟩ := mem_filter.mp hb
    obtain ⟨i, hi, hbi⟩ := mem_biUnion.mp hbI
    exact mem_Ico.mpr ⟨(card_of_mem_intro (heavy (mem_range.mp hi)) hbi).1, hbc⟩
  have hsum : ∑ m ∈ range P.len, ∑ b ∈ (P.introAt m).filter (·.card < c),
      (P.newContaining m c b).card ≤
        ∑ h ∈ Ico 1 c, 2 * θ (c - h) * (P.introducedOfCard h).card := by
    calc ∑ m ∈ range P.len, ∑ b ∈ (P.introAt m).filter (·.card < c),
          (P.newContaining m c b).card
        ≤ ∑ m ∈ range P.len, ∑ b ∈ (P.introAt m).filter (·.card < c), 2 * θ (c - b.card) := by
          refine sum_le_sum fun m hm => sum_le_sum fun b hb => ?_
          obtain ⟨hbm, hbc⟩ := mem_filter.mp hb
          have hb1 := (card_of_mem_intro (heavy (mem_range.mp hm)) hbm).1
          exact (card_newContaining_lt hθ (mem_range.mp hm).le hb1 hbc).le
      _ = ∑ b ∈ P.introduced.filter (·.card < c), 2 * θ (c - b.card) := by
          rw [introduced, filter_biUnion, sum_biUnion fun i hi j hj hne =>
            Finset.disjoint_filter_filter (pairwiseDisjoint_introAt hθ hi hj hne)]
      _ = ∑ h ∈ Ico 1 c, ∑ b ∈ (P.introduced.filter (·.card < c)).filter (·.card = h),
            2 * θ (c - h) := (sum_fiberwise_of_maps_to' hmaps fun h => 2 * θ (c - h)).symm
      _ = ∑ h ∈ Ico 1 c, 2 * θ (c - h) * (P.introducedOfCard h).card := by
          refine sum_congr rfl fun h hh => ?_
          rw [sum_const, smul_eq_mul, mul_comm, filter_filter, introducedOfCard]
          congr 2
          exact filter_congr fun b _ => by have := (mem_Ico.mp hh).2; omega
  -- the leaf is sparse, and the eliminated clauses are counted by `hsum`
  refine (card_le_card hcover).trans ((card_union_le _ _).trans (add_le_add
    (card_filter_card_eq_le_of_sparse hθ hleaf U (fun C hC l hl => ?_) hc)
    ((card_biUnion_le.trans (sum_le_sum fun m _ => card_biUnion_le)).trans hsum)))
  obtain ⟨D, hD, hCD⟩ := refines_of_le hθ (Nat.zero_le _) le_rfl C hC
  exact hU D hD l (hCD hl)

/-- **Petal steps introduce many clauses.** The petal steps with petals of size `j` number at
most `#(introduced, size j) / θ j`. -/
theorem mul_card_petalSteps_le (j : ℕ) :
    θ j * (P.petalSteps j).card ≤ (P.introducedOfCard j).card := by
  have hsub : (P.petalSteps j).biUnion P.introAt ⊆ P.introducedOfCard j := by
    intro a ha
    obtain ⟨i, hi, hai⟩ := mem_biUnion.mp ha
    obtain ⟨hi', hdir, hj⟩ := mem_filter.mp hi
    exact mem_filter.mpr ⟨mem_biUnion.mpr ⟨i, hi', hai⟩,
      hj ▸ card_of_mem_petals (by simpa only [introAt, hdir, intro] using hai)⟩
  have hdisj : ((P.petalSteps j : Finset ℕ) : Set ℕ).PairwiseDisjoint P.introAt :=
    (pairwiseDisjoint_introAt hθ).subset fun i hi => (mem_filter.mp (mem_coe.mp hi)).1
  rw [mul_comm, ← smul_eq_mul, ← sum_const]
  refine (sum_le_sum fun i hi => ?_).trans ((card_biUnion hdisj).symm.trans_le (card_le_card hsub))
  obtain ⟨hi', hdir, hj⟩ := mem_filter.mp hi
  simp only [introAt, hdir, intro, card_petals]
  exact hj ▸ (heavy (mem_range.mp hi')).2.2

/-- In a branch from a clause set of width `k`, all nodes have width `k`. -/
private theorem card_le_of_mem_node {k : ℕ} (hk : ∀ C ∈ P.node 0, C.card ≤ k) :
    ∀ i ≤ P.len, ∀ C ∈ P.node i, C.card ≤ k
  | 0, _ => hk
  | i + 1, hi => fun _ hC =>
    card_le_of_mem_child hθ (heavy hi) (card_le_of_mem_node hk i (by omega)) (P.step i hi ▸ hC)

/-- In a branch from a clause set of width `k`, every chosen flower size is at most `k`. -/
private theorem size_le {k : ℕ} (hk : ∀ C ∈ P.node 0, C.card ≤ k) {i : ℕ} (hi : i < P.len) :
    P.size i ≤ k := by
  obtain ⟨C, hC⟩ := (heavy hi).flower_nonempty hθ
  obtain ⟨hCψ, hCcard, -⟩ := mem_flower.mp hC
  exact hCcard ▸ card_le_of_mem_node hθ hk i hi.le C hCψ

/-- Introduced clauses have size between `1` and `k - 1`. -/
private theorem card_mem_Ico_of_mem_introduced {k : ℕ} (hk : ∀ C ∈ P.node 0, C.card ≤ k)
    {a : Finset (Literal V)} (ha : a ∈ P.introduced) : a.card ∈ Ico 1 k := by
  obtain ⟨i, hi, hai⟩ := mem_biUnion.mp ha
  obtain ⟨h1, hlt⟩ := card_of_mem_intro (heavy (mem_range.mp hi)) hai
  have := size_le hθ hk (mem_range.mp hi)
  exact mem_Ico.mpr ⟨h1, by omega⟩

/-- The introduced clauses split by size into the sizes `1, …, k - 1`. -/
theorem card_introduced_eq_sum {k : ℕ} (hk : ∀ C ∈ P.node 0, C.card ≤ k) :
    P.introduced.card = ∑ c ∈ Ico 1 k, (P.introducedOfCard c).card := by
  exact card_eq_sum_card_fiberwise fun a ha => card_mem_Ico_of_mem_introduced hθ hk ha

/-- Every petal step has petals of some size `1, …, k - 1`. -/
theorem card_petal_le_sum {k : ℕ} (hk : ∀ C ∈ P.node 0, C.card ≤ k) :
    ((range P.len).filter fun i => P.dir i = true).card ≤
      ∑ j ∈ Ico 1 k, (P.petalSteps j).card := by
  have hsub : (range P.len).filter (fun i => P.dir i = true) ⊆
      (Ico 1 k).biUnion P.petalSteps := by
    intro i hi
    obtain ⟨hi', hdir⟩ := mem_filter.mp hi
    obtain ⟨h1, h2, -⟩ := heavy (mem_range.mp hi')
    have := size_le hθ hk (mem_range.mp hi')
    exact mem_biUnion.mpr ⟨P.size i - (P.heart i).card, mem_Ico.mpr ⟨by omega, by omega⟩,
      mem_filter.mpr ⟨hi', hdir, rfl⟩⟩
  exact (card_le_card hsub).trans card_biUnion_le

end

end Path

end Cslib.Logic.PL.ClauseSet.Sparsification
