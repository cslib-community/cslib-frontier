/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Multigraph
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Tactic.Linarith

/-!
# Crossing vertex covers and monotone anchored cuts

For a finite multigraph `G` and a vertex bipartition `b : V → Bool`, the *crossing graph* `D_b`
consists of the edges `e` whose endpoints carry opposite labels `b (G.src e) ≠ b (G.tgt e)`.
Its minimum vertex-cover size `crossingCover G b` equals the minimum of the anchored cut energy

`anchoredCost G b x = ∑ v, vertexPenalty G b x v`

over all edge colorings `x : E → Bool`, where `vertexPenalty G b x v` is `0` if every edge
incident to `v` agrees with the anchor bit `b v`, and `1` otherwise.

Each single-vertex penalty is complement-symmetric and jointly submodular on the Boolean lattice
`(b, x) ↦ Bool`. Consequently:

* `crossingCover G` is symmetric (`crossingCover_notVec`) and submodular
  (`crossingCover_submodular`, in both `ℕ` and `ℝ`).
* Flipping a single vertex bit changes `crossingCover G b` by at most `1`
  (`crossingCover_update_le`).
* Restricting to edge colorings clamped between the endpoint anchors (`IsClamped G b x`,
  `b u && b v ≤ x e ≤ b u || b v`) leaves the minimum unchanged (`exists_clamped_minimizer`).
* For every `b`, the clamped minimizers form a nonempty finite sublattice with a unique least
  element `leastClampedMinimizer G b`, which is monotone in `b`
  (`leastClampedMinimizer_mono`).

By Kőnig's theorem `crossingCover G b` is the size of a maximum matching among the crossing
edges, the cut function `mm(S)` of maximum matching width ([JeongSaetherTelle2015], §2, stated
there for graphs rather than multigraphs). Nothing here depends on that paper: the results are
proved directly.

## Main definitions

* `Cslib.Circuits.Frontier.CrossingCover.IsSubmodularBool`: Boolean-cube submodularity.
* `Cslib.Circuits.Frontier.CrossingCover.IsSymmetricBool`: complement symmetry on the Boolean cube.
* `Cslib.Circuits.Frontier.CrossingCover.IsClamped`: edge coloring clamped between endpoint bits.
* `Cslib.Circuits.Frontier.CrossingCover.vertexPenalty`,
  `Cslib.Circuits.Frontier.CrossingCover.anchoredCost`: anchored NAE vertex penalty and sum.
* `Cslib.Circuits.Frontier.CrossingCover.edgeSplit`,
  `Cslib.Circuits.Frontier.CrossingCover.splitCost`: unanchored vertex-split cost.
* `Cslib.Circuits.Frontier.CrossingCover.IsCrossingCover`,
  `Cslib.Circuits.Frontier.CrossingCover.crossingCover`: minimum vertex cover of crossing edges.
* `Cslib.Circuits.Frontier.CrossingCover.leastClampedMinimizer`: canonical monotone minimizer.

## Main results

* `Cslib.Circuits.Frontier.CrossingCover.anchoredCost_submodular`: joint submodularity of
  `anchoredCost`.
* `Cslib.Circuits.Frontier.CrossingCover.crossingCover_le_anchoredCost`,
  `Cslib.Circuits.Frontier.CrossingCover.exists_clamped_minimizer`: exact identity
  `τ(D_b) = min_x Q_b(x)` with clamped minimizers.
* `Cslib.Circuits.Frontier.CrossingCover.crossingCover_submodular`,
  `Cslib.Circuits.Frontier.CrossingCover.crossingCover_notVec`: symmetric submodularity of
  `τ(D_b)`.
* `Cslib.Circuits.Frontier.CrossingCover.crossingCover_update_le`: `1`-Lipschitz change on a
  single coordinate.
* `Cslib.Circuits.Frontier.CrossingCover.leastClampedMinimizer_mono`: monotonicity of the least
  clamped minimizer.

## References

* [J. Jeong, S. H. Sæther, J. A. Telle, *Maximum Matching Width: New Characterizations and a Fast
  Algorithm for Dominating Set*][JeongSaetherTelle2015]
-/

public section

namespace Cslib.Circuits.Frontier.CrossingCover

open Finset Function

/-! ### Submodular and symmetric functions on the Boolean cube -/

section BoolCube

variable {ι : Type*}

/-- Complement of a Boolean assignment. -/
@[expose] def notVec (a : ι → Bool) : ι → Bool := fun i => !a i

@[simp] theorem notVec_apply (a : ι → Bool) (i : ι) : notVec a i = !a i := rfl

@[simp] theorem notVec_notVec (a : ι → Bool) : notVec (notVec a) = a := by
  ext i; simp [notVec]

@[simp] theorem notVec_update [DecidableEq ι] (a : ι → Bool) (i : ι) (b : Bool) :
    notVec (update a i b) = update (notVec a) i (!b) := by
  ext j
  by_cases h : j = i
  · subst h; simp
  · simp [h]

/-- A real-valued function on the Boolean cube `{0,1}^ι` is **submodular** when
`f (a ⊓ b) + f (a ⊔ b) ≤ f a + f b` for all `a, b`. -/
@[expose] def IsSubmodularBool (f : (ι → Bool) → ℝ) : Prop :=
  ∀ a b : ι → Bool, f (a ⊓ b) + f (a ⊔ b) ≤ f a + f b

/-- A function on the Boolean cube is **complement-symmetric** when `f (!a) = f a`. -/
@[expose] def IsSymmetricBool {α : Type*} (f : (ι → Bool) → α) : Prop :=
  ∀ a : ι → Bool, f (notVec a) = f a

/-- The discrete marginal difference in coordinate `i`: `f (a^{i↦1}) - f (a^{i↦0})`. -/
@[expose] def diffBool [DecidableEq ι] (f : (ι → Bool) → ℝ) (i : ι) (a : ι → Bool) : ℝ :=
  f (update a i true) - f (update a i false)

/-- For a submodular function on the Boolean cube, changing coordinate `i` yields a nonincreasing
(antitone) discrete derivative in the other coordinates. -/
theorem IsSubmodularBool.diffBool_antitone [DecidableEq ι] {f : (ι → Bool) → ℝ}
    (hf : IsSubmodularBool f) (i : ι) : Antitone (diffBool f i) := by
  intro a b hab
  have h1 : update a i true ⊓ update b i false = update a i false := by
    ext j
    by_cases h : j = i
    · subst h; simp
    · simp only [Pi.inf_apply, update_of_ne h]
      exact inf_of_le_left (hab j)
  have h2 : update a i true ⊔ update b i false = update b i true := by
    ext j
    by_cases h : j = i
    · subst h; simp
    · simp only [Pi.sup_apply, update_of_ne h]
      exact sup_of_le_right (hab j)
  have hsub := hf (update a i true) (update b i false)
  rw [h1, h2] at hsub
  simp only [diffBool]
  linarith

/-- For a submodular function, every off-diagonal mixed difference is nonpositive. -/
theorem IsSubmodularBool.mixedDiff_nonpos [DecidableEq ι] {f : (ι → Bool) → ℝ}
    (hf : IsSubmodularBool f) {i j : ι} (_hij : i ≠ j) (a : ι → Bool) :
    f (update (update a i true) j true) - f (update (update a i true) j false) -
      f (update (update a i false) j true) + f (update (update a i false) j false) ≤ 0 := by
  have hle : update a i false ≤ update a i true := fun k => by
    by_cases h : k = i
    · subst h; simp
    · simp [h]
  have h := hf.diffBool_antitone j hle
  simp only [diffBool] at h
  linarith

/-- Complement symmetry reverses the sign of the discrete derivative. -/
theorem IsSymmetricBool.diffBool_notVec [DecidableEq ι] {f : (ι → Bool) → ℝ}
    (hsym : IsSymmetricBool f) (i : ι) (a : ι → Bool) :
    diffBool f i (notVec a) = -diffBool f i a := by
  simp only [diffBool]
  have h1 : f (update (notVec a) i true) = f (update a i false) := by
    rw [← hsym (update a i false), notVec_update]; simp
  have h2 : f (update (notVec a) i false) = f (update a i true) := by
    rw [← hsym (update a i true), notVec_update]; simp
  linarith

end BoolCube

/-! ### Anchored edge-coloring cost and crossing vertex covers -/

section MultigraphCover

variable {V E : Type*} (G : Multigraph V E)

/-- The anchored vertex penalty at `v`: `0` when every incident edge carries the bit `b v`,
and `1` otherwise. -/
noncomputable def vertexPenalty (b : V → Bool) (x : E → Bool) (v : V) : ℕ :=
  open Classical in
  if ∀ e : E, e ∈ G.incidenceSet v → x e = b v then 0 else 1

/-- Total anchored cut cost `Q_b(x) = ∑ v, vertexPenalty G b x v`. -/
@[expose] noncomputable def anchoredCost [Fintype V] (b : V → Bool) (x : E → Bool) : ℕ :=
  ∑ v : V, vertexPenalty G b x v

/-- The unanchored vertex split penalty at `v`: `1` iff incident edges disagree in `x`. -/
@[expose] noncomputable def edgeSplit (x : E → Bool) (v : V) : ℕ :=
  open Classical in
  if (∀ e : E, e ∈ G.incidenceSet v → x e = false) ∨
      (∀ e : E, e ∈ G.incidenceSet v → x e = true) then 0 else 1

/-- Total unanchored vertex-split cost `C(x) = ∑ v, edgeSplit G x v`. -/
@[expose] noncomputable def splitCost [Fintype V] (x : E → Bool) : ℕ :=
  ∑ v : V, edgeSplit G x v

theorem vertexPenalty_of_forall {b : V → Bool} {x : E → Bool} {v : V}
    (h : ∀ e : E, e ∈ G.incidenceSet v → x e = b v) :
    vertexPenalty G b x v = 0 := by
  simp only [vertexPenalty]; split_ifs; rfl

theorem vertexPenalty_of_not_forall {b : V → Bool} {x : E → Bool} {v : V}
    (h : ¬∀ e : E, e ∈ G.incidenceSet v → x e = b v) :
    vertexPenalty G b x v = 1 := by
  simp only [vertexPenalty]; split_ifs; rfl

theorem edgeSplit_of_all_eq {x : E → Bool} {v : V}
    (h : (∀ e : E, e ∈ G.incidenceSet v → x e = false) ∨
      (∀ e : E, e ∈ G.incidenceSet v → x e = true)) :
    edgeSplit G x v = 0 := by
  simp only [edgeSplit]; split_ifs; rfl

theorem edgeSplit_le_vertexPenalty (b : V → Bool) (x : E → Bool) (v : V) :
    edgeSplit G x v ≤ vertexPenalty G b x v := by
  by_cases h2 : ∀ e : E, e ∈ G.incidenceSet v → x e = b v
  · rw [edgeSplit_of_all_eq G (by
      cases hb : b v
      · exact Or.inl fun e he => (h2 e he).trans hb
      · exact Or.inr fun e he => (h2 e he).trans hb)]
    exact Nat.zero_le _
  · rw [vertexPenalty_of_not_forall G h2]
    simp only [edgeSplit]; split_ifs <;> omega

theorem splitCost_le_anchoredCost [Fintype V] (b : V → Bool) (x : E → Bool) :
    splitCost G x ≤ anchoredCost G b x :=
  Finset.sum_le_sum fun v _ => edgeSplit_le_vertexPenalty G b x v

theorem vertexPenalty_le_one (b : V → Bool) (x : E → Bool) (v : V) :
    vertexPenalty G b x v ≤ 1 := by
  simp only [vertexPenalty]; split_ifs <;> omega

theorem edgeSplit_le_one (x : E → Bool) (v : V) : edgeSplit G x v ≤ 1 := by
  simp only [edgeSplit]; split_ifs <;> omega

theorem vertexPenalty_notVec (b : V → Bool) (x : E → Bool) (v : V) :
    vertexPenalty G (notVec b) (notVec x) v = vertexPenalty G b x v := by
  have hiff : (∀ e : E, e ∈ G.incidenceSet v → notVec x e = notVec b v) ↔
      (∀ e : E, e ∈ G.incidenceSet v → x e = b v) :=
    forall₂_congr fun e _ => by
      simp only [notVec_apply]; cases x e <;> cases b v <;> decide
  by_cases h : ∀ e : E, e ∈ G.incidenceSet v → x e = b v
  · rw [vertexPenalty_of_forall G (hiff.mpr h), vertexPenalty_of_forall G h]
  · rw [vertexPenalty_of_not_forall G (fun h' => h (hiff.mp h')), vertexPenalty_of_not_forall G h]

theorem anchoredCost_notVec [Fintype V] (b : V → Bool) (x : E → Bool) :
    anchoredCost G (notVec b) (notVec x) = anchoredCost G b x :=
  Finset.sum_congr rfl fun v _ => vertexPenalty_notVec G b x v

/-- Single-vertex joint submodularity of `vertexPenalty`. -/
theorem vertexPenalty_submodular (b c : V → Bool) (x y : E → Bool) (v : V) :
    vertexPenalty G (b ⊓ c) (x ⊓ y) v + vertexPenalty G (b ⊔ c) (x ⊔ y) v ≤
      vertexPenalty G b x v + vertexPenalty G c y v := by
  by_cases hbx : ∀ e, e ∈ G.incidenceSet v → x e = b v
  · rw [vertexPenalty_of_forall G hbx, zero_add]
    cases hb : b v
    · rw [vertexPenalty_of_forall G fun e he => by simp [hb, hbx e he], zero_add]
      by_cases hcy : ∀ e, e ∈ G.incidenceSet v → y e = c v
      · rw [vertexPenalty_of_forall G hcy, vertexPenalty_of_forall G fun e he => by
          simp [hb, hbx e he, hcy e he]]
      · rw [vertexPenalty_of_not_forall G hcy]; exact vertexPenalty_le_one G _ _ _
    · rw [vertexPenalty_of_forall G (x := x ⊔ y) (b := b ⊔ c) fun e he => by simp [hb, hbx e he],
        add_zero]
      by_cases hcy : ∀ e, e ∈ G.incidenceSet v → y e = c v
      · rw [vertexPenalty_of_forall G hcy, vertexPenalty_of_forall G fun e he => by
          simp [hb, hbx e he, hcy e he]]
      · rw [vertexPenalty_of_not_forall G hcy]; exact vertexPenalty_le_one G _ _ _
  · rw [vertexPenalty_of_not_forall G hbx]
    by_cases hcy : ∀ e, e ∈ G.incidenceSet v → y e = c v
    · rw [vertexPenalty_of_forall G hcy, add_zero]
      cases hc : c v
      · rw [vertexPenalty_of_forall G fun e he => by simp [hc, hcy e he], zero_add]
        exact vertexPenalty_le_one G _ _ _
      · rw [vertexPenalty_of_forall G (x := x ⊔ y) (b := b ⊔ c) fun e he => by simp [hc, hcy e he],
          add_zero]
        exact vertexPenalty_le_one G _ _ _
    · rw [vertexPenalty_of_not_forall G hcy]
      have := vertexPenalty_le_one G (b ⊓ c) (x ⊓ y) v
      have := vertexPenalty_le_one G (b ⊔ c) (x ⊔ y) v
      omega

/-- Joint submodularity of `anchoredCost` in `(b, x)`. -/
theorem anchoredCost_submodular [Fintype V] (b c : V → Bool) (x y : E → Bool) :
    anchoredCost G (b ⊓ c) (x ⊓ y) + anchoredCost G (b ⊔ c) (x ⊔ y) ≤
      anchoredCost G b x + anchoredCost G c y := by
  simp only [anchoredCost, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun v _ => vertexPenalty_submodular G b c x y v

/-- Updating a single vertex anchor bit changes `anchoredCost` by at most `1`. -/
theorem anchoredCost_update_le [Fintype V] [DecidableEq V] (b : V → Bool) (x : E → Bool)
    (v : V) (t : Bool) :
    anchoredCost G (update b v t) x ≤ anchoredCost G b x + 1 := by
  simp only [anchoredCost]
  have hne : ∀ w ∈ (univ.erase v),
      vertexPenalty G (update b v t) x w = vertexPenalty G b x w := fun w hw => by
    have hneq : w ≠ v := (mem_erase.mp hw).1
    by_cases h : ∀ e : E, e ∈ G.incidenceSet w → x e = b w
    · rw [vertexPenalty_of_forall G h, vertexPenalty_of_forall G fun e he => by
        rw [update_of_ne hneq]; exact h e he]
    · rw [vertexPenalty_of_not_forall G h, vertexPenalty_of_not_forall G fun h' => h fun e he => by
        have := h' e he; rwa [update_of_ne hneq] at this]
  have hsum_eq : ∑ w ∈ univ.erase v, vertexPenalty G (update b v t) x w =
      ∑ w ∈ univ.erase v, vertexPenalty G b x w := sum_congr rfl hne
  rw [← add_sum_erase _ _ (mem_univ v), ← add_sum_erase _ _ (mem_univ v), hsum_eq]
  have h1 := vertexPenalty_le_one G (update b v t) x v
  omega

/-- An edge coloring `x` is **clamped** at `b` if every edge between equal-bit endpoints carries
that common bit: `b (src e) ∧ b (tgt e) ≤ x e ≤ b (src e) ∨ b (tgt e)`. -/
def IsClamped (b : V → Bool) (x : E → Bool) : Prop :=
  ∀ e : E, (b (G.src e) && b (G.tgt e)) ≤ x e ∧ x e ≤ (b (G.src e) || b (G.tgt e))

theorem isClamped_iff_eq (b : V → Bool) (x : E → Bool) :
    IsClamped G b x ↔ ∀ e : E, b (G.src e) = b (G.tgt e) → x e = b (G.src e) := by
  constructor
  · intro hx e heq
    obtain ⟨hlo, hhi⟩ := hx e
    rw [heq] at hlo hhi ⊢
    exact le_antisymm (hhi.trans (by cases b (G.tgt e) <;> decide))
      ((by cases b (G.tgt e) <;> decide : b (G.tgt e) ≤ _).trans hlo)
  · intro h e
    by_cases heq : b (G.src e) = b (G.tgt e)
    · have := h e heq
      cases hs : b (G.src e) <;> cases ht : b (G.tgt e) <;> cases hx' : x e <;> simp_all
    · cases hs : b (G.src e) <;> cases ht : b (G.tgt e) <;> cases hx' : x e <;> simp_all

theorem isClamped_notVec {b : V → Bool} {x : E → Bool} (hx : IsClamped G b x) :
    IsClamped G (notVec b) (notVec x) := by
  rw [isClamped_iff_eq] at hx ⊢
  intro e heq
  have heq' : b (G.src e) = b (G.tgt e) := by
    cases h1 : b (G.src e) <;> cases h2 : b (G.tgt e) <;> simp_all [notVec]
  simp [notVec, hx e heq']

theorem isClamped_inf_of_le {b c : V → Bool} (hbc : b ≤ c) {x y : E → Bool}
    (hx : IsClamped G b x) (hy : IsClamped G c y) : IsClamped G b (x ⊓ y) := by
  intro e
  have h1 := hx e; have h2 := hy e
  have hs : b (G.src e) ≤ c (G.src e) := hbc (G.src e)
  have ht : b (G.tgt e) ≤ c (G.tgt e) := hbc (G.tgt e)
  cases hbs : b (G.src e) <;> cases hbt : b (G.tgt e) <;> cases hcs : c (G.src e) <;>
    cases hct : c (G.tgt e) <;> cases hxe : x e <;> cases hye : y e <;> simp_all

theorem isClamped_sup_of_le {b c : V → Bool} (hbc : b ≤ c) {x y : E → Bool}
    (hx : IsClamped G b x) (hy : IsClamped G c y) : IsClamped G c (x ⊔ y) := by
  intro e
  have h1 := hx e; have h2 := hy e
  have hs : b (G.src e) ≤ c (G.src e) := hbc (G.src e)
  have ht : b (G.tgt e) ≤ c (G.tgt e) := hbc (G.tgt e)
  cases hbs : b (G.src e) <;> cases hbt : b (G.tgt e) <;> cases hcs : c (G.src e) <;>
    cases hct : c (G.tgt e) <;> cases hxe : x e <;> cases hye : y e <;> simp_all

/-- Updating one edge `e` joining equal-bit vertices to their common bit does not increase
`anchoredCost G b`. -/
theorem anchoredCost_update_same_le [Fintype V] [DecidableEq E] (b : V → Bool) (x : E → Bool)
    (e : E) (he : b (G.src e) = b (G.tgt e)) :
    anchoredCost G b (update x e (b (G.src e))) ≤ anchoredCost G b x := by
  refine Finset.sum_le_sum fun v _ => ?_
  by_cases h2 : ∀ e' : E, e' ∈ G.incidenceSet v → x e' = b v
  · rw [vertexPenalty_of_forall G h2, vertexPenalty_of_forall G]
    intro e' he'
    by_cases hee : e' = e
    · subst hee
      rcases he' with rfl | rfl <;> simp [he]
    · rw [update_of_ne hee]; exact h2 e' he'
  · rw [vertexPenalty_of_not_forall G h2]; exact vertexPenalty_le_one G _ _ _

/-- A `Finset V` is a **crossing vertex cover** for bipartition `b` if it meets every edge whose
endpoints have opposite `b`-labels. -/
@[expose] def IsCrossingCover (b : V → Bool) (C : Finset V) : Prop :=
  ∀ e : E, b (G.src e) ≠ b (G.tgt e) → G.src e ∈ C ∨ G.tgt e ∈ C

theorem isCrossingCover_univ [Fintype V] (b : V → Bool) : IsCrossingCover G b univ :=
  fun _ _ => Or.inl (mem_univ _)

/-- Minimum vertex-cover cardinality `τ(D_b)` of the crossing graph of `G` at bipartition `b`. -/
@[expose] noncomputable def crossingCover (b : V → Bool) : ℕ :=
  sInf {k : ℕ | ∃ C : Finset V, IsCrossingCover G b C ∧ C.card = k}

private theorem crossingCover_set_nonempty [Finite V] (b : V → Bool) :
    {k : ℕ | ∃ C : Finset V, IsCrossingCover G b C ∧ C.card = k}.Nonempty := by
  have := Fintype.ofFinite V
  exact ⟨univ.card, univ, isCrossingCover_univ G b, rfl⟩

theorem crossingCover_le_card {b : V → Bool} {C : Finset V} (hC : IsCrossingCover G b C) :
    crossingCover G b ≤ C.card :=
  Nat.sInf_le ⟨C, hC, rfl⟩

theorem exists_minCrossingCover [Finite V] (b : V → Bool) :
    ∃ C : Finset V, IsCrossingCover G b C ∧ C.card = crossingCover G b :=
  Nat.sInf_mem (crossingCover_set_nonempty G b)

/-- The vertices penalized by `(b, x)` form a crossing vertex cover, so `τ(D_b) ≤ Q_b(x)`. -/
theorem crossingCover_le_anchoredCost [Fintype V] (b : V → Bool) (x : E → Bool) :
    crossingCover G b ≤ anchoredCost G b x := by
  classical
  let C : Finset V := univ.filter fun v => vertexPenalty G b x v = 1
  have hcov : IsCrossingCover G b C := by
    intro e hne
    by_contra h
    have hnot : G.src e ∉ C ∧ G.tgt e ∉ C := not_or.mp h
    have hpen_eq : ∀ v : V, v ∉ C → ∀ e' : E, e' ∈ G.incidenceSet v → x e' = b v := by
      intro v hv
      by_contra h'
      exact hv (mem_filter.mpr ⟨mem_univ v, vertexPenalty_of_not_forall G h'⟩)
    exact hne ((hpen_eq _ hnot.1 e (Or.inl rfl)).symm.trans (hpen_eq _ hnot.2 e (Or.inr rfl)))
  calc crossingCover G b ≤ C.card := crossingCover_le_card G hcov
    _ = ∑ v : V, vertexPenalty G b x v := by
        rw [card_filter]
        refine Finset.sum_congr rfl fun v _ => ?_
        by_cases hv : ∀ e : E, e ∈ G.incidenceSet v → x e = b v
        · rw [vertexPenalty_of_forall G hv]; simp
        · rw [vertexPenalty_of_not_forall G hv]; simp

/-- Every crossing cover induces a clamped edge coloring with anchored cost at most `|C|`. -/
theorem exists_clamped_of_crossingCover [Fintype V] {b : V → Bool} {C : Finset V}
    (hC : IsCrossingCover G b C) :
    ∃ x : E → Bool, IsClamped G b x ∧ anchoredCost G b x ≤ C.card := by
  classical
  let x : E → Bool := fun e =>
    if G.src e ∉ C then b (G.src e)
    else if G.tgt e ∉ C then b (G.tgt e)
    else b (G.src e)
  refine ⟨x, ?_, ?_⟩
  · rw [isClamped_iff_eq]
    intro e heq
    dsimp [x]; split_ifs <;> simp [heq]
  · calc anchoredCost G b x
        ≤ ∑ v : V, if v ∈ C then 1 else 0 := by
          refine Finset.sum_le_sum fun v _ => ?_
          by_cases hv : v ∈ C
          · simp [hv, vertexPenalty_le_one]
          · simp only [hv, ↓reduceIte, vertexPenalty]
            split_ifs with h
            · exact le_rfl
            · exfalso; apply h; intro e he
              rcases he with rfl | rfl
              · simp [x, hv]
              · by_cases hs : G.src e ∈ C
                · simp [x, hs, hv]
                · simp only [x, hs]
                  by_contra hne
                  rcases hC e hne with h1 | h2
                  · exact hs h1
                  · exact hv h2
      _ = C.card := by rw [← Finset.card_filter]; simp

/-- Minimum crossing-cover size is attained by a clamped edge coloring. -/
theorem exists_clamped_minimizer [Fintype V] (b : V → Bool) :
    ∃ x : E → Bool, IsClamped G b x ∧ anchoredCost G b x = crossingCover G b := by
  obtain ⟨C, hC, hcard⟩ := exists_minCrossingCover G b
  obtain ⟨x, hx, hle⟩ := exists_clamped_of_crossingCover G hC
  exact ⟨x, hx, le_antisymm (hle.trans_eq hcard) (crossingCover_le_anchoredCost G b x)⟩

theorem crossingCover_notVec [Finite V] (b : V → Bool) :
    crossingCover G (notVec b) = crossingCover G b := by
  have := Fintype.ofFinite V
  apply le_antisymm
  · obtain ⟨x, _, hx⟩ := exists_clamped_minimizer G b
    calc crossingCover G (notVec b) ≤ anchoredCost G (notVec b) (notVec x) :=
          crossingCover_le_anchoredCost G _ _
      _ = anchoredCost G b x := anchoredCost_notVec G b x
      _ = crossingCover G b := hx
  · obtain ⟨x, _, hx⟩ := exists_clamped_minimizer G (notVec b)
    calc crossingCover G b ≤ anchoredCost G b (notVec x) :=
          crossingCover_le_anchoredCost G _ _
      _ = anchoredCost G (notVec b) x := by
          have := anchoredCost_notVec G (notVec b) x
          rw [notVec_notVec] at this
          exact this
      _ = crossingCover G (notVec b) := hx

/-- `crossingCover G` is submodular on `V → Bool`. -/
theorem crossingCover_submodular [Finite V] (b c : V → Bool) :
    crossingCover G (b ⊓ c) + crossingCover G (b ⊔ c) ≤
      crossingCover G b + crossingCover G c := by
  have := Fintype.ofFinite V
  obtain ⟨x, _, hx⟩ := exists_clamped_minimizer G b
  obtain ⟨y, _, hy⟩ := exists_clamped_minimizer G c
  calc crossingCover G (b ⊓ c) + crossingCover G (b ⊔ c)
      ≤ anchoredCost G (b ⊓ c) (x ⊓ y) + anchoredCost G (b ⊔ c) (x ⊔ y) :=
        Nat.add_le_add (crossingCover_le_anchoredCost G _ _) (crossingCover_le_anchoredCost G _ _)
    _ ≤ anchoredCost G b x + anchoredCost G c y := anchoredCost_submodular G b c x y
    _ = crossingCover G b + crossingCover G c := by rw [hx, hy]

theorem isSubmodularBool_crossingCover [Finite V] :
    IsSubmodularBool (fun b : V → Bool => (crossingCover G b : ℝ)) := fun b c => by
  change ((crossingCover G (b ⊓ c) : ℝ) + crossingCover G (b ⊔ c)) ≤
    crossingCover G b + crossingCover G c
  norm_cast
  exact crossingCover_submodular G b c

theorem isSymmetricBool_crossingCover [Finite V] :
    IsSymmetricBool (fun b : V → Bool => (crossingCover G b : ℝ)) := fun b =>
  congrArg Nat.cast (crossingCover_notVec G b)

theorem crossingCover_const (t : Bool) : crossingCover G (fun _ => t) = 0 := by
  have hcov : IsCrossingCover G (fun _ => t) ∅ := fun _ hne => (hne rfl).elim
  exact Nat.eq_zero_of_le_zero ((crossingCover_le_card G hcov).trans_eq card_empty)

/-- Flipping one vertex label changes `crossingCover` by at most `1`. -/
theorem crossingCover_update_le [Finite V] [DecidableEq V] (b : V → Bool) (v : V) (t : Bool) :
    crossingCover G (update b v t) ≤ crossingCover G b + 1 := by
  have := Fintype.ofFinite V
  obtain ⟨x, _, hx⟩ := exists_clamped_minimizer G b
  calc crossingCover G (update b v t)
      ≤ anchoredCost G (update b v t) x := crossingCover_le_anchoredCost G _ _
    _ ≤ anchoredCost G b x + 1 := anchoredCost_update_le G b x v t
    _ = crossingCover G b + 1 := by rw [hx]

/-- Absolute difference between `crossingCover G b` and `crossingCover G c` is bounded by their
Hamming distance. -/
theorem crossingCover_sub_le_hamming [Fintype V] (b c : V → Bool) :
    crossingCover G c ≤ crossingCover G b + (univ.filter fun v => b v ≠ c v).card := by
  classical
  have hgen : ∀ (S : Finset V) (b c : V → Bool),
      (∀ v, b v ≠ c v → v ∈ S) → crossingCover G c ≤ crossingCover G b + S.card := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro b c h
      have hbc : b = c := funext fun v => by_contra fun hne => notMem_empty v (h v hne)
      subst hbc; simp
    | @insert v S hv ih =>
      intro b c h
      have h' : ∀ w, update b v (c v) w ≠ c w → w ∈ S := by
        intro w hw
        by_cases hwv : w = v
        · subst hwv; simp at hw
        · rw [update_of_ne hwv] at hw
          exact (mem_insert.mp (h w hw)).resolve_left hwv
      have hstep := crossingCover_update_le G b v (c v)
      have hih := ih (update b v (c v)) c h'
      rw [card_insert_of_notMem hv]; omega
  exact hgen _ b c fun v hv => mem_filter.mpr ⟨mem_univ v, hv⟩

/-- Clamped optimal edge colorings are closed under `⊓` and `⊔` when `b ≤ c`. -/
private theorem clampedMinimizer_inf_sup [Fintype V] {b c : V → Bool} (hbc : b ≤ c)
    {x y : E → Bool}
    (hxm : anchoredCost G b x = crossingCover G b)
    (hym : anchoredCost G c y = crossingCover G c) :
    anchoredCost G b (x ⊓ y) = crossingCover G b ∧
      anchoredCost G c (x ⊔ y) = crossingCover G c := by
  have hsub := anchoredCost_submodular G b c x y
  rw [inf_of_le_left hbc, sup_of_le_right hbc, hxm, hym] at hsub
  have hlo1 := crossingCover_le_anchoredCost G b (x ⊓ y)
  have hlo2 := crossingCover_le_anchoredCost G c (x ⊔ y)
  omega

/-- The **least clamped minimizer** of `anchoredCost G b`: pointwise AND of all clamped
minimizers. -/
@[expose] noncomputable def leastClampedMinimizer [Fintype V] (b : V → Bool) : E → Bool :=
  open Classical in
  fun e => decide (∀ x : E → Bool, IsClamped G b x →
    anchoredCost G b x = crossingCover G b → x e = true)

private noncomputable def finsetInfEdge (S : Finset (E → Bool)) : E → Bool :=
  open Classical in fun e => decide (∀ x ∈ S, x e = true)

private theorem isClamped_minimizer_finset_inf [Fintype V] (b : V → Bool)
    (S : Finset (E → Bool)) (hS : S.Nonempty)
    (hm : ∀ x ∈ S, IsClamped G b x ∧ anchoredCost G b x = crossingCover G b) :
    IsClamped G b (finsetInfEdge S) ∧ anchoredCost G b (finsetInfEdge S) = crossingCover G b := by
  classical
  induction S using Finset.induction_on with
  | empty => exact absurd hS not_nonempty_empty
  | @insert x T _ ih =>
    rcases T.eq_empty_or_nonempty with rfl | hT
    · have hxeq : finsetInfEdge (insert x ∅) = x := by
        ext e; simp [finsetInfEdge]
      rw [hxeq]; exact hm x (mem_insert_self x ∅)
    · have ih' := ih hT fun y hy => hm y (mem_insert_of_mem hy)
      have hx := hm x (mem_insert_self x T)
      have hfn : finsetInfEdge (insert x T) = x ⊓ finsetInfEdge T := by
        ext e; simp [finsetInfEdge]
      rw [hfn]
      exact ⟨isClamped_inf_of_le G le_rfl hx.1 ih'.1,
        (clampedMinimizer_inf_sup G le_rfl hx.2 ih'.2).1⟩

theorem isClamped_leastClampedMinimizer [Fintype V] [Finite E] (b : V → Bool) :
    IsClamped G b (leastClampedMinimizer G b) := by
  classical
  have := Fintype.ofFinite E
  let S : Finset (E → Bool) := univ.filter fun x =>
    IsClamped G b x ∧ anchoredCost G b x = crossingCover G b
  have hS : S.Nonempty := by
    obtain ⟨x, hx, hxm⟩ := exists_clamped_minimizer G b
    exact ⟨x, mem_filter.mpr ⟨mem_univ x, hx, hxm⟩⟩
  have heq : leastClampedMinimizer G b = finsetInfEdge S := by
    ext e; simp [leastClampedMinimizer, finsetInfEdge, S]
  rw [heq]
  exact (isClamped_minimizer_finset_inf G b S hS fun x hx => (mem_filter.mp hx).2).1

theorem anchoredCost_leastClampedMinimizer [Fintype V] [Finite E] (b : V → Bool) :
    anchoredCost G b (leastClampedMinimizer G b) = crossingCover G b := by
  classical
  have := Fintype.ofFinite E
  let S : Finset (E → Bool) := univ.filter fun x =>
    IsClamped G b x ∧ anchoredCost G b x = crossingCover G b
  have hS : S.Nonempty := by
    obtain ⟨x, hx, hxm⟩ := exists_clamped_minimizer G b
    exact ⟨x, mem_filter.mpr ⟨mem_univ x, hx, hxm⟩⟩
  have heq : leastClampedMinimizer G b = finsetInfEdge S := by
    ext e; simp [leastClampedMinimizer, finsetInfEdge, S]
  rw [heq]
  exact (isClamped_minimizer_finset_inf G b S hS fun x hx => (mem_filter.mp hx).2).2

theorem leastClampedMinimizer_le [Fintype V] {b : V → Bool} {x : E → Bool}
    (hx : IsClamped G b x) (hxm : anchoredCost G b x = crossingCover G b) :
    leastClampedMinimizer G b ≤ x := by
  intro e
  cases hl : leastClampedMinimizer G b e
  · exact Bool.false_le _
  · simp only [leastClampedMinimizer, decide_eq_true_eq] at hl
    exact (hl x hx hxm).symm ▸ le_rfl

/-- **Monotonicity of the canonical crossing-cover edge coloring.** Whenever `b ≤ c`,
`leastClampedMinimizer G b ≤ leastClampedMinimizer G c`. -/
theorem leastClampedMinimizer_mono [Fintype V] [Finite E] :
    Monotone (leastClampedMinimizer G) := by
  intro b c hbc
  have hx := isClamped_leastClampedMinimizer G b
  have hxm := anchoredCost_leastClampedMinimizer G b
  have hy := isClamped_leastClampedMinimizer G c
  have hym := anchoredCost_leastClampedMinimizer G c
  have hinf := isClamped_inf_of_le G hbc hx hy
  have hinfm := (clampedMinimizer_inf_sup G hbc hxm hym).1
  have hle := leastClampedMinimizer_le G hinf hinfm
  exact fun e => le_trans (hle e) inf_le_right

theorem leastClampedMinimizer_const [Fintype V] [Finite E] (t : Bool) :
    leastClampedMinimizer G (fun _ => t) = fun _ => t := by
  ext e
  exact (isClamped_iff_eq G (fun _ => t) _).mp (isClamped_leastClampedMinimizer G _) e rfl

end MultigraphCover

end Cslib.Circuits.Frontier.CrossingCover
