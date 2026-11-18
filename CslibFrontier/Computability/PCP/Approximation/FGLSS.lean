/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.PCP
public import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.List.OfFn

/-!
# The FGLSS graph of a PCP verifier

Goldreich [Exercise 9.18][Goldreich2007DraftR5] (after Feige, Goldwasser, Lovász, Safra and
Szegedy) maps an instance `x` of a problem in `PCP(r, q)` to the graph `G_x` whose vertices are
the accepting *views* `(ω, α)` of the verifier on `x`, a random string `ω` and answers `α` to the
queries made with `ω`, and whose edges join mutually inconsistent views: views that give different
answers at the same position of the proof. Independent sets are sets of pairwise consistent views,
which come from a single proof, so the maximum independent set of `G_x` has size
`2 ^ r · max_π Pr[V^π(x) = 1]`.

This module states the graph for the nonadaptive verifiers `Cslib.Complexity.PCPVerifier` (the
queries depend only on the instance and the random string) and proves items 2–4 of the exercise
and its general identity:

* `Cslib.Complexity.PCPVerifier.exists_acceptCount_eq_indepNum_fglssGraph`,
  `Cslib.Complexity.PCPVerifier.acceptCount_le_indepNum_fglssGraph`: the independence number of
  `G_x` is the largest number of random strings accepted with a single proof;
* `Cslib.Complexity.PCPVerifier.indepNum_fglssGraph_le`: it is at most `2 ^ r` (item 2);
* `Cslib.Complexity.IsPCPVerifier.indepNum_fglssGraph_eq_of_mem`: it is `2 ^ r` on members
  (item 3);
* `Cslib.Complexity.IsPCPVerifier.two_mul_indepNum_fglssGraph_le_of_not_mem`: it is at most
  `2 ^ (r - 1)`, stated as `2 · α(G_x) ≤ 2 ^ r`, on non-members (item 4).

Here `r` is the number `V.coins x` of random bits the verifier uses on `x`.

This is a step toward the exercise, not all of it. Item 1 (computing `x ↦ G_x` in time polynomial
in `2 ^ (r + q) |x|`) and the consequence that the PCP Theorem makes Independent Set and Clique
NP-hard to approximate within every constant factor are not proved here.

A view whose queries repeat a position with different answers is inconsistent with itself. The
exercise states the conflict condition without discussing repeated queries; read literally, the
rule joins such a view to itself, so it lies in no independent set. Simple graphs have no loops,
so this interpretation of the rule is implemented by leaving such views out of the vertex set
(`Cslib.Complexity.PCPVerifier.IsFGLSSVertex`), which leaves the independent sets unchanged.

## Main definitions

* `Cslib.Complexity.PCPVerifier.View`, `Cslib.Complexity.PCPVerifier.View.Consistent`: views and
  their consistency.
* `Cslib.Complexity.PCPVerifier.fglssGraph`: the FGLSS graph `G_x`.

## References

* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*][Goldreich2007DraftR5],
  Exercise 9.18
-/

public section

namespace Cslib.Complexity

open Finset

variable {α : Type}

namespace PCPVerifier

variable (V : PCPVerifier α) (a : α)

/-- A view of the verifier `V` on the instance `a`: a random string of `V.coins a` bits and
answers to the queries made with it. -/
structure View where
  /-- The random string. -/
  random : Fin (V.coins a) → Bool
  /-- The answers to the queries `V.queries (a, random)`, in order. -/
  answers : Fin (V.queries (a, List.ofFn random)).length → Bool

variable {V a}

instance : Finite (V.View a) :=
  Finite.of_injective (fun v => (⟨v.random, v.answers⟩ :
      Σ ρ : Fin (V.coins a) → Bool, Fin (V.queries (a, List.ofFn ρ)).length → Bool))
    fun ⟨_, _⟩ ⟨_, _⟩ h => by
      obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.1 h
      cases h
      rfl

/-- Two views are consistent when they give the same answer whenever they query the same
position. -/
def View.Consistent (v w : V.View a) : Prop :=
  ∀ (i : Fin (V.queries (a, List.ofFn v.random)).length)
    (j : Fin (V.queries (a, List.ofFn w.random)).length),
    (V.queries (a, List.ofFn v.random))[i] = (V.queries (a, List.ofFn w.random))[j] →
      v.answers i = w.answers j

/-- Consistent views agree at every position they both query. -/
theorem View.Consistent.eq {v w : V.View a} (h : v.Consistent w)
    {i : Fin (V.queries (a, List.ofFn v.random)).length}
    {j : Fin (V.queries (a, List.ofFn w.random)).length}
    (hij : (V.queries (a, List.ofFn v.random))[i] = (V.queries (a, List.ofFn w.random))[j]) :
    v.answers i = w.answers j :=
  h i j hij

theorem View.Consistent.symm {v w : V.View a} (h : v.Consistent w) : w.Consistent v :=
  fun i j hij => (h j i hij.symm).symm

variable (V a)

/-- The vertices of the FGLSS graph: the views on which `V` accepts and which are consistent with
themselves. -/
structure IsFGLSSVertex (v : V.View a) : Prop where
  /-- `V` accepts the view. -/
  accepts : V.verdict ((a, List.ofFn v.random), List.ofFn v.answers) = true
  /-- The view answers every repeated query in the same way. -/
  consistent : v.Consistent v

/-- **The FGLSS graph** [Goldreich, Exercise 9.18][Goldreich2007DraftR5] of the verifier `V` on
the instance `a`: the accepting self-consistent views, two of them adjacent when they are
inconsistent. A vertex is consistent with itself, so the graph has no loops. -/
def fglssGraph : SimpleGraph {v : V.View a // V.IsFGLSSVertex a v} where
  Adj v w := ¬v.1.Consistent w.1
  symm := ⟨fun _ _ h hc => h hc.symm⟩
  loopless := ⟨fun v h => h v.property.consistent⟩

variable {V a}

/-- The view of `V` with the random string `ρ` that reads its answers from the proof `π`. -/
private def proofView (π : List Bool) (ρ : Fin (V.coins a) → Bool) : V.View a :=
  ⟨ρ, fun i => π.getD (V.queries (a, List.ofFn ρ))[i] false⟩

private theorem ofFn_proofView (π : List Bool) (ρ : Fin (V.coins a) → Bool) :
    List.ofFn (proofView (V := V) (a := a) π ρ).answers =
      answers π (V.queries (a, List.ofFn ρ)) := by
  simp only [proofView, answers]
  simpa only [Fin.getElem_fin] using
    List.ofFn_getElem_eq_map (V.queries (a, List.ofFn ρ)) fun p => π.getD p false

private theorem consistent_proofView (π : List Bool) (ρ ρ' : Fin (V.coins a) → Bool) :
    (proofView (V := V) (a := a) π ρ).Consistent (proofView π ρ') := fun i j h => by
  simp only [proofView] at h ⊢
  rw [h]

/-- **Every proof gives an independent set.** The views read from a proof `π` on the random
strings it makes `V` accept form an independent set of the FGLSS graph, so the number of these
random strings is at most its independence number. -/
theorem acceptCount_le_indepNum_fglssGraph (π : List Bool) :
    acceptCount (fun x => V.accepts x.1 π x.2) a (V.coins a) ≤ (V.fglssGraph a).indepNum := by
  classical
  set R := univ.filter fun ρ : Fin (V.coins a) → Bool => V.accepts a π (List.ofFn ρ) = true
  have hvert (ρ : R) : V.IsFGLSSVertex a (proofView π ρ.1) := by
    refine ⟨?_, consistent_proofView π _ _⟩
    rw [ofFn_proofView]
    exact (mem_filter.1 ρ.2).2
  let e : R ↪ {v : V.View a // V.IsFGLSSVertex a v} :=
    ⟨fun ρ => ⟨proofView π ρ.1, hvert ρ⟩, fun ρ ρ' h => by
      have h := congrArg (fun v => v.1.random) h
      exact Subtype.ext h⟩
  have hind : (V.fglssGraph a).IsIndepSet (univ.map e : Finset _) := by
    intro v _ w _ hvw hadj
    obtain ⟨ρ, -, rfl⟩ := mem_map.1 ‹v ∈ _›
    obtain ⟨ρ', -, rfl⟩ := mem_map.1 ‹w ∈ _›
    exact hadj (consistent_proofView π _ _)
  have h := hind.card_le_indepNum
  rwa [card_map, card_univ, Fintype.card_coe] at h

/-- **An independent set gives a proof.** For every set `S` of pairwise consistent views, the
proof that answers every position as the views of `S` do makes `V` accept on the random strings of
`S`, which are distinct. -/
private theorem exists_card_le_acceptCount {S : Finset {v : V.View a // V.IsFGLSSVertex a v}}
    (hS : (V.fglssGraph a).IsIndepSet S) :
    ∃ π : List Bool, #S ≤ acceptCount (fun x => V.accepts x.1 π x.2) a (V.coins a) := by
  classical
  -- views of `S` are pairwise consistent
  have hcons {v w} (hv : v ∈ S) (hw : w ∈ S) : v.1.Consistent w.1 := by
    by_cases hvw : v = w
    · subst hvw
      exact v.property.consistent
    · by_contra h
      exact hS hv hw hvw h
  -- a bound on the queried positions
  set N := (S.sup fun v => (V.queries (a, List.ofFn v.1.random)).sum) + 1
  have hpos {v} (hv : v ∈ S) (i : Fin (V.queries (a, List.ofFn v.1.random)).length) :
      (V.queries (a, List.ofFn v.1.random))[i] < N := by
    have h₁ : (V.queries (a, List.ofFn v.1.random))[i] ≤
        (V.queries (a, List.ofFn v.1.random)).sum :=
      List.le_sum_of_mem (by rw [Fin.getElem_fin]; exact List.getElem_mem _)
    have h₂ := le_sup (f := fun v => (V.queries (a, List.ofFn v.1.random)).sum) hv
    omega
  let π : List Bool := List.ofFn fun p : Fin N =>
    decide (∃ w ∈ S, ∃ j : Fin (V.queries (a, List.ofFn w.1.random)).length,
      (V.queries (a, List.ofFn w.1.random))[j] = p ∧ w.1.answers j = true)
  have hread {v} (hv : v ∈ S) (i : Fin (V.queries (a, List.ofFn v.1.random)).length) :
      π.getD (V.queries (a, List.ofFn v.1.random))[i] false = v.1.answers i := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem
      (by simp only [π, List.length_ofFn]; exact hpos hv i),
      Option.getD_some]
    simp only [π, List.getElem_ofFn]
    refine Bool.eq_iff_iff.2 ?_
    rw [decide_eq_true_iff]
    constructor
    · rintro ⟨w, hw, j, hj, hwj⟩
      rw [← hwj]
      exact hcons hv hw i j hj.symm
    · intro h
      exact ⟨v, hv, i, rfl, h⟩
  have hacc {v} (hv : v ∈ S) : V.accepts a π (List.ofFn v.1.random) = true := by
    have h := v.property.accepts
    have hans : answers π (V.queries (a, List.ofFn v.1.random)) = List.ofFn v.1.answers := by
      rw [← ofFn_proofView]
      congr 1
      funext i
      exact hread hv i
    rw [accepts, hans]
    exact h
  refine ⟨π, card_le_card_of_injOn (fun v => v.1.random) (fun v hv => ?_) fun v hv w hw h => ?_⟩
  · simpa using hacc hv
  · obtain ⟨⟨ρ, β⟩, hv'⟩ := v
    obtain ⟨⟨ρ', β'⟩, hw'⟩ := w
    dsimp only at h
    subst h
    have hβ : β = β' := funext fun i => hcons hv hw i i rfl
    subst hβ
    rfl

variable (V a) in
/-- **The FGLSS identity** [Goldreich, Exercise 9.18][Goldreich2007DraftR5]: the independence
number of the FGLSS graph is the largest number of random strings on which `V` accepts with a
single proof, `2 ^ r · max_π Pr[V^π(x) = 1]`. Together with
`Cslib.Complexity.PCPVerifier.acceptCount_le_indepNum_fglssGraph`, the maximum is attained. -/
theorem exists_acceptCount_eq_indepNum_fglssGraph :
    ∃ π : List Bool,
      acceptCount (fun x => V.accepts x.1 π x.2) a (V.coins a) = (V.fglssGraph a).indepNum := by
  obtain ⟨S, hS⟩ := (V.fglssGraph a).exists_isNIndepSet_indepNum
  obtain ⟨π, hπ⟩ := exists_card_le_acceptCount hS.isIndepSet
  exact ⟨π, le_antisymm (acceptCount_le_indepNum_fglssGraph π) (hS.card_eq ▸ hπ)⟩

variable (V a) in
/-- **Item 2 of Exercise 9.18**: the independence number of the FGLSS graph is at most `2 ^ r`. -/
theorem indepNum_fglssGraph_le : (V.fglssGraph a).indepNum ≤ 2 ^ V.coins a := by
  obtain ⟨π, hπ⟩ := exists_acceptCount_eq_indepNum_fglssGraph V a
  exact hπ ▸ acceptCount_le_two_pow

end PCPVerifier

namespace IsPCPVerifier

variable {enc : α ↪ List Bool} {r q : ℕ → ℕ} {V : PCPVerifier α} {A : Set α} {a : α}

/-- **Item 3 of Exercise 9.18**: on a member, the FGLSS graph has an independent set of size
`2 ^ r`, so its independence number is `2 ^ r`. -/
theorem indepNum_fglssGraph_eq_of_mem (hV : IsPCPVerifier enc r q V A) (ha : a ∈ A) :
    (V.fglssGraph a).indepNum = 2 ^ V.coins a := by
  refine le_antisymm (V.indepNum_fglssGraph_le a) ?_
  obtain ⟨π, hπ⟩ := hV.complete a ha
  refine le_of_eq_of_le ?_ (PCPVerifier.acceptCount_le_indepNum_fglssGraph π)
  rw [acceptCount, filter_true_of_mem fun ρ _ => hπ _ (List.length_ofFn), card_univ]
  simp

/-- **Item 4 of Exercise 9.18**: on a non-member, the independence number of the FGLSS graph is
at most `2 ^ (r - 1)`, stated as `2 · α(G_x) ≤ 2 ^ r`. -/
theorem two_mul_indepNum_fglssGraph_le_of_not_mem (hV : IsPCPVerifier enc r q V A) (ha : a ∉ A) :
    2 * (V.fglssGraph a).indepNum ≤ 2 ^ V.coins a := by
  obtain ⟨π, hπ⟩ := V.exists_acceptCount_eq_indepNum_fglssGraph a
  exact hπ ▸ hV.sound a ha π

end IsPCPVerifier

end Cslib.Complexity
