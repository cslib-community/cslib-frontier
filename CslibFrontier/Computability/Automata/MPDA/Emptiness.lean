/-
Copyright (c) 2026 Sparsa Roychowdhury. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sparsa Roychowdhury
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Automata.MPDA.WellNested
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Order.FixedPoints
public import CslibFrontier.Foundations.Relation.FiniteClosure
import CslibFrontier.Foundations.Order.FiniteFixedPoint

/-! # Computing well-nested reachability

The emptiness procedure for hole-bounded MPDAs, Algorithm 1 of
[AkshayGastinKrishnaRoychowdhury2020], starts from the set `WR` of pairs of control states joined
by a well-nested run, computed by Algorithm 2 (`WellNestedReach`, Appendix B). This file computes
`WR` for an MPDA with finitely many control states, letters and stack symbols and a decidable
transition relation.

`MPDA.wellNestedPairs M` iterates the closure rules of `MPDA.WellNestedReach` on finite sets of
pairs, as many times as there are pairs. Algorithm 2 alternates a transitive closure with a
push-pop step until nothing changes; any order of applying the rules reaches the same least fixed
point, and the number of iterations is not part of the statements here.

## Main definitions

- `MPDA.wellNestedPairs`: the set `WR` of Algorithm 2, as a computable `Finset`.
- `MPDA.atomicHoles`, `MPDA.holeSegments`: the sets `AHSᵢ` and `HSᵢ` of Algorithm 1.

## Main results

- `MPDA.mem_wellNestedPairs`: `(s, s') ∈ WR` exactly when `MPDA.WellNestedReach M s s'`. With
  `MPDA.wellNestedReach_iff`, this is Lemma 1 of [AkshayGastinKrishnaRoychowdhury2020] for the
  computed set.

## References

* [S. Akshay, P. Gastin, S. Krishna, S. Roychowdhury,
  *Revisiting Underapproximate Reachability for Multipushdown Systems*]
  [AkshayGastinKrishnaRoychowdhury2020]
-/

public section

namespace Cslib.Automata.MPDA

variable {n : ℕ} {State Symbol Γ : Type*}

/-! ## The closure rules of `WR` as a monotone map -/

/-- One application of the closure rules of `WellNestedReach` to a relation `R`: reflexive pairs,
a `nop` transition followed by `R`, and a push followed by `R`, a matching pop and `R`. -/
@[expose] def wellNestedRule (M : MPDA n State Symbol Γ) (R : Set (State × State)) :
    Set (State × State) :=
  {p | p.1 = p.2 ∨ (∃ a s₂, M.Tr p.1 (a, .nop) s₂ ∧ (s₂, p.2) ∈ R) ∨
    ∃ (a b : Symbol) (i : Fin n) (γ : Γ) (s₂ s₃ s₄ : State), M.Tr p.1 (a, .push i γ) s₂ ∧
      (s₂, s₃) ∈ R ∧ M.Tr s₃ (b, .pop i γ) s₄ ∧ (s₄, p.2) ∈ R}

/-- The closure rules of `WellNestedReach` as a monotone map on relations. -/
@[expose] def wellNestedRuleHom (M : MPDA n State Symbol Γ) :
    Set (State × State) →o Set (State × State) where
  toFun := M.wellNestedRule
  monotone' R R' hR p hp := by
    rcases hp with h | ⟨a, s₂, ht, hr⟩ | ⟨a, b, i, γ, s₂, s₃, s₄, h₁, h₂, h₃, h₄⟩
    · exact .inl h
    · exact .inr (.inl ⟨a, s₂, ht, hR hr⟩)
    · exact .inr (.inr ⟨a, b, i, γ, s₂, s₃, s₄, h₁, hR h₂, h₃, hR h₄⟩)

/-- The least fixed point of the closure rules is `WellNestedReach`. -/
theorem lfp_wellNestedRuleHom (M : MPDA n State Symbol Γ) :
    M.wellNestedRuleHom.lfp = {p | M.WellNestedReach p.1 p.2} := by
  apply le_antisymm
  · refine OrderHom.lfp_le _ fun p hp => ?_
    rcases hp with h | ⟨a, s₂, ht, hr⟩ | ⟨a, b, i, γ, s₂, s₃, s₄, h₁, h₂, h₃, h₄⟩
    · obtain ⟨s, s'⟩ := p
      simp only at h
      subst h
      exact .refl s
    · exact .nop ht hr
    · exact .pushPop h₁ h₂ h₃ h₄
  · rintro ⟨s, s'⟩ h
    simp only [Set.mem_ofPred_eq] at h
    induction h with
    | refl s =>
      rw [← OrderHom.map_lfp]
      exact .inl rfl
    | nop ht _ ih =>
      rw [← OrderHom.map_lfp]
      exact .inr (.inl ⟨_, _, ht, ih⟩)
    | pushPop h₁ _ h₃ _ ih ih' =>
      rw [← OrderHom.map_lfp]
      exact .inr (.inr ⟨_, _, _, _, _, _, _, h₁, ih, h₃, ih'⟩)

/-! ## Computing `WR` -/

section Compute

variable [Fintype State] [DecidableEq State] [Fintype Symbol] [Fintype Γ]
  (M : MPDA n State Symbol Γ) [∀ s μ s', Decidable (M.Tr s μ s')]

/-- One application of the closure rules of `WellNestedReach` to a finite relation. -/
@[expose] def wellNestedStep (R : Finset (State × State)) : Finset (State × State) :=
  Finset.univ.filter fun p => p.1 = p.2 ∨ (∃ a s₂, M.Tr p.1 (a, .nop) s₂ ∧ (s₂, p.2) ∈ R) ∨
    ∃ (a b : Symbol) (i : Fin n) (γ : Γ) (s₂ s₃ s₄ : State), M.Tr p.1 (a, .push i γ) s₂ ∧
      (s₂, s₃) ∈ R ∧ M.Tr s₃ (b, .pop i γ) s₄ ∧ (s₄, p.2) ∈ R

/-- The set `WR` of Algorithm 2 of [AkshayGastinKrishnaRoychowdhury2020]: the closure rules of
`WellNestedReach`, iterated from the empty relation once for each pair of control states. -/
@[expose] def wellNestedPairs : Finset (State × State) :=
  (M.wellNestedStep^[Fintype.card (State × State)]) ∅

theorem coe_wellNestedStep (R : Finset (State × State)) :
    (M.wellNestedStep R : Set (State × State)) = M.wellNestedRule R := by
  ext p
  simp [wellNestedStep, wellNestedRule]

theorem coe_iterate_wellNestedStep (k : ℕ) :
    ((M.wellNestedStep^[k] ∅ : Finset (State × State)) : Set (State × State)) =
      (M.wellNestedRuleHom^[k]) ⊥ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', coe_wellNestedStep, ih]
    rfl

/-- **Lemma 1 for the computed set**: `(s, s') ∈ WR` exactly when the MPDA has a well-nested run
from `s` to `s'` (`MPDA.wellNestedReach_iff`). -/
theorem mem_wellNestedPairs {s s' : State} :
    (s, s') ∈ M.wellNestedPairs ↔ M.WellNestedReach s s' := by
  rw [← Finset.mem_coe, wellNestedPairs, coe_iterate_wellNestedStep,
    OrderHom.iterate_card_bot_eq_lfp, lfp_wellNestedRuleHom]
  rfl

end Compute

/-! ## Hole segments -/

section Holes

variable [Fintype State] [DecidableEq State] [Fintype Symbol] [Fintype Γ]
  (M : MPDA n State Symbol Γ) [∀ s μ s', Decidable (M.Tr s μ s')]

/-- The atomic hole segments `AHSᵢ` of stack `i` (Algorithm 1, lines 5–8, of
[AkshayGastinKrishnaRoychowdhury2020]): the triples `(s, α, s')` such that a push of `α` on stack
`i` from `s`, followed by a well-nested run, reaches `s'`. -/
@[expose] def atomicHoles (i : Fin n) : Finset (State × Γ × State) :=
  Finset.univ.filter fun t => ∃ (a : Symbol) (s₁ : State), M.Tr t.1 (a, .push i t.2.1) s₁ ∧
    (s₁, t.2.2) ∈ M.wellNestedPairs

theorem mem_atomicHoles {i : Fin n} {s s' : State} {γ : Γ} :
    (s, γ, s') ∈ M.atomicHoles i ↔
      ∃ (a : Symbol) (s₁ : State), M.Tr s (a, .push i γ) s₁ ∧ M.WellNestedReach s₁ s' := by
  simp [atomicHoles, mem_wellNestedPairs]

/-- An atomic hole segment is a push of `α` on stack `i` followed by a well-nested run. -/
theorem mem_atomicHoles_iff_mTr {i : Fin n} {s s' : State} {γ : Γ} :
    (s, γ, s') ∈ M.atomicHoles i ↔ ∃ (a : Symbol) (w : List (Symbol × Op n Γ)),
      WellNested w ∧ M.MTr s ((a, .push i γ) :: w) s' := by
  rw [mem_atomicHoles]
  constructor
  · rintro ⟨a, s₁, ht, hw⟩
    obtain ⟨w, hw, hrun⟩ := wellNestedReach_iff.mp hw
    exact ⟨a, w, hw, .stepL ht hrun⟩
  · rintro ⟨a, w, hw, hrun⟩
    obtain ⟨s₁, ht, hrun⟩ := LTS.MTr.cons_iff.mp hrun
    exact ⟨a, s₁, ht, wellNestedReach_iff.mpr ⟨w, hw, hrun⟩⟩

/-- The hole segments `HSᵢ` of stack `i` (Algorithm 1, line 9): the reflexive-transitive closure of
the atomic hole segments, forgetting the pushed symbols. The source writes `TransitiveClosure`;
the closure must be reflexive, since `AddPop` (Algorithm 4) splits off the only atomic segment of
a hole through a triple `(i, s, s)`. -/
@[expose] def holeSegments [DecidableEq Γ] (i : Fin n) : Finset (State × State) :=
  Relation.reflTransGenFinset fun s s' => ∃ γ, (s, γ, s') ∈ M.atomicHoles i

theorem mem_holeSegments [DecidableEq Γ] {i : Fin n} {s s' : State} :
    (s, s') ∈ M.holeSegments i ↔
      Relation.ReflTransGen (fun s s' => ∃ γ, (s, γ, s') ∈ M.atomicHoles i) s s' :=
  Relation.mem_reflTransGenFinset _

end Holes

end Cslib.Automata.MPDA
