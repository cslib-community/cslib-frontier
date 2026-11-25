/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser.Elimination

/-!
# Lemma 4.2: one step of gate elimination

**Lemma 4.2** of [Mishra and Santhanam][MishraSanthanam2026]: if `d < a`, a valid state for an
affine disperser for dimension `d` has a step of gate elimination (`State.Valid.exists_step`): a
valid state with smaller `m + s`, `Δa ∈ {0, -1, -2}` and `ΔW ≤ 14 Δa`.

The proof follows Section 4 of the source. Movable affine gates are moved into the affine system
first (`State.Valid.preparation_moveAffine`); then one of the preliminary reductions is a step, or
the state is normal (`State.Valid.step_or_normal`). In a normal state the minimal gate is an
AND-type gate on two distinct inputs among the parameters and auxiliary variables
(`State.Valid.exists_minGate`). An auxiliary input is exchanged with a parameter
(`State.Valid.exists_preparation_auxIn_lt`), a child of the minimal AND reading one of its inputs
is rerouted (`State.Valid.exists_preparation_childIn_lt`), and the analysis restarts; once neither
applies, eliminating the minimal AND is a step (`State.Valid.step_of_minimalAnd`). The preparatory
operations keep `m`, `s` and `a` and do not increase `W`, and they terminate since each lowers,
in lexicographic order, the number of gates, the number of auxiliary inputs of the minimal gate
(`State.auxIn`) and the number of its children reading one of its parameter inputs
(`State.childIn`). The proof establishes the existence of a step; unlike the source, it is not an
algorithm, and no running time is claimed.

## Main results

* `Cslib.Circuits.Boolean.AffineDisperser.State.Valid.exists_step`: Lemma 4.2.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2026]
-/

public section

namespace Cslib.Circuits.Boolean.AffineDisperser

open Finset Cslib.BitString SemiCircuit AffineDisperserCore

namespace State

open AffineDisperserCore.State

variable {n : ℕ} {f : BooleanFunction n}

/-- **Lemma 4.2** of [Mishra and Santhanam][MishraSanthanam2026]: if `d < a`, a valid state for
an affine disperser for dimension `d` has a step of gate elimination: a valid state with smaller
`m + s`, `Δa ∈ {0, -1, -2}` and `ΔW ≤ 14 Δa`. -/
theorem Valid.exists_step {d : ℕ} {S : State n} (hS : S.Valid f) (hf : IsAffineDisperser f d)
    (ha : d < S.a) : ∃ S' : State n, Step f S S' := by
  let measure (T : State n) : ℕ × ℕ × ℕ := (T.gates.card, T.auxIn, T.childIn)
  have hwf : WellFounded (InvImage (Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))) measure) :=
    InvImage.wf measure (WellFounded.prod_lex Nat.lt_wfRel.wf (WellFounded.prod_lex Nat.lt_wfRel.wf
      Nat.lt_wfRel.wf))
  induction S using hwf.induction with
  | h S ih =>
    -- move affine gates into the affine system
    by_cases hmov : ∃ J, S.Movable J
    · obtain ⟨J, hJ⟩ := hmov
      have hp := Valid.preparation_moveAffine hS hJ
      have hcard := moveAffine_gates_card (S := S) ⟨hJ.1, S.freshEqn_notMem, hJ.2.1, hJ.2.2⟩
      obtain ⟨S', hstep⟩ := ih _ (Prod.Lex.left _ _ (hcard ▸ Nat.lt_succ_self _)) hp.valid
        (hp.a_eq ▸ ha)
      exact ⟨S', hstep.of_preparation hp⟩
    -- the preliminary reductions
    rcases Valid.step_or_normal hS hf ha (not_exists.mp hmov) with hstep | hN
    · exact hstep
    -- the minimal AND
    obtain ⟨hne, hand, t₁, t₂, hl, hr, ht12, ht₁, ht₂⟩ :=
      Valid.exists_minGate hS hf ha hN.not_movable hN.no_deletion
    have hG : S.gates.min' hne ∈ S.gates := Finset.min'_mem _ _
    -- an auxiliary input is exchanged with a parameter
    by_cases haux : t₁ ∈ S.aux ∨ t₂ ∈ S.aux
    · obtain ⟨S₁, hp, hgates, hlt⟩ : ∃ S₁ : State n, Preparation f S S₁ ∧ S₁.gates = S.gates ∧
          S₁.auxIn < S.auxIn := by
        rcases haux with h | h
        · exact Valid.exists_preparation_auxIn_lt hS hN hne (Or.inl ⟨hl, hr⟩) h ht12
        · exact Valid.exists_preparation_auxIn_lt hS hN hne (Or.inr ⟨hl, hr⟩) h ht12.symm
      obtain ⟨S', hstep⟩ := ih S₁ (by
        simp only [InvImage, measure, hgates]; exact Prod.Lex.right _ (Prod.Lex.left _ _ hlt))
        hp.valid (hp.a_eq ▸ ha)
      exact ⟨S', hstep.of_preparation hp⟩
    obtain ⟨haux₁, haux₂⟩ := not_or.mp haux
    have hx : t₁ ∈ S.params := (Finset.mem_union.1 ht₁).resolve_right haux₁
    have hy : t₂ ∈ S.params := (Finset.mem_union.1 ht₂).resolve_right haux₂
    obtain ⟨-, hxdeg⟩ := hN.and_param _ hG hand t₁ t₂ (Or.inl ⟨hl, hr⟩) hx hy ht12
    obtain ⟨-, hydeg⟩ := hN.and_param _ hG hand t₂ t₁ (Or.inr ⟨hl, hr⟩) hy hx ht12.symm
    -- a child of the minimal AND reading one of its inputs is rerouted
    by_cases hch : ∃ K ∈ S.gates, (S.gate K).Reads (S.gates.min' hne) ∧
        ((S.gate K).Reads t₁ ∨ (S.gate K).Reads t₂)
    · obtain ⟨K, hK, hKG, hKt⟩ := hch
      obtain ⟨S₁, hp, hgates, hauxeq, hlt⟩ :=
        Valid.exists_preparation_childIn_lt hS hne hl hr ht12 hx hy hxdeg hydeg hK hKG hKt
      obtain ⟨S', hstep⟩ := ih S₁ (by
        simp only [InvImage, measure, hgates, hauxeq]
        exact Prod.Lex.right _ (Prod.Lex.right _ hlt))
        hp.valid (hp.a_eq ▸ ha)
      exact ⟨S', hstep.of_preparation hp⟩
    -- eliminating the minimal AND
    obtain ⟨x, y, hmin⟩ := Valid.exists_minimalAnd hS hf ha hN hG hand hl hr ht12 hx hy
      fun K hK hKG => not_or.mp fun hKt => hch ⟨K, hK, hKG, hKt⟩
    exact Valid.step_of_minimalAnd hS hf ha hN hmin

end State

end Cslib.Circuits.Boolean.AffineDisperser
