/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Nullstellensatz

/-!
# Specializing finitely many elements to an algebraically closed field

Two facts used to move circuits between fields of the same characteristic:

* two fields of the same characteristic have homomorphisms to a common nonzero ring, their tensor
  product over the prime field (`Cslib.exists_common_ring`);
* Zariski's lemma, in the form of Hilbert's Nullstellensatz: finitely many elements of a nonzero
  ring that contains an algebraically closed field `KK` lie in a subring with a homomorphism to `KK`
  (`Cslib.exists_specialisation`).

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `Nc.Rate.Transfer`.

## Main results

* `Cslib.exists_common_ring`, `Cslib.exists_specialisation`.
-/

public section

namespace Cslib

open MvPolynomial
open scoped TensorProduct

section Rings

/-- Two fields of the same characteristic have homomorphisms to a common nonzero ring, namely their
tensor product over the prime field. -/
theorem exists_common_ring.{w} (F : Type w) (KK : Type) [Field F] [Field KK] (p : ℕ)
    [CharP F p] [CharP KK p] :
    ∃ (T : Type w) (_ : CommRing T) (_ : Nontrivial T),
        Nonempty (F →+* T) ∧ Nonempty (KK →+* T) := by
  rcases CharP.char_is_prime_or_zero F p with hp | rfl
  · have : Fact p.Prime := ⟨hp⟩
    let : Algebra (ZMod p) F := ZMod.algebra F p
    let : Algebra (ZMod p) KK := ZMod.algebra KK p
    exact ⟨F ⊗[ZMod p] KK, inferInstance, inferInstance,
      ⟨(Algebra.TensorProduct.includeLeft : F →ₐ[ZMod p] F ⊗[ZMod p] KK).toRingHom⟩,
      ⟨(Algebra.TensorProduct.includeRight : KK →ₐ[ZMod p] F ⊗[ZMod p] KK).toRingHom⟩⟩
  · have : CharZero F := CharP.charP_to_charZero F
    have : CharZero KK := CharP.charP_to_charZero KK
    exact ⟨F ⊗[ℚ] KK, inferInstance, inferInstance,
      ⟨(Algebra.TensorProduct.includeLeft : F →ₐ[ℚ] F ⊗[ℚ] KK).toRingHom⟩,
      ⟨(Algebra.TensorProduct.includeRight : KK →ₐ[ℚ] F ⊗[ℚ] KK).toRingHom⟩⟩

/-- Zariski's lemma, in the form of Hilbert's Nullstellensatz: finitely many elements of a nonzero
ring T that contains an image of the algebraically closed field KK lie in a subring of T that has a
homomorphism to KK. -/
theorem exists_specialisation {KK T : Type*} [Field KK] [IsAlgClosed KK] [CommRing T]
    [Nontrivial T] (g : KK →+* T)
    (S : Finset T) : ∃ A : Subring T, (S : Set T) ⊆ A ∧ Nonempty (A →+* KK) := by
  let φ : MvPolynomial S KK →+* T := eval₂Hom g Subtype.val
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (RingHom.ker φ) (RingHom.ker_ne_top φ)
  obtain ⟨x, rfl⟩ := isMaximal_iff_eq_vanishingIdeal_singleton.1 hM
  have hx : ∀ a ∈ RingHom.ker φ,
      (aeval x : MvPolynomial S KK →ₐ[KK] KK).toRingHom a = 0 := fun a ha =>
    mem_vanishingIdeal_iff.1 (hle ha) x rfl
  refine ⟨φ.range, fun a ha => ⟨X ⟨a, ha⟩, by simp [φ]⟩, ⟨?_⟩⟩
  exact (Ideal.Quotient.lift (RingHom.ker φ) _ hx).comp
      (RingHom.quotientKerEquivRange φ).symm.toRingHom

end Rings

end Cslib
