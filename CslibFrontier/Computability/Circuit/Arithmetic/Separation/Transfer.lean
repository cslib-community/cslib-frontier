/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Border
public import CslibFrontier.Foundations.RingTheory.Specialization

/-!
# Constants in an algebraically closed field of the same characteristic

Appendices A and B of *VP ≠ VNP over every field* [AnthropicVPVNP2026].

* `Separation.lem_transfer` (Lemma lem:transfer): a polynomial with integer coefficients that is
  computed within `S` nodes over a field of characteristic `p` is computed within `S` nodes over
  every algebraically closed field `KK` of characteristic `p`.
* `Separation.lem_transfer_approx` (Lemma lem:transfer-approx): an approximation within `s` nodes
  gives a circuit with constants in `KK[ε, ε⁻¹]` whose output is `q + ε KK[ε][x]`.

Both proofs push the circuit into a common ring of the two fields (`Cslib.exists_common_ring`). The
finitely many constants are then lifted to a subring that has a homomorphism to `KK`
(`Arithmetic.ComputedWithin.exists_finset_lift`, `Cslib.exists_specialisation`), and the circuit
is mapped along it. In the approximate case the constants are first cut off to Laurent polynomials
(`Arithmetic.ApproximatedWithin.exists_laurentPolynomial`), and the lift goes coefficient by
coefficient (`AddMonoidAlgebra.range_map`).

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `Paper.Transfer`.

## Main results

* `Separation.lem_transfer`, `Separation.lem_transfer_approx`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation

open MvPolynomial

variable {F : Type*} {KK : Type} [Field F] [Field KK] [IsAlgClosed KK] {X : Type*}

/-- **Paper: Lemma lem:transfer.** "Let a polynomial with integer coefficients have a circuit with
S gates over a field of characteristic p. It has one with S gates over KK." Here `KK` is any
algebraically closed field of that characteristic. -/
theorem lem_transfer (p : ℕ) [CharP F p] [CharP KK p] (q : MvPolynomial X ℤ) {S : ℕ}
    (h : ComputedWithin (map (Int.castRingHom F) q) S) :
    ComputedWithin (map (Int.castRingHom KK) q) S := by
  obtain ⟨T, _, _, ⟨f⟩, ⟨g⟩⟩ := exists_common_ring F KK p
  obtain ⟨C, hC⟩ := (h.map f).exists_finset_lift
  obtain ⟨A, hA, ⟨ψ⟩⟩ := exists_specialisation g C
  obtain ⟨Q, hQ, e⟩ := hC A.subtype fun t ht => ⟨⟨t, hA ht⟩, rfl⟩
  have e1 : Q = map (Int.castRingHom A) q := by
    apply map_injective A.subtype A.subtype_injective
    rw [e, map_map, map_map]
    exact congrArg (fun r => map r q) (Subsingleton.elim _ _)
  have h2 := hQ.map ψ
  rw [e1, map_map] at h2
  exact (congrArg (fun r => ComputedWithin (map r q) S) (Subsingleton.elim _ _)).mp h2

/-- **Paper: Lemma lem:transfer-approx.** "An approximating circuit for a polynomial with integer
coefficients, over a field of characteristic p, gives one of the same size with constants in
KK[ε,ε⁻¹] and output in f + εKK[ε][x]": the constants are cut off, and the argument of Lemma
lem:transfer is applied to their coefficients. -/
theorem lem_transfer_approx (p : ℕ) [CharP F p] [CharP KK p] (q : MvPolynomial X ℤ) {s : ℕ}
    (h : ApproximatedWithin (map (Int.castRingHom F) q) s) :
    ∃ P : MvPolynomial X (LaurentPolynomial KK), ComputedWithin P s ∧
      ∀ d : X →₀ ℕ, (∀ i : ℤ, i < 0 → (P.coeff d).coeff i = 0) ∧
        (P.coeff d).coeff 0 = (map (Int.castRingHom KK) q).coeff d := by
  suffices main : ∃ P : MvPolynomial X (LaurentPolynomial KK), ComputedWithin P s ∧
      ∀ (d : X →₀ ℕ) (i : ℤ), i ≤ 0 →
        (P.coeff d).coeff i = if i = 0 then (map (Int.castRingHom KK) q).coeff d else 0 by
    obtain ⟨P, hP, hc⟩ := main
    exact ⟨P, hP, fun d => ⟨fun i hi => by rw [hc d i hi.le, ite_eq_right hi.ne],
      by rw [hc d 0 le_rfl, ite_eq_left rfl]⟩⟩
  obtain ⟨T, _, _, ⟨f⟩, ⟨g⟩⟩ := exists_common_ring F KK p
  obtain ⟨P₀, hP₀, hc₀⟩ := h.exists_laurentPolynomial
  obtain ⟨C, hC⟩ := (hP₀.map (AddMonoidAlgebra.mapRingHom ℤ f)).exists_finset_lift
  classical
  obtain ⟨A, hA, ⟨ψ⟩⟩ := exists_specialisation g (C.biUnion fun c => c.coeff.support.image c.coeff)
  obtain ⟨L, hL, hm⟩ := hC (AddMonoidAlgebra.mapRingHom ℤ A.subtype) fun c hc => by
    rw [AddMonoidAlgebra.coe_mapRingHom, AddMonoidAlgebra.range_map]
    refine fun i => ⟨⟨c.coeff i, ?_⟩, rfl⟩
    by_cases hi : c.coeff i = 0
    · rw [hi]
      exact A.zero_mem
    · exact hA (Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨c, hc, Finset.mem_image.2
        ⟨i, Finsupp.mem_support_iff.2 hi, rfl⟩⟩))
  refine ⟨map (AddMonoidAlgebra.mapRingHom ℤ ψ) L, hL.map _, fun d i hi => ?_⟩
  have hP₀c : (P₀.coeff d).coeff i = if i = 0 then (map (Int.castRingHom F) q).coeff d else 0 := by
    have := hc₀ d i hi
    rwa [coeff_map, LaurentPolynomial.coeff_toLaurentSeries] at this
  have e1 : (L.coeff d).coeff i = if i = 0 then ((q.coeff d : ℤ) : A) else 0 := by
    apply A.subtype_injective
    have := congrArg (fun P => (P.coeff d).coeff i) hm
    simp only [coeff_map] at this
    rw [← AddMonoidAlgebra.coeff_mapRingHom, this, AddMonoidAlgebra.coeff_mapRingHom, hP₀c,
      coeff_map]
    split_ifs <;> simp
  rw [coeff_map, AddMonoidAlgebra.coeff_mapRingHom, e1, coeff_map]
  split_ifs <;> simp

end Cslib.Circuits.Arithmetic.Separation
