/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Algebra.Covering.Certificate
public import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

/-!
# Duality in a covering monoid

The two halves of the proof of Theorem A.6 of *VP ≠ VNP over every field* [AnthropicVPVNP2026], for
a commutative monoid with a covering relation (`Cslib.Covering`) and certificates
(`Cslib.Covering.Certificate`).

* The infimum of the weights of the certificates of `t` is an upper functional if `1` has no
  certificate of weight below `1`. It respects `(A β, C, η)` for every `β`
  (`Cslib.Covering.isUpperFunctional_sInf_certificate`).
* Otherwise, `C ^ N` is covered by at most `(c + 1) ^ (k + 1) η ^ (-N)` products of `N` factors
  `A β` (`Cslib.Covering.exists_coveredBy_pow_of_certificate`). Here `k` is the level of a
  certificate of `1` of weight below `1`, and `C` is covered by `c` copies of one `A β₀`. The proof
  exchanges factors `C`, replaces `C ^ k` by the cover as long as it occurs, and replaces the
  remaining factors `C` by copies of `A β₀`.

## Main results

* `Cslib.Covering.isUpperFunctional_sInf_certificate`.
* `Cslib.Covering.exists_coveredBy_pow_of_certificate`.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Theorem A.6 (§A.5) of the paper and its proof in Appendix Q; module `Paper.Gauges` (the
  certificate part)
-/

public section

namespace Cslib.Covering

open Finset

variable {M : Type*} [CommMonoid M] {D : Covering M} {B : Type} [Fintype B]


/-- Proof of Theorem A.6, first half: let `p(t)` be the infimum of the weights of the certificates
for `t`. Certificates can be multiplied, raised to a common level and added along covers. The
trivial certificate of level `0` gives `p(1) ≤ 1`, and copies of `1` give every `t` a certificate of
level `0`, so `p` is an upper functional if `p(1) ≥ 1`. Multiplying a certificate for `tC` by `A_β`
gives one for `tA_β` of one level higher and `η` times the weight, so `p` respects `(A_β, C, η)`. -/
theorem isUpperFunctional_sInf_certificate {C : M} {A : B → M} {η : ℝ} (hη : 0 < η)
    (hone : ∀ t : M, ∃ r : ℕ, D.CoveredBy t (fun _ : Fin r => (1 : M)))
    (h : ∀ k W, Nonempty (Certificate D C A η 1 k W) → 1 ≤ W) :
    IsUpperFunctional D (fun t => sInf {W | ∃ k, Nonempty (Certificate D C A η t k W)}) ∧
      ∀ β, Respects (fun t => sInf {W | ∃ k, Nonempty (Certificate D C A η t k W)}) (A β) C η := by
  classical
  set S : M → Set ℝ := fun t => {W | ∃ k, Nonempty (Certificate D C A η t k W)} with hS
  have hne : ∀ t, (S t).Nonempty := by
    intro t
    obtain ⟨r, hr⟩ := hone t
    exact ⟨_, 0, ⟨.cover hr fun _ => .one 0⟩⟩
  have h0 : ∀ t, ∀ w ∈ S t, 0 ≤ w := fun t w ⟨k, ⟨c⟩⟩ => c.weight_nonneg hη
  refine ⟨isUpperFunctional_sInf hne h0 ⟨0, ⟨.one 0⟩⟩ (fun w ⟨k, hk⟩ => h k w hk)
    (fun s t a ⟨k, ⟨c⟩⟩ b ⟨l, ⟨c'⟩⟩ => ⟨k + l, ⟨c.mul hη c'⟩⟩) ?_, fun β => ?_⟩
  · intro κ _ t b hb w hw
    choose k hk using hw
    exact ⟨_, ⟨∑ j, k j, ⟨.cover hb fun j => (hk j).some.raise hη
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))⟩⟩, le_rfl⟩
  · exact respects_sInf hne h0 hη fun t w ⟨k, ⟨c⟩⟩ => ⟨k + 1, ⟨c.mulGen hη β⟩⟩

/-- Proof of Theorem A.6: if `1` has a certificate of level `k` and weight below `1`, then `k ≥ 1`
and every term has `v_j ≠ 0`, as it would weigh `1` otherwise. So the certificate is a cover of
`C^k` by terms in which at least one `C` was exchanged. (The certificate of level `k₀` is raised to
the level `k = k₀ + 1`.) -/
private theorem thm_duality_exchange {C : M} {A : B → M} {η : ℝ} (hη : 0 < η) {k₀ : ℕ} {W : ℝ}
    (h : Certificate D C A η 1 k₀ W) (hW1 : W < 1) :
    ∃ (κ : Type) (_ : Fintype κ) (u : κ → ℕ) (v : κ → B → ℕ), (∀ j, u j + ∑ β, v j β = k₀ + 1) ∧
      (∀ j, u j < k₀ + 1) ∧ D.CoveredBy (C ^ (k₀ + 1)) (fun j => C ^ u j * (∏ β, A β ^ v j β)) ∧
      ∑ j, η ^ (∑ β, v j β) ≤ 1 := by
  let c := h.raise hη (Nat.le_succ k₀)
  obtain ⟨κ, _, u, v, hu, hc, hW⟩ : ∃ (κ : Type) (_ : Fintype κ) (u : κ → ℕ) (v : κ → B → ℕ),
      (∀ j, u j + ∑ β, v j β = k₀ + 1) ∧
      D.CoveredBy (1 * C ^ (k₀ + 1)) (fun j => C ^ u j * ∏ β, A β ^ v j β) ∧
      ∑ j, η ^ (∑ β, v j β) ≤ W :=
    ⟨c.Index, inferInstance, c.u, c.v, c.level_eq, c.coveredBy, c.weight_le⟩
  rw [one_mul] at hc
  have hlt : ∑ j, η ^ (∑ β, v j β) < 1 := hW.trans_lt hW1
  refine ⟨κ, inferInstance, u, v, hu, fun j => ?_, hc, hlt.le⟩
  by_contra hge
  have h1 := hu j
  have h2 : ∑ β, v j β = 0 := by omega
  have h3 := Finset.single_le_sum (f := fun j => η ^ (∑ β, v j β))
    (fun j _ => by positivity) (Finset.mem_univ j)
  simp only [h2, pow_zero] at h3
  linarith

/-- Proof of Theorem A.6: in `C^N`, replace `C^k` by this cover as long as some term contains it.
The total weight never increases, so it stays at most `1`, and each final term has fewer than `k`
factors `C`. -/
private theorem thm_duality_replace {C : M} {A : B → M} {η : ℝ} (hη : 0 < η)
    {k : ℕ} {κ : Type} [Fintype κ] {u : κ → ℕ}
    {v : κ → B → ℕ} (hu : ∀ j, u j + ∑ β, v j β = k) (huk : ∀ j, u j < k)
    (hc : D.CoveredBy (C ^ k) (fun j => C ^ u j * (∏ β, A β ^ v j β)))
        (hw : ∑ j, η ^ (∑ β, v j β) ≤ 1) (N : ℕ) :
    ∃ (κ' : Type) (_ : Fintype κ') (u' : κ' → ℕ) (v' : κ' → B → ℕ),
      (∀ j, u' j < k) ∧ (∀ j, u' j + ∑ β, v' j β = N) ∧
      D.CoveredBy (C ^ N) (fun j => C ^ u' j * (∏ β, A β ^ v' j β)) ∧ ∑ j,
          η ^ (∑ β, v' j β) ≤ 1 := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases lt_or_ge N k with hN | hN
    · exact ⟨Unit, inferInstance, fun _ => N, fun _ _ => 0, fun _ => by simpa using hN,
        by simp, by simpa using D.refl (C ^ N), by simp⟩
    · have hN' : ∀ j, N - k + u j < N := fun j => by have := huk j; omega
      choose μ i u' v' hu' hs' hc' hw' using fun j => ih _ (hN' j)
      refine ⟨Σ j, μ j, inferInstance, fun x => u' x.1 x.2, fun x β => v x.1 β + v' x.1 x.2 β,
        fun x => hu' _ _, fun x => ?_, ?_, ?_⟩
      · have h1 := hs' x.1 x.2
        have h2 := hu x.1
        rw [Finset.sum_add_distrib]
        dsimp only
        omega
      · have h1 : D.CoveredBy (C ^ N) (fun j => C ^ (N - k + u j) * (∏ β, A β ^ v j β)) := by
          have h2 := D.mul (C ^ (N - k)) hc
          rw [← pow_add, Nat.add_sub_cancel' hN] at h2
          convert h2 using 2 with j
          rw [pow_add]
          ac_rfl
        refine D.bind (c := fun j (x : μ j) =>
          C ^ u' j x * (∏ β, A β ^ (v j β + v' j x β))) h1 fun j => ?_
        have h2 := D.mul ((∏ β, A β ^ v j β)) (hc' j)
        convert h2 using 2 with x
        simp only [pow_add, Finset.prod_mul_distrib]
        ac_rfl
      · rw [Fintype.sum_sigma]
        refine le_trans (Finset.sum_le_sum fun j _ => ?_) hw
        calc ∑ x, η ^ (∑ β, (v j β + v' j x β)) =
            η ^ (∑ β, v j β) * ∑ x, η ^ (∑ β, v' j x β) := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun x _ => by rw [← pow_add, Finset.sum_add_distrib]
          _ ≤ η ^ (∑ β, v j β) * 1 := by gcongr; exact hw' j
          _ = _ := mul_one _

omit [Fintype B] in
/-- Proof of Theorem A.6, the remaining factors: if `C` is covered by `c` copies of `a`, then `Cⁿ`
is covered by `cⁿ` copies of `aⁿ`. -/
private theorem thm_duality_copies {C a : M} {c : ℕ} (hc : D.CoveredBy C (fun _ : Fin c => a))
    (n : ℕ) :
    ∃ (μ : Type) (_ : Fintype μ),
        Fintype.card μ = c ^ n ∧ D.CoveredBy (C ^ n) (fun _ : μ => a ^ n) := by
  induction n with
  | zero => exact ⟨Unit, inferInstance, by simp, by simpa using D.refl (1 : M)⟩
  | succ n ih =>
    obtain ⟨μ, _, hμ, hcov⟩ := ih
    refine ⟨Σ _ : μ, Fin c, inferInstance, ?_, ?_⟩
    · rw [Fintype.card_sigma]
      simp [hμ, pow_succ]
    · have := D.mul_mul hcov hc
      simpa only [pow_succ] using this

/-- Proof of Theorem A.6, second half: from a certificate for `1` of level `k₀` and weight below
`1`, and a cover of `C` by `c` copies of some `A_β`, a cover of `C^N` by products of `N` factors.
The paper bounds the number of terms by `η^(-N)` before, and by `c^k η^(-N)` after, replacing each
remaining factor `C` by `c` copies of `A_β`; the bound here has `c + 1` for `c`, and `k = k₀ + 1`.
-/
theorem exists_coveredBy_pow_of_certificate {C : M} {A : B → M} {η : ℝ} (hη : 0 < η) (hη1 : η < 1)
    {β₀ : B} {c : ℕ}
    (hcA : D.CoveredBy C (fun _ : Fin c => A β₀)) {k₀ : ℕ} {W : ℝ} (h : Certificate D C A η 1 k₀ W)
        (hW1 : W < 1) (N : ℕ) :
    ∃ (κ : Type) (_ : Fintype κ) (v : κ → B → ℕ),
      (Fintype.card κ : ℝ) ≤ ((c : ℝ) + 1) ^ (k₀ + 1) * (η⁻¹) ^ N ∧ (∀ j, ∑ β, v j β = N) ∧
      D.CoveredBy (C ^ N) (fun j => (∏ β, A β ^ v j β)) := by
  classical
  obtain ⟨κ, _, u, v, hu, huk, hc, hw⟩ := thm_duality_exchange hη h hW1
  obtain ⟨κ', _, u', v', hu', hs', hc', hw'⟩ := thm_duality_replace hη hu huk hc hw N
  choose μ i hμ hcov using fun j : κ' => thm_duality_copies hcA (u' j)
  set E : ℝ := ((c : ℝ) + 1) ^ (k₀ + 1) with hE
  refine ⟨Σ j, μ j, inferInstance, fun x β => v' x.1 β + if β = β₀ then u' x.1 else 0,
    ?_, fun x => ?_, ?_⟩
  · rw [Fintype.card_sigma]
    push_cast
    have h1 : ∀ j, (Fintype.card (μ j) : ℝ) ≤ E := fun j => by
      rw [hμ j]
      push_cast
      calc (c : ℝ) ^ u' j ≤ ((c : ℝ) + 1) ^ u' j := by gcongr; linarith
        _ ≤ E := pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) c]) (hu' j).le
    have h2 : (Fintype.card κ' : ℝ) * η ^ N ≤ 1 := by
      refine le_trans ?_ hw'
      rw [← nsmul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
      refine Finset.sum_le_sum fun j _ => pow_le_pow_of_le_one hη.le hη1.le ?_
      have := hs' j
      omega
    calc ∑ j, (Fintype.card (μ j) : ℝ) ≤ ∑ _j : κ', E := Finset.sum_le_sum fun j _ => h1 j
      _ = Fintype.card κ' * E := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = (Fintype.card κ' * η ^ N) * (E * (η⁻¹) ^ N) := by
        rw [inv_pow]
        field_simp
      _ ≤ 1 * (E * (η⁻¹) ^ N) := by gcongr
      _ = _ := one_mul _
  · have := hs' x.1
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    omega
  · refine D.bind (b := fun j => C ^ u' j * (∏ β, A β ^ v' j β))
      (c := fun j (_ : μ j) => (∏ β, A β ^ (v' j β + if β = β₀ then u' j else 0))) hc' fun j => ?_
    have h1 := D.mul ((∏ β, A β ^ v' j β)) (hcov j)
    convert h1 using 2 with x
    simp only [pow_add, Finset.prod_mul_distrib, pow_ite, pow_zero, Finset.prod_ite_eq',
      Finset.mem_univ, ite_true]
    exact mul_comm _ _


end Cslib.Covering
