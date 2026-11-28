/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.ModP.PrimePower
public import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.GCD.BigOperators
import CslibFrontier.Computability.Complexity.Classes.NP.Closure
import CslibFrontier.Computability.Complexity.Classes.P.Closure

/-!
# Composite Moduli for ModP

Characterization of the `ModP` counting class for composite moduli.
Contains the Hertrampf equivalence for prime factorizations, the union closure for all
moduli `k`, and the equivalence of intersection and complement closures for non-prime powers.

## References

* R. Beigel and J. Gill, *Counting classes: thresholds, parity, mods, and fewness*,
  TCS 103(1):3–23, 1992 (`BeigelGill1992`). Locators here (Theorem 32, Corollaries 33–35)
  are from the author's full version (June 10, 1996, pp. 4, 16), linked from
  https://cis.temple.edu/~beigel/papers/bg-mods-tcs.html. That version credits the main
  result to U. Hertrampf, *Relations among MOD-classes*, TCS 74(3):325–328, 1990; the
  Hertrampf proofs here are locally reconstructed and the 1990 original was not inspected.
-/

public section

namespace Cslib.Complexity

variable {α : Type} {enc : α ↪ List Bool} {A B : Set α} {k : ℕ}

theorem mem_ModP_mul_iff {j k : ℕ} (hjk : j.Coprime k) :
    A ∈ ModP (j * k) enc ↔ ∃ B C, B ∈ ModP j enc ∧ C ∈ ModP k enc ∧ A = B ∪ C := by
  constructor
  · rintro ⟨f, hf, hA⟩
    refine ⟨{a | f a % j ≠ 0}, {a | f a % k ≠ 0}, ⟨f, hf, fun _ => Iff.rfl⟩,
      ⟨f, hf, fun _ => Iff.rfl⟩, Set.ext fun a => ?_⟩
    simp only [Set.mem_union, Set.mem_ofPred_eq, hA a, ne_eq, ← not_and_or,
      ← Nat.dvd_iff_mod_eq_zero]
    exact not_congr ⟨fun h => ⟨dvd_of_mul_right_dvd h, dvd_of_mul_left_dvd h⟩,
      fun ⟨hj, hk⟩ => hjk.mul_dvd_of_dvd_of_dvd hj hk⟩
  · rintro ⟨B, C, ⟨f_j, hfj, hB⟩, ⟨f_k, hfk, hC⟩, rfl⟩
    refine ⟨fun a => k * f_j a + j * f_k a,
      SharpP.add_mem (SharpP.mul_mem (SharpP.natCast_mem k) hfj)
        (SharpP.mul_mem (SharpP.natCast_mem j) hfk), fun a => ?_⟩
    simp only [Set.mem_union, hB a, hC a, ne_eq, ← Nat.dvd_iff_mod_eq_zero, ← not_and_or]
    refine not_congr ⟨fun ⟨hj, hk⟩ =>
        dvd_add (mul_comm j k ▸ mul_dvd_mul_left k hj) (mul_dvd_mul_left j hk),
      fun hdvd => ?_⟩
    exact ⟨hjk.dvd_of_dvd_mul_left ((Nat.dvd_add_iff_left (dvd_mul_right j _)).mpr
        ((dvd_mul_right j k).trans hdvd)),
      hjk.symm.dvd_of_dvd_mul_left ((Nat.dvd_add_iff_right (dvd_mul_right k _)).mpr
        ((dvd_mul_left k j).trans hdvd))⟩

open scoped Classical in
theorem mem_ModP_prod_iff {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (h_coprime : (s : Set ι).Pairwise (fun i j => (f i).Coprime (f j))) :
    A ∈ ModP (∏ i ∈ s, f i) enc ↔ ∃ B : ι → Set α, (∀ i ∈ s, B i ∈ ModP (f i) enc) ∧
      A = ⋃ i ∈ s, B i := by
  induction s using Finset.induction_on generalizing A with
  | empty =>
    simp only [Finset.prod_empty, mem_ModP_one]
    exact ⟨fun h => ⟨fun _ => ∅, by simp [h]⟩, fun ⟨_, _, h⟩ => by simp [h]⟩
  | @insert a s ha ih =>
    have h_coprime_a_s : (f a).Coprime (∏ i ∈ s, f i) :=
      Nat.Coprime.prod_right fun i hi =>
        h_coprime (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hi)
          (ne_of_mem_of_not_mem hi ha).symm
    have h_coprime_s := h_coprime.mono (Finset.subset_insert a s)
    rw [Finset.prod_insert ha, mem_ModP_mul_iff h_coprime_a_s]
    constructor
    · rintro ⟨Ba, C, hBa, hC, rfl⟩
      rcases (ih h_coprime_s).mp hC with ⟨B, hB, rfl⟩
      refine ⟨Function.update B a Ba, fun i hi => ?_, ?_⟩
      · rcases Finset.mem_insert.mp hi with rfl | hi_s
        · simpa [Function.update] using hBa
        · simpa [Function.update, ne_of_mem_of_not_mem hi_s ha] using hB i hi_s
      · ext x
        simp only [Finset.mem_insert, Set.mem_iUnion, Set.mem_union, Function.update]
        aesop
    · rintro ⟨B, hB, rfl⟩
      exact ⟨B a, ⋃ i ∈ s, B i, hB a (Finset.mem_insert_self a s),
        (ih h_coprime_s).mpr ⟨B, fun i hi => hB i (Finset.mem_insert_of_mem hi), rfl⟩,
        Finset.set_biUnion_insert a s B⟩


theorem mem_ModP_iff_primeFactors (hk : k ≠ 0) :
    A ∈ ModP k enc ↔ ∃ B : ℕ → Set α, (∀ p ∈ k.primeFactors, B p ∈ ModP p enc) ∧
      A = ⋃ p ∈ k.primeFactors, B p := by
  have hk_eq : k = ∏ p ∈ k.primeFactors, p ^ k.factorization p :=
    (Nat.prod_factorization_pow_eq_self hk).symm.trans
      (Nat.prod_factorization_eq_prod_primeFactors (fun p e => p ^ e))
  have h_coprime : (k.primeFactors : Set ℕ).Pairwise fun i j =>
      (i ^ k.factorization i).Coprime (j ^ k.factorization j) :=
    fun i hi j hj hneq => Nat.pairwise_coprime_pow_primeFactors_factorization (n := k)
      fun h : (⟨i, hi⟩ : k.primeFactors) = ⟨j, hj⟩ => hneq (congrArg Subtype.val h)
  rw [congrArg (ModP · enc) hk_eq,
    mem_ModP_prod_iff k.primeFactors (fun p => p ^ k.factorization p) h_coprime]
  refine exists_congr fun B => and_congr_left fun _ => forall₂_congr fun p hp => ?_
  rw [ModP_prime_pow (Nat.prime_of_mem_primeFactors hp) (Finsupp.mem_support_iff.mp hp)]

theorem ModP_eq_ModP_prod_primeFactors (hk : k ≠ 0) :
    ModP k enc = ModP (∏ p ∈ k.primeFactors, p) enc := by
  ext A
  rw [mem_ModP_iff_primeFactors hk, mem_ModP_prod_iff k.primeFactors (fun p => p)
    fun i hi j hj hneq => (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hi)
      (Nat.prime_of_mem_primeFactors hj)).mpr hneq]

theorem supClosed_ModP (k : ℕ) (hA : A ∈ ModP k enc) (hB : B ∈ ModP k enc) :
    A ∪ B ∈ ModP k enc := by
  rcases eq_or_ne k 0 with rfl | hk
  · rw [ModP_zero] at hA hB ⊢
    exact union_mem_NP hA hB
  · rw [mem_ModP_iff_primeFactors hk] at hA hB ⊢
    rcases hA with ⟨B_A, hB_A, rfl⟩
    rcases hB with ⟨B_B, hB_B, rfl⟩
    refine ⟨fun p => B_A p ∪ B_B p,
      fun p hp => union_mem_ModP (Nat.prime_of_mem_primeFactors hp) (hB_A p hp) (hB_B p hp), ?_⟩
    ext x
    simp only [Set.mem_union, Set.mem_iUnion]
    aesop

private lemma binter_mem_ModP (hk : 2 ≤ k)
    (hInter : ∀ A B, A ∈ ModP k enc → B ∈ ModP k enc → A ∩ B ∈ ModP k enc)
    (s : Finset ℕ) (f : ℕ → Set α) (hf : ∀ p ∈ s, f p ∈ ModP k enc) :
    ⋂ p ∈ s, f p ∈ ModP k enc := by
  induction s using Finset.induction_on with
  | empty => simpa using P_subset_ModP hk univ_mem_P
  | @insert a s _ ih =>
    simpa [Finset.mem_insert] using hInter _ _ (hf a (Finset.mem_insert_self a s))
      (ih fun p hp => hf p (Finset.mem_insert_of_mem hp))

theorem hertrampf_equivalence {k : ℕ} (hk : 2 ≤ k) :
    (∀ A B, A ∈ ModP k enc → B ∈ ModP k enc → A ∩ B ∈ ModP k enc) ↔
      (∀ A, A ∈ ModP k enc → Aᶜ ∈ ModP k enc) := by
  constructor
  · intro hInter A hA
    have hk_ne_zero : k ≠ 0 := by omega
    rcases (mem_ModP_iff_primeFactors hk_ne_zero).mp hA with ⟨B_A, hB_A, rfl⟩
    rw [Set.compl_iUnion₂]
    exact binter_mem_ModP hk hInter k.primeFactors _ fun p hp =>
      ModP_subset_ModP_of_dvd (Nat.dvd_of_mem_primeFactors hp) hk_ne_zero
        (compl_mem_ModP (Nat.prime_of_mem_primeFactors hp) (hB_A p hp))
  · intro hCompl A B hA hB
    simpa using hCompl _ (supClosed_ModP k (hCompl A hA) (hCompl B hB))

end Cslib.Complexity
