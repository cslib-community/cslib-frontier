/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CuttingPlanes
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Cutting planes under reifications

TODO
-/

public section

namespace Cslib.Logic.PL

noncomputable section

open Finset

namespace Ineq

variable {V : Type*} [DecidableEq V] (S : Finset V) (τ : V → Bool)

/-- The inequality of the literal on `v` that `τ` makes false: `xᵥ ≥ 0` if `τ v` is false and
`1 - xᵥ ≥ 0` if `τ v` is true. -/
@[expose] def offLit (v : V) : Ineq V := Literal.toIneq (v, !τ v)

/-- **The guard** of the partial assignment `τ` on `S`: `∑_{v ∈ S} ℓ̄ᵥ ≥ 0`, the sum of the
literals it makes false. `D + K • guard S τ` is the implication `⋀_{v ∈ S} ℓᵥ ⇒ D` of the paper,
with reification coefficient `K`. -/
@[expose] def guard : Ineq V := ∑ v ∈ S, offLit τ v

/-- **The restriction** `D↾ρ` of `D` by the partial assignment `ρ` that is `τ` on `S`: every
variable of `S` is replaced by its value (equation (27) of the paper). -/
@[expose] def restrict (I : Ineq V) : Ineq V :=
  ⟨I.coeff.filter (· ∉ S), I.bound - ∑ v ∈ S, I.coeff v * (τ v).toInt⟩

variable {S τ}

omit [DecidableEq V] in
theorem coeff_offLit (v : V) :
    (offLit τ v).coeff = Finsupp.single v (if τ v then -1 else 1) := by
  cases h : τ v <;> simp [offLit, h]

omit [DecidableEq V] in
theorem bound_offLit (v : V) : (offLit τ v).bound = -(τ v).toInt := by
  cases h : τ v <;> simp [offLit, h]

theorem coeff_guard (w : V) :
    (guard S τ).coeff w = if w ∈ S then (if τ w then -1 else 1) else 0 := by
  simp only [guard, coeff_sum, Finsupp.finsetSum_apply, coeff_offLit,
    Finsupp.single_apply]
  rw [Finset.sum_ite_eq']

omit [DecidableEq V] in
theorem bound_guard : (guard S τ).bound = -∑ v ∈ S, (τ v).toInt := by
  simp [guard, bound_offLit]

theorem coeff_restrict (I : Ineq V) (w : V) :
    (I.restrict S τ).coeff w = if w ∈ S then 0 else I.coeff w := by
  simp only [restrict, Finsupp.filter_apply]
  split_ifs <;> simp_all

theorem restrict_add (I J : Ineq V) : (I + J).restrict S τ = I.restrict S τ + J.restrict S τ := by
  ext w
  · simp only [coeff_restrict, coeff_add, Finsupp.add_apply]; split_ifs <;> simp
  · simp only [restrict, bound_add, coeff_add, Finsupp.add_apply, add_mul, sum_add_distrib]; ring

theorem restrict_nsmul (c : ℕ) (I : Ineq V) : (c • I).restrict S τ = c • I.restrict S τ := by
  ext w
  · simp only [coeff_restrict, coeff_nsmul, Finsupp.smul_apply, nsmul_eq_mul]; split_ifs <;> simp
  · simp only [restrict, bound_nsmul, coeff_nsmul, Finsupp.smul_apply, nsmul_eq_mul, mul_sub,
      mul_sum, mul_assoc]

theorem restrict_restrict (I : Ineq V) : (I.restrict S τ).restrict S τ = I.restrict S τ := by
  ext w
  · simp only [coeff_restrict]; split_ifs <;> rfl
  · simp only [restrict, Finsupp.filter_apply]
    simp only [ite_not, ite_mul, zero_mul, sub_eq_self]
    exact Finset.sum_eq_zero fun v hv => by simp [hv]

/-- The slack bound of `I` on `S`: every multiplier of **Lemma 2** is positive for a reification
coefficient above it. -/
@[expose] def lemma2Bound (S : Finset V) (I : Ineq V) : ℕ := 1 + ∑ v ∈ S, (I.coeff v).natAbs

/-- The signed coefficient of `ℓ̄ᵥ` in `I`: `I = I↾ρ + ∑_{v ∈ S} sᵥ ℓ̄ᵥ`. -/
def offCoeff (τ : V → Bool) (I : Ineq V) (v : V) : ℤ := if τ v then -I.coeff v else I.coeff v

omit [DecidableEq V] in
theorem offCoeff_lt (τ : V → Bool) (I : Ineq V) {v : V} (hv : v ∈ S) :
    offCoeff τ I v < lemma2Bound S I := by
  have h1 : (I.coeff v).natAbs ≤ ∑ v ∈ S, (I.coeff v).natAbs :=
    Finset.single_le_sum_of_canonicallyOrdered (f := fun v => (I.coeff v).natAbs) hv
  have h2 : offCoeff τ I v ≤ ((I.coeff v).natAbs : ℤ) := by
    rw [Int.natCast_natAbs]; unfold offCoeff; split_ifs
    exacts [neg_le_abs _, le_abs_self _]
  have h3 : ((I.coeff v).natAbs : ℤ) ≤ ((∑ v ∈ S, (I.coeff v).natAbs : ℕ) : ℤ) := by
    exact_mod_cast h1
  simp only [lemma2Bound, Nat.cast_add, Nat.cast_one]
  linarith

/-- **Lemma 2 of the paper, as an identity**: adding `(K - sᵥ) ℓ̄ᵥ ≥ 0` to `I` for every `v ∈ S`
gives `I↾ρ + K • guard`. -/
theorem add_sum_offLit (I : Ineq V) (K : ℕ) (hK : ∀ v ∈ S, offCoeff τ I v ≤ K) :
    I + ∑ v ∈ S, ((K : ℤ) - offCoeff τ I v).toNat • offLit τ v =
      I.restrict S τ + K • guard S τ := by
  ext w
  · simp only [coeff_add, Finsupp.add_apply, coeff_sum, Finsupp.finsetSum_apply, coeff_nsmul,
      Finsupp.smul_apply, coeff_offLit, Finsupp.single_apply, coeff_restrict, coeff_guard,
      nsmul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq']
    by_cases hw : w ∈ S
    · have := hK w hw
      simp only [hw, ↓reduceIte, offCoeff] at this ⊢
      rcases Bool.eq_false_or_eq_true (τ w) with ht | ht <;> simp [ht] at this ⊢ <;> omega
    · simp [hw]
  · have hpt : ∀ v ∈ S, ((((K : ℤ) - offCoeff τ I v).toNat : ℕ) : ℤ) * -(τ v).toInt =
        -(I.coeff v * (τ v).toInt) - K * (τ v).toInt := by
      intro v hv
      have := hK v hv
      unfold offCoeff at this ⊢
      rcases Bool.eq_false_or_eq_true (τ v) with ht | ht <;> simp [ht] at this ⊢; omega
    simp only [bound_add, bound_sum, bound_nsmul, bound_offLit, restrict, bound_guard,
      nsmul_eq_mul]
    rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]
    ring

/-- **Division under a guard**: dividing `I↾ρ + c (K + 1) • guard` by `c`, which divides the
coefficients of `I`, gives `(I.div c)↾ρ + (K + 1) • guard`. -/
theorem div_restrict_add_guard {I : Ineq V} {c : ℕ} (hc : 0 < c)
    (hdvd : ∀ v, (c : ℤ) ∣ I.coeff v) (K : ℕ) :
    (I.restrict S τ + (c * (K + 1)) • guard S τ).div c =
      (I.div c).restrict S τ + (K + 1) • guard S τ := by
  have hc' : (0 : ℤ) < c := by exact_mod_cast hc
  have hmul : ∀ v, (c : ℤ) * (I.coeff v / c) = I.coeff v := fun v => Int.mul_ediv_cancel' (hdvd v)
  refine div_eq_of hc ?_ ?_ ?_
  · ext w
    simp only [coeff_add, Finsupp.add_apply, coeff_nsmul, Finsupp.smul_apply, coeff_restrict,
      coeff_div, coeff_guard, nsmul_eq_mul, smul_eq_mul]
    push_cast
    split_ifs <;> simp [hmul]; ring
  · have h1 := (bound_div_le_iff (I := I) hc (y := (I.div c).bound - 1)).not.1 (by omega)
    simp only [bound_add, bound_nsmul, restrict, bound_div, nsmul_eq_mul, coeff_div] at h1 ⊢
    have : ∑ v ∈ S, I.coeff v * (τ v).toInt = c * ∑ v ∈ S, I.coeff v / c * (τ v).toInt := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun v _ => by rw [← mul_assoc, hmul]
    push_cast
    nlinarith
  · have h2 := (bound_div_le_iff (I := I) hc (y := (I.div c).bound)).1 le_rfl
    simp only [bound_add, bound_nsmul, restrict, bound_div, nsmul_eq_mul, coeff_div] at h2 ⊢
    have : ∑ v ∈ S, I.coeff v * (τ v).toInt = c * ∑ v ∈ S, I.coeff v / c * (τ v).toInt := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun v _ => by rw [← mul_assoc, hmul]
    push_cast
    nlinarith

/-! ### Semantics -/

omit [DecidableEq V] in
theorem offLit_eq (v : V) :
    offLit τ v = ⟨Finsupp.single v (if τ v then -1 else 1), -(τ v).toInt⟩ :=
  Ineq.ext (coeff_offLit v) (bound_offLit v)

/-- At an assignment agreeing with `τ` on `v`, the literal `ℓ̄ᵥ` is false: its two sides agree. -/
omit [DecidableEq V] in
theorem lhs_offLit_of_eq {σ : V → Bool} {v : V} (h : σ v = τ v) :
    (offLit τ v).lhs σ = (offLit τ v).bound := by
  rw [offLit_eq, lhs_mk_single, h]
  cases τ v <;> simp

theorem lhs_guard (σ : V → Bool) (h : ∀ v ∈ S, σ v = τ v) :
    (guard S τ).lhs σ = (guard S τ).bound := by
  simp only [guard, lhs_sum, bound_sum]
  exact Finset.sum_congr rfl fun v hv => lhs_offLit_of_eq (h v hv)

/-- Restriction is substitution: at an assignment agreeing with `τ` on `S`, `I↾ρ` and `I` have the
same truth value. -/
theorem holds_restrict_iff {σ : V → Bool} (h : ∀ v ∈ S, σ v = τ v) (I : Ineq V) :
    (I.restrict S τ).Holds σ ↔ I.Holds σ := by
  have hsplit : I = I.restrict S τ + ∑ v ∈ S, (offCoeff τ I v) • offLit τ v := by
    ext w
    · simp only [coeff_add, Finsupp.add_apply, coeff_sum, Finsupp.finsetSum_apply, coeff_zsmul,
        Finsupp.smul_apply, coeff_offLit, Finsupp.single_apply, coeff_restrict, smul_eq_mul,
        mul_ite, mul_zero, Finset.sum_ite_eq']
      by_cases hw : w ∈ S
      · simp only [hw, ↓reduceIte, offCoeff]; cases τ w <;> simp
      · simp [hw]
    · have hpt : ∀ v ∈ S, offCoeff τ I v * -(τ v).toInt = I.coeff v * (τ v).toInt := by
        intro v _
        unfold offCoeff
        rcases Bool.eq_false_or_eq_true (τ v) with ht | ht <;> simp [ht]
      simp only [bound_add, bound_sum, bound_zsmul, bound_offLit, restrict, smul_eq_mul]
      rw [Finset.sum_congr rfl hpt]
      ring
  have hl : ∀ v ∈ S, (offCoeff τ I v • offLit τ v).lhs σ =
      (offCoeff τ I v • offLit τ v).bound := by
    intro v hv
    rw [lhs_of_coeff_eq_smul σ (J := offLit τ v) (c := offCoeff τ I v) rfl, bound_zsmul,
      smul_eq_mul, lhs_offLit_of_eq (h v hv)]
  conv_rhs => rw [hsplit]
  unfold Holds
  rw [lhs_add, bound_add, lhs_sum, bound_sum, Finset.sum_congr rfl hl]
  constructor <;> intro h <;> linarith

/-- **The lifted line means the implication**: at an assignment agreeing with `τ` on `S`, the
line `D↾ρ + K • guard` holds exactly when `D` does. Elsewhere a false literal of the guard adds at
least `K`. -/
theorem holds_restrict_add_guard {σ : V → Bool} (h : ∀ v ∈ S, σ v = τ v) (I : Ineq V) (K : ℕ) :
    (I.restrict S τ + K • guard S τ).Holds σ ↔ I.Holds σ := by
  rw [← holds_restrict_iff h I]
  unfold Holds
  rw [lhs_add, bound_add, lhs_nsmul, bound_nsmul, lhs_guard σ h, nsmul_eq_mul]
  constructor <;> intro h <;> linarith

end Ineq

namespace CuttingPlanes

open Ineq

variable {V : Type*} [DecidableEq V] {S : Finset V} {τ : V → Bool} {Γ : Set (Ineq V)}

omit [DecidableEq V] in
theorem IsProof.literal {ls : List (Ineq V)} (h : IsProof Γ ls) (l : Literal V) :
    IsProof Γ (l.toIneq :: ls) := by
  obtain ⟨v, b⟩ := l
  cases b
  exacts [h.leOne v, h.nonneg v]

/-- Weakening a line by `m v` copies of `ℓ̄ᵥ` for every `v ∈ S`, in at most `3 |S|` lines. -/
theorem IsProof.addOffLits {ls : List (Ineq V)} (h : IsProof Γ ls) {I : Ineq V} (hI : I ∈ ls)
    (m : V → ℕ) (hm : ∀ v ∈ S, 0 < m v) :
    ∃ ext, IsProof Γ (ext ++ ls) ∧ I + ∑ v ∈ S, m v • offLit τ v ∈ ext ++ ls ∧
      ext.length ≤ 3 * #S := by
  induction S using Finset.induction_on with
  | empty => exact ⟨[], h, by simpa using hI, le_rfl⟩
  | @insert a S ha ih =>
    obtain ⟨ext, hp, hmem, hlen⟩ := ih fun v hv => hm v (mem_insert_of_mem hv)
    have h1 := hp.literal (a, !τ a)
    have h2 := h1.smul (m a) (hm a (mem_insert_self a S)) List.mem_cons_self
    have h3 := h2.add (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmem)) List.mem_cons_self
    refine ⟨_ :: _ :: _ :: ext, h3, ?_, ?_⟩
    · rw [sum_insert ha, add_left_comm, add_comm]
      exact List.mem_cons_self
    · rw [card_insert_of_notMem ha]; simp only [List.length_cons]; omega

/-- **Lemma 2 of the paper**: from a line `I`, derive `I↾ρ + K • guard` for `K = lemma2Bound S I`
in at most `3 |S|` further lines. -/
theorem IsProof.lemma2 {ls : List (Ineq V)} (h : IsProof Γ ls) {I : Ineq V} (hI : I ∈ ls) :
    ∃ ext, IsProof Γ (ext ++ ls) ∧
      I.restrict S τ + lemma2Bound S I • guard S τ ∈ ext ++ ls ∧ ext.length ≤ 3 * #S := by
  obtain ⟨ext, hp, hmem, hlen⟩ := h.addOffLits (S := S) (τ := τ) hI
    (fun v => ((lemma2Bound S I : ℤ) - offCoeff τ I v).toNat)
    (fun v hv => by have := offCoeff_lt τ I hv; omega)
  refine ⟨ext, hp, ?_, hlen⟩
  rwa [add_sum_offLit I _ fun v hv => (offCoeff_lt τ I hv).le] at hmem

/-- **Theorem 1 of the paper, for cutting planes**: a cutting planes proof from the restriction
`Γ↾ρ` lifts to one from `Γ` with at most `3 |S| + 1` lines per line, in which every line `D` of the
first proof appears as `D↾ρ + K • guard`, the implication `⋀_{ℓ ∈ ρ} ℓ ⇒ D↾ρ` with some
reification coefficient `K`. The lines of `Γ↾ρ` and the axioms are lifted by Lemma 2, addition and
multiplication line by line, and a division after weakening the guard to a multiple of the
divisor. Unlike the paper, the reification coefficient is not saturated, which cutting planes
cannot do. -/
theorem IsProof.lift {ls : List (Ineq V)} (h : IsProof (Ineq.restrict S τ '' Γ) ls) :
    ∃ ls', IsProof Γ ls' ∧ ls'.length ≤ (3 * #S + 1) * ls.length ∧
      ∀ D ∈ ls, ∃ K : ℕ, D.restrict S τ + K • guard S τ ∈ ls' := by
  induction h with
  | nil => exact ⟨[], .nil, by simp, by simp⟩
  | @hyp ls I h hI ih =>
    obtain ⟨ls', hp, hlen, hall⟩ := ih
    obtain ⟨C, hC, rfl⟩ := hI
    obtain ⟨ext, hp', hmem, hlen'⟩ := (hp.hyp hC).lemma2 (S := S) (τ := τ) List.mem_cons_self
    refine ⟨ext ++ C :: ls', hp', ?_, ?_⟩
    · simp only [List.length_append, List.length_cons]; rw [Nat.mul_succ]; omega
    · intro D hD
      rcases List.mem_cons.1 hD with rfl | hD
      · exact ⟨_, by rwa [restrict_restrict]⟩
      · obtain ⟨K, hK⟩ := hall D hD
        exact ⟨K, List.mem_append_right _ (List.mem_cons_of_mem _ hK)⟩
  | @nonneg ls h v ih =>
    obtain ⟨ls', hp, hlen, hall⟩ := ih
    obtain ⟨ext, hp', hmem, hlen'⟩ := (hp.nonneg v).lemma2 (S := S) (τ := τ) List.mem_cons_self
    refine ⟨ext ++ _ :: ls', hp', ?_, ?_⟩
    · simp only [List.length_append, List.length_cons]; rw [Nat.mul_succ]; omega
    · intro D hD
      rcases List.mem_cons.1 hD with rfl | hD
      · exact ⟨_, hmem⟩
      · obtain ⟨K, hK⟩ := hall D hD
        exact ⟨K, List.mem_append_right _ (List.mem_cons_of_mem _ hK)⟩
  | @leOne ls h v ih =>
    obtain ⟨ls', hp, hlen, hall⟩ := ih
    obtain ⟨ext, hp', hmem, hlen'⟩ := (hp.leOne v).lemma2 (S := S) (τ := τ) List.mem_cons_self
    refine ⟨ext ++ _ :: ls', hp', ?_, ?_⟩
    · simp only [List.length_append, List.length_cons]; rw [Nat.mul_succ]; omega
    · intro D hD
      rcases List.mem_cons.1 hD with rfl | hD
      · exact ⟨_, hmem⟩
      · obtain ⟨K, hK⟩ := hall D hD
        exact ⟨K, List.mem_append_right _ (List.mem_cons_of_mem _ hK)⟩
  | @add ls I J h hI hJ ih =>
    obtain ⟨ls', hp, hlen, hall⟩ := ih
    obtain ⟨KI, hKI⟩ := hall I hI
    obtain ⟨KJ, hKJ⟩ := hall J hJ
    refine ⟨_ :: ls', hp.add hKI hKJ, ?_, ?_⟩
    · simp only [List.length_cons]; rw [Nat.mul_succ]; omega
    · intro D hD
      rcases List.mem_cons.1 hD with rfl | hD
      · refine ⟨KI + KJ, ?_⟩
        rw [restrict_add, add_nsmul]
        convert List.mem_cons_self using 1
        abel
      · obtain ⟨K, hK⟩ := hall D hD
        exact ⟨K, List.mem_cons_of_mem _ hK⟩
  | @smul ls I h c hc hI ih =>
    obtain ⟨ls', hp, hlen, hall⟩ := ih
    obtain ⟨K, hK⟩ := hall I hI
    refine ⟨_ :: ls', hp.smul c hc hK, ?_, ?_⟩
    · simp only [List.length_cons]; rw [Nat.mul_succ]; omega
    · intro D hD
      rcases List.mem_cons.1 hD with rfl | hD
      · refine ⟨c * K, ?_⟩
        rw [restrict_nsmul, mul_nsmul]
        convert List.mem_cons_self using 1
        rw [smul_add, smul_comm]
      · obtain ⟨K, hK⟩ := hall D hD
        exact ⟨K, List.mem_cons_of_mem _ hK⟩
  | @div ls I h c hc hdvd hI ih =>
    obtain ⟨ls', hp, hlen, hall⟩ := ih
    obtain ⟨K, hK⟩ := hall I hI
    obtain ⟨ext, hp', hmem, hlen'⟩ := hp.addOffLits (S := S) (τ := τ) hK
      (fun _ => c * (K + 1) - K)
      (fun _ _ => by have : K + 1 ≤ c * (K + 1) := Nat.le_mul_of_pos_left _ hc; omega)
    have heq : I.restrict S τ + K • guard S τ + ∑ v ∈ S, (c * (K + 1) - K) • offLit τ v =
        I.restrict S τ + (c * (K + 1)) • guard S τ := by
      rw [← Finset.smul_sum, ← Ineq.guard, add_assoc, ← add_nsmul]
      congr 2
      have : K + 1 ≤ c * (K + 1) := Nat.le_mul_of_pos_left _ hc
      omega
    rw [heq] at hmem
    have hdvd' : ∀ v, (c : ℤ) ∣ (I.restrict S τ + (c * (K + 1)) • guard S τ).coeff v := by
      intro v
      simp only [coeff_add, Finsupp.add_apply, coeff_restrict, coeff_nsmul, Finsupp.smul_apply,
        nsmul_eq_mul]
      push_cast
      refine dvd_add ?_ (Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_refl _) _) _)
      split_ifs
      · exact dvd_zero _
      · exact hdvd v
    refine ⟨_ :: (ext ++ ls'), hp'.div c hc hdvd' hmem, ?_, ?_⟩
    · simp only [List.length_cons, List.length_append]; rw [Nat.mul_succ]; omega
    · intro D hD
      rcases List.mem_cons.1 hD with rfl | hD
      · exact ⟨K + 1, by rw [← div_restrict_add_guard hc hdvd K]; exact List.mem_cons_self⟩
      · obtain ⟨K', hK'⟩ := hall D hD
        exact ⟨K', List.mem_cons_of_mem _ (List.mem_append_right _ hK')⟩

/-- **Theorem 1 for cutting planes, as derivability**: if `D` has a derivation of at most `s` lines
from `Γ↾ρ`, then `D↾ρ + K • guard` has one of at most `(3 |S| + 1) s` lines from `Γ`, for some
reification coefficient `K`. -/
theorem DerivableInSize.lift {D : Ineq V} {s : ℕ}
    (h : DerivableInSize (Ineq.restrict S τ '' Γ) D s) :
    ∃ K : ℕ, DerivableInSize Γ (D.restrict S τ + K • guard S τ) ((3 * #S + 1) * s) := by
  obtain ⟨ls, hp, hD, hlen⟩ := h
  obtain ⟨ls', hp', hlen', hall⟩ := hp.lift (S := S) (τ := τ)
  obtain ⟨K, hK⟩ := hall D hD
  exact ⟨K, ls', hp', hK, hlen'.trans (Nat.mul_le_mul_left _ hlen)⟩

end CuttingPlanes

end

end Cslib.Logic.PL
