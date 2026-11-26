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

Unsaturated cutting-planes steps after Lemma 2 and Theorem 1 of [Demirović, McCreesh, McIlree,
Nordström, Oertel and Sidorov][DemirovicMcCreeshMcIlreeNordstromOertelSidorov2024] (Appendix A.2).
The paper's Theorem 1 says that a proof can reason "as if reifications were not present": a
derivation of `D` from the restriction `F↾ρ` of `F` by a partial assignment `ρ` lifts to a
derivation of `⋀_{ℓ ∈ ρ} ℓ ⇒ D` from `F`, with `O(n)` lines per line. Its proof system is
pseudo-Boolean cutting planes with saturation over normalized constraints, together with RUP. This
file proves the corresponding lifting for the integer cutting-planes system
`Cslib.Logic.PL.CuttingPlanes`, which has neither saturation nor RUP; it is not the paper's
Theorem 1. Lifting saturation and RUP steps, and VeriPB derivations, remains open in #7222.

The partial assignment is `τ` on a finite set `S` of variables. The restriction
`Cslib.Logic.PL.Ineq.restrict` substitutes its values (equation (27)), and the implication with
reification coefficient `K` is `D↾ρ + K • guard S τ`, where `Cslib.Logic.PL.Ineq.guard` sums the
literals that `ρ` makes false. For `K` at least the degree `Cslib.Logic.PL.Ineq.degree` of `D↾ρ`
(the reification coefficient of §2.1, which equation (31) uses for `C↾ρ`), it holds exactly when
`⋀_{v ∈ S} xᵥ = τ v ⇒ D` does (`Cslib.Logic.PL.Ineq.holds_restrict_add_guard`). The lifting
(`Cslib.Logic.PL.CuttingPlanes.IsProof.lift`) follows the paper's proof:

* a line of `F↾ρ` or an axiom is lifted after Lemma 2, adding `(K - sᵥ) ℓ̄ᵥ` for each `v ∈ S`
  (`Cslib.Logic.PL.CuttingPlanes.IsProof.restrict_add_guard`);
* sums and multiples are lifted line by line;
* a division by `c` first weakens the guard to the multiple `c (K + 1)`, so that `c` divides it,
  and then divides (`Cslib.Logic.PL.Ineq.add_nsmul_div`, `Cslib.Logic.PL.Ineq.restrict_div`).

**Deviations from the paper.** Without saturation, the reification coefficient grows along the
proof instead of being saturated back to the degree; every line carries one at least its degree,
so it still means the implication. RUP steps (the paper's Case 6) are not cutting-planes steps and
are not covered. The size bound is explicit: at most `3 |S| + 1` lines per line.

Wrapping (§2.2) is the case `ρ = {z ↦ 1}`: a derivation of `D` from `C` gives one of `z ⇒ D` from
`z ⇒ C` (`Cslib.Logic.PL.CuttingPlanes.DerivableInSize.wrap`).

## Main definitions

* `Cslib.Logic.PL.Ineq.restrict`, `Cslib.Logic.PL.Ineq.guard`: restriction by a partial assignment,
  and its guard.
* `Cslib.Logic.PL.Ineq.degree`: the degree of an inequality, as a normalized constraint.
* `Cslib.Logic.PL.Ineq.guardLiftBound`: the reification coefficient of a lifted line of `F↾ρ`.

## Main results

* `Cslib.Logic.PL.Ineq.degree_le_iff`: the degree is the largest shortfall of an assignment.
* `Cslib.Logic.PL.Ineq.holds_restrict_add_guard`: a lifted line with a reification coefficient at
  least its degree means the implication.
* `Cslib.Logic.PL.CuttingPlanes.IsProof.restrict_add_guard`: the guard lifting of one line, after
  Lemma 2 of the paper.
* `Cslib.Logic.PL.CuttingPlanes.IsProof.lift`, `Cslib.Logic.PL.CuttingPlanes.DerivableInSize.lift`:
  lifting a cutting-planes derivation under a partial assignment.
* `Cslib.Logic.PL.CuttingPlanes.DerivableInSize.wrap`: wrapping under a reification.

## References

* [E. Demirović, C. McCreesh, M. J. McIlree, J. Nordström, A. Oertel, K. Sidorov, *Pseudo-Boolean
  Reasoning About States and Transitions to Certify Dynamic Programming and Decision Diagram
  Algorithms*][DemirovicMcCreeshMcIlreeNordstromOertelSidorov2024]
-/

public section

namespace Cslib.Logic.PL

noncomputable section

open Finset

namespace Ineq

variable {V : Type*}

/-! ### The degree -/

/-- **The degree** of `I` as a normalized pseudo-Boolean constraint: the reification coefficient
`K = A − ∑ᵢ min(cᵢ, 0)` of §2.1 of the paper (p. 9:3), called the degree in the proof of its
Theorem 1 (Case 1, p. 9:19). Writing `aᵥ xᵥ` as `aᵥ + |aᵥ| (1 - xᵥ)` for every negative `aᵥ`
turns `I` into a constraint over literals with natural coefficients and bound
`b - ∑_{aᵥ < 0} aᵥ`, here clamped at `0`. -/
def degree (I : Ineq V) : ℕ := (I.bound + I.coeff.sum fun _ a => ((-a).toNat : ℤ)).toNat

/-- No assignment falls short of the bound of `I` by more than its degree. -/
theorem bound_sub_lhs_le_degree (σ : V → Bool) (I : Ineq V) : I.bound - I.lhs σ ≤ I.degree := by
  have h : -(I.coeff.sum fun _ a => ((-a).toNat : ℤ)) ≤ I.lhs σ := by
    rw [lhs_eq_finsuppSum, Finsupp.sum, Finsupp.sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun v _ => ?_
    cases σ v
    · simp
    · simp only [Bool.toInt_true, mul_one]; omega
  have := Int.self_le_toNat (I.bound + I.coeff.sum fun _ a => ((-a).toNat : ℤ))
  rw [degree]; omega

/-- **The degree is the largest shortfall**: `I.degree ≤ n` iff no assignment falls short of the
bound of `I` by more than `n`. The assignment setting exactly the negative coefficients attains
the degree. -/
theorem degree_le_iff {I : Ineq V} {n : ℕ} : I.degree ≤ n ↔ ∀ σ, I.bound - I.lhs σ ≤ n := by
  refine ⟨fun h σ => (bound_sub_lhs_le_degree σ I).trans (by exact_mod_cast h), fun h => ?_⟩
  have hσ : I.lhs (fun v => decide (I.coeff v < 0)) =
      -(I.coeff.sum fun _ a => ((-a).toNat : ℤ)) := by
    rw [lhs_eq_finsuppSum, Finsupp.sum, Finsupp.sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun v _ => by
      by_cases hv : I.coeff v < 0 <;> simp [hv] <;> omega
  have := h fun v => decide (I.coeff v < 0)
  rw [degree, Int.toNat_le]; omega

theorem degree_add_le (I J : Ineq V) : (I + J).degree ≤ I.degree + J.degree :=
  degree_le_iff.2 fun σ => by
    have := bound_sub_lhs_le_degree σ I
    have := bound_sub_lhs_le_degree σ J
    rw [bound_add, lhs_add]; push_cast; linarith

theorem degree_nsmul_le (c : ℕ) (I : Ineq V) : (c • I).degree ≤ c * I.degree :=
  degree_le_iff.2 fun σ => by
    rw [bound_nsmul, lhs_nsmul, nsmul_eq_mul, ← mul_sub]; push_cast
    exact mul_le_mul_of_nonneg_left (bound_sub_lhs_le_degree σ I) (Int.natCast_nonneg c)

/-- Division by a positive integer dividing every coefficient does not raise the degree. -/
theorem degree_div_le {I : Ineq V} {c : ℕ} (hc : 0 < c) (hdvd : ∀ v, (c : ℤ) ∣ I.coeff v) :
    (I.div c).degree ≤ I.degree :=
  degree_le_iff.2 fun σ => by
    have h := bound_sub_lhs_le_degree σ I
    have hl := lhs_of_coeff_eq_smul σ (smul_coeff_div hdvd).symm
    have hc' : (1 : ℤ) ≤ c := by exact_mod_cast hc
    have hd : (0 : ℤ) ≤ I.degree := Int.natCast_nonneg _
    have := (bound_div_le_iff hc (I := I) (y := (I.div c).lhs σ + I.degree)).2 (by nlinarith)
    linarith

/-- Adding `c m` times `J` commutes with division by `c`. -/
theorem add_nsmul_div {c : ℕ} (hc : 0 < c) (I J : Ineq V) (m : ℕ) :
    (I + (c * m) • J).div c = I.div c + m • J := by
  have hc' : (c : ℤ) ≠ 0 := by exact_mod_cast hc.ne'
  ext w
  · simp only [coeff_div, coeff_add, coeff_nsmul, Finsupp.add_apply, Finsupp.smul_apply,
      nsmul_eq_mul]
    push_cast
    rw [show I.coeff w + c * m * J.coeff w = I.coeff w + (m * J.coeff w) * c by ring,
      Int.add_mul_ediv_right _ _ hc']
  · simp only [bound_div, bound_add, bound_nsmul, nsmul_eq_mul]
    push_cast
    rw [show -(I.bound + c * m * J.bound) = -I.bound + (-(m * J.bound)) * c by ring,
      Int.add_mul_ediv_right _ _ hc']
    ring

/-! ### Restriction and the guard -/

variable [DecidableEq V] (S : Finset V) (τ : V → Bool)

/-- The inequality of the literal on `v` that `τ` makes false: `xᵥ ≥ 0` if `τ v` is false and
`1 - xᵥ ≥ 0` if `τ v` is true. -/
private def offLit (v : V) : Ineq V := Literal.toIneq (v, !τ v)

/-- **The guard** of the partial assignment `τ` on `S`: `∑_{v ∈ S} ℓ̄ᵥ ≥ 0`, the sum of the
literals it makes false. With a reification coefficient `K` at least the degree of `D`,
`D + K • guard S τ` is the implication `⋀_{v ∈ S} ℓᵥ ⇒ D` of the paper. -/
def guard : Ineq V := ∑ v ∈ S, offLit τ v

/-- **The restriction** `D↾ρ` of `D` by the partial assignment `ρ` that is `τ` on `S`: every
variable of `S` is replaced by its value (equation (27) of the paper). -/
def restrict (I : Ineq V) : Ineq V :=
  ⟨I.coeff.filter (· ∉ S), I.bound - ∑ v ∈ S, I.coeff v * (τ v).toInt⟩

variable {S τ}

omit [DecidableEq V] in
private theorem coeff_offLit (v : V) :
    (offLit τ v).coeff = Finsupp.single v (if τ v then -1 else 1) := by
  cases h : τ v <;> simp [offLit, h]

omit [DecidableEq V] in
private theorem bound_offLit (v : V) : (offLit τ v).bound = -(τ v).toInt := by
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

@[simp] theorem bound_restrict (I : Ineq V) :
    (I.restrict S τ).bound = I.bound - ∑ v ∈ S, I.coeff v * (τ v).toInt := by
  rw [restrict]

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

/-- Restriction commutes with division by a positive integer dividing every coefficient. -/
theorem restrict_div {I : Ineq V} {c : ℕ} (hc : 0 < c) (hdvd : ∀ v, (c : ℤ) ∣ I.coeff v) :
    (I.div c).restrict S τ = (I.restrict S τ).div c := by
  have hmul : ∀ v, (c : ℤ) * (I.coeff v / c) = I.coeff v := fun v => Int.mul_ediv_cancel' (hdvd v)
  have hsum : ∑ v ∈ S, I.coeff v * (τ v).toInt = c * ∑ v ∈ S, I.coeff v / c * (τ v).toInt := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun v _ => by rw [← mul_assoc, hmul]
  refine (div_eq_of hc ?_ ?_ ?_).symm
  · ext w
    simp only [coeff_restrict, coeff_div, Finsupp.smul_apply, smul_eq_mul]
    split_ifs <;> simp [hmul]
  · have h1 := (bound_div_le_iff (I := I) hc (y := (I.div c).bound - 1)).not.1 (by omega)
    simp only [bound_restrict, coeff_div, hsum]
    nlinarith
  · have h2 := (bound_div_le_iff (I := I) hc (y := (I.div c).bound)).1 le_rfl
    simp only [bound_restrict, coeff_div, hsum]
    nlinarith

variable (S τ) in
/-- The reification coefficient of the lifted line of `I`, after Lemma 2 of the paper: the degree
of `I↾ρ`, so that the lifted line means the implication, plus enough to make every multiplier of
the lifting positive. -/
def guardLiftBound (I : Ineq V) : ℕ := 1 + (I.restrict S τ).degree + ∑ v ∈ S, (I.coeff v).natAbs

theorem degree_restrict_le_guardLiftBound (I : Ineq V) :
    (I.restrict S τ).degree ≤ guardLiftBound S τ I := by
  unfold guardLiftBound; omega

/-- The signed coefficient of `ℓ̄ᵥ` in `I`: `I = I↾ρ + ∑_{v ∈ S} sᵥ ℓ̄ᵥ`. -/
private def offCoeff (τ : V → Bool) (I : Ineq V) (v : V) : ℤ :=
  if τ v then -I.coeff v else I.coeff v

private theorem offCoeff_lt (I : Ineq V) {v : V} (hv : v ∈ S) :
    offCoeff τ I v < guardLiftBound S τ I := by
  have h1 : (I.coeff v).natAbs ≤ ∑ v ∈ S, (I.coeff v).natAbs :=
    Finset.single_le_sum_of_canonicallyOrdered (f := fun v => (I.coeff v).natAbs) hv
  have h2 : offCoeff τ I v ≤ ((I.coeff v).natAbs : ℤ) := by
    rw [Int.natCast_natAbs]; unfold offCoeff; split_ifs
    exacts [neg_le_abs _, le_abs_self _]
  have h3 : ((I.coeff v).natAbs : ℤ) ≤ ((∑ v ∈ S, (I.coeff v).natAbs : ℕ) : ℤ) := by
    exact_mod_cast h1
  have h4 : (0 : ℤ) ≤ ((I.restrict S τ).degree : ℤ) := Int.natCast_nonneg _
  simp only [guardLiftBound, Nat.cast_add, Nat.cast_one]
  linarith

/-- **The identity behind the lifting after Lemma 2**: adding `(K - sᵥ) ℓ̄ᵥ ≥ 0` to `I` for every
`v ∈ S` gives `I↾ρ + K • guard`. -/
private theorem add_sum_offLit (I : Ineq V) (K : ℕ) (hK : ∀ v ∈ S, offCoeff τ I v ≤ K) :
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
    simp only [bound_add, bound_sum, bound_nsmul, bound_offLit, bound_restrict, bound_guard,
      nsmul_eq_mul]
    rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]
    ring

theorem restrict_of_coeff_eq_zero {I : Ineq V} (h : ∀ v ∈ S, I.coeff v = 0) :
    I.restrict S τ = I := by
  ext w
  · exact (coeff_restrict I w).trans (ite_eq_right_iff.2 fun hw => (h w hw).symm)
  · rw [bound_restrict, Finset.sum_eq_zero fun v hv => by rw [h v hv, zero_mul], sub_zero]

theorem restrict_guard : (guard S τ).restrict S τ = 0 := by
  ext w
  · rw [coeff_restrict, coeff_guard]; split_ifs <;> simp_all
  · simp only [bound_restrict, bound_guard, coeff_guard, bound_zero]
    rw [Finset.sum_congr rfl fun v hv => show (if v ∈ S then (if τ v then -1 else 1) else 0) *
      (τ v).toInt = -(τ v).toInt by cases τ v <;> simp [hv]]
    simp

/-! ### Semantics -/

omit [DecidableEq V] in
private theorem offLit_eq (v : V) :
    offLit τ v = ⟨Finsupp.single v (if τ v then -1 else 1), -(τ v).toInt⟩ :=
  Ineq.ext (coeff_offLit v) (bound_offLit v)

omit [DecidableEq V] in
/-- The literal `ℓ̄ᵥ` is false at an assignment agreeing with `τ` on `v`, and true elsewhere. -/
private theorem slack_offLit (σ : V → Bool) (v : V) :
    (offLit τ v).lhs σ - (offLit τ v).bound = if σ v = τ v then 0 else 1 := by
  rw [offLit_eq, lhs_mk_single]
  cases σ v <;> cases τ v <;> simp

omit [DecidableEq V] in
private theorem lhs_guard (σ : V → Bool) (h : ∀ v ∈ S, σ v = τ v) :
    (guard S τ).lhs σ = (guard S τ).bound := by
  simp only [guard, lhs_sum, bound_sum]
  exact Finset.sum_congr rfl fun v hv => by
    have := slack_offLit (τ := τ) σ v; simp only [h v hv, ↓reduceIte] at this; omega

omit [DecidableEq V] in
/-- At an assignment disagreeing with `τ` somewhere on `S`, the guard exceeds its bound. -/
private theorem one_le_slack_guard {σ : V → Bool} {v : V} (hv : v ∈ S) (hne : σ v ≠ τ v) :
    1 ≤ (guard S τ).lhs σ - (guard S τ).bound := by
  simp only [guard, lhs_sum, bound_sum, ← Finset.sum_sub_distrib]
  calc (1 : ℤ) = (offLit τ v).lhs σ - (offLit τ v).bound := by simp [slack_offLit, hne]
    _ ≤ _ := Finset.single_le_sum (f := fun w => (offLit τ w).lhs σ - (offLit τ w).bound)
        (fun w _ => by rw [slack_offLit]; split_ifs <;> simp) hv

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
      simp only [bound_add, bound_sum, bound_zsmul, bound_offLit, bound_restrict, smul_eq_mul]
      rw [Finset.sum_congr rfl hpt]
      ring
  have hl : ∀ v ∈ S, (offCoeff τ I v • offLit τ v).lhs σ =
      (offCoeff τ I v • offLit τ v).bound := by
    intro v hv
    have := slack_offLit (τ := τ) σ v
    simp only [h v hv, ↓reduceIte] at this
    rw [lhs_of_coeff_eq_smul σ (J := offLit τ v) (c := offCoeff τ I v) rfl, bound_zsmul,
      smul_eq_mul]
    congr 1; omega
  conv_rhs => rw [hsplit]
  unfold Holds
  rw [lhs_add, bound_add, lhs_sum, bound_sum, Finset.sum_congr rfl hl]
  constructor <;> intro h <;> linarith

/-- At an assignment agreeing with `τ` on `S`, the line `D↾ρ + K • guard` holds exactly when `D`
does, for every `K`. -/
private theorem holds_restrict_add_guard_of_eq {σ : V → Bool} (h : ∀ v ∈ S, σ v = τ v)
    (I : Ineq V) (K : ℕ) : (I.restrict S τ + K • guard S τ).Holds σ ↔ I.Holds σ := by
  rw [← holds_restrict_iff h I]
  unfold Holds
  rw [lhs_add, bound_add, lhs_nsmul, bound_nsmul, lhs_guard σ h, nsmul_eq_mul]
  constructor <;> intro h <;> linarith

/-- **The lifted line means the implication**: for a reification coefficient `K` at least the
degree of `D↾ρ`, the line `D↾ρ + K • guard` holds exactly when `⋀_{v ∈ S} xᵥ = τ v ⇒ D` does. At
an assignment extending `ρ` it is `D`; elsewhere a false literal of the guard adds at least `K`,
which covers any shortfall of `D↾ρ`. -/
theorem holds_restrict_add_guard {σ : V → Bool} {I : Ineq V} {K : ℕ}
    (hK : (I.restrict S τ).degree ≤ K) :
    (I.restrict S τ + K • guard S τ).Holds σ ↔ ((∀ v ∈ S, σ v = τ v) → I.Holds σ) := by
  by_cases h : ∀ v ∈ S, σ v = τ v
  · exact (holds_restrict_add_guard_of_eq h I K).trans ⟨fun hI _ => hI, fun hI => hI h⟩
  · push Not at h
    obtain ⟨v, hv, hne⟩ := h
    refine iff_of_true ?_ fun h' => absurd (h' v hv) hne
    have hd := bound_sub_lhs_le_degree σ (I.restrict S τ)
    have hg := one_le_slack_guard hv hne
    have hK' : ((I.restrict S τ).degree : ℤ) ≤ K := by exact_mod_cast hK
    unfold Holds
    rw [lhs_add, bound_add, lhs_nsmul, bound_nsmul, nsmul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left hg (Int.natCast_nonneg K)]

end Ineq

namespace CuttingPlanes

open Ineq

variable {V : Type*} [DecidableEq V] {S : Finset V} {τ : V → Bool} {Γ : Set (Ineq V)}

omit [DecidableEq V] in
private theorem IsProof.literal {ls : List (Ineq V)} (h : IsProof Γ ls) (l : Literal V) :
    IsProof Γ (l.toIneq :: ls) := by
  obtain ⟨v, _ | _⟩ := l
  exacts [h.leOne v, h.nonneg v]

omit [DecidableEq V] in
/-- Weakening a line by `m v` copies of `ℓ̄ᵥ` for every `v ∈ S`, in at most `3 |S|` lines. -/
private theorem IsProof.addOffLits {ls : List (Ineq V)} (h : IsProof Γ ls) {I : Ineq V}
    (hI : I ∈ ls) (m : V → ℕ) (hm : ∀ v ∈ S, 0 < m v) :
    ∃ ext, IsProof Γ (ext ++ ls) ∧ I + ∑ v ∈ S, m v • offLit τ v ∈ ext ++ ls ∧
      ext.length ≤ 3 * #S := by
  classical
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

/-- **The guard lifting of a line**, an unsaturated cutting-planes step after Lemma 2 of
[Demirović, McCreesh, McIlree, Nordström, Oertel and
Sidorov][DemirovicMcCreeshMcIlreeNordstromOertelSidorov2024] (whose saturated pseudo-Boolean
version is open in #7222): from a line `I`, derive `I↾ρ + K • guard` for
`K = guardLiftBound S τ I`, which is at least the degree of `I↾ρ`
(`Cslib.Logic.PL.Ineq.degree_restrict_le_guardLiftBound`), in at most `3 |S|` further lines. -/
theorem IsProof.restrict_add_guard {ls : List (Ineq V)} (h : IsProof Γ ls) {I : Ineq V}
    (hI : I ∈ ls) :
    ∃ ext, IsProof Γ (ext ++ ls) ∧
      I.restrict S τ + guardLiftBound S τ I • guard S τ ∈ ext ++ ls ∧ ext.length ≤ 3 * #S := by
  obtain ⟨ext, hp, hmem, hlen⟩ := h.addOffLits (S := S) (τ := τ) hI
    (fun v => ((guardLiftBound S τ I : ℤ) - offCoeff τ I v).toNat)
    (fun v hv => by have := offCoeff_lt (τ := τ) I hv; omega)
  refine ⟨ext, hp, ?_, hlen⟩
  rwa [add_sum_offLit I _ fun v hv => (offCoeff_lt I hv).le] at hmem

/-- One step of the lifting for a line `I` of `Γ↾ρ` or an axiom: the line `J` with
`J↾ρ = I↾ρ` joins the lifted proof and is lifted by `IsProof.restrict_add_guard`. -/
private theorem lift_axiom {ls ls' : List (Ineq V)} {I J : Ineq V} (hp : IsProof Γ (J :: ls'))
    (hlen : ls'.length ≤ (3 * #S + 1) * ls.length)
    (hall : ∀ D ∈ ls, ∃ K : ℕ, (D.restrict S τ).degree ≤ K ∧
      D.restrict S τ + K • guard S τ ∈ ls')
    (hIJ : I.restrict S τ = J.restrict S τ) :
    ∃ ls'', IsProof Γ ls'' ∧ ls''.length ≤ (3 * #S + 1) * (I :: ls).length ∧
      ∀ D ∈ I :: ls, ∃ K : ℕ, (D.restrict S τ).degree ≤ K ∧
        D.restrict S τ + K • guard S τ ∈ ls'' := by
  obtain ⟨ext, hp', hmem, hlen'⟩ := hp.restrict_add_guard (S := S) (τ := τ) List.mem_cons_self
  refine ⟨ext ++ J :: ls', hp', ?_, ?_⟩
  · simp only [List.length_append, List.length_cons]; rw [Nat.mul_succ]; omega
  · intro D hD
    rcases List.mem_cons.1 hD with rfl | hD
    · exact ⟨guardLiftBound S τ J, hIJ ▸ degree_restrict_le_guardLiftBound J, hIJ ▸ hmem⟩
    · exact (hall D hD).imp fun _ h => ⟨h.1, List.mem_append_right _ (List.mem_cons_of_mem _ h.2)⟩

/-- **Lifting a cutting planes proof under a partial assignment**, an unsaturated cutting-planes
step after Theorem 1 of [Demirović, McCreesh, McIlree, Nordström, Oertel and
Sidorov][DemirovicMcCreeshMcIlreeNordstromOertelSidorov2024]. It is not that theorem, whose proof
system is pseudo-Boolean cutting planes with saturation, plus RUP (its Case 6); lifting those, and
VeriPB derivations, is open in #7222.

A cutting planes proof from the restriction `Γ↾ρ` lifts to one from `Γ` with at most
`3 |S| + 1` lines per line, in which every line `D` of the first proof appears as
`D↾ρ + K • guard` with a reification coefficient `K` at least the degree of `D↾ρ`, so that it
means the implication `⋀_{ℓ ∈ ρ} ℓ ⇒ D` (`Cslib.Logic.PL.Ineq.holds_restrict_add_guard`). The
lines of `Γ↾ρ` and the axioms are lifted by `IsProof.restrict_add_guard`, addition and
multiplication line by line, and a division after weakening the guard to a multiple of the
divisor. -/
theorem IsProof.lift {ls : List (Ineq V)} (h : IsProof (Ineq.restrict S τ '' Γ) ls) :
    ∃ ls', IsProof Γ ls' ∧ ls'.length ≤ (3 * #S + 1) * ls.length ∧
      ∀ D ∈ ls, ∃ K : ℕ, (D.restrict S τ).degree ≤ K ∧ D.restrict S τ + K • guard S τ ∈ ls' := by
  induction h with
  | nil => exact ⟨[], .nil, by simp, by simp⟩
  | @hyp ls I h hI ih =>
    obtain ⟨ls', hp, hlen, hall⟩ := ih
    obtain ⟨C, hC, rfl⟩ := hI
    exact lift_axiom (hp.hyp hC) hlen hall (restrict_restrict C)
  | @nonneg ls h v ih =>
    obtain ⟨ls', hp, hlen, hall⟩ := ih
    exact lift_axiom (hp.nonneg v) hlen hall rfl
  | @leOne ls h v ih =>
    obtain ⟨ls', hp, hlen, hall⟩ := ih
    exact lift_axiom (hp.leOne v) hlen hall rfl
  | @add ls I J h hI hJ ih =>
    obtain ⟨ls', hp, hlen, hall⟩ := ih
    obtain ⟨KI, hdI, hKI⟩ := hall I hI
    obtain ⟨KJ, hdJ, hKJ⟩ := hall J hJ
    refine ⟨_ :: ls', hp.add hKI hKJ, ?_, ?_⟩
    · simp only [List.length_cons]; rw [Nat.mul_succ]; omega
    · intro D hD
      rcases List.mem_cons.1 hD with rfl | hD
      · refine ⟨KI + KJ, ?_, ?_⟩
        · rw [restrict_add]; exact (degree_add_le _ _).trans (Nat.add_le_add hdI hdJ)
        · rw [restrict_add, add_nsmul]
          convert List.mem_cons_self using 1
          abel
      · exact (hall D hD).imp fun _ h => ⟨h.1, List.mem_cons_of_mem _ h.2⟩
  | @smul ls I h c hc hI ih =>
    obtain ⟨ls', hp, hlen, hall⟩ := ih
    obtain ⟨K, hd, hK⟩ := hall I hI
    refine ⟨_ :: ls', hp.smul c hc hK, ?_, ?_⟩
    · simp only [List.length_cons]; rw [Nat.mul_succ]; omega
    · intro D hD
      rcases List.mem_cons.1 hD with rfl | hD
      · refine ⟨c * K, ?_, ?_⟩
        · rw [restrict_nsmul]; exact (degree_nsmul_le c _).trans (Nat.mul_le_mul_left c hd)
        · rw [restrict_nsmul, mul_nsmul]
          convert List.mem_cons_self using 1
          rw [smul_add, smul_comm]
      · exact (hall D hD).imp fun _ h => ⟨h.1, List.mem_cons_of_mem _ h.2⟩
  | @div ls I h c hc hdvd hI ih =>
    obtain ⟨ls', hp, hlen, hall⟩ := ih
    obtain ⟨K, hd, hK⟩ := hall I hI
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
    have hdvdr : ∀ v, (c : ℤ) ∣ (I.restrict S τ).coeff v := fun v => by
      rw [coeff_restrict]; split_ifs
      exacts [dvd_zero _, hdvd v]
    have hdvd' : ∀ v, (c : ℤ) ∣ (I.restrict S τ + (c * (K + 1)) • guard S τ).coeff v := by
      intro v
      simp only [coeff_add, Finsupp.add_apply, coeff_nsmul, Finsupp.smul_apply, nsmul_eq_mul]
      push_cast
      exact dvd_add (hdvdr v) (Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_refl _) _) _)
    refine ⟨_ :: (ext ++ ls'), hp'.div c hc hdvd' hmem, ?_, ?_⟩
    · simp only [List.length_cons, List.length_append]; rw [Nat.mul_succ]; omega
    · intro D hD
      rcases List.mem_cons.1 hD with rfl | hD
      · refine ⟨K + 1, ?_, ?_⟩
        · rw [restrict_div hc hdvd]
          exact (degree_div_le hc hdvdr).trans (hd.trans (Nat.le_succ K))
        · rw [restrict_div hc hdvd, ← add_nsmul_div hc]
          exact List.mem_cons_self
      · exact (hall D hD).imp fun _ h =>
          ⟨h.1, List.mem_cons_of_mem _ (List.mem_append_right _ h.2)⟩

/-- **Lifting a derivation under a partial assignment**, the unsaturated cutting-planes step of
`Cslib.Logic.PL.CuttingPlanes.IsProof.lift`: if `D` has a derivation of at most `s` lines from
`Γ↾ρ`, then `D↾ρ + K • guard` has one of at most `(3 |S| + 1) s` lines from `Γ`, for some
reification coefficient `K` at least the degree of `D↾ρ`. -/
theorem DerivableInSize.lift {D : Ineq V} {s : ℕ}
    (h : DerivableInSize (Ineq.restrict S τ '' Γ) D s) :
    ∃ K : ℕ, (D.restrict S τ).degree ≤ K ∧
      DerivableInSize Γ (D.restrict S τ + K • guard S τ) ((3 * #S + 1) * s) := by
  obtain ⟨ls, hp, hD, hlen⟩ := h
  obtain ⟨ls', hp', hlen', hall⟩ := hp.lift (S := S) (τ := τ)
  obtain ⟨K, hd, hK⟩ := hall D hD
  exact ⟨K, hd, ls', hp', hK, hlen'.trans (Nat.mul_le_mul_left _ hlen)⟩

omit [DecidableEq V] in
/-- **Wrapping** (§2.2 of the paper), the case `ρ = {z ↦ 1}` of
`Cslib.Logic.PL.CuttingPlanes.DerivableInSize.lift`: a derivation of `D` from `C` gives one of
`z ⇒ D` from `z ⇒ C`, for a variable `z` in neither, with four lines per line. Here `z ⇒ C` is
`C + K₀ (1 - x_z) ≥ 0`, which means the implication when `K₀` is at least the degree of `C`, and
`z ⇒ D` is `D + K (1 - x_z) ≥ 0` for some `K` at least the degree of `D`. -/
theorem DerivableInSize.wrap {C D : Ineq V} {z : V} {s : ℕ} (hC : C.coeff z = 0)
    (hD : D.coeff z = 0) (K₀ : ℕ) (h : DerivableInSize {C} D s) :
    ∃ K : ℕ, D.degree ≤ K ∧ DerivableInSize {C + K₀ • guard {z} (fun _ => true)}
      (D + K • guard {z} (fun _ => true)) (4 * s) := by
  classical
  have hΓ : Ineq.restrict {z} (fun _ => true) '' {C + K₀ • guard {z} (fun _ => true)} = {C} := by
    rw [Set.image_singleton, restrict_add, restrict_nsmul, restrict_guard, smul_zero, add_zero,
      restrict_of_coeff_eq_zero (by simpa using hC)]
  rw [← hΓ] at h
  obtain ⟨K, hd, hK⟩ := h.lift
  rw [restrict_of_coeff_eq_zero (by simpa using hD)] at hd hK
  exact ⟨K, hd, by rwa [Finset.card_singleton] at hK⟩

end CuttingPlanes

end

end Cslib.Logic.PL
