/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.GenericGroup.BabyStepGiantStep
public import CslibFrontier.Crypto.Computational.GenericGroup.Power
import CslibFrontier.Foundations.Data.Nat.Clog
import CslibFrontier.Foundations.Data.Nat.HalvingRecurrence

/-!
# Recursive discrete logarithm in prime-power-order groups

Algorithm RDL (`recursiveDlog`) of [BonehShoup2023], Section 16.1.2.1 (pp. 684–686), over
`GroupOracleSpec n S`: given a base `g` of order `q ^ e`, a target `u = α • g`, and a base-case
program `base` for order `q`, `recursiveDlog` splits `e` into `⌊e / 2⌋` and `e - ⌊e / 2⌋`,
computing `u · g^(-β)` as `u · g^(q^e - β)` via `power` and `product`.

Bounds count only oracle calls in the worst case over responses; every call is a product
(`GroupQuery.IsProduct`) when `base` makes only products (`queriesSatisfy_recursiveDlog`).
Constants `2` and `6` are this library's; exponent arithmetic and base-case table search are not
costed, and no machine-model bound is claimed.

## Main definitions

* `Cslib.Crypto.GenericGroup.recursiveDlog`: Algorithm RDL over `GroupOracleSpec n S`.

## Main results

* `Cslib.Crypto.GenericGroup.evalPure_recursiveDlog`,
  `Cslib.Crypto.GenericGroup.queriesSatisfy_recursiveDlog`,
  `Cslib.Crypto.GenericGroup.isQueryBounded_recursiveDlog`,
  `Cslib.Crypto.GenericGroup.recursiveDlog_two_pow`,
  `Cslib.Crypto.GenericGroup.evalPure_groupAnswer_recursiveDlog`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 16.1.2.1, pp. 684–686.
-/

public section

namespace Cslib.Crypto.GenericGroup

variable {n : ℕ} {S : Type}

/-- Algorithm RDL ([BonehShoup2023], Section 16.1.2.1, p. 685) over `GroupOracleSpec n S`. -/
def recursiveDlog (base : S → S → OracleComp (GroupOracleSpec n S) ℕ)
    (q e : ℕ) (g u : S) : OracleComp (GroupOracleSpec n S) ℕ :=
  if _h : e ≤ 1 then base g u else do
    let g₁ ← power g (q ^ (e - e / 2))
    let u₁ ← power u (q ^ (e - e / 2))
    let β ← recursiveDlog base q (e / 2) g₁ u₁
    let g₂ ← power g (q ^ (e / 2))
    let w ← power g (q ^ e - β)
    let u₂ ← product u w
    let γ ← recursiveDlog base q (e - e / 2) g₂ u₂
    pure (q ^ (e / 2) * γ + β)
termination_by e
decreasing_by all_goals omega

private theorem recursiveDlog_of_le_one
    (base : S → S → OracleComp (GroupOracleSpec n S) ℕ) (q : ℕ) {e : ℕ} (he : e ≤ 1) (g u : S) :
    recursiveDlog base q e g u = base g u := by
  rw [recursiveDlog]; split_ifs; rfl

private theorem recursiveDlog_of_one_lt
    (base : S → S → OracleComp (GroupOracleSpec n S) ℕ) (q : ℕ) {e : ℕ} (he : 1 < e) (g u : S) :
    recursiveDlog base q e g u = (do
      let g₁ ← power g (q ^ (e - e / 2)); let u₁ ← power u (q ^ (e - e / 2))
      let β ← recursiveDlog base q (e / 2) g₁ u₁
      let g₂ ← power g (q ^ (e / 2)); let w ← power g (q ^ e - β)
      let u₂ ← product u w; let γ ← recursiveDlog base q (e - e / 2) g₂ u₂
      pure (q ^ (e / 2) * γ + β)) := by
  rw [recursiveDlog]; simp only [show ¬e ≤ 1 by omega, ↓reduceDIte]

/-- Every query made by `recursiveDlog` is a product (`GroupQuery.IsProduct`) whenever `base`
makes only product queries. -/
theorem queriesSatisfy_recursiveDlog (base : S → S → OracleComp (GroupOracleSpec n S) ℕ)
    (hbase : ∀ g u, OracleComp.QueriesSatisfy GroupQuery.IsProduct (base g u))
    (q e : ℕ) (g u : S) :
    OracleComp.QueriesSatisfy GroupQuery.IsProduct (recursiveDlog base q e g u) := by
  fun_induction recursiveDlog base q e g u with
  | case1 e g u => exact hbase g u -- e ≤ 1: base solver
  | case2 e g u he ih₁ ih₂ => -- 1 < e: recurse on `e / 2` and `e - e / 2`
    exact .bind (queriesSatisfy_power _ _) fun g₁ =>
      .bind (queriesSatisfy_power _ _) fun u₁ =>
        .bind (ih₁ g₁ u₁) fun _ =>
          .bind (queriesSatisfy_power _ _) fun g₂ =>
            .bind (queriesSatisfy_power _ _) fun w =>
              .bind (queriesSatisfy_product _ _) fun u₂ =>
                .bind (ih₂ g₂ u₂) fun _ => .pure _

/-- Product-query bound for `recursiveDlog` when `2 ≤ q` and `1 ≤ e`, in the worst case over all
oracle responses. Constants `6` and `2` (in `power`) are this library's; exponent arithmetic and
base-case table search are not costed, and no machine-model bound is claimed. -/
theorem isQueryBounded_recursiveDlog {base : S → S → OracleComp (GroupOracleSpec n S) ℕ} {T : ℕ}
    (hbase : ∀ g u, OracleComp.IsQueryBounded (base g u) T) {q : ℕ} (hq : 2 ≤ q)
    (e : ℕ) (he : 1 ≤ e) (g u : S) :
    OracleComp.IsQueryBounded (recursiveDlog base q e g u)
      (e * T + 6 * e * Nat.clog 2 e * Nat.clog 2 q) := by
  fun_induction recursiveDlog base q e g u with
  | case1 e g u he1 => -- e ≤ 1: base solver
    obtain rfl : e = 1 := by omega
    simpa using hbase g u
  | case2 e g u he1 ih₁ ih₂ => -- 1 < e: recurse on `e / 2` and `e - e / 2`
    have he2 : 2 ≤ e := by omega
    set f := e / 2; set d := e - e / 2
    have hfd : f + d = e := by omega
    have hclog_f : Nat.clog 2 f + 1 ≤ Nat.clog 2 e :=
      Nat.clog_two_lt_clog_two_of_le_half he2 (by omega)
    have hclog_d : Nat.clog 2 d + 1 ≤ Nat.clog 2 e :=
      Nat.clog_two_lt_clog_two_of_le_half he2 (by omega)
    have hCq : 1 ≤ Nat.clog 2 q := Nat.clog_pos (by omega) (by omega)
    refine .mono (.bind (isQueryBounded_power g (q ^ d)) fun g₁ =>
      .bind (isQueryBounded_power u (q ^ d)) fun u₁ =>
        .bind (ih₁ g₁ u₁ (by omega)) fun β =>
          .bind (isQueryBounded_power g (q ^ f)) fun g₂ =>
            .bind ((isQueryBounded_power g (q ^ e - β)).mono
              (Nat.mul_le_mul_left 2 (Nat.log_mono_right (Nat.sub_le _ _)))) fun w =>
              .bind (isQueryBounded_product u w) fun u₂ =>
                .bind (ih₂ g₂ u₂ (by omega)) fun _ => .pure _ 0) ?_
    have hlog (m : ℕ) : Nat.log 2 (q ^ m) ≤ m * Nat.clog 2 q :=
      (Nat.log_le_clog 2 _).trans (Nat.clog_pow_le_mul 2 q m)
    have hT : f * T + d * T = e * T := by rw [← add_mul, hfd]
    have hstep : 4 * d + 2 * f + 2 * e + 1 ≤ 6 * e := by omega
    have hc : 4 * d + 2 * f + 2 * e + 6 * f * Nat.clog 2 f + 6 * d * Nat.clog 2 d + 1 ≤
        6 * e * Nat.clog 2 e := by nlinarith only [hfd, hclog_f, hclog_d, hstep]
    have hmul := Nat.mul_le_mul_right (Nat.clog 2 q) hc
    simp only [add_mul, one_mul, Nat.mul_assoc 4, Nat.mul_assoc 2] at hmul
    linarith [hT, hCq, hmul, hlog d, hlog f, hlog e]

/-- **Correctness.** For `s` of additive order `q ^ e` (`1 ≤ e`) and a base-case solver `base`
correct on order `q`, `recursiveDlog base q e (L s) (L (α * s))` outputs `α` for `α < q ^ e`. -/
theorem evalPure_recursiveDlog {L : ZMod n → S}
    {O : (query : GroupQuery n S) → GroupOracleSpec n S query}
    (hO : ∀ β₁ β₂, O (.op (L β₁) (L β₂) 1 1) = some (L (β₁ + β₂)))
    {base : S → S → OracleComp (GroupOracleSpec n S) ℕ} {q : ℕ}
    (hbase : ∀ t : ZMod n, addOrderOf t = q → ∀ a : ℕ, a < q →
      (base (L t) (L (a * t))).evalPure O = a)
    (e : ℕ) (he : 1 ≤ e) (s : ZMod n) (hs : addOrderOf s = q ^ e) (α : ℕ) (hα : α < q ^ e) :
    (recursiveDlog base q e (L s) (L (α * s))).evalPure O = α := by
  induction e using Nat.strong_induction_on generalizing s α with
  | ind e ih =>
    rcases Nat.eq_zero_or_pos q with rfl | hq_pos
    · simp [Nat.zero_pow (by omega : 0 < e)] at hα
    by_cases he1 : e ≤ 1
    · obtain rfl : e = 1 := by omega
      rw [recursiveDlog_of_le_one _ _ (le_refl 1)]
      exact hbase s (by simpa using hs) α (by simpa using hα)
    · set f := e / 2; set d := e - e / 2
      have hfd : f + d = e := by omega
      have hpow_fd : q ^ f * q ^ d = q ^ e := by rw [← pow_add, hfd]
      have hqd_pos : 0 < q ^ d := pow_pos hq_pos d
      have hqf_pos : 0 < q ^ f := pow_pos hq_pos f
      have hs_div {u v : ℕ} (hu : 0 < u) (huv : u * v = q ^ e) : addOrderOf ((u : ℕ) * s) = v := by
        rw [← nsmul_eq_mul, addOrderOf_nsmul_of_dvd hu.ne' (hs ▸ huv ▸ dvd_mul_right u v), hs,
          ← huv, Nat.mul_div_cancel_left _ hu]
      have hs₁ := hs_div hqd_pos (by rw [mul_comm, hpow_fd])
      have hpow_e_s' : (q : ZMod n) ^ e * s = 0 := by
        simpa [nsmul_eq_mul, hs] using addOrderOf_nsmul_eq_zero (x := s)
      have hu₁ : (q ^ d : ℕ) * ((α : ZMod n) * s) =
          ((α % q ^ f : ℕ) : ZMod n) * ((q ^ d : ℕ) * s) := by
        have hnat : q ^ d * α = (α / q ^ f) * q ^ e + (α % q ^ f) * q ^ d := by
          conv_lhs => rw [← Nat.div_add_mod α (q ^ f)]
          rw [← hpow_fd]; ring
        rw [← mul_assoc]; norm_cast; rw [hnat]; push_cast
        rw [add_mul, mul_assoc, hpow_e_s', mul_zero, zero_add, mul_assoc]
      have hβ : (recursiveDlog base q f (L ((q ^ d : ℕ) * s))
          (L ((q ^ d : ℕ) * ((α : ZMod n) * s)))).evalPure O = α % q ^ f := by
        rw [hu₁]; exact ih f (by omega) (by omega) _ hs₁ _ (Nat.mod_lt α hqf_pos)
      have hu₂ : (α : ZMod n) * s + ((q ^ e - α % q ^ f : ℕ) : ZMod n) * s =
          ((α / q ^ f : ℕ) : ZMod n) * ((q ^ f : ℕ) * s) := by
        have hle : α % q ^ f ≤ q ^ e := (Nat.mod_le α (q ^ f)).trans hα.le
        have hnat : α + (q ^ e - α % q ^ f) = (α / q ^ f) * q ^ f + q ^ e := by
          conv_lhs => lhs; rw [← Nat.div_add_mod α (q ^ f)]
          rw [Nat.mul_comm (q ^ f), Nat.add_assoc, Nat.add_sub_of_le hle]
        rw [← add_mul]; norm_cast; rw [hnat]; push_cast
        rw [add_mul, mul_assoc, hpow_e_s', add_zero]
      have hγ : (recursiveDlog base q d (L ((q ^ f : ℕ) * s))
          (L ((α : ZMod n) * s + ((q ^ e - α % q ^ f : ℕ) : ZMod n) * s))).evalPure O =
            α / q ^ f := by
        rw [hu₂]; exact ih d (by omega) (by omega) _ (hs_div hqf_pos hpow_fd) _
          ((Nat.div_lt_iff_lt_mul hqf_pos).mpr (by simpa [mul_comm, hpow_fd] using hα))
      rw [recursiveDlog_of_one_lt _ _ (by omega)]
      simp only [OracleComp.evalPure_bind, OracleComp.evalPure_pure]
      rw [evalPure_power hO _ hqd_pos, evalPure_power hO _ hqd_pos, hβ,
        evalPure_power hO _ hqf_pos,
        evalPure_power hO _ (Nat.sub_pos_of_lt ((Nat.mod_le α _).trans_lt hα)),
        evalPure_product hO, hγ, Nat.div_add_mod]

/-- **Groups of order `2 ^ ℓ`.** Specialization of `recursiveDlog` with `subgroupDlog 2` in
`ZMod (2 ^ ℓ)` ([BonehShoup2023], Section 16.1.2.2, p. 686, the case `n = 2 ^ ℓ`, using
Algorithm RDL of Section 16.1.2.1, p. 685). Every query is a product by
`queriesSatisfy_recursiveDlog` and `queriesSatisfy_subgroupDlog`; the constant `6` is this
library's and no machine-model bound is claimed. -/
theorem recursiveDlog_two_pow [DecidableEq S] {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {L : ZMod (2 ^ ℓ) → S}
    (hL : Function.Injective L) (α : ZMod (2 ^ ℓ)) :
    (recursiveDlog (subgroupDlog 2) 2 ℓ (L 1) (L α)).evalPure (answer L) = α.val ∧
      OracleComp.IsQueryBounded (recursiveDlog (subgroupDlog (q := 2 ^ ℓ) 2) 2 ℓ (L 1) (L α))
        (2 * ℓ + 6 * ℓ * Nat.clog 2 ℓ) := by
  have hO : ∀ β₁ β₂ : ZMod (2 ^ ℓ), answer L (.op (L β₁) (L β₂) 1 1) = some (L (β₁ + β₂)) :=
    fun β₁ β₂ => by rw [answer_op_label hL, one_mul, one_mul]
  refine ⟨?_, ?_⟩
  · simpa [mul_one, ZMod.natCast_zmod_val] using
      evalPure_recursiveDlog hO (fun _ ht _ ha => evalPure_subgroupDlog hL hO ht ha) ℓ hℓ 1
        (ZMod.addOrderOf_one (2 ^ ℓ)) α.val (ZMod.val_lt α)
  · have hb : ∀ g u : S, OracleComp.IsQueryBounded (subgroupDlog (q := 2 ^ ℓ) 2 g u) 2 :=
      fun g u => by simpa using isQueryBounded_subgroupDlog (q := 2 ^ ℓ) 2 g u
    simpa [show Nat.clog 2 2 = 1 by decide, mul_one, Nat.mul_comm ℓ 2] using
      isQueryBounded_recursiveDlog hb (by omega : 2 ≤ 2) ℓ hℓ (L 1) (L α)

/-- **Correctness against `groupAnswer`.** For a `ZMod n`-module `G` (`n ≠ 0`) and `g` of order
`q ^ e = n`, `recursiveDlog (subgroupDlog q) q e g (α • g)` outputs `α.val`. -/
theorem evalPure_groupAnswer_recursiveDlog [NeZero n] {G : Type} [AddCommGroup G]
    [Module (ZMod n) G] [DecidableEq G] {g : G}
    (hg : Function.Injective fun β : ZMod n => β • g)
    {q e : ℕ} (he : 1 ≤ e) (hq : q ^ e = n) (α : ZMod n) :
    (recursiveDlog (subgroupDlog q) q e g (α • g)).evalPure (groupAnswer n g) = α.val := by
  let L : ZMod n → G := fun β => β • g
  have hO : ∀ β₁ β₂ : ZMod n, groupAnswer n g (.op (L β₁) (L β₂) 1 1) = some (L (β₁ + β₂)) :=
    fun β₁ β₂ => by simp [L, groupAnswer, one_smul, add_smul]
  simpa [L, one_smul, mul_one, ZMod.natCast_zmod_val] using
    evalPure_recursiveDlog (q := q) hO (fun _ ht _ ha => evalPure_subgroupDlog hg hO ht ha) e he 1
      (by rw [ZMod.addOrderOf_one, hq]) α.val (hq ▸ ZMod.val_lt α)

end Cslib.Crypto.GenericGroup
