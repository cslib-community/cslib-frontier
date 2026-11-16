/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.DiffieHellman.CyclicGroupFamily
import CslibFrontier.Crypto.Computational.DiffieHellman.EvenOrder
import CslibFrontier.Crypto.Computational.DiffieHellman.SmallFactor
import CslibFrontier.Crypto.Negligible.InversePolynomial
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.WordsRoundTrip
import CslibFrontier.Probability.PMF.Uniform

/-!
# The small-prime-factor DDH test: checked instances and counterexamples

Concrete checks for `CslibFrontier/Crypto/Computational/DiffieHellman/SmallFactor.lean`,
`CslibFrontier/Crypto/Computational/DiffieHellman/EvenOrder.lean`, and
`CslibFrontier/Crypto/Computational/DiffieHellman/CyclicGroupFamily.lean` through ordinary
`module` imports of their public API:

* In `ZMod 15` (odd order `15`, where `EvenOrder` does not apply) with `g = 1` and `l = 3`: the
  fixed-group distinguisher evaluates by `decide` on a Diffie–Hellman triple and a
  non-Diffie–Hellman triple, `ddhAdvantage` is `14 / 27 ≥ 1 / 3`, and the random-world acceptance
  probability is `13 / 27`.
* In `(ZMod 7)ˣ` (order `6`) with generator `3` and prime factor `l = 3`, `ddhAdvantage` is
  `14 / 27`.
* Over cyclic group families: `oddFactorFamily` (order `3 * (2 * d + 1)`) has odd order
  everywhere and fails `DDH` via `not_ddh_of_polynomiallyBounded_minFac`;
  `alternatingFactorFamily` (order `(3 + 2 * (d % 2)) * (30 * d + 1)`) has no common constant
  prime divisor across its orders and fails `DDH` via `not_ddh_of_prime_factor` with the
  non-constant polynomial-time selector `d ↦ 3 + 2 * (d % 2)`; and
  `CyclicGroupFamily.ddhSmallFactorDistinguisher` evaluates by `decide` through the exposed API.
* Five hypothesis counterexamples: composite `l = 4` (`q = 12`), `l = 1` giving zero advantage
  (`q = 6`), non-divisor `l = 2` for `q = 3`, non-injective `g = 0` (`q = 6`, `l = 3`), and
  `trivialGroupFamily` (`q = 1`) satisfying `DDH` with `minFac 1 ≤ 1`.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.DiffieHellmanSmallFactor

open Cslib Cslib.Probability Cslib.Crypto Turing.MultiTapeTM
open scoped NNReal

/-! ### Fixed-group `ZMod 15` (`l = 3`) and parity specialization -/

private theorem zmod15_injective : Function.Injective fun c : ZMod 15 => c • (1 : ZMod 15) := by
  intro a b h
  simpa using h

-- The fixed-group distinguisher evaluates by `decide` on a DDH triple and a non-DDH triple.
example : ddhSmallFactorDistinguisher 15 3 (2 : ZMod 15) 6 12 = pure true :=
  congrArg pure (by decide)

example : ddhSmallFactorDistinguisher 15 3 (3 : ZMod 15) 4 1 = pure false :=
  congrArg pure (by decide)

example (q : ℕ) :
    ddhParityDistinguisher (G := ZMod q) q = ddhSmallFactorDistinguisher q 2 := rfl

example : (15 / 3) • ((6 : ZMod 15) • (1 : ZMod 15)) = 0 :=
  (div_nsmul_smul_eq_zero_iff (by decide : 3 ∣ 15) zmod15_injective 6).mpr ⟨2, rfl⟩

example : (15 / 3) • ((2 : ZMod 15) • (1 : ZMod 15)) ≠ 0 := fun h =>
  absurd ((div_nsmul_smul_eq_zero_iff (by decide : 3 ∣ 15) zmod15_injective 2).mp h) (by decide)

example :
    Pr[ddhRandomExperiment 15 (1 : ZMod 15) (ddhSmallFactorDistinguisher 15 3)] = 13 / 27 := by
  rw [probability_ddhRandomExperiment_ddhSmallFactorDistinguisher 15 3 1 (by decide)
    zmod15_injective]
  norm_num

/-- On `ZMod 15` (odd order `15`), `EvenOrder` does not apply, yet `l = 3` gives exact
advantage `((3 * 3 - 2) * (3 - 1)) / 3 ^ 3 = 14 / 27 ≥ 1 / 3`. -/
theorem zmod15_smallFactor_advantage :
    ¬ Even 15 ∧
      ddhAdvantage 15 (1 : ZMod 15) (ddhSmallFactorDistinguisher 15 3) = 14 / 27 ∧
      ((3 : ℝ≥0)⁻¹ ≤ ddhAdvantage 15 (1 : ZMod 15) (ddhSmallFactorDistinguisher 15 3)) := by
  have hp3 : Nat.Prime 3 := by decide
  have hd3 : 3 ∣ 15 := by decide
  refine ⟨by decide, ?_, inv_le_ddhAdvantage_ddhSmallFactorDistinguisher 15 3 1 hp3 hd3
    zmod15_injective⟩
  rw [ddhAdvantage_ddhSmallFactorDistinguisher 15 3 1 hp3 hd3 zmod15_injective, ← NNReal.coe_inj]
  simp only [Nat.cast_ofNat]
  rw [NNReal.coe_div, NNReal.coe_mul, NNReal.coe_sub (by norm_num),
    NNReal.coe_sub (by norm_num), NNReal.coe_pow]
  norm_num

/-! ### The group `(ZMod 7)ˣ` with prime factor `l = 3 ∣ 6` -/

section UnitsSmallFactor

attribute [local instance] neZero_sub_one_of_prime zmodUnitsModule

local instance : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩

private def zmod7Gen : (ZMod 7)ˣ := ZMod.unitOfCoprime 3 (by norm_num)

private theorem zmod7Gen_generates : ∀ x : (ZMod 7)ˣ, x ∈ Subgroup.zpowers zmod7Gen := by
  have horder : orderOf zmod7Gen = 6 := by
    rw [orderOf_eq_iff (by norm_num)]
    decide
  have htop : Subgroup.zpowers zmod7Gen = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, horder, Nat.card_eq_fintype_card, ZMod.card_units]
  intro x
  rw [htop]
  exact Subgroup.mem_top x

/-- On `(ZMod 7)ˣ` (order `6`, generated by `3`), applying
`ddhAdvantage_ddhSmallFactorDistinguisher` to `injective_smul_ofMul_units` at `l = 3` gives exact
advantage `14 / 27`. -/
theorem zmod7_units_l3_advantage :
    ddhAdvantage (7 - 1) (Additive.ofMul zmod7Gen)
        (ddhSmallFactorDistinguisher (7 - 1) 3) = 14 / 27 := by
  rw [ddhAdvantage_ddhSmallFactorDistinguisher (7 - 1) 3 (Additive.ofMul zmod7Gen)
      (by decide) (by decide) (injective_smul_ofMul_units 7 zmod7Gen_generates),
    ← NNReal.coe_inj]
  simp only [Nat.cast_ofNat]
  rw [NNReal.coe_div, NNReal.coe_mul, NNReal.coe_sub (by norm_num),
    NNReal.coe_sub (by norm_num), NNReal.coe_pow]
  norm_num

end UnitsSmallFactor

/-! ### Hypothesis counterexamples -/

section Counterexamples

/-- `dvd_val_mul_iff` and `eval_ddhRealExperiment_ddhSmallFactorDistinguisher = PMF.pure true`
fail when `l` is composite (`q = 12`, `l = 4`, `a = b = 2`). -/
theorem composite_factor_counterexample :
    (4 ∣ ((2 : ZMod 12) * 2).val ∧
      ¬ ((12 / 4) • ((2 : ZMod 12) • (1 : ZMod 12)) = 0 ∨
        (12 / 4) • ((2 : ZMod 12) • (1 : ZMod 12)) = 0)) ∧
    ProbComp.eval (ddhRealExperiment 12 (1 : ZMod 12) (ddhSmallFactorDistinguisher 12 4)) ≠
      PMF.pure true := by
  refine ⟨by decide, fun heq => ?_⟩
  have hfalse : false ∈
      (ProbComp.eval (ddhRealExperiment 12 (1 : ZMod 12)
        (ddhSmallFactorDistinguisher 12 4))).support := by
    simp only [ddhRealExperiment, ddhSmallFactorDistinguisher, ProbComp.eval_bind,
      ProbComp.eval_pure, ProbComp.eval_uniform, PMF.mem_support_bind_iff,
      Cslib.Probability.PMF.mem_support_uniformOfFintype, PMF.mem_support_pure_iff,
      true_and]
    exact ⟨2, 2, by decide⟩
  rw [heq, PMF.mem_support_pure_iff] at hfalse
  exact Bool.false_ne_true hfalse

/-- When `l = 1` (excluded by `l.Prime`), `ddhSmallFactorDistinguisher q 1` accepts identically
in both experiments and has zero advantage (`q = 6`). -/
theorem one_factor_zero_advantage :
    ddhAdvantage 6 (1 : ZMod 6) (ddhSmallFactorDistinguisher 6 1) = 0 := by
  have h6 : ∀ x : ZMod 6, (6 / 1) • x = 0 := by decide
  have hreal : ProbComp.eval (ddhRealExperiment 6 (1 : ZMod 6)
      (ddhSmallFactorDistinguisher 6 1)) = PMF.pure true := by
    simp only [ddhRealExperiment, ddhSmallFactorDistinguisher, h6, ProbComp.eval_bind,
      ProbComp.eval_uniform, ProbComp.eval_pure, PMF.bind_const]
    congr 1
  have hrand : ProbComp.eval (ddhRandomExperiment 6 (1 : ZMod 6)
      (ddhSmallFactorDistinguisher 6 1)) = PMF.pure true := by
    simp only [ddhRandomExperiment, ddhSmallFactorDistinguisher, h6, ProbComp.eval_bind,
      ProbComp.eval_uniform, ProbComp.eval_pure, PMF.bind_const]
    congr 1
  simp only [ddhAdvantage, Experiment.advantage, hreal, hrand, Game.advantage_self]

/-- When `l ∤ q` (`q = 3`, `l = 2`), `div_nsmul_smul_eq_zero_iff` fails at `a = 2 : ZMod 3`. -/
theorem not_dvd_order_counterexample :
    ¬ ((3 / 2) • ((2 : ZMod 3) • (1 : ZMod 3)) = 0 ↔ 2 ∣ (2 : ZMod 3).val) := by
  decide

/-- When `g` is not injective (`q = 6`, `l = 3`, `g = 0 : ZMod 6`),
`div_nsmul_smul_eq_zero_iff` fails at `a = 1 : ZMod 6`. -/
theorem non_injective_generator_counterexample :
    ¬ ((6 / 3) • ((1 : ZMod 6) • (0 : ZMod 6)) = 0 ↔ 3 ∣ (1 : ZMod 6).val) := by
  decide

end Counterexamples

/-! ### Concrete `CyclicGroupFamily` checks -/

section ConcreteFamilies

/-- Trivial cyclic group family of order `1` everywhere (`ZMod 1`). -/
private def trivialGroupFamily : CyclicGroupFamily where
  Desc := Unit
  encDesc := ⟨fun _ => [], fun _ _ _ => rfl⟩
  order _ := 1
  order_ne_zero _ := one_ne_zero
  Carrier _ := ZMod 1
  addCommGroup _ := inferInstance
  module _ := inferInstance
  generator _ := 0
  card_carrier _ := by simp
  smul_generator_injective _ a b _ := Subsingleton.elim a b
  encode _ _ := []
  encode_injective _ a b _ := Subsingleton.elim a b
  add _ := []
  add_encode _ _ _ := rfl
  smul _ := []
  smul_encode _ _ _ := rfl
  computableInPolyTime_order := ComputableInPolyTime.const 1
  computableInPolyTime_generator := ComputableInPolyTime.const []
  computableInPolyTime_add := ComputableInPolyTime.const []
  computableInPolyTime_smul := ComputableInPolyTime.const []

/-- In `trivialGroupFamily` (`q = 1`, `Nat.minFac 1 = 1`), `DDH` holds despite `minFac 1 ≤ 1`:
the strict `1 < F.order d` hypothesis in `not_ddh_of_polynomiallyBounded_minFac` cannot be
omitted. -/
theorem ddh_trivialGroupFamily :
    (∀ n, ∀ d ∈ ((fun _ : ℕ => PMF.pure () : ℕ → PMF trivialGroupFamily.Desc) n).support,
      (trivialGroupFamily.order d).minFac ≤ 1) ∧
    trivialGroupFamily.DDH (fun _ => PMF.pure ()) := by
  refine ⟨fun _ _ _ => by simp [trivialGroupFamily], fun D _ => ?_⟩
  have hzero : ∀ n,
      (trivialGroupFamily.ddhRealGame (fun _ => PMF.pure ()) D n).advantage
        (trivialGroupFamily.ddhRandomGame (fun _ => PMF.pure ()) D n) = 0 := by
    intro n
    have hEq :
        trivialGroupFamily.ddhRealGame (fun _ => PMF.pure ()) D n =
          trivialGroupFamily.ddhRandomGame (fun _ => PMF.pure ()) D n := by
      simp only [CyclicGroupFamily.ddhRealGame, CyclicGroupFamily.ddhRandomGame, Game.withSetup]
      congr 1; funext d
      simp only [ddhRealExperiment, ddhRandomExperiment, ProbComp.eval_bind, ProbComp.eval_uniform]
      congr 1; funext a; congr 1; funext b
      have hgen : ∀ x : trivialGroupFamily.Carrier d, x = trivialGroupFamily.generator d :=
        fun x => Subsingleton.elim (α := ZMod 1) x _
      rw [hgen ((a * b) • _), hgen (a • _), hgen (b • _)]
      symm
      calc ((PMF.uniformOfFintype (ZMod (trivialGroupFamily.order d))).bind fun c =>
              ProbComp.eval (D n d (trivialGroupFamily.generator d) (trivialGroupFamily.generator d)
                (c • trivialGroupFamily.generator d)))
          = (PMF.uniformOfFintype (ZMod (trivialGroupFamily.order d))).bind fun _ =>
              ProbComp.eval (D n d (trivialGroupFamily.generator d) (trivialGroupFamily.generator d)
                (trivialGroupFamily.generator d)) := by
            congr 1
        _ = ProbComp.eval (D n d (trivialGroupFamily.generator d) (trivialGroupFamily.generator d)
              (trivialGroupFamily.generator d)) := PMF.bind_const _ _
    rw [hEq, Game.advantage_self]
  exact negligible_zero.congr' (Filter.Eventually.of_forall fun n => (hzero n).symm)

private def oddOrder (d : ℕ) : ℕ := 3 * (2 * d + 1)

private def oddOrderAdd : ℕ × List Bool × List Bool → List Bool
  | (d, x, y) => ((ofBits x + ofBits y) % oddOrder d).bits

private def oddOrderSMul : ℕ × ℕ × List Bool → List Bool
  | (d, a, x) => (a * ofBits x % oddOrder d).bits

/-- Concrete odd-order cyclic group family of order `3 * (2 * d + 1)`: `EvenOrder` never
applies, yet `not_ddh_of_polynomiallyBounded_minFac` refutes `DDH`. -/
private def oddFactorFamily : CyclicGroupFamily where
  Desc := ℕ
  encDesc := encNat
  order := oddOrder
  order_ne_zero d := by simp [oddOrder]
  Carrier d := ZMod (oddOrder d)
  addCommGroup d := inferInstance
  module d := inferInstance
  generator _ := 1
  card_carrier d := Nat.card_zmod (oddOrder d)
  smul_generator_injective d a b hab := by simpa using hab
  encode _ x := x.val.bits
  encode_injective d x y hxy := by
    have : NeZero (oddOrder d) := ⟨by simp [oddOrder]⟩
    exact ZMod.val_injective _ (encNat.injective hxy)
  add := oddOrderAdd
  add_encode d x y := by
    have : NeZero (oddOrder d) := ⟨by simp [oddOrder]⟩
    simp only [oddOrderAdd, ofBits_bits, ZMod.val_add]
  smul := oddOrderSMul
  smul_encode d a x := by
    have : NeZero (oddOrder d) := ⟨by simp [oddOrder]⟩
    simp only [oddOrderSMul, ofBits_bits, smul_eq_mul, ZMod.val_mul, ZMod.val_natCast,
      Nat.mod_mul_mod]
  computableInPolyTime_order := by
    unfold oddOrder
    fun_prop
  computableInPolyTime_generator := by
    have h1 : ∀ d : ℕ, ((1 : ZMod (oddOrder d)).val) = 1 := fun d =>
      ZMod.val_one'' (by simp [oddOrder])
    simp only [h1]
    exact ComputableInPolyTime.const _
  computableInPolyTime_add := by
    unfold oddOrderAdd oddOrder
    fun_prop
  computableInPolyTime_smul := by
    unfold oddOrderSMul oddOrder
    fun_prop

-- `CyclicGroupFamily.ddhSmallFactorDistinguisher` evaluates by `decide` on `oddFactorFamily` at
-- `d = 2` (order `15`), confirming `@[expose]` works across `module` imports.
example :
    let d : oddFactorFamily.Desc := show ℕ from 2
    CyclicGroupFamily.ddhSmallFactorDistinguisher oddFactorFamily (fun _ _ => 3)
        0 d (2 : ZMod 15) (6 : ZMod 15) (12 : ZMod 15) = pure true :=
  congrArg pure (by decide)

example :
    let d : oddFactorFamily.Desc := show ℕ from 2
    CyclicGroupFamily.ddhSmallFactorDistinguisher oddFactorFamily (fun _ _ => 3)
        0 d (3 : ZMod 15) (4 : ZMod 15) (1 : ZMod 15) = pure false :=
  congrArg pure (by decide)

example :
    CyclicGroupFamily.ddhParityDistinguisher oddFactorFamily =
      CyclicGroupFamily.ddhSmallFactorDistinguisher oddFactorFamily (fun _ _ => 2) := rfl

/-- `oddFactorFamily` has odd order everywhere (so `not_ddh_of_even_order` does not apply),
and fails `DDH` by `not_ddh_of_polynomiallyBounded_minFac` with `bound _ := 3`. -/
theorem oddFactorFamily_not_ddh :
    (∀ d : oddFactorFamily.Desc, ¬ Even (oddFactorFamily.order d)) ∧
    ¬ oddFactorFamily.DDH (fun n => PMF.pure n) := by
  refine ⟨fun d => ?_, ?_⟩
  · change ℕ at d
    simp only [oddFactorFamily, oddOrder, Nat.not_even_iff_odd]
    exact ⟨3 * d + 1, by ring⟩
  · refine CyclicGroupFamily.not_ddh_of_polynomiallyBounded_minFac oddFactorFamily (fun _ => 3)
      (polynomiallyBounded_iff_le.2 ⟨3, 0, fun _ => by simp⟩)
      (Filter.Eventually.of_forall fun n d hd => ?_).frequently
    have hdn : d = n := (PMF.mem_support_pure_iff n d).mp hd
    dsimp only [oddFactorFamily, oddOrder] at hdn ⊢
    rw [hdn]
    exact ⟨by omega, Nat.minFac_le_of_dvd (by norm_num) ⟨2 * n + 1, rfl⟩⟩

private def altFactor (d : ℕ) : ℕ := 3 + 2 * (d % 2)

private def altOrder (d : ℕ) : ℕ := altFactor d * (30 * d + 1)

private theorem altOrder_ne_zero (d : ℕ) : altOrder d ≠ 0 := by
  simp only [altOrder, altFactor, ne_eq, mul_eq_zero]
  omega

private def altOrderAdd : ℕ × List Bool × List Bool → List Bool
  | (d, x, y) => ((ofBits x + ofBits y) % altOrder d).bits

private def altOrderSMul : ℕ × ℕ × List Bool → List Bool
  | (d, a, x) => (a * ofBits x % altOrder d).bits

/-- Odd-order family whose orders `(3 + 2 * (d % 2)) * (30 * d + 1)` share no constant prime
factor across `d` (`order 0 = 3`, `order 1 = 155`). -/
private def alternatingFactorFamily : CyclicGroupFamily where
  Desc := ℕ
  encDesc := encNat
  order := altOrder
  order_ne_zero := altOrder_ne_zero
  Carrier d := ZMod (altOrder d)
  addCommGroup d := inferInstance
  module d := inferInstance
  generator _ := 1
  card_carrier d := Nat.card_zmod (altOrder d)
  smul_generator_injective d a b hab := by simpa using hab
  encode _ x := x.val.bits
  encode_injective d x y hxy := by
    have : NeZero (altOrder d) := ⟨altOrder_ne_zero d⟩
    exact ZMod.val_injective _ (encNat.injective hxy)
  add := altOrderAdd
  add_encode d x y := by
    have : NeZero (altOrder d) := ⟨altOrder_ne_zero d⟩
    simp only [altOrderAdd, ofBits_bits, ZMod.val_add]
  smul := altOrderSMul
  smul_encode d a x := by
    have : NeZero (altOrder d) := ⟨altOrder_ne_zero d⟩
    simp only [altOrderSMul, ofBits_bits, smul_eq_mul, ZMod.val_mul, ZMod.val_natCast,
      Nat.mod_mul_mod]
  computableInPolyTime_order := by
    unfold altOrder altFactor
    fun_prop
  computableInPolyTime_generator := by
    have h1 : ∀ d : ℕ, ((1 : ZMod (altOrder d)).val) = 1 := fun d =>
      ZMod.val_one'' (by
        refine ne_of_gt ?_
        calc
          1 < 3 := by omega
          _ ≤ 3 + 2 * (d % 2) := by omega
          _ ≤ altOrder d := Nat.le_mul_of_pos_right _ (by omega))
    simp only [h1]
    exact ComputableInPolyTime.const _
  computableInPolyTime_add := by
    unfold altOrderAdd altOrder altFactor
    fun_prop
  computableInPolyTime_smul := by
    unfold altOrderSMul altOrder altFactor
    fun_prop

/-- `alternatingFactorFamily` fails `DDH` via `not_ddh_of_prime_factor` with the non-constant
polynomial-time selector `d ↦ 3 + 2 * (d % 2)` (which outputs `3` on `d = 0` and `5` on `d = 1`).
-/
theorem alternatingFactorFamily_not_ddh :
    altFactor 0 ≠ altFactor 1 ∧
      ¬ alternatingFactorFamily.DDH (fun n => PMF.pure n) := by
  refine ⟨by decide, ?_⟩
  refine CyclicGroupFamily.not_ddh_of_prime_factor alternatingFactorFamily (fun _ d => altFactor d)
    ?_ (fun _ => 5) (polynomiallyBounded_iff_le.2 ⟨5, 0, fun _ => by simp⟩)
    (Filter.Eventually.of_forall fun n d hd => ?_).frequently
  · unfold altFactor
    fun_prop
  · have hdn : d = n := (PMF.mem_support_pure_iff n d).mp hd
    rw [hdn]
    change (altFactor n).Prime ∧ altFactor n ∣ altOrder n ∧ altFactor n ≤ 5
    refine ⟨?_, ⟨30 * n + 1, rfl⟩, ?_⟩
    · simp only [altFactor]
      rcases Nat.mod_two_eq_zero_or_one n with h | h <;> rw [h] <;> decide
    · simp only [altFactor]
      have := Nat.mod_lt n (by norm_num : 0 < 2)
      omega

end ConcreteFamilies

end CslibFrontierTests.Crypto.DiffieHellmanSmallFactor
