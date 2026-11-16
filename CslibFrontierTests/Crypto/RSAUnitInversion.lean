/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.RSAUnitInversion
import CslibFrontier.Crypto.Computational.RSAUnitInversion.Converse
import CslibFrontier.Crypto.Computational.UnitSampling
import Mathlib.Tactic.NormNum.Prime

/-!
# RSA with a uniform unit preimage: checked instances

Checks for `CslibFrontier/Crypto/Computational/RSAUnitInversion.lean`:

* For `N = 33 = 3 * 11` and `e = 3`, the non-unit `6` encrypts to `18`, and `rsaNonUnitRoot`
  recovers `6` from `(33, 3, 18)` alone, as `rsaNonUnitRoot_rsaEval` says. It is the root
  `rsaInvert 33 7 18` of the private exponent (`rsaNonUnitRoot_eq_rsaInvert`); the two differ on
  the unit `2`, and on `33`, which is not below the modulus.
* `p = 2` is allowed: for `N = 10 = 2 * 5` and `e = 3`, the non-units `4` and `5` are their own
  images, and `rsaNonUnitRoot` returns them. So is `e = 1`.
* The branch `y = 0` is needed: the general branch would return `rsaInvert 33 0 0 = 1` for the
  root of `0`, since `BinaryGcd.modInv 3 0 = 0`.
* RSA evaluation keeps units and non-units apart (`coprime_rsaEval_iff`).
* Both certificates apply: `computableInPolyTime_rsaNonUnitRoot` on three inputs read as nested
  pairs on `encNat`, and `isPPT_unitRSAToRSA` on the inverter that returns its challenge.
* Converse bounds (`RSAUnitInversion/Converse.lean`, `UnitSampling.lean`):
  `dist_uniformOfFintype_zmod_units_lt` at `5 * 7`, `dist_uniformOfFintype_zmod_units` at `33`,
  `succProbability_rsaInversionGame_le_of_nonUnitFrac_le` at `desc33` and `echo`,
  `succProbability_rsaInversionGame_le_of_size` at `desc35` (`e = d = 5`, `ℓ = 3`) and `echo`, a
  satisfiable `RSAGen` family with at least `n`-bit primes instantiating `RSAUnitOneWay.rsaOneWay`
  and `rsaOneWay_iff_rsaUnitOneWay`, and counterexamples at `N = 6` (`p = 2`, `q = 3`, `ℓ = 3`) and
  `N = 10` (`p = 2`, `q = 5`, `ℓ = 3`) showing why the prime bit-length hypothesis is required.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.RSAUnitInversion

open Cslib Cslib.Crypto Turing.MultiTapeTM

/-- The key `N = 33`, `e = 3`, `d = 7`: `3 * 7 = 21 ≡ 1 [MOD 20]`. -/
def desc33 : RSADesc :=
  { p := 3, q := 11, e := 3, d := 7, hp := by norm_num, hq := by norm_num, hpq := by decide,
    he := by decide, hed := by decide }

/-- A key with `p = 2`: `N = 10`, `e = 3`, `d = 3`, with `3 * 3 = 9 ≡ 1 [MOD 4]`. -/
def desc10 : RSADesc :=
  { p := 2, q := 5, e := 3, d := 3, hp := by norm_num, hq := by norm_num, hpq := by decide,
    he := by decide, hed := by decide }

/-- A key with `e = 1`: `N = 10`, `e = d = 1`. -/
def desc10One : RSADesc :=
  { p := 2, q := 5, e := 1, d := 1, hp := by norm_num, hq := by norm_num, hpq := by decide,
    he := by decide, hed := by decide }

/-! ### The root of a non-unit -/

/-- `6 ^ 3 = 216 ≡ 18 [MOD 33]`; `gcd 18 33 = 3`, so the exponent is the inverse `7` of `3`
modulo `(3 - 1) * (11 - 1) = 20`, and `18 ^ 7 ≡ 6 [MOD 33]`. -/
example : rsaEval 33 3 6 = 18 := by decide

example : rsaNonUnitRoot 33 3 18 = 6 := by
  unfold rsaNonUnitRoot BinaryGcd.modInv
  decide

example : rsaNonUnitRoot 33 3 (rsaEval 33 3 6) = 6 :=
  rsaNonUnitRoot_rsaEval desc33 (x := 6) (by decide) (by decide)

/-- The private exponent `d = 7` gives the same root of `18`. -/
example : rsaNonUnitRoot 33 3 18 = rsaInvert 33 7 18 :=
  rsaNonUnitRoot_eq_rsaInvert desc33 (by decide) (by decide)

/-- Both hypotheses of `rsaNonUnitRoot_eq_rsaInvert` are needed. On the unit `2` the exponent
found is `0`, so the root returned is `1`, and `2 ^ 7 % 33 = 29`. On `33`, which is not coprime to
the modulus and not below it, the root returned is again `1`, and `33 ^ 7 % 33 = 0`. -/
example : rsaNonUnitRoot 33 3 2 = 1 ∧ rsaInvert 33 7 2 = 29 := by
  unfold rsaNonUnitRoot BinaryGcd.modInv
  decide

example : rsaNonUnitRoot 33 3 33 = 1 ∧ rsaInvert 33 7 33 = 0 := by
  unfold rsaNonUnitRoot BinaryGcd.modInv
  decide

/-- With `p = 2`: `4 ^ 3 ≡ 4` and `5 ^ 3 ≡ 5 [MOD 10]`, and the roots are `4` and `5`. -/
example : rsaEval 10 3 4 = 4 ∧ rsaEval 10 3 5 = 5 := by decide

example : rsaNonUnitRoot 10 3 4 = 4 ∧ rsaNonUnitRoot 10 3 5 = 5 := by
  unfold rsaNonUnitRoot BinaryGcd.modInv
  decide

example : rsaNonUnitRoot 10 3 (rsaEval 10 3 4) = 4 :=
  rsaNonUnitRoot_rsaEval desc10 (x := 4) (by decide) (by decide)

/-- With `e = 1`, RSA evaluation is the identity and so is the root. -/
example : rsaNonUnitRoot 10 1 (rsaEval 10 1 6) = 6 :=
  rsaNonUnitRoot_rsaEval desc10One (x := 6) (by decide) (by decide)

/-- The branch `y = 0` is needed: `BinaryGcd.modInv 3 0 = 0`, and `0 ^ 0 % 33 = 1`. -/
example : BinaryGcd.modInv 3 ((Nat.gcd 0 33 - 1) * (33 / Nat.gcd 0 33 - 1)) = 0 ∧
    rsaInvert 33 0 0 = 1 := by
  unfold BinaryGcd.modInv
  decide

example : rsaNonUnitRoot 33 3 (rsaEval 33 3 0) = 0 :=
  rsaNonUnitRoot_rsaEval desc33 (x := 0) (by decide) (by decide)

/-! ### Units and non-units -/

/-- `5` is a unit modulo `33` and so is its image `5 ^ 3 % 33 = 26`; `6` is not, nor is `18`. -/
example : Nat.Coprime (rsaEval 33 3 5) 33 ∧ ¬ Nat.Coprime (rsaEval 33 3 6) 33 :=
  ⟨(coprime_rsaEval_iff desc33 5).mpr (by decide),
    fun h => absurd ((coprime_rsaEval_iff desc33 6).mp h) (by decide)⟩

/-! ### Certificates -/

example : ComputableInPolyTime
    (fun a : ℕ × ℕ × ℕ => rsaNonUnitRoot (a.1 + 1) a.2.1 a.2.2)
    (encPair encNat (encPair encNat encNat)) encNat :=
  computableInPolyTime_rsaNonUnitRoot (by fun_prop) (by fun_prop) (by fun_prop)
    fun _ => Nat.succ_pos _

/-- The inverter that returns its challenge. -/
noncomputable def echo : RSAInverter := fun _ _ y => pure y

theorem isPPT_echo : echo.IsPPT :=
  ((ComputableInPolyTime.isPPTOn (f := fun x : RSAInput => (x.challenge : ℕ))
    (by fun_prop))).congr fun _ => by simp [echo]

example : (unitRSAToRSA echo).IsPPT := isPPT_unitRSAToRSA isPPT_echo

section Converse

open Cslib.Probability
open scoped NNReal ENNReal Cslib.Probability.PMF

/-! ### Exercises 10.25–10.26 converse bounds and counterexamples -/

example :
    dist (PMF.uniformOfFintype (ZMod (5 * 7)))
      ((PMF.uniformOfFintype (ZMod (5 * 7))ˣ).map Units.val) < (4 : ℝ) / 2 ^ 3 :=
  dist_uniformOfFintype_zmod_units_lt (by decide) (by decide) (by decide) (by decide) (by decide)

example :
    dist (PMF.uniformOfFintype (ZMod 33))
      ((PMF.uniformOfFintype (ZMod 33)ˣ).map Units.val) = 13 / 33 := by
  have htot : Nat.totient 33 = 20 := by decide
  rw [dist_uniformOfFintype_zmod_units 33, htot]
  norm_num

example (n : ℕ) :
    (rsaInversionGame (fun _ => PMF.pure desc33) echo n).succProbability ≤
      (rsaUnitInversionGame (fun _ => PMF.pure desc33) echo n).succProbability + 13 / 33 :=
  succProbability_rsaInversionGame_le_of_nonUnitFrac_le _ echo fun desc hdesc => by
    simp only [PMF.support_pure, Set.mem_singleton_iff] at hdesc
    subst hdesc
    have htot : Nat.totient 33 = 20 := by decide
    norm_num [desc33, htot]

private def desc35 : RSADesc where
  p := 5
  q := 7
  e := 5
  d := 5
  hp := by decide
  hq := by decide
  hpq := by decide
  he := by decide
  hed := by decide

example (n : ℕ) :
    (rsaInversionGame (fun _ => PMF.pure desc35) echo n).succProbability ≤
      (rsaUnitInversionGame (fun _ => PMF.pure desc35) echo n).succProbability + 4 / 2 ^ 3 :=
  succProbability_rsaInversionGame_le_of_size _ echo fun desc hdesc => by
    simp only [PMF.support_pure, Set.mem_singleton_iff] at hdesc
    subst hdesc
    decide

private noncomputable def largePrimeDesc (n : ℕ) : RSADesc :=
  let hpSpec := Nat.exists_infinite_primes (2 ^ n)
  let p := hpSpec.choose
  let qSpec := Nat.exists_infinite_primes (p + 1)
  let q := qSpec.choose
  { p := p
    q := q
    e := 1
    d := 1
    hp := hpSpec.choose_spec.2
    hq := qSpec.choose_spec.2
    hpq := by have := qSpec.choose_spec.1; omega
    he := Nat.coprime_one_left _
    hed := rfl }

private theorem largePrimeDesc_size (n : ℕ) :
    n ≤ (largePrimeDesc n).p.size ∧ n ≤ (largePrimeDesc n).q.size := by
  have hpSpec := (Nat.exists_infinite_primes (2 ^ n)).choose_spec
  have hqSpec := (Nat.exists_infinite_primes ((Nat.exists_infinite_primes (2 ^ n)).choose + 1))
  have hpge : 2 ^ n ≤ (largePrimeDesc n).p := hpSpec.1
  have hqge : 2 ^ n ≤ (largePrimeDesc n).q := by
    have := hqSpec.choose_spec.1
    change (largePrimeDesc n).p + 1 ≤ (largePrimeDesc n).q at this
    omega
  exact ⟨(Nat.lt_size.mpr hpge).le, (Nat.lt_size.mpr hqge).le⟩

private noncomputable def largePrimeGen : RSAGen :=
  fun n => PMF.pure (largePrimeDesc n)

example (h : RSAUnitOneWay largePrimeGen) :
    RSAOneWay largePrimeGen ∧ (RSAOneWay largePrimeGen ↔ RSAUnitOneWay largePrimeGen) := by
  have hsize : ∀ᶠ n in Filter.atTop, ∀ desc ∈ (largePrimeGen n).support,
      n ≤ desc.p.size ∧ n ≤ desc.q.size :=
    Filter.Eventually.of_forall fun n desc hdesc => by
      simp only [largePrimeGen, PMF.support_pure, Set.mem_singleton_iff] at hdesc
      subst hdesc
      exact largePrimeDesc_size n
  exact ⟨h.rsaOneWay hsize, rsaOneWay_iff_rsaUnitOneWay hsize⟩

private def desc6 : RSADesc where
  p := 2
  q := 3
  e := 1
  d := 1
  hp := by decide
  hq := by decide
  hpq := by decide
  he := by decide
  hed := by decide

private def nonUnitInverter6 : RSAInverter :=
  fun _ _ y => pure (if y.val = 1 ∨ y.val = 5 then ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _) y.isLt⟩
    else y)

private theorem heval6 (x : Fin desc6.modulus) : desc6.publicKey.eval x = x := by
  ext
  change x.val ^ 1 % 6 = x.val
  rw [pow_one]
  exact Nat.mod_eq_of_lt x.isLt

private theorem zmod6_unit_val (u : (ZMod 6)ˣ) :
    (u : ZMod 6).val = 1 ∨ (u : ZMod 6).val = 5 := by
  have hcop : Nat.Coprime (u : ZMod 6).val 6 := ZMod.val_coe_unit_coprime u
  have hlt : (u : ZMod 6).val < 6 := ZMod.val_lt _
  interval_cases h : (u : ZMod 6).val <;>
    first
    | exact absurd hcop (by decide)
    | exact Or.inl rfl
    | exact Or.inr rfl

private theorem succProbability_unit_nonUnitInverter6 (n : ℕ) :
    (rsaUnitInversionGame (fun _ => PMF.pure desc6) nonUnitInverter6 n).succProbability = 0 := by
  rw [rsaUnitInversionGame_eq]
  simp only [Game.succProbability, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.pure_bind, ProbComp.eval_pure, nonUnitInverter6, heval6, ENNReal.toNNReal_eq_zero_iff]
  left
  rw [PMF.bind_apply, tsum_eq_zero_iff]
  intro u
  have hval15 : (desc6.unitResidue u).val = 1 ∨ (desc6.unitResidue u).val = 5 :=
    zmod6_unit_val u
  have hne0 : (0 : Fin desc6.modulus) ≠ desc6.unitResidue u := by
    intro h0
    have hv : (desc6.unitResidue u).val = 0 := by rw [← h0]; rfl
    rcases hval15 with h | h <;> omega
  simp [hval15, hne0]

private theorem succProbability_rsa_nonUnitInverter6 (n : ℕ) :
    (rsaInversionGame (fun _ => PMF.pure desc6) nonUnitInverter6 n).succProbability = 2 / 3 := by
  rw [rsaInversionGame_eq]
  simp only [Game.succProbability, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.pure_bind, ProbComp.eval_pure, nonUnitInverter6, heval6]
  rw [PMF.bind_apply, tsum_fintype]
  have hsum : (∑ x : Fin desc6.modulus,
      (PMF.uniformOfFintype (Fin desc6.modulus)) x *
        (PMF.pure (decide ((if x.val = 1 ∨ x.val = 5 then
          (⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _) x.isLt⟩ : Fin desc6.modulus)
          else x) = x))) true) =
      (4 : ℝ≥0∞) / 6 := by
    change (∑ x : Fin 6,
      (PMF.uniformOfFintype (Fin 6)) x *
        (PMF.pure (decide ((if x.val = 1 ∨ x.val = 5 then (0 : Fin 6) else x) = x))) true) =
      (4 : ℝ≥0∞) / 6
    simp only [PMF.uniformOfFintype_apply, Fintype.card_fin, Nat.cast_ofNat, PMF.pure_apply]
    trans (6 : ℝ≥0∞)⁻¹ + 6⁻¹ + 6⁻¹ + 6⁻¹
    · rw [Fin.sum_univ_six]
      simp [Fin.ext_iff]
    rw [div_eq_mul_inv]
    ring
  rw [hsum, ENNReal.toNNReal_div, ENNReal.toNNReal_ofNat, ENNReal.toNNReal_ofNat]
  norm_num

/-- Counterexample showing `ℓ ≤ p.size ∧ ℓ ≤ q.size` cannot be dropped in
`succProbability_rsaInversionGame_le_of_size`: for `N = 6 = 2 * 3` (`p.size = q.size = 2`) and
`ℓ = 3`, `nonUnitInverter6` achieves advantage `2 / 3 > 0 + 4 / 2 ^ 3`. -/
example :
    ¬ ((rsaInversionGame (fun _ => PMF.pure desc6) nonUnitInverter6 0).succProbability ≤
      (rsaUnitInversionGame (fun _ => PMF.pure desc6) nonUnitInverter6 0).succProbability +
        (4 : ℝ≥0) / 2 ^ 3) := by
  rw [succProbability_rsa_nonUnitInverter6, succProbability_unit_nonUnitInverter6]
  norm_num

/-- Counterexample showing `ℓ ≤ p.size ∧ ℓ ≤ q.size` cannot be dropped in
`dist_uniformOfFintype_zmod_units_lt` (or even weakened to `≤`): for `p = 2`, `q = 3`, and
`ℓ = 3`, the statistical distance exceeds `4 / 2 ^ 3 = 1 / 2`. -/
example :
    ¬ (dist (PMF.uniformOfFintype (ZMod (2 * 3)))
        ((PMF.uniformOfFintype (ZMod (2 * 3))ˣ).map Units.val) ≤ (4 : ℝ) / 2 ^ 3) := by
  have htot : Nat.totient (2 * 3) = 2 := by decide
  rw [dist_uniformOfFintype_zmod_units (2 * 3), htot]
  norm_num

/-- Counterexample showing both prime bit-length bounds are required in
`dist_uniformOfFintype_zmod_units_lt`: for `p = 2`, `q = 5`, and `ℓ = 3`, `3 ≤ q.size` holds while
`3 ≤ p.size` fails, and the statistical distance is `6 / 10 > 4 / 2 ^ 3 = 1 / 2`. -/
example :
    ¬ (dist (PMF.uniformOfFintype (ZMod (2 * 5)))
        ((PMF.uniformOfFintype (ZMod (2 * 5))ˣ).map Units.val) < (4 : ℝ) / 2 ^ 3) := by
  have htot : Nat.totient (2 * 5) = 4 := by decide
  rw [dist_uniformOfFintype_zmod_units (2 * 5), htot]
  norm_num

end Converse

end CslibFrontierTests.Crypto.RSAUnitInversion
