/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Computational.RSAUnitInversion
public import CslibFrontier.Probability.StatisticalDistance
import CslibFrontier.Crypto.Computational.UnitSampling
import CslibFrontier.Crypto.Negligible.Dyadic
import CslibFrontier.Foundations.Data.ZMod.Basic

/-!
# Converse reduction from unit RSA to full RSA (Exercises 10.25–10.26)

In [BonehShoup2023], §10.11 (printed p. 431), Exercises 10.25 and 10.26 ask for the converse of
Theorem 10.5: when the modulus `N = p * q` is the product of two distinct `ℓ`-bit primes
(`ℓ ≤ p.size` and `ℓ ≤ q.size`), uniform residues in `ZMod N` and uniform units in `(ZMod N)ˣ`
have statistical distance strictly less than `4 / 2 ^ ℓ` (which equals `2 ^ -(ℓ - 2)` for `ℓ ≥ 2`).
Here `dist_uniformOfFintype_zmod_units_lt` derives `< 4 / 2 ^ ℓ` from the exact non-unit fraction
`Cslib.Crypto.dist_uniformOfFintype_zmod_units` and `Cslib.Crypto.sub_totient_div_lt`. The book's
Exercise 10.26 inequality names an adversary `B` that it does not introduce; here the full-RSA
inverter `A` itself runs in `rsaUnitInversionGame` (so no new reduction is defined), giving
`RSAadv[A] ≤ uRSAadv[A] + 4 / 2 ^ ℓ`.

## Main results

* `Cslib.Crypto.dist_uniformOfFintype_zmod_units_lt`: Exercise 10.25 — for distinct primes `p ≠ q`
  with `ℓ ≤ p.size` and `ℓ ≤ q.size`, `PMF.uniformOfFintype (ZMod (p * q))` and
  `(PMF.uniformOfFintype (ZMod (p * q))ˣ).map Units.val` have statistical distance strictly less
  than `4 / 2 ^ ℓ`.
* `Cslib.Crypto.succProbability_rsaInversionGame_le_of_nonUnitFrac_le`: per-parameter bound in
  terms of an upper bound `δ` on the non-unit fraction `(N - φ(N)) / N` across `(gen n).support`.
* `Cslib.Crypto.succProbability_rsaInversionGame_le_of_size`: Exercise 10.26 — concrete converse
  bound running `A` in both games (no new reduction) with loss `4 / 2 ^ ℓ` when every key in
  `(gen n).support` has `ℓ ≤ p.size` and `ℓ ≤ q.size`.
* `Cslib.Crypto.RSAUnitOneWay.rsaOneWay_of_nonUnitFrac_le`: asymptotic converse when the non-unit
  fraction is bounded by a negligible function on `(gen n).support`.
* `Cslib.Crypto.RSAUnitOneWay.rsaOneWay`: asymptotic converse `RSAUnitOneWay gen → RSAOneWay gen`
  when `n ≤ desc.p.size ∧ n ≤ desc.q.size` eventually holds on `(gen n).support`.
* `Cslib.Crypto.rsaOneWay_iff_rsaUnitOneWay`: equivalence `RSAOneWay gen ↔ RSAUnitOneWay gen`
  under `n ≤ desc.p.size ∧ n ≤ desc.q.size` eventually on `(gen n).support`.

## References

* [BonehShoup2023] §10.11, p. 431, Exercises 10.25–10.26.
-/

public section

namespace Cslib.Crypto

open Cslib.Probability
open scoped NNReal ENNReal Cslib.Probability.PMF

/-- **Boneh–Shoup Exercise 10.25 (§10.11, printed p. 431):** for distinct primes `p ≠ q` with
`ℓ ≤ p.size` and `ℓ ≤ q.size`, uniform residues modulo `p * q` and uniform units in
`(ZMod (p * q))ˣ` have statistical distance strictly less than `4 / 2 ^ ℓ` (`2 ^ -(ℓ - 2)` for
`ℓ ≥ 2`), reusing `dist_uniformOfFintype_zmod_units` and `sub_totient_div_lt`. -/
theorem dist_uniformOfFintype_zmod_units_lt {p q ℓ : ℕ} [NeZero (p * q)]
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hpn : ℓ ≤ p.size) (hqn : ℓ ≤ q.size) :
    dist (PMF.uniformOfFintype (ZMod (p * q)))
      ((PMF.uniformOfFintype (ZMod (p * q))ˣ).map Units.val) < (4 : ℝ) / 2 ^ ℓ := by
  rw [dist_uniformOfFintype_zmod_units (p * q)]
  exact_mod_cast sub_totient_div_lt hp hq hpq hpn hqn

private theorem unitResidue_eq_finEquiv_symm (desc : RSADesc) (u : (ZMod desc.modulus)ˣ) :
    desc.unitResidue u = (ZMod.finEquiv desc.modulus).symm (u : ZMod desc.modulus) := by
  ext
  rw [ZMod.val_finEquiv_symm]
  rfl

/-- Per-parameter converse bound from `rsaUnitInversionGame` to `rsaInversionGame`: running the
same inverter `A` directly in both games (no new reduction is defined), when every key in
`(gen n).support` has non-unit fraction `(N - φ(N)) / N ≤ δ`, `rsaInversionGame` succeeds with
probability at most that of `rsaUnitInversionGame` plus `δ`. -/
theorem succProbability_rsaInversionGame_le_of_nonUnitFrac_le
    (gen : RSAGen) (A : RSAInverter) {n : ℕ} {δ : ℝ≥0}
    (hδ : ∀ desc ∈ (gen n).support,
      ((desc.modulus - desc.modulus.totient : ℕ) : ℝ≥0) / desc.modulus ≤ δ) :
    (rsaInversionGame gen A n).succProbability ≤
      (rsaUnitInversionGame gen A n).succProbability + δ := by
  have hadv : Game.advantage (rsaInversionGame gen A n) (rsaUnitInversionGame gen A n) ≤ δ := by
    rw [rsaInversionGame_eq, rsaUnitInversionGame_eq]
    refine Game.advantage_bind_le_of_support (gen n) _ _ fun desc hdesc => ?_
    let k : ZMod desc.modulus → Game := fun z => do
      let x := (ZMod.finEquiv desc.modulus).symm z
      let x' ← (A n desc.publicKey (desc.publicKey.eval x)).eval
      pure (decide (x' = x))
    have h1 : (do
        let x ← PMF.uniformOfFintype (Fin desc.modulus)
        let x' ← (A n desc.publicKey (desc.publicKey.eval x)).eval
        pure (decide (x' = x))) =
        (PMF.uniformOfFintype (ZMod desc.modulus)).bind k := by
      change (PMF.uniformOfFintype (Fin desc.modulus)).bind _ = _
      rw [← PMF.uniformOfFintype_map_equiv (ZMod.finEquiv desc.modulus).symm.toEquiv, PMF.bind_map]
      rfl
    have h2 : (do
        let x ← PMF.uniformOfFintype (ZMod desc.modulus)ˣ
        let x' ← (A n desc.publicKey (desc.publicKey.eval (desc.unitResidue x))).eval
        pure (decide (x' = desc.unitResidue x))) =
        (PMF.uniformOfFintype (ZMod desc.modulus)ˣ).bind (fun u => k u) := by
      change (PMF.uniformOfFintype (ZMod desc.modulus)ˣ).bind _ = _
      congr 1
      funext u
      simp only [k, unitResidue_eq_finEquiv_symm]
    rw [h1, h2]
    exact (Game.advantage_bind_units_le desc.modulus k).trans (hδ desc hdesc)
  have hcoe : |((rsaInversionGame gen A n).succProbability : ℝ) -
      (rsaUnitInversionGame gen A n).succProbability| ≤ δ := by
    simpa only [Game.coe_advantage] using NNReal.coe_le_coe.mpr hadv
  rw [← NNReal.coe_le_coe, NNReal.coe_add]
  linarith [(abs_sub_le_iff.mp hcoe).1]

/-- **Boneh–Shoup Exercise 10.26 (§10.11, printed p. 431):** running the same inverter `A` in both
games (no new reduction is defined), if every key in `(gen n).support` has primes satisfying
`ℓ ≤ p.size` and `ℓ ≤ q.size`, then `rsaInversionGame` succeeds with probability at most that of
`rsaUnitInversionGame` plus `4 / 2 ^ ℓ` (`2 ^ -(ℓ - 2)` for `ℓ ≥ 2`). -/
theorem succProbability_rsaInversionGame_le_of_size
    (gen : RSAGen) (A : RSAInverter) {n ℓ : ℕ}
    (hsize : ∀ desc ∈ (gen n).support, ℓ ≤ desc.p.size ∧ ℓ ≤ desc.q.size) :
    (rsaInversionGame gen A n).succProbability ≤
      (rsaUnitInversionGame gen A n).succProbability + 4 / 2 ^ ℓ :=
  succProbability_rsaInversionGame_le_of_nonUnitFrac_le gen A fun desc hdesc =>
    (sub_totient_div_lt desc.hp desc.hq desc.hpq (hsize desc hdesc).1 (hsize desc hdesc).2).le

/-- Asymptotic converse of Theorem 10.5 (`RSAOneWay.rsaUnitOneWay`): `RSAUnitOneWay gen` implies
`RSAOneWay gen` whenever the non-unit fraction `(N - φ(N)) / N` on `(gen n).support` is
eventually bounded by a negligible function `δ`, running `A` directly in both games (no new
reduction is defined). -/
theorem RSAUnitOneWay.rsaOneWay_of_nonUnitFrac_le {gen : RSAGen} {δ : ℕ → ℝ≥0}
    (hδ : Negligible δ)
    (hbound : ∀ᶠ n in Filter.atTop, ∀ desc ∈ (gen n).support,
      ((desc.modulus - desc.modulus.totient : ℕ) : ℝ≥0) / desc.modulus ≤ δ n)
    (h : RSAUnitOneWay gen) : RSAOneWay gen := fun A hA =>
  negligible_of_eventually_le ((h A hA).add hδ) <|
    hbound.mono fun _ hn => succProbability_rsaInversionGame_le_of_nonUnitFrac_le gen A hn

/-- Asymptotic converse of Theorem 10.5 (`RSAOneWay.rsaUnitOneWay`): `RSAUnitOneWay gen` implies
`RSAOneWay gen` whenever `n ≤ desc.p.size ∧ n ≤ desc.q.size` holds eventually on `(gen n).support`
(Boneh–Shoup §10.11, Exercise 10.26, p. 431, running `A` directly in both games). -/
theorem RSAUnitOneWay.rsaOneWay {gen : RSAGen}
    (hsize : ∀ᶠ n in Filter.atTop, ∀ desc ∈ (gen n).support,
      n ≤ desc.p.size ∧ n ≤ desc.q.size)
    (h : RSAUnitOneWay gen) : RSAOneWay gen :=
  h.rsaOneWay_of_nonUnitFrac_le (negligible_const_div_two_pow 4)
    (hsize.mono fun _ hn desc hdesc =>
      (sub_totient_div_lt desc.hp desc.hq desc.hpq (hn desc hdesc).1 (hn desc hdesc).2).le)

/-- Under `n`-bit primes (`n ≤ desc.p.size ∧ n ≤ desc.q.size`) eventually on `(gen n).support`,
full-domain RSA one-wayness and unit-domain RSA one-wayness are equivalent. -/
theorem rsaOneWay_iff_rsaUnitOneWay {gen : RSAGen}
    (hsize : ∀ᶠ n in Filter.atTop, ∀ desc ∈ (gen n).support,
      n ≤ desc.p.size ∧ n ≤ desc.q.size) :
    RSAOneWay gen ↔ RSAUnitOneWay gen :=
  ⟨RSAOneWay.rsaUnitOneWay, fun h => h.rsaOneWay hsize⟩

end Cslib.Crypto
