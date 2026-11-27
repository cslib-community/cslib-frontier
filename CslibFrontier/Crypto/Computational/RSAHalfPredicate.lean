/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.RSALeastSignificantBit
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Probabilistic.PPT.Capture

/-!
# The half predicate of RSA

Boneh and Shoup's Exercise 12.21 ("Baby Bleichenbacher attack", [BonehShoup2023], pp. 519–520)
considers, for a residue `x` modulo `n`, the predicate `P_x(r)` that is `1` when `x · r mod n`,
treated as an integer in `[0, n)`, exceeds `n / 2`. Part (a) asks to learn `x` from about
`log₂ n` values of `P_x`; part (b) asks to recover the `e`-th root of `c` from an oracle that says
whether the `e`-th root of its input exceeds `n / 2`.

Here the predicate is written `decide (N < 2 * y)`, which is `y > N / 2` over the reals. For odd
`N` and `y < N`, it equals the parity of `2 * y % N`, so `P_x(2 ^ k)` is the parity of
`2 ^ (k + 1) * x % N`. These are the bits from which `lsbRecover` recovers `x`
(`lsbRecover_map_decide_lt_two_mul`, part (a)). For part (b), `halfToLSBPredictor H` asks a half
oracle `H` about `y * ((N + 1) / 2) ^ e % N`, the RSA image of half the preimage of `y`. For odd
`N`, half of `w` exceeds `N / 2` exactly when `w` is odd, so `halfToLSBPredictor H` predicts the
least significant bit and `lsbInverter` inverts RSA with it. By
`lsbInverter_halfToLSBPredictor`, the inverter on `y = w ^ e % N` calls `H` at
`2 ^ (k * e) * y % N`, the RSA images of `2 ^ k * w % N`, for `k < N.size`, and returns
`lsbRecover` of the answers: part (a) at the points `r = 2 ^ k`.

Part (a) needs an odd modulus: for the modulus `6 = 2 * 3`, `P_0` and `P_3` agree at every point.
The inverter of part (b) needs one because halving needs `2` to be invertible modulo `N`.
The efficiency certificate is relative, as for `isPPT_lsbInverter`: the inverter is PPT whenever
`H` is. Under `RSAOneWay` and eventually odd moduli no always-correct `H` is PPT
(`RSAOneWay.not_frequently_alwaysCorrect_halfPredictor`), so the certificate does not count the
work of an oracle that holds the secret key. The inverter is not stated as an oracle program with
a query bound.

## Main definitions

* `Cslib.Crypto.halfToLSBPredictor`: a half predictor precomposed with halving, as a
  least-significant-bit predictor.

## Main results

* `Cslib.Crypto.lsbRecover_map_decide_lt_two_mul`: part (a), for odd `N ≤ 2 ^ m`, the half
  predicate at `2 ^ 0, …, 2 ^ (m - 1)` determines `x < N` through `lsbRecover`.
* `Cslib.Crypto.lsbInverter_halfToLSBPredictor`: for odd `N`, the inverter built from `H` calls `H`
  at `2 ^ (k * e) * y % N`, `k < N.size`, in order, and returns `lsbRecover` of the answers.
* `Cslib.Crypto.eval_halfToLSBPredictor`: a half predictor that is correct on every RSA image modulo
  an odd `N` gives a correct least-significant-bit predictor.
* `Cslib.Crypto.succProbability_rsaInversionGame_halfToLSBPredictor`: part (b), the inverter
  `lsbInverter (halfToLSBPredictor H)` wins the RSA inversion experiment with probability `1`.
* `Cslib.Crypto.isPPT_halfToLSBPredictor`: `halfToLSBPredictor H` is PPT whenever `H` is.
* `Cslib.Crypto.RSAOneWay.not_frequently_alwaysCorrect_halfPredictor`: under `RSAOneWay` on
  eventually odd moduli, no PPT half predictor is always correct on infinitely many parameters.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Exercise 12.21 (pp. 519–520).
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

/-- For odd `N` and `y < N`, `y > N / 2` exactly when `2 * y % N` is odd. -/
private theorem decide_lt_two_mul_eq_testBit {N y : ℕ} (hN : Odd N) (hy : y < N) :
    decide (N < 2 * y) = (2 * y % N).testBit 0 := by
  obtain ⟨t, rfl⟩ := hN
  rw [Nat.testBit_zero]
  rcases Nat.lt_or_ge (2 * y) (2 * t + 1) with h | h
  · rw [Nat.mod_eq_of_lt h]
    simp only [decide_eq_decide]
    omega
  · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (a := 2 * y - (2 * t + 1)) (by omega)]
    simp only [decide_eq_decide]
    omega

/-- **Exercise 12.21(a)** ([BonehShoup2023], p. 519): for odd `N` with `N ≤ 2 ^ m` and `x < N`,
the values of the half predicate `P_x(r) = [x * r % N > N / 2]` at `r = 2 ^ 0, …, 2 ^ (m - 1)`
determine `x`, which `lsbRecover` computes from them. -/
theorem lsbRecover_map_decide_lt_two_mul {N x m : ℕ} (hN : Odd N) (hx : x < N)
    (hm : N ≤ 2 ^ m) :
    lsbRecover N m ((List.range m).map fun k => decide (N < 2 * (x * 2 ^ k % N))) = x := by
  have hpos : 0 < N := by omega
  apply lsbRecover_eq hx hm
  rw [← binaryValue_testBit_two_pow_mul_mod hN hx m]
  congr 1
  apply List.map_congr_left
  intro k _
  rw [decide_lt_two_mul_eq_testBit hN (Nat.mod_lt _ hpos), Nat.mul_mod, Nat.mod_mod,
    ← Nat.mul_mod, pow_succ]
  congr 2
  ring

/-- Halving modulo odd `N`: `z * ((N + 1) / 2) % N` exceeds `N / 2` exactly when `z` is odd. -/
private theorem decide_lt_two_mul_mul_half_mod {N z : ℕ} (hN : Odd N) (hz : z < N) :
    decide (N < 2 * (z * ((N + 1) / 2) % N)) = z.testBit 0 := by
  have hpos : 0 < N := by omega
  rw [decide_lt_two_mul_eq_testBit hN (Nat.mod_lt _ hpos)]
  congr 1
  obtain ⟨t, rfl⟩ := hN
  have ht : (2 * t + 1 + 1) / 2 = t + 1 := by omega
  rw [ht, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod,
    show 2 * (z * (t + 1)) = z + (2 * t + 1) * z by ring, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hz]

/-- A half predictor as a least-significant-bit predictor: on `y`, ask the half predictor `H`
about `y * ((N + 1) / 2) ^ e % N`, which is the RSA image of half the preimage of `y` modulo
odd `N`. -/
def halfToLSBPredictor (H : RSAPredictor) : RSAPredictor := fun n pk y =>
  H n pk ⟨y * ((pk.N + 1) / 2) ^ pk.e % pk.N, Nat.mod_lt _ y.pos⟩

/-- **Where the inverter asks the half oracle.** For odd `N`, `lsbInverter (halfToLSBPredictor H)`
on `y` calls `H` at the residues `2 ^ (k * e) * y % N` for `k = 0, …, N.size - 1`, in this order,
and returns `lsbRecover N N.size` of the answers, reduced modulo `N`. When `y = w ^ e % N`, these
residues are the RSA images of `2 ^ k * w % N` (`two_pow_mul_rsaEval`). -/
theorem lsbInverter_halfToLSBPredictor {H : RSAPredictor} {n : ℕ} {pk : RSAPublicKey}
    (hN : Odd pk.N) (y : Fin pk.N) :
    lsbInverter (halfToLSBPredictor H) n pk y = (do
      let bits ← (List.range pk.N.size).mapM fun k =>
        H n pk ⟨2 ^ (k * pk.e) * y % pk.N, Nat.mod_lt _ y.pos⟩
      return ⟨lsbRecover pk.N pk.N.size bits % pk.N, Nat.mod_lt _ y.pos⟩) := by
  have hpoint : ∀ k : ℕ, 2 ^ ((k + 1) * pk.e) * y % pk.N % pk.N * ((pk.N + 1) / 2) ^ pk.e % pk.N =
      2 ^ (k * pk.e) * y % pk.N := by
    intro k
    obtain ⟨t, ht⟩ := hN
    have hhalf : (pk.N + 1) / 2 = t + 1 := by omega
    have hinv : 2 * (t + 1) ≡ 1 [MOD pk.N] := by
      rw [Nat.ModEq, show 2 * (t + 1) = 1 + pk.N * 1 by omega, Nat.add_mul_mod_self_left]
    rw [hhalf, Nat.mod_mod, Nat.mod_mul_mod,
      show 2 ^ ((k + 1) * pk.e) * y * (t + 1) ^ pk.e = 2 ^ (k * pk.e) * y * (2 * (t + 1)) ^ pk.e by
        rw [mul_pow, add_mul, one_mul, pow_add]
        ring]
    have h := (hinv.pow pk.e).mul_left (2 ^ (k * pk.e) * y)
    rw [one_pow, mul_one] at h
    exact h
  simp only [lsbInverter, lsbQueries, halfToLSBPredictor, List.mapM_map, Function.comp_def,
    hpoint]

/-- If `H` says correctly, on every RSA image modulo an odd `N`, whether the preimage exceeds
`N / 2`, then `halfToLSBPredictor H` predicts the least significant bit of the preimage
correctly. -/
theorem eval_halfToLSBPredictor {H : RSAPredictor} {n : ℕ} {pk : RSAPublicKey} (hN : Odd pk.N)
    (hH : ∀ w : Fin pk.N, ProbComp.eval (H n pk (pk.eval w)) = PMF.pure (decide (pk.N < 2 * w)))
    (z : Fin pk.N) :
    ProbComp.eval (halfToLSBPredictor H n pk (pk.eval z)) = PMF.pure ((z : ℕ).testBit 0) := by
  have hpos : 0 < pk.N := z.pos
  have hpoint : (⟨(pk.eval z : ℕ) * ((pk.N + 1) / 2) ^ pk.e % pk.N,
      Nat.mod_lt _ (pk.eval z).pos⟩ : Fin pk.N) =
      pk.eval ⟨z * ((pk.N + 1) / 2) % pk.N, Nat.mod_lt _ hpos⟩ := by
    ext
    simp only [RSAPublicKey.val_eval, rsaEval]
    rw [← Nat.pow_mod, mul_pow, Nat.mod_mul_mod]
  simp only [halfToLSBPredictor]
  rw [hpoint, hH, decide_lt_two_mul_mul_half_mod hN z.isLt]

/-- **Exercise 12.21(b)** ([BonehShoup2023], pp. 519–520): if the moduli of `gen n` are odd and
`H` says correctly, on every RSA image, whether the `e`-th root exceeds `N / 2`, then the inverter
`lsbInverter (halfToLSBPredictor H)` recovers the `e`-th root with probability `1`. It asks `H`
about the RSA images of `2 ^ k * x % N` for `k < N.size`, part (a)'s points
(`lsbInverter_halfToLSBPredictor`). The pointwise form, every challenge inverted, is
`eval_lsbInverter` applied to `eval_halfToLSBPredictor`. -/
theorem succProbability_rsaInversionGame_halfToLSBPredictor {gen : RSAGen} {H : RSAPredictor}
    {n : ℕ} (hodd : ∀ desc ∈ (gen n).support, Odd desc.modulus)
    (hH : ∀ desc ∈ (gen n).support, ∀ w : Fin desc.modulus,
      ProbComp.eval (H n desc.publicKey (desc.publicKey.eval w)) =
        PMF.pure (decide (desc.modulus < 2 * w))) :
    Game.succProbability (rsaInversionGame gen (lsbInverter (halfToLSBPredictor H)) n) = 1 :=
  succProbability_rsaInversionGame_lsbInverter hodd fun desc hdesc =>
    eval_halfToLSBPredictor (pk := desc.publicKey) (hodd desc hdesc) (hH desc hdesc)

/-- `halfToLSBPredictor H` is PPT whenever `H` is: the halving step
`y ↦ y * ((N + 1) / 2) ^ e % N` is computable in polynomial time. -/
theorem isPPT_halfToLSBPredictor {H : RSAPredictor} (hH : H.IsPPT) :
    (halfToLSBPredictor H).IsPPT := by
  have hN : ComputableInPolyTime (fun x : RSAInput => x.publicKey.N) encRSAInput encNat := by
    fun_prop
  have hhalf : ComputableInPolyTime (fun x : RSAInput => (x.publicKey.N + 1) / 2)
      encRSAInput encNat :=
    ComputableInPolyTime.binary_div'
      (ComputableInPolyTime.binary_add' hN (ComputableInPolyTime.const 1))
      (ComputableInPolyTime.const 2)
  have hpow : ComputableInPolyTime
      (fun x : RSAInput => ((x.publicKey.N + 1) / 2) ^ x.publicKey.e % x.publicKey.N)
      encRSAInput encNat :=
    ComputableInPolyTime.binary_powMod hhalf (by fun_prop) hN fun x => x.challenge.pos
  have hval : ComputableInPolyTime
      (fun x : RSAInput => (x.challenge : ℕ) * ((x.publicKey.N + 1) / 2) ^ x.publicKey.e %
        x.publicKey.N) encRSAInput encNat := by
    have h := ComputableInPolyTime.binary_mod'
      (ComputableInPolyTime.binary_mul'
        (RSAInput.computableInPolyTime_challenge_val (g := fun x : RSAInput => x)
          (by fun_prop)) hpow) hN
    simpa only [Nat.mul_mod_mod] using h
  have hprepare : ComputableInPolyTime
      (fun x : RSAInput =>
        ({ secParam := x.secParam, publicKey := x.publicKey,
           challenge := ⟨(x.challenge : ℕ) * ((x.publicKey.N + 1) / 2) ^ x.publicKey.e %
             x.publicKey.N, Nat.mod_lt _ x.challenge.pos⟩ } : RSAInput))
      encRSAInput encRSAInput :=
    encRSAInput_mk_polyTime (by fun_prop) (by fun_prop) hval
  exact hH.preprocess hprepare

/-- Under `RSAOneWay gen` and eventually odd moduli, no uniform strict-PPT predictor says with
certainty, on every RSA image modulo `N`, whether the preimage exceeds `N / 2`, for infinitely many
security parameters. This is the hardness reading of `isPPT_halfToLSBPredictor`: no
polynomial-time algorithm computes the half predicate of the RSA preimage exactly from the public
key. It is not part (b), whose oracle may hold the secret key. -/
theorem RSAOneWay.not_frequently_alwaysCorrect_halfPredictor {gen : RSAGen}
    (hRSA : RSAOneWay gen)
    (hodd : ∀ᶠ n in Filter.atTop, ∀ desc ∈ (gen n).support, Odd desc.modulus)
    {H : RSAPredictor} (hH : H.IsPPT) :
    ¬ ∃ᶠ n in Filter.atTop, ∀ desc ∈ (gen n).support, ∀ w : Fin desc.modulus,
      ProbComp.eval (H n desc.publicKey (desc.publicKey.eval w)) =
        PMF.pure (decide (desc.modulus < 2 * w)) := fun hfreq =>
  hRSA.not_frequently_alwaysCorrect_lsbPredictor hodd (isPPT_halfToLSBPredictor hH)
    ((hodd.and_frequently hfreq).mono fun _ h desc hdesc =>
      eval_halfToLSBPredictor (pk := desc.publicKey) (h.1 desc hdesc) (h.2 desc hdesc))

end Cslib.Crypto
