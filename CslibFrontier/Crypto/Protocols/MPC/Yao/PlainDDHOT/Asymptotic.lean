/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.Yao.PlainDDHOT.Games
import CslibFrontier.Crypto.Negligible.Dyadic

/-!
# Yao's protocol in the plain model: the circuit family and the corrupted garbler, asymptotically

This module is a step towards the plain-model statement of Theorem 7 of Lindell and Pinkas
[LindellPinkas2009] (#6045, criterion 2), not that theorem. It fixes how machines get the function
descriptions of the plain-model family `Yao.kdfDDHProbFamily Gs F H c`, and turns the statistical
bound for a corrupted garbler into a statement about a negligible function. **No efficiency
certificate is proved here for any simulator or reduction of the family, no hardness assumption is
applied, and `ProtocolFamily.SemiHonestSecure` is not proved for a corrupted party** (#6045,
criterion 2 stays open).

## How machines get the circuit

The family takes the function descriptions as a parameter `c : ℕ → Yao.Params Gs`. Its public
parameters are the group descriptions of `F` only, and `Yao.kdfDDHProbEncoding` writes no function
description. Efficiency statements about the family use one convention: **the family of function
descriptions is uniform**, that is

`ComputableInPolyTime c encUnary (Yao.encParams encFn)`,

together with `ComputableInPolyTime Gs.inLen encFn encUnary`, the hypothesis of the hybrid-model
theorems of `CslibFrontier/Crypto/Protocols/MPC/Yao/Security.lean`. Every simulator, environment
and reduction reads `1ⁿ` and computes `c n` from it. The public parameters of the family are not
changed, so the definitions of the earlier steps stand as they are.

This differs from `Yao.family`, whose public parameters are the function description, drawn by a
setup law and given to the environment. A uniform family is the case of a deterministic sampler
there (`fun n => pure (c n)`); a randomized choice of the function is not covered here. How either
form compares with the statement of [LindellPinkas2009] was not checked against the source in this
step.

`Yao.encParams_evaluatorLen_polyTime` (`CslibFrontier/Crypto/Protocols/MPC/Yao/Family.lean`) is
the first consequence: the number of transfers `(c n).evaluatorLen` is computed in polynomial time,
so it is polynomially bounded (`ComputableInPolyTime.polynomiallyBounded`), and so is the number
`Nat.log 2 k + 1` of fair coins that draw a transfer below a power of two above `k` transfers, with
`2 ^ (Nat.log 2 k + 1) ≤ 2 * k + 2`.

## What is proved

* `Yao.negligible_advantage_kdfDDHProbFamily_garbler` (corrupted garbler): when the number of
  transfers is polynomially bounded, the advantage of **every** environment, efficient or not,
  between the real game and the ideal game with the composed simulator family `Yao.kdfDDHProbSim`
  is negligible. It is the asymptotic form of the statistical bound
  `Yao.advantage_idealGame_realGame_kdfDDHProbFamily_garbler_le`. The composed simulator is not
  shown to be PPT, so this is not `ProtocolFamily.SemiHonestSecure` at the coalition `{0}`.

## What is not proved

* **The corrupted evaluator has no asymptotic form.** The bound
  `Yao.advantage_idealGame_realGame_kdfDDHProbFamily_evaluator_le_mul` asks that the derived keys
  have length `msgLen n` for **every** group description, not only those that the setup draws at
  `n`. With one key derivation `H` for all `n`, asking this at every `n` forces a constant key
  length, so an asymptotic statement built on it would hold only for keys of constant length. The
  bound must first be restated with the length asked on the support of the setup, as the garbler
  bound is here. After that, its three advantages have to be shown negligible, which needs a PPT
  certificate for each of the three adversaries; none exists (#6045).

## Main results

* `Cslib.Crypto.Protocols.MPC.Yao.negligible_advantage_kdfDDHProbFamily_garbler`

## References

* [Y. Lindell and B. Pinkas, *A Proof of Security of Yao's Protocol for Two-Party
  Computation*][LindellPinkas2009]
-/

public section

namespace Cslib.Crypto.Protocols.MPC.Yao

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.Garbling Turing.MultiTapeTM
open scoped NNReal

variable {Fn : Type} {Gs : Scheme Fn}

/-- Step towards [LindellPinkas2009], Theorem 7 for a corrupted garbler, not the cited result
(#6045): the composed simulator is not shown to be PPT, so this is not
`ProtocolFamily.SemiHonestSecure`.

Let the group description be drawn from any setup law, and let `Z` be **any** environment, efficient
or not, against the plain-model family `Yao.kdfDDHProbFamily Gs F H c` with a corrupted garbler.
Suppose that

* the garbling scheme `Gs` is correct with a projective encoding and tokens of length `msgLen n`
  (`Gs.HasTokenLength`),
* every derived key `H (d, F.encode d r)` has length `msgLen n` for every group description `d`
  that the setup law can draw at `n`,
* the simulators at the coalition `{0}` are `Yao.garblerSim Gs n (c n)` for Yao's protocol,
  `maskedOTSenderSim` with the fair-coin pads for the masked transfer and
  `F.ddhOTSenderSimProb n d` for the DDH transfer, and
* the number of transfers `(c n).evaluatorLen` is polynomially bounded.

Then the advantage of `Z` between `ProtocolFamily.realGame` and `ProtocolFamily.idealGame` with the
composed simulator family `Yao.kdfDDHProbSim` is negligible: it is at most
`(c n).evaluatorLen * (2 / 2 ^ n)` from `n = 1` on
(`Yao.advantage_idealGame_realGame_kdfDDHProbFamily_garbler_le`). No hardness assumption is
involved. The key length `msgLen n` may grow with `n`. -/
theorem negligible_advantage_kdfDDHProbFamily_garbler
    (hproj : Gs.encode = projectiveEncode) (hcorrect : Gs.Correct)
    (F : PrimeOrderGroupFamily) (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (msgLen : ℕ → ℕ) (c : ℕ → Params Gs)
    (T₁ : (n : ℕ) → (I : Finset (Fin 2)) →
      CoalitionSimulator (schedule (c n)) (Input (c n)) Coins (fun _ => List Bool) I)
    (Sm : (n : ℕ) → (d : F.Desc) → (J : Finset (Fin 2)) → CoalitionSimulator
      (maskedOTSchedule (F.Carrier d) (List Bool)) (OTIn (List Bool))
      (MaskedOTCoins (F.Carrier d)) (OTOut (List Bool)) J)
    (S₂ : (n : ℕ) → (d : F.Desc) → (J : Finset (Fin 2)) →
      CoalitionSimulator (ddhOTSchedule (F.Carrier d)) (OTIn (F.Carrier d))
        (DDHOTCoinsWith DDHOTSenderBitCoins (List Bool)) (OTOut (F.Carrier d)) J)
    (Z : Environment (kdfDDHProbFamily Gs F H c) {0})
    (hT₁ : ∀ n, T₁ n {0} = garblerSim Gs n (c n))
    (hSm : ∀ n d, Sm n d {0} = maskedOTSenderSim (F.kdfPadsProb n d))
    (hS₂ : ∀ n d, S₂ n d {0} = F.ddhOTSenderSimProb n d)
    (hH : ∀ n, ∀ d ∈ (setup n).support, ∀ r : F.Carrier d,
      (H (d, F.encode d r)).length = msgLen n)
    (hlabel : ∀ n, Gs.HasTokenLength n (c n).fn (msgLen n))
    (hk : PolynomiallyBounded fun n => (c n).evaluatorLen) :
    Negligible fun n => Game.advantage
      ((kdfDDHProbFamily Gs F H c).realGame setup {0} Z n)
      ((kdfDDHProbFamily Gs F H c).idealGame setup {0}
        (kdfDDHProbSim F H c T₁ Sm S₂ {0}) Z n) := by
  have hbound : Negligible fun n => ((c n).evaluatorLen : ℝ≥0) * (2 / 2 ^ n) := by
    simpa only [Nat.cast_ofNat] using (negligible_const_div_two_pow 2).polynomiallyBounded_mul hk
  refine negligible_of_eventually_le hbound ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  rw [Game.advantage_comm]
  exact advantage_idealGame_realGame_kdfDDHProbFamily_garbler_le hproj hcorrect F setup H msgLen c
    T₁ Sm S₂ Z hn (hT₁ n) (hSm n) (hS₂ n) (hH n) (hlabel n)

end Cslib.Crypto.Protocols.MPC.Yao
