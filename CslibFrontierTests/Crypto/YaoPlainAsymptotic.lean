/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Protocols.MPC.EmptyCoalition
import CslibFrontier.Crypto.Protocols.MPC.Yao.PlainDDHOT.Asymptotic
import CslibFrontier.Crypto.Protocols.MPC.Yao.PlainDDHOT.Encoding
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Probabilistic.UniformNat

/-!
# Tests for the asymptotic bounds of Yao's protocol in the plain model

A client of `CslibFrontier.Crypto.Protocols.MPC.Yao.PlainDDHOT.Asymptotic` under module
encapsulation. Nothing here is a PPT certificate for a simulator or a reduction of
`Yao.kdfDDHProbFamily`, and `ProtocolFamily.SemiHonestSecure` is not proved for a corrupted party
(#6045, criterion 2).

* The convention "the family of function descriptions is uniform" is satisfiable: a constant family
  is computed in polynomial time.
* From the convention, the number of transfers is polynomially bounded, and the transfer index of
  `Yao.kdfDDHDrawnTransferEnv` is drawn by a uniform strict PPT program.
* The width `Nat.log 2 k + 1` covers `k` transfers and costs a factor of at most `2 * k + 2`,
  checked on small `k`, including the boundary `k = 0` and powers of two.
* With no corrupted party, `Yao.kdfDDHProbFamily` satisfies `ProtocolFamily.SemiHonestSecure` for
  `Yao.kdfDDHProbEncoding`, by the statistical bound for a corrupted garbler: the environment sees
  the outputs only. The simulator families are arguments because the composed simulator is built
  from families over all coalitions, and only their values at `{0}` are used.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.YaoPlainAsymptotic

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.Garbling Cslib.Crypto.Protocols.MPC
  Turing.MultiTapeTM

variable {Fn : Type} {Gs : Scheme Fn}

/-- The convention is satisfiable: a constant family of function descriptions is uniform. -/
example (encFn : Fn ↪ List Bool) (c₀ : Yao.Params Gs) :
    ComputableInPolyTime (fun _ : ℕ => c₀) encUnary (Yao.encParams encFn) :=
  .const _

/-- From the convention to the polynomial bound on the number of transfers. -/
example {encFn : Fn ↪ List Bool} {c : ℕ → Yao.Params Gs}
    (hc : ComputableInPolyTime c encUnary (Yao.encParams encFn))
    (hinLen : ComputableInPolyTime Gs.inLen encFn encUnary) :
    PolynomiallyBounded fun n => (c n).evaluatorLen :=
  (Yao.encParams_evaluatorLen_polyTime hc hinLen).polynomiallyBounded

/-- From the convention, the transfer index is drawn by a uniform strict PPT program. -/
example {encFn : Fn ↪ List Bool} {c : ℕ → Yao.Params Gs}
    (hc : ComputableInPolyTime c encUnary (Yao.encParams encFn))
    (hinLen : ComputableInPolyTime Gs.inLen encFn encUnary) :
    IsPPTOn encUnary encNat
      fun n => ProbComp.sampleBinaryNat (Nat.log 2 (c n).evaluatorLen + 1) :=
  isPPTOn_sampleBinaryNat.preprocess (ComputableInPolyTime.unary_succ.comp
    ((ComputableInPolyTime.binary_log_two.comp ComputableInPolyTime.unary_to_binary).comp
      (Yao.encParams_evaluatorLen_polyTime hc hinLen)))

/-- The width `Nat.log 2 k + 1` covers `k` transfers at a factor of at most `2 * k + 2`. -/
example : ∀ k < 20, k ≤ 2 ^ (Nat.log 2 k + 1) ∧ 2 ^ (Nat.log 2 k + 1) ≤ 2 * k + 2 := by
  decide

/-- **No corrupted party.** `Yao.kdfDDHProbFamily` is semi-honest secure against the empty
coalition for `Yao.kdfDDHProbEncoding` when the number of transfers is polynomially bounded: the
statistical bound for a corrupted garbler holds for every environment, and an environment with no
corrupted party sees the outputs only. The key length `msgLen n` may grow with `n`: it is asked
only of the group descriptions that the setup draws at `n`. -/
example (hproj : Gs.encode = projectiveEncode) (hcorrect : Gs.Correct)
    (F : PrimeOrderGroupFamily) (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (msgLen : ℕ → ℕ) (c : ℕ → Yao.Params Gs)
    (T₁ : (n : ℕ) → (I : Finset (Fin 2)) →
      CoalitionSimulator (Yao.schedule (c n)) (Yao.Input (c n)) Yao.Coins (fun _ => List Bool) I)
    (Sm : (n : ℕ) → (d : F.Desc) → (J : Finset (Fin 2)) → CoalitionSimulator
      (maskedOTSchedule (F.Carrier d) (List Bool)) (OTIn (List Bool))
      (MaskedOTCoins (F.Carrier d)) (OTOut (List Bool)) J)
    (S₂ : (n : ℕ) → (d : F.Desc) → (J : Finset (Fin 2)) →
      CoalitionSimulator (ddhOTSchedule (F.Carrier d)) (OTIn (F.Carrier d))
        (DDHOTCoinsWith DDHOTSenderBitCoins (List Bool)) (OTOut (F.Carrier d)) J)
    (hT₁ : ∀ n, T₁ n {0} = Yao.garblerSim Gs n (c n))
    (hSm : ∀ n d, Sm n d {0} = maskedOTSenderSim (F.kdfPadsProb n d))
    (hS₂ : ∀ n d, S₂ n d {0} = F.ddhOTSenderSimProb n d)
    (hH : ∀ n, ∀ d ∈ (setup n).support, ∀ r : F.Carrier d,
      (H (d, F.encode d r)).length = msgLen n)
    (hlabel : ∀ n, Gs.HasTokenLength n (c n).fn (msgLen n))
    (hk : PolynomiallyBounded fun n => (c n).evaluatorLen) :
    (Yao.kdfDDHProbFamily Gs F H c).SemiHonestSecure setup ∅
      (Yao.kdfDDHProbEncoding Gs F H c) :=
  ProtocolFamily.SemiHonestSecure.empty_of_forall_negligible
    (S := Yao.kdfDDHProbSim F H c T₁ Sm S₂ {0})
    (fun Z => Yao.negligible_advantage_kdfDDHProbFamily_garbler hproj hcorrect F setup H msgLen c
      T₁ Sm S₂ Z hT₁ hSm hS₂ hH hlabel hk) _

end CslibFrontierTests.Crypto.YaoPlainAsymptotic
