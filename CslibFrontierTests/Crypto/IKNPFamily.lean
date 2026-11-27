/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Protocols.MPC.IKNP.Family

/-! # IKNP oblivious-transfer extension as a protocol family: module clients

Clients of `CslibFrontier.Crypto.Protocols.MPC.IKNP.Family` under module encapsulation:
* the encoded words of a receiver's view, and the receiver's input word;
* the PPT certificates of both simulator families;
* `CorrelationRobust.iknpSemiHonestSecure` at a linear number of transfers, unfolded to the
  receiver's simulator. -/

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.Protocols.MPC Turing.MultiTapeTM

public section

namespace CslibFrontierTests.Crypto.IKNPFamily

-- The encoded words of a receiver's view: its choice bits, its rows and the two masked words,
-- all but the last framed.
example (w : IKNPReceiverViewWords) :
    encIKNPReceiverViewWords w =
      encPair encBits (encPair (encList encBits) (encPair encBits encBits))
        (w.choices, w.rows, w.masked₀, w.masked₁) :=
  encIKNPReceiverViewWords_apply w

-- The receiver's input is written as the word of its choice bits.
example (hash : List Bool → Bool) (m : ℕ → ℕ) (n : ℕ) (r : Fin (m n) → Bool) :
    (iknpEncoding hash m).input.rep n () 1 r = List.ofFn r :=
  rfl

-- Both simulator families are PPT, the receiver's for a hash computed in polynomial time.
example (hash : List Bool → Bool) (m : ℕ → ℕ) (hh : ComputableInPolyTime hash encBits encBool) :
    SimulatorFamily.IsPPT (iknpEncoding hash m) (P := iknpFamily hash m)
        (fun n _ => iknpSenderSim n (m n) Bool) ∧
      SimulatorFamily.IsPPT (iknpEncoding hash m) (P := iknpFamily hash m)
        (fun n _ => iknpReceiverSim (CorrelationRobust.atLevel hash n (m n))) :=
  ⟨isPPT_iknpSenderSim hash m, isPPT_iknpReceiverSim hash m hh⟩

-- With `n` transfers at the security parameter `n`, a correlation-robust hash gives a PPT
-- simulator family for a corrupted receiver.
example (hash : List Bool → Bool) (h : CorrelationRobust hash) :
    ∃ S : SimulatorFamily (iknpFamily hash id) {1}, S.IsPPT (iknpEncoding hash id) := by
  have hm : PolynomiallyBounded (id : ℕ → ℕ) := ⟨1, .of_forall fun n => by simp⟩
  obtain ⟨S, hS, -⟩ := (h.iknpSemiHonestSecure hm).2
  exact ⟨S, hS⟩

end CslibFrontierTests.Crypto.IKNPFamily
