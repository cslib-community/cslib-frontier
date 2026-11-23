/-
Copyright (c) 2026 Karn Seth, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth, Samuel Schlesinger
-/

module
-- upstream: local-only (test)

public import CslibFrontier.Crypto.Computational.MAC
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Frame.Lookup
import CslibFrontier.Tactic.PPT

/-! The echo MAC shared by the MAC-then-encrypt tests, moved without change from
`CslibFrontierTests.Crypto.MACThenEncrypt` (by Karn Seth and Samuel Schlesinger); it replaces the
copy `CslibFrontierTests.Crypto.MACThenEncryptEncForge` carried. -/

public section

namespace CslibFrontierTests.Crypto.MACThenEncrypt

open Cslib Cslib.Probability Cslib.Crypto Turing.MultiTapeTM

/-- Deterministic echo MAC signing `n`-bit messages by `tag = msg` and checking equality. -/
@[expose] def echoMAC : MACScheme where
  msgLen n := n
  keyGen _ := pure []
  sign _ msg := pure msg
  verify _ msg tag := msg == tag
  keyGen_ppt := by ppt
  sign_ppt := by ppt
  verify_polyTime := by polytime
  verify_sign := by
    intro _ _ _ msg _ tag htag
    simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at htag
    subst htag
    exact beq_self_eq_true _

/-- Every framed `(msg, tag)` pair produced by `echoMAC` on an `n`-bit message has exact length
`3 * n + 1`. -/
theorem echo_pairLen :
    ∀ n km, km ∈ (ProbComp.eval (echoMAC.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ tag ∈ (ProbComp.eval (echoMAC.sign km msg)).support,
        (encPair encBits encBits (msg, tag)).length = 3 * n + 1 := by
  intro n km _ msg hmsg tag htag
  change tag ∈ (ProbComp.eval (pure msg)).support at htag
  simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at htag
  subst htag
  rw [encPair_apply]
  dsimp only
  rw [length_frame_append, encBits_apply, hmsg]
  omega

end CslibFrontierTests.Crypto.MACThenEncrypt
