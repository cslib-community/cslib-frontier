/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Identification
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF.Bind

/-!
# Guessing attacks on Sigma protocols

This module formalizes the generic guessing impersonator against a Sigma protocol in
[BonehShoup2023], Section 19.1.1 and Exercise 19.7. A dishonest prover given an arbitrary
transcript simulator `simulate` commits by sampling a simulated conversation `(t, c₀, z)` and
sending `t`, then answers whatever verifier challenge arrives with `z`. Whenever `simulate`
always produces accepting transcripts, this impersonator wins `SigmaProtocol.directAttack` with
probability at least `(Fintype.card C : ℝ≥0)⁻¹`, without using a witness or any zero-knowledge
indistinguishability property.

## Main definitions

- `SigmaProtocol.guessingImpersonator`: the guessing impersonator built from a transcript
  simulator `simulate : Y → C → PMF (T × Z)`.

## Main results

- `SigmaProtocol.inv_card_le_succProbability_directAttack_guessingImpersonator`: for any
  simulator always outputting accepting transcripts and any key generator `keyGen`,
  `guessingImpersonator simulate` succeeds in `P.directAttack` with probability at least
  `(Fintype.card C : ℝ≥0)⁻¹`.
- `SigmaProtocol.SpecialHVZK.inv_card_le_succProbability_directAttack`: specialization to a
  `SpecialHVZK` simulator (Exercise 19.7).

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  Section 19.1.1 and Exercise 19.7.
-/

public section

namespace Cslib.Crypto.Protocols.SigmaProtocol

open scoped NNReal ENNReal

variable {X Y T C Z : Type} [Fintype C] [Nonempty C]

/-- **The guessing impersonator** ([BonehShoup2023], Section 19.1.1 and Exercise 19.7): given a
transcript simulator `simulate : Y → C → PMF (T × Z)`, sample a simulated conversation
`(t, c₀, z)`, commit `t`, store `z`, and return `z` on any challenge. -/
noncomputable def guessingImpersonator (simulate : Y → C → PMF (T × Z)) :
    Impersonator Y T C Z where
  State := Z
  commit y := (simulateConversation simulate y).map fun (t, _, z) => (t, z)
  respond z _ := PMF.pure z

/-- **Generic guessing bound** ([BonehShoup2023], Exercise 19.7): if `simulate y c` always
outputs accepting `(t, z)`, then `guessingImpersonator simulate` wins `P.directAttack keyGen`
with probability at least `(Fintype.card C : ℝ≥0)⁻¹` (a lower bound where the exercise says
"probability `1/|C|`"). Neither a valid witness in `keyGen` nor simulator indistinguishability is
required. -/
theorem inv_card_le_succProbability_directAttack_guessingImpersonator
    (P : SigmaProtocol X Y T C Z) {simulate : Y → C → PMF (T × Z)}
    (hsim : ∀ y c, ∀ tz ∈ (simulate y c).support, P.Accepts y tz.1 c tz.2)
    (keyGen : PMF (X × Y)) :
    (Fintype.card C : ℝ≥0)⁻¹ ≤
      Game.succProbability (P.directAttack keyGen (guessingImpersonator simulate)) := by
  have key : (Fintype.card C : ℝ≥0∞)⁻¹ ≤
      P.directAttack keyGen (guessingImpersonator simulate) true := by
    simp only [pmf_norm, directAttack, guessingImpersonator, simulateConversation, PMF.map,
      PMF.bind_bind, PMF.pure_bind]
    refine Probability.PMF.le_bind_apply_on_support _ fun key _ => ?_
    refine Probability.PMF.le_bind_apply_on_support _ fun c₀ _ => ?_
    refine Probability.PMF.le_bind_apply_on_support _ fun tz htz => ?_
    rw [PMF.bind_apply]
    refine le_trans ?_ (le_tsum _ c₀)
    have hacc : P.verify key.2 tz.1 c₀ tz.2 = true := hsim key.2 c₀ tz htz
    simp [hacc, Probability.PMF.uniformOfFintype_apply]
  rw [Game.succProbability, ← ENNReal.toNNReal_coe ((Fintype.card C : ℝ≥0)⁻¹)]
  refine ENNReal.toNNReal_mono (PMF.apply_ne_top _ _) ?_
  rwa [ENNReal.coe_inv (by simp), ENNReal.coe_natCast]

/-- The form for special HVZK protocols, as Exercise 19.7 states it: the general guessing bound
instantiated at the simulator of a `SpecialHVZK` Sigma protocol. -/
theorem SpecialHVZK.inv_card_le_succProbability_directAttack {P : SigmaProtocol X Y T C Z}
    {R : X → Y → Prop} {simulate : Y → C → PMF (T × Z)} (h : P.SpecialHVZK R simulate)
    (keyGen : PMF (X × Y)) :
    (Fintype.card C : ℝ≥0)⁻¹ ≤
      Game.succProbability (P.directAttack keyGen (guessingImpersonator simulate)) :=
  inv_card_le_succProbability_directAttack_guessingImpersonator P h.accepts keyGen

end Cslib.Crypto.Protocols.SigmaProtocol
