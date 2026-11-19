/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.TwoProverGame.AnchoredTranscript
import CslibFrontier.Computability.PCP.TwoProverGame.Tsirelson

/-! # Anchoring the CHSH game -/

set_option linter.privateModule false

open Cslib.PCP.TwoProverGame
open scoped unitInterval Real ENNReal

private noncomputable def half : I := ⟨1 / 2, by constructor <;> norm_num⟩

example : (chsh.anchored half).questions (none, none) = 1 / 4 := by
  rw [anchored_questions_apply]
  norm_num [half, ENNReal.ofReal_div_of_pos]
  rw [← ENNReal.inv_pow]
  norm_num

example : (chsh.anchored half).value = 15 / 16 := by
  rw [value_anchored, value_chsh]
  norm_num [half]

example : (chsh.anchored half).quantumValue = 1 - (1 - Real.cos (π / 8) ^ 2) / 4 := by
  rw [quantumValue_anchored, quantumValue_chsh]
  norm_num [half]
  ring

/-- Drawing the noisy reveal independently at each coordinate recovers repeated anchored CHSH. -/
example (n : ℕ) :
    (Cslib.Probability.PMF.pi fun _ : Fin n =>
      Cslib.PCP.AnchoredDependency.law chsh.questions half).map
        (fun samples => (Prod.fst ∘ Prod.snd ∘ samples, Prod.snd ∘ Prod.snd ∘ samples)) =
          ((chsh.anchored half).pow n).questions :=
  Cslib.PCP.AnchoredDependency.map_questions_pi_law chsh half n

/-- Checking one coordinate of two-copy CHSH leaves the verifier's question law intact. -/
example (S : Cslib.PCP.QuantumStrategy (Fin 2 → Option Bool) (Fin 2 → Option Bool)
    (Fin 2 → Bool) (Fin 2 → Bool) (Fin 2) (Fin 2)) :
    (Cslib.PCP.AnchoredDependency.transcriptLaw chsh half {0} S).map
      (fun r => let ((t, _), u) := r; t.combine u) =
        Cslib.Probability.PMF.pi (fun _ : Fin 2 => (chsh.anchored half).questions) :=
  Cslib.PCP.AnchoredDependency.map_questionPairs_transcriptLaw chsh half {0} S


open Cslib.PCP.AnchoredDependency
open Cslib.Probability.PMF (conditionalSnd)

/-- The other retained data have the same probabilities with or without the noisy message
when both questions at the left-out coordinate are anchors. -/
example (S : Cslib.PCP.QuantumStrategy (Fin 2 → Option Bool) (Fin 2 → Option Bool)
    (Fin 2 → Bool) (Fin 2 → Bool) (Fin 2) (Fin 2))
    (hW : ∃ r ∈ winsOnChecked chsh half ({0} : Finset (Fin 2)),
      r ∈ (transcriptLaw chsh half {0} S).support)
    (j : {i : Fin 2 // i ∉ ({0} : Finset (Fin 2))}) (m : Option Bool ⊕ Option Bool) :
    let Q := (transcriptLaw chsh half {0} S).filter (winsOnChecked chsh half {0}) hW
    let J := Q.map fun r => (freeTrials {0} r j, restTranscript {0} j r)
    let J' := Q.map fun r => ((freeTrials {0} r j).2, restTranscript {0} j r)
    (m, (none, none)) ∈ (J.map Prod.fst).support →
      ∀ r, conditionalSnd J (m, (none, none)) r = conditionalSnd J' (none, none) r := by
  dsimp only
  intro hs r
  exact congrArg (fun p => p r)
    (conditionalSnd_restTranscript_given_wins chsh half {0} S j hW (m, (none, none)) hs)
