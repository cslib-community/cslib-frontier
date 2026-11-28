/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Commitment
public import CslibFrontier.Crypto.Computational.TwoStage
public import CslibFrontier.Crypto.Game.HiddenBit
public import CslibFrontier.Crypto.Game.Inversion
import CslibFrontier.Foundations.Data.BitString.ShortWords

/-!
# Guessing a committed bit

This module derives guessing guarantees from chosen-pair hiding. In the single-bit protocol
of [Naor1991], Section 3, the receiver sends a challenge before seeing the commitment to a fair
bit. Its private coins may influence both that challenge and its later guess.
The auxiliary-input remark of [Naor1991], Section 2, p. 3 of the author's copy, compares the
receiver's chance of guessing a bit after the commit stage with its chance given prior information
alone. Here the prior is any joint distribution on a bit and an auxiliary word. It may be biased
and correlated, and it need not have an efficient sampler.

## Main results

* `Cslib.Crypto.PseudorandomGenerator.naorCommit_guessing_and_binding`: a uniform strict-PPT
  receiver has negligible guessing advantage. Binding error is below $2^{-n}$ at positive length.
* `Cslib.Crypto.StatefulHiding.exists_priorPredictor`: for a strict-PPT receiver of an efficient
  hiding commitment, a single strict-PPT predictor given only the auxiliary word reproduces the
  receiver's guessing probability up to negligible error. The prediction target is the selector of
  the receiver's two choices. Choosing `(false, true)` makes it the actual committed bit.
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped ENNReal

/-- The single-bit protocol of [Naor1991], Section 3, Theorem 3.1, p. 6 of the author's copy.
Here `generator` produces the requested prefix of the pseudorandom stream: `3 * n` bits at every
positive security parameter, and one bit at zero to preserve strict expansion. For an arbitrary
expanding finite-output generator this prefix length is available by truncating to one extra bit
and applying `PseudorandomGenerator.amplify` as in Section 2, p. 4.

A uniform strict-PPT receiver chooses its challenge and saves its state before seeing the
commitment. Its absolute deviation from success probability one half in guessing the fair
committed bit is negligible. For an honest uniform challenge of length `3 * n`, the probability
that some commitment has accepted openings to both bits is strictly below `2⁻ⁿ` for every positive
`n`. In the reveal stage the sender discloses the seed. Acceptance for the asserted bit is
`naorVerify`, which checks the seed length and the recomputed commitment. -/
theorem PseudorandomGenerator.naorCommit_guessing_and_binding {generator : List Bool → List Bool}
    (hG : PseudorandomGenerator generator (fun n => max 1 (3 * n))) :
    (∀ (receiver : ℕ → TwoStage Unit (List Bool) (List Bool) Bool (List Bool)),
      TwoStage.IsPPT encUnit encBits encBits encBool encBits receiver →
      Negligible fun n => Game.guessingAdvantage (ProbComp.eval (Experiment.guessBit fun bit => do
        let (r, state) ← (receiver n).choose ()
        let seed ← BitString.sampleList n
        (receiver n).guess state (naorCommit generator r bit seed)))) ∧
    ∀ n, 0 < n → naorBindingProb generator (fun k => 3 * k) n < (1 / 2 : ℝ≥0∞) ^ n := by
  constructor
  · intro receiver hR
    let R : CommitmentReceiver :=
      { choose := fun n _ => (fun rs => ((rs.1, false, true), rs.2)) <$> (receiver n).choose ()
        guess := fun n => (receiver n).guess }
    have hchoose := hR.choose.preprocess
      ((ComputableInPolyTime.fst encUnary encBits).prod (ComputableInPolyTime.const (b := ())))
    have hR' : R.IsPPT := ⟨IsPPTOn.map hchoose (by fun_prop), hR.guess⟩
    apply negligible_of_le (hG.naorGenerableStatefulHiding.empty R hR')
    intro n
    let worlds b := commitmentHidingGame (naorCommit generator) R [] b n
    change _ ≤ Experiment.advantage (worlds false) (worlds true)
    rw [Experiment.advantage_eq_two_mul_guessingAdvantage_guessBit, two_mul]
    refine le_trans (le_of_eq ?_) le_add_self
    congr 3
    exact funext fun b => by cases b <;> simp [worlds, commitmentHidingGame, R]
  · intro n hn
    simpa only [naorBindingProb, max_eq_right (by lia : 1 ≤ 3 * n)] using
      naorBindingProb_lt_of_three_mul (length := fun k => max 1 (3 * k)) hG.length_eq hn
        (le_max_right 1 (3 * n))

/-- For every efficient commitment receiver, there is an efficient predictor using only the
auxiliary input whose success probability differs negligibly from the receiver's. The predictor
is fixed before the joint law of the secret selector and the auxiliary word, whose supported
lengths have one polynomial bound. To predict the committed bit itself, the receiver chooses
`(false, true)` as its challenge pair.

The predictor runs the receiver with a locally generated commitment to its first choice. This
is an original formulation of the prior-information comparison in [Naor1991], Section 2, p. 3
(author's copy), for a single-bit, two-message commitment with polynomial-length auxiliary
inputs. -/
theorem StatefulHiding.exists_priorPredictor
    {commit : List Bool → Bool → List Bool → List Bool} (hhide : StatefulHiding commit)
    (hcommit : ComputableInPolyTime (fun ⟨r, b, seed⟩ => commit r b seed)
      (encPair encBits encBitOpening) encBits)
    {receiver : CommitmentReceiver} (hR : receiver.IsPPT) :
    ∃ predict : ℕ → List Bool → ProbComp Bool, IsPPT encBool predict ∧
      ∀ (prior : ℕ → PMF (Bool × List Bool)) (bound : ℕ → ℕ), PolynomiallyBounded bound →
        (∀ n x, x ∈ (prior n).support → x.2.length ≤ bound n) →
        Negligible fun n => Game.advantage
          (do
            let (bit, aux) ← prior n
            let guess ← ProbComp.eval (commitmentHidingGame commit receiver aux bit n)
            return guess == bit)
          (predictionExperiment (prior n) Prod.snd Prod.fst
            fun aux => ProbComp.eval (predict n aux)) := by
  refine ⟨fun n aux => commitmentHidingGame commit receiver aux false n,
    isPPT_commitmentHidingGame hcommit hR false, ?_⟩
  intro prior bound hbound hsupport
  let game n aux bit := ProbComp.eval (commitmentHidingGame commit receiver aux bit n)
  let gap n aux := Game.advantage (game n aux false) (game n aux true)
  classical
  -- Hiding permits noncomputable advice, so select the worst bounded word at each parameter.
  choose worst hworst hle using fun n => Finset.exists_max_image
    (BitString.shortWords (bound n)) (gap n) ⟨[], BitString.nil_mem_shortWords _⟩
  have hlen : PolynomiallyBounded (fun n => (worst n).length) :=
    hbound.mono_of_le fun n => BitString.mem_shortWords.mp (hworst n)
  refine negligible_of_le (hhide worst hlen receiver hR) fun n =>
    Game.advantage_bind_le_of_support (prior n) _ _ fun ⟨bit, aux⟩ hx => ?_
  cases bit with
  | false => exact (Game.advantage_self _).trans_le zero_le
  | true =>
    have hId : (fun guess : Bool => guess == true) = id := funext fun | false => rfl | true => rfl
    change Game.advantage ((game n aux true).map _) ((game n aux false).map _) ≤ gap n (worst n)
    simpa only [hId, PMF.map_id, Game.advantage_comm] using
      hle n aux (BitString.mem_shortWords.mpr (hsupport n (true, aux) hx))

end Cslib.Crypto
