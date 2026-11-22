/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Commitment
public import CslibFrontier.Crypto.Game.Inversion
import CslibFrontier.Foundations.Data.BitString.ShortWords

/-!
# Guessing a committed bit with prior information

This module derives a prediction guarantee from chosen-pair hiding.
The auxiliary-input remark of [Naor1991], Section 2, p. 3 of the author's copy, compares the
receiver's chance of guessing a bit after the commit stage with its chance given prior information
alone. Here the prior is any joint distribution on a bit and an auxiliary word. It may be biased
and correlated, and it need not have an efficient sampler.

## Main results

* `Cslib.Crypto.StatefulHiding.exists_priorPredictor`: for a strict-PPT receiver of an efficient
  hiding commitment, a single strict-PPT predictor given only the auxiliary word reproduces the
  receiver's guessing probability up to negligible error. The prediction target is the selector of
  the receiver's two choices. Choosing `(false, true)` makes it the actual committed bit.
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

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
  have hmax (n : ℕ) := Finset.exists_max_image (BitString.shortWords (bound n))
    (gap n) ⟨[], BitString.nil_mem_shortWords _⟩
  choose worst hworst hle using hmax
  have hlen : PolynomiallyBounded (fun n => (worst n).length) :=
    hbound.mono_of_le fun n => BitString.mem_shortWords.mp (hworst n)
  apply negligible_of_le (hhide worst hlen receiver hR)
  intro n
  apply Game.advantage_bind_le_of_support (prior n)
  rintro ⟨bit, aux⟩ hx
  cases bit with
  | false => exact (Game.advantage_self _).trans_le zero_le
  | true =>
    have hId : (fun guess : Bool => guess == true) = id := by funext b; cases b <;> rfl
    change Game.advantage ((game n aux true).map _) ((game n aux false).map _) ≤ gap n (worst n)
    rw [hId, PMF.map_id, PMF.map_id, Game.advantage_comm]
    exact hle n aux (BitString.mem_shortWords.mpr (hsupport n (true, aux) hx))

end Cslib.Crypto
