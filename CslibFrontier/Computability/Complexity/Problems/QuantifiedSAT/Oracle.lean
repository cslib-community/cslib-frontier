/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.QuantifiedSAT.Completeness
public import CslibFrontier.Computability.Complexity.Classes.PH.Oracle
public import CslibFrontier.Computability.Complexity.Classes.PH.Image
import CslibFrontier.Computability.Complexity.Classes.Oracle.TQBF
import CslibFrontier.Computability.Complexity.CookLevin.Completeness

/-!
# Complete SAT oracles for the polynomial hierarchy

The native oracle classes ask raw bit-string languages. The oracle `encQBF '' SigmaSAT k`
rejects malformed encodings and answers the existing formula-level complete language on valid
ones. For every positive `k`, this oracle characterizes `Σₖ₊₁` and replaces the union over
all `Σₖ` oracles in deterministic polynomial time.

These are [Arora–Barak, web draft 2007-01-08, Theorem 5.15 and Exercise 5 §7][AroraBarak07]
and [Goldreich, January 2007 draft, Exercise 3.10(2)][Goldreich2007DraftR2]. The matrix is an
unrestricted quantifier-free Boolean formula and variable identifiers are binary, as in
`SigmaSAT_sigmaPComplete`. The first-level SAT oracle uses the existing CNF encoding.
## Main results

* `SigmaP_succ_eq_NPWithOracle_SigmaSAT`: the all-level quantified SAT oracle equality.
* `iUnion_PWithOracle_eq_PWithOracle_SigmaSAT`: complete-oracle replacement for deterministic time.
* `SigmaP_two_eq_NPWithOracle_SAT`: the CNF SAT specialization.

-/

public section
namespace Cslib.Complexity
open Turing.MultiTapeTM
variable {α : Type} {k : ℕ}

/-- The raw-word `ΣₖSAT` oracle is `Σₖ`-complete; malformed words are outside the language. -/
theorem image_SigmaSAT_sigmaPComplete (hk : 1 ≤ k) :
    SigmaPComplete k encBits (encQBF '' SigmaSAT k) :=
  (SigmaSAT_sigmaPComplete hk).image
    { decode := TQBF.decodeQBF
      decode_enc := TQBF.decodeQBF_encQBF
      computable := TQBF.decodeQBF_pt.exists_degree }

/-- **Arora–Barak Theorem 5.15 / Goldreich Exercise 3.10(2):**
`Σₖ₊₁ = NP^{ΣₖSAT}` for every `k ≥ 1`, on every instance encoding. -/
theorem SigmaP_succ_eq_NPWithOracle_SigmaSAT (hk : 1 ≤ k) (enc : α ↪ List Bool) :
    SigmaP (k + 1) enc = NPWithOracle (encQBF '' SigmaSAT k) enc :=
  (image_SigmaSAT_sigmaPComplete hk).SigmaP_succ_eq_NPWithOracle enc

/-- **Goldreich Exercise 3.10(2), deterministic half:** `P^{Σₖ} = P^{kQBF}`. -/
theorem iUnion_PWithOracle_eq_PWithOracle_SigmaSAT (hk : 1 ≤ k) (enc : α ↪ List Bool) :
    (⋃ O ∈ SigmaP k encBits, PWithOracle O enc) =
      PWithOracle (encQBF '' SigmaSAT k) enc :=
  (image_SigmaSAT_sigmaPComplete hk).iUnion_PWithOracle_eq enc

/-- **Arora–Barak Exercise 5 §7:** `Σ₂ = NP^SAT` for the existing CNF SAT encoding.
Both positive and negative oracle answers are certified by the transcript simulation. -/
theorem SigmaP_two_eq_NPWithOracle_SAT (enc : α ↪ List Bool) :
    SigmaP 2 enc = NPWithOracle (encCNF '' SAT) enc :=
  (show SigmaPComplete 1 encBits (encCNF '' SAT) from
    (sigmaPComplete_one_iff.mpr CookLevin.SAT_npComplete).image
      (.list (.list (.pair .nat .bool)))).SigmaP_succ_eq_NPWithOracle enc

end Cslib.Complexity
