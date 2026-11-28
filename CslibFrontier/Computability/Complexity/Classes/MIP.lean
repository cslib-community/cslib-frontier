/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.MIP.Defs
public import CslibFrontier.Computability.Complexity.Classes.MIP.OptimalProver
public import CslibFrontier.Computability.Complexity.Classes.MIP.NEXP
public import CslibFrontier.Computability.Complexity.Classes.MIP.Oracularization
public import CslibFrontier.Computability.Complexity.Classes.MIP.PCP

/-!
# Multiprover interactive proofs (`MIP₂` and `MIP`)

This umbrella module re-exports the multiprover interactive proof development:

* `CslibFrontier.Computability.Complexity.Classes.MIP.Defs`: non-communicating prover families
  (`Prover.independent`, `Prover.independent_state_eq_of_ne`), `IsMultiproverProof`, the classes
  `MIP₂` and `MIP`, closure under polynomial-time many-one reductions (`PolyTimeReducible.mem_MIP₂`,
  `PolyTimeReducible.mem_MIP`), and the embeddings `IP ⊆ MIP₂ ⊆ MIP`.
  The number of provers is constant for each language.
* `CslibFrontier.Computability.Complexity.Classes.MIP.OptimalProver`: coordinatewise presampling and
  deterministic prover optimality (`MIP.exists_deterministic_prover_family`) using generic
  multi-channel coin-fixing (`Interaction.acceptProb_eq_sum`), and pairwise history consistency
  (`MIP.consistentHist`, `MIP.DetProver.ValidFrom.consistentHist`,
  `MIP.validFrom_candidateProver`).
* `CslibFrontier.Computability.Complexity.Classes.MIP.NEXP`: polynomial-time multi-channel
  transcript
  verification, the exponential-padding translation in `Classes.Padding`, and the unconditional
  upper bounds
  `MIP_subset_NEXP : MIP enc ⊆ NEXP enc` and `MIP₂_subset_NEXP : MIP₂ enc ⊆ NEXP enc`.
* `CslibFrontier.Computability.Complexity.Classes.MIP.Oracularization`: simulation of strict
  adaptive proof-oracle verifiers by two classical provers (`PCPPoly_subset_MIP₂`).
* `CslibFrontier.Computability.Complexity.Classes.MIP.PCP`: a strict polynomial-time verifier
  checks an arithmetized exponential computation using a fixed bit-valued proof oracle.

## Main results

* `Cslib.Complexity.NEXP_subset_MIP₂` gives an interactive protocol with two provers.
* `Cslib.Complexity.MIP₂_eq_NEXP` and `Cslib.Complexity.MIP_eq_NEXP` characterize the
  classes with two provers and with a constant number of provers.

## References

* [M. Ben-Or, S. Goldwasser, J. Kilian, A. Wigderson, *Multi-prover interactive proofs: How to
  remove intractability assumptions*][BenOrGoldwasserKilianWigderson1988]
* [L. Babai, L. Fortnow, C. Lund, *Non-deterministic exponential time has two-prover interactive
  protocols*][BabaiFortnowLund1991]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

public section

namespace Cslib.Complexity

variable {α : Type} {enc : α ↪ List Bool}

/-- Every encoded language in nondeterministic exponential time has a strict polynomial-time
verifier interacting with two classical noncommunicating provers. The verifier first uses the
arithmetized computation as a bit-oracle proof, then checks an oracle answer with a second prover
[Babai, Fortnow and Lund, Theorem 1.1, p. 4, and §3.4][BabaiFortnowLund1991]. -/
theorem NEXP_subset_MIP₂ : NEXP enc ⊆ MIP₂ enc :=
  NEXP_subset_PCPPoly.trans PCPPoly_subset_MIP₂

/-- **Babai–Fortnow–Lund** [Theorem 1.1, p. 4][BabaiFortnowLund1991]. Two independently stateful,
noncommunicating provers and a strict polynomial-time private-coin verifier recognize
exactly nondeterministic exponential time. Here the completeness and soundness thresholds are
`2/3` and `1/3`. The source uses amplified errors (§2, p. 6). -/
theorem MIP₂_eq_NEXP (enc : α ↪ List Bool) : MIP₂ enc = NEXP enc :=
  (MIP₂_subset_NEXP enc).antisymm NEXP_subset_MIP₂

/-- Allowing a finite number of provers fixed for each language also gives `NEXP`. -/
theorem MIP_eq_NEXP (enc : α ↪ List Bool) : MIP enc = NEXP enc :=
  (MIP_subset_NEXP enc).antisymm (NEXP_subset_MIP₂.trans (MIP₂_subset_MIP enc))

end Cslib.Complexity
