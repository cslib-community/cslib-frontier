/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.IP.Repetition
public import CslibFrontier.Computability.Complexity.Reduction
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Foundations.Analysis.ENNRealOneSubInvPow

/-!
# Probabilistically checkable proofs against a proof oracle

`PCPPoly` is the class of problems with an adaptive probabilistically checkable proof of
polynomial randomness and polynomially many queries: a strict oracle-PPT verifier
(`Cslib.Probability.IsOraclePPTOn`) queries a proof, a function from query words to bits served by
the stateless prover `Cslib.Complexity.Prover.ofProof`. Some proof is accepted with certainty on
every member, and every proof is accepted with probability at most `1 / 2` on every non-member
[Babai, Fortnow and Lund][BabaiFortnowLund1991], [Arora and Barak, Section 8.5][AroraBarak09].

Unlike `Cslib.Complexity.PCP`, whose verifier is nonadaptive and reads a finite proof string, the
verifier here may choose each query from the earlier answers, and can address exponentially many
locations for a given input length. This is the oracle model used in step 1 of the combined proof of
Theorems 2.3 and 2.4 in [Babai, Fortnow and Lund, §2, pp. 5–6][BabaiFortnowLund1991].
The implication `PCPPoly ⊆ MIP₂`
(`Cslib.Complexity.PCPPoly_subset_MIP₂`) is the oracularization of
`CslibFrontier/Computability/Complexity/Classes/MIP/Oracularization.lean`.

## Main definitions

* `Cslib.Complexity.Prover.ofProof`: the proof oracle of a bit-valued proof.
* `Cslib.Complexity.PCPPoly`: adaptive PCPs with polynomial randomness and queries.

## Main results

* `Cslib.Complexity.mem_PCPPoly_of_inverse_gap`: perfect completeness and an inverse-polynomial
  rejection probability suffice, by repeating on the same proof.
* `Cslib.Complexity.PolyTimeReducible.mem_PCPPoly`: closure under polynomial-time reductions.

## References

* [L. Babai, L. Fortnow, C. Lund, *Non-deterministic exponential time has two-prover interactive
  protocols*][BabaiFortnowLund1991]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Probability Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

/-- The **proof oracle** of the bit string `π : List Bool → Bool`, answering every query `q` by the
one-bit word `[π q]`, with no state. -/
noncomputable abbrev Prover.ofProof {Operation : Type} (π : List Bool → Bool) :
    Prover Operation where
  State := Unit
  init := ()
  respond q s := PMF.pure ([π q.2], s)

/-- **Probabilistically checkable proofs with polynomial randomness and queries**: the problems
with a strict oracle-PPT verifier that accepts some proof with certainty on every member, and every
proof with probability at most `1 / 2` on every non-member. A proof is a function from query words
to bits, with unrestricted support. -/
def PCPPoly (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ verifier : α → WordOracleComp Unit Bool, IsOraclePPTOn enc encBool verifier ∧
    (∀ a ∈ A, ∃ π, acceptProb (verifier a) (Prover.ofProof π) = 1) ∧
    ∀ a ∉ A, ∀ π, acceptProb (verifier a) (Prover.ofProof π) ≤ 1 / 2}

/-- Sequential repetitions against a fixed proof have acceptance probability equal to the
corresponding power of the single-run probability. -/
theorem acceptProb_sequentialRepeat_ofProof {Operation : Type} (k : ℕ)
    (V : WordOracleComp Operation Bool)
    (π : List Bool → Bool) :
    acceptProb (sequentialRepeat k V) (Prover.ofProof π) = (acceptProb V (Prover.ofProof π)) ^ k :=
  le_antisymm (acceptProb_sequentialRepeat_le_of_forall_init _ (fun s => by cases s; rfl) k)
    (le_acceptProb_sequentialRepeat _ (fun s => by cases s; rfl) k)

/-- A perfectly complete adaptive proof-oracle verifier whose rejection probability on each
nonmember is at least `1 / k a` gives membership in `PCPPoly`. The positive denominator is
computed in unary polynomial time, so the verifier can repeat `k a` times on the same proof. -/
theorem mem_PCPPoly_of_inverse_gap {A : Set α} {V : α → WordOracleComp Unit Bool} {k : α → ℕ}
    (hV : IsOraclePPTOn enc encBool V) (hk : ComputableInPolyTime k enc encUnary)
    (hpos : ∀ a, 0 < k a)
    (hc : ∀ a ∈ A, ∃ π, acceptProb (V a) (Prover.ofProof π) = 1)
    (hs : ∀ a ∉ A, ∀ π, acceptProb (V a) (Prover.ofProof π) ≤ 1 - (k a : ENNReal)⁻¹) :
    A ∈ PCPPoly enc := by
  refine ⟨fun a => sequentialRepeat (k a) (V a), hV.sequentialRepeat_count hk, ?_, ?_⟩
  · intro a ha
    obtain ⟨π, hπ⟩ := hc a ha
    exact ⟨π, by rw [acceptProb_sequentialRepeat_ofProof, hπ, one_pow]⟩
  · intro a ha π
    rw [acceptProb_sequentialRepeat_ofProof, one_div]
    exact (pow_le_pow_left' (hs a ha π) _).trans (ENNReal.one_sub_inv_pow_le_inv_two (hpos a).ne')

/-- **`PCPPoly` is closed under polynomial-time reductions.** -/
theorem PolyTimeReducible.mem_PCPPoly {β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {A : Set α} {B : Set β} (hred : PolyTimeReducible encA encB A B) (hB : B ∈ PCPPoly encB) :
    A ∈ PCPPoly encA := by
  obtain ⟨f, hf, hAB⟩ := hred
  obtain ⟨V, hV, hc, hs⟩ := hB
  refine ⟨fun a => V (f a), IsOraclePPTOn.preprocess hV hf, fun a ha => hc _ ((hAB a).mp ha),
    fun a ha => hs _ fun h => ha ((hAB a).mpr h)⟩

end Cslib.Complexity
