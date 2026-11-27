/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Probabilistic.UniformNat.ModIndex
public import CslibFrontier.Languages.Probabilistic.UniformNat.Residue
public import CslibFrontier.Probability.StatisticalDistance.CloseTo
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.Repeat
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Uniform

/-!
# Two independent field-vector challenges for the tableau protocol

The arithmetic verifier draws two independent vectors of residues from fair bits.
Every sampled coordinate is a canonical representative, and the joint event error is
at most twice the error for one vector.

## Main definitions

* `sampleTableauChallenges` draws the external and sumcheck challenge vectors independently.

## Main results

* `isPPTOn_sampleTableauChallenges` certifies the sampler for unary parameters.
* `exists_vectors_of_mem_support_sampleTableauChallenges` describes all supported pairs.
* `closeTo_sampleTableauChallenges` compares the joint law with uniform field vectors.
-/

public section

namespace Cslib.Complexity.MIP

open Cslib.Probability Turing.MultiTapeTM
open scoped ENNReal

/-- Sample two independent length-`R` vectors, using `R.size + p.size + precision` fair bits
per coordinate and returning unary residues modulo `p`. -/
noncomputable def sampleTableauChallenges (R p precision : ℕ) : ProbComp (List ℕ × List ℕ) := do
  let draw := OracleComp.replicate R (ProbComp.sampleModIndex (R.size + p.size + precision) p)
  let r ← draw
  Prod.mk r <$> draw

/-- The joint tableau challenge sampler is strict PPT when its length, modulus and precision
are polynomial-time unary parameters. Both output vectors contain framed unary residues. -/
theorem isPPTOn_sampleTableauChallenges {α : Type} {enc : α ↪ List Bool}
    {R p precision : α → ℕ} (hR : ComputableInPolyTime R enc encUnary)
    (hp : ComputableInPolyTime p enc encUnary)
    (hprec : ComputableInPolyTime precision enc encUnary) :
    IsPPTOn enc (encPair (encList encUnary) (encList encUnary))
      (fun a => sampleTableauChallenges (R a) (p a) (precision a)) := by
  have hsize {f : α → ℕ} (h : ComputableInPolyTime f enc encUnary) :
      ComputableInPolyTime (fun a => (f a).size) enc encUnary :=
    ComputableInPolyTime.binary_size.comp (ComputableInPolyTime.unary_to_binary.comp h)
  have hr := hsize hR
  have hq := hsize hp
  have hs : IsPPTOn enc (encList encUnary) (fun a => OracleComp.replicate (R a)
      (ProbComp.sampleModIndex ((R a).size + (p a).size + precision a) (p a))) :=
    (isPPTOn_sampleModIndex (by fun_prop) hp).replicate hR
  apply hs.bind_with (second := fun a r => Prod.mk r <$> _)
  exact (hs.preprocess (ComputableInPolyTime.fst enc (encList encUnary))).pair
    (ComputableInPolyTime.snd enc (encList encUnary))

/-- Every supported pair is the list of canonical representatives of two `R`-dimensional
residue vectors, including the unique pair of empty lists at dimension zero. -/
theorem exists_vectors_of_mem_support_sampleTableauChallenges {R p precision : ℕ} [NeZero p]
    {c : List ℕ × List ℕ}
    (hc : c ∈ (ProbComp.eval (sampleTableauChallenges R p precision)).support) :
    ∃ r z : Fin R → ZMod p, c =
      (List.ofFn fun j => (r j).val, List.ofFn fun j => (z j).val) := by
  simp only [sampleTableauChallenges, ProbComp.eval_bind, ProbComp.eval_map,
    _root_.PMF.mem_support_bind_iff, _root_.PMF.mem_support_map_iff] at hc
  obtain ⟨a, ha, b, hb, rfl⟩ := hc
  obtain ⟨r, rfl⟩ := ProbComp.exists_vector_of_mem_support_replicate_sampleModIndex ha
  obtain ⟨z, rfl⟩ := ProbComp.exists_vector_of_mem_support_replicate_sampleModIndex hb
  exact ⟨r, z, rfl⟩

/-- The joint event error of the two bounded-randomness challenges from independent uniform
residue vectors is at most twice `2⁻ᵖʳᵉᶜⁱˢⁱᵒⁿ`. -/
theorem closeTo_sampleTableauChallenges (R p precision : ℕ) [NeZero p] :
    CloseTo (ProbComp.eval (sampleTableauChallenges R p precision))
      ((PMF.uniformOfFintype ((Fin R → ZMod p) × (Fin R → ZMod p))).map fun ⟨r, z⟩ =>
        (List.ofFn fun j => (r j).val, List.ofFn fun j => (z j).val))
      (1 / 2 ^ precision + 1 / 2 ^ precision) := by
  have h := ProbComp.closeTo_replicate_sampleModIndex_precision R p precision
  have joint := h.bind fun r _ => h.map (Prod.mk r)
  apply CloseTo.symm
  convert joint using 1
  · rw [_root_.PMF.bind_map]
    simpa only [Function.comp_def, _root_.PMF.map_comp] using
      (PMF.uniformOfFintype_bind_map (fun (r z : Fin R → ZMod p) =>
        (List.ofFn fun j => (r j).val, List.ofFn fun j => (z j).val))).symm
  · simp only [sampleTableauChallenges, ProbComp.eval_bind, ProbComp.eval_map]

/-- A continuation returning the same law on every pair of field vectors returns that law
after drawing actual bounded-randomness challenges. -/
theorem bind_sampleTableauChallenges_of_forall {α : Type} {R p precision : ℕ} [NeZero p]
    (next : (List ℕ × List ℕ) → PMF α) (law : PMF α)
    (h : ∀ r z : Fin R → ZMod p,
      next (List.ofFn fun j => (r j).val, List.ofFn fun j => (z j).val) = law) :
    (ProbComp.eval (sampleTableauChallenges R p precision)).bind next = law := by
  refine (PMF.bind_congr_on_support _ _ (fun _ => law) fun c hc => ?_).trans
    (_root_.PMF.bind_const _ _)
  obtain ⟨r, z, rfl⟩ := exists_vectors_of_mem_support_sampleTableauChallenges hc
  exact h r z

end Cslib.Complexity.MIP
