/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.MIP.Correction
public import CslibFrontier.Languages.Probabilistic.UniformNat.Residue
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Uniform

/-!
# Error of correction along a sampled affine line

The correction verifier samples one direction with bounded fair coins. A rejected line has no
returned value. Under a uniform direction, returning a wrong value requires one of the sampled
points to disagree with the target multilinear function. Replacing the uniform direction by the
fair-bit implementation changes this event probability by at most the joint sampling error.

## Main results

* `correctPoint_wrong_le` bounds the probability of returning an incorrect field representative.
* `run_correctPoint_of_forall` preserves certainty when every direction returns the same value.
-/

public section

namespace Cslib.Complexity.MIP

open Cslib.Code Cslib.Probability Turing.MultiTapeTM QBFProtocol Finset
open scoped ENNReal

/-- If every field direction produces the same checked answer, then sampling with any precision
returns that answer with certainty. -/
theorem run_correctPoint_of_forall (π : List Bool → Bool) {p n : ℕ} [Fact p.Prime]
    (x : Fin n → ZMod p) (y : ℕ) (hall : ∀ v, correctionAnswer π x v = some y)
    (precision : ℕ) :
    (Prover.ofProof π).run (correctPoint p n precision (List.ofFn fun j => (x j).val)) () =
      PMF.pure (some y, ()) := by
  simp only [correctPoint, Prover.run_bind, Prover.run_sample, _root_.PMF.bind_map]
  refine (Probability.PMF.bind_congr_on_support _ _ (fun _ => PMF.pure (some y, ()))
    fun xs hxs => ?_).trans (_root_.PMF.bind_const _ _)
  obtain ⟨v, rfl⟩ := ProbComp.exists_vector_of_mem_support_replicate_sampleModIndex hxs
  exact (run_correctAt π x v).trans (by rw [hall])

/-- The probability of returning a wrong value at a fixed point is at most the relative number
of possible disagreements at the `n + 1` tested nodes plus the statistical sampling error. The
bit proof may give different coefficient replies in every direction. -/
theorem correctPoint_wrong_le (π : List Bool → Bool) {p n : ℕ} [Fact p.Prime] (hp : n + 1 < p)
    {f : (Fin n → ZMod p) → ZMod p} (hf : IsMultilinear f) (x : Fin n → ZMod p)
    (precision : ℕ) :
    (((Prover.ofProof π).run (correctPoint p n precision (List.ofFn fun j => (x j).val)) ()).map
      Prod.fst).toOuterMeasure {o | ∃ y, o = some y ∧ y ≠ (f x).val} ≤
      (n + 1 : ℝ≥0∞) * hammingDist (proofPoint π p) f / p ^ n + 1 / 2 ^ precision := by
  classical
  let point := List.ofFn fun j => (x j).val
  let read (xs : List ℕ) := ((Prover.ofProof π).run (correctAt p n point xs) ()).map Prod.fst
  have hc := (ProbComp.closeTo_replicate_sampleModIndex_precision n p precision).symm.bind_left read
  let ideal := (PMF.uniformOfFintype (Fin n → ZMod p)).map (correctionAnswer π x)
  have hi : ((PMF.uniformOfFintype (Fin n → ZMod p)).map
      (fun v => List.ofFn fun j => (v j).val)).bind read = ideal := by
    rw [_root_.PMF.bind_map]
    unfold ideal
    rw [← _root_.PMF.bind_pure_comp]
    congr 1
    funext v
    change ((Prover.ofProof π).run (correctAt p n _ _) ()).map Prod.fst = PMF.pure _
    rw [run_correctAt, _root_.PMF.pure_map]
  rw [hi] at hc
  let wrong : Set (Option ℕ) := {o | ∃ y, o = some y ∧ y ≠ (f x).val}
  refine le_trans (b := ideal.toOuterMeasure wrong + 1 / 2 ^ precision) ?_ (add_le_add_left ?_ _)
  · simpa only [correctPoint, Prover.run_bind, Prover.run_sample, _root_.PMF.map_bind,
      _root_.PMF.bind_map, Function.comp_apply, read, point, wrong] using hc wrong
  · change ideal.toOuterMeasure wrong ≤ _
    unfold ideal
    rw [ _root_.PMF.toOuterMeasure_map_apply,
      Probability.PMF.toOuterMeasure_uniformOfFintype]
    have hcard := card_checkLineReply_wrong_le hp hf (proofPoint π p) x (correctionReply π x)
    have hsub : (univ.filter fun v => correctionAnswer π x v ∈ wrong) ⊆
        (univ.filter fun v => checkLineReply p n (correctionReply π x v)
          (List.ofFn fun i : Fin (n + 1) =>
            (proofPoint π p (x + ((i.val + 1 : ℕ) : ZMod p) • v)).val) = true ∧
          (hornerMod p 0 (decodeReply p n (correctionReply π x v)) : ZMod p) ≠ f x) := by
      intro v hv
      simp only [mem_filter, mem_univ, true_and] at hv ⊢
      simp only [correctionAnswer] at hv
      split at hv
      · rename_i hcheck
        refine ⟨hcheck, fun h => ?_⟩
        have he := congrArg ZMod.val h
        rw [ZMod.val_natCast_of_lt (hornerMod_lt _ _)] at he
        simp [wrong, he] at hv
      · simp [wrong] at hv
    have h := (card_le_card hsub).trans hcard
    simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_pow]
    rw [← div_eq_mul_inv]
    refine ENNReal.div_le_div_right ?_ _
    simpa only [Set.mem_preimage, hammingDist] using (show
      ((univ.filter fun v => correctionAnswer π x v ∈ wrong).card : ℝ≥0∞) ≤
        (n + 1 : ℝ≥0∞) * (hammingDist (proofPoint π p) f : ℕ) by exact_mod_cast h)

end Cslib.Complexity.MIP
