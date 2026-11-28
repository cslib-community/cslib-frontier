/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.FIPS204
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.DPi
public import CslibFrontier.Computability.Probabilistic.PPT
public import CslibFrontier.Languages.Probabilistic.Vector
public import CslibFrontier.Probability.StatisticalDistance.Product
import CslibFrontier.Computability.Probabilistic.RejectionSampling
import CslibFrontier.Computability.Probabilistic.Repeat
import CslibFrontier.Computability.Probabilistic.Vector
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Languages.Probabilistic.Oracle.Vector
import CslibFrontier.Languages.Probabilistic.RejectionSampling

/-!
# Auxiliary ML-DSA matrix sampling from bounded fair coins

A reduction simulating a matrix random oracle needs fresh independent matrices. A 23-bit
candidate is accepted at 8380417 of its 8388608 values. Capping the attempts at each
coefficient gives a strict fair-bit program with a statistical loss for its entire saved tape.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204.MatrixOracle

open Cslib.Probability OracleComp Turing.MultiTapeTM
open scoped Cslib.Probability.PMF

/-- Draw a matrix from fair bits with a fixed budget per coefficient. Each attempt reads 23
bits and accepts its unsigned value if it is below the modulus. An exhausted coefficient is
zero. This samples auxiliary random-oracle answers in the reduction. -/
noncomputable def sampleMatrixFair (s : Level) (attempts : ℕ) : ProbComp (PublicMatrix s) :=
  replicateFin s.params.k (replicateFin s.params.ℓ (replicateFin 256
    (ProbComp.sampleBlockCapped (uniformFinRejectionSpec 8380417) 0 attempts)))

private theorem cost_sampleList (cost : ℕ → ℕ) (n : ℕ) :
    IsCostBounded cost (BitString.sampleList n) (n * cost 1) := by
  induction n with
  | zero => exact .pure _ _
  | succ n ih =>
    have hb : IsCostBounded cost (ProbComp.uniform Bool) (cost 1) :=
      (isCostBounded_map_iff _ _ _).mpr (IsCostBounded.query 1)
    rw [BitString.sampleList, Nat.succ_mul, Nat.add_comm]
    exact hb.bind fun bit => ih.bind fun rest => .pure (bit :: rest) 0

/-- On every path the matrix tape costs at most 23 times the number of coefficient attempts
times the price of one fair bit (query `1` selects from `Fin 2`). Giving all other queries
unit price and fair bits price zero also shows the program uses only fair bits. -/
theorem cost_matrixTapeFair_le (s : Level) (Q attempts : ℕ) (cost : ℕ → ℕ) :
    IsCostBounded cost (replicateFin Q (sampleMatrixFair s attempts))
      (Q * s.params.k * s.params.ℓ * 256 * attempts * 23 * cost 1) := by
  simp only [Nat.mul_assoc]
  iterate 4
    apply isCostBounded_pi
    intro _
  unfold ProbComp.sampleBlockCapped ProbComp.sampleSeededTrials
  rw [isCostBounded_map_iff, isCostBounded_map_iff,
    show (uniformFinRejectionSpec 8380417).width = 23 by decide]
  simpa only [Nat.mul_assoc] using cost_sampleList cost (attempts * 23)

private theorem dist_replicateFin_uniform {α : Type} [Fintype α] [Nonempty α]
    (draw : ProbComp α) (n : ℕ) {δ : ℝ} (h : dist draw.eval (PMF.uniformOfFintype α) ≤ δ) :
    dist (ProbComp.eval (replicateFin n draw)) (PMF.uniformOfFintype (Fin n → α)) ≤ n * δ := by
  rw [ProbComp.eval_replicateFin, ← PMF.iid_eq_pi, ← PMF.iid_uniformOfFintype]
  exact (PMF.dist_iid_le _ _ n).trans (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg n))

/-- Statistical distance of all `Q` independent matrices in a saved reduction tape, including
the zero fallback on exhaustion. There are 4096, 7680 and 14336 coefficients per matrix at
ML-DSA-44, -65 and -87, respectively. The sampler draws exactly 23 bits per attempt. -/
theorem dist_matrixTapeFair_le (s : Level) (Q attempts : ℕ) :
    dist (ProbComp.eval (replicateFin Q (sampleMatrixFair s attempts)))
      (PMF.uniformOfFintype (Fin Q → PublicMatrix s)) ≤
        (Q * s.params.k * s.params.ℓ * 256 : ℕ) * (8191 / 8388608 : ℝ) ^ attempts := by
  let spec := uniformFinRejectionSpec 8380417
  have ha := congrArg ENNReal.toReal (spec.acceptProb_add_rejectProb)
  have hfin : spec.acceptProb ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  rw [ENNReal.toReal_add hfin spec.rejectProb_ne_top,
    acceptProb_uniformFinRejectionSpec, show Nat.clog 2 8380417 = 23 by decide,
    ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast,
    ENNReal.toReal_one] at ha
  have hr : spec.rejectProb.toReal = 8191 / 8388608 := by norm_num at ha ⊢; linarith
  have h := BlockRejectionSpec.dist_runCapped_le (singleLaw_uniformFinRejectionSpec_some 8380417)
    0 attempts
  rw [← ProbComp.eval_sampleBlockCapped, ENNReal.toReal_pow, hr] at h
  have ht := dist_replicateFin_uniform _ Q (dist_replicateFin_uniform _ s.params.k
    (dist_replicateFin_uniform _ s.params.ℓ (dist_replicateFin_uniform _ 256 h)))
  simp only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc]
  convert ht using 1
  congr 2

/-- Rows, columns and polynomial coefficients in increasing index order, with each list
entry framed and residues in binary.
The reduction saves a framed list of matrices with this encoding. -/
abbrev encPublicMatrix (s : Level) : PublicMatrix s ↪ List Bool :=
  encFinFn s.params.k (encFinFn s.params.ℓ (encFinFn 256 (Fin.valEmbedding.trans encNat)))

open ComputableInPolyTime in
/-- A strict fair-coin machine samples the list of matrices used in the reduction. Both the
matrix count and the retry budget may vary with the input and are charged in unary.
The clock includes writing every framed binary coefficient of the saved tape. -/
theorem isPPTOn_matrixTapeFair {α : Type} {input : α ↪ List Bool} (s : Level)
    {count attempts : α → ℕ} (hcount : ComputableInPolyTime count input encUnary)
    (hattempts : ComputableInPolyTime attempts input encUnary) :
    IsPPTOn input (encList (encPublicMatrix s))
      (fun x => List.ofFn <$> replicateFin (count x) (sampleMatrixFair s (attempts x))) := by
  let enc : Fin 8380417 ↪ List Bool := Fin.valEmbedding.trans encNat
  let spec := uniformFinRejectionSpec 8380417
  have hval := bitsBinaryValue.comp (snd input encBits)
  have htry : ComputableInPolyTime (fun p : α × List Bool => spec.attempt p.2)
      (encPair input encBits) (encOption enc) := by
    refine (ite' (binary_lt' hval (const 8380417))
      (hval.trans (optionSome encNat)) (const none)).of_enc_eq fun p => ?_
    by_cases h : BitString.binaryValue p.2 < 8380417 <;>
      simp [spec, uniformFinRejectionSpec, finCutoffSpec, h, enc]
  have hcoeff : IsPPTOn input enc (fun a => ProbComp.sampleBlockCapped spec 0 (attempts a)) :=
    isPPTOn_sampleBlockCapped hattempts (const spec.width) htry (const 0)
  have hmatrix : IsPPTOn input (encPublicMatrix s) (fun a => sampleMatrixFair s (attempts a)) :=
    ((hcoeff.replicateFin 256).replicateFin s.params.ℓ).replicateFin s.params.k
  simpa only [map_ofFn_replicateFin] using hmatrix.replicate hcount

end Cslib.Crypto.MLDSA.FIPS204.MatrixOracle
