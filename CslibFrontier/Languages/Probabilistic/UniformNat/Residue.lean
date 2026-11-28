/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Vector
public import CslibFrontier.Languages.Probabilistic.UniformNat.ModIndex
public import CslibFrontier.Probability.StatisticalDistance.CloseTo
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Size
import Cslib.Probability.PMF
import CslibFrontier.Foundations.Data.ZMod.Basic
import CslibFrontier.Probability.StatisticalDistance.Product
import CslibFrontier.Probability.StatisticalDistance.TotalVariation

/-!
# Binary samples as canonical residues

`sampleBinaryNat w` reads `w` fair bits as a natural number below `2 ^ w`. These are exactly the
canonical representatives `ZMod.val` of the residues modulo `2 ^ w`, so the sampler draws the
canonical representative of a uniform residue. Repeating it lists the representatives of a uniform
residue vector, in coordinate order, and repeating those runs lists the rows of a uniform residue
matrix. Every count and the width may be zero; at width zero every sample is `0`, the only
representative modulo `1`.

For a positive modulus `q`, reducing each of `count` samples modulo `q` gives a vector
within statistical distance `count * (q / 2 ^ w)` of uniform.

## Main results

* `Cslib.ProbComp.eval_sampleBinaryNat_eq_map_val`: one sample is the representative of a uniform
  residue modulo `2 ^ w`.
* `Cslib.ProbComp.eval_replicate_sampleBinaryNat`: `count` samples list the representatives of a
  uniform residue vector.
* `Cslib.ProbComp.eval_replicate_replicate_sampleBinaryNat`: `rows` lists of `cols` samples list,
  row by row, the representatives of a uniform `rows × cols` residue matrix.
* `Cslib.ProbComp.dist_replicateFin_sampleModNat_le`,
  `Cslib.ProbComp.closeTo_replicate_sampleModIndex_precision`: approximating a uniform residue
  vector and its canonical representatives from a bounded fair-bit tape.
-/

public section

namespace Cslib.ProbComp

open Probability

/-- An unsigned `w`-bit sample is the canonical representative of a uniform residue modulo
`2 ^ w`. -/
theorem eval_sampleBinaryNat_eq_map_val (w : ℕ) :
    eval (sampleBinaryNat w) = (PMF.uniformOfFintype (ZMod (2 ^ w))).map ZMod.val := by
  rw [eval_sampleBinaryNat,
    ← PMF.uniformOfFintype_map_equiv (ZMod.finEquiv (2 ^ w)).toEquiv, PMF.map_comp]
  simp only [Function.comp_def, RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe, ZMod.val_finEquiv]

/-- `count` independent unsigned `w`-bit samples list the canonical representatives of a uniform
residue vector modulo `2 ^ w`. -/
theorem eval_replicate_sampleBinaryNat (count w : ℕ) :
    eval (OracleComp.replicate count (sampleBinaryNat w)) =
      (PMF.uniformOfFintype (Fin count → ZMod (2 ^ w))).map
        fun x => List.ofFn fun j => (x j).val :=
  eval_replicate_of_uniform count _ _ (eval_sampleBinaryNat_eq_map_val w)

/-- `rows` independent lists of `cols` unsigned `w`-bit samples list, row by row, the canonical
representatives of a uniform `rows × cols` residue matrix modulo `2 ^ w`. -/
theorem eval_replicate_replicate_sampleBinaryNat (rows cols w : ℕ) :
    eval (OracleComp.replicate rows (OracleComp.replicate cols (sampleBinaryNat w))) =
      (PMF.uniformOfFintype (_root_.Matrix (Fin rows) (Fin cols) (ZMod (2 ^ w)))).map
        fun A => List.ofFn fun i => List.ofFn fun j => (A i j).val :=
  eval_replicate_of_uniform rows _ _ (eval_replicate_sampleBinaryNat cols w)

/-- A bounded modular sample is already the canonical representative of its residue. -/
theorem eval_sampleModNat_eq_map_val (width q : ℕ) :
    eval (sampleModNat width q) =
      (eval ((Nat.cast : ℕ → ZMod q) <$> sampleModNat width q)).map ZMod.val := by
  rw [eval_map, eval_sampleModNat, PMF.map_comp, PMF.map_comp]
  congr 1 with i : 1
  simp only [Function.comp_apply, ZMod.val_natCast, Nat.mod_mod]

open scoped Cslib.Probability.PMF in
/-- Reducing independent binary samples modulo `q` approximates a uniform residue vector.
The statistical error is at most the sum of the one-coordinate errors. -/
theorem dist_replicateFin_sampleModNat_le (count width q : ℕ) [NeZero q] :
    dist (eval (OracleComp.replicateFin count ((Nat.cast : ℕ → ZMod q) <$> sampleModNat width q)))
      (PMF.uniformOfFintype (Fin count → ZMod q)) ≤ count * ((q : ℝ) / 2 ^ width) := by
  rw [eval_replicateFin, ← PMF.iid_eq_pi, ← PMF.iid_uniformOfFintype, eval_map]
  exact (PMF.dist_iid_le _ _ count).trans <|
    mul_le_mul_of_nonneg_left (dist_map_natCast_eval_sampleModNat_le width q) (Nat.cast_nonneg _)

open scoped ENNReal in
/-- The list of unary residues produced by independent bounded samplers approximates the
canonical representatives of a uniform vector, with error at most `count * q / 2 ^ width` on
every event. -/
theorem closeTo_replicate_sampleModIndex (count width q : ℕ) [NeZero q] :
    CloseTo ((PMF.uniformOfFintype (Fin count → ZMod q)).map
      (fun v => List.ofFn fun j => (v j).val))
      (eval (OracleComp.replicate count (sampleModIndex width q))) (count * q / 2 ^ width) := by
  rw [sampleModIndex_eq_sampleModNat width (NeZero.pos q),
    eval_replicateFin_map (eval_sampleModNat_eq_map_val width q)]
  have h := (closeTo_of_dist_le_ofReal (dist_replicateFin_sampleModNat_le count width q)).symm
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg count), ENNReal.ofReal_natCast,
    ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast] at h
  simpa only [ENNReal.ofReal_pow (by norm_num : 0 ≤ (2 : ℝ)), ENNReal.ofReal_ofNat,
    mul_div_assoc] using h.map (fun v => List.ofFn fun j => (v j).val)

/-- Every supported list of modular samples consists of the canonical representatives of a residue
vector of the requested dimension. -/
theorem exists_vector_of_mem_support_replicate_sampleModIndex {count width q : ℕ} [NeZero q]
    {xs : List ℕ} (hx : xs ∈ (eval (OracleComp.replicate count (sampleModIndex width q))).support) :
    ∃ v : Fin count → ZMod q, xs = List.ofFn fun j => (v j).val := by
  rw [sampleModIndex_eq_sampleModNat _ (NeZero.pos q),
    eval_replicateFin_map (eval_sampleModNat_eq_map_val width q),
    _root_.PMF.mem_support_map_iff] at hx
  obtain ⟨v, _, hv⟩ := hx
  exact ⟨v, hv.symm⟩

open scoped ENNReal in
/-- Using the bit lengths of the count and modulus plus `precision` bits per sample gives
statistical error at most `2 ^ (-precision)` for the whole list. -/
theorem closeTo_replicate_sampleModIndex_precision (count q precision : ℕ) [NeZero q] :
    CloseTo ((PMF.uniformOfFintype (Fin count → ZMod q)).map
      (fun v => List.ofFn fun j => (v j).val))
      (eval (OracleComp.replicate count (sampleModIndex (count.size + q.size + precision) q)))
      (1 / 2 ^ precision) := by
  refine (closeTo_replicate_sampleModIndex count _ q).mono ?_
  have h : (count : ℝ≥0∞) * q ≤ 2 ^ (count.size + q.size) := by
    rw [pow_add]
    exact mul_le_mul' (by exact_mod_cast (Nat.lt_size_self count).le)
      (by exact_mod_cast (Nat.lt_size_self q).le)
  rw [pow_add (2 : ℝ≥0∞) (count.size + q.size), mul_comm (2 ^ (count.size + q.size))]
  calc
    _ ≤ 1 * 2 ^ (count.size + q.size) / (2 ^ precision * 2 ^ (count.size + q.size)) := by
      rw [one_mul]
      exact ENNReal.div_le_div_right h _
    _ = _ := ENNReal.mul_div_mul_right _ _ (by positivity) (by finiteness)

end Cslib.ProbComp
