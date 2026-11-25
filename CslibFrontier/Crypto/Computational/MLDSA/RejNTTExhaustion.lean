/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.ExpandAProgramming
import CslibFrontier.Probability.Product.Event
import CslibFrontier.Probability.PMF.Union
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.List.OfFn

/-!
# Exhaustion of the matrix rejection sampler

[FIPS 204][NISTFIPS204], Appendix C, Table 3 allows 894 bytes for each invocation of
Algorithm 30. An exhausted stream contains at least 43 rejected triples. Each such triple
has its middle byte at least 224 and the low seven bits of its last byte all set.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204

open Cslib.Probability Finset

private abbrev Triple := Fin 3 → Byte

private def rejects (b : Triple) := 8380417 ≤ nttCandidate (b 0) (b 1) (b 2)

private instance (b : Triple) : Decidable (rejects b) := inferInstanceAs (Decidable (_ ≤ _))

private def tripleBytes (b : Triple) : List Byte := [b 0, b 1, b 2]

private theorem count_accepted {n : ℕ} (b : Fin n → Triple) :
    (rejNTTCoefficients ((List.ofFn (fun i => tripleBytes (b i))).flatten)).length +
        ∑ i, (if rejects (b i) then 1 else 0) = n := by
  induction n with
  | zero => simp [rejNTTCoefficients]
  | succ n ih =>
    have ht := ih (fun i => b i.succ)
    rw [List.ofFn_succ, List.flatten_cons, Fin.sum_univ_succ]
    by_cases h : rejects (b 0)
    · simp only [tripleBytes, List.cons_append, List.nil_append, rejNTTCoefficients,
        Nat.not_lt.mpr h, h, ite_false, ite_true] at ht ⊢; omega
    · simp only [tripleBytes, List.cons_append, List.nil_append, rejNTTCoefficients,
        Nat.lt_of_not_ge h, h, ite_false, ite_true, List.length_cons] at ht ⊢; omega

private def groupBytes (n : ℕ) : FixedBytes (n * 3) ≃ (Fin n → Triple) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Byte)).trans (Equiv.curry _ _ _)

private theorem flatten_groupBytes {n : ℕ} (t : FixedBytes (n * 3)) :
    (List.ofFn (fun i => tripleBytes (groupBytes n t i))).flatten = List.ofFn t := by
  rw [List.ofFn_mul t]
  refine congrArg List.flatten (congrArg List.ofFn (funext fun i => ?_))
  have hj (j : Fin 3) : groupBytes n t i j =
      t ⟨i.val * 3 + j.val, by have := i.isLt; have := j.isLt; omega⟩ := by
    change t ⟨j.val + 3 * i.val, _⟩ = _
    exact congrArg t (Fin.ext (by dsimp only; omega))
  simp [tripleBytes, List.ofFn_succ, hj]

private def tailBytes (j : Fin 3) : Finset Byte :=
  if j = 1 then Icc 224 255 else if j = 2 then {127, 255} else univ

private theorem rejects_mem {b : Triple} (hb : rejects b) (j : Fin 3) :
    b j ∈ tailBytes j := by
  have ha : (b 0).val < 256 := (b 0).isLt
  have hmid : (b 1).val < 256 := (b 1).isLt
  have hc : (b 2).val < 256 := (b 2).isLt
  change 8380417 ≤ (b 0).val + 256 * (b 1).val + 65536 * ((b 2).val % 128) at hb
  fin_cases j
  · simp [tailBytes]
  · change b 1 ∈ Icc (224 : Byte) 255
    rw [mem_Icc]; change 224 ≤ (b 1).val ∧ (b 1).val ≤ 255; omega
  · change b 2 ∈ ({127, 255} : Finset Byte)
    simp only [mem_insert, mem_singleton, Fin.ext_iff]
    change (b 2).val = 127 ∨ (b 2).val = 255; omega

private def allowed : Finset Triple := Fintype.piFinset tailBytes

private theorem card_allowed : allowed.card = 16384 := by
  rw [allowed, Fintype.card_piFinset, Fin.prod_univ_three]
  norm_num [tailBytes, Fin.card_Icc, Byte, Fin.val_natCast]

private def atPositions {n : ℕ} (J : Finset (Fin n)) : Set (Fin n → Triple) :=
  {b | ∀ i, b i ∈ (if i ∈ J then (allowed : Set Triple) else Set.univ)}

private theorem prob_atPositions {n : ℕ} (J : Finset (Fin n)) :
    ((PMF.uniformOfFintype (Fin n → Triple)).toOuterMeasure (atPositions J)).toReal =
      (1 / 1024 : ℝ) ^ J.card := by
  classical
  have oneTriple : ((PMF.uniformOfFintype Triple).toOuterMeasure
      (allowed : Set Triple)).toReal = 1 / 1024 := by
    have ht : Fintype.card Triple = 16777216 := by simp [Fintype.card_pi, Byte]
    rw [PMF.toOuterMeasure_uniformOfFintype_toReal]
    simp only [mem_coe, filter_mem_eq_inter, univ_inter, card_allowed, ht]
    norm_num
  rw [← PMF.pi_uniformOfFintype, atPositions, PMF.toOuterMeasure_pi_forall, ENNReal.toReal_prod]
  have hall := ((PMF.uniformOfFintype Triple).toOuterMeasure_apply_eq_one_iff Set.univ).2
    (Set.subset_univ _)
  simp only [apply_ite, oneTriple, hall, ENNReal.toReal_one,
    Fintype.prod_ite_mem, prod_const]

private theorem covers_exhaustion (b : Fin 298 → Triple)
    (h : rejNTTPoly (List.ofFn ((groupBytes 298).symm b)) = none) :
    b ∈ ⋃ J ∈ (univ : Finset (Fin 298)).powersetCard 43, atPositions J := by
  have hlt := (rejNTTPoly_eq_none_iff _).mp h
  rw [← flatten_groupBytes ((groupBytes 298).symm b), Equiv.apply_symm_apply] at hlt
  have hc := count_accepted b
  rw [Finset.sum_boole, Nat.cast_id] at hc
  obtain ⟨J, hJ, hcard⟩ := exists_subset_card_eq
    (show 43 ≤ (univ.filter fun i => rejects (b i)).card by omega)
  refine Set.mem_iUnion₂.mpr ⟨J, mem_powersetCard.mpr ⟨subset_univ _, hcard⟩, fun i => ?_⟩
  by_cases hi : i ∈ J
  · simpa [hi, allowed, Fintype.mem_piFinset] using rejects_mem (mem_filter.mp (hJ hi)).2
  · simp [hi]

/-- With 894 uniformly sampled bytes, FIPS 204 Algorithm 30 exhausts with probability below
2⁻²⁵⁶. The union counts the possible locations of 43 rejections among 298 three-byte proposals. -/
theorem prob_rejNTTPoly_exhaustion :
    ((PMF.uniformOfFintype (FixedBytes 894)).toOuterMeasure
      {t | rejNTTPoly (List.ofFn t) = none}).toReal < 1 / (2 : ℝ) ^ 256 := by
  let P := PMF.uniformOfFintype (Fin 298 → Triple)
  let J := (univ : Finset (Fin 298)).powersetCard 43
  rw [← PMF.uniformOfFintype_map_equiv (groupBytes 298).symm, PMF.toOuterMeasure_map_apply]
  refine (PMF.toOuterMeasure_toReal_mono P fun b => covers_exhaustion b).trans_lt
    ((PMF.toOuterMeasure_toReal_biUnion_finset_le P J atPositions).trans_lt ?_)
  rw [sum_congr rfl fun j hj => by rw [prob_atPositions, (mem_powersetCard.mp hj).2],
    sum_const, nsmul_eq_mul]
  have hc : J.card < 2 ^ 174 := by
    rw [show J.card = Nat.choose 298 43 by simp [J], Nat.choose_eq_descFactorial_div_factorial]
    decide +kernel
  exact (mul_lt_mul_of_pos_right (Nat.cast_lt.mpr hc) (by positivity)).trans_eq (by norm_num)

private theorem isSome_ofFnM {n : ℕ} {α : Type*} (f : Fin n → Option α)
    (h : ∀ i, (f i).isSome) : (Vector.ofFnM f).isSome := by
  have hf : f = fun i => (pure ((f i).get (h i)) : Option α) :=
    funext fun i => (Option.some_get (h i)).symm
  rw [hf, Vector.ofFnM_pure]; rfl

private theorem expandA_exhausts_at_cell (H : Xofs) (s : Level) (rho : List Byte)
    (t : MatrixPrefixes s) (h : (H.withMatrixPrefixes s rho t).expandA s rho = none) :
    ∃ (i : Fin s.params.k) (j : Fin s.params.ℓ), rejNTTPoly (List.ofFn (t i j)) = none := by
  by_contra! cells
  let entry (i : Fin s.params.k) (j : Fin s.params.ℓ) :=
    (rejNTTPoly (List.ofFn (t i j))).map fromNTT
  have ok := isSome_ofFnM (fun i => Vector.ofFnM (entry i)) fun i => isSome_ofFnM (entry i)
    fun j => by simpa only [entry, Option.isSome_map, Option.isSome_iff_ne_none] using cells i j
  have : ((H.withMatrixPrefixes s rho t).expandA s rho).isSome := by
    simp only [Xofs.expandA, read_matrixEntry, bind_pure_comp]
    change (Option.map (fun v i j => ((v.get i).get j).get)
      (Vector.ofFnM fun i => Vector.ofFnM (entry i))).isSome
    rwa [Option.isSome_map]
  simp [h] at this

/-- At a fixed public seed with independent uniform raw SHAKE128 prefixes, the probability
that FIPS 204 Algorithm 32 exhausts at any entry is below the number of entries times 2⁻²⁵⁶. -/
theorem prob_expandA_exhaustion (H : Xofs) (s : Level) (rho : List Byte) :
    ((PMF.uniformOfFintype (MatrixPrefixes s)).toOuterMeasure
      {t | (H.withMatrixPrefixes s rho t).expandA s rho = none}).toReal <
      (s.params.k * s.params.ℓ : ℕ) / (2 : ℝ) ^ 256 := by
  classical
  let P := PMF.uniformOfFintype (MatrixPrefixes s)
  let J := (univ : Finset (Fin s.params.k × Fin s.params.ℓ))
  let bad (p : Fin s.params.k × Fin s.params.ℓ) : Set (MatrixPrefixes s) :=
    {t | rejNTTPoly (List.ofFn (t p.1 p.2)) = none}
  refine (PMF.toOuterMeasure_toReal_mono P (t := ⋃ p ∈ J, bad p) fun t ht => ?_).trans_lt
    ((PMF.toOuterMeasure_toReal_biUnion_finset_le P J bad).trans_lt ?_)
  · obtain ⟨i, j, hij⟩ := expandA_exhausts_at_cell H s rho t ht
    exact Set.mem_iUnion₂.mpr ⟨(i, j), mem_univ _, hij⟩
  · have hne : J.Nonempty := ⟨(⟨0, by cases s <;> decide⟩, ⟨0, by cases s <;> decide⟩), mem_univ _⟩
    refine (sum_lt_sum_of_nonempty (g := fun _ => 1 / (2 : ℝ) ^ 256) hne fun p _ => ?_).trans_eq
      (by simp [J, div_eq_mul_inv])
    have hproj : P.map (fun t => t p.1 p.2) = PMF.uniformOfFintype (FixedBytes 894) := by
      change P.map ((fun row => row p.2) ∘ (fun t => t p.1)) = _
      rw [← PMF.map_comp, show P = _ from PMF.pi_uniformOfFintype.symm, PMF.pi_map_eval,
        ← PMF.pi_uniformOfFintype, PMF.pi_map_eval]
    have hb := prob_rejNTTPoly_exhaustion
    rwa [← hproj, PMF.toOuterMeasure_map_apply] at hb

end Cslib.Crypto.MLDSA.FIPS204
