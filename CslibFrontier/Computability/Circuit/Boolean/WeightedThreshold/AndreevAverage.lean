/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.WeightedThreshold.AndreevWindowed
public import CslibFrontier.Foundations.Data.BitString.Weight

/-!
# Average-case depth-two weighted threshold circuit upper bounds for Andreev's function

This module proves the average-case agreement bounds for the windowed depth-two weighted threshold
circuit `andreevWindowedCircuit b m r B` [Andreev1987]:

1. **Subcube Fourier projection (`andreevSubcubeScore_eq_two_pow_mul_sum`,
   `andreevSubcubeEval_eq_decide`):**
   Summing `X_S(w) * χ_S(andreevParities b m w)` over `S ∈ andreevPrefixSubsets b r` projects onto
   the subcube `andreevSubcube b r (andreevParities b m w)` of size `2 ^ (b - r)` (`r ≤ b`), so
   `andreevSubcubeEval b m r w` is the majority vote on that subcube.
2. **Exact subcube majority correlation (`two_mul_card_andreevSubcubeEval_eq_andreev`) and central
   binomial lower bound (`pow_two_mul_sub_one_sq_le`):**
   For `r < b`, conjugating by the measure-preserving shift involution `andreevShiftTable b m`
   reduces `andreev b m` to a single coordinate `i₀` and `andreevSubcubeEval b m r` to the majority
   vote over `insert i₀ R` (`#R = 2 ^ (b - r) - 1`), yielding the exact agreement count and
   `(2 ^ (2 * K - 1)) ^ 2 ≤ 4 * K * ((2 * K - 1).choose (K - 1)) ^ 2` for `K = 2 ^ (b - r - 1)`.
   Together they give the vote's agreement `1 / 2 + 1 / (2 √(2 L))` for `L = 2 ^ (b - r)`
   (`two_pow_mul_le_card_andreevSubcubeEval_eq_andreev`).
3. **Hoeffding window union bound and average-case circuit upper bounds
   (`card_not_andreevInWindow_le`, `card_eval_andreevWindowedCircuit_self_ne_le`,
   `card_eval_andreevWindowedCircuit_eq_andreev_ge`,
   `card_eval_andreevWindowedCircuit_eq_andreev_ge_sqrt`):**
   Combining the Hoeffding tail bounds for `andreevTableScore` and `andreevBlockSum` over
   `S ∈ andreevPrefixSubsets b r` yields both the `(1 - δ)`-agreement depth-two threshold circuit
   upper bound at `r = b` and the `(1 / 2 + ε)`-correlation upper bound for `r < b`.

## References

* [A. E. Andreev, *On a method for obtaining more than quadratic effective lower bounds for the
  complexity of π-schemes*][Andreev1987]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.WeightedThreshold

open BitString Finset Real

/-! ### Subcube Fourier projection -/

/-- The subcube of truth-table indices `c : BitString b` agreeing with `p : BitString b` on the
first `r` coordinates (`andreevPrefixCoords b r`). -/
def andreevSubcube (b r : ℕ) (p : BitString b) : Finset (BitString b) :=
  univ.filter fun c : BitString b => ∀ j ∈ andreevPrefixCoords b r, c j = p j

@[simp]
theorem mem_andreevSubcube {b r : ℕ} {p c : BitString b} :
    c ∈ andreevSubcube b r p ↔ ∀ j ∈ andreevPrefixCoords b r, c j = p j := by simp [andreevSubcube]

theorem self_mem_andreevSubcube (b r : ℕ) (p : BitString b) :
    p ∈ andreevSubcube b r p := by simp

/-- Embedding `BitString (b - r)` into `BitString b` by fixing the first `r` coordinates to `p`. -/
private def andreevSubcubeEmbedding {b r : ℕ} (hr : r ≤ b) (p : BitString b) :
    BitString (b - r) ↪ BitString b where
  toFun z j := if h : j.val < r then p j else z ⟨j.val - r, by omega⟩
  inj' z₁ z₂ h := by
    funext k; have hk := congrFun h ⟨r + k.val, by omega⟩
    simpa [show ¬ (r + k.val < r) by omega] using hk

private theorem andreevSubcubeEmbedding_apply {b r : ℕ} (hr : r ≤ b) (p : BitString b)
    (z : BitString (b - r)) (j : Fin b) :
    andreevSubcubeEmbedding hr p z j = if h : j.val < r then p j else z ⟨j.val - r, by omega⟩ := rfl

/-- When `r ≤ b`, `andreevSubcube b r p` has cardinality `2 ^ (b - r)`. -/
theorem card_andreevSubcube {b r : ℕ} (hr : r ≤ b) (p : BitString b) :
    #(andreevSubcube b r p) = 2 ^ (b - r) := by
  have hmap : andreevSubcube b r p =
      (univ : Finset (BitString (b - r))).map (andreevSubcubeEmbedding hr p) := by
    ext c; simp only [mem_andreevSubcube, mem_andreevPrefixCoords, mem_map, mem_univ, true_and]
    refine ⟨fun hc => ⟨fun k => c ⟨r + k.val, by omega⟩, ?_⟩, ?_⟩
    · funext j; rw [andreevSubcubeEmbedding_apply]; split_ifs with hj
      · exact (hc j hj).symm
      · congr 1; ext; dsimp; omega
    · rintro ⟨z, rfl⟩ j hj; rw [andreevSubcubeEmbedding_apply]; simp [hj]
  rw [hmap, card_map, card_univ, BitString.card]

/-- Summing `chi ℤ S c * chi ℤ S p` over `S ∈ andreevPrefixSubsets b r` detects membership in
`andreevSubcube b r p`. -/
theorem sum_chi_mul_chi_prefixSubsets (b r : ℕ) (c p : BitString b) :
    ∑ S ∈ andreevPrefixSubsets b r, chi ℤ S c * chi ℤ S p =
      if c ∈ andreevSubcube b r p then (2 : ℤ) ^ #(andreevPrefixCoords b r) else 0 := by
  simpa [andreevPrefixSubsets, mem_andreevSubcube] using
    sum_powerset_chi_mul_chi (R := ℤ) (andreevPrefixCoords b r) c p

/-- **Subcube Fourier projection**: `andreevSubcubeScore b m r w` equals
`2 ^ #(andreevPrefixCoords b r)` times the sum of `1 - 2 * x_c(w)` over
`c ∈ andreevSubcube b r (andreevParities b m w)`. -/
theorem andreevSubcubeScore_eq_two_pow_mul_sum (b m r : ℕ) (w : BitString (2 ^ b + b * m)) :
    andreevSubcubeScore b m r w =
      (2 : ℤ) ^ #(andreevPrefixCoords b r) *
        ∑ c ∈ andreevSubcube b r (andreevParities b m w),
          (1 - 2 * ((andreevTable b m w c).toNat : ℤ)) := by
  unfold andreevSubcubeScore andreevTableScore; simp_rw [sum_mul]; rw [sum_comm]
  calc ∑ c : BitString b, ∑ S ∈ andreevPrefixSubsets b r,
        chi ℤ S c * (1 - 2 * ((andreevTable b m w c).toNat : ℤ)) *
          chi ℤ S (andreevParities b m w)
      = ∑ c : BitString b,
          (∑ S ∈ andreevPrefixSubsets b r, chi ℤ S c * chi ℤ S (andreevParities b m w)) *
            (1 - 2 * ((andreevTable b m w c).toNat : ℤ)) :=
        sum_congr rfl fun c _ => by
          rw [sum_mul]
          exact sum_congr rfl fun S _ => by ring
    _ = (2 : ℤ) ^ #(andreevPrefixCoords b r) *
          ∑ c ∈ andreevSubcube b r (andreevParities b m w),
            (1 - 2 * ((andreevTable b m w c).toNat : ℤ)) := by
        simp_rw [sum_chi_mul_chi_prefixSubsets, ite_mul, zero_mul, ← sum_filter,
          filter_mem_eq_inter, univ_inter, mul_sum]

/-- `andreevSubcubeEval b m r w` is the majority predicate on
`andreevSubcube b r (andreevParities b m w)`. -/
theorem andreevSubcubeEval_eq_decide (b m r : ℕ) (w : BitString (2 ^ b + b * m)) :
    andreevSubcubeEval b m r w =
      decide ((∑ c ∈ andreevSubcube b r (andreevParities b m w),
        (1 - 2 * ((andreevTable b m w c).toNat : ℤ))) ≤ 0) := by
  rw [andreevSubcubeEval, andreevSubcubeScore_eq_two_pow_mul_sum]
  have hpos : (0 : ℤ) < (2 : ℤ) ^ #(andreevPrefixCoords b r) := by positivity
  exact decide_eq_decide.mpr
    ⟨fun h => nonpos_of_mul_nonpos_right h hpos, fun h => mul_nonpos_of_nonneg_of_nonpos hpos.le h⟩

/-! ### Combinatorial subcube majority correlation and central binomial lower bound -/

/-- For any subset `R : Finset ι` on a finite type `ι` and any `k : ℕ`, the number of Boolean
vectors `w : ι → Bool` with `#{i ∈ R | w i = true} = k` is
`2 ^ (Fintype.card ι - #R) * (#R).choose k`. -/
theorem card_filter_card_filter_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Finset ι) (k : ℕ) :
    #{w : ι → Bool | #{i ∈ R | w i = true} = k} =
      2 ^ (Fintype.card ι - #R) * (#R).choose k := by
  let e := Equiv.piEquivPiSubtypeProd (· ∈ R) (fun _ => Bool)
  have hwt (w : ι → Bool) : #{i ∈ R | w i = true} = weight (e w).1 := by
    rw [weight, card_filter, card_filter,
      ← Finset.sum_coe_sort R (fun i => if w i = true then 1 else 0)]; rfl
  have hbij : #{w : ι → Bool | #{i ∈ R | w i = true} = k} =
      #(({u : {i // i ∈ R} → Bool | weight u = k} : Finset _) ×ˢ
        (univ : Finset ({i // i ∉ R} → Bool))) :=
    card_equiv e fun w => by simp [hwt]
  rw [hbij, card_product, card_filter_weight_eq, card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_coe, Fintype.card_subtype_compl, Fintype.card_coe, mul_comm]

/-- For any subset `R : Finset ι`, coordinate `i₀ ∉ R`, and threshold `K ≥ 1`, pairing each
`w : ι → Bool` with `Function.update w i₀ (!w i₀)` proves
`2 * #{w | decide (K ≤ (w i₀).toNat + #{i ∈ R | w i = true}) = w i₀} =
  2 ^ |ι| + 2 ^ (|ι| - #R) * (#R).choose (K - 1)`. -/
theorem two_mul_card_filter_decide_le_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Finset ι) {i₀ : ι} (hi₀ : i₀ ∉ R) {K : ℕ} (hK : 1 ≤ K) :
    2 * #{w : ι → Bool | decide (K ≤ (w i₀).toNat + #{i ∈ R | w i = true}) = w i₀} =
      2 ^ Fintype.card ι + 2 ^ (Fintype.card ι - #R) * (#R).choose (K - 1) := by
  let flip : Equiv.Perm (ι → Bool) :=
    { toFun := fun w => Function.update w i₀ (!w i₀)
      invFun := fun w => Function.update w i₀ (!w i₀)
      left_inv := fun w => by funext i; by_cases h : i = i₀ <;> simp [h]
      right_inv := fun w => by funext i; by_cases h : i = i₀ <;> simp [h] }
  have hR_flip (w : ι → Bool) : #{i ∈ R | flip w i = true} = #{i ∈ R | w i = true} := by
    congr 1; ext i; simp only [mem_filter, and_congr_right_iff]; intro hi
    simp [flip, show i ≠ i₀ from fun h => hi₀ (h ▸ hi)]
  let P : (ι → Bool) → Prop := fun w =>
    decide (K ≤ (w i₀).toNat + #{i ∈ R | w i = true}) = w i₀
  have hpair (w : ι → Bool) :
      (if P w then 1 else 0) + (if P (flip w) then 1 else 0) =
        1 + (if #{i ∈ R | w i = true} = K - 1 then 1 else 0) := by
    dsimp only [P]; rw [hR_flip, show flip w i₀ = !w i₀ by simp [flip]]
    set s := #{i ∈ R | w i = true}
    cases hw : w i₀ <;>
      simp only [Bool.toNat_false, Bool.toNat_true, zero_add, Bool.not_false, Bool.not_true,
        decide_eq_true_eq, decide_eq_false_iff_not, not_le] <;>
      split_ifs <;> omega
  have hsum :
      (∑ w : ι → Bool, ((if P w then 1 else 0) + (if P (flip w) then 1 else 0))) =
        ∑ w : ι → Bool, (1 + (if #{i ∈ R | w i = true} = K - 1 then 1 else 0)) :=
    sum_congr rfl fun w _ => hpair w
  rw [sum_add_distrib, Equiv.sum_comp flip (fun w => if P w then 1 else 0), ← two_mul,
    ← card_filter, sum_add_distrib, sum_const, card_univ, Fintype.card_fun, Fintype.card_bool,
    smul_eq_mul, mul_one, ← card_filter, card_filter_card_filter_eq] at hsum
  exact hsum

/-- Recurrence `(K + 1) * (2 * K + 1).choose K = 2 * (2 * K + 1) * (2 * K - 1).choose (K - 1)`
for `1 ≤ K`. -/
private theorem succ_mul_choose_two_mul_add_one {K : ℕ} (hK : 1 ≤ K) :
    (K + 1) * (2 * K + 1).choose K = 2 * (2 * K + 1) * (2 * K - 1).choose (K - 1) := by
  have h1 := Nat.add_one_mul_choose_eq (2 * K - 1) (K - 1)
  rw [Nat.sub_add_cancel hK, Nat.sub_add_cancel (by omega : 1 ≤ 2 * K)] at h1
  have h2 : (2 * K).choose K = 2 * (2 * K - 1).choose (K - 1) := by nlinarith
  rw [mul_comm, ← Nat.choose_symm_of_eq_add (by omega : 2 * K + 1 = K + 1 + K),
    ← Nat.add_one_mul_choose_eq (2 * K) K, h2]
  ring

/-- **Central binomial lower bound**: for all `K ≥ 1`,
`(2 ^ (2 * K - 1)) ^ 2 ≤ 4 * K * ((2 * K - 1).choose (K - 1)) ^ 2`. -/
theorem pow_two_mul_sub_one_sq_le {K : ℕ} (hK : 1 ≤ K) :
    (2 ^ (2 * K - 1)) ^ 2 ≤ 4 * K * ((2 * K - 1).choose (K - 1)) ^ 2 := by
  induction K, hK using Nat.le_induction with
  | base => decide
  | succ K hK ih =>
    have hrec := succ_mul_choose_two_mul_add_one hK
    rw [show 2 * (K + 1) - 1 = (2 * K - 1) + 2 by omega, pow_add]
    set C' := ((2 * K - 1) + 2).choose (K + 1 - 1)
    have hrec' : (K + 1) * C' = 2 * (2 * K + 1) * (2 * K - 1).choose (K - 1) := by
      simpa [C', show (2 * K - 1) + 2 = 2 * K + 1 by omega] using hrec
    refine Nat.le_of_mul_le_mul_left (c := (K + 1) ^ 2) ?_ (by positivity)
    calc (K + 1) ^ 2 * (2 ^ (2 * K - 1) * 2 ^ 2) ^ 2
        = 16 * (K + 1) ^ 2 * (2 ^ (2 * K - 1)) ^ 2 := by ring
      _ ≤ 16 * (K + 1) ^ 2 * (4 * K * ((2 * K - 1).choose (K - 1)) ^ 2) :=
          Nat.mul_le_mul_left _ ih
      _ ≤ 4 * (K + 1) * (2 * (2 * K + 1) * (2 * K - 1).choose (K - 1)) ^ 2 := by nlinarith
      _ = (K + 1) ^ 2 * (4 * (K + 1) * C' ^ 2) := by rw [← hrec']; ring

/-! ### Exact correlation of `andreevSubcubeEval` with `andreev` -/

/-- Underlying map of `andreevShiftTable b m`: shifts each truth-table index `c : BitString b` by
`andreevParities b m w` (coordinatewise XOR) and leaves all block bits unchanged. -/
def andreevShiftTableFun (b m : ℕ) (w : BitString (2 ^ b + b * m)) : BitString (2 ^ b + b * m) :=
  andreevTranslateTableFun b m (andreevParities b m w) false w

@[simp]
theorem andreevShiftTableFun_tableIndex (b m : ℕ) (w : BitString (2 ^ b + b * m))
    (idx : Fin (2 ^ b)) :
    andreevShiftTableFun b m w (andreevTableIndex b m idx) = w (andreevTableIndex b m
      (BitString.equivFin b ((BitString.equivFin b).symm idx + andreevParities b m w))) := by
  simp [andreevShiftTableFun, andreevTableIndex]

/-- At addresses, `andreevShiftTableFun b m w` reads the table of `w` shifted by its block
parities. -/
theorem andreevTable_shiftTableFun (b m : ℕ) (w : BitString (2 ^ b + b * m)) (c : BitString b) :
    andreevTable b m (andreevShiftTableFun b m w) c =
      andreevTable b m w (c + andreevParities b m w) := by
  rw [andreevTable, andreevShiftTableFun_tableIndex, Equiv.symm_apply_apply]
  rfl

@[simp]
theorem andreevParities_shiftTableFun (b m : ℕ) (w : BitString (2 ^ b + b * m)) :
    andreevParities b m (andreevShiftTableFun b m w) = andreevParities b m w := by
  funext j; simp [andreevShiftTableFun, andreevParities, andreevBlockVar]

theorem andreevShiftTableFun_involutive (b m : ℕ) :
    Function.Involutive (andreevShiftTableFun b m) := fun w => by
  funext i; refine Fin.addCases (fun idx => ?_) (fun u => by simp [andreevShiftTableFun]) i
  change andreevShiftTableFun b m (andreevShiftTableFun b m w) (andreevTableIndex b m idx) =
    w (andreevTableIndex b m idx)
  rw [andreevShiftTableFun_tableIndex, andreevParities_shiftTableFun,
    andreevShiftTableFun_tableIndex, Equiv.symm_apply_apply,
    show (BitString.equivFin b).symm idx + andreevParities b m w + andreevParities b m w =
      (BitString.equivFin b).symm idx by funext j; simp [Bool.add_eq_xor],
    Equiv.apply_symm_apply]

/-- Measure-preserving involution on `BitString (2 ^ b + b * m)` shifting each truth-table index
`c : BitString b` by `andreevParities b m w` (coordinatewise XOR) and leaving all block bits
unchanged. -/
def andreevShiftTable (b m : ℕ) : Equiv.Perm (BitString (2 ^ b + b * m)) :=
  (andreevShiftTableFun_involutive b m).toPerm

@[simp]
theorem andreevShiftTable_apply (b m : ℕ) (w : BitString (2 ^ b + b * m)) :
    andreevShiftTable b m w = andreevShiftTableFun b m w := rfl

/-- The truth-table coordinate `i₀` corresponding to `0 : BitString b`. -/
private def andreevZeroTableCoord (b m : ℕ) : Fin (2 ^ b + b * m) :=
  andreevTableIndex b m (BitString.equivFin b 0)

/-- The punctured subcube support `(andreevSubcube b r 0).erase 0` mapped into truth-table
coordinates in `Fin (2 ^ b + b * m)`. -/
private def andreevZeroPuncturedSupport (b m r : ℕ) : Finset (Fin (2 ^ b + b * m)) :=
  ((andreevSubcube b r 0).erase 0).map ⟨fun c => andreevTableIndex b m (BitString.equivFin b c),
    (andreevTableIndex_injective b m).comp (BitString.equivFin b).injective⟩

private theorem andreevZeroTableCoord_notMem_puncturedSupport (b m r : ℕ) :
    andreevZeroTableCoord b m ∉ andreevZeroPuncturedSupport b m r := by
  simp [andreevZeroTableCoord, andreevZeroPuncturedSupport]

private theorem card_andreevZeroPuncturedSupport {b r : ℕ} (hr : r ≤ b) (m : ℕ) :
    #(andreevZeroPuncturedSupport b m r) = 2 ^ (b - r) - 1 := by
  rw [andreevZeroPuncturedSupport, card_map, card_erase_of_mem (self_mem_andreevSubcube b r 0),
    card_andreevSubcube hr]

/-- Under `andreevShiftTable b m`, `andreev b m` evaluates to `w (andreevZeroTableCoord b m)`. -/
private theorem andreev_shiftTable (b m : ℕ) (w : BitString (2 ^ b + b * m)) :
    andreev b m (andreevShiftTable b m w) = w (andreevZeroTableCoord b m) := by
  rw [andreev_eq_table_parities, andreevShiftTable_apply, andreevParities_shiftTableFun,
    andreevTable_shiftTableFun,
    show andreevParities b m w + andreevParities b m w = (0 : BitString b) by
      funext j; simp [Bool.add_eq_xor, Bool.zero_eq_false]]
  rfl

/-- Under `andreevShiftTable b m`, `andreevSubcubeEval b m r` for `r < b` reduces to the majority
vote over `insert (andreevZeroTableCoord b m) (andreevZeroPuncturedSupport b m r)`. -/
private theorem andreevSubcubeEval_shiftTable {b r : ℕ} (hr : r < b) (m : ℕ)
    (w : BitString (2 ^ b + b * m)) :
    andreevSubcubeEval b m r (andreevShiftTable b m w) =
      decide (2 ^ (b - r - 1) ≤ (w (andreevZeroTableCoord b m)).toNat +
        #{i ∈ andreevZeroPuncturedSupport b m r | w i = true}) := by
  rw [andreevSubcubeEval_eq_decide, andreevShiftTable_apply, andreevParities_shiftTableFun]
  let p := andreevParities b m w
  have hcancel (c : BitString b) : c + p + p = c := funext fun j => by simp [Bool.add_eq_xor]
  have hmap : andreevSubcube b r p =
      (andreevSubcube b r 0).map ⟨fun c => c + p, add_left_injective p⟩ := by
    ext c
    simp only [mem_andreevSubcube, mem_map, Function.Embedding.coeFn_mk]
    exact ⟨fun hc => ⟨c + p, fun j hj => by simp [Bool.add_eq_xor, Bool.zero_eq_false, hc j hj],
        hcancel c⟩,
      fun ⟨d, hd, hdp⟩ j hj => hdp ▸ by simp [Bool.add_eq_xor, Bool.zero_eq_false, hd j hj]⟩
  have hones : (∑ c ∈ (andreevSubcube b r 0).erase 0, ((andreevTable b m w c).toNat : ℤ)) =
      (#{i ∈ andreevZeroPuncturedSupport b m r | w i = true} : ℤ) := by
    rw [andreevZeroPuncturedSupport, card_filter, sum_map, Nat.cast_sum]
    refine sum_congr rfl fun c _ => ?_
    simp only [Function.Embedding.coeFn_mk, andreevTable]
    cases w (andreevTableIndex b m (BitString.equivFin b c)) <;> simp
  rw [hmap, sum_map, sum_congr rfl fun c _ => by
      simp only [Function.Embedding.coeFn_mk, andreevTable_shiftTableFun]
      rw [hcancel],
    ← add_sum_erase _ _ (self_mem_andreevSubcube b r 0), sum_sub_distrib, ← mul_sum, sum_const,
    card_erase_of_mem (self_mem_andreevSubcube b r 0), card_andreevSubcube hr.le, nsmul_one,
    Nat.cast_sub Nat.one_le_two_pow, Nat.cast_one, hones,
    show andreevTable b m w 0 = w (andreevZeroTableCoord b m) from rfl]
  have h2pow : 2 ^ (b - r) = 2 * 2 ^ (b - r - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ b - r)]
  have hpos : 1 ≤ 2 ^ (b - r) := Nat.one_le_two_pow
  exact decide_eq_decide.mpr ⟨by omega, by omega⟩

/-- **Exact correlation of the subcube majority predictor `andreevSubcubeEval` with `andreev`**:
for all `r < b` and `m : ℕ`,
`2 * #{w | andreevSubcubeEval b m r w = andreev b m w} =
  2 ^ (2 ^ b + b * m) +
    2 ^ (2 ^ b + b * m - (2 ^ (b - r) - 1)) * (2 ^ (b - r) - 1).choose (2 ^ (b - r - 1) - 1)`. -/
theorem two_mul_card_andreevSubcubeEval_eq_andreev {b r : ℕ} (hr : r < b) (m : ℕ) :
    2 * #{w : BitString (2 ^ b + b * m) | andreevSubcubeEval b m r w = andreev b m w} =
      2 ^ (2 ^ b + b * m) + 2 ^ (2 ^ b + b * m - (2 ^ (b - r) - 1)) *
        (2 ^ (b - r) - 1).choose (2 ^ (b - r - 1) - 1) := by
  rw [card_filter, ← Equiv.sum_comp (andreevShiftTable b m)]
  simp only [andreevSubcubeEval_shiftTable hr, andreev_shiftTable, ← card_filter]
  simpa [Fintype.card_fin, card_andreevZeroPuncturedSupport hr.le] using
    two_mul_card_filter_decide_le_eq (andreevZeroPuncturedSupport b m r)
      (andreevZeroTableCoord_notMem_puncturedSupport b m r)
      (Nat.one_le_two_pow : 1 ≤ 2 ^ (b - r - 1))

/-- `two_mul_card_andreevSubcubeEval_eq_andreev` over `ℝ`. -/
private theorem cast_two_mul_card_andreevSubcubeEval_eq_andreev {b r : ℕ} (hr : r < b) (m : ℕ) :
    (2 * (#{w : BitString (2 ^ b + b * m) |
      andreevSubcubeEval b m r w = andreev b m w} : ℝ)) =
      (2 ^ (2 ^ b + b * m) : ℝ) + (2 ^ (2 ^ b + b * m - (2 ^ (b - r) - 1)) : ℝ) *
        ((2 ^ (b - r) - 1).choose (2 ^ (b - r - 1) - 1) : ℝ) := by
  exact_mod_cast two_mul_card_andreevSubcubeEval_eq_andreev hr m

/-! ### Hoeffding window union bound and average-case circuit upper bounds -/

/-- The window center `⌊|S| m / 2⌋` lies within `1 / 2` below `|S| m / 2`. -/
theorem sub_andreevWindowCenter_mem_Icc {b : ℕ} (m : ℕ) (S : Finset (Fin b)) :
    0 ≤ (#S * m : ℝ) / 2 - andreevWindowCenter m S ∧
      (#S * m : ℝ) / 2 - andreevWindowCenter m S ≤ 1 / 2 := by
  have h1 : 2 * (((#S * m) / 2 : ℕ) : ℝ) ≤ #S * m := by exact_mod_cast Nat.mul_div_le (#S * m) 2
  have h2 : (#S * m : ℝ) ≤ 2 * (((#S * m) / 2 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (show #S * m ≤ 2 * ((#S * m) / 2) + 1 by omega)
  simp only [andreevWindowCenter, Int.cast_natCast]
  constructor <;> linarith

/-- If `|X_S(w)| < 2 * t` and `|t_S(w) - #S * m / 2| < t` with `3 * t + 1 / 2 ≤ B`, then both
staircase forms `andreevStairForm b m S τ w` (`X_S(w) + t_S(w)` and `t_S(w)`) lie in
`[andreevWindowLower m B S, andreevWindowLower m B S + 2 * B]`. -/
theorem mem_window_of_tableScore_and_blockSum_lt {b m B : ℕ} {S : Finset (Fin b)}
    {w : BitString (2 ^ b + b * m)} {t : ℝ} (hB : 3 * t + 1 / 2 ≤ (B : ℝ))
    (hX : |(andreevTableScore b m S w : ℝ)| < 2 * t)
    (ht : |(andreevBlockSum b m S w : ℝ) - (#S * m : ℝ) / 2| < t) (τ : Bool) :
    andreevWindowLower m B S ≤ andreevStairForm b m S τ w ∧
      andreevStairForm b m S τ w ≤ andreevWindowLower m B S + (2 * B : ℕ) := by
  have hfloor := sub_andreevWindowCenter_mem_Icc m S
  simp only [andreevWindowCenter, Int.cast_natCast] at hfloor
  rw [abs_lt] at hX ht
  rw [← Int.cast_le (R := ℝ), ← Int.cast_le (R := ℝ)]
  cases τ <;>
    simp only [andreevWindowLower, andreevWindowCenter, andreevStairForm, ↓reduceIte,
      Bool.false_eq_true, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_ofNat,
      Int.cast_natCast, Nat.cast_mul, Nat.cast_ofNat] <;>
    constructor <;> linarith

/-- **Hoeffding union bound on out-of-window inputs**: for any `t ≥ 0` with `3 * t + 1 / 2 ≤ B`,
at most `#(andreevPrefixSubsets b r) * 2 * 2 ^ (2 ^ b + b * m) *
(exp (-(2 * t ^ 2 / 2 ^ b)) + exp (-(2 * t ^ 2 / (b * m))))` inputs `w` violate
`andreevInWindow b m r B w`. -/
theorem card_not_andreevInWindow_le (b m r B : ℕ) {t : ℝ} (ht : 0 ≤ t)
    (hB : 3 * t + 1 / 2 ≤ (B : ℝ)) :
    (#{w : BitString (2 ^ b + b * m) | ¬ andreevInWindow b m r B w} : ℝ) ≤
      #(andreevPrefixSubsets b r) * (2 * 2 ^ (2 ^ b + b * m)) *
        (exp (-(2 * t ^ 2 / (2 ^ b : ℝ))) + exp (-(2 * t ^ 2 / (b * m : ℝ)))) := by
  have hsub : ({w : BitString (2 ^ b + b * m) | ¬ andreevInWindow b m r B w} : Finset _) ⊆
      (andreevPrefixSubsets b r).biUnion fun S =>
        ({w : BitString (2 ^ b + b * m) | 2 * t ≤ |(andreevTableScore b m S w : ℝ)|} : Finset _) ∪
          ({w : BitString (2 ^ b + b * m) |
            t ≤ |(andreevBlockSum b m S w : ℝ) - (#S * m : ℝ) / 2|} : Finset _) := by
    intro w hw; simp only [mem_filter, mem_univ, true_and, andreevInWindow, not_forall] at hw
    rcases hw with ⟨S, hS, τ, hnot⟩
    rw [mem_biUnion]; refine ⟨S, hS, ?_⟩; simp only [mem_union, mem_filter, mem_univ, true_and]
    by_contra! hboth; exact hnot (mem_window_of_tableScore_and_blockSum_lt hB hboth.1 hboth.2 τ)
  have hcard := (card_le_card hsub).trans (card_biUnion_le.trans
    (sum_le_sum fun S _ => card_union_le _ _))
  refine ((Nat.cast_le (α := ℝ).mpr hcard).trans ((Nat.cast_sum _ _).trans_le (sum_le_sum
    fun S _ => (Nat.cast_add _ _).trans_le (add_le_add
      (card_filter_le_abs_andreevTableScore b m S ht)
      (card_filter_le_abs_andreevBlockSum_sub_half_bm b m S ht))))).trans_eq ?_
  simp only [sum_const, nsmul_eq_mul]
  ring

/-- **High-probability `(1 - δ)`-agreement depth-two threshold circuit upper bound (`r = b`)**:
`andreevWindowedCircuit b m b B` has `4 * 2 ^ b * B + 1` gates and depth at most `2`, and disagrees
with `Boolean.andreev b m` on at most
`2 ^ b * (2 * 2 ^ (2 ^ b + b * m)) * (exp (-(2 * t ^ 2 / 2 ^ b)) + exp (-(2 * t ^ 2 / (b * m))))`
inputs whenever `0 ≤ t` and `3 * t + 1 / 2 ≤ B`. -/
theorem card_eval_andreevWindowedCircuit_self_ne_le (b m B : ℕ) (o : Fin 1)
    {t : ℝ} (ht : 0 ≤ t) (hB : 3 * t + 1 / 2 ≤ (B : ℝ)) :
    (#{w : BitString (2 ^ b + b * m) |
      (andreevWindowedCircuit b m b B).eval interpretation w o ≠ andreev b m w} : ℝ) ≤
      2 ^ b * (2 * 2 ^ (2 ^ b + b * m)) *
        (exp (-(2 * t ^ 2 / (2 ^ b : ℝ))) + exp (-(2 * t ^ 2 / (b * m : ℝ)))) := by
  refine ((Nat.cast_le.mpr (card_le_card fun w hw => ?_)).trans
    (card_not_andreevInWindow_le b m b B ht hB)).trans_eq
    (by rw [card_andreevPrefixSubsets le_rfl, Nat.cast_pow, Nat.cast_ofNat])
  simp only [mem_filter, mem_univ, true_and] at hw ⊢
  exact fun hin => hw (eval_andreevWindowedCircuit_self_eq_andreev_of_inWindow hin o)

/-- Every input `w` on which `andreevSubcubeEval b m r` agrees with `andreev b m` either agrees
with `andreevWindowedCircuit b m r B` or lies outside the window `andreevInWindow b m r B`. -/
theorem card_andreevSubcubeEval_eq_le_card_eval_andreevWindowedCircuit_add (b m r B : ℕ)
    (o : Fin 1) :
    #{w : BitString (2 ^ b + b * m) | andreevSubcubeEval b m r w = andreev b m w} ≤
      #{w : BitString (2 ^ b + b * m) |
        (andreevWindowedCircuit b m r B).eval interpretation w o = andreev b m w} +
      #{w : BitString (2 ^ b + b * m) | ¬ andreevInWindow b m r B w} := by
  refine (card_le_card ?_).trans (card_union_le _ _)
  intro w hw; simp only [mem_filter, mem_univ, true_and, mem_union] at hw ⊢
  by_cases hin : andreevInWindow b m r B w
  · exact Or.inl ((eval_andreevWindowedCircuit_eq_subcubeEval_of_inWindow hin o).trans hw)
  · exact Or.inr hin

/-- **Average-case `(1 / 2 + ε)`-correlation depth-two threshold circuit upper bound (`r < b`)**:
for `r < b`, `0 ≤ t`, and `3 * t + 1 / 2 ≤ B`, `andreevWindowedCircuit b m r B` has
`4 * 2 ^ r * B + 1` gates and depth at most `2`, and agrees with `Boolean.andreev b m` on at least
`2 ^ (2 ^ b + b * m) / 2 + 2 ^ (2 ^ b + b * m - (2 ^ (b - r) - 1)) *
  (2 ^ (b - r) - 1).choose (2 ^ (b - r - 1) - 1) / 2 -
  2 ^ r * (2 * 2 ^ (2 ^ b + b * m)) * (exp (-(2 * t ^ 2 / 2 ^ b)) + exp (-(2 * t ^ 2 / (b * m))))`
inputs. -/
theorem card_eval_andreevWindowedCircuit_eq_andreev_ge {b r : ℕ} (hr : r < b) (m B : ℕ)
    (o : Fin 1) {t : ℝ} (ht : 0 ≤ t) (hB : 3 * t + 1 / 2 ≤ (B : ℝ)) :
    (2 ^ (2 ^ b + b * m) : ℝ) / 2 +
      (2 ^ (2 ^ b + b * m - (2 ^ (b - r) - 1)) : ℝ) *
        ((2 ^ (b - r) - 1).choose (2 ^ (b - r - 1) - 1) : ℝ) / 2 -
      2 ^ r * (2 * 2 ^ (2 ^ b + b * m)) *
        (exp (-(2 * t ^ 2 / (2 ^ b : ℝ))) + exp (-(2 * t ^ 2 / (b * m : ℝ)))) ≤
      (#{w : BitString (2 ^ b + b * m) |
        (andreevWindowedCircuit b m r B).eval interpretation w o = andreev b m w} : ℝ) := by
  have hsub := cast_two_mul_card_andreevSubcubeEval_eq_andreev hr m
  have hsplit := Nat.cast_le (α := ℝ).mpr
    (card_andreevSubcubeEval_eq_le_card_eval_andreevWindowedCircuit_add b m r B o)
  rw [Nat.cast_add] at hsplit
  have htail := card_not_andreevInWindow_le b m r B ht hB
  rw [card_andreevPrefixSubsets hr.le, Nat.cast_pow, Nat.cast_ofNat] at htail
  linarith

/-- The central binomial lower bound in the form used by the vote: the exact agreement count of
`two_mul_card_andreevSubcubeEval_eq_andreev` is at least `2 ^ n (1 / 2 + 1 / (2 √(2 L)))` for
`L = 2 ^ (b - r)`. -/
private theorem two_pow_mul_half_add_le_two_pow_add_choose {b r : ℕ} (hr : r < b) (m : ℕ) :
    (2 ^ (2 ^ b + b * m) : ℝ) * (1 / 2 + 1 / (2 * Real.sqrt (2 * 2 ^ (b - r)))) ≤
      (2 ^ (2 ^ b + b * m) : ℝ) / 2 +
        (2 ^ (2 ^ b + b * m - (2 ^ (b - r) - 1)) : ℝ) *
          ((2 ^ (b - r) - 1).choose (2 ^ (b - r - 1) - 1) : ℝ) / 2 := by
  have hbinom_nat := pow_two_mul_sub_one_sq_le (Nat.one_le_two_pow : 1 ≤ 2 ^ (b - r - 1))
  rw [show 4 * 2 ^ (b - r - 1) = 2 * (2 * 2 ^ (b - r - 1)) by ring, ← pow_succ',
    Nat.sub_add_cancel (by omega : 1 ≤ b - r)] at hbinom_nat
  have hbinom : (2 : ℝ) ^ (2 ^ (b - r) - 1) ≤
      Real.sqrt (2 * 2 ^ (b - r)) * ((2 ^ (b - r) - 1).choose (2 ^ (b - r - 1) - 1) : ℝ) := by
    refine le_of_sq_le_sq ?_ (by positivity)
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    exact_mod_cast hbinom_nat
  have hpow_split : (2 : ℝ) ^ (2 ^ b + b * m) =
      (2 : ℝ) ^ (2 ^ b + b * m - (2 ^ (b - r) - 1)) * (2 : ℝ) ^ (2 ^ (b - r) - 1) := by
    rw [← pow_add, Nat.sub_add_cancel ((Nat.sub_le _ _).trans
      (Nat.le_add_right_of_le (Nat.pow_le_pow_right (by decide) (by omega))))]
  rw [mul_add, mul_one_div]
  refine add_le_add_right ?_ ((2 ^ (2 ^ b + b * m) : ℝ) / 2)
  rw [hpow_split, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [(by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (2 ^ b + b * m - (2 ^ (b - r) - 1)))]

/-- **Agreement of the subcube vote**: for `r < b`, the majority vote
`andreevSubcubeEval b m r` over the `L = 2 ^ (b - r)` table bits of the subcube agrees with
`andreev b m` on at least a `1 / 2 + 1 / (2 √(2 L))` fraction of the inputs. -/
theorem two_pow_mul_le_card_andreevSubcubeEval_eq_andreev {b r : ℕ} (hr : r < b) (m : ℕ) :
    (2 ^ (2 ^ b + b * m) : ℝ) * (1 / 2 + 1 / (2 * Real.sqrt (2 * 2 ^ (b - r)))) ≤
      (#{w : BitString (2 ^ b + b * m) | andreevSubcubeEval b m r w = andreev b m w} : ℝ) := by
  linarith [cast_two_mul_card_andreevSubcubeEval_eq_andreev hr m,
    two_pow_mul_half_add_le_two_pow_add_choose hr m]

/-- Closed-form square-root correlation lower bound for `andreevWindowedCircuit b m r B` when
`r < b`, combining `card_eval_andreevWindowedCircuit_eq_andreev_ge` with the central binomial
lower bound `pow_two_mul_sub_one_sq_le`. -/
theorem card_eval_andreevWindowedCircuit_eq_andreev_ge_sqrt {b r : ℕ} (hr : r < b) (m B : ℕ)
    (o : Fin 1) {t : ℝ} (ht : 0 ≤ t) (hB : 3 * t + 1 / 2 ≤ (B : ℝ)) :
    (2 ^ (2 ^ b + b * m) : ℝ) * (1 / 2 + 1 / (2 * Real.sqrt (2 * 2 ^ (b - r)))) -
      2 ^ r * (2 * 2 ^ (2 ^ b + b * m)) *
        (exp (-(2 * t ^ 2 / (2 ^ b : ℝ))) + exp (-(2 * t ^ 2 / (b * m : ℝ)))) ≤
      (#{w : BitString (2 ^ b + b * m) |
        (andreevWindowedCircuit b m r B).eval interpretation w o = andreev b m w} : ℝ) :=
  (sub_le_sub_right (two_pow_mul_half_add_le_two_pow_add_choose hr m) _).trans
    (card_eval_andreevWindowedCircuit_eq_andreev_ge hr m B o ht hB)

end Cslib.Circuits.Boolean.WeightedThreshold
