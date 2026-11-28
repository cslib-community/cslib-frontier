/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

public import CslibFrontier.Foundations.Combinatorics.AffineDisperser.Li.AltExt
public import CslibFrontier.Foundations.Combinatorics.AffineDisperser.Li.LinearStrongExtractor
public meta import CslibFrontier.Foundations.Combinatorics.AffineDisperser.Li.LinearStrongExtractor
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Logb
import CslibFrontier.Probability.MinEntropy
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Checked `module` clients for Work Package 2 of #7793:
* `CslibFrontier.Foundations.Combinatorics.AffineDisperser.Li.LinearStrongExtractor`
* `CslibFrontier.Foundations.Combinatorics.AffineDisperser.Li.AltExt`

Exercises concrete non-vacuous witnesses, linearity & structural checks, boundary behavior, and
alternating-extraction / polynomial-correlation-breaker compositions. The `#guard` checks run the
compiled blocks of `rrvWeakDesign` and `rrvWeakDesignTwo`. -/

set_option linter.hashCommand false

public section

namespace CslibFrontierTests.LiLinearStrongExtractor

open Cslib Cslib.BitString Cslib.AffineDisperser.Li Cslib.Probability Cslib.Probability.PMF Finset

private theorem minEntropy_uniformOfFintype_bitString (n : ℕ) :
    minEntropy (PMF.uniformOfFintype (BitString n)) = (n : ℝ) := by
  rw [minEntropy_uniformOfFintype, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Nat.cast_pow, Nat.cast_ofNat, Real.logb_two_pow]

/-! ### 1. Linear Toeplitz extractor, RRV weak designs, RS–Hadamard code, and Trevisan–RRV -/

/-- Unconditional concrete `IsLinearStrongExtractor` witness via `toeplitzLinearExt` on `n = 8`,
`m = 2`, `k = 6`, seed length `9 < 16` (`δ = 1 / 4`, error `1 / 8`). -/
theorem isLinearStrongExtractor_toeplitz_8_2 :
    IsLinearStrongExtractor (toeplitzLinearExt 8 2) 6 (1 / 8) := by
  have h := isLinearStrongExtractor_toeplitz 8 2 (δ := 1 / 4) (by norm_num) (k := 6) (by
    have hlog : Real.logb 2 ((1 / 4 : ℝ)⁻¹) = 2 := by
      rw [show (1 / 4 : ℝ)⁻¹ = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.logb_pow,
        Real.logb_self_eq_one (by norm_num)]
      norm_num
    rw [hlog]
    norm_num)
  norm_num at h
  exact h

/-- Boundary/linearity check for `toeplitzLinearExt`: `𝔽₂`-linear in `x` for any seed `a`. -/
example (x₁ x₂ : BitString 8) (a : BitString (2 + 8 - 1)) :
    toeplitzLinearExt 8 2 (x₁ + x₂) a = toeplitzLinearExt 8 2 x₁ a + toeplitzLinearExt 8 2 x₂ a :=
  isLinearStrongExtractor_toeplitz_8_2.2 a x₁ x₂

/-- Concrete `WeakDesign` instance witness: `rrvWeakDesignTwo 2 2` builds two blocks of size `2`
inside `Fin 8` with exponential overlap bound `≤ 2 * 2 = 4`. -/
theorem rrvWeakDesignTwo_2_2_overlap_le :
    ∑ j : Fin 1, (2 : ℝ) ^ #((rrvWeakDesignTwo 2 2 (by omega)).block 1 ∩
      (rrvWeakDesignTwo 2 2 (by omega)).block (Fin.castLE (by omega) j)) ≤ 4 := by
  have h := (rrvWeakDesignTwo 2 2 (by omega)).sum_two_pow_inter_le 1
  norm_num at h
  simpa using h

/-- Concrete block-size check on `rrvWeakDesignTwo`. -/
theorem rrvWeakDesignTwo_2_2_card_block (i : Fin 2) :
    #((rrvWeakDesignTwo 2 2 (by omega)).block i) = 2 :=
  (rrvWeakDesignTwo 2 2 (by omega)).card_block i

/-! The `#guard`s below run the compiled blocks of the RRV designs, element values in increasing
order. The expected values of the first three come from an independent implementation of the
greedy choice. -/

#guard (List.finRange 2).map (fun i =>
    ((List.finRange (2 * (2 * 2))).filter (· ∈ (rrvWeakDesignTwo 2 2 (by omega)).block i)).map
      Fin.val) == [[0, 4], [1, 5]]

#guard (List.finRange 4).map (fun i =>
    ((List.finRange (8 * 2)).filter (· ∈ (rrvWeakDesign 8 2 4 (by omega)).block i)).map
      Fin.val) ==
  [[0, 2, 4, 6, 8, 10, 12, 14], [1, 3, 5, 7, 9, 11, 13, 15], [0, 3, 4, 7, 8, 11, 12, 15],
    [1, 2, 5, 6, 9, 10, 13, 14]]

-- With no earlier blocks every potential is `0`, so the first block takes value `0` at every
-- coordinate.
#guard ((List.finRange (40 * 2)).filter (· ∈ (rrvWeakDesign 40 2 1 (by omega)).block 0)).map
    Fin.val == (List.range 40).map (2 * ·)

-- With `t = 0` every block is empty.
#guard ((rrvWeakDesign 0 2 3 (by omega)).block 2).card == 0

/-- Concatenated RS–Hadamard code XOR-linearity witness. -/
theorem rsHadamardCode_4_2_add (x y : BitString 4) (idx : BitString (2 + 2)) :
    rsHadamardCode 4 2 (by omega) (x + y) idx =
      (rsHadamardCode 4 2 (by omega) x idx != rsHadamardCode 4 2 (by omega) y idx) := by
  simpa [Bool.add_eq_xor] using rsHadamardCode_add 4 2 (by omega) x y idx

/-- Concrete binary Johnson list-decoding witness for `rsHadamardCode 1 2`: at agreement
`1 / 2 + 1 / 2 = 1`, strictly fewer than `2` codewords agree with any received word (i.e. at
most `1`). -/
theorem card_filter_rsHadamardCode_1_2_le_one (recv : BitString (2 + 2) → Bool) :
    (#({x : BitString 1 |
        (1 / 2 + 1 / 2) * (2 : ℝ) ^ (2 + 2) ≤
          #{z : BitString (2 + 2) | rsHadamardCode 1 2 (by omega) x z = recv z}} :
      Finset (BitString 1)) : ℝ) < 2 := by
  have hlt := card_filter_rsHadamardCode_agree_mul_lt_one 1 2 (by omega) (δ := 1 / 2)
    (by norm_num) (by
      have hdeg : rsDeg 1 2 = 1 := rfl
      rw [hdeg]
      norm_num) recv
  linarith

/-- Concrete non-vacuous sublinear-seed `trevisanRRVExt` witness: on `n = 2048` input bits,
`w = 14` gives seed length `1568 < 2048`, output `m = 1`, error `1 / 2`, and min-entropy `k = 7`. -/
theorem isLinearStrongExtractor_trevisanRRV_2048_1 :
    IsLinearStrongExtractor (trevisanRRVExt 2048 1 14 (by omega)) 7 (1 / 2) := by
  refine isLinearStrongExtractor_trevisanRRV (hm := by omega) (hw := by omega) (hε := by norm_num)
    (hw_bound := by norm_num) (hk := ?_)
  have h2 : ((1 : ℕ) : ℝ) / (1 / 2) = 2 := by norm_num
  rw [h2, Real.logb_self_eq_one (by norm_num)]
  norm_num

/-- Symmetric power-of-two `trevisanRRVExt` witness (`w = 64`, `m = seed = 32768`, `n = 2 ^ 18`,
`ε = 1 / 16`, `k = 65595`) for alternating extraction composition below. -/
theorem isLinearStrongExtractor_trevisanRRV_symm :
    IsLinearStrongExtractor
      (trevisanRRVExt (2 ^ 18) ((64 + 64) * (2 * (64 + 64))) 64 (by omega))
      65595 (1 / 16) := by
  refine isLinearStrongExtractor_trevisanRRV (hm := by omega) (hw := by omega) (hε := by norm_num)
    (hw_bound := by norm_num) (hk := ?_)
  have hratio : (((((64 + 64) * (2 * (64 + 64)) : ℕ) : ℝ) / (1 / 16))) = (2 : ℝ) ^ (19 : ℕ) := by
    norm_num
  rw [hratio, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
  norm_num

/-! ### 2. Imperfect seeds, alternating extraction look-ahead, and `vanderCB` -/

/-- Imperfect-seed witness via `dist_strongExtractor_weakSeed_le`: extracting from a source of
min-entropy `6` on `BitString 8` with a `BitString 9` weak seed of min-entropy `8` (1 bit below
uniform) has statistical distance at most `2 * (1 / 8) = 1 / 4` from uniform jointly with the
seed. -/
theorem dist_toeplitz_weakSeed_witness :
    let Seed := BitString (2 + 8 - 1)
    let ext : BitString 8 → Seed → BitString 2 := toeplitzLinearExt 8 2
    ∀ (X : PMF (BitString 8)) (S : PMF Seed),
      6 ≤ minEntropy X → 8 ≤ minEntropy S →
      dist (X.bind fun x => S.map fun s => (s, ext x s))
        (S.bind fun s => (PMF.uniformOfFintype (BitString 2)).map (s, ·)) ≤ 1 / 4 := by
  intro Seed ext X S hX hS
  have h := dist_strongExtractor_weakSeed_le (kSeed := 8) isLinearStrongExtractor_toeplitz_8_2.1
    hX S id (by rwa [PMF.map_id])
  have hcard : (Fintype.card Seed : ℝ) * (2 : ℝ) ^ (-(8 : ℝ)) * (1 / 8) = 1 / 4 := by
    have hc : Fintype.card Seed = 2 ^ 9 := by
      simp [Seed]
    rw [hc, Nat.cast_pow, Nat.cast_ofNat, Real.rpow_neg zero_le_two, Real.rpow_ofNat]
    norm_num
  have hcomm : (X.bind fun x => S.map fun s => (s, ext x s)) =
      S.bind fun s => X.map fun x => (s, ext x s) := by
    simp only [PMF.map, Function.comp_def]
    exact PMF.bind_comm X S _
  rw [hcomm]
  exact h.trans_eq hcard

/-- Per-round active-source linearity check for `altExtR` via `altExtR_add_source`. -/
example (x₁ x₂ : BitString 8) (y : BitString 2) (ext2 : BitString 2 → BitString 2 → BitString 9)
    (s0 : BitString (2 + 8 - 1)) (k : ℕ) :
    altExtR (toeplitzLinearExt 8 2) ext2 (x₁ + x₂) y s0 k =
      toeplitzLinearExt 8 2 x₁ (altExtS (toeplitzLinearExt 8 2) ext2 (x₁ + x₂) y s0 k) +
      toeplitzLinearExt 8 2 x₂ (altExtS (toeplitzLinearExt 8 2) ext2 (x₁ + x₂) y s0 k) :=
  altExtR_add_source ext2 isLinearStrongExtractor_toeplitz_8_2 x₁ x₂ y s0 k

/-- Concrete two-source round-1 look-ahead witness (`k = 1`, `r = 1`, `ε = 1 / 16`, `δ = 1 / 32`,
total error `5 / 16 < 1 / 2`) via `dist_altExt_lookAhead_le` instantiated with
`isLinearStrongExtractor_trevisanRRV_symm`. -/
theorem dist_altExt_trevisanRRV_lookAhead_witness :
    let d := (64 + 64) * (2 * (64 + 64))
    let ext := trevisanRRVExt (2 ^ 18) d 64 (by omega)
    let view
        (px : BitString (2 ^ 18) × (Fin 1 → BitString (2 ^ 18)))
        (py : (BitString (2 ^ 18) × (Fin 1 → BitString (2 ^ 18))) ×
          (BitString d × (Fin 1 → BitString d))) :=
      let (x, x') := px
      let ((y, y'), (s0, s0')) := py
      (py, (fun i : Fin 1 => altExtR ext ext x y s0 i.val,
            fun i : Fin 2 => fun j : Fin 1 =>
              altExtR ext ext (x' j) (y' j) (s0' j) i.val))
    dist
      ((PMF.uniformOfFintype (BitString (2 ^ 18) × (Fin 1 → BitString (2 ^ 18)))).bind fun px =>
        let (x, _) := px
        (PMF.uniformOfFintype _).map fun py =>
          let ((y, _), (s0, _)) := py
          (view px py, altExtR ext ext x y s0 1))
      ((((PMF.uniformOfFintype (BitString (2 ^ 18) × (Fin 1 → BitString (2 ^ 18)))).bind fun px =>
          (PMF.uniformOfFintype _).map fun py => view px py)).bind fun v =>
        (PMF.uniformOfFintype (BitString d)).map fun u => (v, u)) ≤ 5 / 16 := by
  intro d ext view
  let PX := PMF.uniformOfFintype (BitString (2 ^ 18) × (Fin 1 → BitString (2 ^ 18)))
  let PY := PMF.uniformOfFintype ((BitString (2 ^ 18) × (Fin 1 → BitString (2 ^ 18))) ×
    (BitString d × (Fin 1 → BitString d)))
  change dist
      (PX.bind fun px =>
        let (x, _) := px
        PY.map fun py =>
          let ((y, _), (s0, _)) := py
          (view px py, altExtR ext ext x y s0 1))
      ((PX.bind fun px => PY.map fun py => view px py).bind fun v =>
        (PMF.uniformOfFintype (BitString d)).map fun u => (v, u)) ≤ 5 / 16
  have hPX : ((2 ^ 18 : ℕ) : ℝ) ≤ minEntropy (PX.map Prod.fst) := by
    have hunif : PX.map Prod.fst = PMF.uniformOfFintype (BitString (2 ^ 18)) := by
      change (PMF.uniformOfFintype (BitString (2 ^ 18) × (Fin 1 → BitString (2 ^ 18)))).map
        Prod.fst = _
      exact uniformOfFintype_prod_map_fst
    rw [hunif, minEntropy_uniformOfFintype_bitString]
  have hPY : ((2 ^ 18 : ℕ) : ℝ) ≤ minEntropy (PY.map fun ⟨⟨y, _⟩, _⟩ => y) := by
    have hunif : (PY.map fun ⟨⟨y, _⟩, _⟩ => y) = PMF.uniformOfFintype (BitString (2 ^ 18)) := by
      have h1 : (PY.map fun ⟨⟨y, _⟩, _⟩ => y) = (PY.map Prod.fst).map Prod.fst := by
        rw [PMF.map_comp]; rfl
      have hfst : PY.map Prod.fst =
          PMF.uniformOfFintype (BitString (2 ^ 18) × (Fin 1 → BitString (2 ^ 18))) := by
        change (PMF.uniformOfFintype _).map Prod.fst = _
        exact uniformOfFintype_prod_map_fst
      rw [h1, hfst]
      exact uniformOfFintype_prod_map_fst
    rw [hunif, minEntropy_uniformOfFintype_bitString]
  have hη0 : dist (PY.map fun ⟨_, ⟨s0, s0'⟩⟩ => (s0', s0))
      ((PY.map fun ⟨_, ⟨_, s0'⟩⟩ => s0').bind fun s' =>
        (PMF.uniformOfFintype (BitString d)).map (s', ·)) ≤ 0 := by
    have hsnd : PY.map Prod.snd =
        PMF.uniformOfFintype (BitString d × (Fin 1 → BitString d)) := by
      change (PMF.uniformOfFintype _).map Prod.snd = _
      exact uniformOfFintype_prod_map_snd
    have hL : (PY.map fun ⟨_, ⟨s0, s0'⟩⟩ => (s0', s0)) =
        PMF.uniformOfFintype ((Fin 1 → BitString d) × BitString d) := by
      have h1 : (PY.map fun ⟨_, ⟨s0, s0'⟩⟩ => (s0', s0)) =
          (PY.map Prod.snd).map Prod.swap := by
        rw [PMF.map_comp]; rfl
      rw [h1, hsnd]
      change (PMF.uniformOfFintype (BitString d × (Fin 1 → BitString d))).map
        (Equiv.prodComm _ _) = _
      exact PMF.uniformOfFintype_map_equiv (Equiv.prodComm _ _)
    have hR : ((PY.map fun ⟨_, ⟨_, s0'⟩⟩ => s0').bind fun s' =>
          (PMF.uniformOfFintype (BitString d)).map (s', ·)) =
        PMF.uniformOfFintype ((Fin 1 → BitString d) × BitString d) := by
      have hm : (PY.map fun ⟨_, ⟨_, s0'⟩⟩ => s0') =
          (PY.map Prod.snd).map Prod.snd := by
        rw [PMF.map_comp]; rfl
      rw [hm, hsnd, uniformOfFintype_prod_map_snd, ← uniformOfFintype_prod]
    rw [hL, hR, dist_self]
  have hlog32 : Real.logb 2 ((1 / 32 : ℝ)⁻¹) = 5 := by
    rw [show (1 / 32 : ℝ)⁻¹ = (2 : ℝ) ^ (5 : ℕ) by norm_num, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num)]
    norm_num
  have h := dist_altExt_lookAhead_le (kX := ((2 ^ 18 : ℕ) : ℝ)) (kY := ((2 ^ 18 : ℕ) : ℝ))
    (η0 := 0) (δ := 1 / 32) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    isLinearStrongExtractor_trevisanRRV_symm.1 isLinearStrongExtractor_trevisanRRV_symm.1
    PX PY hPX hPY hη0 1
    (by rw [hlog32]; norm_num)
    (by rw [hlog32]; norm_num)
  exact h.trans_eq (by norm_num)

/-- Concrete sumset alternating-extraction witness (`k = 1`, `ε = 1 / 16`, `δ = 1 / 32`, total
error `5 / 16 < 1 / 2`) via `dist_altExt_sumset_lookAhead_le` and
`isLinearStrongExtractor_trevisanRRV_symm`. -/
theorem dist_altExt_sumset_trevisanRRV_witness :
    let d := (64 + 64) * (2 * (64 + 64))
    let ext := trevisanRRVExt (2 ^ 18) d 64 (by omega)
    let view (a : BitString (2 ^ 18)) (bs : BitString (2 ^ 18) × BitString d) :=
      (bs, fun i : Fin 1 => altExtR ext ext (a + bs.1) (a + bs.1) bs.2 i.val)
    dist
      ((PMF.uniformOfFintype (BitString (2 ^ 18))).bind fun a =>
        (PMF.uniformOfFintype (BitString (2 ^ 18) × BitString d)).map fun bs =>
          (view a bs, altExtR ext ext (a + bs.1) (a + bs.1) bs.2 1))
      (((PMF.uniformOfFintype (BitString (2 ^ 18))).bind fun a =>
          (PMF.uniformOfFintype (BitString (2 ^ 18) × BitString d)).map fun bs =>
            view a bs).bind fun v =>
        (PMF.uniformOfFintype (BitString d)).map fun u => (v, u)) ≤ 5 / 16 := by
  intro d ext view
  have hA : ((2 ^ 18 : ℕ) : ℝ) ≤ minEntropy (PMF.uniformOfFintype (BitString (2 ^ 18))) := by
    rw [minEntropy_uniformOfFintype_bitString]
  have hB : ((2 ^ 18 : ℕ) : ℝ) ≤
      minEntropy ((PMF.uniformOfFintype (BitString (2 ^ 18) × BitString d)).map Prod.fst) := by
    rw [uniformOfFintype_prod_map_fst, minEntropy_uniformOfFintype_bitString]
  have hη0 : dist ((PMF.uniformOfFintype (BitString (2 ^ 18) × BitString d)).map Prod.snd)
      (PMF.uniformOfFintype (BitString d)) ≤ 0 := by
    rw [uniformOfFintype_prod_map_snd, dist_self]
  have hlog32 : Real.logb 2 ((1 / 32 : ℝ)⁻¹) = 5 := by
    rw [show (1 / 32 : ℝ)⁻¹ = (2 : ℝ) ^ (5 : ℕ) by norm_num, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num)]
    norm_num
  have h := dist_altExt_sumset_lookAhead_le (kA := ((2 ^ 18 : ℕ) : ℝ)) (kB := ((2 ^ 18 : ℕ) : ℝ))
    (η0 := 0) (δ := 1 / 32) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    isLinearStrongExtractor_trevisanRRV_symm isLinearStrongExtractor_trevisanRRV_symm
    (PMF.uniformOfFintype (BitString (2 ^ 18)))
    (PMF.uniformOfFintype (BitString (2 ^ 18) × BitString d))
    hA hB hη0 1
    (by rw [hlog32]; norm_num)
    (by rw [hlog32]; norm_num)
  exact h.trans_eq (by norm_num)

/-- Unconditional `t = 2` polynomial weak-seed correlation breaker witness via `vanderCB 2 8` on
`BitString 24` (`kSrc = 23 < 24`, `kSeed = 7 < 8`, error `5 / 16 < 1 / 2`). -/
theorem isLinearWeakSeedCB_vander_2_8 :
    IsLinearWeakSeedCB (vanderCB 2 8 (by omega)) 23 7 2 (5 / 16) := by
  have h := isLinearWeakSeedCB_vander (t := 2) (ℓ := 8) (by omega) (by norm_num)
    (kSrc := 23) (kSeed := 7) (δ := 1 / 16) (by norm_num)
  have hlog : Real.logb 2 ((1 / 16 : ℝ)⁻¹) = 4 := by
    rw [show (1 / 16 : ℝ)⁻¹ = (2 : ℝ) ^ (4 : ℕ) by norm_num, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num)]
    norm_num
  have hval : (1 / 16 : ℝ) +
      (2 : ℝ) ^ (((((2 + 1) * 8 : ℕ) : ℝ) - 23 - 7 + Real.logb 2 ((1 / 16 : ℝ)⁻¹)) / 2) / 2 =
      5 / 16 := by
    rw [hlog]
    have hexp : (((((2 + 1) * 8 : ℕ) : ℝ) - 23 - 7 + 4) / 2) = -(1 : ℕ) := by norm_num
    rw [hexp, Real.rpow_neg zero_le_two, Real.rpow_natCast]
    norm_num
  rwa [hval] at h

/-- Non-vacuous `r = 2` correlation-breaking client witness via `isLinearWeakSeedCB_vander_2_8` on
uniform `B : PMF (BitString 24)` and `J : PMF (BitString 8 × (Fin 2 → BitString 8))` with distinct
8-bit advice strings `![0, 1, 2]`. -/
theorem dist_vanderCB_2_8_client :
    let α : BitString 8 := fun _ => false
    let α' : Fin 2 → BitString 8 :=
      ![fun i => decide (i.val = 0), fun i => decide (i.val = 1)]
    let B := PMF.uniformOfFintype (BitString ((2 + 1) * 8))
    let J := PMF.uniformOfFintype (BitString 8 × (Fin 2 → BitString 8))
    dist
      (B.bind fun b => J.map fun ⟨y, y'⟩ =>
        (vanderCB 2 8 (by omega) b y α, fun j => vanderCB 2 8 (by omega) b (y' j) (α' j)))
      ((PMF.uniformOfFintype Bool).bind fun u =>
        B.bind fun b => J.map fun ⟨_, y'⟩ =>
          (u, fun j => vanderCB 2 8 (by omega) b (y' j) (α' j))) ≤ 5 / 16 := by
  intro α α' B J
  have hα' : ∀ j : Fin 2, α' j ≠ α := by
    intro j hj
    fin_cases j
    · exact absurd (congrFun hj 0) (by decide)
    · exact absurd (congrFun hj 1) (by decide)
  have hB : (23 : ℝ) ≤ minEntropy B := by
    rw [show B = PMF.uniformOfFintype (BitString 24) from rfl,
      minEntropy_uniformOfFintype_bitString]
    norm_num
  have hJ : (7 : ℝ) ≤ minEntropy (J.map Prod.fst) := by
    have hfst : J.map Prod.fst = PMF.uniformOfFintype (BitString 8) := by
      change (PMF.uniformOfFintype (BitString 8 × (Fin 2 → BitString 8))).map Prod.fst = _
      exact uniformOfFintype_prod_map_fst
    rw [hfst, minEntropy_uniformOfFintype_bitString]
    norm_num
  exact isLinearWeakSeedCB_vander_2_8.2 2 (by omega) α α' hα' B J hB hJ

/-- Linearity and negative boundary check for `IsLinearWeakSeedCB`. -/
example (y α : BitString 8) (b₁ b₂ : BitString ((2 + 1) * 8)) :
    vanderCB 2 8 (by omega) (b₁ + b₂) y α =
      vanderCB 2 8 (by omega) b₁ y α + vanderCB 2 8 (by omega) b₂ y α :=
  isLinearWeakSeedCB_vander_2_8.1 y α b₁ b₂

example :
    ¬ IsLinearWeakSeedCB (fun (b y : BitString 2) (_ : Unit) => (b 0 && b 1) != (y 0 && y 1))
      1 1 0 (1 / 4) := by
  rintro ⟨hlin, _⟩
  have h := hlin ![false, false] () ![true, false] ![false, true]
  revert h
  decide

end CslibFrontierTests.LiLinearStrongExtractor
