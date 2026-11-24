/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

import CslibFrontier.Computability.Kolmogorov.LevinCoding
import CslibFrontier.Computability.Kolmogorov.PrefixSymmetry

/-!
Regression clients, concrete finite and geometric witnesses, negative prefix-free boundaries,
and derived consequences for algorithmic probability, Levin's coding theorem, uniform conditional
Kraft–Chaitin, and exact symmetry of information.
-/

namespace CslibFrontierTests.LevinCodingSymmetry

open scoped BigOperators
open Cslib Cslib.Kolmogorov Cslib.Kolmogorov.DescriptionMethod Encodable

/-! ### Finite `universalProb` multiplicity and negative prefix-free boundary -/

example :
    let twoToZeroMethod : DescriptionMethod ℕ :=
      { run p :=
          if p = [false] then Computation.pure 0
          else if p = [true, false] then Computation.pure 0
          else Computation.empty ℕ }
    twoToZeroMethod.IsPrefixFree ∧
      twoToZeroMethod.universalProb 0 = (3 / 4 : ℝ) ∧
      twoToZeroMethod.universalProb 1 = 0 ∧
      twoToZeroMethod.chaitinOmega = (3 / 4 : ℝ) ∧
      (2 : ℝ)⁻¹ ^ twoToZeroMethod.complexity 0 < twoToZeroMethod.universalProb 0 := by
  let M : DescriptionMethod ℕ :=
    { run p :=
        if p = [false] then Computation.pure 0
        else if p = [true, false] then Computation.pure 0
        else Computation.empty ℕ }
  have hprod : ∀ p x, M.Produces p x ↔ (p = [false] ∨ p = [true, false]) ∧ x = 0 := by
    intro p x
    simp only [Produces, M]
    split_ifs with h1 h2
    · constructor
      · intro hx
        have : x = 0 := Computation.mem_unique hx
          (Computation.mem_of_mem_runFor (n := 0) (Computation.runFor_pure 0 0 ▸ rfl))
        exact ⟨Or.inl h1, this⟩
      · rintro ⟨_, rfl⟩
        exact Computation.mem_of_mem_runFor (n := 0) (Computation.runFor_pure 0 0 ▸ rfl)
    · constructor
      · intro hx
        have : x = 0 := Computation.mem_unique hx
          (Computation.mem_of_mem_runFor (n := 0) (Computation.runFor_pure 0 0 ▸ rfl))
        exact ⟨Or.inr h2, this⟩
      · rintro ⟨_, rfl⟩
        exact Computation.mem_of_mem_runFor (n := 0) (Computation.runFor_pure 0 0 ▸ rfl)
    · simp [h1, h2, Computation.notMem_empty]
  have hpf : M.IsPrefixFree := by
    rintro p ⟨x₁, h₁⟩ q ⟨x₂, h₂⟩ hpq
    obtain ⟨hp, _⟩ := (hprod p x₁).mp h₁
    obtain ⟨hq, _⟩ := (hprod q x₂).mp h₂
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> simp at hpq ⊢
  have hu0 : M.universalProb 0 = (3 / 4 : ℝ) := by
    have ha : M.Produces [false] 0 := (hprod _ _).mpr ⟨Or.inl rfl, rfl⟩
    have hb : M.Produces [true, false] 0 := (hprod _ _).mpr ⟨Or.inr rfl, rfl⟩
    let a : {p : List Bool // M.Produces p 0} := ⟨[false], ha⟩
    let b : {p : List Bool // M.Produces p 0} := ⟨[true, false], hb⟩
    have hab : a ≠ b := fun h => by
      have hv := congrArg Subtype.val h
      simp [a, b] at hv
    let S : Finset {p : List Bool // M.Produces p 0} := {a, b}
    have hzero : ∀ p ∉ S, (2 : ℝ)⁻¹ ^ p.1.length = 0 := fun p hp => by
      exfalso
      rcases ((hprod p.1 0).mp p.2).1 with h1 | h2
      · exact hp (Finset.mem_insert.mpr (Or.inl (Subtype.ext h1)))
      · exact hp (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (Subtype.ext h2))))
    rw [universalProb, tsum_eq_sum hzero, Finset.sum_pair hab]
    simp only [a, b, List.length_cons, List.length_nil]
    norm_num
  have hu1 : M.universalProb 1 = 0 := by
    have hzero : ∀ p : {p : List Bool // M.Produces p 1}, (2 : ℝ)⁻¹ ^ p.1.length = 0 := fun p => by
      exfalso
      have : (1 : ℕ) = 0 := ((hprod p.1 1).mp p.2).2
      omega
    simp [universalProb, hzero]
  have homega : M.chaitinOmega = (3 / 4 : ℝ) := by
    have htsum : ∑' x : ℕ, M.universalProb x = M.universalProb 0 := by
      refine tsum_eq_single 0 fun x hx => ?_
      have hzero : ∀ p : {p : List Bool // M.Produces p x}, (2 : ℝ)⁻¹ ^ p.1.length = 0 :=
        fun p => by
          exfalso
          exact hx ((hprod p.1 x).mp p.2).2
      simp [universalProb, hzero]
    rw [← hpf.tsum_universalProb_eq_chaitinOmega, htsum, hu0]
  have hcomp_ge : 1 ≤ M.complexity 0 := by
    have ha : M.Produces [false] 0 := (hprod _ _).mpr ⟨Or.inl rfl, rfl⟩
    have hfin : M.ecomplexity 0 ≠ ⊤ := ne_top_of_le_ne_top (by simp) (ecomplexity_le_length ha)
    obtain ⟨p, hp, hlen⟩ := exists_length_eq_ecomplexity hfin
    rw [← natCast_complexity hfin] at hlen
    have hp_len : p.length = M.complexity 0 := by exact_mod_cast hlen
    rw [← hp_len]
    rcases ((hprod p 0).mp hp).1 with rfl | rfl <;> simp
  have hstrict : (2 : ℝ)⁻¹ ^ M.complexity 0 < M.universalProb 0 := by
    have hpow : (2 : ℝ)⁻¹ ^ M.complexity 0 ≤ (1 / 2 : ℝ) := by
      simpa using pow_le_pow_of_le_one (a := (2 : ℝ)⁻¹) (by positivity) (by norm_num) hcomp_ge
    rw [hu0]
    linarith
  exact ⟨hpf, hu0, hu1, homega, hstrict⟩

-- Negative boundary: extending a program on `ℕ` breaks `IsPrefixFree`.
example :
    let badCond : ℕ → DescriptionMethod ℕ := fun _ =>
      { run p := if p = [] ∨ p = [true] then Computation.pure 0 else Computation.empty ℕ }
    ¬ ∀ y : ℕ, (badCond y).IsPrefixFree := by
  intro badCond hpf
  have hmem0 : (0 : ℕ) ∈ (Computation.pure 0).runFor 0 := by
    change (Computation.pure 0).runFor 0 = some 0
    exact Computation.runFor_pure 0 0
  have h1 : [] ∈ (badCond 0).haltingSet := by
    refine ⟨0, ?_⟩
    simp [Produces, badCond, Computation.mem_of_mem_runFor hmem0]
  have h2 : [true] ∈ (badCond 0).haltingSet := by
    refine ⟨0, ?_⟩
    simp [Produces, badCond, Computation.mem_of_mem_runFor hmem0]
  exact absurd (hpf 0 [] h1 [true] h2 List.nil_prefix) (by simp)

/-! ### Geometric semimeasure and Levin coding clients -/

example :
    (∃ c : ℕ, ∀ n : ℕ, universalPrefix.complexity n ≤ n + 1 + c) ∧
      (∃ c : ℕ, ∀ n : ℕ, (2 : ℝ)⁻¹ ^ (n + 1) ≤ (2 : ℝ) ^ c * universalPrefix.universalProb n) := by
  let μ : ℕ → ℝ := fun n => (2 : ℝ)⁻¹ ^ (n + 1)
  have hnonneg : ∀ n, 0 ≤ μ n := fun n => by positivity
  have hsum : Summable μ := by
    simpa [μ, pow_succ'] using
      (summable_geometric_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num)).mul_left
        (2 : ℝ)⁻¹
  have htsum : ∑' n, μ n ≤ 1 := by
    have hval : (∑' n : ℕ, (2 : ℝ)⁻¹ ^ (n + 1)) = 1 := by
      rw [show (fun n : ℕ => (2 : ℝ)⁻¹ ^ (n + 1)) = fun n => (2 : ℝ)⁻¹ * (2 : ℝ)⁻¹ ^ n from
        funext fun n => by rw [pow_succ']]
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      norm_num
    exact hval.le
  have hμ : IsLowerSemicomputable μ := by
    let num : ℕ → ℕ → ℕ := fun _ _ => 1
    let den : ℕ → ℕ → ℕ := fun n _ => 2 ^ (n + 1)
    have hnum : Computable₂ num := Computable₂.mk (Computable.const 1)
    have hden : Computable₂ den :=
      Computable₂.mk <|
        ((Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2)
          (Primrec.nat_add.comp Primrec.fst (Primrec.const 1))).to_comp
    refine isLowerSemicomputable_of_computable_monotone_tendsto hnum hden
      (fun n _ => Nat.pow_pos (by omega))
      (fun _ _ _ _ => le_rfl)
      (fun n => ?_)
    have hcast : ∀ t : ℕ, (num n t : ℝ) / (den n t : ℝ) = μ n := fun _ => by
      simp [num, den, μ, one_div, inv_pow]
    simp [hcast]
  obtain ⟨c₁, hc₁⟩ := exists_complexity_universalPrefix_le_neg_logb_of_isLowerSemicomputable
    hnonneg hsum htsum hμ
  obtain ⟨c₂, hc₂⟩ := exists_mul_universalProb_universalPrefix_ge hnonneg hsum htsum hμ
  refine ⟨⟨c₁, fun n => ?_⟩, ⟨c₂, hc₂⟩⟩
  have hlog := hc₁ n (by positivity)
  have hneg : -Real.logb 2 (μ n) = ((n + 1 : ℕ) : ℝ) := by
    have hpow : μ n = (2 : ℝ) ^ (-((n + 1 : ℕ) : ℝ)) := by
      rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, ← inv_pow]
    rw [hpow, Real.logb_rpow (by norm_num) (by norm_num)]
    ring
  rw [hneg] at hlog
  exact_mod_cast hlog

-- Combining Solomonoff–Levin universality with marginal semimeasure lower semicomputability.
example :
    ∃ c : ℕ, ∀ x : ℕ,
      ∑' y : ℕ, (2 : ℝ)⁻¹ ^ universalPrefix.complexity (Nat.pair x y) ≤
        (2 : ℝ) ^ c * universalPrefix.universalProb x := by
  let μ : ℕ → ℝ := fun x => ∑' y : ℕ, universalPrefix.universalProb (Nat.pair x y)
  have hnonneg : ∀ x, 0 ≤ μ x := fun _ => tsum_nonneg fun _ => universalProb_nonneg _ _
  obtain ⟨c, hc⟩ := exists_mul_universalProb_universalPrefix_ge
    hnonneg isPrefixFree_universalPrefix.summable_universalProb_marginal
    isPrefixFree_universalPrefix.tsum_universalProb_pair_le_one
    isLowerSemicomputable_universalProb_marginal
  refine ⟨c, fun x => ?_⟩
  have hprog : ∀ y : ℕ,
      (2 : ℝ)⁻¹ ^ universalPrefix.complexity (Nat.pair x y) ≤
        universalPrefix.universalProb (Nat.pair x y) :=
    fun y => two_inv_pow_complexity_universalPrefix_le (Nat.pair x y)
  have hsum_y := isPrefixFree_universalPrefix.summable_universalProb_pair x
  have hsum_comp : Summable fun y : ℕ =>
      (2 : ℝ)⁻¹ ^ universalPrefix.complexity (Nat.pair x y) :=
    Summable.of_nonneg_of_le (fun _ => by positivity) hprog hsum_y
  exact (hsum_comp.tsum_le_tsum hprog hsum_y).trans (hc x)

-- Combining Levin's coding theorem with binary-string symmetry of information:
-- `2⁻¹ ^ (K(x) + K(y | x*)) ≤ 2 ^ c * m(selfDelimitingCode x ++ y)`.
example :
    ∃ c : ℕ, ∀ x y : List Bool,
      (2 : ℝ)⁻¹ ^ (universalPrefixBits.complexity x +
          (condUniversalPrefixBits (shortestPrefixProgramBits x)).complexity y) ≤
        (2 : ℝ) ^ c * universalPrefixBits.universalProb (selfDelimitingCode x ++ y) := by
  obtain ⟨c₁, h₁⟩ := exists_abs_complexity_universalPrefixBits_pair_sub_shortestProgram_le
  obtain ⟨c₂, h₂⟩ := exists_abs_complexity_add_logb_universalProb_universalPrefixBits_le
  refine ⟨c₁ + c₂, fun x y => ?_⟩
  have hsym := (abs_le.mp (h₁ x y)).2
  have hlev := (abs_le.mp (h₂ (selfDelimitingCode x ++ y))).1
  have hpos := universalProb_universalPrefixBits_pos (selfDelimitingCode x ++ y)
  have hk_le : (universalPrefixBits.complexity (selfDelimitingCode x ++ y) : ℝ) ≤
      ((universalPrefixBits.complexity x +
        (condUniversalPrefixBits (shortestPrefixProgramBits x)).complexity y + c₁ : ℕ) : ℝ) := by
    exact_mod_cast (by omega : universalPrefixBits.complexity (selfDelimitingCode x ++ y) ≤
      universalPrefixBits.complexity x +
        (condUniversalPrefixBits (shortestPrefixProgramBits x)).complexity y + c₁)
  have hlog : -((universalPrefixBits.complexity (selfDelimitingCode x ++ y) : ℝ) + c₂) ≤
      Real.logb 2 (universalPrefixBits.universalProb (selfDelimitingCode x ++ y)) := by
    linarith
  have hlog2 : -((universalPrefixBits.complexity x +
        (condUniversalPrefixBits (shortestPrefixProgramBits x)).complexity y +
          (c₁ + c₂) : ℕ) : ℝ) ≤
      Real.logb 2 (universalPrefixBits.universalProb (selfDelimitingCode x ++ y)) := by
    push_cast at hk_le ⊢
    linarith
  have hrpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hlog2
  rw [Real.rpow_logb (by norm_num) (by norm_num) hpos] at hrpow
  have hpow_eq : (2 : ℝ) ^ (-((universalPrefixBits.complexity x +
      (condUniversalPrefixBits (shortestPrefixProgramBits x)).complexity y + (c₁ + c₂) : ℕ) : ℝ)) =
      (2 : ℝ)⁻¹ ^ (universalPrefixBits.complexity x +
        (condUniversalPrefixBits (shortestPrefixProgramBits x)).complexity y) *
        (2 : ℝ)⁻¹ ^ (c₁ + c₂) := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, ← inv_pow, ← pow_add]
  rw [hpow_eq] at hrpow
  calc (2 : ℝ)⁻¹ ^ (universalPrefixBits.complexity x +
        (condUniversalPrefixBits (shortestPrefixProgramBits x)).complexity y)
      = (2 : ℝ)⁻¹ ^ (universalPrefixBits.complexity x +
          (condUniversalPrefixBits (shortestPrefixProgramBits x)).complexity y) *
          ((2 : ℝ)⁻¹ * (2 : ℝ)) ^ (c₁ + c₂) := by
        rw [inv_mul_cancel₀ (by norm_num), one_pow, mul_one]
    _ = ((2 : ℝ)⁻¹ ^ (universalPrefixBits.complexity x +
          (condUniversalPrefixBits (shortestPrefixProgramBits x)).complexity y) *
          (2 : ℝ)⁻¹ ^ (c₁ + c₂)) * (2 : ℝ) ^ (c₁ + c₂) := by
        rw [mul_pow]
        ring
    _ ≤ universalPrefixBits.universalProb (selfDelimitingCode x ++ y) * (2 : ℝ) ^ (c₁ + c₂) := by
        gcongr
    _ = (2 : ℝ) ^ (c₁ + c₂) * universalPrefixBits.universalProb (selfDelimitingCode x ++ y) := by
        ring

/-! ### Conditional invariance, conditional Kraft–Chaitin, and exact symmetry clients -/

example :
    ∃ c : ℕ, ∀ y : ℕ,
      (condUniversalPrefix y).complexity y ≤ 1 + c ∧
        (condUniversalPrefix y).complexity (2 * y + 1) ≤ 1 + c := by
  let req : ℕ → ℕ → Option (ℕ × ℕ) := fun y i =>
    if i = 0 then some (1, y) else if i = 1 then some (1, 2 * y + 1) else Option.none
  have hreq : Computable₂ req := by
    have h0 : PrimrecPred fun yi : ℕ × ℕ => yi.2 = 0 :=
      Primrec.eq.comp Primrec.snd (Primrec.const 0)
    have h1 : PrimrecPred fun yi : ℕ × ℕ => yi.2 = 1 :=
      Primrec.eq.comp Primrec.snd (Primrec.const 1)
    have hr0 : Primrec fun yi : ℕ × ℕ => some (1, yi.1) :=
      Primrec.option_some.comp (Primrec.pair (Primrec.const 1) Primrec.fst)
    have hr1 : Primrec fun yi : ℕ × ℕ => some (1, 2 * yi.1 + 1) :=
      Primrec.option_some.comp <| Primrec.pair (Primrec.const 1)
        (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst)
          (Primrec.const 1))
    exact Primrec₂.to_comp
      (Primrec₂.mk <| (Primrec.ite h0 hr0 (Primrec.ite h1 hr1 (Primrec.const Option.none))).of_eq
        fun _ => rfl)
  have hbound : ∀ y n : ℕ, ∑ i ∈ Finset.range n,
      (match req y i with | Option.none => (0 : ℝ) | some (ℓ, _) => (2 : ℝ)⁻¹ ^ ℓ) ≤ 1 := by
    intro y n
    have hsplit : ∀ m : ℕ, ∑ i ∈ Finset.range m,
        (match req y i with | Option.none => (0 : ℝ) | some (ℓ, _) => (2 : ℝ)⁻¹ ^ ℓ) ≤
        ∑ i ∈ Finset.range 2,
          (match req y i with | Option.none => (0 : ℝ) | some (ℓ, _) => (2 : ℝ)⁻¹ ^ ℓ) := by
      intro m
      rcases le_or_gt m 2 with hm | hm
      · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hm) fun _ _ _ => by
          cases req y _ <;> positivity
      · have hzero : ∀ i ∈ Finset.range m, i ∉ Finset.range 2 →
            (match req y i with | Option.none => (0 : ℝ) | some (ℓ, _) => (2 : ℝ)⁻¹ ^ ℓ) = 0 := by
          intro i _ hi
          rw [Finset.mem_range, not_lt] at hi
          simp [req, show i ≠ 0 by omega, show i ≠ 1 by omega]
        exact (Finset.sum_subset_zero_on_sdiff (Finset.range_mono hm.le)
          (fun i hi => hzero i (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hi).2)
          fun _ _ => rfl).symm.le
    refine (hsplit n).trans ?_
    simp [Finset.sum_range_succ, req]
    norm_num
  obtain ⟨c, hc⟩ := condKraftChaitin_of_sum_le_one hreq hbound
  refine ⟨c, fun y => ?_⟩
  have h0 := hc y 0 1 y rfl
  have h1 := hc y 1 1 (2 * y + 1) rfl
  rw [← natCast_complexity_condUniversalPrefix] at h0 h1
  exact ⟨by exact_mod_cast h0, by exact_mod_cast h1⟩

-- Diagonal consequence of exact prefix-free symmetry of information: `K(x | x*) ≤ O(1)`.
example :
    ∃ c : ℕ, ∀ x : ℕ,
      (condUniversalPrefix (encode (shortestPrefixProgram x))).complexity x ≤ c := by
  obtain ⟨c₁, h₁⟩ := exists_abs_complexity_universalPrefix_pair_sub_shortestProgram_le
  obtain ⟨c₂, h₂⟩ := exists_complexity_universalPrefix_comp_le
    (Primrec₂.natPair.comp Primrec.id Primrec.id).to_comp
  refine ⟨c₁ + c₂, fun x => ?_⟩
  have hsym := abs_le.mp (h₁ x x)
  have hdiag : universalPrefix.complexity (Nat.pair x x) ≤ universalPrefix.complexity x + c₂ := by
    simpa using h₂ x
  omega

-- Derived self-information `|I_K(x : x) - K(x)| ≤ O(1)` plus shortest program witnesses.
example :
    (∀ x : ℕ, universalPrefix.Produces (shortestPrefixProgram x) x ∧
      (shortestPrefixProgram x).length = universalPrefix.complexity x) ∧
      (∃ c : ℕ, ∀ x : ℕ, |prefixInformation x x - (universalPrefix.complexity x : ℤ)| ≤ c) ∧
      (∃ c : ℕ, ∀ x y : ℕ, prefixInformation x y - prefixInformation y x ≤ c) := by
  refine
    ⟨fun x => ⟨universalPrefix_produces_shortestPrefixProgram x, length_shortestPrefixProgram x⟩,
      ?_, ?_⟩
  · obtain ⟨c₁, h₁⟩ := exists_abs_complexity_universalPrefix_pair_sub_shortestProgram_le
    obtain ⟨c₂, h₂⟩ := exists_complexity_universalPrefix_comp_le
      (Primrec₂.natPair.comp Primrec.id Primrec.id).to_comp
    obtain ⟨c₃, h₃⟩ := exists_abs_prefixInformation_sub_le
    refine ⟨c₁ + c₂ + c₃, fun x => ?_⟩
    have hsym := abs_le.mp (h₁ x x)
    have hdiag : universalPrefix.complexity (Nat.pair x x) ≤ universalPrefix.complexity x + c₂ := by
      simpa using h₂ x
    have hinfo := abs_le.mp (h₃ x x)
    rw [abs_le]
    constructor <;> omega
  · obtain ⟨c, hc⟩ := exists_abs_prefixInformation_symm
    exact ⟨c, fun x y => (abs_le.mp (hc x y)).2⟩

end CslibFrontierTests.LevinCodingSymmetry
