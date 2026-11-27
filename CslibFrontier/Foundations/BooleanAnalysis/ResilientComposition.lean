/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Tribes
public import CslibFrontier.Foundations.Data.BitString.Threshold
public import CslibFrontier.Probability.Resilience
import CslibFrontier.Foundations.BooleanAnalysis.Majority
import CslibFrontier.Foundations.Data.BitString.Sign

/-!
# Composed resilient functions and iterated majority

Composing an outer Boolean function `g : BitString m → Bool` with `m` block functions
`h : Fin m → BitString w → Bool` (`Cslib.BitString.composeBlocks`) preserves monotonicity and
self-duality, and characterizes coalitional undeterminedness blockwise
(`isUndetermined_composeBlocks_iff`): a coalition `Q` leaves `composeBlocks g h` undetermined at
`x` precisely when the active blocks where `tribePart Q j` leaves `h j` undetermined leave `g`
undetermined on the block outputs.

When `g = Cslib.majority 3` is the `3`-bit majority and each block function `h j` is self-dual,
uniform independence across blocks (`Cslib.BitString.expect_prod_tribe` in `Tribes`) gives the
exact composition identity
`I_Q(majority 3 ∘ (h₀, h₁, h₂)) = (p₀ + p₁ + p₂ - p₀ * p₁ * p₂) / 2 ≤ (p₀ + p₁ + p₂) / 2` where
`pⱼ = I_{Qⱼ}(hⱼ)` (`Cslib.BitString.coalitionInfluence_composeBlocks_maj3`). Iterating this
`d` times yields the Ben-Or–Linial iterated `3`-majority `iterMaj3 d` on `3 ^ d` bits: it is
monotone, self-dual, exactly balanced (`1 / 2`), and `(q, q / 2 ^ d)`-resilient for every `q`
(`Cslib.BitString.isResilient_iterMaj3`), i.e. `I_q ≤ q / n ^ (log₂ 3)⁻¹ ≈ q / n ^ 0.63`
without `tribes`'s `q < log n` threshold barrier
[Chattopadhyay–Zuckerman][ChattopadhyayZuckerman2019].

## Main definitions

* `Cslib.BitString.composeBlocks`: block composition `g ∘ (h₀, ..., h_{m-1})` on
  `BitString (m * w)`.
* `Cslib.BitString.iterMaj3`: depth-`d` iterated `3`-majority on `BitString (3 ^ d)`.

## Main results

* `Cslib.BitString.monotone_composeBlocks`, `Cslib.BitString.isUndetermined_composeBlocks_iff`:
  structural laws for block composition.
* `Cslib.BitString.coalitionInfluence_composeBlocks_maj3`: exact resilience recursion for
  `Cslib.majority 3` composed with self-dual blocks.
* `Cslib.BitString.monotone_iterMaj3`, `Cslib.BitString.iterMaj3_not`,
  `Cslib.BitString.expect_bitVal_iterMaj3`, `Cslib.BitString.isResilient_iterMaj3`: monotonicity,
  self-duality, exact balance, and `(q, q / 2 ^ d)`-resilience of `iterMaj3 d`.

## References

* [E. Chattopadhyay, D. Zuckerman, *Explicit two-source extractors and resilient
  functions*][ChattopadhyayZuckerman2019]
* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset Function Probability
open scoped BigOperators

/-! ### Block composition -/

/-- Block composition `g (h₀(x₀), ..., h_{m-1}(x_{m-1}))` on `BitString (m * w)`, where the `j`-th
block takes bits at indices `finProdFinEquiv (j, i)`. -/
@[expose] def composeBlocks {m w : ℕ} (g : BitString m → Bool)
    (h : Fin m → BitString w → Bool) (x : BitString (m * w)) : Bool :=
  g fun j => h j fun i => x (finProdFinEquiv (j, i))

/-- Block composition preserves monotonicity. -/
theorem monotone_composeBlocks {m w : ℕ} {g : BitString m → Bool} {h : Fin m → BitString w → Bool}
    (hg : Monotone g) (hh : ∀ j, Monotone (h j)) : Monotone (composeBlocks g h) :=
  fun _ _ hxy => hg fun j => hh j fun i => hxy (finProdFinEquiv (j, i))

/-- Block composition preserves self-duality (`f (fun i => !x i) = !f x`). -/
theorem composeBlocks_not_of_selfDual {m w : ℕ} {g : BitString m → Bool}
    {h : Fin m → BitString w → Bool} (hg : ∀ v, g (fun j => !v j) = !g v)
    (hh : ∀ j u, h j (fun i => !u i) = !h j u) (x : BitString (m * w)) :
    composeBlocks g h (fun k => !x k) = !composeBlocks g h x := by
  simp only [composeBlocks, hh, hg]

/-- Coalition undeterminedness for `composeBlocks g h`: `Q` leaves the composed function
undetermined at `x` if and only if the set of blocks where `tribePart Q j` leaves `h j`
undetermined leaves `g` undetermined on the block outputs. -/
theorem isUndetermined_composeBlocks_iff {m w : ℕ} (g : BitString m → Bool)
    (h : Fin m → BitString w → Bool) (Q : Finset (Fin (m * w))) (x : BitString (m * w)) :
    IsUndetermined Q (composeBlocks g h) x ↔
      IsUndetermined
        (univ.filter fun j =>
          IsUndetermined (tribePart Q j) (h j) fun i => x (finProdFinEquiv (j, i)))
        g fun j => h j fun i => x (finProdFinEquiv (j, i)) := by
  constructor
  · rintro ⟨y, z, hy, hz, hne⟩
    have agree (u : BitString (m * w)) (hu : ∀ k ∉ Q, u k = x k) (j : Fin m)
        (hj : j ∉ univ.filter fun j =>
          IsUndetermined (tribePart Q j) (h j) fun i => x (finProdFinEquiv (j, i))) :
        h j (fun i => u (finProdFinEquiv (j, i))) =
          h j (fun i => x (finProdFinEquiv (j, i))) :=
      not_ne_iff.mp fun hdiff => hj (mem_filter.mpr ⟨mem_univ j,
        fun i => u (finProdFinEquiv (j, i)), fun i => x (finProdFinEquiv (j, i)),
        fun i hi => hu _ (by simpa [mem_tribePart] using hi), fun _ _ => rfl, hdiff⟩)
    exact ⟨fun j => h j fun i => y (finProdFinEquiv (j, i)),
      fun j => h j fun i => z (finProdFinEquiv (j, i)),
      agree y hy, agree z hz, hne⟩
  · rintro ⟨a, b, ha, hb, hne⟩
    have pick (u : Fin m → Bool)
        (hu : ∀ j, ¬IsUndetermined (tribePart Q j) (h j) (fun i => x (finProdFinEquiv (j, i))) →
          u j = h j fun i => x (finProdFinEquiv (j, i))) :
        ∃ y : BitString (m * w), (∀ k ∉ Q, y k = x k) ∧
          ∀ j, h j (fun i => y (finProdFinEquiv (j, i))) = u j := by
      have hexj (j : Fin m) : ∃ v : BitString w,
          (∀ i ∉ tribePart Q j, v i = x (finProdFinEquiv (j, i))) ∧ h j v = u j := by
        by_cases hj : IsUndetermined (tribePart Q j) (h j) fun i => x (finProdFinEquiv (j, i))
        · obtain ⟨y₀, z₀, hy₀, hz₀, hdiff⟩ := hj
          exact if h1 : h j y₀ = u j then ⟨y₀, hy₀, h1⟩ else ⟨z₀, hz₀,
            (Bool.eq_not_of_ne (Ne.symm hdiff)).trans (Bool.eq_not_of_ne (Ne.symm h1)).symm⟩
        · exact ⟨fun i => x (finProdFinEquiv (j, i)), fun _ _ => rfl, (hu j hj).symm⟩
      choose v hv_agree hv_val using hexj
      refine ⟨fun k => v (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2, fun k hk => ?_,
        fun j => by simp only [Equiv.symm_apply_apply, hv_val]⟩
      obtain ⟨⟨j, i⟩, rfl⟩ := finProdFinEquiv.surjective k
      simpa only [Equiv.symm_apply_apply] using
        hv_agree j i (by simpa [mem_tribePart] using hk)
    obtain ⟨y, hyQ, hy_val⟩ := pick a fun j hj => ha j (by simp [hj])
    obtain ⟨z, hzQ, hz_val⟩ := pick b fun j hj => hb j (by simp [hj])
    exact ⟨y, z, hyQ, hzQ, by simpa only [composeBlocks, hy_val, hz_val] using hne⟩

/-! ### Self-dual functions and `3`-majority composition -/

section SelfDual

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
private theorem isUndetermined_compl (Q : Finset ι) {f : (ι → Bool) → Bool}
    (hf : ∀ x, f (fun i => !x i) = !f x) (x : ι → Bool) :
    IsUndetermined Q f (fun i => !x i) ↔ IsUndetermined Q f x := by
  have hstep : ∀ x, IsUndetermined Q f x → IsUndetermined Q f (fun i => !x i) := by
    rintro x ⟨y, z, hy, hz, hne⟩
    refine ⟨fun i => !y i, fun i => !z i,
      fun i hi => congrArg (!·) (hy i hi),
      fun i hi => congrArg (!·) (hz i hi), by simpa only [hf] using mt Bool.not_inj hne⟩
  exact ⟨fun h => by simpa only [Bool.not_not] using hstep _ h, hstep x⟩

private theorem expect_not_isUndetermined_symm {f : (ι → Bool) → Bool}
    (hf : ∀ x, f (fun i => !x i) = !f x) (Q : Finset ι) :
    𝔼 x, (if ¬IsUndetermined Q f x ∧ f x = true then (1 : ℝ) else 0) =
      𝔼 x, (if ¬IsUndetermined Q f x ∧ f x = false then (1 : ℝ) else 0) := by
  refine Fintype.expect_equiv ⟨fun x i => !x i, fun x i => !x i,
    fun x => funext fun i => Bool.not_not (x i),
    fun x => funext fun i => Bool.not_not (x i)⟩ _ _ fun x => ?_
  simp [isUndetermined_compl Q hf x, hf x]

/-- For a self-dual function, the uniform probabilities of being determined as `true` or as
`false` outside `Q` are both `(1 - I_Q(f)) / 2`. -/
theorem expect_not_isUndetermined_and_eq_true {f : (ι → Bool) → Bool}
    (hf : ∀ x, f (fun i => !x i) = !f x) (Q : Finset ι) :
    𝔼 x, (if ¬IsUndetermined Q f x ∧ f x = true then (1 : ℝ) else 0) =
      (1 - coalitionInfluence (PMF.uniformOfFintype (ι → Bool)) Q f) / 2 := by
  have hsum : (𝔼 x, (if ¬IsUndetermined Q f x ∧ f x = true then (1 : ℝ) else 0)) +
      (𝔼 x, (if ¬IsUndetermined Q f x ∧ f x = false then (1 : ℝ) else 0)) =
      1 - coalitionInfluence (PMF.uniformOfFintype (ι → Bool)) Q f := by
    rw [← expect_add_distrib, coalitionInfluence_uniformOfFintype]
    have hpt (x : ι → Bool) :
        (if ¬IsUndetermined Q f x ∧ f x = true then (1 : ℝ) else 0) +
          (if ¬IsUndetermined Q f x ∧ f x = false then (1 : ℝ) else 0) =
        1 - if IsUndetermined Q f x then (1 : ℝ) else 0 := by
      by_cases hu : IsUndetermined Q f x <;> cases f x <;> simp [hu]
    simp_rw [hpt, expect_sub_distrib, expect_const univ_nonempty]
  linarith [expect_not_isUndetermined_symm hf Q]

/-- Same as `expect_not_isUndetermined_and_eq_true` for determined `false` outcomes. -/
theorem expect_not_isUndetermined_and_eq_false {f : (ι → Bool) → Bool}
    (hf : ∀ x, f (fun i => !x i) = !f x) (Q : Finset ι) :
    𝔼 x, (if ¬IsUndetermined Q f x ∧ f x = false then (1 : ℝ) else 0) =
      (1 - coalitionInfluence (PMF.uniformOfFintype (ι → Bool)) Q f) / 2 :=
  (expect_not_isUndetermined_symm hf Q).symm.trans (expect_not_isUndetermined_and_eq_true hf Q)

/-- Every self-dual function is balanced (`𝔼 bitVal = 1 / 2`). -/
theorem expect_bitVal_eq_half_of_selfDual {f : (ι → Bool) → Bool}
    (hf : ∀ x, f (fun i => !x i) = !f x) :
    𝔼 x, bitVal ℝ (f x) = 1 / 2 := by
  have h0 : ∀ x, ¬IsUndetermined (∅ : Finset ι) f x := by
    rintro x ⟨y, z, hy, hz, hne⟩
    exact hne (congrArg f ((funext fun i => hy i (notMem_empty i)).trans
      (funext fun i => hz i (notMem_empty i)).symm))
  simpa [h0, coalitionInfluence_eq_zero_of_forall_not _ h0, bitVal] using
    expect_not_isUndetermined_and_eq_true hf ∅

end SelfDual

private theorem isUndetermined_maj3_classify (S : Finset (Fin 3)) (v : BitString 3) :
    IsUndetermined S (majority 3) v ↔
      2 ≤ #S ∨ (S = {0} ∧ v 1 ≠ v 2) ∨ (S = {1} ∧ v 0 ≠ v 2) ∨ (S = {2} ∧ v 0 ≠ v 1) := by
  revert S v
  decide

private def nInd (b : Bool) : ℕ := if b then 1 else 0

private theorem maj3_split_nat (d : Fin 3 → Bool) (b0 b1 b2 : Bool) :
    (if 2 ≤ #(univ.filter fun j => d j = true) ∨
        (univ.filter (fun j => d j = true) = {0} ∧ b1 ≠ b2) ∨
        (univ.filter (fun j => d j = true) = {1} ∧ b0 ≠ b2) ∨
        (univ.filter (fun j => d j = true) = {2} ∧ b0 ≠ b1) then (1 : ℕ) else 0) =
      nInd (d 0) * nInd (d 1) * nInd (d 2) +
      nInd (d 0) * nInd (d 1) * nInd (!d 2) +
      nInd (d 0) * nInd (!d 1) * nInd (d 2) +
      nInd (!d 0) * nInd (d 1) * nInd (d 2) +
      nInd (d 0) * nInd (!d 1 && b1) * nInd (!d 2 && !b2) +
      nInd (d 0) * nInd (!d 1 && !b1) * nInd (!d 2 && b2) +
      nInd (!d 0 && b0) * nInd (d 1) * nInd (!d 2 && !b2) +
      nInd (!d 0 && !b0) * nInd (d 1) * nInd (!d 2 && b2) +
      nInd (!d 0 && b0) * nInd (!d 1 && !b1) * nInd (d 2) +
      nInd (!d 0 && !b0) * nInd (!d 1 && b1) * nInd (d 2) := by
  obtain ⟨d0, d1, d2, rfl⟩ : ∃ d0 d1 d2, d = ![d0, d1, d2] :=
    ⟨d 0, d 1, d 2, funext fun j => by fin_cases j <;> rfl⟩
  revert d0 d1 d2 b0 b1 b2
  decide

/-- **Exact `3`-majority coalition-influence composition identity**: composing `Cslib.majority 3`
with three self-dual block functions `h₀, h₁, h₂` yields coalition influence
`(p₀ + p₁ + p₂ - p₀ * p₁ * p₂) / 2 ≤ (p₀ + p₁ + p₂) / 2`, where `pⱼ = I_{Qⱼ}(hⱼ)`. -/
theorem coalitionInfluence_composeBlocks_maj3 {w : ℕ} (h : Fin 3 → BitString w → Bool)
    (hh : ∀ j u, h j (fun i => !u i) = !h j u) (Q : Finset (Fin (3 * w))) :
    coalitionInfluence (PMF.uniformOfFintype (BitString (3 * w))) Q
        (composeBlocks (majority 3) h) =
      let p j := coalitionInfluence (PMF.uniformOfFintype (BitString w)) (tribePart Q j) (h j)
      (p 0 + p 1 + p 2 - p 0 * p 1 * p 2) / 2 := by
  dsimp only
  let p (j : Fin 3) :=
    coalitionInfluence (PMF.uniformOfFintype (BitString w)) (tribePart Q j) (h j)
  let eU (j : Fin 3) (u : BitString w) : ℝ :=
    if IsUndetermined (tribePart Q j) (h j) u then 1 else 0
  let eD (j : Fin 3) (u : BitString w) : ℝ :=
    if ¬IsUndetermined (tribePart Q j) (h j) u then 1 else 0
  let eT (j : Fin 3) (u : BitString w) : ℝ :=
    if ¬IsUndetermined (tribePart Q j) (h j) u ∧ h j u = true then 1 else 0
  let eF (j : Fin 3) (u : BitString w) : ℝ :=
    if ¬IsUndetermined (tribePart Q j) (h j) u ∧ h j u = false then 1 else 0
  have heU (j : Fin 3) : 𝔼 u : BitString w, eU j u = p j :=
    (coalitionInfluence_uniformOfFintype (tribePart Q j) (h j)).symm
  have heD (j : Fin 3) : 𝔼 u : BitString w, eD j u = 1 - p j := by
    have hpt (u : BitString w) : eD j u = 1 - eU j u := by
      by_cases hu : IsUndetermined (tribePart Q j) (h j) u <;> simp [eD, eU, hu]
    simp_rw [hpt, expect_sub_distrib, expect_const univ_nonempty, heU]
  have heT (j : Fin 3) : 𝔼 u : BitString w, eT j u = (1 - p j) / 2 :=
    expect_not_isUndetermined_and_eq_true (hh j) (tribePart Q j)
  have heF (j : Fin 3) : 𝔼 u : BitString w, eF j u = (1 - p j) / 2 :=
    expect_not_isUndetermined_and_eq_false (hh j) (tribePart Q j)
  let sl (x : BitString (3 * w)) (j : Fin 3) : BitString w :=
    fun i => x (finProdFinEquiv (j, i))
  have hsplit (x : BitString (3 * w)) :
      (if IsUndetermined Q (composeBlocks (majority 3) h) x then (1 : ℝ) else 0) =
        eU 0 (sl x 0) * eU 1 (sl x 1) * eU 2 (sl x 2) +
        eU 0 (sl x 0) * eU 1 (sl x 1) * eD 2 (sl x 2) +
        eU 0 (sl x 0) * eD 1 (sl x 1) * eU 2 (sl x 2) +
        eD 0 (sl x 0) * eU 1 (sl x 1) * eU 2 (sl x 2) +
        eU 0 (sl x 0) * eT 1 (sl x 1) * eF 2 (sl x 2) +
        eU 0 (sl x 0) * eF 1 (sl x 1) * eT 2 (sl x 2) +
        eT 0 (sl x 0) * eU 1 (sl x 1) * eF 2 (sl x 2) +
        eF 0 (sl x 0) * eU 1 (sl x 1) * eT 2 (sl x 2) +
        eT 0 (sl x 0) * eF 1 (sl x 1) * eU 2 (sl x 2) +
        eF 0 (sl x 0) * eT 1 (sl x 1) * eU 2 (sl x 2) := by
    rw [if_congr (isUndetermined_composeBlocks_iff (majority 3) h Q x) rfl rfl,
      if_congr (isUndetermined_maj3_classify _ _) rfl rfl]
    let D (j : Fin 3) : Bool := decide (IsUndetermined (tribePart Q j) (h j) (sl x j))
    simpa only [eU, eD, eT, eF, nInd, D, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_true_eq, decide_eq_false_iff_not, Nat.cast_add, Nat.cast_mul, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero] using
      congrArg (Nat.cast (R := ℝ)) (maj3_split_nat D (h 0 (sl x 0)) (h 1 (sl x 1)) (h 2 (sl x 2)))
  have hprod (f0 f1 f2 : BitString w → ℝ) :
      𝔼 x : BitString (3 * w), f0 (sl x 0) * f1 (sl x 1) * f2 (sl x 2) =
        (𝔼 u, f0 u) * (𝔼 u, f1 u) * (𝔼 u, f2 u) := by
    simpa [Fin.prod_univ_three] using expect_prod_tribe ![f0, f1, f2]
  rw [coalitionInfluence_uniformOfFintype]
  simp_rw [hsplit, expect_add_distrib, hprod, heU, heD, heT, heF]
  ring

/-! ### Iterated `3`-majority (`iterMaj3`) -/

/-- Ben-Or–Linial iterated `3`-majority on `3 ^ d` bits: at depth `0`, a single coordinate bit; at
depth `d + 1`, `Cslib.majority 3` composed over three independent copies of `iterMaj3 d`. -/
@[expose] def iterMaj3 : (d : ℕ) → BitString (3 ^ d) → Bool
  | 0, x => x 0
  | d + 1, x =>
    composeBlocks (majority 3) (fun _ => iterMaj3 d)
      fun k => x (k.cast (@Nat.pow_succ' 3 d).symm)

/-- `iterMaj3 d` is monotone. -/
theorem monotone_iterMaj3 (d : ℕ) : Monotone (iterMaj3 d) := by
  induction d with
  | zero => exact fun x y hxy => hxy 0
  | succ d ih =>
    exact fun _ _ hxy => monotone_composeBlocks monotone_majority (fun _ => ih) fun k =>
      hxy (k.cast (@Nat.pow_succ' 3 d).symm)

/-- `iterMaj3 d` is self-dual. -/
theorem iterMaj3_not (d : ℕ) (x : BitString (3 ^ d)) :
    iterMaj3 d (fun i => !x i) = !iterMaj3 d x := by
  induction d with
  | zero => rfl
  | succ d ih =>
    exact composeBlocks_not_of_selfDual (majority_not 1) (fun _ => ih) _

/-- `iterMaj3 d` is balanced: `𝔼 bitVal = 1 / 2`. -/
theorem expect_bitVal_iterMaj3 (d : ℕ) :
    𝔼 x : BitString (3 ^ d), bitVal ℝ (iterMaj3 d x) = 1 / 2 :=
  expect_bitVal_eq_half_of_selfDual (iterMaj3_not d)

private theorem coalitionInfluence_comp_finCast {m n : ℕ} (h : m = n)
    (f : BitString n → Bool) (Q : Finset (Fin m)) :
    coalitionInfluence (PMF.uniformOfFintype (BitString m)) Q
      (fun x => f fun k => x (k.cast h.symm)) =
      coalitionInfluence (PMF.uniformOfFintype (BitString n))
        (Q.map (Fin.castOrderIso h).toEquiv.toEmbedding) f := by
  subst h
  exact congrArg (coalitionInfluence _ · f) (Finset.ext fun _ => by simp)

/-- Every coalition `Q` has uniform influence at most `|Q| / 2 ^ d` on `iterMaj3 d`. -/
theorem coalitionInfluence_iterMaj3_le (d : ℕ) (Q : Finset (Fin (3 ^ d))) :
    coalitionInfluence (PMF.uniformOfFintype (BitString (3 ^ d))) Q (iterMaj3 d) ≤
      (#Q : ℝ) / 2 ^ d := by
  induction d with
  | zero =>
    dsimp only [iterMaj3]
    by_cases h0 : (0 : Fin (3 ^ 0)) ∈ Q
    · exact (coalitionInfluence_le_one _ _ _).trans <|
        (by exact_mod_cast card_pos.mpr ⟨0, h0⟩ : (1 : ℝ) ≤ #Q).trans_eq (by norm_num)
    · rw [coalitionInfluence_eq_zero_of_forall_not _
        fun _ ⟨_, _, hy, hz, hne⟩ => hne ((hy 0 h0).trans (hz 0 h0).symm)]
      positivity
  | succ d ih =>
    let Q' : Finset (Fin (3 * 3 ^ d)) :=
      Q.map (Fin.castOrderIso (@Nat.pow_succ' 3 d)).toEquiv.toEmbedding
    dsimp only [iterMaj3]
    rw [coalitionInfluence_comp_finCast (@Nat.pow_succ' 3 d) _ Q,
      coalitionInfluence_composeBlocks_maj3 _ (fun _ => iterMaj3_not d) Q']
    let p (j : Fin 3) :=
      coalitionInfluence (PMF.uniformOfFintype (BitString (3 ^ d))) (tribePart Q' j) (iterMaj3 d)
    have hp_prod : 0 ≤ p 0 * p 1 * p 2 := mul_nonneg
      (mul_nonneg (coalitionInfluence_nonneg ..) (coalitionInfluence_nonneg ..))
      (coalitionInfluence_nonneg ..)
    have hQ : #Q = ∑ j : Fin 3, #(tribePart Q' j) :=
      (card_map _).symm.trans (card_eq_sum_card_tribePart Q')
    calc (p 0 + p 1 + p 2 - p 0 * p 1 * p 2) / 2
        ≤ ((#(tribePart Q' 0) : ℝ) / 2 ^ d + (#(tribePart Q' 1) : ℝ) / 2 ^ d +
            (#(tribePart Q' 2) : ℝ) / 2 ^ d) / 2 := by
          linarith [ih (tribePart Q' 0), ih (tribePart Q' 1), ih (tribePart Q' 2)]
      _ = (#Q : ℝ) / 2 ^ (d + 1) := by
          rw [hQ, Fin.sum_univ_three, pow_succ]; push_cast; ring

/-- **Ben-Or–Linial iterated `3`-majority resilience**: `iterMaj3 d` on `3 ^ d` bits is
`(q, q / 2 ^ d)`-resilient for every `q : ℕ`. -/
theorem isResilient_iterMaj3 (d q : ℕ) : IsResilient q (q / 2 ^ d) (iterMaj3 d) :=
  fun Q hQ => hQ ▸ coalitionInfluence_iterMaj3_le d Q

end Cslib.BitString
