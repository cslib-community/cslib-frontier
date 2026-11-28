/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.LinearAlgebra.Tensor.Party.Price.Basic
public import CslibFrontier.Foundations.LinearAlgebra.Tensor.Party.Extension
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Random pull-backs of prices

Proposition A.8 (prop:random) of *VP ≠ VNP over every field* [AnthropicVPVNP2026]. Let `w` be a
price on `Y`, let `Q` be a further set of parties, and let `σ` be a random map from `Q` to `Y` with
finitely many values. Then some price on `Y ⊕ Q` extends `w` and is at most the expectation of `w`
pulled back along `σ` (`Cslib.PartyTensor.IsPrice.exists_extend_random`). The case of finitely many
values `σ l` with probabilities `θ l` is `Cslib.PartyTensor.IsPrice.exists_extend_of_weights`. The
proof extends the spectral points with `Cslib.PartyTensor.SpectralPoint.exists_extend` and takes a
limit in the compact set of prices below a bound.

## Main results

* `Cslib.PartyTensor.SpectralPoint.exists_extend_keep`: Proposition A.7 for moves of new parties,
  keeping the wire exponents and the value at a tensor.
* `Cslib.PartyTensor.IsPrice.exists_extend_random`,
  `Cslib.PartyTensor.IsPrice.exists_extend_of_weights`.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Proposition A.8 of the paper; module `Paper.Prices` (from `prop_random` on)
-/

public section

namespace Cslib.PartyTensor

open Finset Filter MeasureTheory

variable {K : Type} [Field K]

section Spectral

variable {P Q : Type} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]

/-- Proposition A.7 for the moves `Sum.elim id (σ l)` of new parties `Q` to the parties `P`, with
weights `θ l`: a spectral point `F` over `P` extends to `F'` over `P ⊕ Q` that is at most the
weighted geometric mean of the moved values, keeps the wire exponents on `P` and the value at a
tensor `C` with `0 < F C`. Then every wire exponent of `F'` is at most the weighted mean of the
moved ones. (Applied to the product `W * C` of all wires `⟨2⟩_uv`, `u, v ∈ P`, and `C`: on `P`,
`d_F' ≤ d_F` with equality for the sum over all pairs, hence for each.) -/
theorem SpectralPoint.exists_extend_keep (F : SpectralPoint K P) {m : ℕ} (θ : Fin m → ℝ)
    (hθ : ∀ l, 0 ≤ θ l) (hθ1 : ∑ l, θ l = 1) (σ : Fin m → Q → P) (C : PartyTensor K P)
    (hC : 0 < F C) :
    ∃ F' : SpectralPoint K (P ⊕ Q),
      (∀ t, F' t ≤ ∏ l, F (push (Sum.elim id (σ l)) t) ^ θ l) ∧
      (∀ a b, F'.wireExponent a b ≤ ∑ l,
          θ l * F.wireExponent (Sum.elim id (σ l) a) (Sum.elim id (σ l) b)) ∧
      (∀ p p', F'.wireExponent (Sum.inl p) (Sum.inl p') = F.wireExponent p p') ∧
      F' (push Sum.inl C) = F C := by
  classical
  set W : PartyTensor K P := prod fun e : P × P => wire K 2 e.1 e.2 with hW
  obtain ⟨F', hle, hWC⟩ := SpectralPoint.exists_extend (K := K) (Sum.inl : P → P ⊕ Q)
    (fun l => Sum.elim id (σ l)) (fun l i => rfl) θ hθ hθ1 F (W * C)
  -- on tensors over `P` the extension is not larger
  have hA (A : PartyTensor K P) (h0 : 0 < F A) : F' (push Sum.inl A) ≤ F A := by
    refine (hle _).trans_eq ?_
    have h1 (l : Fin m) : F (push (Sum.elim id (σ l)) (push Sum.inl A)) = F A :=
      F.congr ((antisymmRel_push_push _ _ A).trans (antisymmRel_push_id A))
    simp only [h1]
    rw [← Real.rpow_sum_of_pos h0, hθ1, Real.rpow_one]
  have hW0 : 0 < F W := by
    rw [hW, F.map_prod]
    exact Finset.prod_pos fun e _ => by rw [F.apply_wire_two]; positivity
  rw [F'.congr (antisymmRel_push_mul _ W C), F'.map_mul, F.map_mul] at hWC
  have h1 := hA W hW0
  have h2 := hA C hC
  have hC' : F' (push Sum.inl C) = F C := by
    refine le_antisymm h2 (not_lt.1 fun hlt => ?_)
    exact (lt_of_le_of_lt (mul_le_mul_of_nonneg_right h1 (F'.nonneg _))
      (mul_lt_mul_of_pos_left hlt hW0)).ne hWC
  have hW' : F' (push Sum.inl W) = F W := by
    rw [hC'] at hWC
    exact mul_right_cancel₀ hC.ne' hWC
  have hb (a b : P ⊕ Q) : F'.wireExponent a b ≤ ∑ l,
      θ l * F.wireExponent (Sum.elim id (σ l) a) (Sum.elim id (σ l) b) := by
    have h1 := hle (wire K 2 a b)
    have h2 (l : Fin m) : F (push (Sum.elim id (σ l)) (wire K 2 a b)) =
        2 ^ F.wireExponent (Sum.elim id (σ l) a) (Sum.elim id (σ l) b) := by
      rw [← F.pull_apply, (F.pull _).apply_wire_two, F.pull_wireExponent]
    simp only [h2] at h1
    rw [F'.apply_wire_two] at h1
    have h3 : ∏ l, ((2 : ℝ) ^ F.wireExponent (Sum.elim id (σ l) a) (Sum.elim id (σ l) b)) ^ θ l =
        2 ^ ∑ l, θ l * F.wireExponent (Sum.elim id (σ l) a) (Sum.elim id (σ l) b) := by
      rw [Real.rpow_sum_of_pos (by norm_num)]
      refine Finset.prod_congr rfl fun l _ => ?_
      rw [← Real.rpow_mul (by norm_num), mul_comm]
    rw [h3] at h1
    exact (Real.rpow_le_rpow_left_iff (by norm_num)).1 h1
  refine ⟨F', hle, hb, ?_, hC'⟩
  have hle' (p p' : P) : F'.wireExponent (Sum.inl p) (Sum.inl p') ≤ F.wireExponent p p' :=
    (hb _ _).trans_eq (by simp only [Sum.elim_inl, id]; rw [← Finset.sum_mul, hθ1, one_mul])
  have hsum : ∑ e : P × P, F'.wireExponent (Sum.inl e.1) (Sum.inl e.2) = ∑ e : P × P,
      F.wireExponent e.1 e.2 := by
    rw [← F'.pull_apply, hW, (F'.pull _).map_prod, F.map_prod] at hW'
    simp only [SpectralPoint.apply_wire_two, SpectralPoint.pull_wireExponent] at hW'
    rw [← Real.rpow_sum_of_pos (by norm_num), ← Real.rpow_sum_of_pos (by norm_num)] at hW'
    have h2 := congrArg (Real.logb 2) hW'
    rwa [Real.logb_rpow (by norm_num) (by norm_num), Real.logb_rpow (by norm_num) (by norm_num)]
      at h2
  exact fun p p' => (Finset.sum_eq_sum_iff_of_le fun (e : P × P) _ => hle' e.1 e.2).1 hsum (p, p')
    (Finset.mem_univ _)

end Spectral

section Random

/-- Proof of Proposition A.8, the reduction to finite sets: it is enough to find, for all finite
`Y₀ ⊆ Y` and `Q₀ ⊆ Q` such that `σ` maps `Q₀` into `Y₀`, a price on `Y₀ ∪ Q₀` with the two
properties. These prices form compact sets, so one of them works for all at once. Here `Z` is
`Y ∪ Q`, the two properties are bounds `A ≤ |oo'| ≤ B`, and the compact sets are those of
`isCompact_setOf_isPrice_le K`. -/
private theorem prop_random_compact {Z : Type*} (A B : Z → Z → ℝ)
    (h : ∀ S : Finset Z, ∃ d : S → S → ℝ, IsPrice K d ∧ ∀ a b : S, A a b ≤ d a b ∧ d a b ≤ B a b) :
    ∃ w' : Z → Z → ℝ, IsPrice K w' ∧ ∀ a b, A a b ≤ w' a b ∧ w' a b ≤ B a b := by
  classical
  choose d hd hAB using h
  -- the price on T, as a function on all pairs
  let D : Finset Z → Z → Z → ℝ := fun T a b => if h : a ∈ T ∧
      b ∈ T then d T ⟨a, h.1⟩ ⟨b, h.2⟩ else 0
  have hD : ∀ {S T : Finset Z} (hT : S ⊆ T) (a b : S),
      D T a b = d T ⟨a, hT a.property⟩ ⟨b, hT b.property⟩ :=
    fun hT a b => dite_eq_left ⟨hT a.property, hT b.property⟩
  let U : Ultrafilter (Finset Z) := Ultrafilter.of atTop
  have hmem : ∀ S : Finset Z, ∀ᶠ T in (U : Filter (Finset Z)), S ⊆ T := fun S =>
    Ultrafilter.of_le _ (eventually_ge_atTop S)
  -- on every finite set S the restrictions have a limit, in the compact set of the prices on
  -- S below B
  have key : ∀ S : Finset Z, ∃ v : S → S → ℝ, (IsPrice K v ∧ ∀ a b : S, v a b ≤ B a b) ∧
      ∀ a b : S, Tendsto (fun T => D T a b) U (nhds (v a b)) := by
    intro S
    obtain ⟨v, hv, hlim⟩ := (isCompact_setOf_isPrice_le K fun a b : S => B a b).ultrafilter_le_nhds
      (U.map fun T (a b : S) => D T a b) (by
        rw [le_principal_iff, Ultrafilter.coe_map, Filter.mem_map]
        filter_upwards [hmem S] with T hT
        refine ⟨?_, fun a b => (hD hT a b).le.trans (hAB T _ _).2⟩
        change IsPrice K fun a b : S => D T a b
        rw [funext₂ fun a b => hD hT a b]
        exact IsPrice.comp (hd T) fun a : S => (⟨a, hT a.property⟩ : T))
    have h1 : Tendsto (fun T (a b : S) => D T a b) U (nhds v) := hlim
    exact ⟨v, hv, fun a b => tendsto_pi_nhds.1 (tendsto_pi_nhds.1 h1 a) b⟩
  choose v hv hlim using key
  have ha : ∀ a b : Z, a ∈ ({a, b} : Finset Z) := fun a b => by simp
  have hb : ∀ a b : Z, b ∈ ({a, b} : Finset Z) := fun a b => by simp
  -- the limits fit together
  have hfit : ∀ (S : Finset Z) (a b : S),
      v S a b = v {a.val, b.val} ⟨a, ha _ _⟩ ⟨b, hb _ _⟩ := fun S a b =>
    tendsto_nhds_unique (hlim S a b) (hlim {a.val, b.val} ⟨a, ha _ _⟩ ⟨b, hb _ _⟩)
  refine ⟨fun a b => v {a, b} ⟨a, ha _ _⟩ ⟨b, hb _ _⟩, isPrice_of_finset fun S => ?_,
      fun a b => ⟨?_, ?_⟩⟩
  · rw [show (fun a b : S => v {a.val, b.val} ⟨a, ha _ _⟩ ⟨b, hb _ _⟩) = v S from
      funext₂ fun a b => (hfit S a b).symm]
    exact (hv S).1
  · refine ge_of_tendsto (hlim {a, b} ⟨a, ha _ _⟩ ⟨b, hb _ _⟩) ?_
    filter_upwards [hmem {a, b}] with T hT
    exact ((hAB T _ _).1.trans (hD hT ⟨a, ha _ _⟩ ⟨b, hb _ _⟩).ge :)
  · exact (hv {a, b}).2 ⟨a, ha _ _⟩ ⟨b, hb _ _⟩

/-- Proof of Proposition A.8, the finite case: `Y` and `Q` are finite and `σ` takes the values `π_l`
with probabilities `θ_l`. By a limit, `w = s · d_φ`, and then `s = 1` by homogeneity: the prices
that `SpectralPoint.exists_extend_keep` gives for approximations `s · d_φ` of `w` have a limit,
since they lie in a compact set (`isCompact_setOf_isPrice_le K`). -/
private theorem prop_random_limit {P Q : Type} [Finite P] [Finite Q] {w : P → P → ℝ}
    (hw : IsPrice K w) {m : ℕ} (θ : Fin m → ℝ) (hθ : ∀ l, 0 ≤ θ l) (hθ1 : ∑ l, θ l = 1)
        (σ : Fin m → Q → P) :
    ∃ w' : P ⊕ Q → P ⊕ Q → ℝ, IsPrice K w' ∧ (∀ p p', w' (Sum.inl p) (Sum.inl p') = w p p') ∧
      ∀ a b, w' a b ≤ ∑ l, θ l * w (Sum.elim id (σ l) a) (Sum.elim id (σ l) b) := by
  have := Fintype.ofFinite P
  have := Fintype.ofFinite Q
  classical
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / (n + 1) := fun n => by positivity
  have hle1 : ∀ n : ℕ, (1 : ℝ) / (n + 1) ≤ 1 := fun n => div_le_one_of_le₀ (by simp) (by positivity)
  -- w is s·d_φ up to 1/(n+1)
  choose φ s hs hφ using fun n : ℕ => hw.exists_spectralPoint (id : P → P) (hpos n)
  choose φ' _ h2 h1 _ using fun n => (φ n).exists_extend_keep θ hθ hθ1 σ
    (prod fun e : P × P => wire K 2 e.1 e.2)
    (by
      rw [(φ n).map_prod]
      exact Finset.prod_pos fun e _ => by rw [(φ n).apply_wire_two]; positivity)
  let B : P ⊕ Q → P ⊕ Q → ℝ := fun a b => ∑ l, θ l * w (Sum.elim id (σ l) a) (Sum.elim id (σ l) b)
  let d : ℕ → P ⊕ Q → P ⊕ Q → ℝ := fun n a b => s n * (φ' n).wireExponent a b
  have hd : ∀ n, IsPrice K (d n) := fun n => IsPrice.smul (isPrice_wireExponent (φ' n)) (hs n)
  have hdB : ∀ n a b, d n a b ≤ B a b + 1 / (n + 1) := by
    intro n a b
    calc s n * (φ' n).wireExponent a b
        ≤ s n * ∑ l, θ l * (φ n).wireExponent (Sum.elim id (σ l) a) (Sum.elim id (σ l) b) :=
          mul_le_mul_of_nonneg_left (h2 n a b) (hs n)
      _ = ∑ l, θ l * (s n * (φ n).wireExponent (Sum.elim id (σ l) a) (Sum.elim id (σ l) b)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by ring
      _ ≤ ∑ l, θ l * (w (Sum.elim id (σ l) a) (Sum.elim id (σ l) b) + 1 / (n + 1)) := by
        refine Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left ?_ (hθ l)
        have h3 := (abs_lt.1 (hφ n (Sum.elim id (σ l) a) (Sum.elim id (σ l) b))).1
        simp only [id] at h3
        linarith
      _ = B a b + 1 / (n + 1) := by
        simp only [mul_add]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, hθ1, one_mul]
  let U : Ultrafilter ℕ := Ultrafilter.of atTop
  obtain ⟨w', ⟨hw', -⟩, hlim⟩ :=
      (isCompact_setOf_isPrice_le K fun a b => B a b + 1).ultrafilter_le_nhds (U.map d) (by
    rw [le_principal_iff, Ultrafilter.coe_map, Filter.mem_map]
    exact univ_mem' fun n => ⟨hd n, fun a b => (hdB n a b).trans (by linarith [hle1 n])⟩)
  have hlim' : ∀ a b, Tendsto (fun n => d n a b) U (nhds (w' a b)) := by
    intro a b
    have h3 : Tendsto d U (nhds w') := hlim
    exact tendsto_pi_nhds.1 (tendsto_pi_nhds.1 h3 a) b
  have hzero : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) U (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.mono_left (Ultrafilter.of_le _)
  refine ⟨w', hw', fun p p' => ?_, fun a b => ?_⟩
  · have h3 : Tendsto (fun n => d n (Sum.inl p) (Sum.inl p') - w p p') U (nhds 0) := by
      refine squeeze_zero_norm (fun n => ?_) hzero
      rw [Real.norm_eq_abs, abs_sub_comm]
      change |w p p' - s n * (φ' n).wireExponent (Sum.inl p) (Sum.inl p')| ≤ _
      rw [h1]
      exact (hφ n p p').le
    have h4 := tendsto_nhds_unique h3 ((hlim' (Sum.inl p) (Sum.inl p')).sub_const (w p p'))
    linarith
  · exact le_of_tendsto_of_tendsto (hlim' a b) ((hzero.const_add (B a b)).trans (by rw [add_zero]))
      (Eventually.of_forall fun n => hdB n a b)

/-- Proof of Proposition A.8, the values of `σ`: on a finite set `T` of new points, a random map
with finitely many values at each `o` takes finitely many values `π_l`. With their probabilities
`θ_l`, the expectation of any function of the map is a finite mean. -/
private theorem prop_random_values {Y Q Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (σ : Q → Ω → Y)
    (hfin : ∀ κ, (Set.range (σ κ)).Finite) (hmeas : ∀ κ y, MeasurableSet (σ κ ⁻¹' {y}))
        (T : Finset Q) :
    ∃ (m : ℕ) (θ : Fin m → ℝ) (π : Fin m → T → Y), (∀ l, 0 ≤ θ l) ∧ ∑ l, θ l = 1 ∧
      ∀ f : (T → Y) → ℝ, ∫ ω, f (fun κ : T => σ κ ω) ∂μ = ∑ l, θ l * f (π l) := by
  classical
  have hfin' : (Set.range fun ω (κ : T) => σ κ ω).Finite := by
    refine (Set.Finite.pi' fun κ : T => hfin κ).subset ?_
    rintro _ ⟨ω, rfl⟩ κ
    exact ⟨ω, rfl⟩
  let V : Finset (T → Y) := hfin'.toFinset
  have hV : ∀ ω, (fun κ : T => σ κ ω) ∈ V := fun ω => by simp [V]
  have hmeas' : ∀ f : T → Y, MeasurableSet {ω | (fun κ : T => σ κ ω) = f} := fun f => by
    rw [show {ω | (fun κ : T => σ κ ω) = f} = ⋂ κ : T, σ κ ⁻¹' {f κ} by ext; simp [funext_iff]]
    exact MeasurableSet.iInter fun κ => hmeas _ _
  let e : Fin V.card ≃ V := V.equivFin.symm
  have hmean : ∀ f : (T → Y) → ℝ, ∫ ω, f (fun κ : T => σ κ ω) ∂μ =
      ∑ l : Fin V.card, μ.real {ω | (fun κ : T => σ κ ω) = (e l : T → Y)} * f (e l) := by
    intro f
    have h1 : ∀ ω, f (fun κ : T => σ κ ω) = ∑ g ∈ V,
        ({ω | (fun κ : T => σ κ ω) = g}).indicator (fun _ => f g) ω := by
      intro ω
      rw [Finset.sum_eq_single_of_mem _ (hV ω) fun g _ hg => Set.indicator_of_notMem
        (fun h : (fun κ : T => σ κ ω) = g => hg h.symm) _, Set.indicator_of_mem]
      rfl
    simp only [h1]
    rw [integral_finsetSum]
    · rw [← Finset.sum_coe_sort V]
      refine (Fintype.sum_equiv e _ _ fun l => ?_).symm
      rw [integral_indicator (hmeas' _), setIntegral_const, smul_eq_mul]
    · intro g _
      exact (integrable_const _).indicator (hmeas' g)
  refine ⟨V.card, fun l => μ.real {ω | (fun κ : T => σ κ ω) = (e l : T → Y)}, fun l => e l,
    fun l => measureReal_nonneg, ?_, hmean⟩
  simpa only [mul_one, integral_const, probReal_univ, smul_eq_mul] using (hmean fun _ => 1).symm

end Random

/-- **Paper: Proposition A.8 (prop:random).** Let `w` be a price on `Y`, let `Q` be a set disjoint
from `Y`, and let `σ` be a random map `Y ∪ Q → Y` that is the identity on `Y`, with finitely many
values at each `o`. Then some price on `Y ∪ Q` extends `w` and satisfies `|oo'| ≤ E |σ(o)σ(o')|` for
all `o, o'`. -/
theorem IsPrice.exists_extend_random {Y Q : Type} {w : Y → Y → ℝ} (hw : IsPrice K w)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (σ : Q → Ω → Y) (hfin : ∀ κ, (Set.range (σ κ)).Finite)
    (hmeas : ∀ κ y, MeasurableSet (σ κ ⁻¹' {y})) :
    ∃ w' : Y ⊕ Q → Y ⊕ Q → ℝ, IsPrice K w' ∧ (∀ y y', w' (Sum.inl y) (Sum.inl y') = w y y') ∧
      ∀ o o', w' o o' ≤
        ∫ ω, w (Sum.elim id (fun κ => σ κ ω) o) (Sum.elim id (fun κ => σ κ ω) o') ∂μ := by
  classical
  -- the two properties: at least w on Y, and at most the expectation
  let A : Y ⊕ Q → Y ⊕ Q → ℝ := fun o o' => match o, o' with
    | Sum.inl y, Sum.inl y' => w y y'
    | _, _ => 0
  let E : Y ⊕ Q → Y ⊕ Q → ℝ := fun o o' =>
    ∫ ω, w (Sum.elim id (fun κ => σ κ ω) o) (Sum.elim id (fun κ => σ κ ω) o') ∂μ
  suffices hS : ∀ S : Finset (Y ⊕ Q), ∃ d : S → S → ℝ, IsPrice K d ∧ ∀ a b : S,
      A a b ≤ d a b ∧ d a b ≤ E a b by
    obtain ⟨w', hw', h⟩ := prop_random_compact A E hS
    refine ⟨w', hw', fun y y' => le_antisymm ?_ (h (Sum.inl y) (Sum.inl y')).1,
        fun o o' => (h o o').2⟩
    simpa [E] using (h (Sum.inl y) (Sum.inl y')).2
  intro S
  -- Q₀: the new points of S; Y₀: the old points of S and all values of σ on Q₀
  let T : Finset Q := S.preimage Sum.inr Sum.inr_injective.injOn
  obtain ⟨m, θ, π, hθ, hθ1, hmean⟩ := prop_random_values μ σ hfin hmeas T
  let R : Finset Y := S.preimage Sum.inl Sum.inl_injective.injOn ∪
    Finset.univ.biUnion fun κ : T => Finset.univ.image fun l => π l κ
  have hR : ∀ l κ, π l κ ∈ R := fun l κ => Finset.mem_union_right _
    (Finset.mem_biUnion.2 ⟨κ, Finset.mem_univ κ, Finset.mem_image_of_mem _ (Finset.mem_univ l)⟩)
  obtain ⟨v, hv, hv1, hv2⟩ := prop_random_limit (IsPrice.comp hw (Subtype.val : R → Y)) θ hθ hθ1
    fun l κ => (⟨π l κ, hR l κ⟩ : R)
  -- the points of S among those of Y₀ ∪ Q₀, and their places under a map Q₀ → Y
  let g : S → R ⊕ T := fun a => match a with
    | ⟨Sum.inl y, hy⟩ => Sum.inl ⟨y, Finset.mem_union_left _ (Finset.mem_preimage.2 hy)⟩
    | ⟨Sum.inr κ, hκ⟩ => Sum.inr ⟨κ, Finset.mem_preimage.2 hκ⟩
  let place : (T → Y) → S → Y := fun f a => match a with
    | ⟨Sum.inl y, _⟩ => y
    | ⟨Sum.inr κ, hκ⟩ => f ⟨κ, Finset.mem_preimage.2 hκ⟩
  have hg : ∀ l (a : S),
      ((Sum.elim id (fun κ => (⟨π l κ, hR l κ⟩ : R)) (g a) : R) : Y) = place (π l) a := by
    rintro l ⟨y | κ, ha⟩ <;> rfl
  have hσ : ∀ ω (a : S), Sum.elim id (fun κ => σ κ ω) a.val = place (fun κ : T => σ κ ω) a := by
    rintro ω ⟨y | κ, ha⟩ <;> rfl
  refine ⟨fun a b => v (g a) (g b), IsPrice.comp hv g, fun a b => ⟨?_, ?_⟩⟩
  · obtain ⟨y | κ, ha⟩ := a <;> obtain ⟨y' | κ', hb⟩ := b
    · exact (hv1 ⟨y, _⟩ ⟨y', _⟩).ge
    all_goals exact hv.nonneg _ _
  · refine (hv2 (g a) (g b)).trans (le_of_eq ?_)
    change _ = ∫ ω, w (Sum.elim id (fun κ => σ κ ω) a.val) (Sum.elim id (fun κ => σ κ ω) b.val) ∂μ
    simp only [hg, hσ]
    exact (hmean fun f => w (place f a) (place f b)).symm

/-- Proposition A.8 for a random map with finitely many values `σ_l`, taken with probabilities
`θ_l`. -/
theorem IsPrice.exists_extend_of_weights {Y Q : Type} {w : Y → Y → ℝ} (hw : IsPrice K w)
    {Λ : Type} [Fintype Λ] (θ : Λ → ℝ)
    (hθ : ∀ l, 0 ≤ θ l) (hθ1 : ∑ l, θ l = 1) (σ : Λ → Q → Y) :
    ∃ w' : Y ⊕ Q → Y ⊕ Q → ℝ, IsPrice K w' ∧ (∀ y y', w' (Sum.inl y) (Sum.inl y') = w y y') ∧
      ∀ o o', w' o o' ≤ ∑ l, θ l * w (Sum.elim id (σ l) o) (Sum.elim id (σ l) o') := by
  classical
  let _ : MeasurableSpace Λ := ⊤
  have : MeasurableSingletonClass Λ := ⟨fun _ => trivial⟩
  let p : PMF Λ := PMF.ofFintype (fun l => ENNReal.ofReal (θ l))
    (by rw [← ENNReal.ofReal_sum_of_nonneg fun l _ => hθ l, hθ1, ENNReal.ofReal_one])
  obtain ⟨w', h1, h2, h3⟩ := IsPrice.exists_extend_random hw p.toMeasure (fun κ l => σ l κ)
      (fun κ => Set.toFinite _)
    fun κ y => trivial
  refine ⟨w', h1, h2, fun o o' => (h3 o o').trans (le_of_eq ?_)⟩
  rw [PMF.integral_eq_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [PMF.ofFintype_apply, ENNReal.toReal_ofReal (hθ l), smul_eq_mul]

end Cslib.PartyTensor
