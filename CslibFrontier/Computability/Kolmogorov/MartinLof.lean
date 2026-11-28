/-
Copyright (c) 2026 Matthew Doty, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Kolmogorov.ChaitinOmega
public import Mathlib.Algebra.Order.BigOperators.Expect
import CslibFrontier.Foundations.Data.BitString.Enumeration
import CslibFrontier.Foundations.Data.BitString.Primrec
import CslibFrontier.Foundations.Data.BitString.Sign
import CslibFrontier.Foundations.Data.List.FoldMax
import CslibFrontier.Foundations.Data.List.Primrec
import CslibFrontier.Probability.BitString.CoinFlips
import CslibFrontier.Probability.BitString.Rademacher
import Mathlib.Computability.Primrec.List

/-!
# Martin-Löf randomness, the Levin–Schnorr theorem, and Solovay tests

This module develops the general theory of Martin-Löf randomness on infinite binary sequences
`ℕ → Bool` under `Cslib.BitString.coinFlips`, proving the remaining directions of [LiVitanyi2019]
and [ShenUspenskyVereshchagin2017] on top of `ChaitinOmega.lean`:

* **Left-c.e. measure of effectively open cylinder unions**: for any computably enumerable set
  `{w | (e.eval (encode w)).Dom}` of binary prefixes, `reCoverMass e : ℕ → ℚ` is uniformly
  computable, monotone, and converges to
  `(Cslib.BitString.coinFlips (⋃ w ∈ S, prefixCylinderList w)).toReal` (`tendsto_reCoverMass`).
* **Universal Martin-Löf test and full measure**: `universalMartinLofTest : MartinLofTest`
  captures every `T : MartinLofTest` (`exists_subset_universalMartinLofTest`), characterizes
  `IsMartinLofRandom` (`isMartinLofRandom_iff_passes_universalMartinLofTest`), and yields
  `ae_isMartinLofRandom : ∀ᵐ x ∂Cslib.BitString.coinFlips, IsMartinLofRandom x`.
* **Levin–Schnorr theorem** [LiVitanyi2019, ShenUspenskyVereshchagin2017]: an infinite binary
  sequence `x` is Martin-Löf random if and only if its initial segments have prefix-free complexity
  `n ≤ K(x ↾ n) + O(1)` (`isMartinLofRandom_iff_exists_le_complexity`,
  `isMartinLofRandom_iff_exists_le_ecomplexity`), invariant across prefix-free optimal decoders
  (`isMartinLofRandom_iff_exists_le_complexity_of_optimal`,
  `isMartinLofRandom_iff_exists_le_ecomplexity_of_optimal`).
* **Solovay tests and Borel normality**: `SolovayTest` and `PassesSolovayTest` are equivalent to
  Martin-Löf randomness (`passesSolovayTest_iff_isMartinLofRandom`); combined with sub-Gaussian
  Rademacher concentration this yields Borel's strong law of large numbers for every Martin-Löf
  random sequence (`tendsto_freq_true_of_isMartinLofRandom`) and for Chaitin's `Ω`
  (`tendsto_freq_true_chaitinOmega`).

## Main definitions

* `Cslib.Kolmogorov.reWords`: monotone enumeration of the prefixes accepted by a code `e`.
* `Cslib.Kolmogorov.finitePrefixMass`: exact `coinFlips`-measure of a finite list of cylinders.
* `Cslib.Kolmogorov.reCoverMass`: computable rational lower approximant to the measure of an r.e.
  union of cylinders.
* `Cslib.Kolmogorov.universalMartinLofTest`: a universal Martin-Löf randomness test.
* `Cslib.Kolmogorov.SolovayTest`, `Cslib.Kolmogorov.PassesSolovayTest`: Solovay randomness
  tests with finite sum of cylinder measures.

## Main results

* `Cslib.Kolmogorov.toReal_coinFlips_biUnion_list`, `Cslib.Kolmogorov.finitePrefixMass_nonneg`,
  `Cslib.Kolmogorov.finitePrefixMass_le_one`: measure characterization and bounds for
  `finitePrefixMass`.
* `Cslib.Kolmogorov.reCoverMass_nonneg`, `Cslib.Kolmogorov.reCoverMass_le_one`,
  `Cslib.Kolmogorov.reCoverMass_le_coinFlips`, `Cslib.Kolmogorov.tendsto_reCoverMass`,
  `Cslib.Kolmogorov.exists_computable_approx_coinFlips_of_rePred`: uniform left-c.e. measure of
  effectively open cylinder sets.
* `Cslib.Kolmogorov.DescriptionMethod.isPartrec_universalPrefixBits`: partial recursive
  evaluator for `universalPrefixBits`.
* `Cslib.Kolmogorov.exists_subset_universalMartinLofTest`,
  `Cslib.Kolmogorov.isMartinLofRandom_iff_passes_universalMartinLofTest`,
  `Cslib.Kolmogorov.ae_isMartinLofRandom`: universality and `coinFlips`-almost-everywhere
  randomness.
* `Cslib.Kolmogorov.le_complexity_of_isMartinLofRandom`,
  `Cslib.Kolmogorov.isMartinLofRandom_iff_exists_le_complexity`,
  `Cslib.Kolmogorov.isMartinLofRandom_iff_exists_le_ecomplexity`,
  `Cslib.Kolmogorov.isMartinLofRandom_iff_exists_le_complexity_of_optimal`,
  `Cslib.Kolmogorov.isMartinLofRandom_iff_exists_le_ecomplexity_of_optimal`:
  **Levin–Schnorr theorem** and its invariance across optimal prefix-free machines.
* `Cslib.Kolmogorov.passesSolovayTest_of_isMartinLofRandom`,
  `Cslib.Kolmogorov.isMartinLofRandom_of_forall_passesSolovayTest`,
  `Cslib.Kolmogorov.passesSolovayTest_iff_isMartinLofRandom`: equivalence of Solovay tests
  and Martin-Löf randomness.
* `Cslib.Kolmogorov.tendsto_freq_true_of_isMartinLofRandom`,
  `Cslib.Kolmogorov.tendsto_freq_true_chaitinOmega`: **Borel's strong law of large numbers** for
  Martin-Löf random sequences and Chaitin's `Ω`.

## References

* [M. Li, P. Vitányi, *An Introduction to Kolmogorov Complexity and Its
  Applications*][LiVitanyi2019]
* [A. Shen, V. A. Uspensky, N. Vereshchagin, *Kolmogorov Complexity and Algorithmic
  Randomness*][ShenUspenskyVereshchagin2017]
-/

public section

open scoped BigOperators ENNReal Filter Topology

namespace Cslib.Kolmogorov

open Encodable Denumerable Nat.Partrec Filter MeasureTheory

/-! ### Left-c.e. measure of effectively open cylinder unions -/

private def prefixUnionMaxLen (L : List (List Bool)) : ℕ :=
  (L.map List.length).foldl max 0

private def prefixUnionCount (L : List (List Bool)) : ℕ :=
  (Cslib.BitString.enumList (prefixUnionMaxLen L)).countP
    (fun v => L.any fun w => decide (w <+: v))

/-- Exact `coinFlips` measure in `ℚ` of the finite cylinder union
`⋃ w ∈ L, prefixCylinderList w`. -/
def finitePrefixMass (L : List (List Bool)) : ℚ :=
  (prefixUnionCount L : ℚ) * (2 : ℚ)⁻¹ ^ prefixUnionMaxLen L

private theorem length_le_prefixUnionMaxLen {L : List (List Bool)} {w : List Bool}
    (hw : w ∈ L) : w.length ≤ prefixUnionMaxLen L :=
  List.mem_le_foldl_max (List.mem_map_of_mem hw)

private theorem primrec_prefixUnionMaxLen : Primrec prefixUnionMaxLen :=
  (Primrec.list_foldl (Primrec.list_map Primrec.id (Primrec.list_length.comp Primrec.snd).to₂)
    (Primrec.const 0)
    (Primrec₂.mk (f := fun (_ : List (List Bool)) (mn : ℕ × ℕ) => max mn.1 mn.2) <|
      Primrec.nat_max.comp
        (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))).of_eq fun _ => rfl

private theorem primrec_prefixUnionCount : Primrec prefixUnionCount := by
  have hpred : PrimrecPred fun arg : List (List Bool) × (List Bool × ℕ) =>
      ∃ w ∈ arg.1, w <+: arg.2.1 :=
    (PrimrecRel.exists_mem_list Primrec.list_isPrefix).comp
      Primrec.fst (Primrec.fst.comp Primrec.snd)
  have hh : Primrec₂ fun (L : List (List Bool)) (vn : List Bool × ℕ) =>
      if L.any (fun w => decide (w <+: vn.1)) then vn.2 + 1 else vn.2 := by
    refine Primrec₂.mk <| (Primrec.ite hpred
      (Primrec.succ.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).of_eq fun ⟨L, v, n⟩ => ?_
    simp [List.any_eq_true]
  refine (Primrec.list_foldr
    (Cslib.BitString.primrec_enumList.comp primrec_prefixUnionMaxLen)
    (Primrec.const 0) hh).of_eq fun L => ?_
  dsimp only [prefixUnionCount]
  induction Cslib.BitString.enumList (prefixUnionMaxLen L) with
  | nil => rfl
  | cons a t ih =>
    simp only [List.foldr_cons, List.countP_cons, ih]
    cases L.any fun w => decide (w <+: a) <;> simp

private theorem biUnion_prefixCylinderList_eq_filter (L : List (List Bool)) :
    (⋃ w ∈ L, prefixCylinderList w) =
      ⋃ v ∈ ((Cslib.BitString.enumList (prefixUnionMaxLen L)).filter
        fun v => L.any fun w => decide (w <+: v)).toFinset, prefixCylinderList v := by
  ext x
  simp only [Set.mem_iUnion, List.mem_toFinset, List.mem_filter, Cslib.BitString.mem_enumList,
    List.any_eq_true, decide_eq_true_eq, exists_prop]
  refine ⟨fun ⟨w, hw, hx⟩ => ?_, fun ⟨_, ⟨_, w, hw, hwv⟩, hxv⟩ =>
    ⟨w, hw, prefixCylinderList_subset_of_isPrefix hwv hxv⟩⟩
  refine ⟨List.ofFn fun i : Fin (prefixUnionMaxLen L) => x i,
    ⟨by simp, w, hw, ?_⟩, mem_prefixCylinderList.mpr fun _ => by simp⟩
  have hwM : w.length ≤ prefixUnionMaxLen L := length_le_prefixUnionMaxLen hw
  rw [List.prefix_iff_eq_take]
  refine List.ext_getElem (by simp [hwM]) fun i hi1 _ => ?_
  have hiw : i < w.length := by simpa [hwM] using hi1
  simp only [List.getElem_take, List.getElem_ofFn]
  exact ((mem_prefixCylinderList.mp hx) ⟨i, hiw⟩).symm

private theorem coinFlips_biUnion_list (L : List (List Bool)) :
    Cslib.BitString.coinFlips (⋃ w ∈ L, prefixCylinderList w) =
      (prefixUnionCount L : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ prefixUnionMaxLen L := by
  let M := prefixUnionMaxLen L
  let F := (Cslib.BitString.enumList M).filter fun v => L.any fun w => decide (w <+: v)
  have hlen_mem : ∀ v ∈ F.toFinset, v.length = M := fun v hv =>
    Cslib.BitString.length_of_mem_enumList (List.mem_filter.mp (List.mem_toFinset.mp hv)).1
  have hdisj : (F.toFinset : Set (List Bool)).PairwiseDisjoint prefixCylinderList :=
    fun v₁ hv₁ v₂ hv₂ hne => disjoint_prefixCylinderList_of_prefixDisjoint
      ⟨fun hp => hne (hp.eq_of_length ((hlen_mem v₁ hv₁).trans (hlen_mem v₂ hv₂).symm)),
       fun hp => hne (hp.eq_of_length ((hlen_mem v₂ hv₂).trans (hlen_mem v₁ hv₁).symm)).symm⟩
  have hnd : F.Nodup := ((Cslib.BitString.nodup_enum M).map List.ofFn_injective).filter _
  rw [biUnion_prefixCylinderList_eq_filter,
    measure_biUnion_finset hdisj fun v _ => measurableSet_prefixCylinderList v]
  calc ∑ v ∈ F.toFinset, Cslib.BitString.coinFlips (prefixCylinderList v)
    _ = ∑ _ ∈ F.toFinset, (2 : ℝ≥0∞)⁻¹ ^ M :=
        Finset.sum_congr rfl fun v hv => by
          rw [coinFlips_prefixCylinderList, ENNReal.inv_pow, hlen_mem v hv]
    _ = (F.toFinset.card : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ M := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (prefixUnionCount L : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ prefixUnionMaxLen L := by
        rw [List.toFinset_card_of_nodup hnd, ← List.countP_eq_length_filter]
        rfl

/-- The real value of `finitePrefixMass L` equals the `coinFlips`-measure of the finite cylinder
union `⋃ w ∈ L, prefixCylinderList w`. -/
theorem toReal_coinFlips_biUnion_list (L : List (List Bool)) :
    (Cslib.BitString.coinFlips (⋃ w ∈ L, prefixCylinderList w)).toReal =
      (finitePrefixMass L : ℝ) := by
  rw [coinFlips_biUnion_list, ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_pow]
  simp [finitePrefixMass]

/-- Every finite cylinder union mass `finitePrefixMass L` is nonnegative. -/
theorem finitePrefixMass_nonneg (L : List (List Bool)) : 0 ≤ finitePrefixMass L := by
  dsimp [finitePrefixMass]
  positivity

/-- Every finite cylinder union mass `finitePrefixMass L` is at most `1`. -/
theorem finitePrefixMass_le_one (L : List (List Bool)) : finitePrefixMass L ≤ 1 := by
  have hm := ENNReal.toReal_mono (measure_ne_top Cslib.BitString.coinFlips _)
    (measure_mono (Set.subset_univ (⋃ w ∈ L, prefixCylinderList w)))
  rw [toReal_coinFlips_biUnion_list, measure_univ, ENNReal.toReal_one] at hm
  exact_mod_cast hm

private def reCand (e : Code) (j : ℕ) : Option (List Bool) :=
  (decode (α := List Bool × ℕ) j).bind fun wf =>
    (Code.evaln wf.2 e (encode wf.1)).map fun _ => wf.1

private theorem primrec₂_reCand : Primrec₂ reCand := by
  have hev : Primrec fun ewf : Code × (List Bool × ℕ) =>
      Code.evaln ewf.2.2 ewf.1 (encode ewf.2.1) :=
    Code.primrec_evaln.comp <| Primrec.pair
      (Primrec.pair (Primrec.snd.comp Primrec.snd) Primrec.fst)
      (Primrec.encode.comp (Primrec.fst.comp Primrec.snd))
  have hmap : Primrec₂ fun (e : Code) (wf : List Bool × ℕ) =>
      (Code.evaln wf.2 e (encode wf.1)).map fun _ => wf.1 :=
    Primrec₂.mk <| Primrec.option_map hev (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).to₂
  exact Primrec₂.mk <| (Primrec.option_bind (Primrec.decode.comp Primrec.snd)
    (hmap.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂).of_eq fun _ => rfl

/-- Stage-`t` distinct prefix list enumerated by partial recursive code `e`. -/
def reWords (e : Code) (t : ℕ) : List (List Bool) :=
  Nat.distinctValues (reCand e) t

theorem primrec₂_reWords : Primrec₂ reWords :=
  Primrec.distinctValues primrec₂_reCand

theorem mem_reWords_iff_exists_evaln {e : Code} {t : ℕ} {w : List Bool} :
    w ∈ reWords e t ↔
      ∃ j < t, ∃ wf ∈ decode (α := List Bool × ℕ) j,
        wf.1 = w ∧ (Code.evaln wf.2 e (encode wf.1)).isSome := by
  simp only [reWords, Nat.mem_distinctValues, reCand, Option.bind_eq_some_iff,
    Option.map_eq_some_iff, Option.isSome_iff_exists]
  exact ⟨fun ⟨j, hj, wf, hdec, y, hy, h⟩ => ⟨j, hj, wf, hdec, h, y, hy⟩,
    fun ⟨j, hj, wf, hdec, h, y, hy⟩ => ⟨j, hj, wf, hdec, y, hy, h⟩⟩

theorem exists_mem_reWords_iff_dom {e : Code} {w : List Bool} :
    (∃ t : ℕ, w ∈ reWords e t) ↔ (e.eval (encode w)).Dom := by
  constructor
  · rintro ⟨_, ht⟩
    obtain ⟨_, _, _, _, rfl, y, hy⟩ := by
      simpa only [Option.isSome_iff_exists] using mem_reWords_iff_exists_evaln.mp ht
    exact Part.dom_iff_mem.mpr ⟨y, Code.evaln_sound hy⟩
  · intro hdom
    obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp hdom
    obtain ⟨f, hf⟩ := Code.evaln_complete.mp hy
    exact ⟨encode (w, f) + 1, mem_reWords_iff_exists_evaln.mpr
      ⟨encode (w, f), Nat.lt_succ_self _, (w, f), encodek _, rfl,
        Option.isSome_iff_exists.mpr ⟨y, hf⟩⟩⟩

/-- Uniformly computable monotone rational lower approximant to the `coinFlips`-measure of the
effectively open union `⋃ w ∈ {w | (e.eval (encode w)).Dom}, prefixCylinderList w`.
Because `ℚ` has no canonical Mathlib `Primcodable` instance, uniform computability of the exact
dyadic numerator/denominator pair representing `(reCoverMass e t : ℝ)` is stated in
`exists_computable_approx_coinFlips_of_rePred`. -/
def reCoverMass (e : Code) (t : ℕ) : ℚ :=
  finitePrefixMass (reWords e t)

/-- Each rational approximant `reCoverMass e t` is nonnegative. -/
theorem reCoverMass_nonneg (e : Code) (t : ℕ) : 0 ≤ reCoverMass e t :=
  finitePrefixMass_nonneg (reWords e t)

private theorem monotone_biUnion_reWords (e : Code) :
    Monotone fun t => ⋃ w ∈ reWords e t, prefixCylinderList w := fun _ _ hmn =>
  Set.iUnion₂_mono' fun w hw =>
    ⟨w, (Nat.distinctValues_prefix (reCand e) hmn).subset hw, Set.Subset.rfl⟩

theorem monotone_reCoverMass (e : Code) : Monotone (reCoverMass e) := fun _ _ hmn => by
  have hm := ENNReal.toReal_mono (measure_ne_top Cslib.BitString.coinFlips _)
    (measure_mono (monotone_biUnion_reWords e hmn))
  rw [toReal_coinFlips_biUnion_list, toReal_coinFlips_biUnion_list] at hm
  exact_mod_cast hm

theorem reCoverMass_le_one (e : Code) (t : ℕ) : reCoverMass e t ≤ 1 :=
  finitePrefixMass_le_one (reWords e t)

private theorem tendsto_coinFlips_reWords (e : Code) :
    Tendsto (fun t => Cslib.BitString.coinFlips (⋃ w ∈ reWords e t, prefixCylinderList w)) atTop
      (𝓝 (Cslib.BitString.coinFlips
        (⋃ w ∈ {w | (e.eval (encode w)).Dom}, prefixCylinderList w))) := by
  have hunion : (⋃ t : ℕ, ⋃ w ∈ reWords e t, prefixCylinderList w) =
      ⋃ w ∈ {w | (e.eval (encode w)).Dom}, prefixCylinderList w := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop, ← exists_mem_reWords_iff_dom]
    exact ⟨fun ⟨t, w, hw, hx⟩ => ⟨w, ⟨t, hw⟩, hx⟩, fun ⟨w, ⟨t, hw⟩, hx⟩ => ⟨t, w, hw, hx⟩⟩
  rw [← hunion]
  exact MeasureTheory.tendsto_measure_iUnion_atTop (monotone_biUnion_reWords e)

/-- **Left-c.e. measure of effectively open cylinder sets**: uniformly in a code `e`, the rational
approximants `reCoverMass e t` converge from below to the `coinFlips`-measure of
`⋃ w ∈ {w | (e.eval (encode w)).Dom}, prefixCylinderList w`. -/
theorem tendsto_reCoverMass (e : Code) :
    Tendsto (fun t => (reCoverMass e t : ℝ)) atTop
      (𝓝 (Cslib.BitString.coinFlips
        (⋃ w ∈ {w | (e.eval (encode w)).Dom}, prefixCylinderList w)).toReal) :=
  ((ENNReal.continuousAt_toReal (measure_ne_top Cslib.BitString.coinFlips _)).tendsto.comp
    (tendsto_coinFlips_reWords e)).congr fun t => toReal_coinFlips_biUnion_list (reWords e t)

/-- Every approximant `reCoverMass e t` bounds
`(Cslib.BitString.coinFlips (⋃ w ∈ {w | (e.eval (encode w)).Dom}, prefixCylinderList w)).toReal`
from below. -/
theorem reCoverMass_le_coinFlips (e : Code) (t : ℕ) :
    (reCoverMass e t : ℝ) ≤
      (Cslib.BitString.coinFlips
        (⋃ w ∈ {w | (e.eval (encode w)).Dom}, prefixCylinderList w)).toReal :=
  Monotone.ge_of_tendsto (f := fun s => (reCoverMass e s : ℝ))
    (fun _ _ h => Rat.cast_mono (monotone_reCoverMass e h)) (tendsto_reCoverMass e) t

/-- Every computably enumerable prefix set `S : Set (List Bool)` has a computable monotone rational
sequence converging from below to `(coinFlips (⋃ w ∈ S, prefixCylinderList w)).toReal`. -/
theorem exists_computable_approx_coinFlips_of_rePred {S : Set (List Bool)} (hS : REPred (· ∈ S)) :
    ∃ (num den : ℕ → ℕ), Computable num ∧ Computable den ∧ (∀ t, 0 < den t) ∧
      Monotone (fun t => (num t : ℝ) / (den t : ℝ)) ∧
      Tendsto (fun t => (num t : ℝ) / (den t : ℝ)) atTop
        (𝓝 (Cslib.BitString.coinFlips (⋃ w ∈ S, prefixCylinderList w)).toReal) := by
  obtain ⟨e, he⟩ := rePred_iff_exists_code.mp hS
  have hre : Primrec (reWords e) := primrec₂_reWords.comp (Primrec.const e) Primrec.id
  have hratio : ∀ t : ℕ, (prefixUnionCount (reWords e t) : ℝ) /
      ((2 ^ prefixUnionMaxLen (reWords e t) : ℕ) : ℝ) = (reCoverMass e t : ℝ) := fun t => by
    simp [reCoverMass, finitePrefixMass, inv_pow, div_eq_mul_inv]
  refine ⟨_, _, (primrec_prefixUnionCount.comp hre).to_comp,
    (primrec_two_pow.comp (primrec_prefixUnionMaxLen.comp hre)).to_comp, fun _ => by positivity,
    fun a b hab => by
      dsimp only
      rw [hratio a, hratio b]
      exact_mod_cast monotone_reCoverMass e hab, ?_⟩
  rw [show S = {w | (e.eval (encode w)).Dom} from Set.ext he]
  exact (tendsto_reCoverMass e).congr fun t => (hratio t).symm

/-! ### Capped effective tests and a universal Martin-Löf test -/

private def mlCand (ek : Code × ℕ) (j : ℕ) : Option (List Bool) :=
  (decode (α := List Bool × ℕ) j).bind fun wf =>
    (Code.evaln wf.2 ek.1 (encode (ek.2, wf.1))).map fun _ => wf.1

private theorem primrec₂_mlCand : Primrec₂ mlCand := by
  have hev : Primrec fun arg : (Code × ℕ) × (List Bool × ℕ) =>
      Code.evaln arg.2.2 arg.1.1 (encode (arg.1.2, arg.2.1)) :=
    Code.primrec_evaln.comp <| Primrec.pair
      (Primrec.pair (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.fst))
      (Primrec.encode.comp
        (Primrec.pair (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)))
  have hmap : Primrec₂ fun (ek : Code × ℕ) (wf : List Bool × ℕ) =>
      (Code.evaln wf.2 ek.1 (encode (ek.2, wf.1))).map fun _ => wf.1 :=
    Primrec₂.mk <| Primrec.option_map hev (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).to₂
  exact Primrec₂.mk <| (Primrec.option_bind (Primrec.decode.comp Primrec.snd)
    (hmap.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂).of_eq fun _ => rfl

private def mlCappedStep (ek : Code × ℕ) (j : ℕ) (acc : List (List Bool)) : List (List Bool) :=
  match mlCand ek j with
  | Option.none => acc
  | some w =>
    let cand := w :: acc
    if prefixUnionCount cand * 2 ^ ek.2 ≤ 2 ^ prefixUnionMaxLen cand then cand else acc

private theorem primrec_mlCappedStep :
    Primrec fun arg : (Code × ℕ) × (ℕ × List (List Bool)) =>
      mlCappedStep arg.1 arg.2.1 arg.2.2 := by
  have hcand : Primrec fun arg : (Code × ℕ) × (ℕ × List (List Bool)) =>
      mlCand arg.1 arg.2.1 :=
    primrec₂_mlCand.comp Primrec.fst (Primrec.fst.comp Primrec.snd)
  have hcons : Primrec₂ fun (arg : (Code × ℕ) × (ℕ × List (List Bool))) (w : List Bool) =>
      w :: arg.2.2 :=
    Primrec₂.mk <| Primrec.list_cons.comp Primrec.snd
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hcond : PrimrecPred fun arg : ((Code × ℕ) × (ℕ × List (List Bool))) × List Bool =>
      prefixUnionCount (arg.2 :: arg.1.2.2) * 2 ^ arg.1.1.2 ≤
        2 ^ prefixUnionMaxLen (arg.2 :: arg.1.2.2) :=
    PrimrecRel.comp Primrec.nat_le
      (Primrec.nat_mul.comp
        (primrec_prefixUnionCount.comp (hcons.comp Primrec.fst Primrec.snd))
        (primrec_two_pow.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))
      (primrec_two_pow.comp
        (primrec_prefixUnionMaxLen.comp (hcons.comp Primrec.fst Primrec.snd)))
  have hsome : Primrec₂ fun (arg : (Code × ℕ) × (ℕ × List (List Bool))) (w : List Bool) =>
      if prefixUnionCount (w :: arg.2.2) * 2 ^ arg.1.2 ≤
          2 ^ prefixUnionMaxLen (w :: arg.2.2) then
        w :: arg.2.2
      else arg.2.2 :=
    Primrec₂.mk <| Primrec.ite hcond (hcons.comp Primrec.fst Primrec.snd)
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  refine (Primrec.option_casesOn hcand (Primrec.snd.comp Primrec.snd) hsome).of_eq fun _ => ?_
  simp only [mlCappedStep]
  cases mlCand _ _ <;> rfl

private theorem nat_mul_two_pow_le_iff_ennreal (c k M : ℕ) :
    c * 2 ^ k ≤ 2 ^ M ↔ (c : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ M ≤ (2 : ℝ≥0∞)⁻¹ ^ k := by
  have hM : (2 : ℝ≥0∞) ^ M ≠ 0 ∧ (2 : ℝ≥0∞) ^ M ≠ ⊤ := ⟨by positivity, by simp⟩
  have hk : (2 : ℝ≥0∞) ^ k ≠ 0 ∧ (2 : ℝ≥0∞) ^ k ≠ ⊤ := ⟨by positivity, by simp⟩
  rw [← ENNReal.inv_pow, ← ENNReal.inv_pow,
    ← ENNReal.mul_le_mul_iff_right hM.1 hM.2, ← ENNReal.mul_le_mul_iff_right hk.1 hk.2,
    mul_left_comm (2 ^ M : ℝ≥0∞) (c : ℝ≥0∞), ENNReal.mul_inv_cancel hM.1 hM.2, mul_one,
    mul_left_comm (2 ^ k : ℝ≥0∞) (2 ^ M), ENNReal.mul_inv_cancel hk.1 hk.2, mul_one,
    mul_comm (2 ^ k : ℝ≥0∞)]
  exact_mod_cast Iff.rfl

private theorem dom_of_mlCand_eq_some {ek : Code × ℕ} {j : ℕ} {w : List Bool}
    (hc : mlCand ek j = some w) : (ek.1.eval (encode (ek.2, w))).Dom := by
  simp only [mlCand, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hc
  obtain ⟨⟨_, _⟩, _, y, hy, rfl⟩ := hc
  exact Part.dom_iff_mem.mpr ⟨y, Code.evaln_sound hy⟩

private theorem exists_mlCand_eq_some_of_dom {ek : Code × ℕ} {w : List Bool}
    (hw : (ek.1.eval (encode (ek.2, w))).Dom) : ∃ j : ℕ, mlCand ek j = some w := by
  obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp hw
  obtain ⟨f, hf⟩ := Code.evaln_complete.mp hy
  refine ⟨encode (w, f), ?_⟩
  rw [Option.mem_def] at hf
  dsimp only [mlCand]
  rw [encodek, Option.bind_some]
  change (Code.evaln f ek.1 (encode (ek.2, w))).map (fun _ => w) = some w
  rw [hf]; rfl

private def mlCappedList (ek : Code × ℕ) : ℕ → List (List Bool)
  | 0 => []
  | n + 1 => mlCappedStep ek n (mlCappedList ek n)

private theorem primrec₂_mlCappedList : Primrec₂ mlCappedList := by
  refine (Primrec.nat_rec (Primrec.const []) primrec_mlCappedStep.to₂).of_eq fun ek n => ?_
  induction n with
  | zero => rfl
  | succ m ih => rw [mlCappedList, ← ih]

private theorem mlCappedList_subset_mono (ek : Code × ℕ) {m n : ℕ} (hmn : m ≤ n) :
    mlCappedList ek m ⊆ mlCappedList ek n := by
  induction hmn with
  | refl => exact fun _ h => h
  | step _ ih =>
    intro w hw
    simp only [mlCappedList, mlCappedStep]
    cases mlCand ek _ with
    | none => exact ih hw
    | some _ =>
      dsimp only
      split_ifs
      · exact List.mem_cons_of_mem _ (ih hw)
      · exact ih hw

private theorem mlCappedList_spec (ek : Code × ℕ) (n : ℕ) :
    prefixUnionCount (mlCappedList ek n) * 2 ^ ek.2 ≤
        2 ^ prefixUnionMaxLen (mlCappedList ek n) ∧
      ∀ w ∈ mlCappedList ek n, (ek.1.eval (encode (ek.2, w))).Dom := by
  induction n with
  | zero => simp [mlCappedList, prefixUnionCount, prefixUnionMaxLen]
  | succ n ih =>
    obtain ⟨hmeas, hdom⟩ := ih
    simp only [mlCappedList, mlCappedStep]
    cases hcand : mlCand ek n with
    | none => exact ⟨hmeas, hdom⟩
    | some w =>
      dsimp only
      split_ifs with hcap
      · refine ⟨hcap, fun u hu => ?_⟩
        rcases List.mem_cons.mp hu with rfl | hu'
        · exact dom_of_mlCand_eq_some hcand
        · exact hdom u hu'
      · exact ⟨hmeas, hdom⟩

private theorem coinFlips_mlCappedList_le (ek : Code × ℕ) (n : ℕ) :
    Cslib.BitString.coinFlips (⋃ w ∈ mlCappedList ek n, prefixCylinderList w) ≤
      (2 : ℝ≥0∞)⁻¹ ^ ek.2 := by
  rw [coinFlips_biUnion_list]
  exact (nat_mul_two_pow_le_iff_ennreal _ _ _).mp (mlCappedList_spec ek n).1

private theorem coinFlips_iUnion_mlCapped_le (ek : Code × ℕ) :
    Cslib.BitString.coinFlips
      (⋃ w ∈ {w | ∃ n : ℕ, w ∈ mlCappedList ek n}, prefixCylinderList w) ≤
      (2 : ℝ≥0∞)⁻¹ ^ ek.2 := by
  have heq : (⋃ w ∈ {w | ∃ n : ℕ, w ∈ mlCappedList ek n}, prefixCylinderList w) =
      ⋃ n : ℕ, ⋃ w ∈ mlCappedList ek n, prefixCylinderList w := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    exact ⟨fun ⟨w, ⟨n, hn⟩, hx⟩ => ⟨n, w, hn, hx⟩, fun ⟨n, w, hn, hx⟩ => ⟨w, ⟨n, hn⟩, hx⟩⟩
  rw [heq]
  have hmono : Monotone fun n => ⋃ w ∈ mlCappedList ek n, prefixCylinderList w := fun _ _ hmn =>
    Set.iUnion₂_mono' fun w hw => ⟨w, mlCappedList_subset_mono ek hmn hw, Set.Subset.rfl⟩
  exact le_of_tendsto (MeasureTheory.tendsto_measure_iUnion_atTop hmono)
    (Eventually.of_forall fun n => coinFlips_mlCappedList_le ek n)

private theorem mlCapped_eq_all_of_measure_le (e : Code) (k : ℕ)
    (hle : Cslib.BitString.coinFlips
      (⋃ w ∈ {w | (e.eval (encode (k, w))).Dom}, prefixCylinderList w) ≤ (2 : ℝ≥0∞)⁻¹ ^ k)
    {w : List Bool} (hw : (e.eval (encode (k, w))).Dom) :
    ∃ n : ℕ, w ∈ mlCappedList (e, k) n := by
  obtain ⟨j, hcand⟩ := exists_mlCand_eq_some_of_dom (ek := (e, k)) hw
  refine ⟨j + 1, ?_⟩
  simp only [mlCappedList, mlCappedStep, hcand]
  have hsub : (⋃ u ∈ (w :: mlCappedList (e, k) j), prefixCylinderList u) ⊆
      ⋃ u ∈ {u | (e.eval (encode (k, u))).Dom}, prefixCylinderList u := by
    refine Set.iUnion₂_subset fun u hu => Set.subset_iUnion₂_of_subset u ?_ Set.Subset.rfl
    rcases List.mem_cons.mp hu with rfl | hu'
    · exact hw
    · exact (mlCappedList_spec (e, k) j).2 u hu'
  have hm : (prefixUnionCount (w :: mlCappedList (e, k) j) : ℝ≥0∞) *
      (2 : ℝ≥0∞)⁻¹ ^ prefixUnionMaxLen (w :: mlCappedList (e, k) j) ≤ (2 : ℝ≥0∞)⁻¹ ^ k :=
    calc _ = Cslib.BitString.coinFlips
          (⋃ u ∈ w :: mlCappedList (e, k) j, prefixCylinderList u) :=
          (coinFlips_biUnion_list _).symm
      _ ≤ Cslib.BitString.coinFlips
          (⋃ u ∈ {u | (e.eval (encode (k, u))).Dom}, prefixCylinderList u) :=
          measure_mono hsub
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ k := hle
  simp [(nat_mul_two_pow_le_iff_ennreal _ _ _).mpr hm]

private theorem computablePred_mem_mlCappedList :
    ComputablePred fun arg : (ℕ × List Bool) × (ℕ × ℕ) =>
      arg.1.2 ∈ mlCappedList (ofNat Code arg.2.1, arg.1.1 + arg.2.1 + 1) arg.2.2 := by
  have hlist : Primrec fun arg : (ℕ × List Bool) × (ℕ × ℕ) =>
      mlCappedList (ofNat Code arg.2.1, arg.1.1 + arg.2.1 + 1) arg.2.2 :=
    primrec₂_mlCappedList.comp
      (Primrec.pair ((Primrec.ofNat Code).comp (Primrec.fst.comp Primrec.snd))
        (Primrec.succ.comp (Primrec.nat_add.comp (Primrec.fst.comp Primrec.fst)
          (Primrec.fst.comp Primrec.snd))))
      (Primrec.snd.comp Primrec.snd)
  have heq_pred : ComputablePred (Function.uncurry fun (arg : (ℕ × List Bool) × (ℕ × ℕ))
      (u : List Bool) => u = arg.1.2) :=
    (Primrec.eq.decide.to_comp.comp Computable.snd
      (Computable.snd.comp (Computable.fst.comp Computable.fst))).computablePred
  exact (ComputablePred.exists_mem_list heq_pred hlist.to_comp).of_eq fun arg => by simp

private theorem tsum_two_inv_pow_shift (m : ℕ) :
    (∑' i : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (m + i + 1)) = (2 : ℝ≥0∞)⁻¹ ^ m := by
  have hterm (i : ℕ) : (2 : ℝ≥0∞)⁻¹ ^ (m + i + 1) =
      ((2 : ℝ≥0∞)⁻¹ ^ m * (2 : ℝ≥0∞)⁻¹) * (2 : ℝ≥0∞)⁻¹ ^ i := by
    rw [show m + i + 1 = (m + 1) + i by omega, pow_add, pow_succ]
  simp_rw [hterm, ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  have hsub : (1 : ℝ≥0∞) - (2 : ℝ≥0∞)⁻¹ = (2 : ℝ≥0∞)⁻¹ := by
    conv_lhs => rw [← ENNReal.inv_two_add_inv_two]
    exact ENNReal.add_sub_cancel_right (by norm_num)
  rw [hsub, mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]

/-- A **universal Martin-Löf randomness test**, combining every effective randomness test `i : ℕ`
with shifted tolerance `(m + i + 1)` so its level-`m` union has measure at most `2⁻¹ ^ m`. -/
def universalMartinLofTest : MartinLofTest where
  cover m := {w | ∃ jn : ℕ × ℕ, w ∈ mlCappedList (ofNat Code jn.1, m + jn.1 + 1) jn.2}
  re := ComputablePred.rePred_exists computablePred_mem_mlCappedList
  measure_le m := by
    let U : Set (ℕ → Bool) := ⋃ j : ℕ,
      ⋃ w ∈ {w | ∃ n : ℕ, w ∈ mlCappedList (ofNat Code j, m + j + 1) n},
        prefixCylinderList w
    have hu : (⋃ w ∈ {w | ∃ jn : ℕ × ℕ,
        w ∈ mlCappedList (ofNat Code jn.1, m + jn.1 + 1) jn.2},
        prefixCylinderList w) = U := by
      ext x
      simp only [U, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
      exact ⟨fun ⟨w, ⟨⟨j, n⟩, hw⟩, hx⟩ => ⟨j, w, ⟨n, hw⟩, hx⟩,
        fun ⟨j, w, ⟨n, hw⟩, hx⟩ => ⟨w, ⟨⟨j, n⟩, hw⟩, hx⟩⟩
    rw [hu]
    calc Cslib.BitString.coinFlips U
      _ ≤ ∑' j : ℕ, Cslib.BitString.coinFlips
          (⋃ w ∈ {w | ∃ n : ℕ, w ∈ mlCappedList (ofNat Code j, m + j + 1) n},
            prefixCylinderList w) := measure_iUnion_le _
      _ ≤ ∑' j : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (m + j + 1) :=
          tsum_le_tsum fun j => coinFlips_iUnion_mlCapped_le (ofNat Code j, m + j + 1)
      _ = (2 : ℝ≥0∞)⁻¹ ^ m := tsum_two_inv_pow_shift m

/-- **Universality of `universalMartinLofTest`**: every Martin-Löf test `T` has a constant index
shift `d` such that level `m + d` of `T` is contained in level `m` of
`universalMartinLofTest`. -/
theorem exists_subset_universalMartinLofTest (T : MartinLofTest) :
    ∃ d : ℕ, ∀ m : ℕ, T.cover (m + d) ⊆ universalMartinLofTest.cover m := by
  obtain ⟨e, he⟩ := rePred_iff_exists_code.mp T.re
  refine ⟨encode e + 1, fun m w hw => ?_⟩
  have hw' : w ∈ T.cover (m + encode e + 1) := by rwa [← add_assoc] at hw
  have hset : {u | (e.eval (encode (m + encode e + 1, u))).Dom} = T.cover (m + encode e + 1) :=
    Set.ext fun u => (he (m + encode e + 1, u)).symm
  have hle : Cslib.BitString.coinFlips
      (⋃ u ∈ {u | (e.eval (encode (m + encode e + 1, u))).Dom}, prefixCylinderList u) ≤
      (2 : ℝ≥0∞)⁻¹ ^ (m + encode e + 1) := by
    rw [hset]
    exact T.measure_le (m + encode e + 1)
  obtain ⟨n, hn⟩ :=
    mlCapped_eq_all_of_measure_le e (m + encode e + 1) hle ((he (m + encode e + 1, w)).mp hw')
  exact Set.mem_ofPred_eq.mpr ⟨(encode e, n), by simpa [ofNat_encode] using hn⟩

/-- An infinite sequence `x` is Martin-Löf random if and only if it passes
`universalMartinLofTest`. -/
theorem isMartinLofRandom_iff_passes_universalMartinLofTest (x : ℕ → Bool) :
    IsMartinLofRandom x ↔
      ∃ m : ℕ, x ∉ ⋃ w ∈ universalMartinLofTest.cover m, prefixCylinderList w :=
  ⟨fun hx => hx universalMartinLofTest, fun ⟨m, hm⟩ T =>
    let ⟨d, hd⟩ := exists_subset_universalMartinLofTest T
    ⟨m + d, fun hx => hm (Set.iUnion₂_mono' (fun w hw => ⟨w, hd m hw, Set.Subset.rfl⟩) hx)⟩⟩

/-- **Full measure of Martin-Löf randomness**: `coinFlips`-almost every infinite binary sequence
is Martin-Löf random. -/
theorem ae_isMartinLofRandom : ∀ᵐ x ∂Cslib.BitString.coinFlips, IsMartinLofRandom x := by
  have hN_zero : Cslib.BitString.coinFlips
      (⋂ m : ℕ, ⋃ w ∈ universalMartinLofTest.cover m, prefixCylinderList w) = 0 :=
    le_antisymm (le_of_tendsto_of_tendsto' tendsto_const_nhds
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num))
      fun m => (measure_mono (Set.iInter_subset _ m)).trans (universalMartinLofTest.measure_le m))
      bot_le
  rw [ae_iff]
  convert hN_zero using 2
  ext x
  simp [isMartinLofRandom_iff_passes_universalMartinLofTest]

/-! ### The Levin–Schnorr theorem -/

private def compressCand (arg : (ℕ × List Bool) × ℕ) : Bool :=
  match DescriptionMethod.universalPrefixCand arg.2 with
  | Option.none => false
  | some p =>
    decide ((decode (α := List Bool) p.2).getD [] = arg.1.2 ∧
      p.1.length + arg.1.1 ≤ arg.1.2.length)

private theorem primrec_compressCand : Primrec compressCand := by
  have hbranch : Primrec₂ fun (arg : (ℕ × List Bool) × ℕ) (p : List Bool × ℕ) =>
      decide ((decode (α := List Bool) p.2).getD [] = arg.1.2 ∧
        p.1.length + arg.1.1 ≤ arg.1.2.length) := by
    have hget : Primrec fun q : ((ℕ × List Bool) × ℕ) × (List Bool × ℕ) =>
        (decode (α := List Bool) q.2.2).getD [] :=
      Primrec.option_getD.comp (Primrec.decode.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.const [])
    have heq : Primrec fun q : ((ℕ × List Bool) × ℕ) × (List Bool × ℕ) =>
        decide ((decode (α := List Bool) q.2.2).getD [] = q.1.1.2) :=
      Primrec.eq.decide.comp hget (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
    have hlen : Primrec fun q : ((ℕ × List Bool) × ℕ) × (List Bool × ℕ) =>
        decide (q.2.1.length + q.1.1.1 ≤ q.1.1.2.length) :=
      Primrec.nat_le.decide.comp
        (Primrec.nat_add.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
        (Primrec.list_length.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
    exact Primrec₂.mk <| (Primrec.and.comp heq hlen).of_eq fun q => by simp
  refine (Primrec.option_casesOn
    (DescriptionMethod.primrec_universalPrefixCand.comp Primrec.snd)
    (Primrec.const false) hbranch).of_eq fun arg => ?_
  simp only [compressCand]
  cases DescriptionMethod.universalPrefixCand arg.2 <;> rfl

private theorem tsum_universalPrefixBits_ennreal_le_one :
    (∑' q : DescriptionMethod.universalPrefixBits.haltingSet,
      (2 : ℝ≥0∞)⁻¹ ^ (q : List Bool).length) ≤ 1 := by
  have hpow (n : ℕ) : (2 : ℝ≥0∞)⁻¹ ^ n = ENNReal.ofReal ((2 : ℝ)⁻¹ ^ n) := by
    rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_inv_of_pos (by positivity)]; norm_num
  simp_rw [hpow]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity)
    DescriptionMethod.isPrefixFree_universalPrefixBits.summable_two_inv_pow_length]
  exact ENNReal.ofReal_le_one.mpr
    DescriptionMethod.isPrefixFree_universalPrefixBits.tsum_two_inv_pow_length_le_one

/-- Compressibility Martin-Löf test at redundancy threshold `m`: words `w` compressed by at least
`m` bits under `universalPrefixBits`. -/
private def compressTest : MartinLofTest where
  cover m := {w | ∃ q : List Bool,
    DescriptionMethod.universalPrefixBits.Produces q w ∧ q.length + m ≤ w.length}
  re := by
    have hpred : ComputablePred (Function.uncurry fun (mw : ℕ × List Bool) (k : ℕ) =>
        compressCand (mw, k) = true) :=
      primrec_compressCand.to_comp.computablePred
    refine (ComputablePred.rePred_exists hpred).of_eq fun ⟨m, w⟩ => ?_
    constructor
    · rintro ⟨k, hk⟩
      cases hc : DescriptionMethod.universalPrefixCand k with
      | none => simp [compressCand, hc] at hk
      | some qn =>
        simp only [compressCand, hc, decide_eq_true_eq] at hk
        obtain ⟨hdec, hlen⟩ := hk
        have htab : qn ∈ DescriptionMethod.universalPrefixTable (k + 1) :=
          Nat.mem_distinctValues.mpr ⟨k, Nat.lt_succ_self k, hc⟩
        have hprod' := DescriptionMethod.mem_universalPrefixTable_produces htab
        exact ⟨qn.1, DescriptionMethod.map_produces_iff.mpr ⟨qn.2, hprod', hdec⟩, hlen⟩
    · rintro ⟨q, hprod, hlen⟩
      obtain ⟨n, hprod', hw⟩ := DescriptionMethod.map_produces_iff.mp hprod
      obtain ⟨t, ht⟩ := DescriptionMethod.produces_iff_exists_mem_universalPrefixTable.mp hprod'
      obtain ⟨k, -, hk⟩ := Nat.mem_distinctValues.mp ht
      refine ⟨k, ?_⟩
      simp [compressCand, Option.mem_def.mp hk, hw, hlen]
  measure_le m := by
    let H := {q : List Bool | ∃ w : List Bool,
      DescriptionMethod.universalPrefixBits.Produces q w ∧ q.length + m ≤ w.length}
    have hout : ∀ q : H, ∃ w : List Bool,
        DescriptionMethod.universalPrefixBits.Produces q.val w ∧ q.val.length + m ≤ w.length :=
      fun q => q.property
    choose out hout_prod hout_len using hout
    let S : Set (ℕ → Bool) := ⋃ w ∈ {w | ∃ q : List Bool,
      DescriptionMethod.universalPrefixBits.Produces q w ∧ q.length + m ≤ w.length},
      prefixCylinderList w
    have hsub : S ⊆ ⋃ q : H, prefixCylinderList (out q) := by
      refine Set.iUnion₂_subset fun w ⟨q, hqw, hlen⟩ => ?_
      have heq : out (⟨q, w, hqw, hlen⟩ : H) = w :=
        DescriptionMethod.Produces.unique (hout_prod (⟨q, w, hqw, hlen⟩ : H)) hqw
      rw [← heq]
      exact Set.subset_iUnion (fun q : H => prefixCylinderList (out q)) ⟨q, w, hqw, hlen⟩
    have htsum_H : (∑' q : H, (2 : ℝ≥0∞)⁻¹ ^ (q : List Bool).length) ≤ 1 := by
      have hsubH : H ⊆ DescriptionMethod.universalPrefixBits.haltingSet :=
        fun q ⟨w, hqw, _⟩ => ⟨w, hqw⟩
      let emb : H ↪ DescriptionMethod.universalPrefixBits.haltingSet :=
        ⟨fun q => ⟨q.val, hsubH q.property⟩, fun _ _ h => Subtype.ext
          (congrArg (fun z : DescriptionMethod.universalPrefixBits.haltingSet =>
            (z : List Bool)) h)⟩
      have hcomp :
          (∑' q : H, (2 : ℝ≥0∞)⁻¹ ^ (q : List Bool).length) ≤
            ∑' q : DescriptionMethod.universalPrefixBits.haltingSet,
              (2 : ℝ≥0∞)⁻¹ ^ (q : List Bool).length :=
        CompleteLattice.summable.tsum_le_tsum_of_inj emb emb.injective (fun _ _ => bot_le)
          (fun _ => le_rfl) CompleteLattice.summable
      exact hcomp.trans tsum_universalPrefixBits_ennreal_le_one
    calc Cslib.BitString.coinFlips S
      _ ≤ Cslib.BitString.coinFlips (⋃ q : H, prefixCylinderList (out q)) := measure_mono hsub
      _ ≤ ∑' q : H, Cslib.BitString.coinFlips (prefixCylinderList (out q)) := measure_iUnion_le _
      _ = ∑' q : H, (2 : ℝ≥0∞)⁻¹ ^ (out q).length := by
          congr 1; funext q
          rw [coinFlips_prefixCylinderList, ENNReal.inv_pow]
      _ ≤ ∑' q : H, (2 : ℝ≥0∞)⁻¹ ^ (q.val.length + m) :=
          tsum_le_tsum fun q => pow_le_pow_right_of_le_one' (by norm_num) (hout_len q)
      _ = (2 : ℝ≥0∞)⁻¹ ^ m * ∑' q : H, (2 : ℝ≥0∞)⁻¹ ^ q.val.length := by
          simp_rw [pow_add, mul_comm _ ((2 : ℝ≥0∞)⁻¹ ^ m), ENNReal.tsum_mul_left]
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ m * 1 := by gcongr
      _ = (2 : ℝ≥0∞)⁻¹ ^ m := mul_one _

/-- **Levin–Schnorr randomness theorem (converse direction)** [LiVitanyi2019],
[ShenUspenskyVereshchagin2017]: every Martin-Löf random infinite bit sequence `x` has prefix-free
incompressible initial segments `n ≤ K(x ↾ n) + c` for a uniform constant `c`. -/
theorem le_complexity_of_isMartinLofRandom {x : ℕ → Bool} (hx : IsMartinLofRandom x) :
    ∃ c : ℕ, ∀ n : ℕ,
      n ≤ DescriptionMethod.universalPrefixBits.complexity
        (List.ofFn fun i : Fin n => x i) + c := by
  obtain ⟨m, hm⟩ := hx compressTest
  refine ⟨m, fun n => ?_⟩
  by_contra! hlt
  let w : List Bool := List.ofFn fun i : Fin n => x i
  obtain ⟨q, hq, hqlen⟩ := DescriptionMethod.exists_length_eq_ecomplexity
    (DescriptionMethod.ecomplexity_universalPrefixBits_ne_top w)
  rw [← DescriptionMethod.natCast_complexity_universalPrefixBits, Nat.cast_inj] at hqlen
  dsimp only [w] at hqlen
  have hcomp : q.length + m ≤ w.length := by rw [List.length_ofFn, hqlen]; omega
  exact hm (Set.mem_iUnion₂.mpr
    ⟨w, ⟨q, hq, hcomp⟩, mem_prefixCylinderList.mpr fun _ => by simp [w]⟩)

/-- **Levin–Schnorr theorem**: an infinite bit sequence `x` is Martin-Löf random if and only if
every initial segment `x ↾ n` has prefix-free complexity at least `n - c` for some constant
`c`. -/
theorem isMartinLofRandom_iff_exists_le_complexity (x : ℕ → Bool) :
    IsMartinLofRandom x ↔
      ∃ c : ℕ, ∀ n : ℕ,
        n ≤ DescriptionMethod.universalPrefixBits.complexity
          (List.ofFn fun i : Fin n => x i) + c :=
  ⟨le_complexity_of_isMartinLofRandom, isMartinLofRandom_of_le_complexity⟩

/-- Extended-natural (`ℕ∞`) form of the **Levin–Schnorr theorem**. -/
theorem isMartinLofRandom_iff_exists_le_ecomplexity (x : ℕ → Bool) :
    IsMartinLofRandom x ↔
      ∃ c : ℕ, ∀ n : ℕ,
        (n : ℕ∞) ≤ DescriptionMethod.universalPrefixBits.ecomplexity
          (List.ofFn fun i : Fin n => x i) + c := by
  rw [isMartinLofRandom_iff_exists_le_complexity]
  refine exists_congr fun c => forall_congr' fun n => ?_
  rw [← DescriptionMethod.natCast_complexity_universalPrefixBits]
  exact_mod_cast Iff.rfl

/-- `universalPrefixBits` has a partial recursive evaluator. -/
theorem DescriptionMethod.isPartrec_universalPrefixBits :
    ∃ eval : List Bool →. List Bool, Partrec eval ∧
      ∀ p w, DescriptionMethod.universalPrefixBits.Produces p w ↔ w ∈ eval p := by
  obtain ⟨f, hf, hfU⟩ := DescriptionMethod.isPartrec_universalPrefix
  refine ⟨fun p => (f p).map fun n => (decode (α := List Bool) n).getD [],
    hf.map ((Primrec.option_getD.comp Primrec.decode (Primrec.const [])).to_comp.comp
      Computable.snd), fun p w => ?_⟩
  simp only [DescriptionMethod.universalPrefixBits, DescriptionMethod.map_produces_iff,
    Part.mem_map_iff, hfU]

private theorem exists_ecomplexity_le_universalPrefixBits
    {U : DescriptionMethod (List Bool)} (hU_min : U.MinorizesPrefixPartrec) :
    ∃ c : ℕ, ∀ w : List Bool,
      U.ecomplexity w ≤ DescriptionMethod.universalPrefixBits.ecomplexity w + c := by
  obtain ⟨evalBits, hevalBits, hprodBits⟩ := DescriptionMethod.isPartrec_universalPrefixBits
  exact hU_min.exists_ecomplexity_le_of_partrec_eval
    DescriptionMethod.isPrefixFree_universalPrefixBits hevalBits hprodBits

/-- **Machine-invariant Levin–Schnorr theorem**: for every prefix-free partial recursive description
method `U` on binary strings that minorizes all prefix-free partial recursive decoders,
`IsMartinLofRandom x` is equivalent to `n ≤ K_U(x ↾ n) + O(1)`. -/
theorem isMartinLofRandom_iff_exists_le_ecomplexity_of_optimal
    {U : DescriptionMethod (List Bool)} (hU_min : U.MinorizesPrefixPartrec)
    (hU_pf : U.IsPrefixFree) {eval : List Bool →. List Bool} (heval : Partrec eval)
    (hprod : ∀ p w, U.Produces p w ↔ w ∈ eval p) (x : ℕ → Bool) :
    IsMartinLofRandom x ↔
      ∃ c : ℕ, ∀ n : ℕ,
        (n : ℕ∞) ≤ U.ecomplexity (List.ofFn fun i : Fin n => x i) + c := by
  obtain ⟨c₁, hc₁⟩ :=
    DescriptionMethod.exists_ecomplexity_universalPrefixBits_le_of_partrec_eval hU_pf heval hprod
  obtain ⟨c₂, hc₂⟩ := exists_ecomplexity_le_universalPrefixBits hU_min
  let prefixOf (n : ℕ) := List.ofFn fun i : Fin n => x i
  rw [isMartinLofRandom_iff_exists_le_ecomplexity]
  constructor
  · exact fun ⟨c, hc⟩ => ⟨c + c₁, fun n =>
      calc (n : ℕ∞)
        _ ≤ DescriptionMethod.universalPrefixBits.ecomplexity (prefixOf n) + c := hc n
        _ ≤ (U.ecomplexity (prefixOf n) + c₁) + c := add_le_add_left (hc₁ _) _
        _ = U.ecomplexity (prefixOf n) + ((c + c₁ : ℕ) : ℕ∞) := by
            push_cast
            ac_rfl⟩
  · exact fun ⟨c, hc⟩ => ⟨c + c₂, fun n =>
      calc (n : ℕ∞)
        _ ≤ U.ecomplexity (prefixOf n) + c := hc n
        _ ≤ (DescriptionMethod.universalPrefixBits.ecomplexity (prefixOf n) + c₂) + c :=
            add_le_add_left (hc₂ _) _
        _ = DescriptionMethod.universalPrefixBits.ecomplexity (prefixOf n) +
              ((c + c₂ : ℕ) : ℕ∞) := by
            push_cast
            ac_rfl⟩

/-- Natural-number form of the **machine-invariant Levin–Schnorr theorem**. -/
theorem isMartinLofRandom_iff_exists_le_complexity_of_optimal
    {U : DescriptionMethod (List Bool)} (hU_min : U.MinorizesPrefixPartrec)
    (hU_pf : U.IsPrefixFree) {eval : List Bool →. List Bool} (heval : Partrec eval)
    (hprod : ∀ p w, U.Produces p w ↔ w ∈ eval p) (x : ℕ → Bool) :
    IsMartinLofRandom x ↔
      ∃ c : ℕ, ∀ n : ℕ,
        n ≤ U.complexity (List.ofFn fun i : Fin n => x i) + c := by
  obtain ⟨c₂, hc₂⟩ := exists_ecomplexity_le_universalPrefixBits hU_min
  have hfin : ∀ w : List Bool, U.ecomplexity w ≠ ⊤ := fun w =>
    ne_top_of_le_ne_top
      (by simp [DescriptionMethod.ecomplexity_universalPrefixBits_ne_top w])
      (hc₂ w)
  rw [isMartinLofRandom_iff_exists_le_ecomplexity_of_optimal hU_min hU_pf heval hprod]
  refine exists_congr fun c => forall_congr' fun n => ?_
  rw [← DescriptionMethod.natCast_complexity (hfin _)]
  exact_mod_cast Iff.rfl

/-! ### Solovay tests and equivalence with Martin-Löf randomness -/

/-- A **Solovay randomness test** [LiVitanyi2019, ShenUspenskyVereshchagin2017]: a computably
enumerable collection of binary prefixes whose cylinder measures have finite sum. -/
structure SolovayTest where
  /-- Set of binary prefixes comprising the Solovay test. -/
  cover : Set (List Bool)
  /-- Computable enumerability of membership in `cover`. -/
  re : REPred fun w : List Bool => w ∈ cover
  /-- Finite total dyadic measure of the cylinders generated by `cover`. -/
  tsum_lt_top : (∑' w : cover, (2 : ℝ≥0∞)⁻¹ ^ (w : List Bool).length) < ⊤

/-- A sequence `x : ℕ → Bool` **passes** the Solovay test `S` when it falls into only finitely
many cylinders generated by `S.cover`. -/
@[expose] def PassesSolovayTest (S : SolovayTest) (x : ℕ → Bool) : Prop :=
  {w ∈ S.cover | x ∈ prefixCylinderList w}.Finite

private def prefixCoverCount (L : List (List Bool)) (v : List Bool) : ℕ :=
  L.foldr (fun w acc => if w <+: v then acc + 1 else acc) 0

private theorem prefixCoverCount_eq_countP (L : List (List Bool)) (v : List Bool) :
    prefixCoverCount L v = L.countP (fun w => decide (w <+: v)) := by
  induction L with
  | nil => rfl
  | cons a rest ih =>
    simp only [prefixCoverCount, List.foldr_cons, List.countP_cons]
    change (if a <+: v then prefixCoverCount rest v + 1 else prefixCoverCount rest v) = _
    rw [ih]
    split_ifs with h <;> simp_all

private theorem primrec₂_prefixCoverCount : Primrec₂ prefixCoverCount := by
  have hpred : PrimrecPred fun arg : (List (List Bool) × List Bool) × (List Bool × ℕ) =>
      arg.2.1 <+: arg.1.2 :=
    Primrec.list_isPrefix.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.fst)
  have hh : Primrec₂ fun (Lv : List (List Bool) × List Bool) (wacc : List Bool × ℕ) =>
      if wacc.1 <+: Lv.2 then wacc.2 + 1 else wacc.2 :=
    Primrec₂.mk <| Primrec.ite hpred
      (Primrec.succ.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  exact Primrec₂.mk <| (Primrec.list_foldr Primrec.fst (Primrec.const 0) hh).of_eq fun _ => rfl

private theorem prefixCoverCount_eq_card_filter {L : List (List Bool)} {v : List Bool}
    (hnd : L.Nodup) (hle : ∀ w ∈ L, w.length ≤ v.length) {x : ℕ → Bool}
    (hx : x ∈ prefixCylinderList v) [DecidablePred fun w => x ∈ prefixCylinderList w] :
    prefixCoverCount L v =
      (L.toFinset.filter fun w => x ∈ prefixCylinderList w).card := by
  rw [prefixCoverCount_eq_countP, hnd.card_eq_countP]
  refine List.countP_congr fun w hw => ?_
  simp only [decide_eq_true_eq]
  refine ⟨fun h => prefixCylinderList_subset_of_isPrefix h hx, fun hxw => ?_⟩
  rw [mem_prefixCylinderList] at hx hxw
  rw [List.prefix_iff_eq_take]
  refine List.ext_getElem (by simp [hle w hw]) fun i hi1 _ => ?_
  have hiw : i < w.length := by simpa using hi1
  simp only [List.getElem_take]
  exact (hxw ⟨i, hiw⟩).symm.trans (hx ⟨i, hiw.trans_le (hle w hw)⟩)

private theorem nodup_reWords (e : Code) (n : ℕ) : (reWords e n).Nodup :=
  Nat.nodup_distinctValues (reCand e) n

private def solovayMLCand (e : Code) (K : ℕ) (arg : (ℕ × List Bool) × ℕ) : Bool :=
  decide (arg.1.2.length = prefixUnionMaxLen (reWords e arg.2)) &&
    decide (K * 2 ^ arg.1.1 ≤ prefixCoverCount (reWords e arg.2) arg.1.2)

private theorem primrec_solovayMLCand (e : Code) (K : ℕ) :
    Primrec (solovayMLCand e K) := by
  have hL : Primrec fun arg : (ℕ × List Bool) × ℕ => reWords e arg.2 :=
    primrec₂_reWords.comp (Primrec.const e) Primrec.snd
  exact (Primrec.and.comp
    (Primrec.eq.decide.comp (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst))
      (primrec_prefixUnionMaxLen.comp hL))
    (Primrec.nat_le.decide.comp
      (Primrec.nat_mul.comp (Primrec.const K)
        (primrec_two_pow.comp (Primrec.fst.comp Primrec.fst)))
      (primrec₂_prefixCoverCount.comp hL (Primrec.snd.comp Primrec.fst)))).of_eq fun _ => rfl

private def solovayToMLTest (S : SolovayTest) (e : Code)
    (he : ∀ w, w ∈ S.cover ↔ (e.eval (encode w)).Dom) (K : ℕ) (hK_pos : 1 ≤ K)
    (hK_sum : (∑' w : S.cover, (2 : ℝ≥0∞)⁻¹ ^ (w : List Bool).length) ≤ K) :
    MartinLofTest where
  cover m := {v | ∃ n : ℕ,
    v ∈ Cslib.BitString.enumList (prefixUnionMaxLen (reWords e n)) ∧
      K * 2 ^ m ≤ prefixCoverCount (reWords e n) v}
  re := by
    have hpred : ComputablePred (Function.uncurry fun (mv : ℕ × List Bool) (n : ℕ) =>
        solovayMLCand e K (mv, n) = true) :=
      ((primrec_solovayMLCand e K).to_comp.comp
        (Computable.pair Computable.fst Computable.snd)).computablePred
    refine (ComputablePred.rePred_exists hpred).of_eq fun ⟨m, v⟩ => ?_
    simp [solovayMLCand, Cslib.BitString.mem_enumList]
  measure_le m := by
    classical
    let U : ℕ → Set (ℕ → Bool) := fun n =>
      ⋃ v ∈ {v | v ∈ Cslib.BitString.enumList (prefixUnionMaxLen (reWords e n)) ∧
          K * 2 ^ m ≤ prefixCoverCount (reWords e n) v}, prefixCylinderList v
    have hU_eq : (⋃ v ∈ {v | ∃ n : ℕ,
        v ∈ Cslib.BitString.enumList (prefixUnionMaxLen (reWords e n)) ∧
          K * 2 ^ m ≤ prefixCoverCount (reWords e n) v}, prefixCylinderList v) =
        ⋃ n : ℕ, U n := by
      ext x
      simp only [U, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
      exact ⟨fun ⟨v, ⟨n, hn⟩, hx⟩ => ⟨n, v, hn, hx⟩, fun ⟨n, v, hn, hx⟩ => ⟨v, ⟨n, hn⟩, hx⟩⟩
    have hcard_char : ∀ n x, x ∈ U n →
        K * 2 ^ m ≤ ((reWords e n).toFinset.filter fun w => x ∈ prefixCylinderList w).card := by
      intro n x hx
      obtain ⟨v, ⟨hv_enum, hv_cnt⟩, hxv⟩ := Set.mem_iUnion₂.mp hx
      have hv_len := Cslib.BitString.length_of_mem_enumList hv_enum
      have hle : ∀ w ∈ reWords e n, w.length ≤ v.length := fun w hw => by
        rw [hv_len]
        exact length_le_prefixUnionMaxLen hw
      rw [← prefixCoverCount_eq_card_filter (nodup_reWords e n) hle hxv]
      exact hv_cnt
    have hU_mono : Monotone U := by
      intro a b hab x hx
      have hcnt : K * 2 ^ m ≤
          ((reWords e a).toFinset.filter fun w => x ∈ prefixCylinderList w).card :=
        hcard_char a x hx
      have hsub_fin : (reWords e a).toFinset.filter (fun w => x ∈ prefixCylinderList w) ⊆
          (reWords e b).toFinset.filter (fun w => x ∈ prefixCylinderList w) :=
        Finset.filter_subset_filter _ fun w hw => List.mem_toFinset.mpr
          ((Nat.distinctValues_prefix (reCand e) hab).subset (List.mem_toFinset.mp hw))
      have hcnt_b : K * 2 ^ m ≤
          ((reWords e b).toFinset.filter fun w => x ∈ prefixCylinderList w).card :=
        hcnt.trans (Finset.card_le_card hsub_fin)
      let Mb := prefixUnionMaxLen (reWords e b)
      let v : List Bool := List.ofFn fun i : Fin Mb => x i
      refine Set.mem_iUnion₂.mpr ⟨v, ⟨Cslib.BitString.mem_enumList.mpr (by simp [v, Mb]), ?_⟩,
        mem_prefixCylinderList.mpr fun i => by simp [v]⟩
      have hxv : x ∈ prefixCylinderList v := mem_prefixCylinderList.mpr fun i => by simp [v]
      have hle : ∀ w ∈ reWords e b, w.length ≤ v.length := fun w hw => by
        simp only [v, List.length_ofFn, Mb]
        exact length_le_prefixUnionMaxLen hw
      rw [prefixCoverCount_eq_card_filter (nodup_reWords e b) hle hxv]
      exact hcnt_b
    have hU_le : ∀ n : ℕ, Cslib.BitString.coinFlips (U n) ≤ (2 : ℝ≥0∞)⁻¹ ^ m := by
      intro n
      let Lfin := (reWords e n).toFinset
      let g : (ℕ → Bool) → ℝ≥0∞ :=
        fun x => ∑ w ∈ Lfin, (prefixCylinderList w).indicator (fun _ => (1 : ℝ≥0∞)) x
      have hg_meas : Measurable g :=
        Finset.measurable_sum Lfin fun w _ =>
          (measurable_const).indicator (measurableSet_prefixCylinderList w)
      have hg_ge : ∀ x ∈ U n, ((K * 2 ^ m : ℕ) : ℝ≥0∞) ≤ g x := by
        intro x hx
        have hg_card : g x = ((Lfin.filter fun w => x ∈ prefixCylinderList w).card : ℝ≥0∞) := by
          simp only [g, Set.indicator_apply, Finset.sum_boole]
        rw [hg_card]
        exact_mod_cast hcard_char n x hx
      have hint_U : ((K * 2 ^ m : ℕ) : ℝ≥0∞) * Cslib.BitString.coinFlips (U n) ≤
          ∫⁻ x, g x ∂Cslib.BitString.coinFlips := by
        calc ((K * 2 ^ m : ℕ) : ℝ≥0∞) * Cslib.BitString.coinFlips (U n)
          _ = ∫⁻ _ in U n, ((K * 2 ^ m : ℕ) : ℝ≥0∞) ∂Cslib.BitString.coinFlips := by
              rw [setLIntegral_const]
          _ ≤ ∫⁻ x in U n, g x ∂Cslib.BitString.coinFlips :=
              setLIntegral_mono hg_meas fun x hx => hg_ge x hx
          _ ≤ ∫⁻ x, g x ∂Cslib.BitString.coinFlips :=
              lintegral_mono' Measure.restrict_le_self le_rfl
      have hsub_cov : (Lfin : Set (List Bool)) ⊆ S.cover := fun w hw =>
        (he w).mpr (exists_mem_reWords_iff_dom.mp ⟨n, List.mem_toFinset.mp hw⟩)
      let emb : Lfin ↪ S.cover :=
        ⟨fun w => ⟨w.val, hsub_cov w.property⟩, fun _ _ h => Subtype.ext
          (congrArg (fun z : S.cover => (z : List Bool)) h)⟩
      have hint_g : ∫⁻ x, g x ∂Cslib.BitString.coinFlips ≤ (K : ℝ≥0∞) := by
        calc ∫⁻ x, g x ∂Cslib.BitString.coinFlips
          _ = ∑ w ∈ Lfin, ∫⁻ x, (prefixCylinderList w).indicator (fun _ => (1 : ℝ≥0∞)) x
                ∂Cslib.BitString.coinFlips := by
              simp only [g]
              exact lintegral_finsetSum Lfin fun w _ =>
                measurable_const.indicator (measurableSet_prefixCylinderList w)
          _ = ∑ w ∈ Lfin, Cslib.BitString.coinFlips (prefixCylinderList w) := by
              refine Finset.sum_congr rfl fun w _ => ?_
              rw [lintegral_indicator (measurableSet_prefixCylinderList w), setLIntegral_one]
          _ = ∑ w ∈ Lfin, (2 : ℝ≥0∞)⁻¹ ^ w.length := by
              refine Finset.sum_congr rfl fun w _ => ?_
              rw [coinFlips_prefixCylinderList, ENNReal.inv_pow]
          _ = ∑ w ∈ (Finset.univ.map emb : Finset S.cover),
                (2 : ℝ≥0∞)⁻¹ ^ (w : List Bool).length := by
              rw [Finset.sum_map, ← Finset.sum_coe_sort Lfin _]
              rfl
          _ ≤ ∑' w : S.cover, (2 : ℝ≥0∞)⁻¹ ^ (w : List Bool).length := sum_le_tsum _
          _ ≤ K := hK_sum
      have hint_mul : ((K * 2 ^ m : ℕ) : ℝ≥0∞) * Cslib.BitString.coinFlips (U n) ≤ K :=
        hint_U.trans hint_g
      have hK_ne0 : (K : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hK_netop : (K : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top K
      have hinvK : (K : ℝ≥0∞)⁻¹ * K = 1 := ENNReal.inv_mul_cancel hK_ne0 hK_netop
      have hinv2 : (2 : ℝ≥0∞)⁻¹ ^ m * (2 : ℝ≥0∞) ^ m = 1 := by
        rw [← mul_pow, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_pow]
      calc Cslib.BitString.coinFlips (U n)
        _ = (2 : ℝ≥0∞)⁻¹ ^ m * (K : ℝ≥0∞)⁻¹ *
              (((K * 2 ^ m : ℕ) : ℝ≥0∞) * Cslib.BitString.coinFlips (U n)) := by
            rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_assoc ((2 : ℝ≥0∞)⁻¹ ^ m) _ _,
              ← mul_assoc (K : ℝ≥0∞)⁻¹ _ _, ← mul_assoc (K : ℝ≥0∞)⁻¹ (K : ℝ≥0∞) _, hinvK,
              one_mul, ← mul_assoc _ ((2 : ℝ≥0∞) ^ m) _, hinv2, one_mul]
        _ ≤ (2 : ℝ≥0∞)⁻¹ ^ m * (K : ℝ≥0∞)⁻¹ * K := by gcongr
        _ = (2 : ℝ≥0∞)⁻¹ ^ m := by rw [mul_assoc, hinvK, mul_one]
    rw [hU_eq]
    exact le_of_tendsto (MeasureTheory.tendsto_measure_iUnion_atTop hU_mono)
      (Eventually.of_forall hU_le)

/-- Every Martin-Löf random sequence passes every Solovay test. -/
theorem passesSolovayTest_of_isMartinLofRandom (S : SolovayTest) {x : ℕ → Bool}
    (hx : IsMartinLofRandom x) : PassesSolovayTest S x := by
  classical
  obtain ⟨e, he⟩ := rePred_iff_exists_code.mp S.re
  obtain ⟨K₀, hK₀⟩ := ENNReal.exists_nat_gt S.tsum_lt_top.ne
  let K : ℕ := K₀ + 1
  have hK_sum : (∑' w : S.cover, (2 : ℝ≥0∞)⁻¹ ^ (w : List Bool).length) ≤ K :=
    hK₀.le.trans (by exact_mod_cast Nat.le_succ K₀)
  obtain ⟨m, hm⟩ := hx (solovayToMLTest S e he K (by omega) hK_sum)
  by_contra hinf
  rw [PassesSolovayTest, Set.not_finite] at hinf
  obtain ⟨F, hF_sub, hF_card⟩ := hinf.exists_subset_card_eq (K * 2 ^ m)
  choose fn hfn using fun w : F =>
    exists_mem_reWords_iff_dom.mpr ((he w.val).mp (hF_sub w.property).1)
  let N : ℕ := F.attach.sup fn
  let v : List Bool := List.ofFn fun i : Fin (prefixUnionMaxLen (reWords e N)) => x i
  have hxv : x ∈ prefixCylinderList v := mem_prefixCylinderList.mpr fun _ => by simp [v]
  have hle : ∀ w ∈ reWords e N, w.length ≤ v.length := fun w hw => by
    simpa [v] using length_le_prefixUnionMaxLen hw
  have hsub_filter : F ⊆ (reWords e N).toFinset.filter fun w => x ∈ prefixCylinderList w :=
    fun w hw => Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr <|
      (Nat.distinctValues_prefix (reCand e)
        (Finset.le_sup (f := fn) (Finset.mem_attach F ⟨w, hw⟩))).subset (hfn ⟨w, hw⟩),
      (hF_sub hw).2⟩
  refine hm (Set.mem_iUnion₂.mpr ⟨v, ⟨N, Cslib.BitString.mem_enumList.mpr (by simp [v]), ?_⟩, hxv⟩)
  rw [prefixCoverCount_eq_card_filter (nodup_reWords e N) hle hxv]
  exact hF_card.symm.trans_le (Finset.card_le_card hsub_filter)

private def carveTail : List Bool → List (List Bool)
  | [] => []
  | b :: rest => [!b] :: (carveTail rest).map (b :: ·)

private theorem primrec_carveTail : Primrec carveTail := by
  let step : Bool → List Bool → List (List Bool) → List (List Bool) :=
    fun b _ IH => [!b] :: IH.map (b :: ·)
  have hh : Primrec₂ fun (_ : List Bool) (blIH : Bool × List Bool × List (List Bool)) =>
      step blIH.1 blIH.2.1 blIH.2.2 := by
    have hmap : Primrec fun p : List Bool × (Bool × List Bool × List (List Bool)) =>
        p.2.2.2.map (p.2.1 :: ·) :=
      Primrec.list_map (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
        (Primrec₂.mk <| Primrec.list_cons.comp
          (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)
    exact Primrec₂.mk <| Primrec.list_cons.comp
      (Primrec.list_cons.comp
        (Primrec.not.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.const []))
      hmap
  refine (Primrec.list_rec Primrec.id (Primrec.const []) hh).of_eq fun s => ?_
  change List.recOn s [] step = carveTail s
  induction s with
  | nil => rfl
  | cons b rest ih =>
    change step b rest (List.recOn rest [] step) = [!b] :: (carveTail rest).map (b :: ·)
    rw [ih]

private def carveOut (u w : List Bool) : List (List Bool) :=
  if u <+: w then []
  else if w <+: u then (carveTail (u.drop w.length)).map (w ++ ·)
  else [w]

private theorem primrec₂_carveOut : Primrec₂ carveOut := by
  have htail : Primrec fun uw : List Bool × List Bool =>
      (carveTail (uw.1.drop uw.2.length)).map (uw.2 ++ ·) :=
    Primrec.list_map
      (primrec_carveTail.comp
        (Primrec.list_drop.comp (Primrec.list_length.comp Primrec.snd) Primrec.fst))
      (Primrec₂.mk <| Primrec.list_append.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
  have hinner : Primrec fun uw : List Bool × List Bool =>
      if uw.2 <+: uw.1 then (carveTail (uw.1.drop uw.2.length)).map (uw.2 ++ ·) else [uw.2] :=
    Primrec.ite (Primrec.list_isPrefix.comp Primrec.snd Primrec.fst) htail
      (Primrec.list_cons.comp Primrec.snd (Primrec.const []))
  exact Primrec₂.mk <| Primrec.ite (Primrec.list_isPrefix.comp Primrec.fst Primrec.snd)
    (Primrec.const []) hinner

private theorem prefixDisjoint_cons_cons {a : Bool} {s t : List Bool}
    (h : PrefixDisjoint s t) : PrefixDisjoint (a :: s) (a :: t) :=
  ⟨fun hp => h.1 (List.cons_prefix_cons.mp hp).2, fun hp => h.2 (List.cons_prefix_cons.mp hp).2⟩

private theorem prefixDisjoint_not_cons (b : Bool) (s t : List Bool) :
    PrefixDisjoint (b :: s) ((!b) :: t) := by
  refine ⟨fun hp => ?_, fun hp => ?_⟩
  · have h := (List.cons_prefix_cons.mp hp).1
    cases b <;> cases h
  · have h := (List.cons_prefix_cons.mp hp).1
    cases b <;> cases h

private theorem carveTail_spec (s : List Bool) :
    (∀ t ∈ carveTail s, PrefixDisjoint s t) ∧ (carveTail s).Pairwise PrefixDisjoint := by
  induction s with
  | nil => simp [carveTail]
  | cons b rest ih =>
    rcases ih with ⟨hdisj, hpair⟩
    refine ⟨fun t ht => ?_, ?_⟩
    · simp only [carveTail, List.mem_cons, List.mem_map] at ht
      rcases ht with rfl | ⟨t', ht', rfl⟩
      · exact prefixDisjoint_not_cons b rest []
      · exact prefixDisjoint_cons_cons (hdisj t' ht')
    · simp only [carveTail, List.pairwise_cons]
      refine ⟨fun t ht => ?_, hpair.map _ fun _ _ h => prefixDisjoint_cons_cons h⟩
      obtain ⟨t', _, rfl⟩ := List.mem_map.mp ht
      exact (prefixDisjoint_not_cons b t' []).symm

private theorem mem_prefixCylinderList_append_singleton {y : ℕ → Bool} {w : List Bool} {b : Bool} :
    y ∈ prefixCylinderList (w ++ [b]) ↔ y ∈ prefixCylinderList w ∧ y w.length = b := by
  constructor
  · intro hy
    refine ⟨prefixCylinderList_subset_of_isPrefix (List.prefix_append _ _) hy, ?_⟩
    simpa [List.getElem_append_right] using mem_prefixCylinderList.mp hy ⟨w.length, by simp⟩
  · rintro ⟨hyw, hyb⟩
    rw [mem_prefixCylinderList] at hyw ⊢
    intro ⟨i, hi⟩
    by_cases hlt : i < w.length
    · simpa [List.getElem_append_left hlt] using hyw ⟨i, hlt⟩
    · have heq : i = w.length := by
        simp only [List.length_append, List.length_singleton] at hi; omega
      subst heq
      simpa [List.getElem_append_right] using hyb

private theorem mem_carveTail_cylinder_iff (s w : List Bool) (y : ℕ → Bool) :
    (∃ t ∈ carveTail s, y ∈ prefixCylinderList (w ++ t)) ↔
      y ∈ prefixCylinderList w ∧ y ∉ prefixCylinderList (w ++ s) := by
  induction s generalizing w with
  | nil =>
    simp [carveTail]
  | cons b rest ih =>
    have hrw : w ++ (b :: rest) = (w ++ [b]) ++ rest := (List.append_assoc w [b] rest).symm
    constructor
    · rintro ⟨t, ht, hyt⟩
      simp only [carveTail, List.mem_cons, List.mem_map] at ht
      rcases ht with rfl | ⟨t', ht', rfl⟩
      · rw [mem_prefixCylinderList_append_singleton] at hyt
        refine ⟨hyt.1, fun hyu => ?_⟩
        rw [hrw] at hyu
        have hywb := (mem_prefixCylinderList_append_singleton.mp
          (prefixCylinderList_subset_of_isPrefix (List.prefix_append _ _) hyu)).2
        rw [hyt.2] at hywb
        cases b <;> cases hywb
      · rw [show w ++ b :: t' = (w ++ [b]) ++ t' from (List.append_assoc w [b] t').symm] at hyt
        obtain ⟨hywb, hnot⟩ := (ih (w ++ [b])).mp ⟨t', ht', hyt⟩
        exact ⟨prefixCylinderList_subset_of_isPrefix (List.prefix_append _ _) hywb, by rwa [hrw]⟩
    · rintro ⟨hyw, hynot⟩
      by_cases hyb : y w.length = b
      · obtain ⟨t', ht', hyt'⟩ := (ih (w ++ [b])).mpr
          ⟨mem_prefixCylinderList_append_singleton.mpr ⟨hyw, hyb⟩, by rwa [← hrw]⟩
        refine ⟨b :: t', List.mem_cons_of_mem _ (List.mem_map.mpr ⟨t', ht', rfl⟩), ?_⟩
        rwa [show w ++ b :: t' = (w ++ [b]) ++ t' from (List.append_assoc w [b] t').symm]
      · refine ⟨[!b], List.mem_cons_self, mem_prefixCylinderList_append_singleton.mpr ⟨hyw, ?_⟩⟩
        cases b <;> cases h : y w.length <;> simp_all

private theorem prefixDisjoint_append_left {w s t : List Bool} (h : PrefixDisjoint s t) :
    PrefixDisjoint (w ++ s) (w ++ t) :=
  ⟨fun hp => h.1 ((List.prefix_append_right_inj w).mp hp),
    fun hp => h.2 ((List.prefix_append_right_inj w).mp hp)⟩

private theorem carveOut_spec (u w : List Bool) :
    (∀ v ∈ carveOut u w, w <+: v ∧ PrefixDisjoint u v) ∧
      (carveOut u w).Pairwise PrefixDisjoint ∧
      ⋃ v ∈ carveOut u w, prefixCylinderList v =
        prefixCylinderList w \ prefixCylinderList u := by
  by_cases huw : u <+: w
  · refine ⟨fun v hv => by simp [carveOut, huw] at hv,
      by simp [carveOut, huw], ?_⟩
    simp only [carveOut, huw, ↓reduceIte, List.not_mem_nil, Set.iUnion_false, Set.iUnion_empty]
    exact (Set.sdiff_eq_empty.mpr (prefixCylinderList_subset_of_isPrefix huw)).symm
  · by_cases hwu : w <+: u
    · simp only [carveOut, huw, ↓reduceIte, hwu]
      have hus : w ++ u.drop w.length = u := by
        conv_rhs => rw [← List.take_append_drop w.length u, ← List.prefix_iff_eq_take.mp hwu]
      obtain ⟨hdisj, hpair⟩ := carveTail_spec (u.drop w.length)
      refine ⟨fun v hv => ?_, hpair.map _ fun _ _ h => prefixDisjoint_append_left h, ?_⟩
      · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hv
        exact ⟨List.prefix_append _ _, hus ▸ prefixDisjoint_append_left (hdisj t ht)⟩
      · ext y
        simp only [Set.mem_iUnion, List.mem_map, exists_prop, Set.mem_sdiff]
        conv_rhs => rw [← hus]
        rw [← mem_carveTail_cylinder_iff]
        exact ⟨fun ⟨_, ⟨t, ht, rfl⟩, hy⟩ => ⟨t, ht, hy⟩,
          fun ⟨t, ht, hy⟩ => ⟨w ++ t, ⟨t, ht, rfl⟩, hy⟩⟩
    · simp only [carveOut, huw, ↓reduceIte, hwu, List.mem_singleton, List.pairwise_singleton,
        Set.iUnion_iUnion_eq_left]
      have hduw : PrefixDisjoint u w := ⟨huw, hwu⟩
      refine ⟨fun v hv => ?_, trivial,
        (disjoint_prefixCylinderList_of_prefixDisjoint hduw.symm).sdiff_eq_left.symm⟩
      rw [hv]
      exact ⟨List.prefix_refl w, hduw⟩

private def carveOutSeen (w : List Bool) : List (List Bool) → List (List Bool)
  | [] => [w]
  | u :: rest => (carveOutSeen w rest).flatMap (carveOut u)

private theorem primrec₂_carveOutSeen : Primrec₂ carveOutSeen := by
  let step : List Bool → List (List Bool) → List (List Bool) → List (List Bool) :=
    fun u _ IH => IH.flatMap (carveOut u)
  have hh : Primrec₂ fun (_ : List Bool × List (List Bool))
      (uAcc : List Bool × List (List Bool) × List (List Bool)) =>
      step uAcc.1 uAcc.2.1 uAcc.2.2 :=
    Primrec₂.mk <| Primrec.list_flatMap
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
      (Primrec₂.mk <| primrec₂_carveOut.comp
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)
  refine Primrec₂.mk <| (Primrec.list_rec Primrec.snd
    (Primrec.list_cons.comp Primrec.fst (Primrec.const [])) hh).of_eq fun ⟨w, seen⟩ => ?_
  induction seen with
  | nil => rfl
  | cons u rest ih =>
    change step u rest (@List.recOn (List Bool) (fun _ => List (List Bool)) rest [w] step) = _
    rw [ih]; rfl

private theorem prefixDisjoint_of_prefix_right {u v t : List Bool} (huv : PrefixDisjoint u v)
    (hvt : v <+: t) : PrefixDisjoint u t :=
  (huv.symm.of_prefix_left hvt).symm

private theorem carveOutSeen_spec (w : List Bool) (seen : List (List Bool)) :
    (∀ v ∈ carveOutSeen w seen, w <+: v ∧ ∀ u ∈ seen, PrefixDisjoint u v) ∧
      (carveOutSeen w seen).Pairwise PrefixDisjoint ∧
      ⋃ v ∈ carveOutSeen w seen, prefixCylinderList v =
        prefixCylinderList w \ ⋃ u ∈ seen, prefixCylinderList u := by
  induction seen with
  | nil =>
    simp [carveOutSeen]
  | cons u rest ih =>
    rcases ih with ⟨hprop, hpair, hunion⟩
    simp only [carveOutSeen]
    refine ⟨fun v hv => ?_, ?_, ?_⟩
    · obtain ⟨t, ht, hvt⟩ := List.mem_flatMap.mp hv
      have ⟨hwt, hrest⟩ := hprop t ht
      have ⟨htv, huv⟩ := (carveOut_spec u t).1 v hvt
      refine ⟨hwt.trans htv, fun r hr => ?_⟩
      rcases List.mem_cons.mp hr with rfl | hr'
      · exact huv
      · exact prefixDisjoint_of_prefix_right (hrest r hr') htv
    · rw [List.pairwise_flatMap]
      refine ⟨fun t _ => (carveOut_spec u t).2.1, hpair.imp fun {t₁ t₂} hdisj v₁ hv₁ v₂ hv₂ =>
        prefixDisjoint_of_prefix_right (hdisj.of_prefix_left ((carveOut_spec u t₁).1 v₁ hv₁).1)
          ((carveOut_spec u t₂).1 v₂ hv₂).1⟩
    · calc (⋃ v ∈ (carveOutSeen w rest).flatMap (carveOut u), prefixCylinderList v)
        _ = ⋃ t ∈ carveOutSeen w rest, ⋃ v ∈ carveOut u t, prefixCylinderList v := by
            ext y
            simp only [Set.mem_iUnion, List.mem_flatMap, exists_prop]
            exact ⟨fun ⟨v, ⟨t, ht, hv⟩, hy⟩ => ⟨t, ht, v, hv, hy⟩,
              fun ⟨t, ht, v, hv, hy⟩ => ⟨v, ⟨t, ht, hv⟩, hy⟩⟩
        _ = ⋃ t ∈ carveOutSeen w rest, prefixCylinderList t \ prefixCylinderList u :=
            Set.iUnion₂_congr fun t _ => (carveOut_spec u t).2.2
        _ = (⋃ t ∈ carveOutSeen w rest, prefixCylinderList t) \ prefixCylinderList u := by
            ext y
            simp only [Set.mem_sdiff, Set.mem_iUnion, exists_prop]
            exact ⟨fun ⟨t, ht, hyt, hyu⟩ => ⟨⟨t, ht, hyt⟩, hyu⟩,
              fun ⟨⟨t, ht, hyt⟩, hyu⟩ => ⟨t, ht, hyt, hyu⟩⟩
        _ = (prefixCylinderList w \ ⋃ r ∈ rest, prefixCylinderList r) \ prefixCylinderList u := by
            rw [hunion]
        _ = prefixCylinderList w \ ⋃ r ∈ u :: rest, prefixCylinderList r := by
            ext y
            simp only [Set.mem_sdiff, Set.mem_iUnion, exists_prop, List.mem_cons,
              or_and_right, exists_or, exists_eq_left, not_or, not_exists]
            tauto

private def levelCandWord (e : Code) (m j : ℕ) : Option (List Bool) :=
  (decode (α := List Bool × ℕ) j).bind fun wf =>
    (Code.evaln wf.2 e (encode (m, wf.1))).map fun _ => wf.1

private theorem primrec₂_levelCandWord (e : Code) : Primrec₂ (levelCandWord e) :=
  Primrec₂.mk <| (primrec₂_mlCand.comp
    (Primrec.pair (Primrec.const e) Primrec.fst) Primrec.snd).of_eq fun _ => rfl

private def mlDisjStep (e : Code) (k j : ℕ) (acc : List (List Bool)) : List (List Bool) :=
  match levelCandWord e (k + 1) j with
  | Option.none => acc
  | some w => acc ++ carveOutSeen w acc

private def mlDisjList (e : Code) (k : ℕ) : ℕ → List (List Bool)
  | 0 => []
  | j + 1 => mlDisjStep e k j (mlDisjList e k j)

private theorem primrec₂_mlDisjList (e : Code) : Primrec₂ (mlDisjList e) := by
  have hh : Primrec₂ fun (k : ℕ) (jAcc : ℕ × List (List Bool)) =>
      mlDisjStep e k jAcc.1 jAcc.2 := by
    have hcand : Primrec fun arg : ℕ × (ℕ × List (List Bool)) =>
        levelCandWord e (arg.1 + 1) arg.2.1 :=
      (primrec₂_levelCandWord e).comp (Primrec.succ.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd)
    have hsome : Primrec₂ fun (arg : ℕ × (ℕ × List (List Bool))) (w : List Bool) =>
        arg.2.2 ++ carveOutSeen w arg.2.2 :=
      Primrec₂.mk <| Primrec.list_append.comp
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        (primrec₂_carveOutSeen.comp Primrec.snd
          (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
    refine Primrec₂.mk <| (Primrec.option_casesOn hcand
      (Primrec.snd.comp Primrec.snd) hsome).of_eq fun _ => ?_
    simp only [mlDisjStep]
    cases levelCandWord _ _ _ <;> rfl
  refine (Primrec.nat_rec (Primrec.const []) hh).of_eq fun k j => ?_
  induction j with
  | zero => rfl
  | succ j ih =>
    change mlDisjStep e k j (Nat.rec [] (fun j acc => mlDisjStep e k j acc) j) = _
    rw [ih]; rfl

private theorem mlDisjList_mono (e : Code) (k : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    mlDisjList e k m ⊆ mlDisjList e k n := by
  induction hmn with
  | refl => exact fun _ h => h
  | step _ ih =>
    intro v hv
    simp only [mlDisjList, mlDisjStep]
    cases levelCandWord e (k + 1) _ with
    | none => exact ih hv
    | some _ => exact List.mem_append_left _ (ih hv)

private theorem mlDisjList_spec (e : Code) (k j : ℕ) :
    (mlDisjList e k j).Pairwise PrefixDisjoint ∧
      ∀ v ∈ mlDisjList e k j,
        ∃ w : List Bool, (e.eval (encode (k + 1, w))).Dom ∧ w <+: v := by
  induction j with
  | zero => simp [mlDisjList]
  | succ j ih =>
    obtain ⟨hpair, hdom⟩ := ih
    simp only [mlDisjList, mlDisjStep]
    cases hc : levelCandWord e (k + 1) j with
    | none => exact ⟨hpair, hdom⟩
    | some w =>
      obtain ⟨hprop, hnew_pair, _⟩ := carveOutSeen_spec w (mlDisjList e k j)
      refine ⟨List.pairwise_append.mpr ⟨hpair, hnew_pair, fun u hu v hv => (hprop v hv).2 u hu⟩,
        fun v hv => ?_⟩
      rcases List.mem_append.mp hv with h | h
      · exact hdom v h
      · exact ⟨w, dom_of_mlCand_eq_some (ek := (e, k + 1)) hc, (hprop v h).1⟩

private theorem mlDisjList_covers (e : Code) (k : ℕ) {w : List Bool}
    (hw : (e.eval (encode (k + 1, w))).Dom) :
    ∃ j : ℕ, prefixCylinderList w ⊆ ⋃ v ∈ mlDisjList e k j, prefixCylinderList v := by
  obtain ⟨j, hcand⟩ := exists_mlCand_eq_some_of_dom (ek := (e, k + 1)) hw
  change levelCandWord e (k + 1) j = some w at hcand
  refine ⟨j + 1, fun x hx => ?_⟩
  simp only [mlDisjList, mlDisjStep, hcand, Set.mem_iUnion, List.mem_append, exists_prop]
  by_cases hseen : x ∈ ⋃ u ∈ mlDisjList e k j, prefixCylinderList u
  · obtain ⟨u, hu, hxu⟩ := Set.mem_iUnion₂.mp hseen
    exact ⟨u, Or.inl hu, hxu⟩
  · have hdiff : x ∈ ⋃ v ∈ carveOutSeen w (mlDisjList e k j), prefixCylinderList v := by
      rw [(carveOutSeen_spec w (mlDisjList e k j)).2.2]
      exact ⟨hx, hseen⟩
    obtain ⟨v, hv, hxv⟩ := Set.mem_iUnion₂.mp hdiff
    exact ⟨v, Or.inr hv, hxv⟩

private def martinLofToSolovayTest (T : MartinLofTest) (e : Code)
    (he : ∀ p : ℕ × List Bool, p.2 ∈ T.cover p.1 ↔ (e.eval (encode p)).Dom) :
    SolovayTest where
  cover := {v | ∃ kj : ℕ × ℕ, v ∈ mlDisjList e kj.1 kj.2}
  re := by
    have hmem : ComputablePred fun arg : List Bool × (ℕ × ℕ) =>
        arg.1 ∈ mlDisjList e arg.2.1 arg.2.2 := by
      have hlist : Primrec fun arg : List Bool × (ℕ × ℕ) =>
          mlDisjList e arg.2.1 arg.2.2 :=
        (primrec₂_mlDisjList e).comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
      have heq : ComputablePred (Function.uncurry fun (arg : List Bool × (ℕ × ℕ)) (u : List Bool) =>
          u = arg.1) :=
        (Primrec.eq.decide.to_comp.comp Computable.snd
          (Computable.fst.comp Computable.fst)).computablePred
      exact (ComputablePred.exists_mem_list heq hlist.to_comp).of_eq fun arg => by simp
    exact ComputablePred.rePred_exists hmem
  tsum_lt_top := by
    classical
    have hdisj_rel : ∀ {L : List (List Bool)}, L.Pairwise PrefixDisjoint →
        ∀ {a b}, a ∈ L → b ∈ L → a ≠ b → PrefixDisjoint a b := by
      intro L hL a b ha hb hne
      induction L with
      | nil => simp at ha
      | cons x xs ih =>
        rcases List.pairwise_cons.mp hL with ⟨hx, hxs⟩
        rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
        · exact absurd rfl hne
        · exact hx _ hb'
        · exact (hx _ ha').symm
        · exact ih hxs ha' hb'
    let D : ℕ → Set (List Bool) := fun k => {v | ∃ j : ℕ, v ∈ mlDisjList e k j}
    have hD_sum : ∀ k : ℕ, (∑' v : D k, (2 : ℝ≥0∞)⁻¹ ^ (v : List Bool).length) ≤
        (2 : ℝ≥0∞)⁻¹ ^ (k + 1) := by
      intro k
      refine hasSum_le_of_sum_le CompleteLattice.summable.hasSum fun F => ?_
      have hex_j : ∀ v : D k, ∃ j : ℕ, v.val ∈ mlDisjList e k j := fun v => v.property
      choose fj hfj using hex_j
      let J := F.sup fj
      have hF_in : ∀ v ∈ F, (v : List Bool) ∈ mlDisjList e k J := fun v hv =>
        mlDisjList_mono e k (Finset.le_sup hv) (hfj v)
      have hdisj : (F : Set (D k)).PairwiseDisjoint fun v => prefixCylinderList v.val := by
        intro a ha b hb hne
        have hpa := (mlDisjList_spec e k J).1
        have ha' : a.val ∈ mlDisjList e k J := hF_in a ha
        have hb' : b.val ∈ mlDisjList e k J := hF_in b hb
        have hne' : a.val ≠ b.val := fun h => hne (Subtype.ext h)
        exact disjoint_prefixCylinderList_of_prefixDisjoint (hdisj_rel hpa ha' hb' hne')
      have hsub : (⋃ v ∈ F, prefixCylinderList v.val) ⊆
          ⋃ w ∈ T.cover (k + 1), prefixCylinderList w := by
        refine Set.iUnion₂_subset fun v hv => ?_
        obtain ⟨w, hw_dom, hwv⟩ := (mlDisjList_spec e k J).2 v.val (hF_in v hv)
        exact (prefixCylinderList_subset_of_isPrefix hwv).trans fun _ hx =>
          Set.mem_iUnion₂.mpr ⟨w, (he (k + 1, w)).mpr hw_dom, hx⟩
      calc ∑ v ∈ F, (2 : ℝ≥0∞)⁻¹ ^ (v : List Bool).length
        _ = ∑ v ∈ F, Cslib.BitString.coinFlips (prefixCylinderList v.val) := by
            refine Finset.sum_congr rfl fun v _ => ?_
            rw [coinFlips_prefixCylinderList, ENNReal.inv_pow]
        _ = Cslib.BitString.coinFlips (⋃ v ∈ F, prefixCylinderList v.val) :=
            (measure_biUnion_finset hdisj fun v _ => measurableSet_prefixCylinderList v.val).symm
        _ ≤ Cslib.BitString.coinFlips (⋃ w ∈ T.cover (k + 1), prefixCylinderList w) :=
            measure_mono hsub
        _ ≤ (2 : ℝ≥0∞)⁻¹ ^ (k + 1) := T.measure_le (k + 1)
    have hsum_union :
        (∑' v : {v | ∃ kj : ℕ × ℕ, v ∈ mlDisjList e kj.1 kj.2},
          (2 : ℝ≥0∞)⁻¹ ^ (v : List Bool).length) ≤ 1 := by
      have hex_k : ∀ v : {v | ∃ kj : ℕ × ℕ, v ∈ mlDisjList e kj.1 kj.2},
          ∃ k : ℕ, (v : List Bool) ∈ D k := fun v => by
        obtain ⟨⟨k, j⟩, hj⟩ := v.property
        exact ⟨k, j, hj⟩
      choose fk hfk using hex_k
      refine hasSum_le_of_sum_le CompleteLattice.summable.hasSum fun F => ?_
      let K : ℕ := F.sup fk + 1
      have hmap : ∀ v ∈ F, fk v ∈ Finset.range K := fun v hv =>
        Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup hv))
      have hfib : ∀ k ∈ Finset.range K,
          ∑ v ∈ F.filter (fun v => fk v = k), (2 : ℝ≥0∞)⁻¹ ^ (v : List Bool).length ≤
            (2 : ℝ≥0∞)⁻¹ ^ (k + 1) := by
        intro k _
        let Fk := F.filter (fun v => fk v = k)
        let emb : Fk ↪ D k :=
          ⟨fun v => ⟨v.val.val, v.property |> Finset.mem_filter.mp |>.2 ▸ hfk v.val⟩,
            fun a b h => Subtype.ext (Subtype.ext (congrArg (fun z : D k => (z : List Bool)) h))⟩
        calc ∑ v ∈ Fk, (2 : ℝ≥0∞)⁻¹ ^ (v : List Bool).length
          _ = ∑ v ∈ (Finset.univ.map emb : Finset (D k)),
                (2 : ℝ≥0∞)⁻¹ ^ (v : List Bool).length := by
              rw [Finset.sum_map, ← Finset.sum_coe_sort Fk _]
              rfl
          _ ≤ ∑' v : D k, (2 : ℝ≥0∞)⁻¹ ^ (v : List Bool).length := sum_le_tsum _
          _ ≤ (2 : ℝ≥0∞)⁻¹ ^ (k + 1) := hD_sum k
      calc ∑ v ∈ F, (2 : ℝ≥0∞)⁻¹ ^ (v : List Bool).length
        _ = ∑ k ∈ Finset.range K,
              ∑ v ∈ F.filter (fun v => fk v = k), (2 : ℝ≥0∞)⁻¹ ^ (v : List Bool).length :=
            (Finset.sum_fiberwise_of_maps_to hmap _).symm
        _ ≤ ∑ k ∈ Finset.range K, (2 : ℝ≥0∞)⁻¹ ^ (k + 1) := Finset.sum_le_sum hfib
        _ ≤ ∑' k : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (k + 1) := sum_le_tsum (Finset.range K)
        _ = 1 := by simpa using tsum_two_inv_pow_shift 0
    exact lt_of_le_of_lt hsum_union ENNReal.one_lt_top

/-- **Solovay completeness**: any sequence `x : ℕ → Bool` passing every `SolovayTest` is
Martin-Löf random [LiVitanyi2019, ShenUspenskyVereshchagin2017]. -/
theorem isMartinLofRandom_of_forall_passesSolovayTest {x : ℕ → Bool}
    (hx : ∀ S : SolovayTest, PassesSolovayTest S x) : IsMartinLofRandom x := by
  intro T
  obtain ⟨e, he⟩ := rePred_iff_exists_code.mp T.re
  let S := martinLofToSolovayTest T e he
  have hfin := hx S
  by_contra! hfail
  let M : ℕ := hfin.toFinset.sup List.length
  obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp (hfail (M + 1))
  obtain ⟨j, hj⟩ := mlDisjList_covers e M ((he (M + 1, w)).mp hw)
  obtain ⟨v, hv, hxv⟩ := Set.mem_iUnion₂.mp (hj hxw)
  obtain ⟨w', hw'_dom, hw'v⟩ := (mlDisjList_spec e M j).2 v hv
  have hsub : prefixCylinderList v ⊆ ⋃ u ∈ T.cover (M + 1), prefixCylinderList u :=
    (prefixCylinderList_subset_of_isPrefix hw'v).trans fun _ hy =>
      Set.mem_iUnion₂.mpr ⟨w', (he (M + 1, w')).mpr hw'_dom, hy⟩
  have hmeas : ((1 : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ v.length ≤ (2 : ℝ≥0∞)⁻¹ ^ (M + 1) :=
    calc ((1 : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ v.length
      _ = Cslib.BitString.coinFlips (prefixCylinderList v) := by
          rw [Nat.cast_one, one_mul, coinFlips_prefixCylinderList, ENNReal.inv_pow]
      _ ≤ Cslib.BitString.coinFlips (⋃ u ∈ T.cover (M + 1), prefixCylinderList u) :=
          measure_mono hsub
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ (M + 1) := T.measure_le (M + 1)
  have hpow : 2 ^ (M + 1) ≤ 2 ^ v.length := by
    simpa only [one_mul] using (nat_mul_two_pow_le_iff_ennreal 1 (M + 1) v.length).mpr hmeas
  have hvlen : M + 1 ≤ v.length := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hpow
  have hv_le : v.length ≤ M :=
    Finset.le_sup (hfin.mem_toFinset.mpr ⟨⟨(M, j), hv⟩, hxv⟩)
  omega

/-- **Characterization by Solovay tests** [LiVitanyi2019, ShenUspenskyVereshchagin2017]: an
infinite bit sequence `x` is Martin-Löf random if and only if it passes every `SolovayTest`. -/
theorem passesSolovayTest_iff_isMartinLofRandom (x : ℕ → Bool) :
    (∀ S : SolovayTest, PassesSolovayTest S x) ↔ IsMartinLofRandom x :=
  ⟨isMartinLofRandom_of_forall_passesSolovayTest, fun hx S =>
    passesSolovayTest_of_isMartinLofRandom S hx⟩

/-! ### Borel's strong law of large numbers for Martin-Löf random sequences -/

private noncomputable def trueCount {n : ℕ} (y : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun i : Fin n => y i = true).card

private theorem count_ofFn_eq_trueCount {n : ℕ} (y : Fin n → Bool) :
    (List.ofFn y).count true = trueCount y := by
  induction n with
  | zero => simp [trueCount]
  | succ n ih =>
    rw [List.ofFn_succ, List.count_cons, ih (fun i => y i.succ)]
    simp only [trueCount, Finset.card_filter, Fin.sum_univ_succ]
    cases y 0 <;> simp [Nat.add_comm]

private theorem sum_signVal_eq {n : ℕ} (y : Fin n → Bool) :
    (∑ i : Fin n, Cslib.BitString.signVal (y i)) = (n : ℝ) - 2 * (trueCount y : ℝ) := by
  calc ∑ i : Fin n, Cslib.BitString.signVal (y i)
    _ = ∑ i : Fin n, (1 - 2 * Cslib.BitString.bitVal ℝ (y i)) :=
        Finset.sum_congr rfl fun i _ =>
          Cslib.BitString.signVal_eq_one_sub_two_mul_bitVal (y i)
    _ = (∑ _ : Fin n, (1 : ℝ)) - 2 * ∑ i : Fin n, Cslib.BitString.bitVal ℝ (y i) := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    _ = (n : ℝ) - 2 * (trueCount y : ℝ) := by
        simp [trueCount, Cslib.BitString.bitVal, Finset.sum_boole]

private theorem card_filter_sum_signVal_ge (n : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    ((Finset.univ.filter fun y : Fin n → Bool =>
        2 * δ * n ≤ ∑ i : Fin n, Cslib.BitString.signVal (y i)).card : ℝ) ≤
      (2 ^ n : ℝ) * Real.exp (-2 * δ ^ 2 * n) := by
  let s : ℝ := 2 * δ
  let t : ℝ := 2 * δ * n
  let A := Finset.univ.filter fun y : Fin n → Bool =>
    t ≤ ∑ i : Fin n, Cslib.BitString.signVal (y i)
  have hsum_le : (A.card : ℝ) * Real.exp (s * t) ≤
      ∑ y : Fin n → Bool, Real.exp (s * ∑ i : Fin n, (1 : ℝ) * Cslib.BitString.signVal (y i)) :=
    calc (A.card : ℝ) * Real.exp (s * t)
      _ = ∑ _ ∈ A, Real.exp (s * t) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ y ∈ A, Real.exp (s * ∑ i : Fin n, (1 : ℝ) * Cslib.BitString.signVal (y i)) :=
          Finset.sum_le_sum fun y hy => Real.exp_le_exp.mpr <| by
            simpa only [one_mul] using mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hy).2
              (by positivity : 0 ≤ s)
      _ ≤ ∑ y : Fin n → Bool,
            Real.exp (s * ∑ i : Fin n, (1 : ℝ) * Cslib.BitString.signVal (y i)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A) fun _ _ _ =>
            (Real.exp_pos _).le
  have hexp := Cslib.BitString.expect_exp_mul_sum_mul_signVal_le (fun _ : Fin n => (1 : ℝ)) s
  rw [Fintype.expect_eq_sum_div_card, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Nat.cast_pow, Nat.cast_ofNat, div_le_iff₀ (by positivity)] at hexp
  have hmul : (A.card : ℝ) * Real.exp (s * t) ≤ (2 ^ n : ℝ) * Real.exp (s ^ 2 * n / 2) :=
    hsum_le.trans (by simpa [mul_comm (Real.exp _) (2 ^ n : ℝ)] using hexp)
  calc (A.card : ℝ)
    _ ≤ ((2 ^ n : ℝ) * Real.exp (s ^ 2 * n / 2)) / Real.exp (s * t) :=
        (le_div_iff₀ (Real.exp_pos _)).mpr hmul
    _ = (2 ^ n : ℝ) * Real.exp (s ^ 2 * n / 2 - s * t) := by rw [mul_div_assoc, Real.exp_sub]
    _ = (2 ^ n : ℝ) * Real.exp (-2 * δ ^ 2 * n) := by
      congr 2
      dsimp only [s, t]
      ring

private theorem card_filter_trueCount_le (n : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    ((Finset.univ.filter fun y : Fin n → Bool =>
        δ * n ≤ |(trueCount y : ℝ) - (n : ℝ) / 2|).card : ℝ) ≤
      2 * (2 ^ n : ℝ) * Real.exp (-2 * δ ^ 2 * n) := by
  let S : (Fin n → Bool) → ℝ := fun y => ∑ i : Fin n, Cslib.BitString.signVal (y i)
  let A := Finset.univ.filter fun y : Fin n → Bool => 2 * δ * n ≤ S y
  let B := Finset.univ.filter fun y : Fin n → Bool => 2 * δ * n ≤ -S y
  have hS_neg (y : Fin n → Bool) : S (fun i => !y i) = -S y := by
    simp only [S, Cslib.BitString.signVal_not, Finset.sum_neg_distrib]
  have hB_eq : B.card = A.card := Finset.card_bij (fun y _ i => !y i)
    (fun y hy => by
      simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      rwa [hS_neg])
    (fun _ _ _ _ h => funext fun i => by simpa using congrArg (!·) (congrFun h i))
    (fun y hy => ⟨fun i => !y i, by
        simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
        rwa [hS_neg, neg_neg], funext fun i => Bool.not_not _⟩)
  have hsub : (Finset.univ.filter fun y : Fin n → Bool =>
      δ * n ≤ |(trueCount y : ℝ) - (n : ℝ) / 2|) ⊆ A ∪ B := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, A, B] at hy ⊢
    have hSy : |S y| = 2 * |(trueCount y : ℝ) - (n : ℝ) / 2| := by
      have hS_eq : S y = -2 * ((trueCount y : ℝ) - (n : ℝ) / 2) := by
        dsimp only [S]
        rw [sum_signVal_eq]
        ring
      rw [hS_eq, abs_mul, show |(-2 : ℝ)| = 2 by norm_num]
    exact le_abs.mp (by linarith)
  have hcard_union : ((Finset.univ.filter fun y : Fin n → Bool =>
      δ * n ≤ |(trueCount y : ℝ) - (n : ℝ) / 2|).card : ℝ) ≤ (A.card : ℝ) + (B.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le A B)
  rw [hB_eq] at hcard_union
  linarith [card_filter_sum_signVal_ge n hδ]

private def devCount (w : List Bool) : ℕ :=
  w.foldr (fun b c => bif b then c + 1 else c) 0

private theorem devCount_eq_count (w : List Bool) : devCount w = w.count true := by
  induction w with
  | nil => rfl
  | cons b rest ih =>
    simp only [devCount, List.foldr_cons, List.count_cons]
    change (bif b then devCount rest + 1 else devCount rest) = _
    rw [ih]
    cases b <;> simp

private theorem primrec_devCount : Primrec devCount := by
  have hh : Primrec₂ fun (_ : List Bool) (bc : Bool × ℕ) =>
      bif bc.1 then bc.2 + 1 else bc.2 :=
    Primrec₂.mk <| Primrec.cond (Primrec.fst.comp Primrec.snd)
      (Primrec.succ.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  exact (Primrec.list_foldr Primrec.id (Primrec.const 0) hh).of_eq fun _ => rfl

private def devTestMem (k : ℕ) (w : List Bool) : Prop :=
  0 < w.length ∧ (w.length ≤ k * (2 * devCount w - w.length) ∨
    w.length ≤ k * (w.length - 2 * devCount w))

private def devTestBool (k : ℕ) (w : List Bool) : Bool :=
  decide (0 < w.length) &&
    (decide (w.length ≤ k * (2 * devCount w - w.length)) ||
      decide (w.length ≤ k * (w.length - 2 * devCount w)))

private theorem primrec_devTestBool (k : ℕ) : Primrec (devTestBool k) :=
  (Primrec.and.comp
    (Primrec.nat_lt.decide.comp (Primrec.const 0) Primrec.list_length)
    (Primrec.or.comp
      (Primrec.nat_le.decide.comp Primrec.list_length
        (Primrec.nat_mul.comp (Primrec.const k)
          (Primrec.nat_sub.comp (Primrec.nat_double.comp primrec_devCount) Primrec.list_length)))
      (Primrec.nat_le.decide.comp Primrec.list_length
        (Primrec.nat_mul.comp (Primrec.const k)
          (Primrec.nat_sub.comp Primrec.list_length
            (Primrec.nat_double.comp primrec_devCount)))))).of_eq fun _ => rfl

private theorem real_le_mul_sub_of_nat {n k a b : ℕ} (hn : 0 < n) (h : n ≤ k * (a - b)) :
    (n : ℝ) ≤ (k : ℝ) * ((a : ℝ) - b) := by
  have hba : b ≤ a := by
    by_contra! hlt
    rw [Nat.sub_eq_zero_of_le hlt.le, mul_zero] at h; omega
  have h1 : (n : ℝ) ≤ (k : ℝ) * ((a - b : ℕ) : ℝ) := by exact_mod_cast h
  rwa [Nat.cast_sub hba] at h1

private theorem real_sub_mul_lt_of_nat {n k a b : ℕ} (hn : 0 < n) (hk : 0 < k)
    (h : k * (a - b) < n) : ((a : ℝ) - b) * (k : ℝ) < n := by
  by_cases hba : b ≤ a
  · have h1 : (k : ℝ) * ((a - b : ℕ) : ℝ) < n := by exact_mod_cast h
    rw [Nat.cast_sub hba] at h1; linarith
  · have : (a : ℝ) < b := by exact_mod_cast Nat.lt_of_not_ge hba
    have : (0 : ℝ) < k := by exact_mod_cast hk
    have : (0 : ℝ) < n := by exact_mod_cast hn
    nlinarith

private theorem mem_deviation_filter {k n : ℕ} (hk : 0 < k) {w : List Bool}
    (hw : w.length = n) (hmem : devTestMem k w) :
    (1 / (2 * (k : ℝ))) * n ≤
      |(trueCount (fun i : Fin n => w[i.val]'(Nat.lt_of_lt_of_eq i.isLt hw.symm)) : ℝ) -
        (n : ℝ) / 2| := by
  let y : Fin n → Bool := fun i => w[i.val]'(Nat.lt_of_lt_of_eq i.isLt hw.symm)
  have hcnt : trueCount y = devCount w := by
    rw [← count_ofFn_eq_trueCount,
      show List.ofFn y = w from List.ext_getElem (by simp [hw]) fun i _ _ => by simp [y],
      devCount_eq_count]
  rw [hcnt]
  rcases hmem with ⟨hw_pos, hcond⟩
  subst hw
  have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk
  have htwo_abs : (w.length : ℝ) ≤
      (k : ℝ) * (2 * |(devCount w : ℝ) - (w.length : ℝ) / 2|) := by
    have hhalf : |2 * (devCount w : ℝ) - w.length| =
        2 * |(devCount w : ℝ) - (w.length : ℝ) / 2| := by
      rw [show 2 * (devCount w : ℝ) - w.length =
        2 * ((devCount w : ℝ) - (w.length : ℝ) / 2) by ring, abs_mul]
      norm_num
    rw [← hhalf]
    rcases hcond with hge | hle
    · calc (w.length : ℝ)
        _ ≤ (k : ℝ) * (2 * (devCount w : ℝ) - w.length) := by
            simpa using real_le_mul_sub_of_nat hw_pos hge
        _ ≤ (k : ℝ) * |2 * (devCount w : ℝ) - w.length| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) hk_pos.le
    · calc (w.length : ℝ)
        _ ≤ (k : ℝ) * ((w.length : ℝ) - 2 * (devCount w : ℝ)) := by
            simpa using real_le_mul_sub_of_nat hw_pos hle
        _ ≤ (k : ℝ) * |2 * (devCount w : ℝ) - w.length| :=
            mul_le_mul_of_nonneg_left (neg_sub (2 * (devCount w : ℝ)) _ ▸ neg_le_abs _) hk_pos.le
  rw [one_div, mul_comm (2 * (k : ℝ))⁻¹ _, ← div_eq_mul_inv]
  exact (div_le_iff₀ (by positivity)).mpr (by linarith)

private def deviationSolovayTest (k : ℕ) (hk : 0 < k) : SolovayTest where
  cover := {w | devTestMem k w}
  re := by
    have hbool : ComputablePred fun w : List Bool => devTestBool k w = true :=
      (primrec_devTestBool k).to_comp.computablePred
    refine hbool.to_re.of_eq fun w => ?_
    simp [devTestBool, devTestMem]
  tsum_lt_top := by
    classical
    let δ : ℝ := 1 / (2 * (k : ℝ))
    have hδ : 0 < δ := by positivity
    let r : ℝ := Real.exp (-2 * δ ^ 2)
    have hr0 : 0 ≤ r := (Real.exp_pos _).le
    have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
    have hbound_real : ∀ F : Finset {w : List Bool // devTestMem k w},
        ∑ w ∈ F, (2 : ℝ)⁻¹ ^ w.val.length ≤ 2 / (1 - r) := by
      intro F
      let N : ℕ := F.sup (fun w => w.val.length) + 1
      have hmap : ∀ w ∈ F, w.val.length ∈ Finset.range N := fun w hw =>
        Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := fun w : _ => w.val.length) hw))
      have hfib : ∀ n ∈ Finset.range N,
          ∑ w ∈ F.filter (fun w => w.val.length = n), (2 : ℝ)⁻¹ ^ w.val.length ≤
            2 * r ^ n := by
        intro n _
        let Fn := F.filter (fun w => w.val.length = n)
        let Gn := Finset.univ.filter fun y : Fin n → Bool =>
          δ * n ≤ |(trueCount y : ℝ) - (n : ℝ) / 2|
        let f : Fn → Gn := fun w =>
          ⟨fun i =>
            w.val.val[i.val]'(Nat.lt_of_lt_of_eq i.isLt (Finset.mem_filter.mp w.property).2.symm),
            Finset.mem_filter.mpr ⟨Finset.mem_univ _,
              mem_deviation_filter hk (Finset.mem_filter.mp w.property).2 w.val.property⟩⟩
        have hf_inj : Function.Injective f := by
          intro a b hab
          have ha_len : a.val.val.length = n := (Finset.mem_filter.mp a.property).2
          have hb_len : b.val.val.length = n := (Finset.mem_filter.mp b.property).2
          have hsub := congrArg (fun z : Gn => z.val) hab
          refine Subtype.ext (Subtype.ext (List.ext_getElem (ha_len.trans hb_len.symm)
            fun i hi1 _ => congrFun hsub ⟨i, Nat.lt_of_lt_of_eq hi1 ha_len⟩))
        have hcard_le : Fn.card ≤ Gn.card := by
          simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf_inj
        have hsum_fn : ∑ w ∈ Fn, (2 : ℝ)⁻¹ ^ w.val.length = (Fn.card : ℝ) * (2 : ℝ)⁻¹ ^ n := by
          calc ∑ w ∈ Fn, (2 : ℝ)⁻¹ ^ w.val.length
            _ = ∑ _ ∈ Fn, (2 : ℝ)⁻¹ ^ n :=
                Finset.sum_congr rfl fun w hw => by rw [(Finset.mem_filter.mp hw).2]
            _ = (Fn.card : ℝ) * (2 : ℝ)⁻¹ ^ n := by rw [Finset.sum_const, nsmul_eq_mul]
        rw [hsum_fn]
        have hr_pow : r ^ n = Real.exp (-2 * δ ^ 2 * n) := by
          dsimp only [r]
          rw [← Real.exp_natCast_mul]
          congr 1
          ring
        calc (Fn.card : ℝ) * (2 : ℝ)⁻¹ ^ n
          _ ≤ (Gn.card : ℝ) * (2 : ℝ)⁻¹ ^ n := by gcongr
          _ ≤ (2 * (2 ^ n : ℝ) * Real.exp (-2 * δ ^ 2 * n)) * (2 : ℝ)⁻¹ ^ n :=
              mul_le_mul_of_nonneg_right (card_filter_trueCount_le n hδ.le) (by positivity)
          _ = 2 * Real.exp (-2 * δ ^ 2 * n) := by
              rw [inv_pow]
              have hpow : (2 ^ n : ℝ) ≠ 0 := by positivity
              field_simp
          _ = 2 * r ^ n := by rw [hr_pow]
      calc ∑ w ∈ F, (2 : ℝ)⁻¹ ^ w.val.length
        _ = ∑ n ∈ Finset.range N,
              ∑ w ∈ F.filter (fun w => w.val.length = n), (2 : ℝ)⁻¹ ^ w.val.length :=
            (Finset.sum_fiberwise_of_maps_to hmap _).symm
        _ ≤ ∑ n ∈ Finset.range N, 2 * r ^ n := Finset.sum_le_sum hfib
        _ = 2 * ∑ n ∈ Finset.range N, r ^ n := (Finset.mul_sum _ _ _).symm
        _ ≤ 2 * (1 / (1 - r)) := by
            gcongr
            rw [one_div]
            exact sum_le_hasSum (Finset.range N) (fun _ _ => pow_nonneg hr0 _)
              (hasSum_geometric_of_lt_one hr0 hr1)
        _ = 2 / (1 - r) := by ring
    have hsum_enn :
        (∑' w : {w : List Bool // devTestMem k w}, (2 : ℝ≥0∞)⁻¹ ^ (w : List Bool).length) ≤
          ENNReal.ofReal (2 / (1 - r)) := by
      refine hasSum_le_of_sum_le CompleteLattice.summable.hasSum fun F => ?_
      have hF : ∑ w ∈ F, (2 : ℝ≥0∞)⁻¹ ^ (w : List Bool).length =
          ENNReal.ofReal (∑ w ∈ F, (2 : ℝ)⁻¹ ^ (w : List Bool).length) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_inv_of_pos (by positivity)]
        norm_num
      rw [hF]
      exact ENNReal.ofReal_le_ofReal (hbound_real F)
    exact lt_of_le_of_lt hsum_enn ENNReal.ofReal_lt_top

/-- **Borel's strong law of large numbers for Martin-Löf randomness**
[LiVitanyi2019, ShenUspenskyVereshchagin2017]: every Martin-Löf random infinite binary sequence `x`
is simply normal in base `2`, with asymptotic frequency `1 / 2` of `true` bits. -/
theorem tendsto_freq_true_of_isMartinLofRandom {x : ℕ → Bool} (hx : IsMartinLofRandom x) :
    Tendsto (fun n : ℕ => ((List.ofFn fun i : Fin n => x i).count true : ℝ) / (n : ℝ))
      atTop (𝓝 (1 / 2 : ℝ)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (by linarith : (0 : ℝ) < 2 * ε)
  have hfin :=
    passesSolovayTest_of_isMartinLofRandom (deviationSolovayTest (k + 1) (Nat.succ_pos k)) hx
  refine ⟨hfin.toFinset.sup List.length + 1, fun n hn => ?_⟩
  have hn_pos : 0 < n := lt_of_lt_of_le (Nat.succ_pos _) hn
  let w : List Bool := List.ofFn fun i : Fin n => x i
  have hw_len : w.length = n := by simp [w]
  have hnot_dev :
      (k + 1) * (2 * devCount w - n) < n ∧ (k + 1) * (n - 2 * devCount w) < n := by
    rw [← not_le, ← not_le, ← not_or, ← hw_len]
    intro h
    have hwin : w ∈ hfin.toFinset :=
      hfin.mem_toFinset.mpr ⟨⟨by omega, h⟩, mem_prefixCylinderList.mpr fun _ => by simp [w]⟩
    have := Finset.le_sup (f := List.length) hwin
    omega
  have hupper : (2 * (devCount w : ℝ) - n) * ((k : ℝ) + 1) < n := by
    simpa [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
      real_sub_mul_lt_of_nat hn_pos (Nat.succ_pos k) hnot_dev.1
  have hlower : ((n : ℝ) - 2 * devCount w) * ((k : ℝ) + 1) < n := by
    simpa [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
      real_sub_mul_lt_of_nat hn_pos (Nat.succ_pos k) hnot_dev.2
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have habs_num : |2 * (devCount w : ℝ) - n| < n / ((k : ℝ) + 1) :=
    abs_lt.mpr
      ⟨neg_lt.mpr ((lt_div_iff₀ hk1).mpr (by linarith)), (lt_div_iff₀ hk1).mpr (by linarith)⟩
  have hhalf_lt : (1 : ℝ) / (2 * ((k : ℝ) + 1)) < ε :=
    calc (1 : ℝ) / (2 * ((k : ℝ) + 1))
      _ = (1 / ((k : ℝ) + 1)) / 2 := by field_simp
      _ < (2 * ε) / 2 := by gcongr
      _ = ε := by ring
  have hn_real : (0 : ℝ) < n := by exact_mod_cast hn_pos
  rw [Real.dist_eq, ← devCount_eq_count w]
  have hrw : (devCount w : ℝ) / (n : ℝ) - 1 / 2 = (2 * (devCount w : ℝ) - n) / (2 * n) := by
    field_simp
  rw [hrw, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * n)]
  calc |2 * (devCount w : ℝ) - n| / (2 * n)
    _ < (n / ((k : ℝ) + 1)) / (2 * n) := by gcongr
    _ = 1 / (2 * ((k : ℝ) + 1)) := by field_simp
    _ < ε := hhalf_lt

/-- **Borel normality of Chaitin's `Ω`**: the binary expansion of `chaitinOmega universalPrefix`
has limiting bit frequency `1 / 2`. -/
theorem tendsto_freq_true_chaitinOmega :
    Tendsto (fun n : ℕ =>
        ((List.ofFn fun i : Fin n =>
          realBit (DescriptionMethod.chaitinOmega DescriptionMethod.universalPrefix) i).count
          true : ℝ) / (n : ℝ))
      atTop (𝓝 (1 / 2 : ℝ)) :=
  tendsto_freq_true_of_isMartinLofRandom isMartinLofRandom_chaitinOmega

end Cslib.Kolmogorov
