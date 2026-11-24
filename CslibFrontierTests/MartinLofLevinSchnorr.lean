/-
Copyright (c) 2026 Matthew Doty, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty, Samuel Schlesinger
-/

module
-- upstream: local-only (test)

import CslibFrontier.Computability.Kolmogorov.MartinLof
import CslibFrontier.Foundations.Data.List.Primrec
import CslibFrontier.Probability.BitString.CoinFlips
import Mathlib.Computability.Primrec.List

/-!
Regression clients and finite/infinite witnesses for universal Martin-Löf tests, left-c.e.
measures of effectively open cylinder sets, the Levin–Schnorr theorem, Solovay tests, and
Borel's strong law of large numbers.
-/

namespace CslibFrontierTests.MartinLofLevinSchnorr

open scoped BigOperators ENNReal Filter Topology
open Cslib Cslib.Kolmogorov Cslib.Kolmogorov.DescriptionMethod Filter MeasureTheory

/-! ### Left-c.e. measure of effectively open cylinder sets -/

-- Disjoint finite union `[[false], [true, false]]` has exact mass `3 / 4` and approximants
-- converging to `3 / 4`.
example :
    finitePrefixMass [[false], [true, false]] = 3 / 4 ∧
      0 ≤ finitePrefixMass [[false], [true, false]] ∧
      finitePrefixMass [[false], [true, false]] ≤ 1 ∧
      ∃ (num den : ℕ → ℕ), Computable num ∧ Computable den ∧ (∀ t, 0 < den t) ∧
        Monotone (fun t => (num t : ℝ) / (den t : ℝ)) ∧
        Tendsto (fun t => (num t : ℝ) / (den t : ℝ)) atTop (𝓝 (3 / 4 : ℝ)) := by
  let S : Set (List Bool) := {[false], [true, false]}
  have hS : REPred (· ∈ S) :=
    ((Primrec.eq.comp Primrec.id (Primrec.const [false])).or
      (Primrec.eq.comp Primrec.id (Primrec.const [true, false]))).computablePred.to_re.of_eq
      fun w => by simp [S]
  have hdisj : Disjoint (prefixCylinderList [false]) (prefixCylinderList [true, false]) :=
    disjoint_prefixCylinderList_of_prefixDisjoint
      ⟨fun ⟨t, ht⟩ => by simp at ht, fun ⟨t, ht⟩ => by simp at ht⟩
  have hu : (⋃ w ∈ S, prefixCylinderList w) =
      prefixCylinderList [false] ∪ prefixCylinderList [true, false] := by
    ext x
    simp [S]
  have huL : (⋃ w ∈ ([[false], [true, false]] : List (List Bool)), prefixCylinderList w) =
      ⋃ w ∈ S, prefixCylinderList w := by
    ext x
    simp [S]
  have hm : (Cslib.BitString.coinFlips (⋃ w ∈ S, prefixCylinderList w)).toReal = (3 / 4 : ℝ) := by
    rw [hu, measure_union hdisj (measurableSet_prefixCylinderList [true, false]),
      coinFlips_prefixCylinderList, coinFlips_prefixCylinderList, ENNReal.toReal_add
        (by norm_num) (by norm_num)]
    norm_num
  have hmass : finitePrefixMass [[false], [true, false]] = 3 / 4 :=
    (Rat.cast_inj (α := ℝ)).mp
      (((toReal_coinFlips_biUnion_list _).symm.trans (huL ▸ hm)).trans (by norm_num))
  refine ⟨hmass, finitePrefixMass_nonneg _, finitePrefixMass_le_one _, ?_⟩
  simpa [hm] using exists_computable_approx_coinFlips_of_rePred hS

-- Overlapping union `[[false], [false, true]]` has exact mass `1 / 2` and approximants
-- converging to `1 / 2`.
example :
    finitePrefixMass [[false], [false, true]] = 1 / 2 ∧
      ∃ (num den : ℕ → ℕ), Computable num ∧ Computable den ∧ (∀ t, 0 < den t) ∧
        Monotone (fun t => (num t : ℝ) / (den t : ℝ)) ∧
        Tendsto (fun t => (num t : ℝ) / (den t : ℝ)) atTop (𝓝 (1 / 2 : ℝ)) := by
  let S : Set (List Bool) := {[false], [false, true]}
  have hS : REPred (· ∈ S) :=
    ((Primrec.eq.comp Primrec.id (Primrec.const [false])).or
      (Primrec.eq.comp Primrec.id (Primrec.const [false, true]))).computablePred.to_re.of_eq
      fun w => by simp [S]
  have hsub : prefixCylinderList [false, true] ⊆ prefixCylinderList [false] :=
    prefixCylinderList_subset_of_isPrefix ⟨[true], rfl⟩
  have hu : (⋃ w ∈ S, prefixCylinderList w) = prefixCylinderList [false] := by
    ext x
    simp only [S, Set.mem_iUnion, Set.mem_insert_iff, Set.mem_singleton_iff, exists_prop]
    exact ⟨fun ⟨w, hw, hx⟩ => hw.elim (· ▸ hx) (fun h => hsub (h ▸ hx)),
      fun hx => ⟨[false], Or.inl rfl, hx⟩⟩
  have huL : (⋃ w ∈ ([[false], [false, true]] : List (List Bool)), prefixCylinderList w) =
      ⋃ w ∈ S, prefixCylinderList w := by
    ext x
    simp [S]
  have hm : (Cslib.BitString.coinFlips (⋃ w ∈ S, prefixCylinderList w)).toReal = (1 / 2 : ℝ) := by
    rw [hu, coinFlips_prefixCylinderList]
    norm_num
  refine ⟨(Rat.cast_inj (α := ℝ)).mp
      (((toReal_coinFlips_biUnion_list _).symm.trans (huL ▸ hm)).trans (by norm_num)), ?_⟩
  simpa [hm] using exists_computable_approx_coinFlips_of_rePred hS

-- Total code `Code.zero` covers `[]`, so `reCoverMass Code.zero` bounds the union from below and
-- converges to `1`.
example :
    Monotone (reCoverMass Nat.Partrec.Code.zero) ∧
      (∀ t, 0 ≤ reCoverMass Nat.Partrec.Code.zero t) ∧
      (∀ t, reCoverMass Nat.Partrec.Code.zero t ≤ 1) ∧
      (∀ t, (reCoverMass Nat.Partrec.Code.zero t : ℝ) ≤
        (Cslib.BitString.coinFlips
          (⋃ w ∈ {w : List Bool | (Nat.Partrec.Code.zero.eval (Encodable.encode w)).Dom},
            prefixCylinderList w)).toReal) ∧
      Tendsto (fun t => (reCoverMass Nat.Partrec.Code.zero t : ℝ)) atTop (𝓝 (1 : ℝ)) := by
  have huniv :
      (⋃ w ∈ {w : List Bool | (Nat.Partrec.Code.zero.eval (Encodable.encode w)).Dom},
        prefixCylinderList w) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    refine ⟨[], Part.dom_iff_mem.mpr ⟨0, by simp [Nat.Partrec.Code.eval, Pure.pure, PFun.pure]⟩,
      mem_prefixCylinderList.mpr fun i => Fin.elim0 i⟩
  have hten := tendsto_reCoverMass Nat.Partrec.Code.zero
  rw [huniv, measure_univ, ENNReal.toReal_one] at hten
  exact ⟨monotone_reCoverMass _, reCoverMass_nonneg _, reCoverMass_le_one _,
    reCoverMass_le_coinFlips _, hten⟩

/-! ### Universal Martin-Löf test and full `coinFlips` measure -/

example :
    let emptyMLTest : MartinLofTest :=
      { cover := fun _ => ∅
        re := by
          have h : ComputablePred fun (_ : ℕ × List Bool) => (false : Bool) = true :=
            (Primrec.const false).to_comp.computablePred
          exact h.to_re.of_eq fun _ => by simp
        measure_le := fun _ => by simp }
    ∃ d : ℕ, ∀ m : ℕ, emptyMLTest.cover (m + d) ⊆ universalMartinLofTest.cover m :=
  exists_subset_universalMartinLofTest _

example :
    (∃ m : ℕ, realBit (chaitinOmega universalPrefix) ∉
      ⋃ w ∈ universalMartinLofTest.cover m, prefixCylinderList w) ∧
    (¬ ∃ m : ℕ, (fun _ : ℕ => false) ∉
      ⋃ w ∈ universalMartinLofTest.cover m, prefixCylinderList w) :=
  ⟨(isMartinLofRandom_iff_passes_universalMartinLofTest _).mp isMartinLofRandom_chaitinOmega,
    fun h => not_isMartinLofRandom_of_computable (Computable.const false)
      ((isMartinLofRandom_iff_passes_universalMartinLofTest _).mpr h)⟩

example : Cslib.BitString.coinFlips {x : ℕ → Bool | IsMartinLofRandom x} = 1 := by
  have hcomp : Cslib.BitString.coinFlips {x : ℕ → Bool | ¬ IsMartinLofRandom x} = 0 :=
    ae_iff.mp ae_isMartinLofRandom
  have hunion : {x : ℕ → Bool | IsMartinLofRandom x} =
      ({x : ℕ → Bool | ¬ IsMartinLofRandom x})ᶜ := by
    ext x
    simp
  rw [hunion, measure_compl (by
      have hm : MeasurableSet (⋂ m : ℕ,
          ⋃ w ∈ universalMartinLofTest.cover m, prefixCylinderList w) :=
        MeasurableSet.iInter fun m => MeasurableSet.biUnion (Set.to_countable _)
          fun w _ => measurableSet_prefixCylinderList w
      convert hm using 1
      ext x
      simp [isMartinLofRandom_iff_passes_universalMartinLofTest]) (by simp), hcomp, tsub_zero]
  exact measure_univ

/-! ### Levin–Schnorr clients and machine invariance -/

example :
    ∃ c : ℕ, ∀ n : ℕ,
      (n : ℕ∞) ≤ universalPrefixBits.ecomplexity
        (List.ofFn fun i : Fin n => realBit (chaitinOmega universalPrefix) i) + c :=
  (isMartinLofRandom_iff_exists_le_ecomplexity _).mp isMartinLofRandom_chaitinOmega

-- Constant-false prefixes are arbitrarily compressible (`n - K(0^n)` is unbounded).
example :
    ¬ ∃ c : ℕ, ∀ n : ℕ,
      n ≤ universalPrefixBits.complexity (List.replicate n false) + c := by
  rintro ⟨c, hc⟩
  apply not_isMartinLofRandom_of_computable (Computable.const false)
  rw [isMartinLofRandom_iff_exists_le_complexity]
  refine ⟨c, fun n => ?_⟩
  simpa [List.ofFn_const] using hc n

-- Machine-invariant Levin–Schnorr client instantiated on `universalPrefixBits`.
example (x : ℕ → Bool) :
    IsMartinLofRandom x ↔
      ∃ c : ℕ, ∀ n : ℕ,
        n ≤ universalPrefixBits.complexity (List.ofFn fun i : Fin n => x i) + c := by
  obtain ⟨evalBits, hevalBits, hprodBits⟩ := isPartrec_universalPrefixBits
  exact isMartinLofRandom_iff_exists_le_complexity_of_optimal
    minorizesPrefixPartrec_universalPrefixBits isPrefixFree_universalPrefixBits hevalBits
    hprodBits x

/-! ### Solovay test witnesses and Borel strong law of large numbers -/

example (x : ℕ → Bool) :
    let singletonSolovayTest : SolovayTest :=
      { cover := {[false]}
        re := by
          have hbool : ComputablePred fun w : List Bool => id w = [false] :=
            (Primrec.eq.decide.comp Primrec.id (Primrec.const [false])).to_comp.computablePred
          exact hbool.to_re.of_eq fun _ => by simp
        tsum_lt_top := by
          let u : ({[false]} : Set (List Bool)) := ⟨[false], rfl⟩
          have hu : ∀ w : ({[false]} : Set (List Bool)), w = u := fun w => Subtype.ext w.2
          rw [(hasSum_fintype _).tsum_eq,
            Finset.sum_eq_single u (fun b _ h => absurd (hu b) h)
              (fun h => absurd (Finset.mem_univ u) h)]
          norm_num }
    PassesSolovayTest singletonSolovayTest x :=
  (Set.finite_singleton [false]).subset fun _ hw => hw.1

-- Infinite Solovay test detecting runs of `false`, passed by `Ω` and failed by `0^∞`.
example :
    ∃ S : SolovayTest,
      ¬ PassesSolovayTest S (fun _ => false) ∧
      PassesSolovayTest S (realBit (chaitinOmega universalPrefix)) := by
  let S : SolovayTest :=
    { cover := {w | ∃ n : ℕ, 1 ≤ n ∧ w = List.replicate n false}
      re := by
        have hpred : ComputablePred
            (Function.uncurry fun (w : List Bool) (n : ℕ) =>
              (decide (1 ≤ n) && decide (w = List.replicate n false)) = true) := by
          have hrep : Primrec fun n : ℕ => List.replicate n false := by
            have hstep : Primrec₂ fun (_ : ℕ) (nl : ℕ × List Bool) => false :: nl.2 :=
              Primrec₂.mk <| Primrec.list_cons.comp (Primrec.const false)
                (Primrec.snd.comp Primrec.snd)
            refine (Primrec.nat_rec' Primrec.id (Primrec.const []) hstep).of_eq fun n => ?_
            induction n with
            | zero => rfl
            | succ n ih =>
              dsimp only [id_eq] at ih
              change false :: _ = List.replicate (n + 1) false
              rw [ih, List.replicate_succ]
          have h1 : Primrec fun wn : List Bool × ℕ => decide (1 ≤ wn.2) :=
            Primrec.nat_le.decide.comp (Primrec.const 1) Primrec.snd
          have h2 : Primrec fun wn : List Bool × ℕ =>
              decide (wn.1 = List.replicate wn.2 false) :=
            Primrec.eq.decide.comp Primrec.fst (hrep.comp Primrec.snd)
          exact ((Primrec.and.comp h1 h2).of_eq fun _ => rfl).to_comp.computablePred
        refine (ComputablePred.rePred_exists hpred).of_eq fun w => ?_
        simp
      tsum_lt_top := by
        let emb : {w : List Bool // ∃ n : ℕ, 1 ≤ n ∧ w = List.replicate n false} ↪ ℕ :=
          ⟨fun w => w.1.length, fun a b h => by
            obtain ⟨na, _, ha⟩ := a.2
            obtain ⟨nb, _, hb⟩ := b.2
            have hlen : na = nb := by simpa [ha, hb] using h
            exact Subtype.ext (by simp [ha, hb, hlen])⟩
        have hcomp :
            (∑' w : {w : List Bool // ∃ n : ℕ, 1 ≤ n ∧ w = List.replicate n false},
              (2 : ℝ≥0∞)⁻¹ ^ (w : List Bool).length) ≤
              ∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ n :=
          CompleteLattice.summable.tsum_le_tsum_of_inj emb emb.injective
            (fun _ _ => bot_le) (fun _ => le_rfl) CompleteLattice.summable
        have hgeom : (∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ n) = 2 := by
          rw [ENNReal.tsum_geometric]
          have hsub : (1 : ℝ≥0∞) - (2 : ℝ≥0∞)⁻¹ = (2 : ℝ≥0∞)⁻¹ := by
            conv_lhs => rw [← ENNReal.inv_two_add_inv_two]
            exact ENNReal.add_sub_cancel_right (by norm_num)
          rw [hsub]
          norm_num
        exact hcomp.trans_lt (hgeom ▸ by norm_num) }
  refine ⟨S, fun hfin => ?_, ?_⟩
  · have hsub : Set.range (fun n : ℕ => List.replicate (n + 1) false) ⊆
        {w ∈ S.cover | (fun _ : ℕ => false) ∈ prefixCylinderList w} := by
      rintro w ⟨n, rfl⟩
      exact ⟨⟨n + 1, by omega, rfl⟩, mem_prefixCylinderList.mpr fun i => by simp⟩
    have hinf : (Set.range fun n : ℕ => List.replicate (n + 1) false).Infinite :=
      Set.infinite_range_of_injective fun a b h => by
        have := congrArg List.length h
        simpa using this
    exact hinf (hfin.subset hsub)
  · exact (passesSolovayTest_iff_isMartinLofRandom _).mpr isMartinLofRandom_chaitinOmega S

-- Borel normality client: `true` occurs infinitely often in Chaitin's `Ω`.
example :
    Tendsto (fun n : ℕ =>
        ((List.ofFn fun i : Fin n =>
          realBit (chaitinOmega universalPrefix) i).count true : ℝ) / (n : ℝ))
      atTop (𝓝 (1 / 2 : ℝ)) ∧
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      realBit (chaitinOmega universalPrefix) n = true := by
  have hten := tendsto_freq_true_chaitinOmega
  refine ⟨hten, fun N => ?_⟩
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hten (1 / 4 : ℝ) (by norm_num)
  let b := realBit (chaitinOmega universalPrefix)
  by_contra! hall
  let K : ℕ := max M (4 * N + 1)
  have hc_K := (abs_lt.mp (Real.dist_eq _ _ ▸ hM K (le_max_left M _))).1
  have hcnt : ∀ n : ℕ, (List.ofFn fun i : Fin n => b i).count true ≤ N := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
      by_cases hm : N ≤ m
      · have hbf : b m = false := by
          cases hbm : b m
          · rfl
          · exact absurd hbm (hall m hm)
        rw [List.ofFn_succ', List.concat_eq_append, List.count_append, List.count_singleton]
        simpa [hbf] using ih
      · exact (List.count_le_length).trans_eq (List.length_ofFn) |>.trans (by omega)
  have hleK : ((List.ofFn fun i : Fin K => b i).count true : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hcnt K
  have hKpos : (0 : ℝ) < (K : ℝ) := by positivity
  have hlt_quarter : ((List.ofFn fun i : Fin K => b i).count true : ℝ) / (K : ℝ) < 1 / 4 := by
    rw [div_lt_iff₀ hKpos]
    have h4N : (4 * N + 1 : ℝ) ≤ K := by exact_mod_cast le_max_right M (4 * N + 1)
    nlinarith
  linarith

end CslibFrontierTests.MartinLofLevinSchnorr
