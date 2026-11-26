/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Probability.MarkovChain.RandomWalk
import CslibFrontier.Probability.MarkovChain.RotationMap
import CslibFrontier.Probability.MarkovChain.Spectral
import CslibFrontier.Probability.StatisticalDistance.ClosedForm

/-!
# Reversible spectral gap and lazy mixing: checked witnesses and boundary tests

* **Source-form client checks** for [LevinPeres2017] Theorem 12.4 (`(12.10)` and `(12.13)`),
  Theorem 12.5 (`(12.14)`–`(12.15)`), Lemma 12.2, and Lemma 13.6.
* **Periodic two-state swap chain on `Bool` vs its lazy version**: `swapChain` has maximal
  spectral gap `γ = 2` (`spectralGap_le_two` is tight) yet `γ_* = 0` (`λ_* = 1`) and
  `mixingTime (1 / 4) = ⊤`, whereas `swapChain.lazy` has `γ_* = 1`, `λ_* = 0`,
  `distToStationary 1 = 0`, and `mixingTime (1 / 4) = 1`.
* **Irregular bipartite star graph `K_{1, 3}` on `Fin 4`**: non-uniform `degreeStationary`
  (`π(0) = 1 / 2`, `π(1) = π(2) = π(3) = 1 / 6`), `1 ≤ spectralGap`, and concrete lazy mixing
  bound via `mixingTime_lazy_randomWalk_le`.
* **Regular multigraph (`RotationMap`) and `Subsingleton` boundary**: `flipRot` on `Bool`
  (`1 ≤ edgeExpansion`) mixes via `mixingTime_lazy_randomWalk_le_of_edgeExpansion`, and on `Unit`
  both `spectralContraction` and `spectralGap` vanish.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.MarkovChainSpectral

open Cslib Cslib.RotationMap Cslib.Probability Cslib.Probability.PMF
open Cslib.Probability.MarkovChain Finset
open scoped BigOperators ENNReal Cslib.Probability.PMF

/-! ### 1. Source-form client checks (LPW Theorems 12.4 & 12.5, `(12.13)`) -/

example {S : Type*} [Fintype S] {P : MarkovChain S} {π : PMF S}
    (hrev : P.IsReversible π) {π_min : ℝ} (hpos : 0 < π_min)
    (hmin : ∀ x, π_min ≤ (π x).toReal) (hgap : 0 < P.absSpectralGap π)
    {ε : ℝ} (hε : 0 < ε) :
    P.mixingTime π ε ≤
      (⌈(P.absSpectralGap π)⁻¹ *
        ((1 / 2) * Real.log (1 / π_min) + Real.log (1 / (2 * ε)))⌉₊ : ℕ) ∧
    P.mixingTime π ε ≤ (⌈(P.absSpectralGap π)⁻¹ * Real.log (1 / (ε * π_min))⌉₊ : ℕ) :=
  ⟨hrev.mixingTime_le_of_absSpectralGap_pos hpos hmin hgap hε,
    hrev.mixingTime_le_ceil_mul_log hpos hmin hgap hε⟩

example {S : Type*} [Fintype S] [Nontrivial S] {P : MarkovChain S} {π : PMF S}
    (hrev : P.IsReversible π) (hπ : ∀ x, π x ≠ 0) (hgap : 0 < P.absSpectralGap π)
    {ε : ℝ} (hε : 0 < ε) {t : ℕ} (ht : P.mixingTime π ε ≤ t) :
    ((P.absSpectralGap π)⁻¹ - 1) * Real.log (1 / (2 * ε)) ≤ t :=
  hrev.inv_absSpectralGap_sub_one_mul_log_le_mixingTime hπ hgap hε ht

example {S : Type*} [Fintype S] {P : MarkovChain S} {π : PMF S}
    (hrev : P.IsReversible π) (hπ : ∀ z, π z ≠ 0) (x y : S) (t : ℕ) :
    |((P ^ t) x y).toReal / (π y).toReal - 1| ≤
      P.spectralContraction π ^ t / Real.sqrt ((π x).toReal * (π y).toReal) :=
  hrev.abs_toReal_div_sub_one_le hπ x y t

/-! ### 2. `Subsingleton` boundary -/

example (P : MarkovChain Unit) (π : PMF Unit) :
    P.spectralContraction π = 0 ∧ P.spectralGap π = 0 := by
  simp

/-! ### 3. Periodic two-state swap chain vs lazy swap chain on `Bool` -/

private noncomputable def swapChain : MarkovChain Bool where
  step x := _root_.PMF.pure (!x)

private theorem isReversible_swapChain :
    swapChain.IsReversible (uniformOfFintype Bool) := by
  intro x y
  simp only [uniformOfFintype_apply, Fintype.card_bool, Nat.cast_ofNat]
  congr 1
  change _root_.PMF.pure (!x) y = _root_.PMF.pure (!y) x
  cases x <;> cases y <;> simp

private theorem uniform_bool_ne_zero (x : Bool) :
    (uniformOfFintype Bool) x ≠ 0 := by
  simp [uniformOfFintype_apply]

private theorem uniform_bool_toReal (x : Bool) :
    ((uniformOfFintype Bool) x).toReal = 1 / 2 := by
  rw [uniformOfFintype_apply, Fintype.card_bool]
  norm_num

/-- `swapChain` achieves the upper bound `spectralGap = 2` (`spectralGap_le_two`). -/
private theorem spectralGap_swapChain :
    swapChain.spectralGap (uniformOfFintype Bool) = 2 := by
  refine le_antisymm isReversible_swapChain.spectralGap_le_two ?_
  refine (le_spectralGap_iff uniform_bool_ne_zero).mpr fun f hf => ?_
  rw [Fintype.sum_bool, uniform_bool_toReal, uniform_bool_toReal] at hf
  have hfalse : f false = -f true := by linarith
  have hstep_t : swapChain.stepOp f true = f false := by
    rw [stepOp_apply, Fintype.sum_bool]
    change ((_root_.PMF.pure false) true).toReal * f true +
      ((_root_.PMF.pure false) false).toReal * f false = f false
    simp
  have hstep_f : swapChain.stepOp f false = f true := by
    rw [stepOp_apply, Fintype.sum_bool]
    change ((_root_.PMF.pure true) true).toReal * f true +
      ((_root_.PMF.pure true) false).toReal * f false = f true
    simp
  rw [isReversible_swapChain.dirichletForm_eq_sub, Fintype.sum_bool, Fintype.sum_bool,
    uniform_bool_toReal, uniform_bool_toReal, hstep_t, hstep_f, hfalse]
  ring_nf
  exact le_rfl

example : swapChain.spectralGap (uniformOfFintype Bool) = 2 :=
  spectralGap_swapChain

/-- Despite `spectralGap = 2`, `swapChain` has `absSpectralGap = 0` and never mixes (`⊤`). -/
example :
    swapChain.absSpectralGap (uniformOfFintype Bool) = 0 ∧
      swapChain.mixingTime (uniformOfFintype Bool) (1 / 4) = ⊤ := by
  have heig : swapChain.stepOp (fun b : Bool => if b then 1 else -1) =
      (-1 : ℝ) • fun b : Bool => if b then 1 else -1 := by
    ext b
    rw [stepOp_apply, Fintype.sum_bool]
    cases b
    · change ((_root_.PMF.pure true) true).toReal * 1 +
        ((_root_.PMF.pure true) false).toReal * (-1) = (-1) * (-1)
      norm_num
    · change ((_root_.PMF.pure false) true).toReal * 1 +
        ((_root_.PMF.pure false) false).toReal * (-1) = (-1) * 1
      norm_num
  have hmean := isReversible_swapChain.isStationary.sum_mul_eq_zero_of_stepOp_eq_smul
    (by norm_num : (-1 : ℝ) ≠ 1) heig
  have hsq : ∑ x : Bool, ((uniformOfFintype Bool) x).toReal *
      (if x then (1 : ℝ) else -1) ^ 2 = 1 := by
    rw [Fintype.sum_bool, uniform_bool_toReal, uniform_bool_toReal]
    norm_num
  have hstep_sq : ∑ x : Bool, ((uniformOfFintype Bool) x).toReal *
      swapChain.stepOp (fun b => if b then 1 else -1) x ^ 2 = 1 := by
    rw [heig, Fintype.sum_bool, uniform_bool_toReal, uniform_bool_toReal]
    norm_num
  have hge1 : 1 ≤ swapChain.spectralContraction (uniformOfFintype Bool) := by
    have hle := isReversible_swapChain.isStationary.sum_mul_stepOp_sq_le_spectralContraction hmean
    rw [hstep_sq, hsq, mul_one] at hle
    nlinarith [swapChain.spectralContraction_nonneg (uniformOfFintype Bool)]
  have hlam : swapChain.spectralContraction (uniformOfFintype Bool) = 1 :=
    le_antisymm isReversible_swapChain.isStationary.spectralContraction_le_one hge1
  have hgap0 : swapChain.absSpectralGap (uniformOfFintype Bool) = 0 := by
    linarith [swapChain.one_sub_absSpectralGap (uniformOfFintype Bool), hlam]
  exact ⟨hgap0, isReversible_swapChain.mixingTime_eq_top_of_absSpectralGap_eq_zero
    uniform_bool_ne_zero hgap0 (by norm_num)⟩

/-- Passing to `swapChain.lazy` yields `λ_* = 0`, `d(1) = 0`, and `t_mix(1 / 4) = 1`. -/
example :
    swapChain.lazy.spectralContraction (uniformOfFintype Bool) = 0 ∧
      swapChain.lazy.distToStationary (uniformOfFintype Bool) 1 = 0 ∧
      swapChain.lazy.mixingTime (uniformOfFintype Bool) (1 / 4) = 1 := by
  have hlam0 : swapChain.lazy.spectralContraction (uniformOfFintype Bool) = 0 := by
    rw [isReversible_swapChain.spectralContraction_lazy uniform_bool_ne_zero,
      spectralGap_swapChain]
    norm_num
  have hd1 : swapChain.lazy.distToStationary (uniformOfFintype Bool) 1 = 0 := by
    refine le_antisymm ?_ (swapChain.lazy.distToStationary_nonneg _ 1)
    have h := isReversible_swapChain.lazy.distToStationary_le_of_le_toReal
      (by norm_num : (0 : ℝ) < 1 / 2) (fun x => by rw [uniform_bool_toReal]) 1
    rw [hlam0, zero_pow one_ne_zero, mul_zero] at h
    exact h
  have htmix_le : swapChain.lazy.mixingTime (uniformOfFintype Bool) (1 / 4) ≤ (1 : ℕ) :=
    swapChain.lazy.mixingTime_le_of_distToStationary_le (by linarith)
  have hd0_gt : (1 / 4 : ℝ) <
      swapChain.lazy.distToStationary (uniformOfFintype Bool) 0 := by
    have hd_pure : dist ((swapChain.lazy ^ 0) true) (uniformOfFintype Bool) = 1 / 2 := by
      rw [pow_zero, one_apply, dist_pure_left, uniform_bool_toReal]
      norm_num
    linarith [swapChain.lazy.dist_le_distToStationary (uniformOfFintype Bool) 0 true]
  have htmix_not0 : ¬ swapChain.lazy.mixingTime
      (uniformOfFintype Bool) (1 / 4) ≤ (0 : ℕ) := by
    rw [isReversible_swapChain.lazy.isStationary.mixingTime_le_iff]
    linarith
  have htmix_eq1 : swapChain.lazy.mixingTime (uniformOfFintype Bool) (1 / 4) = 1 := by
    cases hm : swapChain.lazy.mixingTime (uniformOfFintype Bool) (1 / 4) with
    | top =>
      rw [hm] at htmix_le
      exact absurd htmix_le (by simp)
    | coe n =>
      rw [hm] at htmix_le htmix_not0
      have hn1 : n ≤ 1 := ENat.natCast_le_natCast.mp htmix_le
      have hn0 : ¬ n ≤ 0 := fun h => htmix_not0 (ENat.natCast_le_natCast.mpr h)
      congr 1
      omega
  exact ⟨hlam0, hd1, htmix_eq1⟩

/-! ### 4. Irregular bipartite star graph `K_{1, 3}` on `Fin 4` -/

private def starK13 : SimpleGraph (Fin 4) where
  Adj u v := (u = 0 ∧ v ≠ 0) ∨ (v = 0 ∧ u ≠ 0)
  symm := ⟨fun _ _ h => h.elim (fun h1 => Or.inr h1) (fun h2 => Or.inl h2)⟩
  loopless := ⟨fun _ h => h.elim (fun h1 => h1.2 h1.1) (fun h2 => h2.2 h2.1)⟩

private instance : DecidableRel starK13.Adj := fun u v => by
  unfold starK13
  infer_instance

private theorem starK13_ne_bot : starK13 ≠ ⊥ := by
  intro hbot
  have hadj : starK13.Adj 0 1 := Or.inl ⟨rfl, by decide⟩
  rw [hbot] at hadj
  exact hadj

private theorem starK13_connected : starK13.Connected := by
  refine SimpleGraph.connected_iff_exists_forall_reachable starK13 |>.mpr ⟨0, fun v => ?_⟩
  fin_cases v
  · exact SimpleGraph.Reachable.refl 0
  · exact SimpleGraph.Adj.reachable (Or.inl ⟨rfl, by decide⟩)
  · exact SimpleGraph.Adj.reachable (Or.inl ⟨rfl, by decide⟩)
  · exact SimpleGraph.Adj.reachable (Or.inl ⟨rfl, by decide⟩)

private theorem starK13_degree :
    starK13.degree 0 = 3 ∧ starK13.degree 1 = 1 ∧
      starK13.degree 2 = 1 ∧ starK13.degree 3 = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · rw [← starK13.card_neighborFinset_eq_degree]
      decide

private theorem starK13_card_edges : #starK13.edgeFinset = 3 := by
  have hsum := starK13.sum_degrees_eq_twice_card_edges
  rw [Fin.sum_univ_four, starK13_degree.1, starK13_degree.2.1,
    starK13_degree.2.2.1, starK13_degree.2.2.2] at hsum
  omega

/-- Non-uniform `degreeStationary` masses on `K_{1, 3}`: `π(0) = 1 / 2` and `π(1) = 1 / 6`. -/
example :
    (degreeStationary starK13 starK13_ne_bot 0).toReal = 1 / 2 ∧
      (degreeStationary starK13 starK13_ne_bot 1).toReal = 1 / 6 := by
  rw [degreeStationary_apply, degreeStationary_apply, starK13_degree.1, starK13_degree.2.1,
    starK13_card_edges]
  norm_num

/-- On `K_{1, 3}`, `1 ≤ spectralGap`, giving a finite mixing bound for `(randomWalk starK13).lazy`
via `mixingTime_lazy_randomWalk_le`. -/
example :
    1 ≤ (MarkovChain.randomWalk starK13).spectralGap (degreeStationary starK13 starK13_ne_bot) ∧
      ((MarkovChain.randomWalk starK13).lazy).mixingTime
        (degreeStationary starK13 starK13_ne_bot) (1 / 4) ≤
        (⌈2 * ((MarkovChain.randomWalk starK13).spectralGap
            (degreeStationary starK13 starK13_ne_bot))⁻¹ *
          ((1 / 2) * Real.log 6 + Real.log 2)⌉₊ : ℕ) := by
  set π := degreeStationary starK13 starK13_ne_bot
  have hπ0 : (π 0).toReal = 1 / 2 := by
    rw [degreeStationary_apply, starK13_degree.1, starK13_card_edges]
    norm_num
  have hπ1 : (π 1).toReal = 1 / 6 := by
    rw [degreeStationary_apply, starK13_degree.2.1, starK13_card_edges]
    norm_num
  have hπ2 : (π 2).toReal = 1 / 6 := by
    rw [degreeStationary_apply, starK13_degree.2.2.1, starK13_card_edges]
    norm_num
  have hπ3 : (π 3).toReal = 1 / 6 := by
    rw [degreeStationary_apply, starK13_degree.2.2.2, starK13_card_edges]
    norm_num
  have hπ_nz : ∀ v : Fin 4, π v ≠ 0 := by
    intro v
    match v with
    | 0 => intro h; rw [h] at hπ0; norm_num at hπ0
    | 1 => intro h; rw [h] at hπ1; norm_num at hπ1
    | 2 => intro h; rw [h] at hπ2; norm_num at hπ2
    | 3 => intro h; rw [h] at hπ3; norm_num at hπ3
  have hgap1 : 1 ≤ (MarkovChain.randomWalk starK13).spectralGap π := by
    refine (le_spectralGap_iff hπ_nz).mpr fun f hmean => ?_
    rw [Fin.sum_univ_four, hπ0, hπ1, hπ2, hπ3] at hmean
    have hsum_leaves : f 1 + f 2 + f 3 = -3 * f 0 := by linarith
    have hp01 : (MarkovChain.randomWalk starK13 0 1).toReal = 1 / 3 := by
      rw [randomWalk_apply_of_adj (Or.inl ⟨rfl, by decide⟩), starK13_degree.1]
      norm_num
    have hp02 : (MarkovChain.randomWalk starK13 0 2).toReal = 1 / 3 := by
      rw [randomWalk_apply_of_adj (Or.inl ⟨rfl, by decide⟩), starK13_degree.1]
      norm_num
    have hp03 : (MarkovChain.randomWalk starK13 0 3).toReal = 1 / 3 := by
      rw [randomWalk_apply_of_adj (Or.inl ⟨rfl, by decide⟩), starK13_degree.1]
      norm_num
    have hp00 : (MarkovChain.randomWalk starK13 0 0).toReal = 0 := by
      rw [randomWalk_apply_of_not_adj (by rw [starK13_degree.1]; norm_num)
        (starK13.loopless.irrefl 0), ENNReal.toReal_zero]
    have hp_leaf (i : Fin 4) (hi : i ≠ 0) :
        (MarkovChain.randomWalk starK13 i 0).toReal = 1 ∧
          ∀ j : Fin 4, j ≠ 0 → (MarkovChain.randomWalk starK13 i j).toReal = 0 := by
      have hdeg1 : starK13.degree i = 1 := by
        fin_cases i <;> dsimp only at hi ⊢
        · exact absurd rfl hi
        · exact starK13_degree.2.1
        · exact starK13_degree.2.2.1
        · exact starK13_degree.2.2.2
      refine ⟨?_, fun j hj => ?_⟩
      · rw [randomWalk_apply_of_adj (Or.inr ⟨rfl, hi⟩), hdeg1]
        norm_num
      · have hnadj : ¬ starK13.Adj i j := by
          intro hadj
          rcases hadj with ⟨h1, _⟩ | ⟨h2, _⟩
          · exact hi h1
          · exact hj h2
        rw [randomWalk_apply_of_not_adj (by omega) hnadj, ENNReal.toReal_zero]
    have hstep0 : (MarkovChain.randomWalk starK13).stepOp f 0 = (f 1 + f 2 + f 3) / 3 := by
      rw [stepOp_apply, Fin.sum_univ_four, hp00, hp01, hp02, hp03]
      ring
    have hstep1 : (MarkovChain.randomWalk starK13).stepOp f 1 = f 0 := by
      obtain ⟨h10, hrest⟩ := hp_leaf 1 (by decide)
      rw [stepOp_apply, Fin.sum_univ_four, h10, hrest 1 (by decide),
        hrest 2 (by decide), hrest 3 (by decide)]
      ring
    have hstep2 : (MarkovChain.randomWalk starK13).stepOp f 2 = f 0 := by
      obtain ⟨h20, hrest⟩ := hp_leaf 2 (by decide)
      rw [stepOp_apply, Fin.sum_univ_four, h20, hrest 1 (by decide),
        hrest 2 (by decide), hrest 3 (by decide)]
      ring
    have hstep3 : (MarkovChain.randomWalk starK13).stepOp f 3 = f 0 := by
      obtain ⟨h30, hrest⟩ := hp_leaf 3 (by decide)
      rw [stepOp_apply, Fin.sum_univ_four, h30, hrest 1 (by decide),
        hrest 2 (by decide), hrest 3 (by decide)]
      ring
    rw [(isReversible_randomWalk starK13_ne_bot).dirichletForm_eq_sub,
      Fin.sum_univ_four, Fin.sum_univ_four, hπ0, hπ1, hπ2, hπ3,
      hstep0, hstep1, hstep2, hstep3, hsum_leaves]
    have hquad : 1 / 2 * f 0 * (-3 * f 0 / 3) + 1 / 6 * f 1 * f 0 +
        1 / 6 * f 2 * f 0 + 1 / 6 * f 3 * f 0 =
        1 / 6 * (f 1 + f 2 + f 3 + 3 * f 0) * f 0 - f 0 ^ 2 := by ring
    rw [hquad, show f 1 + f 2 + f 3 + 3 * f 0 = 0 by linarith]
    linarith [sq_nonneg (f 0)]
  refine ⟨hgap1, ?_⟩
  have hmix := mixingTime_lazy_randomWalk_le starK13_connected starK13_ne_bot
    (lt_of_lt_of_le zero_lt_one hgap1) (by norm_num : (0 : ℝ) < 1 / 4)
  refine hmix.trans_eq ?_
  rw [starK13_card_edges]
  congr 3
  norm_num

/-! ### 5. Regular multigraph (`RotationMap`) Cheeger mixing witness -/

private def flipRot : RotationMap Bool Unit :=
  ofInvolutive (!·) fun b => Bool.not_not b

private theorem one_le_edgeExpansion_flipRot : 1 ≤ flipRot.edgeExpansion := by
  refine flipRot.le_edgeExpansion_iff.mpr fun S hcard => ?_
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  have hScard : #S = 1 := by
    have hpos : 0 < #S := hne.card_pos
    have h2 : 2 * #S ≤ 2 := by simpa using hcard
    omega
  obtain ⟨b, rfl⟩ := card_eq_one.mp hScard
  have hmem : (b, ()) ∈ flipRot.interedges {b} ({b}ᶜ) := by
    rw [mem_interedges]
    cases b <;> decide
  have h1 : 1 ≤ #(flipRot.interedges {b} ({b}ᶜ)) := card_pos.mpr ⟨(b, ()), hmem⟩
  simpa using (by exact_mod_cast h1 : (1 : ℝ) ≤ #(flipRot.interedges {b} ({b}ᶜ)))

example :
    flipRot.randomWalk.lazy.mixingTime (uniformOfFintype Bool) (1 / 4) ≤
      (⌈(4 * (1 : ℝ) ^ 2 / flipRot.edgeExpansion ^ 2) *
        ((1 / 2) * Real.log 2 + Real.log 2)⌉₊ : ℕ) := by
  have hh : 0 < flipRot.edgeExpansion := lt_of_lt_of_le zero_lt_one one_le_edgeExpansion_flipRot
  refine (mixingTime_lazy_randomWalk_le_of_edgeExpansion (G := flipRot) hh
    (by norm_num : (0 : ℝ) < 1 / 4)).trans_eq ?_
  congr 2
  norm_num

end CslibFrontierTests.MarkovChainSpectral
