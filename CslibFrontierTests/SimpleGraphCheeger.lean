/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Init
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.Cheeger
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Tests for Normalized and Combinatorial Graph Laplacian Cheeger Inequalities

Non-vacuous concrete witnesses exercising
`CslibFrontier.Foundations.Combinatorics.SimpleGraph.Cheeger`:

1. **4-cycle `C_4` (`cycleGraph 4`)**: exact conductance `h_{C_4} = 1 / 2`, exact isoperimetric
   number `h'_{C_4} = 1`, exact normalized spectral gap `λ_{C_4} = 1 = 2 h_{C_4}` (tightness of
   [Chung1997], Lemma 2.1), exact algebraic connectivity `λ'_1(C_4) = 2`, and strict Cheeger lower
   bound `1 / 8 < (cycleGraph 4).normSpectralGap`.
2. **Even complete graphs `K_{2m}` (`⊤ : SimpleGraph (Fin (2 * m))`, `1 ≤ m`)**: infinite regular
   family with `h'_{K_{2m}} = m`, `h_{K_{2m}} = m / (2 m - 1)`, and
   `λ_{K_{2m}} = 2 m / (2 m - 1) = 2 h_{K_{2m}}`.
3. **Irregular barbell family `barbellGraph k` (`Bool × Fin (k + 2)`)**: two `K_{k+2}` cliques
   joined by a single bridge edge (bridge endpoints have degree `k + 2`, non-bridge vertices have
   degree `k + 1`), with exact conductance `h = 1 / ((k + 2)(k + 1) + 1)` and Cheeger bottleneck
   bounds `1 / (2 ((k + 2)(k + 1) + 1)²) < λ ≤ 2 / ((k + 2)(k + 1) + 1)`.
4. **Isolated-vertex model boundary (`edgePlusIsolated` on `Fin 3`)**: single edge `{0, 1}` plus
   isolated vertex `2` (`degree 2 = 0`), which is disconnected with
   `isoperimetricNum = algConnectivity = 0` yet has `conductance = 1 > 0`, witnessing why
   `∀ v, 0 < G.degree v` is required in `connected_iff_conductance_pos` and
   `connected_iff_normSpectralGap_pos`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.SimpleGraphCheeger

open Finset Matrix SimpleGraph

/-! ### 1. Exact conductance and spectral gap of `C_4` -/

theorem cycleGraph_four_isRegular : (cycleGraph 4).IsRegularOfDegree 2 :=
  fun v => cycleGraph_degree_three_le (n := 1) (v := v)

theorem cycleGraph_four_conductance : (cycleGraph 4).conductance = 1 / 2 := by
  have hne_bot : cycleGraph 4 ≠ ⊥ := by
    intro h
    have hadj : (cycleGraph 4).Adj 0 1 := by decide
    rw [h] at hadj
    exact hadj
  refine le_antisymm ?_ ?_
  · let S₀ : Finset (Fin 4) := {0, 1}
    have hvol : (cycleGraph 4).vol S₀ = 4 := by
      rw [cycleGraph_four_isRegular.vol_eq]; decide
    have htot : (cycleGraph 4).totalVol = 8 := by
      rw [totalVol, cycleGraph_four_isRegular.vol_eq]; decide
    have hinter : #((cycleGraph 4).interedges S₀ S₀ᶜ) = 2 := by decide
    have hle := (cycleGraph 4).conductance_le_setConductance (S := S₀) (by
      have hc := (cycleGraph 4).vol_add_vol_compl S₀; omega)
    rw [(cycleGraph 4).setConductance_eq_of_two_mul_vol_le (by omega), hinter, hvol] at hle
    norm_num at hle
    exact hle
  · refine ((cycleGraph 4).le_conductance_iff hne_bot).2 fun S hpos h2 => ?_
    have hcheck : ∀ T : Finset (Fin 4),
        0 < 2 * #T → 2 * (2 * #T) ≤ 2 * #(univ : Finset (Fin 4)) →
          2 * #T ≤ 2 * #((cycleGraph 4).interedges T Tᶜ) := by decide
    rw [cycleGraph_four_isRegular.vol_eq] at hpos h2 ⊢
    rw [totalVol, cycleGraph_four_isRegular.vol_eq] at h2
    have hnat : ((2 * #S : ℕ) : ℝ) ≤ 2 * #((cycleGraph 4).interedges S Sᶜ) := by
      exact_mod_cast hcheck S hpos h2
    push_cast at hnat ⊢
    linarith

theorem cycleGraph_four_isoperimetricNum : (cycleGraph 4).isoperimetricNum = 1 := by
  have h := cycleGraph_four_isRegular.conductance_eq zero_lt_two
  rw [cycleGraph_four_conductance] at h
  linarith

theorem cycleGraph_four_normSpectralGap : (cycleGraph 4).normSpectralGap = 1 := by
  have hle : (cycleGraph 4).normSpectralGap ≤ 1 := by
    have h := (cycleGraph 4).normSpectralGap_le_two_mul_conductance
    rw [cycleGraph_four_conductance] at h
    linarith
  have hne_bot : cycleGraph 4 ≠ ⊥ := by
    intro h
    have hadj : (cycleGraph 4).Adj 0 1 := by decide
    rw [h] at hadj
    exact hadj
  refine le_antisymm hle
    (((cycleGraph 4).le_normSpectralGap_iff hne_bot).2 fun f horth hpos => ?_)
  rw [(cycleGraph 4).normRayleigh_def]
  simp only [cycleGraph_four_isRegular.degree_eq, Nat.cast_ofNat] at horth hpos ⊢
  rw [le_div_iff₀ hpos, one_mul, ← toLinearMap₂'_apply',
    (cycleGraph 4).lapMatrix_toLinearMap₂' ℝ f]
  have hsum4 : f 0 + f 1 + f 2 + f 3 = 0 := by
    rw [Fin.sum_univ_four] at horth
    linarith
  have hdenom4 : ∑ v : Fin 4, f v ^ 2 * 2 = 2 * (f 0 ^ 2 + f 1 ^ 2 + f 2 ^ 2 + f 3 ^ 2) := by
    rw [Fin.sum_univ_four]; ring
  have hnum4 : (∑ i : Fin 4, ∑ j : Fin 4, if (cycleGraph 4).Adj i j then (f i - f j) ^ 2 else 0) =
      2 * ((f 0 - f 1) ^ 2 + (f 1 - f 2) ^ 2 + (f 2 - f 3) ^ 2 + (f 3 - f 0) ^ 2) := by
    simp only [Fin.sum_univ_four]
    have h00 : ¬ (cycleGraph 4).Adj 0 0 := by decide
    have h01 : (cycleGraph 4).Adj 0 1 := by decide
    have h02 : ¬ (cycleGraph 4).Adj 0 2 := by decide
    have h03 : (cycleGraph 4).Adj 0 3 := by decide
    have h10 : (cycleGraph 4).Adj 1 0 := by decide
    have h11 : ¬ (cycleGraph 4).Adj 1 1 := by decide
    have h12 : (cycleGraph 4).Adj 1 2 := by decide
    have h13 : ¬ (cycleGraph 4).Adj 1 3 := by decide
    have h20 : ¬ (cycleGraph 4).Adj 2 0 := by decide
    have h21 : (cycleGraph 4).Adj 2 1 := by decide
    have h22 : ¬ (cycleGraph 4).Adj 2 2 := by decide
    have h23 : (cycleGraph 4).Adj 2 3 := by decide
    have h30 : (cycleGraph 4).Adj 3 0 := by decide
    have h31 : ¬ (cycleGraph 4).Adj 3 1 := by decide
    have h32 : (cycleGraph 4).Adj 3 2 := by decide
    have h33 : ¬ (cycleGraph 4).Adj 3 3 := by decide
    simp only [h00, h01, h02, h03, h10, h11, h12, h13, h20, h21, h22, h23, h30, h31, h32, h33,
      ↓reduceIte]
    ring
  rw [hdenom4, hnum4, mul_div_cancel_left₀ _ two_ne_zero]
  have hid : ((f 0 - f 1) ^ 2 + (f 1 - f 2) ^ 2 + (f 2 - f 3) ^ 2 + (f 3 - f 0) ^ 2) -
      2 * (f 0 ^ 2 + f 1 ^ 2 + f 2 ^ 2 + f 3 ^ 2) =
        2 * (f 0 + f 2) ^ 2 - 2 * (f 0 + f 2) * (f 0 + f 1 + f 2 + f 3) := by ring
  rw [hsum4, mul_zero, sub_zero] at hid
  linarith [sq_nonneg (f 0 + f 2)]

theorem cycleGraph_four_algConnectivity : (cycleGraph 4).algConnectivity = 2 := by
  have h := cycleGraph_four_isRegular.normSpectralGap_eq zero_lt_two
  rw [cycleGraph_four_normSpectralGap] at h
  linarith

theorem cycleGraph_four_strict_cheeger : 1 / 8 < (cycleGraph 4).normSpectralGap := by
  have h := (cycleGraph 4).conductance_sq_div_two_lt_normSpectralGap
    (by rw [cycleGraph_four_conductance]; norm_num)
  rw [cycleGraph_four_conductance] at h
  norm_num at h
  exact h

/-! ### 2. Even complete graphs `K_{2m}` (`⊤ : SimpleGraph (Fin (2 * m))`) -/

private theorem card_interedges_top_compl {W : Type*} [Fintype W] [DecidableEq W] (S : Finset W) :
    #((⊤ : SimpleGraph W).interedges S Sᶜ) = #S * #Sᶜ := by
  have heq : (⊤ : SimpleGraph W).interedges S Sᶜ = S ×ˢ Sᶜ := by
    ext ⟨u, v⟩
    simp only [SimpleGraph.mem_interedges_iff, mem_product, mem_compl, top_adj]
    exact ⟨fun ⟨hu, hv, _⟩ => ⟨hu, hv⟩, fun ⟨hu, hv⟩ => ⟨hu, hv, fun h => hv (h ▸ hu)⟩⟩
  rw [heq, card_product]

theorem complete_even_isoperimetricNum {m : ℕ} (hm : 1 ≤ m) :
    (⊤ : SimpleGraph (Fin (2 * m))).isoperimetricNum = m := by
  let emb : Fin m ↪ Fin (2 * m) :=
    ⟨fun i => ⟨i.val, by omega⟩, fun i j h => Fin.ext (by simpa only [Fin.mk.injEq] using h)⟩
  let S₀ : Finset (Fin (2 * m)) := (univ : Finset (Fin m)).map emb
  have hS₀_card : #S₀ = m := by
    simp only [S₀, card_map, card_univ, Fintype.card_fin]
  have hS₀_2 : 2 * #S₀ ≤ Fintype.card (Fin (2 * m)) := by
    rw [hS₀_card, Fintype.card_fin]
  have : Nontrivial (Fin (2 * m)) := Fin.nontrivial_iff_two_le.2 (by omega)
  refine le_antisymm ?_ ?_
  · have hmul := (⊤ : SimpleGraph (Fin (2 * m))).isoperimetricNum_mul_card_le hS₀_2
    have hcompl := card_add_card_compl S₀
    rw [Fintype.card_fin, hS₀_card] at hcompl
    have hS₀c : #S₀ᶜ = m := by omega
    rw [card_interedges_top_compl, hS₀_card, hS₀c] at hmul
    push_cast at hmul
    have hm_pos : (0 : ℝ) < m := Nat.cast_pos.2 (by omega)
    nlinarith
  · refine (⊤ : SimpleGraph (Fin (2 * m))).le_isoperimetricNum_iff.2 fun S _ h2 => ?_
    have hcompl := card_add_card_compl S
    rw [Fintype.card_fin] at hcompl h2
    have hSc : m ≤ #Sᶜ := by omega
    rw [card_interedges_top_compl, Nat.cast_mul, mul_comm (#S : ℝ)]
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.2 hSc) (Nat.cast_nonneg _)

theorem complete_even_conductance {m : ℕ} (hm : 1 ≤ m) :
    (⊤ : SimpleGraph (Fin (2 * m))).conductance = (m : ℝ) / (2 * m - 1) := by
  have hreg : (⊤ : SimpleGraph (Fin (2 * m))).IsRegularOfDegree (2 * m - 1) := by
    simpa only [Fintype.card_fin] using (IsRegularOfDegree.top (V := Fin (2 * m)))
  rw [hreg.conductance_eq (by omega), complete_even_isoperimetricNum hm,
    Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]

theorem complete_even_normSpectralGap {m : ℕ} (hm : 1 ≤ m) :
    (⊤ : SimpleGraph (Fin (2 * m))).normSpectralGap =
      2 * (⊤ : SimpleGraph (Fin (2 * m))).conductance := by
  rw [normSpectralGap_top (by rw [Fintype.card_fin]; omega), Fintype.card_fin,
    complete_even_conductance hm]
  push_cast
  ring

/-! ### 3. Irregular barbell family `barbellGraph k` (`Bool × Fin (k + 2)`) -/

/-- Two `K_{k+2}` cliques on `{false} × Fin (k + 2)` and `{true} × Fin (k + 2)` joined by the single
bridge edge `((false, 0), (true, 0))`. -/
def barbellGraph (k : ℕ) : SimpleGraph (Bool × Fin (k + 2)) where
  Adj u v := (u.1 = v.1 ∧ u.2 ≠ v.2) ∨ (u.1 ≠ v.1 ∧ u.2 = 0 ∧ v.2 = 0)
  symm := ⟨fun _ _ h => by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · exact Or.inl ⟨h1.symm, h2.symm⟩
    · exact Or.inr ⟨h1.symm, h3, h2⟩⟩
  loopless := ⟨fun _ h => by
    rcases h with ⟨_, h2⟩ | ⟨h1, _, _⟩
    · exact h2 rfl
    · exact h1 rfl⟩

instance (k : ℕ) : DecidableRel (barbellGraph k).Adj :=
  fun u v => inferInstanceAs
    (Decidable ((u.1 = v.1 ∧ u.2 ≠ v.2) ∨ (u.1 ≠ v.1 ∧ u.2 = 0 ∧ v.2 = 0)))

private abbrev sideEmb (k : ℕ) (b : Bool) : Fin (k + 2) ↪ Bool × Fin (k + 2) :=
  ⟨fun j => (b, j), fun _ _ h => (Prod.mk.inj h).2⟩

private theorem sideEmb_apply (k : ℕ) (b : Bool) (j : Fin (k + 2)) :
    sideEmb k b j = (b, j) := rfl

theorem barbellGraph_degree_bridge (k : ℕ) (b : Bool) :
    (barbellGraph k).degree (b, 0) = k + 2 := by
  have hnb : (barbellGraph k).neighborFinset (b, 0) =
      insert (!b, 0) ((univ.erase (0 : Fin (k + 2))).map (sideEmb k b)) := by
    ext ⟨b', j⟩
    rw [(barbellGraph k).mem_neighborFinset]
    simp only [barbellGraph, mem_insert, mem_map, mem_erase, mem_univ, and_true, sideEmb_apply,
      Prod.mk.injEq]
    constructor
    · rintro (⟨hb, hj⟩ | ⟨hb, -, hj0⟩)
      · exact Or.inr ⟨j, hj.symm, hb, rfl⟩
      · refine Or.inl ⟨?_, hj0⟩
        cases b <;> cases b' <;> simp at hb ⊢
    · rintro (⟨rfl, rfl⟩ | ⟨i, hi, rfl, rfl⟩)
      · exact Or.inr ⟨by cases b <;> decide, trivial, rfl⟩
      · exact Or.inl ⟨rfl, hi.symm⟩
  have hnot_mem : (!b, (0 : Fin (k + 2))) ∉
      (univ.erase (0 : Fin (k + 2))).map (sideEmb k b) := by
    simp only [mem_map, mem_erase, mem_univ, and_true, sideEmb_apply, Prod.mk.injEq, not_exists,
      not_and]
    intro j _ hb _
    cases b <;> simp at hb
  rw [← card_neighborFinset_eq_degree, hnb, card_insert_of_notMem hnot_mem, card_map,
    card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
  omega

theorem barbellGraph_degree_nonbridge (k : ℕ) (b : Bool) {j : Fin (k + 2)} (hj : j ≠ 0) :
    (barbellGraph k).degree (b, j) = k + 1 := by
  have hnb : (barbellGraph k).neighborFinset (b, j) =
      (univ.erase j).map (sideEmb k b) := by
    ext ⟨b', i⟩
    rw [(barbellGraph k).mem_neighborFinset]
    simp only [barbellGraph, hj, false_and, and_false, or_false, mem_map, mem_erase, mem_univ,
      and_true, sideEmb_apply, Prod.mk.injEq]
    exact ⟨fun ⟨hb, hij⟩ => ⟨i, hij.symm, hb, rfl⟩, fun ⟨x, hx, hb, hi⟩ => ⟨hb, hi ▸ hx.symm⟩⟩
  rw [← card_neighborFinset_eq_degree, hnb, card_map, card_erase_of_mem (mem_univ j), card_univ,
    Fintype.card_fin]
  omega

/-- `barbellGraph k` is irregular: bridge vertex `(false, 0)` has degree `k + 2` while `(false, 1)`
has degree `k + 1`. -/
theorem barbellGraph_irregular (k : ℕ) :
    (barbellGraph k).degree (false, 0) ≠ (barbellGraph k).degree (false, 1) := by
  have h10 : (1 : Fin (k + 2)) ≠ 0 := by
    intro h
    have := congr_arg Fin.val h
    simp at this
  rw [barbellGraph_degree_bridge, barbellGraph_degree_nonbridge k false h10]
  omega

theorem barbellGraph_connected (k : ℕ) : (barbellGraph k).Connected := by
  refine ((barbellGraph k).connected_iff_exists_forall_reachable).2 ⟨(false, 0), fun ⟨b, j⟩ => ?_⟩
  have hreach_same : ∀ (c : Bool) (i : Fin (k + 2)),
      (barbellGraph k).Reachable (c, 0) (c, i) := fun c i => by
    rcases eq_or_ne i 0 with rfl | hi
    · exact Reachable.refl _
    · exact Adj.reachable (Or.inl ⟨rfl, hi.symm⟩)
  have hbridge_adj : (barbellGraph k).Adj (false, 0) (true, 0) :=
    Or.inr ⟨Bool.false_ne_true, rfl, rfl⟩
  cases b
  · exact hreach_same false j
  · exact hbridge_adj.reachable.trans (hreach_same true j)

private def barbellLeft (k : ℕ) : Finset (Bool × Fin (k + 2)) :=
  univ.filter fun u => u.1 = false

private theorem barbellGraph_vol_half (k : ℕ) (b : Bool) :
    (barbellGraph k).vol (univ.filter fun u : Bool × Fin (k + 2) => u.1 = b) =
      (k + 2) * (k + 1) + 1 := by
  have heq : (univ.filter fun u : Bool × Fin (k + 2) => u.1 = b) =
      (univ : Finset (Fin (k + 2))).map (sideEmb k b) := by
    ext ⟨b', j⟩
    simp only [mem_filter, mem_univ, true_and, mem_map, sideEmb_apply, Prod.mk.injEq,
      exists_eq_right]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  rw [vol, heq, sum_map]
  have hdeg_emb : (∑ x : Fin (k + 2), (barbellGraph k).degree (sideEmb k b x)) =
      ∑ x : Fin (k + 2), (barbellGraph k).degree (b, x) :=
    sum_congr rfl fun _ _ => rfl
  rw [hdeg_emb, ← add_sum_erase _ _ (mem_univ (0 : Fin (k + 2))), barbellGraph_degree_bridge]
  have hrest : ∑ x ∈ univ.erase (0 : Fin (k + 2)), (barbellGraph k).degree (b, x) =
      (k + 1) * (k + 1) := by
    calc ∑ x ∈ univ.erase (0 : Fin (k + 2)), (barbellGraph k).degree (b, x)
        = ∑ _x ∈ univ.erase (0 : Fin (k + 2)), (k + 1) :=
          sum_congr rfl fun x hx => barbellGraph_degree_nonbridge k b (mem_erase.1 hx).1
      _ = (k + 1) * (k + 1) := by
          rw [sum_const, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin, smul_eq_mul,
            show k + 2 - 1 = k + 1 by omega]
  rw [hrest]
  ring

theorem barbellGraph_conductance (k : ℕ) :
    (barbellGraph k).conductance = 1 / (((k + 2) * (k + 1) + 1 : ℕ) : ℝ) := by
  have : Nontrivial (Bool × Fin (k + 2)) :=
    ⟨⟨(false, 0), (true, 0), fun h => by simp at h⟩⟩
  have hleft_vol : (barbellGraph k).vol (barbellLeft k) = (k + 2) * (k + 1) + 1 :=
    barbellGraph_vol_half k false
  have hcompl_eq : (barbellLeft k)ᶜ = univ.filter fun u : Bool × Fin (k + 2) => u.1 = true := by
    ext ⟨b, j⟩
    cases b <;> simp [barbellLeft]
  have hright_vol : (barbellGraph k).vol (barbellLeft k)ᶜ = (k + 2) * (k + 1) + 1 := by
    rw [hcompl_eq]
    exact barbellGraph_vol_half k true
  have htot : (barbellGraph k).totalVol = 2 * ((k + 2) * (k + 1) + 1) := by
    have h := (barbellGraph k).vol_add_vol_compl (barbellLeft k)
    omega
  have hinter_left : (barbellGraph k).interedges (barbellLeft k) (barbellLeft k)ᶜ =
      {((false, 0), (true, 0))} := by
    ext ⟨⟨b1, j1⟩, ⟨b2, j2⟩⟩
    rw [(barbellGraph k).mem_interedges_iff]
    simp only [barbellLeft, mem_compl, mem_filter, mem_univ, true_and, barbellGraph, mem_singleton,
      Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, hb2, ⟨hb_eq, _⟩ | ⟨_, rfl, rfl⟩⟩
      · exact absurd hb_eq.symm hb2
      · refine ⟨⟨rfl, rfl⟩, ?_, rfl⟩
        cases b2
        · exact absurd rfl hb2
        · rfl
    · rintro ⟨⟨rfl, rfl⟩, rfl, rfl⟩
      exact ⟨rfl, fun h => Bool.noConfusion h, Or.inr ⟨Bool.false_ne_true, rfl, rfl⟩⟩
  refine le_antisymm ?_ ?_
  · have hle := (barbellGraph k).conductance_le_setConductance (S := barbellLeft k) (by omega)
    rw [(barbellGraph k).setConductance_eq_of_two_mul_vol_le (by omega), hinter_left,
      card_singleton, Nat.cast_one, hleft_vol] at hle
    exact hle
  · have hlo := (barbellGraph k).two_div_totalVol_le_conductance (barbellGraph_connected k)
    rw [htot, Nat.cast_mul, Nat.cast_ofNat] at hlo
    have hpos : (0 : ℝ) < (((k + 2) * (k + 1) + 1 : ℕ) : ℝ) := Nat.cast_pos.2 (by omega)
    have heq : (2 : ℝ) / (2 * (((k + 2) * (k + 1) + 1 : ℕ) : ℝ)) =
        1 / (((k + 2) * (k + 1) + 1 : ℕ) : ℝ) := by
      field_simp
    rwa [heq] at hlo

theorem barbellGraph_cheeger_bounds (k : ℕ) :
    1 / (2 * (((k + 2) * (k + 1) + 1 : ℕ) : ℝ) ^ 2) < (barbellGraph k).normSpectralGap ∧
      (barbellGraph k).normSpectralGap ≤ 2 / (((k + 2) * (k + 1) + 1 : ℕ) : ℝ) := by
  have : Nontrivial (Bool × Fin (k + 2)) :=
    ⟨⟨(false, 0), (true, 0), fun h => by simp at h⟩⟩
  have hlt := (barbellGraph k).conductance_sq_div_two_lt_normSpectralGap_of_connected
    (barbellGraph_connected k)
  have hle := (barbellGraph k).normSpectralGap_le_two_mul_conductance
  rw [barbellGraph_conductance] at hlt hle
  refine ⟨?_, ?_⟩
  · convert hlt using 1
    ring
  · convert hle using 1
    ring

/-! ### 4. Isolated-vertex model boundary (`edgePlusIsolated` on `Fin 3`) -/

/-- Graph on `Fin 3` with a single edge `{0, 1}` and isolated vertex `2`. -/
def edgePlusIsolated : SimpleGraph (Fin 3) where
  Adj u v := (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0)
  symm := ⟨fun _ _ h => by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨h2, h1⟩
    · exact Or.inl ⟨h2, h1⟩⟩
  loopless := ⟨fun _ h => by rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> exact absurd h (by decide)⟩

instance : DecidableRel edgePlusIsolated.Adj :=
  fun u v => inferInstanceAs (Decidable ((u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0)))

theorem edgePlusIsolated_degree_two : edgePlusIsolated.degree 2 = 0 := by decide

theorem edgePlusIsolated_not_connected : ¬ edgePlusIsolated.Connected := by
  intro hconn
  obtain ⟨p⟩ := hconn 2 0
  obtain ⟨d, -, hd2, _⟩ := p.exists_boundary_dart ({2} : Set (Fin 3)) rfl (by decide)
  have hadj := d.adj
  rw [Set.mem_singleton_iff] at hd2
  rw [hd2] at hadj
  rcases hadj with ⟨h, _⟩ | ⟨h, _⟩ <;> exact absurd h (by decide)

theorem edgePlusIsolated_isoperimetricNum : edgePlusIsolated.isoperimetricNum = 0 := by
  refine le_antisymm ?_ edgePlusIsolated.isoperimetricNum_nonneg
  have hmul :=
    edgePlusIsolated.isoperimetricNum_mul_card_le (S := ({2} : Finset (Fin 3))) (by decide)
  have hinter : #(edgePlusIsolated.interedges ({2} : Finset (Fin 3)) ({2} : Finset (Fin 3))ᶜ) = 0 :=
    by decide
  rw [card_singleton, Nat.cast_one, mul_one, hinter, Nat.cast_zero] at hmul
  exact hmul

theorem edgePlusIsolated_algConnectivity : edgePlusIsolated.algConnectivity = 0 := by
  have hle := edgePlusIsolated.algConnectivity_le_two_mul_isoperimetricNum
  rw [edgePlusIsolated_isoperimetricNum, mul_zero] at hle
  exact le_antisymm hle edgePlusIsolated.algConnectivity_nonneg

/-- Despite being disconnected, `edgePlusIsolated` has `conductance = 1` because `vol {2} = 0`
excludes `{2}` from positive-volume cuts, demonstrating why `∀ v, 0 < G.degree v` is necessary in
`SimpleGraph.connected_iff_conductance_pos`. -/
theorem edgePlusIsolated_conductance : edgePlusIsolated.conductance = 1 := by
  have hne_bot : edgePlusIsolated ≠ ⊥ := by
    intro h
    have hadj : edgePlusIsolated.Adj 0 1 := Or.inl ⟨rfl, rfl⟩
    rw [h] at hadj
    exact hadj
  refine le_antisymm edgePlusIsolated.conductance_le_one ?_
  refine (edgePlusIsolated.le_conductance_iff hne_bot).2 fun S hpos h2 => ?_
  rw [one_mul]
  have hcheck : ∀ T : Finset (Fin 3),
      0 < edgePlusIsolated.vol T → 2 * edgePlusIsolated.vol T ≤ edgePlusIsolated.totalVol →
        edgePlusIsolated.vol T ≤ #(edgePlusIsolated.interedges T Tᶜ) := by
    simp only [vol, totalVol]
    decide
  exact_mod_cast hcheck S hpos h2

end CslibFrontierTests.SimpleGraphCheeger
