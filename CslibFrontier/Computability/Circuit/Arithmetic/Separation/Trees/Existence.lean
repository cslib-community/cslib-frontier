/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Trees.ThinTrees
public import CslibFrontier.Foundations.GroupTheory.SLTower.Tower
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.PlayMoves
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.BaseChange
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Trees.SLTowers
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Trees.TreeProgram
import CslibFrontier.Foundations.Data.Nat.Power

/-!
# The existence of thin trees

Theorem H.2 of [AnthropicVPVNP2026] (pp. 45–46): for laws at the vertices of the tower of `U_h`
whose contraction satisfies `1 + 8 C₁ ≤ h / 4`, there is a constant `C` such that every network on
at most `M ≥ 2` nodes, over any algebra, with units of `ℓ ≥ 1` bits and at most `N ≥ 1` units at a
node, is a sum of networks on thin trees (`ThinTrees`), with `Λ = (lg M) ^ C`, `b = 2 ^ e(h)` and
`γ = 1 / log b`.

The proof is the paper's (pp. 46–48). For the least `n` with `M ≤ |G_n|` the tower
`SLTower.tower h n`, with routes and with the laws transferred to it and mapped to the algebra,
satisfies `TowerConstants` with one constant `c` for all `n` and has `|G_n| ≤ c M` (`exists_towers`,
in `SLTowers.lean`). The tower plan (`TowerPlan.towerPlan`) on this tower is the plan of the
theorem, its tree (`treeParent`, `treeUnits`) is the tree, and the bounds of the tower plan and of
its tree (`TowerTree.lean`, `TreeProgram.lean`) are absorbed in the exponent `C`.

## Main results

* `exists_thinTrees`: Theorem H.2.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Proposition H.1 (p. 44) and Theorem H.2 (pp. 45–46), with its proof (pp. 46–48); modules
  `Paper.Tower` and `Paper.Tree`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Trees

open Finset Cslib.CoveringTower Cut TowerPlan Interpreter

/-! ### Numbers -/

/-- A power of a constant times `Z ≥ 2` is a power of `Z`. -/
private theorem mul_pow_le_pow {c Z a C : ℕ} (hZ : 2 ≤ Z) (h : (c + 4) * a ≤ C) :
    ((c + 3) * Z) ^ a ≤ Z ^ C :=
  have h1 : (c + 3) * Z ^ 1 ≤ Z ^ (c + 4) := Nat.mul_pow_le_pow_of_add_le hZ le_rfl
  calc ((c + 3) * Z) ^ a ≤ (Z ^ (c + 4)) ^ a := Nat.pow_le_pow_left (by simpa using h1) a
    _ = Z ^ ((c + 4) * a) := by rw [← pow_mul]
    _ ≤ Z ^ C := Nat.pow_le_pow_right (by omega) h

/-- The gain as a power of `M`: `B ^ q X ≤ A ^ q` with `0 < M ≤ X` gives `B ≤ A M ^ (-1 / q)`. -/
private theorem le_mul_rpow_neg {B A M X q : ℕ} (hq : 0 < q) (hM : 0 < M) (hX : M ≤ X)
    (h : B ^ q * X ^ 1 ≤ A ^ q) : (B : ℝ) ≤ A * (M : ℝ) ^ (-(1 / (q : ℝ))) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have h1 : ((B : ℝ) * (M : ℝ) ^ (1 / (q : ℝ))) ^ q ≤ (A : ℝ) ^ q := by
    rw [mul_pow, ← Real.rpow_natCast ((M : ℝ) ^ (1 / (q : ℝ))) q, ← Real.rpow_mul hM0.le,
      one_div_mul_cancel (by exact_mod_cast hq.ne'), Real.rpow_one]
    rw [pow_one] at h
    exact_mod_cast (Nat.mul_le_mul_left _ hX).trans h
  rw [Real.rpow_neg hM0.le, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  exact le_of_pow_le_pow_left₀ hq.ne' (Nat.cast_nonneg A) h1

/-- The factor of `lg M ^ 7 M (N + M ^ 2)` in the bounds for the units of the tree. -/
private def treeFactor (c : ℕ) : ℕ := 2 * c * (c * (c * (c + 1) ^ 7 * c * (1 + 2 * c ^ 2)))

/-- The exponent `C` of the thin trees of the towers with the constant `c`. -/
private def treeExponent (c : ℕ) : ℕ :=
  (c + 4) * 2500 + (c + 1) * treeFactor c + (4 + (2 * c * c + 1 + c) * c) * 8 +
    8 * (c * (c + 1) ^ 7) + 8

private theorem le_treeExponent (c : ℕ) :
    (c + 4) * 2500 ≤ treeExponent c ∧ (c + 1) * treeFactor c + 7 ≤ treeExponent c ∧
      (4 + (2 * c * c + 1 + c) * c) * 8 ≤ treeExponent c ∧
      1 + 8 * (c * (c + 1) ^ 7) + 7 ≤ treeExponent c := by
  unfold treeExponent
  omega

/-- The bound `2 c constNormBound` by `lg M ^ 7 M (N + M ^ 2)`. -/
private theorem two_mul_constNormBound_le {c m X M J N : ℕ} (hX : X ≤ c * M)
    (hm : m ≤ c * (J + 1) ^ 7) (hJ : J + 1 ≤ (c + 1) * lg M) :
    2 * c * constNormBound c m X N ≤ treeFactor c * (lg M ^ 7 * M * (N + M ^ 2)) := by
  have h1 : N + 2 * X ^ 2 ≤ (1 + 2 * c ^ 2) * (N + M ^ 2) := by
    have : X ^ 2 ≤ (c * M) ^ 2 := Nat.pow_le_pow_left hX 2
    nlinarith
  have h2 : m ≤ c * ((c + 1) ^ 7 * lg M ^ 7) :=
    hm.trans (Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left hJ 7).trans_eq (mul_pow _ _ _)))
  calc 2 * c * constNormBound c m X N ≤
      2 * c * (c * (c * ((c + 1) ^ 7 * lg M ^ 7) * (c * M) * ((1 + 2 * c ^ 2) * (N + M ^ 2)))) := by
        unfold constNormBound
        gcongr
    _ = _ := by unfold treeFactor; ring

/-! ### The thin trees of one tower -/

section Tower

variable {R : Type*} [CommSemiring R] {h b D J m Uu c q M A N ℓ C : ℕ} {T : Tower h b D J 1}
  {FL : VertexLaws R T} {laws : List (Law R)} {ρ : ℝ}

/-- The sizes of a tower under the conditions, for `|X 0| ≤ c M` and `M ≤ Z`: the constant, the
number of stages, the base parties and the chambers of the level `0` are at most `(c + 3) Z`, and
the length of the routes at most its eighth power. -/
private theorem sizes_le (hC : TowerConstants FL laws c ρ 1 q) (hm : m ≤ c * (J + 1) ^ 7)
    (hX : Fintype.card (T.X 0) ≤ c * M) (hA : A ≤ M) {Z : ℕ} (hMZ : M ≤ Z) :
    c ≤ (c + 3) * Z ∧ m ≤ ((c + 3) * Z) ^ 8 ∧ J + 1 ≤ (c + 3) * Z ∧ A ≤ (c + 3) * Z ∧
      Fintype.card (T.X 0) ≤ (c + 3) * Z := by
  have hc := hC.one_le
  have hJX : J + 1 ≤ Fintype.card (T.X 0) := Nat.lt_two_pow_self.trans_le
    ((Nat.pow_le_pow_left hC.two_lt_ratio.le J).trans (T.pow_le_card_X_zero hC.card_X_last_pos))
  have hZ : 1 ≤ Z :=
    (Nat.pos_of_ne_zero fun h0 => absurd (hJX.trans hX) (by simp [h0])).trans_le hMZ
  have hXG : Fintype.card (T.X 0) ≤ (c + 3) * Z := hX.trans (Nat.mul_le_mul (by omega) hMZ)
  refine ⟨Nat.le_mul_of_pos_right _ hZ |>.trans' (by omega), hm.trans ?_, hJX.trans hXG,
    hA.trans (hMZ.trans (Nat.le_mul_of_pos_left Z (by omega))), hXG⟩
  calc c * (J + 1) ^ 7 ≤ ((c + 3) * Z) * ((c + 3) * Z) ^ 7 :=
        Nat.mul_le_mul ((Nat.le_mul_of_pos_right _ hZ).trans' (by omega))
          (Nat.pow_le_pow_left (hJX.trans hXG) 7)
    _ = _ := (pow_succ' _ _).symm

/-- **The thin trees of one tower** (the proof of Theorem H.2 of [AnthropicVPVNP2026],
pp. 46–48): the tower plan on a tower with routes, laws and the conditions `TowerConstants` with
`r = 1` and `p = 1`, for `M ≤ |X 0| ≤ c M`. -/
private theorem exists_thinTrees_of_tower (Rt : Routes T m Uu)
    (hC : TowerConstants FL laws c ρ 1 q) (hC0 : treeExponent c ≤ C) (hm1 : 1 ≤ m)
    (hm : m ≤ c * (J + 1) ^ 7) (hUu : Uu ≤ 2 * Fintype.card (T.X 0) * m) (hM : 2 ≤ M)
    (hX1 : M ≤ Fintype.card (T.X 0)) (hX2 : Fintype.card (T.X 0) ≤ c * M) (hA : A ≤ M)
    (hN : 1 ≤ N) (hℓ : 1 ≤ ℓ) :
    Nonempty (ThinTrees laws A N ℓ M b FL.lengthBound C (1 / (q : ℝ))) := by
  obtain ⟨e1, e2, e3, e4⟩ := le_treeExponent c
  have hH := hC.toStageRate
  have hc := hC.one_le
  have hl : 2 ≤ lg M := le_lg_of_two_pow_le (k := 1) hM
  have hD : 0 < D := by have := hC.two_lt_ratio; omega
  have hAX : A ≤ Fintype.card (T.X 0) := hA.trans hX1
  have hdep := hC.succ_depth_le hX2
  have hq : 0 < q := by have := hC.two_mul_le; omega
  obtain ⟨ch⟩ := Function.Embedding.nonempty_of_card_le (α := Fin A) (β := T.X 0)
    (by simpa using hAX)
  obtain ⟨Pl⟩ := exists_placement T ch
  have hMN : 2 ≤ M * N := hM.trans (Nat.le_mul_of_pos_right _ hN)
  -- the sizes, as powers of `G`
  obtain ⟨G, hG⟩ : ∃ G, G = (c + 3) * (M * N) := ⟨_, rfl⟩
  have hG3 : 3 ≤ G := hG ▸ (Nat.le_add_left 3 c).trans (Nat.le_mul_of_pos_right _ (by omega))
  have gp {a a' : ℕ} (h : a ≤ a') : G ^ a ≤ G ^ a' := Nat.pow_le_pow_right (by omega) h
  have gk {k a a' : ℕ} (hk : k ≤ 27) (ha : a + 3 ≤ a') : k * G ^ a ≤ G ^ a' := by
    refine le_trans ?_ (gp ha)
    rw [pow_add, mul_comm]
    exact Nat.mul_le_mul_left _ (hk.trans (Nat.pow_le_pow_left hG3 3))
  have hMG : M ≤ G :=
    hG ▸ (Nat.le_mul_of_pos_right _ hN).trans (Nat.le_mul_of_pos_left _ (by omega))
  have hNG : N ≤ G := hG ▸ (Nat.le_mul_of_pos_left _ (by omega)).trans
    (Nat.le_mul_of_pos_left _ (by omega))
  have hcG : c ≤ G := hG ▸ (Nat.le_add_right c 3).trans (Nat.le_mul_of_pos_right _ (by omega))
  obtain ⟨hcG, hmG, hJG, hAG, hXG⟩ := sizes_le hC hm hX2 hA (Z := M * N)
    (Nat.le_mul_of_pos_right _ hN)
  rw [← hG] at hcG hmG hJG hAG hXG
  set X := Fintype.card (T.X 0) with hX
  have hcnb : constNormBound c m X N ≤ G ^ 15 := by
    unfold constNormBound
    calc c * (m * X * (N + 2 * X ^ 2)) ≤ G * (G ^ 8 * G * (G ^ 2 + 2 * G ^ 2)) := by
          gcongr
          exact hNG.trans (Nat.le_self_pow (by norm_num) G)
      _ = 3 * G ^ 12 := by ring
      _ ≤ G ^ 15 := gk (by norm_num) (by norm_num)
  have hcap : constMoveCap c m X N N ≤ G ^ 22 := by
    unfold constMoveCap
    have h1 : 3 * c * constNormBound c m X N ≤ G ^ 19 :=
      (Nat.mul_le_mul (Nat.mul_le_mul_left 3 hcG) hcnb).trans
        (by rw [mul_assoc, ← pow_succ']; exact gk (by norm_num) (by norm_num))
    have h2 : 3 * G ^ 1 ≤ G ^ 19 := gk (by norm_num) (by norm_num)
    have h3 : 2 * G ^ 19 ≤ G ^ 22 := gk (by norm_num) (by norm_num)
    rw [pow_one] at h2
    omega
  -- the outcomes are below `U1`
  obtain ⟨U1, hU1⟩ : ∃ U1, U1 = constMoveCap c m X N N * (c + c) + 1 := ⟨_, rfl⟩
  have hU1G : U1 ≤ G ^ 26 := by
    have h1 : constMoveCap c m X N N * (c + c) ≤ 2 * G ^ 23 :=
      (Nat.mul_le_mul hcap (show c + c ≤ 2 * G by omega)).trans_eq (by ring)
    have h2 : 3 * G ^ 23 ≤ G ^ 26 := gk (by norm_num) (by norm_num)
    have h3 : 1 ≤ G ^ 23 := Nat.one_le_pow _ _ (by omega)
    omega
  -- the sizes of the plan
  have hGV {a : ℕ} (ha : a ≤ G) : a ≤ G ^ 26 := ha.trans (Nat.le_self_pow (by norm_num) G)
  have hV : SizeBound FL m A (G ^ 26) := hC.sizeBound (hGV hcG) (hmG.trans (gp (by norm_num)))
    (hGV (by omega)) (hGV hAG) (hGV hXG)
  have gkV {k e a' : ℕ} (hk : k ≤ 27) (ha : 26 * e + 3 ≤ a') : k * (G ^ 26) ^ e ≤ G ^ a' :=
    (Nat.mul_le_mul_left k (pow_mul G 26 e).symm.le).trans (gk hk ha)
  have hmove := (card_move_le (R := Rt) (ch := ch) hD hV hH.b_pos).trans (gkV (by norm_num) le_rfl)
  have hchan := (card_moveChannel_le (R := Rt) (ch := ch) hD hV).trans (gkV (by norm_num) le_rfl)
  have hslot := (card_moveSlot_le (R := Rt) (ch := ch) hD hV hH.b_pos).trans
    (gkV (by norm_num) le_rfl)
  have hunit := (card_planUnit_le (R := Rt) hD hV Pl (hGV hNG) hU1G).trans
    (gkV (by norm_num) le_rfl)
  have htgt := (card_target_le (m := m) (A := A) hD hV hH.b_pos).trans (gkV (by norm_num) le_rfl)
  have hnode' := (card_node_le hD hV).trans (gkV (by norm_num) le_rfl)
  have hpair : Fintype.card (Sym2 T.Fl) ≤ G := hC.card_pair_le.trans hcG
  have hB : ProgramBound Rt ch FL N U1 (G ^ 190) := {
    base_mul_base_le :=
      (Nat.mul_le_mul hAG hAG).trans ((pow_two G).symm.le.trans (gp (by norm_num)))
    numUnits_le := (card_planUnit Pl).symm.le.trans (hunit.trans (gp (by norm_num)))
    card_channel_le := hchan.trans (gp (by norm_num))
    card_move_le := hmove.trans (gp (by norm_num))
    card_target_le := htgt.trans (gp (by norm_num))
    card_node_le := hnode'.trans (gp (by norm_num))
    card_pair_le := hpair.trans (Nat.le_self_pow (by norm_num) G)
    card_kind_le := (hC.card_kind_le.trans hcG).trans (Nat.le_self_pow (by norm_num) G)
    types_le := (hC.types_le.trans hcG).trans (Nat.le_self_pow (by norm_num) G)
    endTime_le := by
      have := gk (k := 9) (a := 8) (a' := 11) (by norm_num) le_rfl
      have := Nat.le_self_pow (n := 8) (by decide) G
      have := gp (a := 11) (a' := 190) (by norm_num)
      unfold endTime
      omega
    units_le := by
      have h1 : b * Fintype.card (Sym2 T.Fl) * numUnits Rt ch FL N U1 ≤ G ^ 187 :=
        (Nat.mul_le_mul (Nat.mul_le_mul (hC.places_le.trans hcG) hpair)
          ((card_planUnit Pl).symm.le.trans hunit)).trans_eq (by ring)
      have := gk (k := 3) (a := 187) (a' := 190) (by norm_num) le_rfl
      have := Nat.one_le_pow 187 G (by omega)
      omega }
  have hB' : UnitBound Rt FL Pl N U1 (G ^ 190) 0 :=
    ⟨hslot.trans (gp (by norm_num)), hunit.trans (gp (by norm_num)), Nat.zero_le _⟩
  have hMNC {a : ℕ} (ha : a ≤ 2500) : G ^ a ≤ (M * N) ^ C :=
    (gp ha).trans (hG ▸ mul_pow_le_pow hMN (e1.trans hC0))
  have hY : StepBase ((M * N) ^ C) (G ^ 190) :=
    ⟨hG3.trans (Nat.le_self_pow (by norm_num) G), by rw [← pow_mul]; exact hMNC (by norm_num)⟩
  have hsteps : Fintype.card ((Fin A × Fin A) ⊕ (moves Rt FL Pl).Channel) +
      (22 + 8 * G ^ 190) * (G ^ 190) ^ 12 ≤ (M * N) ^ C := by
    rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_congr (moveChannelEquiv Rt FL Pl)]
    have h1 : (22 + 8 * G ^ 190) * (G ^ 190) ^ 12 ≤ 30 * G ^ 2470 := by
      have := Nat.one_le_pow 190 G (by omega)
      calc (22 + 8 * G ^ 190) * (G ^ 190) ^ 12 ≤
          (22 * G ^ 190 + 8 * G ^ 190) * (G ^ 190) ^ 12 := Nat.mul_le_mul_right _ (by omega)
        _ = 30 * G ^ 2470 := by ring
    have h2 : 30 * G ^ 2470 ≤ G ^ 2476 := by
      have := gk (k := 10) (a := 2470) (a' := 2473) (by norm_num) le_rfl
      have := gk (k := 3) (a := 2473) (a' := 2476) (by norm_num) le_rfl
      omega
    have h3 : A * A ≤ G ^ 2476 := (Nat.mul_le_mul hAG hAG).trans
      ((pow_two G).symm.le.trans (gp (by norm_num)))
    have := gk (k := 3) (a := 2476) (a' := 2479) (by norm_num) le_rfl
    have := hMNC (a := 2479) (by norm_num)
    have := hchan.trans (gp (a' := 2476) (by norm_num))
    omega
  obtain ⟨prog⟩ := exists_treeProgram (R := Rt) (FL := FL) (Pl := Pl) hH.h_pos hH.b_pos N hY hB
    hB' hsteps
  -- the units of the tree
  have hBh : (edgeUnitBound FL Uu A N ρ : ℝ) ≤ ((treeFactor c * lg M ^ 7 : ℕ) : ℝ) *
      (M : ℝ) ^ (1 - 1 / (q : ℝ)) * (N + (M : ℝ) ^ 2) := by
    refine (le_mul_rpow_neg hq (by omega) hX1 (hC.edgeUnitBound_pow_mul_le hm1 hUu hAX)).trans ?_
    have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
    calc ((2 * c * constNormBound c m X N : ℕ) : ℝ) * (M : ℝ) ^ (-(1 / (q : ℝ))) ≤
        ((treeFactor c * (lg M ^ 7 * M * (N + M ^ 2)) : ℕ) : ℝ) * (M : ℝ) ^ (-(1 / (q : ℝ))) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast two_mul_constNormBound_le hX2 hm hdep)
            (Real.rpow_nonneg hM0.le _)
      _ = _ := by
          rw [sub_eq_add_neg, Real.rpow_add hM0, Real.rpow_one]
          push_cast
          ring
  have hnode {k : ℕ} (hk : k ≤ (c + 1) * edgeUnitBound FL Uu A N ρ) :
      (k : ℝ) ≤ (lg M ^ C : ℕ) * (M : ℝ) ^ (1 - 1 / (q : ℝ)) * (N + (M : ℝ) ^ 2) := by
    have h3 : (c + 1) * (treeFactor c * lg M ^ 7) ≤ lg M ^ C := by
      rw [← mul_assoc]
      exact Nat.mul_pow_le_pow_of_add_le hl (by omega)
    calc (k : ℝ) ≤ ((c + 1 : ℕ) : ℝ) * edgeUnitBound FL Uu A N ρ := by exact_mod_cast hk
      _ ≤ ((c + 1 : ℕ) : ℝ) * (((treeFactor c * lg M ^ 7 : ℕ) : ℝ) *
          (M : ℝ) ^ (1 - 1 / (q : ℝ)) * (N + (M : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hBh (Nat.cast_nonneg _)
      _ = (((c + 1) * (treeFactor c * lg M ^ 7) : ℕ) : ℝ) * (M : ℝ) ^ (1 - 1 / (q : ℝ)) *
          (N + (M : ℝ) ^ 2) := by push_cast; ring
      _ ≤ _ := by gcongr
  have htot : treeUnitBound FL Uu A N ρ ≤ lg M ^ C * M * (N + M ^ 2) := by
    have h0 : treeFactor c * c ≤ (c + 1) * treeFactor c := by
      rw [mul_comm]
      exact Nat.mul_le_mul_right _ (Nat.le_succ c)
    have h1 : treeFactor c * c * lg M ^ 7 ≤ lg M ^ C :=
      Nat.mul_pow_le_pow_of_add_le hl (by omega)
    calc treeUnitBound FL Uu A N ρ ≤ 2 * c * constNormBound c m X N * c :=
          hC.treeUnitBound_le hm1 hUu hAX
      _ ≤ treeFactor c * (lg M ^ 7 * M * (N + M ^ 2)) * c :=
          Nat.mul_le_mul_right _ (two_mul_constNormBound_le hX2 hm hdep)
      _ = treeFactor c * c * lg M ^ 7 * (M * (N + M ^ 2)) := by ring
      _ ≤ lg M ^ C * (M * (N + M ^ 2)) := Nat.mul_le_mul_right _ h1
      _ = _ := by ring
  -- the units that a party ever holds
  have hK : (4 + (2 * Fintype.card T.Nr * FL.lengthBound + 1 + c) * Fintype.card FL.Kind) * 8 ≤
      C := by
    refine le_trans ?_ (e3.trans hC0)
    gcongr
    exacts [hC.card_nearPair_le, hC.lengthBound_le, hC.card_kind_le]
  have hbase : N + 8 * m * N ≤ lg M ^ C * N := by
    have h1 : m ≤ c * ((c + 1) ^ 7 * lg M ^ 7) :=
      hm.trans (Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left hdep 7).trans_eq (mul_pow _ _ _)))
    have h2 : 1 ≤ lg M ^ 7 := Nat.one_le_pow _ _ (by omega)
    have h3 : (1 + 8 * (c * (c + 1) ^ 7)) * lg M ^ 7 ≤ lg M ^ C :=
      Nat.mul_pow_le_pow_of_add_le hl (by omega)
    calc N + 8 * m * N = (1 + 8 * m) * N := by ring
      _ ≤ (lg M ^ 7 + 8 * (c * ((c + 1) ^ 7 * lg M ^ 7))) * N := Nat.mul_le_mul_right _ (by omega)
      _ = (1 + 8 * (c * (c + 1) ^ 7)) * lg M ^ 7 * N := by ring
      _ ≤ lg M ^ C * N := Nat.mul_le_mul_right _ h3
  -- the dead units
  have hdead : Fintype.card (MoveChannel Rt ch FL) ≤ M ^ C := by
    obtain ⟨h1, h2, h3, h4, h5⟩ := sizes_le hC hm hX2 hA (le_refl M)
    have hG0 : 3 ≤ (c + 3) * M := (Nat.le_add_left 3 c).trans (Nat.le_mul_of_pos_right _ (by omega))
    have h8 {a : ℕ} (ha : a ≤ (c + 3) * M) : a ≤ ((c + 3) * M) ^ 8 :=
      ha.trans (Nat.le_self_pow (by norm_num) _)
    refine (card_moveChannel_le hD
      (hC.sizeBound (h8 h1) h2 (h8 (by omega)) (h8 h4) (h8 h5))).trans ?_
    calc 17 * (((c + 3) * M) ^ 8) ^ 6 ≤ ((c + 3) * M) ^ 3 * ((c + 3) * M) ^ 48 := by
          rw [← pow_mul]
          exact Nat.mul_le_mul_right _
            ((by norm_num : 17 ≤ 3 ^ 3).trans (Nat.pow_le_pow_left hG0 3))
      _ = ((c + 3) * M) ^ 51 := by ring
      _ ≤ M ^ C := mul_pow_le_pow hM (by omega)
  -- the moves
  have hlaw (mv : Move Rt ch FL) :
      (mv.isVertex = true → mv.law ∈ laws) ∧ (mv.isVertex = false → mv.law = relayLaw R) := by
    rcases mv with _ | l
    · exact ⟨fun h => by simp [Move.isVertex] at h, fun _ => rfl⟩
    · exact ⟨fun _ => hC.law_mem _, fun h => by simp [Move.isVertex] at h⟩
  have hlen (mv : Move Rt ch FL) : mv.law.LengthLE c ∧ mv.law.labelLength ≤ c := by
    rcases mv with _ | l
    · exact ⟨fun _ _ => hc, Nat.zero_le _⟩
    · exact ⟨hC.lengthLE _ (hC.law_mem _), hC.labelLength_le _ (hC.law_mem _)⟩
  have hstage (mv : Move Rt ch FL) (hv : mv.isVertex = true) (p : mv.law.Role) :
      0 < (mv.party p).stage := by
    rcases mv with _ | l
    · simp [Move.isVertex] at hv
    · exact Nat.succ_pos _
  have hgoodIff (mv : Move Rt ch FL) (n' : Fin A → Fin A → ℕ) (o' : MoveChannel Rt ch FL → ℕ) :
      GoodOutcome N n' o' mv ↔ if mv.isVertex then
        b * ∑ ν, o' ⟨mv, ν⟩ ^ 2 ≤ FL.lengthBound * moveCount N n' o' mv ^ 2 ∧
          ∀ ν, moveCount N n' o' mv ≤ o' ⟨mv, ν⟩
      else ∀ ν, o' ⟨mv, ν⟩ = moveCount N n' o' mv := by
    rcases mv with _ | l
    · exact Iff.rfl
    · simp only [Move.isVertex, ↓reduceIte, GoodOutcome, VertexMove.OutcomeShort, one_mul]
      exact Iff.rfl
  have hok := towerPlan_ok_moveCap (R := Rt) (Pl := Pl) (lhat := N) (U0 := N) (U1 := U1) hH
    hC.rate_lt_one.le
  have hgood (n : Fin A → Fin A → Fin (N + 1)) (o : (moves Rt FL Pl).Channel → Fin U1) (x)
      (hp : (towerPlan Rt FL Pl N N U1).Possible n o ℓ x) :
      (towerPlan Rt FL Pl N N U1).Good n o x :=
    towerPlan_good_of_possible hℓ hp
  have hU1' (x : Fin (Fintype.card (Move Rt ch FL))) :
      moveCap FL N Uu A N * (c + ((moves Rt FL Pl).law x).labelLength) + 1 ≤ U1 := by
    rw [hU1]
    exact Nat.add_le_add_right (Nat.mul_le_mul (hC.moveCap_le_constMoveCap hm1 hUu hAX)
      (Nat.add_le_add_left (hlen _).2 c)) 1
  have hInit {n : Fin A → Fin A → Fin (N + 1)} (hn : ∀ a, ∑ c, ((n a c : ℕ) + n c a) ≤ N) :
      InitialBound N (initialCounts n) := fun a =>
    (sum_le_sum fun c _ => by split_ifs <;> simp [initialCounts]).trans (hn a)
  have hroot := hC.card_X_last_le
  exact ⟨{
    A' := Fintype.card T.Node - A
    E := Fintype.card (Move Rt ch FL)
    U1 := U1
    U1_pos := by omega
    moves := moves Rt FL Pl
    plan := towerPlan Rt FL Pl N N U1
    decidableGood := fun _ _ _ => Classical.propDecidable _
    cap := moveCap FL N Uu A N
    ok := hok
    isLaw := fun x => (moveOrder Rt ch FL x).isVertex
    law_mem := fun x => (hlaw _).1
    law_eq_relay := fun x => (hlaw _).2
    good_iff := fun n o x => by
      have := hgoodIff (moveOrder Rt ch FL x) (initialCounts n) (outcomeOf Rt FL Pl o)
      simp only [outcomeOf_moveOrder] at this
      exact this
    good_of_possible := hgood
    value := fun n init hloc hinit => by
      classical
      exact Plan.value_moves hok hℓ hgood (m := fun _ => c) (fun x => (hlen _).1) hU1' n init
        hloc hinit
    stage := fun p => (Pl.party.symm p).stage
    depth := J + 1
    root := Pl.party .root
    parent := treeParent Rt FL Pl hH.h_pos N
    units := treeUnits Rt FL Pl N
    dead := deadUnits N Rt FL Pl
    depth_le := hdep.trans (by
      simpa using Nat.mul_pow_le_pow_of_add_le hl (e := 1) (show c + 1 + 1 ≤ C by omega))
    stage_le := fun p => Tower.Node.stage_le _
    stage_base := fun a => by rw [← Pl.party_base, Equiv.symm_apply_apply]; rfl
    stage_eq_depth_iff := fun p => Tower.Node.stage_eq_iff.trans Pl.party.symm_apply_eq
    stage_parent := fun n o p hp => by
      rw [treeParent, Equiv.symm_apply_apply]
      exact Tower.Node.stage_parent _ _ fun h0 => hp (by rw [← h0, Equiv.apply_symm_apply])
    card_children_le := fun n o p hp => card_children_le _ hp
    card_children_root_le := fun n o => (card_children_root_le _).trans (by omega)
    card_dead_le := fun o => card_image_le.trans ((Fintype.card_congr
      (moveChannelEquiv Rt FL Pl)).le.trans hdead)
    stage_pos := fun r hr => by
      change 0 < (Pl.party.symm (Pl.party ((moveOrder Rt ch FL r.1).party r.2))).stage
      rw [Equiv.symm_apply_apply]
      exact hstage _ hr _
    exists_parent := fun n hn o hg u hu => exists_parent _ (hInit hn) hg hu
    card_between_le := fun n hn o hg p hp => card_between_le _ (hInit hn) hg hp
    units_add_sum_le := fun n o p =>
      hnode (treeUnits_add_sum_le hH _ hC.places_le hC.card_X_last_le p)
    sum_units_le := fun n o => (sum_treeUnits_le hH hC.rate_lt_one).trans htot
    sum_count_le := fun n o hg p => sum_count_le_card_seenAt hg hC.exists_nearPair p
    card_held_add_le := fun n hn o hg p => by
      refine (card_held_add_le hH.r_pos hH.b_pos hH.h_pos hg hC.exists_nearPair hC.card_slot_le hn
        p).trans (add_le_add (add_le_add (Nat.mul_le_mul_right _ hK) ?_)
          (Nat.mul_le_mul_right _ (by omega)))
      split_ifs
      exacts [hbase, le_rfl]
    program := prog
    parties_le := (Placement.card_node Pl).symm.le.trans (hnode'.trans (hMNC (by norm_num)))
    moves_le := hmove.trans (hMNC (by norm_num))
    U1_le := hU1G.trans (hMNC (by norm_num))
    card_unit_le := hunit.trans (hMNC (by norm_num)) }⟩

end Tower

/-- **Thin trees** (Theorem H.2 of [AnthropicVPVNP2026], pp. 45–46): for laws at the vertices of
the tower of `U_h` (Theorem G.2, as `Laws.exists_vertexLaws` gives them) whose contraction
satisfies `1 + 8 C₁ ≤ h / 4`, there is a constant `C` such that for every algebra `R` over their
ring, `M ≥ 2`, `A ≤ M` given nodes, `N ≥ 1` and `ℓ ≥ 1` there are thin trees (`ThinTrees`) with
the laws mapped to `R`, the bound `b = 2 ^ e(h)` of the children, the integer `lengthBound` of the
test of the law moves, the exponent `C` and `γ = 1 / log₂ b`. -/
theorem exists_thinTrees {A₀ : Type*} [CommSemiring A₀] {h : ℕ} [NeZero h] (h3 : 3 ≤ h)
    (FL : VertexLaws A₀ (SLTower.tower h 0 (by omega)))
    (hgain : 1 + 8 * FL.contraction ≤ (h : ℝ) / 4) :
    ∃ C : ℕ, ∀ (R : Type*) [CommSemiring R] [Algebra A₀ R] (M A N ℓ : ℕ), 2 ≤ M → A ≤ M →
      1 ≤ N → 1 ≤ ℓ → Nonempty (ThinTrees
        (((univ : Finset FL.Kind).toList.map FL.law).map fun L => L.map (algebraMap A₀ R))
        A N ℓ M (2 ^ SLTower.ee h) FL.lengthBound C
        (1 / Real.logb 2 ((2 ^ SLTower.ee h : ℕ) : ℝ))) := by
  obtain ⟨c, hc⟩ := exists_towers h3 FL hgain
  refine ⟨treeExponent c, fun R _ _ M A N ℓ hM hA hN hℓ => ?_⟩
  obtain ⟨n, m, Uu, ⟨Rt⟩, hC, hX1, hX2, hm1, hm, hUu⟩ := hc R (algebraMap A₀ R) M (by omega)
  have e : Real.logb 2 ((2 ^ SLTower.ee h : ℕ) : ℝ) = SLTower.ee h := by
    push_cast
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
  rw [e]
  exact exists_thinTrees_of_tower Rt hC le_rfl hm1 hm hUu hM hX1 hX2 hA hN hℓ

end Cslib.Circuits.Arithmetic.Separation.Trees
