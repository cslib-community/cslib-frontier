/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.Plan
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.StageBounds
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.Norms
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.Rules
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.StartLoads
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# The tower plan: the capacity of the moves, and the units of the tree

The loads of the edges of the tower plan of [AnthropicVPVNP2026] (proof of Theorem H.2; modules
`Nc.Tow.Cap` and `Nc.Tow.CapOk`) are at most twice `normBound` when `ρ ≤ 1`, and the number of
units at a vertex at most `3 b normBound + 1`. So every move uses at most `moveCap` units, and the
plan obeys the rules with that bound (`towerPlan_ok_moveCap`). For `ρ < 1` the units between the
chambers and their parents add up to at most `treeUnitBound`, those of one chamber are at most
`edgeUnitBound`, and the gain of the tower bounds a power of `edgeUnitBound`.

## Main definitions

* `moveCap`: the bound for the numbers of units of the moves.
* `treeUnitBound`, `edgeUnitBound`: the bounds for the units of the tree, in all and for one
  chamber.

## Main results

* `towerPlan_ok_moveCap`: the tower plan obeys the rules with the bound `moveCap`.
* `sum_parentUnits_le`, `parentUnits_le`: the units of the tree.
* `edgeUnitBound_pow_le`: the gain of the tower.
* `normBound_le`: the bound for the norms, for routes of length at most `m`.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Theorem H.2(b), p. 46, and its proof ("Bounds", p. 47, and (d), (e), p. 48); modules
  `Nc.Tow.Cap`, `Nc.Tow.CapOk`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.TowerPlan

open Finset Cslib.CoveringTower Cut

variable {F : Type*} [CommSemiring F] {h b D J r m Uu A A' U0 U1 : ℕ} {T : Tower h b D J r}
  {R : Routes T m Uu} {ch : Fin A ↪ T.X 0} {FL : VertexLaws F T} {Pl : Placement T ch A'}
  {lhat : ℕ} {n : Fin A → Fin A → ℕ} {o : MoveChannel R ch FL → ℕ} {ρ : ℝ}

variable (FL) in
/-- The bound for the number of units of a move. -/
@[expose] noncomputable def moveCap (U0 Uu A lhat : ℕ) : ℕ :=
  U0 + 2 + ⌈3 * (b : ℝ) * normBound FL Uu A lhat⌉₊

private theorem kap_le_normBound (hρ : StageRate FL ρ) (hρ1 : ρ ≤ 1) {j : ℕ} (hj : j ≤ J) :
    T.kap (edgeLoads (load lhat n o) j) ≤ normBound FL Uu A lhat :=
  (kap_edgeLoads_le hρ hj).trans
    (mul_le_of_le_one_left normBound_nonneg (pow_le_one₀ hρ.ρ_pos.le hρ1))

/-- An edge carries at most twice the bound for the norms. -/
private theorem load_edge_le (hρ : StageRate FL ρ) (hρ1 : ρ ≤ 1) (j : Fin (J + 1))
    (e : T.Ed j) : (load lhat n o (.edge j e) : ℝ) ≤ 2 * normBound FL Uu A lhat := by
  have hk := kap_le_normBound (lhat := lhat) (n := n) (o := o) (Uu := Uu) (A := A) hρ hρ1
    (Nat.le_of_lt_succ j.2)
  have hrX : (1 : ℝ) ≤ r * Fintype.card (T.X j) := by
    exact_mod_cast Nat.mul_pos hρ.r_pos (Fintype.card_pos_iff.2 ⟨T.e0 e⟩)
  have h1 : (load lhat n o (.edge j e) : ℝ) ^ 2 ≤
      ∑ e', (edgeLoads (load lhat n o) j e' : ℝ) ^ 2 := by
    rw [← edgeLoads_of_lt (load lhat n o) j.2 e]
    exact single_le_sum (f := fun e' => (edgeLoads (load lhat n o) j e' : ℝ) ^ 2)
      (fun _ _ => sq_nonneg _) (mem_univ e)
  have h3 := sum_nonneg fun e' (_ : e' ∈ univ) => sq_nonneg (edgeLoads (load lhat n o) j e' : ℝ)
  have hk0 := normBound_nonneg (FL := FL) (Uu := Uu) (A := A) (lhat := lhat)
  refine (pow_le_pow_iff_left₀ (Nat.cast_nonneg _) (by positivity) two_ne_zero).1 ?_
  nlinarith [Tower.kap_sq (edgeLoads (load lhat n o) j), pow_le_pow_left₀ (Tower.kap_nonneg _) hk 2,
    mul_le_mul_of_nonneg_right hrX h3]

/-- The number of units at a vertex is at most `3 b` times the bound for the norms, plus one. -/
private theorem minUnits_le (hρ : StageRate FL ρ) (hρ1 : ρ ≤ 1) (l : VertexMove FL) :
    (l.minUnits (load lhat n o) : ℝ) ≤ 3 * b * normBound FL Uu A lhat + 1 := by
  obtain ⟨j, i, ω, d⟩ := l
  set nf : T.Ed j → ℕ := fun e => load lhat n o (.edge j.castSucc e)
  have hk : T.kap nf ≤ normBound FL Uu A lhat :=
    (show nf = edgeLoads (load lhat n o) j from
      funext fun e => (edgeLoads_of_lt (load lhat n o) (Nat.lt_succ_of_lt j.2) e).symm) ▸
        kap_le_normBound hρ hρ1 j.2.le
  have hb : (1 : ℝ) ≤ b := by exact_mod_cast hρ.b_pos
  have ha : (1 : ℝ) ≤ FL.scale := by exact_mod_cast FL.scale_pos
  have hX : (1 : ℝ) ≤ Fintype.card (T.X (j + 1)) := by
    rw [← T.card_V (Nat.succ_le_of_lt j.2) i]
    exact_mod_cast Nat.mul_pos (Fintype.card_pos_iff.2 ⟨ω⟩) hρ.b_pos
  have h1 : (FL.scale : ℝ) * (⟨j, i, ω, d⟩ : VertexMove FL).minUnits (load lhat n o) ≤
      √(T.NN2 (T.nEnd i nf ω)) + FL.scale :=
    VertexMove.scale_mul_minUnits_le _ _ fun q => load_segment_le j i ω q
  have h3 : √(T.NN2 (T.nEnd i nf ω)) ^ 2 ≤ ∑ ω', √(T.NN2 (T.nEnd i nf ω')) ^ 2 :=
    single_le_sum (f := fun ω' => √(T.NN2 (T.nEnd i nf ω')) ^ 2) (fun _ _ => sq_nonneg _)
      (mem_univ ω)
  have h4 : (r : ℝ) * Fintype.card (T.X j) / 2 * ∑ e ∈ univ.filter (T.ty · = i), (nf e : ℝ) ^ 2 ≤
      T.kap nf ^ 2 := by
    rw [Tower.kap_sq]
    gcongr
    exact subset_univ _
  have h5 : √(T.NN2 (T.nEnd i nf ω)) ^ 2 ≤ 8 * b * T.kap nf ^ 2 := by
    have h6 := (mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤
      Fintype.card (T.X (j + 1)) / b)).trans
        ((T.end_norm j.2 hρ.b_pos hρ.b_le (i := i) (n := nf)).trans
          (mul_le_mul_of_nonneg_left h4 (by norm_num)))
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at h6
    nlinarith [sq_nonneg (√(T.NN2 (T.nEnd i nf ω)))]
  have hk0 := Tower.kap_nonneg nf
  have h7 : √(T.NN2 (T.nEnd i nf ω)) ≤ 3 * b * T.kap nf :=
    (pow_le_pow_iff_left₀ (Real.sqrt_nonneg _) (by positivity) two_ne_zero).1 (by nlinarith)
  refine le_of_mul_le_mul_left ?_ (by positivity : (0 : ℝ) < FL.scale)
  have hk0' := normBound_nonneg (FL := FL) (Uu := Uu) (A := A) (lhat := lhat)
  nlinarith [mul_le_mul_of_nonneg_left hk (by positivity : (0 : ℝ) ≤ 3 * b),
    mul_le_mul_of_nonneg_right ha (by positivity : (0 : ℝ) ≤ 3 * b * normBound FL Uu A lhat)]

/-- Every move uses at most `moveCap` units, if no two base parties share more than `U0` initial
units. -/
private theorem moveCount_le_moveCap (hρ : StageRate FL ρ) (hρ1 : ρ ≤ 1)
    (hn : ∀ a c, n a c ≤ U0) (mv : Move R ch FL) :
    moveCount lhat n o mv ≤ moveCap FL U0 Uu A lhat := by
  have hk := normBound_nonneg (FL := FL) (Uu := Uu) (A := A) (lhat := lhat)
  have hceil := Nat.le_ceil (3 * (b : ℝ) * normBound FL Uu A lhat)
  have hb : (1 : ℝ) ≤ b := by exact_mod_cast hρ.b_pos
  have hedge (j : Fin (J + 1)) (e : T.Ed j) :
      load lhat n o (.edge j e) ≤ ⌈3 * (b : ℝ) * normBound FL Uu A lhat⌉₊ := by
    have := load_edge_le (lhat := lhat) (n := n) (o := o) (Uu := Uu) (A := A) hρ hρ1 j e
    exact_mod_cast this.trans ((by nlinarith : 2 * normBound FL Uu A lhat ≤
      3 * b * normBound FL Uu A lhat).trans hceil)
  unfold moveCap
  rcases mv with ⟨⟨a, c, γ, s⟩ | ⟨j, i, e⟩ | ⟨j, e, s⟩ | e, hx⟩ | l
  · have := moveCount_start_le (lhat := lhat) (n := n) (o := o) hx
    have := batchSize_le (ch := ch) (lhat := lhat) (n := n) a c γ
    have := (Nat.div_le_self (n a c) (Fintype.card (T.X 0))).trans (hn a c)
    omega
  · have := (moveCount_relay_le _ hx).trans (hedge j.castSucc e)
    omega
  · have := (moveCount_middle_le (lhat := lhat) (n := n) (o := o) hx).trans
      (by split_ifs; exacts [hedge j.castSucc e, Nat.zero_le _])
    omega
  · have := (moveCount_relay_le _ hx).trans (hedge (Fin.last J) e)
    omega
  · have h1 := moveCount_vertex_le (lhat := lhat) (n := n) (o := o) l
    have h2 := minUnits_le (lhat := lhat) (n := n) (o := o) (Uu := Uu) (A := A) hρ hρ1 l
    have h3 : (l.minUnits (load lhat n o) : ℝ) <
        (⌈3 * (b : ℝ) * normBound FL Uu A lhat⌉₊ + 2 : ℕ) := by push_cast; linarith
    have := Nat.cast_lt.1 h3
    omega

/-- **The tower plan obeys the rules** ([AnthropicVPVNP2026], proof of Theorem H.2, pp. 46–48),
with the bound `moveCap` for the numbers of units of its moves; the rate `ρ ≤ 1` bounds the norms
of the loads at all stages by `normBound`. -/
theorem towerPlan_ok_moveCap (hρ : StageRate FL ρ) (hρ1 : ρ ≤ 1) :
    (towerPlan R FL Pl lhat U0 U1).Ok (moveCap FL U0 Uu A lhat) :=
  towerPlan_ok hρ.r_pos hρ.b_pos fun n _ mv =>
    moveCount_le_moveCap hρ hρ1 (fun a c => Nat.le_of_lt_succ (n a c).2) mv

/-! ### The units of the tree -/

variable (FL) in
/-- The bound for all units between nodes and their parents. -/
@[expose] noncomputable def treeUnitBound (Uu A lhat : ℕ) (ρ : ℝ) : ℕ :=
  ⌈2 * √h * normBound FL Uu A lhat / (1 - ρ)⌉₊

/-- **All units of the tree** ([AnthropicVPVNP2026], Theorem H.2(b), p. 46, and its proof,
"Bounds", p. 47): the units between the chambers and their parents add up to at most
`treeUnitBound`. -/
theorem sum_parentUnits_le (hρ : StageRate FL ρ) (hρ1 : ρ < 1) :
    ∑ j ∈ range (J + 1), ∑ c, T.parentUnits (edgeLoads (load lhat n o)) j c ≤
      treeUnitBound FL Uu A lhat ρ := by
  have hk := normBound_nonneg (FL := FL) (Uu := Uu) (A := A) (lhat := lhat)
  refine Nat.cast_le.1 (le_trans ?_ (Nat.le_ceil _))
  rw [Nat.cast_sum]
  calc ∑ j ∈ range (J + 1), ((∑ c, T.parentUnits (edgeLoads (load lhat n o)) j c : ℕ) : ℝ) ≤
      ∑ j ∈ range (J + 1), 2 * √h * normBound FL Uu A lhat * ρ ^ j :=
        sum_le_sum fun j hj => (sum_incidentSum_edgeLoads_le hρ
          (Nat.le_of_lt_succ (mem_range.1 hj))).trans_eq (by ring)
    _ ≤ 2 * √h * normBound FL Uu A lhat * (ρ ^ 0 / (1 - ρ)) := by
        rw [← mul_sum, range_eq_Ico]
        gcongr
        exact geom_sum_Ico_le_of_lt_one hρ.ρ_pos.le hρ1
    _ = _ := by rw [pow_zero, mul_one_div]

variable (FL) in
/-- The bound for the units between a node and its parent, as a natural number. -/
@[expose] noncomputable def edgeUnitBound (Uu A lhat : ℕ) (ρ : ℝ) : ℕ :=
  ⌊edgeBound FL Uu A lhat ρ⌋₊

/-- **The units between a chamber and its parent** ([AnthropicVPVNP2026], Theorem H.2(b), p. 46,
and its proof, "Bounds", p. 47). -/
theorem parentUnits_le (hρ : StageRate FL ρ) {j : ℕ} (hj : j ≤ J) (c : T.X j) :
    T.parentUnits (edgeLoads (load lhat n o)) j c ≤ edgeUnitBound FL Uu A lhat ρ :=
  Nat.le_floor (incidentSum_le_edgeBound hρ hj c)

/-- **The gain of the tower** ([AnthropicVPVNP2026], Theorem H.2, proof, "Bounds", p. 47): if
`ρ ^ q D ^ p ≤ 1` with `2 p ≤ q`, the bound for the units between a node and its parent is at
most `(2 h) * normBound / |X 0| ^ (p / q)`, in the form of `q`-th powers. -/
theorem edgeUnitBound_pow_le (hD : 0 < D) (hρ : 0 ≤ ρ) (hh : 0 < h)
    (hX : 0 < Fintype.card (T.X J)) {p q : ℕ} (hpq : 2 * p ≤ q) (hgain : ρ ^ q * (D : ℝ) ^ p ≤ 1) :
    (edgeUnitBound FL Uu A lhat ρ : ℝ) ^ q * (Fintype.card (T.X 0) : ℝ) ^ p ≤
      (2 * (h : ℝ)) ^ q * normBound FL Uu A lhat ^ q := by
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have h2h : (1 : ℝ) ≤ 2 * h := by exact_mod_cast (by omega : 1 ≤ 2 * h)
  have hk := normBound_nonneg (FL := FL) (Uu := Uu) (A := A) (lhat := lhat)
  have hDJ : (D : ℝ) ^ J ≤ Fintype.card (T.X 0) := by
    rw [show (Fintype.card (T.X 0) : ℝ) = D ^ J * Fintype.card (T.X J) by
      exact_mod_cast T.card_X_zero le_rfl]
    exact le_mul_of_one_le_right (by positivity) (by exact_mod_cast hX)
  set x : ℝ := (Fintype.card (T.X 0) : ℝ)
  have hx : 0 < x := (one_le_pow₀ hD1).trans_lt' one_pos |>.trans_le hDJ
  set M := max 1 (√D * ρ) with hMdef
  have hM : (M ^ 2) ^ q ≤ (D : ℝ) ^ (q - 2 * p) := by
    rcases le_total (√D * ρ) 1 with hle | hle
    · rw [hMdef, max_eq_left hle, one_pow, one_pow]
      exact one_le_pow₀ hD1
    · rw [hMdef, max_eq_right hle, mul_pow, Real.sq_sqrt (zero_le_one.trans hD1)]
      calc ((D : ℝ) * ρ ^ 2) ^ q = (D : ℝ) ^ (q - 2 * p) * (ρ ^ q * (D : ℝ) ^ p) ^ 2 := by
            rw [mul_pow, ← pow_mul, mul_pow, ← pow_mul, ← pow_mul, mul_comm q 2]
            nth_rewrite 1 [← Nat.sub_add_cancel hpq]
            ring
        _ ≤ (D : ℝ) ^ (q - 2 * p) * 1 := by
          gcongr
          exact pow_le_one₀ (by positivity) hgain
        _ = _ := mul_one _
  have hb : 0 ≤ edgeBound FL Uu A lhat ρ := by unfold edgeBound; positivity
  have key : (edgeBound FL Uu A lhat ρ ^ q * x ^ p) ^ 2 ≤
      ((2 * (h : ℝ)) ^ q * normBound FL Uu A lhat ^ q) ^ 2 := by
    have ha : √(2 * h / x) ^ 2 = 2 * h / x := Real.sq_sqrt (by positivity)
    have hxq : x ^ (q - 2 * p) * (x ^ p) ^ 2 = x ^ q := by
      rw [← pow_mul, ← pow_add, mul_comm p 2, Nat.sub_add_cancel hpq]
    calc (edgeBound FL Uu A lhat ρ ^ q * x ^ p) ^ 2 =
        (2 * h / x) ^ q * ((M ^ 2) ^ q) ^ J * (normBound FL Uu A lhat ^ q) ^ 2 * (x ^ p) ^ 2 := by
          rw [edgeBound, ← hMdef, show (2 * h / x) ^ q = (√(2 * h / x) ^ 2) ^ q by rw [ha]]
          ring
      _ ≤ (2 * h / x) ^ q * ((D : ℝ) ^ J) ^ (q - 2 * p) * (normBound FL Uu A lhat ^ q) ^ 2 *
          (x ^ p) ^ 2 := by
          gcongr
          exact (pow_le_pow_left₀ (by positivity) hM J).trans_eq (by rw [← pow_mul, ← pow_mul,
            mul_comm])
      _ ≤ (2 * h / x) ^ q * x ^ (q - 2 * p) * (normBound FL Uu A lhat ^ q) ^ 2 * (x ^ p) ^ 2 := by
          gcongr
      _ = (2 * (h : ℝ)) ^ q * (normBound FL Uu A lhat ^ q) ^ 2 := by
          rw [mul_right_comm _ _ ((x ^ p) ^ 2), mul_assoc _ (x ^ (q - 2 * p)), hxq, div_pow,
            div_mul_cancel₀ _ (by positivity)]
      _ ≤ ((2 * (h : ℝ)) ^ q) ^ 2 * (normBound FL Uu A lhat ^ q) ^ 2 := by
          gcongr
          exact le_self_pow₀ (one_le_pow₀ h2h) two_ne_zero
      _ = _ := by ring
  refine le_trans ?_ ((pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 key)
  gcongr
  exact Nat.floor_le hb

/-- The bound for the norms, for routes of length at most `m` that use every edge at most
`2 |X 0| m` times and at most `|X 0|` base parties. -/
theorem normBound_le (hm : 1 ≤ m) (hUu : Uu ≤ 2 * Fintype.card (T.X 0) * m)
    (hA : A ≤ Fintype.card (T.X 0)) (hX : 0 < Fintype.card (T.X 0)) (hb : 0 < b) :
    normBound FL Uu A lhat ≤ (√h * r + √FL.contraction * FL.scale) *
      (m * Fintype.card (T.X 0) * (lhat + 2 * (Fintype.card (T.X 0) : ℝ) ^ 2)) := by
  set X := Fintype.card (T.X 0)
  have hn : startBound T Uu A lhat ≤ 2 * m * (lhat + 2 * X ^ 2) := calc
    Uu * (lhat / X + 2 * A) ≤ 2 * X * m * (lhat / X + 2 * X) := by gcongr
    _ = 2 * m * (X * (lhat / X) + 2 * X ^ 2) := by ring
    _ ≤ _ := by gcongr; exact Nat.mul_div_le lhat X
  have hnR : (startBound T Uu A lhat : ℝ) ≤ 2 * m * (lhat + 2 * (X : ℝ) ^ 2) := by
    exact_mod_cast hn
  have h1 : (1 : ℝ) ≤ m * (lhat + 2 * (X : ℝ) ^ 2) := by
    nlinarith [(mod_cast hX : (1 : ℝ) ≤ X), (mod_cast hm : (1 : ℝ) ≤ m),
      (lhat.cast_nonneg : (0 : ℝ) ≤ lhat)]
  have p1 : √h * (r * X / 2) * startBound T Uu A lhat ≤
      √h * (r * X / 2) * (2 * m * (lhat + 2 * (X : ℝ) ^ 2)) := by gcongr
  have p2 : √FL.contraction * FL.scale / b * X ≤
      √FL.contraction * FL.scale * X * (m * (lhat + 2 * (X : ℝ) ^ 2)) := calc
    _ ≤ √FL.contraction * FL.scale * X * 1 := by
        rw [mul_one]
        gcongr
        exact div_le_self (by positivity) (by exact_mod_cast hb)
    _ ≤ _ := by gcongr
  unfold normBound
  nlinarith [Real.sqrt_nonneg FL.contraction, p1, p2]

end Cslib.Circuits.Arithmetic.Separation.TowerPlan
