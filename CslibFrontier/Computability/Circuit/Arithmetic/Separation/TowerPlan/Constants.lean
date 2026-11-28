/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.Accel
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.Capacity
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.Cardinalities

/-!
# The tower plan: the conditions on a tower and its laws, and the numbers that follow

The proof of Theorem H.2 of [AnthropicVPVNP2026] (module `Nc.Tow.Cst`) uses towers of all sizes
whose shape stays bounded, and absorbs the bounded factors in its constant. `TowerConstants`
states this with one constant `c`: it adds to the conditions `StageRate` of the stages the rate
`ρ < 1`, the gain `ρ ^ q D ^ p ≤ 1` with `2 p ≤ q`, a near pair at every place, a list `laws` that
contains the laws at the vertices, and bounds by `c` for the numbers of types, places, edges of a
type at a chamber, near pairs, pairs of places, kinds and slots of laws and chambers of the last
level, for the lengths of the strings of the laws, for the factor of the norms and for
`1 / (1 - ρ)`.

Under these conditions the bounds of the tower plan are at most natural numbers in `c`, the length
`m` of the routes and the number `X` of chambers of the level `0`: `constNormBound` for the norms,
`constMoveCap` for the units of a move, and in terms of `constNormBound` the units of the tree and
the units between a chamber and its parent. The depth of the tower is logarithmic, with
`J + 1 ≤ (c + 1) lg M` if `X ≤ c M`, and the sizes are bounded as `SizeBound` needs. The list
`lawRoles` has the roles of the relay and of the laws.

## Main definitions

* `TowerConstants`: the conditions on a tower and its laws, with one constant.
* `constNormBound`, `constMoveCap`: the bounds for the norms and for the units of a move by the
  constant.
* `lawRoles`: the roles of the relay and of a list of laws, specified by `mk_mem_lawRoles`.

## Main results

* `TowerConstants.two_lt_ratio`, `TowerConstants.one_le`: the ratio of the numbers of chambers
  is more than `2`, and the constant is positive.
* `TowerConstants.succ_depth_le`: the depth of the tower is logarithmic.
* `TowerConstants.moveCap_le_constMoveCap`, `TowerConstants.treeUnitBound_le`,
  `TowerConstants.edgeUnitBound_pow_mul_le`: the bounds of the tower plan by the constant.
* `TowerConstants.sizeBound`: the sizes are bounded.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Theorem H.2, pp. 45–46, and its proof (p. 46; "Bounds", p. 47; "For (d)", p. 48); module
  `Nc.Tow.Cst`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.TowerPlan

open Finset Cslib.CoveringTower Cut Interpreter

variable {F : Type*} [CommSemiring F] {h b D J r m Uu A c p q lhat : ℕ} {T : Tower h b D J r}
  {FL : VertexLaws F T} {laws : List (Law F)} {ρ : ℝ}

/-- The conditions on a tower, its laws at the vertices `FL`, a list `laws` of laws and a rate `ρ`,
with one constant `c` for the sizes: the conditions `StageRate` of the stages, the rate `ρ < 1`,
the gain `ρ ^ q D ^ p ≤ 1` with `2 p ≤ q`, a near pair at every place, the laws at the vertices
among `laws`, and the bounds by `c`. -/
structure TowerConstants (FL : VertexLaws F T) (laws : List (Law F)) (c : ℕ) (ρ : ℝ)
    (p q : ℕ) : Prop extends StageRate FL ρ where
  /-- The rate is less than `1`. -/
  rate_lt_one : ρ < 1
  /-- Every place at a vertex is an end of a near pair. -/
  exists_nearPair : ∀ f : T.Fl, ∃ ν, T.cN ν = f ∨ T.dN ν = f
  /-- The exponents of the gain. -/
  two_mul_le : 2 * p ≤ q
  /-- The gain: `q` stages of the rate `ρ` outweigh `p` levels of the ratio `D`. -/
  rate_pow_mul_le_one : ρ ^ q * (D : ℝ) ^ p ≤ 1
  /-- The laws at the vertices are among `laws`. -/
  law_mem : ∀ d, FL.law d ∈ laws
  /-- The number of types. -/
  types_le : h ≤ c
  /-- The number of places at a vertex. -/
  places_le : b ≤ c
  /-- The number of edges of a type at a chamber. -/
  degree_le : r ≤ c
  /-- The number of near pairs. -/
  card_nearPair_le : Fintype.card T.Nr ≤ c
  /-- The bound for the squares of the lengths of the strings of the laws at the vertices. -/
  lengthBound_le : FL.lengthBound ≤ c
  /-- The number of kinds of laws at the vertices. -/
  card_kind_le : Fintype.card FL.Kind ≤ c
  /-- The number of pairs of places. -/
  card_pair_le : Fintype.card (Sym2 T.Fl) ≤ c
  /-- The numbers of slots of the laws at the vertices. -/
  card_slot_le : ∀ d, Fintype.card (FL.law d).Slot ≤ c
  /-- The number of chambers of the last level. -/
  card_X_last_le : Fintype.card (T.X J) ≤ c
  /-- The last level has a chamber. -/
  card_X_last_pos : 0 < Fintype.card (T.X J)
  /-- The factor of the norms in `normBound_le`. -/
  normFactor_le : √h * r + √FL.contraction * FL.scale ≤ c
  /-- The sum `1 / (1 - ρ)` of the geometric series of the rates `ρ ^ j` of the stages. -/
  inv_one_sub_le : 1 / (1 - ρ) ≤ c
  /-- The strings of the laws have length at most `c`. -/
  lengthLE : ∀ L ∈ laws, L.LengthLE c
  /-- The labels of the laws have length at most `c`. -/
  labelLength_le : ∀ L ∈ laws, L.labelLength ≤ c

/-- The bound `c m X (lhat + 2 X ^ 2)` for the norms, by the constant `c`, the length `m` of the
routes and the number `X` of chambers of the level `0`. -/
@[expose] def constNormBound (c m X lhat : ℕ) : ℕ := c * (m * X * (lhat + 2 * X ^ 2))

/-- The bound `U0 + 2 + 3 c constNormBound` for the units of a move, by the constant `c`. -/
@[expose] def constMoveCap (c m X lhat U0 : ℕ) : ℕ := U0 + 2 + 3 * c * constNormBound c m X lhat

/-- The number of binary digits of `K` bounds the exponent of a power of two below `c K`. -/
private theorem succ_le_mul_lg {J c K : ℕ} (hJ : 2 ^ J ≤ c * K) : J + 1 ≤ (c + 1) * lg K := by
  have h1 : c * K < 2 ^ (c + lg K) :=
    (pow_add 2 c (lg K)).symm ▸ Nat.mul_lt_mul'' Nat.lt_two_pow_self
      (Nat.lt_pow_succ_log_self one_lt_two K)
  have h2 := (Nat.pow_lt_pow_iff_right (by norm_num)).1 (hJ.trans_lt h1)
  have h3 : c ≤ c * lg K := Nat.le_mul_of_pos_right c (Nat.succ_pos _)
  rw [add_one_mul]
  omega

namespace TowerConstants

variable (hC : TowerConstants FL laws c ρ p q)
include hC

/-- The ratio of the numbers of chambers of two consecutive levels is more than `2`, since
`2 ≤ ρ D` with `ρ < 1`. -/
theorem two_lt_ratio : 2 < D := by
  have h1 := hC.two_le
  have h2 := hC.rate_lt_one
  have h3 := hC.ρ_pos
  by_contra hD
  have : (D : ℝ) ≤ 2 := by exact_mod_cast not_lt.1 hD
  nlinarith

/-- The constant is positive. -/
theorem one_le : 1 ≤ c := hC.h_pos.trans_le hC.types_le

private theorem card_X_zero_pos : 0 < Fintype.card (T.X 0) :=
  (Nat.pow_pos (by have := hC.two_lt_ratio; omega)).trans_le
    (T.pow_le_card_X_zero hC.card_X_last_pos)

/-- **The depth of the tower is logarithmic** ([AnthropicVPVNP2026], Theorem H.2, proof, "Bounds",
p. 47, `J = O(log M)`): if the level `0` has at most `c M` chambers, then `J + 1 ≤ (c + 1) lg M`. -/
theorem succ_depth_le {M : ℕ} (hM : Fintype.card (T.X 0) ≤ c * M) : J + 1 ≤ (c + 1) * lg M :=
  succ_le_mul_lg ((Nat.pow_le_pow_left hC.two_lt_ratio.le J).trans
    ((T.pow_le_card_X_zero hC.card_X_last_pos).trans hM))

/-- **The sizes are bounded**: with the length `m` of the routes, the number `J` of stages, the
number `A` of base parties and the chambers of the level `0` at most `V ≥ c`, the tower, its
routes and its laws satisfy `SizeBound`. -/
theorem sizeBound {V : ℕ} (hcV : c ≤ V) (hm : m ≤ V) (hJ : J ≤ V) (hA : A ≤ V)
    (hX : Fintype.card (T.X 0) ≤ V) : SizeBound FL m A V where
  one_le := hC.one_le.trans hcV
  types_le := hC.types_le.trans hcV
  places_le := hC.places_le.trans hcV
  degree_le := hC.degree_le.trans hcV
  length_le := hm
  stages_le := hJ
  base_le := hA
  card_X_zero_le := hX
  card_kind_le := hC.card_kind_le.trans hcV
  card_slot_le d := (hC.card_slot_le d).trans hcV

/-! ### The bounds of the tower plan by the constant

For routes of length at most `m ≥ 1` that use every edge at most `2 |X 0| m` times, and at most
`|X 0|` base parties. -/

variable (hm : 1 ≤ m) (hUu : Uu ≤ 2 * Fintype.card (T.X 0) * m) (hA : A ≤ Fintype.card (T.X 0))
include hm hUu hA

private theorem normBound_le_constNormBound :
    normBound FL Uu A lhat ≤ constNormBound c m (Fintype.card (T.X 0)) lhat := by
  refine (normBound_le hm hUu hA hC.card_X_zero_pos hC.b_pos).trans ?_
  rw [constNormBound]
  push_cast
  exact mul_le_mul_of_nonneg_right hC.normFactor_le (by positivity)

/-- **The units of a move** ([AnthropicVPVNP2026], Theorem H.2, proof, "For (d)", p. 48): the
bound `moveCap` is at most `constMoveCap`. -/
theorem moveCap_le_constMoveCap {U0 : ℕ} :
    moveCap FL U0 Uu A lhat ≤ constMoveCap c m (Fintype.card (T.X 0)) lhat U0 := by
  have hk := hC.normBound_le_constNormBound hm hUu hA (lhat := lhat)
  have hb : (b : ℝ) ≤ c := by exact_mod_cast hC.places_le
  refine Nat.add_le_add_left (Nat.ceil_le.2 ?_) _
  push_cast
  exact mul_le_mul (by gcongr) hk normBound_nonneg (by positivity)

/-- **All units of the tree** ([AnthropicVPVNP2026], Theorem H.2(b), p. 46, and its proof,
"Bounds", p. 47): the bound `treeUnitBound` is at most `2 c constNormBound c`. -/
theorem treeUnitBound_le :
    treeUnitBound FL Uu A lhat ρ ≤ 2 * c * constNormBound c m (Fintype.card (T.X 0)) lhat * c := by
  have hk := hC.normBound_le_constNormBound hm hUu hA (lhat := lhat)
  have hr : (1 : ℝ) ≤ r := by exact_mod_cast hC.r_pos
  have hs : √(h : ℝ) ≤ c := (le_mul_of_one_le_right (Real.sqrt_nonneg _) hr).trans
    ((le_add_of_nonneg_right (by positivity)).trans hC.normFactor_le)
  have hρ : 0 < 1 - ρ := sub_pos.2 hC.rate_lt_one
  refine Nat.ceil_le.2 ?_
  push_cast
  rw [div_eq_mul_one_div]
  exact mul_le_mul (mul_le_mul (by gcongr) hk normBound_nonneg (by positivity))
    hC.inv_one_sub_le (by positivity) (by positivity)

/-- **The units between a chamber and its parent** ([AnthropicVPVNP2026], Theorem H.2(b), p. 46,
and its proof, "Bounds", p. 47): by the gain, `edgeUnitBound ^ q |X 0| ^ p` is at most
`(2 c constNormBound) ^ q`. -/
theorem edgeUnitBound_pow_mul_le :
    edgeUnitBound FL Uu A lhat ρ ^ q * Fintype.card (T.X 0) ^ p ≤
      (2 * c * constNormBound c m (Fintype.card (T.X 0)) lhat) ^ q := by
  have hk := hC.normBound_le_constNormBound hm hUu hA (lhat := lhat)
  have hh : (h : ℝ) ≤ c := by exact_mod_cast hC.types_le
  have h1 := edgeUnitBound_pow_le (FL := FL) (Uu := Uu) (A := A) (lhat := lhat)
    (by have := hC.two_lt_ratio; omega) hC.ρ_pos.le hC.h_pos hC.card_X_last_pos hC.two_mul_le
    hC.rate_pow_mul_le_one
  have h2 : (2 * (h : ℝ)) ^ q * normBound FL Uu A lhat ^ q ≤
      ((2 * c * constNormBound c m (Fintype.card (T.X 0)) lhat : ℕ) : ℝ) ^ q := by
    have := normBound_nonneg (FL := FL) (Uu := Uu) (A := A) (lhat := lhat)
    push_cast
    rw [mul_pow (2 * (c : ℝ))]
    gcongr
  exact_mod_cast h1.trans h2

end TowerConstants

/-! ### The roles of the relay and of the laws -/

variable (F) in
/-- The roles of the relay and of the laws `laws`, each with its law: the kinds of roles of the
moves of a tower plan whose laws at the vertices are among `laws`. -/
noncomputable def lawRoles (laws : List (Law F)) : List (Σ L : Law F, L.Role) :=
  (relayLaw F :: laws).flatMap fun L => (univ : Finset L.Role).toList.map (Sigma.mk L)

/-- A law with one of its roles is in `lawRoles` if and only if the law is the relay or one of
`laws`. -/
@[simp] theorem mk_mem_lawRoles {L : Law F} (x : L.Role) :
    (⟨L, x⟩ : Σ L : Law F, L.Role) ∈ lawRoles F laws ↔ L = relayLaw F ∨ L ∈ laws := by
  simp only [lawRoles, List.mem_flatMap, List.mem_map, mem_toList, mem_univ, true_and,
    Sigma.mk.injEq, ← List.mem_cons]
  exact ⟨fun ⟨_, ha, _, he, _⟩ => he ▸ ha, fun h => ⟨L, h, x, rfl, HEq.rfl⟩⟩

end Cslib.Circuits.Arithmetic.Separation.TowerPlan
