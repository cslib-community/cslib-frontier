/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.Iterate
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.Laws
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TwoCases.Basic
public import CslibFrontier.Foundations.GroupTheory.SLTower.Tower
public import Mathlib.RingTheory.FiniteType
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cutting.ComputationPieces
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Dealing.Generators
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Dealing.GroupTime
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Dealing.Instances
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Dealing.Numbers
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Dealing.ProgramSize
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.BaseChange
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Laws.Existence
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.Constants
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Uni.Automaton

/-!
# Cutting computations

Theorem J.3 of [AnthropicVPVNP2026] (one cut, p. 53): for a ring `A` with a finite table `θ` of
generators and laws at the vertices of the tower of `U_h` (Theorem G.2), there are `a₀`, `C` and
`v₀` such that for `v ≥ v₀`, `v ^ a₀ ≤ τ` with `4 lg τ ≤ (lg v) ^ 2`, `s ≤ τ` and `2 ≤ k ≤ v ^ 64`
a program of size at most `v ^ a₀` cuts `(τ, s)` into `(τ Λ / k, (s / k + τ / v ^ 256) Λ)` with at
most `k Λ` pieces in `(s + τ k / v ^ 256) Λ` steps, `Λ = (lg v) ^ C` (`Cutting.exists_oneCut`).
The program is the dealing program (`Dealing.Codes.dealProgram`) of the pieces of the computation
of the universal automaton (`Uni.exists_universal_automaton`, `Cutting.exists_computationPieces`)
on `K` blocks of `⌈τ Λ / K⌉` steps, with the evaluator GROUP (`Dealing.exists_evaluatesGroups`); the
numbers of the cut are those of `Dealing.CutNumbers`.

Theorem J.4 (cuts at all scales, p. 54) composes these cuts (`Cut.OneCutAt.exists_isCut`):
there are a multiple `H ≥ 272` of `16` and `C₀`, `v₀` such that for `v ≥ v₀` with
`(lg v) ^ (C₀ α) ≤ v`, `v ^ H ≤ τ ≤ v ^ (H α)` and `s v ^ 48 ≤ τ` some program of size at most
`v ^ H` cuts `(τ, s)` into `(v ^ H, v ^ (H - 32))` with at most `τ v ^ 2 / v ^ H` pieces in at most
`τ / v ^ 24` steps (`Cutting.exists_isCut_allScales`). In the contracting case this gives the
ring, its generators and the cut hypothesis of Appendix K (`Cutting.exists_cutHyp`).

## Main results

* `Cutting.exists_oneCut`: Theorem J.3.
* `Cutting.exists_isCut_allScales`: Theorem J.4.
* `Cutting.exists_cutHyp`: the ring, its generators and the cut hypothesis in the contracting
  case.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Definition J.1 (p. 52), Theorem J.3 (p. 53) and its proof (pp. 53–54), Theorem J.4 (pp. 54–55)
  and the beginning of Appendix K (p. 55: "we keep the ring `A` of Theorem G.2 and the constant `H`
  of Theorem J.4"); module `Paper.Cuts`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Cutting

open Finset Cut Interpreter Dealing GroupProgram TowerPlan

variable {A : Type} [CommRing A] {θ : List Bool → A}

/-- A finite type has an injective code by as many bits as it has elements. -/
private theorem exists_injective_code (α : Type) [Fintype α] :
    ∃ cb : α → BitString (Fintype.card α), Function.Injective cb :=
  ⟨fun z j => decide (Fintype.equivFin α z = j), fun z z' hz => (Fintype.equivFin α).injective
    (by simpa using congrFun hz (Fintype.equivFin α z'))⟩

/-- **One cut** (Theorem J.3 of [AnthropicVPVNP2026], p. 53). For a ring `A` with a table `θ` of
finite support in which every element is the value of a formula, and laws at the vertices of the
tower of `U_h` (Theorem G.2) whose contraction satisfies `1 + 8 C₁ ≤ h / 4`, there are `a₀`, `C`,
`v₀` such that for all `v ≥ v₀`, all `τ ≥ v ^ a₀` with `4 lg τ ≤ (lg v) ^ 2`, all `s ≤ τ` and all
`2 ≤ k ≤ v ^ 64`, with `Λ = (lg v) ^ C`, a program of size at most `v ^ a₀` cuts `(τ, s)` into
`(τ Λ / k, (s / k + τ / v ^ 256) Λ)` with at most `k Λ` pieces in `(s + τ k / v ^ 256) Λ` steps. -/
theorem exists_oneCut (hθ : (Function.support θ).Finite) (hgen : ∀ a, ∃ w : WE, w.val θ = a)
    {h : ℕ} [NeZero h] (h3 : 3 ≤ h) (FL : VertexLaws A (SLTower.tower h 0 (by omega)))
    (hgain : 1 + 8 * FL.contraction ≤ (h : ℝ) / 4) :
    ∃ a₀ C v₀ : ℕ, ∀ v, v₀ ≤ v → ∀ τ s k, v ^ a₀ ≤ τ → 4 * lg τ ≤ lg v ^ 2 → s ≤ τ → 2 ≤ k →
      k ≤ v ^ 64 → ∃ G : Tree, G.size ≤ v ^ a₀ ∧ IsCut θ τ s (τ * lg v ^ C / k)
        ((s / k + τ / v ^ 256) * lg v ^ C) (k * lg v ^ C) ((s + τ * k / v ^ 256) * lg v ^ C) G := by
  classical
  obtain ⟨S, Γ, Q, _, _, _, _, _, _, mu, i, e', bt, CU, -, hU⟩ :=
    Uni.exists_universal_automaton θ hθ
  obtain ⟨cb, hcb⟩ := exists_injective_code (Option Γ)
  obtain ⟨a, e, he, hP⟩ := exists_computationPieces h3 FL hgain
  obtain ⟨Cp, v₁, hP⟩ := hP A Γ S Q mu cb hcb Fintype.card_pos
  -- the evaluator GROUP, for the roles of the relay and the laws
  set laws := ((univ : Finset FL.Kind).toList.map FL.law).map fun L => L.map (algebraMap A A)
  obtain ⟨kinds, hkinds⟩ : ∃ kinds, kinds = lawRoles A laws := ⟨_, rfl⟩
  obtain ⟨ml, hml⟩ : ∃ ml, ml = ((relayLaw A :: laws).map fun L =>
      Fintype.card L.Role + Fintype.card L.Slot + Fintype.card L.Channel).sum := ⟨_, rfl⟩
  obtain ⟨GROUP, κ, hGR⟩ := exists_evaluatesGroups mu cb kinds (fun _ _ _ => hgen _)
    fun _ _ _ _ _ => hgen _
  -- the constants
  obtain ⟨b₁, hb₁⟩ : ∃ b, b = 2 * (Cp + e) + 5 := ⟨_, rfl⟩
  obtain ⟨C1, hC1⟩ : ∃ C, C = Cp + 10 := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = 20000 + Cp + Fintype.card (Option Γ) + Fintype.card S +
      Fintype.card Q + kinds.length + ml + κ + GROUP.code.size + dealBaseSize + 4 * (CU + 1) +
      3 * b₁ := ⟨_, rfl⟩
  obtain ⟨n1, hn1⟩ := poly_lg 1 C1
  refine ⟨a + e + 6 * b₁ + 400, 10 * C1, 2 ^ (Z + 1) + v₁ + n1,
    fun v hv τ s k hτ hlτ hsτ hk hkv => ?_⟩
  -- the logarithms
  have hZ2 : Z + 2 ≤ 2 ^ (Z + 1) := Nat.lt_two_pow_self
  obtain ⟨l, hl⟩ : ∃ l, l = lg v := ⟨_, rfl⟩
  have hlZ : Z + 2 ≤ l := hl ▸ le_lg_of_two_pow_le (by omega)
  obtain ⟨m, hm⟩ : ∃ m, m = l ^ C1 := ⟨_, rfl⟩
  have hlm {p : ℕ} (hp : p ≤ C1) : l ^ p ≤ m := hm ▸ Nat.pow_le_pow_right (by omega) hp
  have hmv : m ≤ v := by simpa [← hl, ← hm] using hn1 v (by omega)
  have vp {x y : ℕ} (hxy : x ≤ y) : v ^ x ≤ v ^ y := Nat.pow_le_pow_right (by omega) hxy
  -- the blocks
  obtain ⟨K, hKe, hKC, hP⟩ := hP v (by omega)
  have hK0 : 0 < K := (Nat.pow_pos (by omega)).trans_le hKe
  have hKv : K ≤ v ^ (e + 1) := hKC.trans ((Nat.mul_le_mul_right _ (by omega : Cp ≤ v)).trans
    (pow_succ' v e).symm.le)
  have hkK : k ≤ K := hkv.trans ((vp (by omega)).trans hKe)
  -- the steps: `K` blocks of `T` steps run the universal automaton
  obtain ⟨tU, htU⟩ : ∃ t, t = (CU + 1) * (2 * τ) * lg (2 * τ) ^ 2 := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T, T = tU / K + 1 := ⟨_, rfl⟩
  have hτ1 : 1 ≤ τ := (Nat.one_le_pow _ _ (by omega)).trans hτ
  have hKT : tU ≤ K * T := by
    rw [hT, Nat.mul_add, Nat.mul_one]
    exact (Nat.div_add_mod tU K).symm.le.trans (Nat.add_le_add_left (Nat.mod_lt tU hK0).le _)
  have hτtU : 2 * τ ≤ tU := by
    rw [htU]
    exact (Nat.le_mul_of_pos_left _ (Nat.succ_pos CU)).trans
      (Nat.le_mul_of_pos_right _ (Nat.pow_pos (Nat.succ_pos _)))
  have hKTm : K * T ≤ τ * m := by
    have hlg : lg (2 * τ) ≤ l ^ 2 := by
      have : Nat.log 2 (2 * τ) = Nat.log 2 τ + 1 := by
        rw [Nat.mul_comm, Nat.log_mul_base (by norm_num) (by omega)]
      rw [← hl] at hlτ
      simp only [lg] at hlτ ⊢
      omega
    have h1 : tU ≤ τ * l ^ 5 :=
      calc tU ≤ (CU + 1) * (2 * τ) * (l ^ 2) ^ 2 := by rw [htU]; gcongr
        _ = τ * (2 * (CU + 1) * l ^ 4) := by ring
        _ ≤ τ * (l * l ^ 4) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
        _ = τ * l ^ 5 := by ring
    have h2 : K ≤ τ := hKv.trans ((vp (by omega)).trans hτ)
    calc K * T = K * (tU / K) + K := by rw [hT]; ring
      _ ≤ τ * l ^ 5 + τ * l ^ 5 := Nat.add_le_add ((Nat.mul_div_le _ _).trans h1)
          (h2.trans (Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))))
      _ = τ * l ^ 5 * 2 := by ring
      _ ≤ τ * l ^ 5 * l := Nat.mul_le_mul_left _ (by omega)
      _ = τ * l ^ 6 := by ring
      _ ≤ τ * m := Nat.mul_le_mul_left _ (hlm (by omega))
  have hTa : v ^ a ≤ T := by
    refine Nat.le_of_mul_le_mul_left (?_ : v ^ (e + 1) * v ^ a ≤ v ^ (e + 1) * T)
      (Nat.pow_pos (by omega))
    rw [← pow_add]
    exact (vp (by omega)).trans (hτ.trans ((by omega : τ ≤ tU).trans (hKT.trans
      (Nat.mul_le_mul_right T hKv))))
  obtain ⟨pc⟩ := hP T k hTa hk hkv
  -- the parts of the input
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = s / K + 1 := ⟨_, rfl⟩
  have hℓT : ℓ ≤ T := by
    rw [hℓ, hT]
    exact Nat.add_le_add_right (Nat.div_le_div_right (by omega)) 1
  have hsK : s ≤ K * ℓ := by
    rw [hℓ, Nat.mul_add, Nat.mul_one]
    exact (Nat.div_add_mod s K).symm.le.trans (Nat.add_le_add_left (Nat.mod_lt s hK0).le _)
  -- the numbers below `X`
  obtain ⟨X, hX⟩ : ∃ X, X = v ^ b₁ := ⟨_, rfl⟩
  have hvX {p : ℕ} (hp : p ≤ b₁) : v ^ p ≤ X := hX ▸ vp hp
  have hv1 : v ≤ X := (pow_one v).ge.trans (hvX (by omega))
  have h3v (p : ℕ) : 3 * v ^ p ≤ v ^ (p + 1) := by
    rw [pow_succ, Nat.mul_comm 3]
    exact Nat.mul_le_mul_left _ (by omega)
  have h1v (p : ℕ) : 1 ≤ v ^ p := Nat.one_le_pow _ _ (by omega)
  have h2v (p : ℕ) {x y : ℕ} (hx : x ≤ v ^ p) (hy : y ≤ v ^ p) : x + y + 1 ≤ v ^ (p + 1) :=
    (Nat.add_le_add (Nat.add_le_add hx hy) (h1v p)).trans
      ((by ring : v ^ p + v ^ p + v ^ p = 3 * v ^ p).le.trans (h3v p))
  have hsmall {x : ℕ} (hx : x ≤ v ^ Cp) : x + 1 ≤ X :=
    (h2v Cp hx (Nat.zero_le _)).trans (hvX (by omega))
  have hKv2 : K + K + 1 ≤ v ^ (e + 1 + 1) := h2v (e + 1) hKv hKv
  have hKX : K + K + 1 ≤ X := hKv2.trans (hvX (by omega))
  have hKK : (K + K) * (K + K) ≤ v ^ (2 * (e + 1 + 1)) := by
    rw [two_mul, pow_add]
    exact Nat.mul_le_mul (by omega) (by omega)
  have hcard : Fintype.card (UnitId (K + K) pc.load pc.moves.Channel pc.U1) + 1 ≤ X := by
    rw [UnitId.card_eq]
    have h1 : (K + K) * (K + K) * pc.load ≤ v ^ (2 * (Cp + e) + 4) :=
      (Nat.mul_le_mul hKK pc.load_le).trans (by rw [← pow_add]; exact vp (by omega))
    have h2 : Fintype.card pc.moves.Channel * pc.U1 ≤ v ^ (2 * (Cp + e) + 4) :=
      (Nat.mul_le_mul pc.card_channel_le pc.U1_le).trans (by rw [← pow_add]; exact vp (by omega))
    exact (h2v _ h1 h2).trans (hvX (by omega))
  -- the roles
  have hlawmem (x : Fin pc.E) : pc.moves.law x ∈ relayLaw A :: laws := by
    cases hx : pc.isLaw x
    · exact pc.law_eq_relay x hx ▸ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (pc.law_mem x hx)
  have hml' (x : Fin pc.E) : Fintype.card (pc.moves.law x).Role +
      Fintype.card (pc.moves.law x).Slot + Fintype.card (pc.moves.law x).Channel ≤ ml :=
    hml ▸ List.le_sum_of_mem (List.mem_map_of_mem (hlawmem x))
  have hkind (r : pc.moves.Role) :
      ∃ t, kinds[t]? = some (⟨pc.moves.law r.1, r.2⟩ : Σ L : Law A, L.Role) :=
    List.mem_iff_getElem?.1 (hkinds ▸ (mk_mem_lawRoles _).2 (List.mem_cons.1 (hlawmem r.1)))
  choose tg htg using hkind
  have htg' (r : pc.moves.Role) : tg r < kinds.length := (List.getElem?_eq_some_iff.1 (htg r)).1
  have hDX : pc.D ≤ X := (Nat.le_succ _).trans (hsmall pc.D_le)
  -- the codes, of `Lc` bits
  obtain ⟨Lc, hLc⟩ : ∃ L, L = lg (X ^ 3) + lg τ + l := ⟨_, rfl⟩
  have hX3 : X ^ 3 < 2 ^ Lc :=
    (lt_two_pow_lg _).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hTL : T < 2 ^ Lc :=
    calc T ≤ K * T := Nat.le_mul_of_pos_left _ hK0
      _ ≤ τ * v := hKTm.trans (Nat.mul_le_mul_left _ hmv)
      _ < 2 ^ lg τ * 2 ^ l := hl ▸ Nat.mul_lt_mul'' (lt_two_pow_lg τ) (lt_two_pow_lg v)
      _ ≤ 2 ^ Lc := by rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hLcm : Lc < m := by
    have h1 : lg (X ^ 3) ≤ 3 * b₁ * l := by
      rw [hX, ← pow_mul, hl, Nat.mul_comm b₁ 3]
      exact lg_pow_le (by omega)
    have h2 : 4 * lg τ ≤ l * l := by rw [← sq, hl]; exact hlτ
    have h3 := Nat.mul_le_mul_right l (show 3 * b₁ + 1 ≤ l by omega)
    rw [Nat.add_mul, one_mul] at h3
    have h4 := Nat.mul_le_mul_left (l * l) (show 3 ≤ l by omega)
    have h5 : l ^ 3 = l * l * l := by ring
    have h6 := hlm (show 3 ≤ C1 by omega)
    have h7 : 1 ≤ l * l := Nat.mul_pos (by omega) (by omega)
    omega
  have hXX : X ≤ X * X := Nat.le_mul_of_pos_left X (by omega)
  have hX30 : 30 * (X * X) ≤ X ^ 3 := by
    have hcube : X ^ 3 = X * (X * X) := by ring
    exact hcube ▸ Nat.mul_le_mul_right _ (by omega)
  have hS : Fintype.card (Option S) ≤ X := by rw [Fintype.card_option]; omega
  have hRow : Fintype.card (RowData (K + K)) + 1 ≤ X := by
    rw [RowData.card_eq, two_mul]
    exact (h2v _ hKK hKK).trans (hvX (by omega))
  have hE := hsmall pc.moves_le
  have hN := hsmall pc.card_channel_le
  have hpS := hsmall pc.steps_le
  have hA' := hsmall pc.parties_le
  have hl' := hsmall pc.load_le
  obtain ⟨C, hC⟩ := Codes.exists_lengthBounds (S := S) (M := pc.moves) (U0 := pc.load)
    (U1 := pc.U1) (D := pc.D) (pS := pc.steps) (Lc := Lc) (by
      rw [Name.card_eq]
      have := Nat.mul_le_mul (show K + K ≤ X by omega) (show K + K ≤ X by omega)
      have := Nat.mul_le_mul hS (show K + K ≤ X by omega)
      omega) (by omega) (by omega) (by
      rw [Fintype.card_sum, Fintype.card_congr (Cell.equivProd _ _ _), Fintype.card_prod,
        Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin]
      have := Nat.mul_le_mul (show K + K + pc.A' ≤ X by omega) (show Fintype.card (UnitId
        (K + K) pc.load pc.moves.Channel pc.U1) ≤ X by omega)
      have := Nat.mul_le_mul (show K + K ≤ X by omega) (show pc.load ≤ X by omega)
      omega)
  have hroles : Fintype.card pc.moves.Role ≤ X :=
    calc Fintype.card pc.moves.Role = ∑ x, Fintype.card (pc.moves.law x).Role := Fintype.card_sigma
      _ ≤ ∑ _x : Fin pc.E, ml := sum_le_sum fun x _ => by have := hml' x; omega
      _ = pc.E * ml := by simp
      _ ≤ v ^ Cp * v := Nat.mul_le_mul pc.moves_le (by omega)
      _ = v ^ (Cp + 1) := (pow_succ _ _).symm
      _ ≤ X := hvX (by omega)
  have H : C.SizeBounds (fun z => (Fintype.equivFin Q z : ℕ)) tg X Lc :=
    ⟨by omega, hC.name, hC.digit, hC.rowData, hC.key, hC.dkey, by omega, by omega, hl',
      by have := hsmall pc.U1_le; omega, hE, hDX, by omega, by omega, by omega, hS, by omega,
      by omega, hroles, fun r => (Fintype.card_subtype_le _).trans (by have := hml' r.1; omega),
      fun r => (Fintype.card_subtype_le _).trans (by have := hml' r.1; omega),
      fun q => (Fin.isLt _).le.trans (by omega), fun r => by have := htg' r; omega⟩
  -- the numbers of the cut
  have hLm : lg v ^ Cp ≤ m := hl ▸ hlm (by omega)
  obtain ⟨ιb, hιb⟩ : ∃ x, x = Cp * K / k := ⟨_, rfl⟩
  obtain ⟨bd, hbd⟩ : ∃ x, x = K * T * lg v ^ Cp / (pc.ub * v ^ 300) := ⟨_, rfl⟩
  obtain ⟨ev, hev⟩ : ∃ x, x = K * T * lg v ^ Cp / (pc.ub * k) := ⟨_, rfl⟩
  have hbits (d : ℕ) : K * T * lg v ^ Cp / (pc.ub * d) * (pc.ub * d) ≤ τ * m ^ 2 :=
    (Nat.div_mul_le_self _ _).trans ((Nat.mul_le_mul hKTm hLm).trans_eq (by ring))
  have hm2 : l * l ≤ m := (sq l).symm.le.trans (hlm (by omega))
  have hl4 : 4 * l ≤ l * l := Nat.mul_le_mul_right l (by omega)
  have hιbX : ιb ≤ X := by
    rw [hιb]
    refine (Nat.div_le_self _ _).trans ((Nat.mul_le_mul (show Cp ≤ v by omega)
      (show K ≤ v ^ (e + 1 + 1) by omega)).trans ?_)
    rw [← pow_succ']
    exact hvX (by omega)
  have hsmallτ : X ^ 6 * m ^ 20 * v ^ 300 ≤ τ :=
    calc X ^ 6 * m ^ 20 * v ^ 300 ≤ X ^ 6 * v ^ 20 * v ^ 300 :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hmv 20))
      _ = v ^ (b₁ * 6 + 20 + 300) := by rw [hX, ← pow_mul, ← pow_add, ← pow_add]
      _ ≤ τ := (vp (by omega)).trans hτ
  have hN : CutNumbers v K τ s k T ℓ pc.ub pc.load X Lc m (Fintype.card (Option Γ)) ιb bd ev
      pc.num :=
    ⟨by omega, hmv, by omega, hkK, hKTm, hℓ, pc.ub_pos, pc.ub_le.trans (Nat.le_succ _),
      (pc.load_mul_ub_le.trans (Nat.mul_le_mul_left T hLm)).trans_eq (Nat.mul_comm _ _), hLcm,
      by omega, by omega,
      hιb ▸ (Nat.div_mul_le_self _ _).trans (Nat.mul_le_mul_right K (by omega)), hιbX,
      by rw [hbd, Nat.mul_assoc]; exact hbits _, by rw [hev, Nat.mul_assoc]; exact hbits _,
      pc.num_le.trans (Nat.mul_le_mul_left k hLm), pc.num_le_D.trans hDX, hsmallτ⟩
  -- the binary numbers of the steps of a block, the bits of a unit and the letters of a part
  obtain ⟨wT, hwT, hwT'⟩ := exists_word hTL
  obtain ⟨wub, hwub, hwub'⟩ := exists_word (pc.ub_le.trans_lt hTL)
  obtain ⟨wl, hwl, hwl'⟩ := exists_word (hℓT.trans_lt hTL)
  have hval (z : Tree) (hz : z.size ≤ s) : Tape.runVal mu i e' (K * T)
      (fun _ => (tbits z).map bt) = _ :=
    (pc.value i e' (fun _ => (tbits z).map bt) ℓ hℓT
      (by rw [List.length_map, length_tbits]; exact hz.trans hsK)).trans
    (sum_congr rfl fun q _ => ite_congr rfl (fun _ => sum_congr rfl fun ρ _ => ite_congr rfl
      (fun _ => sum_congr rfl fun n _ => if_congr (pc.valid_iff n).symm rfl rfl) fun _ => rfl)
      fun _ => rfl)
  have hbase (n o) (hn : pc.program.Valid n) (hg : ∀ x, pc.plan.Good n o x) (g) :
      #{p : Fin (K + K) | pc.piece ⟨n, o⟩ (Fin.castAdd pc.A' p) = g} ≤ ιb := by
    rw [hιb, Nat.le_div_iff_mul_le (by omega)]
    exact pc.card_base_le n o hn hg g
  have hv300 : 0 < pc.ub * v ^ 300 := Nat.mul_pos pc.ub_pos (pow_pos (by omega) 300)
  have hbd' (n o) (hn : pc.program.Valid n) (hg : ∀ x, pc.plan.Good n o x) (g) :
      #((pc.plan.cur n o pc.E).filter
        (OneIn (UnitId.holder pc.moves.channelParty) (pc.piece ⟨n, o⟩) g)) ≤ bd := by
    rw [hbd, Nat.le_div_iff_mul_le hv300, ← Nat.mul_assoc]
    exact pc.card_oneIn_le n o hn hg g
  have hcut := (isCut_dealProgram_of_evaluatesGroups (C := C) (θ := θ) (κ := κ) (bt := bt)
    (hD := pc.one_lt_D) (hmm := pc.num_le_D) (hU0 := pc.load_lt_D) (hU1 := pc.U1_le_D)
    (τ := τ) (s := s) (bd := bd) (ιb := ιb) pc.program hK0 H hC.injective hGR (fun r => htg r) pc.ok
    ((KT.val_eq_binaryValue_reverse wT).symm.trans hwT')
    ((KT.val_eq_binaryValue_reverse wub).symm.trans hwub') pc.ub_pos hwl' hwub' hℓT
    (by simp [hwT]) (by simp [hwub]) hwl.le hwub.le
    (fun z hz hpl => hU τ z (K * T) hpl (le_trans (by
      rw [htU]
      exact Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega))
        (Nat.pow_le_pow_left (lg_mono (by omega)) 2)) hKT)) hval
    hbd' hbase
    (fun n o hn hg y => (pc.program.fn_countGate y ⟨n, o⟩).symm.le.trans
      ((Fin.isLt _).le.trans hDX)) (by omega)
    fun q x ρ n o g b hx hn ho => groupTime_le_of_sizeBounds H
      ((KT.val_eq_binaryValue_reverse wT).symm.trans hwT')
      ((KT.val_eq_binaryValue_reverse wub).symm.trans hwub') (by simp [hwT]) (by simp [hwub])
      pc.ok hx (hbase n o hn ho g)
      hN.ιb_le_X (fun p _ => (pc.valid_iff n).1 hn p)
      (hev ▸ (Nat.le_div_iff_mul_le (Nat.mul_pos pc.ub_pos (by omega))).2
        (by rw [← Nat.mul_assoc]; exact pc.count_le n o hn ho g)) b).mono
    (hN.time_le (by omega)) hN.size_le
    (hN.mm_le.trans (Nat.mul_le_mul_left k (Nat.le_self_pow (by norm_num : 10 ≠ 0) m)))
    hN.dealTime_le
  refine ⟨_, ?_, by rwa [show lg v ^ (10 * C1) = m ^ 10 by rw [← hl, hm, ← pow_mul,
    Nat.mul_comm]]⟩
  refine (size_dealProgram_le pc.program H (pc.num_le_D.trans hDX) (by omega) hwl.le hwub.le
    (by simp [hwT]) (by simp [hwub]) pc.num_le_D (by omega) cb bt i e' pc.load_lt_D
    pc.U1_le_D).trans ?_
  calc (dealBaseSize + 3000) * (X * Lc) ^ 4 ≤ v * (X * v) ^ 4 :=
        Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (Nat.mul_le_mul_left X (by omega)) 4)
    _ = v ^ ((b₁ + 1) * 4 + 1) := by rw [hX, ← pow_succ, ← pow_mul, ← pow_succ']
    _ ≤ v ^ (a + e + 6 * b₁ + 400) := vp (by omega)

/-- **Cuts at all scales** (Theorem J.4 of [AnthropicVPVNP2026], pp. 54–55). For a ring `A` with a
table `θ` of generators as in `exists_oneCut` and laws at the vertices of the tower of `U_h` with
`1 + 8 C₁ ≤ h / 4`, there are a multiple `H ≥ 272` of `16` and `C₀`, `v₀` such that whenever
`v ≥ v₀` and `(lg v) ^ (C₀ α) ≤ v`, for all `τ`, `s` with `v ^ H ≤ τ ≤ v ^ (H α)` and
`s v ^ 48 ≤ τ` some program of size at most `v ^ H` cuts `(τ, s)` into `(v ^ H, v ^ (H - 32))`
with at most `τ v ^ 2 / v ^ H` pieces in at most `τ / v ^ 24` steps. -/
theorem exists_isCut_allScales (hθ : (Function.support θ).Finite)
    (hgen : ∀ a, ∃ w : WE, w.val θ = a) {h : ℕ} [NeZero h] (h3 : 3 ≤ h)
    (FL : VertexLaws A (SLTower.tower h 0 (by omega)))
    (hgain : 1 + 8 * FL.contraction ≤ (h : ℝ) / 4) :
    ∃ H C₀ v₀ : ℕ, 272 ≤ H ∧ 16 ∣ H ∧ ∀ v, v₀ ≤ v → ∀ α τ s, lg v ^ (C₀ * α) ≤ v →
      v ^ H ≤ τ → τ ≤ v ^ (H * α) → s * v ^ 48 ≤ τ → ∃ G : Tree, G.size ≤ v ^ H ∧
        IsCut θ τ s (v ^ H) (v ^ (H - 32)) (τ * v ^ 2 / v ^ H) (τ / v ^ 24) G := by
  obtain ⟨a₀, C, v₀, hcut⟩ := exists_oneCut hθ hgen h3 FL hgain
  refine ⟨16 * (a₀ + 217), (3 * C + 4) * (32 * (a₀ + 217) + 2), v₀ + 2 ^ 100, by omega,
    dvd_mul_right 16 _, fun v hv α τ s hlog hτ hτα hs => ?_⟩
  have hl : 100 ≤ lg v := (Nat.le_succ _).trans (le_lg_of_two_pow_le (by omega))
  have hα : 1 ≤ α := Nat.one_le_iff_ne_zero.2 fun h0 => by
    rw [h0, Nat.mul_zero, pow_zero] at hτα
    have := Nat.le_self_pow (show 16 * (a₀ + 217) ≠ 0 by omega) v
    omega
  have hαl : 4 * (16 * (a₀ + 217) * α) ≤ lg v := by
    refine le_trans ?_ (le_lg_of_lg_pow_le (by omega) hlog)
    rw [show 4 * (16 * (a₀ + 217) * α) = (64 * (a₀ + 217)) * α by ring]
    exact Nat.mul_le_mul_right α ((show 64 * (a₀ + 217) ≤ 4 * (32 * (a₀ + 217) + 2) by omega).trans
      (Nat.mul_le_mul_right _ (by omega)))
  have hone : OneCutAt θ v a₀ (16 * (a₀ + 217) * α) (lg v ^ (C + 1)) :=
    OneCutAt.mono (fun τ' s' k h1 h2 h3 h4 h5 => hcut v (by omega) τ' s' k h1 (by
      calc 4 * lg τ' ≤ 4 * (16 * (a₀ + 217) * α * lg v) := Nat.mul_le_mul_left 4
            ((lg_mono h2).trans (lg_pow_le (Nat.mul_pos (by omega) hα)))
        _ = 4 * (16 * (a₀ + 217) * α) * lg v := by ring
        _ ≤ lg v ^ 2 := (Nat.mul_le_mul_right _ hαl).trans (sq (lg v)).symm.le) h3 h4 h5)
      (Nat.pow_le_pow_right (by omega) (Nat.le_succ C))
  have hΛ : 1 ≤ lg v ^ (C + 1) := Nat.one_le_pow _ _ (by omega)
  exact hone.exists_isCut (by omega) ((lg_ge_two (by omega)).trans (Nat.le_self_pow (by omega) _))
    ((Nat.pow_le_pow_left (Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_right hΛ
      (by norm_num))) _).trans (polylog_loss_le hl hα hlog)) (by omega) (by omega) hτ hτα hs

/-- **The cut hypothesis in the contracting case** (Appendix K of [AnthropicVPVNP2026], p. 55: "we
keep the ring `A` of Theorem G.2 and the constant `H` of Theorem J.4"): in the contracting case
there are a finitely generated subring `A` of the field, a table `θ` of finite support in which
every element of `A` is the value of a formula, and `h ≥ 17`, `C₀`, `v₀` such that the cut
hypothesis `CutHyp θ (16 h) C₀ v₀` (Theorem J.4) holds. -/
theorem exists_cutHyp {K : Type} [Field K] (hK : TwoCases.ContractingCase K) :
    ∃ (A : Subring K) (_ : Algebra.FiniteType ℤ A) (θ : List Bool → A) (h C₀ v₀ : ℕ),
      (Function.support θ).Finite ∧ (∀ a, ∃ w : WE, w.val θ = a) ∧ 17 ≤ h ∧
        CutHyp θ (16 * h) C₀ v₀ := by
  obtain ⟨h', _, h3, A, hA, FL, hgain, -⟩ := Laws.exists_vertexLaws hK
  obtain ⟨θ, hθ, hgen⟩ := WE.exists_table A
  obtain ⟨H, C₀, v₀, hH, ⟨h, rfl⟩, hcut⟩ := exists_isCut_allScales hθ hgen h3 FL hgain
  refine ⟨A, hA, θ, h, C₀, v₀, hθ, hgen, by omega, fun v hv α hl τ s h1 h2 h4 => ?_⟩
  obtain ⟨G, hsize, hG⟩ := hcut v hv α τ s hl h1 h2 h4
  exact ⟨G, hG.cutProg hsize (Nat.div_mul_le_self _ _) (Nat.div_mul_le_self _ _)⟩

end Cslib.Circuits.Arithmetic.Separation.Cutting
