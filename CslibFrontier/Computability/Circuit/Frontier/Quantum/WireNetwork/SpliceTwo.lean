/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
-- `import all`: reads private `ActiveGate`, `placeAct` from `ActiveSplit` and private
-- `capGraph`, `OpenState`, `activeGate_wires_ne`, `placeAct_two_mul_apply` from `OpenState`.
import all CslibFrontier.Computability.Circuit.Frontier.Quantum.WireNetwork.ActiveSplit
import all CslibFrontier.Computability.Circuit.Frontier.Quantum.WireNetwork.OpenState
import CslibFrontier.Computability.Circuit.Frontier.Layouts.Basic
import CslibFrontier.Computability.Circuit.Quantum.PhaseGates
import CslibFrontier.Foundations.Data.Set.Card
import Mathlib.Data.Fintype.Sum

/-!
# Two-qubit gadget splicing for degree-3 and degree-4 wire networks

Internal 2-wire multigraph gadget splice (`OpenState.spliceTwo`) and its degree-`4` (`U(4)`) and
degree-`3` (`HasBondRankTwo`) specializations (`openStateTwoDegFour`, `openStateTwoDegThree`).
-/

-- This proof-only companion is intentionally private; sibling WireNetwork modules use import all.
set_option linter.privateModule false

namespace Cslib.Circuits.Frontier

open Set Matrix
open scoped Finset Kronecker

attribute [local instance] OpenState.instFV OpenState.instDV OpenState.instFE OpenState.instDE

private def spliceTwoGraph {V E V_add E_int W : Type} (G : Multigraph V E) (tip : W → V)
    (q₀ q₁ : W) (G_int : Multigraph V_add E_int) (v₀ v₁ : V_add) :
    Multigraph (V ⊕ V_add) (E ⊕ (Bool ⊕ E_int)) where
  src
    | .inl e₀ => .inl (G.src e₀)
    | .inr (.inl false) => .inl (tip q₀)
    | .inr (.inl true) => .inl (tip q₁)
    | .inr (.inr e_int) => .inr (G_int.src e_int)
  tgt
    | .inl e₀ => .inl (G.tgt e₀)
    | .inr (.inl false) => .inr v₀
    | .inr (.inl true) => .inr v₁
    | .inr (.inr e_int) => .inr (G_int.tgt e_int)

private def spliceTwoTip {V V_add W : Type} [DecidableEq W] (tip : W → V)
    (q₀ q₁ : W) (v₀ v₁ : V_add) (q : W) : V ⊕ V_add :=
  if q = q₀ then .inr v₀ else if q = q₁ then .inr v₁ else .inl (tip q)

private def spliceTwoOldEdge {E E_int W : Type} [DecidableEq W] (q₀ q₁ : W) :
    E ⊕ W ↪ (E ⊕ (Bool ⊕ E_int)) ⊕ W where
  toFun
    | .inl e₀ => .inl (.inl e₀)
    | .inr q =>
      if q = q₀ then .inl (.inr (.inl false))
      else if q = q₁ then .inl (.inr (.inl true))
      else .inr q
  inj' a b hab := by
    cases a with
    | inl ea =>
      cases b with
      | inl eb => exact congrArg Sum.inl (Sum.inl.inj (Sum.inl.inj hab))
      | inr qb => dsimp only at hab; split_ifs at hab <;> cases hab
    | inr qa =>
      cases b with
      | inl eb => dsimp only at hab; split_ifs at hab <;> cases hab
      | inr qb => dsimp only at hab; split_ifs at hab <;> simp_all

private theorem spliceTwoOldEdge_inr {E E_int W : Type} [DecidableEq W] (q₀ q₁ : W) (q : W) :
    spliceTwoOldEdge (E := E) (E_int := E_int) q₀ q₁ (.inr q) =
      if q = q₀ then .inl (.inr (.inl false))
      else if q = q₁ then .inl (.inr (.inl true))
      else .inr q := rfl

private theorem ncard_incidence_spliceTwo_inr {V E V_add E_int W : Type} [DecidableEq W]
    [DecidableEq V_add] [Finite E_int] (G : Multigraph V E) (tip : W → V) {q₀ q₁ : W}
    (hq_ne : q₀ ≠ q₁) (G_int : Multigraph V_add E_int) (v₀ v₁ v : V_add) :
    ((capGraph (spliceTwoGraph G tip q₀ q₁ G_int v₀ v₁)
        (spliceTwoTip tip q₀ q₁ v₀ v₁)).incidenceSet (.inl (.inr v))).ncard =
      (if v = v₀ then 2 else 0) + (if v = v₁ then 2 else 0) + (G_int.incidenceSet v).ncard := by
  let S₀ : Set ((E ⊕ (Bool ⊕ E_int)) ⊕ W) :=
    if v = v₀ then {.inl (.inr (.inl false)), .inr q₀} else ∅
  let S₁ : Set ((E ⊕ (Bool ⊕ E_int)) ⊕ W) :=
    if v = v₁ then {.inl (.inr (.inl true)), .inr q₁} else ∅
  let S_int : Set ((E ⊕ (Bool ⊕ E_int)) ⊕ W) :=
    (fun e => .inl (.inr (.inr e))) '' G_int.incidenceSet v
  have hpart : (capGraph (spliceTwoGraph G tip q₀ q₁ G_int v₀ v₁)
        (spliceTwoTip tip q₀ q₁ v₀ v₁)).incidenceSet (.inl (.inr v)) =
      S₀ ∪ (S₁ ∪ S_int) := by
    ext ((e₀ | (b | e_int)) | q)
    · simp [Multigraph.mem_incidenceSet, capGraph, spliceTwoGraph, S₀, S₁, S_int]
    · cases b <;>
        simp [Multigraph.mem_incidenceSet, capGraph, spliceTwoGraph, S₀, S₁, S_int, eq_comm]
    · simp [Multigraph.mem_incidenceSet, capGraph, spliceTwoGraph, S₀, S₁, S_int]
    · by_cases hq0 : q = q₀
      · subst hq0
        have hnot1 : (.inr q : (E ⊕ (Bool ⊕ E_int)) ⊕ W) ∉ S₁ := by
          dsimp only [S₁]; split_ifs
          · simp [hq_ne]
          · simp
        simp [Multigraph.mem_incidenceSet, capGraph, spliceTwoTip, S₀, S_int, hnot1, eq_comm]
      · by_cases hq1 : q = q₁
        · subst hq1
          have hnot0 : (.inr q : (E ⊕ (Bool ⊕ E_int)) ⊕ W) ∉ S₀ := by
            dsimp only [S₀]; split_ifs
            · simp [hq0]
            · simp
          simp only [Multigraph.mem_incidenceSet, capGraph, spliceTwoTip, hq0, ↓reduceIte]
          simp [S₁, S_int, hnot0, eq_comm]
        · simp [Multigraph.mem_incidenceSet, capGraph, spliceTwoTip, S₀, S₁, S_int, hq0, hq1]
  have hfin₀ : S₀.Finite := by dsimp only [S₀]; split_ifs <;> simp
  have hfin₁ : S₁.Finite := by dsimp only [S₁]; split_ifs <;> simp
  have hfin_int : S_int.Finite := (toFinite _).image _
  have hd₀ : Disjoint S₀ (S₁ ∪ S_int) := by
    rw [Set.disjoint_left]
    intro x hx0 hx12
    dsimp only [S₀] at hx0
    split_ifs at hx0
    · rcases hx0 with rfl | rfl
      · rcases hx12 with hx1 | ⟨_, _, h⟩
        · dsimp only [S₁] at hx1; split_ifs at hx1 <;> simp at hx1
        · cases h
      · rcases hx12 with hx1 | ⟨_, _, h⟩
        · dsimp only [S₁] at hx1
          split_ifs at hx1
          · simp [hq_ne] at hx1
          · exact hx1
        · cases h
    · exact hx0
  have hd₁ : Disjoint S₁ S_int := by
    rw [Set.disjoint_left]
    rintro x hx1 ⟨_, _, rfl⟩
    dsimp only [S₁] at hx1
    split_ifs at hx1 <;> simp at hx1
  have hc₀ : S₀.ncard = if v = v₀ then 2 else 0 := by
    dsimp only [S₀]; split_ifs
    · rw [ncard_insert_of_notMem (by simp), ncard_singleton]
    · exact ncard_empty _
  have hc₁ : S₁.ncard = if v = v₁ then 2 else 0 := by
    dsimp only [S₁]; split_ifs
    · rw [ncard_insert_of_notMem (by simp), ncard_singleton]
    · exact ncard_empty _
  have hc_int : S_int.ncard = (G_int.incidenceSet v).ncard :=
    ncard_image_of_injective _ fun _ _ h => Sum.inr.inj (Sum.inr.inj (Sum.inl.inj h))
  rw [hpart, ncard_union_eq hd₀ hfin₀ (hfin₁.union hfin_int),
    ncard_union_eq hd₁ hfin₁ hfin_int, hc₀, hc₁, hc_int, add_assoc]

/-- Shared 2-wire gadget splice constructor for `OpenState d W`: attaches a finite gadget
`(V_add, E_int, G_int, v₀, v₁, T_add)` onto active wires `q₀ = g.2.2 0` and `q₁ = g.2.2 1`. -/
private noncomputable def OpenState.spliceTwo {d : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    {M : Matrix (W → Bool) (W → Bool) ℂ} {s : ℕ} (S : OpenState d W M s)
    (g : ActiveGate W) (h2 : g.1.val = 2)
    (V_add E_int : Type) [Fintype V_add] [DecidableEq V_add] [Fintype E_int] [DecidableEq E_int]
    (G_int : Multigraph V_add E_int) (hloop_int : G_int.Loopless) (v₀ v₁ : V_add)
    (hcard_add : (d - 2) * Fintype.card V_add = 2)
    (hdeg_add : ∀ v : V_add,
      (if v = v₀ then 2 else 0) + (if v = v₁ then 2 else 0) + (G_int.incidenceSet v).ncard = d)
    (T_add : V_add → Bool → Bool → Bool → Bool → (E_int → Bool) → ℂ)
    (hT_contract : ∀ b₀ b₁ a₀ a₁ : Bool,
      (∑ β : E_int → Bool, ∏ v : V_add, T_add v b₀ b₁ a₀ a₁ β) =
        ∑ z₀ : Bool, ∑ z₁ : Bool,
          (g.2.1 : Matrix (Fin g.1.val → Bool) (Fin g.1.val → Bool) ℂ)
            (fun i => if i = (⟨0, by omega⟩ : Fin g.1.val) then a₀ else a₁)
            (fun i => if i = (⟨0, by omega⟩ : Fin g.1.val) then z₀ else z₁) *
          S.tipMat (g.2.2 ⟨0, by omega⟩) z₀ b₀ * S.tipMat (g.2.2 ⟨1, by omega⟩) z₁ b₁)
    (hT_loc : ∀ (v : V_add) (b₀ b₀' b₁ b₁' a₀ a₀' a₁ a₁' : Bool) (β β' : E_int → Bool),
      (v = v₀ → b₀ = b₀' ∧ a₀ = a₀') →
      (v = v₁ → b₁ = b₁' ∧ a₁ = a₁') →
      Set.EqOn β β' (G_int.incidenceSet v) →
      T_add v b₀ b₁ a₀ a₁ β = T_add v b₀' b₁' a₀' a₁' β') :
    OpenState d W ((placeAct g : Matrix _ _ ℂ) * M) (s + 1) :=
  let i₀ : Fin g.1.val := ⟨0, by omega⟩
  let i₁ : Fin g.1.val := ⟨1, by omega⟩
  let q₀ : W := g.2.2 i₀
  let q₁ : W := g.2.2 i₁
  have hq_ne : q₀ ≠ q₁ := activeGate_wires_ne g h2
  let G' := spliceTwoGraph S.G S.tip q₀ q₁ G_int v₀ v₁
  let tip' := spliceTwoTip S.tip q₀ q₁ v₀ v₁
  let oldEdge : S.E ⊕ W ↪ (S.E ⊕ (Bool ⊕ E_int)) ⊕ W := spliceTwoOldEdge q₀ q₁
  have hmap_u (u : S.V) (e : S.E ⊕ W) :
      e ∈ (capGraph S.G S.tip).incidenceSet (.inl u) ↔
        oldEdge e ∈ (capGraph G' tip').incidenceSet (.inl (.inl u)) := by
    cases e with
    | inl e₀ =>
      change _ ↔ (.inl (.inl e₀) : (S.E ⊕ (Bool ⊕ E_int)) ⊕ W) ∈ _
      simp [Multigraph.mem_incidenceSet, capGraph, G', spliceTwoGraph]
    | inr q =>
      by_cases hq0 : q = q₀
      · subst hq0
        simp [Multigraph.mem_incidenceSet, capGraph, oldEdge, spliceTwoOldEdge_inr, G',
          spliceTwoGraph]
      · by_cases hq1 : q = q₁
        · subst hq1
          simp [Multigraph.mem_incidenceSet, capGraph, oldEdge, spliceTwoOldEdge_inr, hq0, G',
            spliceTwoGraph]
        · simp [Multigraph.mem_incidenceSet, capGraph, oldEdge, spliceTwoOldEdge_inr, hq0, hq1,
            tip', spliceTwoTip]
  have hsurj_u (u : S.V) (e' : (S.E ⊕ (Bool ⊕ E_int)) ⊕ W)
      (he' : e' ∈ (capGraph G' tip').incidenceSet (.inl (.inl u))) :
      ∃ e, oldEdge e = e' := by
    rcases e' with (e₀ | (b | e_int)) | q
    · exact ⟨.inl e₀, rfl⟩
    · cases b
      · exact ⟨.inr q₀, by simp [oldEdge, spliceTwoOldEdge_inr]⟩
      · exact ⟨.inr q₁, by simp [oldEdge, spliceTwoOldEdge_inr, hq_ne.symm]⟩
    · simp [Multigraph.mem_incidenceSet, capGraph, G', spliceTwoGraph] at he'
    · by_cases hq0 : q = q₀
      · subst hq0; simp [Multigraph.mem_incidenceSet, capGraph, tip', spliceTwoTip] at he'
      · by_cases hq1 : q = q₁
        · subst hq1; simp [Multigraph.mem_incidenceSet, capGraph, tip', spliceTwoTip, hq0] at he'
        · exact ⟨.inr q, by simp [oldEdge, spliceTwoOldEdge_inr, hq0, hq1]⟩
  { V := S.V ⊕ V_add
    E := S.E ⊕ (Bool ⊕ E_int)
    instFV := inferInstance
    instDV := inferInstance
    instFE := inferInstance
    instDE := inferInstance
    G := G'
    inVert := S.inVert.trans ⟨Sum.inl, Sum.inl_injective⟩
    tip := tip'
    scalar := S.scalar
    tipMat := fun q => if q = q₀ ∨ q = q₁ then 1 else S.tipMat q
    openF := fun v x γ' => match v with
      | .inl u => S.openF u x (γ' ∘ oldEdge)
      | .inr v =>
        T_add v (γ' (.inl (.inr (.inl false)))) (γ' (.inl (.inr (.inl true))))
          (γ' (.inr q₀)) (γ' (.inr q₁)) (fun e_int => γ' (.inl (.inr (.inr e_int))))
    loopless := by
      rintro (e₀ | (b | e_int))
      · exact fun h => S.loopless e₀ (Sum.inl.inj h)
      · cases b <;> exact Sum.inl_ne_inr
      · exact fun h => hloop_int e_int (Sum.inr.inj h)
    deg_inVert := fun q =>
      (ncard_incidence_eq_of_bij S.G S.tip G' tip' Sum.inl oldEdge (S.inVert q)
        (hmap_u _) (hsurj_u _)).trans (S.deg_inVert q)
    deg_gate := by
      rintro (u | v) hv
      · have hu : u ∉ Set.range S.inVert := fun ⟨q, hq⟩ => hv ⟨q, congrArg Sum.inl hq⟩
        exact (ncard_incidence_eq_of_bij S.G S.tip G' tip' Sum.inl oldEdge u
          (hmap_u u) (hsurj_u u)).trans (S.deg_gate u hu)
      · exact (ncard_incidence_spliceTwo_inr S.G S.tip hq_ne G_int v₀ v₁ v).trans (hdeg_add v)
    reach_tip := fun q => by
      have hprev : G'.toSimpleGraph.Reachable (.inl (S.inVert q)) (.inl (S.tip q)) :=
        reachable_map_inl ⟨Sum.inl, Sum.inl_injective⟩
          (fun e₀ => ⟨.inl e₀, by simp [Multigraph.ends, G', spliceTwoGraph]⟩) (S.reach_tip q)
      by_cases hq0 : q = q₀
      · subst hq0; simp only [tip', spliceTwoTip, ↓reduceIte]
        exact hprev.trans (G'.reachable_src_tgt (.inr (.inl false)))
      · by_cases hq1 : q = q₁
        · subst hq1; simp only [tip', spliceTwoTip, hq0, ↓reduceIte]
          exact hprev.trans (G'.reachable_src_tgt (.inr (.inl true)))
        · simp only [tip', spliceTwoTip, hq0, hq1, ↓reduceIte]; exact hprev
    card_V := by
      rw [Fintype.card_sum]
      obtain ⟨hc1, hc2⟩ := S.card_V
      refine ⟨?_, by omega⟩
      calc (d - 2) * (Fintype.card S.V + Fintype.card V_add - Fintype.card W)
          = (d - 2) * (Fintype.card S.V - Fintype.card W) + (d - 2) * Fintype.card V_add := by
            rw [← mul_add]; congr 1; omega
        _ = 2 * (s + 1) := by rw [hc1, hcard_add]; ring
    contract := fun y x => by
      let eqvFun : ((S.E ⊕ (Bool ⊕ E_int)) ⊕ W → Bool) ≃
          (S.E ⊕ W → Bool) × (Bool × Bool × (E_int → Bool)) :=
        { toFun := fun γ' =>
            (γ' ∘ oldEdge, (γ' (.inr q₀), γ' (.inr q₁), fun e => γ' (.inl (.inr (.inr e)))))
          invFun := fun p s => match s with
            | .inl (.inl e₀) => p.1 (.inl e₀)
            | .inl (.inr (.inl false)) => p.1 (.inr q₀)
            | .inl (.inr (.inl true)) => p.1 (.inr q₁)
            | .inl (.inr (.inr e)) => p.2.2.2 e
            | .inr q => if q = q₀ then p.2.1 else if q = q₁ then p.2.2.1 else p.1 (.inr q)
          left_inv := fun γ' => by
            ext ((e₀ | (b | e_int)) | q)
            · rfl
            · rcases b with _ | _
              · simp [oldEdge, spliceTwoOldEdge_inr]
              · simp [oldEdge, spliceTwoOldEdge_inr, hq_ne.symm]
            · rfl
            · by_cases hq0 : q = q₀
              · subst hq0; simp
              · by_cases hq1 : q = q₁
                · subst hq1; simp [hq0]
                · simp [hq0, hq1, oldEdge, spliceTwoOldEdge_inr]
          right_inv := fun ⟨γ, a₀, a₁, β⟩ => by
            refine Prod.ext (funext fun s => ?_) (Prod.ext ?_ (Prod.ext ?_ (funext fun _ => rfl)))
            · cases s with
              | inl e₀ => rfl
              | inr q =>
                by_cases hq0 : q = q₀
                · subst hq0; simp [oldEdge, spliceTwoOldEdge_inr]
                · by_cases hq1 : q = q₁
                  · subst hq1; simp [oldEdge, spliceTwoOldEdge_inr, hq0]
                  · simp [oldEdge, spliceTwoOldEdge_inr, hq0, hq1]
            · simp
            · simp [hq_ne.symm] }
      have hrhs : (∑ γ' : (S.E ⊕ (Bool ⊕ E_int)) ⊕ W → Bool,
          (∏ v : S.V ⊕ V_add, (match v with
            | .inl u => S.openF u x (γ' ∘ oldEdge)
            | .inr v =>
              T_add v (γ' (.inl (.inr (.inl false)))) (γ' (.inl (.inr (.inl true))))
                (γ' (.inr q₀)) (γ' (.inr q₁)) (fun e_int => γ' (.inl (.inr (.inr e_int)))))) *
            ∏ q : W, (if q = q₀ ∨ q = q₁ then (1 : Matrix Bool Bool ℂ) else S.tipMat q)
              (y q) (γ' (.inr q))) =
          ∑ γ : S.E ⊕ W → Bool,
            (∏ u : S.V, S.openF u x γ) *
              (∑ z₀ : Bool, ∑ z₁ : Bool,
                (g.2.1 : Matrix (Fin g.1.val → Bool) (Fin g.1.val → Bool) ℂ)
                  (fun i => if i = i₀ then y q₀ else y q₁)
                  (fun i => if i = i₀ then z₀ else z₁) *
                  S.tipMat q₀ z₀ (γ (.inr q₀)) * S.tipMat q₁ z₁ (γ (.inr q₁))) *
              ∏ q ∈ (Finset.univ.erase q₀).erase q₁, S.tipMat q (y q) (γ (.inr q)) := by
        rw [← Fintype.sum_equiv eqvFun.symm
          (fun p =>
            (∏ v : S.V ⊕ V_add, (match v with
              | .inl u => S.openF u x ((eqvFun.symm p) ∘ oldEdge)
              | .inr v =>
                T_add v (eqvFun.symm p (.inl (.inr (.inl false))))
                  (eqvFun.symm p (.inl (.inr (.inl true))))
                  (eqvFun.symm p (.inr q₀)) (eqvFun.symm p (.inr q₁))
                  (fun e_int => eqvFun.symm p (.inl (.inr (.inr e_int)))))) *
              ∏ q : W, (if q = q₀ ∨ q = q₁ then (1 : Matrix Bool Bool ℂ) else S.tipMat q)
                (y q) (eqvFun.symm p (.inr q))) _ (fun _ => rfl)]
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun γ _ => ?_
        rw [Fintype.sum_prod_type]
        simp_rw [Fintype.sum_prod_type]
        let body (β : E_int → Bool) : ℂ :=
          (∏ u : S.V, S.openF u x γ) *
            (∏ v : V_add, T_add v (γ (.inr q₀)) (γ (.inr q₁)) (y q₀) (y q₁) β) *
            ∏ q ∈ (Finset.univ.erase q₀).erase q₁, S.tipMat q (y q) (γ (.inr q))
        have hterm_ab (a₀ a₁ : Bool) (β : E_int → Bool) :
            (∏ v : S.V ⊕ V_add, (match v with
              | .inl u => S.openF u x ((eqvFun.symm (γ, a₀, a₁, β)) ∘ oldEdge)
              | .inr v =>
                T_add v (eqvFun.symm (γ, a₀, a₁, β) (.inl (.inr (.inl false))))
                  (eqvFun.symm (γ, a₀, a₁, β) (.inl (.inr (.inl true))))
                  (eqvFun.symm (γ, a₀, a₁, β) (.inr q₀)) (eqvFun.symm (γ, a₀, a₁, β) (.inr q₁))
                  (fun e_int => eqvFun.symm (γ, a₀, a₁, β) (.inl (.inr (.inr e_int)))))) *
            (∏ q : W, (if q = q₀ ∨ q = q₁ then (1 : Matrix Bool Bool ℂ) else S.tipMat q)
              (y q) (eqvFun.symm (γ, a₀, a₁, β) (.inr q))) =
            if a₀ = y q₀ ∧ a₁ = y q₁ then body β else 0 := by
          have hcomp_γ : (eqvFun.symm (γ, a₀, a₁, β)) ∘ oldEdge = γ :=
            congrArg Prod.fst (eqvFun.apply_symm_apply (γ, a₀, a₁, β))
          have ha₀_val : eqvFun.symm (γ, a₀, a₁, β) (.inr q₀) = a₀ :=
            congrArg (Prod.fst ∘ Prod.snd) (eqvFun.apply_symm_apply (γ, a₀, a₁, β))
          have ha₁_val : eqvFun.symm (γ, a₀, a₁, β) (.inr q₁) = a₁ :=
            congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) (eqvFun.apply_symm_apply (γ, a₀, a₁, β))
          have hf0 : eqvFun.symm (γ, a₀, a₁, β) (.inl (.inr (.inl false))) = γ (.inr q₀) := rfl
          have hf1 : eqvFun.symm (γ, a₀, a₁, β) (.inl (.inr (.inl true))) = γ (.inr q₁) := rfl
          have hβ_val : (fun e_int => eqvFun.symm (γ, a₀, a₁, β) (.inl (.inr (.inr e_int)))) = β :=
            rfl
          rw [Fintype.prod_sum_type]
          simp only [hcomp_γ, ha₀_val, ha₁_val, hf0, hf1, hβ_val]
          rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ q₀),
            ← Finset.mul_prod_erase (Finset.univ.erase q₀) _
              (Finset.mem_erase.mpr ⟨hq_ne.symm, Finset.mem_univ q₁⟩)]
          simp only [true_or, or_true, ↓reduceIte, ha₀_val, ha₁_val, Matrix.one_apply]
          have hrest : (∏ q ∈ (Finset.univ.erase q₀).erase q₁,
              (if q = q₀ ∨ q = q₁ then (1 : Matrix Bool Bool ℂ) else S.tipMat q) (y q)
                (eqvFun.symm (γ, a₀, a₁, β) (.inr q))) =
              ∏ q ∈ (Finset.univ.erase q₀).erase q₁, S.tipMat q (y q) (γ (.inr q)) := by
            refine Finset.prod_congr rfl fun q hq => ?_
            have hq1 : q ≠ q₁ := (Finset.mem_erase.mp hq).1
            have hq0 : q ≠ q₀ := (Finset.mem_erase.mp (Finset.mem_erase.mp hq).2).1
            simp only [not_or.mpr ⟨hq0, hq1⟩, ↓reduceIte]
            have hval : eqvFun.symm (γ, a₀, a₁, β) (.inr q) = γ (.inr q) := by
              simp only [eqvFun, Equiv.coe_fn_symm_mk, hq0, hq1, ↓reduceIte]
            rw [hval]
          rw [hrest]
          by_cases h0 : y q₀ = a₀ <;> by_cases h1 : y q₁ = a₁
          · subst h0; subst h1
            simp only [and_self, ↓reduceIte, body]
            ring
          · simp only [h1, show ¬(a₀ = y q₀ ∧ a₁ = y q₁) from fun h => h1 h.2.symm,
              ↓reduceIte, mul_zero, zero_mul]
          · simp only [h0, show ¬(a₀ = y q₀ ∧ a₁ = y q₁) from fun h => h0 h.1.symm,
              ↓reduceIte, zero_mul, mul_zero]
          · simp only [h0, show ¬(a₀ = y q₀ ∧ a₁ = y q₁) from fun h => h0 h.1.symm,
              ↓reduceIte, zero_mul, mul_zero]
        simp_rw [hterm_ab]
        have collapse_a : (∑ a₀ : Bool, ∑ a₁ : Bool, ∑ β : E_int → Bool,
            if a₀ = y q₀ ∧ a₁ = y q₁ then body β else 0) = ∑ β : E_int → Bool, body β := by
          rw [Fintype.sum_bool]
          simp_rw [Fintype.sum_bool]
          cases y q₀ <;> cases y q₁ <;> simp
        rw [collapse_a]
        dsimp only [body]
        rw [← Finset.sum_mul, ← Finset.mul_sum, hT_contract]
      rw [placeAct_two_mul_apply g h2 M y x, S.contract_update_two hq_ne _ y x, hrhs]
    loc_in := by
      rintro (u | _) x₁ x₂ γ' h
      · exact S.loc_in u x₁ x₂ (γ' ∘ oldEdge) fun q hq => h q (congrArg Sum.inl hq)
      · rfl
    loc_edge := by
      rintro (u | v) x γ₁ γ₂ h
      · exact S.loc_edge u x (γ₁ ∘ oldEdge) (γ₂ ∘ oldEdge) fun e he => h ((hmap_u u e).mp he)
      · refine hT_loc v _ _ _ _ _ _ _ _ _ _
          (fun hv0 => ?_) (fun hv1 => ?_) (fun e_int he => ?_)
        · subst hv0
          exact ⟨h (Or.inr rfl),
            h (Or.inl (by simp only [capGraph, tip', spliceTwoTip, ↓reduceIte]))⟩
        · subst hv1
          exact ⟨h (Or.inr rfl),
            h (Or.inl (by simp only [capGraph, tip', spliceTwoTip, hq_ne.symm, ↓reduceIte]))⟩
        · exact h (he.imp (congrArg (Sum.inl ∘ Sum.inr)) (congrArg (Sum.inl ∘ Sum.inr))) }

/-- Step for a general `2`-qubit gate in degree `d = 4` (adds `Unit` vertex and `Bool ⊕ Empty`
edges). -/
private noncomputable def openStateTwoDegFour {W : Type} [Fintype W] [DecidableEq W]
    {M : Matrix (W → Bool) (W → Bool) ℂ} {s : ℕ} (S : OpenState 4 W M s)
    (g : ActiveGate W) (h2 : g.1.val = 2) :
    OpenState 4 W ((placeAct g : Matrix _ _ ℂ) * M) (s + 1) :=
  let i₀ : Fin g.1.val := ⟨0, by omega⟩
  let q₀ : W := g.2.2 i₀
  let q₁ : W := g.2.2 ⟨1, by omega⟩
  S.spliceTwo g h2 Unit Empty { src := Empty.elim, tgt := Empty.elim } (fun e => Empty.elim e)
    () () (by simp)
    (fun ⟨⟩ => by
      have hemp : ({ src := Empty.elim, tgt := Empty.elim } : Multigraph Unit Empty).incidenceSet ()
          = ∅ := by ext e; exact Empty.elim e
      rw [hemp, ncard_empty]; rfl)
    (fun _ b₀ b₁ a₀ a₁ _ =>
      ∑ z₀ : Bool, ∑ z₁ : Bool,
        (g.2.1 : Matrix (Fin g.1.val → Bool) (Fin g.1.val → Bool) ℂ)
          (fun i => if i = i₀ then a₀ else a₁)
          (fun i => if i = i₀ then z₀ else z₁) *
        S.tipMat q₀ z₀ b₀ * S.tipMat q₁ z₁ b₁)
    (fun _ _ _ _ => by simp only [Fintype.sum_unique, Fintype.prod_unique]; rfl)
    (fun ⟨⟩ _ _ _ _ _ _ _ _ _ _ h0 h1 _ => by
      obtain ⟨rfl, rfl⟩ := h0 rfl
      obtain ⟨rfl, rfl⟩ := h1 rfl
      rfl)

/-- Step for a bond-rank-two `2`-qubit gate in degree `d = 3` (adds `Bool` vertices and
`Bool ⊕ Unit` edges). -/
private noncomputable def openStateTwoDegThree {W : Type} [Fintype W] [DecidableEq W]
    {M : Matrix (W → Bool) (W → Bool) ℂ} {s : ℕ} (S : OpenState 3 W M s)
    (g : ActiveGate W) (h2 : g.1.val = 2) (hbond : HasBondRankTwo (h2 ▸ g.2.1)) :
    OpenState 3 W ((placeAct g : Matrix _ _ ℂ) * M) (s + 1) :=
  let q₀ : W := g.2.2 ⟨0, by omega⟩
  let q₁ : W := g.2.2 ⟨1, by omega⟩
  let L_ten : Bool → Bool → Bool → ℂ := Classical.choose hbond
  let R_ten : Bool → Bool → Bool → ℂ := Classical.choose (Classical.choose_spec hbond)
  let G_int : Multigraph Bool Unit := { src := fun _ => false, tgt := fun _ => true }
  S.spliceTwo g h2 Bool Unit G_int (fun _ => Bool.false_ne_true) false true (by simp)
    (fun b => by
      have hset : G_int.incidenceSet b = {()} := by
        ext ⟨⟩; cases b <;> simp [Multigraph.mem_incidenceSet, G_int]
      rw [hset, ncard_singleton]
      cases b <;> decide)
    (fun v b₀ b₁ a₀ a₁ β => match v with
      | false => ∑ z₀ : Bool, L_ten z₀ a₀ (β ()) * S.tipMat q₀ z₀ b₀
      | true => ∑ z₁ : Bool, R_ten z₁ a₁ (β ()) * S.tipMat q₁ z₁ b₁)
    (fun b₀ b₁ a₀ a₁ => by
      have hg_eq (z₀ z₁ : Bool) :
          (g.2.1 : Matrix (Fin g.1.val → Bool) (Fin g.1.val → Bool) ℂ)
            (fun i => if i = ⟨0, by omega⟩ then a₀ else a₁)
            (fun i => if i = ⟨0, by omega⟩ then z₀ else z₁) =
            ∑ b : Bool, L_ten z₀ a₀ b * R_ten z₁ a₁ b := by
        have hLR := Classical.choose_spec (Classical.choose_spec hbond)
        rcases g with ⟨⟨arity, har_lt⟩, gate, wires⟩
        dsimp only at h2 hLR ⊢
        subst h2
        exact hLR (fun i => if i = 0 then a₀ else a₁) (fun i => if i = 0 then z₀ else z₁)
      have hprod_unit : (∑ β : Unit → Bool, ∏ v : Bool, (match v with
          | false => ∑ z₀ : Bool, L_ten z₀ a₀ (β ()) * S.tipMat q₀ z₀ b₀
          | true => ∑ z₁ : Bool, R_ten z₁ a₁ (β ()) * S.tipMat q₁ z₁ b₁)) =
          ∑ b : Bool,
            (∑ z₀ : Bool, L_ten z₀ a₀ b * S.tipMat q₀ z₀ b₀) *
              ∑ z₁ : Bool, R_ten z₁ a₁ b * S.tipMat q₁ z₁ b₁ := by
        simp only [Fintype.prod_bool]
        exact Fintype.sum_equiv (Equiv.funUnique Unit Bool) _ _ fun _ => mul_comm _ _
      refine hprod_unit.trans ?_
      simp only [Finset.sum_mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun z₀ _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun z₁ _ => ?_
      rw [hg_eq z₀ z₁]
      simp only [Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => by dsimp only [q₀, q₁]; ring)
    (fun v _ _ _ _ _ _ _ _ _ _ h0 h1 hβ => by
      cases v
      · obtain ⟨rfl, rfl⟩ := h0 rfl
        rw [hβ (Or.inl rfl)]
      · obtain ⟨rfl, rfl⟩ := h1 rfl
        rw [hβ (Or.inr rfl)])


end Cslib.Circuits.Frontier
