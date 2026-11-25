/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
-- `import all`: reads private `ActiveGate`, `placeAct`, `placeAct_apply` from `ActiveSplit`.
import all CslibFrontier.Computability.Circuit.Frontier.Quantum.WireNetwork.ActiveSplit
import CslibFrontier.Computability.Circuit.Frontier.Layouts.Basic
import CslibFrontier.Foundations.Data.Set.Card
import Mathlib.Data.Fintype.Sum

/-!
# Open wire-segment tensor network states and single-wire gate transitions

Internal capped/open multigraph structures (`capGraph`, `CappedWireNet`, `OpenState`) and inductive
steps for empty circuits, zero-qubit global phase gates, and single-qubit gates, together with
two-wire contraction update helpers.
-/

-- This proof-only companion is intentionally private; sibling WireNetwork modules use import all.
set_option linter.privateModule false

namespace Cslib.Circuits.Frontier

open Set Matrix
open scoped Finset Kronecker

private theorem reachable_map_inl {V V' E E' : Type} {G : Multigraph V E}
    {G' : Multigraph V' E'} (f : V ↪ V')
    (hedges : ∀ e : E, ∃ e' : E', G'.ends e' = Sym2.map f (G.ends e))
    {u w : V} (hr : G.toSimpleGraph.Reachable u w) :
    G'.toSimpleGraph.Reachable (f u) (f w) := by
  obtain ⟨p⟩ := hr
  induction p with
  | nil => exact .refl _
  | cons hab _ ih =>
    obtain ⟨hab_ne, e₀, he₀⟩ := Multigraph.toSimpleGraph_adj.mp hab
    obtain ⟨e', he'⟩ := hedges e₀
    exact (Multigraph.toSimpleGraph_adj.mpr
      ⟨fun h => hab_ne (f.injective h), e', he'.trans (he₀ ▸ rfl)⟩).reachable.trans ih

private theorem mem_closed_iff_of_reachable {V E : Type} {G : Multigraph V E}
    {Comp : Set V} (hcut : G.edgeCut Comp = ∅) {u w : V}
    (hr : G.toSimpleGraph.Reachable u w) : u ∈ Comp ↔ w ∈ Comp := by
  obtain ⟨p⟩ := hr
  induction p with
  | nil => exact Iff.rfl
  | cons hab _ ih =>
    obtain ⟨_, e, hends⟩ := Multigraph.toSimpleGraph_adj.mp hab
    rcases Sym2.eq_iff.mp hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (G.edgeCut_eq_empty_iff.mp hcut e).trans ih
    · exact (G.edgeCut_eq_empty_iff.mp hcut e).symm.trans ih

/-- Capped multigraph obtained by joining each wire `q : W`'s current `tip q : V` to a degree-one
output leaf `.inr q : V ⊕ W` via edge `.inr q : E ⊕ W`. -/
private def capGraph {V E W : Type} (G : Multigraph V E) (tip : W → V) :
    Multigraph (V ⊕ W) (E ⊕ W) where
  src
    | .inl e => .inl (G.src e)
    | .inr q => .inl (tip q)
  tgt
    | .inl e => .inl (G.tgt e)
    | .inr q => .inr q

private theorem capGraph_loopless {V E W : Type} {G : Multigraph V E} (hG : G.Loopless)
    (tip : W → V) : (capGraph G tip).Loopless := by
  rintro (e | q)
  · exact (hG e <| Sum.inl.inj ·)
  · exact Sum.inl_ne_inr

private theorem capGraph_incidence_inr {V E W : Type} (G : Multigraph V E) (tip : W → V)
    (q : W) : (capGraph G tip).incidenceSet (.inr q) = {.inr q} := by
  ext (_ | _) <;> simp [Multigraph.mem_incidenceSet, capGraph, eq_comm]

/-- Compiled capped wire-segment tensor network for an active unitary `M : Matrix (W → Bool) _ ℂ`
using `s` two-qubit gates and maximum degree `d` (`d = 3` or `d = 4`). -/
private structure CappedWireNet (d : ℕ) (W : Type) [Fintype W]
    (M : Matrix (W → Bool) (W → Bool) ℂ) (s : ℕ) : Prop where
  exists_net :
    ∃ (V_fin E_fin : Type) (_ : Fintype V_fin) (_ : DecidableEq V_fin)
      (_ : Fintype E_fin) (_ : DecidableEq E_fin)
      (G : Multigraph V_fin E_fin) (inVert outVert : W ↪ V_fin)
      (F : V_fin → (W → Bool) → (W → Bool) → (E_fin → Bool) → ℂ),
      G.Loopless ∧
      G.MaxDegreeLE d ∧
      Disjoint (Set.range inVert) (Set.range outVert) ∧
      (∀ q : W, (G.incidenceSet (inVert q)).ncard = 1 ∧ (G.incidenceSet (outVert q)).ncard = 1) ∧
      (∀ q : W, G.toSimpleGraph.Reachable (inVert q) (outVert q)) ∧
      Fintype.card V_fin ≤ 2 * Fintype.card W + 2 * s ∧
      (∀ Comp : Set V_fin, G.edgeCut Comp = ∅ → Comp.ncard ≤ (G.touching Comp).ncard + 1 →
        G.cycleRankOn Comp + {q : W | inVert q ∈ Comp}.ncard ≤ s + 1) ∧
      (∀ y x : W → Bool, M y x = ∑ γ : E_fin → Bool, ∏ v : V_fin, F v x y γ) ∧
      (∀ v x₁ x₂ y γ, (∀ q, inVert q = v → x₁ q = x₂ q) → F v x₁ y γ = F v x₂ y γ) ∧
      (∀ v x y₁ y₂ γ, (∀ q, outVert q = v → y₁ q = y₂ q) → F v x y₁ γ = F v x y₂ γ) ∧
      (∀ v x y γ₁ γ₂, Set.EqOn γ₁ γ₂ (G.incidenceSet v) → F v x y γ₁ = F v x y γ₂)

/-- Inductive open state before capping output leaves. -/
private structure OpenState (d : ℕ) (W : Type) [Fintype W] [DecidableEq W]
    (M : Matrix (W → Bool) (W → Bool) ℂ) (s : ℕ) where
  V : Type
  E : Type
  instFV : Fintype V
  instDV : DecidableEq V
  instFE : Fintype E
  instDE : DecidableEq E
  G : Multigraph V E
  inVert : W ↪ V
  tip : W → V
  scalar : ℂ
  tipMat : W → Matrix Bool Bool ℂ
  openF : V → (W → Bool) → (E ⊕ W → Bool) → ℂ
  loopless : G.Loopless
  deg_inVert : ∀ q : W, ((capGraph G tip).incidenceSet (.inl (inVert q))).ncard = 1
  deg_gate : ∀ v : V, v ∉ Set.range inVert → ((capGraph G tip).incidenceSet (.inl v)).ncard = d
  reach_tip : ∀ q : W, G.toSimpleGraph.Reachable (inVert q) (tip q)
  card_V : (d - 2) * (Fintype.card V - Fintype.card W) = 2 * s ∧ Fintype.card W ≤ Fintype.card V
  contract : ∀ y x : W → Bool,
    M y x = scalar * ∑ γ : E ⊕ W → Bool,
      (∏ v : V, openF v x γ) * ∏ q : W, tipMat q (y q) (γ (.inr q))
  loc_in : ∀ v x₁ x₂ γ, (∀ q, inVert q = v → x₁ q = x₂ q) → openF v x₁ γ = openF v x₂ γ
  loc_edge : ∀ v x γ₁ γ₂, Set.EqOn γ₁ γ₂ ((capGraph G tip).incidenceSet (.inl v)) →
    openF v x γ₁ = openF v x γ₂

attribute [instance] OpenState.instFV OpenState.instDV OpenState.instFE OpenState.instDE

/-- Helper: reindexing incident edges at `.inl u` along an injection `emb : E ⊕ W ↪ E' ⊕ W` that
bijects `(capGraph G tip).incidenceSet (.inl u)` onto
`(capGraph G' tip').incidenceSet (.inl (fV u))` preserves `.ncard`. -/
private theorem ncard_incidence_eq_of_bij {V V' E E' W : Type}
    (G : Multigraph V E) (tip : W → V) (G' : Multigraph V' E') (tip' : W → V')
    (fV : V → V') (emb : E ⊕ W ↪ E' ⊕ W) (u : V)
    (hmap : ∀ e, e ∈ (capGraph G tip).incidenceSet (.inl u) ↔
      emb e ∈ (capGraph G' tip').incidenceSet (.inl (fV u)))
    (hsurj : ∀ e' ∈ (capGraph G' tip').incidenceSet (.inl (fV u)), ∃ e, emb e = e') :
    ((capGraph G' tip').incidenceSet (.inl (fV u))).ncard =
      ((capGraph G tip).incidenceSet (.inl u)).ncard := by
  suffices (capGraph G' tip').incidenceSet (.inl (fV u)) =
      emb '' (capGraph G tip).incidenceSet (.inl u) by
    rw [this, ncard_image_of_injective _ emb.injective]
  ext e'
  exact ⟨fun he' => let ⟨e, he⟩ := hsurj e' he'; ⟨e, (hmap e).mpr (he ▸ he'), he⟩,
    fun ⟨e, he, h⟩ => h ▸ (hmap e).mp he⟩

/-- Base open state for `[] : List (ActiveGate W)`. -/
private noncomputable def openStateNil (d : ℕ) (W : Type) [Fintype W] [DecidableEq W] :
    OpenState d W (1 : Matrix (W → Bool) (W → Bool) ℂ) 0 where
  V := W
  E := Empty
  instFV := inferInstance
  instDV := inferInstance
  instFE := inferInstance
  instDE := inferInstance
  G := { src := Empty.elim, tgt := Empty.elim }
  inVert := Function.Embedding.refl W
  tip := id
  scalar := 1
  tipMat := fun _ => 1
  openF := fun v x γ => if γ (.inr v) = x v then 1 else 0
  loopless := fun e => Empty.elim e
  deg_inVert := fun q => by
    have hset : (capGraph { src := Empty.elim, tgt := Empty.elim } id).incidenceSet (.inl q) =
        {(.inr q : Empty ⊕ W)} := by
      ext (e | q')
      · exact Empty.elim e
      · simp [Multigraph.mem_incidenceSet, capGraph, eq_comm]
    change ((capGraph { src := Empty.elim, tgt := Empty.elim } id).incidenceSet (.inl q)).ncard = 1
    rw [hset, ncard_singleton]
  deg_gate := fun v hv => absurd ⟨v, rfl⟩ hv
  reach_tip := fun _ => SimpleGraph.Reachable.refl _
  card_V := ⟨by simp, le_rfl⟩
  contract := fun y x => by
    rw [one_mul, Matrix.one_apply]
    let eqv : (Empty ⊕ W → Bool) ≃ (W → Bool) :=
      { toFun := fun γ q => γ (.inr q)
        invFun := fun z s => match s with | .inl e => Empty.elim e | .inr q => z q
        left_inv := fun γ => by
          ext (e | q)
          · exact Empty.elim e
          · rfl
        right_inv := fun z => rfl }
    have hsum : (∑ γ : Empty ⊕ W → Bool,
        (∏ v : W, if γ (.inr v) = x v then (1 : ℂ) else 0) *
          ∏ q : W, (1 : Matrix Bool Bool ℂ) (y q) (γ (.inr q))) =
        ∑ z : W → Bool,
          (∏ v : W, if z v = x v then (1 : ℂ) else 0) *
            ∏ q : W, (1 : Matrix Bool Bool ℂ) (y q) (z q) :=
      Fintype.sum_equiv eqv _ _ fun _ => rfl
    rw [hsum]
    have hterm (z : W → Bool) :
        (∏ v : W, if z v = x v then (1 : ℂ) else 0) *
          (∏ q : W, (1 : Matrix Bool Bool ℂ) (y q) (z q)) =
          if z = x then (if y = x then 1 else 0) else 0 := by
      by_cases hzx : z = x
      · subst hzx
        simp only [↓reduceIte, Finset.prod_const_one, one_mul, Matrix.one_apply]
        by_cases hyz : y = z
        · subst hyz
          simp only [↓reduceIte, Finset.prod_const_one]
        · simp only [hyz, ↓reduceIte]
          have ⟨q₀, hq₀⟩ : ∃ q, y q ≠ z q := Function.ne_iff.mp hyz
          exact Finset.prod_eq_zero (Finset.mem_univ q₀) (by simp only [hq₀, ↓reduceIte])
      · simp only [hzx, ↓reduceIte]
        have ⟨v₀, hv₀⟩ : ∃ v, z v ≠ x v := Function.ne_iff.mp hzx
        rw [Finset.prod_eq_zero (Finset.mem_univ v₀) (by simp only [hv₀, ↓reduceIte]), zero_mul]
    simp_rw [hterm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  loc_in := fun v x₁ x₂ γ h => by rw [h v rfl]
  loc_edge := fun v x γ₁ γ₂ h => by
    have hmem : (.inr v : Empty ⊕ W) ∈
        (capGraph { src := Empty.elim, tgt := Empty.elim } id).incidenceSet (.inl v) :=
      Or.inl rfl
    rw [h hmem]

/-- Step for a `0`-qubit global phase gate. -/
private noncomputable def openStateZero {d : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    {M : Matrix (W → Bool) (W → Bool) ℂ} {s : ℕ} (S : OpenState d W M s)
    (g : ActiveGate W) (h0 : g.1.val = 0) :
    OpenState d W ((placeAct g : Matrix _ _ ℂ) * M) s :=
  let c₀ : ℂ :=
    (g.2.1 : Matrix (Fin g.1.val → Bool) (Fin g.1.val → Bool) ℂ)
      (fun i => absurd i.isLt (by omega)) (fun i => absurd i.isLt (by omega))
  { S with
    scalar := c₀ * S.scalar
    contract := fun y x => by
      rw [Matrix.mul_apply]
      have hplace (z : W → Bool) :
          (placeAct g : Matrix _ _ ℂ) y z = if y = z then c₀ else 0 := by
        rw [placeAct_apply]
        have hno : ∀ q : W, ¬∃ i : Fin g.1.val, g.2.2 i = q :=
          fun _ ⟨i, _⟩ => absurd i.isLt (by omega)
        have hiff : (∀ q : W, (¬∃ i, g.2.2 i = q) → y q = z q) ↔ y = z :=
          ⟨fun h => funext fun q => h q (hno q), fun h q _ => congrFun h q⟩
        rw [if_congr hiff rfl rfl]
        by_cases hyz : y = z
        · subst hyz
          simp only [↓reduceIte]
          have harg : (y ∘ g.2.2) = fun i : Fin g.1.val => absurd i.isLt (by omega) :=
            funext fun i => absurd i.isLt (by omega)
          rw [harg]
        · simp only [hyz, ↓reduceIte]
      simp_rw [hplace, ite_mul, zero_mul]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      rw [S.contract y x, mul_assoc] }

/-- Step for a `1`-qubit gate on `W` (graph unchanged, absorbed into `tipMat`). -/
private noncomputable def openStateOne {d : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    {M : Matrix (W → Bool) (W → Bool) ℂ} {s : ℕ} (S : OpenState d W M s)
    (g : ActiveGate W) (h1 : g.1.val = 1) :
    OpenState d W ((placeAct g : Matrix _ _ ℂ) * M) s :=
  let i₀ : Fin g.1.val := ⟨0, by omega⟩
  let q₀ : W := g.2.2 i₀
  let gMat : Matrix Bool Bool ℂ :=
    Matrix.of fun b c =>
      (g.2.1 : Matrix (Fin g.1.val → Bool) (Fin g.1.val → Bool) ℂ) (fun _ => b) (fun _ => c)
  { S with
    tipMat := fun q => if q = q₀ then gMat * S.tipMat q₀ else S.tipMat q
    contract := fun y x => by
      rw [Matrix.mul_apply]
      have hplace (z : W → Bool) :
          (placeAct g : Matrix _ _ ℂ) y z =
            if ∀ q ≠ q₀, y q = z q then gMat (y q₀) (z q₀) else 0 := by
        rw [placeAct_apply]
        have hiff : (∀ q : W, (¬∃ i, g.2.2 i = q) → y q = z q) ↔ ∀ q ≠ q₀, y q = z q := by
          refine forall_congr' fun q => imp_congr_left
            ⟨fun h hq => h ⟨i₀, hq.symm⟩, fun h ⟨i, hi⟩ => h ?_⟩
          rw [← hi]; congr 1; ext; omega
        rw [if_congr hiff rfl rfl]
        split_ifs with h
        · have hy_eq : (y ∘ g.2.2) = fun _ : Fin g.1.val => y q₀ :=
            funext fun i => (show i = i₀ by ext; omega) ▸ rfl
          have hz_eq : (z ∘ g.2.2) = fun _ : Fin g.1.val => z q₀ :=
            funext fun i => (show i = i₀ by ext; omega) ▸ rfl
          rw [hy_eq, hz_eq]
          rfl
        · rfl
      have hsum_z : (∑ z : W → Bool, (placeAct g : Matrix _ _ ℂ) y z * M z x) =
          ∑ b : Bool, gMat (y q₀) b * M (Function.update y q₀ b) x := by
        simp_rw [hplace, ite_mul, zero_mul]
        have hfib (z : W → Bool) :
            (∀ q ≠ q₀, y q = z q) ↔ ∃ b : Bool, z = Function.update y q₀ b := by
          constructor
          · intro hz
            refine ⟨z q₀, funext fun q => ?_⟩
            by_cases hq : q = q₀
            · subst hq; simp only [Function.update_self]
            · simp only [ne_eq, hq, not_false_eq_true, Function.update_of_ne, (hz q hq).symm]
          · rintro ⟨b, rfl⟩ q hq
            simp only [ne_eq, hq, not_false_eq_true, Function.update_of_ne]
        let fupd (b : Bool) : W → Bool := Function.update y q₀ b
        have hfupd_inj : Function.Injective fupd := fun b₁ b₂ h => by
          simpa [fupd] using congrFun h q₀
        have hfilt : (Finset.univ.filter fun z : W → Bool => ∀ q ≠ q₀, y q = z q) =
            Finset.univ.image fupd := by
          ext z
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, hfib, Finset.mem_image]
          exact ⟨fun ⟨b, hb⟩ => ⟨b, hb.symm⟩, fun ⟨b, hb⟩ => ⟨b, hb.symm⟩⟩
        rw [← Finset.sum_filter, hfilt, Finset.sum_image (fun _ _ _ _ h => hfupd_inj h)]
        refine Finset.sum_congr rfl fun b _ => ?_
        simp only [fupd, Function.update_self]
      rw [hsum_z]
      have hstep1 : (∑ b : Bool, gMat (y q₀) b * M (Function.update y q₀ b) x) =
          S.scalar * ∑ b : Bool, ∑ γ : S.E ⊕ W → Bool,
            gMat (y q₀) b *
              ((∏ v : S.V, S.openF v x γ) *
                ∏ q : W, S.tipMat q (Function.update y q₀ b q) (γ (.inr q))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [S.contract (Function.update y q₀ b) x, ← mul_assoc, mul_comm (gMat (y q₀) b) S.scalar,
          mul_assoc, Finset.mul_sum]
      rw [hstep1, Finset.sum_comm]
      congr 1
      refine Finset.sum_congr rfl fun γ _ => ?_
      have hprod_upd (b : Bool) :
          (∏ q : W, S.tipMat q (Function.update y q₀ b q) (γ (.inr q))) =
            S.tipMat q₀ b (γ (.inr q₀)) *
              ∏ q ∈ Finset.univ.erase q₀, S.tipMat q (y q) (γ (.inr q)) := by
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ q₀), Function.update_self]
        congr 1
        refine Finset.prod_congr rfl fun q hq => ?_
        rw [Function.update_of_ne (Finset.mem_erase.mp hq).1]
      have hprod_new :
          (∏ q : W, (if q = q₀ then gMat * S.tipMat q₀ else S.tipMat q) (y q) (γ (.inr q))) =
            (gMat * S.tipMat q₀) (y q₀) (γ (.inr q₀)) *
              ∏ q ∈ Finset.univ.erase q₀, S.tipMat q (y q) (γ (.inr q)) := by
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ q₀)]
        simp only [↓reduceIte]
        congr 1
        refine Finset.prod_congr rfl fun q hq => ?_
        simp only [(Finset.mem_erase.mp hq).1, ↓reduceIte]
      rw [hprod_new, Matrix.mul_apply, Fintype.sum_bool]
      simp_rw [hprod_upd]
      rw [Fintype.sum_bool]
      ring }

private theorem activeGate_wires_ne {W : Type} (g : ActiveGate W) (h2 : g.1.val = 2) :
    g.2.2 ⟨0, by omega⟩ ≠ g.2.2 ⟨1, by omega⟩ := fun h => by
  simpa using congrArg Fin.val (g.2.2.injective h)

private theorem placeAct_two_mul_apply {W : Type} [Fintype W] [DecidableEq W]
    (g : ActiveGate W) (h2 : g.1.val = 2) (M : Matrix (W → Bool) (W → Bool) ℂ)
    (y x : W → Bool) :
    let i₀ : Fin g.1.val := ⟨0, by omega⟩
    let i₁ : Fin g.1.val := ⟨1, by omega⟩
    ((placeAct g : Matrix (W → Bool) (W → Bool) ℂ) * M) y x =
      ∑ z₀ : Bool, ∑ z₁ : Bool,
        (g.2.1 : Matrix (Fin g.1.val → Bool) (Fin g.1.val → Bool) ℂ)
          (fun i => if i = i₀ then y (g.2.2 i₀) else y (g.2.2 i₁))
          (fun i => if i = i₀ then z₀ else z₁) *
        M (Function.update (Function.update y (g.2.2 i₁) z₁) (g.2.2 i₀) z₀) x := by
  intro i₀ i₁
  set q₀ : W := g.2.2 i₀
  set q₁ : W := g.2.2 i₁
  have hq_ne : q₀ ≠ q₁ := activeGate_wires_ne g h2
  have hi_cases (i : Fin g.1.val) : i = i₀ ∨ i = i₁ := by
    rcases (by omega : i.val = 0 ∨ i.val = 1) with h | h <;>
      [exact Or.inl (Fin.ext h); exact Or.inr (Fin.ext h)]
  have hi_ne : i₁ ≠ i₀ := fun h => by simpa [i₀, i₁] using congrArg Fin.val h
  have hplace (z : W → Bool) :
      (placeAct g : Matrix (W → Bool) (W → Bool) ℂ) y z =
        if ∀ q, q ≠ q₀ ∧ q ≠ q₁ → y q = z q then
          (g.2.1 : Matrix (Fin g.1.val → Bool) (Fin g.1.val → Bool) ℂ)
            (fun i => if i = i₀ then y q₀ else y q₁)
            (fun i => if i = i₀ then z q₀ else z q₁)
        else 0 := by
    rw [placeAct_apply, if_congr (forall_congr' fun q => imp_congr_left
      ⟨fun h => ⟨fun h0 => h ⟨i₀, h0.symm⟩, fun h1 => h ⟨i₁, h1.symm⟩⟩,
        fun (h : q ≠ q₀ ∧ q ≠ q₁) ⟨i, hi⟩ =>
          (hi_cases i).elim (fun e => h.1 (hi ▸ congrArg g.2.2 e))
            fun e => h.2 (hi ▸ congrArg g.2.2 e)⟩) rfl rfl]
    have hcomp (w : W → Bool) : w ∘ g.2.2 = fun i => if i = i₀ then w q₀ else w q₁ :=
      funext fun i => by rcases hi_cases i with rfl | rfl <;> simp [hi_ne, q₀, q₁]
    split_ifs
    · rw [hcomp y, hcomp z]
    · rfl
  rw [Matrix.mul_apply]
  simp_rw [hplace, ite_mul, zero_mul]
  let fupd (p : Bool × Bool) : W → Bool := Function.update (Function.update y q₁ p.2) q₀ p.1
  have hinv {z : W → Bool} (hz : ∀ q, q ≠ q₀ ∧ q ≠ q₁ → y q = z q) : fupd (z q₀, z q₁) = z :=
    funext fun q => by
      by_cases h0 : q = q₀; · subst h0; simp [fupd]
      by_cases h1 : q = q₁; · subst h1; simp [fupd, h0]
      simp [fupd, h0, h1, hz q ⟨h0, h1⟩]
  rw [← Finset.sum_filter, ← Fintype.sum_prod_type fun p : Bool × Bool =>
    (g.2.1 : Matrix (Fin g.1.val → Bool) (Fin g.1.val → Bool) ℂ)
      (fun i => if i = i₀ then y q₀ else y q₁) (fun i => if i = i₀ then p.1 else p.2) *
    M (fupd p) x]
  exact Finset.sum_nbij' (fun z => (z q₀, z q₁)) fupd (fun _ _ => Finset.mem_univ _)
    (fun _ _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun q ⟨h0, h1⟩ => by simp [fupd, h0, h1]⟩)
    (fun z hz => hinv (Finset.mem_filter.mp hz).2) (fun ⟨_, _⟩ _ => by simp [fupd, hq_ne.symm])
    (fun z hz => by dsimp only; rw [hinv (Finset.mem_filter.mp hz).2])

private theorem OpenState.contract_update_two {d : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    {M : Matrix (W → Bool) (W → Bool) ℂ} {s : ℕ} (S : OpenState d W M s)
    {q₀ q₁ : W} (hq_ne : q₀ ≠ q₁) (K : Bool → Bool → ℂ) (y x : W → Bool) :
    (∑ z₀ : Bool, ∑ z₁ : Bool,
      K z₀ z₁ * M (Function.update (Function.update y q₁ z₁) q₀ z₀) x) =
    S.scalar * ∑ γ : S.E ⊕ W → Bool,
      (∏ u : S.V, S.openF u x γ) *
        (∑ z₀ : Bool, ∑ z₁ : Bool,
          K z₀ z₁ * S.tipMat q₀ z₀ (γ (.inr q₀)) * S.tipMat q₁ z₁ (γ (.inr q₁))) *
        ∏ q ∈ (Finset.univ.erase q₀).erase q₁, S.tipMat q (y q) (γ (.inr q)) := by
  have hstep1 : (∑ z₀ : Bool, ∑ z₁ : Bool,
      K z₀ z₁ * M (Function.update (Function.update y q₁ z₁) q₀ z₀) x) =
      S.scalar * ∑ z₀ : Bool, ∑ z₁ : Bool, ∑ γ : S.E ⊕ W → Bool,
        K z₀ z₁ * ((∏ u : S.V, S.openF u x γ) *
          ∏ q : W, S.tipMat q
            (Function.update (Function.update y q₁ z₁) q₀ z₀ q) (γ (.inr q))) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun z₀ _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun z₁ _ => ?_
    rw [S.contract _ x, ← mul_assoc, mul_comm (K z₀ z₁) S.scalar, mul_assoc, Finset.mul_sum]
  rw [hstep1, Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := Finset.univ (α := Bool)) (t := Finset.univ (α := S.E ⊕ W → Bool))]
  congr 1; refine Finset.sum_congr rfl fun γ _ => ?_
  have hupd (z₀ z₁ : Bool) :
      (∏ q : W, S.tipMat q (Function.update (Function.update y q₁ z₁) q₀ z₀ q) (γ (.inr q))) =
      S.tipMat q₀ z₀ (γ (.inr q₀)) * S.tipMat q₁ z₁ (γ (.inr q₁)) *
        ∏ q ∈ (Finset.univ.erase q₀).erase q₁, S.tipMat q (y q) (γ (.inr q)) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ q₀),
      ← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨hq_ne.symm, Finset.mem_univ q₁⟩),
      Function.update_self, Function.update_of_ne hq_ne.symm, Function.update_self, mul_assoc]
    congr 2; refine Finset.prod_congr rfl fun q hq => ?_
    rw [Function.update_of_ne (Finset.mem_erase.mp (Finset.mem_erase.mp hq).2).1,
      Function.update_of_ne (Finset.mem_erase.mp hq).1]
  simp_rw [hupd]
  rw [Finset.sum_comm, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => by ring


end Cslib.Circuits.Frontier
