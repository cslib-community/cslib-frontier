/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
-- `import all`: reads private `ActiveGate`, `placeAct`, `evalAct` from `ActiveSplit`, private
-- `OpenState` / `CappedWireNet` from `OpenState`, and private 2-qubit splice steps from
-- `SpliceTwo`.
import all CslibFrontier.Computability.Circuit.Frontier.Quantum.WireNetwork.ActiveSplit
import all CslibFrontier.Computability.Circuit.Frontier.Quantum.WireNetwork.OpenState
import all CslibFrontier.Computability.Circuit.Frontier.Quantum.WireNetwork.SpliceTwo
import CslibFrontier.Computability.Circuit.Frontier.Layouts.Basic
import CslibFrontier.Computability.Circuit.Quantum.PhaseGates
import CslibFrontier.Foundations.Data.Set.Card
import Mathlib.Data.Fintype.Sum

/-!
# Closing open wire-network states and component cycle-rank bounds

Closes any `OpenState d W M s` (`d ∈ {3, 4}`) into a `CappedWireNet d W M s` with degree-one
output leaves and component cycle-rank inequality (`OpenState.toCappedWireNet`), and compiles
arbitrary active gate lists (`exists_cappedWireNet`).
-/

-- This proof-only companion is intentionally private; sibling WireNetwork modules use import all.
set_option linter.privateModule false

namespace Cslib.Circuits.Frontier

open Set Matrix
open scoped Finset Kronecker

attribute [local instance] OpenState.instFV OpenState.instDV OpenState.instFE OpenState.instDE

private theorem OpenState.sum_comp_eq {d : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    {M : Matrix (W → Bool) (W → Bool) ℂ} {s : ℕ} (S : OpenState d W M s)
    (Comp : Set (S.V ⊕ W)) [DecidablePred (· ∈ Comp)] [Fintype Comp]
    (hreach_mem : ∀ q : W, (.inl (S.inVert q) : S.V ⊕ W) ∈ Comp ↔ (.inr q : S.V ⊕ W) ∈ Comp)
    (f : S.V ⊕ W → ℕ) :
    (∑ w : Comp, f w.1) =
      (∑ q ∈ Finset.univ.filter (fun q : W => (.inl (S.inVert q) : S.V ⊕ W) ∈ Comp),
        f (.inl (S.inVert q))) +
      (∑ q ∈ Finset.univ.filter (fun q : W => (.inl (S.inVert q) : S.V ⊕ W) ∈ Comp),
        f (.inr q)) +
      ∑ u ∈ Finset.univ.filter (fun u : S.V => (.inl u : S.V ⊕ W) ∈ Comp ∧ u ∉ Set.range S.inVert),
        f (.inl u) := by
  classical
  let inV : W ↪ S.V ⊕ W := S.inVert.trans ⟨Sum.inl, Sum.inl_injective⟩
  let outV : W ↪ S.V ⊕ W := ⟨Sum.inr, Sum.inr_injective⟩
  set FW := Finset.univ.filter (fun q : W => (.inl (S.inVert q) : S.V ⊕ W) ∈ Comp)
  set FI := Finset.univ.filter (fun u : S.V => (.inl u : S.V ⊕ W) ∈ Comp ∧ u ∉ Set.range S.inVert)
  have hsub : (∑ w : Comp, f w.1) = ∑ v ∈ Finset.univ.filter (· ∈ Comp), f v :=
    (Finset.sum_subtype (Finset.univ.filter (· ∈ Comp))
      (fun _ => Finset.mem_filter.trans (and_iff_right (Finset.mem_univ _))) f).symm
  rw [hsub]
  have hpart : (Finset.univ.filter (· ∈ Comp) : Finset (S.V ⊕ W)) =
      FW.image inV ∪ (FW.image outV ∪ FI.image Sum.inl) := by
    ext (u | q)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
        Finset.mem_image, inV, outV, FW, FI, Function.Embedding.trans_apply,
        Function.Embedding.coeFn_mk, Sum.inl.injEq, reduceCtorEq, and_false, exists_false,
        exists_eq_right, false_or, Set.mem_range]
      by_cases hu : ∃ y, S.inVert y = u
      · obtain ⟨y, rfl⟩ := hu
        exact ⟨fun h => Or.inl ⟨y, h, rfl⟩,
          fun h => h.elim (fun ⟨y', hy', hyy⟩ => S.inVert.injective hyy ▸ hy')
            fun h' => absurd ⟨y, rfl⟩ h'.2⟩
      · exact ⟨fun h => Or.inr ⟨h, hu⟩,
          fun h => h.elim (fun ⟨y, _, hy⟩ => absurd ⟨y, hy⟩ hu) And.left⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
        Finset.mem_image, inV, outV, FW, FI, Function.Embedding.trans_apply,
        Function.Embedding.coeFn_mk, reduceCtorEq, Sum.inr.injEq, and_false, exists_false,
        exists_eq_right, false_or, or_false]
      exact (hreach_mem q).symm
  have hd1 : Disjoint (FW.image inV) (FW.image outV ∪ FI.image Sum.inl) := by
    rw [Finset.disjoint_left]
    rintro _ hv1 hv2
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hv1
    rcases Finset.mem_union.mp hv2 with hv_out | hv_gate
    · obtain ⟨q', -, hqq⟩ := Finset.mem_image.mp hv_out
      exact Sum.inl_ne_inr hqq.symm
    · obtain ⟨u, hu, huq⟩ := Finset.mem_image.mp hv_gate
      exact (Finset.mem_filter.mp hu).2.2 ⟨q, Sum.inl.inj huq.symm⟩
  have hd2 : Disjoint (FW.image outV) (FI.image Sum.inl) := by
    rw [Finset.disjoint_left]
    rintro _ hv1 hv2
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hv1
    obtain ⟨u, -, huq⟩ := Finset.mem_image.mp hv2
    exact Sum.inl_ne_inr huq
  rw [hpart, Finset.sum_union hd1, Finset.sum_union hd2,
    Finset.sum_image (fun _ _ _ _ h => inV.injective h),
    Finset.sum_image (fun _ _ _ _ h => outV.injective h),
    Finset.sum_image (fun _ _ _ _ h => Sum.inl_injective h), ← add_assoc]
  rfl

open Classical in
/-- Close an `OpenState d W M s` (`d ∈ {3, 4}`, `Nonempty W`) into a `CappedWireNet d W M s`. -/
private theorem OpenState.toCappedWireNet {d : ℕ} (hd : d = 3 ∨ d = 4) {W : Type}
    [Fintype W] [DecidableEq W] [Nonempty W] {M : Matrix (W → Bool) (W → Bool) ℂ} {s : ℕ}
    (S : OpenState d W M s) : CappedWireNet d W M s := by
  let q_star : W := Classical.arbitrary W
  let G_fin := capGraph S.G S.tip
  let inV : W ↪ S.V ⊕ W := S.inVert.trans ⟨Sum.inl, Sum.inl_injective⟩
  let outV : W ↪ S.V ⊕ W := ⟨Sum.inr, Sum.inr_injective⟩
  let F_fin (v : S.V ⊕ W) (x y : W → Bool) (γ : S.E ⊕ W → Bool) : ℂ :=
    match v with
    | .inl u => S.openF u x γ
    | .inr q => (if q = q_star then S.scalar else 1) * S.tipMat q (y q) (γ (.inr q))
  have hreach_q (q : W) : G_fin.toSimpleGraph.Reachable (inV q) (outV q) :=
    (reachable_map_inl ⟨Sum.inl, Sum.inl_injective⟩
      (fun e₀ => ⟨.inl e₀, by simp [Multigraph.ends, G_fin, capGraph]⟩)
      (S.reach_tip q)).trans (G_fin.reachable_src_tgt (.inr q))
  refine ⟨⟨S.V ⊕ W, S.E ⊕ W, inferInstance, inferInstance, inferInstance, inferInstance,
    G_fin, inV, outV, F_fin, capGraph_loopless S.loopless S.tip, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩⟩
  · -- `G_fin.MaxDegreeLE d`
    rintro (u | q)
    · by_cases hu : u ∈ Set.range S.inVert
      · obtain ⟨q', rfl⟩ := hu
        rw [S.deg_inVert q']
        rcases hd with rfl | rfl <;> omega
      · rw [S.deg_gate u hu]
    · dsimp only [G_fin]
      rw [capGraph_incidence_inr, ncard_singleton]
      rcases hd with rfl | rfl <;> omega
  · -- `Disjoint (range inV) (range outV)`
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨q₁, rfl⟩ ⟨q₂, h⟩
    exact Sum.inl_ne_inr h.symm
  · -- Degree-one input and output leaves
    intro q
    exact ⟨S.deg_inVert q, by
      change ((capGraph S.G S.tip).incidenceSet (.inr q)).ncard = 1
      rw [capGraph_incidence_inr, ncard_singleton]⟩
  · exact hreach_q
  · -- `Fintype.card (S.V ⊕ W) ≤ 2 * Fintype.card W + 2 * s`
    rw [Fintype.card_sum]
    obtain ⟨hc1, hc2⟩ := S.card_V
    rcases hd with rfl | rfl <;> omega
  · -- Component cycle-rank bound: `G_fin.cycleRankOn Comp + {q | inV q ∈ Comp}.ncard ≤ s + 1`
    intro Comp hComp_cut hComp_conn
    have hloopless_ind : (G_fin.induce Comp).Loopless :=
      (capGraph_loopless S.loopless S.tip).induce Comp
    have hinc_eq (w : Comp) :
        ((G_fin.induce Comp).incidenceSet w).ncard = (G_fin.incidenceSet w.1).ncard := by
      have himg : G_fin.incidenceSet w.1 = Subtype.val '' (G_fin.induce Comp).incidenceSet w := by
        ext e
        constructor
        · intro he
          have hboth : G_fin.src e ∈ Comp ∧ G_fin.tgt e ∈ Comp := by
            have hce := G_fin.edgeCut_eq_empty_iff.mp hComp_cut e
            rcases he with hs | ht
            · exact ⟨hs ▸ w.2, hce.mp (hs ▸ w.2)⟩
            · exact ⟨hce.mpr (ht ▸ w.2), ht ▸ w.2⟩
          refine ⟨⟨e, hboth⟩, ?_, rfl⟩
          exact he.imp Subtype.ext Subtype.ext
        · rintro ⟨e', he', rfl⟩
          exact he'.imp (congrArg Subtype.val) (congrArg Subtype.val)
      rw [himg, ncard_image_of_injective _ Subtype.val_injective]
    have hhand := (G_fin.induce Comp).sum_ncard_incidenceSet hloopless_ind
    change _ = 2 * Nat.card ↥{e | G_fin.src e ∈ Comp ∧ G_fin.tgt e ∈ Comp} at hhand
    rw [Nat.card_coe_set_eq, ← G_fin.touching_eq_of_edgeCut_eq_empty hComp_cut] at hhand
    simp_rw [hinc_eq] at hhand
    have hreach_mem (q : W) : inV q ∈ Comp ↔ outV q ∈ Comp :=
      mem_closed_iff_of_reachable hComp_cut (hreach_q q)
    set W_in : Set W := {q : W | inV q ∈ Comp}
    set I_gate : Set S.V := {u : S.V | (.inl u : S.V ⊕ W) ∈ Comp ∧ u ∉ Set.range S.inVert}
    have hI_le : I_gate.ncard ≤ Fintype.card S.V - Fintype.card W := by
      have hsub : I_gate ⊆ (Set.range S.inVert)ᶜ := fun u hu => hu.2
      have hcompl := ncard_add_ncard_compl (Set.range S.inVert)
      rw [ncard_range_of_injective S.inVert.injective, Nat.card_eq_fintype_card,
        Nat.card_eq_fintype_card] at hcompl
      have hle := ncard_le_ncard hsub (toFinite _)
      omega
    have hcardW : (Finset.univ.filter (· ∈ W_in)).card = W_in.ncard := by
      rw [← ncard_coe_finset]; congr 1; ext q; simp
    have hcardI : (Finset.univ.filter (· ∈ I_gate)).card = I_gate.ncard := by
      rw [← ncard_coe_finset]; congr 1; ext u; simp
    have hsum_deg : (∑ w : Comp, (G_fin.incidenceSet w.1).ncard) =
        2 * W_in.ncard + d * I_gate.ncard := by
      rw [S.sum_comp_eq Comp hreach_mem (fun w => (G_fin.incidenceSet w).ncard)]
      change (∑ q ∈ Finset.univ.filter (· ∈ W_in), (G_fin.incidenceSet (inV q)).ncard) +
        (∑ q ∈ Finset.univ.filter (· ∈ W_in), (G_fin.incidenceSet (outV q)).ncard) +
        ∑ u ∈ Finset.univ.filter (· ∈ I_gate), (G_fin.incidenceSet (.inl u)).ncard = _
      have hdeg_out (q : W) : ((capGraph S.G S.tip).incidenceSet (.inr q)).ncard = 1 := by
        rw [capGraph_incidence_inr, ncard_singleton]
      simp only [G_fin, inV, outV, Function.Embedding.trans_apply, Function.Embedding.coeFn_mk]
      rw [Finset.sum_congr rfl fun q (_ : q ∈ Finset.univ.filter (· ∈ W_in)) => S.deg_inVert q,
        Finset.sum_congr rfl fun q (_ : q ∈ Finset.univ.filter (· ∈ W_in)) => hdeg_out q,
        Finset.sum_congr rfl fun u (hu : u ∈ Finset.univ.filter (· ∈ I_gate)) =>
          S.deg_gate u (Finset.mem_filter.mp hu).2.2]
      simp only [Finset.sum_const, smul_eq_mul, mul_one, hcardW, hcardI]
      ring
    have hcard_Comp : Comp.ncard = 2 * W_in.ncard + I_gate.ncard := by
      have h1 : Comp.ncard = ∑ _w : Comp, 1 := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, ← Nat.card_eq_fintype_card,
          Nat.card_coe_set_eq]
      rw [h1, S.sum_comp_eq Comp hreach_mem (fun _ => 1)]
      change (∑ _q ∈ Finset.univ.filter (· ∈ W_in), 1) +
        (∑ _q ∈ Finset.univ.filter (· ∈ W_in), 1) +
        (∑ _u ∈ Finset.univ.filter (· ∈ I_gate), 1) = _
      simp only [Finset.sum_const, smul_eq_mul, mul_one, hcardW, hcardI]
      omega
    obtain ⟨hc1, hc2⟩ := S.card_V
    rw [Multigraph.cycleRankOn]
    rcases hd with rfl | rfl <;> omega
  · -- Contraction identity
    intro y x
    rw [S.contract y x, Finset.mul_sum]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [Fintype.prod_sum_type]
    simp only [F_fin, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, ↓reduceIte]
    ring
  · -- Input locality
    rintro (u | q) x₁ x₂ y γ h
    · exact S.loc_in u x₁ x₂ γ fun q' hq' => h q' (congrArg Sum.inl hq')
    · rfl
  · -- Output locality
    rintro (u | q) x y₁ y₂ γ h
    · rfl
    · simp only [F_fin, h q rfl]
  · -- Edge locality
    rintro (u | q) x y γ₁ γ₂ h
    · exact S.loc_edge u x γ₁ γ₂ h
    · simp only [F_fin, h (by rw [capGraph_incidence_inr]; exact mem_singleton _)]

/-- Every list of active gates compiles into a `CappedWireNet 4 W` (`d = 4`), and into a
`CappedWireNet 3 W` (`d = 3`) when all arity-two gates satisfy `HasBondRankTwo`. -/
private theorem exists_cappedWireNet {W : Type} [Fintype W] [DecidableEq W] [Nonempty W]
    (L : List (ActiveGate W)) :
    CappedWireNet 4 W (evalAct L) (L.filter fun g => decide (g.1.val = 2)).length ∧
      ((∀ g ∈ L, ∀ h : g.1.val = 2, HasBondRankTwo (h ▸ g.2.1)) →
        CappedWireNet 3 W (evalAct L) (L.filter fun g => decide (g.1.val = 2)).length) := by
  suffices hopen :
      Nonempty (OpenState 4 W (evalAct L) (L.filter fun g => decide (g.1.val = 2)).length) ∧
        ((∀ g ∈ L, ∀ h : g.1.val = 2, HasBondRankTwo (h ▸ g.2.1)) →
          Nonempty (OpenState 3 W (evalAct L) (L.filter fun g => decide (g.1.val = 2)).length)) by
    exact ⟨let ⟨S₄⟩ := hopen.1; S₄.toCappedWireNet (Or.inr rfl),
      fun hb => let ⟨S₃⟩ := hopen.2 hb; S₃.toCappedWireNet (Or.inl rfl)⟩
  induction L using List.reverseRecOn with
  | nil =>
    exact ⟨⟨openStateNil 4 W⟩, fun _ => ⟨openStateNil 3 W⟩⟩
  | append_singleton L g ih =>
    have hlen_app : ((L ++ [g]).filter fun a => decide (a.1.val = 2)).length =
        (L.filter fun a => decide (a.1.val = 2)).length + (if g.1.val = 2 then 1 else 0) := by
      simp only [List.filter_append, List.filter_cons, List.filter_nil, List.length_append,
        decide_eq_true_eq]
      split_ifs <;> rfl
    have heval_app : (evalAct (L ++ [g]) : Matrix (W → Bool) (W → Bool) ℂ) =
        (placeAct g : Matrix _ _ ℂ) * (evalAct L : Matrix _ _ ℂ) := by
      rw [evalAct_append]
      simp only [evalAct, one_mul, Submonoid.coe_mul]
    rw [hlen_app, heval_app]
    obtain ⟨⟨S₄⟩, h₃⟩ := ih
    rcases (by omega : g.1.val = 0 ∨ g.1.val = 1 ∨ g.1.val = 2) with h0 | h1 | h2
    · simp only [h0, (by decide : (0 : ℕ) ≠ 2), ↓reduceIte, add_zero]
      exact ⟨⟨openStateZero S₄ g h0⟩, fun hb =>
        let ⟨S₃⟩ := h₃ fun a ha => hb a (List.mem_append_left _ ha)
        ⟨openStateZero S₃ g h0⟩⟩
    · simp only [h1, (by decide : (1 : ℕ) ≠ 2), ↓reduceIte, add_zero]
      exact ⟨⟨openStateOne S₄ g h1⟩, fun hb =>
        let ⟨S₃⟩ := h₃ fun a ha => hb a (List.mem_append_left _ ha)
        ⟨openStateOne S₃ g h1⟩⟩
    · simp only [h2, ↓reduceIte]
      refine ⟨⟨openStateTwoDegFour S₄ g h2⟩, fun hb => ?_⟩
      obtain ⟨S₃⟩ := h₃ fun a ha => hb a (List.mem_append_left _ ha)
      exact ⟨openStateTwoDegThree S₃ g h2
        (hb g (List.mem_append_right _ (List.mem_singleton.mpr rfl)) h2)⟩


end Cslib.Circuits.Frontier
