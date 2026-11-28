/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Arborescence.Branching
public import CslibFrontier.Algorithms.Lean.Arborescence.Table

/-!
# `FinEnum` index-bridge lemmas for Word-RAM Chu–Liu/Edmonds (internal)

Bridges connecting canonical `Fin n` `edmonds` / `edmondsOut` / `optimumBranchingParent`
solutions on finite graphs to materialized `Table` algorithms and explicit `n + 1` super-root
tables.
-/

namespace Cslib.Algorithms.WordRAM.Arborescence.Internal

open Cslib.Algorithms.Lean.Arborescence

/-! ### `FinEnum` bridges and flat input encodings -/

private theorem finEnum_equiv_val {n : ℕ} (v : Fin n) :
    ((@FinEnum.equiv (Fin n) FinEnum.fin) v).val = v.val := by
  change ((List.finRange n).dedup).idxOf v = v.val
  rw [(List.nodup_finRange n).dedup, List.idxOf_finRange]

private theorem finEnum_equiv_symm_val {n : ℕ} (i : Fin (FinEnum.card (Fin n))) :
    ((@FinEnum.equiv (Fin n) FinEnum.fin).symm i).val = i.val := by
  have h := finEnum_equiv_val ((@FinEnum.equiv (Fin n) FinEnum.fin).symm i)
  simpa using h.symm

private theorem edmondsTableAux_congr_dim {n₁ n₂ : ℕ} (hn : n₁ = n₂)
    (r₁ : Fin n₁) (r₂ : Fin n₂) (hr : r₁.val = r₂.val)
    (fuel : ℕ) (a₁ : AdjTable n₁) (a₂ : AdjTable n₂)
    (c₁ : CostTable ℤ n₁) (c₂ : CostTable ℤ n₂)
    (ha : ∀ i j, (hi₁ : i < n₁) → (hj₁ : j < n₁) → (hi₂ : i < n₂) → (hj₂ : j < n₂) →
      a₁[i][j] = a₂[i][j])
    (hc : ∀ i j, (hi₁ : i < n₁) → (hj₁ : j < n₁) → (hi₂ : i < n₂) → (hj₂ : j < n₂) →
      c₁[i][j] = c₂[i][j]) :
    (edmondsTableAux r₁ fuel a₁ c₁).map (fun p => (List.finRange n₁).map fun v => (p[v.val]).val) =
      (edmondsTableAux r₂ fuel a₂ c₂).map
        (fun p => (List.finRange n₂).map fun v => (p[v.val]).val) := by
  subst hn
  have hrr : r₁ = r₂ := Fin.ext hr
  subst hrr
  have ha_eq : a₁ = a₂ := Vector.ext fun i hi => Vector.ext fun j hj => ha i j hi hj hi hj
  have hc_eq : c₁ = c₂ := Vector.ext fun i hi => Vector.ext fun j hj => hc i j hi hj hi hj
  subst ha_eq hc_eq
  rfl

public theorem edmonds_fin_map_eq {n : ℕ} (G : Digraph (Fin n)) [DecidableRel G.Adj]
    (c : Fin n → Fin n → ℤ) (r : Fin n) :
    (edmonds G c r).map (fun f => (List.finRange n).map fun v => (f v).val) =
      (edmondsTableAux r n
        (initAdjTable n fun u w => decide (G.Adj u w))
        (initCostTable n c)).map
        (fun p => (List.finRange n).map fun v => (p[v.val]).val) := by
  rw [← edmondsTable_eq_edmonds]
  unfold edmondsTable
  rw [Option.map_map]
  let e : Fin n ≃ Fin (FinEnum.card (Fin n)) := @FinEnum.equiv (Fin n) FinEnum.fin
  have hcard : FinEnum.card (Fin n) = n := FinEnum.card_fin
  let A₁ := initAdjTable (FinEnum.card (Fin n)) fun u w => decide (G.Adj (e.symm u) (e.symm w))
  let C₁ := initCostTable (FinEnum.card (Fin n)) fun u w => c (e.symm u) (e.symm w)
  have hmap_fn : ∀ p : ParentTable (FinEnum.card (Fin n)),
      ((List.finRange n).map fun v => (e.symm p[(e v).val]).val) =
        ((List.finRange (FinEnum.card (Fin n))).map fun u => (p[u.val]).val) := fun p => by
    refine List.ext_getElem (by simp [hcard]) fun k hk₁ hk₂ => ?_
    simp only [List.getElem_map, List.getElem_finRange]
    have hk_n : k < n := by simpa using hk₁
    rw [finEnum_equiv_symm_val]
    have hek : (e ⟨k, hk_n⟩).val = k := finEnum_equiv_val ⟨k, hk_n⟩
    simp [hek]
  have hfuel : edmondsTableAux (e r) (FinEnum.card (Fin n)) A₁ C₁ =
      edmondsTableAux (e r) n A₁ C₁ := congrArg (fun k => edmondsTableAux (e r) k A₁ C₁) hcard
  have step1 : Option.map (fun p => (List.finRange n).map fun v => (e.symm p[(e v).val]).val)
      (edmondsTableAux (e r) (FinEnum.card (Fin n)) A₁ C₁) =
      Option.map (fun p => (List.finRange (FinEnum.card (Fin n))).map fun u => (p[u.val]).val)
        (edmondsTableAux (e r) n A₁ C₁) := by
    rw [hfuel]
    exact congrArg (Option.map · _) (funext hmap_fn)
  have hsymm {i : ℕ} (h₁ : i < FinEnum.card (Fin n)) (h₂ : i < n) : e.symm ⟨i, h₁⟩ = ⟨i, h₂⟩ :=
    Fin.ext (finEnum_equiv_symm_val ⟨i, h₁⟩)
  refine step1.trans
    (edmondsTableAux_congr_dim hcard (e r) r (finEnum_equiv_val r) n A₁ _ C₁ _ ?_ ?_)
  · intro i j hi₁ hj₁ hi₂ hj₂
    refine (getElem_initAdjTable _ _ ⟨i, hi₁⟩ ⟨j, hj₁⟩).trans
      (Eq.trans ?_ (getElem_initAdjTable _ _ ⟨i, hi₂⟩ ⟨j, hj₂⟩).symm)
    rw [hsymm hi₁ hi₂, hsymm hj₁ hj₂]
  · intro i j hi₁ hj₁ hi₂ hj₂
    refine (getElem_initCostTable _ _ ⟨i, hi₁⟩ ⟨j, hj₁⟩).trans
      (Eq.trans ?_ (getElem_initCostTable _ _ ⟨i, hi₂⟩ ⟨j, hj₂⟩).symm)
    rw [hsymm hi₁ hi₂, hsymm hj₁ hj₂]

public theorem edmondsOut_fin_map_eq {n : ℕ} (G : Digraph (Fin n)) [DecidableRel G.Adj]
    (c : Fin n → Fin n → ℤ) (r : Fin n) :
    (edmondsOut G c r).map (fun f => (List.finRange n).map fun v => (f v).val) =
      (edmondsTableAux r n
        (initAdjTable n fun u w => decide (G.Adj w u))
        (initCostTable n fun u w => c w u)).map
        (fun p => (List.finRange n).map fun v => (p[v.val]).val) := by
  have hout : edmondsOut G c r = edmonds G.reverse (fun u w => c w u) r := by
    rw [← edmondsOutTable_eq_edmondsOut, ← edmondsTable_eq_edmonds]
    rfl
  rw [hout]
  exact edmonds_fin_map_eq G.reverse (fun u w => c w u) r

/-- Adjacency matrix of the `(n + 1)`-vertex super-root reduction digraph (reversed arcs plus
arcs from every `x < n` to super-root `n`). -/
@[expose] public def superRootAdjFin {n : ℕ} (G : Digraph (Fin n)) [DecidableRel G.Adj] :
    AdjTable (n + 1) :=
  initAdjTable (n + 1) fun x y =>
    if hx : x.val < n then
      if hy : y.val < n then decide (G.Adj ⟨y.val, hy⟩ ⟨x.val, hx⟩)
      else true
    else false

/-- Negated reversed cost matrix of the `(n + 1)`-vertex super-root reduction digraph (`0` on
super-root arcs). -/
@[expose] public def superRootCostFin {n : ℕ} (wt : Fin n → Fin n → ℤ) : CostTable ℤ (n + 1) :=
  initCostTable (n + 1) fun x y =>
    if hx : x.val < n then
      if hy : y.val < n then -wt ⟨y.val, hy⟩ ⟨x.val, hx⟩
      else 0
    else 0

public theorem optimumBranchingParent_fin_eq {n : ℕ} (G : Digraph (Fin n)) [DecidableRel G.Adj]
    (wt : Fin n → Fin n → ℤ) :
    ∃ p : ParentTable (n + 1),
      edmondsTableAux (Fin.last n) (n + 1) (superRootAdjFin G) (superRootCostFin wt) = some p ∧
      ∀ v : Fin n, (optimumBranchingParent G wt v).val =
        if (p[v.val]).val < n then (p[v.val]).val else v.val := by
  let _ : FinEnum (Option (Fin n)) := optionFinEnum (Fin n)
  have hcard_fin : @FinEnum.card (Fin n) FinEnum.fin = n := FinEnum.card_fin
  have hcard_opt : FinEnum.card (Option (Fin n)) = n + 1 := by
    change @FinEnum.card (Fin n) FinEnum.fin + 1 = n + 1
    omega
  let eOpt : Option (Fin n) ≃ Fin (FinEnum.card (Option (Fin n))) := FinEnum.equiv
  have he_none : (eOpt none).val = n := hcard_fin
  have he_some (v : Fin n) : (eOpt (some v)).val = v.val := finEnum_equiv_val v
  have hsymm_lt (i : Fin (FinEnum.card (Option (Fin n)))) (hi : i.val < n) :
      eOpt.symm i = some ⟨i.val, hi⟩ := by
    apply eOpt.injective
    rw [Equiv.apply_symm_apply]
    exact Fin.ext (he_some ⟨i.val, hi⟩).symm
  have hsymm_eq (i : Fin (FinEnum.card (Option (Fin n)))) (hi : ¬i.val < n) :
      eOpt.symm i = none := by
    have hin : i.val = n := by have := i.isLt; omega
    apply eOpt.injective
    rw [Equiv.apply_symm_apply]
    exact Fin.ext (hin.trans he_none.symm)
  obtain ⟨pOpt, hpOpt⟩ := edmonds_superRootDigraph_isSome G wt
  have hparent_eq : optimumBranchingParent G wt = restrictParent pOpt := by
    simp [optimumBranchingParent, hpOpt]
  have htab_eq := edmondsTable_eq_edmonds G.superRootDigraph (superRootCost wt) none
  rw [hpOpt] at htab_eq
  unfold edmondsTable at htab_eq
  change Option.map (fun p v => eOpt.symm p[(eOpt v).val])
    (edmondsTableAux (eOpt none) (FinEnum.card (Option (Fin n)))
      (initAdjTable (FinEnum.card (Option (Fin n))) fun u w =>
        decide (G.superRootDigraph.Adj (eOpt.symm u) (eOpt.symm w)))
      (initCostTable (FinEnum.card (Option (Fin n))) fun u w =>
        superRootCost wt (eOpt.symm u) (eOpt.symm w))) = some pOpt at htab_eq
  cases haux1 : edmondsTableAux (eOpt none) (FinEnum.card (Option (Fin n)))
      (initAdjTable (FinEnum.card (Option (Fin n))) fun u w =>
        decide (G.superRootDigraph.Adj (eOpt.symm u) (eOpt.symm w)))
      (initCostTable (FinEnum.card (Option (Fin n))) fun u w =>
        superRootCost wt (eOpt.symm u) (eOpt.symm w)) with
  | none =>
    rw [haux1] at htab_eq
    cases htab_eq
  | some p1 =>
    rw [haux1, Option.map_some, Option.some.injEq] at htab_eq
    let A₁ := initAdjTable (FinEnum.card (Option (Fin n))) fun u w =>
      decide (G.superRootDigraph.Adj (eOpt.symm u) (eOpt.symm w))
    let C₁ := initCostTable (FinEnum.card (Option (Fin n))) fun u w =>
      superRootCost wt (eOpt.symm u) (eOpt.symm w)
    have hcongr := edmondsTableAux_congr_dim hcard_opt (eOpt none) (Fin.last n) he_none (n + 1)
      A₁ (superRootAdjFin G) C₁ (superRootCostFin wt)
      (fun i j hi₁ hj₁ hi₂ hj₂ => by
        refine (getElem_initAdjTable _ _ ⟨i, hi₁⟩ ⟨j, hj₁⟩).trans
          (Eq.trans ?_ (getElem_initAdjTable _ _ ⟨i, hi₂⟩ ⟨j, hj₂⟩).symm)
        by_cases hi : i < n
        · rw [hsymm_lt ⟨i, hi₁⟩ hi]
          by_cases hj : j < n
          · rw [hsymm_lt ⟨j, hj₁⟩ hj]; simp [hi, hj]
          · rw [hsymm_eq ⟨j, hj₁⟩ hj]; simp [hi, hj]
        · rw [hsymm_eq ⟨i, hi₁⟩ hi]; simp [hi])
      (fun i j hi₁ hj₁ hi₂ hj₂ => by
        refine (getElem_initCostTable _ _ ⟨i, hi₁⟩ ⟨j, hj₁⟩).trans
          (Eq.trans ?_ (getElem_initCostTable _ _ ⟨i, hi₂⟩ ⟨j, hj₂⟩).symm)
        by_cases hi : i < n
        · rw [hsymm_lt ⟨i, hi₁⟩ hi]
          by_cases hj : j < n
          · rw [hsymm_lt ⟨j, hj₁⟩ hj]; simp [hi, hj, superRootCost]
          · rw [hsymm_eq ⟨j, hj₁⟩ hj]; simp [hi, hj, superRootCost]
        · rw [hsymm_eq ⟨i, hi₁⟩ hi]; simp [hi, superRootCost])
    have haux1' : edmondsTableAux (eOpt none) (n + 1) A₁ C₁ = some p1 := by
      rw [← hcard_opt]
      exact haux1
    rw [haux1', Option.map_some] at hcongr
    cases haux2 : edmondsTableAux (Fin.last n) (n + 1) (superRootAdjFin G) (superRootCostFin wt)
    with
    | none => simp [haux2] at hcongr
    | some p2 =>
      simp only [haux2, Option.map_some, Option.some.injEq] at hcongr
      refine ⟨p2, rfl, fun v => ?_⟩
      have hv_eq : (p1[v.val]'(by omega)).val = (p2[v.val]'(by omega)).val := by
        have hget := congrArg (fun l => l.getD v.val 0) hcongr
        have hl1 : v.val < ((List.finRange (FinEnum.card (Option (Fin n)))).map
            fun u => (p1[u.val]).val).length := by simp [hcard_opt]
        have hl2 : v.val < ((List.finRange (n + 1)).map fun u => (p2[u.val]).val).length := by simp
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl1, Option.getD_some,
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl2, Option.getD_some] at hget
        simpa using hget
      have hp_v : pOpt (some v) = eOpt.symm (p1[(eOpt (some v)).val]) :=
        (congrFun htab_eq (some v)).symm
      rw [hparent_eq]
      unfold restrictParent
      rw [hp_v]
      have hev : (eOpt (some v)).val = v.val := he_some v
      have hp1_eq : p1[(eOpt (some v)).val] = p1[v.val]'(by omega) := by simp [hev]
      rw [hp1_eq]
      by_cases hlt : (p2[v.val]'(by omega)).val < n
      · have hlt1 : (p1[v.val]'(by omega)).val < n := hv_eq ▸ hlt
        rw [hsymm_lt _ hlt1]
        simp [hlt, hv_eq]
      · have hlt1 : ¬(p1[v.val]'(by omega)).val < n := hv_eq ▸ hlt
        rw [hsymm_eq _ hlt1]
        simp [hlt]

end Cslib.Algorithms.WordRAM.Arborescence.Internal
