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
    ((@FinEnum.equiv (Fin n) FinEnum.fin) v).1 = v.1 := by
  change ((List.finRange n).dedup).idxOf v = v.1
  rw [(List.nodup_finRange n).dedup, List.idxOf_finRange]

private theorem finEnum_equiv_symm_val {n : ℕ} (i : Fin (FinEnum.card (Fin n))) :
    ((@FinEnum.equiv (Fin n) FinEnum.fin).symm i).1 = i.1 := by
  have h := finEnum_equiv_val ((@FinEnum.equiv (Fin n) FinEnum.fin).symm i)
  simpa using h.symm

private theorem edmondsTableAux_congr_dim {n₁ n₂ : ℕ} (hn : n₁ = n₂)
    (r₁ : Fin n₁) (r₂ : Fin n₂) (hr : r₁.1 = r₂.1)
    (fuel : ℕ) (a₁ : AdjTable n₁) (a₂ : AdjTable n₂)
    (c₁ : CostTable ℤ n₁) (c₂ : CostTable ℤ n₂)
    (ha : ∀ i j, (hi₁ : i < n₁) → (hj₁ : j < n₁) → (hi₂ : i < n₂) → (hj₂ : j < n₂) →
      a₁[i][j] = a₂[i][j])
    (hc : ∀ i j, (hi₁ : i < n₁) → (hj₁ : j < n₁) → (hi₂ : i < n₂) → (hj₂ : j < n₂) →
      c₁[i][j] = c₂[i][j]) :
    (edmondsTableAux r₁ fuel a₁ c₁).map (fun p => (List.finRange n₁).map fun v => (p[v.1]).1) =
      (edmondsTableAux r₂ fuel a₂ c₂).map
        (fun p => (List.finRange n₂).map fun v => (p[v.1]).1) := by
  subst hn
  have hrr : r₁ = r₂ := Fin.ext hr
  subst hrr
  have ha_eq : a₁ = a₂ := Vector.ext fun i hi => Vector.ext fun j hj => ha i j hi hj hi hj
  have hc_eq : c₁ = c₂ := Vector.ext fun i hi => Vector.ext fun j hj => hc i j hi hj hi hj
  subst ha_eq hc_eq
  rfl

public theorem edmonds_fin_map_eq {n : ℕ} (G : Digraph (Fin n)) [DecidableRel G.Adj]
    (c : Fin n → Fin n → ℤ) (r : Fin n) :
    (edmonds G c r).map (fun f => (List.finRange n).map fun v => (f v).1) =
      (edmondsTableAux r n
        (initAdjTable n fun u w => decide (G.Adj u w))
        (initCostTable n c)).map
        (fun p => (List.finRange n).map fun v => (p[v.1]).1) := by
  rw [← edmondsTable_eq_edmonds]
  unfold edmondsTable
  rw [Option.map_map]
  let e : Fin n ≃ Fin (FinEnum.card (Fin n)) := @FinEnum.equiv (Fin n) FinEnum.fin
  have hcard : FinEnum.card (Fin n) = n := FinEnum.card_fin
  let A₁ := initAdjTable (FinEnum.card (Fin n)) fun u w => decide (G.Adj (e.symm u) (e.symm w))
  let C₁ := initCostTable (FinEnum.card (Fin n)) fun u w => c (e.symm u) (e.symm w)
  have hmap_fn : ∀ p : ParentTable (FinEnum.card (Fin n)),
      ((List.finRange n).map fun v => (e.symm p[(e v).1]).1) =
        ((List.finRange (FinEnum.card (Fin n))).map fun u => (p[u.1]).1) := fun p => by
    refine List.ext_getElem (by simp [hcard]) fun k hk₁ hk₂ => ?_
    simp only [List.getElem_map, List.getElem_finRange]
    have hk_n : k < n := by simpa using hk₁
    rw [finEnum_equiv_symm_val]
    have hek : (e ⟨k, hk_n⟩).1 = k := finEnum_equiv_val ⟨k, hk_n⟩
    simp [hek]
  have hfuel : edmondsTableAux (e r) (FinEnum.card (Fin n)) A₁ C₁ =
      edmondsTableAux (e r) n A₁ C₁ := congrArg (fun k => edmondsTableAux (e r) k A₁ C₁) hcard
  have step1 : Option.map (fun p => (List.finRange n).map fun v => (e.symm p[(e v).1]).1)
      (edmondsTableAux (e r) (FinEnum.card (Fin n)) A₁ C₁) =
      Option.map (fun p => (List.finRange (FinEnum.card (Fin n))).map fun u => (p[u.1]).1)
        (edmondsTableAux (e r) n A₁ C₁) := by
    rw [hfuel]
    exact congrArg (Option.map · _) (funext hmap_fn)
  refine step1.trans
    (edmondsTableAux_congr_dim hcard (e r) r (finEnum_equiv_val r) n A₁ _ C₁ _ ?_ ?_)
  · intro i j hi₁ hj₁ hi₂ hj₂
    have h1 : A₁[i][j] = decide (G.Adj (e.symm ⟨i, hi₁⟩) (e.symm ⟨j, hj₁⟩)) :=
      getElem_initAdjTable _ _ ⟨i, hi₁⟩ ⟨j, hj₁⟩
    have h2 : (initAdjTable n fun u w => decide (G.Adj u w))[i][j] =
        decide (G.Adj ⟨i, hi₂⟩ ⟨j, hj₂⟩) :=
      getElem_initAdjTable _ _ ⟨i, hi₂⟩ ⟨j, hj₂⟩
    have hu : e.symm ⟨i, hi₁⟩ = ⟨i, hi₂⟩ := Fin.ext (finEnum_equiv_symm_val ⟨i, hi₁⟩)
    have hw : e.symm ⟨j, hj₁⟩ = ⟨j, hj₂⟩ := Fin.ext (finEnum_equiv_symm_val ⟨j, hj₁⟩)
    rw [h1, h2, hu, hw]
  · intro i j hi₁ hj₁ hi₂ hj₂
    have h1 : C₁[i][j] = c (e.symm ⟨i, hi₁⟩) (e.symm ⟨j, hj₁⟩) :=
      getElem_initCostTable _ _ ⟨i, hi₁⟩ ⟨j, hj₁⟩
    have h2 : (initCostTable n c)[i][j] = c ⟨i, hi₂⟩ ⟨j, hj₂⟩ :=
      getElem_initCostTable _ _ ⟨i, hi₂⟩ ⟨j, hj₂⟩
    have hu : e.symm ⟨i, hi₁⟩ = ⟨i, hi₂⟩ := Fin.ext (finEnum_equiv_symm_val ⟨i, hi₁⟩)
    have hw : e.symm ⟨j, hj₁⟩ = ⟨j, hj₂⟩ := Fin.ext (finEnum_equiv_symm_val ⟨j, hj₁⟩)
    rw [h1, h2, hu, hw]

public theorem edmondsOut_fin_map_eq {n : ℕ} (G : Digraph (Fin n)) [DecidableRel G.Adj]
    (c : Fin n → Fin n → ℤ) (r : Fin n) :
    (edmondsOut G c r).map (fun f => (List.finRange n).map fun v => (f v).1) =
      (edmondsTableAux r n
        (initAdjTable n fun u w => decide (G.Adj w u))
        (initCostTable n fun u w => c w u)).map
        (fun p => (List.finRange n).map fun v => (p[v.1]).1) := by
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
    if hx : x.1 < n then
      if hy : y.1 < n then decide (G.Adj ⟨y.1, hy⟩ ⟨x.1, hx⟩)
      else true
    else false

/-- Negated reversed cost matrix of the `(n + 1)`-vertex super-root reduction digraph (`0` on
super-root arcs). -/
@[expose] public def superRootCostFin {n : ℕ} (wt : Fin n → Fin n → ℤ) : CostTable ℤ (n + 1) :=
  initCostTable (n + 1) fun x y =>
    if hx : x.1 < n then
      if hy : y.1 < n then -wt ⟨y.1, hy⟩ ⟨x.1, hx⟩
      else 0
    else 0

public theorem optimumBranchingParent_fin_eq {n : ℕ} (G : Digraph (Fin n)) [DecidableRel G.Adj]
    (wt : Fin n → Fin n → ℤ) :
    ∃ p : ParentTable (n + 1),
      edmondsTableAux (Fin.last n) (n + 1) (superRootAdjFin G) (superRootCostFin wt) = some p ∧
      ∀ v : Fin n, (optimumBranchingParent G wt v).1 =
        if (p[v.1]).1 < n then (p[v.1]).1 else v.1 := by
  let _ : FinEnum (Option (Fin n)) := optionFinEnum (Fin n)
  have hcard_fin : @FinEnum.card (Fin n) FinEnum.fin = n := FinEnum.card_fin
  have hcard_opt : FinEnum.card (Option (Fin n)) = n + 1 := by
    change @FinEnum.card (Fin n) FinEnum.fin + 1 = n + 1
    omega
  let eOpt : Option (Fin n) ≃ Fin (FinEnum.card (Option (Fin n))) := FinEnum.equiv
  have he_none : (eOpt none).1 = n := hcard_fin
  have he_some (v : Fin n) : (eOpt (some v)).1 = v.1 := finEnum_equiv_val v
  have hsymm_lt (i : Fin (FinEnum.card (Option (Fin n)))) (hi : i.1 < n) :
      eOpt.symm i = some ⟨i.1, hi⟩ := by
    apply eOpt.injective
    rw [Equiv.apply_symm_apply]
    exact Fin.ext (he_some ⟨i.1, hi⟩).symm
  have hsymm_eq (i : Fin (FinEnum.card (Option (Fin n)))) (hi : ¬i.1 < n) :
      eOpt.symm i = none := by
    have hin : i.1 = n := by have := i.isLt; omega
    apply eOpt.injective
    rw [Equiv.apply_symm_apply]
    exact Fin.ext (hin.trans he_none.symm)
  obtain ⟨pOpt, hpOpt⟩ := edmonds_superRootDigraph_isSome G wt
  have hparent_eq : optimumBranchingParent G wt = restrictParent pOpt := by
    simp [optimumBranchingParent, hpOpt]
  have htab_eq := edmondsTable_eq_edmonds G.superRootDigraph (superRootCost wt) none
  rw [hpOpt] at htab_eq
  unfold edmondsTable at htab_eq
  change Option.map (fun p v => eOpt.symm p[(eOpt v).1])
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
        have h1 : A₁[i][j] =
            decide (G.superRootDigraph.Adj (eOpt.symm ⟨i, hi₁⟩) (eOpt.symm ⟨j, hj₁⟩)) :=
          getElem_initAdjTable _ _ ⟨i, hi₁⟩ ⟨j, hj₁⟩
        have h2 : (superRootAdjFin G)[i][j] =
            if hx : i < n then if hy : j < n then decide (G.Adj ⟨j, hy⟩ ⟨i, hx⟩) else true
            else false :=
          getElem_initAdjTable _ _ ⟨i, hi₂⟩ ⟨j, hj₂⟩
        rw [h1, h2]
        by_cases hi : i < n
        · rw [hsymm_lt ⟨i, hi₁⟩ hi]
          by_cases hj : j < n
          · rw [hsymm_lt ⟨j, hj₁⟩ hj]; simp [hi, hj]
          · rw [hsymm_eq ⟨j, hj₁⟩ hj]; simp [hi, hj]
        · rw [hsymm_eq ⟨i, hi₁⟩ hi]; simp [hi])
      (fun i j hi₁ hj₁ hi₂ hj₂ => by
        have h1 : C₁[i][j] = superRootCost wt (eOpt.symm ⟨i, hi₁⟩) (eOpt.symm ⟨j, hj₁⟩) :=
          getElem_initCostTable _ _ ⟨i, hi₁⟩ ⟨j, hj₁⟩
        have h2 : (superRootCostFin wt)[i][j] =
            if hx : i < n then if hy : j < n then -wt ⟨j, hy⟩ ⟨i, hx⟩ else 0 else 0 :=
          getElem_initCostTable _ _ ⟨i, hi₂⟩ ⟨j, hj₂⟩
        rw [h1, h2]
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
      have hv_eq : (p1[v.1]'(by omega)).1 = (p2[v.1]'(by omega)).1 := by
        have hget := congrArg (fun l => l.getD v.1 0) hcongr
        have hl1 : v.1 < ((List.finRange (FinEnum.card (Option (Fin n)))).map
            fun u => (p1[u.1]).1).length := by simp [hcard_opt]
        have hl2 : v.1 < ((List.finRange (n + 1)).map fun u => (p2[u.1]).1).length := by simp
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl1, Option.getD_some,
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl2, Option.getD_some] at hget
        simpa using hget
      have hp_v : pOpt (some v) = eOpt.symm (p1[(eOpt (some v)).1]) :=
        (congrFun htab_eq (some v)).symm
      rw [hparent_eq]
      unfold restrictParent
      rw [hp_v]
      have hev : (eOpt (some v)).1 = v.1 := he_some v
      have hp1_eq : p1[(eOpt (some v)).1] = p1[v.1]'(by omega) := by simp [hev]
      rw [hp1_eq]
      by_cases hlt : (p2[v.1]'(by omega)).1 < n
      · have hlt1 : (p1[v.1]'(by omega)).1 < n := hv_eq ▸ hlt
        rw [hsymm_lt _ hlt1]
        simp [hlt, hv_eq]
      · have hlt1 : ¬(p1[v.1]'(by omega)).1 < n := hv_eq ▸ hlt
        rw [hsymm_eq _ hlt1]
        simp [hlt]

end Cslib.Algorithms.WordRAM.Arborescence.Internal
