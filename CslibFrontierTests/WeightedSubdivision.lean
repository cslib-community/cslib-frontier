/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Algorithms.Reachability.MinIsolation.Subdivision
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Subdivision.HozaWeight

/-! Checked generator-to-scan transport and a native callback reading the actual source word. -/

set_option linter.privateModule false

namespace CslibFrontierTests.WeightedSubdivision

open Cslib Cslib.LayeredDigraph.Subdivision
open Turing Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInSpace
open Turing.QueryMachine.Subdivision

private def rectangle : LayeredDigraph (Fin 3 × Fin 2) where
  Adj a b := b.1.val = a.1.val + 1
  layer z := z.1.val
  layer_adj h := h

open Cslib.Reachability.Hoza Cslib.Code.JustesenFamily in
/-- The proved generator supplies an actual family of weights for which every subdivided
scan round has exactly one transcript, including the newly introduced chain vertices. -/
example : ∃ (seed : Fin (codeLength 2 2) → Bool) (C : ℕ),
    ∀ s k, ∃! w, DoubleCounting.Passes
      (graph rectangle (generatedWeight seed) (14 ^ C)).Adj (root (14 ^ C) s) k w := by
  obtain ⟨seed, hseed⟩ := exists_generatedWeight_isMinIsolating rectangle fun _ => rfl
  obtain ⟨C, hC⟩ := generatedWeight_polynomial
  refine ⟨seed, C, fun s k => ?_⟩
  apply existsUnique_passes_of_isMinIsolating (fun z => (hC 2 2 seed z).le) hseed

/-- The exact carrier bound charges the chain slots, not just the original vertices. -/
example (bound : ℕ) : Nat.card (Vertex (Fin 3 × Fin 2) bound) = 6 * (bound + 1) := by
  rw [card_vertex, Nat.card_prod, Nat.card_fin, Nat.card_fin]

/-- Offsets above the source weight are unreachable, so unused rectangular slots do not
silently contribute additional scan paths. -/
example (s : Fin 3 × Fin 2) :
    ¬ Nonempty (Path rectangle (fun _ => 0) 2 (root 2 s) ⟨s, 1⟩) := by
  rintro ⟨p⟩
  have h := offset_le p
  change 1 ≤ 0 at h
  omega

private def readFirst : QueryMachine (Option Bool) where
  init := none
  query _ := 0
  next p := some (p.2.getD false)
  emit _ := []
  halted := Option.isSome
  finish _ := []

private def q : Query Unit := ⟨(), 0, 1, 0, 0⟩

/-- The same fixed adapter distinguishes a present true input bit from end of input. -/
private theorem run_readFirst (w : List Bool) :
    (callback readFirst (fun _ : Query Unit => none) Query.fromLabel
      (fun t => t.getD false)).runFrom w (.inl (.inl q)) 3 =
        .inl (.inr (w[0]?.getD false)) := by
  have h := callback_runFrom readFirst (fun _ : Query Unit => none) Query.fromLabel
    (fun t => t.getD false) w q 1 (by
      intro i hi
      have hi0 : i = 0 := by omega
      subst i
      rfl) (by rfl)
  exact h

open Cslib.Code.JustesenFamily in
private noncomputable def rectangleCode (p : ℕ × ℕ) (i : ℕ) : Bool :=
  if hcol : p.2 < 2 then
    if hi : i < codeLength 2 2 then indexedCodewordMod ⟨p.2, hcol⟩ ⟨i, hi⟩ else false
  else false

open Cslib.Reachability.Hoza Cslib.Code.JustesenFamily in
-- For valid rectangle coordinates the request computes the original generator's weight.
example (seed : Fin (2 ^ codeLength 2 2)) (z : Fin 3 × Fin 2) :
    sourceWeight (fun _ => 2) id (fun _ => codeLength 2 2) rectangleCode
      ⟨seed.val, (finProdFinEquiv z).val, 0, 0, 0⟩ =
      generatedWeight ((BitString.equivFin _).symm seed) z := by
  refine sourceWeight_eq_generatedWeight (fun _ => 2) id (fun _ => codeLength 2 2)
    rectangleCode seed.val seed z 0 0 0 rfl rfl rfl ?_
  intro i
  simp [rectangleCode, z.2.isLt, i.isLt]

private def rankWeight : Query (ℕ × ℕ) → ℕ :=
  sourceWeight Prod.fst Prod.snd (fun _ => 1) (fun _ _ => false)

/-- The subdivision kernel accepts the native retained-rank source weight as its return
routine. This example uses a one-bit seed and a constant code-bit routine. -/
example :
    let enc := encCallback (encPair encNat encNat) (encOption encBool)
    ComputableInSpace
      (callback readFirst (fun _ : Query (ℕ × ℕ) => none) rankWeight
        (fun t => t.getD false)).next
      (QueryMachine.encStateRead enc) enc
      (fun p => (QueryMachine.encStateRead enc p).length) := by
  let encCtx := encPair encNat encNat
  have hw : ComputableInSpace rankWeight (encQuery encCtx) encNat
      (fun q => (encQuery encCtx q).length) :=
    sourceWeight_inSpace encCtx Prod.fst Prod.snd (fun _ => 1) (fun _ _ => false)
      (fst encNat encNat) (snd encNat encNat) (budget_const 1)
      (BigOLe.const 1 _) (budget_const false)
  have ha := budget_optionGetD false
    (budget_id (enc := encOption encBool) (.refl _))
  have hnext := budget_optionSome (budget_optionGetD false
    (snd (encOption encBool) (encOption encBool)))
  have hhalt := budget_optionIsSome (budget_id (enc := encOption encBool) (.refl _))
  exact (callback_parts_inSpace encCtx (encOption encBool) readFirst
    (fun _ => none) rankWeight (fun t => t.getD false)
    (budget_const none) hw ha (budget_const 0) hnext hhalt).2.1

private def inputGraph (w : List Bool) : LayeredDigraph (Fin 2) where
  Adj a b := a = 0 ∧ b = 1 ∧ w[0]?.getD false = true
  layer v := v.val
  layer_adj := by rintro a b ⟨rfl, rfl, _⟩; rfl

/-- Combine actual call execution and graph agreement, rather than just checking the
arithmetic kernel on an externally supplied answer bit. -/
example (w : List Bool) : ∃ b,
    (callback readFirst (fun _ : Query Unit => none) Query.fromLabel
      (fun t => t.getD false)).runFrom w (.inl (.inl q)) 3 = .inl (.inr b) ∧
    (b = true ↔ (graph (inputGraph w) Fin.val 1).Adj (root 1 0) (root 1 1)) := by
  refine ⟨w[0]?.getD false, run_readFirst w, ?_⟩
  exact edgeQuery_agrees (inputGraph w) Fin.valEmbedding Fin.val 1 () (root 1 0) (root 1 1)
    (w[0]?.getD false) (by simp [inputGraph])

private def noEdges : LayeredDigraph Unit where
  Adj _ _ := False
  layer _ := 0
  layer_adj h := h.elim

/-- An original empty path expands to the requested partial source chain, with no
spurious charge of the full departure weight. -/
example : @Quiver.Path.length _ (toQuiver noEdges (fun _ => 2) 2) _ _
    (pathEquiv (G := noEdges) (weight := fun _ => 2) (bound := 2) (fun _ => le_rfl)
      () ⟨(), 1⟩ (by decide) (@Quiver.Path.nil Unit noEdges.toQuiver ())) = 1 := by
  let _ := noEdges.toQuiver
  rw [length_pathEquiv, Quiver.Path.addWeightOfEPs_nil]
  rfl

private def via (i : Fin 2) : rectangle.Path (0, 0) (2, 0) :=
  (LayeredDigraph.Path.ofAdj (G := rectangle) (a := (0, 0)) (b := (1, i)) rfl).comp
    (LayeredDigraph.Path.ofAdj (G := rectangle) (a := (1, i)) (b := (2, 0)) rfl)

private def zeroRectangle : LayeredDigraph (Vertex (Fin 3 × Fin 2) 0) where
  Adj := (graph rectangle (fun _ => 0) 0).Adj
  layer v := rectangle.layer v.vertex
  layer_adj := by
    intro a b he
    rcases he with ⟨_, h, hle⟩ | ⟨_, _, h⟩
    · omega
    · exact rectangle.layer_adj h

/-- A tied diamond remains ambiguous with zero weights; the isolation premise cannot be
omitted from the shortest-path transport theorem. -/
private theorem tiedShortest :
    ¬ ∃! p : Path rectangle (fun _ => 0) 0 (root 0 (0, 0)) (root 0 (2, 0)),
    ∀ r : Path rectangle (fun _ => 0) 0 (root 0 (0, 0)) (root 0 (2, 0)),
      @Quiver.Path.length _ (toQuiver rectangle (fun _ => 0) 0) _ _ p ≤
        @Quiver.Path.length _ (toQuiver rectangle (fun _ => 0) 0) _ _ r := by
  let _ := toQuiver rectangle (fun _ => 0) 0
  let E := pathEquiv (G := rectangle) (weight := fun _ => 0) (bound := 0)
    (fun _ => le_rfl) (0, 0) (root 0 (2, 0)) (by decide)
  have hlen (p : Path rectangle (fun _ => 0) 0 (root 0 (0, 0)) (root 0 (2, 0))) :
      p.length = 2 := by
    have h := LayeredDigraph.Path.layer_end (G := zeroRectangle) p
    change 2 = 0 + p.length at h
    omega
  rintro ⟨p, _, huniq⟩
  have hmin (p : Path rectangle (fun _ => 0) 0 (root 0 (0, 0)) (root 0 (2, 0))) :
      ∀ r : Path rectangle (fun _ => 0) 0 (root 0 (0, 0)) (root 0 (2, 0)),
        p.length ≤ r.length := by intro r; rw [hlen p, hlen r]
  have h := E.injective ((huniq (E (via 0)) (hmin _)).trans (huniq (E (via 1)) (hmin _)).symm)
  have hv := congrArg LayeredDigraph.Path.vertices h
  change [(0, 0), (1, (0 : Fin 2)), (2, 0)] = [(0, 0), (1, (1 : Fin 2)), (2, 0)] at hv
  simp at hv

private def indices : Vertex (Fin 3 × Fin 2) 0 ≃ Fin ((3 * 2) * (0 + 1)) :=
  (equivProd _ _).trans ((Equiv.prodCongr finProdFinEquiv (Equiv.refl _)).trans finProdFinEquiv)

/-- A saturated scan with row-major IDs cannot report unique transcripts from every
original source of the tied rectangle. -/
example : ¬ ∀ s : Fin 3 × Fin 2, ∃! w, DoubleCounting.Passes
    (fun u v => (graph rectangle (fun _ => 0) 0).Adj (indices.symm u) (indices.symm v))
    (indices (root 0 s)) 5 w := by
  intro h
  have hiso := (isMinIsolating_iff_indexedPasses indices (fun _ => le_rfl)
    (by decide : Fintype.card (Fin ((3 * 2) * (0 + 1))) ≤ 5 + 1)).mpr h
  apply tiedShortest
  exact existsUnique_shortest_of_isMinIsolating (fun _ => le_rfl) hiso (0, 0) (root 0 (2, 0))
    ⟨expand (fun _ => le_rfl) (via 0)⟩

end CslibFrontierTests.WeightedSubdivision
