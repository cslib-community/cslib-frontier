/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.GridDrawing.Basic

/-!
# Reindexing orthogonal drawings

Exact port incidence equivalences transport the same vertex positions and paths to new names.

## Main definitions

* `Cslib.Complexity.NCL.GridDrawing.Open.reindex`: rename vertices, edges and boundary wires.
* `Cslib.Complexity.NCL.GridDrawing.Closed.reindex`: rename a closed graph drawing.

## Main results

Reindexing preserves actual finite paths and every nonintersection condition.
-/

public section

namespace Cslib.Complexity.NCL.GridDrawing

open GridRouting Diagram

variable {V E V' E' : Type*} {G : ConstraintGraph V E} {G' : ConstraintGraph V' E'}
  {m n : ℕ} {top : Fin m → E} {bottom : Fin n → E}

/-- Rename an open drawing using an exact equivalence of port incidences. -/
@[expose] noncomputable def Open.reindex (P : Open G top bottom) (σ : V' ≃ V) (τ : E' ≃ E)
    (hp : ∀ v e d, HasPort G' v e d ↔ HasPort G (σ v) (τ e) d)
    (top' : Fin m → E') (bottom' : Fin n → E')
    (ht : ∀ i, τ (top' i) = top i) (hb : ∀ j, τ (bottom' j) = bottom j) :
    Open G' top' bottom' where
  height := P.height
  height_pos := P.height_pos
  vertex := P.vertex ∘ σ
  vertex_injective := P.vertex_injective.comp σ.injective
  vertex_rows v := P.vertex_rows (σ v)
  vertex_separation v w h := P.vertex_separation _ _ (σ.injective.ne h)
  source := P.source ∘ τ
  target := P.target ∘ τ
  trace e := P.trace (τ e)
  edge_rows e := P.edge_rows (τ e)
  path e := P.path (τ e)
  row_le e := P.row_le (τ e)
  top_iff e x := by
    rw [P.top_iff]
    exact ⟨fun ⟨i, hi, hx⟩ => ⟨i, τ.injective ((ht i).trans hi), hx⟩,
      fun ⟨i, hi, hx⟩ => ⟨i, (ht i).symm.trans (congrArg τ hi), hx⟩⟩
  bottom_iff e x := by
    rw [P.bottom_iff]
    exact ⟨fun ⟨i, hi, hx⟩ => ⟨i, τ.injective ((hb i).trans hi), hx⟩,
      fun ⟨i, hi, hx⟩ => ⟨i, (hb i).symm.trans (congrArg τ hi), hx⟩⟩
  source_top i := by rw [Function.comp_apply, ht, P.source_top]
  target_bottom j := by rw [Function.comp_apply, hb, P.target_bottom]
  source_spec e := by
    rcases P.source_spec (τ e) with ⟨i, hi⟩ | ⟨v, hv, he⟩
    · exact .inl ⟨i, τ.injective ((ht i).trans hi)⟩
    · exact .inr ⟨σ.symm v, (hp _ _ _).2 (by simpa only [Equiv.apply_symm_apply] using hv),
        by simpa only [Function.comp_apply, Equiv.apply_symm_apply] using he⟩
  target_spec e := by
    rcases P.target_spec (τ e) with ⟨j, hj⟩ | ⟨v, hv, he⟩
    · exact .inl ⟨j, τ.injective ((hb j).trans hj)⟩
    · exact .inr ⟨σ.symm v, (hp _ _ _).2 (by simpa only [Equiv.apply_symm_apply] using hv),
        by simpa only [Function.comp_apply, Equiv.apply_symm_apply] using he⟩
  source_port v e h := P.source_port _ _ ((hp _ _ _).1 h)
  target_port v e h := P.target_port _ _ ((hp _ _ _).1 h)
  vertex_meet e v h := by
    obtain ⟨d, hd⟩ := P.vertex_meet _ _ h
    exact ⟨d, (hp _ _ _).2 hd⟩
  meet e f p h h₁ h₂ := by
    obtain ⟨v, hv, ⟨de, he⟩, ⟨df, hf⟩⟩ := P.meet _ _ p (τ.injective.ne h) h₁ h₂
    exact ⟨σ.symm v, by simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hv,
      ⟨de, (hp _ _ _).2 (by simpa only [Equiv.apply_symm_apply] using he)⟩,
      ⟨df, (hp _ _ _).2 (by simpa only [Equiv.apply_symm_apply] using hf)⟩⟩

/-- Change the finite boundary bounds by their exact length equalities. -/
@[expose] def Open.castBoundary (P : Open G top bottom) {m' n' : ℕ} (hm : m' = m) (hn : n' = n) :
    Open G (fun i : Fin m' => top (i.cast hm)) (fun j : Fin n' => bottom (j.cast hn)) := by
  subst m' n'
  exact P

/-- Rename a closed drawing while preserving its exact endpoint port incidences. -/
@[expose] noncomputable def Closed.reindex (P : Closed G) (σ : V' ≃ V) (τ : E' ≃ E)
    (hp : ∀ v e d, HasPort G' v e d ↔ HasPort G (σ v) (τ e) d) : Closed G' := by
  classical
  let path e : Path (P.vertex (σ (σ.symm (P.source (τ e)))))
      (P.vertex (σ (σ.symm (P.target (τ e))))) :=
    (P.path (τ e)).cast (by rw [Equiv.apply_symm_apply]) (by rw [Equiv.apply_symm_apply])
  have hpath (e p) : (path e).Contains p ↔ (P.path (τ e)).Contains p :=
    Path.contains_cast_iff _ _ _ _
  refine
    { vertex := P.vertex ∘ σ
      vertex_injective := P.vertex_injective.comp σ.injective
      vertex_separation v w h := P.vertex_separation _ _ (σ.injective.ne h)
      source e := σ.symm (P.source (τ e))
      target e := σ.symm (P.target (τ e))
      source_port e := (hp _ _ _).2
        (by simpa only [Equiv.apply_symm_apply] using P.source_port (τ e))
      target_port e := (hp _ _ _).2
        (by simpa only [Equiv.apply_symm_apply] using P.target_port (τ e))
      edge_rows e := by
        simpa only [Function.comp_apply, Equiv.apply_symm_apply] using P.edge_rows (τ e)
      path := path
      source_eq := ?_
      target_eq := ?_
      vertex_meet := ?_
      meet := ?_ }
  · intro v e h
    simpa only [Equiv.symm_apply_apply] using
      congrArg σ.symm (P.source_eq _ _ ((hp _ _ _).1 h))
  · intro v e h
    simpa only [Equiv.symm_apply_apply] using
      congrArg σ.symm (P.target_eq _ _ ((hp _ _ _).1 h))
  · intro e v h
    obtain ⟨d, hd⟩ := P.vertex_meet _ _ ((hpath _ _).1 h)
    exact ⟨d, (hp _ _ _).2 hd⟩
  · intro e f p h h₁ h₂
    obtain ⟨v, hv, ⟨de, he⟩, ⟨df, hf⟩⟩ :=
      P.meet _ _ p (τ.injective.ne h) ((hpath _ _).1 h₁) ((hpath _ _).1 h₂)
    exact ⟨σ.symm v, by simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hv,
      ⟨de, (hp _ _ _).2 (by simpa only [Equiv.apply_symm_apply] using he)⟩,
      ⟨df, (hp _ _ _).2 (by simpa only [Equiv.apply_symm_apply] using hf)⟩⟩

end Cslib.Complexity.NCL.GridDrawing
