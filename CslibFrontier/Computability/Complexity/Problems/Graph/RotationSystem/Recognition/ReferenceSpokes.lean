/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.ReferenceStar
import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.SplitOrder
import CslibFrontier.Foundations.Geometry.Polygonal.AnnularSpokes
import Mathlib.Data.List.Nodup

/-!
# Prescribed reference spokes at the subdivision cut ports

At a vertex whose prescribed rotation is realized by an embedding, the actual cut ports
can be reached by simple routes starting along the reference rays. The routes are indexed by
the original incident darts, including both ends of a loop. Their outer disk and contact laws
allow the retained subdivision pieces to use the same cut ports. This is original geometry.
-/

public section

namespace Cslib.Complexity.Graph.RotationRecognition

open Cslib.Polygonal

/-- Install the reference rays inside a prescribed vertex's cut disk, reaching each
original dart's actual cut port. Spokes share only the center, remain in the open disk
up to their respective ports, and have positive multiples of the corresponding reference
germs. An empty prescribed word gives the empty family. -/
theorem exists_reference_spokes_at_cutPorts {I : FixedRotationInput} (hI : Valid I)
    {D : PolygonalDrawing I.graph} (hD : D.IsEmbedding)
    {r : RotationSystem I.graph} (hReal : D.Realizes r) (hfixed : Realizes I r)
    {ρ : ℝ} (hρ : 0 < ρ) {v : ℕ} {word : List ℕ} (hw : I.orders.getD v none = some word) :
    ∃ T : {d : Dart I.graph // d.vertex = v} → Route,
      (∀ d, (T d).start = D.vertex v ∧ (T d).finish = D.cutPort ρ d.val ∧
        (∃ a > (0 : ℝ), (T d).germ false =
          a • (referenceDrawing I).germ (subdivisionDart I d.val)) ∧
        (T d).IsSimple ∧ (T d).support \ Metric.ball (D.vertex v) ρ = {D.cutPort ρ d.val}) ∧
      Pairwise (fun d e => (T d).support ∩ (T e).support = {D.vertex v}) := by
  let Fiber := {d : Dart I.graph // d.vertex = v}
  have hword (d : Fiber) : d.val.index ∈ word :=
    ((hI.2.2.2 v word hw).2 _).mpr (mem_fiber.mpr
      ⟨((Dart.indexEquiv I.graph) d.val).isLt, (Dart.vertex_index d.val).trans d.property⟩)
  cases hlen : word.length with
  | zero =>
    have hnone (d : Fiber) : False := by simpa [List.length_eq_zero_iff.mp hlen] using hword d
    exact ⟨fun d => (hnone d).elim, fun d => (hnone d).elim, fun {d} _ _ => (hnone d).elim⟩
  | succ n =>
    let code (i : Fin (n + 1)) := word[i.val]'(by omega)
    have hmem (i : Fin (n + 1)) : code i ∈ word := List.getElem_mem _
    let idx (i : Fin (n + 1)) : Fin (2 * I.graph.edges.length) :=
      ⟨code i, (mem_fiber.mp (((hI.2.2.2 v word hw).2 _).mp (hmem i))).1⟩
    let d (i : Fin (n + 1)) : Dart I.graph := (Dart.indexEquiv I.graph).symm (idx i)
    have hindex (i : Fin (n + 1)) : (d i).index = code i :=
      congrArg Fin.val ((Dart.indexEquiv I.graph).apply_symm_apply (idx i))
    have hdmem (i : Fin (n + 1)) : (d i).index ∈ word := (hindex i).symm ▸ hmem i
    have hdv (i : Fin (n + 1)) : (d i).vertex = v := fixedWord_dart_vertex hI hw (hdmem i)
    have hrank (i : Fin (n + 1)) : word.idxOf (d i).index = i.val := by
      rw [hindex]
      exact (hI.2.2.2 v word hw).1.idxOf_getElem _ (by omega)
    have hdinj : Function.Injective d := fun i j heq =>
      Fin.ext (by rw [← hrank i, ← hrank j, heq])
    let w (i : Fin (n + 1)) := (referenceDrawing I).germ (subdivisionDart I (d i))
    let a (i : Fin (n + 1)) : ℝ := (ρ / 2) / ‖w i‖
    let p (i : Fin (n + 1)) := D.vertex v + a i • w i
    let q (i : Fin (n + 1)) := D.cutPort ρ (d i)
    have hwpos (i : Fin (n + 1)) : 0 < ‖w i‖ := norm_pos_iff.mpr
      (referenceDrawing_subdivisionDart_germ_ne_zero hI (d i))
    have hapos (i : Fin (n + 1)) : 0 < a i := div_pos (half_pos hρ) (hwpos i)
    have hp (i : Fin (n + 1)) : ‖p i - D.vertex v‖ = ρ / 2 := by
      dsimp only [p]
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (hapos i).le]
      exact div_mul_cancel₀ _ (hwpos i).ne'
    have hq (i : Fin (n + 1)) : ‖q i - D.vertex v‖ = ρ := by
      simpa only [q, hdv, dist_eq_norm] using hD.dist_cutPort hρ.le (d i)
    have hpdir (i : Fin (n + 1)) :
        ((p i - D.vertex v).arg : Real.Angle) =
          (referenceDrawing I).direction (subdivisionDart I (d i)) := by
      simp only [p, add_sub_cancel_left, Complex.real_smul, Complex.arg_ofReal_mul (hapos i) _,
        PolygonalDrawing.direction, w]
    have hpinj : Function.Injective (fun i => ((p i - D.vertex v).arg : Real.Angle)) :=
      fun i j heq => hdinj (referenceDrawing_fixedWord_directions_injective hI hw (hdmem i)
        (hdmem j) (by simpa only [hpdir] using heq))
    have hqinj : Function.Injective (fun i => ((q i - D.vertex v).arg : Real.Angle)) :=
      fun i j heq => hdinj (hD.cutPort_direction_injective v hρ (Metric.mem_ball_self hρ)
        (d i) (d j) (hdv i) (hdv j) heq)
    have horder (i j : Fin (n + 1)) (hi : i ≠ Fin.last n) (hj : j ≠ Fin.last n)
        (hij : i ≠ j) :
        sbtw ((referenceDrawing I).direction (subdivisionDart I (d (Fin.last n))))
          ((referenceDrawing I).direction (subdivisionDart I (d i)))
          ((referenceDrawing I).direction (subdivisionDart I (d j))) ↔ j.val < i.val := by
      have hi' : i.val ≠ n := fun h => hi (Fin.ext h)
      have hj' : j.val ≠ n := fun h => hj (Fin.ext h)
      rw [referenceDrawing_fixedWord_clockwise_iff hI hw (hdmem j) (hdmem i)
        (hdmem (Fin.last n)) (hdinj.ne hij.symm) (hdinj.ne hi) (hdinj.ne hj)]
      simp only [hrank, Fin.val_last]; omega
    obtain ⟨T, hT, hpair⟩ := exists_annular_spokes n (D.vertex v) (half_pos hρ)
      (half_lt_self hρ) p q hp hq hpinj hqinj
      (fun i j hi hj hij => by simpa only [hpdir] using horder i j hi hj hij)
      (fun i j hi hj hij => (cutPort_clockwise_iff_reference hI hReal hfixed hρ hw
        (hdmem j) (hdmem i) (hdmem (Fin.last n))
        (hdinj.ne hij.symm) (hdinj.ne hi) (hdinj.ne hj)).trans (horder i j hi hj hij))
    let rank (a : Fiber) : Fin (n + 1) :=
      ⟨word.idxOf a.val.index, by have := List.idxOf_lt_length_of_mem (hword a); omega⟩
    have hback (a : Fiber) : d (rank a) = a.val :=
      (Dart.indexEquiv I.graph).injective (Fin.ext ((hindex (rank a)).trans
        (List.getElem_idxOf (List.idxOf_lt_length_of_mem (hword a)))))
    have hrank_inj : Function.Injective rank := fun a b he =>
      Subtype.ext ((hback a).symm.trans ((congrArg d he).trans (hback b)))
    refine ⟨fun a => T (rank a), fun a' => ?_, fun _ _ h => hpair (hrank_inj.ne h)⟩
    obtain ⟨hstart, hfinish, hgerm, hsimple, hbound⟩ := hT (rank a')
    exact ⟨hstart, by simpa only [q, hback] using hfinish,
      ⟨a (rank a'), hapos _, by simpa only [p, add_sub_cancel_left, w, hback] using hgerm⟩,
      hsimple, by simpa only [q, hback] using hbound⟩

end Cslib.Complexity.Graph.RotationRecognition
