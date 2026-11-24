/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polygonal.Route
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.AffineSpace.Ordered
import Mathlib.Order.Fin.Basic
import CslibFrontier.Foundations.Geometry.Polygonal.SegmentOrder

/-!
# Real coordinate order on polygonal routes

Strictly increasing real coordinates of the listed nodes order the entire continuous
route by its existing chain position. Adjacent descriptions of a shared knot have equal
positions and coordinates. Parameters must belong to the closed unit interval.

## Main results

* `Cslib.Polygonal.Route.eval_re_lt_iff_position_lt_of_strictMono`: actual evaluation
  coordinates have exactly the strict order of their chain positions.
* `Cslib.Polygonal.Route.isSimple_of_strictMono_re`: strict real node order implies simplicity.

This original geometric criterion supports simplicity proofs for future ordered local
patch assembly. It is sufficient, not necessary: closed routes and routes with vertical
segments need not satisfy the premise. A route always has at least one segment.
Global assembly/contact/parity and the HT/query/source objectives remain open under
[#3091](https://github.com/cslib-community/cslib-frontier/issues/3091).
-/

public section

namespace Cslib.Polygonal.Route

private theorem eval_re (p : Route) (i : Fin p.segments) (t : ℝ) :
    (p.eval i t).re = AffineMap.lineMap (p.point i.castSucc).re (p.point i.succ).re t := by
  change Complex.reCLM.toLinearMap.toAffineMap
    (AffineMap.lineMap (p.point i.castSucc) (p.point i.succ) t) = _
  exact AffineMap.apply_lineMap _ _ _ _

private theorem strictMonoOn_eval_re {p : Route}
    (h : StrictMono fun k => (p.point k).re) (i : Fin p.segments) :
    StrictMonoOn (fun t => (p.eval i t).re) (Set.Icc 0 1) := by
  intro s _ t _ hst
  change (p.eval i s).re < (p.eval i t).re
  rw [eval_re, eval_re]
  exact (lineMap_lt_lineMap_iff_of_lt' ((Fin.strictMono_iff_lt_succ.mp h) i)).mpr hst

/-- Strict node real-coordinate order agrees with actual continuum chain-position order.
Both local parameters are restricted to `[0,1]`, including adjacent knot descriptions. -/
theorem eval_re_lt_iff_position_lt_of_strictMono (p : Route)
    (h : StrictMono fun k : Fin (p.bends + 2) => (p.point k).re)
    (i j : Fin p.segments) (s t : ℝ) (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1) :
    (p.eval i s).re < (p.eval j t).re ↔ p.position i s < p.position j t :=
  p.eval_lt_iff_position_lt_of_strictMonoOn Complex.re (strictMonoOn_eval_re h) i j s t hs ht

/-- Strictly increasing real node coordinates imply simplicity on the closed parameter intervals. -/
theorem isSimple_of_strictMono_re {p : Route}
    (h : StrictMono fun k => (p.point k).re) : p.IsSimple :=
  isSimple_of_strictMonoOn_eval Complex.re (strictMonoOn_eval_re h)

end Cslib.Polygonal.Route
