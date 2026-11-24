/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.Bounded
public import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.Reduction
public import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.Hardness
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Bandwidth
import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Word.CompilePolyTime
import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.BandwidthPSPACE

/-!
# PSPACE-complete planar AND/OR reachability with a fixed bandwidth

Compile the fixed-H word instance into its actual numbered planar graph and endpoint bits.
The constructed row order certifies a bandwidth bound depending only on the fixed alphabet.
The output uses the general graph encoding `encAndOrNCL`.

## Main results

* `HWord.Planarized.polyTimeReducible_bounded`: the fixed-H reduction under general graph encoding.
* `exists_BandwidthPlanarAndOrNCL_pspaceHard`: the hardness direction of
  [VanDerZanden2015, Theorem 6], with configuration-to-configuration reachability.
* `exists_BandwidthPlanarAndOrNCL_pspaceComplete`: the full completeness theorem.

## References

* [M. Wrochna, *Reconfiguration in bounded bandwidth and treedepth*][Wrochna2014].
* [T. C. van der Zanden, *Parameterized Complexity of Graph Constraint Logic*][VanDerZanden2015].
-/

public section

namespace Cslib.Complexity.NCL
open _root_.Turing.MultiTapeTM

namespace HWord.Planarized
variable {q : ℕ} (H : Digraph (Fin q)) [DecidableRel H.Adj] (hq : 0 < q)

/-- The actual numbered planar graph and endpoint directions emitted from the H-word input. -/
@[expose] def reduceGraph (x : Instance q) : AndOrNCL.Instance :=
  let y := reduce H hq x
  ⟨Word.compile y.word, y.initial, y.target⟩

/-- Compilation into the general graph instance encoding is polynomial-time. -/
theorem computableInPolyTime_reduceGraph :
    ComputableInPolyTime (reduceGraph H hq) (encInstance q) encAndOrNCL := by
  have hp := computableInPolyTime_reduce H hq
  unfold reduceGraph
  fun_prop

private theorem reduceGraph_mem_AndOrNCL_iff (x : Instance q) :
    reduceGraph H hq x ∈ AndOrNCL ↔ x ∈ language H := by
  simpa only [PlaneWordAndOrNCL, Set.mem_ofPred_eq, checkPlane_reduce H hq x,
    wellTyped_reduce H hq x, true_and, reduceGraph] using reduce_mem_iff H hq x

private theorem reduceGraph_hasBandwidth (x : Instance q) (hx : x ∈ language H) :
    (reduceGraph H hq x).graph.graph.HasBandwidth (layoutBound q) := by
  obtain ⟨t, ht, _, _⟩ := hx
  have hlen : x.source.length = x.target.length :=
    List.length_ofFn.symm.trans (congrArg List.length ht)
  unfold reduceGraph
  rw [reduce_of_length_eq H hq x hlen]
  exact ⟨Diagram.compileBandwidthCertificate Prim.interp (diagram (n := x.source.length) H hq)
    (layoutCertificate (n := x.source.length) H hq)⟩

/-- The actual planar graph has the fixed bandwidth and accepts exactly the source instances. -/
theorem reduceGraph_mem_iff (x : Instance q) :
    reduceGraph H hq x ∈ BandwidthPlanarAndOrNCL (layoutBound q) ↔ x ∈ language H := by
  constructor
  · intro hx
    exact (reduceGraph_mem_AndOrNCL_iff H hq x).mp hx.1.1
  · intro hx
    have ha := (reduceGraph_mem_AndOrNCL_iff H hq x).mpr hx
    exact ⟨⟨ha, Word.isPlanar_compile (checkPlane_reduce H hq x)
      (wellTyped_reduce H hq x) ha.1⟩, reduceGraph_hasBandwidth H hq x hx⟩

omit [DecidableRel H.Adj] in
/-- Fixed-H word reconfiguration reduces to planar AND/OR graphs with fixed bandwidth,
under the ordinary numbered graph encoding. -/
theorem polyTimeReducible_bounded (hq : 0 < q) :
    PolyTimeReducible (encInstance q) encAndOrNCL (language H)
      (BandwidthPlanarAndOrNCL (layoutBound q)) := by
  classical
  exact ⟨reduceGraph H hq, computableInPolyTime_reduceGraph H hq,
    fun x => (reduceGraph_mem_iff H hq x).symm⟩

end HWord.Planarized

/-- For some fixed bandwidth, configuration-to-configuration reachability on planar AND/OR
graphs is PSPACE-hard under `encAndOrNCL`. This is the hardness direction of
[VanDerZanden2015, Theorem 6]. Planarity and bandwidth are properties of the general input graph. -/
theorem exists_BandwidthPlanarAndOrNCL_pspaceHard :
    ∃ bound, PSPACEHard encAndOrNCL (BandwidthPlanarAndOrNCL bound) := by
  classical
  obtain ⟨q, H, hq, hhard⟩ := HWord.exists_language_pspaceHard
  exact ⟨HWord.Planarized.layoutBound q,
    hhard.trans (HWord.Planarized.polyTimeReducible_bounded H hq)⟩

/-- For some fixed bandwidth, configuration-to-configuration reachability on planar AND/OR
multigraphs is PSPACE-complete under the general graph encoding `encAndOrNCL`
[VanDerZanden2015, Theorem 6]. The bandwidth bound is independent of the input graph. -/
theorem exists_BandwidthPlanarAndOrNCL_pspaceComplete :
    ∃ bound, PSPACEComplete encAndOrNCL (BandwidthPlanarAndOrNCL bound) := by
  obtain ⟨bound, hhard⟩ := exists_BandwidthPlanarAndOrNCL_pspaceHard
  exact ⟨bound, BandwidthPlanarAndOrNCL_mem_PSPACE bound, hhard⟩

end Cslib.Complexity.NCL
