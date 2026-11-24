/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module

-- upstream: candidate
public import CslibFrontier.Algorithms.Lean.MinimumSpanningForest.CompactParallel
public import CslibFrontier.Algorithms.Lean.MinimumSpanningForest.DenseCase
public import CslibFrontier.Algorithms.Lean.MinimumSpanningForest.Precompute
public import CslibFrontier.Algorithms.Lean.MinimumSpanningForest.RecursiveReduction
import Mathlib.Data.Nat.Log

/-!
# Cached component decisions in the recursive MSF reduction

Precompute the local decision-tree bank once, with the original input's triple-logarithmic
vertex cutoff. Compact each local multigraph before lookup. The same bank serves all recursive
calls, since the active vertex count decreases.

See [Pettie and Ramachandran, §§4.1 and 5][PettieRamachandran2002].
-/

public section

namespace Cslib.Multigraph.PettieRamachandran

open Finset

variable {V E : Type} {W : Type*} [LinearOrder E] [LinearOrder V] [LinearOrder W]
variable {w : E → W}

private theorem cutoff_mono {m n : ℕ} (h : m ≤ n) :
    m.log2.log2.log2 + 1 ≤ n.log2.log2.log2 + 1 := by
  simp only [Nat.log2_eq_log_two]
  exact Nat.add_le_add_right (Nat.log_mono_right (Nat.log_mono_right (Nat.log_mono_right h))) 1

/-- Both lookup indices of an actual bounded component fit a bank of vertex capacity
`r` and edge capacity `r²`. This holds in any later quotient graph in which its
internal edges are collected. -/
theorem partition_lookup_fits (grower : PrimPartition.Grower V E W w) (hw : Function.Injective w)
    {levelEnds localEnds : E → Sym2 V} {levelEdges active : Finset E} {part : PartitionPart V E W}
    {n : ℕ} (hn : (support levelEnds levelEdges).card ≤ n)
    (hp : part ∈ PrimPartition.partition grower (support levelEnds levelEdges).card.log2.log2.log2
      levelEnds levelEdges id ∅ (support levelEnds levelEdges).toList) :
    let I := compactParallel localEnds w (internalEdges localEnds active part.vertices)
    let r := n.log2.log2.log2 + 1
    (OptimalTree.vertices localEnds I).card ≤ r ∧ I.card ≤ r ^ 2 := by
  obtain ⟨X, hx, hl⟩ := PrimPartition.size_partition _ _ _ _ _ _ hp
  have contains : ∀ e ∈ internalEdges localEnds active part.vertices,
      ∀ x ∈ localEnds e, x ∈ X := by
    intro e he x hxe
    have hxC := (mem_internalEdges.1 he).2 x hxe
    rwa [hx] at hxC
  have bound := hl.trans (cutoff_mono hn)
  exact ⟨(card_le_card (vertices_compactParallel_subset contains)).trans bound,
    (card_compactParallel_le hw contains).trans (Nat.pow_le_pow_left bound 2)⟩

/-- Bind one shared bank to the small solver. A lookup uses the compact vertex and edge
indices of the actual local multigraph. The dense procedure receives the terminal quotient. -/
private noncomputable def withBank (w : E → W) (hw : Function.Injective w) {r : ℕ}
    (bank : MSFPrecompute.Bank r (r ^ 2)) (filled : bank = MSFPrecompute.fillBank r (r ^ 2)) :
    Solvers V E W w where
  small ends S := (MSFPrecompute.cachedMSFOn bank ends (compactParallel ends w S)).eval
    (Cslib.Query.LEQuery.keyOracle w)
  small_eq ends S := by
    rw [filled, MSFPrecompute.cachedMSFOn_fill, (optimalMSFOn_spec _ _ w hw.injOn).1,
      msf_compactParallel]
  dense m ends S := DenseCase.solve m w ends S
  dense_eq m ends S := DenseCase.solve_eq m w hw ends S

/-- Initialize one bank at the original vertex cutoff and reuse it in every recursive round. -/
noncomputable def cachedReduction (grower : PrimPartition.Grower V E W w)
    (hw : Function.Injective w) (ends : E → Sym2 V) (S : Finset E) : Finset E :=
  let r := (support ends S).card.log2.log2.log2 + 1
  let bank := MSFPrecompute.fillBank r (r ^ 2)
  reduceMSF grower (withBank w hw bank rfl) hw ends S

theorem cachedReduction_eq (grower : PrimPartition.Grower V E W w) (hw : Function.Injective w)
    (ends : E → Sym2 V) (S : Finset E) :
    cachedReduction grower hw ends S = msf ends w S :=
  reduceMSF_eq ..

end Cslib.Multigraph.PettieRamachandran
