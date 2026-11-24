/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.MinimumSpanningForest.CachedReduction
public import CslibFrontier.Algorithms.Lean.MinimumSpanningForest.HeapPrim
public import Mathlib.Algebra.Order.Monoid.Prod

/-!
# The graph-level Pettie–Ramachandran minimum spanning forest algorithm

The recursive procedure uses a four-ary soft heap to grow each component, one bank of
optimal decision trees prepared at the original size cutoff, bounded-frontier Prim passes
on the dense quotient, and two Borůvka passes before recursion. Threshold two in the
four-ary heap gives a corruption fraction of at most one sixteenth, within the one-eighth
allowance in [PettieRamachandran2002], §5.

The construction uses the native multigraph's classical component representatives.
Its correctness theorem identifies the output on the original edge labels. The paper's
worst-case instruction bound for the whole algorithm is a separate result.
-/

public section

namespace Cslib.Multigraph.PettieRamachandran

variable {V E W : Type} [LinearOrder V] [LinearOrder E] [LinearOrder W]

/-- The recursive algorithm on injectively weighted edges. -/
noncomputable def forest (ends : E → Sym2 V) (w : E → W) (hw : Function.Injective w)
    (S : Finset E) : Finset E :=
  cachedReduction (PrimPartition.HeapPrim.grower 2 w) hw ends S

/-- The algorithm returns the original graph's minimum spanning forest. -/
theorem forest_eq_msf (ends : E → Sym2 V) (w : E → W) (hw : Function.Injective w)
    (S : Finset E) : forest ends w hw S = msf ends w S :=
  cachedReduction_eq ..

section Ties

variable [AddCommGroup W] [IsOrderedAddMonoid W]

/-- Order equal weights by the index of their original edge. -/
def tieKey {m : ℕ} (w : Fin m → W) (e : Fin m) : W ×ₗ ℤ := toLex (w e, (e.val : ℤ))

omit [LinearOrder W] [AddCommGroup W] [IsOrderedAddMonoid W] in
theorem tieKey_injective {m : ℕ} (w : Fin m → W) : Function.Injective (tieKey w) := by
  intro a b eq
  have h := congrArg (fun k : W ×ₗ ℤ => (ofLex k).2) eq
  exact Fin.ext (Int.ofNat_inj.mp h)

/-- Run the graph-level algorithm with stable edge labels to resolve equal input weights. -/
noncomputable def forestWithTies {m : ℕ} (ends : Fin m → Sym2 V) (w : Fin m → W)
    (S : Finset (Fin m)) : Finset (Fin m) :=
  forest ends (tieKey w) (tieKey_injective w) S

/-- For tied input weights the result is a spanning forest with minimum *original* weight
among all spanning forests, including all tie resolutions. -/
theorem forestWithTies_minimum {m : ℕ} (ends : Fin m → Sym2 V) (w : Fin m → W)
    (S : Finset (Fin m)) : IsSpanningForest ends S (forestWithTies ends w S) ∧
      ∀ F : Finset (Fin m), IsSpanningForest ends S F →
        ∑ e ∈ forestWithTies ends w S, w e ≤ ∑ e ∈ F, w e := by
  rw [forestWithTies, forest_eq_msf]
  refine ⟨isSpanningForest_msf _ (tieKey_injective w), fun F hF => ?_⟩
  have le := sum_msf_le (tieKey w) (tieKey_injective w) hF
  let fstKey : (W ×ₗ ℤ) →+ W := ⟨⟨fun k => (ofLex k).1, rfl⟩, fun _ _ => rfl⟩
  have project (A : Finset (Fin m)) :
      fstKey (∑ e ∈ A, tieKey w e) = ∑ e ∈ A, w e := by
    rw [map_sum]
    rfl
  rw [← project, ← project]
  exact Prod.Lex.monotone_fst _ _ le

end Ties

end Cslib.Multigraph.PettieRamachandran
