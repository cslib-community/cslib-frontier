/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.DescendantBirthTime
import Mathlib.Tactic.FinCases

/-!
# Packet birth access witnesses

One native machine handles mixed birth stages and malformed indices. A two-stage actual native
ancestry ties the retrieved older parameters and proper exponent slice to a retained descriptor.
-/

public section

namespace Turing.MultiTapeTM.DescendantBirth.Tests

open Cslib Circuits.Frontier NativeChild DescendantVertex
open DescendantEndpoint (Frame)

private def oldCall : Call :=
  ⟨⟨[1], 1, 0, 3, -1, [4], 0⟩, [10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]⟩

private def newCall : Call := ⟨⟨[1], 1, 0, 9, -3, [99], 0⟩, []⟩

private def oldBirth : Birth := ⟨oldCall.parameters, 1, [16, 17, 18, 19, 20, 21]⟩

/-- Older, current, missing and oversized-packet birth queries. -/
def requests : Fin 5 → (List Call × Origin) × Option Birth := ![
  (([oldCall, newCall], ⟨1, 1⟩), some oldBirth),
  (([oldCall, newCall], ⟨0, 1⟩), none),
  (([oldCall, newCall], ⟨2, 0⟩), some ⟨newCall.parameters, 0, []⟩),
  (([oldCall, newCall], ⟨3, 1⟩), none),
  (([oldCall, newCall], ⟨1, 2 ^ 100⟩), some ⟨oldCall.parameters, 2 ^ 100, []⟩)]

-- One native machine retrieves creation precision three from the older call despite the
-- later precision nine. Invalid stages and huge packet numbers use the same machine.
/-- The mixed-stage birth queries share one finite native machine. -/
theorem native_birth_boundaries :
    ∃ (d c K : ℕ) (Q : Type) (_ : Finite Q) (tm : MultiTapeTM K Bool Q), ∀ i,
    let a := (requests i).1
    let budget := c * ((encList encCall a.1).length + lookupSize a ^ d + 1)
    tm.ComputesInTimeAndSpace (encPair (encList encCall) encOrigin a)
      (encOption encBirth (requests i).2) budget budget := by
  obtain ⟨d, c, ⟨K, Q, hQ, tm, htm⟩, _⟩ := exists_lookup_inO
  refine ⟨d, c, K, Q, hQ, tm, fun i => ?_⟩
  have h : lookup (requests i).1.1 (requests i).1.2 = (requests i).2 := by
    fin_cases i <;> rfl
  simpa only [h] using htm (requests i).1

private def zeroFrame (vertices : ℕ) : Frame :=
  Frame.ofSeed (U := vertices) (a := 1) 0 (fun _ => 0) 0 0

private def emptyRoot : DescribedNetwork (VertexDesc ℕ) := ⟨0, []⟩

-- An actual native child with two isolated packets is enough to test the birth index and
-- later retention. Packing and networks occur only in this mathematical trace.
private def firstChild : DescribedNetwork (VertexDesc ℕ) :=
  nativeChild [1] 1 0 3 (-1) [4] 0 emptyRoot (([], []), 2, []) oldCall.exponents 0

private def firstTrace : NativeAncestry emptyRoot [zeroFrame 0] firstChild :=
  .cons .nil [1] 3 (-1) [4] 0 (([], []), 2, []) oldCall.exponents rfl
    (fun v hv => by change v < 0 at hv; omega)

private def secondChild : DescribedNetwork (VertexDesc ℕ) :=
  nativeChild [1] 1 0 9 (-3) [99] 0 firstChild (([], [[0], [0]]), 0, []) [] 0

private theorem secondLabels (v : ℕ) (hv : v < (zeroFrame 2).vertices) :
    symbol (zeroFrame 2) v =
      (groupsOf 0 0 firstChild.vertices.length ([], [[0], [0]])).getD v 0 := by
  have hz : symbol (zeroFrame 2) v = 0 := by
    simp [zeroFrame, symbol, rankQuery, Frame.ofSeed, RootPortFinish.symbol,
      TrinomialArithmetic.runSelected, TrinomialArithmetic.hash4, TrinomialArithmetic.eval4,
      TrinomialArithmetic.mul, TrinomialArithmetic.reduce, clmul_zero_right]
  rw [hz]
  change v < 2 at hv
  have hh : v = 0 ∨ v = 1 := by omega
  rcases hh with rfl | rfl <;> rfl

private def secondTrace : NativeAncestry emptyRoot [zeroFrame 2, zeroFrame 0] secondChild :=
  .cons firstTrace [1] 9 (-3) [99] 0 (([], [[0], [0]]), 0, []) [] rfl secondLabels

private theorem retained_origin :
    HasOrigin secondChild.vertices.length 1 ⟨1, 1⟩ [zeroFrame 2, zeroFrame 0] := by
  refine ⟨by decide, Or.inr ⟨by decide, 1, by decide, secondLabels 1 (by decide), ?_, ?_⟩⟩
  · rw [retained_eq_count (D := firstChild) (packing := (([], [[0], [0]]), 0, []))
      rfl secondLabels]
    decide
  · exact ⟨by decide, Or.inl ⟨rfl, by decide⟩⟩

-- The computed older call is tied to the actual retained descriptor, not merely to an
-- independently supplied list of parameters. Its packet number is one, so β is a proper slice.
example : lookup (calls secondTrace) ⟨1, 1⟩ = some oldBirth ∧
    ∃ tags, (secondChild.vertices[1]?).map Prod.snd =
      some (.inr (oldBirth.descriptor tags)) := by
  have hlookup : lookup (calls secondTrace) ⟨1, 1⟩ = some oldBirth := rfl
  obtain ⟨birth, hb, tags, hd⟩ := lookup_of_origin secondTrace retained_origin (by decide)
  have heq : birth = oldBirth := Option.some.inj (hb.symm.trans hlookup)
  subst birth
  exact ⟨hlookup, tags, hd⟩

end Turing.MultiTapeTM.DescendantBirth.Tests
