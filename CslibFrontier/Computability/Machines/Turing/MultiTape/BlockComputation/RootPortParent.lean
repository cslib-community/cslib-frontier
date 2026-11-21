/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RootPortGraph

/-!
# Recovering a parent half-edge of a seeded root child

A proposed parent index is checked against a group-membership query and the rank of that
port in the group. Column ports follow every row port, so the two checks share a certified
row total. The right-hand side of the equivalence uses only bounded bit claims about sums of
the native root port predicate, including the full-prefix count.
-/

public section

namespace Turing.MultiTapeTM.RootPortParent

open Cslib Cslib.Circuits.Frontier MultiTapePTM
open RootPredecessorGraph (edgeCount vertexCount inputOfIndices)
open RootPortGraph (groups ends side)

variable {k q copies a : ℕ} {State : Type} (machine : MultiTapePTM k Bool State)
    (input : List Bool) (b σ : ℕ) (code : BlockLetter k State b → Fin copies → Bool)
    (seed : BalancedSchedules.SeededLabels.Seed (vertexCount k q copies) (6 * a))
    (i : Fin a) (g : ℕ)

/-- One runtime membership test in the prefix of a row or column group. -/
@[expose] def leaf (column : Bool) (bound j : ℕ) : Bool :=
  RootPortQuery.query k (⟨column, i.val, g⟩, inputOfIndices k q copies σ a seed bound j)

/-- Sum of the native leaf bits for a split coordinate, side, group, and prefix. -/
@[expose] def prefixCount (column : Bool) (bound : ℕ) : ℕ :=
  ∑ j : Fin (edgeCount k q copies), (leaf σ seed i g column bound j.val).toNat

/-- Even a full prefix with every edge in the group has count at most the edge universe. -/
theorem prefixCount_le (column : Bool) (bound : ℕ) :
    prefixCount σ seed i g column bound ≤ edgeCount k q copies := by
  calc
    _ ≤ ∑ _ : Fin (edgeCount k q copies), 1 := Finset.sum_le_sum fun j _ => by
      cases leaf σ seed i g column bound j.val <;> decide
    _ = _ := by simp

private theorem count_eq (column : Bool) {bound : ℕ} (hb : bound ≤ edgeCount k q copies) :
    prefixCount σ seed i g column bound =
      ∑ j : Fin (ends (q := q) machine input b σ code).length,
        (NativeChild.portPredecessor (groups seed i) g (ends (q := q) machine input b σ code)
          (side column) bound j.val).toNat := by
  rw [← NativeChild.portRank_eq_sum_predecessors _ _ _ _ (by simpa using hb)]
  exact (RootPortGraph.portRank_eq_sum_query machine input b σ code seed i column g hb).symm

/-- For a genuine candidate, membership in the full prefix checks its actual endpoint's group. -/
private theorem leaf_full (column : Bool) {e : ℕ} (he : e < edgeCount k q copies) :
    leaf σ seed i g column (edgeCount k q copies) e = true ↔
      (groups seed i).getD (side column ((ends (q := q) machine input b σ code).getD e (0, 0))) 0 =
        g := by
  rw [leaf, RootPortGraph.query_eq_portPredecessor machine input b σ code seed i column g le_rfl]
  simp [NativeChild.portPredecessor, he]

/-- A valid child index has exactly the parent certified by these native leaf counts. The
width bound is strict because the full row count may equal the whole edge universe. -/
theorem parentEdge_witness_iff_bits {width rows j e : ℕ}
    (hw : edgeCount k q copies < 2 ^ width) (hr : rows < 2 ^ width)
    (hrows : ∀ bit : Fin width, rows.testBit bit.val =
      (prefixCount σ seed i g false (edgeCount k q copies)).testBit bit.val) :
    let es := ends (q := q) machine input b σ code
    let gs := groups seed i
    (j < (NativeChild.portEdges gs g es Prod.fst).length +
        (NativeChild.portEdges gs g es Prod.snd).length ∧ NativeChild.parentEdge gs g es j = e) ↔
      e < edgeCount k q copies ∧
        ((leaf σ seed i g false (edgeCount k q copies) e = true ∧ j < 2 ^ width ∧
            ∀ bit : Fin width, j.testBit bit.val =
              (prefixCount σ seed i g false e).testBit bit.val) ∨
          (leaf σ seed i g true (edgeCount k q copies) e = true ∧ rows ≤ j ∧
            j - rows < 2 ^ width ∧ ∀ bit : Fin width, (j - rows).testBit bit.val =
              (prefixCount σ seed i g true e).testBit bit.val)) := by
  dsimp only
  let es := ends (q := q) machine input b σ code
  let gs := groups seed i
  have hn : es.length = edgeCount k q copies := by simp [es]
  have hfull := count_eq machine input b σ code seed i g false
    (bound := edgeCount k q copies) le_rfl
  have h := NativeChild.parentEdge_witness_iff_bits gs g es (j := j) (e := e)
    (hn ▸ hw) hr (fun bit => by
      rw [show NativeChild.portPredecessor gs g es Prod.fst es.length =
        NativeChild.portPredecessor gs g es Prod.fst (edgeCount k q copies) by rw [hn]]
      exact (hrows bit).trans (congrArg (fun m : ℕ => m.testBit bit.val) hfull))
  apply h.trans
  by_cases he : e < edgeCount k q copies
  · have hrow := count_eq machine input b σ code seed i g false he.le
    have hcol := count_eq machine input b σ code seed i g true he.le
    have hm₁ := leaf_full machine input b σ code seed i g false he
    have hm₂ := leaf_full machine input b σ code seed i g true he
    change (_ ↔ _)
    simp only [hn, he, true_and, hm₁, hm₂, hrow, hcol]
    rfl
  · simp only [hn, he, false_and]

end Turing.MultiTapeTM.RootPortParent
