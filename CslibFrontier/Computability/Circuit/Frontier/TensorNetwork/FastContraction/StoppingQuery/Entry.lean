/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.DescribedContraction
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListMap
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeOptionPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListBinaryLookup
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListToBits
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Foundations.Data.BitString.Binary
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Bitwise

/-!
# Input requests for the stopping contraction circuit

A terminal label stores four binary indices: an edge assignment, a vertex, a coefficient and a
bit. `entryRequest` selects the vertex descriptor and reads only the assignment bits at that
vertex's ports. It does not enumerate assignments or construct any tensor table. Invalid
vertices return `none`, and ports outside the network's edge range read `false`.

`sum_prod_networkEntry` identifies the indexed sum of products used by the stopping circuit with
the contraction of a described network. `entryRequest_polyTime` implements terminal routing on
the existing explicit encoding of that network. Its polynomial clock charges the complete
encoded network and the binary label; it is not a bound for succinct access to a recursively
described network.
-/

@[expose] public section

namespace Cslib.Circuits.Frontier.FastContraction.StoppingQuery

open Turing.MultiTapeTM ComputableInPolyTime BitString Finset DescribedNetwork

/-- A terminal of the stopping circuit, naming a single bit of one vertex's entry. -/
structure Entry where
  /-- The global edge assignment, as a binary natural. -/
  assignment : ℕ
  /-- The vertex number. -/
  vertex : ℕ
  /-- The representative coefficient number. -/
  coefficient : ℕ
  /-- The bit within that coefficient. -/
  bit : ℕ
  deriving DecidableEq

/-- Four binary natural numbers in field order, each field except the last framed. -/
enc_structure encEntry : Entry where
  assignment : encNat, vertex : encNat, coefficient : encNat, bit : encNat

/-- A terminal routed to a vertex descriptor and the bits on its ordered ports. -/
structure EntryRequest (T : Type) where
  /-- The selected vertex's descriptor. -/
  descriptor : T
  /-- The assignment in the vertex's port order. -/
  assignment : List Bool
  /-- The representative coefficient number. -/
  coefficient : ℕ
  /-- The bit within that coefficient. -/
  bit : ℕ

/-- A framed descriptor, a framed raw assignment word, then the binary coefficient and bit. -/
enc_structure encEntryRequest (T : Type) (encT : T ↪ List Bool) : EntryRequest T where
  descriptor : encT, assignment : encBits, coefficient : encNat, bit : encNat

variable {T : Type}

/-- Select a descriptor and its port bits directly from a binary global assignment. -/
def entryRequest (d : DescribedNetwork T) (e : Entry) : Option (EntryRequest T) :=
  d.vertices[e.vertex]?.map fun v =>
    ⟨v.2, v.1.map (fun i => decide (i < d.numEdges) && e.assignment.testBit i),
      e.coefficient, e.bit⟩

private theorem portBits_eq (edges assignment : ℕ) (ports : List ℕ) :
    ports.map (fun i => decide (i < edges) && assignment.testBit i) =
      wordBits (lowBits edges assignment) ports := by
  apply List.map_congr_left
  intro i _
  by_cases hi : i < edges
  · simp [lowBits, List.getD_eq_getElem?_getD, hi]
  · simp [hi]

/-- Terminal routing agrees with the described network's port convention, including invalid
vertices and ports. Coefficient and bit indices are preserved exactly. -/
theorem entryRequest_eq (d : DescribedNetwork T) (e : Entry) :
    entryRequest d e = d.vertices[e.vertex]?.map (fun v =>
      ⟨v.2, wordBits (lowBits d.numEdges e.assignment) v.1, e.coefficient, e.bit⟩) := by
  simp only [entryRequest, portBits_eq]

/-- The semantic entry named by a global assignment and a vertex; missing vertices are zero. -/
def networkEntry {R : Type*} [Zero R] (d : DescribedNetwork T) (eval : T → List Bool → R)
    (assignment vertex : ℕ) : R :=
  (d.vertices[vertex]?).elim 0 fun v => eval v.2 (wordBits (lowBits d.numEdges assignment) v.1)

/-- Evaluating a routed terminal gives exactly the selected network entry. -/
theorem entryRequest_value {R : Type*} [Zero R] (d : DescribedNetwork T)
    (eval : T → List Bool → R) (e : Entry) :
    (entryRequest d e).elim 0 (fun r => eval r.descriptor r.assignment) =
      networkEntry d eval e.assignment e.vertex := by
  rw [entryRequest_eq, networkEntry]
  cases d.vertices[e.vertex]? <;> rfl

/-- The binary-indexed sum of vertex products is the contraction, also for empty networks. -/
theorem sum_prod_networkEntry {R : Type*} [CommSemiring R] (d : DescribedNetwork T)
    (eval : T → List Bool → R) :
    (∑ a ∈ range (2 ^ d.numEdges), ∏ v ∈ range d.vertices.length, networkEntry d eval a v) =
      d.contraction eval := by
  have hprod (a : ℕ) : (∏ v ∈ range d.vertices.length, networkEntry d eval a v) =
      (d.vertices.map fun v => eval v.2 (wordBits (lowBits d.numEdges a) v.1)).prod := by
    rw [← Fin.prod_univ_eq_prod_range]
    simpa [networkEntry] using Fin.prod_univ_fun_getElem d.vertices
      (fun v => eval v.2 (wordBits (lowBits d.numEdges a) v.1))
  simp_rw [hprod]
  rw [← Fin.sum_univ_eq_sum_range, DescribedNetwork.contraction]
  exact Fintype.sum_equiv (equivFin d.numEdges).symm _ _ fun k => by
    rw [lowBits_eq_ofFn_equivFin_symm]

/-- The framed encoded described network followed by the unframed binary terminal label. -/
abbrev encEntryInput (encT : T ↪ List Bool) : DescribedNetwork T × Entry ↪ List Bool :=
  encPair (encDescribed encT) encEntry

/-- One native machine routes a terminal in polynomial time in the encoded network and binary
label. Binary indices are capped before unary traversal, including out-of-range inputs. -/
theorem entryRequest_polyTime (encT : T ↪ List Bool) :
    ComputableInPolyTime (fun a : DescribedNetwork T × Entry => entryRequest a.1 a.2)
      (encEntryInput encT) (encOption (encEntryRequest T encT)) := by
  have hd := fst (encDescribed encT) encEntry
  have he := snd (encDescribed encT) encEntry
  have hv := vertices_polyTime.comp hd
  have hn := (length_list (encVertex encT)).comp hv
  have hi := encEntry_vertex_deg.computableInPolyTime.comp he
  have hget : ComputableInPolyTime (fun a : DescribedNetwork T × Entry =>
      a.1.vertices[a.2.vertex]?) (encEntryInput encT) (encOption (encVertex encT)) := by
    apply (ComputableInPolyTime.getElem? (encA := encVertex encT) hv
      (binary_min_unary' hn hi)).of_enc_eq
    intro a
    simp only [Function.comp_apply]
    by_cases h : a.2.vertex ≤ a.1.vertices.length
    · simp only [Nat.min_eq_right h]
    · simp [Nat.min_eq_left (by omega : a.1.vertices.length ≤ a.2.vertex),
        List.getElem?_eq_none (by omega : a.1.vertices.length ≤ a.2.vertex)]
  apply optionMapWithInput hget
  have ha := fst (encEntryInput encT) (encVertex encT)
  have hvertex := snd (encEntryInput encT) (encVertex encT)
  have hlabel := he.comp ha
  have hports := (fst (encList encNat) encT).comp hvertex
  have hedges := numEdges_polyTime.comp (hd.comp ha)
  have hassign := encEntry_assignment_deg.computableInPolyTime.comp hlabel
  have hbits := listToBits.comp (mapWithInput
    (f := fun a i => decide (i < a.1.1.numEdges) && a.1.2.assignment.testBit i) hports (by
    have houter := fst (encPair (encEntryInput encT) (encVertex encT)) encNat
    have hport := snd (encPair (encEntryInput encT) (encVertex encT)) encNat
    have hbound := hedges.comp houter
    have hw := (of_eq (f := Nat.bits) (encIn := encNat) (encOut := encBits)
      fun _ => rfl).comp (hassign.comp houter)
    exact bool_and' (binary_lt' hport (unary_to_binary.comp hbound))
      (listGetD_binary (encL := encBits) false hw hport |>.of_enc_eq (fun a => by
        simp only [Nat.testBit_eq_inth, ← List.getD_default_eq_getI]
        rfl))))
  exact encEntryRequest_mk_polyTime T encT ((snd (encList encNat) encT).comp hvertex) hbits
    (encEntry_coefficient_deg.computableInPolyTime.comp hlabel)
    (encEntry_bit_deg.computableInPolyTime.comp hlabel)

end Cslib.Circuits.Frontier.FastContraction.StoppingQuery
