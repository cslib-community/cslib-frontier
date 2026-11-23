/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.DescendantVertexCorrect
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import Mathlib.Data.List.GetD

/-!
# Accessing a packet's stored birth call

`Call` stores the interpolation parameters and packet-major exponent word of one native child
construction. It stores no parent network, packing table or port list. Calls are ordered from
the root toward the current network, so a positive verified origin selects call `stage - 1`.
`lookup` returns that call's parameters and the packet's own exponent slice.

The precision remains binary in `encParameters`. Producing the older unary `NativePacket.PacketCtx`
encoding is not part of this access operation. The semantic conversion `Birth.descriptor` uses the
unchanged `NativeChild.packetCtx` constructor and accepts the separately accessed port tags.

`lookup_of_origin` proves that the log projected from an actual native ancestry gives precisely
the context and exponent slice in the retained packet's actual descriptor. Later splits cannot
replace its precision or interpolation data. This is original access semantics; the complete
compressed entry continuation remains part of #4728.

## Main results

* `Turing.MultiTapeTM.DescendantBirth.lookup_of_origin`: exact context and exponent slice for
  every accepted positive origin of an actual native ancestry.
-/

public section

namespace Turing.MultiTapeTM.DescendantBirth

open Cslib Circuits.Frontier NativeChild DescendantVertex
open DescendantEndpoint (Frame)

/-- The stored interpolation data of one native split, with no graph or packing tables. -/
structure Parameters where
  /-- The coefficients of the ring modulus below its leading coefficient. -/
  modulus : List ℕ
  /-- The number of packet-slot coordinates. -/
  coordinates : ℕ
  /-- The coordinate at which the split occurs. -/
  coordinate : ℕ
  /-- The precision at which this call's packet vertices are created. -/
  precision : ℕ
  /-- The interpolation grid point. -/
  point : ℤ
  /-- The interpolation value as a coefficient list. -/
  value : List ℕ
  /-- The child group. -/
  group : ℕ
  deriving Inhabited, DecidableEq

/-- Binary precision, group and coefficient lists; unary coordinate counters; a binary signed
grid point. Fields occur in declaration order, each but the last framed. -/
enc_structure encParameters : Parameters where
  modulus : (encList encNat), coordinates : encUnary, coordinate : encUnary, precision : encNat,
  point : encIntBin, value : (encList encNat), group : encNat

/-- One stored call and the complete packet-major exponent word chosen at that call. -/
structure Call where
  /-- Short data shared by the packet vertices created at this split. -/
  parameters : Parameters
  /-- The call's complete packet-major exponent word. -/
  exponents : List ℕ
  deriving Inhabited, DecidableEq

/-- Framed call parameters followed by binary exponents in a framed list. -/
enc_structure encCall : Call where parameters : encParameters, exponents : (encList encNat)

/-- The result of selecting one packet from its birth call. -/
structure Birth where
  /-- Parameters from the packet's creation stage. -/
  parameters : Parameters
  /-- The packet's number at that stage. -/
  packet : ℕ
  /-- Only this packet's slice of the call's exponent word. -/
  exponents : List ℕ
  deriving Inhabited, DecidableEq

/-- Framed parameters, a framed binary packet number and binary local exponents. -/
enc_structure encBirth : Birth where
  parameters : encParameters, packet : encNat, exponents : (encList encNat)

/-- Select the packet-major exponent slice while retaining the exact creation parameters. -/
@[expose] def select (call : Call) (packet : ℕ) : Birth :=
  ⟨call.parameters, packet,
    betaSlice call.parameters.coordinate call.parameters.precision call.exponents packet⟩

/-- A positive stage selects its chronological call. Stage zero belongs to the original
network and returns `none`, as do stages beyond the log. -/
@[expose] def lookup (calls : List Call) (origin : Origin) : Option Birth :=
  if origin.stage = 0 then none
  else (calls[origin.stage - 1]?).map fun call => select call origin.index

/-- Reconstruct the mathematical packet descriptor once its ordered row/slot tags are known.
This definition makes no claim about writing the unary packet-context encoding. -/
@[expose] def Birth.descriptor (birth : Birth) (tags : List (Bool × ℕ)) : NativePacket.PacketDesc :=
  (packetCtx birth.parameters.modulus birth.parameters.coordinates birth.parameters.coordinate
    birth.parameters.precision birth.parameters.point birth.parameters.value
    birth.parameters.group birth.packet, tags, birth.exponents)

variable {T : Type} {root : DescribedNetwork (VertexDesc T)}

/-- Project actual native calls into the chronological runtime log, omitting every network,
packing table, row count and port list. -/
@[expose] def calls : {frames : List Frame} → {D : DescribedNetwork (VertexDesc T)} →
    NativeAncestry root frames D → List Call
  | [], _, .nil => []
  | _, _, .cons (f := f) older fl pt t ζ _ _ β _ _ =>
    calls older ++ [⟨⟨fl, f.coordinates, f.coordinate, pt, t, ζ, f.group⟩, β⟩]

/-- The projected runtime log contains exactly one call per ancestry frame. -/
@[simp] theorem length_calls {frames : List Frame} {D : DescribedNetwork (VertexDesc T)}
    (ancestry : NativeAncestry root frames D) : (calls ancestry).length = frames.length := by
  induction ancestry <;> simp [calls, *]

/-- Accessing the stored birth call of an accepted positive origin retrieves exactly the
context and exponents of the actual packet descriptor. Ordered port tags are separate data. -/
theorem lookup_of_origin {frames : List Frame} {D : DescribedNetwork (VertexDesc T)}
    (ancestry : NativeAncestry root frames D) {vertex : ℕ} {origin : Origin}
    (h : HasOrigin D.vertices.length vertex origin frames) (hstage : 0 < origin.stage) :
    ∃ birth, lookup (calls ancestry) origin = some birth ∧
      ∃ tags, (D.vertices[vertex]?).map Prod.snd = some (.inr (birth.descriptor tags)) := by
  induction ancestry generalizing vertex with
  | nil =>
    have hz := h.2.1
    omega
  | @cons frames parent f older fl pt t ζ rows packing β hsize hlabels ih =>
    rcases h.2 with ⟨hs, hv⟩ | ⟨hs, v, hv, hg, hindex, hparent⟩
    · have hrank : retained f f.vertices =
          (groupsOf rows f.coordinate parent.vertices.length packing.1).count f.group := by
        rw [retained_eq_count hsize hlabels, hsize,
          List.take_of_length_le (by simp [groupsOf])]
      have hq : origin.index < packing.2.1 := by
        have hb := h.1
        rw [length_vertices_nativeChild, childRows, hv, hrank] at hb
        omega
      let call : Call := ⟨⟨fl, f.coordinates, f.coordinate, pt, t, ζ, f.group⟩, β⟩
      refine ⟨select call origin.index, ?_, ?_⟩
      · simp [lookup, calls, hs, length_calls, call]
      · have hl := getElem?_vertices_nativeChild_packet fl f.coordinates f.coordinate
          pt t ζ rows parent packing β f.group hq
        dsimp only at hl
        rw [hv, hrank, hl]
        exact ⟨_, rfl⟩
    · have hp : HasOrigin parent.vertices.length v origin frames := by
        simpa only [hsize] using hparent
      obtain ⟨birth, hb, tags, hd⟩ := ih hp
      refine ⟨birth, ?_, tags, ?_⟩
      · have hi : origin.stage - 1 < (calls older).length := by
          rw [length_calls]
          omega
        simpa only [lookup, calls, List.getElem?_append_left hi] using hb
      · let trace := NativeAncestry.cons older fl pt t ζ rows packing β hsize hlabels
        have hc := trace.descriptor_eq_birthDescriptor h
        have ho := older.descriptor_eq_birthDescriptor hp
        have hs' : origin.stage ≠ frames.length + 1 := by omega
        simp only [trace, NativeAncestry.birthDescriptor, hs', ite_false] at hc
        exact hc.trans (ho.symm.trans hd)

end Turing.MultiTapeTM.DescendantBirth
