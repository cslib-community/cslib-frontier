/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.PolyTime.ConvolutionOperand.Signed
public import CslibFrontier.Computability.PolyTime.CountingLeaf.Raw
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Envelope

/-!
# Preparing either operand request from a signed product leaf

The physical carry-save serializer supplies its usual six fields. Its protected context contains
an unchanged payload and the binary half-degree and coefficient index. Only these two indices and
the local width, path, carry and bit fields enter the signed convolution router. The payload is
copied a constant number of times and is excluded from the polynomial arithmetic bound.

`exists_word_inO` constructs the guarded child request natively. An absent operand address
selects the constant zero bit; a present address selects exactly the coefficient and bit returned
by `ConvolutionOperand.Signed.source`. Evaluating the requested operand is a separate continuation
in the native contraction compiler tracked by #4728.
-/

public section

namespace Turing.MultiTapeTM.SignedOperandRequest

open Cslib ConvolutionOperand ComputableInPolyTime

/-- Protected recursive context, followed by the binary half-degree and output coefficient. -/
structure Context where
  /-- The enclosing circuit or contraction request, copied without arithmetic on its contents. -/
  payload : List Bool
  /-- Half the degree of the sparse trinomial. -/
  half : ℕ
  /-- The product coefficient requested by the parent. -/
  index : ℕ

/-- The payload and half-degree are framed; the binary output coefficient is last. -/
enc_structure encContext : Context where
  payload : encBits, half : encNat, index : encNat

/-- The existing six physical serializer fields, with the protected product context interpreted. -/
structure Input where
  context : Context
  count : List Bool
  width : List Bool
  path : List Bool
  carry : Bool
  bit : List Bool

/-- Five framed fields followed by the raw little-endian bit-index word. -/
enc_structure encInput : Input where
  context : encContext, count : encBits, width : encBits, path : encBits,
  carry : encBool, bit : encBits

/-- The typed overlay has exactly the physical counting-leaf serializer's encoding. -/
theorem encInput_eq (x : Input) : encInput x = CountingLeaf.encRawInput
    ⟨encContext x.context, x.count, x.width, x.path, x.carry, x.bit⟩ := rfl

/-- A single recursive operand-bit claim; the protected payload is retained verbatim. -/
structure Request where
  payload : List Bool
  /-- False selects the left factor and true the right factor. -/
  right : Bool
  coefficient : ℕ
  bit : ℕ
  claim : Bool

/-- The payload, side and binary coordinates are framed, followed by the singleton claim bit. -/
enc_structure encRequest : Request where
  payload : encBits, right : encBool, coefficient : encNat, bit : encNat, claim : encBool

/-- Normalize only the short numeric fields and pass the physical path to the signed router. -/
@[expose] def query (right : Bool) (x : Input) : Signed.Query :=
  ⟨x.context.half, ofBits x.width, x.context.index, x.path, ofBits x.bit, x.carry, right⟩

/-- Install the selected coefficient and bit. The zero coordinates are ignored when no request
exists; the dispatch guard, rather than the fallback coordinates, decides whether to call. -/
@[expose] def request (right claim : Bool) (x : Input) : Request :=
  let coordinate := (Signed.source (query right x)).getD (0, 0)
  ⟨x.context.payload, right, coordinate.1, coordinate.2, claim⟩

/-- A three-bit guarded-dispatch header followed by the entire recursive operand request. -/
@[expose] def word (right claim : Bool) (x : Input) : List Bool :=
  [(Signed.source (query right x)).isSome, false, !claim] ++ encRequest (request right claim x)

/-- Only local words and binary product indices enter the polynomial cost. In a product-tree
traversal these words have logarithmic length; arbitrary longer local words are still charged. -/
@[expose] def shortSize (x : Input) : ℕ :=
  x.context.half.size + x.context.index.size + x.count.length + x.width.length +
    x.path.length + x.bit.length + 1

private theorem query_deg (right : Bool) :
    ComputableInDegree (query right) encInput Signed.encQuery 1 1 := by
  have hn : ComputableInDegree ofBits encBits encNat 1 1 :=
    ComputableInO.bitsToNat.computableInDegree DegreeBounded.self DegreeBounded.self le_rfl
  have hc := encInput_context_deg
  exact Signed.encQuery_mk_deg.comp ((encContext_half_deg.comp hc).prod
    ((hn.comp encInput_width_deg).prod ((encContext_index_deg.comp hc).prod
      (encInput_path_deg.prod ((hn.comp encInput_bit_deg).prod
        (encInput_carry_deg.prod (ComputableInDegree.const (encMid := encBool) right)))))))

private theorem query_size (right : Bool) :
    PolyBounded shortSize (fun x => (Signed.encQuery (query right x)).length) := by
  apply PolyBounded.of_forall_le 16 1
  intro x
  have hw := Nat.size_le.mpr (ofBits_lt_two_pow x.width)
  have hb := Nat.size_le.mpr (ofBits_lt_two_pow x.bit)
  simp only [query, Signed.encQuery_apply, Signed.encQueryFields, shortSize, length_encPair,
    encBits_apply, encNat_apply, Nat.size_eq_bits_len, encBool_apply, List.length_singleton,
    pow_one]
  omega

private def compiled (claim : Bool) (q : Signed.Query) : List Bool × Request :=
  let coordinate := (Signed.source q).getD (0, 0)
  ([(Signed.source q).isSome, false, !claim],
    ⟨[], q.right, coordinate.1, coordinate.2, claim⟩)

private theorem compiled_poly (claim : Bool) : ComputableInPolyTime (compiled claim)
    Signed.encQuery (encPair encBits encRequest) := by
  have hs := Signed.computableInPolyTime_source
  have hg :=
    (ComputableInDegree.getD (enc₁ := encPair encNat encNat) (0, 0)).computableInPolyTime.comp hs
  have hh : ComputableInPolyTime (fun b : Bool => [b, false, !claim]) encBool encBits :=
    of_finite _
  exact (hh.comp (optionIsSome hs)).prod (encRequest_mk_polyTime (const [])
    Signed.encQuery_right_deg.computableInPolyTime ((fst encNat encNat).comp hg)
    ((snd encNat encNat).comp hg) (const claim))

private def install (x : List Bool × Request) : Request := {x.2 with payload := x.1}

private theorem install_deg : ComputableInDegree install
    (encPair encBits encRequest) encRequest 1 1 := by
  have hr := ComputableInDegree.snd encBits encRequest
  exact encRequest_mk_deg.comp ((ComputableInDegree.fst encBits encRequest).prod
    ((encRequest_right_deg.comp hr).prod ((encRequest_coefficient_deg.comp hr).prod
      ((encRequest_bit_deg.comp hr).prod (encRequest_claim_deg.comp hr)))))

/-- The whole physical input remains linear in protected payload and local word lengths. -/
theorem encInput_length_le (x : Input) :
    (encInput x).length ≤ 4 * (x.context.payload.length + shortSize x + 3) := by
  simp only [encInput_apply, encInputFields, encContext_apply, encContextFields, shortSize,
    length_encPair, encBits_apply, encNat_apply, Nat.size_eq_bits_len, encBool_apply,
    List.length_singleton]
  omega

/-- Every enabled request is within the chosen operand's coefficient and precision bounds. -/
theorem request_bounds (right claim : Bool) (x : Input)
    (h : (Signed.source (query right x)).isSome = true) :
    (request right claim x).coefficient < 2 * x.context.half ∧
      (request right claim x).bit < ofBits x.width := by
  cases hs : Signed.source (query right x) with
  | none => simp [hs] at h
  | some coordinate =>
    have hb := Signed.source_bounds hs
    simp only [request, hs, Option.getD_some]
    simpa only [query] using hb

/-- The native request preparation is linear in the protected context, with polynomial work
only on the local signed-product metadata. Both the time and charged workspace obey this bound. -/
theorem exists_word_inO (right claim : Bool) : ∃ d,
    ComputableInO (word right claim) encInput encBits
      (fun x => x.context.payload.length + shortSize x ^ d)
      (fun x => x.context.payload.length + shortSize x ^ d) := by
  obtain ⟨T, S, hT, hS, hs⟩ := (compiled_poly claim).exists_computableInO
  have h := hs.comp (query_deg right).inO_one
  have hp := (encContext_payload_deg.comp encInput_context_deg).inO_one
  have hr := (install_deg.inO_one.comp_linear (hp.prod h.snd')).of_enc_eq
    (g := request right claim) (encC := encRequest) (fun _ => rfl)
  have hw := h.fst'.append hr (g := word right claim) (encOut := encBits) (fun _ => rfl)
  let extra (x : Input) := 12 * (shortSize x + 3) + 2 * (T (query right x) + S (query right x))
  have he : PolyBounded shortSize extra :=
    ((PolyBounded.const 12).mul (PolyBounded.self.add (.const 3))).add
      ((PolyBounded.const 2).mul ((hT.comp (query_size right)).add (hS.comp (query_size right))))
  obtain ⟨c, d, hd⟩ := he.exists_le_linear_add_pow (fun x => x.context.payload.length) 12
    (fun x => by simp [shortSize])
  refine ⟨d, hw.mono c (fun x => ?_) (fun x => ?_)⟩ <;>
    refine le_trans ?_ (hd x) <;> have hl := encInput_length_le x <;>
    dsimp only [extra] <;> change (encInput x).length + _ +
      ((encInput x).length + ((encInput x).length + _)) ≤ _ <;> omega

end Turing.MultiTapeTM.SignedOperandRequest
