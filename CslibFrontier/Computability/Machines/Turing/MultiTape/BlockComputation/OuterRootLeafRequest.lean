/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RootBalanceRequest
public import CslibFrontier.Computability.PolyTime.CountingLeaf.Raw
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleValidationNative
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.BitString.Cut
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Envelope

/-!
# Preparing the outer schedule leaf without polynomial work on its path

The protected context has the typed root template. The count tape for `2^h` has `h+1`
cells, providing an exact length check on the raw schedule. Even when an arbitrary physical
index has a long zero padding, the short computation sees at most the precision word's
length of its low bits. The path itself is copied and validated in a constant number of scans.
-/

public section

namespace Turing.MultiTapeTM.OuterRootLeafRequest

open Cslib ComputableInPolyTime

/-- The six physical serializer fields with the protected context interpreted as a root template. -/
structure Input where
  template : RootBalanceRequest.Public
  count : List Bool
  width : List Bool
  path : List Bool
  carry : Bool
  bit : List Bool

enc_structure encInput : Input where
  template : RootBalanceRequest.encPublic, count : encBits, width : encBits, path : encBits,
  carry : encBool, bit : encBits

/-- The existing serializer writes exactly this word, with the same final unframed index. -/
theorem encInput_eq (x : Input) : encInput x = CountingLeaf.encRawInput
    ⟨RootBalanceRequest.encPublic x.template, x.count, x.width, x.path, x.carry, x.bit⟩ := rfl

/-- Only these fields enter the polynomial-time part of the leaf dispatcher. -/
structure Data where
  context : SeededPredecessor.Context
  width : List Bool
  clipped : List Bool
  countLength : ℕ
  pathLength : ℕ
  valid : Bool
  carry : Bool

enc_structure encData : Data where
  context : SeededPredecessor.encContext, width : encBits, clipped : encBits, countLength : encNat,
  pathLength : encNat, valid : encBool, carry : encBool

/-- The binary count and path lengths remain short; the full words are not forwarded. -/
@[expose] def data (k : ℕ) (x : Input) : Data :=
  ⟨x.template.1.context, x.width, x.bit.take x.width.length, x.count.length, x.path.length,
    ScheduleBits.validate k x.path, x.carry⟩

/-- Carry components, malformed schedules and padded indices use the zero leaf. -/
@[expose] def active (z : Data) : Bool :=
  !z.carry && z.valid && decide (z.pathLength + 1 = z.countLength) &&
    decide (ofBits z.clipped < ofBits z.width)

/-- Write the chosen bit and its sign to the public template, retaining its zero seed. -/
@[expose] def setIndex (claim : Bool) (z : Data) : SeededPredecessor.Context :=
  {z.context with edge := ofBits z.clipped, candidate := claim.toNat}

/-- Replace the empty raw field by the actual persistent path. -/
@[expose] def publicRequest (k : ℕ) (claim : Bool) (x : Input) : RootBalanceRequest.Public :=
  (⟨x.path, x.template.1.copies, setIndex claim (data k x)⟩, x.template.2)

/-- The three dispatch bits tell the physical reader when to enter the seeded root verifier. -/
@[expose] def word (k : ℕ) (claim : Bool) (x : Input) : List Bool :=
  [active (data k x), false, !claim] ++ RootBalanceRequest.encPublic (publicRequest k claim x)

/-- Combined length of the three potentially long fields. -/
@[expose] def longSize (x : Input) : ℕ := x.count.length + x.path.length + x.bit.length

/-- The remaining work only depends on the template, binary lengths and precision digits. -/
@[expose] def shortSize (x : Input) : ℕ :=
  (RootBalanceRequest.encPublic x.template).length + x.count.length.size + x.path.length.size +
    x.width.length + 1

private theorem data_deg (k : ℕ) : ComputableInDegree (data k) encInput encData 1 1 := by
  have hn : ComputableInDegree List.length encBits encNat 1 1 :=
    ComputableInO.lengthNat.computableInDegree DegreeBounded.self DegreeBounded.self le_rfl
  have hu : ComputableInDegree List.length encBits encUnary 1 1 :=
    ComputableInO.lengthUnary.computableInDegree DegreeBounded.self DegreeBounded.self le_rfl
  have hv : ComputableInDegree (ScheduleBits.validate k) encBits encBool 1 1 :=
    .of_transducer (ScheduleValidation.reader k) fun w =>
      (ScheduleValidation.run_eq_validate k w).symm
  have hg := (ComputableInDegree.fst RootPredecessorQuery.encInput encNat).comp
    encInput_template_deg
  have hc := RootPredecessorQuery.encInput_context_deg.comp hg
  have hb := ComputableInDegree.bitsTake.comp (encInput_bit_deg.prod (hu.comp encInput_width_deg))
  exact encData_mk_deg.comp (hc.prod (encInput_width_deg.prod (hb.prod
    ((hn.comp encInput_count_deg).prod ((hn.comp encInput_path_deg).prod
      ((hv.comp encInput_path_deg).prod encInput_carry_deg))))))

private theorem data_size (k : ℕ) :
    PolyBounded shortSize (fun x => (encData (data k x)).length) := by
  apply PolyBounded.of_forall_le 8 1
  intro x
  have hclip := List.length_take_le x.width.length x.bit
  simp only [data, encData_apply, encDataFields, shortSize, RootBalanceRequest.encPublic,
    length_encPair, RootPredecessorQuery.length_encInput, encBits_apply, encNat_apply,
    Nat.size_eq_bits_len, encBool_apply, List.length_singleton, pow_one]
  omega

private theorem compiled_poly (claim : Bool) : ComputableInPolyTime
    (fun z => ([active z, false, !claim], setIndex claim z)) encData
      (encPair encBits SeededPredecessor.encContext) := by
  have hc := encData_context_deg.computableInPolyTime
  have hb := bitsToNat.comp encData_clipped_deg.computableInPolyTime
  have hw := bitsToNat.comp encData_width_deg.computableInPolyTime
  have hl := decide_eq' (binary_add' encData_pathLength_deg.computableInPolyTime (const 1))
    encData_countLength_deg.computableInPolyTime
  have hactive : ComputableInPolyTime active encData encBool :=
    bool_and' (bool_and' (bool_and' (bool_not.comp encData_carry_deg.computableInPolyTime)
      encData_valid_deg.computableInPolyTime) hl) (binary_lt' hb hw)
  have hflag : ComputableInPolyTime (fun b : Bool => [b, false, !claim]) encBool encBits :=
    of_finite _
  exact (hflag.comp hactive).prod (SeededPredecessor.encContext_mk_polyTime
    (SeededPredecessor.encContext_universeSize_polyTime hc)
    (SeededPredecessor.encContext_labelLength_polyTime hc)
    (SeededPredecessor.encContext_c0_polyTime hc) (SeededPredecessor.encContext_c1_polyTime hc)
    (SeededPredecessor.encContext_c2_polyTime hc) (SeededPredecessor.encContext_c3_polyTime hc)
    hb (const claim.toNat))

/-- The serializer output is linear in the long fields and protected metadata. -/
theorem encInput_length_le (x : Input) :
    (encInput x).length ≤ 4 * (longSize x + shortSize x + 3) := by
  simp only [encInput_apply, encInputFields, shortSize, longSize, length_encPair, encBool_apply,
    encBits_apply, List.length_singleton]
  omega

/-- The guarded dispatch word is computed natively with a linear charge for all long inputs. -/
theorem exists_word_inO (k : ℕ) (claim : Bool) : ∃ d, ComputableInO (word k claim) encInput encBits
    (fun x => longSize x + shortSize x ^ d) (fun x => longSize x + shortSize x ^ d) := by
  obtain ⟨T, S, hT, hS, hs⟩ := (compiled_poly claim).exists_computableInO
  have h := hs.comp (data_deg k).inO_one
  have hf := (ComputableInDegree.fst encBits SeededPredecessor.encContext).inO_one.comp_linear h
  have hc := (ComputableInDegree.snd encBits SeededPredecessor.encContext).inO_one.comp_linear h
  have hg := (ComputableInDegree.fst RootPredecessorQuery.encInput encNat).comp
    encInput_template_deg
  have hm := (RootPredecessorQuery.encInput_copies_deg.comp hg).inO_one
  have hn := ((ComputableInDegree.snd RootPredecessorQuery.encInput encNat).comp
    encInput_template_deg).inO_one
  have hgraph := (encInput_path_deg.inO_one.prod (hm.prod hc)).of_enc_eq
    (g := fun x => (publicRequest k claim x).1) (encC := RootPredecessorQuery.encInput)
    (fun _ => rfl)
  have hw := hf.append (hgraph.prod hn) (g := word k claim) (encOut := encBits) (fun _ => rfl)
  let small (x : Input) := 24 * (shortSize x + 3) + 2 * (T (data k x) + S (data k x))
  have hsmall : PolyBounded shortSize small :=
    ((PolyBounded.const 24).mul (PolyBounded.self.add (.const 3))).add
      ((PolyBounded.const 2).mul ((hT.comp (data_size k)).add (hS.comp (data_size k))))
  obtain ⟨c, d, hu⟩ := hsmall.exists_le_linear_add_pow longSize 24 (fun x => by simp [shortSize])
  refine ⟨d, hw.mono c (fun x => ?_) (fun x => ?_)⟩ <;>
    refine le_trans ?_ (hu x) <;> have hl := encInput_length_le x <;>
    change (encInput x).length + _ + ((encInput x).length + ((encInput x).length +
      ((encInput x).length + _)) + (encInput x).length) ≤ 24 * longSize x + small x <;>
    dsimp only [small] <;> omega

end Turing.MultiTapeTM.OuterRootLeafRequest
