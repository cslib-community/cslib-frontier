/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.IntervalCount.PolyTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary.Decode
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Max
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListBinaryLookup
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimePiPrimitives
import CslibFrontier.Foundations.Data.List.Lookup

/-!
# Decoding interval data on a native count branch

`IntervalData.decoder` parses the existing interval encoding, retaining its source word, unary
block width and offsets, binary head positions, and finite tables. It is total on arbitrary
words and inverts every encoded interval record. The alternating interval counter uses it when
replaying the coin string selected by its count tree.
-/

public section

namespace Turing.MultiTapePTM.IntervalData

open MultiTapeTM ComputableInPolyTime MultiTapeNTM.ChoiceTable

private noncomputable def finiteDecoder (α : Type) [Finite α] [Nonempty α] :
    Decoder (encFinite α) :=
  let _ := Fintype.ofFinite α
  let value (n : ℕ) : α := (Fintype.equivFin α).symm
    ⟨min n (Fintype.card α - 1), by have := Fintype.card_pos (α := α); omega⟩
  { decode := fun w => value w.length
    decode_enc := fun a => by
      apply (Fintype.equivFin α).injective
      apply Fin.ext
      simp only [value, Equiv.apply_symm_apply, encFinite,
        Function.Embedding.coeFn_mk, encUnary_apply, List.length_replicate]
      have := (Fintype.equivFin α a).isLt
      omega
    computable := by
      have h := unary_min' length_bits (const (Fintype.card α - 1))
      have he (w : List Bool) : encFinite α (value w.length) =
          encUnary (min w.length (Fintype.card α - 1)) := by
        simp [encFinite, value]
      exact (h.of_enc_eq he).exists_degree }

private noncomputable def piDecoder {α β : Type} [Fintype α] {enc : β ↪ List Bool}
    (D : Decoder enc) : Decoder (encPi (Index := α) enc) where
  decode w i := (D.list.decode w).getD (Fintype.equivFin α i).val (D.decode [])
  decode_enc f := by
    funext i
    rw [encPi_apply, D.list.decode_enc, List.getD_ofFn]
    simp
  computable := (pi fun i => listGetD_binary (D.decode []) D.list.computableInPolyTime
    (const (Fintype.equivFin α i).val)).exists_degree

private noncomputable def controlDecoder {k : ℕ} {State : Type} [Finite State] :
    Decoder (encControlData (k := k) (State := State)) :=
  let _ : Nonempty OutputTrack := ⟨.empty⟩
  ((finiteDecoder (Option State)).pair
    ((piDecoder Decoder.unary).pair (finiteDecoder OutputTrack))).map id id
      (fun _ => rfl) (fun a => encControlData_apply a)

/-- Parse all eight fields in the unchanged interval encoding. Finite ranks are clamped,
missing table entries use their component decoder's default, and every encoded record
round-trips. -/
noncomputable def decoder {k : ℕ} {State : Type} [Finite State] :
    Decoder (encIntervalData (k := k) (State := State)) :=
  (Decoder.bits.pair (Decoder.unary.pair ((piDecoder Decoder.intBin).pair
    ((finiteDecoder (Option (Fin k) → SignType)).pair (controlDecoder.pair
      ((piDecoder (Decoder.list (Decoder.option Decoder.bool))).pair (controlDecoder.pair
        (piDecoder (Decoder.list (Decoder.option Decoder.bool)))))))))).map
    IntervalData.equivProd.symm IntervalData.equivProd (fun _ => rfl)
      (fun a => encIntervalData_apply (IntervalData.equivProd.symm a))

end Turing.MultiTapePTM.IntervalData
