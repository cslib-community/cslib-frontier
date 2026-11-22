/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.IntervalCount.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.BitString.Cut
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Envelope
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimePiPrimitives

/-!
# Native extraction of the source window for interval counting

The source word is scanned and cut with linear native operations. Arithmetic uses only the
remaining interval fields and the binary source length. The prepared record contains at most
`2 * b + 1` input symbols, a binary origin and a unary position at most `b + 1`.

`exists_prepare_inO` is the resource certificate consumed by the native interval counter.
`prepare_length_le` bounds the short record on which that counter replays each selected witness.
-/

public section

namespace Turing.MultiTapePTM.IntervalData

open MultiTapeTM ComputableInPolyTime

variable {k : ℕ} {State : Type} [Finite State]

private noncomputable abbrev encFields :
    (List Bool × ℕ × (Option (Fin k) → ℤ) × (Option (Fin k) → SignType) × ControlData k State ×
      (Fin k → List (Option Bool)) × ControlData k State × (Fin k → List (Option Bool))) ↪
        List Bool :=
  encPair encBits (encPair encUnary (encPair (encPi encIntBin)
    (encPair (encFinite (Option (Fin k) → SignType)) (encPair (encControlData (State := State))
      (encPair (encPi (encList (encOption encBool))) (encPair encControlData
        (encPi (encList (encOption encBool)))))))))

private theorem fields_deg : ComputableInDegree
    (IntervalData.equivProd (k := k) (State := State)) encIntervalData encFields 1 1 :=
  .of_eq fun d => (encIntervalData_apply d).symm

private theorem input_deg : ComputableInDegree (IntervalData.input (k := k) (State := State))
    encIntervalData encBits 1 1 := fields_deg.fst'

/-- Replacing the source field preserves all interval metadata and takes linear encoded time. -/
theorem replaceInput_deg : ComputableInDegree
    (fun a : IntervalData k State × List Bool => { a.1 with input := a.2 })
    (encPair encIntervalData encBits) encIntervalData 1 1 := by
  have hd := fields_deg.comp (ComputableInDegree.fst
    (encIntervalData (k := k) (State := State)) encBits)
  exact ((ComputableInDegree.snd encIntervalData encBits).prod hd.snd').of_enc_eq
    (fun _ => encIntervalData_apply _)

namespace InputWindow

private def strip (d : IntervalData k State) : IntervalData k State := { d with input := [] }

/-- Removing the source field preserves all interval metadata and takes linear encoded time. -/
theorem stripInput_deg : ComputableInDegree (fun d : IntervalData k State => { d with input := [] })
    encIntervalData encIntervalData 1 1 := by
  exact replaceInput_deg.comp (ComputableInDegree.id'.prod
    ((ComputableInDegree.const (encMid := encBits) []).mono (d' := 1) (e' := 1)))

private theorem length_eq (d : IntervalData k State) :
    (encIntervalData d).length = 2 * d.input.length + (encIntervalData (strip d)).length := by
  simp only [encIntervalData_apply, IntervalData.equivProd, Equiv.coe_fn_mk, strip,
    length_encPair, encBits_apply, List.length_nil]
  omega

private theorem width_le (d : IntervalData k State) : d.b ≤ (encIntervalData (strip d)).length := by
  rw [encIntervalData_apply]
  simp only [IntervalData.equivProd, Equiv.coe_fn_mk, strip, length_encPair,
    encBits_apply, List.length_nil, encUnary_apply, List.length_replicate]
  omega

private def header (d : IntervalData k State) : IntervalData k State × ℕ :=
  (strip d, d.input.length)

private theorem header_inO : ComputableInO (header (k := k) (State := State)) encIntervalData
    (encPair encIntervalData encNat) (fun d => (encIntervalData d).length)
      (fun d => (encIntervalData d).length) := by
  have h := (stripInput_deg (k := k) (State := State)).inO_one.prod
    (ComputableInO.lengthNat.comp input_deg.inO_one)
  exact h.mono 3 (fun d => by have := length_eq d; omega)
    (fun d => by have := length_eq d; omega)

private structure Cut where
  origin : ℕ
  position : ℕ
  width : ℕ

/-- The absolute cut is binary; the relative position and bounded window width are unary. -/
private enc_structure encCut : Cut where origin : encNat, position : encUnary, width : encUnary

private def initialPosition (a : IntervalData k State × ℕ) : ℕ :=
  let z := (a.1.b : ℤ) * a.1.J none + a.1.cIn.2.1 none + 1
  if !decide (z < 0) && decide (z - (a.2 + 2) < 0) then z.toNat else 0

private def cut (a : IntervalData k State × ℕ) : Cut :=
  ⟨initialPosition a - (a.1.b + 1), min (a.1.b + 1) (initialPosition a), 2 * a.1.b + 1⟩

private theorem cut_polyTime : ComputableInPolyTime (cut (k := k) (State := State))
    (encPair encIntervalData encNat) encCut := by
  have hd := fields_deg.computableInPolyTime.comp
    (fst (encIntervalData (k := k) (State := State)) encNat)
  have hb := hd.snd'.fst'
  have hJ := hd.snd'.snd'.fst'
  have hcIn := hd.snd'.snd'.snd'.snd'.fst'
  have hcontrol : ComputableInPolyTime (fun a : IntervalData k State × ℕ => a.1.cIn)
      (encPair encIntervalData encNat)
      (encPair (encFinite (Option State)) (encPair (encPi encUnary)
        (encFinite MultiTapeNTM.ChoiceTable.OutputTrack))) :=
    hcIn.of_enc_eq (fun a => (encControlData_apply a.1.cIn).symm)
  have hz := intBin_add'
    (intBin_add' (intBin_mul' (intBin_natCast.comp (unary_to_binary.comp hb))
      ((pi_apply _ none).comp hJ))
      (intBin_natCast.comp (unary_to_binary.comp ((pi_apply _ none).comp hcontrol.snd'.fst'))))
    (const 1)
  have hn := intBin_add' (intBin_natCast.comp
    (snd (encIntervalData (k := k) (State := State)) encNat)) (const 2)
  have hp : ComputableInPolyTime (initialPosition (k := k) (State := State))
      (encPair encIntervalData encNat) encNat :=
    ite (bool_and' (bool_not.comp (intBin_isNeg.comp hz))
      (intBin_isNeg.comp (intBin_sub.comp (hz.prod hn)))) (intBin_toNat.comp hz) (const 0)
  have hw := unary_add' hb (const 1)
  exact encCut_mk_polyTime (binary_sub' hp (unary_to_binary.comp hw))
    (binary_min_unary' hw hp) (unary_add' (unary_mul' (const 2) hb) (const 1))

omit [Finite State] in
private theorem position_header (d : IntervalData k State) :
    initialPosition (header d) =
      (inputPosOfCoord d.input ((d.b : ℤ) * d.J none + d.cIn.2.1 none)).val := by
  rw [val_inputPosOfCoord]
  dsimp only [initialPosition, header, strip]
  split_ifs with h
  · simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      decide_eq_true_eq, not_lt] at h
    symm
    apply Nat.min_eq_right
    omega
  · rfl

omit [Finite State] in
private theorem cut_origin_le (d : IntervalData k State) :
    (cut (header d)).origin ≤ d.input.length := by
  have hp := (inputPosOfCoord d.input ((d.b : ℤ) * d.J none + d.cIn.2.1 none)).isLt
  simp only [cut, position_header]
  omega

/-- The prepared record's encoded length depends only on the interval metadata and the binary
source length; the source substring and relative input position are bounded by the block width. -/
theorem prepare_length_le (d : IntervalData k State) :
    (encInputWindow (prepare d)).length ≤
      20 * ((encIntervalData { d with input := [] }).length + d.input.length.size + 1) := by
  let p := (inputPosOfCoord d.input ((d.b : ℤ) * d.J none + d.cIn.2.1 none)).val
  let a := p - (d.b + 1)
  have hp : p ≤ d.input.length + 1 := Nat.le_of_lt_succ (inputPosOfCoord d.input _).isLt
  have ha : a ≤ d.input.length := by dsimp [a]; omega
  have hpos : p - a ≤ d.b + 1 := by dsimp [a]; omega
  have hword : ((d.input.drop a).take (2 * d.b + 1)).length ≤ 2 * d.b + 1 :=
    List.length_take_le _ _
  have hb := width_le d
  have hs := Nat.size_le_size ha
  have hl := length_eq { d with input := (d.input.drop a).take (2 * d.b + 1) }
  change (encInputWindow ⟨{ d with input := (d.input.drop a).take (2 * d.b + 1) }, a, p - a⟩).length
    ≤ _
  simp only [encInputWindow_apply, encInputWindowFields, length_encPair, encNat_apply,
    Nat.size_eq_bits_len, encUnary_apply, List.length_replicate]
  dsimp only [strip] at hl hb
  omega

/-- Extract the actual source window in linear source length plus a fixed polynomial of the
metadata and binary source length. The same bound covers native time and charged workspace. -/
theorem exists_prepare_inO : ∃ D, let budget := fun d : IntervalData k State =>
    d.input.length + ((encIntervalData { d with input := [] }).length + d.input.length.size + 1) ^ D
    ComputableInO prepare encIntervalData encInputWindow budget budget := by
  obtain ⟨T, S, hT, hS, hs⟩ := cut_polyTime (k := k) (State := State) |>.exists_computableInO
  have hc := hs.comp header_inO
  have horigin := encCut_origin_deg.inO_one.comp_linear hc
  have hu := ComputableInO.natToUnary.comp horigin
  have hdrop := ComputableInDegree.bitsDrop.inO_one.comp_linear (input_deg.inO_one.prod hu)
  have htake := ComputableInDegree.bitsTake.inO_one.comp_linear
    (hdrop.prod (encCut_width_deg.inO_one.comp_linear hc))
  have hdata := replaceInput_deg.inO_one.comp_linear (stripInput_deg.inO_one.prod htake)
  have hprep := encInputWindow_mk_deg.inO_one.comp_linear
    (hdata.prod (horigin.prod (encCut_position_deg.inO_one.comp_linear hc)))
  have heq (d : IntervalData k State) :
      (⟨{ strip d with input :=
          (d.input.drop (cut (header d)).origin).take (cut (header d)).width },
        (cut (header d)).origin, (cut (header d)).position⟩ : InputWindow k State) = prepare d := by
    rcases hIn : d.cIn with ⟨state, offsets, track⟩
    simp only [cut, position_header]
    simp only [prepare, strip, header, hIn]
    congr 1
    omega
  have h := hprep.of_enc_eq (g := prepare) (encC := encInputWindow) (fun d => by
    exact congrArg encInputWindow (heq d).symm)
  let size := fun d : IntervalData k State =>
    (encIntervalData (strip d)).length + d.input.length.size + 1
  have hh : PolyBounded size (fun d => (encPair encIntervalData encNat (header d)).length) := by
    apply PolyBounded.of_forall_le 3 1
    intro d
    simp only [header, length_encPair, encNat_apply, Nat.size_eq_bits_len, pow_one]
    dsimp [size]
    omega
  let extra := fun d : IntervalData k State =>
    20 * ((encIntervalData (strip d)).length + T (header d) + S (header d) + 1)
  have he : PolyBounded size extra :=
    (PolyBounded.const 20).mul
      ((((PolyBounded.self.mono (fun _ => by dsimp [size]; omega)).add (hT.comp hh)).add
        (hS.comp hh)).add (.const 1))
  obtain ⟨c, D, hd⟩ := he.exists_le_linear_add_pow (fun d => d.input.length) 40
    (fun d => by dsimp [size]; omega)
  refine ⟨D, h.mono c (fun d => ?_) (fun d => ?_)⟩ <;>
    refine le_trans ?_ (hd d) <;>
    have hl := length_eq d <;> have ho := cut_origin_le d <;>
    dsimp only [extra, Function.comp_apply] <;> omega

end InputWindow

end Turing.MultiTapePTM.IntervalData
