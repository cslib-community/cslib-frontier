/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Reachability.MinIsolation.Generator.Streaming
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
public import CslibFrontier.Foundations.Data.BitString.Binary
import CslibFrontier.Algorithms.Reachability.MinIsolation.Generator.Scale
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Bit
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.FunPropFinite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import CslibFrontier.Foundations.Data.Nat.BinarySize

/-!
# Base-six accumulation from a retained binary seed rank

The ordered seed search retains a binary rank. Reading its bit at a position agrees with
the finite seed used by the generator, including zero bits above the rank's encoded width.
The accumulator visits positions in ascending order and uses the streaming digit update.

The native certificate takes a uniform code-bit routine as a hypothesis. It charges the
encoded request and the numeric seed width, which bounds the possible base-six output and
the live cursor and accumulator. The loop keeps the rank and callback context in its state.
`weightRank` adds the native layer scaling and the weight-zero rule for layer zero.
-/

public section

namespace Cslib.Reachability.Hoza.SeedRank

open Turing.MultiTapeTM ComputableInSpace

/-- A retained code context and binary candidate rank, with the scan width supplied separately. -/
structure Request (κ : Type) where
  /-- Parameters supplied to the code-bit routine. -/
  context : κ
  /-- Binary candidate number, least significant bit first in the seed order. -/
  rank : ℕ
  /-- Number of seed positions to scan. -/
  width : ℕ

variable {κ : Type}

/-- Framed context and binary rank, then the binary seed width. -/
enc_structure encRequest (encContext : κ ↪ List Bool) : Request κ where
  context : encContext, rank : encNat, width : encNat

/-- Accumulate the masked seed digits associated with a retained binary rank. -/
@[expose] def accumulateRank (code : κ → ℕ → Bool) (q : Request κ) : ℕ :=
  accumulateWeightDigits fun i : Fin q.width => code q.context i.val && q.rank.testBit i.val

/-- A bounded rank scans exactly the same bits as the ordered search's finite seed. -/
theorem accumulateRank_eq_seed (code : κ → ℕ → Bool) (ctx : κ)
    {width : ℕ} (rank : Fin (2 ^ width)) :
    accumulateRank code ⟨ctx, rank.val, width⟩ =
      accumulateWeightDigits
        (fun i => code ctx i.val && (BitString.equivFin width).symm rank i) := by
  simp only [accumulateRank, BitString.equivFin_symm_apply]

private structure Registers (κ : Type) where
  context : κ
  rank : ℕ
  cursor : ℕ
  accumulator : ℕ

private enc_structure encRegisters (encContext : κ ↪ List Bool) : Registers κ where
  context : encContext, rank : encNat, cursor : encNat, accumulator : encNat

private def init (q : Request κ) : Registers κ := ⟨q.context, q.rank, 0, 0⟩

private def step (code : κ → ℕ → Bool) (s : Registers κ) : Registers κ :=
  ⟨s.context, s.rank, s.cursor + 1,
    appendWeightDigit s.accumulator (code s.context s.cursor && s.rank.testBit s.cursor)⟩

private theorem iterate_step (code : κ → ℕ → Bool) (q : Request κ) (k : ℕ) :
    (step code)^[k] (init q) = ⟨q.context, q.rank, k, accumulateRank code {q with width := k}⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [step, accumulateRank, accumulateWeightDigits_succ,
      Fin.val_castSucc, Fin.val_last]

private theorem step_inSpace (encContext : κ ↪ List Bool) (code : κ → ℕ → Bool)
    (hc : ComputableInSpace (fun p : κ × ℕ => code p.1 p.2) (encPair encContext encNat)
      encBool (fun p => (encPair encContext encNat p).length)) :
    ComputableInSpace (step code) (encRegisters encContext) (encRegisters encContext)
      (fun s => (encRegisters encContext s).length) := by
  have hin := BigOLe.refl fun s => (encRegisters encContext s).length
  have hid := budget_id hin
  have hctx := encRegisters_context_budget encContext hid
  have hrank := encRegisters_rank_budget encContext hid
  have hi := encRegisters_cursor_budget encContext hid
  have ha := encRegisters_accumulator_budget encContext hid
  have hc' := budget_comp_linear hc (budget_prod hctx hi)
  have hb := budget_comp_lin natTestBit (linear_mul 32) (budget_prod hrank hi)
  have hd := budget_finite (encC := encNat) Bool.toNat (budget_boolAnd hc' hb)
  have hnew := budget_natAdd (budget_natMul (budget_const 6 hin) ha) hd
  exact (encRegisters_mk_budget encContext hctx hrank (budget_natSucc hi) hnew).of_enc_eq
    (fun _ => rfl)

private theorem length_iterate_le (encContext : κ ↪ List Bool) (code : κ → ℕ → Bool)
    (q : Request κ) (k : ℕ) (hk : k ≤ q.width) :
    (encRegisters encContext ((step code)^[k] (init q))).length ≤
      (encRequest encContext q).length + 5 * q.width + 1 := by
  rw [iterate_step]
  have hcur : (encNat k).length ≤ k := length_encNat_eq_size k ▸ Nat.size_le_self k
  have hacc : (encNat (accumulateRank code {q with width := k})).length ≤ 3 * k := by
    rw [length_encNat_eq_size]
    exact size_accumulateWeightDigits_le _
  simp only [encRegisters_apply, encRegistersFields, encRequest_apply, encRequestFields,
    length_encPair]
  omega

/-- With a native linear-space code-bit routine, compute the unscaled weight from a runtime seed
rank. The budget includes the numeric seed width as well as the encoded input. -/
theorem accumulateRank_inSpace [Inhabited κ] (encContext : κ ↪ List Bool) (code : κ → ℕ → Bool)
    (hc : ComputableInSpace (fun p : κ × ℕ => code p.1 p.2) (encPair encContext encNat)
      encBool (fun p => (encPair encContext encNat p).length)) :
    ComputableInSpace (accumulateRank code) (encRequest encContext) encNat
      (fun q => (encRequest encContext q).length + q.width) := by
  let : Inhabited (Registers κ) := ⟨⟨default, 0, 0, 0⟩⟩
  let B (q : Request κ) := (encRequest encContext q).length + q.width
  have hin : (fun q => (encRequest encContext q).length) ≼ B :=
    .of_le fun _ => Nat.le_add_right _ _
  have hid := budget_id hin
  have hinit : ComputableInSpace init (encRequest encContext) (encRegisters encContext) B :=
    encRegisters_mk_budget encContext (encRequest_context_budget encContext hid)
      (encRequest_rank_budget encContext hid) (budget_const 0 hin) (budget_const 0 hin)
  have hrun := budget_iterate (encRequest_width_budget encContext hid) hinit
    (step_inSpace encContext code hc) (length_iterate_le encContext code)
    (show (fun q => (encRequest encContext q).length + 5 * q.width + 1) ≼ B from
      .of_le_linear 5 1 fun _ => by dsimp [B]; omega)
  exact (encRegisters_accumulator_budget encContext hrun).of_enc_eq fun q => by
    rw [iterate_step]

/-- A retained-rank seed request and the binary layer of the vertex being weighed. -/
structure WeightRequest (κ : Type) where
  /-- Code context, rank and width for the digit scan. -/
  seed : Request κ
  /-- Layer of the original vertex. -/
  layer : ℕ

/-- Framed seed request followed by the binary layer. -/
enc_structure encWeightRequest (encContext : κ ↪ List Bool) : WeightRequest κ where
  seed : (encRequest encContext), layer : encNat

/-- Compute the scaled weight for a retained rank, with zero weight in layer zero. -/
@[expose] def weightRank (code : κ → ℕ → Bool) (q : WeightRequest κ) : ℕ :=
  if q.layer = 0 then 0
  else scaleAccumulatedWeight q.layer (accumulateRank code q.seed)

open Code.JustesenFamily in
/-- A callback that gives the executable Justesen bit at each valid index makes the retained
rank evaluator agree with the generated weight used by the isolation theorem. -/
theorem weightRank_eq_generatedWeight {w n : ℕ} (code : κ → ℕ → Bool) (ctx : κ)
    (rank : Fin (2 ^ codeLength w n)) (z : Fin (n + 1) × Fin w)
    (hcode : ∀ j : Fin (codeLength w n), code ctx j.val = indexedCodewordMod z.2 j) :
    weightRank code ⟨⟨ctx, rank.val, codeLength w n⟩, z.1.val⟩ =
      generatedWeight ((BitString.equivFin _).symm rank) z := by
  rw [← generatedWeightScan_eq,
    ← SeedDigits.scaledMaskedPrefix_eq_generatedWeightScan _ z (code ctx) hcode]
  simp only [weightRank, List.length_ofFn, SeedDigits.maskedPrefix_ofFn, accumulateRank_eq_seed]

/-- Compute the scaled weight with a supplied native code-bit routine. The seed width is charged
numerically, while the layer, context and rank are charged through the input encoding. -/
theorem weightRank_inSpace [Inhabited κ] (encContext : κ ↪ List Bool) (code : κ → ℕ → Bool)
    (hc : ComputableInSpace (fun p : κ × ℕ => code p.1 p.2) (encPair encContext encNat)
      encBool (fun p => (encPair encContext encNat p).length)) :
    ComputableInSpace (weightRank code) (encWeightRequest encContext) encNat
      (fun q => (encWeightRequest encContext q).length + q.seed.width) := by
  let B (q : WeightRequest κ) := (encWeightRequest encContext q).length + q.seed.width
  have hin : (fun q => (encWeightRequest encContext q).length) ≼ B :=
    .of_le fun _ => Nat.le_add_right _ _
  have hid := budget_id hin
  have hs := encWeightRequest_seed_budget encContext hid
  have hl := encWeightRequest_layer_budget encContext hid
  have hwidth : (fun q : WeightRequest κ =>
      (encRequest encContext q.seed).length + q.seed.width) ≼ B := by
    refine .of_le fun q => ?_
    simp only [B, encWeightRequest_apply, encWeightRequestFields, length_encPair]
    omega
  have ha := budget_comp (accumulateRank_inSpace encContext code hc) hs hwidth
  have hw := budget_comp_linear scaleAccumulatedWeight_inSpace (budget_prod hl ha)
  exact (budget_ite (budget_natIsZero hl) (budget_const 0 hin) hw).of_enc_eq fun q => by
    simp [weightRank]

end Cslib.Reachability.Hoza.SeedRank
