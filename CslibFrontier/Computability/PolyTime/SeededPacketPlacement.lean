/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.SeededPacketLocation
public import CslibFrontier.Computability.PolyTime.SeededPredecessorFinish
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Seeded local packet placement from vertex keys

The machine computes both labels of a numbered edge with the same four coefficients, then
places it using its supplied binary class rank. For the true rank this gives its packet
and slot in the seeded packing of the whole graph.
-/

public section

namespace Cslib.SeededPacketPlacement

open Turing.MultiTapeTM ComputableInPolyTime PacketPacking BalancedSchedules

/-- The retained seed context, vertex keys and the verified or proposed class rank. -/
structure Input where
  /-- The common seed and graph universe. -/
  context : SeededPredecessor.Context
  /-- Tagged key of the row endpoint. -/
  row : ℕ
  /-- Tagged key of the column endpoint. -/
  column : ℕ
  /-- Class rank used by both packet and slot computations. -/
  rank : ℕ

/-- The row and column vertex numbers and the class rank all use binary encodings. -/
enc_structure encInput : Input where
  context : SeededPredecessor.encContext, row : encNat, column : encNat, rank : encNat

/-- The integer label code of a vertex key, before expansion into alphabet-64 digits. -/
@[expose] def code (c : SeededPredecessor.Context) (v : ℕ) : ℕ :=
  TrinomialArithmetic.runSelected
    ⟨c.universeSize, 6 * c.labelLength, c.c0, c.c1, c.c2, c.c3, v⟩

/-- Every numeric key has a bounded code, even outside the represented graph's vertex range.
This supplies the total label map required when defining a recursive graph split. -/
@[expose] def boundedCode (c : SeededPredecessor.Context) (v : ℕ) :
    Fin (2 ^ (6 * c.labelLength)) :=
  ⟨code c v, Nat.mod_lt _ (by positivity)⟩

/-- Compute the seeded packet and slot using the same rank and label codes. -/
@[expose] def run (p : Input) : ℕ × ℕ :=
  SeededPacketLocation.run
    ⟨p.context.labelLength, code p.context p.row, code p.context p.column, p.rank⟩

/-- The fixed seed computes its mathematical integer label at every valid tagged vertex. -/
theorem code_eq (U a : ℕ) (seed : SeededLabels.Seed U (6 * a))
    (v : Fin U) (oldEdge oldCandidate : ℕ) :
    code ⟨U, a, seed 0, seed 1, seed 2, seed 3, oldEdge, oldCandidate⟩ v.val =
      (SeededLabels.label U (6 * a) seed v).val :=
  TrinomialArithmetic.runSelected_eq U (6 * a) seed v

/-- Using the correct class rank gives this edge's actual packet and slot of the seeded
packing, uniformly over arbitrary finite ordered edge types. -/
theorem run_of_seed {E R C : Type*} [Fintype E] [LinearOrder E]
    (U a : ℕ) (vertex : R ⊕ C ↪ Fin U) (rows : E → R) (cols : E → C)
    (seed : SeededLabels.Seed U (6 * a)) (e : E) (oldEdge oldCandidate : ℕ) :
    let row := fun v => Seeded.label U a seed (vertex (.inl v))
    let col := fun v => Seeded.label U a seed (vertex (.inr v))
    run ⟨⟨U, a, seed 0, seed 1, seed 2, seed 3, oldEdge, oldCandidate⟩,
      (vertex (.inl (rows e))).val, (vertex (.inr (cols e))).val,
      Seeded.rank U a vertex rows cols seed e⟩ =
      (((Packing.ofLabels rows cols row col).packet e).val,
        ((Packing.ofLabels rows cols row col).slot e).val) := by
  dsimp only [run]
  rw [code_eq U a seed (vertex (.inl (rows e))), code_eq U a seed (vertex (.inr (cols e)))]
  exact SeededPacketLocation.run_of_codes a rows cols
    (fun v => SeededLabels.label U (6 * a) seed (vertex (.inl v)))
    (fun v => SeededLabels.label U (6 * a) seed (vertex (.inr v))) e

/-- Evaluate a computed vertex key with a computed shared seed. -/
theorem computableInPolyTime_code {α : Type} {enc : α ↪ List Bool}
    {ctx : α → SeededPredecessor.Context} {v : α → ℕ}
    (hc : ComputableInPolyTime ctx enc SeededPredecessor.encContext)
    (hv : ComputableInPolyTime v enc encNat) :
    ComputableInPolyTime (fun x => code (ctx x) (v x)) enc encNat := by
  open SeededPredecessor in
  exact TrinomialArithmetic.computableInPolyTime_runSelected.comp
    (TrinomialArithmetic.encSelectedInput_mk_polyTime (encContext_universeSize_polyTime hc)
      (unary_mul' (const 6) (encContext_labelLength_polyTime hc))
      (encContext_c0_polyTime hc) (encContext_c1_polyTime hc) (encContext_c2_polyTime hc)
      (encContext_c3_polyTime hc) hv)

/-- The real machine charges both seed evaluations and binary-rank placement. -/
theorem computableInPolyTime_run : ComputableInPolyTime run encInput (encPair encNat encNat) := by
  have hc := encInput_context_deg.computableInPolyTime
  exact SeededPacketLocation.computableInPolyTime_run.comp
    (SeededPacketLocation.encInput_mk_polyTime
      (SeededPredecessor.encContext_labelLength_polyTime hc)
      (computableInPolyTime_code hc encInput_row_deg.computableInPolyTime)
      (computableInPolyTime_code hc encInput_column_deg.computableInPolyTime)
      encInput_rank_deg.computableInPolyTime)

end Cslib.SeededPacketPlacement
