/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.DescendantEndpoint
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RootEndpointCheck
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Cases

/-!
# The native terminal of a compressed descendant endpoint query

The root schedule is read only after all short recursive routing is complete. A finished local
verdict returns its Boolean value; otherwise the terminal invokes the actual root endpoint
algorithm. Serializing the protected schedule and final short query is charged linearly.
-/

public section

namespace Turing.MultiTapeATM.DescendantEndpointTerminal

open MultiTapeTM DescendantEndpoint

/-- A framed raw schedule followed by the short endpoint position. -/
abbrev encInput := encPair encBits encPosition

/-- Binary metadata of the ground lookup, including the length of the protected schedule. -/
@[expose] def shortSize (a : List Bool × Position) : ℕ :=
  (encPosition a.2).length + a.1.length.size + 1

/-- Assemble the one root request after the frame stack has been discharged. -/
@[expose] def queryInput (a : List Bool × Position) : RootEndpointCheck.Input :=
  ((a.2.row, a.2.column), ⟨a.1, a.2.copies, a.2.edge⟩)

/-- A closed local verdict, or the actual root endpoint equality on the original schedule. -/
@[expose] def check (k : ℕ) (a : List Bool × Position) : Bool :=
  a.2.verdict.elim (RootEndpointCheck.check k (queryInput a)) id

/-- The ground predicate returns a local verdict or compares the native root endpoint pair. -/
theorem check_eq_true_iff (k : ℕ) (raw : List Bool) (p : Position) :
    check k (raw, p) = true ↔ p.verdict.elim
      (RootEndpointQuery.query k ⟨raw, p.copies, p.edge⟩ = some (p.row, p.column))
      (fun verdict => verdict = true) := by
  cases hv : p.verdict with
  | none =>
    simp only [check, hv, Option.elim_none, RootEndpointCheck.check, queryInput]
    exact ⟨of_decide_eq_true, decide_eq_true⟩
  | some verdict =>
    simp only [check, hv, Option.elim_some]
    rfl

private theorem queryInput_deg : ComputableInDegree queryInput encInput
    RootEndpointCheck.encInput 1 1 := by
  have hp := ComputableInDegree.snd encBits encPosition
  have hw := ComputableInDegree.fst encBits encPosition
  exact ((encPosition_row_deg.comp hp).prod (encPosition_column_deg.comp hp)).prod
    (RootEndpointInput.encInput_mk_deg.comp
      (hw.prod ((encPosition_copies_deg.comp hp).prod (encPosition_edge_deg.comp hp))))

private theorem short_query_le (a : List Bool × Position) :
    RootEndpointCheck.shortSize (queryInput a) ≤ 4 * shortSize a := by
  simp only [RootEndpointCheck.shortSize, RootEndpointCheck.encEnds, queryInput,
    RootEndpointInput.shortSize, shortSize, encPosition_apply, encPositionFields,
    length_encPair, encNat_apply, Nat.size_eq_bits_len]
  omega

/-- The total terminal predicate has a native clock linear in the raw schedule and polynomial
only in its binary length and the short position. -/
theorem exists_computableInO (k : ℕ) : ∃ d, ComputableInO (check k) encInput encBool
    (fun a => a.1.length + shortSize a ^ d) (fun a => a.1.length + shortSize a ^ d) := by
  obtain ⟨d, hr⟩ := RootEndpointCheck.exists_computableInO k
  have hq := hr.comp queryInput_deg.inO_one
  have hb := (ComputableInDegree.snd encInput encBool).inO_one
  have hc := hq.optionElimSnd hb
  have hp := ComputableInDegree.snd encBits encPosition
  have hprep := ((ComputableInDegree.id' (enc := encInput)).prod
    (encPosition_verdict_deg.comp hp)).inO_one
  have h := hc.comp hprep
  let D := max 1 d
  have hsize (a : List Bool × Position) : 1 ≤ shortSize a := by dsimp [shortSize]; omega
  have hlinear (a : List Bool × Position) : shortSize a ≤ shortSize a ^ D := by
    simpa only [pow_one] using Nat.pow_le_pow_right (hsize a) (Nat.le_max_left 1 d)
  have hpow (a : List Bool × Position) :
      RootEndpointCheck.shortSize (queryInput a) ^ d ≤ 4 ^ d * shortSize a ^ D := by
    calc
      _ ≤ (4 * shortSize a) ^ d := Nat.pow_le_pow_left (short_query_le a) d
      _ = 4 ^ d * shortSize a ^ d := Nat.mul_pow ..
      _ ≤ _ := Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right (hsize a) (Nat.le_max_right 1 d))
  refine ⟨D, (h.of_enc_eq (g := check k) (fun _ => rfl)).mono (30 + 4 ^ d)
    (fun a => ?_) (fun a => ?_)⟩ <;>
    have hl := hlinear a <;> have hp := hpow a
  all_goals
    calc
      _ ≤ 30 * (a.1.length + shortSize a ^ D + 1) + 4 ^ d * shortSize a ^ D := by
        cases hv : a.2.verdict <;>
          simp only [Function.comp_apply, Option.elim_none, Option.elim_some, encInput,
            length_encPair, encBits_apply, encOption_none, encOption_some, encBool_apply,
            List.length_nil, List.length_cons, queryInput, hv, shortSize] at hl hp ⊢ <;> omega
      _ ≤ (30 + 4 ^ d) * (a.1.length + shortSize a ^ D + 1) := by
        rw [Nat.add_mul]
        exact Nat.add_le_add_left (Nat.mul_le_mul_left (4 ^ d) (by omega)) _

end Turing.MultiTapeATM.DescendantEndpointTerminal
