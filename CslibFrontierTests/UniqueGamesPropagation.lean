/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.PCP.Approximation.UniqueGames.PropagationTime
meta import CslibFrontier.Computability.PCP.Approximation.UniqueGames.PropagationTime
meta import CslibFrontier.Computability.WordRAM.Structured.FastEval

/-!
# Label propagation for unique games: worked examples

Kernel-checked runs of `Cslib.Complexity.UniqueGames.Propagation.solve` and Word-RAM execution
checks of `Cslib.Complexity.UniqueGames.Propagation.solveCode` / `program`:

* a satisfiable 3-cycle of rotations, the same cycle with its edges reversed (so that propagation
  inverts the bijections), and an unsatisfiable variant;
* the odd and even cycles of negations over two labels, i.e. 2-colouring a triangle and a square;
  the triangle is also a no-instance of `GapUniqueGames Bool 1 s` for `2/3 ≤ s < 1`;
* a disconnected instance, whose second component pins its seed's label by a loop;
* edges outside the declared vertex range, the empty instance, the single-label (`L = 1`) case,
  and conflicting parallel edges;
* a satisfiable instance with non-injective tables on which `solve` fails, showing that
  completeness needs injective tables;
* Word-RAM execution checks (`#guard`) verifying exact output arrays, decision bits, and step
  counts bounded by `timeBound`, plus theorem-level instantiations of `solveCode_spec`,
  `program_spec_of_wellFormed`, `decideProgram_spec`, and `decodeSolution_encodeSolution`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.UniqueGamesPropagation

open Cslib.Complexity Cslib.Complexity.UniqueGames.Propagation Cslib.PCP Cslib.PCP.Encoded
  Cslib.WordRAM

/-- Rotation by one on three labels. -/
def rot : Fin 3 → Fin 3 := fun a => a + 1

/-- Rotation by two on three labels, the inverse of `rot`. -/
def rot' : Fin 3 → Fin 3 := fun a => a + 2

/-! ### Cycles of rotations -/

/-- The 3-cycle `0 → 1 → 2 → 0` carrying `rot`: going around adds three, which is zero. -/
def cyc : Graph (Fin 3 → Fin 3) := ⟨3, [⟨0, 1, rot⟩, ⟨1, 2, rot⟩, ⟨2, 0, rot⟩]⟩

/-- Every edge of `cyc` carries a bijection. -/
theorem isUniqueGame_cyc : IsUniqueGame cyc := by
  simp only [IsUniqueGame, cyc, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq]
  decide

example : (solve (List.finRange 3) cyc).map (fun σ => (List.range 3).map σ) = some [0, 1, 2] := by
  decide

example : (cyc.toGraph permutationEval).Satisfiable :=
  (solve_isSome_iff (fun a => List.mem_finRange a) isUniqueGame_cyc).1 (by decide)

/-- A yes-instance of `GapUniqueGames (Fin 3) 1 s`, for every `s`. -/
example (s : ℝ) : cyc ∈ (GapUniqueGames (Fin 3) 1 s).yes :=
  mem_yes_gapUniqueGames_one_iff.2 ⟨isUniqueGame_cyc,
    (solve_isSome_iff (fun a => List.mem_finRange a) isUniqueGame_cyc).1 (by decide)⟩

/-- The same cycle traversed backwards, `1 → 0`, `2 → 1`, `0 → 2`, carrying `rot'`: propagation
from the seed `1` runs against the edge directions and inverts `rot'`. -/
def cycRev : Graph (Fin 3 → Fin 3) := ⟨3, [⟨1, 0, rot'⟩, ⟨2, 1, rot'⟩, ⟨0, 2, rot'⟩]⟩

example : (solve (List.finRange 3) cycRev).map (fun σ => (List.range 3).map σ) =
    some [2, 0, 1] := by
  decide

/-- The 3-cycle with its last rotation replaced by the identity: going around adds two. -/
def cycBad : Graph (Fin 3 → Fin 3) := ⟨3, [⟨0, 1, rot⟩, ⟨1, 2, rot⟩, ⟨2, 0, id⟩]⟩

example : ¬ (cycBad.toGraph permutationEval).Satisfiable := by
  rw [← solve_isSome_iff (fun a => List.mem_finRange a)
    (by simp only [IsUniqueGame, cycBad, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq]; decide)]
  decide

/-! ### Cycles of negations: 2-colouring -/

/-- The triangle with negation on every edge: a 2-colouring of an odd cycle. -/
def oddFlip : Graph (Bool → Bool) := ⟨3, [⟨0, 1, not⟩, ⟨1, 2, not⟩, ⟨2, 0, not⟩]⟩

/-- Every edge of `oddFlip` carries a bijection. -/
theorem isUniqueGame_oddFlip : IsUniqueGame oddFlip := by
  simp only [IsUniqueGame, oddFlip, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, and_self]
  exact ⟨fun a b h => by simpa using h, fun b => ⟨!b, by simp⟩⟩

example : (solve [false, true] oddFlip).isSome = false := by decide

/-- The odd triangle of negations has no 2-colouring, as `solve` finds. -/
theorem not_satisfiable_oddFlip : ¬ (oddFlip.toGraph permutationEval).Satisfiable := by
  rw [← solve_isSome_iff (labels := [false, true]) (by decide) isUniqueGame_oddFlip]
  decide

/-- The odd triangle is a no-instance of `GapUniqueGames Bool 1 s` for `2/3 ≤ s < 1`: every
labelling violates at least one of its three edges. -/
example {s : ℝ} (hs : 2 / 3 ≤ s) (hs1 : s < 1) : oddFlip ∈ (GapUniqueGames Bool 1 s).no := by
  refine ⟨⟨?_, hs1⟩, isUniqueGame_oddFlip⟩
  have h := (oddFlip.toGraph permutationEval).inv_card_le_unsatVal not_satisfiable_oddFlip
  change ((Fintype.card (Fin 3) : ℕ) : ℝ)⁻¹ ≤ _ at h
  rw [Fintype.card_fin] at h
  norm_num at h
  linarith

/-- The square with negation on every edge: a 2-colouring of an even cycle. -/
def evenFlip : Graph (Bool → Bool) :=
  ⟨4, [⟨0, 1, not⟩, ⟨1, 2, not⟩, ⟨2, 3, not⟩, ⟨3, 0, not⟩]⟩

example : (solve [false, true] evenFlip).map (fun σ => (List.range 4).map σ) =
    some [false, true, false, true] := by
  decide

/-! ### A disconnected instance -/

/-- The swap of `0` and `1`, fixing `2`. -/
def swap01 : Fin 3 → Fin 3 := fun a => if a = 0 then 1 else if a = 1 then 0 else a

/-- Two components: the cycle `cyc` on `0, 1, 2`, and on `3, 4` the edges `4 → 3` carrying `rot`
and the loop `4 → 4` carrying `swap01`, whose only fixed point `2` pins the label of `4`. The
vertex `5` lies on no edge. -/
def disc : Graph (Fin 3 → Fin 3) :=
  ⟨6, [⟨0, 1, rot⟩, ⟨1, 2, rot⟩, ⟨2, 0, rot⟩, ⟨4, 3, rot⟩, ⟨4, 4, swap01⟩]⟩

example : (solve (List.finRange 3) disc).map (fun σ => (List.range 6).map σ) =
    some [0, 1, 2, 0, 2, 0] := by
  decide

/-! ### Degenerate instances -/

/-- Edges outside the declared vertex range are still handled: `slots` covers every endpoint. -/
example : (solve [false, true] (⟨0, [⟨0, 1, not⟩]⟩ : Graph (Bool → Bool))).map
    (fun σ => (List.range 2).map σ) = some [false, true] := by
  decide

example : slots (⟨0, [⟨0, 1, not⟩]⟩ : Graph (Bool → Bool)) = 2 := by decide

/-- The empty instance is satisfiable. -/
example : (solve [false, true] (⟨0, []⟩ : Graph (Bool → Bool))).isSome = true := by decide

/-- Single-label (`L = 1`) boundary case: every constraint is `id` and every vertex maps to `0`. -/
def oneLabel : Graph (Fin 1 → Fin 1) := ⟨2, [⟨0, 1, id⟩, ⟨1, 0, id⟩]⟩

example : (solve (List.finRange 1) oneLabel).map (fun σ => (List.range 2).map σ) =
    some [0, 0] := by
  decide

/-- Conflicting parallel edges `0 → 1` carrying `id` and `rot`: every edge carries a bijection,
but no labelling satisfies both constraints simultaneously. -/
def parConflict : Graph (Fin 3 → Fin 3) := ⟨2, [⟨0, 1, id⟩, ⟨0, 1, rot⟩]⟩

theorem isUniqueGame_parConflict : IsUniqueGame parConflict := by
  simp only [IsUniqueGame, parConflict, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  decide

example : (solve (List.finRange 3) parConflict).isSome = false := by decide

example : ¬ (parConflict.toGraph permutationEval).Satisfiable := by
  rw [← solve_isSome_iff (fun a => List.mem_finRange a) isUniqueGame_parConflict]
  decide

/-! ### Completeness needs injective tables -/

/-- The edges `0 → 1` and `2 → 1` carry the constant `0` and the loop `2 → 2` the constant `1`.
The labelling `0, 0, 1` satisfies it, but propagation reaches `2` from `1` and inverts the
constant `0` there to the label `0`, which the loop refutes. -/
def constTables : Graph (Fin 2 → Fin 2) :=
  ⟨3, [⟨0, 1, fun _ => 0⟩, ⟨2, 1, fun _ => 0⟩, ⟨2, 2, fun _ => 1⟩]⟩

example : (constTables.toGraph permutationEval).Satisfiable :=
  ⟨fun v => if v = 2 then 1 else 0, (check_eq_true_iff _ _).1 (by decide)⟩

example : (solve (List.finRange 2) constTables).isSome = false := by decide

/-! ### Word-RAM execution and step-bound checks -/

section GuardChecks

set_option linter.hashCommand false

private meta def evalRAM {L : ℕ} (w : ℕ) (g : Graph (Fin L → Fin L)) :
    Option (List ℕ × ℕ × ℕ) :=
  (solveCode.eval w (timeBound g) (Data.init (encode g))).map fun (y, steps) =>
    (outputList y.mem (y.regs Reg.outBase), y.regs Reg.ok, steps)

-- Satisfiable 3-cycle `cyc` (wordBound = 9 * 8 = 72 < 128 = 2^7).
#guard match evalRAM 7 cyc with
  | some (out, ok, steps) => out == [1, 0, 1, 2] && ok == 1 && steps ≤ timeBound cyc
  | none => false

-- Reversed 3-cycle `cycRev` (tests backward bijection inversion in Word-RAM).
#guard match evalRAM 7 cycRev with
  | some (out, ok, steps) => out == [1, 2, 0, 1] && ok == 1 && steps ≤ timeBound cycRev
  | none => false

-- Unsatisfiable 3-cycle `cycBad`.
#guard match evalRAM 7 cycBad with
  | some (out, ok, steps) => out == [0] && ok == 0 && steps ≤ timeBound cycBad
  | none => false

-- Odd and even flip cycles over `Fin 2`.
def oddFlipFin : Graph (Fin 2 → Fin 2) :=
  ⟨3, [⟨0, 1, fun a => 1 - a⟩, ⟨1, 2, fun a => 1 - a⟩, ⟨2, 0, fun a => 1 - a⟩]⟩

def evenFlipFin : Graph (Fin 2 → Fin 2) :=
  ⟨4, [⟨0, 1, fun a => 1 - a⟩, ⟨1, 2, fun a => 1 - a⟩,
       ⟨2, 3, fun a => 1 - a⟩, ⟨3, 0, fun a => 1 - a⟩]⟩

#guard match evalRAM 7 oddFlipFin with
  | some (out, ok, steps) => out == [0] && ok == 0 && steps ≤ timeBound oddFlipFin
  | none => false

#guard match evalRAM 7 evenFlipFin with
  | some (out, ok, steps) => out == [1, 0, 1, 0, 1] && ok == 1 && steps ≤ timeBound evenFlipFin
  | none => false

-- Disconnected 6-vertex instance `disc` with self-loop and isolated vertex
-- (wordBound = 9 * 13 = 117 < 128).
#guard match evalRAM 7 disc with
  | some (out, ok, steps) => out == [1, 0, 1, 2, 0, 2, 0] && ok == 1 && steps ≤ timeBound disc
  | none => false

-- Out-of-range endpoints `⟨0, [⟨0, 1, flip⟩]⟩`.
#guard match evalRAM 6 (⟨0, [⟨0, 1, fun a : Fin 2 => 1 - a⟩]⟩ : Graph (Fin 2 → Fin 2)) with
  | some (out, ok, steps) => out == [1, 0, 1] && ok == 1 && steps ≤ 1000
  | none => false

-- Empty graph `⟨0, []⟩` over `Fin 2` (wordBound = 8 * 2 = 16 < 32 = 2^5).
#guard match evalRAM 5 (⟨0, []⟩ : Graph (Fin 2 → Fin 2)) with
  | some (out, ok, steps) =>
      out == [1] && ok == 1 && steps ≤ timeBound (⟨0, []⟩ : Graph (Fin 2 → Fin 2))
  | none => false

-- Non-injective `constTables` (satisfiable, but `solve` returns `none`, and Word-RAM agrees!).
#guard match evalRAM 7 constTables with
  | some (out, ok, steps) => out == [0] && ok == 0 && steps ≤ timeBound constTables
  | none => false

-- Single-label (`L = 1`) instance `oneLabel`.
#guard match evalRAM 7 oneLabel with
  | some (out, ok, steps) => out == [1, 0, 0] && ok == 1 && steps ≤ timeBound oneLabel
  | none => false

-- Conflicting parallel edges `parConflict` (`IsUniqueGame`, unsatisfiable).
#guard match evalRAM 7 parConflict with
  | some (out, ok, steps) => out == [0] && ok == 0 && steps ≤ timeBound parConflict
  | none => false

end GuardChecks

/-! ### Non-vacuous theorem-level `ExecutesList` and `Executes` instantiations -/

theorem cyc_wordram_executesList :
    InputFits 7 (encode cyc) ∧
    ∃ n ≤ 2444, ExecutesList 7 program (.init (encode cyc)) [1, 0, 1, 2] n := by
  have hw : Fits 7 (wordBound cyc) := by decide
  have hwf : cyc.WellFormed := by
    simp only [Graph.WellFormed, cyc, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq]
    decide
  refine ⟨Fits.inputFits_encode hw, ?_⟩
  obtain ⟨n, hn, hex⟩ := program_spec_of_wellFormed (w := 7) (g := cyc) hwf hw
  have hout : encodeSolution cyc.vertices (solve (List.finRange 3) cyc) = [1, 0, 1, 2] := by
    decide
  rw [hout] at hex
  exact ⟨n, hn, hex⟩

theorem cycBad_wordram_decide :
    ∃ n ≤ timeBound cycBad, Executes 7 decideProgram (.init (encode cycBad)) 0 n := by
  obtain ⟨n, hn, hex⟩ := decideProgram_spec (w := 7) cycBad (by decide)
  have h0 : (solve (List.finRange 3) cycBad).isSome.toNat = 0 := by decide
  exact ⟨n, hn, h0 ▸ hex⟩

theorem disc_wordram_decode_roundtrip :
    ∃ n ≤ timeBound disc,
      ExecutesList 7 program (.init (encode disc)) [1, 0, 1, 2, 0, 2, 0] n ∧
      (decodeSolution 3 [1, 0, 1, 2, 0, 2, 0]).map (fun σ => (List.range 6).map σ) =
        some [0, 1, 2, 0, 2, 0] := by
  obtain ⟨n, hn, hex⟩ := program_spec (w := 7) disc (by decide)
  have hout : encodeSolution (slots disc) (solve (List.finRange 3) disc) =
      [1, 0, 1, 2, 0, 2, 0] := by decide
  refine ⟨n, hn, hout ▸ hex, ?_⟩
  rw [← hout, decodeSolution_encodeSolution]
  decide

theorem oneLabel_solveCode_spec :
    ∃ y, ExecWithin 7 solveCode (Data.init (encode oneLabel)) y (timeBound oneLabel - 1) ∧
      y.regs Reg.ok = 1 ∧ outputList y.mem (y.regs Reg.outBase) = [1, 0, 0] := by
  obtain ⟨y, hy, hok, hout, -⟩ := solveCode_spec (w := 7) oneLabel (by decide)
  have hok1 : (solve (List.finRange 1) oneLabel).isSome.toNat = 1 := by decide
  have hout1 : encodeSolution (slots oneLabel) (solve (List.finRange 1) oneLabel) = [1, 0, 0] := by
    decide
  exact ⟨y, hy, hok.trans hok1, hout.trans hout1⟩

theorem parConflict_wordram_decide :
    ∃ n ≤ timeBound parConflict, Executes 7 decideProgram (.init (encode parConflict)) 0 n := by
  obtain ⟨n, hn, hex⟩ := decideProgram_spec (w := 7) parConflict (by decide)
  have h0 : (solve (List.finRange 3) parConflict).isSome.toNat = 0 := by decide
  exact ⟨n, hn, h0 ▸ hex⟩

end CslibFrontierTests.UniqueGamesPropagation
