/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.Arborescence.Input
public import CslibFrontier.Computability.WordRAM.ListOutput
import CslibFrontier.Algorithms.WordRAM.Arborescence.Internal.EdmondsEntry
import CslibFrontier.Algorithms.WordRAM.Arborescence.Internal.EdmondsOutEntry
import CslibFrontier.Algorithms.WordRAM.Arborescence.Internal.OptBranchingEntry
import CslibFrontier.Computability.WordRAM.Realization.Program.Standard

/-!
# Materialized-table Chu–Liu/Edmonds and optimum branchings on the Word-RAM (`O(n³)`)

This module implements a dense materialized-table Chu–Liu/Edmonds minimum-cost spanning
arborescence algorithm and this formalization's super-root maximum-weight branching reduction on
the deterministic standard-basis Word-RAM (`Cslib.WordRAM.Basis.standard`), proving uniform
width-blind (`¬prog.ReadsWidth`) instruction-count bounds `C * (I.n + 1) ^ 3`
(`Program.ComputesListInTime`) at every word width `w` satisfying `Fits w I.wordBound` (i.e.,
`I.wordBound < 2 ^ w`). Because `wordBound n M₀ = 4 * (n + 1) * M₀ + 32 * (n + 1) ^ 2` is a
polynomial bound on **word values and addresses**, a word width `w` of order
`log(n + 2) + log(M₀ + 2)` bits suffices.

Signed integer arc costs and weights are represented in memory via `Cslib.WordRAM.Signed.encode`
(`2 * |z| + signBit`). In [Edmonds1967Branchings], §4 instruction (I2), equation (1), contracting a
cycle adjusts the weight of each arc entering the cycle by subtracting its selected cycle-edge
weight and adding a cycle-wide offset. This module implements the rooted, reversed min-cost
variant: at round `k`, the contracted exit cost for an arc `(x, w)` leaving a contracted cycle `C`
(`x ∈ C`, `w ∉ C`) is computed as the reduced exit-cost difference `c_k[x][w] - c_k[x][f[x]]` (with
inactive contracted cells set to `0`). Because `f[x]` minimizes `c_k[x][z]` over active non-self
outgoing arcs of `x`, every reduced exit cost is nonnegative (`0 ≤ c_k[x][w] - c_k[x][f[x]]`), so
all entries of the working cost matrix stay within `[-M₀, (k + 1) * M₀]` across all `k ≤ n`
contraction rounds while maintaining exact row-potential equivalence (`∃ φ, ∀ u w, a[u][w] →
c_unred[u][w] = c_red[u][w] + φ u`) with `edmondsTableAux`. Consequently, any word width `w`
satisfying `Fits w (wordBound n M₀)` (`wordBound n M₀ < 2 ^ w`, so `w` of order
`log(n + 2) + log(M₀ + 2)` bits) accommodates all signed-encoded intermediate weights and `O(n²)`
workspace addresses without overflow.

For maximum-weight branchings, [Edmonds1967Branchings], §2 adds a new node with one arc to a
prescribed root and reduces optimum spanning arborescence to optimum branching via a weight shift
(formalized in `CslibFrontier.Algorithms.Lean.Arborescence.Branching`). To solve maximum-weight
branchings via the rooted in-arborescence Word-RAM core, `optimumBranchingProg` implements this
formalization's reverse super-root reduction from
`CslibFrontier.Algorithms.Lean.Arborescence.Branching`: it reduces maximum-weight branching to
rooted spanning in-arborescence by adding a zero-cost arc from every original vertex to the
super-root and reversing and negating all original arcs.

The dense `O(n³)` Word-RAM realization, workspace layout, word-value/address bound, and
instruction-count bounds are original to this formalization over the cycle-contraction algorithm
and §2 weight-shift reduction of [Edmonds1967Branchings], Sections 1–4 ([ChuLiu1965] was not
inspected directly).

## Main definitions

* `Cslib.Algorithms.WordRAM.Arborescence.wordBound`: polynomial bound
  `4 * (n + 1) * M₀ + 32 * (n + 1) ^ 2` on word values and workspace addresses; `Fits w (wordBound
  n M₀)` (`wordBound n M₀ < 2 ^ w`) holds at word widths `w` of order `log(n + 2) + log(M₀ + 2)`
  bits.
* `Cslib.Algorithms.WordRAM.Arborescence.flattenBoolMatrix`,
  `Cslib.Algorithms.WordRAM.Arborescence.flattenSignedMatrix`: row-major flat word-list encodings
  of Boolean adjacency and signed cost/weight matrices.
* `Cslib.Algorithms.WordRAM.Arborescence.ArborescenceInput`,
  `Cslib.Algorithms.WordRAM.Arborescence.BranchingInput`: weighted digraph inputs on `Fin n` with
  intrinsic magnitude and word-value/address bounds (`maxAbsCost`, `maxAbsWeight`, `wordBound`),
  flat word encodings (`encode`), and expected parent-list outputs (`expectedParentList`,
  `expectedOutParentList`).

## Main results

* `Cslib.Algorithms.WordRAM.Arborescence.ArborescenceInput.expectedParentList_eq_nil_iff`,
  `Cslib.Algorithms.WordRAM.Arborescence.ArborescenceInput.expectedParentList_spec`,
  `Cslib.Algorithms.WordRAM.Arborescence.ArborescenceInput.expectedOutParentList_eq_nil_iff`,
  `Cslib.Algorithms.WordRAM.Arborescence.ArborescenceInput.expectedOutParentList_spec`,
  `Cslib.Algorithms.WordRAM.Arborescence.BranchingInput.expectedParentList_spec`: public
  correctness and optimality characterizations of the encoded parent-list outputs.
* `Cslib.Algorithms.WordRAM.Arborescence.exists_edmonds_program`: uniform width-blind
  standard-basis Word-RAM program (`Program.ComputesListInTime`) for Chu–Liu/Edmonds minimum-cost
  spanning in-arborescence running in `C * (I.n + 1) ^ 3` instructions at every word width `w`
  satisfying `Fits w I.wordBound` (`I.wordBound < 2 ^ w`).
* `Cslib.Algorithms.WordRAM.Arborescence.exists_edmondsOut_program`: uniform width-blind
  standard-basis Word-RAM program (`Program.ComputesListInTime`) for minimum-cost spanning
  out-arborescence running in `C * (I.n + 1) ^ 3` instructions at every word width `w` satisfying
  `Fits w I.wordBound` (`I.wordBound < 2 ^ w`).
* `Cslib.Algorithms.WordRAM.Arborescence.exists_optimumBranching_program`: uniform width-blind
  standard-basis Word-RAM program (`Program.ComputesListInTime`) for maximum-weight branching via
  this formalization's super-root reduction, running in `C * (I.n + 1) ^ 3` instructions at every
  word width `w` satisfying `Fits w I.wordBound` (`I.wordBound < 2 ^ w`).

## References

* [J. Edmonds, *Optimum branchings*][Edmonds1967Branchings], Sections 1–4
-/

namespace Cslib.Algorithms.WordRAM.Arborescence

open Cslib.Algorithms.WordRAM.Arborescence.Internal
open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization

/-- Every word width fitting `I.wordBound` satisfies `InputFits w I.encode`. -/
public theorem ArborescenceInput.inputFits_encode {w : ℕ} (I : ArborescenceInput)
    (hwb : Fits w I.wordBound) : InputFits w I.encode :=
  (inputFits_arb_encode I I.natAbs_cost_le_maxAbsCost hwb).2

/-- Every word width fitting `I.wordBound` satisfies `InputFits w I.encode`. -/
public theorem BranchingInput.inputFits_encode {w : ℕ} (I : BranchingInput)
    (hwb : Fits w I.wordBound) : InputFits w I.encode :=
  (inputFits_branching_encode I I.natAbs_weight_le_maxAbsWeight hwb).2

private theorem executesList_of_client_spec {α : Type} {k r C₁ w K n : ℕ}
    {enc : α ↪ (Fin k → ℕ)} {f : α → Memory.Prog ℕ} {Safe : ℕ → α → Memory.State → Prop}
    {pc : ℕ} {prog : Program .standard r} {frontier : Fin r} {out : Fin 1 → Fin r}
    (he : ∀ (w : ℕ) (a : α) (xs : List ℕ),
      (∀ j : Fin k, xs.getD j.val 0 = enc a j) →
      k ≤ xs.length → Fits w (xs.length + 1) → InputFits w xs →
      Safe w a (Memory.State.init xs) →
      (Memory.spec w).ValidHistory (Memory.State.init xs)
        ((Memory.spec w).clientHistory (Memory.State.init xs) (f a)) →
      ∃ y m, Runs w prog (State.init xs) ⟨pc, y⟩ m ∧
        step w prog ⟨pc, y⟩ =
          .halt (wordWords ((Memory.spec w).clientResult (Memory.State.init xs) (f a)) 0) ∧
        memoryState frontier y =
          (Memory.spec w).clientState (Memory.State.init xs) (f a) ∧
        (∀ j, y.regs (out j) =
          wordWords ((Memory.spec w).clientResult (Memory.State.init xs) (f a)) j) ∧
        m + 1 ≤ C₁ * (memoryCost (f a) (Memory.State.init xs) + 0 + 1) + 1)
    (a : α) (xs expected : List ℕ)
    (hlayout : ∀ j : Fin k, xs.getD j.val 0 = enc a j)
    (hk : k ≤ xs.length) (hfit_len : Fits w (xs.length + 1)) (hin_fits : InputFits w xs)
    (hsafe : Safe w a (Memory.State.init xs))
    (hvh : (Memory.spec w).ValidHistory (Memory.State.init xs)
      ((Memory.spec w).clientHistory (Memory.State.init xs) (f a)))
    (hmc : memoryCost (f a) (Memory.State.init xs) + 1 ≤ K * (n + 1) ^ 3)
    (hout : outputList ((Memory.spec 0).clientState (Memory.State.init xs) (f a)).mem
      ((Memory.spec 0).clientResult (Memory.State.init xs) (f a)) = expected)
    (hfit_out :
      Fits w ((Memory.spec 0).clientResult (Memory.State.init xs) (f a) + expected.length)) :
    ∃ t, ExecutesList w prog (State.init xs) expected t ∧
      t ≤ (K * C₁ + 1) * (n + 1) ^ 3 := by
  obtain ⟨y, m, hruns, hhalt, hmem, _, hsteps⟩ :=
    he w a xs hlayout hk hfit_len hin_fits hsafe hvh
  rw [clientState_width w] at hmem
  rw [clientResult_width w] at hhalt
  dsimp only [wordWords] at hhalt
  have hymem :
      y.mem = ((Memory.spec 0).clientState (Memory.State.init xs) (f a)).mem :=
    congrArg Memory.State.mem hmem
  refine ⟨m + 1, ⟨⟨pc, y⟩, m, _, hruns, hhalt, hymem ▸ hout, hfit_out, rfl⟩, ?_⟩
  have hmul : C₁ * (memoryCost (f a) (Memory.State.init xs) + 0 + 1) ≤ C₁ * (K * (n + 1) ^ 3) :=
    Nat.mul_le_mul_left C₁ (by omega)
  have hpos : 1 ≤ (n + 1) ^ 3 := Nat.one_le_pow 3 (n + 1) (Nat.succ_pos _)
  have hring : C₁ * (K * (n + 1) ^ 3) + (n + 1) ^ 3 = (K * C₁ + 1) * (n + 1) ^ 3 := by ring
  linarith only [hsteps, hmul, hpos, hring]

private theorem exists_arb_program_of_spec
    {f : ℕ × ℕ → Memory.Prog ℕ} {Safe : ℕ → ℕ × ℕ → Memory.State → Prop}
    {expected : ArborescenceInput → List ℕ} {lin : ℕ} (hlin : lin ≤ 129)
    (hreal : Realizes .exact f pairWords wordWords Safe (fun _ _ => 0))
    (hspec : ∀ {w M₀ : ℕ} (I : ArborescenceInput),
      (∀ u v, (I.cost u v).natAbs ≤ M₀) → Fits w (wordBound I.n M₀) →
      let s₀ := Memory.State.init I.encode
      let d := (I.n, I.root.1)
      let outAddr := (Memory.spec 0).clientResult s₀ (f d)
      let s' := (Memory.spec 0).clientState s₀ (f d)
      Safe w d s₀ ∧
        (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (f d)) ∧
        memoryCost (f d) s₀ ≤ 43 * I.n ^ 3 + 22 * I.n ^ 2 + lin * I.n + 3 ∧
        outputList s'.mem outAddr = expected I ∧
        Fits w (outAddr + (expected I).length)) :
    ∃ r C : ℕ, ∃ prog : Program .standard r, ¬prog.ReadsWidth ∧
      prog.ComputesListInTime (fun _ I => I.encode) (fun I _ => C * (I.n + 1) ^ 3)
        (fun I w => Fits w I.wordBound) expected := by
  obtain ⟨r, C₁, pc, prog, hnw, frontier, _, he⟩ :=
    hreal.exists_standard_basis_init_program_state_from_words (0 : Fin 1)
  refine ⟨r, 43 * C₁ + 1, prog, hnw, fun I w hwb _ => ?_⟩
  obtain ⟨hfit_len, hin_fits⟩ := inputFits_arb_encode I I.natAbs_cost_le_maxAbsCost hwb
  have hs := hspec I I.natAbs_cost_le_maxAbsCost hwb
  exact executesList_of_client_spec he (I.n, I.root.1) I.encode (expected I)
    (by rintro ⟨_ | _ | _, h⟩; exacts [rfl, rfl, by omega])
    (by simp [ArborescenceInput.encode]) hfit_len hin_fits hs.1 hs.2.1
    (by
      have hmc := hs.2.2.1
      have hsq0 := Nat.zero_le (I.n ^ 2)
      have hlin_mul : lin * I.n ≤ 129 * I.n := Nat.mul_le_mul_right I.n hlin
      have hexp : 43 * (I.n + 1) ^ 3 = 43 * I.n ^ 3 + 129 * I.n ^ 2 + 129 * I.n + 43 := by ring
      linarith only [hmc, hexp, hsq0, hlin_mul])
    hs.2.2.2.1 hs.2.2.2.2

/-! ### Main `O(n³)` Word-RAM running-time theorems -/

public section

/-- Materialized-table Chu–Liu/Edmonds minimum-cost spanning in-arborescence runs in at most
`C * (I.n + 1) ^ 3` instructions on the deterministic width-blind standard-basis Word-RAM at every
word width `w` satisfying `Fits w I.wordBound` (i.e., `I.wordBound < 2 ^ w`, where
`I.wordBound = 4 * (I.n + 1) * I.maxAbsCost + 32 * (I.n + 1) ^ 2` bounds word values and addresses,
so `w` of order `log(I.n + 2) + log(I.maxAbsCost + 2)` bits suffices). -/
theorem exists_edmonds_program :
    ∃ r C : ℕ, ∃ prog : Program .standard r, ¬prog.ReadsWidth ∧
      prog.ComputesListInTime (fun _ I => I.encode) (fun I _ => C * (I.n + 1) ^ 3)
        (fun I w => Fits w I.wordBound) ArborescenceInput.expectedParentList :=
  exists_arb_program_of_spec (by omega) edmondsProg_realizes edmondsProg_spec

/-- Materialized-table Chu–Liu/Edmonds minimum-cost spanning out-arborescence runs in at most
`C * (I.n + 1) ^ 3` instructions on the deterministic width-blind standard-basis Word-RAM at every
word width `w` satisfying `Fits w I.wordBound` (i.e., `I.wordBound < 2 ^ w`, where
`I.wordBound = 4 * (I.n + 1) * I.maxAbsCost + 32 * (I.n + 1) ^ 2` bounds word values and addresses,
so `w` of order `log(I.n + 2) + log(I.maxAbsCost + 2)` bits suffices). -/
theorem exists_edmondsOut_program :
    ∃ r C : ℕ, ∃ prog : Program .standard r, ¬prog.ReadsWidth ∧
      prog.ComputesListInTime (fun _ I => I.encode) (fun I _ => C * (I.n + 1) ^ 3)
        (fun I w => Fits w I.wordBound) ArborescenceInput.expectedOutParentList :=
  exists_arb_program_of_spec (by omega) edmondsOutProg_realizes edmondsOutProg_spec

/-- Maximum-weight branching via this formalization's super-root reduction to rooted spanning
in-arborescence (`CslibFrontier.Algorithms.Lean.Arborescence.Branching`) runs in at most
`C * (I.n + 1) ^ 3` instructions on the deterministic width-blind standard-basis Word-RAM at every
word width `w` satisfying `Fits w I.wordBound` (i.e., `I.wordBound < 2 ^ w`, where
`I.wordBound = 4 * (I.n + 2) * I.maxAbsWeight + 32 * (I.n + 2) ^ 2` bounds word values and
addresses, so `w` of order `log(I.n + 2) + log(I.maxAbsWeight + 2)` bits suffices). -/
theorem exists_optimumBranching_program :
    ∃ r C : ℕ, ∃ prog : Program .standard r, ¬prog.ReadsWidth ∧
      prog.ComputesListInTime (fun _ I => I.encode) (fun I _ => C * (I.n + 1) ^ 3)
        (fun I w => Fits w I.wordBound) BranchingInput.expectedParentList := by
  obtain ⟨r, C₁, pc, prog, hnw, frontier, _, he⟩ :=
    optimumBranchingProg_realizes.exists_standard_basis_init_program_state_from_words (0 : Fin 1)
  refine ⟨r, 80 * C₁ + 1, prog, hnw, fun I w hwb _ => ?_⟩
  obtain ⟨hfit_len, hin_fits⟩ := inputFits_branching_encode I I.natAbs_weight_le_maxAbsWeight hwb
  have hspec := optimumBranchingProg_spec I I.natAbs_weight_le_maxAbsWeight hwb
  exact executesList_of_client_spec he I.n I.encode I.expectedParentList
    (by rintro ⟨_ | _, h⟩; exacts [rfl, by omega])
    (by simp [BranchingInput.encode]) hfit_len hin_fits hspec.1 hspec.2.1
    (by
      have hmc := hspec.2.2.1
      have hpos : 1 ≤ (I.n + 1) ^ 3 := Nat.one_le_pow 3 (I.n + 1) (Nat.succ_pos _)
      have hsq : (I.n + 1) ^ 2 ≤ (I.n + 1) ^ 3 :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (by decide)
      have hlin : I.n + 1 ≤ (I.n + 1) ^ 3 := by
        simpa using Nat.pow_le_pow_right (Nat.succ_pos I.n) (show 1 ≤ 3 by decide)
      linarith [hmc, hpos, hsq, hlin])
    hspec.2.2.2.1 hspec.2.2.2.2

end

end Cslib.Algorithms.WordRAM.Arborescence
