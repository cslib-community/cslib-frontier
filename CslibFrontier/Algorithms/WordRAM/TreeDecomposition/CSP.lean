/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.CSP.Model
public import CslibFrontier.Computability.WordRAM.Function
import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.CSP.Pass
import CslibFrontier.Computability.WordRAM.Realization.Program.Standard

/-!
# Word-RAM FPT dynamic programming for finite-domain CSPs over bounded treewidth

This module proves genuine exact-basis Word-RAM (`Program .exact r`) running-time bounds for both
finite-domain CSP satisfiability (`cspDecideNice`, `cspDecideRooted`) and bounded-word exact model
counting (`cspCountNice`, `cspCountRooted`) over serialized nice tree decompositions and
materialized constraint truth tables.

Unlike abstract recurrence counters, the Word-RAM program here executes every phase in linear
memory and charges every instruction:

* **Bag materialization and erasure**: `introduce` nodes allocate `1 + |childBag|` words and copy
  the child bag via `copyBagProg`; `forget` nodes scan the child bag, allocate `|childBag.erase v|`
  words, and copy the erased bag via `eraseBagProg`.
* **Radix decoding and Horner projection**: `lookupRadixProg` decodes `ofRadix q L m x` in `|L|`
  division/remainder steps, and `radixProjProg` evaluates `toRadix` across constraint scopes,
  `forget`-updated child bags, and `join` sibling bags.
* **Constraint truth-table evaluation**: each constraint `c` is stored in memory as
  `[|c.scope|, q ^ |c.scope|] ++ c.scope ++ table`, and `introduce` / `leaf` nodes scan every
  constraint, test scope inclusion (`subsetBagProg`, `bagMemProg`), project the current radix
  assignment to `c.scope`, and index the truth table in memory.
* **Bounded-word DP arithmetic**: in decision mode (`counting = false`) all DP entries lie in
  `{0, 1}` (no `q ^ |T|` word-width term); in model-counting mode (`counting = true`) DP entries at
  subtree `S` are bounded by `q ^ S.size ≤ q ^ T.size`, accounted for explicitly in
  `Fits w inst.wordBound`.

The implementation is factored under `CslibFrontier.Algorithms.WordRAM.TreeDecomposition.CSP`
into `Model` (pure DP specification, encoding, and bounds; publicly re-exported here), `Radix`,
`BagOps`, `ConstraintScan`, `NodeDesc`, parallel node handlers `LeafIntro`, `Forget`, and `Join`,
`NodeStep`, and `Pass` (imported privately so the top-level interface stays minimal).

## Main definitions

* `Cslib.Algorithms.WordRAM.TreeDecomposition.tupleOfRadix`: positional decoding of a radix index
  into an arity-`r` tuple in `List (Fin q)`.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.ConstraintTable`: materialized truth table of a
  constraint over `ℕ` variable indices.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.encodeNiceTree`: post-order 4-word-per-node
  serialization of `NiceTree ℕ`.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.TreeCSPInstance`: serialized CSP + nice tree
  decomposition instance supporting both satisfiability (`counting = false`) and exact model
  counting (`counting = true`), with constructors `ofNiceTree`, `ofNice`, and `ofRooted`.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.cspNiceStepBound`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.cspRootedStepBound`: explicit FPT step-count
  polynomials.

## Main results

* `Cslib.Algorithms.WordRAM.TreeDecomposition.exists_program_csp_treeDecomposition`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.uniformComputableInTime_csp_treeDecomposition`:
  one fixed Word-RAM program computes `TreeCSPInstance.result` within
  `C * (inst.stepBound + 1) + 1`
  instructions whenever `Fits w inst.wordBound`.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.exists_program_cspDecide_nice`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.exists_program_cspCount_nice`: FPT Word-RAM
  satisfiability and bounded-word model counting on `NiceTreeDecomposition`.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.exists_program_cspDecide_rooted`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.exists_program_cspCount_rooted`: FPT Word-RAM
  satisfiability and bounded-word model counting on `RootedTreeDecomposition` via
  `toNiceTreePruned` (`O((|V| + 1) · q ^ (k + 1) · poly(k, |F|, |F.vars|))` instructions).
-/

public section

namespace Cslib.Algorithms.WordRAM.TreeDecomposition

open SimpleGraph
open Cslib.Logic.PL
open Cslib.Algorithms.Lean.TreeDecomposition
open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization

/-- One fixed exact-basis Word-RAM program computes `TreeCSPInstance.result` within
`≤ C * (inst.stepBound + 1) + 1` instructions for every word width `w` satisfying
`Fits w inst.wordBound` and `InputFits w inst.encode`. -/
theorem exists_program_csp_treeDecomposition :
    ∃ r C : ℕ, ∃ prog : Program .exact r,
      prog.ComputesInTime
        (fun _ inst => inst.encode)
        (fun inst _ => C * (inst.stepBound + 1) + 1)
        (fun inst w => Fits w inst.wordBound)
        TreeCSPInstance.result := by
  obtain ⟨r, C, pc, prog, _, _, hexec⟩ :=
    runTreeCSPProg_realizes.exists_standard_init_program_state_from_words (0 : Fin 1)
  refine ⟨r, C, prog, fun inst w hw hin => ?_⟩
  obtain ⟨hval, hres, hcost⟩ := runTreeCSPProg_spec inst hw
  obtain ⟨y, n, hruns, hhalt, _, _, hn_le⟩ :=
    hexec w () inst.encode (fun j => Fin.elim0 j) (Nat.zero_le _)
      (hw.of_le <| by
        unfold TreeCSPInstance.wordBound
        dsimp only
        omega)
      hin ⟨inst, rfl, hw⟩ hval
  rw [clientResult_width, hres] at hhalt
  exact ⟨n + 1, ⟨⟨pc, y⟩, n, hruns, hhalt, rfl⟩,
    hn_le.trans (Nat.add_le_add_right (Nat.mul_le_mul_left C (by omega)) 1)⟩

/-- Uniform exact-basis Word-RAM computability certificate for `TreeCSPInstance.result`. -/
theorem uniformComputableInTime_csp_treeDecomposition :
    ∃ C : ℕ,
      UniformComputableInTime .exact
        TreeCSPInstance.result
        (fun _ inst => inst.encode)
        (fun inst _ => C * (inst.stepBound + 1) + 1)
        (fun inst w => Fits w inst.wordBound) := by
  obtain ⟨r, C, prog, hcomp⟩ := exists_program_csp_treeDecomposition
  refine ⟨C, r, prog, hcomp, fun inst => ?_⟩
  obtain ⟨w, hw_le, hin⟩ := InputFits.exists_width inst.encode inst.wordBound
  exact ⟨w, (fits_self inst.wordBound).mono hw_le, hin⟩

private theorem steps_le_of_stepBound_le {steps C a b : ℕ} (hsteps : steps ≤ C * (a + 1) + 1)
    (hab : a ≤ b) : steps ≤ C * (b + 1) + 1 :=
  hsteps.trans (Nat.add_le_add_right (Nat.mul_le_mul_left C (Nat.add_le_add_right hab 1)) 1)

open Classical in
/-- **FPT Word-RAM CSP Decision (Nice Tree Decomposition).** One fixed exact-basis Word-RAM
program decides `CSP.Satisfiable sem F` (returning `1` if satisfiable, `0` otherwise) on any
finite-domain CSP `F : CSP Rel V` (`q > 0`, `e : V ≃ Fin m`) and nice tree decomposition `N` of
`F.primalGraph` with `N.width ≤ k` in `≤ C * (cspNiceStepBound q N.size k |F.vars| |F| + 1) + 1`
instructions at any word width `w` satisfying `Fits w inst.wordBound`. -/
theorem exists_program_cspDecide_nice :
    ∃ r C : ℕ, ∃ prog : Program .exact r,
      ∀ {Rel V : Type*} [DecidableEq V] {q m k : ℕ} (hq : 0 < q) (e : V ≃ Fin m)
        (sem : Rel → List (Fin q) → Bool) (F : CSP Rel V)
        (N : F.primalGraph.NiceTreeDecomposition),
        N.width ≤ k →
        ∀ w : ℕ,
          let inst := TreeCSPInstance.ofNice false q hq e sem F N
          Fits w inst.wordBound →
          ∃ steps,
            Executes w prog (.init inst.encode) (if CSP.Satisfiable sem F then 1 else 0) steps ∧
            steps ≤ C * (cspNiceStepBound q N.size k F.vars.length F.length + 1) + 1 := by
  obtain ⟨r, C, prog, hcomp⟩ := exists_program_csp_treeDecomposition
  refine ⟨r, C, prog, fun {_ _} [_] {q _ _} hq e sem F N hk w hw => ?_⟩
  let inst := TreeCSPInstance.ofNice false q hq e sem F N
  obtain ⟨steps, hexec, hsteps⟩ := hcomp inst w hw (inputFits_encode inst hw)
  have hres : inst.result = if CSP.Satisfiable sem F then 1 else 0 := by
    dsimp only [inst, TreeCSPInstance.ofNice]
    rw [TreeCSPInstance.result_ofNiceTree_decide]
    exact if_congr (cspDecideNice_eq_true_iff hq sem N) rfl rfl
  rw [hres] at hexec
  exact ⟨steps, hexec, steps_le_of_stepBound_le hsteps
    (TreeCSPInstance.stepBound_ofNice_le hq false e sem F N hk)⟩

/-- **FPT Word-RAM CSP Model Counting (Nice Tree Decomposition).** One fixed exact-basis Word-RAM
program computes `CSP.modelCount sem F` in `≤ C * (cspNiceStepBound ... + 1) + 1` instructions at
any word width `w` satisfying `Fits w inst.wordBound` (accounting for DP count growth up to
`q ^ N.size`). -/
theorem exists_program_cspCount_nice :
    ∃ r C : ℕ, ∃ prog : Program .exact r,
      ∀ {Rel V : Type*} [DecidableEq V] {q m k : ℕ} (hq : 0 < q) (e : V ≃ Fin m)
        (sem : Rel → List (Fin q) → Bool) (F : CSP Rel V)
        (N : F.primalGraph.NiceTreeDecomposition),
        N.width ≤ k →
        ∀ w : ℕ,
          let inst := TreeCSPInstance.ofNice true q hq e sem F N
          Fits w inst.wordBound →
          ∃ steps,
            Executes w prog (.init inst.encode)
              (@CSP.modelCount _ _ (Fin q) _ inferInstance ⟨⟨0, hq⟩⟩ sem F) steps ∧
            steps ≤ C * (cspNiceStepBound q N.size k F.vars.length F.length + 1) + 1 := by
  obtain ⟨r, C, prog, hcomp⟩ := exists_program_csp_treeDecomposition
  refine ⟨r, C, prog, fun {_ _} [_] {q _ _} hq e sem F N hk w hw => ?_⟩
  let inst := TreeCSPInstance.ofNice true q hq e sem F N
  obtain ⟨steps, hexec, hsteps⟩ := hcomp inst w hw (inputFits_encode inst hw)
  rw [TreeCSPInstance.result_ofNice_count hq e sem F N] at hexec
  exact ⟨steps, hexec, steps_le_of_stepBound_le hsteps
    (TreeCSPInstance.stepBound_ofNice_le hq true e sem F N hk)⟩

open Classical in
/-- **FPT Word-RAM CSP Decision (Rooted Tree Decomposition).** One fixed exact-basis Word-RAM
program decides `CSP.Satisfiable sem F` over any `RootedTreeDecomposition` via `toNiceTreePruned`
in `≤ C * (cspRootedStepBound q m k |F.vars| |F| + 1) + 1` instructions. -/
theorem exists_program_cspDecide_rooted :
    ∃ r C : ℕ, ∃ prog : Program .exact r,
      ∀ {Rel V : Type*} [LinearOrder V] {q m n k : ℕ} (hq : 0 < q) (e : V ≃ Fin m)
        (sem : Rel → List (Fin q) → Bool) (F : CSP Rel V)
        (R : F.primalGraph.RootedTreeDecomposition n),
        R.width ≤ k →
        ∀ w : ℕ,
          let inst := TreeCSPInstance.ofRooted false q hq e sem F R
          Fits w inst.wordBound →
          ∃ steps,
            Executes w prog (.init inst.encode) (if CSP.Satisfiable sem F then 1 else 0) steps ∧
            steps ≤ C * (cspRootedStepBound q m k F.vars.length F.length + 1) + 1 := by
  obtain ⟨r, C, prog, hcomp⟩ := exists_program_csp_treeDecomposition
  refine ⟨r, C, prog, fun {_ _} [_] {q _ _ _} hq e sem F R hk w hw => ?_⟩
  let inst := TreeCSPInstance.ofRooted false q hq e sem F R
  obtain ⟨steps, hexec, hsteps⟩ := hcomp inst w hw (inputFits_encode inst hw)
  have hres : inst.result = if CSP.Satisfiable sem F then 1 else 0 := by
    dsimp only [inst, TreeCSPInstance.ofRooted, TreeCSPInstance.ofNice]
    rw [TreeCSPInstance.result_ofNiceTree_decide]
    exact if_congr (cspDecideNice_eq_true_iff hq sem R.toNiceTreePruned) rfl rfl
  rw [hres] at hexec
  exact ⟨steps, hexec, steps_le_of_stepBound_le hsteps
    (TreeCSPInstance.stepBound_ofRooted_le hq false e sem F R hk)⟩

/-- **FPT Word-RAM CSP Model Counting (Rooted Tree Decomposition).** One fixed exact-basis
Word-RAM program computes `CSP.modelCount sem F` over any `RootedTreeDecomposition` via
`toNiceTreePruned` in `≤ C * (cspRootedStepBound q m k |F.vars| |F| + 1) + 1` instructions whenever
`Fits w inst.wordBound`. -/
theorem exists_program_cspCount_rooted :
    ∃ r C : ℕ, ∃ prog : Program .exact r,
      ∀ {Rel V : Type*} [LinearOrder V] {q m n k : ℕ} (hq : 0 < q) (e : V ≃ Fin m)
        (sem : Rel → List (Fin q) → Bool) (F : CSP Rel V)
        (R : F.primalGraph.RootedTreeDecomposition n),
        R.width ≤ k →
        ∀ w : ℕ,
          let inst := TreeCSPInstance.ofRooted true q hq e sem F R
          Fits w inst.wordBound →
          ∃ steps,
            Executes w prog (.init inst.encode)
              (@CSP.modelCount _ _ (Fin q) _ inferInstance ⟨⟨0, hq⟩⟩ sem F) steps ∧
            steps ≤ C * (cspRootedStepBound q m k F.vars.length F.length + 1) + 1 := by
  obtain ⟨r, C, prog, hcomp⟩ := exists_program_csp_treeDecomposition
  refine ⟨r, C, prog, fun {_ _} [_] {q _ _ _} hq e sem F R hk w hw => ?_⟩
  let inst := TreeCSPInstance.ofRooted true q hq e sem F R
  obtain ⟨steps, hexec, hsteps⟩ := hcomp inst w hw (inputFits_encode inst hw)
  rw [TreeCSPInstance.result_ofRooted_count hq e sem F R] at hexec
  exact ⟨steps, hexec, steps_le_of_stepBound_le hsteps
    (TreeCSPInstance.stepBound_ofRooted_le hq true e sem F R hk)⟩

end Cslib.Algorithms.WordRAM.TreeDecomposition
