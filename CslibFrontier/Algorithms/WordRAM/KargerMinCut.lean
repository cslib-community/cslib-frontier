/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import CslibFrontier.Algorithms.WordRAM.NatLog
import CslibFrontier.Tactic.WramOmega
public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Karger.Graph
public import CslibFrontier.Algorithms.WordRAM.Karger.Contract
public import CslibFrontier.Algorithms.WordRAM.Karger.OutputLaw
public import CslibFrontier.Computability.WordRAM.Copy
public import CslibFrontier.Computability.WordRAM.Time

/-!
# Karger's randomized global minimum cut algorithm on the word RAM

Implements Karger's randomized contraction algorithm `[Karger1993]` on `n`-vertex weighted
undirected multigraphs (`n ≥ 2`, `IsMultigraph W`) over `Cslib.WordRAM.Basis.standard`, providing
three complete machine-level endpoints built on the workspace-relocatable subroutine
`contractDownTo`:

1. **Single-trial contraction (`singleProgram`, `r = 16`):** runs on `n :: flattenMatrix W`,
   computes row degrees at `2 + n ^ 2`, contracts in place down to `2` supervertices in at most
   `42 * n ^ 2 + 12 * n + 21` steps and `n - 2` `rand` calls, outputs a genuine non-trivial cut
   weight `cutWeight W C ≥ minCut W` on every supported branch, and achieves `minCut W` with
   probability at least `2 / (n * (n - 1))` whenever `0 < minCut W`.
2. **Repeated-trial amplification (`amplifiedProgram`, `r = 22`):** runs on
   `R :: n :: flattenMatrix W` (`1 ≤ R`), copies the immutable input matrix from `[3, 3 + n ^ 2)`
   into `[3 + n ^ 2, 3 + 2 * n ^ 2)` via `Cslib.WordRAM.ArrayCopy` before each of `R` independent
   contractions, halts within `R * (50 * n ^ 2 + 12 * n + 30) + 16` steps and `R * (n - 2)` `rand`
   calls with a genuine non-trivial cut weight `≥ minCut W`, and misses `minCut W` with probability
   at most `(1 - 2 / (n * (n - 1))) ^ R` whenever `0 < minCut W`.
3. **Explicit `O(n ^ 4 log n)` high-probability global minimum cut (`highProbProgram`, `r = 22`):**
   runs on `n :: flattenMatrix W`, computes `highProbTrials n = (n * (n - 1) / 2) * (⌊log₂ n⌋ + 2)`
   in registers using shifts and multiplication (without `.div` or `.mod`), halts within
   `33 * n ^ 4 * (Nat.log 2 n + 2)` steps with a genuine non-trivial cut weight `≥ minCut W`, and
   misses `minCut W` with probability at most `1 / (2 * n)` whenever `0 < minCut W` (and
   unconditionally at most `1 / n` in `highProbProgram_failure_le_inv_n`), via an elementary
   Bernoulli power bound without `Real.exp`.

No probability is proved on machine states. Each program simulates a client of
`Cslib.Algorithms.Lean.Karger`: the word it outputs has the law of the answer of
`Cslib.Algorithms.Lean.Karger.karger` (`singleCode_law`), or of the amplification client
`Cslib.Algorithms.Lean.Karger.minRuns` run against independent runs of `karger`
(`amplifiedCode_law`, `highProbCode_law`). Each trial contracts as the client does
(`contractDownTo_law`) and reads half the total weight of the two supervertices left
(`ContractState.mem_add_one`), and the loop of trials keeps the least answer as `minRuns` does
(`ampTrialBody_law`, `ampLoop_law`). The success and failure bounds and the cut realization are the
specification's (`Cslib.Algorithms.Lean.Karger.two_div_le_toOuterMeasure_karger`,
`Cslib.Algorithms.Lean.Karger.minRuns_ne_minCut_le`,
`Cslib.Algorithms.Lean.Karger.exists_cut_of_mem_support_answerLaw`,
`Cslib.Algorithms.Lean.Karger.mem_support_minRuns`), carried through those laws.

## Source statements and notation mapping

* **Source locators (paraphrase):**
  - `[Karger1993]`, Section 2, Theorem 2.1 and Corollary 2.1 (paraphrase): contracting uniformly
    chosen edges in an `n`-vertex multigraph down to `2` meta-vertices returns any fixed global
    minimum cut with probability at least `C(n, 2)⁻¹ = 2 / (n * (n - 1))`, and repeating
    `O(n ^ 2 log n)` independent trials amplifies the success probability to `1 - 1 / poly(n)`.
  - `[KargerStein1996]`, Section 2, Lemma 2.1, Theorem 2.2, and Corollary 2.3, Section 2.1,
    Corollary 2.4, and Section 3 ("Implementing the Contraction Algorithm", Section 3.1, Lemma 3.1
    and Section 3.2, Corollary 3.2) (paraphrase): contracting an `n`-vertex weighted multigraph
    from `k` down to `t` supervertices via edge-weight-proportional selection preserves any fixed
    minimum cut with probability at least `C(t, 2) / C(k, 2) = t * (t - 1) / (k * (k - 1))`
    (`2 / (n * (n - 1))` at `t = 2, k = n`), and an `n × n` weighted adjacency matrix with a
    maintained row-degree array executes each trial in `O(n ^ 2)` total time (`O(n)` per step in
    Section 3.2).
  - `[MitzenmacherUpfal2017]`, Section 1.5, Theorem 1.8 (paraphrase): multiplying single-step
    survival bounds `1 - 2 / i` from `i = n` down to `3` yields `2 / (n * (n - 1))`.
* **Notation mapping, implementation variants, and parameter choices:**
  - `C(n, 2)⁻¹` ↔ `2 / (n * (n - 1))` (`singleProgram_spec`, `amplifiedProgram_spec`);
  - whereas `[KargerStein1996]`, Section 3.1 draws twice (`u` proportional to `D[u]` then `v`
    proportional to `W[u, v]` via two `Random-Select` calls), `contractDownTo` uses an equivalent
    single-draw variant: one unit-cost `rand` draw in `{0, …, S - 1}` (`S = totalDoubledWeight W`)
    resolved through linear prefix-sum scans `uScan` (`rowDeg`) and `vScan` (`W[u, v]`), achieving
    the same `2 * W[u, v] / S` distribution of Lemma 3.1; and whereas Section 3.2 states `O(n)` per
    contraction step, our swap-compaction of active slot `k - 1` into `v` gives `O(k)` instructions
    on `k` active supervertices;
  - the concrete trial count `highProbTrials n = (n * (n - 1) / 2) * (Nat.log 2 n + 2)` and the
    `1 / (2 * n)` failure bound in `highProbProgram_spec` are our own parameter choice instantiating
    the `O(n ^ 2 log n)` amplification of `[Karger1993]`, Section 2, Corollary 2.1;
  - the hypothesis `0 < minCut W` in the `spec` probability clauses (`singleProgram_spec`,
    `amplifiedProgram_spec`, `highProbProgram_spec`) is retained there for the per-trial survival
    ratio, whereas `highProbProgram_failure_le_inv_n` holds unconditionally without `2 ≤ n` or
    `0 < minCut W` (when `minCut W = 0` and `2 ≤ n`, contraction preserves zero minimum cut so
    every run outputs `0`).

## Main definitions

* `Cslib.Algorithms.WordRAM.Karger.singleCode`,
  `Cslib.Algorithms.WordRAM.Karger.singleProgram`,
  `Cslib.Algorithms.WordRAM.Karger.singleTime`: single-trial Basic Karger (`r = 16`).
* `Cslib.Algorithms.WordRAM.Karger.ampCore`,
  `Cslib.Algorithms.WordRAM.Karger.amplifiedCode`,
  `Cslib.Algorithms.WordRAM.Karger.amplifiedProgram`,
  `Cslib.Algorithms.WordRAM.Karger.amplifiedTime`: `R`-trial amplified Karger (`r = 22`).
* `Cslib.Algorithms.WordRAM.Karger.highProbCode`,
  `Cslib.Algorithms.WordRAM.Karger.highProbProgram`,
  `Cslib.Algorithms.WordRAM.Karger.highProbTime`: `O(n ^ 4 log n)` high-probability global min-cut
  (`r = 22`).

## Main results

* `Cslib.Algorithms.WordRAM.Karger.singleCode_law`,
  `Cslib.Algorithms.WordRAM.Karger.amplifiedCode_law`,
  `Cslib.Algorithms.WordRAM.Karger.highProbCode_law`: each program's output has the law of the
  output of `karger` or of amplified `karger`, within its instruction and `rand`-call bounds.
* `Cslib.Algorithms.WordRAM.Karger.ampTrialBody_law`, `Cslib.Algorithms.WordRAM.Karger.ampLoop_law`,
  `Cslib.Algorithms.WordRAM.Karger.ampCore_law`: one trial, the loop of trials and the
  amplification core.
* `Cslib.Algorithms.WordRAM.Karger.singleProgram_spec`: worst-case `O(n ^ 2)` step bound, `n - 2`
  `rand`-call bound, pathwise non-trivial cut realization, `Modifies` frame, and
  `2 / (n * (n - 1))` success probability lower bound for `singleProgram`.
* `Cslib.Algorithms.WordRAM.Karger.amplifiedProgram_spec`: worst-case `O(R * n ^ 2)` step bound,
  `R * (n - 2)` `rand`-call bound, pathwise non-trivial cut realization, `Modifies` frame, and
  `(1 - 2 / (n * (n - 1))) ^ R` failure probability upper bound for `amplifiedProgram`.
* `Cslib.Algorithms.WordRAM.Karger.highProbProgram_spec`,
  `Cslib.Algorithms.WordRAM.Karger.highProbProgram_failure_le_inv_n`: worst-case
  `33 * n ^ 4 * (Nat.log 2 n + 2)` step bound, pathwise non-trivial cut realization, `Modifies`
  frame, and `1 / (2 * n)` (unconditional `1 / n`) failure probability upper bound for
  `highProbProgram`.

## References

* [D. R. Karger, *Global Min-cuts in RNC, and Other Ramifications of a Simple Min-Cut
  Algorithm*][Karger1993]
* [D. R. Karger and C. Stein, *A New Approach to the Minimum Cut Problem*][KargerStein1996]
* [M. Mitzenmacher and E. Upfal, *Probability and Computing*][MitzenmacherUpfal2017]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.Karger

open scoped ENNReal
open Cslib.WeightedCut
open Cslib.Probability.PMF
open Cslib.WordRAM
open Cslib.Algorithms.Karger

/-! ### Word-size sufficiency and `Data.init` matrix layout -/

/-- Under `2 ≤ n` and `logWidth 3 n ≤ w`, workspace end-addresses up to `3 + 2 * (n * n) + n` fit in
`w`-bit words. -/
theorem fits_workspace_of_logWidth_three {n w : ℕ} (hn : 2 ≤ n) (hw : logWidth 3 n ≤ w) :
    Fits w (3 + 2 * (n * n) + n) := by
  have hlt : 3 + 2 * (n * n) + n < (n + 1) ^ 3 := by
    obtain ⟨d, rfl⟩ : ∃ d, n = d + 2 := ⟨n - 2, by omega⟩
    nlinarith
  wram_omega [fits_of_lt_pow hlt]

/-- Under `2 ≤ n` and `logWidth 3 n ≤ w`, `highProbTrials n` fits in `w`-bit words. -/
theorem fits_highProbTrials_of_logWidth_three {n w : ℕ} (hn : 2 ≤ n) (hw : logWidth 3 n ≤ w) :
    Fits w (highProbTrials n) := by
  have hlt : highProbTrials n < (n + 1) ^ 3 := by
    unfold highProbTrials
    have hlog : Nat.log 2 n < n := Nat.log_lt_self 2 (by omega)
    have hlg2 : Nat.log 2 n + 2 ≤ n + 1 := by omega
    have hhalf : n * (n - 1) / 2 < n * n := by
      have hlt : n * (n - 1) < n * n := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
      exact lt_of_le_of_lt (Nat.div_le_self _ _) hlt
    have hmul : (n * (n - 1) / 2) * (Nat.log 2 n + 2) < (n * n) * (n + 1) := by
      have hpos : 0 < Nat.log 2 n + 2 := by omega
      calc
        (n * (n - 1) / 2) * (Nat.log 2 n + 2) < (n * n) * (Nat.log 2 n + 2) :=
          Nat.mul_lt_mul_of_pos_right hhalf hpos
        _ ≤ (n * n) * (n + 1) := Nat.mul_le_mul_left (n * n) hlg2
    have hcube : (n * n) * (n + 1) ≤ (n + 1) ^ 3 := by nlinarith
    exact lt_of_lt_of_le hmul hcube
  wram_omega [fits_of_lt_pow hlt]

/-- `logWidth 3 n ≤ w` and `Fits w (totalDoubledWeight W)` suffice for
`InputFits w (n :: flattenMatrix W)`. -/
theorem inputFits_single {n w : ℕ} {W : Fin n → Fin n → ℕ} (hn : 2 ≤ n)
    (hw : logWidth 3 n ≤ w) (htot : Fits w (totalDoubledWeight W)) :
    InputFits w (n :: flattenMatrix W) :=
  inputFits_cons_flattenMatrix (fits_workspace_of_logWidth_three hn hw) (by omega) (by omega) htot

/-- `logWidth 3 n ≤ w`, `Fits w R`, and `Fits w (totalDoubledWeight W)` suffice for
`InputFits w (R :: n :: flattenMatrix W)`. -/
theorem inputFits_amplified {R n w : ℕ} {W : Fin n → Fin n → ℕ} (hn : 2 ≤ n)
    (hw : logWidth 3 n ≤ w) (hR : Fits w R) (htot : Fits w (totalDoubledWeight W)) :
    InputFits w (R :: n :: flattenMatrix W) := by
  have hws := fits_workspace_of_logWidth_three hn hw
  refine ⟨?_, ?_⟩
  · simp only [List.length_cons, length_flattenMatrix]
    fits
  · intro v hv
    rcases List.mem_cons.mp hv with rfl | hv'
    · exact hR
    · rcases List.mem_cons.mp hv' with rfl | hmem
      · fits
      · fits [mem_flattenMatrix_le_totalDoubledWeight W hmem]

/-- In `Data.init (R :: n :: flattenMatrix W)`, memory holds `W` at base `3` with stride `n`. -/
theorem holdsMatrix_init_amplified {r R n : ℕ} (W : Fin n → Fin n → ℕ) :
    HoldsMatrix (Data.init (r := r) (R :: n :: flattenMatrix W)).mem 3 n W :=
  holdsMatrix_init_append [R, n] W

/-! ### Endpoint 1: Single-trial Basic Karger (`r = 16`) -/

section SingleTrial

open Reg

/-- Setup for `singleCode`: read `n` from `mem[1]` and configure `(wBase, dBase, stride, activeK,
targetT) = (2, 2 + n * n, n, n, 2)`. -/
def singleSetup : Code .standard 16 := ram[
  one ← #1;
  activeK ← *one;
  stride ← activeK;
  wBase ← #2;
  val1 ← activeK * activeK;
  dBase ← wBase + val1;
  targetT ← #2
]

/-- Postprocessing for `singleCode`: load the contracted superedge weight `mem[wBase + 1]` into
`val1`. -/
def singlePost : Code .standard 16 := ram[
  one ← #1;
  addr1 ← wBase + one;
  val1 ← *addr1
]

/-- Structured 16-register single-trial Karger contraction program on `n :: flattenMatrix W`. -/
def singleCode : Code .standard 16 := ram[
  ⟪singleSetup⟫;
  ⟪computeDegreesAndTotal⟫;
  ⟪contractDownTo⟫;
  ⟪singlePost⟫
]

/-- Compiled 16-register single-trial Karger contraction program. -/
def singleProgram : Program .standard 16 :=
  singleCode.program val1

/-- Worst-case instruction bound `42 * n ^ 2 + 12 * n + 21` for `singleProgram`. -/
@[wram_arith]
def singleTime (n : ℕ) : ℕ :=
  42 * n ^ 2 + 12 * n + 21

theorem singleSetup_exec {w n : ℕ} {W : Fin n → Fin n → ℕ} (hn : 2 ≤ n)
    (hw : logWidth 3 n ≤ w) :
    ∃ y : Data 16, Exec w singleSetup (Data.init (n :: flattenMatrix W)) y 7 ∧
      y.mem = (Data.init (r := 16) (n :: flattenMatrix W)).mem ∧
      y.regs wBase = 2 ∧ y.regs dBase = 2 + n * n ∧ y.regs stride = n ∧
      y.regs activeK = n ∧ y.regs targetT = 2 := by
  have hws := fits_workspace_of_logWidth_three hn hw
  have hm1 : (Data.init (r := 16) (n :: flattenMatrix W)).mem 1 = n := rfl
  unfold singleSetup
  wram_exec [hm1]
  exact ⟨rfl, by wram_simp⟩

theorem singlePost_exec {w wb : ℕ} {x : Data 16} (hwBase : x.regs wBase = wb)
    (h1 : Fits w 1) (hwb1 : Fits w (wb + 1)) :
    ∃ y : Data 16, Exec w singlePost x y 3 ∧
      y.mem = x.mem ∧ y.regs val1 = x.mem (wb + 1) := by
  unfold singlePost
  wram_exec [hwBase]
  exact ⟨rfl, by wram_simp⟩

/-- **A single trial runs `karger`.** At word size `w ≥ logWidth 3 n` with
`totalDoubledWeight W < 2 ^ w`, `singleCode` on `n :: flattenMatrix W` runs within
`singleTime n - 1` instructions and `n - 2` `rand` calls and writes only `[2, 2 + n * n + n)`. The
weight it leaves in `val1` has the law of the answer of `Lean.Karger.karger` on `⟨n, W⟩`:
`contractDownTo` contracts as the client does (`contractDownTo_law`), and `singlePost` reads the
weight between the last two supervertices, half their total weight. -/
theorem singleCode_law {n w : ℕ} {W : Fin n → Fin n → ℕ}
    (hn : 2 ≤ n) (hW : IsMultigraph W)
    (hw : logWidth 3 n ≤ w) (htot : Fits w (totalDoubledWeight W)) :
    ExecRandLaw w singleCode (Data.init (n :: flattenMatrix W))
      (fun y => Modifies (Finset.Ico 2 (2 + n * n + n))
        (Data.init (r := 16) (n :: flattenMatrix W)).mem y.mem)
      (42 * n ^ 2 + 12 * n + 20) (n - 2) (fun y => y.regs val1)
      (Lean.Karger.answerLaw ⟨n, W⟩) := by
  have hws_fit := fits_workspace_of_logWidth_three hn hw
  have hwEnd : Fits w (2 + n * n) := by fits
  have hdEnd : Fits w (2 + n * n + n) := by fits
  obtain ⟨y_s, e_s, hm_s, hwb_s, hdb_s, hstr_s, hk_s, ht_s⟩ := singleSetup_exec (W := W) hn hw
  obtain ⟨y_deg, e_deg, hws_d, hmod_d, _, _, hwb_d, hdb_d, hstr_d, hk_d, ht_d, htot_d⟩ :=
    computeDegreesAndTotal_exec (W := W) hwb_s hdb_s hstr_s hk_s (le_refl n) (Or.inl le_rfl)
      (by fits) hwEnd hdEnd htot (hm_s ▸ holdsMatrix_init_single W)
  have hst_deg : ContractState w 2 (2 + n * n) n n 2 W y_deg :=
    ⟨hwb_d, hdb_d, hstr_d, hk_d, ht_d.trans ht_s, htot_d, le_refl n, Or.inl le_rfl,
      hwEnd, hdEnd, htot, hws_d⟩
  have hrun := ExecRandLaw.seq (contractDownTo_law (le_refl 2) hn hW hst_deg)
    (κ := fun G => PMF.pure (totalDoubledWeight G.weight / 2)) fun y ⟨hmod_c, W', hW', hst'⟩ => by
      obtain ⟨y_p, e_p, hmem_p, hv_p⟩ :=
        singlePost_exec (w := w) hst'.regs_wBase (by fits) (by fits)
      have hmod : Modifies (Finset.Ico 2 (2 + n * n + n))
          (Data.init (r := 16) (n :: flattenMatrix W)).mem y_p.mem := by
        rw [hmem_p]
        exact modifies_trans_subset (hm_s ▸ hmod_d) hmod_c
          (Finset.Ico_subset_Ico (by omega) le_rfl)
          (workspaceFootprint_subset_Ico le_rfl le_rfl le_rfl)
      exact (ExecRandLaw.of_execWithin (f := fun y => y.regs val1) e_p.within hmod).congr_law
        (by rw [hv_p, hst'.mem_add_one hW'])
  refine ((ExecRandLaw.foldr_seq_det [singleSetup] (e_s.within.seq e_deg) hrun).congr_law
    ?_).mono (fun _ h => h) (by omega) (by omega)
  rw [Lean.Karger.answerLaw_eq]
  exact PMF.bind_pure_comp _ _

/-- **Single-trial Basic Karger specification (`singleProgram`).**
At word size `w ≥ logWidth 3 n` when `totalDoubledWeight W < 2 ^ w`:
1. `singleProgram` halts within `singleTime n = 42 * n ^ 2 + 12 * n + 21` steps;
2. executes at most `n - 2` `rand` calls;
3. on every supported branch, outputs `cutWeight W C ≥ minCut W` for a genuine non-trivial cut `C`
   of `W` while modifying memory only in `[2, 2 + n * n + n)`;
4. when `0 < minCut W` (excluded only for proof convenience; `S = 0` contraction still halts
   fault-free with a valid cut weight), outputs `minCut W` with probability at least
   `2 / (n * (n - 1))`. -/
theorem singleProgram_spec {n w : ℕ} {W : Fin n → Fin n → ℕ}
    (hn : 2 ≤ n) (hW : IsMultigraph W)
    (hw : logWidth 3 n ≤ w) (htot : Fits w (totalDoubledWeight W)) :
    let input := n :: flattenMatrix W
    RandHaltsWithin w singleProgram (.init input) (singleTime n) ∧
    RandCallsBounded w singleProgram (.init input) (singleTime n) (n - 2) ∧
    (∀ cfg ∈ (runRand w singleProgram (singleTime n) (.running (.init input))).support,
      ∃ (y : Data 16) (C : Finset (Fin n)),
        cfg = .halted (cutWeight W C) y ∧
        y.Bounded w ∧
        IsNonTrivialCut C ∧
        minCut W ≤ cutWeight W C ∧
        Modifies (Finset.Ico 2 (2 + n * n + n)) (Data.init (r := 16) input).mem y.mem) ∧
    (0 < minCut W →
      (2 : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞) ≤
        (evalRand w singleProgram (singleTime n) (.init input)).toOuterMeasure
          {cfg | ∃ y, cfg = .halted (minCut W) y}) := by
  intro input
  obtain ⟨hhalt, hcalls, hpost, hhit, -⟩ := program_of_law (T' := singleTime n)
    (singleCode_law hn hW hw htot) (by wram_omega) (inputFits_single hn hw htot)
    fun _ hv => Lean.Karger.exists_cut_of_mem_support_answerLaw hn hW hv
  refine ⟨hhalt, hcalls, hpost, fun hmin => le_trans ?_ hhit⟩
  rw [Lean.Karger.answerLaw, PMF.toOuterMeasure_map_apply]
  exact Lean.Karger.two_div_le_toOuterMeasure_karger hn hW hmin

end SingleTrial

/-! ### Shared `R`-trial amplification engine (`r = 22`) -/

/-- `16 ≤ 22`, used to embed `computeDegreesAndTotal` and `contractDownTo` into `Data 22`. -/
private theorem hr22 : 16 ≤ 22 := by decide

-- Register layout (`r = 22`) for repeated-trial Karger amplification: registers `0..15` match
-- `Reg` (`Contract.lean`), while `16..21` hold caller state preserved across contractions.
namespace AmpReg

/-- Constant register `0` (`Reg.zero` embedded into `Fin 22`). -/
abbrev zero : Fin 22 := 0
/-- Constant register `1` (`Reg.one` embedded into `Fin 22`). -/
abbrev one : Fin 22 := 1
/-- Working matrix base address (`Reg.wBase` embedded into `Fin 22`). -/
abbrev wBase : Fin 22 := 2
/-- Working degree-array base address (`Reg.dBase` embedded into `Fin 22`). -/
abbrev dBase : Fin 22 := 3
/-- Working matrix row stride (`Reg.stride` embedded into `Fin 22`). -/
abbrev stride : Fin 22 := 4
/-- Active supervertex count `k` (`Reg.activeK` embedded into `Fin 22`). -/
abbrev activeK : Fin 22 := 5
/-- Target supervertex count `t` (`Reg.targetT` embedded into `Fin 22`). -/
abbrev targetT : Fin 22 := 6
/-- Active doubled edge weight `S` (`Reg.totS` embedded into `Fin 22`). -/
abbrev totS : Fin 22 := 7
/-- Loop index scratch register (`Reg.idx` embedded into `Fin 22`). -/
abbrev idx : Fin 22 := 10
/-- Loop counter / remainder scratch register (`Reg.rem` embedded into `Fin 22`). -/
abbrev rem : Fin 22 := 11
/-- Primary scratch address register (`Reg.addr1` embedded into `Fin 22`). -/
abbrev addr1 : Fin 22 := 12
/-- Primary scratch value register (`Reg.val1` embedded into `Fin 22`). -/
abbrev val1 : Fin 22 := 14
/-- Secondary scratch value register (`Reg.val2` embedded into `Fin 22`). -/
abbrev val2 : Fin 22 := 15
/-- Base address of the immutable input matrix `W`. -/
abbrev srcBase : Fin 22 := 16
/-- Original vertex count `n`, preserved across all trials. -/
abbrev nOrig : Fin 22 := 17
/-- Word count `n * n` of the flattened matrix. -/
abbrev matLen : Fin 22 := 18
/-- Total number `R` of independent trials to execute. -/
abbrev numTrials : Fin 22 := 19
/-- Number of trials completed so far (`0 .. R`). -/
abbrev trialIdx : Fin 22 := 20
/-- Minimum cut weight seen across completed trials. -/
abbrev bestVal : Fin 22 := 21

end AmpReg

section AmplificationEngine

open AmpReg

/-- Injective register map embedding `Cslib.WordRAM.ArrayCopy` (`r = 7`) into `Fin 22` with
`(src, dst, len, idx, addr, value, one) = (srcBase, wBase, matLen, idx, addr1, val1, one)`. -/
def copyRegMap : Fin 7 → Fin 22 :=
  ![srcBase, wBase, matLen, idx, addr1, val1, one]

theorem copyRegMap_injective : Function.Injective copyRegMap := by
  decide

/-- Copy `matLen` words from `srcBase` to `wBase` via `Cslib.WordRAM.ArrayCopy.program`. -/
def copyMatrixCode : Code .standard 22 :=
  ArrayCopy.program.rename copyRegMap

theorem copyMatrixCode_exec {w sb wb n : ℕ} {W : Fin n → Fin n → ℕ} {x : Data 22}
    (hsb : x.regs srcBase = sb) (hwb : x.regs wBase = wb) (hlen : x.regs matLen = n * n)
    (hdisj : sb + n * n ≤ wb)
    (h1 : Fits w 1) (hwEnd : Fits w (wb + n * n))
    (hsrc_mat : HoldsMatrix x.mem sb n W) :
    ∃ y : Data 22, ExecWithin w copyMatrixCode x y (7 * (n * n) + 4) ∧
      HoldsMatrix y.mem wb n W ∧
      Modifies (Finset.Ico wb (wb + n * n)) x.mem y.mem ∧
      y.regs wBase = wb ∧ y.regs dBase = x.regs dBase ∧
      y.regs srcBase = sb ∧ y.regs nOrig = x.regs nOrig ∧
      y.regs matLen = n * n ∧ y.regs numTrials = x.regs numTrials ∧
      y.regs trialIdx = x.regs trialIdx ∧ y.regs bestVal = x.regs bestVal := by
  unfold copyMatrixCode
  refine WP.exists_execWithin ?_
  wram_call (ArrayCopy.exec (x.comap copyRegMap) h1 ..)
    renamed copyRegMap_injective with y ⟨⟨hy_mem, hy_src, hy_dst, hy_len⟩, hnot_in⟩
  simp only [show copyRegMap ArrayCopy.src = srcBase from rfl,
    show copyRegMap ArrayCopy.dst = wBase from rfl,
    show copyRegMap ArrayCopy.len = matLen from rfl,
    hsb, hwb, hlen] at hy_mem hy_src hy_dst hy_len ⊢
  refine ⟨le_rfl, fun i j => ?_, fun a ha => ?_, hy_dst, by regs_frame, hy_src,
    by regs_frame, hy_len, by regs_frame, by regs_frame, by regs_frame⟩
  · have hj_lt : i.val * n + j.val < n * n := by nlinarith [i.isLt, j.isLt]
    rw [hy_mem, show wb + i.val * n + j.val = wb + (i.val * n + j.val) by omega,
      ArrayCopy.copyPrefix_read hj_lt, ← Nat.add_assoc]
    exact hsrc_mat i j
  · rw [hy_mem, ArrayCopy.copyPrefix_outside (by rwa [Finset.mem_Ico] at ha)]

/-- Postprocessing at the end of each trial: extract `mem[wBase + 1]`, update `bestVal` (replacing
it unconditionally on trial `0` and taking the minimum thereafter), and increment `trialIdx`. -/
def ampTrialPost : Code .standard 22 := ram[
  zero ← #0;
  one ← #1;
  addr1 ← wBase + one;
  val1 ← *addr1;
  if trialIdx = zero then [
    bestVal ← val1
  ] else [
    if val1 < bestVal then [
      bestVal ← val1
    ] else [
      zero ← #0
    ]
  ];
  trialIdx ← trialIdx + one
]

/-- Single amplification trial: copy `[srcBase, srcBase + n * n)` into `wBase`, initialize row
degrees at `dBase`, contract down to `2` supervertices, and update `bestVal`. -/
def ampTrialBody : Code .standard 22 := ram[
  ⟪copyMatrixCode⟫;
  activeK ← nOrig;
  stride ← nOrig;
  targetT ← #2;
  ⟪computeDegreesAndTotalAt (by decide)⟫;
  ⟪contractDownToAt (by decide)⟫;
  ⟪ampTrialPost⟫
]

/-- Loop running `numTrials` independent contractions. -/
def ampLoop : Code .standard 22 := ram[
  while trialIdx < numTrials do [ ⟪ampTrialBody⟫ ]
]

/-- Shared amplification core assuming `srcBase`, `nOrig`, and `numTrials` are initialized in
registers. -/
def ampCore : Code .standard 22 := ram[
  val1 ← nOrig * nOrig;
  matLen ← val1;
  wBase ← srcBase + matLen;
  dBase ← wBase + matLen;
  trialIdx ← #0;
  bestVal ← #0;
  ⟪ampLoop⟫
]

/-- Loop invariant for `ampLoop` at `trialIdx = i ≤ R`. -/
structure AmpInv (w sb n R i : ℕ) (W : Fin n → Fin n → ℕ) (mem₀ : ℕ → ℕ)
    (x : Data 22) : Prop where
  regs_srcBase : x.regs srcBase = sb
  regs_wBase : x.regs wBase = sb + n * n
  regs_dBase : x.regs dBase = sb + 2 * (n * n)
  regs_nOrig : x.regs nOrig = n
  regs_matLen : x.regs matLen = n * n
  regs_numTrials : x.regs numTrials = R
  regs_trialIdx : x.regs trialIdx = i
  src_matrix : HoldsMatrix x.mem sb n W
  modifies_ws : Modifies (Finset.Ico (sb + n * n) (sb + 2 * (n * n) + n)) mem₀ x.mem

theorem ampTrialPost_exec {w wb i R : ℕ} {x : Data 22}
    (hwb : x.regs wBase = wb) (hti : x.regs trialIdx = i) (hiR : i < R)
    (h1 : Fits w 1) (hwb1 : Fits w (wb + 1)) (hR_fit : Fits w R) :
    ∃ y : Data 22, ExecWithin w ampTrialPost x y 10 ∧
      y.mem = x.mem ∧
      y.regs srcBase = x.regs srcBase ∧
      y.regs wBase = wb ∧
      y.regs dBase = x.regs dBase ∧
      y.regs nOrig = x.regs nOrig ∧
      y.regs matLen = x.regs matLen ∧
      y.regs numTrials = x.regs numTrials ∧
      y.regs trialIdx = i + 1 ∧
      y.regs bestVal =
        (if i = 0 then x.mem (wb + 1) else min (x.mem (wb + 1)) (x.regs bestVal)) := by
  unfold ampTrialPost
  wram_exec -split [hwb]
  wram_call (minUpdate_exec (by decide) (by wram_simp)) with s₂ ⟨hm2, hbv2, hfr⟩
  wram_exec [hfr one (by decide), hfr trialIdx (by decide), hti]
  exact ⟨hm2, by regs_frame, by regs_frame, by regs_frame, by regs_frame, by regs_frame,
    by regs_frame, by wram_simp, by wram_simp [hbv2, hti]⟩

/-- **One trial runs `karger`.** From `AmpInv` at trial `i < R`, `ampTrialBody` runs within
`49 n² + 12 n + 27` instructions and `n - 2` `rand` calls and keeps the invariant at trial `i + 1`.
Its new `bestVal` has the law of the answer `v` of `Lean.Karger.karger` on `⟨n, W⟩`, taken as is on
the first trial and as `min v bestVal` after: `contractDownToAt` contracts the fresh copy of `W` as
the client does (`contractDownToAt_law`), and `ampTrialPost` reads the weight between the last two
supervertices, half their total weight. -/
theorem ampTrialBody_law {w sb n R i : ℕ} {W : Fin n → Fin n → ℕ} {mem₀ : ℕ → ℕ} {x : Data 22}
    (hn : 2 ≤ n) (hW : IsMultigraph W) (hiR : i < R)
    (h1 : Fits w 1) (hdEnd : Fits w (sb + 2 * (n * n) + n))
    (hR_fit : Fits w R) (htot : Fits w (totalDoubledWeight W))
    (hinv : AmpInv w sb n R i W mem₀ x) :
    ExecRandLaw w ampTrialBody x (AmpInv w sb n R (i + 1) W mem₀) (49 * n ^ 2 + 12 * n + 27)
      (n - 2) (fun y => y.regs bestVal)
      ((Lean.Karger.answerLaw ⟨n, W⟩).map fun v =>
        if i = 0 then v else min v (x.regs bestVal)) := by
  let wb := sb + n * n
  let db := sb + 2 * (n * n)
  have hwEnd : Fits w (wb + n * n) := by fits
  obtain ⟨y_deg, e_pre, hst_deg, hmod_deg'⟩ : ∃ y_deg,
      ExecWithin w
        ram[⟪copyMatrixCode⟫; activeK ← nOrig; stride ← nOrig; targetT ← #2;
            ⟪computeDegreesAndTotalAt hr22⟫]
        x y_deg (7 * (n * n) + 4 + 3 + (6 * n ^ 2 + 12 * n + 6)) ∧
      ContractState w wb db n n 2 W (y_deg.comap (Fin.castLE hr22)) ∧
      Modifies (Finset.Ico wb (db + n)) x.mem y_deg.mem := by
    refine WP.exists_execWithin (WP.seq ?_)
    wram_call (copyMatrixCode_exec hinv.regs_srcBase hinv.regs_wBase hinv.regs_matLen
      le_rfl h1 hwEnd hinv.src_matrix) with y_cp ⟨hmat_cp, hmod_cp,
        hwb_cp, hdb_cp, _, hn_cp, _, _, _, _⟩
    wram_exec [hn_cp, hinv.regs_nOrig]
    wram_call (computeDegreesAndTotalAt_exec hr22
      (by wram_simp; exact hwb_cp) (by wram_simp; exact hdb_cp.trans hinv.regs_dBase)
      (by wram_simp) (by wram_simp) (le_refl n) (Or.inl (by omega)) h1 hwEnd hdEnd htot hmat_cp)
      with y_deg ⟨hws_deg, hmod_deg, hwb_d, hdb_d, hstr_d, hk_d, ht_d, htot_d, _⟩
    have ht_d' : y_deg.regs (Fin.castLE hr22 Reg.targetT) = 2 := by
      rw [ht_d]; wram_simp
    exact ⟨by omega, ⟨hwb_d, hdb_d, hstr_d, hk_d, ht_d', htot_d,
      le_refl n, Or.inl (by omega), hwEnd, hdEnd, htot, hws_deg⟩,
      modifies_trans_subset hmod_cp hmod_deg (Finset.Ico_subset_Ico le_rfl (by omega))
        (Finset.Ico_subset_Ico (by omega) le_rfl)⟩
  have hrun := ExecRandLaw.seq (contractDownToAt_law hr22 (le_refl 2) hn hW hst_deg)
    (κ := fun G => PMF.pure (if i = 0 then totalDoubledWeight G.weight / 2
      else min (totalDoubledWeight G.weight / 2) (x.regs bestVal)))
    fun y ⟨hmod_c, hy_hi, W', hW', hst'⟩ => by
      have hz_ti : y.regs trialIdx = i := by regs_frame
      obtain ⟨y_p, e_p, hm_p, hsb_p, hwb_p, hdb_p, hn_p, hml_p, hnt_p, hti_p, hbv_p⟩ :=
        ampTrialPost_exec hst'.regs_wBase hz_ti hiR h1 (by fits) hR_fit
      have hmod : Modifies (Finset.Ico wb (db + n)) x.mem y_p.mem := by
        rw [hm_p]
        exact modifies_trans_subset hmod_deg' hmod_c Finset.Subset.rfl
          (workspaceFootprint_subset_Ico le_rfl (by omega) le_rfl)
      refine (ExecRandLaw.of_execWithin (P := AmpInv w sb n R (i + 1) W mem₀)
        (f := fun y => y.regs bestVal) e_p ⟨by regs_frame, hwb_p, hdb_p.trans hst'.regs_dBase,
        by regs_frame, by regs_frame, by regs_frame, hti_p, fun a b => ?_,
        modifies_trans_subset hinv.modifies_ws hmod Finset.Subset.rfl
          Finset.Subset.rfl⟩).congr_law ?_
      · have hlt := matAddr_lt_end (wb := sb) (le_refl n) a b
        rw [hmod _ (by rw [Finset.mem_Ico]; omega)]
        exact hinv.src_matrix a b
      · have hv : y.mem (wb + 1) = _ := hst'.mem_add_one hW'
        rw [hbv_p, show y.regs bestVal = x.regs bestVal by regs_frame, hv]
  refine ((ExecRandLaw.foldr_seq_det
    [copyMatrixCode, ram[activeK ← nOrig], ram[stride ← nOrig], ram[targetT ← #2]]
    e_pre hrun).congr_law ?_).mono (fun _ h => h) ?_ (by omega)
  · rw [Lean.Karger.answerLaw_eq, PMF.map_comp]
    exact PMF.bind_pure_comp _ _
  · have hnn : n * n = n ^ 2 := (sq n).symm
    omega

/-- **The loop of trials runs amplified Karger.** From `AmpInv` at trial `i`, with `rem = R - i`
trials left, `ampLoop` runs within `rem (50 n² + 12 n + 30) + 2` instructions and `rem (n - 2)`
`rand` calls and ends at trial `R`. Its `bestVal` has the law of the amplification client run
against independent runs of `Lean.Karger.karger` on `⟨n, W⟩`: of `Lean.Karger.minRuns rem` on the
first trial, and of `rem` more `Lean.Karger.minStep`s from `bestVal` after. -/
theorem ampLoop_law {w sb n R : ℕ} {W : Fin n → Fin n → ℕ} {mem₀ : ℕ → ℕ}
    (hR : 1 ≤ R) (hn : 2 ≤ n) (hW : IsMultigraph W)
    (h1 : Fits w 1) (hdEnd : Fits w (sb + 2 * (n * n) + n))
    (hR_fit : Fits w R) (htot : Fits w (totalDoubledWeight W)) :
    ∀ (rem i : ℕ) (x : Data 22), i + rem = R → AmpInv w sb n R i W mem₀ x →
      ExecRandLaw w ampLoop x (AmpInv w sb n R R W mem₀)
        (rem * (50 * n ^ 2 + 12 * n + 30) + 2) (rem * (n - 2)) (fun y => y.regs bestVal)
        (OracleComp.evalWith (fun _ => Lean.Karger.answerLaw ⟨n, W⟩)
          (if i = 0 then Lean.Karger.minRuns rem
            else OracleComp.iterate rem Lean.Karger.minStep (x.regs bestVal))) := by
  unfold ampLoop
  exact minRunsLoop_law hR (by omega) (fun _ _ h => h.regs_trialIdx) (fun _ _ h => h.regs_numTrials)
    fun _ _ hi h => ampTrialBody_law hn hW hi h1 hdEnd hR_fit htot h

/-- **The amplification core runs amplified Karger.** For `1 ≤ R` trials, from a state with
`srcBase = sb`, `nOrig = n`, `numTrials = R` and `HoldsMatrix x.mem sb n W`, `ampCore` runs within
`R (50 n² + 12 n + 30) + 8` instructions and `R (n - 2)` `rand` calls and writes only the
workspace. Its `bestVal` has the law of `Lean.Karger.minRuns R` against independent runs of
`Lean.Karger.karger` on `⟨n, W⟩`. -/
theorem ampCore_law {w sb n R : ℕ} {W : Fin n → Fin n → ℕ} {x : Data 22}
    (hR : 1 ≤ R) (hn : 2 ≤ n) (hW : IsMultigraph W)
    (hsb : x.regs srcBase = sb) (hnOrig : x.regs nOrig = n) (hnumT : x.regs numTrials = R)
    (h1 : Fits w 1) (hdEnd : Fits w (sb + 2 * (n * n) + n))
    (hR_fit : Fits w R) (htot : Fits w (totalDoubledWeight W))
    (hsrc_mat : HoldsMatrix x.mem sb n W) :
    ExecRandLaw w ampCore x
      (fun y => Modifies (Finset.Ico (sb + n * n) (sb + 2 * (n * n) + n)) x.mem y.mem)
      (R * (50 * n ^ 2 + 12 * n + 30) + 8) (R * (n - 2)) (fun y => y.regs bestVal)
      (OracleComp.evalWith (fun _ => Lean.Karger.answerLaw ⟨n, W⟩) (Lean.Karger.minRuns R)) := by
  obtain ⟨s₆, e_pre, hinv₀⟩ : ∃ s₆,
      ExecWithin w
        ram[val1 ← nOrig * nOrig; matLen ← val1; wBase ← srcBase + matLen;
            dBase ← wBase + matLen; trialIdx ← #0; bestVal ← #0] x s₆ 6 ∧
      AmpInv w sb n R 0 W x.mem s₆ := by
    wram_exec [hsb, hnOrig]
    refine ⟨by wram_simp [hsb], by wram_simp, ?_, by wram_simp [hnOrig], by wram_simp,
      by wram_simp [hnumT], by wram_simp, hsrc_mat, Modifies.refl _ _⟩
    wram_simp; omega
  have hloop := ampLoop_law (mem₀ := x.mem) hR hn hW h1 hdEnd hR_fit htot R 0 s₆
    (Nat.zero_add R) hinv₀
  rw [ite_eq_left rfl] at hloop
  exact (ExecRandLaw.foldr_seq_det
    [ram[val1 ← nOrig * nOrig], ram[matLen ← val1], ram[wBase ← srcBase + matLen],
      ram[dBase ← wBase + matLen], ram[trialIdx ← #0]]
    e_pre hloop).mono (fun _ h => h.modifies_ws) (by omega) le_rfl

end AmplificationEngine

/-! ### Endpoint 2: Amplified `R`-trial Karger (`r = 22`) -/

section Amplified

open AmpReg

/-- Setup for `amplifiedCode` on `R :: n :: flattenMatrix W`: load `R = mem[1]`, `n = mem[2]`, and
set `srcBase = 3`. -/
def amplifiedSetup : Code .standard 22 := ram[
  one ← #1;
  numTrials ← *one;
  srcBase ← #2;
  nOrig ← *srcBase;
  srcBase ← #3
]

/-- Structured 22-register `R`-trial Karger program on `R :: n :: flattenMatrix W`. -/
def amplifiedCode : Code .standard 22 := ram[
  ⟪amplifiedSetup⟫;
  ⟪ampCore⟫
]

/-- Compiled 22-register `R`-trial Karger program. -/
def amplifiedProgram : Program .standard 22 :=
  amplifiedCode.program bestVal

/-- Worst-case instruction bound `R * (50 * n ^ 2 + 12 * n + 30) + 16` for `amplifiedProgram`. -/
@[wram_arith]
def amplifiedTime (R n : ℕ) : ℕ :=
  R * (50 * n ^ 2 + 12 * n + 30) + 16

theorem amplifiedSetup_exec {w R n : ℕ} {W : Fin n → Fin n → ℕ}
    (hn : 2 ≤ n) (hw : logWidth 3 n ≤ w) :
    ∃ y : Data 22, Exec w amplifiedSetup (Data.init (R :: n :: flattenMatrix W)) y 5 ∧
      y.mem = (Data.init (r := 22) (R :: n :: flattenMatrix W)).mem ∧
      y.regs srcBase = 3 ∧ y.regs nOrig = n ∧ y.regs numTrials = R := by
  have hws := fits_workspace_of_logWidth_three hn hw
  have hm1 : (Data.init (r := 22) (R :: n :: flattenMatrix W)).mem 1 = R := rfl
  have hm2 : (Data.init (r := 22) (R :: n :: flattenMatrix W)).mem 2 = n := rfl
  unfold amplifiedSetup
  wram_exec [hm1, hm2]
  exact ⟨rfl, by wram_simp⟩

/-- **`amplifiedCode` runs amplified Karger.** At word size `w ≥ logWidth 3 n` with `1 ≤ R`,
`R < 2 ^ w` and `totalDoubledWeight W < 2 ^ w`, `amplifiedCode` on `R :: n :: flattenMatrix W` runs
within `amplifiedTime R n - 1` instructions and `R (n - 2)` `rand` calls and writes only
`[3 + n * n, 3 + 2 * (n * n) + n)`. Its `bestVal` has the law of `Lean.Karger.minRuns R` against
independent runs of `Lean.Karger.karger` on `⟨n, W⟩`. -/
theorem amplifiedCode_law {R n w : ℕ} {W : Fin n → Fin n → ℕ}
    (hR : 1 ≤ R) (hn : 2 ≤ n) (hW : IsMultigraph W)
    (hw : logWidth 3 n ≤ w) (hR_fit : Fits w R) (htot : Fits w (totalDoubledWeight W)) :
    ExecRandLaw w amplifiedCode (Data.init (R :: n :: flattenMatrix W))
      (fun y => Modifies (Finset.Ico (3 + n * n) (3 + 2 * (n * n) + n))
        (Data.init (r := 22) (R :: n :: flattenMatrix W)).mem y.mem)
      (R * (50 * n ^ 2 + 12 * n + 30) + 15) (R * (n - 2)) (fun y => y.regs bestVal)
      (OracleComp.evalWith (fun _ => Lean.Karger.answerLaw ⟨n, W⟩) (Lean.Karger.minRuns R)) := by
  have hws := fits_workspace_of_logWidth_three hn hw
  obtain ⟨y_s, e_s, hm_s, hsb_s, hn_s, hnt_s⟩ := amplifiedSetup_exec (R := R) (W := W) hn hw
  exact (ExecRandLaw.seq_det e_s.within (ampCore_law hR hn hW hsb_s hn_s hnt_s
    (by fits) hws hR_fit htot (hm_s ▸ holdsMatrix_init_amplified W))).mono
    (fun _ h => hm_s ▸ h) (by omega) le_rfl

/-- **`R`-trial amplified Karger specification (`amplifiedProgram`).**
At word size `w ≥ logWidth 3 n` when `1 ≤ R`, `R < 2 ^ w`, and `totalDoubledWeight W < 2 ^ w`:
1. `amplifiedProgram` halts within `amplifiedTime R n = R * (50 * n ^ 2 + 12 * n + 30) + 16` steps;
2. executes at most `R * (n - 2)` `rand` calls;
3. on every supported branch, outputs `cutWeight W C ≥ minCut W` for a genuine non-trivial cut `C`
   of `W` while modifying memory only in `[3 + n * n, 3 + 2 * (n * n) + n)`;
4. when `0 < minCut W` (excluded only for proof convenience; `S = 0` contraction still halts
   fault-free with a valid cut weight), misses `minCut W` with probability at most
   `(1 - 2 / (n * (n - 1))) ^ R`. -/
theorem amplifiedProgram_spec {R n w : ℕ} {W : Fin n → Fin n → ℕ}
    (hR : 1 ≤ R) (hn : 2 ≤ n) (hW : IsMultigraph W)
    (hw : logWidth 3 n ≤ w) (hR_fit : Fits w R) (htot : Fits w (totalDoubledWeight W)) :
    let input := R :: n :: flattenMatrix W
    RandHaltsWithin w amplifiedProgram (.init input) (amplifiedTime R n) ∧
    RandCallsBounded w amplifiedProgram (.init input) (amplifiedTime R n) (R * (n - 2)) ∧
    (∀ cfg ∈ (runRand w amplifiedProgram (amplifiedTime R n) (.running (.init input))).support,
      ∃ (y : Data 22) (C : Finset (Fin n)),
        cfg = .halted (cutWeight W C) y ∧
        y.Bounded w ∧
        IsNonTrivialCut C ∧
        minCut W ≤ cutWeight W C ∧
        Modifies (Finset.Ico (3 + n * n) (3 + 2 * (n * n) + n))
          (Data.init (r := 22) input).mem y.mem) ∧
    (0 < minCut W →
      (evalRand w amplifiedProgram (amplifiedTime R n) (.init input)).toOuterMeasure
          {cfg | ∀ y, cfg ≠ .halted (minCut W) y} ≤
        ((1 : ℝ≥0∞) - (2 : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞)) ^ R) := by
  intro input
  obtain ⟨hhalt, hcalls, hpost, -, hmiss⟩ :=
    program_of_law (T' := amplifiedTime R n) (amplifiedCode_law hR hn hW hw hR_fit htot)
      (by wram_omega)
      (inputFits_amplified hn hw hR_fit htot)
      fun _ hv => Lean.Karger.exists_cut_of_mem_support_answerLaw hn hW
        (Lean.Karger.mem_support_minRuns (by omega) hv)
  exact ⟨hhalt, hcalls, hpost, fun hmin =>
    hmiss.trans (Lean.Karger.minRuns_ne_minCut_le hn hW hmin R)⟩

end Amplified

/-! ### Endpoint 3: Explicit `O(n ^ 4 log n)` high-probability global minimum cut (`r = 22`) -/

section HighProb

open AmpReg

/-- Body of `logLoop`: halve `rem` via right-shift by `1` and increment `idx`. -/
def logStep : Code .standard 22 := ram[
  rem ← rem >>> one;
  idx ← idx + one
]

/-- Loop computing `idx = Nat.log 2 n` from `rem = n` (`n ≥ 1`), `idx = 0`, `one = 1`. -/
def logLoop : Code .standard 22 := ram[
  while one < rem do [ ⟪logStep⟫ ]
]

/-- Setup for `highProbCode` on `n :: flattenMatrix W`: load `n = mem[1]`, compute
`numTrials = highProbTrials n = (n * (n - 1) / 2) * (Nat.log 2 n + 2)` using shifts and
multiplications, and set `srcBase = 2`. -/
def highProbSetup : Code .standard 22 := ram[
  one ← #1;
  nOrig ← *one;
  rem ← nOrig;
  idx ← #0;
  ⟪logLoop⟫;
  val2 ← #2;
  idx ← idx + val2;
  val1 ← nOrig - one;
  val1 ← nOrig * val1;
  val1 ← val1 >>> one;
  numTrials ← val1 * idx;
  srcBase ← #2
]

/-- Structured 22-register `O(n ^ 4 log n)` high-probability Karger program on
`n :: flattenMatrix W`. -/
def highProbCode : Code .standard 22 := ram[
  ⟪highProbSetup⟫;
  ⟪ampCore⟫
]

/-- Compiled 22-register `O(n ^ 4 log n)` high-probability Karger program. -/
def highProbProgram : Program .standard 22 :=
  highProbCode.program bestVal

/-- Worst-case instruction bound `33 * n ^ 4 * (Nat.log 2 n + 2)` for `highProbProgram`. -/
def highProbTime (n : ℕ) : ℕ :=
  33 * n ^ 4 * (Nat.log 2 n + 2)

theorem logLoop_exec {w n : ℕ} {x : Data 22} (hn : 1 ≤ n)
    (hone : x.regs one = 1) (hrem : x.regs rem = n) (hidx : x.regs idx = 0)
    (hnOrig : x.regs nOrig = n)
    (hn_fit : Fits w n) (hlg_fit : Fits w (Nat.log 2 n)) :
    ∃ y : Data 22, ExecWithin w logLoop x y (4 * Nat.log 2 n + 2) ∧
      y.mem = x.mem ∧
      y.regs one = 1 ∧
      y.regs nOrig = n ∧
      y.regs idx = Nat.log 2 n := by
  obtain ⟨y, he, hm, hidx', hframe⟩ := NatLog.shiftLoop_exec (one := one) (rem := rem)
    (idx := idx) (by decide) (by decide) (by decide) hn hone hrem hidx hn_fit hlg_fit
  exact ⟨y, he, hm, by regs_frame, by regs_frame, hidx'⟩

theorem highProbSetup_exec {w n : ℕ} {W : Fin n → Fin n → ℕ}
    (hn : 2 ≤ n) (hw : logWidth 3 n ≤ w) :
    ∃ y : Data 22,
      ExecWithin w highProbSetup (Data.init (n :: flattenMatrix W)) y (4 * Nat.log 2 n + 13) ∧
      y.mem = (Data.init (r := 22) (n :: flattenMatrix W)).mem ∧
      y.regs srcBase = 2 ∧
      y.regs nOrig = n ∧
      y.regs numTrials = highProbTrials n := by
  have hws := fits_workspace_of_logWidth_three hn hw
  have hhp_fit := fits_highProbTrials_of_logWidth_three hn hw
  have hlog_lt : Nat.log 2 n < n := Nat.log_lt_self 2 (by omega)
  have hmul_le : n * (n - 1) ≤ n * n := Nat.mul_le_mul_left n (Nat.sub_le n 1)
  have hdiv_le : n * (n - 1) / 2 ≤ n * (n - 1) := Nat.div_le_self _ _
  have hshr : (n * (n - 1)) >>> 1 = n * (n - 1) / 2 := by rw [Nat.shiftRight_eq_div_pow, pow_one]
  have hhp_eq : n * (n - 1) / 2 * (Nat.log 2 n + 2) = highProbTrials n := rfl
  have hm1 : (Data.init (r := 22) (n :: flattenMatrix W)).mem 1 = n := rfl
  unfold highProbSetup
  wram_exec [hm1]
  wram_call (logLoop_exec (w := w) (n := n) (by omega) (by wram_simp) (by wram_simp) (by wram_simp)
    (by wram_simp) (by fits) (by fits)) with s₅ ⟨hm5, ho5, hn5, hidx5⟩
  wram_exec [ho5, hn5, hidx5, hshr, hhp_eq]
  exact ⟨hm5, by wram_simp [hn5]⟩

/-- The setup's `4 log₂ n + 13` instructions, the `highProbTrials n` trials'
`highProbTrials n (50 n² + 12 n + 30) + 8` and the final halt fit in `highProbTime n`. -/
theorem highProbTime_bound {n : ℕ} (hn : 2 ≤ n) :
    4 * Nat.log 2 n + highProbTrials n * (50 * n ^ 2 + 12 * n + 30) + 22 ≤ highProbTime n := by
  unfold highProbTime highProbTrials
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 2 := ⟨n - 2, by omega⟩
  have h1 : 50 * (d + 2) ^ 2 + 12 * (d + 2) + 30 ≤ 64 * (d + 2) ^ 2 := by nlinarith
  have h2 : ((d + 2) * (d + 2 - 1) / 2) * (64 * (d + 2) ^ 2) ≤ 32 * (d + 2) ^ 4 := by
    have hdiv : 2 * ((d + 2) * (d + 2 - 1) / 2) ≤ (d + 2) * (d + 1) := by
      have hsub : d + 2 - 1 = d + 1 := by omega
      rw [hsub]
      omega
    nlinarith
  have htrial : (((d + 2) * (d + 2 - 1) / 2) * (Nat.log 2 (d + 2) + 2)) *
      (50 * (d + 2) ^ 2 + 12 * (d + 2) + 30) ≤
      32 * (d + 2) ^ 4 * (Nat.log 2 (d + 2) + 2) := by
    calc
      (((d + 2) * (d + 2 - 1) / 2) * (Nat.log 2 (d + 2) + 2)) *
          (50 * (d + 2) ^ 2 + 12 * (d + 2) + 30)
        ≤ (((d + 2) * (d + 2 - 1) / 2) * (Nat.log 2 (d + 2) + 2)) * (64 * (d + 2) ^ 2) := by gcongr
      _ = (((d + 2) * (d + 2 - 1) / 2) * (64 * (d + 2) ^ 2)) * (Nat.log 2 (d + 2) + 2) := by ring
      _ ≤ (32 * (d + 2) ^ 4) * (Nat.log 2 (d + 2) + 2) := Nat.mul_le_mul_right _ h2
  have hoverhead : 4 * Nat.log 2 (d + 2) + 22 ≤ 1 * (d + 2) ^ 4 * (Nat.log 2 (d + 2) + 2) := by
    have hpow4 : 16 ≤ (d + 2) ^ 4 := by nlinarith
    nlinarith
  calc
    4 * Nat.log 2 (d + 2) +
        ((d + 2) * (d + 2 - 1) / 2 * (Nat.log 2 (d + 2) + 2)) *
          (50 * (d + 2) ^ 2 + 12 * (d + 2) + 30) + 22
      = (4 * Nat.log 2 (d + 2) + 22) +
          (((d + 2) * (d + 2 - 1) / 2 * (Nat.log 2 (d + 2) + 2)) *
            (50 * (d + 2) ^ 2 + 12 * (d + 2) + 30)) := by ring
    _ ≤ 1 * (d + 2) ^ 4 * (Nat.log 2 (d + 2) + 2) +
          32 * (d + 2) ^ 4 * (Nat.log 2 (d + 2) + 2) := Nat.add_le_add hoverhead htrial
    _ = 33 * (d + 2) ^ 4 * (Nat.log 2 (d + 2) + 2) := by ring

/-- **`highProbCode` runs amplified Karger.** At word size `w ≥ logWidth 3 n` with
`totalDoubledWeight W < 2 ^ w`, `highProbCode` on `n :: flattenMatrix W` runs within
`4 log₂ n + highProbTrials n (50 n² + 12 n + 30) + 21` instructions and
`highProbTrials n (n - 2)` `rand` calls and writes only `[2 + n * n, 2 + 2 * (n * n) + n)`. Its
`bestVal` has the law of `Lean.Karger.minRuns (highProbTrials n)` against independent runs of
`Lean.Karger.karger` on `⟨n, W⟩`. -/
theorem highProbCode_law {n w : ℕ} {W : Fin n → Fin n → ℕ}
    (hn : 2 ≤ n) (hW : IsMultigraph W)
    (hw : logWidth 3 n ≤ w) (htot : Fits w (totalDoubledWeight W)) :
    ExecRandLaw w highProbCode (Data.init (n :: flattenMatrix W))
      (fun y => Modifies (Finset.Ico (2 + n * n) (2 + 2 * (n * n) + n))
        (Data.init (r := 22) (n :: flattenMatrix W)).mem y.mem)
      (4 * Nat.log 2 n + highProbTrials n * (50 * n ^ 2 + 12 * n + 30) + 21)
      (highProbTrials n * (n - 2)) (fun y => y.regs bestVal)
      (OracleComp.evalWith (fun _ => Lean.Karger.answerLaw ⟨n, W⟩)
        (Lean.Karger.minRuns (highProbTrials n))) := by
  have hws := fits_workspace_of_logWidth_three hn hw
  obtain ⟨y_s, e_s, hm_s, hsb_s, hn_s, hnt_s⟩ := highProbSetup_exec (W := W) hn hw
  exact (ExecRandLaw.seq_det e_s (ampCore_law (highProbTrials_pos hn) hn hW hsb_s hn_s hnt_s
    (by fits) (by fits) (fits_highProbTrials_of_logWidth_three hn hw)
    htot (hm_s ▸ holdsMatrix_init_single W))).mono (fun _ h => hm_s ▸ h) (by omega) le_rfl

/-- **Explicit `O(n ^ 4 log n)` high-probability global minimum cut (`highProbProgram`).**
At word size `w ≥ logWidth 3 n` when `2 ≤ n` and `totalDoubledWeight W < 2 ^ w`:
1. `highProbProgram` halts within `highProbTime n = 33 * n ^ 4 * (Nat.log 2 n + 2)` steps;
2. executes at most `highProbTrials n * (n - 2)` `rand` calls;
3. on every supported branch, outputs `cutWeight W C ≥ minCut W` for a genuine non-trivial cut `C`
   of `W` while modifying memory only in `[2 + n * n, 2 + 2 * (n * n) + n)`;
4. when `0 < minCut W` (excluded only for proof convenience; `S = 0` contraction still halts
   fault-free with a valid cut weight), misses `minCut W` with probability at most `1 / (2 * n)`. -/
theorem highProbProgram_spec {n w : ℕ} {W : Fin n → Fin n → ℕ}
    (hn : 2 ≤ n) (hW : IsMultigraph W)
    (hw : logWidth 3 n ≤ w) (htot : Fits w (totalDoubledWeight W)) :
    let input := n :: flattenMatrix W
    RandHaltsWithin w highProbProgram (.init input) (highProbTime n) ∧
    RandCallsBounded w highProbProgram (.init input) (highProbTime n)
      (highProbTrials n * (n - 2)) ∧
    (∀ cfg ∈ (runRand w highProbProgram (highProbTime n) (.running (.init input))).support,
      ∃ (y : Data 22) (C : Finset (Fin n)),
        cfg = .halted (cutWeight W C) y ∧
        y.Bounded w ∧
        IsNonTrivialCut C ∧
        minCut W ≤ cutWeight W C ∧
        Modifies (Finset.Ico (2 + n * n) (2 + 2 * (n * n) + n))
          (Data.init (r := 22) input).mem y.mem) ∧
    (0 < minCut W →
      (evalRand w highProbProgram (highProbTime n) (.init input)).toOuterMeasure
          {cfg | ∀ y, cfg ≠ .halted (minCut W) y} ≤
        (1 : ℝ≥0∞) / ((2 * n : ℕ) : ℝ≥0∞)) := by
  intro input
  obtain ⟨hhalt, hcalls, hpost, -, hmiss⟩ :=
    program_of_law (highProbCode_law hn hW hw htot) (highProbTime_bound hn)
      (inputFits_single hn hw htot) fun _ hv =>
        Lean.Karger.exists_cut_of_mem_support_answerLaw hn hW
          (Lean.Karger.mem_support_minRuns (Nat.one_le_iff_ne_zero.mp (highProbTrials_pos hn)) hv)
  exact ⟨hhalt, hcalls, hpost, fun hmin =>
    (hmiss.trans (Lean.Karger.minRuns_ne_minCut_le hn hW hmin _)).trans (highProb_failure_le hn)⟩

/-- `highProbProgram` misses `minCut W` with probability at most `1 / n`, unconditionally without
`2 ≤ n` or `0 < minCut W`: for `n < 2` the bound `1 / n` is at least `1`, and for `2 ≤ n` with
`minCut W = 0` every contraction trial outputs `0`. -/
theorem highProbProgram_failure_le_inv_n {n w : ℕ} {W : Fin n → Fin n → ℕ}
    (hW : IsMultigraph W)
    (hw : logWidth 3 n ≤ w) (htot : Fits w (totalDoubledWeight W)) :
    (evalRand w highProbProgram (highProbTime n) (.init (n :: flattenMatrix W))).toOuterMeasure
        {cfg | ∀ y, cfg ≠ .halted (minCut W) y} ≤
      (1 : ℝ≥0∞) / (n : ℝ≥0∞) :=
  program_failure_le_inv_n fun hn =>
    ⟨_, _, _, _, highProbCode_law hn hW hw htot, highProbTime_bound hn,
      fun hpos => (Lean.Karger.minRuns_ne_minCut_le hn hW hpos _).trans (highProb_failure_le hn),
      fun hzero _ hv => Lean.Karger.eq_zero_of_mem_support_answerLaw hn hW hzero
        (Lean.Karger.mem_support_minRuns (Nat.one_le_iff_ne_zero.mp (highProbTrials_pos hn)) hv)⟩

end HighProb

end Cslib.Algorithms.WordRAM.Karger
