/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import CslibFrontier.Algorithms.WordRAM.NatLog
public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Karger.Graph
public import CslibFrontier.Algorithms.WordRAM.Karger.Contract
public import CslibFrontier.Algorithms.Karger.FastCut
public import CslibFrontier.Algorithms.WordRAM.Karger.OutputLaw
public import CslibFrontier.Computability.WordRAM.Copy
public import CslibFrontier.Computability.WordRAM.Randomized.LoopSegmentLaw
public import CslibFrontier.Algorithms.Lean.Karger.FastCut
public import CslibFrontier.Computability.WordRAM.Time
import CslibFrontier.Probability.PMF.Map

/-!
# Karger–Stein's recursive `FastCut` algorithm on the word RAM

Implements the Karger–Stein recursive randomized global minimum cut algorithm (`[KargerStein1996]`,
Section 4, Figure 6, Lemmas 4.1–4.3, and the minimum-cut-value part of Theorem 4.4; paraphrase) on
`n`-vertex weighted undirected
multigraphs (`n ≥ 2`, `IsMultigraph W`) over `Cslib.WordRAM.Basis.standard` using `r = 24`
registers and an explicit iterative frame stack in `O(n ^ 2)` scratch words (`≤ 26 * n ^ 2` stack
words plus `n ^ 2` input words, matching Section 4, Lemma 4.2), providing two machine-level
endpoints on `n :: flattenMatrix W`:

1. **Single-tree recursive contraction (`fastCutProgram`, `r = 24`, `[KargerStein1996]`, Section 4,
   Figure 6 and Lemmas 4.1–4.3; paraphrase):** contracts recursively from `k ≥ 7` down to the
   pure-integer threshold `t = fastCutThreshold k` (smallest `t ≥ 2` with `k * (k - 1) ≤ 2 * t *
   (t - 1)`, an integer deviation from Figure 6's `⌈k / √2 + 1⌉` that is never larger and is
   strictly smaller at e.g. `k = 8`, where `t = 6` vs `7`) along two independent branches, switches
   at `k ≤ 6` to a single contraction down to `2` supervertices (the source's base case: Figure 6's
   `Contract(G, 2)` with the size-7 cutoff of equation (2); a leaf keeps a fixed minimum cut with
   probability `≥ 2 / (k * (k - 1)) ≥ 1 / 15`, equation (2)'s base-case bound, which is where the
   `15` comes from), halts within `fastCutTime n = 2500 * n ^ 2 * (Nat.log 2 n + 2)`
   (`O(n ^ 2 log n)`) steps and `fastCutNodeQueries n ≤ 6 * n ^ 2` (`O(n ^ 2)`) `rand` calls with a
   genuine non-trivial cut weight `cutWeight W C ≥ minCut W` on every supported path, modifies only
   `[2 + n ^ 2, 2 + 27 * n ^ 2)`, and achieves `minCut W` with probability at least
   `1 / (Nat.log 2 n + 15)` whenever `0 < minCut W` (excluded only for proof convenience; when
   `minCut W = 0`, any non-trivial zero-weight cut is already optimal).
2. **Amplified high-probability global minimum cut (`fastCutHighProbProgram`, `r = 24`,
   `[KargerStein1996]`, Section 4, Theorem 4.4; paraphrase, the value part only: the source finds
   all minimum cuts in `O(m log(n ^ 2 / m))` space; we prove the returned value is `minCut W` except
   with probability `≤ 1 / (2 * n)`):** executes our concrete `O(log ^ 2 n)`
   trial schedule `fastCutTrials n = (Nat.log 2 n + 15) * (Nat.log 2 n + 2)` of independent
   `FastCut` trees reusing the same `[2 + n ^ 2, 2 + 27 * n ^ 2)` scratch arena, halts within
   `fastCutHighProbTime n = 2600 * n ^ 2 * (Nat.log 2 n + 15) * (Nat.log 2 n + 2) ^ 2`
   (`O(n ^ 2 log ^ 3 n)`) steps and `fastCutTrials n * (6 * n ^ 2)` `rand` calls with a genuine
   non-trivial cut weight `≥ minCut W`, and misses `minCut W` with probability at most
   `1 / (2 * n)` whenever `0 < minCut W` (and unconditionally at most `1 / n` in
   `fastCutHighProbProgram_failure_le_inv_n`, without `2 ≤ n` or `0 < minCut W`).

The probability argument is proved once for the oracle client
`Cslib.Algorithms.Lean.Karger.fastCut`. Native segments observe exactly that client's answer law
(`fastCutNode_law`, `fastCutTree_law`), and the outer loop observes the existing independent
`minRuns` client (`fastCutAmpLoop_law`, `fastCutHighProbCode_law`). Their certificates keep the
original supported-path instruction and random-call bounds and memory frames. They do not
replace those bounds with expected costs.

`baseCaseAndPop_spec`, `branchContractAndPush_spec`, `fastCutTree_spec` and
`fastCutAmpBody_spec` remain law-derived compatibility statements for the existing exact-basis
bridge. Its still-used `ChildMinCutSurvives` proposition and `KSAmpInv.best_cut` field are retained
for that bridge; the native recursive and amplification stages consume laws directly.

## Main definitions

* `Cslib.Algorithms.WordRAM.Karger.fastCutCode`,
  `Cslib.Algorithms.WordRAM.Karger.fastCutProgram`,
  `Cslib.Algorithms.WordRAM.Karger.fastCutTime`: single-tree `O(n ^ 2 log n)` Karger–Stein
  `FastCut` (`r = 24`).
* `Cslib.Algorithms.WordRAM.Karger.fastCutHighProbCode`,
  `Cslib.Algorithms.WordRAM.Karger.fastCutHighProbProgram`,
  `Cslib.Algorithms.WordRAM.Karger.fastCutHighProbTime`: amplified `O(n ^ 2 log ^ 3 n)`
  high-probability Karger–Stein (`r = 24`).

## Main results

* `Cslib.Algorithms.WordRAM.Karger.fastCutProgram_spec`: worst-case `O(n ^ 2 log n)` step bound,
  `O(n ^ 2)` `rand`-call bound, pathwise non-trivial cut realization, `Modifies` frame, and
  `1 / (Nat.log 2 n + 15)` success probability lower bound for `fastCutProgram`
  (`[KargerStein1996]`, Section 4, Figure 6 and Lemmas 4.1–4.3; paraphrase).
* `Cslib.Algorithms.WordRAM.Karger.fastCutHighProbProgram_spec`,
  `Cslib.Algorithms.WordRAM.Karger.fastCutHighProbProgram_failure_le_inv_n`: worst-case
  `O(n ^ 2 log ^ 3 n)` step bound, pathwise non-trivial cut realization, `Modifies` frame, and
  `1 / (2 * n)` (unconditional `1 / n`) failure probability upper bound for `fastCutHighProbProgram`
  (the minimum-cut-value part of `[KargerStein1996]`, Section 4, Theorem 4.4; paraphrase).

## References

* [D. R. Karger and C. Stein, *A New Approach to the Minimum Cut Problem*][KargerStein1996]
* [D. R. Karger, *Global Min-cuts in RNC, and Other Ramifications of a Simple Min-Cut
  Algorithm*][Karger1993]
* [M. Mitzenmacher and E. Upfal, *Probability and Computing*][MitzenmacherUpfal2017]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.Karger

open scoped ENNReal
open Cslib.WeightedCut
open Cslib.Probability.PMF
open Cslib.WordRAM
open Cslib.Algorithms.Karger

/-! ### Word-size sufficiency (`logWidth 4 n ≤ w`) and input layout -/

/-- `16 ≤ 24`, used to embed `computeDegreesAndTotal` and `contractDownTo` into `Data 24`. -/
private theorem hr24 : 16 ≤ 24 := by decide

/-- Under `2 ≤ n` and `logWidth 4 n ≤ w`, stack workspace end-addresses up to `2 + 27 * (n * n)` fit
in `w`-bit words. -/
private theorem fits_fastCutWorkspace_of_logWidth_four {n w : ℕ} (hn : 2 ≤ n)
    (hw : logWidth 4 n ≤ w) :
    Fits w (2 + 27 * (n * n)) := by
  by_cases hn5 : 5 ≤ n
  · refine (fits_of_lt_pow (k := 4) (n := n) ?_).mono hw
    obtain ⟨d, rfl⟩ : ∃ d, n = d + 5 := ⟨n - 5, by omega⟩
    have hpow : (d + 5 + 1) ^ 4 = (d + 6) ^ 2 * (d + 6) ^ 2 := by ring
    have h36 : 36 ≤ (d + 6) ^ 2 := by nlinarith
    rw [hpow]
    nlinarith
  · have hfit_lw : Fits (logWidth 4 n) (2 + 27 * (n * n)) := by
      interval_cases n <;> decide
    exact hfit_lw.mono hw

/-- Under `2 ≤ n` and `logWidth 4 n ≤ w`, `fastCutTrials n = (Nat.log 2 n + 15) * (Nat.log 2 n + 2)`
fits in `w`-bit words. -/
private theorem fits_fastCutTrials_of_logWidth_four {n w : ℕ} (hn : 2 ≤ n) (hw : logWidth 4 n ≤ w) :
    Fits w (fastCutTrials n) := by
  by_cases hn4 : 4 ≤ n
  · refine (fits_of_lt_pow (k := 4) (n := n) ?_).mono hw
    unfold fastCutTrials
    have hlog : Nat.log 2 n < n := Nat.log_lt_self 2 (by omega)
    have h15 : Nat.log 2 n + 15 ≤ n + 14 := by omega
    have h2 : Nat.log 2 n + 2 ≤ n + 1 := by omega
    have hmul : (Nat.log 2 n + 15) * (Nat.log 2 n + 2) ≤ (n + 14) * (n + 1) :=
      Nat.mul_le_mul h15 h2
    have hpow : (n + 14) * (n + 1) < (n + 1) ^ 4 := by
      obtain ⟨d, rfl⟩ : ∃ d, n = d + 4 := ⟨n - 4, by omega⟩
      have hp4 : (d + 4 + 1) ^ 4 = (d + 5) ^ 2 * (d + 5) ^ 2 := by ring
      have h25 : 25 ≤ (d + 5) ^ 2 := by nlinarith
      rw [hp4]
      nlinarith
    exact lt_of_le_of_lt hmul hpow
  · have hfit_lw : Fits (logWidth 4 n) (fastCutTrials n) := by
      interval_cases n <;> decide
    exact hfit_lw.mono hw

/-- `logWidth 4 n ≤ w` and `Fits w (totalDoubledWeight W)` suffice for
`InputFits w (n :: flattenMatrix W)`. -/
private theorem inputFits_fastCut {n w : ℕ} {W : Fin n → Fin n → ℕ} (hn : 2 ≤ n)
    (hw : logWidth 4 n ≤ w) (htot : Fits w (totalDoubledWeight W)) :
    InputFits w (n :: flattenMatrix W) :=
  inputFits_cons_flattenMatrix (fits_fastCutWorkspace_of_logWidth_four hn hw) (by omega)
    (by nlinarith) htot

/-! ### Register layout (`r = 24`) -/

-- Registers `0..15` match `Reg` (`Contract.lean`) via `Fin.castLE hr24`, while `16..23` hold the
-- immutable input descriptor, explicit iterative frame stack, and outer amplification state.
namespace KSReg

/-- Constant register `0` (`Reg.zero` embedded into `Fin 24`). -/
abbrev zero : Fin 24 := 0
/-- Constant register `1` (`Reg.one` embedded into `Fin 24`). -/
abbrev one : Fin 24 := 1
/-- Working matrix base address (`Reg.wBase` embedded into `Fin 24`). -/
abbrev wBase : Fin 24 := 2
/-- Working degree-array base address (`Reg.dBase` embedded into `Fin 24`). -/
abbrev dBase : Fin 24 := 3
/-- Working matrix row stride (`Reg.stride` embedded into `Fin 24`). -/
abbrev stride : Fin 24 := 4
/-- Active supervertex count `k` (`Reg.activeK` embedded into `Fin 24`). -/
abbrev activeK : Fin 24 := 5
/-- Target supervertex count `t` (`Reg.targetT` embedded into `Fin 24`). -/
abbrev targetT : Fin 24 := 6
/-- Active doubled edge weight `S` (`Reg.totS` embedded into `Fin 24`). -/
abbrev totS : Fin 24 := 7
/-- Row / auxiliary scratch register (`Reg.uReg` embedded into `Fin 24`). -/
abbrev uReg : Fin 24 := 8
/-- Column / auxiliary scratch register (`Reg.vReg` embedded into `Fin 24`). -/
abbrev vReg : Fin 24 := 9
/-- Loop index scratch register (`Reg.idx` embedded into `Fin 24`). -/
abbrev idx : Fin 24 := 10
/-- Loop length / remainder scratch register (`Reg.rem` embedded into `Fin 24`). -/
abbrev rem : Fin 24 := 11
/-- Primary scratch address register (`Reg.addr1` embedded into `Fin 24`). -/
abbrev addr1 : Fin 24 := 12
/-- Secondary scratch address register (`Reg.addr2` embedded into `Fin 24`). -/
abbrev addr2 : Fin 24 := 13
/-- Primary scratch value register (`Reg.val1` embedded into `Fin 24`). -/
abbrev val1 : Fin 24 := 14
/-- Secondary scratch value register (`Reg.val2` embedded into `Fin 24`). -/
abbrev val2 : Fin 24 := 15
/-- Base address (`2`) of the immutable input matrix `W`. -/
abbrev srcBase : Fin 24 := 16
/-- Root vertex count `n`, preserved across all trees. -/
abbrev nOrig : Fin 24 := 17
/-- Current stack frame base address `fp`. -/
abbrev fpReg : Fin 24 := 18
/-- Current active stack depth `sp` (`0` = empty). -/
abbrev spReg : Fin 24 := 19
/-- Cut weight returned by the most recently popped frame. -/
abbrev retVal : Fin 24 := 20
/-- Total number of `FastCut` trees to run in `fastCutHighProbCode`. -/
abbrev numTrials : Fin 24 := 21
/-- Number of `FastCut` trees completed so far. -/
abbrev trialIdx : Fin 24 := 22
/-- Minimum cut weight seen across completed `FastCut` trees. -/
abbrev bestVal : Fin 24 := 23

end KSReg

/-- Caller-register preservation (`j ≥ 16`) for any routine preserving registers `16..23`. -/
private theorem caller_regs_eq {w T : ℕ} {c : Code .standard 24} {x y : Data 24}
    (he : ExecWithin w c x y T)
    (hc : ∀ k : Fin 8, c.Preserves ⟨16 + k.val, by omega⟩) :
    ∀ j : Fin 24, 16 ≤ j.val → y.regs j = x.regs j := fun j hj => by
  have hj' : j = ⟨16 + (j.val - 16), by omega⟩ := Fin.ext (by dsimp; omega)
  exact hj' ▸ he.regs_eq (hc ⟨j.val - 16, by omega⟩)

section Subroutines

open KSReg

/-! ### Deterministic subroutines: block copy, integer threshold, and submatrix compaction -/

/-- Injective register map embedding `Cslib.WordRAM.ArrayCopy` (`r = 7`) into `Fin 24` with
`(src, dst, len, idx, addr, value, one) = (uReg, wBase, rem, idx, addr1, val1, one)`. -/
def ksCopyRegMap : Fin 7 → Fin 24 :=
  ![uReg, wBase, rem, idx, addr1, val1, one]

private theorem ksCopyRegMap_injective : Function.Injective ksCopyRegMap := by
  decide

/-- Copy `rem` words from `uReg` to `wBase` via `Cslib.WordRAM.ArrayCopy.program`. -/
def ksCopyCode : Code .standard 24 :=
  ArrayCopy.program.rename ksCopyRegMap

theorem holdsMatrix_of_copyPrefix {mem : ℕ → ℕ} {sb db k : ℕ} {W : Fin k → Fin k → ℕ}
    (hsrc : HoldsMatrix mem sb k W) :
    HoldsMatrix (ArrayCopy.copyPrefix mem sb db (k * k)) db k W := by
  intro i j
  have hlt : i.val * k + j.val < k * k := by nlinarith [i.isLt, j.isLt]
  have haddr_d : db + i.val * k + j.val = db + (i.val * k + j.val) := by omega
  have haddr_s : sb + (i.val * k + j.val) = sb + i.val * k + j.val := by omega
  rw [haddr_d, ArrayCopy.copyPrefix_read hlt, haddr_s]
  exact hsrc i j

private theorem ksCopyCode_exec {w sb db k : ℕ} {W : Fin k → Fin k → ℕ} {x : Data 24}
    (hsb : x.regs uReg = sb) (hdb : x.regs wBase = db) (hlen : x.regs rem = k * k)
    (hdisj : sb + k * k ≤ db) (h1 : Fits w 1) (hdEnd : Fits w (db + k * k))
    (hsrc : HoldsMatrix x.mem sb k W) :
    ∃ y : Data 24, ExecWithin w ksCopyCode x y (7 * (k * k) + 4) ∧
      HoldsMatrix y.mem db k W ∧
      Modifies (Finset.Ico db (db + k * k)) x.mem y.mem ∧
      y.regs zero = x.regs zero ∧
      y.regs wBase = db ∧
      y.regs dBase = x.regs dBase ∧
      y.regs stride = x.regs stride ∧
      y.regs activeK = x.regs activeK ∧
      y.regs targetT = x.regs targetT ∧
      (∀ j : Fin 24, 16 ≤ j.val → y.regs j = x.regs j) := by
  have hs_fit : Fits w ((x.comap ksCopyRegMap).regs ArrayCopy.src +
      (x.comap ksCopyRegMap).regs ArrayCopy.len) := by
    change Fits w (x.regs uReg + x.regs rem)
    simpa [hsb, hlen] using hdEnd.of_le (by omega)
  have hd_fit : Fits w ((x.comap ksCopyRegMap).regs ArrayCopy.dst +
      (x.comap ksCopyRegMap).regs ArrayCopy.len) := by
    change Fits w (x.regs wBase + x.regs rem)
    simpa [hdb, hlen] using hdEnd
  have hdisj' : (x.comap ksCopyRegMap).regs ArrayCopy.src +
      (x.comap ksCopyRegMap).regs ArrayCopy.len ≤ (x.comap ksCopyRegMap).regs ArrayCopy.dst := by
    change x.regs uReg + x.regs rem ≤ x.regs wBase
    simpa [hsb, hlen, hdb] using hdisj
  obtain ⟨y, hy_exec, ⟨hy_mem, _, hy_dst, _⟩, _⟩ :=
    ExecWithin.rename_post ksCopyRegMap_injective
      (ArrayCopy.exec (x.comap ksCopyRegMap) h1 hs_fit hd_fit hdisj')
  simp only [Data.comap_regs, Data.comap_mem,
    show ksCopyRegMap ArrayCopy.src = uReg from rfl,
    show ksCopyRegMap ArrayCopy.dst = wBase from rfl,
    show ksCopyRegMap ArrayCopy.len = rem from rfl,
    hsb, hdb, hlen] at hy_exec hy_mem hy_dst
  exact ⟨y, hy_exec, hy_mem ▸ holdsMatrix_of_copyPrefix hsrc,
    fun a ha => hy_mem ▸ ArrayCopy.copyPrefix_outside (by rwa [Finset.mem_Ico] at ha),
    hy_exec.regs_eq (by decide), hy_dst, hy_exec.regs_eq (by decide),
    hy_exec.regs_eq (by decide), hy_exec.regs_eq (by decide), hy_exec.regs_eq (by decide),
    caller_regs_eq hy_exec (by decide)⟩

/-- Loop body of `thresholdCode`: advance `t` to `t + 1` while maintaining `uReg = t`
(`= (t + 1) - 1`) and `val1 = 2 * (t + 1) * t` without subtraction. -/
def thresholdLoopBody : Code .standard 24 := ram[
  uReg ← targetT;
  targetT ← targetT + one;
  val1 ← val2 * targetT;
  val1 ← val1 * uReg
]

/-- Preamble of `thresholdCode`: initialize `rem = k * (k - 1)` and `(targetT, uReg, val2, val1) =
(2, 1, 2, 4)`. -/
def thresholdPre : Code .standard 24 := ram[
  one ← #1;
  rem ← activeK - one;
  rem ← activeK * rem;
  targetT ← #2;
  uReg ← #1;
  val2 ← #2;
  val1 ← #4
]

/-- Compute `targetT = fastCutThreshold k` in `O(k)` instructions for `k = x.regs activeK ≥ 7`. -/
def thresholdCode : Code .standard 24 := ram[
  ⟪thresholdPre⟫;
  while val1 < rem do [ ⟪thresholdLoopBody⟫ ]
]

private theorem thresholdCode_exec {w k : ℕ} {x : Data 24} (hk : 7 ≤ k)
    (hactiveK : x.regs activeK = k) (hfit : Fits w (2 * k * (k - 1))) :
    ∃ y : Data 24, ExecWithin w thresholdCode x y (6 * k + 9) ∧
      y.mem = x.mem ∧
      y.regs one = 1 ∧
      y.regs activeK = k ∧
      y.regs targetT = fastCutThreshold k ∧
      y.regs wBase = x.regs wBase ∧
      y.regs dBase = x.regs dBase ∧
      y.regs stride = x.regs stride ∧
      (∀ j : Fin 24, 16 ≤ j.val → y.regs j = x.regs j) := by
  have hk84 : 84 ≤ 2 * k * (k - 1) := by
    obtain ⟨c, rfl⟩ : ∃ c, k = c + 7 := ⟨k - 7, by omega⟩
    have : c + 7 - 1 = c + 6 := by omega
    rw [this]; nlinarith
  let t_star := fastCutThreshold k
  have ht_ge2 : 2 ≤ t_star := fastCutThreshold_ge_two (by omega)
  have ht_le_pred : t_star ≤ k - 1 := fastCutThreshold_le_pred (by omega)
  have ht_spec : k * (k - 1) ≤ 2 * t_star * (t_star - 1) := fastCutThreshold_spec (by omega)
  let I (y : Data 24) : Prop :=
    y.mem = x.mem ∧
    y.regs one = 1 ∧
    y.regs activeK = k ∧
    y.regs rem = k * (k - 1) ∧
    y.regs val2 = 2 ∧
    2 ≤ y.regs targetT ∧
    y.regs targetT ≤ t_star ∧
    y.regs uReg = y.regs targetT - 1 ∧
    y.regs val1 = 2 * y.regs targetT * (y.regs targetT - 1)
  have hbody : ∀ y, I y → (Cond.lt val1 rem).Holds y →
      ∃ z, ExecWithin w thresholdLoopBody y z 4 ∧ I z ∧
        t_star - z.regs targetT < t_star - y.regs targetT := by
    intro y ⟨hym, hy1, hyk, hyrem, hyv2, hyt_ge, hyt_le, _, hyv1⟩ hc
    have hlt_prod : 2 * y.regs targetT * (y.regs targetT - 1) < k * (k - 1) := by
      simpa [Cond.holds_lt, hyv1, hyrem] using hc
    have ht_lt_star : y.regs targetT < t_star := by
      by_contra hge
      exact absurd ht_spec (not_le_of_gt
        (by rwa [show y.regs targetT = t_star by omega] at hlt_prod))
    have hfit_tp1 : Fits w (y.regs targetT + 1) := hfit.of_le (by nlinarith)
    have hfit_2tp1 : Fits w (2 * (y.regs targetT + 1)) := hfit.of_le (by nlinarith)
    have hfit_prod : Fits w (2 * (y.regs targetT + 1) * y.regs targetT) := hfit.of_le (by
      have := Nat.mul_le_mul (by omega : y.regs targetT + 1 ≤ k) (by omega : y.regs targetT ≤ k - 1)
      nlinarith)
    unfold thresholdLoopBody
    wram_exec [hy1, hyv2]
    exact ⟨⟨hym, by wram_simp [hy1], by wram_simp [hyk], by wram_simp [hyrem],
      by wram_simp [hyv2], by wram_simp; omega, by wram_simp; exact ht_lt_star,
      by wram_simp, by wram_simp⟩, by wram_simp; omega⟩
  obtain ⟨x₀, hex_pre, hx₀, hx₀_t⟩ : ∃ x₀, ExecWithin w thresholdPre x x₀ 7 ∧
      I x₀ ∧ x₀.regs targetT = 2 := by
    have : Fits w 4 := hfit.of_le (by omega)
    have : Fits w (k - 1) := hfit.of_le (by nlinarith)
    have : Fits w (k * (k - 1)) := hfit.of_le (by nlinarith)
    unfold thresholdPre
    wram_exec [hactiveK]
    exact ⟨⟨rfl, by wram_simp, by wram_simp [hactiveK], by wram_simp, by wram_simp,
      by wram_simp, by wram_simp; exact ht_ge2, by wram_simp, by wram_simp⟩, by wram_simp⟩
  obtain ⟨y, hex_loop, hy, hc_exit⟩ :=
    ExecWithin.loop_invariant I (fun z => t_star - z.regs targetT) hbody hx₀
  rcases hy with ⟨hym, hy1, hyk, hyrem, _, hyt_ge, hyt_le, _, hyv1⟩
  have hyt_eq : y.regs targetT = t_star := by
    apply le_antisymm hyt_le
    by_contra hlt'
    have hmin := fastCutThreshold_lt_of_lt (by omega : 4 ≤ k) hyt_ge (Nat.lt_of_not_ge hlt')
    simp only [Cond.holds_lt, hyv1, hyrem, not_lt] at hc_exit
    omega
  have htot_exec : ExecWithin w thresholdCode x y (6 * k + 9) :=
    (hex_pre.seq hex_loop).mono (by rw [hx₀_t]; omega)
  exact ⟨y, htot_exec, hym, hy1, hyk, hyt_eq,
    htot_exec.regs_eq (by decide), htot_exec.regs_eq (by decide), htot_exec.regs_eq (by decide),
    caller_regs_eq htot_exec (by decide)⟩

/-- Inner column loop body of `copySubmatrixCode`: copy `mem[idx + vReg]` to `mem[rem + vReg]`. -/
def copySubColBody : Code .standard 24 := ram[
  addr1 ← idx + vReg;
  val1 ← *addr1;
  addr1 ← rem + vReg;
  *addr1 ← val1;
  vReg ← vReg + one
]

/-- Row-pointer advance at the end of `copySubRowBody`. -/
def copySubRowPost : Code .standard 24 := ram[
  idx ← idx + stride;
  rem ← rem + targetT;
  uReg ← uReg + one
]

/-- Outer row loop body of `copySubmatrixCode`: copy row `uReg` of length `targetT` and advance row
pointers `idx` by `stride` and `rem` by `targetT`. -/
def copySubRowBody : Code .standard 24 := ram[
  vReg ← #0;
  while vReg < targetT do [ ⟪copySubColBody⟫ ];
  ⟪copySubRowPost⟫
]

/-- Preamble of `copySubmatrixCode`. -/
def copySubPre : Code .standard 24 := ram[
  idx ← wBase;
  rem ← addr2;
  uReg ← #0
]

/-- Copy the active `t × t` submatrix at `wBase` (stride `stride`) densely into `addr2` (stride `t`)
without `.sub`, `.div`, or `.mod`. -/
def copySubmatrixCode : Code .standard 24 := ram[
  ⟪copySubPre⟫;
  while uReg < targetT do [ ⟪copySubRowBody⟫ ]
]

private theorem copySubmatrixCode_exec {w wb str dstBase t : ℕ} {W : Fin t → Fin t → ℕ}
    {x : Data 24}
    (hwBase : x.regs wBase = wb) (hstride : x.regs stride = str)
    (htargetT : x.regs targetT = t) (hdst : x.regs addr2 = dstBase) (hone : x.regs one = 1)
    (hstr : t ≤ str) (hdisj : wb + str * t ≤ dstBase)
    (hwEnd : Fits w (wb + str * t)) (hdstEnd : Fits w (dstBase + t * t))
    (hmat : HoldsMatrix x.mem wb str W) :
    ∃ y : Data 24, ExecWithin w copySubmatrixCode x y (7 * t ^ 2 + 8 * t + 5) ∧
      HoldsMatrix y.mem dstBase t W ∧
      Modifies (Finset.Ico dstBase (dstBase + t * t)) x.mem y.mem ∧
      y.regs one = 1 ∧
      y.regs wBase = wb ∧
      y.regs dBase = x.regs dBase ∧
      y.regs stride = str ∧
      y.regs activeK = x.regs activeK ∧
      y.regs targetT = t ∧
      y.regs addr2 = dstBase ∧
      (∀ j : Fin 24, 16 ≤ j.val → y.regs j = x.regs j) := by
  let Frame (q : Data 24) : Prop :=
    q.regs one = 1 ∧ q.regs wBase = wb ∧ q.regs stride = str ∧
      q.regs targetT = t ∧ q.regs addr2 = dstBase
  let OuterI (y : Data 24) : Prop :=
    Frame y ∧
    y.regs uReg ≤ t ∧
    y.regs idx = wb + y.regs uReg * str ∧
    y.regs rem = dstBase + y.regs uReg * t ∧
    Modifies (Finset.Ico dstBase (dstBase + t * t)) x.mem y.mem ∧
    ∀ i j : Fin t, i.val < y.regs uReg → y.mem (dstBase + i.val * t + j.val) = W i j
  have houter_body : ∀ y, OuterI y → (Cond.lt uReg targetT).Holds y →
      ∃ z, ExecWithin w copySubRowBody y z (7 * t + 6) ∧ OuterI z ∧
        t - z.regs uReg < t - y.regs uReg := by
    intro y ⟨hyf, hyu_le, hyidx, hyrem, hymod, hydone⟩ hc
    have hu_lt : y.regs uReg < t := by simpa [Cond.holds_lt, hyf.2.2.2.1] using hc
    let u : Fin t := ⟨y.regs uReg, hu_lt⟩
    let InnerI (q : Data 24) : Prop :=
      Frame q ∧
      q.regs uReg = u.val ∧
      q.regs idx = wb + u.val * str ∧
      q.regs rem = dstBase + u.val * t ∧
      q.regs vReg ≤ t ∧
      Modifies (Finset.Ico dstBase (dstBase + t * t)) x.mem q.mem ∧
      ∀ i j : Fin t, (i.val < u.val ∨ (i = u ∧ j.val < q.regs vReg)) →
        q.mem (dstBase + i.val * t + j.val) = W i j
    have hcol_body : ∀ q, InnerI q → (Cond.lt vReg targetT).Holds q →
        ∃ q', ExecWithin w copySubColBody q q' 5 ∧ InnerI q' ∧
          t - q'.regs vReg < t - q.regs vReg := by
      intro q ⟨hqf, hqu, hqidx, hqrem, hqv_le, hqmod, hqdone⟩ hcv
      have hv_lt : q.regs vReg < t := by simpa [Cond.holds_lt, hqf.2.2.2.1] using hcv
      let v : Fin t := ⟨q.regs vReg, hv_lt⟩
      have hsrc_lt : wb + u.val * str + v.val < wb + str * t := matAddr_lt_end hstr u v
      have hdst_lt : dstBase + u.val * t + v.val < dstBase + t * t :=
        matAddr_lt_end (le_refl t) u v
      have : Fits w (wb + u.val * str + v.val) := hwEnd.of_le (by omega)
      have : Fits w (dstBase + u.val * t + v.val) := hdstEnd.of_le (by omega)
      have : Fits w (v.val + 1) := hdstEnd.of_le (by have := Nat.le_mul_self t; omega)
      have hread_src : q.mem (wb + u.val * str + v.val) = W u v := by
        rw [hqmod _ (by rw [Finset.mem_Ico]; omega)]
        exact hmat u v
      have hv_eq : q.regs vReg = v.val := rfl
      unfold copySubColBody
      wram_exec [hqf.1, hqidx, hqrem, hv_eq, hread_src]
      refine ⟨⟨⟨by wram_simp [hqf.1], by wram_simp [hqf.2.1], by wram_simp [hqf.2.2.1],
        by wram_simp [hqf.2.2.2.1], by wram_simp [hqf.2.2.2.2]⟩,
        by wram_simp [hqu], by wram_simp [hqidx], by wram_simp [hqrem],
        by wram_simp; exact hv_lt,
        modifies_trans_subset hqmod
          (modifies_update_of_mem (matAddr_mem_Ico (le_refl t) u v) q.mem _)
          Finset.Subset.rfl Finset.Subset.rfl,
        fun i j hij => ?_⟩, by wram_simp [hv_eq]; omega⟩
      simp only [Data.set_regs_self] at hij
      change Function.update q.mem (dstBase + u.val * t + v.val) (W u v) _ = W i j
      by_cases huv : i = u ∧ j = v
      · rcases huv with ⟨rfl, rfl⟩
        exact Function.update_self _ _ _
      · rw [Function.update_of_ne (fun heq => huv (matAddr_inj (le_refl t) heq))]
        apply hqdone i j
        rcases hij with hlt_u | ⟨rfl, hlt_vp1⟩
        · exact Or.inl hlt_u
        · exact Or.inr ⟨rfl, Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hlt_vp1)
            fun h => huv ⟨rfl, Fin.ext h⟩⟩
    let q₀ := y.set vReg 0
    have hq₀_exec : ExecWithin (B := .standard) w ram[vReg ← #0] y q₀ 1 :=
      ExecWithin.const (fits_zero w)
    have hq₀_inv : InnerI q₀ :=
      ⟨⟨by wram_simp [q₀, hyf.1], by wram_simp [q₀, hyf.2.1], by wram_simp [q₀, hyf.2.2.1],
        by wram_simp [q₀, hyf.2.2.2.1], by wram_simp [q₀, hyf.2.2.2.2]⟩,
        by wram_simp [q₀, u], by wram_simp [q₀, u, hyidx], by wram_simp [q₀, u, hyrem],
        by wram_simp [q₀]; omega, hymod,
        fun i j hij => by
          rcases hij with hlt_u | ⟨_, hlt0⟩
          · exact hydone i j hlt_u
          · simp [q₀] at hlt0⟩
    obtain ⟨q₁, hex_inner, ⟨hqf, hqu, hqidx, hqrem, hqv_le, hqmod, hqdone⟩, hc_inner_exit⟩ :=
      ExecWithin.loop_invariant InnerI (fun q => t - q.regs vReg) hcol_body hq₀_inv
    have hqv_eq : q₁.regs vReg = t := by
      simp only [Cond.holds_lt, hqf.2.2.2.1, not_lt] at hc_inner_exit
      omega
    obtain ⟨z, hex_post, hz_inv, hz_dec⟩ : ∃ z, ExecWithin w copySubRowPost q₁ z 3 ∧
        OuterI z ∧ t - z.regs uReg < t - y.regs uReg := by
      have : Fits w (wb + u.val * str + str) := hwEnd.of_le (by
        have : u.val * str + str ≤ str * t := by
          calc u.val * str + str = (u.val + 1) * str := by ring
            _ ≤ t * str := Nat.mul_le_mul_right str u.isLt
            _ = str * t := Nat.mul_comm t str
        omega)
      have : Fits w (dstBase + u.val * t + t) := hdstEnd.of_le (by
        have : u.val * t + t ≤ t * t := by
          calc u.val * t + t = (u.val + 1) * t := by ring
            _ ≤ t * t := Nat.mul_le_mul_right t u.isLt
        omega)
      have : Fits w (u.val + 1) := hdstEnd.of_le (by
        have := Nat.le_mul_self t; have := u.isLt; omega)
      unfold copySubRowPost
      wram_exec [hqf.1, hqf.2.2.1, hqf.2.2.2.1, hqidx, hqrem, hqu]
      refine ⟨⟨⟨by wram_simp [hqf.1], by wram_simp [hqf.2.1], by wram_simp [hqf.2.2.1],
        by wram_simp [hqf.2.2.2.1], by wram_simp [hqf.2.2.2.2]⟩,
        by wram_simp; exact u.isLt, by wram_simp; ring, by wram_simp; ring, hqmod,
        fun i j hij => ?_⟩, by wram_simp; exact Nat.sub_lt_sub_left hu_lt (Nat.lt_succ_self _)⟩
      simp only [Data.set_regs_self] at hij
      rcases Nat.lt_succ_iff_lt_or_eq.mp hij with hlt_u | heq_u
      · exact hqdone i j (Or.inl hlt_u)
      · exact hqdone i j (Or.inr ⟨Fin.ext heq_u, hqv_eq ▸ j.isLt⟩)
    exact ⟨z, (hq₀_exec.seq (hex_inner.seq hex_post)).mono (by wram_simp [q₀]; omega), hz_inv,
      hz_dec⟩
  obtain ⟨x₀, hx₀_exec, hx₀_inv, hu0⟩ : ∃ x₀, ExecWithin w copySubPre x x₀ 3 ∧
      OuterI x₀ ∧ x₀.regs uReg = 0 := by
    unfold copySubPre
    wram_exec [hwBase, hdst]
    exact ⟨⟨⟨by wram_simp [hone], by wram_simp [hwBase], by wram_simp [hstride],
      by wram_simp [htargetT], by wram_simp [hdst]⟩,
      by wram_simp; omega, by wram_simp; omega, by wram_simp; omega, Modifies.refl _ _,
      fun _ _ hij => by simp at hij⟩, by wram_simp⟩
  obtain ⟨y, hex_outer, ⟨hyf, hyu_le, _, _, hymod, hydone⟩, hc_outer_exit⟩ :=
    ExecWithin.loop_invariant OuterI (fun z => t - z.regs uReg) houter_body hx₀_inv
  have hyu_eq : y.regs uReg = t := by
    simp only [Cond.holds_lt, hyf.2.2.2.1, not_lt] at hc_outer_exit
    omega
  have htot_exec : ExecWithin w copySubmatrixCode x y (7 * t ^ 2 + 8 * t + 5) :=
    (hx₀_exec.seq hex_outer).mono (by rw [hu0, Nat.sub_zero]; exact le_of_eq (by ring))
  exact ⟨y, htot_exec, fun i j => hydone i j (hyu_eq ▸ i.isLt), hymod,
    hyf.1, hyf.2.1, htot_exec.regs_eq (by decide), hyf.2.2.1,
    htot_exec.regs_eq (by decide), hyf.2.2.2.1, hyf.2.2.2.2,
    caller_regs_eq htot_exec (by decide)⟩

/-- Contracting a multigraph never increases `totalDoubledWeight`. -/
theorem totalDoubledWeight_le_of_isContractionOf {n k : ℕ} {W₀ : Fin n → Fin n → ℕ}
    {part : Fin n → Fin k} {W : Fin k → Fin k → ℕ} (hC : IsContractionOf W₀ part W) :
    totalDoubledWeight W ≤ totalDoubledWeight W₀ := by
  unfold totalDoubledWeight
  calc
    ∑ a : Fin k, rowDeg W a
      = ∑ a : Fin k, cutWeight W₀ (pullbackCut part {a}) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [← cutWeight_singleton hC.multigraph a, cutWeight_pullbackCut hC]
    _ ≤ ∑ a : Fin k, ∑ x ∈ pullbackCut part {a}, rowDeg W₀ x :=
          Finset.sum_le_sum fun a _ => cutWeight_le_sum_rowDeg W₀ _
    _ = ∑ x : Fin n, rowDeg W₀ x := by
          rw [← Finset.sum_biUnion]
          · refine Finset.sum_congr ?_ fun _ _ => rfl
            ext x
            simp [pullbackCut]
          · intro a _ b _ hab
            simp only [Finset.disjoint_left, mem_pullbackCut, Finset.mem_singleton]
            rintro x rfl hxb
            exact hab hxb

end Subroutines

/-! ### Explicit iterative call-stack machine for `FastCut` (`r = 24`)

Each active frame at base address `fp` for a `k`-supervertex subproblem (`frameSize k =
4 + 2 * (k * k) + k`) lays out its immutable data first and its mutable workspace second:
* `mem[fp + 0] = parentFp` (immutable during this frame),
* `mem[fp + 1] = k` (immutable during this frame),
* `[fp + 2, fp + 2 + k * k)`: immutable `k × k` matrix `W_k` (stride `k`),
* `mem[fp + 2 + k * k] = stage` (`0`, `1`, or `2`),
* `mem[fp + 3 + k * k] = savedVal1` (Branch 1's returned cut weight),
* `[fp + 4 + k * k, fp + 4 + 2 * (k * k))`: working `k × k` contraction matrix (`wBase`),
* `[fp + 4 + 2 * (k * k), fp + frameSize k)`: working `k`-word degree buffer (`dBase`),
* `childFp = fp + frameSize k`: child frame pushed by Stages `0` and `1`.

Consequently, executing a frame at `fp` (including all of its recursive descendants) modifies only
`Finset.Ico (fp + 2 + k * k) (fp + fastCutScratch k)`, leaving `parentFp`, `k`, `W_k`, and every
ancestor frame below `fp` untouched. -/

section FrameMachine

open KSReg

/-- Frame-dispatch header: load `activeK = k = mem[fp + 1]`, compute `rem = k * k`,
`addr1 = fp + 2`, and `addr2 = fp + 2 + k * k`, load `val2 = stage = mem[addr2]`, and set
`val1 = 7`. -/
def stepHeader : Code .standard 24 := ram[
  zero ← #0;
  one ← #1;
  addr1 ← fpReg + one;
  activeK ← *addr1;
  rem ← activeK * activeK;
  addr1 ← addr1 + one;
  addr2 ← addr1 + rem;
  val2 ← *addr2;
  val1 ← #7
]

/-- Base-case workspace pointer setup (`2 ≤ k ≤ 6`): set `uReg = fp + 2`, `wBase = fp + 4 + k * k`,
`dBase = wBase + k * k`, `stride = k`, and `targetT = 2`. -/
def basePre : Code .standard 24 := ram[
  uReg ← addr1;
  val1 ← #2;
  wBase ← addr2 + val1;
  dBase ← wBase + rem;
  stride ← activeK;
  targetT ← #2
]

/-- Base-case epilogue: read `retVal = mem[wBase + 1]` and pop the frame (`fpReg ← mem[fpReg]`,
`spReg ← spReg - 1`). -/
def basePost : Code .standard 24 := ram[
  zero ← #0;
  one ← #1;
  addr1 ← wBase + one;
  retVal ← *addr1;
  fpReg ← *fpReg;
  spReg ← spReg - one
]

/-- Base-case execution (`2 ≤ k ≤ 6`): copy `W_k` to `wBase`, compute degrees, contract once down to
`2` supervertices, read `W'[0, 1]`, and pop the frame. -/
def baseCaseAndPop : Code .standard 24 := ram[
  ⟪basePre⟫;
  ⟪ksCopyCode⟫;
  ⟪computeDegreesAndTotalAt (by decide)⟫;
  ⟪contractDownToAt (by decide)⟫;
  ⟪basePost⟫
]

/-- Stage `0` update (`7 ≤ k`): set `mem[fp + 2 + k * k] ← 1` before contracting Branch 1. -/
def stageZeroSet : Code .standard 24 := ram[
  *addr2 ← one
]

/-- Stage `1` update (`7 ≤ k`): set `mem[fp + 2 + k * k] ← 2` and save `retVal` into
`mem[fp + 3 + k * k]` before contracting Branch 2. -/
def stageOneSaveAndSet : Code .standard 24 := ram[
  val1 ← #2;
  *addr2 ← val1;
  addr1 ← addr2 + one;
  *addr1 ← retVal
]

/-- Workspace setup for `branchContractAndPush` (`7 ≤ k`). -/
def branchSetup : Code .standard 24 := ram[
  val1 ← #2;
  uReg ← fpReg + val1;
  rem ← activeK * activeK;
  val1 ← #4;
  wBase ← fpReg + val1;
  wBase ← wBase + rem;
  dBase ← wBase + rem;
  stride ← activeK
]

/-- Destination setup before compacting the contracted `t × t` submatrix into `childFp + 2`. -/
def branchCompactPre : Code .standard 24 := ram[
  one ← #1;
  val2 ← dBase + stride;
  val1 ← #2;
  addr2 ← val2 + val1
]

/-- Initialize the child frame header at `childFp = dBase + stride` (`parentFp = fp`, `k_child = t`,
`stage_child = 0`) and push `(fpReg, spReg) ← (childFp, spReg + 1)`. -/
def branchPushChild : Code .standard 24 := ram[
  zero ← #0;
  one ← #1;
  addr1 ← dBase + stride;
  *addr1 ← fpReg;
  addr2 ← addr1 + one;
  *addr2 ← targetT;
  rem ← targetT * targetT;
  addr2 ← addr2 + one;
  addr2 ← addr2 + rem;
  *addr2 ← zero;
  fpReg ← addr1;
  spReg ← spReg + one
]

/-- Deterministic tail of `branchContractAndPush`: compact the `t × t` contracted submatrix into
`childFp + 2` and push the child frame header at `childFp`. -/
def branchTail : Code .standard 24 := ram[
  ⟪branchCompactPre⟫;
  ⟪copySubmatrixCode⟫;
  ⟪branchPushChild⟫
]

/-- Shared Branch 1 / Branch 2 contraction-and-push body (`7 ≤ k`): compute
`t = fastCutThreshold k`, copy `W_k` to `wBase`, compute degrees, contract down to `t`, compact the
`t × t` submatrix into `childFp + 2`, and push the child frame at `childFp = fp + frameSize k`. -/
def branchContractAndPush : Code .standard 24 := ram[
  ⟪thresholdCode⟫;
  ⟪branchSetup⟫;
  ⟪ksCopyCode⟫;
  ⟪computeDegreesAndTotalAt (by decide)⟫;
  ⟪contractDownToAt (by decide)⟫;
  ⟪branchTail⟫
]

/-- Stage `2` epilogue (`7 ≤ k`): set `retVal ← min savedVal1 retVal` and pop the frame. -/
def combineAndPop : Code .standard 24 := ram[
  addr1 ← addr2 + one;
  val1 ← *addr1;
  if val1 < retVal then [
    retVal ← val1
  ] else [
    zero ← #0
  ];
  fpReg ← *fpReg;
  spReg ← spReg - one
]

/-- Single iteration body of the explicit-stack `FastCut` loop. -/
def fastCutStep : Code .standard 24 := ram[
  ⟪stepHeader⟫;
  if activeK < val1 then [
    ⟪baseCaseAndPop⟫
  ] else [
    if val2 = zero then [
      ⟪stageZeroSet⟫;
      ⟪branchContractAndPush⟫
    ] else [
      if val2 = one then [
        ⟪stageOneSaveAndSet⟫;
        ⟪branchContractAndPush⟫
      ] else [
        ⟪combineAndPop⟫
      ]
    ]
  ]
]

/-- Outer explicit-stack `while` loop executing all active frames down to `spReg = 0`. -/
def fastCutLoop : Code .standard 24 := ram[
  while zero < spReg do [ ⟪fastCutStep⟫ ]
]

private theorem stepHeader_exec {w fp k stg : ℕ} {x : Data 24} (hk2 : 2 ≤ k)
    (hfp : x.regs fpReg = fp) (hmem_k : x.mem (fp + 1) = k)
    (hmem_stg : x.mem (fp + 2 + k * k) = stg)
    (hfit : Fits w (fp + frameSize k)) :
    ∃ y : Data 24, Exec w stepHeader x y 9 ∧
      y.mem = x.mem ∧
      y.regs zero = 0 ∧
      y.regs one = 1 ∧
      y.regs activeK = k ∧
      y.regs rem = k * k ∧
      y.regs addr1 = fp + 2 ∧
      y.regs addr2 = fp + 2 + k * k ∧
      y.regs val2 = stg ∧
      y.regs val1 = 7 ∧
      (∀ j : Fin 24, 16 ≤ j.val → y.regs j = x.regs j) := by
  have hfs : fp + (4 + 2 * (k * k) + k) = fp + frameSize k := rfl
  have hkk : 4 ≤ k * k := Nat.mul_le_mul hk2 hk2
  have : Fits w 7 := hfit.of_le (by omega)
  have : Fits w (k * k) := hfit.of_le (by omega)
  have : Fits w (fp + 2) := hfit.of_le (by omega)
  have : Fits w (fp + 2 + k * k) := hfit.of_le (by omega)
  obtain ⟨y, hex, hpost⟩ : ∃ y, Exec w stepHeader x y 9 ∧
      (y.mem = x.mem ∧ y.regs zero = 0 ∧ y.regs one = 1 ∧ y.regs activeK = k ∧
        y.regs rem = k * k ∧ y.regs addr1 = fp + 2 ∧ y.regs addr2 = fp + 2 + k * k ∧
        y.regs val2 = stg ∧ y.regs val1 = 7) := by
    unfold stepHeader
    wram_exec [hfp, hmem_k, show (fp + 1) + 1 = fp + 2 from rfl, hmem_stg]
    exact ⟨rfl, by wram_simp⟩
  exact ⟨y, hex, hpost.1, hpost.2.1, hpost.2.2.1, hpost.2.2.2.1, hpost.2.2.2.2.1,
    hpost.2.2.2.2.2.1, hpost.2.2.2.2.2.2.1, hpost.2.2.2.2.2.2.2.1,
    hpost.2.2.2.2.2.2.2.2, caller_regs_eq hex.within (by decide)⟩

private theorem combineAndPop_exec {w fp parentFp b k v1 r2 : ℕ} {x : Data 24}
    (hk2 : 2 ≤ k) (h0 : x.regs zero = 0) (h1 : x.regs one = 1)
    (ha2 : x.regs addr2 = fp + 2 + k * k)
    (hfp : x.regs fpReg = fp) (hsp : x.regs spReg = b + 1) (hr2 : x.regs retVal = r2)
    (hmem_p : x.mem fp = parentFp) (hmem_v1 : x.mem (fp + 3 + k * k) = v1)
    (hfit : Fits w (fp + frameSize k)) (hsp_fit : Fits w b) :
    ∃ y : Data 24, ExecWithin w combineAndPop x y 7 ∧
      y.mem = x.mem ∧
      y.regs zero = 0 ∧
      y.regs fpReg = parentFp ∧
      y.regs spReg = b ∧
      y.regs retVal = min v1 r2 := by
  have : Fits w (fp + 3 + k * k) := hfit.of_le (by
    unfold frameSize; have := Nat.mul_le_mul hk2 hk2; omega)
  unfold combineAndPop
  wram_exec [h0, h1, ha2, hfp, hsp, hr2,
    show (fp + 2 + k * k) + 1 = fp + 3 + k * k by omega, hmem_p, hmem_v1]
  · exact ⟨rfl, by wram_simp [h0], by wram_simp, by wram_simp,
      by wram_simp; exact (Nat.min_eq_left hc.le).symm⟩
  · exact ⟨rfl, by wram_simp, by wram_simp, by wram_simp,
      by wram_simp [hr2]; exact (Nat.min_eq_right (Nat.le_of_not_lt hc)).symm⟩

/-- The graph held by a recursive frame at its explicit invariant size. This is a view of the
existing native memory layout, with no additional graph representation. -/
private def frameGraph (fp k : ℕ) (x : Data 24) : Lean.Karger.Graph :=
  ⟨k, fun i j => x.mem (fp + 2 + i.val * k + j.val)⟩

/-- The frame observation equals a typed graph exactly when its existing matrix invariant holds. -/
private theorem frameGraph_eq_iff {fp k : ℕ} {x : Data 24} {W : Fin k → Fin k → ℕ} :
    frameGraph fp k x = ⟨k, W⟩ ↔ HoldsMatrix x.mem (fp + 2) k W := by
  simp only [frameGraph, Lean.Karger.Graph.mk.injEq, heq_eq_eq, true_and]
  exact ⟨fun h i j => congrFun (congrFun h i) j, fun h => funext₂ h⟩

/-- The base-case output has exactly the existing contraction-trial answer law. -/
private theorem baseCaseAndPop_law {n w fp parentFp b k : ℕ} {W₀ : Fin n → Fin n → ℕ}
    {W_k : Fin k → Fin k → ℕ} {part : Fin n → Fin k} {x : Data 24}
    (hk2 : 2 ≤ k) (hk6 : k ≤ 6)
    (hk_reg : x.regs activeK = k) (hrem_reg : x.regs rem = k * k)
    (ha1_reg : x.regs addr1 = fp + 2) (ha2_reg : x.regs addr2 = fp + 2 + k * k)
    (hfp : x.regs fpReg = fp) (hsp : x.regs spReg = b + 1)
    (hmem_p : x.mem fp = parentFp) (hmat : HoldsMatrix x.mem (fp + 2) k W_k)
    (hC : IsContractionOf W₀ part W_k)
    (hfit : Fits w (fp + frameSize k)) (hsp_fit : Fits w b)
    (htot : Fits w (totalDoubledWeight W₀)) :
    ExecRandLaw w baseCaseAndPop x
      (fun y => Modifies (Finset.Ico (fp + 2 + k * k) (fp + frameSize k)) x.mem y.mem ∧
        y.regs zero = 0 ∧ y.regs fpReg = parentFp ∧ y.regs spReg = b)
      2000 (k - 2) (fun y => y.regs retVal) (Lean.Karger.answerLaw ⟨k, W_k⟩) := by
  let wb := fp + 4 + k * k
  let db := fp + 4 + 2 * (k * k)
  have hfs_eq : fp + frameSize k = db + k := by dsimp only [db]; unfold frameSize; omega
  have hkk_ge : 4 ≤ k * k := Nat.mul_le_mul hk2 hk2
  have hkk_le : k * k ≤ 36 := Nat.mul_le_mul hk6 hk6
  have hdEnd_fit : Fits w (db + k) := hfs_eq ▸ hfit
  have h1 : Fits w 1 := hdEnd_fit.of_le (by dsimp only [db]; omega)
  have hdb_fit : Fits w db := hdEnd_fit.of_le (by omega)
  have hd_eq : wb + k * k = db := by dsimp only [wb, db]; omega
  have hwEnd_fit : Fits w (wb + k * k) := hd_eq ▸ hdb_fit
  have htot_k : Fits w (totalDoubledWeight W_k) :=
    htot.of_le (totalDoubledWeight_le_of_isContractionOf hC)
  let F_mod := Finset.Ico (fp + 2 + k * k) (fp + frameSize k)
  obtain ⟨x_deg, e_pre, hst_deg, hmod_pre⟩ : ∃ x_deg,
      ExecWithin w ram[⟪basePre⟫; ⟪ksCopyCode⟫; ⟪computeDegreesAndTotalAt hr24⟫]
        x x_deg (6 + (7 * (k * k) + 4) + (6 * k ^ 2 + 12 * k + 6)) ∧
      ContractState w wb db k k 2 W_k (x_deg.comap (Fin.castLE hr24)) ∧
      Modifies F_mod x.mem x_deg.mem := by
    have : Fits w 2 := hdEnd_fit.of_le (by dsimp only [db]; omega)
    have : Fits w wb := hwEnd_fit.of_le (by omega)
    refine WP.exists_execWithin ?_
    unfold basePre
    wram_exec [hk_reg, hrem_reg, ha1_reg, ha2_reg,
      show (fp + 2 + k * k) + 2 = wb by dsimp only [wb]; omega, hd_eq]
    wram_call (ksCopyCode_exec (W := W_k) (by wram_simp) (by wram_simp)
      (by wram_simp [hrem_reg]) (by dsimp only [wb]; omega) h1 hwEnd_fit hmat)
      with x_cp ⟨hmat_cp, hmod_cp, _, hwb_cp, hdb_cp, hstr_cp, hk_cp, ht_cp, _⟩
    wram_call (computeDegreesAndTotalAt_exec hr24
      hwb_cp (by wram_simp at hdb_cp; exact hdb_cp)
      (by wram_simp at hstr_cp; exact hstr_cp) (by wram_simp [hk_reg] at hk_cp; exact hk_cp)
      (le_refl k) (Or.inl (by dsimp only [wb, db]; omega)) h1 hwEnd_fit hdEnd_fit htot_k hmat_cp)
      with x_deg ⟨hws_deg, hmod_deg, hwb_deg, hdb_deg, hstr_deg, hk_deg, ht_deg, htot_deg, _⟩
    have ht_deg' : x_deg.regs (Fin.castLE hr24 Reg.targetT) = 2 := by
      rw [ht_deg]; change x_cp.regs targetT = 2; rw [ht_cp]; wram_simp
    refine ⟨by omega, ⟨hwb_deg, hdb_deg, hstr_deg, hk_deg, ht_deg', htot_deg,
      le_refl k, Or.inl (by dsimp only [wb, db]; omega), hwEnd_fit, hdEnd_fit, htot_k, hws_deg⟩,
      modifies_trans_subset hmod_cp hmod_deg
        (fun a ha => by rw [Finset.mem_Ico] at ha ⊢; rw [hfs_eq]; dsimp only [wb, db] at *; omega)
        (fun a ha => by rw [Finset.mem_Ico] at ha ⊢; rw [hfs_eq]; dsimp only [db] at *; omega)⟩
  have hrun := ExecRandLaw.seq (contractDownToAt_law hr24 (le_refl 2) hk2 hC.multigraph hst_deg)
    (Q := fun y => Modifies F_mod x.mem y.mem ∧
      y.regs zero = 0 ∧ y.regs fpReg = parentFp ∧ y.regs spReg = b)
    (κ := fun G => PMF.pure (totalDoubledWeight G.weight / 2))
    fun z ⟨hmod_c, hhi_c, W', hW', hst_c⟩ => by
      have hz_wb : z.regs wBase = wb := hst_c.regs_wBase
      have hz_fp : z.regs fpReg = fp :=
        (hhi_c fpReg (by decide)).trans ((e_pre.regs_eq (by decide)).trans hfp)
      have hz_sp : z.regs spReg = b + 1 :=
        (hhi_c spReg (by decide)).trans ((e_pre.regs_eq (by decide)).trans hsp)
      have hmod_z : Modifies F_mod x.mem z.mem :=
        modifies_trans_subset hmod_pre hmod_c Finset.Subset.rfl
          (workspaceFootprint_subset_Ico (by dsimp only [wb]; omega) (by dsimp only [wb, db]; omega)
            (by rw [hfs_eq]))
      have hz_mem_p : z.mem fp = parentFp := by
        rw [hmod_z fp (by rw [Finset.mem_Ico]; omega), hmem_p]
      obtain ⟨y_p, e_p, hm_p, hz0, hzfp, hzsp, hv_p⟩ : ∃ y_p,
          ExecWithin w basePost z y_p 6 ∧ y_p.mem = z.mem ∧
          y_p.regs zero = 0 ∧ y_p.regs fpReg = parentFp ∧ y_p.regs spReg = b ∧
          y_p.regs retVal = z.mem (wb + 1) := by
        have : Fits w (wb + 1) := hdEnd_fit.of_le (by dsimp only [wb, db]; omega)
        unfold basePost
        wram_exec [hz_wb, hz_fp, hz_sp, hz_mem_p]
        exact ⟨rfl, by wram_simp, by wram_simp, by wram_simp, by wram_simp⟩
      have hv : z.mem (wb + 1) = _ := hst_c.mem_add_one hW'
      exact (ExecRandLaw.of_execWithin (f := fun y => y.regs retVal) e_p
        ⟨hm_p ▸ hmod_z, hz0, hzfp, hzsp⟩).congr_law (by rw [hv_p, hv])
  refine ((ExecRandLaw.foldr_seq_det [basePre, ksCopyCode] e_pre hrun).congr_law ?_).mono
    (fun _ h => h) ?_ le_rfl
  · rw [Lean.Karger.answerLaw_eq]
    exact PMF.bind_pure_comp _ _
  · have : k ^ 2 ≤ 36 := by simpa [sq] using hkk_le
    omega

theorem baseCaseAndPop_spec {n w fp parentFp b k : ℕ} {W₀ : Fin n → Fin n → ℕ}
    {W_k : Fin k → Fin k → ℕ} {part : Fin n → Fin k} {x : Data 24}
    (hk2 : 2 ≤ k) (hk6 : k ≤ 6)
    (hk_reg : x.regs activeK = k) (hrem_reg : x.regs rem = k * k)
    (ha1_reg : x.regs addr1 = fp + 2) (ha2_reg : x.regs addr2 = fp + 2 + k * k)
    (hfp : x.regs fpReg = fp) (hsp : x.regs spReg = b + 1)
    (hmem_p : x.mem fp = parentFp) (hmat : HoldsMatrix x.mem (fp + 2) k W_k)
    (hC : IsContractionOf W₀ part W_k)
    (hfit : Fits w (fp + frameSize k)) (hsp_fit : Fits w b)
    (htot : Fits w (totalDoubledWeight W₀)) :
    ∃ m : ProbComp (Data 24 × ℕ),
      ExecRand w baseCaseAndPop x m ∧
      m.IsQueryBounded (k - 2) ∧
      (∀ z ∈ m.support,
        z.2 ≤ 2000 ∧
        Modifies (Finset.Ico (fp + 2 + k * k) (fp + frameSize k)) x.mem z.1.mem ∧
        z.1.regs zero = 0 ∧
        z.1.regs fpReg = parentFp ∧
        z.1.regs spReg = b ∧
        ∃ C : Finset (Fin n), IsNonTrivialCut C ∧ z.1.regs retVal = cutWeight W₀ C) ∧
      (∀ B : Finset (Fin k),
        0 < minCut W₀ → IsNonTrivialCut B →
        cutWeight W₀ (pullbackCut part B) = minCut W₀ →
        (2 : ℝ≥0∞) / (30 : ℝ≥0∞) ≤
          m.eval.toOuterMeasure {z | z.1.regs retVal = minCut W₀}) := by
  obtain ⟨m, hm, hq, hsup, hlaw⟩ := baseCaseAndPop_law hk2 hk6 hk_reg hrem_reg ha1_reg ha2_reg
    hfp hsp hmem_p hmat hC hfit hsp_fit htot
  refine ⟨m, hm, hq, ?_, ?_⟩
  · intro z hz
    rcases hsup z hz with ⟨⟨hmod, hz0, hzfp, hzsp⟩, ht⟩
    have hv : z.1.regs retVal ∈ (Lean.Karger.answerLaw ⟨k, W_k⟩).support := by
      rw [← hlaw, ProbComp.eval_map, PMF.mem_support_map_iff]
      exact ⟨z, (ProbComp.support_eval m) ▸ hz, rfl⟩
    have hcut := Lean.Karger.exists_cut_of_mem_support_fastCutLaw hk2 hC
      (by rwa [Lean.Karger.fastCutLaw_leaf (by omega)])
    exact ⟨ht, hmod, hz0, hzfp, hzsp, hcut⟩
  · intro B hmin hB hBmin
    have hprob := Lean.Karger.answerLaw_hit_prob_ge hk2 hmin hC hB hBmin
    rw [← hlaw, ProbComp.eval_map, PMF.toOuterMeasure_map_apply] at hprob
    exact (base_survival_ge hk2 hk6).trans hprob

theorem frameSize_le_fastCutScratch (m : ℕ) :
    frameSize m ≤ fastCutScratch m := by
  by_cases hm : 7 ≤ m
  · rw [fastCutScratch_of_ge_seven hm]
    exact Nat.le_add_right _ _
  · rw [fastCutScratch_of_lt_seven (by omega)]

private theorem two_mul_pred_le_frameSize (k : ℕ) :
    2 * k * (k - 1) ≤ frameSize k := by
  unfold frameSize
  have hle : k * (k - 1) ≤ k * k := Nat.mul_le_mul_left k (Nat.sub_le k 1)
  have h2 : 2 * k * (k - 1) = 2 * (k * (k - 1)) := by ring
  omega

private theorem branch_step_bound {k t n_th n_cp n_deg n_c n_tail : ℕ}
    (hk7 : 7 ≤ k) (htk : t ≤ k)
    (hth : n_th ≤ 6 * k + 9)
    (hcp : n_cp ≤ 7 * (k * k) + 4)
    (hdeg : n_deg ≤ 6 * k ^ 2 + 12 * k + 6)
    (hc : n_c ≤ 36 * (k ^ 2 - t ^ 2) + 4)
    (htail : n_tail ≤ 7 * t ^ 2 + 8 * t + 21) :
    n_th + (8 + (n_cp + (n_deg + (n_c + n_tail)))) ≤ 80 * (k * k) := by
  have ht2_le : t ^ 2 ≤ k ^ 2 := Nat.pow_le_pow_left htk 2
  have hkk : k ^ 2 = k * k := sq k
  have hc' : n_c + 7 * t ^ 2 ≤ 36 * (k * k) + 4 := by
    have : 36 * (k ^ 2 - t ^ 2) + 7 * t ^ 2 ≤ 36 * k ^ 2 := by omega
    omega
  obtain ⟨c, rfl⟩ : ∃ c, k = c + 7 := ⟨k - 7, by omega⟩
  nlinarith

/-- Event on a child-frame entry state `d` at `childFp` asserting that `d.mem` holds a valid
`t`-supervertex contraction `(W₁, part₁)` of `W₀` together with a non-trivial cut `B₁` pulling back
to a minimum cut of `W₀`. -/
def ChildMinCutSurvives {n : ℕ} (W₀ : Fin n → Fin n → ℕ) (childFp t : ℕ) (d : Data 24) : Prop :=
  ∃ (W₁ : Fin t → Fin t → ℕ) (part₁ : Fin n → Fin t) (B₁ : Finset (Fin t)),
    IsContractionOf W₀ part₁ W₁ ∧
    HoldsMatrix d.mem (childFp + 2) t W₁ ∧
    IsNonTrivialCut B₁ ∧
    cutWeight W₀ (pullbackCut part₁ B₁) = minCut W₀

private theorem branchTail_exec {w fp b k t : ℕ} {x : Data 24}
    (ht6 : 6 ≤ t) (htk : t ≤ k)
    (hwBase : x.regs wBase = fp + 4 + k * k)
    (hdBase : x.regs dBase = fp + 4 + 2 * (k * k))
    (hstride : x.regs stride = k)
    (htargetT : x.regs targetT = t)
    (hfp : x.regs fpReg = fp)
    (hsp : x.regs spReg = b + 1)
    (hfit : Fits w (fp + frameSize k + frameSize t))
    (hsp_fit : Fits w (b + 2)) :
    ∃ y : Data 24,
      ExecWithin w branchTail x y (7 * t ^ 2 + 8 * t + 21) ∧
      Modifies (Finset.Ico (fp + frameSize k) (fp + frameSize k + frameSize t)) x.mem y.mem ∧
      y.regs zero = 0 ∧
      y.regs fpReg = fp + frameSize k ∧
      y.regs spReg = b + 2 ∧
      y.mem (fp + frameSize k) = fp ∧
      y.mem (fp + frameSize k + 1) = t ∧
      y.mem (fp + frameSize k + 2 + t * t) = 0 ∧
      ∀ i j : Fin t,
        y.mem (fp + frameSize k + 2 + i.val * t + j.val) =
          x.mem (fp + 4 + k * k + i.val * k + j.val) := by
  let wb := fp + 4 + k * k
  let db := fp + 4 + 2 * (k * k)
  let childFp := fp + frameSize k
  have hcfp_eq : db + k = childFp := by dsimp only [db, childFp]; unfold frameSize; omega
  have htt_ge : 36 ≤ t * t := Nat.mul_le_mul ht6 ht6
  have hfs_t : frameSize t = 4 + 2 * (t * t) + t := rfl
  have : Fits w 2 := hfit.of_le (by rw [hfs_t]; omega)
  have : Fits w childFp := hfit.of_le (by omega)
  have : Fits w (childFp + 2) := hfit.of_le (by rw [hfs_t]; omega)
  have : Fits w (t * t) := hfit.of_le (by rw [hfs_t]; omega)
  have hdstEnd : Fits w (childFp + 2 + t * t) := hfit.of_le (by rw [hfs_t]; omega)
  have hkt_le : k * t ≤ k * k := Nat.mul_le_mul_left k htk
  have hwEnd : Fits w (wb + k * t) := hfit.of_le (by dsimp only [wb]; unfold frameSize; omega)
  refine WP.exists_execWithin ?_
  unfold branchTail branchCompactPre
  wram_exec [hdBase, hstride, hcfp_eq]
  wram_call (copySubmatrixCode_exec (W := fun i j => x.mem (wb + i.val * k + j.val))
    (by wram_simp [hwBase]; rfl) (by wram_simp [hstride]) (by wram_simp [htargetT])
    (by wram_simp; dsimp only [childFp, db] at *; omega) (by wram_simp) htk
    (by dsimp only [wb]; rw [← hcfp_eq]; dsimp only [db]; omega)
    hwEnd hdstEnd (fun _ _ => rfl))
    with x₂ ⟨hmat_sub, hmod_sub, _, _, hdb₂, hstr₂, _, ht₂, _, hhi₂⟩
  have hdb₂' : x₂.regs dBase = db := by wram_simp [hdBase] at hdb₂; exact hdb₂
  have hfp₂ : x₂.regs fpReg = fp := (hhi₂ fpReg (by decide)).trans (by wram_simp [hfp])
  have hsp₂ : x₂.regs spReg = b + 1 := (hhi₂ spReg (by decide)).trans (by wram_simp [hsp])
  unfold branchPushChild
  wram_exec [hdb₂', hstr₂, ht₂, hfp₂, hsp₂, hcfp_eq,
    show (childFp + 1) + 1 = childFp + 2 from rfl, show (b + 1) + 1 = b + 2 from rfl]
  refine ⟨?_, by wram_simp, by wram_simp; rfl, by wram_simp,
    by dsimp only [childFp]; wram_simp, by dsimp only [childFp]; wram_simp,
    by dsimp only [childFp]; wram_simp, ?_⟩
  · intro a ha
    rw [Finset.mem_Ico, hfs_t] at ha
    dsimp only [childFp] at *
    wram_simp
    simpa using hmod_sub a (by rw [Finset.mem_Ico]; omega)
  · intro i j
    have hlt := matAddr_lt_end (wb := childFp + 2) (le_refl t) i j
    dsimp only [childFp, wb] at *
    wram_simp
    exact hmat_sub i j

/-- Branch setup observes exactly one canonical contraction reply in the child frame. -/
private theorem branchContractAndPush_law {n w fp b k : ℕ} {W₀ : Fin n → Fin n → ℕ}
    {W_k : Fin k → Fin k → ℕ} {part : Fin n → Fin k} {x : Data 24}
    (hk7 : 7 ≤ k)
    (hk_reg : x.regs activeK = k)
    (hfp : x.regs fpReg = fp)
    (hsp : x.regs spReg = b + 1)
    (hmat : HoldsMatrix x.mem (fp + 2) k W_k)
    (hC : IsContractionOf W₀ part W_k)
    (hfit : Fits w (fp + fastCutScratch k))
    (hsp_fit : Fits w (b + 2))
    (htot : Fits w (totalDoubledWeight W₀)) :
    let t := fastCutThreshold k
    let childFp := fp + frameSize k
    ExecRandLaw w branchContractAndPush x
      (fun y => Modifies (Finset.Ico (fp + 4 + k * k) (fp + fastCutScratch k)) x.mem y.mem ∧
        y.regs zero = 0 ∧ y.regs fpReg = childFp ∧ y.regs spReg = b + 2 ∧
        y.mem childFp = fp ∧ y.mem (childFp + 1) = t ∧
        y.mem (childFp + 2 + t * t) = 0 ∧
        ∃ (W' : Fin t → Fin t → ℕ) (part' : Fin n → Fin t),
          IsContractionOf W₀ part' W' ∧ HoldsMatrix y.mem (childFp + 2) t W')
      (80 * (k * k)) (k - t) (frameGraph childFp t)
      (Lean.Karger.contractLaw (⟨k, W_k⟩, t)) := by
  intro t childFp
  let wb := fp + 4 + k * k
  let db := fp + 4 + 2 * (k * k)
  have ht6 : 6 ≤ t := fastCutThreshold_ge_six hk7
  have htk : t < k := fastCutThreshold_lt (by omega)
  have hscr_eq : fp + fastCutScratch k = childFp + fastCutScratch t := by
    dsimp only [childFp, t]; rw [fastCutScratch_of_ge_seven hk7]; omega
  have hfs_t_le : frameSize t ≤ fastCutScratch t := frameSize_le_fastCutScratch t
  have hcfp_eq : fp + frameSize k = db + k := by dsimp only [db]; unfold frameSize; omega
  have hfit_child : Fits w (childFp + frameSize t) := hfit.of_le (by omega)
  have hfit_th : Fits w (2 * k * (k - 1)) := by
    have := two_mul_pred_le_frameSize k
    exact hfit.of_le (by dsimp only [childFp] at hfit_child; omega)
  have hdEnd_fit : Fits w (db + k) :=
    hfit_child.of_le (by dsimp only [childFp]; rw [hcfp_eq]; omega)
  have h1 : Fits w 1 := hdEnd_fit.of_le (by dsimp only [db]; omega)
  have hdb_fit : Fits w db := hdEnd_fit.of_le (by omega)
  have hd_eq : wb + k * k = db := by dsimp only [wb, db]; omega
  have hwEnd_fit : Fits w (wb + k * k) := hd_eq ▸ hdb_fit
  have htot_k : Fits w (totalDoubledWeight W_k) :=
    htot.of_le (totalDoubledWeight_le_of_isContractionOf hC)
  let S_mod := Finset.Ico wb (fp + fastCutScratch k)
  obtain ⟨x_deg, e_pre, hst_deg, hmod_pre⟩ : ∃ x_deg,
      ExecWithin w
        ram[⟪thresholdCode⟫; ⟪branchSetup⟫; ⟪ksCopyCode⟫; ⟪computeDegreesAndTotalAt hr24⟫]
        x x_deg ((6 * k + 9) + 8 + (7 * (k * k) + 4) + (6 * k ^ 2 + 12 * k + 6)) ∧
      ContractState w wb db k k t W_k (x_deg.comap (Fin.castLE hr24)) ∧
      Modifies S_mod x.mem x_deg.mem := by
    have : Fits w 4 := hdEnd_fit.of_le (by dsimp only [db]; omega)
    have : Fits w (k * k) := hdEnd_fit.of_le (by dsimp only [db]; omega)
    have : Fits w wb := hwEnd_fit.of_le (by omega)
    refine WP.exists_execWithin (WP.seq ?_)
    wram_call (thresholdCode_exec hk7 hk_reg hfit_th)
      with x_th ⟨hmem_th, _, hk_th, ht_th, _, _, _, hhi_th⟩
    have hfp_th : x_th.regs fpReg = fp := (hhi_th fpReg (by decide)).trans hfp
    unfold branchSetup
    wram_exec [hk_th, hfp_th, hd_eq]
    wram_call (ksCopyCode_exec (W := W_k) (by wram_simp) (by wram_simp; rfl) (by wram_simp)
      (by dsimp only [wb]; omega) h1 hwEnd_fit (hmem_th ▸ hmat))
      with x_cp ⟨hmat_cp, hmod_cp, _, hwb_cp, hdb_cp, hstr_cp, hk_cp, ht_cp, _⟩
    wram_call (computeDegreesAndTotalAt_exec hr24
      hwb_cp (by wram_simp at hdb_cp; change x_cp.regs dBase = _; dsimp only [db]; omega)
      (by wram_simp at hstr_cp; exact hstr_cp) (by wram_simp [hk_th] at hk_cp; exact hk_cp)
      (le_refl k) (Or.inl (by dsimp only [wb, db]; omega)) h1 hwEnd_fit hdEnd_fit htot_k hmat_cp)
      with x_deg ⟨hws_deg, hmod_deg, hwb_deg, hdb_deg, hstr_deg, hk_deg, ht_deg, htot_deg, _⟩
    have ht_deg' : x_deg.regs (Fin.castLE hr24 Reg.targetT) = t := by
      rw [ht_deg]; change x_cp.regs targetT = t; rw [ht_cp]; wram_simp [ht_th]; rfl
    refine ⟨by omega, ⟨hwb_deg, hdb_deg, hstr_deg, hk_deg, ht_deg', htot_deg,
      le_refl k, Or.inl (by dsimp only [wb, db]; omega), hwEnd_fit, hdEnd_fit, htot_k, hws_deg⟩,
      modifies_trans_subset (hmem_th ▸ hmod_cp) hmod_deg
        (fun a ha => by
          rw [Finset.mem_Ico] at ha ⊢; rw [hscr_eq]; dsimp only [childFp] at *
          rw [hcfp_eq]; omega)
        (fun a ha => by
          rw [Finset.mem_Ico] at ha ⊢; rw [hscr_eq]; dsimp only [wb, childFp] at *
          rw [hcfp_eq]; omega)⟩
  have hc_law :=
    (contractDownToAt_law hr24 (by omega : 2 ≤ t) htk.le hC.multigraph hst_deg).withSupport
  have hrun := ExecRandLaw.seq hc_law
    (Q := fun y => Modifies S_mod x.mem y.mem ∧
      y.regs zero = 0 ∧ y.regs fpReg = childFp ∧ y.regs spReg = b + 2 ∧
      y.mem childFp = fp ∧ y.mem (childFp + 1) = t ∧
      y.mem (childFp + 2 + t * t) = 0 ∧
      ∃ (W' : Fin t → Fin t → ℕ) (part' : Fin n → Fin t),
        IsContractionOf W₀ part' W' ∧ HoldsMatrix y.mem (childFp + 2) t W')
    (κ := PMF.pure)
    fun z ⟨⟨hmod_c, hhi_c, W', hW', hst_c⟩, hobs⟩ => by
      obtain ⟨W₁, part₁, hgraph, hC₁⟩ :=
        Lean.Karger.isContractionOf_of_mem_support_contractLaw (by omega) htk.le hC hobs
      have heq := hst_c.heldGraph_eq.symm.trans hgraph
      simp only [Lean.Karger.Graph.mk.injEq, heq_eq_eq, true_and] at heq
      obtain ⟨y, e_tail, hmod_tail, hz0, hzfp, hzsp, hm_cfp, hm_cfp1, hm_cfp_stg, hm_sub⟩ :=
        branchTail_exec ht6 htk.le hst_c.regs_wBase hst_c.regs_dBase hst_c.regs_stride
          hst_c.regs_targetT
          ((hhi_c fpReg (by decide)).trans ((e_pre.regs_eq (by decide)).trans hfp))
          ((hhi_c spReg (by decide)).trans ((e_pre.regs_eq (by decide)).trans hsp))
          hfit_child hsp_fit
      have hmat_y : HoldsMatrix y.mem (childFp + 2) t W' :=
        fun i j => (hm_sub i j).trans (hst_c.workspace.1 i j)
      have hmod_y : Modifies S_mod x.mem y.mem :=
        modifies_trans_subset
          (modifies_trans_subset hmod_pre hmod_c Finset.Subset.rfl
            (workspaceFootprint_subset_Ico le_rfl (by dsimp only [wb, db]; omega)
              (by rw [hscr_eq]; dsimp only [childFp] at *; rw [hcfp_eq]; omega)))
          hmod_tail Finset.Subset.rfl
          (fun a ha => by
            rw [Finset.mem_Ico] at ha ⊢; rw [hscr_eq]
            dsimp only [wb, childFp] at *; rw [hcfp_eq]; dsimp only [db]; omega)
      exact (ExecRandLaw.of_execWithin (f := frameGraph childFp t) e_tail
        ⟨hmod_y, hz0, hzfp, hzsp, hm_cfp, hm_cfp1, hm_cfp_stg, W', part₁, heq ▸ hC₁,
          hmat_y⟩).congr_law (congrArg PMF.pure ((frameGraph_eq_iff.mpr hmat_y).trans
            hst_c.heldGraph_eq.symm))
  refine ((ExecRandLaw.foldr_seq_det [thresholdCode, branchSetup, ksCopyCode] e_pre
    hrun).congr_law (PMF.bind_pure _)).mono (fun _ h => h) ?_ (by omega)
  have hbound := branch_step_bound hk7 htk.le le_rfl le_rfl le_rfl le_rfl le_rfl
  omega

theorem branchContractAndPush_spec {n w fp b k : ℕ} {W₀ : Fin n → Fin n → ℕ}
    {W_k : Fin k → Fin k → ℕ} {part : Fin n → Fin k} {x : Data 24}
    (hk7 : 7 ≤ k)
    (hk_reg : x.regs activeK = k)
    (hfp : x.regs fpReg = fp)
    (hsp : x.regs spReg = b + 1)
    (hmat : HoldsMatrix x.mem (fp + 2) k W_k)
    (hC : IsContractionOf W₀ part W_k)
    (hfit : Fits w (fp + fastCutScratch k))
    (hsp_fit : Fits w (b + 2))
    (htot : Fits w (totalDoubledWeight W₀)) :
    let t := fastCutThreshold k
    let childFp := fp + frameSize k
    ∃ m : ProbComp (Data 24 × ℕ),
      ExecRand w branchContractAndPush x m ∧
      m.IsQueryBounded (k - t) ∧
      (∀ z ∈ m.support,
        z.2 ≤ 80 * (k * k) ∧
        Modifies (Finset.Ico (fp + 4 + k * k) (fp + fastCutScratch k)) x.mem z.1.mem ∧
        z.1.regs zero = 0 ∧
        z.1.regs fpReg = childFp ∧
        z.1.regs spReg = b + 2 ∧
        z.1.mem childFp = fp ∧
        z.1.mem (childFp + 1) = t ∧
        z.1.mem (childFp + 2 + t * t) = 0 ∧
        ∃ (W' : Fin t → Fin t → ℕ) (part' : Fin n → Fin t),
          IsContractionOf W₀ part' W' ∧
          HoldsMatrix z.1.mem (childFp + 2) t W') ∧
      (∀ B : Finset (Fin k),
        0 < minCut W₀ → IsNonTrivialCut B →
        cutWeight W₀ (pullbackCut part B) = minCut W₀ →
        (1 : ℝ≥0∞) / 2 ≤
          m.eval.toOuterMeasure {z | ChildMinCutSurvives W₀ childFp t z.1}) := by
  intro t childFp
  obtain ⟨m, hm, hq, hsup, hlaw⟩ := branchContractAndPush_law hk7 hk_reg hfp hsp hmat hC
    hfit hsp_fit htot
  refine ⟨m, hm, hq, fun z hz => ⟨(hsup z hz).2, (hsup z hz).1⟩, ?_⟩
  intro B hmin hB hBmin
  have hprob := (half_le_threshold_survival hk7).trans
    (Lean.Karger.survives_contractLaw (fastCutThreshold_ge_two (by omega))
      (Nat.le_of_lt (fastCutThreshold_lt (by omega))) hmin hC hB hBmin)
  rw [← hlaw, ProbComp.eval_map, PMF.toOuterMeasure_map_apply] at hprob
  refine hprob.trans (PMF.toOuterMeasure_mono _ fun z ⟨hz, _⟩ => ?_)
  obtain ⟨W', part', B', hgraph, hC', hpb⟩ := hz
  exact ⟨W', part', B', hC', frameGraph_eq_iff.mp hgraph,
    isNonTrivialCut_of_pullbackCut part' (hpb ▸ isNonTrivialCut_pullbackCut hC.surj hB),
    hpb ▸ hBmin⟩

/-- Stage 0 observes one canonical contraction reply in the child frame. -/
private theorem fastCutStep_stage0_law {n w fp b k : ℕ} {W₀ : Fin n → Fin n → ℕ}
    {W_k : Fin k → Fin k → ℕ} {part : Fin n → Fin k} {x : Data 24}
    (hk7 : 7 ≤ k)
    (h0 : x.regs zero = 0) (hfp : x.regs fpReg = fp) (hsp : x.regs spReg = b + 1)
    (hmem_k : x.mem (fp + 1) = k) (hmem_stg : x.mem (fp + 2 + k * k) = 0)
    (hmat : HoldsMatrix x.mem (fp + 2) k W_k) (hC : IsContractionOf W₀ part W_k)
    (hfit : Fits w (fp + fastCutScratch k)) (hsp_fit : Fits w (b + 2))
    (htot : Fits w (totalDoubledWeight W₀)) :
    let t := fastCutThreshold k
    let childFp := fp + frameSize k
    LoopSegmentLaw w (Cond.lt zero spReg) fastCutStep x
      (fun y => Modifies (Finset.Ico (fp + 2 + k * k) (fp + fastCutScratch k)) x.mem y.mem ∧
        y.mem (fp + 2 + k * k) = 1 ∧
        y.regs zero = 0 ∧
        y.regs fpReg = childFp ∧
        y.regs spReg = b + 2 ∧
        y.mem childFp = fp ∧
        y.mem (childFp + 1) = t ∧
        y.mem (childFp + 2 + t * t) = 0 ∧
        ∃ (W' : Fin t → Fin t → ℕ) (part' : Fin n → Fin t),
          IsContractionOf W₀ part' W' ∧
          HoldsMatrix y.mem (childFp + 2) t W')
      (80 * (k * k) + 15) (k - t) (frameGraph childFp t)
      (Lean.Karger.contractLaw (⟨k, W_k⟩, t)) := by
  intro t childFp
  have hc_loop : (Cond.lt zero spReg).Holds x := by simp [Cond.holds_lt, h0, hsp]
  have hfs_le : frameSize k ≤ fastCutScratch k := frameSize_le_fastCutScratch k
  obtain ⟨y_h, hex_hdr, hm_h, h0_h, h1_h, hk_h, _, _, ha2_h, hv2_h, hv1_h, hhi_h⟩ :=
    stepHeader_exec (by omega : 2 ≤ k) hfp hmem_k hmem_stg (hfit.of_le (by omega))
  have hfp_h : y_h.regs fpReg = fp := (hhi_h fpReg (by decide)).trans hfp
  have hsp_h : y_h.regs spReg = b + 1 := (hhi_h spReg (by decide)).trans hsp
  have hnc_lt : ¬(Cond.lt activeK val1).Holds y_h := by
    simp only [Cond.holds_lt, hk_h, hv1_h]; omega
  have hc_eq0 : (Cond.eq val2 zero).Holds y_h := by simp [Cond.holds_eq, hv2_h, h0_h]
  let y_s := y_h.write (fp + 2 + k * k) 1
  have hex_s0 : Exec (B := .standard) w stageZeroSet y_h y_s 1 := by
    unfold stageZeroSet
    simpa [y_s, ha2_h, h1_h] using
      Exec.store (B := .standard) (w := w) (a := addr2) (s := one) (x := y_h)
  have hmat_s : HoldsMatrix y_s.mem (fp + 2) k W_k := fun i j => by
    have hlt := matAddr_lt_end (wb := fp + 2) (le_refl k) i j
    change Function.update y_h.mem (fp + 2 + k * k) 1 _ = W_k i j
    rw [Function.update_of_ne (by omega), hm_h]
    exact hmat i j
  have hbcp :=
    branchContractAndPush_law (x := y_s) hk7 hk_h hfp_h hsp_h hmat_s hC hfit hsp_fit htot
  have hstep : ExecRandLaw w fastCutStep x
      (fun y => Modifies (Finset.Ico (fp + 4 + k * k) (fp + fastCutScratch k)) y_s.mem y.mem ∧
        y.regs zero = 0 ∧ y.regs fpReg = childFp ∧ y.regs spReg = b + 2 ∧
        y.mem childFp = fp ∧ y.mem (childFp + 1) = t ∧ y.mem (childFp + 2 + t * t) = 0 ∧
        ∃ (W' : Fin t → Fin t → ℕ) (part' : Fin n → Fin t),
          IsContractionOf W₀ part' W' ∧ HoldsMatrix y.mem (childFp + 2) t W')
      (9 + (((1 + 80 * (k * k)) + 1) + 2)) (k - t) (frameGraph childFp t)
      (Lean.Karger.contractLaw (⟨k, W_k⟩, t)) := by
    unfold fastCutStep
    exact ExecRandLaw.seq_det hex_hdr.within
      (ExecRandLaw.branch_neg hnc_lt (ExecRandLaw.branch_pos hc_eq0
        (ExecRandLaw.seq_det hex_s0.within hbcp)))
  refine (LoopSegmentLaw.single hc_loop hstep).mono (fun z ⟨hmod₀, rest⟩ => ?_) (by omega) le_rfl
  have hstg_in : fp + 2 + k * k ∈ Finset.Ico (fp + 2 + k * k) (fp + fastCutScratch k) := by
    rw [Finset.mem_Ico]; unfold frameSize at hfs_le; omega
  have hmod_s : Modifies (Finset.Ico (fp + 2 + k * k) (fp + fastCutScratch k)) x.mem y_s.mem := by
    change Modifies _ x.mem (Function.update y_h.mem (fp + 2 + k * k) 1)
    exact hm_h ▸ modifies_update_of_mem hstg_in x.mem 1
  have hstg_val : z.mem (fp + 2 + k * k) = 1 := by
    rw [hmod₀ _ (by rw [Finset.mem_Ico]; omega)]
    exact Function.update_self _ _ _
  exact ⟨modifies_trans_subset hmod_s hmod₀ Finset.Subset.rfl
    (Finset.Ico_subset_Ico (by omega) le_rfl), hstg_val, rest⟩

/-- Stage 1 observes one canonical contraction reply in the child frame. -/
private theorem fastCutStep_stage1_law {n w fp b k v1 : ℕ} {W₀ : Fin n → Fin n → ℕ}
    {W_k : Fin k → Fin k → ℕ} {part : Fin n → Fin k} {x : Data 24}
    (hk7 : 7 ≤ k)
    (h0 : x.regs zero = 0) (hfp : x.regs fpReg = fp) (hsp : x.regs spReg = b + 1)
    (hret : x.regs retVal = v1)
    (hmem_k : x.mem (fp + 1) = k) (hmem_stg : x.mem (fp + 2 + k * k) = 1)
    (hmat : HoldsMatrix x.mem (fp + 2) k W_k) (hC : IsContractionOf W₀ part W_k)
    (hfit : Fits w (fp + fastCutScratch k)) (hsp_fit : Fits w (b + 2))
    (htot : Fits w (totalDoubledWeight W₀)) :
    let t := fastCutThreshold k
    let childFp := fp + frameSize k
    LoopSegmentLaw w (Cond.lt zero spReg) fastCutStep x
      (fun y => Modifies (Finset.Ico (fp + 2 + k * k) (fp + fastCutScratch k)) x.mem y.mem ∧
        y.mem (fp + 2 + k * k) = 2 ∧
        y.mem (fp + 3 + k * k) = v1 ∧
        y.regs zero = 0 ∧
        y.regs fpReg = childFp ∧
        y.regs spReg = b + 2 ∧
        y.mem childFp = fp ∧
        y.mem (childFp + 1) = t ∧
        y.mem (childFp + 2 + t * t) = 0 ∧
        ∃ (W' : Fin t → Fin t → ℕ) (part' : Fin n → Fin t),
          IsContractionOf W₀ part' W' ∧
          HoldsMatrix y.mem (childFp + 2) t W')
      (80 * (k * k) + 20) (k - t) (frameGraph childFp t)
      (Lean.Karger.contractLaw (⟨k, W_k⟩, t)) := by
  intro t childFp
  have hc_loop : (Cond.lt zero spReg).Holds x := by simp [Cond.holds_lt, h0, hsp]
  have hfs_le : frameSize k ≤ fastCutScratch k := frameSize_le_fastCutScratch k
  have hfit_fs : Fits w (fp + frameSize k) := hfit.of_le (by omega)
  obtain ⟨y_h, hex_hdr, hm_h, h0_h, h1_h, hk_h, _, _, ha2_h, hv2_h, hv1_h, hhi_h⟩ :=
    stepHeader_exec (by omega : 2 ≤ k) hfp hmem_k hmem_stg hfit_fs
  have hfp_h : y_h.regs fpReg = fp := (hhi_h fpReg (by decide)).trans hfp
  have hsp_h : y_h.regs spReg = b + 1 := (hhi_h spReg (by decide)).trans hsp
  have hret_h : y_h.regs retVal = v1 := (hhi_h retVal (by decide)).trans hret
  have hnc_lt : ¬(Cond.lt activeK val1).Holds y_h := by
    simp only [Cond.holds_lt, hk_h, hv1_h]; omega
  have hnc_eq0 : ¬(Cond.eq val2 zero).Holds y_h := by simp [Cond.holds_eq, hv2_h, h0_h]
  have hc_eq1 : (Cond.eq val2 one).Holds y_h := by simp [Cond.holds_eq, hv2_h, h1_h]
  obtain ⟨y_s, hex_s1, hys_mem, hk_s, hfp_s, hsp_s⟩ : ∃ y_s,
      ExecWithin w stageOneSaveAndSet y_h y_s 4 ∧
      y_s.mem = Function.update (Function.update x.mem (fp + 2 + k * k) 2) (fp + 3 + k * k) v1 ∧
      y_s.regs activeK = k ∧ y_s.regs fpReg = fp ∧ y_s.regs spReg = b + 1 := by
    have : Fits w 2 := hfit_fs.of_le (by unfold frameSize; omega)
    have : Fits w (fp + 3 + k * k) := hfit_fs.of_le (by unfold frameSize; omega)
    unfold stageOneSaveAndSet
    wram_exec [h1_h, ha2_h, hret_h, show (fp + 2 + k * k) + 1 = fp + 3 + k * k by omega]
    exact ⟨by simp [Data.set_mem, Data.write_mem, hm_h],
      by wram_simp [hk_h], by wram_simp [hfp_h], by wram_simp [hsp_h]⟩
  have hmat_s : HoldsMatrix y_s.mem (fp + 2) k W_k := fun i j => by
    have hlt := matAddr_lt_end (wb := fp + 2) (le_refl k) i j
    rw [hys_mem, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact hmat i j
  have hbcp :=
    branchContractAndPush_law (x := y_s) hk7 hk_s hfp_s hsp_s hmat_s hC hfit hsp_fit htot
  have hstep : ExecRandLaw w fastCutStep x
      (fun y => Modifies (Finset.Ico (fp + 4 + k * k) (fp + fastCutScratch k)) y_s.mem y.mem ∧
        y.regs zero = 0 ∧ y.regs fpReg = childFp ∧ y.regs spReg = b + 2 ∧
        y.mem childFp = fp ∧ y.mem (childFp + 1) = t ∧ y.mem (childFp + 2 + t * t) = 0 ∧
        ∃ (W' : Fin t → Fin t → ℕ) (part' : Fin n → Fin t),
          IsContractionOf W₀ part' W' ∧ HoldsMatrix y.mem (childFp + 2) t W')
      (9 + ((((4 + 80 * (k * k)) + 1) + 2) + 2)) (k - t) (frameGraph childFp t)
      (Lean.Karger.contractLaw (⟨k, W_k⟩, t)) := by
    unfold fastCutStep
    exact ExecRandLaw.seq_det hex_hdr.within
      (ExecRandLaw.branch_neg hnc_lt (ExecRandLaw.branch_neg hnc_eq0
        (ExecRandLaw.branch_pos hc_eq1 (ExecRandLaw.seq_det hex_s1 hbcp))))
  refine (LoopSegmentLaw.single hc_loop hstep).mono (fun z ⟨hmod₀, rest⟩ => ?_) (by omega) le_rfl
  have hstg_in : fp + 2 + k * k ∈ Finset.Ico (fp + 2 + k * k) (fp + fastCutScratch k) := by
    rw [Finset.mem_Ico]; unfold frameSize at hfs_le; omega
  have hv1_in : fp + 3 + k * k ∈ Finset.Ico (fp + 2 + k * k) (fp + fastCutScratch k) := by
    rw [Finset.mem_Ico]; unfold frameSize at hfs_le; omega
  have hmod_s : Modifies (Finset.Ico (fp + 2 + k * k) (fp + fastCutScratch k)) x.mem y_s.mem := by
    rw [hys_mem]
    exact modifies_trans_subset (modifies_update_of_mem hstg_in x.mem 2)
      (modifies_update_of_mem hv1_in _ v1) Finset.Subset.rfl Finset.Subset.rfl
  have hstg_val : z.mem (fp + 2 + k * k) = 2 := by
    rw [hmod₀ _ (by rw [Finset.mem_Ico]; omega), hys_mem,
      Function.update_of_ne (by omega), Function.update_self]
  have hv1_val : z.mem (fp + 3 + k * k) = v1 := by
    rw [hmod₀ _ (by rw [Finset.mem_Ico]; omega), hys_mem, Function.update_self]
  exact ⟨modifies_trans_subset hmod_s hmod₀ Finset.Subset.rfl
    (Finset.Ico_subset_Ico (by omega) le_rfl), hstg_val, hv1_val, rest⟩

private theorem fastCutStep_stage2_seg {w fp parentFp b k v1 r2 : ℕ} {x : Data 24}
    (hk7 : 7 ≤ k)
    (h0 : x.regs zero = 0) (hfp : x.regs fpReg = fp) (hsp : x.regs spReg = b + 1)
    (hr2 : x.regs retVal = r2)
    (hmem_p : x.mem fp = parentFp) (hmem_k : x.mem (fp + 1) = k)
    (hmem_stg : x.mem (fp + 2 + k * k) = 2) (hmem_v1 : x.mem (fp + 3 + k * k) = v1)
    (hfit : Fits w (fp + frameSize k)) (hsp_fit : Fits w b) :
    ∃ (y : Data 24) (n_s2 : ℕ),
      n_s2 ≤ 24 ∧
      LoopSegment w (Cond.lt zero spReg) fastCutStep x (pure (y, n_s2)) ∧
      y.mem = x.mem ∧
      y.regs zero = 0 ∧
      y.regs fpReg = parentFp ∧
      y.regs spReg = b ∧
      y.regs retVal = min v1 r2 := by
  have hc_loop : (Cond.lt zero spReg).Holds x := by simp [Cond.holds_lt, h0, hsp]
  obtain ⟨y_h, hex_hdr, hm_h, h0_h, h1_h, hk_h, _, _, ha2_h, hv2_h, hv1_h, hhi_h⟩ :=
    stepHeader_exec (by omega : 2 ≤ k) hfp hmem_k hmem_stg hfit
  have hfp_h : y_h.regs fpReg = fp := (hhi_h fpReg (by decide)).trans hfp
  have hsp_h : y_h.regs spReg = b + 1 := (hhi_h spReg (by decide)).trans hsp
  have hr2_h : y_h.regs retVal = r2 := (hhi_h retVal (by decide)).trans hr2
  have hnc_lt : ¬(Cond.lt activeK val1).Holds y_h := by
    simp only [Cond.holds_lt, hk_h, hv1_h]; omega
  have hnc_eq0 : ¬(Cond.eq val2 zero).Holds y_h := by
    simp [Cond.holds_eq, hv2_h, h0_h]
  have hnc_eq1 : ¬(Cond.eq val2 one).Holds y_h := by
    simp [Cond.holds_eq, hv2_h, h1_h]
  obtain ⟨y_f, ⟨n_c, hn_c, hex_c⟩, hm_f, h0_f, hfp_f, hsp_f, hret_f⟩ :=
    combineAndPop_exec (by omega : 2 ≤ k) h0_h h1_h ha2_h hfp_h hsp_h hr2_h
      (hm_h ▸ hmem_p) (hm_h ▸ hmem_v1) hfit hsp_fit
  have hstep : Exec w fastCutStep x y_f (9 + (((n_c + 2) + 2) + 2)) := by
    unfold fastCutStep
    exact hex_hdr.seq (.branch_neg hnc_lt (.branch_neg hnc_eq0 (.branch_neg hnc_eq1 hex_c)))
  exact ⟨y_f, 9 + (((n_c + 2) + 2) + 2) + 2, by omega,
    LoopSegment.detSingle hc_loop hstep, hm_f.trans hm_h, h0_f, hfp_f, hsp_f, hret_f⟩

/-- A leaf loop segment has the exact recursive answer law and its original pathwise budgets. -/
private theorem fastCutStep_base_law {n w fp parentFp b k : ℕ} {W₀ : Fin n → Fin n → ℕ}
    {W_k : Fin k → Fin k → ℕ} {part : Fin n → Fin k} {x : Data 24}
    (hk2 : 2 ≤ k) (hk6 : k ≤ 6)
    (h0 : x.regs zero = 0) (hfp : x.regs fpReg = fp) (hsp : x.regs spReg = b + 1)
    (hmem_p : x.mem fp = parentFp) (hmem_k : x.mem (fp + 1) = k)
    (hmat : HoldsMatrix x.mem (fp + 2) k W_k) (hC : IsContractionOf W₀ part W_k)
    (hfit : Fits w (fp + frameSize k)) (hsp_fit : Fits w b)
    (htot : Fits w (totalDoubledWeight W₀)) :
    LoopSegmentLaw w (Cond.lt zero spReg) fastCutStep x
      (fun y => Modifies (Finset.Ico (fp + 2 + k * k) (fp + frameSize k)) x.mem y.mem ∧
        y.regs zero = 0 ∧ y.regs fpReg = parentFp ∧ y.regs spReg = b)
      2400 (k - 2) (fun y => y.regs retVal) (Lean.Karger.fastCutLaw k ⟨k, W_k⟩) := by
  have hc_loop : (Cond.lt zero spReg).Holds x := by simp [Cond.holds_lt, h0, hsp]
  obtain ⟨y_h, hex_hdr, hm_h, _, _, hk_h, hrem_h, ha1_h, ha2_h, _, hv1_h, hhi_h⟩ :=
    stepHeader_exec hk2 hfp hmem_k rfl hfit
  have hfp_h : y_h.regs fpReg = fp := (hhi_h fpReg (by decide)).trans hfp
  have hsp_h : y_h.regs spReg = b + 1 := (hhi_h spReg (by decide)).trans hsp
  have hc_lt : (Cond.lt activeK val1).Holds y_h := by
    simp only [Cond.holds_lt, hk_h, hv1_h]
    omega
  have hbase := baseCaseAndPop_law hk2 hk6 hk_h hrem_h ha1_h ha2_h hfp_h hsp_h
    (hm_h ▸ hmem_p) (hm_h ▸ hmat) hC hfit hsp_fit htot
  have hstep : ExecRandLaw w fastCutStep x
      (fun y => Modifies (Finset.Ico (fp + 2 + k * k) (fp + frameSize k)) x.mem y.mem ∧
        y.regs zero = 0 ∧ y.regs fpReg = parentFp ∧ y.regs spReg = b)
      2010 (k - 2) (fun y => y.regs retVal) (Lean.Karger.answerLaw ⟨k, W_k⟩) := by
    unfold fastCutStep
    exact (ExecRandLaw.seq_det hex_hdr.within (ExecRandLaw.branch_pos hc_lt hbase)).mono
      (fun y ⟨hmod, hz0, hzfp, hzsp⟩ => ⟨hm_h ▸ hmod, hz0, hzfp, hzsp⟩) (by omega) le_rfl
  exact ((LoopSegmentLaw.single hc_loop hstep).congr_law
    (Lean.Karger.fastCutLaw_leaf (by omega) _).symm).mono (fun _ h => h) (by omega) le_rfl

/-- A nonrecursive node uses the same law, instruction bound and random-call bound as its leaf. -/
private theorem fastCutNode_base_law {n w d fp parentFp b k : ℕ} {W₀ : Fin n → Fin n → ℕ}
    {W_k : Fin k → Fin k → ℕ} {part : Fin n → Fin k} {x : Data 24}
    (hk2 : 2 ≤ k) (hk6 : k ≤ 6)
    (h0 : x.regs zero = 0) (hfp : x.regs fpReg = fp) (hsp : x.regs spReg = b + 1)
    (hmem_p : x.mem fp = parentFp) (hmem_k : x.mem (fp + 1) = k)
    (hmat : HoldsMatrix x.mem (fp + 2) k W_k) (hC : IsContractionOf W₀ part W_k)
    (hfit : Fits w (fp + fastCutScratch k)) (hsp_fit : Fits w (b + 1 + d))
    (htot : Fits w (totalDoubledWeight W₀)) :
    LoopSegmentLaw w (Cond.lt zero spReg) fastCutStep x
      (fun y => Modifies (Finset.Ico (fp + 2 + k * k) (fp + fastCutScratch k)) x.mem y.mem ∧
        y.regs zero = 0 ∧ y.regs fpReg = parentFp ∧ y.regs spReg = b)
      (fastCutNodeTime k) (fastCutNodeQueries k) (fun y => y.regs retVal)
      (Lean.Karger.fastCutLaw k ⟨k, W_k⟩) := by
  have hk7 : k < 7 := by omega
  have hscr := fastCutScratch_of_lt_seven hk7
  rw [fastCutNodeTime_of_lt_seven hk7, fastCutNodeQueries_of_lt_seven hk7, hscr]
  exact fastCutStep_base_law hk2 hk6 h0 hfp hsp hmem_p hmem_k hmat hC (hscr ▸ hfit)
    (hsp_fit.of_le (by omega)) htot

private theorem composeBranchWithChild_law {n w d' fp b k T_s : ℕ}
    {W₀ : Fin n → Fin n → ℕ} {W_k : Fin k → Fin k → ℕ}
    {P_frame : (ℕ → ℕ) → Prop} {d₀ : Data 24}
    (hk7 : 7 ≤ k) (hd' : fastCutDepth (fastCutThreshold k) ≤ d')
    (hfit : Fits w (fp + fastCutScratch k)) (hsp_fit : Fits w (b + 1 + (d' + 1)))
    (hs : LoopSegmentLaw w (Cond.lt zero spReg) fastCutStep d₀
      (fun y =>
        let t := fastCutThreshold k
        let childFp := fp + frameSize k
        Modifies (Finset.Ico (fp + 2 + k * k) (fp + fastCutScratch k)) d₀.mem y.mem ∧
        P_frame y.mem ∧ y.regs zero = 0 ∧ y.regs fpReg = childFp ∧ y.regs spReg = b + 2 ∧
        y.mem childFp = fp ∧ y.mem (childFp + 1) = t ∧
        y.mem (childFp + 2 + t * t) = 0 ∧
        ∃ (W' : Fin t → Fin t → ℕ) (part' : Fin n → Fin t),
          IsContractionOf W₀ part' W' ∧ HoldsMatrix y.mem (childFp + 2) t W')
      T_s (k - fastCutThreshold k) (frameGraph (fp + frameSize k) (fastCutThreshold k))
      (Lean.Karger.contractLaw (⟨k, W_k⟩, fastCutThreshold k)))
    (hP_pres : ∀ m₁ m₂ : ℕ → ℕ,
      let t := fastCutThreshold k
      let childFp := fp + frameSize k
      Modifies (Finset.Ico (childFp + 2 + t * t) (childFp + fastCutScratch t)) m₁ m₂ →
      P_frame m₁ → P_frame m₂)
    (hih : ∀ {W_t : Fin (fastCutThreshold k) → Fin (fastCutThreshold k) → ℕ}
      {part_t : Fin n → Fin (fastCutThreshold k)} {x_c : Data 24},
      let t := fastCutThreshold k
      let childFp := fp + frameSize k
      2 ≤ t → fastCutDepth t ≤ d' →
      x_c.regs zero = 0 → x_c.regs fpReg = childFp → x_c.regs spReg = (b + 1) + 1 →
      x_c.mem childFp = fp → x_c.mem (childFp + 1) = t → x_c.mem (childFp + 2 + t * t) = 0 →
      HoldsMatrix x_c.mem (childFp + 2) t W_t → IsContractionOf W₀ part_t W_t →
      Fits w (childFp + fastCutScratch t) → Fits w ((b + 1) + 1 + d') →
      LoopSegmentLaw w (Cond.lt zero spReg) fastCutStep x_c
        (fun y => Modifies (Finset.Ico (childFp + 2 + t * t) (childFp + fastCutScratch t))
          x_c.mem y.mem ∧ y.regs zero = 0 ∧ y.regs fpReg = fp ∧ y.regs spReg = b + 1)
        (fastCutNodeTime t) (fastCutNodeQueries t) (fun y => y.regs retVal)
        (Lean.Karger.fastCutLaw t ⟨t, W_t⟩)) :
    let t := fastCutThreshold k
    LoopSegmentLaw w (Cond.lt zero spReg) fastCutStep d₀
      (fun y => Modifies (Finset.Ico (fp + 2 + k * k) (fp + fastCutScratch k)) d₀.mem y.mem ∧
        P_frame y.mem ∧ y.regs zero = 0 ∧ y.regs fpReg = fp ∧ y.regs spReg = b + 1)
      (T_s + fastCutNodeTime t) ((k - t) + fastCutNodeQueries t) (fun y => y.regs retVal)
      ((Lean.Karger.contractLaw (⟨k, W_k⟩, t)).bind
        fun child => Lean.Karger.fastCutLaw t child) := by
  intro t
  let childFp := fp + frameSize k
  have ht : 2 ≤ t := fastCutThreshold_ge_two (by omega)
  have hscr_eq : fp + fastCutScratch k = childFp + fastCutScratch t := by
    dsimp only [childFp, t]
    rw [fastCutScratch_of_ge_seven hk7]
    omega
  refine hs.trans (κ := Lean.Karger.fastCutLaw t) fun y hy => ?_
  rcases hy with ⟨hmod, hP, hz0, hzfp, hzsp, hm_p, hm_k, hm_stg, W', part', hC', hmat⟩
  have hc := hih ht hd' hz0 hzfp hzsp hm_p hm_k hm_stg hmat hC'
    (hscr_eq ▸ hfit) (hsp_fit.of_le (by omega))
  refine (hc.congr_law (by rw [frameGraph_eq_iff.mpr hmat])).mono ?_ le_rfl le_rfl
  intro z ⟨hmod_c, hz0_c, hzfp_c, hzsp_c⟩
  have hsub_c : Finset.Ico (childFp + 2 + t * t) (childFp + fastCutScratch t) ⊆
      Finset.Ico (fp + 2 + k * k) (fp + fastCutScratch k) := by
    intro a ha
    rw [Finset.mem_Ico] at ha ⊢
    rw [hscr_eq]
    dsimp only [childFp] at *
    unfold frameSize at *
    omega
  exact ⟨modifies_trans_subset hmod hmod_c Finset.Subset.rfl hsub_c,
    hP_pres y.mem z.mem hmod_c hP, hz0_c, hzfp_c, hzsp_c⟩

/-- Every native recursive node has exactly the specification's answer law, with the existing
supported-path instruction, random-call and memory-frame bounds. -/
theorem fastCutNode_law {n w : ℕ} {W₀ : Fin n → Fin n → ℕ}
    (htot : Fits w (totalDoubledWeight W₀)) :
    ∀ (d : ℕ) {fp parentFp b k : ℕ} {W_k : Fin k → Fin k → ℕ} {part : Fin n → Fin k}
      {x : Data 24},
      2 ≤ k → fastCutDepth k ≤ d →
      x.regs zero = 0 → x.regs fpReg = fp → x.regs spReg = b + 1 →
      x.mem fp = parentFp → x.mem (fp + 1) = k → x.mem (fp + 2 + k * k) = 0 →
      HoldsMatrix x.mem (fp + 2) k W_k → IsContractionOf W₀ part W_k →
      Fits w (fp + fastCutScratch k) → Fits w (b + 1 + d) →
      LoopSegmentLaw w (Cond.lt zero spReg) fastCutStep x
        (fun y => Modifies (Finset.Ico (fp + 2 + k * k) (fp + fastCutScratch k)) x.mem y.mem ∧
          y.regs zero = 0 ∧ y.regs fpReg = parentFp ∧ y.regs spReg = b)
        (fastCutNodeTime k) (fastCutNodeQueries k) (fun y => y.regs retVal)
        (Lean.Karger.fastCutLaw k ⟨k, W_k⟩) := by
  intro d
  induction d with
  | zero =>
    intro fp parentFp b k W_k part x hk hd h0 hfp hsp hm_p hm_k _ hmat hC hfit hsp_fit
    have hk6 : k ≤ 6 := by
      by_contra h
      rw [fastCutDepth_of_ge_seven (by omega)] at hd
      omega
    exact fastCutNode_base_law hk hk6 h0 hfp hsp hm_p hm_k hmat hC hfit hsp_fit htot
  | succ d' ih =>
    intro fp parentFp b k W_k part x hk hd h0 hfp hsp hm_p hm_k hm_stg hmat hC hfit hsp_fit
    by_cases hk7 : 7 ≤ k
    · let t := fastCutThreshold k
      have hd' : fastCutDepth t ≤ d' := by
        dsimp only [t]
        rw [fastCutDepth_of_ge_seven hk7] at hd
        omega
      have hkk49 : 49 ≤ k * k := Nat.mul_le_mul hk7 hk7
      have hfs_le := frameSize_le_fastCutScratch k
      have hsp_b2 : Fits w (b + 2) := hsp_fit.of_le (by omega)
      have hs0 := fastCutStep_stage0_law hk7 h0 hfp hsp hm_k hm_stg hmat hC hfit hsp_b2 htot
      have hfirst := composeBranchWithChild_law
        (P_frame := fun mem => mem (fp + 2 + k * k) = 1)
        hk7 hd' hfit hsp_fit hs0
        (fun m₁ m₂ hmod h1 => by
          rw [hmod _ (by rw [Finset.mem_Ico]; unfold frameSize; omega)]
          exact h1)
        (fun ht hd hz0 hzfp hzsp hmp hmk hms hmc hcc hfc hsc =>
          ih ht hd hz0 hzfp hzsp hmp hmk hms hmc hcc hfc hsc)
      let branch := (Lean.Karger.contractLaw (⟨k, W_k⟩, t)).bind
        fun child => Lean.Karger.fastCutLaw t child
      have hsecond : ∀ y,
          (Modifies (Finset.Ico (fp + 2 + k * k) (fp + fastCutScratch k)) x.mem y.mem ∧
            y.mem (fp + 2 + k * k) = 1 ∧
            y.regs zero = 0 ∧ y.regs fpReg = fp ∧ y.regs spReg = b + 1) →
          LoopSegmentLaw w (Cond.lt zero spReg) fastCutStep y
            (fun z => Modifies (Finset.Ico (fp + 2 + k * k) (fp + fastCutScratch k))
              x.mem z.mem ∧ z.regs zero = 0 ∧ z.regs fpReg = parentFp ∧ z.regs spReg = b)
            (80 * (k * k) + 44 + fastCutNodeTime t) ((k - t) + fastCutNodeQueries t)
            (fun z => z.regs retVal) (branch.map (min (y.regs retVal))) := by
        intro y ⟨hmod₁, hstg₁, hy0, hyfp, hysp⟩
        let v₁ := y.regs retVal
        have hm1_p : y.mem fp = parentFp := by
          rw [hmod₁ _ (by rw [Finset.mem_Ico]; omega), hm_p]
        have hm1_k : y.mem (fp + 1) = k := by
          rw [hmod₁ _ (by rw [Finset.mem_Ico]; omega), hm_k]
        have hm1_mat : HoldsMatrix y.mem (fp + 2) k W_k := by
          intro i j
          have hlt := matAddr_lt_end (wb := fp + 2) (le_refl k) i j
          rw [hmod₁ _ (by rw [Finset.mem_Ico]; omega)]
          exact hmat i j
        have hs1 := fastCutStep_stage1_law (v1 := v₁) hk7 hy0 hyfp hysp rfl hm1_k hstg₁
          hm1_mat hC hfit hsp_b2 htot
        have hbranch₂ := composeBranchWithChild_law
          (P_frame := fun mem => mem (fp + 2 + k * k) = 2 ∧ mem (fp + 3 + k * k) = v₁)
          hk7 hd' hfit hsp_fit
          (hs1.mono (fun z ⟨hmod, hstg, hv, rest⟩ => ⟨hmod, ⟨hstg, hv⟩, rest⟩) le_rfl le_rfl)
          (fun m₁ m₂ hmod ⟨hs, hv⟩ => by
            constructor
            · rw [hmod _ (by rw [Finset.mem_Ico]; unfold frameSize; omega)]
              exact hs
            · rw [hmod _ (by rw [Finset.mem_Ico]; unfold frameSize; omega)]
              exact hv)
          (fun ht hd hz0 hzfp hzsp hmp hmk hms hmc hcc hfc hsc =>
            ih ht hd hz0 hzfp hzsp hmp hmk hms hmc hcc hfc hsc)
        have hfinal := hbranch₂.trans
          (Q := fun z => Modifies (Finset.Ico (fp + 2 + k * k) (fp + fastCutScratch k))
            x.mem z.mem ∧ z.regs zero = 0 ∧ z.regs fpReg = parentFp ∧ z.regs spReg = b)
          (f := fun z => z.regs retVal) (κ := fun r₂ => PMF.pure (min v₁ r₂))
          (T₂ := 24) (R₂ := 0) fun z ⟨hmod₂, ⟨hstg₂, hv₁⟩, hz0, hzfp, hzsp⟩ => by
            have hm2_p : z.mem fp = parentFp := by
              rw [hmod₂ _ (by rw [Finset.mem_Ico]; omega), hm1_p]
            have hm2_k : z.mem (fp + 1) = k := by
              rw [hmod₂ _ (by rw [Finset.mem_Ico]; omega), hm1_k]
            obtain ⟨zf, nf, hnf, hseg, hmem, hf0, hffp, hfsp, hret⟩ :=
              fastCutStep_stage2_seg hk7 hz0 hzfp hzsp rfl hm2_p hm2_k hstg₂ hv₁
                (hfit.of_le (by omega)) (hsp_fit.of_le (by omega))
            refine ⟨pure (zf, nf), hseg, .pure _ 0, ?_, ?_⟩
            · intro out hout
              cases OracleComp.eq_of_mem_supportWith_pure hout
              refine ⟨⟨?_, hf0, hffp, hfsp⟩, hnf⟩
              rw [hmem]
              exact modifies_trans_subset hmod₁ hmod₂ Finset.Subset.rfl Finset.Subset.rfl
            · simpa only [map_pure, ProbComp.eval_pure] using congrArg PMF.pure hret
        exact (hfinal.congr_law (PMF.bind_pure_comp _ _)).mono (fun _ h => h)
          (by dsimp only [t]; omega) (by dsimp only [t]; omega)
      have htotal := hfirst.trans (κ := fun a => branch.map (min a)) hsecond
      refine (htotal.congr_law (Lean.Karger.fastCutLaw_node hk7 _).symm).mono
        (fun _ h => h) ?_ ?_
      · rw [fastCutNodeTime_of_ge_seven hk7]
        dsimp only [t]
        omega
      · rw [fastCutNodeQueries_of_ge_seven hk7]
        dsimp only [t]
        omega
    · exact fastCutNode_base_law hk (by omega) h0 hfp hsp hm_p hm_k hmat hC hfit hsp_fit htot

/-- **Structural `LoopSegment` specification of recursive `FastCut` over depth budget `d`.** -/
theorem fastCutNode_spec {n w : ℕ} {W₀ : Fin n → Fin n → ℕ}
    (htot : Fits w (totalDoubledWeight W₀)) :
    ∀ (d : ℕ) {fp parentFp b k : ℕ} {W_k : Fin k → Fin k → ℕ} {part : Fin n → Fin k}
      {x : Data 24},
      2 ≤ k →
      fastCutDepth k ≤ d →
      x.regs zero = 0 →
      x.regs fpReg = fp →
      x.regs spReg = b + 1 →
      x.mem fp = parentFp →
      x.mem (fp + 1) = k →
      x.mem (fp + 2 + k * k) = 0 →
      HoldsMatrix x.mem (fp + 2) k W_k →
      IsContractionOf W₀ part W_k →
      Fits w (fp + fastCutScratch k) →
      Fits w (b + 1 + d) →
      ∃ m : ProbComp (Data 24 × ℕ),
        LoopSegment w (Cond.lt zero spReg) fastCutStep x m ∧
        m.IsQueryBounded (fastCutNodeQueries k) ∧
        (∀ z ∈ m.support,
          z.2 ≤ fastCutNodeTime k ∧
          Modifies (Finset.Ico (fp + 2 + k * k) (fp + fastCutScratch k)) x.mem z.1.mem ∧
          z.1.regs zero = 0 ∧
          z.1.regs fpReg = parentFp ∧
          z.1.regs spReg = b ∧
          ∃ C : Finset (Fin n), IsNonTrivialCut C ∧ z.1.regs retVal = cutWeight W₀ C) ∧
        (∀ B : Finset (Fin k),
          0 < minCut W₀ → IsNonTrivialCut B →
          cutWeight W₀ (pullbackCut part B) = minCut W₀ →
          (2 : ℝ≥0∞) / ((d + 30 : ℕ) : ℝ≥0∞) ≤
            m.eval.toOuterMeasure {z | z.1.regs retVal = minCut W₀}) := by
  intro d fp parentFp b k W_k part x hk hd h0 hfp hsp hm_p hm_k hm_stg hmat hC hfit hsp_fit
  obtain ⟨m, hm, hq, hsup, hlaw⟩ :=
    fastCutNode_law htot d hk hd h0 hfp hsp hm_p hm_k hm_stg hmat hC hfit hsp_fit
  refine ⟨m, hm, hq, ?_, ?_⟩
  · intro z hz
    rcases hsup z hz with ⟨⟨hmod, hz0, hzfp, hzsp⟩, ht⟩
    have hv : z.1.regs retVal ∈ (Lean.Karger.fastCutLaw k ⟨k, W_k⟩).support := by
      rw [← hlaw, ProbComp.eval_map, PMF.mem_support_map_iff]
      exact ⟨z, (ProbComp.support_eval m) ▸ hz, rfl⟩
    exact ⟨ht, hmod, hz0, hzfp, hzsp, Lean.Karger.exists_cut_of_mem_support_fastCutLaw hk hC hv⟩
  · intro B hmin hB hBmin
    have hprob := Lean.Karger.fastCutLaw_hit_prob_ge hmin d hk hd hC B hB hBmin
    rw [← hlaw, ProbComp.eval_map, PMF.toOuterMeasure_map_apply] at hprob
    exact hprob

/-- Root-frame setup before copying the input matrix `W` from `srcBase` into `fp₀ + 2`. -/
def fastCutRootSetup : Code .standard 24 := ram[
  zero ← #0;
  one ← #1;
  rem ← nOrig * nOrig;
  fpReg ← srcBase + rem;
  *fpReg ← zero;
  addr1 ← fpReg + one;
  *addr1 ← nOrig;
  uReg ← srcBase;
  wBase ← addr1 + one
]

/-- Root-frame stage/stack-pointer initialization after copying `W` into `fp₀ + 2`. -/
def fastCutRootFinish : Code .standard 24 := ram[
  zero ← #0;
  one ← #1;
  rem ← nOrig * nOrig;
  addr2 ← wBase + rem;
  *addr2 ← zero;
  spReg ← #1
]

/-- Single `FastCut` tree execution from `srcBase` and `nOrig`, writing `retVal` and preserving
`srcBase`, `nOrig`, `numTrials`, `trialIdx`, and `bestVal`. -/
def fastCutTree : Code .standard 24 := ram[
  ⟪fastCutRootSetup⟫;
  ⟪ksCopyCode⟫;
  ⟪fastCutRootFinish⟫;
  ⟪fastCutLoop⟫
]

/-- A complete native tree has exactly the recursive specification answer law. -/
theorem fastCutTree_law {n w sb : ℕ} {W : Fin n → Fin n → ℕ} {x : Data 24}
    (hn : 2 ≤ n) (hW : IsMultigraph W)
    (hsb : x.regs srcBase = sb) (hnOrig : x.regs nOrig = n)
    (hmat : HoldsMatrix x.mem sb n W)
    (hws_fit : Fits w (sb + 27 * (n * n)))
    (hsp_fit : Fits w (2 * Nat.log 2 n + 1))
    (htot : Fits w (totalDoubledWeight W)) :
    ExecRandLaw w fastCutTree x
      (fun y => Modifies (Finset.Ico (sb + n * n) (sb + 27 * (n * n))) x.mem y.mem ∧
        y.regs srcBase = sb ∧
        y.regs nOrig = n ∧
        y.regs numTrials = x.regs numTrials ∧
        y.regs trialIdx = x.regs trialIdx ∧
        y.regs bestVal = x.regs bestVal)
      (fastCutNodeTime n + 7 * (n * n) + 21) (fastCutNodeQueries n)
      (fun y => y.regs retVal) (Lean.Karger.fastCutLaw n ⟨n, W⟩) := by
  let fp₀ := sb + n * n
  let S_all := Finset.Ico fp₀ (sb + 27 * (n * n))
  have hscr_le : fastCutScratch n ≤ 26 * (n * n) := fastCutScratch_le hn
  have hfs_le : frameSize n ≤ fastCutScratch n := frameSize_le_fastCutScratch n
  have hnn_ge : 4 ≤ n * n := Nat.mul_le_mul hn hn
  have hfit_scr : Fits w (fp₀ + fastCutScratch n) := hws_fit.of_le (by dsimp only [fp₀]; omega)
  have hfit_fs : Fits w (fp₀ + frameSize n) := hfit_scr.of_le (by omega)
  have h1_fit : Fits w 1 := hfit_fs.of_le (by unfold frameSize; omega)
  have hstg_fit : Fits w (fp₀ + 2 + n * n) := hfit_fs.of_le (by unfold frameSize; omega)
  obtain ⟨x₃, e_pre, hx₃_0, hx₃_fp, hx₃_sp, hx₃_p, hx₃_k, hx₃_stg, hx₃_mat, hmod_pre⟩ : ∃ x₃,
      ExecWithin w ram[⟪fastCutRootSetup⟫; ⟪ksCopyCode⟫; ⟪fastCutRootFinish⟫]
        x x₃ (9 + (7 * (n * n) + 4) + 6) ∧
      x₃.regs zero = 0 ∧ x₃.regs fpReg = fp₀ ∧ x₃.regs spReg = 1 ∧
      x₃.mem fp₀ = 0 ∧ x₃.mem (fp₀ + 1) = n ∧ x₃.mem (fp₀ + 2 + n * n) = 0 ∧
      HoldsMatrix x₃.mem (fp₀ + 2) n W ∧ Modifies S_all x.mem x₃.mem := by
    have : Fits w (n * n) := hfit_fs.of_le (by unfold frameSize; omega)
    have : Fits w (fp₀ + 2) := hfit_fs.of_le (by unfold frameSize; omega)
    refine WP.exists_execWithin ?_
    unfold fastCutRootSetup
    wram_exec [hsb, hnOrig, show (fp₀ + 1) + 1 = fp₀ + 2 from rfl]
    have hx₁_src : HoldsMatrix (Function.update (Function.update x.mem fp₀ 0) (fp₀ + 1) n)
        sb n W := fun i j => by
      have hlt : sb + i.val * n + j.val < fp₀ := matAddr_lt_end (wb := sb) (le_refl n) i j
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hmat i j
    wram_call (ksCopyCode_exec (W := W) (by wram_simp) (by wram_simp; rfl)
      (by wram_simp) (by dsimp only [fp₀]; omega) h1_fit hstg_fit hx₁_src)
      with x₂ ⟨hmat_cp, hmod_cp, _, hwb₂, _, _, _, _, hhi₂⟩
    have hn_x₂ : x₂.regs nOrig = n := (hhi₂ nOrig (by decide)).trans (by wram_simp [hnOrig])
    have hfp_x₂ : x₂.regs fpReg = fp₀ := (hhi₂ fpReg (by decide)).trans (by wram_simp; rfl)
    unfold fastCutRootFinish
    wram_exec [hn_x₂, hwb₂]
    have hfp_in : fp₀ ∈ S_all := by rw [Finset.mem_Ico]; dsimp only [fp₀]; omega
    have hfp1_in : fp₀ + 1 ∈ S_all := by rw [Finset.mem_Ico]; dsimp only [fp₀]; omega
    have hstg_in : fp₀ + 2 + n * n ∈ S_all := by rw [Finset.mem_Ico]; dsimp only [fp₀]; omega
    refine ⟨by wram_simp, by wram_simp [hfp_x₂], by wram_simp, ?_, ?_, by wram_simp, ?_, ?_⟩
    · wram_simp
      simpa [show sb + n * n = fp₀ from rfl, Function.update_of_ne (by omega : fp₀ ≠ fp₀ + 1)]
        using hmod_cp fp₀ (by rw [Finset.mem_Ico]; omega)
    · wram_simp
      simpa [show sb + n * n = fp₀ from rfl]
        using hmod_cp (fp₀ + 1) (by rw [Finset.mem_Ico]; omega)
    · intro i j
      have hlt := matAddr_lt_end (wb := fp₀ + 2) (le_refl n) i j
      wram_simp
      exact hmat_cp i j
    · simp only [Data.set_mem, Data.write_mem]
      exact modifies_trans_subset
        (modifies_trans_subset
          (modifies_trans_subset (modifies_update_of_mem hfp_in x.mem 0)
            (modifies_update_of_mem hfp1_in _ n) Finset.Subset.rfl Finset.Subset.rfl)
          hmod_cp Finset.Subset.rfl
          (fun a ha => by rw [Finset.mem_Ico] at ha ⊢; dsimp only [fp₀] at *; omega))
        (modifies_update_of_mem hstg_in _ 0) Finset.Subset.rfl Finset.Subset.rfl
  have hloop : ExecRandLaw w fastCutLoop x₃
      (fun y => Modifies (Finset.Ico (fp₀ + 2 + n * n) (fp₀ + fastCutScratch n)) x₃.mem y.mem ∧
        y.regs zero = 0 ∧ y.regs fpReg = 0 ∧ y.regs spReg = 0)
      (fastCutNodeTime n + 2) (fastCutNodeQueries n)
      (fun y => y.regs retVal) (Lean.Karger.fastCutLaw n ⟨n, W⟩) :=
    (fastCutNode_law htot (2 * Nat.log 2 n) (b := 0) (parentFp := 0)
      hn (fastCutDepth_le_two_mul_log n) hx₃_0 hx₃_fp hx₃_sp hx₃_p hx₃_k hx₃_stg hx₃_mat
      (isContractionOf_id hW) hfit_scr
      (by simpa only [Nat.zero_add, Nat.add_comm 1] using hsp_fit)).finish
      fun _ ⟨_, hz0, _, hzsp⟩ => by simp [Cond.holds_lt, hz0, hzsp]
  have htree := ((((ExecRandLaw.foldr_seq_det [fastCutRootSetup, ksCopyCode] e_pre hloop
    |>.withPreserves (i := srcBase) (by decide))
    |>.withPreserves (i := nOrig) (by decide))
    |>.withPreserves (i := numTrials) (by decide))
    |>.withPreserves (i := trialIdx) (by decide))
    |>.withPreserves (i := bestVal) (by decide)
  refine htree.mono (fun y ⟨⟨⟨⟨⟨⟨hmod, _⟩, hsb_y⟩, hn_y⟩, hnt_y⟩, hti_y⟩, hbv_y⟩ =>
    ⟨modifies_trans_subset hmod_pre hmod Finset.Subset.rfl
      (fun a ha => by rw [Finset.mem_Ico] at ha ⊢; dsimp only [fp₀] at *; omega),
      hsb_y.trans hsb, hn_y.trans hnOrig, hnt_y, hti_y, hbv_y⟩) (by omega) le_rfl

theorem fastCutTree_spec {n w sb : ℕ} {W : Fin n → Fin n → ℕ} {x : Data 24}
    (hn : 2 ≤ n) (hW : IsMultigraph W)
    (hsb : x.regs srcBase = sb) (hnOrig : x.regs nOrig = n)
    (hmat : HoldsMatrix x.mem sb n W)
    (hws_fit : Fits w (sb + 27 * (n * n)))
    (hsp_fit : Fits w (2 * Nat.log 2 n + 1))
    (htot : Fits w (totalDoubledWeight W)) :
    ∃ m : ProbComp (Data 24 × ℕ),
      ExecRand w fastCutTree x m ∧
      m.IsQueryBounded (fastCutNodeQueries n) ∧
      (∀ z ∈ m.support,
        z.2 ≤ fastCutNodeTime n + 7 * (n * n) + 21 ∧
        Modifies (Finset.Ico (sb + n * n) (sb + 27 * (n * n))) x.mem z.1.mem ∧
        z.1.regs srcBase = sb ∧
        z.1.regs nOrig = n ∧
        z.1.regs numTrials = x.regs numTrials ∧
        z.1.regs trialIdx = x.regs trialIdx ∧
        z.1.regs bestVal = x.regs bestVal ∧
        ∃ C : Finset (Fin n), IsNonTrivialCut C ∧ z.1.regs retVal = cutWeight W C) ∧
      (0 < minCut W →
        (1 : ℝ≥0∞) / ((Nat.log 2 n + 15 : ℕ) : ℝ≥0∞) ≤
          m.eval.toOuterMeasure {z | z.1.regs retVal = minCut W}) := by
  obtain ⟨m, hm, hq, hsup, hlaw⟩ := fastCutTree_law hn hW hsb hnOrig hmat hws_fit hsp_fit htot
  refine ⟨m, hm, hq, ?_, ?_⟩
  · intro z hz
    rcases hsup z hz with ⟨⟨hmod, hzsb, hzn, hznt, hzti, hzbv⟩, ht⟩
    have hv : z.1.regs retVal ∈ (Lean.Karger.fastCutLaw n ⟨n, W⟩).support := by
      rw [← hlaw, ProbComp.eval_map, PMF.mem_support_map_iff]
      exact ⟨z, (ProbComp.support_eval m) ▸ hz, rfl⟩
    exact ⟨ht, hmod, hzsb, hzn, hznt, hzti, hzbv,
      Lean.Karger.exists_cut_of_mem_support_fastCutLaw hn (isContractionOf_id hW) hv⟩
  · intro hmin
    have hprob := Lean.Karger.fastCutLaw_root_hit_prob_ge hn hW hmin
    rw [← hlaw, ProbComp.eval_map, PMF.toOuterMeasure_map_apply] at hprob
    exact hprob

end FrameMachine

/-! ### Endpoint 1: Single-tree recursive `FastCut` (`r = 24`) -/

section FastCutSingle

open KSReg

/-- Setup for `fastCutCode` on `n :: flattenMatrix W`: load `n = mem[1]` and set `srcBase = 2`. -/
def fastCutSetup : Code .standard 24 := ram[
  one ← #1;
  nOrig ← *one;
  srcBase ← #2
]

/-- Structured 24-register single-tree Karger–Stein `FastCut` code on `n :: flattenMatrix W`. -/
def fastCutCode : Code .standard 24 := ram[
  ⟪fastCutSetup⟫;
  ⟪fastCutTree⟫
]

/-- Compiled 24-register single-tree Karger–Stein `FastCut` program. -/
def fastCutProgram : Program .standard 24 :=
  fastCutCode.program retVal

/-- Worst-case `O(n ^ 2 log n)` instruction bound `2500 * n ^ 2 * (Nat.log 2 n + 2)` for
`fastCutProgram`. -/
def fastCutTime (n : ℕ) : ℕ :=
  2500 * n ^ 2 * (Nat.log 2 n + 2)

private theorem fits_sp_of_ws {n w : ℕ} (hn : 2 ≤ n) (hws : Fits w (2 + 27 * (n * n))) :
    Fits w (2 * Nat.log 2 n + 1) := by
  have hlog : Nat.log 2 n < n := Nat.log_lt_self 2 (by omega)
  have hmul : n ≤ n * n := Nat.le_mul_self n
  exact hws.of_le (by omega)

private theorem fastCutTime_bound {n : ℕ} (hn : 2 ≤ n) :
    3 + (fastCutNodeTime n + 7 * (n * n) + 21) + 1 ≤ fastCutTime n := by
  unfold fastCutTime
  have hnt := fastCutNodeTime_le hn
  have hnn : n * n = n ^ 2 := (sq n).symm
  rw [hnn]
  have hn2 : 4 ≤ n ^ 2 := by nlinarith
  have hlg : 2 ≤ Nat.log 2 n + 2 := by omega
  have hov : 7 * n ^ 2 + 25 ≤ 100 * n ^ 2 * (Nat.log 2 n + 2) := by nlinarith
  linarith

private theorem fastCutSetup_exec {w n : ℕ} {W : Fin n → Fin n → ℕ}
    (hn : 2 ≤ n) (hw : logWidth 4 n ≤ w) :
    ∃ y : Data 24, Exec w fastCutSetup (Data.init (n :: flattenMatrix W)) y 3 ∧
      y.mem = (Data.init (r := 24) (n :: flattenMatrix W)).mem ∧
      y.regs srcBase = 2 ∧
      y.regs nOrig = n := by
  have hws := fits_fastCutWorkspace_of_logWidth_four hn hw
  have hm1 : (Data.init (r := 24) (n :: flattenMatrix W)).mem 1 = n := rfl
  unfold fastCutSetup
  wram_exec [hm1]
  exact ⟨rfl, by wram_simp⟩

/-- The single-tree code observes the recursive answer law, including the charged input setup. -/
theorem fastCutCode_law {n w : ℕ} {W : Fin n → Fin n → ℕ}
    (hn : 2 ≤ n) (hW : IsMultigraph W)
    (hw : logWidth 4 n ≤ w) (htot : Fits w (totalDoubledWeight W)) :
    ExecRandLaw w fastCutCode (Data.init (n :: flattenMatrix W))
      (fun y => Modifies (Finset.Ico (2 + n * n) (2 + 27 * (n * n)))
        (Data.init (r := 24) (n :: flattenMatrix W)).mem y.mem)
      (3 + (fastCutNodeTime n + 7 * (n * n) + 21)) (fastCutNodeQueries n)
      (fun y => y.regs retVal) (Lean.Karger.fastCutLaw n ⟨n, W⟩) := by
  have hws := fits_fastCutWorkspace_of_logWidth_four hn hw
  have hsp := fits_sp_of_ws hn hws
  obtain ⟨y_s, e_s, hm_s, hsb_s, hn_s⟩ := fastCutSetup_exec (W := W) hn hw
  have htree := fastCutTree_law hn hW hsb_s hn_s
    (hm_s ▸ holdsMatrix_init_single W) hws hsp htot
  exact (ExecRandLaw.seq_det e_s.within htree).mono
    (fun _ h => hm_s ▸ h.1) le_rfl le_rfl

/-- Structured `ProbComp` specification of `fastCutCode`. -/
theorem fastCutCode_spec {n w : ℕ} {W : Fin n → Fin n → ℕ}
    (hn : 2 ≤ n) (hW : IsMultigraph W)
    (hw : logWidth 4 n ≤ w) (htot : Fits w (totalDoubledWeight W)) :
    ∃ m : ProbComp (Data 24 × ℕ),
      ExecRand w fastCutCode (Data.init (n :: flattenMatrix W)) m ∧
      m.IsQueryBounded (fastCutNodeQueries n) ∧
      (∀ z ∈ m.support,
        z.2 + 1 ≤ fastCutTime n ∧
        Modifies (Finset.Ico (2 + n * n) (2 + 27 * (n * n)))
          (Data.init (r := 24) (n :: flattenMatrix W)).mem z.1.mem ∧
        ∃ C : Finset (Fin n), IsNonTrivialCut C ∧ z.1.regs retVal = cutWeight W C) ∧
      (0 < minCut W →
        (1 : ℝ≥0∞) / ((Nat.log 2 n + 15 : ℕ) : ℝ≥0∞) ≤
          m.eval.toOuterMeasure {z | z.1.regs retVal = minCut W}) := by
  obtain ⟨m, hm, hq, hsup, hlaw⟩ := fastCutCode_law hn hW hw htot
  have hbound := fastCutTime_bound hn
  refine ⟨m, hm, hq, ?_, ?_⟩
  · intro z hz
    have hv : z.1.regs retVal ∈ (Lean.Karger.fastCutLaw n ⟨n, W⟩).support := by
      rw [← hlaw, ProbComp.eval_map, PMF.mem_support_map_iff]
      exact ⟨z, (ProbComp.support_eval m) ▸ hz, rfl⟩
    exact ⟨by have := (hsup z hz).2; omega, (hsup z hz).1,
      Lean.Karger.exists_cut_of_mem_support_fastCutLaw hn (isContractionOf_id hW) hv⟩
  · intro hmin
    have hprob := Lean.Karger.fastCutLaw_root_hit_prob_ge hn hW hmin
    rw [← hlaw, ProbComp.eval_map, PMF.toOuterMeasure_map_apply] at hprob
    exact hprob

/-- **Single-tree Karger–Stein `FastCut` specification (`fastCutProgram`, `[KargerStein1996]`,
Section 4, Figure 6 and Lemmas 4.1–4.3; paraphrase).**
At word size `w ≥ logWidth 4 n` when `2 ≤ n` and `totalDoubledWeight W < 2 ^ w`:
1. `fastCutProgram` halts within `fastCutTime n = 2500 * n ^ 2 * (Nat.log 2 n + 2)` steps;
2. executes at most `fastCutNodeQueries n` (`≤ 6 * (n * n)`) `rand` calls;
3. on every supported branch, outputs `cutWeight W C ≥ minCut W` for a genuine non-trivial cut `C`
   of `W` while modifying memory only in `[2 + n * n, 2 + 27 * (n * n))`;
4. when `0 < minCut W` (excluded only for proof convenience), outputs `minCut W` with probability at
   least `1 / (Nat.log 2 n + 15)`. -/
theorem fastCutProgram_spec {n w : ℕ} {W : Fin n → Fin n → ℕ}
    (hn : 2 ≤ n) (hW : IsMultigraph W)
    (hw : logWidth 4 n ≤ w) (htot : Fits w (totalDoubledWeight W)) :
    let input := n :: flattenMatrix W
    RandHaltsWithin w fastCutProgram (.init input) (fastCutTime n) ∧
    RandCallsBounded w fastCutProgram (.init input) (fastCutTime n) (fastCutNodeQueries n) ∧
    (∀ cfg ∈ (runRand w fastCutProgram (fastCutTime n) (.running (.init input))).support,
      ∃ (y : Data 24) (C : Finset (Fin n)),
        cfg = .halted (cutWeight W C) y ∧
        y.Bounded w ∧
        IsNonTrivialCut C ∧
        minCut W ≤ cutWeight W C ∧
        Modifies (Finset.Ico (2 + n * n) (2 + 27 * (n * n)))
          (Data.init (r := 24) input).mem y.mem) ∧
    (0 < minCut W →
      (1 : ℝ≥0∞) / ((Nat.log 2 n + 15 : ℕ) : ℝ≥0∞) ≤
        (evalRand w fastCutProgram (fastCutTime n) (.init input)).toOuterMeasure
          {cfg | ∃ y, cfg = .halted (minCut W) y}) := by
  intro input
  obtain ⟨hhalt, hcalls, hpost, hhit, -⟩ :=
    program_of_law (fastCutCode_law hn hW hw htot) (fastCutTime_bound hn)
      (inputFits_fastCut hn hw htot) fun _ hv =>
        Lean.Karger.exists_cut_of_mem_support_fastCutLaw hn (isContractionOf_id hW) hv
  exact ⟨hhalt, hcalls, hpost, fun hmin =>
    (Lean.Karger.fastCutLaw_root_hit_prob_ge hn hW hmin).trans hhit⟩

end FastCutSingle

/-! ### Endpoint 2: Amplified `O(n ^ 2 log ^ 3 n)` high-probability `FastCut` (`r = 24`) -/

section FastCutHighProb

open KSReg

/-- Body of `ksLogLoop`: halve `rem` via right-shift by `1` and increment `idx`. -/
def ksLogStep : Code .standard 24 := ram[
  rem ← rem >>> one;
  idx ← idx + one
]

/-- Loop computing `idx = Nat.log 2 n` from `rem = n` (`n ≥ 1`), `idx = 0`, `one = 1`. -/
def ksLogLoop : Code .standard 24 := ram[
  while one < rem do [ ⟪ksLogStep⟫ ]
]

/-- Setup for `fastCutHighProbCode` on `n :: flattenMatrix W`: load `n = mem[1]`, compute
`numTrials = fastCutTrials n = (Nat.log 2 n + 15) * (Nat.log 2 n + 2)` without subtraction or
division, and initialize `srcBase = 2`, `trialIdx = 0`, `bestVal = 0`. -/
def fastCutHighProbSetup : Code .standard 24 := ram[
  one ← #1;
  nOrig ← *one;
  rem ← nOrig;
  idx ← #0;
  ⟪ksLogLoop⟫;
  val1 ← #15;
  val1 ← idx + val1;
  val2 ← #2;
  val2 ← idx + val2;
  numTrials ← val1 * val2;
  srcBase ← #2;
  trialIdx ← #0;
  bestVal ← #0
]

/-- Postprocessing after each `fastCutTree` trial: update `bestVal` with `retVal` (unconditionally
on trial `0` and via minimum thereafter) and increment `trialIdx`. -/
def fastCutAmpPost : Code .standard 24 := ram[
  zero ← #0;
  one ← #1;
  if trialIdx = zero then [
    bestVal ← retVal
  ] else [
    if retVal < bestVal then [
      bestVal ← retVal
    ] else [
      zero ← #0
    ]
  ];
  trialIdx ← trialIdx + one
]

/-- Body of one outer `FastCut` amplification trial. -/
def fastCutAmpBody : Code .standard 24 := ram[
  ⟪fastCutTree⟫;
  ⟪fastCutAmpPost⟫
]

/-- Outer amplification loop running `numTrials` independent `FastCut` trees. -/
def fastCutAmpLoop : Code .standard 24 := ram[
  while trialIdx < numTrials do [ ⟪fastCutAmpBody⟫ ]
]

/-- Structured 24-register `O(n ^ 2 log ^ 3 n)` high-probability Karger–Stein program on
`n :: flattenMatrix W`. -/
def fastCutHighProbCode : Code .standard 24 := ram[
  ⟪fastCutHighProbSetup⟫;
  ⟪fastCutAmpLoop⟫
]

/-- Compiled 24-register `O(n ^ 2 log ^ 3 n)` high-probability Karger–Stein program. -/
def fastCutHighProbProgram : Program .standard 24 :=
  fastCutHighProbCode.program bestVal

/-- Worst-case instruction bound `2600 * n ^ 2 * (Nat.log 2 n + 15) * (Nat.log 2 n + 2) ^ 2`
(`O(n ^ 2 log ^ 3 n)`) for `fastCutHighProbProgram`. -/
def fastCutHighProbTime (n : ℕ) : ℕ :=
  2600 * n ^ 2 * (Nat.log 2 n + 15) * (Nat.log 2 n + 2) ^ 2

/-- Loop invariant for `fastCutAmpLoop` at `trialIdx = i ≤ R`. -/
structure KSAmpInv (sb n R i : ℕ) (W : Fin n → Fin n → ℕ) (mem₀ : ℕ → ℕ)
    (x : Data 24) : Prop where
  regs_srcBase : x.regs srcBase = sb
  regs_nOrig : x.regs nOrig = n
  regs_numTrials : x.regs numTrials = R
  regs_trialIdx : x.regs trialIdx = i
  src_matrix : HoldsMatrix x.mem sb n W
  modifies_ws : Modifies (Finset.Ico (sb + n * n) (sb + 27 * (n * n))) mem₀ x.mem
  best_cut : 0 < i → ∃ C : Finset (Fin n), IsNonTrivialCut C ∧ x.regs bestVal = cutWeight W C

private theorem ksLogLoop_exec {w n : ℕ} {x : Data 24} (hn : 1 ≤ n)
    (hone : x.regs one = 1) (hrem : x.regs rem = n) (hidx : x.regs idx = 0)
    (hnOrig : x.regs nOrig = n)
    (hn_fit : Fits w n) (hlg_fit : Fits w (Nat.log 2 n)) :
    ∃ y : Data 24, ExecWithin w ksLogLoop x y (4 * Nat.log 2 n + 2) ∧
      y.mem = x.mem ∧
      y.regs one = 1 ∧
      y.regs nOrig = n ∧
      y.regs idx = Nat.log 2 n := by
  obtain ⟨y, he, hm, hidx', hframe⟩ := NatLog.shiftLoop_exec (one := one) (rem := rem)
    (idx := idx) (by decide) (by decide) (by decide) hn hone hrem hidx hn_fit hlg_fit
  exact ⟨y, he, hm, (hframe one (by decide) (by decide)).trans hone,
    (hframe nOrig (by decide) (by decide)).trans hnOrig, hidx'⟩

private theorem fastCutHighProbSetup_exec {w n : ℕ} {W : Fin n → Fin n → ℕ}
    (hn : 2 ≤ n) (hw : logWidth 4 n ≤ w) :
    ∃ y : Data 24,
      ExecWithin w fastCutHighProbSetup (Data.init (n :: flattenMatrix W)) y
        (4 * Nat.log 2 n + 14) ∧
      y.mem = (Data.init (r := 24) (n :: flattenMatrix W)).mem ∧
      y.regs srcBase = 2 ∧
      y.regs nOrig = n ∧
      y.regs numTrials = fastCutTrials n ∧
      y.regs trialIdx = 0 ∧
      y.regs bestVal = 0 := by
  have hws := fits_fastCutWorkspace_of_logWidth_four hn hw
  have hhp_fit := fits_fastCutTrials_of_logWidth_four hn hw
  have hnn : 4 ≤ n * n := Nat.mul_le_mul hn hn
  have : Fits w 15 := hws.of_le (by omega)
  have hn_fit : Fits w n := hws.of_le (by have := Nat.le_mul_self n; omega)
  have hlg_fit : Fits w (Nat.log 2 n) := hhp_fit.of_le (by unfold fastCutTrials; nlinarith)
  have : Fits w (Nat.log 2 n + 15) := hhp_fit.of_le (by unfold fastCutTrials; nlinarith)
  have : Fits w (Nat.log 2 n + 2) := hhp_fit.of_le (by unfold fastCutTrials; nlinarith)
  have hhp_eq : (Nat.log 2 n + 15) * (Nat.log 2 n + 2) = fastCutTrials n := rfl
  have hm1 : (Data.init (r := 24) (n :: flattenMatrix W)).mem 1 = n := rfl
  unfold fastCutHighProbSetup
  wram_exec [hm1]
  wram_call (ksLogLoop_exec (by omega) (by wram_simp) (by wram_simp) (by wram_simp) (by wram_simp)
    hn_fit hlg_fit) with s₅ ⟨hm5, _, hn5, hidx5⟩
  wram_exec [hn5, hidx5, hhp_eq]
  exact ⟨hm5, by wram_simp [hn5]⟩

private theorem fastCutAmpPost_exec {w i R : ℕ} {x : Data 24}
    (hti : x.regs trialIdx = i) (hiR : i < R)
    (h1 : Fits w 1) (hR_fit : Fits w R) :
    ∃ y : Data 24, ExecWithin w fastCutAmpPost x y 8 ∧
      y.mem = x.mem ∧
      y.regs srcBase = x.regs srcBase ∧
      y.regs nOrig = x.regs nOrig ∧
      y.regs numTrials = x.regs numTrials ∧
      y.regs trialIdx = i + 1 ∧
      y.regs bestVal =
        (if i = 0 then x.regs retVal else min (x.regs retVal) (x.regs bestVal)) := by
  have hi1_fit : Fits w (i + 1) := hR_fit.of_le (by omega)
  unfold fastCutAmpPost
  wram_exec -split
  wram_call (minUpdate_exec (by decide) (by wram_simp)) with s₂ ⟨hm2, hbv2, hfr⟩
  wram_exec [hfr one (by decide), hfr trialIdx (by decide), hti]
  refine ⟨hm2, ?_, ?_, ?_, by wram_simp, ?_⟩
  · wram_simp [hfr srcBase (by decide)]
  · wram_simp [hfr nOrig (by decide)]
  · wram_simp [hfr numTrials (by decide)]
  · wram_simp [hbv2, hti]

private theorem ksAmpTrial_step_bound {n t_tree n_p : ℕ} (hn : 2 ≤ n)
    (htree : t_tree ≤ fastCutNodeTime n + 7 * (n * n) + 21) (hp : n_p ≤ 8) :
    t_tree + n_p + 2 ≤ 2500 * n ^ 2 * (Nat.log 2 n + 2) := by
  have hnt := fastCutNodeTime_le hn
  have hnn : n * n = n ^ 2 := (sq n).symm
  rw [hnn] at htree
  have hn2 : 4 ≤ n ^ 2 := by nlinarith
  have hlg : 2 ≤ Nat.log 2 n + 2 := by omega
  have hov : 7 * n ^ 2 + 31 ≤ 100 * n ^ 2 * (Nat.log 2 n + 2) := by nlinarith
  linarith

/-- One native amplification trial observes a fresh recursive answer and updates the minimum. -/
private theorem fastCutAmpBody_law {w sb n R i : ℕ} {W : Fin n → Fin n → ℕ} {mem₀ : ℕ → ℕ}
    {x : Data 24}
    (hn : 2 ≤ n) (hW : IsMultigraph W) (hiR : i < R)
    (h1 : Fits w 1) (hws_fit : Fits w (sb + 27 * (n * n)))
    (hsp_fit : Fits w (2 * Nat.log 2 n + 1))
    (hR_fit : Fits w R) (htot : Fits w (totalDoubledWeight W))
    (hinv : KSAmpInv sb n R i W mem₀ x) :
    ExecRandLaw w fastCutAmpBody x (KSAmpInv sb n R (i + 1) W mem₀)
      (fastCutNodeTime n + 7 * (n * n) + 21 + 8) (6 * (n * n))
      (fun y => y.regs bestVal)
      ((Lean.Karger.fastCutLaw n ⟨n, W⟩).map
        fun v => if i = 0 then v else min v (x.regs bestVal)) := by
  have htree := (fastCutTree_law hn hW hinv.regs_srcBase hinv.regs_nOrig hinv.src_matrix
    hws_fit hsp_fit htot).withSupport
  have hrun := ExecRandLaw.seq htree
    (κ := fun v => PMF.pure (if i = 0 then v else min v (x.regs bestVal)))
    fun d ⟨⟨hmod₀, hsb₀, hn₀, hnt₀, hti₀, hbv₀⟩, hv⟩ => by
      obtain ⟨C_new, hC_nt, hrv₀⟩ :=
        Lean.Karger.exists_cut_of_mem_support_fastCutLaw hn (isContractionOf_id hW) hv
      obtain ⟨y, e_p, hym, hsb_y, hn_y, hnt_y, hti_y, hbv_y⟩ :=
        fastCutAmpPost_exec (hti₀.trans hinv.regs_trialIdx) hiR h1 hR_fit
      have hinv' : KSAmpInv sb n R (i + 1) W mem₀ y := by
        refine ⟨hsb_y.trans hsb₀, hn_y.trans hn₀, hnt_y.trans (hnt₀.trans hinv.regs_numTrials),
          hti_y, fun u v => ?_, hym ▸ modifies_trans_subset hinv.modifies_ws hmod₀
            Finset.Subset.rfl Finset.Subset.rfl, fun _ => ?_⟩
        · have hlt := matAddr_lt_end (wb := sb) (le_refl n) u v
          rw [hym, hmod₀ _ (by rw [Finset.mem_Ico]; omega)]
          exact hinv.src_matrix u v
        · by_cases hi0 : i = 0
          · exact ⟨C_new, hC_nt, by simp [hbv_y, hi0, hrv₀]⟩
          · obtain ⟨C_old, hC_old_nt, hbv_old⟩ := hinv.best_cut (Nat.pos_of_ne_zero hi0)
            simp only [hbv_y, hi0, ↓reduceIte, hrv₀, hbv₀, hbv_old]
            rcases min_cases (cutWeight W C_new) (cutWeight W C_old) with ⟨hmin, _⟩ | ⟨hmin, _⟩
            · exact ⟨C_new, hC_nt, hmin⟩
            · exact ⟨C_old, hC_old_nt, hmin⟩
      exact (ExecRandLaw.of_execWithin (f := fun y => y.regs bestVal) e_p hinv').congr_law
        (by rw [hbv_y, hbv₀])
  exact (hrun.congr_law (PMF.bind_pure_comp _ _)).mono (fun _ h => h) le_rfl
    (by simpa using fastCutNodeQueries_le hn)

theorem fastCutAmpBody_spec {w sb n R i : ℕ} {W : Fin n → Fin n → ℕ} {mem₀ : ℕ → ℕ} {x : Data 24}
    (hn : 2 ≤ n) (hW : IsMultigraph W) (hiR : i < R)
    (h1 : Fits w 1) (hws_fit : Fits w (sb + 27 * (n * n)))
    (hsp_fit : Fits w (2 * Nat.log 2 n + 1))
    (hR_fit : Fits w R) (htot : Fits w (totalDoubledWeight W))
    (hinv : KSAmpInv sb n R i W mem₀ x) :
    ∃ m : ProbComp (Data 24 × ℕ),
      ExecRand w fastCutAmpBody x m ∧
      m.IsQueryBounded (6 * (n * n)) ∧
      (∀ z ∈ m.support,
        z.2 + 2 ≤ 2500 * n ^ 2 * (Nat.log 2 n + 2) ∧
        KSAmpInv sb n R (i + 1) W mem₀ z.1 ∧
        (0 < i → x.regs bestVal = minCut W → z.1.regs bestVal = minCut W)) ∧
      (0 < minCut W →
        m.eval.toOuterMeasure {z | z.1.regs bestVal ≠ minCut W} ≤
          (1 : ℝ≥0∞) - (1 : ℝ≥0∞) / ((Nat.log 2 n + 15 : ℕ) : ℝ≥0∞)) := by
  obtain ⟨m, hm, hq, hsup, hlaw⟩ :=
    fastCutAmpBody_law hn hW hiR h1 hws_fit hsp_fit hR_fit htot hinv
  have hbound := ksAmpTrial_step_bound hn le_rfl le_rfl
  refine ⟨m, hm, hq, ?_, ?_⟩
  · intro z hz
    refine ⟨by have := (hsup z hz).2; omega, (hsup z hz).1, ?_⟩
    intro hi hb
    have hv : z.1.regs bestVal ∈ ((Lean.Karger.fastCutLaw n ⟨n, W⟩).map
        fun v => if i = 0 then v else min v (x.regs bestVal)).support := by
      rw [← hlaw, ProbComp.eval_map, PMF.mem_support_map_iff]
      exact ⟨z, (ProbComp.support_eval m) ▸ hz, rfl⟩
    obtain ⟨v, hv, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hv
    rw [← heq]
    simp only [show i ≠ 0 by omega, ↓reduceIte, hb,
      min_eq_right (Lean.Karger.minCut_le_of_mem_support_fastCutLaw hn (isContractionOf_id hW) hv)]
  · intro hmin
    have hprob := Lean.Karger.fastCutLaw_update_failure_le hn hW hmin i (x.regs bestVal)
      (fun hi => by
        obtain ⟨C, hC, heq⟩ := hinv.best_cut hi
        rw [heq]
        exact minCut_le_cutWeight W hC)
    rw [← hlaw, ProbComp.eval_map, PMF.toOuterMeasure_map_apply] at hprob
    exact hprob

/-- The native loop has the law of independent trials of the existing amplification client.
The positive total trial count excludes the empty-client convention at an arbitrary initial word. -/
theorem fastCutAmpLoop_law {w sb n R : ℕ} {W : Fin n → Fin n → ℕ} {mem₀ : ℕ → ℕ}
    (hR : 1 ≤ R) (hn : 2 ≤ n) (hW : IsMultigraph W)
    (h1 : Fits w 1) (hws_fit : Fits w (sb + 27 * (n * n)))
    (hsp_fit : Fits w (2 * Nat.log 2 n + 1))
    (hR_fit : Fits w R) (htot : Fits w (totalDoubledWeight W)) :
    ∀ (remaining i : ℕ) (x : Data 24), i + remaining = R → KSAmpInv sb n R i W mem₀ x →
      ExecRandLaw w fastCutAmpLoop x (KSAmpInv sb n R R W mem₀)
        (remaining * (2500 * n ^ 2 * (Nat.log 2 n + 2)) + 2)
        (remaining * (6 * (n * n))) (fun y => y.regs bestVal)
        (OracleComp.evalWith (fun _ => Lean.Karger.fastCutLaw n ⟨n, W⟩)
          (if i = 0 then Lean.Karger.minRuns remaining
            else OracleComp.iterate remaining Lean.Karger.minStep (x.regs bestVal))) := by
  unfold fastCutAmpLoop
  exact minRunsLoop_law hR (ksAmpTrial_step_bound hn le_rfl le_rfl) (fun _ _ h => h.regs_trialIdx)
    (fun _ _ h => h.regs_numTrials)
    fun _ _ hi h => fastCutAmpBody_law hn hW hi h1 hws_fit hsp_fit hR_fit htot h


private theorem fastCutHighProbTime_bound {n : ℕ} (hn : 2 ≤ n) :
    (4 * Nat.log 2 n + 14) +
        (fastCutTrials n * (2500 * n ^ 2 * (Nat.log 2 n + 2)) + 2) + 1 ≤
      fastCutHighProbTime n := by
  unfold fastCutHighProbTime fastCutTrials
  let L := Nat.log 2 n
  change (4 * L + 14) + (((L + 15) * (L + 2)) * (2500 * n ^ 2 * (L + 2)) + 2) + 1 ≤
    2600 * n ^ 2 * (L + 15) * (L + 2) ^ 2
  let P := n ^ 2 * (L + 2) ^ 2
  have hn2 : 4 ≤ n ^ 2 := by nlinarith
  have hL2 : 4 ≤ (L + 2) ^ 2 := by rw [sq]; nlinarith
  have hP : 16 ≤ P := by dsimp only [P]; nlinarith
  have hL : 4 * L + 17 ≤ 100 * P * (L + 15) := by nlinarith
  have hp_eq : 100 * P * (L + 15) = 100 * n ^ 2 * (L + 15) * (L + 2) ^ 2 := by
    dsimp only [P]; ring
  have hmul : ((L + 15) * (L + 2)) * (2500 * n ^ 2 * (L + 2)) =
      2500 * n ^ 2 * (L + 15) * (L + 2) ^ 2 := by ring
  linarith

/-- The full native high-probability code observes the existing independent-trial law, paying for
the original setup, every loop-control instruction and the same random-call budget. -/
theorem fastCutHighProbCode_law {n w : ℕ} {W : Fin n → Fin n → ℕ}
    (hn : 2 ≤ n) (hW : IsMultigraph W)
    (hw : logWidth 4 n ≤ w) (htot : Fits w (totalDoubledWeight W)) :
    ExecRandLaw w fastCutHighProbCode (Data.init (n :: flattenMatrix W))
      (fun y => Modifies (Finset.Ico (2 + n * n) (2 + 27 * (n * n)))
        (Data.init (r := 24) (n :: flattenMatrix W)).mem y.mem)
      ((4 * Nat.log 2 n + 14) +
        (fastCutTrials n * (2500 * n ^ 2 * (Nat.log 2 n + 2)) + 2))
      (fastCutTrials n * (6 * (n * n))) (fun y => y.regs bestVal)
      (Lean.Karger.fastCutHighProbLaw n ⟨n, W⟩) := by
  have hws := fits_fastCutWorkspace_of_logWidth_four hn hw
  have hsp := fits_sp_of_ws hn hws
  have h1 : Fits w 1 := hws.of_le (by omega)
  have hhp_fit := fits_fastCutTrials_of_logWidth_four hn hw
  obtain ⟨y_s, ⟨n_s, hn_s, e_s⟩, hm_s, hsb_s, hn_s_r, hnt_s, hti_s, _⟩ :=
    fastCutHighProbSetup_exec (W := W) hn hw
  have hinv₀ : KSAmpInv 2 n (fastCutTrials n) 0 W
      (Data.init (r := 24) (n :: flattenMatrix W)).mem y_s :=
    ⟨hsb_s, hn_s_r, hnt_s, hti_s, hm_s ▸ holdsMatrix_init_single W,
      hm_s ▸ Modifies.refl _ _, fun h0 => absurd h0 (by omega)⟩
  have hloop := fastCutAmpLoop_law (fastCutTrials_pos n) hn hW h1 hws hsp hhp_fit htot
    (fastCutTrials n) 0 y_s (Nat.zero_add _) hinv₀
  rw [ite_eq_left rfl] at hloop
  exact (ExecRandLaw.seq_det ⟨n_s, hn_s, e_s⟩ hloop).mono
    (fun _ h => h.modifies_ws) le_rfl le_rfl

/-- Structured `ProbComp` specification of `fastCutHighProbCode`. -/
theorem fastCutHighProbCode_spec {n w : ℕ} {W : Fin n → Fin n → ℕ}
    (hn : 2 ≤ n) (hW : IsMultigraph W)
    (hw : logWidth 4 n ≤ w) (htot : Fits w (totalDoubledWeight W)) :
    ∃ m : ProbComp (Data 24 × ℕ),
      ExecRand w fastCutHighProbCode (Data.init (n :: flattenMatrix W)) m ∧
      m.IsQueryBounded (fastCutTrials n * (6 * (n * n))) ∧
      (∀ z ∈ m.support,
        z.2 + 1 ≤ fastCutHighProbTime n ∧
        Modifies (Finset.Ico (2 + n * n) (2 + 27 * (n * n)))
          (Data.init (r := 24) (n :: flattenMatrix W)).mem z.1.mem ∧
        ∃ C : Finset (Fin n), IsNonTrivialCut C ∧ z.1.regs bestVal = cutWeight W C) ∧
      (0 < minCut W →
        m.eval.toOuterMeasure {z | z.1.regs bestVal ≠ minCut W} ≤
          (1 : ℝ≥0∞) / ((2 * n : ℕ) : ℝ≥0∞)) := by
  obtain ⟨m, hm, hq, hsup, hlaw⟩ := fastCutHighProbCode_law hn hW hw htot
  have hbound := fastCutHighProbTime_bound hn
  refine ⟨m, hm, hq, ?_, ?_⟩
  · intro z hz
    have hv : z.1.regs bestVal ∈ (Lean.Karger.fastCutHighProbLaw n ⟨n, W⟩).support := by
      rw [← hlaw, ProbComp.eval_map, PMF.mem_support_map_iff]
      exact ⟨z, (ProbComp.support_eval m) ▸ hz, rfl⟩
    exact ⟨by have := (hsup z hz).2; omega, (hsup z hz).1,
      Lean.Karger.exists_cut_of_mem_support_fastCutHighProbLaw hn hW hv⟩
  · intro hmin
    have hprob := Lean.Karger.fastCutHighProbLaw_failure_le hn hW hmin
    rw [← hlaw, ProbComp.eval_map, PMF.toOuterMeasure_map_apply] at hprob
    exact hprob

/-- **Amplified `O(n ^ 2 log ^ 3 n)` high-probability Karger–Stein (`fastCutHighProbProgram`,
the minimum-cut-value part of `[KargerStein1996]`, Section 4, Theorem 4.4; paraphrase).**
At word size `w ≥ logWidth 4 n` when `2 ≤ n` and `totalDoubledWeight W < 2 ^ w`:
1. `fastCutHighProbProgram` halts within
   `fastCutHighProbTime n = 2600 * n ^ 2 * (Nat.log 2 n + 15) * (Nat.log 2 n + 2) ^ 2` steps;
2. executes at most `fastCutTrials n * (6 * (n * n))` `rand` calls;
3. on every supported branch, outputs `cutWeight W C ≥ minCut W` for a genuine non-trivial cut `C`
   of `W` while modifying memory only in `[2 + n * n, 2 + 27 * (n * n))`;
4. when `0 < minCut W` (excluded only for proof convenience), misses `minCut W` with probability at
   most `1 / (2 * n)`. -/
theorem fastCutHighProbProgram_spec {n w : ℕ} {W : Fin n → Fin n → ℕ}
    (hn : 2 ≤ n) (hW : IsMultigraph W)
    (hw : logWidth 4 n ≤ w) (htot : Fits w (totalDoubledWeight W)) :
    let input := n :: flattenMatrix W
    RandHaltsWithin w fastCutHighProbProgram (.init input) (fastCutHighProbTime n) ∧
    RandCallsBounded w fastCutHighProbProgram (.init input) (fastCutHighProbTime n)
      (fastCutTrials n * (6 * (n * n))) ∧
    (∀ cfg ∈ (runRand w fastCutHighProbProgram (fastCutHighProbTime n)
        (.running (.init input))).support,
      ∃ (y : Data 24) (C : Finset (Fin n)),
        cfg = .halted (cutWeight W C) y ∧
        y.Bounded w ∧
        IsNonTrivialCut C ∧
        minCut W ≤ cutWeight W C ∧
        Modifies (Finset.Ico (2 + n * n) (2 + 27 * (n * n)))
          (Data.init (r := 24) input).mem y.mem) ∧
    (0 < minCut W →
      (evalRand w fastCutHighProbProgram (fastCutHighProbTime n) (.init input)).toOuterMeasure
          {cfg | ∀ y, cfg ≠ .halted (minCut W) y} ≤
        (1 : ℝ≥0∞) / ((2 * n : ℕ) : ℝ≥0∞)) := by
  intro input
  obtain ⟨hhalt, hcalls, hpost, -, hmiss⟩ :=
    program_of_law (fastCutHighProbCode_law hn hW hw htot) (fastCutHighProbTime_bound hn)
      (inputFits_fastCut hn hw htot) fun _ hv =>
        Lean.Karger.exists_cut_of_mem_support_fastCutHighProbLaw hn hW hv
  exact ⟨hhalt, hcalls, hpost, fun hmin =>
    hmiss.trans (Lean.Karger.fastCutHighProbLaw_failure_le hn hW hmin)⟩

/-- `fastCutHighProbProgram` misses `minCut W` with probability at most `1 / n`, unconditionally
without `2 ≤ n` or `0 < minCut W`: for `n < 2` the bound `1 / n` is at least `1`, and for `2 ≤ n`
with `minCut W = 0` every recursive trial outputs `0`. -/
theorem fastCutHighProbProgram_failure_le_inv_n {n w : ℕ} {W : Fin n → Fin n → ℕ}
    (hW : IsMultigraph W)
    (hw : logWidth 4 n ≤ w) (htot : Fits w (totalDoubledWeight W)) :
    (evalRand w fastCutHighProbProgram (fastCutHighProbTime n)
        (.init (n :: flattenMatrix W))).toOuterMeasure
        {cfg | ∀ y, cfg ≠ .halted (minCut W) y} ≤
      (1 : ℝ≥0∞) / (n : ℝ≥0∞) :=
  program_failure_le_inv_n fun hn =>
    ⟨_, _, _, _, fastCutHighProbCode_law hn hW hw htot, fastCutHighProbTime_bound hn,
      Lean.Karger.fastCutHighProbLaw_failure_le hn hW,
      Lean.Karger.eq_zero_of_mem_support_fastCutHighProbLaw hn hW⟩

end FastCutHighProb

end Cslib.Algorithms.WordRAM.Karger
