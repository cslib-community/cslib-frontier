/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.MaxFlow.RelabelToFront
public import CslibFrontier.Computability.WordRAM.ListOutput
public import CslibFrontier.Computability.WordRAM.Time
import CslibFrontier.Computability.WordRAM.Allocation
import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.InputArray
import CslibFrontier.Computability.WordRAM.Notation
import CslibFrontier.Computability.WordRAM.SymbolicExec
import CslibFrontier.Foundations.Data.List.RowMajor
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Relabel-to-Front Maximum Flow in `O(|V|³)` Word-RAM Time

Lowers the executable Goldberg–Tarjan relabel-to-front maximum-flow algorithm
(`Cslib.Algorithms.Lean.MaxFlow.relabelToFrontDense`, [GoldbergTarjan1988], Sections 3–4;
[CLRS2009], Sections 26.4–26.5) to the standard-basis word RAM (`Cslib.WordRAM.Basis.standard`),
proving `O(n³)` instruction bounds for both scalar maximum-flow value (`Program.ComputesInTime`)
and joint value + minimum `s`–`t` gap cut + maximum-flow matrix output
(`Program.ComputesListInTime`).

## Input, workspace layout, and word bound

An instance (`Cslib.Algorithms.WordRAM.PushRelabel.Instance`) specifies `n : ℕ`, terminals
`s t : Fin n`, and an `n × n` integer capacity matrix `cap : Fin n → Fin n → ℕ`. Its word-list
encoding `Instance.encode` (`n :: s :: t :: flattenMatrix cap`, length `3 + n * n`) stores `n`, `s`,
`t` at addresses `1, 2, 3` and `cap u v` at `4 + u * n + v`.

For `s ≠ t`, the structured solver `solver` allocates contiguous arrays past the input:
* `baseF = 4 + n * n`: current preflow matrix `flow[u, v] ≤ maxCap` (`n * n` words);
* `baseE = 4 + 2 * n * n`: vertex excesses `(excess v).toNat ≤ n * maxCap` for `v ≠ s` (`n` words);
* `baseH = 4 + 2 * n * n + n`: vertex heights `height[v] ≤ 2 * n - 1` (`n` words);
* `baseC = 4 + 2 * n * n + 2 * n`: current-arc scan indices `cur[v] ≤ n` (`n` words);
* `baseO = 4 + 2 * n * n + 3 * n`: active-list vertex order `done ++ todo` (`n - 2` words);
* `outBase = 4 + 2 * n * n + 4 * n`: list output `[1 + n + n², value, cut[0..n), flow[0..n²)]`.

Every array address, counter, height, capacity, residual capacity (`≤ 2 * maxCap`), excess
(`≤ n * maxCap`), and flow value fits below `Instance.wordBound`, i.e. `O(log n + log maxCap)`
word width (`w = O(log n + log maxCap)`). Both inner `discharge` and outer move-to-front loops
execute via `ExecWithin.loop_potential` against exact step counts from `dischargeLoop` and
`rtfLoop`, paying `O(1)` per push, discharge, and current-arc advance and `O(n)` per relabel
scan/list-shift, yielding total time `prTime n = 720 * n ^ 3 + 40` (`O(n³)`).

## Main definitions

* `Cslib.Algorithms.WordRAM.PushRelabel.Instance`,
  `Cslib.Algorithms.WordRAM.PushRelabel.Instance.toNetwork`,
  `Cslib.Algorithms.WordRAM.PushRelabel.Instance.maxCap`,
  `Cslib.Algorithms.WordRAM.PushRelabel.Instance.out`,
  `Cslib.Algorithms.WordRAM.PushRelabel.Instance.maxFlowValue`,
  `Cslib.Algorithms.WordRAM.PushRelabel.Instance.answerWords`,
  `Cslib.Algorithms.WordRAM.PushRelabel.Instance.encode`,
  `Cslib.Algorithms.WordRAM.PushRelabel.Instance.wordBound`.
* `Cslib.Algorithms.WordRAM.PushRelabel.prTime`,
  `Cslib.Algorithms.WordRAM.PushRelabel.outBase`,
  `Cslib.Algorithms.WordRAM.PushRelabel.acc`,
  `Cslib.Algorithms.WordRAM.PushRelabel.solver`,
  `Cslib.Algorithms.WordRAM.PushRelabel.program`,
  `Cslib.Algorithms.WordRAM.PushRelabel.flowProgram`: `O(n³)` instruction budget, output
  registers (`14` and `31`), structured solver, list-output flat program (value, minimum gap
  cut, and flow), and scalar flow-value flat program over `Basis.standard`.

## Main results

* `Cslib.Algorithms.WordRAM.PushRelabel.Instance.isMaxFlow_out`,
  `Cslib.Algorithms.WordRAM.PushRelabel.Instance.isMinCut_out`: maximum-flow and minimum-cut
  correctness of `inst.out` when `inst.s ≠ inst.t`.
* `Cslib.Algorithms.WordRAM.PushRelabel.program_spec`,
  `Cslib.Algorithms.WordRAM.PushRelabel.computesListInTime_pushRelabel`: `O(n³)` list execution
  (`Program.ComputesListInTime`) outputting `inst.answerWords` at any width admitting
  `inst.wordBound`.
* `Cslib.Algorithms.WordRAM.PushRelabel.executes_maxFlowValue`,
  `Cslib.Algorithms.WordRAM.PushRelabel.computesInTime_maxFlowValue`: `O(n³)` scalar execution
  (`Program.ComputesInTime`) returning `inst.maxFlowValue`.
* `Cslib.Algorithms.WordRAM.PushRelabel.not_readsWidth_program`,
  `Cslib.Algorithms.WordRAM.PushRelabel.isRandFree_program`,
  `Cslib.Algorithms.WordRAM.PushRelabel.not_readsWidth_flowProgram`,
  `Cslib.Algorithms.WordRAM.PushRelabel.isRandFree_flowProgram`: width-independence and determinism.

## References

* [A. V. Goldberg and R. E. Tarjan,
  *A New Approach to the Maximum-Flow Problem*][GoldbergTarjan1988]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest, and C. Stein,
  *Introduction to Algorithms*][CLRS2009]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.PushRelabel

open Cslib.WordRAM
open Cslib.Algorithms.Lean.MaxFlow
open Cslib.Algorithms.Lean.MaxFlow.Network
open Cslib.Algorithms.Lean.MaxFlow.Network.Preflow
open Cslib.Algorithms.Lean.MaxFlow.Network.PushRelabel
open Cslib.Algorithms.Lean.MaxFlow.Network.RelabelToFront

/-! ### Problem instances, encodings, and pure-specification bridges -/

/-- An instance of the integral maximum-flow / minimum `s`–`t` cut problem on `Fin n`. -/
structure Instance where
  /-- Number of vertices. -/
  n : ℕ
  /-- Source vertex. -/
  s : Fin n
  /-- Sink vertex. -/
  t : Fin n
  /-- Nonnegative integral arc capacity matrix. -/
  cap : Fin n → Fin n → ℕ

namespace Instance

/-- Flow network corresponding to `inst`. -/
def toNetwork (inst : Instance) : Network (Fin inst.n) where
  cap := inst.cap
  s := inst.s
  t := inst.t

/-- Maximum single-arc capacity in `inst`. -/
def maxCap (inst : Instance) : ℕ :=
  Finset.univ.sup fun p : Fin inst.n × Fin inst.n => inst.cap p.1 p.2

theorem cap_le_maxCap (inst : Instance) (u v : Fin inst.n) : inst.cap u v ≤ inst.maxCap :=
  Finset.le_sup (f := fun p : Fin inst.n × Fin inst.n => inst.cap p.1 p.2)
    (Finset.mem_univ (u, v))

private theorem n_pos (inst : Instance) : 0 < inst.n :=
  inst.s.pos

/-- Canonical pure relabel-to-front output on `inst`. -/
def out (inst : Instance) : RelabelToFrontOutput inst.toNetwork :=
  relabelToFrontDense inst.toNetwork

/-- Optimal integer maximum-flow value as a natural number. -/
def maxFlowValue (inst : Instance) : ℕ :=
  inst.out.flow.value.toNat

/-- Encoded output word list `[maxFlowValue, cutIndicators..., flowMatrix...]`: length
`1 + n + n * n`, where entry `1 + v` is `1` iff `v ∈ inst.out.cut` and entry
`1 + n + u * n + v` is `inst.out.flow u v`. -/
def answerWords (inst : Instance) : List ℕ :=
  inst.maxFlowValue ::
    ((List.finRange inst.n).map (fun v => if v ∈ inst.out.cut then 1 else 0) ++
      (List.finRange inst.n).flatMap fun u =>
        (List.finRange inst.n).map fun v => inst.out.flow u v)

/-- Word-RAM input encoding `n :: s :: t :: flattenMatrix cap`, of length `3 + n * n`. -/
def encode (inst : Instance) : List ℕ :=
  inst.n :: inst.s.val :: inst.t.val ::
    (List.finRange inst.n).flatMap fun u =>
      (List.finRange inst.n).map fun v => inst.cap u v

/-- Word-size envelope (`O(n² + n * maxCap)`), so `w = O(log n + log maxCap)` suffices. -/
def wordBound (inst : Instance) : ℕ :=
  4 * inst.n * inst.n + 10 * inst.n + 2 * (inst.n + 1) * inst.maxCap + 16

theorem isMaxFlow_out (inst : Instance) (hst : inst.s ≠ inst.t) :
    inst.out.flow.IsMaxFlow :=
  (relabelToFrontDense_correct (N := inst.toNetwork) hst).1

theorem isMinCut_out (inst : Instance) (hst : inst.s ≠ inst.t) :
    inst.toNetwork.IsMinCut inst.out.cut :=
  (relabelToFrontDense_correct (N := inst.toNetwork) hst).2.1

theorem natCast_maxFlowValue (inst : Instance) :
    (inst.maxFlowValue : ℤ) = inst.out.flow.value := by
  unfold maxFlowValue
  by_cases hst : inst.s = inst.t
  · simp [out, relabelToFrontDense, relabelToFront, relabelToFrontWith, hst, toNetwork,
      Network.Flow.value, Network.Flow.netOut, Network.Flow.zero]
  · obtain ⟨_, _, hval, _⟩ := relabelToFrontDense_correct (N := inst.toNetwork) hst
    rw [out, hval]
    exact Int.toNat_of_nonneg (Int.natCast_nonneg _)

theorem maxFlowValue_le (inst : Instance) :
    inst.maxFlowValue ≤ inst.n * inst.maxCap := by
  have hcast := inst.natCast_maxFlowValue
  have h1 : (∑ v : Fin inst.n, (inst.out.flow inst.s v : ℤ)) ≤ inst.n * inst.maxCap := by
    simpa using Finset.sum_le_sum fun v (_ : v ∈ Finset.univ) =>
      Int.ofNat_le.mpr ((inst.out.flow.le_cap inst.s v).trans (inst.cap_le_maxCap inst.s v))
  have h2 : (0 : ℤ) ≤ ∑ u : Fin inst.n, (inst.out.flow u inst.s : ℤ) :=
    Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _
  unfold Network.Flow.value Network.Flow.netOut at hcast
  change _ = (∑ v, (inst.out.flow inst.s v : ℤ)) - ∑ u, (inst.out.flow u inst.s : ℤ) at hcast
  omega

theorem length_answerWords (inst : Instance) :
    inst.answerWords.length = 1 + inst.n + inst.n * inst.n := by
  simp only [answerWords, List.length_cons, List.length_append, List.length_map,
    List.length_finRange, List.length_flatMap, List.map_const', List.sum_replicate,
    smul_eq_mul]
  omega

private theorem init_mem_n {r : ℕ} (inst : Instance) :
    (Data.init inst.encode : Data r).mem 1 = inst.n := rfl

private theorem init_mem_s {r : ℕ} (inst : Instance) :
    (Data.init inst.encode : Data r).mem 2 = inst.s.val := rfl

private theorem init_mem_t {r : ℕ} (inst : Instance) :
    (Data.init inst.encode : Data r).mem 3 = inst.t.val := rfl

private theorem init_mem_cap {r : ℕ} (inst : Instance) (u v : Fin inst.n) :
    (Data.init inst.encode : Data r).mem (4 + (u.val * inst.n + v.val)) = inst.cap u v := by
  simpa [encode] using Data.init_mem_flatMap_finRange (r := r) [inst.n, inst.s.val, inst.t.val]
    (fun u' v' => inst.cap u' v') u v

theorem inputFits_encode (inst : Instance) {w : ℕ} (hw : Fits w inst.wordBound) :
    InputFits w inst.encode := by
  refine InputFits.flatMap_finRange [inst.n, inst.s.val, inst.t.val]
    (fun u v => inst.cap u v)
    (hw.of_le (by
      unfold wordBound
      dsimp only [List.length]; nlinarith [inst.n_pos])) ?_
    fun u v => hw.of_le (by
      unfold wordBound
      nlinarith [inst.cap_le_maxCap u v, inst.n_pos])
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact hw.of_le (by unfold wordBound; nlinarith [inst.n_pos])
  · exact hw.of_le (by have := inst.s.isLt; unfold wordBound; omega)
  · exact hw.of_le (by have := inst.t.isLt; unfold wordBound; omega)

end Instance

/-- Explicit `O(n³)` instruction-count bound for Word-RAM relabel-to-front. -/
def prTime (n : ℕ) : ℕ :=
  720 * n ^ 3 + 40

/-- Register holding the base output address `[len, maxFlowValue, cut..., flow...]`. -/
abbrev outBase : Fin 32 := 14

/-- Output accumulator register holding `maxFlowValue`. -/
abbrev acc : Fin 32 := 31

end Cslib.Algorithms.WordRAM.PushRelabel

end

public section

namespace Cslib.Algorithms.WordRAM.PushRelabel

open Cslib.WordRAM
open Cslib.Algorithms.Lean.MaxFlow
open Cslib.Algorithms.Lean.MaxFlow.Network
open Cslib.Algorithms.Lean.MaxFlow.Network.Preflow
open Cslib.Algorithms.Lean.MaxFlow.Network.PushRelabel
open Cslib.Algorithms.Lean.MaxFlow.Network.RelabelToFront

/-! ### Register layout and structured Word-RAM solver -/

private abbrev zero : Fin 32 := 0
private abbrev one : Fin 32 := 1
private abbrev rn : Fin 32 := 2
private abbrev rs : Fin 32 := 3
private abbrev rt : Fin 32 := 4
private abbrev rnn : Fin 32 := 5
private abbrev rTwoN : Fin 32 := 6
private abbrev rLim : Fin 32 := 7
private abbrev rCapBase : Fin 32 := 8
private abbrev baseF : Fin 32 := 9
private abbrev baseE : Fin 32 := 10
private abbrev baseH : Fin 32 := 11
private abbrev baseC : Fin 32 := 12
private abbrev baseO : Fin 32 := 13
private abbrev rTwo : Fin 32 := 15

private abbrev rPos : Fin 32 := 16
private abbrev rU : Fin 32 := 17
private abbrev rRel : Fin 32 := 18
private abbrev rCur : Fin 32 := 19
private abbrev rEx : Fin 32 := 20
private abbrev rHU : Fin 32 := 21
private abbrev rIdx : Fin 32 := 22
private abbrev rMinH : Fin 32 := 23
private abbrev rDelta : Fin 32 := 24
private abbrev rRc : Fin 32 := 25
private abbrev rRev : Fin 32 := 26
private abbrev rAddr : Fin 32 := 27
private abbrev rAddr2 : Fin 32 := 28
private abbrev rVal : Fin 32 := 29
private abbrev rVal2 : Fin 32 := 30

private def setupCode : Code .standard 32 :=
  ram[
    zero ← #0;
    one ← #1;
    rTwo ← #2;
    rCapBase ← #4;
    rn ← *one;
    rs ← *rTwo;
    rAddr ← #3;
    rt ← *rAddr;
    rnn ← rn * rn;
    rTwoN ← rTwo * rn;
    if rs = rt then [ rLim ← zero ] else [ rLim ← rn - rTwo ];
    baseF ← rCapBase + rnn;
    baseE ← baseF + rnn;
    baseH ← baseE + rn;
    baseC ← baseH + rn;
    baseO ← baseC + rn;
    outBase ← baseO + rn
  ]

private def zeroOutPfx : Code .standard 32 :=
  ram[
    rVal ← rn + rnn; rVal ← rVal + one; *outBase ← rVal;
    rAddr ← outBase + one; *rAddr ← zero;
    rAddr2 ← outBase + rTwo; rVal2 ← rn + rnn
  ]

private def zeroOutCode : Code .standard 32 :=
  (zeroOutPfx.seq (fillConst rAddr2 rVal2 zero one rIdx rAddr)).seq (ram[ acc ← zero ])

private def saturateBody : Code .standard 32 :=
  ram[
    rVal ← rAddr2 + rIdx;
    rAddr ← rCapBase + rVal; rVal2 ← *rAddr;
    rAddr ← baseF + rVal; *rAddr ← rVal2;
    if rIdx = rs then [ rVal ← rVal ] else [ rAddr ← baseE + rIdx; *rAddr ← rVal2 ];
    rIdx ← rIdx + one
  ]

private def buildOrderBody : Code .standard 32 :=
  ram[
    if rIdx = rs then [ rVal ← rVal ] else [
      if rIdx = rt then [ rVal ← rVal ] else [
        rAddr ← baseO + rPos; *rAddr ← rIdx; rPos ← rPos + one
      ]
    ];
    rIdx ← rIdx + one
  ]

private def initPrefix1 : Code .standard 32 :=
  ram[ rVal ← rnn + rTwoN; rVal ← rVal + rn ]

private def initMid : Code .standard 32 :=
  ram[
    rAddr ← baseH + rs; *rAddr ← rn;
    rAddr2 ← rs * rn;
    rIdx ← zero
  ]

private def initNonTermCode : Code .standard 32 :=
  (initPrefix1.seq (fillConst baseF rVal zero one rIdx rAddr)).seq
    (initMid.seq ((Code.loop (.lt rIdx rn) saturateBody).seq
      ((ram[ rPos ← zero; rIdx ← zero ]).seq
        ((Code.loop (.lt rIdx rn) buildOrderBody).seq (ram[ rPos ← zero ])))))

private def relabelBody : Code .standard 32 :=
  ram[
    rAddr ← rU * rn; rAddr ← rAddr + rIdx;
    rAddr2 ← rCapBase + rAddr; rRc ← *rAddr2;
    rAddr2 ← baseF + rAddr; rVal ← *rAddr2;
    rRc ← rRc - rVal;
    rAddr ← rIdx * rn; rAddr ← rAddr + rU; rAddr ← baseF + rAddr;
    rVal ← *rAddr; rRc ← rRc + rVal;
    if zero < rRc then [
      rAddr ← baseH + rIdx; rVal ← *rAddr;
      if rVal < rMinH then [ rMinH ← rVal ] else [ rVal ← rVal ]
    ] else [ rVal ← rVal ];
    rIdx ← rIdx + one
  ]

private def relabelTail : Code .standard 32 :=
  ram[
    rHU ← rMinH + one;
    rAddr ← baseH + rU; *rAddr ← rHU;
    rAddr ← baseC + rU; *rAddr ← zero;
    rCur ← zero;
    rRel ← one
  ]

private def relabelCode : Code .standard 32 :=
  (ram[ rMinH ← rTwoN; rIdx ← zero ]).seq ((Code.loop (.lt rIdx rn) relabelBody).seq relabelTail)

private def resCapCode : Code .standard 32 :=
  ram[
    rAddr ← rU * rn; rAddr ← rAddr + rCur;
    rAddr2 ← rCapBase + rAddr; rRc ← *rAddr2;
    rAddr2 ← baseF + rAddr; rVal ← *rAddr2;
    rRc ← rRc - rVal;
    rAddr ← rCur * rn; rAddr ← rAddr + rU;
    rAddr2 ← baseF + rAddr; rVal ← *rAddr2;
    rRc ← rRc + rVal
  ]

private def admissibleTail : Code .standard 32 :=
  ram[
    if zero < rRc then [
      rAddr ← baseH + rCur; rVal ← *rAddr; rVal2 ← rVal + one;
      if rHU = rVal2 then [ rVal2 ← one ] else [ rVal2 ← zero ]
    ] else [ rVal2 ← zero ]
  ]

private def admissibleCode : Code .standard 32 :=
  resCapCode.seq admissibleTail

private def pushDeltaCode : Code .standard 32 :=
  ram[ if rEx < rRc then [ rDelta ← rEx ] else [ rDelta ← rRc ] ]

private def pushMid1 : Code .standard 32 :=
  ram[
    rAddr2 ← rCur * rn; rAddr2 ← rAddr2 + rU; rAddr2 ← baseF + rAddr2;
    rVal ← *rAddr2
  ]

private def pushRevCode : Code .standard 32 :=
  ram[ if rDelta < rVal then [ rRev ← rDelta ] else [ rRev ← rVal ] ]

private def pushMid2 : Code .standard 32 :=
  ram[
    rVal ← rVal - rRev; *rAddr2 ← rVal;
    rVal2 ← rDelta - rRev;
    rAddr ← rU * rn; rAddr ← rAddr + rCur; rAddr ← baseF + rAddr;
    rVal ← *rAddr; rVal ← rVal + rVal2; *rAddr ← rVal;
    rEx ← rEx - rDelta;
    rAddr ← baseE + rU; *rAddr ← rEx
  ]

private def pushPart1 : Code .standard 32 :=
  pushDeltaCode.seq (pushMid1.seq (pushRevCode.seq pushMid2))

private def pushTail : Code .standard 32 :=
  ram[
    if rCur = rs then [ rVal ← rVal ] else [
      rAddr ← baseE + rCur; rVal ← *rAddr; rVal ← rVal + rDelta; *rAddr ← rVal
    ]
  ]

private def pushBody : Code .standard 32 :=
  pushPart1.seq pushTail

private def advanceCode : Code .standard 32 :=
  ram[ rCur ← rCur + one; rAddr ← baseC + rU; *rAddr ← rCur ]

private def dischargeElse : Code .standard 32 :=
  admissibleCode.seq (Code.branch (.eq rVal2 one) pushBody advanceCode)

private def dischargeBody : Code .standard 32 :=
  Code.branch (.eq rCur rn) relabelCode dischargeElse

private def dischargeInit : Code .standard 32 :=
  ram[
    rRel ← zero;
    rAddr ← baseE + rU; rEx ← *rAddr;
    rAddr ← baseH + rU; rHU ← *rAddr;
    rAddr ← baseC + rU; rCur ← *rAddr
  ]

private def dischargeCode : Code .standard 32 :=
  dischargeInit.seq (Code.loop (.lt zero rEx) dischargeBody)

private def shiftOrderBody : Code .standard 32 :=
  ram[
    rVal ← rIdx - one;
    rAddr ← baseO + rVal; rVal2 ← *rAddr;
    rAddr ← baseO + rIdx; *rAddr ← rVal2;
    rIdx ← rVal
  ]

private def shiftOrderTail : Code .standard 32 :=
  ram[ *baseO ← rU; rPos ← one ]

private def shiftOrderCode : Code .standard 32 :=
  (ram[ rIdx ← rPos ]).seq ((Code.loop (.lt zero rIdx) shiftOrderBody).seq shiftOrderTail)

private def outerBranch : Code .standard 32 :=
  Code.branch (.eq rRel one) shiftOrderCode (ram[ rPos ← rPos + one ])

private def outerBody : Code .standard 32 :=
  (ram[ rAddr ← baseO + rPos; rU ← *rAddr ]).seq (dischargeCode.seq outerBranch)

private def outerCode : Code .standard 32 :=
  Code.loop (.lt rPos rLim) outerBody

private def scanGapInner : Code .standard 32 :=
  ram[
    rAddr ← baseH + rIdx; rVal ← *rAddr;
    if rVal = rCur then [ rRel ← one ] else [ rVal ← rVal ];
    rIdx ← rIdx + one
  ]

private def writeCutBody : Code .standard 32 :=
  ram[
    rAddr ← baseH + rIdx; rVal ← *rAddr;
    rAddr2 ← outBase + rTwo; rAddr2 ← rAddr2 + rIdx;
    if rMinH < rVal then [ *rAddr2 ← one ] else [ *rAddr2 ← zero ];
    rIdx ← rIdx + one
  ]

private def copyFlowBody : Code .standard 32 :=
  ram[
    rAddr ← baseF + rIdx; rVal ← *rAddr;
    rAddr2 ← outBase + rTwo; rAddr2 ← rAddr2 + rn; rAddr2 ← rAddr2 + rIdx;
    *rAddr2 ← rVal;
    rIdx ← rIdx + one
  ]

private def gapTail : Code .standard 32 :=
  ram[
    if rRel = zero then [ rMinH ← rCur ] else [ rVal ← rVal ];
    rCur ← rCur - one
  ]

private def gapOuterBody : Code .standard 32 :=
  (ram[ rRel ← zero; rIdx ← zero ]).seq ((Code.loop (.lt rIdx rn) scanGapInner).seq gapTail)

private def cutPfx : Code .standard 32 :=
  ram[
    rAddr ← baseE + rt; acc ← *rAddr;
    rMinH ← rn;
    rCur ← rn - one
  ]

private def cutHdr : Code .standard 32 :=
  ram[
    rVal ← rn + rnn; rVal ← rVal + one; *outBase ← rVal;
    rAddr ← outBase + one; *rAddr ← acc; rIdx ← zero
  ]

private def cutAndOutputCode : Code .standard 32 :=
  cutPfx.seq ((Code.loop (.lt zero rCur) gapOuterBody).seq
    (cutHdr.seq ((Code.loop (.lt rIdx rn) writeCutBody).seq
      ((ram[ rIdx ← zero ]).seq (Code.loop (.lt rIdx rnn) copyFlowBody)))))

/-- Structured standard-basis Word-RAM relabel-to-front solver: writes
`[1 + n + n², maxFlowValue, cut..., flow...]` starting at `outBase` and leaves `maxFlowValue` in
register `acc` (`31`). -/
def solver : Code .standard 32 :=
  setupCode.seq (Code.branch (.eq rs rt) zeroOutCode
    (initNonTermCode.seq (outerCode.seq cutAndOutputCode)))

/-- Flat Word-RAM relabel-to-front program computing `inst.answerWords` (`[maxFlowValue,
cutIndicators..., flowMatrix...]`) via `ExecutesList`. -/
def program : Program .standard 32 :=
  solver.program outBase

/-- Flat Word-RAM relabel-to-front program computing scalar `inst.maxFlowValue` in register `acc`
via `Executes`. -/
def flowProgram : Program .standard 32 :=
  solver.program acc

/-! ### Helper bridges between `tabulate` and `id` in `RelabelToFront` -/

section Helpers

private theorem list_getElem_eq_of_eq {α : Type*} {l : List α} {i j : ℕ} (h : i = j)
    (hi : i < l.length) : l[i]'hi = l[j]'(h ▸ hi) := by
  subst h
  rfl

private theorem getElem_flatMap_finRange {n : ℕ} (f : Fin n → Fin n → ℕ) (u v : Fin n)
    (h : u.val * n + v.val <
      ((List.finRange n).flatMap fun a => (List.finRange n).map (f a)).length) :
    ((List.finRange n).flatMap fun a => (List.finRange n).map (f a))[u.val * n + v.val]'h =
      f u v := by
  have hget := List.getD_flatMap_ofFn f 0 u v
  simp only [List.ofFn_eq_map, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h,
    Option.getD_some] at hget
  exact hget

private theorem dischargeLoop_tabulate {n : ℕ} {N : Network (Fin n)} (adj : Fin n → List (Fin n))
    (u : Fin n) :
    ∀ (fuel : ℕ) (s : CAState N),
      dischargeLoop adj tabulateCA u fuel s = dischargeLoop adj id u fuel s
  | 0, _ => by
    unfold dischargeLoop
    split_ifs <;> rfl
  | fuel + 1, s => by
    rw [dischargeLoop.eq_def (norm := tabulateCA), dischargeLoop.eq_def (norm := id)]
    dsimp only
    split_ifs with hact
    · cases s.cur u with
      | nil => simp only [id_eq, tabulateCA_eq, dischargeLoop_tabulate adj u fuel]
      | cons v vs =>
        dsimp only
        split_ifs <;>
          simp only [id_eq, tabulateCA_eq, dischargeLoop_tabulate adj u fuel]
    · rfl

private theorem rtfLoop_tabulate {n : ℕ} {N : Network (Fin n)} (adj : Fin n → List (Fin n)) :
    ∀ (fuel : ℕ) (st : RTFState N),
      rtfLoop adj tabulateCA tabulateRTF fuel st = rtfLoop adj id id fuel st
  | fuel, st => by
    rw [rtfLoop.eq_def (caNorm := tabulateCA), rtfLoop.eq_def (caNorm := id)]
    dsimp only
    cases htodo : st.todo with
    | nil => rfl
    | cons u rest =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
        dsimp only
        have hdis : discharge adj tabulateCA u st.ca = discharge adj id u st.ca :=
          dischargeLoop_tabulate adj u _ st.ca
        rw [hdis]
        simp only [id_eq, tabulateRTF_eq, rtfLoop_tabulate adj fuel]

private theorem out_eq_id (inst : Instance) (hst : inst.s ≠ inst.t) :
    inst.out = relabelToFrontWith inst.toNetwork (nonTermFin inst.toNetwork)
      (defaultAdj inst.n) id id := by
  have hst' : inst.toNetwork.s ≠ inst.toNetwork.t := hst
  unfold Instance.out relabelToFrontDense relabelToFront relabelToFrontWith
  rw [ite_eq_right hst', ite_eq_right hst', rtfLoop_tabulate]

private theorem out_eq_ofState (inst : Instance) (hst : inst.s ≠ inst.t) :
    let r := rtfLoop (defaultAdj inst.n) id id (rtfFuel (Fin inst.n))
      (RTFState.init inst.toNetwork (defaultAdj inst.n) (nonTermFin inst.toNetwork))
    inst.out = RelabelToFrontOutput.ofState r.1 r.2 := by
  have hst' : inst.toNetwork.s ≠ inst.toNetwork.t := hst
  rw [out_eq_id inst hst]
  unfold relabelToFrontWith
  rw [ite_eq_right hst']

private theorem two_le_n_of_ne (inst : Instance) (hst : inst.s ≠ inst.t) : 2 ≤ inst.n := by
  simpa [Finset.card_pair hst] using Finset.card_le_univ ({inst.s, inst.t} : Finset (Fin inst.n))

private theorem drop_finRange_eq_cons {n k : ℕ} (hk : k < n) :
    (List.finRange n).drop k = ⟨k, hk⟩ :: (List.finRange n).drop (k + 1) := by
  rw [List.drop_eq_getElem_cons (by simp [hk]), List.getElem_finRange]
  simp

private theorem drop_finRange_eq_nil {n : ℕ} :
    (List.finRange n).drop n = [] :=
  List.drop_of_length_le (by simp)

private theorem preflow_excess_le (inst : Instance) (f : inst.toNetwork.Preflow)
    (v : Fin inst.n) (hvs : v ≠ inst.s) : (f.excess v).toNat ≤ inst.n * inst.maxCap := by
  have hnonneg : 0 ≤ f.excess v := f.excess_nonneg hvs
  have hin : ∑ u : Fin inst.n, (f u v : ℤ) ≤ inst.n * inst.maxCap := by
    simpa using Finset.sum_le_sum fun u (_ : u ∈ Finset.univ) =>
      Int.ofNat_le.mpr ((f.le_cap u v).trans (inst.cap_le_maxCap u v))
  have hout : (0 : ℤ) ≤ ∑ w : Fin inst.n, (f v w : ℤ) :=
    Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _
  unfold Preflow.excess at hnonneg ⊢
  omega

private theorem resCap_le_two_maxCap (inst : Instance) (f : inst.toNetwork.Preflow)
    (u v : Fin inst.n) : f.resCap u v ≤ 2 * inst.maxCap := by
  have h0 := inst.cap_le_maxCap u v
  have h1 := (f.le_cap u v).trans h0
  have h2 := (f.le_cap v u).trans (inst.cap_le_maxCap v u)
  change inst.cap u v - f u v + f v u ≤ 2 * inst.maxCap
  omega

private theorem initial_excess_eq (inst : Instance) (v : Fin inst.n) (hvs : v ≠ inst.s) :
    (Preflow.initial inst.toNetwork).excess v = inst.cap inst.s v := by
  unfold Preflow.excess Preflow.initial
  rw [Finset.sum_eq_single inst.toNetwork.s (fun _ _ hu => by simp [hu])
      (fun h => absurd (Finset.mem_univ _) h),
    Finset.sum_eq_zero fun _ _ => by simp [show v ≠ inst.toNetwork.s from hvs]]
  simp [Instance.toNetwork]

private theorem excess_sink_eq_value (inst : Instance) (f : inst.toNetwork.Preflow)
    (hst : inst.s ≠ inst.t) (hz : ∀ v, v ≠ inst.s → v ≠ inst.t → f.excess v = 0) :
    (f.toFlow hz).value = f.excess inst.t := by
  have hsum : ∑ v : Fin inst.n, f.excess v = 0 := by
    unfold Preflow.excess
    rw [Finset.sum_sub_distrib, Finset.sum_comm]
    omega
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ inst.s),
    ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hst.symm, Finset.mem_univ _⟩),
    Finset.sum_eq_zero fun v hv =>
      hz v (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hv)) (Finset.ne_of_mem_erase hv),
    add_zero] at hsum
  unfold Preflow.excess at hsum
  unfold Network.Flow.value Network.Flow.netOut Preflow.excess
  change (∑ w : Fin inst.n, (f inst.s w : ℤ)) - ∑ u : Fin inst.n, (f u inst.s : ℤ) = _
  omega

private theorem rtfInv_length_eq {inst : Instance} {st : RTFState inst.toNetwork}
    (hinv : RTFInv (defaultAdj inst.n) st) (hst : inst.s ≠ inst.t) :
    (st.done ++ st.todo).length = inst.n - 2 := by
  have hfs : (st.done ++ st.todo).toFinset = (Finset.univ.erase inst.s).erase inst.t := by
    ext v
    have hm : v ∈ st.done ++ st.todo ↔ v ≠ inst.s ∧ v ≠ inst.t := hinv.mem_iff v
    simpa [and_comm] using hm
  rw [← List.toFinset_card_of_nodup hinv.nodup, hfs,
    Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hst.symm, Finset.mem_univ _⟩),
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  omega

private theorem gapLevel_minimal {V : Type*} [Fintype V] {h : V → ℕ} {j : ℕ}
    (hj0 : 0 < j) (hjn : j < Fintype.card V) (hj : ∀ v, h v ≠ j) :
    gapLevel h ≤ j := by
  unfold gapLevel
  cases hfind : (List.range (Fintype.card V)).find? (fun k => decide (0 < k ∧ ∀ v, h v ≠ k)) with
  | none =>
    exact absurd (decide_eq_true ⟨hj0, hj⟩)
      (List.find?_eq_none.mp hfind j (List.mem_range.mpr hjn))
  | some g =>
    simp only [Option.getD_some]
    obtain ⟨_, i, _, hig, hbef⟩ := List.find?_eq_some_iff_getElem.mp hfind
    have hi_eq : i = g := by simpa using hig
    subst hi_eq
    by_contra hlt
    have hj_lt : j < i := by omega
    simpa [hj0, hj] using hbef j hj_lt

private theorem outputList_eq_answerWords (inst : Instance) (mem : ℕ → ℕ)
    (hlen : mem (4 + 2 * inst.n * inst.n + 4 * inst.n) = 1 + inst.n + inst.n * inst.n)
    (hval : mem (4 + 2 * inst.n * inst.n + 4 * inst.n + 1) = inst.maxFlowValue)
    (hcut : ∀ v : Fin inst.n,
      mem (4 + 2 * inst.n * inst.n + 4 * inst.n + 2 + v.val) =
        if v ∈ inst.out.cut then 1 else 0)
    (hflow : ∀ u v : Fin inst.n,
      mem (4 + 2 * inst.n * inst.n + 4 * inst.n + 2 + inst.n + (u.val * inst.n + v.val)) =
        inst.out.flow u v) :
    outputList mem (4 + 2 * inst.n * inst.n + 4 * inst.n) = inst.answerWords := by
  have hn := inst.n_pos
  have hans_def : inst.answerWords = inst.maxFlowValue ::
      ((List.finRange inst.n).map (fun v => if v ∈ inst.out.cut then 1 else 0) ++
       (List.finRange inst.n).flatMap fun a =>
         (List.finRange inst.n).map fun b => inst.out.flow a b) := rfl
  rw [outputList_eq_iff]
  refine ⟨hlen.trans inst.length_answerWords.symm, fun i => ?_⟩
  have hi_lt : i.val < inst.answerWords.length := i.isLt
  rcases Nat.eq_zero_or_pos i.val with hz | hpos
  · change mem (4 + 2 * inst.n * inst.n + 4 * inst.n + 1 + i.val) = inst.answerWords[i.val]'hi_lt
    rw [List.getElem_of_eq hans_def hi_lt, list_getElem_eq_of_eq hz, List.getElem_cons_zero,
      hz, Nat.add_zero, hval]
  · have hil : i.val < 1 + inst.n + inst.n * inst.n := inst.length_answerWords ▸ hi_lt
    have hj : i.val = (i.val - 1) + 1 := by omega
    change mem (4 + 2 * inst.n * inst.n + 4 * inst.n + 1 + i.val) = inst.answerWords[i.val]'hi_lt
    by_cases hlt : i.val - 1 < inst.n
    · let v : Fin inst.n := ⟨i.val - 1, hlt⟩
      have haddr : 4 + 2 * inst.n * inst.n + 4 * inst.n + 1 + i.val =
          4 + 2 * inst.n * inst.n + 4 * inst.n + 2 + v.val := by
        simp only [v]; omega
      rw [haddr, hcut v, List.getElem_of_eq hans_def hi_lt, list_getElem_eq_of_eq hj,
        List.getElem_cons_succ, List.getElem_append_left (by simp [hlt]),
        List.getElem_map, List.getElem_finRange]
      rfl
    · have hj_lt : i.val - 1 - inst.n < inst.n * inst.n := by omega
      let u : Fin inst.n := ⟨(i.val - 1 - inst.n) / inst.n, Nat.div_lt_of_lt_mul hj_lt⟩
      let v : Fin inst.n := ⟨(i.val - 1 - inst.n) % inst.n, Nat.mod_lt _ hn⟩
      have hk_eq : u.val * inst.n + v.val = i.val - 1 - inst.n := by
        simpa [u, v, Nat.mul_comm] using Nat.div_add_mod (i.val - 1 - inst.n) inst.n
      have haddr : 4 + 2 * inst.n * inst.n + 4 * inst.n + 1 + i.val =
          4 + 2 * inst.n * inst.n + 4 * inst.n + 2 + inst.n + (u.val * inst.n + v.val) := by
        rw [hk_eq]; omega
      rw [haddr, hflow u v, List.getElem_of_eq hans_def hi_lt, list_getElem_eq_of_eq hj,
        List.getElem_cons_succ, List.getElem_append_right (by simp; omega)]
      simp only [List.length_map, List.length_finRange]
      have hlen_fl : u.val * inst.n + v.val <
          ((List.finRange inst.n).flatMap fun a =>
            (List.finRange inst.n).map fun b => inst.out.flow a b).length := by
        rw [hk_eq]
        simpa [List.map_const', smul_eq_mul] using hj_lt
      have hget := getElem_flatMap_finRange (fun a b => inst.out.flow a b) u v hlen_fl
      simp_rw [← hk_eq]
      exact hget.symm

private theorem execWithin_branch_pos {B : Basis} {r w T T' : ℕ} {c : Cond r}
    {t e : Code B r} {x z : Data r} (hc : c.Holds x) (hex : ExecWithin w t x z T)
    (hT : T + 1 ≤ T') : ExecWithin w (.branch c t e) x z T' := by
  obtain ⟨k, hk, h⟩ := hex
  exact ⟨k + 1, by omega, .branch_pos hc h⟩

private theorem execWithin_branch_neg {B : Basis} {r w T T' : ℕ} {c : Cond r}
    {t e : Code B r} {x z : Data r} (hc : ¬ c.Holds x) (hex : ExecWithin w e x z T)
    (hT : T + 2 ≤ T') : ExecWithin w (.branch c t e) x z T' := by
  obtain ⟨k, hk, h⟩ := hex
  exact ⟨k + 2, by omega, .branch_neg hc h⟩

end Helpers


/-! ### Machine state invariants and representation uniqueness -/

section Invariants

/-- Fixed registers and untouched capacity-matrix memory `[0, 4 + n * n)` maintained after
`setupCode`. -/
private structure CtxInv (inst : Instance) (x : Data 32) : Prop where
  hzero : x.regs zero = 0
  hone : x.regs one = 1
  hrTwo : x.regs rTwo = 2
  hrn : x.regs rn = inst.n
  hrs : x.regs rs = inst.s.val
  hrt : x.regs rt = inst.t.val
  hrnn : x.regs rnn = inst.n * inst.n
  hrTwoN : x.regs rTwoN = 2 * inst.n
  hrLim : x.regs rLim = if inst.s = inst.t then 0 else inst.n - 2
  hrCapBase : x.regs rCapBase = 4
  hbaseF : x.regs baseF = 4 + inst.n * inst.n
  hbaseE : x.regs baseE = 4 + 2 * inst.n * inst.n
  hbaseH : x.regs baseH = 4 + 2 * inst.n * inst.n + inst.n
  hbaseC : x.regs baseC = 4 + 2 * inst.n * inst.n + 2 * inst.n
  hbaseO : x.regs baseO = 4 + 2 * inst.n * inst.n + 3 * inst.n
  houtBase : x.regs outBase = 4 + 2 * inst.n * inst.n + 4 * inst.n
  mem_input : ∀ a < 4 + inst.n * inst.n, x.mem a = (Data.init inst.encode : Data 32).mem a

private theorem CtxInv.of_eq {inst : Instance} {x y : Data 32} (hx : CtxInv inst x)
    (hr : ∀ i : Fin 32, i.val < 16 → y.regs i = x.regs i)
    (hm : ∀ a < 4 + inst.n * inst.n, y.mem a = x.mem a) : CtxInv inst y :=
  { hzero := (hr zero (by decide)).trans hx.hzero
    hone := (hr one (by decide)).trans hx.hone
    hrTwo := (hr rTwo (by decide)).trans hx.hrTwo
    hrn := (hr rn (by decide)).trans hx.hrn
    hrs := (hr rs (by decide)).trans hx.hrs
    hrt := (hr rt (by decide)).trans hx.hrt
    hrnn := (hr rnn (by decide)).trans hx.hrnn
    hrTwoN := (hr rTwoN (by decide)).trans hx.hrTwoN
    hrLim := (hr rLim (by decide)).trans hx.hrLim
    hrCapBase := (hr rCapBase (by decide)).trans hx.hrCapBase
    hbaseF := (hr baseF (by decide)).trans hx.hbaseF
    hbaseE := (hr baseE (by decide)).trans hx.hbaseE
    hbaseH := (hr baseH (by decide)).trans hx.hbaseH
    hbaseC := (hr baseC (by decide)).trans hx.hbaseC
    hbaseO := (hr baseO (by decide)).trans hx.hbaseO
    houtBase := (hr outBase (by decide)).trans hx.houtBase
    mem_input := fun a ha => (hm a ha).trans (hx.mem_input a ha) }

private theorem CtxInv.set {inst : Instance} {x : Data 32} (hx : CtxInv inst x)
    {r : Fin 32} (hr : 16 ≤ r.val) {val : ℕ} : CtxInv inst (x.set r val) :=
  hx.of_eq
    (fun i hi => Data.set_regs_of_ne (fun h => by have := congrArg Fin.val h; omega) val)
    fun _ _ => rfl

private theorem set_regs_lt {x : Data 32} {r i : Fin 32} {v k : ℕ}
    (hi : i.val < k) (hk : k ≤ r.val) : (x.set r v).regs i = x.regs i :=
  Data.set_regs_of_ne (fun h => by have := congrArg Fin.val h; omega) v

private theorem CtxInv.write_ge {inst : Instance} {x : Data 32} (hx : CtxInv inst x)
    {a : ℕ} (ha : 4 + inst.n * inst.n ≤ a) {val : ℕ} : CtxInv inst (x.write a val) :=
  hx.of_eq (fun _ _ => rfl) fun q hq => Data.write_mem_of_ne (by omega) val

private theorem CtxInv.cap_eq {inst : Instance} {x : Data 32} (hx : CtxInv inst x)
    (u v : Fin inst.n) : x.mem (4 + (u.val * inst.n + v.val)) = inst.cap u v := by
  have huv : u.val * inst.n + v.val < inst.n * inst.n := by nlinarith [u.isLt, v.isLt]
  rw [hx.mem_input _ (by omega)]
  exact inst.init_mem_cap u v

private theorem fits_of_addr {inst : Instance} {w a : ℕ} (hw : Fits w inst.wordBound)
    (ha : a ≤ 4 * inst.n * inst.n + 10 * inst.n + 16) : Fits w a :=
  hw.of_le (by unfold Instance.wordBound; omega)

private theorem fits_of_val {inst : Instance} {w v : ℕ} (hw : Fits w inst.wordBound)
    (hv : v ≤ 2 * (inst.n + 1) * inst.maxCap) : Fits w v :=
  hw.of_le (by unfold Instance.wordBound; omega)

private theorem fits_val_of_le_two_maxCap {inst : Instance} {w v : ℕ} (hw : Fits w inst.wordBound)
    (hv : v ≤ 2 * inst.maxCap) : Fits w v :=
  fits_of_val hw (by nlinarith [inst.n_pos])

private theorem fits_val_of_le_n_maxCap {inst : Instance} {w v : ℕ} (hw : Fits w inst.wordBound)
    (hv : v ≤ inst.n * inst.maxCap) : Fits w v :=
  fits_of_val hw (by nlinarith)

private theorem fits_arc {inst : Instance} {w : ℕ} (hw : Fits w inst.wordBound)
    (u v : Fin inst.n) :
    Fits w (u.val * inst.n) ∧ Fits w (u.val * inst.n + v.val) ∧
    Fits w (4 + (u.val * inst.n + v.val)) ∧
    Fits w (4 + inst.n * inst.n + (u.val * inst.n + v.val)) := by
  have := List.mul_add_lt_sq u.isLt v.isLt
  have := u.isLt
  exact ⟨fits_of_addr hw (by nlinarith), fits_of_addr hw (by nlinarith),
    fits_of_addr hw (by nlinarith), fits_of_addr hw (by nlinarith)⟩

private theorem fits_vtx {inst : Instance} {w : ℕ} (hw : Fits w inst.wordBound) (v : Fin inst.n) :
    Fits w (4 + 2 * inst.n * inst.n + v.val) ∧
    Fits w (4 + 2 * inst.n * inst.n + inst.n + v.val) ∧
    Fits w (4 + 2 * inst.n * inst.n + 2 * inst.n + v.val) ∧
    Fits w (v.val + 1) := by
  have := v.isLt
  exact ⟨fits_of_addr hw (by nlinarith), fits_of_addr hw (by nlinarith),
    fits_of_addr hw (by nlinarith), fits_of_addr hw (by nlinarith)⟩

private theorem fits_resCap {inst : Instance} {w : ℕ} (hw : Fits w inst.wordBound)
    (f : inst.toNetwork.Preflow) (u v : Fin inst.n) :
    Fits w (inst.cap u v - f u v) ∧ Fits w (f.resCap u v) :=
  ⟨fits_of_val hw (by
      have := inst.cap_le_maxCap u v
      have := Nat.sub_le (inst.cap u v) (f u v)
      nlinarith),
   fits_of_val hw (by have := resCap_le_two_maxCap inst f u v; nlinarith)⟩

private theorem baseF_le_baseE (n k : ℕ) : 4 + n * n ≤ 4 + 2 * n * n + k := by
  nlinarith

private theorem baseF_le_baseOut (n k : ℕ) : 4 + n * n ≤ 4 + 2 * n * n + 4 * n + k := by
  nlinarith

private theorem outerPot_step_le (n o₁ o₂ a₁ a₂ d₁ d₂ r₁ r₂ do' da dr T_br : ℕ)
    (ho : o₁ = do' + o₂) (hd : d₁ = 1 + d₂) (ha : a₁ = da + a₂) (hr : r₁ = dr + r₂)
    (hT : T_br ≤ 3 + (8 * n + 7) * dr) :
    56 * o₂ + 32 * a₂ + 22 * d₂ + (33 * n + 38) * r₂ +
        (2 + (2 + 56 * do' + 32 * da + (25 * n + 30) * dr + 9 + T_br)) ≤
      56 * o₁ + 32 * a₁ + 22 * d₁ + (33 * n + 38) * r₁ := by
  nlinarith

private theorem outerPot_init_le (n ops dis adv rel : ℕ)
    (hrel : rel ≤ 2 * n ^ 2) (hdis : dis ≤ 2 * n ^ 3) (hops : ops ≤ 4 * n ^ 3)
    (htot : dis + ops + adv ≤ 8 * n ^ 3) :
    56 * ops + 32 * adv + 22 * dis + (33 * n + 38) * rel + 2 ≤
      590 * n ^ 3 + 76 * n ^ 2 + 2 := by
  nlinarith

private theorem two_mul_sq (n : ℕ) : 2 * n * n = n * n + n * n := by
  ring

private theorem four_mul_sq (n : ℕ) : 4 * n * n = n * n + n * n + n * n + n * n := by
  ring

private theorem min_reg_exec {r : ℕ} {w : ℕ} (c a b : Fin r) (x : Data r) :
    ExecWithin (B := .standard) w (ram[ if a < b then [ c ← a ] else [ c ← b ] ]) x
      (x.set c (min (x.regs a) (x.regs b))) 3 := by
  by_cases hlt : x.regs a < x.regs b
  · rw [min_eq_left hlt.le]
    refine execWithin_branch_pos (by simp [Cond.holds_lt, hlt]) ?_ le_rfl
    ram_eval
  · rw [min_eq_right (not_lt.mp hlt)]
    refine execWithin_branch_neg (by simp [Cond.holds_lt, hlt]) ?_ le_rfl
    ram_eval

private theorem cut_mono_le (n : ℕ) :
    4 + ((n - 1) * (8 * n + 8 + 2) + 2 + (6 + ((n - 0) * (8 + 2) + 2 +
        (1 + ((n * n - 0) * (7 + 2) + 2))))) ≤
      19 * n * n + 24 * n + 20 := by
  simp only [Nat.sub_zero]
  have h1 : n - 1 ≤ n := Nat.sub_le n 1
  have h2 : (n - 1) * (8 * n + 8 + 2) ≤ n * (8 * n + 10) := Nat.mul_le_mul_right _ h1
  nlinarith

private theorem fin_pair_inj {n : ℕ} {u₁ v₁ u₂ v₂ : Fin n}
    (h : u₁.val * n + v₁.val = u₂.val * n + v₂.val) : u₁ = u₂ ∧ v₁ = v₂ := by
  have hu : u₁.val = u₂.val := by nlinarith [u₁.isLt, v₁.isLt, u₂.isLt, v₂.isLt]
  have hv : v₁.val = v₂.val := by nlinarith
  exact ⟨Fin.ext hu, Fin.ext hv⟩

/-- In-memory representation of a `CAState` (`flow`, `excess`, `height`, `cur`). -/
private structure CAMem (inst : Instance) (s : CAState inst.toNetwork) (mem : ℕ → ℕ) : Prop where
  hflow : ∀ u v : Fin inst.n,
    mem (4 + inst.n * inst.n + (u.val * inst.n + v.val)) = s.pr.flow u v
  hexcess : ∀ v : Fin inst.n, v ≠ inst.s →
    mem (4 + 2 * inst.n * inst.n + v.val) = (s.pr.flow.excess v).toNat
  hheight : ∀ v : Fin inst.n,
    mem (4 + 2 * inst.n * inst.n + inst.n + v.val) = s.pr.height v
  hcur : ∀ v : Fin inst.n, ∃ k ≤ inst.n,
    mem (4 + 2 * inst.n * inst.n + 2 * inst.n + v.val) = k ∧
    s.cur v = (List.finRange inst.n).drop k

private theorem CAMem.of_mem_eq {inst : Instance} {s : CAState inst.toNetwork} {m₁ m₂ : ℕ → ℕ}
    (h : CAMem inst s m₁)
    (hm : ∀ a, 4 + inst.n * inst.n ≤ a → a < 4 + 2 * inst.n * inst.n + 3 * inst.n → m₂ a = m₁ a) :
    CAMem inst s m₂ :=
  { hflow := fun u v => by
      have hlt := List.mul_add_lt_sq u.isLt v.isLt
      exact (hm _ (by omega) (by nlinarith)).trans (h.hflow u v)
    hexcess := fun v hv =>
      (hm _ (by nlinarith [v.isLt]) (by omega)).trans (h.hexcess v hv)
    hheight := fun v =>
      (hm _ (by nlinarith [v.isLt]) (by omega)).trans (h.hheight v)
    hcur := fun v => by
      obtain ⟨k, hk, hm1, hdrop⟩ := h.hcur v
      exact ⟨k, hk, (hm _ (by nlinarith [v.isLt]) (by omega)).trans hm1, hdrop⟩ }

private theorem caMem_unique {inst : Instance} {s₁ s₂ : CAState inst.toNetwork} {m : ℕ → ℕ}
    (h₁ : CAMem inst s₁ m) (h₂ : CAMem inst s₂ m) : s₁ = s₂ := by
  rcases s₁ with ⟨⟨f₁, h₁'⟩, c₁⟩
  rcases s₂ with ⟨⟨f₂, h₂'⟩, c₂⟩
  congr 1
  · congr 1
    · exact Preflow.ext (funext fun u => funext fun v => (h₁.hflow u v).symm.trans (h₂.hflow u v))
    · exact funext fun v => (h₁.hheight v).symm.trans (h₂.hheight v)
  · exact funext fun v => by
      obtain ⟨k₁, _, hm₁, hd₁⟩ := h₁.hcur v
      obtain ⟨k₂, _, hm₂, hd₂⟩ := h₂.hcur v
      exact (hd₁.trans (congrArg (List.drop · _) (hm₁.symm.trans hm₂))).trans hd₂.symm

/-- In-memory representation of the active vertex list `done ++ todo` and cursor `rPos`. -/
private structure OrderMem (inst : Instance) (done todo : List (Fin inst.n)) (x : Data 32) :
    Prop where
  hrPos : x.regs rPos = done.length
  hlen : (done ++ todo).length = inst.n - 2
  hmem : ∀ (i : ℕ) (hi : i < (done ++ todo).length),
    x.mem (4 + 2 * inst.n * inst.n + 3 * inst.n + i) = ((done ++ todo)[i]'hi).val

private theorem OrderMem.of_eq {inst : Instance} {done todo : List (Fin inst.n)} {x y : Data 32}
    (h : OrderMem inst done todo x) (hr : y.regs rPos = x.regs rPos)
    (hm : ∀ i < inst.n - 2,
      y.mem (4 + 2 * inst.n * inst.n + 3 * inst.n + i) =
        x.mem (4 + 2 * inst.n * inst.n + 3 * inst.n + i)) :
    OrderMem inst done todo y :=
  { hrPos := hr.trans h.hrPos
    hlen := h.hlen
    hmem := fun i hi => (hm i (h.hlen ▸ hi)).trans (h.hmem i hi) }

/-- Combined outer invariant at step boundaries of `outerCode`. -/
private structure RTFMem (inst : Instance) (st : RTFState inst.toNetwork) (x : Data 32) : Prop where
  hinv : RTFInv (defaultAdj inst.n) st
  hca : CAMem inst st.ca x.mem
  hord : OrderMem inst st.done st.todo x
  hdis0 : st.discharges = 0
  hadv0 : st.advances = 0

private theorem rtfMem_unique {inst : Instance} {st₁ st₂ : RTFState inst.toNetwork} {x : Data 32}
    (h₁ : RTFMem inst st₁ x) (h₂ : RTFMem inst st₂ x) : st₁ = st₂ := by
  rcases st₁ with ⟨ca₁, done₁, todo₁, dis₁, adv₁⟩
  rcases st₂ with ⟨ca₂, done₂, todo₂, dis₂, adv₂⟩
  have hcat : done₁ ++ todo₁ = done₂ ++ todo₂ :=
    List.ext_getElem (h₁.hord.hlen.trans h₂.hord.hlen.symm) fun i hi₁ hi₂ =>
      Fin.ext ((h₁.hord.hmem i hi₁).symm.trans (h₂.hord.hmem i hi₂))
  obtain ⟨hd, ht⟩ := List.append_inj hcat (h₁.hord.hrPos.symm.trans h₂.hord.hrPos)
  simp only [RTFState.mk.injEq]
  exact ⟨caMem_unique h₁.hca h₂.hca, hd, ht, h₁.hdis0.trans h₂.hdis0.symm,
    h₁.hadv0.trans h₂.hadv0.symm⟩

end Invariants

/-! ### Initialization specifications -/

section Initialization

private theorem setupCode_spec (inst : Instance) {w : ℕ} (hw : Fits w inst.wordBound) :
    ∃ y, ExecWithin w setupCode (Data.init inst.encode) y 20 ∧ CtxInv inst y := by
  have hn : 0 < inst.n := inst.n_pos
  have hf4 : Fits w 4 := fits_of_addr hw (by nlinarith)
  have hfn : Fits w inst.n := fits_of_addr hw (by nlinarith)
  have hfnn : Fits w (inst.n * inst.n) := fits_of_addr hw (by nlinarith)
  have hf2n : Fits w (2 * inst.n) := fits_of_addr hw (by nlinarith)
  have hf_bF : Fits w (4 + inst.n * inst.n) := fits_of_addr hw (by nlinarith)
  have hm1 := inst.init_mem_n (r := 32)
  have hm2 := inst.init_mem_s (r := 32)
  have hm3 := inst.init_mem_t (r := 32)
  refine WP.exists_execWithin ?_
  unfold setupCode
  by_cases hst : inst.s = inst.t
  · have hval : inst.s.val = inst.t.val := congrArg Fin.val hst
    wram_exec [Data.init_regs, hm1, hm2, hm3, hval, hf4, hfn, hfnn, hf2n, hf_bF]
    · exact
        { hzero := by wram_simp
          hone := by wram_simp
          hrTwo := by wram_simp
          hrn := by wram_simp
          hrs := by wram_simp; exact hval.symm
          hrt := by wram_simp
          hrnn := by wram_simp
          hrTwoN := by wram_simp
          hrLim := by wram_simp [hst]
          hrCapBase := by wram_simp
          hbaseF := by wram_simp
          hbaseE := by wram_simp; ring
          hbaseH := by wram_simp; ring
          hbaseC := by wram_simp; ring
          hbaseO := by wram_simp; ring
          houtBase := by wram_simp; ring
          mem_input := fun _ _ => rfl }
    all_goals exact fits_of_addr hw (by nlinarith)
  · have hval : inst.s.val ≠ inst.t.val := fun h => hst (Fin.ext h)
    have hfn2 : Fits w (inst.n - 2) := fits_of_addr hw (by have := Nat.sub_le inst.n 2; nlinarith)
    wram_exec [Data.init_regs, hm1, hm2, hm3, hval, hf4, hfn, hfnn, hf2n, hfn2, hf_bF]
    · exact
        { hzero := by wram_simp
          hone := by wram_simp
          hrTwo := by wram_simp
          hrn := by wram_simp
          hrs := by wram_simp
          hrt := by wram_simp
          hrnn := by wram_simp
          hrTwoN := by wram_simp
          hrLim := by wram_simp [hst]
          hrCapBase := by wram_simp
          hbaseF := by wram_simp
          hbaseE := by wram_simp; ring
          hbaseH := by wram_simp; ring
          hbaseC := by wram_simp; ring
          hbaseO := by wram_simp; ring
          houtBase := by wram_simp; ring
          mem_input := fun _ _ => rfl }
    all_goals exact fits_of_addr hw (by have := Nat.sub_le inst.n 2; nlinarith)

private theorem zeroOutCode_spec (inst : Instance) {w : ℕ} (hw : Fits w inst.wordBound)
    (hst : inst.s = inst.t) {x : Data 32} (hx : CtxInv inst x) :
    ∃ y, ExecWithin w zeroOutCode x y (5 * inst.n * inst.n + 5 * inst.n + 15) ∧
      CtxInv inst y ∧ y.regs acc = inst.maxFlowValue ∧
      outputList y.mem (y.regs outBase) = inst.answerWords := by
  have hn := inst.n_pos
  have hf_sum : Fits w (inst.n + inst.n * inst.n) := fits_of_addr hw (by nlinarith)
  have hf_len : Fits w (inst.n + inst.n * inst.n + 1) := fits_of_addr hw (by nlinarith)
  have hf_out1 : Fits w (4 + 2 * inst.n * inst.n + 4 * inst.n + 1) := fits_of_addr hw (by nlinarith)
  have hf_out2 : Fits w (4 + 2 * inst.n * inst.n + 4 * inst.n + 2) := fits_of_addr hw (by nlinarith)
  have hf_end : Fits w ((4 + 2 * inst.n * inst.n + 4 * inst.n + 2) + (inst.n + inst.n * inst.n)) :=
    fits_of_addr hw (by nlinarith)
  obtain ⟨x₁, hx₁_ex, hx₁_ctx, hx₁_a2, hx₁_v2, hx₁_m0, hx₁_m1⟩ :
      ∃ x₁, ExecWithin w zeroOutPfx x x₁ 7 ∧ CtxInv inst x₁ ∧
        x₁.regs rAddr2 = 4 + 2 * inst.n * inst.n + 4 * inst.n + 2 ∧
        x₁.regs rVal2 = inst.n + inst.n * inst.n ∧
        x₁.mem (4 + 2 * inst.n * inst.n + 4 * inst.n) = 1 + inst.n + inst.n * inst.n ∧
        x₁.mem (4 + 2 * inst.n * inst.n + 4 * inst.n + 1) = 0 := by
    refine WP.exists_execWithin ?_
    unfold zeroOutPfx
    wram_exec [hx.hrn, hx.hrnn, hx.hone, hx.houtBase, hx.hzero, hx.hrTwo,
      hf_sum, hf_len, hf_out1, hf_out2]
    refine ⟨((hx.set (by decide)).set (by decide)).write_ge (by nlinarith) |>.set (by decide)
        |>.write_ge (by nlinarith) |>.set (by decide) |>.set (by decide),
      by wram_simp,
      by wram_simp, ?_, ?_⟩
    · rw [Data.set_mem, Data.set_mem, Data.write_mem_of_ne (by omega), Data.set_mem,
        Data.write_mem_self]
      omega
    · rw [Data.set_mem, Data.set_mem, Data.write_mem_self]
  obtain ⟨x₂, hx₂_ex, hx₂_reg, _, hx₂_mem⟩ :=
    fillConst_exec (r := 32) (w := w) (base := rAddr2) (len := rVal2) (val := zero)
      (one := one) (idx := rIdx) (addr := rAddr) (x := x₁)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hx₁_ctx.hone (by rwa [hx₁_a2, hx₁_v2]) (by rwa [hx₁_v2])
  have hx₂_ctx : CtxInv inst x₂ :=
    hx₁_ctx.of_eq
      (fun i hi => hx₂_reg i (fun h => by subst h; simp at hi) (fun h => by subst h; simp at hi))
      fun a ha => by
        rw [hx₂_mem, fill_of_not_owns fun hown => by
          simp only [Block.Owns] at hown
          rw [hx₁_a2] at hown; nlinarith]
  have hfin : ExecWithin (B := .standard) w (ram[ acc ← zero ]) x₂ (x₂.set acc 0) 1 := by
    ram_eval [hx₂_ctx.hzero]
  set y := x₂.set acc 0
  have hy_ctx : CtxInv inst y := hx₂_ctx.set (by decide)
  have hst' : inst.toNetwork.s = inst.toNetwork.t := hst
  have hout_def : inst.out = ⟨[], Flow.zero inst.toNetwork, ∅, 0, 0⟩ := by
    unfold Instance.out relabelToFrontDense relabelToFront relabelToFrontWith
    rw [ite_eq_left hst']
  have hval0 : inst.maxFlowValue = 0 := by
    simp [Instance.maxFlowValue, hout_def, Network.Flow.value, Network.Flow.netOut,
      Network.Flow.zero]
  refine ⟨y, ((hx₁_ex.seq hx₂_ex.within).seq hfin).mono (by rw [hx₁_v2]; nlinarith), hy_ctx,
    by simp [y, hval0], ?_⟩
  rw [hy_ctx.houtBase]
  have hno {a : ℕ} (ha : a < 4 + 2 * inst.n * inst.n + 4 * inst.n + 2) :
      y.mem a = x₁.mem a := by
    rw [Data.set_mem, hx₂_mem]
    exact fill_of_not_owns fun h => absurd (hx₁_a2 ▸ h.1) (not_le.mpr ha)
  have hyes {k : ℕ} (hk : k < inst.n + inst.n * inst.n) :
      y.mem (4 + 2 * inst.n * inst.n + 4 * inst.n + 2 + k) = 0 := by
    rw [Data.set_mem, hx₂_mem,
      fill_of_owns ⟨hx₁_a2 ▸ Nat.le_add_right _ _, by simp [hx₁_a2, hx₁_v2, hk]⟩]
    exact hx₁_ctx.hzero
  refine outputList_eq_answerWords inst y.mem ((hno (by omega)).trans hx₁_m0)
    ((hno (by omega)).trans (hx₁_m1.trans hval0.symm))
    (fun v => (hyes (lt_add_of_lt_of_nonneg v.isLt (Nat.zero_le _))).trans (by simp [hout_def]))
    (fun u v => ?_)
  rw [Nat.add_assoc (4 + 2 * inst.n * inst.n + 4 * inst.n + 2),
    hyes (Nat.add_lt_add_left (List.mul_add_lt_sq u.isLt v.isLt) _), hout_def]
  rfl

private theorem initNonTermCode_spec (inst : Instance) {w : ℕ} (hw : Fits w inst.wordBound)
    (hst : inst.s ≠ inst.t) {x : Data 32} (hx : CtxInv inst x) :
    ∃ y, ExecWithin w initNonTermCode x y (5 * inst.n * inst.n + 40 * inst.n + 18) ∧
      CtxInv inst y ∧
      RTFMem inst
        (RTFState.init inst.toNetwork (defaultAdj inst.n) (nonTermFin inst.toNetwork)) y := by
  have hn := inst.n_pos
  have hn_sq : inst.n ≤ inst.n * inst.n := Nat.le_mul_self inst.n
  have hs_lt := inst.s.isLt
  have ht_lt := inst.t.isLt
  have h2nn := two_mul_sq inst.n
  have h4nn := four_mul_sq inst.n
  have hf_add1 : Fits w (inst.n * inst.n + 2 * inst.n) := fits_of_addr hw (by omega)
  have hf_len : Fits w (inst.n * inst.n + 3 * inst.n) := fits_of_addr hw (by omega)
  have hf_end : Fits w ((4 + inst.n * inst.n) + (inst.n * inst.n + 3 * inst.n)) :=
    fits_of_addr hw (by omega)
  obtain ⟨x₁, hx₁_ex, hx₁_ctx, hx₁_val, hx₁_mem⟩ :
      ∃ x₁, ExecWithin w initPrefix1 x x₁ 2 ∧ CtxInv inst x₁ ∧
        x₁.regs rVal = inst.n * inst.n + 3 * inst.n ∧ x₁.mem = x.mem := by
    refine WP.exists_execWithin ?_
    unfold initPrefix1
    wram_exec [hx.hrnn, hx.hrTwoN, hx.hrn, hf_add1, hf_len]
    refine ⟨?_, by wram_simp; ring, rfl⟩
    exact (hx.set (by decide)).set (by decide)
  obtain ⟨x₂, hx₂_ex, hx₂_reg, _, hx₂_mem⟩ :=
    fillConst_exec (r := 32) (w := w) (base := baseF) (len := rVal) (val := zero)
      (one := one) (idx := rIdx) (addr := rAddr) (x := x₁)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hx₁_ctx.hone (by rwa [hx₁_ctx.hbaseF, hx₁_val]) (by rwa [hx₁_val])
  have hx₂_ctx : CtxInv inst x₂ :=
    hx₁_ctx.of_eq
      (fun i hi => hx₂_reg i (fun h => by subst h; simp at hi) (fun h => by subst h; simp at hi))
      fun a ha => by
        rw [hx₂_mem,
          fill_of_not_owns
            (fun hown => by simp only [Block.Owns] at hown; rw [hx₁_ctx.hbaseF] at hown; omega),
          hx₁_mem]
  have hx₂_zero : ∀ a, 4 + inst.n * inst.n ≤ a → a < 4 + 2 * inst.n * inst.n + 3 * inst.n →
      x₂.mem a = 0 := fun a ha₁ ha₂ => by
    rw [hx₂_mem,
      fill_of_owns (by simp only [Block.Owns]; rw [hx₁_ctx.hbaseF, hx₁_val]; exact ⟨ha₁, by omega⟩),
      hx₁_ctx.hzero]
  obtain ⟨_, hf_hs, _, _⟩ := fits_vtx hw inst.s
  obtain ⟨hf_sn, _, _, _⟩ := fits_arc hw inst.s inst.s
  obtain ⟨x₃, hx₃_ex, hx₃_ctx, hx₃_a2, hx₃_idx, hx₃_fl, hx₃_ex0, hx₃_ht, hx₃_cu⟩ :
      ∃ x₃, ExecWithin w initMid x₂ x₃ 4 ∧ CtxInv inst x₃ ∧
        x₃.regs rAddr2 = inst.s.val * inst.n ∧ x₃.regs rIdx = 0 ∧
        (∀ u v : Fin inst.n, x₃.mem (4 + inst.n * inst.n + (u.val * inst.n + v.val)) = 0) ∧
        (∀ v : Fin inst.n, x₃.mem (4 + 2 * inst.n * inst.n + v.val) = 0) ∧
        (∀ v : Fin inst.n, x₃.mem (4 + 2 * inst.n * inst.n + inst.n + v.val) =
          Preflow.initialHeight inst.toNetwork v) ∧
        (∀ v : Fin inst.n, x₃.mem (4 + 2 * inst.n * inst.n + 2 * inst.n + v.val) = 0) := by
    refine WP.exists_execWithin ?_
    unfold initMid
    wram_exec [hx₂_ctx.hbaseH, hx₂_ctx.hrs, hx₂_ctx.hrn, hx₂_ctx.hzero, hf_hs, hf_sn]
    refine ⟨((hx₂_ctx.set (by decide)).write_ge (by omega)).set (by decide) |>.set (by decide),
      by wram_simp,
      by wram_simp,
      fun u v => by
        have := List.mul_add_lt_sq u.isLt v.isLt
        exact (Data.write_mem_of_ne (by omega) _).trans (hx₂_zero _ (by omega) (by omega)),
      fun v => by
        have := v.isLt
        exact (Data.write_mem_of_ne (by omega) _).trans (hx₂_zero _ (by omega) (by omega)),
      fun v => ?_,
      fun v => by
        have := v.isLt
        exact (Data.write_mem_of_ne (by omega) _).trans (hx₂_zero _ (by omega) (by omega))⟩
    have := v.isLt
    unfold Preflow.initialHeight
    simp only [Fintype.card_fin, Data.set_mem]
    by_cases hvs : v = inst.s
    · subst hvs
      exact (Data.write_mem_self _ _ _).trans (ite_eq_left rfl).symm
    · rw [Data.write_mem_of_ne (fun h => hvs (Fin.ext (by omega))),
        ite_eq_right (show v ≠ inst.toNetwork.s from hvs)]
      exact hx₂_zero _ (by omega) (by omega)
  -- Loop 1: saturate arcs leaving `s`
  let P1 (k : ℕ) (z : Data 32) : Prop :=
    CtxInv inst z ∧ z.regs rAddr2 = inst.s.val * inst.n ∧
    (∀ u v : Fin inst.n, z.mem (4 + inst.n * inst.n + (u.val * inst.n + v.val)) =
      if u = inst.s ∧ v.val < k then inst.cap u v else 0) ∧
    (∀ v : Fin inst.n, v ≠ inst.s → z.mem (4 + 2 * inst.n * inst.n + v.val) =
      if v.val < k then inst.cap inst.s v else 0) ∧
    (∀ v : Fin inst.n, z.mem (4 + 2 * inst.n * inst.n + inst.n + v.val) =
      Preflow.initialHeight inst.toNetwork v) ∧
    (∀ v : Fin inst.n, z.mem (4 + 2 * inst.n * inst.n + 2 * inst.n + v.val) = 0)
  have hP1_body (z : Data 32) (hz : P1 (z.regs rIdx) z) (hlt : z.regs rIdx < inst.n) :
      ∃ z', ExecWithin w saturateBody z z' 10 ∧ P1 (z.regs rIdx + 1) z' ∧
        z'.regs rIdx = z.regs rIdx + 1 := by
    obtain ⟨hzc, hza2, hzfl, hzex, hzht, hzcu⟩ := hz
    set k := z.regs rIdx
    have hk_def : z.regs rIdx = k := rfl
    let vk : Fin inst.n := ⟨k, hlt⟩
    have hvk_val : vk.val = k := rfl
    have hsnk : inst.s.val * inst.n + k < inst.n * inst.n :=
      List.mul_add_lt_sq inst.s.isLt vk.isLt
    have hcap_mem : z.mem (4 + (inst.s.val * inst.n + k)) = inst.cap inst.s vk :=
      hzc.cap_eq inst.s vk
    have hcap_fit : Fits w (inst.cap inst.s vk) :=
      fits_val_of_le_two_maxCap hw (by have := inst.cap_le_maxCap inst.s vk; omega)
    obtain ⟨_, hf_snk, hf_c, hf_f⟩ := fits_arc hw inst.s vk
    obtain ⟨hf_e, _, _, hf_k1⟩ := fits_vtx hw vk
    have hflow_step : ∀ u v : Fin inst.n,
        Function.update z.mem (4 + inst.n * inst.n + (inst.s.val * inst.n + k))
          (inst.cap inst.s vk) (4 + inst.n * inst.n + (u.val * inst.n + v.val)) =
          if u = inst.s ∧ v.val < k + 1 then inst.cap u v else 0 := fun u v => by
      by_cases huv : u = inst.s ∧ v.val = k
      · obtain ⟨rfl, hvk⟩ := huv
        have hveq : v = vk := Fin.ext hvk
        subst hveq
        simp [vk]
      · rw [Function.update_of_ne (fun h => huv <| by
            obtain ⟨hu, hv⟩ :=
              fin_pair_inj (by omega : u.val * inst.n + v.val = inst.s.val * inst.n + vk.val)
            exact ⟨hu, congrArg Fin.val hv⟩), hzfl u v]
        by_cases hu : u = inst.s
        · simp [hu, le_iff_lt_or_eq, show v.val ≠ k from fun h => huv ⟨hu, h⟩]
        · simp [hu]
    refine WP.exists_execWithin ?_
    unfold saturateBody
    by_cases hks : k = inst.s.val
    · wram_exec [hk_def, hza2, hzc.hrCapBase, hzc.hbaseF, hzc.hrs.trans hks.symm, hzc.hone,
        hcap_mem, hcap_fit, hf_snk, hf_c, hf_f, hf_k1]
      refine ⟨⟨((((hzc.set (by decide)).set (by decide)).set (by decide)).set (by decide)
          |>.write_ge (by omega)).set (by decide) |>.set (by decide),
        by wram_simp [hza2], fun u v => hflow_step u v, fun v hvs => ?_,
        fun v => (Data.write_mem_of_ne (by have := v.isLt; omega) _).trans (hzht v),
        fun v => (Data.write_mem_of_ne (by have := v.isLt; omega) _).trans (hzcu v)⟩,
        by wram_simp⟩
      have := v.isLt
      rw [Data.set_mem, Data.set_mem, Data.write_mem_of_ne (by omega)]
      simp only [Data.set_mem, hzex v hvs]
      simp [le_iff_lt_or_eq, show v.val ≠ k from fun h => hvs (Fin.ext (h.trans hks))]
    · wram_exec [hk_def, hza2, hzc.hrCapBase, hzc.hbaseF, hzc.hbaseE, hzc.hrs, hzc.hone,
        hcap_mem, hcap_fit, hks, hf_snk, hf_c, hf_f, hf_e, hf_k1]
      refine ⟨⟨((((((hzc.set (by decide)).set (by decide)).set (by decide)).set (by decide)
          |>.write_ge (by omega)).set (by decide)).write_ge (by omega)).set (by decide),
        by wram_simp [hza2],
        fun u v => (Data.write_mem_of_ne (by have := List.mul_add_lt_sq u.isLt v.isLt; omega)
          _).trans (hflow_step u v),
        fun v hvs => ?_,
        fun v => (Data.write_mem_of_ne (by have := v.isLt; omega) _).trans
          ((Data.write_mem_of_ne (by have := v.isLt; omega) _).trans (hzht v)),
        fun v => (Data.write_mem_of_ne (by have := v.isLt; omega) _).trans
          ((Data.write_mem_of_ne (by have := v.isLt; omega) _).trans (hzcu v))⟩,
        by wram_simp⟩
      have := v.isLt
      rw [Data.set_mem]
      by_cases hvk : v.val = k
      · simp [show v = vk from Fin.ext hvk, vk]
      · rw [Data.write_mem_of_ne (by omega), Data.set_mem, Data.write_mem_of_ne (by omega)]
        simpa [le_iff_lt_or_eq, hvk] using hzex v hvs
  obtain ⟨x₄, hx₄_ex, hx₄_P, _⟩ := ExecWithin.loop_count P1
    (fun z hz => hz.1.hrn) hP1_body (by omega)
    ⟨hx₃_ctx, hx₃_a2, fun u v => by simpa [hx₃_idx] using hx₃_fl u v,
      fun v _ => by simpa [hx₃_idx] using hx₃_ex0 v, hx₃_ht, hx₃_cu⟩
  rw [hx₃_idx, Nat.sub_zero] at hx₄_ex
  have hx₄_ca : CAMem inst (CAState.init inst.toNetwork (defaultAdj inst.n)) x₄.mem := by
    obtain ⟨_, _, hfl, hex, hht, hcu⟩ := hx₄_P
    exact { hflow := fun u v => by
              rw [hfl u v]
              by_cases hus : u = inst.s <;>
                simp [CAState.init, PushRelabel.init, Preflow.initial, Instance.toNetwork,
                  v.isLt, hus]
            hexcess := fun v hv => by
              rw [hex v hv, ite_eq_left v.isLt]
              simp only [CAState.init, PushRelabel.init]
              rw [initial_excess_eq inst v hv, Int.toNat_natCast]
            hheight := hht
            hcur := fun v => ⟨0, Nat.zero_le _, hcu v, by simp [CAState.init, defaultAdj]⟩ }
  -- Prepare `rPos ← 0; rIdx ← 0` for `buildOrderBody`
  have hprep2 :
      ExecWithin w (ram[ rPos ← zero; rIdx ← zero ] : Code .standard 32) x₄
        ((x₄.set rPos 0).set rIdx 0) 2 := by
    ram_eval [hx₄_P.1.hzero]
  set x₅ := (x₄.set rPos 0).set rIdx 0
  have hx₅_ctx : CtxInv inst x₅ := (hx₄_P.1.set (by decide)).set (by decide)
  -- Loop 2: build `nonTermFin inst.toNetwork`
  let P2 (k : ℕ) (z : Data 32) : Prop :=
    CtxInv inst z ∧ k ≤ inst.n ∧
    CAMem inst (CAState.init inst.toNetwork (defaultAdj inst.n)) z.mem ∧
    (let pfx := ((List.finRange inst.n).take k).filter (fun v => v ≠ inst.s ∧ v ≠ inst.t)
     z.regs rPos = pfx.length ∧
     ∀ (i : ℕ) (hi : i < pfx.length),
       z.mem (4 + 2 * inst.n * inst.n + 3 * inst.n + i) = (pfx[i]'hi).val)
  have hP2_body (z : Data 32) (hz : P2 (z.regs rIdx) z) (hlt : z.regs rIdx < inst.n) :
      ∃ z', ExecWithin w buildOrderBody z z' 8 ∧ P2 (z.regs rIdx + 1) z' ∧
        z'.regs rIdx = z.regs rIdx + 1 := by
    obtain ⟨hzc, hk_le, hzca, hpos, hmem_p⟩ := hz
    set k := z.regs rIdx
    let vk : Fin inst.n := ⟨k, hlt⟩
    let pfx := ((List.finRange inst.n).take k).filter (fun v => v ≠ inst.s ∧ v ≠ inst.t)
    change z.regs rPos = pfx.length at hpos
    have hpfx_le : pfx.length ≤ k :=
      calc pfx.length ≤ ((List.finRange inst.n).take k).length := List.length_filter_le _ _
        _ ≤ k := by simp
    have hpfx_sub : pfx.length ≤ inst.n - 2 := by
      have hsub : pfx.toFinset ⊆ (Finset.univ.erase inst.s).erase inst.t := fun w hw => by
        simp only [pfx, List.mem_toFinset, List.mem_filter, List.mem_take_iff_getElem,
          decide_eq_true_eq] at hw
        exact Finset.mem_erase.mpr ⟨hw.2.2, Finset.mem_erase.mpr ⟨hw.2.1, Finset.mem_univ _⟩⟩
      rw [← List.toFinset_card_of_nodup ((List.nodup_finRange inst.n).take.filter _)]
      calc pfx.toFinset.card
          ≤ ((Finset.univ.erase inst.s).erase inst.t).card := Finset.card_le_card hsub
        _ = inst.n - 2 := by
            rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hst.symm, Finset.mem_univ _⟩),
              Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
            omega
    have htake : ((List.finRange inst.n).take (k + 1)).filter (fun v => v ≠ inst.s ∧ v ≠ inst.t) =
        if vk ≠ inst.s ∧ vk ≠ inst.t then pfx ++ [vk] else pfx := by
      rw [List.take_succ_finRange hlt, List.filter_append]
      by_cases hnt : vk ≠ inst.s ∧ vk ≠ inst.t <;> simp [pfx, vk, hnt]
    obtain ⟨_, _, _, hf_k1⟩ := fits_vtx hw vk
    have hf_o : Fits w (4 + 2 * inst.n * inst.n + 3 * inst.n + pfx.length) :=
      fits_of_addr hw (by omega)
    have hf_pos1 : Fits w (pfx.length + 1) := fits_of_addr hw (by omega)
    have hskip (hnt : ¬ (vk ≠ inst.s ∧ vk ≠ inst.t)) :
        P2 (k + 1) ((z.set rVal (z.regs rVal)).set rIdx (k + 1)) ∧
          ((z.set rVal (z.regs rVal)).set rIdx (k + 1)).regs rIdx = k + 1 := by
      rw [ite_eq_right hnt] at htake
      refine ⟨⟨(hzc.set (by decide)).set (by decide), by omega, hzca,
        by wram_simp [htake, hpos],
        fun i hi => ?_⟩, by wram_simp⟩
      change z.mem _ = _
      rw [List.getElem_of_eq htake hi]
      exact hmem_p i (by simpa only [htake] using hi)
    refine WP.exists_execWithin ?_
    unfold buildOrderBody
    have hk_def : z.regs rIdx = k := rfl
    by_cases hks : k = inst.s.val
    · wram_exec [hk_def, hzc.hrs.trans hks.symm, hzc.hone, hf_k1]
      exact hskip (by simp [show vk = inst.s from Fin.ext hks])
    · by_cases hkt : k = inst.t.val
      · wram_exec [hk_def, hzc.hrs, hzc.hrt.trans hkt.symm, hzc.hone, hks, hf_k1]
        exact hskip (by simp [show vk = inst.t from Fin.ext hkt])
      · have hnt : vk ≠ inst.s ∧ vk ≠ inst.t :=
          ⟨fun h => hks (congrArg Fin.val h), fun h => hkt (congrArg Fin.val h)⟩
        rw [ite_eq_left hnt] at htake
        wram_exec [hk_def, hzc.hrs, hzc.hrt, hzc.hbaseO, hzc.hone, hpos, hks, hkt,
          hf_o, hf_pos1, hf_k1]
        refine ⟨⟨(((hzc.set (by decide)).write_ge (by omega)).set (by decide)).set (by decide),
          by omega, hzca.of_mem_eq fun a _ ha2 => Data.write_mem_of_ne (by omega) _,
          ?_, fun i hi => ?_⟩, by wram_simp⟩
        · rw [htake, List.length_append, List.length_singleton]
          wram_simp
        · have hi' : i < (pfx ++ [vk]).length := htake ▸ hi
          rw [Data.set_mem, Data.set_mem, List.getElem_of_eq htake hi]
          by_cases hil : i < pfx.length
          · rw [Data.write_mem_of_ne (by omega), Data.set_mem, List.getElem_append_left hil]
            exact hmem_p i hil
          · have hieq : i = pfx.length := by
              rw [List.length_append, List.length_singleton] at hi'; omega
            subst hieq
            rw [Data.write_mem_self, List.getElem_append_right le_rfl]
            simp [vk, k]
  obtain ⟨x₆, hx₆_ex, hx₆_P, _⟩ := ExecWithin.loop_count P2
    (fun z hz => hz.1.hrn) hP2_body (Nat.zero_le _)
    ⟨hx₅_ctx, Nat.zero_le _, hx₄_ca, by wram_simp [x₅]; rfl,
      fun _ h => by simp [x₅] at h⟩
  simp only [show x₅.regs rIdx = 0 from by wram_simp [x₅], Nat.sub_zero] at hx₆_ex
  have hfin : ExecWithin (B := .standard) w (ram[ rPos ← zero ]) x₆ (x₆.set rPos 0) 1 := by
    ram_eval [hx₆_P.1.hzero]
  set y := x₆.set rPos 0
  have hy_ctx : CtxInv inst y := hx₆_P.1.set (by decide)
  have hinit_inv : RTFInv (defaultAdj inst.n)
      (RTFState.init inst.toNetwork (defaultAdj inst.n) (nonTermFin inst.toNetwork)) :=
    rtfInv_init (N := inst.toNetwork) hst (nodup_nonTermFin inst.toNetwork)
      (mem_nonTermFin inst.toNetwork)
  have htake_n :
      ((List.finRange inst.n).take inst.n).filter (fun v => v ≠ inst.s ∧ v ≠ inst.t) =
        nonTermFin inst.toNetwork := by
    rw [List.take_of_length_le (by simp)]
    rfl
  refine ⟨y, ((hx₁_ex.seq hx₂_ex.within).seq
      (hx₃_ex.seq (hx₄_ex.seq (hprep2.seq (hx₆_ex.seq hfin))))).mono ?_,
    hy_ctx, ?_⟩
  · rw [hx₁_val]
    nlinarith
  · refine
      { hinv := hinit_inv
        hca := hx₆_P.2.2.1
        hord :=
          { hrPos := by wram_simp [y, RTFState.init]; rfl
            hlen := rtfInv_length_eq hinit_inv hst
            hmem := fun i hi => by
              change x₆.mem _ = ((nonTermFin inst.toNetwork)[i]'hi).val
              rw [List.getElem_of_eq htake_n.symm hi]
              exact hx₆_P.2.2.2.2 i (htake_n.symm ▸ hi) }
        hdis0 := rfl
        hadv0 := rfl }

end Initialization

/-! ### Inner `discharge` lowering -/

section DischargeLowering

private theorem relabelBody_step (inst : Instance) {w : ℕ} (hw : Fits w inst.wordBound)
    {u : Fin inst.n} {s : CAState inst.toNetwork} (hs : CAInv (defaultAdj inst.n) s)
    (_hact : s.pr.flow.IsActive u) :
    let h := s.pr.height
    let S := fun k : ℕ =>
      Finset.univ.filter fun v : Fin inst.n => v.val < k ∧ 0 < s.pr.flow.resCap u v
    ∀ (y : Data 32),
      CtxInv inst y → CAMem inst s y.mem → y.regs rU = u.val → y.regs rIdx < inst.n →
      (∀ (_hk_empty : ¬ (S (y.regs rIdx)).Nonempty), y.regs rMinH = 2 * inst.n) →
      (∀ (hk_ne : (S (y.regs rIdx)).Nonempty), y.regs rMinH = (S (y.regs rIdx)).inf' hk_ne h) →
      ∃ y', ExecWithin w relabelBody y y' 19 ∧
        (∀ i : Fin 32, i.val < 22 → y'.regs i = y.regs i) ∧
        y'.mem = y.mem ∧ y'.regs rIdx = y.regs rIdx + 1 ∧
        (∀ _hk' : ¬ (S (y.regs rIdx + 1)).Nonempty, y'.regs rMinH = 2 * inst.n) ∧
        (∀ hk' : (S (y.regs rIdx + 1)).Nonempty,
          y'.regs rMinH = (S (y.regs rIdx + 1)).inf' hk' h) := by
  intro h S y hyc hyca hyu hlt hm0 hm1
  set k := y.regs rIdx
  have hk_def : y.regs rIdx = k := rfl
  let v : Fin inst.n := ⟨k, hlt⟩
  have hn := inst.n_pos
  obtain ⟨hf_un, hf_unv, hf_c, hf_fuv⟩ := fits_arc hw u v
  obtain ⟨hf_vn, hf_vnu, _, hf_fvu⟩ := fits_arc hw v u
  obtain ⟨_, hf_hv, _, hf_k1⟩ := fits_vtx hw v
  obtain ⟨hf_rem, hf_rc⟩ := fits_resCap hw s.pr.flow u v
  have hcap_uv := hyc.cap_eq u v
  have hfl_uv := hyca.hflow u v
  have hfl_vu := hyca.hflow v u
  have hht_v : y.mem (4 + 2 * inst.n * inst.n + inst.n + v.val) = h v := hyca.hheight v
  have hv_val : v.val = k := rfl
  rw [hv_val] at hf_unv hf_c hf_fuv hf_vn hf_vnu hf_fvu hf_hv hf_k1 hcap_uv hfl_uv hfl_vu hht_v
  have hrc_eq : inst.cap u v - s.pr.flow u v + s.pr.flow v u = s.pr.flow.resCap u v := rfl
  have hS_sub : S (k + 1) = if 0 < s.pr.flow.resCap u v then insert v (S k) else S k := by
    ext w'
    by_cases hwv : w' = v
    · subst hwv
      split_ifs with hpos <;> simp [S, hv_val, hpos]
    · have hne : w'.val ≠ k := fun h => hwv (Fin.ext h)
      split_ifs <;> simp [S, hwv, Nat.le_iff_lt_or_eq, hne]
  unfold relabelBody
  refine WP.exists_execWithin ?_
  by_cases hrc : 0 < s.pr.flow.resCap u v
  · rw [ite_eq_left hrc] at hS_sub
    have hv_le : h v ≤ 2 * inst.n - 1 := (hs.prInv.height_le v).trans (by simp)
    have hne' : (S (k + 1)).Nonempty := hS_sub ▸ ⟨v, Finset.mem_insert_self _ _⟩
    have h_new (hS : (S k).Nonempty) :
        (S (k + 1)).inf' hne' h = min (h v) ((S k).inf' hS h) := by
      simp only [hS_sub]
      rw [Finset.inf'_insert (H := hS), min_comm]
    by_cases hlt_m : h v < y.regs rMinH
    · wram_exec [hyu, hyc.hrn, hyc.hrCapBase, hyc.hbaseF, hyc.hzero, hyc.hbaseH, hyc.hone,
        hk_def, hcap_uv, hfl_uv, hfl_vu, hrc_eq, s.pr.flow.le_cap u v,
        hrc, hht_v, hlt_m,
        hf_un, hf_unv, hf_c, hf_fuv, hf_rem, hf_vn, hf_vnu, hf_fvu, hf_rc, hf_hv, hf_k1]
      refine ⟨fun i hi => by
          repeat rw [set_regs_lt hi (by decide)],
        rfl, by wram_simp, fun hk' => absurd hne' hk', fun _ => ?_⟩
      by_cases hS : (S k).Nonempty
      · have hm := hm1 hS
        rw [h_new hS, min_eq_left (by omega)]
        wram_simp
      · have hS_eq : S (k + 1) = {v} := by rw [hS_sub, Finset.not_nonempty_iff_eq_empty.mp hS]; rfl
        simp only [hS_eq, Finset.inf'_singleton]
        wram_simp
    · have hS : (S k).Nonempty := by_contra fun hS => by have := hm0 hS; omega
      have hm := hm1 hS
      wram_exec [hyu, hyc.hrn, hyc.hrCapBase, hyc.hbaseF, hyc.hzero, hyc.hbaseH, hyc.hone,
        hk_def, hcap_uv, hfl_uv, hfl_vu, hrc_eq, s.pr.flow.le_cap u v,
        hrc, hht_v, hlt_m,
        hf_un, hf_unv, hf_c, hf_fuv, hf_rem, hf_vn, hf_vnu, hf_fvu, hf_rc, hf_hv, hf_k1]
      refine ⟨fun i hi => by
          repeat rw [set_regs_lt hi (by decide)],
        rfl, by wram_simp, fun hk' => absurd hne' hk', fun _ => ?_⟩
      rw [h_new hS, min_eq_right (by omega), ← hm]
      wram_simp
  · rw [ite_eq_right hrc] at hS_sub
    have hrc0 : s.pr.flow.resCap u v = 0 := by omega
    wram_exec [hyu, hyc.hrn, hyc.hrCapBase, hyc.hbaseF, hyc.hzero, hyc.hone,
      hk_def, hcap_uv, hfl_uv, hfl_vu, hrc_eq, s.pr.flow.le_cap u v, hrc0,
      hf_un, hf_unv, hf_c, hf_fuv, hf_rem, hf_vn, hf_vnu, hf_fvu, hf_rc, hf_k1]
    refine ⟨fun i hi => by
        repeat rw [set_regs_lt hi (by decide)],
      rfl,
      by wram_simp,
      fun hk' => by wram_simp [hm0 (hS_sub ▸ hk')], fun hk' => ?_⟩
    simp only [hS_sub] at hk' ⊢
    wram_simp [hm1 hk']

private theorem relabelCode_spec (inst : Instance) {w : ℕ} (hw : Fits w inst.wordBound)
    {u : Fin inst.n} {s : CAState inst.toNetwork} (hs : CAInv (defaultAdj inst.n) s)
    (hact : s.pr.flow.IsActive u) (hcu : s.cur u = [])
    {x : Data 32} (hx : CtxInv inst x) (hxca : CAMem inst s x.mem)
    (hxu : x.regs rU = u.val) (hxex : x.regs rEx = (s.pr.flow.excess u).toNat) :
    ∃ y, ExecWithin w relabelCode x y (21 * inst.n + 11) ∧
      CtxInv inst y ∧
      CAMem inst ⟨s.pr.apply (.relabel u), Function.update s.cur u (defaultAdj inst.n u)⟩ y.mem ∧
      y.regs rPos = x.regs rPos ∧ y.regs rU = u.val ∧ y.regs rRel = 1 ∧
      y.regs rCur = 0 ∧ y.regs rEx = (s.pr.flow.excess u).toNat ∧
      y.regs rHU = (s.pr.apply (.relabel u)).height u ∧
      (∀ a, a ≠ 4 + 2 * inst.n * inst.n + inst.n + u.val →
        a ≠ 4 + 2 * inst.n * inst.n + 2 * inst.n + u.val → y.mem a = x.mem a) := by
  have hn := inst.n_pos
  let S := fun k : ℕ =>
    Finset.univ.filter fun v : Fin inst.n => v.val < k ∧ 0 < s.pr.flow.resCap u v
  have hprep : ExecWithin (B := .standard) w (ram[ rMinH ← rTwoN; rIdx ← zero ]) x
      ((x.set rMinH (2 * inst.n)).set rIdx 0) 2 := by
    ram_eval [hx.hrTwoN, hx.hzero]
  set x₁ := (x.set rMinH (2 * inst.n)).set rIdx 0
  have hx₁_ctx : CtxInv inst x₁ := (hx.set (by decide)).set (by decide)
  let P (k : ℕ) (z : Data 32) : Prop :=
    CtxInv inst z ∧ z.mem = x.mem ∧ z.regs rU = u.val ∧ z.regs rPos = x.regs rPos ∧
    z.regs rEx = (s.pr.flow.excess u).toNat ∧
    (∀ hk_e : ¬ (S k).Nonempty, z.regs rMinH = 2 * inst.n) ∧
    (∀ hk_ne : (S k).Nonempty, z.regs rMinH = (S k).inf' hk_ne s.pr.height)
  have hbody (z : Data 32) (hz : P (z.regs rIdx) z) (hlt : z.regs rIdx < inst.n) :
      ∃ z', ExecWithin w relabelBody z z' 19 ∧ P (z.regs rIdx + 1) z' ∧
        z'.regs rIdx = z.regs rIdx + 1 := by
    obtain ⟨hzc, hzmem, hzu, hzpos, hzex, hzm0, hzm1⟩ := hz
    obtain ⟨z', hz'_ex, hz'_reg, hz'_mem, hz'_idx, hz'_m0, hz'_m1⟩ :=
      relabelBody_step inst hw hs hact z hzc (hzmem ▸ hxca) hzu hlt hzm0 hzm1
    have hz'_ctx : CtxInv inst z' :=
      hzc.of_eq (fun i hi => hz'_reg i (by omega)) (fun _ _ => by rw [hz'_mem])
    refine ⟨z', hz'_ex, ⟨hz'_ctx, hz'_mem.trans hzmem,
      (hz'_reg rU (by decide)).trans hzu,
      (hz'_reg rPos (by decide)).trans hzpos,
      (hz'_reg rEx (by decide)).trans hzex,
      hz'_m0, hz'_m1⟩, hz'_idx⟩
  have hx₁_P : P (x₁.regs rIdx) x₁ :=
    ⟨hx₁_ctx, rfl, by wram_simp [x₁, hxu], by wram_simp [x₁], by wram_simp [x₁, hxex],
      fun _ => by wram_simp [x₁], fun h => by
        exfalso; obtain ⟨w, hw⟩ := h; simp [S, x₁] at hw⟩
  obtain ⟨x₂, hx₂_ex, hx₂_P, hx₂_idx⟩ := ExecWithin.loop_count P
    (fun z hz => hz.1.hrn) hbody (by simp [x₁]) hx₁_P
  simp only [show x₁.regs rIdx = 0 from by simp [x₁], Nat.sub_zero] at hx₂_ex
  obtain ⟨hx₂_ctx, hx₂_mem, hx₂_u, hx₂_pos, hx₂_exr, _, hx₂_m1⟩ := hx₂_P
  have hSn : S inst.n = s.pr.flow.resNbrs u := by
    ext v
    simp [S, Preflow.resNbrs]
  have hne : (s.pr.flow.resNbrs u).Nonempty := s.pr.flow.resNbrs_nonempty hact.2.2
  have hm_eq : x₂.regs rMinH = (s.pr.flow.resNbrs u).inf' hne s.pr.height := by
    simpa only [hSn] using hx₂_m1 (hSn ▸ hne)
  obtain ⟨hs', _⟩ := discharge_relabel_step (adjValid_defaultAdj inst.toNetwork) hs hact hcu
  have hnew_ht :
      (s.pr.apply (.relabel u)).height u = (s.pr.flow.resNbrs u).inf' hne s.pr.height + 1 := by
    change s.pr.flow.relabel s.pr.height u u = _
    rw [Preflow.relabel_self]
    simp [Preflow.relabelHeight, hne]
  have hnew_le : (s.pr.flow.resNbrs u).inf' hne s.pr.height + 1 ≤ 2 * inst.n - 1 :=
    hnew_ht ▸ (hs'.prInv.height_le u).trans (by simp)
  obtain ⟨_, hf_hu, hf_cu, _⟩ := fits_vtx hw u
  have hf_hval : Fits w ((s.pr.flow.resNbrs u).inf' hne s.pr.height + 1) :=
    fits_of_addr hw (by omega)
  obtain ⟨y, hy_ex, hy_ctx, hy_pos, hy_u, hy_rel, hy_cur, hy_exr, hy_hu, hy_mem⟩ :
      ∃ y, ExecWithin w relabelTail x₂ y 7 ∧ CtxInv inst y ∧
        y.regs rPos = x.regs rPos ∧ y.regs rU = u.val ∧ y.regs rRel = 1 ∧
        y.regs rCur = 0 ∧ y.regs rEx = (s.pr.flow.excess u).toNat ∧
        y.regs rHU = (s.pr.apply (.relabel u)).height u ∧
        y.mem = Function.update (Function.update x.mem (4 + 2 * inst.n * inst.n + inst.n + u.val)
            ((s.pr.apply (.relabel u)).height u))
          (4 + 2 * inst.n * inst.n + 2 * inst.n + u.val) 0 := by
    refine WP.exists_execWithin ?_
    unfold relabelTail
    wram_exec [hm_eq, hx₂_ctx.hone, hx₂_ctx.hbaseH, hx₂_u, hx₂_ctx.hbaseC, hx₂_ctx.hzero,
      hf_hval, hf_hu, hf_cu]
    exact ⟨((((((hx₂_ctx.set (by decide)).set (by decide)).write_ge (by nlinarith)).set
        (by decide)).write_ge (by nlinarith)).set (by decide)).set (by decide),
      by wram_simp [hx₂_pos],
      by wram_simp [hx₂_u],
      by wram_simp,
      by wram_simp,
      by wram_simp [hx₂_exr],
      by wram_simp [hnew_ht],
      by
        rw [← hx₂_mem, hnew_ht]
        rfl⟩
  have hmem_out : ∀ a, a ≠ 4 + 2 * inst.n * inst.n + inst.n + u.val →
      a ≠ 4 + 2 * inst.n * inst.n + 2 * inst.n + u.val → y.mem a = x.mem a := fun a ha1 ha2 => by
    rw [hy_mem, Function.update_of_ne ha2, Function.update_of_ne ha1]
  refine ⟨y, (hprep.seq (hx₂_ex.seq hy_ex)).mono (by omega), hy_ctx, ?_,
    hy_pos, hy_u, hy_rel, hy_cur, hy_exr, hy_hu, hmem_out⟩
  exact
    { hflow := fun a b => by
        have := two_mul_sq inst.n
        have := List.mul_add_lt_sq a.isLt b.isLt
        rw [hmem_out _ (by omega) (by omega)]
        exact hxca.hflow a b
      hexcess := fun v hv => by
        have := v.isLt
        rw [hmem_out _ (by nlinarith) (by nlinarith)]
        exact hxca.hexcess v hv
      hheight := fun v => by
        by_cases hvu : v = u
        · subst hvu
          rw [hy_mem, Function.update_of_ne (by omega), Function.update_self]
        · have := v.isLt
          have := u.isLt
          rw [hmem_out _ (fun h => hvu (Fin.ext (by omega))) (by omega), hxca.hheight v]
          exact (Preflow.relabel_of_ne _ _ hvu).symm
      hcur := fun v => by
        by_cases hvu : v = u
        · subst hvu
          exact ⟨0, Nat.zero_le _, by rw [hy_mem, Function.update_self], by simp [defaultAdj]⟩
        · obtain ⟨k, hk, hkm, hdrop⟩ := hxca.hcur v
          have := v.isLt
          have := u.isLt
          exact ⟨k, hk, (hmem_out _ (by omega) (fun h => hvu (Fin.ext (by omega)))).trans hkm,
            by simpa [Function.update_of_ne hvu] using hdrop⟩ }

private theorem resCapCode_spec (inst : Instance) {w : ℕ} (hw : Fits w inst.wordBound)
    {u v : Fin inst.n} {s : CAState inst.toNetwork} {x : Data 32}
    (hx : CtxInv inst x) (hxca : CAMem inst s x.mem)
    (hxu : x.regs rU = u.val) (hxcur : x.regs rCur = v.val) :
    ∃ y, ExecWithin w resCapCode x y 12 ∧
      (∀ i : Fin 32, i.val < 25 → y.regs i = x.regs i) ∧
      y.mem = x.mem ∧ y.regs rRc = s.pr.flow.resCap u v := by
  obtain ⟨hf_un, hf_unv, hf_c, hf_fuv⟩ := fits_arc hw u v
  obtain ⟨hf_vn, hf_vnu, _, hf_fvu⟩ := fits_arc hw v u
  obtain ⟨hf_rem, hf_rc⟩ := fits_resCap hw s.pr.flow u v
  have hrc_eq : inst.cap u v - s.pr.flow u v + s.pr.flow v u = s.pr.flow.resCap u v := rfl
  refine WP.exists_execWithin ?_
  unfold resCapCode
  wram_exec [hxu, hx.hrn, hxcur, hx.hrCapBase, hx.hbaseF, hx.cap_eq u v,
    hxca.hflow u v, hxca.hflow v u, s.pr.flow.le_cap u v, hrc_eq,
    hf_un, hf_unv, hf_c, hf_fuv, hf_rem, hf_vn, hf_vnu, hf_fvu, hf_rc]
  exact ⟨fun i hi => by repeat rw [set_regs_lt hi (by decide)], rfl, by wram_simp⟩

private theorem admissibleCode_spec (inst : Instance) {w : ℕ} (hw : Fits w inst.wordBound)
    {u v : Fin inst.n} {s : CAState inst.toNetwork} (hs : CAInv (defaultAdj inst.n) s)
    {x : Data 32} (hx : CtxInv inst x) (hxca : CAMem inst s x.mem)
    (hxu : x.regs rU = u.val) (hxcur : x.regs rCur = v.val)
    (hxhu : x.regs rHU = s.pr.height u) :
    ∃ y, ExecWithin w admissibleCode x y 19 ∧
      (∀ i : Fin 32, i.val < 25 → y.regs i = x.regs i) ∧
      y.mem = x.mem ∧ y.regs rRc = s.pr.flow.resCap u v ∧
      y.regs rVal2 =
        if 0 < s.pr.flow.resCap u v ∧ s.pr.height u = s.pr.height v + 1 then 1 else 0 := by
  obtain ⟨x₁, hx₁_ex, hx₁_reg, hx₁_mem, hx₁_rc⟩ :=
    resCapCode_spec inst hw hx hxca hxu hxcur
  have hx₁_ctx : CtxInv inst x₁ :=
    hx.of_eq (fun i hi => hx₁_reg i (by omega)) (fun _ _ => by rw [hx₁_mem])
  have hx₁_hu : x₁.regs rHU = s.pr.height u := (hx₁_reg rHU (by decide)).trans hxhu
  have hx₁_cur : x₁.regs rCur = v.val := (hx₁_reg rCur (by decide)).trans hxcur
  have hx₁_hv : x₁.mem (4 + 2 * inst.n * inst.n + inst.n + v.val) = s.pr.height v :=
    hx₁_mem ▸ hxca.hheight v
  have hv_le : s.pr.height v ≤ 2 * inst.n - 1 := (hs.prInv.height_le v).trans (by simp)
  obtain ⟨_, hf_hv, _, _⟩ := fits_vtx hw v
  have hf_hv1 : Fits w (s.pr.height v + 1) :=
    fits_of_addr hw (by have := Nat.sub_le (2 * inst.n) 1; nlinarith)
  obtain ⟨y, hy_ex, hy_reg, hy_mem, hy_rc, hy_v2⟩ :
      ∃ y, ExecWithin w admissibleTail x₁ y 7 ∧
        (∀ i : Fin 32, i.val < 25 → y.regs i = x₁.regs i) ∧
        y.mem = x₁.mem ∧ y.regs rRc = s.pr.flow.resCap u v ∧
        y.regs rVal2 =
          if 0 < s.pr.flow.resCap u v ∧ s.pr.height u = s.pr.height v + 1 then 1 else 0 := by
    refine WP.exists_execWithin ?_
    unfold admissibleTail
    by_cases hrc : 0 < s.pr.flow.resCap u v
    · by_cases heq : s.pr.height u = s.pr.height v + 1 <;>
        (wram_exec [hx₁_ctx.hzero, hx₁_rc, hrc, hx₁_ctx.hbaseH, hx₁_cur, hx₁_hv, hx₁_ctx.hone,
            hx₁_hu, heq, hf_hv, hf_hv1]
         exact ⟨fun i hi => by
             repeat rw [set_regs_lt hi (by decide)],
           rfl,
           by wram_simp [hx₁_rc],
           by wram_simp [hrc, heq]⟩)
    · have hrc0 : s.pr.flow.resCap u v = 0 := by omega
      wram_exec [hx₁_ctx.hzero, hx₁_rc, hrc0]
      exact ⟨fun i hi => by repeat rw [set_regs_lt hi (by decide)],
        rfl, by wram_simp [hx₁_rc], by simp [hrc]⟩
  exact ⟨y, (hx₁_ex.seq hy_ex).mono (by omega), fun i hi => (hy_reg i hi).trans (hx₁_reg i hi),
    hy_mem.trans hx₁_mem, hy_rc, hy_v2⟩

private theorem pushBody_spec (inst : Instance) {w : ℕ} (hw : Fits w inst.wordBound)
    {u v : Fin inst.n} {s : CAState inst.toNetwork} (_hs : CAInv (defaultAdj inst.n) s)
    (hact : s.pr.flow.IsActive u)
    (hadm : 0 < s.pr.flow.resCap u v ∧ s.pr.height u = s.pr.height v + 1)
    {x : Data 32} (hx : CtxInv inst x) (hxca : CAMem inst s x.mem)
    (hxu : x.regs rU = u.val) (hxcur : x.regs rCur = v.val)
    (hxex : x.regs rEx = (s.pr.flow.excess u).toNat) (hxrc : x.regs rRc = s.pr.flow.resCap u v) :
    ∃ y, ExecWithin w pushBody x y 28 ∧ CtxInv inst y ∧
      CAMem inst ⟨s.pr.apply (.push u v), s.cur⟩ y.mem ∧
      y.regs rPos = x.regs rPos ∧ y.regs rU = u.val ∧ y.regs rRel = x.regs rRel ∧
      y.regs rCur = v.val ∧ y.regs rHU = x.regs rHU ∧
      y.regs rEx = ((s.pr.apply (.push u v)).flow.excess u).toNat ∧
      (∀ a, 4 + 2 * inst.n * inst.n + inst.n ≤ a → y.mem a = x.mem a) := by
  have hn := inst.n_pos
  have hn_sq : inst.n ≤ inst.n * inst.n := Nat.le_mul_self inst.n
  have h2nn := two_mul_sq inst.n
  have h4nn := four_mul_sq inst.n
  have hu_lt := u.isLt
  have hv_lt := v.isLt
  have huv_sq := List.mul_add_lt_sq u.isLt v.isLt
  have hvu_sq := List.mul_add_lt_sq v.isLt u.isLt
  have huv : u ≠ v := (⟨hact, hadm.1, hadm.2⟩ : s.pr.flow.CanPush s.pr.height u v).ne
  let δ := s.pr.flow.pushAmount u v
  let rev := min δ (s.pr.flow v u)
  have hδ_le_ex : δ ≤ (s.pr.flow.excess u).toNat := min_le_left _ _
  have hrev_le_δ : rev ≤ δ := min_le_left _ _
  have hrev_le_fvu : rev ≤ s.pr.flow v u := min_le_right _ _
  have hnew_fuv : s.pr.flow u v + (δ - rev) = (s.pr.flow.push u v) u v := by
    change _ = Preflow.pushFun s.pr.flow u v δ u v
    simp [Preflow.pushFun, rev]
  have hnew_fvu : s.pr.flow v u - rev = (s.pr.flow.push u v) v u := by
    change _ = Preflow.pushFun s.pr.flow u v δ v u
    simp [Preflow.pushFun, huv, huv.symm, rev]
  have hexu_new : (s.pr.flow.excess u).toNat - δ = ((s.pr.flow.push u v).excess u).toNat := by
    have := s.pr.flow.excess_nonneg hact.1
    have := s.pr.flow.excess_push_self huv
    omega
  obtain ⟨hf_vn, hf_vnu, _, hf_fvu⟩ := fits_arc hw v u
  obtain ⟨hf_un, hf_unv, _, hf_fuv⟩ := fits_arc hw u v
  obtain ⟨hf_eu, _, _, _⟩ := fits_vtx hw u
  obtain ⟨hf_ev, _, _, _⟩ := fits_vtx hw v
  have hf_fvu_new : Fits w (s.pr.flow v u - rev) := fits_val_of_le_two_maxCap hw (by
    have := (s.pr.flow.le_cap v u).trans (inst.cap_le_maxCap v u)
    omega)
  have hf_rem : Fits w (δ - rev) := fits_val_of_le_two_maxCap hw (by
    have : δ ≤ s.pr.flow.resCap u v := min_le_right _ _
    have := resCap_le_two_maxCap inst s.pr.flow u v
    omega)
  have hf_fuv_new : Fits w (s.pr.flow u v + (δ - rev)) := fits_val_of_le_two_maxCap hw (by
    have h1 := ((s.pr.flow.push u v).le_cap u v).trans (inst.cap_le_maxCap u v)
    rw [← hnew_fuv] at h1; omega)
  have hf_exu_new : Fits w ((s.pr.flow.excess u).toNat - δ) :=
    fits_val_of_le_n_maxCap hw
      (hexu_new.symm ▸ preflow_excess_le inst (s.pr.flow.push u v) u hact.1)
  have hfl_vu_mem : x.mem (4 + inst.n * inst.n + (v.val * inst.n + u.val)) = s.pr.flow v u :=
    hxca.hflow v u
  have hfl_uv_mem :
      Function.update x.mem (4 + inst.n * inst.n + (v.val * inst.n + u.val)) (s.pr.flow v u - rev)
        (4 + inst.n * inst.n + (u.val * inst.n + v.val)) = s.pr.flow u v := by
    rw [Function.update_of_ne (fun h =>
      huv (fin_pair_inj (by omega : u.val * inst.n + v.val = v.val * inst.n + u.val)).1),
      hxca.hflow u v]
  have hd_ex : ExecWithin w pushDeltaCode x (x.set rDelta δ) 3 := by
    have hmin := min_reg_exec (w := w) rDelta rEx rRc x
    rwa [hxex, hxrc] at hmin
  set d₁ := x.set rDelta δ
  have hd₁_ctx : CtxInv inst d₁ := hx.set (by decide)
  obtain ⟨d₂, hm1_ex', hd₂_ctx, hd₂_mem, hd₂_pos, hd₂_u, hd₂_rel, hd₂_cur, hd₂_hu, hd₂_exr,
      hd₂_delta, hd₂_a2, hd₂_val⟩ :
      ∃ d₂, ExecWithin w pushMid1 d₁ d₂ 4 ∧ CtxInv inst d₂ ∧
        d₂.mem = x.mem ∧ d₂.regs rPos = x.regs rPos ∧ d₂.regs rU = u.val ∧
        d₂.regs rRel = x.regs rRel ∧ d₂.regs rCur = v.val ∧ d₂.regs rHU = x.regs rHU ∧
        d₂.regs rEx = (s.pr.flow.excess u).toNat ∧ d₂.regs rDelta = δ ∧
        d₂.regs rAddr2 = 4 + inst.n * inst.n + (v.val * inst.n + u.val) ∧
        d₂.regs rVal = s.pr.flow v u := by
    refine WP.exists_execWithin ?_
    unfold pushMid1
    wram_exec [hd₁_ctx.hrn, hd₁_ctx.hbaseF,
      show d₁.mem (4 + inst.n * inst.n + (v.val * inst.n + u.val)) = s.pr.flow v u from hfl_vu_mem,
      hf_vn, hf_vnu, hf_fvu,
      show d₁.regs rCur = v.val from by wram_simp [d₁, hxcur],
      show d₁.regs rU = u.val from by wram_simp [d₁, hxu]]
    exact ⟨(((hd₁_ctx.set (by decide)).set (by decide)).set (by decide)).set (by decide), rfl,
      by wram_simp [d₁], by wram_simp [d₁, hxu], by wram_simp [d₁], by wram_simp [d₁, hxcur],
      by wram_simp [d₁], by wram_simp [d₁, hxex], by wram_simp [d₁], by wram_simp, by wram_simp⟩
  have hr_ex : ExecWithin w pushRevCode d₂ (d₂.set rRev rev) 3 := by
    have hmin := min_reg_exec (w := w) rRev rDelta rVal d₂
    rwa [hd₂_delta, hd₂_val] at hmin
  set d₃ := d₂.set rRev rev
  have hd₃_ctx : CtxInv inst d₃ := hd₂_ctx.set (by decide)
  obtain ⟨x₁, hm2_ex', hx₁_ctx, hx₁_pos, hx₁_u, hx₁_rel, hx₁_cur, hx₁_hu, hx₁_delta, hx₁_exr,
      hx₁_mem⟩ :
      ∃ x₁, ExecWithin w pushMid2 d₃ x₁ 12 ∧ CtxInv inst x₁ ∧
        x₁.regs rPos = x.regs rPos ∧ x₁.regs rU = u.val ∧ x₁.regs rRel = x.regs rRel ∧
        x₁.regs rCur = v.val ∧ x₁.regs rHU = x.regs rHU ∧ x₁.regs rDelta = δ ∧
        x₁.regs rEx = ((s.pr.apply (.push u v)).flow.excess u).toNat ∧
        x₁.mem = Function.update (Function.update (Function.update x.mem
            (4 + inst.n * inst.n + (v.val * inst.n + u.val)) (s.pr.flow.push u v v u))
            (4 + inst.n * inst.n + (u.val * inst.n + v.val)) (s.pr.flow.push u v u v))
          (4 + 2 * inst.n * inst.n + u.val) ((s.pr.flow.push u v).excess u).toNat := by
    refine WP.exists_execWithin ?_
    unfold pushMid2
    have hfl_uv_d₃ :
        Function.update d₃.mem (4 + inst.n * inst.n + (v.val * inst.n + u.val))
          (s.pr.flow v u - rev) (4 + inst.n * inst.n + (u.val * inst.n + v.val)) =
          s.pr.flow u v :=
      hd₂_mem ▸ hfl_uv_mem
    have hfl_uv_push :
        Function.update x.mem (4 + inst.n * inst.n + (v.val * inst.n + u.val))
          (s.pr.flow.push u v v u) (4 + inst.n * inst.n + (u.val * inst.n + v.val)) =
          s.pr.flow u v := by
      simpa [← hnew_fvu] using hfl_uv_mem
    wram_exec [hd₃_ctx.hrn, hd₃_ctx.hbaseF, hd₃_ctx.hbaseE,
      show d₃.regs rVal = s.pr.flow v u from by wram_simp [d₃, hd₂_val],
      show d₃.regs rRev = rev from by wram_simp [d₃],
      show d₃.regs rAddr2 = 4 + inst.n * inst.n + (v.val * inst.n + u.val) from
        by wram_simp [d₃, hd₂_a2],
      show d₃.regs rDelta = δ from by wram_simp [d₃, hd₂_delta],
      show d₃.regs rU = u.val from by wram_simp [d₃, hd₂_u],
      show d₃.regs rCur = v.val from by wram_simp [d₃, hd₂_cur],
      show d₃.regs rEx = (s.pr.flow.excess u).toNat from by wram_simp [d₃, hd₂_exr],
      hfl_uv_d₃, hrev_le_fvu, hrev_le_δ, hδ_le_ex, hnew_fvu, hnew_fuv, hexu_new,
      hf_fvu_new, hf_rem, hf_un, hf_unv, hf_fuv, hf_fuv_new, hf_exu_new, hf_eu]
    · refine ⟨(((((((((hd₃_ctx.set (by decide)).write_ge (by omega)).set (by decide)).set
          (by decide)).set (by decide)).set (by decide)).set (by decide)).set (by decide)
          |>.write_ge (by omega)).set (by decide)).set (by decide) |>.write_ge
          (baseF_le_baseE inst.n u.val),
        by wram_simp [d₃, hd₂_pos],
        by wram_simp [d₃, hd₂_u],
        by wram_simp [d₃, hd₂_rel],
        by wram_simp [d₃, hd₂_cur],
        by wram_simp [d₃, hd₂_hu],
        by wram_simp [d₃, hd₂_delta],
        by
          wram_simp [hexu_new]
          rfl, ?_⟩
      simp only [Data.set_mem, Data.write_mem]
      rw [show d₃.mem = x.mem from hd₂_mem, hfl_uv_push, hnew_fuv]
    · simp only [Data.set_mem, Data.write_mem, show d₃.mem = x.mem from hd₂_mem]
      rw [hfl_uv_push]
      exact hf_fuv_new
  have hx₁_ex : ExecWithin w pushPart1 x x₁ 22 :=
    (hd_ex.seq (hm1_ex'.seq (hr_ex.seq hm2_ex'))).mono (by omega)
  obtain ⟨y, hy_ex, hy_ctx, hy_ca, hy_pos, hy_u, hy_rel, hy_cur, hy_hu, hy_exr, hy_out⟩ :
      ∃ y, ExecWithin w pushTail x₁ y 6 ∧ CtxInv inst y ∧
        CAMem inst ⟨s.pr.apply (.push u v), s.cur⟩ y.mem ∧
        y.regs rPos = x.regs rPos ∧ y.regs rU = u.val ∧ y.regs rRel = x.regs rRel ∧
        y.regs rCur = v.val ∧ y.regs rHU = x.regs rHU ∧
        y.regs rEx = ((s.pr.apply (.push u v)).flow.excess u).toNat ∧
        (∀ a, 4 + 2 * inst.n * inst.n + inst.n ≤ a → y.mem a = x.mem a) := by
    have hpost_push (mem : ℕ → ℕ)
        (hagree : ∀ a, (a < 4 + 2 * inst.n * inst.n ∨ 4 + 2 * inst.n * inst.n + inst.n ≤ a) →
          mem a = x₁.mem a)
        (hex : ∀ w : Fin inst.n, w ≠ inst.s →
          mem (4 + 2 * inst.n * inst.n + w.val) = ((s.pr.flow.push u v).excess w).toNat) :
        CAMem inst ⟨s.pr.apply (.push u v), s.cur⟩ mem ∧
          ∀ a, 4 + 2 * inst.n * inst.n + inst.n ≤ a → mem a = x.mem a := by
      have htop_eq : ∀ a, 4 + 2 * inst.n * inst.n + inst.n ≤ a → mem a = x.mem a := fun a ha => by
        rw [hagree _ (Or.inr ha), hx₁_mem, Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      refine ⟨{ hflow := fun a b => by
                  have := List.mul_add_lt_sq a.isLt b.isLt
                  rw [hagree _ (Or.inl (by omega)), hx₁_mem, Function.update_of_ne (by omega)]
                  by_cases hab : a = u ∧ b = v
                  · obtain ⟨rfl, rfl⟩ := hab
                    rw [Function.update_self]; rfl
                  · rw [Function.update_of_ne fun h => hab (fin_pair_inj (by omega))]
                    by_cases hba : a = v ∧ b = u
                    · obtain ⟨rfl, rfl⟩ := hba
                      rw [Function.update_self]; rfl
                    · rw [Function.update_of_ne fun h => hba (fin_pair_inj (by omega)),
                        hxca.hflow a b]
                      change s.pr.flow a b = Preflow.pushFun s.pr.flow u v δ a b
                      simp [Preflow.pushFun, hab, hba]
                hexcess := hex
                hheight := fun w => (htop_eq _ (by omega)).trans (hxca.hheight w)
                hcur := fun w => by
                  obtain ⟨k, hk, hkm, hdrop⟩ := hxca.hcur w
                  exact ⟨k, hk, (htop_eq _ (by omega)).trans hkm, hdrop⟩ }, htop_eq⟩
    have hex_x1_of_ne : ∀ w : Fin inst.n, w ≠ inst.s → w ≠ u → w ≠ v →
        x₁.mem (4 + 2 * inst.n * inst.n + w.val) = ((s.pr.flow.push u v).excess w).toNat :=
      fun w hw_ne hwu hwv => by
        rw [hx₁_mem, Function.update_of_ne (fun h => hwu (Fin.ext (by omega))),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega), hxca.hexcess w hw_ne]
        exact congrArg Int.toNat (s.pr.flow.excess_push_of_ne hwu hwv).symm
    refine WP.exists_execWithin ?_
    unfold pushTail
    by_cases hvs : v = inst.s
    · wram_exec [hx₁_cur, hx₁_ctx.hrs, congrArg Fin.val hvs]
      rw [show x₁.set rVal (x₁.regs rVal) = x₁ from Data.ext (Function.update_eq_self _ _) rfl]
      obtain ⟨hca, hframe⟩ := hpost_push x₁.mem (fun _ _ => rfl) fun w hw_ne => by
        rcases eq_or_ne w u with rfl | hwu
        · rw [hx₁_mem, Function.update_self]
        · exact hex_x1_of_ne w hw_ne hwu fun h => hw_ne (h.trans hvs)
      exact ⟨hx₁_ctx, hca, hx₁_pos, hx₁_u, hx₁_rel, hx₁_cur, hx₁_hu, hx₁_exr, hframe⟩
    · have hex_v_mem : x₁.mem (4 + 2 * inst.n * inst.n + v.val) = (s.pr.flow.excess v).toNat := by
        rw [hx₁_mem, Function.update_of_ne (fun h => huv (Fin.ext (by omega))),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hxca.hexcess v hvs
      have hexv_new : (s.pr.flow.excess v).toNat + δ = ((s.pr.flow.push u v).excess v).toNat := by
        have := s.pr.flow.excess_nonneg hvs
        have := s.pr.flow.excess_push_target huv
        omega
      have hf_exv_new : Fits w ((s.pr.flow.excess v).toNat + δ) :=
        fits_val_of_le_n_maxCap hw
          (hexv_new.symm ▸ preflow_excess_le inst (s.pr.flow.push u v) v hvs)
      wram_exec [hx₁_cur, hx₁_ctx.hrs, show v.val ≠ inst.s.val from fun h => hvs (Fin.ext h),
        hx₁_ctx.hbaseE, hex_v_mem, hx₁_delta, hexv_new, hf_ev, hf_exv_new]
      obtain ⟨hca, hframe⟩ := hpost_push
        (Function.update x₁.mem (4 + 2 * inst.n * inst.n + v.val)
          ((s.pr.flow.push u v).excess v).toNat)
        (fun a ha => Function.update_of_ne (by have := v.isLt; omega) _ _)
        fun w hw_ne => by
          by_cases hwv : w = v
          · subst hwv; rw [Function.update_self]
          · rw [Function.update_of_ne (fun h => hwv (Fin.ext (by omega)))]
            by_cases hwu : w = u
            · subst hwu; rw [hx₁_mem, Function.update_self]
            · exact hex_x1_of_ne w hw_ne hwu hwv
      exact ⟨((hx₁_ctx.set (by decide)).set (by decide)).set (by decide) |>.write_ge
          (baseF_le_baseE inst.n v.val), hca,
        by wram_simp [hx₁_pos],
        by wram_simp [hx₁_u],
        by wram_simp [hx₁_rel],
        by wram_simp [hx₁_cur],
        by wram_simp [hx₁_hu],
        by wram_simp [hx₁_exr], hframe⟩
  exact ⟨y, (hx₁_ex.seq hy_ex).mono (by omega), hy_ctx, hy_ca, hy_pos, hy_u, hy_rel, hy_cur, hy_hu,
    hy_exr, hy_out⟩

private theorem advanceCode_spec (inst : Instance) {w : ℕ} (hw : Fits w inst.wordBound)
    {u : Fin inst.n} {k : ℕ} (hk : k < inst.n) {s : CAState inst.toNetwork}
    (_hs : CAInv (defaultAdj inst.n) s) (hcu : s.cur u = (List.finRange inst.n).drop k)
    {x : Data 32} (hx : CtxInv inst x) (hxca : CAMem inst s x.mem)
    (hxu : x.regs rU = u.val) (hxcur : x.regs rCur = k) :
    let vs := (List.finRange inst.n).drop (k + 1)
    let s' : CAState inst.toNetwork := ⟨s.pr, Function.update s.cur u vs⟩
    ∃ y, ExecWithin w advanceCode x y 3 ∧ CtxInv inst y ∧ CAMem inst s' y.mem ∧
      y.regs rPos = x.regs rPos ∧ y.regs rU = u.val ∧ y.regs rRel = x.regs rRel ∧
      y.regs rCur = k + 1 ∧ y.regs rEx = x.regs rEx ∧ y.regs rHU = x.regs rHU ∧
      (∀ a, a ≠ 4 + 2 * inst.n * inst.n + 2 * inst.n + u.val → y.mem a = x.mem a) := by
  obtain ⟨_, _, hf_cu, _⟩ := fits_vtx hw u
  obtain ⟨_, _, _, hf_k1⟩ := fits_vtx hw ⟨k, hk⟩
  refine WP.exists_execWithin ?_
  unfold advanceCode
  wram_exec [hxcur, hx.hone, hx.hbaseC, hxu, hf_k1, hf_cu]
  refine ⟨((hx.set (by decide)).set (by decide)).write_ge (by nlinarith), ?_,
    by wram_simp,
    by wram_simp [hxu],
    by wram_simp,
    by wram_simp,
    by wram_simp,
    by wram_simp,
    fun a ha => Data.write_mem_of_ne ha _⟩
  exact
    { hflow := fun a b => (Data.write_mem_of_ne
        (by nlinarith [List.mul_add_lt_sq a.isLt b.isLt]) _).trans (hxca.hflow a b)
      hexcess := fun w hw => (Data.write_mem_of_ne (by nlinarith [w.isLt]) _).trans
        (hxca.hexcess w hw)
      hheight := fun w => (Data.write_mem_of_ne (by nlinarith [w.isLt]) _).trans (hxca.hheight w)
      hcur := fun w => by
        by_cases hwu : w = u
        · subst hwu
          exact ⟨k + 1, hk, Data.write_mem_self _ _ _, by simp⟩
        · obtain ⟨j, hj, hjm, hdrop⟩ := hxca.hcur w
          exact ⟨j, hj, (Data.write_mem_of_ne (fun h => hwu (Fin.ext (by omega))) _).trans hjm,
            by simpa [Function.update_of_ne hwu] using hdrop⟩ }

open scoped Classical in
private noncomputable def dischargePot (inst : Instance) (u : Fin inst.n) (y : Data 32) : ℕ :=
  if h : ∃ s : CAState inst.toNetwork, CAInv (defaultAdj inst.n) s ∧ CAMem inst s y.mem then
    let s := Classical.choose h
    let d := discharge (defaultAdj inst.n) id u s
    56 * d.ops.length + 32 * d.advances + (25 * inst.n + 30) * s.pr.numRelabels d.ops
  else 0

private theorem dischargePot_eq (inst : Instance) (u : Fin inst.n) {s : CAState inst.toNetwork}
    (hs : CAInv (defaultAdj inst.n) s) {y : Data 32} (hca : CAMem inst s y.mem) :
    let d := discharge (defaultAdj inst.n) id u s
    dischargePot inst u y =
      56 * d.ops.length + 32 * d.advances + (25 * inst.n + 30) * s.pr.numRelabels d.ops := by
  have h : ∃ s' : CAState inst.toNetwork, CAInv (defaultAdj inst.n) s' ∧ CAMem inst s' y.mem :=
    ⟨s, hs, hca⟩
  simp only [dischargePot, dite_eq_left h, caMem_unique (Classical.choose_spec h).2 hca]

private theorem dischargeCode_spec (inst : Instance) {w : ℕ} (hw : Fits w inst.wordBound)
    {u : Fin inst.n} (hus : u ≠ inst.s) (hut : u ≠ inst.t)
    {s₀ : CAState inst.toNetwork} (hs₀ : CAInv (defaultAdj inst.n) s₀)
    {x : Data 32} (hx : CtxInv inst x) (hxca : CAMem inst s₀ x.mem)
    (hxu : x.regs rU = u.val) :
    let d₀ := discharge (defaultAdj inst.n) id u s₀
    ∃ y, ExecWithin w dischargeCode x y
        (56 * d₀.ops.length + 32 * d₀.advances +
          (25 * inst.n + 30) * s₀.pr.numRelabels d₀.ops + 9) ∧
      CtxInv inst y ∧ CAMem inst d₀.ca y.mem ∧
      y.regs rPos = x.regs rPos ∧ y.regs rU = u.val ∧
      y.regs rRel = (if d₀.relabeled then 1 else 0) ∧
      (∀ a, 4 + 2 * inst.n * inst.n + 3 * inst.n ≤ a → y.mem a = x.mem a) := by
  intro d₀
  have hadj := adjValid_defaultAdj inst.toNetwork
  obtain ⟨k₀, hk₀, hkm₀, hdrop₀⟩ := hxca.hcur u
  obtain ⟨hf_eu, hf_hu, hf_cu, _⟩ := fits_vtx hw u
  obtain ⟨x₁, hx₁_ex, hx₁_ctx, hx₁_mem, hx₁_pos, hx₁_u, hx₁_rel, hx₁_exr, hx₁_hu, hx₁_cur⟩ :
      ∃ x₁, ExecWithin w dischargeInit x x₁ 7 ∧ CtxInv inst x₁ ∧ x₁.mem = x.mem ∧
        x₁.regs rPos = x.regs rPos ∧ x₁.regs rU = u.val ∧ x₁.regs rRel = 0 ∧
        x₁.regs rEx = (s₀.pr.flow.excess u).toNat ∧ x₁.regs rHU = s₀.pr.height u ∧
        x₁.regs rCur = k₀ := by
    refine WP.exists_execWithin ?_
    unfold dischargeInit
    wram_exec [hx.hzero, hx.hbaseE, hx.hbaseH, hx.hbaseC, hxu,
      hxca.hexcess u hus, hxca.hheight u, hkm₀, hf_eu, hf_hu, hf_cu]
    exact ⟨((((((hx.set (by decide)).set (by decide)).set (by decide)).set (by decide)).set
        (by decide)).set (by decide)).set (by decide),
      rfl, by wram_simp, by wram_simp [hxu], by wram_simp, by wram_simp, by wram_simp, by wram_simp⟩
  let I' (y : Data 32) : Prop :=
    CtxInv inst y ∧ y.regs rPos = x.regs rPos ∧ y.regs rU = u.val ∧
    (∀ a, 4 + 2 * inst.n * inst.n + 3 * inst.n ≤ a → y.mem a = x.mem a) ∧
    ∃ (s : CAState inst.toNetwork) (k : ℕ) (bRel : Bool),
      CAInv (defaultAdj inst.n) s ∧ CAMem inst s y.mem ∧
      y.regs rEx = (s.pr.flow.excess u).toNat ∧
      y.regs rHU = s.pr.height u ∧
      k ≤ inst.n ∧ y.regs rCur = k ∧ s.cur u = (List.finRange inst.n).drop k ∧
      y.regs rRel = (if bRel then 1 else 0) ∧
      (discharge (defaultAdj inst.n) id u s).ca = d₀.ca ∧
      (bRel || (discharge (defaultAdj inst.n) id u s).relabeled) = d₀.relabeled
  have hbody (y : Data 32) (hy : I' y) (hc : (Cond.lt zero rEx).Holds y) :
      ∃ z T, ExecWithin w dischargeBody y z T ∧ I' z ∧
        T + 2 + dischargePot inst u z ≤ dischargePot inst u y := by
    obtain ⟨hyc, hypos, hyu, hytop, s, k, bRel, hs, hyca, hyex, hyhu, hk_le, hycur, hdrop,
      hyrel, hdca, hrel_eq⟩ := hy
    have hex_pos : 0 < y.regs rEx := by simpa only [Cond.holds_lt, hyc.hzero] using hc
    have hact : s.pr.flow.IsActive u := ⟨hus, hut, by omega⟩
    have hpot_y := dischargePot_eq inst u hs hyca
    by_cases hkn : k = inst.n
    · have hcur_nil : s.cur u = [] := by rw [hdrop, hkn, drop_finRange_eq_nil]
      obtain ⟨z, hz_ex, hzc, hzca, hzpos, hzu, hzrel, hzcur, hzex, hzhu, hzmem⟩ :=
        relabelCode_spec inst hw hs hact hcur_nil hyc hyca hyu hyex
      obtain ⟨hs', hd_eq⟩ := discharge_relabel_step hadj hs hact hcur_nil
      set s' : CAState inst.toNetwork :=
        ⟨s.pr.apply (.relabel u), Function.update s.cur u (defaultAdj inst.n u)⟩
      have hbr : ExecWithin w dischargeBody y z (21 * inst.n + 12) :=
        execWithin_branch_pos (by simp only [Cond.holds_eq, hycur, hkn, hyc.hrn]) hz_ex le_rfl
      have hnr : s.pr.numRelabels (discharge (defaultAdj inst.n) id u s).ops =
          1 + (s.pr.apply (.relabel u)).numRelabels
            (discharge (defaultAdj inst.n) id u s').ops := by
        rw [hd_eq, State.numRelabels_cons]; rfl
      have := u.isLt
      refine ⟨z, 21 * inst.n + 12, hbr, ⟨hzc, hzpos.trans hypos, hzu,
        fun a ha => (hzmem a (by omega) (by omega)).trans
          (hytop a ha),
        s', 0, true, hs', hzca, hzex, hzhu, Nat.zero_le _, hzcur, by simp [s', defaultAdj],
        by simp [hzrel], (congrArg DischargeOutput.ca hd_eq).symm.trans hdca,
        by simpa [congrArg DischargeOutput.relabeled hd_eq] using hrel_eq⟩, ?_⟩
      rw [hpot_y, dischargePot_eq inst u hs' hzca, hnr, hd_eq]
      dsimp only [s']
      simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
      omega
    · have hk_lt : k < inst.n := by omega
      let v : Fin inst.n := ⟨k, hk_lt⟩
      have hcur_cons : s.cur u = v :: (List.finRange inst.n).drop (k + 1) :=
        hdrop ▸ drop_finRange_eq_cons hk_lt
      obtain ⟨y₁, hy₁_ex, hy₁_reg, hy₁_mem, hy₁_rc, hy₁_v2⟩ :=
        admissibleCode_spec inst hw hs hyc hyca hyu (v := v) hycur hyhu
      have hy₁_ctx : CtxInv inst y₁ :=
        hyc.of_eq (fun i hi => hy₁_reg i (by omega)) (fun _ _ => by rw [hy₁_mem])
      have hy₁_ca : CAMem inst s y₁.mem := hy₁_mem ▸ hyca
      have hy₁_pos : y₁.regs rPos = x.regs rPos := (hy₁_reg rPos (by decide)).trans hypos
      have hy₁_u : y₁.regs rU = u.val := (hy₁_reg rU (by decide)).trans hyu
      have hy₁_rel : y₁.regs rRel = (if bRel then 1 else 0) :=
        (hy₁_reg rRel (by decide)).trans hyrel
      have hy₁_cur : y₁.regs rCur = v.val := (hy₁_reg rCur (by decide)).trans hycur
      have hy₁_exr : y₁.regs rEx = (s.pr.flow.excess u).toNat :=
        (hy₁_reg rEx (by decide)).trans hyex
      have hy₁_hu : y₁.regs rHU = s.pr.height u := (hy₁_reg rHU (by decide)).trans hyhu
      have hkn' : ¬ (Cond.eq rCur rn).Holds y := by simp only [Cond.holds_eq, hycur, hyc.hrn]; omega
      by_cases hadm : 0 < s.pr.flow.resCap u v ∧ s.pr.height u = s.pr.height v + 1
      · obtain ⟨z, hz_ex, hzc, hzca, hzpos, hzu, hzrel, hzcur, hzhu, hzex, hztop⟩ :=
          pushBody_spec inst hw hs hact hadm hy₁_ctx hy₁_ca hy₁_u hy₁_cur hy₁_exr hy₁_rc
        obtain ⟨hs', hd_eq⟩ := discharge_push_step hadj hs hact hcur_cons hadm
        set s' : CAState inst.toNetwork := ⟨s.pr.apply (.push u v), s.cur⟩
        have hif : ExecWithin w dischargeElse y z 48 :=
          (hy₁_ex.seq (execWithin_branch_pos
            (by simp [Cond.holds_eq, hy₁_v2, hadm, hy₁_ctx.hone]) hz_ex le_rfl)).mono (by omega)
        have hbr : ExecWithin w dischargeBody y z 50 := execWithin_branch_neg hkn' hif le_rfl
        have hnr : s.pr.numRelabels (discharge (defaultAdj inst.n) id u s).ops =
            (s.pr.apply (.push u v)).numRelabels (discharge (defaultAdj inst.n) id u s').ops := by
          rw [hd_eq, State.numRelabels_cons]
          dsimp only [s']
          simp [Op.IsRelabel]
        refine ⟨z, 50, hbr, ⟨hzc, hzpos.trans hy₁_pos, hzu,
          fun a ha => (hztop a (by omega)).trans (hy₁_mem ▸ hytop a ha),
          s', k, bRel, hs', hzca, hzex, hzhu.trans hy₁_hu, hk_le, hzcur, hdrop,
          hzrel.trans hy₁_rel, (congrArg DischargeOutput.ca hd_eq).symm.trans hdca,
          by rw [← congrArg DischargeOutput.relabeled hd_eq, hrel_eq]⟩, ?_⟩
        rw [hpot_y, dischargePot_eq inst u hs' hzca, hnr, hd_eq]
        dsimp only [s']
        simp only [List.length_cons]
        omega
      · obtain ⟨z, hz_ex, hzc, hzca, hzpos, hzu, hzrel, hzcur, hzex, hzhu, hzmem⟩ :=
          advanceCode_spec inst hw hk_lt hs hdrop hy₁_ctx hy₁_ca hy₁_u hy₁_cur
        obtain ⟨hs', hd_eq⟩ := discharge_advance_step hadj hs hact hcur_cons hadm
        set s' : CAState inst.toNetwork :=
          ⟨s.pr, Function.update s.cur u ((List.finRange inst.n).drop (k + 1))⟩
        have hif : ExecWithin w dischargeElse y z 24 :=
          (hy₁_ex.seq (execWithin_branch_neg
            (by simp [Cond.holds_eq, hy₁_v2, hadm, hy₁_ctx.hone]) hz_ex le_rfl)).mono (by omega)
        have hbr : ExecWithin w dischargeBody y z 26 := execWithin_branch_neg hkn' hif le_rfl
        refine ⟨z, 26, hbr, ⟨hzc, hzpos.trans hy₁_pos, hzu,
          fun a ha => (hzmem a (by have := u.isLt; omega)).trans (hy₁_mem ▸ hytop a ha),
          s', k + 1, bRel, hs', hzca, hzex.trans hy₁_exr, hzhu.trans hy₁_hu,
          hk_lt, hzcur, by simp [s'], hzrel.trans hy₁_rel,
          (congrArg DischargeOutput.ca hd_eq).symm.trans hdca,
          by rw [← congrArg DischargeOutput.relabeled hd_eq, hrel_eq]⟩, ?_⟩
        rw [hpot_y, dischargePot_eq inst u hs' hzca, hd_eq]
        dsimp only [s']
        omega
  have hx₁_I : I' x₁ :=
    ⟨hx₁_ctx, hx₁_pos, hx₁_u, fun _ _ => hx₁_mem ▸ rfl,
      s₀, k₀, false, hs₀, hx₁_mem ▸ hxca, hx₁_exr, hx₁_hu, hk₀, hx₁_cur, hdrop₀,
      hx₁_rel, rfl, by simp [d₀]⟩
  obtain ⟨y, hl_ex, hl_I, hl_stop⟩ :=
    ExecWithin.loop_potential I' (dischargePot inst u) hbody hx₁_I
  obtain ⟨hyc, hypos, hyu, hytop, s_end, _, bRel, _, hyca, hyex, _, _, _, _, hyrel, hca_eq, hrel⟩ :=
    hl_I
  have hnot_act : ¬ s_end.pr.flow.IsActive u := fun ha => by
    simp only [Cond.holds_lt, hyc.hzero] at hl_stop
    have := ha.2.2
    omega
  have hd_end := discharge_eq_of_not_isActive (adj := defaultAdj inst.n) id hnot_act
  have hs_end_eq : s_end = d₀.ca := by rw [← hca_eq, hd_end]
  have hbRel_eq : bRel = d₀.relabeled := by simpa [hd_end] using hrel
  have hpot_x₁ : dischargePot inst u x₁ =
      56 * d₀.ops.length + 32 * d₀.advances + (25 * inst.n + 30) * s₀.pr.numRelabels d₀.ops :=
    dischargePot_eq inst u hs₀ (hx₁_mem ▸ hxca)
  exact ⟨y, (hx₁_ex.seq hl_ex).mono (by rw [hpot_x₁]; omega), hyc, hs_end_eq ▸ hyca, hypos, hyu,
    by rw [hyrel, hbRel_eq], hytop⟩

end DischargeLowering

/-! ### Outer relabel-to-front loop lowering -/

section OuterLowering

private theorem shiftOrderCode_spec (inst : Instance) {w : ℕ} (hw : Fits w inst.wordBound)
    (_hst : inst.s ≠ inst.t) {u : Fin inst.n} {done rest : List (Fin inst.n)}
    (hlen : (done ++ u :: rest).length = inst.n - 2)
    {x : Data 32} (hx : CtxInv inst x)
    (hxord : OrderMem inst done (u :: rest) x) (hxu : x.regs rU = u.val) :
    ∃ y, ExecWithin w shiftOrderCode x y (8 * inst.n + 6) ∧ CtxInv inst y ∧
      OrderMem inst [u] (done ++ rest) y ∧
      (∀ a, a < 4 + 2 * inst.n * inst.n + 3 * inst.n → y.mem a = x.mem a) := by
  have hn := inst.n_pos
  have hn_sq : inst.n ≤ inst.n * inst.n := Nat.le_mul_self inst.n
  have hn2 : inst.n - 2 ≤ inst.n := Nat.sub_le inst.n 2
  have h2nn := two_mul_sq inst.n
  have h4nn := four_mul_sq inst.n
  have hpos_lt : done.length < inst.n - 2 := by
    rw [← hlen, List.length_append, List.length_cons]; omega
  let ord := done ++ u :: rest
  let ord' := [u] ++ (done ++ rest)
  have hord_len : ord.length = inst.n - 2 := hlen
  have hord'_len : ord'.length = inst.n - 2 := by
    simp only [ord', List.singleton_append, List.length_cons, List.length_append]
    rw [List.length_append, List.length_cons] at hlen
    omega
  have hprep : ExecWithin (B := .standard) w (ram[ rIdx ← rPos ]) x
      (x.set rIdx done.length) 1 := by
    ram_eval [hxord.hrPos]
  set x₁ := x.set rIdx done.length
  have hx₁_ctx : CtxInv inst x₁ := hx.set (by decide)
  let P (y : Data 32) : Prop :=
    CtxInv inst y ∧ y.regs rU = u.val ∧ y.regs rIdx ≤ done.length ∧
    (∀ a, a < 4 + 2 * inst.n * inst.n + 3 * inst.n → y.mem a = x.mem a) ∧
    (∀ (j : ℕ) (hj : j < done.length), j < y.regs rIdx →
      y.mem (4 + 2 * inst.n * inst.n + 3 * inst.n + j) = (done[j]'hj).val) ∧
    (∀ (j : ℕ) (hj : j < done.length), y.regs rIdx ≤ j →
      y.mem (4 + 2 * inst.n * inst.n + 3 * inst.n + (j + 1)) = (done[j]'hj).val) ∧
    (∀ (j : ℕ) (hj : j < inst.n - 2), done.length < j →
      y.mem (4 + 2 * inst.n * inst.n + 3 * inst.n + j) = (ord[j]'(hlen ▸ hj)).val)
  have hbody (y : Data 32) (hy : P y) (hc : (Cond.lt zero rIdx).Holds y) :
      ∃ z, ExecWithin w shiftOrderBody y z 6 ∧ P z ∧ z.regs rIdx < y.regs rIdx := by
    obtain ⟨hyc, hyu, hyidx, hylow, hypref, hysuf, hyrest⟩ := hy
    have hk_pos : 0 < y.regs rIdx := by simpa only [Cond.holds_lt, hyc.hzero] using hc
    set k := y.regs rIdx
    have hf_km1 : Fits w (k - 1) := fits_of_addr hw (by omega)
    have hf_a1 : Fits w (4 + 2 * inst.n * inst.n + 3 * inst.n + (k - 1)) :=
      fits_of_addr hw (by omega)
    have hf_a2 : Fits w (4 + 2 * inst.n * inst.n + 3 * inst.n + k) :=
      fits_of_addr hw (by omega)
    have hk_dl : k - 1 < done.length := by omega
    have hread : y.mem (4 + 2 * inst.n * inst.n + 3 * inst.n + (k - 1)) =
        (done[k - 1]'hk_dl).val :=
      hypref (k - 1) hk_dl (by omega)
    refine WP.exists_execWithin ?_
    unfold shiftOrderBody
    wram_exec [hyc.hone, hk_pos, hyc.hbaseO, hread, hf_km1, hf_a1, hf_a2]
    refine ⟨⟨((hyc.set (by decide)).set (by decide)).set (by decide) |>.set (by decide)
        |>.write_ge (by omega) |>.set (by decide),
      by wram_simp [hyu],
      (Nat.sub_le k 1).trans hyidx,
      fun a ha => (Data.write_mem_of_ne (by omega) _).trans (hylow a ha),
      fun j hj_lt hj => ?_, fun j hj_lt hj₁ => ?_,
      fun j hj_lt hj₁ => (Data.write_mem_of_ne (by omega) _).trans (hyrest j hj_lt hj₁)⟩,
      Nat.sub_lt hk_pos Nat.one_pos⟩
    · wram_simp at hj
      exact (Data.write_mem_of_ne (by omega) _).trans (hypref j hj_lt (by omega))
    · wram_simp at hj₁
      by_cases hjk : j = k - 1
      · subst hjk
        rw [show (k - 1) + 1 = k by omega, Data.set_mem, Data.write_mem_self]
        exact hread
      · exact (Data.write_mem_of_ne (by omega) _).trans (hysuf j hj_lt (by omega))
  have hx₁_P : P x₁ :=
    ⟨hx₁_ctx, by wram_simp [x₁, hxu], by wram_simp [x₁]; exact le_rfl, fun _ _ => rfl,
      fun j hj_lt _ => by
        have hmem := hxord.hmem j (by simp only [List.length_append]; omega)
        rw [List.getElem_append_left hj_lt] at hmem
        simpa only [x₁, Data.set_mem] using hmem,
      fun _ _ hj₁ => by simp only [x₁, Data.set_regs_self] at hj₁; omega,
      fun j hj_lt _ => hxord.hmem j (hlen ▸ hj_lt)⟩
  obtain ⟨y₁, hy₁_ex, hy₁_P, hl_stop⟩ :=
    ExecWithin.loop_invariant (cond := .lt zero rIdx) (body := shiftOrderBody) P
      (fun y => y.regs rIdx) hbody hx₁_P
  obtain ⟨hy₁_ctx, hy₁_u, _, hy₁_low, _, hy₁_suf, hy₁_rest⟩ := hy₁_P
  have hk0 : y₁.regs rIdx = 0 := by simp only [Cond.holds_lt, hy₁_ctx.hzero] at hl_stop; omega
  have hf_bO : Fits w (4 + 2 * inst.n * inst.n + 3 * inst.n) := fits_of_addr hw (by omega)
  obtain ⟨y, hy_ex, hy_ctx, hy_pos, hy_mem⟩ :
      ∃ y, ExecWithin w shiftOrderTail y₁ y 2 ∧ CtxInv inst y ∧ y.regs rPos = 1 ∧
        y.mem = Function.update y₁.mem (4 + 2 * inst.n * inst.n + 3 * inst.n) u.val := by
    refine WP.exists_execWithin ?_
    unfold shiftOrderTail
    wram_exec [hy₁_ctx.hbaseO, hy₁_u, hy₁_ctx.hone, hf_bO]
    exact ⟨(hy₁_ctx.write_ge (by omega)).set (by decide), by wram_simp, rfl⟩
  refine ⟨y, (hprep.seq (hy₁_ex.seq hy_ex)).mono (by simp only [x₁, Data.set_regs_self]; omega),
    hy_ctx,
    { hrPos := by simp [hy_pos]
      hlen := hord'_len
      hmem := fun i hi => by
        rw [hy_mem]
        rcases Nat.eq_zero_or_pos i with rfl | hipos
        · simp
        · rw [Function.update_of_ne (by omega)]
          have hi1 : i = (i - 1) + 1 := by omega
          simp only [List.singleton_append]
          rw [list_getElem_eq_of_eq hi1, List.getElem_cons_succ]
          by_cases hid : i - 1 < done.length
          · simpa [show i - 1 + 1 = i by omega, List.getElem_append_left hid] using
              hy₁_suf (i - 1) hid (by omega)
          · have heq := hy₁_rest i (hord'_len ▸ hi) (by omega)
            simp only [ord] at heq
            rw [heq, List.getElem_append_right (by omega), List.getElem_append_right (by omega),
              list_getElem_eq_of_eq (show i - done.length = (i - 1 - done.length) + 1 by omega),
              List.getElem_cons_succ] },
    fun a ha => by
      rw [hy_mem, Function.update_of_ne (by omega)]
      exact hy₁_low a ha⟩

open scoped Classical in
private noncomputable def outerPot (inst : Instance) (y : Data 32) : ℕ :=
  if h : ∃ st : RTFState inst.toNetwork, RTFMem inst st y then
    let st := Classical.choose h
    let r := rtfLoop (defaultAdj inst.n) id id (rtfFuel (Fin inst.n)) st
    56 * r.1.length + 32 * r.2.advances + 22 * r.2.discharges +
      (33 * inst.n + 38) * st.ca.pr.numRelabels r.1
  else 0

private theorem outerPot_eq (inst : Instance) {st : RTFState inst.toNetwork} {y : Data 32}
    (hmem : RTFMem inst st y) :
    let r := rtfLoop (defaultAdj inst.n) id id (rtfFuel (Fin inst.n)) st
    outerPot inst y =
      56 * r.1.length + 32 * r.2.advances + 22 * r.2.discharges +
        (33 * inst.n + 38) * st.ca.pr.numRelabels r.1 := by
  have h : ∃ st' : RTFState inst.toNetwork, RTFMem inst st' y := ⟨st, hmem⟩
  simp only [outerPot, dite_eq_left h, rtfMem_unique (Classical.choose_spec h) hmem]

private theorem outerCode_spec (inst : Instance) {w : ℕ} (hw : Fits w inst.wordBound)
    (hst : inst.s ≠ inst.t) {x : Data 32} (hx : CtxInv inst x)
    (hxrtf : RTFMem inst
      (RTFState.init inst.toNetwork (defaultAdj inst.n) (nonTermFin inst.toNetwork)) x) :
    ∃ y, ExecWithin w outerCode x y (590 * inst.n ^ 3 + 76 * inst.n ^ 2 + 2) ∧
      CtxInv inst y ∧
      CAInv (defaultAdj inst.n) (rtfLoop (defaultAdj inst.n) id id (rtfFuel (Fin inst.n))
        (RTFState.init inst.toNetwork (defaultAdj inst.n) (nonTermFin inst.toNetwork))).2.ca ∧
      (∀ v : Fin inst.n, ¬ (rtfLoop (defaultAdj inst.n) id id (rtfFuel (Fin inst.n))
        (RTFState.init inst.toNetwork (defaultAdj inst.n)
          (nonTermFin inst.toNetwork))).2.ca.pr.flow.IsActive v) ∧
      CAMem inst (rtfLoop (defaultAdj inst.n) id id (rtfFuel (Fin inst.n))
        (RTFState.init inst.toNetwork (defaultAdj inst.n)
          (nonTermFin inst.toNetwork))).2.ca y.mem := by
  have hadj := adjValid_defaultAdj inst.toNetwork
  set st₀ := RTFState.init inst.toNetwork (defaultAdj inst.n) (nonTermFin inst.toNetwork)
  set r₀ := rtfLoop (defaultAdj inst.n) id id (rtfFuel (Fin inst.n)) st₀
  let I (y : Data 32) : Prop :=
    CtxInv inst y ∧ ∃ st : RTFState inst.toNetwork,
      RTFMem inst st y ∧
      let r := rtfLoop (defaultAdj inst.n) id id (rtfFuel (Fin inst.n)) st
      r.2.ca = r₀.2.ca
  have hbody (y : Data 32) (hy : I y) (hc : (Cond.lt rPos rLim).Holds y) :
      ∃ z T, ExecWithin w outerBody y z T ∧ I z ∧
        T + 2 + outerPot inst z ≤ outerPot inst y := by
    obtain ⟨hyc, st, hst_mem, hr_eq⟩ := hy
    have hpot_y := outerPot_eq inst hst_mem
    have hlt_pos : y.regs rPos < inst.n - 2 := by
      simpa only [Cond.holds_lt, hyc.hrLim, ite_eq_right hst] using hc
    have htodo_ne : st.todo ≠ [] := by
      intro hnil
      have hlen := hst_mem.hord.hlen
      rw [hnil, List.append_nil, ← hst_mem.hord.hrPos] at hlen
      omega
    obtain ⟨u, rest, htodo⟩ := List.exists_cons_of_ne_nil htodo_ne
    have hu_mem : u ∈ st.done ++ u :: rest := List.mem_append_right _ List.mem_cons_self
    have hu_ne := (htodo ▸ hst_mem.hinv.mem_iff u).mp hu_mem
    have hf_o : Fits w (4 + 2 * inst.n * inst.n + 3 * inst.n + st.done.length) :=
      fits_of_addr hw (by
        have hlen := hst_mem.hord.hlen
        rw [htodo, List.length_append, List.length_cons] at hlen
        have hsub := Nat.sub_le inst.n 2
        have hdon : st.done.length ≤ inst.n := by omega
        nlinarith [inst.n_pos])
    have hu_addr : y.mem (4 + 2 * inst.n * inst.n + 3 * inst.n + st.done.length) = u.val := by
      have hi : st.done.length < (st.done ++ st.todo).length := by
        rw [htodo, List.length_append, List.length_cons]; omega
      have hm := hst_mem.hord.hmem st.done.length hi
      simpa [htodo] using hm
    have hload : ∃ y₁, ExecWithin w (ram[ rAddr ← baseO + rPos; rU ← *rAddr ]) y y₁ 2 ∧
        CtxInv inst y₁ ∧ y₁.mem = y.mem ∧ y₁.regs rPos = st.done.length ∧
        y₁.regs rU = u.val := by
      refine WP.exists_execWithin ?_
      wram_exec [hyc.hbaseO, hst_mem.hord.hrPos, hu_addr, hf_o]
      exact ⟨(hyc.set (by decide)).set (by decide), rfl, by wram_simp [hst_mem.hord.hrPos],
        by wram_simp⟩
    obtain ⟨y₁, hy₁_ex, hy₁_ctx, hy₁_mem, hy₁_pos, hy₁_u⟩ := hload
    have hy₁_ca : CAMem inst st.ca y₁.mem := hy₁_mem ▸ hst_mem.hca
    obtain ⟨y₂, hy₂_ex, hy₂_ctx, hy₂_ca, hy₂_pos, hy₂_u, hy₂_rel, hy₂_top⟩ :=
      dischargeCode_spec inst hw hu_ne.1 hu_ne.2 hst_mem.hinv.caInv hy₁_ctx hy₁_ca hy₁_u
    set d := discharge (defaultAdj inst.n) id u st.ca
    have hy₂_ord : OrderMem inst st.done (u :: rest) y₂ :=
      (htodo ▸ hst_mem.hord).of_eq (hy₂_pos.trans (hy₁_pos.trans hst_mem.hord.hrPos.symm))
        fun i hi => (hy₂_top _ (by omega)).trans (by rw [hy₁_mem])
    have hr_step := rtfLoop_step hadj hst_mem.hinv htodo hst
    set st' : RTFState inst.toNetwork :=
      if d.relabeled then
        { ca := d.ca, done := [u], todo := st.done ++ rest, discharges := 0, advances := 0 }
      else
        { ca := d.ca, done := st.done ++ [u], todo := rest, discharges := 0, advances := 0 }
    obtain ⟨hinv', hr1, hrdis, hradv, hrca, _, _⟩ := hr_step
    obtain ⟨_, _, hdnr, _, _, hd_rel_iff, _⟩ :=
      discharge_spec hadj (norm := id) (fun _ => rfl) u hst_mem.hinv.caInv
    have hpot_z_step : ∀ (z : Data 32) (T_branch : ℕ),
        ExecWithin w outerBranch y₂ z T_branch →
        RTFMem inst st' z →
        T_branch ≤ (if d.relabeled then 8 * inst.n + 7 else 3) →
        outerPot inst z + (2 + (2 + 56 * d.ops.length + 32 * d.advances +
          (25 * inst.n + 30) * st.ca.pr.numRelabels d.ops + 9 + T_branch)) ≤ outerPot inst y := by
      intro z T_br _ hz_mem hTbr
      rw [hpot_y, outerPot_eq inst hz_mem]
      have hnr1 :
          st.ca.pr.numRelabels
              (rtfLoop (defaultAdj inst.n) id id (rtfFuel (Fin inst.n)) st).1 =
            st.ca.pr.numRelabels d.ops +
              st'.ca.pr.numRelabels
                (rtfLoop (defaultAdj inst.n) id id (rtfFuel (Fin inst.n)) st').1 := by
        have hst'_ca : st'.ca = d.ca := by dsimp only [st']; split_ifs <;> rfl
        rw [hr1, State.numRelabels_append, ← hdnr, hst'_ca]
      have hbr_rel : T_br ≤ 3 + (8 * inst.n + 7) * st.ca.pr.numRelabels d.ops := by
        by_cases hrel : d.relabeled = true
        · have h1 : T_br ≤ 8 * inst.n + 7 := by simpa [hrel] using hTbr
          have hmul := Nat.le_mul_of_pos_right (8 * inst.n + 7)
            (show 0 < st.ca.pr.numRelabels d.ops from hd_rel_iff.mp hrel)
          omega
        · have h2 : T_br ≤ 3 := by simpa [hrel] using hTbr
          omega
      exact outerPot_step_le inst.n _ _ _ _ _ _ _ _ _ _ _ _
        (by rw [hr1, List.length_append])
        (by rw [hrdis, hst_mem.hdis0])
        (by rw [hradv, hst_mem.hadv0, Nat.zero_add])
        hnr1 hbr_rel
    by_cases hrel : d.relabeled = true
    · obtain ⟨z, hz_ex, hz_ctx, hz_ord, hz_low⟩ :=
        shiftOrderCode_spec inst hw hst (htodo ▸ hst_mem.hord.hlen) hy₂_ctx hy₂_ord hy₂_u
      have hz_ca : CAMem inst st'.ca z.mem := by
        rw [show st'.ca = d.ca by simp [st', hrel]]
        exact hy₂_ca.of_mem_eq fun a _ ha2 => hz_low a ha2
      have hz_mem : RTFMem inst st' z :=
        { hinv := hinv'
          hca := hz_ca
          hord := by
            rw [show st'.done = [u] by simp [st', hrel],
              show st'.todo = st.done ++ rest by simp [st', hrel]]
            exact hz_ord
          hdis0 := by simp [st', hrel]
          hadv0 := by simp [st', hrel] }
      have hif : ExecWithin w outerBranch y₂ z (8 * inst.n + 7) :=
        execWithin_branch_pos (by simp [Cond.holds_eq, hy₂_rel, hrel, hy₂_ctx.hone]) hz_ex le_rfl
      refine ⟨z, 2 + (56 * d.ops.length + 32 * d.advances +
          (25 * inst.n + 30) * st.ca.pr.numRelabels d.ops + 9) + (8 * inst.n + 7),
        (hy₁_ex.seq (hy₂_ex.seq hif)).mono (by omega),
        ⟨hz_ctx, st', hz_mem, hrca.symm.trans hr_eq⟩, ?_⟩
      have hbound := hpot_z_step z (8 * inst.n + 7) hif hz_mem (by simp [hrel])
      omega
    · have hrel_f : d.relabeled = false := Bool.eq_false_iff.mpr hrel
      have hf_pos1 : Fits w (st.done.length + 1) :=
        fits_of_addr hw (by
          have hlen := hst_mem.hord.hlen
          rw [List.length_append] at hlen
          nlinarith [Nat.sub_le inst.n 2, Nat.le_mul_self inst.n])
      obtain ⟨_, hstep, rfl⟩ : ∃ z, ExecWithin (B := .standard) w (ram[ rPos ← rPos + one ]) y₂
          z 1 ∧ z = y₂.set rPos (st.done.length + 1) := by
        refine WP.exists_execWithin ?_
        wram_exec [hy₂_ctx.hone, hy₂_pos.trans hy₁_pos, hf_pos1]
        rfl
      have hz_ex : ExecWithin w outerBranch y₂ (y₂.set rPos (st.done.length + 1)) 3 :=
        execWithin_branch_neg (by simp [Cond.holds_eq, hy₂_rel, hrel_f, hy₂_ctx.hone]) hstep le_rfl
      have hz_ctx : CtxInv inst (y₂.set rPos (st.done.length + 1)) := hy₂_ctx.set (by decide)
      have hz_mem : RTFMem inst st' (y₂.set rPos (st.done.length + 1)) :=
        { hinv := hinv'
          hca := by
            rw [show st'.ca = d.ca by simp [st', hrel_f]]
            exact hy₂_ca
          hord := by
            rw [show st'.done = st.done ++ [u] by simp [st', hrel_f],
              show st'.todo = rest by simp [st', hrel_f]]
            exact
              { hrPos := by simp [List.length_append]
                hlen := by simpa [List.append_assoc] using hy₂_ord.hlen
                hmem := fun i hi => by
                  have hm := hy₂_ord.hmem i (by simpa [List.append_assoc] using hi)
                  change y₂.mem _ = ((st.done ++ [u] ++ rest)[i]'hi).val
                  simpa only [List.append_assoc, List.singleton_append] using hm }
          hdis0 := by simp [st', hrel_f]
          hadv0 := by simp [st', hrel_f] }
      refine ⟨y₂.set rPos (st.done.length + 1),
        2 + (56 * d.ops.length + 32 * d.advances +
          (25 * inst.n + 30) * st.ca.pr.numRelabels d.ops + 9) + 3,
        (hy₁_ex.seq (hy₂_ex.seq hz_ex)).mono (by omega),
        ⟨hz_ctx, st', hz_mem, hrca.symm.trans hr_eq⟩, ?_⟩
      have hbound :=
        hpot_z_step (y₂.set rPos (st.done.length + 1)) 3 hz_ex hz_mem (by simp [hrel_f])
      omega
  obtain ⟨y, hl_ex, hl_I, hl_stop⟩ :=
    ExecWithin.loop_potential I (outerPot inst) hbody ⟨hx, st₀, hxrtf, rfl⟩
  obtain ⟨hyc, st_end, hst_end_mem, hr_end_eq⟩ := hl_I
  have hpos_ge : inst.n - 2 ≤ y.regs rPos := by
    simp only [Cond.holds_lt, hyc.hrLim, ite_eq_right hst] at hl_stop; omega
  have htodo_nil : st_end.todo = [] := by
    have h1 := hst_end_mem.hord.hlen
    rw [List.length_append, ← hst_end_mem.hord.hrPos] at h1
    exact List.eq_nil_of_length_eq_zero (by omega)
  have hca_eq : st_end.ca = r₀.2.ca := by
    rw [← hr_end_eq, rtfLoop.eq_def]
    dsimp only
    rw [htodo_nil]
  obtain ⟨_, _, _, _, hrel_le, _, hdis_le, _, hops_le, htot_le⟩ :=
    relabelToFrontDense_correct (N := inst.toNetwork) hst
  have hout_of := out_eq_ofState inst hst
  have hbound : outerPot inst x + 2 ≤ 590 * inst.n ^ 3 + 76 * inst.n ^ 2 + 2 := by
    rw [outerPot_eq inst hxrtf,
      show r₀.1 = inst.out.ops by rw [hout_of]; rfl,
      show r₀.2.discharges = inst.out.discharges by rw [hout_of]; rfl,
      show r₀.2.advances = inst.out.advances by rw [hout_of]; rfl,
      show st₀.ca.pr = PushRelabel.init inst.toNetwork from rfl]
    exact outerPot_init_le inst.n _ _ _ _ hrel_le hdis_le hops_le htot_le
  have hnot_act : ∀ v : Fin inst.n, ¬ r₀.2.ca.pr.flow.IsActive v := by
    rw [← hca_eq]
    intro v hv
    have hm := (hst_end_mem.hinv.mem_iff v).mpr ⟨hv.1, hv.2.1⟩
    rw [htodo_nil, List.append_nil] at hm
    exact hst_end_mem.hinv.done_inactive v hm hv
  exact ⟨y, hl_ex.mono hbound, hyc, hca_eq ▸ hst_end_mem.hinv.caInv, hnot_act,
    hca_eq ▸ hst_end_mem.hca⟩

end OuterLowering

/-! ### Output extraction and main Word-RAM correctness / complexity theorems -/

section OutputAndMain

private theorem cutAndOutputCode_spec (inst : Instance) {w : ℕ} (hw : Fits w inst.wordBound)
    (hst : inst.s ≠ inst.t) {x : Data 32} (hx : CtxInv inst x)
    (hcaInv : CAInv (defaultAdj inst.n) (rtfLoop (defaultAdj inst.n) id id (rtfFuel (Fin inst.n))
      (RTFState.init inst.toNetwork (defaultAdj inst.n) (nonTermFin inst.toNetwork))).2.ca)
    (hnot_act : ∀ v : Fin inst.n, ¬ (rtfLoop (defaultAdj inst.n) id id (rtfFuel (Fin inst.n))
      (RTFState.init inst.toNetwork (defaultAdj inst.n)
        (nonTermFin inst.toNetwork))).2.ca.pr.flow.IsActive v)
    (hxca : CAMem inst (rtfLoop (defaultAdj inst.n) id id (rtfFuel (Fin inst.n))
      (RTFState.init inst.toNetwork (defaultAdj inst.n) (nonTermFin inst.toNetwork))).2.ca x.mem) :
    ∃ y, ExecWithin w cutAndOutputCode x y (19 * inst.n * inst.n + 24 * inst.n + 20) ∧
      CtxInv inst y ∧ y.regs acc = inst.maxFlowValue ∧
      outputList y.mem (y.regs outBase) = inst.answerWords := by
  have hn := inst.n_pos
  have hn_sq : inst.n ≤ inst.n * inst.n := Nat.le_mul_self inst.n
  have h2nn := two_mul_sq inst.n
  have h4nn := four_mul_sq inst.n
  have h2n := two_le_n_of_ne inst hst
  have hout_of := out_eq_ofState inst hst
  set st_end := (rtfLoop (defaultAdj inst.n) id id (rtfFuel (Fin inst.n))
    (RTFState.init inst.toNetwork (defaultAdj inst.n) (nonTermFin inst.toNetwork))).2
  have hz : ∀ v, v ≠ inst.s → v ≠ inst.t → st_end.ca.pr.flow.excess v = 0 :=
    excess_eq_zero_of_forall_not_isActive _ hnot_act
  have hz' : ∀ v, v ≠ inst.toNetwork.s → v ≠ inst.toNetwork.t → st_end.ca.pr.flow.excess v = 0 :=
    hz
  have hval := hcaInv.prInv.valid
  have hout_flow : inst.out.flow = st_end.ca.pr.flow.toFlow hz' := by
    rw [hout_of]
    simp only [RelabelToFrontOutput.ofState]
    rw [dite_eq_left hz']
  have hout_cut : inst.out.cut = gapCut st_end.ca.pr.height := by rw [hout_of]; rfl
  have hflow_val : inst.maxFlowValue = (st_end.ca.pr.flow.excess inst.t).toNat := by
    have h1 := inst.natCast_maxFlowValue
    have h2 : inst.out.flow.value = st_end.ca.pr.flow.excess inst.t :=
      hout_flow ▸ excess_sink_eq_value inst st_end.ca.pr.flow hst hz
    omega
  let h := st_end.ca.pr.height
  obtain ⟨hf_et, _, _, _⟩ := fits_vtx hw inst.t
  have hf_nm1 : Fits w (inst.n - 1) := fits_of_addr hw (by omega)
  obtain ⟨x₁, hx₁_ex, hx₁_ctx, hx₁_mem, hx₁_acc, hx₁_min, hx₁_cur⟩ :
      ∃ x₁, ExecWithin w cutPfx x x₁ 4 ∧ CtxInv inst x₁ ∧ x₁.mem = x.mem ∧
        x₁.regs acc = inst.maxFlowValue ∧ x₁.regs rMinH = inst.n ∧
        x₁.regs rCur = inst.n - 1 := by
    refine WP.exists_execWithin ?_
    unfold cutPfx
    wram_exec [hx.hbaseE, hx.hrt, hx.hrn, hx.hone, hxca.hexcess inst.t hst.symm, hf_et, hf_nm1]
    exact ⟨(((hx.set (by decide)).set (by decide)).set (by decide)).set (by decide), rfl,
      by wram_simp [hflow_val], by wram_simp, by wram_simp⟩
  let EmptyLevel (j : ℕ) : Prop := 0 < j ∧ j < inst.n ∧ ∀ v : Fin inst.n, h v ≠ j
  let GInv (y : Data 32) : Prop :=
    CtxInv inst y ∧ y.mem = x.mem ∧ y.regs acc = inst.maxFlowValue ∧
    y.regs rCur < inst.n ∧ y.regs rMinH ≤ inst.n ∧
    (y.regs rMinH = inst.n → ∀ j, y.regs rCur < j → ¬ EmptyLevel j) ∧
    (y.regs rMinH < inst.n → y.regs rCur < y.regs rMinH ∧ EmptyLevel (y.regs rMinH) ∧
      ∀ j, y.regs rCur < j → j < y.regs rMinH → ¬ EmptyLevel j)
  have hgapBody (y : Data 32) (hy : GInv y) (hc : (Cond.lt zero rCur).Holds y) :
      ∃ z, ExecWithin w gapOuterBody y z (8 * inst.n + 8) ∧ GInv z ∧
        z.regs rCur < y.regs rCur := by
    obtain ⟨hyc, hymem, hyacc, hycur_lt, hymin_le, hym_eq, hym_lt⟩ := hy
    have hk_pos : 0 < y.regs rCur := by simpa only [Cond.holds_lt, hyc.hzero] using hc
    set k := y.regs rCur
    have hinit_in : ExecWithin (B := .standard) w (ram[ rRel ← zero; rIdx ← zero ]) y
        ((y.set rRel 0).set rIdx 0) 2 := by
      ram_eval [hyc.hzero]
    set y₁ := (y.set rRel 0).set rIdx 0
    have hy₁_ctx : CtxInv inst y₁ := (hyc.set (by decide)).set (by decide)
    let SInv (idx : ℕ) (s : Data 32) : Prop :=
      CtxInv inst s ∧ s.mem = x.mem ∧ s.regs acc = inst.maxFlowValue ∧
      s.regs rMinH = y.regs rMinH ∧ s.regs rCur = k ∧
      (s.regs rRel = 0 ∧ (∀ v : Fin inst.n, v.val < idx → h v ≠ k) ∨
       s.regs rRel = 1 ∧ (∃ v : Fin inst.n, v.val < idx ∧ h v = k))
    have hscan (s : Data 32) (hs : SInv (s.regs rIdx) s) (hlt : s.regs rIdx < inst.n) :
        ∃ s', ExecWithin w scanGapInner s s' 6 ∧ SInv (s.regs rIdx + 1) s' ∧
          s'.regs rIdx = s.regs rIdx + 1 := by
      obtain ⟨hsc, hsmem, hsacc, hsmin, hscur, hsrel⟩ := hs
      set idx := s.regs rIdx
      have hidx_def : s.regs rIdx = idx := rfl
      let v : Fin inst.n := ⟨idx, hlt⟩
      have hhv : s.mem (4 + 2 * inst.n * inst.n + inst.n + idx) = h v := hsmem ▸ hxca.hheight v
      obtain ⟨_, hf_hv, _, hf_i1⟩ := fits_vtx hw v
      refine WP.exists_execWithin ?_
      unfold scanGapInner
      by_cases heq : h v = k <;>
        (wram_exec [hidx_def, hsc.hbaseH, hhv, hscur, heq, hsc.hone, hf_hv, hf_i1]
         refine ⟨⟨(((hsc.set (by decide)).set (by decide)).set (by decide)).set (by decide),
           hsmem,
           by wram_simp [hsacc],
           by wram_simp [hsmin],
           by wram_simp [hscur], ?_⟩,
           by wram_simp⟩)
      · exact Or.inr ⟨by wram_simp,
          ⟨v, by simp [v], heq⟩⟩
      · rcases hsrel with ⟨hr0, hall⟩ | ⟨hr1, w, hw_lt, hwk⟩
        · exact Or.inl ⟨by wram_simp [hr0], fun w hw_lt => (Nat.lt_succ_iff_lt_or_eq.mp hw_lt).elim
            (hall w) fun hweq => (show w = v from Fin.ext hweq) ▸ heq⟩
        · exact Or.inr ⟨by wram_simp [hr1], ⟨w, Nat.lt_succ_of_lt hw_lt, hwk⟩⟩
    have hy₁_S : SInv (y₁.regs rIdx) y₁ :=
      ⟨hy₁_ctx, hymem, by wram_simp [y₁, hyacc], by wram_simp [y₁], by wram_simp [y₁]; rfl,
        Or.inl ⟨by wram_simp [y₁], fun _ h => by simp [y₁] at h⟩⟩
    obtain ⟨y₂, hy₂_ex, hy₂_S, _⟩ := ExecWithin.loop_count SInv
      (fun s hs => hs.1.hrn) hscan (by wram_simp [y₁]; exact Nat.zero_le _) hy₁_S
    simp only [show y₁.regs rIdx = 0 from by wram_simp [y₁], Nat.sub_zero] at hy₂_ex
    obtain ⟨hy₂_ctx, hy₂_mem, hy₂_acc, hy₂_min, hy₂_cur, hy₂_rel⟩ := hy₂_S
    have hf_km1 : Fits w (k - 1) := fits_of_addr hw (by omega)
    obtain ⟨z, hz_ex, hz_G, hz_lt⟩ :
        ∃ z, ExecWithin w gapTail y₂ z 4 ∧ GInv z ∧ z.regs rCur < k := by
      refine WP.exists_execWithin ?_
      unfold gapTail
      rcases hy₂_rel with ⟨hr0, hall⟩ | ⟨hr1, v, _, hvk⟩
      · wram_exec [hr0, hy₂_ctx.hzero, hy₂_cur, hk_pos, hy₂_ctx.hone, hf_km1]
        exact ⟨⟨(hy₂_ctx.set (by decide)).set (by decide), hy₂_mem, hy₂_acc,
          (Nat.sub_le k 1).trans_lt hycur_lt, hycur_lt.le,
          fun (h : k = inst.n) => absurd h hycur_lt.ne,
          fun _ => ⟨Nat.sub_lt hk_pos Nat.one_pos, ⟨hk_pos, hycur_lt, fun v => hall v v.isLt⟩,
            fun _ (hj₁ : k - 1 < _) (hj₂ : _ < k) => by omega⟩⟩,
          Nat.sub_lt hk_pos Nat.one_pos⟩
      · have hne_emp : ¬ EmptyLevel k := fun ⟨_, _, hne⟩ => hne v hvk
        wram_exec [hr1, hy₂_ctx.hzero, hy₂_cur, hk_pos, hy₂_ctx.hone, hf_km1]
        rw [show y₂.set rVal (y₂.regs rVal) = y₂ from Data.ext (Function.update_eq_self _ _) rfl]
        refine ⟨⟨hy₂_ctx.set (by decide), hy₂_mem, hy₂_acc,
          (Nat.sub_le k 1).trans_lt hycur_lt, hy₂_min.symm ▸ hymin_le,
          fun (hm : y₂.regs rMinH = inst.n) j (hj₁ : k - 1 < j) => ?_,
          fun (hm : y₂.regs rMinH < inst.n) => ?_⟩,
          Nat.sub_lt hk_pos Nat.one_pos⟩
        · exact (Nat.lt_or_eq_of_le (Nat.le_of_pred_lt hj₁)).elim
            (hym_eq (hy₂_min.symm.trans hm) j) fun hkj => hkj ▸ hne_emp
        · obtain ⟨h1, h2, h3⟩ := hym_lt (hy₂_min ▸ hm)
          exact ⟨(Nat.sub_le k 1).trans_lt (hy₂_min.symm ▸ h1), hy₂_min ▸ h2,
            fun j (hj₁ : k - 1 < j) (hj₂ : j < y₂.regs rMinH) =>
              (Nat.lt_or_eq_of_le (Nat.le_of_pred_lt hj₁)).elim
                (fun hkj => h3 j hkj (hy₂_min ▸ hj₂)) fun hkj => hkj ▸ hne_emp⟩
    exact ⟨z, (hinit_in.seq (hy₂_ex.seq hz_ex)).mono (by omega), hz_G, hz_lt⟩
  have hx₁_G : GInv x₁ :=
    ⟨hx₁_ctx, hx₁_mem, hx₁_acc, by omega, by omega,
      fun _ j hj₁ ⟨_, hj₂, _⟩ => by omega, fun h => by omega⟩
  obtain ⟨x₂, hx₂_ex, hx₂_G, hgap_stop⟩ :=
    ExecWithin.loop_invariant (cond := .lt zero rCur) (body := gapOuterBody) GInv
      (fun y => y.regs rCur) hgapBody hx₁_G
  obtain ⟨hx₂_ctx, hx₂_mem, hx₂_acc, hx₂_cur_lt, hx₂_min_le, hx₂_meq, hx₂_mlt⟩ := hx₂_G
  have hk0 : x₂.regs rCur = 0 := by
    simp only [Cond.holds_lt, hx₂_ctx.hzero] at hgap_stop; omega
  have hgap_eq : x₂.regs rMinH = gapLevel h := by
    obtain ⟨g, hg0, hgn, hgne⟩ := hval.exists_gap
    have hnot_n : x₂.regs rMinH ≠ inst.n := fun heq =>
      hx₂_meq heq g (by omega) ⟨hg0, by simpa using hgn, hgne⟩
    obtain ⟨hm0, hm_emp, hmin⟩ := hx₂_mlt (by omega)
    have hle1 := gapLevel_minimal hm_emp.1 (by simpa using hm_emp.2.1) hm_emp.2.2
    obtain ⟨hg_0, hg_lt, hg_ne⟩ := hval.gapLevel_spec
    have hle2 : x₂.regs rMinH ≤ gapLevel h := by_contra fun hlt =>
      hmin (gapLevel h) (by simpa [hk0] using hg_0) (by omega) ⟨hg_0, by simpa using hg_lt, hg_ne⟩
    omega
  have hf_sum : Fits w (inst.n + inst.n * inst.n) := fits_of_addr hw (by omega)
  have hf_len : Fits w (inst.n + inst.n * inst.n + 1) := fits_of_addr hw (by omega)
  have hf_out1 : Fits w (4 + 2 * inst.n * inst.n + 4 * inst.n + 1) :=
    fits_of_addr hw (by omega)
  obtain ⟨x₃, hx₃_ex, hx₃_ctx, hx₃_acc, hx₃_min, hx₃_idx, hx₃_m0, hx₃_m1, hx₃_low⟩ :
      ∃ x₃, ExecWithin w cutHdr x₂ x₃ 6 ∧
        CtxInv inst x₃ ∧ x₃.regs acc = inst.maxFlowValue ∧ x₃.regs rMinH = gapLevel h ∧
        x₃.regs rIdx = 0 ∧
        x₃.mem (4 + 2 * inst.n * inst.n + 4 * inst.n) = 1 + inst.n + inst.n * inst.n ∧
        x₃.mem (4 + 2 * inst.n * inst.n + 4 * inst.n + 1) = inst.maxFlowValue ∧
        (∀ a, a < 4 + 2 * inst.n * inst.n + 4 * inst.n → x₃.mem a = x.mem a) := by
    refine WP.exists_execWithin ?_
    unfold cutHdr
    wram_exec [hx₂_ctx.hrn, hx₂_ctx.hrnn, hx₂_ctx.hone, hx₂_ctx.houtBase, hx₂_ctx.hzero, hx₂_acc,
      hf_sum, hf_len, hf_out1, fits_val_of_le_n_maxCap hw inst.maxFlowValue_le]
    refine ⟨(((hx₂_ctx.set (by decide)).set (by decide)).write_ge
        (baseF_le_baseOut inst.n 0)).set (by decide) |>.write_ge
        (baseF_le_baseOut inst.n 1) |>.set (by decide),
      by wram_simp [hx₂_acc],
      by wram_simp [hgap_eq],
      by wram_simp, ?_,
      by rw [Data.set_mem, Data.write_mem_self], fun a ha => ?_⟩
    · rw [Data.set_mem, Data.write_mem_of_ne (by omega), Data.set_mem, Data.write_mem_self]; omega
    · rw [Data.set_mem, Data.write_mem_of_ne (by omega), Data.set_mem,
        Data.write_mem_of_ne (by omega), Data.set_mem, Data.set_mem, hx₂_mem]
  let PCut (k : ℕ) (s : Data 32) : Prop :=
    CtxInv inst s ∧ s.regs acc = inst.maxFlowValue ∧ s.regs rMinH = gapLevel h ∧
    (∀ a, a < 4 + 2 * inst.n * inst.n + 4 * inst.n + 2 → s.mem a = x₃.mem a) ∧
    (∀ v : Fin inst.n, v.val < k →
      s.mem (4 + 2 * inst.n * inst.n + 4 * inst.n + 2 + v.val) =
        if v ∈ inst.out.cut then 1 else 0)
  have hcut_body (s : Data 32) (hs : PCut (s.regs rIdx) s) (hlt : s.regs rIdx < inst.n) :
      ∃ s', ExecWithin w writeCutBody s s' 8 ∧ PCut (s.regs rIdx + 1) s' ∧
        s'.regs rIdx = s.regs rIdx + 1 := by
    obtain ⟨hsc, hsacc, hsmin, hslow, hscut⟩ := hs
    set k := s.regs rIdx
    have hk_def : s.regs rIdx = k := rfl
    let v : Fin inst.n := ⟨k, hlt⟩
    have hhv : s.mem (4 + 2 * inst.n * inst.n + inst.n + k) = h v := by
      rw [hslow _ (by omega), hx₃_low _ (by omega)]; exact hxca.hheight v
    obtain ⟨_, hf_hv, _, hf_k1⟩ := fits_vtx hw v
    have hf_o2 : Fits w (4 + 2 * inst.n * inst.n + 4 * inst.n + 2) := fits_of_addr hw (by omega)
    have hf_o2k : Fits w (4 + 2 * inst.n * inst.n + 4 * inst.n + 2 + k) :=
      fits_of_addr hw (by omega)
    have hv_in : v ∈ inst.out.cut ↔ gapLevel h < h v := by rw [hout_cut, mem_gapCut]
    have hpost_cut (bval : ℕ) (hb : bval = if v ∈ inst.out.cut then 1 else 0) :
        let s' := (((((s.set rAddr ((4 + 2 * inst.n * inst.n + inst.n) + k)).set rVal (h v)).set
          rAddr2 ((4 + 2 * inst.n * inst.n + 4 * inst.n) + 2)).set
          rAddr2 (((4 + 2 * inst.n * inst.n + 4 * inst.n) + 2) + k)).write
          (((4 + 2 * inst.n * inst.n + 4 * inst.n) + 2) + k) bval).set rIdx (k + 1)
        PCut (k + 1) s' ∧ s'.regs rIdx = k + 1 :=
      ⟨⟨(((((hsc.set (by decide)).set (by decide)).set (by decide)).set (by decide)).write_ge
          (by omega)).set (by decide),
        by wram_simp [hsacc],
        by wram_simp [hsmin],
        fun a ha => (Data.write_mem_of_ne (by omega) _).trans (hslow a ha),
        fun w hw_lt => by
          by_cases hwv : w.val = k
          · obtain rfl : w = v := Fin.ext hwv
            rw [Data.set_mem, show v.val = k from rfl, Data.write_mem_self, hb]
          · rw [Data.set_mem, Data.write_mem_of_ne (by omega)]
            exact hscut w (by omega)⟩,
        by wram_simp⟩
    refine WP.exists_execWithin ?_
    unfold writeCutBody
    by_cases hgt : gapLevel h < h v
    · wram_exec [hk_def, hsc.hbaseH, hhv, hsc.houtBase, hsc.hrTwo, hsmin, hgt, hsc.hone,
        hf_hv, hf_o2, hf_o2k, hf_k1]
      exact hpost_cut 1 (ite_eq_left (hv_in.mpr hgt)).symm
    · wram_exec [hk_def, hsc.hbaseH, hhv, hsc.houtBase, hsc.hrTwo, hsmin, hgt, hsc.hzero, hsc.hone,
        hf_hv, hf_o2, hf_o2k, hf_k1]
      exact hpost_cut 0 (ite_eq_right (mt hv_in.mp hgt)).symm
  obtain ⟨x₄, hx₄_ex, hx₄_P, _⟩ := ExecWithin.loop_count PCut
    (fun s hs => hs.1.hrn) hcut_body (by rw [hx₃_idx]; exact Nat.zero_le _)
    ⟨hx₃_ctx, hx₃_acc, hx₃_min, fun _ _ => rfl, fun _ h => by rw [hx₃_idx] at h; omega⟩
  rw [hx₃_idx, Nat.sub_zero] at hx₄_ex
  obtain ⟨hx₄_ctx, hx₄_acc, _, hx₄_low, hx₄_cut⟩ := hx₄_P
  have hprep_fl : ExecWithin (B := .standard) w (ram[ rIdx ← zero ]) x₄ (x₄.set rIdx 0) 1 := by
    ram_eval [hx₄_ctx.hzero]
  set x₅ := x₄.set rIdx 0
  have hx₅_ctx : CtxInv inst x₅ := hx₄_ctx.set (by decide)
  let PFlow (k : ℕ) (s : Data 32) : Prop :=
    CtxInv inst s ∧ s.regs acc = inst.maxFlowValue ∧
    (∀ a, a < 4 + 2 * inst.n * inst.n + 4 * inst.n + 2 + inst.n → s.mem a = x₄.mem a) ∧
    (∀ u v : Fin inst.n, u.val * inst.n + v.val < k →
      s.mem (4 + 2 * inst.n * inst.n + 4 * inst.n + 2 + inst.n + (u.val * inst.n + v.val)) =
        inst.out.flow u v)
  have hflow_body (s : Data 32) (hs : PFlow (s.regs rIdx) s)
      (hlt : s.regs rIdx < inst.n * inst.n) :
      ∃ s', ExecWithin w copyFlowBody s s' 7 ∧ PFlow (s.regs rIdx + 1) s' ∧
        s'.regs rIdx = s.regs rIdx + 1 := by
    obtain ⟨hsc, hsacc, hslow, hsfl⟩ := hs
    set k := s.regs rIdx
    have hk_def : s.regs rIdx = k := rfl
    let u : Fin inst.n := ⟨k / inst.n, Nat.div_lt_of_lt_mul hlt⟩
    let v : Fin inst.n := ⟨k % inst.n, Nat.mod_lt _ hn⟩
    have hk_eq : u.val * inst.n + v.val = k := by
      simpa [u, v, Nat.mul_comm] using Nat.div_add_mod k inst.n
    have hfl_val : s.mem (4 + inst.n * inst.n + k) = inst.out.flow u v := by
      rw [hslow _ (by omega), hx₄_low _ (by omega), hx₃_low _ (by omega),
        ← hk_eq, hxca.hflow u v, hout_flow]
      rfl
    have hf_f : Fits w (4 + inst.n * inst.n + k) := fits_of_addr hw (by omega)
    have hf_o2 : Fits w (4 + 2 * inst.n * inst.n + 4 * inst.n + 2) := fits_of_addr hw (by omega)
    have hf_o2n : Fits w (4 + 2 * inst.n * inst.n + 4 * inst.n + 2 + inst.n) :=
      fits_of_addr hw (by omega)
    have hf_o2nk : Fits w (4 + 2 * inst.n * inst.n + 4 * inst.n + 2 + inst.n + k) :=
      fits_of_addr hw (by omega)
    have hf_k1 : Fits w (k + 1) := fits_of_addr hw (by omega)
    refine WP.exists_execWithin ?_
    unfold copyFlowBody
    wram_exec [hk_def, hsc.hbaseF, hfl_val, hsc.houtBase, hsc.hrTwo, hsc.hrn, hsc.hone,
      hf_f, hf_o2, hf_o2n, hf_o2nk, hf_k1]
    refine ⟨⟨((((((hsc.set (by decide)).set (by decide)).set (by decide)).set (by decide)).set
        (by decide)).write_ge (by omega)).set (by decide),
      by wram_simp [hsacc],
      fun a ha => by rw [Data.set_mem, Data.write_mem_of_ne (by omega)]; exact hslow a ha,
      fun a b hab => ?_⟩, by wram_simp⟩
    by_cases hkeq : a.val * inst.n + b.val = k
    · obtain ⟨rfl, rfl⟩ := fin_pair_inj (hkeq.trans hk_eq.symm)
      rw [Data.set_mem, hk_eq, Data.write_mem_self]
    · rw [Data.set_mem, Data.write_mem_of_ne (by omega)]
      exact hsfl a b (by omega)
  obtain ⟨y, hy_ex, hy_P, _⟩ := ExecWithin.loop_count PFlow
    (fun s hs => hs.1.hrnn) hflow_body (by simp [x₅])
    ⟨hx₅_ctx, hx₄_acc, fun _ _ => rfl, fun _ _ h => by simp [x₅] at h⟩
  simp only [show x₅.regs rIdx = 0 from by simp [x₅], Nat.sub_zero] at hy_ex
  obtain ⟨hy_ctx, hy_acc, hy_low, hy_fl⟩ := hy_P
  refine ⟨y, (hx₁_ex.seq (hx₂_ex.seq (hx₃_ex.seq (hx₄_ex.seq (hprep_fl.seq hy_ex))))).mono
      (hx₁_cur ▸ cut_mono_le inst.n),
    hy_ctx, hy_acc, ?_⟩
  rw [hy_ctx.houtBase]
  exact outputList_eq_answerWords inst y.mem
    (by rw [hy_low _ (by omega), hx₄_low _ (by omega), hx₃_m0])
    (by rw [hy_low _ (by omega), hx₄_low _ (by omega), hx₃_m1])
    (fun v => by rw [hy_low _ (by have := v.isLt; omega), hx₄_cut v v.isLt])
    (fun u v => hy_fl u v (List.mul_add_lt_sq u.isLt v.isLt))

/-- Structured execution of `solver` completes within `prTime inst.n - 1` instructions at any
word width admitting `inst.wordBound`, writing `inst.answerWords` at `outBase` and
`inst.maxFlowValue` in register `acc`. -/
private theorem solver_spec (inst : Instance) {w : ℕ} (hw : Fits w inst.wordBound) :
    ∃ y, ExecWithin w solver (Data.init inst.encode) y (prTime inst.n - 1) ∧
      y.regs outBase = 4 + 2 * inst.n * inst.n + 4 * inst.n ∧
      y.regs acc = inst.maxFlowValue ∧
      outputList y.mem (y.regs outBase) = inst.answerWords := by
  have hn := inst.n_pos
  have hsub : 720 * inst.n ^ 3 + 40 - 1 = 720 * inst.n ^ 3 + 39 := by omega
  obtain ⟨y₁, hy₁_ex, hy₁_ctx⟩ := setupCode_spec inst hw
  by_cases hst : inst.s = inst.t
  · obtain ⟨y₂, hy₂_ex, hy₂_ctx, hy₂_acc, hy₂_out⟩ := zeroOutCode_spec inst hw hst hy₁_ctx
    have hbr := execWithin_branch_pos (c := .eq rs rt)
      (e := initNonTermCode.seq (outerCode.seq cutAndOutputCode))
      (by simp only [Cond.holds_eq, hy₁_ctx.hrs, hy₁_ctx.hrt, congrArg Fin.val hst])
      hy₂_ex (T' := 5 * inst.n * inst.n + 5 * inst.n + 16) (by omega)
    refine ⟨y₂, (hy₁_ex.seq hbr).mono ?_, hy₂_ctx.houtBase, hy₂_acc, hy₂_out⟩
    unfold prTime
    rw [hsub]
    have : inst.n * inst.n ≤ inst.n ^ 3 := calc
      inst.n * inst.n = 1 * (inst.n * inst.n) := by ring
      _ ≤ inst.n * (inst.n * inst.n) := Nat.mul_le_mul_right _ hn
      _ = inst.n ^ 3 := by ring
    nlinarith [Nat.le_self_pow (by decide : 3 ≠ 0) inst.n]
  · have h2n := two_le_n_of_ne inst hst
    obtain ⟨y₂, hy₂_ex, hy₂_ctx, hy₂_rtf⟩ := initNonTermCode_spec inst hw hst hy₁_ctx
    obtain ⟨y₃, hy₃_ex, hy₃_ctx, hcaInv, hnot_act, hy₃_ca⟩ :=
      outerCode_spec inst hw hst hy₂_ctx hy₂_rtf
    obtain ⟨y₄, hy₄_ex, hy₄_ctx, hy₄_acc, hy₄_out⟩ :=
      cutAndOutputCode_spec inst hw hst hy₃_ctx hcaInv hnot_act hy₃_ca
    have hbr := execWithin_branch_neg (c := .eq rs rt) (t := zeroOutCode)
      (by
        simp only [Cond.holds_eq, hy₁_ctx.hrs, hy₁_ctx.hrt]
        exact fun h => hst (Fin.ext h))
      (hy₂_ex.seq (hy₃_ex.seq hy₄_ex))
      (T' := (5 * inst.n * inst.n + 40 * inst.n + 18) + (590 * inst.n ^ 3 + 76 * inst.n ^ 2 + 2) +
        (19 * inst.n * inst.n + 24 * inst.n + 20) + 2) (by omega)
    refine ⟨y₄, (hy₁_ex.seq hbr).mono ?_, hy₄_ctx.houtBase, hy₄_acc, hy₄_out⟩
    unfold prTime
    rw [hsub]
    nlinarith

/-- **`O(|V|³)` Word-RAM relabel-to-front maximum flow & minimum gap cut (`ExecutesList`).**
For any instance `inst` and word width `w` satisfying `Fits w inst.wordBound`, `program` halts
within `prTime inst.n = 720 * n ^ 3 + 40` instructions (final `halt` included) and outputs
`inst.answerWords = [maxFlowValue, cutIndicators..., flowMatrix...]`. -/
theorem program_spec (inst : Instance) {w : ℕ} (hw : Fits w inst.wordBound) :
    ∃ steps ≤ prTime inst.n,
      ExecutesList w program (.init inst.encode) inst.answerWords steps := by
  obtain ⟨y, ⟨steps, hsteps, hexec⟩, hyout, _, hylist⟩ := solver_spec inst hw
  have hfit_out : Fits w (y.regs outBase + (outputList y.mem (y.regs outBase)).length) := by
    rw [hylist, hyout, inst.length_answerWords]
    exact fits_of_addr hw (by have := inst.n_pos; nlinarith)
  refine ⟨steps + 1, by unfold prTime at hsteps ⊢; omega, ?_⟩
  have hex := hexec.executesList outBase hfit_out
  rwa [hylist] at hex

/-- Fixed-program `Program.ComputesListInTime` certificate for `O(n³)` Word-RAM relabel-to-front
returning `inst.answerWords` (`maxFlowValue`, minimum gap cut, and maximum flow matrix). -/
theorem computesListInTime_pushRelabel :
    program.ComputesListInTime (fun _ inst => inst.encode)
      (fun inst _ => prTime inst.n) (fun inst w => Fits w inst.wordBound)
      Instance.answerWords := by
  intro inst w hw _
  obtain ⟨steps, hle, hex⟩ := program_spec inst hw
  exact ⟨steps, hex, hle⟩

/-- **`O(|V|³)` Word-RAM scalar maximum-flow value (`Executes`).** -/
theorem executes_maxFlowValue (inst : Instance) {w : ℕ} (hw : Fits w inst.wordBound) :
    ∃ steps, Executes w flowProgram (.init inst.encode) inst.maxFlowValue steps ∧
      steps ≤ prTime inst.n := by
  obtain ⟨y, ⟨steps, hsteps, hexec⟩, _, hyacc, _⟩ := solver_spec inst hw
  refine ⟨steps + 1, hyacc ▸ hexec.executes acc, ?_⟩
  unfold prTime at hsteps ⊢
  omega

/-- Fixed-program `Program.ComputesInTime` certificate for `O(n³)` Word-RAM relabel-to-front
returning `inst.maxFlowValue`. -/
theorem computesInTime_maxFlowValue :
    flowProgram.ComputesInTime (fun _ inst => inst.encode)
      (fun inst _ => prTime inst.n) (fun inst w => Fits w inst.wordBound)
      Instance.maxFlowValue :=
  fun inst _ hw _ => executes_maxFlowValue inst hw

/-- `program` does not inspect the word width (`width%`). -/
theorem not_readsWidth_program : ¬ program.ReadsWidth := by
  apply Code.not_readsWidth_program
  decide +kernel

/-- `program` is deterministic (`rand`-free). -/
theorem isRandFree_program : program.IsRandFree := by
  rw [program, Code.isRandFree_program]
  decide +kernel

/-- `flowProgram` does not inspect the word width (`width%`). -/
theorem not_readsWidth_flowProgram : ¬ flowProgram.ReadsWidth := by
  apply Code.not_readsWidth_program
  decide +kernel

/-- `flowProgram` is deterministic (`rand`-free). -/
theorem isRandFree_flowProgram : flowProgram.IsRandFree := by
  rw [flowProgram, Code.isRandFree_program]
  decide +kernel

end OutputAndMain

end Cslib.Algorithms.WordRAM.PushRelabel
