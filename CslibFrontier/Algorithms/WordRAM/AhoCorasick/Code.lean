/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.AhoCorasick.Layout
import CslibFrontier.Computability.WordRAM.Allocation

/-!
# Structured Word-RAM Code for Aho–Corasick

Internal `Code .standard 26` program blocks for all four execution phases of `searchCode`:
`setupAndClearCode`, `buildTrieCode`, `bfsBuildCode`, and `scanCode`. All blocks live in one
module isolated from the pure correctness models and proofs, exposed to sibling phase modules so
`wram_exec` and `writeStart` checks can unfold them cleanly. Downstream clients importing
`CslibFrontier.Algorithms.WordRAM.AhoCorasick` receive only `searchCode` and `searchProgram`.

## Main definitions

* `Cslib.Algorithms.WordRAM.AhoCorasick.setupAndClearCode`: Phase 1 header decode and zero-fill.
* `Cslib.Algorithms.WordRAM.AhoCorasick.buildTrieCode`: Phase 2 flat-array trie builder.
* `Cslib.Algorithms.WordRAM.AhoCorasick.bfsBuildCode`: Phase 3 BFS failure/next-move/output pass.
* `Cslib.Algorithms.WordRAM.AhoCorasick.scanCode`: Phase 4 amortized text scanner.
-/

public section

namespace Cslib.Algorithms.WordRAM.AhoCorasick

open Cslib.WordRAM
open Reg

/-! ## Word-RAM structured code -/

/-- Load the serialized header metadata `(σ, |P|, ‖P‖, |t|)` into layout registers. -/
@[expose] def setupHeaderCode : Code .standard 26 := ram[
  zero ← #0;
  one ← #1;
  r6 ← #1; sigma ← *r6;
  r6 ← #2; numPat ← *r6;
  r6 ← #3; totPat ← *r6;
  r6 ← #4; textLen ← *r6;
  maxS ← totPat + one;
  patBase ← #5 ]

/-- Compute all scratch-array base address registers from the loaded header metadata. -/
@[expose] def setupBaseCode : Code .standard 26 := ram[
  textBase ← patBase + numPat;
  textBase ← textBase + totPat;
  trieBase ← textBase + textLen;
  r7 ← maxS * sigma;
  deltaBase ← trieBase + r7;
  failBase ← deltaBase + r7;
  depthBase ← failBase + maxS;
  termBase ← depthBase + maxS;
  outHeadBase ← termBase + maxS;
  outNextBase ← outHeadBase + maxS;
  queueBase ← outNextBase + maxS;
  out ← queueBase + maxS;
  r1 ← trieBase ]

/-- Header decode and workspace base-address initialization (`setupHeaderCode; setupBaseCode`). -/
@[expose] def setupCode : Code .standard 26 :=
  .seq setupHeaderCode setupBaseCode

/-- Phase 1 code: decode header registers and zero-fill all scratch arrays `[trieBase, out)`. -/
@[expose] def setupAndClearCode : Code .standard 26 :=
  .seq setupCode (zeroFill r1 out zero one)

/-- Branch allocating a fresh trie state if `trie[u, a] = 0`, or moving to existing child `r7`. -/
@[expose] def trieCharBranchCode : Code .standard 26 :=
  .branch (.lt zero r7)
    (ram[ r4 ← r7 ])
    (ram[
      *r6 ← rState;
      r7 ← depthBase + r4;
      r7 ← *r7;
      r7 ← r7 + one;
      r6 ← depthBase + rState;
      *r6 ← r7;
      r4 ← rState;
      rState ← rState + one ])

/-- Inner trie insertion step processing a single keyword character `a = *r2`. -/
@[expose] def trieCharStepCode : Code .standard 26 :=
  .seq
    (ram[
      r5 ← *r2;
      r2 ← r2 + one;
      r3 ← r3 - one;
      r6 ← r4 * sigma;
      r6 ← r6 + r5;
      r6 ← trieBase + r6;
      r7 ← *r6 ])
    trieCharBranchCode

/-- Mark non-root terminal state `term[r4] := 1` and decrement remaining keyword counter `r1`. -/
@[expose] def triePatBranchCode : Code .standard 26 :=
  .branch (.lt zero r4)
    (ram[ r6 ← termBase + r4; *r6 ← one; r1 ← r1 - one ])
    (ram[ r1 ← r1 - one ])

/-- Outer trie insertion step parsing one length-prefixed keyword from `r2`. -/
@[expose] def triePatStepCode : Code .standard 26 :=
  .seq
    (ram[
      r3 ← *r2;
      r2 ← r2 + one;
      r4 ← #0 ])
    (.seq
      (.loop (.lt zero r3) trieCharStepCode)
      triePatBranchCode)

/-- Phase 2 code: construct the flat `maxS × σ` array trie (`Algorithm 2`). -/
@[expose] def buildTrieCode : Code .standard 26 :=
  .seq
    (ram[ rState ← #1; r1 ← numPat; r2 ← patBase ])
    (.loop (.lt zero r1) triePatStepCode)

/-- Depth-1 BFS step initializing `delta[0, r5]` and enqueueing children of root `0`. -/
@[expose] def bfsRootStepCode : Code .standard 26 :=
  .seq (ram[ r6 ← trieBase + r5; r6 ← *r6 ])
    (.branch (.lt zero r6)
      (.seq
        (ram[
          r7 ← deltaBase + r5; *r7 ← r6;
          r7 ← failBase + r6; *r7 ← zero;
          r7 ← queueBase + r2; *r7 ← r6;
          r2 ← r2 + one;
          r7 ← outNextBase + r6; *r7 ← zero;
          rState ← termBase + r6; rState ← *rState ])
        (.branch (.lt zero rState)
          (ram[ r7 ← outHeadBase + r6; *r7 ← r6; r5 ← r5 + one ])
          (ram[ r7 ← outHeadBase + r6; *r7 ← zero; r5 ← r5 + one ])))
      (ram[ r7 ← deltaBase + r5; *r7 ← zero; r5 ← r5 + one ]))

/-- Write `delta[r, a]`, `fail[s]`, and enqueue newly discovered trie child `s`. -/
@[expose] def bfsInnerStoreCode : Code .standard 26 := ram[
  rState ← r3 * sigma; rState ← rState + r5; rState ← deltaBase + rState; *rState ← r6;
  rState ← failBase + r6; *rState ← r7;
  rState ← queueBase + r2; *rState ← r6;
  r2 ← r2 + one ]

/-- Link `outNext[s]` to `outHead[fail[s]]` and load `term[s]` into `rState`. -/
@[expose] def bfsInnerLinkCode : Code .standard 26 := ram[
  r7 ← outHeadBase + r7; r7 ← *r7;
  rState ← outNextBase + r6; *rState ← r7;
  rState ← termBase + r6; rState ← *rState ]

/-- Inner BFS step over symbol `r5` of dequeued state `r3` (failure link in `r4`). -/
@[expose] def bfsInnerStepCode : Code .standard 26 :=
  .seq
    (ram[
      r6 ← r3 * sigma; r6 ← r6 + r5; r6 ← trieBase + r6; r6 ← *r6;
      r7 ← r4 * sigma; r7 ← r7 + r5; r7 ← deltaBase + r7; r7 ← *r7 ])
    (.branch (.lt zero r6)
      (.seq
        (.seq bfsInnerStoreCode bfsInnerLinkCode)
        (.branch (.lt zero rState)
          (ram[ rState ← outHeadBase + r6; *rState ← r6; r5 ← r5 + one ])
          (ram[ rState ← outHeadBase + r6; *rState ← r7; r5 ← r5 + one ])))
      (ram[
        rState ← r3 * sigma; rState ← rState + r5; rState ← deltaBase + rState; *rState ← r7;
        r5 ← r5 + one ]))

/-- Outer BFS step dequeuing state `r3 = queue[r1]` and sweeping `a ∈ [0, σ)`. -/
@[expose] def bfsOuterStepCode : Code .standard 26 :=
  .seq
    (ram[
      r3 ← queueBase + r1; r3 ← *r3;
      r1 ← r1 + one;
      r4 ← failBase + r3; r4 ← *r4;
      r5 ← #0 ])
    (.loop (.lt r5 sigma) bfsInnerStepCode)

/-- Phase 3 code: breadth-first failure, `delta`, and output-link construction (`Algorithm 3`). -/
@[expose] def bfsBuildCode : Code .standard 26 :=
  .seq
    (.seq (ram[ r1 ← #0; r2 ← #0; r5 ← #0 ]) (.loop (.lt r5 sigma) bfsRootStepCode))
    (.loop (.lt r1 r2) bfsOuterStepCode)

/-- Set `r7 := 1` iff `rState > 0` and `trie[rState, r5] = 0` (failure loop guard). -/
@[expose] def computeFailCond : Code .standard 26 :=
  .seq (ram[ r7 ← #0 ])
    (.branch (.lt zero rState)
      (.seq
        (ram[
          r6 ← rState * sigma;
          r6 ← r6 + r5;
          r6 ← trieBase + r6;
          r6 ← *r6 ])
        (.branch (.lt zero r6)
          (ram[ r7 ← #0 ])
          (ram[ r7 ← #1 ])))
      (ram[ r7 ← #0 ]))

/-- Single amortized text-scanning transition following `fail` links to a matching edge (`r5`). -/
@[expose] def stepCode : Code .standard 26 :=
  .seq computeFailCond
    (.seq
      (.loop (.lt zero r7)
        (.seq (ram[ r6 ← failBase + rState; rState ← *r6 ]) computeFailCond))
      (ram[
        r6 ← rState * sigma;
        r6 ← r6 + r5;
        r6 ← trieBase + r6;
        rState ← *r6 ]))

/-- Single output-chain emission step appending `[r3, depth[r4]]` to `*r2` and advancing `r4`. -/
@[expose] def emitStepCode : Code .standard 26 := ram[
  r6 ← depthBase + r4;
  r6 ← *r6;
  *r2 ← r3;
  r2 ← r2 + one;
  *r2 ← r6;
  r2 ← r2 + one;
  r6 ← outNextBase + r4;
  r4 ← *r6 ]

/-- Walk the linked output chain starting at `outHead[rState]`, emitting all matches at `r3`. -/
@[expose] def emitCode : Code .standard 26 :=
  .seq (ram[ r6 ← outHeadBase + rState; r4 ← *r6 ])
    (.loop (.lt zero r4) emitStepCode)

/-- Process text character `text[r1]`, updating `rState` via `stepCode` and emitting matches. -/
@[expose] def scanStepCode : Code .standard 26 :=
  .seq
    (ram[
      r6 ← textBase + r1;
      r5 ← *r6;
      r3 ← r1 + one ])
    (.seq stepCode (.seq emitCode (ram[ r1 ← r3 ])))

/-- Phase 4 code: scan `text[0..textLen)` and write the length-prefixed `[pos, len]` list at
`out`. -/
@[expose] def scanCode : Code .standard 26 :=
  .seq
    (ram[
      rState ← #0;
      r1 ← #0;
      r2 ← out + one ])
    (.seq
      (.loop (.lt r1 textLen) scanStepCode)
      (ram[
        r6 ← out + one;
        r6 ← r2 - r6;
        *out ← r6 ]))

end Cslib.Algorithms.WordRAM.AhoCorasick
