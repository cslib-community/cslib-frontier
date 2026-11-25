/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.Arborescence.Internal.BasicProg
import CslibFrontier.Foundations.Data.List.RowMajor
import CslibFrontier.Tactic.Realize

/-!
# Core Chu–Liu/Edmonds phase programs and `Realizes` certificates (internal)

Defines `bestEntryProg`, `bestExitProg`, `contractTablesProg`, `expandLevelProg`, and
`edmondsCoreProg` over `Memory.Prog`, together with their `Realizes .exact` certificates.
-/

namespace Cslib.Algorithms.WordRAM.Arborescence.Internal

open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization
open Cslib.WordRAM.Realization.Signed

-- 6. `bestEntryProg` and `bestExitProg` (with Edmonds §4 reduced exit costs)

/-- Parameters for scanning arcs entering a cycle from non-cycle vertex `u`. -/
public structure BestEntryRowArgs where
  /-- Matrix dimension (number of vertices). -/
  n : ℕ
  /-- Source non-cycle vertex index `u`. -/
  u : ℕ
  /-- Base address of the working `n × n` adjacency table. -/
  adjBase : ℕ
  /-- Base address of the working `n × n` cost table. -/
  costBase : ℕ
  /-- Base address of the `n`-word `0`/`1` cycle-membership mask. -/
  maskBase : ℕ
  /-- Output base address for candidate feasibility indicators (`n` words). -/
  predOut : ℕ
  /-- Output base address for candidate signed costs (`n` words). -/
  costOut : ℕ

private word_enc_structure encBestEntryRowArgs : BestEntryRowArgs where
  n : wordWords, u : wordWords, adjBase : wordWords, costBase : wordWords,
  maskBase : wordWords, predOut : wordWords, costOut : wordWords

private instance : WordEncoding BestEntryRowArgs := ⟨7, encBestEntryRowArgs⟩

/-- Writes candidate feasibility `(inY = 1 ∧ auy = 1)` and cost for target `y` from `env.u`. -/
@[expose] public def bestEntryRowStep (q : BestEntryRowArgs × ℕ) : Memory.Prog ℕ := do
  let env := Prod.fst q
  let y := Prod.snd q
  let inY ← Memory.read (env.maskBase + y)
  let auy ← Memory.read (env.adjBase + env.u * env.n + y)
  let cuy ← Memory.read (env.costBase + env.u * env.n + y)
  let pv := if inY = 1 ∧ auy = 1 then 1 else 0
  Memory.write (env.predOut + y) pv
  Memory.write (env.costOut + y) cuy
  pure (y + 1)

/-- Address-fit safety precondition for one step of `bestEntryRowStep`. -/
public abbrev BestEntryRowStepSafe (w : ℕ) (q : BestEntryRowArgs × ℕ) (_ : Memory.State) : Prop :=
  let env := Prod.fst q
  let y := Prod.snd q
  Fits w 1 ∧ Fits w (env.maskBase + y) ∧ Fits w (env.adjBase + env.u * env.n + y) ∧
    Fits w (env.costBase + env.u * env.n + y) ∧ Fits w (env.predOut + y) ∧
    Fits w (env.costOut + y) ∧ Fits w (y + 1)

private theorem bestEntryRowStep_realizes :
    Realizes .exact bestEntryRowStep (appendWords encBestEntryRowArgs wordWords) wordWords
      BestEntryRowStepSafe (fun _ _ => 0) := by
  unfold bestEntryRowStep
  realize
  all_goals
    obtain ⟨h1, hm, ha, hc, hp, hco, hy⟩ := h
    first | exact h1 | exact hm | exact ha | exact hc | exact hp | exact hco | exact hy

/-- Fills candidate entry feasibility and cost arrays for source vertex `a.u`. -/
@[expose] public def fillBestEntryRowProg (a : BestEntryRowArgs) : Memory.Prog ℕ :=
  iterate bestEntryRowStep a a.n 0

private theorem fillBestEntryRowProg_realizes :
    Realizes .exact fillBestEntryRowProg encBestEntryRowArgs wordWords
      (fun w a s => iterationSafe bestEntryRowStep BestEntryRowStepSafe w a a.n 0 s)
      (fun _ _ => 0) := by
  unfold fillBestEntryRowProg
  realize [bestEntryRowStep_realizes]
  exact h

/-- Parameters referencing contraction stack frame `k` within workspace `ws`. -/
public structure LevelArgs where
  /-- Matrix dimension (number of vertices). -/
  n : ℕ
  /-- Workspace base address. -/
  ws : ℕ
  /-- Contraction stack frame index. -/
  k : ℕ

private word_enc_structure encLevelArgs : LevelArgs where
  n : wordWords, ws : wordWords, k : wordWords

private instance : WordEncoding LevelArgs := ⟨3, encLevelArgs⟩

/-- Computes and stores the best cycle-entry vertex `bEntry[u]` into frame `env.k`. -/
@[expose] public def bestEntryOuterStep (q : LevelArgs × ℕ) : Memory.Prog ℕ := do
  let env := Prod.fst q
  let u := Prod.snd q
  let _ ← Memory.read 0
  let rowArgs : BestEntryRowArgs :=
    ⟨env.n, u, curAdjBase env.ws env.n, curCostBase env.ws env.n,
      frameMaskBase env.ws env.n env.k, candPredBase env.ws env.n, candCostBase env.ws env.n⟩
  let _ ← fillBestEntryRowProg rowArgs
  let best ← argMinArrayProg ⟨env.n, candPredBase env.ws env.n, candCostBase env.ws env.n⟩
  Memory.write (frameBEntryBase env.ws env.n env.k + u) best
  pure (u + 1)

/-- Safety precondition for one source vertex in `bestEntryOuterStep`. -/
public abbrev BestEntryOuterStepSafe (w : ℕ) (q : LevelArgs × ℕ) (s : Memory.State) : Prop :=
  let env := Prod.fst q
  let u := Prod.snd q
  let rowArgs : BestEntryRowArgs :=
    ⟨env.n, u, curAdjBase env.ws env.n, curCostBase env.ws env.n,
      frameMaskBase env.ws env.n env.k, candPredBase env.ws env.n, candCostBase env.ws env.n⟩
  let s1 := (Memory.spec 0).clientState s (fillBestEntryRowProg rowArgs)
  u < env.n ∧ env.k < env.n ∧ WsFits w env.ws env.n ∧
    iterationSafe bestEntryRowStep BestEntryRowStepSafe w rowArgs env.n 0 s ∧
    iterationSafe argMinStep ArgMinStepSafe w
      ⟨env.n, candPredBase env.ws env.n, candCostBase env.ws env.n⟩ env.n ⟨0, env.n, 0⟩ s1

private theorem bestEntryOuterStep_realizes :
    Realizes .exact bestEntryOuterStep (appendWords encLevelArgs wordWords) wordWords
      BestEntryOuterStepSafe (fun _ _ => 0) := by
  unfold bestEntryOuterStep
  realize [fillBestEntryRowProg_realizes, argMinArrayProg_realizes]
  all_goals
    obtain ⟨hu, hk, hws, hrow, harg⟩ := h
    first
    | exact hrow
    | exact harg
    | exact hws.of_le (by
        dsimp only [wsSize, frameMaskBase, frameBEntryBase, frameBase, curAdjBase, curCostBase,
          candPredBase, candCostBase]
        nlinarith)

/-- Populates `frameBEntryBase` at level `a.k` across all `u < a.n`. -/
@[expose] public def bestEntryProg (a : LevelArgs) : Memory.Prog ℕ :=
  iterate bestEntryOuterStep a a.n 0

private theorem bestEntryProg_realizes :
    Realizes .exact bestEntryProg encLevelArgs wordWords
      (fun w a s => iterationSafe bestEntryOuterStep BestEntryOuterStepSafe w a a.n 0 s)
      (fun _ _ => 0) := by
  unfold bestEntryProg
  realize [bestEntryOuterStep_realizes]
  exact h

/-- Parameters for scanning arcs exiting a cycle toward column `col` with reduced costs. -/
public structure BestExitRowArgs where
  /-- Matrix dimension (number of vertices). -/
  n : ℕ
  /-- Target column index `col`. -/
  col : ℕ
  /-- Base address of the working `n × n` adjacency table. -/
  adjBase : ℕ
  /-- Base address of the working `n × n` cost table. -/
  costBase : ℕ
  /-- Base address of the `n`-word `0`/`1` cycle-membership mask. -/
  maskBase : ℕ
  /-- Base address of the `n`-word selected cycle-parent array. -/
  parentBase : ℕ
  /-- Output base address for candidate feasibility indicators (`n` words). -/
  predOut : ℕ
  /-- Output base address for candidate signed reduced costs (`n` words). -/
  costOut : ℕ

private word_enc_structure encBestExitRowArgs : BestExitRowArgs where
  n : wordWords, col : wordWords, adjBase : wordWords, costBase : wordWords,
  maskBase : wordWords, parentBase : wordWords, predOut : wordWords, costOut : wordWords

private instance : WordEncoding BestExitRowArgs := ⟨8, encBestExitRowArgs⟩

/-- Writes candidate exit feasibility and reduced cost `c[x][col] - c[x][f[x]]` at row `x`. -/
@[expose] public def bestExitRowStep (q : BestExitRowArgs × ℕ) : Memory.Prog ℕ := do
  let env := Prod.fst q
  let x := Prod.snd q
  let inX ← Memory.read (env.maskBase + x)
  let axw ← Memory.read (env.adjBase + x * env.n + env.col)
  let cxw ← Memory.read (env.costBase + x * env.n + env.col)
  let fx ← Memory.read (env.parentBase + x)
  if inX = 1 ∧ axw = 1 then
    let cxfx ← Memory.read (env.costBase + x * env.n + fx)
    let diff ← signedSubProg (cxw, cxfx)
    Memory.write (env.predOut + x) 1
    Memory.write (env.costOut + x) diff
    pure (x + 1)
  else
    Memory.write (env.predOut + x) 0
    Memory.write (env.costOut + x) 0
    pure (x + 1)

/-- Address- and arithmetic-fit safety precondition for one step of `bestExitRowStep`. -/
public abbrev BestExitRowStepSafe (w : ℕ) (q : BestExitRowArgs × ℕ) (s : Memory.State) : Prop :=
  let env := Prod.fst q
  let x := Prod.snd q
  let cxw := s.mem (env.costBase + x * env.n + env.col)
  let fx := s.mem (env.parentBase + x)
  let cxfx := s.mem (env.costBase + x * env.n + fx)
  Fits w 2 ∧ Fits w (env.maskBase + x) ∧ Fits w (env.adjBase + x * env.n + env.col) ∧
    Fits w (env.costBase + x * env.n + env.col) ∧ Fits w (env.parentBase + x) ∧
    Fits w (env.predOut + x) ∧ Fits w (env.costOut + x) ∧ Fits w (x + 1) ∧
    (s.mem (env.maskBase + x) = 1 →
      Fits w (env.costBase + x * env.n + fx) ∧ Fits w (cxfx + 1) ∧
        Fits w (2 * (cxw / 2 + cxfx / 2) + 1))

private theorem bestExitRowStep_realizes :
    Realizes .exact bestExitRowStep (appendWords encBestExitRowArgs wordWords) wordWords
      BestExitRowStepSafe (fun _ _ => 0) := by
  unfold bestExitRowStep
  realize [signedSubProg_realizes]
  all_goals
    obtain ⟨h2, hm, ha, hc, hp, hpo, hco, hx, hsub⟩ := h
    first
    | exact h2
    | exact h2.of_le (by omega)
    | exact hm
    | exact ha
    | exact hc
    | exact hp
    | exact hpo
    | exact hco
    | exact hx
    | exact (hsub ‹_›).1
    | exact (hsub ‹_›).2.1
    | exact (hsub ‹_›).2.2

/-- Fills candidate exit feasibility and reduced cost arrays for target column `a.col`. -/
@[expose] public def fillBestExitRowProg (a : BestExitRowArgs) : Memory.Prog ℕ :=
  iterate bestExitRowStep a a.n 0

private theorem fillBestExitRowProg_realizes :
    Realizes .exact fillBestExitRowProg encBestExitRowArgs wordWords
      (fun w a s => iterationSafe bestExitRowStep BestExitRowStepSafe w a a.n 0 s)
      (fun _ _ => 0) := by
  unfold fillBestExitRowProg
  realize [bestExitRowStep_realizes]
  exact h

/-- Computes and stores the best cycle-exit vertex `bExit[col]` into frame `env.k`. -/
@[expose] public def bestExitOuterStep (q : LevelArgs × ℕ) : Memory.Prog ℕ := do
  let env := Prod.fst q
  let col := Prod.snd q
  let _ ← Memory.read 0
  let rowArgs : BestExitRowArgs :=
    ⟨env.n, col, curAdjBase env.ws env.n, curCostBase env.ws env.n,
      frameMaskBase env.ws env.n env.k, frameParentBase env.ws env.n env.k,
      candPredBase env.ws env.n, candCostBase env.ws env.n⟩
  let _ ← fillBestExitRowProg rowArgs
  let best ← argMinArrayProg ⟨env.n, candPredBase env.ws env.n, candCostBase env.ws env.n⟩
  Memory.write (frameBExitBase env.ws env.n env.k + col) best
  pure (col + 1)

/-- Safety precondition for one target column in `bestExitOuterStep`. -/
public abbrev BestExitOuterStepSafe (w : ℕ) (q : LevelArgs × ℕ) (s : Memory.State) : Prop :=
  let env := Prod.fst q
  let col := Prod.snd q
  let rowArgs : BestExitRowArgs :=
    ⟨env.n, col, curAdjBase env.ws env.n, curCostBase env.ws env.n,
      frameMaskBase env.ws env.n env.k, frameParentBase env.ws env.n env.k,
      candPredBase env.ws env.n, candCostBase env.ws env.n⟩
  let s1 := (Memory.spec 0).clientState s (fillBestExitRowProg rowArgs)
  col < env.n ∧ env.k < env.n ∧ WsFits w env.ws env.n ∧
    iterationSafe bestExitRowStep BestExitRowStepSafe w rowArgs env.n 0 s ∧
    iterationSafe argMinStep ArgMinStepSafe w
      ⟨env.n, candPredBase env.ws env.n, candCostBase env.ws env.n⟩ env.n ⟨0, env.n, 0⟩ s1

private theorem bestExitOuterStep_realizes :
    Realizes .exact bestExitOuterStep (appendWords encLevelArgs wordWords) wordWords
      BestExitOuterStepSafe (fun _ _ => 0) := by
  unfold bestExitOuterStep
  realize [fillBestExitRowProg_realizes, argMinArrayProg_realizes]
  all_goals
    obtain ⟨hcol, hk, hws, hrow, harg⟩ := h
    first
    | exact hrow
    | exact harg
    | exact hws.of_le (by
        dsimp only [wsSize, frameParentBase, frameMaskBase, frameBExitBase, frameBase, curAdjBase,
          curCostBase, candPredBase, candCostBase]
        nlinarith)

/-- Populates `frameBExitBase` at level `a.k` across all `col < a.n`. -/
@[expose] public def bestExitProg (a : LevelArgs) : Memory.Prog ℕ :=
  iterate bestExitOuterStep a a.n 0

private theorem bestExitProg_realizes :
    Realizes .exact bestExitProg encLevelArgs wordWords
      (fun w a s => iterationSafe bestExitOuterStep BestExitOuterStepSafe w a a.n 0 s)
      (fun _ _ => 0) := by
  unfold bestExitProg
  realize [bestExitOuterStep_realizes]
  exact h

-- 8. `contractTablesProg`

/-- Parameters for contracting row `u` of the adjacency and reduced-cost matrices at frame `k`. -/
public structure ContractRowArgs where
  /-- Current matrix dimension (number of vertices). -/
  n : ℕ
  /-- Designated root vertex index. -/
  r : ℕ
  /-- Representative vertex of the contracted cycle. -/
  x0 : ℕ
  /-- Row index being contracted. -/
  u : ℕ
  /-- Workspace base address. -/
  ws : ℕ
  /-- Contraction stack frame index. -/
  k : ℕ

private word_enc_structure encContractRowArgs : ContractRowArgs where
  n : wordWords, r : wordWords, x0 : wordWords, u : wordWords, ws : wordWords, k : wordWords

private instance : WordEncoding ContractRowArgs := ⟨6, encContractRowArgs⟩

private abbrev unitWords : Unit ↪ (Fin 0 → ℕ) :=
  (Equiv.ofUnique Unit (Fin 0 → ℕ)).toEmbedding

/-- Writes contracted adjacency bit `(u, col)` into `nextAdjBase`. -/
@[expose] public def contractAdjCellProg (q : ContractRowArgs × ℕ) : Memory.Prog Unit := do
  let env := Prod.fst q
  let col := Prod.snd q
  let inU ← Memory.read (frameMaskBase env.ws env.n env.k + env.u)
  let inW ← Memory.read (frameMaskBase env.ws env.n env.k + col)
  let auw ← Memory.read (curAdjBase env.ws env.n + env.u * env.n + col)
  let beU ← Memory.read (frameBEntryBase env.ws env.n env.k + env.u)
  let bxW ← Memory.read (frameBExitBase env.ws env.n env.k + col)
  let newAdj :=
    if inU = 1 then
      if env.u = env.x0 then
        if inW = 0 ∧ bxW < env.n then 1 else 0
      else if col = env.r then 1 else 0
    else if inW = 1 then
      if col = env.x0 ∧ beU < env.n then 1 else 0
    else auw
  Memory.write (nextAdjBase env.ws env.n + env.u * env.n + col) newAdj

private abbrev ContractAdjCellSafe (w : ℕ) (q : ContractRowArgs × ℕ) (_ : Memory.State) : Prop :=
  let env := Prod.fst q
  let col := Prod.snd q
  env.u < env.n ∧ col < env.n ∧ env.k < env.n ∧ WsFits w env.ws env.n

private theorem contractAdjCellProg_realizes :
    Realizes .exact contractAdjCellProg (appendWords encContractRowArgs wordWords) unitWords
      ContractAdjCellSafe (fun _ _ => 0) := by
  unfold contractAdjCellProg
  realize
  all_goals
    obtain ⟨hu, hcol, hk, hws⟩ := h
    exact hws.of_le (by
      dsimp only [wsSize, frameMaskBase, frameBEntryBase, frameBExitBase, frameBase, curAdjBase,
        nextAdjBase]
      nlinarith)

/-- Writes contracted signed cost `(u, col)` into `nextCostBase` using reduced exit costs. -/
@[expose] public def contractCostCellProg (q : ContractRowArgs × ℕ) : Memory.Prog Unit := do
  let env := Prod.fst q
  let col := Prod.snd q
  let inU ← Memory.read (frameMaskBase env.ws env.n env.k + env.u)
  let inW ← Memory.read (frameMaskBase env.ws env.n env.k + col)
  let auw ← Memory.read (curAdjBase env.ws env.n + env.u * env.n + col)
  let cuw ← Memory.read (curCostBase env.ws env.n + env.u * env.n + col)
  let beU ← Memory.read (frameBEntryBase env.ws env.n env.k + env.u)
  let bxW ← Memory.read (frameBExitBase env.ws env.n env.k + col)
  let newCost ←
    if inU = 1 then
      if env.u = env.x0 then
        if inW = 0 ∧ bxW < env.n then do
          let cxw ← Memory.read (curCostBase env.ws env.n + bxW * env.n + col)
          let fx ← Memory.read (frameParentBase env.ws env.n env.k + bxW)
          let cxfx ← Memory.read (curCostBase env.ws env.n + bxW * env.n + fx)
          signedSubProg (cxw, cxfx)
        else pure 0
      else pure 0
    else if inW = 1 then
      if col = env.x0 ∧ beU < env.n then
        Memory.read (curCostBase env.ws env.n + env.u * env.n + beU)
      else pure 0
    else if auw = 1 then pure cuw
    else pure 0
  Memory.write (nextCostBase env.ws env.n + env.u * env.n + col) newCost

/-- Address- and arithmetic-fit safety precondition for one contracted cell `(u, col)`. -/
public abbrev ContractRowStepSafe (w : ℕ) (q : ContractRowArgs × ℕ) (s : Memory.State) : Prop :=
  let env := Prod.fst q
  let col := Prod.snd q
  let bxW := s.mem (frameBExitBase env.ws env.n env.k + col)
  let cxw := s.mem (curCostBase env.ws env.n + bxW * env.n + col)
  let fx := s.mem (frameParentBase env.ws env.n env.k + bxW)
  let cxfx := s.mem (curCostBase env.ws env.n + bxW * env.n + fx)
  env.u < env.n ∧ col < env.n ∧ env.k < env.n ∧ WsFits w env.ws env.n ∧
    (s.mem (frameMaskBase env.ws env.n env.k + env.u) = 1 →
      env.u = env.x0 → s.mem (frameMaskBase env.ws env.n env.k + col) = 0 → bxW < env.n →
      fx < env.n ∧ Fits w (cxfx + 1) ∧ Fits w (2 * (cxw / 2 + cxfx / 2) + 1))

private theorem contractCostCellProg_realizes :
    Realizes .exact contractCostCellProg (appendWords encContractRowArgs wordWords) unitWords
      ContractRowStepSafe (fun _ _ => 0) := by
  unfold contractCostCellProg
  realize [signedSubProg_realizes]
  all_goals
    obtain ⟨hu, hcol, hk, hws, hsub⟩ := h
    have hfr := frame_le_frames hk
    have huc := List.mul_add_lt_sq hu hcol
    first
    | exact (hsub ‹_› ‹_› ‹_› ‹_›).2.1
    | exact (hsub ‹_› ‹_› ‹_› ‹_›).2.2
    | exact hws.of_le (by
        dsimp only [wsSize, frameParentBase, frameMaskBase, frameBEntryBase, frameBExitBase,
          frameBase, curAdjBase, curCostBase, nextCostBase]
        omega)
    | exact hws.of_le (by
        have hbx : s.mem (frameBExitBase d.1.ws d.1.n d.1.k + d.2) < d.1.n := ‹_›
        have hbx_c := List.mul_add_lt_sq hbx hcol
        have hfx := (hsub ‹_› ‹_› ‹_› hbx).1
        have hbx_f := List.mul_add_lt_sq hbx hfx
        dsimp only [wsSize, frameParentBase, frameMaskBase, frameBEntryBase, frameBExitBase,
          frameBase, curAdjBase, curCostBase, nextCostBase] at hbx hbx_c hfx hbx_f ⊢
        omega)
    | exact hws.of_le (by
        have hbe : s.mem (frameBEntryBase d.1.ws d.1.n d.1.k + d.1.u) < d.1.n := ‹_›
        have hu_be := List.mul_add_lt_sq hu hbe
        dsimp only [wsSize, frameParentBase, frameMaskBase, frameBEntryBase, frameBExitBase,
          frameBase, curAdjBase, curCostBase, nextCostBase] at hbe hu_be ⊢
        omega)

/-- Contracts one cell `(env.u, col)` in cost then adjacency order. -/
@[expose] public def contractRowStep (q : ContractRowArgs × ℕ) : Memory.Prog ℕ := do
  contractCostCellProg q
  contractAdjCellProg q
  pure (Prod.snd q + 1)

private theorem contractRowStep_realizes :
    Realizes .exact contractRowStep (appendWords encContractRowArgs wordWords) wordWords
      ContractRowStepSafe (fun _ _ => 0) := by
  unfold contractRowStep
  realize [contractCostCellProg_realizes, contractAdjCellProg_realizes]
  all_goals
    obtain ⟨hu, hcol, hk, hws, hadd⟩ := h
    first
    | exact ⟨hu, hcol, hk, hws, hadd⟩
    | exact ⟨hu, hcol, hk, hws⟩
    | exact hws.of_le (by dsimp only [wsSize]; nlinarith)

/-- Contracts row `a.u` across all columns into `nextAdjBase`/`nextCostBase`. -/
@[expose] public def fillContractRowProg (a : ContractRowArgs) : Memory.Prog ℕ :=
  iterate contractRowStep a a.n 0

private theorem fillContractRowProg_realizes :
    Realizes .exact fillContractRowProg encContractRowArgs wordWords
      (fun w a s => iterationSafe contractRowStep ContractRowStepSafe w a a.n 0 s)
      (fun _ _ => 0) := by
  unfold fillContractRowProg
  realize [contractRowStep_realizes]
  exact h

/-- Parameters for contracting the active graph around cycle representative `x0` at frame `k`. -/
public structure ContractArgs where
  /-- Matrix dimension (number of vertices). -/
  n : ℕ
  /-- Designated root vertex index. -/
  r : ℕ
  /-- Representative vertex of the contracted cycle. -/
  x0 : ℕ
  /-- Workspace base address. -/
  ws : ℕ
  /-- Contraction stack frame index. -/
  k : ℕ

private word_enc_structure encContractArgs : ContractArgs where
  n : wordWords, r : wordWords, x0 : wordWords, ws : wordWords, k : wordWords

private instance : WordEncoding ContractArgs := ⟨5, encContractArgs⟩

/-- Contracts row `u` across all columns into `nextAdjBase`/`nextCostBase`. -/
@[expose] public def contractOuterStep (q : ContractArgs × ℕ) : Memory.Prog ℕ := do
  let env := Prod.fst q
  let u := Prod.snd q
  let _ ← Memory.read 0
  let _ ← fillContractRowProg ⟨env.n, env.r, env.x0, u, env.ws, env.k⟩
  pure (u + 1)

/-- Safety precondition for contracting row `u` in `contractOuterStep`. -/
public abbrev ContractOuterStepSafe (w : ℕ) (q : ContractArgs × ℕ) (s : Memory.State) : Prop :=
  let env := Prod.fst q
  let u := Prod.snd q
  Fits w (u + 1) ∧
    iterationSafe contractRowStep ContractRowStepSafe w
      ⟨env.n, env.r, env.x0, u, env.ws, env.k⟩ env.n 0 s

private theorem contractOuterStep_realizes :
    Realizes .exact contractOuterStep (appendWords encContractArgs wordWords) wordWords
      ContractOuterStepSafe (fun _ _ => 0) := by
  unfold contractOuterStep
  realize [fillContractRowProg_realizes]
  all_goals first | exact h.1 | exact h.2

/-- Builds contracted adjacency and reduced-cost tables in `nextAdjBase`/`nextCostBase`. -/
@[expose] public def contractLoopProg (a : ContractArgs) : Memory.Prog ℕ :=
  iterate contractOuterStep a a.n 0

private theorem contractLoopProg_realizes :
    Realizes .exact contractLoopProg encContractArgs wordWords
      (fun w a s => iterationSafe contractOuterStep ContractOuterStepSafe w a a.n 0 s)
      (fun _ _ => 0) := by
  unfold contractLoopProg
  realize [contractOuterStep_realizes]
  exact h

/-- Builds contracted tables and copies them back into `curAdjBase`/`curCostBase`. -/
@[expose] public def contractTablesProg (a : ContractArgs) : Memory.Prog ℕ := do
  let _ ← contractLoopProg a
  copyWordsProg ⟨nextAdjBase a.ws a.n, curAdjBase a.ws a.n, 2 * (a.n * a.n)⟩

private theorem contractTablesProg_realizes :
    Realizes .exact contractTablesProg encContractArgs wordWords
      (fun w a s =>
        let s1 := (Memory.spec 0).clientState s (contractLoopProg a)
        let cp : CopyArgs := ⟨nextAdjBase a.ws a.n, curAdjBase a.ws a.n, 2 * (a.n * a.n)⟩
        WsFits w a.ws a.n ∧
          iterationSafe contractOuterStep ContractOuterStepSafe w a a.n 0 s ∧
          iterationSafe copyStep CopyStepSafe w cp (2 * (a.n * a.n)) 0 s1)
      (fun _ _ => 0) := by
  unfold contractTablesProg
  realize [contractLoopProg_realizes, copyWordsProg_realizes]
  all_goals
    obtain ⟨hws, hloop, hcp⟩ := h
    first
    | exact hloop
    | exact hcp
    | exact hws.of_le (by
        dsimp only [wsSize, curAdjBase, nextAdjBase]
        nlinarith)

-- 9. `expandLevelProg`

/-- Parameters for expanding frame `k`'s cycle parent map using contracted parent `qx0` and exit
`bx`. -/
public structure ExpandRowArgs where
  /-- Matrix dimension (number of vertices). -/
  n : ℕ
  /-- Representative vertex of the contracted cycle at frame `k`. -/
  x0 : ℕ
  /-- Selected parent `curParent[x0]` of the contracted cycle node. -/
  qx0 : ℕ
  /-- Best cycle-exit vertex `frameBExit[qx0]`. -/
  bx : ℕ
  /-- Workspace base address. -/
  ws : ℕ
  /-- Contraction stack frame index being expanded. -/
  k : ℕ

private word_enc_structure encExpandRowArgs : ExpandRowArgs where
  n : wordWords, x0 : wordWords, qx0 : wordWords, bx : wordWords, ws : wordWords, k : wordWords

private instance : WordEncoding ExpandRowArgs := ⟨6, encExpandRowArgs⟩

/-- Computes the expanded parent for vertex `v` and writes it to `nextParentBase`. -/
@[expose] public def expandRowStep (q : ExpandRowArgs × ℕ) : Memory.Prog ℕ := do
  let env := Prod.fst q
  let v := Prod.snd q
  let inV ← Memory.read (frameMaskBase env.ws env.n env.k + v)
  let fv ← Memory.read (frameParentBase env.ws env.n env.k + v)
  let qv ← Memory.read (curParentBase env.ws env.n + v)
  let bev ← Memory.read (frameBEntryBase env.ws env.n env.k + v)
  let outV :=
    if inV = 1 then
      if env.bx < env.n then
        if v = env.bx then env.qx0 else fv
      else fv
    else if qv = env.x0 then
      if bev < env.n then bev else v
    else qv
  Memory.write (nextParentBase env.ws env.n + v) outV
  pure (v + 1)

/-- Address-fit safety precondition for expanding vertex `v` in `expandRowStep`. -/
public abbrev ExpandRowStepSafe (w : ℕ) (q : ExpandRowArgs × ℕ) (_ : Memory.State) : Prop :=
  let env := Prod.fst q
  let v := Prod.snd q
  v < env.n ∧ env.k < env.n ∧ WsFits w env.ws env.n

private theorem expandRowStep_realizes :
    Realizes .exact expandRowStep (appendWords encExpandRowArgs wordWords) wordWords
      ExpandRowStepSafe (fun _ _ => 0) := by
  unfold expandRowStep
  realize
  all_goals
    obtain ⟨hv, hk, hws⟩ := h
    exact hws.of_le (by
      dsimp only [wsSize, frameMaskBase, frameParentBase, frameBEntryBase, frameBase,
        curParentBase, nextParentBase]
      nlinarith)

/-- Expands all `a.n` parent entries at level `a.k` into `nextParentBase`. -/
@[expose] public def fillExpandRowProg (a : ExpandRowArgs) : Memory.Prog ℕ :=
  iterate expandRowStep a a.n 0

private theorem fillExpandRowProg_realizes :
    Realizes .exact fillExpandRowProg encExpandRowArgs wordWords
      (fun w a s => iterationSafe expandRowStep ExpandRowStepSafe w a a.n 0 s)
      (fun _ _ => 0) := by
  unfold fillExpandRowProg
  realize [expandRowStep_realizes]
  exact h

/-- Uncontracts stack frame `a.k`, updating `curParentBase` with the expanded parent array. -/
@[expose] public def expandLevelProg (a : LevelArgs) : Memory.Prog ℕ := do
  let x0 ← Memory.read (frameRepAddr a.ws a.n a.k)
  let qx0 ← Memory.read (curParentBase a.ws a.n + x0)
  let bx ← Memory.read (frameBExitBase a.ws a.n a.k + qx0)
  let _ ← fillExpandRowProg ⟨a.n, x0, qx0, bx, a.ws, a.k⟩
  copyWordsProg ⟨nextParentBase a.ws a.n, curParentBase a.ws a.n, a.n⟩

/-- Safety precondition for uncontracting stack frame `a.k` in `expandLevelProg`. -/
public abbrev ExpandLevelSafe (w : ℕ) (a : LevelArgs) (s : Memory.State) : Prop :=
  let x0 := s.mem (frameRepAddr a.ws a.n a.k)
  let qx0 := s.mem (curParentBase a.ws a.n + x0)
  let bx := s.mem (frameBExitBase a.ws a.n a.k + qx0)
  let rArgs : ExpandRowArgs := ⟨a.n, x0, qx0, bx, a.ws, a.k⟩
  let s1 := (Memory.spec 0).clientState s (fillExpandRowProg rArgs)
  let cArgs : CopyArgs := ⟨nextParentBase a.ws a.n, curParentBase a.ws a.n, a.n⟩
  a.k < a.n ∧ WsFits w a.ws a.n ∧ x0 < a.n ∧ qx0 < a.n ∧
    iterationSafe expandRowStep ExpandRowStepSafe w rArgs a.n 0 s ∧
    iterationSafe copyStep CopyStepSafe w cArgs a.n 0 s1

private theorem expandLevelProg_realizes :
    Realizes .exact expandLevelProg encLevelArgs wordWords
      ExpandLevelSafe (fun _ _ => 0) := by
  unfold expandLevelProg
  realize [fillExpandRowProg_realizes, copyWordsProg_realizes]
  all_goals
    obtain ⟨hk, hws, hx0, hqx0, hexp, hcopy⟩ := h
    first
    | exact hexp
    | exact hcopy
    | exact hws.of_le (by
        dsimp only [wsSize, frameRepAddr, frameBExitBase, frameBase, curParentBase,
          nextParentBase] at hx0 hqx0 ⊢
        nlinarith)

-- 10. `edmondsCoreProg`: forward contraction pass + backward expansion pass

/-- Top-level parameters for the in-workspace Chu–Liu/Edmonds solver core. -/
public structure CoreArgs where
  /-- Number of vertices. -/
  n : ℕ
  /-- Designated root vertex index. -/
  r : ℕ
  /-- Workspace base address. -/
  ws : ℕ

/-- Word encoding of `CoreArgs` into 3 consecutive registers. -/
public word_enc_structure encCoreArgs : CoreArgs where
  n : wordWords, r : wordWords, ws : wordWords

private instance : WordEncoding CoreArgs := ⟨3, encCoreArgs⟩

/-- Forward contraction loop state (`status`: `0` active, `1` acyclic feasible, `2` infeasible). -/
public structure ForwardState where
  /-- Current contraction depth `k`. -/
  k : ℕ
  /-- Solver status (`0` running, `1` feasible acyclic tree found, `2` infeasible). -/
  status : ℕ
  /-- Number of contracted frames pushed before terminating. -/
  depth : ℕ

private word_enc_structure encForwardState : ForwardState where
  k : wordWords, status : wordWords, depth : wordWords

private instance : WordEncoding ForwardState := ⟨3, encForwardState⟩

/-- Performs one full contraction round at frame `a.k` around cycle vertex `a.x0`. -/
@[expose] public def contractRoundBodyProg (a : ContractArgs) : Memory.Prog ℕ := do
  Memory.write (frameRepAddr a.ws a.n a.k) a.x0
  let _ ← cycleMaskProg
    ⟨a.n, frameParentBase a.ws a.n a.k, frameMaskBase a.ws a.n a.k, a.x0⟩
  let _ ← bestEntryProg ⟨a.n, a.ws, a.k⟩
  let _ ← bestExitProg ⟨a.n, a.ws, a.k⟩
  contractTablesProg a

/-- Safety precondition for one full contraction round `contractRoundBodyProg`. -/
public abbrev ContractRoundBodySafe (w : ℕ) (a : ContractArgs) (s : Memory.State) : Prop :=
  let s0 : Memory.State := ⟨Function.update s.mem (frameRepAddr a.ws a.n a.k) a.x0, s.frontier⟩
  let cmArgs : CycleMaskArgs :=
    ⟨a.n, frameParentBase a.ws a.n a.k, frameMaskBase a.ws a.n a.k, a.x0⟩
  let s0z := (Memory.spec 0).clientState s0 (zeroWordsProg ⟨cmArgs.maskBase, cmArgs.n⟩)
  let s1 := (Memory.spec 0).clientState s0 (cycleMaskProg cmArgs)
  let lvArgs : LevelArgs := ⟨a.n, a.ws, a.k⟩
  let s2 := (Memory.spec 0).clientState s1 (bestEntryProg lvArgs)
  let s3 := (Memory.spec 0).clientState s2 (bestExitProg lvArgs)
  let s4 := (Memory.spec 0).clientState s3 (contractLoopProg a)
  let cp : CopyArgs := ⟨nextAdjBase a.ws a.n, curAdjBase a.ws a.n, 2 * (a.n * a.n)⟩
  a.k < a.n ∧ WsFits w a.ws a.n ∧
    iterationSafe zeroStep ZeroStepSafe w ⟨cmArgs.maskBase, cmArgs.n⟩ cmArgs.n 0 s0 ∧
    iterationSafe cycleMaskStep CycleMaskStepSafe w cmArgs cmArgs.n ⟨0, cmArgs.x0⟩ s0z ∧
    iterationSafe bestEntryOuterStep BestEntryOuterStepSafe w lvArgs lvArgs.n 0 s1 ∧
    iterationSafe bestExitOuterStep BestExitOuterStepSafe w lvArgs lvArgs.n 0 s2 ∧
    iterationSafe contractOuterStep ContractOuterStepSafe w a a.n 0 s3 ∧
    iterationSafe copyStep CopyStepSafe w cp (2 * (a.n * a.n)) 0 s4

private theorem contractRoundBodyProg_realizes :
    Realizes .exact contractRoundBodyProg encContractArgs wordWords
      ContractRoundBodySafe (fun _ _ => 0) := by
  unfold contractRoundBodyProg
  realize [cycleMaskProg_realizes, bestEntryProg_realizes, bestExitProg_realizes,
    contractTablesProg_realizes]
  all_goals
    obtain ⟨hk, hws, hz, hcm, hbe, hbx, hct, hcp⟩ := h
    first
    | exact hz
    | exact hcm
    | exact hbe
    | exact hbx
    | exact hct
    | exact hcp
    | exact hws
    | exact hws.of_le (by
        dsimp only [wsSize, frameRepAddr, frameParentBase, frameMaskBase, frameBase]
        nlinarith)

/-- Executes one step of the forward contraction pass (noop once `st.status ≠ 0`). -/
@[expose] public def forwardStep (q : CoreArgs × ForwardState) : Memory.Prog ForwardState := do
  let env := Prod.fst q
  let st := Prod.snd q
  let _ ← Memory.read 0
  if st.status = 0 then
    let feas ← selectParentsProg ⟨env.n, env.r, env.ws, st.k⟩
    if feas = 0 then
      pure ⟨st.k + 1, 2, st.depth⟩
    else
      let x0 ← findCycleProg ⟨env.n, env.r, frameParentBase env.ws env.n st.k⟩
      if x0 = env.n then
        let _ ← copyWordsProg ⟨frameParentBase env.ws env.n st.k, curParentBase env.ws env.n, env.n⟩
        pure ⟨st.k + 1, 1, st.k⟩
      else
        let _ ← contractRoundBodyProg ⟨env.n, env.r, x0, env.ws, st.k⟩
        pure ⟨st.k + 1, 0, st.k + 1⟩
  else
    pure ⟨st.k + 1, st.status, st.depth⟩

/-- Safety precondition for one forward contraction iteration in `forwardStep`. -/
public abbrev ForwardStepSafe (w : ℕ) (q : CoreArgs × ForwardState) (s : Memory.State) : Prop :=
  let env := Prod.fst q
  let st := Prod.snd q
  let selArgs : SelectArgs := ⟨env.n, env.r, env.ws, st.k⟩
  let sSel := (Memory.spec 0).clientState s (selectParentsProg selArgs)
  let fcArgs : FindCycleArgs := ⟨env.n, env.r, frameParentBase env.ws env.n st.k⟩
  let x0 := (Memory.spec 0).clientResult sSel (findCycleProg fcArgs)
  let sFc := (Memory.spec 0).clientState sSel (findCycleProg fcArgs)
  let cpArgs : CopyArgs := ⟨frameParentBase env.ws env.n st.k, curParentBase env.ws env.n, env.n⟩
  st.k < env.n ∧ WsFits w env.ws env.n ∧
    (st.status = 0 →
      iterationSafe selectOuterStep SelectOuterStepSafe w selArgs env.n ⟨0, 1⟩ s ∧
      ((Memory.spec 0).clientResult s (selectParentsProg selArgs) ≠ 0 →
        iterationSafe findCycleOuterStep FindCycleOuterStepSafe w fcArgs env.n ⟨0, env.n⟩ sSel ∧
        (x0 = env.n → iterationSafe copyStep CopyStepSafe w cpArgs env.n 0 sFc) ∧
        (x0 ≠ env.n → ContractRoundBodySafe w ⟨env.n, env.r, x0, env.ws, st.k⟩ sFc)))

private theorem forwardStep_realizes :
    Realizes .exact forwardStep (appendWords encCoreArgs encForwardState) encForwardState
      ForwardStepSafe (fun _ _ => 0) := by
  unfold forwardStep
  realize [selectParentsProg_realizes, findCycleProg_realizes, copyWordsProg_realizes,
    contractRoundBodyProg_realizes]
  all_goals
    obtain ⟨hk, hws, hst0⟩ := h
    first
    | exact (hst0 ‹_›).1
    | exact ((hst0 ‹_›).2 ‹_›).1
    | exact ((hst0 ‹_›).2 ‹_›).2.1 ‹_›
    | exact ((hst0 ‹_›).2 ‹_›).2.2 ‹_›
    | exact hws.of_le (by
        dsimp only [wsSize, frameParentBase, frameBase, curParentBase]
        nlinarith)

/-- Runs up to `a.n` forward contraction rounds from an initialized workspace. -/
@[expose] public def forwardProg (a : CoreArgs) : Memory.Prog ForwardState :=
  iterate forwardStep a a.n ⟨0, 0, 0⟩

private theorem forwardProg_realizes :
    Realizes .exact forwardProg encCoreArgs encForwardState
      (fun w a s => iterationSafe forwardStep ForwardStepSafe w a a.n ⟨0, 0, 0⟩ s)
      (fun _ _ => 0) := by
  unfold forwardProg
  realize [forwardStep_realizes]
  exact h

/-- Parameters for the backward cycle-expansion pass over `depth` contracted frames. -/
public structure BackwardArgs where
  /-- Number of vertices. -/
  n : ℕ
  /-- Workspace base address. -/
  ws : ℕ
  /-- Total number of contracted stack frames to unwind. -/
  depth : ℕ

private word_enc_structure encBackwardArgs : BackwardArgs where
  n : wordWords, ws : wordWords, depth : wordWords

private instance : WordEncoding BackwardArgs := ⟨3, encBackwardArgs⟩

/-- Expands stack frame `env.depth - (j + 1)` at backward step `j`. -/
@[expose] public def backwardStep (q : BackwardArgs × ℕ) : Memory.Prog ℕ := do
  let env := Prod.fst q
  let j := Prod.snd q
  let _ ← Memory.read 0
  let k := env.depth - (j + 1)
  let _ ← expandLevelProg ⟨env.n, env.ws, k⟩
  pure (j + 1)

/-- Safety precondition for one backward expansion iteration in `backwardStep`. -/
public abbrev BackwardStepSafe (w : ℕ) (q : BackwardArgs × ℕ) (s : Memory.State) : Prop :=
  let env := Prod.fst q
  let j := Prod.snd q
  let k := env.depth - (j + 1)
  j + 1 ≤ env.depth ∧ Fits w (j + 1) ∧ ExpandLevelSafe w ⟨env.n, env.ws, k⟩ s

private theorem backwardStep_realizes :
    Realizes .exact backwardStep (appendWords encBackwardArgs wordWords) wordWords
      BackwardStepSafe (fun _ _ => 0) := by
  unfold backwardStep
  realize [expandLevelProg_realizes]
  all_goals first | exact h.1 | exact h.2.1 | exact h.2.2

/-- Expands all `a.depth` contracted frames back into `curParentBase`. -/
@[expose] public def backwardProg (a : BackwardArgs) : Memory.Prog ℕ :=
  iterate backwardStep a a.depth 0

private theorem backwardProg_realizes :
    Realizes .exact backwardProg encBackwardArgs wordWords
      (fun w a s => iterationSafe backwardStep BackwardStepSafe w a a.depth 0 s)
      (fun _ _ => 0) := by
  unfold backwardProg
  realize [backwardStep_realizes]
  exact h

/-- Full in-workspace Chu–Liu/Edmonds solver: forward contraction followed by backward cycle
expansion, returning `1` iff feasible. -/
@[expose] public def edmondsCoreProg (a : CoreArgs) : Memory.Prog ℕ := do
  let res ← forwardProg a
  if res.status = 1 then
    let _ ← backwardProg ⟨a.n, a.ws, res.depth⟩
    pure 1
  else
    pure 0

public theorem edmondsCoreProg_realizes :
    Realizes .exact edmondsCoreProg encCoreArgs wordWords
      (fun w a s =>
        let res := (Memory.spec 0).clientResult s (forwardProg a)
        let s1 := (Memory.spec 0).clientState s (forwardProg a)
        Fits w 1 ∧
          iterationSafe forwardStep ForwardStepSafe w a a.n ⟨0, 0, 0⟩ s ∧
          (res.status = 1 →
            iterationSafe backwardStep BackwardStepSafe w ⟨a.n, a.ws, res.depth⟩ res.depth 0 s1))
      (fun _ _ => 0) := by
  unfold edmondsCoreProg
  realize [forwardProg_realizes, backwardProg_realizes]
  all_goals
    obtain ⟨h1, hfwd, hbwd⟩ := h
    first | exact h1 | exact hfwd | exact hbwd ‹_›

end Cslib.Algorithms.WordRAM.Arborescence.Internal
