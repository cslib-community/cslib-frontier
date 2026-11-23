/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.MaxFlow.EdmondsKarp
public import CslibFrontier.Algorithms.Lean.MaxFlow.BipartiteMatching
public import CslibFrontier.Algorithms.Lean.MaxFlow.VertexSeparator
public import CslibFrontier.Algorithms.Lean.GomoryHu.WeightedCut
public import CslibFrontier.Algorithms.WordRAM.Karger.Contract
public import CslibFrontier.Computability.WordRAM.Realization.Absorb
public import CslibFrontier.Computability.WordRAM.Realization.ProgFrame
public import CslibFrontier.Computability.WordRAM.Realization.WordEncoding.Equiv
import CslibFrontier.Computability.WordRAM.Realization.Program.Standard
import CslibFrontier.Foundations.Data.List.RowMajor
import CslibFrontier.Tactic.Realize
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Dense Edmonds–Karp maximum flow, bipartite matching, and vertex separators on the Word-RAM

A relocatable memory-client subroutine `ekProg` implementing the shortest-augmenting-path maximum
flow algorithm of Edmonds and Karp ([EdmondsKarp1972]; [CLRS2009], Theorem 26.8), together with
uniform flat programs over `Cslib.WordRAM.Basis.exact` for dense maximum flow / minimum `s`–`t`
cut, maximum bipartite matching with König minimum vertex cover and perfect-matching decision, and
minimum vertex separators by vertex splitting. All programs use `Basis.exact` for unit-cost
multiplication in dense row-major matrix indexing, matching
`CslibFrontier.Algorithms.WordRAM.GomoryHu`.

Each round of `ekProg` runs a layered breadth-first search on the residual graph, storing residual
distances `Flow.resDist` at `distAddr` and parent pointers, then walks parent pointers from `t`
back to `s` twice to compute and push the bottleneck. Every round augments along a shortest
augmenting path, so `Network.shortestAugmentingSeq_length_le` bounds the number of rounds by
`n * n * (n / 2) < n ^ 3`. When `t` is no longer reached, the reached set is a minimum cut, and
the solver sums the capacities leaving it. Every arithmetic operation is guarded by `ekBound n B`,
so a round costs `O(n ^ 2)` memory operations and the whole computation `O(n ^ 5)`.

## Main definitions

* `Cslib.Algorithms.WordRAM.EdmondsKarp.Ctx`, `Ctx.equiv`, `distAddr`, `ekScratch`, `ekBound`,
  `CtxFits`, `ekProg`, `ekCost`: the relocatable solver context, output distance address, scratch
  size, word bound, subroutine, and memory budget.
* `Cslib.Algorithms.WordRAM.EdmondsKarp.fillRange`: fill a range of memory with one word.
* `Cslib.Algorithms.WordRAM.EdmondsKarp.encodeFlowInput`, `ekFlowAddr`, `ekCutAddr`,
  `ekWorkspace`: input encoding, output flow and cut addresses, and workspace frontier for dense
  maximum flow.
* `Cslib.Algorithms.WordRAM.EdmondsKarp.encodeBipartiteMatrix`, `encodeBipartiteInput`,
  `bmMatchAddr`, `bmCovLAddr`, `bmCovRAddr`: input encoding and output matching and König cover
  addresses for bipartite matching.
* `Cslib.Algorithms.WordRAM.EdmondsKarp.encodeBoolVec`, `encodeSepInput`, `sepOutAddr`,
  `sepSideAddr`: input encoding and output separator and side-labelling addresses for minimum
  vertex separators.

## Main results

* `Cslib.Algorithms.WordRAM.EdmondsKarp.ekProg_spec`, `memoryCost_ekProg_le`, `ekProg_realizes`,
  `validHistory_ekProg`, `preservesAt_ekProg`, `ekProg_result_le`: correctness, `O(n ^ 5)` memory
  cost, compilation to `Basis.exact`, admissibility, frame, and return-value bound for clients
  calling `ekProg` as a subroutine (such as Gomory–Hu construction).
* `Cslib.Algorithms.WordRAM.EdmondsKarp.exists_edmondsKarp_program`: uniform `O((n + 1) ^ 5)`
  flat program over `Basis.exact` computing a maximum flow and minimum `s`–`t` cut.
* `Cslib.Algorithms.WordRAM.EdmondsKarp.exists_bipartiteMatching_program`,
  `Cslib.Algorithms.WordRAM.EdmondsKarp.exists_perfectMatching_program`: uniform
  `O((m + r + 1) ^ 5)` maximum bipartite matching with König minimum vertex cover, and uniform
  `O((n + 1) ^ 5)` bipartite perfect-matching decision.
* `Cslib.Algorithms.WordRAM.EdmondsKarp.exists_minSeparator_program`: uniform `O((n + 1) ^ 5)`
  minimum vertex separator and side-labelling certificate by vertex splitting.
* `Cslib.Algorithms.WordRAM.EdmondsKarp.fillRange_realizes`, `fillRange_spec`,
  `memoryCost_fillRange_le`, `validHistory_fillRange`: realization and specification of
  `fillRange`.

## References

* [EdmondsKarp1972]
* [CLRS2009]
* [Koenig1931]
* [Menger1927]
-/

public section

namespace Cslib.Algorithms.WordRAM.EdmondsKarp

open Cslib.Algorithms.Lean.MaxFlow Cslib.Algorithms.Lean.GomoryHu Cslib.WeightedCut
open Cslib.Algorithms.WordRAM.Karger Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization
open StateTransitionSpec (clientResult_bind clientState_bind clientResult_pure clientState_pure)

/-! ### Layout -/

/-- Solver context: `n` vertices, capacity matrix at `matBase`, scratch area at `scratchBase`,
and a bound `capBound` on the capacities. -/
structure Ctx where
  /-- Number of vertices. -/
  n : ℕ
  /-- Base address of the row-major capacity matrix. -/
  matBase : ℕ
  /-- Base address of the solver's scratch area. -/
  scratchBase : ℕ
  /-- Upper bound on edge capacities. -/
  capBound : ℕ

/-- Equivalence between `Ctx` and its four `ℕ` fields for word encoding. -/
@[expose] def Ctx.equiv : Ctx ≃ ℕ × ℕ × ℕ × ℕ where
  toFun c := (c.n, c.matBase, c.scratchBase, c.capBound)
  invFun := fun (n, matBase, scratchBase, capBound) => ⟨n, matBase, scratchBase, capBound⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding Ctx := .ofEquiv Ctx.equiv

/-- Address of the capacity `W u v`. -/
private abbrev capAddr (c : Ctx) (u v : ℕ) : ℕ := c.matBase + u * c.n + v

/-- Address of the flow on the arc `(u, v)`. -/
private abbrev flowAddr (c : Ctx) (u v : ℕ) : ℕ := c.scratchBase + u * c.n + v

/-- Address of the breadth-first-search distance of `x` (`n` when `x` is not reached). -/
abbrev distAddr (c : Ctx) (x : ℕ) : ℕ := c.scratchBase + c.n * c.n + x

/-- Address of the breadth-first-search parent of `x`. -/
private abbrev predAddr (c : Ctx) (x : ℕ) : ℕ := c.scratchBase + c.n * c.n + c.n + x

/-- Words of scratch memory used by the solver: the flow matrix, distances and parents. -/
abbrev ekScratch (n : ℕ) : ℕ := n * n + 2 * n

/-- Every word the solver computes or stores is at most `ekBound n B`: round counts below `n ^ 3`,
cut sums up to `n * n * B`, residual capacities up to `2 * B`, flow updates up to `3 * B`. -/
abbrev ekBound (n B : ℕ) : ℕ := n * n * n + n * n * B + 3 * B + 1

/-- Layout and word-size requirements on a context: the matrix lies below the scratch area and
both the scratch area and `ekBound` fit a word. -/
abbrev CtxFits (w : ℕ) (c : Ctx) : Prop :=
  c.matBase + c.n * c.n ≤ c.scratchBase ∧ Fits w (c.scratchBase + ekScratch c.n) ∧
    Fits w (ekBound c.n c.capBound)

attribute [local client_simps] runClient_read runClient_write

/-! ### Programs -/

/-- One step of `fillRange`: write `val` at `base + idx`. -/
private def fillStep (d : (ℕ × ℕ) × ℕ) : Memory.Prog ℕ := do
  Memory.write (d.1.1 + d.2) d.1.2
  pure (d.2 + 1)

/-- Write `val` at the `len` addresses from `base` (`d = ((base, val), len)`). -/
def fillRange (d : (ℕ × ℕ) × ℕ) : Memory.Prog Unit := do
  let _ ← iterate fillStep d.1 d.2 0
  pure ()

/-- Residual capacity `W u v - f u v + f v u` of the arc `(u, v)` (`d = ((c, u), v)`), guarded to
be at most `2 * B`. -/
private def readResCap (d : (Ctx × ℕ) × ℕ) : Memory.Prog ℕ := do
  let c := d.1.1
  let u := d.1.2
  let v := d.2
  let cap ← Memory.read (capAddr c u v)
  let fuv ← Memory.read (flowAddr c u v)
  let fvu ← Memory.read (flowAddr c v u)
  if cap ≤ c.capBound ∧ fuv ≤ cap ∧ fvu ≤ c.capBound then pure (cap - fuv + fvu) else pure 0

/-- Innermost step of the search (`d = (((c, layer), u), v)`): reach `v` from `u` at distance
`layer + 1` when `v` is unreached and `(u, v)` has residual capacity. -/
private def bfsInnerStep (d : ((Ctx × ℕ) × ℕ) × ℕ) : Memory.Prog ℕ := do
  let c := d.1.1.1
  let layer := d.1.1.2
  let u := d.1.2
  let v := d.2
  let dv ← Memory.read (distAddr c v)
  let rc ← readResCap ((c, u), v)
  if dv = c.n ∧ 0 < rc then
    Memory.write (distAddr c v) (layer + 1)
    Memory.write (predAddr c v) u
    pure (v + 1)
  else
    pure (v + 1)

/-- Middle step of the search (`d = ((c, layer), u)`): expand `u` if it lies in layer `layer`. -/
private def bfsMidStep (d : (Ctx × ℕ) × ℕ) : Memory.Prog ℕ := do
  let c := d.1.1
  let layer := d.1.2
  let u := d.2
  let du ← Memory.read (distAddr c u)
  if du = layer then
    let _ ← iterate bfsInnerStep ((c, layer), u) c.n 0
    pure (u + 1)
  else
    pure (u + 1)

/-- One layer of the search (`d = (c, layer)`). -/
private def bfsLayerStep (d : Ctx × ℕ) : Memory.Prog ℕ := do
  let _ ← Memory.read 0
  let _ ← iterate bfsMidStep d d.1.n 0
  pure (d.2 + 1)

/-- Layered breadth-first search from `s` (`d = (c, s)`) on the residual graph of the stored
flow. -/
private def bfsProg (d : Ctx × ℕ) : Memory.Prog Unit := do
  let c := d.1
  let s := d.2
  fillRange ((distAddr c 0, c.n), c.n)
  Memory.write (distAddr c s) 0
  Memory.write (predAddr c s) s
  let _ ← iterate bfsLayerStep c (c.n - 1) 0
  pure ()

/-- One step of the bottleneck walk (`d = (c, (cur, δ))`): move to the parent `p` of `cur` and
take the minimum of `δ` and the residual capacity of `(p, cur)`. -/
private def bnStep (d : Ctx × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let c := d.1
  let cur := d.2.1
  let δ := d.2.2
  let _ ← Memory.read 0
  if cur < c.n then
    let p ← Memory.read (predAddr c cur)
    if p < c.n then
      let rc ← readResCap ((c, p), cur)
      if rc ≤ δ then pure (p, rc) else pure (p, δ)
    else pure (0, δ)
  else pure (0, δ)

/-- One step of the augmentation walk (`d = ((c, δ), cur)`): push `δ` units along the arc
`(p, cur)` from the parent `p` of `cur`, cancelling flow on `(cur, p)` first. -/
private def augStep (d : (Ctx × ℕ) × ℕ) : Memory.Prog ℕ := do
  let c := d.1.1
  let δ := d.1.2
  let cur := d.2
  let _ ← Memory.read 0
  if cur < c.n then
    let p ← Memory.read (predAddr c cur)
    if p < c.n then
      let fcp ← Memory.read (flowAddr c cur p)
      let fpc ← Memory.read (flowAddr c p cur)
      if fpc ≤ c.capBound ∧ δ ≤ 2 * c.capBound then
        let r := if δ ≤ fcp then δ else fcp
        Memory.write (flowAddr c cur p) (fcp - r)
        Memory.write (flowAddr c p cur) (fpc + (δ - r))
        pure p
      else pure p
    else pure 0
  else pure 0

/-- One round (`d = ((c, (s, t)), st)`, `st = 0` while running): search, and if `t` is reached,
compute the bottleneck of the found path and push it. Returns `1` once `t` is not reached. -/
private def roundStep (d : (Ctx × (ℕ × ℕ)) × ℕ) : Memory.Prog ℕ := do
  let c := d.1.1
  let s := d.1.2.1
  let t := d.1.2.2
  let _ ← Memory.read 0
  if d.2 = 0 then
    bfsProg (c, s)
    let dt ← Memory.read (distAddr c t)
    if 0 < dt ∧ dt < c.n then
      let r ← iterate bnStep c dt (t, 2 * c.capBound)
      let _ ← iterate augStep (c, r.2) dt t
      pure 0
    else pure 1
  else pure 1

/-- Inner step of the cut sum (`d = ((c, u), (v, acc))`): add `W u v` when `v` is unreached. -/
private def cutInnerStep (d : (Ctx × ℕ) × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let c := d.1.1
  let u := d.1.2
  let v := d.2.1
  let acc := d.2.2
  let dv ← Memory.read (distAddr c v)
  let x ← Memory.read (capAddr c u v)
  if dv = c.n ∧ x ≤ c.capBound ∧ acc ≤ c.n * c.n * c.capBound then
    pure (v + 1, acc + x)
  else
    pure (v + 1, acc)

/-- Outer step of the cut sum (`d = (c, (u, acc))`): add the capacities from `u` to the unreached
vertices when `u` is reached. -/
private def cutOuterStep (d : Ctx × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let c := d.1
  let u := d.2.1
  let acc := d.2.2
  let du ← Memory.read (distAddr c u)
  if du < c.n then
    let r ← iterate cutInnerStep (c, u) c.n (0, acc)
    pure (u + 1, r.2)
  else
    pure (u + 1, acc)

/-- **Dense Edmonds–Karp** (`d = (c, (s, t))`): clear the flow, run `n ^ 3` rounds (rounds after
`t` stops being reached do nothing), and return the weight of the reached set of the final
search. -/
def ekProg (d : Ctx × (ℕ × ℕ)) : Memory.Prog ℕ := do
  let c := d.1
  fillRange ((flowAddr c 0 0, 0), c.n * c.n)
  let _ ← iterate roundStep d (c.n * c.n * c.n) 0
  let r ← iterate cutOuterStep c c.n (0, 0)
  pure r.2

private theorem clientResult_bfsInnerStep (d : ((Ctx × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (bfsInnerStep d) = d.2 + 1 := by
  unfold bfsInnerStep
  rw [clientResult_bind_read, clientResult_bind]
  split_ifs
  · rw [clientResult_bind_write, clientResult_bind_write, clientResult_pure]
  · rfl

private theorem clientResult_bfsMidStep (d : (Ctx × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (bfsMidStep d) = d.2 + 1 := by
  unfold bfsMidStep
  rw [clientResult_bind_read]
  split_ifs
  · rw [clientResult_bind, clientResult_pure]
  · rfl

private theorem clientResult_cutInnerStep_fst (d : (Ctx × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    ((Memory.spec 0).clientResult s (cutInnerStep d)).1 = d.2.1 + 1 := by
  unfold cutInnerStep
  rw [clientResult_bind_read, clientResult_bind_read]
  split_ifs <;> rfl

private theorem clientResult_cutOuterStep_fst (d : Ctx × (ℕ × ℕ)) (s : Memory.State) :
    ((Memory.spec 0).clientResult s (cutOuterStep d)).1 = d.2.1 + 1 := by
  unfold cutOuterStep
  rw [clientResult_bind_read]
  split_ifs
  · rw [clientResult_bind, clientResult_pure]
  · rfl

/-! ### Compilation (`Realizes`) -/

/-- `omega` after unfolding the layout abbreviations and reducing projections. -/
local macro "ek_omega" : tactic => `(tactic| (
  dsimp -failIfUnchanged only [CtxFits, ekScratch, ekBound, capAddr, flowAddr, distAddr,
    predAddr] at *
  omega))

/-- Close the arithmetic side goals of `realize` for the solver's programs. -/
local macro "ek_side" : tactic => `(tactic| (
  dsimp -failIfUnchanged only [CtxFits, ekScratch, ekBound, capAddr, flowAddr, distAddr,
    predAddr] at *
  first
  | assumption
  | (constructor <;> first | assumption | (constructor <;> assumption))
  | omega
  | (apply Fits.of_le ‹Fits _ (_ + (_ * _ + 2 * _))›; first | omega | nlinarith)
  | (apply Fits.of_le ‹Fits _ (_ * _ * _ + _ * _ * _ + 3 * _ + 1)›; first | omega | nlinarith)))

private theorem idx_lt_sq {u v n : ℕ} (hu : u < n) (hv : v < n) : u * n + v < n * n := by
  have : (u + 1) * n ≤ n * n := Nat.mul_le_mul_right n hu
  rw [Nat.succ_mul] at this
  omega

private theorem fillStep_realizes :
    Realizes .exact fillStep (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (d.1.1 + d.2) ∧ Fits w (d.2 + 1)) (fun _ _ => 0) := by
  unfold fillStep
  realize
  · exact h.1
  · exact h.2

theorem fillRange_realizes :
    Realizes .exact fillRange (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w d _ => let ((base, _), len) := d; Fits w (base + len)) (fun _ _ => 0) := by
  unfold fillRange
  realize [fillStep_realizes]
  refine iterationSafe_of_stepInv _ _ w d
    (fun rem (idx : ℕ) _ => idx + rem = d.2 ∧ Fits w (d.1.1 + d.2)) ?_ ⟨Nat.zero_add _, h⟩
  intro rem idx t ⟨hsum, hfit⟩
  dsimp only [fillStep]
  simp only [client_simps]
  exact ⟨⟨by apply hfit.of_le; omega, by apply hfit.of_le; omega⟩, by omega, hfit⟩

private theorem readResCap_realizes :
    Realizes .exact readResCap (WordEncoding.encode (α := (Ctx × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => CtxFits w d.1.1 ∧ d.1.2 < d.1.1.n ∧ d.2 < d.1.1.n) (fun _ _ => 0) := by
  unfold readResCap
  realize
  all_goals
    obtain ⟨⟨hlay, hws, hwb⟩, hu, hv⟩ := h
    have h1 := idx_lt_sq hu hv
    have h2 := idx_lt_sq hv hu
    ek_side

private theorem bfsInnerStep_realizes :
    Realizes .exact bfsInnerStep (WordEncoding.encode (α := ((Ctx × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => CtxFits w d.1.1.1 ∧ d.1.1.2 < d.1.1.1.n ∧ d.1.2 < d.1.1.1.n ∧
        d.2 < d.1.1.1.n) (fun _ _ => 0) := by
  unfold bfsInnerStep
  realize [readResCap_realizes]
  all_goals
    obtain ⟨⟨hlay, hws, hwb⟩, hl, hu, hv⟩ := h
    ek_side

private theorem bfsMidStep_realizes :
    Realizes .exact bfsMidStep (WordEncoding.encode (α := (Ctx × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => CtxFits w d.1.1 ∧ d.1.2 < d.1.1.n ∧ d.2 < d.1.1.n) (fun _ _ => 0) := by
  unfold bfsMidStep
  realize [bfsInnerStep_realizes]
  all_goals
    obtain ⟨⟨hlay, hws, hwb⟩, hl, hu⟩ := h
    try ek_side
  refine iterationSafe_of_stepInv _ _ w _
    (fun rem (v : ℕ) _ => v + rem = d.1.1.n) ?_ (Nat.zero_add _)
  intro rem v t hsum
  dsimp only at *
  refine ⟨⟨⟨hlay, hws, hwb⟩, hl, hu, by omega⟩, ?_⟩
  rw [clientResult_bfsInnerStep]; omega

private theorem bfsLayerStep_realizes :
    Realizes .exact bfsLayerStep (WordEncoding.encode (α := Ctx × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => CtxFits w d.1 ∧ d.2 < d.1.n) (fun _ _ => 0) := by
  unfold bfsLayerStep
  realize [bfsMidStep_realizes]
  all_goals
    obtain ⟨⟨hlay, hws, hwb⟩, hl⟩ := h
    try ek_side
  refine iterationSafe_of_stepInv _ _ w _
    (fun rem (u : ℕ) _ => u + rem = d.1.n) ?_ (Nat.zero_add _)
  intro rem u t hsum
  dsimp only at *
  refine ⟨⟨⟨hlay, hws, hwb⟩, hl, by omega⟩, ?_⟩
  rw [clientResult_bfsMidStep]; omega

private theorem bfsProg_realizes :
    Realizes .exact bfsProg (WordEncoding.encode (α := Ctx × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w d _ => CtxFits w d.1 ∧ d.2 < d.1.n) (fun _ _ => 0) := by
  unfold bfsProg
  realize [fillRange_realizes, bfsLayerStep_realizes]
  all_goals
    obtain ⟨⟨hlay, hws, hwb⟩, hs⟩ := h
    try ek_side
  refine iterationSafe_of_stepInv _ _ w _
    (fun rem (layer : ℕ) _ => layer + rem = d.1.n - 1) ?_ (Nat.zero_add _)
  intro rem layer t hsum
  dsimp only at *
  refine ⟨⟨⟨hlay, hws, hwb⟩, by omega⟩, ?_⟩
  dsimp only [bfsLayerStep]
  simp only [client_simps]
  omega

private theorem bnStep_realizes :
    Realizes .exact bnStep (WordEncoding.encode (α := Ctx × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w d _ => CtxFits w d.1) (fun _ _ => 0) := by
  unfold bnStep
  realize [readResCap_realizes]
  all_goals
    obtain ⟨hlay, hws, hwb⟩ := h
    ek_side

private theorem augStep_realizes :
    Realizes .exact augStep (WordEncoding.encode (α := (Ctx × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => CtxFits w d.1.1) (fun _ _ => 0) := by
  unfold augStep
  realize
  all_goals
    obtain ⟨hlay, hws, hwb⟩ := h
    ek_side

private theorem roundStep_realizes :
    Realizes .exact roundStep (WordEncoding.encode (α := (Ctx × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => CtxFits w d.1.1 ∧ d.1.2.1 < d.1.1.n ∧ d.1.2.2 < d.1.1.n) (fun _ _ => 0) := by
  unfold roundStep
  realize [bfsProg_realizes, bnStep_realizes, augStep_realizes]
  all_goals
    obtain ⟨⟨hlay, hws, hwb⟩, hs, ht⟩ := h
    try ek_side
  all_goals
    refine iterationSafe_of_stepInv _ _ w _ (fun _ _ _ => True) ?_ trivial
    intro _ _ _ _
    exact ⟨⟨hlay, hws, hwb⟩, trivial⟩

private theorem cutInnerStep_realizes :
    Realizes .exact cutInnerStep (WordEncoding.encode (α := (Ctx × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w d _ => CtxFits w d.1.1 ∧ d.1.2 < d.1.1.n ∧ d.2.1 < d.1.1.n) (fun _ _ => 0) := by
  unfold cutInnerStep
  realize
  all_goals
    obtain ⟨⟨hlay, hws, hwb⟩, hu, hv⟩ := h
    have h1 := idx_lt_sq hu hv
    ek_side

private theorem cutOuterStep_realizes :
    Realizes .exact cutOuterStep (WordEncoding.encode (α := Ctx × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w d _ => CtxFits w d.1 ∧ d.2.1 < d.1.n) (fun _ _ => 0) := by
  unfold cutOuterStep
  realize [cutInnerStep_realizes]
  all_goals
    obtain ⟨⟨hlay, hws, hwb⟩, hu⟩ := h
    try ek_side
  refine iterationSafe_of_stepInv _ _ w _
    (fun rem (va : ℕ × ℕ) _ => va.1 + rem = d.1.n) ?_ (Nat.zero_add _)
  intro rem va t hsum
  dsimp only at *
  refine ⟨⟨⟨hlay, hws, hwb⟩, hu, by omega⟩, ?_⟩
  rw [clientResult_cutInnerStep_fst]; dsimp only; omega

theorem ekProg_realizes :
    Realizes .exact ekProg (WordEncoding.encode (α := Ctx × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => let (c, s, t) := d; CtxFits w c ∧ s < c.n ∧ t < c.n) (fun _ _ => 0) := by
  unfold ekProg
  realize [fillRange_realizes, roundStep_realizes, cutOuterStep_realizes]
  all_goals
    obtain ⟨⟨hlay, hws, hwb⟩, hs, ht⟩ := h
    try ek_side
  · refine iterationSafe_of_stepInv _ _ w _ (fun _ _ _ => True) ?_ trivial
    intro _ _ _ _
    exact ⟨⟨⟨hlay, hws, hwb⟩, hs, ht⟩, trivial⟩
  · refine iterationSafe_of_stepInv _ _ w _
      (fun rem (ua : ℕ × ℕ) _ => ua.1 + rem = d.1.n) ?_ (Nat.zero_add _)
    intro rem ua t hsum
    dsimp only at *
    refine ⟨⟨⟨hlay, hws, hwb⟩, by omega⟩, ?_⟩
    rw [clientResult_cutOuterStep_fst]; dsimp only; omega

/-! ### Frames and read-only steps -/

private theorem preservesAt_fillRange {a base val len : ℕ}
    (hout : a < base ∨ base + len ≤ a) : PreservesAt a (fillRange ((base, val), len)) := fun s => by
  unfold fillRange
  rw [clientState_bind]
  change ((Memory.spec 0).clientState s (iterate fillStep (base, val) len 0)).mem a = s.mem a
  refine iterate_invariant_of fillStep (base, val)
    (fun rem (idx : ℕ) t => idx + rem = len ∧ t.mem a = s.mem a)
    (fun rem idx t ⟨hsum, hmem⟩ => ?_) ⟨Nat.zero_add _, rfl⟩ |>.2
  unfold fillStep
  simp only [client_simps]
  exact ⟨by omega, (Function.update_of_ne (by omega) _ t.mem).trans hmem⟩

/-- `fillRange ((base, val), len)` writes `val` on `[base, base + len)` and nothing else. -/
theorem fillRange_spec (base val len : ℕ) (s : Memory.State) :
    let s' := (Memory.spec 0).clientState s (fillRange ((base, val), len))
    (∀ i < len, s'.mem (base + i) = val) ∧
      (∀ a, (a < base ∨ base + len ≤ a) → s'.mem a = s.mem a) := by
  intro s'
  refine ⟨?_, fun a ha => preservesAt_fillRange ha s⟩
  unfold s' fillRange
  rw [clientState_bind]
  change ∀ i < len, ((Memory.spec 0).clientState s (iterate fillStep (base, val) len 0)).mem
    (base + i) = val
  have hinv := iterate_invariant_of fillStep (base, val)
    (fun rem (idx : ℕ) t => idx + rem = len ∧ ∀ i < idx, t.mem (base + i) = val)
    (fun rem idx t ⟨hsum, hprev⟩ => by
      unfold fillStep
      simp only [StateTransitionSpec.clientState, StateTransitionSpec.clientResult, client_simps]
      refine ⟨by omega, fun i hi => ?_⟩
      by_cases h : i = idx
      · subst h; simp
      · rw [Function.update_of_ne (by omega)]; exact hprev i (by omega))
    (n := len) (a := 0) (s := s) ⟨Nat.zero_add _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  intro i hi
  exact hinv.2 i (by omega)

private theorem memoryCost_map_write_le {α : Type} (f : Unit → α) (a v : ℕ) (s : Memory.State) :
    memoryCost (f <$> Memory.write a v) s ≤ 1 :=
  le_refl 1

theorem memoryCost_fillRange_le (base val len : ℕ) (s : Memory.State) :
    memoryCost (fillRange ((base, val), len)) s ≤ len := by
  unfold fillRange
  have hit := memoryCost_iterate_le_of fillStep 1 (base, val)
    (fun idx t => by unfold fillStep; exact memoryCost_map_write_le _ _ _ t) len 0 s
  exact le_trans (memoryCost_bind_le hit fun _ t => (memoryCost_pure () t).le) (by omega)

theorem validHistory_fillRange {w base val len : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hend : base + len ≤ s.frontier) (hval : Fits w val) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fillRange ((base, val), len))) := by
  unfold fillRange
  refine validHistory_bind_step
    (validHistory_iterate_nat (Inv := fun t => Memory.WellFormed w t ∧ base + len ≤ t.frontier)
      len 0 (fun idx hidx t ht => ⟨?_, ?_⟩) ⟨hwf, hend⟩)
    (validHistory_pure _ _ _)
  · unfold fillStep
    exact validHistory_write_bind (by have := ht.2; ek_omega) hval (validHistory_pure _ _ _)
  · unfold fillStep; simp only [client_simps]

private theorem readResCap_state (d : (Ctx × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (readResCap d) = s := by
  unfold readResCap
  rw [clientState_bind_read, clientState_bind_read, clientState_bind_read]
  split_ifs <;> rfl

private theorem bnStep_state (d : Ctx × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (bnStep d) = s := by
  unfold bnStep
  rw [clientState_bind_read]
  split_ifs
  · rw [clientState_bind_read]
    split_ifs
    · rw [clientState_bind, readResCap_state]
      split_ifs <;> rfl
    · rfl
  · rfl

private theorem cutInnerStep_state (d : (Ctx × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (cutInnerStep d) = s := by
  unfold cutInnerStep
  rw [clientState_bind_read, clientState_bind_read]
  split_ifs <;> rfl

private theorem cutOuterStep_state (d : Ctx × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (cutOuterStep d) = s := by
  unfold cutOuterStep
  rw [clientState_bind_read]
  split_ifs
  · rw [clientState_bind,
      clientState_iterate_eq_of _ _ (fun a t => cutInnerStep_state _ t)]
    rfl
  · rfl

private theorem preservesAt_bfsProg {a : ℕ} {d : Ctx × ℕ} (hs : d.2 < d.1.n)
    (ha : a < distAddr d.1 0 ∨ predAddr d.1 d.1.n ≤ a) : PreservesAt a (bfsProg d) := by
  obtain ⟨c, src⟩ := d
  dsimp only at hs ha
  unfold bfsProg
  refine preservesAt_bind (preservesAt_fillRange (by ek_omega)) fun _ => ?_
  refine preservesAt_bind (preservesAt_write _ (by ek_omega)) fun _ => ?_
  refine preservesAt_bind (preservesAt_write _ (by ek_omega)) fun _ => ?_
  refine preservesAt_bind (preservesAt_iterate (fun layer => ?_) _ _)
    fun _ => preservesAt_pure _ _
  unfold bfsLayerStep
  refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
  refine preservesAt_bind (preservesAt_iterate_nat fun u hu => ⟨?_, fun t => ?_⟩)
    fun _ => preservesAt_pure _ _
  · unfold bfsMidStep
    refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
    refine preservesAt_ite _ ?_ (preservesAt_pure _ _)
    refine preservesAt_bind (preservesAt_iterate_nat fun v hv => ⟨?_, fun t => ?_⟩)
      fun _ => preservesAt_pure _ _
    · unfold bfsInnerStep
      refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
      refine preservesAt_bind
        (fun t => congrArg (fun st : Memory.State => st.mem a) (readResCap_state _ t))
        fun _ => ?_
      refine preservesAt_ite _ ?_ (preservesAt_pure _ _)
      refine preservesAt_bind (preservesAt_write _ (by ek_omega)) fun _ => ?_
      exact preservesAt_map _ (preservesAt_write _ (by ek_omega))
    · exact clientResult_bfsInnerStep _ _
  · exact clientResult_bfsMidStep _ _

/-! ### The search only lowers unreached distances to `layer + 1` -/

/-- Between `t` and `t'`, every distance below `n` either is unchanged or went from `n` (unreached)
to `layer + 1`. -/
private def DistRel (c : Ctx) (layer : ℕ) (t t' : Memory.State) : Prop :=
  ∀ x < c.n, t'.mem (distAddr c x) = t.mem (distAddr c x) ∨
    (t.mem (distAddr c x) = c.n ∧ t'.mem (distAddr c x) = layer + 1)

private theorem DistRel.refl (c : Ctx) (layer : ℕ) (t : Memory.State) : DistRel c layer t t :=
  fun _ _ => Or.inl rfl

private theorem DistRel.trans {c : Ctx} {layer : ℕ}
    {t₁ t₂ t₃ : Memory.State} (h₁ : DistRel c layer t₁ t₂) (h₂ : DistRel c layer t₂ t₃) :
    DistRel c layer t₁ t₃ := fun x hx => by
  rcases h₁ x hx with h | ⟨ha, hb⟩ <;> rcases h₂ x hx with h' | ⟨ha', hb'⟩
  · exact Or.inl (h'.trans h)
  · exact Or.inr ⟨h ▸ ha', hb'⟩
  · exact Or.inr ⟨ha, h'.trans hb⟩
  · omega

private theorem bfsInnerStep_rel (d : ((Ctx × ℕ) × ℕ) × ℕ) (t : Memory.State) :
    DistRel d.1.1.1 d.1.1.2 t ((Memory.spec 0).clientState t (bfsInnerStep d)) := by
  intro x hx
  unfold bfsInnerStep
  dsimp only
  rw [clientState_bind_read, clientState_bind, readResCap_state]
  split_ifs with hc
  · rw [clientState_bind_write, clientState_bind_write, clientState_pure]
    dsimp only
    rw [Function.update_of_ne (by ek_omega)]
    by_cases hxv : x = d.2
    · subst hxv
      exact Or.inr ⟨hc.1, Function.update_self _ _ _⟩
    · exact Or.inl (Function.update_of_ne (by ek_omega) _ _)
  · exact Or.inl rfl


private theorem bfsInner_iterate_rel (c : Ctx) (layer u : ℕ)
    (m v₀ : ℕ) (t : Memory.State) :
    DistRel c layer t
      ((Memory.spec 0).clientState t (iterate bfsInnerStep ((c, layer), u) m v₀)) :=
  iterate_invariant_of bfsInnerStep ((c, layer), u) (fun _ _ t' => DistRel c layer t t')
    (fun _ v t' h => h.trans (bfsInnerStep_rel (((c, layer), u), v) t'))
    (DistRel.refl c layer t)

private theorem bfsMidStep_rel (c : Ctx) (layer u : ℕ)
    (t : Memory.State) :
    DistRel c layer t ((Memory.spec 0).clientState t (bfsMidStep ((c, layer), u))) := by
  unfold bfsMidStep
  dsimp only
  rw [clientState_bind_read]
  split_ifs
  · rw [clientState_bind, clientState_pure]
    exact bfsInner_iterate_rel c layer u _ _ t
  · exact DistRel.refl c layer t

private theorem bfsMid_iterate_rel (c : Ctx) (layer : ℕ)
    (m u₀ : ℕ) (t : Memory.State) :
    DistRel c layer t
      ((Memory.spec 0).clientState t (iterate bfsMidStep (c, layer) m u₀)) :=
  iterate_invariant_of bfsMidStep (c, layer) (fun _ _ t' => DistRel c layer t t')
    (fun _ u t' h => h.trans (bfsMidStep_rel c layer u t'))
    (DistRel.refl c layer t)

/-! ### Memory-operation counts -/

private theorem memoryCost_readResCap_le (d : (Ctx × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (readResCap d) s ≤ 3 := by
  unfold readResCap
  exact le_trans (memoryCost_bind_le (memoryCost_read _ _).le fun _ _ =>
    memoryCost_bind_le (memoryCost_read _ _).le fun _ _ =>
      memoryCost_bind_le (memoryCost_read _ _).le fun _ t =>
        memoryCost_ite_le (memoryCost_pure _ t).le (memoryCost_pure _ t).le) (by decide)

private theorem memoryCost_bfsInnerStep_le (d : ((Ctx × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (bfsInnerStep d) s ≤ 6 := by
  unfold bfsInnerStep
  exact le_trans (memoryCost_bind_le (memoryCost_read _ _).le fun _ t1 =>
    memoryCost_bind_le (memoryCost_readResCap_le _ t1) fun _ t2 =>
      memoryCost_ite_le (memoryCost_bind_le (memoryCost_write _ _ t2).le fun _ t3 =>
        memoryCost_map_write_le _ _ _ t3) (Nat.zero_le _)) (by decide)

/-- Number of `x < n` (as `Fin n`) with `lo ≤ x` satisfying `P`, split at `x = lo`. -/
private theorem card_filter_ge_split {n lo : ℕ} (hlo : lo < n) (P : Fin n → Prop)
    [DecidablePred P] :
    (Finset.univ.filter fun x : Fin n => lo ≤ x.1 ∧ P x).card =
      (Finset.univ.filter fun x : Fin n => lo + 1 ≤ x.1 ∧ P x).card +
        if P ⟨lo, hlo⟩ then 1 else 0 := by
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter fun x : Fin n => lo ≤ x.1 ∧ P x) (fun x : Fin n => x.1 = lo)
  rw [Finset.filter_filter, Finset.filter_filter] at h
  have e1 : (Finset.univ.filter fun x : Fin n => (lo ≤ x.1 ∧ P x) ∧ ¬ x.1 = lo) =
      Finset.univ.filter fun x : Fin n => lo + 1 ≤ x.1 ∧ P x := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨by omega, h2⟩, fun ⟨h1, h2⟩ => ⟨⟨by omega, h2⟩, by omega⟩⟩
  have e2 : (Finset.univ.filter fun x : Fin n => (lo ≤ x.1 ∧ P x) ∧ x.1 = lo).card =
      if P ⟨lo, hlo⟩ then 1 else 0 := by
    split_ifs with hP
    · rw [Finset.card_eq_one]
      refine ⟨⟨lo, hlo⟩, ?_⟩
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨-, hx⟩; exact Fin.ext hx
      · rintro rfl; exact ⟨⟨le_rfl, hP⟩, rfl⟩
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro x - ⟨⟨-, hPx⟩, hx⟩
      have hxe : x = ⟨lo, hlo⟩ := Fin.ext hx
      exact hP (hxe ▸ hPx)
  rw [e1, e2] at h
  omega

/-- Number of vertices at distance at least `lo` in `t`, split at distance exactly `lo`. -/
private theorem card_dist_ge_split (c : Ctx) (lo : ℕ) (t : Memory.State) :
    (Finset.univ.filter fun x : Fin c.n => lo ≤ t.mem (distAddr c x.1)).card =
      (Finset.univ.filter fun x : Fin c.n => lo + 1 ≤ t.mem (distAddr c x.1)).card +
        (Finset.univ.filter fun x : Fin c.n => t.mem (distAddr c x.1) = lo).card := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    omega
  · rw [Finset.disjoint_filter]
    intro x _ h1 h2
    omega

/-- One layer of the search costs at most `1 + n` plus `6 n` per vertex expanded, the vertices at
distance exactly `layer`. -/
private theorem memoryCost_bfsLayerStep_le (c : Ctx) (layer : ℕ) (hl : layer + 1 < c.n)
    (t : Memory.State) :
    memoryCost (bfsLayerStep (c, layer)) t ≤
      1 + c.n + 6 * c.n *
        (Finset.univ.filter fun x : Fin c.n => t.mem (distAddr c x.1) = layer).card := by
  unfold bfsLayerStep
  dsimp only
  rw [memoryCost_bind', memoryCost_read, clientState_read, memoryCost_bind',
    memoryCost_pure]
  have hmid := memoryCost_iterate_le_potential bfsMidStep (c, layer)
    (fun j (u : ℕ) t' => u + j = c.n ∧ DistRel c layer t t')
    (fun u t' => 6 * c.n *
      (Finset.univ.filter fun x : Fin c.n => u ≤ x.1 ∧ t'.mem (distAddr c x.1) = layer).card)
    1 ?_ c.n 0 t ⟨Nat.zero_add _, DistRel.refl c layer t⟩
  · have hcard : (Finset.univ.filter fun x : Fin c.n =>
        0 ≤ x.1 ∧ t.mem (distAddr c x.1) = layer) =
        Finset.univ.filter fun x : Fin c.n => t.mem (distAddr c x.1) = layer := by
      ext x; simp
    rw [hcard] at hmid
    omega
  intro j u t' ⟨hsum, hrel⟩
  have hu : u < c.n := by omega
  have hl' : layer + 1 ≠ c.n := by omega
  have hstep_rel := bfsMidStep_rel c layer u t'
  have hres : (Memory.spec 0).clientResult t' (bfsMidStep ((c, layer), u)) = u + 1 := by
    exact clientResult_bfsMidStep _ _
  rw [hres]
  refine ⟨⟨by omega, hrel.trans hstep_rel⟩, ?_⟩
  set t'' := (Memory.spec 0).clientState t' (bfsMidStep ((c, layer), u))
  have hsame : ∀ x : Fin c.n,
      t''.mem (distAddr c x.1) = layer ↔ t'.mem (distAddr c x.1) = layer := fun x => by
    rcases hstep_rel x.1 x.2 with h | ⟨h1, h2⟩
    · rw [h]
    · rw [h1, h2]; omega
  have hcnt : (Finset.univ.filter fun x : Fin c.n =>
      u + 1 ≤ x.1 ∧ t''.mem (distAddr c x.1) = layer) =
      Finset.univ.filter fun x : Fin c.n => u + 1 ≤ x.1 ∧ t'.mem (distAddr c x.1) = layer := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hsame x]
  have hcost : memoryCost (bfsMidStep ((c, layer), u)) t' ≤
      1 + if t'.mem (distAddr c u) = layer then 6 * c.n else 0 := by
    unfold bfsMidStep
    dsimp only
    rw [memoryCost_bind', memoryCost_read, clientState_read, clientResult_read]
    split_ifs with hdu
    · rw [memoryCost_bind', memoryCost_pure]
      have hin := memoryCost_iterate_le_of bfsInnerStep 6 ((c, layer), u)
        (fun v t3 => memoryCost_bfsInnerStep_le _ t3) c.n 0 t'
      omega
    · rw [memoryCost_pure]
  rw [hcnt, card_filter_ge_split hu (fun x : Fin c.n => t'.mem (distAddr c x.1) = layer)]
  change _ + _ ≤ 1 + 6 * c.n * (_ + if t'.mem (distAddr c u) = layer then 1 else 0)
  split_ifs at hcost ⊢ <;> rw [Nat.mul_add] <;> omega


private theorem memoryCost_bfsProg_le (d : Ctx × ℕ) (s : Memory.State) :
    memoryCost (bfsProg d) s ≤ 8 * (d.1.n + 1) ^ 2 := by
  obtain ⟨c, src⟩ := d
  dsimp only
  unfold bfsProg
  dsimp only
  rw [memoryCost_bind', memoryCost_bind', memoryCost_write, memoryCost_bind', memoryCost_write,
    memoryCost_bind', memoryCost_pure]
  have hfill := memoryCost_fillRange_le (distAddr c 0) c.n c.n s
  set t₀ := (Memory.spec 0).clientState _ (Memory.write (predAddr c src) src)
  have hlayers := memoryCost_iterate_le_potential bfsLayerStep c
    (fun j (layer : ℕ) _ => layer + j = c.n - 1)
    (fun layer t' => 6 * c.n *
      (Finset.univ.filter fun x : Fin c.n => layer ≤ t'.mem (distAddr c x.1)).card)
    (1 + c.n) ?_ (c.n - 1) 0 t₀ (Nat.zero_add _)
  · have hcard : (Finset.univ.filter fun x : Fin c.n => 0 ≤ t₀.mem (distAddr c x.1)).card ≤ c.n :=
      (Finset.card_le_univ _).trans (by simp)
    have h1 : 6 * c.n * (Finset.univ.filter fun x : Fin c.n =>
        0 ≤ t₀.mem (distAddr c x.1)).card ≤ 6 * c.n * c.n := Nat.mul_le_mul_left _ hcard
    have h2 : (1 + c.n) * (c.n - 1) ≤ (c.n + 1) * c.n := Nat.mul_le_mul (by omega) (Nat.sub_le _ _)
    have h3 : 8 * (c.n + 1) ^ 2 = 8 * (c.n * c.n) + 16 * c.n + 8 := by ring
    have h4 : (c.n + 1) * c.n = c.n * c.n + c.n := by ring
    have h5 : 6 * c.n * c.n = 6 * (c.n * c.n) := by ring
    omega
  intro j layer t' hsum
  have hl : layer + 1 < c.n := by omega
  have hres : (Memory.spec 0).clientResult t' (bfsLayerStep (c, layer)) = layer + 1 := by
    unfold bfsLayerStep; simp only [client_simps]
  rw [hres]
  refine ⟨by omega, ?_⟩
  have hcost := memoryCost_bfsLayerStep_le c layer hl t'
  have hrel : DistRel c layer t' ((Memory.spec 0).clientState t' (bfsLayerStep (c, layer))) := by
    unfold bfsLayerStep
    dsimp only
    rw [clientState_bind_read, clientState_bind,
      clientState_pure]
    exact bfsMid_iterate_rel c layer _ _ t'
  set t'' := (Memory.spec 0).clientState t' (bfsLayerStep (c, layer))
  have hsame : (Finset.univ.filter fun x : Fin c.n => layer + 1 ≤ t''.mem (distAddr c x.1)) =
      Finset.univ.filter fun x : Fin c.n => layer + 1 ≤ t'.mem (distAddr c x.1) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hrel x.1 x.2 with h | ⟨h1, h2⟩
    · rw [h]
    · rw [h1, h2]; omega
  rw [hsame, card_dist_ge_split c layer t', Nat.mul_add]
  omega

private theorem memoryCost_bnStep_le (d : Ctx × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (bnStep d) s ≤ 5 := by
  unfold bnStep
  exact le_trans (memoryCost_bind_le (memoryCost_read _ _).le fun _ t1 =>
    memoryCost_ite_le (memoryCost_bind_le (memoryCost_read _ _).le fun _ t2 =>
      memoryCost_ite_le (memoryCost_bind_le (memoryCost_readResCap_le _ t2) fun _ t3 =>
        memoryCost_ite_le (memoryCost_pure _ t3).le (memoryCost_pure _ t3).le)
        (Nat.zero_le _)) (Nat.zero_le _)) (by decide)

private theorem memoryCost_augStep_le (d : (Ctx × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (augStep d) s ≤ 6 := by
  unfold augStep
  exact le_trans (memoryCost_bind_le (memoryCost_read _ _).le fun _ t1 =>
    memoryCost_ite_le (memoryCost_bind_le (memoryCost_read _ _).le fun _ t2 =>
      memoryCost_ite_le (memoryCost_bind_le (memoryCost_read _ _).le fun _ t3 =>
        memoryCost_bind_le (memoryCost_read _ _).le fun _ t4 =>
          memoryCost_ite_le (memoryCost_bind_le (memoryCost_write _ _ t4).le fun _ t5 =>
            memoryCost_map_write_le _ _ _ t5) (Nat.zero_le _))
        (Nat.zero_le _)) (Nat.zero_le _)) (by decide)

private theorem memoryCost_roundStep_le (d : (Ctx × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    memoryCost (roundStep d) s ≤ 13 * (d.1.1.n + 1) ^ 2 := by
  unfold roundStep
  dsimp only
  have hbr : ∀ dt t, memoryCost
      (if 0 < dt ∧ dt < d.1.1.n then do
        let r ← iterate bnStep d.1.1 dt (d.1.2.2, 2 * d.1.1.capBound)
        let _ ← iterate augStep (d.1.1, r.2) dt d.1.2.2
        pure 0
      else pure 1) t ≤ 11 * d.1.1.n := by
    intro dt t
    rw [memoryCost_ite]
    split_ifs with hdt
    · refine le_trans (memoryCost_bind_le
        (memoryCost_iterate_le_of bnStep 5 _ (fun _ _ => memoryCost_bnStep_le _ _) dt _ t)
        fun _ t2 => memoryCost_bind_le
          (memoryCost_iterate_le_of augStep 6 _ (fun _ _ => memoryCost_augStep_le _ _) dt _ t2)
          fun _ t3 => (memoryCost_pure _ t3).le) ?_
      omega
    · exact Nat.zero_le _
  refine le_trans (memoryCost_bind_le (memoryCost_read _ _).le fun _ t1 =>
    memoryCost_ite_le (memoryCost_bind_le (memoryCost_bfsProg_le _ t1) fun _ t2 =>
      memoryCost_bind_le (memoryCost_read _ _).le fun dt t3 => hbr dt t3)
      (Nat.zero_le _)) ?_
  dsimp only
  have h : 13 * (d.1.1.n + 1) ^ 2 = 13 * (d.1.1.n * d.1.1.n) + 26 * d.1.1.n + 13 := by ring
  have h' : 8 * (d.1.1.n + 1) ^ 2 = 8 * (d.1.1.n * d.1.1.n) + 16 * d.1.1.n + 8 := by ring
  have hsq := Nat.le_mul_self d.1.1.n
  omega

private theorem memoryCost_cutOuterStep_le (d : Ctx × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (cutOuterStep d) s ≤ 1 + 2 * d.1.n := by
  unfold cutOuterStep
  have hin : ∀ va t, memoryCost (cutInnerStep ((d.1, d.2.1), va)) t ≤ 2 := fun va t => by
    unfold cutInnerStep
    exact le_trans (memoryCost_bind_le (memoryCost_read _ _).le fun _ t1 =>
      memoryCost_bind_le (memoryCost_read _ _).le fun _ t2 =>
        memoryCost_ite_le (memoryCost_pure _ t2).le (memoryCost_pure _ t2).le) (by decide)
  refine le_trans (memoryCost_bind_le (memoryCost_read _ _).le fun _ t1 =>
    memoryCost_ite_le (memoryCost_bind_le
      (memoryCost_iterate_le_of cutInnerStep 2 _ hin d.1.n _ t1) fun _ t2 =>
        (memoryCost_pure _ t2).le) (Nat.zero_le _)) ?_
  omega

/-- Memory-operation budget of `ekProg` on `n` vertices, `O(n ^ 5)`. -/
abbrev ekCost (n : ℕ) : ℕ := 20 * (n + 1) ^ 5

theorem memoryCost_ekProg_le (c : Ctx) (s t : ℕ) (st : Memory.State) :
    memoryCost (ekProg (c, (s, t))) st ≤ ekCost c.n := by
  unfold ekProg
  dsimp only
  set n := c.n
  refine le_trans (memoryCost_bind_le (memoryCost_fillRange_le _ _ _ st) fun _ t1 =>
    memoryCost_bind_le (memoryCost_iterate_le_of roundStep (13 * (n + 1) ^ 2) (c, (s, t))
      (fun _ _ => memoryCost_roundStep_le _ _) (n * n * n) 0 t1) fun _ t2 =>
      memoryCost_bind_le (memoryCost_iterate_le_of cutOuterStep (1 + 2 * n) c
        (fun _ _ => memoryCost_cutOuterStep_le _ _) n (0, 0) t2) fun _ t3 =>
        (memoryCost_pure _ t3).le) ?_
  have h1 : 13 * (n + 1) ^ 2 * (n * n * n) ≤ 13 * (n + 1) ^ 5 := by
    have : n * n * n ≤ (n + 1) ^ 3 := by
      have := Nat.pow_le_pow_left (Nat.le_succ n) 3
      simpa [pow_succ, pow_zero, one_mul, mul_assoc] using this
    calc 13 * (n + 1) ^ 2 * (n * n * n) ≤ 13 * (n + 1) ^ 2 * (n + 1) ^ 3 :=
          Nat.mul_le_mul_left _ this
      _ = 13 * (n + 1) ^ 5 := by ring
  have h2 : (1 + 2 * n) * n + n * n ≤ 7 * (n + 1) ^ 5 := by
    have : (n + 1) ^ 2 ≤ (n + 1) ^ 5 := Nat.pow_le_pow_right (Nat.succ_pos n) (by decide)
    nlinarith
  dsimp only [ekCost]
  omega


/-! ### Admissibility (`ValidHistory`) -/

/-- The solver's memory invariant: well-formed memory and an allocated scratch area. -/
private abbrev EkReady (w : ℕ) (c : Ctx) (t : Memory.State) : Prop :=
  Memory.WellFormed w t ∧ c.scratchBase + ekScratch c.n ≤ t.frontier

private theorem ekReady_write {w : ℕ} {c : Ctx} {t : Memory.State} (ht : EkReady w c t)
    (a v : ℕ) (hv : Fits w v) : EkReady w c ⟨Function.update t.mem a v, t.frontier⟩ := by
  refine ⟨⟨ht.1.frontier_fits, fun b => ?_⟩, ht.2⟩
  dsimp only
  by_cases hb : b = a
  · subst hb; simpa using hv
  · rw [Function.update_of_ne hb]; exact ht.1.mem_fits b

private theorem validHistory_readResCap {w : ℕ} {d : (Ctx × ℕ) × ℕ} {t : Memory.State}
    (ht : EkReady w d.1.1 t) (hlay : d.1.1.matBase + d.1.1.n * d.1.1.n ≤ d.1.1.scratchBase)
    (hu : d.1.2 < d.1.1.n) (hv : d.2 < d.1.1.n) :
    (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t (readResCap d)) := by
  have h1 := idx_lt_sq hu hv
  have h2 := idx_lt_sq hv hu
  have hfr := ht.2
  unfold readResCap
  refine validHistory_read_bind (by ek_omega) ?_
  refine validHistory_read_bind (by ek_omega) ?_
  refine validHistory_read_bind (by ek_omega) ?_
  exact validHistory_ite (fun _ => validHistory_pure _ _ _) (fun _ => validHistory_pure _ _ _)

private theorem validHistory_bfsProg {w : ℕ} {d : Ctx × ℕ} {t : Memory.State}
    (hc : CtxFits w d.1) (hs : d.2 < d.1.n) (ht : EkReady w d.1 t) :
    (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t (bfsProg d)) := by
  obtain ⟨c, src⟩ := d
  dsimp only at hc hs ht
  obtain ⟨hlay, hws, hwb⟩ := hc
  unfold bfsProg
  dsimp only
  have hfill := validHistory_fillRange (base := distAddr c 0) (val := c.n) (len := c.n) ht.1
    (by have := ht.2; ek_omega) (hws.of_le (by ek_omega))
  refine validHistory_bind_step hfill ?_
  have ht1 : EkReady w c _ := MonotoneMemInv.pres ht hfill
  refine validHistory_write_bind (by have := ht1.2; ek_omega) (fits_zero w) ?_
  have ht2 := ekReady_write ht1 (distAddr c src) 0 (fits_zero w)
  refine validHistory_write_bind (by have := ht2.2; ek_omega) (hws.of_le (by ek_omega)) ?_
  have ht3 := ekReady_write ht2 (predAddr c src) src (hws.of_le (by ek_omega))
  refine validHistory_bind_step
    (validHistory_iterate_nat (Inv := EkReady w c) (c.n - 1) 0
      (fun layer hlayer t' ht' => ⟨?_, ?_⟩) ht3) (validHistory_pure _ _ _)
  · unfold bfsLayerStep
    refine validHistory_read_bind (by have := ht'.2; ek_omega) ?_
    refine validHistory_bind_step
      (validHistory_iterate_nat (Inv := EkReady w c) c.n 0
        (fun u hu t'' ht'' => ⟨?_, ?_⟩) ht') (validHistory_pure _ _ _)
    · unfold bfsMidStep
      refine validHistory_read_bind (by have := ht''.2; ek_omega) ?_
      refine validHistory_ite (fun _ => ?_) (fun _ => validHistory_pure _ _ _)
      refine validHistory_bind_step
        (validHistory_iterate_nat (Inv := EkReady w c) c.n 0
          (fun v hv t3 ht3 => ⟨?_, ?_⟩) ht'') (validHistory_pure _ _ _)
      · unfold bfsInnerStep
        refine validHistory_read_bind (by have := ht3.2; ek_omega) ?_
        have hrc := validHistory_readResCap (d := ((c, u), v)) ht3 hlay (by ek_omega)
          (by ek_omega)
        refine validHistory_bind_step hrc ?_
        have ht4 : EkReady w c _ := MonotoneMemInv.pres ht3 hrc
        refine validHistory_ite (fun _ => ?_) (fun _ => validHistory_pure _ _ _)
        refine validHistory_write_bind (by have := ht4.2; ek_omega)
          (hws.of_le (by ek_omega)) ?_
        exact validHistory_write_bind (by have := ht4.2; ek_omega)
          (hws.of_le (by ek_omega)) (validHistory_pure _ _ _)
      · exact clientResult_bfsInnerStep _ _
    · exact clientResult_bfsMidStep _ _
  · unfold bfsLayerStep
    simp only [client_simps]

private theorem validHistory_bnStep {w : ℕ} {d : Ctx × (ℕ × ℕ)} {t : Memory.State}
    (hlay : d.1.matBase + d.1.n * d.1.n ≤ d.1.scratchBase) (hn : 0 < d.1.n) (ht : EkReady w d.1 t) :
    (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t (bnStep d)) := by
  have hfr := ht.2
  unfold bnStep
  refine validHistory_read_bind (by ek_omega) ?_
  refine validHistory_ite (fun hcur => ?_) (fun _ => validHistory_pure _ _ _)
  refine validHistory_read_bind (by ek_omega) ?_
  refine validHistory_ite (fun hp => ?_) (fun _ => validHistory_pure _ _ _)
  refine validHistory_bind_step
    (validHistory_readResCap (d := ((d.1, _), d.2.1)) ht hlay hp hcur) ?_
  exact validHistory_ite (fun _ => validHistory_pure _ _ _) (fun _ => validHistory_pure _ _ _)

private theorem validHistory_augStep {w : ℕ} {d : (Ctx × ℕ) × ℕ} {t : Memory.State}
    (hc : CtxFits w d.1.1) (hn : 0 < d.1.1.n) (ht : EkReady w d.1.1 t) :
    (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t (augStep d)) := by
  obtain ⟨hlay, hws, hwb⟩ := hc
  have hfr := ht.2
  unfold augStep
  refine validHistory_read_bind (by ek_omega) ?_
  refine validHistory_ite (fun hcur => ?_) (fun _ => validHistory_pure _ _ _)
  refine validHistory_read_bind (by ek_omega) ?_
  refine validHistory_ite (fun hp => ?_) (fun _ => validHistory_pure _ _ _)
  have h1 := idx_lt_sq hcur hp
  have h2 := idx_lt_sq hp hcur
  refine validHistory_read_bind (by ek_omega) ?_
  refine validHistory_read_bind (by ek_omega) ?_
  refine validHistory_ite (fun hg => ?_) (fun _ => validHistory_pure _ _ _)
  refine validHistory_write_bind (by ek_omega) ((ht.1.mem_fits _).of_le (Nat.sub_le _ _)) ?_
  exact validHistory_write_bind (by ek_omega) (hwb.of_le (by split_ifs <;> ek_omega))
    (validHistory_pure _ _ _)

private theorem validHistory_roundStep {w : ℕ} {d : (Ctx × (ℕ × ℕ)) × ℕ} {t : Memory.State}
    (hc : CtxFits w d.1.1) (hs : d.1.2.1 < d.1.1.n) (hsnk : d.1.2.2 < d.1.1.n)
    (ht : EkReady w d.1.1 t) :
    (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t (roundStep d)) := by
  obtain ⟨⟨c, src, snk⟩, st⟩ := d
  dsimp only at hc hs hsnk ht
  have hn : 0 < c.n := by omega
  unfold roundStep
  dsimp only
  refine validHistory_read_bind (by have := ht.2; ek_omega) ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => validHistory_pure _ _ _)
  have hb := validHistory_bfsProg (d := (c, src)) hc hs ht
  refine validHistory_bind_step hb ?_
  have ht1 : EkReady w c _ := MonotoneMemInv.pres ht hb
  refine validHistory_read_bind (by have := ht1.2; ek_omega) ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => validHistory_pure _ _ _)
  have hbn : ∀ m, (Memory.spec w).ValidHistory _ ((Memory.spec w).clientHistory _
      (iterate bnStep c m (snk, 2 * c.capBound))) := fun m =>
    validHistory_iterate_inv (EkReady w c) bnStep c
      (fun a t' ht' => validHistory_bnStep (d := (c, a)) hc.1 hn ht') m _ ht1
  refine validHistory_bind_step (hbn _) ?_
  exact validHistory_bind_step
    (validHistory_iterate_inv (EkReady w c) augStep _
      (fun a t' ht' => validHistory_augStep (d := ((c, _), a)) hc hn ht') _ snk
      (MonotoneMemInv.pres ht1 (hbn _)))
    (validHistory_pure _ _ _)

private theorem validHistory_cutOuterStep {w : ℕ} {d : Ctx × (ℕ × ℕ)} {t : Memory.State}
    (hlay : d.1.matBase + d.1.n * d.1.n ≤ d.1.scratchBase) (hu : d.2.1 < d.1.n)
    (ht : EkReady w d.1 t) :
    (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t (cutOuterStep d)) := by
  have hfr := ht.2
  unfold cutOuterStep
  refine validHistory_read_bind (by ek_omega) ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => validHistory_pure _ _ _)
  refine validHistory_bind_step
    (validHistory_iterate_fst (Inv := EkReady w d.1) d.1.n 0 _
      (fun v hv b t' ht' => ⟨?_, ?_⟩) ht) (validHistory_pure _ _ _)
  · have h1 := idx_lt_sq hu (show v < d.1.n by omega)
    have hfr' := ht'.2
    unfold cutInnerStep
    refine validHistory_read_bind (by ek_omega) ?_
    refine validHistory_read_bind (by ek_omega) ?_
    exact validHistory_ite (fun _ => validHistory_pure _ _ _) (fun _ => validHistory_pure _ _ _)
  · exact clientResult_cutInnerStep_fst _ _

theorem validHistory_ekProg {w : ℕ} {c : Ctx} {src snk : ℕ} {s : Memory.State}
    (hc : CtxFits w c) (hs : src < c.n) (ht : snk < c.n)
    (hwf : Memory.WellFormed w s) (hfr : c.scratchBase + ekScratch c.n ≤ s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (ekProg (c, (src, snk)))) := by
  have hr : EkReady w c s := ⟨hwf, hfr⟩
  unfold ekProg
  dsimp only
  have hfill := validHistory_fillRange (base := flowAddr c 0 0) (val := 0) (len := c.n * c.n) hwf
    (by ek_omega) (fits_zero w)
  refine validHistory_bind_step hfill ?_
  have hr1 : EkReady w c _ := MonotoneMemInv.pres hr hfill
  have hrounds := validHistory_iterate_inv (EkReady w c) roundStep (c, (src, snk))
    (fun a t' ht' => validHistory_roundStep (d := ((c, (src, snk)), a)) hc hs ht ht')
    (c.n * c.n * c.n) 0 hr1
  refine validHistory_bind_step hrounds ?_
  have hr2 : EkReady w c _ := MonotoneMemInv.pres hr1 hrounds
  refine validHistory_bind_step
    (validHistory_iterate_fst (Inv := EkReady w c) c.n 0 0
      (fun u hu b t' ht' => ⟨validHistory_cutOuterStep (d := (c, (u, b))) hc.1
        (by dsimp only; omega) ht',
        ?_⟩) hr2) (validHistory_pure _ _ _)
  exact clientResult_cutOuterStep_fst _ _


/-! ### Frame and result bound of the solver -/

private theorem preservesAt_augStep {a : ℕ} {d : (Ctx × ℕ) × ℕ}
    (ha : a < flowAddr d.1.1 0 0 ∨ distAddr d.1.1 0 ≤ a) : PreservesAt a (augStep d) := by
  unfold augStep
  dsimp only
  refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
  split_ifs with hcur
  · refine preservesAt_bind (preservesAt_read _ _) fun p => ?_
    split_ifs with hp
    · have h1 := idx_lt_sq hcur hp
      have h2 := idx_lt_sq hp hcur
      refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
      refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
      refine preservesAt_ite _ ?_ (preservesAt_pure _ _)
      refine preservesAt_bind (preservesAt_write _ (by ek_omega)) fun _ => ?_
      exact preservesAt_map _ (preservesAt_write _ (by ek_omega))
    · exact preservesAt_pure _ _
  · exact preservesAt_pure _ _

private theorem preservesAt_roundStep {a : ℕ} {d : (Ctx × (ℕ × ℕ)) × ℕ}
    (hs : d.1.2.1 < d.1.1.n)
    (ha : a < d.1.1.scratchBase ∨ d.1.1.scratchBase + ekScratch d.1.1.n ≤ a) :
    PreservesAt a (roundStep d) := by
  obtain ⟨⟨c, src, snk⟩, sv⟩ := d
  dsimp only at hs ha
  unfold roundStep
  dsimp only
  refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
  refine preservesAt_ite _ ?_ (preservesAt_pure _ _)
  refine preservesAt_bind (preservesAt_bfsProg (d := (c, src)) hs (by ek_omega)) fun _ => ?_
  refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
  refine preservesAt_ite _ ?_ (preservesAt_pure _ _)
  refine preservesAt_bind (fun t => congrArg (fun st : Memory.State => st.mem a)
    (clientState_iterate_eq_of _ _ (fun _ t' => bnStep_state _ t') _ _ t)) fun _ => ?_
  exact preservesAt_bind
    (preservesAt_iterate (fun _ => preservesAt_augStep (by ek_omega)) _ _)
    fun _ => preservesAt_pure _ _

theorem preservesAt_ekProg {a : ℕ} {c : Ctx} {src snk : ℕ} (hs : src < c.n)
    (ha : a < c.scratchBase ∨ c.scratchBase + ekScratch c.n ≤ a) :
    PreservesAt a (ekProg (c, (src, snk))) := by
  unfold ekProg
  dsimp only
  refine preservesAt_bind (preservesAt_fillRange (by ek_omega)) fun _ => ?_
  refine preservesAt_bind (preservesAt_iterate
    (fun sv => preservesAt_roundStep (d := ((c, (src, snk)), sv)) hs ha) _ _) fun _ => ?_
  exact preservesAt_bind (fun t => congrArg (fun st : Memory.State => st.mem a)
    (clientState_iterate_eq_of _ _ (fun _ t' => cutOuterStep_state _ t') _ _ t))
    fun _ => preservesAt_pure _ _

private theorem cutInnerStep_acc_le (d : (Ctx × ℕ) × (ℕ × ℕ)) (t : Memory.State)
    (h : d.2.2 ≤ d.1.1.n * d.1.1.n * d.1.1.capBound + d.1.1.capBound) :
    ((Memory.spec 0).clientResult t (cutInnerStep d)).2 ≤
      d.1.1.n * d.1.1.n * d.1.1.capBound + d.1.1.capBound := by
  unfold cutInnerStep
  dsimp only
  rw [clientResult_bind_read, clientResult_bind_read]
  split_ifs with hg
  · rw [clientResult_pure]
    dsimp only
    omega
  · rw [clientResult_pure]
    exact h

private theorem cutOuterStep_acc_le (d : Ctx × (ℕ × ℕ)) (t : Memory.State)
    (h : d.2.2 ≤ d.1.n * d.1.n * d.1.capBound + d.1.capBound) :
    ((Memory.spec 0).clientResult t (cutOuterStep d)).2 ≤
      d.1.n * d.1.n * d.1.capBound + d.1.capBound := by
  unfold cutOuterStep
  dsimp only
  rw [clientResult_bind_read]
  split_ifs
  · rw [clientResult_bind, clientResult_pure]
    exact iterate_invariant_of cutInnerStep (d.1, d.2.1)
      (fun _ (va : ℕ × ℕ) _ => va.2 ≤ d.1.n * d.1.n * d.1.capBound + d.1.capBound)
      (fun _ va t' hva => cutInnerStep_acc_le ((d.1, d.2.1), va) t' hva) h
  · rw [clientResult_pure]
    exact h

theorem ekProg_result_le (c : Ctx) (s t : ℕ) (st : Memory.State) :
    (Memory.spec 0).clientResult st (ekProg (c, (s, t))) ≤
      c.n * c.n * c.capBound + c.capBound := by
  unfold ekProg
  rw [clientResult_bind, clientResult_bind,
    clientResult_bind, clientResult_pure]
  exact iterate_invariant_of cutOuterStep c
    (fun _ (ua : ℕ × ℕ) _ => ua.2 ≤ c.n * c.n * c.capBound + c.capBound)
    (fun _ ua t' hua => cutOuterStep_acc_le (c, ua) t' hua) (Nat.zero_le _)


/-! ### Semantics: residual capacities and the breadth-first search -/

section Semantics

variable {n mb sb B : ℕ} {W : Fin n → Fin n → ℕ} {src snk : Fin n}

/-- The state holds the capacities `W` at `mb`. -/
private def MatLoaded (n mb : ℕ) (W : Fin n → Fin n → ℕ) (t : Memory.State) : Prop :=
  ∀ u v : Fin n, t.mem (mb + u.1 * n + v.1) = W u v

/-- The state holds the flow `f` at `sb`. -/
private def FlowStored {N : Network (Fin n)} (sb : ℕ) (f : N.Flow) (t : Memory.State) : Prop :=
  ∀ x y : Fin n, t.mem (sb + x.1 * n + y.1) = f x y

private theorem MatLoaded.congr {t t' : Memory.State} (hlay : mb + n * n ≤ sb)
    (hW : MatLoaded n mb W t) (h : ∀ a < sb + n * n, t'.mem a = t.mem a) :
    MatLoaded n mb W t' := fun u v => by
  rw [h _ (by have := idx_lt_sq u.2 v.2; omega)]
  exact hW u v

private theorem FlowStored.congr {N : Network (Fin n)} {f : N.Flow} {t t' : Memory.State}
    (hf : FlowStored sb f t) (h : ∀ a < sb + n * n, t'.mem a = t.mem a) :
    FlowStored sb f t' := fun x y => by
  rw [h _ (by have := idx_lt_sq x.2 y.2; omega)]
  exact hf x y

private theorem readResCap_spec (hB : ∀ u v, W u v ≤ B) {t : Memory.State}
    (hW : MatLoaded n mb W t) {f : (Network.mk W src snk).Flow} (hf : FlowStored sb f t)
    (u v : Fin n) :
    (Memory.spec 0).clientResult t (readResCap ((⟨n, mb, sb, B⟩, u.1), v.1)) = f.resCap u v := by
  unfold readResCap
  dsimp only [capAddr, flowAddr]
  rw [clientResult_bind_read, clientResult_bind_read, clientResult_bind_read, hW u v, hf u v,
    hf v u]
  have hc : W u v ≤ B ∧ f u v ≤ W u v ∧ f v u ≤ B :=
    ⟨hB u v, f.le_cap u v, (f.le_cap v u).trans (hB v u)⟩
  rw [ite_eq_left hc, clientResult_pure]
  rfl

/-- Invariant after the layers below `layer`: distances up to `layer` are exact, the others still
`n`, and every reached vertex other than the source has a parent one layer closer. -/
private def BfsLayerInv {N : Network (Fin n)} (mb sb B : ℕ) (f : N.Flow) (layer : ℕ)
    (t : Memory.State) : Prop :=
  (∀ x : Fin n,
    (f.resDist x ≤ layer → t.mem (distAddr ⟨n, mb, sb, B⟩ x.1) = f.resDist x) ∧
    (layer < f.resDist x → t.mem (distAddr ⟨n, mb, sb, B⟩ x.1) = n)) ∧
  (∀ x : Fin n,
    0 < t.mem (distAddr ⟨n, mb, sb, B⟩ x.1) → t.mem (distAddr ⟨n, mb, sb, B⟩ x.1) < n →
    ∃ u : Fin n,
      t.mem (predAddr ⟨n, mb, sb, B⟩ x.1) = u.1 ∧
      f.resDist u + 1 = f.resDist x ∧
      0 < f.resCap u x)

private theorem bfsMid_spec (hB : ∀ u v, W u v ≤ B) (hlay : mb + n * n ≤ sb)
    {layer : ℕ} {s st : Memory.State} (hW : MatLoaded n mb W s)
    (f : (Network.mk W src snk).Flow) (hf : FlowStored sb f s)
    (hlayer_lt : layer + 1 < n)
    (hst_low : ∀ a < sb + n * n, st.mem a = s.mem a)
    (hlinv : BfsLayerInv mb sb B f layer st) :
    let t_end :=
      (Memory.spec 0).clientState st (iterate bfsMidStep (⟨n, mb, sb, B⟩, layer) (n) 0)
    (Memory.spec 0).clientResult st (iterate bfsMidStep (⟨n, mb, sb, B⟩, layer) (n) 0) =
      n ∧
    (∀ a < sb + n * n, t_end.mem a = s.mem a) ∧
    BfsLayerInv mb sb B f (layer + 1) t_end := by
  let M := n
  have hmid := iterate_invariant_of bfsMidStep (⟨n, mb, sb, B⟩, layer)
    (fun urem (u : ℕ) t' =>
      u + urem = M ∧
      (∀ a < sb + n * n, t'.mem a = s.mem a) ∧
      (∀ x : Fin M, f.resDist x ≤ layer → t'.mem (distAddr ⟨n, mb, sb, B⟩ x.1) = f.resDist x) ∧
      (∀ x : Fin M, layer + 1 < f.resDist x → t'.mem (distAddr ⟨n, mb, sb, B⟩ x.1) = M) ∧
      (∀ x : Fin M, f.resDist x = layer + 1 →
        t'.mem (distAddr ⟨n, mb, sb, B⟩ x.1) = layer + 1 ∨
          t'.mem (distAddr ⟨n, mb, sb, B⟩ x.1) = M) ∧
      (∀ x : Fin M, f.resDist x = layer + 1 →
        (∃ u' : Fin M, u'.1 < u ∧ f.resDist u' = layer ∧ 0 < f.resCap u' x) →
        t'.mem (distAddr ⟨n, mb, sb, B⟩ x.1) = layer + 1) ∧
      (∀ x : Fin M, 0 < t'.mem (distAddr ⟨n, mb, sb, B⟩ x.1) →
        t'.mem (distAddr ⟨n, mb, sb, B⟩ x.1) < M →
        ∃ p : Fin M, t'.mem (predAddr ⟨n, mb, sb, B⟩ x.1) = p.1 ∧
          f.resDist p + 1 = f.resDist x ∧ 0 < f.resCap p x))
    (fun urem u t' ⟨husum, ht_low, hd_le, hd_gt, hd_eq, hd_found, hpar⟩ => by
      have hu_lt : u < M := by omega
      let uFin : Fin M := ⟨u, hu_lt⟩
      unfold bfsMidStep
      dsimp only
      rw [clientResult_bind_read, clientState_bind_read]
      by_cases hdu : t'.mem (distAddr ⟨n, mb, sb, B⟩ u) = layer
      · rw [ite_eq_left hdu, clientResult_bind, clientState_bind, clientResult_pure,
          clientState_pure]
        have hres_u : f.resDist uFin = layer := by
          by_contra hne
          rcases lt_trichotomy (f.resDist uFin) layer with hlt | heq | hgt
          · have h1 : t'.mem (distAddr ⟨n, mb, sb, B⟩ u) = f.resDist uFin :=
            hd_le uFin (le_of_lt hlt)
            omega
          · exact hne heq
          · by_cases h1 : f.resDist uFin = layer + 1
            · rcases hd_eq uFin h1 with h | h
              · have h' : t'.mem (distAddr ⟨n, mb, sb, B⟩ u) = layer + 1 := h; omega
              · have h' : t'.mem (distAddr ⟨n, mb, sb, B⟩ u) = M := h; omega
            · have h2 : t'.mem (distAddr ⟨n, mb, sb, B⟩ u) = M := hd_gt uFin (by omega)
              omega
        have hinn := iterate_invariant_of bfsInnerStep ((⟨n, mb, sb, B⟩, layer), u)
          (fun vrem (v : ℕ) t'' =>
            v + vrem = M ∧
            (∀ a < sb + n * n, t''.mem a = s.mem a) ∧
            (∀ x : Fin M, f.resDist x ≤ layer →
              t''.mem (distAddr ⟨n, mb, sb, B⟩ x.1) = f.resDist x) ∧
            (∀ x : Fin M, layer + 1 < f.resDist x → t''.mem (distAddr ⟨n, mb, sb, B⟩ x.1) = M) ∧
            (∀ x : Fin M, f.resDist x = layer + 1 →
              t''.mem (distAddr ⟨n, mb, sb, B⟩ x.1) = layer + 1 ∨
                t''.mem (distAddr ⟨n, mb, sb, B⟩ x.1) = M) ∧
            (∀ x : Fin M, f.resDist x = layer + 1 →
              (∃ u' : Fin M, u'.1 < u ∧ f.resDist u' = layer ∧ 0 < f.resCap u' x) →
              t''.mem (distAddr ⟨n, mb, sb, B⟩ x.1) = layer + 1) ∧
            (∀ x : Fin M, x.1 < v → 0 < f.resCap uFin x → f.resDist x = layer + 1 →
              t''.mem (distAddr ⟨n, mb, sb, B⟩ x.1) = layer + 1) ∧
            (∀ x : Fin M, 0 < t''.mem (distAddr ⟨n, mb, sb, B⟩ x.1) →
              t''.mem (distAddr ⟨n, mb, sb, B⟩ x.1) < M →
              ∃ p : Fin M, t''.mem (predAddr ⟨n, mb, sb, B⟩ x.1) = p.1 ∧
                f.resDist p + 1 = f.resDist x ∧ 0 < f.resCap p x))
          (fun vrem v t'' ⟨hvsum, hi_low, hi_le, hi_gt, hi_eq, hi_found, hi_cur, hi_par⟩ => by
            have hv_lt : v < M := by omega
            let vFin : Fin M := ⟨v, hv_lt⟩
            have hf'' : FlowStored sb f t'' := hf.congr hi_low
            have hW'' : MatLoaded n mb W t'' := hW.congr hlay hi_low
            unfold bfsInnerStep
            dsimp only
            rw [clientResult_bind_read, clientState_bind_read, clientResult_bind, clientState_bind]
            have hrc_r' : (Memory.spec 0).clientResult t''
                (readResCap ((⟨n, mb, sb, B⟩, u), v)) = f.resCap uFin vFin :=
              readResCap_spec hB hW'' hf'' uFin vFin
            have hrc_s' : (Memory.spec 0).clientState t''
                (readResCap ((⟨n, mb, sb, B⟩, u), v)) = t'' := readResCap_state _ t''
            rw [hrc_r', hrc_s']
            by_cases hcond : t''.mem (distAddr ⟨n, mb, sb, B⟩ v) = M ∧ 0 < f.resCap uFin vFin
            · rw [ite_eq_left hcond, clientResult_bind_write, clientState_bind_write,
                clientResult_bind_write,
                clientState_bind_write]
              simp only [client_simps]
              have hv_res : f.resDist vFin = layer + 1 := by
                have htri := f.resDist_le_add_one_of_pos_resCap hcond.2
                rw [hres_u] at htri
                have hnle : ¬ f.resDist vFin ≤ layer := fun hle => by
                  have h1 : t''.mem (distAddr ⟨n, mb, sb, B⟩ v) = f.resDist vFin := hi_le vFin hle
                  omega
                omega
              refine ⟨by omega, fun a ha => ?_, fun x hx => ?_, fun x hx => ?_,
                fun x hx => ?_, fun x hx hex => ?_, fun x hx hpos hx1 => ?_,
                fun x hpos hlt => ?_⟩
              · rw [Function.update_of_ne (by ek_omega),
                  Function.update_of_ne (by ek_omega)]
                exact hi_low a ha
              · have hxv : x.1 ≠ v := fun h => by
                  have : x = vFin := Fin.ext h; subst this; omega
                rw [Function.update_of_ne (by have := x.2; ek_omega),
                  Function.update_of_ne (by ek_omega)]
                exact hi_le x hx
              · have hxv : x.1 ≠ v := fun h => by
                  have : x = vFin := Fin.ext h; subst this; omega
                rw [Function.update_of_ne (by have := x.2; ek_omega),
                  Function.update_of_ne (by ek_omega)]
                exact hi_gt x hx
              · rw [Function.update_of_ne (by have := x.2; ek_omega)]
                by_cases hxv : x.1 = v
                · left; rw [hxv, Function.update_self]
                · rw [Function.update_of_ne (by ek_omega)]; exact hi_eq x hx
              · rw [Function.update_of_ne (by have := x.2; ek_omega)]
                by_cases hxv : x.1 = v
                · rw [hxv, Function.update_self]
                · rw [Function.update_of_ne (by ek_omega)]; exact hi_found x hx hex
              · rw [Function.update_of_ne (by have := x.2; ek_omega)]
                by_cases hxv : x.1 = v
                · rw [hxv, Function.update_self]
                · rw [Function.update_of_ne (by ek_omega)]
                  exact hi_cur x (by omega) hpos hx1
              · rw [Function.update_of_ne (by have := x.2; ek_omega)]
                  at hpos hlt
                by_cases hxv : x.1 = v
                · have hxeq : x = vFin := Fin.ext hxv
                  subst hxeq
                  exact ⟨uFin, by dsimp only [vFin]; rw [Function.update_self],
                    by rw [hres_u, hv_res], hcond.2⟩
                · rw [Function.update_of_ne (by ek_omega)] at hpos hlt
                  obtain ⟨p, hp1, hp2, hp3⟩ := hi_par x hpos hlt
                  exact ⟨p, by
                    rw [Function.update_of_ne (by ek_omega),
                      Function.update_of_ne (by have := x.2; ek_omega)]
                    exact hp1, hp2, hp3⟩
            · rw [ite_eq_right hcond]
              simp only [client_simps]
              refine ⟨by omega, hi_low, hi_le, hi_gt, hi_eq, hi_found,
                fun x hx hpos hx1 => ?_, hi_par⟩
              by_cases hxv : x.1 = v
              · have hxeq : x = vFin := Fin.ext hxv
                subst hxeq
                rcases hi_eq vFin hx1 with h1 | hM'
                · exact h1
                · exact absurd ⟨hM', hpos⟩ hcond
              · exact hi_cur x (by omega) hpos hx1)
          (n := M) (a := 0) (s := t')
          ⟨Nat.zero_add _, ht_low, hd_le, hd_gt, hd_eq, hd_found,
            fun _ hx => absurd hx (Nat.not_lt_zero _), hpar⟩
        obtain ⟨hvsum_end, h1, h2, h3, h4, h5, h6, h7⟩ := hinn
        have hv_end : (Memory.spec 0).clientResult t'
            (iterate bfsInnerStep ((⟨n, mb, sb, B⟩, layer), u) M 0) = M := by omega
        rw [hv_end] at h6
        refine ⟨by omega, h1, h2, h3, h4, fun x hx ⟨u', hu', hru', hrc'⟩ => ?_, h7⟩
        by_cases hu_eq : u'.1 = u
        · have : u' = uFin := Fin.ext hu_eq
          subst this
          exact h6 x x.2 hrc' hx
        · exact h5 x hx ⟨u', by omega, hru', hrc'⟩
      · rw [ite_eq_right hdu]
        simp only [client_simps]
        refine ⟨by omega, ht_low, hd_le, hd_gt, hd_eq,
          fun x hx ⟨u', hu', hru', hrc'⟩ => ?_, hpar⟩
        by_cases hu_eq : u'.1 = u
        · have : u' = uFin := Fin.ext hu_eq
          subst this
          have h1 : t'.mem (distAddr ⟨n, mb, sb, B⟩ u) = f.resDist uFin :=
            hd_le uFin (le_of_eq hru')
          omega
        · exact hd_found x hx ⟨u', by omega, hru', hrc'⟩)
    (n := M) (a := 0) (s := st)
    ⟨Nat.zero_add _, hst_low, fun x hx => (hlinv.1 x).1 hx,
      fun x hx => (hlinv.1 x).2 (by omega),
      fun x hx => Or.inr ((hlinv.1 x).2 (by omega)),
      fun _ _ ⟨_, hu, _⟩ => absurd hu (Nat.not_lt_zero _),
      hlinv.2⟩
  obtain ⟨husum_end, hm_low, hm_le, hm_gt, _, hm_found, hm_par⟩ := hmid
  have hu_end : (Memory.spec 0).clientResult st
      (iterate bfsMidStep (⟨n, mb, sb, B⟩, layer) M 0) = M := by omega
  rw [hu_end] at hm_found
  refine ⟨hu_end, hm_low, ⟨fun x => ⟨fun hx => ?_, fun hx => hm_gt x hx⟩, hm_par⟩⟩
  by_cases hx_eq : f.resDist x = layer + 1
  · have hcard : layer + 1 < Fintype.card (Fin M) := by rw [Fintype.card_fin]; exact hlayer_lt
    obtain ⟨u', hru', hrc'⟩ := f.exists_pred_of_resDist_eq_succ hcard hx_eq
    rw [hx_eq]
    exact hm_found x hx_eq ⟨u', u'.2, hru', hrc'⟩
  · exact hm_le x (by omega)

private theorem bfsProg_spec (hB : ∀ u v, W u v ≤ B) (hlay : mb + n * n ≤ sb)
    {s : Memory.State} (hW : MatLoaded n mb W s)
    (f : (Network.mk W src snk).Flow) (hf : FlowStored sb f s) :
    let t := (Memory.spec 0).clientState s (bfsProg (⟨n, mb, sb, B⟩, src.1))
    (∀ a < sb + n * n, t.mem a = s.mem a) ∧
      (∀ x : Fin n, t.mem (distAddr ⟨n, mb, sb, B⟩ x.1) = f.resDist x) ∧
      (∀ x : Fin n, 0 < f.resDist x → f.resDist x < n →
        ∃ u : Fin n,
          t.mem (predAddr ⟨n, mb, sb, B⟩ x.1) = u.1 ∧
          f.resDist u + 1 = f.resDist x ∧
          0 < f.resCap u x) := by
  intro t
  have hpres : ∀ a < sb + n * n, t.mem a = s.mem a :=
    fun a ha => preservesAt_bfsProg (d := (⟨n, mb, sb, B⟩, src.1)) src.2 (Or.inl (by ek_omega)) s
  refine ⟨hpres, ?_⟩
  let M := n
  set s1 := (Memory.spec 0).clientState s (fillRange ((distAddr ⟨n, mb, sb, B⟩ 0, M), M))
  have hs1 := fillRange_spec (distAddr ⟨n, mb, sb, B⟩ 0) M M s
  set s2 : Memory.State :=
    ⟨Function.update (Function.update s1.mem (distAddr ⟨n, mb, sb, B⟩ src.1) 0)
      (predAddr ⟨n, mb, sb, B⟩ src.1) src.1, s1.frontier⟩
  have hsrc := src.2
  have hs2_low : ∀ a < sb + n * n, s2.mem a = s.mem a := by
    intro a ha
    have hne1 : a ≠ predAddr ⟨n, mb, sb, B⟩ src.1 := by ek_omega
    have hne2 : a ≠ distAddr ⟨n, mb, sb, B⟩ src.1 := by ek_omega
    dsimp only [s2]
    rw [Function.update_of_ne hne1, Function.update_of_ne hne2]
    exact hs1.2 a (Or.inl (by ek_omega))
  have hfill : ∀ x : Fin n, s1.mem (distAddr ⟨n, mb, sb, B⟩ x.1) = n := fun x =>
    hs1.1 x.1 x.2
  have hinv0 : BfsLayerInv mb sb B f 0 s2 := by
    refine ⟨fun x => ⟨fun hle => ?_, fun hgt => ?_⟩, fun x hpos hlt => ?_⟩
    · have hx0 : f.resDist x = 0 := Nat.eq_zero_of_le_zero hle
      have hxs : x = src := f.eq_source_of_resDist_eq_zero hx0
      subst hxs
      dsimp only [s2]
      rw [Function.update_of_ne (by ek_omega), Function.update_self, hx0]
    · have hxs : x ≠ src := fun h => by
        rw [h] at hgt
        have := f.resDist_source
        simp only at this
        omega
      have hxne : x.1 ≠ src.1 := fun h => hxs (Fin.ext h)
      have hx := x.2
      dsimp only [s2]
      rw [Function.update_of_ne (by ek_omega), Function.update_of_ne (by ek_omega)]
      exact hfill x
    · have hx := x.2
      by_cases hx0 : x.1 = src.1
      · dsimp only [s2] at hpos
        rw [hx0, Function.update_of_ne (by ek_omega), Function.update_self] at hpos
        omega
      · dsimp only [s2] at hlt
        rw [Function.update_of_ne (by ek_omega), Function.update_of_ne (by ek_omega),
          hfill x] at hlt
        omega
  have hlayers := iterate_invariant_of bfsLayerStep ⟨n, mb, sb, B⟩
    (fun rem (layer : ℕ) st =>
      layer + rem = M - 1 ∧ (∀ a < sb + n * n, st.mem a = s.mem a) ∧
        BfsLayerInv mb sb B f layer st)
    (fun rem layer st ⟨hsum, hst_low, hlinv⟩ => by
      have hlayer_lt : layer + 1 < M := by omega
      obtain ⟨_, hm_low, hm_inv⟩ := bfsMid_spec hB hlay hW f hf hlayer_lt hst_low hlinv
      unfold bfsLayerStep
      dsimp only
      rw [clientResult_bind_read, clientState_bind_read, clientResult_bind,
        clientState_bind, clientResult_pure,
        clientState_pure]
      exact ⟨by omega, hm_low, hm_inv⟩)
    (n := M - 1) (a := 0) (s := s2) ⟨Nat.zero_add _, hs2_low, hinv0⟩
  obtain ⟨hsum_end, _, hinv_end⟩ := hlayers
  set s3 := (Memory.spec 0).clientState s2 (iterate bfsLayerStep ⟨n, mb, sb, B⟩ (M - 1) 0)
  have hlay_eq : ((Memory.spec 0).clientResult s2
      (iterate bfsLayerStep ⟨n, mb, sb, B⟩ (M - 1) 0)) = M - 1 := by omega
  rw [hlay_eq] at hinv_end
  have ht_eq : t = s3 := by
    change (Memory.spec 0).clientState s (bfsProg (⟨n, mb, sb, B⟩, src.1)) = s3
    unfold bfsProg
    dsimp only
    rw [clientState_bind, clientState_bind_write, clientState_bind_write,
      clientState_bind, clientState_pure]
  rw [ht_eq]
  have hdist_all : ∀ x : Fin M, s3.mem (distAddr ⟨n, mb, sb, B⟩ x.1) = f.resDist x := by
    intro x
    have hle_card : f.resDist x ≤ M := by simpa [Fintype.card_fin] using f.resDist_le_card x
    by_cases hx : f.resDist x ≤ M - 1
    · exact (hinv_end.1 x).1 hx
    · have hxM : f.resDist x = M := by omega
      rw [(hinv_end.1 x).2 (by omega), hxM]
  refine ⟨hdist_all, fun x hpos hlt => ?_⟩
  rw [← hdist_all x] at hpos hlt
  exact hinv_end.2 x hpos hlt

end Semantics


/-! ### Semantics: the augmenting path, its bottleneck, and the augmentation -/

private theorem fin_mul_add_inj {M : ℕ} {x₁ y₁ x₂ y₂ : Fin M}
    (h : x₁.1 * M + y₁.1 = x₂.1 * M + y₂.1) : x₁ = x₂ ∧ y₁ = y₂ := by
  have hM : 0 < M := Nat.zero_lt_of_lt x₁.2
  have hd : (x₁.1 * M + y₁.1) / M = (x₂.1 * M + y₂.1) / M := congrArg (· / M) h
  have hm : (x₁.1 * M + y₁.1) % M = (x₂.1 * M + y₂.1) % M := congrArg (· % M) h
  rw [Nat.mul_comm x₁.1 M, Nat.mul_add_div hM, Nat.div_eq_of_lt y₁.2, add_zero,
    Nat.mul_comm x₂.1 M, Nat.mul_add_div hM, Nat.div_eq_of_lt y₂.2, add_zero] at hd
  rw [Nat.mul_comm x₁.1 M, Nat.mul_add_mod, Nat.mod_eq_of_lt y₁.2,
    Nat.mul_comm x₂.1 M, Nat.mul_add_mod, Nat.mod_eq_of_lt y₂.2] at hm
  exact ⟨Fin.ext hd, Fin.ext hm⟩

private def buildPath {M : ℕ} (parOf : Fin M → Fin M) : ℕ → Fin M → List (Fin M)
  | 0, cur => [cur]
  | rem + 1, cur => buildPath parOf rem (parOf cur) ++ [cur]

private theorem buildPath_ne_nil {M : ℕ} (parOf : Fin M → Fin M) :
    ∀ rem cur, buildPath parOf rem cur ≠ []
  | 0, _ => List.cons_ne_nil _ _
  | _ + 1, cur => List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil cur [])

private theorem buildPath_getLast? {M : ℕ} (parOf : Fin M → Fin M) :
    ∀ rem cur, (buildPath parOf rem cur).getLast? = some cur
  | 0, _ => rfl
  | rem + 1, cur => by
    unfold buildPath
    rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil cur [])]
    rfl

private theorem buildPath_props {M : ℕ} {N : Network (Fin M)} (f : N.Flow)
    (parOf : Fin M → Fin M)
    (hpar : ∀ x : Fin M, 0 < f.resDist x → f.resDist x < M →
      f.resDist (parOf x) + 1 = f.resDist x ∧ 0 < f.resCap (parOf x) x) :
    ∀ rem (cur : Fin M), rem < M → f.resDist cur = rem →
      (buildPath parOf rem cur).head? = some N.s ∧
      (∀ z ∈ buildPath parOf rem cur, f.resDist z ≤ rem) ∧
      (buildPath parOf rem cur).Nodup ∧
      (∀ e ∈ pathArcs (buildPath parOf rem cur), 1 ≤ f.resCap e.1 e.2)
  | 0, cur, _, hcur => by
    have hs : cur = N.s := f.eq_source_of_resDist_eq_zero hcur
    refine ⟨by simp [buildPath, hs], ?_, List.nodup_singleton cur, by simp [buildPath]⟩
    intro z hz
    simp only [buildPath, List.mem_singleton] at hz
    subst hz
    exact le_of_eq hcur
  | rem + 1, cur, hrem, hcur => by
    obtain ⟨hd_p, hrc_p⟩ := hpar cur (by omega) (by omega)
    have hp_rem : f.resDist (parOf cur) = rem := by omega
    obtain ⟨hhead, hle, hnd, harcs⟩ := buildPath_props f parOf hpar rem (parOf cur)
      (by omega) hp_rem
    have hne := buildPath_ne_nil parOf rem (parOf cur)
    have hlast := buildPath_getLast? parOf rem (parOf cur)
    unfold buildPath
    refine ⟨by rw [List.head?_append_of_ne_nil _ hne]; exact hhead, ?_, ?_, ?_⟩
    · intro z hz
      rcases List.mem_append.mp hz with hz1 | hz2
      · exact (hle z hz1).trans (Nat.le_succ rem)
      · simp only [List.mem_singleton] at hz2; subst hz2; omega
    · refine List.Nodup.append hnd (List.nodup_singleton cur) fun a ha hb => ?_
      simp only [List.mem_singleton] at hb
      subst hb
      have := hle a ha
      omega
    · rw [pathArcs_append_singleton hne hlast]
      intro e he
      rcases List.mem_append.mp he with he1 | he2
      · exact harcs e he1
      · simp only [List.mem_singleton] at he2; subst he2; exact hrc_p


private theorem length_buildPath {M : ℕ} (parOf : Fin M → Fin M) :
    ∀ rem cur, (buildPath parOf rem cur).length = rem + 1
  | 0, _ => rfl
  | rem + 1, cur => by
    rw [buildPath, List.length_append, length_buildPath parOf rem (parOf cur)]
    rfl

private theorem length_pathArcs_buildPath {M : ℕ} (parOf : Fin M → Fin M) (rem : ℕ)
    (cur : Fin M) : (pathArcs (buildPath parOf rem cur)).length = rem := by
  have h := length_pathArcs_add_one (buildPath_ne_nil parOf rem cur)
  rw [length_buildPath] at h
  omega

private theorem pathArcs_buildPath_succ {M : ℕ} (parOf : Fin M → Fin M) (rem : ℕ)
    (cur : Fin M) :
    pathArcs (buildPath parOf (rem + 1) cur) =
      pathArcs (buildPath parOf rem (parOf cur)) ++ [(parOf cur, cur)] := by
  rw [buildPath]
  exact pathArcs_append_singleton (buildPath_ne_nil parOf rem (parOf cur))
    (buildPath_getLast? parOf rem (parOf cur))

section Walks

variable {n mb sb B : ℕ} {W : Fin n → Fin n → ℕ} {src snk : Fin n}

/-- The bottleneck walk computes, from `δ`, the minimum of `δ` and the residual capacities along
the path to `cur` built from the parent function. -/
private theorem iterate_bnStep_spec (hB : ∀ u v, W u v ≤ B) {t : Memory.State}
    (hW : MatLoaded n mb W t) (f : (Network.mk W src snk).Flow) (hf : FlowStored sb f t)
    (parOf : Fin n → Fin n)
    (hpar : ∀ x : Fin n, 0 < f.resDist x → f.resDist x < n →
      f.resDist (parOf x) + 1 = f.resDist x ∧ 0 < f.resCap (parOf x) x)
    (hp_mem : ∀ x : Fin n, 0 < f.resDist x → f.resDist x < n →
      t.mem (predAddr ⟨n, mb, sb, B⟩ x.1) = (parOf x).1) :
    ∀ rem (cur : Fin n) (δ : ℕ), rem < n → f.resDist cur = rem →
      let δ' := ((Memory.spec 0).clientResult t
        (iterate bnStep ⟨n, mb, sb, B⟩ rem (cur.1, δ))).2
      δ' ≤ δ ∧ (∀ e ∈ pathArcs (buildPath parOf rem cur), δ' ≤ f.resCap e.1 e.2) ∧
        (δ' = δ ∨ ∃ e ∈ pathArcs (buildPath parOf rem cur), δ' = f.resCap e.1 e.2)
  | 0, cur, δ, _, _ => by
    refine ⟨le_rfl, ?_, Or.inl rfl⟩
    simp [buildPath, pathArcs_singleton]
  | rem + 1, cur, δ, hrem, hcur => by
    obtain ⟨hd_p, hrc_p⟩ := hpar cur (by omega) (by omega)
    have hp_rem : f.resDist (parOf cur) = rem := by omega
    have hpv := hp_mem cur (by omega) (by omega)
    set δ₁ := if f.resCap (parOf cur) cur ≤ δ then f.resCap (parOf cur) cur else δ with hδ₁
    have hstep : (Memory.spec 0).clientResult t (bnStep (⟨n, mb, sb, B⟩, (cur.1, δ))) =
        ((parOf cur).1, δ₁) := by
      unfold bnStep
      dsimp only
      rw [clientResult_bind_read, ite_eq_left cur.2, clientResult_bind_read, hpv,
        ite_eq_left (parOf cur).2, clientResult_bind,
        readResCap_state, readResCap_spec hB hW hf (parOf cur) cur]
      rw [hδ₁]
      split_ifs <;> rfl
    have hred : ((Memory.spec 0).clientResult t
        (iterate bnStep ⟨n, mb, sb, B⟩ (rem + 1) (cur.1, δ))).2 =
        ((Memory.spec 0).clientResult t
          (iterate bnStep ⟨n, mb, sb, B⟩ rem ((parOf cur).1, δ₁))).2 := by
      change ((Memory.spec 0).clientResult t
        (bnStep (⟨n, mb, sb, B⟩, (cur.1, δ)) >>= iterate bnStep ⟨n, mb, sb, B⟩ rem)).2 = _
      rw [clientResult_bind, bnStep_state, hstep]
    have hih := iterate_bnStep_spec hB hW f hf parOf hpar hp_mem rem (parOf cur) δ₁
      (by omega) hp_rem
    dsimp only at hih ⊢
    rw [hred, pathArcs_buildPath_succ]
    obtain ⟨h1, h2, h3⟩ := hih
    have hδ₁δ : δ₁ ≤ δ := by rw [hδ₁]; split_ifs <;> omega
    have hδ₁r : δ₁ ≤ f.resCap (parOf cur) cur := by rw [hδ₁]; split_ifs <;> omega
    refine ⟨h1.trans hδ₁δ, fun e he => ?_, ?_⟩
    · rcases List.mem_append.mp he with he | he
      · exact h2 e he
      · rw [List.mem_singleton] at he
        subst he
        exact h1.trans hδ₁r
    · rcases h3 with h3 | ⟨e, he, h3⟩
      · rw [h3, hδ₁]
        split_ifs
        · exact Or.inr ⟨(parOf cur, cur), List.mem_append_right _ (List.mem_singleton_self _),
            rfl⟩
        · exact Or.inl rfl
      · exact Or.inr ⟨e, List.mem_append_left _ he, h3⟩

end Walks


private theorem augStep_spec {c : Ctx} {δ cur p : ℕ} (hcur : cur < c.n) (hp : p < c.n)
    {t : Memory.State} (hpred : t.mem (predAddr c cur) = p)
    (hfB : t.mem (flowAddr c p cur) ≤ c.capBound) (hδ : δ ≤ 2 * c.capBound) :
    (Memory.spec 0).clientResult t (augStep ((c, δ), cur)) = p ∧
    (Memory.spec 0).clientState t (augStep ((c, δ), cur)) =
      ⟨Function.update (Function.update t.mem (flowAddr c cur p)
          (t.mem (flowAddr c cur p) - min δ (t.mem (flowAddr c cur p))))
        (flowAddr c p cur) (t.mem (flowAddr c p cur) + (δ - min δ (t.mem (flowAddr c cur p)))),
        t.frontier⟩ := by
  refine ⟨?_, ?_⟩
  · unfold augStep
    dsimp only
    rw [clientResult_bind_read, ite_eq_left hcur, clientResult_bind_read, hpred, ite_eq_left hp,
      clientResult_bind_read, clientResult_bind_read, ite_eq_left ⟨hfB, hδ⟩]
    rfl
  · unfold augStep
    dsimp only
    rw [clientState_bind_read, ite_eq_left hcur, clientState_bind_read, hpred, ite_eq_left hp,
      clientState_bind_read, clientState_bind_read, ite_eq_left ⟨hfB, hδ⟩]
    rfl

section AugWalk

variable {n mb sb B : ℕ} {W : Fin n → Fin n → ℕ} {src snk : Fin n}

/-- The augmentation walk pushes `δ` along the path to `cur` built from the parent function,
cancelling reverse flow first, exactly as `Network.Flow.augmentFun`. -/
private theorem iterate_augStep_spec (hB : ∀ u v, W u v ≤ B) (f : (Network.mk W src snk).Flow)
    (parOf : Fin n → Fin n)
    (hpar : ∀ x : Fin n, 0 < f.resDist x → f.resDist x < n →
      f.resDist (parOf x) + 1 = f.resDist x ∧ 0 < f.resCap (parOf x) x)
    (δ : ℕ) (hδ : δ ≤ 2 * B) :
    ∀ rem (cur : Fin n) (u_st : Memory.State), rem < n → f.resDist cur = rem →
      (∀ x : Fin n, 0 < f.resDist x → f.resDist x < n →
        u_st.mem (predAddr ⟨n, mb, sb, B⟩ x.1) = (parOf x).1) →
      (∀ x y : Fin n,
        ((x, y) ∈ pathArcs (buildPath parOf rem cur) ∨
          (y, x) ∈ pathArcs (buildPath parOf rem cur)) →
        u_st.mem (flowAddr ⟨n, mb, sb, B⟩ x.1 y.1) = f x y) →
      ∀ x y : Fin n,
        ((Memory.spec 0).clientState u_st
          (iterate augStep (⟨n, mb, sb, B⟩, δ) rem cur.1)).mem (flowAddr ⟨n, mb, sb, B⟩ x.1 y.1) =
          if (x, y) ∈ pathArcs (buildPath parOf rem cur) then f x y + (δ - min δ (f y x))
          else if (y, x) ∈ pathArcs (buildPath parOf rem cur) then f x y - min δ (f x y)
          else u_st.mem (flowAddr ⟨n, mb, sb, B⟩ x.1 y.1)
  | 0, cur, u_st, _, _, _, _ => fun x y => by
    simp only [iterate, buildPath, pathArcs_singleton, List.not_mem_nil, ↓reduceIte]
    rfl
  | rem + 1, cur, u_st, hrem, hcur, hp_mem, hf_sub => by
    intro x y
    set c : Ctx := ⟨n, mb, sb, B⟩
    obtain ⟨hd_p, hrc_p⟩ := hpar cur (by omega) (by omega)
    have hp_rem : f.resDist (parOf cur) = rem := by omega
    have hne_pc : parOf cur ≠ cur := fun h => by rw [h] at hp_rem; omega
    have harcs_eq := pathArcs_buildPath_succ parOf rem cur
    have hf_rev : u_st.mem (flowAddr c cur.1 (parOf cur).1) = f cur (parOf cur) :=
      hf_sub cur (parOf cur) (Or.inr (by rw [harcs_eq]; simp))
    have hf_fwd : u_st.mem (flowAddr c (parOf cur).1 cur.1) = f (parOf cur) cur :=
      hf_sub (parOf cur) cur (Or.inl (by rw [harcs_eq]; simp))
    have hfB : u_st.mem (flowAddr c (parOf cur).1 cur.1) ≤ c.capBound := by
      rw [hf_fwd]; exact (f.le_cap _ _).trans (hB _ _)
    obtain ⟨hres1, hst1⟩ := augStep_spec (c := c) (δ := δ) cur.2 (parOf cur).2
      (hp_mem cur (by omega) (by omega)) hfB hδ
    set u1 := (Memory.spec 0).clientState u_st (augStep ((c, δ), cur.1))
    have haddr : ∀ a b a' b' : Fin n, flowAddr c a.1 b.1 = flowAddr c a'.1 b'.1 →
        a = a' ∧ b = b' := fun a b a' b' h => by
      dsimp only [c, flowAddr] at h
      exact fin_mul_add_inj (by omega)
    have hflow1 : ∀ x y : Fin n, u1.mem (flowAddr c x.1 y.1) =
        if (x, y) = (parOf cur, cur) then f x y + (δ - min δ (f y x))
        else if (y, x) = (parOf cur, cur) then f x y - min δ (f x y)
        else u_st.mem (flowAddr c x.1 y.1) := by
      intro x y
      rw [hst1]
      dsimp only
      rw [hf_rev, hf_fwd]
      by_cases hxy : (x, y) = (parOf cur, cur)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hxy
        rw [ite_eq_left rfl, Function.update_self]
      · rw [ite_eq_right hxy, Function.update_of_ne (fun h => hxy (Prod.ext (haddr _ _ _ _ h).1
          (haddr _ _ _ _ h).2))]
        by_cases hyx : (y, x) = (parOf cur, cur)
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hyx
          rw [ite_eq_left rfl, Function.update_self]
        · rw [ite_eq_right hyx, Function.update_of_ne (fun h => hyx (Prod.ext (haddr _ _ _ _ h).2
            (haddr _ _ _ _ h).1))]
    have hpar1 : ∀ x : Fin n, 0 < f.resDist x → f.resDist x < n →
        u1.mem (predAddr c x.1) = (parOf x).1 := fun x hx1 hx2 => by
      rw [preservesAt_augStep (d := ((c, δ), cur.1)) (Or.inr (by ek_omega)) u_st]
      exact hp_mem x hx1 hx2
    obtain ⟨_, hle_rem, _, _⟩ := buildPath_props f parOf hpar rem (parOf cur) (by omega) hp_rem
    have hdisj : ∀ a b : Fin n, (a, b) ∈ pathArcs (buildPath parOf rem (parOf cur)) →
        a ≠ cur ∧ b ≠ cur := by
      intro a b hab
      have ha := hle_rem a (fst_mem_of_mem_pathArcs hab)
      have hb := hle_rem b (snd_mem_of_mem_pathArcs hab)
      exact ⟨fun h => by subst h; omega, fun h => by subst h; omega⟩
    have hf_sub1 : ∀ x y : Fin n,
        ((x, y) ∈ pathArcs (buildPath parOf rem (parOf cur)) ∨
          (y, x) ∈ pathArcs (buildPath parOf rem (parOf cur))) →
        u1.mem (flowAddr c x.1 y.1) = f x y := by
      intro x y hmem
      rw [hflow1 x y]
      rcases hmem with hxy | hyx
      · obtain ⟨_, hyc⟩ := hdisj x y hxy
        have h1 : (x, y) ≠ (parOf cur, cur) := fun h => hyc (Prod.mk.inj h).2
        have h2 : (y, x) ≠ (parOf cur, cur) := fun h => (hdisj x y hxy).1 (Prod.mk.inj h).2
        rw [ite_eq_right h1, ite_eq_right h2]
        exact hf_sub x y (Or.inl (by rw [harcs_eq]; exact List.mem_append_left _ hxy))
      · obtain ⟨hxc, _⟩ := hdisj y x hyx
        have h1 : (x, y) ≠ (parOf cur, cur) := fun h => hxc (Prod.mk.inj h).2
        have h2 : (y, x) ≠ (parOf cur, cur) := fun h => (hdisj y x hyx).2 (Prod.mk.inj h).2
        rw [ite_eq_right h1, ite_eq_right h2]
        exact hf_sub x y (Or.inr (by rw [harcs_eq]; exact List.mem_append_left _ hyx))
    have hih := iterate_augStep_spec hB f parOf hpar δ hδ rem (parOf cur) u1 (by omega) hp_rem
      hpar1 hf_sub1 x y
    change ((Memory.spec 0).clientState u_st
      (augStep ((c, δ), cur.1) >>= iterate augStep (c, δ) rem)).mem _ = _
    rw [clientState_bind, hres1, hih, hflow1 x y, harcs_eq]
    simp only [List.mem_append, List.mem_singleton]
    by_cases h1 : (x, y) ∈ pathArcs (buildPath parOf rem (parOf cur))
    · rw [ite_eq_left h1, ite_eq_left (Or.inl h1)]
    · by_cases h2 : (x, y) = (parOf cur, cur)
      · have h3 : (y, x) ∉ pathArcs (buildPath parOf rem (parOf cur)) := fun h =>
          (hdisj y x h).1 (Prod.mk.inj h2).2
        rw [ite_eq_right h1, ite_eq_right h3, ite_eq_left h2, ite_eq_left (Or.inr h2)]
      · have h12 : ¬ ((x, y) ∈ pathArcs (buildPath parOf rem (parOf cur)) ∨
            (x, y) = (parOf cur, cur)) := not_or.mpr ⟨h1, h2⟩
        rw [ite_eq_right h1, ite_eq_right h12]
        by_cases h3 : (y, x) ∈ pathArcs (buildPath parOf rem (parOf cur))
        · rw [ite_eq_left h3, ite_eq_left (Or.inl h3)]
        · by_cases h4 : (y, x) = (parOf cur, cur)
          · rw [ite_eq_right h3, ite_eq_right h2, ite_eq_left h4, ite_eq_left (Or.inr h4)]
          · have h34 : ¬ ((y, x) ∈ pathArcs (buildPath parOf rem (parOf cur)) ∨
                (y, x) = (parOf cur, cur)) := not_or.mpr ⟨h3, h4⟩
            rw [ite_eq_right h3, ite_eq_right h2, ite_eq_right h4, ite_eq_right h34]

end AugWalk


/-! ### Semantics: one round -/

section Round

variable {n mb sb B : ℕ} {W : Fin n → Fin n → ℕ} {src snk : Fin n}

/-- One running round from a state storing the flow `f`: either `t` is not reached, and the
round leaves the flow alone and stores the residual distances, or it pushes the bottleneck along
a shortest augmenting path. -/
private theorem roundStep_spec (hst : src ≠ snk) (hB : ∀ u v, W u v ≤ B)
    (hlay : mb + n * n ≤ sb) {t : Memory.State} (hW : MatLoaded n mb W t)
    (f : (Network.mk W src snk).Flow) (hf : FlowStored sb f t) :
    let r := (Memory.spec 0).clientResult t (roundStep ((⟨n, mb, sb, B⟩, (src.1, snk.1)), 0))
    let t' := (Memory.spec 0).clientState t (roundStep ((⟨n, mb, sb, B⟩, (src.1, snk.1)), 0))
    (r = 1 ∧ FlowStored sb f t' ∧
        (∀ x : Fin n, t'.mem (distAddr ⟨n, mb, sb, B⟩ x.1) = f.resDist x) ∧ f.resDist snk = n) ∨
      (r = 0 ∧ ∃ (p : List (Fin n)) (hp : f.IsShortestAugmentingPath p),
        FlowStored sb (f.augmentByBottleneck p hp.isAugmentingPath) t') := by
  intro r t'
  set c : Ctx := ⟨n, mb, sb, B⟩
  obtain ⟨hb_low, hb_dist, hb_par⟩ := bfsProg_spec (B := B) (src := src) (snk := snk) hB hlay hW
    f hf
  set tb := (Memory.spec 0).clientState t (bfsProg (c, src.1))
  have hfb : FlowStored sb f tb := hf.congr hb_low
  have hWb : MatLoaded n mb W tb := hW.congr hlay hb_low
  have hred_r : r = (Memory.spec 0).clientResult tb
      (do
        let dt ← Memory.read (distAddr c snk.1)
        if 0 < dt ∧ dt < c.n then
          let r ← iterate bnStep c dt (snk.1, 2 * c.capBound)
          let _ ← iterate augStep (c, r.2) dt snk.1
          pure 0
        else pure 1) := by
    change (Memory.spec 0).clientResult t (roundStep ((c, (src.1, snk.1)), 0)) = _
    unfold roundStep
    dsimp only
    rw [clientResult_bind_read, ite_eq_left rfl, clientResult_bind]
  have hred_s : t' = (Memory.spec 0).clientState tb
      (do
        let dt ← Memory.read (distAddr c snk.1)
        if 0 < dt ∧ dt < c.n then
          let r ← iterate bnStep c dt (snk.1, 2 * c.capBound)
          let _ ← iterate augStep (c, r.2) dt snk.1
          pure 0
        else pure 1) := by
    change (Memory.spec 0).clientState t (roundStep ((c, (src.1, snk.1)), 0)) = _
    unfold roundStep
    dsimp only
    rw [clientState_bind_read, ite_eq_left rfl, clientState_bind]
  rw [clientResult_bind_read] at hred_r
  rw [clientState_bind_read] at hred_s
  have hdt : tb.mem (distAddr c snk.1) = f.resDist snk := hb_dist snk
  rw [hdt] at hred_r hred_s
  by_cases hreach : 0 < f.resDist snk ∧ f.resDist snk < c.n
  · right
    rw [ite_eq_left hreach] at hred_r hred_s
    refine ⟨?_, ?_⟩
    · rw [hred_r, clientResult_bind, clientResult_bind,
        clientResult_pure]
    let parOf : Fin n → Fin n := fun x =>
      if h : tb.mem (predAddr c x.1) < n then ⟨tb.mem (predAddr c x.1), h⟩ else x
    have hpar_spec : ∀ x : Fin n, 0 < f.resDist x → f.resDist x < n →
        tb.mem (predAddr c x.1) = (parOf x).1 ∧
          f.resDist (parOf x) + 1 = f.resDist x ∧ 0 < f.resCap (parOf x) x := by
      intro x hx1 hx2
      obtain ⟨u, hu1, hu2, hu3⟩ := hb_par x hx1 hx2
      have hlt : tb.mem (predAddr c x.1) < n := by rw [hu1]; exact u.2
      have hpu : parOf x = u := by
        simp only [parOf, dite_eq_left hlt]
        exact Fin.ext hu1
      exact ⟨by rw [hpu, hu1], by rw [hpu]; exact hu2, by rw [hpu]; exact hu3⟩
    have hpar : ∀ x : Fin n, 0 < f.resDist x → f.resDist x < n →
        f.resDist (parOf x) + 1 = f.resDist x ∧ 0 < f.resCap (parOf x) x :=
      fun x h1 h2 => (hpar_spec x h1 h2).2
    have hp_mem : ∀ x : Fin n, 0 < f.resDist x → f.resDist x < n →
        tb.mem (predAddr c x.1) = (parOf x).1 := fun x h1 h2 => (hpar_spec x h1 h2).1
    set k := f.resDist snk
    let p := buildPath parOf k snk
    obtain ⟨hhead, -, hnd, harcs⟩ := buildPath_props f parOf hpar k snk hreach.2 rfl
    have hp : f.IsShortestAugmentingPath p :=
      ⟨⟨hnd, hhead, buildPath_getLast? parOf k snk, fun e he => harcs e he⟩,
        length_pathArcs_buildPath parOf k snk⟩
    refine ⟨p, hp, ?_⟩
    -- the bottleneck
    obtain ⟨hδ1, hδ2, hδ3⟩ := iterate_bnStep_spec hB hWb f hfb parOf hpar hp_mem k snk
      (2 * B) hreach.2 rfl
    set δ := ((Memory.spec 0).clientResult tb (iterate bnStep c k (snk.1, 2 * B))).2
    have hne : pathArcs p ≠ [] := by
      intro h
      have := length_pathArcs_buildPath parOf k snk
      rw [show buildPath parOf k snk = p from rfl, h] at this
      simp at this
      omega
    have hδ_eq : δ = f.bottleneck p := by
      obtain ⟨e₀, he₀, hbe₀⟩ := f.exists_mem_pathArcs_resCap_eq_bottleneck hne
      refine le_antisymm ((hδ2 e₀ he₀).trans hbe₀.le) ?_
      rcases hδ3 with h | ⟨e, he, h⟩
      · rw [h]
        refine (f.bottleneck_le_resCap he₀).trans ?_
        have := f.resCap_le_cap_add_cap e₀.1 e₀.2
        have h1 := hB e₀.1 e₀.2
        have h2 := hB e₀.2 e₀.1
        change f.resCap e₀.1 e₀.2 ≤ W e₀.1 e₀.2 + W e₀.2 e₀.1 at this
        omega
      · rw [h]
        exact f.bottleneck_le_resCap he
    have hδB : δ ≤ 2 * B := hδ1
    -- the augmentation
    have hflows := iterate_augStep_spec (mb := mb) (sb := sb) hB f parOf hpar δ hδB k snk tb
      hreach.2 rfl hp_mem (fun x y _ => hfb x y)
    have hst_eq : t' = (Memory.spec 0).clientState tb (iterate augStep (c, δ) k snk.1) := by
      rw [hred_s, clientState_bind,
        clientState_iterate_eq_of _ _ (fun _ t'' => bnStep_state _ t''),
        clientState_bind, clientState_pure]
    intro x y
    rw [hst_eq]
    change _ = Network.Flow.augmentFun f p (f.bottleneck p) x y
    rw [hflows x y, ← hδ_eq, hfb x y]
    rfl
  · left
    rw [ite_eq_right hreach] at hred_r hred_s
    have hk : f.resDist snk = n := by
      have hle : f.resDist snk ≤ n := by simpa [Fintype.card_fin] using f.resDist_le_card snk
      by_contra hne
      have hpos : 0 < f.resDist snk := by
        by_contra h0
        exact hst (f.eq_source_of_resDist_eq_zero (by omega)).symm
      exact hreach ⟨hpos, by change _ < n; omega⟩
    rw [clientState_pure] at hred_s
    rw [clientResult_pure] at hred_r
    rw [hred_s]
    exact ⟨hred_r, hfb, hb_dist, hk⟩

end Round


/-! ### Semantics: the cut sum and the whole solver -/

private theorem sum_filter_lt_succ {n u : ℕ} (hu : u < n) (P : Fin n → Prop) [DecidablePred P]
    (g : Fin n → ℕ) :
    ∑ x ∈ Finset.univ.filter (fun x : Fin n => x.1 < u + 1 ∧ P x), g x =
      ∑ x ∈ Finset.univ.filter (fun x : Fin n => x.1 < u ∧ P x), g x +
        if P ⟨u, hu⟩ then g ⟨u, hu⟩ else 0 := by
  have h := Finset.sum_filter_add_sum_filter_not
    (Finset.univ.filter fun x : Fin n => x.1 < u + 1 ∧ P x) (fun x : Fin n => x.1 = u) g
  rw [Finset.filter_filter, Finset.filter_filter] at h
  have e1 : (Finset.univ.filter fun x : Fin n => (x.1 < u + 1 ∧ P x) ∧ ¬ x.1 = u) =
      Finset.univ.filter fun x : Fin n => x.1 < u ∧ P x := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨by omega, h2⟩, fun ⟨h1, h2⟩ => ⟨⟨by omega, h2⟩, by omega⟩⟩
  have e2 : ∑ x ∈ Finset.univ.filter (fun x : Fin n => (x.1 < u + 1 ∧ P x) ∧ x.1 = u), g x =
      if P ⟨u, hu⟩ then g ⟨u, hu⟩ else 0 := by
    split_ifs with hP
    · rw [Finset.sum_eq_single_of_mem ⟨u, hu⟩ (by simp [hP])]
      intro x hx hxu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact absurd (Fin.ext hx.2) hxu
    · rw [Finset.sum_eq_zero]
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      have hxe : x = ⟨u, hu⟩ := Fin.ext hx.2
      exact absurd (hxe ▸ hx.1.2) hP
  rw [e1, e2] at h
  omega

private theorem sum_filter_lt_full {n : ℕ} (P : Fin n → Prop) [DecidablePred P]
    (g : Fin n → ℕ) :
    ∑ x ∈ Finset.univ.filter (fun x : Fin n => x.1 < n ∧ P x), g x =
      ∑ x ∈ Finset.univ.filter P, g x := by
  congr 1
  ext x
  simp

private theorem sum_sum_le_sq {n B : ℕ} {W : Fin n → Fin n → ℕ} (hB : ∀ u v, W u v ≤ B)
    (S T : Finset (Fin n)) : ∑ x ∈ S, ∑ y ∈ T, W x y ≤ n * n * B := by
  calc ∑ x ∈ S, ∑ y ∈ T, W x y ≤ ∑ x ∈ S, ∑ y ∈ T, B :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hB x y
    _ = S.card * (T.card * B) := by simp
    _ ≤ n * (n * B) := Nat.mul_le_mul (by simpa using S.card_le_univ)
          (Nat.mul_le_mul_right _ (by simpa using T.card_le_univ))
    _ = n * n * B := by ring

section Final

variable {n mb sb B : ℕ} {W : Fin n → Fin n → ℕ}

private theorem iterate_cutInner_spec (hB : ∀ u v, W u v ≤ B) {t : Memory.State}
    (hW : MatLoaded n mb W t) (C : Finset (Fin n))
    (hC : ∀ x : Fin n, (t.mem (distAddr ⟨n, mb, sb, B⟩ x.1) = n ↔ x ∉ C))
    (u : Fin n) (acc : ℕ) (hacc : acc + ∑ y ∈ Finset.univ \ C, W u y ≤ n * n * B) :
    ((Memory.spec 0).clientResult t
      (iterate cutInnerStep (⟨n, mb, sb, B⟩, u.1) n (0, acc))).2 =
      acc + ∑ y ∈ Finset.univ \ C, W u y := by
  have hinv := iterate_invariant_of cutInnerStep (⟨n, mb, sb, B⟩, u.1)
    (fun rem (va : ℕ × ℕ) t' => va.1 + rem = n ∧
      va.2 = acc + ∑ y ∈ Finset.univ.filter (fun y : Fin n => y.1 < va.1 ∧ y ∉ C), W u y ∧
      t' = t)
    (fun rem va t' ⟨hsum, hacc', ht'⟩ => by
      subst ht'
      have hv : va.1 < n := by omega
      set vFin : Fin n := ⟨va.1, hv⟩ with hvFin
      have hpart_le : ∑ y ∈ Finset.univ.filter (fun y : Fin n => y.1 < va.1 ∧ y ∉ C), W u y ≤
          ∑ y ∈ Finset.univ \ C, W u y := by
        refine Finset.sum_le_sum_of_subset fun y hy => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
        simp [hy.2]
      have hres : (Memory.spec 0).clientResult t' (cutInnerStep ((⟨n, mb, sb, B⟩, u.1), va)) =
          (va.1 + 1, if vFin ∉ C then va.2 + W u vFin else va.2) := by
        unfold cutInnerStep
        dsimp only
        rw [clientResult_bind_read, clientResult_bind_read]
        have hcap : t'.mem (capAddr ⟨n, mb, sb, B⟩ u.1 va.1) = W u vFin := hW u vFin
        rw [hcap]
        by_cases hvC : vFin ∈ C
        · have hd : t'.mem (distAddr ⟨n, mb, sb, B⟩ va.1) ≠ n := fun h => (hC vFin).mp h hvC
          rw [ite_eq_right (fun h => hd h.1), ite_eq_right (not_not.mpr hvC),
            clientResult_pure]
        · have hd := (hC vFin).mpr hvC
          rw [ite_eq_left ⟨hd, hB u vFin, by omega⟩, ite_eq_left hvC, clientResult_pure]
      refine ⟨?_, ?_, cutInnerStep_state _ t'⟩
      · rw [hres]; dsimp only; omega
      · rw [hres]
        dsimp only
        rw [sum_filter_lt_succ hv (fun y => y ∉ C), ← hvFin]
        split_ifs <;> omega)
    (n := n) (a := (0, acc)) (s := t) ⟨Nat.zero_add _, by simp, rfl⟩
  obtain ⟨hsum_end, hacc_end, -⟩ := hinv
  rw [hacc_end, show ((Memory.spec 0).clientResult t
    (iterate cutInnerStep (⟨n, mb, sb, B⟩, u.1) n (0, acc))).1 = n by omega,
    sum_filter_lt_full]
  congr 2
  ext y
  simp

private theorem iterate_cutOuter_spec (hB : ∀ u v, W u v ≤ B) {t : Memory.State}
    (hW : MatLoaded n mb W t) (C : Finset (Fin n))
    (hC : ∀ x : Fin n, (t.mem (distAddr ⟨n, mb, sb, B⟩ x.1) = n ↔ x ∉ C))
    (hC' : ∀ x : Fin n, (t.mem (distAddr ⟨n, mb, sb, B⟩ x.1) < n ↔ x ∈ C)) :
    ((Memory.spec 0).clientResult t (iterate cutOuterStep ⟨n, mb, sb, B⟩ n (0, 0))).2 =
      cutWeight W C := by
  have hinv := iterate_invariant_of cutOuterStep ⟨n, mb, sb, B⟩
    (fun rem (ua : ℕ × ℕ) t' => ua.1 + rem = n ∧
      ua.2 = ∑ x ∈ Finset.univ.filter (fun x : Fin n => x.1 < ua.1 ∧ x ∈ C),
        ∑ y ∈ Finset.univ \ C, W x y ∧ t' = t)
    (fun rem ua t' ⟨hsum, hacc', ht'⟩ => by
      subst ht'
      have hu : ua.1 < n := by omega
      set uFin : Fin n := ⟨ua.1, hu⟩ with huFin
      have hsplit := sum_filter_lt_succ hu (fun x => x ∈ C)
        (fun x => ∑ y ∈ Finset.univ \ C, W x y)
      have hres : (Memory.spec 0).clientResult t' (cutOuterStep (⟨n, mb, sb, B⟩, ua)) =
          (ua.1 + 1, if uFin ∈ C then ua.2 + ∑ y ∈ Finset.univ \ C, W uFin y else ua.2) := by
        unfold cutOuterStep
        dsimp only
        rw [clientResult_bind_read]
        by_cases huC : uFin ∈ C
        · rw [ite_eq_left ((hC' uFin).mpr huC), ite_eq_left huC, clientResult_bind,
            clientResult_pure]
          congr 1
          refine iterate_cutInner_spec hB hW C hC uFin ua.2 ?_
          rw [hacc']
          have := sum_sum_le_sq hB
            (Finset.univ.filter (fun x : Fin n => x.1 < ua.1 + 1 ∧ x ∈ C)) (Finset.univ \ C)
          rw [hsplit, ite_eq_left huC] at this
          exact this
        · rw [ite_eq_right (fun h => huC ((hC' uFin).mp h)), ite_eq_right huC,
            clientResult_pure]
      refine ⟨?_, ?_, cutOuterStep_state _ t'⟩
      · rw [hres]; dsimp only; omega
      · rw [hres]
        dsimp only
        rw [hsplit, ← huFin]
        split_ifs <;> omega)
    (n := n) (a := (0, 0)) (s := t) ⟨Nat.zero_add _, by simp, rfl⟩
  obtain ⟨hsum_end, hacc_end, -⟩ := hinv
  rw [hacc_end, show ((Memory.spec 0).clientResult t
    (iterate cutOuterStep ⟨n, mb, sb, B⟩ n (0, 0))).1 = n by omega, sum_filter_lt_full,
    show Finset.univ.filter (· ∈ C) = C by ext; simp]
  rfl

end Final


private theorem roundStep_idle {d : (Ctx × (ℕ × ℕ)) × ℕ} (h : d.2 ≠ 0) (t : Memory.State) :
    (Memory.spec 0).clientResult t (roundStep d) = 1 ∧
      (Memory.spec 0).clientState t (roundStep d) = t := by
  unfold roundStep
  dsimp only
  exact ⟨by rw [clientResult_bind_read, ite_eq_right h, clientResult_pure],
    by rw [clientState_bind_read, ite_eq_right h, clientState_pure]⟩

/-- **Correctness of dense Edmonds–Karp on a flow network.** On a state holding the capacities
`N.cap ≤ B` at `mb`, `ekProg` leaves memory outside its scratch area unchanged, stores an integral
maximum flow `f` at `flowAddr`, marks `C = f.reachableCut` via `distAddr < n` as a minimum `s`–`t`
cut with `f.value = N.cutCapacity C`, and returns `N.cutCapacity C`. -/
private theorem ekProg_flow_spec {n mb sb B : ℕ} (N : Network (Fin n)) (hst : N.s ≠ N.t)
    (hB : ∀ u v, N.cap u v ≤ B) (hlay : mb + n * n ≤ sb) {st : Memory.State}
    (hW : ∀ u v : Fin n, st.mem (mb + u.1 * n + v.1) = N.cap u v) :
    let c : Ctx := ⟨n, mb, sb, B⟩
    let st' := (Memory.spec 0).clientState st (ekProg (c, (N.s.1, N.t.1)))
    let C : Finset (Fin n) := Finset.univ.filter fun x => st'.mem (distAddr c x.1) < n
    (∀ a, (a < sb ∨ sb + ekScratch n ≤ a) → st'.mem a = st.mem a) ∧
      ∃ f : N.Flow,
        (∀ u v : Fin n, st'.mem (flowAddr c u.1 v.1) = f u v) ∧
        (∀ x : Fin n, st'.mem (distAddr c x.1) ≤ n) ∧
        f.IsMaxFlow ∧ N.IsMinCut C ∧ C = f.reachableCut ∧
        f.value = (N.cutCapacity C : ℤ) ∧
        (Memory.spec 0).clientResult st (ekProg (c, (N.s.1, N.t.1))) = N.cutCapacity C := by
  dsimp only
  have hn : 0 < n := Nat.zero_lt_of_lt N.s.2
  have hframe : ∀ a, (a < sb ∨ sb + ekScratch n ≤ a) →
      ((Memory.spec 0).clientState st (ekProg (⟨n, mb, sb, B⟩, (N.s.1, N.t.1)))).mem a =
        st.mem a :=
    fun a ha => preservesAt_ekProg (c := ⟨n, mb, sb, B⟩) (src := N.s.1) (snk := N.t.1) N.s.2 ha st
  set s1 := (Memory.spec 0).clientState st (fillRange ((flowAddr ⟨n, mb, sb, B⟩ 0 0, 0), n * n))
  have hs1 := fillRange_spec (flowAddr ⟨n, mb, sb, B⟩ 0 0) 0 (n * n) st
  have hW1 : MatLoaded n mb N.cap s1 := fun u v => by
    rw [hs1.2 _ (Or.inl (by have := idx_lt_sq u.2 v.2; ek_omega))]
    exact hW u v
  have hf1 : FlowStored sb (Network.Flow.zero N) s1 := fun x y => by
    have h := hs1.1 (x.1 * n + y.1) (idx_lt_sq x.2 y.2)
    have he : flowAddr ⟨n, mb, sb, B⟩ 0 0 + (x.1 * n + y.1) = sb + x.1 * n + y.1 := by
      dsimp only [flowAddr]; ring
    rw [he] at h
    exact h
  have hloop := iterate_invariant_of roundStep (⟨n, mb, sb, B⟩, (N.s.1, N.t.1))
    (fun rem (sv : ℕ) tt => sv ≤ 1 ∧ MatLoaded n mb N.cap tt ∧
      ∃ (k : ℕ) (flows : ℕ → N.Flow) (paths : ℕ → List (Fin n)),
        N.IsShortestAugmentingSeq k flows paths ∧ FlowStored sb (flows k) tt ∧
        (sv = 0 → k + rem = n * n * n) ∧
        (sv = 1 → (∀ x : Fin n, tt.mem (distAddr ⟨n, mb, sb, B⟩ x.1) = (flows k).resDist x) ∧
          (flows k).resDist N.t = n))
    (fun rem sv tt ⟨hsv, hWt, k, flows, paths, hseq, hft, h0, h1⟩ => by
      have hWt' : ∀ tt', (∀ a, (a < sb ∨ sb + ekScratch n ≤ a) → tt'.mem a = tt.mem a) →
          MatLoaded n mb N.cap tt' := fun tt' hfr u v => by
        rw [hfr _ (Or.inl (by have := idx_lt_sq u.2 v.2; omega))]
        exact hWt u v
      have hfr_round : ∀ a, (a < sb ∨ sb + ekScratch n ≤ a) →
          ((Memory.spec 0).clientState tt (roundStep ((⟨n, mb, sb, B⟩, (N.s.1, N.t.1)), sv))).mem a
            = tt.mem a :=
        fun a ha => preservesAt_roundStep (d := ((⟨n, mb, sb, B⟩, (N.s.1, N.t.1)), sv)) N.s.2 ha tt
      by_cases hsv0 : sv = 0
      · subst hsv0
        have hk := h0 rfl
        rcases roundStep_spec (B := B) hst hB hlay hWt (flows k) hft with
          ⟨hr, hf', hd, hrt⟩ | ⟨hr, p, hp, hf'⟩
        · refine ⟨le_of_eq hr, hWt' _ hfr_round, k, flows, paths, hseq, hf',
            fun h => absurd (hr.symm.trans h) one_ne_zero, fun _ => ⟨hd, hrt⟩⟩
        · let flows' : ℕ → N.Flow := fun i =>
            if i ≤ k then flows i else (flows k).augmentByBottleneck p hp.isAugmentingPath
          let paths' : ℕ → List (Fin n) := fun i => if i = k then p else paths i
          have hseq' : N.IsShortestAugmentingSeq (k + 1) flows' paths' := by
            intro j hj
            by_cases hjk : j = k
            · subst hjk
              simp only [flows', paths', ite_eq_left (le_refl j),
                ite_eq_right (show ¬ j + 1 ≤ j by omega),
                ite_eq_left rfl]
              exact ⟨hp, trivial⟩
            · obtain ⟨hpj, hj'⟩ := hseq j (by omega)
              simp only [flows', paths', ite_eq_left (show j ≤ k by omega),
                ite_eq_left (show j + 1 ≤ k by omega), ite_eq_right hjk]
              exact ⟨hpj, hj'⟩
          have hf'' : FlowStored sb (flows' (k + 1))
              ((Memory.spec 0).clientState tt
                (roundStep ((⟨n, mb, sb, B⟩, (N.s.1, N.t.1)), 0))) := by
            simp only [flows', ite_eq_right (show ¬ k + 1 ≤ k by omega)]
            exact hf'
          refine ⟨by omega, hWt' _ hfr_round, k + 1, flows', paths', hseq', hf'',
            fun _ => by omega, fun h => absurd (hr.symm.trans h) zero_ne_one⟩
      · have hsv1 : sv = 1 := by omega
        obtain ⟨hr, hs⟩ := roundStep_idle (d := ((⟨n, mb, sb, B⟩, (N.s.1, N.t.1)), sv)) hsv0 tt
        rw [hr, hs]
        exact ⟨le_rfl, hWt, k, flows, paths, hseq, hft, fun h => absurd h one_ne_zero,
          fun _ => h1 hsv1⟩)
    (n := n * n * n) (a := 0) (s := s1)
    ⟨Nat.zero_le _, hW1, 0, fun _ => Network.Flow.zero N, fun _ => [],
      fun j hj => absurd hj (Nat.not_lt_zero _), hf1, fun _ => by omega,
      fun h => absurd h zero_ne_one⟩
  set s2 := (Memory.spec 0).clientState s1
    (iterate roundStep (⟨n, mb, sb, B⟩, (N.s.1, N.t.1)) (n * n * n) 0)
  obtain ⟨hsv, hW2, k, flows, paths, hseq, hf2, h0, h1⟩ := hloop
  have hsv1 : (Memory.spec 0).clientResult s1
      (iterate roundStep (⟨n, mb, sb, B⟩, (N.s.1, N.t.1)) (n * n * n) 0) = 1 := by
    by_contra hne
    have hk := h0 (by omega)
    have hb := N.shortestAugmentingSeq_length_le hst hseq
    have hsym := N.card_symArcs_le_card_sq
    rw [Fintype.card_fin] at hb hsym
    have h2 : N.symArcs.card * (n / 2) ≤ n * n * (n / 2) := Nat.mul_le_mul_right _ hsym
    have h3 : n * n * (n / 2) < n * n * n :=
      Nat.mul_lt_mul_of_pos_left (Nat.div_lt_self hn (by norm_num)) (Nat.mul_pos hn hn)
    omega
  obtain ⟨hdist, hres_t⟩ := h1 hsv1
  have hst_eq : (Memory.spec 0).clientState st (ekProg (⟨n, mb, sb, B⟩, (N.s.1, N.t.1))) = s2 := by
    unfold ekProg
    dsimp only
    rw [clientState_bind, clientState_bind,
      clientState_bind,
      clientState_iterate_eq_of _ _ (fun _ t' => cutOuterStep_state _ t'),
      clientState_pure]
  have hres_eq : (Memory.spec 0).clientResult st (ekProg (⟨n, mb, sb, B⟩, (N.s.1, N.t.1))) =
      ((Memory.spec 0).clientResult s2 (iterate cutOuterStep ⟨n, mb, sb, B⟩ n (0, 0))).2 := by
    unfold ekProg
    dsimp only
    rw [clientResult_bind, clientResult_bind,
      clientResult_bind, clientResult_pure]
  rw [hst_eq, hres_eq]
  rw [hst_eq] at hframe
  refine ⟨hframe, flows k, ?_⟩
  set f := flows k
  set C : Finset (Fin n) := Finset.univ.filter fun x => s2.mem (distAddr ⟨n, mb, sb, B⟩ x.1) < n
  have hle : ∀ x : Fin n, s2.mem (distAddr ⟨n, mb, sb, B⟩ x.1) ≤ n := fun x => by
    rw [hdist x]; simpa [Fintype.card_fin] using f.resDist_le_card x
  have hC' : ∀ x : Fin n, (s2.mem (distAddr ⟨n, mb, sb, B⟩ x.1) < n ↔ x ∈ C) := fun x => by
    simp [C]
  have hC : ∀ x : Fin n, (s2.mem (distAddr ⟨n, mb, sb, B⟩ x.1) = n ↔ x ∉ C) := fun x => by
    rw [← hC' x]
    have := hle x
    omega
  have hno : ¬ ∃ p, f.IsAugmentingPath p := by
    rw [f.exists_augmentingPath_iff_resReachable, ← f.resDist_lt_card_iff_resReachable,
      Fintype.card_fin]
    omega
  have hC_eq : C = f.reachableCut := by
    ext x
    rw [f.mem_reachableCut_iff, ← f.resDist_lt_card_iff_resReachable, Fintype.card_fin,
      ← hdist x, hC' x]
  have hval : f.value = (N.cutCapacity C : ℤ) := by
    rw [hC_eq]
    exact f.value_eq_cutCapacity_reachableCut hno
  have hmin : N.IsMinCut C := by
    rw [hC_eq]
    exact f.isMinCut_of_value_eq_cutCapacity (f.reachableCut_isCut hno)
      (f.value_eq_cutCapacity_reachableCut hno)
  have hmax : f.IsMaxFlow := (f.isMaxFlow_iff_not_exists_augmentingPath hst).mpr hno
  have hres : ((Memory.spec 0).clientResult s2 (iterate cutOuterStep ⟨n, mb, sb, B⟩ n (0, 0))).2 =
      N.cutCapacity C := iterate_cutOuter_spec hB hW2 C hC hC'
  exact ⟨fun u v => hf2 u v, hle, hmax, hmin, hC_eq, hval, hres⟩

/-- **Correctness of dense Edmonds–Karp.** On a state holding the capacities `W ≤ B` at `mb`,
`ekProg` leaves memory outside its scratch area unchanged, the set `C` of vertices whose final
distance is below `n` is a minimum `s`–`t` cut of `cutWeight W`, and the returned value is
`cutWeight W C`. -/
theorem ekProg_spec {n mb sb B : ℕ} {W : Fin n → Fin n → ℕ} {s t : Fin n} (hst : s ≠ t)
    (hB : ∀ u v, W u v ≤ B) (hlay : mb + n * n ≤ sb) {st : Memory.State}
    (hW : ∀ u v : Fin n, st.mem (mb + u.1 * n + v.1) = W u v) :
    let c : Ctx := ⟨n, mb, sb, B⟩
    let st' := (Memory.spec 0).clientState st (ekProg (c, (s.1, t.1)))
    let C : Finset (Fin n) := Finset.univ.filter fun x => st'.mem (distAddr c x.1) < n
    (∀ a, (a < sb ∨ sb + ekScratch n ≤ a) → st'.mem a = st.mem a) ∧
      IsMinCutBetween (cutWeight W) s t C ∧
      (Memory.spec 0).clientResult st (ekProg (c, (s.1, t.1))) = cutWeight W C := by
  obtain ⟨hframe, _, _, _, _, hmin, _, _, hres⟩ :=
    ekProg_flow_spec (Network.mk W s t) hst hB hlay hW
  exact ⟨hframe, hmin.isMinCutBetween, hres⟩

/-! ### Uniform dense Edmonds–Karp flat program -/

section UniformEK

/-- Word-RAM input `n :: s :: t :: flattenMatrix N.cap`: vertex count at address `1`, source at `2`,
sink at `3`, and row-major capacity matrix `N.cap u v` at `4 + u * n + v`. -/
@[expose] def encodeFlowInput {n : ℕ} (N : Network (Fin n)) : List ℕ :=
  n :: N.s.1 :: N.t.1 :: flattenMatrix N.cap

/-- Output address of the final flow value `f u v` left by `exists_edmondsKarp_program`. -/
@[expose] def ekFlowAddr (n u v : ℕ) : ℕ := 4 + n * n + u * n + v

/-- Output address of the final residual distance of `x` (`< n` iff `x` lies in the minimum cut)
left by `exists_edmondsKarp_program`. -/
@[expose] def ekCutAddr (n x : ℕ) : ℕ := 4 + n * n + n * n + x

/-- Memory frontier required by `exists_edmondsKarp_program`: `4 + 2 * n^2 + 2 * n`. -/
@[expose] def ekWorkspace (n : ℕ) : ℕ := 4 + 2 * (n * n) + 2 * n

private def ekMaxStep (d : ℕ × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let x ← Memory.read (d.1 + d.2.1)
  if d.2.2 < x then pure (d.2.1 + 1, x) else pure (d.2.1 + 1, d.2.2)

private def ekFullMain (d : ℕ × ℕ × ℕ) : Memory.Prog ℕ := do
  let n := d.1
  let s := d.2.1
  let t := d.2.2
  let _ ← Memory.alloc (ekScratch n)
  if s < n ∧ t < n then
    let m ← iterate ekMaxStep 4 (n * n) (0, 0)
    ekProg (⟨n, 4, 4 + n * n, m.2⟩, (s, t))
  else
    pure 0

private def ekFullProg (_ : Unit) : Memory.Prog ℕ := do
  let n ← Memory.read 1
  let s ← Memory.read 2
  let t ← Memory.read 3
  ekFullMain (n, s, t)

private theorem ekMaxStep_realizes :
    Realizes .exact ekMaxStep (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w d _ => Fits w (d.1 + d.2.1) ∧ Fits w (d.2.1 + 1)) (fun _ _ => 0) := by
  unfold ekMaxStep
  realize
  · exact h.1
  · exact h.2
  · exact h.2

private theorem ekMaxScan_spec {base len B : ℕ} {st : Memory.State}
    (hB : ∀ i < len, st.mem (base + i) ≤ B) :
    let r := (Memory.spec 0).clientResult st (iterate ekMaxStep base len (0, 0))
    r.2 ≤ B ∧ ∀ i < len, st.mem (base + i) ≤ r.2 := by
  have hst : ∀ a t, (Memory.spec 0).clientState t (ekMaxStep (base, a)) = t := fun a t => by
    unfold ekMaxStep
    rw [clientState_bind_read]
    split_ifs <;> rfl
  have hinv := iterate_invariant_of ekMaxStep base
    (fun rem (p : ℕ × ℕ) t => t = st ∧ p.1 + rem = len ∧ p.2 ≤ B ∧
      ∀ i < p.1, st.mem (base + i) ≤ p.2)
    (fun rem p t ⟨ht, hsum, hle, hall⟩ => by
      subst ht
      refine ⟨hst p t, ?_⟩
      unfold ekMaxStep
      rw [clientResult_bind_read]
      dsimp only
      split_ifs with hlt
      · rw [clientResult_pure]
        dsimp only
        refine ⟨by omega, hB p.1 (by omega), fun i hi => ?_⟩
        by_cases hip : i = p.1
        · subst hip; exact le_rfl
        · exact (hall i (by omega)).trans (Nat.le_of_lt hlt)
      · rw [clientResult_pure]
        dsimp only
        refine ⟨by omega, hle, fun i hi => ?_⟩
        by_cases hip : i = p.1
        · subst hip; omega
        · exact hall i (by omega))
    (n := len) (a := (0, 0)) (s := st)
    ⟨rfl, Nat.zero_add _, Nat.zero_le _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  exact ⟨hinv.2.2.1, fun i hi => hinv.2.2.2 i (by omega)⟩

private theorem ekMaxScan_state (base len : ℕ) (st : Memory.State) :
    (Memory.spec 0).clientState st (iterate ekMaxStep base len (0, 0)) = st :=
  clientState_iterate_eq_of ekMaxStep base (fun _ t => by
    unfold ekMaxStep
    rw [clientState_bind_read]
    split_ifs <;> rfl) len (0, 0) st

private theorem clientResult_ekMaxStep_fst (d : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    ((Memory.spec 0).clientResult s (ekMaxStep d)).1 = d.2.1 + 1 := by
  unfold ekMaxStep
  rw [clientResult_bind_read]
  split_ifs <;> rfl

private theorem ekFullMain_realizes :
    Realizes .exact ekFullMain (WordEncoding.encode (α := ℕ × ℕ × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d st => st.frontier = 4 + d.1 * d.1 ∧ Fits w (ekWorkspace d.1) ∧
        ∃ B, (∀ i < d.1 * d.1, st.mem (4 + i) ≤ B) ∧ Fits w (ekBound d.1 B))
      (fun _ _ => 0) := by
  unfold ekFullMain
  realize [ekMaxStep_realizes, ekProg_realizes]
  all_goals
    obtain ⟨hfr, hw, B, hB, hwB⟩ := h
    dsimp -failIfUnchanged only [CtxFits, ekScratch, ekWorkspace] at *
    try assumption
    try (apply hw.of_le; omega)
  · refine iterationSafe_of_stepInv _ _ w _
      (fun rem (p : ℕ × ℕ) _ => p.1 + rem = d.1 * d.1) ?_ (Nat.zero_add _)
    intro rem p t hsum
    dsimp only at hsum ⊢
    refine ⟨⟨hw.of_le (by omega), hw.of_le (by omega), hw.of_le (by omega)⟩, ?_⟩
    rw [clientResult_ekMaxStep_fst]
    dsimp only
    omega
  · have hal : ∀ i < d.1 * d.1,
        ((Memory.spec 0).clientState s (Memory.alloc (ekScratch d.1))).mem (4 + i) ≤ B :=
      fun i hi => (Memory.mem_step_of_lt_frontier s (.alloc (ekScratch d.1))
        (by rw [hfr]; omega) (by simp)).trans_le (hB i hi)
    have hM := (ekMaxScan_spec hal).1
    refine ⟨by omega, hw.of_le (by omega), hwB.of_le (by unfold ekBound; gcongr <;> exact hM)⟩

private theorem ekFullProg_realizes :
    Realizes .exact ekFullProg (WordEncoding.encode (α := Unit)) (WordEncoding.encode (α := ℕ))
      (fun w _ st => st.frontier = 4 + st.mem 1 * st.mem 1 ∧ Fits w (ekWorkspace (st.mem 1)) ∧
        ∃ B, (∀ i < st.mem 1 * st.mem 1, st.mem (4 + i) ≤ B) ∧ Fits w (ekBound (st.mem 1) B))
      (fun _ _ => 0) := by
  unfold ekFullProg
  realize [ekFullMain_realizes]
  all_goals
    obtain ⟨hfr, hw, B, hB, hwB⟩ := h
    first
    | exact hw.of_le (by dsimp only [ekWorkspace]; omega)
    | exact hfr
    | exact ⟨B, hB, hwB⟩

private theorem memoryCost_ekFullProg_le (s : Memory.State) :
    memoryCost (ekFullProg ()) s ≤ 25 * (s.mem 1 + 1) ^ 5 := by
  unfold ekFullProg
  rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
    memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
    memoryCost_bind', memoryCost_read, clientResult_read, clientState_read]
  unfold ekFullMain
  dsimp only
  set n := s.mem 1
  have hstep : ∀ (p : ℕ × ℕ) t, memoryCost (ekMaxStep (4, p)) t ≤ 1 := fun p t => by
    unfold ekMaxStep
    exact memoryCost_read_bind_le fun _ _ => memoryCost_ite_le (by simp) (by simp)
  have hmain : memoryCost (do
      let _ ← Memory.alloc (ekScratch n)
      if s.mem 2 < n ∧ s.mem 3 < n then
        let m ← iterate ekMaxStep 4 (n * n) (0, 0)
        ekProg (⟨n, 4, 4 + n * n, m.2⟩, (s.mem 2, s.mem 3))
      else pure 0) s ≤ (ekScratch n + 1) + (n * n + ekCost n) := by
    refine memoryCost_bind_le (memoryCost_alloc _ _).le fun _ t => ?_
    refine memoryCost_ite_le ?_ (by simp)
    exact memoryCost_bind_le
      (by simpa [Nat.one_mul] using memoryCost_iterate_le_of ekMaxStep 1 4 hstep (n * n) (0, 0) t)
      fun m t' => memoryCost_ekProg_le ⟨n, 4, 4 + n * n, m.2⟩ (s.mem 2) (s.mem 3) t'
  have h1 : (n + 1) ^ 2 ≤ (n + 1) ^ 5 := Nat.pow_le_pow_right (Nat.succ_pos n) (by decide)
  have h2 : 1 ≤ (n + 1) ^ 5 := Nat.one_le_pow _ _ (Nat.succ_pos n)
  dsimp only [ekScratch, ekCost] at hmain
  nlinarith

private theorem flowInit_mem_matrix {n : ℕ} (N : Network (Fin n)) {i : ℕ} (hi : i < n * n) :
    (Memory.State.init (encodeFlowInput N)).mem (4 + i) =
      (flattenMatrix N.cap)[i]'(by rw [length_flattenMatrix]; exact hi) := by
  change (if 4 + i = 0 then (encodeFlowInput N).length
    else (encodeFlowInput N).getD (4 + i - 1) 0) = _
  rw [ite_eq_right (by omega), show 4 + i - 1 = i + 3 by omega]
  change (flattenMatrix N.cap).getD i 0 = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some]

private theorem flowInit_mat_eq {n : ℕ} (N : Network (Fin n)) (u v : Fin n) :
    (Memory.State.init (encodeFlowInput N)).mem (4 + u.1 * n + v.1) = N.cap u v := by
  have hlt := idx_lt_sq u.2 v.2
  rw [Nat.add_assoc, flowInit_mem_matrix N hlt, getElem_flattenMatrix]

private theorem flowInit_le {n B : ℕ} {N : Network (Fin n)} (hB : ∀ u v, N.cap u v ≤ B)
    {i : ℕ} (hi : i < n * n) : (Memory.State.init (encodeFlowInput N)).mem (4 + i) ≤ B := by
  have hn : 0 < n := Nat.pos_of_ne_zero fun h => by simp [h] at hi
  have hu : i / n < n := Nat.div_lt_of_lt_mul hi
  have hv : i % n < n := Nat.mod_lt i hn
  have hidx : 4 + i = 4 + (⟨i / n, hu⟩ : Fin n).1 * n + (⟨i % n, hv⟩ : Fin n).1 := by
    dsimp only
    rw [Nat.add_assoc, Nat.div_add_mod']
  rw [hidx, flowInit_mat_eq N]
  exact hB _ _

private theorem inputFits_encodeFlowInput {n B w : ℕ} (N : Network (Fin n))
    (hB : ∀ u v, N.cap u v ≤ B) (hw : Fits w (ekWorkspace n)) (hwB : Fits w (ekBound n B)) :
    InputFits w (encodeFlowInput N) := by
  have hBw : Fits w B := hwB.of_le (by dsimp only [ekBound]; omega)
  refine ⟨hw.of_le ?_, fun x hx => ?_⟩
  · simp only [encodeFlowInput, List.length_cons, length_flattenMatrix, ekWorkspace]
    omega
  · simp only [encodeFlowInput, List.mem_cons] at hx
    rcases hx with rfl | rfl | rfl | hx
    · exact hw.of_le (by dsimp only [ekWorkspace]; omega)
    · exact hw.of_le (by have := N.s.2; dsimp only [ekWorkspace]; omega)
    · exact hw.of_le (by have := N.t.2; dsimp only [ekWorkspace]; omega)
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      rw [length_flattenMatrix] at hi
      rw [← flowInit_mem_matrix N hi]
      exact hBw.of_le (flowInit_le hB hi)

private theorem validHistory_ekFullProg {n B w : ℕ} (N : Network (Fin n))
    (hB : ∀ u v, N.cap u v ≤ B) (hw : Fits w (ekWorkspace n)) (hwB : Fits w (ekBound n B)) :
    (Memory.spec w).ValidHistory (Memory.State.init (encodeFlowInput N))
      ((Memory.spec w).clientHistory (Memory.State.init (encodeFlowInput N)) (ekFullProg ())) := by
  set st := Memory.State.init (encodeFlowInput N)
  have hfr : st.frontier = 4 + n * n := by
    simp only [st, Memory.State.init, encodeFlowInput, List.length_cons, length_flattenMatrix]
    omega
  have hwf : Memory.WellFormed w st :=
    Memory.wellFormed_init (inputFits_encodeFlowInput N hB hw hwB)
      (hw.of_le (by simp only [encodeFlowInput, List.length_cons, length_flattenMatrix,
        ekWorkspace]; omega))
  have h1 : st.mem 1 = n := by simp [st, Memory.State.init, encodeFlowInput]
  have h2 : st.mem 2 = N.s.1 := by simp [st, Memory.State.init, encodeFlowInput]
  have h3 : st.mem 3 = N.t.1 := by simp [st, Memory.State.init, encodeFlowInput]
  unfold ekFullProg
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_read_bind (by omega) ?_
  rw [h1, h2, h3]
  unfold ekFullMain
  dsimp only
  have halloc : (Memory.spec w).ValidHistory st
      ((Memory.spec w).clientHistory st (Memory.alloc (ekScratch n))) :=
    validHistory_alloc (by rw [hfr]; exact hw.of_le (by dsimp only [ekScratch, ekWorkspace]; omega))
  refine validHistory_bind_step halloc ?_
  set st1 := (Memory.spec 0).clientState st (Memory.alloc (ekScratch n))
  have hwf1 : Memory.WellFormed w st1 := wellFormed_clientState hwf halloc
  have hfr1 : ekWorkspace n ≤ st1.frontier := by
    change ekWorkspace n ≤ st.frontier + ekScratch n
    rw [hfr]; dsimp only [ekScratch, ekWorkspace]; omega
  refine validHistory_ite (fun _ => ?_) (fun _ => validHistory_pure _ _ _)
  have hmx : (Memory.spec w).ValidHistory st1
      ((Memory.spec w).clientHistory st1 (iterate ekMaxStep 4 (n * n) (0, 0))) := by
    refine validHistory_iterate_fst (Inv := fun t => Memory.WellFormed w t ∧
        ekWorkspace n ≤ t.frontier) (n * n) 0 0 (fun i hi b t ht => ⟨?_, ?_⟩) ⟨hwf1, hfr1⟩
    · unfold ekMaxStep
      refine validHistory_read_bind (by have := ht.2; dsimp only [ekWorkspace] at this ⊢; omega) ?_
      exact validHistory_ite (fun _ => validHistory_pure _ _ _) (fun _ => validHistory_pure _ _ _)
    · exact clientResult_ekMaxStep_fst _ t
  refine validHistory_bind_step hmx ?_
  rw [ekMaxScan_state]
  have hal : ∀ i < n * n, st1.mem (4 + i) ≤ B := fun i hi =>
    (Memory.mem_step_of_lt_frontier st (.alloc (ekScratch n)) (by rw [hfr]; omega)
      (by simp)).trans_le (flowInit_le hB hi)
  have hM := (ekMaxScan_spec hal).1
  exact validHistory_ekProg
    (c := ⟨n, 4, 4 + n * n,
      ((Memory.spec 0).clientResult st1 (iterate ekMaxStep 4 (n * n) (0, 0))).2⟩)
    ⟨by dsimp only; omega,
      hw.of_le (by dsimp only [ekScratch, ekWorkspace]; omega),
      hwB.of_le (by dsimp only [ekBound]; gcongr)⟩
    N.s.2 N.t.2 hwf1
    (by dsimp only [ekScratch, ekWorkspace] at hfr1 ⊢; omega)

/-- **Dense Edmonds–Karp on the Word-RAM** ([EdmondsKarp1972], Theorem 1; [CLRS2009],
Theorem 26.8): one uniform flat program over `Basis.exact` that, on `encodeFlowInput N` for any
network `N : Network (Fin n)` with `N.s ≠ N.t` and capacities at most `B`, halts within
`C * (n + 1) ^ 5` instructions at every word width fitting `ekWorkspace n` and `ekBound n B`.
This formalizes the dense `O((n + 1) ^ 5)` adjacency-matrix variant rather than the sparse
`O(|V| |E| ^ 2)` adjacency-list bound of [CLRS2009], Theorem 26.8. It returns the maximum flow
value `N.cutCapacity C_cut`, stores a maximum flow `f` at `ekFlowAddr`, and marks the minimum cut
`C_cut = f.reachableCut` at `ekCutAddr < n`. -/
theorem exists_edmondsKarp_program :
    ∃ (R C pc : ℕ), 0 < C ∧ ∃ prog : Program .exact R,
      ∀ {n : ℕ} (N : Network (Fin n)) (B w : ℕ), N.s ≠ N.t →
        (∀ u v, N.cap u v ≤ B) → Fits w (ekWorkspace n) → Fits w (ekBound n B) →
        ∃ (y : Data R) (steps res : ℕ) (f : N.Flow),
          let C_cut : Finset (Fin n) := Finset.univ.filter fun x => y.mem (ekCutAddr n x.1) < n
          Runs w prog (State.init (encodeFlowInput N)) ⟨pc, y⟩ steps ∧
          step w prog ⟨pc, y⟩ = .halt res ∧
          steps + 1 ≤ C * (n + 1) ^ 5 ∧
          (∀ u v : Fin n, y.mem (ekFlowAddr n u.1 v.1) = f u v) ∧
          f.IsMaxFlow ∧ N.IsMinCut C_cut ∧ C_cut = f.reachableCut ∧
          f.value = (N.cutCapacity C_cut : ℤ) ∧ res = N.cutCapacity C_cut := by
  obtain ⟨R, C₀, pc, prog, _, _, hprog⟩ :=
    ekFullProg_realizes.exists_standard_init_program_state_from_words 0
  refine ⟨R, 26 * C₀ + 2, pc, by omega, prog, ?_⟩
  intro n N B w hst hB hw hwB
  set st := Memory.State.init (encodeFlowInput N)
  have hfr : st.frontier = 4 + n * n := by
    simp only [st, Memory.State.init, encodeFlowInput, List.length_cons, length_flattenMatrix]
    omega
  have h1 : st.mem 1 = n := by simp [st, Memory.State.init, encodeFlowInput]
  have h2 : st.mem 2 = N.s.1 := by simp [st, Memory.State.init, encodeFlowInput]
  have h3 : st.mem 3 = N.t.1 := by simp [st, Memory.State.init, encodeFlowInput]
  have hlen : Fits w ((encodeFlowInput N).length + 1) := hw.of_le (by
    simp only [encodeFlowInput, List.length_cons, length_flattenMatrix, ekWorkspace]; omega)
  obtain ⟨y, steps, hruns, hhalt, hmem, _, hbound⟩ :=
    hprog w () (encodeFlowInput N) (fun j => Fin.elim0 j) (Nat.zero_le _) hlen
      (inputFits_encodeFlowInput N hB hw hwB)
      ⟨by rw [h1]; exact hfr, by rw [h1]; exact hw, B,
        by rw [h1]; exact fun i hi => flowInit_le hB hi, by rw [h1]; exact hwB⟩
      (validHistory_ekFullProg N hB hw hwB)
  rw [clientState_width w (ekFullProg ())] at hmem
  rw [clientResult_width w (ekFullProg ())] at hhalt
  set st1 := (Memory.spec 0).clientState st (Memory.alloc (ekScratch n))
  have hmat1 : ∀ u v : Fin n, st1.mem (4 + u.1 * n + v.1) = N.cap u v := fun u v => by
    have hidx := idx_lt_sq u.2 v.2
    exact (Memory.mem_step_of_lt_frontier st (.alloc (ekScratch n)) (by rw [hfr]; omega)
      (by simp)).trans (flowInit_mat_eq N u v)
  have hal : ∀ i < n * n, st1.mem (4 + i) ≤ B := fun i hi =>
    (Memory.mem_step_of_lt_frontier st (.alloc (ekScratch n)) (by rw [hfr]; omega)
      (by simp)).trans_le (flowInit_le hB hi)
  set M := ((Memory.spec 0).clientResult st1 (iterate ekMaxStep 4 (n * n) (0, 0))).2
  have hM_ge : ∀ u v : Fin n, N.cap u v ≤ M := fun u v => by
    have h := (ekMaxScan_spec hal).2 (u.1 * n + v.1) (idx_lt_sq u.2 v.2)
    rw [show 4 + (u.1 * n + v.1) = 4 + u.1 * n + v.1 by omega, hmat1 u v] at h
    exact h
  have hst_ek : (Memory.spec 0).clientState st (ekFullProg ()) =
      (Memory.spec 0).clientState st1 (ekProg (⟨n, 4, 4 + n * n, M⟩, (N.s.1, N.t.1))) := by
    unfold ekFullProg
    rw [clientState_bind_read, clientState_bind_read, clientState_bind_read, h1, h2, h3]
    unfold ekFullMain
    dsimp only
    rw [clientState_bind, ite_eq_left ⟨N.s.2, N.t.2⟩, clientState_bind, ekMaxScan_state]
  have hres_ek : (Memory.spec 0).clientResult st (ekFullProg ()) =
      (Memory.spec 0).clientResult st1 (ekProg (⟨n, 4, 4 + n * n, M⟩, (N.s.1, N.t.1))) := by
    unfold ekFullProg
    rw [clientResult_bind_read, clientResult_bind_read, clientResult_bind_read, h1, h2, h3]
    unfold ekFullMain
    dsimp only
    rw [clientResult_bind, ite_eq_left ⟨N.s.2, N.t.2⟩, clientResult_bind, ekMaxScan_state]
  obtain ⟨_, f, hflow, _, hmax, hmin, hC_eq, hval, hres⟩ :=
    ekProg_flow_spec N hst hM_ge (le_refl (4 + n * n)) hmat1
  have hymem : y.mem =
      ((Memory.spec 0).clientState st1 (ekProg (⟨n, 4, 4 + n * n, M⟩, (N.s.1, N.t.1)))).mem := by
    rw [← hst_ek]
    exact congrArg Memory.State.mem hmem
  have hmc : memoryCost (ekFullProg ()) st ≤ 25 * (n + 1) ^ 5 := by
    have := memoryCost_ekFullProg_le st
    rwa [h1] at this
  have hp : 1 ≤ (n + 1) ^ 5 := Nat.one_le_pow _ _ (Nat.succ_pos n)
  refine ⟨y, steps, (Memory.spec 0).clientResult st (ekFullProg ()), f, hruns, hhalt, ?_,
    ?_, hmax, ?_, ?_, ?_, ?_⟩
  · calc steps + 1
        ≤ C₀ * (memoryCost (ekFullProg ()) st + 0 + 1) + 1 := hbound
      _ ≤ C₀ * (25 * (n + 1) ^ 5 + 1) + 1 :=
          Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) 1
      _ ≤ (26 * C₀ + 2) * (n + 1) ^ 5 := by nlinarith
  · intro u v
    rw [hymem]
    exact hflow u v
  · simpa only [hymem, ekCutAddr, distAddr] using hmin
  · simpa only [hymem, ekCutAddr, distAddr] using hC_eq
  · simpa only [hymem, ekCutAddr, distAddr] using hval
  · rw [hres_ek]
    simpa only [hymem, ekCutAddr, distAddr] using hres

end UniformEK


/-! ### Uniform bipartite matching, König vertex cover, and perfect matching -/

section UniformBipartite

/-- Row-major `0`/`1` encoding of `G : Fin m × Fin r → Bool`. -/
@[expose] def encodeBipartiteMatrix {m r : ℕ} (G : Fin m × Fin r → Bool) : List ℕ :=
  (List.finRange m).flatMap fun u => (List.finRange r).map fun v => if G (u, v) then 1 else 0

/-- Word-RAM input `m :: r :: encodeBipartiteMatrix G`: left count at address `1`, right count at
`2`, and `G (u, v)` (`0` or `1`) at `3 + u * r + v`. -/
@[expose] def encodeBipartiteInput {m r : ℕ} (G : Fin m × Fin r → Bool) : List ℕ :=
  m :: r :: encodeBipartiteMatrix G

private abbrev bmNodes (m r : ℕ) : ℕ := 2 + (m + r)
private abbrev bmMatBase (m r : ℕ) : ℕ := 3 + m * r
private abbrev bmScrBase (m r : ℕ) : ℕ := bmMatBase m r + bmNodes m r * bmNodes m r
private abbrev bmCovLBase (m r : ℕ) : ℕ := bmScrBase m r + ekScratch (bmNodes m r)
private abbrev bmCovRBase (m r : ℕ) : ℕ := bmCovLBase m r + m
private abbrev bmScratch (m r : ℕ) : ℕ :=
  bmNodes m r * bmNodes m r + ekScratch (bmNodes m r) + m + r

/-- Output address of the matching indicator for `(u, v)` (`1` iff `(u, v) ∈ M`). -/
@[expose] def bmMatchAddr (m r u v : ℕ) : ℕ :=
  3 + m * r + (2 + (m + r)) * (2 + (m + r)) + (2 + u) * (2 + (m + r)) + (2 + m + v)

/-- Output address of the König left-cover indicator for `u` (`1` iff `u ∈ C.left`). -/
@[expose] def bmCovLAddr (m r u : ℕ) : ℕ :=
  3 + m * r + 2 * ((2 + (m + r)) * (2 + (m + r))) + 2 * (2 + (m + r)) + u

/-- Output address of the König right-cover indicator for `v` (`1` iff `v ∈ C.right`). -/
@[expose] def bmCovRAddr (m r v : ℕ) : ℕ :=
  3 + m * r + 2 * ((2 + (m + r)) * (2 + (m + r))) + 2 * (2 + (m + r)) + m + v

private abbrev bmWorkspace (m r : ℕ) : ℕ :=
  3 + m * r + 2 * ((2 + (m + r)) * (2 + (m + r))) + 2 * (2 + (m + r)) + m + r

private theorem idx_lt_rect {u v m r : ℕ} (hu : u < m) (hv : v < r) : u * r + v < m * r := by
  have h1 : (u + 1) * r ≤ m * r := Nat.mul_le_mul_right r hu
  rw [Nat.succ_mul] at h1
  omega

private theorem length_encodeBipartiteMatrix {m r : ℕ} (G : Fin m × Fin r → Bool) :
    (encodeBipartiteMatrix G).length = m * r := by
  simp [encodeBipartiteMatrix, List.length_flatMap, List.map_const', List.sum_replicate]

private theorem getElem_encodeBipartiteMatrix {m r : ℕ} (G : Fin m × Fin r → Bool)
    (u : Fin m) (v : Fin r) :
    (encodeBipartiteMatrix G)[u.1 * r + v.1]'(by
      rw [length_encodeBipartiteMatrix]; exact idx_lt_rect u.2 v.2) =
      if G (u, v) then 1 else 0 := by
  have hlen : ∀ x ∈ List.finRange m,
      ((List.finRange r).map fun w => if G (x, w) then 1 else 0).length = r := fun _ _ => by
    simp
  have hq := List.getElem?_flatMap_mul_add (List.finRange m)
    (fun x => (List.finRange r).map fun w => if G (x, w) then 1 else 0) r hlen
    (i := u.1) (j := v.1) (by simp [u.2]) v.2
  have hlt : u.1 * r + v.1 < (encodeBipartiteMatrix G).length := by
    rw [length_encodeBipartiteMatrix]; exact idx_lt_rect u.2 v.2
  have h1 : (encodeBipartiteMatrix G)[u.1 * r + v.1]? = some (if G (u, v) then 1 else 0) := by
    simpa [encodeBipartiteMatrix] using hq
  rw [List.getElem?_eq_getElem hlt] at h1
  exact Option.some.inj h1

private theorem bmInit_mem_edge {m r : ℕ} (G : Fin m × Fin r → Bool) (u : Fin m) (v : Fin r) :
    (Memory.State.init (encodeBipartiteInput G)).mem (3 + u.1 * r + v.1) =
      if G (u, v) then 1 else 0 := by
  have hlt : u.1 * r + v.1 < (encodeBipartiteMatrix G).length := by
    rw [length_encodeBipartiteMatrix]; exact idx_lt_rect u.2 v.2
  change (if 3 + u.1 * r + v.1 = 0 then (encodeBipartiteInput G).length
    else (encodeBipartiteInput G).getD (3 + u.1 * r + v.1 - 1) 0) = _
  rw [ite_eq_right (by omega), show 3 + u.1 * r + v.1 - 1 = (u.1 * r + v.1) + 2 by omega]
  change (encodeBipartiteMatrix G).getD (u.1 * r + v.1) 0 = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
  exact getElem_encodeBipartiteMatrix G u v

private theorem inputFits_encodeBipartiteInput {m r w : ℕ} (G : Fin m × Fin r → Bool)
    (hw : Fits w (bmWorkspace m r)) : InputFits w (encodeBipartiteInput G) := by
  refine ⟨hw.of_le ?_, fun x hx => ?_⟩
  · simp only [encodeBipartiteInput, List.length_cons, length_encodeBipartiteMatrix, bmWorkspace]
    omega
  · simp only [encodeBipartiteInput, List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · exact hw.of_le (by dsimp only [bmWorkspace]; omega)
    · exact hw.of_le (by dsimp only [bmWorkspace]; omega)
    · simp only [encodeBipartiteMatrix, List.mem_flatMap, List.mem_map] at hx
      obtain ⟨_, _, _, _, rfl⟩ := hx
      split_ifs
      · exact hw.of_le (by dsimp only [bmWorkspace]; omega)
      · exact fits_zero w

private def bmSrcStep (d : (ℕ × ℕ) × ℕ) : Memory.Prog ℕ := do
  Memory.write (bmMatBase d.1.1 d.1.2 + (2 + d.2)) 1
  pure (d.2 + 1)

private def bmSnkStep (d : (ℕ × ℕ) × ℕ) : Memory.Prog ℕ := do
  let m := d.1.1
  let r := d.1.2
  Memory.write (bmMatBase m r + (2 + m + d.2) * bmNodes m r + 1) 1
  pure (d.2 + 1)

private def bmEdgeInner (d : ((ℕ × ℕ) × ℕ) × ℕ) : Memory.Prog ℕ := do
  let m := d.1.1.1
  let r := d.1.1.2
  let u := d.1.2
  let v := d.2
  let g ← Memory.read (3 + u * r + v)
  let cap := if g = 0 then 0 else 1
  Memory.write (bmMatBase m r + (2 + u) * bmNodes m r + (2 + m + v)) cap
  pure (v + 1)

private def bmEdgeOuter (d : (ℕ × ℕ) × ℕ) : Memory.Prog ℕ := do
  let _ ← Memory.read 0
  let _ ← iterate bmEdgeInner (d.1, d.2) d.1.2 0
  pure (d.2 + 1)

private def bmCovRStep (d : (ℕ × ℕ) × ℕ) : Memory.Prog ℕ := do
  let m := d.1.1
  let r := d.1.2
  let v := d.2
  let nv := bmNodes m r
  let dv ← Memory.read (bmScrBase m r + nv * nv + (2 + m + v))
  let bit := if dv < nv then 1 else 0
  Memory.write (bmCovRBase m r + v) bit
  pure (v + 1)

private def bmCovLInner (d : ((ℕ × ℕ) × ℕ) × ℕ) : Memory.Prog ℕ := do
  let m := d.1.1.1
  let r := d.1.1.2
  let u := d.1.2
  let v := d.2
  let nv := bmNodes m r
  let g ← Memory.read (3 + u * r + v)
  let dv ← Memory.read (bmScrBase m r + nv * nv + (2 + m + v))
  if g ≠ 0 ∧ dv = nv then
    Memory.write (bmCovLBase m r + u) 1
    pure (v + 1)
  else
    pure (v + 1)

private def bmCovLOuter (d : (ℕ × ℕ) × ℕ) : Memory.Prog ℕ := do
  let m := d.1.1
  let r := d.1.2
  let u := d.2
  let nv := bmNodes m r
  let du ← Memory.read (bmScrBase m r + nv * nv + (2 + u))
  let bit := if du = nv then 1 else 0
  Memory.write (bmCovLBase m r + u) bit
  let _ ← iterate bmCovLInner ((m, r), u) r 0
  pure (u + 1)

private def bmMain (d : ℕ × ℕ) : Memory.Prog ℕ := do
  let m := d.1
  let r := d.2
  let nv := bmNodes m r
  let _ ← Memory.alloc (bmScratch m r)
  fillRange ((bmMatBase m r, 0), nv * nv)
  let _ ← iterate bmSrcStep (m, r) m 0
  let _ ← iterate bmSnkStep (m, r) r 0
  let _ ← iterate bmEdgeOuter (m, r) m 0
  let res ← ekProg (⟨nv, bmMatBase m r, bmScrBase m r, 1⟩, (0, 1))
  let _ ← iterate bmCovRStep (m, r) r 0
  let _ ← iterate bmCovLOuter (m, r) m 0
  pure res

private def bmProg (_ : Unit) : Memory.Prog ℕ := do
  let m ← Memory.read 1
  let r ← Memory.read 2
  bmMain (m, r)

private def pmProg (_ : Unit) : Memory.Prog ℕ := do
  let m ← Memory.read 1
  let r ← Memory.read 2
  let res ← bmMain (m, r)
  if m = r ∧ res = m then pure 1 else pure 0

local macro "bm_omega" : tactic => `(tactic| (
  dsimp -failIfUnchanged only [bmWorkspace, bmScratch, bmCovRAddr, bmCovLAddr, bmMatchAddr,
    bmCovRBase, bmCovLBase, bmScrBase, bmMatBase, bmNodes, ekScratch, ekBound, CtxFits] at *
  first | omega | nlinarith))

private theorem clientResult_bmEdgeInner (d : ((ℕ × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (bmEdgeInner d) = d.2 + 1 :=
  rfl

private theorem clientResult_bmEdgeOuter (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (bmEdgeOuter d) = d.2 + 1 := by
  unfold bmEdgeOuter
  rw [clientResult_bind_read, clientResult_bind, clientResult_pure]

private theorem clientResult_bmCovLInner (d : ((ℕ × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (bmCovLInner d) = d.2 + 1 := by
  unfold bmCovLInner
  rw [clientResult_bind_read, clientResult_bind_read]
  split_ifs <;> simp only [clientResult_bind_write, clientResult_pure]

private theorem clientResult_bmCovLOuter (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (bmCovLOuter d) = d.2 + 1 := by
  unfold bmCovLOuter
  rw [clientResult_bind_read, clientResult_bind_write, clientResult_bind, clientResult_pure]

private theorem bmSrcStep_realizes :
    Realizes .exact bmSrcStep (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (bmWorkspace d.1.1 d.1.2) ∧ d.2 < d.1.1) (fun _ _ => 0) := by
  unfold bmSrcStep
  realize
  all_goals
    obtain ⟨hw, hu⟩ := h
    apply hw.of_le; bm_omega

private theorem bmSnkStep_realizes :
    Realizes .exact bmSnkStep (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (bmWorkspace d.1.1 d.1.2) ∧ d.2 < d.1.2) (fun _ _ => 0) := by
  unfold bmSnkStep
  realize
  all_goals
    obtain ⟨hw, hv⟩ := h
    apply hw.of_le
    have h1 : (2 + d.1.1 + d.2) * (2 + (d.1.1 + d.1.2)) + 1 <
        (2 + (d.1.1 + d.1.2)) * (2 + (d.1.1 + d.1.2)) :=
      idx_lt_sq (by omega) (by omega)
    bm_omega

private theorem bmEdgeInner_realizes :
    Realizes .exact bmEdgeInner (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (bmWorkspace d.1.1.1 d.1.1.2) ∧ d.1.2 < d.1.1.1 ∧ d.2 < d.1.1.2)
      (fun _ _ => 0) := by
  unfold bmEdgeInner
  realize
  all_goals
    obtain ⟨hw, hu, hv⟩ := h
    apply hw.of_le
    have h1 : d.1.2 * d.1.1.2 + d.2 < d.1.1.1 * d.1.1.2 := idx_lt_rect hu hv
    have h2 : (2 + d.1.2) * (2 + (d.1.1.1 + d.1.1.2)) + (2 + d.1.1.1 + d.2) <
        (2 + (d.1.1.1 + d.1.1.2)) * (2 + (d.1.1.1 + d.1.1.2)) :=
      idx_lt_sq (by omega) (by omega)
    bm_omega

private theorem bmEdgeOuter_realizes :
    Realizes .exact bmEdgeOuter (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (bmWorkspace d.1.1 d.1.2) ∧ d.2 < d.1.1) (fun _ _ => 0) := by
  unfold bmEdgeOuter
  realize [bmEdgeInner_realizes]
  all_goals
    obtain ⟨hw, hu⟩ := h
    try (apply hw.of_le; bm_omega)
  refine iterationSafe_of_stepInv _ _ w _ (fun rem (v : ℕ) _ => v + rem = d.1.2) ?_ (Nat.zero_add _)
  intro rem v t hsum
  dsimp only at hsum ⊢
  refine ⟨⟨hw, hu, by omega⟩, ?_⟩
  rw [clientResult_bmEdgeInner]
  dsimp only
  omega

private theorem bmCovRStep_realizes :
    Realizes .exact bmCovRStep (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (bmWorkspace d.1.1 d.1.2) ∧ d.2 < d.1.2) (fun _ _ => 0) := by
  unfold bmCovRStep
  realize
  all_goals
    obtain ⟨hw, hv⟩ := h
    apply hw.of_le; bm_omega

private theorem bmCovLInner_realizes :
    Realizes .exact bmCovLInner (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (bmWorkspace d.1.1.1 d.1.1.2) ∧ d.1.2 < d.1.1.1 ∧ d.2 < d.1.1.2)
      (fun _ _ => 0) := by
  unfold bmCovLInner
  realize
  all_goals
    obtain ⟨hw, hu, hv⟩ := h
    apply hw.of_le
    have h1 : d.1.2 * d.1.1.2 + d.2 < d.1.1.1 * d.1.1.2 := idx_lt_rect hu hv
    bm_omega

private theorem bmCovLOuter_realizes :
    Realizes .exact bmCovLOuter (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (bmWorkspace d.1.1 d.1.2) ∧ d.2 < d.1.1) (fun _ _ => 0) := by
  unfold bmCovLOuter
  realize [bmCovLInner_realizes]
  all_goals
    obtain ⟨hw, hu⟩ := h
    try (apply hw.of_le; bm_omega)
  refine iterationSafe_of_stepInv _ _ w _ (fun rem (v : ℕ) _ => v + rem = d.1.2) ?_ (Nat.zero_add _)
  intro rem v t hsum
  dsimp only at hsum ⊢
  refine ⟨⟨hw, hu, by omega⟩, ?_⟩
  rw [clientResult_bmCovLInner]
  dsimp only
  omega

private theorem bmMain_realizes :
    Realizes .exact bmMain (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (bmWorkspace d.1 d.2) ∧ Fits w (ekBound (2 + (d.1 + d.2)) 1))
      (fun _ _ => 0) := by
  unfold bmMain
  realize [fillRange_realizes, bmSrcStep_realizes, bmSnkStep_realizes, bmEdgeOuter_realizes,
    ekProg_realizes, bmCovRStep_realizes, bmCovLOuter_realizes]
  all_goals
    obtain ⟨hw, hwB⟩ := h
    try (apply hw.of_le; bm_omega)
    try bm_omega
  · refine iterationSafe_of_stepInv _ _ w _ (fun rem (u : ℕ) _ => u + rem = d.1) ?_ (Nat.zero_add _)
    intro rem u t hsum
    dsimp only at hsum ⊢
    refine ⟨⟨hw, by omega⟩, ?_⟩
    change u + 1 + rem = d.1; omega
  · refine iterationSafe_of_stepInv _ _ w _ (fun rem (v : ℕ) _ => v + rem = d.2) ?_ (Nat.zero_add _)
    intro rem v t hsum
    dsimp only at hsum ⊢
    refine ⟨⟨hw, by omega⟩, ?_⟩
    change v + 1 + rem = d.2; omega
  · refine iterationSafe_of_stepInv _ _ w _ (fun rem (u : ℕ) _ => u + rem = d.1) ?_ (Nat.zero_add _)
    intro rem u t hsum
    dsimp only at hsum ⊢
    refine ⟨⟨hw, by omega⟩, ?_⟩
    rw [clientResult_bmEdgeOuter]; dsimp only; omega
  · refine ⟨by bm_omega, hw.of_le (by bm_omega), hwB⟩
  · refine iterationSafe_of_stepInv _ _ w _ (fun rem (v : ℕ) _ => v + rem = d.2) ?_ (Nat.zero_add _)
    intro rem v t hsum
    dsimp only at hsum ⊢
    refine ⟨⟨hw, by omega⟩, ?_⟩
    change v + 1 + rem = d.2; omega
  · refine iterationSafe_of_stepInv _ _ w _ (fun rem (u : ℕ) _ => u + rem = d.1) ?_ (Nat.zero_add _)
    intro rem u t hsum
    dsimp only at hsum ⊢
    refine ⟨⟨hw, by omega⟩, ?_⟩
    rw [clientResult_bmCovLOuter]; dsimp only; omega

private theorem bmProg_realizes :
    Realizes .exact bmProg (WordEncoding.encode (α := Unit)) (WordEncoding.encode (α := ℕ))
      (fun w _ st => Fits w (bmWorkspace (st.mem 1) (st.mem 2)) ∧
        Fits w (ekBound (2 + (st.mem 1 + st.mem 2)) 1)) (fun _ _ => 0) := by
  unfold bmProg
  realize [bmMain_realizes]
  all_goals
    obtain ⟨hw, hwB⟩ := h
    first
    | exact hw.of_le (by bm_omega)
    | exact hwB

private theorem pmProg_realizes :
    Realizes .exact pmProg (WordEncoding.encode (α := Unit)) (WordEncoding.encode (α := ℕ))
      (fun w _ st => Fits w (bmWorkspace (st.mem 1) (st.mem 2)) ∧
        Fits w (ekBound (2 + (st.mem 1 + st.mem 2)) 1)) (fun _ _ => 0) := by
  unfold pmProg
  realize [bmMain_realizes]
  all_goals
    obtain ⟨hw, hwB⟩ := h
    first
    | exact hw.of_le (by bm_omega)
    | exact hwB

private theorem memoryCost_bmMain_le (m r : ℕ) (s : Memory.State) :
    memoryCost (bmMain (m, r)) s ≤ 5200 * (m + r + 1) ^ 5 := by
  unfold bmMain
  dsimp only
  have hsrc : ∀ (u : ℕ) t, memoryCost (bmSrcStep ((m, r), u)) t ≤ 1 := fun _ _ => by
    unfold bmSrcStep; exact le_refl 1
  have hsnk : ∀ (v : ℕ) t, memoryCost (bmSnkStep ((m, r), v)) t ≤ 1 := fun _ _ => by
    unfold bmSnkStep; exact le_refl 1
  have hei : ∀ u v t, memoryCost (bmEdgeInner (((m, r), u), v)) t ≤ 2 := fun _ _ _ => by
    unfold bmEdgeInner
    exact memoryCost_read_bind_le fun _ _ => le_refl 1
  have heo : ∀ (u : ℕ) t, memoryCost (bmEdgeOuter ((m, r), u)) t ≤ 1 + 2 * r := fun u t => by
    unfold bmEdgeOuter
    refine (memoryCost_read_bind_le (k := 2 * r) fun _ t' => ?_).trans (by omega)
    have hit := memoryCost_iterate_le_of bmEdgeInner 2 ((m, r), u) (hei u) r 0 t'
    exact (memoryCost_bind_le (k₂ := 0) hit fun _ _ => le_refl 0).trans (by omega)
  have hcr : ∀ (v : ℕ) t, memoryCost (bmCovRStep ((m, r), v)) t ≤ 2 := fun _ _ => by
    unfold bmCovRStep
    exact memoryCost_read_bind_le fun _ _ => le_refl 1
  have hcli : ∀ u v t, memoryCost (bmCovLInner (((m, r), u), v)) t ≤ 3 := fun _ _ _ => by
    unfold bmCovLInner
    refine (memoryCost_read_bind_le (k := 2) fun _ _ =>
      (memoryCost_read_bind_le (k := 1) fun _ _ =>
        memoryCost_ite_le (memoryCost_write_bind_le fun _ _ => by simp) (by simp)).trans
      (by omega)).trans (by omega)
  have hclo : ∀ (u : ℕ) t, memoryCost (bmCovLOuter ((m, r), u)) t ≤ 2 + 3 * r := fun u t => by
    unfold bmCovLOuter
    refine (memoryCost_read_bind_le (k := 1 + 3 * r) fun _ _ =>
      (memoryCost_write_bind_le (k := 3 * r) fun _ t' => ?_).trans (by omega)).trans (by omega)
    have hit := memoryCost_iterate_le_of bmCovLInner 3 ((m, r), u) (hcli u) r 0 t'
    exact (memoryCost_bind_le (k₂ := 0) hit fun _ _ => le_refl 0).trans (by omega)
  have htot : memoryCost (bmMain (m, r)) s ≤
      (bmScratch m r + 1) + (bmNodes m r * bmNodes m r + (m + (r + ((1 + 2 * r) * m +
        (ekCost (bmNodes m r) + (2 * r + ((2 + 3 * r) * m + 0))))))) := by
    unfold bmMain
    dsimp only
    refine memoryCost_bind_le (memoryCost_alloc _ _).le fun _ t1 => ?_
    refine memoryCost_bind_le (memoryCost_fillRange_le _ _ _ t1) fun _ t2 => ?_
    refine memoryCost_bind_le
      (by simpa [Nat.one_mul] using memoryCost_iterate_le_of bmSrcStep 1 (m, r) hsrc m 0 t2)
      fun _ t3 => ?_
    refine memoryCost_bind_le
      (by simpa [Nat.one_mul] using memoryCost_iterate_le_of bmSnkStep 1 (m, r) hsnk r 0 t3)
      fun _ t4 => ?_
    refine memoryCost_bind_le
      (memoryCost_iterate_le_of bmEdgeOuter (1 + 2 * r) (m, r) heo m 0 t4) fun _ t5 => ?_
    refine memoryCost_bind_le (memoryCost_ekProg_le _ 0 1 t5) fun _ t6 => ?_
    refine memoryCost_bind_le
      (memoryCost_iterate_le_of bmCovRStep 2 (m, r) hcr r 0 t6) fun _ t7 => ?_
    refine memoryCost_bind_le
      (memoryCost_iterate_le_of bmCovLOuter (2 + 3 * r) (m, r) hclo m 0 t7) fun _ _ => by simp
  refine htot.trans ?_
  dsimp only [bmScratch, bmNodes, ekScratch, ekCost]
  set k := m + r + 1
  have hm : m ≤ k := by omega
  have hr : r ≤ k := by omega
  have hnv : 2 + (m + r) + 1 ≤ 3 * k := by omega
  have hpow5 : (2 + (m + r) + 1) ^ 5 ≤ (3 * k) ^ 5 := Nat.pow_le_pow_left hnv 5
  have h35 : (3 * k) ^ 5 = 243 * k ^ 5 := by ring
  have hk2 : k ^ 2 ≤ k ^ 5 := Nat.pow_le_pow_right (by omega) (by decide)
  have hk1 : 1 ≤ k ^ 5 := Nat.one_le_pow _ _ (by omega)
  have hmr : m * r ≤ k ^ 2 := by nlinarith
  have hnv2 : (2 + (m + r)) * (2 + (m + r)) ≤ 9 * k ^ 2 := by nlinarith
  nlinarith

private abbrev BmReady (w m r : ℕ) (s : Memory.State) : Prop :=
  Memory.WellFormed w s ∧ bmWorkspace m r ≤ s.frontier

private theorem validHistory_bmMain {w m r : ℕ} {st : Memory.State}
    (hwf : Memory.WellFormed w st) (hfr : st.frontier = 3 + m * r)
    (hw : Fits w (bmWorkspace m r)) (hwB : Fits w (ekBound (bmNodes m r) 1)) :
    (Memory.spec w).ValidHistory st ((Memory.spec w).clientHistory st (bmMain (m, r))) := by
  unfold bmMain
  dsimp only
  have halloc : (Memory.spec w).ValidHistory st
      ((Memory.spec w).clientHistory st (Memory.alloc (bmScratch m r))) :=
    validHistory_alloc (by rw [hfr]; exact hw.of_le (by bm_omega))
  refine validHistory_bind_step halloc ?_
  set s1 := (Memory.spec 0).clientState st (Memory.alloc (bmScratch m r))
  have hs1 : BmReady w m r s1 :=
    ⟨wellFormed_clientState hwf halloc,
      by change bmWorkspace m r ≤ st.frontier + bmScratch m r; rw [hfr]; bm_omega⟩
  have hfill := validHistory_fillRange (base := bmMatBase m r) (val := 0)
    (len := bmNodes m r * bmNodes m r) hs1.1 (by have := hs1.2; bm_omega) (fits_zero w)
  refine validHistory_bind_step hfill ?_
  set s2 := (Memory.spec 0).clientState s1
    (fillRange ((bmMatBase m r, 0), bmNodes m r * bmNodes m r))
  have hs2 : BmReady w m r s2 := MonotoneMemInv.pres hs1 hfill
  have hsrc : (Memory.spec w).ValidHistory s2
      ((Memory.spec w).clientHistory s2 (iterate bmSrcStep (m, r) m 0)) := by
    refine validHistory_iterate_nat (Inv := BmReady w m r) m 0 (fun u hu t ht => ⟨?_, ?_⟩) hs2
    · unfold bmSrcStep
      exact validHistory_write_bind (by have := ht.2; bm_omega)
        (hw.of_le (by bm_omega)) (validHistory_pure _ _ _)
    · rfl
  refine validHistory_bind_step hsrc ?_
  set s3 := (Memory.spec 0).clientState s2 (iterate bmSrcStep (m, r) m 0)
  have hs3 : BmReady w m r s3 := MonotoneMemInv.pres hs2 hsrc
  have hsnk : (Memory.spec w).ValidHistory s3
      ((Memory.spec w).clientHistory s3 (iterate bmSnkStep (m, r) r 0)) := by
    refine validHistory_iterate_nat (Inv := BmReady w m r) r 0 (fun v hv t ht => ⟨?_, ?_⟩) hs3
    · unfold bmSnkStep
      have h1 : (2 + m + v) * bmNodes m r + 1 < bmNodes m r * bmNodes m r :=
        idx_lt_sq (by dsimp only [bmNodes]; omega) (by dsimp only [bmNodes]; omega)
      exact validHistory_write_bind (by have := ht.2; bm_omega)
        (hw.of_le (by bm_omega)) (validHistory_pure _ _ _)
    · rfl
  refine validHistory_bind_step hsnk ?_
  set s4 := (Memory.spec 0).clientState s3 (iterate bmSnkStep (m, r) r 0)
  have hs4 : BmReady w m r s4 := MonotoneMemInv.pres hs3 hsnk
  have hedge : (Memory.spec w).ValidHistory s4
      ((Memory.spec w).clientHistory s4 (iterate bmEdgeOuter (m, r) m 0)) := by
    refine validHistory_iterate_nat (Inv := BmReady w m r) m 0 (fun u hu t ht => ⟨?_, ?_⟩) hs4
    · unfold bmEdgeOuter
      refine validHistory_read_bind (by have := ht.2; bm_omega) ?_
      refine validHistory_bind_step
        (validHistory_iterate_nat (Inv := BmReady w m r) r 0 (fun v hv t' ht' => ⟨?_, ?_⟩) ht)
        (validHistory_pure _ _ _)
      · unfold bmEdgeInner
        have h1 : u * r + v < m * r := idx_lt_rect (by omega) (by omega)
        have h2 : (2 + u) * bmNodes m r + (2 + m + v) < bmNodes m r * bmNodes m r :=
          idx_lt_sq (by dsimp only [bmNodes]; omega) (by dsimp only [bmNodes]; omega)
        refine validHistory_read_bind (by have := ht'.2; bm_omega) ?_
        exact validHistory_write_bind (by have := ht'.2; bm_omega)
          (hw.of_le (by split_ifs <;> bm_omega)) (validHistory_pure _ _ _)
      · exact clientResult_bmEdgeInner _ t'
    · exact clientResult_bmEdgeOuter _ t
  refine validHistory_bind_step hedge ?_
  set s5 := (Memory.spec 0).clientState s4 (iterate bmEdgeOuter (m, r) m 0)
  have hs5 : BmReady w m r s5 := MonotoneMemInv.pres hs4 hedge
  have hek := validHistory_ekProg (c := ⟨bmNodes m r, bmMatBase m r, bmScrBase m r, 1⟩)
    (src := 0) (snk := 1) ⟨by bm_omega, hw.of_le (by bm_omega), hwB⟩
    (by bm_omega) (by bm_omega) hs5.1 (by have := hs5.2; bm_omega)
  refine validHistory_bind_step hek ?_
  set s6 := (Memory.spec 0).clientState s5
    (ekProg (⟨bmNodes m r, bmMatBase m r, bmScrBase m r, 1⟩, (0, 1)))
  have hs6 : BmReady w m r s6 := MonotoneMemInv.pres hs5 hek
  have hcr : (Memory.spec w).ValidHistory s6
      ((Memory.spec w).clientHistory s6 (iterate bmCovRStep (m, r) r 0)) := by
    refine validHistory_iterate_nat (Inv := BmReady w m r) r 0 (fun v hv t ht => ⟨?_, ?_⟩) hs6
    · unfold bmCovRStep
      refine validHistory_read_bind (by have := ht.2; bm_omega) ?_
      exact validHistory_write_bind (by have := ht.2; bm_omega)
        (hw.of_le (by split_ifs <;> bm_omega)) (validHistory_pure _ _ _)
    · rfl
  refine validHistory_bind_step hcr ?_
  set s7 := (Memory.spec 0).clientState s6 (iterate bmCovRStep (m, r) r 0)
  have hs7 : BmReady w m r s7 := MonotoneMemInv.pres hs6 hcr
  have hcl : (Memory.spec w).ValidHistory s7
      ((Memory.spec w).clientHistory s7 (iterate bmCovLOuter (m, r) m 0)) := by
    refine validHistory_iterate_nat (Inv := BmReady w m r) m 0 (fun u hu t ht => ⟨?_, ?_⟩) hs7
    · unfold bmCovLOuter
      refine validHistory_read_bind (by have := ht.2; bm_omega) ?_
      have hw0 : (Memory.spec w).ValidHistory t
          ((Memory.spec w).clientHistory t (Memory.write (bmCovLBase m r + u)
            (if t.mem (bmScrBase m r + bmNodes m r * bmNodes m r + (2 + u)) = bmNodes m r
             then 1 else 0))) :=
        validHistory_write (by have := ht.2; bm_omega) (hw.of_le (by split_ifs <;> bm_omega))
      refine validHistory_bind_step hw0 ?_
      have ht1 := MonotoneMemInv.pres ht hw0
      refine validHistory_bind_step
        (validHistory_iterate_nat (Inv := BmReady w m r) r 0 (fun v hv t' ht' => ⟨?_, ?_⟩) ht1)
        (validHistory_pure _ _ _)
      · unfold bmCovLInner
        have h1 : u * r + v < m * r := idx_lt_rect (by omega) (by omega)
        refine validHistory_read_bind (by have := ht'.2; bm_omega) ?_
        refine validHistory_read_bind (by have := ht'.2; bm_omega) ?_
        refine validHistory_ite (fun _ => ?_) (fun _ => validHistory_pure _ _ _)
        exact validHistory_write_bind (by have := ht'.2; bm_omega)
          (hw.of_le (by bm_omega)) (validHistory_pure _ _ _)
      · exact clientResult_bmCovLInner _ t'
    · exact clientResult_bmCovLOuter _ t
  exact validHistory_bind_step hcl (validHistory_pure _ _ _)

private theorem bipartiteFinEquiv_val {m r : ℕ} :
    (bipartiteFinEquiv m r .source).1 = 0 ∧
    (bipartiteFinEquiv m r .sink).1 = 1 ∧
    (∀ u : Fin m, (bipartiteFinEquiv m r (.left u)).1 = 2 + u.1) ∧
    (∀ v : Fin r, (bipartiteFinEquiv m r (.right v)).1 = 2 + m + v.1) := by
  refine ⟨rfl, rfl, fun u => ?_, fun v => ?_⟩
  · simp [bipartiteFinEquiv, bipartiteVertexEquiv]
  · simp [bipartiteFinEquiv, bipartiteVertexEquiv]; omega

private theorem bmBuild_spec {m r : ℕ} (G : Fin m × Fin r → Bool) {st : Memory.State}
    (hG : ∀ u : Fin m, ∀ v : Fin r, st.mem (3 + u.1 * r + v.1) = if G (u, v) then 1 else 0) :
    let st1 := (Memory.spec 0).clientState st
      (fillRange ((bmMatBase m r, 0), bmNodes m r * bmNodes m r))
    let st2 := (Memory.spec 0).clientState st1 (iterate bmSrcStep (m, r) m 0)
    let st3 := (Memory.spec 0).clientState st2 (iterate bmSnkStep (m, r) r 0)
    let st4 := (Memory.spec 0).clientState st3 (iterate bmEdgeOuter (m, r) m 0)
    (∀ u : Fin m, ∀ v : Fin r, st4.mem (3 + u.1 * r + v.1) = if G (u, v) then 1 else 0) ∧
      ∀ x y : Fin (bmNodes m r),
        st4.mem (bmMatBase m r + x.1 * bmNodes m r + y.1) = (bipartiteFinNetwork G).cap x y := by
  intro st1 st2 st3 st4
  have h1 := fillRange_spec (bmMatBase m r) 0 (bmNodes m r * bmNodes m r) st
  have hG1 : ∀ u : Fin m, ∀ v : Fin r, st1.mem (3 + u.1 * r + v.1) = if G (u, v) then 1 else 0 := by
    intro u v
    have hlt : u.1 * r + v.1 < m * r := idx_lt_rect u.2 v.2
    rw [h1.2 _ (Or.inl (by dsimp only [bmMatBase]; omega))]
    exact hG u v
  have hM1 : ∀ a < bmNodes m r * bmNodes m r, st1.mem (bmMatBase m r + a) = 0 := h1.1
  have h2 := iterate_invariant_of bmSrcStep (m, r)
    (fun rem (k : ℕ) t => k + rem = m ∧
      (∀ a < bmMatBase m r, t.mem a = st1.mem a) ∧
      (∀ x y : Fin (bmNodes m r), t.mem (bmMatBase m r + x.1 * bmNodes m r + y.1) =
        if x.1 = 0 ∧ 2 ≤ y.1 ∧ y.1 < 2 + k then 1 else 0))
    (fun rem k t ⟨hsum, hlo, hmat⟩ => by
      unfold bmSrcStep
      rw [clientResult_bind_write, clientState_bind_write, clientResult_pure, clientState_pure]
      dsimp only
      refine ⟨by omega, fun a ha => ?_, fun x y => ?_⟩
      · rw [Function.update_of_ne (by omega)]; exact hlo a ha
      · by_cases heq : bmMatBase m r + x.1 * bmNodes m r + y.1 = bmMatBase m r + (2 + k)
        · rw [heq, Function.update_self]
          have hxy := fin_mul_add_inj (M := bmNodes m r) (x₁ := x) (y₁ := y)
            (x₂ := ⟨0, by dsimp only [bmNodes]; omega⟩)
            (y₂ := ⟨2 + k, by dsimp only [bmNodes]; omega⟩) (by dsimp only; omega)
          have hx0 : x.1 = 0 := congrArg Fin.val hxy.1
          have hyk : y.1 = 2 + k := congrArg Fin.val hxy.2
          rw [ite_eq_left (by omega)]
        · rw [Function.update_of_ne heq, hmat x y]
          by_cases hcond : x.1 = 0 ∧ 2 ≤ y.1 ∧ y.1 < 2 + k
          · rw [ite_eq_left hcond, ite_eq_left (by omega)]
          · rw [ite_eq_right hcond, ite_eq_right]
            intro ⟨hx0, hy2, hylt⟩
            apply hcond
            refine ⟨hx0, hy2, ?_⟩
            by_cases hyk : y.1 = 2 + k
            · exfalso; apply heq; rw [hx0, hyk]; simp
            · omega)
    (n := m) (a := 0) (s := st1) ⟨Nat.zero_add _, fun _ _ => rfl, fun x y => by
      rw [ite_eq_right (by omega), Nat.add_assoc]
      exact hM1 _ (idx_lt_sq x.2 y.2)⟩
  have h2r : (Memory.spec 0).clientResult st1 (iterate bmSrcStep (m, r) m 0) = m := by
    have := h2.1; omega
  have h3 := iterate_invariant_of bmSnkStep (m, r)
    (fun rem (k : ℕ) t => k + rem = r ∧
      (∀ a < bmMatBase m r, t.mem a = st1.mem a) ∧
      (∀ x y : Fin (bmNodes m r), t.mem (bmMatBase m r + x.1 * bmNodes m r + y.1) =
        if (x.1 = 0 ∧ 2 ≤ y.1 ∧ y.1 < 2 + m) ∨
           (2 + m ≤ x.1 ∧ x.1 < 2 + m + k ∧ y.1 = 1) then 1 else 0))
    (fun rem k t ⟨hsum, hlo, hmat⟩ => by
      unfold bmSnkStep
      rw [clientResult_bind_write, clientState_bind_write, clientResult_pure, clientState_pure]
      dsimp only
      refine ⟨by omega, fun a ha => ?_, fun x y => ?_⟩
      · rw [Function.update_of_ne (by omega)]; exact hlo a ha
      · by_cases heq : bmMatBase m r + x.1 * bmNodes m r + y.1 =
            bmMatBase m r + (2 + m + k) * bmNodes m r + 1
        · rw [heq, Function.update_self]
          have hxy := fin_mul_add_inj (M := bmNodes m r) (x₁ := x) (y₁ := y)
            (x₂ := ⟨2 + m + k, by dsimp only [bmNodes]; omega⟩)
            (y₂ := ⟨1, by dsimp only [bmNodes]; omega⟩) (by dsimp only; omega)
          have hxk : x.1 = 2 + m + k := congrArg Fin.val hxy.1
          have hy1 : y.1 = 1 := congrArg Fin.val hxy.2
          rw [ite_eq_left (Or.inr (by omega))]
        · rw [Function.update_of_ne heq, hmat x y]
          by_cases hcond : (x.1 = 0 ∧ 2 ≤ y.1 ∧ y.1 < 2 + m) ∨
              (2 + m ≤ x.1 ∧ x.1 < 2 + m + k ∧ y.1 = 1)
          · rw [ite_eq_left hcond, ite_eq_left (hcond.imp id (by omega))]
          · rw [ite_eq_right hcond, ite_eq_right]
            intro hnew
            rcases hnew with hL | ⟨h1, h2, hy1⟩
            · exact hcond (Or.inl hL)
            · apply hcond; right
              by_cases hxk : x.1 = 2 + m + k
              · exfalso; apply heq; rw [hxk, hy1]
              · omega)
    (n := r) (a := 0) (s := st2) ⟨Nat.zero_add _, h2.2.1, fun x y => by
      have := h2.2.2 x y
      rw [h2r] at this
      rw [this]
      by_cases hp : x.1 = 0 ∧ 2 ≤ y.1 ∧ y.1 < 2 + m
      · rw [ite_eq_left hp, ite_eq_left (Or.inl hp)]
      · rw [ite_eq_right hp, ite_eq_right (by omega)]⟩
  have h3r : (Memory.spec 0).clientResult st2 (iterate bmSnkStep (m, r) r 0) = r := by
    have := h3.1; omega
  have h4 := iterate_invariant_of bmEdgeOuter (m, r)
    (fun rem (ku : ℕ) t => ku + rem = m ∧
      (∀ a < bmMatBase m r, t.mem a = st1.mem a) ∧
      (∀ x y : Fin (bmNodes m r), t.mem (bmMatBase m r + x.1 * bmNodes m r + y.1) =
        if (x.1 = 0 ∧ 2 ≤ y.1 ∧ y.1 < 2 + m) ∨
           (2 + m ≤ x.1 ∧ x.1 < 2 + m + r ∧ y.1 = 1) then 1
        else if hx : 2 ≤ x.1 ∧ x.1 < 2 + ku ∧ x.1 < 2 + m then
          if hy : 2 + m ≤ y.1 ∧ y.1 < 2 + m + r then
            if G (⟨x.1 - 2, by omega⟩, ⟨y.1 - (2 + m), by omega⟩) then 1 else 0
          else 0
        else 0))
    (fun rem ku t ⟨hsum, hlo, hmat⟩ => by
      have hku : ku < m := by omega
      have hinner := iterate_invariant_of bmEdgeInner ((m, r), ku)
        (fun remv (kv : ℕ) t' => kv + remv = r ∧
          (∀ a < bmMatBase m r, t'.mem a = st1.mem a) ∧
          (∀ x y : Fin (bmNodes m r), t'.mem (bmMatBase m r + x.1 * bmNodes m r + y.1) =
            if (x.1 = 0 ∧ 2 ≤ y.1 ∧ y.1 < 2 + m) ∨
               (2 + m ≤ x.1 ∧ x.1 < 2 + m + r ∧ y.1 = 1) then 1
            else if hx : 2 ≤ x.1 ∧ x.1 < 2 + ku ∧ x.1 < 2 + m then
              if hy : 2 + m ≤ y.1 ∧ y.1 < 2 + m + r then
                if G (⟨x.1 - 2, by omega⟩, ⟨y.1 - (2 + m), by omega⟩) then 1 else 0
              else 0
            else if hx' : x.1 = 2 + ku ∧ 2 + m ≤ y.1 ∧ y.1 < 2 + m + kv ∧ y.1 < 2 + m + r then
              if G (⟨ku, hku⟩, ⟨y.1 - (2 + m), by omega⟩) then 1 else 0
            else 0))
        (fun remv kv t' ⟨hsumv, hlo', hmat'⟩ => by
          have hkv : kv < r := by omega
          have hgread : t'.mem (3 + ku * r + kv) = if G (⟨ku, hku⟩, ⟨kv, hkv⟩) then 1 else 0 := by
            have hlt : ku * r + kv < m * r := idx_lt_rect hku hkv
            rw [hlo' _ (by dsimp only [bmMatBase]; omega)]
            exact hG1 ⟨ku, hku⟩ ⟨kv, hkv⟩
          unfold bmEdgeInner
          rw [clientResult_bind_read, clientState_bind_read, clientResult_bind_write,
            clientState_bind_write, clientResult_pure, clientState_pure]
          dsimp only
          refine ⟨by omega, fun a ha => ?_, fun x y => ?_⟩
          · rw [Function.update_of_ne (by omega)]; exact hlo' a ha
          · by_cases heq : bmMatBase m r + x.1 * bmNodes m r + y.1 =
                bmMatBase m r + (2 + ku) * bmNodes m r + (2 + m + kv)
            · rw [heq, Function.update_self, hgread]
              have hxy := fin_mul_add_inj (M := bmNodes m r) (x₁ := x) (y₁ := y)
                (x₂ := ⟨2 + ku, by dsimp only [bmNodes]; omega⟩)
                (y₂ := ⟨2 + m + kv, by dsimp only [bmNodes]; omega⟩) (by dsimp only; omega)
              have hxu : x.1 = 2 + ku := congrArg Fin.val hxy.1
              have hyv : y.1 = 2 + m + kv := congrArg Fin.val hxy.2
              have h1 : ¬ ((x.1 = 0 ∧ 2 ≤ y.1 ∧ y.1 < 2 + m) ∨
                  (2 + m ≤ x.1 ∧ x.1 < 2 + m + r ∧ y.1 = 1)) := by omega
              have h2 : ¬ (2 ≤ x.1 ∧ x.1 < 2 + ku ∧ x.1 < 2 + m) := by omega
              have h3 : x.1 = 2 + ku ∧ 2 + m ≤ y.1 ∧ y.1 < 2 + m + (kv + 1) ∧ y.1 < 2 + m + r :=
                by omega
              rw [ite_eq_right h1, dite_eq_right h2, dite_eq_left h3]
              have hfin : (⟨y.1 - (2 + m), by omega⟩ : Fin r) = ⟨kv, hkv⟩ :=
                Fin.ext (by dsimp only; omega)
              rw [hfin]
              cases G (⟨ku, hku⟩, ⟨kv, hkv⟩) <;> rfl
            · rw [Function.update_of_ne heq, hmat' x y]
              by_cases h1 : (x.1 = 0 ∧ 2 ≤ y.1 ∧ y.1 < 2 + m) ∨
                  (2 + m ≤ x.1 ∧ x.1 < 2 + m + r ∧ y.1 = 1)
              · rw [ite_eq_left h1, ite_eq_left h1]
              · rw [ite_eq_right h1, ite_eq_right h1]
                by_cases h2 : 2 ≤ x.1 ∧ x.1 < 2 + ku ∧ x.1 < 2 + m
                · rw [dite_eq_left h2, dite_eq_left h2]
                · rw [dite_eq_right h2, dite_eq_right h2]
                  by_cases h3 : x.1 = 2 + ku ∧ 2 + m ≤ y.1 ∧ y.1 < 2 + m + kv ∧ y.1 < 2 + m + r
                  · rw [dite_eq_left h3, dite_eq_left (by omega)]
                  · rw [dite_eq_right h3, dite_eq_right]
                    intro ⟨hxu, hy1, hy2, hy3⟩
                    apply h3; refine ⟨hxu, hy1, ?_, hy3⟩
                    by_cases hyv : y.1 = 2 + m + kv
                    · exfalso; apply heq; rw [hxu, hyv]
                    · omega)
        (n := r) (a := 0) (s := t) ⟨Nat.zero_add _, hlo, fun x y => by
          rw [hmat x y]
          by_cases h1 : (x.1 = 0 ∧ 2 ≤ y.1 ∧ y.1 < 2 + m) ∨
              (2 + m ≤ x.1 ∧ x.1 < 2 + m + r ∧ y.1 = 1)
          · rw [ite_eq_left h1, ite_eq_left h1]
          · rw [ite_eq_right h1, ite_eq_right h1]
            by_cases h2 : 2 ≤ x.1 ∧ x.1 < 2 + ku ∧ x.1 < 2 + m
            · rw [dite_eq_left h2, dite_eq_left h2]
            · rw [dite_eq_right h2, dite_eq_right h2, dite_eq_right (by omega)]⟩
      have hinner_r :
          (Memory.spec 0).clientResult t (iterate bmEdgeInner ((m, r), ku) r 0) = r := by
        have := hinner.1; omega
      unfold bmEdgeOuter
      rw [clientResult_bind_read, clientResult_bind, clientResult_pure,
        clientState_bind_read, clientState_bind, clientState_pure]
      refine ⟨by omega, hinner.2.1, fun x y => ?_⟩
      dsimp only
      have hmat_i := hinner.2.2 x y
      rw [hinner_r] at hmat_i
      rw [hmat_i]
      by_cases h1 : (x.1 = 0 ∧ 2 ≤ y.1 ∧ y.1 < 2 + m) ∨
          (2 + m ≤ x.1 ∧ x.1 < 2 + m + r ∧ y.1 = 1)
      · rw [ite_eq_left h1, ite_eq_left h1]
      · rw [ite_eq_right h1, ite_eq_right h1]
        by_cases h2 : 2 ≤ x.1 ∧ x.1 < 2 + ku ∧ x.1 < 2 + m
        · rw [dite_eq_left h2,
            dite_eq_left (by omega : 2 ≤ x.1 ∧ x.1 < 2 + (ku + 1) ∧ x.1 < 2 + m)]
        · rw [dite_eq_right h2]
          by_cases hxu : x.1 = 2 + ku
          · rw [dite_eq_left (by omega : 2 ≤ x.1 ∧ x.1 < 2 + (ku + 1) ∧ x.1 < 2 + m)]
            by_cases hy : 2 + m ≤ y.1 ∧ y.1 < 2 + m + r
            · rw [dite_eq_left ⟨hxu, hy.1, hy.2, hy.2⟩, dite_eq_left hy]
              have hfin : (⟨x.1 - 2, by omega⟩ : Fin m) = ⟨ku, hku⟩ :=
                Fin.ext (by dsimp only; omega)
              rw [hfin]
            · rw [dite_eq_right (fun h => hy ⟨h.2.1, h.2.2.1⟩), dite_eq_right hy]
          · rw [dite_eq_right (by omega), dite_eq_right (by omega)])
    (n := m) (a := 0) (s := st3) ⟨Nat.zero_add _, h3.2.1, fun x y => by
      have := h3.2.2 x y
      rw [h3r] at this
      rw [this]
      by_cases h1 : (x.1 = 0 ∧ 2 ≤ y.1 ∧ y.1 < 2 + m) ∨
          (2 + m ≤ x.1 ∧ x.1 < 2 + m + r ∧ y.1 = 1)
      · rw [ite_eq_left h1, ite_eq_left h1]
      · rw [ite_eq_right h1, ite_eq_right h1, dite_eq_right (by omega)]⟩
  have h4r : (Memory.spec 0).clientResult st3 (iterate bmEdgeOuter (m, r) m 0) = m := by
    have := h4.1; omega
  refine ⟨fun u v => ?_, fun x y => ?_⟩
  · have hlt : u.1 * r + v.1 < m * r := idx_lt_rect u.2 v.2
    rw [h4.2.1 _ (by dsimp only [bmMatBase]; omega)]
    exact hG1 u v
  · have hm4 := h4.2.2 x y
    rw [h4r] at hm4
    rw [hm4]
    obtain ⟨hsrc0, hsnk1, hleft, hright⟩ := bipartiteFinEquiv_val (m := m) (r := r)
    have hx_eq : x = bipartiteFinEquiv m r ((bipartiteFinEquiv m r).symm x) :=
      ((bipartiteFinEquiv m r).apply_symm_apply x).symm
    have hy_eq : y = bipartiteFinEquiv m r ((bipartiteFinEquiv m r).symm y) :=
      ((bipartiteFinEquiv m r).apply_symm_apply y).symm
    change _ = (bipartiteNetwork G).cap ((bipartiteFinEquiv m r).symm x)
        ((bipartiteFinEquiv m r).symm y)
    generalize hbx : (bipartiteFinEquiv m r).symm x = bx at hx_eq
    generalize hby : (bipartiteFinEquiv m r).symm y = by_ at hy_eq
    have hxval : x.1 = (bipartiteFinEquiv m r bx).1 := congrArg Fin.val hx_eq
    have hyval : y.1 = (bipartiteFinEquiv m r by_).1 := congrArg Fin.val hy_eq
    cases bx <;> cases by_ <;>
      simp only [hsrc0, hsnk1, hleft, hright, bipartiteNetwork] at hxval hyval ⊢
    all_goals
      try (rw [ite_eq_left]; omega)
      try (rw [ite_eq_right (by omega), dite_eq_right (by omega)])
      try (rw [ite_eq_right (by omega), dite_eq_left (by omega), dite_eq_right (by omega)])
    -- Remaining case: left u, right v
    rename_i u v
    have h1 : ¬ ((x.1 = 0 ∧ 2 ≤ y.1 ∧ y.1 < 2 + m) ∨
        (2 + m ≤ x.1 ∧ x.1 < 2 + m + r ∧ y.1 = 1)) := by omega
    have h2 : 2 ≤ x.1 ∧ x.1 < 2 + m ∧ x.1 < 2 + m := by have := u.2; omega
    have h3 : 2 + m ≤ y.1 ∧ y.1 < 2 + m + r := by have := v.2; omega
    rw [ite_eq_right h1, dite_eq_left h2, dite_eq_left h3]
    have hu : (⟨x.1 - 2, by omega⟩ : Fin m) = u := Fin.ext (by dsimp only; omega)
    have hv : (⟨y.1 - (2 + m), by omega⟩ : Fin r) = v := Fin.ext (by dsimp only; omega)
    rw [hu, hv]

private theorem bmCovR_spec {m r : ℕ} (st : Memory.State) :
    let st' := (Memory.spec 0).clientState st (iterate bmCovRStep (m, r) r 0)
    (∀ a < bmCovRBase m r, st'.mem a = st.mem a) ∧
      (∀ v : Fin r, st'.mem (bmCovRBase m r + v.1) =
        if st.mem (bmScrBase m r + bmNodes m r * bmNodes m r + (2 + m + v.1)) < bmNodes m r
        then 1 else 0) := by
  have h := iterate_invariant_of bmCovRStep (m, r)
    (fun rem (k : ℕ) t => k + rem = r ∧
      (∀ a < bmCovRBase m r, t.mem a = st.mem a) ∧
      (∀ v : Fin r, v.1 < k → t.mem (bmCovRBase m r + v.1) =
        if st.mem (bmScrBase m r + bmNodes m r * bmNodes m r + (2 + m + v.1)) < bmNodes m r
        then 1 else 0))
    (fun rem k t ⟨hsum, hlo, hcov⟩ => by
      unfold bmCovRStep
      rw [clientResult_bind_read, clientState_bind_read, clientResult_bind_write,
        clientState_bind_write, clientResult_pure, clientState_pure]
      dsimp only
      have hread : t.mem (bmScrBase m r + bmNodes m r * bmNodes m r + (2 + m + k)) =
          st.mem (bmScrBase m r + bmNodes m r * bmNodes m r + (2 + m + k)) :=
        hlo _ (by bm_omega)
      refine ⟨by omega, fun a ha => ?_, fun v hv => ?_⟩
      · rw [Function.update_of_ne (by omega)]; exact hlo a ha
      · by_cases hvk : v.1 = k
        · rw [hvk, Function.update_self, hread]
        · rw [Function.update_of_ne (by omega)]; exact hcov v (by omega))
    (n := r) (a := 0) (s := st)
      ⟨Nat.zero_add _, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  exact ⟨h.2.1, fun v => h.2.2 v (by omega)⟩

private theorem bmCovL_spec {m r : ℕ} (G : Fin m × Fin r → Bool) {st : Memory.State}
    (hG : ∀ u : Fin m, ∀ v : Fin r, st.mem (3 + u.1 * r + v.1) = if G (u, v) then 1 else 0) :
    let st' := (Memory.spec 0).clientState st (iterate bmCovLOuter (m, r) m 0)
    (∀ a, (a < bmCovLBase m r ∨ bmCovRBase m r ≤ a) → st'.mem a = st.mem a) ∧
      (∀ u : Fin m, st'.mem (bmCovLBase m r + u.1) =
        if st.mem (bmScrBase m r + bmNodes m r * bmNodes m r + (2 + u.1)) = bmNodes m r ∨
           ∃ v : Fin r, G (u, v) = true ∧
             st.mem (bmScrBase m r + bmNodes m r * bmNodes m r + (2 + m + v.1)) = bmNodes m r
        then 1 else 0) := by
  have h := iterate_invariant_of bmCovLOuter (m, r)
    (fun rem (ku : ℕ) t => ku + rem = m ∧
      (∀ a, (a < bmCovLBase m r ∨ bmCovRBase m r ≤ a) → t.mem a = st.mem a) ∧
      (∀ u : Fin m, u.1 < ku → t.mem (bmCovLBase m r + u.1) =
        if st.mem (bmScrBase m r + bmNodes m r * bmNodes m r + (2 + u.1)) = bmNodes m r ∨
           ∃ v : Fin r, G (u, v) = true ∧
             st.mem (bmScrBase m r + bmNodes m r * bmNodes m r + (2 + m + v.1)) = bmNodes m r
        then 1 else 0))
    (fun rem ku t ⟨hsum, hfr, hcov⟩ => by
      have hku : ku < m := by omega
      have hdu : t.mem (bmScrBase m r + bmNodes m r * bmNodes m r + (2 + ku)) =
          st.mem (bmScrBase m r + bmNodes m r * bmNodes m r + (2 + ku)) :=
        hfr _ (Or.inl (by bm_omega))
      set t1 : Memory.State := ⟨Function.update t.mem (bmCovLBase m r + ku)
        (if t.mem (bmScrBase m r + bmNodes m r * bmNodes m r + (2 + ku)) = bmNodes m r
         then 1 else 0), t.frontier⟩
      have hinner := iterate_invariant_of bmCovLInner ((m, r), ku)
        (fun remv (kv : ℕ) t' => kv + remv = r ∧
          (∀ a, a ≠ bmCovLBase m r + ku → t'.mem a = t.mem a) ∧
          t'.mem (bmCovLBase m r + ku) =
            if st.mem (bmScrBase m r + bmNodes m r * bmNodes m r + (2 + ku)) = bmNodes m r ∨
               ∃ v : Fin r, v.1 < kv ∧ G (⟨ku, hku⟩, v) = true ∧
                 st.mem (bmScrBase m r + bmNodes m r * bmNodes m r + (2 + m + v.1)) = bmNodes m r
            then 1 else 0)
        (fun remv kv t' ⟨hsumv, hne, hcur⟩ => by
          have hkv : kv < r := by omega
          have hlt : ku * r + kv < m * r := idx_lt_rect hku hkv
          have hg : t'.mem (3 + ku * r + kv) = if G (⟨ku, hku⟩, ⟨kv, hkv⟩) then 1 else 0 := by
            rw [hne _ (by bm_omega), hfr _ (Or.inl (by bm_omega))]
            exact hG ⟨ku, hku⟩ ⟨kv, hkv⟩
          have hdv : t'.mem (bmScrBase m r + bmNodes m r * bmNodes m r + (2 + m + kv)) =
              st.mem (bmScrBase m r + bmNodes m r * bmNodes m r + (2 + m + kv)) := by
            rw [hne _ (by bm_omega), hfr _ (Or.inl (by bm_omega))]
          unfold bmCovLInner
          rw [clientResult_bind_read, clientResult_bind_read, clientState_bind_read,
            clientState_bind_read, hg, hdv]
          by_cases hcond : (if G (⟨ku, hku⟩, ⟨kv, hkv⟩) = true then 1 else 0) ≠ 0 ∧
              st.mem (bmScrBase m r + bmNodes m r * bmNodes m r + (2 + m + kv)) = bmNodes m r
          · rw [ite_eq_left hcond, clientResult_bind_write, clientResult_pure,
              clientState_bind_write, clientState_pure]
            have hGkv : G (⟨ku, hku⟩, ⟨kv, hkv⟩) = true := by
              cases hb : G (⟨ku, hku⟩, ⟨kv, hkv⟩)
              · simp [hb] at hcond
              · rfl
            refine ⟨by omega, fun a ha => ?_, ?_⟩
            · dsimp only; rw [Function.update_of_ne ha]; exact hne a ha
            · dsimp only; rw [Function.update_self, ite_eq_left]
              exact Or.inr ⟨⟨kv, hkv⟩, by dsimp only; omega, hGkv, hcond.2⟩
          · rw [ite_eq_right hcond, clientResult_pure, clientState_pure]
            refine ⟨by omega, hne, ?_⟩
            rw [hcur]
            have hiff :
                (st.mem (bmScrBase m r + bmNodes m r * bmNodes m r + (2 + ku)) = bmNodes m r ∨
                  ∃ v : Fin r, v.1 < kv ∧ G (⟨ku, hku⟩, v) = true ∧
                    st.mem (bmScrBase m r + bmNodes m r * bmNodes m r + (2 + m + v.1)) =
                      bmNodes m r) ↔
                (st.mem (bmScrBase m r + bmNodes m r * bmNodes m r + (2 + ku)) = bmNodes m r ∨
                  ∃ v : Fin r, v.1 < kv + 1 ∧ G (⟨ku, hku⟩, v) = true ∧
                    st.mem (bmScrBase m r + bmNodes m r * bmNodes m r + (2 + m + v.1)) =
                      bmNodes m r) := by
              constructor
              · rintro (h | ⟨v, hv, h1, h2⟩)
                · exact Or.inl h
                · exact Or.inr ⟨v, by omega, h1, h2⟩
              · rintro (h | ⟨v, hv, h1, h2⟩)
                · exact Or.inl h
                · by_cases hvk : v.1 = kv
                  · exfalso; apply hcond
                    have hv_eq : v = ⟨kv, hkv⟩ := Fin.ext hvk
                    rw [hv_eq] at h1 h2
                    exact ⟨by simp [h1], h2⟩
                  · exact Or.inr ⟨v, by omega, h1, h2⟩
            by_cases hp : st.mem (bmScrBase m r + bmNodes m r * bmNodes m r + (2 + ku)) =
                bmNodes m r ∨
                ∃ v : Fin r, v.1 < kv ∧ G (⟨ku, hku⟩, v) = true ∧
                  st.mem (bmScrBase m r + bmNodes m r * bmNodes m r + (2 + m + v.1)) = bmNodes m r
            · rw [ite_eq_left hp, ite_eq_left (hiff.mp hp)]
            · rw [ite_eq_right hp, ite_eq_right (fun h => hp (hiff.mpr h))])
        (n := r) (a := 0) (s := t1) ⟨Nat.zero_add _, fun a ha => by
          dsimp only [t1]; rw [Function.update_of_ne ha], by
          dsimp only [t1]; rw [Function.update_self, hdu]
          have : ¬ ∃ v : Fin r, v.1 < 0 ∧ G (⟨ku, hku⟩, v) = true ∧
              st.mem (bmScrBase m r + bmNodes m r * bmNodes m r + (2 + m + v.1)) = bmNodes m r := by
            rintro ⟨_, hv, _⟩; omega
          simp only [this, or_false]⟩
      unfold bmCovLOuter
      rw [clientResult_bind_read, clientResult_bind_write, clientResult_bind, clientResult_pure,
        clientState_bind_read, clientState_bind_write, clientState_bind, clientState_pure]
      refine ⟨by omega, fun a ha => ?_, fun u hu => ?_⟩
      · rw [hinner.2.1 a (by rcases ha with ha | ha <;> bm_omega)]
        exact hfr a ha
      · by_cases huk : u.1 = ku
        · have hu_eq : u = ⟨ku, hku⟩ := Fin.ext huk
          have hin_r :
              (Memory.spec 0).clientResult t1 (iterate bmCovLInner ((m, r), ku) r 0) = r := by
            have := hinner.1; omega
          have h22 := hinner.2.2
          rw [hin_r] at h22
          rw [hu_eq, h22]
          congr 1; ext; constructor
          · rintro (h | ⟨v, _, h1, h2⟩)
            · exact Or.inl h
            · exact Or.inr ⟨v, h1, h2⟩
          · rintro (h | ⟨v, h1, h2⟩)
            · exact Or.inl h
            · exact Or.inr ⟨v, by have := v.2; omega, h1, h2⟩
        · rw [hinner.2.1 _ (by omega)]
          exact hcov u (by omega))
    (n := m) (a := 0) (s := st)
    ⟨Nat.zero_add _, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  exact ⟨h.2.1, fun u => h.2.2 u (by omega)⟩

private theorem bmMain_spec {m r : ℕ} (G : Fin m × Fin r → Bool) {st : Memory.State}
    (hG : ∀ u : Fin m, ∀ v : Fin r, st.mem (3 + u.1 * r + v.1) = if G (u, v) then 1 else 0)
    (hfr : st.frontier = 3 + m * r) :
    let st' := (Memory.spec 0).clientState st (bmMain (m, r))
    let res := (Memory.spec 0).clientResult st (bmMain (m, r))
    ∃ (M : Finset (Fin m × Fin r)) (C : VertexCover (Fin m) (Fin r)),
      IsMaxMatching G M ∧ IsMinVertexCover G C ∧ M.card = C.size ∧ res = M.card ∧
      (∀ u : Fin m, ∀ v : Fin r, st'.mem (bmMatchAddr m r u.1 v.1) = if (u, v) ∈ M then 1 else 0) ∧
      (∀ u : Fin m, st'.mem (bmCovLAddr m r u.1) = if u ∈ C.left then 1 else 0) ∧
      (∀ v : Fin r, st'.mem (bmCovRAddr m r v.1) = if v ∈ C.right then 1 else 0) := by
  set st0 := (Memory.spec 0).clientState st (Memory.alloc (bmScratch m r))
  have hG0 : ∀ u : Fin m, ∀ v : Fin r, st0.mem (3 + u.1 * r + v.1) = if G (u, v) then 1 else 0 := by
    intro u v
    have hlt : u.1 * r + v.1 < m * r := idx_lt_rect u.2 v.2
    exact (Memory.mem_step_of_lt_frontier st (.alloc (bmScratch m r)) (by rw [hfr]; omega)
      (by simp)).trans (hG u v)
  obtain ⟨hG4, hmat4⟩ := bmBuild_spec G hG0
  set st1 := (Memory.spec 0).clientState st0
    (fillRange ((bmMatBase m r, 0), bmNodes m r * bmNodes m r))
  set st2 := (Memory.spec 0).clientState st1 (iterate bmSrcStep (m, r) m 0)
  set st3 := (Memory.spec 0).clientState st2 (iterate bmSnkStep (m, r) r 0)
  set st4 := (Memory.spec 0).clientState st3 (iterate bmEdgeOuter (m, r) m 0)
  have hst_ne : (bipartiteFinNetwork G).s ≠ (bipartiteFinNetwork G).t := by
    intro h; exact bipartiteNetwork_s_ne_t G ((bipartiteFinEquiv m r).injective h)
  have hcap_le1 : ∀ x y : Fin (bmNodes m r), (bipartiteFinNetwork G).cap x y ≤ 1 := fun x y => by
    change (bipartiteNetwork G).cap ((bipartiteFinEquiv m r).symm x)
      ((bipartiteFinEquiv m r).symm y) ≤ 1
    cases (bipartiteFinEquiv m r).symm x <;> cases (bipartiteFinEquiv m r).symm y <;>
      simp [bipartiteNetwork]
    split_ifs <;> omega
  have hst0_eq : (bipartiteFinNetwork G).s.1 = 0 ∧ (bipartiteFinNetwork G).t.1 = 1 :=
    ⟨bipartiteFinEquiv_val.1, bipartiteFinEquiv_val.2.1⟩
  have hEk := ekProg_flow_spec (mb := bmMatBase m r) (sb := bmScrBase m r) (B := 1)
    (bipartiteFinNetwork G) hst_ne hcap_le1 (le_refl _) hmat4
  rw [hst0_eq.1, hst0_eq.2] at hEk
  obtain ⟨hEk_frame, fFin, hflow, hdist_le, _, hmin, hC_eq, hval, hres⟩ := hEk
  set st5 := (Memory.spec 0).clientState st4
    (ekProg (⟨bmNodes m r, bmMatBase m r, bmScrBase m r, 1⟩, (0, 1)))
  set CFin : Finset (Fin (bmNodes m r)) :=
    Finset.univ.filter fun x =>
      st5.mem (distAddr ⟨bmNodes m r, bmMatBase m r, bmScrBase m r, 1⟩ x.1) < bmNodes m r
  have hG5 : ∀ u : Fin m, ∀ v : Fin r, st5.mem (3 + u.1 * r + v.1) = if G (u, v) then 1 else 0 := by
    intro u v
    have hlt : u.1 * r + v.1 < m * r := idx_lt_rect u.2 v.2
    rw [hEk_frame _ (Or.inl (by bm_omega))]
    exact hG4 u v
  obtain ⟨hR_fr, hR_cov⟩ := bmCovR_spec (m := m) (r := r) st5
  set st6 := (Memory.spec 0).clientState st5 (iterate bmCovRStep (m, r) r 0)
  have hG6 : ∀ u : Fin m, ∀ v : Fin r, st6.mem (3 + u.1 * r + v.1) = if G (u, v) then 1 else 0 := by
    intro u v
    have hlt : u.1 * r + v.1 < m * r := idx_lt_rect u.2 v.2
    rw [hR_fr _ (by bm_omega)]
    exact hG5 u v
  obtain ⟨hL_fr, hL_cov⟩ := bmCovL_spec G hG6
  set st7 := (Memory.spec 0).clientState st6 (iterate bmCovLOuter (m, r) m 0)
  have hst_main : (Memory.spec 0).clientState st (bmMain (m, r)) = st7 := by
    unfold bmMain; dsimp only
    rw [clientState_bind, clientState_bind, clientState_bind, clientState_bind,
      clientState_bind, clientState_bind, clientState_bind, clientState_bind, clientState_pure]
  have hres_main : (Memory.spec 0).clientResult st (bmMain (m, r)) =
      (Memory.spec 0).clientResult st4
        (ekProg (⟨bmNodes m r, bmMatBase m r, bmScrBase m r, 1⟩, (0, 1))) := by
    unfold bmMain; dsimp only
    rw [clientResult_bind, clientResult_bind, clientResult_bind, clientResult_bind,
      clientResult_bind, clientResult_bind, clientResult_bind, clientResult_bind, clientResult_pure]
  let f := fFin.ofReindex (bipartiteFinEquiv m r)
  let S := Network.cutOfReindex (bipartiteFinEquiv m r) CFin
  have hS_cut : (bipartiteNetwork G).IsCut S :=
    Network.isCut_cutOfReindex (bipartiteFinEquiv m r) hmin.1
  have hcap_eq : (bipartiteNetwork G).cutCapacity S = (bipartiteFinNetwork G).cutCapacity CFin :=
    Network.cutCapacity_cutOfReindex (bipartiteFinEquiv m r) (bipartiteNetwork G) CFin
  have hf_val : f.value = fFin.value := Network.Flow.value_ofReindex (bipartiteFinEquiv m r) fFin
  obtain ⟨hM_max, hC_min, hMC_eq⟩ :=
    bipartiteMatching_of_maxFlow_minCut hS_cut (by rw [hf_val, hval, hcap_eq])
  refine ⟨flowToMatching f, cutToVertexCover G S, hM_max, hC_min, hMC_eq, ?_, ?_, ?_, ?_⟩
  · rw [hres_main, hres, ← hcap_eq]
    have hcoe := card_flowToMatching_coe f
    omega
  · intro u v
    rw [hst_main]
    have h1 : (2 + u.1) * bmNodes m r + (2 + m + v.1) < bmNodes m r * bmNodes m r :=
      idx_lt_sq (by have := u.2; dsimp only [bmNodes]; omega)
        (by have := v.2; dsimp only [bmNodes]; omega)
    rw [hL_fr _ (Or.inl (by dsimp only [bmMatchAddr]; bm_omega)),
      hR_fr _ (by dsimp only [bmMatchAddr]; bm_omega)]
    have hfl := hflow (bipartiteFinEquiv m r (.left u)) (bipartiteFinEquiv m r (.right v))
    obtain ⟨_, _, hleft, hright⟩ := bipartiteFinEquiv_val (m := m) (r := r)
    rw [hleft u, hright v] at hfl
    have haddr_m : bmMatchAddr m r u.1 v.1 =
        flowAddr ⟨bmNodes m r, bmMatBase m r, bmScrBase m r, 1⟩ (2 + u.1) (2 + m + v.1) := rfl
    rw [haddr_m, hfl]
    have hf_eq : fFin (bipartiteFinEquiv m r (.left u)) (bipartiteFinEquiv m r (.right v)) =
        f (.left u) (.right v) := rfl
    rw [hf_eq]
    have hle1 : f (.left u) (.right v) ≤ 1 := by
      have := f.le_cap (.left u) (.right v)
      simp only [bipartiteNetwork] at this
      split_ifs at this <;> omega
    simp only [flowToMatching, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hpos : 0 < f (.left u) (.right v)
    · rw [ite_eq_left hpos]; omega
    · rw [ite_eq_right hpos]; omega
  · intro u
    rw [hst_main]
    have haddr_l : bmCovLAddr m r u.1 = bmCovLBase m r + u.1 := by
      dsimp only [bmCovLAddr, bmCovLBase, bmScrBase, bmMatBase, bmNodes, ekScratch]; ring
    rw [haddr_l, hL_cov u]
    have hdist_iff : ∀ x : Fin (bmNodes m r),
        st6.mem (bmScrBase m r + bmNodes m r * bmNodes m r + x.1) = bmNodes m r ↔ x ∉ CFin := by
      intro x
      rw [hR_fr _ (by have := x.2; bm_omega)]
      have hl := hdist_le x
      dsimp only [distAddr, bmNodes] at hl ⊢
      simp only [CFin, Finset.mem_filter, Finset.mem_univ, true_and, distAddr, bmNodes]
      omega
    obtain ⟨_, _, hleft, hright⟩ := bipartiteFinEquiv_val (m := m) (r := r)
    have hlu : st6.mem (bmScrBase m r + bmNodes m r * bmNodes m r + (2 + u.1)) = bmNodes m r ↔
        BipartiteVertex.left u ∉ S := by
      rw [← hleft u, hdist_iff]
      simp [S, Network.cutOfReindex]
    have hrv : ∀ v : Fin r,
        st6.mem (bmScrBase m r + bmNodes m r * bmNodes m r + (2 + m + v.1)) = bmNodes m r ↔
          BipartiteVertex.right v ∉ S := fun v => by
      rw [← hright v, hdist_iff]
      simp [S, Network.cutOfReindex]
    simp only [cutToVertexCover, Finset.mem_filter, Finset.mem_univ, true_and]
    have hiff : (st6.mem (bmScrBase m r + bmNodes m r * bmNodes m r + (2 + u.1)) = bmNodes m r ∨
        ∃ v : Fin r, G (u, v) = true ∧
          st6.mem (bmScrBase m r + bmNodes m r * bmNodes m r + (2 + m + v.1)) = bmNodes m r) ↔
        (BipartiteVertex.left u ∉ S ∨ ∃ v : Fin r, G (u, v) = true ∧ BipartiteVertex.right v ∉ S) :=
      or_congr hlu (exists_congr fun v => and_congr_right fun _ => hrv v)
    by_cases hp : BipartiteVertex.left u ∉ S ∨
        ∃ v : Fin r, G (u, v) = true ∧ BipartiteVertex.right v ∉ S
    · rw [ite_eq_left (hiff.mpr hp), ite_eq_left hp]
    · rw [ite_eq_right (fun h => hp (hiff.mp h)), ite_eq_right hp]
  · intro v
    rw [hst_main]
    have haddr_r : bmCovRAddr m r v.1 = bmCovRBase m r + v.1 := by
      dsimp only [bmCovRAddr, bmCovRBase, bmCovLBase, bmScrBase, bmMatBase, bmNodes, ekScratch]
      ring
    rw [haddr_r, hL_fr _ (Or.inr (by omega)), hR_cov v]
    obtain ⟨_, _, _, hright⟩ := bipartiteFinEquiv_val (m := m) (r := r)
    have hrv : st5.mem (bmScrBase m r + bmNodes m r * bmNodes m r + (2 + m + v.1)) < bmNodes m r ↔
        BipartiteVertex.right v ∈ S := by
      rw [← hright v]
      simp [S, Network.cutOfReindex, CFin, distAddr]
    simp only [cutToVertexCover, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hp : BipartiteVertex.right v ∈ S
    · rw [ite_eq_left (hrv.mpr hp), ite_eq_left hp]
    · rw [ite_eq_right (fun h => hp (hrv.mp h)), ite_eq_right hp]

private theorem bmInit_setup {m r w : ℕ} (G : Fin m × Fin r → Bool)
    (hw : Fits w (bmWorkspace m r)) :
    let st := Memory.State.init (encodeBipartiteInput G)
    st.frontier = 3 + m * r ∧ st.mem 1 = m ∧ st.mem 2 = r ∧
      Fits w ((encodeBipartiteInput G).length + 1) ∧ Memory.WellFormed w st := by
  have hfr : (Memory.State.init (encodeBipartiteInput G)).frontier = 3 + m * r := by
    simp only [Memory.State.init, encodeBipartiteInput, List.length_cons,
      length_encodeBipartiteMatrix]; omega
  have hlen : Fits w ((encodeBipartiteInput G).length + 1) := hw.of_le (by
    simp only [encodeBipartiteInput, List.length_cons, length_encodeBipartiteMatrix,
      bmWorkspace]; omega)
  exact ⟨hfr, by simp [Memory.State.init, encodeBipartiteInput],
    by simp [Memory.State.init, encodeBipartiteInput], hlen,
    Memory.wellFormed_init (inputFits_encodeBipartiteInput G hw) hlen⟩

/-- **Maximum bipartite matching and König vertex cover on the Word-RAM** ([Koenig1931];
[CLRS2009], Section 26.3): one uniform flat program over `Basis.exact` that, on
`encodeBipartiteInput G` for any `G : Fin m × Fin r → Bool`, halts within `C * (m + r + 1) ^ 5`
instructions at every word width fitting `ekBound (2 + (m + r)) 1`. It returns the maximum
matching cardinality `M.card = C.size`, stores `M` at `bmMatchAddr`, and stores a minimum König
vertex cover `C` at `bmCovLAddr` and `bmCovRAddr`. -/
theorem exists_bipartiteMatching_program :
    ∃ (R C pc : ℕ), 0 < C ∧ ∃ prog : Program .exact R,
      ∀ {m r w : ℕ} (G : Fin m × Fin r → Bool),
        Fits w (ekBound (2 + (m + r)) 1) →
        ∃ (y : Data R) (steps res : ℕ) (M : Finset (Fin m × Fin r))
          (cov : VertexCover (Fin m) (Fin r)),
          Runs w prog (State.init (encodeBipartiteInput G)) ⟨pc, y⟩ steps ∧
          step w prog ⟨pc, y⟩ = .halt res ∧
          steps + 1 ≤ C * (m + r + 1) ^ 5 ∧
          IsMaxMatching G M ∧ IsMinVertexCover G cov ∧ M.card = cov.size ∧ res = M.card ∧
          (∀ u : Fin m, ∀ v : Fin r,
            y.mem (bmMatchAddr m r u.1 v.1) = if (u, v) ∈ M then 1 else 0) ∧
          (∀ u : Fin m, y.mem (bmCovLAddr m r u.1) = if u ∈ cov.left then 1 else 0) ∧
          (∀ v : Fin r, y.mem (bmCovRAddr m r v.1) = if v ∈ cov.right then 1 else 0) := by
  obtain ⟨R, C₀, pc, prog, _, _, hprog⟩ :=
    bmProg_realizes.exists_standard_init_program_state_from_words 0
  refine ⟨R, 5204 * C₀ + 2, pc, by omega, prog, ?_⟩
  intro m r w G hwB
  have hw : Fits w (bmWorkspace m r) := hwB.of_le (by dsimp only [bmWorkspace, ekBound]; nlinarith)
  set st := Memory.State.init (encodeBipartiteInput G)
  obtain ⟨hfr, h1, h2, hlen, hwf⟩ := bmInit_setup G hw
  have hvh : (Memory.spec w).ValidHistory st ((Memory.spec w).clientHistory st (bmProg ())) := by
    unfold bmProg
    refine validHistory_read_bind (by rw [hfr]; omega) ?_
    refine validHistory_read_bind (by rw [hfr]; omega) ?_
    rw [h1, h2]
    exact validHistory_bmMain hwf hfr hw hwB
  obtain ⟨y, steps, hruns, hhalt, hmem, _, hbound⟩ :=
    hprog w () (encodeBipartiteInput G) (fun j => Fin.elim0 j) (Nat.zero_le _) hlen
      (inputFits_encodeBipartiteInput G hw) ⟨by rw [h1, h2]; exact hw, by rw [h1, h2]; exact hwB⟩
      hvh
  rw [clientState_width w (bmProg ())] at hmem
  rw [clientResult_width w (bmProg ())] at hhalt
  have hst_eq : (Memory.spec 0).clientState st (bmProg ()) =
      (Memory.spec 0).clientState st (bmMain (m, r)) := by
    unfold bmProg; rw [clientState_bind_read, clientState_bind_read, h1, h2]
  have hres_eq : (Memory.spec 0).clientResult st (bmProg ()) =
      (Memory.spec 0).clientResult st (bmMain (m, r)) := by
    unfold bmProg; rw [clientResult_bind_read, clientResult_bind_read, h1, h2]
  obtain ⟨M, cov, hM, hC, hMC, hres, hm_mem, hcl_mem, hcr_mem⟩ :=
    bmMain_spec G (bmInit_mem_edge G) hfr
  have hymem : y.mem = ((Memory.spec 0).clientState st (bmMain (m, r))).mem := by
    rw [← hst_eq]; exact congrArg Memory.State.mem hmem
  have hmc : memoryCost (bmProg ()) st ≤ 5202 * (m + r + 1) ^ 5 := by
    unfold bmProg
    rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
      memoryCost_bind', memoryCost_read, clientResult_read, clientState_read, h1, h2]
    have h1p : 1 ≤ (m + r + 1) ^ 5 := Nat.one_le_pow _ _ (by omega)
    have := memoryCost_bmMain_le m r st
    omega
  have hp : 1 ≤ (m + r + 1) ^ 5 := Nat.one_le_pow _ _ (by omega)
  refine ⟨y, steps, _, M, cov, hruns, hhalt, ?_, hM, hC, hMC, hres_eq.trans hres,
    fun u v => by rw [hymem]; exact hm_mem u v,
    fun u => by rw [hymem]; exact hcl_mem u,
    fun v => by rw [hymem]; exact hcr_mem v⟩
  calc steps + 1
      ≤ C₀ * (memoryCost (bmProg ()) st + 0 + 1) + 1 := hbound
    _ ≤ C₀ * (5202 * (m + r + 1) ^ 5 + 1) + 1 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) 1
    _ ≤ (5204 * C₀ + 2) * (m + r + 1) ^ 5 := by nlinarith

/-- **Bipartite perfect matching decision on the Word-RAM:** one uniform flat program over
`Basis.exact` that, on `encodeBipartiteInput G` for any `G : Fin n × Fin n → Bool`, halts within
`C * (n + 1) ^ 5` instructions at every word width fitting `ekBound (2 + (n + n)) 1`, returning `1`
iff `Cslib.Circuits.BipartiteMatching.HasPerfectMatching G` and `0` otherwise. -/
theorem exists_perfectMatching_program :
    ∃ (R C pc : ℕ), 0 < C ∧ ∃ prog : Program .exact R,
      ∀ {n w : ℕ} (G : Fin n × Fin n → Bool),
        Fits w (ekBound (2 + (n + n)) 1) →
        ∃ (y : Data R) (steps res : ℕ),
          Runs w prog (State.init (encodeBipartiteInput G)) ⟨pc, y⟩ steps ∧
          step w prog ⟨pc, y⟩ = .halt res ∧
          steps + 1 ≤ C * (n + 1) ^ 5 ∧
          (res = 1 ↔ Cslib.Circuits.BipartiteMatching.HasPerfectMatching G) ∧
          res ≤ 1 := by
  obtain ⟨R, C₀, pc, prog, _, _, hprog⟩ :=
    pmProg_realizes.exists_standard_init_program_state_from_words 0
  refine ⟨R, 168000 * C₀ + 2, pc, by omega, prog, ?_⟩
  intro n w G hwB
  have hw : Fits w (bmWorkspace n n) := hwB.of_le (by dsimp only [bmWorkspace, ekBound]; nlinarith)
  set st := Memory.State.init (encodeBipartiteInput G)
  obtain ⟨hfr, h1, h2, hlen, hwf⟩ := bmInit_setup G hw
  have hvh : (Memory.spec w).ValidHistory st ((Memory.spec w).clientHistory st (pmProg ())) := by
    unfold pmProg
    refine validHistory_read_bind (by rw [hfr]; omega) ?_
    refine validHistory_read_bind (by rw [hfr]; omega) ?_
    rw [h1, h2]
    exact validHistory_bind_step (validHistory_bmMain hwf hfr hw hwB)
      (validHistory_ite (fun _ => validHistory_pure _ _ _) (fun _ => validHistory_pure _ _ _))
  obtain ⟨y, steps, hruns, hhalt, _, _, hbound⟩ :=
    hprog w () (encodeBipartiteInput G) (fun j => Fin.elim0 j) (Nat.zero_le _) hlen
      (inputFits_encodeBipartiteInput G hw) ⟨by rw [h1, h2]; exact hw, by rw [h1, h2]; exact hwB⟩
      hvh
  rw [clientResult_width w (pmProg ())] at hhalt
  obtain ⟨M, _, hM, _, _, hres, _, _, _⟩ := bmMain_spec G (bmInit_mem_edge G) hfr
  have hres_pm : (Memory.spec 0).clientResult st (pmProg ()) =
      if M.card = n then 1 else 0 := by
    unfold pmProg
    rw [clientResult_bind_read, clientResult_bind_read, h1, h2, clientResult_bind, hres]
    by_cases hc : M.card = n
    · rw [ite_eq_left ⟨rfl, hc⟩, ite_eq_left hc, clientResult_pure]
    · rw [ite_eq_right (fun h => hc h.2), ite_eq_right hc, clientResult_pure]
  have hmc : memoryCost (pmProg ()) st ≤ 167000 * (n + 1) ^ 5 := by
    unfold pmProg
    rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
      memoryCost_bind', memoryCost_read, clientResult_read, clientState_read, h1, h2]
    have hmain : memoryCost (bmMain (n, n) >>= fun res =>
        if n = n ∧ res = n then pure 1 else pure 0) st ≤ 5200 * (n + n + 1) ^ 5 + 0 :=
      memoryCost_bind_le (memoryCost_bmMain_le n n st) fun _ _ => by
        rw [memoryCost_ite]; split_ifs <;> exact le_refl 0
    have h2 : (n + n + 1) ^ 5 ≤ (2 * (n + 1)) ^ 5 := Nat.pow_le_pow_left (by omega) 5
    have h25 : (2 * (n + 1)) ^ 5 = 32 * (n + 1) ^ 5 := by ring
    have h1p : 1 ≤ (n + 1) ^ 5 := Nat.one_le_pow _ _ (by omega)
    nlinarith
  have hp : 1 ≤ (n + 1) ^ 5 := Nat.one_le_pow _ _ (by omega)
  refine ⟨y, steps, (Memory.spec 0).clientResult st (pmProg ()), hruns, hhalt, ?_, ?_, ?_⟩
  · calc steps + 1
        ≤ C₀ * (memoryCost (pmProg ()) st + 0 + 1) + 1 := hbound
      _ ≤ C₀ * (167000 * (n + 1) ^ 5 + 1) + 1 :=
          Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) 1
      _ ≤ (168000 * C₀ + 2) * (n + 1) ^ 5 := by nlinarith
  · rw [hres_pm, hasPerfectMatching_iff_exists_matching_card, Fintype.card_fin]
    constructor
    · intro h
      have hcard : M.card = n := by split_ifs at h with hc; exact hc
      exact ⟨M, hM.1, hcard⟩
    · rintro ⟨M', hM', hcard⟩
      have hle₁ : n ≤ M.card := le_trans (le_of_eq hcard.symm) (hM.2 M' hM')
      have htriv : IsVertexCover G ⟨Finset.univ, ∅⟩ := fun u _ _ => .inl (Finset.mem_univ u)
      have hle₂ : M.card ≤ n := by
        simpa [VertexCover.size] using card_le_size_of_matching_vertexCover hM.1 htriv
      rw [ite_eq_left (by omega)]
  · rw [hres_pm]; split_ifs <;> omega

end UniformBipartite

/-! ### Uniform minimum vertex separator by vertex splitting -/

section UniformVertexSeparator

/-- Encode a Boolean vector of length `n` as `n` words (`1` for `true`, `0` for `false`). -/
@[expose] def encodeBoolVec {n : ℕ} (v : Vector Bool n) : List ℕ :=
  (List.finRange n).map fun i => if vget v i then 1 else 0

/-- Word-RAM input for minimum vertex separator: `n :: (encodeBoolVec Z ++ encodeBoolVec A ++
encodeBoolVec B ++ flattenMatrix (fun u v => if G.Adj u v then 1 else 0))`. Address `1` stores `n`;
`2 + v` stores `Z[v]`; `2 + n + v` stores `A[v]`; `2 + 2 * n + v` stores `B[v]`; and
`2 + 3 * n + u * n + v` stores `G.Adj u v`. -/
@[expose] def encodeSepInput {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Z A B : Vector Bool n) : List ℕ :=
  n :: (encodeBoolVec Z ++ encodeBoolVec A ++ encodeBoolVec B ++
    flattenMatrix (fun u v : Fin n => if G.Adj u v then 1 else 0))

private abbrev sepNodes (n : ℕ) : ℕ := n + n + 2
private abbrev sepMatBase (n : ℕ) : ℕ := 2 + 3 * n + n * n
private abbrev sepScrBase (n : ℕ) : ℕ := sepMatBase n + sepNodes n * sepNodes n
private abbrev sepOutBase (n : ℕ) : ℕ := sepScrBase n + ekScratch (sepNodes n)
private abbrev sepSideBase (n : ℕ) : ℕ := sepOutBase n + n
private abbrev sepScratch (n : ℕ) : ℕ :=
  sepNodes n * sepNodes n + ekScratch (sepNodes n) + n + n

/-- Output address of the separator indicator for `v` (`1` iff `v ∈ out.sep`). -/
@[expose] def sepOutAddr (n v : ℕ) : ℕ :=
  2 + 3 * n + n * n + 2 * ((n + n + 2) * (n + n + 2)) + 2 * (n + n + 2) + v

/-- Output address of the side-labelling indicator for `v` (`1` iff `vget out.side v = true`). -/
@[expose] def sepSideAddr (n v : ℕ) : ℕ :=
  2 + 3 * n + n * n + 2 * ((n + n + 2) * (n + n + 2)) + 2 * (n + n + 2) + n + v

private abbrev sepWorkspace (n : ℕ) : ℕ :=
  2 + 3 * n + n * n + 2 * ((n + n + 2) * (n + n + 2)) + 2 * (n + n + 2) + n + n

private theorem length_encodeBoolVec {n : ℕ} (v : Vector Bool n) :
    (encodeBoolVec v).length = n := by
  simp [encodeBoolVec]

private theorem getElem_encodeBoolVec {n : ℕ} (v : Vector Bool n) (i : Fin n) :
    (encodeBoolVec v)[i.1]'(by rw [length_encodeBoolVec]; exact i.2) =
      if vget v i then 1 else 0 := by
  simp [encodeBoolVec]

private theorem length_encodeSepInput {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Z A B : Vector Bool n) :
    (encodeSepInput G Z A B).length = 1 + 3 * n + n * n := by
  simp only [encodeSepInput, List.length_cons, List.length_append, length_encodeBoolVec,
    length_flattenMatrix]
  omega

private theorem sepInit_mem_Z {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Z A B : Vector Bool n) (v : Fin n) :
    (Memory.State.init (encodeSepInput G Z A B)).mem (2 + v.1) =
      if vget Z v then 1 else 0 := by
  have hv : v.1 < (encodeBoolVec Z).length := by rw [length_encodeBoolVec]; exact v.2
  change (if 2 + v.1 = 0 then (encodeSepInput G Z A B).length
    else (encodeSepInput G Z A B).getD (2 + v.1 - 1) 0) = _
  rw [ite_eq_right (by omega), show 2 + v.1 - 1 = v.1 + 1 by omega]
  change (encodeBoolVec Z ++ encodeBoolVec A ++ encodeBoolVec B ++
    flattenMatrix (fun u w : Fin n => if G.Adj u w then 1 else 0)).getD v.1 0 = _
  rw [List.getD_eq_getElem?_getD, List.append_assoc, List.append_assoc,
    List.getElem?_append_left hv, List.getElem?_eq_getElem hv, Option.getD_some,
    getElem_encodeBoolVec]

private theorem sepInit_mem_A {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Z A B : Vector Bool n) (v : Fin n) :
    (Memory.State.init (encodeSepInput G Z A B)).mem (2 + n + v.1) =
      if vget A v then 1 else 0 := by
  have hv : v.1 < (encodeBoolVec A).length := by rw [length_encodeBoolVec]; exact v.2
  change (if 2 + n + v.1 = 0 then (encodeSepInput G Z A B).length
    else (encodeSepInput G Z A B).getD (2 + n + v.1 - 1) 0) = _
  rw [ite_eq_right (by omega), show 2 + n + v.1 - 1 = (n + v.1) + 1 by omega]
  change (encodeBoolVec Z ++ encodeBoolVec A ++ encodeBoolVec B ++
    flattenMatrix (fun u w : Fin n => if G.Adj u w then 1 else 0)).getD (n + v.1) 0 = _
  rw [List.getD_eq_getElem?_getD, List.append_assoc, List.append_assoc,
    List.getElem?_append_right (by rw [length_encodeBoolVec]; omega),
    length_encodeBoolVec, Nat.add_sub_cancel_left,
    List.getElem?_append_left hv, List.getElem?_eq_getElem hv, Option.getD_some,
    getElem_encodeBoolVec]

private theorem sepInit_mem_B {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Z A B : Vector Bool n) (v : Fin n) :
    (Memory.State.init (encodeSepInput G Z A B)).mem (2 + 2 * n + v.1) =
      if vget B v then 1 else 0 := by
  have hv : v.1 < (encodeBoolVec B).length := by rw [length_encodeBoolVec]; exact v.2
  change (if 2 + 2 * n + v.1 = 0 then (encodeSepInput G Z A B).length
    else (encodeSepInput G Z A B).getD (2 + 2 * n + v.1 - 1) 0) = _
  rw [ite_eq_right (by omega), show 2 + 2 * n + v.1 - 1 = (2 * n + v.1) + 1 by omega]
  change (encodeBoolVec Z ++ encodeBoolVec A ++ encodeBoolVec B ++
    flattenMatrix (fun u w : Fin n => if G.Adj u w then 1 else 0)).getD (2 * n + v.1) 0 = _
  rw [List.getD_eq_getElem?_getD, List.append_assoc, List.append_assoc,
    List.getElem?_append_right (by rw [length_encodeBoolVec]; omega),
    length_encodeBoolVec, show 2 * n + v.1 - n = n + v.1 by omega,
    List.getElem?_append_right (by rw [length_encodeBoolVec]; omega),
    length_encodeBoolVec, Nat.add_sub_cancel_left,
    List.getElem?_append_left hv, List.getElem?_eq_getElem hv, Option.getD_some,
    getElem_encodeBoolVec]

private theorem sepInit_mem_edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Z A B : Vector Bool n) (u v : Fin n) :
    (Memory.State.init (encodeSepInput G Z A B)).mem (2 + 3 * n + u.1 * n + v.1) =
      if G.Adj u v then 1 else 0 := by
  have hlt :
      u.1 * n + v.1 < (flattenMatrix (fun a b : Fin n => if G.Adj a b then 1 else 0)).length := by
    rw [length_flattenMatrix]; exact idx_lt_sq u.2 v.2
  change (if 2 + 3 * n + u.1 * n + v.1 = 0 then (encodeSepInput G Z A B).length
    else (encodeSepInput G Z A B).getD (2 + 3 * n + u.1 * n + v.1 - 1) 0) = _
  rw [ite_eq_right (by omega), show 2 + 3 * n + u.1 * n + v.1 - 1 =
    (3 * n + (u.1 * n + v.1)) + 1 by omega]
  change (encodeBoolVec Z ++ encodeBoolVec A ++ encodeBoolVec B ++
    flattenMatrix (fun a b : Fin n => if G.Adj a b then 1 else 0)).getD
      (3 * n + (u.1 * n + v.1)) 0 = _
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by simp only [List.length_append, length_encodeBoolVec]; omega),
    show (encodeBoolVec Z ++ encodeBoolVec A ++ encodeBoolVec B).length = 3 * n by
      simp only [List.length_append, length_encodeBoolVec]; omega,
    Nat.add_sub_cancel_left, List.getElem?_eq_getElem hlt, Option.getD_some,
    getElem_flattenMatrix]

private theorem inputFits_encodeSepInput {n w : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Z A B : Vector Bool n) (hw : Fits w (sepWorkspace n)) :
    InputFits w (encodeSepInput G Z A B) := by
  have h1 : Fits w 1 := hw.of_le (by dsimp only [sepWorkspace]; omega)
  have hbv : ∀ (v : Vector Bool n) x, x ∈ encodeBoolVec v → Fits w x := by
    intro v x hx
    simp only [encodeBoolVec, List.mem_map] at hx
    obtain ⟨_, _, rfl⟩ := hx
    split_ifs
    · exact h1
    · exact fits_zero w
  refine ⟨hw.of_le (by rw [length_encodeSepInput]; dsimp only [sepWorkspace]; omega),
    fun x hx => ?_⟩
  simp only [encodeSepInput, List.mem_cons, List.mem_append] at hx
  rcases hx with rfl | (((hx | hx) | hx) | hx)
  · exact hw.of_le (by dsimp only [sepWorkspace]; omega)
  · exact hbv Z x hx
  · exact hbv A x hx
  · exact hbv B x hx
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    rw [length_flattenMatrix] at hi
    have hn : 0 < n := Nat.pos_of_ne_zero fun h => by simp [h] at hi
    have hu : i / n < n := Nat.div_lt_of_lt_mul hi
    have hv : i % n < n := Nat.mod_lt i hn
    have hidx : i = (⟨i / n, hu⟩ : Fin n).1 * n + (⟨i % n, hv⟩ : Fin n).1 :=
      (Nat.div_add_mod' i n).symm
    have he := getElem_flattenMatrix (W := fun a b : Fin n => if G.Adj a b then 1 else 0)
      ⟨i / n, hu⟩ ⟨i % n, hv⟩
    have hval : (flattenMatrix (fun a b : Fin n => if G.Adj a b then 1 else 0))[i] =
        if G.Adj ⟨i / n, hu⟩ ⟨i % n, hv⟩ then 1 else 0 := by
      rw [← he]; congr 1
    rw [hval]
    split_ifs
    · exact h1
    · exact fits_zero w

private def sepVertStep (d : ℕ × ℕ) : Memory.Prog ℕ := do
  let n := d.1
  let v := d.2
  let nv := sepNodes n
  let z ← Memory.read (2 + v)
  let a ← Memory.read (2 + n + v)
  let b ← Memory.read (2 + 2 * n + v)
  let capA := if a = 0 then 0 else n + 1
  let capB := if b = 0 then 0 else n + 1
  let capZ := if z = 0 then 1 else 0
  Memory.write (sepMatBase n + (v + 2)) capA
  Memory.write (sepMatBase n + (v + n + 2) * nv + 1) capB
  Memory.write (sepMatBase n + (v + 2) * nv + (v + n + 2)) capZ
  pure (v + 1)

private def sepEdgeInner (d : (ℕ × ℕ) × ℕ) : Memory.Prog ℕ := do
  let n := d.1.1
  let u := d.1.2
  let v := d.2
  let nv := sepNodes n
  let e ← Memory.read (2 + 3 * n + u * n + v)
  let cap := if e = 0 then 0 else n + 1
  Memory.write (sepMatBase n + (u + n + 2) * nv + (v + 2)) cap
  pure (v + 1)

private def sepEdgeOuter (d : ℕ × ℕ) : Memory.Prog ℕ := do
  let _ ← Memory.read 0
  let _ ← iterate sepEdgeInner d d.1 0
  pure (d.2 + 1)

private def sepExtractStep (d : ℕ × ℕ) : Memory.Prog ℕ := do
  let n := d.1
  let v := d.2
  let nv := sepNodes n
  let z ← Memory.read (2 + v)
  let din ← Memory.read (sepScrBase n + nv * nv + (v + 2))
  let dout ← Memory.read (sepScrBase n + nv * nv + (v + n + 2))
  let inSep := if z = 0 ∧ din < nv ∧ dout = nv then 1 else 0
  let inSide := if dout < nv then 1 else 0
  Memory.write (sepOutBase n + v) inSep
  Memory.write (sepSideBase n + v) inSide
  pure (v + 1)

private def sepMain (n : ℕ) : Memory.Prog ℕ := do
  let nv := sepNodes n
  let _ ← Memory.alloc (sepScratch n)
  fillRange ((sepMatBase n, 0), nv * nv)
  let _ ← iterate sepVertStep n n 0
  let _ ← iterate sepEdgeOuter n n 0
  let res ← ekProg (⟨nv, sepMatBase n, sepScrBase n, n + 1⟩, (0, 1))
  let _ ← iterate sepExtractStep n n 0
  pure res

private def sepProg (_ : Unit) : Memory.Prog ℕ := do
  let n ← Memory.read 1
  sepMain n

local macro "sep_omega" : tactic => `(tactic| (
  dsimp -failIfUnchanged only [sepWorkspace, sepScratch, sepOutAddr, sepSideAddr,
    sepSideBase, sepOutBase, sepScrBase, sepMatBase, sepNodes, ekScratch, ekBound, CtxFits] at *
  first | omega | nlinarith))

private theorem clientResult_sepEdgeOuter (d : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (sepEdgeOuter d) = d.2 + 1 := by
  unfold sepEdgeOuter
  rw [clientResult_bind_read, clientResult_bind, clientResult_pure]

private theorem sepVertStep_realizes :
    Realizes .exact sepVertStep (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (sepWorkspace d.1) ∧ d.2 < d.1) (fun _ _ => 0) := by
  unfold sepVertStep
  realize
  all_goals
    obtain ⟨hw, hv⟩ := h
    apply hw.of_le
    have h1 : (d.2 + d.1 + 2) * (d.1 + d.1 + 2) + 1 <
        (d.1 + d.1 + 2) * (d.1 + d.1 + 2) := idx_lt_sq (by omega) (by omega)
    have h2 : (d.2 + 2) * (d.1 + d.1 + 2) + (d.2 + d.1 + 2) <
        (d.1 + d.1 + 2) * (d.1 + d.1 + 2) := idx_lt_sq (by omega) (by omega)
    sep_omega

private theorem sepEdgeInner_realizes :
    Realizes .exact sepEdgeInner (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (sepWorkspace d.1.1) ∧ d.1.2 < d.1.1 ∧ d.2 < d.1.1)
      (fun _ _ => 0) := by
  unfold sepEdgeInner
  realize
  all_goals
    obtain ⟨hw, hu, hv⟩ := h
    apply hw.of_le
    have h1 : d.1.2 * d.1.1 + d.2 < d.1.1 * d.1.1 := idx_lt_sq hu hv
    have h2 : (d.1.2 + d.1.1 + 2) * (d.1.1 + d.1.1 + 2) + (d.2 + 2) <
        (d.1.1 + d.1.1 + 2) * (d.1.1 + d.1.1 + 2) := idx_lt_sq (by omega) (by omega)
    sep_omega

private theorem sepEdgeOuter_realizes :
    Realizes .exact sepEdgeOuter (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (sepWorkspace d.1) ∧ d.2 < d.1) (fun _ _ => 0) := by
  unfold sepEdgeOuter
  realize [sepEdgeInner_realizes]
  all_goals
    obtain ⟨hw, hu⟩ := h
    try (apply hw.of_le; sep_omega)
  refine iterationSafe_of_stepInv _ _ w _ (fun rem (v : ℕ) _ => v + rem = d.1) ?_ (Nat.zero_add _)
  intro rem v t hsum
  dsimp only at hsum ⊢
  refine ⟨⟨hw, hu, by omega⟩, ?_⟩
  change v + 1 + rem = d.1; omega

private theorem sepExtractStep_realizes :
    Realizes .exact sepExtractStep (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (sepWorkspace d.1) ∧ d.2 < d.1) (fun _ _ => 0) := by
  unfold sepExtractStep
  realize
  all_goals
    obtain ⟨hw, hv⟩ := h
    apply hw.of_le; sep_omega

private theorem sepMain_realizes :
    Realizes .exact sepMain (WordEncoding.encode (α := ℕ)) (WordEncoding.encode (α := ℕ))
      (fun w n _ => Fits w (sepWorkspace n) ∧ Fits w (ekBound (n + n + 2) (n + 1)))
      (fun _ _ => 0) := by
  unfold sepMain
  realize [fillRange_realizes, sepVertStep_realizes, sepEdgeOuter_realizes,
    ekProg_realizes, sepExtractStep_realizes]
  all_goals
    obtain ⟨hw, hwB⟩ := h
    try (apply hw.of_le; sep_omega)
    try sep_omega
  · refine iterationSafe_of_stepInv _ _ w _ (fun rem (v : ℕ) _ => v + rem = d) ?_ (Nat.zero_add _)
    intro rem v t hsum
    dsimp only at hsum ⊢
    refine ⟨⟨hw, by omega⟩, ?_⟩
    change v + 1 + rem = d; omega
  · refine iterationSafe_of_stepInv _ _ w _ (fun rem (u : ℕ) _ => u + rem = d) ?_ (Nat.zero_add _)
    intro rem u t hsum
    dsimp only at hsum ⊢
    refine ⟨⟨hw, by omega⟩, ?_⟩
    rw [clientResult_sepEdgeOuter]; dsimp only; omega
  · refine ⟨by sep_omega, hw.of_le (by sep_omega), hwB⟩
  · refine iterationSafe_of_stepInv _ _ w _ (fun rem (v : ℕ) _ => v + rem = d) ?_ (Nat.zero_add _)
    intro rem v t hsum
    dsimp only at hsum ⊢
    refine ⟨⟨hw, by omega⟩, ?_⟩
    change v + 1 + rem = d; omega

private theorem sepProg_realizes :
    Realizes .exact sepProg (WordEncoding.encode (α := Unit)) (WordEncoding.encode (α := ℕ))
      (fun w _ st => Fits w (sepWorkspace (st.mem 1)) ∧
        Fits w (ekBound (st.mem 1 + st.mem 1 + 2) (st.mem 1 + 1))) (fun _ _ => 0) := by
  unfold sepProg
  realize [sepMain_realizes]
  all_goals
    obtain ⟨hw, hwB⟩ := h
    first
    | exact hw.of_le (by sep_omega)
    | exact hwB

private theorem memoryCost_sepMain_le (n : ℕ) (s : Memory.State) :
    memoryCost (sepMain n) s ≤ 5200 * (n + 1) ^ 5 := by
  have hv : ∀ (v : ℕ) t, memoryCost (sepVertStep (n, v)) t ≤ 6 := fun _ _ => by
    unfold sepVertStep
    refine (memoryCost_read_bind_le (k := 5) fun _ _ =>
      (memoryCost_read_bind_le (k := 4) fun _ _ =>
        (memoryCost_read_bind_le (k := 3) fun _ _ =>
          (memoryCost_write_bind_le (k := 2) fun _ _ =>
            (memoryCost_write_bind_le (k := 1) fun _ _ => le_refl 1).trans
              (by omega)).trans (by omega)).trans (by omega)).trans (by omega)).trans (by omega)
  have hei : ∀ u v t, memoryCost (sepEdgeInner ((n, u), v)) t ≤ 2 := fun _ _ _ => by
    unfold sepEdgeInner
    exact memoryCost_read_bind_le fun _ _ => le_refl 1
  have heo : ∀ (u : ℕ) t, memoryCost (sepEdgeOuter (n, u)) t ≤ 1 + 2 * n := fun u t => by
    unfold sepEdgeOuter
    refine (memoryCost_read_bind_le (k := 2 * n) fun _ t' => ?_).trans (by omega)
    have hit := memoryCost_iterate_le_of sepEdgeInner 2 (n, u) (hei u) n 0 t'
    exact (memoryCost_bind_le (k₂ := 0) hit fun _ _ => le_refl 0).trans (by omega)
  have hex : ∀ (v : ℕ) t, memoryCost (sepExtractStep (n, v)) t ≤ 5 := fun _ _ => by
    unfold sepExtractStep
    refine (memoryCost_read_bind_le (k := 4) fun _ _ =>
      (memoryCost_read_bind_le (k := 3) fun _ _ =>
        (memoryCost_read_bind_le (k := 2) fun _ _ =>
          (memoryCost_write_bind_le (k := 1) fun _ _ => le_refl 1).trans
            (by omega)).trans (by omega)).trans (by omega)).trans (by omega)
  have htot : memoryCost (sepMain n) s ≤
      (sepScratch n + 1) + (sepNodes n * sepNodes n + (6 * n + ((1 + 2 * n) * n +
        (ekCost (sepNodes n) + (5 * n + 0))))) := by
    unfold sepMain
    dsimp only
    refine memoryCost_bind_le (memoryCost_alloc _ _).le fun _ t1 => ?_
    refine memoryCost_bind_le (memoryCost_fillRange_le _ _ _ t1) fun _ t2 => ?_
    refine memoryCost_bind_le (memoryCost_iterate_le_of sepVertStep 6 n hv n 0 t2) fun _ t3 => ?_
    refine memoryCost_bind_le
      (memoryCost_iterate_le_of sepEdgeOuter (1 + 2 * n) n heo n 0 t3) fun _ t4 => ?_
    refine memoryCost_bind_le (memoryCost_ekProg_le _ 0 1 t4) fun _ t5 => ?_
    refine memoryCost_bind_le
      (memoryCost_iterate_le_of sepExtractStep 5 n hex n 0 t5) fun _ _ => le_refl 0
  refine htot.trans ?_
  dsimp only [sepScratch, sepNodes, ekScratch, ekCost]
  set k := n + 1 with hk
  have hnv : n + n + 2 + 1 ≤ 3 * k := by omega
  have hpow5 : (n + n + 2 + 1) ^ 5 ≤ (3 * k) ^ 5 := Nat.pow_le_pow_left hnv 5
  have h35 : (3 * k) ^ 5 = 243 * k ^ 5 := by ring
  have hk2 : k ^ 2 ≤ k ^ 5 := Nat.pow_le_pow_right (by omega) (by decide)
  have hk1 : 1 ≤ k ^ 5 := Nat.one_le_pow _ _ (by omega)
  have hn2 : n * n ≤ k ^ 2 := by rw [hk]; nlinarith
  have hnv2 : (n + n + 2) * (n + n + 2) ≤ 9 * k ^ 2 := by rw [hk]; nlinarith
  nlinarith

private abbrev SepReady (w n : ℕ) (s : Memory.State) : Prop :=
  Memory.WellFormed w s ∧ sepWorkspace n ≤ s.frontier

private theorem validHistory_sepMain {w n : ℕ} {st : Memory.State}
    (hwf : Memory.WellFormed w st) (hfr : st.frontier = 2 + 3 * n + n * n)
    (hw : Fits w (sepWorkspace n)) (hwB : Fits w (ekBound (sepNodes n) (n + 1))) :
    (Memory.spec w).ValidHistory st ((Memory.spec w).clientHistory st (sepMain n)) := by
  unfold sepMain
  dsimp only
  have halloc : (Memory.spec w).ValidHistory st
      ((Memory.spec w).clientHistory st (Memory.alloc (sepScratch n))) :=
    validHistory_alloc (by rw [hfr]; exact hw.of_le (by sep_omega))
  refine validHistory_bind_step halloc ?_
  set s1 := (Memory.spec 0).clientState st (Memory.alloc (sepScratch n))
  have hs1 : SepReady w n s1 :=
    ⟨wellFormed_clientState hwf halloc,
      by change sepWorkspace n ≤ st.frontier + sepScratch n; rw [hfr]; sep_omega⟩
  have hfill := validHistory_fillRange (base := sepMatBase n) (val := 0)
    (len := sepNodes n * sepNodes n) hs1.1 (by have := hs1.2; sep_omega) (fits_zero w)
  refine validHistory_bind_step hfill ?_
  set s2 := (Memory.spec 0).clientState s1
    (fillRange ((sepMatBase n, 0), sepNodes n * sepNodes n))
  have hs2 : SepReady w n s2 := MonotoneMemInv.pres hs1 hfill
  have h1fit : Fits w 1 := hw.of_le (by sep_omega)
  have hn1fit : Fits w (n + 1) := hw.of_le (by sep_omega)
  have hvert : (Memory.spec w).ValidHistory s2
      ((Memory.spec w).clientHistory s2 (iterate sepVertStep n n 0)) := by
    refine validHistory_iterate_nat (Inv := SepReady w n) n 0 (fun v hv t ht => ⟨?_, ?_⟩) hs2
    · unfold sepVertStep
      have h1 : (v + n + 2) * sepNodes n + 1 < sepNodes n * sepNodes n :=
        idx_lt_sq (by dsimp only [sepNodes]; omega) (by dsimp only [sepNodes]; omega)
      have h2 : (v + 2) * sepNodes n + (v + n + 2) < sepNodes n * sepNodes n :=
        idx_lt_sq (by dsimp only [sepNodes]; omega) (by dsimp only [sepNodes]; omega)
      refine validHistory_read_bind (by have := ht.2; sep_omega) ?_
      refine validHistory_read_bind (by have := ht.2; sep_omega) ?_
      refine validHistory_read_bind (by have := ht.2; sep_omega) ?_
      refine validHistory_write_bind (by have := ht.2; sep_omega)
        (by split_ifs <;> first | exact fits_zero w | exact hn1fit) ?_
      refine validHistory_write_bind (by have := ht.2; sep_omega)
        (by split_ifs <;> first | exact fits_zero w | exact hn1fit) ?_
      exact validHistory_write_bind (by have := ht.2; sep_omega)
        (by split_ifs <;> first | exact h1fit | exact fits_zero w) (validHistory_pure _ _ _)
    · rfl
  refine validHistory_bind_step hvert ?_
  set s3 := (Memory.spec 0).clientState s2 (iterate sepVertStep n n 0)
  have hs3 : SepReady w n s3 := MonotoneMemInv.pres hs2 hvert
  have hedge : (Memory.spec w).ValidHistory s3
      ((Memory.spec w).clientHistory s3 (iterate sepEdgeOuter n n 0)) := by
    refine validHistory_iterate_nat (Inv := SepReady w n) n 0 (fun u hu t ht => ⟨?_, ?_⟩) hs3
    · unfold sepEdgeOuter
      refine validHistory_read_bind (by have := ht.2; sep_omega) ?_
      refine validHistory_bind_step
        (validHistory_iterate_nat (Inv := SepReady w n) n 0 (fun v hv t' ht' => ⟨?_, ?_⟩) ht)
        (validHistory_pure _ _ _)
      · unfold sepEdgeInner
        have h1 : u * n + v < n * n := idx_lt_sq (by omega) (by omega)
        have h2 : (u + n + 2) * sepNodes n + (v + 2) < sepNodes n * sepNodes n :=
          idx_lt_sq (by dsimp only [sepNodes]; omega) (by dsimp only [sepNodes]; omega)
        refine validHistory_read_bind (by have := ht'.2; sep_omega) ?_
        exact validHistory_write_bind (by have := ht'.2; sep_omega)
          (by split_ifs <;> first | exact fits_zero w | exact hn1fit) (validHistory_pure _ _ _)
      · rfl
    · exact clientResult_sepEdgeOuter _ t
  refine validHistory_bind_step hedge ?_
  set s4 := (Memory.spec 0).clientState s3 (iterate sepEdgeOuter n n 0)
  have hs4 : SepReady w n s4 := MonotoneMemInv.pres hs3 hedge
  have hek := validHistory_ekProg (c := ⟨sepNodes n, sepMatBase n, sepScrBase n, n + 1⟩)
    (src := 0) (snk := 1) ⟨by sep_omega, hw.of_le (by sep_omega), hwB⟩
    (by sep_omega) (by sep_omega) hs4.1 (by have := hs4.2; sep_omega)
  refine validHistory_bind_step hek ?_
  set s5 := (Memory.spec 0).clientState s4
    (ekProg (⟨sepNodes n, sepMatBase n, sepScrBase n, n + 1⟩, (0, 1)))
  have hs5 : SepReady w n s5 := MonotoneMemInv.pres hs4 hek
  have hex : (Memory.spec w).ValidHistory s5
      ((Memory.spec w).clientHistory s5 (iterate sepExtractStep n n 0)) := by
    refine validHistory_iterate_nat (Inv := SepReady w n) n 0 (fun v hv t ht => ⟨?_, ?_⟩) hs5
    · unfold sepExtractStep
      refine validHistory_read_bind (by have := ht.2; sep_omega) ?_
      refine validHistory_read_bind (by have := ht.2; sep_omega) ?_
      refine validHistory_read_bind (by have := ht.2; sep_omega) ?_
      refine validHistory_write_bind (by have := ht.2; sep_omega)
        (by split_ifs <;> first | exact h1fit | exact fits_zero w) ?_
      exact validHistory_write_bind (by have := ht.2; sep_omega)
        (by split_ifs <;> first | exact h1fit | exact fits_zero w) (validHistory_pure _ _ _)
    · rfl
  exact validHistory_bind_step hex (validHistory_pure _ _ _)

private theorem splitNode_equivFin_val {n : ℕ} :
    (SplitNode.equivFin n .src).1 = 0 ∧
    (SplitNode.equivFin n .snk).1 = 1 ∧
    (∀ v : Fin n, (SplitNode.equivFin n (.inV v)).1 = v.1 + 2) ∧
    (∀ v : Fin n, (SplitNode.equivFin n (.outV v)).1 = v.1 + n + 2) :=
  ⟨rfl, rfl, fun _ => rfl, fun _ => rfl⟩

private theorem sepBuild_spec {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Z A B : Vector Bool n) {st : Memory.State}
    (hZ : ∀ v : Fin n, st.mem (2 + v.1) = if vget Z v then 1 else 0)
    (hA : ∀ v : Fin n, st.mem (2 + n + v.1) = if vget A v then 1 else 0)
    (hB : ∀ v : Fin n, st.mem (2 + 2 * n + v.1) = if vget B v then 1 else 0)
    (hG : ∀ u v : Fin n, st.mem (2 + 3 * n + u.1 * n + v.1) = if G.Adj u v then 1 else 0) :
    let st1 := (Memory.spec 0).clientState st
      (fillRange ((sepMatBase n, 0), sepNodes n * sepNodes n))
    let st2 := (Memory.spec 0).clientState st1 (iterate sepVertStep n n 0)
    let st3 := (Memory.spec 0).clientState st2 (iterate sepEdgeOuter n n 0)
    (∀ a < sepMatBase n, st3.mem a = st.mem a) ∧
      ∀ x y : Fin (sepNodes n),
        st3.mem (sepMatBase n + x.1 * sepNodes n + y.1) =
          ((vertexSplitNetwork G Z A B).reindex (SplitNode.equivFin n)).cap x y := by
  intro st1 st2 st3
  have h1 := fillRange_spec (sepMatBase n) 0 (sepNodes n * sepNodes n) st
  have hlo1 : ∀ a < sepMatBase n, st1.mem a = st.mem a := fun a ha => h1.2 a (Or.inl ha)
  have hM1 : ∀ a < sepNodes n * sepNodes n, st1.mem (sepMatBase n + a) = 0 := h1.1
  have h2 := iterate_invariant_of sepVertStep n
    (fun rem (k : ℕ) t => k + rem = n ∧
      (∀ a < sepMatBase n, t.mem a = st.mem a) ∧
      (∀ x y : Fin (sepNodes n), t.mem (sepMatBase n + x.1 * sepNodes n + y.1) =
        if hy : x.1 = 0 ∧ 2 ≤ y.1 ∧ y.1 < k + 2 ∧ y.1 < n + 2 then
          if vget A ⟨y.1 - 2, by omega⟩ then n + 1 else 0
        else if hx : n + 2 ≤ x.1 ∧ x.1 < k + n + 2 ∧ x.1 < n + n + 2 ∧ y.1 = 1 then
          if vget B ⟨x.1 - n - 2, by omega⟩ then n + 1 else 0
        else if hxy : 2 ≤ x.1 ∧ x.1 < k + 2 ∧ x.1 < n + 2 ∧ y.1 = x.1 + n then
          if vget Z ⟨x.1 - 2, by omega⟩ = false then 1 else 0
        else 0))
    (fun rem k t ⟨hsum, hlo, hmat⟩ => by
      have hk : k < n := by omega
      have hzk : t.mem (2 + k) = if vget Z ⟨k, hk⟩ then 1 else 0 := by
        rw [hlo _ (by dsimp only [sepMatBase]; omega)]; exact hZ ⟨k, hk⟩
      have hak : t.mem (2 + n + k) = if vget A ⟨k, hk⟩ then 1 else 0 := by
        rw [hlo _ (by dsimp only [sepMatBase]; omega)]; exact hA ⟨k, hk⟩
      have hbk : t.mem (2 + 2 * n + k) = if vget B ⟨k, hk⟩ then 1 else 0 := by
        rw [hlo _ (by dsimp only [sepMatBase]; omega)]; exact hB ⟨k, hk⟩
      unfold sepVertStep
      rw [clientResult_bind_read, clientResult_bind_read, clientResult_bind_read,
        clientResult_bind_write, clientResult_bind_write, clientResult_bind_write,
        clientResult_pure,
        clientState_bind_read, clientState_bind_read, clientState_bind_read,
        clientState_bind_write, clientState_bind_write, clientState_bind_write,
        clientState_pure]
      dsimp only
      set aA := sepMatBase n + (k + 2)
      set aB := sepMatBase n + (k + n + 2) * sepNodes n + 1
      set aZ := sepMatBase n + (k + 2) * sepNodes n + (k + n + 2)
      have hneAZ : aA ≠ aZ := by
        intro h
        have hxy := fin_mul_add_inj (M := sepNodes n)
          (x₁ := ⟨0, by dsimp only [sepNodes]; omega⟩)
          (y₁ := ⟨k + 2, by dsimp only [sepNodes]; omega⟩)
          (x₂ := ⟨k + 2, by dsimp only [sepNodes]; omega⟩)
          (y₂ := ⟨k + n + 2, by dsimp only [sepNodes]; omega⟩)
          (by dsimp only [aA, aZ] at h ⊢; omega)
        have := congrArg Fin.val hxy.1; dsimp only at this; omega
      have hneAB : aA ≠ aB := by
        intro h
        have hxy := fin_mul_add_inj (M := sepNodes n)
          (x₁ := ⟨0, by dsimp only [sepNodes]; omega⟩)
          (y₁ := ⟨k + 2, by dsimp only [sepNodes]; omega⟩)
          (x₂ := ⟨k + n + 2, by dsimp only [sepNodes]; omega⟩)
          (y₂ := ⟨1, by dsimp only [sepNodes]; omega⟩) (by dsimp only [aA, aB] at h ⊢; omega)
        have := congrArg Fin.val hxy.1; dsimp only at this; omega
      have hneBZ : aB ≠ aZ := by
        intro h
        have hxy := fin_mul_add_inj (M := sepNodes n)
          (x₁ := ⟨k + n + 2, by dsimp only [sepNodes]; omega⟩)
          (y₁ := ⟨1, by dsimp only [sepNodes]; omega⟩)
          (x₂ := ⟨k + 2, by dsimp only [sepNodes]; omega⟩)
          (y₂ := ⟨k + n + 2, by dsimp only [sepNodes]; omega⟩)
          (by dsimp only [aB, aZ] at h ⊢; omega)
        have := congrArg Fin.val hxy.1; dsimp only at this; omega
      refine ⟨by omega, fun a ha => ?_, fun x y => ?_⟩
      · rw [Function.update_of_ne (by dsimp only [aZ]; omega),
          Function.update_of_ne (by dsimp only [aB]; omega),
          Function.update_of_ne (by dsimp only [aA]; omega)]
        exact hlo a ha
      · set addr := sepMatBase n + x.1 * sepNodes n + y.1
        by_cases hz : addr = aZ
        · rw [hz, Function.update_self, hzk]
          have hxy := fin_mul_add_inj (M := sepNodes n) (x₁ := x) (y₁ := y)
            (x₂ := ⟨k + 2, by dsimp only [sepNodes]; omega⟩)
            (y₂ := ⟨k + n + 2, by dsimp only [sepNodes]; omega⟩)
            (by dsimp only [addr, aZ] at hz ⊢; omega)
          have hxv : x.1 = k + 2 := congrArg Fin.val hxy.1
          have hyv : y.1 = k + n + 2 := congrArg Fin.val hxy.2
          rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left (by omega)]
          have hfin : (⟨x.1 - 2, by omega⟩ : Fin n) = ⟨k, hk⟩ := Fin.ext (by dsimp only; omega)
          rw [hfin]; cases vget Z ⟨k, hk⟩ <;> rfl
        · rw [Function.update_of_ne hz]
          by_cases hb : addr = aB
          · rw [hb, Function.update_self, hbk]
            have hxy := fin_mul_add_inj (M := sepNodes n) (x₁ := x) (y₁ := y)
              (x₂ := ⟨k + n + 2, by dsimp only [sepNodes]; omega⟩)
              (y₂ := ⟨1, by dsimp only [sepNodes]; omega⟩)
              (by dsimp only [addr, aB] at hb ⊢; omega)
            have hxv : x.1 = k + n + 2 := congrArg Fin.val hxy.1
            have hyv : y.1 = 1 := congrArg Fin.val hxy.2
            rw [dite_eq_right (by omega), dite_eq_left (by omega)]
            have hfin : (⟨x.1 - n - 2, by omega⟩ : Fin n) = ⟨k, hk⟩ :=
              Fin.ext (by dsimp only; omega)
            rw [hfin]; cases vget B ⟨k, hk⟩ <;> rfl
          · rw [Function.update_of_ne hb]
            by_cases ha : addr = aA
            · rw [ha, Function.update_self, hak]
              have hxy := fin_mul_add_inj (M := sepNodes n) (x₁ := x) (y₁ := y)
                (x₂ := ⟨0, by dsimp only [sepNodes]; omega⟩)
                (y₂ := ⟨k + 2, by dsimp only [sepNodes]; omega⟩)
                (by dsimp only [addr, aA] at ha ⊢; omega)
              have hxv : x.1 = 0 := congrArg Fin.val hxy.1
              have hyv : y.1 = k + 2 := congrArg Fin.val hxy.2
              rw [dite_eq_left (by omega)]
              have hfin : (⟨y.1 - 2, by omega⟩ : Fin n) = ⟨k, hk⟩ :=
                Fin.ext (by dsimp only; omega)
              rw [hfin]; cases vget A ⟨k, hk⟩ <;> rfl
            · rw [Function.update_of_ne ha, hmat x y]
              by_cases h1 : x.1 = 0 ∧ 2 ≤ y.1 ∧ y.1 < k + 2 ∧ y.1 < n + 2
              · rw [dite_eq_left h1,
                  dite_eq_left (by omega : x.1 = 0 ∧ 2 ≤ y.1 ∧ y.1 < k + 1 + 2 ∧ y.1 < n + 2)]
              · have h1' : ¬(x.1 = 0 ∧ 2 ≤ y.1 ∧ y.1 < k + 1 + 2 ∧ y.1 < n + 2) := by
                  intro ⟨hx0, hy2, hyk, hyn⟩
                  apply h1; refine ⟨hx0, hy2, ?_, hyn⟩
                  by_cases hye : y.1 = k + 2
                  · exfalso; apply ha; dsimp only [addr, aA]; rw [hx0, hye]; simp
                  · omega
                rw [dite_eq_right h1, dite_eq_right h1']
                by_cases h2 : n + 2 ≤ x.1 ∧ x.1 < k + n + 2 ∧ x.1 < n + n + 2 ∧ y.1 = 1
                · rw [dite_eq_left h2,
                    dite_eq_left (by omega :
                      n + 2 ≤ x.1 ∧ x.1 < k + 1 + n + 2 ∧ x.1 < n + n + 2 ∧ y.1 = 1)]
                · have h2' : ¬(n + 2 ≤ x.1 ∧ x.1 < k + 1 + n + 2 ∧
                      x.1 < n + n + 2 ∧ y.1 = 1) := by
                    intro ⟨hxn, hxk, hxn2, hy1⟩
                    apply h2; refine ⟨hxn, ?_, hxn2, hy1⟩
                    by_cases hxe : x.1 = k + n + 2
                    · exfalso; apply hb; dsimp only [addr, aB]; rw [hxe, hy1]
                    · omega
                  rw [dite_eq_right h2, dite_eq_right h2']
                  by_cases h3 : 2 ≤ x.1 ∧ x.1 < k + 2 ∧ x.1 < n + 2 ∧ y.1 = x.1 + n
                  · rw [dite_eq_left h3,
                      dite_eq_left (by omega :
                        2 ≤ x.1 ∧ x.1 < k + 1 + 2 ∧ x.1 < n + 2 ∧ y.1 = x.1 + n)]
                  · have h3' : ¬(2 ≤ x.1 ∧ x.1 < k + 1 + 2 ∧ x.1 < n + 2 ∧ y.1 = x.1 + n) := by
                      intro ⟨hx2, hxk, hxn, hyx⟩
                      apply h3; refine ⟨hx2, ?_, hxn, hyx⟩
                      by_cases hxe : x.1 = k + 2
                      · exfalso; apply hz; dsimp only [addr, aZ]; rw [hxe, hyx, hxe]; omega
                      · omega
                    rw [dite_eq_right h3, dite_eq_right h3'])
    (n := n) (a := 0) (s := st1) ⟨Nat.zero_add _, hlo1, fun x y => by
      rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
        Nat.add_assoc]
      exact hM1 _ (idx_lt_sq x.2 y.2)⟩
  have h2r : (Memory.spec 0).clientResult st1 (iterate sepVertStep n n 0) = n := by
    have := h2.1; omega
  have h3 := iterate_invariant_of sepEdgeOuter n
    (fun rem (ku : ℕ) t => ku + rem = n ∧
      (∀ a < sepMatBase n, t.mem a = st.mem a) ∧
      (∀ x y : Fin (sepNodes n), t.mem (sepMatBase n + x.1 * sepNodes n + y.1) =
        if hy : x.1 = 0 ∧ 2 ≤ y.1 ∧ y.1 < n + 2 then
          if vget A ⟨y.1 - 2, by omega⟩ then n + 1 else 0
        else if hx : n + 2 ≤ x.1 ∧ x.1 < n + n + 2 ∧ y.1 = 1 then
          if vget B ⟨x.1 - n - 2, by omega⟩ then n + 1 else 0
        else if hxy : 2 ≤ x.1 ∧ x.1 < n + 2 ∧ y.1 = x.1 + n then
          if vget Z ⟨x.1 - 2, by omega⟩ = false then 1 else 0
        else if he : n + 2 ≤ x.1 ∧ x.1 < ku + n + 2 ∧ x.1 < n + n + 2 ∧
            2 ≤ y.1 ∧ y.1 < n + 2 then
          if G.Adj ⟨x.1 - n - 2, by omega⟩ ⟨y.1 - 2, by omega⟩ then n + 1 else 0
        else 0))
    (fun rem ku t ⟨hsum, hlo, hmat⟩ => by
      have hku : ku < n := by omega
      have hinner := iterate_invariant_of sepEdgeInner (n, ku)
        (fun remv (kv : ℕ) t' => kv + remv = n ∧
          (∀ a < sepMatBase n, t'.mem a = st.mem a) ∧
          (∀ x y : Fin (sepNodes n), t'.mem (sepMatBase n + x.1 * sepNodes n + y.1) =
            if hy : x.1 = 0 ∧ 2 ≤ y.1 ∧ y.1 < n + 2 then
              if vget A ⟨y.1 - 2, by omega⟩ then n + 1 else 0
            else if hx : n + 2 ≤ x.1 ∧ x.1 < n + n + 2 ∧ y.1 = 1 then
              if vget B ⟨x.1 - n - 2, by omega⟩ then n + 1 else 0
            else if hxy : 2 ≤ x.1 ∧ x.1 < n + 2 ∧ y.1 = x.1 + n then
              if vget Z ⟨x.1 - 2, by omega⟩ = false then 1 else 0
            else if he : n + 2 ≤ x.1 ∧ x.1 < ku + n + 2 ∧ x.1 < n + n + 2 ∧
                2 ≤ y.1 ∧ y.1 < n + 2 then
              if G.Adj ⟨x.1 - n - 2, by omega⟩ ⟨y.1 - 2, by omega⟩ then n + 1 else 0
            else if he' : x.1 = ku + n + 2 ∧ 2 ≤ y.1 ∧ y.1 < kv + 2 ∧ y.1 < n + 2 then
              if G.Adj ⟨ku, hku⟩ ⟨y.1 - 2, by omega⟩ then n + 1 else 0
            else 0))
        (fun remv kv t' ⟨hsumv, hlo', hmat'⟩ => by
          have hkv : kv < n := by omega
          have hge : t'.mem (2 + 3 * n + ku * n + kv) =
              if G.Adj ⟨ku, hku⟩ ⟨kv, hkv⟩ then 1 else 0 := by
            have hlt : ku * n + kv < n * n := idx_lt_sq hku hkv
            rw [hlo' _ (by dsimp only [sepMatBase]; omega)]
            exact hG ⟨ku, hku⟩ ⟨kv, hkv⟩
          unfold sepEdgeInner
          rw [clientResult_bind_read, clientState_bind_read, clientResult_bind_write,
            clientState_bind_write, clientResult_pure, clientState_pure]
          dsimp only
          refine ⟨by omega, fun a ha => ?_, fun x y => ?_⟩
          · rw [Function.update_of_ne (by omega)]; exact hlo' a ha
          · by_cases heq : sepMatBase n + x.1 * sepNodes n + y.1 =
                sepMatBase n + (ku + n + 2) * sepNodes n + (kv + 2)
            · rw [heq, Function.update_self, hge]
              have hxy := fin_mul_add_inj (M := sepNodes n) (x₁ := x) (y₁ := y)
                (x₂ := ⟨ku + n + 2, by dsimp only [sepNodes]; omega⟩)
                (y₂ := ⟨kv + 2, by dsimp only [sepNodes]; omega⟩) (by dsimp only; omega)
              have hxu : x.1 = ku + n + 2 := congrArg Fin.val hxy.1
              have hyv : y.1 = kv + 2 := congrArg Fin.val hxy.2
              rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
                dite_eq_right (by omega), dite_eq_left (by omega)]
              have hfin : (⟨y.1 - 2, by omega⟩ : Fin n) = ⟨kv, hkv⟩ :=
                Fin.ext (by dsimp only; omega)
              rw [hfin]
              by_cases h : G.Adj ⟨ku, hku⟩ ⟨kv, hkv⟩ <;> simp [h]
            · rw [Function.update_of_ne heq, hmat' x y]
              by_cases h1 : x.1 = 0 ∧ 2 ≤ y.1 ∧ y.1 < n + 2
              · rw [dite_eq_left h1, dite_eq_left h1]
              · rw [dite_eq_right h1, dite_eq_right h1]
                by_cases h2 : n + 2 ≤ x.1 ∧ x.1 < n + n + 2 ∧ y.1 = 1
                · rw [dite_eq_left h2, dite_eq_left h2]
                · rw [dite_eq_right h2, dite_eq_right h2]
                  by_cases h3 : 2 ≤ x.1 ∧ x.1 < n + 2 ∧ y.1 = x.1 + n
                  · rw [dite_eq_left h3, dite_eq_left h3]
                  · rw [dite_eq_right h3, dite_eq_right h3]
                    by_cases h4 : n + 2 ≤ x.1 ∧ x.1 < ku + n + 2 ∧ x.1 < n + n + 2 ∧
                        2 ≤ y.1 ∧ y.1 < n + 2
                    · rw [dite_eq_left h4, dite_eq_left h4]
                    · rw [dite_eq_right h4, dite_eq_right h4]
                      by_cases h5 : x.1 = ku + n + 2 ∧ 2 ≤ y.1 ∧ y.1 < kv + 2 ∧ y.1 < n + 2
                      · rw [dite_eq_left h5, dite_eq_left (by omega)]
                      · rw [dite_eq_right h5, dite_eq_right]
                        intro ⟨hxu, hy2, hyk, hyn⟩
                        apply h5; refine ⟨hxu, hy2, ?_, hyn⟩
                        by_cases hye : y.1 = kv + 2
                        · exfalso; apply heq; rw [hxu, hye]
                        · omega)
        (n := n) (a := 0) (s := t) ⟨Nat.zero_add _, hlo, fun x y => by
          rw [hmat x y]
          by_cases h1 : x.1 = 0 ∧ 2 ≤ y.1 ∧ y.1 < n + 2
          · rw [dite_eq_left h1, dite_eq_left h1]
          · rw [dite_eq_right h1, dite_eq_right h1]
            by_cases h2 : n + 2 ≤ x.1 ∧ x.1 < n + n + 2 ∧ y.1 = 1
            · rw [dite_eq_left h2, dite_eq_left h2]
            · rw [dite_eq_right h2, dite_eq_right h2]
              by_cases h3 : 2 ≤ x.1 ∧ x.1 < n + 2 ∧ y.1 = x.1 + n
              · rw [dite_eq_left h3, dite_eq_left h3]
              · rw [dite_eq_right h3, dite_eq_right h3]
                by_cases h4 : n + 2 ≤ x.1 ∧ x.1 < ku + n + 2 ∧ x.1 < n + n + 2 ∧
                    2 ≤ y.1 ∧ y.1 < n + 2
                · rw [dite_eq_left h4, dite_eq_left h4]
                · rw [dite_eq_right h4, dite_eq_right h4, dite_eq_right (by omega)]⟩
      have hinner_r : (Memory.spec 0).clientResult t (iterate sepEdgeInner (n, ku) n 0) = n := by
        have := hinner.1; omega
      unfold sepEdgeOuter
      rw [clientResult_bind_read, clientResult_bind, clientResult_pure,
        clientState_bind_read, clientState_bind, clientState_pure]
      refine ⟨by omega, hinner.2.1, fun x y => ?_⟩
      dsimp only
      have hmat_i := hinner.2.2 x y
      rw [hinner_r] at hmat_i
      rw [hmat_i]
      by_cases h1 : x.1 = 0 ∧ 2 ≤ y.1 ∧ y.1 < n + 2
      · rw [dite_eq_left h1, dite_eq_left h1]
      · rw [dite_eq_right h1, dite_eq_right h1]
        by_cases h2 : n + 2 ≤ x.1 ∧ x.1 < n + n + 2 ∧ y.1 = 1
        · rw [dite_eq_left h2, dite_eq_left h2]
        · rw [dite_eq_right h2, dite_eq_right h2]
          by_cases h3 : 2 ≤ x.1 ∧ x.1 < n + 2 ∧ y.1 = x.1 + n
          · rw [dite_eq_left h3, dite_eq_left h3]
          · rw [dite_eq_right h3, dite_eq_right h3]
            by_cases h4 : n + 2 ≤ x.1 ∧ x.1 < ku + n + 2 ∧ x.1 < n + n + 2 ∧
                2 ≤ y.1 ∧ y.1 < n + 2
            · rw [dite_eq_left h4,
                dite_eq_left (by omega : n + 2 ≤ x.1 ∧ x.1 < ku + 1 + n + 2 ∧
                  x.1 < n + n + 2 ∧ 2 ≤ y.1 ∧ y.1 < n + 2)]
            · rw [dite_eq_right h4]
              by_cases hxu : x.1 = ku + n + 2 ∧ 2 ≤ y.1 ∧ y.1 < n + 2
              · rw [dite_eq_left (by omega : x.1 = ku + n + 2 ∧ 2 ≤ y.1 ∧ y.1 < n + 2 ∧
                    y.1 < n + 2),
                  dite_eq_left (by omega : n + 2 ≤ x.1 ∧ x.1 < ku + 1 + n + 2 ∧
                    x.1 < n + n + 2 ∧ 2 ≤ y.1 ∧ y.1 < n + 2)]
                have hfin : (⟨x.1 - n - 2, by omega⟩ : Fin n) = ⟨ku, hku⟩ :=
                  Fin.ext (by dsimp only; omega)
                rw [hfin]
              · rw [dite_eq_right (by omega), dite_eq_right (by omega)])
    (n := n) (a := 0) (s := st2) ⟨Nat.zero_add _, h2.2.1, fun x y => by
      have hm2 := h2.2.2 x y
      rw [h2r] at hm2
      rw [hm2]
      by_cases h1 : x.1 = 0 ∧ 2 ≤ y.1 ∧ y.1 < n + 2
      · rw [dite_eq_left (by omega : x.1 = 0 ∧ 2 ≤ y.1 ∧ y.1 < n + 2 ∧ y.1 < n + 2),
          dite_eq_left h1]
      · rw [dite_eq_right (by omega), dite_eq_right h1]
        by_cases h2' : n + 2 ≤ x.1 ∧ x.1 < n + n + 2 ∧ y.1 = 1
        · rw [dite_eq_left (by omega : n + 2 ≤ x.1 ∧ x.1 < n + n + 2 ∧ x.1 < n + n + 2 ∧ y.1 = 1),
            dite_eq_left h2']
        · rw [dite_eq_right (by omega), dite_eq_right h2']
          by_cases h3' : 2 ≤ x.1 ∧ x.1 < n + 2 ∧ y.1 = x.1 + n
          · rw [dite_eq_left (by omega : 2 ≤ x.1 ∧ x.1 < n + 2 ∧ x.1 < n + 2 ∧ y.1 = x.1 + n),
              dite_eq_left h3']
          · rw [dite_eq_right (by omega), dite_eq_right h3', dite_eq_right (by omega)]⟩
  have h3r : (Memory.spec 0).clientResult st2 (iterate sepEdgeOuter n n 0) = n := by
    have := h3.1; omega
  refine ⟨h3.2.1, fun x y => ?_⟩
  have hm3 := h3.2.2 x y
  rw [h3r] at hm3
  rw [hm3]
  obtain ⟨hsrc0, hsnk1, hinV, houtV⟩ := splitNode_equivFin_val (n := n)
  have hx_eq : x = SplitNode.equivFin n ((SplitNode.equivFin n).symm x) :=
    ((SplitNode.equivFin n).apply_symm_apply x).symm
  have hy_eq : y = SplitNode.equivFin n ((SplitNode.equivFin n).symm y) :=
    ((SplitNode.equivFin n).apply_symm_apply y).symm
  change _ = (vertexSplitNetwork G Z A B).cap ((SplitNode.equivFin n).symm x)
    ((SplitNode.equivFin n).symm y)
  generalize hsx : (SplitNode.equivFin n).symm x = sx at hx_eq
  generalize hsy : (SplitNode.equivFin n).symm y = sy at hy_eq
  have hxval : x.1 = (SplitNode.equivFin n sx).1 := congrArg Fin.val hx_eq
  have hyval : y.1 = (SplitNode.equivFin n sy).1 := congrArg Fin.val hy_eq
  cases sx <;> cases sy <;>
    simp only [hsrc0, hsnk1, hinV, houtV, vertexSplitNetwork, vertexSplitCap] at hxval hyval ⊢
  all_goals
    try (rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
      dite_eq_right (by omega)])
  · rename_i v
    rw [dite_eq_left (by have := v.2; omega)]
    have hv : (⟨y.1 - 2, by have := v.2; omega⟩ : Fin n) = v := Fin.ext (by dsimp only; omega)
    rw [hv]
  · rename_i u v
    by_cases huv : u = v
    · subst huv
      rw [dite_eq_right (by omega), dite_eq_right (by omega),
        dite_eq_left (by have := u.2; omega)]
      have hu : (⟨x.1 - 2, by have := u.2; omega⟩ : Fin n) = u := Fin.ext (by dsimp only; omega)
      rw [hu]; simp
    · have hne : u.1 ≠ v.1 := fun h => huv (Fin.ext h)
      rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
        dite_eq_right (by omega), ite_eq_right (fun h => huv h.1)]
  · rename_i u
    rw [dite_eq_right (by omega), dite_eq_left (by have := u.2; omega)]
    have hu : (⟨x.1 - n - 2, by have := u.2; omega⟩ : Fin n) = u := Fin.ext (by dsimp only; omega)
    rw [hu]
  · rename_i u v
    rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
      dite_eq_left (by have := u.2; have := v.2; omega)]
    have hu : (⟨x.1 - n - 2, by have := u.2; omega⟩ : Fin n) = u := Fin.ext (by dsimp only; omega)
    have hv : (⟨y.1 - 2, by have := v.2; omega⟩ : Fin n) = v := Fin.ext (by dsimp only; omega)
    rw [hu, hv]

private theorem sepExtract_spec {n : ℕ} (st : Memory.State) :
    let st' := (Memory.spec 0).clientState st (iterate sepExtractStep n n 0)
    (∀ v : Fin n, st'.mem (sepOutBase n + v.1) =
      if st.mem (2 + v.1) = 0 ∧
         st.mem (sepScrBase n + sepNodes n * sepNodes n + (v.1 + 2)) < sepNodes n ∧
         st.mem (sepScrBase n + sepNodes n * sepNodes n + (v.1 + n + 2)) = sepNodes n
      then 1 else 0) ∧
    (∀ v : Fin n, st'.mem (sepSideBase n + v.1) =
      if st.mem (sepScrBase n + sepNodes n * sepNodes n + (v.1 + n + 2)) < sepNodes n
      then 1 else 0) := by
  have h := iterate_invariant_of sepExtractStep n
    (fun rem (k : ℕ) t => k + rem = n ∧
      (∀ a < sepOutBase n, t.mem a = st.mem a) ∧
      (∀ v : Fin n, v.1 < k → t.mem (sepOutBase n + v.1) =
        if st.mem (2 + v.1) = 0 ∧
           st.mem (sepScrBase n + sepNodes n * sepNodes n + (v.1 + 2)) < sepNodes n ∧
           st.mem (sepScrBase n + sepNodes n * sepNodes n + (v.1 + n + 2)) = sepNodes n
        then 1 else 0) ∧
      (∀ v : Fin n, v.1 < k → t.mem (sepSideBase n + v.1) =
        if st.mem (sepScrBase n + sepNodes n * sepNodes n + (v.1 + n + 2)) < sepNodes n
        then 1 else 0))
    (fun rem k t ⟨hsum, hlo, hout, hside⟩ => by
      have hz : t.mem (2 + k) = st.mem (2 + k) := hlo _ (by sep_omega)
      have hdin : t.mem (sepScrBase n + sepNodes n * sepNodes n + (k + 2)) =
          st.mem (sepScrBase n + sepNodes n * sepNodes n + (k + 2)) := hlo _ (by sep_omega)
      have hdout : t.mem (sepScrBase n + sepNodes n * sepNodes n + (k + n + 2)) =
          st.mem (sepScrBase n + sepNodes n * sepNodes n + (k + n + 2)) := hlo _ (by sep_omega)
      unfold sepExtractStep
      rw [clientResult_bind_read, clientResult_bind_read, clientResult_bind_read,
        clientResult_bind_write, clientResult_bind_write, clientResult_pure,
        clientState_bind_read, clientState_bind_read, clientState_bind_read,
        clientState_bind_write, clientState_bind_write, clientState_pure]
      dsimp only
      refine ⟨by omega, fun a ha => ?_, fun v hv => ?_, fun v hv => ?_⟩
      · rw [Function.update_of_ne (by dsimp only [sepSideBase]; omega),
          Function.update_of_ne (by omega)]
        exact hlo a ha
      · rw [Function.update_of_ne (by have := v.2; dsimp only [sepSideBase]; omega)]
        by_cases hvk : v.1 = k
        · rw [hvk, Function.update_self, hz, hdin, hdout]
        · rw [Function.update_of_ne (by omega)]; exact hout v (by omega)
      · by_cases hvk : v.1 = k
        · rw [hvk, Function.update_self, hdout]
        · rw [Function.update_of_ne (by omega),
            Function.update_of_ne (by dsimp only [sepSideBase]; omega)]
          exact hside v (by omega))
    (n := n) (a := 0) (s := st)
    ⟨Nat.zero_add _, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ h => absurd h (Nat.not_lt_zero _)⟩
  exact ⟨fun v => h.2.2.1 v (by omega), fun v => h.2.2.2 v (by omega)⟩

/-- **Minimum vertex separator by vertex splitting on the Word-RAM:** one uniform flat program over
`Basis.exact` that, on `encodeSepInput G Z A B` for any `G : SimpleGraph (Fin n)` and `Z A B :
Vector Bool n`, halts within `C * (n + 1) ^ 5` instructions at every word width fitting
`ekBound (n + n + 2) (n + 1)`. It returns the minimum separator size `out.sep.length`, stores the
`0`/`1` separator indicator at `sepOutAddr`, and stores the side labelling certificate `out.side` at
`sepSideAddr`. -/
theorem exists_minSeparator_program :
    ∃ (R C pc : ℕ), 0 < C ∧ ∃ prog : Program .exact R,
      ∀ {n w : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (Z A B : Vector Bool n),
        Fits w (ekBound (n + n + 2) (n + 1)) →
        ∃ (y : Data R) (steps res : ℕ) (out : SeparatorOutput n),
          Runs w prog (State.init (encodeSepInput G Z A B)) ⟨pc, y⟩ steps ∧
          step w prog ⟨pc, y⟩ = .halt res ∧
          steps + 1 ≤ C * (n + 1) ^ 5 ∧
          out.sep.Nodup ∧
          (∀ v ∈ out.sep, vget Z v = false) ∧
          G.IsSeparator {v | vget A v = true} {v | vget B v = true}
            ({v | vget Z v = true} ∪ {v | v ∈ out.sep}) ∧
          (∀ Y : Finset (Fin n),
            G.IsSeparator {v | vget A v = true} {v | vget B v = true}
              ({v | vget Z v = true} ∪ ↑Y) → out.sep.length ≤ Y.card) ∧
          (∀ {u v : Fin n}, G.Adj u v → vget Z u = false → vget Z v = false →
            u ∉ out.sep → v ∉ out.sep → vget out.side u = vget out.side v) ∧
          (∀ {v : Fin n}, vget A v = true → vget Z v = false → v ∉ out.sep →
            vget out.side v = true) ∧
          (∀ {v : Fin n}, vget B v = true → vget out.side v = false) ∧
          res = out.sep.length ∧
          (∀ v : Fin n, y.mem (sepOutAddr n v.1) = if v ∈ out.sep then 1 else 0) ∧
          (∀ v : Fin n, y.mem (sepSideAddr n v.1) = if vget out.side v then 1 else 0) := by
  obtain ⟨R, C₀, pc, prog, _, _, hprog⟩ :=
    sepProg_realizes.exists_standard_init_program_state_from_words 0
  refine ⟨R, 5204 * C₀ + 2, pc, by omega, prog, ?_⟩
  intro n w G _ Z A B hwB
  have hw : Fits w (sepWorkspace n) := hwB.of_le (by dsimp only [sepWorkspace, ekBound]; nlinarith)
  set st := Memory.State.init (encodeSepInput G Z A B)
  have hfr : st.frontier = 2 + 3 * n + n * n := by
    simp only [st, Memory.State.init, length_encodeSepInput]; omega
  have h1 : st.mem 1 = n := by simp [st, Memory.State.init, encodeSepInput]
  have hlen : Fits w ((encodeSepInput G Z A B).length + 1) := hw.of_le (by
    rw [length_encodeSepInput]; dsimp only [sepWorkspace]; omega)
  have hwf : Memory.WellFormed w st :=
    Memory.wellFormed_init (inputFits_encodeSepInput G Z A B hw) hlen
  have hvh : (Memory.spec w).ValidHistory st ((Memory.spec w).clientHistory st (sepProg ())) := by
    unfold sepProg
    refine validHistory_read_bind (by omega) ?_
    rw [h1]
    exact validHistory_sepMain hwf hfr hw hwB
  obtain ⟨y, steps, hruns, hhalt, hmem, _, hbound⟩ :=
    hprog w () (encodeSepInput G Z A B) (fun j => Fin.elim0 j) (Nat.zero_le _) hlen
      (inputFits_encodeSepInput G Z A B hw) ⟨by rw [h1]; exact hw, by rw [h1]; exact hwB⟩ hvh
  rw [clientState_width w (sepProg ())] at hmem
  rw [clientResult_width w (sepProg ())] at hhalt
  set st0 := (Memory.spec 0).clientState st (Memory.alloc (sepScratch n))
  have hlo0 : ∀ a < sepMatBase n, st0.mem a = st.mem a := fun a ha =>
    Memory.mem_step_of_lt_frontier st (.alloc (sepScratch n))
      (by rw [hfr]; dsimp only [sepMatBase] at ha; omega) (by simp)
  have hZ0 : ∀ v : Fin n, st0.mem (2 + v.1) = if vget Z v then 1 else 0 := fun v => by
    rw [hlo0 _ (by have := v.2; dsimp only [sepMatBase]; omega)]; exact sepInit_mem_Z G Z A B v
  have hA0 : ∀ v : Fin n, st0.mem (2 + n + v.1) = if vget A v then 1 else 0 := fun v => by
    rw [hlo0 _ (by have := v.2; dsimp only [sepMatBase]; omega)]; exact sepInit_mem_A G Z A B v
  have hB0 : ∀ v : Fin n, st0.mem (2 + 2 * n + v.1) = if vget B v then 1 else 0 := fun v => by
    rw [hlo0 _ (by have := v.2; dsimp only [sepMatBase]; omega)]; exact sepInit_mem_B G Z A B v
  have hG0 : ∀ u v : Fin n, st0.mem (2 + 3 * n + u.1 * n + v.1) = if G.Adj u v then 1 else 0 := by
    intro u v
    have hlt := idx_lt_sq u.2 v.2
    rw [hlo0 _ (by dsimp only [sepMatBase]; omega)]; exact sepInit_mem_edge G Z A B u v
  obtain ⟨hlo3, hmat3⟩ := sepBuild_spec G Z A B hZ0 hA0 hB0 hG0
  set st1 := (Memory.spec 0).clientState st0
    (fillRange ((sepMatBase n, 0), sepNodes n * sepNodes n))
  set st2 := (Memory.spec 0).clientState st1 (iterate sepVertStep n n 0)
  set st3 := (Memory.spec 0).clientState st2 (iterate sepEdgeOuter n n 0)
  set NFin := (vertexSplitNetwork G Z A B).reindex (SplitNode.equivFin n)
  have hst_ne : NFin.s ≠ NFin.t :=
    (SplitNode.equivFin n).injective.ne (by simp [vertexSplitNetwork])
  have hcap_le : ∀ x y : Fin (sepNodes n), NFin.cap x y ≤ n + 1 := fun x y => by
    change vertexSplitCap G Z A B ((SplitNode.equivFin n).symm x)
      ((SplitNode.equivFin n).symm y) ≤ n + 1
    cases (SplitNode.equivFin n).symm x <;> cases (SplitNode.equivFin n).symm y <;>
      simp only [vertexSplitCap] <;> first | omega | (split_ifs <;> omega)
  have hEk := ekProg_flow_spec (mb := sepMatBase n) (sb := sepScrBase n) (B := n + 1)
    NFin hst_ne hcap_le (le_refl _) hmat3
  have hs0 : NFin.s.1 = 0 := rfl
  have ht1 : NFin.t.1 = 1 := rfl
  rw [hs0, ht1] at hEk
  obtain ⟨hEk_frame, _, _, hdist_le, _, hminFin, _, _, hres_ek⟩ := hEk
  set st4 := (Memory.spec 0).clientState st3
    (ekProg (⟨sepNodes n, sepMatBase n, sepScrBase n, n + 1⟩, (0, 1)))
  set CFin : Finset (Fin (sepNodes n)) :=
    Finset.univ.filter fun x =>
      st4.mem (distAddr ⟨sepNodes n, sepMatBase n, sepScrBase n, n + 1⟩ x.1) < sepNodes n
  set S : Finset (SplitNode n) := Network.cutOfReindex (SplitNode.equivFin n) CFin
  have hS_min : (vertexSplitNetwork G Z A B).IsMinCut S :=
    Network.isMinCut_cutOfReindex (SplitNode.equivFin n) hminFin
  set out := separatorOfCut Z S
  obtain ⟨hOut_mem, hSide_mem⟩ := sepExtract_spec (n := n) st4
  set st5 := (Memory.spec 0).clientState st4 (iterate sepExtractStep n n 0)
  have hst_prog : (Memory.spec 0).clientState st (sepProg ()) = st5 := by
    unfold sepProg; rw [clientState_bind_read, h1]
    unfold sepMain; dsimp only
    rw [clientState_bind, clientState_bind, clientState_bind, clientState_bind,
      clientState_bind, clientState_bind, clientState_pure]
  have hres_prog : (Memory.spec 0).clientResult st (sepProg ()) =
      (Memory.spec 0).clientResult st3
        (ekProg (⟨sepNodes n, sepMatBase n, sepScrBase n, n + 1⟩, (0, 1))) := by
    unfold sepProg; rw [clientResult_bind_read, h1]
    unfold sepMain; dsimp only
    rw [clientResult_bind, clientResult_bind, clientResult_bind, clientResult_bind,
      clientResult_bind, clientResult_bind, clientResult_pure]
  have hymem : y.mem = st5.mem := by
    rw [← hst_prog]; exact congrArg Memory.State.mem hmem
  have hmc : memoryCost (sepProg ()) st ≤ 5202 * (n + 1) ^ 5 := by
    unfold sepProg
    rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read, h1]
    have h1p : 1 ≤ (n + 1) ^ 5 := Nat.one_le_pow _ _ (by omega)
    have := memoryCost_sepMain_le n st
    omega
  have hp : 1 ≤ (n + 1) ^ 5 := Nat.one_le_pow _ _ (by omega)
  refine ⟨y, steps, (Memory.spec 0).clientResult st (sepProg ()), out, hruns, hhalt, ?_,
    separatorOfCut_nodup_sep Z S,
    fun v hv => separatorOfCut_vget_eq_false_of_mem_sep hv,
    separatorOfCut_isSeparator hS_min,
    fun Y hY => separatorOfCut_length_sep_le hS_min hY,
    fun huv hu hv hus hvs => separatorOfCut_side_eq_of_adj hS_min huv hu hv hus hvs,
    fun hA hZ hvs => separatorOfCut_side_eq_true hS_min hA hZ hvs,
    fun hB => separatorOfCut_side_eq_false hS_min hB, ?_, ?_, ?_⟩
  · calc steps + 1
        ≤ C₀ * (memoryCost (sepProg ()) st + 0 + 1) + 1 := hbound
      _ ≤ C₀ * (5202 * (n + 1) ^ 5 + 1) + 1 :=
          Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) 1
      _ ≤ (5204 * C₀ + 2) * (n + 1) ^ 5 := by nlinarith
  · rw [hres_prog, hres_ek, ← Network.cutCapacity_cutOfReindex (SplitNode.equivFin n),
      separatorOfCut_length_sep_eq_cutCapacity hS_min]
  · intro v
    rw [hymem]
    have haddr : sepOutAddr n v.1 = sepOutBase n + v.1 := by
      dsimp only [sepOutAddr, sepOutBase, sepScrBase, sepMatBase, sepNodes, ekScratch]; ring
    rw [haddr, hOut_mem v]
    have hZ4 : st4.mem (2 + v.1) = if vget Z v then 1 else 0 := by
      rw [hEk_frame _ (Or.inl (by have := v.2; sep_omega)),
        hlo3 _ (by have := v.2; dsimp only [sepMatBase]; omega)]
      exact hZ0 v
    have hin_iff : st4.mem (sepScrBase n + sepNodes n * sepNodes n + (v.1 + 2)) < sepNodes n ↔
        SplitNode.inV v ∈ S := by
      have : (SplitNode.equivFin n (.inV v)).1 = v.1 + 2 := rfl
      rw [← this]
      simp [S, Network.cutOfReindex, CFin, distAddr]
    have hout_iff : st4.mem (sepScrBase n + sepNodes n * sepNodes n + (v.1 + n + 2)) = sepNodes n ↔
        SplitNode.outV v ∉ S := by
      have hle := hdist_le (SplitNode.equivFin n (.outV v))
      have : (SplitNode.equivFin n (.outV v)).1 = v.1 + n + 2 := rfl
      rw [this] at hle
      dsimp only [distAddr] at hle
      have hlt_iff : st4.mem (sepScrBase n + sepNodes n * sepNodes n + (v.1 + n + 2)) <
          sepNodes n ↔ SplitNode.outV v ∈ S := by
        rw [← this]; simp [S, Network.cutOfReindex, CFin, distAddr]
      rw [← hlt_iff]
      dsimp only [sepNodes] at hle ⊢
      omega
    have hZ_iff : st4.mem (2 + v.1) = 0 ↔ vget Z v = false := by
      rw [hZ4]; cases vget Z v <;> simp
    have hmem_sep : v ∈ out.sep ↔
        vget Z v = false ∧ SplitNode.inV v ∈ S ∧ SplitNode.outV v ∉ S := by
      simp only [out, separatorOfCut, List.mem_filter, List.mem_finRange, true_and,
        Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not, and_assoc]
    have hiff : (st4.mem (2 + v.1) = 0 ∧
        st4.mem (sepScrBase n + sepNodes n * sepNodes n + (v.1 + 2)) < sepNodes n ∧
        st4.mem (sepScrBase n + sepNodes n * sepNodes n + (v.1 + n + 2)) = sepNodes n) ↔
        v ∈ out.sep :=
      (and_congr hZ_iff (and_congr hin_iff hout_iff)).trans hmem_sep.symm
    by_cases hp : v ∈ out.sep
    · rw [ite_eq_left (hiff.mpr hp), ite_eq_left hp]
    · rw [ite_eq_right (fun h => hp (hiff.mp h)), ite_eq_right hp]
  · intro v
    rw [hymem]
    have haddr : sepSideAddr n v.1 = sepSideBase n + v.1 := by
      dsimp only [sepSideAddr, sepSideBase, sepOutBase, sepScrBase, sepMatBase, sepNodes,
        ekScratch]
      ring
    rw [haddr, hSide_mem v]
    have hout_iff : st4.mem (sepScrBase n + sepNodes n * sepNodes n + (v.1 + n + 2)) <
        sepNodes n ↔ vget out.side v = true := by
      have : (SplitNode.equivFin n (.outV v)).1 = v.1 + n + 2 := rfl
      rw [← this]
      simp [out, separatorOfCut, vget, S, Network.cutOfReindex, CFin, distAddr]
    by_cases hp : vget out.side v = true
    · rw [ite_eq_left (hout_iff.mpr hp), ite_eq_left hp]
    · rw [ite_eq_right (fun h => hp (hout_iff.mp h)), ite_eq_right hp]

end UniformVertexSeparator

end Cslib.Algorithms.WordRAM.EdmondsKarp
