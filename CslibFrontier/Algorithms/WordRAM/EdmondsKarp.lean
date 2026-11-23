/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.MaxFlow.EdmondsKarp
public import CslibFrontier.Algorithms.Lean.GomoryHu.WeightedCut
public import CslibFrontier.Computability.WordRAM.Realization.Absorb
public import CslibFrontier.Computability.WordRAM.Realization.ProgFrame
public import CslibFrontier.Computability.WordRAM.Realization.WordEncoding.Equiv
import CslibFrontier.Tactic.Realize
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Dense Edmonds–Karp maximum flow on the Word-RAM

A memory-client program `ekProg` computing a maximum flow and a minimum `s`–`t` cut of the
network whose capacities are an `n × n` matrix `W` stored in row-major order, with the
shortest-augmenting-path rule of Edmonds and Karp ([EdmondsKarp1972]). It is a subroutine with a
relocatable layout: the context `c : Ctx` places the capacity matrix at `c.matBase`, a scratch
area of `ekScratch n` words at `sb`, and bounds the capacities by `B`.

Each round runs a layered breadth-first search on the residual graph (`bfsProg`), which stores
the residual distances `Flow.resDist` at `distAddr` and a parent of every reached vertex at
`predAddr`, then walks the parent pointers from `t` back to `s` twice: once to compute the
bottleneck and once to push it (`bnStep`, `augStep`). Every round augments along a shortest
augmenting path, so `Network.shortestAugmentingSeq_length_le` bounds the number of rounds by
`n * n * (n / 2) < n ^ 3`. When `t` is no longer reached, the reached set is a minimum cut, and
`cutOuterStep` sums the capacities leaving it.

Every arithmetic operation is guarded so that its result is at most `ekBound n B`; the guards
always pass on actual runs, since flows never exceed capacities. The breadth-first search expands
each vertex at most once, so a round costs `O(n ^ 2)` memory operations and the whole computation
`O(n ^ 5)`.

## Main definitions

* `Cslib.Algorithms.WordRAM.EdmondsKarp.Ctx`, `Ctx.equiv`, `distAddr`, `ekScratch`, `ekBound`,
  `CtxFits`: the solver context, output distance address, scratch size, and word bound.
* `Cslib.Algorithms.WordRAM.EdmondsKarp.ekProg`: the solver, and `ekCost`, its memory budget.
* `Cslib.Algorithms.WordRAM.EdmondsKarp.fillRange`: fill a range of memory with one word.

## Main results

* `Cslib.Algorithms.WordRAM.EdmondsKarp.ekProg_spec`: the reached set of the final search is a
  minimum `s`–`t` cut of `cutWeight W`, the returned value is its weight, and memory outside the
  scratch area is unchanged.
* `Cslib.Algorithms.WordRAM.EdmondsKarp.memoryCost_ekProg_le`: at most `ekCost n = 20 (n + 1) ^ 5`
  memory operations from any state.
* `Cslib.Algorithms.WordRAM.EdmondsKarp.ekProg_realizes`,
  `Cslib.Algorithms.WordRAM.EdmondsKarp.validHistory_ekProg`,
  `Cslib.Algorithms.WordRAM.EdmondsKarp.preservesAt_ekProg`,
  `Cslib.Algorithms.WordRAM.EdmondsKarp.ekProg_result_le`: compilation to `Basis.exact` code,
  admissibility on a well-formed memory with the scratch area allocated, the frame, and the bound
  `n * n * B + B` on the returned word, for clients that call `ekProg`.
* `Cslib.Algorithms.WordRAM.EdmondsKarp.fillRange_realizes`, `fillRange_spec`,
  `memoryCost_fillRange_le`, `validHistory_fillRange`: the same for `fillRange`.

## References

* [EdmondsKarp1972]
-/

public section

namespace Cslib.Algorithms.WordRAM.EdmondsKarp

open Cslib.Algorithms.Lean.MaxFlow Cslib.Algorithms.Lean.GomoryHu Cslib.WeightedCut
open Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization
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
  dsimp only
  have hn : 0 < n := Nat.zero_lt_of_lt s.2
  have hframe : ∀ a, (a < sb ∨ sb + ekScratch n ≤ a) →
      ((Memory.spec 0).clientState st (ekProg (⟨n, mb, sb, B⟩, (s.1, t.1)))).mem a = st.mem a :=
    fun a ha => preservesAt_ekProg (c := ⟨n, mb, sb, B⟩) (src := s.1) (snk := t.1) s.2 ha st
  let N : Network (Fin n) := Network.mk W s t
  set s1 := (Memory.spec 0).clientState st (fillRange ((flowAddr ⟨n, mb, sb, B⟩ 0 0, 0), n * n))
  have hs1 := fillRange_spec (flowAddr ⟨n, mb, sb, B⟩ 0 0) 0 (n * n) st
  have hW1 : MatLoaded n mb W s1 := fun u v => by
    rw [hs1.2 _ (Or.inl (by have := idx_lt_sq u.2 v.2; ek_omega))]
    exact hW u v
  have hf1 : FlowStored sb (Network.Flow.zero N) s1 := fun x y => by
    have h := hs1.1 (x.1 * n + y.1) (idx_lt_sq x.2 y.2)
    have he : flowAddr ⟨n, mb, sb, B⟩ 0 0 + (x.1 * n + y.1) = sb + x.1 * n + y.1 := by
      dsimp only [flowAddr]; ring
    rw [he] at h
    exact h
  have hloop := iterate_invariant_of roundStep (⟨n, mb, sb, B⟩, (s.1, t.1))
    (fun rem (sv : ℕ) tt => sv ≤ 1 ∧ MatLoaded n mb W tt ∧
      ∃ (k : ℕ) (flows : ℕ → N.Flow) (paths : ℕ → List (Fin n)),
        N.IsShortestAugmentingSeq k flows paths ∧ FlowStored sb (flows k) tt ∧
        (sv = 0 → k + rem = n * n * n) ∧
        (sv = 1 → (∀ x : Fin n, tt.mem (distAddr ⟨n, mb, sb, B⟩ x.1) = (flows k).resDist x) ∧
          (flows k).resDist t = n))
    (fun rem sv tt ⟨hsv, hWt, k, flows, paths, hseq, hft, h0, h1⟩ => by
      have hWt' : ∀ tt', (∀ a, (a < sb ∨ sb + ekScratch n ≤ a) → tt'.mem a = tt.mem a) →
          MatLoaded n mb W tt' := fun tt' hfr u v => by
        rw [hfr _ (Or.inl (by have := idx_lt_sq u.2 v.2; omega))]
        exact hWt u v
      have hfr_round : ∀ a, (a < sb ∨ sb + ekScratch n ≤ a) →
          ((Memory.spec 0).clientState tt (roundStep ((⟨n, mb, sb, B⟩, (s.1, t.1)), sv))).mem a =
            tt.mem a :=
        fun a ha => preservesAt_roundStep (d := ((⟨n, mb, sb, B⟩, (s.1, t.1)), sv)) s.2 ha tt
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
              ((Memory.spec 0).clientState tt (roundStep ((⟨n, mb, sb, B⟩, (s.1, t.1)), 0))) := by
            simp only [flows', ite_eq_right (show ¬ k + 1 ≤ k by omega)]
            exact hf'
          refine ⟨by omega, hWt' _ hfr_round, k + 1, flows', paths', hseq', hf'',
            fun _ => by omega, fun h => absurd (hr.symm.trans h) zero_ne_one⟩
      · have hsv1 : sv = 1 := by omega
        obtain ⟨hr, hs⟩ := roundStep_idle (d := ((⟨n, mb, sb, B⟩, (s.1, t.1)), sv)) hsv0 tt
        rw [hr, hs]
        exact ⟨le_rfl, hWt, k, flows, paths, hseq, hft, fun h => absurd h one_ne_zero,
          fun _ => h1 hsv1⟩)
    (n := n * n * n) (a := 0) (s := s1)
    ⟨Nat.zero_le _, hW1, 0, fun _ => Network.Flow.zero N, fun _ => [],
      fun j hj => absurd hj (Nat.not_lt_zero _), hf1, fun _ => by omega,
      fun h => absurd h zero_ne_one⟩
  set s2 := (Memory.spec 0).clientState s1
    (iterate roundStep (⟨n, mb, sb, B⟩, (s.1, t.1)) (n * n * n) 0)
  obtain ⟨hsv, hW2, k, flows, paths, hseq, hf2, h0, h1⟩ := hloop
  have hsv1 : (Memory.spec 0).clientResult s1
      (iterate roundStep (⟨n, mb, sb, B⟩, (s.1, t.1)) (n * n * n) 0) = 1 := by
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
  have hst_eq : (Memory.spec 0).clientState st (ekProg (⟨n, mb, sb, B⟩, (s.1, t.1))) = s2 := by
    unfold ekProg
    dsimp only
    rw [clientState_bind, clientState_bind,
      clientState_bind,
      clientState_iterate_eq_of _ _ (fun _ t' => cutOuterStep_state _ t'),
      clientState_pure]
  have hres_eq : (Memory.spec 0).clientResult st (ekProg (⟨n, mb, sb, B⟩, (s.1, t.1))) =
      ((Memory.spec 0).clientResult s2 (iterate cutOuterStep ⟨n, mb, sb, B⟩ n (0, 0))).2 := by
    unfold ekProg
    dsimp only
    rw [clientResult_bind, clientResult_bind,
      clientResult_bind, clientResult_pure]
  rw [hst_eq, hres_eq]
  rw [hst_eq] at hframe
  refine ⟨hframe, ?_⟩
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
  refine ⟨?_, iterate_cutOuter_spec hB hW2 C hC hC'⟩
  have hno : ¬ ∃ p, f.IsAugmentingPath p := by
    rw [f.exists_augmentingPath_iff_resReachable, ← f.resDist_lt_card_iff_resReachable,
      Fintype.card_fin]
    change ¬ f.resDist t < n
    omega
  have hC_eq : C = f.reachableCut := by
    ext x
    rw [f.mem_reachableCut_iff, ← f.resDist_lt_card_iff_resReachable, Fintype.card_fin,
      ← hdist x, hC' x]
  have hmin : N.IsMinCut f.reachableCut :=
    f.isMinCut_of_value_eq_cutCapacity (f.reachableCut_isCut hno)
      (f.value_eq_cutCapacity_reachableCut hno)
  rw [hC_eq]
  exact hmin.isMinCutBetween

end Cslib.Algorithms.WordRAM.EdmondsKarp
