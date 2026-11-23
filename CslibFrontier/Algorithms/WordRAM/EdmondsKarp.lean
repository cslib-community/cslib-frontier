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
import CslibFrontier.Tactic.Realize
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Dense Edmonds–Karp maximum flow on the Word-RAM

A memory-client program `ekProg` computing a maximum flow and a minimum `s`–`t` cut of the
network whose capacities are an `n × n` matrix `W` stored in row-major order, with the
shortest-augmenting-path rule of Edmonds and Karp ([EdmondsKarp1972]). It is a subroutine with a
relocatable layout: the context `c = (n, mb, sb, B)` places the capacity matrix at `mb`, a scratch
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

* `Cslib.Algorithms.WordRAM.EdmondsKarp.Ctx`, `capAddr`, `flowAddr`, `distAddr`, `predAddr`,
  `ekScratch`, `ekBound`: the layout and the word bound.
* `Cslib.Algorithms.WordRAM.EdmondsKarp.ekProg`: the solver.

## Main results

* `Cslib.Algorithms.WordRAM.EdmondsKarp.ekProg_realizes`: `ekProg` compiles to `Basis.exact`
  word-RAM code.
* `Cslib.Algorithms.WordRAM.EdmondsKarp.ekProg_spec`: the reached set of the final search is a
  minimum `s`–`t` cut of `cutWeight W`, and the returned value is its weight.
* `Cslib.Algorithms.WordRAM.EdmondsKarp.memoryCost_ekProg_le`: at most `ekCost n` memory
  operations, `O(n ^ 5)`.

## References

* [EdmondsKarp1972]
-/

public section

namespace Cslib.Algorithms.WordRAM.EdmondsKarp

open Cslib.Algorithms.Lean.MaxFlow Cslib.Algorithms.Lean.GomoryHu Cslib.WeightedCut
open Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization

/-! ### Layout -/

/-- Solver context `(n, mb, sb, B)`: `n` vertices, capacity matrix at `mb`, scratch area at `sb`,
and a bound `B` on the capacities. -/
abbrev Ctx := ℕ × ℕ × ℕ × ℕ

/-- Address of the capacity `W u v`. -/
abbrev capAddr (c : Ctx) (u v : ℕ) : ℕ := c.2.1 + u * c.1 + v

/-- Address of the flow on the arc `(u, v)`. -/
abbrev flowAddr (c : Ctx) (u v : ℕ) : ℕ := c.2.2.1 + u * c.1 + v

/-- Address of the breadth-first-search distance of `x` (`n` when `x` is not reached). -/
abbrev distAddr (c : Ctx) (x : ℕ) : ℕ := c.2.2.1 + c.1 * c.1 + x

/-- Address of the breadth-first-search parent of `x`. -/
abbrev predAddr (c : Ctx) (x : ℕ) : ℕ := c.2.2.1 + c.1 * c.1 + c.1 + x

/-- Words of scratch memory used by the solver: the flow matrix, distances and parents. -/
abbrev ekScratch (n : ℕ) : ℕ := n * n + 2 * n

/-- Every word the solver computes or stores is at most `ekBound n B`: round counts below `n ^ 3`,
cut sums up to `n * n * B`, residual capacities up to `2 * B`, flow updates up to `3 * B`. -/
abbrev ekBound (n B : ℕ) : ℕ := n * n * n + n * n * B + 3 * B + 1

/-- Layout and word-size requirements on a context: the matrix lies below the scratch area and
both the scratch area and `ekBound` fit a word. -/
abbrev CtxFits (w : ℕ) (c : Ctx) : Prop :=
  c.2.1 + c.1 * c.1 ≤ c.2.2.1 ∧ Fits w (c.2.2.1 + ekScratch c.1) ∧ Fits w (ekBound c.1 c.2.2.2)

/-! ### Client reduction tactic -/

@[client_simps]
private theorem fst_runClient_read (w : ℕ) (s : (Memory.spec w).State) (a : ℕ) :
    ((Memory.spec w).runClient s (Memory.read a)).1 = s.mem a :=
  rfl

@[client_simps]
private theorem fst_snd_runClient_read (w : ℕ) (s : (Memory.spec w).State) (a : ℕ) :
    ((Memory.spec w).runClient s (Memory.read a)).2.1 = s :=
  rfl

@[client_simps]
private theorem fst_runClient_write (w : ℕ) (s : (Memory.spec w).State) (a v : ℕ) :
    ((Memory.spec w).runClient s (Memory.write a v)).1 = () :=
  rfl

@[client_simps]
private theorem fst_snd_runClient_write (w : ℕ) (s : (Memory.spec w).State) (a v : ℕ) :
    ((Memory.spec w).runClient s (Memory.write a v)).2.1 =
      ⟨Function.update s.mem a v, s.frontier⟩ :=
  rfl

@[client_simps]
private theorem fst_runClient_ite {α : Type} (w : ℕ) (s : (Memory.spec w).State)
    (c : Prop) [Decidable c] (p₁ p₂ : (Memory.spec w).Client α) :
    ((Memory.spec w).runClient s (if c then p₁ else p₂)).1 =
      if c then (Memory.spec w).clientResult s p₁ else (Memory.spec w).clientResult s p₂ :=
  apply_ite (fun p => ((Memory.spec w).runClient s p).1) c p₁ p₂

@[client_simps]
private theorem fst_snd_runClient_ite {α : Type} (w : ℕ) (s : (Memory.spec w).State)
    (c : Prop) [Decidable c] (p₁ p₂ : (Memory.spec w).Client α) :
    ((Memory.spec w).runClient s (if c then p₁ else p₂)).2.1 =
      if c then (Memory.spec w).clientState s p₁ else (Memory.spec w).clientState s p₂ :=
  apply_ite (fun p => ((Memory.spec w).runClient s p).2.1) c p₁ p₂

local elab "simp_client" : tactic => do
  Lean.Elab.Tactic.evalTactic
    (← `(tactic| all_goals (dsimp -failIfUnchanged only;
                            simp -failIfUnchanged only [*, ↓reduceIte, client_simps])))
  for _ in [:6] do
    let gs ← Lean.Elab.Tactic.getGoals
    if gs.isEmpty then break
    let mut progress := false
    let mut newGs : List Lean.MVarId := []
    for g in gs do
      Lean.Elab.Tactic.setGoals [g]
      try
        Lean.Elab.Tactic.evalTactic
          (← `(tactic| (dsimp -failIfUnchanged only;
                        split_ifs <;>
                          simp -failIfUnchanged only [*, ↓reduceIte, client_simps])))
        progress := true
        newGs := newGs ++ (← Lean.Elab.Tactic.getGoals)
      catch _ =>
        newGs := newGs ++ [g]
    Lean.Elab.Tactic.setGoals newGs
    if !progress then break

/-! ### Programs -/

/-- One step of `fillRange`: write `val` at `base + idx`. -/
def fillStep (d : (ℕ × ℕ) × ℕ) : Memory.Prog ℕ := do
  Memory.write (d.1.1 + d.2) d.1.2
  pure (d.2 + 1)

/-- Write `val` at the `len` addresses from `base` (`d = ((base, val), len)`). -/
def fillRange (d : (ℕ × ℕ) × ℕ) : Memory.Prog Unit := do
  let _ ← iterate fillStep d.1 d.2 0
  pure ()

/-- Residual capacity `W u v - f u v + f v u` of the arc `(u, v)` (`d = ((c, u), v)`), guarded to
be at most `2 * B`. -/
def readResCap (d : (Ctx × ℕ) × ℕ) : Memory.Prog ℕ := do
  let c := d.1.1
  let u := d.1.2
  let v := d.2
  let cap ← Memory.read (capAddr c u v)
  let fuv ← Memory.read (flowAddr c u v)
  let fvu ← Memory.read (flowAddr c v u)
  if cap ≤ c.2.2.2 ∧ fuv ≤ cap ∧ fvu ≤ c.2.2.2 then pure (cap - fuv + fvu) else pure 0

/-- Innermost step of the search (`d = (((c, layer), u), v)`): reach `v` from `u` at distance
`layer + 1` when `v` is unreached and `(u, v)` has residual capacity. -/
def bfsInnerStep (d : ((Ctx × ℕ) × ℕ) × ℕ) : Memory.Prog ℕ := do
  let c := d.1.1.1
  let layer := d.1.1.2
  let u := d.1.2
  let v := d.2
  let dv ← Memory.read (distAddr c v)
  let rc ← readResCap ((c, u), v)
  if dv = c.1 ∧ 0 < rc then
    Memory.write (distAddr c v) (layer + 1)
    Memory.write (predAddr c v) u
    pure (v + 1)
  else
    pure (v + 1)

/-- Middle step of the search (`d = ((c, layer), u)`): expand `u` if it lies in layer `layer`. -/
def bfsMidStep (d : (Ctx × ℕ) × ℕ) : Memory.Prog ℕ := do
  let c := d.1.1
  let layer := d.1.2
  let u := d.2
  let du ← Memory.read (distAddr c u)
  if du = layer then
    let _ ← iterate bfsInnerStep ((c, layer), u) c.1 0
    pure (u + 1)
  else
    pure (u + 1)

/-- One layer of the search (`d = (c, layer)`). -/
def bfsLayerStep (d : Ctx × ℕ) : Memory.Prog ℕ := do
  let _ ← Memory.read 0
  let _ ← iterate bfsMidStep d d.1.1 0
  pure (d.2 + 1)

/-- Layered breadth-first search from `s` (`d = (c, s)`) on the residual graph of the stored
flow. -/
def bfsProg (d : Ctx × ℕ) : Memory.Prog Unit := do
  let c := d.1
  let s := d.2
  fillRange ((distAddr c 0, c.1), c.1)
  Memory.write (distAddr c s) 0
  Memory.write (predAddr c s) s
  let _ ← iterate bfsLayerStep c (c.1 - 1) 0
  pure ()

/-- One step of the bottleneck walk (`d = (c, (cur, δ))`): move to the parent `p` of `cur` and
take the minimum of `δ` and the residual capacity of `(p, cur)`. -/
def bnStep (d : Ctx × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let c := d.1
  let cur := d.2.1
  let δ := d.2.2
  let _ ← Memory.read 0
  if cur < c.1 then
    let p ← Memory.read (predAddr c cur)
    if p < c.1 then
      let rc ← readResCap ((c, p), cur)
      if rc ≤ δ then pure (p, rc) else pure (p, δ)
    else pure (0, δ)
  else pure (0, δ)

/-- One step of the augmentation walk (`d = ((c, δ), cur)`): push `δ` units along the arc
`(p, cur)` from the parent `p` of `cur`, cancelling flow on `(cur, p)` first. -/
def augStep (d : (Ctx × ℕ) × ℕ) : Memory.Prog ℕ := do
  let c := d.1.1
  let δ := d.1.2
  let cur := d.2
  let _ ← Memory.read 0
  if cur < c.1 then
    let p ← Memory.read (predAddr c cur)
    if p < c.1 then
      let fcp ← Memory.read (flowAddr c cur p)
      let fpc ← Memory.read (flowAddr c p cur)
      if fpc ≤ c.2.2.2 ∧ δ ≤ 2 * c.2.2.2 then
        let r := if δ ≤ fcp then δ else fcp
        Memory.write (flowAddr c cur p) (fcp - r)
        Memory.write (flowAddr c p cur) (fpc + (δ - r))
        pure p
      else pure p
    else pure 0
  else pure 0

/-- One round (`d = ((c, (s, t)), st)`, `st = 0` while running): search, and if `t` is reached,
compute the bottleneck of the found path and push it. Returns `1` once `t` is not reached. -/
def roundStep (d : (Ctx × (ℕ × ℕ)) × ℕ) : Memory.Prog ℕ := do
  let c := d.1.1
  let s := d.1.2.1
  let t := d.1.2.2
  let _ ← Memory.read 0
  if d.2 = 0 then
    bfsProg (c, s)
    let dt ← Memory.read (distAddr c t)
    if 0 < dt ∧ dt < c.1 then
      let r ← iterate bnStep c dt (t, 2 * c.2.2.2)
      let _ ← iterate augStep (c, r.2) dt t
      pure 0
    else pure 1
  else pure 1

/-- Inner step of the cut sum (`d = ((c, u), (v, acc))`): add `W u v` when `v` is unreached. -/
def cutInnerStep (d : (Ctx × ℕ) × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let c := d.1.1
  let u := d.1.2
  let v := d.2.1
  let acc := d.2.2
  let dv ← Memory.read (distAddr c v)
  let x ← Memory.read (capAddr c u v)
  if dv = c.1 ∧ x ≤ c.2.2.2 ∧ acc ≤ c.1 * c.1 * c.2.2.2 then
    pure (v + 1, acc + x)
  else
    pure (v + 1, acc)

/-- Outer step of the cut sum (`d = (c, (u, acc))`): add the capacities from `u` to the unreached
vertices when `u` is reached. -/
def cutOuterStep (d : Ctx × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let c := d.1
  let u := d.2.1
  let acc := d.2.2
  let du ← Memory.read (distAddr c u)
  if du < c.1 then
    let r ← iterate cutInnerStep (c, u) c.1 (0, acc)
    pure (u + 1, r.2)
  else
    pure (u + 1, acc)

/-- **Dense Edmonds–Karp** (`d = (c, (s, t))`): clear the flow, run `n ^ 3` rounds (rounds after
`t` stops being reached do nothing), and return the weight of the reached set of the final
search. -/
def ekProg (d : Ctx × (ℕ × ℕ)) : Memory.Prog ℕ := do
  let c := d.1
  fillRange ((flowAddr c 0 0, 0), c.1 * c.1)
  let _ ← iterate roundStep d (c.1 * c.1 * c.1) 0
  let r ← iterate cutOuterStep c c.1 (0, 0)
  pure r.2

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
      (fun w d _ => Fits w (d.1.1 + d.2)) (fun _ _ => 0) := by
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
      (fun w d _ => CtxFits w d.1.1 ∧ d.1.2 < d.1.1.1 ∧ d.2 < d.1.1.1) (fun _ _ => 0) := by
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
      (fun w d _ => CtxFits w d.1.1.1 ∧ d.1.1.2 < d.1.1.1.1 ∧ d.1.2 < d.1.1.1.1 ∧
        d.2 < d.1.1.1.1) (fun _ _ => 0) := by
  unfold bfsInnerStep
  realize [readResCap_realizes]
  all_goals
    obtain ⟨⟨hlay, hws, hwb⟩, hl, hu, hv⟩ := h
    ek_side

private theorem bfsMidStep_realizes :
    Realizes .exact bfsMidStep (WordEncoding.encode (α := (Ctx × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => CtxFits w d.1.1 ∧ d.1.2 < d.1.1.1 ∧ d.2 < d.1.1.1) (fun _ _ => 0) := by
  unfold bfsMidStep
  realize [bfsInnerStep_realizes]
  all_goals
    obtain ⟨⟨hlay, hws, hwb⟩, hl, hu⟩ := h
    try ek_side
  refine iterationSafe_of_stepInv _ _ w _
    (fun rem (v : ℕ) _ => v + rem = d.1.1.1) ?_ (Nat.zero_add _)
  intro rem v t hsum
  dsimp only at *
  refine ⟨⟨⟨hlay, hws, hwb⟩, hl, hu, by omega⟩, ?_⟩
  dsimp only [bfsInnerStep]
  simp_client <;> omega

private theorem bfsLayerStep_realizes :
    Realizes .exact bfsLayerStep (WordEncoding.encode (α := Ctx × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => CtxFits w d.1 ∧ d.2 < d.1.1) (fun _ _ => 0) := by
  unfold bfsLayerStep
  realize [bfsMidStep_realizes]
  all_goals
    obtain ⟨⟨hlay, hws, hwb⟩, hl⟩ := h
    try ek_side
  refine iterationSafe_of_stepInv _ _ w _
    (fun rem (u : ℕ) _ => u + rem = d.1.1) ?_ (Nat.zero_add _)
  intro rem u t hsum
  dsimp only at *
  refine ⟨⟨⟨hlay, hws, hwb⟩, hl, by omega⟩, ?_⟩
  dsimp only [bfsMidStep]
  simp_client <;> omega

private theorem bfsProg_realizes :
    Realizes .exact bfsProg (WordEncoding.encode (α := Ctx × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w d _ => CtxFits w d.1 ∧ d.2 < d.1.1) (fun _ _ => 0) := by
  unfold bfsProg
  realize [fillRange_realizes, bfsLayerStep_realizes]
  all_goals
    obtain ⟨⟨hlay, hws, hwb⟩, hs⟩ := h
    try ek_side
  refine iterationSafe_of_stepInv _ _ w _
    (fun rem (layer : ℕ) _ => layer + rem = d.1.1 - 1) ?_ (Nat.zero_add _)
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
      (fun w d _ => CtxFits w d.1.1 ∧ d.1.2.1 < d.1.1.1 ∧ d.1.2.2 < d.1.1.1) (fun _ _ => 0) := by
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
      (fun w d _ => CtxFits w d.1.1 ∧ d.1.2 < d.1.1.1 ∧ d.2.1 < d.1.1.1) (fun _ _ => 0) := by
  unfold cutInnerStep
  realize
  all_goals
    obtain ⟨⟨hlay, hws, hwb⟩, hu, hv⟩ := h
    have h1 := idx_lt_sq hu hv
    ek_side

private theorem cutOuterStep_realizes :
    Realizes .exact cutOuterStep (WordEncoding.encode (α := Ctx × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w d _ => CtxFits w d.1 ∧ d.2.1 < d.1.1) (fun _ _ => 0) := by
  unfold cutOuterStep
  realize [cutInnerStep_realizes]
  all_goals
    obtain ⟨⟨hlay, hws, hwb⟩, hu⟩ := h
    try ek_side
  refine iterationSafe_of_stepInv _ _ w _
    (fun rem (va : ℕ × ℕ) _ => va.1 + rem = d.1.1) ?_ (Nat.zero_add _)
  intro rem va t hsum
  dsimp only at *
  refine ⟨⟨⟨hlay, hws, hwb⟩, hu, by omega⟩, ?_⟩
  dsimp only [cutInnerStep]
  simp_client <;> omega

theorem ekProg_realizes :
    Realizes .exact ekProg (WordEncoding.encode (α := Ctx × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => CtxFits w d.1 ∧ d.2.1 < d.1.1 ∧ d.2.2 < d.1.1) (fun _ _ => 0) := by
  unfold ekProg
  realize [fillRange_realizes, roundStep_realizes, cutOuterStep_realizes]
  all_goals
    obtain ⟨⟨hlay, hws, hwb⟩, hs, ht⟩ := h
    try ek_side
  · refine iterationSafe_of_stepInv _ _ w _ (fun _ _ _ => True) ?_ trivial
    intro _ _ _ _
    exact ⟨⟨⟨hlay, hws, hwb⟩, hs, ht⟩, trivial⟩
  · refine iterationSafe_of_stepInv _ _ w _
      (fun rem (ua : ℕ × ℕ) _ => ua.1 + rem = d.1.1) ?_ (Nat.zero_add _)
    intro rem ua t hsum
    dsimp only at *
    refine ⟨⟨⟨hlay, hws, hwb⟩, by omega⟩, ?_⟩
    dsimp only [cutOuterStep]
    simp_client <;> omega

/-! ### Frames and read-only steps -/

theorem preservesAt_fillRange {a : ℕ} {d : (ℕ × ℕ) × ℕ}
    (hout : a < d.1.1 ∨ d.1.1 + d.2 ≤ a) : PreservesAt a (fillRange d) := fun s => by
  unfold fillRange
  rw [StateTransitionSpec.clientState_bind]
  change ((Memory.spec 0).clientState s (iterate fillStep d.1 d.2 0)).mem a = s.mem a
  refine iterate_invariant_of fillStep d.1
    (fun rem (idx : ℕ) t => idx + rem = d.2 ∧ t.mem a = s.mem a)
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
  rw [StateTransitionSpec.clientState_bind]
  change ∀ i < len, ((Memory.spec 0).clientState s (iterate fillStep (base, val) len 0)).mem
    (base + i) = val
  have hinv := iterate_invariant_of fillStep (base, val)
    (fun rem (idx : ℕ) t => idx + rem = len ∧ ∀ i < idx, t.mem (base + i) = val)
    (fun rem idx t ⟨hsum, hprev⟩ => by
      unfold fillStep
      simp only [client_simps]
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

theorem memoryCost_fillRange_le (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (fillRange d) s ≤ d.2 := by
  unfold fillRange
  have hit := memoryCost_iterate_le_of fillStep 1 d.1
    (fun idx t => by unfold fillStep; exact memoryCost_map_write_le _ _ _ t) d.2 0 s
  exact le_trans (memoryCost_bind_le hit fun _ t => (memoryCost_pure () t).le) (by omega)

theorem validHistory_fillRange {w : ℕ} {d : (ℕ × ℕ) × ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hend : d.1.1 + d.2 ≤ s.frontier) (hval : Fits w d.1.2) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (fillRange d)) := by
  rcases d with ⟨⟨base, val⟩, len⟩
  dsimp only at hend hval
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
  simp_client

private theorem bnStep_state (d : Ctx × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (bnStep d) = s := by
  unfold bnStep
  rw [clientState_bind_read]
  split_ifs
  · rw [clientState_bind_read]
    split_ifs
    · rw [StateTransitionSpec.clientState_bind, readResCap_state]
      split_ifs <;> rfl
    · rfl
  · rfl

private theorem cutInnerStep_state (d : (Ctx × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (cutInnerStep d) = s := by
  unfold cutInnerStep
  simp_client

private theorem cutOuterStep_state (d : Ctx × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (cutOuterStep d) = s := by
  unfold cutOuterStep
  rw [clientState_bind_read]
  split_ifs
  · rw [StateTransitionSpec.clientState_bind,
      clientState_iterate_eq_of _ _ (fun a t => cutInnerStep_state _ t)]
    rfl
  · rfl

private theorem preservesAt_bfsProg {a : ℕ} {d : Ctx × ℕ} (hs : d.2 < d.1.1)
    (ha : a < distAddr d.1 0 ∨ predAddr d.1 d.1.1 ≤ a) : PreservesAt a (bfsProg d) := by
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
      refine preservesAt_bind (fun t => congrArg (fun st : Memory.State => st.mem a) (readResCap_state _ t)) fun _ => ?_
      refine preservesAt_ite _ ?_ (preservesAt_pure _ _)
      refine preservesAt_bind (preservesAt_write _ (by ek_omega)) fun _ => ?_
      exact preservesAt_map _ (preservesAt_write _ (by ek_omega))
    · unfold bfsInnerStep
      simp_client
  · unfold bfsMidStep
    simp_client

/-! ### The search only lowers unreached distances to `layer + 1` -/

/-- Between `t` and `t'`, every distance below `n` either is unchanged or went from `n` (unreached)
to `layer + 1`. -/
private def DistRel (c : Ctx) (layer : ℕ) (t t' : Memory.State) : Prop :=
  ∀ x < c.1, t'.mem (distAddr c x) = t.mem (distAddr c x) ∨
    (t.mem (distAddr c x) = c.1 ∧ t'.mem (distAddr c x) = layer + 1)

private theorem DistRel.refl (c : Ctx) (layer : ℕ) (t : Memory.State) : DistRel c layer t t :=
  fun _ _ => Or.inl rfl

private theorem DistRel.trans {c : Ctx} {layer : ℕ} (hl : layer + 1 ≠ c.1)
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
  rw [clientState_bind_read, StateTransitionSpec.clientState_bind, readResCap_state]
  split_ifs with hc
  · rw [clientState_bind_write, clientState_bind_write, StateTransitionSpec.clientState_pure]
    dsimp only
    rw [Function.update_of_ne (by ek_omega)]
    by_cases hxv : x = d.2
    · subst hxv
      exact Or.inr ⟨hc.1, Function.update_self _ _ _⟩
    · exact Or.inl (Function.update_of_ne (by ek_omega) _ _)
  · exact Or.inl rfl


private theorem bfsInner_iterate_rel (c : Ctx) (layer u : ℕ) (hl : layer + 1 ≠ c.1)
    (m v₀ : ℕ) (t : Memory.State) :
    DistRel c layer t
      ((Memory.spec 0).clientState t (iterate bfsInnerStep ((c, layer), u) m v₀)) :=
  iterate_invariant_of bfsInnerStep ((c, layer), u) (fun _ _ t' => DistRel c layer t t')
    (fun _ v t' h => h.trans hl (bfsInnerStep_rel (((c, layer), u), v) t'))
    (DistRel.refl c layer t)

private theorem bfsMidStep_rel (c : Ctx) (layer u : ℕ) (hl : layer + 1 ≠ c.1)
    (t : Memory.State) :
    DistRel c layer t ((Memory.spec 0).clientState t (bfsMidStep ((c, layer), u))) := by
  unfold bfsMidStep
  dsimp only
  rw [clientState_bind_read]
  split_ifs
  · rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure]
    exact bfsInner_iterate_rel c layer u hl _ _ t
  · exact DistRel.refl c layer t

private theorem bfsMid_iterate_rel (c : Ctx) (layer : ℕ) (hl : layer + 1 ≠ c.1)
    (m u₀ : ℕ) (t : Memory.State) :
    DistRel c layer t
      ((Memory.spec 0).clientState t (iterate bfsMidStep (c, layer) m u₀)) :=
  iterate_invariant_of bfsMidStep (c, layer) (fun _ _ t' => DistRel c layer t t')
    (fun _ u t' h => h.trans hl (bfsMidStep_rel c layer u hl t'))
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
    (Finset.univ.filter fun x : Fin c.1 => lo ≤ t.mem (distAddr c x.1)).card =
      (Finset.univ.filter fun x : Fin c.1 => lo + 1 ≤ t.mem (distAddr c x.1)).card +
        (Finset.univ.filter fun x : Fin c.1 => t.mem (distAddr c x.1) = lo).card := by
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
private theorem memoryCost_bfsLayerStep_le (c : Ctx) (layer : ℕ) (hl : layer + 1 < c.1)
    (t : Memory.State) :
    memoryCost (bfsLayerStep (c, layer)) t ≤
      1 + c.1 + 6 * c.1 *
        (Finset.univ.filter fun x : Fin c.1 => t.mem (distAddr c x.1) = layer).card := by
  unfold bfsLayerStep
  dsimp only
  rw [memoryCost_bind', memoryCost_read, clientState_read, memoryCost_bind',
    memoryCost_pure]
  have hmid := memoryCost_iterate_le_potential bfsMidStep (c, layer)
    (fun j (u : ℕ) t' => u + j = c.1 ∧ DistRel c layer t t')
    (fun u t' => 6 * c.1 *
      (Finset.univ.filter fun x : Fin c.1 => u ≤ x.1 ∧ t'.mem (distAddr c x.1) = layer).card)
    1 ?_ c.1 0 t ⟨Nat.zero_add _, DistRel.refl c layer t⟩
  · have hcard : (Finset.univ.filter fun x : Fin c.1 =>
        0 ≤ x.1 ∧ t.mem (distAddr c x.1) = layer) =
        Finset.univ.filter fun x : Fin c.1 => t.mem (distAddr c x.1) = layer := by
      ext x; simp
    rw [hcard] at hmid
    omega
  intro j u t' ⟨hsum, hrel⟩
  have hu : u < c.1 := by omega
  have hl' : layer + 1 ≠ c.1 := by omega
  have hstep_rel := bfsMidStep_rel c layer u hl' t'
  have hres : (Memory.spec 0).clientResult t' (bfsMidStep ((c, layer), u)) = u + 1 := by
    unfold bfsMidStep; simp_client
  rw [hres]
  refine ⟨⟨by omega, hrel.trans hl' hstep_rel⟩, ?_⟩
  set t'' := (Memory.spec 0).clientState t' (bfsMidStep ((c, layer), u))
  have hsame : ∀ x : Fin c.1,
      t''.mem (distAddr c x.1) = layer ↔ t'.mem (distAddr c x.1) = layer := fun x => by
    rcases hstep_rel x.1 x.2 with h | ⟨h1, h2⟩
    · rw [h]
    · rw [h1, h2]; omega
  have hcnt : (Finset.univ.filter fun x : Fin c.1 =>
      u + 1 ≤ x.1 ∧ t''.mem (distAddr c x.1) = layer) =
      Finset.univ.filter fun x : Fin c.1 => u + 1 ≤ x.1 ∧ t'.mem (distAddr c x.1) = layer := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hsame x]
  have hcost : memoryCost (bfsMidStep ((c, layer), u)) t' ≤
      1 + if t'.mem (distAddr c u) = layer then 6 * c.1 else 0 := by
    unfold bfsMidStep
    dsimp only
    rw [memoryCost_bind', memoryCost_read, clientState_read, clientResult_read]
    split_ifs with hdu
    · rw [memoryCost_bind', memoryCost_pure]
      have hin := memoryCost_iterate_le_of bfsInnerStep 6 ((c, layer), u)
        (fun v t3 => memoryCost_bfsInnerStep_le _ t3) c.1 0 t'
      omega
    · rw [memoryCost_pure]
  rw [hcnt, card_filter_ge_split hu (fun x : Fin c.1 => t'.mem (distAddr c x.1) = layer)]
  change _ + _ ≤ 1 + 6 * c.1 * (_ + if t'.mem (distAddr c u) = layer then 1 else 0)
  split_ifs at hcost ⊢ <;> rw [Nat.mul_add] <;> omega


private theorem memoryCost_bfsProg_le (d : Ctx × ℕ) (s : Memory.State) :
    memoryCost (bfsProg d) s ≤ 8 * (d.1.1 + 1) ^ 2 := by
  obtain ⟨c, src⟩ := d
  dsimp only
  unfold bfsProg
  dsimp only
  rw [memoryCost_bind', memoryCost_bind', memoryCost_write, memoryCost_bind', memoryCost_write,
    memoryCost_bind', memoryCost_pure]
  have hfill := memoryCost_fillRange_le ((distAddr c 0, c.1), c.1) s
  set t₀ := (Memory.spec 0).clientState _ (Memory.write (predAddr c src) src)
  have hlayers := memoryCost_iterate_le_potential bfsLayerStep c
    (fun j (layer : ℕ) _ => layer + j = c.1 - 1)
    (fun layer t' => 6 * c.1 *
      (Finset.univ.filter fun x : Fin c.1 => layer ≤ t'.mem (distAddr c x.1)).card)
    (1 + c.1) ?_ (c.1 - 1) 0 t₀ (Nat.zero_add _)
  · have hcard : (Finset.univ.filter fun x : Fin c.1 => 0 ≤ t₀.mem (distAddr c x.1)).card ≤ c.1 :=
      (Finset.card_le_univ _).trans (by simp)
    have h1 : 6 * c.1 * (Finset.univ.filter fun x : Fin c.1 =>
        0 ≤ t₀.mem (distAddr c x.1)).card ≤ 6 * c.1 * c.1 := Nat.mul_le_mul_left _ hcard
    have h2 : (1 + c.1) * (c.1 - 1) ≤ (c.1 + 1) * c.1 := Nat.mul_le_mul (by omega) (Nat.sub_le _ _)
    have h3 : 8 * (c.1 + 1) ^ 2 = 8 * (c.1 * c.1) + 16 * c.1 + 8 := by ring
    have h4 : (c.1 + 1) * c.1 = c.1 * c.1 + c.1 := by ring
    have h5 : 6 * c.1 * c.1 = 6 * (c.1 * c.1) := by ring
    omega
  intro j layer t' hsum
  have hl : layer + 1 < c.1 := by omega
  have hres : (Memory.spec 0).clientResult t' (bfsLayerStep (c, layer)) = layer + 1 := by
    unfold bfsLayerStep; simp only [client_simps]
  rw [hres]
  refine ⟨by omega, ?_⟩
  have hcost := memoryCost_bfsLayerStep_le c layer hl t'
  have hrel : DistRel c layer t' ((Memory.spec 0).clientState t' (bfsLayerStep (c, layer))) := by
    unfold bfsLayerStep
    dsimp only
    rw [clientState_bind_read, StateTransitionSpec.clientState_bind,
      StateTransitionSpec.clientState_pure]
    exact bfsMid_iterate_rel c layer (by omega) _ _ t'
  set t'' := (Memory.spec 0).clientState t' (bfsLayerStep (c, layer))
  have hsame : (Finset.univ.filter fun x : Fin c.1 => layer + 1 ≤ t''.mem (distAddr c x.1)) =
      Finset.univ.filter fun x : Fin c.1 => layer + 1 ≤ t'.mem (distAddr c x.1) := by
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
    memoryCost (roundStep d) s ≤ 13 * (d.1.1.1 + 1) ^ 2 := by
  unfold roundStep
  dsimp only
  have hbr : ∀ dt t, memoryCost
      (if 0 < dt ∧ dt < d.1.1.1 then do
        let r ← iterate bnStep d.1.1 dt (d.1.2.2, 2 * d.1.1.2.2.2)
        let _ ← iterate augStep (d.1.1, r.2) dt d.1.2.2
        pure 0
      else pure 1) t ≤ 11 * d.1.1.1 := by
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
  have h : 13 * (d.1.1.1 + 1) ^ 2 = 13 * (d.1.1.1 * d.1.1.1) + 26 * d.1.1.1 + 13 := by ring
  have h' : 8 * (d.1.1.1 + 1) ^ 2 = 8 * (d.1.1.1 * d.1.1.1) + 16 * d.1.1.1 + 8 := by ring
  have hsq := Nat.le_mul_self d.1.1.1
  omega

private theorem memoryCost_cutOuterStep_le (d : Ctx × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (cutOuterStep d) s ≤ 1 + 2 * d.1.1 := by
  unfold cutOuterStep
  have hin : ∀ va t, memoryCost (cutInnerStep ((d.1, d.2.1), va)) t ≤ 2 := fun va t => by
    unfold cutInnerStep
    exact le_trans (memoryCost_bind_le (memoryCost_read _ _).le fun _ t1 =>
      memoryCost_bind_le (memoryCost_read _ _).le fun _ t2 =>
        memoryCost_ite_le (memoryCost_pure _ t2).le (memoryCost_pure _ t2).le) (by decide)
  refine le_trans (memoryCost_bind_le (memoryCost_read _ _).le fun _ t1 =>
    memoryCost_ite_le (memoryCost_bind_le
      (memoryCost_iterate_le_of cutInnerStep 2 _ hin d.1.1 _ t1) fun _ t2 =>
        (memoryCost_pure _ t2).le) (Nat.zero_le _)) ?_
  omega

/-- Memory-operation budget of `ekProg` on `n` vertices, `O(n ^ 5)`. -/
abbrev ekCost (n : ℕ) : ℕ := 20 * (n + 1) ^ 5

theorem memoryCost_ekProg_le (d : Ctx × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (ekProg d) s ≤ ekCost d.1.1 := by
  unfold ekProg
  dsimp only
  set n := d.1.1
  refine le_trans (memoryCost_bind_le (memoryCost_fillRange_le _ s) fun _ t1 =>
    memoryCost_bind_le (memoryCost_iterate_le_of roundStep (13 * (n + 1) ^ 2) d
      (fun _ _ => memoryCost_roundStep_le _ _) (n * n * n) 0 t1) fun _ t2 =>
      memoryCost_bind_le (memoryCost_iterate_le_of cutOuterStep (1 + 2 * n) d.1
        (fun _ _ => memoryCost_cutOuterStep_le _ _) n (0, 0) t2) fun _ t3 =>
        (memoryCost_pure _ t3).le) ?_
  dsimp only
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
  Memory.WellFormed w t ∧ c.2.2.1 + ekScratch c.1 ≤ t.frontier

private theorem ekReady_write {w : ℕ} {c : Ctx} {t : Memory.State} (ht : EkReady w c t)
    (a v : ℕ) (hv : Fits w v) : EkReady w c ⟨Function.update t.mem a v, t.frontier⟩ := by
  refine ⟨⟨ht.1.frontier_fits, fun b => ?_⟩, ht.2⟩
  dsimp only
  by_cases hb : b = a
  · subst hb; simpa using hv
  · rw [Function.update_of_ne hb]; exact ht.1.mem_fits b

private theorem validHistory_readResCap {w : ℕ} {d : (Ctx × ℕ) × ℕ} {t : Memory.State}
    (ht : EkReady w d.1.1 t) (hlay : d.1.1.2.1 + d.1.1.1 * d.1.1.1 ≤ d.1.1.2.2.1)
    (hu : d.1.2 < d.1.1.1) (hv : d.2 < d.1.1.1) :
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
    (hc : CtxFits w d.1) (hs : d.2 < d.1.1) (ht : EkReady w d.1 t) :
    (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t (bfsProg d)) := by
  obtain ⟨c, src⟩ := d
  dsimp only at hc hs ht
  obtain ⟨hlay, hws, hwb⟩ := hc
  unfold bfsProg
  dsimp only
  have hfill := validHistory_fillRange (d := ((distAddr c 0, c.1), c.1)) ht.1
    (by have := ht.2; ek_omega) (hws.of_le (by ek_omega))
  refine validHistory_bind_step hfill ?_
  have ht1 : EkReady w c _ := MonotoneMemInv.pres ht hfill
  refine validHistory_write_bind (by have := ht1.2; ek_omega) (fits_zero w) ?_
  have ht2 := ekReady_write ht1 (distAddr c src) 0 (fits_zero w)
  refine validHistory_write_bind (by have := ht2.2; ek_omega) (hws.of_le (by ek_omega)) ?_
  have ht3 := ekReady_write ht2 (predAddr c src) src (hws.of_le (by ek_omega))
  refine validHistory_bind_step
    (validHistory_iterate_nat (Inv := EkReady w c) (c.1 - 1) 0
      (fun layer hlayer t' ht' => ⟨?_, ?_⟩) ht3) (validHistory_pure _ _ _)
  · unfold bfsLayerStep
    refine validHistory_read_bind (by have := ht'.2; ek_omega) ?_
    refine validHistory_bind_step
      (validHistory_iterate_nat (Inv := EkReady w c) c.1 0
        (fun u hu t'' ht'' => ⟨?_, ?_⟩) ht') (validHistory_pure _ _ _)
    · unfold bfsMidStep
      refine validHistory_read_bind (by have := ht''.2; ek_omega) ?_
      refine validHistory_ite (fun _ => ?_) (fun _ => validHistory_pure _ _ _)
      refine validHistory_bind_step
        (validHistory_iterate_nat (Inv := EkReady w c) c.1 0
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
      · unfold bfsInnerStep
        simp_client
    · unfold bfsMidStep
      simp_client
  · unfold bfsLayerStep
    simp only [client_simps]

private theorem validHistory_bnStep {w : ℕ} {d : Ctx × (ℕ × ℕ)} {t : Memory.State}
    (hlay : d.1.2.1 + d.1.1 * d.1.1 ≤ d.1.2.2.1) (hn : 0 < d.1.1) (ht : EkReady w d.1 t) :
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
    (hc : CtxFits w d.1.1) (hn : 0 < d.1.1.1) (ht : EkReady w d.1.1 t) :
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
    (hc : CtxFits w d.1.1) (hs : d.1.2.1 < d.1.1.1) (hsnk : d.1.2.2 < d.1.1.1)
    (ht : EkReady w d.1.1 t) :
    (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t (roundStep d)) := by
  obtain ⟨⟨c, src, snk⟩, st⟩ := d
  dsimp only at hc hs hsnk ht
  have hn : 0 < c.1 := by omega
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
      (iterate bnStep c m (snk, 2 * c.2.2.2))) := fun m =>
    validHistory_iterate_inv (EkReady w c) bnStep c
      (fun a t' ht' => validHistory_bnStep (d := (c, a)) hc.1 hn ht') m _ ht1
  refine validHistory_bind_step (hbn _) ?_
  exact validHistory_bind_step
    (validHistory_iterate_inv (EkReady w c) augStep _
      (fun a t' ht' => validHistory_augStep (d := ((c, _), a)) hc hn ht') _ snk
      (MonotoneMemInv.pres ht1 (hbn _)))
    (validHistory_pure _ _ _)

private theorem validHistory_cutOuterStep {w : ℕ} {d : Ctx × (ℕ × ℕ)} {t : Memory.State}
    (hlay : d.1.2.1 + d.1.1 * d.1.1 ≤ d.1.2.2.1) (hu : d.2.1 < d.1.1) (ht : EkReady w d.1 t) :
    (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t (cutOuterStep d)) := by
  have hfr := ht.2
  unfold cutOuterStep
  refine validHistory_read_bind (by ek_omega) ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => validHistory_pure _ _ _)
  refine validHistory_bind_step
    (validHistory_iterate_fst (Inv := EkReady w d.1) d.1.1 0 _
      (fun v hv b t' ht' => ⟨?_, ?_⟩) ht) (validHistory_pure _ _ _)
  · have h1 := idx_lt_sq hu (show v < d.1.1 by omega)
    have hfr' := ht'.2
    unfold cutInnerStep
    refine validHistory_read_bind (by ek_omega) ?_
    refine validHistory_read_bind (by ek_omega) ?_
    exact validHistory_ite (fun _ => validHistory_pure _ _ _) (fun _ => validHistory_pure _ _ _)
  · unfold cutInnerStep
    simp_client

theorem validHistory_ekProg {w : ℕ} {d : Ctx × (ℕ × ℕ)} {s : Memory.State}
    (hc : CtxFits w d.1) (hs : d.2.1 < d.1.1) (ht : d.2.2 < d.1.1)
    (hwf : Memory.WellFormed w s) (hfr : d.1.2.2.1 + ekScratch d.1.1 ≤ s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (ekProg d)) := by
  obtain ⟨c, src, snk⟩ := d
  dsimp only at hc hs ht hfr
  have hr : EkReady w c s := ⟨hwf, hfr⟩
  unfold ekProg
  dsimp only
  have hfill := validHistory_fillRange (d := ((flowAddr c 0 0, 0), c.1 * c.1)) hwf
    (by ek_omega) (fits_zero w)
  refine validHistory_bind_step hfill ?_
  have hr1 : EkReady w c _ := MonotoneMemInv.pres hr hfill
  have hrounds := validHistory_iterate_inv (EkReady w c) roundStep (c, (src, snk))
    (fun a t' ht' => validHistory_roundStep (d := ((c, (src, snk)), a)) hc hs ht ht')
    (c.1 * c.1 * c.1) 0 hr1
  refine validHistory_bind_step hrounds ?_
  have hr2 : EkReady w c _ := MonotoneMemInv.pres hr1 hrounds
  refine validHistory_bind_step
    (validHistory_iterate_fst (Inv := EkReady w c) c.1 0 0
      (fun u hu b t' ht' => ⟨validHistory_cutOuterStep (d := (c, (u, b))) hc.1 (by dsimp only; omega) ht',
        ?_⟩) hr2) (validHistory_pure _ _ _)
  unfold cutOuterStep
  simp_client


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

theorem preservesAt_ekProg {a : ℕ} {d : Ctx × (ℕ × ℕ)} (hs : d.2.1 < d.1.1)
    (ha : a < d.1.2.2.1 ∨ d.1.2.2.1 + ekScratch d.1.1 ≤ a) : PreservesAt a (ekProg d) := by
  obtain ⟨c, src, snk⟩ := d
  dsimp only at hs ha
  unfold ekProg
  dsimp only
  refine preservesAt_bind (preservesAt_fillRange (by ek_omega)) fun _ => ?_
  refine preservesAt_bind (preservesAt_iterate (fun st => ?_) _ _) fun _ => ?_
  · unfold roundStep
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
  · exact preservesAt_bind (fun t => congrArg (fun st : Memory.State => st.mem a)
      (clientState_iterate_eq_of _ _ (fun _ t' => cutOuterStep_state _ t') _ _ t))
      fun _ => preservesAt_pure _ _

private theorem cutInnerStep_acc_le (d : (Ctx × ℕ) × (ℕ × ℕ)) (t : Memory.State)
    (h : d.2.2 ≤ d.1.1.1 * d.1.1.1 * d.1.1.2.2.2 + d.1.1.2.2.2) :
    ((Memory.spec 0).clientResult t (cutInnerStep d)).2 ≤
      d.1.1.1 * d.1.1.1 * d.1.1.2.2.2 + d.1.1.2.2.2 := by
  unfold cutInnerStep
  dsimp only
  rw [clientResult_bind_read, clientResult_bind_read]
  split_ifs with hg
  · rw [StateTransitionSpec.clientResult_pure]
    dsimp only
    omega
  · rw [StateTransitionSpec.clientResult_pure]
    exact h

private theorem cutOuterStep_acc_le (d : Ctx × (ℕ × ℕ)) (t : Memory.State)
    (h : d.2.2 ≤ d.1.1 * d.1.1 * d.1.2.2.2 + d.1.2.2.2) :
    ((Memory.spec 0).clientResult t (cutOuterStep d)).2 ≤
      d.1.1 * d.1.1 * d.1.2.2.2 + d.1.2.2.2 := by
  unfold cutOuterStep
  dsimp only
  rw [clientResult_bind_read]
  split_ifs
  · rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_pure]
    exact iterate_invariant_of cutInnerStep (d.1, d.2.1)
      (fun _ (va : ℕ × ℕ) _ => va.2 ≤ d.1.1 * d.1.1 * d.1.2.2.2 + d.1.2.2.2)
      (fun _ va t' hva => cutInnerStep_acc_le ((d.1, d.2.1), va) t' hva) h
  · rw [StateTransitionSpec.clientResult_pure]
    exact h

theorem ekProg_result_le (d : Ctx × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientResult s (ekProg d) ≤ d.1.1 * d.1.1 * d.1.2.2.2 + d.1.2.2.2 := by
  unfold ekProg
  dsimp only
  rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind,
    StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_pure]
  exact iterate_invariant_of cutOuterStep d.1
    (fun _ (ua : ℕ × ℕ) _ => ua.2 ≤ d.1.1 * d.1.1 * d.1.2.2.2 + d.1.2.2.2)
    (fun _ ua t' hua => cutOuterStep_acc_le (d.1, ua) t' hua) (Nat.zero_le _)


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
    (Memory.spec 0).clientResult t (readResCap (((n, mb, sb, B), u.1), v.1)) = f.resCap u v := by
  unfold readResCap
  dsimp only [capAddr, flowAddr]
  rw [clientResult_bind_read, clientResult_bind_read, clientResult_bind_read, hW u v, hf u v,
    hf v u]
  have hc : W u v ≤ B ∧ f u v ≤ W u v ∧ f v u ≤ B :=
    ⟨hB u v, f.le_cap u v, (f.le_cap v u).trans (hB v u)⟩
  rw [if_pos hc, StateTransitionSpec.clientResult_pure]
  rfl

/-- Invariant after the layers below `layer`: distances up to `layer` are exact, the others still
`n`, and every reached vertex other than the source has a parent one layer closer. -/
private def BfsLayerInv {N : Network (Fin n)} (mb sb B : ℕ) (f : N.Flow) (layer : ℕ)
    (t : Memory.State) : Prop :=
  (∀ x : Fin n,
    (f.resDist x ≤ layer → t.mem (distAddr (n, mb, sb, B) x.1) = f.resDist x) ∧
    (layer < f.resDist x → t.mem (distAddr (n, mb, sb, B) x.1) = n)) ∧
  (∀ x : Fin n,
    0 < t.mem (distAddr (n, mb, sb, B) x.1) → t.mem (distAddr (n, mb, sb, B) x.1) < n →
    ∃ u : Fin n,
      t.mem (predAddr (n, mb, sb, B) x.1) = u.1 ∧
      f.resDist u + 1 = f.resDist x ∧
      0 < f.resCap u x)

private theorem bfsMid_spec (hB : ∀ u v, W u v ≤ B) (hlay : mb + n * n ≤ sb)
    {layer : ℕ} {s st : Memory.State} (hW : MatLoaded n mb W s)
    (f : (Network.mk W src snk).Flow) (hf : FlowStored sb f s)
    (hlayer_lt : layer + 1 < n)
    (hst_low : ∀ a < sb + n * n, st.mem a = s.mem a)
    (hlinv : BfsLayerInv mb sb B f layer st) :
    let t_end :=
      (Memory.spec 0).clientState st (iterate bfsMidStep ((n, mb, sb, B), layer) (n) 0)
    (Memory.spec 0).clientResult st (iterate bfsMidStep ((n, mb, sb, B), layer) (n) 0) =
      n ∧
    (∀ a < sb + n * n, t_end.mem a = s.mem a) ∧
    BfsLayerInv mb sb B f (layer + 1) t_end := by
  let M := n
  have hmid := iterate_invariant_of bfsMidStep ((n, mb, sb, B), layer)
    (fun urem (u : ℕ) t' =>
      u + urem = M ∧
      (∀ a < sb + n * n, t'.mem a = s.mem a) ∧
      (∀ x : Fin M, f.resDist x ≤ layer → t'.mem (distAddr (n, mb, sb, B) x.1) = f.resDist x) ∧
      (∀ x : Fin M, layer + 1 < f.resDist x → t'.mem (distAddr (n, mb, sb, B) x.1) = M) ∧
      (∀ x : Fin M, f.resDist x = layer + 1 →
        t'.mem (distAddr (n, mb, sb, B) x.1) = layer + 1 ∨ t'.mem (distAddr (n, mb, sb, B) x.1) = M) ∧
      (∀ x : Fin M, f.resDist x = layer + 1 →
        (∃ u' : Fin M, u'.1 < u ∧ f.resDist u' = layer ∧ 0 < f.resCap u' x) →
        t'.mem (distAddr (n, mb, sb, B) x.1) = layer + 1) ∧
      (∀ x : Fin M, 0 < t'.mem (distAddr (n, mb, sb, B) x.1) → t'.mem (distAddr (n, mb, sb, B) x.1) < M →
        ∃ p : Fin M, t'.mem (predAddr (n, mb, sb, B) x.1) = p.1 ∧
          f.resDist p + 1 = f.resDist x ∧ 0 < f.resCap p x))
    (fun urem u t' ⟨husum, ht_low, hd_le, hd_gt, hd_eq, hd_found, hpar⟩ => by
      have hu_lt : u < M := by omega
      let uFin : Fin M := ⟨u, hu_lt⟩
      unfold bfsMidStep
      dsimp only
      rw [clientResult_bind_read, clientState_bind_read]
      by_cases hdu : t'.mem (distAddr (n, mb, sb, B) u) = layer
      · rw [ite_eq_left hdu, StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_pure, StateTransitionSpec.clientState_pure]
        have hres_u : f.resDist uFin = layer := by
          by_contra hne
          rcases lt_trichotomy (f.resDist uFin) layer with hlt | heq | hgt
          · have h1 : t'.mem (distAddr (n, mb, sb, B) u) = f.resDist uFin := hd_le uFin (le_of_lt hlt)
            omega
          · exact hne heq
          · by_cases h1 : f.resDist uFin = layer + 1
            · rcases hd_eq uFin h1 with h | h
              · have h' : t'.mem (distAddr (n, mb, sb, B) u) = layer + 1 := h; omega
              · have h' : t'.mem (distAddr (n, mb, sb, B) u) = M := h; omega
            · have h2 : t'.mem (distAddr (n, mb, sb, B) u) = M := hd_gt uFin (by omega)
              omega
        have hinn := iterate_invariant_of bfsInnerStep (((n, mb, sb, B), layer), u)
          (fun vrem (v : ℕ) t'' =>
            v + vrem = M ∧
            (∀ a < sb + n * n, t''.mem a = s.mem a) ∧
            (∀ x : Fin M, f.resDist x ≤ layer → t''.mem (distAddr (n, mb, sb, B) x.1) = f.resDist x) ∧
            (∀ x : Fin M, layer + 1 < f.resDist x → t''.mem (distAddr (n, mb, sb, B) x.1) = M) ∧
            (∀ x : Fin M, f.resDist x = layer + 1 →
              t''.mem (distAddr (n, mb, sb, B) x.1) = layer + 1 ∨ t''.mem (distAddr (n, mb, sb, B) x.1) = M) ∧
            (∀ x : Fin M, f.resDist x = layer + 1 →
              (∃ u' : Fin M, u'.1 < u ∧ f.resDist u' = layer ∧ 0 < f.resCap u' x) →
              t''.mem (distAddr (n, mb, sb, B) x.1) = layer + 1) ∧
            (∀ x : Fin M, x.1 < v → 0 < f.resCap uFin x → f.resDist x = layer + 1 →
              t''.mem (distAddr (n, mb, sb, B) x.1) = layer + 1) ∧
            (∀ x : Fin M, 0 < t''.mem (distAddr (n, mb, sb, B) x.1) → t''.mem (distAddr (n, mb, sb, B) x.1) < M →
              ∃ p : Fin M, t''.mem (predAddr (n, mb, sb, B) x.1) = p.1 ∧
                f.resDist p + 1 = f.resDist x ∧ 0 < f.resCap p x))
          (fun vrem v t'' ⟨hvsum, hi_low, hi_le, hi_gt, hi_eq, hi_found, hi_cur, hi_par⟩ => by
            have hv_lt : v < M := by omega
            let vFin : Fin M := ⟨v, hv_lt⟩
            have hf'' : FlowStored sb f t'' := hf.congr hi_low
            have hW'' : MatLoaded n mb W t'' := hW.congr hlay hi_low
            unfold bfsInnerStep
            dsimp only
            rw [clientResult_bind_read, clientState_bind_read, StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind]
            have hrc_r' : (Memory.spec 0).clientResult t''
                (readResCap (((n, mb, sb, B), u), v)) = f.resCap uFin vFin :=
              readResCap_spec hB hW'' hf'' uFin vFin
            have hrc_s' : (Memory.spec 0).clientState t''
                (readResCap (((n, mb, sb, B), u), v)) = t'' := readResCap_state _ t''
            rw [hrc_r', hrc_s']
            by_cases hcond : t''.mem (distAddr (n, mb, sb, B) v) = M ∧ 0 < f.resCap uFin vFin
            · rw [ite_eq_left hcond, clientResult_bind_write, clientState_bind_write, clientResult_bind_write,
                clientState_bind_write]
              simp only [client_simps]
              have hv_res : f.resDist vFin = layer + 1 := by
                have htri := f.resDist_le_add_one_of_pos_resCap hcond.2
                rw [hres_u] at htri
                have hnle : ¬ f.resDist vFin ≤ layer := fun hle => by
                  have h1 : t''.mem (distAddr (n, mb, sb, B) v) = f.resDist vFin := hi_le vFin hle
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
            (iterate bfsInnerStep (((n, mb, sb, B), layer), u) M 0) = M := by omega
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
          have h1 : t'.mem (distAddr (n, mb, sb, B) u) = f.resDist uFin := hd_le uFin (le_of_eq hru')
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
      (iterate bfsMidStep ((n, mb, sb, B), layer) M 0) = M := by omega
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
    let t := (Memory.spec 0).clientState s (bfsProg ((n, mb, sb, B), src.1))
    (∀ a < sb + n * n, t.mem a = s.mem a) ∧
      (∀ x : Fin n, t.mem (distAddr (n, mb, sb, B) x.1) = f.resDist x) ∧
      (∀ x : Fin n, 0 < f.resDist x → f.resDist x < n →
        ∃ u : Fin n,
          t.mem (predAddr (n, mb, sb, B) x.1) = u.1 ∧
          f.resDist u + 1 = f.resDist x ∧
          0 < f.resCap u x) := by
  intro t
  have hpres : ∀ a < sb + n * n, t.mem a = s.mem a :=
    fun a ha => preservesAt_bfsProg (d := ((n, mb, sb, B), src.1)) src.2 (Or.inl (by ek_omega)) s
  refine ⟨hpres, ?_⟩
  let M := n
  set s1 := (Memory.spec 0).clientState s (fillRange ((distAddr (n, mb, sb, B) 0, M), M))
  have hs1 := fillRange_spec (distAddr (n, mb, sb, B) 0) M M s
  set s2 : Memory.State :=
    ⟨Function.update (Function.update s1.mem (distAddr (n, mb, sb, B) src.1) 0)
      (predAddr (n, mb, sb, B) src.1) src.1, s1.frontier⟩
  have hsrc := src.2
  have hs2_low : ∀ a < sb + n * n, s2.mem a = s.mem a := by
    intro a ha
    have hne1 : a ≠ predAddr (n, mb, sb, B) src.1 := by ek_omega
    have hne2 : a ≠ distAddr (n, mb, sb, B) src.1 := by ek_omega
    dsimp only [s2]
    rw [Function.update_of_ne hne1, Function.update_of_ne hne2]
    exact hs1.2 a (Or.inl (by ek_omega))
  have hfill : ∀ x : Fin n, s1.mem (distAddr (n, mb, sb, B) x.1) = n := fun x =>
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
  have hlayers := iterate_invariant_of bfsLayerStep (n, mb, sb, B)
    (fun rem (layer : ℕ) st =>
      layer + rem = M - 1 ∧ (∀ a < sb + n * n, st.mem a = s.mem a) ∧
        BfsLayerInv mb sb B f layer st)
    (fun rem layer st ⟨hsum, hst_low, hlinv⟩ => by
      have hlayer_lt : layer + 1 < M := by omega
      obtain ⟨_, hm_low, hm_inv⟩ := bfsMid_spec hB hlay hW f hf hlayer_lt hst_low hlinv
      unfold bfsLayerStep
      dsimp only
      rw [clientResult_bind_read, clientState_bind_read, StateTransitionSpec.clientResult_bind,
        StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_pure,
        StateTransitionSpec.clientState_pure]
      exact ⟨by omega, hm_low, hm_inv⟩)
    (n := M - 1) (a := 0) (s := s2) ⟨Nat.zero_add _, hs2_low, hinv0⟩
  obtain ⟨hsum_end, _, hinv_end⟩ := hlayers
  set s3 := (Memory.spec 0).clientState s2 (iterate bfsLayerStep (n, mb, sb, B) (M - 1) 0)
  have hlay_eq : ((Memory.spec 0).clientResult s2
      (iterate bfsLayerStep (n, mb, sb, B) (M - 1) 0)) = M - 1 := by omega
  rw [hlay_eq] at hinv_end
  have ht_eq : t = s3 := by
    change (Memory.spec 0).clientState s (bfsProg ((n, mb, sb, B), src.1)) = s3
    unfold bfsProg
    dsimp only
    rw [StateTransitionSpec.clientState_bind, clientState_bind_write, clientState_bind_write,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure]
  rw [ht_eq]
  have hdist_all : ∀ x : Fin M, s3.mem (distAddr (n, mb, sb, B) x.1) = f.resDist x := by
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

/-! ### Interface (proofs in progress) -/

/-- **Correctness of dense Edmonds–Karp.** On a state holding the capacities `W ≤ B` at `mb`,
`ekProg` leaves memory outside its scratch area unchanged, the set `C` of vertices whose final
distance is below `n` is a minimum `s`–`t` cut of `cutWeight W`, and the returned value is
`cutWeight W C`. -/
theorem ekProg_spec {n mb sb B : ℕ} {W : Fin n → Fin n → ℕ} {s t : Fin n} (hst : s ≠ t)
    (hB : ∀ u v, W u v ≤ B) (hlay : mb + n * n ≤ sb) {st : Memory.State}
    (hW : ∀ u v : Fin n, st.mem (mb + u.1 * n + v.1) = W u v) :
    let c : Ctx := (n, mb, sb, B)
    let st' := (Memory.spec 0).clientState st (ekProg (c, (s.1, t.1)))
    let C : Finset (Fin n) := Finset.univ.filter fun x => st'.mem (distAddr c x.1) < n
    (∀ a, (a < sb ∨ sb + ekScratch n ≤ a) → st'.mem a = st.mem a) ∧
      IsMinCutBetween (cutWeight W) s t C ∧
      (Memory.spec 0).clientResult st (ekProg (c, (s.1, t.1))) = cutWeight W C := by
  sorry

end Cslib.Algorithms.WordRAM.EdmondsKarp
