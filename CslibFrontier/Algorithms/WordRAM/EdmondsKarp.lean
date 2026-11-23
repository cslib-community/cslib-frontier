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

private theorem fillRange_realizes :
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

/-! ### Interface (proofs in progress) -/

/-- Memory-operation budget of `ekProg` on `n` vertices, `O(n ^ 5)`. -/
abbrev ekCost (n : ℕ) : ℕ := 20 * (n + 1) ^ 5

theorem preservesAt_ekProg {a : ℕ} {d : Ctx × (ℕ × ℕ)}
    (ha : a < d.1.2.2.1 ∨ d.1.2.2.1 + ekScratch d.1.1 ≤ a) : PreservesAt a (ekProg d) := by
  sorry

theorem validHistory_ekProg {w : ℕ} {d : Ctx × (ℕ × ℕ)} {s : Memory.State}
    (hc : CtxFits w d.1) (hs : d.2.1 < d.1.1) (ht : d.2.2 < d.1.1)
    (hwf : Memory.WellFormed w s) (hfr : d.1.2.2.1 + ekScratch d.1.1 ≤ s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (ekProg d)) := by
  sorry

theorem ekProg_result_le (d : Ctx × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientResult s (ekProg d) ≤ d.1.1 * d.1.1 * d.1.2.2.2 + d.1.2.2.2 := by
  sorry

theorem memoryCost_ekProg_le (d : Ctx × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (ekProg d) s ≤ ekCost d.1.1 := by
  sorry

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
