/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.WordRAM.Realization.Absorb
public import CslibFrontier.Computability.WordRAM.Realization.ProgFrame
public import CslibFrontier.Computability.WordRAM.Realization.WordEncoding.Equiv
import CslibFrontier.Tactic.Realize
import Mathlib.Tactic.Linarith

/-!
# Core layout, programs, realization, and frames for dense Edmonds–Karp

Shared memory layout (`Ctx`, `distAddr`, `ekScratch`, `ekBound`, `CtxFits`), relocatable Word-RAM
memory programs (`fillRange`, `ekProg`), exact-basis realization certificates
(`fillRange_realizes`, `ekProg_realizes`), and `fillRange` frame/cost/validity lemmas used across
`CslibFrontier.Algorithms.WordRAM.EdmondsKarp`.

## Main definitions

* `Cslib.Algorithms.WordRAM.EdmondsKarp.Ctx`, `Ctx.equiv`, `distAddr`, `ekScratch`, `ekBound`,
  `CtxFits`: solver context, layout bounds, and word-width predicate.
* `Cslib.Algorithms.WordRAM.EdmondsKarp.fillRange`: fill a memory range with a constant word.
* `Cslib.Algorithms.WordRAM.EdmondsKarp.ekProg`: relocatable dense Edmonds–Karp solver.

## Main results

* `Cslib.Algorithms.WordRAM.EdmondsKarp.fillRange_realizes`,
  `Cslib.Algorithms.WordRAM.EdmondsKarp.ekProg_realizes`: compilation to `Basis.exact`.
* `Cslib.Algorithms.WordRAM.EdmondsKarp.fillRange_spec`,
  `Cslib.Algorithms.WordRAM.EdmondsKarp.memoryCost_fillRange_le`,
  `Cslib.Algorithms.WordRAM.EdmondsKarp.validHistory_fillRange`: specification, cost, and
  admissibility of `fillRange`.
-/

public section

namespace Cslib.Algorithms.WordRAM.EdmondsKarp

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


namespace Internal

/-- Address of the capacity `W u v`. -/
abbrev capAddr (c : Ctx) (u v : ℕ) : ℕ := c.matBase + u * c.n + v

/-- Address of the flow on the arc `(u, v)`. -/
abbrev flowAddr (c : Ctx) (u v : ℕ) : ℕ := c.scratchBase + u * c.n + v

/-- Address of the breadth-first-search parent of `x`. -/
abbrev predAddr (c : Ctx) (x : ℕ) : ℕ := c.scratchBase + c.n * c.n + c.n + x


end Internal

open Internal

/-- Address of the breadth-first-search distance of `x` (`n` when `x` is not reached). -/
abbrev distAddr (c : Ctx) (x : ℕ) : ℕ := c.scratchBase + c.n * c.n + x


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


namespace Internal

/-- Residual capacity `W u v - f u v + f v u` of the arc `(u, v)` (`d = ((c, u), v)`), guarded to
be at most `2 * B`. -/
@[expose] def readResCap (d : (Ctx × ℕ) × ℕ) : Memory.Prog ℕ := do
  let cu := d.1
  let c := cu.1
  let u := cu.2
  let v := d.2
  let cap ← Memory.read (capAddr c u v)
  let fuv ← Memory.read (flowAddr c u v)
  let fvu ← Memory.read (flowAddr c v u)
  if cap ≤ c.capBound ∧ fuv ≤ cap ∧ fvu ≤ c.capBound then pure (cap - fuv + fvu) else pure 0

/-- Innermost step of the search (`d = (((c, layer), u), v)`): reach `v` from `u` at distance
`layer + 1` when `v` is unreached and `(u, v)` has residual capacity. -/
@[expose] def bfsInnerStep (d : ((Ctx × ℕ) × ℕ) × ℕ) : Memory.Prog ℕ := do
  let clu := d.1
  let cl := clu.1
  let c := cl.1
  let layer := cl.2
  let u := clu.2
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
@[expose] def bfsMidStep (d : (Ctx × ℕ) × ℕ) : Memory.Prog ℕ := do
  let cl := d.1
  let c := cl.1
  let layer := cl.2
  let u := d.2
  let du ← Memory.read (distAddr c u)
  if du = layer then
    let _ ← iterate bfsInnerStep ((c, layer), u) c.n 0
    pure (u + 1)
  else
    pure (u + 1)

/-- One layer of the search (`d = (c, layer)`). -/
@[expose] def bfsLayerStep (d : Ctx × ℕ) : Memory.Prog ℕ := do
  let _ ← Memory.read 0
  let _ ← iterate bfsMidStep d d.1.n 0
  pure (d.2 + 1)

/-- Layered breadth-first search from `s` (`d = (c, s)`) on the residual graph of the stored
flow. -/
@[expose] def bfsProg (d : Ctx × ℕ) : Memory.Prog Unit := do
  let c := d.1
  let s := d.2
  fillRange ((distAddr c 0, c.n), c.n)
  Memory.write (distAddr c s) 0
  Memory.write (predAddr c s) s
  let _ ← iterate bfsLayerStep c (c.n - 1) 0
  pure ()

/-- One step of the bottleneck walk (`d = (c, (cur, δ))`): move to the parent `p` of `cur` and
take the minimum of `δ` and the residual capacity of `(p, cur)`. -/
@[expose] def bnStep (d : Ctx × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let c := d.1
  let curδ := d.2
  let cur := curδ.1
  let δ := curδ.2
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
@[expose] def augStep (d : (Ctx × ℕ) × ℕ) : Memory.Prog ℕ := do
  let cδ := d.1
  let c := cδ.1
  let δ := cδ.2
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
@[expose] def roundStep (d : (Ctx × (ℕ × ℕ)) × ℕ) : Memory.Prog ℕ := do
  let cst := d.1
  let c := cst.1
  let st := cst.2
  let s := st.1
  let t := st.2
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
@[expose] def cutInnerStep (d : (Ctx × ℕ) × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let cu := d.1
  let c := cu.1
  let u := cu.2
  let va := d.2
  let v := va.1
  let acc := va.2
  let dv ← Memory.read (distAddr c v)
  let x ← Memory.read (capAddr c u v)
  if dv = c.n ∧ x ≤ c.capBound ∧ acc ≤ c.n * c.n * c.capBound then
    pure (v + 1, acc + x)
  else
    pure (v + 1, acc)

/-- Outer step of the cut sum (`d = (c, (u, acc))`): add the capacities from `u` to the unreached
vertices when `u` is reached. -/
@[expose] def cutOuterStep (d : Ctx × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let c := d.1
  let ua := d.2
  let u := ua.1
  let acc := ua.2
  let du ← Memory.read (distAddr c u)
  if du < c.n then
    let r ← iterate cutInnerStep (c, u) c.n (0, acc)
    pure (u + 1, r.2)
  else
    pure (u + 1, acc)


end Internal

/-- **Dense Edmonds–Karp** (`d = (c, (s, t))`): clear the flow, run `n ^ 3` rounds (rounds after
`t` stops being reached do nothing), and return the weight of the reached set of the final
search. -/
@[expose] def ekProg (d : Ctx × (ℕ × ℕ)) : Memory.Prog ℕ := do
  let c := d.1
  fillRange ((flowAddr c 0 0, 0), c.n * c.n)
  let _ ← iterate roundStep d (c.n * c.n * c.n) 0
  let r ← iterate cutOuterStep c c.n (0, 0)
  pure r.2


namespace Internal

theorem clientResult_bfsInnerStep (d : ((Ctx × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (bfsInnerStep d) = d.2 + 1 := by
  unfold bfsInnerStep
  rw [clientResult_bind_read, clientResult_bind]
  split_ifs
  · rw [clientResult_bind_write, clientResult_bind_write, clientResult_pure]
  · rfl

theorem clientResult_bfsMidStep (d : (Ctx × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (bfsMidStep d) = d.2 + 1 := by
  unfold bfsMidStep
  rw [clientResult_bind_read]
  split_ifs
  · rw [clientResult_bind, clientResult_pure]
  · rfl


theorem clientResult_cutInnerStep_fst (cu : Ctx × ℕ) (va : ℕ × ℕ) (s : Memory.State) :
    ((Memory.spec 0).clientResult s (cutInnerStep (cu, va))).1 = va.1 + 1 := by
  unfold cutInnerStep
  rw [clientResult_bind_read, clientResult_bind_read]
  split_ifs <;> rfl

theorem clientResult_cutOuterStep_fst (c : Ctx) (ua : ℕ × ℕ) (s : Memory.State) :
    ((Memory.spec 0).clientResult s (cutOuterStep (c, ua))).1 = ua.1 + 1 := by
  unfold cutOuterStep
  rw [clientResult_bind_read]
  split_ifs
  · rw [clientResult_bind, clientResult_pure]
  · rfl

end Internal

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


namespace Internal

theorem idx_lt_sq {u v n : ℕ} (hu : u < n) (hv : v < n) : u * n + v < n * n := by
  have : (u + 1) * n ≤ n * n := Nat.mul_le_mul_right n hu
  rw [Nat.succ_mul] at this
  omega


end Internal

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
  rw [clientResult_cutInnerStep_fst]; omega

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
    rw [clientResult_cutOuterStep_fst]; omega


namespace Internal

theorem preservesAt_fillRange {a base val len : ℕ}
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


end Internal

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


namespace Internal

theorem memoryCost_map_write_le {α : Type} (f : Unit → α) (a v : ℕ) (s : Memory.State) :
    memoryCost (f <$> Memory.write a v) s ≤ 1 :=
  le_refl 1


end Internal

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


namespace Internal

theorem readResCap_state (d : (Ctx × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (readResCap d) = s := by
  unfold readResCap
  rw [clientState_bind_read, clientState_bind_read, clientState_bind_read]
  split_ifs <;> rfl

theorem bnStep_state (d : Ctx × (ℕ × ℕ)) (s : Memory.State) :
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

theorem cutInnerStep_state (d : (Ctx × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (cutInnerStep d) = s := by
  unfold cutInnerStep
  rw [clientState_bind_read, clientState_bind_read]
  split_ifs <;> rfl

theorem cutOuterStep_state (d : Ctx × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (cutOuterStep d) = s := by
  unfold cutOuterStep
  rw [clientState_bind_read]
  split_ifs
  · rw [clientState_bind,
      clientState_iterate_eq_of _ _ (fun a t => cutInnerStep_state _ t)]
    rfl
  · rfl

theorem preservesAt_bfsProg {a : ℕ} {d : Ctx × ℕ} (hs : d.2 < d.1.n)
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
@[expose] def DistRel (c : Ctx) (layer : ℕ) (t t' : Memory.State) : Prop :=
  ∀ x < c.n, t'.mem (distAddr c x) = t.mem (distAddr c x) ∨
    (t.mem (distAddr c x) = c.n ∧ t'.mem (distAddr c x) = layer + 1)

theorem DistRel.refl (c : Ctx) (layer : ℕ) (t : Memory.State) : DistRel c layer t t :=
  fun _ _ => Or.inl rfl

theorem DistRel.trans {c : Ctx} {layer : ℕ}
    {t₁ t₂ t₃ : Memory.State} (h₁ : DistRel c layer t₁ t₂) (h₂ : DistRel c layer t₂ t₃) :
    DistRel c layer t₁ t₃ := fun x hx => by
  rcases h₁ x hx with h | ⟨ha, hb⟩ <;> rcases h₂ x hx with h' | ⟨ha', hb'⟩
  · exact Or.inl (h'.trans h)
  · exact Or.inr ⟨h ▸ ha', hb'⟩
  · exact Or.inr ⟨ha, h'.trans hb⟩
  · omega


end Internal

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


namespace Internal

theorem bfsMidStep_rel (c : Ctx) (layer u : ℕ)
    (t : Memory.State) :
    DistRel c layer t ((Memory.spec 0).clientState t (bfsMidStep ((c, layer), u))) := by
  unfold bfsMidStep
  dsimp only
  rw [clientState_bind_read]
  split_ifs
  · rw [clientState_bind, clientState_pure]
    exact bfsInner_iterate_rel c layer u _ _ t
  · exact DistRel.refl c layer t

theorem bfsMid_iterate_rel (c : Ctx) (layer : ℕ)
    (m u₀ : ℕ) (t : Memory.State) :
    DistRel c layer t
      ((Memory.spec 0).clientState t (iterate bfsMidStep (c, layer) m u₀)) :=
  iterate_invariant_of bfsMidStep (c, layer) (fun _ _ t' => DistRel c layer t t')
    (fun _ u t' h => h.trans (bfsMidStep_rel c layer u t'))
    (DistRel.refl c layer t)

end Internal

end Cslib.Algorithms.WordRAM.EdmondsKarp
