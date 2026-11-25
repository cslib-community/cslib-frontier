/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.GomoryHu.Gusfield
public import CslibFrontier.Algorithms.WordRAM.EdmondsKarp.Core
public import CslibFrontier.Algorithms.WordRAM.Karger.Contract
public import CslibFrontier.Computability.WordRAM.Time
public import CslibFrontier.Foundations.Combinatorics.WeightedCut.MinCutBetween
import CslibFrontier.Algorithms.WordRAM.EdmondsKarp.Spec
import CslibFrontier.Computability.WordRAM.Realization.Program.Standard
import CslibFrontier.Foundations.Data.List.RowMajor
import CslibFrontier.Tactic.Realize
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Gomory–Hu trees on the Word-RAM

Gusfield's algorithm ([Gusfield1990]) as one uniform flat program over
`Cslib.WordRAM.Basis.exact`, with the dense Edmonds–Karp solver
`Cslib.Algorithms.WordRAM.EdmondsKarp.ekProg` ([EdmondsKarp1972]) as its maximum flow subroutine.
`Basis.exact` supplies the unit-cost multiplication used for the row-major addresses
`3 + u * n + v` of the `n × n` weight matrix and of the flow matrix of the subroutine.

## Overview

The input `encodeInput W r = n :: r :: flattenMatrix W` places `n` at address `1`, the root `r` at
address `2` and `W u v` at `3 + u * n + v`. The program allocates the workspace up to
`ghWorkspace n = 3 + 2 * n ^ 2 + 4 * n`: the parent array at `parAddr n u = 3 + n * n + u`, the
weight array at `wtAddr n u = 3 + n * n + n + u`, and the scratch area of `ekProg` after them. It
then

1. scans the matrix for its maximum entry `M`, the capacity bound given to `ekProg`;
2. starts from the star centred at `r`, with weight `0` everywhere;
3. for `s = 0, …, n - 1` other than `r`, with `t` the current parent of `s`: runs `ekProg` on
   `(s, t)`, whose final breadth-first search marks the `s`-side `X` of a minimum `s`–`t` cut;
   re-hangs below `s` every other vertex with parent `t` in `X`; and if the parent of `t` lies in
   `X`, lets `s` take the place of `t`. The tree-edge weights are updated from the flow value as
   in `Cslib.Algorithms.Lean.GomoryHu.gusfieldStepWeight`.

Each step costs `ekCost n + O(n)` memory operations, `O(n ^ 5)`, so the program halts within
`C * (n + 1) ^ 6` instructions. This is the `O(n ^ 6)` bound of Gusfield's algorithm with dense
Edmonds–Karp, formerly stated with `TimeM` annotations, now proved for a machine.

Correctness is transferred from `Cslib.Algorithms.Lean.GomoryHu.gusfieldWithWeights_spec`, which
accepts any oracle returning minimum cuts: after `k` steps the arrays hold
`gusfieldWeightLoop C val r` run on the first `k` vertices, for oracles `C` and `val` that agree
with the machine at every pair it queried. The machine and `Cslib.Algorithms.Lean.GomoryHu.gomoryHu`
may return different minimum cuts, and hence different trees.

## Main definitions

* `Cslib.Algorithms.WordRAM.GomoryHu.encodeInput`: the input word list `n :: r :: flattenMatrix W`.
* `Cslib.Algorithms.WordRAM.GomoryHu.parAddr`, `Cslib.Algorithms.WordRAM.GomoryHu.wtAddr`,
  `Cslib.Algorithms.WordRAM.GomoryHu.ghWorkspace`: the output addresses and the memory frontier.

## Main results

* `Cslib.Algorithms.WordRAM.GomoryHu.exists_gomoryHu_program`: one program over `Basis.exact`
  halts within `C * (n + 1) ^ 6` instructions on every weighted multigraph `W` on `Fin n` with
  entries at most `B` and every root `r`, at every word width fitting `ghWorkspace n` and
  `ekBound n B`, leaving in memory a parent function rooted at `r` whose parent graph is a
  Gomory–Hu tree of `W`, together with the minimum cut weight `minCutBetween W u (p u)` of every
  tree edge.

## Limitations

The weights are natural numbers, and the word width must hold `ekBound n B`, a bound on the cut
sums and flow updates of the subroutine.

## References

* [Gusfield1990]
* [EdmondsKarp1972]
-/

public section

namespace Cslib.Algorithms.WordRAM.GomoryHu

open Cslib.Algorithms.Lean.GomoryHu Cslib.WeightedCut SimpleGraph
open Cslib.Algorithms.WordRAM.EdmondsKarp Cslib.Algorithms.WordRAM.Karger
open Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization
open StateTransitionSpec (clientResult_bind clientResult_pure)

/-! ### Input encoding and layout -/

/-- Word-RAM input `n :: r :: flattenMatrix W`: the number of vertices, the root, and the weight
matrix in row-major order, so that `W u v` is the input word at memory address `3 + u * n + v`. -/
@[expose] def encodeInput {n : ℕ} (W : Fin n → Fin n → ℕ) (r : Fin n) : List ℕ :=
  n :: r.1 :: flattenMatrix W

/-- Address of the parent of `u` in the output tree (`3 + n * n + u`). -/
@[expose] def parAddr (n u : ℕ) : ℕ := 3 + n * n + u

/-- Address of the weight of the tree edge from `u` to its parent (`3 + n * n + n + u`). -/
@[expose] def wtAddr (n u : ℕ) : ℕ := 3 + n * n + n + u

/-- Memory frontier `3 + 2 * (n * n) + 4 * n` of the program: the input, the parent and weight
arrays, and the scratch area of the Edmonds–Karp subroutine. -/
@[expose] def ghWorkspace (n : ℕ) : ℕ := 3 + 2 * (n * n) + 4 * n

private abbrev parBase (n : ℕ) : ℕ := 3 + n * n
private abbrev wtBase (n : ℕ) : ℕ := 3 + n * n + n
private abbrev scrBase (n : ℕ) : ℕ := 3 + n * n + 2 * n
private abbrev distBase (n : ℕ) : ℕ := 3 + n * n + 2 * n + n * n

/-- Words allocated past the input. -/
private abbrev ghScratch (n : ℕ) : ℕ := 2 * n + ekScratch n

/-- Edmonds–Karp context: matrix at `3`, scratch area at `scrBase n`, capacity bound `B`. -/
private abbrev ghCtx (n B : ℕ) : Ctx := ⟨n, 3, scrBase n, B⟩

private theorem input_add_ghScratch (n : ℕ) : 3 + n * n + ghScratch n = ghWorkspace n := by
  unfold ghWorkspace ghScratch ekScratch
  ring

/-! ### Programs -/

/-- One step of the maximum scan (`d = (base, (idx, acc))`): fold the word at `base + idx` into
the running maximum `acc`. -/
private def maxStep (d : ℕ × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let x ← Memory.read (d.1 + d.2.1)
  if x ≤ d.2.2 then pure (d.2.1 + 1, d.2.2) else pure (d.2.1 + 1, x)

/-- One step of the re-hanging scan (`d = (((n, s), t), z)`): re-hang `z` below `s` when
`z ∉ {s, t}`, the parent of `z` is `t`, and `z` was reached by the final search of the
Edmonds–Karp run, that is, lies on the `s`-side of the computed cut. -/
private def rehangStep (d : ((ℕ × ℕ) × ℕ) × ℕ) : Memory.Prog ℕ := do
  let n := d.1.1.1
  let s := d.1.1.2
  let t := d.1.2
  let z := d.2
  let pz ← Memory.read (parBase n + z)
  let dz ← Memory.read (distBase n + z)
  if z ≠ s ∧ z ≠ t ∧ pz = t ∧ dz < n then
    Memory.write (parBase n + z) s
    pure (z + 1)
  else
    pure (z + 1)

/-- One step of Gusfield's algorithm (`d = ((n, r, B), s)`), skipping the root `r`: with
`t = p s`, compute a minimum `s`–`t` cut `X` with Edmonds–Karp, re-hang the vertices on the
`s`-side with parent `t` below `s`, and if `p t ∈ X`, swap `s` and `t`. The writes at `t` precede
those at `s`, matching `gusfieldStep` and `gusfieldStepWeight`, which give `s` priority. -/
private def ghStep (d : (ℕ × ℕ × ℕ) × ℕ) : Memory.Prog ℕ := do
  let n := d.1.1
  let r := d.1.2.1
  let B := d.1.2.2
  let s := d.2
  let _ ← Memory.read 0
  if s = r then pure (s + 1)
  else
    let t ← Memory.read (parBase n + s)
    if t < n then
      let v ← ekProg (ghCtx n B, (s, t))
      let _ ← iterate rehangStep ((n, s), t) n 0
      let pt ← Memory.read (parBase n + t)
      if pt < n then
        let dpt ← Memory.read (distBase n + pt)
        if dpt < n then
          let wt ← Memory.read (wtBase n + t)
          Memory.write (parBase n + t) s
          Memory.write (parBase n + s) pt
          Memory.write (wtBase n + t) v
          Memory.write (wtBase n + s) wt
          pure (s + 1)
        else
          Memory.write (wtBase n + s) v
          pure (s + 1)
      else pure (s + 1)
    else pure (s + 1)

/-- Gusfield's algorithm on `n` vertices with root `r` (`d = (n, r)`): allocate the workspace,
scan the matrix for its maximum entry, start from the star centred at `r` with zero weights, and
process `s = 0, …, n - 1`. -/
private def ghMain (d : ℕ × ℕ) : Memory.Prog ℕ := do
  let n := d.1
  let r := d.2
  let _ ← Memory.alloc (ghScratch n)
  let m ← iterate maxStep 3 (n * n) (0, 0)
  fillRange ((parBase n, r), n)
  fillRange ((wtBase n, 0), n)
  let _ ← iterate ghStep (n, r, m.2) n 0
  pure 0

/-- Gusfield's algorithm on the Word-RAM input `n :: r :: W`. -/
private def ghProg (_ : Unit) : Memory.Prog ℕ := do
  let n ← Memory.read 1
  let r ← Memory.read 2
  ghMain (n, r)

/-! ### Realization -/

private theorem maxStep_realizes :
    Realizes .exact maxStep (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w d _ => Fits w (d.1 + d.2.1) ∧ Fits w (d.2.1 + 1)) (fun _ _ => 0) := by
  unfold maxStep
  realize
  all_goals first | exact h.1 | exact h.2

private theorem rehangStep_realizes :
    Realizes .exact rehangStep (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (ghWorkspace d.1.1.1) ∧ d.1.1.2 < d.1.1.1 ∧ d.2 < d.1.1.1)
      (fun _ _ => 0) := by
  unfold rehangStep
  realize
  all_goals
    obtain ⟨hw, hs, hz⟩ := h
    dsimp -failIfUnchanged only [ghWorkspace, parBase, wtBase, scrBase, distBase] at *
    first | omega | (apply hw.of_le; omega)

private theorem ghStep_realizes :
    Realizes .exact ghStep (WordEncoding.encode (α := (ℕ × ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (ghWorkspace d.1.1) ∧ Fits w (ekBound d.1.1 d.1.2.2) ∧ d.2 < d.1.1)
      (fun _ _ => 0) := by
  unfold ghStep
  realize [ekProg_realizes, rehangStep_realizes]
  all_goals
    obtain ⟨hw, hB, hs⟩ := h
    dsimp -failIfUnchanged only [ghWorkspace, parBase, wtBase, scrBase, distBase] at *
    try omega
    try (apply hw.of_le; omega)
  · exact ⟨by dsimp only [ghCtx]; omega,
      hw.of_le (by dsimp only [ghCtx, ekScratch]; omega), hB⟩
  · refine iterationSafe_of_stepInv _ _ w _
      (fun rem (z : ℕ) _ => z + rem = d.1.1) ?_ (Nat.zero_add _)
    intro rem z t hsum
    dsimp only at hsum ⊢
    refine ⟨⟨hw, hs, by omega⟩, ?_⟩
    dsimp only [rehangStep]
    rw [clientResult_bind_read, clientResult_bind_read]
    split_ifs <;> simp only [clientResult_bind_write, clientResult_pure] <;> omega

/-- The maximum scan over `len` words from `base` returns an upper bound of those words, and it
is below every common bound `B` of them. -/
private theorem maxScan_spec {base len B : ℕ} {st : Memory.State}
    (hB : ∀ i < len, st.mem (base + i) ≤ B) :
    let m := ((Memory.spec 0).clientResult st (iterate maxStep base len (0, 0))).2
    m ≤ B ∧ ∀ i < len, st.mem (base + i) ≤ m := by
  intro m
  obtain ⟨-, hsum, hle, hall⟩ := iterate_invariant_of maxStep base
    (fun rem (ia : ℕ × ℕ) t =>
      t = st ∧ ia.1 + rem = len ∧ ia.2 ≤ B ∧ ∀ i < ia.1, st.mem (base + i) ≤ ia.2)
    (fun rem ia t ⟨ht, hsum, hacc, hprev⟩ => by
      subst ht
      unfold maxStep
      rw [clientResult_bind_read, clientState_bind_read]
      by_cases hx : t.mem (base + ia.1) ≤ ia.2
      · rw [ite_eq_left hx, StateTransitionSpec.clientResult_pure,
          StateTransitionSpec.clientState_pure]
        dsimp -failIfUnchanged only at hsum ⊢
        refine ⟨rfl, by omega, hacc, fun i hi => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact hprev i hi
        · exact hx
      · rw [ite_eq_right hx, StateTransitionSpec.clientResult_pure,
          StateTransitionSpec.clientState_pure]
        dsimp -failIfUnchanged only at hsum ⊢
        refine ⟨rfl, by omega, hB _ (by omega), fun i hi => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact (hprev i hi).trans (by omega)
        · exact le_rfl)
    (n := len) (a := (0, 0)) (s := st)
    ⟨rfl, Nat.zero_add _, Nat.zero_le _, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  exact ⟨hle, fun i hi => hall i (by omega)⟩

private theorem ghMain_realizes :
    Realizes .exact ghMain (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d s => s.frontier = 3 + d.1 * d.1 ∧ Fits w (ghWorkspace d.1) ∧
        ∃ B, (∀ i < d.1 * d.1, s.mem (3 + i) ≤ B) ∧ Fits w (ekBound d.1 B))
      (fun _ _ => 0) := by
  unfold ghMain
  realize [maxStep_realizes, fillRange_realizes, ghStep_realizes]
  all_goals
    obtain ⟨hfr, hw, B, hB, hwB⟩ := h
    dsimp -failIfUnchanged only [ghWorkspace, parBase, wtBase, scrBase, distBase, ghScratch,
      ekScratch] at *
    try omega
    try (apply hw.of_le; omega)
  · refine iterationSafe_of_stepInv _ _ w _
      (fun rem (ia : ℕ × ℕ) _ => ia.1 + rem = d.1 * d.1) ?_ (Nat.zero_add _)
    intro rem ia t hsum
    dsimp only at hsum ⊢
    refine ⟨⟨hw.of_le (by omega), hw.of_le (by omega), hw.of_le (by nlinarith)⟩, ?_⟩
    dsimp only [maxStep]
    rw [clientResult_bind_read]
    split_ifs <;> simp only [clientResult_pure] <;> omega
  · have hclr : ∀ i < d.1 * d.1,
        clear s.mem s.frontier (ghScratch d.1) (3 + i) ≤ B := fun i hi => by
      rw [clear_of_not_owns fun h => absurd h.1 (by change ¬s.frontier ≤ 3 + i; omega)]
      exact hB i hi
    have hM := (maxScan_spec (st := ⟨clear s.mem s.frontier (ghScratch d.1),
      s.frontier + ghScratch d.1⟩) hclr).1
    refine iterationSafe_of_stepInv _ _ w _
      (fun rem (z : ℕ) _ => z + rem = d.1) ?_ (Nat.zero_add _)
    intro rem z t hsum
    dsimp only at hsum ⊢
    refine ⟨⟨hw, hwB.of_le (by unfold ekBound; gcongr), by omega⟩, ?_⟩
    dsimp only [ghStep]
    rw [clientResult_bind_read]
    split_ifs
    · rw [clientResult_pure]; omega
    · rw [clientResult_bind_read]
      split_ifs
      · rw [clientResult_bind, clientResult_bind, clientResult_bind_read]
        split_ifs
        · rw [clientResult_bind_read]
          split_ifs
          · rw [clientResult_bind_read, clientResult_bind_write, clientResult_bind_write,
              clientResult_bind_write, clientResult_bind_write, clientResult_pure]; omega
          · rw [clientResult_bind_write, clientResult_pure]; omega
        · rw [clientResult_pure]; omega
      · rw [clientResult_pure]; omega

private theorem ghProg_realizes :
    Realizes .exact ghProg (WordEncoding.encode (α := Unit))
      (WordEncoding.encode (α := ℕ))
      (fun w _ s => s.frontier = 3 + s.mem 1 * s.mem 1 ∧ Fits w (ghWorkspace (s.mem 1)) ∧
        ∃ B, (∀ i < s.mem 1 * s.mem 1, s.mem (3 + i) ≤ B) ∧ Fits w (ekBound (s.mem 1) B))
      (fun _ _ => 0) := by
  unfold ghProg
  realize [ghMain_realizes]
  all_goals
    obtain ⟨hfr, hw, B, hB, hwB⟩ := h
    first
      | exact hfr | exact hw | exact ⟨B, hB, hwB⟩
      | (apply hw.of_le; dsimp only [ghWorkspace]; omega)

/-! ### State-level effect of the loop steps -/

/-- The re-hanging scan re-hangs below `s` exactly the vertices `z ∉ {s, t}` with parent `t` whose
distance word is below `n`, and changes no word outside the parent array. -/
private theorem rehang_spec (n s t : ℕ) (st : Memory.State) :
    let st' := (Memory.spec 0).clientState st (iterate rehangStep ((n, s), t) n 0)
    (∀ a, (a < parBase n ∨ parBase n + n ≤ a) → st'.mem a = st.mem a) ∧
    ∀ z < n, st'.mem (parBase n + z) =
      if z ≠ s ∧ z ≠ t ∧ st.mem (parBase n + z) = t ∧ st.mem (distBase n + z) < n then s
      else st.mem (parBase n + z) := by
  intro st'
  obtain ⟨hsum, hfr, hpar⟩ := iterate_invariant_of rehangStep ((n, s), t)
    (fun rem (z : ℕ) u => z + rem = n ∧
      (∀ a, (a < parBase n ∨ parBase n + n ≤ a) → u.mem a = st.mem a) ∧
      ∀ y < n, u.mem (parBase n + y) =
        if y < z ∧ (y ≠ s ∧ y ≠ t ∧ st.mem (parBase n + y) = t ∧ st.mem (distBase n + y) < n)
        then s else st.mem (parBase n + y))
    (fun rem z u ⟨hsum, hfr, hpar⟩ => by
      have hz : z < n := by omega
      have hpz : u.mem (parBase n + z) = st.mem (parBase n + z) := by
        rw [hpar z hz, ite_eq_right_iff]
        exact fun h => absurd h.1 (lt_irrefl z)
      have hdz : u.mem (distBase n + z) = st.mem (distBase n + z) :=
        hfr _ (Or.inr (by dsimp only [distBase, parBase]; omega))
      unfold rehangStep
      dsimp only
      rw [clientResult_bind_read, clientState_bind_read, clientResult_bind_read,
        clientState_bind_read, hpz, hdz]
      by_cases hc : z ≠ s ∧ z ≠ t ∧ st.mem (parBase n + z) = t ∧ st.mem (distBase n + z) < n
      · rw [ite_eq_left hc, clientResult_bind_write, clientState_bind_write,
          StateTransitionSpec.clientResult_pure, StateTransitionSpec.clientState_pure]
        refine ⟨by omega, fun a ha => ?_, fun y hy => ?_⟩
        · dsimp only
          rw [Function.update_of_ne (by omega)]
          exact hfr a ha
        · dsimp only
          by_cases hyz : y = z
          · subst hyz
            rw [Function.update_self, ite_eq_left ⟨Nat.lt_succ_self y, hc⟩]
          · rw [Function.update_of_ne (by omega), hpar y hy]
            split_ifs <;> omega
      · rw [ite_eq_right hc, StateTransitionSpec.clientResult_pure,
          StateTransitionSpec.clientState_pure]
        refine ⟨by omega, hfr, fun y hy => ?_⟩
        rw [hpar y hy]
        by_cases hyz : y = z
        · subst hyz
          rw [ite_eq_right (fun h => absurd h.1 (lt_irrefl y)),
            ite_eq_right (fun h => hc h.2)]
        · split_ifs <;> omega)
    (n := n) (a := 0) (s := st) ⟨Nat.zero_add _, fun _ _ => rfl, fun y _ =>
      (ite_eq_right (fun h => absurd h.1 (Nat.not_lt_zero y))).symm⟩
  refine ⟨hfr, fun z hz => ?_⟩
  rw [hpar z hz, ite_and]
  simp only [show z < (Memory.spec 0).clientResult st (iterate rehangStep ((n, s), t) n 0) by
    omega, ↓reduceIte]

private theorem clientResult_ghStep (n r B k : ℕ) (st : Memory.State) :
    (Memory.spec 0).clientResult st (ghStep ((n, r, B), k)) = k + 1 := by
  unfold ghStep
  dsimp only
  rw [clientResult_bind_read]
  split_ifs
  · rfl
  · rw [clientResult_bind_read]
    split_ifs
    · rw [clientResult_bind, clientResult_bind, clientResult_bind_read]
      split_ifs
      · rw [clientResult_bind_read]
        split_ifs
        · rw [clientResult_bind_read, clientResult_bind_write, clientResult_bind_write,
            clientResult_bind_write, clientResult_bind_write, clientResult_pure]
        · rw [clientResult_bind_write, clientResult_pure]
      · rfl
    · rfl

/-- State-level effect of one step of Gusfield's algorithm on a non-root vertex `k` with parent
`t`, in terms of the state `st1` and value `v` left by the Edmonds–Karp run. -/
private theorem ghStep_spec {n r B k t : ℕ} {st : Memory.State} (hk : k < n) (hkr : k ≠ r)
    (hpar : ∀ z < n, st.mem (parBase n + z) < n) (htdef : st.mem (parBase n + k) = t) :
    let st1 := (Memory.spec 0).clientState st (ekProg (ghCtx n B, (k, t)))
    let v := (Memory.spec 0).clientResult st (ekProg (ghCtx n B, (k, t)))
    let st' := (Memory.spec 0).clientState st (ghStep ((n, r, B), k))
    (∀ a < parBase n, st'.mem a = st.mem a) ∧
    (∀ z < n, st'.mem (parBase n + z) =
      if z = k then
        (if st1.mem (distBase n + st.mem (parBase n + t)) < n then st.mem (parBase n + t) else t)
      else if z = t then
        (if st1.mem (distBase n + st.mem (parBase n + t)) < n then k else st.mem (parBase n + t))
      else if st.mem (parBase n + z) = t ∧ st1.mem (distBase n + z) < n then k
      else st.mem (parBase n + z)) ∧
    (∀ z < n, st'.mem (wtBase n + z) =
      if st1.mem (distBase n + st.mem (parBase n + t)) < n then
        (if z = k then st.mem (wtBase n + t) else if z = t then v else st.mem (wtBase n + z))
      else if z = k then v else st.mem (wtBase n + z)) := by
  intro st1 v st'
  have ht : t < n := htdef ▸ hpar k hk
  have hpt : st.mem (parBase n + t) < n := hpar t ht
  have h1 : ∀ a < scrBase n, st1.mem a = st.mem a := fun a ha =>
    preservesAt_ekProg (c := ghCtx n B) (src := k) (snk := t) hk (Or.inl ha) st
  obtain ⟨h2fr, h2par⟩ := rehang_spec n k t st1
  have e1 : (Memory.spec 0).clientState st (ekProg (ghCtx n B, (k, t))) = st1 := rfl
  have e2 : (Memory.spec 0).clientResult st (ekProg (ghCtx n B, (k, t))) = v := rfl
  generalize hst2 : (Memory.spec 0).clientState st1 (iterate rehangStep ((n, k), t) n 0) = st2
    at h2fr h2par
  have hP2 : ∀ y < n, st2.mem (parBase n + y) =
      if y ≠ k ∧ y ≠ t ∧ st.mem (parBase n + y) = t ∧ st1.mem (distBase n + y) < n then k
      else st.mem (parBase n + y) := fun y hy => by
    rw [h2par y hy, h1 _ (by dsimp only [scrBase, parBase]; omega)]
  have hPt2 : st2.mem (parBase n + t) = st.mem (parBase n + t) := by
    rw [hP2 t ht, ite_eq_right (fun h => h.2.1 rfl)]
  have hD2 : ∀ y, st2.mem (distBase n + y) = st1.mem (distBase n + y) := fun y =>
    h2fr _ (Or.inr (by dsimp only [distBase, parBase]; omega))
  have hW2 : ∀ y < n, st2.mem (wtBase n + y) = st.mem (wtBase n + y) := fun y hy => by
    rw [h2fr _ (Or.inr (by dsimp only [wtBase, parBase]; omega)),
      h1 _ (by dsimp only [scrBase, wtBase]; omega)]
  have hlow2 : ∀ a < parBase n, st2.mem a = st.mem a := fun a ha => by
    rw [h2fr _ (Or.inl ha), h1 _ (by dsimp only [scrBase, parBase] at ha ⊢; omega)]
  have key : st' = if st1.mem (distBase n + st.mem (parBase n + t)) < n then
      ⟨Function.update (Function.update (Function.update (Function.update st2.mem
        (parBase n + t) k) (parBase n + k) (st.mem (parBase n + t))) (wtBase n + t) v)
        (wtBase n + k) (st.mem (wtBase n + t)), st2.frontier⟩
    else ⟨Function.update st2.mem (wtBase n + k) v, st2.frontier⟩ := by
    change (Memory.spec 0).clientState st (ghStep ((n, r, B), k)) = _
    unfold ghStep
    rw [clientState_bind_read, ite_eq_right hkr, clientState_bind_read, htdef, ite_eq_left ht,
      StateTransitionSpec.clientState_bind, e1, e2, StateTransitionSpec.clientState_bind, hst2,
      clientState_bind_read, hPt2, ite_eq_left hpt, clientState_bind_read, hD2]
    by_cases hX : st1.mem (distBase n + st.mem (parBase n + t)) < n
    · rw [ite_eq_left hX, ite_eq_left hX, clientState_bind_read, hW2 t ht, clientState_bind_write,
        clientState_bind_write, clientState_bind_write, clientState_bind_write,
        StateTransitionSpec.clientState_pure]
    · rw [ite_eq_right hX, ite_eq_right hX, clientState_bind_write,
        StateTransitionSpec.clientState_pure]
  refine ⟨fun a ha => ?_, fun z hz => ?_, fun z hz => ?_⟩
  · have hne : ∀ b, a ≠ parBase n + b := fun b => by omega
    have hne' : ∀ b, a ≠ wtBase n + b := fun b => by dsimp only [wtBase, parBase] at ha ⊢; omega
    rw [key]
    split_ifs
    · dsimp only
      rw [Function.update_of_ne (hne' _), Function.update_of_ne (hne' _),
        Function.update_of_ne (hne _), Function.update_of_ne (hne _), hlow2 a ha]
    · dsimp only
      rw [Function.update_of_ne (hne' _), hlow2 a ha]
  · by_cases hX : st1.mem (distBase n + st.mem (parBase n + t)) < n
    · rw [key, ite_eq_left hX]
      dsimp only
      simp only [Function.update_apply, hX, ↓reduceIte]
      by_cases hzk : z = k
      · subst hzk
        simp only [parBase, wtBase] at *
        split_ifs <;> omega
      · by_cases hzt : z = t
        · subst hzt
          simp only [parBase, wtBase] at *
          split_ifs <;> omega
        · rw [hP2 z hz]
          simp only [parBase, wtBase] at *
          split_ifs <;> omega
    · rw [key, ite_eq_right hX]
      dsimp only
      simp only [Function.update_apply, hX, ↓reduceIte]
      by_cases hzk : z = k
      · subst hzk
        rw [hP2 z hz]
        simp only [parBase, wtBase] at *
        split_ifs <;> omega
      · by_cases hzt : z = t
        · subst hzt
          rw [hP2 z hz]
          simp only [parBase, wtBase] at *
          split_ifs <;> omega
        · rw [hP2 z hz]
          simp only [parBase, wtBase] at *
          split_ifs <;> omega
  · by_cases hX : st1.mem (distBase n + st.mem (parBase n + t)) < n
    · rw [key, ite_eq_left hX]
      dsimp only
      simp only [Function.update_apply, hX, ↓reduceIte, hW2 z hz]
      simp only [parBase, wtBase] at *
      split_ifs <;> omega
    · rw [key, ite_eq_right hX]
      dsimp only
      simp only [Function.update_apply, hX, ↓reduceIte, hW2 z hz]
      simp only [parBase, wtBase] at *
      split_ifs <;> omega

/-! ### Gusfield's algorithm on prefixes of the vertex order -/

/-- Processing one more vertex `s` after the list `l`. -/
private theorem gusfieldWeightLoop_append {V β : Type*} [DecidableEq V] (C : V → V → Finset V)
    (val : V → V → β) (r : V) (l : List V) (s : V) (p : V → V) (w : V → β) :
    gusfieldWeightLoop C val r (l ++ [s]) p w =
      if s = r then gusfieldWeightLoop C val r l p w
      else
        ((gusfieldStep (gusfieldWeightLoop C val r l p w).1 s
            (C s ((gusfieldWeightLoop C val r l p w).1 s))),
          gusfieldStepWeight (gusfieldWeightLoop C val r l p w).1
            (gusfieldWeightLoop C val r l p w).2 s
            (C s ((gusfieldWeightLoop C val r l p w).1 s))
            (val s ((gusfieldWeightLoop C val r l p w).1 s))) := by
  induction l generalizing p w with
  | nil => by_cases hs : s = r <;> simp only [List.nil_append, gusfieldWeightLoop, hs, ↓reduceIte]
  | cons x l ih =>
    by_cases hx : x = r <;> simp only [List.cons_append, gusfieldWeightLoop, hx, ↓reduceIte, ih]

/-- The loop only queries the oracles at the vertices of the list. -/
private theorem gusfieldWeightLoop_congr {V β : Type*} [DecidableEq V] {C C' : V → V → Finset V}
    {val val' : V → V → β} (r : V) :
    ∀ {l : List V}, (∀ a ∈ l, C a = C' a ∧ val a = val' a) → ∀ p w,
      gusfieldWeightLoop C val r l p w = gusfieldWeightLoop C' val' r l p w
  | [], _, _, _ => rfl
  | x :: l, h, p, w => by
    obtain ⟨hC, hv⟩ := h x (List.mem_cons_self ..)
    have ih := gusfieldWeightLoop_congr r (l := l) fun a ha => h a (List.mem_cons_of_mem x ha)
    by_cases hx : x = r <;> simp only [gusfieldWeightLoop, hx, ↓reduceIte, hC, hv, ih]

/-- `gusfieldStep` in terms of word-level data: `P` reads the parent of a vertex, `D` decides
membership in `X`, and `t` is the parent of `s`. -/
private theorem val_gusfieldStep {n : ℕ} (p : Fin n → Fin n) (s : Fin n) (X : Finset (Fin n))
    (P : ℕ → ℕ) (D : ℕ → Prop) [DecidablePred D] (t : ℕ) (hP : ∀ y : Fin n, P y.1 = (p y).1)
    (hD : ∀ y : Fin n, y ∈ X ↔ D y.1) (ht : t = (p s).1) (z : Fin n) :
    (gusfieldStep p s X z).1 =
      if z.1 = s.1 then (if D (P t) then P t else t)
      else if z.1 = t then (if D (P t) then s.1 else P t)
      else if P z.1 = t ∧ D z.1 then s.1 else P z.1 := by
  subst ht
  rw [hP (p s), hP z]
  simp only [← hD, Fin.val_inj]
  unfold gusfieldStep
  split_ifs <;> rfl

/-- `gusfieldStepWeight` in terms of word-level data, as in `val_gusfieldStep`; `Wt` reads the
weight of a vertex. -/
private theorem gusfieldStepWeight_eq {n : ℕ} (p : Fin n → Fin n) (w : Fin n → ℕ) (s : Fin n)
    (X : Finset (Fin n)) (v : ℕ) (P Wt : ℕ → ℕ) (D : ℕ → Prop) [DecidablePred D] (t : ℕ)
    (hP : ∀ y : Fin n, P y.1 = (p y).1) (hW : ∀ y : Fin n, Wt y.1 = w y)
    (hD : ∀ y : Fin n, y ∈ X ↔ D y.1) (ht : t = (p s).1) (z : Fin n) :
    gusfieldStepWeight p w s X v z =
      if D (P t) then (if z.1 = s.1 then Wt t else if z.1 = t then v else Wt z.1)
      else if z.1 = s.1 then v else Wt z.1 := by
  subst ht
  rw [hP (p s), hW (p s), hW z]
  simp only [← hD, Fin.val_inj]
  unfold gusfieldStepWeight
  split_ifs <;> rfl

/-- The matrix `W` is stored row-major from address `3`. -/
private def MatrixLoaded {n : ℕ} (W : Fin n → Fin n → ℕ) (s : Memory.State) : Prop :=
  ∀ u v : Fin n, s.mem (3 + u.1 * n + v.1) = W u v

/-- After processing the first `k` vertices, the parent and weight arrays hold the result of
Gusfield's algorithm on them for some valid cut and value oracles. -/
private def GusfieldAt {n : ℕ} (W : Fin n → Fin n → ℕ) (r : Fin n) (k : ℕ) (s : Memory.State) :
    Prop :=
  ∃ (C : Fin n → Fin n → Finset (Fin n)) (val : Fin n → Fin n → ℕ),
    (∀ a b, a ≠ b → IsMinCutBetween (cutWeight W) a b (C a b)) ∧
    (∀ a b, a ≠ b → val a b = cutWeight W (C a b)) ∧
    ∀ z : Fin n,
      s.mem (parBase n + z.1) =
          ((gusfieldWeightLoop C val r ((List.finRange n).take k) (fun _ => r)
            (fun _ => 0)).1 z).1 ∧
        s.mem (wtBase n + z.1) =
          (gusfieldWeightLoop C val r ((List.finRange n).take k) (fun _ => r) (fun _ => 0)).2 z

private theorem lt_of_mem_take_finRange {n k : ℕ} {x : Fin n}
    (hx : x ∈ (List.finRange n).take k) : x.1 < k := by
  obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.mp hx
  rw [List.getElem_finRange, Fin.val_cast]
  exact lt_of_lt_of_le hj (min_le_left _ _)

/-- One step of the program advances the invariant: the machine's Edmonds–Karp cut replaces the
oracle at the queried pair, which the earlier steps never query. -/
private theorem gusfieldAt_ghStep {n : ℕ} {W : Fin n → Fin n → ℕ} {r : Fin n} {M k : ℕ}
    (hk : k < n) (hWM : ∀ u v, W u v ≤ M) {st : Memory.State} (hW : MatrixLoaded W st)
    (hG : GusfieldAt W r k st) :
    MatrixLoaded W ((Memory.spec 0).clientState st (ghStep ((n, r.1, M), k))) ∧
      GusfieldAt W r (k + 1) ((Memory.spec 0).clientState st (ghStep ((n, r.1, M), k))) := by
  obtain ⟨C, val, hC, hval, hmem⟩ := hG
  generalize hres : gusfieldWeightLoop C val r ((List.finRange n).take k) (fun _ => r)
    (fun _ => 0) = res at hmem
  by_cases hkr : k = r.1
  · have hst : (Memory.spec 0).clientState st (ghStep ((n, r.1, M), k)) = st := by
      unfold ghStep
      rw [clientState_bind_read, ite_eq_left hkr]
      rfl
    rw [hst]
    refine ⟨hW, C, val, hC, hval, fun z => ?_⟩
    rw [List.take_succ_finRange hk, gusfieldWeightLoop_append, hres,
      ite_eq_left (Fin.ext hkr : (⟨k, hk⟩ : Fin n) = r)]
    exact hmem z
  have hP : ∀ y : Fin n, st.mem (parBase n + y.1) = (res.1 y).1 := fun y => (hmem y).1
  have hWt : ∀ y : Fin n, st.mem (wtBase n + y.1) = res.2 y := fun y => (hmem y).2
  have hpar : ∀ z < n, st.mem (parBase n + z) < n := fun z hz => (hP ⟨z, hz⟩) ▸ (res.1 _).2
  have hsr : (⟨k, hk⟩ : Fin n) ≠ r := fun h => hkr (congrArg Fin.val h)
  obtain ⟨hlow, hpar', hwt'⟩ := ghStep_spec (r := r.1) (B := M) hk hkr hpar (hP ⟨k, hk⟩)
  set X : Finset (Fin n) := Finset.univ.filter fun x =>
    ((Memory.spec 0).clientState st (ekProg (ghCtx n M, (k, (res.1 ⟨k, hk⟩).1)))).mem
      (distBase n + x.1) < n with hX
  have hmemX : ∀ x : Fin n, x ∈ X ↔
      ((Memory.spec 0).clientState st (ekProg (ghCtx n M, (k, (res.1 ⟨k, hk⟩).1)))).mem
        (distBase n + x.1) < n := fun x => by
    rw [hX, Finset.mem_filter]
    exact and_iff_right (Finset.mem_univ x)
  have hspec : (⟨k, hk⟩ : Fin n) ≠ res.1 ⟨k, hk⟩ →
      IsMinCutBetween (cutWeight W) ⟨k, hk⟩ (res.1 ⟨k, hk⟩) X ∧
        (Memory.spec 0).clientResult st (ekProg (ghCtx n M, (k, (res.1 ⟨k, hk⟩).1))) =
          cutWeight W X := fun hne =>
    let h := ekProg_spec (mb := 3) (sb := scrBase n) hne hWM (by dsimp only [scrBase]; omega) hW
    ⟨h.2.1, h.2.2⟩
  let C' : Fin n → Fin n → Finset (Fin n) := fun a b =>
    if a = ⟨k, hk⟩ ∧ b = res.1 ⟨k, hk⟩ then X else C a b
  let val' : Fin n → Fin n → ℕ := fun a b =>
    if a = ⟨k, hk⟩ ∧ b = res.1 ⟨k, hk⟩ then
      (Memory.spec 0).clientResult st (ekProg (ghCtx n M, (k, (res.1 ⟨k, hk⟩).1)))
    else val a b
  have hC' : ∀ a b, a ≠ b → IsMinCutBetween (cutWeight W) a b (C' a b) := by
    intro a b hab
    by_cases h : a = ⟨k, hk⟩ ∧ b = res.1 ⟨k, hk⟩
    · obtain ⟨rfl, rfl⟩ := h
      simp only [C', and_self, ↓reduceIte]
      exact (hspec hab).1
    · simp only [C', h, ↓reduceIte]
      exact hC a b hab
  have hval' : ∀ a b, a ≠ b → val' a b = cutWeight W (C' a b) := by
    intro a b hab
    by_cases h : a = ⟨k, hk⟩ ∧ b = res.1 ⟨k, hk⟩
    · obtain ⟨rfl, rfl⟩ := h
      simp only [val', C', and_self, ↓reduceIte]
      exact (hspec hab).2
    · simp only [val', C', h, ↓reduceIte]
      exact hval a b hab
  have hpre : gusfieldWeightLoop C' val' r ((List.finRange n).take k) (fun _ => r)
      (fun _ => 0) = res := by
    rw [← hres]
    refine (gusfieldWeightLoop_congr r (fun a ha => ⟨funext fun b => ?_, funext fun b => ?_⟩)
      _ _).symm <;>
    · have hlt := lt_of_mem_take_finRange ha
      refine (ite_eq_right fun h => ?_).symm
      have h1 := congrArg Fin.val h.1
      dsimp only at h1
      omega
  have hnew : gusfieldWeightLoop C' val' r ((List.finRange n).take (k + 1)) (fun _ => r)
      (fun _ => 0) =
        (gusfieldStep res.1 ⟨k, hk⟩ X, gusfieldStepWeight res.1 res.2 ⟨k, hk⟩ X
          ((Memory.spec 0).clientResult st (ekProg (ghCtx n M, (k, (res.1 ⟨k, hk⟩).1))))) := by
    rw [List.take_succ_finRange hk, gusfieldWeightLoop_append, hpre, ite_eq_right hsr]
    simp only [C', val', and_self, ↓reduceIte]
  refine ⟨fun u v => ?_, C', val', hC', hval', fun z => ?_⟩
  · have huv : u.1 * n + v.1 < n * n := by nlinarith [u.2, v.2]
    rw [hlow _ (by dsimp only [parBase]; omega)]
    exact hW u v
  · rw [hnew]
    refine ⟨(hpar' z.1 z.2).trans ?_, (hwt' z.1 z.2).trans ?_⟩
    · exact (val_gusfieldStep res.1 ⟨k, hk⟩ X (fun y => st.mem (parBase n + y))
        (fun y => ((Memory.spec 0).clientState st
          (ekProg (ghCtx n M, (k, (res.1 ⟨k, hk⟩).1)))).mem (distBase n + y) < n)
        ((res.1 ⟨k, hk⟩).1) hP hmemX rfl z).symm
    · exact (gusfieldStepWeight_eq res.1 res.2 ⟨k, hk⟩ X _ (fun y => st.mem (parBase n + y))
        (fun y => st.mem (wtBase n + y))
        (fun y => ((Memory.spec 0).clientState st
          (ekProg (ghCtx n M, (k, (res.1 ⟨k, hk⟩).1)))).mem (distBase n + y) < n)
        ((res.1 ⟨k, hk⟩).1) hP hWt hmemX rfl z).symm

/-! ### The input -/

private theorem init_frontier {n : ℕ} (W : Fin n → Fin n → ℕ) (r : Fin n) :
    (Memory.State.init (encodeInput W r)).frontier = 3 + n * n := by
  change (encodeInput W r).length + 1 = 3 + n * n
  simp only [encodeInput, List.length_cons, length_flattenMatrix]
  omega

private theorem init_mem_matrix {n : ℕ} (W : Fin n → Fin n → ℕ) (r : Fin n) {i : ℕ}
    (hi : i < n * n) :
    (Memory.State.init (encodeInput W r)).mem (3 + i) =
      (flattenMatrix W)[i]'(by rw [length_flattenMatrix]; exact hi) := by
  change (if 3 + i = 0 then (encodeInput W r).length
    else (encodeInput W r).getD (3 + i - 1) 0) = _
  rw [ite_eq_right (by omega), show 3 + i - 1 = i + 2 by omega]
  change (flattenMatrix W).getD i 0 = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some]

private theorem matrixLoaded_init {n : ℕ} (W : Fin n → Fin n → ℕ) (r : Fin n) :
    MatrixLoaded W (Memory.State.init (encodeInput W r)) := fun u v => by
  have hlt : u.1 * n + v.1 < n * n := by nlinarith [u.2, v.2]
  rw [Nat.add_assoc, init_mem_matrix W r hlt, getElem_flattenMatrix]

private theorem init_le {n : ℕ} {W : Fin n → Fin n → ℕ} (r : Fin n) {B : ℕ}
    (hB : ∀ u v, W u v ≤ B) {i : ℕ} (hi : i < n * n) :
    (Memory.State.init (encodeInput W r)).mem (3 + i) ≤ B := by
  have hn : 0 < n := Nat.pos_of_ne_zero fun h => by simp [h] at hi
  have hu : i / n < n := Nat.div_lt_of_lt_mul hi
  have hv : i % n < n := Nat.mod_lt i hn
  have hidx : 3 + i = 3 + (⟨i / n, hu⟩ : Fin n).1 * n + (⟨i % n, hv⟩ : Fin n).1 := by
    dsimp only
    rw [Nat.add_assoc, Nat.div_add_mod']
  rw [hidx, matrixLoaded_init W r]
  exact hB _ _

private theorem inputFits_encodeInput {n : ℕ} {W : Fin n → Fin n → ℕ} (r : Fin n) {B w : ℕ}
    (hB : ∀ u v, W u v ≤ B) (hw : Fits w (ghWorkspace n)) (hwB : Fits w (ekBound n B)) :
    InputFits w (encodeInput W r) := by
  have hBw : Fits w B := hwB.of_le (by unfold ekBound; omega)
  refine ⟨hw.of_le ?_, fun x hx => ?_⟩
  · simp only [encodeInput, List.length_cons, length_flattenMatrix, ghWorkspace]
    omega
  · simp only [encodeInput, List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · exact hw.of_le (by unfold ghWorkspace; omega)
    · exact hw.of_le (by unfold ghWorkspace; omega)
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      rw [length_flattenMatrix] at hi
      rw [← init_mem_matrix W r hi]
      exact hBw.of_le (init_le r hB hi)

/-! ### Admissibility -/

private abbrev MemReady (w n : ℕ) (s : Memory.State) : Prop :=
  Memory.WellFormed w s ∧ ghWorkspace n ≤ s.frontier

private theorem validHistory_maxScan {w n : ℕ} {st : Memory.State} (hs : MemReady w n st) :
    (Memory.spec w).ValidHistory st
      ((Memory.spec w).clientHistory st (iterate maxStep 3 (n * n) (0, 0))) := by
  refine validHistory_iterate_fst (Inv := MemReady w n) (n * n) 0 0
    (fun i hi b u hu => ⟨?_, ?_⟩) hs
  · have hfr := hu.2
    unfold maxStep
    dsimp only [ghWorkspace] at hfr ⊢
    refine validHistory_read_bind (by omega) ?_
    exact validHistory_ite (fun _ => validHistory_pure _ _ _) (fun _ => validHistory_pure _ _ _)
  · unfold maxStep
    rw [clientResult_bind_read]
    split_ifs <;> rfl

private theorem validHistory_rehang {w n s t : ℕ} {st : Memory.State} (hs : MemReady w n st)
    (hsn : s < n) :
    (Memory.spec w).ValidHistory st
      ((Memory.spec w).clientHistory st (iterate rehangStep ((n, s), t) n 0)) := by
  refine validHistory_iterate_nat (Inv := MemReady w n) n 0 (fun z hz u hu => ⟨?_, ?_⟩) hs
  · have hfit : Fits w (ghWorkspace n) := hu.1.frontier_fits.of_le hu.2
    have hfr := hu.2
    unfold rehangStep
    dsimp only [ghWorkspace, parBase, distBase] at hfr hfit ⊢
    refine validHistory_read_bind (by omega) ?_
    refine validHistory_read_bind (by omega) ?_
    refine validHistory_ite (fun _ => ?_) (fun _ => validHistory_pure _ _ _)
    exact validHistory_write_bind (by omega) (hfit.of_le (by omega)) (validHistory_pure _ _ _)
  · unfold rehangStep
    rw [clientResult_bind_read, clientResult_bind_read]
    split_ifs <;> rfl

private theorem ekProg_result_le_ekBound (n B k t : ℕ) (st : Memory.State) :
    (Memory.spec 0).clientResult st (ekProg (ghCtx n B, (k, t))) ≤ ekBound n B := by
  have h := ekProg_result_le (ghCtx n B) k t st
  dsimp only [ghCtx] at h ⊢
  have : n * n * (n + B) = n * n * n + n * n * B := Nat.mul_add _ _ _
  unfold ekBound
  omega

private theorem validHistory_ghStep {w n r B k : ℕ} {st : Memory.State} (hs : MemReady w n st)
    (hB : Fits w (ekBound n B)) (hk : k < n) :
    (Memory.spec w).ValidHistory st ((Memory.spec w).clientHistory st (ghStep ((n, r, B), k))) := by
  have hfit : Fits w (ghWorkspace n) := hs.1.frontier_fits.of_le hs.2
  have hfr := hs.2
  unfold ghStep
  dsimp only [ghWorkspace, parBase, wtBase, distBase, scrBase] at hfr hfit ⊢
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_ite (fun _ => validHistory_pure _ _ _) (fun _ => ?_)
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_ite (fun ht => ?_) (fun _ => validHistory_pure _ _ _)
  have hek := validHistory_ekProg (c := ghCtx n B) (src := k) (snk := st.mem (3 + n * n + k))
    ⟨by dsimp only [ghCtx, scrBase]; omega,
      hfit.of_le (by dsimp only [ghCtx, ekScratch, scrBase]; omega), hB⟩
    hk ht hs.1 (by dsimp only [ghCtx, ekScratch, scrBase]; omega)
  refine validHistory_bind_step hek ?_
  have hs1 := MonotoneMemInv.pres hs hek
  have hr := validHistory_rehang (t := st.mem (3 + n * n + k)) hs1 hk
  refine validHistory_bind_step hr ?_
  have hs2 := MonotoneMemInv.pres hs1 hr
  have hv := hB.of_le (ekProg_result_le_ekBound n B k (st.mem (3 + n * n + k)) st)
  have hfr2 := hs2.2
  dsimp only [ghWorkspace] at hfr2
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => validHistory_pure _ _ _)
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => ?_)
  · refine validHistory_read_bind (by omega) ?_
    refine validHistory_write_bind (by omega) (hfit.of_le (by omega)) ?_
    refine validHistory_write_bind (by dsimp only; omega) (hs2.1.mem_fits _) ?_
    refine validHistory_write_bind (by dsimp only; omega) hv ?_
    exact validHistory_write_bind (by dsimp only; omega) (hs2.1.mem_fits _)
      (validHistory_pure _ _ _)
  · exact validHistory_write_bind (by omega) hv (validHistory_pure _ _ _)

private theorem clientState_maxScan (n : ℕ) (st : Memory.State) :
    (Memory.spec 0).clientState st (iterate maxStep 3 (n * n) (0, 0)) = st :=
  clientState_iterate_eq_of maxStep 3 (fun a t => by
    unfold maxStep
    rw [clientState_bind_read]
    split_ifs <;> rfl) _ _ _

private theorem validHistory_ghMain {w n r B : ℕ} {st : Memory.State}
    (hwf : Memory.WellFormed w st) (hfr : st.frontier = 3 + n * n) (hw : Fits w (ghWorkspace n))
    (hr : Fits w r) (hB : ∀ i < n * n, st.mem (3 + i) ≤ B) (hwB : Fits w (ekBound n B)) :
    (Memory.spec w).ValidHistory st ((Memory.spec w).clientHistory st (ghMain (n, r))) := by
  unfold ghMain
  dsimp only
  have halloc : (Memory.spec w).ValidHistory st
      ((Memory.spec w).clientHistory st (Memory.alloc (ghScratch n))) :=
    validHistory_alloc (by rw [hfr, input_add_ghScratch]; exact hw)
  refine validHistory_bind_step halloc ?_
  have hs1 : MemReady w n ((Memory.spec 0).clientState st (Memory.alloc (ghScratch n))) := by
    refine ⟨wellFormed_clientState hwf halloc, ?_⟩
    change ghWorkspace n ≤ st.frontier + ghScratch n
    rw [hfr, input_add_ghScratch]
  have hal : ∀ i < n * n,
      ((Memory.spec 0).clientState st (Memory.alloc (ghScratch n))).mem (3 + i) ≤ B :=
    fun i hi => (Memory.mem_step_of_lt_frontier st (.alloc (ghScratch n))
      (by rw [hfr]; omega) (by simp)).trans_le (hB i hi)
  have hM := (maxScan_spec hal).1
  have hmx := validHistory_maxScan hs1
  refine validHistory_bind_step hmx ?_
  rw [clientState_maxScan]
  have hfr1 := hs1.2
  dsimp only [ghWorkspace] at hfr1
  have hf1 := validHistory_fillRange (base := parBase n) (val := r) (len := n) hs1.1
    (by dsimp only [parBase]; omega) hr
  refine validHistory_bind_step hf1 ?_
  have hs3 := MonotoneMemInv.pres hs1 hf1
  have hfr3 := hs3.2
  dsimp only [ghWorkspace] at hfr3
  have hf2 := validHistory_fillRange (base := wtBase n) (val := 0) (len := n) hs3.1
    (by dsimp only [wtBase]; omega)
    (fits_zero w)
  refine validHistory_bind_step hf2 ?_
  have hs4 := MonotoneMemInv.pres hs3 hf2
  refine validHistory_bind_step (validHistory_iterate_nat (Inv := MemReady w n) n 0
    (fun k hk u hu => ⟨validHistory_ghStep hu (hwB.of_le (by unfold ekBound; gcongr)) (by omega),
      clientResult_ghStep _ _ _ _ _⟩) hs4) (validHistory_pure _ _ _)

private theorem validHistory_ghProg {n : ℕ} {W : Fin n → Fin n → ℕ} (r : Fin n) {B w : ℕ}
    (hB : ∀ u v, W u v ≤ B) (hw : Fits w (ghWorkspace n)) (hwB : Fits w (ekBound n B)) :
    (Memory.spec w).ValidHistory (Memory.State.init (encodeInput W r))
      ((Memory.spec w).clientHistory (Memory.State.init (encodeInput W r)) (ghProg ())) := by
  have hfr := init_frontier W r
  have hin := inputFits_encodeInput r hB hw hwB
  have hwf : Memory.WellFormed w (Memory.State.init (encodeInput W r)) :=
    Memory.wellFormed_init hin (by rw [← init_frontier W r] at hfr; exact hw.of_le (by
      simp only [encodeInput, List.length_cons, length_flattenMatrix, ghWorkspace]
      omega))
  unfold ghProg
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_read_bind (by omega) ?_
  exact validHistory_ghMain hwf hfr hw (hw.of_le (by
    change r.1 ≤ ghWorkspace n
    have := r.2
    unfold ghWorkspace
    omega)) (fun i hi => init_le r hB hi) hwB

/-! ### Memory-operation counts -/

private theorem memoryCost_maxStep_le (d : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (maxStep d) s ≤ 1 := by
  unfold maxStep
  exact memoryCost_read_bind_le fun _ _ => memoryCost_ite_le (by simp) (by simp)

private theorem memoryCost_rehangStep_le (d : ((ℕ × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (rehangStep d) s ≤ 3 := by
  unfold rehangStep
  exact memoryCost_read_bind_le fun _ _ => memoryCost_read_bind_le fun _ _ =>
    memoryCost_ite_le (memoryCost_write_bind_le fun _ _ => by simp) (by simp)

private theorem memoryCost_ghStep_le (n r B k : ℕ) (s : Memory.State) :
    memoryCost (ghStep ((n, r, B), k)) s ≤ ekCost n + 3 * n + 9 := by
  unfold ghStep
  dsimp only
  refine (memoryCost_read_bind_le (k := ekCost n + 3 * n + 8) fun _ t => ?_).trans (by omega)
  refine memoryCost_ite_le (by simp) ?_
  refine (memoryCost_read_bind_le (k := ekCost n + 3 * n + 7) fun x t => ?_).trans (by omega)
  refine memoryCost_ite_le ?_ (by simp)
  have hek : memoryCost (ekProg (ghCtx n B, (k, x))) t ≤ ekCost n :=
    memoryCost_ekProg_le (ghCtx n B) k x t
  refine (memoryCost_bind_le (k₁ := ekCost n) (k₂ := 3 * n + 7) hek
    fun _ t => ?_).trans (by omega)
  refine (memoryCost_bind_le (k₁ := 3 * n) (k₂ := 7)
    (memoryCost_iterate_le_of rehangStep 3 _ (fun _ _ => memoryCost_rehangStep_le _ _) n 0 _)
    fun _ t => ?_).trans (by omega)
  refine (memoryCost_read_bind_le (k := 6) fun _ t => ?_).trans (by omega)
  refine memoryCost_ite_le ?_ (by simp)
  refine (memoryCost_read_bind_le (k := 5) fun _ t => ?_).trans (by omega)
  refine memoryCost_ite_le ?_ ?_
  · refine (memoryCost_read_bind_le (k := 4) fun _ t => ?_).trans (by omega)
    exact memoryCost_write_bind_le fun _ _ => memoryCost_write_bind_le fun _ _ =>
      memoryCost_write_bind_le fun _ _ => memoryCost_write_bind_le fun _ _ => by simp
  · exact (memoryCost_write_bind_le (k := 0) fun _ _ => by simp).trans (by omega)

private theorem ghCost_arith (n : ℕ) :
    2 * n + (n * n + 2 * n) + 1 +
        (1 * (n * n) + (n + (n + ((20 * (n + 1) ^ 5 + 3 * n + 9) * n + 0)))) ≤
      38 * (n + 1) ^ 6 := by
  have h6 : (n + 1) ^ 6 = (n + 1) ^ 5 * (n + 1) := pow_succ _ _
  have h5 : (n + 1) ^ 2 ≤ (n + 1) ^ 5 := Nat.pow_le_pow_right (Nat.succ_pos n) (by norm_num)
  have h1 : 1 ≤ (n + 1) ^ 5 := Nat.one_le_pow _ _ (Nat.succ_pos n)
  nlinarith

private theorem memoryCost_ghMain_le (n r : ℕ) (s : Memory.State) :
    memoryCost (ghMain (n, r)) s ≤ 38 * (n + 1) ^ 6 := by
  unfold ghMain
  dsimp only
  refine le_trans (memoryCost_bind_le (memoryCost_alloc _ _).le fun _ t => ?_) (ghCost_arith n)
  refine memoryCost_bind_le (memoryCost_iterate_le_of maxStep 1 3
    (fun _ _ => memoryCost_maxStep_le _ _) (n * n) (0, 0) t) fun m t => ?_
  refine memoryCost_bind_le (memoryCost_fillRange_le (parBase n) r n t) fun _ t => ?_
  refine memoryCost_bind_le (memoryCost_fillRange_le (wtBase n) 0 n t) fun _ t => ?_
  exact memoryCost_bind_le (memoryCost_iterate_le_of ghStep (ekCost n + 3 * n + 9) _
    (fun k t => memoryCost_ghStep_le n r m.2 k t) n 0 t) fun _ t => by simp

private theorem memoryCost_ghProg_le (s : Memory.State) :
    memoryCost (ghProg ()) s ≤ 40 * (s.mem 1 + 1) ^ 6 := by
  unfold ghProg
  rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read, memoryCost_bind',
    memoryCost_read, clientResult_read, clientState_read]
  have h := memoryCost_ghMain_le (s.mem 1) (s.mem 2) s
  have h1 : 1 ≤ (s.mem 1 + 1) ^ 6 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  omega

/-! ### Correctness -/

/-- The program leaves Gusfield's algorithm with valid oracles on all `n` vertices in memory. -/
private theorem gusfieldAt_ghProg {n : ℕ} {W : Fin n → Fin n → ℕ} (r : Fin n) {B : ℕ}
    (hB : ∀ u v, W u v ≤ B) :
    GusfieldAt W r n
      ((Memory.spec 0).clientState (Memory.State.init (encodeInput W r)) (ghProg ())) := by
  have hfr0 := init_frontier W r
  have hW0 := matrixLoaded_init W r
  have e0 : (Memory.spec 0).clientState (Memory.State.init (encodeInput W r)) (ghProg ()) =
      (Memory.spec 0).clientState (Memory.State.init (encodeInput W r)) (ghMain (n, r.1)) := by
    unfold ghProg
    rw [clientState_bind_read, clientState_bind_read]
    rfl
  have hent : ∀ i < n * n, (Memory.State.init (encodeInput W r)).mem (3 + i) ≤ B :=
    fun i hi => init_le r hB hi
  rw [e0]
  generalize Memory.State.init (encodeInput W r) = s₀ at hfr0 hW0 hent
  unfold ghMain
  dsimp only
  have hal : ∀ a < 3 + n * n,
      ((Memory.spec 0).clientState s₀ (Memory.alloc (ghScratch n))).mem a = s₀.mem a :=
    fun a ha => Memory.mem_step_of_lt_frontier s₀ (.alloc _) (by rw [hfr0]; exact ha) (by simp)
  rw [StateTransitionSpec.clientState_bind]
  generalize (Memory.spec 0).clientState s₀ (Memory.alloc (ghScratch n)) = s_al at hal ⊢
  rw [StateTransitionSpec.clientState_bind, clientState_maxScan]
  have hent' : ∀ i < n * n, s_al.mem (3 + i) ≤ B := fun i hi =>
    (hal _ (by omega)).trans_le (hent i hi)
  obtain ⟨-, hMall⟩ := maxScan_spec hent'
  generalize ((Memory.spec 0).clientResult s_al (iterate maxStep 3 (n * n) (0, 0))).2 = M
    at hMall ⊢
  have hWM : ∀ u v : Fin n, W u v ≤ M := fun u v => by
    have hlt : u.1 * n + v.1 < n * n := by nlinarith [u.2, v.2]
    have h := hMall _ hlt
    rwa [← Nat.add_assoc, hal _ (by omega), hW0 u v] at h
  rw [StateTransitionSpec.clientState_bind]
  obtain ⟨hp1, hp1fr⟩ := fillRange_spec (parBase n) r.1 n s_al
  generalize (Memory.spec 0).clientState s_al (fillRange ((parBase n, r.1), n)) = s_p
    at hp1 hp1fr ⊢
  rw [StateTransitionSpec.clientState_bind]
  obtain ⟨hw1, hw1fr⟩ := fillRange_spec (wtBase n) 0 n s_p
  generalize (Memory.spec 0).clientState s_p (fillRange ((wtBase n, 0), n)) = s_w at hw1 hw1fr ⊢
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure]
  have hWw : MatrixLoaded W s_w := fun u v => by
    have hlt : u.1 * n + v.1 < n * n := by nlinarith [u.2, v.2]
    rw [hw1fr _ (Or.inl (by dsimp only [wtBase]; omega)),
      hp1fr _ (Or.inl (by dsimp only [parBase]; omega)), hal _ (by omega)]
    exact hW0 u v
  have hG0 : GusfieldAt W r 0 s_w := by
    have hex : ∀ a b : Fin n, a ≠ b → ∃ X, IsMinCutBetween (cutWeight W) a b X :=
      fun a b hab => exists_isMinCutBetween _ hab
    choose! C₀ hC₀ using hex
    refine ⟨C₀, fun a b => cutWeight W (C₀ a b), hC₀, fun _ _ _ => rfl, fun z => ?_⟩
    rw [List.take_zero]
    refine ⟨?_, ?_⟩
    · rw [hw1fr _ (Or.inl (by dsimp only [parBase, wtBase]; omega)), hp1 z.1 z.2]
      rfl
    · rw [hw1 z.1 z.2]
      rfl
  obtain ⟨hsum, -, hG⟩ := iterate_invariant_of ghStep (n, r.1, M)
    (fun rem k st => k + rem = n ∧ MatrixLoaded W st ∧ GusfieldAt W r k st)
    (fun rem k st ⟨hsum, hW, hG⟩ => by
      rw [clientResult_ghStep]
      obtain ⟨h1, h2⟩ := gusfieldAt_ghStep (by omega) hWM hW hG
      exact ⟨by omega, h1, h2⟩)
    (n := n) (a := 0) (s := s_w) ⟨Nat.zero_add _, hWw, hG0⟩
  rw [Nat.add_zero] at hsum
  rw [hsum] at hG
  exact hG

/-! ### The uniform program -/

/-- **Gusfield's Gomory–Hu tree algorithm on the Word-RAM** ([Gusfield1990], with
[EdmondsKarp1972] as the maximum flow subroutine): one flat program over `Basis.exact` that, on
the input `encodeInput W r` of a weighted multigraph `W` on `Fin n` with entries at most `B` and a
root `r`, halts within `C * (n + 1) ^ 6` instructions at every word width `w` that fits the
workspace `ghWorkspace n` and the subroutine's word bound `ekBound n B`. The final memory holds a
parent function `p` rooted at `r` whose parent graph is a Gomory–Hu tree of `W` (at `parAddr n u`)
and the minimum cut weight `minCutBetween W u (p u)` of every tree edge (at `wtAddr n u`, `0` at
the root). -/
theorem exists_gomoryHu_program :
    ∃ (R C pc : ℕ), 0 < C ∧ ∃ prog : Program .exact R,
      ∀ {n : ℕ} (W : Fin n → Fin n → ℕ) (r : Fin n) (B w : ℕ), IsMultigraph W →
        (∀ u v, W u v ≤ B) → Fits w (ghWorkspace n) → Fits w (ekBound n B) →
        ∃ (y : Data R) (steps res : ℕ) (p : Fin n → Fin n),
          Runs w prog (State.init (encodeInput W r)) ⟨pc, y⟩ steps ∧
          step w prog ⟨pc, y⟩ = .halt res ∧
          steps + 1 ≤ C * (n + 1) ^ 6 ∧
          (∀ u, y.mem (parAddr n u.1) = (p u).1) ∧ p r = r ∧
          IsGomoryHuTree (cutWeight W) (parentGraph p) ∧
          ∀ u, y.mem (wtAddr n u.1) = minCutBetween W u (p u) := by
  obtain ⟨R, C₀, pc, prog, frontier, _, hprog⟩ :=
    ghProg_realizes.exists_standard_init_program_state_from_words 0
  refine ⟨R, 41 * C₀ + 2, pc, by omega, prog, ?_⟩
  intro n W r B w hW hB hw hwB
  have hfr := init_frontier W r
  have hlen : Fits w ((encodeInput W r).length + 1) := hw.of_le (by
    simp only [encodeInput, List.length_cons, length_flattenMatrix, ghWorkspace]
    omega)
  obtain ⟨y, steps, hruns, hhalt, hmem, _, hbound⟩ :=
    hprog w () (encodeInput W r) (fun j => Fin.elim0 j) (Nat.zero_le _) hlen
      (inputFits_encodeInput r hB hw hwB) ⟨hfr, hw, B, fun i hi => init_le r hB hi, hwB⟩
      (validHistory_ghProg r hB hw hwB)
  rw [clientState_width w (ghProg ())] at hmem
  have hymem : y.mem =
      ((Memory.spec 0).clientState (Memory.State.init (encodeInput W r)) (ghProg ())).mem :=
    congrArg Memory.State.mem hmem
  obtain ⟨C, val, hC, hval, hcells⟩ := gusfieldAt_ghProg r hB
  rw [List.take_of_length_le (by rw [List.length_finRange])] at hcells
  obtain ⟨htree, hroot, hwroot, hside⟩ :=
    gusfieldWithWeights_spec (cutWeight_compl' hW) (isSubmodular_cutWeight W) hC hval r 0
      (List.nodup_finRange n) (fun x _ => List.mem_finRange x)
  have hmc : memoryCost (ghProg ()) (Memory.State.init (encodeInput W r)) ≤ 40 * (n + 1) ^ 6 :=
    memoryCost_ghProg_le _
  have hp : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (Nat.succ_pos n)
  refine ⟨y, steps, _, (gusfieldWithWeights C val r 0 (List.finRange n)).1, hruns, hhalt, ?_,
    fun u => ?_, hroot, htree, fun u => ?_⟩
  · calc steps + 1
        ≤ C₀ * (memoryCost (ghProg ()) (Memory.State.init (encodeInput W r)) + 0 + 1) + 1 :=
          hbound
      _ ≤ C₀ * (40 * (n + 1) ^ 6 + 1) + 1 :=
          Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) 1
      _ ≤ (41 * C₀ + 2) * (n + 1) ^ 6 := by nlinarith
  · rw [hymem]
    exact (hcells u).1
  · rw [hymem]
    refine (hcells u).2.trans ?_
    change (gusfieldWithWeights C val r 0 (List.finRange n)).2 u = _
    by_cases hur : u = r
    · subst hur
      rw [hwroot, hroot, minCutBetween_self]
    · obtain ⟨hcut, hwt⟩ := hside u hur
      rw [hwt]
      exact ((isMinCutBetween_cutWeight_iff W).mp hcut).2.2

end Cslib.Algorithms.WordRAM.GomoryHu
