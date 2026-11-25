/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.OddCycleTransversal.NetworkProg
import CslibFrontier.Tactic.Realize
import Mathlib.Tactic.Linarith

/-!
# Compression leaf, base-3 odometer, and outer `octProg` Word-RAM programs

This module defines the `Memory.Prog` routines implementing Hüffner's three-way compression leaf
(`buildWProg`, `unpackGuessProg`, `checkProperProg`, `buildTerminalsProg`, `countDelProg`,
`commitLeafProg`, `leafProg`), the base-3 odometer (`incOdomProg`, `compressProg`), and the
top-level iterative-compression loop (`octStep`, `octProg`), together with `octProg_realizes`.

## Main definitions

* `Cslib.Algorithms.WordRAM.OddCycleTransversal.buildWProg`,
  `Cslib.Algorithms.WordRAM.OddCycleTransversal.unpackGuessProg`,
  `Cslib.Algorithms.WordRAM.OddCycleTransversal.checkProperProg`,
  `Cslib.Algorithms.WordRAM.OddCycleTransversal.buildTerminalsProg`,
  `Cslib.Algorithms.WordRAM.OddCycleTransversal.countDelProg`,
  `Cslib.Algorithms.WordRAM.OddCycleTransversal.commitLeafProg`,
  `Cslib.Algorithms.WordRAM.OddCycleTransversal.leafProg`: compression-leaf subroutines.
* `Cslib.Algorithms.WordRAM.OddCycleTransversal.incOdomProg`,
  `Cslib.Algorithms.WordRAM.OddCycleTransversal.base3At`,
  `Cslib.Algorithms.WordRAM.OddCycleTransversal.compressProg`: base-3 odometer enumeration.
* `Cslib.Algorithms.WordRAM.OddCycleTransversal.octProg`: top-level solver program.

## Main results

* `Cslib.Algorithms.WordRAM.OddCycleTransversal.incOdomProg_base3At`: arithmetic increment spec for
  the base-3 odometer.
* `Cslib.Algorithms.WordRAM.OddCycleTransversal.octProg_realizes`: exact-basis Word-RAM realization
  certificate for `octProg`.
-/

public section

namespace Cslib.Algorithms.WordRAM.OddCycleTransversal

open Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization
open StateTransitionSpec (clientResult_bind clientState_bind clientResult_pure clientState_pure)

attribute [local client_simps] runClient_read runClient_write StateTransitionSpec.clientState_map

private theorem iterationSafe_idx {δ σ : Type} (idx : σ → ℕ)
    (body : δ × σ → Memory.Prog σ) (safe : ℕ → δ × σ → Memory.State → Prop)
    (w : ℕ) (d : δ) {n : ℕ} {a₀ : σ} {s : Memory.State} (ha₀ : idx a₀ = 0)
    (hsafe : ∀ a t, idx a < n → safe w (d, a) t)
    (hstep : ∀ a t, idx ((Memory.spec 0).clientResult t (body (d, a))) = idx a + 1) :
    iterationSafe body safe w d n a₀ s :=
  iterationSafe_of_stepInv body safe w d (fun rem a _ => idx a + rem = n)
    (fun _ a t hsum =>
      ⟨hsafe a t (by omega),
        by rw [hstep]; omega⟩)
    (by omega)

/-! ### Compression leaf, base-3 odometer, and outer iterative compression -/

/-- Scan `v`, appending it to `wListBase` when `wBase n + v = 1`. -/
@[expose] def buildWListStep (d : ℕ × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let n := d.1
  let v := LoopAccArgs.idx d
  let L := LoopAccArgs.acc d
  let wv ← Memory.read (wBase n + v)
  if wv = 1 then
    Memory.write (wListBase n + L) v
    pure (v + 1, L + 1)
  else
    pure (v + 1, L)

private theorem buildWListStep_realizes :
    Realizes .exact buildWListStep (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w d _ => Fits w (octWorkspace d.1) ∧ d.2.1 < d.1 ∧ d.2.2 ≤ d.2.1)
      (fun _ _ => 0) := by
  unfold buildWListStep
  realize
  all_goals
    obtain ⟨hw, hv, hL⟩ := h
    dsimp -failIfUnchanged only [octWorkspace, wBase, wListBase,
      LoopAccArgs.idx, LoopAccArgs.acc] at *
    first | omega | (apply hw.of_le; omega)

theorem clientResult_buildWListStep (d : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    let res := (Memory.spec 0).clientResult s (buildWListStep d)
    res.1 = LoopAccArgs.idx d + 1 ∧ res.2 ≤ LoopAccArgs.acc d + 1 := by
  unfold buildWListStep
  rw [clientResult_bind_read]
  split_ifs <;> simp only [clientResult_bind_write, clientResult_pure] <;> exact ⟨trivial, by omega⟩

/-- Copy `sepBase` into `wBase`, insert `m`, and compact into `wListBase`. -/
@[expose] def buildWProg (d : ℕ × ℕ) : Memory.Prog ℕ := do
  let n := d.1
  let m := d.2
  copyRange ((sepBase n, wBase n), n)
  Memory.write (wBase n + m) 1
  let res ← iterate buildWListStep n n (0, 0)
  pure res.2

private theorem buildWProg_realizes :
    Realizes .exact buildWProg (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (octWorkspace d.1) ∧ d.2 < d.1) (fun _ _ => 0) := by
  unfold buildWProg
  realize [copyRange_realizes, buildWListStep_realizes]
  all_goals
    obtain ⟨hw, hm⟩ := h
    dsimp -failIfUnchanged only [octWorkspace, sepBase, wBase] at *
    try omega
    try (apply hw.of_le; omega)
  refine iterationSafe_of_stepInv _ _ w _
    (fun rem (vL : ℕ × ℕ) _ => vL.1 + rem = d.1 ∧ vL.2 ≤ vL.1) ?_ ⟨Nat.zero_add _, le_rfl⟩
  intro rem vL t ⟨hsum, hL⟩
  dsimp only
  refine ⟨⟨hw, by omega, hL⟩, ?_⟩
  obtain ⟨h1, h2⟩ := clientResult_buildWListStep (d.1, vL) t
  dsimp only [LoopAccArgs.idx, LoopAccArgs.acc] at h1 h2
  exact ⟨by omega, by omega⟩

/-- Single step of `unpackGuessProg`. -/
@[expose] def unpackStep (d : ℕ × ℕ) : Memory.Prog ℕ := do
  let n := d.1
  let j := d.2
  let wv ← Memory.read (wListBase n + j)
  let dg ← Memory.read (digitBase n + j)
  if wv < n ∧ dg ≤ 2 then
    Memory.write (guessBase n + wv) dg
    pure (j + 1)
  else
    pure (j + 1)

private theorem unpackStep_realizes :
    Realizes .exact unpackStep (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (octWorkspace d.1) ∧ d.2 < d.1) (fun _ _ => 0) := by
  unfold unpackStep
  realize
  all_goals
    obtain ⟨hw, hj⟩ := h
    dsimp -failIfUnchanged only [octWorkspace, wListBase, digitBase, guessBase] at *
    first | omega | (apply hw.of_le; omega)

theorem clientResult_unpackStep (d : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (unpackStep d) = d.2 + 1 := by
  unfold unpackStep
  rw [clientResult_bind_read, clientResult_bind_read]
  split_ifs <;> simp only [clientResult_bind_write, clientResult_pure]

/-- Scatter base-3 odometer digits from `digitBase` to `guessBase`. -/
@[expose] def unpackGuessProg (d : ℕ × ℕ) : Memory.Prog Unit := do
  let n := d.1
  let L := d.2
  fillRange ((guessBase n, 0), n)
  let _ ← iterate unpackStep n L 0
  pure ()

private theorem unpackGuessProg_realizes :
    Realizes .exact unpackGuessProg (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w d _ => Fits w (octWorkspace d.1) ∧ d.2 ≤ d.1) (fun _ _ => 0) := by
  unfold unpackGuessProg
  realize [fillRange_realizes, unpackStep_realizes]
  all_goals
    obtain ⟨hw, hL⟩ := h
    dsimp -failIfUnchanged only [octWorkspace, guessBase] at *
    try omega
    try (apply hw.of_le; omega)
  exact iterationSafe_idx (fun j => j) _ _ w _ rfl (fun _ _ hj => ⟨hw, hj.trans_le hL⟩)
    fun j => clientResult_unpackStep (d.1, j)

theorem preservesAt_unpackGuessProg {a : ℕ} {d : ℕ × ℕ} (ha : a < guessBase d.1) :
    PreservesAt a (unpackGuessProg d) := by
  unfold unpackGuessProg
  refine preservesAt_bind (preservesAt_fillRange (Or.inl ha)) fun _ => ?_
  refine preservesAt_bind (preservesAt_iterate (fun j => ?_) _ _) fun _ => preservesAt_pure _ _
  unfold unpackStep
  refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
  refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
  refine preservesAt_ite _ ?_ (preservesAt_pure _ _)
  exact preservesAt_bind
    (preservesAt_write _ (by dsimp only [guessBase] at ha ⊢; omega))
    fun _ => preservesAt_pure _ _

/-- Number of vertices in `properInnerStep` arguments `(((n, m), u), du), (j, ok)`. -/
abbrev ProperInnerArgs.n (d : (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) : ℕ := d.1.1.1.1

/-- Active vertex prefix bound in `properInnerStep` arguments. -/
abbrev ProperInnerArgs.m (d : (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) : ℕ := d.1.1.1.2

/-- Candidate vertex `u` in `properInnerStep` arguments. -/
abbrev ProperInnerArgs.u (d : (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) : ℕ := d.1.1.2

/-- Candidate colour `du` in `properInnerStep` arguments. -/
abbrev ProperInnerArgs.du (d : (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) : ℕ := d.1.2

/-- Scan index `j` in `properInnerStep` arguments. -/
abbrev ProperInnerArgs.j (d : (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) : ℕ := d.2.1

/-- Properness flag `ok` in `properInnerStep` arguments. -/
abbrev ProperInnerArgs.ok (d : (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) : ℕ := d.2.2

/-- Check proper colouring between candidate vertex `u` and the `j`-th entry of `W`. -/
@[expose] def properInnerStep (d : (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let n := ProperInnerArgs.n d
  let m := ProperInnerArgs.m d
  let u := ProperInnerArgs.u d
  let du := ProperInnerArgs.du d
  let j := ProperInnerArgs.j d
  let ok := ProperInnerArgs.ok d
  let v ← Memory.read (wListBase n + j)
  let dv ← Memory.read (digitBase n + j)
  if u < n ∧ v < n ∧ u < m ∧ v < m ∧ 0 < dv ∧ du = dv then
    let e ← Memory.read (3 + u * n + v)
    if e = 1 then pure (j + 1, 0) else pure (j + 1, ok)
  else
    pure (j + 1, ok)

private theorem properInnerStep_realizes :
    Realizes .exact properInnerStep
      (WordEncoding.encode (α := (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w d _ => Fits w (octWorkspace d.1.1.1.1) ∧ d.2.1 < d.1.1.1.1)
      (fun _ _ => 0) := by
  unfold properInnerStep
  realize
  all_goals
    obtain ⟨hw, hj⟩ := h
    dsimp -failIfUnchanged only [octWorkspace, wListBase, digitBase,
      ProperInnerArgs.n, ProperInnerArgs.m, ProperInnerArgs.u,
      ProperInnerArgs.du, ProperInnerArgs.j] at *
    first | omega | (apply hw.of_le; first | omega | nlinarith)

theorem clientResult_properInnerStep_fst (d : (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ))
    (s : Memory.State) :
    ((Memory.spec 0).clientResult s (properInnerStep d)).1 = ProperInnerArgs.j d + 1 := by
  unfold properInnerStep
  rw [clientResult_bind_read, clientResult_bind_read]
  split_ifs
  · rw [clientResult_bind_read]; split_ifs <;> rfl
  · rfl

/-- Number of vertices in `properOuterStep` arguments `((n, m), L), (i, ok)`. -/
abbrev ProperOuterArgs.n (d : ((ℕ × ℕ) × ℕ) × (ℕ × ℕ)) : ℕ := d.1.1.1

/-- Active vertex prefix bound in `properOuterStep` arguments. -/
abbrev ProperOuterArgs.m (d : ((ℕ × ℕ) × ℕ) × (ℕ × ℕ)) : ℕ := d.1.1.2

/-- List length `L` in `properOuterStep` arguments. -/
abbrev ProperOuterArgs.L (d : ((ℕ × ℕ) × ℕ) × (ℕ × ℕ)) : ℕ := d.1.2

/-- Outer scan index `i` in `properOuterStep` arguments. -/
abbrev ProperOuterArgs.i (d : ((ℕ × ℕ) × ℕ) × (ℕ × ℕ)) : ℕ := d.2.1

/-- Accumulated properness flag `ok` in `properOuterStep` arguments. -/
abbrev ProperOuterArgs.ok (d : ((ℕ × ℕ) × ℕ) × (ℕ × ℕ)) : ℕ := d.2.2

/-- Outer loop checking that the guessed colouring is proper on `W \ D`. -/
@[expose] def properOuterStep (d : ((ℕ × ℕ) × ℕ) × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let n := ProperOuterArgs.n d
  let m := ProperOuterArgs.m d
  let L := ProperOuterArgs.L d
  let i := ProperOuterArgs.i d
  let ok := ProperOuterArgs.ok d
  let u ← Memory.read (wListBase n + i)
  let du ← Memory.read (digitBase n + i)
  if u < n ∧ 0 < du then
    let res ← iterate properInnerStep (((n, m), u), du) L (0, ok)
    pure (i + 1, res.2)
  else
    pure (i + 1, ok)

private theorem properOuterStep_realizes :
    Realizes .exact properOuterStep
      (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w d _ => Fits w (octWorkspace d.1.1.1) ∧ d.1.2 ≤ d.1.1.1 ∧ d.2.1 < d.1.2)
      (fun _ _ => 0) := by
  unfold properOuterStep
  realize [properInnerStep_realizes]
  all_goals
    obtain ⟨hw, hL, hi⟩ := h
    dsimp -failIfUnchanged only [octWorkspace, wListBase, digitBase,
      ProperOuterArgs.n, ProperOuterArgs.m, ProperOuterArgs.L, ProperOuterArgs.i] at *
    try omega
    try (apply hw.of_le; omega)
  exact iterationSafe_idx (fun x => x.1) _ _ w _ rfl (fun _ _ hj => ⟨hw, hj.trans_le hL⟩)
    fun jok => clientResult_properInnerStep_fst (_, jok)

theorem clientResult_properOuterStep_fst (d : ((ℕ × ℕ) × ℕ) × (ℕ × ℕ))
    (s : Memory.State) :
    ((Memory.spec 0).clientResult s (properOuterStep d)).1 = ProperOuterArgs.i d + 1 := by
  unfold properOuterStep
  rw [clientResult_bind_read, clientResult_bind_read]
  split_ifs <;> simp only [clientResult_bind, clientResult_pure]

/-- Decide whether the base-3 guess is proper on `W \ D`. -/
@[expose] def checkProperProg (d : (ℕ × ℕ) × ℕ) : Memory.Prog ℕ := do
  let _ ← Memory.read 0
  let res ← iterate properOuterStep d d.2 (0, 1)
  pure res.2

private theorem checkProperProg_realizes :
    Realizes .exact checkProperProg (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (octWorkspace d.1.1) ∧ d.2 ≤ d.1.1) (fun _ _ => 0) := by
  unfold checkProperProg
  realize [properOuterStep_realizes]
  all_goals
    obtain ⟨hw, hL⟩ := h
    dsimp -failIfUnchanged only [octWorkspace] at *
    try omega
    try (apply hw.of_le; omega)
  exact iterationSafe_idx (fun x => x.1) _ _ w _ rfl (fun _ _ hi => ⟨hw, hL, hi⟩)
    fun iok => clientResult_properOuterStep_fst (d, iok)

theorem preservesAt_checkProperProg (a : ℕ) (d : (ℕ × ℕ) × ℕ) :
    PreservesAt a (checkProperProg d) := by
  unfold checkProperProg
  refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
  refine preservesAt_bind (preservesAt_iterate (fun iok => ?_) _ _) fun _ => preservesAt_pure _ _
  unfold properOuterStep
  refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
  refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
  refine preservesAt_ite _ ?_ (preservesAt_pure _ _)
  refine preservesAt_bind (preservesAt_iterate (fun jok => ?_) _ _) fun _ => preservesAt_pure _ _
  unfold properInnerStep
  refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
  refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
  refine preservesAt_ite _ ?_ (preservesAt_pure _ _)
  refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
  exact preservesAt_ite _ (preservesAt_pure _ _) (preservesAt_pure _ _)

/-- Number of vertices in `termInnerStep` arguments `((n, m), (v, cv)), j`. -/
abbrev TermInnerArgs.n (d : ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) : ℕ := d.1.1.1

/-- Active vertex prefix bound in `termInnerStep` arguments. -/
abbrev TermInnerArgs.m (d : ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) : ℕ := d.1.1.2

/-- Candidate vertex `v` in `termInnerStep` arguments. -/
abbrev TermInnerArgs.v (d : ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) : ℕ := d.1.2.1

/-- Colour `cv` of vertex `v` in `termInnerStep` arguments. -/
abbrev TermInnerArgs.cv (d : ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) : ℕ := d.1.2.2

/-- Classify vertex `v ∉ W` as a keep/flip terminal against the `j`-th entry of `W`. -/
@[expose] def termInnerStep (d : ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) : Memory.Prog ℕ := do
  let n := TermInnerArgs.n d
  let m := TermInnerArgs.m d
  let v := TermInnerArgs.v d
  let cv := TermInnerArgs.cv d
  let j := d.2
  let u ← Memory.read (wListBase n + j)
  let du ← Memory.read (digitBase n + j)
  if u < n ∧ v < n ∧ u < m ∧ v < m ∧ 0 < du then
    let e ← Memory.read (3 + u * n + v)
    if e = 1 then
      if du - 1 = cv then
        Memory.write (flipBase n + v) 1
        pure (j + 1)
      else
        Memory.write (keepBase n + v) 1
        pure (j + 1)
    else pure (j + 1)
  else pure (j + 1)

private theorem termInnerStep_realizes :
    Realizes .exact termInnerStep
      (WordEncoding.encode (α := ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (octWorkspace d.1.1.1) ∧ d.2 < d.1.1.1)
      (fun _ _ => 0) := by
  unfold termInnerStep
  realize
  all_goals
    obtain ⟨hw, hj⟩ := h
    dsimp -failIfUnchanged only [octWorkspace, wListBase, digitBase, flipBase, keepBase,
      TermInnerArgs.n, TermInnerArgs.m, TermInnerArgs.v, TermInnerArgs.cv] at *
    first | omega | (apply hw.of_le; first | omega | nlinarith)

theorem clientResult_termInnerStep (d : ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (termInnerStep d) = d.2 + 1 := by
  unfold termInnerStep
  rw [clientResult_bind_read, clientResult_bind_read]
  split_ifs <;> try rfl
  all_goals
    rw [clientResult_bind_read]
    split_ifs <;> simp only [clientResult_bind_write, clientResult_pure]

/-- Number of vertices in `termOuterStep` arguments `((n, m), L), v`. -/
abbrev TermOuterArgs.n (d : ((ℕ × ℕ) × ℕ) × ℕ) : ℕ := d.1.1.1

/-- Active vertex prefix bound in `termOuterStep` arguments. -/
abbrev TermOuterArgs.m (d : ((ℕ × ℕ) × ℕ) × ℕ) : ℕ := d.1.1.2

/-- List length `L` in `termOuterStep` arguments. -/
abbrev TermOuterArgs.L (d : ((ℕ × ℕ) × ℕ) × ℕ) : ℕ := d.1.2

/-- Outer loop populating `keepBase` and `flipBase` for every `v < m` off `W`. -/
@[expose] def termOuterStep (d : ((ℕ × ℕ) × ℕ) × ℕ) : Memory.Prog ℕ := do
  let n := TermOuterArgs.n d
  let m := TermOuterArgs.m d
  let L := TermOuterArgs.L d
  let v := d.2
  let zv ← Memory.read (wBase n + v)
  let cv ← Memory.read (colBase n + v)
  if zv = 0 ∧ v < m then
    let _ ← iterate termInnerStep ((n, m), (v, cv)) L 0
    pure (v + 1)
  else
    pure (v + 1)

private theorem termOuterStep_realizes :
    Realizes .exact termOuterStep
      (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (octWorkspace d.1.1.1) ∧ d.1.2 ≤ d.1.1.1 ∧ d.2 < d.1.1.1)
      (fun _ _ => 0) := by
  unfold termOuterStep
  realize [termInnerStep_realizes]
  all_goals
    obtain ⟨hw, hL, hv⟩ := h
    dsimp -failIfUnchanged only [octWorkspace, wBase, colBase,
      TermOuterArgs.n, TermOuterArgs.m, TermOuterArgs.L] at *
    try omega
    try (apply hw.of_le; omega)
  exact iterationSafe_idx (fun j => j) _ _ w _ rfl (fun _ _ hj => ⟨hw, hj.trans_le hL⟩)
    fun j => clientResult_termInnerStep (_, j)

theorem clientResult_termOuterStep (d : ((ℕ × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (termOuterStep d) = d.2 + 1 := by
  unfold termOuterStep
  rw [clientResult_bind_read, clientResult_bind_read]
  split_ifs <;> simp only [clientResult_bind, clientResult_pure]

/-- Mark keep and flip terminals outside `W`. -/
@[expose] def buildTerminalsProg (d : (ℕ × ℕ) × ℕ) : Memory.Prog Unit := do
  let n := GraphStepArgs.n d
  fillRange ((keepBase n, 0), n)
  fillRange ((flipBase n, 0), n)
  let _ ← iterate termOuterStep d n 0
  pure ()

private theorem buildTerminalsProg_realizes :
    Realizes .exact buildTerminalsProg (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w d _ => Fits w (octWorkspace d.1.1) ∧ d.2 ≤ d.1.1) (fun _ _ => 0) := by
  unfold buildTerminalsProg
  realize [fillRange_realizes, termOuterStep_realizes]
  all_goals
    obtain ⟨hw, hL⟩ := h
    dsimp -failIfUnchanged only [octWorkspace, keepBase, flipBase, GraphStepArgs.n] at *
    try omega
    try (apply hw.of_le; omega)
  exact iterationSafe_idx (fun v => v) _ _ w _ rfl (fun _ _ hv => ⟨hw, hL, hv⟩)
    fun v => clientResult_termOuterStep (d, v)

theorem preservesAt_buildTerminalsProg {a : ℕ} {d : (ℕ × ℕ) × ℕ}
    (ha : a < keepBase (GraphStepArgs.n d)) :
    PreservesAt a (buildTerminalsProg d) := by
  have ha_flip : a < flipBase (GraphStepArgs.n d) := by
    dsimp only [keepBase, flipBase, GraphStepArgs.n] at ha ⊢; omega
  unfold buildTerminalsProg
  refine preservesAt_bind (preservesAt_fillRange (Or.inl ha)) fun _ => ?_
  refine preservesAt_bind (preservesAt_fillRange (Or.inl ha_flip)) fun _ => ?_
  refine preservesAt_bind (preservesAt_iterate (fun v => ?_) _ _) fun _ => preservesAt_pure _ _
  unfold termOuterStep
  refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
  refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
  refine preservesAt_ite _ ?_ (preservesAt_pure _ _)
  refine preservesAt_bind (preservesAt_iterate (fun j => ?_) _ _) fun _ => preservesAt_pure _ _
  unfold termInnerStep
  refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
  refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
  refine preservesAt_ite _ ?_ (preservesAt_pure _ _)
  refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
  refine preservesAt_ite _ ?_ (preservesAt_pure _ _)
  refine preservesAt_ite _ ?_ ?_ <;>
    exact preservesAt_bind
      (preservesAt_write _
        (by dsimp only [keepBase, flipBase, TermInnerArgs.n, TermOuterArgs.n,
          GraphStepArgs.n] at ha ⊢; omega))
      fun _ => preservesAt_pure _ _

/-- Increment the deleted-vertex counter when `digitBase n + j = 0`. -/
@[expose] def countDelStep (d : ℕ × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let n := d.1
  let j := LoopAccArgs.idx d
  let cnt := LoopAccArgs.acc d
  let dj ← Memory.read (digitBase n + j)
  if dj = 0 then pure (j + 1, cnt + 1) else pure (j + 1, cnt)

private theorem countDelStep_realizes :
    Realizes .exact countDelStep (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w d _ => Fits w (octWorkspace d.1) ∧ d.2.1 < d.1 ∧ d.2.2 ≤ d.2.1)
      (fun _ _ => 0) := by
  unfold countDelStep
  realize
  all_goals
    obtain ⟨hw, hj, hc⟩ := h
    dsimp -failIfUnchanged only [octWorkspace, digitBase,
      LoopAccArgs.idx, LoopAccArgs.acc] at *
    first | omega | (apply hw.of_le; omega)

theorem clientResult_countDelStep (d : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    let res := (Memory.spec 0).clientResult s (countDelStep d)
    res.1 = LoopAccArgs.idx d + 1 ∧ res.2 ≤ LoopAccArgs.acc d + 1 := by
  unfold countDelStep
  rw [clientResult_bind_read]
  split_ifs <;> simp only [clientResult_pure] <;> exact ⟨trivial, by omega⟩

/-- Count deleted vertices (`digit = 0`) in `W`. -/
@[expose] def countDelProg (d : ℕ × ℕ) : Memory.Prog ℕ := do
  let _ ← Memory.read 0
  let res ← iterate countDelStep d.1 d.2 (0, 0)
  pure res.2

private theorem countDelProg_realizes :
    Realizes .exact countDelProg (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (octWorkspace d.1) ∧ d.2 ≤ d.1) (fun _ _ => 0) := by
  unfold countDelProg
  realize [countDelStep_realizes]
  obtain ⟨hw, hL⟩ := h
  refine iterationSafe_of_stepInv _ _ w _
    (fun rem (jc : ℕ × ℕ) _ => jc.1 + rem = d.2 ∧ jc.2 ≤ jc.1) ?_ ⟨Nat.zero_add _, le_rfl⟩
  intro rem jc t ⟨hsum, hc⟩
  dsimp only
  refine ⟨⟨hw, by omega, hc⟩, ?_⟩
  obtain ⟨h1, h2⟩ := clientResult_countDelStep (d.1, jc) t
  dsimp only [LoopAccArgs.idx, LoopAccArgs.acc] at h1 h2
  exact ⟨by omega, by omega⟩

theorem preservesAt_countDelProg (a : ℕ) (d : ℕ × ℕ) :
    PreservesAt a (countDelProg d) := by
  unfold countDelProg
  refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
  refine preservesAt_bind (preservesAt_iterate (fun jc => ?_) _ _) fun _ => preservesAt_pure _ _
  unfold countDelStep
  refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
  exact preservesAt_ite _ (preservesAt_pure _ _) (preservesAt_pure _ _)

/-- Single-vertex commit updating `sepBase` and `colBase`. -/
@[expose] def commitStep (d : ℕ × ℕ) : Memory.Prog ℕ := do
  let n := d.1
  let v := d.2
  let wv ← Memory.read (wBase n + v)
  let gv ← Memory.read (guessBase n + v)
  let xv ← Memory.read (sepOutBase n + v)
  let cv ← Memory.read (colBase n + v)
  let dout ← Memory.read (distBase n + (v + n + 2))
  if (wv = 1 ∧ gv = 0) ∨ xv = 1 then
    Memory.write (sepBase n + v) 1
  else
    Memory.write (sepBase n + v) 0
  if wv = 1 then
    if gv = 2 then Memory.write (colBase n + v) 1 else Memory.write (colBase n + v) 0
  else
    if dout < splitCount n then
      if cv = 1 then Memory.write (colBase n + v) 1 else Memory.write (colBase n + v) 0
    else
      if cv = 1 then Memory.write (colBase n + v) 0 else Memory.write (colBase n + v) 1
  pure (v + 1)

private theorem commitStep_realizes :
    Realizes .exact commitStep (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (octWorkspace d.1) ∧ d.2 < d.1) (fun _ _ => 0) := by
  unfold commitStep
  realize
  all_goals
    obtain ⟨hw, hv⟩ := h
    dsimp -failIfUnchanged only [octWorkspace, wBase, guessBase, sepOutBase, parBase, distBase,
      flowBase, colBase, sepBase, splitCount] at *
    have hsq := splitCount_sq d.1
    first | omega | (apply hw.of_le; omega)

theorem clientResult_commitStep (d : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (commitStep d) = d.2 + 1 := by
  unfold commitStep
  rw [clientResult_bind_read, clientResult_bind_read, clientResult_bind_read,
    clientResult_bind_read, clientResult_bind_read]
  dsimp only
  split_ifs <;> simp only [clientResult_bind_write, clientResult_pure]

/-- Commit the accepted transversal `D ∪ X` and flipped colouring into `sepBase`/`colBase`. -/
@[expose] def commitLeafProg (n : ℕ) : Memory.Prog Unit := do
  let _ ← Memory.read 0
  let _ ← iterate commitStep n n 0
  pure ()

private theorem commitLeafProg_realizes :
    Realizes .exact commitLeafProg (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w n _ => Fits w (octWorkspace n)) (fun _ _ => 0) := by
  unfold commitLeafProg
  realize [commitStep_realizes]
  exact iterationSafe_idx (fun v => v) _ _ w _ rfl (fun _ _ hv => ⟨h, hv⟩)
    fun v => clientResult_commitStep (d, v)

theorem preservesAt_commitLeafProg {a n : ℕ}
    (ha : a < sepBase n ∨ wBase n ≤ a) :
    PreservesAt a (commitLeafProg n) := by
  unfold commitLeafProg
  refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
  refine preservesAt_bind (preservesAt_iterate_nat fun v hv => ⟨fun s => ?_, fun s => ?_⟩)
    fun _ => preservesAt_pure _ _
  · unfold commitStep
    have hsep : a ≠ sepBase n + v := by dsimp only [sepBase, wBase] at ha ⊢; omega
    have hcol : a ≠ colBase n + v := by dsimp only [sepBase, colBase, wBase] at ha ⊢; omega
    rw [clientState_bind_read, clientState_bind_read, clientState_bind_read,
      clientState_bind_read, clientState_bind_read]
    dsimp only
    split_ifs <;>
      (rw [clientState_bind_write, clientState_bind_write, clientState_pure]
       dsimp only
       rw [Function.update_of_ne hcol, Function.update_of_ne hsep])
  · exact clientResult_commitStep (n, v) s

/-- Number of vertices in compression leaf configuration `(((n, k), m), L)`. -/
abbrev CompressCfg.n (d : ((ℕ × ℕ) × ℕ) × ℕ) : ℕ := d.1.1.1

/-- Deletion budget `k` in compression leaf configuration. -/
abbrev CompressCfg.k (d : ((ℕ × ℕ) × ℕ) × ℕ) : ℕ := d.1.1.2

/-- Active vertex prefix bound `m` in compression leaf configuration. -/
abbrev CompressCfg.m (d : ((ℕ × ℕ) × ℕ) × ℕ) : ℕ := d.1.2

/-- Evaluate one base-3 guess `D, σ` on `W` via `minSepProg`, committing on success. -/
@[expose] def leafProg (d : ((ℕ × ℕ) × ℕ) × ℕ) : Memory.Prog ℕ := do
  let n := CompressCfg.n d
  let k := CompressCfg.k d
  let m := CompressCfg.m d
  let L := d.2
  unpackGuessProg (n, L)
  let ok ← checkProperProg ((n, m), L)
  if ok = 1 then
    buildTerminalsProg ((n, m), L)
    let sepCnt ← minSepProg (n, m)
    let delCnt ← countDelProg (n, L)
    if sepCnt ≤ n ∧ delCnt ≤ n ∧ delCnt + sepCnt ≤ k then
      commitLeafProg n
      pure 1
    else
      pure 0
  else
    pure 0

private theorem leafProg_realizes :
    Realizes .exact leafProg (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (octWorkspace d.1.1.1) ∧ d.2 ≤ d.1.1.1)
      (fun _ _ => 0) := by
  unfold leafProg
  realize [unpackGuessProg_realizes, checkProperProg_realizes, buildTerminalsProg_realizes,
    minSepProg_realizes, countDelProg_realizes, commitLeafProg_realizes]
  all_goals
    obtain ⟨hw, hL⟩ := h
    dsimp -failIfUnchanged only [octWorkspace, CompressCfg.n, CompressCfg.k, CompressCfg.m] at *
    first | exact hw | omega | (apply hw.of_le; omega)

theorem preservesAt_leafProg {a : ℕ} {d : ((ℕ × ℕ) × ℕ) × ℕ}
    (ha : a < sepBase (CompressCfg.n d) ∨
      (wBase (CompressCfg.n d) ≤ a ∧ a < guessBase (CompressCfg.n d))) :
    PreservesAt a (leafProg d) := by
  have hg : a < guessBase (CompressCfg.n d) := by
    dsimp only [sepBase, wBase, guessBase, CompressCfg.n] at ha ⊢; omega
  have hk : a < keepBase (CompressCfg.n d) := by
    dsimp only [guessBase, keepBase, CompressCfg.n] at hg ⊢; omega
  have hf : a < flowBase (CompressCfg.n d) := by
    dsimp only [keepBase, flowBase, CompressCfg.n] at hk ⊢; omega
  have hc : a < sepBase (CompressCfg.n d) ∨ wBase (CompressCfg.n d) ≤ a := ha.imp id And.left
  unfold leafProg
  refine preservesAt_bind (preservesAt_unpackGuessProg hg) fun _ => ?_
  refine preservesAt_bind (preservesAt_checkProperProg a _) fun _ => ?_
  refine preservesAt_ite _ ?_ (preservesAt_pure _ _)
  refine preservesAt_bind (preservesAt_buildTerminalsProg hk) fun _ => ?_
  refine preservesAt_bind (preservesAt_minSepProg hf) fun _ => ?_
  refine preservesAt_bind (preservesAt_countDelProg a _) fun _ => ?_
  refine preservesAt_ite _ ?_ (preservesAt_pure _ _)
  exact preservesAt_bind (preservesAt_commitLeafProg hc) fun _ => preservesAt_pure _ _

/-- Single-digit carry propagation step of the base-3 odometer. -/
@[expose] def incOdomStep (d : ℕ × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let n := d.1
  let j := LoopAccArgs.idx d
  let carry := LoopAccArgs.acc d
  let dj ← Memory.read (digitBase n + j)
  if carry = 1 then
    if dj < 2 then
      Memory.write (digitBase n + j) (dj + 1)
      pure (j + 1, 0)
    else
      Memory.write (digitBase n + j) 0
      pure (j + 1, 1)
  else
    pure (j + 1, 0)

private theorem incOdomStep_realizes :
    Realizes .exact incOdomStep (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w d _ => Fits w (octWorkspace d.1) ∧ d.2.1 < d.1)
      (fun _ _ => 0) := by
  unfold incOdomStep
  realize
  all_goals
    obtain ⟨hw, hj⟩ := h
    dsimp -failIfUnchanged only [octWorkspace, digitBase,
      LoopAccArgs.idx, LoopAccArgs.acc] at *
    first | omega | (apply hw.of_le; omega)

theorem clientResult_incOdomStep_fst (d : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    ((Memory.spec 0).clientResult s (incOdomStep d)).1 = LoopAccArgs.idx d + 1 := by
  unfold incOdomStep
  rw [clientResult_bind_read]
  split_ifs <;> simp only [clientResult_bind_write, clientResult_pure]

/-- Increment the `L`-digit base-3 odometer in `digitBase`, returning final carry (`0`/`1`). -/
@[expose] def incOdomProg (d : ℕ × ℕ) : Memory.Prog ℕ := do
  let _ ← Memory.read 0
  let res ← iterate incOdomStep d.1 d.2 (0, 1)
  pure res.2

private theorem incOdomProg_realizes :
    Realizes .exact incOdomProg (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (octWorkspace d.1) ∧ d.2 ≤ d.1) (fun _ _ => 0) := by
  unfold incOdomProg
  realize [incOdomStep_realizes]
  all_goals
    obtain ⟨hw, hL⟩ := h
    dsimp -failIfUnchanged only [octWorkspace] at *
    try omega
    try (apply hw.of_le; omega)
  exact iterationSafe_idx (fun x => x.1) _ _ w _ rfl (fun _ _ hj => ⟨hw, hj.trans_le hL⟩)
    fun jc => clientResult_incOdomStep_fst (d.1, jc)

/-- Number of vertices in `guessStep` arguments `((((n, k), m), L), (done, found))`. -/
abbrev GuessStepArgs.n (d : (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) : ℕ := d.1.1.1.1

/-- List length `L` in `guessStep` arguments. -/
abbrev GuessStepArgs.L (d : (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) : ℕ := d.1.2

/-- Current found flag `found` in `guessStep` arguments. -/
abbrev GuessStepArgs.found (d : (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) : ℕ := d.2.2

/-- One odometer iteration of `compressProg`: evaluate `leafProg` and advance `digitBase`. -/
@[expose] def guessStep (d : (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let _ ← Memory.read 0
  let found' ← if GuessStepArgs.found d = 0 then leafProg d.1 else pure (GuessStepArgs.found d)
  let done' ← incOdomProg (GuessStepArgs.n d, GuessStepArgs.L d)
  pure (done', found')

private theorem guessStep_realizes :
    Realizes .exact guessStep
      (WordEncoding.encode (α := (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w d _ => Fits w (octWorkspace d.1.1.1.1) ∧ d.1.2 ≤ d.1.1.1.1)
      (fun _ _ => 0) := by
  unfold guessStep
  realize [leafProg_realizes, incOdomProg_realizes]
  all_goals
    obtain ⟨hw, hL⟩ := h
    dsimp -failIfUnchanged only [GuessStepArgs.n, GuessStepArgs.L] at *
    first | exact hw | exact hL

/-- Clamped base-3 evaluation of `L` digits starting at `base` in `mem`. -/
@[expose] def base3At (mem : ℕ → ℕ) (base : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => base3At mem base j + min (mem (base + j)) 2 * 3 ^ j

theorem base3At_lt (mem : ℕ → ℕ) (base : ℕ) :
    ∀ L, base3At mem base L < 3 ^ L
  | 0 => by simp [base3At]
  | j + 1 => by
    have ih := base3At_lt mem base j
    have hmin : min (mem (base + j)) 2 ≤ 2 := Nat.min_le_right _ _
    have hmul : min (mem (base + j)) 2 * 3 ^ j ≤ 2 * 3 ^ j := Nat.mul_le_mul_right _ hmin
    simp only [base3At, pow_succ]
    omega

theorem base3At_congr {m₁ m₂ : ℕ → ℕ} {base : ℕ} :
    ∀ {L}, (∀ i < L, m₁ (base + i) = m₂ (base + i)) → base3At m₁ base L = base3At m₂ base L
  | 0, _ => rfl
  | j + 1, h => by
    unfold base3At
    rw [base3At_congr fun i hi => h i (by omega), h j (by omega)]

theorem incOdomProg_base3At (n L : ℕ) (s : Memory.State) :
    let done' := (Memory.spec 0).clientResult s (incOdomProg (n, L))
    let s' := (Memory.spec 0).clientState s (incOdomProg (n, L))
    done' ≤ 1 ∧
      base3At s'.mem (digitBase n) L + done' * 3 ^ L = base3At s.mem (digitBase n) L + 1 := by
  unfold incOdomProg
  simp only [client_simps]
  have hinv := iterate_invariant_of incOdomStep n
    (fun rem (jc : ℕ × ℕ) t =>
      jc.1 + rem = L ∧ jc.2 ≤ 1 ∧
        (∀ i, jc.1 ≤ i → t.mem (digitBase n + i) = s.mem (digitBase n + i)) ∧
        base3At t.mem (digitBase n) jc.1 + jc.2 * 3 ^ jc.1 =
          base3At s.mem (digitBase n) jc.1 + 1)
    (fun rem jc t ⟨hsum, hcarry, habove, hval⟩ => by
      dsimp only [incOdomStep, LoopAccArgs.idx, LoopAccArgs.acc]
      have hdj : t.mem (digitBase n + jc.1) = s.mem (digitBase n + jc.1) := habove jc.1 le_rfl
      by_cases hc : jc.2 = 1
      · by_cases hlt : t.mem (digitBase n + jc.1) < 2
        · rw [clientResult_bind_read, clientState_bind_read, ite_eq_left hc, ite_eq_left hlt,
            clientResult_bind_write, clientState_bind_write, clientResult_pure, clientState_pure]
          dsimp only
          have hpre : base3At (Function.update t.mem (digitBase n + jc.1)
              (t.mem (digitBase n + jc.1) + 1)) (digitBase n) jc.1 =
              base3At t.mem (digitBase n) jc.1 :=
            base3At_congr fun i hi => Function.update_of_ne (by omega) _ _
          refine ⟨by omega, by omega,
            fun i hi => (Function.update_of_ne (by omega) _ _).trans (habove i (by omega)), ?_⟩
          simp only [base3At, hpre, Function.update_self, zero_mul, add_zero]
          rw [hc, one_mul] at hval
          have hmin1 : min (t.mem (digitBase n + jc.1) + 1) 2 = t.mem (digitBase n + jc.1) + 1 :=
            Nat.min_eq_left (by omega)
          have hmin0 : min (s.mem (digitBase n + jc.1)) 2 = t.mem (digitBase n + jc.1) := by
            rw [← hdj]; exact Nat.min_eq_left (by omega)
          rw [hmin1, hmin0, add_mul, one_mul]
          omega
        · rw [clientResult_bind_read, clientState_bind_read, ite_eq_left hc, ite_eq_right hlt,
            clientResult_bind_write, clientState_bind_write, clientResult_pure, clientState_pure]
          dsimp only
          have hpre : base3At (Function.update t.mem (digitBase n + jc.1) 0)
              (digitBase n) jc.1 = base3At t.mem (digitBase n) jc.1 :=
            base3At_congr fun i hi => Function.update_of_ne (by omega) _ _
          refine ⟨by omega, by omega,
            fun i hi => (Function.update_of_ne (by omega) _ _).trans (habove i (by omega)), ?_⟩
          simp only [base3At, hpre, Function.update_self, Nat.zero_min, zero_mul, add_zero,
            one_mul, pow_succ]
          rw [hc, one_mul] at hval
          have hmin0 : min (s.mem (digitBase n + jc.1)) 2 = 2 := by
            rw [← hdj]; exact Nat.min_eq_right (by omega)
          rw [hmin0]
          omega
      · have hc0 : jc.2 = 0 := by omega
        rw [clientResult_bind_read, clientState_bind_read, ite_eq_right hc,
          clientResult_pure, clientState_pure]
        dsimp only
        refine ⟨by omega, by omega, fun i hi => habove i (by omega), ?_⟩
        simp only [base3At, hdj, zero_mul, add_zero]
        rw [hc0, zero_mul, add_zero] at hval
        omega)
    (n := L) (a := (0, 1)) (s := s) ⟨Nat.zero_add _, le_rfl, fun _ _ => rfl, by simp [base3At]⟩
  obtain ⟨hL0, hcarry, _, hval⟩ := hinv
  have hfst : ((Memory.spec 0).clientResult s (iterate incOdomStep n L (0, 1))).1 = L := by omega
  rw [hfst] at hval
  exact ⟨hcarry, hval⟩

/-- Enumerate up to `3 ^ L` guesses on `W` via a base-3 odometer. -/
@[expose] def compressProg (d : ((ℕ × ℕ) × ℕ) × ℕ) : Memory.Prog ℕ := do
  let n := CompressCfg.n d
  let L := d.2
  fillRange ((digitBase n, 0), L)
  let res ← boundedWhile (fun _ (st : ℕ × ℕ) => st.1 = 0) guessStep d (3 ^ L) (0, 0)
  pure res.2

private theorem compressProg_realizes :
    Realizes .exact compressProg (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (octWorkspace d.1.1.1) ∧ d.2 ≤ d.1.1.1)
      (fun _ _ => 0) := by
  unfold compressProg
  realize [fillRange_realizes, guessStep_realizes]
  all_goals
    obtain ⟨hw, hL⟩ := h
    dsimp -failIfUnchanged only [octWorkspace, digitBase, CompressCfg.n] at *
    try omega
    try (apply hw.of_le; omega)
  intro hv
  refine whileSafe_of_measure _ _ _ w _ (fun (_ : ℕ × ℕ) _ => True)
    (fun (st : ℕ × ℕ) t => if st.1 = 0 then 3 ^ d.2 - base3At t.mem (digitBase d.1.1.1) d.2 else 0)
    ?_ ?_ trivial ?_ hv
  · intro st t _ hzero hg
    have hlt := base3At_lt t.mem (digitBase d.1.1.1) d.2
    simp only [hg, ↓reduceIte] at hzero
    omega
  · intro st t _ hg _
    refine ⟨⟨hw, hL⟩, trivial, ?_⟩
    have hlt := base3At_lt t.mem (digitBase d.1.1.1) d.2
    let t₁ := if st.2 = 0 then (Memory.spec 0).clientState t (leafProg d) else t
    have hstep : ((Memory.spec 0).clientResult t (guessStep (d, st))).1 =
          (Memory.spec 0).clientResult t₁ (incOdomProg (d.1.1.1, d.2)) ∧
        (Memory.spec 0).clientState t (guessStep (d, st)) =
          (Memory.spec 0).clientState t₁ (incOdomProg (d.1.1.1, d.2)) := by
      unfold guessStep
      dsimp only [GuessStepArgs.n, GuessStepArgs.L, GuessStepArgs.found, t₁]
      by_cases h0 : st.2 = 0
      · rw [clientResult_bind_read, clientState_bind_read, ite_eq_left h0, ite_eq_left h0,
          clientResult_bind, clientState_bind, clientResult_bind, clientResult_pure,
          clientState_bind, clientState_pure]
        exact ⟨rfl, rfl⟩
      · rw [clientResult_bind_read, clientState_bind_read, ite_eq_right h0, ite_eq_right h0,
          clientResult_bind, clientState_bind, clientState_pure, clientResult_bind,
          clientResult_pure, clientState_bind, clientState_pure]
        exact ⟨rfl, rfl⟩
    have hpres :
        base3At t₁.mem (digitBase d.1.1.1) d.2 = base3At t.mem (digitBase d.1.1.1) d.2 := by
      dsimp only [t₁]
      split_ifs
      · refine base3At_congr fun i hi => preservesAt_leafProg (Or.inr ⟨?_, ?_⟩) t
        · dsimp only [wBase, digitBase, CompressCfg.n]; omega
        · dsimp only [digitBase, guessBase, CompressCfg.n]; omega
      · rfl
    simp only [hstep.1, hstep.2, hg, ↓reduceIte]
    obtain ⟨hdone_le, hodom_eq⟩ := incOdomProg_base3At d.1.1.1 d.2 t₁
    rw [hpres] at hodom_eq
    split_ifs with hdone0
    · rw [hdone0, zero_mul, add_zero] at hodom_eq; omega
    · omega
  · simp only [↓reduceIte]
    exact Nat.sub_le _ _

/-- Number of vertices in `octStep` arguments `(n, k), (m, alive)`. -/
abbrev OctStepArgs.n (d : (ℕ × ℕ) × (ℕ × ℕ)) : ℕ := d.1.1

/-- Deletion budget `k` in `octStep` arguments. -/
abbrev OctStepArgs.k (d : (ℕ × ℕ) × (ℕ × ℕ)) : ℕ := d.1.2

/-- Active vertex index `m` in `octStep` arguments. -/
abbrev OctStepArgs.m (d : (ℕ × ℕ) × (ℕ × ℕ)) : ℕ := d.2.1

/-- Liveness flag `alive` in `octStep` arguments. -/
abbrev OctStepArgs.alive (d : (ℕ × ℕ) × (ℕ × ℕ)) : ℕ := d.2.2

/-- One iterative-compression step incorporating vertex `m` into the candidate set. -/
@[expose] def octStep (d : (ℕ × ℕ) × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let n := OctStepArgs.n d
  let k := OctStepArgs.k d
  let m := OctStepArgs.m d
  let alive := OctStepArgs.alive d
  let _ ← Memory.read 0
  if alive = 1 then
    let L ← buildWProg (n, m)
    if L ≤ k then
      Memory.write (sepBase n + m) 1
      pure (m + 1, 1)
    else if L ≤ n then
      let ok ← compressProg (((n, k), m + 1), L)
      pure (m + 1, ok)
    else
      pure (m + 1, 0)
  else
    pure (m + 1, 0)

private theorem octStep_realizes :
    Realizes .exact octStep (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w d _ => Fits w (octWorkspace d.1.1) ∧ d.2.1 < d.1.1)
      (fun _ _ => 0) := by
  unfold octStep
  realize [buildWProg_realizes, compressProg_realizes]
  all_goals
    obtain ⟨hw, hm⟩ := h
    dsimp -failIfUnchanged only [octWorkspace, sepBase,
      OctStepArgs.n, OctStepArgs.k, OctStepArgs.m, OctStepArgs.alive] at *
    first | exact hw | omega | (apply hw.of_le; omega)

theorem clientResult_octStep_fst (d : (ℕ × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    ((Memory.spec 0).clientResult s (octStep d)).1 = OctStepArgs.m d + 1 := by
  unfold octStep
  rw [clientResult_bind_read]
  split_ifs <;> try rfl
  rw [clientResult_bind]
  split_ifs <;> simp only [clientResult_bind, clientResult_pure]

/-- Top-level exact-basis Word-RAM iterative-compression odd-cycle-transversal program. -/
@[expose] def octProg (_ : Unit) : Memory.Prog ℕ := do
  let n ← Memory.read 1
  let k ← Memory.read 2
  let _ ← Memory.alloc (octScratch n)
  fillRange ((sepBase n, 0), n)
  fillRange ((colBase n, 0), n)
  let res ← iterate octStep (n, k) n (0, 1)
  pure res.2

/-- Exact-basis Word-RAM realization certificate for `octProg`. -/
theorem octProg_realizes :
    Realizes .exact octProg (WordEncoding.encode (α := Unit))
      (WordEncoding.encode (α := ℕ))
      (fun w _ s => s.frontier = 3 + s.mem 1 * s.mem 1 ∧ Fits w (octWorkspace (s.mem 1)))
      (fun _ _ => 0) := by
  unfold octProg
  realize [fillRange_realizes, octStep_realizes]
  all_goals
    obtain ⟨hfr, hw⟩ := h
    dsimp -failIfUnchanged only [octWorkspace, octScratch, sepBase, colBase, splitCount] at *
    have hsq := splitCount_sq (s.mem 1)
    try omega
    try (apply hw.of_le; omega)
  exact iterationSafe_idx (fun x => x.1) _ _ w _ rfl (fun _ _ hm => ⟨hw, hm⟩)
    fun ma => clientResult_octStep_fst (_, ma)

end Cslib.Algorithms.WordRAM.OddCycleTransversal
