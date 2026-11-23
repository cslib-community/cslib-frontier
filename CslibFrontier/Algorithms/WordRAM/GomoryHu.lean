/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.GomoryHu.Gusfield
public import CslibFrontier.Algorithms.WordRAM.EdmondsKarp
public import CslibFrontier.Algorithms.WordRAM.Karger.Contract
public import CslibFrontier.Computability.WordRAM.Time
import CslibFrontier.Computability.WordRAM.Realization.Program.Standard
import CslibFrontier.Tactic.Realize
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Gomory–Hu trees on the Word-RAM

TODO docstring.
-/

public section

namespace Cslib.Algorithms.WordRAM.GomoryHu

open Cslib.Algorithms.Lean.GomoryHu Cslib.WeightedCut SimpleGraph
open Cslib.Algorithms.WordRAM.EdmondsKarp Cslib.Algorithms.WordRAM.Karger
open Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization

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
private abbrev ghCtx (n B : ℕ) : Ctx := (n, 3, scrBase n, B)

private theorem input_add_ghScratch (n : ℕ) : 3 + n * n + ghScratch n = ghWorkspace n := by
  unfold ghWorkspace ghScratch ekScratch
  ring

/-! ### Client reduction helpers -/

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

-- TEMP: to be replaced by the public lemmas of `EdmondsKarp.lean` (maxflow-ek, board #72).
private theorem fillRange_realizes :
    Realizes .exact fillRange (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w d _ => Fits w (d.1.1 + d.2)) (fun _ _ => 0) := by
  sorry

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
  · exact ⟨by dsimp only; omega, hw.of_le (by dsimp only [ekScratch]; omega), hB⟩
  · refine iterationSafe_of_stepInv _ _ w _
      (fun rem (z : ℕ) _ => z + rem = d.1.1) ?_ (Nat.zero_add _)
    intro rem z t hsum
    dsimp only at hsum ⊢
    refine ⟨⟨hw, hs, by omega⟩, ?_⟩
    dsimp -failIfUnchanged only [rehangStep]
    simp_client <;> omega

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
    dsimp -failIfUnchanged only [maxStep]
    simp_client <;> omega
  · have hclr : ∀ i < d.1 * d.1,
        clear s.mem s.frontier (ghScratch d.1) (3 + i) ≤ B := fun i hi => by
      rw [clear_of_not_owns fun h => absurd h.1 (by show ¬s.frontier ≤ 3 + i; omega)]
      exact hB i hi
    have hM := (maxScan_spec (st := ⟨clear s.mem s.frontier (ghScratch d.1),
      s.frontier + ghScratch d.1⟩) hclr).1
    refine iterationSafe_of_stepInv _ _ w _
      (fun rem (z : ℕ) _ => z + rem = d.1) ?_ (Nat.zero_add _)
    intro rem z t hsum
    dsimp only at hsum ⊢
    refine ⟨⟨hw, hwB.of_le (by unfold ekBound; gcongr), by omega⟩, ?_⟩
    dsimp -failIfUnchanged only [ghStep]
    simp_client <;> omega

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

end Cslib.Algorithms.WordRAM.GomoryHu
