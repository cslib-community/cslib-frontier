/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (regression tests for `ProgFrame`, `ValidProg`, and `realize` upgrades)

public import CslibFrontier.Computability.WordRAM.Realization.ProgFrame
public import CslibFrontier.Computability.WordRAM.Realization.Structure
public import CslibFrontier.DataStructure.Memory.Record
public import CslibFrontier.Tactic.Realize
public import CslibFrontier.Tactic.ValidProg

/-!
# Regression tests for `ProgFrame`, `ValidProg`, and `realize` call/structure/link automation

Covers:
1. Structural admissibility discharge via `valid_prog` over `Memory.Prog` (`pure`, `bind`,
   `Memory.read`, `Memory.write`, `ite`, `iterate`, `boundedWhile`, and `MonotoneMemInv`).
2. Monadic cost calculation/bounds via `prog_cost` (including nested conditionals).
3. Coordinate-only staging and thin-wrapper unfolding in `realize`.
4. Structure-aware `callArgument` and projection reduction for `@[word_enc_structure]` types.
5. Direct `realize` lowering of `DataStructure.link` over `Record.Prog` without `conv` preambles,
   plus `Fin k → ℕ` vector call matching.
-/

public section

namespace CslibFrontierTests.WordRAMValidProg

open Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization

@[expose] def twoCellSafe (w base : ℕ) (s : Memory.State) : Prop :=
  Memory.WellFormed w s ∧ base + 2 ≤ s.frontier

instance (w base : ℕ) : MonotoneMemInv w (twoCellSafe w base) :=
  ⟨fun h hv => ⟨wellFormed_clientState h.1 hv,
    h.2.trans (Memory.frontier_le_clientState (w := 0) _ _)⟩⟩

theorem valid_prog_straightLine (w base : ℕ) (s : Memory.State)
    (_hwf : Memory.WellFormed w s) (hfr : base + 2 ≤ s.frontier) (v : ℕ) (hv : Fits w v) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (do
      let x ← Memory.read base
      Memory.write (base + 1) v
      if x = 0 then Memory.write base v else pure ())) := by
  have hb0 : base < s.frontier := by omega
  have hb1 : base + 1 < s.frontier := by omega
  valid_prog

theorem valid_prog_iterate (w base n : ℕ) (s : Memory.State) (hsafe : twoCellSafe w base s)
    (v : ℕ) (hv : Fits w v) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (iterate (fun (d : ℕ × ℕ) => do
        let x ← Memory.read d.1
        Memory.write (d.1 + 1) v
        pure (x + d.2)) base n 0)) := by
  valid_prog
  · have := ‹twoCellSafe w base _›.2; omega
  · have := ‹twoCellSafe w base _›.2; omega

theorem valid_prog_boundedWhile (w base n : ℕ) (s : Memory.State) (hsafe : twoCellSafe w base s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (boundedWhile (fun _ (k : ℕ) => 0 < k)
        (fun (d : ℕ × ℕ) => do
          let x ← Memory.read d.1
          if x = 0 then pure 0 else pure (d.2 - 1)) base n n)) := by
  valid_prog
  have := ‹twoCellSafe w base _›.2; omega

theorem prog_cost_nested (base v : ℕ) (s : Memory.State) :
    memoryCost (do
      let x ← Memory.read base
      if x = 0 then pure 0
      else do
        let y ← Memory.read (base + 1)
        if y = 0 then do
          Memory.write (base + 2) v
          pure 1
        else pure 2) s ≤ 3 := by
  prog_cost

@[expose] def wideCallee (d : (ℕ × ℕ) × (ℕ × ℕ)) : Memory.Prog ℕ := do
  let x ← Memory.read (d.1.1 + d.2.1)
  pure (x + d.1.2 + d.2.2)

private theorem realizes_wideCallee :
    Realizes .exact wideCallee WordEncoding.encode WordEncoding.encode
      (fun w d s => Fits w (d.1.1 + d.2.1) ∧ Fits w (s.mem (d.1.1 + d.2.1) + d.1.2 + d.2.2))
      (fun _ _ => 0) := by
  realize
  · exact h.1
  · exact h.2

/-- Thin wrapper tail-calling a multi-word certificate with one computed leaf: `realize` unfolds
the wrapper and stages only the missing coordinate without `Realizes.congr`. -/
@[expose] def wideWrapper (d : (ℕ × ℕ) × (ℕ × ℕ)) : Memory.Prog ℕ :=
  wideCallee (d.1, (d.2.1 + 1, d.2.2))

theorem realizes_wideWrapper :
    Realizes .exact wideWrapper WordEncoding.encode WordEncoding.encode
      (fun w d s => Fits w (d.2.1 + 1) ∧ Fits w (d.1.1 + (d.2.1 + 1)) ∧
        Fits w (s.mem (d.1.1 + (d.2.1 + 1)) + d.1.2 + d.2.2))
      (fun _ _ => 0) := by
  realize [realizes_wideCallee]
  · exact h.1
  · exact h.2.1
  · exact h.2.2

/-- Structure-aware `callArgument` and projection reduction on `word_enc_structure`. -/
structure SpanArgs where
  base : ℕ
  idx : ℕ
  delta : ℕ

word_enc_structure spanArgsWords : SpanArgs where
  base : wordWords,
  idx : wordWords,
  delta : wordWords

@[expose] def spanAdd (a : SpanArgs) : Memory.Prog ℕ := do
  let v ← Memory.read (a.base + a.idx)
  pure (v + a.delta)

private theorem realizes_spanAdd :
    Realizes .exact spanAdd spanArgsWords WordEncoding.encode
      (fun w a s => Fits w (a.base + a.idx) ∧ Fits w (s.mem (a.base + a.idx) + a.delta))
      (fun _ _ => 0) := by
  realize
  · exact h.1
  · exact h.2

@[expose] def spanCaller (a : SpanArgs) : Memory.Prog ℕ :=
  spanAdd ⟨a.base, a.idx + 1, a.delta⟩

theorem realizes_spanCaller :
    Realizes .exact spanCaller spanArgsWords WordEncoding.encode
      (fun w a s => Fits w (a.idx + 1) ∧ Fits w (a.base + (a.idx + 1)) ∧
        Fits w (s.mem (a.base + (a.idx + 1)) + a.delta))
      (fun _ _ => 0) := by
  realize [realizes_spanAdd]
  · exact h.1
  · exact h.2.1
  · exact h.2.2

/-- Direct `DataStructure.link` compilation and `Fin k → ℕ` vector call matching in `realize`. -/
inductive PairCell where
  | fst
  | snd
  deriving DecidableEq

def pairLayout (base : ℕ) : Record.Layout (fun (_ : PairCell) => True) where
  addr
    | .fst => base
    | .snd => base + 1
  addr_injOn i j _ _ h := by cases i <;> cases j <;> simp at h <;> rfl

def swapIfZero (v : ℕ) : Record.Prog PairCell ℕ := do
  let x ← Record.read .fst
  if x = 0 then
    Record.write .snd v
    pure v
  else
    pure x

theorem realizes_swapIfZero :
    Realizes .exact
      (fun d : Fin 2 → ℕ => link (E := Memory.spec 0)
        ((pairLayout (d 0)).methods 0) (swapIfZero (d 1)))
      (.refl _) WordEncoding.encode
      (fun w d _ => Fits w (d 0 + 1)) (fun _ _ => 0) := by
  realize
  exact h

theorem realizes_swapCaller :
    Realizes .exact
      (fun d : ℕ × ℕ => do
        let y ← link (E := Memory.spec 0)
          ((pairLayout d.1).methods 0) (swapIfZero (d.2 + 1))
        pure y)
      WordEncoding.encode WordEncoding.encode
      (fun w d _ => Fits w (d.1 + 1) ∧ Fits w (d.2 + 1)) (fun _ _ => 0) := by
  realize [realizes_swapIfZero]
  · exact h.2
  · exact h.1

end CslibFrontierTests.WordRAMValidProg
