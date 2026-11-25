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
# Core layout and `fillRange` primitive for dense Edmonds–Karp

Shared memory layout (`Ctx`, `distAddr`, `ekScratch`, `ekBound`, `CtxFits`) and the relocatable
memory-fill primitive (`fillRange`, `fillRange_realizes`, `fillRange_spec`,
`memoryCost_fillRange_le`, `validHistory_fillRange`) used across
`CslibFrontier.Algorithms.WordRAM.EdmondsKarp`.

## Main definitions

* `Cslib.Algorithms.WordRAM.EdmondsKarp.Ctx`, `Ctx.equiv`, `distAddr`, `ekScratch`, `ekBound`,
  `CtxFits`: solver context, layout bounds, and word-width predicate.
* `Cslib.Algorithms.WordRAM.EdmondsKarp.fillRange`: fill a memory range with a constant word.

## Main results

* `Cslib.Algorithms.WordRAM.EdmondsKarp.fillRange_realizes`: compilation to `Basis.exact`.
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

/-! ### `fillRange` primitive -/

/-- One step of `fillRange`: write `val` at `base + idx`. -/
private def fillStep (d : (ℕ × ℕ) × ℕ) : Memory.Prog ℕ := do
  Memory.write (d.1.1 + d.2) d.1.2
  pure (d.2 + 1)

/-- Write `val` at the `len` addresses from `base` (`d = ((base, val), len)`). -/
def fillRange (d : (ℕ × ℕ) × ℕ) : Memory.Prog Unit := do
  let _ ← iterate fillStep d.1 d.2 0
  pure ()

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

theorem memoryCost_fillRange_le (base val len : ℕ) (s : Memory.State) :
    memoryCost (fillRange ((base, val), len)) s ≤ len := by
  unfold fillRange
  have hit := memoryCost_iterate_le_of fillStep 1 (base, val)
    (fun idx t => by unfold fillStep; exact le_refl 1) len 0 s
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
    exact validHistory_write_bind (by have := ht.2; dsimp only; omega) hval
      (validHistory_pure _ _ _)
  · unfold fillStep; simp only [client_simps]

end Cslib.Algorithms.WordRAM.EdmondsKarp
