/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.OddCycleTransversal.Layout
public import CslibFrontier.Computability.WordRAM.Realization.ProgFrame
public import CslibFrontier.Computability.WordRAM.Realization.WhileAbsorb
import CslibFrontier.Tactic.Realize
import Mathlib.Tactic.Linarith

/-!
# Range fill/copy routines, memory-readiness framing, and adjacency-matrix predicate

This module certifies the low-level `fillRange` and `copyRange` `Memory.Prog` routines along with
their frame, admissibility (`MemReady`), cost, and functional specs, plus the `MatrixLoaded`
predicate linking `encodeInput G k` to linear memory.

## Main definitions

* `Cslib.Algorithms.WordRAM.OddCycleTransversal.fillRange`,
  `Cslib.Algorithms.WordRAM.OddCycleTransversal.copyRange`: contiguous slice fill and copy.
* `Cslib.Algorithms.WordRAM.OddCycleTransversal.MemReady`: well-formed memory frontier invariant.
* `Cslib.Algorithms.WordRAM.OddCycleTransversal.MatrixLoaded`: adjacency-matrix memory invariant.

## Main results

* `Cslib.Algorithms.WordRAM.OddCycleTransversal.fillRange_realizes`,
  `Cslib.Algorithms.WordRAM.OddCycleTransversal.copyRange_realizes`: exact-basis realization.
* `Cslib.Algorithms.WordRAM.OddCycleTransversal.fillRange_spec`,
  `Cslib.Algorithms.WordRAM.OddCycleTransversal.copyRange_spec`: functional specifications.
* `Cslib.Algorithms.WordRAM.OddCycleTransversal.matrixLoaded_init`: initial-memory invariant.
-/

public section

namespace Cslib.Algorithms.WordRAM.OddCycleTransversal

open SimpleGraph
open Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization
open StateTransitionSpec (clientResult_bind clientState_bind clientResult_pure clientState_pure)

/-! ### Client reduction and frame helpers for `Memory.Prog` -/

attribute [local client_simps] runClient_read runClient_write clientState_map

/-- Graph dimension `n` encoded in a `((n, m), k)` step-argument tuple. -/
abbrev GraphStepArgs.n (d : (ℕ × ℕ) × ℕ) : ℕ := d.1.1

/-- Subgraph prefix size `m` encoded in a `((n, m), k)` step-argument tuple. -/
abbrev GraphStepArgs.m (d : (ℕ × ℕ) × ℕ) : ℕ := d.1.2

/-- Current loop index encoded in a `(n, (idx, acc))` step-argument tuple. -/
abbrev LoopAccArgs.idx (d : ℕ × (ℕ × ℕ)) : ℕ := d.2.1

/-- Current accumulator or carry encoded in a `(n, (idx, acc))` step-argument tuple. -/
abbrev LoopAccArgs.acc (d : ℕ × (ℕ × ℕ)) : ℕ := d.2.2

/-- Frame lemma along an indexed iteration preserving the first state coordinate. -/
theorem preservesAt_iterate_fst {a : ℕ} {δ β : Type}
    {body : δ × (ℕ × β) → Memory.Prog (ℕ × β)} {d : δ}
    {m : ℕ} (b₀ : β) (hstep : ∀ i < m, ∀ b, PreservesAt a (body (d, (i, b))) ∧
      ∀ s, ((Memory.spec 0).clientResult s (body (d, (i, b)))).1 = i + 1) :
    PreservesAt a (iterate body d m (0, b₀)) := fun s =>
  (iterate_invariant_of body d (fun rem (ib : ℕ × β) t => ib.1 + rem = m ∧ t.mem a = s.mem a)
    (fun rem ib t ⟨hsum, hmem⟩ => by
      obtain ⟨hp, hr⟩ := hstep ib.1 (by omega) ib.2
      exact ⟨by rw [hr]; omega, (hp t).trans hmem⟩)
    ⟨Nat.zero_add _, rfl⟩).2

/-! ### Array fill and copy helpers -/

/-- Single step of `fillRange`: write `val` to `base + i` and increment `i`. -/
private def fillStep : (ℕ × ℕ) × ℕ → Memory.Prog ℕ
  | ((base, val), idx) => do
    Memory.write (base + idx) val
    pure (idx + 1)

/-- Fill `len` contiguous memory cells starting at `base` with `val`
for `d = ((base, val), len)`. -/
@[expose] def fillRange (d : (ℕ × ℕ) × ℕ) : Memory.Prog Unit := do
  let _ ← iterate (fun ((base, val), idx) => do
    Memory.write (base + idx) val
    pure (idx + 1)) d.1 d.2 0
  pure ()

private theorem fillStep_realizes :
    Realizes .exact fillStep (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (d.1.1 + d.2) ∧ Fits w (d.2 + 1)) (fun _ _ => 0) := by
  unfold fillStep
  realize
  · exact h.1
  · exact h.2

/-- Exact-basis realization certificate for `fillRange`. -/
theorem fillRange_realizes :
    Realizes .exact fillRange (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w d _ => let ((base, _), len) := d; Fits w (base + len)) (fun _ _ => 0) := by
  change Realizes .exact (fun d : (ℕ × ℕ) × ℕ => do let _ ← iterate fillStep d.1 d.2 0; pure ())
    _ _ _ _
  realize [fillStep_realizes]
  refine iterationSafe_of_stepInv _ _ w d
    (fun rem (idx : ℕ) _ => idx + rem = d.2 ∧ Fits w (d.1.1 + d.2)) ?_ ⟨Nat.zero_add _, h⟩
  intro rem idx t ⟨hsum, hfit⟩
  dsimp only [fillStep]
  simp only [client_simps]
  exact ⟨⟨by apply hfit.of_le; omega, by apply hfit.of_le; omega⟩, by omega, hfit⟩

/-- `fillRange` preserves addresses outside `[base, base + len)`. -/
theorem preservesAt_fillRange {a : ℕ} {d : (ℕ × ℕ) × ℕ}
    (hout : let ((base, _), len) := d; a < base ∨ base + len ≤ a) :
    PreservesAt a (fillRange d) := fun s => by
  rcases d with ⟨⟨base, val⟩, len⟩
  unfold fillRange
  rw [StateTransitionSpec.clientState_bind]
  change ((Memory.spec 0).clientState s (iterate fillStep (base, val) len 0)).mem a = s.mem a
  refine iterate_invariant_of fillStep (base, val)
    (fun rem (idx : ℕ) t => idx + rem = len ∧ t.mem a = s.mem a)
    (fun rem idx t ⟨hsum, hmem⟩ => ?_) ⟨Nat.zero_add _, rfl⟩ |>.2
  unfold fillStep
  simp only [client_simps]
  exact ⟨by omega, (Function.update_of_ne (by omega) _ t.mem).trans hmem⟩

/-- Single step of `copyRange`: copy `src + i` to `dst + i` and increment `i`. -/
private def copyStep : (ℕ × ℕ) × ℕ → Memory.Prog ℕ
  | ((src, dst), idx) => do
    let v ← Memory.read (src + idx)
    Memory.write (dst + idx) v
    pure (idx + 1)

/-- Copy `len` contiguous words from `src` to `dst` for `d = ((src, dst), len)`. -/
@[expose] def copyRange (d : (ℕ × ℕ) × ℕ) : Memory.Prog Unit := do
  let _ ← iterate (fun ((src, dst), idx) => do
    let v ← Memory.read (src + idx)
    Memory.write (dst + idx) v
    pure (idx + 1)) d.1 d.2 0
  pure ()

private theorem copyStep_realizes :
    Realizes .exact copyStep (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (d.1.1 + d.2) ∧ Fits w (d.1.2 + d.2) ∧ Fits w (d.2 + 1))
      (fun _ _ => 0) := by
  unfold copyStep
  realize
  · exact h.1
  · exact h.2.1
  · exact h.2.2

/-- Exact-basis realization certificate for `copyRange`. -/
theorem copyRange_realizes :
    Realizes .exact copyRange (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w d _ => let ((src, dst), len) := d; Fits w (src + len) ∧ Fits w (dst + len))
      (fun _ _ => 0) := by
  change Realizes .exact (fun d : (ℕ × ℕ) × ℕ => do let _ ← iterate copyStep d.1 d.2 0; pure ())
    _ _ _ _
  realize [copyStep_realizes]
  refine iterationSafe_of_stepInv _ _ w d
    (fun rem (idx : ℕ) _ => idx + rem = d.2 ∧ Fits w (d.1.1 + d.2) ∧ Fits w (d.1.2 + d.2))
    ?_ ⟨Nat.zero_add _, h.1, h.2⟩
  intro rem idx t ⟨hsum, hf1, hf2⟩
  dsimp only [copyStep]
  simp only [client_simps]
  exact ⟨⟨by apply hf1.of_le; omega, by apply hf2.of_le; omega, by apply hf1.of_le; omega⟩,
    by omega, hf1, hf2⟩

/-! ### Admissibility (`ValidHistory`) and `memoryCost` bounds -/

/-- Well-formed memory state with allocated workspace `octWorkspace n`. -/
abbrev MemReady (w n : ℕ) (s : Memory.State) : Prop :=
  Memory.WellFormed w s ∧ octWorkspace n ≤ s.frontier

theorem validHistory_bind_ready {α β : Type} {w n : ℕ} {s : Memory.State}
    (hs : MemReady w n s) {p : Memory.Prog α} {q : α → Memory.Prog β}
    (hp : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p))
    (hq : ∀ x t, MemReady w n t →
      (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t (q x))) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p >>= q)) :=
  validHistory_bind_step hp (hq _ _ (MonotoneMemInv.pres hs hp))

theorem memReady_write {w n : ℕ} {s : Memory.State} (hs : MemReady w n s) (a v : ℕ)
    (hv : Fits w v) : MemReady w n ⟨Function.update s.mem a v, s.frontier⟩ := by
  refine ⟨⟨hs.1.frontier_fits, fun b => ?_⟩, hs.2⟩
  dsimp only
  by_cases hb : b = a
  · subst hb; simpa using hv
  · rw [Function.update_of_ne hb]; exact hs.1.mem_fits b

theorem memoryCost_boundedWhile_le_of {δ σ : Type}
    (guard : δ → σ → Prop) [∀ d a, Decidable (guard d a)]
    (body : δ × σ → Memory.Prog σ) (c : ℕ) (d : δ)
    (hstep : ∀ a s, guard d a → memoryCost (body (d, a)) s ≤ c)
    (m : ℕ) (a : σ) (s : Memory.State) :
    memoryCost (boundedWhile guard body d m a) s ≤ c * m := by
  induction m generalizing a s with
  | zero => simp [boundedWhile]
  | succ m ih =>
    unfold boundedWhile
    by_cases hg : guard d a
    · rw [ite_eq_left hg, memoryCost_bind']
      have h1 := hstep a s hg
      have h2 := ih ((Memory.spec 0).clientResult s (body (d, a)))
        ((Memory.spec 0).clientState s (body (d, a)))
      rw [Nat.mul_succ]
      omega
    · rw [ite_eq_right hg]
      simp

theorem validHistory_fillRange {w n : ℕ} {d : (ℕ × ℕ) × ℕ} {s : Memory.State}
    (hs : MemReady w n s) (hend : let ((base, _), len) := d; base + len ≤ octWorkspace n)
    (hval : let ((_, val), _) := d; Fits w val) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (fillRange d)) := by
  rcases d with ⟨⟨base, val⟩, len⟩
  change (Memory.spec w).ValidHistory s
    ((Memory.spec w).clientHistory s (do let _ ← iterate fillStep (base, val) len 0; pure ()))
  refine validHistory_bind_step
    (validHistory_iterate_nat (Inv := MemReady w n) len 0 (fun idx hidx t ht => ⟨?_, ?_⟩) hs)
    (validHistory_pure _ _ _)
  · unfold fillStep
    dsimp only at hend ⊢
    exact validHistory_write_bind (by have := ht.2; omega) hval (validHistory_pure _ _ _)
  · unfold fillStep; simp only [client_simps]

theorem validHistory_copyRange {w n : ℕ} {d : (ℕ × ℕ) × ℕ} {s : Memory.State}
    (hs : MemReady w n s) (hsrc : let ((src, _), len) := d; src + len ≤ octWorkspace n)
    (hdst : let ((_, dst), len) := d; dst + len ≤ octWorkspace n) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (copyRange d)) := by
  rcases d with ⟨⟨srcB, dstB⟩, len⟩
  change (Memory.spec w).ValidHistory s
    ((Memory.spec w).clientHistory s (do let _ ← iterate copyStep (srcB, dstB) len 0; pure ()))
  refine validHistory_bind_step
    (validHistory_iterate_nat (Inv := MemReady w n) len 0 (fun idx hidx t ht => ⟨?_, ?_⟩) hs)
    (validHistory_pure _ _ _)
  · unfold copyStep
    dsimp only at hsrc hdst ⊢
    exact validHistory_read_bind (by have := ht.2; omega)
      (validHistory_write_bind (by have := ht.2; omega) (ht.1.mem_fits _)
        (validHistory_pure _ _ _))
  · unfold copyStep; simp only [client_simps]

theorem memoryCost_fillRange_le (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (fillRange d) s ≤ d.2 := by
  change memoryCost (do let _ ← iterate fillStep d.1 d.2 0; pure ()) s ≤ d.2
  have hit := memoryCost_iterate_le_of fillStep 1 d.1
    (fun idx t => by unfold fillStep; exact (le_refl 1)) d.2 0 s
  exact le_trans (memoryCost_bind_le hit fun _ t => (memoryCost_pure () t).le) (by omega)

theorem memoryCost_copyRange_le (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (copyRange d) s ≤ 2 * d.2 := by
  change memoryCost (do let _ ← iterate copyStep d.1 d.2 0; pure ()) s ≤ 2 * d.2
  have hit := memoryCost_iterate_le_of copyStep 2 d.1
    (fun idx t => by
      unfold copyStep
      exact memoryCost_bind_le (memoryCost_read _ t).le fun _ t' =>
        (le_refl 1 : memoryCost _ t' ≤ 1)) d.2 0 s
  exact le_trans (memoryCost_bind_le hit fun _ t => (memoryCost_pure () t).le) (by omega)

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
      rw [clientResult_bind_write, clientState_bind_write, clientResult_pure, clientState_pure]
      dsimp only
      refine ⟨by omega, fun i hi => ?_⟩
      by_cases h : i = idx
      · subst h; simp
      · rw [Function.update_of_ne (by omega)]; exact hprev i (by omega))
    (n := len) (a := 0) (s := s) ⟨Nat.zero_add _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  intro i hi
  exact hinv.2 i (by omega)

theorem preservesAt_copyRange {a : ℕ} {d : (ℕ × ℕ) × ℕ}
    (hout : let ((_, dst), len) := d; a < dst ∨ dst + len ≤ a) :
    PreservesAt a (copyRange d) := fun s => by
  rcases d with ⟨⟨src, dst⟩, len⟩
  unfold copyRange
  rw [StateTransitionSpec.clientState_bind]
  change ((Memory.spec 0).clientState s (iterate copyStep (src, dst) len 0)).mem a = s.mem a
  refine (iterate_invariant_of copyStep (src, dst)
    (fun rem (idx : ℕ) t => idx + rem = len ∧ t.mem a = s.mem a)
    (fun rem idx t ⟨hsum, hmem⟩ => ?_) ⟨Nat.zero_add _, rfl⟩).2
  unfold copyStep
  simp only [client_simps]
  exact ⟨by omega, (Function.update_of_ne (by omega) _ t.mem).trans hmem⟩

theorem copyRange_spec {srcB dstB len : ℕ} (hdisj : srcB + len ≤ dstB) (s : Memory.State) :
    let s' := (Memory.spec 0).clientState s (copyRange ((srcB, dstB), len))
    (∀ i < len, s'.mem (dstB + i) = s.mem (srcB + i)) ∧
      (∀ a, (a < dstB ∨ dstB + len ≤ a) → s'.mem a = s.mem a) := by
  intro s'
  refine ⟨?_, fun a ha => preservesAt_copyRange ha s⟩
  unfold s' copyRange
  rw [StateTransitionSpec.clientState_bind]
  change ∀ i < len, ((Memory.spec 0).clientState s (iterate copyStep (srcB, dstB) len 0)).mem
    (dstB + i) = s.mem (srcB + i)
  have hinv := iterate_invariant_of copyStep (srcB, dstB)
    (fun rem (idx : ℕ) t => idx + rem = len ∧
      (∀ i < len, t.mem (srcB + i) = s.mem (srcB + i)) ∧
      (∀ i < idx, t.mem (dstB + i) = s.mem (srcB + i)))
    (fun rem idx t ⟨hsum, hsrc, hdst⟩ => by
      unfold copyStep
      rw [clientResult_bind_read, clientState_bind_read, clientResult_bind_write,
        clientState_bind_write, clientResult_pure, clientState_pure]
      dsimp only
      refine ⟨by omega, fun i hi => ?_, fun i hi => ?_⟩
      · rw [Function.update_of_ne (by omega)]
        exact hsrc i hi
      · by_cases h : i = idx
        · subst h
          simpa using hsrc i (by omega)
        · rw [Function.update_of_ne (by omega)]
          exact hdst i (by omega))
    (n := len) (a := 0) (s := s)
    ⟨Nat.zero_add _, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  intro i hi
  exact hinv.2.2 i (by omega)

/-- Invariant asserting that row-major adjacency matrix of `G` resides at memory offset `3`. -/
@[expose] def MatrixLoaded {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Memory.State) : Prop :=
  ∀ u v : Fin n, s.mem (3 + u.1 * n + v.1) = if G.Adj u v then 1 else 0

theorem matrixLoaded_init {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) :
    MatrixLoaded G (Memory.State.init (encodeInput G k)) := by
  intro u v
  have hne : 3 + u.1 * n + v.1 ≠ 0 := by omega
  have hsub : 3 + u.1 * n + v.1 - 1 = (u.1 * n + v.1) + 2 := by omega
  have hlt : u.1 * n + v.1 < (encodeAdjMatrix G).length := by
    rw [length_encodeAdjMatrix]
    nlinarith [u.2, v.2]
  change (if 3 + u.1 * n + v.1 = 0 then (encodeInput G k).length
    else (encodeInput G k).getD (3 + u.1 * n + v.1 - 1) 0) = _
  rw [ite_eq_right hne, hsub]
  change (encodeAdjMatrix G).getD (u.1 * n + v.1) 0 = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some,
    getElem_encodeAdjMatrix]

end Cslib.Algorithms.WordRAM.OddCycleTransversal
