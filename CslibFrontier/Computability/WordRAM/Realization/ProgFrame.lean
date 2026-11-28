/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Realization.While
public import CslibFrontier.Computability.WordRAM.Realization.LoopCongr
public import CslibFrontier.DataStructure.Memory.Frame
public import CslibFrontier.DataStructure.StateTransition.ClientMap

/-!
# Admissibility and loop-invariant combinators for `Memory.Prog`

This module provides width-independent reasoning principles for `Memory.Prog` clients over
`Memory.spec`:

1. **Primitive `clientState`, `clientResult`, and `memoryCost` equations**: closed-form reductions
   for `Memory.read`, `Memory.write`, `Memory.alloc`, `Memory.allocDirty`, and conditional
   branches (`memoryCost_ite`).
2. **Monotone state invariants and `ValidHistory` rules**: `MonotoneMemInv` (synthesized for
   `Memory.WellFormed`, frontier lower bounds `F ≤ s.frontier` and `F < s.frontier`, and
   conjunctions), `wellFormed_clientState`, and structural `ValidHistory` decomposition rules.
3. **Loop-invariant and `memoryCost` combinators**: step-invariant transport across `iterate` and
   `boundedWhile`, read-only loop state preservation, and constant per-step `memoryCost` bounds.

## Main definitions

* `MonotoneMemInv`: memory-state invariant preserved by any admissible `Memory.Prog` step.
* `PreservesAt`: a program leaves one memory address unchanged.

## Main results

* `clientState_read`, `clientResult_read`, `clientState_write`, `clientResult_write`,
  `clientState_allocDirty`, `clientResult_allocDirty`,
  `runClient_allocDirty`, `runClient_ite`, `prog_clientState_ite`, `prog_clientResult_ite`,
  `state_frontier_ite`, `state_mem_ite`, `memoryCost_read`, `memoryCost_write`,
  `memoryCost_alloc`, `memoryCost_allocDirty`, `memoryCost_ite`: primitive state, result, and cost
  equations.
* `wellFormed_clientState`, `validHistory_pure`, `validHistory_read`, `validHistory_write`,
  `validHistory_alloc`, `validHistory_allocDirty`, `validHistory_allocDirty_bind`,
  `validHistory_bind_step`, `validHistory_read_bind`, `validHistory_write_bind`,
  `validHistory_ite`, `validHistory_dite`, `validHistory_iterate_inv`,
  `validHistory_boundedWhile_inv`: monadic admissibility combinators.
* `boundedWhile_invariant_of`, `iterate_invariant_of`, `iterationSafe_of_stepInv`,
  `clientState_iterate_eq_of`, `clientState_boundedWhile_eq_of`, `memoryCost_iterate_le_of`,
  `memoryCost_iterate_le_potential`: generic loop invariant and cost lemmas, including an amortized
  bound with a potential.
* `clientResult_bind_read`, `clientState_bind_write`, `runClient_read`, `runClient_write`,
  `memoryCost_bind_le`,
  `memoryCost_read_bind_le`, `memoryCost_write_bind_le`, `memoryCost_ite_le`,
  `validHistory_iterate_nat`, `validHistory_iterate_fst`: reductions through primitive steps and
  cost and admissibility combinators for counting loops.
* `PreservesAt`, `preservesAt_bind`, `preservesAt_iterate`, `preservesAt_iterate_nat`:
  single-address frames.
-/

public section

namespace Cslib.WordRAM.Realization

open Cslib.DataStructure

/-! ## Primitive client state, result, and cost equations -/

theorem clientState_read (w : ℕ) (s : Memory.State) (a : ℕ) :
    (Memory.spec w).clientState s (Memory.read a) = s := rfl

@[simp, client_simps] theorem clientResult_read (w : ℕ) (s : Memory.State) (a : ℕ) :
    (Memory.spec w).clientResult s (Memory.read a) = s.mem a := Eq.trans rfl rfl

theorem clientState_write (w : ℕ) (s : Memory.State) (a v : ℕ) :
    (Memory.spec w).clientState s (Memory.write a v) =
      ⟨Function.update s.mem a v, s.frontier⟩ :=
  Eq.trans rfl rfl

@[simp, client_simps] theorem clientResult_write (w : ℕ) (s : Memory.State) (a v : ℕ) :
    (Memory.spec w).clientResult s (Memory.write a v) = () :=
  Eq.trans rfl rfl

theorem clientState_allocDirty (w : ℕ) (s : Memory.State) (k : ℕ) :
    (Memory.spec w).clientState s (Memory.allocDirty k) = ⟨s.mem, s.frontier + k⟩ :=
  Eq.trans rfl rfl

@[simp, client_simps] theorem clientResult_allocDirty (w : ℕ) (s : Memory.State) (k : ℕ) :
    (Memory.spec w).clientResult s (Memory.allocDirty k) = s.frontier :=
  Eq.trans rfl rfl

/-- Running `Memory.allocDirty` advances the frontier by `k` and returns the old frontier. -/
theorem runClient_allocDirty (w : ℕ) (s : (Memory.spec w).State) (k : ℕ) :
    (Memory.spec w).runClient s (Memory.allocDirty k) =
      (s.frontier, ⟨s.mem, s.frontier + k⟩, [Memory.Op.allocDirty k]) :=
  rfl

theorem runClient_ite {α : Type} (w : ℕ) (c : Prop) [Decidable c]
    (p₁ p₂ : Memory.Prog α) (s : Memory.State) :
    (Memory.spec w).runClient s (if c then p₁ else p₂ : Memory.Prog α) =
      if c then (Memory.spec w).runClient s p₁ else (Memory.spec w).runClient s p₂ := by
  split_ifs <;> rfl

theorem prog_clientState_ite {α : Type} (w : ℕ)
    (c : Prop) [Decidable c] (p₁ p₂ : Memory.Prog α) (s : Memory.State) :
    (Memory.spec w).clientState s (if c then p₁ else p₂ : Memory.Prog α) =
      if c then (Memory.spec w).clientState s p₁ else (Memory.spec w).clientState s p₂ := by
  split_ifs <;> rfl

@[simp, client_simps] theorem prog_clientResult_ite {α : Type} (w : ℕ)
    (c : Prop) [Decidable c] (p₁ p₂ : Memory.Prog α) (s : Memory.State) :
    (Memory.spec w).clientResult s (if c then p₁ else p₂ : Memory.Prog α) =
      if c then (Memory.spec w).clientResult s p₁ else (Memory.spec w).clientResult s p₂ := by
  split_ifs <;> rfl

@[simp, client_simps] theorem state_frontier_ite
    (c : Prop) [Decidable c] (s₁ s₂ : Memory.State) :
    (if c then s₁ else s₂).frontier = if c then s₁.frontier else s₂.frontier := by
  split_ifs <;> rfl

@[simp, client_simps] theorem state_mem_ite
    (c : Prop) [Decidable c] (s₁ s₂ : Memory.State) (x : ℕ) :
    (if c then s₁ else s₂).mem x = if c then s₁.mem x else s₂.mem x := by
  split_ifs <;> rfl

/-- Split `ValidHistory` across `Memory.allocDirty k >>= q` directly in closed form. -/
theorem validHistory_allocDirty_bind {α : Type} {w : ℕ} {s : Memory.State} {k : ℕ}
    {q : ℕ → Memory.Prog α} (hk : Fits w (s.frontier + k))
    (hq : (Memory.spec w).ValidHistory ⟨s.mem, s.frontier + k⟩
      ((Memory.spec w).clientHistory ⟨s.mem, s.frontier + k⟩ (q s.frontier))) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (Memory.allocDirty k >>= q)) :=
  ⟨hk, hq⟩

@[simp, client_simps] theorem memoryCost_read (a : ℕ) (s : Memory.State) :
    memoryCost (Memory.read a) s = 1 := rfl

@[simp, client_simps] theorem memoryCost_write (a v : ℕ) (s : Memory.State) :
    memoryCost (Memory.write a v) s = 1 := rfl

@[simp, client_simps] theorem memoryCost_alloc (k : ℕ) (s : Memory.State) :
    memoryCost (Memory.alloc k) s = k + 1 := rfl

@[simp, client_simps] theorem memoryCost_allocDirty (k : ℕ) (s : Memory.State) :
    memoryCost (Memory.allocDirty k) s = 1 := rfl

/-- Push `memoryCost` inside a conditional `Memory.Prog` branch. -/
theorem memoryCost_ite {α : Type} (c : Prop) [Decidable c] (p₁ p₂ : Memory.Prog α)
    (s : Memory.State) :
    memoryCost (if c then p₁ else p₂) s = if c then memoryCost p₁ s else memoryCost p₂ s :=
  apply_ite (fun p => memoryCost p s) c p₁ p₂

/-! ## Monotone memory invariants and `ValidHistory` combinators -/

/-- Admissible `Memory.Prog` execution preserves `Memory.WellFormed w`. -/
theorem wellFormed_clientState {α : Type} {w : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) {p : Memory.Prog α}
    (hv : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p)) :
    Memory.WellFormed w ((Memory.spec 0).clientState s p) := by
  rw [← clientState_width w p s]
  have h := hwf.run hv
  rwa [StateTransitionSpec.run_runClient] at h

/-- A predicate on `Memory.State` preserved across every admissible `Memory.Prog` step at width
`w`. Synthesized automatically for `Memory.WellFormed w`, frontier lower bounds `F ≤ s.frontier`
and `F < s.frontier`, and conjunctions. -/
class MonotoneMemInv (w : ℕ) (Inv : Memory.State → Prop) : Prop where
  /-- Any valid execution from a state satisfying `Inv` ends in a state satisfying `Inv`. -/
  pres : ∀ {α : Type} {s : Memory.State} {p : Memory.Prog α},
    Inv s → (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p) →
    Inv ((Memory.spec 0).clientState s p)

instance instMonotoneMemInv_true (w : ℕ) : MonotoneMemInv w (fun _ => True) :=
  ⟨fun _ _ => trivial⟩

instance instMonotoneMemInv_wellFormed (w : ℕ) : MonotoneMemInv w (Memory.WellFormed w) :=
  ⟨fun hs hv => wellFormed_clientState hs hv⟩

instance instMonotoneMemInv_le_frontier (w F : ℕ) :
    MonotoneMemInv w (fun s => F ≤ s.frontier) :=
  ⟨fun hs _ => hs.trans (Memory.frontier_le_clientState (w := 0) _ _)⟩

instance instMonotoneMemInv_lt_frontier (w F : ℕ) :
    MonotoneMemInv w (fun s => F < s.frontier) :=
  ⟨fun hs _ => lt_of_lt_of_le hs (Memory.frontier_le_clientState (w := 0) _ _)⟩

instance instMonotoneMemInv_and (w : ℕ) (P Q : Memory.State → Prop)
    [MonotoneMemInv w P] [MonotoneMemInv w Q] :
    MonotoneMemInv w (fun s => P s ∧ Q s) :=
  ⟨fun ⟨hp, hq⟩ hv => ⟨MonotoneMemInv.pres hp hv, MonotoneMemInv.pres hq hv⟩⟩

/-- Admissibility of `pure a` is trivial. -/
theorem validHistory_pure {α : Type} (w : ℕ) (s : Memory.State) (a : α) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (Pure.pure a)) :=
  trivial

/-- Admissibility of a single `Memory.read a`. -/
theorem validHistory_read {w : ℕ} {s : Memory.State} {a : ℕ} (ha : a < s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (Memory.read a)) :=
  ⟨ha, trivial⟩

/-- Admissibility of a single `Memory.write a v`. -/
theorem validHistory_write {w : ℕ} {s : Memory.State} {a v : ℕ}
    (ha : a < s.frontier) (hv : Fits w v) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (Memory.write a v)) :=
  ⟨⟨ha, hv⟩, trivial⟩

/-- Admissibility of a single `Memory.alloc k`. -/
theorem validHistory_alloc {w : ℕ} {s : Memory.State} {k : ℕ} (hk : Fits w (s.frontier + k)) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (Memory.alloc k)) :=
  ⟨hk, trivial⟩

/-- Admissibility of a single `Memory.allocDirty k`. -/
theorem validHistory_allocDirty {w : ℕ} {s : Memory.State} {k : ℕ} (hk : Fits w (s.frontier + k)) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (Memory.allocDirty k)) :=
  ⟨hk, trivial⟩

/-- Split `ValidHistory` across `p >>= q` at width-0 intermediate state and result. -/
theorem validHistory_bind_step {α β : Type} {w : ℕ} {s : Memory.State}
    {p : Memory.Prog α} {q : α → Memory.Prog β}
    (hp : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p))
    (hq : (Memory.spec w).ValidHistory ((Memory.spec 0).clientState s p)
      ((Memory.spec w).clientHistory ((Memory.spec 0).clientState s p)
        (q ((Memory.spec 0).clientResult s p)))) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p >>= q)) :=
  (validHistory_bind' w p q s).mpr ⟨hp, hq⟩

private theorem validHistory_bind_inv {α β : Type} {w : ℕ} {Inv : Memory.State → Prop}
    [MonotoneMemInv w Inv] {s : Memory.State} (hinv : Inv s)
    {p : Memory.Prog α} {q : α → Memory.Prog β}
    (hp : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p))
    (hq : Inv ((Memory.spec 0).clientState s p) →
      (Memory.spec w).ValidHistory ((Memory.spec 0).clientState s p)
        ((Memory.spec w).clientHistory ((Memory.spec 0).clientState s p)
          (q ((Memory.spec 0).clientResult s p)))) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p >>= q)) :=
  validHistory_bind_step hp (hq (MonotoneMemInv.pres hinv hp))

/-- Split `ValidHistory` across `Memory.read a >>= q` directly in closed form. -/
theorem validHistory_read_bind {α : Type} {w : ℕ} {s : Memory.State} {a : ℕ}
    {q : ℕ → Memory.Prog α} (ha : a < s.frontier)
    (hq : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (q (s.mem a)))) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (Memory.read a >>= q)) :=
  ⟨ha, hq⟩

/-- Split `ValidHistory` across `Memory.write a v >>= q` directly in closed form. -/
theorem validHistory_write_bind {α : Type} {w : ℕ} {s : Memory.State} {a v : ℕ}
    {q : Unit → Memory.Prog α} (ha : a < s.frontier) (hv : Fits w v)
    (hq : (Memory.spec w).ValidHistory ⟨Function.update s.mem a v, s.frontier⟩
      ((Memory.spec w).clientHistory ⟨Function.update s.mem a v, s.frontier⟩ (q ()))) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (Memory.write a v >>= q)) :=
  ⟨⟨ha, hv⟩, hq⟩

/-- Split `ValidHistory` across `if c then p₁ else p₂`. -/
theorem validHistory_ite {α : Type} {w : ℕ} {s : Memory.State} {c : Prop} [Decidable c]
    {p₁ p₂ : Memory.Prog α}
    (h₁ : c → (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p₁))
    (h₂ : ¬c → (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p₂)) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (if c then p₁ else p₂)) := by
  split_ifs with h
  · exact h₁ h
  · exact h₂ h

/-- Split `ValidHistory` across dependent `if h : c then p₁ h else p₂ h`. -/
theorem validHistory_dite {α : Type} {w : ℕ} {s : Memory.State} {c : Prop} [Decidable c]
    {p₁ : c → Memory.Prog α} {p₂ : ¬c → Memory.Prog α}
    (h₁ : ∀ h : c, (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p₁ h)))
    (h₂ : ∀ h : ¬c, (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p₂ h))) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (if h : c then p₁ h else p₂ h)) := by
  split_ifs with h
  · exact h₁ h
  · exact h₂ h

/-- `ValidHistory` of `iterate` given a `MonotoneMemInv` body certificate. -/
theorem validHistory_iterate_inv {δ σ : Type} {w : ℕ} (Inv : Memory.State → Prop)
    [MonotoneMemInv w Inv] (body : δ × σ → Memory.Prog σ) (d : δ)
    (hstep : ∀ a t, Inv t →
      (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t (body (d, a))))
    (n : ℕ) (a : σ) {s : Memory.State} (hinv : Inv s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (iterate body d n a)) := by
  induction n generalizing a s with
  | zero => exact validHistory_pure w s a
  | succ n ih =>
    exact validHistory_bind_inv hinv (hstep a s hinv) fun hinv' => ih _ hinv'

/-- `ValidHistory` of `boundedWhile` given a `MonotoneMemInv` body certificate. -/
theorem validHistory_boundedWhile_inv {δ σ : Type} {w : ℕ} (Inv : Memory.State → Prop)
    [MonotoneMemInv w Inv]
    (guard : δ → σ → Prop) [∀ d a, Decidable (guard d a)]
    (body : δ × σ → Memory.Prog σ) (d : δ)
    (hstep : ∀ a t, Inv t → guard d a →
      (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t (body (d, a))))
    (n : ℕ) (a : σ) {s : Memory.State} (hinv : Inv s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (boundedWhile guard body d n a)) := by
  induction n generalizing a s with
  | zero => exact validHistory_pure w s a
  | succ n ih =>
    unfold boundedWhile
    exact validHistory_ite
      (fun hg => validHistory_bind_inv hinv (hstep a s hinv hg) fun hinv' => ih _ hinv')
      (fun _ => validHistory_pure w s a)

/-! ## Generic loop-invariant, read-only, and cost lemmas -/

/-- An invariant `I a s` preserved by each guarded step of `boundedWhile` holds on exit. -/
theorem boundedWhile_invariant_of {δ σ : Type}
    (guard : δ → σ → Prop) [∀ d a, Decidable (guard d a)]
    (body : δ × σ → Memory.Prog σ) (d : δ)
    (I : σ → Memory.State → Prop)
    (hstep : ∀ a s, I a s → guard d a →
      I ((Memory.spec 0).clientResult s (body (d, a)))
        ((Memory.spec 0).clientState s (body (d, a))))
    (n : ℕ) (a : σ) (s : Memory.State) (hi : I a s) :
    I ((Memory.spec 0).clientResult s (boundedWhile guard body d n a))
      ((Memory.spec 0).clientState s (boundedWhile guard body d n a)) := by
  induction n generalizing a s with
  | zero => exact hi
  | succ n ih =>
    unfold boundedWhile
    by_cases hg : guard d a
    · rw [ite_eq_left hg, StateTransitionSpec.clientResult_bind,
        StateTransitionSpec.clientState_bind]
      exact ih _ _ (hstep a s hi hg)
    · simp only [hg, ↓reduceIte]
      exact hi

/-- A step-indexed invariant `I j a s` preserved by `body` establishes `iterationSafe`. -/
theorem iterationSafe_of_stepInv {δ σ : Type}
    (body : δ × σ → Memory.Prog σ) (safe : ℕ → δ × σ → Memory.State → Prop)
    (w : ℕ) (d : δ) (I : ℕ → σ → Memory.State → Prop)
    (hstep : ∀ j a s, I (j + 1) a s →
      safe w (d, a) s ∧
        I j ((Memory.spec 0).clientResult s (body (d, a)))
          ((Memory.spec 0).clientState s (body (d, a))))
    {n : ℕ} {a : σ} {s : Memory.State} (hi : I n a s) :
    iterationSafe body safe w d n a s := by
  induction n generalizing a s with
  | zero => trivial
  | succ n ih =>
    obtain ⟨hs, hi'⟩ := hstep n a s hi
    exact ⟨hs, ih hi'⟩

/-- A step-indexed invariant `I j a s` preserved by `body` reaches `I 0` after `n` steps of
`iterate`. -/
theorem iterate_invariant_of {δ σ : Type}
    (body : δ × σ → Memory.Prog σ) (d : δ)
    (I : ℕ → σ → Memory.State → Prop)
    (hstep : ∀ j a s, I (j + 1) a s →
      I j ((Memory.spec 0).clientResult s (body (d, a)))
        ((Memory.spec 0).clientState s (body (d, a))))
    {n : ℕ} {a : σ} {s : Memory.State} (hi : I n a s) :
    I 0 ((Memory.spec 0).clientResult s (iterate body d n a))
      ((Memory.spec 0).clientState s (iterate body d n a)) := by
  induction n generalizing a s with
  | zero => exact hi
  | succ n ih =>
    rw [show iterate body d (n + 1) a = (body (d, a) >>= iterate body d n) from rfl,
      StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind]
    exact ih (hstep n a s hi)

/-- A read-only `iterate` loop leaves `clientState` unchanged. -/
theorem clientState_iterate_eq_of {δ σ : Type}
    (body : δ × σ → Memory.Prog σ) (d : δ)
    (hstep : ∀ a t, (Memory.spec 0).clientState t (body (d, a)) = t)
    (n : ℕ) (a : σ) (s : Memory.State) :
    (Memory.spec 0).clientState s (iterate body d n a) = s :=
  iterate_invariant_of body d (fun _ _ t => t = s)
    (fun _ a' t ht => (hstep a' t).trans ht) rfl

/-- A read-only `boundedWhile` loop leaves `clientState` unchanged. -/
theorem clientState_boundedWhile_eq_of {δ σ : Type}
    (guard : δ → σ → Prop) [∀ d a, Decidable (guard d a)]
    (body : δ × σ → Memory.Prog σ) (d : δ)
    (hstep : ∀ a t, guard d a → (Memory.spec 0).clientState t (body (d, a)) = t)
    (n : ℕ) (a : σ) (s : Memory.State) :
    (Memory.spec 0).clientState s (boundedWhile guard body d n a) = s :=
  boundedWhile_invariant_of guard body d (fun _ t => t = s)
    (fun a' t ht hg => (hstep a' t hg).trans ht) n a s rfl

/-- Constant upper bound on `memoryCost` of an `iterate` loop with fixed environment `d`. -/
theorem memoryCost_iterate_le_of {δ σ : Type} (body : δ × σ → Memory.Prog σ) (c : ℕ)
    (d : δ) (hstep : ∀ a s, memoryCost (body (d, a)) s ≤ c)
    (n : ℕ) (a : σ) (s : Memory.State) :
    memoryCost (iterate body d n a) s ≤ c * n := by
  induction n generalizing a s with
  | zero => simp [iterate]
  | succ n ih =>
    change memoryCost (body (d, a) >>= iterate body d n) s ≤ c * (n + 1)
    rw [memoryCost_bind']
    have h1 := hstep a s
    have h2 := ih ((Memory.spec 0).clientResult s (body (d, a)))
      ((Memory.spec 0).clientState s (body (d, a)))
    rw [Nat.mul_succ]
    omega

/-- Amortized `memoryCost` bound for `iterate`: if every step from a state satisfying the
step-indexed invariant `I` costs at most `c` plus the drop of the potential `Φ`, and preserves `I`,
then `m` steps cost at most `c * m` plus the initial potential. -/
theorem memoryCost_iterate_le_potential {δ σ : Type} (body : δ × σ → Memory.Prog σ) (d : δ)
    (I : ℕ → σ → Memory.State → Prop) (Φ : σ → Memory.State → ℕ) (c : ℕ)
    (hstep : ∀ j a s, I (j + 1) a s →
      I j ((Memory.spec 0).clientResult s (body (d, a)))
          ((Memory.spec 0).clientState s (body (d, a))) ∧
        memoryCost (body (d, a)) s +
            Φ ((Memory.spec 0).clientResult s (body (d, a)))
              ((Memory.spec 0).clientState s (body (d, a))) ≤
          c + Φ a s)
    (m : ℕ) (a : σ) (s : Memory.State) (hi : I m a s) :
    memoryCost (iterate body d m a) s ≤ c * m + Φ a s := by
  induction m generalizing a s with
  | zero => simp [iterate]
  | succ m ih =>
    change memoryCost (body (d, a) >>= iterate body d m) s ≤ c * (m + 1) + Φ a s
    rw [memoryCost_bind']
    obtain ⟨hi', h1⟩ := hstep m a s hi
    have h2 := ih _ _ hi'
    rw [Nat.mul_succ]
    omega

/-! ## Reductions through `read`, `write`, `map`, and cost combinators -/

theorem clientResult_bind_read {α : Type} (w : ℕ) (s : Memory.State) (a : ℕ)
    (k : ℕ → Memory.Prog α) :
    (Memory.spec w).clientResult s (Memory.read a >>= k) =
      (Memory.spec w).clientResult s (k (s.mem a)) :=
  rfl

theorem clientState_bind_read {α : Type} (w : ℕ) (s : Memory.State) (a : ℕ)
    (k : ℕ → Memory.Prog α) :
    (Memory.spec w).clientState s (Memory.read a >>= k) =
      (Memory.spec w).clientState s (k (s.mem a)) :=
  rfl

theorem clientResult_bind_write {α : Type} (w : ℕ) (s : Memory.State) (a v : ℕ)
    (k : Unit → Memory.Prog α) :
    (Memory.spec w).clientResult s (Memory.write a v >>= k) =
      (Memory.spec w).clientResult ⟨Function.update s.mem a v, s.frontier⟩ (k ()) :=
  rfl

theorem clientState_bind_write {α : Type} (w : ℕ) (s : Memory.State) (a v : ℕ)
    (k : Unit → Memory.Prog α) :
    (Memory.spec w).clientState s (Memory.write a v >>= k) =
      (Memory.spec w).clientState ⟨Function.update s.mem a v, s.frontier⟩ (k ()) :=
  rfl

/-- Running `Memory.read` returns the stored word, leaves memory unchanged, and logs the read.
Add this and `runClient_write` with `attribute [local client_simps]` when simplifying `runClient`
projections directly. -/
theorem runClient_read (w : ℕ) (s : (Memory.spec w).State) (a : ℕ) :
    (Memory.spec w).runClient s (Memory.read a) = (s.mem a, s, [Memory.Op.read a]) :=
  rfl

/-- Running `Memory.write` updates the cell at `a`, preserves the frontier, and logs the write. -/
theorem runClient_write (w : ℕ) (s : (Memory.spec w).State) (a v : ℕ) :
    (Memory.spec w).runClient s (Memory.write a v) =
      ((), ⟨Function.update s.mem a v, s.frontier⟩, [Memory.Op.write a v]) :=
  rfl

theorem memoryCost_bind_le {α β : Type} {p : Memory.Prog α} {q : α → Memory.Prog β}
    {s : Memory.State} {k₁ k₂ : ℕ} (h₁ : memoryCost p s ≤ k₁)
    (h₂ : ∀ x t, memoryCost (q x) t ≤ k₂) :
    memoryCost (p >>= q) s ≤ k₁ + k₂ := by
  rw [memoryCost_bind']
  have := h₂ ((Memory.spec 0).clientResult s p) ((Memory.spec 0).clientState s p)
  omega

/-- A read followed by a continuation of cost at most `k` costs at most `k + 1`. -/
theorem memoryCost_read_bind_le {α : Type} {a : ℕ} {q : ℕ → Memory.Prog α}
    {s : Memory.State} {k : ℕ} (h : ∀ x t, memoryCost (q x) t ≤ k) :
    memoryCost (Memory.read a >>= q) s ≤ k + 1 := by
  have := memoryCost_bind_le (memoryCost_read a s).le h
  omega

/-- A write followed by a continuation of cost at most `k` costs at most `k + 1`. -/
theorem memoryCost_write_bind_le {α : Type} {a v : ℕ} {q : Unit → Memory.Prog α}
    {s : Memory.State} {k : ℕ} (h : ∀ x t, memoryCost (q x) t ≤ k) :
    memoryCost (Memory.write a v >>= q) s ≤ k + 1 := by
  have := memoryCost_bind_le (memoryCost_write a v s).le h
  omega

theorem memoryCost_ite_le {α : Type} {c : Prop} [Decidable c]
    {p₁ p₂ : Memory.Prog α} {s : Memory.State} {k : ℕ}
    (h₁ : memoryCost p₁ s ≤ k) (h₂ : memoryCost p₂ s ≤ k) :
    memoryCost (if c then p₁ else p₂) s ≤ k := by
  rw [memoryCost_ite]
  split_ifs <;> assumption

/-- `ValidHistory` of a counting `iterate` loop whose step returns its index plus one. -/
theorem validHistory_iterate_nat {w : ℕ} {Inv : Memory.State → Prop} [MonotoneMemInv w Inv]
    {δ : Type} {body : δ × ℕ → Memory.Prog ℕ} {d : δ}
    (m i₀ : ℕ) (hstep : ∀ i, i < i₀ + m → ∀ t, Inv t →
      (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t (body (d, i))) ∧
        (Memory.spec 0).clientResult t (body (d, i)) = i + 1)
    {s : Memory.State} (hinv : Inv s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (iterate body d m i₀)) := by
  induction m generalizing i₀ s with
  | zero => exact validHistory_pure w s i₀
  | succ m ih =>
    obtain ⟨hv, hr⟩ := hstep i₀ (by omega) s hinv
    refine validHistory_bind_step hv ?_
    rw [hr]
    exact ih (i₀ + 1) (fun i hi => hstep i (by omega)) (MonotoneMemInv.pres hinv hv)

/-- `ValidHistory` of an `iterate` loop whose state carries a counter in its first component. -/
theorem validHistory_iterate_fst {w : ℕ} {Inv : Memory.State → Prop} [MonotoneMemInv w Inv]
    {δ β : Type} {body : δ × (ℕ × β) → Memory.Prog (ℕ × β)} {d : δ}
    (m i₀ : ℕ) (b₀ : β) (hstep : ∀ i, i < i₀ + m → ∀ b t, Inv t →
      (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t (body (d, (i, b)))) ∧
        ((Memory.spec 0).clientResult t (body (d, (i, b)))).1 = i + 1)
    {s : Memory.State} (hinv : Inv s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (iterate body d m (i₀, b₀))) := by
  induction m generalizing i₀ b₀ s with
  | zero => exact validHistory_pure w s (i₀, b₀)
  | succ m ih =>
    obtain ⟨hv, hr⟩ := hstep i₀ (by omega) b₀ s hinv
    refine validHistory_bind_step hv ?_
    have hpair : (Memory.spec 0).clientResult s (body (d, (i₀, b₀))) =
        (i₀ + 1, ((Memory.spec 0).clientResult s (body (d, (i₀, b₀)))).2) :=
      Prod.ext hr rfl
    rw [hpair]
    exact ih (i₀ + 1) _ (fun i hi => hstep i (by omega)) (MonotoneMemInv.pres hinv hv)

/-! ## Single-address frames -/

/-- `p` leaves memory address `a` unchanged from every starting state. -/
@[expose] def PreservesAt (a : ℕ) {α : Type} (p : Memory.Prog α) : Prop :=
  ∀ s, ((Memory.spec 0).clientState s p).mem a = s.mem a

theorem preservesAt_pure (a : ℕ) {α : Type} (x : α) :
    PreservesAt a (pure x : Memory.Prog α) :=
  fun _ => rfl

theorem preservesAt_read (a b : ℕ) : PreservesAt a (Memory.read b) :=
  fun _ => rfl

theorem preservesAt_write {a b : ℕ} (v : ℕ) (hne : a ≠ b) :
    PreservesAt a (Memory.write b v) := fun s => by
  change Function.update s.mem b v a = s.mem a
  exact Function.update_of_ne hne v s.mem

theorem preservesAt_bind {a : ℕ} {α β : Type} {p : Memory.Prog α} {k : α → Memory.Prog β}
    (hp : PreservesAt a p) (hk : ∀ x, PreservesAt a (k x)) :
    PreservesAt a (p >>= k) := fun s => by
  rw [StateTransitionSpec.clientState_bind, hk, hp]

theorem preservesAt_map {a : ℕ} {α β : Type} (f : α → β) {p : Memory.Prog α}
    (hp : PreservesAt a p) : PreservesAt a (f <$> p) := fun s => by
  rw [StateTransitionSpec.clientState_map, hp]

theorem preservesAt_ite {a : ℕ} {α : Type} (c : Prop) [Decidable c]
    {p₁ p₂ : Memory.Prog α} (h₁ : PreservesAt a p₁) (h₂ : PreservesAt a p₂) :
    PreservesAt a (if c then p₁ else p₂) := by
  split_ifs
  · exact h₁
  · exact h₂

theorem preservesAt_iterate {a : ℕ} {δ σ : Type} {body : δ × σ → Memory.Prog σ} {d : δ}
    (hstep : ∀ st, PreservesAt a (body (d, st))) (m : ℕ) (st₀ : σ) :
    PreservesAt a (iterate body d m st₀) := fun s =>
  iterate_invariant_of body d (fun _ _ t => t.mem a = s.mem a)
    (fun _ st t ht => (hstep st t).trans ht) rfl

/-- Frame of a counting `iterate` loop whose step returns its index plus one: only the steps
`i < m` that actually run need to preserve `a`. -/
theorem preservesAt_iterate_nat {a : ℕ} {δ : Type} {body : δ × ℕ → Memory.Prog ℕ} {d : δ}
    {m : ℕ} (hstep : ∀ i < m, PreservesAt a (body (d, i)) ∧
      ∀ s, (Memory.spec 0).clientResult s (body (d, i)) = i + 1) :
    PreservesAt a (iterate body d m 0) := fun s =>
  (iterate_invariant_of body d (fun rem (i : ℕ) t => i + rem = m ∧ t.mem a = s.mem a)
    (fun rem i t ⟨hsum, hmem⟩ => by
      obtain ⟨hp, hr⟩ := hstep i (by omega)
      exact ⟨by rw [hr]; omega, (hp t).trans hmem⟩)
    ⟨Nat.zero_add _, rfl⟩).2

end Cslib.WordRAM.Realization
