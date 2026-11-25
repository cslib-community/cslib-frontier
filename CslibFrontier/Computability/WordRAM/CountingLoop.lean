/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Structured

/-!
# Constant-cost counting loops

An indexed semantic invariant describes the state after each completed iteration. The native
counter increases by exactly one, and the limit register keeps the fixed endpoint. The rule
derives the counter bounds, decreasing rank and final index from these facts; clients still
prove execution of the actual body, including its word fits and memory semantics.

## Main results

* `ExecWithin.loop_count`: count from the current index to `N` with a body allowance `T`,
  charging `(N - index) * (T + 2) + 2`, including both loop-control instructions per iteration
  and the final test/exit. No one-past-end word-fit premise is required.
* `prefix_write_step`: advance a written-prefix and outside-prefix memory invariant across a
  single store at `d + j`.
* `ExecWithin.loop_prefixWrite`: a counting loop from `0` to `N` whose iteration `j` stores `e j`
  at `d + j`, from a per-iteration body specification alone.

This is an original specialization of `ExecWithin.loop_invariant`.
-/

public section

namespace Cslib.WordRAM

/-- Execute a native counting loop with an indexed semantic invariant. The invariant supplies
the unchanged limit register. Each body execution advances the counter by exactly one and
establishes the next semantic state. The bound excludes setup and the final program halt. -/
theorem ExecWithin.loop_count {B : Basis} {r w N T : ℕ} {index limit : Fin r}
    {body : Code B r} (P : ℕ → Data r → Prop)
    (hlimit : ∀ y, P (y.regs index) y → y.regs limit = N)
    (hbody : ∀ y, P (y.regs index) y → y.regs index < N →
      ∃ z, ExecWithin w body y z T ∧ P (y.regs index + 1) z ∧
        z.regs index = y.regs index + 1)
    {x : Data r} (hle : x.regs index ≤ N) (hx : P (x.regs index) x) :
    ∃ y, ExecWithin w (.loop (.lt index limit) body) x y
      ((N - x.regs index) * (T + 2) + 2) ∧ P N y ∧ y.regs index = N := by
  let I (y : Data r) := y.regs index ≤ N ∧ P (y.regs index) y
  obtain ⟨y, hy, hI, hstop⟩ := loop_invariant
    (cond := .lt index limit) (body := body) I (fun y => N - y.regs index) (by
    intro s hs hc
    have hlt : s.regs index < N := by
      simpa only [Cond.holds_lt, hlimit s hs.2] using hc
    obtain ⟨t, ht, hp, hi⟩ := hbody s hs.2 hlt
    refine ⟨t, ht, ⟨by omega, ?_⟩, by omega⟩
    simpa only [hi] using hp) ⟨hle, hx⟩
  have hend : y.regs index = N := by
    have := hI.1
    simp only [Cond.holds_lt, hlimit y hI.2] at hstop
    omega
  exact ⟨y, hy, hend ▸ hI.2, hend⟩

/-- Advance a loop's written-prefix and outside-prefix memory invariants across a single store
at `d + j`. -/
theorem prefix_write_step {α : Type*} {m₀ m z : ℕ → α} {d j : ℕ} {e : ℕ → α}
    (hm : ∀ i < j, m (d + i) = e i)
    (hf : ∀ a, ¬(d ≤ a ∧ a < d + j) → m a = m₀ a)
    (hz : z = Function.update m (d + j) (e j)) :
    (∀ i < j + 1, z (d + i) = e i) ∧
      ∀ a, ¬(d ≤ a ∧ a < d + (j + 1)) → z a = m₀ a := by
  subst hz
  refine ⟨fun i hi => ?_, fun a ha => ?_⟩
  · by_cases hij : i = j
    · subst hij
      exact Function.update_self _ _ _
    · rw [Function.update_of_ne (by omega : d + i ≠ d + j)]
      exact hm i (by omega)
  · rw [Function.update_of_ne (by omega : a ≠ d + j)]
    exact hf a (by omega)

/-- Execute a native counting loop from index `0` to `N` whose iteration `j` stores `e j` at
`d + j`. The state invariant `R` supplies the unchanged limit register. Each body execution may
read the memory outside the cells stored so far, which still agrees with the initial state, and
must store `e j` at `d + j` and nowhere else, preserve `R` and advance the counter by one. At exit
`[d, d + N)` holds `e` and every other cell is unchanged. The bound excludes setup and the final
program halt. -/
theorem ExecWithin.loop_prefixWrite {B : Basis} {r w N T d : ℕ} {index limit : Fin r}
    {body : Code B r} {x : Data r} (R : Data r → Prop) (e : Fin N → ℕ)
    (hlimit : ∀ y, R y → y.regs limit = N)
    (hbody : ∀ y, R y → (hlt : y.regs index < N) →
      (∀ a, ¬(d ≤ a ∧ a < d + y.regs index) → y.mem a = x.mem a) →
      ∃ z, ExecWithin w body y z T ∧
        z.mem = Function.update y.mem (d + y.regs index) (e ⟨y.regs index, hlt⟩) ∧ R z ∧
        z.regs index = y.regs index + 1)
    (hx : x.regs index = 0) (hR : R x) :
    ∃ y, ExecWithin w (.loop (.lt index limit) body) x y (N * (T + 2) + 2) ∧ R y ∧
      (∀ j : Fin N, y.mem (d + j) = e j) ∧
      ∀ a, ¬(d ≤ a ∧ a < d + N) → y.mem a = x.mem a := by
  let e' (i : ℕ) : ℕ := if h : i < N then e ⟨i, h⟩ else 0
  let P (j : ℕ) (y : Data r) : Prop :=
    R y ∧ (∀ i < j, y.mem (d + i) = e' i) ∧ ∀ a, ¬(d ≤ a ∧ a < d + j) → y.mem a = x.mem a
  obtain ⟨y, hy, ⟨hRy, hm, hf⟩, -⟩ := loop_count (index := index) (limit := limit) (body := body)
    (N := N) P (fun y hy => hlimit y hy.1)
    (fun y ⟨hRy, hm, hf⟩ hlt => by
      obtain ⟨z, hz, hmz, hRz, hiz⟩ := hbody y hRy hlt hf
      rw [show e ⟨y.regs index, hlt⟩ = e' (y.regs index) by simp only [e', hlt, dite_true]] at hmz
      exact ⟨z, hz, ⟨hRz, prefix_write_step hm hf hmz⟩, hiz⟩)
    (by omega) ⟨hR, fun i hi => by omega, fun _ _ => rfl⟩
  rw [hx, Nat.sub_zero] at hy
  exact ⟨y, hy, hRy, fun j => (hm j j.isLt).trans (by simp only [e', j.isLt, dite_true]), hf⟩

end Cslib.WordRAM
