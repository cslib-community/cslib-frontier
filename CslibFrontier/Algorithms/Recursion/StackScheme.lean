/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Ring

/-!
# Depth-first recursion with an explicit stack

A *recursion scheme* (`Cslib.Algorithms.StackRecursion.Scheme`) evaluates node descriptions `x : X`
to values `y : Y` without reference to any machine model. A node is either a leaf, evaluated by
`leaf`, or a call, which keeps an accumulator `a : A`: starting from `start x`, it asks `next x a`
for its next child, folds the child's value into the accumulator with `absorb`, and when `next`
returns `none` produces its value with `finish`. Children may depend on the values of earlier
children through the accumulator.

The explicit-stack transition `Scheme.step` keeps the open calls with their accumulators, innermost
first, together with a register holding either a pending call or a returned value (`State`). Each
step performs one call or one return. A derivation `Scheme.Eval I x y n h`, with `n` nodes and at
most `h` open calls, reaches `y` in `2 * n - 1` steps (`Scheme.Eval.run`), through states with at
most `h` open calls whose nodes, frames and values satisfy the invariant `I`
(`Scheme.Eval.good_iterate`). When `2 * n - 1 ≤ fuel a`, the clocked run `Scheme.run` returns
`some y` (`Scheme.run_eq_some`).

Multi-tape Turing machine polynomial-time step certificates and native workspace/time bounds for
this scheme live in `CslibFrontier.Computability.GenericRAM.Native.StackRecursion`.

## Main definitions

* `Cslib.Algorithms.StackRecursion.Scheme`: an explicit-stack recursion scheme.
* `Cslib.Algorithms.StackRecursion.Invariant`: predicates on the nodes, frames and values met.
* `Cslib.Algorithms.StackRecursion.State`, `Cslib.Algorithms.StackRecursion.State.returned`:
  the explicit-stack state and its returned-value register.
* `Cslib.Algorithms.StackRecursion.Scheme.Loop`, `Cslib.Algorithms.StackRecursion.Scheme.Eval`,
  `Cslib.Algorithms.StackRecursion.Scheme.Good`: derivations of the loop of a call and of the value
  of a node, with their node counts and stack depths, and the state invariant.
* `Cslib.Algorithms.StackRecursion.Scheme.resume`, `Cslib.Algorithms.StackRecursion.Scheme.step`,
  `Cslib.Algorithms.StackRecursion.Scheme.run`: the stack transition and its clocked run.

## Main results

* `Cslib.Algorithms.StackRecursion.Scheme.Loop.child`: a call's loop absorbs an evaluated child.
* `Cslib.Algorithms.StackRecursion.Scheme.Loop.run`,
  `Cslib.Algorithms.StackRecursion.Scheme.Eval.run`: a loop with `n` child nodes runs in `2 * n`
  steps, and a derivation with `n` nodes reaches its value in `2 * n - 1` steps.
* `Cslib.Algorithms.StackRecursion.Scheme.Loop.good`,
  `Cslib.Algorithms.StackRecursion.Scheme.Eval.good`,
  `Cslib.Algorithms.StackRecursion.Scheme.Eval.good_iterate`: every state reached along a run
  satisfies the stack-depth and node/frame/value invariant.
* `Cslib.Algorithms.StackRecursion.Scheme.run_eq_some`: enough fuel returns `some y`.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Appendix D.4.7 (p. 64).
-/

public section

namespace Cslib.Algorithms.StackRecursion

/-- A *recursion scheme*. A node `x` is a leaf when `isLeaf x`, with value `leaf x`. Otherwise
it is a call: its accumulator starts at `start x`; while `next x a` returns a child, the child is
evaluated and its value folded into the accumulator by `absorb`; when `next x a` is `none` the
call returns `finish x a`. -/
structure Scheme (X A Y : Type) where
  /-- Whether a node is a leaf. -/
  isLeaf : X → Bool
  /-- The value of a leaf. -/
  leaf : X → Y
  /-- The initial accumulator of a call. -/
  start : X → A
  /-- The next child of a call with the given accumulator, or `none` when it is done. -/
  next : X → A → Option X
  /-- Fold the value of the current child into the accumulator. -/
  absorb : X → A → Y → A
  /-- The value of a call from its final accumulator. -/
  finish : X → A → Y

/-- Predicates on what a derivation meets: the nodes evaluated, the frames pushed (a call with
its accumulator while one of its children is evaluated) and the values returned. -/
structure Invariant (X A Y : Type) where
  /-- Every node evaluated satisfies `node`. -/
  node : X → Prop
  /-- Every pushed frame satisfies `frame`. -/
  frame : X → A → Prop
  /-- Every returned value satisfies `value`. -/
  value : Y → Prop

/-- A state of the stack machine: the open calls with their accumulators, innermost first, a
pending call and a returned value. -/
abbrev State (X A Y : Type) := List (X × A) × Option X × Option Y

/-- The returned-value register of an explicit-stack state. -/
abbrev State.returned {X A Y : Type} (σ : State X A Y) : Option Y := σ.2.2

namespace Scheme

variable {X A Y : Type} (R : Scheme X A Y)

/-- Continue the call `x` with accumulator `a` above the stack `st`: push its frame and call its
next child, or return its value when it has none. -/
@[expose] def resume (x : X) (a : A) (st : List (X × A)) : State X A Y :=
  match R.next x a with
  | none => (st, none, some (R.finish x a))
  | some c => ((x, a) :: st, some c, none)

/-- **One step of the stack machine.** A pending leaf is evaluated; a pending call is started; a
returned value is absorbed by the innermost open call, which then continues. A value returned
with no open call is final. -/
@[expose] def step : State X A Y → State X A Y
  | (st, some x, _) => if R.isLeaf x then (st, none, some (R.leaf x)) else R.resume x (R.start x) st
  | ((x, a) :: st, none, some y) => R.resume x (R.absorb x a y) st
  | σ => σ

theorem resume_of_next_none {x : X} {a : A} (st : List (X × A)) (h : R.next x a = none) :
    R.resume x a st = (st, none, some (R.finish x a)) := by
  simp [resume, h]

theorem resume_of_next_some {x c : X} {a : A} (st : List (X × A)) (h : R.next x a = some c) :
    R.resume x a st = ((x, a) :: st, some c, none) := by
  simp [resume, h]

theorem step_leaf {x : X} (st : List (X × A)) (r : Option Y) (h : R.isLeaf x = true) :
    R.step (st, some x, r) = (st, none, some (R.leaf x)) := by
  simp [step, h]

theorem step_call {x : X} (st : List (X × A)) (r : Option Y) (h : R.isLeaf x = false) :
    R.step (st, some x, r) = R.resume x (R.start x) st := by
  simp [step, h]

theorem step_return (x : X) (a : A) (st : List (X × A)) (y : Y) :
    R.step ((x, a) :: st, none, some y) = R.resume x (R.absorb x a y) st := rfl

/-- A value returned with no open call is final. -/
@[simp] theorem step_final (y : Y) : R.step ([], none, some y) = ([], none, some y) := rfl

/-- **The loop of a call.** `R.Loop I x a a' n h`: the call `x`, from accumulator `a`, evaluates
its remaining children with `n` nodes in total and ends with accumulator `a'`, using at most `h`
stack levels above its own frame. Every frame pushed, child evaluated and value returned
satisfies `I`. -/
inductive Loop (I : Invariant X A Y) : X → A → A → ℕ → ℕ → Prop
  /-- The call has no further child. -/
  | done {x : X} {a : A} : R.next x a = none → Loop I x a a 0 0
  /-- The next child is a leaf. -/
  | leaf {x c : X} {a a' : A} {n h : ℕ} : I.frame x a → R.next x a = some c → I.node c →
      R.isLeaf c = true → I.value (R.leaf c) → Loop I x (R.absorb x a (R.leaf c)) a' n h →
      Loop I x a a' (n + 1) h
  /-- The next child is a call, whose own loop ends with accumulator `b`. -/
  | call {x c : X} {a b a' : A} {n₁ h₁ n₂ h₂ : ℕ} : I.frame x a → R.next x a = some c →
      I.node c → R.isLeaf c = false → Loop I c (R.start c) b n₁ h₁ → I.value (R.finish c b) →
      Loop I x (R.absorb x a (R.finish c b)) a' n₂ h₂ →
      Loop I x a a' (n₁ + 1 + n₂) (max (h₁ + 1) h₂)

/-- **A derivation of the value of a node.** `R.Eval I x y n h`: the node `x` has value `y`,
computed with `n` nodes and at most `h` open calls, and every node, frame and value met satisfies
`I`. A leaf has one node and no open call; a call has one more node and one more level than its
loop. -/
@[expose] def Eval (I : Invariant X A Y) (x : X) (y : Y) (n h : ℕ) : Prop :=
  I.node x ∧ I.value y ∧
    ((R.isLeaf x = true ∧ y = R.leaf x ∧ n = 1 ∧ h = 0) ∨
      (R.isLeaf x = false ∧ ∃ b n' h', R.Loop I x (R.start x) b n' h' ∧ y = R.finish x b ∧
        n = n' + 1 ∧ h = h' + 1))

variable {R} {I : Invariant X A Y}

/-- A leaf is evaluated by `leaf`. -/
theorem Eval.leaf {x : X} (hx : I.node x) (hl : R.isLeaf x = true) (hv : I.value (R.leaf x)) :
    R.Eval I x (R.leaf x) 1 0 :=
  ⟨hx, hv, .inl ⟨hl, rfl, rfl, rfl⟩⟩

/-- A call is evaluated by its loop, from `start`, and `finish`. -/
theorem Eval.call {x : X} {b : A} {n h : ℕ} (hx : I.node x) (hl : R.isLeaf x = false)
    (hloop : R.Loop I x (R.start x) b n h) (hv : I.value (R.finish x b)) :
    R.Eval I x (R.finish x b) (n + 1) (h + 1) :=
  ⟨hx, hv, .inr ⟨hl, b, n, h, hloop, rfl, rfl, rfl⟩⟩

/-- **The loop absorbs an evaluated child.** -/
theorem Loop.child {x c : X} {a a' : A} {y : Y} {n₁ h₁ n₂ h₂ : ℕ} (hf : I.frame x a)
    (hn : R.next x a = some c) (hc : R.Eval I c y n₁ h₁)
    (hrest : R.Loop I x (R.absorb x a y) a' n₂ h₂) :
    R.Loop I x a a' (n₁ + n₂) (max h₁ h₂) := by
  obtain ⟨hnode, hval, ⟨hl, rfl, rfl, rfl⟩ | ⟨hl, b, n', h', hloop, rfl, rfl, rfl⟩⟩ := hc
  · simpa [Nat.add_comm] using Loop.leaf hf hn hnode hl hval hrest
  · exact Loop.call hf hn hnode hl hloop hval hrest

/-- Every derivation has at least one node. -/
theorem Eval.one_le {x : X} {y : Y} {n h : ℕ} (he : R.Eval I x y n h) : 1 ≤ n := by
  obtain ⟨-, -, ⟨-, -, rfl, -⟩ | ⟨-, -, -, -, -, -, rfl, -⟩⟩ := he <;> omega

/-! ### The machine follows the derivation -/

/-- **A loop is run in two steps per node**, ending with the value of the call returned to the
stack below it. -/
theorem Loop.run {x : X} {a a' : A} {n h : ℕ} (hl : R.Loop I x a a' n h) (st : List (X × A)) :
    R.step^[2 * n] (R.resume x a st) = (st, none, some (R.finish x a')) := by
  induction hl generalizing st with
  | done hn => exact R.resume_of_next_none st hn
  | @leaf x c a a' n h _ hn _ hl _ _ ih =>
    rw [Nat.mul_succ, Function.iterate_succ_apply, Function.iterate_succ_apply,
      R.resume_of_next_some st hn, R.step_leaf _ _ hl, R.step_return, ih]
  | @call x c a b a' n₁ h₁ n₂ h₂ _ hn _ hl _ _ _ ih₁ ih₂ =>
    rw [show 2 * (n₁ + 1 + n₂) = 2 * n₂ + 1 + 2 * n₁ + 1 by ring]
    simp only [Function.iterate_add_apply, Function.iterate_one]
    rw [R.resume_of_next_some st hn, R.step_call _ _ hl, ih₁, R.step_return, ih₂]

/-- **A node with `n` nodes is evaluated in `2 * n - 1` steps**, above any stack. -/
theorem Eval.run {x : X} {y : Y} {n h : ℕ} (he : R.Eval I x y n h) (st : List (X × A)) :
    R.step^[2 * n - 1] (st, some x, none) = (st, none, some y) := by
  obtain ⟨-, -, ⟨hl, rfl, rfl, rfl⟩ | ⟨hl, b, n', h', hloop, rfl, rfl, rfl⟩⟩ := he
  · exact R.step_leaf st none hl
  · rw [show 2 * (n' + 1) - 1 = 2 * n' + 1 by omega, Function.iterate_succ_apply,
      R.step_call _ _ hl, hloop.run]

/-! ### The states met -/

/-- A state is *good* for `I` and a depth `H` when at most `H` calls are open, every open frame
satisfies `I`, and the register holds either a pending node or a returned value satisfying
`I`. -/
@[expose] def Good (I : Invariant X A Y) (H : ℕ) (σ : State X A Y) : Prop :=
  σ.1.length ≤ H ∧ (∀ f ∈ σ.1, I.frame f.1 f.2) ∧
    ((∃ x, σ.2 = (some x, none) ∧ I.node x) ∨ (∃ y, σ.2 = (none, some y) ∧ I.value y))

theorem Good.mono {H H' : ℕ} {σ : State X A Y} (hσ : Good I H σ) (h : H ≤ H') : Good I H' σ :=
  ⟨hσ.1.trans h, hσ.2⟩

private theorem good_push {x : X} {a : A} {st : List (X × A)} {H : ℕ} {r : Option X × Option Y}
    (hst : ∀ f ∈ st, I.frame f.1 f.2) (hf : I.frame x a) (hH : st.length + 1 ≤ H)
    (hr : (∃ x, r = (some x, none) ∧ I.node x) ∨ (∃ y, r = (none, some y) ∧ I.value y)) :
    Good I H ((x, a) :: st, r) :=
  ⟨by simpa using hH, List.forall_mem_cons.mpr ⟨hf, hst⟩, hr⟩

/-- **The states of a loop are good**, strictly before it returns. -/
theorem Loop.good {x : X} {a a' : A} {n h : ℕ} (hl : R.Loop I x a a' n h) {st : List (X × A)}
    (hst : ∀ f ∈ st, I.frame f.1 f.2) :
    ∀ j < 2 * n, Good I (st.length + h + 1) (R.step^[j] (R.resume x a st)) := by
  induction hl generalizing st with
  | done _ => intro j hj; omega
  | @leaf x c a a' n h hf hn hc hl hv _ ih =>
    intro j hj
    rw [R.resume_of_next_some st hn]
    rcases j with _ | _ | j
    · exact good_push hst hf (by omega) (.inl ⟨c, rfl, hc⟩)
    · rw [Function.iterate_one, R.step_leaf _ _ hl]
      exact good_push hst hf (by omega) (.inr ⟨_, rfl, hv⟩)
    · rw [Function.iterate_succ_apply, Function.iterate_succ_apply, R.step_leaf _ _ hl,
        R.step_return]
      exact ih hst j (by omega)
  | @call x c a b a' n₁ h₁ n₂ h₂ hf hn hc hl hloop₁ hv _ ih₁ ih₂ =>
    intro j hj
    rw [R.resume_of_next_some st hn]
    rcases j with _ | j
    · exact good_push hst hf (by omega) (.inl ⟨c, rfl, hc⟩)
    rw [Function.iterate_succ_apply, R.step_call _ _ hl]
    rcases Nat.lt_or_ge j (2 * n₁) with hj₁ | hj₁
    · exact (ih₁ (List.forall_mem_cons.mpr ⟨hf, hst⟩) j hj₁).mono
        (by simp only [List.length_cons]; omega)
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj₁
    rw [Nat.add_comm (2 * n₁) k, Function.iterate_add_apply, hloop₁.run]
    rcases k with _ | k
    · exact good_push hst hf (by omega) (.inr ⟨_, rfl, hv⟩)
    · rw [Function.iterate_succ_apply, R.step_return]
      exact (ih₂ hst k (by omega)).mono (by omega)

/-- **The states of an evaluation are good**, up to and including its returned value. -/
theorem Eval.good {x : X} {y : Y} {n h : ℕ} (he : R.Eval I x y n h) {st : List (X × A)}
    (hst : ∀ f ∈ st, I.frame f.1 f.2) :
    ∀ j ≤ 2 * n - 1, Good I (st.length + h) (R.step^[j] (st, some x, none)) := by
  obtain ⟨hx, hy, ⟨hl, rfl, rfl, rfl⟩ | ⟨hl, b, n', h', hloop, rfl, rfl, rfl⟩⟩ := he <;>
    rintro (_ | j) hj
  · exact ⟨by simp, hst, .inl ⟨x, rfl, hx⟩⟩
  · rw [show j = 0 by omega, Function.iterate_one, R.step_leaf _ _ hl]
    exact ⟨by simp, hst, .inr ⟨_, rfl, hy⟩⟩
  · exact ⟨by simp, hst, .inl ⟨x, rfl, hx⟩⟩
  · rw [Function.iterate_succ_apply, R.step_call _ _ hl]
    rcases Nat.lt_or_ge j (2 * n') with hj' | hj'
    · exact (hloop.good hst j hj').mono (by omega)
    · rw [show j = 2 * n' by omega, hloop.run]
      exact ⟨by simp, hst, .inr ⟨_, rfl, hy⟩⟩

/-- **Every state of a run from an empty stack is good**, including the final state, which no
step changes. -/
theorem Eval.good_iterate {x : X} {y : Y} {n h : ℕ} (he : R.Eval I x y n h) (j : ℕ) :
    Good I h (R.step^[j] ([], some x, none)) := by
  by_cases hj : j ≤ 2 * n - 1
  · simpa using he.good (st := []) (by simp) j hj
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt (show 2 * n - 1 < j by omega)
    rw [show 2 * n - 1 + k + 1 = (k + 1) + (2 * n - 1) by omega, Function.iterate_add_apply,
      he.run, Function.iterate_fixed (R.step_final y)]
    exact ⟨by simp, by simp, .inr ⟨y, rfl, he.2.1⟩⟩

variable (R) in
/-- **The clocked run**: the register after `fuel a` steps from the root `root a` on an empty
stack. -/
@[expose] def run {I : Type} (fuel : I → ℕ) (root : I → X) (a : I) : Option Y :=
  State.returned (R.step^[fuel a] ([], some (root a), none))

/-- **Enough fuel gives the value.** -/
theorem run_eq_some {I : Type} {fuel : I → ℕ} {root : I → X} {Inv : Invariant X A Y} {a : I}
    {y : Y} {N H : ℕ} (he : R.Eval Inv (root a) y N H) (hfuel : 2 * N - 1 ≤ fuel a) :
    R.run fuel root a = some y := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hfuel
  rw [run, hk, Nat.add_comm, Function.iterate_add_apply, he.run,
    Function.iterate_fixed (R.step_final y)]

end Scheme

end Cslib.Algorithms.StackRecursion
