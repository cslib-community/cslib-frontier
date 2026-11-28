/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Realization.LoopFrame
public import CslibFrontier.Tactic.Fits
public import CslibFrontier.Tactic.WramOmega
public meta import Lean.Elab.Tactic.Basic

/-!
# Loops, calls and a `do`-block driver for framed memory triples

`Memory.FramedTriple w s p c S Q` says that the memory program `p`, run from `s` at word size `w`,
issues only admissible operations, costs at most `c` memory units, changes no allocated cell
outside `S` and never lowers the frontier (`Memory.Modifies S`), and ends in a result and state
satisfying `Q`. This module adds the rules that a program verified for a `realize` certificate
needs beyond the primitive ones of `Cslib.DataStructure.Memory.TripleFrame`:

* `FramedTriple.iterate` checks a bounded loop `iterate body d n a₀` from an invariant. Each step,
  started at a state the loop may reach, meets the body's realization safety predicate and a
  framed triple re-establishing the invariant; the loop then meets its safety predicate
  `iterationSafe` and a framed triple. The step and the final postcondition receive the frame
  facts of the loop so far, so invariants need not repeat them.
* `FramedTriple.call` and `FramedTriple.call_eq` call a sub-program through its own triple, whose
  modifies-set lies in the caller's; the continuation receives the sub-program's finer frame.
  `FramedTriple.seq` continues at the concrete state and result that the sub-program reaches, as
  safety predicates that name intermediate states require.
* `FramedTriple.ite_max` and `FramedTriple.dite_max` combine branch costs by `max`.
* `framedTriple_iff_frontier_eq` relates a framed triple whose postcondition keeps the frontier to
  the conjunction (history, cost, frontier, frame, postcondition) of older specifications.

The tactic `framed_triple` walks a `do` block with these rules. It synthesizes the cost and compares
it with the stated bound at the end; it applies a primitive rule for each read, write, allocation
and return and a conditional rule for each `if`, and it takes a sub-program call through a triple
for it in the local context: by `FramedTriple.call_eq` when that triple fixes the result and
final state, and by `FramedTriple.seq` otherwise. Side conditions are tried with `region_omega`,
which proves address, region and word-size bounds (`a < s.frontier`, `a ∈ S`, `a ∉ S` and
`S ⊆ T` for regions built from `Set.Ico`, unions, insertions and set-builder intervals, and
`Fits w v`) by linear arithmetic over the plain arithmetic hypotheses, unfolding the
`@[wram_arith]` layout definitions and local definitions. The goals it cannot close remain in
the order of the program: postconditions at each `pure`, and unsolved side conditions where they
arise.

## Usage

A loop `copyWordsProg a := iterate copyStep a a.len 0`, whose body reads `a.src + i`, writes it to
`a.dst + i` and returns `i + 1`, is specified and proved as follows.

```
theorem copyWordsProg_spec (a : CopyArgs) (s₀ : Memory.State)
    (hsrc_f : a.src + a.len ≤ s₀.frontier) (hdst_f : a.dst + a.len ≤ s₀.frontier)
    (hdisj : a.src + a.len ≤ a.dst) (hfit_src : Fits w (a.src + a.len))
    (hfit_dst : Fits w (a.dst + a.len)) (hfit_vals : ∀ i < a.len, Fits w (s₀.mem (a.src + i))) :
    iterationSafe copyStep CopyStepSafe w a a.len 0 s₀ ∧
      Memory.FramedTriple w s₀ (copyWordsProg a) (2 * a.len) (Set.Ico a.dst (a.dst + a.len))
        fun _ t => ∀ i < a.len, t.mem (a.dst + i) = s₀.mem (a.src + i) := by
  refine Memory.FramedTriple.iterate
    (fun k i t => i = k ∧ ∀ j < k, t.mem (a.dst + j) = s₀.mem (a.src + j))
    ⟨rfl, by simp⟩ (fun k hk i t ⟨hi, hdone⟩ ⟨hfr, hframe⟩ => ?_) fun _ _ h _ => h.2
  subst i
  have hsrc := hframe (a.src + k) (by omega) (by region_omega)
  have hval := hsrc ▸ hfit_vals k hk
  refine ⟨⟨by region_omega, by region_omega, by region_omega⟩, ?_⟩
  unfold copyStep
  framed_triple
  refine ⟨rfl, Nat.forall_lt_succ_right.2 ⟨fun j hj => ?_, by simp [hsrc]⟩⟩
  simp [hj.ne, hdone j hj]
```

The first argument of `FramedTriple.iterate` is the invariant, the second its initial case, the
third the step, which receives the invariant and the frame `Memory.Modifies S s₀ t` of the loop so
far and returns the body's safety predicate and its triple, and the last derives the
postcondition. `framed_triple` closes the step's address, region and word-size conditions and its
cost, and leaves the postcondition of the step.

## Main results

* `Cslib.DataStructure.Memory.FramedTriple.iterate`: bounded iteration with the loop's safety
  predicate.
* `Cslib.DataStructure.Memory.FramedTriple.call`, `Cslib.DataStructure.Memory.FramedTriple.call_eq`,
  `Cslib.DataStructure.Memory.FramedTriple.seq`: calling a sub-program through its triple.
* `Cslib.DataStructure.Memory.FramedTriple.ite_max`,
  `Cslib.DataStructure.Memory.FramedTriple.dite_max`: conditionals with branch costs combined by
  `max`.
* `Cslib.WordRAM.Realization.framedTriple_iff_frontier_eq`: framed triples that keep the frontier
  as frontier-and-frame conjunctions.

## Main definitions

* `region_omega`: closes address, region and word-size side conditions; `region_prune` clears the
  hypotheses that are not plain arithmetic before it calls the arithmetic closers.
* `framed_triple_step`, `framed_triple`: one structural step, and the walk of a `do` block.

The rules and tactics are original infrastructure over the existing memory clients.
-/

public section

namespace Cslib.DataStructure.Memory.FramedTriple

open Cslib.WordRAM Cslib.WordRAM.Realization

variable {w : ℕ} {α β : Type} {s : State} {c c₁ c₂ : ℕ} {S S₁ : Set ℕ} {Q : α → State → Prop}

/-- Call a sub-program through its own framed triple, whose modifies-set lies in the caller's. The
continuation runs from every result and state the sub-program may reach, with its postcondition
and its finer frame. Costs add. -/
theorem call {p : Prog β} {k : β → Prog α} {Q₁ : β → State → Prop}
    (hp : FramedTriple w s p c₁ S₁ Q₁) (hS : S₁ ⊆ S)
    (hk : ∀ b t, Q₁ b t → Memory.Modifies S₁ s t → FramedTriple w t (k b) c₂ S Q) :
    FramedTriple w s (p >>= k) (c₁ + c₂) S Q :=
  bind_same (Triple.mono hp le_rfl fun b t ⟨hm, hq⟩ => ⟨hm.mono hS, hk b t hq hm⟩)

/-- Call a sub-program whose framed triple fixes its result `r` and final state `t`; the
continuation runs from them. `framed_triple` applies this rule with a triple from the local
context. -/
theorem call_eq {p : Prog β} {k : β → Prog α} {r : β} {t : State}
    (hp : FramedTriple w s p c₁ S₁ fun r' t' => r' = r ∧ t' = t) (hS : S₁ ⊆ S)
    (hk : FramedTriple w t (k r) c₂ S Q) : FramedTriple w s (p >>= k) (c₁ + c₂) S Q :=
  call hp hS fun _ _ h _ => h.1 ▸ h.2 ▸ hk

/-- Call a sub-program through its own framed triple and continue at the concrete result and
state that the realization interpreter assigns it, as a realization safety predicate that names
intermediate states requires. -/
theorem seq {p : Prog β} {k : β → Prog α} {Q₁ : β → State → Prop}
    (hp : FramedTriple w s p c₁ S₁ Q₁) (hS : S₁ ⊆ S)
    (hk : FramedTriple w ((spec 0).clientState s p) (k ((spec 0).clientResult s p)) c₂ S Q) :
    FramedTriple w s (p >>= k) (c₁ + c₂) S Q :=
  call_eq ((framedTriple_with_realization hp).mono le_rfl fun _ _ h => ⟨h.1, h.2.1⟩) hS hk

/-- A conditional whose branch costs combine by `max`. -/
theorem ite_max {cond : Prop} [Decidable cond] {p₁ p₂ : Prog α}
    (h₁ : cond → FramedTriple w s p₁ c₁ S Q) (h₂ : ¬cond → FramedTriple w s p₂ c₂ S Q) :
    FramedTriple w s (if cond then p₁ else p₂) (max c₁ c₂) S Q :=
  ite (fun h => (h₁ h).mono (le_max_left _ _) fun _ _ => id)
    fun h => (h₂ h).mono (le_max_right _ _) fun _ _ => id

/-- A dependent conditional whose branch costs combine by `max`. -/
theorem dite_max {cond : Prop} [Decidable cond] {p₁ : cond → Prog α} {p₂ : ¬cond → Prog α}
    (h₁ : ∀ h : cond, FramedTriple w s (p₁ h) c₁ S Q)
    (h₂ : ∀ h : ¬cond, FramedTriple w s (p₂ h) c₂ S Q) :
    FramedTriple w s (if h : cond then p₁ h else p₂ h) (max c₁ c₂) S Q :=
  dite (fun h => (h₁ h).mono (le_max_left _ _) fun _ _ => id)
    fun h => (h₂ h).mono (le_max_right _ _) fun _ _ => id

/-- **Bounded iteration.** Each of the `n` steps, run from a state satisfying the invariant and
reached from `s` within the frame `S`, meets the body's realization safety predicate and a framed
triple of cost `c` re-establishing the invariant. The loop then meets its iteration safety
predicate and a framed triple of cost `c * n` whose postcondition follows from the final invariant
and the loop's frame. Unlike `iterate_framedTriple_of_step`, the invariant need not restate the
frame of the loop so far. -/
theorem iterate {δ σ : Type} {body : δ × σ → Prog σ} {safe : ℕ → δ × σ → State → Prop} {d : δ}
    {n : ℕ} {a₀ : σ} {Q : σ → State → Prop} (inv : ℕ → σ → State → Prop) (h₀ : inv 0 a₀ s)
    (hstep : ∀ k < n, ∀ a t, inv k a t → Memory.Modifies S s t →
      safe w (d, a) t ∧ FramedTriple w t (body (d, a)) c S (inv (k + 1)))
    (hpost : ∀ a t, inv n a t → Memory.Modifies S s t → Q a t) :
    iterationSafe body safe w d n a₀ s ∧
      FramedTriple w s (Realization.iterate body d n a₀) (c * n) S Q := by
  obtain ⟨hsafe, h⟩ := iterate_framedTriple_of_step body safe w d c n
    (fun k a t => inv k a t ∧ Memory.Modifies S s t) S
    (fun k hk a t ⟨hi, hm⟩ => by
      obtain ⟨hs, hft⟩ := hstep k hk a t hi hm
      exact ⟨fun _ => hs, Triple.mono hft le_rfl fun _ _ ⟨hm', hi'⟩ => ⟨hm', hi', hm.trans hm'⟩⟩)
    a₀ s ⟨h₀, Modifies.refl S s⟩
  exact ⟨hsafe, h.mono le_rfl fun a t ⟨hi, hm⟩ => hpost a t hi hm⟩

end Cslib.DataStructure.Memory.FramedTriple

namespace Cslib.WordRAM.Realization

open Cslib.DataStructure

/-- A framed triple whose postcondition keeps the frontier is the conjunction of an admissible
history, a cost bound, an unchanged frontier, a frame over every cell outside `{x | mod x}` and
the postcondition, read through the realization interpreter. -/
theorem framedTriple_iff_frontier_eq {α : Type} {w : ℕ} {s : Memory.State} {p : Memory.Prog α}
    {c : ℕ} {mod : ℕ → Prop} {Q : α → Memory.State → Prop} :
    Memory.FramedTriple w s p c {x | mod x} (fun a t => t.frontier = s.frontier ∧ Q a t) ↔
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p) ∧
      memoryCost p s ≤ c ∧ ((Memory.spec 0).clientState s p).frontier = s.frontier ∧
      (∀ x, ¬mod x → ((Memory.spec 0).clientState s p).mem x = s.mem x) ∧
      Q ((Memory.spec 0).clientResult s p) ((Memory.spec 0).clientState s p) := by
  rw [framedTriple_iff_realization]
  refine ⟨fun ⟨hv, hc, hm, hfr, hq⟩ => ⟨hv, hc, hfr, fun x hx => ?_, hq⟩,
    fun ⟨hv, hc, hfr, hx, hq⟩ => ⟨hv, hc, ⟨hfr.ge, fun x _ h => hx x h⟩, hfr, hq⟩⟩
  by_cases hlt : x < s.frontier
  · exact hm.2 x hlt hx
  · rw [← clientState_width w]
    exact Memory.mem_clientState_of_frontier_le s p hv
      (by rw [clientState_width w, hfr]; omega)

end Cslib.WordRAM.Realization

public meta section

namespace Cslib.WordRAM.Realization.FramedLoop

open Lean Meta Elab Tactic

/-- Whether `e` is a proposition that linear arithmetic reads as it stands: an equation,
disequation or comparison of natural numbers or integers, a word-size bound `Fits w v`, a
membership `x ∈ S` that interval simplification turns into one of these, or a propositional
combination of these, without quantifiers. -/
private partial def isPlainArith (e : Expr) : MetaM Bool := do
  let e ← instantiateMVars e
  let isNum (α : Expr) : Bool := α.isConstOf ``Nat || α.isConstOf ``Int
  match_expr e with
  | Eq α _ _ => return isNum α
  | Ne α _ _ => return isNum α
  | LE.le α _ _ _ => return isNum α
  | LT.lt α _ _ _ => return isNum α
  | GE.ge α _ _ _ => return isNum α
  | GT.gt α _ _ _ => return isNum α
  | Membership.mem _ _ _ _ _ => return true
  | Not p => isPlainArith p
  | And p q => return (← isPlainArith p) && (← isPlainArith q)
  | Or p q => return (← isPlainArith p) && (← isPlainArith q)
  | Iff p q => return (← isPlainArith p) && (← isPlainArith q)
  | True => return true
  | False => return true
  | _ =>
    match e with
    | .forallE _ p q _ => return !q.hasLooseBVars && (← isPlainArith p) && (← isPlainArith q)
    | _ => return e.isAppOf ``Cslib.WordRAM.Fits

/-- Clear every hypothesis that is a proposition other than plain arithmetic (comparisons of
natural numbers or integers, word-size bounds `Fits w v`, and their quantifier-free combinations),
so that the arithmetic closers of `region_omega` see only the facts they can use. -/
elab (name := regionPrune) "region_prune" : tactic => liftMetaTactic1 fun g => g.withContext do
  let mut drop : Array FVarId := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail || d.isLet then continue
    if ← isProp d.type then
      unless ← isPlainArith d.type do drop := drop.push d.fvarId
  g.tryClearMany drop

end Cslib.WordRAM.Realization.FramedLoop

end

namespace Cslib.WordRAM.Realization.FramedLoop

/-- Close an address, region or word-size side condition: `a < s.frontier`, `a ∈ S`, `a ∉ S`,
`S ⊆ T` for regions built from `Set.Ico`, `∪`, `insert`, singletons and set-builder intervals, or
`Fits w v`. It keeps only the plain arithmetic hypotheses (`region_prune`), unfolds interval
membership and structure projections, and closes the goal by `omega`, by `fits`, or by
`wram_omega` over the `@[wram_arith]` layout definitions and the local definitions in context. -/
macro (name := regionOmega) "region_omega" : tactic => `(tactic|
  first
  | assumption
  | (region_prune
     (try simp only [Set.mem_Ico, Set.mem_Iio, Set.mem_Ici, Set.mem_union, Set.mem_insert_iff,
       Set.mem_singleton_iff, Set.mem_ofPred_eq, Set.mem_univ, Set.mem_empty_iff_false] at *) <;>
     first
     | omega
     | fits
     | wram_omega_silent)
  | (intro _ _
     region_prune
     (try simp only [Set.mem_Ico, Set.mem_Iio, Set.mem_Ici, Set.mem_union, Set.mem_insert_iff,
       Set.mem_singleton_iff, Set.mem_ofPred_eq, Set.mem_univ, Set.mem_empty_iff_false] at *) <;>
     first
     | omega
     | wram_omega_silent))

/-- One structural step of `framed_triple` on the main goal: a read, write, allocation or
return, a conditional, or a call of a sub-program through a framed triple for it in the local
context (`FramedTriple.call_eq` when the triple fixes the result and final state,
`FramedTriple.seq` otherwise). Side conditions are tried with `region_omega` and left open
otherwise. -/
macro (name := framedTripleStep) "framed_triple_step" : tactic => `(tactic|
  first
  | (eapply Cslib.DataStructure.Memory.FramedTriple.read_bind; on_goal 1 => try region_omega)
  | (eapply Cslib.DataStructure.Memory.FramedTriple.write_bind_of_mem
     on_goal 3 => try region_omega
     on_goal 2 => try region_omega
     on_goal 1 => try region_omega)
  | (eapply Cslib.DataStructure.Memory.FramedTriple.read; on_goal 1 => try region_omega)
  | (eapply Cslib.DataStructure.Memory.FramedTriple.write
     on_goal 3 => try region_omega
     on_goal 2 => try region_omega
     on_goal 1 => try region_omega)
  | (eapply Cslib.DataStructure.Memory.FramedTriple.allocDirty_bind; on_goal 1 => try region_omega)
  | (eapply Cslib.DataStructure.Memory.FramedTriple.alloc_bind; on_goal 1 => try region_omega)
  | eapply Cslib.DataStructure.Memory.FramedTriple.pure (c := 0)
  | (eapply Cslib.DataStructure.Memory.FramedTriple.call_eq
     on_goal 1 => assumption
     on_goal 1 => first | exact subset_rfl | exact Set.empty_subset _ | try region_omega)
  | (eapply Cslib.DataStructure.Memory.FramedTriple.seq
     on_goal 1 => assumption
     on_goal 1 => first | exact subset_rfl | exact Set.empty_subset _ | try region_omega)
  | (eapply Cslib.DataStructure.Memory.FramedTriple.ite_max <;> intro)
  | (eapply Cslib.DataStructure.Memory.FramedTriple.dite_max <;> intro))

/-- Walk the `do` block of a `Memory.FramedTriple` goal with `framed_triple_step`. The cost is
synthesized and compared with the stated bound at the end by `omega`; side conditions are tried
with `region_omega`, trivial postconditions are closed, and the remaining goals are left to the
author in the order of the program. A sub-program call is taken through a triple for it in the
local context; a call whose continuation needs the sub-program's postcondition at an arbitrary
result is composed with `FramedTriple.call` by hand. -/
macro (name := framedTriple) "framed_triple" : tactic => `(tactic|
  (eapply Cslib.DataStructure.Memory.FramedTriple.mono (hQ := fun _ _ => id)
   on_goal 1 => (try dsimp only); repeat' framed_triple_step
   all_goals try first | omega | trivial))

end Cslib.WordRAM.Realization.FramedLoop
