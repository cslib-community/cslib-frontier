/-
Copyright (c) 2026 Sparsa Roychowdhury. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sparsa Roychowdhury
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Computability.Automata.Acceptors.Acceptor
public import Cslib.Foundations.Semantics.LTS.Basic

/-! # Multistack pushdown automata

A multistack pushdown automaton (MPDA) with `n` stacks is a finite control equipped with `n`
stacks over a common stack alphabet. Every transition carries an input symbol and performs at most
one stack operation: it either leaves all stacks untouched (`nop`), pushes a symbol onto one stack,
or pops a given symbol from the top of one stack.

Following the conventions of `NA`, an `MPDA` extends an `LTS` over its control states, whose labels
pair an input symbol with a stack operation. We do not impose any finiteness assumption. The
configuration semantics is itself an `LTS` (`MPDA.configLTS`), so that the generic `LTS` API for
multistep transitions applies directly to runs of the automaton.

A word is accepted when some run starts in an initial state with all stacks empty and ends in an
accepting state with all stacks empty, as in Section 2 of [AkshayGastinKrishnaRoychowdhury2020].
The paper has a single initial state; we allow a set of initial states, as `NA` does.

## Main definitions

- `MPDA.Op`: the stack operations of an MPDA.
- `MPDA.OpKind`, `MPDA.Op.kind`: the kind of a stack operation, forgetting the stack symbol.
- `MPDA`: multistack pushdown automata.
- `MPDA.Config`: configurations, consisting of a control state and the contents of all stacks.
- `MPDA.configLTS`: the transition system on configurations.
- An `Acceptor` instance for acceptance by final state and empty stacks.
- `MPDA.IsVisibly`: every transition on a letter performs the operation kind of that letter.

## Main results

- `MPDA.configLTS_mTr_state`: every run on configurations projects to a run of the control.
- `MPDA.IsVisibly.kind_eq`: every operation of a run of a visibly MPDA has the kind of its letter.
- `MPDA.exists_inv_pair_of_configLTS_mTr`: an invariant of two-stack configurations and the input
  read that every transition preserves holds along runs.

## References

* [S. Akshay, P. Gastin, S. Krishna, S. Roychowdhury,
  *Revisiting Underapproximate Reachability for Multipushdown Systems*]
  [AkshayGastinKrishnaRoychowdhury2020]
-/

public section

namespace Cslib.Automata

/-- The stack operations of a multistack pushdown automaton with `n` stacks over the stack
alphabet `Γ`. -/
inductive MPDA.Op (n : ℕ) (Γ : Type*) where
  /-- Leave all stacks unchanged. -/
  | nop
  /-- Push `γ` onto stack `i`. -/
  | push (i : Fin n) (γ : Γ)
  /-- Pop `γ` from the top of stack `i`. -/
  | pop (i : Fin n) (γ : Γ)
  deriving DecidableEq

/-- A multistack pushdown automaton with `n` stacks, control states `State`, input alphabet `Symbol`
and stack alphabet `Γ`. Its transition relation is an `LTS` over control states, whose labels pair
an input symbol with a stack operation. -/
structure MPDA (n : ℕ) (State Symbol Γ : Type*) extends LTS State (Symbol × MPDA.Op n Γ) where
  /-- The set of initial states. -/
  start : Set State
  /-- The set of accepting states. -/
  accept : Set State

namespace MPDA

variable {n : ℕ} {State Symbol Γ : Type*}

/-- The contents of `n` stacks. The head of each list is the top of the stack. -/
abbrev Stacks (n : ℕ) (Γ : Type*) := Fin n → List Γ

/-- All stacks are empty. -/
@[expose] def Stacks.empty : Stacks n Γ := fun _ => []

/-- `op.Apply σ σ'` holds when performing `op` on the stacks `σ` yields `σ'`. A pop of `γ` from
stack `i` is enabled only when `γ` is on top of stack `i`. -/
def Op.Apply : Op n Γ → Stacks n Γ → Stacks n Γ → Prop
  | .nop, σ, σ' => σ' = σ
  | .push i γ, σ, σ' => σ' = Function.update σ i (γ :: σ i)
  | .pop i γ, σ, σ' => σ = Function.update σ' i (γ :: σ' i)

@[simp]
theorem Op.apply_nop {σ σ' : Stacks n Γ} : (Op.nop : Op n Γ).Apply σ σ' ↔ σ' = σ := Iff.rfl

@[simp]
theorem Op.apply_push {i : Fin n} {γ : Γ} {σ σ' : Stacks n Γ} :
    (Op.push i γ).Apply σ σ' ↔ σ' = Function.update σ i (γ :: σ i) := Iff.rfl

@[simp]
theorem Op.apply_pop {i : Fin n} {γ : Γ} {σ σ' : Stacks n Γ} :
    (Op.pop i γ).Apply σ σ' ↔ σ = Function.update σ' i (γ :: σ' i) := Iff.rfl

/-! ### Two stacks -/

/-- Two stacks with contents `s₀` and `s₁`. -/
@[expose] def Stacks.pair (s₀ s₁ : List Γ) : Stacks 2 Γ := fun i => if i = 0 then s₀ else s₁

theorem Stacks.eq_pair_iff {σ : Stacks 2 Γ} {s₀ s₁ : List Γ} :
    σ = Stacks.pair s₀ s₁ ↔ σ 0 = s₀ ∧ σ 1 = s₁ := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h₀, h₁⟩
    funext i
    match i with
    | ⟨0, _⟩ => exact h₀
    | ⟨1, _⟩ => exact h₁

theorem Stacks.empty_eq_pair : (Stacks.empty : Stacks 2 Γ) = Stacks.pair [] [] :=
  Stacks.eq_pair_iff.mpr ⟨rfl, rfl⟩

theorem Op.apply_push_zero_pair {γ : Γ} {s₀ s₁ : List Γ} {σ : Stacks 2 Γ} :
    (Op.push 0 γ).Apply (Stacks.pair s₀ s₁) σ ↔ σ = Stacks.pair (γ :: s₀) s₁ := by
  rw [Op.apply_push, show Function.update (Stacks.pair s₀ s₁) 0 (γ :: Stacks.pair s₀ s₁ 0) =
    Stacks.pair (γ :: s₀) s₁ from Stacks.eq_pair_iff.mpr ⟨rfl, rfl⟩]

theorem Op.apply_push_one_pair {γ : Γ} {s₀ s₁ : List Γ} {σ : Stacks 2 Γ} :
    (Op.push 1 γ).Apply (Stacks.pair s₀ s₁) σ ↔ σ = Stacks.pair s₀ (γ :: s₁) := by
  rw [Op.apply_push, show Function.update (Stacks.pair s₀ s₁) 1 (γ :: Stacks.pair s₀ s₁ 1) =
    Stacks.pair s₀ (γ :: s₁) from Stacks.eq_pair_iff.mpr ⟨rfl, rfl⟩]

theorem Op.apply_pop_zero_pair {γ : Γ} {s₀ s₁ : List Γ} {σ : Stacks 2 Γ} :
    (Op.pop 0 γ).Apply (Stacks.pair s₀ s₁) σ ↔ ∃ t, s₀ = γ :: t ∧ σ = Stacks.pair t s₁ := by
  rw [Op.apply_pop]
  constructor
  · intro h
    exact ⟨σ 0, congrFun h 0, Stacks.eq_pair_iff.mpr ⟨rfl, (congrFun h 1).symm⟩⟩
  · rintro ⟨t, rfl, rfl⟩
    exact ((Stacks.eq_pair_iff (σ := Function.update (Stacks.pair t s₁) 0
      (γ :: Stacks.pair t s₁ 0))).mpr ⟨rfl, rfl⟩).symm

theorem Op.apply_pop_one_pair {γ : Γ} {s₀ s₁ : List Γ} {σ : Stacks 2 Γ} :
    (Op.pop 1 γ).Apply (Stacks.pair s₀ s₁) σ ↔ ∃ t, s₁ = γ :: t ∧ σ = Stacks.pair s₀ t := by
  rw [Op.apply_pop]
  constructor
  · intro h
    exact ⟨σ 1, congrFun h 1, Stacks.eq_pair_iff.mpr ⟨(congrFun h 0).symm, rfl⟩⟩
  · rintro ⟨t, rfl, rfl⟩
    exact ((Stacks.eq_pair_iff (σ := Function.update (Stacks.pair s₀ t) 1
      (γ :: Stacks.pair s₀ t 1))).mpr ⟨rfl, rfl⟩).symm

/-- The kind of a stack operation: a push on stack `i`, a pop from stack `i`, or no stack
operation. A visibly pushdown alphabet assigns a kind to each letter. -/
inductive OpKind (n : ℕ) where
  /-- A push on stack `i`. -/
  | push (i : Fin n)
  /-- A pop from stack `i`. -/
  | pop (i : Fin n)
  /-- No stack operation. -/
  | nop
  deriving DecidableEq

/-- The kind of an operation, forgetting its stack symbol. -/
@[expose, simp] def Op.kind : Op n Γ → OpKind n
  | .nop => .nop
  | .push i _ => .push i
  | .pop i _ => .pop i

theorem Op.kind_eq_push {op : Op n Γ} {i : Fin n} : op.kind = .push i ↔ ∃ γ, op = .push i γ := by
  cases op <;> simp

theorem Op.kind_eq_pop {op : Op n Γ} {i : Fin n} : op.kind = .pop i ↔ ∃ γ, op = .pop i γ := by
  cases op <;> simp

/-- A configuration of an MPDA: a control state and the contents of all stacks. -/
@[ext]
structure Config (n : ℕ) (State Γ : Type*) where
  /-- The control state. -/
  state : State
  /-- The contents of the stacks. -/
  contents : Stacks n Γ

/-- The transition system on configurations of an MPDA. A configuration `c` moves to `c'` with
label `μ` when the control moves along `μ` and the stack operation of `μ` turns the stacks of `c`
into those of `c'`. -/
def configLTS (M : MPDA n State Symbol Γ) : LTS (Config n State Γ) (Symbol × Op n Γ) where
  Tr c μ c' := M.Tr c.state μ c'.state ∧ μ.2.Apply c.contents c'.contents

@[simp]
theorem configLTS_tr {M : MPDA n State Symbol Γ} {c c' : Config n State Γ}
    {μ : Symbol × Op n Γ} :
    M.configLTS.Tr c μ c' ↔ M.Tr c.state μ c'.state ∧ μ.2.Apply c.contents c'.contents :=
  Iff.rfl

/-- Every run on configurations projects to a run of the control. -/
theorem configLTS_mTr_state {M : MPDA n State Symbol Γ} {c c' : Config n State Γ}
    {μs : List (Symbol × Op n Γ)} (h : M.configLTS.MTr c μs c') :
    M.MTr c.state μs c'.state := by
  induction h with
  | refl => exact .refl
  | stepL htr _ ih => exact .stepL (configLTS_tr.mp htr).1 ih

/-! ### Repeating a transition -/

section Repeat

variable {M : MPDA n State Symbol Γ} {q : State} {x : Symbol} {i : Fin n} {γ : Γ}

/-- Repeating `k` times a transition that pushes `γ` on stack `i` and stays in its state. -/
theorem configLTS_mTr_replicate_push (h : M.Tr q (x, .push i γ) q) :
    ∀ (k : ℕ) (σ : Stacks n Γ), M.configLTS.MTr ⟨q, σ⟩ (List.replicate k (x, .push i γ))
      ⟨q, Function.update σ i (List.replicate k γ ++ σ i)⟩
  | 0, σ => by simp
  | k + 1, σ => .stepL (configLTS_tr.mpr ⟨h, Op.apply_push.mpr rfl⟩) (by
      have := configLTS_mTr_replicate_push h k (Function.update σ i (γ :: σ i))
      rwa [Function.update_idem, Function.update_self, show List.replicate k γ ++ γ :: σ i =
        List.replicate (k + 1) γ ++ σ i by
          rw [List.replicate_succ', List.append_assoc, List.singleton_append]] at this)

/-- Repeating `k` times a transition that pops `γ` from stack `i` and stays in its state. -/
theorem configLTS_mTr_replicate_pop (h : M.Tr q (x, .pop i γ) q) :
    ∀ (k : ℕ) (σ : Stacks n Γ), M.configLTS.MTr ⟨q, Function.update σ i (List.replicate k γ ++ σ i)⟩
      (List.replicate k (x, .pop i γ)) ⟨q, σ⟩
  | 0, σ => by simp
  | k + 1, σ => .stepL (s2 := ⟨q, Function.update σ i (List.replicate k γ ++ σ i)⟩)
      (configLTS_tr.mpr ⟨h, Op.apply_pop.mpr (by
        change Function.update σ i (List.replicate (k + 1) γ ++ σ i) =
          Function.update (Function.update σ i (List.replicate k γ ++ σ i)) i
            (γ :: Function.update σ i (List.replicate k γ ++ σ i) i)
        rw [Function.update_self, Function.update_idem, List.replicate_succ, List.cons_append])⟩)
      (configLTS_mTr_replicate_pop h k σ)

end Repeat

/-! ### Repeating a transition on two stacks -/

section RepeatPair

variable {M : MPDA 2 State Symbol Γ} {q : State} {x : Symbol} {γ : Γ}

theorem configLTS_mTr_replicate_push_zero (h : M.Tr q (x, .push 0 γ) q) (s₁ : List Γ) (k : ℕ)
    (s₀ : List Γ) : M.configLTS.MTr ⟨q, Stacks.pair s₀ s₁⟩
      (List.replicate k (x, .push 0 γ)) ⟨q, Stacks.pair (List.replicate k γ ++ s₀) s₁⟩ := by
  convert configLTS_mTr_replicate_push h k (Stacks.pair s₀ s₁)
  symm; exact Stacks.eq_pair_iff.mpr ⟨rfl, rfl⟩

theorem configLTS_mTr_replicate_push_one (h : M.Tr q (x, .push 1 γ) q) (s₀ : List Γ) (k : ℕ)
    (s₁ : List Γ) : M.configLTS.MTr ⟨q, Stacks.pair s₀ s₁⟩
      (List.replicate k (x, .push 1 γ)) ⟨q, Stacks.pair s₀ (List.replicate k γ ++ s₁)⟩ := by
  convert configLTS_mTr_replicate_push h k (Stacks.pair s₀ s₁)
  symm; exact Stacks.eq_pair_iff.mpr ⟨rfl, rfl⟩

theorem configLTS_mTr_replicate_pop_zero (h : M.Tr q (x, .pop 0 γ) q) (s₁ : List Γ) (k : ℕ)
    (s₀ : List Γ) : M.configLTS.MTr ⟨q, Stacks.pair (List.replicate k γ ++ s₀) s₁⟩
      (List.replicate k (x, .pop 0 γ)) ⟨q, Stacks.pair s₀ s₁⟩ := by
  convert configLTS_mTr_replicate_pop h k (Stacks.pair s₀ s₁)
  symm; exact Stacks.eq_pair_iff.mpr ⟨rfl, rfl⟩

theorem configLTS_mTr_replicate_pop_one (h : M.Tr q (x, .pop 1 γ) q) (s₀ : List Γ) (k : ℕ)
    (s₁ : List Γ) : M.configLTS.MTr ⟨q, Stacks.pair s₀ (List.replicate k γ ++ s₁)⟩
      (List.replicate k (x, .pop 1 γ)) ⟨q, Stacks.pair s₀ s₁⟩ := by
  convert configLTS_mTr_replicate_pop h k (Stacks.pair s₀ s₁)
  symm; exact Stacks.eq_pair_iff.mpr ⟨rfl, rfl⟩

end RepeatPair

/-- An invariant of the control state, the contents of two stacks and the input read so far
that holds at the start of a run and is preserved by every transition holds at its end. -/
theorem exists_inv_pair_of_configLTS_mTr {M : MPDA 2 State Symbol Γ}
    (Inv : State → List Γ → List Γ → List Symbol → Prop)
    (hstep : ∀ {q q' : State} {s₀ s₁ : List Γ} {u : List Symbol} {μ : Symbol × Op 2 Γ}
      {σ : Stacks 2 Γ}, Inv q s₀ s₁ u → M.configLTS.Tr ⟨q, Stacks.pair s₀ s₁⟩ μ ⟨q', σ⟩ →
        ∃ t₀ t₁, σ = Stacks.pair t₀ t₁ ∧ Inv q' t₀ t₁ (u ++ [μ.1]))
    {q : State} {s₀ s₁ : List Γ} {μs : List (Symbol × Op 2 Γ)} {c : Config 2 State Γ}
    (h : M.configLTS.MTr ⟨q, Stacks.pair s₀ s₁⟩ μs c) (h₀ : Inv q s₀ s₁ []) :
    ∃ t₀ t₁, c.contents = Stacks.pair t₀ t₁ ∧ Inv c.state t₀ t₁ (μs.map Prod.fst) := by
  induction μs using List.reverseRecOn generalizing c with
  | nil =>
    obtain rfl := LTS.MTr.nil_eq _ h
    exact ⟨s₀, s₁, rfl, h₀⟩
  | append_singleton μs μ ih =>
    obtain ⟨⟨q', σ'⟩, h₁, h₂⟩ := LTS.MTr.split h
    obtain ⟨t₀, t₁, hc', hinv⟩ := ih h₁
    simp only at hc' hinv
    subst hc'
    obtain ⟨u₀, u₁, hσ, hinv'⟩ := hstep hinv ((LTS.MTr.singleton_iff _ _ _ _).mp h₂)
    exact ⟨u₀, u₁, hσ, by simpa using hinv'⟩

/-- An MPDA reads the letters visibly for `κ` if every transition on a letter `a` performs an
operation of kind `κ a`. -/
@[expose] def IsVisibly (M : MPDA n State Symbol Γ) (κ : Symbol → OpKind n) : Prop :=
  ∀ s a op s', M.Tr s (a, op) s' → op.kind = κ a

/-- Every operation of a run of a visibly MPDA has the kind of its letter. -/
theorem IsVisibly.kind_eq {M : MPDA n State Symbol Γ} {κ : Symbol → OpKind n}
    (hM : M.IsVisibly κ) {c c' : Config n State Γ} {w : List (Symbol × Op n Γ)}
    (h : M.configLTS.MTr c w c') : ∀ μ ∈ w, μ.2.kind = κ μ.1 := by
  induction h with
  | refl => simp
  | stepL htr _ ih =>
    intro μ hμ
    rcases List.mem_cons.mp hμ with rfl | hμ
    · exact hM _ _ _ _ (configLTS_tr.mp htr).1
    · exact ih μ hμ

/-- An MPDA accepts a word if it has a run labelled by that word that starts in an initial state
with all stacks empty and ends in an accepting state with all stacks empty. -/
@[simp, scoped grind =]
instance : Acceptor (MPDA n State Symbol Γ) Symbol where
  Accepts M xs := ∃ s ∈ M.start, ∃ s' ∈ M.accept, ∃ μs : List (Symbol × Op n Γ),
    μs.map Prod.fst = xs ∧ M.configLTS.MTr ⟨s, Stacks.empty⟩ μs ⟨s', Stacks.empty⟩

end MPDA

end Cslib.Automata
