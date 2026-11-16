/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Devon Tuma
-/

module
-- upstream: submitted #1129 @dbe22c640c85b2e9fbcb2ec16cd3d14ccb37c4e8

public import Cslib.Foundations.Data.PFunctor.Free.Fold
public import CslibFrontier.Probability.PMF

/-!
# Probabilistic programs with oracles

`OracleComp spec α` is a terminating program with typed oracle calls described by the
specification `spec : OracleSpec ι`, which gives the response type `spec q` of each query `q : ι`.
A specification is the data of a polynomial functor, and programs are its `PFunctor.FreeM`.
Ordinary `do` notation applies when intermediate and result types share a universe; across
different universes, programs use the free monad's explicit heterogeneous `bind` and `map`. The
query, response, and result types may live in independent universes, and the program itself lives
in their maximum.

Randomness is not a separate effect. `unifSpec` is the interface answering `n` with a uniform
element of `Fin (n + 1)`, and `ProbComp` is `OracleComp unifSpec`. Any other distribution is
reached by evaluating an interface with that distribution, so the base language has no
primitive beyond uniform choice from a finite range.

`OracleComp.interpret` runs a program in an ordinary monad by answering each call with a handler,
when the responses and result share that monad's object universe. In that setting it can target
`PMF`, `StateT State m`, another `OracleComp`, or a writer monad; it is
`PFunctor.FreeM.liftM`, so it preserves sequencing, and interpretations compose.
`OracleComp.substitute` is the heterogeneous fold used for reductions into another `OracleComp`
when source responses, target responses, or the final result live in different universes. The
distribution semantics `evalWith` is likewise a heterogeneous PMF fold; raw state semantics is
defined in `Languages.Probabilistic.Semantics`.

Neither termination nor a bound on the number of queries asserts computational efficiency.
Computational efficiency requires a separate machine-realizability predicate. Unbounded loops and
nontermination are outside this language; bounded iteration uses Lean recursion.

## References

This is the design of Devon Tuma, Quang Dao, and collaborators'
[VCVio](https://github.com/Verified-zkEVM/VCVio): `OracleSpec`, `OracleComp`, and `unifSpec`
are their definitions, and `OracleComp.interpret` is their `simulateQ`.
-/

@[expose] public section

namespace Cslib

open Probability

universe u u' v v' w w' x

/-- An oracle specification: the response type of each query in `ι`. -/
abbrev OracleSpec (ι : Type u) := ι → Type v

/-- Terminating programs with typed oracle calls described by `spec`.

The result universe is independent of the query and response universes. -/
abbrev OracleComp {ι : Type u} (spec : OracleSpec.{u, v} ι) (α : Type w) :=
  (PFunctor.mk ι spec).FreeM α

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec.{u, v} ι}

/-- Make one oracle call. Later queries may depend on the answer. -/
def query (q : ι) : OracleComp spec (spec q) := PFunctor.FreeM.lift (P := ⟨ι, spec⟩) q

/-- Structural induction on an oracle program whose result and response types may live in
different universes, presenting sequencing with the heterogeneous free-monad bind. -/
@[elab_as_elim] theorem induction {α : Type w}
    {motive : OracleComp spec α → Prop}
    (pure : ∀ a, motive (pure a))
    (query_bind : ∀ q (cont : spec q → OracleComp spec α),
      (∀ a, motive (cont a)) → motive (PFunctor.FreeM.bind (query q) cont))
    (program : OracleComp spec α) : motive program := by
  induction program with
  | pure a => exact pure a
  | liftBind q cont ih => exact query_bind q cont ih

section Interpret

variable {α β State : Type v} {m : Type v → Type w} [Monad m]

/-- Run a program in the monad `m`, answering each oracle call with `oracle`.

Because Lean's ordinary `Monad` is an endofunctor on one universe, generic monadic interpretation
requires the response and result types in that universe. Universe-polymorphic semantics use the
heterogeneous fold operations instead. -/
def interpret (oracle : (q : ι) → m (spec q)) (program : OracleComp spec α) : m α :=
  program.liftM oracle

@[simp] theorem interpret_pure (oracle : (q : ι) → m (spec q)) (a : α) :
    interpret oracle (pure a) = pure a := rfl

variable [LawfulMonad m]

@[simp] theorem interpret_bind (oracle : (q : ι) → m (spec q))
    (program : OracleComp spec α) (next : α → OracleComp spec β) :
    interpret oracle (program >>= next) =
      interpret oracle program >>= fun a => interpret oracle (next a) :=
  PFunctor.FreeM.liftM_bind _ _ _

@[simp] theorem interpret_query (oracle : (q : ι) → m (spec q)) (q : ι) :
    interpret oracle (query q) = oracle q :=
  PFunctor.FreeM.liftM_lift _ _

@[simp] theorem interpret_map (oracle : (q : ι) → m (spec q)) (f : α → β)
    (program : OracleComp spec α) :
    interpret oracle (f <$> program) = f <$> interpret oracle program :=
  PFunctor.FreeM.liftM_map _ _ _

/-- Answering each call by itself leaves the program unchanged. -/
@[simp] theorem interpret_query_eq_self (program : OracleComp spec α) :
    interpret query program = program :=
  PFunctor.FreeM.liftM_lift_eq_self program

/-- Interpretations compose: interpreting a program whose calls were replaced by programs over
another interface is interpreting the original calls through the replacements. No fresh state is
introduced between calls. -/
theorem interpret_interpret {ι' : Type u'} {spec' : OracleSpec.{u', v} ι'}
    (handler : (q : ι) → OracleComp spec' (spec q)) (oracle : (q : ι') → m (spec' q))
    (program : OracleComp spec α) :
    interpret oracle (interpret handler program) =
      interpret (fun q => interpret oracle (handler q)) program :=
  PFunctor.FreeM.liftM_comp _ _ _

/-- An oracle may consult a fixed private environment without changing it. Its stateful execution
agrees with interpreting the program against that environment. -/
theorem run_interpret_readOnly (oracle : (q : ι) → State → m (spec q))
    (program : OracleComp spec α) (s : State) :
    (interpret (m := StateT State m) (fun q s => (fun a => (a, s)) <$> oracle q s) program).run s =
      (fun a => (a, s)) <$> interpret (fun q => oracle q s) program := by
  induction program using PFunctor.FreeM.induction generalizing s with
  | pure a => simp
  | lift_bind q cont ih =>
    change (interpret (m := StateT State m) _ (query q >>= cont)).run s =
      (fun a => (a, s)) <$> interpret _ (query q >>= cont)
    simp only [interpret_bind, interpret_query, StateT.run_bind]
    simp only [StateT.run, bind_map_left, map_bind]
    exact bind_congr fun a => ih a s

/-- Adding an untouched private state to a memoryless oracle does not change the result. -/
theorem run_interpret_stateless (oracle : (q : ι) → m (spec q))
    (program : OracleComp spec α) (s : State) :
    (interpret (m := StateT State m) (fun q s => (fun a => (a, s)) <$> oracle q) program).run s =
      (fun a => (a, s)) <$> interpret oracle program :=
  run_interpret_readOnly (fun q _ => oracle q) program s

end Interpret

/-! ### Oracle substitution -/

/-- Replace each call by a program over another oracle interface.

Unlike generic interpretation into an ordinary `Monad`, substitution uses the free monad's
heterogeneous bind, so the source responses, target responses, and final result may live in
independent universes. -/
def substitute {ι' : Type u'} {spec' : OracleSpec.{u', v'} ι'} {α : Type w}
    (handler : (q : ι) → OracleComp spec' (spec q))
    (program : OracleComp spec α) : OracleComp spec' α :=
  PFunctor.FreeM.foldFreeM pure
    (fun q cont => PFunctor.FreeM.bind (handler q) cont) program

/-- Substitution leaves a returned value unchanged. -/
@[simp] theorem substitute_pure {ι' : Type u'} {spec' : OracleSpec.{u', v'} ι'}
    (handler : (q : ι) → OracleComp spec' (spec q)) {α : Type w} (a : α) :
    substitute handler (pure a : OracleComp spec α) = pure a := rfl

/-- Substitution commutes with heterogeneous sequencing. -/
@[simp] theorem substitute_bind {ι' : Type u'} {spec' : OracleSpec.{u', v'} ι'}
    (handler : (q : ι) → OracleComp spec' (spec q)) {α : Type w} {β : Type w'}
    (program : OracleComp spec α) (next : α → OracleComp spec β) :
    substitute handler (PFunctor.FreeM.bind program next) =
      PFunctor.FreeM.bind (substitute handler program) fun a => substitute handler (next a) := by
  induction program with
  | pure a => rfl
  | liftBind q cont ih =>
    simp only [PFunctor.FreeM.bind, substitute, PFunctor.FreeM.foldFreeM,
      PFunctor.FreeM.bind_assoc]
    exact congrArg (PFunctor.FreeM.bind (handler q)) (funext ih)

/-- Substitution of a single query applies its handler. -/
@[simp] theorem substitute_query {ι' : Type u'} {spec' : OracleSpec.{u', v'} ι'}
    (handler : (q : ι) → OracleComp spec' (spec q)) (q : ι) :
    substitute handler (query (spec := spec) q) = handler q := by
  simp only [substitute, query, PFunctor.FreeM.lift, PFunctor.FreeM.foldFreeM,
    PFunctor.FreeM.foldFreeM_pure, PFunctor.FreeM.bind_pure]

/-- Substitution commutes with heterogeneous mapping. -/
@[simp] theorem substitute_map {ι' : Type u'} {spec' : OracleSpec.{u', v'} ι'}
    (handler : (q : ι) → OracleComp spec' (spec q)) {α : Type w} {β : Type w'}
    (f : α → β) (program : OracleComp spec α) :
    substitute handler (PFunctor.FreeM.map f program) =
      PFunctor.FreeM.map f (substitute handler program) := by
  rw [← PFunctor.FreeM.bind_pure_comp, substitute_bind]
  simp only [Function.comp_apply, substitute_pure]
  exact PFunctor.FreeM.bind_pure_comp f (substitute handler program)

/-- Replacing every query by itself leaves a program unchanged. -/
@[simp] theorem substitute_query_eq_self {α : Type w} (program : OracleComp spec α) :
    substitute query program = program := by
  induction program with
  | pure a => rfl
  | liftBind q cont ih =>
    change PFunctor.FreeM.bind (query q) (fun a => substitute query (cont a)) =
      PFunctor.FreeM.bind (query q) cont
    exact congrArg (PFunctor.FreeM.bind (query q)) (funext ih)

/-- Successive substitutions compose by substituting the second handler through the first. -/
theorem substitute_substitute {ι' : Type u'} {spec' : OracleSpec.{u', v'} ι'}
    {ι'' : Type x} {spec'' : OracleSpec.{x, w'} ι''} {α : Type w}
    (first : (q : ι) → OracleComp spec' (spec q))
    (second : (q : ι') → OracleComp spec'' (spec' q)) (program : OracleComp spec α) :
    substitute second (substitute first program) =
      substitute (fun q => substitute second (first q)) program := by
  induction program with
  | pure a => rfl
  | liftBind q cont ih =>
    change substitute second
        (PFunctor.FreeM.bind (first q) fun a => substitute first (cont a)) =
      PFunctor.FreeM.bind (substitute second (first q)) fun a =>
        substitute (fun q => substitute second (first q)) (cont a)
    rw [substitute_bind]
    exact congrArg (PFunctor.FreeM.bind (substitute second (first q))) (funext ih)

/-- On one object universe, substitution is the existing generic monadic interpretation into the
target free monad. -/
theorem substitute_eq_interpret {ι' : Type u'} {spec' : OracleSpec.{u', v'} ι'}
    (handler : (q : ι) → OracleComp spec' (spec q)) {γ : Type v}
    (program : OracleComp spec γ) : substitute handler program = interpret handler program := by
  induction program with
  | pure a => rfl
  | liftBind q cont ih =>
    change PFunctor.FreeM.bind (handler q) (fun a => substitute handler (cont a)) =
      PFunctor.FreeM.bind (handler q) (fun a => interpret handler (cont a))
    exact congrArg (PFunctor.FreeM.bind (handler q)) (funext ih)

/-! ### Distribution semantics -/

/-- The output distribution of `program` when each call `q` is answered by an independent sample
of `oracle q`. Unlike generic monadic interpretation, PMF bind relates different carrier
universes, so the result universe is independent of the response universe. -/
noncomputable def evalWith {α : Type w} (oracle : (q : ι) → PMF (spec q))
    (program : OracleComp spec α) : PMF α :=
  PFunctor.FreeM.foldFreeM PMF.pure (fun q cont => (oracle q).bind cont) program

/-- A returned value has a point distribution. -/
@[simp] theorem evalWith_pure {α : Type w} (oracle : (q : ι) → PMF (spec q)) (a : α) :
    evalWith oracle (pure a : OracleComp spec α) = PMF.pure a := rfl

/-- Evaluating a heterogeneous sequence binds the first output distribution to the continuation
semantics. -/
@[simp] theorem evalWith_freeMBind {α : Type w} {β : Type w'}
    (oracle : (q : ι) → PMF (spec q)) (program : OracleComp spec α)
    (next : α → OracleComp spec β) :
    evalWith oracle (PFunctor.FreeM.bind program next) =
      (evalWith oracle program).bind fun a => evalWith oracle (next a) := by
  induction program with
  | pure a =>
    change evalWith oracle (next a) = (PMF.pure a).bind fun a => evalWith oracle (next a)
    rw [PMF.pure_bind]
  | liftBind q cont ih =>
    simp only [PFunctor.FreeM.bind, evalWith, PFunctor.FreeM.foldFreeM, PMF.bind_bind]
    exact congrArg (PMF.bind (oracle q)) (funext ih)

/-- Evaluating an ordinary same-universe sequence binds the first output distribution to the
continuation semantics. -/
@[simp] theorem evalWith_bind {α β : Type w}
    (oracle : (q : ι) → PMF (spec q)) (program : OracleComp spec α)
    (next : α → OracleComp spec β) :
    evalWith oracle (program >>= next) =
      (evalWith oracle program).bind fun a => evalWith oracle (next a) := by
  simpa only [PFunctor.FreeM.bind_eq_bind] using evalWith_freeMBind oracle program next

/-- Heterogeneous postprocessing maps the output distribution. -/
@[simp] theorem evalWith_freeMMap {α : Type w} {β : Type w'}
    (oracle : (q : ι) → PMF (spec q))
    (f : α → β) (program : OracleComp spec α) :
    evalWith oracle (PFunctor.FreeM.map f program) = (evalWith oracle program).map f := by
  rw [← PFunctor.FreeM.bind_pure_comp, evalWith_freeMBind]
  rfl

/-- Ordinary same-universe postprocessing maps the output distribution. -/
@[simp] theorem evalWith_map {α β : Type w} (oracle : (q : ι) → PMF (spec q))
    (f : α → β) (program : OracleComp spec α) :
    evalWith oracle (f <$> program) = (evalWith oracle program).map f := by
  simpa only [PFunctor.FreeM.map_eq_map] using evalWith_freeMMap oracle f program

/-- A single call has the distribution of its answer. -/
@[simp] theorem evalWith_query (oracle : (q : ι) → PMF (spec q)) (q : ι) :
    evalWith oracle (query (spec := spec) q) = oracle q := by
  simp only [evalWith, query, PFunctor.FreeM.lift, PFunctor.FreeM.foldFreeM,
    PFunctor.FreeM.foldFreeM_pure, PMF.bind_pure]

/-- On one object universe, distribution semantics agrees with generic interpretation into
`PMF`. -/
theorem evalWith_eq_interpret (oracle : (q : ι) → PMF (spec q)) {γ : Type v}
    (program : OracleComp spec γ) : evalWith oracle program = interpret oracle program := by
  induction program using OracleComp.induction with
  | pure a => rfl
  | query_bind q cont ih =>
    rw [evalWith_freeMBind, evalWith_query]
    rw [PFunctor.FreeM.bind_eq_bind, interpret_bind, interpret_query,
      Probability.PMF.monad_bind_eq_bind]
    exact congrArg (PMF.bind (oracle q)) (funext ih)

end OracleComp

/-- The uniform sampling interface: the query `n` is answered by a uniform element of
`Fin (n + 1)`. -/
abbrev unifSpec : OracleSpec ℕ := fun n => Fin (n + 1)

/-- Probabilistic programs whose only randomness is uniform choice from a finite range. -/
abbrev ProbComp (α : Type w) := OracleComp unifSpec α

namespace ProbComp

variable {α : Type w} {β : Type w'}

/-- Draw a uniform element of `Fin (n + 1)`. -/
def unifFin (n : ℕ) : ProbComp (Fin (n + 1)) := OracleComp.query (spec := unifSpec) n

/-- Uniform sampling from a nonempty finite type, through an enumeration of it. -/
noncomputable def uniform (α : Type w) [Fintype α] [Nonempty α] : ProbComp α :=
  PFunctor.FreeM.map
    (fun i => (Fintype.equivFin α).symm (Fin.cast (Nat.sub_add_cancel Fintype.card_pos) i))
    (unifFin (Fintype.card α - 1))

/-- The oracle answering each query uniformly. -/
noncomputable def unifOracle (n : ℕ) : PMF (Fin (n + 1)) := PMF.uniformOfFintype (Fin (n + 1))

/-- The distribution denoted by a closed probabilistic program. -/
noncomputable def eval (program : ProbComp α) : PMF α :=
  OracleComp.evalWith unifOracle program

@[simp] theorem eval_pure (a : α) : eval (pure a) = PMF.pure a := rfl

@[simp] theorem eval_freeMBind (program : ProbComp α) (next : α → ProbComp β) :
    eval (PFunctor.FreeM.bind program next) =
      (eval program).bind (fun a => eval (next a)) := by
  exact OracleComp.evalWith_freeMBind _ _ _

@[simp] theorem eval_bind {α β : Type w} (program : ProbComp α) (next : α → ProbComp β) :
    eval (program >>= next) = (eval program).bind (fun a => eval (next a)) := by
  simpa only [PFunctor.FreeM.bind_eq_bind] using eval_freeMBind program next

@[simp] theorem eval_freeMMap (f : α → β) (program : ProbComp α) :
    eval (PFunctor.FreeM.map f program) = (eval program).map f := by
  exact OracleComp.evalWith_freeMMap _ _ _

@[simp] theorem eval_map {α β : Type w} (f : α → β) (program : ProbComp α) :
    eval (f <$> program) = (eval program).map f := by
  simpa only [PFunctor.FreeM.map_eq_map] using eval_freeMMap f program

@[simp] theorem eval_unifFin (n : ℕ) :
    eval (unifFin n) = PMF.uniformOfFintype (Fin (n + 1)) := by
  exact OracleComp.evalWith_query _ _

/-- Sampling through an enumeration is uniform on the type. -/
@[simp] theorem eval_uniform (α : Type w) [Fintype α] [Nonempty α] :
    eval (uniform α) = PMF.uniformOfFintype α := by
  rw [uniform, eval_freeMMap, eval_unifFin]
  exact PMF.uniformOfFintype_map_equiv
    ((finCongr (Nat.sub_add_cancel Fintype.card_pos)).trans (Fintype.equivFin α).symm)

end ProbComp

end Cslib
