/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Basic

/-!
# Sums of oracle interfaces

A program may call two interfaces at once: a query of `spec₁ ⊕ₒ spec₂` is a query of either,
answered as there. A program with private coins is the main instance (`probOracleSpec`), with
uniform sampling on the left; a forger calling a signer and a hash function, and the prover and
verifier oracles of an interactive protocol, are others.

`OracleComp.sumHandler left right` answers the two kinds of call with handlers in the same monad,
and `OracleComp.liftLeft` and `OracleComp.liftRight` embed a program over one side. Interpreting
an embedded program uses only the corresponding handler (`interpret_sumHandler_liftLeft`).

## Main definitions

* `Cslib.OracleSpec.sum`, notation `spec₁ ⊕ₒ spec₂`: the disjoint sum of two interfaces.
* `Cslib.OracleSpec.empty`: the interface without queries.
* `Cslib.OracleComp.sumHandler`: answer the two sides with separate handlers.
* `Cslib.OracleComp.liftLeft`, `Cslib.OracleComp.liftRight`: embed a program over one side.

## Main results

* `Cslib.OracleComp.interpret_sumHandler_liftLeft`,
  `Cslib.OracleComp.interpret_sumHandler_liftRight`: an embedded program uses only its own side's
  handler.
* `Cslib.OracleComp.interpret_sumHandler`: interpretation distributes over the two sides.
* `Cslib.OracleComp.liftLeft_freeMBind`, `.liftRight_freeMBind`, `.liftLeft_freeMMap`, and
  `.liftRight_freeMMap`: embedding commutes with heterogeneous sequencing and mapping. The
  corresponding shorter `*_bind` and `*_map` names are the ordinary same-universe forms.

## References

* For the underlying oracle-program design, see the
  [VCVio](https://github.com/Verified-zkEVM/VCVio) credit in `Languages.Probabilistic.Basic`.
-/

@[expose] public section

namespace Cslib

universe u₁ u₂ u₃ v w w' x

/-- The disjoint sum of two interfaces: a query of either, answered as there.

The query types may live in independent universes. The response types share one universe because
Lean does not coerce type terms into a maximum universe without changing their carriers. -/
abbrev OracleSpec.sum {ι₁ : Type u₁} {ι₂ : Type u₂} (spec₁ : OracleSpec.{u₁, v} ι₁)
    (spec₂ : OracleSpec.{u₂, v} ι₂) : OracleSpec.{max u₁ u₂, v} (ι₁ ⊕ ι₂)
  | .inl q => spec₁ q
  | .inr q => spec₂ q

@[inherit_doc] scoped infixr:65 " ⊕ₒ " => OracleSpec.sum

/-- The interface without queries, for a party that uses no oracle. -/
abbrev OracleSpec.empty : OracleSpec.{0, v} Empty := fun q => q.elim

namespace OracleComp

section Handler

variable {ι₁ : Type u₁} {ι₂ : Type u₂} {spec₁ : OracleSpec.{u₁, v} ι₁}
  {spec₂ : OracleSpec.{u₂, v} ι₂}

/-- Answer the calls of the left interface with `left` and those of the right with `right`. -/
abbrev sumHandler {m : Type v → Type x} (left : (q : ι₁) → m (spec₁ q))
    (right : (q : ι₂) → m (spec₂ q)) : (q : ι₁ ⊕ ι₂) → m ((spec₁ ⊕ₒ spec₂) q)
  | .inl q => left q
  | .inr q => right q

/-- `sumHandler` answers a left query `.inl q` with `left q`. -/
theorem sumHandler_inl {m : Type v → Type x} (left : (q : ι₁) → m (spec₁ q))
    (right : (q : ι₂) → m (spec₂ q)) (q : ι₁) : sumHandler left right (.inl q) = left q := rfl

/-- `sumHandler` answers a right query `.inr q` with `right q`. -/
theorem sumHandler_inr {m : Type v → Type x} (left : (q : ι₁) → m (spec₁ q))
    (right : (q : ι₂) → m (spec₂ q)) (q : ι₂) : sumHandler left right (.inr q) = right q := rfl

end Handler

section Lift

variable {ι₁ : Type u₁} {ι₂ : Type u₂} {spec₁ : OracleSpec.{u₁, v} ι₁}
  {spec₂ : OracleSpec.{u₂, v} ι₂} {α : Type w} {β : Type w'}

/-- A program over the left interface, as a program over the sum. -/
def liftLeft (program : OracleComp spec₁ α) : OracleComp (spec₁ ⊕ₒ spec₂) α :=
  substitute (fun q => query (spec := spec₁ ⊕ₒ spec₂) (.inl q)) program

/-- A program over the right interface, as a program over the sum. -/
def liftRight (program : OracleComp spec₂ α) : OracleComp (spec₁ ⊕ₒ spec₂) α :=
  substitute (fun q => query (spec := spec₁ ⊕ₒ spec₂) (.inr q)) program

/-- Lifting `pure a` from the left interface yields `pure a`. -/
@[simp] theorem liftLeft_pure (a : α) :
    liftLeft (spec₂ := spec₂) (pure a : OracleComp spec₁ α) = pure a := rfl

/-- Lifting `pure a` from the right interface yields `pure a`. -/
@[simp] theorem liftRight_pure (a : α) :
    liftRight (spec₁ := spec₁) (pure a : OracleComp spec₂ α) = pure a := rfl

/-- `liftLeft` commutes with heterogeneous free-monad bind. -/
@[simp] theorem liftLeft_freeMBind (program : OracleComp spec₁ α)
    (next : α → OracleComp spec₁ β) :
    liftLeft (spec₂ := spec₂) (PFunctor.FreeM.bind program next) =
      PFunctor.FreeM.bind (liftLeft program) fun a => liftLeft (next a) :=
  substitute_bind _ _ _

/-- `liftLeft` commutes with ordinary same-universe monadic bind `>>=`. -/
@[simp] theorem liftLeft_bind {α β : Type w} (program : OracleComp spec₁ α)
    (next : α → OracleComp spec₁ β) :
    liftLeft (spec₂ := spec₂) (program >>= next) =
      liftLeft program >>= fun a => liftLeft (next a) := by
  simpa only [PFunctor.FreeM.bind_eq_bind] using liftLeft_freeMBind program next

/-- `liftRight` commutes with heterogeneous free-monad bind. -/
@[simp] theorem liftRight_freeMBind (program : OracleComp spec₂ α)
    (next : α → OracleComp spec₂ β) :
    liftRight (spec₁ := spec₁) (PFunctor.FreeM.bind program next) =
      PFunctor.FreeM.bind (liftRight program) fun a => liftRight (next a) :=
  substitute_bind _ _ _

/-- `liftRight` commutes with ordinary same-universe monadic bind `>>=`. -/
@[simp] theorem liftRight_bind {α β : Type w} (program : OracleComp spec₂ α)
    (next : α → OracleComp spec₂ β) :
    liftRight (spec₁ := spec₁) (program >>= next) =
      liftRight program >>= fun a => liftRight (next a) := by
  simpa only [PFunctor.FreeM.bind_eq_bind] using liftRight_freeMBind program next

/-- `liftLeft` commutes with heterogeneous free-monad map. -/
@[simp] theorem liftLeft_freeMMap (f : α → β) (program : OracleComp spec₁ α) :
    liftLeft (spec₂ := spec₂) (PFunctor.FreeM.map f program) =
      PFunctor.FreeM.map f (liftLeft program) :=
  substitute_map _ _ _

/-- `liftLeft` commutes with ordinary same-universe functorial map `<$>`. -/
@[simp] theorem liftLeft_map {α β : Type w} (f : α → β) (program : OracleComp spec₁ α) :
    liftLeft (spec₂ := spec₂) (f <$> program) = f <$> liftLeft program := by
  simpa only [PFunctor.FreeM.map_eq_map] using liftLeft_freeMMap f program

/-- `liftRight` commutes with heterogeneous free-monad map. -/
@[simp] theorem liftRight_freeMMap (f : α → β) (program : OracleComp spec₂ α) :
    liftRight (spec₁ := spec₁) (PFunctor.FreeM.map f program) =
      PFunctor.FreeM.map f (liftRight program) :=
  substitute_map _ _ _

/-- `liftRight` commutes with ordinary same-universe functorial map `<$>`. -/
@[simp] theorem liftRight_map {α β : Type w} (f : α → β) (program : OracleComp spec₂ α) :
    liftRight (spec₁ := spec₁) (f <$> program) = f <$> liftRight program := by
  simpa only [PFunctor.FreeM.map_eq_map] using liftRight_freeMMap f program

/-- Lifting a single query `query q` from the left interface produces `query (.inl q)`. -/
@[simp] theorem liftLeft_query (q : ι₁) :
    liftLeft (spec₂ := spec₂) (query q) = query (spec := spec₁ ⊕ₒ spec₂) (.inl q) :=
  substitute_query _ _

/-- Lifting a single query `query q` from the right interface produces `query (.inr q)`. -/
@[simp] theorem liftRight_query (q : ι₂) :
    liftRight (spec₁ := spec₁) (query q) = query (spec := spec₁ ⊕ₒ spec₂) (.inr q) :=
  substitute_query _ _

end Lift

section HandlerSemantics

variable {ι₁ : Type u₁} {ι₂ : Type u₂} {spec₁ : OracleSpec.{u₁, v} ι₁}
  {spec₂ : OracleSpec.{u₂, v} ι₂} {α : Type w}

variable {m : Type v → Type x} [Monad m] [LawfulMonad m]

/-- An embedded left program uses only the left handler. -/
@[simp] theorem interpret_sumHandler_liftLeft (left : (q : ι₁) → m (spec₁ q))
    (right : (q : ι₂) → m (spec₂ q)) {γ : Type v} (program : OracleComp spec₁ γ) :
    interpret (sumHandler left right) (liftLeft program) = interpret left program := by
  induction program with
  | pure a => rfl
  | liftBind q cont ih =>
    change interpret (sumHandler left right)
        (PFunctor.FreeM.bind (query (Sum.inl q)) fun a => liftLeft (cont a)) =
      interpret left (PFunctor.FreeM.bind (query q) cont)
    simp only [PFunctor.FreeM.bind_eq_bind, interpret_bind, interpret_query, ih]

/-- An embedded right program uses only the right handler. -/
@[simp] theorem interpret_sumHandler_liftRight (left : (q : ι₁) → m (spec₁ q))
    (right : (q : ι₂) → m (spec₂ q)) {γ : Type v} (program : OracleComp spec₂ γ) :
    interpret (sumHandler left right) (liftRight program) = interpret right program := by
  induction program with
  | pure a => rfl
  | liftBind q cont ih =>
    change interpret (sumHandler left right)
        (PFunctor.FreeM.bind (query (Sum.inr q)) fun a => liftRight (cont a)) =
      interpret right (PFunctor.FreeM.bind (query q) cont)
    simp only [PFunctor.FreeM.bind_eq_bind, interpret_bind, interpret_query, ih]

omit [LawfulMonad m] in
/-- Interpretation distributes over the two sides of a combined handler. -/
theorem interpret_sumHandler {κ : Type u₃} {target : OracleSpec.{u₃, v} κ}
    (oracle : (q : κ) → m (target q)) (left : (q : ι₁) → OracleComp target (spec₁ q))
    (right : (q : ι₂) → OracleComp target (spec₂ q)) :
    (fun q => interpret oracle (sumHandler left right q)) =
      sumHandler (fun q => interpret oracle (left q)) (fun q => interpret oracle (right q)) := by
  funext q
  cases q <;> rfl

end HandlerSemantics

end OracleComp

end Cslib
