/-
Copyright (c) 2026 Jesse Alama, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Foundations.Data.PFunctor.Free

/-!
# Stateless evaluation and query-count interpreters for `PFunctor.FreeM`

Pure evaluation (`PFunctor.FreeM.eval`) and structural query counting
(`PFunctor.FreeM.countQueries`) for programs in `PFunctor.FreeM` against a stateless dependent
oracle `(a : P.A) → P.B a`, without bumping the universe of `P.FreeM α` or importing `TimeM`.

## Main definitions

* `PFunctor.FreeM.eval`: evaluate a `P.FreeM α` computation by answering each shape `a : P.A`
  using `oracle a : P.B a`.
* `PFunctor.FreeM.countQueries`: count the `liftBind` queries executed along the oracle-determined
  path.

## Main results

* `PFunctor.FreeM.eval_pure`, `PFunctor.FreeM.eval_liftBind`, `PFunctor.FreeM.eval_lift`,
  `PFunctor.FreeM.eval_bind`, `PFunctor.FreeM.eval_map`: equational laws for `eval`.
* `PFunctor.FreeM.countQueries_pure`, `PFunctor.FreeM.countQueries_liftBind`,
  `PFunctor.FreeM.countQueries_lift`, `PFunctor.FreeM.countQueries_bind`,
  `PFunctor.FreeM.countQueries_map`: structural query-count composition laws.
-/

public section

universe uA uB u v

namespace PFunctor.FreeM

variable {P : PFunctor.{uA, uB}} {α : Type u} {β : Type v}

/-- Evaluate a `PFunctor.FreeM` computation by answering each query with `oracle`. -/
@[expose] def eval (oracle : (a : P.A) → P.B a) : P.FreeM α → α
  | .pure a => a
  | .liftBind q cont => eval oracle (cont (oracle q))

/-- Count the queries issued by a `PFunctor.FreeM` computation along the path determined by
`oracle`. -/
@[expose] def countQueries (oracle : (a : P.A) → P.B a) : P.FreeM α → ℕ
  | .pure _ => 0
  | .liftBind q cont => 1 + countQueries oracle (cont (oracle q))

@[simp] theorem eval_pure (oracle : (a : P.A) → P.B a) (x : α) :
    eval oracle (pure x : P.FreeM α) = x := rfl

theorem eval_liftBind (oracle : (a : P.A) → P.B a) (q : P.A) (cont : P.B q → P.FreeM α) :
    eval oracle (.liftBind q cont) = eval oracle (cont (oracle q)) := rfl

@[simp] theorem eval_lift (oracle : (a : P.A) → P.B a) (q : P.A) :
    eval oracle (lift (P := P) q) = oracle q := rfl

@[simp] theorem eval_bind {γ : Type u} (oracle : (a : P.A) → P.B a) (p : P.FreeM α)
    (f : α → P.FreeM γ) :
    eval oracle (p >>= f) = eval oracle (f (eval oracle p)) := by
  induction p using PFunctor.FreeM.recOn with
  | pure x => rfl
  | liftBind q cont ih => exact ih (oracle q)

@[simp] theorem eval_map {γ : Type u} (oracle : (a : P.A) → P.B a) (f : α → γ) (p : P.FreeM α) :
    eval oracle (f <$> p) = f (eval oracle p) := by
  induction p using PFunctor.FreeM.recOn with
  | pure x => rfl
  | liftBind q cont ih => exact ih (oracle q)

@[simp] theorem countQueries_pure (oracle : (a : P.A) → P.B a) (x : α) :
    countQueries oracle (pure x : P.FreeM α) = 0 := rfl

theorem countQueries_liftBind (oracle : (a : P.A) → P.B a) (q : P.A)
    (cont : P.B q → P.FreeM α) :
    countQueries oracle (.liftBind q cont) = 1 + countQueries oracle (cont (oracle q)) := rfl

@[simp] theorem countQueries_lift (oracle : (a : P.A) → P.B a) (q : P.A) :
    countQueries oracle (lift (P := P) q) = 1 := rfl

@[simp] theorem countQueries_bind {γ : Type u} (oracle : (a : P.A) → P.B a) (p : P.FreeM α)
    (f : α → P.FreeM γ) :
    countQueries oracle (p >>= f) =
      countQueries oracle p + countQueries oracle (f (eval oracle p)) := by
  induction p using PFunctor.FreeM.recOn with
  | pure x => simp only [← PFunctor.FreeM.bind_eq_bind,
      PFunctor.FreeM.bind, countQueries, eval, zero_add]
  | liftBind q cont ih =>
    change 1 + countQueries oracle (cont (oracle q) >>= f) =
      (1 + countQueries oracle (cont (oracle q))) +
        countQueries oracle (f (eval oracle (cont (oracle q))))
    rw [ih (oracle q), Nat.add_assoc]

@[simp] theorem countQueries_map {γ : Type u} (oracle : (a : P.A) → P.B a) (f : α → γ)
    (p : P.FreeM α) :
    countQueries oracle (f <$> p) = countQueries oracle p := by
  induction p using PFunctor.FreeM.recOn with
  | pure x => rfl
  | liftBind q cont ih =>
    change 1 + countQueries oracle (f <$> cont (oracle q)) =
      1 + countQueries oracle (cont (oracle q))
    rw [ih (oracle q)]

end PFunctor.FreeM
