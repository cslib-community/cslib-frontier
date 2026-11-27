/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init

/-!
# `StateT` programs applied to a state

A `StateT σ m α` program is a function `σ → m (α × σ)`, and handlers are often written and
reasoned about as applications `x s` rather than through `StateT.run`. Lean's `StateT.run_bind`,
`StateT.run_map` and `StateT.run_pure` are stated with `.run`, so `rw` cannot use them on such
applications. This file restates them for the applied form.

## Rewrite interface

* `Cslib.StateT.bind_apply`, `Cslib.StateT.map_apply`, `Cslib.StateT.pure_apply`: the applied
  forms of `StateT.run_bind`, `StateT.run_map` and `StateT.run_pure`.
-/

public section

namespace Cslib

universe u v

variable {m : Type u → Type v} {σ α β : Type u}

/-- `StateT.run_bind` for a program applied directly to its initial state. -/
theorem StateT.bind_apply [Monad m] (x : StateT σ m α) (f : α → StateT σ m β) (s : σ) :
    (x >>= f) s = x s >>= fun p => f p.1 p.2 :=
  StateT.run_bind x f s

/-- `StateT.run_map` for a program applied directly to its initial state. -/
theorem StateT.map_apply [Monad m] [LawfulMonad m] (f : α → β) (x : StateT σ m α) (s : σ) :
    (f <$> x) s = (fun p => (f p.1, p.2)) <$> x s :=
  StateT.run_map f x s

/-- `StateT.run_pure` for a program applied directly to its initial state. -/
theorem StateT.pure_apply [Monad m] (a : α) (s : σ) : (pure a : StateT σ m α) s = pure (a, s) :=
  rfl

end Cslib
