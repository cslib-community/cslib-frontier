/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Algorithms.Lean.Query.FreeM

/-!
# Running a query program with its queries replaced by subprograms

For a handler `h` sending each query of the signature `F` to a program of `FreeM G`,
`p.liftM h : FreeM G α` runs `p` with each query replaced by its subprogram. Against an oracle
for `G`, it returns what `p` returns against the oracle answering each `F`-query by evaluating its
subprogram, and its cost is the cost of `p` with each query weighted by the cost of its
subprogram along that path. Embedding a program into a larger query signature
(`fun q => FreeM.lift (.inl q)`) and implementing an abstract query by a comparison program are
the two typical handlers.

## Main results

* `Cslib.FreeM.eval_liftM`: evaluation of `p.liftM h`.
* `Cslib.FreeM.cost_liftM`: the cost of `p.liftM h` is the cost of `p` with each query weighted by
  the cost of its subprogram.
-/

public section

namespace Cslib.FreeM

universe u v w t

variable {F : Type u → Type v} {G : Type u → Type w} {α : Type u}

/-- Evaluating `p.liftM h` against `oracle` evaluates `p` against the oracle that answers each
query by evaluating its subprogram. -/
theorem eval_liftM (oracle : {ι : Type u} → G ι → ι) (h : {ι : Type u} → F ι → FreeM G ι)
    (p : FreeM F α) : (p.liftM h).eval oracle = p.eval fun q => (h q).eval oracle := by
  induction p with
  | pure a => rfl
  | lift_bind op cont ih =>
    change ((FreeM.lift op >>= cont).liftM h).eval oracle =
      (FreeM.lift op >>= cont).eval fun q => (h q).eval oracle
    rw [liftM_lift_bind, eval_bind, ih, eval_liftBind]

/-- The cost of `p.liftM h` is the cost of `p` against the oracle answering each query by
evaluating its subprogram, with each query weighted by the cost of its subprogram. -/
theorem cost_liftM {T : Type t} [AddMonoid T] (oracle : {ι : Type u} → G ι → ι)
    (weight : {ι : Type u} → G ι → T) (h : {ι : Type u} → F ι → FreeM G ι) (p : FreeM F α) :
    (p.liftM h).cost oracle weight =
      p.cost (fun q => (h q).eval oracle) (fun q => (h q).cost oracle weight) := by
  induction p with
  | pure a => rfl
  | lift_bind op cont ih =>
    change ((FreeM.lift op >>= cont).liftM h).cost oracle weight =
      (FreeM.lift op >>= cont).cost (fun q => (h q).eval oracle) fun q => (h q).cost oracle weight
    rw [liftM_lift_bind, cost_bind, ih, cost_liftBind]

end Cslib.FreeM
