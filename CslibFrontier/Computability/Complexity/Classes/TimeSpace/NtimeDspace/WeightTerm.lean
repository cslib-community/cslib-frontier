/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.CounterLocal
public import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# The Hermite weight as a term

The running weight multiplies separately truncated reciprocal factors. Each
factor is evaluated by a scalar Horner loop with a cached inverse and one
modular accumulator; no degree tuple is enumerated by `weightT`. Projection correctness requires the
flat-weight no-alias bound.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.ProgTerm

open Term

variable {w : List Bool}

/-- `x ^ e` exactly. -/
def powT (x e : Term) : Term := foldT e (const 1) fun acc _ => mul acc x

theorem powT_denote (x e : Term) (env : List ℕ) (hx : StableAt w x env) :
    (powT x e).denote w env = x.denote w env ^ e.denote w env := by
  simp only [powT, denote_foldT, denote_const]
  rw [foldAcc_eq _ env (fun acc _ => acc * x.denote w env) (fun acc k => by
    simp [hx.cons₂])]
  induction e.denote w env with
  | zero => rfl
  | succ m ih => rw [List.range_succ, List.foldl_append, ih]; simp [pow_succ]

theorem StableAt.powT {x e : Term} {env : List ℕ} (hx : StableAt w x env)
    (he : StableAt w e env) : StableAt w (powT x e) env := fun extra => by
  rw [powT_denote x e _ (hx.extend extra), powT_denote x e env hx, hx extra, he extra]

/-- `T / x^i`, by dividing `i` times; every value is at most `T`. -/
def divPowT (x T i : Term) : Term := foldT i T fun acc _ => div acc x

theorem divPowT_denote (x T i : Term) (env : List ℕ) (hx : StableAt w x env) :
    (divPowT x T i).denote w env = T.denote w env / x.denote w env ^ i.denote w env := by
  simp only [divPowT, denote_foldT]
  rw [foldAcc_eq _ env (fun acc _ => acc / x.denote w env) (fun acc k => by simp [hx.cons₂])]
  induction i.denote w env with
  | zero => simp
  | succ m
      ih => rw [List.range_succ, List.foldl_append, ih]; simp [pow_succ, Nat.div_div_eq_div_mul]

/-- The digit `T / x^i % x`. -/
def digitT (x T i : Term) : Term := mod (divPowT x T i) x

theorem digitT_denote (x T i : Term) (env : List ℕ) (hx : StableAt w x env) :
    (digitT x T i).denote w env =
      T.denote w env / x.denote w env ^ i.denote w env % x.denote w env := by
  simp [digitT, divPowT_denote x T i env hx]

theorem StableAt.digitT {x T i : Term} {env : List ℕ} (hx : StableAt w x env)
    (hT : StableAt w T env) (hi : StableAt w i env) : StableAt w (digitT x T i) env :=
  fun extra => by
    rw [digitT_denote x T i _ (hx.extend extra), digitT_denote x T i env hx, hx extra, hT extra,
      hi extra]

/-- A scalar fold reducing its accumulator modulo `p` after every step. -/
def foldModT (p n : Term) (body : Term → Term → Term) : Term :=
  foldT n (const 0) fun acc i => mod (body acc i) p

theorem foldModT_denote (p n : Term) (body : Term → Term → Term) (env : List ℕ)
    (P : ℕ) (step : ZMod P → ℕ → ZMod P)
    (hp : StableAt w p env) (hpv : p.denote w env = P)
    (hb : ∀ acc i,
      ((body (lvl (env.length + 1)) (lvl env.length)).denote w (acc :: i :: env) : ZMod P) =
        step acc i) :
    ((foldModT p n body).denote w env : ZMod P) =
      (List.range (n.denote w env)).foldl step 0 := by
  simp only [foldModT, denote_foldT, denote_const]
  generalize n.denote w env = count
  induction count with
  | zero => simp
  | succ count ih =>
    rw [foldAcc_succ, List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, denote_mod, hp.cons₂, hpv,
      ZMod.natCast_mod, hb, ih]

end Cslib.Complexity.NtimeDspace.ProgTerm
