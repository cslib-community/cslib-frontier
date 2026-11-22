/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.ProgTerm
import Mathlib.Data.List.GetD

/-!
# Composable program pieces

A piece of the simulator is a Lean function from argument terms to a term. Its
contract says that its meaning is a function of the meanings of its arguments,
in every environment that extends a fixed base environment of global values.
Arguments must be *stable*: their meaning does not change when the environment
is extended by binders. Variables bound below the extension point and closed
terms are stable, and stability is preserved by the non-binding combinators.

`foldAcc_eq` turns a fold whose body has a known step function into
`List.foldl`, and the remaining lemmas evaluate the modular folds as sums and
products in `ZMod p`.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.ProgTerm

open Term

variable (w : List Bool)

/-- The meaning of `t` does not change when `env` is extended by binders. -/
def StableAt (t : Term) (env : List ℕ) : Prop :=
  ∀ extra : List ℕ, t.denote w (extra ++ env) = t.denote w env

variable {w}

theorem StableAt.cons {t : Term} {env : List ℕ} (h : StableAt w t env) (x : ℕ) :
    t.denote w (x :: env) = t.denote w env := h [x]

theorem StableAt.cons₂ {t : Term} {env : List ℕ} (h : StableAt w t env) (x y : ℕ) :
    t.denote w (x :: y :: env) = t.denote w env := h [x, y]

theorem StableAt.extend {t : Term} {env : List ℕ} (h : StableAt w t env) (pre : List ℕ) :
    StableAt w t (pre ++ env) := fun extra => by rw [← List.append_assoc, h, h]

theorem stableAt_lvl {l : ℕ} {env : List ℕ} (hl : l < env.length) :
    StableAt w (lvl l) env := fun extra => by
  simp only [denote_lvl, List.length_append]
  rw [show extra.length + env.length - l - 1 = extra.length + (env.length - l - 1) by omega,
    List.getD_append_right]
  · simp
  · omega

theorem stableAt_const (k : ℕ) (env : List ℕ) : StableAt w (const k) env := fun _ => rfl

theorem StableAt.add {a b : Term} {env : List ℕ} (ha : StableAt w a env) (hb : StableAt w b env) :
    StableAt w (add a b) env := fun extra => by simp [ha extra, hb extra]
theorem StableAt.sub {a b : Term} {env : List ℕ} (ha : StableAt w a env) (hb : StableAt w b env) :
    StableAt w (sub a b) env := fun extra => by simp [ha extra, hb extra]
theorem StableAt.mul {a b : Term} {env : List ℕ} (ha : StableAt w a env) (hb : StableAt w b env) :
    StableAt w (mul a b) env := fun extra => by simp [ha extra, hb extra]
theorem StableAt.div {a b : Term} {env : List ℕ} (ha : StableAt w a env) (hb : StableAt w b env) :
    StableAt w (div a b) env := fun extra => by simp [ha extra, hb extra]
theorem StableAt.mod {a b : Term} {env : List ℕ} (ha : StableAt w a env) (hb : StableAt w b env) :
    StableAt w (mod a b) env := fun extra => by simp [ha extra, hb extra]
theorem StableAt.bit {a b : Term} {env : List ℕ} (ha : StableAt w a env) (hb : StableAt w b env) :
    StableAt w (bit a b) env := fun extra => by simp [ha extra, hb extra]
theorem StableAt.lt {a b : Term} {env : List ℕ} (ha : StableAt w a env) (hb : StableAt w b env) :
    StableAt w (lt a b) env := fun extra => by simp [ha extra, hb extra]
theorem StableAt.input {a : Term} {env : List ℕ} (ha : StableAt w a env) :
    StableAt w (input a) env := fun extra => by simp [ha extra]
theorem StableAt.ite {c a b : Term} {env : List ℕ} (hc : StableAt w c env)
    (ha : StableAt w a env) (hb : StableAt w b env) :
    StableAt w (ite c a b) env := fun extra => by simp [hc extra, ha extra, hb extra]

/-! ### Folds with a known step -/

/-- A fold whose body has step function `step` is `List.foldl step`. -/
theorem foldAcc_eq (f : Term → Term → Term) (env : List ℕ) (step : ℕ → ℕ → ℕ)
    (hstep : ∀ acc k, (f (lvl (env.length + 1)) (lvl env.length)).denote w (acc :: k :: env) =
      step acc k) (init n : ℕ) :
    foldAcc w f env init n = (List.range n).foldl step init := by
  unfold foldAcc
  congr 1
  funext acc k
  exact hstep acc k

theorem foldl_sumMod (P : ℕ) (g : ℕ → ℕ) (n init : ℕ) :
    (List.range n).foldl (fun acc k => (acc + g k) % P) init =
      (init + ∑ k ∈ Finset.range n, g k) % P ∨ n = 0 := by
  induction n generalizing init with
  | zero => right; rfl
  | succ n ih =>
    left
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Finset.sum_range_succ]
    rcases ih init with h | h
    · rw [h, Nat.mod_add_mod, Nat.add_assoc]
    · subst h; simp

/-- A modular-sum fold from `0` computes the residue of the sum. -/
theorem foldl_sumMod_zero (P : ℕ) (g : ℕ → ℕ) (n : ℕ) :
    (((List.range n).foldl (fun acc k : ℕ => (acc + g k) % P) 0 : ℕ) : ZMod P) =
      ∑ k ∈ Finset.range n, (g k : ZMod P) := by
  rcases foldl_sumMod P g n 0 with h | h
  · rw [h, Nat.zero_add, ZMod.natCast_mod, Nat.cast_sum]
  · subst h; simp

/-- A modular-product fold from `1` computes the residue of the product. -/
theorem foldl_prodMod_one (P : ℕ) (g : ℕ → ℕ) (n : ℕ) :
    (((List.range n).foldl (fun acc k : ℕ => (acc * g k) % P) 1 : ℕ) : ZMod P) =
      ∏ k ∈ Finset.range n, (g k : ZMod P) := by
  suffices ∀ init : ℕ, (((List.range n).foldl (fun acc k : ℕ => (acc * g k) % P) init : ℕ) : ZMod P)
      =
      (init : ZMod P) * ∏ k ∈ Finset.range n, (g k : ZMod P) by simpa using this 1
  induction n with
  | zero => intro init; simp
  | succ n ih =>
    intro init
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Finset.prod_range_succ, ZMod.natCast_mod, Nat.cast_mul, ih, mul_assoc]

/-! ### Loop variables and generic loops -/

@[simp] theorem denote_lvl_let (env : List ℕ) (x : ℕ) :
    (lvl env.length).denote w (x :: env) = x := by simp [denote_lvl]

@[simp] theorem denote_lvl_index (env : List ℕ) (acc k : ℕ) :
    (lvl env.length).denote w (acc :: k :: env) = k := by
  simp [denote_lvl, Nat.add_assoc, Nat.add_sub_cancel_left]

@[simp] theorem denote_lvl_acc (env : List ℕ) (acc k : ℕ) :
    (lvl (env.length + 1)).denote w (acc :: k :: env) = acc := by
  simp [denote_lvl, Nat.add_assoc, Nat.add_sub_add_left]

theorem foldl_add_sum (g : ℕ → ℕ) (n init : ℕ) :
    (List.range n).foldl (fun acc k => acc + g k) init = init + ∑ k ∈ Finset.range n, g k := by
  induction n generalizing init with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih,
      Finset.sum_range_succ, Nat.add_assoc]

/-- A plain sum over `k < n`. -/
def sumT (n : Term) (body : Term → Term) : Term :=
  foldT n (const 0) fun acc i => add acc (body i)

theorem denote_sumT (n : Term) (body : Term → Term) (env : List ℕ) (c : ℕ → ℕ)
    (hb : ∀ acc k, (body (lvl env.length)).denote w (acc :: k :: env) = c k) :
    (sumT n body).denote w env = ∑ k ∈ Finset.range (n.denote w env), c k := by
  simp only [sumT, denote_foldT, denote_const]
  rw [foldAcc_eq _ env (fun acc k => acc + c k) (fun acc k => by simp [hb]), foldl_add_sum,
    Nat.zero_add]

/-- A modular sum over `k < n`. -/
theorem denote_sumMod (p n : Term) (body : Term → Term) (env : List ℕ) (P : ℕ) (c : ℕ → ℕ)
    (hp : StableAt w p env) (hpv : p.denote w env = P)
    (hb : ∀ acc k, (body (lvl env.length)).denote w (acc :: k :: env) = c k) :
    (Term.sumMod p n body).denote w env = (∑ k ∈ Finset.range (n.denote w env), c k) % P := by
  simp only [Term.sumMod, denote_foldT, denote_const]
  rw [foldAcc_eq _ env (fun acc k => (acc + c k) % P) (fun acc k => by
    simp [hb, hp.cons₂, hpv])]
  rcases foldl_sumMod P c (n.denote w env) 0 with h | h
  · rw [h, Nat.zero_add]
  · rw [h]; simp

/-- A modular product over `k < n`, as a residue. -/
theorem denote_prodMod (p n : Term) (body : Term → Term) (env : List ℕ) (P : ℕ) (c : ℕ → ℕ)
    (hp : StableAt w p env) (hpv : p.denote w env = P)
    (hb : ∀ acc k, (body (lvl env.length)).denote w (acc :: k :: env) = c k) :
    ((Term.prodMod p n body).denote w env : ZMod P) =
      ∏ k ∈ Finset.range (n.denote w env), (c k : ZMod P) := by
  simp only [Term.prodMod, denote_foldT, denote_const]
  rw [foldAcc_eq _ env (fun acc k => (acc * c k) % P) (fun acc k => by
    simp [hb, hp.cons₂, hpv]), foldl_prodMod_one]

/-- A modular product, at the residue level: the body need only be congruent to
`c k` modulo `P`, for every accumulator and every `k` below the bound. -/
theorem denote_prodModZ (p n : Term) (body : Term → Term) (env : List ℕ) (P : ℕ)
    (c : ℕ → ZMod P) (hp : StableAt w p env) (hpv : p.denote w env = P)
    (hb : ∀ acc k, k < n.denote w env →
      ((body (lvl env.length)).denote w (acc :: k :: env) : ZMod P) = c k) :
    ((Term.prodMod p n body).denote w env : ZMod P) =
      ∏ k ∈ Finset.range (n.denote w env), c k := by
  simp only [Term.prodMod, denote_foldT, denote_const]
  have key : ∀ m, m ≤ n.denote w env →
      ((foldAcc w (fun acc i => mod (mul acc (body i)) p) env 1 m : ℕ) : ZMod P) =
        ∏ k ∈ Finset.range m, c k := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      rw [foldAcc_succ, Finset.prod_range_succ, ← ih (by omega)]
      simp only [denote_mod, denote_mul, denote_lvl_acc, hp.cons₂, hpv, ZMod.natCast_mod,
        Nat.cast_mul, hb _ m (by omega)]
  exact key _ le_rfl

/-- A modular sum, at the residue level. -/
theorem denote_sumModZ (p n : Term) (body : Term → Term) (env : List ℕ) (P : ℕ)
    (c : ℕ → ZMod P) (hp : StableAt w p env) (hpv : p.denote w env = P)
    (hb : ∀ acc k, k < n.denote w env →
      ((body (lvl env.length)).denote w (acc :: k :: env) : ZMod P) = c k) :
    ((Term.sumMod p n body).denote w env : ZMod P) =
      ∑ k ∈ Finset.range (n.denote w env), c k := by
  simp only [Term.sumMod, denote_foldT, denote_const]
  have key : ∀ m, m ≤ n.denote w env →
      ((foldAcc w (fun acc i => mod (add acc (body i)) p) env 0 m : ℕ) : ZMod P) =
        ∑ k ∈ Finset.range m, c k := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      rw [foldAcc_succ, Finset.sum_range_succ, ← ih (by omega)]
      simp only [denote_mod, denote_add, denote_lvl_acc, hp.cons₂, hpv, ZMod.natCast_mod,
        Nat.cast_add, hb _ m (by omega)]
  exact key _ le_rfl

end Cslib.Complexity.NtimeDspace.ProgTerm
