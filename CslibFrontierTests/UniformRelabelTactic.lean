/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of relabel_uniform and drop_uniform)

public import CslibFrontier.Tactic.UniformRelabel
public import Mathlib.Data.ZMod.Basic

/-! # Tests for `relabel_uniform` and `drop_uniform` -/

public section

namespace CslibFrontierTests.UniformRelabelTactic
open Cslib.Probability

example {q : ℕ} [NeZero q] (c : ZMod q) {γ : Type*} (k : ZMod q → PMF γ) :
    (PMF.uniformOfFintype (ZMod q)).bind (fun x => k (x + c)) =
      (PMF.uniformOfFintype (ZMod q)).bind k := by relabel_uniform (Equiv.addRight c)
example {q : ℕ} [NeZero q] (c : ZMod q) {γ : Type*} (k : ZMod q → PMF γ) :
    (PMF.uniformOfFintype (ZMod q)).bind k =
      (PMF.uniformOfFintype (ZMod q)).bind (fun x => k (c + x)) := by
  relabel_uniform (fun x => c + x)
example {q : ℕ} [NeZero q] (c : ZMod q) : (PMF.uniformOfFintype (ZMod q)).map (c - ·) =
    PMF.uniformOfFintype (ZMod q) := by relabel_uniform (fun x => c - x)
example {q : ℕ} [NeZero q] (c : ZMod q) : PMF.uniformOfFintype (ZMod q) =
    (PMF.uniformOfFintype (ZMod q)).map (· + c) := by relabel_uniform (fun x => x + c)
example {q : ℕ} [NeZero q] (β : ZMod q) {γ : Type} (f : ZMod q × ZMod q → γ) :
    (do let a ← PMF.uniformOfFintype (ZMod q); let b ← PMF.uniformOfFintype (ZMod q)
        PMF.pure (f (a + b * β, b))) =
      ((PMF.uniformOfFintype (ZMod q)).bind fun a =>
        (PMF.uniformOfFintype (ZMod q)).map fun b => f (a, b)) := by
  relabel_uniform (fun p : ZMod q × ZMod q => (p.1 + p.2 * β, p.2))
example {q : ℕ} [NeZero q] (β : ZMod q) {γ : Type*} (g : (Fin 2 → ZMod q) × (Fin 2 → ZMod q) → γ) :
    (PMF.uniformOfFintype (Fin 2 → ZMod q × ZMod q)).map
        (fun r => g (fun i => (r i).1 + (r i).2 * β, fun i => (r i).2)) =
      ((PMF.uniformOfFintype (Fin 2 → ZMod q)).bind fun a =>
        (PMF.uniformOfFintype (Fin 2 → ZMod q)).map fun b => g (a, b)) := by
  relabel_uniform (fun r : Fin 2 → ZMod q × ZMod q =>
    (fun i => (r i).1 + (r i).2 * β, fun i => (r i).2))
  intro r₁ r₂ h; funext i
  have h₁ := congr_fun (Prod.mk.inj h).1 i; have h₂ := congr_fun (Prod.mk.inj h).2 i
  rw [h₂] at h₁; exact Prod.ext (add_right_cancel h₁) h₂
example {n k : ℕ} (c : Fin k → Fin n → Bool) {γ : Type*} (f : (Fin k → Fin n → Bool) → γ) :
    ((PMF.uniformOfFintype (Fin k → Fin n → Bool)).map fun r => f fun j m => xor (r j m) (c j m)) =
      (PMF.uniformOfFintype (Fin k → Fin n → Bool)).map f := by
  relabel_uniform (fun (r : Fin k → Fin n → Bool) j m => xor (r j m) (c j m))
example {α γ : Type*} [Fintype α] [Nonempty α] (f : α → α) (hf : Function.Bijective f)
    (k : α → PMF γ) :
    ((PMF.uniformOfFintype α).bind fun a => k (f a)) = (PMF.uniformOfFintype α).bind k := by
  relabel_uniform f
example {F : Type*} [Field F] [Fintype F] [DecidableEq F] {a b c : F} (hc : c ≠ a * b)
    {γ : Type*} (k : F → F → PMF γ) :
    ((PMF.uniformOfFintype F).bind fun σ => (PMF.uniformOfFintype F).bind fun τ =>
        k (σ + τ * b) (a * (σ + τ * b) + τ * (c - a * b))) =
      ((PMF.uniformOfFintype F).bind fun x => (PMF.uniformOfFintype F).bind fun y => k x y) := by
  relabel_uniform (fun p : F × F => (p.1 + p.2 * b, a * (p.1 + p.2 * b) + p.2 * (c - a * b)))
  rintro ⟨s₁, t₁⟩ ⟨s₂, t₂⟩ h; simp only [Prod.mk.injEq] at h
  have ht : t₁ = t₂ :=
    mul_right_cancel₀ (sub_ne_zero.mpr hc) (by linear_combination -a * h.1 + h.2)
  subst ht; exact Prod.ext (add_right_cancel h.1) rfl
example {q : ℕ} [NeZero q] (b : ZMod q) {γ : Type*} (k : ZMod q → PMF γ) :
    ((PMF.uniformOfFintype (ZMod q)).bind fun τ => (PMF.uniformOfFintype (ZMod q)).bind fun σ =>
      k (σ + τ * b)) = (PMF.uniformOfFintype (ZMod q)).bind k := by
  drop_uniform with τ; relabel_uniform (Equiv.addRight (τ * b))
example {q : ℕ} [NeZero q] (c d : ZMod q) {γ : Type*} (f : ZMod q → ZMod q → γ) :
    (((PMF.uniformOfFintype (ZMod q)).map (· + c)).bind fun x =>
        ((PMF.uniformOfFintype (ZMod q)).map (· + d)).map fun y => f x y) =
      (PMF.uniformOfFintype (ZMod q × ZMod q)).map fun p => f (p.1 + c) (p.2 + d) := by
  relabel_uniform (Equiv.refl (ZMod q × ZMod q))
example (n m : ℕ) (h : n = m) : n = m := by
  fail_if_success relabel_uniform (Equiv.refl Bool)
  fail_if_success drop_uniform with x
  exact h

end CslibFrontierTests.UniformRelabelTactic
