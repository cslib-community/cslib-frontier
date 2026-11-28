/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.Accel
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Cslib.Foundations.Data.Nat.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Accelerators and changes of the ring of constants

Tries of constants map along ring homomorphisms (`Interpreter.KT.map`). An accelerator with
constants in `R` gives one with constants in `R'` along an `A`-algebra map, and back along an
injective one (`Interpreter.IsAccT.map`, `Interpreter.IsAccT.of_map`). The constants of a trie lie
in a finitely generated subalgebra (`Interpreter.KT.exists_lift`). Bounds for the number of binary
digits `Interpreter.lg` follow, and `Interpreter.HasAcc` states that an accelerator exists at a
scale.

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `NS1.Main`.

## Main definitions

* `Interpreter.KT.map`, `Interpreter.KT.consts`, `Interpreter.HasAcc`.

## Main results

* `Interpreter.val_map`, `Interpreter.IsAccT.map`, `Interpreter.IsAccT.of_map`,
  `Interpreter.KT.exists_lift`.
* `Interpreter.poly_lg`: `c * lg n ^ k ≤ n` for all large `n`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Interpreter

open Cslib.Circuits.Arithmetic.Separation.Interpreter.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A} {R : Type} [CommRing R] [Algebra A R]

section Map

variable {R' : Type} [CommRing R'] [Algebra A R']

namespace KT

/-- The images of the constants. -/
@[expose] def map (f : R → R') : KT R → KT R'
  | none => none
  | leaf c => leaf (f c)
  | node l r => node (l.map f) (r.map f)

omit [CommRing R] [CommRing R'] in
theorem nds_map (f : R → R') (K : KT R) : (K.map f).nds = K.nds := by
  induction K with
  | none => rfl
  | leaf c => rfl
  | node l r ihl ihr => simp [map, nds, ihl, ihr]

omit [CommRing R] [CommRing R'] in
theorem ht_map (f : R → R') (K : KT R) : (K.map f).ht = K.ht := by
  induction K with
  | none => rfl
  | leaf c => rfl
  | node l r ihl ihr => simp [map, ht, ihl, ihr]

theorem combVal_map (f : R →+* R') (c : R) (p : List Bool) : combVal (f c) p = f (combVal c p) := by
  induction p generalizing c with
  | nil => simp [combVal]
  | cons b p ih =>
    cases b with
    | true => rw [combVal, combVal, ← map_pow, ih]
    | false =>
      cases p with
      | nil => rfl
      | cons a p => simp [combVal]

theorem lk_map (f : R →+* R') (K : KT R) (p : List Bool) : (K.map f).lk p = f (K.lk p) := by
  induction K generalizing p with
  | none => simp [map, lk]
  | leaf c => exact combVal_map f c p
  | node l r ihl ihr =>
    cases p with
    | nil => simp [map, lk]
    | cons a p =>
      cases a with
      | true => exact ihr p
      | false => exact ihl p

omit [CommRing R] [CommRing R'] in
theorem inB_map (f : R → R') (B : ℕ) (K : KT R) (p : List Bool) : (K.map f).InB B p ↔ K.InB B p :=
    by
  induction K generalizing p with
  | none => exact Iff.rfl
  | leaf c => exact Iff.rfl
  | node l r ihl ihr =>
    cases p with
    | nil => exact Iff.rfl
    | cons a p =>
      cases a with
      | true => exact ihr p
      | false => exact ihl p

/-- The constants. -/
@[expose] def consts : KT R → Set R
  | none => ∅
  | leaf c => {c}
  | node l r => l.consts ∪ r.consts

omit [CommRing R] in
theorem consts_finite (K : KT R) : K.consts.Finite := by
  induction K with
  | none => exact Set.finite_empty
  | leaf c => exact Set.finite_singleton c
  | node l r ihl ihr => exact ihl.union ihr

theorem exists_lift (S : Subalgebra A R) (K : KT R) (h : K.consts ⊆ S) : ∃ K' : KT S,
    K'.map S.val = K := by
  induction K with
  | none => exact ⟨none, rfl⟩
  | leaf c => exact ⟨leaf ⟨c, h rfl⟩, rfl⟩
  | node l r ihl ihr =>
    obtain ⟨l', rfl⟩ := ihl fun c hc => h (Or.inl hc)
    obtain ⟨r', rfl⟩ := ihr fun c hc => h (Or.inr hc)
    exact ⟨node l' r', rfl⟩

end KT

theorem val_map (f : R →ₐ[A] R') (K : KT R) (l : List (Run A)) : val (K.map f).lk l =
    f (val K.lk l) := by
  rw [val, val, map_list_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun r _ => ?_
  simp only [wt, Function.comp_apply, map_mul, AlgHom.commutes, map_list_prod, List.map_map]
  congr 2
  refine List.map_congr_left fun p _ => ?_
  exact KT.lk_map (f : R →+* R') K p

theorem IsAccT.map {H v t : ℕ} {K : KT R} {B : ℕ} {D : Tree} (h : IsAccT θ H v t K B D)
    (f : R →ₐ[A] R') :
    IsAccT θ H v t (K.map f) B D := by
  refine ⟨fun z hz => ⟨(h.run z hz).1, fun r hr => ⟨((h.run z hz).2 r hr).1, fun p hp =>
    (KT.inB_map f B K p).2 (((h.run z hz).2 r hr).2 p hp)⟩⟩, fun z hz hp => ?_⟩
  rw [val_map, h.val z hz hp, AlgHom.commutes]

theorem IsAccT.of_map {H v t : ℕ} {K : KT R} {B : ℕ} {D : Tree} {f : R →ₐ[A] R'}
    (hf : Function.Injective f)
    (h : IsAccT θ H v t (K.map f) B D) : IsAccT θ H v t K B D := by
  refine ⟨fun z hz => ⟨(h.run z hz).1, fun r hr => ⟨((h.run z hz).2 r hr).1, fun p hp =>
    (KT.inB_map f B K p).1 (((h.run z hz).2 r hr).2 p hp)⟩⟩, fun z hz hp => hf ?_⟩
  rw [← val_map, h.val z hz hp, AlgHom.commutes]

end Map

section Logs

theorem lt_two_pow_lg (n : ℕ) : n < 2 ^ lg n := Nat.lt_pow_succ_log_self Nat.one_lt_two n

theorem lg_mono {a b : ℕ} (h : a ≤ b) : lg a ≤ lg b := Nat.succ_le_succ (Nat.log_mono_right h)

theorem lg_pow_le {n k : ℕ} (hk : 1 ≤ k) : lg (n ^ k) ≤ k * lg n := by
  have h1 : n ^ k < 2 ^ (k * lg n) := by
    rw [Nat.mul_comm, pow_mul]
    exact Nat.pow_lt_pow_left (lt_two_pow_lg n) (by omega)
  unfold lg at h1 ⊢
  refine Nat.succ_le_of_lt (Nat.log_lt_of_lt_pow' ?_ h1)
  have : 1 * 1 ≤ k * (Nat.log 2 n + 1) := Nat.mul_le_mul hk (by omega)
  omega

theorem le_lg_pow {n k : ℕ} (hn : n ≠ 0) : k * (lg n - 1) + 1 ≤ lg (n ^ k) := by
  unfold lg
  rw [Nat.add_sub_cancel]
  refine Nat.succ_le_succ (Nat.le_log_of_pow_le Nat.one_lt_two ?_)
  rw [Nat.mul_comm, pow_mul]
  exact Nat.pow_le_pow_left (Nat.pow_log_le_self 2 hn) k

theorem le_lg_of_two_pow_le {n k : ℕ} (h : 2 ^ k ≤ n) : k + 1 ≤ lg n :=
  Nat.succ_le_succ (Nat.le_log_of_pow_le Nat.one_lt_two h)

theorem two_pow_lg_le {n : ℕ} (hn : n ≠ 0) : 2 ^ (lg n - 1) ≤ n := by
  unfold lg
  rw [Nat.add_sub_cancel]
  exact Nat.pow_log_le_self 2 hn

/-- Powers of the logarithm are small. -/
theorem poly_lg (c k : ℕ) : ∃ n₀, ∀ n, n₀ ≤ n → c * lg n ^ k ≤ n := by
  obtain ⟨L₀, hL₀⟩ :=
    Filter.eventually_atTop.1 (Nat.eventually_mul_pow_le_pow (2 * c) k Nat.one_lt_two)
  refine ⟨2 ^ L₀, fun n hn => ?_⟩
  have hn0 : n ≠ 0 := by have := Nat.one_le_two_pow (n := L₀); omega
  have h3 := hL₀ (lg n) ((Nat.le_succ _).trans (le_lg_of_two_pow_le hn))
  have e : 2 ^ lg n = 2 * 2 ^ (lg n - 1) := by
    unfold lg
    rw [Nat.add_sub_cancel, pow_succ']
  rw [Nat.mul_assoc, e] at h3
  exact (Nat.le_of_mul_le_mul_left h3 Nat.zero_lt_two).trans (two_pow_lg_le hn0)

end Logs

theorem lg_ge_two {u : ℕ} (hu : 4 ≤ u) : 2 ≤ lg u := le_trans (by decide)
    (le_lg_of_two_pow_le (k := 2) (by omega))

/-- There is an accelerator of size `s` at the scale `V = v ^ H` over `R`: a trie of at most `s`
nodes with constants of `R`, and a program of size at most `s` that has the values of the universal
plain sums of `V` steps on all instances of size `V ^ (1 - 2 η)` in `V ^ (1 - η)` steps,
`η = 16 / H`; names of constants and exponents are of polylogarithmic length. -/
@[expose] def HasAcc (θ : List Bool → A) (R : Type) [CommRing R] [Algebra A R] (H v s : ℕ) : Prop :=
  ∃ (K : KT R) (B : ℕ) (D : Tree), IsAccT θ H v (v ^ (H - 16)) K B D ∧ K.nds ≤ s ∧ D.size ≤ s ∧
    K.ht ≤ lg (max (v ^ H) s) ^ 2 ∧ B ≤ lg (max (v ^ H) s) ^ 3

end Cslib.Circuits.Arithmetic.Separation.Interpreter
