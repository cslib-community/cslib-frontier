/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.RingTheory.LaurentPolynomial.OrderSpan
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.BaseChange
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.FullTrie

/-!
# Trees of constants and the spans of their budgets

The constants of an approximate accelerator are Laurent polynomials in ε, stored in a tree of
constants (`KT`). This file adds a predicate for all constants of a tree (`KT.All`) and bounds the
span of the products of powers of the constants that a budget names (`span_budg`), also after
the constants are expanded into their repeated squares (`span_expand_budg`).

## Main definitions

* `KT.All`: every constant of a tree satisfies a predicate.

## Main results

* `KT.All.imp`, `KT.All.map`, `KT.All.expand`, `KT.exists_bound`.
* `span_budg`, `span_expand_budg`: the spans of the budgets' products.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Appendix N (Proposition N.4, Theorem N.5) of the paper; module `NS1.ApproxOrd`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Interpreter

open LaurentPolynomial

variable {E : Type} [CommRing E]

namespace KT

variable {R R' : Type}

/-- All constants satisfy `P`. -/
@[expose] def All (P : R → Prop) : KT R → Prop
  | none => True
  | leaf c => P c
  | node l r => l.All P ∧ r.All P

theorem All.imp {P Q : R → Prop} (hPQ : ∀ c, P c → Q c) {K : KT R} (h : K.All P) : K.All Q := by
  induction K with
  | none => trivial
  | leaf c => exact hPQ c h
  | node l r ihl ihr => exact ⟨ihl h.1, ihr h.2⟩

theorem All.map {P : R → Prop} {Q : R' → Prop} {f : R → R'} (hPQ : ∀ c, P c → Q (f c))
    {K : KT R} (h : K.All P) :
    (K.map f).All Q := by
  induction K with
  | none => trivial
  | leaf c => exact hPQ c h
  | node l r ihl ihr => exact ⟨ihl h.1, ihr h.2⟩

theorem All.expand [CommRing R] {P Q : R → Prop} {B : ℕ} (hPQ : ∀ c, P c → ∀ b < B, Q (c ^ 2 ^ b))
    {K : KT R} (h : K.All P) :
    (K.expand B).All Q := by
  induction K with
  | none => trivial
  | node l r ihl ihr => exact ⟨ihl h.1, ihr h.2⟩
  | leaf c =>
    have h1 : ∀ n b, b + n ≤ B → (comb (c ^ 2 ^ b) n).All Q := by
      intro n
      induction n with
      | zero => exact fun _ _ => trivial
      | succ n ih =>
        intro b hb
        refine ⟨hPQ c h b (by omega), ?_⟩
        rw [← pow_mul, ← pow_succ]
        exact ih (b + 1) (by omega)
    have := h1 B 0 (by omega)
    rwa [pow_zero, pow_one] at this

theorem exists_bound {P : ℕ → R → Prop} (hP : ∀ c, ∃ n, P n c)
    (hm : ∀ n m c, n ≤ m → P n c → P m c) (K : KT R) :
    ∃ n, K.All (P n) := by
  induction K with
  | none => exact ⟨0, trivial⟩
  | leaf c => exact hP c
  | node l r ihl ihr =>
    obtain ⟨n, hn⟩ := ihl
    obtain ⟨m, hm'⟩ := ihr
    exact ⟨max n m, hn.imp fun c => hm _ _ c (le_max_left _ _),
        hm'.imp fun c => hm _ _ c (le_max_right _ _)⟩

end KT

/-- **The orders of the products of powers of the constants**, for all budgets with `J` digits. -/
theorem span_budg {n J : ℕ} {K : KT E[T;T⁻¹]} (h : K.All (Span n))
    {q : Bt × E[T;T⁻¹]} (hq : q ∈ K.budg J) :
    Span (K.nds * 2 ^ J * n) q.2 := by
  induction K generalizing q with
  | none =>
    simp only [KT.budg, List.mem_singleton] at hq
    subst hq
    exact Span.one _
  | leaf c =>
    simp only [KT.budg, List.mem_map] at hq
    obtain ⟨w, hw, rfl⟩ := hq
    refine ((show Span n c from h).pow _).mono ?_
    rw [KT.nds, one_mul]
    exact Nat.mul_le_mul_right _ (val_lt_of_length (KT.length_words hw)).le
  | node l r ihl ihr =>
    simp only [KT.budg, List.mem_flatMap, List.mem_map] at hq
    obtain ⟨p, hp, q', hq', rfl⟩ := hq
    refine ((ihl h.1 hp).mul (ihr h.2 hq')).mono ?_
    simp only [KT.nds, add_mul]
    exact Nat.le_add_right _ _

/-- **The exponents of the outer weights**: products of powers of constants of span `M`. -/
theorem span_expand_budg {K : KT E[T;T⁻¹]} {M B J : ℕ} (hM : K.All (Span M)) {q : Bt × E[T;T⁻¹]}
    (hq : q ∈ (K.expand B).budg J) : Span ((K.expand B).nds * 2 ^ J * (2 ^ B * M)) q.2 :=
  span_budg (hM.expand (Q := Span (2 ^ B * M)) fun _ hc _ hb =>
    (hc.pow _).mono (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hb.le))) hq


end Cslib.Circuits.Arithmetic.Separation.Interpreter
