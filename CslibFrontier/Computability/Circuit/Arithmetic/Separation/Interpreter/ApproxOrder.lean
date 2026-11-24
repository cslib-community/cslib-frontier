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
public import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Data.Int.Interval
import Mathlib.Logic.Equiv.PartialEquiv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Bound
import Mathlib.Tactic.Continuity

/-!
# Laurent polynomials in ε: orders, spans, rescaling

Used for approximate accelerators, whose constants are Laurent polynomials in ε.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Appendix N (Proposition N.4, Theorem N.5) of the paper; module `NS1.ApproxOrd`
-/

@[expose] public section

namespace Cslib.Circuits.Arithmetic.Separation.Interpreter

open LaurentPolynomial

variable {A : Type} [CommRing A] {E : Type} [CommRing E] [Algebra A E]

namespace KT

variable {R R' : Type} [CommRing R] [CommRing R']

/-- All constants satisfy `P`. -/
def All (P : R → Prop) : KT R → Prop
  | none => True
  | leaf c => P c
  | node l r => l.All P ∧ r.All P

omit [CommRing R] in
theorem All.imp {P Q : R → Prop} (hPQ : ∀ c, P c → Q c) {K : KT R} (h : K.All P) : K.All Q := by
  induction K with
  | none => trivial
  | leaf c => exact hPQ c h
  | node l r ihl ihr => exact ⟨ihl h.1, ihr h.2⟩

omit [CommRing R] [CommRing R'] in
theorem All.map {P : R → Prop} {Q : R' → Prop} {f : R → R'} (hPQ : ∀ c, P c → Q (f c))
    {K : KT R} (h : K.All P) :
    (K.map f).All Q := by
  induction K with
  | none => trivial
  | leaf c => exact hPQ c h
  | node l r ihl ihr => exact ⟨ihl h.1, ihr h.2⟩

theorem All.expand {P Q : R → Prop} {B : ℕ} (hPQ : ∀ c, P c → ∀ b < B, Q (c ^ 2 ^ b))
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

omit [CommRing R] in
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
    exact Nat.mul_le_mul_right _ (val_lt_of_length' w (KT.length_words hw)).le
  | node l r ihl ihr =>
    simp only [KT.budg, List.mem_flatMap, List.mem_map] at hq
    obtain ⟨p, hp, q', hq', rfl⟩ := hq
    refine ((ihl h.1 hp).mul (ihr h.2 hq')).mono ?_
    simp only [KT.nds, add_mul]
    exact Nat.le_add_right _ _
where
  val_lt_of_length' {J : ℕ} (w : List Bool) (hw : w.length = J) : KT.val w < 2 ^ J := by
    induction w generalizing J with
    | nil => simp [KT.val, ← hw]
    | cons b w ih =>
      subst hw
      have := ih rfl
      rw [KT.val, List.length_cons, pow_succ]
      cases b <;> simp <;> omega

end Cslib.Circuits.Arithmetic.Separation.Interpreter
