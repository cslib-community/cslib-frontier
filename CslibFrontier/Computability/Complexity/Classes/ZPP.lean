/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.RP
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Foundations.Data.BitString.WordCount

/-!
# The class ZPP

`ZPP` is defined like `RP` (`Cslib.Complexity.RP`), through deterministic polynomial-time machines
that read a random string, but with zero error: `A ∈ ZPP enc` when there are a polynomial `p` and
a function `V : α × List Bool → Option Bool`, computable in polynomial time on inputs
`frame (enc a) ++ r`, such that for every instance `a` an answer `V (a, r) = some b` is always
right, `b = true` exactly when `a ∈ A`, and at least half of the random strings `r` of length
`p (enc a).length` give an answer (`Cslib.Complexity.DecidesWithZeroError`). These are the
algorithms that never err and say "don't know" with probability at most `1 / 2`
[Arora and Barak, Section 7.3][AroraBarak09]; the definition through expected polynomial running
time defines the same class, but expected running time is not modelled here.

`ZPP = RP ∩ coRP` [Arora and Barak, Section 7.3][AroraBarak09]
(`Cslib.Complexity.ZPP_eq_RP_inter_coRP`). Answering `true` only on the answer `some true` decides
a problem in `ZPP` with one-sided error, and so does answering `false` only on `some false` for its
complement. Conversely, for one-sided-error deciders of a problem and of its complement, which
read disjoint parts of the random string, the first accepting gives the answer `some true`, the
second the answer `some false`, and neither errs; on a member the first accepts on at least half of
the random strings, and on a non-member the second does.

## Main definitions

* `Cslib.Complexity.DecidesWithZeroError`: the zero-error condition.
* `Cslib.Complexity.ZPP`.

## Main results

* `Cslib.Complexity.ZPP_subset_RP`, `Cslib.Complexity.ZPP_subset_coRP`.
* `Cslib.Complexity.exists_zeroError_errorExponent_of_mem_RP_inter_coRP`: a problem in
  `RP ∩ coRP` has zero-error deciders answering `none` with probability at most `2 ^ (-q(n))`.
* `Cslib.Complexity.RP_inter_coRP_subset_ZPP`.
* `Cslib.Complexity.ZPP_eq_RP_inter_coRP`: `ZPP = RP ∩ coRP`.
* `Cslib.Complexity.compl_mem_ZPP`: `ZPP` is closed under complement.

## References

* [J. Gill, *Computational complexity of probabilistic Turing machines*][Gill1977]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type}

/-- `V` decides `A` with zero error, using random strings whose length is `p` evaluated at the
length of the encoded instance: for every instance `a`, an answer `V (a, r) = some b` is right,
`b = true` exactly when `a ∈ A`, and at least half of the random strings give an answer. -/
def DecidesWithZeroError (enc : α ↪ List Bool) (p : Polynomial ℕ)
    (V : α × List Bool → Option Bool) (A : Set α) : Prop :=
  ∀ a, (∀ r : Fin (p.eval (enc a).length) → Bool, ∀ b, V (a, List.ofFn r) = some b →
      (b = true ↔ a ∈ A)) ∧
    2 ^ p.eval (enc a).length ≤
      2 * acceptCount (fun x => (V x).isSome) a (p.eval (enc a).length)

/-- The problems decided with zero error by polynomial-time machines reading polynomially long
random strings, with respect to the encoding `enc` of instances [Gill][Gill1977],
[Arora and Barak, Section 7.3][AroraBarak09]. -/
def ZPP (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (p : Polynomial ℕ) (V : α × List Bool → Option Bool),
    ComputableInPolyTime V (encPair enc encBits) (encOption encBool) ∧
      DecidesWithZeroError enc p V A}

variable {enc : α ↪ List Bool}

theorem mem_ZPP {A : Set α} : A ∈ ZPP enc ↔ ∃ (p : Polynomial ℕ)
    (V : α × List Bool → Option Bool),
    ComputableInPolyTime V (encPair enc encBits) (encOption encBool) ∧
      DecidesWithZeroError enc p V A :=
  Iff.rfl

section Answers

variable {V : α × List Bool → Option Bool} {A : Set α} {a : α} {m : ℕ}

/-- On a member, a verifier whose answers are never wrong accepts with `getD false` wherever it
answers. -/
theorem acceptCount_isSome_le_acceptCount_getD
    (hright : ∀ r : Fin m → Bool, ∀ b, V (a, List.ofFn r) = some b → (b = true ↔ a ∈ A))
    (ha : a ∈ A) :
    acceptCount (fun x => (V x).isSome) a m ≤ acceptCount (fun x => (V x).getD false) a m :=
  Finset.card_le_card fun r => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Option.isSome_iff_exists]
    rintro ⟨b, hb⟩
    rw [hb, Option.getD_some, (hright r b hb).mpr ha]

/-- On a non-member, a verifier whose answers are never wrong never accepts with `getD false`. -/
theorem getD_false_eq_false
    (hright : ∀ r : Fin m → Bool, ∀ b, V (a, List.ofFn r) = some b → (b = true ↔ a ∈ A))
    (ha : a ∉ A) (r : Fin m → Bool) : (V (a, List.ofFn r)).getD false = false := by
  cases hV : V (a, List.ofFn r) with
  | none => rfl
  | some b => simpa using (hright r b hV).not.mpr ha

/-- Negating the answers of a verifier whose answers are never wrong for `A` gives answers that are
never wrong for `Aᶜ`. -/
theorem map_not_eq_some_iff_mem_compl
    (hright : ∀ r : Fin m → Bool, ∀ b, V (a, List.ofFn r) = some b → (b = true ↔ a ∈ A)) :
    ∀ r : Fin m → Bool, ∀ b, (V (a, List.ofFn r)).map Bool.not = some b → (b = true ↔ a ∈ Aᶜ) :=
  fun r b hb => by
    obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.mp hb
    have := hright r b' hb'
    cases b' <;> simp_all

end Answers

namespace DecidesWithZeroError

variable {p : Polynomial ℕ} {V : α × List Bool → Option Bool} {A : Set α}

/-- Accepting exactly on the answer `some true` decides the problem with one-sided error. -/
theorem decidesWithOneSidedError (h : DecidesWithZeroError enc p V A) :
    DecidesWithOneSidedError enc p (fun x => (V x).getD false) A := fun a =>
  ⟨fun ha => (h a).2.trans
      (Nat.mul_le_mul_left 2 (acceptCount_isSome_le_acceptCount_getD (h a).1 ha)),
    getD_false_eq_false (h a).1⟩

/-- Negating the answers decides the complement with zero error. -/
theorem compl (h : DecidesWithZeroError enc p V A) :
    DecidesWithZeroError enc p (fun x => (V x).map Bool.not) Aᶜ := fun a =>
  ⟨map_not_eq_some_iff_mem_compl (h a).1, by simpa only [Option.isSome_map] using (h a).2⟩

end DecidesWithZeroError

/-- **`ZPP` is closed under complement.** -/
theorem compl_mem_ZPP {A : Set α} (hA : A ∈ ZPP enc) : Aᶜ ∈ ZPP enc := by
  obtain ⟨p, V, hV, h⟩ := mem_ZPP.mp hA
  exact mem_ZPP.mpr ⟨p, fun x => (V x).map Bool.not, by fun_prop, h.compl⟩

/-- **`ZPP ⊆ RP`**: accept exactly on the answer `some true`. -/
theorem ZPP_subset_RP : ZPP enc ⊆ RP enc := fun _ ⟨p, V, hV, h⟩ =>
  ⟨p, fun x => (V x).getD false,
    (ComputableInPolyTime.optionGetDWithInput hV (.const false)),
    h.decidesWithOneSidedError⟩

/-- **`ZPP ⊆ coRP`**: the complement is in `ZPP`, hence in `RP`. -/
theorem ZPP_subset_coRP : ZPP enc ⊆ coRP enc := fun _ hA => ZPP_subset_RP (compl_mem_ZPP hA)

/-! ### Splitting random strings -/

/-- The random strings of length `m + k` whose last `k` bits satisfy `P`. -/
private theorem card_filter_drop (m k : ℕ) (P : List Bool → Prop) [DecidablePred P] :
    (Finset.univ.filter fun r : Fin (m + k) → Bool => P ((List.ofFn r).drop m)).card =
      2 ^ m * (Finset.univ.filter fun v : Fin k → Bool => P (List.ofFn v)).card := by
  have h := BitString.card_filter_take_drop (Nat.le_add_right m k) (fun _ => True) P
  rw [Nat.add_sub_cancel_left] at h
  simpa using h

/-- A prefix of the right length is a random string of that length. -/
private theorem exists_ofFn_eq_take {m k : ℕ} (r : Fin (m + k) → Bool) :
    ∃ u : Fin m → Bool, List.ofFn u = (List.ofFn r).take m :=
  ⟨_, by rw [List.ofFn_add, List.take_left' List.length_ofFn]⟩

/-- A suffix of the right length is a random string of that length. -/
private theorem exists_ofFn_eq_drop {m k : ℕ} (r : Fin (m + k) → Bool) :
    ∃ v : Fin k → Bool, List.ofFn v = (List.ofFn r).drop m :=
  ⟨_, by rw [List.ofFn_add, List.drop_left' List.length_ofFn]⟩

/-- Scaling an acceptance-count error bound from `m₁` random bits to `m₁ + m₂` random bits. -/
private theorem errorExponent_scale {q m₁ m₂ c ans : ℕ}
    (he : 2 ^ q * (2 ^ m₁ - c) ≤ 2 ^ m₁) (hge : c * 2 ^ m₂ ≤ ans) :
    2 ^ q * (2 ^ (m₁ + m₂) - ans) ≤ 2 ^ (m₁ + m₂) :=
  calc 2 ^ q * (2 ^ (m₁ + m₂) - ans)
      ≤ 2 ^ q * ((2 ^ m₁ - c) * 2 ^ m₂) := by
        gcongr
        rw [Nat.sub_mul, pow_add]
        exact Nat.sub_le_sub_left hge _
    _ = 2 ^ q * (2 ^ m₁ - c) * 2 ^ m₂ := by ring
    _ ≤ 2 ^ m₁ * 2 ^ m₂ := Nat.mul_le_mul_right _ he
    _ = 2 ^ (m₁ + m₂) := (pow_add _ _ _).symm

/-! ### `RP ∩ coRP ⊆ ZPP` -/

/-- **Zero-error deciders with error exponent `q` from `RP ∩ coRP`**: for every polynomial `q`, a
problem in `RP ∩ coRP` has a polynomial-time verifier that never gives a wrong answer and answers
`none` on at most a `2 ^ (-q(n))` fraction of the random strings. Reduce the error of
one-sided-error deciders `V₁` of `A` and `V₂` of its complement to `2 ^ (-q(n))`, run them on the
first and the last part of the random string, and answer `some true` when `V₁` accepts,
`some false` when `V₂` does, and `none` otherwise. -/
theorem exists_zeroError_errorExponent_of_mem_RP_inter_coRP {A : Set α}
    (hA : A ∈ RP enc ∩ coRP enc) (q : Polynomial ℕ) :
    ∃ (p : Polynomial ℕ) (V : α × List Bool → Option Bool),
      ComputableInPolyTime V (encPair enc encBits) (encOption encBool) ∧
      ∀ a, (∀ r : Fin (p.eval (enc a).length) → Bool, ∀ b, V (a, List.ofFn r) = some b →
          (b = true ↔ a ∈ A)) ∧
        ErrorExponentAt enc q p (fun x => (V x).isSome) a true := by
  obtain ⟨p₁, V₁, hV₁, h₁⟩ := mem_RP_iff_forall_decidesWithOneSidedErrorExponent.mp hA.1 q
  obtain ⟨p₂, V₂, hV₂, h₂⟩ :=
    mem_RP_iff_forall_decidesWithOneSidedErrorExponent.mp (mem_coRP.mp hA.2) q
  let len (a : α) : ℕ := p₁.eval (enc a).length
  let V (x : α × List Bool) : Option Bool :=
    if V₁ (x.1, x.2.take (len x.1)) then some true
    else if V₂ (x.1, x.2.drop (len x.1)) then some false else none
  have hpoly : ComputableInPolyTime V (encPair enc encBits) (encOption encBool) := by
    dsimp [V, len]
    fun_prop
  refine ⟨p₁ + p₂, V, hpoly, fun a => ?_⟩
  set m₂ := p₂.eval (enc a).length
  have heval : (p₁ + p₂).eval (enc a).length = len a + m₂ := Polynomial.eval_add
  -- `V₁` never accepts a non-member, and `V₂` never accepts a member
  have hV₁ (ha : a ∉ A) (r : Fin (len a + m₂) → Bool) :
      V₁ (a, (List.ofFn r).take (len a)) = false := by
    obtain ⟨u, hu⟩ := exists_ofFn_eq_take r
    exact hu ▸ (h₁ a).2 ha u
  have hV₂ (ha : a ∈ A) (r : Fin (len a + m₂) → Bool) :
      V₂ (a, (List.ofFn r).drop (len a)) = false := by
    obtain ⟨v, hv⟩ := exists_ofFn_eq_drop r
    exact hv ▸ (h₂ a).2 (not_not.mpr ha) v
  refine ⟨?_, errorExponentAt_true_iff.2 ?_⟩
  · rw [heval]
    intro r b hb
    simp only [V] at hb
    split_ifs at hb with hacc hrej <;> cases hb
    · exact iff_of_true rfl (by_contra fun ha => Bool.false_ne_true (hV₁ ha r ▸ hacc))
    · exact iff_of_false Bool.false_ne_true fun ha => Bool.false_ne_true (hV₂ ha r ▸ hrej)
  rw [heval]
  set ans := acceptCount (fun x => (V x).isSome) a (len a + m₂)
  by_cases ha : a ∈ A
  · -- on a member, `V₁` rejects on at most a `2 ^ (-q(n))` fraction of its random strings
    have hcount : (Finset.univ.filter fun r : Fin (len a + m₂) → Bool =>
          V₁ (a, (List.ofFn r).take (len a)) = true).card = acceptCount V₁ a (len a) * 2 ^ m₂ := by
      rw [BitString.card_filter_take (Nat.le_add_right _ _) fun u => V₁ (a, u) = true,
        Nat.add_sub_cancel_left, Nat.mul_comm]
      rfl
    have hge : acceptCount V₁ a (len a) * 2 ^ m₂ ≤ ans :=
      hcount ▸ Finset.card_le_card fun r hr => by simp [V, (Finset.mem_filter.mp hr).2]
    exact errorExponent_scale (errorExponentAt_true_iff.1 ((h₁ a).1 ha)) hge
  · -- on a non-member, `V₂` rejects on at most a `2 ^ (-q(n))` fraction of its random strings
    have hge : 2 ^ len a * acceptCount V₂ a m₂ ≤ ans :=
      card_filter_drop (len a) m₂ (fun v => V₂ (a, v) = true) ▸
        Finset.card_le_card fun r hr => by simp [V, (Finset.mem_filter.mp hr).2, hV₁ ha r]
    rw [Nat.add_comm]
    exact errorExponent_scale (errorExponentAt_true_iff.1 ((h₂ a).1 ha)) (by rwa [Nat.mul_comm])

/-- **`RP ∩ coRP ⊆ ZPP`**: the zero-error decider of
`Cslib.Complexity.exists_zeroError_errorExponent_of_mem_RP_inter_coRP` with error exponent `1`
answers on at least half of the random strings. -/
theorem RP_inter_coRP_subset_ZPP : RP enc ∩ coRP enc ⊆ ZPP enc := fun A hA => by
  obtain ⟨p, V, hV, h⟩ := exists_zeroError_errorExponent_of_mem_RP_inter_coRP hA 1
  refine ⟨p, V, hV, fun a => ⟨(h a).1, ?_⟩⟩
  have e := errorExponentAt_true_iff.1 (h a).2
  have := acceptCount_le_two_pow (V := fun x => (V x).isSome) (a := a) (n := p.eval (enc a).length)
  simp only [Polynomial.eval_one, pow_one] at e
  omega

/-- **`ZPP = RP ∩ coRP`** [Arora and Barak, Section 7.3][AroraBarak09]. -/
theorem ZPP_eq_RP_inter_coRP : ZPP enc = RP enc ∩ coRP enc :=
  Set.Subset.antisymm (fun _ hA => ⟨ZPP_subset_RP hA, ZPP_subset_coRP hA⟩)
    RP_inter_coRP_subset_ZPP

end Cslib.Complexity
