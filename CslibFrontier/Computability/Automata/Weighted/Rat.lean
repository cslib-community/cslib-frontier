/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Automata.Weighted.Rep
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.ReduceOption

/-!
# Rational series of bounded dimension

Closure properties of `Cslib.Automata.Weighted.RatLe n f` (series realized by a linear
representation of dimension at most `n`), the normal form with a single initial and single final
state (`RatLe.normal`), and trailing idle-padding (`Series.idle`, `RatLe.idle`).

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `Nc.Tape.Rat` (with trailing idle
padding from `Nc.Tape.ProgRun`).

## Main definitions

* `Cslib.Automata.Weighted.RatLe`: bounded-dimension rational series.
* `Cslib.Automata.Weighted.Series.letter`: indicator series of a single letter.
* `Cslib.Automata.Weighted.Series.idle`: pad a series with trailing `none` letters.

## Main results

* `RatLe.add`, `RatLe.mul`, `RatLe.kstar`, `RatLe.smul`, `RatLe.sum`.
* `RatLe.letter`: single-letter series has dimension at most `2`.
* `RatLe.normal`: normal form with one initial and one final state matching on non-empty words.
* `RatLe.idle`: dimension increases by at most `1` under trailing idle padding.
-/

public section

namespace Cslib.Automata.Weighted

open Finset Matrix

variable {F : Type*} [CommRing F] {Ω : Type*}

/-- The series has a linear representation of dimension at most `n`. -/
@[expose] def RatLe (n : ℕ) (f : Series F Ω) : Prop :=
  ∃ (Q : Type) (_ : Fintype Q) (r : Rep F Ω Q), Fintype.card Q ≤ n ∧ r.series = f

namespace RatLe

theorem mono {n m : ℕ} {f : Series F Ω} (h : RatLe n f) (hm : n ≤ m) : RatLe m f := by
  obtain ⟨Q, _, r, h1, h2⟩ := h
  exact ⟨Q, _, r, h1.trans hm, h2⟩

theorem zero : RatLe 0 (0 : Series F Ω) :=
  ⟨Empty, inferInstance, ⟨0, 0, 0⟩, by simp, by ext o; simp [Rep.series]⟩

theorem add {n m : ℕ} {f g : Series F Ω} (hf : RatLe n f) (hg : RatLe m g) :
    RatLe (n + m) (f + g) := by
  obtain ⟨Q₁, _, r₁, h1, rfl⟩ := hf
  obtain ⟨Q₂, _, r₂, h2, rfl⟩ := hg
  exact ⟨Q₁ ⊕ Q₂, inferInstance, r₁.add r₂, by simp; omega, funext (Rep.add_series r₁ r₂)⟩

theorem mul {n m : ℕ} {f g : Series F Ω} (hf : RatLe n f) (hg : RatLe m g) :
    RatLe (n + m) (Series.mul f g) := by
  obtain ⟨Q₁, _, r₁, h1, rfl⟩ := hf
  obtain ⟨Q₂, _, r₂, h2, rfl⟩ := hg
  exact ⟨Q₁ ⊕ Q₂, inferInstance, r₁.mul r₂, by simp; omega, funext (Rep.mul_series r₁ r₂)⟩

theorem kstar {n : ℕ} {f : Series F Ω} (hf : RatLe n f) : RatLe (n + 1) (Series.kstar f) := by
  obtain ⟨Q₁, _, r₁, h1, rfl⟩ := hf
  exact ⟨Unit ⊕ Q₁, inferInstance, r₁.star, by simp; omega, funext r₁.star_series⟩

theorem smul {n : ℕ} {f : Series F Ω} (c : F) (hf : RatLe n f) : RatLe n (c • f) := by
  obtain ⟨Q, _, r, h1, rfl⟩ := hf
  refine ⟨Q, _, ⟨c • r.lam, r.mu, r.gam⟩, h1, ?_⟩
  ext o
  have htail (o : List Ω) : (⟨c • r.lam, r.mu, r.gam⟩ : Rep F Ω Q).tail o = r.tail o := by
    induction o with
    | nil => rfl
    | cons a o ih => simp [Rep.tail, ih]
  simp [Rep.series, htail]

theorem one : RatLe 1 (Series.one : Series F Ω) := by
  refine ⟨Unit, inferInstance, ⟨1, 0, 1⟩, by simp, ?_⟩
  funext o
  cases o <;> simp [Rep.series, Rep.tail, Series.one]

theorem sum {ι : Type*} (s : Finset ι) (n : ι → ℕ) (f : ι → Series F Ω)
    (h : ∀ i ∈ s, RatLe (n i) (f i)) :
    RatLe (∑ i ∈ s, n i) (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end RatLe

/-- The indicator series of a single letter `a`. -/
@[expose] def Series.letter [DecidableEq Ω] (a : Ω) : Series F Ω :=
  fun o => if o = [a] then 1 else 0

theorem RatLe.letter [DecidableEq Ω] (a : Ω) :
    RatLe 2 (Series.letter a : Series F Ω) := by
  refine ⟨Bool, inferInstance, ⟨fun q => if q then 0 else 1,
    fun b => Matrix.of fun q q' => if b = a ∧ q = false ∧ q' = true then 1 else 0,
    fun q => if q then 1 else 0⟩, by simp, ?_⟩
  ext o
  match o with
  | [] | _ :: _ :: _ => simp [Rep.series, Rep.tail, Series.letter, dotProduct, Matrix.mulVec]
  | [b] =>
    by_cases h : b = a <;>
      simp [Rep.series, Rep.tail, Series.letter, dotProduct, Matrix.mulVec, h]

/-- Normal form: one initial and one final state, giving the same values at non-empty words. -/
theorem RatLe.normal {n : ℕ} {f : Series F Ω} (hf : RatLe n f) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (mu : Ω → Matrix Q Q F) (i e : Q),
      Fintype.card Q ≤ n + 2 ∧ ∀ o : List Ω, o ≠ [] → (o.map mu).prod i e = f o := by
  classical
  obtain ⟨Q, _, r, h1, rfl⟩ := hf
  let mu : Ω → Matrix (Option (Option Q)) (Option (Option Q)) F :=
    fun a => Matrix.of fun q q' =>
      match q, q' with
      | none, none => 0
      | none, some none => r.lam ⬝ᵥ (r.mu a *ᵥ r.gam)
      | none, some (some q') => (r.lam ᵥ* r.mu a) q'
      | some none, _ => 0
      | some (some _), none => 0
      | some (some q), some none => (r.mu a *ᵥ r.gam) q
      | some (some q), some (some q') => r.mu a q q'
  have hsink (o : List Ω) (ho : o ≠ []) : (o.map mu).prod (some none) (some none) = 0 := by
    obtain ⟨b, o', rfl⟩ := List.exists_cons_of_ne_nil ho
    simp [Matrix.mul_apply, mu]
  have key (o : List Ω) : ∀ q, o ≠ [] →
      (o.map mu).prod (some (some q)) (some none) = r.tail o q := by
    induction o with
    | nil => simp
    | cons a o ih =>
      intro q _
      rw [List.map_cons, List.prod_cons, Matrix.mul_apply, Fintype.sum_option, Fintype.sum_option]
      rcases eq_or_ne o [] with rfl | ho
      · simp [mu, Rep.tail]
      · simp only [mu, Matrix.of_apply, zero_mul, zero_add]
        rw [hsink o ho, mul_zero, zero_add, Rep.tail, Matrix.mulVec, dotProduct]
        exact Finset.sum_congr rfl fun q' _ => by rw [ih q' ho]
  refine ⟨Option (Option Q), inferInstance, inferInstance, mu, none, some none, by simp; omega,
    fun o ho => ?_⟩
  obtain ⟨a, o, rfl⟩ := List.exists_cons_of_ne_nil ho
  rw [List.map_cons, List.prod_cons, Matrix.mul_apply, Fintype.sum_option, Fintype.sum_option]
  rcases eq_or_ne o [] with rfl | ho
  · simp [mu, Rep.series, Rep.tail]
  · rw [Finset.sum_congr rfl fun q' _ => by rw [key o q' ho]]
    simp only [mu, Matrix.of_apply, zero_mul, zero_add]
    rw [hsink o ho, mul_zero, zero_add, Rep.series, Rep.tail, Matrix.dotProduct_mulVec]
    rfl

section Idle

/-- The words of a series, followed by arbitrarily many idle (`none`) letters. -/
@[expose] def Series.idle (P : Series F Ω) : Series F (Option Ω) :=
  Series.mul
    (fun o => if o.all Option.isSome then P o.reduceOption else 0)
    (fun o => if o.all Option.isNone then 1 else 0)

theorem RatLe.idle {n : ℕ} {P : Series F Ω} (hP : RatLe n P) :
    RatLe (n + 1) (Series.idle P) := by
  refine RatLe.mul ?_ ?_
  · obtain ⟨Q, _, r, hn, rfl⟩ := hP
    refine ⟨Q, inferInstance, ⟨r.lam, fun a => a.elim 0 r.mu, r.gam⟩, hn, ?_⟩
    have key (o : List (Option Ω)) :
        (⟨r.lam, fun a => a.elim 0 r.mu, r.gam⟩ : Rep F (Option Ω) Q).tail o =
          if o.all Option.isSome then r.tail o.reduceOption else 0 := by
      induction o with
      | nil => rfl
      | cons a o ih =>
        rw [Rep.tail, ih]
        cases a <;> by_cases h : o.all Option.isSome <;>
          simp [h, List.reduceOption_cons_of_some, Rep.tail]
    funext o
    by_cases h : o.all Option.isSome <;> simp [Rep.series, key, h]
  · refine ⟨Unit, inferInstance, ⟨1, fun a => a.elim 1 fun _ => 0, 1⟩, by simp, ?_⟩
    have key (o : List (Option Ω)) :
        (⟨1, fun a => a.elim 1 fun _ => 0, 1⟩ : Rep F (Option Ω) Unit).tail o =
          if o.all Option.isNone then 1 else 0 := by
      induction o with
      | nil => rfl
      | cons a o ih =>
        rw [Rep.tail, ih]
        cases a <;> simp
    funext o
    by_cases h : o.all Option.isNone <;> simp [Rep.series, key, h]

theorem idle_apply (P : Series F Ω) (w : List Ω) (j : ℕ) :
    Series.idle P (w.map some ++ List.replicate j none) = P w := by
  rw [Series.idle, Series.mul, Finset.sum_eq_single w.length]
  · rw [List.take_left' (by simp), List.drop_left' (by simp)]
    simp [List.reduceOption]
  · intro k hk hne
    rw [mem_range, List.length_append, List.length_map, List.length_replicate] at hk
    rcases lt_or_gt_of_ne hne with h | h
    · have hmem : some w[k] ∈ (w.map some ++ List.replicate j none).drop k := by
        rw [List.drop_append_of_le_length (by simp; omega), List.mem_append, ← List.map_drop]
        exact Or.inl (List.mem_map.2 ⟨w[k], List.drop_eq_getElem_cons h ▸ List.mem_cons_self, rfl⟩)
      simp [(List.all_eq_false (p := Option.isNone)).2 ⟨_, hmem, nofun⟩]
    · have hmem : none ∈ (w.map some ++ List.replicate j none).take k := by
        rw [List.take_append, List.mem_append, List.length_map, List.take_replicate]
        exact Or.inr (List.mem_replicate.2 ⟨by omega, rfl⟩)
      simp [(List.all_eq_false (p := Option.isSome)).2 ⟨_, hmem, nofun⟩]
  · exact fun h => absurd (mem_range.2 (by simp; omega)) h

theorem idle_ne_zero (P : Series F Ω) (o : List (Option Ω)) (h : Series.idle P o ≠ 0) :
    ∃ (w : List Ω) (j : ℕ), o = w.map some ++ List.replicate j none := by
  unfold Series.idle Series.mul at h
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  beta_reduce at hk
  have h1 : (o.take k).all Option.isSome = true :=
    by_contra fun hn => hk (by rw [ite_eq_right hn, zero_mul])
  have h2 : (o.drop k).all Option.isNone = true :=
    by_contra fun hn => hk (by rw [ite_eq_right hn, mul_zero])
  have e1 (l : List (Option Ω)) (hl : l.all Option.isSome = true) :
      l.reduceOption.map some = l := by
    induction l with
    | nil => rfl
    | cons a l ih =>
      rcases a with _ | a
      · simp at hl
      · simpa [List.reduceOption_cons_of_some] using ih (by simpa using hl)
  have e2 (l : List (Option Ω)) (hl : l.all Option.isNone = true) :
      List.replicate l.length none = l :=
    (List.eq_replicate_iff.2 ⟨rfl, fun a ha => by simpa using List.all_eq_true.1 hl a ha⟩).symm
  exact ⟨(o.take k).reduceOption, (o.drop k).length,
    by rw [e1 _ h1, e2 _ h2, List.take_append_drop]⟩

end Idle

end Cslib.Automata.Weighted
