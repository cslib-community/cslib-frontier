/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Automata.Weighted.Rat
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Set.Finite.List

/-!
# Series on several channels

Letters are pairs `(channel, letter)`. `hat f v` is the sum of the series `f` over all words whose
projections to the channels are the words `v z`. Products of series become convolutions over
antidiagonal channel cuts `anti v`.

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `Nc.Tape.Hat`.

## Main definitions

* `Cslib.Automata.Weighted.proj`: project a word of channel-letter pairs to each channel.
* `Cslib.Automata.Weighted.fib`: finite set of channel words with prescribed projections.
* `Cslib.Automata.Weighted.hat`: sum of a series over `fib v`.
* `Cslib.Automata.Weighted.anti`: all ways to cut channel words into prefix/suffix pairs.
* `Cslib.Automata.Weighted.Series.ne`: zero out the empty word.

## Main results

* `sum_length_proj`: total length of projections equals word length.
* `hat_mul`: `hat` turns Cauchy product into convolution over `anti v`.
* `hat_kstar`: recursion for `hat (Series.kstar f) v`.
-/

public section

namespace Cslib.Automata.Weighted

open Finset

section Basic

variable {Z Γ : Type*} [DecidableEq Z]

/-- The words on the individual channels. -/
@[expose] def proj (o : List (Z × Γ)) : Z → List Γ :=
  fun z => (o.filter fun a => a.1 = z).map Prod.snd

@[simp] theorem proj_nil : proj ([] : List (Z × Γ)) = fun _ => [] := rfl

theorem proj_append (o₁ o₂ : List (Z × Γ)) (z : Z) :
    proj (o₁ ++ o₂) z = proj o₁ z ++ proj o₂ z := by
  simp [proj]

theorem proj_cons (a : Z × Γ) (o : List (Z × Γ)) (z : Z) :
    proj (a :: o) z = if a.1 = z then a.2 :: proj o z else proj o z := by
  by_cases h : a.1 = z <;> simp [proj, h]

theorem sum_length_proj [Fintype Z] (o : List (Z × Γ)) :
    ∑ z, (proj o z).length = o.length := by
  induction o with
  | nil => simp
  | cons a o ih =>
    have hlen : ∀ z, (proj (a :: o) z).length =
        (proj o z).length + if a.1 = z then 1 else 0 := by
      intro z
      rw [proj_cons]
      by_cases h : a.1 = z <;> simp [h]
    simp only [hlen, Finset.sum_add_distrib, ih, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
      List.length_cons]

end Basic

section Hat

variable {F : Type*} [CommRing F] {Z Γ : Type*} [Fintype Z] [DecidableEq Z] [Finite Γ]

/-- The finite set of channel words with given projections. -/
@[expose] noncomputable def fib (v : Z → List Γ) : Finset (List (Z × Γ)) :=
  (show {o : List (Z × Γ) | proj o = v}.Finite from
    (List.finite_length_eq (Z × Γ) (∑ z, (v z).length)).subset (by
      rintro o rfl
      exact (sum_length_proj o).symm)).toFinset

theorem mem_fib {v : Z → List Γ} {o : List (Z × Γ)} : o ∈ fib v ↔ proj o = v := by
  simp [fib]

/-- The sum of a series over the words with given channel projections. -/
@[expose] noncomputable def hat (f : Series F (Z × Γ)) (v : Z → List Γ) : F :=
  ∑ o ∈ fib v, f o

/-- All ways to cut the words on the channels into two parts. -/
@[expose] def anti {Z Γ : Type*} [Fintype Z] [DecidableEq Z] [DecidableEq Γ]
    (v : Z → List Γ) : Finset ((Z → List Γ) × (Z → List Γ)) :=
  (Fintype.piFinset fun z => range ((v z).length + 1)).image fun k =>
    (fun z => (v z).take (k z), fun z => (v z).drop (k z))

theorem mem_anti {Z Γ : Type*} [Fintype Z] [DecidableEq Z] [DecidableEq Γ]
    {v : Z → List Γ} {p : (Z → List Γ) × (Z → List Γ)} :
    p ∈ anti v ↔ ∀ z, p.1 z ++ p.2 z = v z := by
  simp only [anti, Finset.mem_image, Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · rintro ⟨k, -, rfl⟩ z
    simp
  · intro h
    refine ⟨fun z => (p.1 z).length, fun z => ?_, ?_⟩
    · rw [← h z]; simp; omega
    · ext1
      · funext z; simp only; rw [← h z]; simp
      · funext z; simp only; rw [← h z]; simp

theorem hat_add (f g : Series F (Z × Γ)) (v : Z → List Γ) :
    hat (f + g) v = hat f v + hat g v := by
  simp [hat, Finset.sum_add_distrib]

theorem hat_smul (c : F) (f : Series F (Z × Γ)) (v : Z → List Γ) :
    hat (c • f) v = c * hat f v := by
  simp [hat, Finset.mul_sum]

theorem hat_sum {ι : Type*} (s : Finset ι) (f : ι → Series F (Z × Γ)) (v : Z → List Γ) :
    hat (∑ i ∈ s, f i) v = ∑ i ∈ s, hat (f i) v := by
  simp only [hat, Finset.sum_apply]
  rw [Finset.sum_comm]

theorem hat_one [DecidableEq Γ] (v : Z → List Γ) :
    hat (Series.one : Series F (Z × Γ)) v = if v = fun _ => [] then 1 else 0 := by
  simp only [hat, Series.one, Finset.sum_ite_eq', mem_fib, proj_nil]
  by_cases h : v = fun _ => []
  · simp [h]
  · simp [h, Ne.symm h]

theorem hat_mul [DecidableEq Γ] (f g : Series F (Z × Γ)) (v : Z → List Γ) :
    hat (Series.mul f g) v = ∑ p ∈ anti v, hat f p.1 * hat g p.2 := by
  simp only [hat, Series.mul, Finset.sum_mul_sum, Finset.sum_sigma']
  refine Finset.sum_bij'
    (i := fun x _ =>
      ⟨⟨proj (x.1.take x.2), proj (x.1.drop x.2)⟩, x.1.take x.2, x.1.drop x.2⟩)
    (j := fun y _ => ⟨y.2.1 ++ y.2.2, y.2.1.length⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨o, k⟩ h
    simp only [Finset.mem_sigma, mem_fib, Finset.mem_range] at h
    simp only [Finset.mem_sigma, mem_anti, mem_fib, and_true]
    intro z
    rw [← proj_append, List.take_append_drop, h.1]
  · rintro ⟨⟨v₁, v₂⟩, a, b⟩ h
    simp only [Finset.mem_sigma, mem_anti, mem_fib] at h
    obtain ⟨h1, h2, h3⟩ := h
    simp only [Finset.mem_sigma, mem_fib, Finset.mem_range, List.length_append]
    refine ⟨?_, by omega⟩
    funext z
    rw [proj_append, h2, h3]
    exact h1 z
  · rintro ⟨o, k⟩ h
    simp only [Finset.mem_sigma, mem_fib, Finset.mem_range] at h
    simp only [List.take_append_drop, List.length_take, Sigma.mk.injEq, heq_eq_eq, true_and]
    omega
  · rintro ⟨⟨v₁, v₂⟩, a, b⟩ h
    simp only [Finset.mem_sigma, mem_anti, mem_fib] at h
    obtain ⟨_, h2, h3⟩ := h
    simp [h2, h3]
  · rintro ⟨o, k⟩ _
    rfl

/-- The part of a series supported on non-empty words. -/
@[expose] def Series.ne {Z Γ : Type*} (f : Series F (Z × Γ)) : Series F (Z × Γ) :=
  fun o => if o = [] then 0 else f o

omit [Fintype Z] [DecidableEq Z] [Finite Γ] in
theorem kstar_eq (f : Series F (Z × Γ)) :
    Series.kstar f = Series.one + Series.mul (Series.ne f) (Series.kstar f) := by
  funext o
  cases o with
  | nil => simp [Series.kstar_nil, Series.one, Series.mul, Series.ne]
  | cons a o =>
    rw [Series.kstar_cons, Pi.add_apply, Series.mul]
    conv_rhs => rw [Finset.sum_range_succ']
    simp [Series.one, Series.ne]

theorem hat_ne [DecidableEq Γ] (f : Series F (Z × Γ)) (v : Z → List Γ) :
    hat (Series.ne f) v = if v = fun _ => [] then 0 else hat f v := by
  split_ifs with h
  · rw [hat]
    refine Finset.sum_eq_zero fun o ho => ?_
    rw [mem_fib, h] at ho
    have ho_nil : o = [] := by
      have hlen := sum_length_proj o
      rw [ho] at hlen
      simpa using hlen.symm
    simp [Series.ne, ho_nil]
  · rw [hat, hat]
    refine Finset.sum_congr rfl fun o ho => ?_
    rw [mem_fib] at ho
    have ho_ne : o ≠ [] := by rintro rfl; exact h (by rw [← ho]; rfl)
    simp [Series.ne, ho_ne]

/-- The convolution recursion for `hat` of a Kleene star. -/
theorem hat_kstar [DecidableEq Γ] (f : Series F (Z × Γ)) (v : Z → List Γ) :
    hat (Series.kstar f) v = (if v = fun _ => [] then 1 else 0) +
      ∑ p ∈ (anti v).filter (fun p => p.1 ≠ fun _ => []),
        hat f p.1 * hat (Series.kstar f) p.2 := by
  conv_lhs => rw [kstar_eq]
  rw [hat_add, hat_one, hat_mul, Finset.sum_filter]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [hat_ne]
  by_cases h : p.1 = fun _ => [] <;> simp [h]

end Hat

end Cslib.Automata.Weighted
