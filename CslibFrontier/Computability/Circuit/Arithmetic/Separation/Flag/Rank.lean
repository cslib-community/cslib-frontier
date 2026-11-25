/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Flag.Blow

/-!
# The growth function, and contracting lengths along homomorphisms of matrices

`Flag.grow` is the growth function of a length, and `Flag.Good` the property that a contracting
length gives along a homomorphism from matrices over `F₂`.

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `Nc.Flag.Rank`.

## Main results

* `Flag.grow_mono`, `Flag.good_of_contr`, `Flag.Good.dg_zero`.
-/

public section

open Finset Matrix

namespace Cslib.Circuits.Arithmetic.Separation.Flag

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {G : Type*} [Group G]

/-- The growth allowed by the contraction. -/
@[expose] noncomputable def grow (m : ℕ) (s : ℝ) (r : ℕ) : ℝ :=
  m * (Nat.log m r + 1) * s ^ Nat.log m r

theorem grow_nonneg (m : ℕ) {s : ℝ} (hs : 1 ≤ s) (r : ℕ) : 0 ≤ grow m s r := by
  unfold grow
  positivity

theorem grow_mono (m : ℕ) {s : ℝ} (hs : 1 ≤ s) {r r' : ℕ} (h : r ≤ r') :
    grow m s r ≤ grow m s r' := by
  unfold grow
  have hl : Nat.log m r ≤ Nat.log m r' := Nat.log_mono_right h
  have : 0 ≤ s ^ Nat.log m r := by positivity
  gcongr

/-- Facts about `f = l ∘ τ`. -/
structure Good (f : Matrix ι ι F2 → ℝ) (m : ℕ) (s : ℝ) : Prop where
  nonneg : ∀ M, 0 ≤ f M
  zero : f 0 = 0
  add : ∀ M N, f (M + N) ≤ f M + f N
  digit : ∀ (q : ℕ) (e : Fin m × Fin q ↪ ι) (i : Fin m),
    DM f (dg ((univ : Finset (Fin m × Fin q)).map e)) ≤
      s ^ 2 * DM f (dg ((({i} : Finset (Fin m)) ×ˢ univ).map e))

theorem good_of_contr (l : Len G) {m : ℕ} {s : ℝ} (hC : Contr l m s)
    (τ : Matrix ι ι F2 → G) (hτ : ∀ M N, τ (M + N) = τ M * τ N) :
    Good (fun M => l (τ M)) m s where
  nonneg _ := apply_nonneg l _
  zero := by
    have : τ 0 = 1 := by simpa using hτ 0 0
    simp only [this, map_one_eq_zero l]
  add M N := hτ M N ▸ map_mul_le_add l _ _
  digit _ e i := DM_digit l hC τ hτ e i

variable {f : Matrix ι ι F2 → ℝ} {m : ℕ} {s : ℝ}

theorem Good.dg_zero (h : Good f m s) : DM f (dg (∅ : Finset ι)) = 0 := by
  simp [DM, dg_empty, h.zero]

end Cslib.Circuits.Arithmetic.Separation.Flag
