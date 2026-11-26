/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.LinearAlgebra.Tensor.Party.WireExponent

/-!
# Prices

Definition A.4 (def:price) of *VP ≠ VNP over every field* [AnthropicVPVNP2026]. A *price* on a
finite set `V` is a limit of multiples `c • F.wireExponent`, `c ≥ 0`, of the wire exponents of
spectral points `F` on `V` (`Cslib.PartyTensor.prices`, the closure of
`Cslib.PartyTensor.priceCone`). A function on the pairs of any set `Y` is a price
(`Cslib.PartyTensor.IsPrice`) if all its pull-backs to finite sets are prices.

Prices are pseudometrics. They are closed under pull-backs, multiples and pointwise limits, and the
prices below a given function form a compact set.

## Main definitions

* `Cslib.PartyTensor.priceCone`, `Cslib.PartyTensor.prices`, `Cslib.PartyTensor.IsPrice`.
* `Cslib.PartyTensor.wires`: a product of wires (`Nc.Price.Network`).

## Main results

* `Cslib.PartyTensor.isPrice_iff_forall_exists`: the definition by approximation.
* `Cslib.PartyTensor.IsPrice.nonneg`, `IsPrice.self`, `IsPrice.symm`, `IsPrice.triangle`: prices are
  pseudometrics.
* `Cslib.PartyTensor.IsPrice.comp`, `IsPrice.smul`, `Cslib.PartyTensor.isClosed_setOf_isPrice`,
  `Cslib.PartyTensor.isPrice_of_tendsto`, `Cslib.PartyTensor.isCompact_setOf_isPrice_le`.
* `Cslib.PartyTensor.unit_two_entry` (over a commutative semiring): the entries of a unit tensor
  with two legs.
* `Cslib.PartyTensor.SpectralPoint.apply_wires`: a spectral point at a product of wires.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Definition A.4 of the paper; modules `Nc.Price.Basic`, `Nc.Price.Network` and
  `Paper.Prices` (the definition and its properties)
-/

public section

namespace Cslib.PartyTensor

open Finset Filter

section Field

variable {K : Type} [Field K]

section Finite

variable (K) in
/-- The multiples `c • F.wireExponent`, `c ≥ 0`, of the wire exponents of spectral points. -/
def priceCone (V : Type) [Fintype V] [DecidableEq V] : Set (V → V → ℝ) :=
  {d | ∃ (F : SpectralPoint K V) (c : ℝ), 0 ≤ c ∧ d = fun u v => c * F.wireExponent u v}

variable (K) in
/-- The prices on a finite set of parties: the closure of `priceCone`. -/
def prices (V : Type) [Fintype V] [DecidableEq V] : Set (V → V → ℝ) := closure (priceCone K V)

variable {U V : Type} [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]

theorem priceCone_comp (f : U → V) {d : V → V → ℝ} (h : d ∈ priceCone K V) :
    (fun a b => d (f a) (f b)) ∈ priceCone K U := by
  obtain ⟨F, c, hc, rfl⟩ := h
  exact ⟨F.pull f, c, hc, by funext a b; rw [F.pull_wireExponent]⟩

omit [Field K] in
private theorem continuous_comp {X Y : Type*} (f : X → Y) :
    Continuous fun (d : Y → Y → ℝ) (a b : X) => d (f a) (f b) := by
  fun_prop

theorem prices_comp (f : U → V) {d : V → V → ℝ} (h : d ∈ prices K V) :
    (fun a b => d (f a) (f b)) ∈ prices K U :=
  map_mem_closure (continuous_comp f) h fun _ hd => priceCone_comp f hd

theorem priceCone_smul {d : V → V → ℝ} (h : d ∈ priceCone K V) {c : ℝ} (hc : 0 ≤ c) :
    (fun a b => c * d a b) ∈ priceCone K V := by
  obtain ⟨F, c', hc', rfl⟩ := h
  exact ⟨F, c * c', mul_nonneg hc hc', by funext a b; ring⟩

theorem prices_smul {d : V → V → ℝ} (h : d ∈ prices K V) {c : ℝ} (hc : 0 ≤ c) :
    (fun a b => c * d a b) ∈ prices K V :=
  map_mem_closure (f := fun (d : V → V → ℝ) a b => c * d a b) (by fun_prop) h
    fun _ hd => priceCone_smul hd hc

/-- A closed property of the wire exponents of spectral points that is kept by multiples holds for
prices. -/
theorem prices_induction {d : V → V → ℝ} (h : d ∈ prices K V) {S : Set (V → V → ℝ)}
    (hS : IsClosed S)
    (hF : ∀ (F : SpectralPoint K V) (c : ℝ), 0 ≤ c → (fun u v => c * F.wireExponent u v) ∈ S) :
    d ∈ S := by
  refine closure_minimal ?_ hS h
  rintro _ ⟨F, c, hc, rfl⟩
  exact hF F c hc

end Finite

section General

variable (K) in
/-- A function `w` on the pairs of a set `Y` is a *price* if all its pull-backs to finite sets are.
-/
def IsPrice {Y : Type*} (w : Y → Y → ℝ) : Prop :=
  ∀ (n : ℕ) (f : Fin n → Y), (fun i j => w (f i) (f j)) ∈ prices K (Fin n)

variable {Y : Type*} {w : Y → Y → ℝ}

theorem IsPrice.mem (h : IsPrice K w) {V : Type} [Fintype V] [DecidableEq V] (g : V → Y) :
    (fun a b => w (g a) (g b)) ∈ prices K V := by
  simpa using prices_comp (Fintype.equivFin V) (h _ fun i => g ((Fintype.equivFin V).symm i))

theorem isPrice_of_mem {V : Type} [Fintype V] [DecidableEq V] {d : V → V → ℝ}
    (h : d ∈ prices K V) : IsPrice K d := fun _ f => prices_comp f h

/-- The wire exponent of a spectral point is a price. -/
theorem isPrice_wireExponent {V : Type} [Fintype V] [DecidableEq V] (F : SpectralPoint K V) :
    IsPrice K F.wireExponent :=
  isPrice_of_mem (subset_closure ⟨F, 1, zero_le_one, by simp⟩)

/-- A function is a price if its restrictions to finite subsets are. -/
theorem isPrice_of_finset (h : ∀ S : Finset Y, IsPrice K fun a b : S => w a b) : IsPrice K w := by
  classical
  intro n f
  exact h (Finset.univ.image f) n fun i => ⟨f i, by simp⟩

/-- Approximation by the wire exponent of a spectral point. -/
theorem IsPrice.exists_spectralPoint (h : IsPrice K w) {V : Type} [Fintype V] [DecidableEq V]
    (g : V → Y) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (F : SpectralPoint K V) (c : ℝ), 0 ≤ c ∧
      ∀ a b, |w (g a) (g b) - c * F.wireExponent a b| < δ := by
  obtain ⟨d, ⟨F, c, hc, rfl⟩, hd⟩ := Metric.mem_closure_iff.1 (h.mem g) δ hδ
  exact ⟨F, c, hc, fun a b =>
    Real.dist_eq _ _ ▸ (dist_pi_lt_iff hδ).1 ((dist_pi_lt_iff hδ).1 hd a) b⟩

/-- `0` is a price. -/
theorem isPrice_zero : IsPrice K fun _ _ : Y => 0 := fun n _ =>
  subset_closure ⟨SpectralPoint.support K (Fin n), 0, le_rfl, by simp⟩

/-- **Paper: Definition A.4 (def:price).** A price on a finite set `V` is a limit of multiples
`s · d_φ`, `s ≥ 0`, with `φ` a spectral point on `V`; a function on the pairs of an arbitrary set
`Y` is a price if all its pull-backs to finite sets are prices. -/
theorem isPrice_iff_forall_exists {V : Type} [Fintype V] [DecidableEq V] (d : V → V → ℝ) :
    IsPrice K d ↔ ∀ δ : ℝ, 0 < δ → ∃ (F : SpectralPoint K V) (s : ℝ), 0 ≤ s ∧
      ∀ u v, |d u v - s * F.wireExponent u v| < δ := by
  refine ⟨fun h δ hδ => h.exists_spectralPoint id hδ, fun h => isPrice_of_mem ?_⟩
  rw [prices, Metric.mem_closure_iff]
  intro δ hδ
  obtain ⟨F, s, hs, hd⟩ := h δ hδ
  refine ⟨_, ⟨F, s, hs, rfl⟩, (dist_pi_lt_iff hδ).2 fun u => (dist_pi_lt_iff hδ).2 fun v => ?_⟩
  rw [Real.dist_eq]
  exact hd u v

/-- Prices are pseudometrics. By Lemma A.2 the wire exponents are, and the conditions are closed and
kept by multiples. -/
private theorem isPseudometric (h : IsPrice K w) :
    (∀ a b, 0 ≤ w a b) ∧ (∀ a, w a a = 0) ∧ (∀ a b, w a b = w b a) ∧
      ∀ a b c, w a c ≤ w a b + w b c := by
  refine ⟨fun a b => prices_induction (S := {d | 0 ≤ d 0 1}) (h 2 ![a, b])
      (isClosed_le continuous_const (by fun_prop))
      fun F c hc => mul_nonneg hc (F.wireExponent_nonneg 0 1),
    fun a => prices_induction (S := {d | d 0 0 = 0}) (h 1 ![a])
      (isClosed_eq (by fun_prop) continuous_const)
      fun F c _ => by simp [F.wireExponent_self],
    fun a b => prices_induction (S := {d | d 0 1 = d 1 0}) (h 2 ![a, b])
      (isClosed_eq (by fun_prop) (by fun_prop))
      fun F c _ => congrArg (c * ·) (F.wireExponent_comm 0 1),
    fun a b c => prices_induction (S := {d | d 0 2 ≤ d 0 1 + d 1 2}) (h 3 ![a, b, c])
      (isClosed_le (by fun_prop) (by fun_prop))
      fun F s hs => (mul_le_mul_of_nonneg_left (F.wireExponent_triangle 0 1 2) hs).trans_eq
        (mul_add _ _ _)⟩

theorem IsPrice.nonneg (h : IsPrice K w) (a b : Y) : 0 ≤ w a b := (isPseudometric h).1 a b

theorem IsPrice.self (h : IsPrice K w) (a : Y) : w a a = 0 := (isPseudometric h).2.1 a

theorem IsPrice.symm (h : IsPrice K w) (a b : Y) : w a b = w b a := (isPseudometric h).2.2.1 a b

theorem IsPrice.triangle (h : IsPrice K w) (a b c : Y) : w a c ≤ w a b + w b c :=
  (isPseudometric h).2.2.2 a b c

/-- Pull-backs of prices are prices. -/
theorem IsPrice.comp {Z : Type*} (h : IsPrice K w) (g : Z → Y) :
    IsPrice K fun a b => w (g a) (g b) :=
  fun n f => h n fun i => g (f i)

/-- Nonnegative multiples of prices are prices. -/
theorem IsPrice.smul (h : IsPrice K w) {c : ℝ} (hc : 0 ≤ c) : IsPrice K fun a b => c * w a b :=
  fun n f => prices_smul (h n f) hc

variable (K) in
/-- The set of prices is closed under pointwise convergence. -/
theorem isClosed_setOf_isPrice : IsClosed {w : Y → Y → ℝ | IsPrice K w} := by
  simp only [IsPrice, prices, Set.ofPred_forall]
  exact isClosed_iInter fun _ => isClosed_iInter fun f =>
    isClosed_closure.preimage (continuous_comp f)

/-- Pointwise limits of prices are prices. -/
theorem isPrice_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] {d : ι → Y → Y → ℝ}
    (h : ∀ a b, Tendsto (fun i => d i a b) l (nhds (w a b))) (hd : ∀ᶠ i in l, IsPrice K (d i)) :
    IsPrice K w :=
  (isClosed_setOf_isPrice K).mem_of_tendsto
    (tendsto_pi_nhds.2 fun a => tendsto_pi_nhds.2 (h a)) hd

variable (K) in
/-- The prices below a given function form a compact set, by Tychonoff's theorem. -/
theorem isCompact_setOf_isPrice_le (C : Y → Y → ℝ) :
    IsCompact {w : Y → Y → ℝ | IsPrice K w ∧ ∀ a b, w a b ≤ C a b} := by
  have h1 : IsCompact {w : Y → Y → ℝ | ∀ a, w a ∈ {v : Y → ℝ | ∀ b, v b ∈ Set.Icc 0 (C a b)}} :=
    isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => isCompact_Icc
  have h2 : IsClosed {w : Y → Y → ℝ | ∀ a b, w a b ≤ C a b} := by
    simpa only [Set.ofPred_forall] using
      isClosed_iInter fun _ => isClosed_iInter fun _ =>
        isClosed_le (by fun_prop) continuous_const
  exact h1.of_isClosed_subset ((isClosed_setOf_isPrice K).inter h2)
    fun _ ⟨hw, hC⟩ a b => ⟨hw.nonneg a b, hC a b⟩

end General

end Field

section CommSemiring

variable {K : Type} [CommSemiring K]

/-- The entries of the unit tensor with two legs (a wire before it is placed). -/
theorem unit_two_entry {n : ℕ} (y : Fin 2 → Fin n) :
    (unit K (Fin 2) n).entry y = if y 0 = y 1 then 1 else 0 := by
  have key : (∀ i j, y i = y j) ↔ y 0 = y 1 := by
    simp only [Fin.forall_fin_two]
    exact ⟨fun h => h.1.2, fun h => ⟨⟨trivial, h⟩, h.symm, trivial⟩⟩
  by_cases h : y 0 = y 1
  · rw [unit_entry_of (key.2 h), ite_eq_left h]
  · rw [unit_entry_of_not (mt key.1 h), ite_eq_right h]

variable {I E : Type} [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E]

variable (K) in
/-- A product of wires: one of dimension `n e` from `a e` to `b e` for every `e`. -/
@[expose] def wires (a b : E → I) (n : E → ℕ) : PartyTensor K I :=
  prod fun e => wire K (n e) (a e) (b e)

end CommSemiring

/-- A spectral point at a product of wires of dimensions `n e ≥ 1`. -/
theorem SpectralPoint.apply_wires {K : Type} [Field K] {I E : Type} [Fintype I] [DecidableEq I]
    [Fintype E] [DecidableEq E] (F : SpectralPoint K I) (a b : E → I) {n : E → ℕ}
    (hn : ∀ e, 1 ≤ n e) : F (wires K a b n) = ∏ e, (n e : ℝ) ^ F.wireExponent (a e) (b e) := by
  rw [wires, F.map_prod]
  exact Finset.prod_congr rfl fun e _ => F.apply_wire _ _ (hn e)

end Cslib.PartyTensor
