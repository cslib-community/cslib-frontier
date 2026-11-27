/-
Copyright (c) 2026 Richard Dodson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Dodson
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-!
# The quadratic network for modular addition

The one-hidden-layer network of open problem MAIS-O6 of [Levine2026, Section 5.1]. On an input
`(a, b)` in `(ℤ/p)²` it computes

`f_w(a, b) = ∑ j, V_j (u'_j(a) + u''_j(b))² ∈ ℝ^p`,

and it is trained to output the coordinate vector indexed by `a + b`. The `j`th summand is one
hidden neuron: it adds two entries of the lookup tables `u'_j, u''_j : ℤ/p → ℝ`, squares the
result and writes the vector `V_j` to the output.

The source gives the network, the exception for neurons whose contribution vanishes
identically, and the single-frequency form: for some `k`, both lookup tables of a neuron are a
constant plus a linear combination of `cos (2π k · / p)` and `sin (2π k · / p)`. The problem's
page in the source's repository names [MAISA6, Conjecture 4.9] as its formalization, and this
module follows [MAISA6, Section 4] for what that document makes explicit:

* an *exact fit* is a parameter at which the network equals the target on every input
  ([MAISA6], the set `W₀(p, H)`; the source uses the term without a displayed definition);
* a neuron is *active* when its contribution `(a, b) ↦ V_j (u'_j(a) + u''_j(b))²` is not
  identically zero ([MAISA6], before Conjecture 4.9), which is the complement of the source's
  exception;
* in the *single-frequency form* the frequency ranges over `0 ≤ k ≤ (p - 1) / 2` in [MAISA6],
  with `k = 0` giving the constant tables;
* the loss is half the mean squared error.

The parameter space is a Euclidean space, so that its norm is the Euclidean norm of the whole
parameter vector and it carries Lebesgue measure, as [MAISA6] uses for the ball and for the
local learning coefficient. Neurons are indexed by an arbitrary finite type; width `H` is
`Fin H`.

## Main definitions

* `Cslib.MachineLearning.ModularAddition.Params`: the parameter space.
* `Cslib.MachineLearning.ModularAddition.net`, `target`, `loss`: the network, its target and
  half the mean squared error.
* `Cslib.MachineLearning.ModularAddition.IsExactFit`, `IsActive`, `IsSingleFrequency`.

## Main results

* `Cslib.MachineLearning.ModularAddition.loss_eq_zero_iff`: the exact fits are the zeros of the
  loss.
* `Cslib.MachineLearning.ModularAddition.not_isActive_iff`: a neuron is inactive exactly when
  its output vector is zero or its tables are opposite constants.
* `Cslib.MachineLearning.ModularAddition.isSingleFrequency_iff_exists_le`: for odd `p` the
  frequency may be taken in `0, …, (p - 1) / 2`.

## References

* [L. Levine, *Math for AI safety: an invitation for mathematicians*, Section 5.1][Levine2026]
* [*Does geometric simplicity force a legible mechanism? Singular geometry of modular
  addition*, agenda MAIS-A6, Section 4][MAISA6]
-/

public section

namespace Cslib.MachineLearning.ModularAddition

open scoped Real

variable {p : ℕ} [NeZero p] {ι : Type} [Fintype ι]

/-- The parameter space for modulus `p` and hidden neurons indexed by `ι`: for each neuron its
two lookup tables and its output vector, `3 p` real numbers, with the Euclidean norm of the
whole parameter vector ([MAISA6, Section 4], where `d = 3 p H`). -/
abbrev Params (p : ℕ) (ι : Type) : Type := EuclideanSpace ℝ (ι × Fin 3 × ZMod p)

/-- The first lookup table `u'_j` of neuron `j`. -/
@[expose] def left (w : Params p ι) (j : ι) (a : ZMod p) : ℝ := w (j, 0, a)

/-- The second lookup table `u''_j` of neuron `j`. -/
@[expose] def right (w : Params p ι) (j : ι) (b : ZMod p) : ℝ := w (j, 1, b)

/-- The output vector `V_j` of neuron `j`. -/
@[expose] def out (w : Params p ι) (j : ι) (c : ZMod p) : ℝ := w (j, 2, c)

/-- The parameter with the given tables and output vectors. -/
@[expose] def Params.mk (l r o : ι → ZMod p → ℝ) : Params p ι :=
  WithLp.toLp 2 fun ⟨j, i, a⟩ => ![l j a, r j a, o j a] i

omit [NeZero p] [Fintype ι] in
@[simp] theorem left_mk (l r o : ι → ZMod p → ℝ) : left (Params.mk l r o) = l := rfl

omit [NeZero p] [Fintype ι] in
@[simp] theorem right_mk (l r o : ι → ZMod p → ℝ) : right (Params.mk l r o) = r := rfl

omit [NeZero p] [Fintype ι] in
@[simp] theorem out_mk (l r o : ι → ZMod p → ℝ) : out (Params.mk l r o) = o := rfl

/-- The contribution of neuron `j`: the function `(a, b) ↦ V_j (u'_j(a) + u''_j(b))²`, at the
output coordinate `c`. -/
@[expose] def contribution (w : Params p ι) (j : ι) (a b c : ZMod p) : ℝ :=
  out w j c * (left w j a + right w j b) ^ 2

/-- The network `f_w(a, b) = ∑ j, V_j (u'_j(a) + u''_j(b))²` of [Levine2026, Section 5.1], at
the output coordinate `c`. -/
@[expose] def net (w : Params p ι) (a b c : ZMod p) : ℝ := ∑ j, contribution w j a b c

/-- The target: the coordinate vector indexed by `a + b`. -/
@[expose] def target (a b c : ZMod p) : ℝ := if c = a + b then 1 else 0

/-- The residual of the network on all inputs and output coordinates, as a vector with `p ^ 3`
entries. -/
@[expose] def residual (w : Params p ι) : EuclideanSpace ℝ (ZMod p × ZMod p × ZMod p) :=
  WithLp.toLp 2 fun ⟨a, b, c⟩ => net w a b c - target a b c

/-- The loss: half the mean squared error over the `p ^ 2` inputs, the function `K` of
[MAISA6, Section 4]. [Levine2026, Section 5.1] says "squared-error loss averaged over all
`p ^ 2` inputs" and does not display a prefactor; a positive factor does not change the local
learning coefficient. -/
@[expose] noncomputable def loss (w : Params p ι) : ℝ := ‖residual w‖ ^ 2 / (2 * (p : ℝ) ^ 2)

/-- An exact fit: the network equals the target on every input. This is the set `W₀(p, H)` of
[MAISA6, Section 4]; [Levine2026, Section 5.1] uses the term without a displayed definition. -/
@[expose] def IsExactFit (w : Params p ι) : Prop := ∀ a b c, net w a b c = target a b c

/-- The exact fits are the zeros of the loss. -/
theorem loss_eq_zero_iff (w : Params p ι) : loss w = 0 ↔ IsExactFit w := by
  have hp : (2 * (p : ℝ) ^ 2) ≠ 0 := by
    have : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne p)
    positivity
  rw [loss, div_eq_zero_iff, or_iff_left hp, sq_eq_zero_iff, norm_eq_zero]
  constructor
  · intro h a b c
    have := congrArg (fun v : EuclideanSpace ℝ (ZMod p × ZMod p × ZMod p) => v (a, b, c)) h
    exact sub_eq_zero.1 this
  · intro h
    ext ⟨a, b, c⟩
    exact sub_eq_zero.2 (h a b c)

/-! ### Active neurons -/

/-- A neuron is active when its contribution is not identically zero. [Levine2026, Section 5.1]
states the exception per neuron, "apart from neurons whose contribution vanishes identically";
[MAISA6], before Conjecture 4.9, names the complement: these are the neurons that are not
active. -/
@[expose] def IsActive (w : Params p ι) (j : ι) : Prop := ∃ a b c, contribution w j a b c ≠ 0

omit [Fintype ι] in
/-- A neuron is inactive exactly when its output vector is zero or its two tables are opposite
constants. -/
theorem not_isActive_iff (w : Params p ι) (j : ι) :
    ¬ IsActive w j ↔ out w j = 0 ∨ ∃ t : ℝ, (∀ a, left w j a = t) ∧ ∀ b, right w j b = -t := by
  simp only [IsActive, not_exists, not_not, contribution, mul_eq_zero, sq_eq_zero_iff]
  constructor
  · intro h
    by_cases ho : out w j = 0
    · exact Or.inl ho
    · obtain ⟨c, hc⟩ := Function.ne_iff.1 ho
      have hsum : ∀ a b, left w j a + right w j b = 0 := fun a b => (h a b c).resolve_left hc
      refine Or.inr ⟨left w j 0, fun a => ?_, fun b => ?_⟩
      · linarith [hsum a 0, hsum 0 0]
      · linarith [hsum 0 b]
  · rintro (ho | ⟨t, hl, hr⟩) a b c
    · exact Or.inl (congrFun ho c)
    · exact Or.inr (by rw [hl, hr]; ring)

/-! ### Single-frequency form -/

/-- The cosine table of frequency `k`: `a ↦ cos (2π k a / p)`. -/
@[expose] noncomputable def cosTable (p k : ℕ) (a : ZMod p) : ℝ := Real.cos (2 * π * k * a.val / p)

/-- The sine table of frequency `k`: `a ↦ sin (2π k a / p)`. -/
@[expose] noncomputable def sinTable (p k : ℕ) (a : ZMod p) : ℝ := Real.sin (2 * π * k * a.val / p)

/-- The tables of frequency `k`: a constant plus a combination of `cos (2π k · / p)` and
`sin (2π k · / p)`. This is `F₀ + F_k` of [MAISA6]. Frequency `0` gives the constants, and `k`
and `p - k` give the same space, for `k ≤ p`. -/
@[expose] noncomputable def freqSpace (p k : ℕ) : Submodule ℝ (ZMod p → ℝ) :=
  Submodule.span ℝ {fun _ => 1, cosTable p k, sinTable p k}

/-- A neuron has single-frequency form: for some `k`, both of its lookup tables are a constant
plus a linear combination of `cos (2π k · / p)` and `sin (2π k · / p)`
([Levine2026, Section 5.1]). One frequency serves both tables of the neuron, different neurons
may use different frequencies, and `k = 0` is allowed, as in [MAISA6]. -/
@[expose] def IsSingleFrequency (w : Params p ι) (j : ι) : Prop :=
  ∃ k : ℕ, left w j ∈ freqSpace p k ∧ right w j ∈ freqSpace p k

theorem one_mem_freqSpace (p k : ℕ) : (fun _ : ZMod p => (1 : ℝ)) ∈ freqSpace p k :=
  Submodule.subset_span (by simp)

theorem cosTable_mem_freqSpace (p k : ℕ) : cosTable p k ∈ freqSpace p k :=
  Submodule.subset_span (by simp)

theorem sinTable_mem_freqSpace (p k : ℕ) : sinTable p k ∈ freqSpace p k :=
  Submodule.subset_span (by simp)

/-- The constant tables have every frequency. -/
theorem const_mem_freqSpace (p k : ℕ) (t : ℝ) : (fun _ : ZMod p => t) ∈ freqSpace p k := by
  have h := Submodule.smul_mem _ t (one_mem_freqSpace p k)
  have heq : t • (fun _ : ZMod p => (1 : ℝ)) = fun _ => t := by
    funext a
    simp
  rwa [heq] at h

omit [NeZero p] in
private theorem angle_add_mul (k q : ℕ) (a : ZMod p) (hp : (p : ℝ) ≠ 0) :
    2 * π * ((k + p * q : ℕ) : ℝ) * a.val / p =
      2 * π * k * a.val / p + ((q * a.val : ℕ) : ℝ) * (2 * π) := by
  push_cast
  field_simp

omit [NeZero p] in
private theorem angle_sub (k : ℕ) (hk : k ≤ p) (a : ZMod p) (hp : (p : ℝ) ≠ 0) :
    2 * π * ((p - k : ℕ) : ℝ) * a.val / p =
      (a.val : ℝ) * (2 * π) - 2 * π * k * a.val / p := by
  rw [Nat.cast_sub hk]
  field_simp

theorem cosTable_add_mul (k q : ℕ) : cosTable p (k + p * q) = cosTable p k := by
  funext a
  rw [cosTable, cosTable, angle_add_mul k q a (Nat.cast_ne_zero.2 (NeZero.ne p)),
    Real.cos_add_nat_mul_two_pi]

theorem sinTable_add_mul (k q : ℕ) : sinTable p (k + p * q) = sinTable p k := by
  funext a
  rw [sinTable, sinTable, angle_add_mul k q a (Nat.cast_ne_zero.2 (NeZero.ne p)),
    Real.sin_add_nat_mul_two_pi]

theorem cosTable_sub (k : ℕ) (hk : k ≤ p) : cosTable p (p - k) = cosTable p k := by
  funext a
  rw [cosTable, cosTable, angle_sub k hk a (Nat.cast_ne_zero.2 (NeZero.ne p)),
    Real.cos_nat_mul_two_pi_sub]

theorem sinTable_sub (k : ℕ) (hk : k ≤ p) : sinTable p (p - k) = -sinTable p k := by
  funext a
  rw [Pi.neg_apply, sinTable, sinTable, angle_sub k hk a (Nat.cast_ne_zero.2 (NeZero.ne p)),
    Real.sin_nat_mul_two_pi_sub]

/-- The frequency matters only modulo `p`. -/
theorem freqSpace_mod (p k : ℕ) [NeZero p] : freqSpace p (k % p) = freqSpace p k := by
  conv_rhs => rw [← Nat.mod_add_div k p]
  rw [freqSpace, freqSpace, cosTable_add_mul, sinTable_add_mul]

/-- The frequencies `k` and `p - k` give the same tables, for `k ≤ p`. For a larger `k`, reduce
it modulo `p` first (`freqSpace_mod`). -/
theorem freqSpace_sub (p k : ℕ) [NeZero p] (hk : k ≤ p) : freqSpace p (p - k) = freqSpace p k := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro f (rfl | rfl | rfl)
    · exact one_mem_freqSpace p k
    · rw [cosTable_sub k hk]
      exact cosTable_mem_freqSpace p k
    · rw [sinTable_sub k hk]
      exact Submodule.neg_mem _ (sinTable_mem_freqSpace p k)
  · rintro f (rfl | rfl | rfl)
    · exact one_mem_freqSpace p (p - k)
    · rw [← cosTable_sub k hk]
      exact cosTable_mem_freqSpace p (p - k)
    · rw [← neg_neg (sinTable p k), ← sinTable_sub k hk]
      exact Submodule.neg_mem _ (sinTable_mem_freqSpace p (p - k))

omit [Fintype ι] in
/-- For odd `p` the frequency of a single-frequency neuron may be taken in the range
`0, …, (p - 1) / 2` of [MAISA6]. -/
theorem isSingleFrequency_iff_exists_le (hp : Odd p) (w : Params p ι) (j : ι) :
    IsSingleFrequency w j ↔
      ∃ k ≤ (p - 1) / 2, left w j ∈ freqSpace p k ∧ right w j ∈ freqSpace p k := by
  refine ⟨fun ⟨k, hl, hr⟩ => ?_, fun ⟨k, _, h⟩ => ⟨k, h⟩⟩
  have hpos : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hlt : k % p < p := Nat.mod_lt k hpos
  obtain ⟨n, hn⟩ := hp
  rw [← freqSpace_mod p k] at hl hr
  by_cases hsmall : k % p ≤ (p - 1) / 2
  · exact ⟨k % p, hsmall, hl, hr⟩
  · refine ⟨p - k % p, by omega, ?_, ?_⟩
    · rwa [freqSpace_sub p (k % p) hlt.le]
    · rwa [freqSpace_sub p (k % p) hlt.le]

omit [NeZero p] [Fintype ι] in
/-- A neuron with constant tables has single-frequency form, with frequency `0`. In particular
an inactive neuron with a nonzero output vector does. -/
theorem isSingleFrequency_of_const (w : Params p ι) (j : ι) (t s : ℝ)
    (hl : ∀ a, left w j a = t) (hr : ∀ b, right w j b = s) : IsSingleFrequency w j := by
  refine ⟨0, ?_, ?_⟩
  · rw [show left w j = fun _ => t from funext hl]
    exact const_mem_freqSpace p 0 t
  · rw [show right w j = fun _ => s from funext hr]
    exact const_mem_freqSpace p 0 s

/-! ### Padding -/

section Extend

variable {κ : Type} [Fintype κ]

omit [NeZero p] [Fintype ι] [Fintype κ] in
private theorem prodMap_injective (e : ι ↪ κ) :
    Function.Injective fun x : ι × Fin 3 × ZMod p => (e x.1, x.2) := fun x y h => by
  obtain ⟨h1, h2⟩ := Prod.mk.inj h
  exact Prod.ext (e.injective h1) h2

/-- Padding: the parameter on the neurons `κ` that agrees with `w` on the image of `e` and is
zero on every other neuron. With `e` an embedding of the neurons of a narrow network into those
of a wider one, this adds neurons whose tables and output vectors are zero, as [MAISA6] does to
carry the Fourier fit to every width `H ≥ 2 p - 1`. -/
@[expose] noncomputable def extend (e : ι ↪ κ) (w : Params p ι) : Params p κ :=
  WithLp.toLp 2 (Function.extend (fun x : ι × Fin 3 × ZMod p => (e x.1, x.2)) (WithLp.ofLp w) 0)

omit [NeZero p] [Fintype ι] [Fintype κ] in
/-- Padding agrees with the parameter on the image of the embedding. -/
theorem extend_apply (e : ι ↪ κ) (w : Params p ι) (j : ι) (x : Fin 3 × ZMod p) :
    extend e w (e j, x) = w (j, x) :=
  (prodMap_injective e).extend_apply _ _ (j, x)

omit [NeZero p] [Fintype ι] [Fintype κ] in
/-- Padding is zero on the neurons outside the image of the embedding. -/
theorem extend_apply_of_forall_ne (e : ι ↪ κ) (w : Params p ι) {j' : κ} (h : ∀ j, e j ≠ j')
    (x : Fin 3 × ZMod p) : extend e w (j', x) = 0 :=
  Function.extend_apply' _ _ _ (by
    rintro ⟨y, hy⟩
    exact h y.1 (congrArg Prod.fst hy))

omit [NeZero p] in
/-- Padding does not change the network. -/
theorem net_extend (e : ι ↪ κ) (w : Params p ι) : net (extend e w) = net w := by
  funext a b c
  have hzero : ∀ j' ∈ (Finset.univ : Finset κ), j' ∉ Finset.univ.map e →
      contribution (extend e w) j' a b c = 0 := by
    intro j' _ hj'
    have hne : ∀ j, e j ≠ j' := fun j hj => hj' (Finset.mem_map.2 ⟨j, Finset.mem_univ j, hj⟩)
    simp [contribution, out, extend_apply_of_forall_ne e w hne]
  rw [net, ← Finset.sum_subset (Finset.subset_univ (Finset.univ.map e)) hzero, Finset.sum_map]
  simp [net, contribution, out, left, right, extend_apply]

omit [NeZero p] in
/-- Padding preserves exact fits. -/
theorem isExactFit_extend (e : ι ↪ κ) (w : Params p ι) :
    IsExactFit (extend e w) ↔ IsExactFit w := by
  simp only [IsExactFit, net_extend]

/-- Padding preserves the norm. -/
theorem norm_extend (e : ι ↪ κ) (w : Params p ι) : ‖extend e w‖ = ‖w‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  have hzero : ∀ y ∈ (Finset.univ : Finset (κ × Fin 3 × ZMod p)),
      y ∉ Finset.univ.map ⟨_, prodMap_injective (p := p) e⟩ → ‖extend e w y‖ ^ 2 = 0 := by
    intro y _ hy
    have hne : ∀ j, e j ≠ y.1 := fun j hj => hy (Finset.mem_map.2 ⟨(j, y.2), Finset.mem_univ _,
      Prod.ext hj rfl⟩)
    rw [show y = (y.1, y.2) from rfl, extend_apply_of_forall_ne e w hne]
    simp
  rw [← Finset.sum_subset (Finset.subset_univ _) hzero, Finset.sum_map]
  exact Finset.sum_congr rfl fun x _ => by
    rw [Function.Embedding.coeFn_mk, show x = (x.1, x.2) from rfl, extend_apply]

end Extend

end Cslib.MachineLearning.ModularAddition
