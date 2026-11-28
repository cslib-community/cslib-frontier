/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.LinearAlgebra.Tensor.Party.WireExponent
public import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Covers up to `ε`, and sums with few terms

`t.BorderCoveredBy D b`: the tensor `t` is a sum of restrictions of the `b k` up to `ε`, with
denominators at most `ε ^ D`. The local maps have entries in `K[ε]`, and the sum of the
`localApply (L k) (C ∘ (b k).entry)` is `ε ^ D • t` plus higher powers of `ε`. For `D = 0` this is
the exact relation `t.CoveredBy b` (`Cslib.PartyTensor.borderCoveredBy_zero_iff`).

Lemma N.3 of *VP ≠ VNP over every field* [AnthropicVPVNP2026] bounds a spectral point at such a
sum with few terms: `F t ≤ |κ| ^ g · max_k F (b k)`, where `g` is the unit exponent of the parties
that hold legs of `t` (`Cslib.PartyTensor.SpectralPoint.apply_le_of_borderCoveredBy`). The proof
takes tensor powers `t^N`, sorts the words of `N` terms by their types, extracts the coefficient
of `ε ^ (N D)` at the cost of a factor polynomial in `N`, and takes `N`-th roots.

## Main definitions

* `Cslib.PartyTensor.BorderCoveredBy`: covers up to `ε`.

## Main results

* `Cslib.PartyTensor.borderCoveredBy_zero_iff`, `Cslib.PartyTensor.CoveredBy.borderCoveredBy`.
* `Cslib.PartyTensor.SpectralPoint.apply_le_of_borderCoveredBy`: Lemma N.3.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Lemma N.3 (§N.2) of the paper; modules `Nc.Rate.Defs` (`BSum`), `Nc.Price.BorderSum` and
  `Nc.Price.BorderFew` (`few`)
-/

public section

namespace Cslib.PartyTensor

open Finset Polynomial

section CommSemiring

variable {K : Type} [CommSemiring K] {I : Type} [Fintype I] [DecidableEq I] {κ : Type} [Fintype κ]

/-- `t` is a sum of restrictions of the `b k` up to `ε`, with denominators at most `ε ^ D`: with
local maps that are polynomials in `ε`, the sum is `ε ^ D • t + ε ^ (D + 1) • (anything)`. The
coefficients of `ε ^ i`, `i ≤ D`, of `∑ k, localApply (L k) (C ∘ (b k).entry) x` are `0` for
`i < D` and `t.entry x` for `i = D`. -/
@[expose] def BorderCoveredBy (t : PartyTensor K I) (D : ℕ)
    (b : κ → PartyTensor K I) : Prop :=
  ∃ L : ∀ k p, t.Index p → (b k).Index p → K[X], ∀ x, ∀ i ≤ D,
    (∑ k, localApply (L k) (fun y => C ((b k).entry y)) x).coeff i = if i = D then t.entry x else 0

/-- An exact cover is a cover up to `ε` with `D = 0`, by constant local maps. -/
theorem CoveredBy.borderCoveredBy {t : PartyTensor K I} {b : κ → PartyTensor K I}
    (h : t.CoveredBy b) : t.BorderCoveredBy 0 b := by
  obtain ⟨L, hL⟩ := h
  refine ⟨fun k p a c => C (L k p a c), fun x i hi => ?_⟩
  obtain rfl : i = 0 := Nat.le_zero.1 hi
  simp [hL x, localApply, Polynomial.coeff_zero_prod]

/-- A cover up to `ε` with `D = 0` is an exact cover: evaluate the local maps at `ε = 0`. -/
theorem borderCoveredBy_zero_iff {t : PartyTensor K I} {b : κ → PartyTensor K I} :
    t.BorderCoveredBy 0 b ↔ t.CoveredBy b := by
  refine ⟨fun ⟨L, hL⟩ => ⟨fun k p a c => (L k p a c).eval 0, fun x => ?_⟩,
    CoveredBy.borderCoveredBy⟩
  have h := hL x 0 le_rfl
  rw [ite_eq_left rfl, Polynomial.coeff_zero_eq_eval_zero] at h
  rw [← h]
  simp [localApply, Polynomial.eval_finsetSum, Polynomial.eval_prod]

end CommSemiring

variable {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I]


/-- The array over `K[ε]` that local maps with polynomial entries make of a tensor. -/
private noncomputable def polyApp {α : I → Type} (z : PartyTensor K I)
    (Φ : ∀ p, α p → z.Index p → Polynomial K)
    (x : ∀ p, α p) : Polynomial K :=
  localApply Φ (fun y => C (z.entry y)) x

/-- A product of images of tensors is the image of the product of the tensors. -/
private theorem polyApp_prod {τ : Type} [Fintype τ] [DecidableEq τ] {α : τ → I → Type}
    (b : τ → PartyTensor K I)
    (Φ : ∀ i p, α i p → (b i).Index p → Polynomial K) (x : ∀ p i, α i p) :
    polyApp (α := fun p => ∀ i, α i p) (prod b) (fun p a c => ∏ i, Φ i p (a i) (c i)) x =
      ∏ i, polyApp (b i) (Φ i) fun p => x p i := by
  unfold polyApp
  rw [← localApply_prod]
  congr 1
  funext y
  exact map_prod C _ _

/-- Proof of Lemma N.3, powers: if the images of the `b k` sum to `ε ^ D • t` up to higher powers,
then the products of `N` images, over all words, sum to `ε ^ (N D) • t^N` up to higher powers. -/
private theorem coeff_sum_words {κ : Type} [Fintype κ] {D : ℕ} {t : PartyTensor K I}
    {b : κ → PartyTensor K I}
    {L : ∀ k p, t.Index p → (b k).Index p → Polynomial K}
    (hL : ∀ x, ∀ i ≤ D, (∑ k, polyApp (b k) (L k) x).coeff i = if i = D then t.entry x else 0)
    (N : ℕ) (x : ∀ p, Fin N → t.Index p) {j : ℕ} (hj : j ≤ N * D) :
    (∑ w : Fin N → κ, ∏ i, polyApp (b (w i)) (L (w i)) fun p => x p i).coeff j =
      if j = N * D then ((t ^ N)).entry x else 0 := by
  classical
  rw [← Fintype.prod_sum (f := fun (i : Fin N) k => polyApp (b k) (L k) fun p => x p i)]
  have hQ : ∀ i : Fin N, ∃ Q : Polynomial K, (∑ k, polyApp (b k) (L k) fun p => x p i) = X ^ D * Q ∧
      Q.coeff 0 = t.entry fun p => x p i := by
    intro i
    obtain ⟨Q, hQ⟩ : X ^ D ∣ ∑ k, polyApp (b k) (L k) fun p => x p i :=
      X_pow_dvd_iff.2 fun d hd => (hL _ d hd.le).trans (ite_eq_right hd.ne)
    refine ⟨Q, hQ, ?_⟩
    have := (hL (fun p => x p i) D le_rfl).trans (ite_eq_left rfl)
    rwa [hQ, coeff_X_pow_mul', ite_eq_left le_rfl, Nat.sub_self] at this
  choose Q hQ hQ0 using hQ
  simp only [hQ, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← pow_mul, mul_comm D N, coeff_X_pow_mul']
  rcases eq_or_lt_of_le hj with rfl | hlt
  · rw [ite_eq_left le_rfl, ite_eq_left rfl, Nat.sub_self, coeff_zero_prod]
    exact Finset.prod_congr rfl fun i _ => hQ0 i
  · rw [ite_eq_right hlt.not_ge, ite_eq_right hlt.ne]

/-- The coefficient of ε ^ D of a product of polynomials, as a sum over the choices of the
exponents. -/
private theorem coeff_prod_choices {τ : Type} [Fintype τ] [DecidableEq τ] (f : τ → Polynomial K)
    (D : ℕ) :
    (∏ p, f p).coeff D =
      ∑ d : τ → Fin (D + 1), if (∑ p, (d p).val) = D then ∏ p, (f p).coeff (d p) else 0 := by
  rw [← Polynomial.coeff_coe, show ((∏ p, f p : Polynomial K) : PowerSeries K) = ∏ p,
      (f p : PowerSeries K) from
    map_prod Polynomial.coeToPowerSeries.ringHom f univ, PowerSeries.coeff_prod,
        ← Finset.sum_filter]
  simp only [Polynomial.coeff_coe]
  refine Finset.sum_bij' (fun l hl p => ⟨l p, ?_⟩)
      (fun d _ => Finsupp.equivFunOnFinite.symm fun p => (d p).val)
    ?_ ?_ ?_ ?_ ?_
  · rw [Finset.mem_finsuppAntidiag] at hl
    exact Nat.lt_succ_of_le
        (hl.1 ▸ Finset.single_le_sum (fun q _ => Nat.zero_le (l q)) (Finset.mem_univ p))
  · intro l hl
    rw [Finset.mem_finsuppAntidiag] at hl
    simpa using hl.1
  · exact fun d hd => Finset.mem_finsuppAntidiag.2
      ⟨by simpa using (Finset.mem_filter.1 hd).2, Finset.subset_univ _⟩
  · exact fun l _ => by ext; simp
  · exact fun d _ => by funext; simp
  · exact fun _ _ => rfl

/-- Proof of Lemma N.3, extraction of a coefficient: the coefficient of `ε ^ D` of the image of a
tensor `z` under local maps with polynomial entries is a sum of at most `(D + 1) ^ |I|` restrictions
of `z`, so a spectral point is at most that many times its value at `z`. -/
private theorem le_coeff (F : SpectralPoint K I)
    [Nonempty I] {s z : PartyTensor K I} {D : ℕ} (Φ : ∀ p, s.Index p → z.Index p → Polynomial K)
    (h : ∀ x, s.entry x = (polyApp z Φ x).coeff D) :
    F s ≤ ((D : ℝ) + 1) ^ Fintype.card I * F z := by
  classical
  let p₀ : I := Classical.arbitrary I
  let L : (I → Fin (D + 1)) → ∀ p, s.Index p → z.Index p → K := fun d p a c =>
    (if p = p₀ then (if (∑ q, (d q).val) = D then (1 : K) else 0) else 1) * (Φ p a c).coeff (d p)
  have hs : s.CoveredBy fun _ : I → Fin (D + 1) => z := by
    refine ⟨L, fun x => ?_⟩
    simp only [h, polyApp, Polynomial.finsetSum_coeff, coeff_mul_C, coeff_prod_choices, localApply,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' univ p₀, ite_eq_left (Finset.mem_univ _)]
    split_ifs <;> simp
  refine (F.le_sum _ _ hs).trans (le_of_eq ?_)
  simp [Finset.card_univ]



variable {A κ : Type} [Fintype A] [DecidableEq A] [Fintype κ]

/-- The number of times a word uses each letter. -/
private noncomputable def wordType {N : ℕ} (w : Fin N → κ) : κ → Fin (N + 1) :=
  open Classical in fun k =>
      ⟨#{i | w i = k}, Nat.lt_succ_of_le ((card_le_univ _).trans_eq (Fintype.card_fin N))⟩

omit [Fintype κ] in
/-- Words of one type differ by a permutation of the places. -/
private theorem exists_perm_of_wordType {N : ℕ} {w w₀ : Fin N → κ} (h : wordType w = wordType w₀) :
    ∃ σ : Equiv.Perm (Fin N), w₀ ∘ σ = w := by
  classical
  have hc : ∀ k, Fintype.card {i // w i = k} = Fintype.card {i // w₀ i = k} := fun k => by
    rw [Fintype.card_subtype, Fintype.card_subtype]
    exact congrArg Fin.val (congr_fun h k)
  exact ⟨Equiv.ofFiberEquiv fun k => Fintype.equivOfCardEq (hc k),
    funext fun i => Equiv.ofFiberEquiv_map _ i⟩

/-- For r orders ρ m of the places, the sum over m of the images of a
product, with the places in the order ρ m, is one image of the product times the unit tensor of
size r on the
parties that hold legs. So a spectral point is at most (E + 1) ^ #parties · r ^ g · ∏ at the
coefficient of ε ^ E. -/
private theorem le_type_bound (F : SpectralPoint K I) [Nonempty A] (π : A → I) (t : PartyTensor K I)
    (ht : ∀ q, q ∉ Set.range π → Subsingleton (t.Index q)) {N E r : ℕ} (hr : 1 ≤ r)
        (c : Fin N → PartyTensor K I)
    (L : ∀ j p, t.Index p → (c j).Index p → Polynomial K) (ρ : Fin r → Equiv.Perm (Fin N))
    (v : (∀ p, Fin N → t.Index p) → K)
    (hv : ∀ x, v x = (∑ m, ∏ j, polyApp (c j) (L j) fun p => x p (ρ m j)).coeff E) :
    F (((t ^ N)).withEntry v) ≤
      ((E : ℝ) + 1) ^ Fintype.card I * ((r : ℝ) ^ F.unitExponent π * ∏ j, F (c j)) := by
  classical
  have hI : Nonempty I := ⟨π (Classical.arbitrary A)⟩
  let pick : ∀ q, ({a : A // π a = q} → Fin r) → Equiv.Perm (Fin N) := fun q u =>
    if h : ∃ a, π a = q then ρ (u ⟨h.choose, h.choose_spec⟩) else 1
  let z : PartyTensor K I := push π (unit K A r) * prod c
  let Φ : ∀ q, (Fin N → t.Index q) → z.Index q → Polynomial K := fun q a y =>
    ∏ j, L j q (a (pick q y.1 j)) (y.2 j)
  have key : ∀ x, ∑ m, ∏ j, polyApp (c j) (L j) (fun p => x p (ρ m j)) = polyApp z Φ x := by
    intro x
    let f : (A → Fin r) → Polynomial K := fun u =>
      C ((unit K A r).entry u) * ∏ j, polyApp (c j) (L j) fun q => x q (pick q (fun a => u a.val) j)
    have e1 : polyApp z Φ x = ∑ u, f u := by
      have e : ∀ u, f u = ∑ y : ∀ q, (prod c).Index q,
          (∏ q, ∏ j, L j q (x q (pick q (fun a => u a.val) j)) (y q j)) *
            C ((unit K A r).entry u * (prod c).entry y) := by
        intro u
        change C _ * _ = _
        rw [← polyApp_prod (α := fun _ q => t.Index q) c L fun q j =>
            x q (pick q (fun a => u a.val) j), polyApp, localApply,
          Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ => by rw [map_mul]; exact mul_left_comm _ _ _
      simp only [e]
      rw [← Fintype.sum_prod_type']
      refine Fintype.sum_equiv
        ((Equiv.arrowProdEquivProdArrow (α := I) (fun q => {a : A // π a = q} → Fin r)
          fun q => (prod c).Index q).trans
          (Equiv.prodCongr
            (Equiv.piCongrFiberwise (f := π) (γ₁ := fun _ : A => Fin r) fun _ => Equiv.refl _).symm
            (Equiv.refl _))) _ _ fun y => ?_
      have hfib : ∀ q, (fun a : {a : A // π a = q} => (y (π a.val)).1 ⟨a.val, rfl⟩) = (y q).1 := by
        intro q
        funext a
        obtain ⟨a, rfl⟩ := a
        rfl
      change (∏ q, ∏ j, L j q (x q (pick q (y q).1 j)) ((y q).2 j)) * C _ =
        (∏ q, ∏ j, L j q (x q (pick q (fun a => (y (π a.val)).1 ⟨a.val, rfl⟩) j)) ((y q).2 j)) * C _
      simp only [hfib]
      rfl
    rw [e1]
    refine Finset.sum_of_injOn (fun m _ => m)
        (fun m _ m' _ h => congr_fun h (Classical.arbitrary A))
      (fun _ _ => by simp) (fun u _ hu => ?_) fun m _ => ?_
    · change C _ * _ = 0
      rw [unit_entry_of_not, map_zero, zero_mul]
      intro h
      exact hu ⟨u (Classical.arbitrary A), by simp, funext fun a => h _ _⟩
    · change _ = C _ * _
      rw [unit_entry_of (fun _ _ => rfl), map_one, one_mul]
      refine Finset.prod_congr rfl fun j _ => congr_arg _ (funext fun q => ?_)
      by_cases hq : ∃ a, π a = q
      · simp only [pick, dite_eq_left hq]
      · have := ht q fun ⟨a, ha⟩ => hq ⟨a, ha⟩
        exact Subsingleton.elim _ _
  refine (le_coeff F (s := ((t ^ N)).withEntry v) (D := E) Φ fun x =>
    (hv x).trans (congr_arg (fun P => P.coeff E) (key x))).trans (le_of_eq ?_)
  rw [F.map_mul, F.map_prod, F.apply_push_unit π hr]

/-- A bound for all powers with a factor polynomial in N holds without the
factor. -/
private theorem le_of_pow_le_poly {x B C : ℝ} (a : ℕ) (hB : 0 ≤ B)
    (h : ∀ N : ℕ, x ^ N ≤ C * ((N : ℝ) + 1) ^ a * B ^ N) : x ≤ B := by
  by_contra! hlt
  have hx : 0 < x := hB.trans_lt hlt
  have hlim : Filter.Tendsto (fun N : ℕ => C * 2 ^ a * ((N : ℝ) ^ a * (B / x) ^ N)) Filter.atTop
      (nhds 0) := by
    simpa using (tendsto_pow_const_mul_const_pow_of_lt_one a (by positivity)
      ((div_lt_one hx).2 hlt)).const_mul (C * 2 ^ a)
  obtain ⟨N, hN, hN1⟩ :=
      ((hlim.eventually (eventually_lt_nhds one_pos)).and (Filter.eventually_ge_atTop 1)).exists
  have hC : 0 ≤ C := zero_le_one.trans (by simpa using h 0)
  have h1 : (1 : ℝ) ≤ C * ((N : ℝ) + 1) ^ a * (B / x) ^ N := by
    rw [div_pow, mul_div_assoc', le_div_iff₀ (pow_pos hx N), one_mul]
    exact h N
  have h2 : C * ((N : ℝ) + 1) ^ a * (B / x) ^ N ≤ C * 2 ^ a * ((N : ℝ) ^ a * (B / x) ^ N) := by
    have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    rw [← mul_assoc, mul_assoc C (2 ^ a) _, ← mul_pow]
    gcongr
    linarith
  linarith

/-- The N-th power of the value at t is at most the number of types times the
factor of the extraction times (|κ| ^ g · M) ^ N. -/
private theorem pow_le_few (F : SpectralPoint K I) [Nonempty A] [Nonempty κ] (π : A → I)
    (t : PartyTensor K I)
    (ht : ∀ q, q ∉ Set.range π → Subsingleton (t.Index q))
        {b : κ → PartyTensor K I} {D : ℕ} (h : t.BorderCoveredBy D b) {M : ℝ}
    (hM : ∀ k, F (b k) ≤ M) (N : ℕ) :
    F t ^ N ≤ ((N : ℝ) + 1) ^ Fintype.card κ * (((N * D : ℕ) : ℝ) + 1) ^ Fintype.card I *
      ((Fintype.card κ : ℝ) ^ F.unitExponent π * M) ^ N := by
  classical
  have hI : Nonempty I := ⟨π (Classical.arbitrary A)⟩
  have hM0 : 0 ≤ M := (F.nonneg _).trans (hM (Classical.arbitrary κ))
  obtain ⟨L₁, hL₁⟩ := h
  set B := (Fintype.card κ : ℝ) ^ F.unitExponent π * M with hB
  let G : (Fin N → κ) → (∀ p, Fin N → t.Index p) → Polynomial K := fun w x =>
    ∏ i, polyApp (b (w i)) (L₁ (w i)) fun p => x p i
  let v : (κ → Fin (N + 1)) → (∀ p, Fin N → t.Index p) → K := fun τ x =>
    (∑ w : {w : Fin N → κ // wordType w = τ}, G w x).coeff (N * D)
  have hsum : ∀ x, ((t ^ N)).entry x = ∑ τ, v τ x := by
    intro x
    refine ((coeff_sum_words hL₁ N x le_rfl).trans (ite_eq_left rfl)).symm.trans ?_
    change _ = ∑ τ, (∑ w : {w : Fin N → κ // wordType w = τ}, G w x).coeff (N * D)
    rw [← Polynomial.finsetSum_coeff]
    exact congr_arg (fun P : K[X] => P.coeff _)
      (Fintype.sum_fiberwise (wordType (N := N) (κ := κ)) fun w => G w x).symm
  rw [← F.map_pow]
  refine (F.le_sum_entry _ v hsum).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ ((((N * D : ℕ) : ℝ) + 1) ^ Fintype.card I * B ^ N) fun
      τ _ => ?_).trans
    (le_of_eq ?_)
  · rcases isEmpty_or_nonempty {w : Fin N → κ // wordType w = τ} with he | ⟨⟨w₀, hw₀⟩⟩
    · rw [F.eq_zero fun x => (by
        simp only [v, Finset.univ_eq_empty, Finset.sum_empty, coeff_zero] : v τ x = 0)]
      positivity
    let W := {w : Fin N → κ // wordType w = τ}
    let num := Fintype.equivFin W
    have hσ : ∀ m, ∃ σ : Equiv.Perm (Fin N), w₀ ∘ σ = (num.symm m).val := fun m =>
      exists_perm_of_wordType ((num.symm m).property.trans hw₀.symm)
    choose σ hσ using hσ
    have hr : 1 ≤ Fintype.card W := Fintype.card_pos_iff.2 ⟨⟨w₀, hw₀⟩⟩
    have hv : ∀ x, v τ x =
        (∑ m, ∏ j, polyApp (b (w₀ j)) (L₁ (w₀ j)) fun p => x p ((σ m).symm j)).coeff (N * D) := by
      intro x
      refine congr_arg (fun P : K[X] => P.coeff _) (Fintype.sum_equiv num _ _ fun w => ?_)
      refine Fintype.prod_equiv (σ (num w)) _ _ fun i => ?_
      have := congr_fun (hσ (num w)) i
      simp only [Function.comp_apply, Equiv.symm_apply_apply] at this ⊢
      rw [this]
    refine (le_type_bound F π t ht hr (fun j => b (w₀ j)) (fun j => L₁ (w₀ j))
        (fun m => (σ m).symm) _
      hv).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [hB, mul_pow, ← Real.rpow_mul_natCast (by positivity), mul_comm (F.unitExponent π),
      Real.rpow_natCast_mul (by positivity)]
    refine mul_le_mul (Real.rpow_le_rpow (by positivity) ?_ (F.unitExponent_nonneg π)) ?_
      (Finset.prod_nonneg fun _ _ => F.nonneg _) (by positivity)
    · exact_mod_cast (Fintype.card_subtype_le _).trans_eq (by simp)
    · exact (Finset.prod_le_prod₀ (fun _ _ => F.nonneg _) fun j _ => hM _).trans (by simp)
  · rw [nsmul_eq_mul, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
    push_cast
    ring

/-- **Paper: Lemma N.3** (sums with few terms, approximate version). If `t` is a sum of
restrictions of the `b k` up to `ε`, every `b k` has value at most `M`, and the legs of `t` outside
the range of `π` are trivial, then `F t ≤ |κ| ^ g · M`, where `g = F.unitExponent π` is the exponent
of the unit tensor on the parties that hold legs. The choice among the terms costs only this
exponent. -/
theorem SpectralPoint.apply_le_of_borderCoveredBy (F : SpectralPoint K I)
    [Nonempty I] [Nonempty κ] (π : A → I) (t : PartyTensor K I)
    (ht : ∀ q, q ∉ Set.range π → Subsingleton (t.Index q))
    {b : κ → PartyTensor K I} {D : ℕ} (h : t.BorderCoveredBy D b) {M : ℝ} (hM : ∀ k, F (b k) ≤ M) :
    F t ≤ (Fintype.card κ : ℝ) ^ F.unitExponent π * M := by
  have hM0 : 0 ≤ M := (F.nonneg _).trans (hM (Classical.arbitrary κ))
  have hB : 0 ≤ (Fintype.card κ : ℝ) ^ F.unitExponent π * M := by positivity
  rcases isEmpty_or_nonempty A with hA | hA
  · have hsub : ∀ q, Subsingleton (t.Index q) := fun q => ht q (by simp [Set.range_eq_empty])
    by_cases h0 : ∀ x, t.entry x = 0
    · rw [F.eq_zero h0]
      exact hB
    obtain ⟨x, hx⟩ := not_forall.1 h0
    have h1 : F t ≤ 1 := by
      refine (F.le_card t).trans ?_
      exact_mod_cast Fintype.card_le_one_iff_subsingleton.2 (@Pi.instSubsingleton I t.Index hsub)
    obtain ⟨L, hL⟩ := h
    obtain ⟨k, y, hy⟩ : ∃ k y, (b k).entry y ≠ 0 := by
      by_contra! hne
      exact hx (by simpa [hne, localApply] using ((hL x D le_rfl).trans (ite_eq_left rfl)).symm)
    refine h1.trans (one_le_mul_of_one_le_of_one_le ?_ ((F.one_le hy).trans (hM k)))
    exact Real.one_le_rpow (by exact_mod_cast Fintype.card_pos) (F.unitExponent_nonneg π)
  · refine le_of_pow_le_poly (C := ((D : ℝ) + 1) ^ Fintype.card I)
      (Fintype.card κ + Fintype.card I) hB fun N => ?_
    refine (pow_le_few F π t ht h hM N).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    have h2 : ((N * D : ℕ) : ℝ) + 1 ≤ ((D : ℝ) + 1) * ((N : ℝ) + 1) := by
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) N, Nat.cast_nonneg (α := ℝ) D]
    calc _ ≤ ((N : ℝ) + 1) ^ Fintype.card κ *
          (((D : ℝ) + 1) * ((N : ℝ) + 1)) ^ Fintype.card I := by gcongr
      _ = _ := by rw [mul_pow, pow_add]; ring

end Cslib.PartyTensor
