/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Algebra/Polynomial/Sturm/Sequence.lean`)

public import CslibFrontier.Init
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Sturm.Sequence
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.List.SignVariations
public import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.Perfect
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Instances.Sign
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# Sturm's theorem for real polynomials

This file proves Sturm's theorem over `ℝ[X]` on top of Mathlib's `Polynomial.sturmSeq` and
`List.signVariations` (see [BasuPollackRoy2006]).

For any nonzero real polynomial `p` with `g = EuclideanDomain.gcd p (derivative p)`, dividing out
`g` yields the coprime pair `(p / g, derivative p / g)`, whose Sturm sign-variation count
`Polynomial.sturmReducedVariations p x` agrees with `Polynomial.sturmVariations p x` at every point
where `g.eval x ≠ 0` (while `sturmVariations p x = 0` at roots of `g`). Across any point `x`,
`sturmReducedVariations p` is locally constant away from roots of `p`, constant on a right
neighborhood `(x, x + δ)`, and increases by `1` on a left neighborhood `(x - δ, x)` precisely when
`x` is a root of `p` (of any multiplicity). Consequently,
`sturmReducedVariations p x + #{r ∈ p.roots.toFinset | r ≤ x}` is locally constant on `ℝ`, hence
constant, yielding Sturm's root-counting identity on `(a, b]` both for general nonzero polynomials
(away from multiple-root endpoints) and unconditionally for separable (squarefree) polynomials.

## Main definitions

* `Polynomial.sturmVariations`: sign variations of `sturmSeq p (derivative p)` evaluated at `x`.
* `Polynomial.sturmReducedVariations`: sign variations of
  `sturmSeq (p / gcd p p') (p' / gcd p p')` evaluated at `x`.

## Main results

* `Polynomial.sturmSeq_map`: `Polynomial.sturmSeq` commutes with `Polynomial.map` along any ring
  homomorphism between fields.
* `Polynomial.sturmVariations_eq_sturmReducedVariations`,
  `Polynomial.sturmVariations_eq_zero_of_gcd_eval_eq_zero`: relation between `sturmVariations` and
  `sturmReducedVariations` on general nonzero polynomials.
* `Polynomial.sturmReducedVariations_sub_eq_card_roots_Ioc`,
  `Polynomial.sturmReducedVariations_antitone`,
  `Polynomial.sturmVariations_sub_eq_card_roots_Ioc_of_gcd_eval_ne_zero`: general Sturm's theorem
  counting distinct real roots in `(a, b]` without multiplicity.
* `Polynomial.sturmVariations_sub_eq_card_roots_Ioc`,
  `Polynomial.sturmVariations_sub_eq_card_roots_Ioc_of_squarefree`,
  `Polynomial.sturmVariations_sub_eq_card_roots_Ioo`,
  `Polynomial.sturmVariations_sub_eq_card_roots_Icc`,
  `Polynomial.sturmVariations_antitone`: unconditional specializations for separable (squarefree)
  polynomials.

## References

* [S. Basu, R. Pollack, and M.-F. Roy, *Algorithms in Real Algebraic Geometry*][BasuPollackRoy2006],
  Theorem 2.50, p. 52 (counts distinct roots in an open interval over a real closed field; the
  reduced-variation theorem here uses finite real endpoints and counts roots in `(a, b]` over `ℝ`
  via local constancy of `sturmReducedVariations p x + #{r ≤ x}` on top of Mathlib's
  `Polynomial.sturmSeq`).
-/

public section

open Filter Set SignType
open scoped Topology

namespace Polynomial

private theorem sturmSeq_map_aux {K L : Type*} [Field K] [DecidableEq K] [Field L]
    [DecidableEq L] (f : K →+* L) :
    ∀ (m : ℕ) (p q : K[X]), (if q = 0 then 0 else q.natDegree + 1) ≤ m →
      Polynomial.sturmSeq (p.map f) (q.map f) =
        (Polynomial.sturmSeq p q).map (Polynomial.map f)
  | m, p, q, hm => by
    by_cases hp : p = 0
    · subst hp
      simp only [Polynomial.map_zero, Polynomial.sturmSeq_zero_left, List.map_nil]
    · have hpf : p.map f ≠ 0 := (Polynomial.map_ne_zero_iff f.injective).mpr hp
      by_cases hq : q = 0
      · subst hq
        simp only [Polynomial.map_zero, Polynomial.sturmSeq_zero_right,
          ite_eq_right (fun h => absurd h hp), ite_eq_right (fun h => absurd h hpf),
          List.map_cons, List.map_nil]
      · have hqf : q.map f ≠ 0 := (Polynomial.map_ne_zero_iff f.injective).mpr hq
        obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := by
          have hpos : 0 < m := by
            rw [ite_eq_right (fun h => absurd h hq)] at hm
            omega
          exact Nat.exists_eq_succ_of_ne_zero hpos.ne'
        subst hk
        let r := -p % q
        have hr_meas : (if r = 0 then 0 else r.natDegree + 1) ≤ k := by
          rw [ite_eq_right (fun h => absurd h hq)] at hm
          by_cases hr0 : r = 0
          · simp only [hr0, ↓reduceIte, Nat.zero_le]
          · rw [ite_eq_right (fun h => absurd h hr0)]
            have hlt : r.degree < q.degree := Polynomial.degree_mod_lt (-p) hq
            have hnat : r.natDegree < q.natDegree :=
              (Polynomial.natDegree_lt_iff_degree_lt hr0).mpr
                (by rwa [← Polynomial.degree_eq_natDegree hq])
            omega
        have ih := sturmSeq_map_aux f k q r hr_meas
        rw [Polynomial.sturmSeq_cons hp, Polynomial.sturmSeq_cons hpf, List.map_cons, ← ih,
          ← Polynomial.map_neg, ← Polynomial.map_mod]

/-- `Polynomial.sturmSeq` commutes with `Polynomial.map` along any ring homomorphism between
fields. -/
theorem sturmSeq_map {K L : Type*} [Field K] [DecidableEq K] [Field L] [DecidableEq L]
    (f : K →+* L) (p q : K[X]) :
    Polynomial.sturmSeq (p.map f) (q.map f) = (Polynomial.sturmSeq p q).map (Polynomial.map f) :=
  sturmSeq_map_aux f (if q = 0 then 0 else q.natDegree + 1) p q le_rfl

/-- The number of sign variations of the canonical Sturm sequence `sturmSeq p (derivative p)`
evaluated at `x : ℝ`. -/
@[expose] noncomputable def sturmVariations (p : ℝ[X]) (x : ℝ) : ℕ :=
  open Classical in
  ((sturmSeq p (derivative p)).map (eval x)).signVariations

/-- Sign variations of the reduced coprime Sturm sequence
`sturmSeq (p / gcd p (derivative p)) (derivative p / gcd p (derivative p))` at `x : ℝ`. -/
@[expose] noncomputable def sturmReducedVariations (p : ℝ[X]) (x : ℝ) : ℕ :=
  open Classical in
  let g := EuclideanDomain.gcd p (derivative p)
  ((sturmSeq (p / g) (derivative p / g)).map (eval x)).signVariations

private theorem signVariations_map_mul_of_ne_zero {c : ℝ} (hc : c ≠ 0) (xs : List ℝ) :
    (xs.map (c * ·)).signVariations = xs.signVariations := by
  rcases lt_or_gt_of_ne hc with hneg | hpos
  · refine List.signVariations_map_of_sign_eq_neg (fun x => ?_) xs
    change sign (c * x) = -sign x
    rw [sign_mul, sign_neg hneg, neg_one_mul]
  · refine List.signVariations_map (fun x => ?_) xs
    change sign (c * x) = sign x
    rw [sign_mul, sign_pos hpos, one_mul]

private theorem signVariations_eq_zero_of_forall_zero :
    ∀ {xs : List ℝ}, (∀ x ∈ xs, x = 0) → xs.signVariations = 0
  | [], _ => rfl
  | x :: xs, h => by
    rw [h x List.mem_cons_self, List.signVariations_zero_cons]
    exact signVariations_eq_zero_of_forall_zero fun y hy => h y (List.mem_cons_of_mem _ hy)

private theorem gcd_deriv_ne_zero {p : ℝ[X]} (hp : p ≠ 0) :
    open Classical in EuclideanDomain.gcd p (derivative p) ≠ 0 := by
  classical
  exact fun h0 => hp (EuclideanDomain.gcd_eq_zero_iff.mp h0).1

private theorem mul_div_gcd_deriv {p : ℝ[X]} (hp : p ≠ 0) :
    open Classical in
    let g := EuclideanDomain.gcd p (derivative p)
    g * (p / g) = p ∧ g * (derivative p / g) = derivative p ∧
      IsCoprime (p / g) (derivative p / g) := by
  classical
  dsimp only
  set g := EuclideanDomain.gcd p (derivative p)
  have hg0 : g ≠ 0 := gcd_deriv_ne_zero hp
  have hp_eq : g * (p / g) = p :=
    EuclideanDomain.mul_div_cancel' hg0 (EuclideanDomain.gcd_dvd_left p (derivative p))
  have hdp_eq : g * (derivative p / g) = derivative p :=
    EuclideanDomain.mul_div_cancel' hg0 (EuclideanDomain.gcd_dvd_right p (derivative p))
  refine ⟨hp_eq, hdp_eq, EuclideanDomain.gcdA p (derivative p),
    EuclideanDomain.gcdB p (derivative p), ?_⟩
  have hbez := EuclideanDomain.gcd_eq_gcd_ab p (derivative p)
  apply mul_left_cancel₀ hg0
  linear_combination -hbez + EuclideanDomain.gcdA p (derivative p) * hp_eq +
    EuclideanDomain.gcdB p (derivative p) * hdp_eq

private theorem sturmSeq_eq_map_gcd_deriv {p : ℝ[X]} (hp : p ≠ 0) :
    open Classical in
    let g := EuclideanDomain.gcd p (derivative p)
    sturmSeq p (derivative p) = (sturmSeq (p / g) (derivative p / g)).map (g * ·) := by
  classical
  dsimp only
  obtain ⟨hp_eq, hdp_eq, _⟩ := mul_div_gcd_deriv hp
  rw [← sturmSeq_mul_left (gcd_deriv_ne_zero hp), hp_eq, hdp_eq]

/-- At any point `x` where `gcd p (derivative p)` vanishes, `sturmVariations p x = 0`. -/
theorem sturmVariations_eq_zero_of_gcd_eval_eq_zero {p : ℝ[X]} {x : ℝ}
    (hgx : (open Classical in EuclideanDomain.gcd p (derivative p)).eval x = 0) :
    sturmVariations p x = 0 := by
  classical
  by_cases hp : p = 0
  · simp only [sturmVariations, hp, derivative_zero, sturmSeq_zero_left, List.map_nil,
      List.signVariations_nil]
  · rw [sturmVariations, sturmSeq_eq_map_gcd_deriv hp, List.map_map]
    refine signVariations_eq_zero_of_forall_zero fun v hv => ?_
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hv
    simp only [Function.comp_apply, eval_mul, hgx, zero_mul]

/-- Wherever `gcd p (derivative p)` does not vanish at `x`, `sturmVariations p x` equals
`sturmReducedVariations p x`. -/
theorem sturmVariations_eq_sturmReducedVariations {p : ℝ[X]} (hp : p ≠ 0) {x : ℝ}
    (hgx : (open Classical in EuclideanDomain.gcd p (derivative p)).eval x ≠ 0) :
    sturmVariations p x = sturmReducedVariations p x := by
  classical
  set g := EuclideanDomain.gcd p (derivative p)
  rw [sturmVariations, sturmReducedVariations, sturmSeq_eq_map_gcd_deriv hp]
  have hmap : ((sturmSeq (p / g) (derivative p / g)).map (g * ·)).map (eval x) =
      ((sturmSeq (p / g) (derivative p / g)).map (eval x)).map (g.eval x * ·) := by
    rw [List.map_map, List.map_map]
    exact List.map_congr_left fun q _ => eval_mul
  rw [hmap, signVariations_map_mul_of_ne_zero hgx]

/-- For separable `p`, `sturmVariations p x = sturmReducedVariations p x` everywhere. -/
theorem sturmVariations_eq_sturmReducedVariations_of_separable {p : ℝ[X]} (hp : p.Separable)
    (x : ℝ) : sturmVariations p x = sturmReducedVariations p x := by
  classical
  refine sturmVariations_eq_sturmReducedVariations hp.ne_zero fun hgx => ?_
  have hp0 : p.eval x = 0 := by
    obtain ⟨q, hq⟩ := EuclideanDomain.gcd_dvd_left p (derivative p)
    rw [hq, eval_mul, hgx, zero_mul]
  have hdp0 : (derivative p).eval x = 0 := by
    obtain ⟨q, hq⟩ := EuclideanDomain.gcd_dvd_right p (derivative p)
    rw [hq, eval_mul, hgx, zero_mul]
  obtain ⟨a, b, hab⟩ := hp
  have hev := congrArg (eval x) hab
  simp only [eval_add, eval_mul, hp0, hdp0, mul_zero, add_zero, eval_one, zero_ne_one] at hev

/-- Any `IsCoprime p q` is preserved under the signed remainder step `(p, q) ↦ (q, -p % q)`. -/
private theorem isCoprime_neg_mod {K : Type*} [Field K] {p q : K[X]} (h : IsCoprime p q) :
    IsCoprime q (-p % q) := by
  rcases h with ⟨a, b, hab⟩
  refine ⟨b - a * (-p / q), -a, ?_⟩
  have hdiv := EuclideanDomain.div_add_mod (-p) q
  linear_combination hab - a * hdiv

/-- Predicate capturing the local Sturm-chain invariants at `x : ℝ` for a list of polynomials:
no element is identically zero, the list is nonempty and its last entry is nonzero at `x`,
no two adjacent entries vanish simultaneously at `x`, and at any interior zero the neighboring
entries have opposite nonzero signs. -/
private inductive IsSturmChainAt (x : ℝ) : List ℝ[X] → Prop
  | singleton {f : ℝ[X]} (hf0 : f ≠ 0) (hfx : f.eval x ≠ 0) : IsSturmChainAt x [f]
  | cons {f g : ℝ[X]} {t : List ℝ[X]} (hf0 : f ≠ 0)
      (hpair : ¬(f.eval x = 0 ∧ g.eval x = 0))
      (htriple : ∀ h t', t = h :: t' → g.eval x = 0 → sign (f.eval x) = -sign (h.eval x))
      (htail : IsSturmChainAt x (g :: t)) :
      IsSturmChainAt x (f :: g :: t)

private theorem isSturmChainAt_ne_nil {x : ℝ} {L : List ℝ[X]} (h : IsSturmChainAt x L) :
    L ≠ [] := by
  cases h <;> exact List.cons_ne_nil _ _

private theorem isSturmChainAt_sturmSeq {p q : ℝ[X]} (hp : p ≠ 0) (hcop : IsCoprime p q)
    (x : ℝ) :
    open Classical in IsSturmChainAt x (sturmSeq p q) := by
  classical
  induction p, q using sturmSeq.induct with
  | case1 q => exact absurd rfl hp
  | case2 p q hp0 ih =>
    rw [sturmSeq_cons hp0]
    by_cases hq0 : q = 0
    · subst hq0
      rw [sturmSeq_zero_left]
      have hunit : IsUnit p := isCoprime_zero_right.mp hcop
      obtain ⟨c, hc, hpc⟩ := isUnit_iff.mp hunit
      have hne : p.eval x ≠ 0 := by
        rw [← hpc, eval_C]
        exact hc.ne_zero
      exact IsSturmChainAt.singleton hp0 hne
    · have hcop' : IsCoprime q (-p % q) := isCoprime_neg_mod hcop
      have htail := ih hq0 hcop'
      obtain ⟨t, ht⟩ : ∃ t, sturmSeq q (-p % q) = q :: t := by
        rw [sturmSeq_cons hq0]
        exact ⟨_, rfl⟩
      rw [ht] at htail ⊢
      refine IsSturmChainAt.cons hp0 ?_ ?_ htail
      · rintro ⟨hpx, hqx⟩
        obtain ⟨a, b, hab⟩ := hcop
        have hev := congrArg (eval x) hab
        simp only [eval_add, eval_mul, hpx, hqx, mul_zero, add_zero, eval_one, zero_ne_one] at hev
      · intro h t' ht' hqx
        have hrem : h = -p % q := by
          have := sturmSeq_cons (p := q) (q := -p % q) hq0
          rw [ht] at this
          rcases List.cons.inj this with ⟨_, hsub⟩
          have hr_ne : -p % q ≠ 0 := by
            intro hzero
            rw [hzero, sturmSeq_zero_left] at hsub
            rw [hsub] at ht'
            exact List.cons_ne_nil _ _ ht'.symm
          rw [sturmSeq_cons hr_ne, ht'] at hsub
          exact (List.cons.inj hsub).1
        subst hrem
        rw [eval_mod_eq_self_of_root hqx, eval_neg, Left.sign_neg, neg_neg]

/-- If `L` is a Sturm chain at `x` whose head does not vanish at `x`, and `y` preserves the sign
of every entry of `L` that does not vanish at `x`, then `L` has the same number of sign variations
at `y` and at `x`. -/
private theorem signVariations_eval_eq_of_isSturmChainAt {x y : ℝ} :
    ∀ {L : List ℝ[X]}, IsSturmChainAt x L →
      (∀ f, L.head? = some f → f.eval x ≠ 0) →
      (∀ f ∈ L, f.eval x ≠ 0 → sign (f.eval y) = sign (f.eval x)) →
      (L.map (eval y)).signVariations = (L.map (eval x)).signVariations
  | [], h, _, _ => absurd rfl (isSturmChainAt_ne_nil h)
  | [_], _, _, _ => by simp only [List.map_cons, List.map_nil, List.signVariations_singleton]
  | f :: g :: t, hchain, hhead, hsign => by
    cases hchain with
    | cons hf0 hpair htriple htail =>
      have hsign_of {q : ℝ[X]} (hq : q ∈ f :: g :: t) (hqx : q.eval x ≠ 0) :
          sign (q.eval y) = sign (q.eval x) ∧ q.eval y ≠ 0 :=
        ⟨hsign q hq hqx, sign_ne_zero.mp (hsign q hq hqx ▸ sign_ne_zero.mpr hqx)⟩
      have hfx : f.eval x ≠ 0 := hhead f rfl
      obtain ⟨hfy_sign, hfy⟩ := hsign_of List.mem_cons_self hfx
      by_cases hgx : g.eval x = 0
      · have hne_t : t ≠ [] := by
          intro ht0; subst ht0
          cases htail with | singleton _ hgx' => exact hgx' hgx
        obtain ⟨h, t', rfl⟩ := List.exists_cons_of_ne_nil hne_t
        have hsign_fh : sign (f.eval x) = -sign (h.eval x) := htriple h t' rfl hgx
        have hhx : h.eval x ≠ 0 := by
          cases htail with | cons _ hpair' _ _ => exact fun hh => hpair' ⟨hgx, hh⟩
        obtain ⟨hhy_sign, hhy⟩ := hsign_of (by simp only [List.mem_cons, true_or, or_true]) hhx
        have hhtail : IsSturmChainAt x (h :: t') := by
          cases htail with | cons _ _ _ htail' => exact htail'
        have ih := signVariations_eval_eq_of_isSturmChainAt hhtail
          (fun _ h0 => by cases h0; exact hhx)
          (fun q hq => hsign q (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq)))
        simp only [List.map_cons] at ih ⊢
        rw [hgx, List.signVariations_cons_zero_cons]
        have hfx_ne_hhx : sign (f.eval x) ≠ sign (h.eval x) := by
          have hhs : sign (h.eval x) ≠ 0 := sign_ne_zero.mpr hhx
          rw [hsign_fh]; revert hhs; cases sign (h.eval x) <;> decide
        rw [List.signVariations_cons_cons_of_ne_zero _ hfx hhx, ite_eq_right hfx_ne_hhx]
        by_cases hgy : g.eval y = 0
        · rw [hgy, List.signVariations_cons_zero_cons]
          have hfy_ne_hhy : sign (f.eval y) ≠ sign (h.eval y) := by
            rw [hfy_sign, hhy_sign]; exact hfx_ne_hhx
          rw [List.signVariations_cons_cons_of_ne_zero _ hfy hhy, ite_eq_right hfy_ne_hhy, ih]
        · rw [List.signVariations_cons_cons_of_ne_zero _ hfy hgy,
            List.signVariations_cons_cons_of_ne_zero _ hgy hhy, ih]
          have hopp : sign (f.eval y) = -sign (h.eval y) := by rw [hfy_sign, hhy_sign, hsign_fh]
          have hsf : sign (f.eval y) ≠ 0 := sign_ne_zero.mpr hfy
          have hsg : sign (g.eval y) ≠ 0 := sign_ne_zero.mpr hgy
          rcases (sign (f.eval y)).trichotomy with hs1 | hs1 | hs1 <;>
            rcases (sign (g.eval y)).trichotomy with hs2 | hs2 | hs2 <;>
            rcases (sign (h.eval y)).trichotomy with hs3 | hs3 | hs3 <;>
            simp only [hs1, hs2, hs3] at hopp hsf hsg ⊢ <;>
            first | exact absurd hopp (by decide) | exact absurd rfl hsf |
              exact absurd rfl hsg | simp only [↓reduceIte, reduceCtorEq, add_zero]
      · obtain ⟨hgy_sign, hgy⟩ := hsign_of (by simp only [List.mem_cons, true_or, or_true]) hgx
        have ih := signVariations_eval_eq_of_isSturmChainAt htail
          (fun _ h0 => by cases h0; exact hgx)
          (fun q hq => hsign q (List.mem_cons_of_mem f hq))
        simp only [List.map_cons] at ih ⊢
        rw [List.signVariations_cons_cons_of_ne_zero _ hfy hgy,
          List.signVariations_cons_cons_of_ne_zero _ hfx hgx, hfy_sign, hgy_sign, ih]

/-- Near any point `x`, every polynomial in `L` that does not vanish at `x` preserves its sign. -/
private theorem eventually_sign_eq_of_mem {x : ℝ} (L : List ℝ[X]) :
    ∀ᶠ y in 𝓝 x, ∀ f ∈ L, f.eval x ≠ 0 → sign (f.eval y) = sign (f.eval x) := by
  have hall : ∀ᶠ y in 𝓝 x, ∀ f ∈ L.toFinset, f.eval x ≠ 0 → sign (f.eval y) = sign (f.eval x) := by
    refine (Filter.eventually_all_finset L.toFinset).mpr fun f _ => ?_
    by_cases hfx : f.eval x = 0
    · exact Eventually.of_forall fun _ h => absurd hfx h
    · have hcont := (continuousAt_sign_of_ne_zero hfx).tendsto.comp (f.continuous.tendsto x)
      rw [nhds_discrete SignType, tendsto_pure] at hcont
      exact hcont.mono fun y hy _ => hy
  exact hall.mono fun y hy f hf hfx => hy f (List.mem_toFinset.mpr hf) hfx

private theorem div_gcd_deriv_ne_zero {p : ℝ[X]} (hp : p ≠ 0) :
    open Classical in p / EuclideanDomain.gcd p (derivative p) ≠ 0 := by
  classical
  obtain ⟨hp_eq, _, _⟩ := mul_div_gcd_deriv hp
  intro h0
  rw [h0, mul_zero] at hp_eq
  exact hp hp_eq.symm

private theorem derivative_eq_pow_mul {p h : ℝ[X]} {x : ℝ} {m : ℕ} (hm : 0 < m)
    (hp : p = (X - C x) ^ m * h) :
    derivative p = (X - C x) ^ (m - 1) * (C (m : ℝ) * h + (X - C x) * derivative h) := by
  conv_lhs => rw [hp]
  rw [derivative_mul, derivative_X_sub_C_pow]
  have hm_eq : (X - C x) ^ m = (X - C x) ^ (m - 1) * (X - C x) := by
    rw [← pow_succ, Nat.sub_add_cancel hm]
  conv_lhs => rw [hm_eq]
  ring

private theorem isRoot_div_gcd_deriv_iff {p : ℝ[X]} (hp : p ≠ 0) (x : ℝ) :
    open Classical in (p / EuclideanDomain.gcd p (derivative p)).IsRoot x ↔ p.IsRoot x := by
  classical
  set g := EuclideanDomain.gcd p (derivative p)
  obtain ⟨hp_eq, _, _⟩ := mul_div_gcd_deriv hp
  constructor
  · intro hA
    rw [IsRoot.def] at hA ⊢
    rw [← hp_eq, eval_mul, hA, mul_zero]
  · intro hpx
    by_contra hAx
    rw [IsRoot.def] at hpx hAx
    have hm_pos : 0 < p.rootMultiplicity x := (rootMultiplicity_pos hp).mpr hpx
    obtain ⟨h, hp_fac, hh_ndvd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp x
    have hhx : h.eval x ≠ 0 := mt dvd_iff_isRoot.mpr hh_ndvd
    set m := p.rootMultiplicity x
    have hcop_lin : IsCoprime (X - C x) (p / g) := by
      refine ⟨-C ((p / g).eval x)⁻¹ * ((p / g) /ₘ (X - C x)), C ((p / g).eval x)⁻¹, ?_⟩
      have hdiv := modByMonic_add_div (p / g) (X - C x)
      rw [modByMonic_X_sub_C_eq_C_eval] at hdiv
      have hinv : C ((p / g).eval x)⁻¹ * C ((p / g).eval x) = 1 := by
        rw [← map_mul, inv_mul_cancel₀ hAx, map_one]
      linear_combination -C ((p / g).eval x)⁻¹ * hdiv + hinv
    have hpow_dvd_g : (X - C x) ^ m ∣ g := (hcop_lin.pow_left).dvd_of_dvd_mul_left
      (by rw [mul_comm, hp_eq, hp_fac]; exact dvd_mul_right _ _)
    obtain ⟨w, hw⟩ := dvd_trans hpow_dvd_g (EuclideanDomain.gcd_dvd_right p (derivative p))
    have hderiv_fac := derivative_eq_pow_mul hm_pos hp_fac
    have hpow_split : (X - C x) ^ m * w = (X - C x) ^ (m - 1) * ((X - C x) * w) := by
      rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel hm_pos]
    rw [hw, hpow_split] at hderiv_fac
    have hcancel := mul_left_cancel₀ (pow_ne_zero (m - 1) (X_sub_C_ne_zero x)) hderiv_fac
    have hev := congrArg (eval x) hcancel
    simp only [eval_add, eval_mul, eval_C, eval_sub, eval_X, sub_self, zero_mul, add_zero] at hev
    exact mul_ne_zero (Nat.cast_ne_zero.mpr hm_pos.ne') hhx hev.symm

private theorem eventually_sign_div_gcd_of_eval_eq_zero {p : ℝ[X]} (hp : p ≠ 0) {x : ℝ}
    (hpx : p.eval x = 0) :
    open Classical in
    let g := EuclideanDomain.gcd p (derivative p)
    let A := p / g
    let B := derivative p / g
    (∀ᶠ y in 𝓝[>] x, sign (A.eval y) = sign (B.eval x)) ∧
    (∀ᶠ y in 𝓝[<] x, sign (A.eval y) = -sign (B.eval x)) := by
  classical
  dsimp only
  set g := EuclideanDomain.gcd p (derivative p)
  set A := p / g
  set B := derivative p / g
  obtain ⟨hp_eq, hdp_eq, hcop⟩ := mul_div_gcd_deriv hp
  have hAx : A.eval x = 0 := (isRoot_div_gcd_deriv_iff hp x).mpr hpx
  have hBx : B.eval x ≠ 0 := by
    intro hB0
    obtain ⟨u, v, huv⟩ : IsCoprime A B := hcop
    have hev := congrArg (eval x) huv
    simp only [eval_add, eval_mul, hAx, hB0, mul_zero, add_zero, eval_one, zero_ne_one] at hev
  have hm_pos : 0 < p.rootMultiplicity x := (rootMultiplicity_pos hp).mpr hpx
  obtain ⟨h, hp_fac, hh_ndvd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp x
  have hhx : h.eval x ≠ 0 := mt dvd_iff_isRoot.mpr hh_ndvd
  set m := p.rootMultiplicity x
  set Q := C (m : ℝ) * h + (X - C x) * derivative h
  have hderiv_fac : derivative p = (X - C x) ^ (m - 1) * Q := derivative_eq_pow_mul hm_pos hp_fac
  have hprod_x : 0 < (h * Q).eval x := by
    simp only [Q, eval_mul, eval_add, eval_C, eval_sub, eval_X, sub_self, zero_mul, add_zero]
    have hm_real : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm_pos
    have hsq_pos : 0 < h.eval x * h.eval x := mul_self_pos.mpr hhx
    nlinarith
  have hprod_nhds : ∀ᶠ y in 𝓝 x, 0 < (h * Q).eval y :=
    ((h * Q).continuous.tendsto x).eventually (lt_mem_nhds hprod_x)
  have hB_sign_nhds : ∀ᶠ y in 𝓝 x, sign (B.eval y) = sign (B.eval x) :=
    (eventually_sign_eq_of_mem [B]).mono fun y hy => hy B List.mem_cons_self hBx
  have hg_no_root : ∀ᶠ y in 𝓝 x, y ≠ x → g.eval y ≠ 0 := by
    have hg0 : g ≠ 0 := gcd_deriv_ne_zero hp
    have hall : ∀ᶠ y in 𝓝 x, ∀ r ∈ g.roots.toFinset, r ≠ x → y ≠ r := by
      refine (Filter.eventually_all_finset g.roots.toFinset).mpr fun r _ => ?_
      by_cases hrx : r = x
      · exact Eventually.of_forall fun _ h => absurd hrx h
      · exact (eventually_ne_nhds (Ne.symm hrx)).mono fun _ hy _ => hy
    refine hall.mono fun y hy hyx hgy =>
      hy y (Multiset.mem_toFinset.mpr ((mem_roots hg0).mpr hgy)) hyx rfl
  have hpdp_id : ∀ y : ℝ,
      (g.eval y) ^ 2 * (A.eval y * B.eval y) =
        (y - x) * ((y - x) ^ (m - 1)) ^ 2 * (h * Q).eval y := fun y => by
    have h1 : p.eval y * (derivative p).eval y = (g.eval y) ^ 2 * (A.eval y * B.eval y) := by
      have hp_ev : p.eval y = g.eval y * A.eval y := by rw [← hp_eq, eval_mul]
      have hdp_ev : (derivative p).eval y = g.eval y * B.eval y := by rw [← hdp_eq, eval_mul]
      rw [hp_ev, hdp_ev]; ring
    have h2 : p.eval y * (derivative p).eval y =
        (y - x) * ((y - x) ^ (m - 1)) ^ 2 * (h * Q).eval y := by
      rw [congrArg (eval y) hp_fac, congrArg (eval y) hderiv_fac]
      have hm_pow : (y - x) ^ m = (y - x) * (y - x) ^ (m - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel hm_pos]
      simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, hm_pow]
      ring
    exact h1.symm.trans h2
  have hbase : ∀ᶠ y in 𝓝 x,
      y ≠ x → (x < y → sign (A.eval y) = sign (B.eval x)) ∧
        (y < x → sign (A.eval y) = -sign (B.eval x)) := by
    filter_upwards [hprod_nhds, hB_sign_nhds, hg_no_root] with y hpy hBy hgy hyx
    have hg_sq : 0 < (g.eval y) ^ 2 := sq_pos_of_ne_zero (hgy hyx)
    have hy_sq : 0 < ((y - x) ^ (m - 1)) ^ 2 :=
      sq_pos_of_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hyx))
    have hid := hpdp_id y
    constructor
    · intro hxy
      have hrhs : 0 < (y - x) * ((y - x) ^ (m - 1)) ^ 2 * (h * Q).eval y :=
        mul_pos (mul_pos (sub_pos.mpr hxy) hy_sq) hpy
      have hab : 0 < A.eval y * B.eval y := by nlinarith
      have hmul_sign : sign (A.eval y) * sign (B.eval y) = 1 := by rw [← sign_mul, sign_pos hab]
      rw [← hBy]; revert hmul_sign; cases sign (A.eval y) <;> cases sign (B.eval y) <;> decide
    · intro hyx_lt
      have hrhs : (y - x) * ((y - x) ^ (m - 1)) ^ 2 * (h * Q).eval y < 0 :=
        mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (sub_neg.mpr hyx_lt) hy_sq) hpy
      have hab : A.eval y * B.eval y < 0 := by nlinarith
      have hmul_sign : sign (A.eval y) * sign (B.eval y) = -1 := by rw [← sign_mul, sign_neg hab]
      rw [← hBy]; revert hmul_sign; cases sign (A.eval y) <;> cases sign (B.eval y) <;> decide
  exact ⟨((hbase.filter_mono nhdsWithin_le_nhds).and eventually_mem_nhdsWithin).mono
      fun y ⟨hf, hxy⟩ => (hf hxy.ne').1 hxy,
    ((hbase.filter_mono nhdsWithin_le_nhds).and eventually_mem_nhdsWithin).mono
      fun y ⟨hf, hyx⟩ => (hf hyx.ne).2 hyx⟩

private theorem eventually_sturmReducedVariations_of_eval_ne_zero {p : ℝ[X]} (hp : p ≠ 0)
    {x : ℝ} (hpx : p.eval x ≠ 0) :
    ∀ᶠ y in 𝓝 x, sturmReducedVariations p y = sturmReducedVariations p x := by
  classical
  set g := EuclideanDomain.gcd p (derivative p)
  set A := p / g
  set B := derivative p / g
  have hA0 : A ≠ 0 := div_gcd_deriv_ne_zero hp
  have hAx : A.eval x ≠ 0 := fun h0 => hpx ((isRoot_div_gcd_deriv_iff hp x).mp h0)
  obtain ⟨_, _, hcop⟩ := mul_div_gcd_deriv hp
  have hchain := isSturmChainAt_sturmSeq hA0 hcop x
  refine (eventually_sign_eq_of_mem (sturmSeq A B)).mono fun y hy => ?_
  simp only [sturmReducedVariations]
  exact signVariations_eval_eq_of_isSturmChainAt hchain (fun f hf => by
    rw [head?_sturmSeq hA0] at hf
    cases hf
    exact hAx) hy

private theorem eventually_sturmReducedVariations_of_eval_eq_zero {p : ℝ[X]} (hp : p ≠ 0)
    {x : ℝ} (hpx : p.eval x = 0) :
    (∀ᶠ y in 𝓝[>] x, sturmReducedVariations p y = sturmReducedVariations p x) ∧
    (∀ᶠ y in 𝓝[<] x, sturmReducedVariations p y = sturmReducedVariations p x + 1) := by
  classical
  set g := EuclideanDomain.gcd p (derivative p)
  set A := p / g
  set B := derivative p / g
  have hA0 : A ≠ 0 := div_gcd_deriv_ne_zero hp
  have hAx : A.eval x = 0 := (isRoot_div_gcd_deriv_iff hp x).mpr hpx
  obtain ⟨_, _, hcop⟩ := mul_div_gcd_deriv hp
  have hdne : B.eval x ≠ 0 := by
    intro hd0
    obtain ⟨a, b, hab⟩ : IsCoprime A B := hcop
    have hev := congrArg (eval x) hab
    simp only [eval_add, eval_mul, hAx, hd0, mul_zero, add_zero, eval_one, zero_ne_one] at hev
  have hB0 : B ≠ 0 := fun h => hdne (by rw [h, eval_zero])
  have hcop' : IsCoprime B (-A % B) := isCoprime_neg_mod hcop
  have htail_chain := isSturmChainAt_sturmSeq hB0 hcop' x
  set tail := sturmSeq B (-A % B) with htail_def
  have hseq_eq : sturmSeq A B = A :: tail := sturmSeq_cons hA0
  have htail_eq : ∀ᶠ y in 𝓝 x,
      (tail.map (eval y)).signVariations = sturmReducedVariations p x := by
    refine (eventually_sign_eq_of_mem tail).mono fun y hy => ?_
    have hvar : (tail.map (eval y)).signVariations = (tail.map (eval x)).signVariations :=
      signVariations_eval_eq_of_isSturmChainAt htail_chain (fun f hf => by
        rw [htail_def, head?_sturmSeq hB0] at hf
        cases hf
        exact hdne) hy
    rw [hvar, sturmReducedVariations, show p / EuclideanDomain.gcd p (derivative p) = A from rfl,
      show derivative p / EuclideanDomain.gcd p (derivative p) = B from rfl,
      hseq_eq, List.map_cons, hAx, List.signVariations_zero_cons]
  obtain ⟨rest, hrest⟩ : ∃ rest, tail = B :: rest := by
    rw [htail_def, sturmSeq_cons hB0]; exact ⟨_, rfl⟩
  have hB_sign : ∀ᶠ y in 𝓝 x, sign (B.eval y) = sign (B.eval x) :=
    (eventually_sign_eq_of_mem [B]).mono fun y hy => hy B List.mem_cons_self hdne
  obtain ⟨hright, hleft⟩ := eventually_sign_div_gcd_of_eval_eq_zero hp hpx
  have hstep {y : ℝ} (htail_y : (tail.map (eval y)).signVariations = sturmReducedVariations p x)
      (hB_y : sign (B.eval y) = sign (B.eval x)) (hA_ne : sign (A.eval y) ≠ 0) :
      sturmReducedVariations p y =
        (if sign (A.eval y) = sign (B.eval y) then 0 else 1) + sturmReducedVariations p x := by
    have hAy_ne : A.eval y ≠ 0 := sign_ne_zero.mp hA_ne
    have hBy_ne : B.eval y ≠ 0 := sign_ne_zero.mp (hB_y ▸ sign_ne_zero.mpr hdne)
    have htail_y' : (B.eval y :: rest.map (eval y)).signVariations =
        sturmReducedVariations p x := by simpa only [hrest, List.map_cons] using htail_y
    rw [sturmReducedVariations, show p / EuclideanDomain.gcd p (derivative p) = A from rfl,
      show derivative p / EuclideanDomain.gcd p (derivative p) = B from rfl,
      hseq_eq, hrest, List.map_cons, List.map_cons,
      List.signVariations_cons_cons_of_ne_zero _ hAy_ne hBy_ne, htail_y', add_comm]
  constructor
  · refine ((htail_eq.filter_mono nhdsWithin_le_nhds).and
      ((hB_sign.filter_mono nhdsWithin_le_nhds).and hright)).mono ?_
    rintro y ⟨htail_y, hB_y, hA_y⟩
    change sign (A.eval y) = sign (B.eval x) at hA_y
    rw [hstep htail_y hB_y (hA_y ▸ sign_ne_zero.mpr hdne), hA_y, hB_y, ite_eq_left rfl,
      Nat.zero_add]
  · refine ((htail_eq.filter_mono nhdsWithin_le_nhds).and
      ((hB_sign.filter_mono nhdsWithin_le_nhds).and hleft)).mono ?_
    rintro y ⟨htail_y, hB_y, hA_y⟩
    change sign (A.eval y) = -sign (B.eval x) at hA_y
    have hbx_ne : sign (B.eval x) ≠ 0 := sign_ne_zero.mpr hdne
    have hne_neg : -sign (B.eval x) ≠ 0 := by revert hbx_ne; cases sign (B.eval x) <;> decide
    have hne_sign : sign (A.eval y) ≠ sign (B.eval y) := by
      rw [hA_y, hB_y]; revert hbx_ne; cases sign (B.eval x) <;> decide
    rw [hstep htail_y hB_y (hA_y ▸ hne_neg), ite_eq_right hne_sign, Nat.add_comm]

/-- Combining left-neighborhood, value-at-`x`, and right-neighborhood statements on `ℝ` into a
full `𝓝 x` statement. -/
private theorem eventually_nhds_of_lt_of_gt {P : ℝ → Prop} {x : ℝ} (hx : P x)
    (hlt : ∀ᶠ y in 𝓝[<] x, P y) (hgt : ∀ᶠ y in 𝓝[>] x, P y) : ∀ᶠ y in 𝓝 x, P y := by
  obtain ⟨a, ha, ha_sub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hlt
  obtain ⟨b, hb, hb_sub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hgt
  refine Filter.mem_of_superset (Ioo_mem_nhds ha hb) fun y hy => ?_
  rcases lt_trichotomy y x with hlt' | rfl | hgt'
  · exact ha_sub ⟨hy.1, hlt'⟩
  · exact hx
  · exact hb_sub ⟨hgt', hy.2⟩

/-- The augmented function `sturmReducedVariations p x + #{r ∈ p.roots.toFinset | r ≤ x}` is locally
constant on `ℝ` for every nonzero `p : ℝ[X]`. -/
private theorem isLocallyConstant_sturmReducedVariations_add_card {p : ℝ[X]} (hp : p ≠ 0) :
    IsLocallyConstant (fun x : ℝ =>
      sturmReducedVariations p x + (p.roots.toFinset.filter (· ≤ x)).card) := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
  have hno_other : ∀ᶠ y in 𝓝 x,
      ∀ r ∈ p.roots.toFinset, r ≠ x → (r ≤ y ↔ r ≤ x) := by
    refine (Filter.eventually_all_finset p.roots.toFinset).mpr fun r _ => ?_
    by_cases hrx : r = x
    · exact Eventually.of_forall fun _ h => absurd hrx h
    · rcases lt_or_gt_of_ne hrx with hlt | hgt
      · filter_upwards [lt_mem_nhds hlt] with y hy _
        exact iff_of_true hy.le hlt.le
      · filter_upwards [gt_mem_nhds hgt] with y hy _
        exact iff_of_false (not_le_of_gt hy) (not_le_of_gt hgt)
  have hgt_filter : ∀ᶠ y in 𝓝[>] x,
      (p.roots.toFinset.filter (· ≤ y)).card = (p.roots.toFinset.filter (· ≤ x)).card := by
    refine ((hno_other.filter_mono nhdsWithin_le_nhds).and eventually_mem_nhdsWithin).mono ?_
    rintro y ⟨hy, hxy⟩
    congr 1
    ext r
    simp only [Finset.mem_filter, and_congr_right_iff]
    intro hr
    by_cases hrx : r = x
    · subst hrx
      exact iff_of_true (le_of_lt hxy) le_rfl
    · exact hy r hr hrx
  have hlt_filter : ∀ᶠ y in 𝓝[<] x,
      (p.roots.toFinset.filter (· ≤ y)).card + (if p.eval x = 0 then 1 else 0) =
        (p.roots.toFinset.filter (· ≤ x)).card := by
    refine ((hno_other.filter_mono nhdsWithin_le_nhds).and eventually_mem_nhdsWithin).mono ?_
    rintro y ⟨hy, hyx⟩
    by_cases hpx : p.eval x = 0
    · have hxmem : x ∈ p.roots.toFinset :=
        Multiset.mem_toFinset.mpr ((mem_roots hp).mpr hpx)
      have hxnot : x ∉ p.roots.toFinset.filter (· ≤ y) := by
        simp only [Finset.mem_filter, not_and, not_le]
        intro _
        exact hyx
      have heq : p.roots.toFinset.filter (· ≤ x) =
          insert x (p.roots.toFinset.filter (· ≤ y)) := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hr, hle⟩
          rcases eq_or_ne r x with rfl | hrx
          · exact Or.inl rfl
          · exact Or.inr ⟨hr, (hy r hr hrx).mpr hle⟩
        · rintro (rfl | ⟨hr, hle⟩)
          · exact ⟨hxmem, le_rfl⟩
          · by_cases hrx : r = x
            · subst hrx; exact ⟨hxmem, le_rfl⟩
            · exact ⟨hr, (hy r hr hrx).mp hle⟩
      rw [ite_eq_left hpx, heq, Finset.card_insert_of_notMem hxnot, add_comm]
    · rw [ite_eq_right hpx, add_zero]
      congr 1
      ext r
      simp only [Finset.mem_filter, and_congr_right_iff]
      intro hr
      have hrx : r ≠ x := fun h => hpx (h ▸ isRoot_of_mem_roots (Multiset.mem_toFinset.mp hr))
      exact hy r hr hrx
  have hcombine :
      (∀ᶠ y in 𝓝[>] x, sturmReducedVariations p y = sturmReducedVariations p x) →
      (∀ᶠ y in 𝓝[<] x, sturmReducedVariations p y =
        sturmReducedVariations p x + (if p.eval x = 0 then 1 else 0)) →
      ∀ᶠ y in 𝓝 x,
        sturmReducedVariations p y + (p.roots.toFinset.filter (· ≤ y)).card =
          sturmReducedVariations p x + (p.roots.toFinset.filter (· ≤ x)).card :=
    fun hgt_v hlt_v => eventually_nhds_of_lt_of_gt rfl
      (by filter_upwards [hlt_v, hlt_filter] with y hy1 hy2; omega)
      (by filter_upwards [hgt_v, hgt_filter] with y hy1 hy2; rw [hy1, hy2])
  by_cases hpx : p.eval x = 0
  · obtain ⟨hsv_gt, hsv_lt⟩ := eventually_sturmReducedVariations_of_eval_eq_zero hp hpx
    exact hcombine hsv_gt (by simpa only [ite_eq_left hpx] using hsv_lt)
  · have hsv := eventually_sturmReducedVariations_of_eval_ne_zero hp hpx
    exact hcombine (hsv.filter_mono nhdsWithin_le_nhds)
      (by simpa only [ite_eq_right hpx, add_zero] using hsv.filter_mono nhdsWithin_le_nhds)

/-- **General Sturm's theorem** via reduced coprime Sturm variations: for any nonzero `p : ℝ[X]`
and `a ≤ b`, `sturmReducedVariations p a - sturmReducedVariations p b` equals the number of
distinct real roots of `p` in `(a, b]` (counted without multiplicity). -/
theorem sturmReducedVariations_sub_eq_card_roots_Ioc {p : ℝ[X]} (hp : p ≠ 0) {a b : ℝ}
    (hab : a ≤ b) :
    sturmReducedVariations p a - sturmReducedVariations p b =
      (p.roots.toFinset.filter (fun r => a < r ∧ r ≤ b)).card := by
  have hconst :=
    (isLocallyConstant_sturmReducedVariations_add_card hp).apply_eq_of_preconnectedSpace a b
  have hsplit : p.roots.toFinset.filter (· ≤ b) =
      p.roots.toFinset.filter (· ≤ a) ∪ p.roots.toFinset.filter (fun r => a < r ∧ r ≤ b) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hr, hrb⟩
      rcases le_or_gt r a with hra | har
      · exact Or.inl ⟨hr, hra⟩
      · exact Or.inr ⟨hr, har, hrb⟩
    · rintro (⟨hr, hra⟩ | ⟨hr, _, hrb⟩)
      · exact ⟨hr, hra.trans hab⟩
      · exact ⟨hr, hrb⟩
  have hdisj : Disjoint (p.roots.toFinset.filter (· ≤ a))
      (p.roots.toFinset.filter (fun r => a < r ∧ r ≤ b)) := by
    rw [Finset.disjoint_left]
    intro r hr1 hr2
    simp only [Finset.mem_filter] at hr1 hr2
    linarith [hr1.2, hr2.2.1]
  rw [hsplit, Finset.card_union_of_disjoint hdisj] at hconst
  omega

/-- `sturmReducedVariations p` is antitone on `ℝ` for every nonzero `p : ℝ[X]`. -/
theorem sturmReducedVariations_antitone {p : ℝ[X]} (hp : p ≠ 0) :
    Antitone (sturmReducedVariations p) := by
  intro a b hab
  have hconst :=
    (isLocallyConstant_sturmReducedVariations_add_card hp).apply_eq_of_preconnectedSpace a b
  have hsub : p.roots.toFinset.filter (· ≤ a) ⊆ p.roots.toFinset.filter (· ≤ b) := by
    intro r hr
    simp only [Finset.mem_filter] at hr ⊢
    exact ⟨hr.1, hr.2.trans hab⟩
  have hcard := Finset.card_le_card hsub
  omega

/-- **General Sturm's theorem** on `(a, b]` for any nonzero `p : ℝ[X]` whose multiple-root divisor
`gcd p (derivative p)` does not vanish at `a` or `b` (after [BasuPollackRoy2006], Theorem 2.50,
p. 52, adapted to finite real endpoints on `(a, b]`). -/
theorem sturmVariations_sub_eq_card_roots_Ioc_of_gcd_eval_ne_zero {p : ℝ[X]} (hp : p ≠ 0)
    {a b : ℝ} (hab : a ≤ b)
    (ha : (open Classical in EuclideanDomain.gcd p (derivative p)).eval a ≠ 0)
    (hb : (open Classical in EuclideanDomain.gcd p (derivative p)).eval b ≠ 0) :
    sturmVariations p a - sturmVariations p b =
      (p.roots.toFinset.filter (fun r => a < r ∧ r ≤ b)).card := by
  rw [sturmVariations_eq_sturmReducedVariations hp ha,
    sturmVariations_eq_sturmReducedVariations hp hb]
  exact sturmReducedVariations_sub_eq_card_roots_Ioc hp hab

/-- **Sturm's theorem** on half-open intervals `(a, b]` for separable `p : ℝ[X]`
(after [BasuPollackRoy2006], Theorem 2.50, p. 52, adapted to finite real endpoints on `(a, b]`):
the drop `sturmVariations p a - sturmVariations p b` equals the number of distinct real roots of
`p` in `(a, b]`, with no nonvanishing assumption on the endpoints. -/
theorem sturmVariations_sub_eq_card_roots_Ioc {p : ℝ[X]} (hp : p.Separable) {a b : ℝ}
    (hab : a ≤ b) :
    sturmVariations p a - sturmVariations p b =
      (p.roots.toFinset.filter (fun r => a < r ∧ r ≤ b)).card := by
  rw [sturmVariations_eq_sturmReducedVariations_of_separable hp a,
    sturmVariations_eq_sturmReducedVariations_of_separable hp b]
  exact sturmReducedVariations_sub_eq_card_roots_Ioc hp.ne_zero hab

/-- `sturmVariations p` is antitone on `ℝ` for separable `p : ℝ[X]`. -/
theorem sturmVariations_antitone {p : ℝ[X]} (hp : p.Separable) :
    Antitone (sturmVariations p) := by
  intro a b hab
  rw [sturmVariations_eq_sturmReducedVariations_of_separable hp a,
    sturmVariations_eq_sturmReducedVariations_of_separable hp b]
  exact sturmReducedVariations_antitone hp.ne_zero hab

/-- Squarefree version of Sturm's theorem on `(a, b]` over `ℝ[X]`. -/
theorem sturmVariations_sub_eq_card_roots_Ioc_of_squarefree {p : ℝ[X]} (hp : Squarefree p)
    {a b : ℝ} (hab : a ≤ b) :
    sturmVariations p a - sturmVariations p b =
      (p.roots.toFinset.filter (fun r => a < r ∧ r ≤ b)).card :=
  sturmVariations_sub_eq_card_roots_Ioc (PerfectField.separable_iff_squarefree.mpr hp) hab

/-- Open-interval form of Sturm's theorem when `b` is not a root. -/
theorem sturmVariations_sub_eq_card_roots_Ioo {p : ℝ[X]} (hp : p.Separable) {a b : ℝ}
    (hab : a ≤ b) (hb : p.eval b ≠ 0) :
    sturmVariations p a - sturmVariations p b =
      (p.roots.toFinset.filter (fun r => a < r ∧ r < b)).card := by
  rw [sturmVariations_sub_eq_card_roots_Ioc hp hab]
  congr 1
  ext r
  simp only [Finset.mem_filter, Multiset.mem_toFinset, mem_roots hp.ne_zero, IsRoot.def]
  constructor
  · rintro ⟨hr, har, hrb⟩
    refine ⟨hr, har, lt_of_le_of_ne hrb ?_⟩
    intro hreq
    subst hreq
    exact hb hr
  · rintro ⟨hr, har, hrb⟩
    exact ⟨hr, har, hrb.le⟩

/-- Closed-interval form of Sturm's theorem when the left endpoint is not a root. -/
theorem sturmVariations_sub_eq_card_roots_Icc {p : ℝ[X]} (hp : p.Separable) {a b : ℝ}
    (hab : a ≤ b) (ha : p.eval a ≠ 0) :
    sturmVariations p a - sturmVariations p b =
      (p.roots.toFinset.filter (fun r => a ≤ r ∧ r ≤ b)).card := by
  rw [sturmVariations_sub_eq_card_roots_Ioc hp hab]
  congr 1
  ext r
  simp only [Finset.mem_filter, Multiset.mem_toFinset, mem_roots hp.ne_zero, IsRoot.def]
  constructor
  · rintro ⟨hr, har, hrb⟩
    exact ⟨hr, har.le, hrb⟩
  · rintro ⟨hr, har, hrb⟩
    refine ⟨hr, lt_of_le_of_ne har ?_, hrb⟩
    intro hreq
    subst hreq
    exact ha hr

end Polynomial
