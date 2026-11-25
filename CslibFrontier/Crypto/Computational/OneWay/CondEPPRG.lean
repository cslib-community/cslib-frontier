/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.OneWay
public import CslibFrontier.Crypto.Computational.OneWay.Normalize
public import CslibFrontier.Crypto.Computational.Pseudoentropy.WordReduction
public import CslibFrontier.Probability.Entropy.BitString
public import CslibFrontier.Crypto.Computational.GeneratorReindex
public import CslibFrontier.Foundations.Data.BitString.List.Binary
import CslibFrontier.Computability.Probabilistic.LinearHash
import CslibFrontier.Computability.Probabilistic.UniformNat
import CslibFrontier.Computability.Probabilistic.CoinTape
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Crypto.Primitives.PRG.NextBit
import CslibFrontier.Crypto.Game.Statistical
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.StatisticalDistance.ClosedForm
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Foundations.Data.Nat.Asymptotics
import CslibFrontier.Tactic.PMFSwap
import CslibFrontier.Tactic.PPT
import CslibFrontier.Tactic.EncLen

/-!
# Conditional Entropy-Preserving Pseudorandom Generators from One-Way Functions

This module formalizes conditional entropy-preserving pseudorandom generators
($\mu$-condEP-PRGs) and their construction from one-way functions following
[Y. Liu and R. Pass, *On One-Way Functions and Kolmogorov Complexity*][LiuPass2020]. All section,
definition, theorem, lemma, and page locators follow the full version `arXiv:2009.11514v1`
(and ECCC TR20-052): Section 5 (Definition 5.1, §5.1, p. 11; Lemma 5.1, §5.3, p. 14; Lemma 5.2,
§5.3, p. 15; Theorem 5.5, §5.3, p. 15) and Appendix A (printed pp. 21–23, PDF pp. 22–24). Note that
in `arXiv:2009.11514v1`, `Theorem` and `Definition` share one section counter while `Lemma` and
`Fact` share a separate section counter.

## Main definitions

* `Cslib.Crypto.CondEPPRG`: $(\mu, \gamma)$-conditional entropy-preserving pseudorandom generator
  with entropy-loss constant $\alpha$
  ([Liu and Pass, Definition 5.1, §5.1, p. 11 of arXiv:2009.11514v1][LiuPass2020]).
* `Cslib.Crypto.regularityBucket`: regularity buckets partitioning $\{0, 1\}^n$ by logarithmic
  preimage fiber size $\lfloor \log_2 |f^{-1}(f(x))| \rfloor \in \{0, \dots, n\}$
  ([Liu and Pass, Lemma 5.2, §5.3, p. 15 of arXiv:2009.11514v1][LiuPass2020]).

## Main results

* `Cslib.Crypto.exists_regularity_bucket`: for every `f : BitString n → Image`, some regularity
  bucket $S_{n, r}$ has cardinality at least $2^n / (n + 1)$ and every $x \in S_{n, r}$ has fiber
  cardinality in $[2^r, 2^{r + 1})$
  ([Liu and Pass, Lemma 5.2 and Claim 3, §5.3, p. 15 of arXiv:2009.11514v1][LiuPass2020]).
* `Cslib.Crypto.OneWay.exists_condEPPRG`: every one-way function yields a
  $(1 / n^\delta, \gamma)$-condEP-PRG for any prescribed stretch factor $\gamma$ and polynomial
  security exponent $\delta$
  ([Liu and Pass, Theorem 5.5, §5.3, p. 15 of arXiv:2009.11514v1][LiuPass2020]).

## References

* [Y. Liu and R. Pass, *On One-Way Functions and Kolmogorov Complexity*][LiuPass2020],
  full version `arXiv:2009.11514v1` (Section 5 and Appendix A).
-/

public section

namespace Cslib.Crypto

open Probability Probability.PMF BitString Filter Turing.MultiTapeTM
open scoped NNReal ENNReal

/-! ### Definition 5.1: Conditional entropy-preserving PRG -/

/-- **[Liu and Pass, Definition 5.1, §5.1, p. 11 of arXiv:2009.11514v1][LiuPass2020]: Conditional
entropy-preserving pseudorandom generator ($\mu$-condEP-PRG).**
A deterministic polynomial-time function $G : \{0, 1\}^* \to \{0, 1\}^*$ is a
$(\mu, \gamma)$-condEP-PRG with entropy-loss constant $\alpha$ if:
1. $G$ is computable in polynomial time (`ComputableInPolyTime G encBits encBits`),
2. $G$ stretches every $n$-bit seed $z \in \{0, 1\}^n$ to length
   $n + \gamma \lfloor \log_2 n \rfloor$,
3. there exists a sequence of nonempty conditioning events $E_n \subseteq \{0, 1\}^n$ such that:
   - **(Conditional pseudorandomness):** For every uniform strict PPT distinguisher $\mathcal{A}$,
     eventually in $n$, the distinguishing advantage between $G(U_n \mid E_n)$ and
     $U_{n + \gamma \lfloor \log_2 n \rfloor}$ is at most $\mu(n)$ (`≤ μ n`; note that
     [LiuPass2020], Definition 2.6, p. 9 writes strict `< μ(n)`),
   - **(Conditional entropy preservation):** Eventually in $n$, the Shannon entropy of
     $G(U_n \mid E_n)$ (base 2) is at least $n - \alpha \lfloor \log_2 n \rfloor$.

Deviations from Definition 5.1: `γ` and `α` are natural numbers with `Nat.log 2 n` (`⌊log₂ n⌋`) in
place of real constants and `log n`; `α` is an explicit parameter of `CondEPPRG` rather than
existentially quantified; `E n` is explicitly required to be nonempty; distinguishers are uniform
strict PPT (`IsPPT encBool`) rather than general PPT machines clocked only in `1^n`; and the
distinguishing bound uses `≤ μ n` instead of `< μ(n)`. -/
@[expose] def CondEPPRG (G : List Bool → List Bool) (μ : ℕ → ℝ) (γ α : ℕ) : Prop :=
  ComputableInPolyTime G encBits encBits ∧
  (∀ z : List Bool, (G z).length = z.length + γ * Nat.log 2 z.length) ∧
  ∃ (E : ∀ n, Finset (BitString n)) (hE : ∀ n, (E n).Nonempty),
    (∀ adversary : Distinguisher, IsPPT encBool adversary →
      ∀ᶠ n : ℕ in atTop,
        (Game.advantage
          ((((PMF.uniformOfFinset (E n) (hE n)).map List.ofFn).map G).bind
            fun y => ProbComp.eval (adversary n y))
          ((BitString.uniformList (n + γ * Nat.log 2 n)).bind
            fun y => ProbComp.eval (adversary n y)) : ℝ) ≤ μ n) ∧
    (∀ᶠ n : ℕ in atTop,
      (n : ℝ) - (α : ℝ) * (Nat.log 2 n : ℝ) ≤
        PMF.entropy ((PMF.uniformOfFinset (E n) (hE n)).map fun x =>
          BitString.ofList (n + γ * Nat.log 2 n) (G (List.ofFn x))))

/-! ### Lemma 5.2: Regularity bucket pigeonhole -/

/-- Logarithmic fiber size
$\lfloor \log_2 |\{x' : f(x') = f(x)\}| \rfloor \in \mathrm{Fin}\; (n + 1)$
of an input $x \in \mathrm{BitString}\; n$ under $f$. -/
@[expose] noncomputable def fiberLogIndex {n : ℕ} {Image : Type*} (f : BitString n → Image)
    (x : BitString n) : Fin (n + 1) := by
  classical
  refine ⟨Nat.log 2 (Nat.card {x' : BitString n // f x' = f x}), ?_⟩
  have hcard : Nat.card {x' : BitString n // f x' = f x} ≤ 2 ^ n := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin] using Fintype.card_subtype_le (fun x' : BitString n => f x' = f x)
  exact Nat.lt_succ_of_le ((Nat.log_mono_right hcard).trans_eq (Nat.log_pow Nat.one_lt_two n))

/-- The $r$-th regularity bucket $S_{n, r} = \{x \in \mathrm{BitString}\; n :
\lfloor \log_2 |f^{-1}(f(x))| \rfloor = r\}$
([Liu and Pass, Proof of Lemma 5.2, §5.3, p. 15 of arXiv:2009.11514v1][LiuPass2020]). -/
@[expose] noncomputable def regularityBucket {n : ℕ} {Image : Type*} (f : BitString n → Image)
    (r : Fin (n + 1)) : Finset (BitString n) := by
  classical
  exact Finset.univ.filter fun x => fiberLogIndex f x = r

@[simp]
theorem mem_regularityBucket {n : ℕ} {Image : Type*} (f : BitString n → Image)
    (r : Fin (n + 1)) (x : BitString n) :
    x ∈ regularityBucket f r ↔ fiberLogIndex f x = r := by
  classical
  simp only [regularityBucket, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Every input $x$ in `regularityBucket f r` has fiber cardinality in $[2^r, 2^{r + 1})$. -/
theorem card_fiber_of_mem_regularityBucket {n : ℕ} {Image : Type*} (f : BitString n → Image)
    (r : Fin (n + 1)) {x : BitString n} (hx : x ∈ regularityBucket f r) :
    2 ^ r.val ≤ Nat.card {x' : BitString n // f x' = f x} ∧
      Nat.card {x' : BitString n // f x' = f x} < 2 ^ (r.val + 1) := by
  classical
  have hfib : Nat.log 2 (Nat.card {x' : BitString n // f x' = f x}) = r.val :=
    congrArg Fin.val ((mem_regularityBucket f r x).mp hx)
  have : Nonempty {x' : BitString n // f x' = f x} := ⟨⟨x, rfl⟩⟩
  rw [← hfib]
  exact ⟨Nat.pow_log_le_self 2 Nat.card_pos.ne', Nat.lt_pow_succ_log_self Nat.one_lt_two _⟩

/-- `regularityBucket f r` is a union of full fibers of `f`: if $f(x') = f(x)$, then
$x' \in S_{n, r} \iff x \in S_{n, r}$. -/
theorem mem_regularityBucket_of_eq {n : ℕ} {Image : Type*} (f : BitString n → Image)
    (r : Fin (n + 1)) {x x' : BitString n} (heq : f x' = f x) :
    x' ∈ regularityBucket f r ↔ x ∈ regularityBucket f r := by
  simp only [mem_regularityBucket, Fin.ext_iff, fiberLogIndex, heq]

/-- **[Liu and Pass, Lemma 5.2 and Claim 3, §5.3, p. 15 of arXiv:2009.11514v1][LiuPass2020]:
Existence of a dense regularity bucket.**
For every $n$ and every function $f : \mathrm{BitString}\; n \to \mathrm{Image}$, there exists a
regularity index $r \in \mathrm{Fin}\; (n + 1)$ such that the bucket $S_{n, r}$ has cardinality at
least $2^n / (n + 1)$ (i.e. $2^n \le (n + 1) \cdot |S_{n, r}|$), is nonempty, and every
$x \in S_{n, r}$ has fiber size in $[2^r, 2^{r + 1})$. -/
theorem exists_regularity_bucket {n : ℕ} {Image : Type*} (f : BitString n → Image) :
    ∃ r : Fin (n + 1),
      (regularityBucket f r).Nonempty ∧
      2 ^ n ≤ (n + 1) * (regularityBucket f r).card ∧
      ∀ x ∈ regularityBucket f r,
        2 ^ r.val ≤ Nat.card {x' : BitString n // f x' = f x} ∧
          Nat.card {x' : BitString n // f x' = f x} < 2 ^ (r.val + 1) := by
  classical
  have hsum : ∑ r : Fin (n + 1), (regularityBucket f r).card = 2 ^ n := by
    simpa only [regularityBucket, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin] using (Finset.card_eq_sum_card_fiberwise
      (f := fiberLogIndex f) (s := Finset.univ) (t := Finset.univ) fun _ _ =>
        Finset.mem_univ _).symm
  obtain ⟨r, -, hr⟩ : ∃ r ∈ (Finset.univ : Finset (Fin (n + 1))),
      2 ^ n ≤ (n + 1) * (regularityBucket f r).card := by
    by_contra! hlt
    have hlt' := Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_univ _⟩ hlt
    rw [← Finset.mul_sum, hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at hlt'
    exact hlt'.false
  exact ⟨r, Finset.card_pos.mp (Nat.pos_of_mul_pos_left (lt_of_lt_of_le (by positivity) hr)), hr,
    fun _ hx => card_fiber_of_mem_regularityBucket f r hx⟩

/-! ### Fiber resampling and regularity bucket mass bounds -/

private theorem uniformOfFintype_fiber_map_val_apply {n : ℕ} {Image : Type*} [DecidableEq Image]
    (f : BitString n → Image) (x₀ z : BitString n) :
    haveI : Nonempty {x : BitString n // f x = f x₀} := ⟨⟨x₀, rfl⟩⟩
    ((PMF.uniformOfFintype {x : BitString n // f x = f x₀}).map Subtype.val) z =
      if f z = f x₀ then (Fintype.card {x : BitString n // f x = f z} : ℝ≥0∞)⁻¹ else 0 := by
  have : Nonempty {x : BitString n // f x = f x₀} := ⟨⟨x₀, rfl⟩⟩
  split_ifs with hfz
  · rw [map_apply_of_injective _ Subtype.val_injective ⟨z, hfz⟩, PMF.uniformOfFintype_apply]
    congr 2
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun x => by rw [hfz])
  · rw [PMF.map_apply, tsum_fintype]
    exact Finset.sum_eq_zero fun b _ => ite_eq_right fun h : z = b.1 => hfz (h ▸ b.2)

/-- Resampling a preimage uniformly from the fiber of an element drawn uniformly from a
nonempty regularity bucket recovers `uniformOfFinset (regularityBucket f r) hS`. -/
theorem bind_regularityBucket_fiber_eq {n : ℕ} {Image : Type*} [DecidableEq Image]
    (f : BitString n → Image) (r : Fin (n + 1)) (hS : (regularityBucket f r).Nonempty) :
    haveI (x₀ : BitString n) : Nonempty {x : BitString n // f x = f x₀} := ⟨⟨x₀, rfl⟩⟩
    (PMF.uniformOfFinset (regularityBucket f r) hS).bind
      (fun x₀ => (PMF.uniformOfFintype {x : BitString n // f x = f x₀}).map Subtype.val) =
      PMF.uniformOfFinset (regularityBucket f r) hS := by
  classical
  have (x₀ : BitString n) : Nonempty {x : BitString n // f x = f x₀} := ⟨⟨x₀, rfl⟩⟩
  ext z
  have : Nonempty {x : BitString n // f x = f z} := ⟨⟨z, rfl⟩⟩
  rw [PMF.bind_apply, tsum_fintype]
  simp_rw [uniformOfFintype_fiber_map_val_apply, PMF.uniformOfFinset_apply]
  trans (∑ x₀ : BitString n, if f x₀ = f z then
      (if z ∈ regularityBucket f r then ((regularityBucket f r).card : ℝ≥0∞)⁻¹ else 0) *
        (Fintype.card {x : BitString n // f x = f z} : ℝ≥0∞)⁻¹ else 0)
  · refine Finset.sum_congr rfl fun x₀ _ => ?_
    by_cases hfx : f x₀ = f z
    · simp only [hfx, ↓reduceIte, mem_regularityBucket_of_eq f r hfx]
    · simp only [hfx, Ne.symm hfx, ↓reduceIte, mul_zero]
  · rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_left_comm,
      ← Fintype.card_subtype, ENNReal.mul_inv_cancel
        (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) (ENNReal.natCast_ne_top _), mul_one]
    congr 1

/-- Averaging any real-valued function over `x₀ ← uniformOfFinset (regularityBucket f r)` and
`x ← uniformOfFintype {x // f x = f x₀}` equals its average over `x ← uniformOfFinset`. -/
theorem sum_regularityBucket_fiber_eq {n : ℕ} {Image : Type*} [DecidableEq Image]
    (f : BitString n → Image) (r : Fin (n + 1)) (hS : (regularityBucket f r).Nonempty)
    (Φ : BitString n → ℝ) :
    haveI (x₀ : BitString n) : Nonempty {x : BitString n // f x = f x₀} := ⟨⟨x₀, rfl⟩⟩
    ∑ x₀ : BitString n, (PMF.uniformOfFinset (regularityBucket f r) hS x₀).toReal *
      ∑ x : {x : BitString n // f x = f x₀},
        (PMF.uniformOfFintype {x : BitString n // f x = f x₀} x).toReal * Φ x.1 =
      ∑ x : BitString n, (PMF.uniformOfFinset (regularityBucket f r) hS x).toReal * Φ x := by
  have (x₀ : BitString n) : Nonempty {x : BitString n // f x = f x₀} := ⟨⟨x₀, rfl⟩⟩
  conv_lhs =>
    arg 2; ext x₀
    rw [← sum_map_mul (PMF.uniformOfFintype {x : BitString n // f x = f x₀}) Subtype.val Φ]
  rw [← sum_bind_mul, bind_regularityBucket_fiber_eq]

/-- Pointwise image probability bound when $x$ is drawn uniformly from a dense regularity bucket
$S_{n, r}$ with $2^n \le (n + 1) \cdot |S_{n, r}|$. -/
theorem mass_map_regularityBucket_le {n : ℕ} {Image : Type*}
    (f : BitString n → Image) (r : Fin (n + 1)) (hS : (regularityBucket f r).Nonempty)
    (hdense : 2 ^ n ≤ (n + 1) * (regularityBucket f r).card) (y : Image) :
    (((PMF.uniformOfFinset (regularityBucket f r) hS).map f) y).toReal ≤
      (2 * (n + 1 : ℝ) * (2 : ℝ) ^ r.val) / (2 : ℝ) ^ n := by
  classical
  let S := regularityBucket f r
  have hmap : (((PMF.uniformOfFinset S hS).map f) y).toReal =
      ((S.filter fun x => f x = y).card : ℝ) / S.card := by
    have h := toOuterMeasure_uniformOfFinset_toReal S hS {x | f x = y}
    simpa only [PMF.toOuterMeasure_apply, PMF.map_apply, eq_comm, Set.indicator_apply,
      Set.mem_ofPred_eq, tsum_fintype, ← Finset.sum_filter] using h
  have hcard_le : (S.filter fun x => f x = y).card ≤ 2 * 2 ^ r.val := by
    rcases (S.filter fun x => f x = y).eq_empty_or_nonempty with hemp | ⟨x₀, hx₀⟩
    · simp [hemp]
    · rw [Finset.mem_filter] at hx₀
      have hlt := (card_fiber_of_mem_regularityBucket f r hx₀.1).2
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype, pow_succ'] at hlt
      exact (Finset.card_le_card fun _ hx => Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2.trans hx₀.2.symm⟩).trans hlt.le
  rw [hmap, div_le_div_iff₀ (Nat.cast_pos.mpr hS.card_pos) (by positivity)]
  calc ((S.filter fun x => f x = y).card : ℝ) * (2 : ℝ) ^ n
      ≤ (2 * (2 : ℝ) ^ r.val) * ((n + 1 : ℝ) * S.card) := by gcongr <;> assumption_mod_cast
    _ = _ := by ring

private theorem uniformOfFintype_bitString_toReal (k : ℕ) (x : BitString k) :
    (PMF.uniformOfFintype (BitString k) x).toReal = ((2 : ℝ) ^ k)⁻¹ := by
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Nat.cast_pow, Nat.cast_ofNat, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat]

/-- For any nonnegative function $G : \mathrm{BitString}\; n \to \mathbb{R}$, its expectation over
$S_{n, r}$ (with $2^n \le (n + 1) |S_{n, r}|$) is at most $(n + 1)$ times its expectation over the
uniform distribution on $\mathrm{BitString}\; n$. -/
private theorem sum_uniformOfFinset_le_mul_uniformOfFintype {n : ℕ}
    (S : Finset (BitString n)) (hS : S.Nonempty) (hdense : 2 ^ n ≤ (n + 1) * S.card)
    (G : BitString n → ℝ) (hG : ∀ x, 0 ≤ G x) :
    ∑ x : BitString n, (PMF.uniformOfFinset S hS x).toReal * G x ≤
      (n + 1 : ℝ) * ∑ x : BitString n, (PMF.uniformOfFintype (BitString n) x).toReal * G x := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => by
    rw [← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (hG x)
    rw [PMF.uniformOfFinset_apply, uniformOfFintype_bitString_toReal]
    split_ifs
    · rw [ENNReal.toReal_inv, ENNReal.toReal_natCast, inv_eq_one_div, inv_eq_one_div, mul_one_div,
        div_le_div_iff₀ (Nat.cast_pos.mpr hS.card_pos) (by positivity)]
      have : (2 : ℝ) ^ n ≤ (n + 1 : ℝ) * S.card := by exact_mod_cast hdense
      linarith
    · rw [ENNReal.toReal_zero]; positivity

/-! ### Trivial inverter and regularity deficit bound -/

/-- The trivial inverter that ignores the challenge image and samples a uniform $k$-bit string. -/
private noncomputable def trivialInverter : Inverter := fun k _ => BitString.sampleList k

private theorem isPPT_trivialInverter : IsPPT encBits trivialInverter :=
  (ComputableInPolyTime.fst encUnary encBits).sampleList

private theorem uniformOfFintype_bool_toReal (b : Bool) :
    (PMF.uniformOfFintype Bool b).toReal = 1 / 2 := by
  simp only [PMF.uniformOfFintype_apply, Fintype.card_bool, Nat.cast_ofNat, ENNReal.toReal_inv,
    ENNReal.toReal_ofNat, one_div]

private abbrev finiteFn (g : List Bool → List Bool) (imgLen : ℕ → ℕ) (k : ℕ) :
    BitString k → BitString (imgLen k) :=
  fun x => ofList (imgLen k) (g (List.ofFn x))

private theorem finiteFn_ofFn {g : List Bool → List Bool} {imgLen : ℕ → ℕ}
    (himgLen : ∀ x, (g x).length = imgLen x.length) {k : ℕ} (x : BitString k) :
    List.ofFn (finiteFn g imgLen k x) = g (List.ofFn x) :=
  ofFn_ofList (by simp only [himgLen, List.length_ofFn])

private theorem trivialInverter_succ_ge {g : List Bool → List Bool} {imgLen : ℕ → ℕ}
    (himgLen : ∀ x, (g x).length = imgLen x.length) (k : ℕ)
    (r : Fin (k + 1))
    (hdense : 2 ^ k ≤ (k + 1) * (regularityBucket (finiteFn g imgLen k) r).card) :
    ((2 : ℝ) ^ r.val) / ((k + 1 : ℝ) * (2 : ℝ) ^ k) ≤
      (Game.succProbability (ProbComp.eval (inversionGame g trivialInverter k)) : ℝ) := by
  classical
  let f := finiteFn g imgLen k
  let S := regularityBucket f r
  have hfeq (x x' : BitString k) : (g (List.ofFn x') == g (List.ofFn x)) = decide (f x' = f x) := by
    rw [beq_eq_decide]
    refine decide_eq_decide.mpr ⟨fun h => by simp only [f, finiteFn, h], fun h => ?_⟩
    simpa only [f, finiteFn_ofFn himgLen] using congrArg List.ofFn h
  have heval : (Game.succProbability (ProbComp.eval (inversionGame g trivialInverter k)) : ℝ) =
      ((2 : ℝ) ^ k)⁻¹ * ((2 : ℝ) ^ k)⁻¹ *
        ∑ x : BitString k, (Nat.card {x' : BitString k // f x' = f x} : ℝ) := by
    rw [Game.coe_succProbability]
    simp only [pmf_norm, inversionGame, inversionExperiment, trivialInverter,
      BitString.eval_sampleList, BitString.uniformList, bind_apply_toReal, PMF.pure_apply,
      uniformOfFintype_bitString_toReal, hfeq, ← Finset.mul_sum, mul_assoc]
    congr 2; refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, apply_ite ENNReal.toReal,
      ENNReal.toReal_one, ENNReal.toReal_zero, eq_comm (a := true), decide_eq_true_eq,
      Finset.sum_boole]
  have hsum : (S.card : ℝ) * (2 : ℝ) ^ r.val ≤
      ∑ x : BitString k, (Nat.card {x' : BitString k // f x' = f x} : ℝ) := by
    calc (S.card : ℝ) * (2 : ℝ) ^ r.val
        = ∑ _x ∈ S, (2 : ℝ) ^ r.val := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ x ∈ S, (Nat.card {x' : BitString k // f x' = f x} : ℝ) :=
          Finset.sum_le_sum fun x hx => by
            exact_mod_cast (card_fiber_of_mem_regularityBucket f r hx).1
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) fun _ _ _ =>
          Nat.cast_nonneg _
  have hdense_r : (2 : ℝ) ^ k ≤ (k + 1 : ℝ) * S.card := by exact_mod_cast hdense
  have hstep : (2 : ℝ) ^ r.val / ((k + 1 : ℝ) * (2 : ℝ) ^ k) ≤
      (2 : ℝ) ^ r.val * S.card / ((2 : ℝ) ^ k * (2 : ℝ) ^ k) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [show (0 : ℝ) ≤ (2 : ℝ) ^ r.val * (2 : ℝ) ^ k by positivity]
  rw [heval]
  refine (hstep.trans_eq (by ring)).trans (mul_le_mul_of_nonneg_left hsum (by positivity))

private theorem two_pow_mul_log_le_pow (A : ℕ) {k : ℕ} (hk : 0 < k) :
    2 ^ (A * Nat.log 2 k) ≤ k ^ A := by
  rw [mul_comm, pow_mul]
  exact Nat.pow_le_pow_left (Nat.pow_log_le_self 2 hk.ne') A

/-- For any one-way function $g$ with fixed output length `imgLen` and any sequence of dense
regularity indices $r(k)$, for every constant $D \in \mathbb{N}$ we eventually have
$r(k) + D \lfloor \log_2 k \rfloor \le k$. -/
theorem eventually_regularity_gap {g : List Bool → List Bool} (hg : OneWay g)
    {imgLen : ℕ → ℕ} (himgLen : ∀ x, (g x).length = imgLen x.length)
    (r : ∀ k, Fin (k + 1))
    (hdense : ∀ k, 2 ^ k ≤ (k + 1) *
      (regularityBucket (fun x : BitString k => ofList (imgLen k) (g (List.ofFn x))) (r k)).card)
    (D : ℕ) :
    ∀ᶠ k : ℕ in atTop, (r k).val + D * Nat.log 2 k ≤ k := by
  have hneg :=
    (hg.inversion_negligible trivialInverter isPPT_trivialInverter).eventually_le_inv_polynomial
      (p := fun k => (k + 1) ^ (D + 1)) (by fun_prop) (fun k => by positivity)
  filter_upwards [hneg, eventually_ge_atTop 2] with k hk hk2
  have hcomb : ((2 : ℝ) ^ (r k).val) / ((k + 1 : ℝ) * (2 : ℝ) ^ k) ≤
      1 / ((k + 1 : ℝ) ^ (D + 1)) :=
    (trivialInverter_succ_ge himgLen k (r k) (hdense k)).trans (by exact_mod_cast hk)
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, pow_succ', mul_left_comm] at hcomb
  have hle : (2 : ℝ) ^ (r k).val * (k + 1 : ℝ) ^ D ≤ (2 : ℝ) ^ k :=
    le_of_mul_le_mul_left hcomb (by positivity)
  have hpow_nat : 2 ^ ((r k).val + D * Nat.log 2 k) ≤ 2 ^ k := by
    rw [pow_add]
    exact le_trans (Nat.mul_le_mul_left _
      ((two_pow_mul_log_le_pow D (by omega)).trans (Nat.pow_le_pow_left (by omega : k ≤ k + 1) D)))
      (by exact_mod_cast hle)
  exact (Nat.pow_le_pow_iff_right Nat.one_lt_two).mp hpow_nat

/-! ### Generator parameters and deterministic construction -/

/-- Binary encoding width $\lfloor \log_2 k \rfloor + 1$ for a regularity index
$r \in \{0, \dots, k\}$. -/
private def regWidth (k : ℕ) : ℕ := Nat.log 2 k + 1

/-- Every $r \le k$ fits in `regWidth k` binary bits: $r < 2^{\mathrm{regWidth}\; k}$. -/
private theorem lt_two_pow_regWidth {k r : ℕ} (hr : r ≤ k) : r < 2 ^ regWidth k := by
  rcases k.eq_zero_or_pos with rfl | hk
  · simp only [regWidth, Nat.log_zero_right, zero_add, pow_one]; omega
  · exact lt_of_le_of_lt hr (Nat.lt_pow_succ_log_self Nat.one_lt_two k)

/-- Maximum Goldreich–Levin output count allocated in the matrix $h_2$ at core parameter $k$. -/
private def mMax (d γ_core k : ℕ) : ℕ :=
  2 * (d * Nat.log 2 k) + γ_core * Nat.log 2 k + Nat.log 2 k + 1

/-- Total number of rows in the second universal hash matrix $h_2$ at core parameter $k$. -/
private def h2Rows (d γ_core k : ℕ) : ℕ := k + mMax d γ_core k

/-- Core seed length at OWF input length $k$:
$\mathrm{regWidth}(k) + k + k \cdot \mathrm{imgLen}(k) +
\mathrm{h2Rows}(d, \gamma_{\text{core}}, k) \cdot k$. -/
private def coreSeedLen (imgLen : ℕ → ℕ) (d γ_core k : ℕ) : ℕ :=
  regWidth k + k + k * imgLen k + h2Rows d γ_core k * k

/-- Actual Goldreich–Levin bit count extracted at core parameter $k$ and total seed length $n$. -/
private def mActual (d γ k n : ℕ) : ℕ :=
  2 * (d * Nat.log 2 k) + Nat.log 2 k + 1 + γ * Nat.log 2 n

/-- Number of LHL bits extracted from $x$ by $h_2$ for regularity index $r$. -/
private def l2Val (d k r : ℕ) : ℕ := min (r - d * Nat.log 2 k) (k - 2 * (d * Nat.log 2 k))

/-- Number of LHL bits extracted from $g(x)$ by $h_1$ for regularity index $r$. -/
private def l1Val (d k r : ℕ) : ℕ := (k - 2 * (d * Nat.log 2 k)) - l2Val d k r

/-- Length of the LHL prefix of the generator output before the `mActual` Goldreich–Levin bits. -/
private def lhlPrefixLen (d k n : ℕ) : ℕ := n - (2 * (d * Nat.log 2 k) + Nat.log 2 k + 1)

private theorem l1Val_add_l2Val (d k r : ℕ) :
    l1Val d k r + l2Val d k r = k - 2 * (d * Nat.log 2 k) := by unfold l1Val l2Val; omega
private theorem l1Val_le (d k r : ℕ) : l1Val d k r ≤ k := by unfold l1Val; omega
private theorem l2Val_le (d k r : ℕ) : l2Val d k r ≤ k := by unfold l2Val; omega
private theorem l2Val_eq_of_gap {d k r : ℕ} (hgap : r + d * Nat.log 2 k ≤ k) :
    l2Val d k r = r - d * Nat.log 2 k := by unfold l2Val; omega
private theorem l1Val_add_le_of_gap {d k r : ℕ} (hgap : r + d * Nat.log 2 k ≤ k) :
    l1Val d k r + d * Nat.log 2 k ≤ k - r := by
  have hsum := l1Val_add_l2Val d k r; have hl2 := l2Val_eq_of_gap hgap; omega
private theorem mActual_le_mMax {d γ γ_core k n : ℕ}
    (hlog : γ * Nat.log 2 n ≤ γ_core * Nat.log 2 k) :
    mActual d γ k n ≤ mMax d γ_core k := by unfold mActual mMax; omega
private theorem lhlPrefixLen_add_mActual {d γ k n : ℕ}
    (hle : 2 * (d * Nat.log 2 k) + Nat.log 2 k + 1 ≤ n) :
    lhlPrefixLen d k n + mActual d γ k n = n + γ * Nat.log 2 n := by
  unfold lhlPrefixLen mActual; omega
private theorem coreSeedLen_ge_succ (imgLen : ℕ → ℕ) (d γ_core k : ℕ) :
    k + 1 ≤ coreSeedLen imgLen d γ_core k := by unfold coreSeedLen regWidth; omega

@[local fun_prop]
private theorem computableInPolyTime_regWidth {α : Type} {encode : α ↪ List Bool}
    {k : α → ℕ} (hk : ComputableInPolyTime k encode encUnary) :
    ComputableInPolyTime (fun a => regWidth (k a)) encode encUnary := by unfold regWidth; fun_prop

@[local fun_prop]
private theorem computableInPolyTime_mMax {α : Type} {encode : α ↪ List Bool}
    (d γ_core : ℕ) {k : α → ℕ} (hk : ComputableInPolyTime k encode encUnary) :
    ComputableInPolyTime (fun a => mMax d γ_core (k a)) encode encUnary := by unfold mMax; fun_prop

@[local fun_prop]
private theorem computableInPolyTime_h2Rows {α : Type} {encode : α ↪ List Bool}
    (d γ_core : ℕ) {k : α → ℕ} (hk : ComputableInPolyTime k encode encUnary) :
    ComputableInPolyTime (fun a => h2Rows d γ_core (k a)) encode encUnary := by
  unfold h2Rows; fun_prop

@[local fun_prop]
private theorem computableInPolyTime_coreSeedLen {α : Type} {encode : α ↪ List Bool}
    {imgLen : ℕ → ℕ} (himgLen : ComputableInPolyTime imgLen encUnary encUnary)
    (d γ_core : ℕ) {k : α → ℕ} (hk : ComputableInPolyTime k encode encUnary) :
    ComputableInPolyTime (fun a => coreSeedLen imgLen d γ_core (k a)) encode encUnary := by
  unfold coreSeedLen; fun_prop

@[local fun_prop]
private theorem computableInPolyTime_mActual {α : Type} {encode : α ↪ List Bool}
    (d γ : ℕ) {k n : α → ℕ}
    (hk : ComputableInPolyTime k encode encUnary) (hn : ComputableInPolyTime n encode encUnary) :
    ComputableInPolyTime (fun a => mActual d γ (k a) (n a)) encode encUnary := by
  unfold mActual; fun_prop

@[local fun_prop]
private theorem computableInPolyTime_l2Val {α : Type} {encode : α ↪ List Bool}
    (d : ℕ) {k r : α → ℕ}
    (hk : ComputableInPolyTime k encode encUnary) (hr : ComputableInPolyTime r encode encUnary) :
    ComputableInPolyTime (fun a => l2Val d (k a) (r a)) encode encUnary := by unfold l2Val; fun_prop

@[local fun_prop]
private theorem computableInPolyTime_l1Val {α : Type} {encode : α ↪ List Bool}
    (d : ℕ) {k r : α → ℕ}
    (hk : ComputableInPolyTime k encode encUnary) (hr : ComputableInPolyTime r encode encUnary) :
    ComputableInPolyTime (fun a => l1Val d (k a) (r a)) encode encUnary := by unfold l1Val; fun_prop

/-- Unpadded output of the conditional entropy-preserving generator on seed `z`:
`pad ++ h1 ++ LinearHash.wordHash l1 h1 (g x) ++ h2 ++ LinearHash.wordHash (l2 + mActual) h2 x`. -/
private def rawGen (g : List Bool → List Bool) (imgLen : ℕ → ℕ) (d γ_core γ : ℕ)
    (z : List Bool) : List Bool :=
  let n := z.length
  let k := GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n
  let w := regWidth k
  let r := boundedBinaryValue k (z.take w)
  let l1 := l1Val d k r
  let l2 := l2Val d k r
  let x := (z.drop w).take k
  let h1 := (z.drop (w + k)).take (k * imgLen k)
  let h2 := (z.drop (w + k + k * imgLen k)).take (h2Rows d γ_core k * k)
  let pad := z.drop (coreSeedLen imgLen d γ_core k)
  pad ++ h1 ++ LinearHash.wordHash l1 h1 (g x) ++
    h2 ++ LinearHash.wordHash (l2 + mActual d γ k n) h2 x

/-- Full deterministic conditional entropy-preserving generator `G` ([Liu and Pass, Proof of
Theorem 5.5, §5.3, pp. 15–16 and Appendix A, pp. 21–23 of arXiv:2009.11514v1][LiuPass2020]),
normalized to output length `z.length + γ * Nat.log 2 z.length` on every input `z`. -/
private def fullGen (g : List Bool → List Bool) (imgLen : ℕ → ℕ) (d γ_core γ : ℕ)
    (z : List Bool) : List Bool :=
  let targetLen := z.length + γ * Nat.log 2 z.length
  (rawGen g imgLen d γ_core γ z ++ List.replicate targetLen false).take targetLen

@[simp]
private theorem length_fullGen (g : List Bool → List Bool) (imgLen : ℕ → ℕ) (d γ_core γ : ℕ)
    (z : List Bool) :
    (fullGen g imgLen d γ_core γ z).length = z.length + γ * Nat.log 2 z.length := by
  simp only [fullGen, List.length_take, List.length_append, List.length_replicate,
    min_eq_left (Nat.le_add_left _ _)]

/-- When `coreSeedLen k ≤ z.length` and `2 * (d * Nat.log 2 k) ≤ k`, `rawGen` already has length
`z.length + γ * Nat.log 2 z.length`, so `fullGen` equals `rawGen`. -/
private theorem fullGen_eq_rawGen {g : List Bool → List Bool} {imgLen : ℕ → ℕ} {d γ_core γ : ℕ}
    {z : List Bool}
    (hfits : coreSeedLen imgLen d γ_core
      (GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) z.length) ≤ z.length)
    (hk : 2 * (d * Nat.log 2
      (GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) z.length)) ≤
        GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) z.length) :
    fullGen g imgLen d γ_core γ z = rawGen g imgLen d γ_core γ z := by
  refine List.take_left' ?_
  have := l1Val_add_l2Val d
    (GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) z.length)
    (boundedBinaryValue (GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) z.length)
      (z.take (regWidth (GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) z.length))))
  simp only [rawGen, coreSeedLen, regWidth, mActual, List.length_append, List.length_drop,
    List.length_take, LinearHash.length_wordHash] at hfits this ⊢
  omega

@[local fun_prop]
private theorem computableInPolyTime_rawGen {g : List Bool → List Bool} {imgLen : ℕ → ℕ}
    (hg : ComputableInPolyTime g encBits encBits)
    (himgLen : ComputableInPolyTime imgLen encUnary encUnary)
    (d γ_core γ : ℕ) :
    ComputableInPolyTime (rawGen g imgLen d γ_core γ) encBits encBits := by
  have hk : ComputableInPolyTime
      (fun z : List Bool => GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) z.length)
      encBits encUnary :=
    GeneratorReindex.isPolyTime_parameter
      (computableInPolyTime_coreSeedLen himgLen d γ_core (.id' (encIn := encUnary)))
      .length_bits
  have hw := computableInPolyTime_regWidth hk
  have hid := ComputableInPolyTime.id' (encIn := encBits)
  have hr := ComputableInPolyTime.bitsBoundedBinaryValueWithInput hk
    (.bitsTakeWithInput hid hw)
  have hx := ComputableInPolyTime.bitsTakeWithInput (.bitsDropWithInput hid hw) hk
  have hh1Size := ComputableInPolyTime.unary_mul' hk (himgLen.comp hk)
  have hh1 := ComputableInPolyTime.bitsTakeWithInput
    (.bitsDropWithInput hid (.unary_add' hw hk)) hh1Size
  have hh2 := ComputableInPolyTime.bitsTakeWithInput
    (.bitsDropWithInput hid (.unary_add' (.unary_add' hw hk) hh1Size))
    (.unary_mul' (computableInPolyTime_h2Rows d γ_core hk) hk)
  have hpad := ComputableInPolyTime.bitsDropWithInput hid
    (computableInPolyTime_coreSeedLen himgLen d γ_core hk)
  have hd1 := LinearHash.computableInPolyTime_wordHash
    (computableInPolyTime_l1Val d hk hr) hh1 (hg.comp hx)
  have hd2 := LinearHash.computableInPolyTime_wordHash
    (.unary_add' (computableInPolyTime_l2Val d hk hr)
      (computableInPolyTime_mActual d γ hk .length_bits)) hh2 hx
  exact .bitsAppend (.bitsAppend (.bitsAppend (.bitsAppend hpad hh1) hd1) hh2) hd2

private theorem computableInPolyTime_fullGen {g : List Bool → List Bool} {imgLen : ℕ → ℕ}
    (hg : ComputableInPolyTime g encBits encBits)
    (himgLen : ComputableInPolyTime imgLen encUnary encUnary)
    (d γ_core γ : ℕ) :
    ComputableInPolyTime (fullGen g imgLen d γ_core γ) encBits encBits :=
  let hn := ComputableInPolyTime.length_bits
  let htarget := ComputableInPolyTime.unary_add' hn
    (.unary_mul' (.const γ) (ComputableInPolyTime.unary_log_two.comp hn))
  .bitsTakeWithInput (.bitsAppend (computableInPolyTime_rawGen hg himgLen d γ_core γ)
    ((ComputableInPolyTime.bitsReplicate false).comp htarget)) htarget

/-! ### Seed packing and conditioning events $E_n$ -/

/-- Mapping a nonempty finset along an embedding commutes with `PMF.uniformOfFinset`. -/
private theorem uniformOfFinset_map {α β : Type*} [Finite α]
    (s : Finset α) (hs : s.Nonempty) (e : α ↪ β) :
    PMF.uniformOfFinset (s.map e) (Finset.map_nonempty.mpr hs) =
      (PMF.uniformOfFinset s hs).map e := by
  classical
  let := Fintype.ofFinite α
  ext b
  rw [PMF.uniformOfFinset_apply, Finset.card_map]
  by_cases hb : b ∈ s.map e
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hb
    rw [ite_eq_left (Finset.mem_map_of_mem e ha), map_apply_of_injective _ e.injective,
      PMF.uniformOfFinset_apply, ite_eq_left ha]
  · rw [ite_eq_right hb, PMF.map_apply, tsum_fintype]
    exact (Finset.sum_eq_zero fun a _ => by
      by_cases ha : a ∈ s
      · exact ite_eq_right fun h : b = e a => hb (h ▸ Finset.mem_map_of_mem e ha)
      · simp only [PMF.uniformOfFinset_apply, ha, ↓reduceIte, ite_self]).symm

/-- Product of a nonempty finset with `Finset.univ` under `PMF.uniformOfFinset` factors into
independent sampling from `PMF.uniformOfFinset` and `PMF.uniformOfFintype`. -/
private theorem uniformOfFinset_product_univ {α β : Type*} [Fintype β] [Nonempty β]
    (s : Finset α) (hs : s.Nonempty) :
    PMF.uniformOfFinset (s ×ˢ (Finset.univ : Finset β)) (hs.product Finset.univ_nonempty) =
      (PMF.uniformOfFinset s hs).bind fun a =>
        (PMF.uniformOfFintype β).map fun b => (a, b) := by
  classical
  ext ⟨a, b⟩
  rw [bind_map_prodMk_apply]
  by_cases ha : a ∈ s
  · simp only [PMF.uniformOfFinset_apply, PMF.uniformOfFintype_apply, Finset.mem_product,
      Finset.mem_univ, and_true, ha, ↓reduceIte, Finset.card_product, Finset.card_univ,
      Nat.cast_mul, ENNReal.mul_inv (Or.inl (Nat.cast_ne_zero.mpr hs.card_pos.ne'))
        (Or.inl (ENNReal.natCast_ne_top _))]
  · simp only [PMF.uniformOfFinset_apply, Finset.mem_product, ha, false_and, ↓reduceIte,
      zero_mul]

/-- Uniform components `(h1, h2, pad)` of a seed at core parameter `k` and seed length `n`. -/
private abbrev RestTuple (imgLen : ℕ → ℕ) (d γ_core k n : ℕ) : Type :=
  BitString (k * imgLen k) × BitString (h2Rows d γ_core k * k) ×
    BitString (n - coreSeedLen imgLen d γ_core k)

/-- Structured seed tuple `(x, h1, h2, pad)` at core parameter `k` and seed length `n`. -/
private abbrev SeedTuple (imgLen : ℕ → ℕ) (d γ_core k n : ℕ) : Type :=
  BitString k × RestTuple imgLen d γ_core k n

/-- Concatenate the regularity header `binaryWord (regWidth k) r` with `x, h1, h2, pad`. -/
private def packSeedWords {imgLen : ℕ → ℕ} {d γ_core k n : ℕ} (r : ℕ)
    (t : SeedTuple imgLen d γ_core k n) : List Bool :=
  binaryWord (regWidth k) r ++ List.ofFn t.1 ++ List.ofFn t.2.1 ++
    List.ofFn t.2.2.1 ++ List.ofFn t.2.2.2

private theorem length_packSeedWords {imgLen : ℕ → ℕ} {d γ_core k n r : ℕ}
    (hr : r ≤ k) (hfits : coreSeedLen imgLen d γ_core k ≤ n)
    (t : SeedTuple imgLen d γ_core k n) :
    (packSeedWords r t).length = n := by
  have hrw : (binaryWord (regWidth k) r).length = regWidth k :=
    length_binaryWord (lt_two_pow_regWidth hr)
  have hcs : coreSeedLen imgLen d γ_core k =
      regWidth k + k + k * imgLen k + h2Rows d γ_core k * k := rfl
  simp only [packSeedWords, List.length_append, List.length_ofFn, hrw]
  omega

private theorem packSeedWords_injective {imgLen : ℕ → ℕ} {d γ_core k n r : ℕ} :
    Function.Injective (packSeedWords (imgLen := imgLen) (d := d) (γ_core := γ_core)
      (k := k) (n := n) r) := by
  rintro ⟨x, h1, h2, pad⟩ ⟨x', h1', h2', pad'⟩ h
  dsimp only [packSeedWords] at h
  have h4 := List.append_inj h (by simp only [List.length_append, List.length_ofFn])
  have h3 := List.append_inj h4.1 (by simp only [List.length_append, List.length_ofFn])
  have h2_eq := List.append_inj h3.1 (by simp only [List.length_append, List.length_ofFn])
  have h1_eq := List.append_inj h2_eq.1 rfl
  simp only [List.ofFn_inj] at h1_eq h2_eq h3 h4
  exact Prod.ext h1_eq.2 (Prod.ext h2_eq.2 (Prod.ext h3.2 h4.2))

/-- Embedding of `SeedTuple imgLen d γ_core k n` into `BitString n`. -/
private def packSeedEmb {imgLen : ℕ → ℕ} {d γ_core k n r : ℕ}
    (hr : r ≤ k) (hfits : coreSeedLen imgLen d γ_core k ≤ n) :
    SeedTuple imgLen d γ_core k n ↪ BitString n :=
  ⟨fun t => ofList n (packSeedWords r t), fun t t' h => by
    have h1 := congrArg List.ofFn h
    rw [ofFn_ofList (length_packSeedWords hr hfits t),
      ofFn_ofList (length_packSeedWords hr hfits t')] at h1
    exact packSeedWords_injective h1⟩

@[simp]
private theorem ofFn_packSeedEmb {imgLen : ℕ → ℕ} {d γ_core k n r : ℕ}
    (hr : r ≤ k) (hfits : coreSeedLen imgLen d γ_core k ≤ n)
    (t : SeedTuple imgLen d γ_core k n) :
    List.ofFn (packSeedEmb hr hfits t) = packSeedWords r t :=
  -- Unfold the embedding first: unifying it with `ofList` directly takes seconds.
  (congrArg List.ofFn (congrFun (Function.Embedding.coeFn_mk _ _) t)).trans
    (ofFn_ofList (length_packSeedWords hr hfits t))

/-- Evaluating `fullGen` on a packed seed (when `coreSeedLen k ≤ n` and `2 * (d * log₂ k) ≤ k`)
recovers the exact concatenation of `pad`, `h1`, `wordHash l1 h1 (g x)`, `h2`, and
`wordHash (l2 + mActual) h2 x`. -/
private theorem fullGen_packSeedWords (g : List Bool → List Bool) (imgLen : ℕ → ℕ)
    (d γ_core γ n r : ℕ)
    (hr : r ≤ GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n)
    (hfits : coreSeedLen imgLen d γ_core
      (GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n) ≤ n)
    (hk_2d : 2 * (d * Nat.log 2
      (GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n)) ≤
        GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n)
    (t : SeedTuple imgLen d γ_core
      (GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n) n) :
    let k := GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n
    fullGen g imgLen d γ_core γ (packSeedWords r t) =
      List.ofFn t.2.2.2 ++ List.ofFn t.2.1 ++
        LinearHash.wordHash (l1Val d k r) (List.ofFn t.2.1) (g (List.ofFn t.1)) ++
        List.ofFn t.2.2.1 ++
        LinearHash.wordHash (l2Val d k r + mActual d γ k n)
          (List.ofFn t.2.2.1) (List.ofFn t.1) := by
  intro k
  have hu0 : (binaryWord (regWidth k) r).length = regWidth k :=
    length_binaryWord (lt_two_pow_regWidth hr)
  have hlen : (packSeedWords r t).length = n := length_packSeedWords hr hfits t
  have hpack : packSeedWords r t = binaryWord (regWidth k) r ++
      (List.ofFn t.1 ++ (List.ofFn t.2.1 ++ (List.ofFn t.2.2.1 ++ List.ofFn t.2.2.2))) := by
    simp only [packSeedWords, k, List.append_assoc]
  have hdrop0 : (packSeedWords r t).drop (regWidth k) =
      List.ofFn t.1 ++ (List.ofFn t.2.1 ++ (List.ofFn t.2.2.1 ++ List.ofFn t.2.2.2)) := by
    rw [hpack, List.drop_left' hu0]
  have hdrop1 : (packSeedWords r t).drop (regWidth k + k) =
      List.ofFn t.2.1 ++ (List.ofFn t.2.2.1 ++ List.ofFn t.2.2.2) := by
    rw [← List.drop_drop, hdrop0, List.drop_left' List.length_ofFn]
  have hdrop2 : (packSeedWords r t).drop (regWidth k + k + k * imgLen k) =
      List.ofFn t.2.2.1 ++ List.ofFn t.2.2.2 := by
    rw [← List.drop_drop, hdrop1, List.drop_left' List.length_ofFn]
  have hdrop3 : (packSeedWords r t).drop (coreSeedLen imgLen d γ_core k) = List.ofFn t.2.2.2 := by
    change (packSeedWords r t).drop (regWidth k + k + k * imgLen k + h2Rows d γ_core k * k) = _
    rw [← List.drop_drop, hdrop2, List.drop_left' List.length_ofFn]
  rw [fullGen_eq_rawGen (by rwa [hlen]) (by rwa [hlen])]
  unfold rawGen; dsimp only
  rw [hlen, show (packSeedWords r t).take (regWidth k) = binaryWord (regWidth k) r by
      rw [hpack, List.take_left' hu0],
    boundedBinaryValue_eq, binaryValue_binaryWord, Nat.min_eq_right hr,
    hdrop0, hdrop1, hdrop2, hdrop3,
    List.take_left' (List.length_ofFn (f := t.1)),
    List.take_left' (List.length_ofFn (f := t.2.1)),
    List.take_left' (List.length_ofFn (f := t.2.2.1))]

/-- Conditioning event $E_n \subseteq \mathrm{BitString}\; n$ at seed length $n$
([Liu and Pass, Proof of Theorem 5.5, §5.3, pp. 15–16 of arXiv:2009.11514v1][LiuPass2020]). -/
private noncomputable def condSeedSet (imgLen : ℕ → ℕ) (d γ_core : ℕ)
    (S : ∀ k, Finset (BitString k)) (r : ∀ k, Fin (k + 1)) (n : ℕ) :
    Finset (BitString n) := by
  classical
  let k := GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n
  exact if hfits : coreSeedLen imgLen d γ_core k ≤ n then
    (S k ×ˢ (Finset.univ : Finset (RestTuple imgLen d γ_core k n))).map
      (packSeedEmb (Nat.le_of_lt_succ (r k).isLt) hfits)
  else Finset.univ

private theorem condSeedSet_nonempty (imgLen : ℕ → ℕ) (d γ_core : ℕ)
    (S : ∀ k, Finset (BitString k)) (hS : ∀ k, (S k).Nonempty)
    (r : ∀ k, Fin (k + 1)) (n : ℕ) :
    (condSeedSet imgLen d γ_core S r n).Nonempty := by
  unfold condSeedSet
  dsimp only
  split_ifs
  · exact Finset.map_nonempty.mpr ((hS _).product Finset.univ_nonempty)
  · exact Finset.univ_nonempty

/-- When `coreSeedLen k ≤ n` and `S k = S'`, sampling uniformly from `condSeedSet ... n` and
converting to `List Bool` is identical to sampling `x ← uniformOfFinset S'` and independent uniform
`h1, h2, pad` and applying `packSeedWords (r k).val`. -/
private theorem uniformOfFinset_condSeedSet_map_ofFn (imgLen : ℕ → ℕ) (d γ_core : ℕ)
    (S : ∀ k, Finset (BitString k)) (hS : ∀ k, (S k).Nonempty)
    (r : ∀ k, Fin (k + 1)) {n k : ℕ}
    (hk : k = GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n)
    (hfits : coreSeedLen imgLen d γ_core k ≤ n)
    {S' : Finset (BitString k)} (hS' : S'.Nonempty) (hS_eq : S k = S') :
    (PMF.uniformOfFinset (condSeedSet imgLen d γ_core S r n)
      (condSeedSet_nonempty imgLen d γ_core S hS r n)).map List.ofFn =
      (PMF.uniformOfFinset S' hS').bind fun x =>
        (PMF.uniformOfFintype (BitString (k * imgLen k))).bind fun h1 =>
          (PMF.uniformOfFintype (BitString (h2Rows d γ_core k * k))).bind fun h2 =>
            (PMF.uniformOfFintype (BitString (n - coreSeedLen imgLen d γ_core k))).map fun pad =>
              packSeedWords (r k).val (x, h1, h2, pad) := by
  classical
  subst hS_eq hk
  rw [show PMF.uniformOfFinset (condSeedSet imgLen d γ_core S r n) _ =
      (PMF.uniformOfFinset (S _ ×ˢ (Finset.univ : Finset (RestTuple imgLen d γ_core _ n)))
        ((hS _).product Finset.univ_nonempty)).map
          (packSeedEmb (Nat.le_of_lt_succ (r _).isLt) hfits) by
      rw [← uniformOfFinset_map]; congr 1; unfold condSeedSet; exact dite_eq_left hfits,
    PMF.map_comp, uniformOfFinset_product_univ (hs := hS _)]
  simp only [pmf_norm, RestTuple, ← PMF.uniformOfFintype_prod, ofFn_packSeedEmb]

/-! ### Leftover hash statistical distance and conditional entropy preservation -/

/-- Any initial row prefix of a flat uniform Boolean matrix is two-universal. -/
private theorem isTwoUniversal_block_prefix {n m count : ℕ} (h : m ≤ count) :
    IsTwoUniversal (PMF.uniformOfFintype (BitString (count * n)))
      (fun matrix => LinearHash.hash (block matrix ∘ Fin.castLE h)) := by
  refine IsUniversalHash.precompose_seed _ (blocksEquiv (m := count) (k := n))
    (hash := fun rows => LinearHash.hash (rows ∘ Fin.castLE h)) ?_
  rw [uniformOfFintype_map_equiv]
  exact LinearHash.isTwoUniversal_prefix h

/-- Conditional leftover hash bound on the preimage fibers of a regularity bucket $S_{k, r}$:
replacing `hash2 h2 x` (where $x \leftarrow S_{k, r}$ is resampled from the fiber of $x_0$) with
an independent uniform $m_2$-bit string changes the joint distribution with $(x_0, h_2)$ by at most
`if m2 = 0 then 0 else Real.sqrt ((2 : ℝ) ^ m2 / (2 : ℝ) ^ r.val) / 2`. -/
private theorem dist_seededHash_regularityBucket_fiber_le {k m2 c2 : ℕ} {Image : Type*}
    [DecidableEq Image] (f : BitString k → Image) (r : Fin (k + 1))
    (hS : (regularityBucket f r).Nonempty) (hm2 : m2 ≤ c2) :
    haveI (x₀ : BitString k) : Nonempty {x : BitString k // f x = f x₀} := ⟨⟨x₀, rfl⟩⟩
    let side := PMF.uniformOfFinset (regularityBucket f r) hS
    let source (x₀ : BitString k) :=
      (PMF.uniformOfFintype {x : BitString k // f x = f x₀}).map Subtype.val
    let seed2 := PMF.uniformOfFintype (BitString (c2 * k))
    let hash2 (h2 : BitString (c2 * k)) (x : BitString k) : BitString m2 :=
      LinearHash.hash (block h2 ∘ Fin.castLE hm2) x
    dist (side.bind fun x₀ => (seededHash seed2 (source x₀) hash2).map (x₀, ·))
      (side.bind fun x₀ =>
        (seed2.bind fun h2 => (PMF.uniformOfFintype (BitString m2)).map (h2, ·)).map (x₀, ·)) ≤
      if m2 = 0 then 0 else Real.sqrt ((2 : ℝ) ^ m2 / (2 : ℝ) ^ r.val) / 2 := by
  have (x₀ : BitString k) : Nonempty {x : BitString k // f x = f x₀} := ⟨⟨x₀, rfl⟩⟩
  intro side source seed2 hash2
  split_ifs with hm2_zero
  · subst m2
    have : Subsingleton (BitString 0) := ⟨fun _ _ => funext fun i => i.elim0⟩
    simp only [seededHash_eq_uniform_of_subsingleton, dist_self, le_rfl]
  · refine ((isTwoUniversal_block_prefix hm2).leftover_hash_conditional side source).trans
      (div_le_div_of_nonneg_right (Real.sqrt_le_sqrt ?_) (by norm_num))
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat,
      div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_left ((Finset.sum_le_sum fun x₀ _ => ?_).trans_eq
      (by rw [← Finset.sum_mul, PMF.sum_toReal side, one_mul])) (by positivity)
    by_cases hx₀ : x₀ ∈ regularityBucket f r
    · refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
      rw [collisionProbability_map_of_injective _ _ Subtype.val_injective,
        collisionProbability_uniform, ← Nat.card_eq_fintype_card, inv_eq_one_div, inv_eq_one_div]
      exact one_div_le_one_div_of_le (by positivity)
        (by exact_mod_cast (card_fiber_of_mem_regularityBucket f r hx₀).1)
    · simp [side, PMF.uniformOfFinset_apply, hx₀]

/-- Taking the first `a ≤ count` bits of `LinearHash.wordHash count` gives
`LinearHash.wordHash a`. -/
private theorem wordHash_take {a count : ℕ} (h : a ≤ count) (seed input : List Bool) :
    (LinearHash.wordHash count seed input).take a = LinearHash.wordHash a seed input := by
  simp only [LinearHash.wordHash, listRows, ← List.map_take, List.take_range,
    Nat.min_eq_left h]

/-- On `BitString` inputs, `LinearHash.wordHash m` with `m ≤ count` agrees with
`LinearHash.hash` on the first `m` block rows of the seed matrix. -/
private theorem wordHash_ofFn_prefix {k m count : ℕ} (hm : m ≤ count)
    (matrix : BitString (count * k)) (x : BitString k) :
    LinearHash.wordHash m (List.ofFn matrix) (List.ofFn x) =
      List.ofFn (LinearHash.hash (block matrix ∘ Fin.castLE hm) x) := by
  rw [LinearHash.wordHash_eq_ofFn, block_ofList_prefix hm, ofList_ofFn]

private theorem l2Val_le_h2Rows (d γ_core k r : ℕ) :
    l2Val d k r ≤ h2Rows d γ_core k :=
  (l2Val_le d k r).trans (Nat.le_add_right k _)

private theorem lhlPrefixLen_le_output (d γ k n : ℕ) :
    lhlPrefixLen d k n ≤ n + γ * Nat.log 2 n := by unfold lhlPrefixLen; omega

private theorem lhlPrefixLen_split (imgLen : ℕ → ℕ) (d γ_core : ℕ) {k n : ℕ} (r : ℕ)
    (hfits : coreSeedLen imgLen d γ_core k ≤ n)
    (hk : 2 * (d * Nat.log 2 k) ≤ k) :
    (n - coreSeedLen imgLen d γ_core k) + k * imgLen k + l1Val d k r +
      h2Rows d γ_core k * k + l2Val d k r = lhlPrefixLen d k n := by
  have hl12 := l1Val_add_l2Val d k r
  have hcs : coreSeedLen imgLen d γ_core k =
      (Nat.log 2 k + 1) + k + k * imgLen k + h2Rows d γ_core k * k := rfl
  unfold lhlPrefixLen
  omega

/-- Core leftover-hash tuple distribution at input length `k` on regularity bucket $S_{k, r}$:
samples $x \leftarrow S_{k, r}$, $h_1$, $h_2$ uniformly and outputs
$((h_1, \mathrm{hash}_1(h_1, f(x))), (h_2, \mathrm{hash}_2(h_2, x)))$. -/
private noncomputable def coreLHLDist {k imgLen_k m1 m2 c2 : ℕ}
    (f : BitString k → BitString imgLen_k) (r : Fin (k + 1))
    (hS : (regularityBucket f r).Nonempty) (hm1 : m1 ≤ k) (hm2 : m2 ≤ c2) :
    PMF ((BitString (k * imgLen_k) × BitString m1) × (BitString (c2 * k) × BitString m2)) := do
  let x ← PMF.uniformOfFinset (regularityBucket f r) hS
  let h1 ← PMF.uniformOfFintype (BitString (k * imgLen_k))
  (PMF.uniformOfFintype (BitString (c2 * k))).map fun h2 =>
    ((h1, LinearHash.hash (block h1 ∘ Fin.castLE hm1) (f x)),
      (h2, LinearHash.hash (block h2 ∘ Fin.castLE hm2) x))

/-- Ideal uniform core tuple distribution matching `coreLHLDist`. -/
private noncomputable def unifCoreDist (k imgLen_k m1 m2 c2 : ℕ) :
    PMF ((BitString (k * imgLen_k) × BitString m1) × (BitString (c2 * k) × BitString m2)) := do
  let p1 ← do
    let h1 ← PMF.uniformOfFintype (BitString (k * imgLen_k))
    (PMF.uniformOfFintype (BitString m1)).map (h1, ·)
  let h2 ← PMF.uniformOfFintype (BitString (c2 * k))
  (PMF.uniformOfFintype (BitString m2)).map fun d2 => (p1, (h2, d2))

/-- Statistical distance between `coreLHLDist` and `unifCoreDist` is bounded by the sum of the
fiber leftover-hash error on $x$ and the image leftover-hash error on $f(x)$
([Liu and Pass, Lemma 5.1, §5.3, p. 14 and Appendix A, pp. 22–23 of
arXiv:2009.11514v1][LiuPass2020]). -/
private theorem dist_coreLHLDist_unifCoreDist_le {k imgLen_k m1 m2 c2 : ℕ}
    (f : BitString k → BitString imgLen_k) (r : Fin (k + 1))
    (hS : (regularityBucket f r).Nonempty)
    (hdense : 2 ^ k ≤ (k + 1) * (regularityBucket f r).card)
    (hm1 : m1 ≤ k) (hm2 : m2 ≤ c2) :
    dist (coreLHLDist f r hS hm1 hm2) (unifCoreDist k imgLen_k m1 m2 c2) ≤
      (if m2 = 0 then 0 else Real.sqrt ((2 : ℝ) ^ m2 / (2 : ℝ) ^ r.val) / 2) +
        Real.sqrt ((2 : ℝ) ^ m1 * ((2 * (k + 1 : ℝ) * (2 : ℝ) ^ r.val) / (2 : ℝ) ^ k)) / 2 := by
  have (x₀ : BitString k) : Nonempty {x : BitString k // f x = f x₀} := ⟨⟨x₀, rfl⟩⟩
  let side := PMF.uniformOfFinset (regularityBucket f r) hS
  let seed1 := PMF.uniformOfFintype (BitString (k * imgLen_k))
  let seed2 := PMF.uniformOfFintype (BitString (c2 * k))
  let unif2 := seed2.bind fun h2 => (PMF.uniformOfFintype (BitString m2)).map (h2, ·)
  let stepF (xhd2 : BitString k × (BitString (c2 * k) × BitString m2)) :=
    seed1.map fun h1 => ((h1, LinearHash.hash (block h1 ∘ Fin.castLE hm1) (f xhd2.1)), xhd2.2)
  let midCore := (side.bind fun x₀ => unif2.map (x₀, ·)).bind stepF
  refine (dist_triangle _ midCore _).trans (add_le_add ?_ ?_)
  · rw [show coreLHLDist f r hS hm1 hm2 =
        (side.bind fun x₀ => (seededHash seed2
          ((PMF.uniformOfFintype {x : BitString k // f x = f x₀}).map Subtype.val)
          (fun h2 x => LinearHash.hash (block h2 ∘ Fin.castLE hm2) x)).map (x₀, ·)).bind stepF by
      conv_lhs => unfold coreLHLDist; rw [← bind_regularityBucket_fiber_eq f r hS]
      simp only [pmf_norm, side, seededHash, stepF]
      congr 1; funext x₀; pmf_swap with h2 x h1; simp only [x.property]]
    exact (PMF.dist_bind_le _ _ stepF).trans (dist_seededHash_regularityBucket_fiber_le f r hS hm2)
  · rw [show midCore = (seededHash seed1 (side.map f)
          (fun h1 y => LinearHash.hash (block h1 ∘ Fin.castLE hm1) y)).bind fun p1 =>
            unif2.map (p1, ·) by simp only [pmf_norm, midCore, stepF, seededHash]; pmf_swap,
      show unifCoreDist k imgLen_k m1 m2 c2 =
          (seed1.bind fun h1 => (PMF.uniformOfFintype (BitString m1)).map (h1, ·)).bind fun p1 =>
            unif2.map (p1, ·) by simp only [unifCoreDist, seed1, seed2, unif2, pmf_norm]]
    refine (PMF.dist_bind_le _ _ _).trans ?_
    simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow,
      Nat.cast_ofNat] using (isTwoUniversal_block_prefix hm1).leftover_hash_of_mass_le
        (side.map f) (mass_map_regularityBucket_le f r hS hdense)

private theorem sqrt_l2Val_fiber_le {d k r : ℕ} {D c : ℝ} (hc : 0 ≤ c)
    (hgap : r + d * Nat.log 2 k ≤ k) (hD : (2 : ℝ) ^ r ≤ D) :
    (if l2Val d k r = 0 then 0 else c * Real.sqrt ((2 : ℝ) ^ (l2Val d k r) / D)) ≤
      c * Real.sqrt (1 / (2 : ℝ) ^ (d * Nat.log 2 k)) := by
  split_ifs with hm2
  · positivity
  · have hl2 := l2Val_eq_of_gap hgap
    have hpow : (2 : ℝ) ^ r = (2 : ℝ) ^ (l2Val d k r) * (2 : ℝ) ^ (d * Nat.log 2 k) := by
      rw [← pow_add]; congr 1; omega
    refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hc
    exact (div_le_div_of_nonneg_left (by positivity) (by positivity) hD).trans_eq
      (by rw [hpow, div_mul_eq_div_div, div_self (by positivity)])

/-- Under the regularity gap `r.val + d * Nat.log 2 k ≤ k`, the statistical distance between
`coreLHLDist` (with $m_1 = \mathrm{l1Val}\; d\; k\; r$ and $m_2 = \mathrm{l2Val}\; d\; k\; r$)
and `unifCoreDist` is at most $\sqrt{2 (k + 1) / 2^{d \lfloor \log_2 k \rfloor}}$. -/
private theorem dist_coreLHLDist_unifCoreDist_le_of_gap {k imgLen_k d γ_core : ℕ}
    (f : BitString k → BitString imgLen_k) (r : Fin (k + 1))
    (hS : (regularityBucket f r).Nonempty)
    (hdense : 2 ^ k ≤ (k + 1) * (regularityBucket f r).card)
    (hgap : r.val + d * Nat.log 2 k ≤ k) :
    dist (coreLHLDist f r hS (l1Val_le d k r.val) (l2Val_le_h2Rows d γ_core k r.val))
      (unifCoreDist k imgLen_k (l1Val d k r.val) (l2Val d k r.val) (h2Rows d γ_core k)) ≤
      Real.sqrt (2 * (k + 1 : ℝ) / (2 : ℝ) ^ (d * Nat.log 2 k)) := by
  have hbase := dist_coreLHLDist_unifCoreDist_le f r hS hdense (l1Val_le d k r.val)
    (l2Val_le_h2Rows d γ_core k r.val)
  have hterm1 :
      (if l2Val d k r.val = 0 then 0
        else Real.sqrt ((2 : ℝ) ^ (l2Val d k r.val) / (2 : ℝ) ^ r.val) / 2) ≤
        Real.sqrt (2 * (k + 1 : ℝ) / (2 : ℝ) ^ (d * Nat.log 2 k)) / 2 := by
    have h := sqrt_l2Val_fiber_le (c := 1 / 2) (by norm_num) hgap (le_rfl (a := (2 : ℝ) ^ r.val))
    have hmono : Real.sqrt (1 / (2 : ℝ) ^ (d * Nat.log 2 k)) ≤
        Real.sqrt (2 * (k + 1 : ℝ) / (2 : ℝ) ^ (d * Nat.log 2 k)) :=
      Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (by linarith) (by positivity))
    split_ifs at h ⊢ <;> linarith
  have hterm2 :
      Real.sqrt ((2 : ℝ) ^ (l1Val d k r.val) *
        ((2 * (k + 1 : ℝ) * (2 : ℝ) ^ r.val) / (2 : ℝ) ^ k)) / 2 ≤
        Real.sqrt (2 * (k + 1 : ℝ) / (2 : ℝ) ^ (d * Nat.log 2 k)) / 2 := by
    have hl1_le : l1Val d k r.val + r.val + d * Nat.log 2 k ≤ k := by
      have := l1Val_add_le_of_gap hgap; omega
    have hpow : (2 : ℝ) ^ (l1Val d k r.val) * (2 : ℝ) ^ r.val * (2 : ℝ) ^ (d * Nat.log 2 k) ≤
        (2 : ℝ) ^ k := by
      simpa only [pow_add] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hl1_le
    refine div_le_div_of_nonneg_right (Real.sqrt_le_sqrt ?_) (by norm_num)
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [show (0 : ℝ) ≤ 2 * (k + 1 : ℝ) by positivity]
  linarith [hbase, hterm1, hterm2]

private theorem bind_uniformOfFintype_append (a b : ℕ) :
    ((uniformList a).bind fun u =>
      (PMF.uniformOfFintype (BitString b)).map fun v => u ++ List.ofFn v) =
      uniformList (a + b) := by
  rw [uniformList_add]
  simp only [uniformList, PMF.bind_map, PMF.map_comp, Function.comp_def]

private theorem uniformOfFintype_five_append (n0 n1 n2 n3 n4 : ℕ) :
    ((PMF.uniformOfFintype (BitString n0)).bind fun u0 =>
      (PMF.uniformOfFintype (BitString n1)).bind fun u1 =>
        (PMF.uniformOfFintype (BitString n2)).bind fun u2 =>
          (PMF.uniformOfFintype (BitString n3)).bind fun u3 =>
            (PMF.uniformOfFintype (BitString n4)).map fun u4 =>
              List.ofFn u0 ++ List.ofFn u1 ++ List.ofFn u2 ++ List.ofFn u3 ++ List.ofFn u4) =
      uniformList (n0 + n1 + n2 + n3 + n4) := by
  have h0 : (PMF.uniformOfFintype (BitString n0)).map List.ofFn = uniformList n0 := rfl
  rw [← bind_uniformOfFintype_append, ← bind_uniformOfFintype_append,
    ← bind_uniformOfFintype_append, ← bind_uniformOfFintype_append, ← h0]
  simp only [pmf_norm]

private theorem unifCoreDist_bind_pad_append (k imgLen_k m1 m2 c2 padLen : ℕ) :
    ((unifCoreDist k imgLen_k m1 m2 c2).bind fun c =>
      (PMF.uniformOfFintype (BitString padLen)).map fun pad =>
        List.ofFn pad ++ List.ofFn c.1.1 ++ List.ofFn c.1.2 ++
          List.ofFn c.2.1 ++ List.ofFn c.2.2) =
      uniformList (padLen + k * imgLen_k + m1 + c2 * k + m2) := by
  rw [← uniformOfFintype_five_append]
  simp only [pmf_norm, unifCoreDist]
  pmf_swap

private theorem entropy_fullGen_condSeedSet_ge (g : List Bool → List Bool) (imgLen : ℕ → ℕ)
    (d γ_core γ : ℕ) (S : ∀ k, Finset (BitString k)) (hS : ∀ k, (S k).Nonempty)
    (r : ∀ k, Fin (k + 1)) {n k : ℕ}
    (hk : k = GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n)
    (hfits : coreSeedLen imgLen d γ_core k ≤ n)
    (hk_2d : 2 * (d * Nat.log 2 k) ≤ k)
    (hg_len : ∀ x : BitString k, (g (List.ofFn x)).length = imgLen k)
    (hS_eq : S k = regularityBucket
      (fun x : BitString k => ofList (imgLen k) (g (List.ofFn x))) (r k))
    (hdist : dist
      (coreLHLDist (fun x : BitString k => ofList (imgLen k) (g (List.ofFn x))) (r k)
        (hS_eq ▸ hS k) (l1Val_le d k (r k).val) (l2Val_le_h2Rows d γ_core k (r k).val))
      (unifCoreDist k (imgLen k) (l1Val d k (r k).val) (l2Val d k (r k).val)
        (h2Rows d γ_core k)) ≤ 1 / (lhlPrefixLen d k n : ℝ) ^ 2) :
    ((lhlPrefixLen d k n : ℝ) - 2) ≤
      PMF.entropy ((PMF.uniformOfFinset (condSeedSet imgLen d γ_core S r n)
        (condSeedSet_nonempty imgLen d γ_core S hS r n)).map fun x =>
          ofList (n + γ * Nat.log 2 n) (fullGen g imgLen d γ_core γ (List.ofFn x))) := by
  subst hk
  set k := GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n
  let f (x : BitString k) : BitString (imgLen k) := ofList (imgLen k) (g (List.ofFn x))
  have hS_reg : (regularityBucket f (r k)).Nonempty := hS_eq ▸ hS k
  let m_lhl := lhlPrefixLen d k n
  let padLen := n - coreSeedLen imgLen d γ_core k
  let m1 := l1Val d k (r k).val
  let m2 := l2Val d k (r k).val
  let c2 := h2Rows d γ_core k
  let D_lhl := ((PMF.uniformOfFinset (condSeedSet imgLen d γ_core S r n)
    (condSeedSet_nonempty imgLen d γ_core S hS r n)).map List.ofFn).map fun z =>
      ofList m_lhl ((fullGen g imgLen d γ_core γ z).take m_lhl)
  let packLHL
      (c : (BitString (k * imgLen k) × BitString m1) × (BitString (c2 * k) × BitString m2)) :=
    (PMF.uniformOfFintype (BitString padLen)).map fun pad =>
      ofList m_lhl (List.ofFn pad ++ List.ofFn c.1.1 ++ List.ofFn c.1.2 ++
        List.ofFn c.2.1 ++ List.ofFn c.2.2)
  have hlen := lhlPrefixLen_split imgLen d γ_core (r k).val hfits hk_2d
  have hreal_lhl : D_lhl = (coreLHLDist f (r k) hS_reg (l1Val_le d k (r k).val)
      (l2Val_le_h2Rows d γ_core k (r k).val)).bind packLHL := by
    dsimp only [D_lhl, coreLHLDist, packLHL]
    rw [uniformOfFinset_condSeedSet_map_ofFn imgLen d γ_core S hS r rfl hfits hS_reg hS_eq]
    simp only [pmf_norm]
    congr 1
    funext x
    congr 1
    funext h1
    congr 1
    funext h2
    congr 1
    funext pad
    congr 1
    rw [fullGen_packSeedWords g imgLen d γ_core γ n (r k).val
      (Nat.le_of_lt_succ (r k).isLt) hfits hk_2d (x, h1, h2, pad)]
    set u := List.ofFn pad ++ List.ofFn h1 ++
      LinearHash.wordHash m1 (List.ofFn h1) (g (List.ofFn x)) ++ List.ofFn h2
    have hu : m_lhl = u.length + m2 := by
      simp only [u, List.length_append, List.length_ofFn, LinearHash.length_wordHash]
      exact hlen.symm
    rw [hu, List.take_append, List.take_of_length_le (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left, wordHash_take (Nat.le_add_right m2 _),
      wordHash_ofFn_prefix (l2Val_le_h2Rows d γ_core k (r k).val)]
    dsimp only [u]
    rw [show g (List.ofFn x) = List.ofFn (f x) from (ofFn_ofList (hg_len x)).symm,
      wordHash_ofFn_prefix (l1Val_le d k (r k).val)]
    rfl
  have hunif_lhl : (unifCoreDist k (imgLen k) m1 m2 c2).bind packLHL =
      PMF.uniformOfFintype (BitString m_lhl) := by
    have h : (unifCoreDist k (imgLen k) m1 m2 c2).bind packLHL =
        ((unifCoreDist k (imgLen k) m1 m2 c2).bind fun c =>
          (PMF.uniformOfFintype (BitString padLen)).map fun pad =>
            List.ofFn pad ++ List.ofFn c.1.1 ++ List.ofFn c.1.2 ++
              List.ofFn c.2.1 ++ List.ofFn c.2.2).map (ofList m_lhl) := by
      simp only [packLHL, pmf_norm]
    rw [h, unifCoreDist_bind_pad_append, hlen, Cslib.BitString.uniformList_ofList]
  refine (entropy_ge_of_dist_uniform_le D_lhl (by
    rw [hreal_lhl, ← hunif_lhl]; exact (PMF.dist_bind_le _ _ packLHL).trans hdist)).trans ?_
  rw [show D_lhl = ((PMF.uniformOfFinset (condSeedSet imgLen d γ_core S r n)
      (condSeedSet_nonempty imgLen d γ_core S hS r n)).map fun x =>
        ofList (n + γ * Nat.log 2 n) (fullGen g imgLen d γ_core γ (List.ofFn x))).map
          fun y => ofList m_lhl (List.ofFn y) by
      simp only [D_lhl, PMF.map_comp, Function.comp_def]
      congr 1; funext x
      rw [ofFn_ofList (by simp only [length_fullGen, List.length_ofFn]), BitString.ofList_take]]
  exact PMF.entropy_map_le _ _

/-! ### Goldreich–Levin hybrid reduction and PPT inverter -/

/-- Overwrite row `idx` of a flat `k`-column Boolean matrix word `h2` with `query`. -/
private def spliceMatrixWord (k idx : ℕ) (h2 query : List Bool) : List Bool :=
  h2.take (idx * k) ++ query ++ h2.drop ((idx + 1) * k)

@[local fun_prop]
private theorem computableInPolyTime_spliceMatrixWord {α : Type} {encode : α ↪ List Bool}
    {k idx : α → ℕ} {h2 query : α → List Bool}
    (hk : ComputableInPolyTime k encode encUnary)
    (hidx : ComputableInPolyTime idx encode encUnary)
    (hh2 : ComputableInPolyTime h2 encode encBits)
    (hquery : ComputableInPolyTime query encode encBits) :
    ComputableInPolyTime
      (fun a => spliceMatrixWord (k a) (idx a) (h2 a) (query a)) encode encBits :=
  .bitsAppend (.bitsAppend (.bitsTakeWithInput hh2 (.unary_mul' hidx hk)) hquery)
    (.bitsDropWithInput hh2 (.unary_mul' (.unary_add' hidx (.const 1)) hk))

/-- Assemble the word challenge fed to the PRG distinguisher at hybrid step `idx = m2 + j`. -/
private def wordChallenge (k m1 idx : ℕ) (pad h1 image h2 digest r_word z_tail query : List Bool) :
    List Bool :=
  pad ++ h1 ++ LinearHash.wordHash m1 h1 image ++
    spliceMatrixWord k idx h2 query ++ digest ++ r_word ++ z_tail

@[local fun_prop]
private theorem computableInPolyTime_wordChallenge {α : Type} {encode : α ↪ List Bool}
    {k m1 idx : α → ℕ} {pad h1 image h2 digest r_word z_tail query : α → List Bool}
    (hk : ComputableInPolyTime k encode encUnary)
    (hm1 : ComputableInPolyTime m1 encode encUnary)
    (hidx : ComputableInPolyTime idx encode encUnary)
    (hpad : ComputableInPolyTime pad encode encBits)
    (hh1 : ComputableInPolyTime h1 encode encBits)
    (himage : ComputableInPolyTime image encode encBits)
    (hh2 : ComputableInPolyTime h2 encode encBits)
    (hdigest : ComputableInPolyTime digest encode encBits)
    (hr_word : ComputableInPolyTime r_word encode encBits)
    (hz_tail : ComputableInPolyTime z_tail encode encBits)
    (hquery : ComputableInPolyTime query encode encBits) :
    ComputableInPolyTime
      (fun a => wordChallenge (k a) (m1 a) (idx a) (pad a) (h1 a) (image a)
        (h2 a) (digest a) (r_word a) (z_tail a) (query a)) encode encBits :=
  .bitsAppend (.bitsAppend (.bitsAppend (.bitsAppend (.bitsAppend (.bitsAppend hpad hh1)
    (LinearHash.computableInPolyTime_wordHash hm1 hh1 himage))
    (computableInPolyTime_spliceMatrixWord hk hidx hh2 hquery)) hdigest) hr_word) hz_tail

/-- Convert the saved-coin distinguisher into a signed parity predictor for row `idx` of `h2`. -/
private def wordStepPredictor (evaluate : (ℕ × List Bool) → List Bool → Bool)
    (n k m1 idx : ℕ)
    (pad h1 image h2 digest r_word pol_word z_tail coins query : List Bool) : Bool :=
  let r_bit := r_word.headD false
  let pol := pol_word.headD false
  (if evaluate (n, wordChallenge k m1 idx pad h1 image h2 digest r_word z_tail query) coins then
    r_bit
  else !r_bit) ^^ pol

@[local fun_prop]
private theorem computableInPolyTime_wordStepPredictor {α : Type} {encode : α ↪ List Bool}
    {evaluate : (ℕ × List Bool) → List Bool → Bool}
    {n k m1 idx : α → ℕ}
    {pad h1 image h2 digest r_word pol_word z_tail coins query : α → List Bool}
    (hevaluate : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × List Bool => evaluate p.1 p.2)
      (encPair (encPair encUnary encBits) encBits) encBool)
    (hn : ComputableInPolyTime n encode encUnary)
    (hk : ComputableInPolyTime k encode encUnary)
    (hm1 : ComputableInPolyTime m1 encode encUnary)
    (hidx : ComputableInPolyTime idx encode encUnary)
    (hpad : ComputableInPolyTime pad encode encBits)
    (hh1 : ComputableInPolyTime h1 encode encBits)
    (himage : ComputableInPolyTime image encode encBits)
    (hh2 : ComputableInPolyTime h2 encode encBits)
    (hdigest : ComputableInPolyTime digest encode encBits)
    (hr_word : ComputableInPolyTime r_word encode encBits)
    (hpol_word : ComputableInPolyTime pol_word encode encBits)
    (hz_tail : ComputableInPolyTime z_tail encode encBits)
    (hcoins : ComputableInPolyTime coins encode encBits)
    (hquery : ComputableInPolyTime query encode encBits) :
    ComputableInPolyTime
      (fun a => wordStepPredictor evaluate (n a) (k a) (m1 a) (idx a) (pad a) (h1 a)
        (image a) (h2 a) (digest a) (r_word a) (pol_word a) (z_tail a) (coins a) (query a))
      encode encBool := by
  -- `fun_prop` takes seconds to find this composition through the case split.
  have heval : ComputableInPolyTime
      (fun a => evaluate (n a, wordChallenge (k a) (m1 a) (idx a) (pad a) (h1 a) (image a) (h2 a)
        (digest a) (r_word a) (z_tail a) (query a)) (coins a)) encode encBool :=
    hevaluate.comp' ((hn.prod (computableInPolyTime_wordChallenge hk hm1 hidx hpad hh1
      himage hh2 hdigest hr_word hz_tail hquery)).prod hcoins)
  have hr_bit : ComputableInPolyTime (fun a => (r_word a).headD false) encode encBool :=
    (ComputableInPolyTime.headD false).comp' hr_word
  exact ComputableInPolyTime.bool_xor.comp'
    ((heval.ite hr_bit (ComputableInPolyTime.bool_not.comp' hr_bit)).prod
      ((ComputableInPolyTime.headD (encA := encBool) false).comp' hpol_word))

/-- Coin budget for the PRG distinguisher on an output of length `n + γ * Nat.log 2 n` at
security parameter `n`. -/
private def condCoinBudget (c_eval d_eval γ n : ℕ) : ℕ :=
  c_eval * (3 * n + γ * Nat.log 2 n + 2) ^ d_eval

@[local fun_prop]
private theorem computableInPolyTime_condCoinBudget {α : Type} {encode : α ↪ List Bool}
    (c_eval d_eval γ : ℕ) {n : α → ℕ}
    (hn : ComputableInPolyTime n encode encUnary) :
    ComputableInPolyTime (fun a => condCoinBudget c_eval d_eval γ (n a))
      encode encUnary := by unfold condCoinBudget; fun_prop

/-- Inner Goldreich–Levin inversion step: sample `h2`, `digest`, and `masks`, and run
`wordDecode`. -/
private noncomputable def innerGuessInverter (g : List Bool → List Bool)
    (evaluate : (ℕ × List Bool) → List Bool → Bool)
    (d γ_core deg n k r_val j : ℕ)
    (pad h1 image r_word pol_word z_tail coins : List Bool) : ProbComp (List Bool) := do
  let h2 ← BitString.sampleList (h2Rows d γ_core k * k)
  let digest ← BitString.sampleList (l2Val d k r_val + j)
  let masks ← BitString.sampleList
    (GoldreichLevin.maskCount k (GoldreichLevin.precision deg k) * k)
  return GoldreichLevin.wordDecode g
    (wordStepPredictor evaluate n k (l1Val d k r_val) (l2Val d k r_val + j)
      pad h1 image h2 digest r_word pol_word z_tail coins)
    deg k image masks

@[local fun_prop]
private theorem isPPTOn_innerGuessInverter {α : Type} {encode : α ↪ List Bool}
    {g : List Bool → List Bool} {evaluate : (ℕ × List Bool) → List Bool → Bool}
    (d γ_core deg : ℕ)
    {n k r_val j : α → ℕ} {pad h1 image r_word pol_word z_tail coins : α → List Bool}
    (hg : ComputableInPolyTime g encBits encBits)
    (hevaluate : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × List Bool => evaluate p.1 p.2)
      (encPair (encPair encUnary encBits) encBits) encBool)
    (hn : ComputableInPolyTime n encode encUnary)
    (hk : ComputableInPolyTime k encode encUnary)
    (hr_val : ComputableInPolyTime r_val encode encUnary)
    (hj : ComputableInPolyTime j encode encUnary)
    (hpad : ComputableInPolyTime pad encode encBits)
    (hh1 : ComputableInPolyTime h1 encode encBits)
    (himage : ComputableInPolyTime image encode encBits)
    (hr_word : ComputableInPolyTime r_word encode encBits)
    (hpol_word : ComputableInPolyTime pol_word encode encBits)
    (hz_tail : ComputableInPolyTime z_tail encode encBits)
    (hcoins : ComputableInPolyTime coins encode encBits) :
    IsPPTOn encode encBits (fun a => innerGuessInverter g evaluate d γ_core deg
      (n a) (k a) (r_val a) (j a) (pad a) (h1 a) (image a)
      (r_word a) (pol_word a) (z_tail a) (coins a)) := by
  unfold innerGuessInverter
  fun_prop

/-- Sample the auxiliary hybrid randomness (`pad`, `h1`, `r_word`, `pol_word`, `z_tail`, `coins`)
and invoke `innerGuessInverter`. -/
private noncomputable def stepAuxInverter (g : List Bool → List Bool) (imgLen : ℕ → ℕ)
    (evaluate : (ℕ × List Bool) → List Bool → Bool)
    (d γ_core γ c_eval d_eval deg k r_val n_offset j : ℕ)
    (image : List Bool) : ProbComp (List Bool) := do
  let pad ← BitString.sampleList n_offset
  let h1 ← BitString.sampleList (k * imgLen k)
  let r_word ← BitString.sampleList 1
  let pol_word ← BitString.sampleList 1
  let z_tail ← BitString.sampleList
    (mActual d γ k (coreSeedLen imgLen d γ_core k + n_offset) - (j + 1))
  let coins ← BitString.sampleList
    (condCoinBudget c_eval d_eval γ (coreSeedLen imgLen d γ_core k + n_offset))
  innerGuessInverter g evaluate d γ_core deg
    (coreSeedLen imgLen d γ_core k + n_offset) k r_val j pad h1 image r_word pol_word z_tail coins

@[local fun_prop]
private theorem isPPTOn_stepAuxInverter {α : Type} {encode : α ↪ List Bool}
    {g : List Bool → List Bool} {imgLen : ℕ → ℕ}
    {evaluate : (ℕ × List Bool) → List Bool → Bool}
    (d γ_core γ c_eval d_eval deg : ℕ)
    {k r_val n_offset j : α → ℕ} {image : α → List Bool}
    (hg : ComputableInPolyTime g encBits encBits)
    (himgLen : ComputableInPolyTime imgLen encUnary encUnary)
    (hevaluate : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × List Bool => evaluate p.1 p.2)
      (encPair (encPair encUnary encBits) encBits) encBool)
    (hk : ComputableInPolyTime k encode encUnary)
    (hr_val : ComputableInPolyTime r_val encode encUnary)
    (hn_offset : ComputableInPolyTime n_offset encode encUnary)
    (hj : ComputableInPolyTime j encode encUnary)
    (himage : ComputableInPolyTime image encode encBits) :
    IsPPTOn encode encBits (fun a => stepAuxInverter g imgLen evaluate d γ_core γ
      c_eval d_eval deg (k a) (r_val a) (n_offset a) (j a) (image a)) := by
  unfold stepAuxInverter
  fun_prop

/-- Complete uniform PPT inverter reducing conditional PRG distinguishing to inverting `g`:
samples `r_val`, `n_offset`, and hybrid step `j` in dyadic ranges and runs `stepAuxInverter`. -/
private noncomputable def condInverter (g : List Bool → List Bool) (imgLen : ℕ → ℕ)
    (evaluate : (ℕ × List Bool) → List Bool → Bool)
    (d γ_core γ c_eval d_eval deg : ℕ) : Inverter := fun k image => do
  let r_val ← ProbComp.sampleDyadicIndex (k + 1)
  let n_offset ← ProbComp.sampleDyadicIndex (coreSeedLen imgLen d γ_core (k + 1))
  let j ← ProbComp.sampleDyadicIndex
    (mActual d γ k (coreSeedLen imgLen d γ_core k + n_offset))
  stepAuxInverter g imgLen evaluate d γ_core γ c_eval d_eval deg k r_val n_offset j image

private theorem isPPT_condInverter {g : List Bool → List Bool} {imgLen : ℕ → ℕ}
    {evaluate : (ℕ × List Bool) → List Bool → Bool}
    (hg : ComputableInPolyTime g encBits encBits)
    (himgLen : ComputableInPolyTime imgLen encUnary encUnary)
    (hevaluate : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × List Bool => evaluate p.1 p.2)
      (encPair (encPair encUnary encBits) encBits) encBool)
    (d γ_core γ c_eval d_eval deg : ℕ) :
    IsPPT encBits (condInverter g imgLen evaluate d γ_core γ c_eval d_eval deg) := by
  unfold condInverter
  fun_prop

/-- Typed finite predictor matching `wordStepPredictor`. -/
private def stepPredictor (evaluate : (ℕ × List Bool) → List Bool → Bool)
    (n k imgLen_k d γ_core r_val j : ℕ)
    (pad h1 r_word pol_word z_tail coins : List Bool)
    (image : BitString imgLen_k)
    (rows : Fin (h2Rows d γ_core k) → BitString k)
    (digest : BitString (l2Val d k r_val + j))
    (query : BitString k) : Bool :=
  wordStepPredictor evaluate n k (l1Val d k r_val) (l2Val d k r_val + j)
    pad h1 (List.ofFn image)
    (List.ofFn ((blocksEquiv (m := h2Rows d γ_core k) (k := k)).symm rows))
    (List.ofFn digest) r_word pol_word z_tail coins (List.ofFn query)

/-- `innerGuessInverter` evaluates to `Pseudoentropy.guessInverter` mapped by `List.ofFn`. -/
private theorem eval_innerGuessInverter {k imgLen_k : ℕ}
    (g : List Bool → List Bool) (f : BitString k → BitString imgLen_k)
    (hf : ∀ x : BitString k, g (List.ofFn x) = List.ofFn (f x))
    (evaluate : (ℕ × List Bool) → List Bool → Bool)
    (d γ_core deg n r_val j : ℕ)
    (pad h1 r_word pol_word z_tail coins : List Bool) (image : BitString imgLen_k) :
    ProbComp.eval (innerGuessInverter g evaluate d γ_core deg n k r_val j
        pad h1 (List.ofFn image) r_word pol_word z_tail coins) =
      (Pseudoentropy.guessInverter f
        (stepPredictor evaluate n k imgLen_k d γ_core r_val j pad h1 r_word pol_word z_tail coins
          image)
        (PMF.uniformOfFintype (Fin (h2Rows d γ_core k) → BitString k))
        (GoldreichLevin.precision deg k) image).map List.ofFn := by
  have hmatrix : uniformList (h2Rows d γ_core k * k) =
      (PMF.uniformOfFintype (Fin (h2Rows d γ_core k) → BitString k)).map
        (fun rows => List.ofFn ((blocksEquiv (m := h2Rows d γ_core k) (k := k)).symm rows)) := by
    rw [uniformList,
      ← PMF.uniformOfFintype_map_equiv (blocksEquiv (m := h2Rows d γ_core k) (k := k)).symm,
      PMF.map_comp]
    rfl
  have hfunction : (fun bits : BitString k => g (List.ofFn bits)) =
      (List.ofFn : BitString imgLen_k → List Bool) ∘ f := funext hf
  have hdecode (predictor : List Bool → Bool) :
      (uniformList (GoldreichLevin.maskCount k (GoldreichLevin.precision deg k) * k)).bind
        (fun masks => PMF.pure (GoldreichLevin.wordDecode g predictor deg k
          (List.ofFn image) masks)) =
      (GoldreichLevin.invertFixed f (fun query => predictor (List.ofFn query))
        (GoldreichLevin.maskCount k (GoldreichLevin.precision deg k)) image).map List.ofFn := by
    change (uniformList _).map (GoldreichLevin.wordDecode g predictor deg k (List.ofFn image)) = _
    rw [GoldreichLevin.uniform_wordDecode, hfunction,
      GoldreichLevin.invertFixed_comp_injective f List.ofFn (fun _ _ h => List.ofFn_inj.mp h)]
  simp only [innerGuessInverter, ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList]
  simp_rw [hdecode, hmatrix]
  simp only [pmf_norm, uniformList, Pseudoentropy.guessInverter]
  rfl

/-- Splicing row `idx` in a flat matrix word agrees with `Function.update` on the block rows. -/
private theorem spliceMatrixWord_eq_ofFn_update {m k : ℕ} (rows : Fin m → BitString k)
    (idx : Fin m) (query : BitString k) :
    spliceMatrixWord k idx.val
        (List.ofFn ((blocksEquiv (m := m) (k := k)).symm rows)) (List.ofFn query) =
      List.ofFn ((blocksEquiv (m := m) (k := k)).symm (Function.update rows idx query)) := by
  have hidx_le : (idx.val + 1) * k ≤ m * k := Nat.mul_le_mul_right k idx.isLt
  have htake_len : (List.take (idx.val * k) (List.ofFn (blocksEquiv.symm rows))).length =
      idx.val * k := by
    simp only [List.length_take, List.length_ofFn]; rw [Nat.add_mul, one_mul] at hidx_le; omega
  refine List.ext_getElem (by
    simp only [spliceMatrixWord, List.length_append, List.length_take, List.length_drop,
      List.length_ofFn]
    rw [Nat.add_mul, one_mul] at hidx_le ⊢; omega) fun p hp₁ hp₂ => ?_
  rw [List.length_ofFn] at hp₂
  let q := finProdFinEquiv.symm ⟨p, hp₂⟩
  have hp_eq : p = q.1.val * k + q.2.val := by
    have := congrArg Fin.val (finProdFinEquiv.apply_symm_apply ⟨p, hp₂⟩)
    simpa only [q, finProdFinEquiv_apply_val, Nat.mul_comm, Nat.add_comm] using this.symm
  simp only [List.getElem_ofFn, blocksEquiv_symm_apply, spliceMatrixWord]
  rcases lt_trichotomy q.1.val idx.val with hlt | heq | hgt
  · have hlt_p : p < idx.val * k := by
      have : (q.1.val + 1) * k ≤ idx.val * k := Nat.mul_le_mul_right k hlt
      rw [Nat.add_mul, one_mul] at this; have := q.2.isLt; omega
    rw [List.getElem_append_left (by simp only [List.length_append, htake_len]; omega),
      List.getElem_append_left (by omega), List.getElem_take, List.getElem_ofFn,
      blocksEquiv_symm_apply, Function.update_of_ne (Fin.ne_of_val_ne hlt.ne)]
  · rw [List.getElem_append_left (by
        simp only [List.length_append, htake_len, List.length_ofFn, hp_eq, heq]; have := q.2.isLt
        omega),
      List.getElem_append_right (by simp only [htake_len, hp_eq, heq]; exact Nat.le_add_right _ _),
      List.getElem_ofFn, show Function.update rows idx query q.1 = query by
        rw [Fin.ext heq, Function.update_self]]
    refine congrArg query (Fin.ext ?_)
    change p - (List.take (idx.val * k) (List.ofFn (blocksEquiv.symm rows))).length = q.2.val
    rw [htake_len, hp_eq, heq, add_tsub_cancel_left]
  · have hge_p : (idx.val + 1) * k ≤ p :=
      (Nat.mul_le_mul_right k hgt).trans (by rw [hp_eq]; exact Nat.le_add_right _ _)
    have hmid_len :
        (List.take (idx.val * k) (List.ofFn (blocksEquiv.symm rows)) ++ List.ofFn query).length =
          (idx.val + 1) * k := by
      rw [List.length_append, htake_len, List.length_ofFn, Nat.add_mul, one_mul]
    rw [List.getElem_append_right (by rw [hmid_len]; exact hge_p), List.getElem_drop,
      List.getElem_ofFn, blocksEquiv_symm_apply, Function.update_of_ne (Fin.ne_of_val_ne hgt.ne')]
    exact congrArg (fun x : Fin (m * k) =>
      rows (finProdFinEquiv.symm x).1 (finProdFinEquiv.symm x).2)
      (Fin.ext (by dsimp only; rw [hmid_len]; exact Nat.add_sub_of_le hge_p))

private theorem update_comp_castLE_of_eq {c2 m_pre : ℕ} {α : Type*}
    (rows : Fin c2 → α) (idx : Fin c2) (query : α)
    (hlen : m_pre ≤ c2) (hidx : m_pre = idx.val) :
    Function.update rows idx query ∘ Fin.castLE hlen = rows ∘ Fin.castLE hlen := by
  funext i
  simp only [Function.comp_apply]
  have hne : (Fin.castLE hlen i).val ≠ idx.val := by
    simp only [Fin.val_castLE, ← hidx]
    exact ne_of_lt i.isLt
  exact Function.update_of_ne (Fin.ne_of_val_ne hne) _ _

/-- Averaging `2 * agreement - 1` over the random guess bit `r_bit : Bool` equals twice the
distinguishing gap between the target inner-product bit `x ⬝ᵥ query` and a uniform bit. -/
private theorem sum_bool_agreement_eq {k : ℕ} (evalBit : BitString k → Bool → Bool)
    (x : BitString k) :
    (∑ r_bit : Bool, (PMF.uniformOfFintype Bool r_bit).toReal *
      (2 * GoldreichLevin.agreement
        (fun query => if evalBit query r_bit then r_bit else !r_bit) x - 1)) =
    2 * ((((PMF.uniformOfFintype (BitString k)).map
          (fun query => evalBit query (x ⬝ᵥ query))) true).toReal -
        (((PMF.uniformOfFintype (BitString k)).bind fun query =>
          (PMF.uniformOfFintype Bool).map (evalBit query)) true).toReal) := by
  have hsum :
      ∑ r_bit : Bool, (PMF.uniformOfFintype Bool r_bit).toReal *
        GoldreichLevin.agreement (fun query => if evalBit query r_bit then r_bit else !r_bit) x =
      1 / 2 +
        (((PMF.uniformOfFintype (BitString k)).map
          (fun query => evalBit query (x ⬝ᵥ query))) true).toReal -
        (((PMF.uniformOfFintype (BitString k)).bind fun query =>
          (PMF.uniformOfFintype Bool).map (evalBit query)) true).toReal := by
    refine Eq.symm <| (PRG.toReal_bind_guessOfDistinguisher (PMF.uniformOfFintype (BitString k))
      (fun query => x ⬝ᵥ query) (fun query b => PMF.pure (evalBit query b))).symm.trans ?_
    simp only [pmf_norm, GoldreichLevin.agreement_eq_probability, PRG.guessOfDistinguisher,
      PMF.map, beq_eq_decide]
    rw [PMF.bind_comm, PMF.bind_apply_toReal]
  simp_rw [mul_sub, mul_one, mul_left_comm _ (2 : ℝ)]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, PMF.sum_toReal, hsum]
  ring

private theorem cond_xor_eq (b r_bit pol : Bool) :
    ((if b then r_bit else !r_bit) ^^ pol) = (if (b ^^ pol) then r_bit else !r_bit) := by
  cases b <;> cases r_bit <;> cases pol <;> rfl

private theorem sum_mul_sum_mul_sum_comm {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (wa : α → ℝ) (wb : β → ℝ) (wc : γ → ℝ) (f : α → β → γ → ℝ) :
    (∑ a : α, wa a * ∑ b : β, wb b * ∑ c : γ, wc c * f a b c) =
    ∑ c : γ, wc c * ∑ a : α, wa a * ∑ b : β, wb b * f a b c := by
  simp_rw [Finset.mul_sum]
  trans (∑ a : α, ∑ c : γ, ∑ b : β, wa a * (wb b * (wc c * f a b c)))
  · refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun a _ =>
        Finset.sum_congr rfl fun b _ => by ring

private noncomputable def fiberErr (deg k m2 fibCard : ℕ) : ℝ :=
  1 / (GoldreichLevin.precision deg k : ℝ) +
    if m2 = 0 then 0 else 2 * Real.sqrt ((2 : ℝ) ^ m2 / fibCard)

private noncomputable def stepWordEval {k imgLen_k : ℕ}
    (f : BitString k → BitString imgLen_k) (x₀ : BitString k)
    (evaluate : (ℕ × List Bool) → List Bool → Bool) (pol : Bool)
    (n d γ_core r_val j : ℕ) (pad h1 z_tail coins : List Bool)
    (hlen : l2Val d k r_val + j ≤ h2Rows d γ_core k)
    (rows : Fin (h2Rows d γ_core k) → BitString k) (x : BitString k) (b : Bool) : Bool :=
  (evaluate (n, pad ++ h1 ++ LinearHash.wordHash (l1Val d k r_val) h1 (List.ofFn (f x₀)) ++
    List.ofFn ((blocksEquiv (m := h2Rows d γ_core k) (k := k)).symm rows) ++
    List.ofFn (LinearHash.hash (rows ∘ Fin.castLE hlen) x) ++ [b] ++ z_tail) coins) ^^ pol

private noncomputable def stepGuessHit {k imgLen_k : ℕ}
    (f : BitString k → BitString imgLen_k) (x₀ : BitString k)
    (evaluate : (ℕ × List Bool) → List Bool → Bool)
    (n d γ_core r_val j deg : ℕ) (pad h1 z_tail coins : List Bool) (r_bit pol : Bool) : PMF Bool :=
  (Pseudoentropy.guessInverter f
    (stepPredictor evaluate n k imgLen_k d γ_core r_val j pad h1 [r_bit] [pol]
      z_tail coins (f x₀))
    (PMF.uniformOfFintype (Fin (h2Rows d γ_core k) → BitString k))
    (GoldreichLevin.precision deg k) (f x₀)).map (fun z => f z == f x₀)

private noncomputable def fiberStepDist {k imgLen_k : ℕ}
    (f : BitString k → BitString imgLen_k) (x₀ : BitString k)
    (evaluate : (ℕ × List Bool) → List Bool → Bool) (pol : Bool)
    (n d γ_core r_val j : ℕ) (pad h1 z_tail coins : List Bool)
    (hidx_lt : l2Val d k r_val + j < h2Rows d γ_core k) (real : Bool) : PMF Bool :=
  haveI : Nonempty {x : BitString k // f x = f x₀} := ⟨⟨x₀, rfl⟩⟩
  (PMF.uniformOfFintype (Fin (h2Rows d γ_core k) → BitString k)).bind fun rows =>
    (PMF.uniformOfFintype {x : BitString k // f x = f x₀}).bind fun x =>
      let body b := stepWordEval f x₀ evaluate pol n d γ_core r_val j pad h1 z_tail coins
        hidx_lt.le rows x.val b
      if real then PMF.pure (body (x.val ⬝ᵥ rows ⟨l2Val d k r_val + j, hidx_lt⟩))
      else (PMF.uniformOfFintype Bool).map body

/-- Single-step hybrid prediction-to-inversion inequality on the fiber of `x₀` for fixed auxiliary
words `pad`, `h1`, `z_tail`, `coins` and polarity `pol`
([Liu and Pass, Proof of Lemma 5.1, Appendix A, pp. 22–23 of arXiv:2009.11514v1][LiuPass2020]). -/
private theorem fiber_step_diff_le {k imgLen_k : ℕ}
    (f : BitString k → BitString imgLen_k) (x₀ : BitString k)
    (evaluate : (ℕ × List Bool) → List Bool → Bool) (pol : Bool)
    (n d γ_core r_val j deg : ℕ)
    (pad h1 z_tail coins : List Bool)
    (hidx_lt : l2Val d k r_val + j < h2Rows d γ_core k) :
    2 * ((fiberStepDist f x₀ evaluate pol n d γ_core r_val j pad h1 z_tail coins hidx_lt true
            true).toReal -
          (fiberStepDist f x₀ evaluate pol n d γ_core r_val j pad h1 z_tail coins hidx_lt false
            true).toReal) ≤
      fiberErr deg k (l2Val d k r_val) (Nat.card {x : BitString k // f x = f x₀}) +
      2 ^ (j + 1) *
        ∑ r_bit : Bool, (PMF.uniformOfFintype Bool r_bit).toReal *
          (stepGuessHit f x₀ evaluate n d γ_core r_val j deg pad h1 z_tail coins r_bit pol
            true).toReal := by
  have : Nonempty {x : BitString k // f x = f x₀} := ⟨⟨x₀, rfl⟩⟩
  let hlen : l2Val d k r_val + j ≤ h2Rows d γ_core k := hidx_lt.le
  let c2 := h2Rows d γ_core k
  let idx : Fin c2 := ⟨l2Val d k r_val + j, hidx_lt⟩
  let evalBit (rows : Fin c2 → BitString k) (x query : BitString k) (b : Bool) : Bool :=
    (evaluate (n, wordChallenge k (l1Val d k r_val) (l2Val d k r_val + j) pad h1
      (List.ofFn (f x₀)) (List.ofFn ((blocksEquiv (m := c2) (k := k)).symm rows))
      (List.ofFn (LinearHash.hash (rows ∘ Fin.castLE hlen) x)) [b] z_tail
      (List.ofFn query)) coins) ^^ pol
  have hupd (rows : Fin c2 → BitString k) (query x : BitString k) (b : Bool) :
      stepWordEval f x₀ evaluate pol n d γ_core r_val j pad h1 z_tail coins hlen
        (Function.update rows idx query) x b = evalBit rows x query b := by
    simp only [stepWordEval, evalBit, wordChallenge,
      (spliceMatrixWord_eq_ofFn_update rows idx query).symm,
      update_comp_castLE_of_eq rows idx query hlen rfl]
    rfl
  have hp_real : fiberStepDist f x₀ evaluate pol n d γ_core r_val j pad h1 z_tail coins
        hidx_lt true =
      (PMF.uniformOfFintype (Fin c2 → BitString k)).bind fun rows =>
        (PMF.uniformOfFintype {x : BitString k // f x = f x₀}).bind fun x =>
          (PMF.uniformOfFintype (BitString k)).map fun query =>
            evalBit rows x.val query (x.val ⬝ᵥ query) := by
    dsimp only [fiberStepDist]; rw [PMF.bind_uniformOfFintype_update idx]
    pmf_swap with rows x query
    simp only [ite_true, hupd]
    exact congrArg (fun v => PMF.pure (evalBit rows x.val query (x.val ⬝ᵥ v)))
      (Function.update_self idx query rows)
  have hp_rand : fiberStepDist f x₀ evaluate pol n d γ_core r_val j pad h1 z_tail coins
        hidx_lt false =
      (PMF.uniformOfFintype (Fin c2 → BitString k)).bind fun rows =>
        (PMF.uniformOfFintype {x : BitString k // f x = f x₀}).bind fun x =>
          (PMF.uniformOfFintype (BitString k)).bind fun query =>
            (PMF.uniformOfFintype Bool).map (evalBit rows x.val query) := by
    dsimp only [fiberStepDist]; rw [PMF.bind_uniformOfFintype_update idx]
    pmf_swap with rows x query
    simp only [Bool.false_eq_true, ite_false, hupd]
  have hpred_eq (r_bit : Bool) (rows : Fin c2 → BitString k) (x : BitString k) :
      (fun query => if evalBit rows x query r_bit then r_bit else !r_bit) =
      stepPredictor evaluate n k imgLen_k d γ_core r_val j pad h1 [r_bit] [pol]
        z_tail coins (f x₀) rows (LinearHash.hash (rows ∘ Fin.castLE hlen) x) :=
    funext fun query => by
      simp only [stepPredictor, wordStepPredictor, evalBit, cond_xor_eq, List.headD_cons]
  rw [hp_real, hp_rand, PMF.bind_apply_toReal, PMF.bind_apply_toReal, ← Finset.sum_sub_distrib,
    Finset.mul_sum]
  refine le_trans (le_of_eq ?_) (PMF.sum_le_affine (PMF.uniformOfFintype Bool) fun r_bit =>
    Pseudoentropy.matrix_fiber_correlation_le f (f x₀) hlen
      (stepPredictor evaluate n k imgLen_k d γ_core r_val j pad h1 [r_bit] [pol] z_tail coins
        (f x₀))
      (GoldreichLevin.precision deg k) (GoldreichLevin.precision_pos deg k))
  refine (Finset.sum_congr rfl fun rows _ => ?_).trans (sum_mul_sum_mul_sum_comm _ _ _ _)
  rw [PMF.bind_apply_toReal, PMF.bind_apply_toReal, ← mul_sub, ← Finset.sum_sub_distrib,
    mul_left_comm, Finset.mul_sum]
  refine congrArg (_ * ·) (Finset.sum_congr rfl fun x _ => ?_)
  rw [← mul_sub, mul_left_comm, ← sum_bool_agreement_eq (evalBit rows x.val) x.val]
  simp_rw [hpred_eq _ rows x.val]

private theorem ofFn_hash_castLE_succ {k c2 w : ℕ} (rows : Fin c2 → BitString k) (x : BitString k)
    (hlen : w ≤ c2) (hidx_lt : w < c2) :
    List.ofFn (LinearHash.hash (rows ∘ Fin.castLE (Nat.succ_le_of_lt hidx_lt)) x) =
      List.ofFn (LinearHash.hash (rows ∘ Fin.castLE hlen) x) ++ [x ⬝ᵥ rows ⟨w, hidx_lt⟩] := by
  rw [List.ofFn_succ', List.concat_eq_append]
  refine congrArg₂ (· ++ ·) rfl ?_
  simp only [LinearHash.hash, Function.comp_apply, dotProduct_comm]
  rfl

private theorem uniformList_one_eq :
    BitString.uniformList 1 = (PMF.uniformOfFintype Bool).map (fun b => [b]) := by
  rw [BitString.uniformList_succ 0, BitString.uniformList_zero]
  simp only [pmf_norm]
  rfl

private theorem le_two_mul_sum_uniformOfFintype_bool (G : Bool → ℝ) (hG : ∀ p, 0 ≤ G p)
    (pol : Bool) :
    G pol ≤ 2 * ∑ p : Bool, (PMF.uniformOfFintype Bool p).toReal * G p := by
  have hle : (PMF.uniformOfFintype Bool pol).toReal * G pol ≤
      ∑ p : Bool, (PMF.uniformOfFintype Bool p).toReal * G p :=
    Finset.single_le_sum (fun p _ => mul_nonneg ENNReal.toReal_nonneg (hG p)) (Finset.mem_univ pol)
  rw [uniformOfFintype_bool_toReal] at hle
  linarith

/-- Acceptance distribution of the twisted distinguisher `evaluate ... ^^ pol` at hybrid step `j`
conditioned on the fiber of `x₀`. -/
private noncomputable def fiberHybridAcceptDist {k imgLen_k : ℕ}
    (f : BitString k → BitString imgLen_k) (x₀ : BitString k)
    (evaluate : (ℕ × List Bool) → List Bool → Bool) (pol : Bool)
    (n d γ_core r_val padLen m coinLen j : ℕ)
    (hlen : l2Val d k r_val + j ≤ h2Rows d γ_core k) : PMF Bool :=
  haveI : Nonempty {x : BitString k // f x = f x₀} := ⟨⟨x₀, rfl⟩⟩
  do
    let pad ← BitString.uniformList padLen
    let h1 ← BitString.uniformList (k * imgLen_k)
    let z_tail ← BitString.uniformList (m - j)
    let coins ← BitString.uniformList coinLen
    let rows ← PMF.uniformOfFintype (Fin (h2Rows d γ_core k) → BitString k)
    (PMF.uniformOfFintype {x : BitString k // f x = f x₀}).map fun x =>
      (evaluate (n, pad ++ h1 ++
        LinearHash.wordHash (l1Val d k r_val) h1 (List.ofFn (f x₀)) ++
        List.ofFn ((blocksEquiv (m := h2Rows d γ_core k) (k := k)).symm rows) ++
        List.ofFn (LinearHash.hash (rows ∘ Fin.castLE hlen) x.val) ++ z_tail) coins) ^^ pol

private theorem eval_stepAuxInverter_map_eq (g : List Bool → List Bool) (imgLen : ℕ → ℕ)
    {k : ℕ} (f : BitString k → BitString (imgLen k))
    (hf : ∀ x : BitString k, g (List.ofFn x) = List.ofFn (f x))
    (x₀ : BitString k)
    (evaluate : (ℕ × List Bool) → List Bool → Bool)
    (d γ_core γ c_eval d_eval deg r_val n_offset j : ℕ) :
    let n := coreSeedLen imgLen d γ_core k + n_offset
    let m := mActual d γ k n
    let coinLen := condCoinBudget c_eval d_eval γ n
    let Aux := BitString n_offset × BitString (k * imgLen k) × BitString (m - (j + 1)) ×
      BitString coinLen
    (ProbComp.eval (stepAuxInverter g imgLen evaluate d γ_core γ c_eval d_eval deg
      k r_val n_offset j (List.ofFn (f x₀)))).map (fun w => decide (g w = List.ofFn (f x₀))) =
    (PMF.uniformOfFintype Aux).bind fun a =>
      (PMF.uniformOfFintype Bool).bind fun r_bit =>
        (PMF.uniformOfFintype Bool).bind fun p =>
          stepGuessHit f x₀ evaluate n d γ_core r_val j deg
            (List.ofFn a.1) (List.ofFn a.2.1) (List.ofFn a.2.2.1) (List.ofFn a.2.2.2) r_bit p := by
  intro n m coinLen Aux
  simp only [stepAuxInverter, ProbComp.eval_bind, BitString.eval_sampleList, PMF.map_bind,
    uniformList_one_eq, PMF.bind_map, Function.comp_def]
  simp only [Aux, BitString.uniformList, ← PMF.uniformOfFintype_prod, pmf_norm]
  pmf_swap with pad h1 z_tail coins r_bit p
  rw [eval_innerGuessInverter g f hf, PMF.map_comp]
  congr 1; funext z
  simp only [Function.comp_apply, hf z, List.ofFn_inj, beq_eq_decide]

private theorem two_mul_bind_sub_toReal_le {α : Type*} [Fintype α]
    (μ : PMF α) (p₁ p₂ : α → PMF Bool) (C W : ℝ) (G : α → ℝ)
    (hpoint : ∀ a, μ a ≠ 0 →
      2 * ((p₁ a true).toReal - (p₂ a true).toReal) ≤ C + W * G a) :
    2 * (((μ.bind p₁) true).toReal - ((μ.bind p₂) true).toReal) ≤
      C + W * ∑ a : α, (μ a).toReal * G a := by
  simp only [PMF.bind_apply_toReal, ← Finset.sum_sub_distrib, Finset.mul_sum, ← mul_sub,
    mul_left_comm (2 : ℝ)]
  rw [← Finset.mul_sum]
  refine (Finset.sum_le_sum fun a _ => ?_).trans_eq (PMF.sum_affine μ C W G)
  by_cases ha : μ a = 0
  · simp only [ha, ENNReal.toReal_zero, zero_mul, le_refl]
  · exact mul_le_mul_of_nonneg_left (hpoint a ha) ENNReal.toReal_nonneg

/-- Single-step hybrid inequality on the fiber of `x₀`, averaged over the auxiliary hybrid words
`pad`, `h1`, `z_tail`, `coins` and bounded by `stepAuxInverter`. -/
private theorem fiberHybrid_step_le (g : List Bool → List Bool) (imgLen : ℕ → ℕ)
    {k : ℕ} (f : BitString k → BitString (imgLen k))
    (hf : ∀ x : BitString k, g (List.ofFn x) = List.ofFn (f x))
    (x₀ : BitString k)
    (evaluate : (ℕ × List Bool) → List Bool → Bool) (pol : Bool)
    (d γ_core γ c_eval d_eval deg r_val n_offset j : ℕ)
    (hj : j < mActual d γ k (coreSeedLen imgLen d γ_core k + n_offset))
    (hlen : l2Val d k r_val + j ≤ h2Rows d γ_core k)
    (hidx_lt : l2Val d k r_val + j < h2Rows d γ_core k) :
    let n := coreSeedLen imgLen d γ_core k + n_offset
    let m := mActual d γ k n
    let coinLen := condCoinBudget c_eval d_eval γ n
    2 * ((fiberHybridAcceptDist f x₀ evaluate pol n d γ_core r_val n_offset m coinLen (j + 1)
          (Nat.succ_le_of_lt hidx_lt) true).toReal -
        (fiberHybridAcceptDist f x₀ evaluate pol n d γ_core r_val n_offset m coinLen j
          hlen true).toReal) ≤
      1 / (GoldreichLevin.precision deg k : ℝ) +
      (if l2Val d k r_val = 0 then 0 else
        2 * Real.sqrt ((2 : ℝ) ^ (l2Val d k r_val) / Nat.card {x : BitString k // f x = f x₀})) +
      2 ^ (j + 2) *
        (((ProbComp.eval (stepAuxInverter g imgLen evaluate d γ_core γ c_eval d_eval deg
          k r_val n_offset j (List.ofFn (f x₀)))).map
            (fun w => decide (g w = List.ofFn (f x₀)))) true).toReal := by
  intro n m coinLen
  let Aux := BitString n_offset × BitString (k * imgLen k) × BitString (m - (j + 1)) ×
    BitString coinLen
  let stepD (real : Bool) (a : Aux) : PMF Bool :=
    fiberStepDist f x₀ evaluate pol n d γ_core r_val j
      (List.ofFn a.1) (List.ofFn a.2.1) (List.ofFn a.2.2.1) (List.ofFn a.2.2.2) hidx_lt real
  let invHit (a : Aux) (r_bit p : Bool) : PMF Bool :=
    stepGuessHit f x₀ evaluate n d γ_core r_val j deg
      (List.ofFn a.1) (List.ofFn a.2.1) (List.ofFn a.2.2.1) (List.ofFn a.2.2.2) r_bit p
  have hsucc_eq :
      fiberHybridAcceptDist f x₀ evaluate pol n d γ_core r_val n_offset m coinLen (j + 1)
        (Nat.succ_le_of_lt hidx_lt) = (PMF.uniformOfFintype Aux).bind (stepD true) := by
    simp only [pmf_norm, fiberHybridAcceptDist, Aux, stepD, fiberStepDist, stepWordEval,
      ↓reduceIte, ← PMF.uniformOfFintype_prod, BitString.uniformList]
    pmf_swap with pad h1 z_tail coins rows x
    simp only [List.append_assoc]
    exact congrArg (fun s => PMF.pure (evaluate (n, List.ofFn pad ++ (List.ofFn h1 ++
      (LinearHash.wordHash (l1Val d k r_val) (List.ofFn h1) (List.ofFn (f x₀)) ++
        (List.ofFn ((blocksEquiv (m := h2Rows d γ_core k) (k := k)).symm rows) ++ s))))
      (List.ofFn coins) ^^ pol))
      ((congrArg (· ++ List.ofFn z_tail)
        (ofFn_hash_castLE_succ rows x.val hlen hidx_lt)).trans (List.append_assoc _ _ _))
  have hcurr_eq :
      fiberHybridAcceptDist f x₀ evaluate pol n d γ_core r_val n_offset m coinLen j hlen =
      (PMF.uniformOfFintype Aux).bind (stepD false) := by
    have hm_sub : m - j = (m - (j + 1)) + 1 := by dsimp [m, n]; omega
    unfold fiberHybridAcceptDist
    rw [hm_sub, BitString.uniformList_succ]
    simp only [pmf_norm, Aux, stepD, fiberStepDist, stepWordEval, Bool.false_eq_true, ↓reduceIte,
      ← PMF.uniformOfFintype_prod, BitString.uniformList]
    pmf_swap with pad h1 z_tail coins rows x b
    simp only [List.append_assoc, List.singleton_append]
  rw [hsucc_eq, hcurr_eq]
  let C : ℝ := fiberErr deg k (l2Val d k r_val) (Nat.card {x : BitString k // f x = f x₀})
  refine (two_mul_bind_sub_toReal_le (PMF.uniformOfFintype Aux) (stepD true) (stepD false)
    C ((2 : ℝ) ^ (j + 2))
    (fun a => ∑ r_bit : Bool, (PMF.uniformOfFintype Bool r_bit).toReal *
      ∑ p : Bool, (PMF.uniformOfFintype Bool p).toReal * (invHit a r_bit p true).toReal)
    fun a _ => ?_).trans_eq ?_
  · have hfib := fiber_step_diff_le f x₀ evaluate pol n d γ_core r_val j deg
      (List.ofFn a.1) (List.ofFn a.2.1) (List.ofFn a.2.2.1) (List.ofFn a.2.2.2) hidx_lt
    have hsum_le :
        (∑ r_bit : Bool, (PMF.uniformOfFintype Bool r_bit).toReal *
          (invHit a r_bit pol true).toReal) ≤
        2 * ∑ r_bit : Bool, (PMF.uniformOfFintype Bool r_bit).toReal *
          ∑ p : Bool, (PMF.uniformOfFintype Bool p).toReal * (invHit a r_bit p true).toReal := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun r_bit _ => ?_
      have hbool := le_two_mul_sum_uniformOfFintype_bool
        (fun p => (invHit a r_bit p true).toReal) (fun _ => ENNReal.toReal_nonneg) pol
      have := mul_le_mul_of_nonneg_left hbool
        (ENNReal.toReal_nonneg : 0 ≤ (PMF.uniformOfFintype Bool r_bit).toReal)
      linarith
    have hmul := mul_le_mul_of_nonneg_left hsum_le (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (j + 1))
    have hpow : (2 : ℝ) ^ (j + 2) = (2 : ℝ) ^ (j + 1) * 2 := by ring
    rw [← mul_assoc, ← hpow] at hmul
    dsimp only [stepD, C, invHit] at hfib hmul ⊢
    linarith
  · rw [eval_stepAuxInverter_map_eq g imgLen f hf x₀ evaluate d γ_core γ c_eval d_eval deg
      r_val n_offset j]
    simp only [C, fiberErr, invHit, PMF.bind_apply_toReal]
    rfl

private theorem sum_le_mul_sampleDyadicIndex {α : Type} (bound : ℕ) (s : Finset ℕ)
    (hs : s ⊆ Finset.range (dyadicSize bound)) (P : ℕ → ProbComp α) (E : α → Bool) :
    ∑ j ∈ s, (((ProbComp.eval (P j)).map E) true).toReal ≤
      (dyadicSize bound : ℝ) *
        (((ProbComp.eval (do let j ← ProbComp.sampleDyadicIndex bound; P j)).map E)
          true).toReal := by
  have hpos : (0 : ℝ) < dyadicSize bound := Nat.cast_pos.mpr (dyadicSize_pos bound)
  simp only [pmf_norm, ProbComp.eval_sampleDyadicIndex, PMF.bind_apply_toReal,
    PMF.uniformOfFintype_apply, Fintype.card_fin, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ← Finset.mul_sum, ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
  rw [Fin.sum_univ_eq_sum_range fun j => (((ProbComp.eval (P j)).map E) true).toReal]
  exact Finset.sum_le_sum_of_subset_of_nonneg hs fun _ _ _ => ENNReal.toReal_nonneg

private theorem single_le_mul_sampleDyadicIndex {α : Type} (bound i : ℕ) (hi : i ≤ bound)
    (P : ℕ → ProbComp α) (E : α → Bool) :
    (((ProbComp.eval (P i)).map E) true).toReal ≤
      (dyadicSize bound : ℝ) *
        (((ProbComp.eval (do let j ← ProbComp.sampleDyadicIndex bound; P j)).map E)
          true).toReal := by
  simpa only [Finset.sum_singleton] using sum_le_mul_sampleDyadicIndex bound {i}
    (Finset.singleton_subset_iff.mpr (Finset.mem_range.mpr (lt_of_le_of_lt hi (lt_dyadicSize _))))
    P E

private theorem sum_range_le_mul_sampleDyadicIndex {α : Type} (bound : ℕ)
    (P : ℕ → ProbComp α) (E : α → Bool) :
    ∑ j ∈ Finset.range bound, (((ProbComp.eval (P j)).map E) true).toReal ≤
      (dyadicSize bound : ℝ) *
        (((ProbComp.eval (do let j ← ProbComp.sampleDyadicIndex bound; P j)).map E)
          true).toReal :=
  sum_le_mul_sampleDyadicIndex bound (Finset.range bound)
    (Finset.range_mono (lt_dyadicSize bound).le) P E

/-- Telescoped hybrid inequality across all `m = mActual d γ k n` steps on the fiber of `x₀`,
bounded by `condInverter`. -/
private theorem fiberHybrid_total_le (g : List Bool → List Bool) (imgLen : ℕ → ℕ)
    {k : ℕ} (f : BitString k → BitString (imgLen k))
    (hf : ∀ x : BitString k, g (List.ofFn x) = List.ofFn (f x))
    (x₀ : BitString k)
    (evaluate : (ℕ × List Bool) → List Bool → Bool) (pol : Bool)
    (d γ_core γ c_eval d_eval deg r_val n_offset : ℕ)
    (hr_le : r_val ≤ k + 1)
    (hn_off_le : n_offset ≤ coreSeedLen imgLen d γ_core (k + 1))
    (hm_le : l2Val d k r_val + mActual d γ k (coreSeedLen imgLen d γ_core k + n_offset) ≤
      h2Rows d γ_core k) :
    let n := coreSeedLen imgLen d γ_core k + n_offset
    let m := mActual d γ k n
    let coinLen := condCoinBudget c_eval d_eval γ n
    2 * ((fiberHybridAcceptDist f x₀ evaluate pol n d γ_core r_val n_offset m coinLen m
          hm_le true).toReal -
        (fiberHybridAcceptDist f x₀ evaluate pol n d γ_core r_val n_offset m coinLen 0
          (by omega) true).toReal) ≤
      (m : ℝ) * (1 / (GoldreichLevin.precision deg k : ℝ) +
        (if l2Val d k r_val = 0 then 0 else
          2 * Real.sqrt ((2 : ℝ) ^ (l2Val d k r_val) / Nat.card {x : BitString k // f x = f x₀}))) +
      (2 : ℝ) ^ (m + 1) * (dyadicSize m : ℝ) *
        (dyadicSize (coreSeedLen imgLen d γ_core (k + 1)) : ℝ) *
        (dyadicSize (k + 1) : ℝ) *
        (((ProbComp.eval (condInverter g imgLen evaluate d γ_core γ c_eval d_eval deg
          k (List.ofFn (f x₀)))).map
            (fun w => decide (g w = List.ofFn (f x₀)))) true).toReal := by
  intro n m coinLen
  let F (j : ℕ) : ℝ :=
    if hj : l2Val d k r_val + j ≤ h2Rows d γ_core k then
      (fiberHybridAcceptDist f x₀ evaluate pol n d γ_core r_val n_offset m coinLen j hj true).toReal
    else 0
  let C : ℝ := 1 / (GoldreichLevin.precision deg k : ℝ) +
    (if l2Val d k r_val = 0 then 0 else
      2 * Real.sqrt ((2 : ℝ) ^ (l2Val d k r_val) / Nat.card {x : BitString k // f x = f x₀}))
  let stepInv (j : ℕ) : ℝ :=
    (((ProbComp.eval (stepAuxInverter g imgLen evaluate d γ_core γ c_eval d_eval deg
      k r_val n_offset j (List.ofFn (f x₀)))).map
        (fun w => decide (g w = List.ofFn (f x₀)))) true).toReal
  have hsum_step : 2 * (F m - F 0) ≤
      (m : ℝ) * C + (2 : ℝ) ^ (m + 1) * ∑ j ∈ Finset.range m, stepInv j := by
    have hm_sum : (m : ℝ) * C + (2 : ℝ) ^ (m + 1) * ∑ j ∈ Finset.range m, stepInv j =
        ∑ j ∈ Finset.range m, (C + (2 : ℝ) ^ (m + 1) * stepInv j) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        ← Finset.mul_sum]
    rw [← Finset.sum_range_sub, Finset.mul_sum, hm_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    have hj_lt : j < m := Finset.mem_range.mp hj
    have hj_lt' : j < mActual d γ k (coreSeedLen imgLen d γ_core k + n_offset) := hj_lt
    have hidx_lt : l2Val d k r_val + j < h2Rows d γ_core k := by omega
    rw [show F (j + 1) = _ from dite_eq_left (Nat.succ_le_of_lt hidx_lt),
      show F j = _ from dite_eq_left hidx_lt.le]
    have h1 := fiberHybrid_step_le g imgLen f hf x₀ evaluate pol d γ_core γ c_eval d_eval deg
      r_val n_offset j hj_lt' hidx_lt.le hidx_lt
    have hmul : (2 : ℝ) ^ (j + 2) * stepInv j ≤ (2 : ℝ) ^ (m + 1) * stepInv j :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num) (by dsimp [m] at hj_lt; omega)) ENNReal.toReal_nonneg
    dsimp only [C, stepInv] at h1 ⊢; linarith
  let E (w : List Bool) := decide (g w = List.ofFn (f x₀))
  let runOff r_v n_off := do
    let j ← ProbComp.sampleDyadicIndex (mActual d γ k (coreSeedLen imgLen d γ_core k + n_off))
    stepAuxInverter g imgLen evaluate d γ_core γ c_eval d_eval deg k r_v n_off j (List.ofFn (f x₀))
  have hdyadic := (sum_range_le_mul_sampleDyadicIndex m
    (stepAuxInverter g imgLen evaluate d γ_core γ c_eval d_eval deg k r_val n_offset ·
      (List.ofFn (f x₀))) E).trans <|
    mul_le_mul_of_nonneg_left
      ((single_le_mul_sampleDyadicIndex (coreSeedLen imgLen d γ_core (k + 1)) n_offset hn_off_le
        (runOff r_val) E).trans <|
        mul_le_mul_of_nonneg_left (single_le_mul_sampleDyadicIndex (k + 1) r_val hr_le
          (fun r_v => do
            let n_off ← ProbComp.sampleDyadicIndex (coreSeedLen imgLen d γ_core (k + 1))
            runOff r_v n_off) E) (by positivity))
      (by positivity)
  rw [show F m = _ from dite_eq_left hm_le,
    show F 0 = _ from dite_eq_left (by omega)] at hsum_step
  have hmul_inv := mul_le_mul_of_nonneg_left hdyadic (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (m + 1))
  dsimp only [C, stepInv, condInverter, E, runOff] at hsum_step hmul_inv ⊢
  linarith

private theorem inversionGame_succProbability_eq (g : List Bool → List Bool) {k imgLen_k : ℕ}
    (f : BitString k → BitString imgLen_k)
    (hf : ∀ x : BitString k, g (List.ofFn x) = List.ofFn (f x))
    (adversary : Inverter) :
    (Game.succProbability (ProbComp.eval (inversionGame g adversary k)) : ℝ) =
      ∑ x₀ : BitString k, (PMF.uniformOfFintype (BitString k) x₀).toReal *
        (((ProbComp.eval (adversary k (List.ofFn (f x₀)))).map
          (fun w => decide (g w = List.ofFn (f x₀)))) true).toReal := by
  rw [Game.coe_succProbability]
  simp only [pmf_norm, inversionGame, inversionExperiment, BitString.eval_sampleList,
    BitString.uniformList, PMF.bind_apply_toReal, beq_eq_decide]
  refine Finset.sum_congr rfl fun x₀ _ => ?_
  rw [hf x₀]
  rfl

/-- Telescoped hybrid inequality averaged over a dense regularity bucket $S_{k, r}$ under the
regularity gap $r + d \lfloor \log_2 k \rfloor \le k$. -/
private theorem bucketHybrid_total_le (g : List Bool → List Bool) (imgLen : ℕ → ℕ)
    {k : ℕ} (f : BitString k → BitString (imgLen k))
    (hf : ∀ x : BitString k, g (List.ofFn x) = List.ofFn (f x))
    (r : Fin (k + 1)) (hS : (regularityBucket f r).Nonempty)
    (hdense : 2 ^ k ≤ (k + 1) * (regularityBucket f r).card)
    (evaluate : (ℕ × List Bool) → List Bool → Bool) (pol : Bool)
    (d γ_core γ c_eval d_eval deg n_offset n : ℕ)
    (hn_eq : coreSeedLen imgLen d γ_core k + n_offset = n)
    (hgap : r.val + d * Nat.log 2 k ≤ k)
    (hn_off_le : n_offset ≤ coreSeedLen imgLen d γ_core (k + 1))
    (hm_le : l2Val d k r.val + mActual d γ k n ≤ h2Rows d γ_core k) :
    let m := mActual d γ k n
    let coinLen := condCoinBudget c_eval d_eval γ n
    let side := PMF.uniformOfFinset (regularityBucket f r) hS
    2 * (((side.bind fun x₀ =>
          fiberHybridAcceptDist f x₀ evaluate pol n d γ_core r.val n_offset m coinLen m
            hm_le) true).toReal -
        ((side.bind fun x₀ =>
          fiberHybridAcceptDist f x₀ evaluate pol n d γ_core r.val n_offset m coinLen 0
            (by omega)) true).toReal) ≤
      (m : ℝ) * (1 / (GoldreichLevin.precision deg k : ℝ) +
        2 * Real.sqrt (1 / (2 : ℝ) ^ (d * Nat.log 2 k))) +
      (2 : ℝ) ^ (m + 1) * (dyadicSize m : ℝ) *
        (dyadicSize (coreSeedLen imgLen d γ_core (k + 1)) : ℝ) *
        (dyadicSize (k + 1) : ℝ) * (k + 1 : ℝ) *
        (Game.succProbability (ProbComp.eval
          (inversionGame g
            (condInverter g imgLen evaluate d γ_core γ c_eval d_eval deg) k)) : ℝ) := by
  subst hn_eq
  intro m coinLen side
  let n := coreSeedLen imgLen d γ_core k + n_offset
  let invX (x₀ : BitString k) : ℝ :=
    (((ProbComp.eval (condInverter g imgLen evaluate d γ_core γ c_eval d_eval deg
      k (List.ofFn (f x₀)))).map (fun w => decide (g w = List.ofFn (f x₀)))) true).toReal
  let W : ℝ := (2 : ℝ) ^ (m + 1) * (dyadicSize m : ℝ) *
    (dyadicSize (coreSeedLen imgLen d γ_core (k + 1)) : ℝ) * (dyadicSize (k + 1) : ℝ)
  refine (two_mul_bind_sub_toReal_le side
    (fun x₀ => fiberHybridAcceptDist f x₀ evaluate pol n d γ_core r.val n_offset m coinLen m hm_le)
    (fun x₀ => fiberHybridAcceptDist f x₀ evaluate pol n d γ_core r.val n_offset m coinLen 0
      (by omega))
    ((m : ℝ) * (1 / (GoldreichLevin.precision deg k : ℝ) +
      2 * Real.sqrt (1 / (2 : ℝ) ^ (d * Nat.log 2 k)))) W invX fun x₀ ha => by
    have hx₀ : x₀ ∈ regularityBucket f r := by
      by_contra hnot
      exact ha (by simp only [side, PMF.uniformOfFinset_apply, hnot, ↓reduceIte])
    have htot := fiberHybrid_total_le g imgLen f hf x₀ evaluate pol d γ_core γ c_eval d_eval deg
      r.val n_offset r.isLt.le hn_off_le hm_le
    have hfib_err :
        (if l2Val d k r.val = 0 then 0 else
          2 * Real.sqrt ((2 : ℝ) ^ (l2Val d k r.val) /
            Nat.card {x : BitString k // f x = f x₀})) ≤
        2 * Real.sqrt (1 / (2 : ℝ) ^ (d * Nat.log 2 k)) :=
      sqrt_l2Val_fiber_le (by norm_num) hgap
        (by exact_mod_cast (card_fiber_of_mem_regularityBucket f r hx₀).1)
    have hm_err := mul_le_mul_of_nonneg_left
      (add_le_add_left hfib_err (1 / (GoldreichLevin.precision deg k : ℝ)))
      (Nat.cast_nonneg (α := ℝ) m)
    dsimp only [W, invX, m, n, coinLen] at htot hm_err ⊢
    linarith).trans ?_
  have hbucket_le := sum_uniformOfFinset_le_mul_uniformOfFintype (regularityBucket f r) hS hdense
    invX (fun _ => ENNReal.toReal_nonneg)
  rw [← inversionGame_succProbability_eq g f hf
    (condInverter g imgLen evaluate d γ_core γ c_eval d_eval deg)] at hbucket_le
  have hmul_W := mul_le_mul_of_nonneg_left hbucket_le (by positivity : 0 ≤ W)
  dsimp only [W, side] at hmul_W ⊢
  linarith

private theorem bind_fiberHybridAcceptDist_eq {k imgLen_k : ℕ}
    (f : BitString k → BitString imgLen_k) (r : Fin (k + 1))
    (hS : (regularityBucket f r).Nonempty)
    (evaluate : (ℕ × List Bool) → List Bool → Bool) (pol : Bool)
    (n d γ_core padLen m coinLen j : ℕ)
    (hlen : l2Val d k r.val + j ≤ h2Rows d γ_core k) :
    ((PMF.uniformOfFinset (regularityBucket f r) hS).bind fun x₀ =>
      fiberHybridAcceptDist f x₀ evaluate pol n d γ_core r.val padLen m coinLen j hlen) =
    (PMF.uniformOfFinset (regularityBucket f r) hS).bind fun x =>
      (BitString.uniformList padLen).bind fun pad =>
        (BitString.uniformList (k * imgLen_k)).bind fun h1 =>
          (BitString.uniformList (m - j)).bind fun z_tail =>
            (BitString.uniformList coinLen).bind fun coins =>
              (PMF.uniformOfFintype (BitString (h2Rows d γ_core k * k))).map fun h2 =>
                (evaluate (n, pad ++ h1 ++
                  LinearHash.wordHash (l1Val d k r.val) h1 (List.ofFn (f x)) ++
                  List.ofFn h2 ++
                  List.ofFn (LinearHash.hash (block h2 ∘ Fin.castLE hlen) x) ++
                  z_tail) coins) ^^ pol := by
  have (x₀ : BitString k) : Nonempty {x : BitString k // f x = f x₀} := ⟨⟨x₀, rfl⟩⟩
  conv_rhs => rw [← bind_regularityBucket_fiber_eq f r hS]
  simp only [fiberHybridAcceptDist, pmf_norm,
    ← PMF.uniformOfFintype_map_equiv (blocksEquiv (m := h2Rows d γ_core k) (k := k))]
  congr 1; funext x₀
  pmf_swap with x pad h1 z_tail coins h2
  rw [x.property, Equiv.symm_apply_apply]
  rfl

/-- Extend a core LHL tuple `(h1, d1, h2, d2)` with random `pad`, `z_tail`, and `coins` and
evaluate the twisted distinguisher. -/
private noncomputable def evalCore {k imgLen_k m1 m2 c2 : ℕ}
    (evaluate : (ℕ × List Bool) → List Bool → Bool) (pol : Bool)
    (n padLen m coinLen : ℕ)
    (c : (BitString (k * imgLen_k) × BitString m1) × (BitString (c2 * k) × BitString m2)) :
    PMF Bool := do
  let pad ← BitString.uniformList padLen
  let z_tail ← BitString.uniformList m
  (BitString.uniformList coinLen).map fun coins =>
    (evaluate (n, pad ++ List.ofFn c.1.1 ++ List.ofFn c.1.2 ++
      List.ofFn c.2.1 ++ List.ofFn c.2.2 ++ z_tail) coins) ^^ pol

/-- At hybrid step `j = 0`, averaging `fiberHybridAcceptDist` over $S_{k, r}$ equals
`coreLHLDist` bound to `evalCore`. -/
private theorem bind_fiberHybridAcceptDist_zero_eq {k imgLen_k : ℕ}
    (f : BitString k → BitString imgLen_k) (r : Fin (k + 1))
    (hS : (regularityBucket f r).Nonempty)
    (evaluate : (ℕ × List Bool) → List Bool → Bool) (pol : Bool)
    (n d γ_core padLen m coinLen : ℕ)
    (hlen0 : l2Val d k r.val + 0 ≤ h2Rows d γ_core k) :
    ((PMF.uniformOfFinset (regularityBucket f r) hS).bind fun x₀ =>
      fiberHybridAcceptDist f x₀ evaluate pol n d γ_core r.val padLen m coinLen 0 hlen0) =
    (coreLHLDist f r hS (l1Val_le d k r.val) (l2Val_le_h2Rows d γ_core k r.val)).bind
      (evalCore evaluate pol n padLen m coinLen) := by
  rw [bind_fiberHybridAcceptDist_eq]
  unfold coreLHLDist evalCore
  simp only [pmf_norm, Nat.sub_zero, BitString.uniformList]
  pmf_swap with x h1 h2 pad z_tail coins
  have hw := wordHash_ofFn_prefix (l1Val_le d k r.val) h1 (f x)
  simp only [Function.comp_def] at hw ⊢
  rw [hw]
  rfl

/-- Binding `unifCoreDist` to `evalCore` yields the ideal uniform challenge distribution of length
`L = padLen + k * imgLen_k + m1 + c2 * k + m2 + m`. -/
private theorem unifCoreDist_bind_evalCore_eq (k imgLen_k m1 m2 c2 : ℕ)
    (evaluate : (ℕ × List Bool) → List Bool → Bool) (pol : Bool)
    (n padLen m coinLen L : ℕ)
    (hL : padLen + k * imgLen_k + m1 + c2 * k + m2 + m = L) :
    (unifCoreDist k imgLen_k m1 m2 c2).bind (evalCore evaluate pol n padLen m coinLen) =
      (BitString.uniformList L).bind fun y =>
        (BitString.uniformList coinLen).map fun coins => (evaluate (n, y) coins) ^^ pol := by
  have hstep :
      (unifCoreDist k imgLen_k m1 m2 c2).bind (evalCore evaluate pol n padLen m coinLen) =
      (((unifCoreDist k imgLen_k m1 m2 c2).bind fun c =>
        (PMF.uniformOfFintype (BitString padLen)).map fun pad =>
          List.ofFn pad ++ List.ofFn c.1.1 ++ List.ofFn c.1.2 ++
            List.ofFn c.2.1 ++ List.ofFn c.2.2).bind fun prefix_word =>
        (BitString.uniformList m).map fun z_tail => prefix_word ++ z_tail).bind fun y =>
          (BitString.uniformList coinLen).map fun coins => (evaluate (n, y) coins) ^^ pol := by
    unfold evalCore
    simp only [BitString.uniformList, pmf_norm]
  rw [hstep, unifCoreDist_bind_pad_append, ← BitString.uniformList_add, hL]

/-- At hybrid step `j = mActual d γ k n`, averaging `fiberHybridAcceptDist` over $S_{k, r(k)}$
equals the real conditional generator output distribution on `condSeedSet` fed into the twisted
distinguisher. -/
private theorem bind_fiberHybridAcceptDist_top_eq (g : List Bool → List Bool) (imgLen : ℕ → ℕ)
    (d γ_core γ : ℕ) (S : ∀ k, Finset (BitString k)) (hS : ∀ k, (S k).Nonempty)
    (r : ∀ k, Fin (k + 1))
    (evaluate : (ℕ × List Bool) → List Bool → Bool) (pol : Bool)
    {n k coinLen : ℕ}
    (hk : k = GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n)
    (hfits : coreSeedLen imgLen d γ_core k ≤ n)
    (hk_2d : 2 * (d * Nat.log 2 k) ≤ k)
    (hf : ∀ x : BitString k, g (List.ofFn x) = List.ofFn (ofList (imgLen k) (g (List.ofFn x))))
    (hS_eq : S k = regularityBucket
      (fun x : BitString k => ofList (imgLen k) (g (List.ofFn x))) (r k))
    (hm_le : l2Val d k (r k).val + mActual d γ k n ≤ h2Rows d γ_core k) :
    let f (x : BitString k) : BitString (imgLen k) := ofList (imgLen k) (g (List.ofFn x))
    ((PMF.uniformOfFinset (regularityBucket f (r k)) (hS_eq ▸ hS k)).bind fun x₀ =>
      fiberHybridAcceptDist f x₀ evaluate pol n d γ_core (r k).val
        (n - coreSeedLen imgLen d γ_core k) (mActual d γ k n) coinLen (mActual d γ k n) hm_le) =
    ((PMF.uniformOfFinset (condSeedSet imgLen d γ_core S r n)
      (condSeedSet_nonempty imgLen d γ_core S hS r n)).map List.ofFn).bind fun seed =>
        (BitString.uniformList coinLen).map fun coins =>
          (evaluate (n, fullGen g imgLen d γ_core γ seed) coins) ^^ pol := by
  subst hk
  set k := GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n
  intro f
  rw [bind_fiberHybridAcceptDist_eq,
    uniformOfFinset_condSeedSet_map_ofFn imgLen d γ_core S hS r rfl hfits (hS_eq ▸ hS k) hS_eq]
  rw [Nat.sub_self, BitString.uniformList_zero]
  simp only [pmf_norm, BitString.uniformList]
  congr 1; funext x
  pmf_swap with h1 h2 pad coins
  rw [List.append_nil, fullGen_packSeedWords g imgLen d γ_core γ n (r k).val
    (Nat.le_of_lt_succ (r k).isLt) hfits hk_2d (x, h1, h2, pad),
    hf x, wordHash_ofFn_prefix hm_le h2 x]
  rfl

private theorem pow_le_two_pow_two_mul_log (B : ℕ) {k : ℕ} (hk : 2 ≤ k) :
    k ^ B ≤ 2 ^ (2 * B * Nat.log 2 k) := by
  have hlog : 1 ≤ Nat.log 2 k := Nat.le_log_of_pow_le Nat.one_lt_two hk
  have hk_le : k ≤ 2 ^ (2 * Nat.log 2 k) :=
    (Nat.lt_pow_succ_log_self Nat.one_lt_two k).le.trans
      (Nat.pow_le_pow_right Nat.zero_lt_two (by omega))
  calc
    k ^ B ≤ (2 ^ (2 * Nat.log 2 k)) ^ B := Nat.pow_le_pow_left hk_le B
    _ = 2 ^ (2 * B * Nat.log 2 k) := by rw [← pow_mul]; ring_nf

private theorem log_le_two_mul_log_of_le_pow {E k n : ℕ} (hk : 2 ≤ k) (hn : n ≤ k ^ E) :
    Nat.log 2 n ≤ 2 * E * Nat.log 2 k := by
  have hle : n ≤ 2 ^ (2 * E * Nat.log 2 k) := hn.trans (pow_le_two_pow_two_mul_log E hk)
  exact (Nat.log_mono_right hle).trans_eq (Nat.log_pow Nat.one_lt_two _)

private theorem dist_bool_le_of_xor_sub_le (P₁ P₂ : PMF Bool) (B : ℝ)
    (h : ∀ pol : Bool,
      ((P₁.map (fun b => b ^^ pol)) true).toReal -
        ((P₂.map (fun b => b ^^ pol)) true).toReal ≤ B) :
    dist P₁ P₂ ≤ B := by
  have hfalse : (P₁ true).toReal - (P₂ true).toReal ≤ B := by
    simpa only [Bool.xor_false, show (fun b : Bool => b) = id from rfl, PMF.map_id] using h false
  have htrue : (1 - (P₁ true).toReal) - (1 - (P₂ true).toReal) ≤ B := by
    simpa only [Bool.xor_true, PMF.map_apply, tsum_fintype, Fintype.sum_bool,
      Bool.not_true, Bool.not_false, Bool.true_eq_false, reduceIte, add_zero, zero_add,
      PMF.toReal_false_eq_one_sub] using h true
  rw [dist_bool, abs_sub_le_iff]
  exact ⟨hfalse, by linarith⟩

private theorem length_encPair_le_condCoinBudget (c_eval d_eval γ n : ℕ) {w : List Bool}
    (hw : w.length = n + γ * Nat.log 2 n) :
    c_eval * ((encPair encUnary encBits (n, w)).length + 1) ^ d_eval ≤
      condCoinBudget c_eval d_eval γ n := by
  unfold condCoinBudget
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  enc_len [hw]

/-- Combined conditional PRG distinguishing bound at seed length `n`:
bounds the advantage of `adversary n` between `fullGen` on `condSeedSet` and `uniformList` by the
sum of the LHL core error, the Goldreich–Levin precision error, the prefix fiber hash error, and
the `condInverter` success probability. -/
private theorem dist_condSeedSet_uniform_le (g : List Bool → List Bool) (imgLen : ℕ → ℕ)
    (d γ_core γ c_eval d_eval deg : ℕ)
    (S : ∀ k, Finset (BitString k)) (hS : ∀ k, (S k).Nonempty)
    (r : ∀ k, Fin (k + 1))
    (evaluate : (ℕ × List Bool) → List Bool → Bool)
    (adversary : Distinguisher)
    (hlaw : ∀ (a : ℕ × List Bool) length,
      c_eval * ((encPair encUnary encBits a).length + 1) ^ d_eval ≤ length →
      ProbComp.eval (adversary a.1 a.2) = (BitString.uniformList length).map (evaluate a))
    {n k : ℕ}
    (hk : k = GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n)
    (hfits : coreSeedLen imgLen d γ_core k ≤ n)
    (hlt_next : n < coreSeedLen imgLen d γ_core (k + 1))
    (hk_2d : 2 * (d * Nat.log 2 k) ≤ k)
    (hgap : (r k).val + d * Nat.log 2 k ≤ k)
    (hm_le : l2Val d k (r k).val + mActual d γ k n ≤ h2Rows d γ_core k)
    (hf : ∀ x : BitString k, g (List.ofFn x) = List.ofFn (ofList (imgLen k) (g (List.ofFn x))))
    (hS_eq : S k = regularityBucket
      (fun x : BitString k => ofList (imgLen k) (g (List.ofFn x))) (r k))
    (hdense : 2 ^ k ≤ (k + 1) *
      (regularityBucket (fun x : BitString k => ofList (imgLen k) (g (List.ofFn x))) (r k)).card) :
    let m := mActual d γ k n
    (Game.advantage
      ((((PMF.uniformOfFinset (condSeedSet imgLen d γ_core S r n)
        (condSeedSet_nonempty imgLen d γ_core S hS r n)).map List.ofFn).map
          (fullGen g imgLen d γ_core γ)).bind fun y => ProbComp.eval (adversary n y))
      ((BitString.uniformList (n + γ * Nat.log 2 n)).bind
        fun y => ProbComp.eval (adversary n y)) : ℝ) ≤
      Real.sqrt (2 * (k + 1 : ℝ) / (2 : ℝ) ^ (d * Nat.log 2 k)) +
      (m : ℝ) / (2 * (GoldreichLevin.precision deg k : ℝ)) +
      (m : ℝ) * Real.sqrt (1 / (2 : ℝ) ^ (d * Nat.log 2 k)) +
      (1 / 2) * (2 : ℝ) ^ (m + 1) * (dyadicSize m : ℝ) *
        (dyadicSize (coreSeedLen imgLen d γ_core (k + 1)) : ℝ) *
        (dyadicSize (k + 1) : ℝ) * (k + 1 : ℝ) *
        (Game.succProbability (ProbComp.eval
          (inversionGame g
            (condInverter g imgLen evaluate d γ_core γ c_eval d_eval deg) k)) : ℝ) := by
  subst hk
  set k := GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n
  intro m
  let f (x : BitString k) : BitString (imgLen k) := ofList (imgLen k) (g (List.ofFn x))
  let hS_reg : (regularityBucket f (r k)).Nonempty := hS_eq ▸ hS k
  let n_offset := n - coreSeedLen imgLen d γ_core k
  let coinLen := condCoinBudget c_eval d_eval γ n
  let P₁ : PMF Bool :=
    ((PMF.uniformOfFinset (condSeedSet imgLen d γ_core S r n)
      (condSeedSet_nonempty imgLen d γ_core S hS r n)).map List.ofFn).bind fun seed =>
        (BitString.uniformList coinLen).map (evaluate (n, fullGen g imgLen d γ_core γ seed))
  let P₂ : PMF Bool :=
    (BitString.uniformList (n + γ * Nat.log 2 n)).bind fun y =>
      (BitString.uniformList coinLen).map (evaluate (n, y))
  rw [show ((((PMF.uniformOfFinset (condSeedSet imgLen d γ_core S r n)
        (condSeedSet_nonempty imgLen d γ_core S hS r n)).map List.ofFn).map
          (fullGen g imgLen d γ_core γ)).bind fun y => ProbComp.eval (adversary n y)) = P₁ by
      simp only [P₁, PMF.bind_map, Function.comp_def]
      exact congrArg _ (funext fun x => hlaw _ coinLen
        (length_encPair_le_condCoinBudget c_eval d_eval γ n
          ((length_fullGen _ _ _ _ _ _).trans (by rw [List.length_ofFn])))),
    show ((BitString.uniformList (n + γ * Nat.log 2 n)).bind
        fun y => ProbComp.eval (adversary n y)) = P₂ by
      simp only [P₂, BitString.uniformList, PMF.bind_map, Function.comp_def]
      exact congrArg _ (funext fun y => hlaw _ coinLen
        (length_encPair_le_condCoinBudget c_eval d_eval γ n List.length_ofFn)),
    Game.advantage_eq_nndist, coe_nndist]
  refine dist_bool_le_of_xor_sub_le P₁ P₂ _ fun pol => ?_
  have hP₁ : P₁.map (· ^^ pol) =
      (PMF.uniformOfFinset (regularityBucket f (r k)) hS_reg).bind fun x₀ =>
        fiberHybridAcceptDist f x₀ evaluate pol n d γ_core (r k).val n_offset m
          coinLen m hm_le := by
    rw [bind_fiberHybridAcceptDist_top_eq g imgLen d γ_core γ S hS r evaluate pol
      rfl hfits hk_2d hf hS_eq hm_le]
    simp only [P₁, pmf_norm]
  have hL : n_offset + k * imgLen k + l1Val d k (r k).val + h2Rows d γ_core k * k +
      l2Val d k (r k).val + m = n + γ * Nat.log 2 n := by
    have h1 := lhlPrefixLen_split imgLen d γ_core (r k).val hfits hk_2d
    have hcs : coreSeedLen imgLen d γ_core k =
        (Nat.log 2 k + 1) + k + k * imgLen k + h2Rows d γ_core k * k := rfl
    have h3 := lhlPrefixLen_add_mActual (γ := γ) (d := d) (k := k) (n := n) (by omega)
    dsimp only [m, n_offset] at h1 h3 ⊢; omega
  have hlen0 : l2Val d k (r k).val + 0 ≤ h2Rows d γ_core k :=
    (Nat.add_zero _).le.trans (l2Val_le_h2Rows d γ_core k (r k).val)
  let P₀ : PMF Bool :=
    (PMF.uniformOfFinset (regularityBucket f (r k)) hS_reg).bind fun x₀ =>
      fiberHybridAcceptDist f x₀ evaluate pol n d γ_core (r k).val n_offset m coinLen 0 hlen0
  have hdist_core : (P₀ true).toReal - ((P₂.map (· ^^ pol)) true).toReal ≤
      Real.sqrt (2 * (k + 1 : ℝ) / (2 : ℝ) ^ (d * Nat.log 2 k)) := by
    refine ((le_abs_self _).trans_eq (dist_bool P₀ _).symm).trans ?_
    rw [show P₀ = (coreLHLDist f (r k) hS_reg (l1Val_le d k (r k).val)
        (l2Val_le_h2Rows d γ_core k (r k).val)).bind (evalCore evaluate pol n n_offset m coinLen)
      from bind_fiberHybridAcceptDist_zero_eq f (r k) hS_reg evaluate pol n d γ_core n_offset m
        coinLen hlen0,
      show P₂.map (· ^^ pol) = (unifCoreDist k (imgLen k) (l1Val d k (r k).val)
        (l2Val d k (r k).val) (h2Rows d γ_core k)).bind (evalCore evaluate pol n n_offset m coinLen)
      by rw [unifCoreDist_bind_evalCore_eq _ _ _ _ _ _ _ _ _ _ _ _ hL]; simp only [P₂, pmf_norm]]
    exact (PMF.dist_bind_le _ _ _).trans
      (dist_coreLHLDist_unifCoreDist_le_of_gap f (r k) hS_reg hdense hgap)
  have hbucket := bucketHybrid_total_le g imgLen f hf (r k) hS_reg hdense evaluate pol
    d γ_core γ c_eval d_eval deg n_offset n (Nat.add_sub_of_le hfits) hgap
    (by dsimp [n_offset]; omega) hm_le
  dsimp only [m, coinLen] at hbucket ⊢
  rw [hP₁]
  linarith [show (m : ℝ) * (1 / (GoldreichLevin.precision deg k : ℝ) +
      2 * Real.sqrt (1 / (2 : ℝ) ^ (d * Nat.log 2 k))) =
      2 * ((m : ℝ) / (2 * (GoldreichLevin.precision deg k : ℝ)) +
        (m : ℝ) * Real.sqrt (1 / (2 : ℝ) ^ (d * Nat.log 2 k))) by ring]

/-! ### Theorem 5.5: Existence of a conditional entropy-preserving PRG from any OWF -/

private theorem eventually_coreSeedLen_succ_le_pow {imgLen : ℕ → ℕ} {c_i d_i : ℕ}
    (himg : ∀ k, imgLen k ≤ c_i * (k + 1) ^ d_i) (d γ_core : ℕ) :
    ∀ᶠ k : ℕ in atTop, coreSeedLen imgLen d γ_core (k + 1) ≤ k ^ (d_i + 4) := by
  filter_upwards [eventually_ge_atTop (max 8 (c_i * 2 ^ d_i + 2 * d + γ_core + 4))] with k hk
  have hk8 : 8 ≤ k := le_trans (le_max_left _ _) hk
  have hkM : c_i * 2 ^ d_i + 2 * d + γ_core + 4 ≤ k := le_trans (le_max_right _ _) hk
  have hlog : Nat.log 2 (k + 1) ≤ k + 1 := Nat.log_le_self 2 (k + 1)
  have himg_k1 : imgLen (k + 1) ≤ k ^ (d_i + 1) := calc
    imgLen (k + 1) ≤ c_i * (k + 2) ^ d_i := himg (k + 1)
    _ ≤ c_i * (2 * k) ^ d_i := by gcongr; omega
    _ = c_i * 2 ^ d_i * k ^ d_i := by rw [mul_pow]; ring
    _ ≤ k * k ^ d_i := by gcongr; omega
    _ = k ^ (d_i + 1) := (pow_succ' k d_i).symm
  have hh2 : h2Rows d γ_core (k + 1) ≤ 2 * k ^ 2 := by
    have hd := Nat.mul_le_mul_left d hlog
    have hγ := Nat.mul_le_mul_left γ_core hlog
    have hlin : h2Rows d γ_core (k + 1) ≤ (2 * d + γ_core + 3) * (k + 1) := by
      rw [show (2 * d + γ_core + 3) * (k + 1) =
        2 * (d * (k + 1)) + γ_core * (k + 1) + 3 * (k + 1) by ring]
      unfold h2Rows mMax; omega
    exact hlin.trans <| (Nat.mul_le_mul (by omega : 2 * d + γ_core + 3 ≤ k)
      (by omega : k + 1 ≤ 2 * k)).trans_eq (by ring)
  have hpow2 : k ^ (d_i + 2) ≤ k ^ (d_i + 3) := Nat.pow_le_pow_right (by omega) (by omega)
  have hpow3 : k ^ 3 ≤ k ^ (d_i + 3) := Nat.pow_le_pow_right (by omega) (by omega)
  have hsq : 8 * k ≤ k ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right k hk8
  have hpow_sq : k ^ 2 ≤ k ^ (d_i + 3) := Nat.pow_le_pow_right (by omega) (by omega)
  calc coreSeedLen imgLen d γ_core (k + 1)
      ≤ 2 * k ^ (d_i + 3) + (2 * k) * k ^ (d_i + 1) + (2 * k ^ 2) * (2 * k) := by
        unfold coreSeedLen regWidth; gcongr <;> omega
    _ = 2 * k ^ (d_i + 3) + 2 * k ^ (d_i + 2) + 4 * k ^ 3 := by
        rw [show 2 * k * k ^ (d_i + 1) = 2 * k ^ (d_i + 2) by rw [pow_succ']; ring]; ring
    _ ≤ k * k ^ (d_i + 3) := (by omega : _ ≤ 8 * k ^ (d_i + 3)).trans (Nat.mul_le_mul_right _ hk8)
    _ = k ^ (d_i + 4) := (pow_succ' k (d_i + 3)).symm

private theorem sqrt_lhl_err_le {E δ k n : ℕ} (hk : 8 ≤ k) (hn_pos : 1 ≤ n) (hn : n ≤ k ^ E) :
    let d := 2 * (E * (2 * δ + 4) + 4)
    Real.sqrt (2 * (k + 1 : ℝ) / (2 : ℝ) ^ (d * Nat.log 2 k)) ≤
      1 / (4 * (n : ℝ) ^ (δ + 2)) := by
  intro d
  have hk_sq : 8 * k ≤ k ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right k hk
  have hnat : 2 * (k + 1) * (16 * n ^ (2 * δ + 4)) ≤ 2 ^ (d * Nat.log 2 k) := calc
    2 * (k + 1) * (16 * n ^ (2 * δ + 4))
      ≤ k ^ 2 * (k ^ 2 * (k ^ E) ^ (2 * δ + 4)) := by gcongr <;> omega
    _ = k ^ (E * (2 * δ + 4) + 4) := by rw [← pow_mul]; simp only [pow_add]; ring
    _ ≤ 2 ^ (d * Nat.log 2 k) := by
        simpa only [d, mul_assoc] using pow_le_two_pow_two_mul_log _ (by omega : 2 ≤ k)
  have hn_rpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
  refine (Real.sqrt_le_sqrt ?_).trans_eq (Real.sqrt_sq (by positivity))
  rw [div_pow, one_pow, div_le_div_iff₀ (by positivity) (by positivity), one_mul,
    show (4 * (n : ℝ) ^ (δ + 2)) ^ 2 = 16 * (n : ℝ) ^ (2 * δ + 4) by ring]
  exact_mod_cast hnat

private theorem gl_err_le {E δ k n m : ℕ} (hk : 8 ≤ k) (hn_pos : 1 ≤ n) (hn : n ≤ k ^ E)
    (hm : m ≤ n ^ 2) :
    let deg := E * (δ + 2) + 2
    (m : ℝ) / (2 * (GoldreichLevin.precision deg k : ℝ)) ≤ 1 / (4 * (n : ℝ) ^ δ) := by
  intro deg
  have hnat : 4 * n ^ δ * m ≤ 2 * GoldreichLevin.precision deg k := calc
    4 * n ^ δ * m ≤ 4 * n ^ δ * n ^ 2 := by gcongr
    _ = 4 * n ^ (δ + 2) := by rw [pow_add]; ring
    _ ≤ k ^ 2 * (k ^ E) ^ (δ + 2) := by
        gcongr; exact (by omega : 4 ≤ k).trans (Nat.le_self_pow two_ne_zero k)
    _ = k ^ deg := by rw [← pow_mul]; dsimp [deg]; rw [pow_add]; ring
    _ ≤ 2 * (k + 1) ^ deg :=
        (Nat.pow_le_pow_left (by omega) _).trans (Nat.le_mul_of_pos_left _ two_pos)
  have hn_rpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
  have := GoldreichLevin.precision_pos deg k
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, mul_comm]
  exact_mod_cast hnat

private theorem inv_term_le {E δ d γ_core k n m cs_succ : ℕ} {succProb : ℝ}
    (hk : 2 * d + γ_core + 8 ≤ k) (hn_pos : 1 ≤ n) (hn : n ≤ k ^ E)
    (hcs : cs_succ ≤ k ^ E) (hm : m ≤ mMax d γ_core k) (hsucc_nonneg : 0 ≤ succProb)
    (hsucc : succProb ≤
      1 / ((k + 1 : ℝ) ^ ((2 * d + γ_core + 2) + 3 + (E + 1) + 2 + 2 + E * δ))) :
    (1 / 2) * (2 : ℝ) ^ (m + 1) * (dyadicSize m : ℝ) *
      (dyadicSize cs_succ : ℝ) * (dyadicSize (k + 1) : ℝ) * (k + 1 : ℝ) * succProb ≤
      1 / (4 * (n : ℝ) ^ δ) := by
  let D_inv := (2 * d + γ_core + 2) + 3 + (E + 1) + 2 + 2 + E * δ
  have hk_sq : 8 * k ≤ k ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right k (by omega)
  have hm' : m ≤ (2 * d + γ_core + 1) * Nat.log 2 k + 1 := by
    rw [show (2 * d + γ_core + 1) * Nat.log 2 k =
      2 * (d * Nat.log 2 k) + γ_core * Nat.log 2 k + Nat.log 2 k by ring]
    unfold mMax at hm; omega
  have h1 : 2 ^ (m + 1) ≤ k ^ (2 * d + γ_core + 2) := calc
    2 ^ (m + 1) ≤ 2 ^ ((2 * d + γ_core + 1) * Nat.log 2 k + 2) :=
      Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
    _ = 4 * 2 ^ ((2 * d + γ_core + 1) * Nat.log 2 k) := by rw [pow_add]; ring
    _ ≤ k * k ^ (2 * d + γ_core + 1) :=
      Nat.mul_le_mul (by omega) (two_pow_mul_log_le_pow _ (by omega))
    _ = k ^ (2 * d + γ_core + 2) := (pow_succ' k _).symm
  have h2 : dyadicSize m ≤ k ^ 3 := by
    have := Nat.mul_le_mul_left (2 * d + γ_core + 1) (Nat.log_le_self 2 k)
    have := Nat.mul_le_mul_right k (by omega : 2 * d + γ_core + 1 ≤ k)
    have : 4 ≤ k * k := Nat.mul_le_mul (by omega : 2 ≤ k) (by omega : 2 ≤ k)
    have : 4 * (k * k) ≤ k ^ 3 := by
      rw [pow_succ' k 2, sq]; exact Nat.mul_le_mul_right _ (by omega)
    have := dyadicSize_le m
    omega
  have h3 : dyadicSize cs_succ ≤ k ^ (E + 1) := by
    have : 1 ≤ k ^ E := Nat.one_le_pow E k (by omega)
    exact (dyadicSize_le cs_succ).trans <|
      (by omega : 2 * (cs_succ + 1) ≤ 4 * k ^ E).trans <|
        (Nat.mul_le_mul_right _ (by omega : 4 ≤ k)).trans_eq (pow_succ' k E).symm
  have h4 : dyadicSize (k + 1) ≤ k ^ 2 := (dyadicSize_le _).trans (by omega)
  let P_nat := 2 ^ (m + 1) * dyadicSize m * dyadicSize cs_succ * dyadicSize (k + 1) * (k + 1)
  have hprod_nat : P_nat * (4 * n ^ δ) ≤ (k + 1) ^ D_inv := calc
    P_nat * (4 * n ^ δ)
      = 2 ^ (m + 1) * dyadicSize m * dyadicSize cs_succ * dyadicSize (k + 1) *
          (4 * (k + 1)) * n ^ δ := by dsimp [P_nat]; ring
    _ ≤ k ^ (2 * d + γ_core + 2) * k ^ 3 * k ^ (E + 1) * k ^ 2 * k ^ 2 * (k ^ E) ^ δ := by
        gcongr; omega
    _ = k ^ D_inv := by rw [← pow_mul]; simp only [D_inv, pow_add]
    _ ≤ (k + 1) ^ D_inv := Nat.pow_le_pow_left (by omega) D_inv
  calc (1 / 2) * (2 : ℝ) ^ (m + 1) * (dyadicSize m : ℝ) * (dyadicSize cs_succ : ℝ) *
        (dyadicSize (k + 1) : ℝ) * (k + 1 : ℝ) * succProb
      = (1 / 2) * (P_nat : ℝ) * succProb := by dsimp [P_nat]; push_cast; ring
    _ ≤ (P_nat : ℝ) * (1 / (k + 1 : ℝ) ^ D_inv) :=
        (mul_le_mul_of_nonneg_right (by linarith) hsucc_nonneg).trans
          (mul_le_mul_of_nonneg_left hsucc (Nat.cast_nonneg _))
    _ ≤ 1 / (4 * (n : ℝ) ^ δ) := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
        exact_mod_cast hprod_nat

private theorem coreSeedLen_parameter_bounds {imgLen : ℕ → ℕ} {d γ_core E n k : ℕ}
    (hk : k = GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n)
    (hn0 : coreSeedLen imgLen d γ_core 0 ≤ n)
    (hcs_pow : coreSeedLen imgLen d γ_core (k + 1) ≤ k ^ E) :
    coreSeedLen imgLen d γ_core k ≤ n ∧
      n < coreSeedLen imgLen d γ_core (k + 1) ∧
      n ≤ k ^ E ∧
      k < n ∧
      1 ≤ n := by
  subst hk
  have hfits := GeneratorReindex.parameter_fits hn0
  have hlt_next :=
    GeneratorReindex.lt_length_succ_parameter (coreSeedLen_ge_succ imgLen d γ_core) n
  have hk_lt_n : GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n < n :=
    lt_of_lt_of_le (Nat.lt_succ_self _) ((coreSeedLen_ge_succ imgLen d γ_core _).trans hfits)
  exact ⟨hfits, hlt_next, hlt_next.le.trans hcs_pow, hk_lt_n, by omega⟩

private theorem fullGen_condSeedSet_advantage_le
    {g : List Bool → List Bool} {imgLen : ℕ → ℕ}
    (himgLen : ∀ x, (g x).length = imgLen x.length)
    (E δ γ d γ_core c_eval d_eval : ℕ)
    (hd : d = 2 * (E * (2 * δ + 4) + 4)) (hγ_core : γ_core = γ * (2 * E))
    (S : ∀ k, Finset (BitString k)) (hS : ∀ k, (S k).Nonempty) (r : ∀ k, Fin (k + 1))
    (hS_eq : ∀ k,
      S k = regularityBucket (fun x : BitString k => ofList (imgLen k) (g (List.ofFn x))) (r k))
    (hdense : ∀ k, 2 ^ k ≤ (k + 1) * (S k).card)
    (evaluate : (ℕ × List Bool) → List Bool → Bool) (adversary : Distinguisher)
    (hlaw : ∀ (a : ℕ × List Bool) length,
      c_eval * ((encPair encUnary encBits a).length + 1) ^ d_eval ≤ length →
      ProbComp.eval (adversary a.1 a.2) = (BitString.uniformList length).map (evaluate a))
    {n k : ℕ} (hk_eq : k = GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n)
    (hn0 : coreSeedLen imgLen d γ_core 0 ≤ n)
    (hk_min : 2 * d + γ_core + γ + 8 ≤ k)
    (hk_2d : 2 * (d * Nat.log 2 k) ≤ k)
    (hgap : (r k).val + d * Nat.log 2 k ≤ k)
    (hcs_pow : coreSeedLen imgLen d γ_core (k + 1) ≤ k ^ E)
    (hinv_le : (Game.succProbability (ProbComp.eval
      (inversionGame g (condInverter g imgLen evaluate d γ_core γ c_eval d_eval
        (E * (δ + 2) + 2)) k)) : ℝ) ≤
      1 / ((k + 1 : ℝ) ^ ((2 * d + γ_core + 2) + 3 + (E + 1) + 2 + 2 + E * δ))) :
    (Game.advantage
      ((((PMF.uniformOfFinset (condSeedSet imgLen d γ_core S r n)
        (condSeedSet_nonempty imgLen d γ_core S hS r n)).map List.ofFn).map
          (fullGen g imgLen d γ_core γ)).bind fun y => ProbComp.eval (adversary n y))
      ((BitString.uniformList (n + γ * Nat.log 2 n)).bind
        fun y => ProbComp.eval (adversary n y)) : ℝ) ≤ 1 / (n : ℝ) ^ δ := by
  subst hk_eq
  set k := GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n
  obtain ⟨hfits, hlt_next, hn_le_pow, hk_lt_n, hn_pos⟩ :=
    coreSeedLen_parameter_bounds (k := k) rfl hn0 hcs_pow
  have hlog_le := log_le_two_mul_log_of_le_pow (by omega : 2 ≤ k) hn_le_pow
  have hm_le_mMax : mActual d γ k n ≤ mMax d γ_core k := mActual_le_mMax (by
    rw [hγ_core, Nat.mul_assoc]; exact Nat.mul_le_mul_left γ hlog_le)
  have hm_le : l2Val d k (r k).val + mActual d γ k n ≤ h2Rows d γ_core k := by
    have := l2Val_le d k (r k).val; unfold h2Rows; omega
  have hm_le_n2 : mActual d γ k n ≤ n ^ 2 := by
    have hcs : coreSeedLen imgLen d γ_core k =
        (Nat.log 2 k + 1) + k + k * imgLen k + h2Rows d γ_core k * k := rfl
    have hγ_log := Nat.mul_le_mul_left γ (Nat.log_le_self 2 n)
    unfold mActual
    calc _ ≤ (γ + 1) * n := by
          rw [show (γ + 1) * n = γ * n + n by ring]; omega
      _ ≤ n * n := Nat.mul_le_mul_right n (by omega)
      _ = n ^ 2 := (sq n).symm
  have hdist := dist_condSeedSet_uniform_le g imgLen d γ_core γ c_eval d_eval (E * (δ + 2) + 2)
    S hS r evaluate adversary hlaw rfl hfits hlt_next hk_2d hgap hm_le
    (fun x => (finiteFn_ofFn himgLen x).symm) (hS_eq k)
    (by rw [← hS_eq k]; exact hdense k)
  have hlhl_err : Real.sqrt (2 * (k + 1 : ℝ) / (2 : ℝ) ^ (d * Nat.log 2 k)) ≤
      1 / (4 * (n : ℝ) ^ (δ + 2)) := by
    rw [hd]; exact sqrt_lhl_err_le (δ := δ) (by omega) hn_pos hn_le_pow
  have hn_rpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
  have hterm1 : Real.sqrt (2 * (k + 1 : ℝ) / (2 : ℝ) ^ (d * Nat.log 2 k)) ≤
      1 / (4 * (n : ℝ) ^ δ) := hlhl_err.trans <| one_div_le_one_div_of_le (by positivity) <|
    mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.pow_le_pow_right hn_pos (Nat.le_add_right δ 2))
      (by norm_num)
  have hterm2 := gl_err_le (δ := δ) (by omega) hn_pos hn_le_pow hm_le_n2
  have hterm3 : (mActual d γ k n : ℝ) * Real.sqrt (1 / (2 : ℝ) ^ (d * Nat.log 2 k)) ≤
      1 / (4 * (n : ℝ) ^ δ) := by
    have hs := (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right
      (by linarith : (1 : ℝ) ≤ 2 * (k + 1 : ℝ)) (by positivity))).trans hlhl_err
    have hm_r : (mActual d γ k n : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hm_le_n2
    refine (mul_le_mul hm_r hs (by positivity) (by positivity)).trans_eq ?_
    rw [pow_add (n : ℝ) δ 2]; field_simp
  have hterm4 := inv_term_le (by omega) hn_pos hn_le_pow hcs_pow hm_le_mMax (by positivity) hinv_le
  dsimp only [k] at hdist hterm1 hterm2 hterm3 hterm4
  linarith only [hdist, hterm1, hterm2, hterm3, hterm4,
    show 4 * (1 / (4 * (n : ℝ) ^ δ)) = 1 / (n : ℝ) ^ δ by ring]

private theorem fullGen_condSeedSet_entropy_ge
    {g : List Bool → List Bool} {imgLen : ℕ → ℕ}
    (himgLen : ∀ x, (g x).length = imgLen x.length)
    (E δ γ d γ_core : ℕ) (hd : d = 2 * (E * (2 * δ + 4) + 4))
    (S : ∀ k, Finset (BitString k)) (hS : ∀ k, (S k).Nonempty) (r : ∀ k, Fin (k + 1))
    (hS_eq : ∀ k,
      S k = regularityBucket (fun x : BitString k => ofList (imgLen k) (g (List.ofFn x))) (r k))
    (hdense : ∀ k, 2 ^ k ≤ (k + 1) * (S k).card)
    {n k : ℕ} (hk_eq : k = GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n)
    (hn0 : coreSeedLen imgLen d γ_core 0 ≤ n) (hlog_n1 : 1 ≤ Nat.log 2 n)
    (hk8 : 8 ≤ k) (hk_2d : 2 * (d * Nat.log 2 k) ≤ k)
    (hgap : (r k).val + d * Nat.log 2 k ≤ k)
    (hcs_pow : coreSeedLen imgLen d γ_core (k + 1) ≤ k ^ E) :
    (n : ℝ) - ((2 * d + 4 : ℕ) : ℝ) * (Nat.log 2 n : ℝ) ≤
      PMF.entropy ((PMF.uniformOfFinset (condSeedSet imgLen d γ_core S r n)
        (condSeedSet_nonempty imgLen d γ_core S hS r n)).map fun x =>
          BitString.ofList (n + γ * Nat.log 2 n)
            (fullGen g imgLen d γ_core γ (List.ofFn x))) := by
  subst hk_eq
  set k := GeneratorReindex.parameter (coreSeedLen imgLen d γ_core) n
  let f_k (x : BitString k) : BitString (imgLen k) := ofList (imgLen k) (g (List.ofFn x))
  have hS_reg : (regularityBucket f_k (r k)).Nonempty := hS_eq k ▸ hS k
  obtain ⟨hfits, -, hn_le_pow, hk_lt_n, hn_pos⟩ :=
    coreSeedLen_parameter_bounds (k := k) rfl hn0 hcs_pow
  have hcs_def : coreSeedLen imgLen d γ_core k =
      (Nat.log 2 k + 1) + k + k * imgLen k + h2Rows d γ_core k * k := rfl
  have hh2_pos : 1 ≤ h2Rows d γ_core k * k :=
    Nat.mul_pos (by unfold h2Rows mMax; omega) (by omega)
  have hlhl_pos : 1 ≤ lhlPrefixLen d k n := by unfold lhlPrefixLen; omega
  have hlhl_le_n : lhlPrefixLen d k n ≤ n := by unfold lhlPrefixLen; omega
  have hdist_core :
      dist (coreLHLDist f_k (r k) hS_reg (l1Val_le d k (r k).val)
          (l2Val_le_h2Rows d γ_core k (r k).val))
        (unifCoreDist k (imgLen k) (l1Val d k (r k).val) (l2Val d k (r k).val)
          (h2Rows d γ_core k)) ≤ 1 / (lhlPrefixLen d k n : ℝ) ^ 2 :=
    (dist_coreLHLDist_unifCoreDist_le_of_gap f_k (r k) hS_reg (hS_eq k ▸ hdense k) hgap).trans <|
      (hd ▸ sqrt_lhl_err_le (δ := δ) hk8 hn_pos hn_le_pow).trans <|
        one_div_le_one_div_of_le (by positivity) <| by
          exact_mod_cast ((Nat.pow_le_pow_left hlhl_le_n 2).trans
            (Nat.pow_le_pow_right hn_pos (Nat.le_add_left 2 δ))).trans (by omega :
              n ^ (δ + 2) ≤ 4 * n ^ (δ + 2))
  have hent := entropy_fullGen_condSeedSet_ge g imgLen d γ_core γ S hS r rfl hfits hk_2d
    (fun x => by simp only [himgLen, List.length_ofFn]) (hS_eq k) hdist_core
  have hlog_kn_r : (Nat.log 2 k : ℝ) ≤ (Nat.log 2 n : ℝ) := by
    exact_mod_cast Nat.log_mono_right hk_lt_n.le
  refine le_trans ?_ hent
  unfold lhlPrefixLen
  rw [Nat.cast_sub (by omega : 2 * (d * Nat.log 2 k) + Nat.log 2 k + 1 ≤ n)]
  push_cast
  linarith [mul_le_mul_of_nonneg_left hlog_kn_r (Nat.cast_nonneg (α := ℝ) d),
    (by exact_mod_cast hlog_n1 : (1 : ℝ) ≤ Nat.log 2 n)]

/-- **[Liu and Pass, Theorem 5.5, §5.3, p. 15 of arXiv:2009.11514v1][LiuPass2020]: Every one-way
function yields a conditional entropy-preserving pseudorandom generator.**
For every one-way function $f : \{0, 1\}^* \to \{0, 1\}^*$ and every prescribed polynomial
security exponent $\delta \in \mathbb{N}$ and stretch constant $\gamma \in \mathbb{N}$, there
exist a deterministic polynomial-time generator $G : \{0, 1\}^* \to \{0, 1\}^*$ and an
entropy-loss constant $\alpha \in \mathbb{N}$ such that $G$ is a $(1 / n^\delta, \gamma)$-condEP-PRG
with entropy loss $\alpha$. -/
theorem OneWay.exists_condEPPRG {f : List Bool → List Bool} (hf : OneWay f) (δ γ : ℕ) :
    ∃ (G : List Bool → List Bool) (α : ℕ),
      CondEPPRG G (fun n => 1 / (n : ℝ) ^ δ) γ α := by
  obtain ⟨g, imgLen, hg, himgLen, himgLen_poly⟩ := hf.exists_fixedOutputLength
  obtain ⟨c_i, d_i, himg_raw⟩ := hg.polyTime.polyBounded_length.exists_le
  have himg_le : ∀ k, imgLen k ≤ c_i * (k + 1) ^ d_i := fun k => by
    simpa only [encBits_apply, himgLen, List.length_replicate] using
      himg_raw (List.replicate k false)
  let E := d_i + 4
  let γ_core := γ * (2 * E)
  let d := 2 * (E * (2 * δ + 4) + 4)
  let α := 2 * d + 4
  let deg := E * (δ + 2) + 2
  let f_fin (k : ℕ) (x : BitString k) : BitString (imgLen k) :=
    ofList (imgLen k) (g (List.ofFn x))
  have hbucket (k : ℕ) := exists_regularity_bucket (f_fin k)
  let r (k : ℕ) : Fin (k + 1) := (hbucket k).choose
  let S (k : ℕ) : Finset (BitString k) := regularityBucket (f_fin k) (r k)
  have hS (k : ℕ) : (S k).Nonempty := (hbucket k).choose_spec.1
  have hdense (k : ℕ) : 2 ^ k ≤ (k + 1) * (S k).card := (hbucket k).choose_spec.2.1
  have hparam_tendsto := GeneratorReindex.parameter_tendsto (coreSeedLen imgLen d γ_core)
  have hev_k_base : ∀ᶠ k : ℕ in atTop,
      (2 * d + γ_core + γ + 8 ≤ k) ∧
      (2 * (d * Nat.log 2 k) ≤ k) ∧
      ((r k).val + d * Nat.log 2 k ≤ k) ∧
      (coreSeedLen imgLen d γ_core (k + 1) ≤ k ^ E) := by
    filter_upwards [eventually_ge_atTop (2 * d + γ_core + γ + 8),
      Nat.eventually_add_mul_log_le 0 (2 * d) Nat.one_lt_two,
      eventually_regularity_gap hg himgLen r hdense d,
      eventually_coreSeedLen_succ_le_pow himg_le d γ_core] with k hk1 hk2 hk3 hk4
    exact ⟨hk1, by rw [← Nat.mul_assoc]; omega, hk3, hk4⟩
  refine ⟨fullGen g imgLen d γ_core γ, α,
    computableInPolyTime_fullGen hg.polyTime himgLen_poly d γ_core γ,
    length_fullGen g imgLen d γ_core γ,
    condSeedSet imgLen d γ_core S r, condSeedSet_nonempty imgLen d γ_core S hS r, ?_, ?_⟩
  · intro adversary hadv
    obtain ⟨c_eval, d_eval, evaluate, hevaluate, -, hlaw⟩ := hadv.exists_total_seeded_evaluator
    let D_inv := (2 * d + γ_core + 2) + 3 + (E + 1) + 2 + 2 + E * δ
    have hinv_ppt : IsPPT encBits
        (condInverter g imgLen evaluate d γ_core γ c_eval d_eval deg) :=
      isPPT_condInverter hg.polyTime himgLen_poly hevaluate d γ_core γ c_eval d_eval
        deg
    have hinv_neg :=
      (hg.inversion_negligible _ hinv_ppt).eventually_le_inv_polynomial
        (p := fun k => (k + 1) ^ D_inv) (by fun_prop) (fun k => by positivity)
    filter_upwards [eventually_ge_atTop (coreSeedLen imgLen d γ_core 0),
      hparam_tendsto.eventually (hev_k_base.and hinv_neg)] with
      n hn0 ⟨⟨hk_min, hk_2d, hgap, hcs_pow⟩, hinv_le⟩
    exact fullGen_condSeedSet_advantage_le himgLen E δ γ d γ_core c_eval d_eval rfl rfl
      S hS r (fun _ => rfl) hdense evaluate adversary hlaw rfl hn0 hk_min hk_2d hgap hcs_pow
      (by simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_one] using hinv_le)
  · filter_upwards [eventually_ge_atTop (coreSeedLen imgLen d γ_core 0),
      Nat.eventually_le_log 1 Nat.one_lt_two,
      hparam_tendsto.eventually hev_k_base] with
      n hn0 hlog_n1 ⟨hk_min, hk_2d, hgap, hcs_pow⟩
    exact fullGen_condSeedSet_entropy_ge himgLen E δ γ d γ_core rfl S hS r (fun _ => rfl) hdense
      rfl hn0 hlog_n1 (by omega) hk_2d hgap hcs_pow

end Cslib.Crypto
