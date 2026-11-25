/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.PPT
public import CslibFrontier.Computability.Probabilistic.PPT.Capture
public import CslibFrontier.Foundations.Data.BitString.List
public import CslibFrontier.Languages.Probabilistic.BitString
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Nat.Dist
public import Mathlib.Data.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Map

/-!
# Mild Average-Case Hardness of Functions Against Efficient Heuristics

This module formalizes generic mild average-case hardness definitions for functions
`f : List Bool → ℕ` (and `f : List Bool → ℕ∞`) over the uniform distribution on `{0, 1}^n`
following [Y. Liu and R. Pass, *On One-Way Functions and Kolmogorov Complexity*][LiuPass2020].
The parametric kernel `MildlyHardOnAverageFor` expresses hardness over any monotone asymptotic
length quantifier (`MonoQuant`, satisfied by both `∀ᶠ n in atTop` and `∃ᶠ n in atTop`) and
heuristic admissibility predicate (`IsPPTOn`, `IsDetPolyTime`), providing monotonicity,
admissibility and quantifier transport, zero-gap equivalence, one-sided-to-symmetric `2g → g`
gap shifting, and negative nonvacuity witnesses across all named specializations. All section,
definition, theorem, lemma, and page locators follow the full version `arXiv:2009.11514v1` (and
ECCC TR20-052).

## Main definitions

* `Cslib.Complexity.MonoQuant`: asymptotic length quantifiers `Quant : (ℕ → Prop) → Prop` closed
  under eventual implication (`∀ᶠ n in atTop`), instantiated for both `Filter.Eventually · atTop`
  and `Filter.Frequently · atTop`.
* `Cslib.Complexity.IsDetPolyTime`: admissibility predicate embedding deterministic polynomial-time
  heuristics `List Bool → β` into `List Bool → ProbComp β` via `pure`.
* `Cslib.Complexity.MildlyHardOnAverageFor`: the parametric mild average-case hardness kernel over
  `Quant`, `Admissible`, and a Boolean correctness test `correct n x v`.
* `Cslib.Complexity.MildlyHardOnAverageWith`, `Cslib.Complexity.MildlyHardOnAverageDetWith`,
  `Cslib.Complexity.MildlyHardOnAverageIOWith`: specializations of `MildlyHardOnAverageFor` to
  uniform strict PPT heuristics (`∀ᶠ`), deterministic polynomial-time heuristics (`∀ᶠ`), and
  infinitely-often deterministic heuristics (`∃ᶠ`).
* `Cslib.Complexity.MildlyHardOnAverage`: mild average-case hardness of exact computation for
  `List Bool → ℕ` against uniform strict PPT heuristics
  ([Liu and Pass, Definition 2.4, §2.3, p. 8 of arXiv:2009.11514v1][LiuPass2020]).
* `Cslib.Complexity.MildlyHardOnAverageToApprox`: mild average-case hardness of symmetric
  $g(n)$-approximation (`Nat.dist v (f x) ≤ g n`, i.e., $|v - f(x)| \le g(|x|)$) for
  `List Bool → ℕ` against uniform strict PPT heuristics
  ([Liu and Pass, Definition 2.5, §2.3, p. 8 of arXiv:2009.11514v1][LiuPass2020]).
* `Cslib.Complexity.MildlyHardOnAverageToOneSidedApprox`: library helper for one-sided
  underestimation error (`f x - g n ≤ v ∧ v ≤ f x`) against uniform strict PPT heuristics.
* `Cslib.Complexity.MildlyHardOnAverageDet`, `Cslib.Complexity.MildlyHardOnAverageToApproxDet`,
  `Cslib.Complexity.MildlyHardOnAverageToOneSidedApproxDet`:
  library specializations to deterministic polynomial-time heuristics.
* `Cslib.Complexity.MildlyHardOnAverageIO`, `Cslib.Complexity.MildlyHardOnAverageToApproxIO`,
  `Cslib.Complexity.MildlyHardOnAverageToOneSidedApproxIO`:
  library infinitely-often (`∃ᶠ n in atTop`) deterministic companions.
* `Cslib.Complexity.MildlyHardOnAverageENat`, `Cslib.Complexity.MildlyHardOnAverageIOENat`:
  library `ℕ∞`-valued companions for `List Bool → ℕ∞`, against heuristics with outputs in `ℕ`.

## Main results

* `Cslib.Complexity.MildlyHardOnAverageFor.mono`: hardness for a weaker correctness test implies
  hardness for a stronger one under any `MonoQuant`.
* `Cslib.Complexity.MildlyHardOnAverageFor.of_admissible`,
  `Cslib.Complexity.MildlyHardOnAverageFor.of_quant`: contravariance in the heuristic admissibility
  class and covariance in the length quantifier.
* `Cslib.Complexity.mildlyHardOnAverageFor_isDetPolyTime_iff`: equivalence between `ProbComp`-lifted
  `IsDetPolyTime` hardness and direct quantification over polynomial-time `List Bool → β`.
* `Cslib.Complexity.MildlyHardOnAverageFor.approx_zero_iff`,
  `Cslib.Complexity.MildlyHardOnAverageFor.oneSidedApprox_zero_iff`: zero-gap approximation
  hardness coincides with exact hardness.
* `Cslib.Complexity.MildlyHardOnAverageFor.approx_of_oneSided_two_mul`,
  `Cslib.Complexity.MildlyHardOnAverageToOneSidedApprox.mildlyHardOnAverageToApprox`,
  `Cslib.Complexity.MildlyHardOnAverageToOneSidedApproxDet.mildlyHardOnAverageToApproxDet`:
  shift + gap-scaling bridge converting one-sided $(2 g)$-approximation hardness into symmetric
  $g$-approximation hardness whenever `fun x => g x.length` is computable in polynomial time.
* `Cslib.Complexity.MildlyHardOnAverageToApprox.eventually_real_abs_sub_le`:
  upper-rounded integer log window `d * (Nat.log 2 n + 1)` implies the real-valued symmetric window
  $|(v : \mathbb{R}) - f(x)| \le d \log_2 |x|$ of Definition 2.5.
* `Cslib.Complexity.MildlyHardOnAverageFor.not_of_forall_poly`,
  `Cslib.Complexity.MildlyHardOnAverageFor.not_of_admissible_pure`,
  `Cslib.Complexity.not_mildlyHardOnAverageIO_zero`,
  `Cslib.Complexity.not_mildlyHardOnAverage_zero`:
  kernel negative-witness criteria and constant-zero nonvacuity lemmas.

## References

* [Y. Liu and R. Pass, *On One-Way Functions and Kolmogorov Complexity*][LiuPass2020],
  full version `arXiv:2009.11514v1` (Section 2.3).
-/

@[expose] public section

namespace Cslib.Complexity

open Filter Cslib.Probability Cslib.Probability.PMF Turing.MultiTapeTM

/-! ### Monotone asymptotic quantifiers and the parametric hardness kernel -/

/-- An asymptotic length quantifier `Quant : (ℕ → Prop) → Prop` closed under eventual implication
along `atTop`. Both `Filter.Eventually · atTop` (`∀ᶠ n in atTop`) and
`Filter.Frequently · atTop` (`∃ᶠ n in atTop`) satisfy `MonoQuant`, even though `Frequently` is not
a filter. -/
class MonoQuant (Quant : (ℕ → Prop) → Prop) : Prop where
  /-- Transport `Quant P` to `Quant Q` along an eventual implication `∀ᶠ n in atTop, P n → Q n`. -/
  imp_of_eventually {P Q : ℕ → Prop} : (∀ᶠ n in atTop, P n → Q n) → Quant P → Quant Q

instance : MonoQuant (Filter.Eventually · atTop) where
  imp_of_eventually hPQ hP := hP.mp hPQ

instance : MonoQuant (Filter.Frequently · atTop) where
  imp_of_eventually hPQ hP := (hP.and_eventually hPQ).mono fun _ ⟨hp, hpq⟩ => hpq hp

private theorem MonoQuant.not_of_eventually_not {Quant : (ℕ → Prop) → Prop} [MonoQuant Quant]
    (hfalse : ¬ Quant fun _ => False) {P : ℕ → Prop} (hnot : ∀ᶠ n in atTop, ¬ P n) :
    ¬ Quant P :=
  fun hP => hfalse (MonoQuant.imp_of_eventually hnot hP)

/-- Admissibility predicate for deterministic polynomial-time heuristics lifted into `ProbComp`:
`H` is point-wise `pure ∘ hDet` for some `hDet : List Bool → β` computable in polynomial time. -/
def IsDetPolyTime {β : Type} (encOut : β ↪ List Bool) (H : List Bool → ProbComp β) : Prop :=
  ∃ hDet : List Bool → β, ComputableInPolyTime hDet encBits encOut ∧ ∀ x, H x = pure (hDet x)

/-- Every deterministic polynomial-time heuristic is a strict PPT heuristic. -/
theorem IsDetPolyTime.isPPTOn {β : Type} {encOut : β ↪ List Bool}
    {H : List Bool → ProbComp β} (h : IsDetPolyTime encOut H) :
    IsPPTOn encBits encOut H := by
  obtain ⟨hDet, hpoly, hH⟩ := h
  simpa only [funext hH] using hpoly.isPPTOn

/-- Lifting a polynomial-time function `List Bool → β` with `pure` yields an `IsDetPolyTime`
heuristic. -/
theorem IsDetPolyTime.of_computableInPolyTime {β : Type} {encOut : β ↪ List Bool}
    {hDet : List Bool → β} (hpoly : ComputableInPolyTime hDet encBits encOut) :
    IsDetPolyTime encOut (fun x => pure (hDet x)) :=
  ⟨hDet, hpoly, fun _ => rfl⟩

/-- Subtracting a polynomial-time length function `g x.length` preserves
`IsPPTOn encBits encNat`. -/
private theorem isPPTOn_map_sub_length {g : ℕ → ℕ}
    (hg : ComputableInPolyTime (fun x : List Bool => g x.length) encBits encNat)
    {H : List Bool → ProbComp ℕ} (hppt : IsPPTOn encBits encNat H) :
    IsPPTOn encBits encNat (fun x => (fun v => v - g x.length) <$> H x) :=
  hppt.map_with <| ComputableInPolyTime.binary_sub'
    (ComputableInPolyTime.snd encBits encNat)
    (hg.comp (ComputableInPolyTime.fst encBits encNat))

/-- Subtracting a polynomial-time length function `g x.length` preserves `IsDetPolyTime encNat`. -/
private theorem IsDetPolyTime.map_sub_length {g : ℕ → ℕ}
    (hg : ComputableInPolyTime (fun x : List Bool => g x.length) encBits encNat)
    {H : List Bool → ProbComp ℕ} (hdet : IsDetPolyTime encNat H) :
    IsDetPolyTime encNat (fun x => (fun v => v - g x.length) <$> H x) := by
  obtain ⟨hDet, hpoly, hH⟩ := hdet
  exact ⟨fun x => hDet x - g x.length, ComputableInPolyTime.binary_sub' hpoly hg,
    fun x => by simp [hH x]⟩

/-- **Parametric mild average-case hardness kernel (`MildlyHardOnAverageFor`).**
For an asymptotic length quantifier `Quant : (ℕ → Prop) → Prop`, a heuristic admissibility
predicate `Admissible : (List Bool → ProbComp β) → Prop`, and a Boolean correctness test
`correct : ℕ → List Bool → β → Bool`, there exists a positive polynomial `p` such that every
admissible heuristic `H` satisfies `Quant` on the lengths `n` where `H` passes `correct n x` with
probability at most `1 - 1 / p(n)` over `x ← {0, 1}^n` and `H`'s coins. -/
def MildlyHardOnAverageFor {β : Type}
    (Quant : (ℕ → Prop) → Prop)
    (Admissible : (List Bool → ProbComp β) → Prop)
    (correct : ℕ → List Bool → β → Bool) : Prop :=
  ∃ p : Polynomial ℕ, (∀ n, 0 < p.eval n) ∧
    ∀ H : List Bool → ProbComp β, Admissible H →
      Quant fun n =>
        ((do
          let x ← BitString.uniformList n
          (ProbComp.eval (H x)).map (correct n x) : PMF Bool) true).toReal ≤
          1 - 1 / ((p.eval n : ℕ) : ℝ)

private theorem bind_map_le_of_imp {β : Type} {n : ℕ} (q : List Bool → PMF β)
    {c₁ c₂ : List Bool → β → Bool}
    (himp : ∀ x : List Bool, x.length = n → ∀ v, c₁ x v = true → c₂ x v = true) :
    (((BitString.uniformList n).bind fun x => (q x).map (c₁ x)) true).toReal ≤
      (((BitString.uniformList n).bind fun x => (q x).map (c₂ x)) true).toReal :=
  ENNReal.toReal_mono (PMF.apply_ne_top _ _) <|
    PMF.bind_apply_mono_on_support _ true fun x hx =>
      map_true_mono _ fun v _ => himp x (BitString.length_of_mem_support_uniformList hx) v

/-- **Monotonicity in the correctness test:** if, for all sufficiently large `n`, every output
passing `correct₁` on an input of length `n` also passes `correct₂`, then hardness for `correct₂`
implies hardness for `correct₁`. -/
theorem MildlyHardOnAverageFor.mono {β : Type}
    {Quant : (ℕ → Prop) → Prop} [MonoQuant Quant]
    {Admissible : (List Bool → ProbComp β) → Prop}
    {correct₁ correct₂ : ℕ → List Bool → β → Bool}
    (himp : ∀ᶠ n in atTop, ∀ x : List Bool, x.length = n → ∀ v,
      correct₁ n x v = true → correct₂ n x v = true)
    (h : MildlyHardOnAverageFor Quant Admissible correct₂) :
    MildlyHardOnAverageFor Quant Admissible correct₁ := by
  obtain ⟨p, hp, hH⟩ := h
  refine ⟨p, hp, fun H hadm => MonoQuant.imp_of_eventually ?_ (hH H hadm)⟩
  filter_upwards [himp] with n hn hp_n
  exact (bind_map_le_of_imp (fun x => ProbComp.eval (H x)) hn).trans hp_n

/-- **Contravariance in admissibility:** hardness against a broader heuristic class `Admissible₂`
implies hardness against any narrower class `Admissible₁`. -/
theorem MildlyHardOnAverageFor.of_admissible {β : Type}
    {Quant : (ℕ → Prop) → Prop}
    {Admissible₁ Admissible₂ : (List Bool → ProbComp β) → Prop}
    {correct : ℕ → List Bool → β → Bool}
    (hadm : ∀ {H}, Admissible₁ H → Admissible₂ H)
    (h : MildlyHardOnAverageFor Quant Admissible₂ correct) :
    MildlyHardOnAverageFor Quant Admissible₁ correct :=
  let ⟨p, hp, hH⟩ := h
  ⟨p, hp, fun H h1 => hH H (hadm h1)⟩

/-- **Covariance in the length quantifier:** transporting `Quant₂` to a weaker quantifier `Quant₁`
preserves `MildlyHardOnAverageFor`. -/
theorem MildlyHardOnAverageFor.of_quant {β : Type}
    {Quant₁ Quant₂ : (ℕ → Prop) → Prop}
    {Admissible : (List Bool → ProbComp β) → Prop}
    {correct : ℕ → List Bool → β → Bool}
    (hq : ∀ {P}, Quant₂ P → Quant₁ P)
    (h : MildlyHardOnAverageFor Quant₂ Admissible correct) :
    MildlyHardOnAverageFor Quant₁ Admissible correct :=
  let ⟨p, hp, hH⟩ := h
  ⟨p, hp, fun H hadm => hq (hH H hadm)⟩

/-- Quantifying over `IsDetPolyTime` heuristics in `ProbComp` is equivalent to quantifying directly
over deterministic polynomial-time functions `H : List Bool → β`. -/
theorem mildlyHardOnAverageFor_isDetPolyTime_iff {β : Type}
    {Quant : (ℕ → Prop) → Prop} {encOut : β ↪ List Bool}
    {correct : ℕ → List Bool → β → Bool} :
    MildlyHardOnAverageFor Quant (IsDetPolyTime encOut) correct ↔
      ∃ p : Polynomial ℕ, (∀ n, 0 < p.eval n) ∧
        ∀ H : List Bool → β, ComputableInPolyTime H encBits encOut →
          Quant fun n =>
            (((BitString.uniformList n).map fun x => correct n x (H x)) true).toReal ≤
              1 - 1 / ((p.eval n : ℕ) : ℝ) := by
  have heval (hDet : List Bool → β) (n : ℕ) :
      (do
        let x ← BitString.uniformList n
        (ProbComp.eval (pure (hDet x))).map (correct n x) : PMF Bool) =
        (BitString.uniformList n).map fun x => correct n x (hDet x) := by
    simp only [ProbComp.eval_pure, PMF.pure_map]; rfl
  exact ⟨fun ⟨p, hp, hH⟩ => ⟨p, hp, fun hDet hpoly => by
      simpa only [heval] using hH (fun x => pure (hDet x)) (.of_computableInPolyTime hpoly)⟩,
    fun ⟨p, hp, hH⟩ => ⟨p, hp, fun H ⟨hDet, hpoly, hEq⟩ => by
      simpa only [funext hEq, heval] using hH hDet hpoly⟩⟩

/-- Monotonicity of symmetric `g`-approximation hardness on the kernel. -/
theorem MildlyHardOnAverageFor.approx_mono
    {Quant : (ℕ → Prop) → Prop} [MonoQuant Quant]
    {Admissible : (List Bool → ProbComp ℕ) → Prop}
    {g₁ g₂ : ℕ → ℕ} {f : List Bool → ℕ} (hle : ∀ n, g₁ n ≤ g₂ n)
    (h : MildlyHardOnAverageFor Quant Admissible fun n x v => decide (Nat.dist v (f x) ≤ g₂ n)) :
    MildlyHardOnAverageFor Quant Admissible fun n x v => decide (Nat.dist v (f x) ≤ g₁ n) :=
  h.mono (.of_forall fun n _ _ _ hv => by
    simp only [decide_eq_true_eq] at hv ⊢; exact hv.trans (hle n))

/-- Monotonicity of one-sided `g`-approximation hardness on the kernel. -/
theorem MildlyHardOnAverageFor.oneSidedApprox_mono
    {Quant : (ℕ → Prop) → Prop} [MonoQuant Quant]
    {Admissible : (List Bool → ProbComp ℕ) → Prop}
    {g₁ g₂ : ℕ → ℕ} {f : List Bool → ℕ} (hle : ∀ n, g₁ n ≤ g₂ n)
    (h : MildlyHardOnAverageFor Quant Admissible
      fun n x v => decide (f x - g₂ n ≤ v ∧ v ≤ f x)) :
    MildlyHardOnAverageFor Quant Admissible
      fun n x v => decide (f x - g₁ n ≤ v ∧ v ≤ f x) :=
  h.mono (.of_forall fun n _ _ _ hv => by
    simp only [decide_eq_true_eq] at hv ⊢; have := hle n; omega)

/-- Symmetric `g`-approximation hardness implies one-sided `g`-approximation hardness on the
kernel. -/
theorem MildlyHardOnAverageFor.oneSidedApprox_of_approx
    {Quant : (ℕ → Prop) → Prop} [MonoQuant Quant]
    {Admissible : (List Bool → ProbComp ℕ) → Prop}
    {g : ℕ → ℕ} {f : List Bool → ℕ}
    (h : MildlyHardOnAverageFor Quant Admissible fun n x v => decide (Nat.dist v (f x) ≤ g n)) :
    MildlyHardOnAverageFor Quant Admissible fun n x v => decide (f x - g n ≤ v ∧ v ≤ f x) :=
  h.mono (.of_forall fun _ _ _ _ hv => by
    simp only [decide_eq_true_eq] at hv ⊢; unfold Nat.dist; omega)

/-- Symmetric `g`-approximation hardness implies exact hardness on the kernel. -/
theorem MildlyHardOnAverageFor.exact_of_approx
    {Quant : (ℕ → Prop) → Prop} [MonoQuant Quant]
    {Admissible : (List Bool → ProbComp ℕ) → Prop}
    {g : ℕ → ℕ} {f : List Bool → ℕ}
    (h : MildlyHardOnAverageFor Quant Admissible fun n x v => decide (Nat.dist v (f x) ≤ g n)) :
    MildlyHardOnAverageFor Quant Admissible fun _ x v => decide (v = f x) :=
  h.mono (.of_forall fun _ _ _ _ hv => by rw [decide_eq_true_eq] at hv; simp [hv])

/-- One-sided `g`-approximation hardness implies exact hardness on the kernel. -/
theorem MildlyHardOnAverageFor.exact_of_oneSidedApprox
    {Quant : (ℕ → Prop) → Prop} [MonoQuant Quant]
    {Admissible : (List Bool → ProbComp ℕ) → Prop}
    {g : ℕ → ℕ} {f : List Bool → ℕ}
    (h : MildlyHardOnAverageFor Quant Admissible
      fun n x v => decide (f x - g n ≤ v ∧ v ≤ f x)) :
    MildlyHardOnAverageFor Quant Admissible fun _ x v => decide (v = f x) :=
  h.mono (.of_forall fun _ _ _ _ hv => by simp only [decide_eq_true_eq] at hv ⊢; omega)

/-- **Zero-gap specialization (symmetric):** symmetric `0`-approximation hardness coincides with
exact hardness for every quantifier and admissibility predicate. -/
theorem MildlyHardOnAverageFor.approx_zero_iff
    {Quant : (ℕ → Prop) → Prop}
    {Admissible : (List Bool → ProbComp ℕ) → Prop}
    {f : List Bool → ℕ} :
    (MildlyHardOnAverageFor Quant Admissible fun _ x v => decide (Nat.dist v (f x) ≤ 0)) ↔
      MildlyHardOnAverageFor Quant Admissible fun _ x v => decide (v = f x) :=
  Iff.of_eq (congrArg (MildlyHardOnAverageFor Quant Admissible)
    (funext fun _ => funext fun _ => funext fun _ =>
      decide_eq_decide.mpr (by unfold Nat.dist; omega)))

/-- **Zero-gap specialization (one-sided):** one-sided `0`-approximation hardness coincides with
exact hardness for every quantifier and admissibility predicate. -/
theorem MildlyHardOnAverageFor.oneSidedApprox_zero_iff
    {Quant : (ℕ → Prop) → Prop}
    {Admissible : (List Bool → ProbComp ℕ) → Prop}
    {f : List Bool → ℕ} :
    (MildlyHardOnAverageFor Quant Admissible fun _ x v => decide (f x - 0 ≤ v ∧ v ≤ f x)) ↔
      MildlyHardOnAverageFor Quant Admissible fun _ x v => decide (v = f x) :=
  Iff.of_eq (congrArg (MildlyHardOnAverageFor Quant Admissible)
    (funext fun _ => funext fun _ => funext fun _ => decide_eq_decide.mpr (by omega)))

/-- **Parametric `2g → g` gap-shifting bridge:** whenever `Admissible` is closed under shifting
outputs down by `g x.length`, one-sided `(2 g)`-approximation hardness implies symmetric
`g`-approximation hardness. -/
theorem MildlyHardOnAverageFor.approx_of_oneSided_two_mul
    {Quant : (ℕ → Prop) → Prop} [MonoQuant Quant]
    {Admissible : (List Bool → ProbComp ℕ) → Prop}
    {g : ℕ → ℕ} {f : List Bool → ℕ}
    (hshift : ∀ {H : List Bool → ProbComp ℕ}, Admissible H →
      Admissible (fun x => (fun v => v - g x.length) <$> H x))
    (h : MildlyHardOnAverageFor Quant Admissible
      fun n x v => decide (f x - 2 * g n ≤ v ∧ v ≤ f x)) :
    MildlyHardOnAverageFor Quant Admissible
      fun n x v => decide (Nat.dist v (f x) ≤ g n) := by
  obtain ⟨p, hp, hH⟩ := h
  refine ⟨p, hp, fun H hadm => MonoQuant.imp_of_eventually ?_ (hH _ (hshift hadm))⟩
  refine .of_forall fun n hn => (ENNReal.toReal_mono (PMF.apply_ne_top _ _) ?_).trans hn
  refine PMF.bind_apply_mono_on_support _ true fun x hx => ?_
  have hlen : x.length = n := BitString.length_of_mem_support_uniformList hx
  rw [ProbComp.eval_map, PMF.map_comp]
  refine map_true_mono _ fun v _ hdist => ?_
  simp only [Function.comp_apply, decide_eq_true_eq, hlen] at hdist ⊢
  unfold Nat.dist at hdist
  omega

/-- **Negative-witness criterion on the kernel:** if `Quant` rejects `False` and every positive
polynomial `p` admits an admissible heuristic whose success probability eventually exceeds
`1 - 1 / p(n)`, then `MildlyHardOnAverageFor` fails. -/
theorem MildlyHardOnAverageFor.not_of_forall_poly {β : Type}
    {Quant : (ℕ → Prop) → Prop} [MonoQuant Quant] (hfalse : ¬ Quant fun _ => False)
    {Admissible : (List Bool → ProbComp β) → Prop}
    {correct : ℕ → List Bool → β → Bool}
    (hwin : ∀ p : Polynomial ℕ, (∀ n, 0 < p.eval n) →
      ∃ H : List Bool → ProbComp β, Admissible H ∧
        ∀ᶠ n in atTop,
          1 - 1 / ((p.eval n : ℕ) : ℝ) <
            ((do
              let x ← BitString.uniformList n
              (ProbComp.eval (H x)).map (correct n x) : PMF Bool) true).toReal) :
    ¬ MildlyHardOnAverageFor Quant Admissible correct := by
  rintro ⟨p, hp, hhard⟩
  obtain ⟨H, hadm, hlt⟩ := hwin p hp
  exact MonoQuant.not_of_eventually_not hfalse (hlt.mono fun _ => not_le_of_gt) (hhard H hadm)

/-- **Constant-heuristic nonvacuity on the kernel:** if an admissible constant heuristic `pure v₀`
eventually passes `correct` on every input of length `n`, then `MildlyHardOnAverageFor` fails. -/
theorem MildlyHardOnAverageFor.not_of_admissible_pure {β : Type}
    {Quant : (ℕ → Prop) → Prop} [MonoQuant Quant] (hfalse : ¬ Quant fun _ => False)
    {Admissible : (List Bool → ProbComp β) → Prop}
    {correct : ℕ → List Bool → β → Bool} {v₀ : β}
    (hadm : Admissible (fun _ => pure v₀))
    (hcorr : ∀ᶠ n in atTop, ∀ x : List Bool, x.length = n → correct n x v₀ = true) :
    ¬ MildlyHardOnAverageFor Quant Admissible correct := by
  refine MildlyHardOnAverageFor.not_of_forall_poly hfalse fun p hp => ⟨fun _ => pure v₀, hadm, ?_⟩
  filter_upwards [hcorr] with n hn
  rw [show ((do
      let x ← BitString.uniformList n
      (ProbComp.eval (pure v₀)).map (correct n x) : PMF Bool)) = PMF.pure true from
    (PMF.bind_congr_on_support (BitString.uniformList n) _ (fun _ => PMF.pure true) fun x hx => by
      simp [hn x (BitString.length_of_mem_support_uniformList hx)]).trans (PMF.bind_const _ _)]
  simp only [PMF.pure_apply_self, ENNReal.toReal_one]
  linarith [one_div_pos.mpr (show (0 : ℝ) < (p.eval n : ℕ) by exact_mod_cast hp n)]

/-! ### Specializations of the kernel to PPT, deterministic, and infinitely-often cores -/

/-- **Mild average-case hardness for a correctness test, against strict PPT heuristics**:
`MildlyHardOnAverageFor` instantiated at `∀ᶠ n in atTop` and `IsPPTOn encBits encNat`. -/
abbrev MildlyHardOnAverageWith (correct : ℕ → List Bool → ℕ → Bool) : Prop :=
  MildlyHardOnAverageFor (Filter.Eventually · atTop) (IsPPTOn encBits encNat) correct

/-- **Mild average-case hardness for a correctness test, against deterministic heuristics**:
`MildlyHardOnAverageFor` instantiated at `∀ᶠ n in atTop` and `IsDetPolyTime encNat`. -/
abbrev MildlyHardOnAverageDetWith (correct : ℕ → List Bool → ℕ → Bool) : Prop :=
  MildlyHardOnAverageFor (Filter.Eventually · atTop) (IsDetPolyTime encNat) correct

/-- **Infinitely-often mild average-case hardness for a correctness test, against deterministic
heuristics**: `MildlyHardOnAverageFor` instantiated at `∃ᶠ n in atTop` and
`IsDetPolyTime encNat`. -/
abbrev MildlyHardOnAverageIOWith (correct : ℕ → List Bool → ℕ → Bool) : Prop :=
  MildlyHardOnAverageFor (Filter.Frequently · atTop) (IsDetPolyTime encNat) correct

/-- Monotonicity of `MildlyHardOnAverageWith` in the correctness test. -/
theorem MildlyHardOnAverageWith.mono {correct₁ correct₂ : ℕ → List Bool → ℕ → Bool}
    (himp : ∀ᶠ n in atTop, ∀ x : List Bool, x.length = n → ∀ v,
      correct₁ n x v = true → correct₂ n x v = true)
    (h : MildlyHardOnAverageWith correct₂) : MildlyHardOnAverageWith correct₁ :=
  MildlyHardOnAverageFor.mono himp h

/-- `MildlyHardOnAverageWith.mono` for deterministic heuristics. -/
theorem MildlyHardOnAverageDetWith.mono {correct₁ correct₂ : ℕ → List Bool → ℕ → Bool}
    (himp : ∀ᶠ n in atTop, ∀ x : List Bool, x.length = n → ∀ v,
      correct₁ n x v = true → correct₂ n x v = true)
    (h : MildlyHardOnAverageDetWith correct₂) : MildlyHardOnAverageDetWith correct₁ :=
  MildlyHardOnAverageFor.mono himp h

/-- `MildlyHardOnAverageWith.mono` for infinitely-often hardness. -/
theorem MildlyHardOnAverageIOWith.mono {correct₁ correct₂ : ℕ → List Bool → ℕ → Bool}
    (himp : ∀ᶠ n in atTop, ∀ x : List Bool, x.length = n → ∀ v,
      correct₁ n x v = true → correct₂ n x v = true)
    (h : MildlyHardOnAverageIOWith correct₂) : MildlyHardOnAverageIOWith correct₁ :=
  MildlyHardOnAverageFor.mono himp h

/-- Hardness against strict PPT heuristics implies hardness against deterministic polynomial-time
heuristics, since every deterministic polynomial-time heuristic is a strict PPT heuristic. -/
theorem MildlyHardOnAverageWith.mildlyHardOnAverageDetWith {correct : ℕ → List Bool → ℕ → Bool}
    (h : MildlyHardOnAverageWith correct) : MildlyHardOnAverageDetWith correct :=
  h.of_admissible IsDetPolyTime.isPPTOn

/-- Eventual hardness implies infinitely-often hardness. -/
theorem MildlyHardOnAverageDetWith.mildlyHardOnAverageIOWith {correct : ℕ → List Bool → ℕ → Bool}
    (h : MildlyHardOnAverageDetWith correct) : MildlyHardOnAverageIOWith correct :=
  h.of_quant Filter.Eventually.frequently

/-! ### Average-case hardness definitions
([Liu and Pass, Definitions 2.4 and 2.5, §2.3, p. 8 of arXiv:2009.11514v1][LiuPass2020]) -/

/-- **[Liu and Pass, Definition 2.4, §2.3, p. 8 of arXiv:2009.11514v1][LiuPass2020]:
Mildly hard on average (`MildlyHardOnAverage`).**
A function $f : \{0, 1\}^* \to \mathbb{N}$ is mildly hard on average if there exists a positive
polynomial $p$ such that for every uniform strict PPT heuristic
$\mathcal{H} : \{0, 1\}^* \to \mathrm{ProbComp}\ \mathbb{N}$, for all sufficiently large
$n \in \mathbb{N}$,
$$\Pr_{x \leftarrow \{0, 1\}^n, v \leftarrow \mathcal{H}(x)}[v = f(x)] \le 1 - \frac{1}{p(n)}.$$ -/
def MildlyHardOnAverage (f : List Bool → ℕ) : Prop :=
  MildlyHardOnAverageWith fun _ x v => decide (v = f x)

/-- **[Liu and Pass, Definition 2.5, §2.3, p. 8 of arXiv:2009.11514v1][LiuPass2020]:
Mildly hard on average to $g$-approximate (`MildlyHardOnAverageToApprox`).**
A function $f : \{0, 1\}^* \to \mathbb{N}$ is mildly hard on average to $g$-approximate if there
exists a positive polynomial $p$ such that for every uniform strict PPT heuristic
$\mathcal{H} : \{0, 1\}^* \to \mathrm{ProbComp}\ \mathbb{N}$, for all sufficiently large
$n \in \mathbb{N}$,
$$\Pr_{x \leftarrow \{0, 1\}^n, v \leftarrow \mathcal{H}(x)}[|v - f(x)| \le g(n)]
  \le 1 - \frac{1}{p(n)},$$
where $|v - f(x)|$ is formalized on $\mathbb{N}$ by the symmetric distance `Nat.dist v (f x)`. -/
def MildlyHardOnAverageToApprox (g : ℕ → ℕ) (f : List Bool → ℕ) : Prop :=
  MildlyHardOnAverageWith fun n x v => decide (Nat.dist v (f x) ≤ g n)

/-- **Library helper (`MildlyHardOnAverageToOneSidedApprox`):** one-sided underestimation
approximation hardness against uniform strict PPT heuristics, requiring
$$\Pr_{x \leftarrow \{0, 1\}^n, v \leftarrow \mathcal{H}(x)}[f(x) - g(n) \le v \le f(x)]
  \le 1 - \frac{1}{p(n)}$$
for all sufficiently large $n$. By
`MildlyHardOnAverageToOneSidedApprox.mildlyHardOnAverageToApprox`, one-sided
$(2 g)$-approximation hardness implies symmetric $g$-approximation hardness
(`MildlyHardOnAverageToApprox g f`) whenever `fun x => g x.length` is computable in polynomial time
by shifting any heuristic output down by $g(|x|)$. -/
def MildlyHardOnAverageToOneSidedApprox (g : ℕ → ℕ) (f : List Bool → ℕ) : Prop :=
  MildlyHardOnAverageWith fun n x v => decide (f x - g n ≤ v ∧ v ≤ f x)

/-- **Library specialization (`MildlyHardOnAverageDet`):** deterministic polynomial-time heuristic
specialization of `MildlyHardOnAverage`. -/
def MildlyHardOnAverageDet (f : List Bool → ℕ) : Prop :=
  MildlyHardOnAverageDetWith fun _ x v => decide (v = f x)

/-- **Library specialization (`MildlyHardOnAverageToApproxDet`):** deterministic polynomial-time
heuristic specialization of `MildlyHardOnAverageToApprox`. -/
def MildlyHardOnAverageToApproxDet (g : ℕ → ℕ) (f : List Bool → ℕ) : Prop :=
  MildlyHardOnAverageDetWith fun n x v => decide (Nat.dist v (f x) ≤ g n)

/-- **Library specialization (`MildlyHardOnAverageToOneSidedApproxDet`):** deterministic
polynomial-time heuristic specialization of `MildlyHardOnAverageToOneSidedApprox`. -/
def MildlyHardOnAverageToOneSidedApproxDet (g : ℕ → ℕ) (f : List Bool → ℕ) : Prop :=
  MildlyHardOnAverageDetWith fun n x v => decide (f x - g n ≤ v ∧ v ≤ f x)

/-- **Library companion (`MildlyHardOnAverageIO`):** infinitely-often (`∃ᶠ n in atTop`)
deterministic-heuristic companion to `MildlyHardOnAverageDet`. -/
def MildlyHardOnAverageIO (f : List Bool → ℕ) : Prop :=
  MildlyHardOnAverageIOWith fun _ x v => decide (v = f x)

/-- **Library companion (`MildlyHardOnAverageToApproxIO`):** infinitely-often (`∃ᶠ n in atTop`)
deterministic-heuristic companion to `MildlyHardOnAverageToApproxDet`. -/
def MildlyHardOnAverageToApproxIO (g : ℕ → ℕ) (f : List Bool → ℕ) : Prop :=
  MildlyHardOnAverageIOWith fun n x v => decide (Nat.dist v (f x) ≤ g n)

/-- **Library companion (`MildlyHardOnAverageToOneSidedApproxIO`):** infinitely-often
(`∃ᶠ n in atTop`) deterministic-heuristic companion to `MildlyHardOnAverageToOneSidedApproxDet`. -/
def MildlyHardOnAverageToOneSidedApproxIO (g : ℕ → ℕ) (f : List Bool → ℕ) : Prop :=
  MildlyHardOnAverageIOWith fun n x v => decide (f x - g n ≤ v ∧ v ≤ f x)

/-- **Library companion (`MildlyHardOnAverageENat`):** `ℕ∞`-valued companion to
`MildlyHardOnAverage` for functions `f : List Bool → ℕ∞` such as `Kolmogorov.timeBounded t`.
Heuristics output natural numbers, so no output is correct on an input with `f x = ⊤`: the
predicate holds for every `f` that is `⊤` on all inputs of every sufficiently large length. -/
def MildlyHardOnAverageENat (f : List Bool → ℕ∞) : Prop :=
  MildlyHardOnAverageWith fun _ x v => decide ((v : ℕ∞) = f x)

/-- **Library companion (`MildlyHardOnAverageIOENat`):** `ℕ∞`-valued companion to
`MildlyHardOnAverageIO` for functions `f : List Bool → ℕ∞` such as `Kolmogorov.timeBounded t`.
Heuristics output natural numbers, so no output is correct on an input with `f x = ⊤`: the
predicate holds for every `f` that is `⊤` on all inputs of infinitely many lengths. -/
def MildlyHardOnAverageIOENat (f : List Bool → ℕ∞) : Prop :=
  MildlyHardOnAverageIOWith fun _ x v => decide ((v : ℕ∞) = f x)

/-! ### Monotonicity, shifting, and specialization corollaries -/

/-- Monotonicity of `MildlyHardOnAverageToApprox` in the error window: if $g_1(n) \le g_2(n)$ for
all $n$, then hardness of $g_2$-approximation implies hardness of $g_1$-approximation. -/
theorem MildlyHardOnAverageToApprox.mono {g₁ g₂ : ℕ → ℕ} {f : List Bool → ℕ}
    (hle : ∀ n, g₁ n ≤ g₂ n) (h : MildlyHardOnAverageToApprox g₂ f) :
    MildlyHardOnAverageToApprox g₁ f :=
  MildlyHardOnAverageFor.approx_mono (Quant := (Filter.Eventually · atTop))
    (Admissible := IsPPTOn encBits encNat) hle h

/-- Monotonicity of `MildlyHardOnAverageToApproxDet` in the error window. -/
theorem MildlyHardOnAverageToApproxDet.mono {g₁ g₂ : ℕ → ℕ} {f : List Bool → ℕ}
    (hle : ∀ n, g₁ n ≤ g₂ n) (h : MildlyHardOnAverageToApproxDet g₂ f) :
    MildlyHardOnAverageToApproxDet g₁ f :=
  MildlyHardOnAverageFor.approx_mono (Quant := (Filter.Eventually · atTop))
    (Admissible := IsDetPolyTime encNat) hle h

/-- Monotonicity of `MildlyHardOnAverageToOneSidedApprox` in the error window. -/
theorem MildlyHardOnAverageToOneSidedApprox.mono {g₁ g₂ : ℕ → ℕ} {f : List Bool → ℕ}
    (hle : ∀ n, g₁ n ≤ g₂ n) (h : MildlyHardOnAverageToOneSidedApprox g₂ f) :
    MildlyHardOnAverageToOneSidedApprox g₁ f :=
  MildlyHardOnAverageFor.oneSidedApprox_mono (Quant := (Filter.Eventually · atTop))
    (Admissible := IsPPTOn encBits encNat) hle h

/-- Monotonicity of `MildlyHardOnAverageToOneSidedApproxDet` in the error window. -/
theorem MildlyHardOnAverageToOneSidedApproxDet.mono {g₁ g₂ : ℕ → ℕ} {f : List Bool → ℕ}
    (hle : ∀ n, g₁ n ≤ g₂ n) (h : MildlyHardOnAverageToOneSidedApproxDet g₂ f) :
    MildlyHardOnAverageToOneSidedApproxDet g₁ f :=
  MildlyHardOnAverageFor.oneSidedApprox_mono (Quant := (Filter.Eventually · atTop))
    (Admissible := IsDetPolyTime encNat) hle h

/-- Symmetric $g$-approximation hardness (`MildlyHardOnAverageToApprox g f`) implies one-sided
$g$-approximation hardness (`MildlyHardOnAverageToOneSidedApprox g f`). -/
theorem MildlyHardOnAverageToApprox.mildlyHardOnAverageToOneSidedApprox {g : ℕ → ℕ}
    {f : List Bool → ℕ} (h : MildlyHardOnAverageToApprox g f) :
    MildlyHardOnAverageToOneSidedApprox g f :=
  MildlyHardOnAverageFor.oneSidedApprox_of_approx (Quant := (Filter.Eventually · atTop))
    (Admissible := IsPPTOn encBits encNat) (g := g) (f := f) h

/--
**Shift + gap-scaling bridge (`MildlyHardOnAverageToOneSidedApprox.mildlyHardOnAverageToApprox`):**
shifting a symmetric $g$-estimator $\mathcal{H}(x)$ down by $g(|x|)$ produces a one-sided
$(2 g)$-estimator $\mathcal{H}'(x) = \mathcal{H}(x) - g(|x|)$, because $|v - f(x)| \le g(|x|)$
implies $f(x) - 2 g(|x|) \le v - g(|x|) \le f(x)$. Consequently, when `fun x => g x.length` is
computable in polynomial time, one-sided $(2 g)$-approximation hardness against PPT heuristics
implies symmetric $g$-approximation hardness (`MildlyHardOnAverageToApprox g f`). -/
theorem MildlyHardOnAverageToOneSidedApprox.mildlyHardOnAverageToApprox {g : ℕ → ℕ}
    {f : List Bool → ℕ}
    (hg : ComputableInPolyTime (fun x : List Bool => g x.length) encBits encNat)
    (h : MildlyHardOnAverageToOneSidedApprox (fun n => 2 * g n) f) :
    MildlyHardOnAverageToApprox g f :=
  MildlyHardOnAverageFor.approx_of_oneSided_two_mul (Quant := (Filter.Eventually · atTop))
    (Admissible := IsPPTOn encBits encNat) (isPPTOn_map_sub_length hg) h

/-- Deterministic counterpart of
`MildlyHardOnAverageToOneSidedApprox.mildlyHardOnAverageToApprox`. -/
theorem MildlyHardOnAverageToOneSidedApproxDet.mildlyHardOnAverageToApproxDet {g : ℕ → ℕ}
    {f : List Bool → ℕ}
    (hg : ComputableInPolyTime (fun x : List Bool => g x.length) encBits encNat)
    (h : MildlyHardOnAverageToOneSidedApproxDet (fun n => 2 * g n) f) :
    MildlyHardOnAverageToApproxDet g f :=
  MildlyHardOnAverageFor.approx_of_oneSided_two_mul (Quant := (Filter.Eventually · atTop))
    (Admissible := IsDetPolyTime encNat) (IsDetPolyTime.map_sub_length hg) h

/-- `MildlyHardOnAverageDet` implies `MildlyHardOnAverageIO`. -/
theorem MildlyHardOnAverageDet.mildlyHardOnAverageIO {f : List Bool → ℕ}
    (h : MildlyHardOnAverageDet f) : MildlyHardOnAverageIO f :=
  MildlyHardOnAverageDetWith.mildlyHardOnAverageIOWith h

/-- `MildlyHardOnAverageToApproxDet` implies `MildlyHardOnAverageToApproxIO`. -/
theorem MildlyHardOnAverageToApproxDet.mildlyHardOnAverageToApproxIO {g : ℕ → ℕ}
    {f : List Bool → ℕ} (h : MildlyHardOnAverageToApproxDet g f) :
    MildlyHardOnAverageToApproxIO g f :=
  MildlyHardOnAverageDetWith.mildlyHardOnAverageIOWith h

/-- `MildlyHardOnAverageToOneSidedApproxDet` implies `MildlyHardOnAverageToOneSidedApproxIO`. -/
theorem MildlyHardOnAverageToOneSidedApproxDet.mildlyHardOnAverageToOneSidedApproxIO {g : ℕ → ℕ}
    {f : List Bool → ℕ} (h : MildlyHardOnAverageToOneSidedApproxDet g f) :
    MildlyHardOnAverageToOneSidedApproxIO g f :=
  MildlyHardOnAverageDetWith.mildlyHardOnAverageIOWith h

/-- `MildlyHardOnAverageToApproxDet g f` implies `MildlyHardOnAverageDet f`. -/
theorem MildlyHardOnAverageToApproxDet.mildlyHardOnAverageDet {g : ℕ → ℕ} {f : List Bool → ℕ}
    (h : MildlyHardOnAverageToApproxDet g f) : MildlyHardOnAverageDet f :=
  MildlyHardOnAverageFor.exact_of_approx (Quant := (Filter.Eventually · atTop))
    (Admissible := IsDetPolyTime encNat) (g := g) (f := f) h

/-- `MildlyHardOnAverageToOneSidedApproxDet g f` implies `MildlyHardOnAverageDet f`. -/
theorem MildlyHardOnAverageToOneSidedApproxDet.mildlyHardOnAverageDet {g : ℕ → ℕ}
    {f : List Bool → ℕ} (h : MildlyHardOnAverageToOneSidedApproxDet g f) :
    MildlyHardOnAverageDet f :=
  MildlyHardOnAverageFor.exact_of_oneSidedApprox (Quant := (Filter.Eventually · atTop))
    (Admissible := IsDetPolyTime encNat) (g := g) (f := f) h

/-- `MildlyHardOnAverageToApproxIO g f` implies `MildlyHardOnAverageIO f`. -/
theorem MildlyHardOnAverageToApproxIO.mildlyHardOnAverageIO {g : ℕ → ℕ} {f : List Bool → ℕ}
    (h : MildlyHardOnAverageToApproxIO g f) : MildlyHardOnAverageIO f :=
  MildlyHardOnAverageFor.exact_of_approx (Quant := (Filter.Frequently · atTop))
    (Admissible := IsDetPolyTime encNat) (g := g) (f := f) h

/-- `MildlyHardOnAverageToOneSidedApproxIO g f` implies `MildlyHardOnAverageIO f`. -/
theorem MildlyHardOnAverageToOneSidedApproxIO.mildlyHardOnAverageIO {g : ℕ → ℕ}
    {f : List Bool → ℕ} (h : MildlyHardOnAverageToOneSidedApproxIO g f) :
    MildlyHardOnAverageIO f :=
  MildlyHardOnAverageFor.exact_of_oneSidedApprox (Quant := (Filter.Frequently · atTop))
    (Admissible := IsDetPolyTime encNat) (g := g) (f := f) h

/-- `MildlyHardOnAverageToApprox` implies `MildlyHardOnAverageToApproxDet` (since every
deterministic polynomial-time heuristic is a strict PPT heuristic). -/
theorem MildlyHardOnAverageToApprox.mildlyHardOnAverageToApproxDet {g : ℕ → ℕ}
    {f : List Bool → ℕ} (h : MildlyHardOnAverageToApprox g f) :
    MildlyHardOnAverageToApproxDet g f :=
  MildlyHardOnAverageWith.mildlyHardOnAverageDetWith h

/-- `MildlyHardOnAverageToOneSidedApprox` implies `MildlyHardOnAverageToOneSidedApproxDet`. -/
theorem MildlyHardOnAverageToOneSidedApprox.mildlyHardOnAverageToOneSidedApproxDet {g : ℕ → ℕ}
    {f : List Bool → ℕ} (h : MildlyHardOnAverageToOneSidedApprox g f) :
    MildlyHardOnAverageToOneSidedApproxDet g f :=
  MildlyHardOnAverageWith.mildlyHardOnAverageDetWith h

/-- `MildlyHardOnAverage` implies `MildlyHardOnAverageDet`. -/
theorem MildlyHardOnAverage.mildlyHardOnAverageDet {f : List Bool → ℕ}
    (h : MildlyHardOnAverage f) : MildlyHardOnAverageDet f :=
  MildlyHardOnAverageWith.mildlyHardOnAverageDetWith h

/-- `MildlyHardOnAverage` implies `MildlyHardOnAverageIO`. -/
theorem MildlyHardOnAverage.mildlyHardOnAverageIO {f : List Bool → ℕ}
    (h : MildlyHardOnAverage f) :
    MildlyHardOnAverageIO f :=
  h.mildlyHardOnAverageDet.mildlyHardOnAverageIO

/-- `MildlyHardOnAverageToApprox g f` implies `MildlyHardOnAverage f`. -/
theorem MildlyHardOnAverageToApprox.mildlyHardOnAverage {g : ℕ → ℕ} {f : List Bool → ℕ}
    (h : MildlyHardOnAverageToApprox g f) : MildlyHardOnAverage f :=
  MildlyHardOnAverageFor.exact_of_approx (Quant := (Filter.Eventually · atTop))
    (Admissible := IsPPTOn encBits encNat) (g := g) (f := f) h

/-- `MildlyHardOnAverageToOneSidedApprox g f` implies `MildlyHardOnAverage f`. -/
theorem MildlyHardOnAverageToOneSidedApprox.mildlyHardOnAverage {g : ℕ → ℕ} {f : List Bool → ℕ}
    (h : MildlyHardOnAverageToOneSidedApprox g f) : MildlyHardOnAverage f :=
  MildlyHardOnAverageFor.exact_of_oneSidedApprox (Quant := (Filter.Eventually · atTop))
    (Admissible := IsPPTOn encBits encNat) (g := g) (f := f) h

/-! ### Rounded logarithm bounds and real-valued log window bridge -/

/-- For every $n \in \mathbb{N}$, $\lceil \log_2 n \rceil \le \lfloor \log_2 n \rfloor + 1$. -/
theorem nat_clog_two_le_log_two_succ (n : ℕ) : Nat.clog 2 n ≤ Nat.log 2 n + 1 :=
  Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_pow_succ_log_self Nat.one_lt_two n))

/-- For every $n \ge 1$, the real binary logarithm satisfies
$\log_2 n \le \lfloor \log_2 n \rfloor + 1$. -/
theorem real_logb_two_le_nat_log_two_succ {n : ℕ} (hn : 1 ≤ n) :
    Real.logb 2 (n : ℝ) ≤ (Nat.log 2 n + 1 : ℕ) := by
  rw [Real.logb_le_iff_le_rpow (by norm_num) (by exact_mod_cast hn), Real.rpow_natCast]
  exact_mod_cast (Nat.lt_pow_succ_log_self Nat.one_lt_two n).le

/-- Any real-valued symmetric approximation error $|(v : \mathbb{R}) - (w : \mathbb{R})| \le
d \log_2 n$ (for $n \ge 1$) implies the upper-rounded integer distance bound
`Nat.dist v w ≤ d * (Nat.log 2 n + 1)`. -/
theorem nat_dist_le_mul_log_two_succ_of_abs_sub_le_mul_logb {v w d n : ℕ} (hn : 1 ≤ n)
    (h : |(v : ℝ) - (w : ℝ)| ≤ (d : ℝ) * Real.logb 2 (n : ℝ)) :
    Nat.dist v w ≤ d * (Nat.log 2 n + 1) := by
  have hdist : ((Nat.dist v w : ℕ) : ℝ) = |(v : ℝ) - (w : ℝ)| := by
    rcases le_total v w with hvw | hwv
    · rw [show Nat.dist v w = w - v by unfold Nat.dist; omega, Nat.cast_sub hvw,
        abs_of_nonpos (sub_nonpos.2 (by exact_mod_cast hvw)), neg_sub]
    · rw [show Nat.dist v w = v - w by unfold Nat.dist; omega, Nat.cast_sub hwv,
        abs_of_nonneg (sub_nonneg.2 (by exact_mod_cast hwv))]
  exact_mod_cast (hdist.trans_le (h.trans (mul_le_mul_of_nonneg_left
    (real_logb_two_le_nat_log_two_succ hn) (Nat.cast_nonneg d)))).trans_eq (Nat.cast_mul ..).symm

/-- **Real-valued $d \log_2 n$ approximation window bridge:** if `f` is mildly hard on average to
approximate within the upper-rounded integer window `fun n => d * (Nat.log 2 n + 1)`, then `f` is
mildly hard on average to approximate within the real-valued window $d \log_2 n$ of
[Liu and Pass, Definition 2.5 and Theorem 3.1 (c), pp. 8–9 of arXiv:2009.11514v1][LiuPass2020]. -/
theorem MildlyHardOnAverageToApprox.eventually_real_abs_sub_le {d : ℕ} {f : List Bool → ℕ}
    (h : MildlyHardOnAverageToApprox (fun n => d * (Nat.log 2 n + 1)) f) :
    MildlyHardOnAverageWith fun n x v =>
      decide (|(v : ℝ) - (f x : ℝ)| ≤ (d : ℝ) * Real.logb 2 (n : ℝ)) :=
  MildlyHardOnAverageWith.mono ((eventually_ge_atTop 1).mono fun _ hn1 _ _ _ hv => by
    rw [decide_eq_true_eq] at hv ⊢
    exact nat_dist_le_mul_log_two_succ_of_abs_sub_le_mul_logb hn1 hv) h

/-! ### Negative-side nonvacuity lemmas for the constant zero function -/

/-- The constant zero function `fun _ => 0` is **not** `MildlyHardOnAverageIO`, because the
constant zero polynomial-time heuristic succeeds with probability $1$ on every input length. -/
theorem not_mildlyHardOnAverageIO_zero : ¬ MildlyHardOnAverageIO (fun _ => 0) :=
  MildlyHardOnAverageFor.not_of_admissible_pure (Quant := (Filter.Frequently · atTop))
    (Admissible := IsDetPolyTime encNat) (correct := fun _ _ v => decide (v = 0))
    (fun h => nomatch h.exists)
    (IsDetPolyTime.of_computableInPolyTime (ComputableInPolyTime.const 0))
    (.of_forall fun _ _ _ => rfl)

/-- The constant zero function `fun _ => 0` is not `MildlyHardOnAverageDet`. -/
theorem not_mildlyHardOnAverageDet_zero : ¬ MildlyHardOnAverageDet (fun _ => 0) :=
  fun h => not_mildlyHardOnAverageIO_zero h.mildlyHardOnAverageIO

/-- The constant zero function `fun _ => 0` is not `MildlyHardOnAverage`. -/
theorem not_mildlyHardOnAverage_zero : ¬ MildlyHardOnAverage (fun _ => 0) :=
  fun h => not_mildlyHardOnAverageIO_zero h.mildlyHardOnAverageIO

/-- The constant zero function `fun _ => 0` is not `MildlyHardOnAverageToApproxIO g` for any error
function `g`. -/
theorem not_mildlyHardOnAverageToApproxIO_zero (g : ℕ → ℕ) :
    ¬ MildlyHardOnAverageToApproxIO g (fun _ => 0) :=
  fun h => not_mildlyHardOnAverageIO_zero h.mildlyHardOnAverageIO

/-- The constant zero function `fun _ => 0` is not `MildlyHardOnAverageToApproxDet g` for any error
function `g`. -/
theorem not_mildlyHardOnAverageToApproxDet_zero (g : ℕ → ℕ) :
    ¬ MildlyHardOnAverageToApproxDet g (fun _ => 0) :=
  fun h => not_mildlyHardOnAverageIO_zero h.mildlyHardOnAverageDet.mildlyHardOnAverageIO

/-- The constant zero function `fun _ => 0` is not `MildlyHardOnAverageToApprox g` for any error
function `g`. -/
theorem not_mildlyHardOnAverageToApprox_zero (g : ℕ → ℕ) :
    ¬ MildlyHardOnAverageToApprox g (fun _ => 0) :=
  fun h => not_mildlyHardOnAverageIO_zero h.mildlyHardOnAverage.mildlyHardOnAverageIO

/-- The constant zero function `fun _ => 0` is not `MildlyHardOnAverageToOneSidedApprox g` for any
error function `g`. -/
theorem not_mildlyHardOnAverageToOneSidedApprox_zero (g : ℕ → ℕ) :
    ¬ MildlyHardOnAverageToOneSidedApprox g (fun _ => 0) :=
  fun h => not_mildlyHardOnAverageIO_zero h.mildlyHardOnAverage.mildlyHardOnAverageIO

end Cslib.Complexity
