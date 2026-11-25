/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Mechanism.VCG
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Taxation principle, weak monotonicity, and cyclic monotonicity

Fundamental characterizations of dominant-strategy incentive compatibility (DSIC) for general
direct-revelation mechanisms `Cslib.GameTheory.Mechanism ι Ω` on valuation domains
`V : ι → Set (Ω → ℝ)` ([Nisan2007], §9.5.1–9.5.2, pp. 225–227).

* **Taxation principle** ([Nisan2007], Proposition 9.27, p. 226): `M` is DSIC on `V` if and only if,
  for every agent `i` and others' reports `b₋ᵢ` in the domain, there exist outcome-dependent prices
  `p : Ω → ℝ` such that `i`'s payment is `p (M.outcome (v, b₋ᵢ))` and `M.outcome (v, b₋ᵢ)`
  maximizes `v a - p a` over the range `{M.outcome (v', b₋ᵢ) | v' ∈ V i}`.
* **Weak monotonicity (WMON)** ([Nisan2007], Definition 9.28, p. 227): a social choice rule `f` is
  weakly monotone on `V` when changing a single player's valuation from `v` to `v'` with
  `a = f(v, b₋ᵢ)` and `a' = f(v', b₋ᵢ)` implies `v(a) - v(a') ≥ v'(a) - v'(a')`.
  We prove the necessity half of [Nisan2007], Theorem 9.29 (p. 227): every DSIC-implementable rule
  is weakly monotone. The sufficiency half on convex domains (Saks–Yu, stated without proof in
  [Nisan2007], p. 227) is not formalized here and remains open.
* **Cyclic monotonicity**: extending WMON from 2-cycles to finite cycles of arbitrary length yields
  an exact characterization of DSIC implementability on every domain `V` and every outcome type `Ω`
  (with no finiteness or convexity assumption), via Rockafellar/Rochet's `sInf`-over-chains pricing
  construction.

## Main definitions

* `Mechanism.IsImplementableOn`, `Mechanism.IsImplementable`: existence of a payment rule making an
  outcome rule DSIC (on domains `V`, or universally).
* `Mechanism.IsWeaklyMonotoneOn`, `Mechanism.IsWeaklyMonotone`: weak monotonicity (WMON).
* `Mechanism.IsCyclicallyMonotoneOn`: nonnegativity of cyclic gain sums for each agent.

## Main results

* `Mechanism.isDSICOn_iff_taxation`, `Mechanism.isDSIC_iff_taxation`: the taxation principle
  ([Nisan2007], Proposition 9.27, p. 226).
* `Mechanism.isImplementableOn_iff_exists_prices`: price-menu characterization of implementability.
* `Mechanism.IsDSICOn.isWeaklyMonotoneOn`, `Mechanism.IsImplementableOn.isWeaklyMonotoneOn`,
  `Mechanism.IsImplementable.isWeaklyMonotone`: necessity of weak monotonicity ([Nisan2007],
  Theorem 9.29, necessity half, p. 227).
* `Mechanism.isImplementableOn_iff_isCyclicallyMonotoneOn`: cyclic monotonicity characterizes
  DSIC-implementability on arbitrary domains and arbitrary outcome types.
* `Mechanism.IsCyclicallyMonotoneOn.isWeaklyMonotoneOn`: weak monotonicity is the length-2 cycle
  case of cyclic monotonicity.

## References

* [N. Nisan, *Introduction to Mechanism Design (for Computer Scientists)*][Nisan2007]
-/

public section

namespace Cslib.GameTheory.Mechanism

variable {ι Ω : Type*}

/-- An outcome rule `f` is **DSIC-implementable on `V`** if there is a payment rule `p` making
`⟨f, p⟩` dominant-strategy incentive compatible on the valuation domains `V`. -/
@[expose] def IsImplementableOn [DecidableEq ι] (f : (ι → Ω → ℝ) → Ω)
    (V : ι → Set (Ω → ℝ)) : Prop :=
  ∃ p : (ι → Ω → ℝ) → ι → ℝ, (⟨f, p⟩ : Mechanism ι Ω).IsDSICOn V

/-- An outcome rule `f` is **DSIC-implementable** (on the unrestricted domain `ℝ^Ω`) if there is a
payment rule `p` making `⟨f, p⟩` DSIC. -/
@[expose] def IsImplementable [DecidableEq ι] (f : (ι → Ω → ℝ) → Ω) : Prop :=
  ∃ p : (ι → Ω → ℝ) → ι → ℝ, (⟨f, p⟩ : Mechanism ι Ω).IsDSIC

/-- A universally implementable rule is implementable on every domain. -/
theorem IsImplementable.isImplementableOn [DecidableEq ι] {f : (ι → Ω → ℝ) → Ω}
    (hf : IsImplementable f) (V : ι → Set (Ω → ℝ)) : IsImplementableOn f V :=
  let ⟨p, hp⟩ := hf
  ⟨p, hp.isDSICOn V⟩

/-- On the full valuation domains `fun _ => Set.univ`, `IsImplementableOn` agrees with
`IsImplementable`. -/
theorem isImplementableOn_univ_iff [DecidableEq ι] {f : (ι → Ω → ℝ) → Ω} :
    IsImplementableOn f (fun _ => Set.univ) ↔ IsImplementable f := by
  simp only [IsImplementableOn, IsImplementable, isDSICOn_univ_iff]

private theorem update_mem [DecidableEq ι] {V : ι → Set (Ω → ℝ)} {b : ι → Ω → ℝ} {i : ι}
    {v : Ω → ℝ} (hb : ∀ j, j ≠ i → b j ∈ V j) (hv : v ∈ V i) :
    ∀ j, Function.update b i v j ∈ V j := fun j => by
  rcases eq_or_ne j i with rfl | hji
  · simpa [Function.update_self] using hv
  · simpa [Function.update_of_ne hji] using hb j hji

/-! ### Taxation principle (Nisan 2007, Proposition 9.27) -/

/-- **Taxation principle** ([Nisan2007], Proposition 9.27, §9.5.1, p. 226): a direct-revelation
mechanism `M` is DSIC on the domains `V` if and only if, for every agent `i` and every tuple of
others' reports `b₋ᵢ` in the domain, there exist prices `p : Ω → ℝ` depending only on the outcome
such that (i) agent `i` pays `p(M.outcome(v, b₋ᵢ))` for all `v ∈ V i`, and (ii) `M.outcome(v, b₋ᵢ)`
maximizes `v a - p a` over the induced range `{M.outcome(v', b₋ᵢ) | v' ∈ V i}`. -/
theorem isDSICOn_iff_taxation [DecidableEq ι] {M : Mechanism ι Ω} {V : ι → Set (Ω → ℝ)} :
    M.IsDSICOn V ↔
      ∀ (i : ι) (b : ι → Ω → ℝ), (∀ j, j ≠ i → b j ∈ V j) →
        ∃ p : Ω → ℝ,
          (∀ v ∈ V i,
            M.payment (Function.update b i v) i = p (M.outcome (Function.update b i v))) ∧
          (∀ v ∈ V i, ∀ a ∈ (fun v' => M.outcome (Function.update b i v')) '' V i,
            v a - p a ≤
              v (M.outcome (Function.update b i v)) - p (M.outcome (Function.update b i v))) := by
  classical
  constructor
  · intro hM i b hb
    let p : Ω → ℝ := fun a =>
      if h : ∃ v ∈ V i, M.outcome (Function.update b i v) = a then
        M.payment (Function.update b i h.choose) i
      else 0
    have hp : ∀ v ∈ V i,
        M.payment (Function.update b i v) i = p (M.outcome (Function.update b i v)) := by
      intro v hv
      have hex : ∃ w ∈ V i, M.outcome (Function.update b i w) =
          M.outcome (Function.update b i v) := ⟨v, hv, rfl⟩
      simp only [p, hex, ↓reduceDIte]
      obtain ⟨hw, hout⟩ := hex.choose_spec
      have h1 := hM i (Function.update b i hex.choose) v (update_mem hb hw) hv
      have h2 := hM i (Function.update b i v) hex.choose (update_mem hb hv) hw
      simp only [utility, Function.update_idem, hout] at h1 h2
      linarith
    refine ⟨p, hp, ?_⟩
    rintro v hv _ ⟨v', hv', rfl⟩
    rw [← hp v' hv', ← hp v hv]
    simpa only [utility, Function.update_idem] using
      hM i (Function.update b i v') v (update_mem hb hv') hv
  · intro h i b v hb hv
    obtain ⟨p, hp, hmax⟩ := h i b fun j _ => hb j
    have hupd : Function.update b i (b i) = b := Function.update_eq_self i b
    have h1 : M.payment b i = p (M.outcome b) := hupd ▸ hp (b i) (hb i)
    simpa only [utility, h1, hp v hv] using
      hmax v hv (M.outcome b) ⟨b i, hb i, congrArg M.outcome hupd⟩

/-- **Taxation principle on unrestricted domains** ([Nisan2007], Proposition 9.27, §9.5.1, p. 226):
specialization of `isDSICOn_iff_taxation` to `V i = Set.univ`. -/
theorem isDSIC_iff_taxation [DecidableEq ι] {M : Mechanism ι Ω} :
    M.IsDSIC ↔
      ∀ (i : ι) (b : ι → Ω → ℝ),
        ∃ p : Ω → ℝ,
          (∀ v : Ω → ℝ,
            M.payment (Function.update b i v) i = p (M.outcome (Function.update b i v))) ∧
          (∀ v : Ω → ℝ, ∀ a ∈ Set.range (fun v' => M.outcome (Function.update b i v')),
            v a - p a ≤
              v (M.outcome (Function.update b i v)) - p (M.outcome (Function.update b i v))) := by
  rw [← isDSICOn_univ_iff, isDSICOn_iff_taxation]
  simp only [Set.mem_univ, Set.image_univ, forall_const]

/-- **Price-menu characterization of implementability**: an outcome rule `f` is DSIC-implementable
on `V` if and only if, for each agent `i` and valid reports `b₋ᵢ` of the others, there exist
outcome prices `p : Ω → ℝ` such that `f(v, b₋ᵢ)` maximizes `v a - p a` over the range
`{f(v', b₋ᵢ) | v' ∈ V i}`. -/
theorem isImplementableOn_iff_exists_prices [DecidableEq ι] {f : (ι → Ω → ℝ) → Ω}
    {V : ι → Set (Ω → ℝ)} :
    IsImplementableOn f V ↔
      ∀ (i : ι) (b : ι → Ω → ℝ), (∀ j, j ≠ i → b j ∈ V j) →
        ∃ p : Ω → ℝ, ∀ v ∈ V i,
          ∀ a ∈ (fun v' => f (Function.update b i v')) '' V i,
            v a - p a ≤ v (f (Function.update b i v)) - p (f (Function.update b i v)) := by
  classical
  constructor
  · rintro ⟨pay, hM⟩ i b hb
    obtain ⟨p, -, hmax⟩ := (isDSICOn_iff_taxation.1 hM) i b hb
    exact ⟨p, hmax⟩
  · intro h
    let priceOf : (i : ι) → (ι → Ω → ℝ) → Ω → ℝ := fun i b =>
      if hb : ∀ j, j ≠ i → b j ∈ V j then (h i b hb).choose else 0
    let pay : (ι → Ω → ℝ) → ι → ℝ := fun b i => priceOf i (Function.update b i 0) (f b)
    refine ⟨pay, isDSICOn_iff_taxation.2 fun i b hb => ?_⟩
    have hb0 : ∀ j, j ≠ i → (Function.update b i 0) j ∈ V j := fun j hj => by
      rw [Function.update_of_ne hj]
      exact hb j hj
    refine ⟨priceOf i (Function.update b i 0), fun v _ => by simp only [pay, Function.update_idem],
      fun v hv a ha => ?_⟩
    dsimp only [priceOf]
    rw [dite_eq_left hb0]
    simpa only [Function.update_idem] using
      (h i (Function.update b i 0) hb0).choose_spec v hv a
        (by simpa only [Function.update_idem] using ha)

/-! ### Weak monotonicity (Nisan 2007, Definition 9.28 & Theorem 9.29 necessity) -/

/-- **Weak monotonicity (WMON) on valuation domains `V`** ([Nisan2007], Definition 9.28, §9.5.2,
p. 227): changing player `i`'s report from `v` to `v'` (holding `b₋ᵢ` fixed in `V`) satisfies
`v(a) - v(a') ≥ v'(a) - v'(a')` where `a = f(v, b₋ᵢ)` and `a' = f(v', b₋ᵢ)`. Dropping the textbook's
side condition `a ≠ a'` is equivalent because `a = a'` reduces to `0 ≤ 0`. -/
@[expose] def IsWeaklyMonotoneOn [DecidableEq ι] (f : (ι → Ω → ℝ) → Ω)
    (V : ι → Set (Ω → ℝ)) : Prop :=
  ∀ (i : ι) (b : ι → Ω → ℝ) (v v' : Ω → ℝ),
    (∀ j, j ≠ i → b j ∈ V j) → v ∈ V i → v' ∈ V i →
    v' (f (Function.update b i v)) - v' (f (Function.update b i v')) ≤
      v (f (Function.update b i v)) - v (f (Function.update b i v'))

/-- **Weak monotonicity (WMON)** on the unrestricted domain `ℝ^Ω` ([Nisan2007], Definition 9.28,
§9.5.2, p. 227). -/
@[expose] def IsWeaklyMonotone [DecidableEq ι] (f : (ι → Ω → ℝ) → Ω) : Prop :=
  ∀ (i : ι) (b : ι → Ω → ℝ) (v v' : Ω → ℝ),
    v' (f (Function.update b i v)) - v' (f (Function.update b i v')) ≤
      v (f (Function.update b i v)) - v (f (Function.update b i v'))

/-- On the full domains `fun _ => Set.univ`, `IsWeaklyMonotoneOn` coincides with
`IsWeaklyMonotone`. -/
theorem isWeaklyMonotoneOn_univ_iff [DecidableEq ι] {f : (ι → Ω → ℝ) → Ω} :
    IsWeaklyMonotoneOn f (fun _ => Set.univ) ↔ IsWeaklyMonotone f := by
  simp only [IsWeaklyMonotoneOn, IsWeaklyMonotone, Set.mem_univ, forall_const]

/-- **Necessity of weak monotonicity** ([Nisan2007], Theorem 9.29, first part, §9.5.2, p. 227):
the outcome rule of every DSIC mechanism on `V` satisfies WMON on `V`. (The sufficiency half of
Theorem 9.29 for convex domains is not formalized here.) -/
theorem IsDSICOn.isWeaklyMonotoneOn [DecidableEq ι] {M : Mechanism ι Ω} {V : ι → Set (Ω → ℝ)}
    (hM : M.IsDSICOn V) : IsWeaklyMonotoneOn M.outcome V := by
  intro i b v v' hb hv hv'
  have h1 := hM i (Function.update b i v') v (update_mem hb hv') hv
  have h2 := hM i (Function.update b i v) v' (update_mem hb hv) hv'
  simp only [utility, Function.update_idem] at h1 h2
  linarith

/-- Necessity of weak monotonicity for implementable outcome rules on `V` ([Nisan2007],
Theorem 9.29, first part, §9.5.2, p. 227). -/
theorem IsImplementableOn.isWeaklyMonotoneOn [DecidableEq ι] {f : (ι → Ω → ℝ) → Ω}
    {V : ι → Set (Ω → ℝ)} (hf : IsImplementableOn f V) : IsWeaklyMonotoneOn f V :=
  let ⟨_, hM⟩ := hf
  hM.isWeaklyMonotoneOn

/-- Necessity of weak monotonicity on unrestricted domains ([Nisan2007], Theorem 9.29, first part,
§9.5.2, p. 227). -/
theorem IsImplementable.isWeaklyMonotone [DecidableEq ι] {f : (ι → Ω → ℝ) → Ω}
    (hf : IsImplementable f) : IsWeaklyMonotone f :=
  isWeaklyMonotoneOn_univ_iff.1 (hf.isImplementableOn _).isWeaklyMonotoneOn

/-- The outcome rule of an unrestricted DSIC mechanism is weakly monotone. -/
theorem IsDSIC.isWeaklyMonotone [DecidableEq ι] {M : Mechanism ι Ω} (hM : M.IsDSIC) :
    IsWeaklyMonotone M.outcome :=
  ⟨M.payment, hM⟩ |> IsImplementable.isWeaklyMonotone

/-! ### Cyclic monotonicity (exact characterization of DSIC implementability) -/

/-- **Cyclic monotonicity** on valuation domains `V`: for every agent `i`, others' valid reports
`b₋ᵢ`, and every nonempty finite cycle `v : Fin (k + 1) → (Ω → ℝ)` of valuations in `V i`, the
sum `∑ t, (v t (f(v t, b₋ᵢ)) - v t (f(v (t + 1), b₋ᵢ)))` (with indices modulo `k + 1`) is
nonnegative. For `k = 1` (2-cycles), this reduces to `IsWeaklyMonotoneOn`. -/
@[expose] def IsCyclicallyMonotoneOn [DecidableEq ι] (f : (ι → Ω → ℝ) → Ω)
    (V : ι → Set (Ω → ℝ)) : Prop :=
  ∀ (i : ι) (b : ι → Ω → ℝ), (∀ j, j ≠ i → b j ∈ V j) →
    ∀ (k : ℕ) (v : Fin (k + 1) → Ω → ℝ), (∀ t, v t ∈ V i) →
      0 ≤ ∑ t : Fin (k + 1),
        (v t (f (Function.update b i (v t))) - v t (f (Function.update b i (v (t + 1)))))

/-- Weak monotonicity is the 2-cycle (`k = 1`) case of cyclic monotonicity. -/
theorem IsCyclicallyMonotoneOn.isWeaklyMonotoneOn [DecidableEq ι] {f : (ι → Ω → ℝ) → Ω}
    {V : ι → Set (Ω → ℝ)} (hf : IsCyclicallyMonotoneOn f V) : IsWeaklyMonotoneOn f V := by
  intro i b v v' hb hv hv'
  have hc := hf i b hb 1 (fun t => if t = 0 then v else v') fun t => by
    fin_cases t
    exacts [hv, hv']
  rw [Fin.sum_univ_two, show (0 : Fin 2) + 1 = 1 from rfl,
    show (1 : Fin 2) + 1 = 0 from rfl] at hc
  simp only [↓reduceIte, one_ne_zero] at hc
  linarith

private def chainWeight (g : (Ω → ℝ) → Ω) (v₀ : Ω → ℝ) (n : ℕ)
    (u : Fin (n + 1) → Ω → ℝ) : ℝ :=
  (∑ t : Fin n, (u t.castSucc (g (u t.castSucc)) - u t.castSucc (g (u t.succ)))) +
    (u (Fin.last n) (g (u (Fin.last n))) - u (Fin.last n) (g v₀))

private def consSeq {n : ℕ} (v : Ω → ℝ) (u : Fin (n + 1) → Ω → ℝ) : Fin (n + 2) → Ω → ℝ :=
  Fin.cases v u

private def snocSeq {n : ℕ} (u : Fin (n + 1) → Ω → ℝ) (v₀ : Ω → ℝ) : Fin (n + 2) → Ω → ℝ :=
  fun t => if h : t.val < n + 1 then u ⟨t.val, h⟩ else v₀

private theorem chainWeight_cons (g : (Ω → ℝ) → Ω) (v₀ v : Ω → ℝ) (n : ℕ)
    (u : Fin (n + 1) → Ω → ℝ) :
    chainWeight g v₀ (n + 1) (consSeq v u) =
      (v (g v) - v (g (u 0))) + chainWeight g v₀ n u := by
  simp only [chainWeight, Fin.sum_univ_succ, consSeq, ← Fin.succ_last, Fin.castSucc_zero,
    Fin.cases_zero, Fin.cases_succ, Fin.castSucc_succ]
  ring

private theorem cycleSum_snoc (g : (Ω → ℝ) → Ω) (v₀ : Ω → ℝ) (n : ℕ)
    (u : Fin (n + 1) → Ω → ℝ) :
    ∑ t : Fin (n + 2),
      (snocSeq u v₀ t (g (snocSeq u v₀ t)) -
        snocSeq u v₀ t (g (snocSeq u v₀ (t + 1)))) =
      chainWeight g v₀ n u + (v₀ (g v₀) - v₀ (g (u 0))) := by
  have hcast : ∀ s : Fin (n + 1), snocSeq u v₀ s.castSucc = u s := fun s => by
    simp only [snocSeq, Fin.val_castSucc, s.isLt, ↓reduceDIte, Fin.eta]
  have hlast_eq : snocSeq u v₀ (Fin.last (n + 1)) = v₀ := by
    simp only [snocSeq, Fin.val_last, lt_self_iff_false, ↓reduceDIte]
  rw [Fin.sum_univ_castSucc, Fin.last_add_one, ← Fin.castSucc_zero, hlast_eq, hcast 0]
  congr 1
  rw [Fin.sum_univ_castSucc, chainWeight]
  congr 1
  · refine Finset.sum_congr rfl fun t _ => ?_
    rw [Fin.coeSucc_eq_succ, hcast t.castSucc, show t.castSucc.succ = t.succ.castSucc from rfl,
      hcast t.succ]
  · rw [Fin.coeSucc_eq_succ, hcast (Fin.last n), Fin.succ_last, hlast_eq]

/-- **Cyclic monotonicity characterizes DSIC implementability** (the Rockafellar–Rochet
characterization, attributed to Rochet 1987; proved here without finiteness or convexity
assumptions via an `sInf`-over-chains potential): an outcome rule `f` is DSIC-implementable on
arbitrary domains `V : ι → Set (Ω → ℝ)` if and only if `f` is cyclically monotone on `V`. -/
theorem isImplementableOn_iff_isCyclicallyMonotoneOn [DecidableEq ι]
    {f : (ι → Ω → ℝ) → Ω} {V : ι → Set (Ω → ℝ)} :
    IsImplementableOn f V ↔ IsCyclicallyMonotoneOn f V := by
  rw [isImplementableOn_iff_exists_prices]
  constructor
  · intro h i b hb k v hv
    obtain ⟨p, hp⟩ := h i b hb
    set g : (Ω → ℝ) → Ω := fun u => f (Function.update b i u)
    have hsum : ∑ t : Fin (k + 1), (p (g (v t)) - p (g (v (t + 1)))) ≤
        ∑ t : Fin (k + 1), (v t (g (v t)) - v t (g (v (t + 1)))) :=
      Finset.sum_le_sum fun t _ => by
        linarith [hp (v t) (hv t) (g (v (t + 1))) ⟨v (t + 1), hv (t + 1), rfl⟩]
    have hshift : ∑ t : Fin (k + 1), p (g (v (t + 1))) = ∑ t : Fin (k + 1), p (g (v t)) := by
      conv_lhs => simp only [Fin.sum_univ_castSucc, Fin.last_add_one, Fin.coeSucc_eq_succ]
      rw [add_comm]
      exact (Fin.sum_univ_succ fun t => p (g (v t))).symm
    rw [Finset.sum_sub_distrib, hshift, sub_self] at hsum
    exact hsum
  · intro hcyc i b hb
    by_cases hne : (V i).Nonempty
    · obtain ⟨v₀, hv₀⟩ := hne
      let g : (Ω → ℝ) → Ω := fun u => f (Function.update b i u)
      let paths (a : Ω) : Set ℝ :=
        {r | ∃ (n : ℕ) (u : Fin (n + 1) → Ω → ℝ),
          (∀ t, u t ∈ V i) ∧ g (u 0) = a ∧ r = chainWeight g v₀ n u}
      have hne_paths : ∀ v ∈ V i, (paths (g v)).Nonempty := fun v hv =>
        ⟨v (g v) - v (g v₀), 0, fun _ => v, fun _ => hv, rfl, by
          simp only [chainWeight, Finset.univ_eq_empty, Finset.sum_empty, zero_add]⟩
      have hbdd : ∀ a : Ω, BddBelow (paths a) := fun a => by
        refine ⟨v₀ a - v₀ (g v₀), ?_⟩
        rintro _ ⟨n, u, hu, hhead, rfl⟩
        have hsnoc : ∀ t : Fin (n + 2), snocSeq u v₀ t ∈ V i := fun t => by
          simp only [snocSeq]
          split_ifs with h
          · exact hu ⟨t.val, h⟩
          · exact hv₀
        have hc := hcyc i b hb (n + 1) (snocSeq u v₀) hsnoc
        rw [cycleSum_snoc g v₀ n u, hhead] at hc
        linarith
      refine ⟨fun a => sInf (paths a), ?_⟩
      rintro v hv _ ⟨v', hv', rfl⟩
      suffices sInf (paths (g v)) - (v (g v) - v (g v')) ≤ sInf (paths (g v')) by linarith
      refine le_csInf (hne_paths v' hv') ?_
      rintro _ ⟨n, u, hu, hhead, rfl⟩
      have hcons : (v (g v) - v (g v')) + chainWeight g v₀ n u ∈ paths (g v) :=
        ⟨n + 1, consSeq v u, fun t => Fin.cases hv hu t, rfl, by rw [chainWeight_cons, hhead]⟩
      linarith [csInf_le (hbdd (g v)) hcons]
    · exact ⟨0, fun v hv => absurd ⟨v, hv⟩ hne⟩

end Cslib.GameTheory.Mechanism
