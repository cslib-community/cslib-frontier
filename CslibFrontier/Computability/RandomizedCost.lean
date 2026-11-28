/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Threshold
public import CslibFrontier.Probability.IID
public import CslibFrontier.Probability.Minimax
public import Mathlib.Basic.NNReal.Basic
import CslibFrontier.Foundations.Data.ENat.IInf
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.ToReal

/-!
# Model-generic public-coin randomized cost, minimax duality, and amplification

Many concrete models of randomized computation — two-party communication protocols,
number-on-forehead multiparty protocols, randomized decision trees, and coin-fixed cell-probe
schemes — share the same relationship between deterministic strategies, public-coin mixtures,
input distributions, and repetition. A deterministic model is given by an evaluation map
`eval : M → X → Z` and a worst-case natural-number cost `cost : M → ℕ` (`Cslib.RandomizedCost`).

This module provides that model-independent library infrastructure once (background:
[Yao1977, vonNeumann1928]):

* **Public-coin and distributional complexity (`PMF`):** drawing a strategy from `μ : PMF M` gives
  worst-case support cost `PMF.maxCost C.cost μ`, per-input failure probability `C.errorProb`,
  promise correctness `C.Solves`, and least cost `C.ecomplexity` in `ℕ∞`, paired with deterministic
  `C.detComplexity` and distributional `C.distributionalComplexity`. Averaging gives the easy
  direction on arbitrary promise sets (`Solves.exists_distributionalError_le`,
  `distributionalComplexity_le_ecomplexity`), and finite-game minimax duality gives the converse on
  finite promise sets (`ecomplexity_le_of_forall_distributionalComplexity_le`,
  `ecomplexity_eq_iSup_distributionalComplexity`).
* **Majority error amplification:** when strategies for a Boolean function can be sequenced via
  `runAll` with additive cost, taking the strict majority of `2 r` independent draws reduces error
  `ε ≤ 1 / 2` to `(4 ε (1 - ε)) ^ r` at `2 r` times the cost (`Solves.amplify`,
  `ecomplexity_le_two_mul_mul`).
* **Finitely supported mixtures (`StdSimplex`):** `C.simplexComplexity` and
  `C.simplexDistributionalComplexity` package `ℕ`-valued worst-case complexity over
  `Convexity.StdSimplex` together with attainment and minimax equality
  (`simplexComplexity_eq_iSup_simplexDistributionalComplexity`,
  `exists_simplexDistributionalComplexity_eq_simplexComplexity`).
* **Zero-error coin-fixing expectation:** when a randomized execution on input `x` decomposes as
  `μ.bind fun m => PMF.pure (evalOut m x, costAt m x)`, expected cost equals the `μ`-average of
  `costAt · x` (`tsum_snd_eq_of_bind_pure`) and some deterministic `m ∈ μ.support` preserves
  zero-error correctness across `A` while matching expected cost under any input distribution
  (`exists_mem_support_of_coinFixing`, `exists_mem_support_tsum_mul_le_of_coinFixing`).

## Main definitions

* `Cslib.RandomizedCost`: deterministic evaluation `eval : M → X → Z` paired with worst-case cost
  `cost : M → ℕ`.
* `Cslib.RandomizedCost.DetSolves`, `Cslib.RandomizedCost.detComplexity`: deterministic promise
  correctness and least cost in `ℕ∞`.
* `Cslib.RandomizedCost.distributionalError`, `Cslib.RandomizedCost.distributionalComplexity`:
  distributional error and least cost under `ν : PMF X`.
* `Cslib.RandomizedCost.errorProb`, `Cslib.RandomizedCost.Solves`,
  `Cslib.RandomizedCost.ecomplexity`, `Cslib.RandomizedCost.ecomplexityFun`: public-coin error,
  promise correctness, and complexity in `ℕ∞`.
* `Cslib.RandomizedCost.amplify`: strict majority of `2 r` independent draws combined by `runAll`.
* `Cslib.RandomizedCost.simplexComplexity`, `Cslib.RandomizedCost.simplexDistributionalComplexity`:
  `ℕ`-valued randomized and distributional complexity over `Convexity.StdSimplex`.

## Main results

* `Cslib.RandomizedCost.ecomplexity_le_detComplexity`,
  `Cslib.RandomizedCost.ecomplexity_comap_le`: deterministic embedding and simulation monotonicity.
* `Cslib.RandomizedCost.Solves.exists_distributionalError_le`,
  `Cslib.RandomizedCost.distributionalComplexity_le_ecomplexity`: averaging lower-bound direction.
* `Cslib.RandomizedCost.ecomplexity_le_of_forall_distributionalComplexity_le`,
  `Cslib.RandomizedCost.ecomplexity_eq_iSup_distributionalComplexity`,
  `Cslib.RandomizedCost.ecomplexityFun_eq_iSup_distributionalComplexity`: minimax converse and
  supremum equality on `PMF`.
* `Cslib.RandomizedCost.Solves.amplify`, `Cslib.RandomizedCost.ecomplexity_le_two_mul_mul`,
  `Cslib.RandomizedCost.ecomplexityFun_le_two_mul_mul_one_third`: majority error amplification.
* `Cslib.RandomizedCost.simplexDistributionalComplexity_le_simplexComplexity`,
  `Cslib.RandomizedCost.simplexComplexity_eq_iSup_simplexDistributionalComplexity`,
  `Cslib.RandomizedCost.exists_simplexDistributionalComplexity_eq_simplexComplexity`: minimax
  duality on `Convexity.StdSimplex`.
* `Cslib.RandomizedCost.tsum_snd_eq_of_bind_pure`,
  `Cslib.RandomizedCost.exists_mem_support_of_coinFixing`,
  `Cslib.RandomizedCost.exists_mem_support_tsum_mul_le_of_coinFixing`: coin-fixed expected cost and
  zero-error averaging.

## References

* [A. C.-C. Yao, *Probabilistic computations: toward a unified measure of complexity*][Yao1977]
* [J. von Neumann, *Zur Theorie der Gesellschaftsspiele*][vonNeumann1928]
-/

public section

open scoped ENNReal NNReal

namespace Cslib

open Convexity Probability

universe u v w

/-- A deterministic model of strategies `M` from inputs `X` to outputs `Z` with worst-case
natural-number cost `cost : M → ℕ`. -/
structure RandomizedCost (M : Type u) (X : Type v) (Z : Type w) where
  /-- Output of strategy `m` on input `x`. -/
  eval : M → X → Z
  /-- Worst-case natural-number cost of strategy `m`. -/
  cost : M → ℕ

namespace RandomizedCost

section PublicCoin

variable {M : Type u} {X : Type v} {Z : Type w}

/-- Deterministic strategy `m` solves `R` on promise set `A`. -/
@[expose] def DetSolves (C : RandomizedCost M X Z) (m : M) (R : X → Z → Prop) (A : Set X) : Prop :=
  ∀ x ∈ A, R x (C.eval m x)

/-- Least cost in `ℕ∞` of a deterministic strategy solving `R` on `A`, or `⊤` if none exists. -/
@[expose] noncomputable def detComplexity (C : RandomizedCost M X Z) (R : X → Z → Prop)
    (A : Set X) : ℕ∞ :=
  ⨅ m : {m : M // C.DetSolves m R A}, (C.cost m.val : ℕ∞)

/-- Probability that deterministic strategy `m` errs against `R` on an input drawn from `ν`. -/
@[expose] noncomputable def distributionalError (C : RandomizedCost M X Z) (m : M) (ν : PMF X)
    (R : X → Z → Prop) : ℝ :=
  PMF.errorProb (fun x m => R x (C.eval m x)) ν m

/-- Least cost in `ℕ∞` of a deterministic strategy erring with probability at most `ε` under `ν`. -/
@[expose] noncomputable def distributionalComplexity (C : RandomizedCost M X Z) (ε : ℝ)
    (R : X → Z → Prop) (ν : PMF X) : ℕ∞ :=
  ⨅ m : {m : M // C.distributionalError m ν R ≤ ε}, (C.cost m.val : ℕ∞)

/-- Probability that a strategy drawn from `μ` errs against `R` on input `x`. -/
@[expose] noncomputable def errorProb (C : RandomizedCost M X Z) (μ : PMF M) (R : X → Z → Prop)
    (x : X) : ℝ :=
  PMF.errorProb (fun m x => R x (C.eval m x)) μ x

/-- Public-coin mixture `μ` solves `R` on `A` with worst-case error at most `ε`. -/
@[expose] def Solves (C : RandomizedCost M X Z) (μ : PMF M) (ε : ℝ) (R : X → Z → Prop)
    (A : Set X) : Prop :=
  ∀ x ∈ A, C.errorProb μ R x ≤ ε

/-- Least worst-case support cost in `ℕ∞` of a public-coin mixture solving `R` on `A` with error
`ε`, or `⊤` if none exists. -/
@[expose] noncomputable def ecomplexity (C : RandomizedCost M X Z) (ε : ℝ) (R : X → Z → Prop)
    (A : Set X) : ℕ∞ :=
  ⨅ μ : {μ : PMF M // C.Solves μ ε R A}, PMF.maxCost C.cost μ.val

/-- Public-coin complexity of computing a total function `f : X → Z` with error `ε`. -/
@[expose] noncomputable def ecomplexityFun (C : RandomizedCost M X Z) (ε : ℝ) (f : X → Z) : ℕ∞ :=
  C.ecomplexity ε (fun x z => f x = z) Set.univ

variable {C : RandomizedCost M X Z} {μ : PMF M} {m : M} {R : X → Z → Prop} {A A' : Set X}
  {ν : PMF X} {ε ε' : ℝ} {x : X}

theorem distributionalComplexity_le_cost (hm : C.distributionalError m ν R ≤ ε) :
    C.distributionalComplexity ε R ν ≤ C.cost m :=
  ENat.iInf_subtype_natCast_le hm

theorem le_distributionalComplexity_iff {k : ℕ∞} :
    k ≤ C.distributionalComplexity ε R ν ↔
      ∀ m : M, C.distributionalError m ν R ≤ ε → k ≤ C.cost m :=
  ENat.le_iInf_subtype_natCast_iff

theorem distributionalComplexity_le_iff {k : ℕ} :
    C.distributionalComplexity ε R ν ≤ k ↔
      ∃ m : M, C.distributionalError m ν R ≤ ε ∧ C.cost m ≤ k :=
  ENat.iInf_subtype_natCast_le_natCast_iff

theorem distributionalComplexity_anti (hε : ε ≤ ε') :
    C.distributionalComplexity ε' R ν ≤ C.distributionalComplexity ε R ν :=
  ENat.iInf_subtype_natCast_mono fun _ hm => hm.trans hε

theorem errorProb_nonneg : 0 ≤ C.errorProb μ R x :=
  PMF.errorProb_nonneg

theorem errorProb_le_one : C.errorProb μ R x ≤ 1 :=
  PMF.errorProb_le_one

open Classical in
theorem errorProb_pure (C : RandomizedCost M X Z) (m : M) (R : X → Z → Prop) (x : X) :
    C.errorProb (PMF.pure m) R x = if R x (C.eval m x) then 0 else 1 :=
  PMF.errorProb_pure (fun m x => R x (C.eval m x)) m x

theorem Solves.mono (h : C.Solves μ ε R A) (hε : ε ≤ ε') (hA : A' ⊆ A) : C.Solves μ ε' R A' :=
  fun x hx => (h x (hA hx)).trans hε

/-- A deterministic strategy solving `R` on `A` solves it as a point-mass mixture with any
nonnegative error budget. -/
theorem solves_pure (hm : C.DetSolves m R A) (hε : 0 ≤ ε) : C.Solves (PMF.pure m) ε R A :=
  fun x hx => PMF.errorProb_pure_le (fun m x => R x (C.eval m x)) (hm x hx) hε

theorem ecomplexity_le_maxCost (h : C.Solves μ ε R A) :
    C.ecomplexity ε R A ≤ PMF.maxCost C.cost μ :=
  ENat.iInf_subtype_le h

theorem le_ecomplexity_iff {k : ℕ∞} :
    k ≤ C.ecomplexity ε R A ↔ ∀ μ : PMF M, C.Solves μ ε R A → k ≤ PMF.maxCost C.cost μ :=
  ENat.le_iInf_subtype_iff

theorem ecomplexity_le_iff {k : ℕ} :
    C.ecomplexity ε R A ≤ k ↔ ∃ μ : PMF M, C.Solves μ ε R A ∧ PMF.maxCost C.cost μ ≤ k :=
  ENat.iInf_subtype_le_natCast_iff

/-- Allowing larger error cannot increase public-coin complexity. -/
theorem ecomplexity_anti (hε : ε ≤ ε') : C.ecomplexity ε' R A ≤ C.ecomplexity ε R A :=
  ENat.iInf_subtype_mono fun _ hμ => hμ.mono hε subset_rfl

/-- Restricting the promise set cannot increase public-coin complexity. -/
theorem ecomplexity_mono (hA : A' ⊆ A) : C.ecomplexity ε R A' ≤ C.ecomplexity ε R A :=
  ENat.iInf_subtype_mono fun _ hμ => hμ.mono le_rfl hA

/-- Public-coin mixtures with nonnegative error are at least as cheap as deterministic strategies.
-/
theorem ecomplexity_le_detComplexity (hε : 0 ≤ ε) : C.ecomplexity ε R A ≤ C.detComplexity R A :=
  ENat.iInf_subtype_le_iInf_subtype PMF.pure (fun _ hm => solves_pure hm hε)
    fun m _ => (PMF.maxCost_pure C.cost m).le

/-- Translating strategies along `φ : M' → M` and inputs along `g : X → X'` without increasing
cost bounds public-coin complexity under `C` by that under `C'`. -/
theorem ecomplexity_comap_le {M' : Type*} {X' : Type*} {C' : RandomizedCost M' X' Z}
    (φ : M' → M) (g : X → X') (heval : ∀ m' x, C.eval (φ m') x = C'.eval m' (g x))
    (hcost : ∀ m', C.cost (φ m') ≤ C'.cost m') {S : X' → Z → Prop} {B : Set X'}
    (hg : Set.MapsTo g A B) :
    C.ecomplexity ε (fun x z => S (g x) z) A ≤ C'.ecomplexity ε S B :=
  ENat.iInf_subtype_le_iInf_subtype (PMF.map φ)
    (fun μ hμ x hx => by
      rw [errorProb, PMF.errorProb, PMF.toOuterMeasure_map_apply]
      simpa only [errorProb, PMF.errorProb, Set.preimage_ofPred_eq, heval] using hμ (g x) (hg hx))
    fun μ _ => PMF.maxCost_map_le C.cost C'.cost φ μ fun m' _ => hcost m'

/-- Averaging lower-bound step: if `μ` solves `R` on `A` with error `ε`, then for every input
distribution `ν` supported on `A` some strategy in `μ.support` has distributional error at most `ε`
under `ν`. -/
theorem Solves.exists_distributionalError_le (h : C.Solves μ ε R A) (ν : PMF X)
    (hν : ∀ x ∈ ν.support, x ∈ A) : ∃ m ∈ μ.support, C.distributionalError m ν R ≤ ε :=
  PMF.exists_errorProb_le ν fun x hx => h x (hν x hx)

/-- Under every input distribution `ν` supported on `A`, distributional complexity is at most
public-coin complexity on `A`. -/
theorem distributionalComplexity_le_ecomplexity (hν : ∀ x ∈ ν.support, x ∈ A) :
    C.distributionalComplexity ε R ν ≤ C.ecomplexity ε R A :=
  le_ecomplexity_iff.mpr fun _ hμ => by
    obtain ⟨m, hm, herr⟩ := hμ.exists_distributionalError_le ν hν
    exact (distributionalComplexity_le_cost herr).trans (PMF.le_maxCost hm)

/-- Minimax converse on a finite promise set `A`: if at least one strategy has cost at most `c` and
every input distribution supported on `A` admits a deterministic strategy of cost at most `c` and
error at most `ε`, then `C.ecomplexity ε R A ≤ c`. -/
theorem ecomplexity_le_of_forall_distributionalComplexity_le [Finite A] {c : ℕ}
    (hc : ∃ m : M, C.cost m ≤ c)
    (h : ∀ ν : PMF X, (∀ x ∈ ν.support, x ∈ A) → C.distributionalComplexity ε R ν ≤ c) :
    C.ecomplexity ε R A ≤ c := by
  obtain ⟨m₀, hm₀⟩ := hc
  have : Nonempty {m : M // C.cost m ≤ c} := ⟨⟨m₀, hm₀⟩⟩
  obtain ⟨μ, hμ, hmax⟩ := PMF.exists_maxCost_le_and_forall_errorProb_le
    (cost := C.cost) (Acc := fun m x => R x (C.eval m x)) (D := A) (c := c) (ε := ε) fun ν hν =>
      let ⟨m, herr, hm⟩ := distributionalComplexity_le_iff.mp (h ν hν)
      ⟨m, hm, herr⟩
  exact ecomplexity_le_iff.mpr ⟨μ, hμ, hmax⟩

/-- Budget-`c` minimax equivalence on a finite promise set `A`: when a strategy of cost at most `c`
exists, public-coin complexity is at most `c` iff distributional complexity is at most `c` under
every distribution supported on `A`. -/
theorem ecomplexity_le_iff_forall_distributionalComplexity_le [Finite A] {c : ℕ}
    (hc : ∃ m : M, C.cost m ≤ c) :
    C.ecomplexity ε R A ≤ c ↔
      ∀ ν : PMF X, (∀ x ∈ ν.support, x ∈ A) → C.distributionalComplexity ε R ν ≤ c :=
  ⟨fun h _ hν => (distributionalComplexity_le_ecomplexity hν).trans h,
    ecomplexity_le_of_forall_distributionalComplexity_le hc⟩

/-- Minimax supremum characterization on a finite promise set `A`: when a zero-cost strategy exists,
public-coin complexity equals the supremum of distributional complexities over input distributions
supported on `A`. -/
theorem ecomplexity_eq_iSup_distributionalComplexity [Finite A] (h0 : ∃ m : M, C.cost m = 0) :
    C.ecomplexity ε R A =
      ⨆ (ν : PMF X) (_ : ∀ x ∈ ν.support, x ∈ A), C.distributionalComplexity ε R ν :=
  let ⟨m₀, hm₀⟩ := h0
  ENat.eq_iSup₂_of_le_natCast_iff fun c =>
    ecomplexity_le_iff_forall_distributionalComplexity_le ⟨m₀, hm₀.le.trans (Nat.zero_le c)⟩

/-- Minimax supremum characterization for computing a total function `f : X → Z` on a finite input
type. -/
theorem ecomplexityFun_eq_iSup_distributionalComplexity [Finite X] (h0 : ∃ m : M, C.cost m = 0)
    (f : X → Z) :
    C.ecomplexityFun ε f = ⨆ ν : PMF X, C.distributionalComplexity ε (fun x z => f x = z) ν := by
  rw [ecomplexityFun, ecomplexity_eq_iSup_distributionalComplexity h0]
  simp only [Set.mem_univ, implies_true, iSup_pos]

end PublicCoin

/-! ### Majority error amplification for Boolean strategies -/

section Amplification

variable {M : Type u} {X : Type v}

/-- If the strict majority of `2 r` bits differs from `b`, at least `r` coordinates differ from
`b`. -/
private theorem le_card_filter_ne_of_strictMajorityOn_ne {r : ℕ} {v : Fin (2 * r) → Bool}
    {b : Bool} (h : BitString.strictMajorityOn Finset.univ v ≠ b) :
    r ≤ (Finset.univ.filter fun i => ¬v i = b).card := by
  have h₁ := BitString.card_filter_eq_le_half_of_strictMajorityOn_ne Finset.univ v b h
  have h₂ := Finset.card_filter_add_card_filter_not (s := Finset.univ) fun i => v i = b
  rw [Finset.card_univ, Fintype.card_fin] at h₁ h₂
  omega

/-- Strict majority of `2 r` independent draws from `μ`, sequenced by `runAll`. -/
@[expose] noncomputable def amplify (_ : RandomizedCost M X Bool)
    (runAll : ∀ {k : ℕ}, (Fin k → M) → ((Fin k → Bool) → Bool) → M)
    (μ : PMF M) (r : ℕ) : PMF M :=
  (PMF.iid μ (2 * r)).map fun ms => runAll ms (BitString.strictMajorityOn Finset.univ)

variable {C : RandomizedCost M X Bool}
  {runAll : ∀ {k : ℕ}, (Fin k → M) → ((Fin k → Bool) → Bool) → M}
  {μ : PMF M} {f : X → Bool} {A : Set X} {ε : ℝ}

/-- Sequencing `2 r` draws of cost at most `c` has support cost at most `2 r c`. -/
theorem maxCost_amplify_le
    (hcost : ∀ {k d : ℕ} {ms : Fin k → M} {g : (Fin k → Bool) → Bool},
      (∀ i, C.cost (ms i) ≤ d) → C.cost (runAll ms g) ≤ k * d)
    {c : ℕ} (hμ : PMF.maxCost C.cost μ ≤ c) (r : ℕ) :
    PMF.maxCost C.cost (C.amplify runAll μ r) ≤ 2 * r * c := by
  refine PMF.maxCost_le_iff.mpr fun m hm => ?_
  obtain ⟨ms, hms, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hm
  exact_mod_cast hcost fun i => by
    exact_mod_cast (PMF.le_maxCost ((PMF.mem_support_iid_iff _ _).mp hms i)).trans hμ

/-- Strict-majority error reduction: if `μ` computes `f` on `A` with error `ε ≤ 1 / 2`, then the
strict majority of `2 r` independent runs computes `f` on `A` with error `(4 ε (1 - ε)) ^ r`. -/
theorem Solves.amplify
    (heval : ∀ {k : ℕ} (ms : Fin k → M) (g : (Fin k → Bool) → Bool) (x : X),
      C.eval (runAll ms g) x = g fun i => C.eval (ms i) x)
    (hμ : C.Solves μ ε (fun x b => f x = b) A) (hε : ε ≤ 1 / 2) (r : ℕ) :
    C.Solves (C.amplify runAll μ r) ((4 * ε * (1 - ε)) ^ r) (fun x b => f x = b) A := by
  intro x hx
  set e : M → Bool := fun m => decide (C.eval m x ≠ f x)
  have he : ((μ.map e) true).toReal ≤ ε := by
    have hpre : e ⁻¹' {true} = {m | ¬f x = C.eval m x} := by
      ext
      simp only [e, Set.mem_preimage, Set.mem_singleton_iff, decide_eq_true_eq, Set.mem_ofPred_eq]
      exact ne_comm
    rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply, hpre]
    exact hμ x hx
  refine le_trans ?_ (PMF.iid_card_ge_le he hε r)
  rw [errorProb, PMF.errorProb, RandomizedCost.amplify, PMF.toOuterMeasure_map_apply, PMF.iid_map,
    PMF.toOuterMeasure_map_apply]
  refine PMF.toOuterMeasure_toReal_mono _ fun ms hms => ?_
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, heval] at hms ⊢
  simpa [e] using le_card_filter_ne_of_strictMajorityOn_ne (Ne.symm hms)

/-- Public-coin cost bound under majority repetition on `A`: reducing error `ε ≤ 1 / 2` to
`(4 ε (1 - ε)) ^ r` multiplies complexity by at most `2 r`. -/
theorem ecomplexity_le_two_mul_mul
    (heval : ∀ {k : ℕ} (ms : Fin k → M) (g : (Fin k → Bool) → Bool) (x : X),
      C.eval (runAll ms g) x = g fun i => C.eval (ms i) x)
    (hcost : ∀ {k d : ℕ} {ms : Fin k → M} {g : (Fin k → Bool) → Bool},
      (∀ i, C.cost (ms i) ≤ d) → C.cost (runAll ms g) ≤ k * d)
    (h0 : ∃ m : M, C.cost m = 0) (hε : ε ≤ 1 / 2) (r : ℕ) :
    C.ecomplexity ((4 * ε * (1 - ε)) ^ r) (fun x b => f x = b) A ≤
      2 * r * C.ecomplexity ε (fun x b => f x = b) A := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · obtain ⟨m₀, hm₀⟩ := h0
    rw [pow_zero, Nat.cast_zero, mul_zero, zero_mul]
    exact (ecomplexity_le_maxCost (μ := PMF.pure m₀) fun _ _ => errorProb_le_one).trans
      (by simp [hm₀])
  cases h : C.ecomplexity ε (fun x b => f x = b) A using ENat.recTopCoe with
  | top =>
    rw [ENat.mul_top (by exact_mod_cast (Nat.mul_pos two_pos hr).ne')]
    exact le_top
  | coe c =>
    obtain ⟨μ, hμ, hc⟩ := ecomplexity_le_iff.mp h.le
    exact (ecomplexity_le_maxCost (hμ.amplify heval hε r)).trans (maxCost_amplify_le hcost hc r)

/-- Public-coin cost bound under majority repetition for a total Boolean function `f : X → Bool`. -/
theorem ecomplexityFun_le_two_mul_mul
    (heval : ∀ {k : ℕ} (ms : Fin k → M) (g : (Fin k → Bool) → Bool) (x : X),
      C.eval (runAll ms g) x = g fun i => C.eval (ms i) x)
    (hcost : ∀ {k d : ℕ} {ms : Fin k → M} {g : (Fin k → Bool) → Bool},
      (∀ i, C.cost (ms i) ≤ d) → C.cost (runAll ms g) ≤ k * d)
    (h0 : ∃ m : M, C.cost m = 0) (hε : ε ≤ 1 / 2) (r : ℕ) :
    C.ecomplexityFun ((4 * ε * (1 - ε)) ^ r) f ≤ 2 * r * C.ecomplexityFun ε f :=
  ecomplexity_le_two_mul_mul heval hcost h0 hε r

/-- Specialization of `ecomplexityFun_le_two_mul_mul` from error `1 / 3` to `(8 / 9) ^ r` in `2 r`
runs. -/
theorem ecomplexityFun_le_two_mul_mul_one_third
    (heval : ∀ {k : ℕ} (ms : Fin k → M) (g : (Fin k → Bool) → Bool) (x : X),
      C.eval (runAll ms g) x = g fun i => C.eval (ms i) x)
    (hcost : ∀ {k d : ℕ} {ms : Fin k → M} {g : (Fin k → Bool) → Bool},
      (∀ i, C.cost (ms i) ≤ d) → C.cost (runAll ms g) ≤ k * d)
    (h0 : ∃ m : M, C.cost m = 0) (r : ℕ) :
    C.ecomplexityFun ((8 / 9) ^ r) f ≤ 2 * r * C.ecomplexityFun (1 / 3) f := by
  have h := ecomplexityFun_le_two_mul_mul (C := C) (f := f) (ε := 1 / 3) heval hcost h0
    (by norm_num) r
  rwa [show (4 * (1 / 3) * (1 - 1 / 3) : ℝ) = 8 / 9 by norm_num] at h

end Amplification

/-! ### Finitely supported mixtures (`StdSimplex`) and `ℕ`-valued Yao minimax -/

section StdSimplex

variable {M : Type u} {X : Type v} {Z : Type w}

/-- Least worst-case support cost in `ℕ` of a finitely supported mixture (`StdSimplex ℝ M`)
solving `R` on all inputs with nonnegative error budget `ε`. -/
@[expose] noncomputable def simplexComplexity (C : RandomizedCost M X Z) (ε : ℝ≥0)
    (R : X → Z → Prop) : ℕ :=
  sInf {d | ∃ μ : StdSimplex ℝ M,
    (∀ x, μ.errorProb (fun m => R x (C.eval m x)) ≤ ε) ∧ μ.maxCost C.cost ≤ d}

/-- Least cost in `ℕ` of a deterministic strategy erring with probability at most `ε` under a
finitely supported input distribution `ν : StdSimplex ℝ X`. -/
@[expose] noncomputable def simplexDistributionalComplexity (C : RandomizedCost M X Z) (ε : ℝ≥0)
    (ν : StdSimplex ℝ X) (R : X → Z → Prop) : ℕ :=
  sInf {d | ∃ m : M, ν.errorProb (fun x => R x (C.eval m x)) ≤ ε ∧ C.cost m ≤ d}

variable {C : RandomizedCost M X Z} {R : X → Z → Prop} {ν : StdSimplex ℝ X} {ε : ℝ≥0} {d : ℕ}

theorem simplexComplexity_le_maxCost {μ : StdSimplex ℝ M}
    (h : ∀ x, μ.errorProb (fun m => R x (C.eval m x)) ≤ ε) :
    C.simplexComplexity ε R ≤ μ.maxCost C.cost :=
  Nat.sInf_le_of_le h

theorem simplexDistributionalComplexity_le_cost {m : M}
    (h : ν.errorProb (fun x => R x (C.eval m x)) ≤ ε) :
    C.simplexDistributionalComplexity ε ν R ≤ C.cost m :=
  Nat.sInf_le_of_le h

/-- When some deterministic strategy solves `R` everywhere, `simplexComplexity` is attained. -/
theorem exists_simplexComplexity_eq (hex : ∃ m : M, ∀ x, R x (C.eval m x)) :
    ∃ μ : StdSimplex ℝ M,
      (∀ x, μ.errorProb (fun m => R x (C.eval m x)) ≤ ε) ∧
        μ.maxCost C.cost = C.simplexComplexity ε R := by
  obtain ⟨m₀, hm₀⟩ := hex
  exact Nat.exists_eq_sInf_of_exists (StdSimplex.maxCost C.cost)
    ⟨StdSimplex.single m₀, fun x =>
      (StdSimplex.errorProb_single_of_pos (Acc := fun m => R x (C.eval m x)) (hm₀ x)).trans_le
        ε.coe_nonneg⟩

/-- When some deterministic strategy solves `R` everywhere, `simplexDistributionalComplexity` is
attained. -/
theorem exists_simplexDistributionalComplexity_eq (ν : StdSimplex ℝ X)
    (hex : ∃ m : M, ∀ x, R x (C.eval m x)) :
    ∃ m : M, ν.errorProb (fun x => R x (C.eval m x)) ≤ ε ∧
      C.cost m = C.simplexDistributionalComplexity ε ν R := by
  obtain ⟨m₀, hm₀⟩ := hex
  exact Nat.exists_eq_sInf_of_exists C.cost
    ⟨m₀, (StdSimplex.errorProb_eq_zero_iff.mpr fun x _ => hm₀ x).trans_le ε.coe_nonneg⟩

/-- Averaging lower bound on `StdSimplex`: distributional complexity under any `ν` is at most
randomized complexity. -/
theorem simplexDistributionalComplexity_le_simplexComplexity (ν : StdSimplex ℝ X)
    (hex : ∃ m : M, ∀ x, R x (C.eval m x)) :
    C.simplexDistributionalComplexity ε ν R ≤ C.simplexComplexity ε R := by
  obtain ⟨μ, hμ, hd⟩ := exists_simplexComplexity_eq (C := C) (ε := ε) hex
  obtain ⟨m, hm, herr⟩ := StdSimplex.exists_errorProb_le (fun m x => R x (C.eval m x)) μ ν hμ
  exact (simplexDistributionalComplexity_le_cost herr).trans
    ((StdSimplex.le_maxCost hm).trans_eq hd)

/-- Budget-`d` minimax equivalence on `StdSimplex` over a finite nonempty input space. -/
theorem simplexComplexity_le_iff_forall_simplexDistributionalComplexity_le [Finite X] [Nonempty X]
    (hex : ∃ m : M, ∀ x, R x (C.eval m x)) :
    C.simplexComplexity ε R ≤ d ↔
      ∀ ν : StdSimplex ℝ X, C.simplexDistributionalComplexity ε ν R ≤ d := by
  refine ⟨fun h ν => (simplexDistributionalComplexity_le_simplexComplexity ν hex).trans h,
    fun h => ?_⟩
  obtain ⟨μ, hμ, hd⟩ := StdSimplex.exists_maxCost_le_and_forall_errorProb_le C.cost
    (fun m x => R x (C.eval m x)) (d := d) (ε := ε) fun ν =>
      let ⟨m, herr, hm⟩ :=
        exists_simplexDistributionalComplexity_eq (C := C) (ε := ε) ν hex
      ⟨m, hm.trans_le (h ν), herr⟩
  exact (simplexComplexity_le_maxCost hμ).trans hd

/-- Minimax supremum characterization on `StdSimplex`: randomized complexity equals the supremum of
distributional complexities over input distributions. -/
theorem simplexComplexity_eq_iSup_simplexDistributionalComplexity [Finite X] [Nonempty X]
    (hex : ∃ m : M, ∀ x, R x (C.eval m x)) :
    C.simplexComplexity ε R =
      ⨆ ν : StdSimplex ℝ X, C.simplexDistributionalComplexity ε ν R :=
  Nat.eq_ciSup_of_le_iff fun _ =>
    simplexComplexity_le_iff_forall_simplexDistributionalComplexity_le hex

/-- Attainment of a hardest input distribution on `StdSimplex`. -/
theorem exists_simplexDistributionalComplexity_eq_simplexComplexity [Finite X] [Nonempty X]
    (hex : ∃ m : M, ∀ x, R x (C.eval m x)) :
    ∃ ν : StdSimplex ℝ X,
      C.simplexDistributionalComplexity ε ν R = C.simplexComplexity ε R :=
  Nat.exists_eq_of_le_iff fun _ =>
    simplexComplexity_le_iff_forall_simplexDistributionalComplexity_le hex

end StdSimplex

/-! ### Coin-fixed zero-error expected cost and Yao averaging -/

section CoinFixing

variable {M : Type u} {X : Type v} {Y : Type w}

/-- Expected second component of a point-mass `(output, cost)` law `PMF.pure p`. -/
theorem tsum_pure_snd_natCast (p : Y × ℕ) :
    (∑' z : Y × ℕ, (PMF.pure p) z * (z.2 : ℝ≥0∞)) = (p.2 : ℝ≥0∞) := by
  rw [tsum_eq_single p fun z hz => by simp [PMF.pure_apply, hz]]
  simp

/-- When a joint `(output, cost)` law `run` is a mixture `μ.bind fun m => PMF.pure (out m, c m)`
of deterministic outcomes, its expected cost is the `μ`-average of `c`. -/
theorem tsum_snd_eq_of_bind_pure (μ : PMF M) (out : M → Y) (c : M → ℕ) {run : PMF (Y × ℕ)}
    (hrun : run = μ.bind fun m => PMF.pure (out m, c m)) :
    (∑' z : Y × ℕ, run z * (z.2 : ℝ≥0∞)) = ∑' m, μ m * (c m : ℝ≥0∞) := by
  rw [hrun, PMF.tsum_bind_mul]
  exact tsum_congr fun _ => congrArg (_ * ·) (tsum_pure_snd_natCast _)

/-- Every strategy in the support of a coin-fixing law `μ` inherits any zero-error output property
`Good` satisfied across the supported outputs of `run x`. -/
theorem good_of_mem_support_coinFixing {μ : PMF M} {run : X → PMF (Y × ℕ)}
    {evalOut : M → X → Y} {costAt : M → X → ℕ} {A : Set X} {Good : X → Y → Prop}
    (hcorr : ∀ x ∈ A, ∀ y ∈ ((run x).map Prod.fst).support, Good x y)
    (hlaw : ∀ x ∈ A, run x = μ.bind fun m => PMF.pure (evalOut m x, costAt m x))
    {m : M} (hm : m ∈ μ.support) :
    ∀ x ∈ A, Good x (evalOut m x) := by
  intro x hx
  apply hcorr x hx
  rw [hlaw x hx, PMF.mem_support_map_iff]
  exact ⟨(evalOut m x, costAt m x), (PMF.mem_support_bind_iff _ _ _).mpr ⟨m, hm, by simp⟩, rfl⟩

/-- Coin-fixing averaging for zero-error computations: if `run x` decomposes through a coin law
`μ` on `A` and on `ν.support`, and every supported output on `A` satisfies `Good x`, then some
deterministic `m ∈ μ.support` satisfies `Good x (evalOut m x)` for all `x ∈ A` and has `ν`-expected
cost at most the `ν`-expected cost of `run`. -/
theorem exists_mem_support_of_coinFixing (μ : PMF M) (ν : PMF X) (run : X → PMF (Y × ℕ))
    (evalOut : M → X → Y) (costAt : M → X → ℕ) (A : Set X) (Good : X → Y → Prop)
    (hcorr : ∀ x ∈ A, ∀ y ∈ ((run x).map Prod.fst).support, Good x y)
    (hlawA : ∀ x ∈ A, run x = μ.bind fun m => PMF.pure (evalOut m x, costAt m x))
    (hlawν : ∀ x ∈ ν.support, run x = μ.bind fun m => PMF.pure (evalOut m x, costAt m x)) :
    ∃ m ∈ μ.support, (∀ x ∈ A, Good x (evalOut m x)) ∧
      (∑' x, ν x * (costAt m x : ℝ≥0∞)) ≤
        ∑' x, ν x * ∑' z : Y × ℕ, (run x) z * (z.2 : ℝ≥0∞) := by
  obtain ⟨m, hm, hle⟩ :=
    PMF.exists_mem_support_tsum_mul_le_tsum_mul μ ν fun m x => (costAt m x : ℝ≥0∞)
  refine ⟨m, hm, good_of_mem_support_coinFixing hcorr hlawA hm,
    hle.trans (tsum_le_tsum fun x => ?_)⟩
  by_cases hx : x ∈ ν.support
  · rw [tsum_snd_eq_of_bind_pure μ (fun m => evalOut m x) (fun m => costAt m x) (hlawν x hx)]
  · simp [(PMF.apply_eq_zero_iff ν x).mpr hx]

/-- Uniform-budget specialization of `exists_mem_support_of_coinFixing`: when expected cost on
every `x ∈ ν.support` is at most `ε`, some `m ∈ μ.support` preserves `Good` on `A` and has
`ν`-expected cost at most `ε`. -/
theorem exists_mem_support_tsum_mul_le_of_coinFixing (μ : PMF M) (ν : PMF X)
    (run : X → PMF (Y × ℕ)) (evalOut : M → X → Y) (costAt : M → X → ℕ) (A : Set X)
    (Good : X → Y → Prop)
    (hcorr : ∀ x ∈ A, ∀ y ∈ ((run x).map Prod.fst).support, Good x y)
    (hlawA : ∀ x ∈ A, run x = μ.bind fun m => PMF.pure (evalOut m x, costAt m x))
    (hlawν : ∀ x ∈ ν.support, run x = μ.bind fun m => PMF.pure (evalOut m x, costAt m x))
    {ε : ℝ≥0∞} (hε : ∀ x ∈ ν.support, (∑' z : Y × ℕ, (run x) z * (z.2 : ℝ≥0∞)) ≤ ε) :
    ∃ m ∈ μ.support, (∀ x ∈ A, Good x (evalOut m x)) ∧
      (∑' x, ν x * (costAt m x : ℝ≥0∞)) ≤ ε := by
  obtain ⟨m, hm, hgood, hle⟩ :=
    exists_mem_support_of_coinFixing μ ν run evalOut costAt A Good hcorr hlawA hlawν
  refine ⟨m, hm, hgood, hle.trans ((tsum_le_tsum (g := fun x => ν x * ε) fun x => ?_).trans ?_)⟩
  · by_cases hx : x ∈ ν.support
    · exact mul_le_mul_right (hε x hx) (ν x)
    · simp [(PMF.apply_eq_zero_iff ν x).mpr hx]
  · rw [ENNReal.tsum_mul_right, ν.tsum_coe, one_mul]

end CoinFixing

end RandomizedCost

end Cslib
