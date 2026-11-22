/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.NOF.Protocol
public import CslibFrontier.Computability.RandomizedCost
public import Cslib.Probability.PMF
public import Mathlib.Basic.Real.Basic
import CslibFrontier.Foundations.Data.ENat.IInf

/-!
# Randomized number-on-forehead protocols

In a *public-coin* number-on-forehead protocol the players share random bits, which they use to
draw a deterministic protocol from a distribution and run it; so a public-coin protocol is a
distribution over deterministic NOF protocols (`NOF.PublicCoin`), instantiating the model-generic
kernel `Cslib.RandomizedCost` (`NOF.Protocol.randomizedCost`). It solves a relation `R` on a set
`A` of inputs with error `ε` when on every input of `A` its output is not related to the input with
probability at most `ε` (`NOF.PublicCoin.Solves`). Its cost bounds the tree depth over the random
choices (`NOF.PublicCoin.depth`), and the public-coin communication complexity is the least cost
(`NOF.PublicCoin.ecomplexity`, `NOF.PublicCoin.ecomplexityFun`). Deterministic protocols are
public-coin protocols (`NOF.PublicCoin.ecomplexity_le_protocol`).

Instantiating `Cslib.RandomizedCost` on `NOF.Protocol.randomizedCost` extends the two-party
public-coin minimax and amplification developments (after
[Kushilevitz and Nisan, Chapters 3 and 6][KushilevitzNisan1997] and [Yao1977, vonNeumann1928]) to
multiparty NOF protocols: on a finite promise set `A` with nonempty output type `Z`, public-coin NOF
complexity equals the supremum of distributional complexities
(`NOF.Protocol.distributionalComplexity`) over input distributions supported on `A`, combining the
averaging lower bound on arbitrary promise sets
(`NOF.PublicCoin.Solves.exists_distributionalError_le`,
`NOF.PublicCoin.distributionalComplexity_le_ecomplexity`) with the minimax converse
(`NOF.PublicCoin.ecomplexity_le_of_forall_distributionalComplexity_le`,
`NOF.PublicCoin.ecomplexity_eq_iSup_distributionalComplexity`).

For Boolean functions, taking the strict majority of `2 r` independent runs
(`NOF.PublicCoin.amplify`, sequenced via `NOF.Protocol.runAll`, after
[Kushilevitz and Nisan, Chapter 3][KushilevitzNisan1997]) amplifies error `ε ≤ 1 / 2` down to
`(4 ε (1 - ε)) ^ r` at `2 r` times the communication cost (`NOF.PublicCoin.Solves.amplify`,
`NOF.PublicCoin.ecomplexity_le_two_mul_mul`).

## Main definitions

* `Cslib.Communication.NOF.Protocol.randomizedCost`: deterministic NOF protocols as a
  `Cslib.RandomizedCost` model.
* `Cslib.Communication.NOF.Protocol.distributionalError`,
  `Cslib.Communication.NOF.Protocol.distributionalComplexity`: distributional error and least depth
  under an input distribution `ν`.
* `Cslib.Communication.NOF.PublicCoin`: public-coin NOF protocols, with `NOF.PublicCoin.depth`,
  `NOF.PublicCoin.errorProb`, `NOF.PublicCoin.Solves`, `NOF.PublicCoin.ecomplexity`,
  `NOF.PublicCoin.ecomplexityFun`, and `NOF.PublicCoin.amplify`.

## Main results

* `Cslib.Communication.NOF.PublicCoin.ecomplexity_le_protocol`: randomness does not hurt.
* `Cslib.Communication.NOF.PublicCoin.Solves.exists_distributionalError_le`,
  `Cslib.Communication.NOF.PublicCoin.distributionalComplexity_le_ecomplexity`: averaging lower
  bound for public-coin NOF protocols.
* `Cslib.Communication.NOF.PublicCoin.ecomplexity_le_of_forall_distributionalComplexity_le`,
  `Cslib.Communication.NOF.PublicCoin.ecomplexity_eq_iSup_distributionalComplexity`,
  `Cslib.Communication.NOF.PublicCoin.ecomplexityFun_eq_iSup_distributionalComplexity`: multiparty
  NOF minimax characterization instantiating `Cslib.RandomizedCost`.
* `Cslib.Communication.NOF.PublicCoin.Solves.amplify`,
  `Cslib.Communication.NOF.PublicCoin.ecomplexity_le_two_mul_mul`,
  `Cslib.Communication.NOF.PublicCoin.ecomplexityFun_le_two_mul_mul_one_third`: majority error
  amplification for Boolean NOF protocols.

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
* [E. Kushilevitz and N. Nisan, *Communication Complexity*][KushilevitzNisan1997]
* [A. C.-C. Yao, *Probabilistic computations: toward a unified measure of complexity*][Yao1977]
* [J. von Neumann, *Zur Theorie der Gesellschaftsspiele*][vonNeumann1928]
-/

@[expose] public section

namespace Cslib.Communication.NOF

open Probability

universe u v w

variable {ι : Type u} {X : ι → Type v} {Z : Type w}

/-- A public-coin number-on-forehead protocol: the players use shared random bits to draw a
deterministic protocol from this distribution, and run it. -/
abbrev PublicCoin (X : ι → Type v) (Z : Type w) : Type (max u v w) :=
  PMF (Protocol X Z)

/-- Deterministic NOF protocols as a `RandomizedCost` model with evaluation `Protocol.run` and
worst-case cost `Protocol.depth`. -/
def Protocol.randomizedCost (X : ι → Type v) (Z : Type w) :
    RandomizedCost (Protocol X Z) (∀ i, X i) Z :=
  ⟨Protocol.run, Protocol.depth⟩

namespace Protocol

/-- The error of a deterministic protocol on inputs drawn from `ν`: the probability that its output
on an input drawn from `ν` is not related to it by `R`. -/
noncomputable def distributionalError (p : Protocol X Z) (ν : PMF (∀ i, X i))
    (R : (∀ i, X i) → Z → Prop) : ℝ :=
  PMF.errorProb (fun x (p : Protocol X Z) => R x (p.run x)) ν p

/-- The *distributional complexity* `D^ν_ε(R)` of `R` under `ν`: the least depth of a deterministic
NOF protocol erring with probability at most `ε` on inputs drawn from `ν`, or `⊤` if none exists. -/
noncomputable def distributionalComplexity (ε : ℝ) (R : (∀ i, X i) → Z → Prop)
    (ν : PMF (∀ i, X i)) : ℕ∞ :=
  (randomizedCost X Z).distributionalComplexity ε R ν

variable {p : Protocol X Z} {ε ε' : ℝ} {R : (∀ i, X i) → Z → Prop} {ν : PMF (∀ i, X i)}

theorem distributionalComplexity_le_depth (hp : p.distributionalError ν R ≤ ε) :
    distributionalComplexity ε R ν ≤ p.depth :=
  RandomizedCost.distributionalComplexity_le_cost hp

theorem le_distributionalComplexity_iff {k : ℕ∞} :
    k ≤ distributionalComplexity ε R ν ↔
      ∀ p : Protocol X Z, p.distributionalError ν R ≤ ε → k ≤ p.depth :=
  RandomizedCost.le_distributionalComplexity_iff

theorem distributionalComplexity_le_iff {k : ℕ} :
    distributionalComplexity ε R ν ≤ k ↔
      ∃ p : Protocol X Z, p.distributionalError ν R ≤ ε ∧ p.depth ≤ k :=
  RandomizedCost.distributionalComplexity_le_iff

/-- Allowing more error makes a relation easier under `ν`. -/
theorem distributionalComplexity_anti (hε : ε ≤ ε') :
    distributionalComplexity ε' R ν ≤ distributionalComplexity ε R ν :=
  RandomizedCost.distributionalComplexity_anti hε

end Protocol

namespace PublicCoin

/-- The supremum of the tree depths of protocols in the support, or `⊤` if these depths are
unbounded. Each tree's depth counts even branches unreachable by any input. -/
noncomputable def depth (μ : PublicCoin X Z) : ℕ∞ :=
  PMF.maxCost Protocol.depth μ

/-- The probability that the protocol drawn from `μ` outputs, on the input `x`, a value not related
to `x` by `R`. -/
noncomputable def errorProb (μ : PublicCoin X Z) (R : (∀ i, X i) → Z → Prop) (x : ∀ i, X i) : ℝ :=
  PMF.errorProb (fun (p : Protocol X Z) x => R x (p.run x)) μ x

/-- A public-coin protocol `μ` solves `R` on `A` with error `ε` when on every input of `A` its
output is not related to the input with probability at most `ε`. -/
def Solves (μ : PublicCoin X Z) (ε : ℝ) (R : (∀ i, X i) → Z → Prop) (A : Set (∀ i, X i)) :
    Prop :=
  ∀ x ∈ A, μ.errorProb R x ≤ ε

/-- The public-coin communication complexity of `R` on `A` with error `ε`: the least cost of a
public-coin protocol solving it with error `ε`, or `⊤` if there is none. -/
noncomputable def ecomplexity (ε : ℝ) (R : (∀ i, X i) → Z → Prop) (A : Set (∀ i, X i)) : ℕ∞ :=
  (Protocol.randomizedCost X Z).ecomplexity ε R A

/-- The public-coin communication complexity of computing `f` with error `ε`: `ecomplexity` of the
relation `f x = z` on all inputs. -/
noncomputable def ecomplexityFun (ε : ℝ) (f : (∀ i, X i) → Z) : ℕ∞ :=
  (Protocol.randomizedCost X Z).ecomplexityFun ε f

variable {μ : PublicCoin X Z} {p : Protocol X Z} {R : (∀ i, X i) → Z → Prop}
  {A A' : Set (∀ i, X i)} {ε ε' : ℝ} {x : ∀ i, X i}

theorem depth_le_iff {c : ℕ∞} : μ.depth ≤ c ↔ ∀ p ∈ μ.support, (p.depth : ℕ∞) ≤ c :=
  PMF.maxCost_le_iff

theorem depth_le_depth (hp : p ∈ μ.support) : (p.depth : ℕ∞) ≤ μ.depth :=
  PMF.le_maxCost hp

@[simp] theorem depth_pure (p : Protocol X Z) : depth (PMF.pure p) = p.depth :=
  PMF.maxCost_pure Protocol.depth p

theorem errorProb_nonneg : 0 ≤ μ.errorProb R x :=
  RandomizedCost.errorProb_nonneg (C := Protocol.randomizedCost X Z)

theorem errorProb_le_one : μ.errorProb R x ≤ 1 :=
  RandomizedCost.errorProb_le_one (C := Protocol.randomizedCost X Z)

open Classical in
theorem errorProb_pure (p : Protocol X Z) (R : (∀ i, X i) → Z → Prop) (x : ∀ i, X i) :
    errorProb (PMF.pure p) R x = if R x (p.run x) then 0 else 1 :=
  (Protocol.randomizedCost X Z).errorProb_pure p R x

theorem Solves.mono (h : μ.Solves ε R A) (hε : ε ≤ ε') (hA : A' ⊆ A) : μ.Solves ε' R A' :=
  RandomizedCost.Solves.mono (C := Protocol.randomizedCost X Z) h hε hA

/-- A deterministic protocol solving `R` is a public-coin protocol solving it with any nonnegative
error. -/
theorem solves_pure (hp : p.Solves R A) (hε : 0 ≤ ε) : Solves (PMF.pure p) ε R A :=
  RandomizedCost.solves_pure (C := Protocol.randomizedCost X Z) hp hε

/-- **The averaging argument**, the easy direction of Yao's principle: if `μ` solves `R` on `A`
with error `ε`, then for every distribution `ν` on `A` some protocol that `μ` can draw errs with
probability at most `ε` on inputs drawn from `ν`. -/
theorem Solves.exists_distributionalError_le (h : μ.Solves ε R A) (ν : PMF (∀ i, X i))
    (hν : ∀ x ∈ ν.support, x ∈ A) : ∃ p ∈ μ.support, p.distributionalError ν R ≤ ε :=
  RandomizedCost.Solves.exists_distributionalError_le (C := Protocol.randomizedCost X Z) h ν hν

theorem ecomplexity_le_depth (h : μ.Solves ε R A) : ecomplexity ε R A ≤ μ.depth :=
  RandomizedCost.ecomplexity_le_maxCost h

theorem le_ecomplexity_iff {k : ℕ∞} :
    k ≤ ecomplexity ε R A ↔ ∀ μ : PublicCoin X Z, μ.Solves ε R A → k ≤ μ.depth :=
  RandomizedCost.le_ecomplexity_iff

theorem ecomplexity_le_iff {k : ℕ} :
    ecomplexity ε R A ≤ k ↔ ∃ μ : PublicCoin X Z, μ.Solves ε R A ∧ μ.depth ≤ k :=
  RandomizedCost.ecomplexity_le_iff

/-- Allowing more error makes a relation easier. -/
theorem ecomplexity_anti (hε : ε ≤ ε') : ecomplexity ε' R A ≤ ecomplexity ε R A :=
  RandomizedCost.ecomplexity_anti hε

/-- Solving a relation on a larger set is harder. -/
theorem ecomplexity_mono (hA : A' ⊆ A) : ecomplexity ε R A' ≤ ecomplexity ε R A :=
  RandomizedCost.ecomplexity_mono hA

/-- Public-coin protocols with nonnegative error are at least as good as deterministic ones. -/
theorem ecomplexity_le_protocol (hε : 0 ≤ ε) : ecomplexity ε R A ≤ Protocol.ecomplexity R A :=
  RandomizedCost.ecomplexity_le_detComplexity hε

theorem ecomplexityFun_le_protocol {f : (∀ i, X i) → Z} (hε : 0 ≤ ε) :
    ecomplexityFun ε f ≤ Protocol.ecomplexityFun f :=
  ecomplexity_le_protocol hε

/-! ### Distributional lower bounds and minimax duality for NOF protocols -/

/-- Multiparty NOF instantiation of `RandomizedCost.distributionalComplexity_le_ecomplexity` (the
averaging direction, after [Yao1977] and [Kushilevitz and Nisan, Chapter 3][KushilevitzNisan1997]):
under every distribution `ν` supported on `A`, distributional NOF complexity is at most public-coin
NOF complexity on `A`. -/
theorem distributionalComplexity_le_ecomplexity {ν : PMF (∀ i, X i)}
    (hν : ∀ x ∈ ν.support, x ∈ A) :
    Protocol.distributionalComplexity ε R ν ≤ ecomplexity ε R A :=
  RandomizedCost.distributionalComplexity_le_ecomplexity hν

/-- Multiparty NOF instantiation of
`RandomizedCost.ecomplexity_le_of_forall_distributionalComplexity_le` (the minimax converse, after
[Kushilevitz and Nisan, Theorem 3.20 and Chapter 6][KushilevitzNisan1997] and
[Yao1977, vonNeumann1928]): on a finite promise set `A` with nonempty output type `Z`, if under
every distribution supported on `A` some deterministic NOF protocol of depth at most `c` errs with
probability at most `ε`, then `ecomplexity ε R A ≤ c`. -/
theorem ecomplexity_le_of_forall_distributionalComplexity_le [Finite A] [Nonempty Z] {c : ℕ}
    (h : ∀ ν : PMF (∀ i, X i), (∀ x ∈ ν.support, x ∈ A) →
      Protocol.distributionalComplexity ε R ν ≤ c) :
    ecomplexity ε R A ≤ c :=
  RandomizedCost.ecomplexity_le_of_forall_distributionalComplexity_le
    ⟨.output (Classical.arbitrary Z), Nat.zero_le c⟩ h

/-- Multiparty NOF instantiation of
`RandomizedCost.ecomplexity_le_iff_forall_distributionalComplexity_le`: on a finite promise set `A`
with nonempty output type `Z`, public-coin NOF complexity on `A` is at most `c` iff distributional
complexity is at most `c` under every distribution supported on `A`. -/
theorem ecomplexity_le_iff_forall_distributionalComplexity_le [Finite A] [Nonempty Z] {c : ℕ} :
    ecomplexity ε R A ≤ c ↔
      ∀ ν : PMF (∀ i, X i), (∀ x ∈ ν.support, x ∈ A) →
        Protocol.distributionalComplexity ε R ν ≤ c :=
  RandomizedCost.ecomplexity_le_iff_forall_distributionalComplexity_le
    ⟨.output (Classical.arbitrary Z), Nat.zero_le c⟩

/-- Multiparty NOF instantiation of `RandomizedCost.ecomplexity_eq_iSup_distributionalComplexity`
(after [Kushilevitz and Nisan, Theorem 3.20 and Chapter 6][KushilevitzNisan1997] and [Yao1977]): on
a finite promise set `A` with nonempty output type `Z`, public-coin NOF complexity equals the
supremum of distributional complexities over distributions supported on `A`. -/
theorem ecomplexity_eq_iSup_distributionalComplexity [Finite A] [Nonempty Z] :
    ecomplexity ε R A =
      ⨆ (ν : PMF (∀ i, X i)) (_ : ∀ x ∈ ν.support, x ∈ A),
        Protocol.distributionalComplexity ε R ν :=
  RandomizedCost.ecomplexity_eq_iSup_distributionalComplexity
    ⟨.output (Classical.arbitrary Z), rfl⟩

/-- Multiparty NOF instantiation of `RandomizedCost.ecomplexityFun_eq_iSup_distributionalComplexity`
for computing a total function over finitely many players with finite input types. -/
theorem ecomplexityFun_eq_iSup_distributionalComplexity [Finite ι] [∀ i, Finite (X i)] [Nonempty Z]
    (f : (∀ i, X i) → Z) :
    ecomplexityFun ε f =
      ⨆ ν : PMF (∀ i, X i), Protocol.distributionalComplexity ε (fun x z => f x = z) ν :=
  RandomizedCost.ecomplexityFun_eq_iSup_distributionalComplexity
    ⟨.output (Classical.arbitrary Z), rfl⟩ f

/-! ### Majority error amplification for Boolean NOF protocols -/

section Amplification

/-- Strict majority of `2 r` independent runs of a Boolean public-coin NOF protocol `μ`. -/
noncomputable def amplify (μ : PublicCoin X Bool) (r : ℕ) : PublicCoin X Bool :=
  (Protocol.randomizedCost X Bool).amplify (@Protocol.runAll ι X Bool Bool) μ r

variable {μ : PublicCoin X Bool} {f : (∀ i, X i) → Bool}

/-- The majority of `2 r` runs writes at most `2 r` times as many bits. -/
theorem depth_amplify_le {c : ℕ} (hμ : μ.depth ≤ c) (r : ℕ) :
    (μ.amplify r).depth ≤ 2 * r * c :=
  (Protocol.randomizedCost X Bool).maxCost_amplify_le Protocol.depth_runAll_le hμ r

/-- Multiparty NOF instantiation of `RandomizedCost.Solves.amplify` (after
[Kushilevitz and Nisan, Chapter 3][KushilevitzNisan1997]): if `μ` computes `f` on `A` with error
`ε ≤ 1 / 2`, then the strict majority of `2 r` independent runs computes `f` on `A` with error
`(4 ε (1 - ε)) ^ r`. -/
theorem Solves.amplify (hμ : μ.Solves ε (fun x b => f x = b) A) (hε : ε ≤ 1 / 2) (r : ℕ) :
    (μ.amplify r).Solves ((4 * ε * (1 - ε)) ^ r) (fun x b => f x = b) A :=
  RandomizedCost.Solves.amplify (C := Protocol.randomizedCost X Bool) Protocol.run_runAll hμ hε r

/-- Multiparty NOF instantiation of `RandomizedCost.ecomplexity_le_two_mul_mul` on `A`: reducing
error `ε ≤ 1 / 2` to `(4 ε (1 - ε)) ^ r` multiplies complexity by at most `2 r`. -/
theorem ecomplexity_le_two_mul_mul (hε : ε ≤ 1 / 2) (r : ℕ) :
    ecomplexity ((4 * ε * (1 - ε)) ^ r) (fun x b => f x = b) A ≤
      2 * r * ecomplexity ε (fun x b => f x = b) A :=
  RandomizedCost.ecomplexity_le_two_mul_mul Protocol.run_runAll Protocol.depth_runAll_le
    ⟨.output true, rfl⟩ hε r

/-- Multiparty NOF instantiation of `RandomizedCost.ecomplexityFun_le_two_mul_mul` for total
Boolean functions. -/
theorem ecomplexityFun_le_two_mul_mul (hε : ε ≤ 1 / 2) (r : ℕ) :
    ecomplexityFun ((4 * ε * (1 - ε)) ^ r) f ≤ 2 * r * ecomplexityFun ε f :=
  RandomizedCost.ecomplexityFun_le_two_mul_mul Protocol.run_runAll Protocol.depth_runAll_le
    ⟨.output true, rfl⟩ hε r

/-- Specialization of `ecomplexityFun_le_two_mul_mul` from error `1 / 3`: `2 r` NOF runs reduce the
error to `(8 / 9) ^ r`. -/
theorem ecomplexityFun_le_two_mul_mul_one_third (r : ℕ) :
    ecomplexityFun ((8 / 9) ^ r) f ≤ 2 * r * ecomplexityFun (1 / 3) f :=
  RandomizedCost.ecomplexityFun_le_two_mul_mul_one_third Protocol.run_runAll
    Protocol.depth_runAll_le ⟨.output true, rfl⟩ r

end Amplification

end PublicCoin

end Cslib.Communication.NOF
