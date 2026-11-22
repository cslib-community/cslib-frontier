/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.NOF.Protocol
public import CslibFrontier.Probability.Minimax
public import Cslib.Probability.PMF
public import Mathlib.Basic.Real.Basic
import CslibFrontier.Foundations.Data.ENat.IInf
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.ToReal

/-!
# Randomized number-on-forehead protocols

In a *public-coin* number-on-forehead protocol the players share random bits, which they use to
draw a deterministic protocol from a distribution and run it; so a public-coin protocol is a
distribution over deterministic NOF protocols (`NOF.PublicCoin`), as in the two-party model
`Cslib.Communication.PublicCoin`. It solves a relation `R` on a set `A` of inputs with error `ε`
when on every input of `A` its output is not related to the input with probability at most `ε`
(`NOF.PublicCoin.Solves`). Its cost bounds the tree depth over the random choices
(`NOF.PublicCoin.depth`), and the public-coin communication complexity is the least cost
(`NOF.PublicCoin.ecomplexity`, `NOF.PublicCoin.ecomplexityFun`). Deterministic protocols are
public-coin protocols (`NOF.PublicCoin.ecomplexity_le_protocol`).

If a public-coin protocol has error at most `ε` on every input of `A`, then for every distribution
`ν` on `A` some protocol it can draw errs with probability at most `ε` on inputs drawn from `ν`
(`NOF.PublicCoin.Solves.exists_distributionalError_le`). This averaging argument is the easy
direction of Yao's principle [Yao1977], and turns lower bounds on deterministic protocols over a
distribution into lower bounds on public-coin protocols.

## Main definitions

* `Cslib.Communication.NOF.PublicCoin`: public-coin NOF protocols, with
  `NOF.PublicCoin.depth`, `NOF.PublicCoin.errorProb`, `NOF.PublicCoin.Solves`,
  `NOF.PublicCoin.ecomplexity` and `NOF.PublicCoin.ecomplexityFun`.
* `Cslib.Communication.NOF.Protocol.distributionalError`: the error of a deterministic protocol on
  inputs drawn from a distribution.

## Main results

* `Cslib.Communication.NOF.PublicCoin.ecomplexity_le_protocol`: randomness does not hurt.
* `Cslib.Communication.NOF.PublicCoin.Solves.exists_distributionalError_le`: the averaging
  argument.

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
* [A. C.-C. Yao, *Probabilistic computations: toward a unified measure of complexity*][Yao1977]
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

/-- The error of a deterministic protocol on inputs drawn from `ν`: the probability that its output
on an input drawn from `ν` is not related to it by `R`. -/
noncomputable def Protocol.distributionalError (p : Protocol X Z) (ν : PMF (∀ i, X i))
    (R : (∀ i, X i) → Z → Prop) : ℝ :=
  PMF.errorProb (fun x (p : Protocol X Z) => R x (p.run x)) ν p

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
  ⨅ μ : {μ : PublicCoin X Z // μ.Solves ε R A}, μ.1.depth

/-- The public-coin communication complexity of computing `f` with error `ε`: `ecomplexity` of the
relation `f x = z` on all inputs. -/
noncomputable def ecomplexityFun (ε : ℝ) (f : (∀ i, X i) → Z) : ℕ∞ :=
  ecomplexity ε (fun x z => f x = z) Set.univ

variable {μ : PublicCoin X Z} {p : Protocol X Z} {R : (∀ i, X i) → Z → Prop}
  {A A' : Set (∀ i, X i)} {ε ε' : ℝ} {x : ∀ i, X i}

theorem depth_le_iff {c : ℕ∞} : μ.depth ≤ c ↔ ∀ p ∈ μ.support, (p.depth : ℕ∞) ≤ c :=
  PMF.maxCost_le_iff

theorem depth_le_depth (hp : p ∈ μ.support) : (p.depth : ℕ∞) ≤ μ.depth :=
  PMF.le_maxCost hp

@[simp] theorem depth_pure (p : Protocol X Z) : depth (PMF.pure p) = p.depth :=
  PMF.maxCost_pure Protocol.depth p

theorem errorProb_nonneg : 0 ≤ μ.errorProb R x :=
  PMF.errorProb_nonneg

theorem errorProb_le_one : μ.errorProb R x ≤ 1 :=
  PMF.errorProb_le_one

open Classical in
theorem errorProb_pure (p : Protocol X Z) (R : (∀ i, X i) → Z → Prop) (x : ∀ i, X i) :
    errorProb (PMF.pure p) R x = if R x (p.run x) then 0 else 1 :=
  PMF.errorProb_pure (fun (p : Protocol X Z) x => R x (p.run x)) p x

theorem Solves.mono (h : μ.Solves ε R A) (hε : ε ≤ ε') (hA : A' ⊆ A) : μ.Solves ε' R A' :=
  fun x hx => (h x (hA hx)).trans hε

/-- A deterministic protocol solving `R` is a public-coin protocol solving it with any nonnegative
error. -/
theorem solves_pure (hp : p.Solves R A) (hε : 0 ≤ ε) : Solves (PMF.pure p) ε R A :=
  fun x hx => PMF.errorProb_pure_le (fun (p : Protocol X Z) x => R x (p.run x)) (hp x hx) hε

/-- **The averaging argument**, the easy direction of Yao's principle: if `μ` solves `R` on `A`
with error `ε`, then for every distribution `ν` on `A` some protocol that `μ` can draw errs with
probability at most `ε` on inputs drawn from `ν`. -/
theorem Solves.exists_distributionalError_le (h : μ.Solves ε R A) (ν : PMF (∀ i, X i))
    (hν : ∀ x ∈ ν.support, x ∈ A) : ∃ p ∈ μ.support, p.distributionalError ν R ≤ ε :=
  PMF.exists_errorProb_le ν fun x hx => h x (hν x hx)

theorem ecomplexity_le_depth (h : μ.Solves ε R A) : ecomplexity ε R A ≤ μ.depth :=
  ENat.iInf_subtype_le h

theorem le_ecomplexity_iff {k : ℕ∞} :
    k ≤ ecomplexity ε R A ↔ ∀ μ : PublicCoin X Z, μ.Solves ε R A → k ≤ μ.depth :=
  ENat.le_iInf_subtype_iff

theorem ecomplexity_le_iff {k : ℕ} :
    ecomplexity ε R A ≤ k ↔ ∃ μ : PublicCoin X Z, μ.Solves ε R A ∧ μ.depth ≤ k :=
  ENat.iInf_subtype_le_natCast_iff

/-- Allowing more error makes a relation easier. -/
theorem ecomplexity_anti (hε : ε ≤ ε') : ecomplexity ε' R A ≤ ecomplexity ε R A :=
  ENat.iInf_subtype_mono fun _ hμ => hμ.mono hε subset_rfl

/-- Solving a relation on a larger set is harder. -/
theorem ecomplexity_mono (hA : A' ⊆ A) : ecomplexity ε R A' ≤ ecomplexity ε R A :=
  ENat.iInf_subtype_mono fun _ hμ => hμ.mono le_rfl hA

/-- Public-coin protocols with nonnegative error are at least as good as deterministic ones. -/
theorem ecomplexity_le_protocol (hε : 0 ≤ ε) : ecomplexity ε R A ≤ Protocol.ecomplexity R A :=
  ENat.iInf_subtype_le_iInf_subtype PMF.pure (fun _ hp => solves_pure hp hε)
    fun p _ => (depth_pure p).le

theorem ecomplexityFun_le_protocol {f : (∀ i, X i) → Z} (hε : 0 ≤ ε) :
    ecomplexityFun ε f ≤ Protocol.ecomplexityFun f :=
  ecomplexity_le_protocol hε

end PublicCoin

end Cslib.Communication.NOF
