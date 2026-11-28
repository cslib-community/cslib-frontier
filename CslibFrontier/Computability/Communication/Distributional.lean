/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Randomized

/-!
# Distributional complexity and Yao's minimax principle

The *distributional complexity* `D^ν_ε(R)` of a relation `R` under a distribution `ν` on the pairs
of inputs is the least depth of a deterministic protocol that errs with probability at most `ε` on
inputs drawn from `ν` (`Protocol.distributionalComplexity`), specializing
`Cslib.RandomizedCost.distributionalComplexity` to `Protocol.randomizedCost`
[Kushilevitz and Nisan, Chapter 3][KushilevitzNisan1997].

*Yao's minimax principle* [Yao1977] says that randomized protocols are exactly as good as
deterministic protocols against the hardest distribution: the public-coin complexity of `R` on
`A × B` with error `ε` is the largest distributional complexity with error `ε` under a
distribution on `A × B` (`PublicCoin.ecomplexity_eq_iSup_distributionalComplexity`), when the
inputs are finite and there is some output. Both directions instantiate `Cslib.RandomizedCost`:
the averaging argument (`PublicCoin.distributionalComplexity_le_ecomplexity`) and minimax duality
(`PublicCoin.ecomplexity_le_of_forall_distributionalComplexity_le`).

## Main definitions

* `Cslib.Communication.Protocol.distributionalComplexity`: the distributional complexity.

## Main results

* `Cslib.Communication.PublicCoin.distributionalComplexity_le_ecomplexity`: the easy direction of
  Yao's principle.
* `Cslib.Communication.PublicCoin.ecomplexity_le_of_forall_distributionalComplexity_le`: the hard
  direction of Yao's principle.
* `Cslib.Communication.PublicCoin.ecomplexity_eq_iSup_distributionalComplexity`,
  `Cslib.Communication.PublicCoin.ecomplexityFun_eq_iSup_distributionalComplexity`: Yao's
  minimax principle.

## References

* [E. Kushilevitz and N. Nisan, *Communication Complexity*][KushilevitzNisan1997]
* [A. C.-C. Yao, *Probabilistic computations: toward a unified measure of complexity*][Yao1977]
-/

@[expose] public section

namespace Cslib.Communication

open Probability

variable {X Y Z : Type*}

namespace Protocol

/-- The *distributional complexity* `D^ν_ε(R)` of `R` under a distribution `ν` on the pairs of
inputs: the least depth of a deterministic protocol whose output on a pair of inputs drawn from `ν`
is not related to them by `R` with probability at most `ε`, or `⊤` if there is none. -/
noncomputable def distributionalComplexity (ε : ℝ) (R : X → Y → Z → Prop) (ν : PMF (X × Y)) :
    ℕ∞ :=
  (randomizedCost X Y Z).distributionalComplexity ε (fun q z => R q.1 q.2 z) ν

variable {p : Protocol X Y Z} {ε ε' : ℝ} {R : X → Y → Z → Prop} {ν : PMF (X × Y)}

theorem distributionalComplexity_le_depth (hp : p.distributionalError ν R ≤ ε) :
    distributionalComplexity ε R ν ≤ p.depth :=
  RandomizedCost.distributionalComplexity_le_cost hp

theorem le_distributionalComplexity_iff {k : ℕ∞} :
    k ≤ distributionalComplexity ε R ν ↔
      ∀ p : Protocol X Y Z, p.distributionalError ν R ≤ ε → k ≤ p.depth :=
  RandomizedCost.le_distributionalComplexity_iff

theorem distributionalComplexity_le_iff {k : ℕ} :
    distributionalComplexity ε R ν ≤ k ↔
      ∃ p : Protocol X Y Z, p.distributionalError ν R ≤ ε ∧ p.depth ≤ k :=
  RandomizedCost.distributionalComplexity_le_iff

/-- Allowing more error makes a relation easier. -/
theorem distributionalComplexity_anti (hε : ε ≤ ε') :
    distributionalComplexity ε' R ν ≤ distributionalComplexity ε R ν :=
  RandomizedCost.distributionalComplexity_anti hε

end Protocol

namespace PublicCoin

variable {ε : ℝ} {R : X → Y → Z → Prop} {A : Set X} {B : Set Y}

/-- **Yao's principle, the easy direction**: under every distribution `ν` on `A × B`, the
distributional complexity with error `ε` is at most the public-coin complexity on `A × B` with
error `ε`. -/
theorem distributionalComplexity_le_ecomplexity {ν : PMF (X × Y)}
    (hν : ∀ q ∈ ν.support, q.1 ∈ A ∧ q.2 ∈ B) :
    Protocol.distributionalComplexity ε R ν ≤ ecomplexity ε R A B :=
  ecomplexity_eq_randomizedCost ε R A B ▸
    RandomizedCost.distributionalComplexity_le_ecomplexity hν

/-- **Yao's principle, the hard direction**: on finite inputs, if under every distribution on
`A × B` some deterministic protocol sending at most `c` bits errs with probability at most `ε`,
then some public-coin protocol sending at most `c` bits errs with probability at most `ε` on every
pair of inputs from `A × B`. The protocol draws from finitely many deterministic protocols. -/
theorem ecomplexity_le_of_forall_distributionalComplexity_le [Finite X] [Finite Y] [Nonempty Z]
    {c : ℕ} (h : ∀ ν : PMF (X × Y), (∀ q ∈ ν.support, q.1 ∈ A ∧ q.2 ∈ B) →
      Protocol.distributionalComplexity ε R ν ≤ c) :
    ecomplexity ε R A B ≤ c :=
  ecomplexity_eq_randomizedCost ε R A B ▸
    RandomizedCost.ecomplexity_le_of_forall_distributionalComplexity_le
      ⟨.output (Classical.arbitrary Z), Nat.zero_le c⟩ h

/-- **Yao's principle**: on finite inputs, the public-coin complexity on `A × B` with error `ε` is
at most `c` exactly when the distributional complexity with error `ε` is at most `c` under every
distribution on `A × B`. -/
theorem ecomplexity_le_iff_forall_distributionalComplexity_le [Finite X] [Finite Y] [Nonempty Z]
    {c : ℕ} :
    ecomplexity ε R A B ≤ c ↔ ∀ ν : PMF (X × Y), (∀ q ∈ ν.support, q.1 ∈ A ∧ q.2 ∈ B) →
      Protocol.distributionalComplexity ε R ν ≤ c :=
  ecomplexity_eq_randomizedCost ε R A B ▸
    RandomizedCost.ecomplexity_le_iff_forall_distributionalComplexity_le
      ⟨.output (Classical.arbitrary Z), Nat.zero_le c⟩

/-- **Yao's minimax principle** [Kushilevitz and Nisan, Theorem 3.20][KushilevitzNisan1997]: on
finite inputs, the public-coin complexity on `A × B` with error `ε` is the largest distributional
complexity with error `ε` under a distribution on `A × B`. -/
theorem ecomplexity_eq_iSup_distributionalComplexity [Finite X] [Finite Y] [Nonempty Z] :
    ecomplexity ε R A B = ⨆ (ν : PMF (X × Y)) (_ : ∀ q ∈ ν.support, q.1 ∈ A ∧ q.2 ∈ B),
      Protocol.distributionalComplexity ε R ν :=
  (ecomplexity_eq_randomizedCost ε R A B).trans <|
    RandomizedCost.ecomplexity_eq_iSup_distributionalComplexity
      ⟨.output (Classical.arbitrary Z), rfl⟩

/-- **Yao's minimax principle** for computing a function: on finite inputs, the public-coin
complexity of `f` with error `ε` is the largest distributional complexity of `f` with error `ε`. -/
theorem ecomplexityFun_eq_iSup_distributionalComplexity [Finite X] [Finite Y] [Nonempty Z]
    (f : X → Y → Z) :
    ecomplexityFun ε f = ⨆ ν : PMF (X × Y),
      Protocol.distributionalComplexity ε (fun x y z => f x y = z) ν := by
  simpa only [ecomplexityFun, ecomplexity_eq_randomizedCost, Set.univ_prod_univ,
    RandomizedCost.ecomplexityFun, Protocol.distributionalComplexity] using
    (Protocol.randomizedCost X Y Z).ecomplexityFun_eq_iSup_distributionalComplexity
      ⟨.output (Classical.arbitrary Z), rfl⟩ (fun q => f q.1 q.2)

end PublicCoin

end Cslib.Communication
