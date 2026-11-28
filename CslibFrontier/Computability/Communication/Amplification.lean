/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Operations
public import CslibFrontier.Computability.Communication.Randomized

/-!
# Amplification of public-coin protocols

A public-coin protocol computing a Boolean function `f` with error `ε ≤ 1 / 2` can be run `2 r`
times with independent coins, answering with the strict majority of the outputs
(`BitString.strictMajorityOn`) [Kushilevitz and Nisan, Chapter 3][KushilevitzNisan1997]. This
module instantiates the generic majority-amplification kernel of `Cslib.RandomizedCost` on
`Protocol.randomizedCost` and `Protocol.runAll`: `2 r` runs reduce error `ε ≤ 1 / 2` to
`(4 ε (1 - ε)) ^ r` at `2 r` times the communication cost (`PublicCoin.ecomplexity_le_two_mul_mul`,
`PublicCoin.ecomplexityFun_le_two_mul_mul`), and from `1 / 3` to `(8 / 9) ^ r`
(`PublicCoin.ecomplexityFun_le_two_mul_mul_one_third`).

## Main definitions

* `Cslib.Communication.PublicCoin.amplify`: the strict majority of `2 r` independent runs.

## Main results

* `Cslib.Communication.PublicCoin.Solves.amplify`: the error of the majority of `2 r` runs.
* `Cslib.Communication.PublicCoin.ecomplexity_le_two_mul_mul`,
  `Cslib.Communication.PublicCoin.ecomplexityFun_le_two_mul_mul`: amplification of public-coin
  protocols for Boolean functions.
* `Cslib.Communication.PublicCoin.ecomplexityFun_le_two_mul_mul_one_third`: amplification from
  error `1 / 3`.

## References

* [E. Kushilevitz and N. Nisan, *Communication Complexity*][KushilevitzNisan1997]
-/

@[expose] public section

namespace Cslib.Communication

namespace PublicCoin

variable {X Y : Type*}

/-- The strict majority of `2 r` independent runs of `μ`. -/
noncomputable def amplify (μ : PublicCoin X Y Bool) (r : ℕ) : PublicCoin X Y Bool :=
  (Protocol.randomizedCost X Y Bool).amplify (@Protocol.runAll X Y Bool Bool) μ r

variable {μ : PublicCoin X Y Bool} {f : X → Y → Bool} {A : Set X} {B : Set Y} {ε : ℝ}

/-- The majority of `2 r` runs sends at most `2 r` times as many bits. -/
theorem depth_amplify_le {c : ℕ} (hμ : μ.depth ≤ c) (r : ℕ) : (μ.amplify r).depth ≤ 2 * r * c :=
  (Protocol.randomizedCost X Y Bool).maxCost_amplify_le Protocol.depth_runAll_le hμ r

/-- **Amplification**: if `μ` computes `f` on `A × B` with error `ε ≤ 1 / 2`, then the majority of
`2 r` independent runs computes it with error `(4 ε (1 - ε)) ^ r`. -/
theorem Solves.amplify (hμ : μ.Solves ε (fun x y b => f x y = b) A B) (hε : ε ≤ 1 / 2)
    (r : ℕ) : (μ.amplify r).Solves ((4 * ε * (1 - ε)) ^ r) (fun x y b => f x y = b) A B :=
  solves_iff_randomizedCost.mpr <|
    RandomizedCost.Solves.amplify
      (f := fun q : X × Y => f q.1 q.2)
      (fun ps g q => Protocol.run_runAll ps g q.1 q.2)
      (solves_iff_randomizedCost.mp hμ) hε r

/-- **Amplification** of public-coin protocols: for error `ε ≤ 1 / 2`, computing a Boolean function
on `A × B` with error `(4 ε (1 - ε)) ^ r` costs at most `2 r` times as much as with error `ε`. -/
theorem ecomplexity_le_two_mul_mul (hε : ε ≤ 1 / 2) (r : ℕ) :
    ecomplexity ((4 * ε * (1 - ε)) ^ r) (fun x y b => f x y = b) A B ≤
      2 * r * ecomplexity ε (fun x y b => f x y = b) A B := by
  simpa only [ecomplexity_eq_randomizedCost] using
    (Protocol.randomizedCost X Y Bool).ecomplexity_le_two_mul_mul
      (f := fun q : X × Y => f q.1 q.2)
      (fun ps g q => Protocol.run_runAll ps g q.1 q.2)
      Protocol.depth_runAll_le ⟨.output true, rfl⟩ hε r

/-- **Amplification** of public-coin protocols for Boolean functions: for error `ε ≤ 1 / 2`,
computing `f` with error `(4 ε (1 - ε)) ^ r` costs at most `2 r` times as much as with error
`ε`. -/
theorem ecomplexityFun_le_two_mul_mul (hε : ε ≤ 1 / 2) (r : ℕ) :
    ecomplexityFun ((4 * ε * (1 - ε)) ^ r) f ≤ 2 * r * ecomplexityFun ε f :=
  ecomplexity_le_two_mul_mul hε r

/-- **Amplification** from error `1 / 3`: `2 r` runs reduce the error to `(8 / 9) ^ r`. -/
theorem ecomplexityFun_le_two_mul_mul_one_third (r : ℕ) :
    ecomplexityFun ((8 / 9) ^ r) f ≤ 2 * r * ecomplexityFun (1 / 3) f := by
  simpa only [ecomplexityFun, ecomplexity_eq_randomizedCost, Set.univ_prod_univ,
    RandomizedCost.ecomplexityFun] using
    (Protocol.randomizedCost X Y Bool).ecomplexityFun_le_two_mul_mul_one_third
      (f := fun q : X × Y => f q.1 q.2)
      (fun ps g q => Protocol.run_runAll ps g q.1 q.2)
      Protocol.depth_runAll_le ⟨.output true, rfl⟩ r

end PublicCoin

end Cslib.Communication
