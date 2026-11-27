/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.CHSHRigidity
public import CslibFrontier.Foundations.Quantum.Algebra.Braiding

/-!
# The anticommutation test

The Pauli braiding test of [Natarajan and Vidick, §4.1, Figure 2][NatarajanVidick2017]
(arXiv:1610.03574v1, p. 17) certifies anticommutation through an *anticommutation game*: for each
pair `(a, b)` with `a · b = 1`, the players play a game whose second player answers the special
questions `q_X`, `q_Z` with observables `X'(a, b)`, `Z'(a, b)`, and near-optimal play forces these
to nearly anticommute. The CHSH game is such a game (their Lemma 9, p. 14). The consistency test
then ties `X'(a, b)` to the first player's linearity-test observable `X(a)`, and `Z'(a, b)` to
`Z(b)`.

This file proves the **CHSH operator-transfer step** toward
[Natarajan and Vidick, §4.3.2, Lemma 18][NatarajanVidick2017] (p. 21), for commuting-operator
strategies in any star-ordered algebra with a continuous functional calculus, with explicit
constants. Its inputs are a common state `φ`, for every pair with `a · b = 1` a CHSH strategy
`G(a, b)` in that state whose first player's observables `X'(a, b)`, `Z'(a, b)` play the role of the
source's special-question observables (the roles in CHSH are symmetric), its winning probability
`cos²(π/8) - ε(a, b)`, and contractions `X(a)`, `Z(b)` commuting with `Z'(a, b)`, `X'(a, b)`
together with their consistency distances. Then (`Cslib.PCP.oddExpect_norm_anticomm_sq_le_of_chsh`)

`E_{a,b} [a · b = 1] ‖X(a) Z(b) + Z(b) X(a)‖²_φ ≤
9 (E [a · b = 1] ‖X(a) - X'(a, b)‖²_φ + E [a · b = 1] ‖Z(b) - Z'(a, b)‖²_φ +
K E [a · b = 1] ε(a, b))`,

with each masked average `E [a · b = 1]` written `Cslib.BitString.oddExpect`

with `K = (4 + 2√2)² · 8√2` (`Cslib.PCP.chshAnticommConst`, value
`Cslib.PCP.chshAnticommConst_eq`): CHSH rigidity (`Cslib.PCP.CommutingStrategy.anticomm_of_chsh`)
bounds the anticommutation of `X'`, `Z'`, and the transfer through consistency
(`Cslib.Quantum.norm_mul_sub_smul_mul_sq_le_of_consistent`) moves it to `X`, `Z`. Only
contractions are needed: the observables of arbitrary, non-projective binary measurements qualify
(`Cslib.Quantum.Measurement.star_observable_mul_self_le_one`), like the source's special-question
marginals. Composed with the braiding and Pauli-family bounds
(`Cslib.Quantum.expect_norm_pauliFamily_sub_sq_le_of_anticommute`), which use unitaries, this
bounds the Pauli-family defect by the consistency distances, the CHSH deficits and the linearity
defects (`Cslib.PCP.expect_norm_pauliFamily_sub_sq_le_of_chsh`).

**Relation to the source.** The source derives the conditional anticommutation estimate
`E_{a,b | a·b = 1}` from the tested strategy; here the strategies, the consistency distances and the
common state are inputs. The averages are masked and unconditional: for `n ≥ 1` the pairs with
`a · b = 1` have probability `(1 - 2⁻ⁿ) / 2`, so each masked average is that factor times the
conditional one, and for `n = 0` there are no such pairs and the masked averages vanish. The
verifier-level CHSH estimate from a single tested strategy is
`Cslib.PCP.expect_norm_pauliBraidingBasis_anticomm_sq_le` in
`CslibFrontier/Computability/PCP/TwoProverGame/PauliBraidingAnticommutation.lean`.
It uses conditional averaging and the consistency and anticommutation branch scores.
The full Pauli braiding rigidity theorem is tracked in cslib-community/cslib-frontier#6149.

## Main definitions

* `Cslib.PCP.chshAnticommConst`: the constant `(4 + 2√2)² · 8√2`.

## Main results

* `Cslib.PCP.oddExpect_norm_anticomm_sq_le_of_chsh`: the CHSH operator transfer, anticommutation of
  the consistent contractions from the CHSH anticommutation test.
* `Cslib.PCP.expect_norm_pauliFamily_sub_sq_le_of_chsh`: the Pauli-family defect from the CHSH
  anticommutation test, consistency and linearity.

## References

* [A. Natarajan and T. Vidick, *A quantum linearity test for robustly verifying
  entanglement*][NatarajanVidick2017]
-/

public section

namespace Cslib.PCP

open Finset Quantum
open scoped BigOperators Real

/-- The constant `(4 + 2√2)² · 8√2` relating the squared anticommutation defect of a CHSH strategy
to its deficit from the optimal winning probability. -/
noncomputable def chshAnticommConst : ℝ :=
  (4 + 2 * √2) ^ 2 * (8 * √2)

theorem chshAnticommConst_eq : chshAnticommConst = (4 + 2 * √2) ^ 2 * (8 * √2) := by
  unfold chshAnticommConst; rfl

theorem chshAnticommConst_nonneg : 0 ≤ chshAnticommConst := by
  rw [chshAnticommConst_eq]; positivity

variable {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [Algebra ℂ 𝒜]
  [StarModule ℂ 𝒜] [SelfAdjointDecompose 𝒜] [TopologicalSpace 𝒜]
  [ContinuousFunctionalCalculus ℝ 𝒜 IsSelfAdjoint] [NonnegSpectrumClass ℝ 𝒜]

/-- The squared anticommutation defect of the first player's observables in a CHSH strategy is at
most `K ε` when it wins with probability at least `cos²(π/8) - ε`. -/
theorem norm_anticomm_sq_le_of_chsh (G : CommutingStrategy Bool Bool Bool Bool 𝒜) {ε : ℝ}
    (h : Real.cos (π / 8) ^ 2 - ε ≤ TwoProverGame.chsh.commutingWinProb G) :
    G.state.norm ((G.alice false).observable * (G.alice true).observable +
      (G.alice true).observable * (G.alice false).observable) ^ 2 ≤ chshAnticommConst * ε := by
  have hε : 0 ≤ ε := by linarith [TwoProverGame.commutingWinProb_chsh_le G]
  have h₁ := AlgState.approx_iff.mp (G.anticomm_of_chsh h)
  rw [sub_zero] at h₁
  calc _ ≤ chshRigidityError ε ^ 2 := pow_le_pow_left₀ (G.state.norm_nonneg _) h₁ 2
    _ = chshAnticommConst * ε := by
        unfold chshRigidityError chshAnticommConst
        rw [mul_pow, Real.sq_sqrt (by positivity)]
        ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **CHSH operator transfer** (a step toward [Natarajan and Vidick, §4.3.2, Lemma 18]). For every
pair with `a · b = 1`, let the CHSH strategy `G(a, b)` in the common state `φ` have first-player
observables `X'(a, b)`, `Z'(a, b)` and win with probability at least `cos²(π/8) - ε(a, b)`. If the
contractions `X(a)`, `Z(b)` commute with `Z'(a, b)`, `X'(a, b)` on these pairs, the averaged masked
anticommutation defect of `X`, `Z` is at most
`9 (E [a·b = 1] ‖X(a) - X'(a, b)‖² + E [a·b = 1] ‖Z(b) - Z'(a, b)‖² + K E [a·b = 1] ε(a, b))`. -/
theorem oddExpect_norm_anticomm_sq_le_of_chsh (φ : AlgState 𝒜) (X Z : (ι → Bool) → 𝒜)
    (G : (ι → Bool) → (ι → Bool) → CommutingStrategy Bool Bool Bool Bool 𝒜)
    (hφ : ∀ a b, a ⬝ᵥ b = true → (G a b).state = φ) (hX : ∀ a, star (X a) * X a ≤ 1)
    (hZ : ∀ b, star (Z b) * Z b ≤ 1)
    (hXZ' : ∀ a b, a ⬝ᵥ b = true → Commute (X a) ((G a b).alice true).observable)
    (hZX' : ∀ a b, a ⬝ᵥ b = true → Commute (Z b) ((G a b).alice false).observable)
    (ε : (ι → Bool) → (ι → Bool) → ℝ)
    (hε : ∀ a b, a ⬝ᵥ b = true →
      Real.cos (π / 8) ^ 2 - ε a b ≤ TwoProverGame.chsh.commutingWinProb (G a b)) :
    BitString.oddExpect (fun a b => φ.norm (X a * Z b + Z b * X a) ^ 2) ≤
      9 * (BitString.oddExpect (fun a b => φ.norm (X a - ((G a b).alice false).observable) ^ 2) +
        BitString.oddExpect (fun a b => φ.norm (Z b - ((G a b).alice true).observable) ^ 2) +
        chshAnticommConst * BitString.oddExpect ε) := by
  rw [← BitString.oddExpect_const_mul, ← BitString.oddExpect_add, ← BitString.oddExpect_add,
    ← BitString.oddExpect_const_mul]
  refine BitString.oddExpect_mono fun a b hab => ?_
  have htr := norm_mul_sub_smul_mul_sq_le_of_consistent φ (hX a) (hZ b)
    ((G a b).alice false).star_observable_mul_self_le_one
    ((G a b).alice true).star_observable_mul_self_le_one (hXZ' a b hab) (hZX' a b hab)
    (s := -1) (by simp)
  have hR := norm_anticomm_sq_le_of_chsh (G a b) (hε a b hab)
  rw [hφ a b hab] at hR
  simp only [neg_one_smul, sub_neg_eq_add] at htr
  rw [add_comm (Z b * X a)] at htr
  linarith

/-- **The Pauli-family defect from the CHSH anticommutation test, consistency and linearity.** Let
Alice's unitaries `X(a)`, `Z(b)` with `X(0) = 1` have consistent unitary copies `X''(a)`, `Z''(b)`
for Bob, commuting with them, as in the linearity and consistency tests, and let the CHSH
strategies `G(a, b)` be as in `Cslib.PCP.oddExpect_norm_anticomm_sq_le_of_chsh`. Then the
multiplicative defect `E_{p,q} ‖P(p) P(q) - P(pq)‖²_φ` of the Pauli family
`P(a, b, s) = s X(a) Z(b)` is bounded by the consistency distances, the CHSH deficits and the
linearity defects. -/
theorem expect_norm_pauliFamily_sub_sq_le_of_chsh (φ : AlgState 𝒜) (X Z X'' Z'' : (ι → Bool) → 𝒜)
    (G : (ι → Bool) → (ι → Bool) → CommutingStrategy Bool Bool Bool Bool 𝒜)
    (hφ : ∀ a b, a ⬝ᵥ b = true → (G a b).state = φ) (hX : ∀ a, X a ∈ unitary 𝒜)
    (hZ : ∀ b, Z b ∈ unitary 𝒜) (hX'' : ∀ a, X'' a ∈ unitary 𝒜) (hZ'' : ∀ b, Z'' b ∈ unitary 𝒜)
    (hXZ'' : ∀ a b, Commute (X a) (Z'' b)) (hZZ'' : ∀ b b', Commute (Z b) (Z'' b'))
    (hZX'' : ∀ b a, Commute (Z b) (X'' a)) (hX0 : X 0 = 1)
    (hXZ' : ∀ a b, a ⬝ᵥ b = true → Commute (X a) ((G a b).alice true).observable)
    (hZX' : ∀ a b, a ⬝ᵥ b = true → Commute (Z b) ((G a b).alice false).observable)
    (ε : (ι → Bool) → (ι → Bool) → ℝ)
    (hε : ∀ a b, a ⬝ᵥ b = true →
      Real.cos (π / 8) ^ 2 - ε a b ≤ TwoProverGame.chsh.commutingWinProb (G a b)) :
    𝔼 p, 𝔼 q, φ.norm (pauliFamily X Z p * pauliFamily X Z q - pauliFamily X Z (p * q)) ^ 2 ≤
      5 * (40 * 𝔼 c, φ.norm (Z c - Z'' c) ^ 2 + 32 * 𝔼 a, φ.norm (X a - X'' a) ^ 2 +
        33 * (9 * (BitString.oddExpect
            (fun a b => φ.norm (X a - ((G a b).alice false).observable) ^ 2) +
          BitString.oddExpect (fun a b => φ.norm (Z b - ((G a b).alice true).observable) ^ 2) +
          chshAnticommConst * BitString.oddExpect ε)) +
        𝔼 a, 𝔼 a', φ.norm (X a * X a' - X (a + a')) ^ 2 +
        33 * 𝔼 b, 𝔼 b', φ.norm (Z b * Z b' - Z (b + b')) ^ 2) := by
  have h₁ := expect_norm_pauliFamily_sub_sq_le_of_anticommute φ X Z X'' Z'' hX hZ hX'' hZ'' hXZ''
    hZZ'' hZX'' hX0
  have h₂ := oddExpect_norm_anticomm_sq_le_of_chsh φ X Z G hφ
    (fun a => (Unitary.star_mul_self_of_mem (hX a)).le)
    (fun b => (Unitary.star_mul_self_of_mem (hZ b)).le) hXZ' hZX' ε hε
  refine h₁.trans ?_
  linarith

end Cslib.PCP
