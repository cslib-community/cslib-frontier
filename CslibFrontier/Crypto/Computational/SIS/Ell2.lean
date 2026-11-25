/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.SIS.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Probability.PMF.Bind
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Short integer solution problem in the Euclidean norm

The Euclidean (`ℓ₂`) formulation of the short integer solution problem from [MicciancioRegev2007]
(§5.1, p. 17), built directly on the parameter family, encodings, and solver model of
`CslibFrontier/Crypto/Computational/SIS/Basic.lean` with no parallel parameter structures:

* `Cslib.Crypto.SIS.IsEll2Solution` ([MicciancioRegev2007], Definition 5.1, p. 17): a nonzero
  integer vector `z` with Euclidean norm `‖z‖₂ ≤ β` and `A z ≡ 0 (mod q)`. For natural-number
  bounds `β`, this is equivalent to the decidable integer inequality `∑ i, z i ^ 2 ≤ β ^ 2`
  (`Cslib.Crypto.SIS.isEll2Solution_nat_iff`).
* `Cslib.Crypto.SIS.exists_isEll2Solution` ([MicciancioRegev2007], Lemma 5.2, p. 17): for every
  nonzero modulus `q`, dimensions `n` and `m > 0`, matrix `A ∈ ℤ_q^{n×m}`, and real bound
  `β ≥ √m · q^{n / m}`, an `ℓ₂`-SIS solution exists by the pigeonhole principle.
* `Cslib.Crypto.sisEll2Experiment` and `Cslib.Crypto.sisEll2Advantage` ([MicciancioRegev2007],
  Definitions 5.1 and 5.3, p. 17): the fixed-instance experiment and solver success probability
  at an arbitrary real Euclidean bound `β : ℝ`.
* `Cslib.Crypto.SISEll2`: the asymptotic hardness hypothesis reusing `SISParams` and
  `SISParams.Solver.IsPPT`, together with the norm-comparison bridges `Cslib.Crypto.SIS.toSISEll2`
  and `Cslib.Crypto.SISEll2.toSIS` to `Cslib.Crypto.SIS`.

`SISEll2` is an explicit computational hardness hypothesis against uniform classical strict PPT
programs, not a theorem. No worst-case lattice reduction is proved in this file.

## Main definitions

* `Cslib.Crypto.SIS.IsEll2Solution`: short nonzero integer kernel vectors in the `ℓ₂` norm.
* `Cslib.Crypto.sisEll2Experiment`, `Cslib.Crypto.sisEll2Advantage`: the fixed-instance `ℓ₂`-SIS
  experiment and its success probability.
* `Cslib.Crypto.SISEll2`: the `ℓ₂`-SIS hardness hypothesis for a `SISParams` family.

## Main results

* `Cslib.Crypto.SIS.isEll2Solution_nat_iff`: integer sum-of-squares characterization for `β : ℕ`.
* `Cslib.Crypto.SIS.IsEll2Solution.mono`: monotonicity of `ℓ₂`-SIS solutions in `β`.
* `Cslib.Crypto.SIS.IsSolution.isEll2Solution`, `Cslib.Crypto.SIS.IsEll2Solution.isSolution`:
  conversions between `ℓ_∞` and `ℓ₂` solutions via `‖z‖_∞ ≤ ‖z‖₂ ≤ √m · ‖z‖_∞`.
* `Cslib.Crypto.SIS.exists_isEll2Solution`: existence of `ℓ₂`-SIS solutions for `β ≥ √m · q^{n/m}`
  ([MicciancioRegev2007], Lemma 5.2, p. 17).
* `Cslib.Crypto.sisEll2Advantage_mono`, `Cslib.Crypto.sisEll2Advantage_le_sisAdvantage`,
  `Cslib.Crypto.sisAdvantage_le_sisEll2Advantage`: fixed-instance advantage bounds.
* `Cslib.Crypto.SIS.toSISEll2`, `Cslib.Crypto.SISEll2.toSIS`: asymptotic bridges between `SIS` and
  `SISEll2`.

## References

* [D. Micciancio and O. Regev, *Worst-Case to Average-Case Reductions Based on Gaussian
  Measures*][MicciancioRegev2007]
* [V. Lyubashevsky, *Lattice Signatures Without Trapdoors*][Lyubashevsky2012]
-/

@[expose] public section

namespace Cslib.Crypto

open Probability
open scoped _root_.Matrix NNReal

namespace SIS

/-- `z` is a short integer solution in the Euclidean (`ℓ₂`) norm for `A` with bound `β`: it is
nonzero, has `‖z‖₂ ≤ β`, and satisfies `A z ≡ 0 (mod q)` ([MicciancioRegev2007], Definition 5.1,
§5.1, p. 17). Since `0 ≤ ‖z‖₂`, negative values of `β` admit no solutions. -/
def IsEll2Solution {q : ℕ} {ρ ι : Type*} [Fintype ι] (A : Matrix ρ ι (ZMod q)) (β : ℝ)
    (z : ι → ℤ) : Prop :=
  z ≠ 0 ∧ ‖WithLp.toLp 2 (fun i => (z i : ℝ))‖ ≤ β ∧ InKernelLattice A z

/-- For a natural-number bound `β`, `SIS.IsEll2Solution A β z` is equivalent to the decidable
integer inequality `∑ i, z i ^ 2 ≤ β ^ 2` alongside `z ≠ 0` and `A z ≡ 0 (mod q)`. -/
theorem isEll2Solution_nat_iff {q : ℕ} {ρ ι : Type*} [Fintype ι]
    (A : Matrix ρ ι (ZMod q)) (β : ℕ) (z : ι → ℤ) :
    IsEll2Solution A (β : ℝ) z ↔
      z ≠ 0 ∧ (∑ i : ι, z i ^ 2) ≤ (β : ℤ) ^ 2 ∧ InKernelLattice A z := by
  refine and_congr_right fun _ => and_congr_left fun _ => ?_
  rw [← sq_le_sq₀ (norm_nonneg _) (Nat.cast_nonneg β), EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  exact_mod_cast Iff.rfl

/-- Increasing the Euclidean norm bound preserves `ℓ₂`-SIS solutions. -/
theorem IsEll2Solution.mono {q : ℕ} {ρ ι : Type*} [Fintype ι]
    {A : Matrix ρ ι (ZMod q)} {β β' : ℝ} {z : ι → ℤ}
    (hz : IsEll2Solution A β z) (hβ : β ≤ β') : IsEll2Solution A β' z :=
  ⟨hz.1, hz.2.1.trans hβ, hz.2.2⟩

/-- Every `ℓ_∞`-SIS solution with bound `β` is an `ℓ₂`-SIS solution with bound `√|ι| · β`. -/
theorem IsSolution.isEll2Solution {q : ℕ} {ρ ι : Type*} [Fintype ι]
    {A : Matrix ρ ι (ZMod q)} {β : ℕ} {z : ι → ℤ} (hz : IsSolution A β z) :
    IsEll2Solution A (Real.sqrt (Fintype.card ι) * β) z := by
  refine ⟨hz.1, ?_, hz.2.2⟩
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), EuclideanSpace.norm_sq_eq, mul_pow,
    Real.sq_sqrt (Nat.cast_nonneg _)]
  exact (Finset.sum_le_sum (g := fun _ => (β : ℝ) ^ 2) fun i _ => by
    rw [WithLp.ofLp_toLp, Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (by exact_mod_cast hz.2.1 i) 2).trans_eq (by simp)

/-- Every `ℓ₂`-SIS solution with real bound `β` is an `ℓ_∞`-SIS solution with bound `⌊β⌋₊`. -/
theorem IsEll2Solution.isSolution {q : ℕ} {ρ ι : Type*} [Fintype ι]
    {A : Matrix ρ ι (ZMod q)} {β : ℝ} {z : ι → ℤ} (hz : IsEll2Solution A β z) :
    IsSolution A ⌊β⌋₊ z := by
  refine ⟨hz.1, fun i => ?_, hz.2.2⟩
  rw [Int.abs_eq_natAbs]
  exact_mod_cast Nat.le_floor <| (show ((z i).natAbs : ℝ) = ‖(z i : ℝ)‖ by
    rw [Real.norm_eq_abs, ← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]).le.trans <|
    (PiLp.norm_apply_le (WithLp.toLp 2 fun j => (z j : ℝ)) i).trans hz.2.1

/-- **Existence of short integer solutions in the `ℓ₂` norm** ([MicciancioRegev2007], Lemma 5.2,
§5.1, p. 17). For every nonzero modulus `q`, dimensions `n` and `m > 0`, matrix `A ∈ ℤ_q^{n×m}`,
and real bound `β ≥ √m · q^{n / m}`, there exists a nonzero integer vector `z : Fin m → ℤ` with
`‖z‖₂ ≤ β` and `A z ≡ 0 (mod q)`. -/
theorem exists_isEll2Solution {q n m : ℕ} [NeZero q] (hm : 0 < m)
    (A : Matrix (Fin n) (Fin m) (ZMod q)) {β : ℝ}
    (hβ : Real.sqrt m * (q : ℝ) ^ ((n : ℝ) / m) ≤ β) :
    ∃ z : Fin m → ℤ, IsEll2Solution A β z := by
  set K : ℕ := ⌊(q : ℝ) ^ ((n : ℝ) / m)⌋₊
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hpow_lt : q ^ n < (K + 1) ^ m := by
    have hpow := pow_lt_pow_left₀
      (by simpa [K] using Nat.lt_floor_add_one ((q : ℝ) ^ ((n : ℝ) / m)))
      (Real.rpow_nonneg hq0 _) hm.ne'
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq0,
      div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr hm.ne'), Real.rpow_natCast] at hpow
    exact_mod_cast hpow
  obtain ⟨x, y, hxy, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun x : Fin m → Fin (K + 1) => A *ᵥ fun i => ((x i : ℕ) : ZMod q))
    (by simpa [Fintype.card_fun, ZMod.card q, Fintype.card_fin] using hpow_lt)
  let z : Fin m → ℤ := fun i => (x i : ℤ) - (y i : ℤ)
  have hsol : IsSolution A K z :=
    ⟨fun h0 => hxy <| funext fun i => Fin.ext (by
       have : (x i : ℤ) - (y i : ℤ) = 0 := congrFun h0 i
       omega),
     fun i => by
       have hx := (x i).isLt
       have hy := (y i).isLt
       simp only [z, abs_le]
       omega,
     by
       rw [InKernelLattice, show (Int.cast ∘ z : Fin m → ZMod q) =
         (fun i => ((x i : ℕ) : ZMod q)) - (fun i => ((y i : ℕ) : ZMod q)) by ext i; simp [z],
         Matrix.mulVec_sub]
       exact sub_eq_zero.mpr hf⟩
  exact ⟨z, hsol.isEll2Solution.mono <| by
    rw [Fintype.card_fin]
    exact (mul_le_mul_of_nonneg_left (Nat.floor_le (Real.rpow_nonneg hq0 _))
      (Real.sqrt_nonneg _)).trans hβ⟩

end SIS

/-! ### The fixed-instance `ℓ₂`-SIS experiment -/

section Experiment

variable (q : ℕ) [NeZero q] {n m : ℕ}

/-- The `ℓ₂`-SIS experiment ([MicciancioRegev2007], Definitions 5.1 and 5.3, §5.1, p. 17) for
modulus `q`, dimensions `n × m`, and real Euclidean bound `β`: the challenger draws a uniform
`A ∈ ℤ_q^{n×m}`; the solver wins when it returns a nonzero integer kernel vector `z` with
`‖z‖₂ ≤ β`. -/
noncomputable def sisEll2Experiment (β : ℝ)
    (S : Matrix (Fin n) (Fin m) (ZMod q) → ProbComp (Fin m → ℤ)) : ProbComp Bool := do
  let A ← ProbComp.uniform (Matrix (Fin n) (Fin m) (ZMod q))
  let z ← S A
  return @decide (SIS.IsEll2Solution A β z) (Classical.propDecidable _)

/-- The `ℓ₂`-SIS advantage of `S`: its success probability in `sisEll2Experiment`. -/
noncomputable def sisEll2Advantage (β : ℝ)
    (S : Matrix (Fin n) (Fin m) (ZMod q) → ProbComp (Fin m → ℤ)) : ℝ≥0 :=
  Game.succProbability (ProbComp.eval (sisEll2Experiment q β S))

private theorem sisAdvantage_le_of_imp {P Q : Matrix (Fin n) (Fin m) (ZMod q) → (Fin m → ℤ) → Prop}
    (dP : ∀ A z, Decidable (P A z)) (dQ : ∀ A z, Decidable (Q A z))
    (S : Matrix (Fin n) (Fin m) (ZMod q) → ProbComp (Fin m → ℤ))
    (himp : ∀ A z, P A z → Q A z) :
    Game.succProbability (ProbComp.eval do
        let A ← ProbComp.uniform (Matrix (Fin n) (Fin m) (ZMod q))
        let z ← S A
        return @decide (P A z) (dP A z)) ≤
      Game.succProbability (ProbComp.eval do
        let A ← ProbComp.uniform (Matrix (Fin n) (Fin m) (ZMod q))
        let z ← S A
        return @decide (Q A z) (dQ A z)) := by
  refine ENNReal.toNNReal_mono (PMF.apply_ne_top _ _) ?_
  simp only [ProbComp.eval_bind, ProbComp.eval_pure]
  refine PMF.bind_apply_mono_on_support _ _ fun A _ =>
    PMF.bind_apply_mono_on_support _ _ fun z _ => ?_
  by_cases h : P A z
  · simp [h, himp A z h]
  · simp [h]

/-- Increasing the Euclidean norm bound cannot decrease a solver's `ℓ₂`-SIS advantage. -/
theorem sisEll2Advantage_mono {β β' : ℝ} (hβ : β ≤ β')
    (S : Matrix (Fin n) (Fin m) (ZMod q) → ProbComp (Fin m → ℤ)) :
    sisEll2Advantage q β S ≤ sisEll2Advantage q β' S :=
  sisAdvantage_le_of_imp q _ _ S fun _ _ h => h.mono hβ

/-- At a natural-number bound `β`, every solver's `ℓ₂`-SIS advantage is at most its `ℓ_∞`-SIS
advantage, because `‖z‖_∞ ≤ ‖z‖₂`. -/
theorem sisEll2Advantage_le_sisAdvantage (β : ℕ)
    (S : Matrix (Fin n) (Fin m) (ZMod q) → ProbComp (Fin m → ℤ)) :
    sisEll2Advantage q (β : ℝ) S ≤ sisAdvantage q β S :=
  sisAdvantage_le_of_imp q _ _ S fun _ _ h => by simpa [Nat.floor_natCast] using h.isSolution

/-- Whenever `√m · β ≤ β₂`, every solver's `ℓ_∞`-SIS advantage at bound `β` is at most its
`ℓ₂`-SIS advantage at bound `β₂`, because `‖z‖₂ ≤ √m · ‖z‖_∞`. -/
theorem sisAdvantage_le_sisEll2Advantage {β : ℕ} {β₂ : ℝ} (hβ : Real.sqrt m * β ≤ β₂)
    (S : Matrix (Fin n) (Fin m) (ZMod q) → ProbComp (Fin m → ℤ)) :
    sisAdvantage q β S ≤ sisEll2Advantage q β₂ S :=
  sisAdvantage_le_of_imp q _ _ S fun _ _ h =>
    h.isEll2Solution.mono (by simpa [Fintype.card_fin] using hβ)

end Experiment

/-! ### Asymptotic `ℓ₂`-SIS hardness and bridges to `SIS` -/

/-- The `ℓ₂`-SIS hardness hypothesis for a parameter family `P`: every PPT solver has negligible
advantage in `sisEll2Experiment` at the parameters `P` assigns to each security parameter. This is
a hypothesis against classical adversaries, not a theorem of hardness.

*Source.* This is the `SIS_{q, m, β}` problem of [MicciancioRegev2007], Definitions 5.1 and 5.3
(§5.1, p. 17): given a uniform `A ∈ ℤ_q^{n×m}`, find a nonzero `z ∈ ℤ^m` with `A z ≡ 0 (mod q)`
and Euclidean norm `‖z‖₂ ≤ β`. It also matches [Lyubashevsky2012], Definition 3.1 (p. 6, ePrint
2011/537). This definition differs from [MicciancioRegev2007], Definitions 5.1 and 5.3, in three
ways.
* The bound `P.β κ` is a natural number rather than an arbitrary positive real function `β(n)`,
  because `SISEll2` reuses `SISParams` directly. Real Euclidean bounds are supported at the
  fixed-instance level by `SIS.IsEll2Solution`, `sisEll2Experiment`, and `sisEll2Advantage`.
* The parameter family `P` is an arbitrary schedule indexed by a separate security parameter `κ`,
  whereas [MicciancioRegev2007], Definition 5.3 (§5.1, p. 17), takes the number of equations `n`
  as the security parameter and allows arbitrary `n`-indexed functions `q(n)`, `m(n)`, and `β(n)`
  (noting on p. 17 that polynomial instance size requires `m(n) = n^{O(1)}` while `q(n)` and `β(n)`
  may be exponentially large, that taking `q(n)` and `β(n)` polynomially bounded as well is the
  typical choice of interest, and that the Lemma 5.2 threshold `β ≥ √m · q^{n/m}` is a sufficient
  guarantee that solutions exist rather than part of Definition 5.3).
* Solvers are uniform classical strict PPT programs (`SISParams.Solver.IsPPT`) whose success
  probability must be negligible in `κ`, matching `SIS`. -/
def SISEll2 (P : SISParams) : Prop :=
  ∀ S : P.Solver, S.IsPPT → Negligible fun κ => sisEll2Advantage (P.q κ) (P.β κ : ℝ) (S κ)

/-- Hardness of `ℓ_∞`-SIS implies hardness of `ℓ₂`-SIS for the same parameter family `P`, since
every `ℓ₂`-SIS solution with bound `β` is also an `ℓ_∞`-SIS solution with bound `β`. -/
theorem SIS.toSISEll2 {P : SISParams} (h : SIS P) : SISEll2 P :=
  fun S hS => negligible_of_le (h S hS) fun κ =>
    sisEll2Advantage_le_sisAdvantage (P.q κ) (P.β κ) (S κ)

/-- Hardness of `ℓ₂`-SIS for `P` implies hardness of `ℓ_∞`-SIS for `{ P with β := β₁ }` whenever
`√(P.m κ) · β₁ κ ≤ P.β κ` for every `κ`. Because `{ P with β := β₁ }` shares `P`'s dimensions,
modulus, input layout, and solver type, callers can chain this directly with reductions from `SIS`
such as `SIS.collisionResistantForOn_ajtaiWordHash`. -/
theorem SISEll2.toSIS {P : SISParams} {β₁ : ℕ → ℕ} (h : SISEll2 P)
    (hβ : ∀ κ, Real.sqrt (P.m κ) * β₁ κ ≤ P.β κ) :
    SIS { P with β := β₁ } :=
  fun S ⟨k, State, hfin, machine, c, d, hrun⟩ =>
    negligible_of_le (h S ⟨k, State, hfin, machine, c, d, fun x => hrun ⟨x.secParam, x.matrix⟩⟩)
      fun κ => sisAdvantage_le_sisEll2Advantage (P.q κ) (hβ κ) (S κ)

end Cslib.Crypto
