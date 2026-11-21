/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module

public import CslibFrontier.Crypto.Computational.SIS.Ell2
import CslibFrontier.Crypto.Computational.Lattice.GIVP
import CslibFrontier.Crypto.Computational.Lattice.ShortestVector
import CslibFrontier.Crypto.Computational.SIS.Ajtai
import CslibFrontier.Tactic.PPT

/-!
# Tests for `GIVP`, `GDD`, `IncGDD`, and `ℓ₂`-SIS

Ordinary `module` client verifying the public interfaces of
`CslibFrontier/Crypto/Computational/Lattice/GIVP.lean`,
`CslibFrontier/Crypto/Computational/Lattice/ShortestVector.lean`, and
`CslibFrontier/Crypto/Computational/SIS/Ell2.lean`:

1. Concrete `GIVP`, `SIVP`, `GDD`, and `IncGDD` witnesses on `ℤ² ⊂ EuclideanSpace ℝ (Fin 2)`
   (including `SIVP.IsSolution` as the definitional `φ = λ_n` specialization of `GIVP.IsSolution`,
   parameter transfer, off-lattice `GDD`, a non-isotropic `IncGDD` basis with `‖S‖ = 3`, and a
   rank-`0` boundary check).
2. Concrete `ℓ₂`-SIS checks: MR07 Lemma 5.2 (`SIS.exists_isEll2Solution`), the integer
   sum-of-squares characterization (`SIS.isEll2Solution_nat_iff`), real-bound monotonicity
   (`sisEll2Advantage_mono`), negative-bound rejection, the trivial `β = q` regime, `ℓ_∞`/`ℓ₂`
   sharpness separation on `![1, 1]`, and chaining `SISEll2.toSIS` into
   `SIS.collisionResistantForOn_ajtaiWordHash`. Nonvacuity of `SISEll2` is proved in
   `CslibFrontierTests/Crypto/ModuleSIS.lean` (`not_sisEll2_zeroRowSIS`) by reusing `zeroRowSIS`
   and `not_sis_zeroRowSIS` through `SISEll2.toSIS`.
-/

namespace CslibFrontierTests.Crypto.LatticeGIVPSISEll2

open ZLattice Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM
open scoped NNReal _root_.Matrix

/-! ### 1. `GIVP`, `GDD`, and `IncGDD` witnesses -/

/-- The standard Euclidean lattice `ℤ² ⊂ EuclideanSpace ℝ (Fin 2)`. -/
private noncomputable abbrev stdEuc : Submodule ℤ (EuclideanSpace ℝ (Fin 2)) :=
  Submodule.span ℤ (Set.range (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis)

private theorem finrank_stdEuc : Module.finrank ℤ stdEuc = 2 := by
  rw [ZLattice.rank ℝ stdEuc, finrank_euclideanSpace_fin]

private theorem norm_basisFun (i : Fin 2) :
    ‖EuclideanSpace.basisFun (Fin 2) ℝ i‖ = 1 :=
  (EuclideanSpace.basisFun (Fin 2) ℝ).orthonormal.1 i

private theorem stdEuc_ne_bot : stdEuc ≠ ⊥ :=
  (Submodule.ne_bot_iff _).2
    ⟨(EuclideanSpace.basisFun (Fin 2) ℝ).toBasis 0, Submodule.subset_span ⟨0, rfl⟩,
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.ne_zero 0⟩

private theorem one_le_norm_stdEuc {v : EuclideanSpace ℝ (Fin 2)} (hv : v ∈ stdEuc)
    (hv0 : v ≠ 0) : 1 ≤ ‖v‖ := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv0 (by ext i; exact h i)
  obtain ⟨k, hk⟩ := ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.mem_span_iff_repr_mem ℤ v).1 hv i
  have hvi : (k : ℝ) = v i := by
    simpa [EuclideanSpace.basisFun_repr] using hk
  have hk0 : k ≠ 0 := by
    intro h
    subst h
    exact hi (by simpa using hvi.symm)
  calc (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk0
    _ = ‖v i‖ := by rw [hvi, Real.norm_eq_abs]
    _ ≤ ‖v‖ := PiLp.norm_apply_le v i

private theorem minimum_stdEuc : minimum stdEuc = 1 :=
  le_antisymm
    (by
      have h0 : ‖(EuclideanSpace.basisFun (Fin 2) ℝ).toBasis 0‖ = 1 := by
        simp
      exact h0 ▸ minimum_le_norm (Submodule.subset_span ⟨0, rfl⟩)
        ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.ne_zero 0))
    ((le_minimum_iff stdEuc_ne_bot).2 fun _ => one_le_norm_stdEuc)

/-- The standard basis solves `GIVP^{λ₂}_1` on `ℤ²`, which is definitionally `SIVP_1`
(`SIVP.IsSolution`), and `SIVP.IsSolution.mono` / `SIVP.IsSolution.one_le` apply directly. -/
example :
    GIVP.IsSolution (fun L => successiveMinimum L (Module.finrank ℤ L)) 1 stdEuc
      (fun i => EuclideanSpace.basisFun (Fin 2) ℝ (Fin.cast finrank_stdEuc i)) ∧
    SIVP.IsSolution 2 stdEuc
      (fun i => EuclideanSpace.basisFun (Fin 2) ℝ (Fin.cast finrank_stdEuc i)) := by
  have hmin : 1 ≤ successiveMinimum stdEuc (Module.finrank ℤ stdEuc) := by
    rw [finrank_stdEuc]
    calc (1 : ℝ) = minimum stdEuc := minimum_stdEuc.symm
      _ ≤ _ := minimum_le_successiveMinimum stdEuc stdEuc_ne_bot (by norm_num) (by simp)
  have hSIVP :
      SIVP.IsSolution 1 stdEuc
        (fun i => EuclideanSpace.basisFun (Fin 2) ℝ (Fin.cast finrank_stdEuc i)) := by
    refine ⟨(EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.linearIndependent.comp _
      (Fin.cast_injective _), fun i => Submodule.subset_span ⟨_, rfl⟩, fun i => ?_⟩
    rw [one_mul, norm_basisFun]
    exact hmin
  have _ : (1 : ℝ) ≤ 1 := hSIVP.one_le (by simp)
  exact ⟨hSIVP, hSIVP.mono (by norm_num)⟩

/-- `GIVP.IsSolution.mono` and `GIVP.IsSolution.of_param_le` transfer bounds across parameters. -/
example :
    GIVP.IsSolution (fun _ => (1 / 2 : ℝ)) 4 stdEuc
      (fun i => EuclideanSpace.basisFun (Fin 2) ℝ (Fin.cast finrank_stdEuc i)) := by
  have hbase : GIVP.IsSolution (fun _ => (1 : ℝ)) 1 stdEuc
      (fun i => EuclideanSpace.basisFun (Fin 2) ℝ (Fin.cast finrank_stdEuc i)) :=
    ⟨(EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.linearIndependent.comp _ (Fin.cast_injective _),
      fun i => Submodule.subset_span ⟨_, rfl⟩, fun i => by rw [one_mul, norm_basisFun]⟩
  have hmono := hbase.mono (by norm_num) (by norm_num : (1 : ℝ) ≤ 2)
  simpa [show (2 : ℝ) * 2 = 4 by norm_num] using
    hmono.of_param_le (ψ := fun _ => (1 / 2 : ℝ)) (c := 2) (by norm_num) (by norm_num)

/-- Off-lattice `GDD` witness on `ℤ²`: `0 ∈ ℤ²` lies within distance `5/12 ≤ 1 · (1/2)` of
`(1/3, 1/4)`, and monotonicity widens the factor from `1` to `2`. -/
example :
    let t : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![1 / 3, 1 / 4]
    GDD.IsSolution (fun _ => (1 / 2 : ℝ)) 1 stdEuc t 0 ∧
    GDD.IsSolution (fun _ => (1 / 2 : ℝ)) 2 stdEuc t 0 := by
  intro t
  have hnorm : ‖(0 : EuclideanSpace ℝ (Fin 2)) - t‖ ≤ 1 * (1 / 2 : ℝ) := by
    rw [zero_sub, norm_neg, ← sq_le_sq₀ (norm_nonneg _) (by norm_num), EuclideanSpace.norm_sq_eq]
    simp only [t, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Real.norm_eq_abs, sq_abs]
    norm_num
  have h1 : GDD.IsSolution (fun _ => (1 / 2 : ℝ)) 1 stdEuc t 0 := ⟨stdEuc.zero_mem, hnorm⟩
  exact ⟨h1, h1.mono (by norm_num) (by norm_num)⟩

/-- Non-isotropic `IncGDD` witness on `ℤ²` with `S = ![(2, 0), (0, 3)]`: its Pi supremum norm is
`‖S‖ = 3`, `(stdEuc, S, 2)` is valid for `γ = 1, φ = 1`, and `0 ∈ ℤ²` solves `IncGDD` at
`g = 3`, `t = (1/2, 5/2)` with `r < ‖0 - t‖ ≤ ‖S‖ / 3 + r = 3`. -/
example :
    let S2 : Fin 2 → EuclideanSpace ℝ (Fin 2) :=
      ![(2 : ℝ) • EuclideanSpace.basisFun (Fin 2) ℝ 0,
        (3 : ℝ) • EuclideanSpace.basisFun (Fin 2) ℝ 1]
    let S : Fin (Module.finrank ℤ stdEuc) → EuclideanSpace ℝ (Fin 2) :=
      S2 ∘ Fin.cast finrank_stdEuc
    let t : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![1 / 2, 5 / 2]
    ‖S‖ = 3 ∧
      IncGDD.IsValidInstance (fun _ => (1 : ℝ)) 1 stdEuc S 2 ∧
      IncGDD.IsSolution 3 stdEuc S t 2 0 := by
  intro S2 S t
  have hS2_0 : ‖S2 0‖ = 2 := by simp [S2, norm_smul]
  have hS2_1 : ‖S2 1‖ = 3 := by simp [S2, norm_smul]
  have hS2_le : ∀ j : Fin 2, ‖S2 j‖ ≤ 3 := fun j => by
    fin_cases j
    · exact hS2_0.le.trans (by norm_num)
    · exact hS2_1.le
  have hSnorm : ‖S‖ = 3 := by
    refine le_antisymm ?_ ?_
    · rw [pi_norm_le_iff_of_nonneg (by norm_num)]
      intro i
      exact hS2_le (Fin.cast finrank_stdEuc i)
    · calc (3 : ℝ) = ‖S (Fin.cast finrank_stdEuc.symm 1)‖ := by
              change (3 : ℝ) = ‖S2 (Fin.cast finrank_stdEuc (Fin.cast finrank_stdEuc.symm 1))‖
              simpa using hS2_1.symm
        _ ≤ ‖S‖ := norm_le_pi_norm S _
  have hS2lin : LinearIndependent ℝ S2 := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have h0 : (∑ i : Fin 2, c i • S2 i) 0 = 0 := by rw [hc]; rfl
    have h1 : (∑ i : Fin 2, c i • S2 i) 1 = 0 := by rw [hc]; rfl
    simp [Fin.sum_univ_two, S2] at h0 h1
    intro i
    fin_cases i
    · simpa using h0
    · simpa using h1
  have hS2mem : ∀ j : Fin 2, S2 j ∈ stdEuc := fun j => by
    fin_cases j
    · simpa [S2, ← Int.cast_smul_eq_zsmul ℝ (2 : ℤ)] using
        stdEuc.smul_mem (2 : ℤ) (Submodule.subset_span ⟨0, rfl⟩)
    · simpa [S2, ← Int.cast_smul_eq_zsmul ℝ (3 : ℤ)] using
        stdEuc.smul_mem (3 : ℤ) (Submodule.subset_span ⟨1, rfl⟩)
  have hSmem : ∀ i, S i ∈ stdEuc := fun i => hS2mem (Fin.cast finrank_stdEuc i)
  have hdist : ‖(0 : EuclideanSpace ℝ (Fin 2)) - t‖ ≤ ‖S‖ / 3 + 2 := by
    rw [hSnorm, zero_sub, norm_neg, ← sq_le_sq₀ (norm_nonneg _) (by norm_num),
      EuclideanSpace.norm_sq_eq]
    simp only [t, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Real.norm_eq_abs, sq_abs]
    norm_num
  exact ⟨hSnorm, ⟨hS2lin.comp _ (Fin.cast_injective _), hSmem, by norm_num⟩,
    ⟨stdEuc.zero_mem, hdist⟩⟩

/-- Rank-`0` boundary check: on `⊥ : Submodule ℤ (EuclideanSpace ℝ (Fin 0))`, the empty family `S₀`
has `‖S₀‖ = 0` and satisfies `GIVP`, `IncGDD.IsValidInstance`, and `IncGDD.IsSolution`. -/
example :
    let L₀ : Submodule ℤ (EuclideanSpace ℝ (Fin 0)) := ⊥
    let S₀ : Fin (Module.finrank ℤ L₀) → EuclideanSpace ℝ (Fin 0) := 0
    ‖S₀‖ = 0 ∧
      GIVP.IsSolution (fun _ => 0) 1 L₀ S₀ ∧
      IncGDD.IsValidInstance (fun _ => 0) 1 L₀ S₀ 1 ∧
      IncGDD.IsSolution 2 L₀ S₀ 0 1 0 := by
  intro L₀ S₀
  have hrank : Module.finrank ℤ L₀ = 0 := by simp [L₀]
  have hempty : IsEmpty (Fin (Module.finrank ℤ L₀)) := by
    rw [hrank]
    infer_instance
  refine ⟨by simp [S₀],
    ⟨linearIndependent_empty_type, fun i => hempty.elim i, fun i => hempty.elim i⟩,
    ⟨linearIndependent_empty_type, fun i => hempty.elim i, by norm_num⟩,
    ⟨L₀.zero_mem, by simp [S₀]⟩⟩

/-! ### 2. `ℓ₂`-SIS, MR07 Lemma 5.2, sharpness, nonvacuity, and Ajtai CRHF client -/

private abbrev toyMat : Matrix (Fin 1) (Fin 2) (ZMod 3) := !![1, 2]

/-- Concrete instantiation of MR07 Lemma 5.2 (`SIS.exists_isEll2Solution`): for `n = 1, m = 2,
q = 3`, `√2 · 3^{1/2} = √6`, so `toyMat` admits an `ℓ₂`-SIS solution of norm at most `√6`. -/
public theorem exists_isEll2Solution_toyMat :
    ∃ z : Fin 2 → ℤ, SIS.IsEll2Solution !![(1 : ZMod 3), 2] (Real.sqrt 6) z := by
  refine SIS.exists_isEll2Solution (by norm_num : 0 < 2) toyMat ?_
  have h3 : (3 : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt 3 := by
    rw [Real.sqrt_eq_rpow]
  rw [Nat.cast_ofNat, Nat.cast_one, Nat.cast_ofNat, h3, ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- `SIS.isEll2Solution_nat_iff` gives a decidable integer check for natural-number bounds:
`![1, 1]` has `1² + 1² = 2 ≤ 2²`, so it solves `ℓ₂`-SIS at bound `2`. -/
example : SIS.IsEll2Solution toyMat (2 : ℕ) ![1, 1] :=
  (SIS.isEll2Solution_nat_iff toyMat 2 ![1, 1]).2 (by decide)

/-- Sharpness separation between `ℓ_∞` and `ℓ₂`: `![1, 1]` is an `ℓ_∞`-SIS solution at bound `1`
and an `ℓ₂`-SIS solution at non-integer real bound `√2`, but not an `ℓ₂`-SIS solution at bound
`1`. -/
example :
    SIS.IsSolution toyMat 1 ![1, 1] ∧
    SIS.IsEll2Solution toyMat (Real.sqrt 2) ![1, 1] ∧
    ¬SIS.IsEll2Solution toyMat 1 ![1, 1] := by
  have hinf : SIS.IsSolution toyMat 1 ![1, 1] := by decide
  have hell2 : SIS.IsEll2Solution toyMat (Real.sqrt 2) ![1, 1] := by
    simpa using hinf.isEll2Solution
  have hnot : ¬SIS.IsEll2Solution toyMat 1 ![1, 1] := by
    rw [show (1 : ℝ) = ((1 : ℕ) : ℝ) by norm_num, SIS.isEll2Solution_nat_iff]
    decide
  exact ⟨hinf, hell2, hnot⟩

/-- Non-integer real-bound monotonicity of `sisEll2Advantage` and comparison with `sisAdvantage`. -/
example (S : Matrix (Fin 1) (Fin 2) (ZMod 3) → ProbComp (Fin 2 → ℤ)) :
    sisEll2Advantage 3 1 S ≤ sisEll2Advantage 3 (Real.sqrt 2) S ∧
    sisAdvantage 3 1 S ≤ sisEll2Advantage 3 (Real.sqrt 2) S :=
  ⟨sisEll2Advantage_mono 3 (by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num) S,
    sisAdvantage_le_sisEll2Advantage 3 (by simp) S⟩

/-- Negative Euclidean bounds admit no `ℓ₂`-SIS solutions. -/
example (z : Fin 2 → ℤ) : ¬SIS.IsEll2Solution toyMat (-1) z := fun hz =>
  not_lt_of_ge hz.2.1 (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (norm_nonneg _))

/-- Trivial regime `q ≤ β`: `![3, 0]` solves `ℓ₂`-SIS at bound `q = 3` for every `1 × 2` matrix
over `ZMod 3`. -/
example (A : Matrix (Fin 1) (Fin 2) (ZMod 3)) : SIS.IsEll2Solution A (3 : ℕ) ![3, 0] := by
  rw [SIS.isEll2Solution_nat_iff]
  refine ⟨by decide, by decide, ?_⟩
  have hzero : (Int.cast ∘ (![3, 0] : Fin 2 → ℤ) : Fin 2 → ZMod 3) = 0 := by decide
  rw [Cslib.Crypto.InKernelLattice, hzero, Matrix.mulVec_zero]

/-- Polynomial `SISParams` family with `m = (κ + 1)(κ + 3)` and Euclidean bound `β = κ + 3 ≥ √m`,
so `SISEll2` directly implies `ℓ_∞`-`SIS` at bound `1` and Ajtai collision resistance. -/
private def ajtaiPolySISEll2 : SISParams where
  n κ := κ + 1
  m κ := (κ + 1) * (κ + 3)
  q κ := (κ + 2) ^ 2
  β κ := κ + 3
  hq _ := ⟨by positivity⟩

/-- Chaining `SISEll2.toSIS` directly into `SIS.collisionResistantForOn_ajtaiWordHash` with zero
parameter-family conversions. -/
example (h : SISEll2 ajtaiPolySISEll2) :
    let P₁ : SISParams := { ajtaiPolySISEll2 with β := fun _ => 1 }
    CollisionResistantForOn P₁.encInput (ajtaiSetup P₁) (ajtaiWordHash P₁)
      (fun _ d s => s.length == P₁.m d.secParam) := by
  have hβ : ∀ κ, Real.sqrt (ajtaiPolySISEll2.m κ) * (1 : ℕ) ≤ ajtaiPolySISEll2.β κ := fun κ => by
    simp only [ajtaiPolySISEll2, Nat.cast_one, mul_one]
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    push_cast
    nlinarith
  exact (h.toSIS (β₁ := fun _ => 1) hβ).collisionResistantForOn_ajtaiWordHash
    (show ComputableInPolyTime (fun κ => (κ + 1) * (κ + 3)) encUnary encUnary by fun_prop)
    fun _ => le_rfl

/-- `SIS.toSISEll2` transfers `ℓ_∞`-SIS hardness to `ℓ₂`-SIS on the same parameter family. -/
example (h : SIS ajtaiPolySISEll2) : SISEll2 ajtaiPolySISEll2 := h.toSISEll2

end CslibFrontierTests.Crypto.LatticeGIVPSISEll2
