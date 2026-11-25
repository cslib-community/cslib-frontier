/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.RotationStrategy
public import CslibFrontier.Foundations.Quantum.Clifford
public import CslibFrontier.Foundations.Data.BitString.Sign
import CslibFrontier.Foundations.Analysis.InnerProductSpace.PiL2
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.MetricSpace.ProperSpace.Real

/-!
# General XOR games, Tsirelson's vector characterization, and the Odd-Cycle game

In a binary nonlocal game (`TwoProverGame X Y Bool Bool`), Alice and Bob each answer one bit; it is
an **XOR game** (`Cslib.PCP.TwoProverGame.IsXORGame`, `Cslib.PCP.TwoProverGame.xorGame`) when the
referee's verdict depends only on `a ^^ b`
([Cleve, Høyer, Toner, Watrous, §5][CleveHoyerTonerWatrous2004], `arXiv:quant-ph/0404076v2`).

This module formalizes:

1. **Tsirelson's vector correspondence** (`Cslib.PCP.tsirelson_vectors_of_observables`,
   `Cslib.PCP.tsirelson_observables_of_vectors`, `Cslib.PCP.tsirelson_iff`,
   [Cirel'son][Cirelson1980];
   [Cleve, Høyer, Toner, Watrous, §5.3, Theorem 4][CleveHoyerTonerWatrous2004]):
   a table `c : S → T → ℝ` arises as `⟨ψ| A_s ⊗ B_t |ψ⟩` for a unit vector `ψ ∈ ℂⁿ ⊗ ℂⁿ` and
   `±1` observables `A_s, B_t` if and only if it arises as real unit-vector inner products
   `⟪u_s, v_t⟫` in `ℝᵐ`, with the quantitative bounds `m = 2n²` and `n = 2^⌈m / 2⌉`
   (`⌈m / 2⌉ = (m + 1) / 2`), plus the general POVM bridge
   `Cslib.PCP.QuantumStrategy.exists_unit_vectors_correlation`.
2. **Exact vector characterization and entanglement bound for XOR games**
   (`Cslib.PCP.TwoProverGame.value_sub_trivialWinProb`,
   `Cslib.PCP.TwoProverGame.exists_max_unit_vectors_xorGame`,
   `Cslib.PCP.TwoProverGame.quantumValue_sub_trivialWinProb`,
   `Cslib.PCP.TwoProverGame.exists_maxEntangled_optimal_strategy`,
   [Cleve, Høyer, Toner, Watrous, §5.3–5.4, Proposition 5 &
   Theorem 10][CleveHoyerTonerWatrous2004]):
   `ω_q(G) - τ(G)` equals half the maximum of `∑_{x,y} π(x,y) (V(0|x,y) - V(1|x,y)) ⟪u_x, v_y⟫`
   over real unit vectors in `ℝ^m` for `m = min(|X|, |Y|)`, and every XOR game on nonempty finite
   question sets attains `quantumValue` using `⌈min(|X|, |Y|) / 2⌉` shared EPR pairs.
3. **The Odd-Cycle XOR game** (`Cslib.PCP.TwoProverGame.oddCycleGame`,
   `Cslib.PCP.TwoProverGame.value_oddCycleGame`,
   `Cslib.PCP.TwoProverGame.quantumWinProb_oddCycleGame_oddCycleStrategy`,
   `Cslib.PCP.TwoProverGame.value_oddCycleGame_lt_quantumValue`,
   [Cleve, Høyer, Toner, Watrous, §3.2][CleveHoyerTonerWatrous2004]): on an odd cycle of length
   `n ≥ 3`, the classical value is `1 - 1 / (2n)`, whereas the Braunstein–Caves EPR rotation
   strategy wins with probability `cos²(π / (4n)) > 1 - 1 / (2n)`.

## References

* [B. S. Cirel'son, *Quantum generalizations of Bell's inequality*][Cirelson1980]
* [R. Cleve, P. Høyer, B. Toner, J. Watrous, *Consequences and limits of nonlocal
  strategies*][CleveHoyerTonerWatrous2004]
-/

@[expose] public section

namespace Cslib.PCP

open Matrix Quantum Finset Real
open Cslib.BitString (signVal)
open Cslib.Probability.PMF (uniformOfFintype uniformOfFintype_apply)
open scoped Kronecker ComplexOrder

private theorem continuous_finset_sum_real {α β : Type*} [TopologicalSpace α] (s : Finset β)
    {g : β → α → ℝ} (hg : ∀ b ∈ s, Continuous (g b)) :
    Continuous (fun a => ∑ b ∈ s, g b a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using continuous_const
  | @insert b s hb ih =>
    have hgb : Continuous (g b) := hg b (Finset.mem_insert_self b s)
    have hgs : Continuous (fun a => ∑ c ∈ s, g c a) :=
      ih fun c hc => hg c (Finset.mem_insert_of_mem hc)
    have hadd : Continuous (fun a => g b a + ∑ c ∈ s, g c a) := hgb.add hgs
    simpa only [Finset.sum_insert hb] using hadd

/-! ### Realification of complex `L²` vectors and contraction dilation -/

/-- Split a complex Euclidean vector `w ∈ ℂ^α` into real and imaginary coordinates in
`ℝ^(α × Bool)`. -/
private noncomputable def complexToRealLp {α : Type*} (w : EuclideanSpace ℂ α) :
    EuclideanSpace ℝ (α × Bool) :=
  WithLp.toLp 2 fun ib => bif ib.2 then (w.ofLp ib.1).im else (w.ofLp ib.1).re

private theorem inner_complexToRealLp {α : Type*} [Fintype α]
    (w₁ w₂ : EuclideanSpace ℂ α) :
    inner ℝ (complexToRealLp w₁) (complexToRealLp w₂) = (inner ℂ w₁ w₂).re := by
  rw [PiLp.inner_apply, PiLp.inner_apply, Complex.re_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_bool]
  simp only [complexToRealLp, WithLp.ofLp_toLp, Bool.cond_true, Bool.cond_false,
    RCLike.inner_apply, conj_trivial, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

private theorem norm_complexToRealLp {α : Type*} [Fintype α] (w : EuclideanSpace ℂ α) :
    ‖complexToRealLp w‖ = ‖w‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq, inner_complexToRealLp]
  simp [sq]

private theorem reindex_euclideanSpace_norm {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (u : EuclideanSpace ℝ α) :
    ‖(WithLp.toLp 2 (u.ofLp ∘ e.symm) : EuclideanSpace ℝ β)‖ = ‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  exact Equiv.sum_comp e.symm fun a => ‖u.ofLp a‖ ^ 2

private theorem reindex_euclideanSpace_inner {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (u v : EuclideanSpace ℝ α) :
    inner ℝ (WithLp.toLp 2 (u.ofLp ∘ e.symm) : EuclideanSpace ℝ β)
        (WithLp.toLp 2 (v.ofLp ∘ e.symm) : EuclideanSpace ℝ β) =
      inner ℝ u v := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  exact Equiv.sum_comp e.symm fun a => inner ℝ (u.ofLp a) (v.ofLp a)

/-! ### Tsirelson's vector correspondence (CHTW §5.3, Theorem 4) -/

private theorem hermitian_quadForm_eq_ofReal_re {α : Type*} [Fintype α]
    {H : Matrix α α ℂ} (hH : H.IsHermitian) (x : α → ℂ) :
    star x ⬝ᵥ (H *ᵥ x) = ((star x ⬝ᵥ (H *ᵥ x)).re : ℂ) := by
  have hself : star (star x ⬝ᵥ (H *ᵥ x)) = star x ⬝ᵥ (H *ᵥ x) := by
    conv_lhs =>
      rw [star_dotProduct, star_star, star_mulVec, hH.eq, ← dotProduct_mulVec]
  exact Complex.ext (Complex.ofReal_re _).symm (by
    have him := congrArg Complex.im hself
    simp only [Complex.star_def, Complex.conj_im] at him
    rw [Complex.ofReal_im]
    linarith)

/-- **Tsirelson's correspondence, `(1) ⇒ (2)`** ([Cirel'son][Cirelson1980];
[Cleve, Høyer, Toner, Watrous, §5.3, Theorem 4][CleveHoyerTonerWatrous2004]): `±1` observables
`A_s, B_t` on `ℂ^ι` and a unit state `ψ ∈ ℂ^(ι × ι)` yield real unit vectors in
`ℝ^(2 |ι|²)` with `⟨ψ| A_s ⊗ B_t |ψ⟩ = ⟪u_s, v_t⟫`. -/
theorem tsirelson_vectors_of_observables {S T ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ (ι × ι)) (hψ : ‖ψ‖ = 1)
    (A : S → Matrix ι ι ℂ) (B : T → Matrix ι ι ℂ)
    (hA_herm : ∀ s, (A s).IsHermitian) (hA_sq : ∀ s, A s * A s = 1)
    (hB_herm : ∀ t, (B t).IsHermitian) (hB_sq : ∀ t, B t * B t = 1) :
    0 < 2 * Fintype.card ι ^ 2 ∧
      ∃ (u : S → EuclideanSpace ℝ (Fin (2 * Fintype.card ι ^ 2)))
        (v : T → EuclideanSpace ℝ (Fin (2 * Fintype.card ι ^ 2))),
        (∀ s, ‖u s‖ = 1) ∧ (∀ t, ‖v t‖ = 1) ∧
        ∀ s t, star ψ.ofLp ⬝ᵥ (((A s) ⊗ₖ (B t)) *ᵥ ψ.ofLp) = (inner ℝ (u s) (v t) : ℂ) := by
  have hcard_pos : 0 < Fintype.card ι := by
    by_contra h0
    have hempty : IsEmpty ι := Fintype.card_eq_zero_iff.mp (Nat.eq_zero_of_not_pos h0)
    have hψ0 : ‖ψ‖ = 0 := by
      rw [EuclideanSpace.norm_eq]
      simp
    linarith
  have hm_pos : 0 < 2 * Fintype.card ι ^ 2 := by positivity
  let γ (s : S) : EuclideanSpace ℂ (ι × ι) :=
    WithLp.toLp 2 (((A s) ⊗ₖ (1 : Matrix ι ι ℂ)) *ᵥ ψ.ofLp)
  let δ (t : T) : EuclideanSpace ℂ (ι × ι) :=
    WithLp.toLp 2 (((1 : Matrix ι ι ℂ) ⊗ₖ (B t)) *ᵥ ψ.ofLp)
  have hγ_norm (s : S) : ‖γ s‖ = 1 := by
    have hiso : ((A s) ⊗ₖ (1 : Matrix ι ι ℂ))ᴴ * ((A s) ⊗ₖ (1 : Matrix ι ι ℂ)) = 1 := by
      rw [conjTranspose_kronecker, (hA_herm s).eq, conjTranspose_one, ← mul_kronecker_mul,
        hA_sq s, Matrix.mul_one, one_kronecker_one]
    exact (Matrix.norm_toLp_mulVec_of_conjTranspose_mul_self hiso ψ).trans hψ
  have hδ_norm (t : T) : ‖δ t‖ = 1 := by
    have hiso : ((1 : Matrix ι ι ℂ) ⊗ₖ (B t))ᴴ * ((1 : Matrix ι ι ℂ) ⊗ₖ (B t)) = 1 := by
      rw [conjTranspose_kronecker, conjTranspose_one, (hB_herm t).eq, ← mul_kronecker_mul,
        Matrix.mul_one, hB_sq t, one_kronecker_one]
    exact (Matrix.norm_toLp_mulVec_of_conjTranspose_mul_self hiso ψ).trans hψ
  have heq_card : Fintype.card ((ι × ι) × Bool) = 2 * Fintype.card ι ^ 2 := by
    simp only [Fintype.card_prod, Fintype.card_bool]
    ring
  let e : ((ι × ι) × Bool) ≃ Fin (2 * Fintype.card ι ^ 2) := Fintype.equivFinOfCardEq heq_card
  refine ⟨hm_pos,
    fun s => WithLp.toLp 2 ((complexToRealLp (γ s)).ofLp ∘ e.symm),
    fun t => WithLp.toLp 2 ((complexToRealLp (δ t)).ofLp ∘ e.symm),
    fun s => (reindex_euclideanSpace_norm e _).trans ((norm_complexToRealLp _).trans (hγ_norm s)),
    fun t => (reindex_euclideanSpace_norm e _).trans ((norm_complexToRealLp _).trans (hδ_norm t)),
    fun s t => ?_⟩
  rw [reindex_euclideanSpace_inner, inner_complexToRealLp]
  have hinner : inner ℂ (γ s) (δ t) = star ψ.ofLp ⬝ᵥ (((A s) ⊗ₖ (B t)) *ᵥ ψ.ofLp) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    dsimp only [γ, δ]
    rw [WithLp.ofLp_toLp, WithLp.ofLp_toLp, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec,
      conjTranspose_kronecker, (hA_herm s).eq, conjTranspose_one, ← mul_kronecker_mul,
      Matrix.mul_one, Matrix.one_mul]
  have hAB_herm : ((A s) ⊗ₖ (B t)).IsHermitian := by
    rw [IsHermitian, conjTranspose_kronecker, (hA_herm s).eq, (hB_herm t).eq]
  rw [hinner]
  exact hermitian_quadForm_eq_ofReal_re hAB_herm ψ.ofLp

namespace QuantumStrategy

private theorem kronecker_one_mulVec_apply {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (M : Matrix ι ι ℂ) (v : ι × κ → ℂ) (i : ι) (k : κ) :
    ((M ⊗ₖ (1 : Matrix κ κ ℂ)) *ᵥ v) (i, k) = (M *ᵥ fun j => v (j, k)) i := by
  simp only [mulVec, dotProduct, Fintype.sum_prod_type, kroneckerMap_apply, Matrix.one_apply,
    mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

private theorem one_kronecker_mulVec_apply {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (N : Matrix κ κ ℂ) (v : ι × κ → ℂ) (i : ι) (k : κ) :
    (((1 : Matrix ι ι ℂ) ⊗ₖ N) *ᵥ v) (i, k) = (N *ᵥ fun l => v (i, l)) k := by
  simp only [mulVec, dotProduct, Fintype.sum_prod_type, kroneckerMap_apply, Matrix.one_apply,
    ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

private theorem norm_kronecker_one_mulVec_le {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {M : Matrix ι ι ℂ} (hM : (1 - Mᴴ * M).PosSemidef)
    (ψ : EuclideanSpace ℂ (ι × κ)) :
    ‖(WithLp.toLp 2 ((M ⊗ₖ (1 : Matrix κ κ ℂ)) *ᵥ ψ.ofLp) : EuclideanSpace ℂ (ι × κ))‖ ≤
      ‖ψ‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type_right,
    Fintype.sum_prod_type_right]
  refine Finset.sum_le_sum fun k _ => ?_
  let ψk : EuclideanSpace ℂ ι := WithLp.toLp 2 fun i => ψ.ofLp (i, k)
  have hslice : (∑ i : ι, ‖((WithLp.toLp 2
      ((M ⊗ₖ (1 : Matrix κ κ ℂ)) *ᵥ ψ.ofLp) : EuclideanSpace ℂ (ι × κ))).ofLp (i, k)‖ ^ 2) =
      ‖(WithLp.toLp 2 (M *ᵥ ψk.ofLp) : EuclideanSpace ℂ ι)‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp only [ψk]
    rw [WithLp.ofLp_toLp, kronecker_one_mulVec_apply]
  rw [hslice, ← EuclideanSpace.norm_sq_eq ψk]
  exact pow_le_pow_left₀ (norm_nonneg _) (Matrix.norm_toLp_mulVec_le_of_posSemidef hM ψk) 2

/-- Every quantum strategy with binary answers—even with non-projective POVMs and unequal local
dimensions—has its correlation table realized by real unit vectors. -/
theorem exists_unit_vectors_correlation {S T ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (strat : QuantumStrategy S T Bool Bool ι κ) :
    ∃ (M : ℕ) (_ : 0 < M) (u : S → EuclideanSpace ℝ (Fin M)) (v : T → EuclideanSpace ℝ (Fin M)),
      (∀ s, ‖u s‖ = 1) ∧ (∀ t, ‖v t‖ = 1) ∧
      ∀ s t, inner ℝ (u s) (v t) = strat.correlation s t := by
  let ψ := strat.state
  let A (s : S) := (strat.alice s).observable
  let B (t : T) := (strat.bob t).observable
  let γ (s : S) : EuclideanSpace ℂ (ι × κ) :=
    WithLp.toLp 2 ((A s ⊗ₖ (1 : Matrix κ κ ℂ)) *ᵥ ψ.ofLp)
  let δ (t : T) : EuclideanSpace ℂ (ι × κ) :=
    WithLp.toLp 2 (((1 : Matrix ι ι ℂ) ⊗ₖ B t) *ᵥ ψ.ofLp)
  have hγ_le (s : S) : ‖γ s‖ ≤ 1 := by
    have hpsd : (1 - (A s)ᴴ * A s).PosSemidef := by
      rw [(POVM.isHermitian_observable (strat.alice s)).eq]
      exact POVM.posSemidef_one_sub_observable_mul_self (strat.alice s)
    exact (norm_kronecker_one_mulVec_le hpsd ψ).trans_eq strat.norm_state
  have hδ_le (t : T) : ‖δ t‖ ≤ 1 := by
    have hpsd : (1 - (B t)ᴴ * B t).PosSemidef := by
      rw [(POVM.isHermitian_observable (strat.bob t)).eq]
      exact POVM.posSemidef_one_sub_observable_mul_self (strat.bob t)
    let ψ' : EuclideanSpace ℂ (κ × ι) := WithLp.toLp 2 (ψ.ofLp ∘ Equiv.prodComm κ ι)
    let δ' : EuclideanSpace ℂ (κ × ι) :=
      WithLp.toLp 2 ((B t ⊗ₖ (1 : Matrix ι ι ℂ)) *ᵥ ψ'.ofLp)
    have hδ_eq : ‖δ t‖ = ‖δ'‖ := by
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
        ← Equiv.sum_comp (Equiv.prodComm ι κ)]
      refine Finset.sum_congr rfl fun ⟨i, k⟩ _ => ?_
      dsimp only [δ, δ', ψ', Equiv.prodComm_apply, Prod.swap, Function.comp_apply]
      rw [WithLp.ofLp_toLp, WithLp.ofLp_toLp, one_kronecker_mulVec_apply,
        kronecker_one_mulVec_apply]
      rfl
    have hψ_eq : ‖ψ'‖ = ‖ψ‖ := by
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
      exact Equiv.sum_comp (Equiv.prodComm κ ι) fun p => ‖ψ.ofLp p‖ ^ 2
    exact (hδ_eq.trans_le (norm_kronecker_one_mulVec_le hpsd ψ')).trans_eq
      (hψ_eq.trans strat.norm_state)
  let α' (s : S) := complexToRealLp (γ s)
  let β' (t : T) := complexToRealLp (δ t)
  let Pad := ((ι × κ) × Bool) ⊕ Bool
  let uPad (s : S) : EuclideanSpace ℝ Pad :=
    WithLp.toLp 2 (Sum.elim (α' s).ofLp
      (fun b => bif b then 0 else Real.sqrt (1 - ‖α' s‖ ^ 2)))
  let vPad (t : T) : EuclideanSpace ℝ Pad :=
    WithLp.toLp 2 (Sum.elim (β' t).ofLp
      (fun b => bif b then Real.sqrt (1 - ‖β' t‖ ^ 2) else 0))
  have huPad (s : S) : ‖uPad s‖ = 1 := by
    have hle1 : ‖α' s‖ ^ 2 ≤ 1 := by
      rw [norm_complexToRealLp]
      nlinarith [hγ_le s, norm_nonneg (γ s)]
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type, Fintype.sum_bool]
    have hsum : (∑ x : (ι × κ) × Bool, ‖(uPad s).ofLp (Sum.inl x)‖ ^ 2) = ‖α' s‖ ^ 2 :=
      (EuclideanSpace.norm_sq_eq (α' s)).symm
    rw [hsum]
    simp only [uPad, Sum.elim_inr, Bool.cond_true, Bool.cond_false, norm_zero,
      Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by linarith : 0 ≤ 1 - ‖α' s‖ ^ 2)]
    ring
  have hvPad (t : T) : ‖vPad t‖ = 1 := by
    have hle1 : ‖β' t‖ ^ 2 ≤ 1 := by
      rw [norm_complexToRealLp]
      nlinarith [hδ_le t, norm_nonneg (δ t)]
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type, Fintype.sum_bool]
    have hsum : (∑ x : (ι × κ) × Bool, ‖(vPad t).ofLp (Sum.inl x)‖ ^ 2) = ‖β' t‖ ^ 2 :=
      (EuclideanSpace.norm_sq_eq (β' t)).symm
    rw [hsum]
    simp only [vPad, Sum.elim_inr, Bool.cond_true, Bool.cond_false, norm_zero,
      Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by linarith : 0 ≤ 1 - ‖β' t‖ ^ 2)]
    ring
  let M := Fintype.card Pad
  have hM : 0 < M := Fintype.card_pos_iff.mpr ⟨Sum.inr false⟩
  let e : Pad ≃ Fin M := Fintype.equivFin Pad
  refine ⟨M, hM,
    fun s => WithLp.toLp 2 ((uPad s).ofLp ∘ e.symm),
    fun t => WithLp.toLp 2 ((vPad t).ofLp ∘ e.symm),
    fun s => (reindex_euclideanSpace_norm e _).trans (huPad s),
    fun t => (reindex_euclideanSpace_norm e _).trans (hvPad t),
    fun s t => ?_⟩
  rw [reindex_euclideanSpace_inner, PiLp.inner_apply, Fintype.sum_sum_type, Fintype.sum_bool]
  have hinl : (∑ x : (ι × κ) × Bool, inner ℝ ((uPad s).ofLp (Sum.inl x))
      ((vPad t).ofLp (Sum.inl x))) = inner ℝ (α' s) (β' t) :=
    (PiLp.inner_apply (α' s) (β' t)).symm
  rw [hinl]
  simp only [uPad, vPad, Sum.elim_inr, Bool.cond_true, Bool.cond_false,
    RCLike.inner_apply, conj_trivial, mul_zero, zero_mul, add_zero]
  rw [inner_complexToRealLp, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  dsimp only [γ, δ]
  rw [WithLp.ofLp_toLp, WithLp.ofLp_toLp, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec,
    conjTranspose_kronecker, (POVM.isHermitian_observable (strat.alice s)).eq, conjTranspose_one,
    ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  rfl

/-- Synthesize a projective quantum strategy on `⌈m / 2⌉` shared EPR pairs whose correlations equal
the real inner products `⟪u s, v t⟫`. -/
noncomputable def ofUnitVectors {S T : Type*} {m : ℕ}
    (u : S → EuclideanSpace ℝ (Fin m)) (hu : ∀ s, ‖u s‖ = 1)
    (v : T → EuclideanSpace ℝ (Fin m)) (hv : ∀ t, ‖v t‖ = 1) :
    QuantumStrategy S T Bool Bool (Fin ((m + 1) / 2) → Bool) (Fin ((m + 1) / 2) → Bool) where
  state := maxEntangled (Fin ((m + 1) / 2) → Bool)
  norm_state := norm_maxEntangled
  alice s := POVM.ofObservable (cliffordObservable (u s))
    (isHermitian_cliffordObservable (u s)) (cliffordObservable_mul_self (hu s))
  bob t := POVM.ofObservable (cliffordObservable (v t))ᵀ
    (isHermitian_transpose_cliffordObservable (v t)) (transpose_cliffordObservable_mul_self (hv t))

theorem correlation_ofUnitVectors {S T : Type*} {m : ℕ}
    (u : S → EuclideanSpace ℝ (Fin m)) (hu : ∀ s, ‖u s‖ = 1)
    (v : T → EuclideanSpace ℝ (Fin m)) (hv : ∀ t, ‖v t‖ = 1) (s : S) (t : T) :
    (ofUnitVectors u hu v hv).correlation s t = inner ℝ (u s) (v t) := by
  unfold correlation ofUnitVectors
  rw [POVM.observable_ofObservable, POVM.observable_ofObservable,
    star_maxEntangled_cliffordObservable (u s) (v t), Complex.ofReal_re]

end QuantumStrategy

/-- **Tsirelson's correspondence, `(2) ⇒ (1)`** ([Cirel'son][Cirelson1980];
[Cleve, Høyer, Toner, Watrous, §5.3, Theorem 4][CleveHoyerTonerWatrous2004]): real unit vectors in
`ℝ^m` yield `±1` observables in dimension `n = 2^⌈m / 2⌉` (`⌈m / 2⌉ = (m + 1) / 2`) and a
maximally entangled unit state realizing all inner products `⟪u_s, v_t⟫`. -/
theorem tsirelson_observables_of_vectors {S T : Type*} {m : ℕ}
    (u : S → EuclideanSpace ℝ (Fin m)) (hu : ∀ s, ‖u s‖ = 1)
    (v : T → EuclideanSpace ℝ (Fin m)) (hv : ∀ t, ‖v t‖ = 1) :
    let n := 2 ^ ((m + 1) / 2)
    0 < n ∧
      ∃ (ψ : EuclideanSpace ℂ (Fin n × Fin n))
        (A : S → Matrix (Fin n) (Fin n) ℂ) (B : T → Matrix (Fin n) (Fin n) ℂ),
        ‖ψ‖ = 1 ∧
        (∀ s, (A s).IsHermitian ∧ A s * A s = 1) ∧
        (∀ t, (B t).IsHermitian ∧ B t * B t = 1) ∧
        ∀ s t, star ψ.ofLp ⬝ᵥ (((A s) ⊗ₖ (B t)) *ᵥ ψ.ofLp) = (inner ℝ (u s) (v t) : ℂ) := by
  intro n
  let k := (m + 1) / 2
  let ι := Fin k → Bool
  have hcard : Fintype.card ι = n := by
    simp [ι, n, k]
  let e : ι ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let ψ : EuclideanSpace ℂ (Fin n × Fin n) :=
    WithLp.toLp 2 ((maxEntangled ι).ofLp ∘ (e.prodCongr e).symm)
  have hψ : ‖ψ‖ = 1 := by
    rw [EuclideanSpace.norm_eq, ← norm_maxEntangled (ι := ι), EuclideanSpace.norm_eq]
    congr 1
    exact Equiv.sum_comp (e.prodCongr e).symm fun p => ‖(maxEntangled ι).ofLp p‖ ^ 2
  let A (s : S) : Matrix (Fin n) (Fin n) ℂ :=
    submatrix (cliffordObservable (u s)) e.symm e.symm
  let B (t : T) : Matrix (Fin n) (Fin n) ℂ :=
    submatrix (cliffordObservable (v t))ᵀ e.symm e.symm
  refine ⟨by positivity, ψ, A, B, hψ, ?_, ?_, ?_⟩
  · intro s
    refine ⟨?_, ?_⟩
    · rw [IsHermitian, conjTranspose_submatrix, (isHermitian_cliffordObservable (u s)).eq]
    · dsimp only [A]
      rw [submatrix_mul_equiv _ _ e.symm e.symm e.symm, cliffordObservable_mul_self (hu s),
        submatrix_one_equiv]
  · intro t
    refine ⟨?_, ?_⟩
    · rw [IsHermitian, conjTranspose_submatrix,
        (isHermitian_transpose_cliffordObservable (v t)).eq]
    · dsimp only [B]
      rw [submatrix_mul_equiv _ _ e.symm e.symm e.symm,
        transpose_cliffordObservable_mul_self (hv t), submatrix_one_equiv]
  · intro s t
    have hkr : (A s ⊗ₖ B t) =
        submatrix ((cliffordObservable (u s)) ⊗ₖ (cliffordObservable (v t))ᵀ)
          (e.prodCongr e).symm (e.prodCongr e).symm := by
      ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
      rfl
    rw [hkr]
    exact (star_dotProduct_submatrix_mulVec (e.prodCongr e)
      ((cliffordObservable (u s)) ⊗ₖ (cliffordObservable (v t))ᵀ) (maxEntangled ι).ofLp).trans
      (star_maxEntangled_cliffordObservable (u s) (v t))

/-- **Tsirelson's theorem** ([Cirel'son][Cirelson1980];
[Cleve, Høyer, Toner, Watrous, §5.3, Theorem 4][CleveHoyerTonerWatrous2004]): `c : S → T → ℝ` is
realized by `±1` observables on `ℂⁿ ⊗ ℂⁿ` if and only if it is realized by unit vectors in
`ℝᵐ`. -/
theorem tsirelson_iff {S T : Type*} (c : S → T → ℝ) :
    (∃ (n : ℕ) (_ : 0 < n) (ψ : EuclideanSpace ℂ (Fin n × Fin n))
        (A : S → Matrix (Fin n) (Fin n) ℂ) (B : T → Matrix (Fin n) (Fin n) ℂ),
        ‖ψ‖ = 1 ∧
        (∀ s, (A s).IsHermitian ∧ A s * A s = 1) ∧
        (∀ t, (B t).IsHermitian ∧ B t * B t = 1) ∧
        ∀ s t, star ψ.ofLp ⬝ᵥ (((A s) ⊗ₖ (B t)) *ᵥ ψ.ofLp) = (c s t : ℂ)) ↔
      (∃ (m : ℕ) (_ : 0 < m) (u : S → EuclideanSpace ℝ (Fin m))
        (v : T → EuclideanSpace ℝ (Fin m)),
        (∀ s, ‖u s‖ = 1) ∧ (∀ t, ‖v t‖ = 1) ∧ ∀ s t, inner ℝ (u s) (v t) = c s t) := by
  constructor
  · rintro ⟨n, _, ψ, A, B, hψ, hA, hB, hc⟩
    obtain ⟨hm, u, v, hu, hv, huv⟩ := tsirelson_vectors_of_observables ψ hψ A B
      (fun s => (hA s).1) (fun s => (hA s).2) (fun t => (hB t).1) (fun t => (hB t).2)
    refine ⟨2 * Fintype.card (Fin n) ^ 2, hm, u, v, hu, hv, fun s t => ?_⟩
    exact Complex.ofReal_injective ((huv s t).symm.trans (hc s t))
  · rintro ⟨m, _, u, v, hu, hv, huv⟩
    obtain ⟨hn, ψ, A, B, hψ, hA, hB, hobs⟩ := tsirelson_observables_of_vectors u hu v hv
    refine ⟨2 ^ ((m + 1) / 2), hn, ψ, A, B, hψ, hA, hB, fun s t => ?_⟩
    rw [hobs s t, huv s t]

/-! ### Elementary Gram–Schmidt dimension reduction to `min(|S|, |T|)` -/

private theorem exists_orthonormal_expansion {M : ℕ} :
    ∀ (r : ℕ) (v : Fin r → EuclideanSpace ℝ (Fin M)),
      ∃ e : Fin r → EuclideanSpace ℝ (Fin M),
        (∀ i j, i ≠ j → inner ℝ (e i) (e j) = 0) ∧
        (∀ i, ‖e i‖ = 1 ∨ e i = 0) ∧
        (∀ j, v j = ∑ i : Fin r, inner ℝ (e i) (v j) • e i)
  | 0, _ => ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun j => j.elim0⟩
  | r + 1, v => by
    obtain ⟨e₀, horth₀, hnorm₀, hexp₀⟩ :=
      exists_orthonormal_expansion r (fun j : Fin r => v j.castSucc)
    let w : EuclideanSpace ℝ (Fin M) :=
      v (Fin.last r) - ∑ i : Fin r, inner ℝ (e₀ i) (v (Fin.last r)) • e₀ i
    let elast : EuclideanSpace ℝ (Fin M) := if w = 0 then 0 else ‖w‖⁻¹ • w
    let e : Fin (r + 1) → EuclideanSpace ℝ (Fin M) := Fin.snoc e₀ elast
    have horth_w (i : Fin r) : inner ℝ (e₀ i) w = 0 := by
      dsimp only [w]
      rw [inner_sub_right, inner_sum]
      have hterm (k : Fin r) :
          inner ℝ (e₀ i) (inner ℝ (e₀ k) (v (Fin.last r)) • e₀ k) =
            if k = i then inner ℝ (e₀ i) (v (Fin.last r)) else 0 := by
        rw [inner_smul_right]
        by_cases hki : k = i
        · subst hki
          rw [ite_eq_left_iff.mpr (fun h => absurd rfl h)]
          rcases hnorm₀ k with hk1 | hk0
          · rw [real_inner_self_eq_norm_sq, hk1, one_pow, mul_one]
          · simp [hk0]
        · rw [ite_eq_right_iff.mpr (fun h => absurd h hki), horth₀ i k (Ne.symm hki), mul_zero]
      simp_rw [hterm]
      have hsum : (∑ k : Fin r, if k = i then inner ℝ (e₀ i) (v (Fin.last r)) else 0) =
          inner ℝ (e₀ i) (v (Fin.last r)) :=
        (Finset.sum_eq_single i (fun k _ hki => ite_eq_right_iff.mpr fun h => absurd h hki)
          (fun hi => absurd (Finset.mem_univ i) hi)).trans (by simp)
      rw [hsum, sub_self]
    have horth_elast (i : Fin r) : inner ℝ (e₀ i) elast = 0 := by
      dsimp only [elast]
      split_ifs with hw
      · simp
      · rw [inner_smul_right, horth_w i, mul_zero]
    have horth : ∀ i j : Fin (r + 1), i ≠ j → inner ℝ (e i) (e j) = 0 := by
      intro i j
      refine Fin.lastCases ?_ (fun i₀ => ?_) i
      · refine Fin.lastCases ?_ (fun j₀ => ?_) j
        · intro hij
          exact absurd rfl hij
        · intro _
          dsimp only [e]
          rw [Fin.snoc_last, Fin.snoc_castSucc, real_inner_comm, horth_elast j₀]
      · refine Fin.lastCases ?_ (fun j₀ => ?_) j
        · intro _
          dsimp only [e]
          rw [Fin.snoc_castSucc, Fin.snoc_last, horth_elast i₀]
        · intro hij
          dsimp only [e]
          rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
          exact horth₀ i₀ j₀ fun h => hij (congrArg Fin.castSucc h)
    have hnorm : ∀ i : Fin (r + 1), ‖e i‖ = 1 ∨ e i = 0 := by
      intro i
      refine Fin.lastCases ?_ (fun i₀ => ?_) i
      · dsimp only [e]
        rw [Fin.snoc_last]
        dsimp only [elast]
        split_ifs with hw
        · exact Or.inr rfl
        · left
          rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg w)),
            inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)]
      · dsimp only [e]
        rw [Fin.snoc_castSucc]
        exact hnorm₀ i₀
    refine ⟨e, horth, hnorm, fun j => ?_⟩
    refine Fin.lastCases ?_ (fun j₀ => ?_) j
    · rw [Fin.sum_univ_castSucc]
      simp only [e, Fin.snoc_castSucc, Fin.snoc_last]
      have helast_v : inner ℝ elast (v (Fin.last r)) • elast = w := by
        have hv_eq : v (Fin.last r) =
            (∑ i : Fin r, inner ℝ (e₀ i) (v (Fin.last r)) • e₀ i) + w := by
          dsimp only [w]; abel
        dsimp only [elast]
        split_ifs with hw
        · simp [hw]
        · have hne : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
          have hin : inner ℝ (‖w‖⁻¹ • w) (v (Fin.last r)) = ‖w‖ := by
            rw [hv_eq, inner_add_right, inner_sum]
            have hz : ∑ i : Fin r, inner ℝ (‖w‖⁻¹ • w)
                (inner ℝ (e₀ i) (v (Fin.last r)) • e₀ i) = 0 := by
              refine Finset.sum_eq_zero fun i _ => ?_
              rw [inner_smul_left, inner_smul_right, RCLike.conj_to_real,
                real_inner_comm (e₀ i) w, horth_w i, mul_zero, mul_zero]
            rw [hz, zero_add, inner_smul_left, RCLike.conj_to_real, real_inner_self_eq_norm_sq, sq,
              ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
          rw [hin, smul_smul, mul_inv_cancel₀ hne, one_smul]
      rw [helast_v]
      dsimp only [w]
      abel
    · rw [Fin.sum_univ_castSucc]
      simp only [e, Fin.snoc_castSucc, Fin.snoc_last]
      have hlast0 : inner ℝ elast (v j₀.castSucc) = 0 := by
        rw [hexp₀ j₀, inner_sum]
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [inner_smul_right, real_inner_comm (e₀ i) elast, horth_elast i, mul_zero]
      rw [hlast0, zero_smul, add_zero]
      exact hexp₀ j₀

private theorem bessel_sum_sq_le {M r : ℕ} (e : Fin r → EuclideanSpace ℝ (Fin M))
    (horth : ∀ i j, i ≠ j → inner ℝ (e i) (e j) = 0)
    (hnorm : ∀ i, ‖e i‖ = 1 ∨ e i = 0) (x : EuclideanSpace ℝ (Fin M)) :
    (∑ i : Fin r, inner ℝ (e i) x ^ 2) ≤ ‖x‖ ^ 2 := by
  let p : EuclideanSpace ℝ (Fin M) := ∑ i : Fin r, inner ℝ (e i) x • e i
  have hp_sq : ‖p‖ ^ 2 = ∑ i : Fin r, inner ℝ (e i) x ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    dsimp only [p]
    rw [sum_inner]
    have hrow (i : Fin r) :
        inner ℝ (inner ℝ (e i) x • e i) (∑ j : Fin r, inner ℝ (e j) x • e j) =
          inner ℝ (e i) x ^ 2 := by
      rw [inner_sum]
      have hterm (j : Fin r) :
          inner ℝ (inner ℝ (e i) x • e i) (inner ℝ (e j) x • e j) =
            if j = i then inner ℝ (e i) x ^ 2 else 0 := by
        rw [inner_smul_left, inner_smul_right, RCLike.conj_to_real]
        by_cases hji : j = i
        · subst hji
          rw [ite_eq_left_iff.mpr (fun h => absurd rfl h)]
          rcases hnorm j with hj1 | hj0
          · rw [real_inner_self_eq_norm_sq, hj1, one_pow, mul_one, ← sq]
          · simp [hj0]
        · rw [ite_eq_right_iff.mpr (fun h => absurd h hji), horth i j (Ne.symm hji), mul_zero,
            mul_zero]
      simp_rw [hterm]
      exact (Finset.sum_eq_single i (fun j _ hji => ite_eq_right_iff.mpr fun h => absurd h hji)
        (fun hi => absurd (Finset.mem_univ i) hi)).trans (by simp)
    simp_rw [hrow]
  have hxp : inner ℝ x p = ∑ i : Fin r, inner ℝ (e i) x ^ 2 := by
    dsimp only [p]
    rw [inner_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_right, real_inner_comm (e i) x, sq]
  have hdiff : 0 ≤ ‖x - p‖ ^ 2 := sq_nonneg _
  rw [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_sub_right,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_comm x p, hxp, hp_sq]
    at hdiff
  linarith

private theorem exists_unit_vectors_dim_le_right {S T : Type*} [Fintype S] [Fintype T]
    {m M : ℕ} (hm_pos : 0 < m) (hTm : Fintype.card T ≤ m)
    (W : S → T → ℝ)
    (u : S → EuclideanSpace ℝ (Fin M)) (hu : ∀ s, ‖u s‖ = 1)
    (v : T → EuclideanSpace ℝ (Fin M)) (hv : ∀ t, ‖v t‖ = 1) :
    ∃ (u' : S → EuclideanSpace ℝ (Fin m)) (v' : T → EuclideanSpace ℝ (Fin m)),
      (∀ s, ‖u' s‖ = 1) ∧ (∀ t, ‖v' t‖ = 1) ∧
      ∑ s : S, ∑ t : T, W s t * inner ℝ (u s) (v t) ≤
        ∑ s : S, ∑ t : T, W s t * inner ℝ (u' s) (v' t) := by
  let r := Fintype.card T
  let eT : T ≃ Fin r := Fintype.equivFin T
  obtain ⟨e, horth, hnorm, hexp⟩ := exists_orthonormal_expansion r (fun j => v (eT.symm j))
  let proj (x : EuclideanSpace ℝ (Fin M)) : EuclideanSpace ℝ (Fin m) :=
    WithLp.toLp 2 fun k : Fin m => if hk : k.1 < r then inner ℝ (e ⟨k.1, hk⟩) x else 0
  let emb : Fin r ↪ Fin m := ⟨fun j => ⟨j.1, by omega⟩, fun a b h => Fin.ext (Fin.mk.inj h)⟩
  have hproj_inner (x y : EuclideanSpace ℝ (Fin M)) :
      inner ℝ (proj x) (proj y) = ∑ j : Fin r, inner ℝ (e j) x * inner ℝ (e j) y := by
    rw [PiLp.inner_apply]
    have hsub : (∑ k ∈ Finset.univ.map emb, inner ℝ ((proj x).ofLp k) ((proj y).ofLp k)) =
        ∑ k : Fin m, inner ℝ ((proj x).ofLp k) ((proj y).ofLp k) := by
      refine Finset.sum_subset (Finset.subset_univ _) fun k _ hk_not => ?_
      have hge : ¬ k.1 < r := fun hlt =>
        hk_not (Finset.mem_map.mpr ⟨⟨k.1, hlt⟩, Finset.mem_univ _, rfl⟩)
      simp [proj, hge]
    rw [← hsub, Finset.sum_map]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hlt : (emb j).1 < r := j.2
    simp only [proj, hlt, ↓reduceDIte, RCLike.inner_apply, conj_trivial]
    exact mul_comm _ _
  have hproj_norm_le (x : EuclideanSpace ℝ (Fin M)) : ‖proj x‖ ≤ ‖x‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [← real_inner_self_eq_norm_sq, hproj_inner]
    simpa only [← sq] using bessel_sum_sq_le e horth hnorm x
  have hproj_v (x : EuclideanSpace ℝ (Fin M)) (t : T) :
      inner ℝ (proj x) (proj (v t)) = inner ℝ x (v t) := by
    have hvt : v t = ∑ i : Fin r, inner ℝ (e i) (v t) • e i := by
      simpa only [Equiv.symm_apply_apply] using hexp (eT t)
    conv_rhs => rw [hvt]
    rw [inner_sum, hproj_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_right, real_inner_comm x (e i), mul_comm]
  let v' (t : T) : EuclideanSpace ℝ (Fin m) := proj (v t)
  have hv' (t : T) : ‖v' t‖ = 1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    rw [← real_inner_self_eq_norm_sq, hproj_v (v t) t, real_inner_self_eq_norm_sq, hv t]
  let w (s : S) : EuclideanSpace ℝ (Fin m) := ∑ t : T, W s t • v' t
  let d0 : EuclideanSpace ℝ (Fin m) := EuclideanSpace.single ⟨0, hm_pos⟩ 1
  have hd0 : ‖d0‖ = 1 := by simp [d0]
  let u' (s : S) : EuclideanSpace ℝ (Fin m) :=
    if w s = 0 then d0 else ‖w s‖⁻¹ • w s
  have hu' (s : S) : ‖u' s‖ = 1 := by
    dsimp only [u']
    split_ifs with hws
    · exact hd0
    · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hws)]
  refine ⟨u', v', hu', hv', Finset.sum_le_sum fun s _ => ?_⟩
  have hlhs : (∑ t : T, W s t * inner ℝ (u s) (v t)) = inner ℝ (proj (u s)) (w s) := by
    dsimp only [w]
    rw [inner_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [inner_smul_right, ← hproj_v (u s) t]
  have hrhs : (∑ t : T, W s t * inner ℝ (u' s) (v' t)) = inner ℝ (u' s) (w s) := by
    dsimp only [w]
    rw [inner_sum]
    refine Finset.sum_congr rfl fun t _ => (inner_smul_right _ _ _).symm
  have hu'_ws : inner ℝ (u' s) (w s) = ‖w s‖ := by
    dsimp only [u']
    split_ifs with hws
    · simp [hws]
    · rw [inner_smul_left, RCLike.conj_to_real, real_inner_self_eq_norm_sq, sq, ← mul_assoc,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hws), one_mul]
  rw [hlhs, hrhs, hu'_ws]
  calc
    inner ℝ (proj (u s)) (w s) ≤ ‖proj (u s)‖ * ‖w s‖ := real_inner_le_norm _ _
    _ ≤ 1 * ‖w s‖ :=
      mul_le_mul_of_nonneg_right ((hproj_norm_le (u s)).trans_eq (hu s)) (norm_nonneg _)
    _ = ‖w s‖ := one_mul _

private theorem exists_unit_vectors_dim_min {S T : Type*} [Fintype S] [Nonempty S]
    [Fintype T] [Nonempty T] {M : ℕ} (W : S → T → ℝ)
    (u : S → EuclideanSpace ℝ (Fin M)) (hu : ∀ s, ‖u s‖ = 1)
    (v : T → EuclideanSpace ℝ (Fin M)) (hv : ∀ t, ‖v t‖ = 1) :
    let m := min (Fintype.card S) (Fintype.card T)
    ∃ (u' : S → EuclideanSpace ℝ (Fin m)) (v' : T → EuclideanSpace ℝ (Fin m)),
      (∀ s, ‖u' s‖ = 1) ∧ (∀ t, ‖v' t‖ = 1) ∧
      ∑ s : S, ∑ t : T, W s t * inner ℝ (u s) (v t) ≤
        ∑ s : S, ∑ t : T, W s t * inner ℝ (u' s) (v' t) := by
  intro m
  have hm_pos : 0 < m := lt_min Fintype.card_pos Fintype.card_pos
  rcases le_total (Fintype.card T) (Fintype.card S) with hTS | hST
  · have hm : Fintype.card T ≤ m := le_min hTS le_rfl
    exact exists_unit_vectors_dim_le_right hm_pos hm W u hu v hv
  · have hm : Fintype.card S ≤ m := le_min le_rfl hST
    obtain ⟨v', u', hv', hu', hle⟩ :=
      exists_unit_vectors_dim_le_right hm_pos hm (fun t s => W s t) v hv u hu
    refine ⟨u', v', hu', hv', ?_⟩
    have hswap1 : (∑ s : S, ∑ t : T, W s t * inner ℝ (u s) (v t)) =
        ∑ t : T, ∑ s : S, W s t * inner ℝ (v t) (u s) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [real_inner_comm]
    have hswap2 : (∑ t : T, ∑ s : S, W s t * inner ℝ (v' t) (u' s)) =
        ∑ s : S, ∑ t : T, W s t * inner ℝ (u' s) (v' t) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [real_inner_comm]
    exact (hswap1 ▸ hle).trans_eq hswap2

/-! ### General XOR games, Proposition 5, and Theorem 10 (CHTW §5.3–5.4) -/

namespace TwoProverGame

section XOR

variable {X Y : Type*}

/-- A binary game is an **XOR game** when its acceptance predicate depends only on `a ^^ b`
([Cleve, Høyer, Toner, Watrous, §5][CleveHoyerTonerWatrous2004]). -/
def IsXORGame (G : TwoProverGame X Y Bool Bool) : Prop :=
  ∀ x y a b, G.accepts x y a b ↔ G.accepts x y (a ^^ b) false

/-- The canonical **XOR game** with question distribution `μ` and target parity `f x y`, accepted
when `(a ^^ b) = f x y`. -/
noncomputable def xorGame (μ : PMF (X × Y)) (f : X → Y → Bool) :
    TwoProverGame X Y Bool Bool where
  questions := μ
  accepts x y a b := (a ^^ b) = f x y

instance (μ : PMF (X × Y)) (f : X → Y → Bool) (x : X) (y : Y) (a b : Bool) :
    Decidable ((xorGame μ f).accepts x y a b) :=
  inferInstanceAs (Decidable ((a ^^ b) = f x y))

theorem isXORGame_xorGame (μ : PMF (X × Y)) (f : X → Y → Bool) :
    (xorGame μ f).IsXORGame := by
  intro x y a b
  simp [xorGame]

/-- `chsh` is the uniform `xorGame` for `x && y`. -/
theorem chsh_eq_xorGame :
    chsh = xorGame (uniformOfFintype (Bool × Bool)) (fun x y => x && y) :=
  rfl

/-- The **trivial random winning probability** `τ(G)` when Alice and Bob ignore their questions and
output independent uniform bits
([Cleve, Høyer, Toner, Watrous, §5.3][CleveHoyerTonerWatrous2004]). -/
noncomputable def trivialWinProb (G : TwoProverGame X Y Bool Bool) : ℝ :=
  G.answersWinProb (fun _ _ => uniformOfFintype (Bool × Bool))

/-- The XOR bias coefficient `V(0 | x, y) - V(1 | x, y)` in `{ -1, 0, 1 }`. -/
def xorCoeff (G : TwoProverGame X Y Bool Bool) [∀ x y a b, Decidable (G.accepts x y a b)]
    (x : X) (y : Y) : ℝ :=
  (if G.accepts x y false false then 1 else 0) - (if G.accepts x y true false then 1 else 0)

@[simp] theorem xorCoeff_xorGame (μ : PMF (X × Y)) (f : X → Y → Bool) (x : X) (y : Y) :
    (xorGame μ f).xorCoeff x y = signVal (f x y) := by
  cases h : f x y <;> simp [xorCoeff, xorGame, signVal, h]

section FiniteQuestions

variable [Fintype X] [Fintype Y]

/-- Explicit sum formula for `τ(G)` on an XOR game, matching
`τ(G) = ½ ∑_{c ∈ {0,1}} ∑_{x,y} π(x,y) V(c | x,y)`
([Cleve, Høyer, Toner, Watrous, §5.3][CleveHoyerTonerWatrous2004]). -/
theorem trivialWinProb_eq_sum {G : TwoProverGame X Y Bool Bool}
    [∀ x y a b, Decidable (G.accepts x y a b)] (hG : G.IsXORGame) :
    G.trivialWinProb = (1 / 2 : ℝ) * ∑ x : X, ∑ y : Y, (G.questions (x, y)).toReal *
      ((if G.accepts x y false false then (1 : ℝ) else 0) +
        (if G.accepts x y true false then 1 else 0)) := by
  rw [trivialWinProb, answersWinProb_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  have hunif (p : Bool × Bool) : ((uniformOfFintype (Bool × Bool)) p).toReal = 1 / 4 := by
    rw [uniformOfFintype_apply, Fintype.card_prod, Fintype.card_bool]
    norm_num
  rw [Fintype.sum_bool]
  simp only [Fintype.sum_bool, hunif]
  have h01 : G.accepts x y false true = G.accepts x y true false := propext (hG x y false true)
  have h11 : G.accepts x y true true = G.accepts x y false false := propext (hG x y true true)
  by_cases hf : G.accepts x y false false <;> by_cases ht : G.accepts x y true false <;>
    simp only [h01, h11, hf, ht, ↓reduceIte] <;> ring

end FiniteQuestions

@[simp] theorem trivialWinProb_xorGame [Finite X] [Finite Y] (μ : PMF (X × Y))
    (f : X → Y → Bool) :
    (xorGame μ f).trivialWinProb = 1 / 2 := by
  let _ := Fintype.ofFinite X
  let _ := Fintype.ofFinite Y
  rw [trivialWinProb_eq_sum (isXORGame_xorGame μ f)]
  have h1 (x : X) (y : Y) :
      ((if (xorGame μ f).accepts x y false false then (1 : ℝ) else 0) +
        (if (xorGame μ f).accepts x y true false then 1 else 0)) = 1 := by
    cases h : f x y <;> simp [xorGame, h]
  simp_rw [h1, mul_one]
  have hsum : (∑ x : X, ∑ y : Y, (μ (x, y)).toReal) = 1 := by
    rw [← Fintype.sum_prod_type (f := fun p => (μ p).toReal)]
    exact Cslib.Probability.PMF.sum_toReal μ
  dsimp only [xorGame]
  rw [hsum, mul_one]

section FiniteQuestions2

variable [Fintype X] [Fintype Y]

/-- Quantum advantage over the trivial random strategy in terms of `S.correlation`
([Cleve, Høyer, Toner, Watrous, proof of Proposition 5][CleveHoyerTonerWatrous2004]). -/
theorem quantumWinProb_sub_trivialWinProb {G : TwoProverGame X Y Bool Bool}
    [∀ x y a b, Decidable (G.accepts x y a b)] (hG : G.IsXORGame)
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (S : QuantumStrategy X Y Bool Bool ι κ) :
    G.quantumWinProb S - G.trivialWinProb =
      (1 / 2 : ℝ) * ∑ x : X, ∑ y : Y,
        (G.questions (x, y)).toReal * G.xorCoeff x y * S.correlation x y := by
  rw [quantumWinProb_eq_sum, trivialWinProb_eq_sum hG, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  have hsum_p := S.sum_prob x y
  have hcorr := S.correlation_eq x y
  rw [Fintype.sum_bool] at hsum_p ⊢
  simp only [Fintype.sum_bool] at hsum_p ⊢
  change (G.questions (x, y)).toReal *
      ((if G.accepts x y true true then S.prob x y true true else 0) +
        (if G.accepts x y true false then S.prob x y true false else 0) +
        ((if G.accepts x y false true then S.prob x y false true else 0) +
          (if G.accepts x y false false then S.prob x y false false else 0))) - _ = _
  have h01 : G.accepts x y false true = G.accepts x y true false := propext (hG x y false true)
  have h11 : G.accepts x y true true = G.accepts x y false false := propext (hG x y true true)
  unfold xorCoeff
  by_cases hf : G.accepts x y false false <;> by_cases ht : G.accepts x y true false
  · simp only [h01, h11, hf, ht, ↓reduceIte]
    linear_combination (G.questions (x, y)).toReal * hsum_p
  · simp only [h01, h11, hf, ht, ↓reduceIte]
    linear_combination (1 / 2 : ℝ) * (G.questions (x, y)).toReal * (hsum_p - hcorr)
  · simp only [h01, h11, hf, ht, ↓reduceIte]
    linear_combination (1 / 2 : ℝ) * (G.questions (x, y)).toReal * (hsum_p + hcorr)
  · simp only [h01, h11, hf, ht, ↓reduceIte]
    ring

/-- Deterministic advantage over `τ(G)` as a `±1` sign bilinear form. -/
theorem winProb_sub_trivialWinProb {G : TwoProverGame X Y Bool Bool}
    [∀ x y a b, Decidable (G.accepts x y a b)] (hG : G.IsXORGame)
    (ha : X → Bool) (hb : Y → Bool) :
    G.winProb ha hb - G.trivialWinProb =
      (1 / 2 : ℝ) * ∑ x : X, ∑ y : Y,
        (G.questions (x, y)).toReal * G.xorCoeff x y * (signVal (ha x) * signVal (hb y)) := by
  rw [← G.quantumWinProb_ofDeterministic ha hb, quantumWinProb_sub_trivialWinProb hG]
  congr 1
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  congr 1
  rw [QuantumStrategy.correlation_eq]
  have hp (a b : Bool) :
      (QuantumStrategy.ofDeterministic ha hb).prob x y a b =
        if a = ha x ∧ b = hb y then 1 else 0 := by
    simp only [QuantumStrategy.prob_eq, QuantumStrategy.ofDeterministic, POVM.const]
    by_cases h1 : a = ha x <;> by_cases h2 : b = hb y <;> simp [h1, h2]
  simp only [hp]
  cases ha x <;> cases hb y <;> simp [signVal]

/-- **Classical bias characterization of XOR games**
([Cleve, Høyer, Toner, Watrous, §5.3][CleveHoyerTonerWatrous2004]):
`ω_c(G) - τ(G) = ½ max_{a,b : {±1}} ∑_{x,y} π(x,y) xorCoeff(x,y) a(x) b(y)`. -/
theorem value_sub_trivialWinProb {G : TwoProverGame X Y Bool Bool}
    [∀ x y a b, Decidable (G.accepts x y a b)] (hG : G.IsXORGame) :
    G.value - G.trivialWinProb =
      (1 / 2 : ℝ) * ⨆ (ha : X → Bool) (hb : Y → Bool),
        ∑ x : X, ∑ y : Y,
          (G.questions (x, y)).toReal * G.xorCoeff x y * (signVal (ha x) * signVal (hb y)) := by
  let B (ha : X → Bool) (hb : Y → Bool) : ℝ :=
    ∑ x : X, ∑ y : Y,
      (G.questions (x, y)).toReal * G.xorCoeff x y * (signVal (ha x) * signVal (hb y))
  have hb_bdd1 (ha : X → Bool) : BddAbove (Set.range (B ha)) := (Set.finite_range _).bddAbove
  have hb_bdd2 : BddAbove (Set.range fun ha : X → Bool => ⨆ hb : Y → Bool, B ha hb) :=
    (Set.finite_range _).bddAbove
  obtain ⟨ha₀, hb₀, hmax⟩ := G.exists_winProb_eq_value
  apply le_antisymm
  · rw [← hmax, winProb_sub_trivialWinProb hG ha₀ hb₀]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    exact (le_ciSup (hb_bdd1 ha₀) hb₀).trans (le_ciSup hb_bdd2 ha₀)
  · obtain ⟨ha₁, hha₁⟩ := exists_eq_ciSup_of_finite (f := fun ha : X → Bool => ⨆ hb, B ha hb)
    obtain ⟨hb₁, hhb₁⟩ := exists_eq_ciSup_of_finite (f := B ha₁)
    rw [← hha₁, ← hhb₁]
    change (1 / 2 : ℝ) * B ha₁ hb₁ ≤ G.value - G.trivialWinProb
    rw [← winProb_sub_trivialWinProb hG ha₁ hb₁]
    linarith [G.winProb_le_value ha₁ hb₁]

/-- **Proposition 5 (attainment form)** of
[Cleve, Høyer, Toner, Watrous, §5.3][CleveHoyerTonerWatrous2004]: for every XOR game `G` on
nonempty finite question sets and `m = min(|X|, |Y|)`, there exist real unit vectors in `ℝ^m`
maximizing the vector objective across all dimensions and attaining `ω_q(G) - τ(G)`. -/
theorem exists_max_unit_vectors_xorGame [Nonempty X] [Nonempty Y]
    {G : TwoProverGame X Y Bool Bool} [∀ x y a b, Decidable (G.accepts x y a b)]
    (hG : G.IsXORGame) :
    let m := min (Fintype.card X) (Fintype.card Y)
    ∃ (u : X → EuclideanSpace ℝ (Fin m)) (v : Y → EuclideanSpace ℝ (Fin m)),
      (∀ x, ‖u x‖ = 1) ∧ (∀ y, ‖v y‖ = 1) ∧
      (∀ {M : ℕ} (u' : X → EuclideanSpace ℝ (Fin M)) (v' : Y → EuclideanSpace ℝ (Fin M)),
        (∀ x, ‖u' x‖ = 1) → (∀ y, ‖v' y‖ = 1) →
        ∑ x : X, ∑ y : Y, (G.questions (x, y)).toReal * G.xorCoeff x y * inner ℝ (u' x) (v' y) ≤
          ∑ x : X, ∑ y : Y, (G.questions (x, y)).toReal * G.xorCoeff x y * inner ℝ (u x) (v y)) ∧
      G.quantumValue - G.trivialWinProb =
        (1 / 2 : ℝ) * ∑ x : X, ∑ y : Y,
          (G.questions (x, y)).toReal * G.xorCoeff x y * inner ℝ (u x) (v y) := by
  intro m
  have hm_pos : 0 < m := lt_min Fintype.card_pos Fintype.card_pos
  let W (x : X) (y : Y) : ℝ := (G.questions (x, y)).toReal * G.xorCoeff x y
  let Sph := Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1
  have : Nonempty Sph :=
    ⟨⟨EuclideanSpace.single ⟨0, hm_pos⟩ 1, mem_sphere_zero_iff_norm.mpr (by simp)⟩⟩
  have : CompactSpace Sph := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  let Dom := (X → Sph) × (Y → Sph)
  let F (uv : Dom) : ℝ :=
    ∑ x : X, ∑ y : Y, W x y * inner ℝ (uv.1 x : EuclideanSpace ℝ (Fin m)) (uv.2 y)
  have hF_cont : Continuous F := by
    refine continuous_finset_sum_real Finset.univ fun x _ =>
      continuous_finset_sum_real Finset.univ fun y _ => ?_
    refine continuous_const.mul (Continuous.inner ?_ ?_)
    · exact continuous_subtype_val.comp ((continuous_apply x).comp continuous_fst)
    · exact continuous_subtype_val.comp ((continuous_apply y).comp continuous_snd)
  obtain ⟨⟨u₀, v₀⟩, _, hmax_dom⟩ :=
    isCompact_univ.exists_isMaxOn Set.univ_nonempty hF_cont.continuousOn
  let u (x : X) : EuclideanSpace ℝ (Fin m) := (u₀ x).1
  let v (y : Y) : EuclideanSpace ℝ (Fin m) := (v₀ y).1
  have hu (x : X) : ‖u x‖ = 1 := mem_sphere_zero_iff_norm.mp (u₀ x).2
  have hv (y : Y) : ‖v y‖ = 1 := mem_sphere_zero_iff_norm.mp (v₀ y).2
  have hmax_all : ∀ {M : ℕ} (u' : X → EuclideanSpace ℝ (Fin M)) (v' : Y → EuclideanSpace ℝ (Fin M)),
      (∀ x, ‖u' x‖ = 1) → (∀ y, ‖v' y‖ = 1) →
      ∑ x : X, ∑ y : Y, W x y * inner ℝ (u' x) (v' y) ≤
        ∑ x : X, ∑ y : Y, W x y * inner ℝ (u x) (v y) := by
    intro M u' v' hu' hv'
    obtain ⟨u'', v'', hu'', hv'', hle⟩ := exists_unit_vectors_dim_min W u' hu' v' hv'
    let p : Dom :=
      (fun x => ⟨u'' x, mem_sphere_zero_iff_norm.mpr (hu'' x)⟩,
        fun y => ⟨v'' y, mem_sphere_zero_iff_norm.mpr (hv'' y)⟩)
    exact hle.trans (isMaxOn_iff.mp hmax_dom p (Set.mem_univ p))
  refine ⟨u, v, hu, hv, fun u' v' hu' hv' => hmax_all u' v' hu' hv', ?_⟩
  let S_opt := QuantumStrategy.ofUnitVectors u hu v hv
  have hS_opt : G.quantumWinProb S_opt = G.trivialWinProb +
      (1 / 2 : ℝ) * ∑ x : X, ∑ y : Y, W x y * inner ℝ (u x) (v y) := by
    have hsub := quantumWinProb_sub_trivialWinProb hG S_opt
    dsimp only [S_opt] at hsub
    simp only [QuantumStrategy.correlation_ofUnitVectors] at hsub
    linarith
  have hval_le : G.quantumValue ≤ G.quantumWinProb S_opt := by
    refine G.quantumValue_le (G.quantumWinProb_nonneg S_opt) fun {ι κ} _ _ _ _ S => ?_
    obtain ⟨M, _, uS, vS, huS, hvS, hcorrS⟩ := S.exists_unit_vectors_correlation
    have hsubS := quantumWinProb_sub_trivialWinProb hG S
    have hrew : (∑ x : X, ∑ y : Y, W x y * S.correlation x y) =
        ∑ x : X, ∑ y : Y, W x y * inner ℝ (uS x) (vS y) := by
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      rw [hcorrS]
    have hle := hmax_all uS vS huS hvS
    linarith
  have hopt_le : G.quantumWinProb S_opt ≤ G.quantumValue := G.quantumWinProb_le_quantumValue S_opt
  linarith

/-- **Proposition 5 (supremum / SDP form)** of
[Cleve, Høyer, Toner, Watrous, §5.3][CleveHoyerTonerWatrous2004]: `ω_q(G) - τ(G)` is half the
supremum over real unit vectors in `ℝ^(min(|X|, |Y|))`. -/
theorem quantumValue_sub_trivialWinProb [Nonempty X] [Nonempty Y]
    {G : TwoProverGame X Y Bool Bool} [∀ x y a b, Decidable (G.accepts x y a b)]
    (hG : G.IsXORGame) :
    let m := min (Fintype.card X) (Fintype.card Y)
    let Sph := Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1
    G.quantumValue - G.trivialWinProb =
      (1 / 2 : ℝ) * ⨆ (u : X → Sph) (v : Y → Sph),
        ∑ x : X, ∑ y : Y,
          (G.questions (x, y)).toReal * G.xorCoeff x y *
            inner ℝ (u x : EuclideanSpace ℝ (Fin m)) (v y) := by
  intro m Sph
  obtain ⟨u₀, v₀, hu₀, hv₀, hmax, hval⟩ := exists_max_unit_vectors_xorGame hG
  let obj (u : X → Sph) (v : Y → Sph) : ℝ :=
    ∑ x : X, ∑ y : Y,
      (G.questions (x, y)).toReal * G.xorCoeff x y *
        inner ℝ (u x : EuclideanSpace ℝ (Fin m)) (v y)
  let topVal : ℝ :=
    ∑ x : X, ∑ y : Y, (G.questions (x, y)).toReal * G.xorCoeff x y * inner ℝ (u₀ x) (v₀ y)
  let uSph : X → Sph := fun x => ⟨u₀ x, mem_sphere_zero_iff_norm.mpr (hu₀ x)⟩
  let vSph : Y → Sph := fun y => ⟨v₀ y, mem_sphere_zero_iff_norm.mpr (hv₀ y)⟩
  have : Nonempty Sph := ⟨uSph (Classical.arbitrary X)⟩
  have hub (u : X → Sph) (v : Y → Sph) : obj u v ≤ topVal :=
    hmax (fun x => (u x).1) (fun y => (v y).1)
      (fun x => mem_sphere_zero_iff_norm.mp (u x).2)
      (fun y => mem_sphere_zero_iff_norm.mp (v y).2)
  have hbdd1 (u : X → Sph) : BddAbove (Set.range (obj u)) :=
    ⟨topVal, by rintro _ ⟨v, rfl⟩; exact hub u v⟩
  have hbdd2 : BddAbove (Set.range fun u : X → Sph => ⨆ v : Y → Sph, obj u v) :=
    ⟨topVal, by rintro _ ⟨u, rfl⟩; exact ciSup_le (hub u)⟩
  have heq : (⨆ (u : X → Sph) (v : Y → Sph), obj u v) = topVal := by
    apply le_antisymm
    · exact ciSup_le fun u => ciSup_le (hub u)
    · calc
        topVal = obj uSph vSph := rfl
        _ ≤ ⨆ v : Y → Sph, obj uSph v := le_ciSup (hbdd1 uSph) vSph
        _ ≤ ⨆ (u : X → Sph) (v : Y → Sph), obj u v := le_ciSup hbdd2 uSph
  rw [hval, heq]

/-- **Theorem 10** of [Cleve, Høyer, Toner, Watrous, §5.4][CleveHoyerTonerWatrous2004]: every XOR
game on nonempty finite question sets has an optimal quantum strategy sharing a maximally entangled
state on `⌈min(|X|, |Y|) / 2⌉` qubits. -/
theorem exists_maxEntangled_optimal_strategy [Nonempty X] [Nonempty Y]
    {G : TwoProverGame X Y Bool Bool} (hG : G.IsXORGame) :
    let k := (min (Fintype.card X) (Fintype.card Y) + 1) / 2
    ∃ S : QuantumStrategy X Y Bool Bool (Fin k → Bool) (Fin k → Bool),
      S.state = maxEntangled (Fin k → Bool) ∧ G.quantumWinProb S = G.quantumValue := by
  classical
  intro k
  obtain ⟨u, v, hu, hv, _, hval⟩ := exists_max_unit_vectors_xorGame hG
  let S := QuantumStrategy.ofUnitVectors u hu v hv
  refine ⟨S, rfl, ?_⟩
  have hsub := quantumWinProb_sub_trivialWinProb hG S
  dsimp only [S] at hsub
  simp only [QuantumStrategy.correlation_ofUnitVectors] at hsub
  linarith

end FiniteQuestions2

end XOR

/-! ### The Odd-Cycle XOR game (CHTW §3.2) -/

section OddCycle

/-- Question distribution of the `n`-vertex Odd-Cycle game: uniform over
`{(s, t) | s = t ∨ s + 1 = t}` in `ZMod n × ZMod n`
([Cleve, Høyer, Toner, Watrous, §3.2][CleveHoyerTonerWatrous2004]). -/
noncomputable def oddCycleQuestions (n : ℕ) [NeZero n] : PMF (ZMod n × ZMod n) :=
  (uniformOfFintype (ZMod n × Bool)).map fun sb => bif sb.2 then (sb.1, sb.1 + 1) else (sb.1, sb.1)

/-- The **Odd-Cycle XOR game** on `ZMod n`
([Cleve, Høyer, Toner, Watrous, §3.2][CleveHoyerTonerWatrous2004]): answers must agree when `s = t`
and differ when `s + 1 = t`. -/
noncomputable def oddCycleGame (n : ℕ) [NeZero n] : TwoProverGame (ZMod n) (ZMod n) Bool Bool :=
  xorGame (oddCycleQuestions n) (fun s t => decide (s + 1 = t))

instance (n : ℕ) [NeZero n] (x y : ZMod n) (a b : Bool) :
    Decidable ((oddCycleGame n).accepts x y a b) :=
  inferInstanceAs (Decidable ((a ^^ b) = decide (x + 1 = y)))

theorem isXORGame_oddCycleGame (n : ℕ) [NeZero n] : (oddCycleGame n).IsXORGame :=
  isXORGame_xorGame _ _

@[simp] theorem xorCoeff_oddCycleGame (n : ℕ) [NeZero n] (s t : ZMod n) :
    (oddCycleGame n).xorCoeff s t = signVal (decide (s + 1 = t)) := by
  by_cases h : s + 1 = t <;> simp [xorCoeff, oddCycleGame, xorGame, signVal, h]

private theorem zmod_add_one_ne_self {n : ℕ} (hn3 : 3 ≤ n) (s : ZMod n) :
    s + 1 ≠ s := by
  intro h
  have h10 : (1 : ZMod n) = 0 := by linear_combination h
  have hval := congrArg ZMod.val h10
  have : Fact (1 < n) := ⟨by omega⟩
  simp only [ZMod.val_one, ZMod.val_zero] at hval
  omega

/-- Explicit winning probability of a deterministic strategy `(ha, hb)` on `oddCycleGame n`. -/
theorem winProb_oddCycleGame {n : ℕ} [NeZero n] (ha hb : ZMod n → Bool) :
    (oddCycleGame n).winProb ha hb =
      ∑ sb : ZMod n × Bool,
        if (ha sb.1 ^^ hb (bif sb.2 then sb.1 + 1 else sb.1)) =
            decide (sb.1 + 1 = bif sb.2 then sb.1 + 1 else sb.1)
        then (2 * (n : ℝ))⁻¹ else 0 := by
  rw [TwoProverGame.winProb, oddCycleGame, xorGame, oddCycleQuestions,
    _root_.PMF.toOuterMeasure_map_apply, Cslib.Probability.PMF.toOuterMeasure_apply_toReal]
  refine Finset.sum_congr rfl fun sb _ => ?_
  have hmass : ((uniformOfFintype (ZMod n × Bool)) sb).toReal = (2 * (n : ℝ))⁻¹ := by
    rw [uniformOfFintype_apply, Fintype.card_prod, ZMod.card, Fintype.card_bool,
      ENNReal.toReal_inv, Nat.cast_mul, Nat.cast_ofNat, ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofNat, mul_comm]
  rw [hmass]
  rcases sb with ⟨s, b⟩
  cases b
  · dsimp only [Bool.cond_false]
    by_cases h : (ha s ^^ hb s) = decide (s + 1 = s) <;> simp [h]
  · dsimp only [Bool.cond_true]
    by_cases h : (ha s ^^ hb (s + 1)) = decide (s + 1 = s + 1) <;> simp [h]

/-- The alternating parity coloring `s.val % 2 == 1` wins `oddCycleGame n` with probability
`1 - 1 / (2n)` for odd `n ≥ 3`. -/
theorem winProb_oddCycleGame_parity {n : ℕ} [NeZero n] (hn : Odd n) (hn3 : 3 ≤ n) :
    let color (s : ZMod n) : Bool := decide (s.val % 2 = 1)
    (oddCycleGame n).winProb color color = 1 - 1 / (2 * (n : ℝ)) := by
  intro color
  rw [winProb_oddCycleGame, Fintype.sum_prod_type]
  have hfalse (s : ZMod n) : decide (s + 1 = s) = false :=
    decide_eq_false (zmod_add_one_ne_self hn3 s)
  simp only [Fintype.sum_bool, Bool.cond_true, Bool.cond_false, decide_true, hfalse, Bool.xor_self,
    ↓reduceIte]
  let last : ZMod n := ((n - 1 : ℕ) : ZMod n)
  have hlast_val : last.val = n - 1 := ZMod.val_natCast_of_lt (by omega)
  have hlast_succ : last + 1 = 0 := by
    have h1 : (1 : ZMod n) = ((1 : ℕ) : ZMod n) := Nat.cast_one.symm
    dsimp only [last]
    rw [h1, ← Nat.cast_add, show n - 1 + 1 = n by omega, ZMod.natCast_self]
  obtain ⟨k, hk⟩ := hn
  have hn_pos : (0 : ℝ) < n := by positivity
  have : Fact (1 < n) := ⟨by omega⟩
  have hedge (s : ZMod n) :
      ((color s ^^ color (s + 1)) = true) ↔ s ≠ last := by
    by_cases hs : s = last
    · subst hs
      rw [hlast_succ]
      simp only [ne_eq, not_true_eq_false, iff_false]
      have hl0 : color last = false := by
        simp only [color, hlast_val, show n - 1 = 2 * k by omega, Nat.mul_mod_right,
          decide_eq_false_iff_not]
        omega
      have hc0 : color 0 = false := by
        simp [color]
      rw [hl0, hc0]
      decide
    · simp only [ne_eq, hs, not_false_eq_true, iff_true]
      have hsv_lt : s.val < 2 * k := by
        have hlt := s.val_lt
        have hne_val : s.val ≠ 2 * k := by
          intro heq
          apply hs
          apply ZMod.val_injective
          rw [hlast_val]
          omega
        omega
      have hsucc_val : (s + 1).val = s.val + 1 := by
        rw [ZMod.val_add, ZMod.val_one, Nat.mod_eq_of_lt (by omega)]
      simp only [color, hsucc_val]
      rcases Nat.mod_two_eq_zero_or_one s.val with h0 | h1
      · have hnext : (s.val + 1) % 2 = 1 := by omega
        simp [h0, hnext]
      · have hnext : (s.val + 1) % 2 = 0 := by omega
        simp [h1, hnext]
  simp_rw [hedge]
  let inv2n : ℝ := (2 * (n : ℝ))⁻¹
  have hterm (s : ZMod n) :
      ((if s ≠ last then inv2n else 0) + inv2n) =
        if s = last then inv2n else 2 * inv2n := by
    by_cases hs : s = last
    · simp [hs]
    · simp only [hs, ne_eq, not_false_eq_true, ↓reduceIte]
      ring
  change (∑ s : ZMod n, ((if s ≠ last then inv2n else 0) + inv2n)) = _
  simp_rw [hterm]
  have hsum : (∑ s : ZMod n, if s = last then inv2n else 2 * inv2n) =
      inv2n + ((n - 1 : ℕ) : ℝ) * (2 * inv2n) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ last)]
    simp only [↓reduceIte]
    congr 1
    have hconst : ∀ s ∈ Finset.univ.erase last,
        (if s = last then inv2n else 2 * inv2n) = 2 * inv2n := by
      intro s hs
      rw [ite_eq_right_iff.mpr (fun h => absurd h (Finset.ne_of_mem_erase hs))]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, ZMod.card, nsmul_eq_mul]
  rw [hsum, Nat.cast_sub (by omega)]
  dsimp only [inv2n]
  push_cast
  field_simp
  ring

/-- **Classical value of the Odd-Cycle game**
([Cleve, Høyer, Toner, Watrous, §3.2][CleveHoyerTonerWatrous2004]):
`ω_c(oddCycleGame n) = 1 - 1 / (2n)` for odd `n ≥ 3`. -/
theorem value_oddCycleGame {n : ℕ} [NeZero n] (hn : Odd n) (hn3 : 3 ≤ n) :
    (oddCycleGame n).value = 1 - 1 / (2 * (n : ℝ)) := by
  apply le_antisymm
  · refine ciSup_le fun ha => ciSup_le fun hb => ?_
    -- Not every pair in `ZMod n × Bool` can be won, since an odd cycle is not 2-colorable.
    have hnot_all : ¬ ∀ sb : ZMod n × Bool,
        (ha sb.1 ^^ hb (bif sb.2 then sb.1 + 1 else sb.1)) =
          decide (sb.1 + 1 = bif sb.2 then sb.1 + 1 else sb.1) := by
      intro hall
      have hsame (s : ZMod n) : ha s = hb s := by
        have h0 := hall (s, false)
        simp only [Bool.cond_false, decide_eq_false (zmod_add_one_ne_self hn3 s)] at h0
        cases h_a : ha s <;> cases h_b : hb s <;> simp [h_a, h_b] at h0 ⊢
      have hflip (s : ZMod n) : ha (s + 1) = !(ha s) := by
        have h1 := hall (s, true)
        simp only [Bool.cond_true, decide_true] at h1
        rw [← hsame (s + 1)] at h1
        cases h_a : ha s <;> cases h_a1 : ha (s + 1) <;> simp [h_a, h_a1] at h1 ⊢
      have hind : ∀ j : ℕ, ha (j : ZMod n) = if j % 2 = 1 then !(ha 0) else ha 0 := by
        intro j
        induction j with
        | zero => simp
        | succ j ih =>
          rw [Nat.cast_add, Nat.cast_one, hflip (j : ZMod n), ih]
          rcases Nat.mod_two_eq_zero_or_one j with h0 | h1
          · have hnext : (j + 1) % 2 = 1 := by omega
            simp [h0, hnext]
          · have hnext : (j + 1) % 2 = 0 := by omega
            simp [h1, hnext]
      have hn_cast := hind n
      obtain ⟨k, hk⟩ := hn
      have hn_mod : n % 2 = 1 := by omega
      simp only [ZMod.natCast_self, hn_mod, ↓reduceIte] at hn_cast
      exact Bool.not_ne_self (ha 0) hn_cast.symm
    obtain ⟨sb₀, hsb₀⟩ := not_forall.mp hnot_all
    rw [winProb_oddCycleGame]
    have hcard : Fintype.card (ZMod n × Bool) = 2 * n := by
      rw [Fintype.card_prod, ZMod.card, Fintype.card_bool, mul_comm]
    let Win (sb : ZMod n × Bool) : Prop :=
      (ha sb.1 ^^ hb (bif sb.2 then sb.1 + 1 else sb.1)) =
        decide (sb.1 + 1 = bif sb.2 then sb.1 + 1 else sb.1)
    change (∑ x : ZMod n × Bool, if Win x then (2 * (n : ℝ))⁻¹ else 0) ≤ _
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ sb₀)]
    rw [ite_eq_right_iff.mpr (fun h => absurd h hsb₀), zero_add]
    have hle_each : ∀ x ∈ Finset.univ.erase sb₀,
        (if Win x then ((2 * (n : ℝ))⁻¹) else 0) ≤ (2 * (n : ℝ))⁻¹ := by
      intro x _
      split_ifs
      · exact le_rfl
      · positivity
    have hsum_le := Finset.sum_le_sum hle_each
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ sb₀), Finset.card_univ,
      hcard, nsmul_eq_mul] at hsum_le
    have hn_pos : (0 : ℝ) < n := by positivity
    calc
      (∑ x ∈ Finset.univ.erase sb₀, if Win x then (2 * (n : ℝ))⁻¹ else 0)
          ≤ ((2 * n - 1 : ℕ) : ℝ) * (2 * (n : ℝ))⁻¹ := hsum_le
      _ = 1 - 1 / (2 * (n : ℝ)) := by
        rw [Nat.cast_sub (by omega)]
        push_cast
        field_simp
  · rw [← winProb_oddCycleGame_parity hn hn3]
    exact (oddCycleGame n).winProb_le_value _ _

/-- Alice's measurement angle `(π/2 - π/(2n)) s - π/(4n)` in the Braunstein–Caves strategy for
`oddCycleGame n`. (Note: [Cleve, Høyer, Toner, Watrous, §3.2][CleveHoyerTonerWatrous2004] print
`+ π/(4n)`, which corresponds to the reversed edge orientation `t + 1 ≡ s`; for `s + 1 ≡ t`,
`- π/(4n)` gives `α_s - β_{s+1} = -π/2 + π/(4n)` and `sin²(α_s - β_{s+1}) = cos²(π/(4n))`.) -/
noncomputable def oddCycleAliceAngle (n : ℕ) (s : ZMod n) : ℝ :=
  (π / 2 - π / (2 * (n : ℝ))) * (s.val : ℝ) - π / (4 * (n : ℝ))

/-- Bob's measurement angle `(π/2 - π/(2n)) t` in the Braunstein–Caves strategy for
`oddCycleGame n`. -/
noncomputable def oddCycleBobAngle (n : ℕ) (t : ZMod n) : ℝ :=
  (π / 2 - π / (2 * (n : ℝ))) * (t.val : ℝ)

/-- The **Braunstein–Caves EPR rotation strategy** for `oddCycleGame n`
([Cleve, Høyer, Toner, Watrous, §3.2][CleveHoyerTonerWatrous2004]). -/
noncomputable def oddCycleStrategy (n : ℕ) :
    QuantumStrategy (ZMod n) (ZMod n) Bool Bool Bool Bool where
  state := bell
  norm_state := norm_bell
  alice s := chshRotatedMeasurement (oddCycleAliceAngle n s)
  bob t := chshRotatedMeasurement (oddCycleBobAngle n t)

private theorem correlation_oddCycleStrategy (n : ℕ) (s t : ZMod n) :
    (oddCycleStrategy n).correlation s t =
      cos (2 * (oddCycleAliceAngle n s - oddCycleBobAngle n t)) := by
  have hS : (oddCycleStrategy n).state = maxEntangled Bool := bell_eq_maxEntangled
  have hA : (oddCycleStrategy n).alice s = chshRotatedMeasurement (oddCycleAliceAngle n s) := rfl
  have hB : (oddCycleStrategy n).bob t = chshRotatedMeasurement (oddCycleBobAngle n t) := rfl
  rw [QuantumStrategy.correlation, hS, hA, hB, observable_chshRotatedMeasurement,
    observable_chshRotatedMeasurement, star_maxEntangled_dotProduct_kronecker_mulVec, mul_sub,
    cos_sub]
  simp only [Fintype.sum_bool, Fintype.card_bool, Matrix.of_apply, ite_true, Bool.true_eq_false,
    Bool.false_eq_true, ite_false]
  generalize cos (2 * oddCycleAliceAngle n s) = a
  generalize sin (2 * oddCycleAliceAngle n s) = b
  generalize cos (2 * oddCycleBobAngle n t) = c
  generalize sin (2 * oddCycleBobAngle n t) = d
  rw [show (-(a : ℂ) * -(c : ℂ) + -(b : ℂ) * -(d : ℂ) + (-(b : ℂ) * -(d : ℂ) + (a : ℂ) * c)) /
      ((2 : ℕ) : ℂ) = ((a * c + b * d : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]

/-- **Braunstein–Caves quantum value lower bound for the Odd-Cycle game**
([Cleve, Høyer, Toner, Watrous, §3.2][CleveHoyerTonerWatrous2004]): for odd `n ≥ 3`,
`oddCycleStrategy n` wins `oddCycleGame n` with probability `cos²(π / (4n))`. -/
theorem quantumWinProb_oddCycleGame_oddCycleStrategy {n : ℕ} [NeZero n]
    (hn : Odd n) (hn3 : 3 ≤ n) :
    (oddCycleGame n).quantumWinProb (oddCycleStrategy n) = cos (π / (4 * (n : ℝ))) ^ 2 := by
  have htriv : (oddCycleGame n).trivialWinProb = 1 / 2 := trivialWinProb_xorGame _ _
  have hsub := quantumWinProb_sub_trivialWinProb (isXORGame_oddCycleGame n) (oddCycleStrategy n)
  rw [htriv] at hsub
  have hn_pos : (0 : ℝ) < n := by positivity
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  -- Evaluate the question-weighted correlation sum by pulling back along `oddCycleQuestions`:
  have hprob (p : ZMod n × ZMod n) :
      ((oddCycleGame n).questions p).toReal =
        if p.1 = p.2 ∨ p.1 + 1 = p.2 then (2 * (n : ℝ))⁻¹ else 0 := by
    rcases p with ⟨s, t⟩
    change ((oddCycleQuestions n (s, t))).toReal = _
    rw [oddCycleQuestions, _root_.PMF.map_apply, tsum_fintype, Fintype.sum_prod_type]
    simp_rw [Fintype.sum_bool]
    simp only [Bool.cond_true, Bool.cond_false, Prod.mk.injEq, uniformOfFintype_apply,
      Fintype.card_prod, ZMod.card, Fintype.card_bool]
    by_cases hst : s = t
    · subst t
      have hne : s ≠ s + 1 := (zmod_add_one_ne_self hn3 s).symm
      simp only [true_or, ↓reduceIte]
      have hinner (x : ZMod n) :
          ((if s = x ∧ s = x + 1 then ((n * 2 : ℕ) : ENNReal)⁻¹ else 0) +
            (if s = x ∧ s = x then ((n * 2 : ℕ) : ENNReal)⁻¹ else 0)) =
          if x = s then ((n * 2 : ℕ) : ENNReal)⁻¹ else 0 := by
        by_cases hx : x = s
        · subst x
          simp [hne]
        · simp [Ne.symm hx, hx]
      simp_rw [hinner]
      rw [Finset.sum_ite_eq' Finset.univ s (fun _ => ((n * 2 : ℕ) : ENNReal)⁻¹)]
      simp only [Finset.mem_univ, ↓reduceIte, ENNReal.toReal_inv, Nat.cast_mul, Nat.cast_ofNat,
        ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofNat]
      ring
    · by_cases hsucc : s + 1 = t
      · subst t
        simp only [hst, false_or, ↓reduceIte]
        have hinner (x : ZMod n) :
            ((if s = x ∧ s + 1 = x + 1 then ((n * 2 : ℕ) : ENNReal)⁻¹ else 0) +
              (if s = x ∧ s + 1 = x then ((n * 2 : ℕ) : ENNReal)⁻¹ else 0)) =
            if x = s then ((n * 2 : ℕ) : ENNReal)⁻¹ else 0 := by
          by_cases hx : x = s
          · subst x
            simp [zmod_add_one_ne_self hn3 s]
          · simp [Ne.symm hx, hx]
        simp_rw [hinner]
        rw [Finset.sum_ite_eq' Finset.univ s (fun _ => ((n * 2 : ℕ) : ENNReal)⁻¹)]
        simp only [Finset.mem_univ, ↓reduceIte, ENNReal.toReal_inv, Nat.cast_mul, Nat.cast_ofNat,
          ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofNat]
        ring
      · simp only [hst, hsucc, or_self, ↓reduceIte]
        have hz : (∑ x : ZMod n,
            ((if s = x ∧ t = x + 1 then ((n * 2 : ℕ) : ENNReal)⁻¹ else 0) +
              (if s = x ∧ t = x then ((n * 2 : ℕ) : ENNReal)⁻¹ else 0))) = 0 := by
          refine Finset.sum_eq_zero fun x _ => ?_
          by_cases hx : s = x
          · subst hx
            have h1 : t ≠ s + 1 := Ne.symm hsucc
            have h2 : t ≠ s := Ne.symm hst
            simp [h1, h2]
          · simp [hx]
        rw [hz, ENNReal.toReal_zero]
  have hrow (s : ZMod n) :
      (∑ t : ZMod n, ((oddCycleGame n).questions (s, t)).toReal *
          (oddCycleGame n).xorCoeff s t * (oddCycleStrategy n).correlation s t) =
        (n : ℝ)⁻¹ * cos (π / (2 * (n : ℝ))) := by
    have hne : s + 1 ≠ s := zmod_add_one_ne_self hn3 s
    have hterm (t : ZMod n) :
        ((oddCycleGame n).questions (s, t)).toReal *
            (oddCycleGame n).xorCoeff s t * (oddCycleStrategy n).correlation s t =
          if t = s then (2 * (n : ℝ))⁻¹ * cos (π / (2 * (n : ℝ)))
          else if t = s + 1 then (2 * (n : ℝ))⁻¹ * cos (π / (2 * (n : ℝ)))
          else 0 := by
      rw [hprob (s, t), xorCoeff_oddCycleGame, correlation_oddCycleStrategy]
      by_cases hts : t = s
      · subst t
        simp only [↓reduceIte, true_or, decide_eq_false hne, signVal, Bool.false_eq_true]
        have hang : 2 * (oddCycleAliceAngle n s - oddCycleBobAngle n s) =
            -(π / (2 * (n : ℝ))) := by
          unfold oddCycleAliceAngle oddCycleBobAngle
          ring
        rw [hang, cos_neg]
        ring
      · by_cases ht1 : t = s + 1
        · subst t
          have hst_f : s ≠ s + 1 := hne.symm
          simp only [hne, hst_f, false_or, ↓reduceIte, decide_true, signVal]
          have : Fact (1 < n) := ⟨by omega⟩
          -- Show `-cos (2 * (α_s - β_{s+1})) = cos (π / (2n))`:
          have hcos : -cos (2 * (oddCycleAliceAngle n s - oddCycleBobAngle n (s + 1))) =
              cos (π / (2 * (n : ℝ))) := by
            by_cases hlt : s.val + 1 < n
            · have hval : (s + 1).val = s.val + 1 := by
                rw [ZMod.val_add, ZMod.val_one, Nat.mod_eq_of_lt hlt]
              have hang : 2 * (oddCycleAliceAngle n s - oddCycleBobAngle n (s + 1)) =
                  -(π - π / (2 * (n : ℝ))) := by
                unfold oddCycleAliceAngle oddCycleBobAngle
                rw [hval, Nat.cast_add, Nat.cast_one]
                field_simp
                ring
              rw [hang, cos_neg, cos_pi_sub, neg_neg]
            · have hsv : s.val = n - 1 := by
                have := s.val_lt
                omega
              have hval0 : (s + 1).val = 0 := by
                rw [ZMod.val_add, ZMod.val_one, hsv, show n - 1 + 1 = n by omega, Nat.mod_self]
              obtain ⟨k, hk⟩ := hn
              have hang : 2 * (oddCycleAliceAngle n s - oddCycleBobAngle n (s + 1)) =
                  -(π - π / (2 * (n : ℝ))) + (k : ℝ) * (2 * π) := by
                unfold oddCycleAliceAngle oddCycleBobAngle
                rw [hsv, hval0, Nat.cast_zero, mul_zero, sub_zero]
                have hn_sub : ((n - 1 : ℕ) : ℝ) = 2 * (k : ℝ) := by
                  rw [hk, show 2 * k + 1 - 1 = 2 * k by omega]
                  push_cast
                  rfl
                rw [hn_sub]
                have hn_eq : (n : ℝ) = 2 * (k : ℝ) + 1 := by exact_mod_cast hk
                field_simp
                rw [hn_eq]
                ring
              rw [hang, cos_add_nat_mul_two_pi _ k, cos_neg, cos_pi_sub, neg_neg]
          linear_combination (2 * (n : ℝ))⁻¹ * hcos
        · have h1 : s ≠ t := Ne.symm hts
          have h2 : s + 1 ≠ t := Ne.symm ht1
          simp [hts, ht1, h1, h2]
    simp_rw [hterm]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s)]
    simp only [↓reduceIte]
    have hs1_mem : s + 1 ∈ Finset.univ.erase s :=
      Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩
    rw [← Finset.add_sum_erase _ _ hs1_mem]
    simp only [hne, ↓reduceIte]
    have hrest : (∑ x ∈ (Finset.univ.erase s).erase (s + 1),
        if x = s then (2 * (n : ℝ))⁻¹ * cos (π / (2 * (n : ℝ)))
        else if x = s + 1 then (2 * (n : ℝ))⁻¹ * cos (π / (2 * (n : ℝ))) else 0) = 0 := by
      refine Finset.sum_eq_zero fun x hx => ?_
      have hx1 : x ≠ s + 1 := (Finset.mem_erase.mp hx).1
      have hx0 : x ≠ s := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
      simp [hx0, hx1]
    rw [hrest, add_zero]
    ring
  simp_rw [hrow] at hsub
  rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul,
    mul_inv_cancel_left₀ hn_ne] at hsub
  have hhalf : 1 / 2 + (1 / 2 : ℝ) * cos (π / (2 * (n : ℝ))) = cos (π / (4 * (n : ℝ))) ^ 2 := by
    have hdouble : π / (2 * (n : ℝ)) = 2 * (π / (4 * (n : ℝ))) := by ring
    rw [hdouble, cos_two_mul]
    ring
  linarith

/-- Entanglement strictly helps in every Odd-Cycle game (`n ≥ 3` odd):
`ω_c(oddCycleGame n) = 1 - 1 / (2n) < cos²(π / (4n)) ≤ ω_q(oddCycleGame n)`
([Cleve, Høyer, Toner, Watrous, §3.2][CleveHoyerTonerWatrous2004]). -/
theorem value_oddCycleGame_lt_quantumValue {n : ℕ} [NeZero n] (hn : Odd n) (hn3 : 3 ≤ n) :
    (oddCycleGame n).value < (oddCycleGame n).quantumValue := by
  have hn_real : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hsin_sq : sin (π / (4 * (n : ℝ))) ^ 2 ≤ (π / (4 * (n : ℝ))) ^ 2 := sin_sq_le_sq
  have hpi_sq : (π / (4 * (n : ℝ))) ^ 2 < 1 / (2 * (n : ℝ)) := by
    have h16 : π ^ 2 ≤ 16 := by nlinarith [pi_pos, pi_le_four]
    rw [div_pow, mul_pow, div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [h16, hn_real]
  have hcos_gt : 1 - 1 / (2 * (n : ℝ)) < cos (π / (4 * (n : ℝ))) ^ 2 := by
    have hsc := sin_sq_add_cos_sq (π / (4 * (n : ℝ)))
    linarith
  calc
    (oddCycleGame n).value = 1 - 1 / (2 * (n : ℝ)) := value_oddCycleGame hn hn3
    _ < cos (π / (4 * (n : ℝ))) ^ 2 := hcos_gt
    _ = (oddCycleGame n).quantumWinProb (oddCycleStrategy n) :=
      (quantumWinProb_oddCycleGame_oddCycleStrategy hn hn3).symm
    _ ≤ (oddCycleGame n).quantumValue :=
      (oddCycleGame n).quantumWinProb_le_quantumValue (oddCycleStrategy n)

end OddCycle

end TwoProverGame

end Cslib.PCP
