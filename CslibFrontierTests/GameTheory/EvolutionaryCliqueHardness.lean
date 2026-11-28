/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.GameTheory.Evolutionary.CliqueHardness
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Computational complexity of ESS: checked instances

Ordinary `module` client of `CslibFrontier.GameTheory.Evolutionary.CliqueHardness` exercising:

1. Nisan's clique game `cliqueESSGame` on `K₃` (`cliqueNum = 3`):
   * `k = 2 < 3`: the uniform strategy on `K₃` is an ESS (`Lemma 29.4`), pure `none` is not
     (`Lemma 29.6`), and an ESS exists;
   * `k = 3 = 3`: no ESS exists (`exists_isESS_cliqueESSGame_iff`), neither pure `none` nor the
     uniform clique strategy (`Lemma 29.7`);
   * `k = 4 > 3`: pure `none` is the unique ESS (`Lemmas 29.5` and `29.7`).
2. Non-clique graph `P₃` (path `0 - 1 - 2`, `cliqueNum = 2`, maximal clique `{0, 1}`):
   * Lemma 29.3 strict inequality off cliques: the uniform strategy over all three vertices earns
     `11 / 18 < 3 / 4 = 1 - 1 / (2 * 2)`, whereas the uniform strategy on `{0, 1}` achieves `3 / 4`;
   * Lemma 29.4: the uniform strategy on maximal clique `{0, 1}` is an ESS for `k = 1`.
3. Boundary cases of `cliqueESSGame`: empty vertex type `Empty` (`k = 1`, pure `none` is an ESS)
   and `k = 0` on `K₁` (showing `0 < k` cannot be dropped from `isESS_cliqueESSGame_pureNone_iff`).
4. Concrete `SymGameHasESS` and `SymGameIsESS` witnesses and model boundaries:
   * Hawks and Doves (`V = 2, C = 1`), whose payoff matrix is NOT symmetric (`matA ≠ matAᵀ`) yet
     forms a symmetric two-player game (`matB = matAᵀ`): belongs to `SymGameHasESS`, `[1, 0]`
     belongs to `SymGameIsESS`, `[0, 1]` does not, and malformed length `[1]` is rejected;
   * the `2 × 2` zero game has no ESS (`∉ SymGameHasESS`, `∉ SymGameIsESS`);
   * an asymmetric bimatrix game (`matB ≠ matAᵀ`) is rejected from `SymGameHasESS` and
     `SymGameIsESS` even when `toSymGame` has an ESS.
5. Ordinary `module` client access to `SymGameHasESS_npHard`, `SymGameHasESS_coNPHard`, and
   `SymGameIsESS_coNPHard` (Theorems 29.8 and 29.9).
-/

public section

namespace CslibFrontierTests.GameTheory.EvolutionaryCliqueHardness

open Cslib.Complexity Cslib.GameTheory Cslib.GameTheory.BimatrixCode Cslib.GameTheory.BimatrixGame
  Cslib.Logic.PL Matrix Turing.MultiTapeTM

/-! ### Nisan's game on `K₃` -/

/-- Complete graph `K₃` on `Fin 3`. -/
abbrev K3 : SimpleGraph (Fin 3) := ⊤

private theorem K3_cliqueNum : K3.cliqueNum = 3 := by
  simp [K3]

theorem K3_k2_uniform_isESS :
    (cliqueESSGame K3 2).IsESS (cliqueUniformStrategy (Finset.univ : Finset (Fin 3))) := by
  have hmax : Maximal (fun S : Finset (Fin 3) => K3.IsClique (S : Set (Fin 3))) Finset.univ :=
    ⟨fun _ _ _ _ h => h, fun _ _ _ => Finset.subset_univ _⟩
  exact isESS_cliqueESSGame_of_maximalClique K3 (by decide) hmax (by decide)

theorem K3_k2_pureNone_not_isESS :
    ¬ (cliqueESSGame K3 2).IsESS (Pi.single none 1) := by
  rw [isESS_cliqueESSGame_pureNone_iff K3 (by decide), K3_cliqueNum]
  decide

theorem K3_k3_no_isESS : ¬ ∃ s, (cliqueESSGame K3 3).IsESS s := by
  rw [exists_isESS_cliqueESSGame_iff K3 (by decide), K3_cliqueNum]
  decide

theorem K3_k3_uniform_not_isESS :
    ¬ (cliqueESSGame K3 3).IsESS (cliqueUniformStrategy (Finset.univ : Finset (Fin 3))) := by
  refine not_isESS_cliqueESSGame_of_cliqueNum_le K3 (by rw [K3_cliqueNum]) fun h => ?_
  have h0 := congrFun h none
  simp at h0

theorem K3_k4_pureNone_isESS :
    (cliqueESSGame K3 4).IsESS (Pi.single none 1) := by
  rw [isESS_cliqueESSGame_pureNone_iff K3 (by decide), K3_cliqueNum]
  decide

theorem K3_k4_unique_isESS {s : Option (Fin 3) → ℝ} (hs : (cliqueESSGame K3 4).IsESS s) :
    s = Pi.single none 1 := by
  by_contra hne
  exact not_isESS_cliqueESSGame_of_cliqueNum_le K3 (by rw [K3_cliqueNum]; decide) hne hs

/-! ### Non-clique graph `P₃` (`0 - 1 - 2`) -/

/-- The path graph `P₃` on `Fin 3` with edges `0 - 1` and `1 - 2` (non-edge `0 - 2`). -/
@[expose] def P3 : SimpleGraph (Fin 3) where
  Adj u v := (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) ∨ (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 1)
  symm := ⟨fun u v h => by
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp⟩
  loopless := ⟨fun u => by fin_cases u <;> decide⟩

instance : DecidableRel P3.Adj := fun u v => by
  dsimp only [P3]
  infer_instance

private theorem P3_clique01 : P3.IsClique (({0, 1} : Finset (Fin 3)) : Set (Fin 3)) := by
  intro u hu v hv huv
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hu hv
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact absurd rfl huv
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact absurd rfl huv

private theorem P3_maximal01 :
    Maximal (fun S : Finset (Fin 3) => P3.IsClique (S : Set (Fin 3))) {0, 1} := by
  refine ⟨P3_clique01, fun T hT hsub x hx => ?_⟩
  fin_cases x
  · decide
  · decide
  · exfalso
    have h0 : (0 : Fin 3) ∈ T := hsub (by decide)
    have hadj : P3.Adj 0 2 := hT h0 hx (by decide)
    simp [P3] at hadj

private theorem P3_cliqueNum : P3.cliqueNum = 2 := by
  refine le_antisymm ?_ ?_
  · by_contra hgt
    have h3 : 3 ≤ P3.cliqueNum := by omega
    obtain ⟨S, hS⟩ := P3.exists_isNClique_cliqueNum
    have hcard : S.card = 3 := le_antisymm (by simpa using S.card_le_univ) (hS.card_eq ▸ h3)
    have huniv : S = Finset.univ := Finset.eq_univ_of_card S (by simpa using hcard)
    have hadj : P3.Adj 0 2 := hS.isClique (by simp [huniv]) (by simp [huniv]) (by decide)
    simp [P3] at hadj
  · simpa using P3_clique01.card_le_cliqueNum

/-- Lemma 29.3 equality on the maximum clique `{0, 1}` of `P₃`. -/
theorem P3_uniform01_payoff :
    (cliqueESSGame P3 1).payoff₁ (cliqueUniformStrategy ({0, 1} : Finset (Fin 3)))
      (cliqueUniformStrategy ({0, 1} : Finset (Fin 3))) = 3 / 4 := by
  have hm : IsMixedStrategy (cliqueUniformStrategy ({0, 1} : Finset (Fin 3))) :=
    isMixedStrategy_cliqueUniformStrategy (by decide)
  have hN : P3.IsNClique P3.cliqueNum ({0, 1} : Finset (Fin 3)) :=
    ⟨P3_clique01, by rw [P3_cliqueNum]; decide⟩
  have heq := (payoff₁_self_cliqueESSGame_eq_iff P3 1 hm (cliqueUniformStrategy_none _)).2
    ⟨{0, 1}, hN, rfl⟩
  rw [heq, P3_cliqueNum]
  norm_num

/-- Lemma 29.3 strict inequality off cliques: the uniform distribution on all three vertices of `P₃`
earns `11 / 18 < 3 / 4 = 1 - 1 / (2 * P3.cliqueNum)`. -/
theorem P3_uniformAll_payoff_lt :
    (cliqueESSGame P3 1).payoff₁ (cliqueUniformStrategy (Finset.univ : Finset (Fin 3)))
      (cliqueUniformStrategy (Finset.univ : Finset (Fin 3))) <
      1 - 1 / (2 * (P3.cliqueNum : ℝ)) := by
  have hm : IsMixedStrategy (cliqueUniformStrategy (Finset.univ : Finset (Fin 3))) :=
    isMixedStrategy_cliqueUniformStrategy (by decide)
  have hle := payoff₁_self_cliqueESSGame_le P3 1 hm (cliqueUniformStrategy_none _)
  refine lt_of_le_of_ne hle fun heq => ?_
  obtain ⟨C, hC, hEq⟩ :=
    (payoff₁_self_cliqueESSGame_eq_iff P3 1 hm (cliqueUniformStrategy_none _)).1 heq
  have hmem (v : Fin 3) : v ∈ C := by
    by_contra hv
    have hv' := congrFun hEq (some v)
    simp [hv] at hv'
  have hadj : P3.Adj 0 2 := hC.isClique (hmem 0) (hmem 2) (by decide)
  simp [P3] at hadj

/-- Lemma 29.4 on maximal clique `{0, 1}` of `P₃` with `k = 1`. -/
theorem P3_uniform01_isESS :
    (cliqueESSGame P3 1).IsESS (cliqueUniformStrategy ({0, 1} : Finset (Fin 3))) :=
  isESS_cliqueESSGame_of_maximalClique P3 (by decide) P3_maximal01 (by decide)

/-! ### Boundary cases of `cliqueESSGame` -/

/-- Empty vertex type: `cliqueNum = 0 < 1`, and pure `none` is an ESS. -/
theorem emptyGraph_pureNone_isESS :
    (cliqueESSGame (⊥ : SimpleGraph Empty) 1).IsESS (Pi.single none 1) := by
  rw [isESS_cliqueESSGame_pureNone_iff (⊥ : SimpleGraph Empty) (by decide)]
  have h0 : (⊥ : SimpleGraph Empty).cliqueNum = 0 :=
    Nat.eq_zero_of_le_zero ((⊥ : SimpleGraph Empty).cliqueNum_le_natCard.trans_eq (by simp))
  omega

/-- Boundary `k = 0`: on `K₁`, `1 - 1 / (2 * 0 : ℝ) = 1`, so pure `none` is an ESS even though
`¬ (K₁.cliqueNum < 0)`, confirming `0 < k` cannot be dropped from
`isESS_cliqueESSGame_pureNone_iff`. -/
theorem K1_k0_pureNone_isESS :
    (cliqueESSGame (⊤ : SimpleGraph (Fin 1)) 0).IsESS (Pi.single none 1) := by
  rw [isESS_iff_forall_lt_or]
  refine ⟨isMixedStrategy_single none, fun t ht hne => Or.inr ⟨?_, ?_⟩⟩
  · simp only [payoff₁_eq_dotProduct, dotProduct, mulVec, Fintype.sum_option, Fin.sum_univ_one,
      Pi.single_apply, reduceCtorEq, ↓reduceIte, mul_one, mul_zero, add_zero, zero_mul,
      cliqueESSGame_A_none_right]
    have hsum := ht.sum_eq_one
    rw [Fintype.sum_option, Fin.sum_univ_one] at hsum
    linarith
  · simp only [payoff₁_eq_dotProduct, dotProduct, mulVec, Fintype.sum_option, Fin.sum_univ_one,
      Pi.single_apply, reduceCtorEq, ↓reduceIte, add_zero, zero_mul,
      cliqueESSGame_A_none_left, cliqueESSGame_A_none_right, cliqueESSGame_A_some_some]
    have hsum := ht.sum_eq_one
    rw [Fintype.sum_option, Fin.sum_univ_one] at hsum
    have ht1_ne : t (some 0) ≠ 0 := fun h0 => hne (funext fun x => by
      cases x with
      | none => simp only [Pi.single_eq_same]; linarith
      | some v => fin_cases v; simpa using h0)
    have hsq : 0 < t (some 0) ^ 2 := sq_pos_of_ne_zero ht1_ne
    have h0 : (0 : ℝ) = 1 / (2 * (0 : ℕ)) := by norm_num
    nlinarith

/-! ### Concrete `SymGameHasESS` and `SymGameIsESS` witnesses and model boundaries -/

/-- Hawks and Doves (`V = 2, C = 1`) as a `BimatrixCode`: `matA ≠ matAᵀ`, yet `matB = matAᵀ`. -/
def hawkDoveCode : BimatrixCode :=
  ⟨[[1 / 2, 2], [0, 1]], [[1 / 2, 0], [2, 1]]⟩

/-- The `2 × 2` zero game as a `BimatrixCode`. -/
def zeroGameCode : BimatrixCode :=
  ⟨[[0, 0], [0, 0]], [[0, 0], [0, 0]]⟩

/-- An asymmetric bimatrix game (`matB ≠ matAᵀ`) whose player-1 matrix has an ESS. -/
def asymGameCode : BimatrixCode :=
  ⟨[[2, 0], [0, 2]], [[0, 1], [0, 0]]⟩

theorem hawkDoveCode_isSymmetric : hawkDoveCode.IsSymmetric := by
  refine ⟨⟨by decide, by decide, rfl, ?_, ?_⟩, rfl, fun i j => ?_⟩
  · intro r hr; simp only [hawkDoveCode, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> rfl
  · intro r hr; simp only [hawkDoveCode, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> rfl
  · fin_cases i <;> fin_cases j <;> norm_num [hawkDoveCode]

private def hawkDoveEquiv : Fin hawkDoveCode.rows ≃ Fin 2 :=
  finCongr (rfl : hawkDoveCode.rows = 2)

private theorem hawkDoveCode_A_eq (i j : Fin hawkDoveCode.rows) :
    hawkDoveCode.toSymGame.A i j = (hawkDove 2 1).A (hawkDoveEquiv i) (hawkDoveEquiv j) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [toSymGame, hawkDoveCode, hawkDove_A, hawkDoveEquiv, finCongr, Equiv.coe_fn_mk,
      Fin.cast]

theorem hawkDoveCode_mem_SymGameHasESS : hawkDoveCode ∈ SymGameHasESS := by
  refine ⟨hawkDoveCode_isSymmetric, (![1, 0] : Fin 2 → ℝ) ∘ hawkDoveEquiv,
    (isESS_relabel hawkDoveEquiv hawkDoveCode_A_eq).2
      ((isESS_hawkDove_iff_of_lt (by norm_num) (by norm_num)).2 rfl)⟩

theorem hawkDoveCode_hawk_mem_SymGameIsESS :
    (⟨hawkDoveCode, [1, 0]⟩ : SymGameStrategyInstance) ∈ SymGameIsESS := by
  refine ⟨hawkDoveCode_isSymmetric, rfl, ?_⟩
  change hawkDoveCode.toSymGame.IsESS (strategyVec [1, 0])
  have hvec : strategyVec (n := hawkDoveCode.rows) [1, 0] =
      (![1, 0] : Fin 2 → ℝ) ∘ hawkDoveEquiv := by
    funext i; fin_cases i <;> simp [strategyVec, hawkDoveEquiv, finCongr, Fin.cast]
  rw [hvec, isESS_relabel hawkDoveEquiv hawkDoveCode_A_eq]
  exact (isESS_hawkDove_iff_of_lt (by norm_num) (by norm_num)).2 rfl

theorem hawkDoveCode_dove_notMem_SymGameIsESS :
    (⟨hawkDoveCode, [0, 1]⟩ : SymGameStrategyInstance) ∉ SymGameIsESS := by
  rintro ⟨-, -, hESS⟩
  change hawkDoveCode.toSymGame.IsESS (strategyVec [0, 1]) at hESS
  have hvec : strategyVec (n := hawkDoveCode.rows) [0, 1] =
      (![0, 1] : Fin 2 → ℝ) ∘ hawkDoveEquiv := by
    funext i; fin_cases i <;> simp [strategyVec, hawkDoveEquiv, finCongr, Fin.cast]
  rw [hvec, isESS_relabel hawkDoveEquiv hawkDoveCode_A_eq,
    isESS_hawkDove_iff_of_lt (by norm_num) (by norm_num)] at hESS
  have h0 := congrFun hESS 0
  norm_num at h0

/-- Length boundary: a truncated strategy `[1]` is rejected even though `strategyVec [1] = ![1, 0]`
would be an ESS. -/
theorem hawkDoveCode_short_notMem_SymGameIsESS :
    (⟨hawkDoveCode, [1]⟩ : SymGameStrategyInstance) ∉ SymGameIsESS := by
  rintro ⟨-, hlen, -⟩
  simp [hawkDoveCode, rows] at hlen

private def zeroGameEquiv : Fin zeroGameCode.rows ≃ Fin 2 :=
  finCongr (rfl : zeroGameCode.rows = 2)

theorem zeroGameCode_notMem_SymGameHasESS : zeroGameCode ∉ SymGameHasESS := by
  rintro ⟨-, s, hs⟩
  have hA : ∀ i j : Fin zeroGameCode.rows,
      zeroGameCode.toSymGame.A i j =
        (⟨0, 0⟩ : BimatrixGame (Fin 2) (Fin 2)).A (zeroGameEquiv i) (zeroGameEquiv j) := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [toSymGame, zeroGameCode]
  have hs' : (⟨0, 0⟩ : BimatrixGame (Fin 2) (Fin 2)).IsESS (s ∘ zeroGameEquiv.symm) :=
    (isESS_relabel zeroGameEquiv hA).1 (by
      have heq : (s ∘ zeroGameEquiv.symm) ∘ zeroGameEquiv = s := funext fun a => by simp
      rwa [heq])
  have hex : ∃ t, (⟨0, 0⟩ : BimatrixGame (Fin 2) (Fin 2)).IsESS t := ⟨_, hs'⟩
  rw [exists_isESS_fin_two_iff] at hex
  rcases hex with h | h <;> exact h rfl

/-- Symmetry boundary: an asymmetric bimatrix game (`matB ≠ matAᵀ`) is rejected from
`SymGameHasESS` even though `toSymGame` has an ESS. -/
theorem asymGameCode_notMem_SymGameHasESS : asymGameCode ∉ SymGameHasESS := by
  rintro ⟨⟨-, -, hsym⟩, -⟩
  have h01 := hsym ⟨0, by decide⟩ ⟨1, by decide⟩
  norm_num [asymGameCode] at h01

/-! ### Client access to the complexity headlines -/

theorem client_SymGameHasESS_npHard : NPHard encBimatrix SymGameHasESS :=
  SymGameHasESS_npHard

theorem client_SymGameHasESS_coNPHard : coNPHard encBimatrix SymGameHasESS :=
  SymGameHasESS_coNPHard

theorem client_SymGameIsESS_coNPHard : coNPHard encSymGameStrategyInstance SymGameIsESS :=
  SymGameIsESS_coNPHard

end CslibFrontierTests.GameTheory.EvolutionaryCliqueHardness
