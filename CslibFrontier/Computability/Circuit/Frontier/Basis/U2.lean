/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Basis.U2.BranchingProgram
public import CslibFrontier.Computability.Circuit.Frontier.Basis.U2.Compression
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Gaussian.CostLambda
public import CslibFrontier.Computability.Circuit.Frontier.Nondeterministic
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Logb
import CslibFrontier.Foundations.Data.Nat.Card
import CslibFrontier.Foundations.Data.Nat.IntermediateValue
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Parametric and unconditional `4.6362 n` `U₂` circuit lower bounds

Combines the saturated `U₂` compression (`Basis.U2.Compression`), the `3`-state pair-compressed
branching program (`Basis.U2.BranchingProgram`), the `7/8` cubic matching theorem
(`Layouts.WeightedMatching`), and the unconditional Gaussian two-cap bound
`Gaussian.u2CubicPairBound_gaussian` (`Layouts.Gaussian.CostLambda`) to establish:

1. **Parametric `U₂` frontier reductions** from any `U2CubicPairBound p B_pair` for nondeterministic
   (`∀ k`), worst-case, average-case (`RectangleBias`), and quadratic-form correlation models.
2. **Unconditional `(4.6362 - ε) n` (`46362 / 10000`) `U₂` circuit lower bounds** across
   nondeterministic, worst-case, and average-case circuits over every `U₂` basis
   (`Interpretation.IsU2`), with specializations to `Boolean.DeMorgan` and `Boolean`.

Here `U₂` restricts binary gates to polarized `AND` operations and excludes `XOR` and `XNOR`;
the `Boolean` specialization is the library's `AND`/`OR`/`NOT` basis, with constants.
"Unconditional" refers to the proved numerical layout bound: the worst-case and average-case
reductions still require `DenseRectangleFree` and `RectangleBias` witnesses, respectively.

The `U₂` pair-compressed `4.6362 n` frontier lower bounds and parametric `U2CubicPairBound`
reductions are original to this library.

## Main results

* `Cslib.Circuits.Frontier.eventually_lt_innerSize_u2_nondeterministic`,
  `Cslib.Circuits.Frontier.eventually_lt_innerSize_u2`,
  `Cslib.Circuits.Frontier.eventually_agreement_le_u2`,
  `Cslib.Circuits.Frontier.eventually_abs_correlation_quadForm_le_u2`: parametric `U₂`
  nondeterministic, worst-case, average-case, and quadratic-form correlation reductions.
* `Cslib.Circuits.Frontier.eventually_46362_div_10000_sub_mul_lt_innerSize_u2_nondeterministic`,
  `Cslib.Circuits.Frontier.eventually_46362_div_10000_sub_mul_lt_innerSize_u2`,
  `Cslib.Circuits.Frontier.eventually_46362_div_10000_sub_mul_lt_innerSize_deMorgan`,
  `Cslib.Circuits.Frontier.eventually_46362_div_10000_sub_mul_lt_innerSize_boolean`: unconditional
  `(4.6362 - ε) n` nondeterministic and worst-case `U₂`, De Morgan, and Boolean lower bounds.
* `Cslib.Circuits.Frontier.eventually_agreement_le_u2_46362`,
  `Cslib.Circuits.Frontier.eventually_agreement_le_deMorgan_46362`,
  `Cslib.Circuits.Frontier.eventually_agreement_le_boolean_46362`: unconditional `(4.6362 - ε) n`
  average-case `U₂`, De Morgan, and Boolean lower bounds.
-/

public section

namespace Cslib.Circuits.Frontier

open Set Filter Asymptotics Matrix Cslib.Circuits.Frontier.Compiler

universe v


private theorem read_hiddenNetwork_zero {σ : Signature} {n m_out : ℕ}
    (c : Circuit σ n m_out) (I : Interpretation σ Bool) (Acc : Fin m_out → Set Bool) :
    (hiddenNetwork (k := 0) c I Acc).read = (network c I Acc).read := by
  ext i
  simp only [hiddenNetwork, Network.read, Network.readIn, Network.hide, Network.reindex,
    mem_ofPred_eq, mem_univ, true_and, Equiv.symm_symm]
  have hfin : (@finSumFinEquiv n 0) (.inl i) = i := Fin.ext rfl
  rw [hfin]

/-- Combine `exists_u2_saturated`, `Multigraph.exists_isMatching_seven_eighths`, and
`U2CubicPairBound p B_pair` to construct `U2PairData` for any `U₂` circuit with uniform constant
`C₀` depending only on `(p, B_pair, ξ)`. -/
private theorem exists_u2PairData_of_u2CubicPairBound {p B_pair : ℝ} (_hp : 0 < p)
    (hBp_le : B_pair ≤ 2 * p) (hbound : U2CubicPairBound p B_pair)
    (hδA : 2 * p - B_pair ≤ (7 / 8) * B_pair + (1 / 8) * (2 * p)) {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ C₀ : ℝ, ∀ {n k : ℕ} {σ : Signature.{v}} {I : Interpretation σ Bool},
      I.IsU2 → ∀ (Acc : Set Bool) (c : Circuit σ (n + k) 1),
        ∃ D : U2PairData c I, ∀ s_idx : ℕ,
          let P := D.Q.quotient.pairNodeVerts D.M D.M D.score (D.pairLay.initial s_idx)
          ((D.Q.quotient.edgeCut P).ncard : ℝ) -
              (2 - Real.logb 2 3) *
                ((D.Q.quotient.activeCleanPairs D.M D.M D.score P).ncard : ℝ) ≤
            ((7 / 8) * B_pair + (1 / 8) * (2 * p)) * c.innerSize -
              (((7 / 8) * B_pair + (1 / 8) * (2 * p)) - (2 * p - B_pair)) *
                (hiddenNetwork c I fun _ => Acc).read.ncard +
              ξ * Nat.card (Vertex c) + C₀ := by
  classical
  obtain ⟨N₀, hN₀⟩ := hbound ξ hξ
  set δ_dirty := 2 * p - B_pair
  set A := (7 / 8) * B_pair + (1 / 8) * (2 * p)
  have hδ0 : 0 ≤ δ_dirty := by dsimp [δ_dirty]; linarith
  have hA_sub : 0 ≤ A - δ_dirty := by linarith
  let C₀ : ℝ := 3 * (max 1 N₀ : ℝ) + |A| + 1
  refine ⟨C₀, fun {n k σ I} hU2 Acc c => ?_⟩
  obtain ⟨Q, dirty, hsat, hdirty_sub, hgt1⟩ := exists_u2_saturated c hU2 (fun _ => Acc)
  set R := (hiddenNetwork c I fun _ => Acc).read.ncard
  have hfan : c.FanInAtMost 2 := hU2.fanInAtMost_two c
  have hR_le : R ≤ c.innerSize + 1 := by
    have h1 : R ≤ (network c I fun _ => Acc).read.ncard :=
      (Network.ncard_read_hide_le _).trans (Network.ncard_read_reindex _ _).le
    have h2 := cycleRank_add_ncard_read_le I (fun _ => Acc) hfan (connected c)
    omega
  have hblk_le_V : Nat.card Q.blocks ≤ Nat.card (Vertex c) := by
    refine Nat.card_le_card_of_injective
      (fun B : Q.blocks => B.val.head (Q.ne_nil B.val B.property))
      fun B₁ B₂ h => Subtype.ext ?_
    dsimp only at h
    have hm : B₁.val.head (Q.ne_nil B₁.val B₁.property) ∈ B₂.val := h ▸ List.head_mem _
    exact Q.eq_of_mem B₁.val B₁.property B₂.val B₂.property _ (List.head_mem _) hm
  rcases le_or_gt (Nat.card Q.blocks) (max 1 N₀) with hsmall | hlarge
  · let score : Q.external → ℝ := fun _ => 0
    obtain ⟨pairLay, -⟩ :=
      Layout.exists_threshold (fun _ : Q.quotient.PairNode ∅ ∅ score => (0 : ℝ))
    refine ⟨U2PairData.mk Q hsat ∅ (fun ⟨_, h⟩ => h.elim) (fun _ h => h.elim)
      (fun _ h => h.elim) score pairLay, fun s_idx => ?_⟩
    dsimp only
    set P := Q.quotient.pairNodeVerts ∅ ∅ score (pairLay.initial s_idx)
    have hact0 : Q.quotient.activeCleanPairs ∅ ∅ score P = ∅ := by
      ext e; simp [Multigraph.activeCleanPairs]
    have hdegQ : Q.quotient.MaxDegreeLE 3 := fun B => by
      rw [Q.ncard_incidenceSet_quotient B]
      exact Q.ncard_edgeCut_le B.val B.property
    have hcut_le : (Q.quotient.edgeCut P).ncard ≤ 3 * max 1 N₀ :=
      calc (Q.quotient.edgeCut P).ncard
          ≤ (Q.quotient.touching P).ncard := ncard_le_ncard (Q.quotient.edgeCut_subset_touching P)
        _ ≤ 3 * P.ncard := Q.quotient.ncard_touching_le hdegQ P
        _ ≤ 3 * Nat.card Q.blocks := Nat.mul_le_mul_left 3 (ncard_le_card P)
        _ ≤ 3 * max 1 N₀ := Nat.mul_le_mul_left 3 hsmall
    rw [hact0, ncard_empty, Nat.cast_zero, mul_zero, sub_zero]
    have hcutR : ((Q.quotient.edgeCut P).ncard : ℝ) ≤ 3 * (max 1 N₀ : ℝ) := by
      exact_mod_cast hcut_le
    have hRR : (R : ℝ) ≤ c.innerSize + 1 := by exact_mod_cast hR_le
    have hs0 : (0 : ℝ) ≤ c.innerSize := Nat.cast_nonneg _
    have hxi0 : 0 ≤ ξ * Nat.card (Vertex c) := by positivity
    have hlow : -A ≤ A * c.innerSize - (A - δ_dirty) * R := by
      have hm := mul_le_mul_of_nonneg_left hRR hA_sub
      nlinarith
    dsimp only [C₀]
    linarith [le_abs_self A]
  · have htwo : 1 < Nat.card Q.blocks := (le_max_left 1 N₀).trans_lt hlarge
    have hN_lt : N₀ < Nat.card Q.blocks := (le_max_right 1 N₀).trans_lt hlarge
    obtain ⟨hclean3, hread_cnt, hdirty_cnt⟩ := hgt1 htwo
    have h3_all : ∀ B : Q.blocks, (Q.quotient.incidenceSet B).ncard = 3 :=
      hsat.ncard_incidenceSet_quotient (connected c) htwo
    obtain ⟨M_full, hM_full, -, hcov_nat⟩ := Q.quotient.exists_isMatching_seven_eighths
      Q.quotient_loopless hsat.injective_ends_quotient h3_all
    let M_clean : Set Q.external :=
      {e ∈ M_full | (Q.quotient.src e).val ∉ dirty ∧ (Q.quotient.tgt e).val ∉ dirty}
    have hM_clean : Q.quotient.IsMatching M_clean := fun _ h₁ _ h₂ => hM_full h₁.1 h₂.1
    have hclean_pair : ∀ e ∈ M_clean, CleanBlock3 I {v | v ∈ (Q.quotient.src e).val} ∧
        CleanBlock3 I {v | v ∈ (Q.quotient.tgt e).val} :=
      fun e he => ⟨hclean3 _ (Q.quotient.src e).property he.2.1,
          hclean3 _ (Q.quotient.tgt e).property he.2.2⟩
    have hdrop_le : M_full.ncard ≤ M_clean.ncard + dirty.card := by
      have := Fintype.ofFinite (Edge c)
      let M_drop : Set Q.external := M_full \ M_clean
      have hwit : ∀ e ∈ M_drop, ∃ b : dirty,
          (⟨b.val, hdirty_sub b.property⟩ : Q.blocks) = Q.quotient.src e ∨
            (⟨b.val, hdirty_sub b.property⟩ : Q.blocks) = Q.quotient.tgt e := by
        rintro e ⟨heM, hnot⟩
        by_cases hs : (Q.quotient.src e).val ∈ dirty
        · exact ⟨⟨(Q.quotient.src e).val, hs⟩, Or.inl rfl⟩
        · have ht : (Q.quotient.tgt e).val ∈ dirty :=
            by_contra fun ht => hnot ⟨heM, hs, ht⟩
          exact ⟨⟨(Q.quotient.tgt e).val, ht⟩, Or.inr rfl⟩
      choose b_of hb_end using fun e : M_drop => hwit e.val e.property
      have hinj : Function.Injective b_of := by
        intro e₁ e₂ heq
        have hBeq : (⟨(b_of e₁).val, hdirty_sub (b_of e₁).property⟩ : Q.blocks) =
            ⟨(b_of e₂).val, hdirty_sub (b_of e₂).property⟩ := by rw [heq]
        by_contra hne
        have hmem₁ : (⟨(b_of e₁).val, hdirty_sub (b_of e₁).property⟩ : Q.blocks) ∈
            ({Q.quotient.src e₁.val, Q.quotient.tgt e₁.val} : Set Q.blocks) := by
          rcases hb_end e₁ with h | h <;> simp [h]
        have hmem₂ : (⟨(b_of e₁).val, hdirty_sub (b_of e₁).property⟩ : Q.blocks) ∈
            ({Q.quotient.src e₂.val, Q.quotient.tgt e₂.val} : Set Q.blocks) := by
          rw [hBeq]; rcases hb_end e₂ with h | h <;> simp [h]
        exact disjoint_left.mp (hM_full e₁.property.1 e₂.property.1 fun h => hne (Subtype.ext h))
          hmem₁ hmem₂
      have hcard_drop : (M_full \ M_clean).ncard ≤ dirty.card := by
        have h1 := Nat.card_le_card_of_injective b_of hinj
        rwa [Nat.card_coe_set_eq, Nat.card_eq_finsetCard] at h1
      have hpart := ncard_sdiff_add_ncard_of_subset (fun _ he => he.1 : M_clean ⊆ M_full)
      omega
    obtain ⟨score, pairLay, hσ⟩ := hN₀ Q.blocks Q.external Q.quotient Q.quotient_loopless
      hsat.injective_ends_quotient h3_all hN_lt M_clean M_clean hM_clean (Subset.refl _)
    refine ⟨U2PairData.mk Q hsat M_clean (fun _ => h3_all) hM_clean hclean_pair score pairLay,
      fun s_idx => ?_⟩
    dsimp only
    refine (hσ s_idx).trans ?_
    have hcovR : 7 * (Nat.card Q.blocks : ℝ) ≤ 16 * (M_full.ncard : ℝ) := by exact_mod_cast hcov_nat
    have hdropR : (M_full.ncard : ℝ) ≤ (M_clean.ncard : ℝ) + (dirty.card : ℝ) := by
      exact_mod_cast hdrop_le
    have hreadR : (Nat.card Q.blocks : ℝ) + 2 * R ≤ 2 * c.innerSize := by exact_mod_cast hread_cnt
    have hdirtyR : (Nat.card Q.blocks : ℝ) + 2 * (dirty.card : ℝ) ≤ 2 * c.innerSize + 2 := by
      exact_mod_cast hdirty_cnt
    have hblkR : (Nat.card Q.blocks : ℝ) ≤ Nat.card (Vertex c) := by exact_mod_cast hblk_le_V
    set h : ℝ := (Nat.card Q.blocks : ℝ)
    set m : ℝ := (M_clean.ncard : ℝ)
    set d : ℝ := (dirty.card : ℝ)
    have hm_lo : (7 / 16) * h - d ≤ m := by linarith
    have hcost_eq : (h - 2 * m) * p + m * B_pair = h * p - m * δ_dirty := by
      dsimp only [δ_dirty]; ring
    have hm_mul := mul_le_mul_of_nonneg_right hm_lo hδ0
    have hp_id : p - (7 / 16) * δ_dirty = A / 2 := by
      dsimp only [A, δ_dirty]; ring
    have hterm1 := mul_le_mul_of_nonneg_left (show h ≤ 2 * c.innerSize - 2 * R by linarith)
      (by linarith : 0 ≤ (A - δ_dirty) / 2)
    have hterm2 := mul_le_mul_of_nonneg_left hdirtyR (by linarith : 0 ≤ δ_dirty / 2)
    have hxi_le : ξ * h ≤ ξ * Nat.card (Vertex c) := mul_le_mul_of_nonneg_left hblkR hξ.le
    have hC0_ge : δ_dirty ≤ C₀ := by
      have hN0_pos : (0 : ℝ) ≤ max 1 (N₀ : ℝ) := by positivity
      dsimp only [C₀]; linarith [le_abs_self A, hN0_pos]
    have hid1 : h * p - (7 / 16 * h - d) * δ_dirty = A / 2 * h + δ_dirty * d := by
      rw [← hp_id]
      ring
    have hid2 : (A - δ_dirty) / 2 * (2 * (c.innerSize : ℝ) - 2 * R) +
        δ_dirty / 2 * (2 * (c.innerSize : ℝ) + 2) =
        A * c.innerSize - (A - δ_dirty) * R + δ_dirty := by ring
    linarith

private lemma u2_one_sub_mul_min_nonneg {A ε : ℝ} (hA : 0 < A) :
    0 ≤ 1 - A * min ε (1 / A) := by
  have h := mul_le_mul_of_nonneg_left (min_le_right ε (1 / A)) hA.le
  rw [mul_one_div_cancel hA.ne'] at h
  linarith

private lemma u2_vertex_bounds {n m : ℕ} {σ : Signature.{v}} {I : Interpretation σ Bool}
    (hU2 : I.IsU2) (c : Circuit σ m 1) {M μ₀ : ℝ} (hM : 0 ≤ M) (hμ₀ : 0 < μ₀)
    (hs : (c.innerSize : ℝ) ≤ M * n) :
    let ξ := μ₀ / (8 * (4 * M + 4))
    1 ≤ Nat.card (Vertex c) ∧
      ξ * Nat.card (Vertex c) ≤ (μ₀ / 8) * n + 3 * ξ ∧
      Real.logb 2 (Nat.card (Vertex c)) ≤ Real.log (4 * M * n + 4) / Real.log 2 := by
  intro ξ
  have hξ : 0 < ξ := by positivity
  have hV_pos : 1 ≤ Nat.card (Vertex c) := by
    have : Nonempty (Vertex c) := ⟨.output 0⟩
    exact Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
  have hV_le : (Nat.card (Vertex c) : ℝ) ≤ 4 * M * n + 3 := by
    have h1 : Nat.card (Vertex c) ≤ 2 * 2 * c.innerSize + 3 * 1 :=
      card_vertex_le (hU2.fanInAtMost_two c)
    have h2 : (Nat.card (Vertex c) : ℝ) ≤ 4 * c.innerSize + 3 := by exact_mod_cast h1
    linarith
  have hxiV : ξ * Nat.card (Vertex c) ≤ (μ₀ / 8) * n + 3 * ξ := by
    have h1 := mul_le_mul_of_nonneg_left hV_le hξ.le
    have h2 : ξ * (4 * M) ≤ μ₀ / 8 := by
      dsimp only [ξ]
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have h3 := mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg (α := ℝ) n)
    linarith
  have hlogV : Real.logb 2 (Nat.card (Vertex c)) ≤ Real.log (4 * M * n + 4) / Real.log 2 :=
    div_le_div_of_nonneg_right
      (Real.log_le_log (Nat.cast_pos.mpr hV_pos) (by linarith only [hV_le]))
      (Real.log_pos one_lt_two).le
  exact ⟨hV_pos, hxiV, hlogV⟩

private lemma u2_max_sup_le {A δ_dirty ε' s ξV C₀ : ℝ} {n R U K : ℕ}
    (hA : 0 < A) (hδ0 : 0 ≤ δ_dirty) (hA_sub : 0 ≤ A - δ_dirty) (h1mAε : 0 ≤ 1 - A * ε')
    (hK_pos : 1 ≤ K) (hcompl : (R : ℝ) + U = n) (hu : 2 ^ U ≤ K)
    (hs : s ≤ (1 + (1 - δ_dirty) / A - ε') * n) (hξV : 0 ≤ ξV) :
    max 0 (A * s - (A - δ_dirty) * R + ξV + C₀) ≤
      (1 - A * ε') * n + A * Real.logb 2 K + ξV + |C₀| := by
  have hunread_log : (U : ℝ) ≤ Real.logb 2 K := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by exact_mod_cast hK_pos), Real.rpow_natCast]
    exact_mod_cast hu
  have hR_lo : (n : ℝ) - Real.logb 2 K ≤ R := by linarith
  have hmain_id : A * (1 + (1 - δ_dirty) / A - ε') * n - (A - δ_dirty) * n =
      (1 - A * ε') * n := by
    field_simp
    ring
  have hlogK0 : 0 ≤ Real.logb 2 K :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast hK_pos)
  refine max_le (by positivity) ?_
  have h1 := mul_le_mul_of_nonneg_left hs hA.le
  have h2 := mul_le_mul_of_nonneg_left hR_lo hA_sub
  have h3 : (A - δ_dirty) * Real.logb 2 K ≤ A * Real.logb 2 K :=
    mul_le_mul_of_nonneg_right (by linarith) hlogK0
  linarith [le_abs_self C₀]

/-- **Parametric `U₂` nondeterministic frontier lower bound.** Under `U2CubicPairBound p B_pair`
with `0 < p`, `0 < B_pair ≤ 2 p`, and `δ_dirty := 2 p - B_pair ≤ A := (7/8) B_pair + (1/8)(2p)`,
every nondeterministic circuit over a `U₂` basis deciding dense `K_n`-rectangle-free sets `S_n`
with any number `k` of witness inputs requires more than `(1 + (1 - δ_dirty) / A - ε) n` inner
gates. -/
theorem eventually_lt_innerSize_u2_nondeterministic {p B_pair : ℝ} (hp : 0 < p)
    (hBp : 0 < B_pair) (hBp_le : B_pair ≤ 2 * p) (hbound : U2CubicPairBound p B_pair)
    (hδA : 2 * p - B_pair ≤ (7 / 8) * B_pair + (1 / 8) * (2 * p))
    {S : ∀ n, Set (Fin n → Bool)} {K : ℕ → ℕ} (hSK : DenseRectangleFree S K)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (k : ℕ) (σ : Signature.{v}) (I : Interpretation σ Bool) (Acc : Set Bool)
      (c : Circuit σ (n + k) 1), I.IsU2 → c.NondeterministicDecides I Acc (S n) →
        (1 + (1 - (2 * p - B_pair)) / ((7 / 8) * B_pair + (1 / 8) * (2 * p)) - ε) * n <
          c.innerSize := by
  set δ_dirty := 2 * p - B_pair
  set A := (7 / 8) * B_pair + (1 / 8) * (2 * p)
  have hA : 0 < A := by dsimp [A]; positivity
  have hA_sub : 0 ≤ A - δ_dirty := by linarith
  set L_u2 := 1 + (1 - δ_dirty) / A
  set ε' := min ε (1 / A)
  have hε' : 0 < ε' := lt_min hε (by positivity)
  have hε'_le : ε' ≤ ε := min_le_left _ _
  have h1mAε : 0 ≤ 1 - A * ε' := u2_one_sub_mul_min_nonneg hA
  set ξ := A * ε' / (8 * (4 * |L_u2| + 4))
  have hξ : 0 < ξ := by positivity
  obtain ⟨C₀, hData⟩ := exists_u2PairData_of_u2CubicPairBound.{v} hp hBp_le hbound hδA hξ
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hcard_bool : (Nat.card Bool : ℝ) = 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_bool]; norm_num
  have hdef_o : (fun n : ℕ => (n : ℝ) - Real.logb 2 (S n).ncard) =o[atTop] fun n => (n : ℝ) := by
    refine (hSK.isLittleO_deficit.const_mul_left (1 / Real.log 2)).congr_left fun n => ?_
    rw [hcard_bool, Real.logb]
    field_simp
  have hK_o : (fun n : ℕ => (3 + A) * Real.logb 2 (K n)) =o[atTop] fun n => (n : ℝ) := by
    refine (hSK.isLittleO_log.const_mul_left ((3 + A) / Real.log 2)).congr_left fun n => ?_
    simp only [Real.logb]; ring
  have hV_o : (fun n : ℕ => (7 / Real.log 2) * Real.log (4 * |L_u2| * n + 4)) =o[atTop]
      fun n => (n : ℝ) :=
    (isLittleO_log_affine (by positivity) (by norm_num)).const_mul_left _
  have hconst_o : (fun _ : ℕ => 15 + |C₀| + 3 * ξ) =o[atTop] fun n => (n : ℝ) :=
    (isLittleO_const_id_atTop _).natCast_atTop
  have herr_o := ((hdef_o.add hK_o).add hV_o).add hconst_o
  filter_upwards [herr_o.bound (show 0 < A * ε' / 2 by positivity),
    hSK.eventually_rectangleFree, eventually_card_mul_sq_le_ncard hSK,
    eventually_ge_atTop 1] with n herr hfreen hbign hn1
  intro k σ I Acc c hU2 hdec
  suffices hlt : (L_u2 - ε') * n < c.innerSize by
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right (sub_le_sub_left hε'_le L_u2) (Nat.cast_nonneg n)) hlt
  by_contra! hle
  have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hs_nonneg : (0 : ℝ) ≤ c.innerSize := Nat.cast_nonneg _
  have hL_nonneg : 0 ≤ L_u2 - ε' := by nlinarith
  have hs_le_L : (c.innerSize : ℝ) ≤ |L_u2| * n :=
    hle.trans (mul_le_mul_of_nonneg_right (by linarith [le_abs_self L_u2]) (Nat.cast_nonneg n))
  set N := hiddenNetwork c I fun _ => Acc
  have hacc_N : N.accepted = S n := by
    rw [accepted_hiddenNetwork]
    ext x; rw [hdec x]
    exact exists_congr fun y => ⟨fun h => h 0, fun h o => Subsingleton.elim o 0 ▸ h⟩
  have hfreen' : RectangleFree N.accepted (K n) := hacc_N ▸ hfreen
  have hbign' : Nat.card Bool * K n ^ 2 ≤ N.accepted.ncard := hacc_N ▸ hbign
  have hu_lt : Nat.card Bool ^ N.readᶜ.ncard < K n :=
    hfreen'.pow_ncard_compl_lt N.dependsOn_read hbign'
  rw [Nat.card_eq_fintype_card, Fintype.card_bool] at hu_lt hbign'
  have hK_pos : 1 ≤ K n := hfreen.pos
  have hS_pos : (0 : ℝ) < (S n).ncard := by
    have : 0 < 2 * K n ^ 2 := by positivity
    rw [← hacc_N]
    exact_mod_cast this.trans_le hbign'
  obtain ⟨D, hD⟩ := hData hU2 Acc c
  have hclean_N : ∀ v, IsCleanVertex v →
      (∀ x α, N.Constraint v x α ↔ Constraint I (fun _ => univ) v (fun _ => false) α) ∧
        N.readAt v = ∅ :=
    fun v hv => ⟨hidden_constraint_iff_of_isCleanVertex I _ hv,
      readAt_hidden_eq_empty_of_isCleanVertex I _ hv⟩
  have hm_N : ∀ v, (N.readAt v).ncard ≤ 1 := fun v =>
    (Network.ncard_readAt_hide_le _ v).trans
      ((Network.ncard_readAt_reindex _ _ v).trans_le (ncard_readAt_le I _ v))
  have hfan : c.FanInAtMost 2 := hU2.fanInAtMost_two c
  obtain ⟨hV_pos, hxiV, hlogV0⟩ :=
    u2_vertex_bounds hU2 c (abs_nonneg L_u2) (mul_pos hA hε') hs_le_L
  set B_sup := A * c.innerSize - (A - δ_dirty) * N.read.ncard + ξ * Nat.card (Vertex c) + C₀
  have hmul_bp := D.mul_size_branchingProgram_le_rpow N hclean_N hV_pos
    (maxDegreeLE le_rfl hfan) hm_N hK_pos hu_lt.le hD
  have hrect_bp := (D.branchingProgram N).ncard_accepted_le (D.length_branchingProgram_pos N)
    (by rwa [D.accepted_branchingProgram N rfl hclean_N])
  rw [D.accepted_branchingProgram N rfl hclean_N, hacc_N] at hrect_bp
  have hS_le_rpow : ((S n).ncard : ℝ) ≤ (2 : ℝ) ^
      (max 0 B_sup + 15 + 3 * Real.logb 2 (K n) + 7 * Real.logb 2 (Nat.card (Vertex c))) :=
    (show ((S n).ncard : ℝ) ≤ _ by exact_mod_cast hrect_bp).trans hmul_bp
  have hlogS : Real.logb 2 (S n).ncard ≤
      max 0 B_sup + 15 + 3 * Real.logb 2 (K n) + 7 * Real.logb 2 (Nat.card (Vertex c)) := by
    have := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hS_pos hS_le_rpow
    rwa [Real.logb_rpow (by norm_num) (by norm_num)] at this
  have hcompl_eq : (N.read.ncard : ℝ) + N.readᶜ.ncard = n := by
    rw [← Nat.cast_add, ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hmax_le := u2_max_sup_le (C₀ := C₀) hA (sub_nonneg.mpr hBp_le) hA_sub h1mAε hK_pos
    hcompl_eq hu_lt.le hle (by positivity : 0 ≤ ξ * Nat.card (Vertex c))
  have hlogV : 7 * Real.logb 2 (Nat.card (Vertex c)) ≤
      (7 / Real.log 2) * Real.log (4 * |L_u2| * n + 4) := by
    rw [div_mul_eq_mul_div, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hlogV0 (by norm_num)
  simp only [Real.norm_eq_abs, Nat.abs_cast] at herr
  have herr' := (le_abs_self _).trans herr
  have hpos_margin : 0 < A * ε' * n := by positivity
  linarith only [hlogS, hmax_le, hxiV, hlogV, herr', hpos_margin]

/-- **Parametric `U₂` worst-case frontier lower bound.** Every deterministic circuit over a `U₂`
basis deciding dense `K_n`-rectangle-free sets `S_n` requires more than
`(1 + (1 - δ_dirty) / A - ε) n` inner gates. -/
theorem eventually_lt_innerSize_u2 {p B_pair : ℝ} (hp : 0 < p) (hBp : 0 < B_pair)
    (hBp_le : B_pair ≤ 2 * p) (hbound : U2CubicPairBound p B_pair)
    (hδA : 2 * p - B_pair ≤ (7 / 8) * B_pair + (1 / 8) * (2 * p))
    {S : ∀ n, Set (Fin n → Bool)} {K : ℕ → ℕ} (hSK : DenseRectangleFree S K)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ Bool) (Acc : Set Bool)
      (c : Circuit σ n 1), I.IsU2 → c.Decides I Acc (S n) →
        (1 + (1 - (2 * p - B_pair)) / ((7 / 8) * B_pair + (1 / 8) * (2 * p)) - ε) * n <
          c.innerSize := by
  filter_upwards [eventually_lt_innerSize_u2_nondeterministic.{v} hp hBp hBp_le hbound hδA hSK
    hε] with n hn σ I Acc c hU2 hdec
  exact hn 0 σ I Acc c hU2 hdec.nondeterministicDecides

/-- **Parametric `U₂` average-case frontier lower bound.** Below `(1 + (1 - δ_dirty) / A - ε) n`
inner gates, every circuit over a `U₂` basis agrees with a family `S_n` of rectangle bias `b_n`
(`log K_n = o(n)`) on at most `1 / 2 + b_n + exp (-γ n)` of inputs. -/
theorem eventually_agreement_le_u2 {p B_pair : ℝ} (hp : 0 < p) (hBp : 0 < B_pair)
    (hBp_le : B_pair ≤ 2 * p) (hbound : U2CubicPairBound p B_pair)
    (hδA : 2 * p - B_pair ≤ (7 / 8) * B_pair + (1 / 8) * (2 * p))
    {S : ∀ n, Set (Fin n → Bool)} {K : ℕ → ℕ} {b : ℕ → ℝ}
    (hbias : ∀ᶠ n in atTop, RectangleBias (S n) (K n) (b n))
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ γ > 0, ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ Bool) (Acc : Set Bool)
      (c : Circuit σ n 1), I.IsU2 →
        (c.innerSize : ℝ) ≤
          (1 + (1 - (2 * p - B_pair)) / ((7 / 8) * B_pair + (1 / 8) * (2 * p)) - ε) * n →
        agreement (S n) {x | c.eval I x 0 ∈ Acc} ≤ 1 / 2 + b n + Real.exp (-(γ * n)) := by
  set δ_dirty := 2 * p - B_pair
  set A := (7 / 8) * B_pair + (1 / 8) * (2 * p)
  have hA : 0 < A := by dsimp [A]; positivity
  have hA_sub : 0 ≤ A - δ_dirty := by linarith
  set L_u2 := 1 + (1 - δ_dirty) / A
  set ε' := min ε (1 / A)
  have hε' : 0 < ε' := lt_min hε (by positivity)
  have hε'_le : ε' ≤ ε := min_le_left _ _
  have h1mAε : 0 ≤ 1 - A * ε' := u2_one_sub_mul_min_nonneg hA
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  set μ := min (A * ε' / 4) (1 / 4)
  have hμ : 0 < μ := lt_min (by positivity) (by norm_num)
  refine ⟨μ * Real.log 2, by positivity, ?_⟩
  set ξ := A * ε' / (8 * (4 * |L_u2| + 4))
  have hξ : 0 < ξ := by positivity
  obtain ⟨C₀, hData⟩ := exists_u2PairData_of_u2CubicPairBound.{v} hp hBp_le hbound hδA hξ
  set K' : ℕ → ℕ := fun n => max (K n) 2
  have hK'_logb : (fun n : ℕ => Real.logb 2 (K' n)) =o[atTop] fun n => (n : ℝ) :=
    isLittleO_logb_max_two hK 2
  have hV_o : (fun n : ℕ => (7 / Real.log 2) * Real.log (4 * |L_u2| * n + 4)) =o[atTop]
      fun n => (n : ℝ) :=
    (isLittleO_log_affine (by positivity) (by norm_num)).const_mul_left _
  have hconst_o : (fun _ : ℕ => 15 + |C₀| + 3 * ξ) =o[atTop] fun n => (n : ℝ) :=
    (isLittleO_const_id_atTop _).natCast_atTop
  have herr_o := ((hK'_logb.const_mul_left (3 + A)).add hV_o).add hconst_o
  have hsmall_o : (fun n : ℕ => 2 + 2 * Real.logb 2 (K' n)) =o[atTop] fun n => (n : ℝ) :=
    (isLittleO_const_id_atTop _).natCast_atTop.add (hK'_logb.const_mul_left 2)
  filter_upwards [hbias, herr_o.bound (show 0 < A * ε' / 2 by positivity),
    hsmall_o.bound (by norm_num : (0 : ℝ) < 1 / 2), eventually_ge_atTop 1] with
    n hbiasn herr hsmalln hn1
  intro σ I Acc c hU2 hsize
  have hsize' : (c.innerSize : ℝ) ≤ (L_u2 - ε') * n :=
    hsize.trans (mul_le_mul_of_nonneg_right (sub_le_sub_left hε'_le L_u2) (Nat.cast_nonneg n))
  have hK2 : 2 ≤ K' n := le_max_right _ _
  have hK_posR : (0 : ℝ) < K' n := by exact_mod_cast (show 0 < K' n by omega)
  have hK_ge1R : (1 : ℝ) ≤ K' n := by exact_mod_cast (show 1 ≤ K' n by omega)
  have hS : RectangleBias (S n) (K' n) (b n) := hbiasn.mono (le_max_left _ _)
  simp only [Real.norm_eq_abs, Nat.abs_cast] at herr hsmalln
  have hsmalln' := (le_abs_self _).trans hsmalln
  have hb : 0 ≤ b n := hS.nonneg (by
    rw [Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin,
      Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]
    exact le_pow_half_of_logb one_lt_two (by omega) (by push_cast; linarith))
  by_cases hu : K' n ≤ Nat.card Bool ^ (network c I fun _ => Acc).readᶜ.ncard
  · have hunr := agreement_le_of_unread I Acc c hS hb (by omega) hu
    rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool, Nat.cast_ofNat] at hunr
    have hres_le : ((2 * K' n ^ 2 : ℕ) : ℝ) / (2 : ℝ) ^ n ≤
        Real.exp (-((μ * Real.log 2) * n)) := by
      have hKr : ((2 * K' n ^ 2 : ℕ) : ℝ) = (2 : ℝ) ^ (1 + 2 * Real.logb 2 (K' n)) := by
        push_cast
        rw [Real.rpow_add (by norm_num), Real.rpow_one, mul_comm 2 (Real.logb 2 (K' n)),
          Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hK_posR,
          Real.rpow_ofNat]
      rw [hKr, ← Real.rpow_natCast (2 : ℝ), ← Real.rpow_sub (by norm_num),
        Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      refine Real.exp_le_exp.mpr ?_
      have hμn : μ * n ≤ (1 / 4) * n :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg n)
      have hexp_le : 1 + 2 * Real.logb 2 (K' n) - n ≤ -(μ * n) := by linarith
      have := mul_le_mul_of_nonneg_left hexp_le hlog2_pos.le
      linarith
    exact hunr.trans (add_le_add_right hres_le _)
  · push Not at hu
    rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at hu
    obtain ⟨D, hD⟩ := hData (n := n) (k := 0) hU2 Acc c
    rw [read_hiddenNetwork_zero] at hD
    set R := (network c I fun _ => Acc).read.ncard
    set V := Nat.card (Vertex c)
    set B_sup := A * c.innerSize - (A - δ_dirty) * R + ξ * V + C₀
    have hs_le_L : (c.innerSize : ℝ) ≤ |L_u2| * n :=
      hsize'.trans (mul_le_mul_of_nonneg_right (by linarith [le_abs_self L_u2]) (Nat.cast_nonneg n))
    have hfan : c.FanInAtMost 2 := hU2.fanInAtMost_two c
    obtain ⟨hV_pos, hxiV, hlogV0⟩ :=
      u2_vertex_bounds hU2 c (abs_nonneg L_u2) (mul_pos hA hε') hs_le_L
    let R_res : ℝ :=
      (2 : ℝ) ^ (max 0 B_sup + 15 + 3 * Real.logb 2 (K' n) + 7 * Real.logb 2 V)
    have bound_acc (A_set : Set Bool) :
        |signedCount (S n) (network c I fun _ => A_set).accepted| ≤
          2 * b n * (network c I fun _ => A_set).accepted.ncard + R_res := by
      set N_A := network c I fun _ => A_set
      have hclean_A : ∀ v, IsCleanVertex v →
          (∀ x α, N_A.Constraint v x α ↔ Constraint I (fun _ => univ) v (fun _ => false) α) ∧
            N_A.readAt v = ∅ :=
        fun v hv =>
          ⟨constraint_iff_of_isCleanVertex I _ hv, readAt_eq_empty_of_isCleanVertex I _ hv⟩
      have hunamb := D.unambiguous_branchingProgram N_A rfl hclean_A fun _ _ _ => satisfies_unique
      have hpeel := (D.branchingProgram N_A).abs_signedCount_accepted_le hunamb
        (D.length_branchingProgram_pos N_A) hb hS
      rw [D.accepted_branchingProgram N_A rfl hclean_A] at hpeel
      have hread_eq : N_A.read = (network c I fun _ => Acc).read := rfl
      have hmul := D.mul_size_branchingProgram_le_rpow N_A hclean_A hV_pos
        (maxDegreeLE le_rfl hfan) (ncard_readAt_le I _) (K := K' n) (by omega)
        (by rw [hread_eq]; exact hu.le) hD
      exact hpeel.trans (by gcongr)
    have h₁ := bound_acc Acc
    have h₂ := bound_acc Accᶜ
    rw [accepted_network_eq_eval] at h₁
    have hacc_c : (network c I fun _ => Accᶜ).accepted = {x | c.eval I x 0 ∈ Acc}ᶜ := by
      rw [accepted_network_eq_eval]; rfl
    rw [hacc_c] at h₂
    have hagr := agreement_le h₁ h₂
    have hcard_in : (Nat.card (Fin n → Bool) : ℝ) = (2 : ℝ) ^ n := by
      rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin,
        Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]
      push_cast; rfl
    have hb_half : (1 + 2 * b n) / 2 = 1 / 2 + b n := by ring
    have hres_half : (R_res + R_res) / (2 * (2 : ℝ) ^ n) = R_res / (2 : ℝ) ^ n := by
      field_simp
      ring
    rw [hcard_in, hb_half, hres_half] at hagr
    -- Bound the exponent of `R_res / 2 ^ n` by `-(A * ε' / 4) * n`.
    have hcompl_eq : (R : ℝ) + (network c I fun _ => Acc).readᶜ.ncard = n := by
      rw [← Nat.cast_add, ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
    have hmax_le := u2_max_sup_le (C₀ := C₀) hA (sub_nonneg.mpr hBp_le) hA_sub h1mAε
      (Nat.one_le_of_lt hK2) hcompl_eq hu.le hsize' (mul_nonneg hξ.le (Nat.cast_nonneg V))
    have hlogV : 7 * Real.logb 2 V ≤ (7 / Real.log 2) * Real.log (4 * |L_u2| * n + 4) := by
      rw [div_mul_eq_mul_div, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hlogV0 (by norm_num)
    have herr' := (le_abs_self _).trans herr
    have hexp_le : max 0 B_sup + 15 + 3 * Real.logb 2 (K' n) + 7 * Real.logb 2 V - n ≤
        -(μ * n) := by
      have hμ_le : μ * n ≤ (A * ε' / 4) * n :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg n)
      have hmargin : (0 : ℝ) ≤ A * ε' * n := by positivity
      linarith only [hmax_le, hxiV, hlogV, herr', hμ_le, hmargin]
    have hratio : R_res / (2 : ℝ) ^ n ≤ Real.exp (-((μ * Real.log 2) * n)) := by
      dsimp only [R_res]
      rw [← Real.rpow_natCast (2 : ℝ), ← Real.rpow_sub (by norm_num),
        Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      refine Real.exp_le_exp.mpr ?_
      have := mul_le_mul_of_nonneg_left hexp_le hlog2_pos.le
      linarith only [this]
    exact hagr.trans (add_le_add_right hratio _)

/-- **Parametric `U₂` quadratic-form correlation bound.** Under `U2CubicPairBound p B_pair` with
`δ_dirty := 2 p - B_pair < 1` and `δ_dirty ≤ A := (7/8) B_pair + (1/8)(2p)`, set
`L_u2 = 1 + (1 - δ_dirty) / A` and `c* = 1 + (1/2 - δ_dirty) / A`. For every `c ≥ 1/2`, every
`γ < (c* - c) / (2 L_u2)`, and every family `Q_n` whose polar matrix has bisection cut rank
`⌊n/2⌋ - o(n)`, every `U₂` circuit with at most `c n` inner gates has correlation at most
`2^{-γ n}` with `BitString.quadForm (Q n)`. -/
theorem eventually_abs_correlation_quadForm_le_u2 {p B_pair c γ : ℝ} (hp : 0 < p)
    (hBp : 0 < B_pair) (hBp_le : B_pair ≤ 2 * p) (hbound : U2CubicPairBound p B_pair)
    (hδA : 2 * p - B_pair ≤ (7 / 8) * B_pair + (1 / 8) * (2 * p))
    (hδ1 : 2 * p - B_pair < 1) (hc : 1 / 2 ≤ c)
    (hγ : γ <
      (1 + (1 / 2 - (2 * p - B_pair)) / ((7 / 8) * B_pair + (1 / 8) * (2 * p)) - c) /
        (2 * (1 + (1 - (2 * p - B_pair)) / ((7 / 8) * B_pair + (1 / 8) * (2 * p)))))
    (Q : ∀ n, Matrix (Fin n) (Fin n) (ZMod 2)) (e : ℕ → ℝ)
    (he : e =o[atTop] fun n => (n : ℝ))
    (hQ : ∀ᶠ n in atTop, ∀ U : Set (Fin n), U.ncard = n / 2 →
      ((n / 2 : ℕ) : ℝ) ≤ (Q n + (Q n)ᵀ).cutRank U + e n) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ Bool) (Acc : Set Bool)
      (C : Circuit σ n 1), I.IsU2 → (C.innerSize : ℝ) ≤ c * n →
        |correlation {x | BitString.quadForm (Q n) x} {x | C.eval I x 0 ∈ Acc}| ≤
          (2 : ℝ) ^ (-γ * n) := by
  set δ_dirty := 2 * p - B_pair
  set A := (7 / 8) * B_pair + (1 / 8) * (2 * p)
  have hA : 0 < A := by dsimp [A]; positivity
  have hδ0 : 0 ≤ δ_dirty := by dsimp [δ_dirty]; linarith
  have hA_sub : 0 ≤ A - δ_dirty := by linarith
  set L_u2 := 1 + (1 - δ_dirty) / A
  set c_star := 1 + (1 / 2 - δ_dirty) / A
  have hL_pos : 0 < L_u2 := by
    have : 0 < (1 - δ_dirty) / A := div_pos (by linarith) hA
    dsimp [L_u2]; linarith
  set θ := (c_star - c) / L_u2
  have h2γ : 2 * γ < θ := by
    have : (c_star - c) / (2 * L_u2) = θ / 2 := by dsimp only [θ]; ring_nf
    linarith
  have hdenom_pos : 0 < A + 1 - δ_dirty := by linarith
  have hθ_alt : θ = (A + 1 / 2 - δ_dirty - A * c) / (A + 1 - δ_dirty) := by
    dsimp only [θ, c_star, L_u2]
    field_simp
    ring
  have hθ_bal : A * c - (A - δ_dirty) * (1 - θ) - 1 / 2 = -θ := by
    rw [hθ_alt]
    field_simp
    ring
  have hθ_half : θ ≤ 1 / 2 := by
    rw [hθ_alt, div_le_iff₀ hdenom_pos]
    nlinarith
  set Δ := θ - 2 * γ
  have hΔ : 0 < Δ := by dsimp [Δ]; linarith
  set ξ := Δ / (8 * (4 * c + 4))
  have hξ : 0 < ξ := by positivity
  obtain ⟨C₀, hData⟩ := exists_u2PairData_of_u2CubicPairBound.{v} hp hBp_le hbound hδA hξ
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hV_o : (fun n : ℕ => (6 / Real.log 2) * Real.log (4 * c * n + 4)) =o[atTop]
      fun n => (n : ℝ) :=
    (isLittleO_log_affine (by positivity) (by norm_num)).const_mul_left _
  have hconst_o : (fun _ : ℕ => |C₀| + 3 * ξ + 3 / 2) =o[atTop] fun n => (n : ℝ) :=
    (isLittleO_const_id_atTop _).natCast_atTop
  have herr_o := (he.norm_left.add hV_o).add hconst_o
  filter_upwards [hQ, herr_o.bound (show 0 < Δ / 2 by positivity), eventually_ge_atTop 1] with
    n hQn herr hn1
  intro σ I Acc C hU2 hsize
  simp only [Real.norm_eq_abs, Nat.abs_cast] at herr
  have herr' := (le_abs_self _).trans herr
  have he_le : e n ≤ |e n| := le_abs_self (e n)
  have hΔn : 0 ≤ Δ * n := by positivity
  apply abs_le_of_sq_le_sq _ (by positivity)
  have hsq_rhs : ((2 : ℝ) ^ (-γ * n)) ^ 2 = (2 : ℝ) ^ (-(2 * γ) * n) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    push_cast; ring_nf
  rw [hsq_rhs]
  set N₁ := network C I fun _ => Acc
  have hcompl : (N₁.readᶜ.ncard : ℝ) + N₁.read.ncard = n := by
    rw [← Nat.cast_add, add_comm, ncard_add_ncard_compl, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have hhalf_le : ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) / 2 := by
    rw [le_div_iff₀ (by norm_num)]
    exact_mod_cast Nat.div_mul_le_self n 2
  have hhalf_ge : (n : ℝ) / 2 - 1 / 2 ≤ ((n / 2 : ℕ) : ℝ) := by
    have : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by
      exact_mod_cast (show n ≤ 2 * (n / 2) + 1 by omega)
    linarith
  by_cases hd : θ * n ≤ N₁.readᶜ.ncard
  · refine (sq_correlation_quadForm_le_of_unread I Acc C (Q n) hQn
      (k := min N₁.readᶜ.ncard (n / 2)) (min_le_right _ _) (min_le_left _ _)).trans
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
    have hθn_half : θ * n ≤ (n : ℝ) / 2 := by
      linarith [mul_le_mul_of_nonneg_right hθ_half (Nat.cast_nonneg (α := ℝ) n)]
    have hk : θ * n - 1 / 2 ≤ ((min N₁.readᶜ.ncard (n / 2) : ℕ) : ℝ) := by
      rcases min_choice N₁.readᶜ.ncard (n / 2) with h | h <;> rw [h] <;> linarith
    have hxi0 : 0 ≤ 3 * ξ + |C₀| := by positivity
    have hVlog0 : 0 ≤ (6 / Real.log 2) * Real.log (4 * c * n + 4) :=
      mul_nonneg (by positivity) (Real.log_nonneg (by nlinarith [Nat.cast_nonneg (α := ℝ) n]))
    have hΔ_eq : Δ * n = θ * n - 2 * γ * n := by dsimp only [Δ]; ring
    linarith only [hk, herr', he_le, hxi0, hVlog0, hΔn, hΔ_eq]
  · push Not at hd
    have hread_lo : (1 - θ) * n < N₁.read.ncard := by linarith
    have hread_half : n / 2 ≤ N₁.read.ncard := by
      have h1 : ((n / 2 : ℕ) : ℝ) < N₁.read.ncard := by
        have := mul_le_mul_of_nonneg_right hθ_half (Nat.cast_nonneg (α := ℝ) n)
        linarith
      exact_mod_cast h1.le
    obtain ⟨D, hD⟩ := hData (n := n) (k := 0) hU2 Acc C
    rw [read_hiddenNetwork_zero] at hD
    set B_sup := A * C.innerSize - (A - δ_dirty) * N₁.read.ncard + ξ * Nat.card (Vertex C) + C₀
    refine (D.sq_correlation_quadForm_le Acc (Q n) hQn hread_half hD).trans
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
    obtain ⟨hV_pos, hxiV, hlogV0⟩ := u2_vertex_bounds hU2 C (by linarith) hΔ hsize
    have hnatlog : 6 * (Nat.log 2 (Nat.card (Vertex C)) : ℝ) ≤
        (6 / Real.log 2) * Real.log (4 * c * n + 4) := by
      have h1 : (Nat.log 2 (Nat.card (Vertex C)) : ℝ) ≤ Real.logb 2 (Nat.card (Vertex C)) := by
        rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity), Real.rpow_natCast]
        exact_mod_cast Nat.pow_log_le_self 2 (by omega)
      rw [div_mul_eq_mul_div, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (h1.trans hlogV0) (by norm_num)
    have hB_le : B_sup - (n : ℝ) / 2 ≤ -θ * n + ξ * Nat.card (Vertex C) + |C₀| := by
      have h1 := mul_le_mul_of_nonneg_left hsize hA.le
      have h2 := mul_le_mul_of_nonneg_left hread_lo.le hA_sub
      have hbal_n : (A * c - (A - δ_dirty) * (1 - θ) - 1 / 2) * n = -θ * n := by
        rw [hθ_bal]
      have hC0 := le_abs_self C₀
      dsimp only [B_sup]
      linarith only [h1, h2, hbal_n, hC0]
    have hΔ_eq : Δ * n = θ * n - 2 * γ * n := by dsimp only [Δ]; ring
    have hn0 : ((n + 0 : ℕ) : ℝ) = n := by push_cast; ring
    linarith only [hB_le, hxiV, hnatlog, herr', he_le, hΔn, hΔ_eq, hn0]


/-! ### Unconditional `4.6362 n` `U₂` circuit lower bounds -/

private theorem u2_dirty_le_A_gaussian :
    2 * Gaussian.gaussianCoefficient - 271212 / 1000000 ≤
      (7 / 8) * (271212 / 1000000) + (1 / 8) * (2 * Gaussian.gaussianCoefficient) := by
  linarith [Gaussian.two_mul_gaussianCoefficient_le]

/-- **Unconditional `(4.6362 - ε) n` `U₂` nondeterministic frontier lower bound.** For every dense
`K_n`-rectangle-free family `S_n ⊆ Bool^n` and every `ε > 0`, eventually every nondeterministic
circuit with any number `k` of witness inputs over any `U₂` basis deciding `S_n` has more than
`(46362 / 10000 - ε) n` inner gates. -/
theorem eventually_46362_div_10000_sub_mul_lt_innerSize_u2_nondeterministic
    {S : ∀ n, Set (Fin n → Bool)} {K : ℕ → ℕ} (hSK : DenseRectangleFree S K)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (k : ℕ) (σ : Signature.{v}) (I : Interpretation σ Bool) (Acc : Set Bool)
      (c : Circuit σ (n + k) 1), I.IsU2 → c.NondeterministicDecides I Acc (S n) →
        (46362 / 10000 - ε) * n < c.innerSize := by
  filter_upwards [eventually_lt_innerSize_u2_nondeterministic.{v} Gaussian.gaussianCoefficient_pos
    (by norm_num) Gaussian.le_two_mul_gaussianCoefficient Gaussian.u2CubicPairBound_gaussian
    u2_dirty_le_A_gaussian hSK hε] with n hn k σ I Acc c hU2 hdec
  refine lt_of_le_of_lt ?_ (hn k σ I Acc c hU2 hdec)
  exact mul_le_mul_of_nonneg_right (by linarith [Gaussian.u2CircuitCoefficient_ge_46362])
    (Nat.cast_nonneg n)

/-- **Unconditional `(4.6362 - ε) n` `U₂` worst-case frontier lower bound.** For every dense
`K_n`-rectangle-free family `S_n ⊆ Bool^n` and every `ε > 0`, eventually every circuit over any `U₂`
basis deciding `S_n` has more than `(46362 / 10000 - ε) n` inner gates. -/
theorem eventually_46362_div_10000_sub_mul_lt_innerSize_u2
    {S : ∀ n, Set (Fin n → Bool)} {K : ℕ → ℕ} (hSK : DenseRectangleFree S K)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ Bool) (Acc : Set Bool)
      (c : Circuit σ n 1), I.IsU2 → c.Decides I Acc (S n) →
        (46362 / 10000 - ε) * n < c.innerSize := by
  filter_upwards [eventually_46362_div_10000_sub_mul_lt_innerSize_u2_nondeterministic.{v} hSK hε]
    with n hn σ I Acc c hU2 hdec
  exact hn 0 σ I Acc c hU2 hdec.nondeterministicDecides

/-- **Unconditional `(4.6362 - ε) n` De Morgan circuit lower bound.** -/
theorem eventually_46362_div_10000_sub_mul_lt_innerSize_deMorgan
    {S : ∀ n, Set (Fin n → Bool)} {K : ℕ → ℕ} (hSK : DenseRectangleFree S K)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (Acc : Set Bool) (c : Circuit Boolean.DeMorgan.signature n 1),
      c.Decides Boolean.DeMorgan.interpretation Acc (S n) →
        (46362 / 10000 - ε) * n < c.innerSize := by
  filter_upwards [eventually_46362_div_10000_sub_mul_lt_innerSize_u2.{0} hSK hε]
    with n hn Acc c hdec
  exact hn Boolean.DeMorgan.signature Boolean.DeMorgan.interpretation Acc c Boolean.DeMorgan.isU2
    hdec

/-- **Unconditional `(4.6362 - ε) n` Boolean circuit lower bound** (De Morgan with constants). -/
theorem eventually_46362_div_10000_sub_mul_lt_innerSize_boolean
    {S : ∀ n, Set (Fin n → Bool)} {K : ℕ → ℕ} (hSK : DenseRectangleFree S K)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (Acc : Set Bool) (c : Circuit Boolean.signature n 1),
      c.Decides Boolean.interpretation Acc (S n) →
        (46362 / 10000 - ε) * n < c.innerSize := by
  filter_upwards [eventually_46362_div_10000_sub_mul_lt_innerSize_u2.{0} hSK hε]
    with n hn Acc c hdec
  exact hn Boolean.signature Boolean.interpretation Acc c Boolean.isU2 hdec

/-- **Unconditional `(4.6362 - ε) n` `U₂` average-case frontier lower bound.** Below
`(46362 / 10000 - ε) n` inner gates, every circuit over any `U₂` basis agrees with a family `S_n`
of rectangle bias `b_n` (`log K_n = o(n)`) on at most `1 / 2 + b_n + exp (-γ n)` of inputs. -/
theorem eventually_agreement_le_u2_46362
    {S : ∀ n, Set (Fin n → Bool)} {K : ℕ → ℕ} {b : ℕ → ℝ}
    (hbias : ∀ᶠ n in atTop, RectangleBias (S n) (K n) (b n))
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ γ > 0, ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ Bool) (Acc : Set Bool)
      (c : Circuit σ n 1), I.IsU2 → (c.innerSize : ℝ) ≤ (46362 / 10000 - ε) * n →
        agreement (S n) {x | c.eval I x 0 ∈ Acc} ≤ 1 / 2 + b n + Real.exp (-(γ * n)) := by
  obtain ⟨γ, hγ, hev⟩ := eventually_agreement_le_u2.{v} Gaussian.gaussianCoefficient_pos
    (by norm_num) Gaussian.le_two_mul_gaussianCoefficient Gaussian.u2CubicPairBound_gaussian
    u2_dirty_le_A_gaussian hbias hK hε
  refine ⟨γ, hγ, ?_⟩
  filter_upwards [hev] with n hn σ I Acc c hU2 hsize
  refine hn σ I Acc c hU2 (hsize.trans ?_)
  exact mul_le_mul_of_nonneg_right (by linarith [Gaussian.u2CircuitCoefficient_ge_46362])
    (Nat.cast_nonneg n)

/-- **Unconditional `(4.6362 - ε) n` De Morgan average-case lower bound.** -/
theorem eventually_agreement_le_deMorgan_46362
    {S : ∀ n, Set (Fin n → Bool)} {K : ℕ → ℕ} {b : ℕ → ℝ}
    (hbias : ∀ᶠ n in atTop, RectangleBias (S n) (K n) (b n))
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ γ > 0, ∀ᶠ n in atTop, ∀ (Acc : Set Bool) (c : Circuit Boolean.DeMorgan.signature n 1),
      (c.innerSize : ℝ) ≤ (46362 / 10000 - ε) * n →
        agreement (S n) {x | c.eval Boolean.DeMorgan.interpretation x 0 ∈ Acc} ≤
          1 / 2 + b n + Real.exp (-(γ * n)) := by
  obtain ⟨γ, hγ, hev⟩ := eventually_agreement_le_u2_46362.{0} hbias hK hε
  refine ⟨γ, hγ, ?_⟩
  filter_upwards [hev] with n hn Acc c hsize
  exact hn Boolean.DeMorgan.signature Boolean.DeMorgan.interpretation Acc c
    Boolean.DeMorgan.isU2 hsize

/-- **Unconditional `(4.6362 - ε) n` Boolean average-case lower bound.** -/
theorem eventually_agreement_le_boolean_46362
    {S : ∀ n, Set (Fin n → Bool)} {K : ℕ → ℕ} {b : ℕ → ℝ}
    (hbias : ∀ᶠ n in atTop, RectangleBias (S n) (K n) (b n))
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ γ > 0, ∀ᶠ n in atTop, ∀ (Acc : Set Bool) (c : Circuit Boolean.signature n 1),
      (c.innerSize : ℝ) ≤ (46362 / 10000 - ε) * n →
        agreement (S n) {x | c.eval Boolean.interpretation x 0 ∈ Acc} ≤
          1 / 2 + b n + Real.exp (-(γ * n)) := by
  obtain ⟨γ, hγ, hev⟩ := eventually_agreement_le_u2_46362.{0} hbias hK hε
  refine ⟨γ, hγ, ?_⟩
  filter_upwards [hev] with n hn Acc c hsize
  exact hn Boolean.signature Boolean.interpretation Acc c Boolean.isU2 hsize

end Cslib.Circuits.Frontier
