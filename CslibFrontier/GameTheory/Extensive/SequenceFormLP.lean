/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Extensive.SequenceForm
public import Mathlib.Order.Bounds.Defs
import CslibFrontier.Foundations.LinearAlgebra.Matrix.LinearProgramming
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Two-player sequence-form equilibria, best-response LP duality, and zero-sum games

This module develops two-player equilibrium and linear-programming theory in sequence form for
extensive-form games with perfect recall ([vonStengel2007], Sections 3.10–3.11):

* **Sequence-form dual feasibility and LP strong duality** (`exists_seqMat_transpose_mulVec_ge`,
  `exists_isGreatest_isLeast_seqLP`): under `PerfectRecall T i`, any payoff vector
  `b : SeqVar T i → ℝ` is upper-bounded by `(seqMat T i)ᵀ *ᵥ p` for a bounded dual vector `p`, so
  maximizing `b ⬝ᵥ x` over `T.IsRealizationPlan i x` and minimizing `seqRhs T i ⬝ᵥ p`
  (= `p none`) over `b ≤ (seqMat T i)ᵀ *ᵥ p` attain equal optima.
* **Best-response duality & LCP complementarity** (`isSeqBestResponseFalse_iff_dual`,
  `isSeqBestResponseTrue_iff_dual`, `isSeqNash_iff_complementarity`): a realization plan is a
  sequence-form best response iff it satisfies dual feasibility and complementary slackness with an
  information-set multiplier vector, yielding the bilinear sequence-form complementarity / LCP
  characterization of Nash equilibria ([vonStengel2007], Theorem 3.14, Section 3.11, p. 74).
* **Equivalence with mixed and behavioral Nash equilibria** (`isMixedNash_toCostGame_iff_isSeqNash`,
  `isBehaviorNash_iff_isSeqNash`, `exists_isSeqNash`, `exists_isBehaviorNash`): under perfect
  recall for both players, mixed Nash equilibria of `T.toCostGame` and behavioral Nash equilibria
  (`IsBehaviorNash`) match bilinear sequence-form equilibria (`IsSeqNash`) without requiring
  positive chance probabilities.
* **Two-player zero-sum sequence-form LP minimax theorem**
  (`ExtensiveTree.IsZeroSum.exists_seq_lp_minimax`, [vonStengel2007], Theorem 3.13, Section 3.11,
  p. 73): in a two-player zero-sum extensive-form game with perfect recall, applying
  linear-programming strong duality directly to the sequence-form LP pair produces optimal
  realization plans `(x*, y*)` forming a sequence-form Nash equilibrium / saddle point together with
  induced minimax behavioral strategies via Kuhn's theorem
  (`ExtensiveTree.IsZeroSum.exists_behavior_minimax`).

## Main definitions

* `Cslib.GameTheory.Extensive.ExtensiveTree.IsSeqBestResponseFalse`,
  `Cslib.GameTheory.Extensive.ExtensiveTree.IsSeqBestResponseTrue`: best-response realization
  plans in a two-player extensive game.
* `Cslib.GameTheory.Extensive.ExtensiveTree.IsSeqNash`: two-player sequence-form Nash equilibrium.
* `Cslib.GameTheory.Extensive.ExtensiveTree.IsBehaviorNash`: behavioral Nash equilibrium.
* `Cslib.GameTheory.Extensive.ExtensiveTree.IsZeroSum`: two-player extensive games whose leaf
  payoffs sum to zero.

## Main results

* `Cslib.GameTheory.Extensive.exists_seqMat_transpose_mulVec_ge`: unconstrained dual feasibility for
  `seqMat`.
* `Cslib.GameTheory.Extensive.exists_isGreatest_isLeast_seqLP`: strong LP duality over
  realization plans.
* `Cslib.GameTheory.Extensive.isSeqBestResponseFalse_iff_dual`,
  `Cslib.GameTheory.Extensive.isSeqBestResponseTrue_iff_dual`: best-response KKT / complementarity
  characterization.
* `Cslib.GameTheory.Extensive.isSeqNash_iff_complementarity`: **Theorem 3.14**
  ([vonStengel2007], Section 3.11, p. 74) — sequence-form LCP / complementarity characterization of
  two-player Nash equilibria.
* `Cslib.GameTheory.Extensive.isMixedNash_toCostGame_iff_isSeqNash`,
  `Cslib.GameTheory.Extensive.isBehaviorNash_iff_isSeqNash`,
  `Cslib.GameTheory.Extensive.exists_isSeqNash`,
  `Cslib.GameTheory.Extensive.exists_isBehaviorNash`: equivalence and existence of sequence-form
  and behavioral Nash equilibria.
* `Cslib.GameTheory.Extensive.ExtensiveTree.IsZeroSum.exists_seq_lp_minimax`,
  `Cslib.GameTheory.Extensive.ExtensiveTree.IsZeroSum.exists_behavior_minimax`: **Theorem 3.13**
  ([vonStengel2007], Section 3.11, p. 73) — zero-sum extensive-form minimax equilibrium directly
  from sequence-form LP duality.

## References

* [B. von Stengel, *Equilibrium Computation for Two-Player Games in Strategic and Extensive
  Form*][vonStengel2007], Sections 3.10–3.11 (pp. 72–74), Theorem 3.13 (p. 73), and
  Theorem 3.14 (p. 74).
-/

public section

namespace Cslib.GameTheory.Extensive

open Finset Matrix

universe u v

section SequenceLP

variable {ι : Type u} {H : ι → Type v} {Act : ∀ i, H i → Type}

open Classical in
/-- Under perfect recall, every objective `b : SeqVar T i → ℝ` admits a dual multiplier vector
`p` satisfying `b ≤ (seqMat T i)ᵀ *ᵥ p` ([vonStengel2007], Section 3.10). -/
theorem exists_seqMat_transpose_mulVec_ge [DecidableEq ι] [∀ j h, Finite (Act j h)]
    [∀ j h, Nonempty (Act j h)] {T : ExtensiveTree ι H Act} {i : ι} [Fintype (H i)]
    (hpr : T.PerfectRecall i) (b : SeqVar T i → ℝ) :
    ∃ p : Option {h : H i // T.OccursInfoSet i h} → ℝ, b ≤ (seqMat T i)ᵀ *ᵥ p := by
  classical
  let _ : ∀ j h, Fintype (Act j h) := fun j h => Fintype.ofFinite (Act j h)
  let S := {h : H i // T.OccursInfoSet i h}
  let maxLen : ℕ := (occursSeqFinset T i).sup List.length
  let r : ℝ := (Fintype.card S : ℝ) + 1
  let M : ℝ := ∑ σ : SeqVar T i, max (b σ) 0
  have hM0 : 0 ≤ M := sum_nonneg fun σ _ => le_max_right _ _
  have hbM : ∀ σ : SeqVar T i, b σ ≤ M := fun σ =>
    (le_max_left (b σ) 0).trans (single_le_sum (fun τ _ => le_max_right (b τ) 0) (mem_univ σ))
  have hr1 : 1 ≤ r := by
    simp only [r]
    linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card S)]
  let p : Option S → ℝ
    | none => M * r ^ maxLen
    | some h => M * r ^ (maxLen - ((T.infoSeq i h.1).length + 1))
  have hpow_ge : ∀ k : ℕ, M ≤ M * r ^ k := fun k => by
    have h1 : 1 ≤ r ^ k := one_le_pow₀ hr1
    nlinarith
  have hdiff : ∀ k : ℕ, k + 1 ≤ maxLen →
      M * r ^ (maxLen - k) - (Fintype.card S : ℝ) * (M * r ^ (maxLen - (k + 1))) =
        M * r ^ (maxLen - (k + 1)) := fun k hk => by
    have hsub : maxLen - k = (maxLen - (k + 1)) + 1 := by omega
    rw [hsub, pow_succ]
    simp only [r]
    ring
  have hrow_eval : ∀ σ : SeqVar T i,
      ((seqMat T i)ᵀ *ᵥ p) σ =
        p none * (seqMat T i *ᵥ Pi.single σ (1 : ℝ)) none +
          ∑ h : S, p (some h) * (seqMat T i *ᵥ Pi.single σ (1 : ℝ)) (some h) := fun σ => by
    have hdot : ((seqMat T i)ᵀ *ᵥ p) σ = ((seqMat T i)ᵀ *ᵥ p) ⬝ᵥ Pi.single σ (1 : ℝ) := by
      rw [dotProduct, sum_eq_single σ (fun τ _ h => by simp [h]) (fun h => absurd (mem_univ σ) h)]
      simp
    rw [hdot, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, dotProduct, Fintype.sum_option]
  refine ⟨p, fun σ => ?_⟩
  change b σ ≤ ((seqMat T i)ᵀ *ᵥ p) σ
  rw [hrow_eval σ]
  by_cases hnil : σ.1 = []
  · have hσ_nil : σ = SeqVar.nil T i := Subtype.ext (by simp [hnil])
    subst hσ_nil
    have hnone : (seqMat T i *ᵥ Pi.single (SeqVar.nil T i) (1 : ℝ)) none = 1 := by
      rw [seqMat_mulVec_none, Pi.single_eq_same]
    have hsome : ∀ h : S, (seqMat T i *ᵥ Pi.single (SeqVar.nil T i) (1 : ℝ)) (some h) =
        if T.infoSeq i h.1 = [] then -1 else 0 := fun h => by
      rw [seqMat_mulVec_some hpr h]
      have hsum0 : ∑ a : Act i h.1,
          Pi.single (M := fun _ => ℝ) (SeqVar.nil T i) (1 : ℝ)
            (SeqVar.infoSeqExt hpr h.2 a) = 0 :=
        sum_eq_zero fun a _ => by
          have hne : SeqVar.infoSeqExt hpr h.2 a ≠ SeqVar.nil T i := by
            intro heq
            exact seqVar_infoSeqExt_ne_nil hpr h.2 a (by simpa using congrArg Subtype.val heq)
          exact Pi.single_eq_of_ne hne _
      rw [hsum0, add_zero]
      by_cases hi : T.infoSeq i h.1 = []
      · have heq : SeqVar.infoSeq hpr h.2 = SeqVar.nil T i := by
          apply Subtype.ext
          rw [SeqVar.infoSeq_val, hi]
          simp
        simp [hi, heq]
      · have hne : SeqVar.infoSeq hpr h.2 ≠ SeqVar.nil T i := by
          intro heq
          apply hi
          have hv := congrArg Subtype.val heq
          simpa [SeqVar.infoSeq_val] using hv
        simp [hi, hne]
    rw [hnone, mul_one]
    simp_rw [hsome]
    by_cases hex : ∃ h₀ : S, T.infoSeq i h₀.1 = []
    · obtain ⟨h₀, hh₀⟩ := hex
      have hlen1 : 1 ≤ maxLen := by
        let τ := SeqVar.infoSeqExt hpr h₀.2 (Classical.arbitrary (Act i h₀.1))
        have hmem : τ.1 ∈ occursSeqFinset T i := mem_occursSeqFinset.2 τ.2
        have hle := Finset.le_sup (f := List.length) hmem
        have hlenτ : τ.1.length = 1 := by
          dsimp [τ]
          rw [SeqVar.infoSeqExt_val, hh₀, List.nil_append, List.length_singleton]
        linarith
      have hterm : ∀ h : S, -(M * r ^ (maxLen - 1)) ≤
          p (some h) * (if T.infoSeq i h.1 = [] then (-1 : ℝ) else 0) := by
        intro h
        split_ifs with h1
        · have hlenh : (T.infoSeq i h.1).length = 0 := by rw [h1, List.length_nil]
          simp [p, hlenh]
        · rw [mul_zero]
          have : 0 ≤ M * r ^ (maxLen - 1) := by positivity
          linarith
      have hsum_lb : -((Fintype.card S : ℝ) * (M * r ^ (maxLen - 1))) ≤
          ∑ h : S, p (some h) * (if T.infoSeq i h.1 = [] then (-1 : ℝ) else 0) := by
        calc -((Fintype.card S : ℝ) * (M * r ^ (maxLen - 1)))
            = ∑ _ : S, -(M * r ^ (maxLen - 1)) := by simp
          _ ≤ _ := sum_le_sum fun h _ => hterm h
      have hpnone : p none = M * r ^ maxLen := rfl
      have hcomb : p none - (Fintype.card S : ℝ) * (M * r ^ (maxLen - 1)) =
          M * r ^ (maxLen - 1) := by
        rw [hpnone]
        simpa using hdiff 0 hlen1
      linarith [hbM (SeqVar.nil T i), hpow_ge (maxLen - 1)]
    · push Not at hex
      have hzero : ∑ h : S, p (some h) * (if T.infoSeq i h.1 = [] then (-1 : ℝ) else 0) = 0 :=
        sum_eq_zero fun h _ => by simp [hex h]
      rw [hzero, add_zero]
      exact (hbM (SeqVar.nil T i)).trans (hpow_ge maxLen)
  · obtain ⟨h₀, a₀, rfl⟩ := exists_infoSeqExt_of_seqVar_ne_nil hpr σ hnil
    let σ₀ := SeqVar.infoSeqExt hpr h₀.2 a₀
    have hnone : (seqMat T i *ᵥ Pi.single σ₀ (1 : ℝ)) none = 0 := by
      rw [seqMat_mulVec_none]
      have hne : SeqVar.nil T i ≠ σ₀ := fun heq =>
        seqVar_infoSeqExt_ne_nil hpr h₀.2 a₀ (by simpa [σ₀] using (congrArg Subtype.val heq).symm)
      exact Pi.single_eq_of_ne hne _
    rw [hnone, mul_zero, zero_add]
    rw [← add_sum_erase univ _ (mem_univ h₀)]
    have hh₀_val : (seqMat T i *ᵥ Pi.single σ₀ (1 : ℝ)) (some h₀) = 1 := by
      rw [seqMat_mulVec_some hpr h₀]
      have hne_pre : SeqVar.infoSeq hpr h₀.2 ≠ σ₀ := fun heq => by
        have hlen := congrArg (List.length ∘ Subtype.val) heq
        simp only [Function.comp_apply, SeqVar.infoSeq_val, σ₀, SeqVar.infoSeqExt_val,
          List.length_append, List.length_singleton] at hlen
        omega
      rw [Pi.single_eq_of_ne hne_pre, neg_zero, zero_add]
      rw [sum_eq_single a₀]
      · exact Pi.single_eq_same _ _
      · intro a _ hne
        have hnea : SeqVar.infoSeqExt hpr h₀.2 a ≠ σ₀ := fun heq => by
          have hpair := seqVar_infoSeqExt_inj hpr heq
          exact hne (eq_of_heq (Sigma.mk.inj_iff.1 hpair).2)
        exact Pi.single_eq_of_ne hnea _
      · intro hmem
        exact absurd (mem_univ a₀) hmem
    rw [hh₀_val, mul_one]
    have hother : ∀ h ∈ univ.erase h₀,
        (seqMat T i *ᵥ Pi.single σ₀ (1 : ℝ)) (some h) =
          if σ₀.1 = T.infoSeq i h.1 then -1 else 0 := fun h hh => by
      have hne : h ≠ h₀ := ne_of_mem_erase hh
      rw [seqMat_mulVec_some hpr h]
      have hsum0 : ∑ a : Act i h.1, Pi.single (M := fun _ => ℝ) σ₀ (1 : ℝ)
          (SeqVar.infoSeqExt hpr h.2 a) = 0 :=
        sum_eq_zero fun a _ => by
          have hnea : SeqVar.infoSeqExt hpr h.2 a ≠ σ₀ := fun heq => by
            have hpair := seqVar_infoSeqExt_inj hpr heq
            have hh1 : (⟨h.1, h.2⟩ : S) = ⟨h₀.1, h₀.2⟩ := by
              simpa only [Sigma.ext_iff] using (Sigma.mk.inj_iff.1 hpair).1
            exact hne hh1
          exact Pi.single_eq_of_ne hnea _
      rw [hsum0, add_zero]
      by_cases hi : σ₀.1 = T.infoSeq i h.1
      · have heq : SeqVar.infoSeq hpr h.2 = σ₀ := by
          apply Subtype.ext
          rw [SeqVar.infoSeq_val, hi]
        simp [hi, heq]
      · have hneh : SeqVar.infoSeq hpr h.2 ≠ σ₀ := fun heq => by
          apply hi
          have hv := congrArg Subtype.val heq
          rw [SeqVar.infoSeq_val] at hv
          exact hv.symm
        simp [hi, hneh]
    rw [sum_congr rfl fun h hh => congrArg (p (some h) * ·) (hother h hh)]
    let d : ℕ := (T.infoSeq i h₀.1).length + 1
    have hlen_ext : σ₀.1.length = d := by
      dsimp [σ₀, d]
      rw [SeqVar.infoSeqExt_val, List.length_append, List.length_singleton]
    have hpself : p (some h₀) = M * r ^ (maxLen - d) := rfl
    by_cases hex : ∃ h₁ ∈ univ.erase h₀, σ₀.1 = T.infoSeq i h₁.1
    · obtain ⟨h₁, _, hh₁⟩ := hex
      have hlen1 : d + 1 ≤ maxLen := by
        let τ := SeqVar.infoSeqExt hpr h₁.2 (Classical.arbitrary (Act i h₁.1))
        have hmem : τ.1 ∈ occursSeqFinset T i := mem_occursSeqFinset.2 τ.2
        have hle := Finset.le_sup (f := List.length) hmem
        have hlenτ : τ.1.length = d + 1 := by
          dsimp [τ]
          rw [SeqVar.infoSeqExt_val, List.length_append, List.length_singleton, ← hh₁, hlen_ext]
        linarith
      have hterm : ∀ h ∈ univ.erase h₀, -(M * r ^ (maxLen - (d + 1))) ≤
          p (some h) * (if σ₀.1 = T.infoSeq i h.1 then (-1 : ℝ) else 0) := fun h _ => by
        split_ifs with h1
        · have hlenh : (T.infoSeq i h.1).length = d := by rw [← h1, hlen_ext]
          simp [p, hlenh]
        · rw [mul_zero]
          have : 0 ≤ M * r ^ (maxLen - (d + 1)) := by positivity
          linarith
      have hsum_lb : -(((univ.erase h₀).card : ℝ) * (M * r ^ (maxLen - (d + 1)))) ≤
          ∑ h ∈ univ.erase h₀,
            p (some h) * (if σ₀.1 = T.infoSeq i h.1 then (-1 : ℝ) else 0) := by
        calc -(((univ.erase h₀).card : ℝ) * (M * r ^ (maxLen - (d + 1))))
            = ∑ _ ∈ univ.erase h₀, -(M * r ^ (maxLen - (d + 1))) := by simp
          _ ≤ _ := sum_le_sum hterm
      have hcard : ((univ.erase h₀).card : ℝ) ≤ (Fintype.card S : ℝ) := by
        exact_mod_cast (card_erase_le (a := h₀) (s := univ)).trans (by rw [card_univ])
      have hmul_card : ((univ.erase h₀).card : ℝ) * (M * r ^ (maxLen - (d + 1))) ≤
          (Fintype.card S : ℝ) * (M * r ^ (maxLen - (d + 1))) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      have hcomb := hdiff d hlen1
      rw [hpself]
      linarith [hbM σ₀, hpow_ge (maxLen - (d + 1))]
    · push Not at hex
      have hzero : ∑ h ∈ univ.erase h₀,
          p (some h) * (if σ₀.1 = T.infoSeq i h.1 then (-1 : ℝ) else 0) = 0 :=
        sum_eq_zero fun h hh => by simp [hex h hh]
      rw [hzero, add_zero, hpself]
      exact (hbM σ₀).trans (hpow_ge (maxLen - d))

@[simp]
theorem seqRhs_dotProduct (T : ExtensiveTree ι H Act) (i : ι)
    [Fintype {h : H i // T.OccursInfoSet i h}]
    (q : Option {h : H i // T.OccursInfoSet i h} → ℝ) :
    seqRhs T i ⬝ᵥ q = q none := by
  simp [dotProduct]

@[simp]
theorem dotProduct_seqRhs (T : ExtensiveTree ι H Act) (i : ι)
    [Fintype {h : H i // T.OccursInfoSet i h}]
    (q : Option {h : H i // T.OccursInfoSet i h} → ℝ) :
    q ⬝ᵥ seqRhs T i = q none := by
  rw [dotProduct_comm, seqRhs_dotProduct]

private theorem max_sub_max_neg (a : ℝ) : max a 0 - max (-a) 0 = a := by
  rcases le_total a 0 with h | h <;> simp [h]

open Classical in
/-- **Sequence-form linear programming strong duality** ([vonStengel2007], Section 3.11, p. 73):
under perfect recall, maximizing `b ⬝ᵥ x` over `T.IsRealizationPlan i x` and minimizing
`seqRhs T i ⬝ᵥ q` (= `q none`) over dual multipliers `b ≤ (seqMat T i)ᵀ *ᵥ q` attain equal
optima. -/
theorem exists_isGreatest_isLeast_seqLP [DecidableEq ι] [∀ j h, Fintype (Act j h)]
    [∀ j h, Nonempty (Act j h)] {T : ExtensiveTree ι H Act} {i : ι} [Fintype (H i)]
    (hpr : T.PerfectRecall i) (b : SeqVar T i → ℝ) :
    ∃ v, IsGreatest ((b ⬝ᵥ ·) '' {x | T.IsRealizationPlan i x}) v ∧
      IsLeast ((seqRhs T i ⬝ᵥ ·) '' {q | b ≤ (seqMat T i)ᵀ *ᵥ q}) v := by
  classical
  let E := seqMat T i
  let e := seqRhs T i
  let s₀ : PureStrategy H Act i := fun _ => Classical.arbitrary _
  let x₀ := T.pureToRealizationPlan i s₀
  have hx₀ : T.IsRealizationPlan i x₀ := isRealizationPlan_pureToRealizationPlan hpr s₀
  obtain ⟨q₀, hq₀⟩ := exists_seqMat_transpose_mulVec_ge hpr b
  let A := fromRows E (-E)
  let rhs := Sum.elim e (-e)
  have hP : ∃ x, 0 ≤ x ∧ A *ᵥ x ≤ rhs := by
    refine ⟨x₀, fun σ => hx₀.1 σ, ?_⟩
    rw [fromRows_mulVec, neg_mulVec, Sum.elim_le_elim_iff]
    exact ⟨le_of_eq hx₀.2, neg_le_neg (le_of_eq hx₀.2.symm)⟩
  have hdualLift : ∀ q : Option {h : H i // T.OccursInfoSet i h} → ℝ,
      b ≤ Eᵀ *ᵥ q →
      ∃ y : _ → ℝ, (0 ≤ y ∧ b ≤ y ᵥ* A) ∧ y ⬝ᵥ rhs = e ⬝ᵥ q := by
    intro q hq
    let y : _ → ℝ := Sum.elim (fun r => max (q r) 0) (fun r => max (-q r) 0)
    refine ⟨y, ⟨fun r => by cases r <;> simp [y], ?_⟩, ?_⟩
    · rw [vecMul_fromRows, vecMul_neg, ← sub_eq_add_neg, ← sub_vecMul]
      have hcomp : y ∘ Sum.inl - y ∘ Sum.inr = q := by
        ext r; exact max_sub_max_neg (q r)
      rw [hcomp, ← Matrix.mulVec_transpose]
      exact hq
    · rw [dotProduct, dotProduct, Fintype.sum_sum_type]
      simp only [y, rhs, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply]
      rw [← sum_add_distrib]
      refine sum_congr rfl fun r _ => ?_
      conv_rhs => rw [← max_sub_max_neg (q r)]
      ring
  have hD : ∃ y, 0 ≤ y ∧ b ≤ y ᵥ* A := by
    obtain ⟨y, hy, _⟩ := hdualLift q₀ hq₀
    exact ⟨y, hy⟩
  obtain ⟨v, ⟨⟨xOpt, ⟨hxOpt_nn, hxOpt_le⟩, hvx⟩, hmax⟩,
      ⟨⟨yOpt, ⟨hyOpt_nn, hyOpt_le⟩, hvy⟩, hmin⟩⟩ :=
    Matrix.exists_isGreatest_isLeast_dotProduct_of_nonneg A rhs b hP hD
  have hAx_iff : ∀ x, (0 ≤ x ∧ A *ᵥ x ≤ rhs) ↔ T.IsRealizationPlan i x := by
    intro x
    rw [fromRows_mulVec, neg_mulVec, Sum.elim_le_elim_iff]
    refine ⟨fun ⟨hnn, h1, h2⟩ => ⟨hnn, le_antisymm h1 (neg_le_neg_iff.1 h2)⟩,
      fun ⟨hnn, heq⟩ => ⟨hnn, le_of_eq heq, neg_le_neg (le_of_eq heq.symm)⟩⟩
  let qOpt : Option {h : H i // T.OccursInfoSet i h} → ℝ :=
    fun r => yOpt (.inl r) - yOpt (.inr r)
  have hqOpt_eq : yOpt = Sum.elim (fun r => yOpt (.inl r)) (fun r => yOpt (.inr r)) := by
    ext r; cases r <;> rfl
  have hqOpt_feas : b ≤ Eᵀ *ᵥ qOpt := by
    rw [Matrix.mulVec_transpose]
    have hvec : qOpt ᵥ* E = yOpt ᵥ* A := by
      conv_rhs => rw [hqOpt_eq, vecMul_fromRows, vecMul_neg, ← sub_eq_add_neg, ← sub_vecMul]
      rfl
    simpa only [hvec] using hyOpt_le
  have hqOpt_obj : e ⬝ᵥ qOpt = yOpt ⬝ᵥ rhs := by
    conv_rhs => rw [hqOpt_eq]
    rw [dotProduct, dotProduct, Fintype.sum_sum_type]
    simp only [qOpt, rhs, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply]
    rw [← sum_add_distrib]
    refine sum_congr rfl fun r _ => ?_
    ring
  refine ⟨v, ⟨⟨xOpt, (hAx_iff xOpt).1 ⟨hxOpt_nn, hxOpt_le⟩, hvx⟩, ?_⟩,
      ⟨⟨qOpt, hqOpt_feas, hqOpt_obj.trans hvy⟩, ?_⟩⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hmax ⟨x, (hAx_iff x).2 hx, rfl⟩
  · rintro _ ⟨q, hq, rfl⟩
    obtain ⟨y, hy, hyobj⟩ := hdualLift q hq
    change v ≤ e ⬝ᵥ q
    rw [← hyobj]
    exact hmin ⟨y, hy, rfl⟩

open Classical in
private theorem isRealizationPlan_max_iff_dual [DecidableEq ι] [∀ j h, Fintype (Act j h)]
    [∀ j h, Nonempty (Act j h)] {T : ExtensiveTree ι H Act} {i : ι} [Fintype (H i)]
    (hpr : T.PerfectRecall i) (x c : SeqVar T i → ℝ) :
    (T.IsRealizationPlan i x ∧ ∀ x', T.IsRealizationPlan i x' → c ⬝ᵥ x' ≤ c ⬝ᵥ x) ↔
      T.IsRealizationPlan i x ∧
        ∃ q : Option {h : H i // T.OccursInfoSet i h} → ℝ,
          c ≤ (seqMat T i)ᵀ *ᵥ q ∧ ∀ σ, x σ = 0 ∨ ((seqMat T i)ᵀ *ᵥ q) σ = c σ := by
  classical
  have hweak : ∀ (x' : SeqVar T i → ℝ) (q : Option {h : H i // T.OccursInfoSet i h} → ℝ),
      T.IsRealizationPlan i x' → c ≤ (seqMat T i)ᵀ *ᵥ q → c ⬝ᵥ x' ≤ q none := by
    intro x' q ⟨hx'nn, hx'eq⟩ hq
    calc c ⬝ᵥ x' = x' ⬝ᵥ c := dotProduct_comm _ _
      _ ≤ x' ⬝ᵥ ((seqMat T i)ᵀ *ᵥ q) := dotProduct_le_dotProduct_of_nonneg_left hq hx'nn
      _ = (seqMat T i *ᵥ x') ⬝ᵥ q := by rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
      _ = seqRhs T i ⬝ᵥ q := by rw [hx'eq]
      _ = q none := seqRhs_dotProduct T i q
  constructor
  · rintro ⟨hx, hbest⟩
    obtain ⟨v, hvP, hvD⟩ := exists_isGreatest_isLeast_seqLP hpr c
    obtain ⟨q, hq, hvq⟩ := hvD.1
    have hv_eq : c ⬝ᵥ x = v := by
      have hx_le : c ⬝ᵥ x ≤ v := hvP.2 ⟨x, hx, rfl⟩
      obtain ⟨xMax, hxMax, hvx⟩ := hvP.1
      have hmax_le : v ≤ c ⬝ᵥ x := by
        dsimp only at hvx
        rw [← hvx]
        exact hbest xMax hxMax
      exact le_antisymm hx_le hmax_le
    dsimp only at hvq
    rw [seqRhs_dotProduct] at hvq
    have hgap0 : ∑ σ : SeqVar T i, x σ * (((seqMat T i)ᵀ *ᵥ q) σ - c σ) = 0 := by
      have hxEq : x ⬝ᵥ ((seqMat T i)ᵀ *ᵥ q) = q none := by
        rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, hx.2, seqRhs_dotProduct]
      have hdot : x ⬝ᵥ ((seqMat T i)ᵀ *ᵥ q - c) = 0 := by
        rw [dotProduct_sub, hxEq, hvq, dotProduct_comm x c, hv_eq, sub_self]
      exact hdot
    have hterm_nn : ∀ σ ∈ univ, 0 ≤ x σ * (((seqMat T i)ᵀ *ᵥ q) σ - c σ) := fun σ _ =>
      mul_nonneg (hx.1 σ) (sub_nonneg.2 (hq σ))
    refine ⟨hx, q, hq, fun σ => ?_⟩
    have hz := (sum_eq_zero_iff_of_nonneg hterm_nn).1 hgap0 σ (mem_univ σ)
    rcases mul_eq_zero.1 hz with h0 | h0
    · exact .inl h0
    · exact .inr (sub_eq_zero.1 h0)
  · rintro ⟨hx, q, hq, hcs⟩
    refine ⟨hx, fun x' hx' => ?_⟩
    have hxEq : x ⬝ᵥ ((seqMat T i)ᵀ *ᵥ q) = q none := by
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, hx.2, seqRhs_dotProduct]
    have hmatch : c ⬝ᵥ x = q none := by
      rw [← hxEq, dotProduct_comm c x]
      refine sum_congr rfl fun σ _ => ?_
      rcases hcs σ with h0 | heq
      · simp [h0]
      · rw [heq]
    exact hmatch ▸ hweak x' q hx' hq

end SequenceLP

section TwoPlayerEquilibrium

variable {H : Bool → Type v} {Act : ∀ i, H i → Type}

open Classical in
/-- `x` is a **sequence-form best response** for player `false` to player `true`'s strategy `y`.
-/
@[expose] noncomputable def ExtensiveTree.IsSeqBestResponseFalse [∀ i h, Fintype (Act i h)]
    (T : ExtensiveTree Bool H Act) (x : SeqVar T false → ℝ) (y : SeqVar T true → ℝ) : Prop :=
  T.IsRealizationPlan false x ∧
    ∀ x', T.IsRealizationPlan false x' →
      x' ⬝ᵥ (T.seqPayoffMat false *ᵥ y) ≤ x ⬝ᵥ (T.seqPayoffMat false *ᵥ y)

open Classical in
/-- `y` is a **sequence-form best response** for player `true` to player `false`'s strategy `x`.
-/
@[expose] noncomputable def ExtensiveTree.IsSeqBestResponseTrue [∀ i h, Fintype (Act i h)]
    (T : ExtensiveTree Bool H Act) (y : SeqVar T true → ℝ) (x : SeqVar T false → ℝ) : Prop :=
  T.IsRealizationPlan true y ∧
    ∀ y', T.IsRealizationPlan true y' →
      x ⬝ᵥ (T.seqPayoffMat true *ᵥ y') ≤ x ⬝ᵥ (T.seqPayoffMat true *ᵥ y)

open Classical in
/-- A pair `(x, y)` of realization plans is a **sequence-form Nash equilibrium**
([vonStengel2007], Sections 3.10–3.11) if each plan maximizes its bilinear payoff against the
other. -/
@[expose] noncomputable def ExtensiveTree.IsSeqNash [∀ i h, Fintype (Act i h)]
    (T : ExtensiveTree Bool H Act) (x : SeqVar T false → ℝ) (y : SeqVar T true → ℝ) : Prop :=
  T.IsSeqBestResponseFalse x y ∧ T.IsSeqBestResponseTrue y x

open Classical in
/-- A behavioral strategy profile `β` is a **behavioral Nash equilibrium** if every player plays
a valid behavior strategy and no unilateral deviation to another behavior strategy strictly
increases expected payoff. -/
@[expose] def ExtensiveTree.IsBehaviorNash [∀ i h, Fintype (Act i h)]
    (T : ExtensiveTree Bool H Act) (β : ∀ i, ∀ h : H i, Act i h → ℝ) : Prop :=
  (∀ i, IsBehaviorStrategy (β i)) ∧
    ∀ i (β' : ∀ h : H i, Act i h → ℝ), IsBehaviorStrategy β' →
      T.evalBehavior (Function.update β i β') i ≤ T.evalBehavior β i

open Classical in
/-- **Complementarity / KKT characterization of sequence-form best response** for player `false`
([vonStengel2007], Section 3.11, pp. 73–74): under perfect recall, `x` is a sequence-form best
response to `y` iff `x` is a valid realization plan and there exists an information-set multiplier
vector `q` satisfying dual feasibility `T.seqPayoffMat false *ᵥ y ≤ (seqMat T false)ᵀ *ᵥ q` and
complementary slackness. -/
theorem isSeqBestResponseFalse_iff_dual [∀ i h, Fintype (Act i h)] [∀ i h, Nonempty (Act i h)]
    {T : ExtensiveTree Bool H Act} [Fintype (H false)] (hpr : T.PerfectRecall false)
    (x : SeqVar T false → ℝ) (y : SeqVar T true → ℝ) :
    T.IsSeqBestResponseFalse x y ↔
      T.IsRealizationPlan false x ∧
        ∃ q : Option {h : H false // T.OccursInfoSet false h} → ℝ,
          T.seqPayoffMat false *ᵥ y ≤ (seqMat T false)ᵀ *ᵥ q ∧
            ∀ σ, x σ = 0 ∨ ((seqMat T false)ᵀ *ᵥ q) σ = (T.seqPayoffMat false *ᵥ y) σ := by
  have heq : T.IsSeqBestResponseFalse x y ↔
      (T.IsRealizationPlan false x ∧
        ∀ x', T.IsRealizationPlan false x' →
          (T.seqPayoffMat false *ᵥ y) ⬝ᵥ x' ≤ (T.seqPayoffMat false *ᵥ y) ⬝ᵥ x) := by
    simp [ExtensiveTree.IsSeqBestResponseFalse, dotProduct_comm]
  rw [heq]
  exact isRealizationPlan_max_iff_dual hpr x (T.seqPayoffMat false *ᵥ y)

open Classical in
/-- **Complementarity / KKT characterization of sequence-form best response** for player `true`
([vonStengel2007], Section 3.11, p. 74). -/
theorem isSeqBestResponseTrue_iff_dual [∀ i h, Fintype (Act i h)] [∀ i h, Nonempty (Act i h)]
    {T : ExtensiveTree Bool H Act} [Fintype (H true)] (hpr : T.PerfectRecall true)
    (y : SeqVar T true → ℝ) (x : SeqVar T false → ℝ) :
    T.IsSeqBestResponseTrue y x ↔
      T.IsRealizationPlan true y ∧
        ∃ p : Option {h : H true // T.OccursInfoSet true h} → ℝ,
          (T.seqPayoffMat true)ᵀ *ᵥ x ≤ (seqMat T true)ᵀ *ᵥ p ∧
            ∀ τ, y τ = 0 ∨ ((seqMat T true)ᵀ *ᵥ p) τ = ((T.seqPayoffMat true)ᵀ *ᵥ x) τ := by
  have hobj_eq : ∀ y' : SeqVar T true → ℝ,
      x ⬝ᵥ (T.seqPayoffMat true *ᵥ y') = ((T.seqPayoffMat true)ᵀ *ᵥ x) ⬝ᵥ y' := fun y' => by
    rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]
  have heq : T.IsSeqBestResponseTrue y x ↔
      (T.IsRealizationPlan true y ∧
        ∀ y', T.IsRealizationPlan true y' →
          ((T.seqPayoffMat true)ᵀ *ᵥ x) ⬝ᵥ y' ≤ ((T.seqPayoffMat true)ᵀ *ᵥ x) ⬝ᵥ y) := by
    simp only [ExtensiveTree.IsSeqBestResponseTrue, hobj_eq]
  rw [heq]
  exact isRealizationPlan_max_iff_dual hpr y ((T.seqPayoffMat true)ᵀ *ᵥ x)

open Classical in
/-- **Sequence-form complementarity / LCP characterization of two-player Nash equilibria**
([vonStengel2007], Theorem 3.14, Section 3.11, p. 74): `(x, y)` is a sequence-form Nash equilibrium
iff `(x, y)` are valid realization plans paired with dual multipliers `(q, p)` satisfying dual
feasibility and complementary slackness. -/
theorem isSeqNash_iff_complementarity [∀ i h, Fintype (Act i h)] [∀ i h, Nonempty (Act i h)]
    {T : ExtensiveTree Bool H Act} [Fintype (H false)] [Fintype (H true)]
    (hpr : ∀ i, T.PerfectRecall i) (x : SeqVar T false → ℝ) (y : SeqVar T true → ℝ) :
    T.IsSeqNash x y ↔
      T.IsRealizationPlan false x ∧ T.IsRealizationPlan true y ∧
        ∃ (q : Option {h : H false // T.OccursInfoSet false h} → ℝ)
          (p : Option {h : H true // T.OccursInfoSet true h} → ℝ),
          T.seqPayoffMat false *ᵥ y ≤ (seqMat T false)ᵀ *ᵥ q ∧
            (T.seqPayoffMat true)ᵀ *ᵥ x ≤ (seqMat T true)ᵀ *ᵥ p ∧
            (∀ σ, x σ = 0 ∨ ((seqMat T false)ᵀ *ᵥ q) σ = (T.seqPayoffMat false *ᵥ y) σ) ∧
            (∀ τ, y τ = 0 ∨ ((seqMat T true)ᵀ *ᵥ p) τ = ((T.seqPayoffMat true)ᵀ *ᵥ x) τ) := by
  rw [ExtensiveTree.IsSeqNash, isSeqBestResponseFalse_iff_dual (hpr false),
    isSeqBestResponseTrue_iff_dual (hpr true)]
  constructor
  · rintro ⟨⟨hx, q, hq, hcsx⟩, ⟨hy, p, hp, hcsy⟩⟩
    exact ⟨hx, hy, q, p, hq, hp, hcsx, hcsy⟩
  · rintro ⟨hx, hy, q, p, hq, hp, hcsx, hcsy⟩
    exact ⟨⟨hx, q, hq, hcsx⟩, ⟨hy, p, hp, hcsy⟩⟩

/-- **Mixed Nash equilibria equal sequence-form Nash equilibria** ([vonStengel2007], §3.10): under
perfect recall for both players, a mixed strategy profile `μ` is a mixed Nash equilibrium of
`T.toCostGame` iff its induced realization plans `(x, y)` form a sequence-form Nash equilibrium. -/
theorem isMixedNash_toCostGame_iff_isSeqNash [∀ i, Fintype (H i)] [∀ i, DecidableEq (H i)]
    [∀ i h, Fintype (Act i h)] [∀ i h, Nonempty (Act i h)] {T : ExtensiveTree Bool H Act}
    (hpr : ∀ i, T.PerfectRecall i) (μ : ∀ i, PureStrategy H Act i → ℝ) :
    T.toCostGame.IsMixedNash μ ↔
      (∀ i, IsMixedStrategy (μ i)) ∧
        T.IsSeqNash (T.mixedToRealizationPlan false (μ false))
          (T.mixedToRealizationPlan true (μ true)) := by
  classical
  constructor
  · rintro ⟨hmix, hopt⟩
    refine ⟨hmix, ?_⟩
    have hnash := CostGame.IsMixedNash.expectedCost_le_update ⟨hmix, hopt⟩
    refine ⟨⟨isRealizationPlan_mixedToRealizationPlan (hpr false) (hmix false), fun x' hx' => ?_⟩,
        ⟨isRealizationPlan_mixedToRealizationPlan (hpr true) (hmix true), fun y' hy' => ?_⟩⟩
    · obtain ⟨μ', hμ', hplan'⟩ := exists_mixed_of_isRealizationPlan (hpr false) hx'
      have hdev := hnash false hμ'
      rw [T.toCostGame_expectedCost, T.toCostGame_expectedCost, neg_le_neg_iff] at hdev
      rw [evalMixed_eq_seqPayoffMat, evalMixed_eq_seqPayoffMat] at hdev
      simpa only [Function.update_self, Function.update_of_ne (by decide : (true : Bool) ≠ false),
        hplan'] using hdev
    · obtain ⟨μ', hμ', hplan'⟩ := exists_mixed_of_isRealizationPlan (hpr true) hy'
      have hdev := hnash true hμ'
      rw [T.toCostGame_expectedCost, T.toCostGame_expectedCost, neg_le_neg_iff] at hdev
      rw [evalMixed_eq_seqPayoffMat, evalMixed_eq_seqPayoffMat] at hdev
      simpa only [Function.update_self, Function.update_of_ne (by decide : (false : Bool) ≠ true),
        hplan'] using hdev
  · rintro ⟨hmix, hbr0, hbr1⟩
    refine ⟨hmix, fun i s => ?_⟩
    have hupdate_eval : T.toCostGame.deviationCost μ i s =
        T.toCostGame.expectedCost (Function.update μ i (Pi.single s (1 : ℝ))) i := by
      have hsum_s : ∑ b, (Pi.single (M := fun _ => ℝ) s (1 : ℝ)) b = ∑ b, μ i b := by
        rw [sum_eq_single s (fun _ _ hb => Pi.single_eq_of_ne hb _)
          (fun h => absurd (mem_univ s) h), Pi.single_eq_same, (hmix i).sum_eq_one]
      have hsum_upd : ∑ b, Function.update μ i (Pi.single s (1 : ℝ)) i b = 1 := by
        rw [Function.update_self, hsum_s, (hmix i).sum_eq_one]
      rw [← CostGame.sum_mul_deviationCost_eq_expectedCost T.toCostGame
        (Function.update μ i (Pi.single s (1 : ℝ))) hsum_upd]
      have hdev_upd : ∀ b,
          T.toCostGame.deviationCost (Function.update μ i (Pi.single s (1 : ℝ))) i b =
            T.toCostGame.deviationCost μ i b := fun b =>
        CostGame.deviationCost_update_self T.toCostGame μ hsum_s b
      simp_rw [hdev_upd]
      rw [Function.update_self]
      simp [Pi.single_apply]
    rw [hupdate_eval, T.toCostGame_expectedCost, T.toCostGame_expectedCost, neg_le_neg_iff]
    cases i with
    | false =>
      rw [evalMixed_eq_seqPayoffMat, evalMixed_eq_seqPayoffMat]
      simp only [Function.update_self, Function.update_of_ne (by decide : (true : Bool) ≠ false)]
      exact hbr0.2 _
        (isRealizationPlan_mixedToRealizationPlan (hpr false) (isMixedStrategy_single s))
    | true =>
      rw [evalMixed_eq_seqPayoffMat, evalMixed_eq_seqPayoffMat]
      simp only [Function.update_self, Function.update_of_ne (by decide : (false : Bool) ≠ true)]
      exact hbr1.2 _
        (isRealizationPlan_mixedToRealizationPlan (hpr true) (isMixedStrategy_single s))

/-- **Behavioral Nash equilibria equal sequence-form Nash equilibria** ([vonStengel2007], §3.10):
under perfect recall for both players, `β` is a behavioral Nash equilibrium iff its induced
realization plans form a sequence-form Nash equilibrium. -/
theorem isBehaviorNash_iff_isSeqNash [∀ i h, Fintype (Act i h)] [∀ i h, Nonempty (Act i h)]
    {T : ExtensiveTree Bool H Act} (hpr : ∀ i, T.PerfectRecall i)
    (β : ∀ i, ∀ h : H i, Act i h → ℝ) :
    T.IsBehaviorNash β ↔
      (∀ i, IsBehaviorStrategy (β i)) ∧
        T.IsSeqNash (T.behaviorToRealizationPlan false (β false))
          (T.behaviorToRealizationPlan true (β true)) := by
  classical
  constructor
  · rintro ⟨hbeh, hopt⟩
    refine ⟨hbeh, ?_⟩
    refine ⟨⟨isRealizationPlan_behaviorToRealizationPlan (hpr false) (hbeh false),
          fun x' hx' => ?_⟩,
        ⟨isRealizationPlan_behaviorToRealizationPlan (hpr true) (hbeh true),
          fun y' hy' => ?_⟩⟩
    · let β' := T.realizationPlanToBehavior false (hpr false) x'
      have hβ' := isBehaviorStrategy_realizationPlanToBehavior (hpr false) hx'
      have hreal' := behaviorToRealizationPlan_realizationPlanToBehavior (hpr false) hx'
      have hdev := hopt false β' hβ'
      rw [evalBehavior_eq_seqPayoffMat, evalBehavior_eq_seqPayoffMat] at hdev
      have hup0 : Function.update β false β' false = β' := Function.update_self _ _ _
      have hup1 : Function.update β false β' true = β true :=
        Function.update_of_ne (by decide) _ _
      rw [hup0, hup1, hreal'] at hdev
      exact hdev
    · let β' := T.realizationPlanToBehavior true (hpr true) y'
      have hβ' := isBehaviorStrategy_realizationPlanToBehavior (hpr true) hy'
      have hreal' := behaviorToRealizationPlan_realizationPlanToBehavior (hpr true) hy'
      have hdev := hopt true β' hβ'
      rw [evalBehavior_eq_seqPayoffMat, evalBehavior_eq_seqPayoffMat] at hdev
      have hup0 : Function.update β true β' false = β false :=
        Function.update_of_ne (by decide) _ _
      have hup1 : Function.update β true β' true = β' := Function.update_self _ _ _
      rw [hup0, hup1, hreal'] at hdev
      exact hdev
  · rintro ⟨hbeh, hbr0, hbr1⟩
    refine ⟨hbeh, fun i β' hβ' => ?_⟩
    cases i with
    | false =>
      rw [evalBehavior_eq_seqPayoffMat, evalBehavior_eq_seqPayoffMat]
      have hup0 : Function.update β false β' false = β' := Function.update_self _ _ _
      have hup1 : Function.update β false β' true = β true :=
        Function.update_of_ne (by decide) _ _
      rw [hup0, hup1]
      exact hbr0.2 _ (isRealizationPlan_behaviorToRealizationPlan (hpr false) hβ')
    | true =>
      rw [evalBehavior_eq_seqPayoffMat, evalBehavior_eq_seqPayoffMat]
      have hup0 : Function.update β true β' false = β false :=
        Function.update_of_ne (by decide) _ _
      have hup1 : Function.update β true β' true = β' := Function.update_self _ _ _
      rw [hup0, hup1]
      exact hbr1.2 _ (isRealizationPlan_behaviorToRealizationPlan (hpr true) hβ')

/-- Existence of a sequence-form Nash equilibrium in any finite two-player extensive game with
perfect recall ([vonStengel2007], Sections 3.10–3.11). -/
theorem exists_isSeqNash [∀ i, Finite (H i)] [∀ i h, Fintype (Act i h)]
    [∀ i h, Nonempty (Act i h)] {T : ExtensiveTree Bool H Act}
    (hpr : ∀ i, T.PerfectRecall i) :
    ∃ x y, T.IsSeqNash x y := by
  classical
  let _ : ∀ i, Fintype (H i) := fun i => Fintype.ofFinite (H i)
  obtain ⟨μ, hμ⟩ := CostGame.exists_isMixedNash (G := T.toCostGame)
  exact ⟨_, _, ((isMixedNash_toCostGame_iff_isSeqNash hpr μ).1 hμ).2⟩

private theorem isBehaviorNash_of_isSeqNash [∀ i h, Fintype (Act i h)]
    [∀ i h, Nonempty (Act i h)] {T : ExtensiveTree Bool H Act} (hpr : ∀ i, T.PerfectRecall i)
    {x : SeqVar T false → ℝ} {y : SeqVar T true → ℝ} (hnash : T.IsSeqNash x y) :
    ∃ β : ∀ i, ∀ h : H i, Act i h → ℝ,
      T.IsBehaviorNash β ∧ T.evalBehavior β false = x ⬝ᵥ (T.seqPayoffMat false *ᵥ y) := by
  let β : ∀ i, ∀ h : H i, Act i h → ℝ := fun
    | false => T.realizationPlanToBehavior false (hpr false) x
    | true => T.realizationPlanToBehavior true (hpr true) y
  have hbeh : ∀ i, IsBehaviorStrategy (β i) := fun
    | false => isBehaviorStrategy_realizationPlanToBehavior (hpr false) hnash.1.1
    | true => isBehaviorStrategy_realizationPlanToBehavior (hpr true) hnash.2.1
  have hx_eq : T.behaviorToRealizationPlan false (β false) = x :=
    behaviorToRealizationPlan_realizationPlanToBehavior (hpr false) hnash.1.1
  have hy_eq : T.behaviorToRealizationPlan true (β true) = y :=
    behaviorToRealizationPlan_realizationPlanToBehavior (hpr true) hnash.2.1
  refine ⟨β, (isBehaviorNash_iff_isSeqNash hpr β).2 ⟨hbeh, ?_⟩, ?_⟩
  · rw [hx_eq, hy_eq]
    exact hnash
  · rw [evalBehavior_eq_seqPayoffMat, hx_eq, hy_eq]

/-- Existence of a behavioral Nash equilibrium in any finite two-player extensive game with
perfect recall. -/
theorem exists_isBehaviorNash [∀ i, Finite (H i)] [∀ i h, Fintype (Act i h)]
    [∀ i h, Nonempty (Act i h)] {T : ExtensiveTree Bool H Act}
    (hpr : ∀ i, T.PerfectRecall i) :
    ∃ β : ∀ i, ∀ h : H i, Act i h → ℝ, T.IsBehaviorNash β := by
  obtain ⟨_, _, hseq⟩ := exists_isSeqNash hpr
  obtain ⟨β, hβ, _⟩ := isBehaviorNash_of_isSeqNash hpr hseq
  exact ⟨β, hβ⟩

end TwoPlayerEquilibrium

section ZeroSumLP

variable {H : Bool → Type v} {Act : ∀ i, H i → Type}

/-- A two-player extensive-form game is **zero-sum** ([vonStengel2007], Section 3.11, p. 73) if the
players' payoffs sum to `0` at every terminal leaf. -/
@[expose] def ExtensiveTree.IsZeroSum (T : ExtensiveTree Bool H Act) : Prop :=
  ∀ z : Terminal T, z.payoff false + z.payoff true = 0

namespace ExtensiveTree.IsZeroSum

open Classical in
private theorem realizationProbBehavior_eq_one_of_forall {i : Bool}
    (β : ∀ h : H i, Act i h → ℝ) :
    ∀ {l : Seq H Act i}, (∀ p ∈ l, β p.1 p.2 = 1) → realizationProbBehavior β l = 1
  | [], _ => by simp
  | p :: l, hl => by
      rw [realizationProbBehavior_cons, hl p List.mem_cons_self, one_mul]
      exact realizationProbBehavior_eq_one_of_forall β fun q hq =>
        hl q (List.mem_cons_of_mem _ hq)

open Classical in
private theorem realizationProbBehavior_eq_zero_of_exists {i : Bool}
    (β : ∀ h : H i, Act i h → ℝ) :
    ∀ {l : Seq H Act i} {q : Choice H Act i},
      q ∈ l → β q.1 q.2 = 0 → realizationProbBehavior β l = 0
  | [], _, hmem, _ => False.elim (List.not_mem_nil hmem)
  | p :: l, q, hmem, hq0 => by
      rw [realizationProbBehavior_cons]
      rcases List.mem_cons.1 hmem with rfl | hmem'
      · rw [hq0, zero_mul]
      · rw [realizationProbBehavior_eq_zero_of_exists β hmem' hq0, mul_zero]

open Classical in
private theorem realizationProbBehavior_congr {i : Bool}
    (β₁ β₀ : ∀ h : H i, Act i h → ℝ) :
    ∀ {l : Seq H Act i},
      (∀ p ∈ l, β₁ p.1 p.2 = β₀ p.1 p.2) →
      realizationProbBehavior β₁ l = realizationProbBehavior β₀ l
  | [], _ => by simp
  | p :: l, h => by
      rw [realizationProbBehavior_cons, realizationProbBehavior_cons,
        h p List.mem_cons_self,
        realizationProbBehavior_congr β₁ β₀ fun q hq => h q (List.mem_cons_of_mem _ hq)]

open Classical in
private theorem exists_behavior_diff_eq_single [∀ i h, Nonempty (Act i h)]
    {T : ExtensiveTree Bool H Act} {i : Bool} (hpr : T.PerfectRecall i) (σ : SeqVar T i) :
    (σ.1 = [] ∧ T.behaviorToRealizationPlan i (fun _ _ => 0) = Pi.single σ (1 : ℝ)) ∨
      ∃ β₁ β₀ : ∀ h : H i, Act i h → ℝ,
        T.behaviorToRealizationPlan i β₁ - T.behaviorToRealizationPlan i β₀ =
          Pi.single σ (1 : ℝ) := by
  by_cases hnil : σ.1 = []
  · refine .inl ⟨hnil, ?_⟩
    ext τ
    simp only [ExtensiveTree.behaviorToRealizationPlan_apply, Pi.single_apply]
    by_cases hτ : τ = σ
    · subst hτ
      simp [hnil]
    · have hτ_ne : τ.1 ≠ [] := fun h => hτ (Subtype.ext (h.trans hnil.symm))
      cases ht : τ.1 with
      | nil => exact absurd ht hτ_ne
      | cons q tl => simp [hτ]
  · refine .inr ?_
    obtain ⟨⟨h₀, hh₀⟩, a₀, rfl⟩ := exists_infoSeqExt_of_seqVar_ne_nil hpr σ hnil
    let target : Seq H Act i := T.infoSeq i h₀ ++ [⟨h₀, a₀⟩]
    let β₁ : ∀ h : H i, Act i h → ℝ := fun h a =>
      if (⟨h, a⟩ : Choice H Act i) ∈ target then 1 else 0
    let β₀ : ∀ h : H i, Act i h → ℝ := fun h a =>
      if (⟨h, a⟩ : Choice H Act i) ∈ target ∧ (⟨h, a⟩ : Choice H Act i) ≠ ⟨h₀, a₀⟩ then 1 else 0
    refine ⟨β₁, β₀, ?_⟩
    ext τ
    simp only [Pi.sub_apply, ExtensiveTree.behaviorToRealizationPlan_apply, Pi.single_apply]
    by_cases hτ : τ = SeqVar.infoSeqExt hpr hh₀ a₀
    · rw [hτ]
      simp only [↓reduceIte, SeqVar.infoSeqExt_val]
      have hprod1 : realizationProbBehavior β₁ target = 1 :=
        realizationProbBehavior_eq_one_of_forall β₁ fun p hp => by simp [β₁, hp]
      have hprod0 : realizationProbBehavior β₀ target = 0 :=
        realizationProbBehavior_eq_zero_of_exists β₀
          (by simp [target] : (⟨h₀, a₀⟩ : Choice H Act i) ∈ target) (by simp [β₀])
      change realizationProbBehavior β₁ target - realizationProbBehavior β₀ target = 1
      rw [hprod1, hprod0, sub_zero]
    · simp only [hτ, ↓reduceIte]
      by_cases hall : ∀ p ∈ τ.1, p ∈ target
      · by_cases hmem : (⟨h₀, a₀⟩ : Choice H Act i) ∈ τ.1
        · exfalso
          obtain ⟨pre, post, hsplit⟩ := List.mem_iff_append.1 hmem
          obtain ⟨z, rem, hz⟩ := τ.2
          have hseq : z.seq i = pre ++ ⟨h₀, a₀⟩ :: (post ++ rem) := by
            rw [← hz, hsplit, List.append_assoc, List.cons_append]
          obtain ⟨v, hv, hpre⟩ := z.exists_node_of_seq_append pre (post ++ rem) h₀ a₀ hseq
          have hpre_eq : pre = T.infoSeq i h₀ := by
            rw [← hpr.playerSeq_eq_infoSeq hv, hpre]
          have hpost_ne : post ≠ [] := by
            intro hn
            apply hτ
            apply Subtype.ext
            rw [SeqVar.infoSeqExt_val, hsplit, hn, hpre_eq]
          cases post with
          | nil => exact absurd rfl hpost_ne
          | cons q post' =>
            have hq_target : q ∈ target := hall q (by rw [hsplit]; simp)
            have hq_fst : q.1 ∈ target.map Sigma.fst := List.mem_map.2 ⟨q, hq_target, rfl⟩
            have hzn := hpr.noRepeatedInfoSet z
            rw [← hz, List.map_append] at hzn
            have hnodup : (τ.1.map Sigma.fst).Nodup := List.Nodup.of_append_left hzn
            have hsplit' : τ.1 = target ++ q :: post' := by
              rw [hsplit, hpre_eq]
              simp only [target, List.append_assoc, List.singleton_append]
            rw [hsplit', List.map_append, List.nodup_append] at hnodup
            exact hnodup.2.2 q.1 hq_fst q.1 (List.mem_cons_self) rfl
        · have heq : realizationProbBehavior β₁ τ.1 = realizationProbBehavior β₀ τ.1 :=
            realizationProbBehavior_congr β₁ β₀ fun p hp => by
              have hne : p ≠ ⟨h₀, a₀⟩ := fun h => hmem (h ▸ hp)
              rcases p with ⟨ph, pa⟩
              by_cases h1 : (⟨ph, pa⟩ : Choice H Act i) ∈ target
              · simp only [β₁, β₀, h1, true_and, ↓reduceIte]
                split_ifs with hne'
                · rfl
                · exact absurd hne hne'
              · simp [β₁, β₀, h1]
          rw [heq, sub_self]
      · push Not at hall
        obtain ⟨q, hq_mem, hq_not⟩ := hall
        have hzero1 : realizationProbBehavior β₁ τ.1 = 0 :=
          realizationProbBehavior_eq_zero_of_exists β₁ hq_mem (by simp [β₁, hq_not])
        have hzero0 : realizationProbBehavior β₀ τ.1 = 0 :=
          realizationProbBehavior_eq_zero_of_exists β₀ hq_mem (by simp [β₀, hq_not])
        rw [hzero1, hzero0, sub_self]

theorem evalBehavior_true [∀ i h, Fintype (Act i h)] {T : ExtensiveTree Bool H Act}
    (hzs : T.IsZeroSum) (β : ∀ i, ∀ h : H i, Act i h → ℝ) :
    T.evalBehavior β true = -T.evalBehavior β false := by
  rw [T.evalBehavior_eq_sum_terminal β true, T.evalBehavior_eq_sum_terminal β false,
    ← sum_neg_distrib]
  refine sum_congr rfl fun z _ => ?_
  have hpay : z.payoff true = -z.payoff false := eq_neg_of_add_eq_zero_right (hzs z)
  rw [hpay, mul_neg]

theorem evalMixed_true [∀ i, Fintype (H i)] [∀ i, DecidableEq (H i)] [∀ i h, Fintype (Act i h)]
    {T : ExtensiveTree Bool H Act} (hzs : T.IsZeroSum) (μ : ∀ i, PureStrategy H Act i → ℝ) :
    T.evalMixed μ true = -T.evalMixed μ false := by
  rw [T.evalMixed_eq_sum_terminal μ true, T.evalMixed_eq_sum_terminal μ false, ← sum_neg_distrib]
  refine sum_congr rfl fun z _ => ?_
  have hpay : z.payoff true = -z.payoff false := eq_neg_of_add_eq_zero_right (hzs z)
  rw [hpay, mul_neg]

open Classical in
theorem seqPayoffMat_true_of_perfectRecall [∀ i h, Fintype (Act i h)] [∀ i h, Nonempty (Act i h)]
    {T : ExtensiveTree Bool H Act} (hpr : ∀ i, T.PerfectRecall i) (hzs : T.IsZeroSum) :
    T.seqPayoffMat true = -T.seqPayoffMat false := by
  let Smat := T.seqPayoffMat false + T.seqPayoffMat true
  have hbilin : ∀ (β₀ : ∀ h : H false, Act false h → ℝ) (β₁ : ∀ h : H true, Act true h → ℝ),
      (T.behaviorToRealizationPlan false β₀) ⬝ᵥ
        (Smat *ᵥ T.behaviorToRealizationPlan true β₁) = 0 := by
    intro β₀ β₁
    let β : ∀ i, ∀ h : H i, Act i h → ℝ := fun | false => β₀ | true => β₁
    have h0 := evalBehavior_eq_seqPayoffMat T β false
    have h1 := evalBehavior_eq_seqPayoffMat T β true
    have hsum := hzs.evalBehavior_true β
    dsimp [β] at h0 h1 hsum
    rw [h1, h0] at hsum
    rw [add_mulVec, dotProduct_add]
    linarith
  have hright : ∀ (β₀ : ∀ h : H false, Act false h → ℝ) (σ₁ : SeqVar T true),
      (T.behaviorToRealizationPlan false β₀) ⬝ᵥ (Smat *ᵥ Pi.single σ₁ (1 : ℝ)) = 0 := by
    intro β₀ σ₁
    rcases exists_behavior_diff_eq_single (hpr true) σ₁ with ⟨_, h0⟩ | ⟨γ₁, γ₀, hdiff⟩
    · rw [← h0, hbilin β₀ (fun _ _ => 0)]
    · rw [← hdiff, mulVec_sub, dotProduct_sub, hbilin β₀ γ₁, hbilin β₀ γ₀, sub_zero]
  have hzero : ∀ (σ₀ : SeqVar T false) (σ₁ : SeqVar T true), Smat σ₀ σ₁ = 0 := by
    intro σ₀ σ₁
    have hsingle : (Pi.single σ₀ (1 : ℝ)) ⬝ᵥ (Smat *ᵥ Pi.single σ₁ (1 : ℝ)) = Smat σ₀ σ₁ := by
      simp
    rw [← hsingle]
    rcases exists_behavior_diff_eq_single (hpr false) σ₀ with ⟨_, h0⟩ | ⟨β₁, β₀, hdiff⟩
    · rw [← h0, hright _ σ₁]
    · rw [← hdiff, sub_dotProduct, hright β₁ σ₁, hright β₀ σ₁, sub_zero]
  ext σ₀ σ₁
  have h := hzero σ₀ σ₁
  simp only [Smat, Matrix.add_apply] at h
  simp only [Matrix.neg_apply]
  linarith

open Classical in
private theorem seq_weak_duality_lower [∀ i h, Fintype (Act i h)] {T : ExtensiveTree Bool H Act}
    [Fintype (H true)]
    {x : SeqVar T false → ℝ} {y : SeqVar T true → ℝ}
    {q : Option {h : H true // T.OccursInfoSet true h} → ℝ}
    (hy : T.IsRealizationPlan true y)
    (hq : (seqMat T true)ᵀ *ᵥ q ≤ (T.seqPayoffMat false)ᵀ *ᵥ x) :
    q none ≤ x ⬝ᵥ (T.seqPayoffMat false *ᵥ y) := by
  calc q none = seqRhs T true ⬝ᵥ q := (seqRhs_dotProduct T true q).symm
    _ = (seqMat T true *ᵥ y) ⬝ᵥ q := by rw [hy.2]
    _ = y ⬝ᵥ ((seqMat T true)ᵀ *ᵥ q) := by
        rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    _ ≤ y ⬝ᵥ ((T.seqPayoffMat false)ᵀ *ᵥ x) :=
        dotProduct_le_dotProduct_of_nonneg_left hq hy.1
    _ = x ⬝ᵥ (T.seqPayoffMat false *ᵥ y) := by
        rw [Matrix.mulVec_transpose, dotProduct_comm, Matrix.dotProduct_mulVec]

open Classical in
private theorem seq_weak_duality_upper [∀ i h, Fintype (Act i h)] {T : ExtensiveTree Bool H Act}
    [Fintype (H false)]
    {x : SeqVar T false → ℝ} {y : SeqVar T true → ℝ}
    {p : Option {h : H false // T.OccursInfoSet false h} → ℝ}
    (hx : T.IsRealizationPlan false x)
    (hp : T.seqPayoffMat false *ᵥ y ≤ (seqMat T false)ᵀ *ᵥ p) :
    x ⬝ᵥ (T.seqPayoffMat false *ᵥ y) ≤ p none := by
  calc x ⬝ᵥ (T.seqPayoffMat false *ᵥ y)
      ≤ x ⬝ᵥ ((seqMat T false)ᵀ *ᵥ p) := dotProduct_le_dotProduct_of_nonneg_left hp hx.1
    _ = (seqMat T false *ᵥ x) ⬝ᵥ p := by
        rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    _ = seqRhs T false ⬝ᵥ p := by rw [hx.2]
    _ = p none := seqRhs_dotProduct T false p

open Classical in
/-- **Weak duality** between player `false`'s maximin sequence-form LP and player `true`'s
minimax sequence-form LP ([vonStengel2007], Section 3.11, p. 73). -/
theorem seq_weak_duality [∀ i h, Fintype (Act i h)] {T : ExtensiveTree Bool H Act}
    [Fintype (H false)] [Fintype (H true)]
    {x : SeqVar T false → ℝ} {y : SeqVar T true → ℝ}
    {q : Option {h : H true // T.OccursInfoSet true h} → ℝ}
    {p : Option {h : H false // T.OccursInfoSet false h} → ℝ}
    (hx : T.IsRealizationPlan false x) (hy : T.IsRealizationPlan true y)
    (hq : (seqMat T true)ᵀ *ᵥ q ≤ (T.seqPayoffMat false)ᵀ *ᵥ x)
    (hp : T.seqPayoffMat false *ᵥ y ≤ (seqMat T false)ᵀ *ᵥ p) :
    q none ≤ x ⬝ᵥ (T.seqPayoffMat false *ᵥ y) ∧
      x ⬝ᵥ (T.seqPayoffMat false *ᵥ y) ≤ p none :=
  ⟨seq_weak_duality_lower hy hq, seq_weak_duality_upper hx hp⟩

open Classical in
/-- **Zero-sum sequence-form LP minimax theorem** ([vonStengel2007], Theorem 3.13, Section 3.11,
p. 73): in a two-player zero-sum extensive-form game with perfect recall, the sequence-form LP pair
`max { q none | x ≥ 0, E₁ x = e₁, E₂ᵀ q ≤ Aᵀ x }` and
`min { p none | y ≥ 0, E₂ y = e₂, A y ≤ E₁ᵀ p }` attains a common optimal value `v`, and any
optimal solutions `(x*, y*)` form a sequence-form Nash equilibrium / minimax saddle point with
value `x* ⬝ᵥ A *ᵥ y* = v`. Proved directly from LP duality without fixed-point theorems. -/
theorem exists_seq_lp_minimax [∀ i h, Fintype (Act i h)] [∀ i h, Nonempty (Act i h)]
    {T : ExtensiveTree Bool H Act} [Fintype (H false)] [Fintype (H true)]
    (hpr : ∀ i, T.PerfectRecall i) (hzs : T.IsZeroSum) :
    ∃ v x y q p,
      T.IsRealizationPlan false x ∧ T.IsRealizationPlan true y ∧
      (seqMat T true)ᵀ *ᵥ q ≤ (T.seqPayoffMat false)ᵀ *ᵥ x ∧
      T.seqPayoffMat false *ᵥ y ≤ (seqMat T false)ᵀ *ᵥ p ∧
      x ⬝ᵥ (T.seqPayoffMat false *ᵥ y) = v ∧ q none = v ∧ p none = v ∧
      T.IsSeqNash x y ∧
      IsGreatest
        ((fun u : (SeqVar T false → ℝ) × (Option {h : H true // T.OccursInfoSet true h} → ℝ) =>
          u.2 none) '' {u | T.IsRealizationPlan false u.1 ∧
            (seqMat T true)ᵀ *ᵥ u.2 ≤ (T.seqPayoffMat false)ᵀ *ᵥ u.1}) v ∧
      IsLeast
        ((fun w : (SeqVar T true → ℝ) × (Option {h : H false // T.OccursInfoSet false h} → ℝ) =>
          w.2 none) '' {w | T.IsRealizationPlan true w.1 ∧
            T.seqPayoffMat false *ᵥ w.1 ≤ (seqMat T false)ᵀ *ᵥ w.2}) v := by
  classical
  let S₁ := Option {h : H false // T.OccursInfoSet false h}
  let S₂ := Option {h : H true // T.OccursInfoSet true h}
  let E₁ := seqMat T false
  let E₂ := seqMat T true
  let e₁ := seqRhs T false
  let e₂ := seqRhs T true
  let A₀ := T.seqPayoffMat false
  let Row := SeqVar T false ⊕ S₁ ⊕ S₁ ⊕ SeqVar T true
  let Col := SeqVar T false ⊕ S₂
  let M : Matrix Row Col ℝ := fun r c =>
    match r, c with
    | .inl σ₀, .inl σ => if σ₀ = σ then -1 else 0
    | .inl _, .inr _ => 0
    | .inr (.inl row₁), .inl σ => E₁ row₁ σ
    | .inr (.inl _), .inr _ => 0
    | .inr (.inr (.inl row₁)), .inl σ => -E₁ row₁ σ
    | .inr (.inr (.inl _)), .inr _ => 0
    | .inr (.inr (.inr τ)), .inl σ => -A₀ σ τ
    | .inr (.inr (.inr τ)), .inr row₂ => E₂ row₂ τ
  let rhs : Row → ℝ
    | .inl _ => 0
    | .inr (.inl row₁) => e₁ row₁
    | .inr (.inr (.inl row₁)) => -e₁ row₁
    | .inr (.inr (.inr _)) => 0
  let obj : Col → ℝ := Sum.elim 0 e₂
  have hM_mulVec : ∀ (x : SeqVar T false → ℝ) (q : S₂ → ℝ),
      M *ᵥ Sum.elim x q ≤ rhs ↔
        T.IsRealizationPlan false x ∧ E₂ᵀ *ᵥ q ≤ A₀ᵀ *ᵥ x := by
    intro x q
    have hl : ∀ σ₀, (M *ᵥ Sum.elim x q) (.inl σ₀) = -x σ₀ := fun σ₀ => by
      rw [Matrix.mulVec, dotProduct]
      dsimp only [Col]
      rw [Fintype.sum_sum_type]
      dsimp only [M]
      simp only [Sum.elim_inl, Sum.elim_inr, zero_mul, sum_const_zero, add_zero]
      rw [sum_eq_single σ₀]
      · simp
      · intro σ _ hne
        simp [hne.symm]
      · intro hmem
        exact absurd (mem_univ σ₀) hmem
    have he1 : ∀ row₁, (M *ᵥ Sum.elim x q) (.inr (.inl row₁)) = (E₁ *ᵥ x) row₁ := fun row₁ => by
      rw [Matrix.mulVec, dotProduct]
      dsimp only [Col]
      rw [Fintype.sum_sum_type]
      dsimp only [M]
      simp only [Sum.elim_inl, Sum.elim_inr, zero_mul, sum_const_zero, add_zero]
      rfl
    have he1n : ∀ row₁,
        (M *ᵥ Sum.elim x q) (.inr (.inr (.inl row₁))) = -(E₁ *ᵥ x) row₁ := fun row₁ => by
      rw [Matrix.mulVec, dotProduct]
      dsimp only [Col]
      rw [Fintype.sum_sum_type]
      dsimp only [M]
      simp only [Sum.elim_inl, Sum.elim_inr, zero_mul, sum_const_zero, add_zero, neg_mul,
        sum_neg_distrib]
      rfl
    have hlcp : ∀ τ, (M *ᵥ Sum.elim x q) (.inr (.inr (.inr τ))) =
        -((A₀ᵀ *ᵥ x) τ) + (E₂ᵀ *ᵥ q) τ := fun τ => by
      rw [Matrix.mulVec, dotProduct]
      dsimp only [Col]
      rw [Fintype.sum_sum_type]
      dsimp only [M]
      simp only [Sum.elim_inl, Sum.elim_inr, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
        neg_mul, sum_neg_distrib]
      rfl
    constructor
    · intro hle
      refine ⟨⟨fun σ => ?_, funext fun row₁ => ?_⟩, fun τ => ?_⟩
      · have h := hle (.inl σ)
        rw [hl, show rhs (.inl σ) = 0 from rfl] at h
        linarith
      · have h1 := hle (.inr (.inl row₁))
        have h2 := hle (.inr (.inr (.inl row₁)))
        rw [he1] at h1
        rw [he1n] at h2
        change (E₁ *ᵥ x) row₁ ≤ e₁ row₁ at h1
        change -(E₁ *ᵥ x) row₁ ≤ -e₁ row₁ at h2
        linarith
      · have h := hle (.inr (.inr (.inr τ)))
        rw [hlcp] at h
        change -((A₀ᵀ *ᵥ x) τ) + (E₂ᵀ *ᵥ q) τ ≤ 0 at h
        linarith
    · rintro ⟨⟨hxnn, hxeq⟩, hqle⟩ r
      rcases r with σ₀ | (row₁ | (row₁ | τ))
      · rw [hl]; change -x σ₀ ≤ 0; linarith [hxnn σ₀]
      · rw [he1, hxeq]
      · rw [he1n, hxeq]
      · rw [hlcp]; change -((A₀ᵀ *ᵥ x) τ) + (E₂ᵀ *ᵥ q) τ ≤ 0; linarith [hqle τ]
  have hM_vecMul : ∀ (s : SeqVar T false → ℝ) (p₁ p₂ : S₁ → ℝ) (y : SeqVar T true → ℝ),
      Sum.elim s (Sum.elim p₁ (Sum.elim p₂ y)) ᵥ* M = obj ↔
        s = E₁ᵀ *ᵥ (p₁ - p₂) - A₀ *ᵥ y ∧ E₂ *ᵥ y = e₂ := by
    intro s p₁ p₂ y
    have hL : ∀ σ, (Sum.elim s (Sum.elim p₁ (Sum.elim p₂ y)) ᵥ* M) (.inl σ) =
        -s σ + (E₁ᵀ *ᵥ (p₁ - p₂)) σ - (A₀ *ᵥ y) σ := fun σ => by
      rw [vecMul, dotProduct]
      dsimp only [M, Row]
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      have hs : ∑ σ₀ : SeqVar T false, s σ₀ * (if σ₀ = σ then (-1 : ℝ) else 0) = -s σ := by
        rw [sum_eq_single σ]
        · simp
        · intro σ₀ _ hne
          simp [hne]
        · intro hmem
          exact absurd (mem_univ σ) hmem
      rw [hs]
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.sub_apply, mul_neg,
        sum_neg_distrib]
      have hdot₁ : ∑ r₁ : S₁, p₁ r₁ * E₁ r₁ σ = ∑ r₁ : S₁, E₁ r₁ σ * p₁ r₁ :=
        sum_congr rfl fun r₁ _ => mul_comm _ _
      have hdot₂ : ∑ r₁ : S₁, p₂ r₁ * E₁ r₁ σ = ∑ r₁ : S₁, E₁ r₁ σ * p₂ r₁ :=
        sum_congr rfl fun r₁ _ => mul_comm _ _
      have hdotA : ∑ τ : SeqVar T true, y τ * A₀ σ τ = ∑ τ : SeqVar T true, A₀ σ τ * y τ :=
        sum_congr rfl fun τ _ => mul_comm _ _
      have hdiff_sum : ∑ r₁ : S₁, E₁ r₁ σ * p₁ r₁ - ∑ r₁ : S₁, E₁ r₁ σ * p₂ r₁ =
          ∑ r₁ : S₁, E₁ r₁ σ * (p₁ r₁ - p₂ r₁) := by
        rw [← sum_sub_distrib]
        exact sum_congr rfl fun r₁ _ => by ring
      linarith [hdot₁, hdot₂, hdotA, hdiff_sum]
    have hR : ∀ row₂, (Sum.elim s (Sum.elim p₁ (Sum.elim p₂ y)) ᵥ* M) (.inr row₂) =
        (E₂ *ᵥ y) row₂ := fun row₂ => by
      rw [vecMul, dotProduct]
      dsimp only [M, Row]
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, mul_zero, sum_const_zero, zero_add]
      rw [Matrix.mulVec, dotProduct]
      exact sum_congr rfl fun τ _ => mul_comm _ _
    constructor
    · intro heq
      constructor
      · funext σ
        have h := congrFun heq (.inl σ)
        rw [hL] at h
        change -s σ + (E₁ᵀ *ᵥ (p₁ - p₂)) σ - (A₀ *ᵥ y) σ = 0 at h
        change s σ = (E₁ᵀ *ᵥ (p₁ - p₂)) σ - (A₀ *ᵥ y) σ
        linarith
      · funext row₂
        have h := congrFun heq (.inr row₂)
        rw [hR] at h
        exact h
    · intro hpair
      rcases hpair with ⟨hs, hy⟩
      funext c
      rcases c with σ | row₂
      · rw [hL]
        have hσ := congrFun hs σ
        change s σ = (E₁ᵀ *ᵥ (p₁ - p₂)) σ - (A₀ *ᵥ y) σ at hσ
        change -s σ + (E₁ᵀ *ᵥ (p₁ - p₂)) σ - (A₀ *ᵥ y) σ = 0
        linarith
      · rw [hR]
        exact congrFun hy row₂
  have hP : ∃ u : Col → ℝ, M *ᵥ u ≤ rhs := by
    let s₀ : PureStrategy H Act false := fun _ => Classical.arbitrary _
    let x₀ := T.pureToRealizationPlan false s₀
    have hx₀ := isRealizationPlan_pureToRealizationPlan (hpr false) s₀
    obtain ⟨qNeg, hqNeg⟩ := exists_seqMat_transpose_mulVec_ge (hpr true) (-(A₀ᵀ *ᵥ x₀))
    refine ⟨Sum.elim x₀ (-qNeg), (hM_mulVec x₀ (-qNeg)).2 ⟨hx₀, fun τ => ?_⟩⟩
    have hτ := hqNeg τ
    rw [Matrix.mulVec_neg, Pi.neg_apply]
    linarith [show (-((A₀ᵀ *ᵥ x₀) τ)) ≤ (E₂ᵀ *ᵥ qNeg) τ from hτ]
  have hD : ∃ v : Row → ℝ, 0 ≤ v ∧ v ᵥ* M = obj := by
    let s₁ : PureStrategy H Act true := fun _ => Classical.arbitrary _
    let y₀ := T.pureToRealizationPlan true s₁
    have hy₀ := isRealizationPlan_pureToRealizationPlan (hpr true) s₁
    obtain ⟨p₀, hp₀⟩ := exists_seqMat_transpose_mulVec_ge (hpr false) (A₀ *ᵥ y₀)
    let p₁ : S₁ → ℝ := fun r => max (p₀ r) 0
    let p₂ : S₁ → ℝ := fun r => max (-p₀ r) 0
    have hpdiff : p₁ - p₂ = p₀ := by
      ext r; exact max_sub_max_neg (p₀ r)
    let s : SeqVar T false → ℝ := E₁ᵀ *ᵥ p₀ - A₀ *ᵥ y₀
    refine ⟨Sum.elim s (Sum.elim p₁ (Sum.elim p₂ y₀)), ?_, ?_⟩
    · intro r
      rcases r with σ | (row₁ | (row₁ | τ))
      · exact sub_nonneg.2 (hp₀ σ)
      · exact le_max_right _ _
      · exact le_max_right _ _
      · exact hy₀.1 τ
    · rw [hM_vecMul]
      exact ⟨by rw [hpdiff], hy₀.2⟩
  obtain ⟨val, ⟨⟨uStar, huStar_le, hval_u⟩, hmax⟩,
      ⟨⟨vStar, ⟨hvStar_nn, hvStar_eq⟩, hval_v⟩, hmin⟩⟩ :=
    Matrix.exists_isGreatest_isLeast_dotProduct M rhs obj hP hD
  let xStar : SeqVar T false → ℝ := fun σ => uStar (.inl σ)
  let qStar : S₂ → ℝ := fun row₂ => uStar (.inr row₂)
  have huStar_eq : uStar = Sum.elim xStar qStar := by
    ext c; cases c <;> rfl
  have hxStar_qStar : T.IsRealizationPlan false xStar ∧ E₂ᵀ *ᵥ qStar ≤ A₀ᵀ *ᵥ xStar :=
    (hM_mulVec xStar qStar).1 (huStar_eq ▸ huStar_le)
  have hqStar_val : qStar none = val := by
    rw [← hval_u, huStar_eq]
    dsimp only [obj, dotProduct, Col]
    rw [Fintype.sum_sum_type]
    simp only [e₂, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zero_mul, sum_const_zero, zero_add]
    change qStar none = ∑ a₂, seqRhs T true a₂ * qStar a₂
    rw [← dotProduct, seqRhs_dotProduct]
  let sStar : SeqVar T false → ℝ := fun σ => vStar (.inl σ)
  let p₁Star : S₁ → ℝ := fun r => vStar (.inr (.inl r))
  let p₂Star : S₁ → ℝ := fun r => vStar (.inr (.inr (.inl r)))
  let yStar : SeqVar T true → ℝ := fun τ => vStar (.inr (.inr (.inr τ)))
  have hvStar_split : vStar = Sum.elim sStar (Sum.elim p₁Star (Sum.elim p₂Star yStar)) := by
    ext r; rcases r with σ | (row₁ | (row₁ | τ)) <;> rfl
  have hvStar_rel := (hM_vecMul sStar p₁Star p₂Star yStar).1 (hvStar_split ▸ hvStar_eq)
  let pStar : S₁ → ℝ := p₁Star - p₂Star
  have hyStar_feas : T.IsRealizationPlan true yStar :=
    ⟨fun τ => hvStar_nn (.inr (.inr (.inr τ))), hvStar_rel.2⟩
  have hpStar_feas : A₀ *ᵥ yStar ≤ E₁ᵀ *ᵥ pStar := fun σ => by
    have hsσ : 0 ≤ sStar σ := hvStar_nn (.inl σ)
    have heq := congrFun hvStar_rel.1 σ
    change sStar σ = (E₁ᵀ *ᵥ pStar) σ - (A₀ *ᵥ yStar) σ at heq
    linarith
  have hpStar_val : pStar none = val := by
    rw [← hval_v, hvStar_split]
    dsimp only [pStar, dotProduct, Row]
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [rhs, e₁, Sum.elim_inl, Sum.elim_inr, mul_zero, sum_const_zero, zero_add, add_zero,
      mul_neg, sum_neg_distrib]
    change p₁Star none - p₂Star none =
      (∑ a₁, p₁Star a₁ * seqRhs T false a₁) + -(∑ a₂, p₂Star a₂ * seqRhs T false a₂)
    rw [← dotProduct, ← dotProduct, dotProduct_seqRhs, dotProduct_seqRhs, sub_eq_add_neg]
  have hweak_opt := seq_weak_duality hxStar_qStar.1 hyStar_feas hxStar_qStar.2 hpStar_feas
  have hmid : xStar ⬝ᵥ (A₀ *ᵥ yStar) = val := by
    have h1 : val ≤ xStar ⬝ᵥ (A₀ *ᵥ yStar) := hqStar_val ▸ hweak_opt.1
    have h2 : xStar ⬝ᵥ (A₀ *ᵥ yStar) ≤ val := hpStar_val ▸ hweak_opt.2
    exact le_antisymm h2 h1
  have hbr0 : T.IsSeqBestResponseFalse xStar yStar := by
    refine ⟨hxStar_qStar.1, fun x' hx' => ?_⟩
    have hw := seq_weak_duality_upper hx' (y := yStar) (p := pStar) hpStar_feas
    rw [hpStar_val, ← hmid] at hw
    exact hw
  have hmat_neg : T.seqPayoffMat true = -T.seqPayoffMat false :=
    hzs.seqPayoffMat_true_of_perfectRecall hpr
  have hbr1 : T.IsSeqBestResponseTrue yStar xStar := by
    refine ⟨hyStar_feas, fun y' hy' => ?_⟩
    have hw := seq_weak_duality_lower hy' hxStar_qStar.2
    rw [hqStar_val, ← hmid] at hw
    rw [hmat_neg, neg_mulVec, dotProduct_neg, neg_mulVec, dotProduct_neg, neg_le_neg_iff]
    exact hw
  refine ⟨val, xStar, yStar, qStar, pStar, hxStar_qStar.1, hyStar_feas, hxStar_qStar.2,
    hpStar_feas, hmid, hqStar_val, hpStar_val, ⟨hbr0, hbr1⟩, ?_, ?_⟩
  · refine ⟨⟨(xStar, qStar), ⟨hxStar_qStar.1, hxStar_qStar.2⟩, hqStar_val⟩, ?_⟩
    rintro _ ⟨⟨x, q⟩, ⟨hx, hq⟩, rfl⟩
    have hmem : Sum.elim x q ∈ {u | M *ᵥ u ≤ rhs} := (hM_mulVec x q).2 ⟨hx, hq⟩
    have hle := hmax ⟨Sum.elim x q, hmem, rfl⟩
    dsimp only at hle ⊢
    have hobj : obj ⬝ᵥ Sum.elim x q = q none := by
      dsimp only [obj, dotProduct, Col]
      rw [Fintype.sum_sum_type]
      simp only [e₂, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zero_mul, sum_const_zero, zero_add]
      change ∑ a₂, seqRhs T true a₂ * q a₂ = q none
      rw [← dotProduct, seqRhs_dotProduct]
    rwa [hobj] at hle
  · refine ⟨⟨(yStar, pStar), ⟨hyStar_feas, hpStar_feas⟩, hpStar_val⟩, ?_⟩
    rintro _ ⟨⟨y, p⟩, ⟨hy, hp⟩, rfl⟩
    let s := E₁ᵀ *ᵥ p - A₀ *ᵥ y
    let p₁ : S₁ → ℝ := fun r => max (p r) 0
    let p₂ : S₁ → ℝ := fun r => max (-p r) 0
    have hpdiff : p₁ - p₂ = p := by
      ext r; exact max_sub_max_neg (p r)
    let vVec := Sum.elim s (Sum.elim p₁ (Sum.elim p₂ y))
    have hvnn : 0 ≤ vVec := fun r => by
      rcases r with σ | (row₁ | (row₁ | τ))
      · exact sub_nonneg.2 (hp σ)
      · exact le_max_right _ _
      · exact le_max_right _ _
      · exact hy.1 τ
    have hvEq : vVec ᵥ* M = obj := (hM_vecMul s p₁ p₂ y).2 ⟨by rw [hpdiff], hy.2⟩
    have hle := hmin ⟨vVec, ⟨hvnn, hvEq⟩, rfl⟩
    dsimp only at hle ⊢
    have hvobj : vVec ⬝ᵥ rhs = p none := by
      dsimp only [vVec, dotProduct, Row]
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
      simp only [rhs, e₁, Sum.elim_inl, Sum.elim_inr, mul_zero, sum_const_zero, zero_add, add_zero,
        mul_neg, sum_neg_distrib]
      change (∑ a₁, p₁ a₁ * seqRhs T false a₁) + -(∑ a₂, p₂ a₂ * seqRhs T false a₂) = p none
      rw [← dotProduct, ← dotProduct, dotProduct_seqRhs, dotProduct_seqRhs, ← sub_eq_add_neg]
      exact max_sub_max_neg (p none)
    rwa [hvobj] at hle

/-- In a zero-sum extensive-form game with perfect recall, LP strong duality also constructs an
explicit minimax behavioral Nash equilibrium profile `β` realizing the minimax game value. -/
theorem exists_behavior_minimax [∀ i h, Fintype (Act i h)] [∀ i h, Nonempty (Act i h)]
    {T : ExtensiveTree Bool H Act} [Finite (H false)] [Finite (H true)]
    (hpr : ∀ i, T.PerfectRecall i) (hzs : T.IsZeroSum) :
    ∃ (v : ℝ) (β : ∀ i, ∀ h : H i, Act i h → ℝ),
      T.IsBehaviorNash β ∧ T.evalBehavior β false = v ∧ T.evalBehavior β true = -v := by
  classical
  let _ := Fintype.ofFinite (H false)
  let _ := Fintype.ofFinite (H true)
  obtain ⟨v, _, _, _, _, _, _, _, _, hmid, _, _, hnash, _, _⟩ := hzs.exists_seq_lp_minimax hpr
  obtain ⟨β, hβ_nash, hev⟩ := isBehaviorNash_of_isSeqNash hpr hnash
  have hev0 : T.evalBehavior β false = v := hev.trans hmid
  exact ⟨v, β, hβ_nash, hev0, by rw [hzs.evalBehavior_true, hev0]⟩

end ExtensiveTree.IsZeroSum

end ZeroSumLP

end Cslib.GameTheory.Extensive
