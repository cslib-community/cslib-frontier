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
  have hM0 : 0 ≤ M := sum_nonneg fun _ _ => le_max_right _ _
  have hbM : ∀ σ : SeqVar T i, b σ ≤ M := fun σ =>
    (le_max_left (b σ) 0).trans (single_le_sum (fun τ _ => le_max_right (b τ) 0) (mem_univ σ))
  have hr1 : 1 ≤ r := by linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card S)]
  let p : Option S → ℝ
    | none => M * r ^ maxLen
    | some h => M * r ^ (maxLen - ((T.infoSeq i h.1).length + 1))
  have hpow_ge : ∀ k : ℕ, M ≤ M * r ^ k := fun k => le_mul_of_one_le_right hM0 (one_le_pow₀ hr1)
  have hdiff : ∀ k : ℕ, k + 1 ≤ maxLen →
      M * r ^ (maxLen - k) - (Fintype.card S : ℝ) * (M * r ^ (maxLen - (k + 1))) =
        M * r ^ (maxLen - (k + 1)) := fun k hk => by
    rw [show maxLen - k = (maxLen - (k + 1)) + 1 by omega, pow_succ]
    dsimp only [r]
    ring
  have hsome_no_ext : ∀ (σ : SeqVar T i) (h : S),
      (∀ a : Act i h.1, SeqVar.infoSeqExt hpr h.2 a ≠ σ) →
      (seqMat T i *ᵥ Pi.single σ (1 : ℝ)) (some h) =
        if T.infoSeq i h.1 = σ.1 then -1 else 0 := fun σ h hno => by
    rw [seqMat_mulVec_some hpr h, sum_eq_zero fun a _ => Pi.single_eq_of_ne (hno a) _, add_zero]
    by_cases hi : T.infoSeq i h.1 = σ.1
    · simp [hi, show SeqVar.infoSeq hpr h.2 = σ from Subtype.ext (by rw [SeqVar.infoSeq_val, hi])]
    · have hne : SeqVar.infoSeq hpr h.2 ≠ σ := fun heq =>
        hi (by simpa [SeqVar.infoSeq_val] using congrArg Subtype.val heq)
      simp [hi, hne]
  have hbound : ∀ (σ : SeqVar T i) (U : Finset S),
      b σ ≤ M * r ^ (maxLen - σ.1.length) +
        ∑ h ∈ U, p (some h) * (if T.infoSeq i h.1 = σ.1 then (-1 : ℝ) else 0) := fun σ U => by
    by_cases hex : ∃ h₁ ∈ U, T.infoSeq i h₁.1 = σ.1
    · obtain ⟨h₁, _, hh₁⟩ := hex
      let k := σ.1.length
      have hlen1 : k + 1 ≤ maxLen := by
        let τ := SeqVar.infoSeqExt hpr h₁.2 (Classical.arbitrary (Act i h₁.1))
        have hle := Finset.le_sup (f := List.length) (mem_occursSeqFinset.2 τ.2)
        have hlenτ : τ.1.length = k + 1 := by
          dsimp [τ, k]
          rw [SeqVar.infoSeqExt_val, hh₁, List.length_append, List.length_singleton]
        omega
      have hterm : ∀ h ∈ U, -(M * r ^ (maxLen - (k + 1))) ≤
          p (some h) * (if T.infoSeq i h.1 = σ.1 then (-1 : ℝ) else 0) := fun h _ => by
        split_ifs with h1
        · simp [p, k, ← h1]
        · rw [mul_zero]; linarith [show 0 ≤ M * r ^ (maxLen - (k + 1)) by positivity]
      have hsum_lb : -((U.card : ℝ) * (M * r ^ (maxLen - (k + 1)))) ≤
          ∑ h ∈ U, p (some h) * (if T.infoSeq i h.1 = σ.1 then (-1 : ℝ) else 0) := by
        simpa using sum_le_sum hterm
      have hcard : (U.card : ℝ) ≤ Fintype.card S := by exact_mod_cast card_le_univ U
      have hmul := mul_le_mul_of_nonneg_right hcard
        (show 0 ≤ M * r ^ (maxLen - (k + 1)) by positivity)
      calc b σ
          ≤ M * r ^ (maxLen - (k + 1)) := (hbM σ).trans (hpow_ge (maxLen - (k + 1)))
        _ = M * r ^ (maxLen - k) - (Fintype.card S : ℝ) * (M * r ^ (maxLen - (k + 1))) :=
            (hdiff k hlen1).symm
        _ ≤ M * r ^ (maxLen - k) +
              ∑ h ∈ U, p (some h) * (if T.infoSeq i h.1 = σ.1 then (-1 : ℝ) else 0) := by
            linarith
    · push Not at hex
      rw [sum_eq_zero fun h hh => by simp [hex h hh], add_zero]
      exact (hbM σ).trans (hpow_ge _)
  refine ⟨p, fun σ => ?_⟩
  have hrow : ((seqMat T i)ᵀ *ᵥ p) σ =
      p none * (seqMat T i *ᵥ Pi.single σ (1 : ℝ)) none +
        ∑ h : S, p (some h) * (seqMat T i *ᵥ Pi.single σ (1 : ℝ)) (some h) := by
    have hdot : ((seqMat T i)ᵀ *ᵥ p) σ = ((seqMat T i)ᵀ *ᵥ p) ⬝ᵥ Pi.single σ (1 : ℝ) := by
      rw [dotProduct, sum_eq_single σ (fun τ _ h => by simp [h]) (fun h => absurd (mem_univ σ) h)]
      simp
    rw [hdot, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, dotProduct, Fintype.sum_option]
  change b σ ≤ ((seqMat T i)ᵀ *ᵥ p) σ
  rw [hrow]
  by_cases hnil : σ.1 = []
  · have hσ : σ = SeqVar.nil T i := Subtype.ext (by simp [hnil])
    rw [hσ, seqMat_mulVec_none, Pi.single_eq_same, mul_one,
      sum_congr rfl fun h _ => congrArg (p (some h) * ·) <|
        hsome_no_ext (SeqVar.nil T i) h fun a heq =>
          seqVar_infoSeqExt_ne_nil hpr h.2 a (by simpa using congrArg Subtype.val heq)]
    simpa [p] using hbound (SeqVar.nil T i) univ
  · obtain ⟨h₀, a₀, rfl⟩ := exists_infoSeqExt_of_seqVar_ne_nil hpr σ hnil
    let σ₀ := SeqVar.infoSeqExt hpr h₀.2 a₀
    have hnone : (seqMat T i *ᵥ Pi.single σ₀ (1 : ℝ)) none = 0 := by
      rw [seqMat_mulVec_none]
      exact Pi.single_eq_of_ne (fun heq => seqVar_infoSeqExt_ne_nil hpr h₀.2 a₀
        (by simpa [σ₀] using (congrArg Subtype.val heq).symm)) _
    have hh₀_val : (seqMat T i *ᵥ Pi.single σ₀ (1 : ℝ)) (some h₀) = 1 := by
      rw [seqMat_mulVec_some hpr h₀, Pi.single_eq_of_ne (fun heq => by
        have hlen := congrArg (List.length ∘ Subtype.val) heq
        simp [σ₀, SeqVar.infoSeq_val, SeqVar.infoSeqExt_val] at hlen), neg_zero, zero_add,
        sum_eq_single a₀ (fun a _ hne => Pi.single_eq_of_ne (fun heq =>
          hne (eq_of_heq (Sigma.mk.inj_iff.1 (seqVar_infoSeqExt_inj hpr heq)).2)) _)
          (fun h => absurd (mem_univ a₀) h), Pi.single_eq_same]
    rw [hnone, mul_zero, zero_add, ← add_sum_erase univ _ (mem_univ h₀), hh₀_val, mul_one,
      sum_congr rfl fun h hh => congrArg (p (some h) * ·) <|
        hsome_no_ext σ₀ h fun a heq => (ne_of_mem_erase hh) <| by
          simpa only [Sigma.ext_iff] using (Sigma.mk.inj_iff.1 (seqVar_infoSeqExt_inj hpr heq)).1]
    have hlen : σ₀.1.length = (T.infoSeq i h₀.1).length + 1 := by
      simp [σ₀, SeqVar.infoSeqExt_val]
    simpa [p, hlen, eq_comm] using hbound σ₀ (univ.erase h₀)

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
  let A := fromRows E (-E)
  let rhs := Sum.elim e (-e)
  have hAx_iff : ∀ x, (0 ≤ x ∧ A *ᵥ x ≤ rhs) ↔ T.IsRealizationPlan i x := fun x => by
    rw [fromRows_mulVec, neg_mulVec, Sum.elim_le_elim_iff]
    exact ⟨fun ⟨hnn, h1, h2⟩ => ⟨hnn, le_antisymm h1 (neg_le_neg_iff.1 h2)⟩,
      fun ⟨hnn, heq⟩ => ⟨hnn, heq.le, neg_le_neg heq.symm.le⟩⟩
  have hvec_elim : ∀ f g : Option {h : H i // T.OccursInfoSet i h} → ℝ,
      Sum.elim f g ᵥ* A = Eᵀ *ᵥ (f - g) ∧ Sum.elim f g ⬝ᵥ rhs = e ⬝ᵥ (f - g) := fun f g => by
    refine ⟨?_, ?_⟩
    · rw [vecMul_fromRows, vecMul_neg, ← sub_eq_add_neg, ← sub_vecMul, ← Matrix.mulVec_transpose]
      rfl
    · rw [dotProduct, dotProduct, Fintype.sum_sum_type, ← sum_add_distrib]
      exact sum_congr rfl fun r _ => by
        cases r <;> simp only [rhs, e, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, Pi.sub_apply] <;>
          ring
  have hdualLift : ∀ q, b ≤ Eᵀ *ᵥ q → ∃ y, (0 ≤ y ∧ b ≤ y ᵥ* A) ∧ y ⬝ᵥ rhs = e ⬝ᵥ q :=
    fun q hq => by
      let f := fun r => max (q r) 0
      let g := fun r => max (-q r) 0
      have hfg : f - g = q := funext fun r => max_sub_max_neg (q r)
      refine ⟨Sum.elim f g, ⟨fun r => by cases r <;> simp [f, g], ?_⟩, ?_⟩
      · rw [(hvec_elim f g).1, hfg]
        exact hq
      · rw [(hvec_elim f g).2, hfg]
  have hP : ∃ x, 0 ≤ x ∧ A *ᵥ x ≤ rhs :=
    ⟨_, (hAx_iff _).2 (isRealizationPlan_pureToRealizationPlan hpr fun _ => Classical.arbitrary _)⟩
  obtain ⟨q₀, hq₀⟩ := exists_seqMat_transpose_mulVec_ge hpr b
  obtain ⟨y₀, hy₀, _⟩ := hdualLift q₀ hq₀
  obtain ⟨v, ⟨⟨xOpt, hxOpt, hvx⟩, hmax⟩, ⟨⟨yOpt, ⟨_, hyOpt_le⟩, hvy⟩, hmin⟩⟩ :=
    Matrix.exists_isGreatest_isLeast_dotProduct_of_nonneg A rhs b hP ⟨y₀, hy₀⟩
  have hyOpt_eq : yOpt = Sum.elim (yOpt ∘ .inl) (yOpt ∘ .inr) := by
    ext r
    cases r <;> rfl
  obtain ⟨hvf, hvo⟩ := hvec_elim (yOpt ∘ .inl) (yOpt ∘ .inr)
  rw [← hyOpt_eq] at hvf hvo
  refine ⟨v, ⟨⟨xOpt, (hAx_iff xOpt).1 hxOpt, hvx⟩,
      fun _ ⟨x, hx, h⟩ => h ▸ hmax ⟨x, (hAx_iff x).2 hx, rfl⟩⟩,
    ⟨⟨_, show b ≤ Eᵀ *ᵥ _ by rwa [← hvf], hvo.symm.trans hvy⟩,
      fun _ ⟨q, hq, h⟩ => ?_⟩⟩
  obtain ⟨y, hy, hyobj⟩ := hdualLift q hq
  dsimp only at h ⊢
  rw [← h, ← hyobj]
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
  have hxEq : ∀ x' q, T.IsRealizationPlan i x' → x' ⬝ᵥ ((seqMat T i)ᵀ *ᵥ q) = q none :=
    fun x' q hx' => by
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, hx'.2, seqRhs_dotProduct]
  have hweak : ∀ x' q, T.IsRealizationPlan i x' → c ≤ (seqMat T i)ᵀ *ᵥ q → c ⬝ᵥ x' ≤ q none :=
    fun x' q hx' hq =>
      calc c ⬝ᵥ x' = x' ⬝ᵥ c := dotProduct_comm _ _
        _ ≤ x' ⬝ᵥ ((seqMat T i)ᵀ *ᵥ q) := dotProduct_le_dotProduct_of_nonneg_left hq hx'.1
        _ = q none := hxEq x' q hx'
  refine ⟨fun ⟨hx, hbest⟩ => ?_, fun ⟨hx, q, hq, hcs⟩ => ⟨hx, fun x' hx' => ?_⟩⟩
  · obtain ⟨v, ⟨⟨xMax, hxMax, hvx⟩, hmax⟩, ⟨⟨q, hq, hvq⟩, _⟩⟩ :=
      exists_isGreatest_isLeast_seqLP hpr c
    have hv_eq : c ⬝ᵥ x = v := le_antisymm (hmax ⟨x, hx, rfl⟩) (hvx ▸ hbest xMax hxMax)
    have hgap0 : x ⬝ᵥ ((seqMat T i)ᵀ *ᵥ q - c) = 0 := by
      dsimp only at hvq
      rw [seqRhs_dotProduct] at hvq
      rw [dotProduct_sub, hxEq x q hx, hvq, dotProduct_comm x c, hv_eq, sub_self]
    refine ⟨hx, q, hq, fun σ => ?_⟩
    have hz := (sum_eq_zero_iff_of_nonneg fun τ _ =>
      mul_nonneg (hx.1 τ) (sub_nonneg.2 (hq τ))).1 hgap0 σ (mem_univ σ)
    exact (mul_eq_zero.1 hz).imp_right sub_eq_zero.1
  · have hmatch : c ⬝ᵥ x = q none := by
      rw [← hxEq x q hx, dotProduct_comm c x]
      exact sum_congr rfl fun σ _ => (hcs σ).elim (fun h0 => by simp [h0]) fun heq => by rw [heq]
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
  refine ⟨fun ⟨hmix, hopt⟩ => ⟨hmix, ?_⟩, fun ⟨hmix, hbr0, hbr1⟩ => ⟨hmix, fun i s => ?_⟩⟩
  · have hnash := CostGame.IsMixedNash.expectedCost_le_update ⟨hmix, hopt⟩
    refine ⟨⟨isRealizationPlan_mixedToRealizationPlan (hpr false) (hmix false), fun x' hx' => ?_⟩,
        ⟨isRealizationPlan_mixedToRealizationPlan (hpr true) (hmix true), fun y' hy' => ?_⟩⟩
    · obtain ⟨μ', hμ', hplan'⟩ := exists_mixed_of_isRealizationPlan (hpr false) hx'
      have hdev := hnash false hμ'
      rw [T.toCostGame_expectedCost, T.toCostGame_expectedCost, neg_le_neg_iff,
        evalMixed_eq_seqPayoffMat, evalMixed_eq_seqPayoffMat] at hdev
      simpa only [Function.update_self, Function.update_of_ne (by decide : (true : Bool) ≠ false),
        hplan'] using hdev
    · obtain ⟨μ', hμ', hplan'⟩ := exists_mixed_of_isRealizationPlan (hpr true) hy'
      have hdev := hnash true hμ'
      rw [T.toCostGame_expectedCost, T.toCostGame_expectedCost, neg_le_neg_iff,
        evalMixed_eq_seqPayoffMat, evalMixed_eq_seqPayoffMat] at hdev
      simpa only [Function.update_self, Function.update_of_ne (by decide : (false : Bool) ≠ true),
        hplan'] using hdev
  · have hsum_s : ∑ b, (Pi.single (M := fun _ => ℝ) s (1 : ℝ)) b = ∑ b, μ i b := by
      rw [sum_eq_single s (fun _ _ hb => Pi.single_eq_of_ne hb _) (fun h => absurd (mem_univ s) h),
        Pi.single_eq_same, (hmix i).sum_eq_one]
    have hupd_eval : T.toCostGame.deviationCost μ i s =
        T.toCostGame.expectedCost (Function.update μ i (Pi.single s (1 : ℝ))) i := by
      rw [← CostGame.sum_mul_deviationCost_eq_expectedCost T.toCostGame _
        (by rw [Function.update_self, hsum_s, (hmix i).sum_eq_one])]
      simp_rw [CostGame.deviationCost_update_self T.toCostGame μ hsum_s]
      simp [Function.update_self, Pi.single_apply]
    rw [hupd_eval, T.toCostGame_expectedCost, T.toCostGame_expectedCost, neg_le_neg_iff,
      evalMixed_eq_seqPayoffMat, evalMixed_eq_seqPayoffMat]
    cases i
    · simpa only [Function.update_self, Function.update_of_ne (by decide : (true : Bool) ≠ false)]
        using hbr0.2 _
          (isRealizationPlan_mixedToRealizationPlan (hpr false) (isMixedStrategy_single s))
    · simpa only [Function.update_self, Function.update_of_ne (by decide : (false : Bool) ≠ true)]
        using hbr1.2 _
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
  refine ⟨fun ⟨hbeh, hopt⟩ => ⟨hbeh,
      ⟨⟨isRealizationPlan_behaviorToRealizationPlan (hpr false) (hbeh false), fun x' hx' => ?_⟩,
       ⟨isRealizationPlan_behaviorToRealizationPlan (hpr true) (hbeh true), fun y' hy' => ?_⟩⟩⟩,
    fun ⟨hbeh, hbr0, hbr1⟩ => ⟨hbeh, fun i β' hβ' => ?_⟩⟩
  · have hdev := hopt false _ (isBehaviorStrategy_realizationPlanToBehavior (hpr false) hx')
    simpa only [evalBehavior_eq_seqPayoffMat, Function.update_self,
      Function.update_of_ne (by decide : (true : Bool) ≠ false),
      behaviorToRealizationPlan_realizationPlanToBehavior (hpr false) hx'] using hdev
  · have hdev := hopt true _ (isBehaviorStrategy_realizationPlanToBehavior (hpr true) hy')
    simpa only [evalBehavior_eq_seqPayoffMat, Function.update_self,
      Function.update_of_ne (by decide : (false : Bool) ≠ true),
      behaviorToRealizationPlan_realizationPlanToBehavior (hpr true) hy'] using hdev
  · rw [evalBehavior_eq_seqPayoffMat, evalBehavior_eq_seqPayoffMat]
    cases i
    · simpa only [Function.update_self, Function.update_of_ne (by decide : (true : Bool) ≠ false)]
        using hbr0.2 _ (isRealizationPlan_behaviorToRealizationPlan (hpr false) hβ')
    · simpa only [Function.update_self, Function.update_of_ne (by decide : (false : Bool) ≠ true)]
        using hbr1.2 _ (isRealizationPlan_behaviorToRealizationPlan (hpr true) hβ')

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
  · refine .inl ⟨hnil, funext fun τ => ?_⟩
    simp only [ExtensiveTree.behaviorToRealizationPlan_apply, Pi.single_apply]
    by_cases hτ : τ = σ
    · subst hτ
      simp [hnil]
    · cases ht : τ.1 with
      | nil => exact absurd (Subtype.ext (ht.trans hnil.symm)) hτ
      | cons _ _ => simp [hτ]
  · obtain ⟨⟨h₀, hh₀⟩, a₀, rfl⟩ := exists_infoSeqExt_of_seqVar_ne_nil hpr σ hnil
    let target : Seq H Act i := T.infoSeq i h₀ ++ [⟨h₀, a₀⟩]
    let β₁ : ∀ h : H i, Act i h → ℝ := fun h a =>
      if (⟨h, a⟩ : Choice H Act i) ∈ target then 1 else 0
    let β₀ : ∀ h : H i, Act i h → ℝ := fun h a =>
      if (⟨h, a⟩ : Choice H Act i) ∈ target ∧ (⟨h, a⟩ : Choice H Act i) ≠ ⟨h₀, a₀⟩ then 1 else 0
    refine .inr ⟨β₁, β₀, funext fun τ => ?_⟩
    simp only [Pi.sub_apply, ExtensiveTree.behaviorToRealizationPlan_apply, Pi.single_apply]
    by_cases hτ : τ = SeqVar.infoSeqExt hpr hh₀ a₀
    · rw [hτ]
      simp only [↓reduceIte, SeqVar.infoSeqExt_val]
      change realizationProbBehavior β₁ target - realizationProbBehavior β₀ target = 1
      rw [realizationProbBehavior_eq_one_of_forall β₁ fun p hp => by simp [β₁, hp],
        realizationProbBehavior_eq_zero_of_exists β₀ (by simp [target] : ⟨h₀, a₀⟩ ∈ target)
          (by simp [β₀]), sub_zero]
    · simp only [hτ, ↓reduceIte]
      by_cases hall : ∀ p ∈ τ.1, p ∈ target
      · by_cases hmem : (⟨h₀, a₀⟩ : Choice H Act i) ∈ τ.1
        · exfalso
          obtain ⟨pre, post, hsplit⟩ := List.mem_iff_append.1 hmem
          obtain ⟨z, rem, hz⟩ := τ.2
          obtain ⟨v, hv, hpre⟩ := z.exists_node_of_seq_append pre (post ++ rem) h₀ a₀
            (by rw [← hz, hsplit, List.append_assoc, List.cons_append])
          have hpre_eq : pre = T.infoSeq i h₀ := hpre.symm.trans (hpr.playerSeq_eq_infoSeq hv)
          cases post with
          | nil => exact hτ (Subtype.ext (by rw [SeqVar.infoSeqExt_val, hsplit, hpre_eq]))
          | cons q post' =>
            have hq_mem : q ∈ τ.1 := by
              rw [hsplit]
              simp
            have hq_fst : q.1 ∈ target.map Sigma.fst := List.mem_map.2 ⟨q, hall q hq_mem, rfl⟩
            have hzn := hpr.noRepeatedInfoSet z
            rw [← hz, List.map_append] at hzn
            have hnodup : (τ.1.map Sigma.fst).Nodup := List.Nodup.of_append_left hzn
            have hsplit' : τ.1 = target ++ q :: post' := by
              rw [hsplit, hpre_eq]
              simp [target, List.append_assoc]
            rw [hsplit', List.map_append, List.nodup_append] at hnodup
            exact hnodup.2.2 q.1 hq_fst q.1 List.mem_cons_self rfl
        · rw [realizationProbBehavior_congr β₁ β₀ fun ⟨ph, pa⟩ hp => by
            have hne : (⟨ph, pa⟩ : Choice H Act i) ≠ ⟨h₀, a₀⟩ := fun h => hmem (h ▸ hp)
            dsimp only [β₁, β₀]
            exact if_congr (and_iff_left hne).symm rfl rfl, sub_self]
      · push Not at hall
        obtain ⟨q, hq_mem, hq_not⟩ := hall
        rw [realizationProbBehavior_eq_zero_of_exists β₁ hq_mem (by simp [β₁, hq_not]),
          realizationProbBehavior_eq_zero_of_exists β₀ hq_mem (by simp [β₀, hq_not]), sub_self]

theorem evalBehavior_true [∀ i h, Fintype (Act i h)] {T : ExtensiveTree Bool H Act}
    (hzs : T.IsZeroSum) (β : ∀ i, ∀ h : H i, Act i h → ℝ) :
    T.evalBehavior β true = -T.evalBehavior β false := by
  rw [T.evalBehavior_eq_sum_terminal β true, T.evalBehavior_eq_sum_terminal β false,
    ← sum_neg_distrib]
  exact sum_congr rfl fun z _ => by rw [eq_neg_of_add_eq_zero_right (hzs z), mul_neg]

theorem evalMixed_true [∀ i, Fintype (H i)] [∀ i, DecidableEq (H i)] [∀ i h, Fintype (Act i h)]
    {T : ExtensiveTree Bool H Act} (hzs : T.IsZeroSum) (μ : ∀ i, PureStrategy H Act i → ℝ) :
    T.evalMixed μ true = -T.evalMixed μ false := by
  rw [T.evalMixed_eq_sum_terminal μ true, T.evalMixed_eq_sum_terminal μ false, ← sum_neg_distrib]
  exact sum_congr rfl fun z _ => by rw [eq_neg_of_add_eq_zero_right (hzs z), mul_neg]

open Classical in
theorem seqPayoffMat_true_of_perfectRecall [∀ i h, Fintype (Act i h)] [∀ i h, Nonempty (Act i h)]
    {T : ExtensiveTree Bool H Act} (hpr : ∀ i, T.PerfectRecall i) (hzs : T.IsZeroSum) :
    T.seqPayoffMat true = -T.seqPayoffMat false := by
  let Smat := T.seqPayoffMat false + T.seqPayoffMat true
  have hbilin : ∀ (β₀ : ∀ h : H false, Act false h → ℝ) (β₁ : ∀ h : H true, Act true h → ℝ),
      (T.behaviorToRealizationPlan false β₀) ⬝ᵥ
        (Smat *ᵥ T.behaviorToRealizationPlan true β₁) = 0 := fun β₀ β₁ => by
    let β : ∀ i, ∀ h : H i, Act i h → ℝ := fun | false => β₀ | true => β₁
    have h0 := evalBehavior_eq_seqPayoffMat T β false
    have h1 := evalBehavior_eq_seqPayoffMat T β true
    have hsum := hzs.evalBehavior_true β
    dsimp [β] at h0 h1 hsum
    rw [add_mulVec, dotProduct_add]; linarith
  have hright : ∀ (β₀ : ∀ h : H false, Act false h → ℝ) (σ₁ : SeqVar T true),
      (T.behaviorToRealizationPlan false β₀) ⬝ᵥ (Smat *ᵥ Pi.single σ₁ (1 : ℝ)) = 0 :=
    fun β₀ σ₁ => by
      rcases exists_behavior_diff_eq_single (hpr true) σ₁ with ⟨_, h0⟩ | ⟨γ₁, γ₀, hdiff⟩
      · rw [← h0, hbilin β₀ (fun _ _ => 0)]
      · rw [← hdiff, mulVec_sub, dotProduct_sub, hbilin β₀ γ₁, hbilin β₀ γ₀, sub_zero]
  ext σ₀ σ₁
  have hzero : Smat σ₀ σ₁ = 0 := by
    rw [← show (Pi.single σ₀ (1 : ℝ)) ⬝ᵥ (Smat *ᵥ Pi.single σ₁ (1 : ℝ)) = Smat σ₀ σ₁ by simp]
    rcases exists_behavior_diff_eq_single (hpr false) σ₀ with ⟨_, h0⟩ | ⟨β₁, β₀, hdiff⟩
    · rw [← h0, hright _ σ₁]
    · rw [← hdiff, sub_dotProduct, hright β₁ σ₁, hright β₀ σ₁, sub_zero]
  simp only [Smat, Matrix.add_apply, Matrix.neg_apply] at hzero ⊢
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
      M *ᵥ Sum.elim x q ≤ rhs ↔ T.IsRealizationPlan false x ∧ E₂ᵀ *ᵥ q ≤ A₀ᵀ *ᵥ x := fun x q => by
    have hl : ∀ σ₀, (M *ᵥ Sum.elim x q) (.inl σ₀) = -x σ₀ := fun σ₀ => by
      rw [Matrix.mulVec, dotProduct]
      dsimp only [Col]
      rw [Fintype.sum_sum_type]
      dsimp only [M]
      simp only [Sum.elim_inl, Sum.elim_inr, zero_mul, sum_const_zero, add_zero]
      rw [sum_eq_single σ₀ (fun _ _ hne => by simp [hne.symm]) (fun h => absurd (mem_univ σ₀) h)]
      simp
    have he1 : ∀ row₁, (M *ᵥ Sum.elim x q) (.inr (.inl row₁)) = (E₁ *ᵥ x) row₁ := fun row₁ => by
      rw [Matrix.mulVec, dotProduct]
      dsimp only [Col]
      rw [Fintype.sum_sum_type]
      dsimp only [M]
      simp only [Sum.elim_inl, Sum.elim_inr, zero_mul, sum_const_zero, add_zero]; rfl
    have he1n : ∀ row₁, (M *ᵥ Sum.elim x q) (.inr (.inr (.inl row₁))) = -(E₁ *ᵥ x) row₁ :=
      fun row₁ => by
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
      simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, sum_neg_distrib, Matrix.mulVec, dotProduct,
        Matrix.transpose_apply]
      rfl
    refine ⟨fun hle => ⟨⟨fun σ => ?_, funext fun row₁ => ?_⟩, fun τ => ?_⟩,
      fun ⟨⟨hxnn, hxeq⟩, hqle⟩ r => ?_⟩
    · have h := hle (.inl σ)
      rw [hl] at h
      dsimp only [rhs] at h
      linarith
    · have h1 := hle (.inr (.inl row₁))
      have h2 := hle (.inr (.inr (.inl row₁)))
      rw [he1] at h1
      rw [he1n] at h2
      dsimp only [rhs] at h1 h2; linarith
    · have h := hle (.inr (.inr (.inr τ)))
      rw [hlcp] at h
      dsimp only [rhs] at h
      linarith
    · rcases r with σ₀ | (row₁ | (row₁ | τ))
      · rw [hl]
        dsimp only [rhs]
        linarith [hxnn σ₀]
      · rw [he1, hxeq]
      · rw [he1n, hxeq]
      · rw [hlcp]
        dsimp only [rhs]
        linarith [hqle τ]
  have hM_vecMul : ∀ (s : SeqVar T false → ℝ) (p₁ p₂ : S₁ → ℝ) (y : SeqVar T true → ℝ),
      Sum.elim s (Sum.elim p₁ (Sum.elim p₂ y)) ᵥ* M = obj ↔
        s = E₁ᵀ *ᵥ (p₁ - p₂) - A₀ *ᵥ y ∧ E₂ *ᵥ y = e₂ := fun s p₁ p₂ y => by
    have hL : ∀ σ, (Sum.elim s (Sum.elim p₁ (Sum.elim p₂ y)) ᵥ* M) (.inl σ) =
        -s σ + (E₁ᵀ *ᵥ (p₁ - p₂)) σ - (A₀ *ᵥ y) σ := fun σ => by
      rw [vecMul, dotProduct]
      dsimp only [M, Row]
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      have hs : ∑ σ₀ : SeqVar T false, s σ₀ * (if σ₀ = σ then (-1 : ℝ) else 0) = -s σ := by
        rw [sum_eq_single σ (fun _ _ hne => by simp [hne]) (fun h => absurd (mem_univ σ) h)]
        simp
      rw [hs]
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.sub_apply, mul_neg,
        sum_neg_distrib, sub_eq_add_neg]
      have hc1 : ∑ x, p₁ x * E₁ x σ - ∑ x, p₂ x * E₁ x σ = ∑ x, E₁ x σ * (p₁ x + -p₂ x) := by
        rw [← sum_sub_distrib]
        exact sum_congr rfl fun _ _ => by ring
      have hc2 : ∑ x, y x * A₀ σ x = ∑ x, A₀ σ x * y x := sum_congr rfl fun _ _ => mul_comm _ _
      linarith
    have hR : ∀ row₂, (Sum.elim s (Sum.elim p₁ (Sum.elim p₂ y)) ᵥ* M) (.inr row₂) =
        (E₂ *ᵥ y) row₂ := fun row₂ => by
      rw [vecMul, dotProduct]
      dsimp only [M, Row]
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, mul_zero, sum_const_zero, zero_add,
        Matrix.mulVec, dotProduct]
      exact sum_congr rfl fun _ _ => mul_comm _ _
    refine ⟨fun heq => ⟨funext fun σ => ?_, funext fun row₂ => ?_⟩,
      fun ⟨hs, hy⟩ => funext fun c => ?_⟩
    · have h := congrFun heq (.inl σ)
      rw [hL] at h
      dsimp only [obj] at h
      simp only [Sum.elim_inl, Pi.zero_apply] at h
      change s σ = (E₁ᵀ *ᵥ (p₁ - p₂)) σ - (A₀ *ᵥ y) σ
      linarith
    · have h := congrFun heq (.inr row₂)
      rwa [hR] at h
    · rcases c with σ | row₂
      · rw [hL]
        have hσ := congrFun hs σ
        change s σ = (E₁ᵀ *ᵥ (p₁ - p₂)) σ - (A₀ *ᵥ y) σ at hσ
        dsimp only [obj]
        simp only [Sum.elim_inl, Pi.zero_apply]; linarith
      · rw [hR]
        exact congrFun hy row₂
  have hobj_eval : ∀ x q, obj ⬝ᵥ Sum.elim x q = q none := fun x q => by
    dsimp only [obj, dotProduct, Col]
    rw [Fintype.sum_sum_type]
    simp only [e₂, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zero_mul, sum_const_zero, zero_add]
    exact seqRhs_dotProduct T true q
  have hrhs_eval : ∀ s p₁ p₂ y,
      Sum.elim s (Sum.elim p₁ (Sum.elim p₂ y)) ⬝ᵥ rhs = p₁ none - p₂ none := fun s p₁ p₂ y => by
    dsimp only [dotProduct, Row]
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [rhs, e₁, Sum.elim_inl, Sum.elim_inr, mul_zero, sum_const_zero, zero_add, add_zero,
      mul_neg, sum_neg_distrib]
    change (p₁ ⬝ᵥ seqRhs T false) + -(p₂ ⬝ᵥ seqRhs T false) = p₁ none - p₂ none
    rw [dotProduct_seqRhs, dotProduct_seqRhs, sub_eq_add_neg]
  let liftDual (y : SeqVar T true → ℝ) (p : S₁ → ℝ) : Row → ℝ :=
    Sum.elim (E₁ᵀ *ᵥ p - A₀ *ᵥ y)
      (Sum.elim (fun r => max (p r) 0) (Sum.elim (fun r => max (-p r) 0) y))
  have hliftDual : ∀ y p, T.IsRealizationPlan true y → A₀ *ᵥ y ≤ E₁ᵀ *ᵥ p →
      (0 ≤ liftDual y p ∧ liftDual y p ᵥ* M = obj) ∧ liftDual y p ⬝ᵥ rhs = p none :=
    fun y p hy hp => by
      have hpdiff : (fun r => max (p r) 0) - (fun r => max (-p r) 0) = p :=
        funext fun r => max_sub_max_neg (p r)
      refine ⟨⟨fun r => ?_, (hM_vecMul _ _ _ y).2 ⟨by rw [hpdiff], hy.2⟩⟩, ?_⟩
      · rcases r with σ | (_ | (_ | τ))
        · exact sub_nonneg.2 (hp σ)
        · exact le_max_right _ _
        · exact le_max_right _ _
        · exact hy.1 τ
      · dsimp only [liftDual]
        rw [hrhs_eval]
        exact max_sub_max_neg (p none)
  have hP : ∃ u : Col → ℝ, M *ᵥ u ≤ rhs := by
    let x₀ := T.pureToRealizationPlan false (fun _ => Classical.arbitrary _)
    obtain ⟨qNeg, hqNeg⟩ := exists_seqMat_transpose_mulVec_ge (hpr true) (-(A₀ᵀ *ᵥ x₀))
    refine ⟨Sum.elim x₀ (-qNeg), (hM_mulVec x₀ (-qNeg)).2
      ⟨isRealizationPlan_pureToRealizationPlan (hpr false) _, fun τ => ?_⟩⟩
    have hτ := hqNeg τ
    rw [Matrix.mulVec_neg, Pi.neg_apply]
    linarith [show -((A₀ᵀ *ᵥ x₀) τ) ≤ (E₂ᵀ *ᵥ qNeg) τ from hτ]
  have hD : ∃ v : Row → ℝ, 0 ≤ v ∧ v ᵥ* M = obj := by
    let y₀ := T.pureToRealizationPlan true (fun _ => Classical.arbitrary _)
    obtain ⟨p₀, hp₀⟩ := exists_seqMat_transpose_mulVec_ge (hpr false) (A₀ *ᵥ y₀)
    exact ⟨liftDual y₀ p₀, (hliftDual y₀ p₀
      (isRealizationPlan_pureToRealizationPlan (hpr true) _) hp₀).1⟩
  obtain ⟨val, ⟨⟨uStar, huStar_le, hval_u⟩, hmax⟩,
      ⟨⟨vStar, ⟨hvStar_nn, hvStar_eq⟩, hval_v⟩, hmin⟩⟩ :=
    Matrix.exists_isGreatest_isLeast_dotProduct M rhs obj hP hD
  dsimp only at hval_u hval_v
  let xStar : SeqVar T false → ℝ := uStar ∘ .inl
  let qStar : S₂ → ℝ := uStar ∘ .inr
  have huStar_eq : uStar = Sum.elim xStar qStar := by
    ext c
    cases c <;> rfl
  have hxStar_qStar := (hM_mulVec xStar qStar).1 (huStar_eq ▸ huStar_le)
  have hqStar_val : qStar none = val := by rw [← hval_u, huStar_eq, hobj_eval]
  let sStar : SeqVar T false → ℝ := fun σ => vStar (.inl σ)
  let p₁Star : S₁ → ℝ := fun r => vStar (.inr (.inl r))
  let p₂Star : S₁ → ℝ := fun r => vStar (.inr (.inr (.inl r)))
  let yStar : SeqVar T true → ℝ := fun τ => vStar (.inr (.inr (.inr τ)))
  have hvStar_split : vStar = Sum.elim sStar (Sum.elim p₁Star (Sum.elim p₂Star yStar)) := by
    ext r
    rcases r with _ | (_ | (_ | _)) <;> rfl
  have hvStar_rel := (hM_vecMul sStar p₁Star p₂Star yStar).1 (hvStar_split ▸ hvStar_eq)
  let pStar : S₁ → ℝ := p₁Star - p₂Star
  have hyStar_feas : T.IsRealizationPlan true yStar :=
    ⟨fun τ => hvStar_nn (.inr (.inr (.inr τ))), hvStar_rel.2⟩
  have hpStar_feas : A₀ *ᵥ yStar ≤ E₁ᵀ *ᵥ pStar := fun σ => by
    have hsσ : 0 ≤ sStar σ := hvStar_nn (.inl σ)
    have heq := congrFun hvStar_rel.1 σ
    change sStar σ = (E₁ᵀ *ᵥ pStar) σ - (A₀ *ᵥ yStar) σ at heq
    linarith
  have hpStar_val : pStar none = val := by rw [← hval_v, hvStar_split, hrhs_eval]; rfl
  have hweak_opt := seq_weak_duality hxStar_qStar.1 hyStar_feas hxStar_qStar.2 hpStar_feas
  have hmid : xStar ⬝ᵥ (A₀ *ᵥ yStar) = val :=
    le_antisymm (hpStar_val ▸ hweak_opt.2) (hqStar_val ▸ hweak_opt.1)
  have hbr0 : T.IsSeqBestResponseFalse xStar yStar :=
    ⟨hxStar_qStar.1, fun x' hx' => by
      have hw := seq_weak_duality_upper hx' hpStar_feas
      rwa [hpStar_val, ← hmid] at hw⟩
  have hbr1 : T.IsSeqBestResponseTrue yStar xStar :=
    ⟨hyStar_feas, fun y' hy' => by
      have hw := seq_weak_duality_lower hy' hxStar_qStar.2
      rw [hqStar_val, ← hmid] at hw
      rw [hzs.seqPayoffMat_true_of_perfectRecall hpr, neg_mulVec, dotProduct_neg, neg_mulVec,
        dotProduct_neg, neg_le_neg_iff]
      exact hw⟩
  refine ⟨val, xStar, yStar, qStar, pStar, hxStar_qStar.1, hyStar_feas, hxStar_qStar.2,
    hpStar_feas, hmid, hqStar_val, hpStar_val, ⟨hbr0, hbr1⟩,
    ⟨⟨(xStar, qStar), hxStar_qStar, hqStar_val⟩, ?_⟩,
    ⟨⟨(yStar, pStar), ⟨hyStar_feas, hpStar_feas⟩, hpStar_val⟩, ?_⟩⟩
  · rintro _ ⟨⟨x, q⟩, hxq, rfl⟩
    have hle := hmax ⟨Sum.elim x q, (hM_mulVec x q).2 hxq, rfl⟩
    dsimp only at hle ⊢
    rwa [hobj_eval] at hle
  · rintro _ ⟨⟨y, p⟩, ⟨hy, hp⟩, rfl⟩
    obtain ⟨hfeas, hobj⟩ := hliftDual y p hy hp
    have hle := hmin ⟨liftDual y p, hfeas, rfl⟩
    dsimp only at hle ⊢
    rwa [hobj] at hle

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
