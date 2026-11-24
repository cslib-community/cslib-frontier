/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.LinearAlgebra.Matrix.VertexExtremePoints
public import CslibFrontier.GameTheory.Extensive.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.Convex.Combination
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Infix
import Mathlib.Data.List.Sigma
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Sequence form, realization plans, and Kuhn's theorem

This module develops the sequence form of an extensive-form game for a player `i` with perfect
recall ([vonStengel2007], Sections 3.9–3.10):

* `SeqVar T i`: the finite type of realized player-`i` sequences (`σ : Seq H Act i` occurring as a
  prefix of some terminal path's `z.seq i`).
* Under `PerfectRecall T i`, every occurring information set `h` has a unique preceding
  player-`i` sequence `infoSeq T i h`, and `seqVarEquiv` bijects `Unit ⊕ (Σ h, Act i h.1)` with
  `SeqVar T i` (`|S_i| = 1 + ∑_{h ∈ H_i} |C_h|`, `card_seqVar`, [vonStengel2007], §3.10, p. 70).
* `seqMat T i *ᵥ x = seqRhs T i` (`E x = e`) and `x ≥ 0` define `IsRealizationPlan T i x`,
  unfolded by `isRealizationPlan_iff` as `x ∅ = 1` together with flow conservation
  `∑ a : Act i h, x (σ_h a) = x σ_h` at each occurring information set `h`.
* **Proposition 3.10** ([vonStengel2007], §3.10): `isRealizationPlan_mixedToRealizationPlan`,
  `isRealizationPlan_behaviorToRealizationPlan`, `isBehaviorStrategy_realizationPlanToBehavior`,
  `behaviorToRealizationPlan_realizationPlanToBehavior`, and `realizationPlanToBehavior_unique`.
* **Proposition 3.11** ([vonStengel2007], §3.10):
  `realizationEquivMixed_iff_mixedToRealizationPlan_eq` — two mixed strategies of player `i` are
  realization-equivalent iff they induce the same realization plan (under positive chance
  probabilities and no repeated opponent information sets).
* **Corollary 3.12 (Kuhn's theorem)** ([vonStengel2007], §3.10): `kuhn_theorem` and
  `kuhn_theorem_exists` — under `PerfectRecall T i`, every mixed strategy of player `i` is
  realization-equivalent to an explicit behavioral strategy `realizationPlanToBehavior`.
* Reduced strategic form & realization-plan polytope ([vonStengel2007], §§3.9–3.10):
  `ReducedEquiv`, `reducedEquiv_iff_agree_on_reachable`, `evalPure_eq_of_reducedEquiv`,
  `isRealizationPlan_iff_mem_convexHull`, `mem_extremePoints_isRealizationPlan_iff`, and
  `isVertex_seqPolyMat_iff` linking to `Matrix.IsVertex`.
* Two-player bilinear sequence form ([vonStengel2007], §3.10): `seqPayoffMat`,
  `evalBehavior_eq_seqPayoffMat`, `evalMixed_eq_seqPayoffMat`.

## References

* [B. von Stengel, *Equilibrium Computation for Two-Player Games in Strategic and Extensive
  Form*][vonStengel2007], Sections 3.9–3.10.
-/

public section

namespace Cslib.GameTheory.Extensive

open Finset Matrix

universe u v

section Structural

variable {ι : Type u} {H : ι → Type v} {Act : ∀ i, H i → Type}

/-- Given a node `v` where player `i` decides at information set `h` and an action `a : Act i h`,
extend `v` through `a` to a terminal path. -/
noncomputable def Node.extendDecisionOf [∀ j h', Nonempty (Act j h')] {i : ι} {h : H i} :
    {T : ExtensiveTree ι H Act} → (v : Node T) → v.IsDecisionOf i h → Act i h → Terminal T
  | .leaf _, .here, hv, _ => False.elim hv
  | .decision j h' next, .here, hv, a => by
      have hj : j = i := (Sigma.mk.inj_iff.1 hv).1
      cases hj
      have hh : h' = h := eq_of_heq (Sigma.mk.inj_iff.1 hv).2
      cases hh
      exact .decision a (Classical.arbitrary (Terminal (next a)))
  | @ExtensiveTree.chance _ _ _ _ _ _ _ _, .chance c sub, hv, a =>
      .chance c (sub.extendDecisionOf hv a)
  | .decision _ _ _, .decision b sub, hv, a =>
      .decision b (sub.extendDecisionOf hv a)

theorem Node.playerSeq_append_singleton_prefix_extendDecisionOf [DecidableEq ι]
    [∀ j h', Nonempty (Act j h')] {i : ι} {h : H i} :
    ∀ {T : ExtensiveTree ι H Act} (v : Node T) (hv : v.IsDecisionOf i h) (a : Act i h),
      v.playerSeq i ++ [⟨h, a⟩] <+: (v.extendDecisionOf hv a).seq i
  | .leaf _, .here, hv, _ => False.elim hv
  | .decision j h' next, .here, hv, a => by
      have hj : j = i := (Sigma.mk.inj_iff.1 hv).1
      cases hj
      have hh : h' = h := eq_of_heq (Sigma.mk.inj_iff.1 hv).2
      cases hh
      simp [Node.extendDecisionOf, Terminal.seq_decision_self, Node.playerSeq_here]
  | @ExtensiveTree.chance _ _ _ _ _ _ _ _, .chance c sub, hv, a => by
      simp only [Node.playerSeq_chance, Node.extendDecisionOf, Terminal.seq_chance]
      exact sub.playerSeq_append_singleton_prefix_extendDecisionOf hv a
  | .decision j h' next, .decision b sub, hv, a => by
      by_cases hij : j = i
      · subst hij
        simp only [Node.playerSeq_decision_self, List.cons_append, Node.extendDecisionOf,
          Terminal.seq_decision_self, List.cons_prefix_cons, true_and]
        exact sub.playerSeq_append_singleton_prefix_extendDecisionOf hv a
      · simp only [Node.playerSeq_decision_ne hij, Node.extendDecisionOf,
          Terminal.seq_decision_ne hij]
        exact sub.playerSeq_append_singleton_prefix_extendDecisionOf hv a

theorem Node.playerSeq_prefix_extendDecisionOf [DecidableEq ι]
    [∀ j h', Nonempty (Act j h')] {i : ι} {h : H i} {T : ExtensiveTree ι H Act}
    (v : Node T) (hv : v.IsDecisionOf i h) (a : Act i h) :
    v.playerSeq i <+: (v.extendDecisionOf hv a).seq i :=
  (List.prefix_append _ [⟨h, a⟩]).trans (v.playerSeq_append_singleton_prefix_extendDecisionOf hv a)

/-- Every decomposition `z.seq i = pre ++ ⟨h, a⟩ :: post` identifies a decision node `v` of
player `i` at information set `h` along `z` whose preceding player-`i` sequence is `pre`. -/
theorem Terminal.exists_node_of_seq_append [DecidableEq ι] {i : ι} :
    ∀ {T : ExtensiveTree ι H Act} (z : Terminal T) (pre post : Seq H Act i)
      (h : H i) (a : Act i h),
      z.seq i = pre ++ ⟨h, a⟩ :: post →
        ∃ v : Node T, v.IsDecisionOf i h ∧ v.playerSeq i = pre
  | .leaf _, .leaf, pre, _, _, _, hseq => by
      rw [Terminal.seq_leaf] at hseq
      exact absurd hseq (by cases pre <;> simp)
  | @ExtensiveTree.chance _ _ _ _ _ _ _ _, .chance c sub, pre, post, h, a, hseq => by
      rw [Terminal.seq_chance] at hseq
      obtain ⟨v, hv, hpre⟩ := sub.exists_node_of_seq_append pre post h a hseq
      exact ⟨.chance c v, hv, hpre⟩
  | .decision j h' _, .decision a' sub, [], post, h, a, hseq => by
      by_cases hij : j = i
      · subst hij
        rw [Terminal.seq_decision_self] at hseq
        simp only [List.nil_append, List.cons.injEq] at hseq
        have hh : h' = h := (Sigma.mk.inj_iff.1 hseq.1).1
        subst hh
        exact ⟨.here, rfl, rfl⟩
      · rw [Terminal.seq_decision_ne hij] at hseq
        obtain ⟨v, hv, hpre⟩ := sub.exists_node_of_seq_append [] post h a hseq
        exact ⟨.decision a' v, hv, by simp [hij, hpre]⟩
  | .decision j h' _, .decision a' sub, q :: pre', post, h, a, hseq => by
      by_cases hij : j = i
      · subst hij
        rw [Terminal.seq_decision_self] at hseq
        simp only [List.cons_append, List.cons.injEq] at hseq
        rcases hseq with ⟨rfl, htail⟩
        obtain ⟨v, hv, hpre⟩ := sub.exists_node_of_seq_append pre' post h a htail
        exact ⟨.decision a' v, hv, by simp [hpre]⟩
      · rw [Terminal.seq_decision_ne hij] at hseq
        obtain ⟨v, hv, hpre⟩ := sub.exists_node_of_seq_append (q :: pre') post h a hseq
        exact ⟨.decision a' v, hv, by simp [hij, hpre]⟩

private theorem exists_strict_prefix_of_mem_playerSeq [DecidableEq ι] {i : ι} :
    ∀ {T : ExtensiveTree ι H Act} (v : Node T) {h : H i},
      h ∈ (v.playerSeq i).map Sigma.fst →
        ∃ u : Node T, u.IsDecisionOf i h ∧ (u.playerSeq i).length < (v.playerSeq i).length
  | _, .here => fun hmem => by simp at hmem
  | @ExtensiveTree.chance _ _ _ _ _ _ _ _, .chance c sub => fun hmem => by
      obtain ⟨u, hu, hlen⟩ := exists_strict_prefix_of_mem_playerSeq sub hmem
      exact ⟨.chance c u, hu, hlen⟩
  | .decision j h' _, .decision a sub => fun hmem => by
      by_cases hij : j = i
      · subst hij
        simp only [Node.playerSeq_decision_self, List.map_cons, List.mem_cons] at hmem
        rcases hmem with rfl | hmem
        · exact ⟨.here, rfl, by simp⟩
        · obtain ⟨u, hu, hlen⟩ := exists_strict_prefix_of_mem_playerSeq sub hmem
          exact ⟨.decision a u, hu, by simp [hlen]⟩
      · simp only [Node.playerSeq_decision_ne hij] at hmem
        obtain ⟨u, hu, hlen⟩ := exists_strict_prefix_of_mem_playerSeq sub hmem
        exact ⟨.decision a u, hu, by simp [hij, hlen]⟩

/-- Finite type of player-`i` choice sequences occurring as a prefix of at least one terminal play
in `T`. -/
abbrev SeqVar [DecidableEq ι] (T : ExtensiveTree ι H Act) (i : ι) : Type v :=
  {σ : Seq H Act i // ∃ z : Terminal T, σ <+: z.seq i}

open Classical in
/-- Finite set of all player-`i` sequences occurring as a prefix of some terminal play in `T`. -/
noncomputable def occursSeqFinset [DecidableEq ι] [∀ j h, Fintype (Act j h)]
    (T : ExtensiveTree ι H Act) (i : ι) : Finset (Seq H Act i) :=
  univ.biUnion fun z : Terminal T => (z.seq i).inits.toFinset

theorem mem_occursSeqFinset [DecidableEq ι] [∀ j h, Fintype (Act j h)]
    {T : ExtensiveTree ι H Act} {i : ι} {σ : Seq H Act i} :
    σ ∈ occursSeqFinset T i ↔ ∃ z : Terminal T, σ <+: z.seq i := by
  simp only [occursSeqFinset, mem_biUnion, mem_univ, true_and, List.mem_toFinset, List.mem_inits]

open Classical in
noncomputable instance SeqVar.instFintype [DecidableEq ι] [∀ j h, Fintype (Act j h)]
    (T : ExtensiveTree ι H Act) (i : ι) : Fintype (SeqVar T i) :=
  Fintype.subtype (occursSeqFinset T i) fun _ => mem_occursSeqFinset

open Classical in
/-- Under perfect recall for player `i`, the unique player-`i` choice sequence preceding every
decision node of information set `h`. -/
noncomputable def ExtensiveTree.infoSeq [DecidableEq ι] (T : ExtensiveTree ι H Act) (i : ι)
    (h : H i) : Seq H Act i :=
  if hex : T.OccursInfoSet i h then hex.choose.playerSeq i else []

theorem ExtensiveTree.PerfectRecall.playerSeq_eq_infoSeq [DecidableEq ι]
    {T : ExtensiveTree ι H Act} {i : ι} (hpr : T.PerfectRecall i) {h : H i} {v : Node T}
    (hv : v.IsDecisionOf i h) :
    v.playerSeq i = T.infoSeq i h := by
  have hex : T.OccursInfoSet i h := ⟨v, hv⟩
  simp only [ExtensiveTree.infoSeq, hex, ↓reduceDIte]
  exact hpr hv hex.choose_spec

theorem ExtensiveTree.PerfectRecall.not_mem_infoSeq [DecidableEq ι]
    {T : ExtensiveTree ι H Act} {i : ι} (hpr : T.PerfectRecall i) {h : H i}
    (hh : T.OccursInfoSet i h) :
    h ∉ (T.infoSeq i h).map Sigma.fst := by
  intro hmem
  obtain ⟨v, hv⟩ := hh
  rw [← hpr.playerSeq_eq_infoSeq hv] at hmem
  obtain ⟨u, hu, hlen⟩ := exists_strict_prefix_of_mem_playerSeq v hmem
  rw [hpr.playerSeq_eq_infoSeq hv, hpr.playerSeq_eq_infoSeq hu] at hlen
  exact lt_irrefl _ hlen

/-- The empty sequence `[]` in `SeqVar T i`. -/
def SeqVar.nil [DecidableEq ι] [∀ j h, Nonempty (Act j h)]
    (T : ExtensiveTree ι H Act) (i : ι) : SeqVar T i :=
  ⟨[], let ⟨z⟩ := Terminal.instNonempty T; ⟨z, List.nil_prefix⟩⟩

@[simp]
theorem SeqVar.nil_val [DecidableEq ι] [∀ j h, Nonempty (Act j h)]
    (T : ExtensiveTree ι H Act) (i : ι) :
    (SeqVar.nil T i).1 = [] := by
  simp [SeqVar.nil]

/-- `T.infoSeq i h` as an element of `SeqVar T i` when `h` occurs in `T`. -/
noncomputable def SeqVar.infoSeq [DecidableEq ι] [∀ j h, Nonempty (Act j h)]
    {T : ExtensiveTree ι H Act} {i : ι} (hpr : T.PerfectRecall i) {h : H i}
    (hh : T.OccursInfoSet i h) : SeqVar T i :=
  ⟨T.infoSeq i h, by
    obtain ⟨v, hv⟩ := hh
    let a₀ := Classical.arbitrary (Act i h)
    refine ⟨v.extendDecisionOf hv a₀, ?_⟩
    rw [← hpr.playerSeq_eq_infoSeq hv]
    exact v.playerSeq_prefix_extendDecisionOf hv a₀⟩

/-- Extension `T.infoSeq i h ++ [⟨h, a⟩]` as an element of `SeqVar T i`. -/
noncomputable def SeqVar.infoSeqExt [DecidableEq ι] [∀ j h, Nonempty (Act j h)]
    {T : ExtensiveTree ι H Act} {i : ι} (hpr : T.PerfectRecall i) {h : H i}
    (hh : T.OccursInfoSet i h) (a : Act i h) : SeqVar T i :=
  ⟨T.infoSeq i h ++ [⟨h, a⟩], by
    obtain ⟨v, hv⟩ := hh
    refine ⟨v.extendDecisionOf hv a, ?_⟩
    rw [← hpr.playerSeq_eq_infoSeq hv]
    exact v.playerSeq_append_singleton_prefix_extendDecisionOf hv a⟩

theorem SeqVar.infoSeq_val [DecidableEq ι] [∀ j h, Nonempty (Act j h)]
    {T : ExtensiveTree ι H Act} {i : ι} (hpr : T.PerfectRecall i) {h : H i}
    (hh : T.OccursInfoSet i h) :
    (SeqVar.infoSeq hpr hh).1 = T.infoSeq i h := by
  rw [SeqVar.infoSeq]

theorem SeqVar.infoSeqExt_val [DecidableEq ι] [∀ j h, Nonempty (Act j h)]
    {T : ExtensiveTree ι H Act} {i : ι} (hpr : T.PerfectRecall i) {h : H i}
    (hh : T.OccursInfoSet i h) (a : Act i h) :
    (SeqVar.infoSeqExt hpr hh a).1 = T.infoSeq i h ++ [⟨h, a⟩] := by
  rw [SeqVar.infoSeqExt]

private theorem seqVar_infoSeqExt_ne_nil [DecidableEq ι] [∀ j h, Nonempty (Act j h)]
    {T : ExtensiveTree ι H Act} {i : ι} (hpr : T.PerfectRecall i) {h : H i}
    (hh : T.OccursInfoSet i h) (a : Act i h) :
    (SeqVar.infoSeqExt hpr hh a).1 ≠ [] := by
  simp [SeqVar.infoSeqExt]

private theorem seqVar_infoSeqExt_inj [DecidableEq ι] [∀ j h, Nonempty (Act j h)]
    {T : ExtensiveTree ι H Act} {i : ι} (hpr : T.PerfectRecall i)
    {h₁ h₂ : H i} {hh₁ : T.OccursInfoSet i h₁} {hh₂ : T.OccursInfoSet i h₂}
    {a₁ : Act i h₁} {a₂ : Act i h₂}
    (heq : SeqVar.infoSeqExt hpr hh₁ a₁ = SeqVar.infoSeqExt hpr hh₂ a₂) :
    (⟨⟨h₁, hh₁⟩, a₁⟩ : Σ h : {h : H i // T.OccursInfoSet i h}, Act i h.1) =
      ⟨⟨h₂, hh₂⟩, a₂⟩ := by
  have h1 : T.infoSeq i h₁ ++ [⟨h₁, a₁⟩] = T.infoSeq i h₂ ++ [⟨h₂, a₂⟩] := congrArg Subtype.val heq
  have hlast : ([⟨h₁, a₁⟩] : Seq H Act i) = [⟨h₂, a₂⟩] := List.append_inj_right' h1 rfl
  have hp : (⟨h₁, a₁⟩ : Choice H Act i) = ⟨h₂, a₂⟩ := (List.cons.inj hlast).1
  have hh : h₁ = h₂ := (Sigma.mk.inj_iff.1 hp).1
  cases hh
  have ha : a₁ = a₂ := eq_of_heq (Sigma.mk.inj_iff.1 hp).2
  cases ha
  rfl

theorem exists_infoSeqExt_of_seqVar_ne_nil [DecidableEq ι] [∀ j h, Nonempty (Act j h)]
    {T : ExtensiveTree ι H Act} {i : ι} (hpr : T.PerfectRecall i)
    (σ : SeqVar T i) (hne : σ.1 ≠ []) :
    ∃ (h : {h : H i // T.OccursInfoSet i h}) (a : Act i h.1),
      σ = SeqVar.infoSeqExt hpr h.2 a := by
  obtain ⟨z, post, hz⟩ := σ.2
  have hdrop : σ.1 = σ.1.dropLast ++ [σ.1.getLast hne] := (List.dropLast_append_getLast hne).symm
  generalize hq : σ.1.getLast hne = q
  rcases q with ⟨h, a⟩
  rw [hq] at hdrop
  have hseq : z.seq i = σ.1.dropLast ++ ⟨h, a⟩ :: post := by
    calc z.seq i = σ.1 ++ post := hz.symm
      _ = (σ.1.dropLast ++ [⟨h, a⟩]) ++ post := congrArg (· ++ post) hdrop
      _ = σ.1.dropLast ++ ⟨h, a⟩ :: post := by rw [List.append_assoc, List.singleton_append]
  obtain ⟨v, hv, hpre⟩ := z.exists_node_of_seq_append σ.1.dropLast post h a hseq
  have hh : T.OccursInfoSet i h := ⟨v, hv⟩
  refine ⟨⟨h, hh⟩, a, Subtype.ext ?_⟩
  have hpre_eq : σ.1.dropLast = T.infoSeq i h := by
    rw [← hpr.playerSeq_eq_infoSeq hv, hpre]
  calc σ.1 = σ.1.dropLast ++ [⟨h, a⟩] := hdrop
    _ = T.infoSeq i h ++ [⟨h, a⟩] := by rw [hpre_eq]

/-- Under perfect recall for player `i`, `SeqVar T i` is in bijection with
`Unit ⊕ (Σ h : {h : H i // T.OccursInfoSet i h}, Act i h.1)` ([vonStengel2007], Section 3.10). -/
noncomputable def seqVarEquiv [DecidableEq ι] [∀ j h, Nonempty (Act j h)]
    {T : ExtensiveTree ι H Act} {i : ι} (hpr : T.PerfectRecall i) :
    Unit ⊕ (Σ h : {h : H i // T.OccursInfoSet i h}, Act i h.1) ≃ SeqVar T i :=
  let toFun : Unit ⊕ (Σ h : {h : H i // T.OccursInfoSet i h}, Act i h.1) → SeqVar T i
    | .inl () => SeqVar.nil T i
    | .inr ⟨h, a⟩ => SeqVar.infoSeqExt hpr h.2 a
  have hinj : Function.Injective toFun := by
    rintro (⟨⟩ | ⟨h₁, a₁⟩) (⟨⟩ | ⟨h₂, a₂⟩) h
    · rfl
    · exact absurd (congrArg Subtype.val h).symm (seqVar_infoSeqExt_ne_nil hpr h₂.2 a₂)
    · exact absurd (congrArg Subtype.val h) (seqVar_infoSeqExt_ne_nil hpr h₁.2 a₁)
    · exact congrArg Sum.inr (seqVar_infoSeqExt_inj hpr h)
  have hsurj : Function.Surjective toFun := by
    intro σ
    by_cases hne : σ.1 = []
    · exact ⟨.inl (), Subtype.ext hne.symm⟩
    · obtain ⟨h, a, rfl⟩ := exists_infoSeqExt_of_seqVar_ne_nil hpr σ hne
      exact ⟨.inr ⟨h, a⟩, rfl⟩
  Equiv.ofBijective toFun ⟨hinj, hsurj⟩

open Classical in
/-- Under perfect recall for player `i`, the number of realized sequences equals
`1 + ∑ h ∈ H_i, |C_h|` ([vonStengel2007], Section 3.10, p. 70). -/
theorem card_seqVar [DecidableEq ι] [∀ j h, Fintype (Act j h)] [∀ j h, Nonempty (Act j h)]
    {T : ExtensiveTree ι H Act} {i : ι} [Fintype (H i)] (hpr : T.PerfectRecall i) :
    Fintype.card (SeqVar T i) =
      1 + ∑ h : {h : H i // T.OccursInfoSet i h}, Fintype.card (Act i h.1) := by
  rw [← Fintype.card_congr (seqVarEquiv hpr), Fintype.card_sum, Fintype.card_unit,
    Fintype.card_sigma]

end Structural

section RealizationPlans

variable {ι : Type u} {H : ι → Type v} {Act : ∀ i, H i → Type}

open Classical in
/-- Row index of the sequence-form constraint matrix `E x = e` ([vonStengel2007], Section 3.10):
`none` selects the root normalization `x [] = 1`, and `some h` selects flow conservation at
occurring information set `h`. -/
noncomputable instance SeqRow.instFintype (T : ExtensiveTree ι H Act)
    (i : ι) [Fintype (H i)] :
    Fintype (Option {h : H i // T.OccursInfoSet i h}) :=
  inferInstance

open Classical in
/-- Sequence-form constraint matrix `E` of player `i` ([vonStengel2007], Section 3.10):
* root row (`none`): `1` on `[]`, `0` elsewhere;
* information-set row (`some h`): `-1` on `infoSeq h`, `+1` on each extension
  `infoSeq h ++ [⟨h, a⟩]`, `0` elsewhere. -/
noncomputable def seqMat [DecidableEq ι] (T : ExtensiveTree ι H Act) (i : ι) :
    Matrix (Option {h : H i // T.OccursInfoSet i h}) (SeqVar T i) ℝ
  | none, σ => if σ.1 = [] then 1 else 0
  | some h, σ =>
      if σ.1 = T.infoSeq i h.1 then -1
      else if ∃ a : Act i h.1, σ.1 = T.infoSeq i h.1 ++ [⟨h.1, a⟩] then 1
      else 0

/-- Sequence-form right-hand side `e` (`1` at root `none`, `0` at every information set
`some h`). -/
def seqRhs (T : ExtensiveTree ι H Act) (i : ι) :
    Option {h : H i // T.OccursInfoSet i h} → ℝ
  | none => 1
  | some _ => 0

@[simp]
theorem seqRhs_none (T : ExtensiveTree ι H Act) (i : ι) :
    seqRhs T i none = 1 := by
  simp [seqRhs]

@[simp]
theorem seqRhs_some (T : ExtensiveTree ι H Act) (i : ι) (h : {h : H i // T.OccursInfoSet i h}) :
    seqRhs T i (some h) = 0 := by
  simp [seqRhs]

/-- A **realization plan** of player `i` is a nonnegative vector `x : SeqVar T i → ℝ` satisfying
`seqMat T i *ᵥ x = seqRhs T i` ([vonStengel2007], Section 3.10). -/
@[expose] def ExtensiveTree.IsRealizationPlan [DecidableEq ι] [∀ j h, Fintype (Act j h)]
    (T : ExtensiveTree ι H Act) (i : ι) (x : SeqVar T i → ℝ) : Prop :=
  (∀ σ, 0 ≤ x σ) ∧ seqMat T i *ᵥ x = seqRhs T i

theorem seqMat_mulVec_none [DecidableEq ι] [∀ j h, Fintype (Act j h)]
    [∀ j h, Nonempty (Act j h)] (T : ExtensiveTree ι H Act) (i : ι)
    (x : SeqVar T i → ℝ) :
    (seqMat T i *ᵥ x) none = x (SeqVar.nil T i) := by
  classical
  simp only [Matrix.mulVec, dotProduct, seqMat]
  rw [sum_eq_single (SeqVar.nil T i)]
  · simp [SeqVar.nil]
  · intro σ _ hne
    have hne' : σ.1 ≠ [] := fun h => hne (Subtype.ext h)
    simp [hne']
  · intro hmem
    exact absurd (mem_univ _) hmem

theorem seqMat_mulVec_some [DecidableEq ι] [∀ j h, Fintype (Act j h)]
    [∀ j h, Nonempty (Act j h)] {T : ExtensiveTree ι H Act} {i : ι}
    (hpr : T.PerfectRecall i) (h : {h : H i // T.OccursInfoSet i h}) (x : SeqVar T i → ℝ) :
    (seqMat T i *ᵥ x) (some h) =
      -x (SeqVar.infoSeq hpr h.2) + ∑ a : Act i h.1, x (SeqVar.infoSeqExt hpr h.2 a) := by
  classical
  let S : Finset (SeqVar T i) :=
    insert (SeqVar.infoSeq hpr h.2) (univ.image fun a : Act i h.1 => SeqVar.infoSeqExt hpr h.2 a)
  have hS_subset : S ⊆ univ := subset_univ _
  have hzero : ∀ σ ∈ (univ : Finset (SeqVar T i)), σ ∉ S →
      seqMat T i (some h) σ * x σ = 0 := by
    intro σ _ hσ
    have h1 : σ.1 ≠ T.infoSeq i h.1 := fun heq =>
      hσ (mem_insert.2 (Or.inl (Subtype.ext heq)))
    have h2 : ¬ ∃ a : Act i h.1, σ.1 = T.infoSeq i h.1 ++ [⟨h.1, a⟩] := by
      rintro ⟨a, ha⟩
      exact hσ (mem_insert.2 (Or.inr (mem_image.2 ⟨a, mem_univ a, Subtype.ext ha.symm⟩)))
    simp [seqMat, h1, h2]
  rw [Matrix.mulVec, dotProduct, ← sum_subset hS_subset hzero]
  simp only [seqMat]
  have hnotmem : SeqVar.infoSeq hpr h.2 ∉
      univ.image (fun a : Act i h.1 => SeqVar.infoSeqExt hpr h.2 a) := by
    simp only [mem_image, mem_univ, true_and, not_exists]
    intro a heq
    have hlen := congrArg (List.length ∘ Subtype.val) heq
    simp [SeqVar.infoSeq, SeqVar.infoSeqExt] at hlen
  rw [sum_insert hnotmem]
  congr 1
  · simp [SeqVar.infoSeq]
  · rw [sum_image]
    · refine sum_congr rfl fun a _ => ?_
      have hne_len : (SeqVar.infoSeqExt hpr h.2 a).1 ≠ T.infoSeq i h.1 := by
        intro heq
        have hlen := congrArg List.length heq
        simp [SeqVar.infoSeqExt] at hlen
      have hex : ∃ b : Act i h.1, (SeqVar.infoSeqExt hpr h.2 a).1 = T.infoSeq i h.1 ++ [⟨h.1, b⟩] :=
        ⟨a, rfl⟩
      simp [hne_len, hex]
    · intro a₁ _ a₂ _ heq
      have h1 := seqVar_infoSeqExt_inj hpr heq
      exact eq_of_heq (Sigma.mk.inj_iff.1 h1).2

/-- **Proposition 3.10 (characterization)** ([vonStengel2007], Section 3.10): under perfect recall,
`IsRealizationPlan T i x` holds iff `x ≥ 0`, `x [] = 1`, and for every occurring information set `h`
of player `i`, `∑ a : Act i h, x (infoSeq h ++ [⟨h, a⟩]) = x (infoSeq h)`. -/
theorem isRealizationPlan_iff [DecidableEq ι] [∀ j h, Fintype (Act j h)]
    [∀ j h, Nonempty (Act j h)] {T : ExtensiveTree ι H Act} {i : ι}
    (hpr : T.PerfectRecall i) (x : SeqVar T i → ℝ) :
    T.IsRealizationPlan i x ↔
      (∀ σ, 0 ≤ x σ) ∧ x (SeqVar.nil T i) = 1 ∧
        ∀ h (hh : T.OccursInfoSet i h),
          ∑ a : Act i h, x (SeqVar.infoSeqExt hpr hh a) = x (SeqVar.infoSeq hpr hh) := by
  constructor
  · rintro ⟨hnn, heq⟩
    refine ⟨hnn, ?_, ?_⟩
    · have h0 := congrFun heq none
      simpa [seqMat_mulVec_none, seqRhs] using h0
    · intro h hh
      have hh0 := congrFun heq (some ⟨h, hh⟩)
      rw [seqMat_mulVec_some hpr ⟨h, hh⟩, seqRhs] at hh0
      linarith
  · rintro ⟨hnn, hnil, hflow⟩
    refine ⟨hnn, funext fun r => ?_⟩
    cases r with
    | none => simp [seqMat_mulVec_none, seqRhs, hnil]
    | some h =>
      rw [seqMat_mulVec_some hpr h, seqRhs, hflow h.1 h.2]
      ring

/-- Realization plan induced by a mixed strategy `μ` of player `i`. -/
noncomputable def ExtensiveTree.mixedToRealizationPlan [DecidableEq ι]
    (T : ExtensiveTree ι H Act) (i : ι) [Fintype (H i)] [DecidableEq (H i)]
    [∀ j h, Fintype (Act j h)] (μ : PureStrategy H Act i → ℝ) (σ : SeqVar T i) : ℝ :=
  realizationProbMixed μ σ.1

/-- Unfolding equation for `ExtensiveTree.mixedToRealizationPlan`, whose body is not exposed. -/
theorem ExtensiveTree.mixedToRealizationPlan_def [DecidableEq ι]
    (T : ExtensiveTree ι H Act) (i : ι) [Fintype (H i)] [DecidableEq (H i)]
    [∀ j h, Fintype (Act j h)] (μ : PureStrategy H Act i → ℝ) (σ : SeqVar T i) :
    T.mixedToRealizationPlan i μ σ = realizationProbMixed μ σ.1 := by
  rw [ExtensiveTree.mixedToRealizationPlan]

/-- Realization plan induced by a behavior strategy `β` of player `i`. -/
def ExtensiveTree.behaviorToRealizationPlan [DecidableEq ι]
    (T : ExtensiveTree ι H Act) (i : ι) (β : ∀ h : H i, Act i h → ℝ) (σ : SeqVar T i) : ℝ :=
  realizationProbBehavior β σ.1

@[simp]
theorem ExtensiveTree.behaviorToRealizationPlan_apply [DecidableEq ι]
    (T : ExtensiveTree ι H Act) (i : ι) (β : ∀ h : H i, Act i h → ℝ) (σ : SeqVar T i) :
    T.behaviorToRealizationPlan i β σ = realizationProbBehavior β σ.1 := by
  simp [ExtensiveTree.behaviorToRealizationPlan]

open Classical in
/-- Realization plan induced by a pure strategy `s` of player `i`. -/
noncomputable def ExtensiveTree.pureToRealizationPlan [DecidableEq ι]
    (T : ExtensiveTree ι H Act) (i : ι) (s : PureStrategy H Act i) (σ : SeqVar T i) : ℝ :=
  if MatchesSeq s σ.1 then 1 else 0

open Classical in
/-- Unfolding equation for `ExtensiveTree.pureToRealizationPlan`, whose body is not exposed. -/
theorem ExtensiveTree.pureToRealizationPlan_def [DecidableEq ι]
    (T : ExtensiveTree ι H Act) (i : ι) (s : PureStrategy H Act i) (σ : SeqVar T i) :
    T.pureToRealizationPlan i s σ = if MatchesSeq s σ.1 then 1 else 0 := by
  rw [ExtensiveTree.pureToRealizationPlan]

theorem pureToRealizationPlan_eq_mixedToRealizationPlan [DecidableEq ι]
    (T : ExtensiveTree ι H Act) (i : ι) [Fintype (H i)] [DecidableEq (H i)]
    [∀ j h, Fintype (Act j h)] [∀ h, DecidableEq (Act i h)] (s : PureStrategy H Act i) :
    T.pureToRealizationPlan i s = T.mixedToRealizationPlan i (Pi.single s (1 : ℝ)) := by
  ext σ
  simp only [ExtensiveTree.pureToRealizationPlan, ExtensiveTree.mixedToRealizationPlan]
  exact (realizationProbMixed_single_eq s σ.1).symm

theorem pureToRealizationPlan_eq_behaviorToRealizationPlan [DecidableEq ι]
    (T : ExtensiveTree ι H Act) (i : ι) [∀ h, DecidableEq (Act i h)]
    (s : PureStrategy H Act i) :
    T.pureToRealizationPlan i s = T.behaviorToRealizationPlan i (pureToBehavior s) := by
  ext σ
  simp only [ExtensiveTree.pureToRealizationPlan, ExtensiveTree.behaviorToRealizationPlan]
  exact (realizationProbBehavior_pureToBehavior_eq s σ.1).symm

/-- Flow-conservation identity for `realizationProbMixed` at any prefix `σ₀` and information set
`h`, without requiring perfect recall or even nonnegativity of `μ`. -/
theorem sum_realizationProbMixed_append_singleton {i : ι} [Fintype (H i)] [DecidableEq (H i)]
    [∀ h, Fintype (Act i h)] (μ : PureStrategy H Act i → ℝ) (σ₀ : Seq H Act i) (h : H i) :
    ∑ a : Act i h, realizationProbMixed μ (σ₀ ++ [⟨h, a⟩]) = realizationProbMixed μ σ₀ := by
  classical
  simp only [realizationProbMixed_def]
  rw [sum_comm]
  refine sum_congr rfl fun s _ => ?_
  have hiff : ∀ a : Act i h,
      MatchesSeq s (σ₀ ++ [⟨h, a⟩]) ↔ MatchesSeq s σ₀ ∧ s h = a := by
    intro a
    simp [matchesSeq_append, matchesSeq_cons]
  by_cases hs : MatchesSeq s σ₀
  · simp only [hs, ↓reduceIte]
    have hif : ∀ a : Act i h,
        (if MatchesSeq s (σ₀ ++ [⟨h, a⟩]) then μ s else 0) = if a = s h then μ s else 0 := by
      intro a
      by_cases h1 : MatchesSeq s (σ₀ ++ [⟨h, a⟩]) <;> by_cases h2 : a = s h
      · simp only [h1, ↓reduceIte]
        simp only [h2, ↓reduceIte]
      · exact absurd ((hiff a).1 h1).2.symm h2
      · exact absurd ((hiff a).2 ⟨hs, h2.symm⟩) h1
      · simp only [h1, ↓reduceIte]
        simp only [h2, ↓reduceIte]
    simp_rw [hif, sum_ite_eq']
    simp
  · simp only [hs, ↓reduceIte]
    refine sum_eq_zero fun a _ => ?_
    have hna : ¬ MatchesSeq s (σ₀ ++ [⟨h, a⟩]) := fun hma => hs ((hiff a).1 hma).1
    simp [hna]

/-- **Proposition 3.10(a)** ([vonStengel2007], Section 3.10): every mixed strategy of player `i`
induces a valid realization plan. -/
theorem isRealizationPlan_mixedToRealizationPlan [DecidableEq ι] [∀ j h, Fintype (Act j h)]
    [∀ j h, Nonempty (Act j h)] {T : ExtensiveTree ι H Act} {i : ι} [Fintype (H i)]
    [DecidableEq (H i)] (hpr : T.PerfectRecall i) {μ : PureStrategy H Act i → ℝ}
    (hμ : IsMixedStrategy μ) :
    T.IsRealizationPlan i (T.mixedToRealizationPlan i μ) := by
  rw [isRealizationPlan_iff hpr]
  refine ⟨fun σ => realizationProbMixed_nonneg hμ σ.1, ?_, ?_⟩
  · simpa [ExtensiveTree.mixedToRealizationPlan, SeqVar.nil] using realizationProbMixed_nil hμ
  · intro h hh
    exact sum_realizationProbMixed_append_singleton μ (T.infoSeq i h) h

/-- **Proposition 3.10(a)** ([vonStengel2007], Section 3.10): every behavior strategy of player `i`
induces a valid realization plan. -/
theorem isRealizationPlan_behaviorToRealizationPlan [DecidableEq ι]
    [∀ j h, Fintype (Act j h)] [∀ j h, Nonempty (Act j h)]
    {T : ExtensiveTree ι H Act} {i : ι} (hpr : T.PerfectRecall i)
    {β : ∀ h : H i, Act i h → ℝ} (hβ : IsBehaviorStrategy β) :
    T.IsRealizationPlan i (T.behaviorToRealizationPlan i β) := by
  rw [isRealizationPlan_iff hpr]
  refine ⟨fun σ => realizationProbBehavior_nonneg hβ σ.1, ?_, ?_⟩
  · simp [ExtensiveTree.behaviorToRealizationPlan, SeqVar.nil]
  · intro h hh
    simp only [ExtensiveTree.behaviorToRealizationPlan, SeqVar.infoSeqExt, SeqVar.infoSeq,
      realizationProbBehavior_append, realizationProbBehavior_cons, realizationProbBehavior_nil,
      mul_one, ← mul_sum]
    rw [(hβ h).sum_eq_one, mul_one]

/-- **Proposition 3.10(a)** ([vonStengel2007], Section 3.10): every pure strategy of player `i`
induces a valid `{0, 1}` realization plan. -/
theorem isRealizationPlan_pureToRealizationPlan [DecidableEq ι] [∀ j h, Fintype (Act j h)]
    [∀ j h, Nonempty (Act j h)] {T : ExtensiveTree ι H Act} {i : ι} [Finite (H i)]
    (hpr : T.PerfectRecall i) (s : PureStrategy H Act i) :
    T.IsRealizationPlan i (T.pureToRealizationPlan i s) := by
  classical
  let _ := Fintype.ofFinite (H i)
  rw [pureToRealizationPlan_eq_mixedToRealizationPlan]
  exact isRealizationPlan_mixedToRealizationPlan hpr (isMixedStrategy_single s)

open Classical in
/-- Behavior strategy reconstructed from a realization plan `x` ([vonStengel2007], §3.10):
`β(a | h) = x(σ_h a) / x(σ_h)` when `x(σ_h) > 0`, and an arbitrary deterministic distribution at
irrelevant (`x(σ_h) = 0`) or non-occurring information sets. -/
noncomputable def ExtensiveTree.realizationPlanToBehavior [DecidableEq ι]
    [∀ j h, Nonempty (Act j h)]
    (T : ExtensiveTree ι H Act) (i : ι) (hpr : T.PerfectRecall i)
    (x : SeqVar T i → ℝ) (h : H i) (a : Act i h) : ℝ :=
  if hh : T.OccursInfoSet i h then
    if 0 < x (SeqVar.infoSeq hpr hh) then
      x (SeqVar.infoSeqExt hpr hh a) / x (SeqVar.infoSeq hpr hh)
    else
      Pi.single (M := fun _ => ℝ) (Classical.arbitrary (Act i h)) (1 : ℝ) a
  else
    Pi.single (M := fun _ => ℝ) (Classical.arbitrary (Act i h)) (1 : ℝ) a

/-- Formula for `realizationPlanToBehavior` at any occurring information set reached with positive
probability `x (infoSeq h) > 0`. -/
theorem ExtensiveTree.realizationPlanToBehavior_eq_div [DecidableEq ι]
    [∀ j h, Nonempty (Act j h)]
    {T : ExtensiveTree ι H Act} {i : ι} (hpr : T.PerfectRecall i)
    {x : SeqVar T i → ℝ} {h : H i} (hh : T.OccursInfoSet i h)
    (hpos : 0 < x (SeqVar.infoSeq hpr hh)) (a : Act i h) :
    T.realizationPlanToBehavior i hpr x h a =
      x (SeqVar.infoSeqExt hpr hh a) / x (SeqVar.infoSeq hpr hh) := by
  simp only [ExtensiveTree.realizationPlanToBehavior, hh, hpos, ↓reduceDIte, ↓reduceIte]

/-- **Proposition 3.10(b)** ([vonStengel2007], Section 3.10): `realizationPlanToBehavior`
produces a valid behavior strategy for every realization plan `x`. -/
theorem isBehaviorStrategy_realizationPlanToBehavior [DecidableEq ι]
    [∀ j h, Fintype (Act j h)] [∀ j h, Nonempty (Act j h)]
    {T : ExtensiveTree ι H Act} {i : ι} (hpr : T.PerfectRecall i)
    {x : SeqVar T i → ℝ} (hx : T.IsRealizationPlan i x) :
    IsBehaviorStrategy (T.realizationPlanToBehavior i hpr x) := by
  classical
  have hiff := (isRealizationPlan_iff hpr x).1 hx
  intro h
  by_cases hh : T.OccursInfoSet i h
  · by_cases hpos : 0 < x (SeqVar.infoSeq hpr hh)
    · rw [isMixedStrategy_iff]
      refine ⟨fun a => ?_, ?_⟩
      · simp only [ExtensiveTree.realizationPlanToBehavior, hh, hpos, ↓reduceDIte, ↓reduceIte]
        exact div_nonneg (hiff.1 _) hpos.le
      · simp only [ExtensiveTree.realizationPlanToBehavior, hh, hpos, ↓reduceDIte, ↓reduceIte]
        rw [← sum_div, hiff.2.2 h hh, div_self hpos.ne']
    · have hfn : T.realizationPlanToBehavior i hpr x h =
          Pi.single (M := fun _ => ℝ) (Classical.arbitrary (Act i h)) (1 : ℝ) := by
        ext a
        simp only [ExtensiveTree.realizationPlanToBehavior, hh, hpos, ↓reduceDIte, ↓reduceIte]
      rw [hfn]
      exact isMixedStrategy_single (Classical.arbitrary (Act i h))
  · have hfn : T.realizationPlanToBehavior i hpr x h =
        Pi.single (M := fun _ => ℝ) (Classical.arbitrary (Act i h)) (1 : ℝ) := by
      ext a
      simp only [ExtensiveTree.realizationPlanToBehavior, hh, ↓reduceDIte]
    rw [hfn]
    exact isMixedStrategy_single (Classical.arbitrary (Act i h))

/-- **Proposition 3.10(b)** ([vonStengel2007], Section 3.10): under perfect recall, the realization
plan of `T.realizationPlanToBehavior i hpr x` is `x` itself. -/
theorem behaviorToRealizationPlan_realizationPlanToBehavior [DecidableEq ι]
    [∀ j h, Fintype (Act j h)] [∀ j h, Nonempty (Act j h)]
    {T : ExtensiveTree ι H Act} {i : ι} (hpr : T.PerfectRecall i)
    {x : SeqVar T i → ℝ} (hx : T.IsRealizationPlan i x) :
    T.behaviorToRealizationPlan i (T.realizationPlanToBehavior i hpr x) = x := by
  classical
  have hiff := (isRealizationPlan_iff hpr x).1 hx
  have hlen : ∀ (n : ℕ) (σ : SeqVar T i), σ.1.length = n →
      T.behaviorToRealizationPlan i (T.realizationPlanToBehavior i hpr x) σ = x σ := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro σ hσ
      by_cases hnil : σ.1 = []
      · have hσ_nil : σ = SeqVar.nil T i := Subtype.ext hnil
        rw [hσ_nil]
        simp only [ExtensiveTree.behaviorToRealizationPlan, SeqVar.nil,
          realizationProbBehavior_nil]
        exact (hiff.2.1).symm
      · obtain ⟨⟨h, hh⟩, a, rfl⟩ := exists_infoSeqExt_of_seqVar_ne_nil hpr σ hnil
        have ih_pre :
            T.behaviorToRealizationPlan i (T.realizationPlanToBehavior i hpr x)
              (SeqVar.infoSeq hpr hh) = x (SeqVar.infoSeq hpr hh) := by
          apply ih (SeqVar.infoSeq hpr hh).1.length
          · rw [← hσ]
            simp [SeqVar.infoSeq, SeqVar.infoSeqExt]
          · rfl
        have hstep :
            T.behaviorToRealizationPlan i (T.realizationPlanToBehavior i hpr x)
                (SeqVar.infoSeqExt hpr hh a) =
              x (SeqVar.infoSeq hpr hh) * T.realizationPlanToBehavior i hpr x h a := by
          simp only [ExtensiveTree.behaviorToRealizationPlan, SeqVar.infoSeqExt,
            realizationProbBehavior_append, realizationProbBehavior_cons,
            realizationProbBehavior_nil, mul_one]
          simpa [ExtensiveTree.behaviorToRealizationPlan, SeqVar.infoSeq] using
            congrArg (· * T.realizationPlanToBehavior i hpr x h a) ih_pre
        rw [hstep]
        dsimp only [ExtensiveTree.realizationPlanToBehavior]
        by_cases hpos : 0 < x (SeqVar.infoSeq hpr hh)
        · simp only [hh, hpos, ↓reduceDIte, ↓reduceIte]
          field_simp [hpos.ne']
        · have hx0 : x (SeqVar.infoSeq hpr hh) = 0 :=
            le_antisymm (not_lt.1 hpos) (hiff.1 _)
          have hsum0 : ∑ c : Act i h, x (SeqVar.infoSeqExt hpr hh c) = 0 := by
            rw [hiff.2.2 h hh, hx0]
          have ha0 : x (SeqVar.infoSeqExt hpr hh a) = 0 :=
            (sum_eq_zero_iff_of_nonneg fun c _ => hiff.1 _).1 hsum0 a (mem_univ a)
          rw [hx0, zero_mul, ha0]
  ext σ
  exact hlen σ.1.length σ rfl

/-- **Proposition 3.10 (uniqueness at relevant information sets)** ([vonStengel2007], §3.10):
any behavior strategy realizing `x` agrees with `T.realizationPlanToBehavior i hpr x` at every
information set `h` reached with positive probability `x (infoSeq h) > 0`. -/
theorem realizationPlanToBehavior_unique [DecidableEq ι]
    [∀ j h, Nonempty (Act j h)] {T : ExtensiveTree ι H Act} {i : ι}
    (hpr : T.PerfectRecall i) {x : SeqVar T i → ℝ} {β : ∀ h : H i, Act i h → ℝ}
    (hreal : T.behaviorToRealizationPlan i β = x) {h : H i} (hh : T.OccursInfoSet i h)
    (hpos : 0 < x (SeqVar.infoSeq hpr hh)) :
    β h = T.realizationPlanToBehavior i hpr x h := by
  classical
  ext a
  have h1 := congrFun hreal (SeqVar.infoSeq hpr hh)
  have h2 := congrFun hreal (SeqVar.infoSeqExt hpr hh a)
  simp only [ExtensiveTree.behaviorToRealizationPlan, SeqVar.infoSeq, SeqVar.infoSeqExt,
    realizationProbBehavior_append, realizationProbBehavior_cons, realizationProbBehavior_nil,
    mul_one] at h1 h2
  rw [h1] at h2
  dsimp only [ExtensiveTree.realizationPlanToBehavior]
  simp only [hh, hpos, ↓reduceDIte, ↓reduceIte]
  rw [eq_div_iff hpos.ne', mul_comm]
  exact h2

end RealizationPlans

section KuhnAndRealizationEquiv

variable {ι : Type u} {H : ι → Type v} {Act : ∀ i, H i → Type}

/-- When `((z.seq j).map Sigma.fst).Nodup`, there exists a pure strategy `s_j` matching `z.seq j`.
-/
private theorem exists_pureStrategy_matchesSeq {T : ExtensiveTree ι H Act} [DecidableEq ι]
    [∀ j h, Nonempty (Act j h)] {j : ι} {z : Terminal T}
    (hnodup : ((z.seq j).map Sigma.fst).Nodup) :
    ∃ s_j : PureStrategy H Act j, MatchesSeq s_j (z.seq j) := by
  classical
  let s_j : PureStrategy H Act j := fun h =>
    if hex : ∃ a : Act j h, (⟨h, a⟩ : Choice H Act j) ∈ z.seq j then hex.choose
    else Classical.arbitrary (Act j h)
  refine ⟨s_j, fun p hp => ?_⟩
  rcases p with ⟨h, a⟩
  have hex : ∃ b : Act j h, (⟨h, b⟩ : Choice H Act j) ∈ z.seq j := ⟨a, hp⟩
  simp only [s_j, hex, ↓reduceDIte]
  have hnk : (z.seq j).NodupKeys := by
    simpa [List.NodupKeys, List.keys] using hnodup
  exact hnk.eq_of_mk_mem hex.choose_spec hp

/-- **Corollary 3.12 (Kuhn's theorem)** ([vonStengel2007], Section 3.10): under perfect recall for
player `i`, every mixed strategy `μ` of player `i` is realization-equivalent to the explicit
behavior strategy `T.realizationPlanToBehavior i hpr (T.mixedToRealizationPlan i μ)`. -/
theorem kuhn_theorem [Fintype ι] [DecidableEq ι] [∀ j, Fintype (H j)] [∀ j, DecidableEq (H j)]
    [∀ j h, Fintype (Act j h)] [∀ j h, Nonempty (Act j h)]
    {T : ExtensiveTree ι H Act} {i : ι} (hpr : T.PerfectRecall i)
    {μ : PureStrategy H Act i → ℝ} (hμ : IsMixedStrategy μ) :
    let β := T.realizationPlanToBehavior i hpr (T.mixedToRealizationPlan i μ)
    IsBehaviorStrategy β ∧
      (∀ z : Terminal T, realizationProbBehavior β (z.seq i) = realizationProbMixed μ (z.seq i)) ∧
      T.RealizationEquivMixedBehavior i μ β := by
  let x := T.mixedToRealizationPlan i μ
  let β := T.realizationPlanToBehavior i hpr x
  have hx : T.IsRealizationPlan i x := isRealizationPlan_mixedToRealizationPlan hpr hμ
  have hβ : IsBehaviorStrategy β := isBehaviorStrategy_realizationPlanToBehavior hpr hx
  have hreal : T.behaviorToRealizationPlan i β = x :=
    behaviorToRealizationPlan_realizationPlanToBehavior hpr hx
  have hterm : ∀ z : Terminal T,
      realizationProbBehavior β (z.seq i) = realizationProbMixed μ (z.seq i) := by
    intro z
    have hz := congrFun hreal ⟨z.seq i, z, List.prefix_rfl⟩
    simpa [ExtensiveTree.behaviorToRealizationPlan, ExtensiveTree.mixedToRealizationPlan, x]
      using hz
  refine ⟨hβ, hterm, ExtensiveTree.RealizationEquivFactor.of_forall_terminal_eq fun z => ?_⟩
  exact (hterm z).symm

/-- Existential form of **Kuhn's theorem** ([vonStengel2007], Corollary 3.12). -/
theorem kuhn_theorem_exists [Fintype ι] [DecidableEq ι] [∀ j, Fintype (H j)]
    [∀ j, DecidableEq (H j)] [∀ j h, Fintype (Act j h)] [∀ j h, Nonempty (Act j h)]
    {T : ExtensiveTree ι H Act} {i : ι} (hpr : T.PerfectRecall i)
    {μ : PureStrategy H Act i → ℝ} (hμ : IsMixedStrategy μ) :
    ∃ β : ∀ h : H i, Act i h → ℝ,
      IsBehaviorStrategy β ∧ T.RealizationEquivMixedBehavior i μ β :=
  let h := kuhn_theorem hpr hμ
  ⟨_, h.1, h.2.2⟩

/-- First half of **Proposition 3.11** ([vonStengel2007], Section 3.10): mixed strategies with the
same realization plan are realization-equivalent. -/
theorem realizationEquivMixed_of_mixedToRealizationPlan_eq [Fintype ι] [DecidableEq ι]
    [∀ j, Fintype (H j)] [∀ j, DecidableEq (H j)] [∀ j h, Fintype (Act j h)]
    {T : ExtensiveTree ι H Act} {i : ι} {μ₁ μ₂ : PureStrategy H Act i → ℝ}
    (heq : T.mixedToRealizationPlan i μ₁ = T.mixedToRealizationPlan i μ₂) :
    T.RealizationEquivMixed i μ₁ μ₂ :=
  ExtensiveTree.RealizationEquivFactor.of_forall_terminal_eq fun z =>
    congrFun heq ⟨z.seq i, z, List.prefix_rfl⟩

/-- Second half of **Proposition 3.11** ([vonStengel2007], Section 3.10): under positive chance
probabilities and no repeated opponent information sets, realization-equivalent mixed strategies
must induce identical realization plans. -/
theorem mixedToRealizationPlan_eq_of_realizationEquivMixed [Fintype ι] [DecidableEq ι]
    [∀ j, Fintype (H j)] [∀ j, DecidableEq (H j)] [∀ j h, Fintype (Act j h)]
    [∀ j h, Nonempty (Act j h)] {T : ExtensiveTree ι H Act} {i : ι}
    (hpos : T.HasPositiveChance) (hnr : ∀ j ≠ i, T.NoRepeatedInfoSet j)
    {μ₁ μ₂ : PureStrategy H Act i → ℝ} (heq : T.RealizationEquivMixed i μ₁ μ₂) :
    T.mixedToRealizationPlan i μ₁ = T.mixedToRealizationPlan i μ₂ := by
  classical
  have hterm : ∀ z : Terminal T,
      realizationProbMixed μ₁ (z.seq i) = realizationProbMixed μ₂ (z.seq i) := by
    intro z
    have hs_other : ∀ j : ι, ∃ s_j : PureStrategy H Act j,
        j ≠ i → MatchesSeq s_j (z.seq j) := by
      intro j
      by_cases hj : j = i
      · exact ⟨fun _ => Classical.arbitrary _, fun hne => absurd hj hne⟩
      · obtain ⟨s_j, hs_j⟩ := exists_pureStrategy_matchesSeq (hnr j hj z)
        exact ⟨s_j, fun _ => hs_j⟩
    choose s hs using hs_other
    have hfactor := heq s z
    rw [terminalProbWithFactor_def, terminalProbWithFactor_def] at hfactor
    have hprod1 : (∏ j ∈ univ.erase i, if MatchesSeq (s j) (z.seq j) then (1 : ℝ) else 0) = 1 :=
      prod_eq_one fun j hj => by simp [hs j (ne_of_mem_erase hj)]
    rw [hprod1, mul_one, mul_one] at hfactor
    exact mul_left_cancel₀ (hpos.chanceWeight_pos z).ne' hfactor
  let maxLen : ℕ := (occursSeqFinset T i).sup List.length
  have hlen : ∀ (d : ℕ) (σ : SeqVar T i), maxLen - σ.1.length = d →
      realizationProbMixed μ₁ σ.1 = realizationProbMixed μ₂ σ.1 := by
    intro d
    induction d using Nat.strong_induction_on with
    | ind d ih =>
      intro σ hd
      by_cases hfull : ∃ w : Terminal T, w.seq i = σ.1
      · obtain ⟨w, hw⟩ := hfull
        rw [← hw]
        exact hterm w
      · obtain ⟨z, post, hz⟩ := σ.2
        have hpost_ne : post ≠ [] := by
          intro hnil
          rw [hnil, List.append_nil] at hz
          exact hfull ⟨z, hz.symm⟩
        cases post with
        | nil => exact absurd rfl hpost_ne
        | cons p post' =>
          rcases p with ⟨h, a⟩
          have hseq : z.seq i = σ.1 ++ ⟨h, a⟩ :: post' := hz.symm
          obtain ⟨v, hv, hpre⟩ := z.exists_node_of_seq_append σ.1 post' h a hseq
          have hstep : ∀ c : Act i h,
              realizationProbMixed μ₁ (σ.1 ++ [⟨h, c⟩]) =
                realizationProbMixed μ₂ (σ.1 ++ [⟨h, c⟩]) := by
            intro c
            let σc : SeqVar T i := ⟨σ.1 ++ [⟨h, c⟩], by
              refine ⟨v.extendDecisionOf hv c, ?_⟩
              rw [← hpre]
              exact v.playerSeq_append_singleton_prefix_extendDecisionOf hv c⟩
            have hmem : σc.1 ∈ occursSeqFinset T i := mem_occursSeqFinset.2 σc.2
            have hle_max : σc.1.length ≤ maxLen := Finset.le_sup (f := List.length) hmem
            have hlt_len : σ.1.length < σc.1.length := by simp [σc]
            have hlt_d : maxLen - σc.1.length < d := by
              rw [← hd]
              omega
            exact ih (maxLen - σc.1.length) hlt_d σc rfl
          calc realizationProbMixed μ₁ σ.1
              = ∑ c : Act i h, realizationProbMixed μ₁ (σ.1 ++ [⟨h, c⟩]) :=
                  (sum_realizationProbMixed_append_singleton μ₁ σ.1 h).symm
            _ = ∑ c : Act i h, realizationProbMixed μ₂ (σ.1 ++ [⟨h, c⟩]) :=
                  sum_congr rfl fun c _ => hstep c
            _ = realizationProbMixed μ₂ σ.1 :=
                  sum_realizationProbMixed_append_singleton μ₂ σ.1 h
  ext σ
  exact hlen (maxLen - σ.1.length) σ rfl

/-- **Proposition 3.11** ([vonStengel2007], Section 3.10): under positive chance probabilities and
no repeated opponent information sets, two mixed strategies of player `i` are realization-equivalent
iff they induce the same realization plan. -/
theorem realizationEquivMixed_iff_mixedToRealizationPlan_eq [Fintype ι] [DecidableEq ι]
    [∀ j, Fintype (H j)] [∀ j, DecidableEq (H j)] [∀ j h, Fintype (Act j h)]
    [∀ j h, Nonempty (Act j h)] {T : ExtensiveTree ι H Act} {i : ι}
    (hpos : T.HasPositiveChance) (hnr : ∀ j ≠ i, T.NoRepeatedInfoSet j)
    (μ₁ μ₂ : PureStrategy H Act i → ℝ) :
    T.RealizationEquivMixed i μ₁ μ₂ ↔
      T.mixedToRealizationPlan i μ₁ = T.mixedToRealizationPlan i μ₂ :=
  ⟨mixedToRealizationPlan_eq_of_realizationEquivMixed hpos hnr,
    realizationEquivMixed_of_mixedToRealizationPlan_eq⟩

end KuhnAndRealizationEquiv

section ReducedFormAndPolytope

variable {ι : Type u} {H : ι → Type v} {Act : ∀ i, H i → Type}

/-- **Reduced strategic form equivalence** ([vonStengel2007], Section 3.9): two pure strategies
of player `i` are equivalent in the reduced strategic form iff they induce the same `{0, 1}`
realization plan (equivalently, make the same choices at all reachable information sets). -/
@[expose] def ExtensiveTree.ReducedEquiv [DecidableEq ι]
    (T : ExtensiveTree ι H Act) (i : ι) (s₁ s₂ : PureStrategy H Act i) : Prop :=
  T.pureToRealizationPlan i s₁ = T.pureToRealizationPlan i s₂

theorem reducedEquiv_iff_agree_on_reachable [DecidableEq ι]
    [∀ j h, Nonempty (Act j h)] {T : ExtensiveTree ι H Act} {i : ι}
    (hpr : T.PerfectRecall i) (s₁ s₂ : PureStrategy H Act i) :
    T.ReducedEquiv i s₁ s₂ ↔
      ∀ h (_hh : T.OccursInfoSet i h), MatchesSeq s₁ (T.infoSeq i h) → s₁ h = s₂ h := by
  classical
  have hpt : ∀ s₁ s₂ : PureStrategy H Act i,
      T.pureToRealizationPlan i s₁ = T.pureToRealizationPlan i s₂ ↔
        ∀ σ : SeqVar T i, MatchesSeq s₁ σ.1 ↔ MatchesSeq s₂ σ.1 := by
    intro s₁ s₂
    constructor
    · intro heq σ
      have hσ := congrFun heq σ
      simp only [ExtensiveTree.pureToRealizationPlan] at hσ
      constructor <;> intro hm
      · by_contra hm2
        simp [hm, hm2] at hσ
      · by_contra hm1
        simp [hm, hm1] at hσ
    · intro hall
      ext σ
      simp only [ExtensiveTree.pureToRealizationPlan]
      by_cases hm : MatchesSeq s₁ σ.1
      · simp [hm, (hall σ).1 hm]
      · have hm2 : ¬ MatchesSeq s₂ σ.1 := fun h2 => hm ((hall σ).2 h2)
        simp [hm, hm2]
  rw [ExtensiveTree.ReducedEquiv, hpt]
  constructor
  · intro hall h hh hm1
    have hσ := hall (SeqVar.infoSeqExt hpr hh (s₁ h))
    have hm1' : MatchesSeq s₁ (SeqVar.infoSeqExt hpr hh (s₁ h)).1 :=
      (matchesSeq_append s₁ (T.infoSeq i h) [⟨h, s₁ h⟩]).2 ⟨hm1, by simp⟩
    have hm2' := (matchesSeq_append s₂ (T.infoSeq i h) [⟨h, s₁ h⟩]).1 (hσ.1 hm1')
    have hs2 : s₂ h = s₁ h := (matchesSeq_cons s₂ ⟨h, s₁ h⟩ []).1 hm2'.2 |>.1
    exact hs2.symm
  · intro hagree σ
    have hlen : ∀ n (τ : SeqVar T i), τ.1.length = n →
        (MatchesSeq s₁ τ.1 ↔ MatchesSeq s₂ τ.1) := by
      intro n
      induction n using Nat.strong_induction_on with
      | ind n ih =>
        intro τ hτ
        by_cases hnil : τ.1 = []
        · simp [hnil]
        · obtain ⟨⟨h, hh⟩, a, rfl⟩ := exists_infoSeqExt_of_seqVar_ne_nil hpr τ hnil
          have ih_pre : MatchesSeq s₁ (SeqVar.infoSeq hpr hh).1 ↔
              MatchesSeq s₂ (SeqVar.infoSeq hpr hh).1 := by
            apply ih (SeqVar.infoSeq hpr hh).1.length
            · rw [← hτ]
              simp [SeqVar.infoSeq, SeqVar.infoSeqExt]
            · rfl
          simp only [SeqVar.infoSeqExt, matchesSeq_append, matchesSeq_cons, matchesSeq_nil,
            and_true]
          constructor
          · rintro ⟨hm1, ha⟩
            have hm2 := ih_pre.1 hm1
            refine ⟨hm2, ?_⟩
            rw [← hagree h hh hm1]
            exact ha
          · rintro ⟨hm2, ha⟩
            have hm1 := ih_pre.2 hm2
            refine ⟨hm1, ?_⟩
            rw [hagree h hh hm1]
            exact ha
    exact hlen σ.1.length σ rfl

/-- Pure strategies that agree in the reduced strategic form yield identical payoffs against all
opponent pure strategy profiles. -/
theorem evalPure_eq_of_reducedEquiv [Finite ι] [DecidableEq ι] [∀ j h, Finite (Act j h)]
    {T : ExtensiveTree ι H Act} {i : ι} {s₁ s₂ : PureStrategy H Act i}
    (heq : T.ReducedEquiv i s₁ s₂) (s : ∀ j, PureStrategy H Act j) (k : ι) :
    T.evalPure (Function.update s i s₁) k = T.evalPure (Function.update s i s₂) k := by
  classical
  let _ := Fintype.ofFinite ι
  let _ := fun j h => Fintype.ofFinite (Act j h)
  rw [ExtensiveTree.evalPure_eq_sum_terminal, ExtensiveTree.evalPure_eq_sum_terminal]
  refine sum_congr rfl fun z _ => ?_
  rw [terminalProbPure_eq, terminalProbPure_eq]
  have h1 : ∀ s' : PureStrategy H Act i,
      (∏ j, if MatchesSeq (Function.update s i s' j) (z.seq j) then (1 : ℝ) else 0) =
        (if MatchesSeq s' (z.seq i) then 1 else 0) *
          ∏ j ∈ univ.erase i, if MatchesSeq (s j) (z.seq j) then 1 else 0 := by
    intro s'
    rw [← mul_prod_erase univ _ (mem_univ i), Function.update_self]
    congr 1
    refine prod_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (ne_of_mem_erase hj)]
  rw [h1 s₁, h1 s₂]
  have hz := congrFun heq ⟨z.seq i, z, List.prefix_rfl⟩
  simp only [ExtensiveTree.pureToRealizationPlan] at hz
  have hz' : (if MatchesSeq s₁ (z.seq i) then (1 : ℝ) else 0) =
      if MatchesSeq s₂ (z.seq i) then 1 else 0 := by
    convert hz
  rw [hz']

theorem mixedToRealizationPlan_eq_sum_pure [DecidableEq ι] (T : ExtensiveTree ι H Act) (i : ι)
    [Fintype (H i)] [DecidableEq (H i)] [∀ j h, Fintype (Act j h)]
    (μ : PureStrategy H Act i → ℝ) :
    T.mixedToRealizationPlan i μ =
      ∑ s : PureStrategy H Act i, μ s • T.pureToRealizationPlan i s := by
  classical
  ext σ
  simp only [ExtensiveTree.mixedToRealizationPlan, realizationProbMixed_def,
    ExtensiveTree.pureToRealizationPlan, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine sum_congr rfl fun s _ => ?_
  split_ifs <;> simp

theorem convex_isRealizationPlan [DecidableEq ι] [∀ j h, Fintype (Act j h)]
    (T : ExtensiveTree ι H Act) (i : ι) :
    Convex ℝ {x : SeqVar T i → ℝ | T.IsRealizationPlan i x} := by
  rintro x ⟨hx_nn, hx_eq⟩ y ⟨hy_nn, hy_eq⟩ a b ha hb hab
  refine ⟨fun σ => add_nonneg (mul_nonneg ha (hx_nn σ)) (mul_nonneg hb (hy_nn σ)), ?_⟩
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hx_eq, hy_eq, ← add_smul, hab,
    one_smul]

private theorem exists_mixed_of_isRealizationPlan [DecidableEq ι] [∀ j h, Fintype (Act j h)]
    [∀ j h, Nonempty (Act j h)] {T : ExtensiveTree ι H Act} {i : ι} [Fintype (H i)]
    [DecidableEq (H i)] (hpr : T.PerfectRecall i) {x : SeqVar T i → ℝ}
    (hx : T.IsRealizationPlan i x) :
    ∃ μ : PureStrategy H Act i → ℝ, IsMixedStrategy μ ∧ T.mixedToRealizationPlan i μ = x := by
  let β := T.realizationPlanToBehavior i hpr x
  have hβ : IsBehaviorStrategy β := isBehaviorStrategy_realizationPlanToBehavior hpr hx
  refine ⟨behaviorToMixed β, isMixedStrategy_behaviorToMixed hβ, ?_⟩
  ext σ
  have hnodup : (σ.1.map Sigma.fst).Nodup := by
    obtain ⟨z, τ, hz⟩ := σ.2
    have hzn : ((z.seq i).map Sigma.fst).Nodup := hpr.noRepeatedInfoSet z
    rw [← hz, List.map_append] at hzn
    exact List.Nodup.of_append_left hzn
  rw [ExtensiveTree.mixedToRealizationPlan, realizationProbMixed_behaviorToMixed hβ hnodup]
  exact congrFun (behaviorToRealizationPlan_realizationPlanToBehavior hpr hx) σ

/-- Under perfect recall, the set of realization plans is the convex hull of the pure realization
plans `pureToRealizationPlan T i s` ([vonStengel2007], Section 3.10). -/
theorem isRealizationPlan_iff_mem_convexHull [DecidableEq ι] [∀ j h, Fintype (Act j h)]
    [∀ j h, Nonempty (Act j h)] {T : ExtensiveTree ι H Act} {i : ι} [Finite (H i)]
    (hpr : T.PerfectRecall i) (x : SeqVar T i → ℝ) :
    T.IsRealizationPlan i x ↔ x ∈ convexHull ℝ (Set.range (T.pureToRealizationPlan i)) := by
  classical
  let _ := Fintype.ofFinite (H i)
  constructor
  · intro hx
    obtain ⟨μ, hμ, hplan⟩ := exists_mixed_of_isRealizationPlan hpr hx
    rw [← hplan, mixedToRealizationPlan_eq_sum_pure]
    exact (convex_convexHull ℝ _).sum_mem (fun s _ => hμ.nonneg s) hμ.sum_eq_one
      fun s _ => subset_convexHull ℝ _ ⟨s, rfl⟩
  · intro hx
    have hsub : convexHull ℝ (Set.range (T.pureToRealizationPlan i)) ⊆
        {y | T.IsRealizationPlan i y} := by
      refine convexHull_min ?_ (convex_isRealizationPlan T i)
      rintro _ ⟨s, rfl⟩
      exact isRealizationPlan_pureToRealizationPlan hpr s
    exact hsub hx

/-- **Extreme points of the realization-plan polytope** ([vonStengel2007], §§3.9–3.10): under
perfect recall, `x` is an extreme point of `{y | T.IsRealizationPlan i y}` iff `x` is a `{0, 1}`
pure realization plan `T.pureToRealizationPlan i s`. -/
theorem mem_extremePoints_isRealizationPlan_iff [DecidableEq ι] [∀ j h, Fintype (Act j h)]
    [∀ j h, Nonempty (Act j h)] {T : ExtensiveTree ι H Act} {i : ι} [Finite (H i)]
    (hpr : T.PerfectRecall i) (x : SeqVar T i → ℝ) :
    x ∈ ({y : SeqVar T i → ℝ | T.IsRealizationPlan i y}).extremePoints ℝ ↔
      x ∈ Set.range (T.pureToRealizationPlan i) := by
  classical
  let _ := Fintype.ofFinite (H i)
  constructor
  · rintro ⟨hx, hext⟩
    obtain ⟨μ, hμ, hplan⟩ := exists_mixed_of_isRealizationPlan hpr hx
    rw [mixedToRealizationPlan_eq_sum_pure] at hplan
    replace hplan : x = ∑ s : PureStrategy H Act i, μ s • T.pureToRealizationPlan i s := hplan.symm
    obtain ⟨s, hs_pos⟩ := hμ.exists_pos
    refine ⟨s, ?_⟩
    by_cases hs1 : μ s = 1
    · have hrest : ∀ t ∈ (univ : Finset (PureStrategy H Act i)).erase s, μ t = 0 := by
        have hsum0 : ∑ t ∈ univ.erase s, μ t = 0 := by
          have := hμ.sum_eq_one
          rw [← add_sum_erase univ μ (mem_univ s), hs1] at this
          linarith
        exact (sum_eq_zero_iff_of_nonneg fun t _ => hμ.nonneg t).1 hsum0
      rw [hplan, ← add_sum_erase univ _ (mem_univ s), hs1, one_smul]
      have h0 : ∑ t ∈ univ.erase s, μ t • T.pureToRealizationPlan i t = 0 :=
        sum_eq_zero fun t ht => by simp [hrest t ht]
      rw [h0, add_zero]
    · have hs_lt : μ s < 1 := lt_of_le_of_ne (by
        have := single_le_sum (fun t _ => hμ.nonneg t) (mem_univ s)
        simpa [hμ.sum_eq_one] using this) hs1
      have hrem : 0 < 1 - μ s := sub_pos.2 hs_lt
      let y : SeqVar T i → ℝ :=
        (1 - μ s)⁻¹ • ∑ t ∈ univ.erase s, μ t • T.pureToRealizationPlan i t
      have hy_sum : ∑ t ∈ univ.erase s, ((1 - μ s)⁻¹ * μ t) = 1 := by
        rw [← mul_sum]
        have := hμ.sum_eq_one
        rw [← add_sum_erase univ μ (mem_univ s)] at this
        have hsum_er : ∑ t ∈ univ.erase s, μ t = 1 - μ s := by linarith
        rw [hsum_er, inv_mul_cancel₀ hrem.ne']
      have hy : T.IsRealizationPlan i y := by
        have hy_eq : y = ∑ t ∈ univ.erase s, ((1 - μ s)⁻¹ * μ t) • T.pureToRealizationPlan i t := by
          simp only [y, smul_sum, smul_smul]
        rw [hy_eq]
        exact (convex_isRealizationPlan T i).sum_mem
          (fun t _ => mul_nonneg (inv_nonneg.2 hrem.le) (hμ.nonneg t)) hy_sum
          fun t _ => isRealizationPlan_pureToRealizationPlan hpr t
      have hs_feas : T.IsRealizationPlan i (T.pureToRealizationPlan i s) :=
        isRealizationPlan_pureToRealizationPlan hpr s
      have hseg : x ∈ openSegment ℝ (T.pureToRealizationPlan i s) y := by
        refine ⟨μ s, 1 - μ s, hs_pos, hrem, by ring, ?_⟩
        rw [hplan, ← add_sum_erase univ _ (mem_univ s)]
        congr 1
        simp only [y, smul_smul, mul_inv_cancel₀ hrem.ne', one_smul]
      exact hext hs_feas hy hseg
  · rintro ⟨s, rfl⟩
    refine ⟨isRealizationPlan_pureToRealizationPlan hpr s, ?_⟩
    rintro x₁ hx₁ x₂ hx₂ ⟨a, b, ha, hb, hab, hseg⟩
    have hiff1 := (isRealizationPlan_iff hpr x₁).1 hx₁
    have hiff2 := (isRealizationPlan_iff hpr x₂).1 hx₂
    have hmatch : ∀ τ : SeqVar T i, x₁ τ = T.pureToRealizationPlan i s τ := by
      have hlen : ∀ n (τ : SeqVar T i), τ.1.length = n →
          x₁ τ = T.pureToRealizationPlan i s τ := by
        intro n
        induction n using Nat.strong_induction_on with
        | ind n ih =>
          intro τ hτ
          by_cases hnil : τ.1 = []
          · have : τ = SeqVar.nil T i := Subtype.ext hnil
            rw [this, hiff1.2.1]
            simp [ExtensiveTree.pureToRealizationPlan, SeqVar.nil]
          · obtain ⟨⟨h, hh⟩, c, rfl⟩ := exists_infoSeqExt_of_seqVar_ne_nil hpr τ hnil
            have ih_pre : x₁ (SeqVar.infoSeq hpr hh) =
                T.pureToRealizationPlan i s (SeqVar.infoSeq hpr hh) := by
              apply ih (SeqVar.infoSeq hpr hh).1.length
              · rw [← hτ]
                simp [SeqVar.infoSeq, SeqVar.infoSeqExt]
              · rfl
            have hsum_pre : a * x₁ (SeqVar.infoSeqExt hpr hh c) +
                b * x₂ (SeqVar.infoSeqExt hpr hh c) =
                  T.pureToRealizationPlan i s (SeqVar.infoSeqExt hpr hh c) := by
              have := congrFun hseg (SeqVar.infoSeqExt hpr hh c)
              simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this
            by_cases hval : T.pureToRealizationPlan i s (SeqVar.infoSeqExt hpr hh c) = 0
            · rw [hval] at hsum_pre ⊢
              have ha0 : a * x₁ (SeqVar.infoSeqExt hpr hh c) = 0 := by
                have h1 := mul_nonneg ha.le (hiff1.1 (SeqVar.infoSeqExt hpr hh c))
                have h2 := mul_nonneg hb.le (hiff2.1 (SeqVar.infoSeqExt hpr hh c))
                linarith
              exact (mul_eq_zero.1 ha0).resolve_left ha.ne'
            · have hm_ext : MatchesSeq s (SeqVar.infoSeqExt hpr hh c).1 := by
                by_contra hm
                exact hval (by simp [ExtensiveTree.pureToRealizationPlan, hm])
              have hm_split := (matchesSeq_append s (T.infoSeq i h) [⟨h, c⟩]).1 hm_ext
              have hs_c : s h = c := (matchesSeq_cons s ⟨h, c⟩ []).1 hm_split.2 |>.1
              have hpre_one : T.pureToRealizationPlan i s (SeqVar.infoSeq hpr hh) = 1 := by
                simp [ExtensiveTree.pureToRealizationPlan, SeqVar.infoSeq, hm_split.1]
              have hothers : ∀ c' : Act i h, c' ≠ c →
                  x₁ (SeqVar.infoSeqExt hpr hh c') = 0 := by
                intro c' hc'
                have hsum_c' := congrFun hseg (SeqVar.infoSeqExt hpr hh c')
                have hm_c' : ¬ MatchesSeq s (SeqVar.infoSeqExt hpr hh c').1 := by
                  intro hm'
                  have hsc' :=
                    (matchesSeq_cons s ⟨h, c'⟩ []).1
                      ((matchesSeq_append s (T.infoSeq i h) [⟨h, c'⟩]).1 hm').2 |>.1
                  exact hc' (hsc'.symm.trans hs_c)
                have h0_c' : T.pureToRealizationPlan i s (SeqVar.infoSeqExt hpr hh c') = 0 := by
                  simp [ExtensiveTree.pureToRealizationPlan, hm_c']
                rw [h0_c'] at hsum_c'
                have h1 := mul_nonneg ha.le (hiff1.1 (SeqVar.infoSeqExt hpr hh c'))
                have h2 := mul_nonneg hb.le (hiff2.1 (SeqVar.infoSeqExt hpr hh c'))
                have ha0 : a * x₁ (SeqVar.infoSeqExt hpr hh c') = 0 := by
                  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hsum_c'
                  linarith
                exact (mul_eq_zero.1 ha0).resolve_left ha.ne'
              have hflow1 := hiff1.2.2 h hh
              rw [ih_pre, hpre_one] at hflow1
              have hs_one : T.pureToRealizationPlan i s (SeqVar.infoSeqExt hpr hh c) = 1 := by
                simp [ExtensiveTree.pureToRealizationPlan, hm_ext]
              rw [hs_one, ← hflow1, sum_eq_single c]
              · exact fun c' _ hc' => hothers c' hc'
              · exact fun hmem => absurd (mem_univ c) hmem
      intro τ
      exact hlen τ.1.length τ rfl
    exact funext hmatch

open Classical in
/-- Inequality-system matrix stacking `[E; -E; -I]` so that `seqPolyMat T i *ᵥ x ≤ seqPolyRhs T i`
is equivalent to `T.IsRealizationPlan i x`, enabling direct `Matrix.IsVertex` reasoning. -/
noncomputable def seqPolyMat [DecidableEq ι] (T : ExtensiveTree ι H Act) (i : ι) :
    Matrix
      (Option {h : H i // T.OccursInfoSet i h} ⊕
        Option {h : H i // T.OccursInfoSet i h} ⊕ SeqVar T i)
      (SeqVar T i) ℝ
  | .inl r, σ => seqMat T i r σ
  | .inr (.inl r), σ => -seqMat T i r σ
  | .inr (.inr σ₀), σ => if σ₀ = σ then -1 else 0

/-- Inequality-system right-hand side stacking `[e; -e; 0]`. -/
def seqPolyRhs [DecidableEq ι] (T : ExtensiveTree ι H Act) (i : ι) :
    (Option {h : H i // T.OccursInfoSet i h} ⊕
      Option {h : H i // T.OccursInfoSet i h} ⊕ SeqVar T i) → ℝ
  | .inl r => seqRhs T i r
  | .inr (.inl r) => -seqRhs T i r
  | .inr (.inr _) => 0

@[simp]
theorem seqPolyRhs_inl [DecidableEq ι] (T : ExtensiveTree ι H Act) (i : ι)
    (r : Option {h : H i // T.OccursInfoSet i h}) :
    seqPolyRhs T i (.inl r) = seqRhs T i r := by
  simp [seqPolyRhs]

@[simp]
theorem seqPolyRhs_inr_inl [DecidableEq ι] (T : ExtensiveTree ι H Act) (i : ι)
    (r : Option {h : H i // T.OccursInfoSet i h}) :
    seqPolyRhs T i (.inr (.inl r)) = -seqRhs T i r := by
  simp [seqPolyRhs]

@[simp]
theorem seqPolyRhs_inr_inr [DecidableEq ι] (T : ExtensiveTree ι H Act) (i : ι) (σ : SeqVar T i) :
    seqPolyRhs T i (.inr (.inr σ)) = 0 := by
  simp [seqPolyRhs]

theorem seqPolyMat_mulVec_le_iff [DecidableEq ι] [∀ j h, Fintype (Act j h)]
    (T : ExtensiveTree ι H Act) (i : ι) (x : SeqVar T i → ℝ) :
    seqPolyMat T i *ᵥ x ≤ seqPolyRhs T i ↔ T.IsRealizationPlan i x := by
  classical
  have hmul : ∀ r, (seqPolyMat T i *ᵥ x) (.inl r) = (seqMat T i *ᵥ x) r := by
    intro r
    rfl
  have hmul_neg : ∀ r, (seqPolyMat T i *ᵥ x) (.inr (.inl r)) = -(seqMat T i *ᵥ x) r := by
    intro r
    simp [Matrix.mulVec, dotProduct, seqPolyMat, neg_mul, sum_neg_distrib]
  have hmul_nn : ∀ σ₀, (seqPolyMat T i *ᵥ x) (.inr (.inr σ₀)) = -x σ₀ := by
    intro σ₀
    simp only [Matrix.mulVec, dotProduct, seqPolyMat]
    rw [sum_eq_single σ₀]
    · simp
    · intro σ _ hne
      simp [hne.symm]
    · intro hmem
      exact absurd (mem_univ σ₀) hmem
  constructor
  · intro hle
    refine ⟨fun σ₀ => ?_, funext fun r => ?_⟩
    · have h := hle (.inr (.inr σ₀))
      rw [hmul_nn, seqPolyRhs] at h
      linarith
    · have h1 := hle (.inl r)
      have h2 := hle (.inr (.inl r))
      rw [hmul, seqPolyRhs] at h1
      rw [hmul_neg, seqPolyRhs] at h2
      linarith
  · rintro ⟨hnn, heq⟩ k
    rcases k with r | (r | σ₀)
    · rw [hmul, heq, seqPolyRhs]
    · rw [hmul_neg, heq, seqPolyRhs]
    · rw [hmul_nn, seqPolyRhs]
      linarith [hnn σ₀]

open Classical in
/-- **Polyhedral vertex characterization** ([vonStengel2007], Section 3.10, p. 72): the basic
feasible vertices (`Matrix.IsVertex`) of the realization-plan polytope `seqMat *ᵥ x = seqRhs, x ≥ 0`
are precisely the pure realization plans `T.pureToRealizationPlan i s`. -/
theorem isVertex_seqPolyMat_iff [DecidableEq ι] [∀ j h, Fintype (Act j h)]
    [∀ j h, Nonempty (Act j h)] {T : ExtensiveTree ι H Act} {i : ι} [Fintype (H i)]
    (hpr : T.PerfectRecall i) (x : SeqVar T i → ℝ) :
    Matrix.IsVertex (seqPolyMat T i) (seqPolyRhs T i) x ↔
      x ∈ Set.range (T.pureToRealizationPlan i) := by
  classical
  rw [Matrix.isVertex_iff_mem_extremePoints_real]
  have hset : {y : SeqVar T i → ℝ | seqPolyMat T i *ᵥ y ≤ seqPolyRhs T i} =
      {y : SeqVar T i → ℝ | T.IsRealizationPlan i y} :=
    Set.ext fun y => seqPolyMat_mulVec_le_iff T i y
  rw [hset, mem_extremePoints_isRealizationPlan_iff hpr x]

end ReducedFormAndPolytope

section TwoPlayerBilinear

variable {H : Bool → Type v} {Act : ∀ i, H i → Type}

open Classical in
/-- Sequence-form payoff matrix of player `p : Bool` in a two-player extensive game
([vonStengel2007], Section 3.10). -/
noncomputable def ExtensiveTree.seqPayoffMat [∀ i h, Fintype (Act i h)]
    (T : ExtensiveTree Bool H Act) (p : Bool) :
    Matrix (SeqVar T false) (SeqVar T true) ℝ :=
  fun σ₀ σ₁ => ∑ z : Terminal T,
    if z.seq false = σ₀.1 ∧ z.seq true = σ₁.1 then z.chanceWeight * z.payoff p else 0

theorem seqPayoffMat_bilinear [∀ i h, Fintype (Act i h)]
    (T : ExtensiveTree Bool H Act) (p : Bool)
    (r₀ : Seq H Act false → ℝ) (r₁ : Seq H Act true → ℝ) :
    (fun σ => r₀ σ.1) ⬝ᵥ (T.seqPayoffMat p *ᵥ fun τ => r₁ τ.1) =
      ∑ z : Terminal T, (z.chanceWeight * r₀ (z.seq false) * r₁ (z.seq true)) * z.payoff p := by
  classical
  simp only [dotProduct, Matrix.mulVec, ExtensiveTree.seqPayoffMat, mul_sum, sum_mul]
  calc ∑ σ₀ : SeqVar T false, ∑ σ₁ : SeqVar T true, ∑ z : Terminal T,
          r₀ σ₀.1 * ((if z.seq false = σ₀.1 ∧ z.seq true = σ₁.1 then
            z.chanceWeight * z.payoff p else 0) * r₁ σ₁.1)
      = ∑ σ₀ : SeqVar T false, ∑ z : Terminal T, ∑ σ₁ : SeqVar T true,
          r₀ σ₀.1 * ((if z.seq false = σ₀.1 ∧ z.seq true = σ₁.1 then
            z.chanceWeight * z.payoff p else 0) * r₁ σ₁.1) := by
        refine sum_congr rfl fun σ₀ _ => sum_comm
    _ = ∑ z : Terminal T, ∑ σ₀ : SeqVar T false, ∑ σ₁ : SeqVar T true,
          r₀ σ₀.1 * ((if z.seq false = σ₀.1 ∧ z.seq true = σ₁.1 then
            z.chanceWeight * z.payoff p else 0) * r₁ σ₁.1) := sum_comm
    _ = ∑ z : Terminal T, (z.chanceWeight * r₀ (z.seq false) * r₁ (z.seq true)) * z.payoff p := by
        refine sum_congr rfl fun z _ => ?_
        let σz₀ : SeqVar T false := ⟨z.seq false, z, List.prefix_rfl⟩
        let σz₁ : SeqVar T true := ⟨z.seq true, z, List.prefix_rfl⟩
        rw [sum_eq_single σz₀]
        · rw [sum_eq_single σz₁]
          · simp [σz₀, σz₁]
            ring
          · intro σ₁ _ hne
            have hne' : z.seq true ≠ σ₁.1 := fun h => hne (Subtype.ext h.symm)
            simp [hne']
          · intro hmem
            exact absurd (mem_univ σz₁) hmem
        · intro σ₀ _ hne
          refine sum_eq_zero fun σ₁ _ => ?_
          have hne' : z.seq false ≠ σ₀.1 := fun h => hne (Subtype.ext h.symm)
          simp [hne']
        · intro hmem
          exact absurd (mem_univ σz₀) hmem

/-- Expected payoff in a two-player extensive game under behavior strategies expressed in bilinear
sequence form `xᵀ A_p y` ([vonStengel2007], Section 3.10). -/
theorem evalBehavior_eq_seqPayoffMat [∀ i h, Fintype (Act i h)]
    (T : ExtensiveTree Bool H Act) (β : ∀ i, ∀ h : H i, Act i h → ℝ) (p : Bool) :
    T.evalBehavior β p =
      (T.behaviorToRealizationPlan false (β false)) ⬝ᵥ
        (T.seqPayoffMat p *ᵥ T.behaviorToRealizationPlan true (β true)) := by
  rw [ExtensiveTree.evalBehavior_eq_sum_terminal]
  have hb := seqPayoffMat_bilinear T p (realizationProbBehavior (β false))
    (realizationProbBehavior (β true))
  change _ = (fun σ => realizationProbBehavior (β false) σ.1) ⬝ᵥ
    (T.seqPayoffMat p *ᵥ fun τ => realizationProbBehavior (β true) τ.1)
  rw [hb]
  refine sum_congr rfl fun z _ => ?_
  rw [terminalProbBehavior_eq, Fintype.prod_bool]
  ring

/-- Expected payoff in a two-player extensive game under mixed strategies expressed in bilinear
sequence form `xᵀ A_p y` ([vonStengel2007], Section 3.10). -/
theorem evalMixed_eq_seqPayoffMat [∀ i, Fintype (H i)] [∀ i, DecidableEq (H i)]
    [∀ i h, Fintype (Act i h)] (T : ExtensiveTree Bool H Act)
    (μ : ∀ i, PureStrategy H Act i → ℝ) (p : Bool) :
    T.evalMixed μ p =
      (T.mixedToRealizationPlan false (μ false)) ⬝ᵥ
        (T.seqPayoffMat p *ᵥ T.mixedToRealizationPlan true (μ true)) := by
  rw [ExtensiveTree.evalMixed_eq_sum_terminal]
  have hb := seqPayoffMat_bilinear T p (realizationProbMixed (μ false))
    (realizationProbMixed (μ true))
  have h0 : T.mixedToRealizationPlan false (μ false) =
      fun σ => realizationProbMixed (μ false) σ.1 := rfl
  have h1 : T.mixedToRealizationPlan true (μ true) =
      fun τ => realizationProbMixed (μ true) τ.1 := rfl
  rw [h0, h1, hb]
  refine sum_congr rfl fun z _ => ?_
  rw [terminalProbMixed_eq, Fintype.prod_bool]
  ring

end TwoPlayerBilinear

end Cslib.GameTheory.Extensive
