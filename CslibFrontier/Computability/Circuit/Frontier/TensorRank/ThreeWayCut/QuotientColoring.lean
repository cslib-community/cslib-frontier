/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
-- `import all`: reads private planar sector helpers from `PlanarGeometry` and private Gaussian
-- block-sample measures and symmetries from `SampleSpace`.
import all CslibFrontier.Computability.Circuit.Frontier.TensorRank.ThreeWayCut.PlanarGeometry
import all CslibFrontier.Computability.Circuit.Frontier.TensorRank.ThreeWayCut.SampleSpace
import CslibFrontier.Computability.Circuit.Frontier.Layouts.Gaussian.EdgeScores
import CslibFrontier.Foundations.MeasureTheory.Constructions.BorelSpace.Order
import CslibFrontier.Foundations.Probability.Gaussian.ConvexCap
import CslibFrontier.Foundations.Probability.Gaussian.OffMedian
import CslibFrontier.Foundations.Probability.WeightedSecondMoment
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

/-!
# `Z₃`-equivariant block coloring on a loopless subcubic multigraph

Defines `edgeVec2`, sector counts `secCount`, tie-broken sector winner `blockColor`, and pairwise /
bichromatic cut events (`cutPairEvent`, `cutAnyEvent`), establishing local ball dependence and exact
`1 / 3` vertex and cut marginals under `Z₃` symmetry.
-/

-- This proof-only companion is intentionally private; sibling ThreeWayCut modules use import all.
set_option linter.privateModule false

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace

namespace Cslib.Circuits.Frontier.TensorRank

open Cslib.Circuits.Frontier.Gaussian Cslib.Circuits.Frontier.Multigraph

attribute [local instance]
  instIsProbabilityMeasure_gauss2
  instIsProbabilityMeasure_gaussTie
  instIsProbabilityMeasure_blockMeasure

section QuotientColoring

variable {W F : Type*} [Fintype W] [Finite F]

/-- The `2`D Gaussian edge vector `(edgeScore Q q R g₁ e, edgeScore Q q R g₂ e)` of an edge `e`. -/
private noncomputable def edgeVec2 (Q : Multigraph W F) (q : ℝ) (R : ℕ)
    (ω : W → BlockSample) (e : F) : ℝ × ℝ :=
  (edgeScore Q q R (fun B => (ω B).1.1) e, edgeScore Q q R (fun B => (ω B).1.2) e)

omit [Finite F] in
private theorem measurable_edgeVec2 (Q : Multigraph W F) (q : ℝ) (R : ℕ) (e : F) :
    Measurable fun ω : W → BlockSample => edgeVec2 Q q R ω e := by
  exact ((measurable_edgeScore q R e).comp (by fun_prop)).prodMk
    ((measurable_edgeScore q R e).comp (by fun_prop))

omit [Finite F] in
private theorem edgeVec2_congr {Q : Multigraph W F} {q : ℝ} {R : ℕ} {B : W} {e : F}
    (he : e ∈ Q.incidenceSet B) {ω ω' : W → BlockSample}
    (h : ∀ z ∈ closedBall Q.toSimpleGraph B (R + 1), ω z = ω' z) :
    edgeVec2 Q q R ω e = edgeVec2 Q q R ω' e := by
  ext
  · exact edgeScore_congr he fun z hz => congrArg (fun s => s.1.1) (h z hz)
  · exact edgeScore_congr he fun z hz => congrArg (fun s => s.1.2) (h z hz)

omit [Finite F] in
private theorem dot2_edgeVec2 (Q : Multigraph W F) (q : ℝ) (R : ℕ) (u : ℝ × ℝ)
    (ω : W → BlockSample) (e : F) :
    dot2 u (edgeVec2 Q q R ω e) = edgeScore Q q R (fun B => dot2 u (ω B).1) e := by
  dsimp [dot2, edgeVec2, edgeScore]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun B _ => ?_
  ring

omit [Finite F] in
private theorem edgeVec2_rotSample (Q : Multigraph W F) (q : ℝ) (R : ℕ)
    (ω : W → BlockSample) (e : F) :
    edgeVec2 Q q R (fun B => rotSample (ω B)) e = rot120 (edgeVec2 Q q R ω e) := by
  have h1 := dot2_edgeVec2 Q q R (-1 / 2, -√3 / 2) ω e
  have h2 := dot2_edgeVec2 Q q R (√3 / 2, -1 / 2) ω e
  simp only [edgeVec2, rotSample, rot120, dot2, neg_div, neg_mul, ← sub_eq_add_neg] at h1 h2 ⊢
  exact Prod.ext h1.symm h2.symm

omit [Finite F] in
private theorem edgeVec2_negSample (Q : Multigraph W F) (q : ℝ) (R : ℕ)
    (ω : W → BlockSample) (e : F) :
    edgeVec2 Q q R (fun B => negSample (ω B)) e = neg2 (edgeVec2 Q q R ω e) := by
  have h1 := dot2_edgeVec2 Q q R (-1, 0) ω e
  have h2 := dot2_edgeVec2 Q q R (0, -1) ω e
  simp only [edgeVec2, negSample, neg2, dot2, neg_one_mul, zero_mul, zero_add, add_zero]
    at h1 h2 ⊢
  exact Prod.ext h1.symm h2.symm

private theorem toFinset_eq_of_fintype {α : Type*} (S : Set α) (i₁ : Fintype S) [i₂ : Fintype S] :
    @Set.toFinset α S i₁ = @Set.toFinset α S i₂ := by
  ext x
  rw [@Set.mem_toFinset _ _ i₁, @Set.mem_toFinset _ _ i₂]

open Classical in
/-- Number of incident edges at `B` falling into open sector `c`. -/
private noncomputable def secCount (Q : Multigraph W F) (q : ℝ) (R : ℕ)
    (ω : W → BlockSample) (B : W) (c : Fin 3) : ℕ :=
  ((@Set.toFinset F (Q.incidenceSet B) (Fintype.ofFinite _)).filter fun e =>
    inOpenSector c (edgeVec2 Q q R ω e)).card

private theorem secCount_rotSample (Q : Multigraph W F) (q : ℝ) (R : ℕ)
    (ω : W → BlockSample) (B : W) (c : Fin 3) :
    secCount Q q R (fun B' => rotSample (ω B')) B (c + 1) = secCount Q q R ω B c := by
  classical
  have := Fintype.ofFinite F
  refine congrArg Finset.card (Finset.ext fun e => ?_)
  simp only [Finset.mem_filter, edgeVec2_rotSample, inOpenSector_rot120]

/-- Lexicographic sector comparison `(secCount, tieBreaker)`. -/
private def beats (Q : Multigraph W F) (q : ℝ) (R : ℕ)
    (ω : W → BlockSample) (B : W) (c c' : Fin 3) : Prop :=
  secCount Q q R ω B c' < secCount Q q R ω B c ∨
    (secCount Q q R ω B c' = secCount Q q R ω B c ∧ (ω B).2 c' < (ω B).2 c)

private theorem beats_rotSample (Q : Multigraph W F) (q : ℝ) (R : ℕ)
    (ω : W → BlockSample) (B : W) (c c' : Fin 3) :
    beats Q q R (fun B' => rotSample (ω B')) B (c + 1) (c' + 1) ↔ beats Q q R ω B c c' := by
  rw [beats, secCount_rotSample, secCount_rotSample]
  simp only [beats, rotSample, shiftTie_add_one]

private theorem beats_asymm {Q : Multigraph W F} {q : ℝ} {R : ℕ}
    {ω : W → BlockSample} {B : W} {c c' : Fin 3}
    (h : beats Q q R ω B c c') : ¬beats Q q R ω B c' c := by
  simp only [beats] at h ⊢
  rintro (h' | ⟨heq, hτ'⟩) <;> rcases h with hlt | ⟨heq2, hτ⟩ <;>
    first | omega | linarith only [hτ, hτ']

private theorem beats_total {Q : Multigraph W F} {q : ℝ} {R : ℕ}
    {ω : W → BlockSample} {B : W} (hinj : Function.Injective (ω B).2)
    {c c' : Fin 3} (hne : c ≠ c') :
    beats Q q R ω B c c' ∨ beats Q q R ω B c' c := by
  rcases lt_trichotomy (secCount Q q R ω B c') (secCount Q q R ω B c) with hlt | heq | hgt
  · exact Or.inl (Or.inl hlt)
  · rcases lt_or_gt_of_ne (fun h => hne (hinj h).symm) with hτ | hτ
    · exact Or.inl (Or.inr ⟨heq, hτ⟩)
    · exact Or.inr (Or.inr ⟨heq.symm, hτ⟩)
  · exact Or.inr (Or.inl hgt)

private theorem beats_trans {Q : Multigraph W F} {q : ℝ} {R : ℕ}
    {ω : W → BlockSample} {B : W} {c₁ c₂ c₃ : Fin 3}
    (h12 : beats Q q R ω B c₁ c₂) (h23 : beats Q q R ω B c₂ c₃) :
    beats Q q R ω B c₁ c₃ := by
  rcases h12 with hlt1 | ⟨heq1, hτ1⟩ <;> rcases h23 with hlt2 | ⟨heq2, hτ2⟩
  · exact Or.inl (hlt2.trans hlt1)
  · exact Or.inl (heq2.trans_lt hlt1)
  · exact Or.inl (hlt2.trans_eq heq1)
  · exact Or.inr ⟨heq2.trans heq1, hτ2.trans hτ1⟩

open Classical in
/-- Block sector color: chooses the unique winner under `beats` (with deterministic fallback on
measure-zero ties). -/
private noncomputable def blockColor (Q : Multigraph W F) (q : ℝ) (R : ℕ)
    (ω : W → BlockSample) (B : W) : Fin 3 :=
  if beats Q q R ω B 0 1 ∧ beats Q q R ω B 0 2 then 0
  else if beats Q q R ω B 1 2 then 1
  else 2

private theorem blockColor_eq_iff_of_injective {Q : Multigraph W F} {q : ℝ} {R : ℕ}
    {ω : W → BlockSample} {B : W} (hinj : Function.Injective (ω B).2) (c : Fin 3) :
    blockColor Q q R ω B = c ↔ ∀ c' : Fin 3, c' ≠ c → beats Q q R ω B c c' := by
  have ht01 := beats_total (Q := Q) (q := q) (R := R) hinj (by decide : (0 : Fin 3) ≠ 1)
  have ht12 := beats_total (Q := Q) (q := q) (R := R) hinj (by decide : (1 : Fin 3) ≠ 2)
  have ht02 := beats_total (Q := Q) (q := q) (R := R) hinj (by decide : (0 : Fin 3) ≠ 2)
  constructor
  · intro hc c' hc'
    subst hc
    unfold blockColor at hc' ⊢
    split_ifs at hc' ⊢ with h0 h1
    · fin_cases c'
      · exact absurd rfl hc'
      · exact h0.1
      · exact h0.2
    · fin_cases c'
      · rcases ht01 with hb01 | hb10
        · exact absurd ⟨hb01, beats_trans hb01 h1⟩ h0
        · exact hb10
      · exact absurd rfl hc'
      · exact h1
    · have hb21 : beats Q q R ω B 2 1 := ht12.resolve_left h1
      fin_cases c'
      · rcases ht02 with hb02 | hb20
        · rcases ht01 with hb01 | hb10
          · exact absurd ⟨hb01, hb02⟩ h0
          · exact absurd (beats_trans hb10 hb02) h1
        · exact hb20
      · exact hb21
      · exact absurd rfl hc'
  · intro hall
    unfold blockColor
    fin_cases c <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at hall ⊢
    · exact ite_eq_left ⟨hall 1 (by decide), hall 2 (by decide)⟩
    · rw [ite_eq_right fun h => beats_asymm (hall 0 (by decide)) h.1,
        ite_eq_left (hall 2 (by decide))]
    · rw [ite_eq_right fun h => beats_asymm (hall 0 (by decide)) h.2,
        ite_eq_right (beats_asymm (hall 1 (by decide)))]

private theorem blockColor_of_strict_majority {Q : Multigraph W F} {q : ℝ} {R : ℕ}
    {ω : W → BlockSample} {B : W} (hinj : Function.Injective (ω B).2) {c : Fin 3}
    (hmaj : ∀ c' : Fin 3, c' ≠ c → secCount Q q R ω B c' < secCount Q q R ω B c) :
    blockColor Q q R ω B = c :=
  (blockColor_eq_iff_of_injective hinj c).mpr fun c' hc' => Or.inl (hmaj c' hc')

private theorem blockColor_rotSample {Q : Multigraph W F} {q : ℝ} {R : ℕ}
    {ω : W → BlockSample} {B : W} (hinj : Function.Injective (ω B).2) :
    blockColor Q q R (fun B' => rotSample (ω B')) B = blockColor Q q R ω B + 1 := by
  have hinj' : Function.Injective (((fun B' => rotSample (ω B')) B).2) :=
    fun _ _ h => add_right_cancel (hinj h)
  set c := blockColor Q q R ω B
  have hall := (blockColor_eq_iff_of_injective hinj c).mp rfl
  refine (blockColor_eq_iff_of_injective (Q := Q) (q := q) (R := R)
      (ω := fun B' => rotSample (ω B')) hinj' (c + 1)).mpr fun c' hc' => ?_
  have hc'_eq : c' = (c' + 2) + 1 := by fin_cases c' <;> decide
  rw [hc'_eq, beats_rotSample]
  exact hall (c' + 2) fun h => hc' (hc'_eq.trans (congrArg (· + 1) h))


omit [Finite F] in
private theorem measurableSet_inOpenSector_edgeVec2 (Q : Multigraph W F) (q : ℝ) (R : ℕ)
    (e : F) (c : Fin 3) :
    MeasurableSet {ω : W → BlockSample | inOpenSector c (edgeVec2 Q q R ω e)} := by
  dsimp [inOpenSector]
  exact (measurableSet_lt
      ((by unfold dot2; fun_prop : Measurable (dot2 (normVec c))).comp
        (measurable_edgeVec2 Q q R e)) measurable_const).inter
    (measurableSet_lt measurable_const
      ((by unfold dot2; fun_prop : Measurable (dot2 (normVec (c + 2)))).comp
        (measurable_edgeVec2 Q q R e)))

open Classical in
private theorem measurable_secCount (Q : Multigraph W F) (q : ℝ) (R : ℕ) (B : W) (c : Fin 3) :
    Measurable fun ω : W → BlockSample => secCount Q q R ω B c := by
  have := Fintype.ofFinite F
  have hfn : (fun ω : W → BlockSample => secCount Q q R ω B c) =
      fun ω => ∑ e ∈ (Q.incidenceSet B).toFinset,
        if inOpenSector c (edgeVec2 Q q R ω e) then 1 else 0 := by
    funext ω
    unfold secCount
    rw [toFinset_eq_of_fintype (Q.incidenceSet B) _]
    exact Finset.card_filter (fun e => inOpenSector c (edgeVec2 Q q R ω e))
      (Q.incidenceSet B).toFinset
  rw [hfn]
  exact Finset.measurable_sum _ fun e _ =>
    Measurable.ite (measurableSet_inOpenSector_edgeVec2 Q q R e c) measurable_const measurable_const

private theorem measurableSet_beats (Q : Multigraph W F) (q : ℝ) (R : ℕ) (B : W)
    (c c' : Fin 3) : MeasurableSet {ω : W → BlockSample | beats Q q R ω B c c'} := by
  dsimp [beats]
  exact (measurableSet_lt (measurable_secCount Q q R B c') (measurable_secCount Q q R B c)).union
    ((measurableSet_eq_fun (measurable_secCount Q q R B c')
      (measurable_secCount Q q R B c)).inter
      (measurableSet_lt
        ((measurable_pi_apply c').comp ((measurable_snd).comp (measurable_pi_apply B)))
        ((measurable_pi_apply c).comp ((measurable_snd).comp (measurable_pi_apply B)))))

private theorem measurableSet_blockColor_eq (Q : Multigraph W F) (q : ℝ) (R : ℕ)
    (B : W) (c : Fin 3) :
    MeasurableSet {ω : W → BlockSample | blockColor Q q R ω B = c} :=
  (Measurable.ite ((measurableSet_beats Q q R B 0 1).inter (measurableSet_beats Q q R B 0 2))
      measurable_const (Measurable.ite (measurableSet_beats Q q R B 1 2) measurable_const
        measurable_const) : Measurable fun ω => blockColor Q q R ω B)
    (measurableSet_singleton c)

private theorem dependsOn_blockColor (Q : Multigraph W F) (q : ℝ) (R : ℕ) (B : W) :
    DependsOn (fun ω => blockColor Q q R ω B) (closedBall Q.toSimpleGraph B (R + 1)) := by
  intro ω₁ ω₂ h12
  have hsec (c : Fin 3) : secCount Q q R ω₁ B c = secCount Q q R ω₂ B c := by
    classical
    refine congrArg Finset.card (Finset.filter_congr fun e he => ?_)
    rw [edgeVec2_congr ((@Set.mem_toFinset _ _ (Fintype.ofFinite _)).mp he) h12]
  have hbeats (c c' : Fin 3) : beats Q q R ω₁ B c c' ↔ beats Q q R ω₂ B c c' := by
    rw [beats, beats, hsec, hsec, h12 B (by simp [closedBall])]
  dsimp only [blockColor]
  rw [hbeats 0 1, hbeats 0 2, hbeats 1 2]

/-- At any block `B`, the event `{ω | ¬Function.Injective (ω B).2}` has measure zero under
`Measure.pi (fun _ => blockMeasure)`. -/
private theorem measureReal_not_injective_tie_zero (B : W) :
    (Measure.pi fun _ : W => blockMeasure).real
      {ω : W → BlockSample | ¬Function.Injective (ω B).2} = 0 := by
  have hmp_eval : MeasurePreserving (fun ω : W → BlockSample => (ω B).2)
      (Measure.pi fun _ : W => blockMeasure) gaussTie :=
    (MeasureTheory.measurePreserving_snd (μ := gauss2) (ν := gaussTie)).comp
      (MeasureTheory.measurePreserving_eval (fun _ : W => blockMeasure) B)
  have hm : MeasurableSet {τ : Fin 3 → ℝ | ¬Function.Injective τ} := by
    have hset : {τ : Fin 3 → ℝ | ¬Function.Injective τ} =
        ⋃ c₁ : Fin 3, ⋃ c₂ ∈ ({c₁}ᶜ : Set (Fin 3)), {τ | τ c₁ = τ c₂} := by
      ext τ
      simp only [mem_ofPred_eq, mem_iUnion, mem_compl_iff, mem_singleton_iff]
      change (¬∀ a₁ a₂ : Fin 3, τ a₁ = τ a₂ → a₁ = a₂) ↔ _
      push Not
      exact ⟨fun ⟨c₁, c₂, heq, hne⟩ => ⟨c₁, c₂, Ne.symm hne, heq⟩,
        fun ⟨c₁, c₂, hne, heq⟩ => ⟨c₁, c₂, heq, Ne.symm hne⟩⟩
    rw [hset]
    exact MeasurableSet.iUnion fun c₁ => (toFinite _).measurableSet_biUnion fun c₂ _ =>
      measurableSet_eq_fun (measurable_pi_apply c₁) (measurable_pi_apply c₂)
  have hpre : {ω : W → BlockSample | ¬Function.Injective (ω B).2} =
      (fun ω : W → BlockSample => (ω B).2) ⁻¹' {τ : Fin 3 → ℝ | ¬Function.Injective τ} := rfl
  rw [hpre, hmp_eval.measureReal_preimage hm.nullMeasurableSet]
  exact gaussTie_not_injective_zero

/-- Three pairwise disjoint events whose probabilities agree along the cycle `k ↦ k + 1` each
carry a third of the probability of their union. -/
private theorem measureReal_eq_third_of_cyclic {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] (E : Fin 3 → Set Ω) (hm : ∀ c, MeasurableSet (E c))
    (hd : Pairwise (Function.onFun Disjoint E)) (hstep : ∀ k, P.real (E k) = P.real (E (k + 1)))
    (c : Fin 3) : P.real (E c) = 1 / 3 * P.real (⋃ c, E c) := by
  have h01 : P.real (E 0) = P.real (E 1) := hstep 0
  have h12 : P.real (E 1) = P.real (E 2) := hstep 1
  rw [measureReal_iUnion_fintype hd hm, Fin.sum_univ_three]
  fin_cases c <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> linarith only [h01, h12]

/-- **Exact `1 / 3` marginal.** By `Z₃`-symmetry (`rotSample`), every block `B` lands in each color
`c : Fin 3` with probability `1 / 3`. -/
private theorem measureReal_blockColor_eq_one_third (Q : Multigraph W F) (q : ℝ) (R : ℕ)
    (B : W) (c : Fin 3) :
    (Measure.pi fun _ : W => blockMeasure).real
      {ω | blockColor Q q R ω B = c} = 1 / 3 := by
  set P := Measure.pi fun _ : W => blockMeasure
  have hN_null : P {ω : W → BlockSample | ¬Function.Injective (ω B).2} = 0 :=
    (measureReal_eq_zero_iff (measure_ne_top _ _)).mp (measureReal_not_injective_tie_zero B)
  have hmp_rot : MeasurePreserving (fun ω B' => rotSample (ω B')) P P :=
    measurePreserving_pi _ _ fun _ => measurePreserving_rotSample
  have h := measureReal_eq_third_of_cyclic (P := P) (fun c => {ω | blockColor Q q R ω B = c})
    (measurableSet_blockColor_eq Q q R B)
    (fun a b hab => disjoint_left.mpr fun _ (ha : _ = a) (hb : _ = b) => hab (ha.symm.trans hb))
    (fun k => ?_) c
  · rwa [iUnion_eq_univ_iff.mpr fun ω => ⟨_, rfl⟩, probReal_univ, mul_one] at h
  rw [← hmp_rot.measureReal_preimage
    (measurableSet_blockColor_eq Q q R B (k + 1)).nullMeasurableSet]
  refine measureReal_congr ?_
  filter_upwards [compl_mem_ae_iff.mpr hN_null] with ω hω
  simp [blockColor_rotSample (not_not.mp hω)]

/-- Event that quotient edge `e` crosses between color `c` and color `c + 1`. -/
private def cutPairEvent (Q : Multigraph W F) (q : ℝ) (R : ℕ) (c : Fin 3) (e : F) :
    Set (W → BlockSample) :=
  {ω | (blockColor Q q R ω (Q.src e) = c ∧ blockColor Q q R ω (Q.tgt e) = c + 1) ∨
    (blockColor Q q R ω (Q.src e) = c + 1 ∧ blockColor Q q R ω (Q.tgt e) = c)}

/-- Event that quotient edge `e` is bichromatic (`blockColor (src e) ≠ blockColor (tgt e)`). -/
private def cutAnyEvent (Q : Multigraph W F) (q : ℝ) (R : ℕ) (e : F) :
    Set (W → BlockSample) :=
  {ω | blockColor Q q R ω (Q.src e) ≠ blockColor Q q R ω (Q.tgt e)}

private theorem measurableSet_cutPairEvent (Q : Multigraph W F) (q : ℝ) (R : ℕ)
    (c : Fin 3) (e : F) : MeasurableSet (cutPairEvent Q q R c e) :=
  ((measurableSet_blockColor_eq Q q R (Q.src e) c).inter
      (measurableSet_blockColor_eq Q q R (Q.tgt e) (c + 1))).union
    ((measurableSet_blockColor_eq Q q R (Q.src e) (c + 1)).inter
      (measurableSet_blockColor_eq Q q R (Q.tgt e) c))

private theorem dependsOn_cutPairEvent (Q : Multigraph W F) (q : ℝ) (R : ℕ)
    (c : Fin 3) (e : F) :
    DependsOn (· ∈ cutPairEvent Q q R c e)
      (closedBall Q.toSimpleGraph (Q.src e) (R + 2)) := by
  intro ω₁ ω₂ h12
  have hcs := dependsOn_blockColor Q q R (Q.src e) fun z hz => h12 z <| by
    simp only [closedBall, mem_ofPred_eq] at hz ⊢
    exact hz.trans (Nat.cast_le.mpr (Nat.le_succ _))
  have hct := dependsOn_blockColor Q q R (Q.tgt e) fun z hz =>
    h12 z (closedBall_tgt_subset e (R + 1) hz)
  simp only [cutPairEvent, mem_ofPred_eq, hcs, hct]


private theorem iUnion_cutPairEvent_eq_cutAnyEvent (Q : Multigraph W F) (q : ℝ) (R : ℕ) (e : F) :
    ⋃ c, cutPairEvent Q q R c e = cutAnyEvent Q q R e := by
  ext ω
  simp only [mem_iUnion, cutPairEvent, cutAnyEvent, mem_ofPred_eq]
  generalize blockColor Q q R ω (Q.src e) = a
  generalize blockColor Q q R ω (Q.tgt e) = b
  fin_cases a <;> fin_cases b <;> decide

private theorem measurableSet_cutAnyEvent (Q : Multigraph W F) (q : ℝ) (R : ℕ) (e : F) :
    MeasurableSet (cutAnyEvent Q q R e) := by
  rw [← iUnion_cutPairEvent_eq_cutAnyEvent Q q R e]
  exact .iUnion fun c => measurableSet_cutPairEvent Q q R c e

/-- **Exact `1 / 3` cut symmetry.** Each unordered color pair `{c, c + 1}` receives `1 / 3` of the
bichromatic probability of every edge `e`. -/
private theorem measureReal_cutPairEvent_eq_third (Q : Multigraph W F) (q : ℝ) (R : ℕ)
    (c : Fin 3) (e : F) :
    (Measure.pi fun _ : W => blockMeasure).real (cutPairEvent Q q R c e) =
      1 / 3 * (Measure.pi fun _ : W => blockMeasure).real (cutAnyEvent Q q R e) := by
  set P := Measure.pi fun _ : W => blockMeasure
  have hnull (B : W) : P {ω : W → BlockSample | ¬Function.Injective (ω B).2} = 0 :=
    (measureReal_eq_zero_iff (measure_ne_top _ _)).mp (measureReal_not_injective_tie_zero B)
  have hmp_rot : MeasurePreserving (fun ω B' => rotSample (ω B')) P P :=
    measurePreserving_pi _ _ fun _ => measurePreserving_rotSample
  rw [← iUnion_cutPairEvent_eq_cutAnyEvent Q q R e]
  refine measureReal_eq_third_of_cyclic (fun c => cutPairEvent Q q R c e)
    (fun c => measurableSet_cutPairEvent Q q R c e)
    (fun a b hab => disjoint_left.mpr fun _ h1 h2 => hab <|
      (by decide : ∀ u v a b : Fin 3, (u = a ∧ v = a + 1 ∨ u = a + 1 ∧ v = a) →
        (u = b ∧ v = b + 1 ∨ u = b + 1 ∧ v = b) → a = b) _ _ a b h1 h2)
    (fun k => ?_) c
  rw [← hmp_rot.measureReal_preimage
    (measurableSet_cutPairEvent Q q R (k + 1) e).nullMeasurableSet]
  refine measureReal_congr ?_
  filter_upwards [compl_mem_ae_iff.mpr (hnull (Q.src e)), compl_mem_ae_iff.mpr (hnull (Q.tgt e))]
    with ω h1 h2
  simp [cutPairEvent, blockColor_rotSample (not_not.mp h1), blockColor_rotSample (not_not.mp h2)]

omit [Finite F] in
private theorem measure_dot2_edgeVec2_eq_zero {Q : Multigraph W F} {q : ℝ} {R : ℕ} {e : F}
    (hunit : ‖edgeVector Q q R e‖ = 1) (c : Fin 3) :
    (Measure.pi fun _ : W => blockMeasure)
      {ω : W → BlockSample | dot2 (normVec c) (edgeVec2 Q q R ω e) = 0} = 0 := by
  set P := Measure.pi fun _ : W => blockMeasure
  let proj_n (ω : W → BlockSample) : W → ℝ := fun B' => dot2 (normVec c) (ω B').1
  have hmp_n : MeasurePreserving proj_n P (Measure.pi fun _ : W => gaussianReal 0 1) :=
    measurePreserving_pi _ _ fun _ =>
      (measurePreserving_dot2_unit (normVec_sq c)).comp
        (MeasureTheory.measurePreserving_fst (μ := gauss2) (ν := gaussTie))
  have hpre : {ω | dot2 (normVec c) (edgeVec2 Q q R ω e) = 0} =
      proj_n ⁻¹' {g : W → ℝ | ⟪edgeVector Q q R e, WithLp.toLp 2 g⟫ = 0} := by
    ext ω; simp [proj_n, dot2_edgeVec2, edgeScore]
  have hm : MeasurableSet {g : W → ℝ | ⟪edgeVector Q q R e, WithLp.toLp 2 g⟫ = 0} :=
    (isClosed_eq (by fun_prop) continuous_const).measurableSet
  have hz : P.real {ω | dot2 (normVec c) (edgeVec2 Q q R ω e) = 0} = 0 := by
    rw [hpre, hmp_n.measureReal_preimage hm.nullMeasurableSet]
    exact measureReal_pi_gaussianReal_inner_eq_zero hunit
  rw [measureReal_def, ENNReal.toReal_eq_zero_iff] at hz
  exact hz.resolve_right (measure_ne_top _ _)

end QuotientColoring

end Cslib.Circuits.Frontier.TensorRank
