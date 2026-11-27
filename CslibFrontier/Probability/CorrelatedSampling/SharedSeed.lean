/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StatisticalDistance
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.ProductMeasure
import CslibFrontier.Probability.PMF.ToReal
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Correlated sampling from a distribution-independent seed

Two parties hold distributions `P` and `Q` on a finite set `S` and share randomness, but do not
communicate. Holenstein's protocol [Holenstein, §5, Figure 1 and the proof of Lemma 5.2,
pp. 152–153][Holenstein2009] gives them a shared
sequence of independent uniform points `(x_n, u_n)` of `S × [0, 1]` (`seed`). Each party outputs
the first `x_n` with `u_n < P (x_n)`, the first point under the graph of its own distribution
(`seedSample`). The law of the seed depends only on `S`, not on `P` or `Q`, and each party
computes its output from the seed and its own distribution alone.

The first point of an i.i.d. sequence that lies in a set `R` of positive probability is
distributed as one point conditioned on `R` (`map_firstHit`). For the region under the graph of
`P`, that point's first coordinate has law `P` (`map_seedSample`). If the first point under the
graph of `max P Q` lies under the graph of `min P Q`, it is also the first point under each graph,
and both parties output it. The two regions have areas `(1 + δ) / |S|` and `(1 - δ) / |S|`, where
`δ` is the statistical distance, so the outputs differ with probability at most
`2δ / (1 + δ) ≤ 2δ` (`seedSample_disagree_le`).

The library's finite correlated sampling (`Cslib.Probability.CorrelatedSampling.shared`) proves the
same bounds from a seed whose law is built from the whole family of distributions. This file is
Holenstein's protocol itself, with the seed fixed in advance.

The statement of the seed's independence and of both bounds follows Holenstein: the infinite
product and the strict acceptance predicate are his sampling step (Figure 1), and conditioning the
first hit in the union gives his min/max ratio (proof of Lemma 5.2) before weakening to `2δ`. The
formal proof route through `firstHit` is original (cslib-frontier issue #6718). The results here
concern two finite-alphabet distributions; they do not assert Holenstein's full embedding lemma.

## Main definitions

* `Cslib.Probability.CorrelatedSampling.firstHit`: the first entry of a sequence in a set.
* `Cslib.Probability.CorrelatedSampling.seed`: Holenstein's shared sequence of uniform points of
  `S × [0, 1]`.
* `Cslib.Probability.CorrelatedSampling.seedSample`: a party's output, read off the seed using only
  its own distribution.

## Main results

* `Cslib.Probability.CorrelatedSampling.map_firstHit`: the first entry in `R` of an i.i.d. sequence
  is distributed as one entry conditioned on `R`.
* `Cslib.Probability.CorrelatedSampling.map_seedSample`: each party outputs a sample of its own
  distribution.
* `Cslib.Probability.CorrelatedSampling.seedSample_disagree_le`: the two outputs differ with
  probability at most `2δ`.

## Implementation notes

The seed is an infinite sequence, so it is a `Measure` on `ℕ → S × unitInterval`, not a `PMF`.
When no point of the sequence lies under the graph of its distribution, a party outputs a fixed
default element. Both parties use the same default, so they agree when neither has a hit. If only
one party has no hit, it returns the default while the other may return a different element. For
each fixed distribution the no-hit event has measure zero (`infinitePi_forall_notMem`), and the
disagreement bound accounts for it: it bounds the event that the first point under the graph of
`max P Q` is not under the graph of `min P Q`, which contains every disagreement.

The alphabet carries a measurable structure with measurable singletons
(`MeasurableSingletonClass`), so that the graph regions are measurable.

## References

* [T. Holenstein, *Parallel repetition: simplifications and the no-signaling case*][Holenstein2009]
-/

public section

namespace Cslib.Probability.CorrelatedSampling

open MeasureTheory Finset ProbabilityTheory
open scoped ENNReal unitInterval

/-! ### The first entry of a sequence in a set -/

section FirstHit

variable {β : Type*}

/-- The event that the first entry of `ω` in `R` has index `n` and lies in `B`. -/
private def hitAt (R B : Set β) (n : ℕ) : Set (ℕ → β) := {ω | (∀ i < n, ω i ∉ R) ∧ ω n ∈ B ∩ R}

open Classical in
/-- The first entry of `ω` in `R`, or `d` if no entry lies in `R`. -/
noncomputable def firstHit (R : Set β) (d : β) (ω : ℕ → β) : β :=
  if h : ∃ n, ω n ∈ R then ω (Nat.find h) else d

/-- When some entry lies in `R`, the first one lies in `B` exactly when the first entry in `R`
occurs at some index and lies in `B`. -/
private theorem firstHit_mem_iff {R : Set β} {d : β} {ω : ℕ → β} (h : ∃ n, ω n ∈ R) (B : Set β) :
    firstHit R d ω ∈ B ↔ ∃ n, ω ∈ hitAt R B n := by
  classical
  rw [firstHit, dite_eq_left h]
  constructor
  · intro hB
    exact ⟨Nat.find h, fun i hi => Nat.find_min h hi, hB, Nat.find_spec h⟩
  · rintro ⟨n, hlt, hB, hR⟩
    have hn : Nat.find h = n :=
      le_antisymm (Nat.find_min' h hR) (not_lt.1 fun hlt' => hlt _ hlt' (Nat.find_spec h))
    rwa [hn]

theorem firstHit_of_forall_notMem {R : Set β} {d : β} {ω : ℕ → β} (h : ∀ n, ω n ∉ R) :
    firstHit R d ω = d := by
  classical
  rw [firstHit, dite_eq_right fun ⟨n, hn⟩ => h n hn]

/-- If the first entry in `R'` lies in a subset `R`, it is also the first entry in `R`. -/
theorem firstHit_eq_of_subset {R R' : Set β} (hRR' : R ⊆ R') {d : β} {ω : ℕ → β}
    (h' : ∃ n, ω n ∈ R') (hR : firstHit R' d ω ∈ R) : firstHit R d ω = firstHit R' d ω := by
  obtain ⟨n, hlt, hnR, -⟩ := (firstHit_mem_iff h' R).1 hR
  have e : firstHit R d ω = ω n :=
    (firstHit_mem_iff ⟨n, hnR⟩ {ω n}).2 ⟨n, fun i hi hiR => hlt i hi (hRR' hiR), rfl, hnR⟩
  have e' : firstHit R' d ω = ω n := (firstHit_mem_iff h' {ω n}).2 ⟨n, hlt, rfl, hRR' hnR⟩
  rw [e, e']

private theorem preimage_firstHit (R : Set β) (d : β) (B : Set β) :
    firstHit R d ⁻¹' B = (⋃ n, hitAt R B n) ∪ {ω | (∀ n, ω n ∉ R) ∧ d ∈ B} := by
  ext ω
  simp only [Set.mem_preimage, Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq]
  by_cases h : ∃ n, ω n ∈ R
  · rw [firstHit_mem_iff h]
    obtain ⟨n, hn⟩ := h
    exact ⟨Or.inl, fun h' => h'.resolve_right fun h'' => h''.1 n hn⟩
  · push Not at h
    rw [firstHit_of_forall_notMem h]
    exact ⟨fun hd => Or.inr ⟨h, hd⟩, fun h' => h'.elim (fun ⟨n, hn⟩ => (h n hn.2.2).elim)
      And.right⟩

private theorem pairwise_disjoint_hitAt (R B : Set β) :
    Pairwise (Function.onFun Disjoint (hitAt R B)) := by
  intro n m hnm
  rw [Function.onFun, Set.disjoint_left]
  rintro ω ⟨hn, -, hnR⟩ ⟨hm, -, hmR⟩
  rcases lt_or_gt_of_ne hnm with h | h
  · exact hm n h hnR
  · exact hn m h hmR

private theorem hitAt_eq_pi (R B : Set β) (n : ℕ) :
    hitAt R B n = Set.pi (range (n + 1) : Set ℕ) fun i => if i < n then Rᶜ else B ∩ R := by
  ext ω
  simp only [hitAt, Set.mem_ofPred_eq, Set.mem_pi, coe_range, Set.mem_Iio]
  constructor
  · rintro ⟨h, hn⟩ i hi
    split_ifs with hin
    · exact h i hin
    · rwa [show i = n by omega]
  · intro h
    refine ⟨fun i hi => ?_, ?_⟩
    · simpa [hi] using h i (by omega)
    · simpa using h n (by omega)

variable [MeasurableSpace β]

private theorem measurableSet_hitAt {R B : Set β} (hR : MeasurableSet R) (hB : MeasurableSet B)
    (n : ℕ) :
    MeasurableSet (hitAt R B n) := by
  rw [hitAt_eq_pi]
  refine MeasurableSet.pi (Set.to_countable _) fun i _ => ?_
  split_ifs
  · exact hR.compl
  · exact hB.inter hR

theorem measurable_firstHit {R : Set β} (hR : MeasurableSet R) (d : β) :
    Measurable (firstHit R d) := by
  intro B hB
  rw [preimage_firstHit]
  refine (MeasurableSet.iUnion fun n => measurableSet_hitAt hR hB n).union ?_
  by_cases hd : d ∈ B
  · simp only [hd, and_true, Set.ofPred_forall]
    exact MeasurableSet.iInter fun n =>
      (measurable_pi_apply n hR.compl : MeasurableSet ((fun ω : ℕ → β => ω n) ⁻¹' Rᶜ))
  · simp only [hd, and_false, Set.ofPred_false, MeasurableSet.empty]

variable (μ : Measure β) [IsProbabilityMeasure μ]

private theorem infinitePi_hitAt {R B : Set β} (hR : MeasurableSet R) (hB : MeasurableSet B)
    (n : ℕ) :
    Measure.infinitePi (fun _ : ℕ => μ) (hitAt R B n) = μ Rᶜ ^ n * μ (B ∩ R) := by
  rw [hitAt_eq_pi, Measure.infinitePi_pi _ fun i _ => ?_, prod_range_succ,
    ite_eq_right (lt_irrefl n), prod_congr rfl (g := fun _ => μ Rᶜ) fun i hi => by
      rw [ite_eq_left (mem_range.1 hi)], prod_const, card_range]
  split_ifs
  · exact hR.compl
  · exact hB.inter hR

private theorem infinitePi_iUnion_hitAt {R B : Set β} (hR : MeasurableSet R)
    (hB : MeasurableSet B) :
    Measure.infinitePi (fun _ : ℕ => μ) (⋃ n, hitAt R B n) = (μ R)⁻¹ * μ (R ∩ B) := by
  rw [measure_iUnion (pairwise_disjoint_hitAt R B) (measurableSet_hitAt hR hB),
    tsum_congr (infinitePi_hitAt μ hR hB), ENNReal.tsum_mul_right, ENNReal.tsum_geometric,
    prob_compl_eq_one_sub hR, ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one,
    Set.inter_comm]

/-- Almost surely some entry of an i.i.d. sequence lies in a set of positive probability. -/
theorem infinitePi_forall_notMem {R : Set β} (hR : MeasurableSet R) (h0 : μ R ≠ 0) :
    Measure.infinitePi (fun _ : ℕ => μ) {ω | ∀ n, ω n ∉ R} = 0 := by
  have hc : {ω : ℕ → β | ∀ n, ω n ∉ R} = (⋃ n, hitAt R Set.univ n)ᶜ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    constructor
    · rintro h n ⟨-, -, hn⟩
      exact h n hn
    · intro h n hn
      obtain ⟨m, hm⟩ := (firstHit_mem_iff (d := ω 0) ⟨n, hn⟩ Set.univ).1 (Set.mem_univ _)
      exact h m hm
  rw [hc, prob_compl_eq_one_sub (MeasurableSet.iUnion fun n => measurableSet_hitAt hR .univ n),
    infinitePi_iUnion_hitAt μ hR .univ, Set.inter_univ,
    ENNReal.inv_mul_cancel h0 (measure_ne_top _ _), tsub_self]

/-- **The first entry in a set.** In an i.i.d. sequence with law `μ`, the first entry in a set `R`
of positive probability is distributed as `μ` conditioned on `R`. -/
theorem map_firstHit {R : Set β} (hR : MeasurableSet R) (h0 : μ R ≠ 0) (d : β) :
    (Measure.infinitePi fun _ : ℕ => μ).map (firstHit R d) = μ[|R] := by
  ext B hB
  rw [Measure.map_apply (measurable_firstHit hR d) hB, cond_apply hR]
  refine le_antisymm ?_ ?_
  · rw [preimage_firstHit, ← infinitePi_iUnion_hitAt μ hR hB]
    refine (measure_union_le _ _).trans ?_
    rw [measure_mono_null (fun ω (hω : ω ∈ {ω : ℕ → β | (∀ n, ω n ∉ R) ∧ d ∈ B}) => hω.1)
      (infinitePi_forall_notMem μ hR h0), add_zero]
  · rw [← infinitePi_iUnion_hitAt μ hR hB, preimage_firstHit]
    exact measure_mono Set.subset_union_left

end FirstHit

/-! ### Holenstein's protocol -/

section Holenstein

variable (S : Type*) [Fintype S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]

/-- One point of Holenstein's shared sequence: a uniform point of `S × [0, 1]`. -/
noncomputable def seedPoint : Measure (S × I) := (PMF.uniformOfFintype S).toMeasure.prod volume

instance : IsProbabilityMeasure (seedPoint S) := by
  unfold seedPoint
  infer_instance

/-- **Holenstein's shared seed**: a sequence of independent uniform points of `S × [0, 1]`. Its
law depends only on `S`, not on the parties' distributions. -/
noncomputable def seed : Measure (ℕ → S × I) := Measure.infinitePi fun _ => seedPoint S

instance : IsProbabilityMeasure (seed S) := by
  unfold seed
  infer_instance

variable {S}

/-- The points of `S × [0, 1]` strictly under the graph of `t`. -/
def underGraph (t : S → ℝ) : Set (S × I) := {p | (p.2 : ℝ) < t p.1}

open Classical in
/-- **A party's output** in Holenstein's protocol: the first point of the seed under the graph of
its own distribution `P`, or a fixed default when there is none. -/
noncomputable def seedSample (P : PMF S) (ω : ℕ → S × I) : S :=
  (firstHit (underGraph fun s => (P s).toReal) (Classical.arbitrary S, 0) ω).1

omit [Fintype S] [Nonempty S] in
theorem measurableSet_underGraph [Finite S] (t : S → ℝ) : MeasurableSet (underGraph t) :=
  measurableSet_lt (measurable_subtype_coe.comp measurable_snd)
    ((measurable_of_countable t).comp measurable_fst)

omit [Fintype S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S] in
private theorem underGraph_mono {t t' : S → ℝ} (h : t ≤ t') : underGraph t ⊆ underGraph t' := by
  intro p hp
  simp only [underGraph, Set.mem_ofPred_eq] at hp ⊢
  exact hp.trans_le (h _)

/-- The region under the graph of `t` has area `(∑ s, t s) / |S|`. -/
theorem seedPoint_underGraph {t : S → ℝ} (h0 : ∀ s, 0 ≤ t s) (h1 : ∀ s, t s ≤ 1) :
    seedPoint S (underGraph t) = (∑ s, ENNReal.ofReal (t s)) * (Fintype.card S : ℝ≥0∞)⁻¹ := by
  rw [seedPoint, Measure.prod_apply (measurableSet_underGraph t), lintegral_fintype, sum_mul]
  refine sum_congr rfl fun s _ => ?_
  have hslice : Prod.mk s ⁻¹' underGraph t = Set.Iio (⟨t s, h0 s, h1 s⟩ : I) := by
    ext u
    simp [underGraph, ← Subtype.coe_lt_coe]
  rw [hslice, unitInterval.volume_Iio,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton s), PMF.uniformOfFintype_apply]

private theorem seedPoint_real_underGraph {t : S → ℝ} (h0 : ∀ s, 0 ≤ t s) (h1 : ∀ s, t s ≤ 1) :
    (seedPoint S).real (underGraph t) = (∑ s, t s) / Fintype.card S := by
  rw [measureReal_def, seedPoint_underGraph h0 h1, ENNReal.toReal_mul,
    ENNReal.toReal_sum fun _ _ => ENNReal.ofReal_ne_top, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, div_eq_mul_inv]
  congr 1
  exact sum_congr rfl fun s _ => ENNReal.toReal_ofReal (h0 s)

omit [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S] in
private theorem sum_ofReal_toReal (P : PMF S) : ∑ s, ENNReal.ofReal (P s).toReal = 1 := by
  simp_rw [ENNReal.ofReal_toReal (P.apply_ne_top _)]
  simpa [tsum_fintype] using P.tsum_coe

private theorem seedPoint_underGraph_ne_zero (P : PMF S) :
    seedPoint S (underGraph fun s => (P s).toReal) ≠ 0 := by
  rw [seedPoint_underGraph (fun _ => ENNReal.toReal_nonneg)
    (fun _ => Cslib.Probability.PMF.toReal_apply_le_one P _), sum_ofReal_toReal, one_mul]
  exact ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _)

omit [Fintype S] in
theorem measurable_seedSample [Finite S] (P : PMF S) : Measurable (seedSample P) :=
  measurable_fst.comp (measurable_firstHit (measurableSet_underGraph _) _)

/-- **Holenstein's protocol, marginals** [Holenstein, §5, Figure 1 and the proof of Lemma 5.2,
pp. 152–153][Holenstein2009]. A party reading
the shared seed with its own distribution `P` outputs a sample of `P`. -/
theorem map_seedSample (P : PMF S) : (seed S).map (seedSample P) = P.toMeasure := by
  set t : S → ℝ := fun s => (P s).toReal
  have h0 : ∀ s, 0 ≤ t s := fun _ => ENNReal.toReal_nonneg
  have h1 : ∀ s, t s ≤ 1 := fun _ => Cslib.Probability.PMF.toReal_apply_le_one P _
  have hmap : seedSample P = Prod.fst ∘ firstHit (underGraph t) (Classical.arbitrary S, 0) := rfl
  refine Measure.ext_of_singleton fun s => ?_
  rw [hmap, ← Measure.map_map measurable_fst
      (measurable_firstHit (measurableSet_underGraph t) _), seed,
    map_firstHit _ (measurableSet_underGraph t) (seedPoint_underGraph_ne_zero P),
    Measure.map_apply measurable_fst (measurableSet_singleton s),
    cond_apply (measurableSet_underGraph t), PMF.toMeasure_apply_singleton _ _
      (measurableSet_singleton s)]
  classical
  have hslice : underGraph t ∩ Prod.fst ⁻¹' {s} = underGraph fun x => if x = s then t x else 0 := by
    ext ⟨x, u⟩
    by_cases hx : x = s
    · simp [underGraph, hx]
    · simpa [underGraph, hx] using u.2.1
  have hn : (Fintype.card S : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hn' : (Fintype.card S : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [hslice, seedPoint_underGraph h0 h1, seedPoint_underGraph (fun x => by split_ifs <;> simp [h0])
      (fun x => by split_ifs <;> simp [h1]), sum_ofReal_toReal, one_mul,
    inv_inv, mul_left_comm, ENNReal.mul_inv_cancel hn hn', mul_one]
  rw [sum_eq_single s (fun b _ hb => by simp [hb]) (by simp)]
  simp [t, ENNReal.ofReal_toReal (P.apply_ne_top s)]

open scoped Cslib.Probability.PMF in
/-- **Holenstein's protocol, disagreement** [Holenstein, §5, Figure 1 and the proof of Lemma 5.2,
pp. 152–153][Holenstein2009]. Two parties reading the same shared seed with their own
distributions `P` and `Q` output different elements with probability at most `2δ`, where `δ` is
the statistical distance between `P` and `Q`. Conditioning the first point under the graph of
`max P Q` gives the disagreement bound `2δ / (1 + δ)`, the complement of Holenstein's agreement
ratio `(1 - δ) / (1 + δ)` (p. 153), which is then weakened to `2δ`. A disagreement
in which only one party finds no point under its graph is included in the bounded event. -/
theorem seedSample_disagree_le (P Q : PMF S) :
    (seed S).real {ω | seedSample P ω ≠ seedSample Q ω} ≤ 2 * dist P Q := by
  set tP : S → ℝ := fun s => (P s).toReal
  set tQ : S → ℝ := fun s => (Q s).toReal
  set d : S × I := (Classical.arbitrary S, 0)
  set U := underGraph (tP ⊔ tQ)
  set M := underGraph (tP ⊓ tQ)
  have hPU : underGraph tP ⊆ U := underGraph_mono le_sup_left
  have hQU : underGraph tQ ⊆ U := underGraph_mono le_sup_right
  have hMP : M ⊆ underGraph tP := underGraph_mono inf_le_left
  have hMQ : M ⊆ underGraph tQ := underGraph_mono inf_le_right
  have hMU : M ⊆ U := hMP.trans hPU
  -- The outputs can differ only if the first point under `max P Q` is not under `min P Q`.
  have hsub : {ω | seedSample P ω ≠ seedSample Q ω} ⊆ firstHit U d ⁻¹' Mᶜ := by
    intro ω hne hM
    refine hne ?_
    by_cases h : ∃ n, ω n ∈ U
    · change (firstHit (underGraph tP) d ω).1 = (firstHit (underGraph tQ) d ω).1
      rw [firstHit_eq_of_subset hPU h (hMP hM), firstHit_eq_of_subset hQU h (hMQ hM)]
    · push Not at h
      change (firstHit (underGraph tP) d ω).1 = (firstHit (underGraph tQ) d ω).1
      rw [firstHit_of_forall_notMem fun n hn => h n (hPU hn),
        firstHit_of_forall_notMem fun n hn => h n (hQU hn)]
  have hU0 : seedPoint S U ≠ 0 := fun h =>
    seedPoint_underGraph_ne_zero P (measure_mono_null hPU h)
  have hprob : (seed S).real (firstHit U d ⁻¹' Mᶜ) =
      ((seedPoint S).real U - (seedPoint S).real M) / (seedPoint S).real U := by
    rw [measureReal_def, ← Measure.map_apply (measurable_firstHit (measurableSet_underGraph _) d)
        (measurableSet_underGraph _).compl, seed,
      map_firstHit _ (measurableSet_underGraph _) hU0, cond_apply (measurableSet_underGraph _),
      ENNReal.toReal_mul, ENNReal.toReal_inv, ← Set.sdiff_eq,
      ← measureReal_def, ← measureReal_def, measureReal_sdiff hMU (measurableSet_underGraph _),
      div_eq_inv_mul]
  have h0 : ∀ s, 0 ≤ tP s := fun _ => ENNReal.toReal_nonneg
  have h0' : ∀ s, 0 ≤ tQ s := fun _ => ENNReal.toReal_nonneg
  have h1 : ∀ s, tP s ≤ 1 := fun _ => Cslib.Probability.PMF.toReal_apply_le_one P _
  have h1' : ∀ s, tQ s ≤ 1 := fun _ => Cslib.Probability.PMF.toReal_apply_le_one Q _
  have hUr : (seedPoint S).real U = (1 + dist P Q) / Fintype.card S := by
    rw [seedPoint_real_underGraph (t := tP ⊔ tQ) (fun s => le_max_of_le_left (h0 s))
      (fun s => max_le (h1 s) (h1' s))]
    exact congrArg (· / _) (Cslib.Probability.PMF.sum_max_toReal P Q)
  have hMr : (seedPoint S).real M = (1 - dist P Q) / Fintype.card S := by
    rw [seedPoint_real_underGraph (t := tP ⊓ tQ) (fun s => le_min (h0 s) (h0' s))
      (fun s => min_le_of_left_le (h1 s))]
    exact congrArg (· / _) (Cslib.Probability.PMF.sum_min_toReal P Q)
  have hδ : 0 ≤ dist P Q := dist_nonneg
  have hn : (0 : ℝ) < Fintype.card S := Nat.cast_pos.2 Fintype.card_pos
  refine (measureReal_mono hsub).trans ?_
  rw [hprob, hUr, hMr, ← sub_div, div_div_div_cancel_right₀ hn.ne']
  calc (1 + dist P Q - (1 - dist P Q)) / (1 + dist P Q) = 2 * dist P Q / (1 + dist P Q) := by ring
    _ ≤ 2 * dist P Q := div_le_self (by positivity) (by linarith)

end Holenstein

end Cslib.Probability.CorrelatedSampling
