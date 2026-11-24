/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.PACLearning.RealizableSample
public import CslibFrontier.MachineLearning.PACLearning.VCDimension
import CslibFrontier.MachineLearning.PACLearning.DualVCDimension
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fintype.Pi
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The One-Inclusion Graph Predictor and Transductive Error Bound

For a binary concept class `C : ConceptClass α Bool` of VC dimension `d`, empirical risk
minimization requires `Ω((d log (1 / ε)) / ε)` examples in the worst case. Haussler, Littlestone,
and Warmuth [HausslerLittlestoneWarmuth1994] removed the `log (1 / ε)` factor in expectation using
the **one-inclusion graph** (the induced subgraph of the Boolean hypercube on the labelings `C`
realizes on the `m + 1` observed and test points):

1. **Subgraph density bound** (`card_oneInclusionEdges_le_mul_card`, Lemma 2.4 (locator
   unverified)): if every finite shattered set of `S : Finset (ι → Bool)` has size at most `d`,
   then the one-inclusion graph of `S` has at most `d * |S|` edges.
2. **Bounded-outdegree orientation** (`exists_orientation_outdegree_le`, §2.3 (locator unverified)
   / Hakimi's theorem via Hall's marriage theorem): every induced subgraph `U ⊆ S` has at most
   `d * |U|` edges, so the edges of `S` can be oriented so that every vertex has outdegree at most
   `d`.
3. **Leave-one-out transductive bound** (`card_leaveOneOut_mistakes_le`, Theorem 2.3 (locator
   unverified)): the parameter-free improper predictor `oneInclusionLearner C` orients the
   one-inclusion graph on the unordered point set of `m` labeled training examples plus one
   unlabeled test point, predicting toward edge heads (and reusing the observed label on duplicate
   points). On any realizable sample of length `m + 1`, `oneInclusionLearner C` errs on at most `d`
   of the `m + 1` leave-one-out folds.
4. **Expected generalization error and `O(d / (ε δ))` PAC learning**
   (`lintegral_error_oneInclusionLearner_le`, `isPACLearnerFor_oneInclusionLearner`,
   `sampleComplexity_realizableDistributions_le_div_vcDim`):
   by exchangeability of `D ^ (m + 1)`, `oneInclusionLearner C` achieves expected true error at
   most `d / (m + 1)` (with exact constant `1` and no logarithmic factors), yielding an `(ε, δ)`-PAC
   learner whenever `d ≤ ε δ (m + 1)`. At fixed confidence `δ`, this achieves the optimal `O(d / ε)`
   dependence in `ε` matching Ehrenfeucht–Haussler–Kearns–Valiant [EHKV1989].

## Main definitions

- `oneInclusionEdges S`: canonical edges `(i, f)` of the one-inclusion graph of
  `S : Finset (ι → Bool)`, pairing coordinate `i : ι` with the `false`-endpoint `f ∈ S` whose
  `i`-flip `Function.update f i true` also lies in `S`.
- `tailEndpoint orient e`, `oneInclusionOutdegree S orient g`: tail endpoint and vertex outdegree
  under an edge orientation `orient : (ι × (ι → Bool)) → Bool`.
- `oneInclusionLearner C`: the parameter-free one-inclusion graph batch learner `Learner α Bool m`.

## Main results

- `card_oneInclusionEdges_le_mul_card`: `(oneInclusionEdges S).card ≤ d * S.card` when `S` shatters
  no finite set of more than `d` coordinates.
- `exists_orientation_outdegree_le`: existence of an orientation with maximum outdegree at most `d`.
- `oneInclusionLearner_apply_sample_of_realizable`, `oneInclusionLearner_eq_of_forall_consistent`:
  exact sample-consistency on realizable training data and unanimous-extension characterization.
- `card_leaveOneOut_mistakes_le`: on any realizable `(m + 1)`-sample, `oneInclusionLearner C` errs
  on at most `d` of the `m + 1` leave-one-out folds.
- `lintegral_error_oneInclusionLearner_le`: `𝔼[error D (oneInclusionLearner C S)] ≤ d / (m + 1)`.
- `isPACLearnerFor_oneInclusionLearner`, `sampleComplexity_realizableDistributions_le_div_vcDim`:
  realizable `(ε, δ)`-PAC learning for `d ≤ ε δ (m + 1)` and sample complexity at most
  `⌈vcDim C / (ε δ)⌉₊` on countable domains with measurable singletons.

## References

* [D. Haussler, N. Littlestone, M. K. Warmuth, *Predicting `{0, 1}`-Functions on Randomly Drawn
  Points*][HausslerLittlestoneWarmuth1994]
-/

public section

open Finset MeasureTheory
open scoped ENNReal NNReal

namespace Cslib.MachineLearning.PACLearning

variable {α ι : Type*}

/-! ### 1. The one-inclusion graph and the `d * |S|` edge-density bound -/

/-- Canonical undirected edges `(i, f)` of the one-inclusion graph of `S : Finset (ι → Bool)`:
coordinate `i : ι` paired with the lower endpoint `f ∈ S` (`f i = false`) whose `i`-flip
`Function.update f i true` also belongs to `S` [HausslerLittlestoneWarmuth1994]. -/
def oneInclusionEdges [DecidableEq ι] [Fintype ι] (S : Finset (ι → Bool)) :
    Finset (ι × (ι → Bool)) :=
  (Finset.univ ×ˢ S).filter fun e => e.2 e.1 = false ∧ Function.update e.2 e.1 true ∈ S

@[simp]
theorem mem_oneInclusionEdges [DecidableEq ι] [Fintype ι] {S : Finset (ι → Bool)}
    {e : ι × (ι → Bool)} :
    e ∈ oneInclusionEdges S ↔
      e.2 ∈ S ∧ e.2 e.1 = false ∧ Function.update e.2 e.1 true ∈ S := by
  simp only [oneInclusionEdges, mem_filter, mem_product, mem_univ, true_and]

theorem oneInclusionEdges_mono [DecidableEq ι] [Fintype ι] {S₁ S₂ : Finset (ι → Bool)}
    (h : S₁ ⊆ S₂) : oneInclusionEdges S₁ ⊆ oneInclusionEdges S₂ := by
  intro e he
  rcases mem_oneInclusionEdges.mp he with ⟨h1, h2, h3⟩
  exact mem_oneInclusionEdges.mpr ⟨h h1, h2, h h3⟩

private theorem setShatters_image_succ {n : ℕ} {S : Set (Fin (n + 1) → Bool)} {W : Set (Fin n)}
    (hW : SetShatters (Fin.tail '' S) W) : SetShatters S (Fin.succ '' W) :=
  SetShatters.image_of_comp hW

private theorem setShatters_insert_zero {n : ℕ} {S : Set (Fin (n + 1) → Bool)} {W : Set (Fin n)}
    (hW : SetShatters {g | Fin.cons false g ∈ S ∧ Fin.cons true g ∈ S} W) :
    SetShatters S (insert 0 (Fin.succ '' W)) := by
  classical
  intro T hT
  obtain ⟨g, ⟨hg0, hg1⟩, hgT⟩ := hW (W ∩ Fin.succ ⁻¹' T) Set.inter_subset_left
  let b : Bool := decide ((0 : Fin (n + 1)) ∈ T)
  refine ⟨Fin.cons b g, by cases hb : b <;> [exact hg0; exact hg1], Set.ext fun x => ?_⟩
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
  rcases Fin.eq_zero_or_eq_succ x with rfl | ⟨i, rfl⟩
  · simp [b]
  · constructor
    · rintro ⟨hgi, hxins⟩
      simp only [Fin.cons_succ] at hgi
      have hiW : i ∈ W := by
        rcases hxins with h0 | ⟨j, hj, hji⟩
        · exact absurd h0 (Fin.succ_ne_zero i)
        · rwa [Fin.succ_inj.mp hji] at hj
      have hmem : i ∈ g ⁻¹' {true} ∩ W := ⟨hgi, hiW⟩
      rw [hgT] at hmem
      exact hmem.2
    · intro hiT
      have hiW : i ∈ W := by
        rcases hT hiT with h0 | ⟨j, hj, hji⟩
        · exact absurd h0 (Fin.succ_ne_zero i)
        · rwa [Fin.succ_inj.mp hji] at hj
      have hmem : i ∈ g ⁻¹' {true} ∩ W := hgT ▸ ⟨hiW, hiT⟩
      exact ⟨by simpa only [Fin.cons_succ, Set.mem_preimage, Set.mem_singleton_iff] using hmem.1,
        Or.inr ⟨i, hiW, rfl⟩⟩

private theorem card_oneInclusionEdges_fin_le :
    ∀ {n d : ℕ} {S : Finset (Fin n → Bool)},
      (∀ W : Finset (Fin n), SetShatters (S : Set (Fin n → Bool)) ↑W → W.card ≤ d) →
      (oneInclusionEdges S).card ≤ d * S.card
  | 0, d, S, _ => by
    have hemp : oneInclusionEdges S = ∅ := eq_empty_of_forall_notMem fun e _ => Fin.elim0 e.1
    simp [hemp]
  | n + 1, d, S, hS => by
    classical
    let S₀ : Finset (Fin n → Bool) := Finset.univ.filter fun g => Fin.cons false g ∈ S
    let S₁ : Finset (Fin n → Bool) := Finset.univ.filter fun g => Fin.cons true g ∈ S
    have hcard_b : ∀ b : Bool,
        (S.filter fun f => f 0 = b).card =
          (Finset.univ.filter fun g : Fin n → Bool => Fin.cons b g ∈ S).card := by
      intro b
      refine card_bij (fun f _ => Fin.tail f) ?_ ?_ ?_
      · intro f hf
        rcases mem_filter.mp hf with ⟨hfS, hf0⟩
        rw [mem_filter]
        refine ⟨mem_univ _, ?_⟩
        have hcons : Fin.cons b (Fin.tail f) = f := by
          rw [← hf0, Fin.cons_self_tail]
        rwa [hcons]
      · intro f₁ h₁ f₂ h₂ htail
        have hf₁ : Fin.cons b (Fin.tail f₁) = f₁ := by
          rw [← (mem_filter.mp h₁).2, Fin.cons_self_tail]
        have hf₂ : Fin.cons b (Fin.tail f₂) = f₂ := by
          rw [← (mem_filter.mp h₂).2, Fin.cons_self_tail]
        rw [← hf₁, ← hf₂, htail]
      · intro g hg
        exact ⟨Fin.cons b g, mem_filter.mpr ⟨(mem_filter.mp hg).2, rfl⟩,
          by simp [Fin.tail_cons]⟩
    have hScard : S.card = (S₀ ∪ S₁).card + (S₀ ∩ S₁).card := by
      have hsplit := card_filter_add_card_filter_not (s := S) (fun f => f 0 = false)
      have hnot : (S.filter fun f => ¬ f 0 = false) = S.filter fun f => f 0 = true := by
        congr 1; ext f; cases f 0 <;> simp
      rw [hnot, hcard_b false, hcard_b true] at hsplit
      exact hsplit.symm.trans (card_union_add_card_inter S₀ S₁).symm
    -- Count edges along coordinate `0`.
    have hedge0 : ((oneInclusionEdges S).filter fun e => e.1 = 0).card = (S₀ ∩ S₁).card := by
      refine card_bij (fun e _ => Fin.tail e.2) ?_ ?_ ?_
      · intro ⟨i, f⟩ he
        rcases mem_filter.mp he with ⟨heE, hi0⟩
        dsimp only at hi0
        subst hi0
        rcases mem_oneInclusionEdges.mp heE with ⟨hfS, hf0, hupdS⟩
        have hcons0 : Fin.cons false (Fin.tail f) = f := by
          rw [← hf0, Fin.cons_self_tail]
        have hcons1 : Fin.cons true (Fin.tail f) = Function.update f 0 true := by
          ext k
          rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨j, rfl⟩
          · simp
          · simp [Fin.tail]
        exact mem_inter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hcons0.symm ▸ hfS⟩,
          mem_filter.mpr ⟨mem_univ _, hcons1.symm ▸ hupdS⟩⟩
      · intro ⟨i₁, f₁⟩ h₁ ⟨i₂, f₂⟩ h₂ htail
        rcases mem_filter.mp h₁ with ⟨he₁, rfl⟩
        rcases mem_filter.mp h₂ with ⟨he₂, rfl⟩
        have hf₁ : Fin.cons false (Fin.tail f₁) = f₁ := by
          rw [← (mem_oneInclusionEdges.mp he₁).2.1, Fin.cons_self_tail]
        have hf₂ : Fin.cons false (Fin.tail f₂) = f₂ := by
          rw [← (mem_oneInclusionEdges.mp he₂).2.1, Fin.cons_self_tail]
        exact Prod.ext rfl (by rw [← hf₁, ← hf₂, htail])
      · intro g hg
        rcases mem_inter.mp hg with ⟨hg0, hg1⟩
        refine ⟨(0, Fin.cons false g), mem_filter.mpr ⟨mem_oneInclusionEdges.mpr
          ⟨(mem_filter.mp hg0).2, rfl, ?_⟩, rfl⟩, by simp [Fin.tail_cons]⟩
        have hupd : Function.update (Fin.cons false g : Fin (n + 1) → Bool) 0 true =
            Fin.cons true g := by
          ext k
          rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨j, rfl⟩ <;> simp
        rw [hupd]
        exact (mem_filter.mp hg1).2
    -- Count edges along coordinates `j.succ` with `f 0 = b`.
    have hedge_succ : ∀ b : Bool,
        ((oneInclusionEdges S).filter fun e => e.1 ≠ 0 ∧ e.2 0 = b).card =
          (oneInclusionEdges
            (Finset.univ.filter fun g : Fin n → Bool => Fin.cons b g ∈ S)).card := by
      intro b
      let Sb := Finset.univ.filter fun g : Fin n → Bool => Fin.cons b g ∈ S
      refine card_bij (fun e he => ((e.1).pred (mem_filter.mp he).2.1, Fin.tail e.2)) ?_ ?_ ?_
      · intro ⟨i, f⟩ he
        rcases mem_filter.mp he with ⟨heE, hi0, hfb⟩
        rcases mem_oneInclusionEdges.mp heE with ⟨hfS, hfi, hupdS⟩
        dsimp only at hi0 hfb hfS hfi hupdS ⊢
        have hcons : Fin.cons b (Fin.tail f) = f := by
          rw [← hfb, Fin.cons_self_tail]
        have hupd_eq : Fin.cons b (Function.update (Fin.tail f) (i.pred hi0) true) =
            Function.update f i true := by
          ext k
          rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨j, rfl⟩
          · simp [hfb, hi0.symm]
          · by_cases hji : j = i.pred hi0
            · subst hji
              simp [Fin.succ_pred]
            · have hki : j.succ ≠ i := fun h => hji <| Fin.ext <| by
                have hval := congrArg Fin.val h
                simp only [Fin.val_succ, Fin.val_pred] at hval ⊢
                omega
              simp [Fin.tail, hji, hki]
        refine mem_oneInclusionEdges.mpr ⟨mem_filter.mpr ⟨mem_univ _, hcons.symm ▸ hfS⟩, ?_,
          mem_filter.mpr ⟨mem_univ _, hupd_eq.symm ▸ hupdS⟩⟩
        simpa [Fin.tail, Fin.succ_pred] using hfi
      · intro ⟨i₁, f₁⟩ h₁ ⟨i₂, f₂⟩ h₂ heq
        rcases mem_filter.mp h₁ with ⟨_, hi₁, hfb₁⟩
        rcases mem_filter.mp h₂ with ⟨_, hi₂, hfb₂⟩
        rcases Prod.mk.inj heq with ⟨hip, htail⟩
        have hi_eq : i₁ = i₂ := by
          rw [← Fin.succ_pred i₁ hi₁, ← Fin.succ_pred i₂ hi₂, hip]
        have hf₁ : Fin.cons b (Fin.tail f₁) = f₁ := by rw [← hfb₁, Fin.cons_self_tail]
        have hf₂ : Fin.cons b (Fin.tail f₂) = f₂ := by rw [← hfb₂, Fin.cons_self_tail]
        exact Prod.ext hi_eq (by rw [← hf₁, ← hf₂, htail])
      · rintro ⟨j, g⟩ he
        rcases mem_oneInclusionEdges.mp he with ⟨hgSb, hgj, hupdSb⟩
        dsimp only at hgSb hgj hupdSb
        have hupd_cons : Function.update (Fin.cons b g : Fin (n + 1) → Bool) j.succ true =
            Fin.cons b (Function.update g j true) := by
          ext k
          rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k', rfl⟩
          · simp [(Fin.succ_ne_zero j).symm]
          · by_cases hkj : k' = j
            · subst hkj; simp
            · simp [hkj]
        refine ⟨(j.succ, Fin.cons b g), mem_filter.mpr ⟨mem_oneInclusionEdges.mpr
          ⟨(mem_filter.mp hgSb).2, by simpa using hgj, ?_⟩, Fin.succ_ne_zero j, rfl⟩, ?_⟩
        · rw [hupd_cons]
          exact (mem_filter.mp hupdSb).2
        · simp [Fin.tail_cons]
    have hedges_total :
        (oneInclusionEdges S).card =
          (S₀ ∩ S₁).card + (oneInclusionEdges S₀).card + (oneInclusionEdges S₁).card := by
      have hpart0 := card_filter_add_card_filter_not (s := oneInclusionEdges S) (fun e => e.1 = 0)
      have hpartb := card_filter_add_card_filter_not
        (s := (oneInclusionEdges S).filter fun e => ¬ e.1 = 0) (fun e => e.2 0 = false)
      rw [filter_filter, filter_filter] at hpartb
      have hnotb : ((oneInclusionEdges S).filter fun e => ¬ e.1 = 0 ∧ ¬ e.2 0 = false) =
          (oneInclusionEdges S).filter fun e => e.1 ≠ 0 ∧ e.2 0 = true := by
        congr 1; ext e; cases e.2 0 <;> simp
      have hedge_S0 : ((oneInclusionEdges S).filter fun e => ¬ e.1 = 0 ∧ e.2 0 = false).card =
          (oneInclusionEdges S₀).card := hedge_succ false
      have hedge_S1 : ((oneInclusionEdges S).filter fun e => e.1 ≠ 0 ∧ e.2 0 = true).card =
          (oneInclusionEdges S₁).card := hedge_succ true
      rw [hnotb, hedge_S0, hedge_S1] at hpartb
      rw [hedge0, ← hpartb] at hpart0
      omega
    have hedges_submod :
        (oneInclusionEdges S₀).card + (oneInclusionEdges S₁).card ≤
          (oneInclusionEdges (S₀ ∪ S₁)).card + (oneInclusionEdges (S₀ ∩ S₁)).card := by
      rw [← card_union_add_card_inter]
      have hinter : oneInclusionEdges S₀ ∩ oneInclusionEdges S₁ = oneInclusionEdges (S₀ ∩ S₁) := by
        ext e
        simp only [mem_inter, mem_oneInclusionEdges]
        tauto
      have hunion : oneInclusionEdges S₀ ∪ oneInclusionEdges S₁ ⊆
          oneInclusionEdges (S₀ ∪ S₁) :=
        union_subset (oneInclusionEdges_mono subset_union_left)
          (oneInclusionEdges_mono subset_union_right)
      rw [hinter]
      exact Nat.add_le_add_right (card_le_card hunion) _
    have hsh_union : ∀ W : Finset (Fin n),
        SetShatters (↑(S₀ ∪ S₁) : Set (Fin n → Bool)) ↑W → W.card ≤ d := by
      intro W hW
      have hsub : (↑(S₀ ∪ S₁) : Set (Fin n → Bool)) ⊆
          Fin.tail '' (S : Set (Fin (n + 1) → Bool)) := by
        intro g hg
        rcases mem_union.mp (mem_coe.mp hg) with hg0 | hg1
        · exact ⟨Fin.cons false g, (mem_filter.mp hg0).2, by simp [Fin.tail_cons]⟩
        · exact ⟨Fin.cons true g, (mem_filter.mp hg1).2, by simp [Fin.tail_cons]⟩
      have hsh' : SetShatters (S : Set (Fin (n + 1) → Bool)) ↑(W.map (Fin.succEmb n)) := by
        rw [coe_map]
        exact setShatters_image_succ (hW.superset hsub)
      simpa only [card_map] using hS _ hsh'
    have hsh_inter : ∀ W : Finset (Fin n),
        SetShatters (↑(S₀ ∩ S₁) : Set (Fin n → Bool)) ↑W → W.card + 1 ≤ d := by
      intro W hW
      have hsub : (↑(S₀ ∩ S₁) : Set (Fin n → Bool)) ⊆
          {g | Fin.cons false g ∈ S ∧ Fin.cons true g ∈ S} := by
        intro g hg
        rcases mem_inter.mp (mem_coe.mp hg) with ⟨hg0, hg1⟩
        exact ⟨(mem_filter.mp hg0).2, (mem_filter.mp hg1).2⟩
      have h0not : (0 : Fin (n + 1)) ∉ W.map (Fin.succEmb n) := by
        simp only [mem_map, Fin.coe_succEmb, not_exists, not_and]
        exact fun i _ => Fin.succ_ne_zero i
      have hsh' : SetShatters (S : Set (Fin (n + 1) → Bool))
          ↑(insert 0 (W.map (Fin.succEmb n))) := by
        rw [coe_insert, coe_map]
        exact setShatters_insert_zero (hW.superset hsub)
      have hcard := hS _ hsh'
      rwa [card_insert_of_notMem h0not, card_map] at hcard
    rcases d with _ | d
    · have hemp_inter : (S₀ ∩ S₁).card = 0 := by
        rw [card_eq_zero, ← not_nonempty_iff_eq_empty]
        intro ⟨g, hg⟩
        have hsh0 : SetShatters (↑(S₀ ∩ S₁) : Set (Fin n → Bool)) ↑(∅ : Finset (Fin n)) := by
          intro T hT
          have hTeq : T = ∅ := Set.subset_empty_iff.mp (by simpa using hT)
          subst hTeq
          exact ⟨g, hg, by simp⟩
        have := hsh_inter ∅ hsh0
        omega
      have hemp_edges_inter : (oneInclusionEdges (S₀ ∩ S₁)).card = 0 := by
        rw [card_eq_zero.mp hemp_inter]
        simp [oneInclusionEdges]
      have ih_u := card_oneInclusionEdges_fin_le (d := 0) hsh_union
      omega
    · have ih_u := card_oneInclusionEdges_fin_le (d := d + 1) hsh_union
      have ih_i := card_oneInclusionEdges_fin_le (d := d) fun W hW => by
        have := hsh_inter W hW; omega
      calc (oneInclusionEdges S).card
          = (S₀ ∩ S₁).card + ((oneInclusionEdges S₀).card + (oneInclusionEdges S₁).card) := by
            omega
        _ ≤ (S₀ ∩ S₁).card +
              ((oneInclusionEdges (S₀ ∪ S₁)).card + (oneInclusionEdges (S₀ ∩ S₁)).card) :=
            Nat.add_le_add_left hedges_submod _
        _ ≤ (S₀ ∩ S₁).card + ((d + 1) * (S₀ ∪ S₁).card + d * (S₀ ∩ S₁).card) :=
            Nat.add_le_add_left (Nat.add_le_add ih_u ih_i) _
        _ = (d + 1) * ((S₀ ∪ S₁).card + (S₀ ∩ S₁).card) := by ring
        _ = (d + 1) * S.card := by rw [← hScard]

/-- **Haussler–Littlestone–Warmuth subgraph edge-density bound**
[HausslerLittlestoneWarmuth1994, Lemma 2.4 (locator unverified)]: if `S : Finset (ι → Bool)`
shatters no finite set of more than `d` coordinates, then `(oneInclusionEdges S).card ≤ d * S.card`.
-/
theorem card_oneInclusionEdges_le_mul_card [DecidableEq ι] [Fintype ι] {d : ℕ}
    {S : Finset (ι → Bool)}
    (hS : ∀ W : Finset ι, SetShatters (S : Set (ι → Bool)) ↑W → W.card ≤ d) :
    (oneInclusionEdges S).card ≤ d * S.card := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let S' : Finset (Fin (Fintype.card ι) → Bool) := S.image (· ∘ e)
  have hinj_fn : Function.Injective (fun f : ι → Bool => f ∘ e) :=
    fun f₁ f₂ h => funext fun i => by simpa using congrFun h (e.symm i)
  have hcard_S : S'.card = S.card := card_image_of_injective S hinj_fn
  have hedg_eq : (oneInclusionEdges S).card = (oneInclusionEdges S').card := by
    refine card_bij (fun p _ => (e.symm p.1, p.2 ∘ e)) ?_ ?_ ?_
    · rintro ⟨i, f⟩ hp
      rcases mem_oneInclusionEdges.mp hp with ⟨hfS, hfi, hupdS⟩
      dsimp only at hfS hfi hupdS ⊢
      have hupd : Function.update (f ∘ e) (e.symm i) true = Function.update f i true ∘ e := by
        ext j
        by_cases hj : j = e.symm i
        · subst hj; simp
        · have hej : e j ≠ i := fun h => hj (by rw [← h, Equiv.symm_apply_apply])
          simp [hj, hej]
      exact mem_oneInclusionEdges.mpr ⟨mem_image_of_mem _ hfS, by simp [hfi],
        hupd ▸ mem_image_of_mem _ hupdS⟩
    · rintro ⟨i₁, f₁⟩ _ ⟨i₂, f₂⟩ _ heq
      rcases Prod.mk.inj heq with ⟨hi, hf⟩
      exact Prod.ext (e.symm.injective hi) (hinj_fn hf)
    · rintro ⟨j, g⟩ hp
      rcases mem_oneInclusionEdges.mp hp with ⟨hgS', hgj, hupdS'⟩
      dsimp only at hgS' hgj hupdS'
      rcases mem_image.mp hgS' with ⟨f, hfS, rfl⟩
      rcases mem_image.mp hupdS' with ⟨f', hf'S, hf'eq⟩
      have hf'_upd : f' = Function.update f (e j) true := by
        apply hinj_fn
        dsimp only
        rw [hf'eq]
        ext k
        by_cases hkj : k = j
        · subst hkj; simp
        · simp [hkj, e.injective.ne hkj]
      refine ⟨(e j, f), mem_oneInclusionEdges.mpr ⟨hfS, hgj, hf'_upd ▸ hf'S⟩, ?_⟩
      simp
  have hS' : ∀ W : Finset (Fin (Fintype.card ι)),
      SetShatters (S' : Set (Fin (Fintype.card ι) → Bool)) ↑W → W.card ≤ d := fun W hW =>
    SetShatters.card_le_of_comp hS (by simpa only [S', coe_image] using hW)
  rw [hedg_eq, ← hcard_S]
  exact card_oneInclusionEdges_fin_le hS'

/-! ### 2. Bounded-outdegree orientation via Hall's marriage theorem -/

/-- The tail endpoint of edge `e = (i, f)` under orientation `orient`: when `orient e = true` the
edge points from `f` (`e.2 e.1 = false`) to `Function.update f i true`, so the tail is `f`; when
`orient e = false` the tail is `Function.update f i true`. -/
def tailEndpoint [DecidableEq ι] (orient : (ι × (ι → Bool)) → Bool)
    (e : ι × (ι → Bool)) : ι → Bool :=
  Function.update e.2 e.1 (!orient e)

/-- Outdegree of `g` in `oneInclusionEdges S` under edge orientation `orient`. -/
def oneInclusionOutdegree [DecidableEq ι] [Fintype ι] (S : Finset (ι → Bool))
    (orient : (ι × (ι → Bool)) → Bool) (g : ι → Bool) : ℕ :=
  ((oneInclusionEdges S).filter fun e => tailEndpoint orient e = g).card

/-- **Haussler–Littlestone–Warmuth Bounded-Outdegree Orientation Lemma**
[HausslerLittlestoneWarmuth1994, §2.3 (locator unverified)]: if `S : Finset (ι → Bool)` shatters no
finite set of more than `d` coordinates, then `oneInclusionEdges S` admits an orientation `orient`
in which every vertex has outdegree at most `d`. -/
theorem exists_orientation_outdegree_le [DecidableEq ι] [Fintype ι] {d : ℕ}
    {S : Finset (ι → Bool)}
    (hS : ∀ W : Finset ι, SetShatters (S : Set (ι → Bool)) ↑W → W.card ≤ d) :
    ∃ orient : (ι × (ι → Bool)) → Bool, ∀ g : ι → Bool, oneInclusionOutdegree S orient g ≤ d := by
  classical
  let E := (oneInclusionEdges S : Set (ι × (ι → Bool)))
  let slots : E → Finset ((ι → Bool) × Fin d) := fun e =>
    ({e.1.2, Function.update e.1.2 e.1.1 true} : Finset (ι → Bool)) ×ˢ Finset.univ
  have hHall : ∀ A : Finset E, A.card ≤ (A.biUnion slots).card := by
    intro A
    let U : Finset (ι → Bool) :=
      A.biUnion fun e => ({e.1.2, Function.update e.1.2 e.1.1 true} : Finset (ι → Bool))
    have hprod : A.biUnion slots = U ×ˢ (Finset.univ : Finset (Fin d)) := by
      ext ⟨g, k⟩
      simp [slots, U]
    have hUS : U ⊆ S := by
      intro g hg
      rcases mem_biUnion.mp hg with ⟨e, _, hgpair⟩
      rcases mem_oneInclusionEdges.mp e.2 with ⟨he0, _, he1⟩
      rcases mem_insert.mp hgpair with rfl | hg1
      · exact he0
      · exact (mem_singleton.mp hg1) ▸ he1
    have hsub_edges : A.image Subtype.val ⊆ oneInclusionEdges U := by
      intro e' he'
      rcases mem_image.mp he' with ⟨e, heA, rfl⟩
      rcases mem_oneInclusionEdges.mp e.2 with ⟨_, hfalse, _⟩
      refine mem_oneInclusionEdges.mpr ⟨?_, hfalse, ?_⟩
      · exact mem_biUnion.mpr ⟨e, heA, mem_insert_self _ _⟩
      · exact mem_biUnion.mpr ⟨e, heA, mem_insert_of_mem (mem_singleton_self _)⟩
    have hU_sh : ∀ W : Finset ι, SetShatters (U : Set (ι → Bool)) ↑W → W.card ≤ d :=
      fun W hW => hS W (hW.superset (coe_subset.mpr hUS))
    calc A.card
        = (A.image Subtype.val).card := (card_image_of_injective A Subtype.coe_injective).symm
      _ ≤ (oneInclusionEdges U).card := card_le_card hsub_edges
      _ ≤ d * U.card := card_oneInclusionEdges_le_mul_card hU_sh
      _ = (A.biUnion slots).card := by
          rw [hprod, card_product, card_univ, Fintype.card_fin, mul_comm]
  obtain ⟨φ, hφ_inj, hφ_mem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' slots).mp hHall
  let orient : (ι × (ι → Bool)) → Bool := fun e =>
    if he : e ∈ oneInclusionEdges S then decide ((φ ⟨e, he⟩).1 = e.2) else false
  have htail_eq : ∀ (e : ι × (ι → Bool)) (he : e ∈ oneInclusionEdges S),
      tailEndpoint orient e = (φ ⟨e, he⟩).1 := by
    intro e he
    have hmem := (mem_product.mp (hφ_mem ⟨e, he⟩)).1
    have hfalse : e.2 e.1 = false := (mem_oneInclusionEdges.mp he).2.1
    simp only [tailEndpoint, orient, he, ↓reduceDIte]
    rcases mem_insert.mp hmem with h0 | h1
    · simp only [h0, decide_true, Bool.not_true]
      ext j
      by_cases hje : j = e.1
      · subst hje; simp [hfalse]
      · simp [hje]
    · have h1' : (φ ⟨e, he⟩).1 = Function.update e.2 e.1 true := mem_singleton.mp h1
      have hne : (φ ⟨e, he⟩).1 ≠ e.2 := by
        intro heq
        have hval := congrFun (heq.symm.trans h1') e.1
        rw [hfalse, Function.update_self] at hval
        exact Bool.false_ne_true hval
      rw [decide_eq_false hne, Bool.not_false, h1']
  refine ⟨orient, fun g => ?_⟩
  let outEdges := (oneInclusionEdges S).filter fun e => tailEndpoint orient e = g
  have hinj : Function.Injective
      (fun x : outEdges => (φ ⟨x.1, (mem_filter.mp x.2).1⟩).2) := by
    intro x₁ x₂ h2
    rcases mem_filter.mp x₁.2 with ⟨he₁, ht₁⟩
    rcases mem_filter.mp x₂.2 with ⟨he₂, ht₂⟩
    have h1 : (φ ⟨x₁.1, he₁⟩).1 = (φ ⟨x₂.1, he₂⟩).1 :=
      (htail_eq x₁.1 he₁).symm.trans (ht₁.trans (ht₂.symm.trans (htail_eq x₂.1 he₂)))
    have hE : (⟨x₁.1, he₁⟩ : E) = ⟨x₂.1, he₂⟩ := hφ_inj (Prod.ext h1 h2)
    exact Subtype.ext (congrArg (·.1) hE)
  have hcard := (Fintype.card_le_of_injective _ hinj).trans_eq (Fintype.card_fin d)
  simpa only [Fintype.card_coe, oneInclusionOutdegree, outEdges] using hcard

/-! ### 3. Parameter-free one-inclusion learner and transductive leave-one-out bound -/

/-- Finite set of labelings `↑U → Bool` realized by `C` on `U : Finset α`. -/
private noncomputable def resFinset (C : ConceptClass α Bool) (U : Finset α) :
    Finset (↑U → Bool) :=
  open Classical in
  letI : DecidableEq α := Classical.decEq α
  Finset.univ.filter fun f : ↑U → Bool => ∃ c ∈ C, ∀ u : ↑U, f u = c u.1

private theorem mem_resFinset {C : ConceptClass α Bool} {U : Finset α} {f : ↑U → Bool} :
    f ∈ resFinset C U ↔ ∃ c ∈ C, ∀ u : ↑U, f u = c u.1 := by
  simp [resFinset]

private theorem card_le_of_setShatters_resFinset {C : ConceptClass α Bool} {U : Finset α}
    {d : ℕ} (hC : ∀ W : Finset α, SetShatters C ↑W → W.card ≤ d)
    (W : Finset ↑U) (hW : SetShatters (resFinset C U : Set (↑U → Bool)) ↑W) :
    W.card ≤ d := by
  have hsub : (resFinset C U : Set (↑U → Bool)) ⊆ (fun c : α → Bool => c ∘ Subtype.val) '' C := by
    intro f hf
    obtain ⟨c, hc, hcf⟩ := mem_resFinset.mp hf
    exact ⟨c, hc, funext fun u => (hcf u).symm⟩
  exact SetShatters.card_le_of_comp hC (hW.superset hsub)

/-- Canonical orientation of `oneInclusionEdges (resFinset C U)` achieving outdegree at most
`vcDim (resFinset C U : Set (↑U → Bool))` (and hence at most `d` whenever `C` shatters no finite
set of size exceeding `d`). -/
private noncomputable def canonicalOrient (C : ConceptClass α Bool) (U : Finset α) :
    (↑U × (↑U → Bool)) → Bool :=
  open Classical in
  letI : DecidableEq α := Classical.decEq α
  let hfin : HasFiniteVCDim (resFinset C U : Set (↑U → Bool)) := hasFiniteVCDim_of_finite _
  (exists_orientation_outdegree_le (S := resFinset C U)
    (d := vcDim (resFinset C U : Set (↑U → Bool)))
    fun _ hW => hW.card_le_vcDim hfin).choose

private theorem oneInclusionOutdegree_canonicalOrient_le {C : ConceptClass α Bool}
    {U : Finset α} {d : ℕ} (hC : ∀ W : Finset α, SetShatters C ↑W → W.card ≤ d)
    (g : ↑U → Bool) :
    letI : DecidableEq α := Classical.decEq α
    oneInclusionOutdegree (resFinset C U) (canonicalOrient C U) g ≤ d := by
  classical
  have hfin : HasFiniteVCDim (resFinset C U : Set (↑U → Bool)) := hasFiniteVCDim_of_finite _
  have hspec := (exists_orientation_outdegree_le (S := resFinset C U)
    (d := vcDim (resFinset C U : Set (↑U → Bool)))
    fun _ hW => hW.card_le_vcDim hfin).choose_spec g
  have hvc_le : vcDim (resFinset C U : Set (↑U → Bool)) ≤ d := by
    have hevc : evcDim (resFinset C U : Set (↑U → Bool)) ≤ d :=
      evcDim_le_iff.mpr fun W hW => Nat.cast_le.mpr (card_le_of_setShatters_resFinset hC W hW)
    exact Nat.cast_le.mp ((natCast_vcDim hfin).trans_le hevc)
  exact hspec.trans hvc_le

/-- The parameter-free **Haussler–Littlestone–Warmuth one-inclusion graph learner**
[HausslerLittlestoneWarmuth1994, §2 (locator unverified)]: if test point `x` already appears in `S`,
reuse its observed label; otherwise form the unordered point set `U` of `S` and `x`, restrict to
concepts of `C` consistent with `S`, and resolve `0`/`1` ambiguity at `x` using
`canonicalOrient C U`. -/
noncomputable def oneInclusionLearner (C : ConceptClass α Bool) {m : ℕ}
    (S : LabeledSample α Bool m) (x : α) : Bool :=
  open Classical in
  letI : DecidableEq α := Classical.decEq α
  if hmem : ∃ j : Fin m, (S j).1 = x then
    (S hmem.choose).2
  else
    let U : Finset α := insert x (Finset.univ.image fun j : Fin m => (S j).1)
    let R := resFinset C U
    let ix : ↑U := ⟨x, mem_insert_self x _⟩
    let VS := R.filter fun f =>
      ∀ j : Fin m, f ⟨(S j).1, mem_insert_of_mem (mem_image_of_mem _ (mem_univ j))⟩ = (S j).2
    let V0 := VS.filter fun f => f ix = false
    let V1 := VS.filter fun f => f ix = true
    if h0 : V0.Nonempty then
      if V1.Nonempty then
        canonicalOrient C U (ix, h0.choose)
      else
        false
    else
      true

/-- Non-dependent predicate recording that `x ∈ U` is the coordinate of an outgoing edge from
`c|_U` in `oneInclusionEdges (resFinset C U)` under `canonicalOrient C U`. -/
private def isOutgoingAt (C : ConceptClass α Bool) (U : Finset α) (c : α → Bool) (x : α) : Prop :=
  letI : DecidableEq α := Classical.decEq α
  ∃ hx : x ∈ U,
    let g : ↑U → Bool := fun u => c u.1
    let e : ↑U × (↑U → Bool) := (⟨x, hx⟩, Function.update g ⟨x, hx⟩ false)
    e ∈ oneInclusionEdges (resFinset C U) ∧ tailEndpoint (canonicalOrient C U) e = g

private theorem mistake_imp_fresh_and_isOutgoingAt {C : ConceptClass α Bool} {m : ℕ}
    {S : LabeledSample α Bool m} {x : α} {c : α → Bool} (hc : c ∈ C)
    (hS : ∀ j : Fin m, (S j).2 = c (S j).1)
    (herr : oneInclusionLearner C S x ≠ c x) :
    letI : DecidableEq α := Classical.decEq α
    (∀ j : Fin m, (S j).1 ≠ x) ∧
      isOutgoingAt C (insert x (Finset.univ.image fun j : Fin m => (S j).1)) c x := by
  classical
  unfold oneInclusionLearner at herr
  by_cases hmem : ∃ j : Fin m, (S j).1 = x
  · simp only [hmem, ↓reduceDIte] at herr
    exact absurd ((hS hmem.choose).trans (congrArg c hmem.choose_spec)) herr
  simp only [hmem, ↓reduceDIte] at herr
  have hfresh : ∀ j : Fin m, (S j).1 ≠ x := fun j hj => hmem ⟨j, hj⟩
  refine ⟨hfresh, mem_insert_self x _, ?_⟩
  let U : Finset α := insert x (Finset.univ.image fun j : Fin m => (S j).1)
  let R := resFinset C U
  let ix : ↑U := ⟨x, mem_insert_self x _⟩
  let g : ↑U → Bool := fun u => c u.1
  let VS := R.filter fun f =>
    ∀ j : Fin m, f ⟨(S j).1, mem_insert_of_mem (mem_image_of_mem _ (mem_univ j))⟩ = (S j).2
  let V0 := VS.filter fun f => f ix = false
  let V1 := VS.filter fun f => f ix = true
  change (if h0 : V0.Nonempty then if V1.Nonempty then canonicalOrient C U (ix, h0.choose)
    else false else true) ≠ c x at herr
  have hgVS : g ∈ VS :=
    mem_filter.mpr ⟨mem_resFinset.mpr ⟨c, hc, fun _ => rfl⟩, fun j => (hS j).symm⟩
  have hVS_eq : ∀ f ∈ VS, f = Function.update g ix (f ix) := by
    intro f hf
    funext u
    by_cases hu : u = ix
    · subst hu; simp
    · have hux : u.1 ≠ x := fun heq => hu (Subtype.ext heq)
      have hu_img : u.1 ∈ Finset.univ.image (fun j : Fin m => (S j).1) :=
        (mem_insert.mp u.2).resolve_left hux
      rcases mem_image.mp hu_img with ⟨j, _, hSj⟩
      have hfS := (mem_filter.mp hf).2 j
      have huj : (⟨(S j).1, mem_insert_of_mem (mem_image_of_mem _ (mem_univ j))⟩ : ↑U) = u :=
        Subtype.ext hSj
      rw [huj] at hfS
      rw [Function.update_of_ne hu, hfS, hS j, hSj]
  by_cases h0 : V0.Nonempty
  · simp only [h0, ↓reduceDIte] at herr
    by_cases h1 : V1.Nonempty
    · simp only [h1, ↓reduceIte] at herr
      have hf0_mem : h0.choose ∈ V0 := h0.choose_spec
      rcases mem_filter.mp hf0_mem with ⟨hf0VS, hf0_false⟩
      have hf0_eq : h0.choose = Function.update g ix false := by
        simpa [hf0_false] using hVS_eq h0.choose hf0VS
      obtain ⟨f₁, hf₁V1⟩ := h1
      rcases mem_filter.mp hf₁V1 with ⟨hf₁VS, hf₁_true⟩
      have hf₁_eq : f₁ = Function.update g ix true := by
        simpa [hf₁_true] using hVS_eq f₁ hf₁VS
      have hupd_f0 : Function.update (Function.update g ix false) ix true = f₁ := by
        rw [hf₁_eq]; simp
      have hedge : (ix, Function.update g ix false) ∈ oneInclusionEdges R :=
        mem_oneInclusionEdges.mpr ⟨hf0_eq ▸ (mem_filter.mp hf0VS).1, by simp,
          hupd_f0.symm ▸ (mem_filter.mp hf₁VS).1⟩
      rw [hf0_eq] at herr
      have hnot_or : (!canonicalOrient C U (ix, Function.update g ix false)) = c x := by
        revert herr
        cases canonicalOrient C U (ix, Function.update g ix false) <;> cases c x <;> decide
      refine ⟨hedge, ?_⟩
      unfold tailEndpoint
      rw [Function.update_idem, hnot_or]
      funext u
      by_cases hu : u = ix
      · subst hu; exact Function.update_self ix (c x) g
      · exact Function.update_of_ne hu (c x) g
    · simp only [h1, ↓reduceIte] at herr
      cases hgx : c x
      · exact absurd hgx.symm herr
      · exact (h1 ⟨g, mem_filter.mpr ⟨hgVS, hgx⟩⟩).elim
  · simp only [h0, ↓reduceDIte] at herr
    cases hgx : c x
    · exact (h0 ⟨g, mem_filter.mpr ⟨hgVS, hgx⟩⟩).elim
    · exact absurd hgx.symm herr

/-- On any realizable sample `S`, `oneInclusionLearner C S` reproduces the observed label on every
training example `(S j).1`. -/
theorem oneInclusionLearner_apply_sample_of_realizable {C : ConceptClass α Bool} {m : ℕ}
    {S : LabeledSample α Bool m} (hS : Realizable C S) (j : Fin m) :
    oneInclusionLearner C S (S j).1 = (S j).2 := by
  obtain ⟨c, hc, hcS⟩ := hS
  by_contra herr
  have herr' : oneInclusionLearner C S (S j).1 ≠ c (S j).1 := by rwa [← hcS j]
  exact (mistake_imp_fresh_and_isOutgoingAt hc hcS herr').1 j rfl

/-- If `S` is realizable by `C` and every concept in `C` consistent with `S` assigns label `b` to
`x`, then `oneInclusionLearner C S x = b`. -/
theorem oneInclusionLearner_eq_of_forall_consistent {C : ConceptClass α Bool} {m : ℕ}
    {S : LabeledSample α Bool m} (hS : Realizable C S) {x : α} {b : Bool}
    (huniq : ∀ c ∈ C, (∀ j : Fin m, (S j).2 = c (S j).1) → c x = b) :
    oneInclusionLearner C S x = b := by
  classical
  obtain ⟨c, hc, hcS⟩ := hS
  by_contra hne
  have herr : oneInclusionLearner C S x ≠ c x := by rwa [huniq c hc hcS]
  obtain ⟨hfresh, hx, he, _⟩ := mistake_imp_fresh_and_isOutgoingAt hc hcS herr
  rcases mem_oneInclusionEdges.mp he with ⟨hf0, _, hf1⟩
  dsimp only at hf0 hf1
  rw [Function.update_idem] at hf1
  have hb_eq : ∀ v : Bool,
      Function.update (fun u : ↑(insert x (Finset.univ.image fun k : Fin m => (S k).1)) => c u.1)
        ⟨x, hx⟩ v ∈ resFinset C (insert x (Finset.univ.image fun k : Fin m => (S k).1)) →
      b = v := by
    intro v hmem
    obtain ⟨c', hc', hc'f⟩ := mem_resFinset.mp hmem
    have hc'S : ∀ j : Fin m, (S j).2 = c' (S j).1 := fun j => by
      have hjx : (⟨(S j).1, mem_insert_of_mem (mem_image_of_mem _ (mem_univ j))⟩ :
          ↑(insert x (Finset.univ.image fun k : Fin m => (S k).1))) ≠ ⟨x, hx⟩ :=
        fun h => hfresh j (congrArg Subtype.val h)
      have hval := hc'f ⟨(S j).1, mem_insert_of_mem (mem_image_of_mem _ (mem_univ j))⟩
      rw [Function.update_of_ne hjx] at hval
      exact (hcS j).trans hval
    have hv := hc'f ⟨x, hx⟩
    rw [Function.update_self] at hv
    exact (huniq c' hc' hc'S).symm.trans hv.symm
  exact Bool.false_ne_true ((hb_eq false hf0).symm.trans (hb_eq true hf1))

/-- **Haussler–Littlestone–Warmuth Transductive Leave-One-Out Bound**
[HausslerLittlestoneWarmuth1994, Theorem 2.3 (locator unverified)]: if `C` shatters no finite set of
more than `d` points, then on every realizable `(m + 1)`-sample `Z` (`Realizable C Z`),
`oneInclusionLearner C` errs on at most `d` of the `m + 1` leave-one-out folds
`(t.removeNth Z, (Z t).1)`. -/
theorem card_leaveOneOut_mistakes_le {C : ConceptClass α Bool} {d m : ℕ}
    (hC : ∀ W : Finset α, SetShatters C ↑W → W.card ≤ d)
    {Z : LabeledSample α Bool (m + 1)} (hZ : Realizable C Z) :
    (Finset.univ.filter fun t : Fin (m + 1) =>
      oneInclusionLearner C (t.removeNth Z) (Z t).1 ≠ (Z t).2).card ≤ d := by
  classical
  obtain ⟨c, hc, hcZ⟩ := hZ
  let UZ : Finset α := Finset.univ.image fun t : Fin (m + 1) => (Z t).1
  have hU_eq : ∀ t : Fin (m + 1),
      insert (Z t).1 (Finset.univ.image fun j : Fin m => (t.removeNth Z j).1) = UZ := by
    intro t
    ext a
    constructor
    · intro ha
      rcases mem_insert.mp ha with ha0 | ha_img
      · exact mem_image.mpr ⟨t, mem_univ t, ha0.symm⟩
      · rcases mem_image.mp ha_img with ⟨j, _, hj⟩
        exact mem_image.mpr ⟨t.succAbove j, mem_univ _, hj⟩
    · intro ha
      rcases mem_image.mp ha with ⟨s, _, hs⟩
      by_cases hst : s = t
      · exact mem_insert.mpr (Or.inl (hs.symm.trans (congrArg (fun k => (Z k).1) hst)))
      · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hst
        refine mem_insert.mpr (Or.inr (mem_image.mpr ⟨j, mem_univ j, ?_⟩))
        simpa only [Fin.removeNth, hj] using hs
  let M : Finset (Fin (m + 1)) := Finset.univ.filter fun t : Fin (m + 1) =>
    oneInclusionLearner C (t.removeNth Z) (Z t).1 ≠ (Z t).2
  let gZ : ↑UZ → Bool := fun u => c u.1
  let OutEdges := (oneInclusionEdges (resFinset C UZ)).filter fun e =>
    tailEndpoint (canonicalOrient C UZ) e = gZ
  have hstep : ∀ t ∈ M,
      (∀ j : Fin m, (Z (t.succAbove j)).1 ≠ (Z t).1) ∧ isOutgoingAt C UZ c (Z t).1 := by
    intro t ht
    have herr : oneInclusionLearner C (t.removeNth Z) (Z t).1 ≠ c (Z t).1 := by
      simpa [hcZ t] using (mem_filter.mp ht).2
    have h := mistake_imp_fresh_and_isOutgoingAt (S := t.removeNth Z) hc
      (fun j => hcZ (t.succAbove j)) herr
    rw [hU_eq t] at h
    exact ⟨fun j => h.1 j, h.2⟩
  have hcard_le : M.card ≤ OutEdges.card := by
    let toEdge : M → OutEdges := fun t =>
      let hx : (Z t.1).1 ∈ UZ := mem_image_of_mem _ (mem_univ t.1)
      let e : ↑UZ × (↑UZ → Bool) := (⟨(Z t.1).1, hx⟩, Function.update gZ ⟨(Z t.1).1, hx⟩ false)
      ⟨e, by
        rcases (hstep t.1 t.2).2 with ⟨hx', he_mem, htail⟩
        have hsub : (⟨(Z t.1).1, hx'⟩ : ↑UZ) = ⟨(Z t.1).1, hx⟩ := rfl
        exact mem_filter.mpr ⟨he_mem, htail⟩⟩
    have hinj : Function.Injective toEdge := by
      intro t₁ t₂ heq
      by_contra hne
      have ht_ne : t₂.1 ≠ t₁.1 := fun h => hne (Subtype.ext h.symm)
      obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq ht_ne
      have hZ_eq : (Z t₁.1).1 = (Z t₂.1).1 :=
        congrArg (fun x : OutEdges => x.1.1.1) heq
      exact (hstep t₁.1 t₁.2).1 j (hj ▸ hZ_eq.symm)
    simpa using Fintype.card_le_of_injective toEdge hinj
  exact hcard_le.trans (oneInclusionOutdegree_canonicalOrient_le hC gZ)

/-! ### 4. Expected generalization error `d / (m + 1)` and realizable PAC sample complexity -/

section Measure

variable [MeasurableSpace α]

/-- Exchangeability of `D ^ (m + 1)`: for any jointly measurable learner `A : Learner α Bool m`
and any coordinate `t : Fin (m + 1)`, the expected true error of `A` on `m` i.i.d. examples equals
the probability that `A` errs on held-out example `t` of `m + 1` i.i.d. examples. -/
theorem lintegral_error_eq_leaveOneOut {m : ℕ} {A : Learner α Bool m}
    (hA : Measurable fun p : LabeledSample α Bool m × α => A p.1 p.2)
    (D : Measure (α × Bool)) [IsProbabilityMeasure D] (t : Fin (m + 1)) :
    ∫⁻ S, error D (A S) ∂Measure.pi (fun _ : Fin m => D) =
      Measure.pi (fun _ : Fin (m + 1) => D)
        {Z | A (t.removeNth Z) (Z t).1 ≠ (Z t).2} := by
  let F : Set ((α × Bool) × LabeledSample α Bool m) := {q | A q.2 q.1.1 ≠ q.1.2}
  have hF : MeasurableSet F := by
    have hpred : Measurable fun q : (α × Bool) × LabeledSample α Bool m => A q.2 q.1.1 :=
      hA.comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst))
    exact (measurableSet_eq_fun hpred (measurable_snd.comp measurable_fst)).compl
  have he := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => D) t
  have hset : {Z : LabeledSample α Bool (m + 1) | A (t.removeNth Z) (Z t).1 ≠ (Z t).2} =
      MeasurableEquiv.piFinSuccAbove (fun _ => α × Bool) t ⁻¹' F := by
    ext Z
    rfl
  rw [hset, he.measure_preimage hF.nullMeasurableSet, Measure.prod_apply_symm hF]
  rfl

/-- Multiplicative form of the Haussler–Littlestone–Warmuth expected error bound
[HausslerLittlestoneWarmuth1994, Theorem 2.3 (locator unverified)]:
`(m + 1) * ∫⁻ S, error D (oneInclusionLearner C S) ∂D^m ≤ d`. -/
private theorem mul_lintegral_error_oneInclusionLearner_le {C : ConceptClass α Bool} {d m : ℕ}
    (hC : ∀ W : Finset α, SetShatters C ↑W → W.card ≤ d)
    (hmeas : Measurable fun p : LabeledSample α Bool m × α => oneInclusionLearner C p.1 p.2)
    {D : Measure (α × Bool)} [IsProbabilityMeasure D] (hD : IsRealizableBy D C) :
    (m + 1 : ℝ≥0∞) *
        ∫⁻ S, error D (oneInclusionLearner C S) ∂Measure.pi (fun _ : Fin m => D) ≤ d := by
  set μ := Measure.pi (fun _ : Fin (m + 1) => D)
  have hsum_eq : (m + 1 : ℝ≥0∞) *
      ∫⁻ S, error D (oneInclusionLearner C S) ∂Measure.pi (fun _ : Fin m => D) =
      ∑ t : Fin (m + 1), μ {Z | oneInclusionLearner C (t.removeNth Z) (Z t).1 ≠ (Z t).2} := by
    have hcard : (m + 1 : ℝ≥0∞) = ((Finset.univ : Finset (Fin (m + 1))).card : ℕ) := by simp
    rw [hcard, ← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_congr rfl fun t _ => lintegral_error_eq_leaveOneOut hmeas D t
  rw [hsum_eq]
  have hmeas_t : ∀ t : Fin (m + 1),
      MeasurableSet {Z : LabeledSample α Bool (m + 1) |
        oneInclusionLearner C (t.removeNth Z) (Z t).1 ≠ (Z t).2} := by
    intro t
    have hrem : Measurable fun Z : LabeledSample α Bool (m + 1) => t.removeNth Z :=
      measurable_pi_iff.mpr fun j => measurable_pi_apply (t.succAbove j)
    have hpred : Measurable fun Z : LabeledSample α Bool (m + 1) =>
        oneInclusionLearner C (t.removeNth Z) (Z t).1 :=
      hmeas.comp (hrem.prodMk (measurable_fst.comp (measurable_pi_apply t)))
    exact (measurableSet_eq_fun hpred (measurable_snd.comp (measurable_pi_apply t))).compl
  calc ∑ t : Fin (m + 1), μ {Z | oneInclusionLearner C (t.removeNth Z) (Z t).1 ≠ (Z t).2}
      = ∫⁻ Z, ∑ t : Fin (m + 1),
          {Z : LabeledSample α Bool (m + 1) |
            oneInclusionLearner C (t.removeNth Z) (Z t).1 ≠ (Z t).2}.indicator 1 Z ∂μ := by
        refine (Finset.sum_congr rfl fun t _ => (lintegral_indicator_one (hmeas_t t)).symm).trans ?_
        exact (lintegral_finsetSum _ fun t _ => measurable_one.indicator (hmeas_t t)).symm
    _ ≤ ∫⁻ _, (d : ℝ≥0∞) ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hD.ae_realizable (m + 1)] with Z hZ
        have hcount : ∑ t : Fin (m + 1),
            {Z : LabeledSample α Bool (m + 1) |
              oneInclusionLearner C (t.removeNth Z) (Z t).1 ≠ (Z t).2}.indicator 1 Z =
            ((Finset.univ.filter fun t : Fin (m + 1) =>
              oneInclusionLearner C (t.removeNth Z) (Z t).1 ≠ (Z t).2).card : ℝ≥0∞) := by
          rw [Finset.card_filter, Nat.cast_sum]
          refine Finset.sum_congr rfl fun t _ => ?_
          by_cases h : oneInclusionLearner C (t.removeNth Z) (Z t).1 ≠ (Z t).2 <;> simp [h]
        rw [hcount]
        exact_mod_cast card_leaveOneOut_mistakes_le hC hZ
    _ = d := by rw [lintegral_const, measure_univ, mul_one]

/-- **Haussler–Littlestone–Warmuth Expected Error Bound**
[HausslerLittlestoneWarmuth1994, Theorem 2.3 (locator unverified)]: if `C` shatters no finite set of
more than `d` points, `oneInclusionLearner C` is jointly measurable, and `D` is realizable by `C`,
then on `m` i.i.d. examples from `D`, `𝔼[error D (oneInclusionLearner C S)] ≤ d / (m + 1)`. -/
theorem lintegral_error_oneInclusionLearner_le {C : ConceptClass α Bool} {d m : ℕ}
    (hC : ∀ W : Finset α, SetShatters C ↑W → W.card ≤ d)
    (hmeas : Measurable fun p : LabeledSample α Bool m × α => oneInclusionLearner C p.1 p.2)
    {D : Measure (α × Bool)} [IsProbabilityMeasure D] (hD : IsRealizableBy D C) :
    ∫⁻ S, error D (oneInclusionLearner C S) ∂Measure.pi (fun _ : Fin m => D) ≤
      (d : ℝ≥0∞) / (m + 1) := by
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl (by simp)), mul_comm]
  exact mul_lintegral_error_oneInclusionLearner_le hC hmeas hD

/-- **Haussler–Littlestone–Warmuth PAC Sample-Size Theorem**
[HausslerLittlestoneWarmuth1994, Theorem 2.3 (locator unverified)]: if `C` shatters no finite set of
more than `d` points and `oneInclusionLearner C` is jointly measurable at sample size `m`, then
`oneInclusionLearner C` is an `(ε, δ)`-PAC learner over `realizableDistributions C` whenever
`d ≤ ε δ (m + 1)`. -/
theorem isPACLearnerFor_oneInclusionLearner {C : ConceptClass α Bool} {d m : ℕ}
    (hC : ∀ W : Finset α, SetShatters C ↑W → W.card ≤ d)
    (hmeas : Measurable fun p : LabeledSample α Bool m × α => oneInclusionLearner C p.1 p.2)
    {ε δ : Set.Ioo (0 : ℝ≥0) 1} (hm : (d : ℝ≥0) ≤ ε.val * δ.val * (m + 1)) :
    IsPACLearnerFor m ε δ C (realizableDistributions C) := by
  refine ⟨oneInclusionLearner C, fun D _ hD => ?_⟩
  rw [IsRealizableBy.optimalError_eq_zero hD, zero_add]
  set μ := Measure.pi (fun _ : Fin m => D)
  have hε : (ε.val : ℝ≥0∞) ≠ 0 := by simpa using ε.2.1.ne'
  have hpos : ((m + 1 : ℝ≥0∞)) ≠ 0 := by positivity
  have hmeas_err : Measurable fun S : LabeledSample α Bool m =>
      error D (oneInclusionLearner C S) := by
    have hmis : MeasurableSet {p : LabeledSample α Bool m × (α × Bool) |
        oneInclusionLearner C p.1 p.2.1 ≠ p.2.2} :=
      (measurableSet_eq_fun
        (hmeas.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))
        (measurable_snd.comp measurable_snd)).compl
    exact measurable_measure_prodMk_left hmis
  have hsub : {S : LabeledSample α Bool m | (ε.val : ℝ≥0∞) < error D (oneInclusionLearner C S)} ⊆
      {S | (ε.val : ℝ≥0∞) * (m + 1) ≤ (m + 1) * error D (oneInclusionLearner C S)} := by
    intro S hS
    calc (ε.val : ℝ≥0∞) * (m + 1)
        ≤ error D (oneInclusionLearner C S) * (m + 1) := by gcongr; exact hS.le
      _ = (m + 1) * error D (oneInclusionLearner C S) := mul_comm _ _
  have hint : ∫⁻ S, (m + 1 : ℝ≥0∞) * error D (oneInclusionLearner C S) ∂μ ≤ d := by
    rw [lintegral_const_mul _ hmeas_err]
    exact mul_lintegral_error_oneInclusionLearner_le hC hmeas hD
  calc μ {S | (ε.val : ℝ≥0∞) < error D (oneInclusionLearner C S)}
      ≤ μ {S | (ε.val : ℝ≥0∞) * (m + 1) ≤ (m + 1) * error D (oneInclusionLearner C S)} :=
        measure_mono hsub
    _ ≤ (∫⁻ S, (m + 1 : ℝ≥0∞) * error D (oneInclusionLearner C S) ∂μ) /
          ((ε.val : ℝ≥0∞) * (m + 1)) :=
        meas_ge_le_lintegral_div (hmeas_err.const_mul _).aemeasurable
          (mul_ne_zero hε hpos) (ENNReal.mul_ne_top ENNReal.coe_ne_top (by simp))
    _ ≤ (d : ℝ≥0∞) / ((ε.val : ℝ≥0∞) * (m + 1)) := by gcongr
    _ ≤ δ.val := by
        rw [ENNReal.div_le_iff (mul_ne_zero hε hpos)
          (ENNReal.mul_ne_top ENNReal.coe_ne_top (by simp))]
        have hcoe : ((d : ℝ≥0) : ℝ≥0∞) ≤ ((ε.val * δ.val * (m + 1) : ℝ≥0) : ℝ≥0∞) :=
          ENNReal.coe_le_coe.mpr hm
        push_cast at hcoe
        calc (d : ℝ≥0∞) ≤ ε.val * δ.val * (m + 1) := hcoe
          _ = δ.val * (ε.val * (m + 1)) := by ring

/-- On a countable domain with measurable singletons, any class `C` of finite VC dimension achieves
realizable PAC sample complexity at most `⌈vcDim C / (ε δ)⌉₊` via `oneInclusionLearner C`,
eliminating the `log (1 / ε)` factor of empirical risk minimization at fixed confidence `δ`. -/
theorem sampleComplexity_realizableDistributions_le_div_vcDim
    [Countable α] [MeasurableSingletonClass α] {C : ConceptClass α Bool}
    (hC : HasFiniteVCDim C) (ε δ : Set.Ioo (0 : ℝ≥0) 1) :
    sampleComplexity IsPACLearnerFor C ε δ (realizableDistributions C) ≤
      ⌈(vcDim C : ℝ≥0) / (ε.val * δ.val)⌉₊ := by
  refine Nat.sInf_le ?_
  refine isPACLearnerFor_oneInclusionLearner (fun W hW => hW.card_le_vcDim hC)
    (measurable_of_countable _) ?_
  have hεδ : 0 < ε.val * δ.val := mul_pos ε.2.1 δ.2.1
  have h := Nat.le_ceil ((vcDim C : ℝ≥0) / (ε.val * δ.val))
  rw [div_le_iff₀' hεδ] at h
  exact h.trans (by gcongr; exact le_self_add)

end Measure

end Cslib.MachineLearning.PACLearning


