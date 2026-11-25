/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.PACLearning.GrowthFunction
public import CslibFrontier.MachineLearning.PACLearning.NatarajanDimension
import CslibFrontier.Foundations.Data.Nat.Choose.Sum
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Graph Dimension, Pseudo-Cubes, and the Daniely–Shalev-Shwartz Dimension

For binary classification (`β = Bool`), the Vapnik–Chervonenkis dimension characterizes both
uniform convergence and PAC learnability. For multiclass concept classes `C : ConceptClass α β`,
three distinct combinatorial dimensions govern different regimes:

1. **Natarajan dimension** (`NatarajanShatters`, `natarajanDim` in
   `CslibFrontier/MachineLearning/PACLearning/NatarajanDimension.lean`; [Natarajan1989]): pairs of
   witness labelings `f₀, f₁ : α → β` realizing all `2 ^ |W|` binary choices on `W`.
2. **Daniely–Shalev-Shwartz (DS) dimension** (`IsPseudoCube`, `DSShatters`, `dsDim`;
   [DanielyShalevShwartz2014]; [BrukhimCarmonDinurMoranYehudayoff2022]): the largest size of a
   finite set `W` on which the restriction of `C` contains a **pseudo-cube** — a nonempty finite
   set `P` of labelings of `W` in which every `f ∈ P` and coordinate `i ∈ W` admits an
   *`i`-neighbor* `g ∈ P` differing from `f` exclusively at `i`. Finite DS dimension characterizes
   multiclass PAC learnability over arbitrary label spaces [BrukhimCarmonDinurMoranYehudayoff2022].
3. **Graph dimension** (`GraphShatters`, `graphDim`; [Natarajan1989];
   [BenDavidCesaBianchiHausslerLong1995]): a single reference labeling `f : α → β` against which
   every subset `B ⊆ W` is realized by some `c ∈ C` agreeing with `f` on `B` and disagreeing with
   `f` on `W \ B`, equivalently the VC dimension of the binary concept-graph class `conceptGraph C`
   on `α × β` (`graphDim_eq_evcDim_conceptGraph`).

This module develops `GraphShatters`/`graphDim` and `IsPseudoCube`/`DSShatters`/`dsDim`, connects
them to Sauer's lemma (`GrowthFunction.lean`) and Natarajan's lemma (`NatarajanDimension.lean`),
proves the universal hierarchy `natarajanDim C ≤ dsDim C ≤ graphDim C` together with their
quantitative `O(d log |β|)` equivalence over finite label spaces (`graphDim_le_mul_natarajanDim`),
and establishes strict separations at both inequalities (`hexagonClass` for `|β| = 3` and
`revealingSetClass` for infinite label spaces).

## Main definitions

- `GraphShatters C W`, `graphDim C`, `HasFiniteGraphDim C`: graph shattering and graph dimension.
- `conceptGraph C`: the binary graph class `{(x, y) ↦ decide (c x = y) | c ∈ C}` on `α × β`.
- `IsPseudoCube P`: a nonempty `Finset (ι → β)` closed under coordinate `i`-neighbors.
- `DSShatters C W`, `dsDim C`, `HasFiniteDSDim C`: DS-shattering and the Daniely–Shalev-Shwartz
  dimension.
- `hexagonClass`: the 6-cycle `{f : Fin 2 → Fin 3 | f 0 ≠ f 1}` separating `natarajanDim` from
  `dsDim` at three labels.
- `revealingSetClass α`: the class `{x ↦ if x ∈ B then none else some B | B : Finset α}` separating
  `dsDim` (`= 1`) from `graphDim` (`= ⊤`) on infinite domains.

## Main results

- `graphDim_eq_evcDim_conceptGraph`: `graphDim C = evcDim (conceptGraph C)`.
- `ncard_restriction_le_sum_choose_graphDim`: Sauer–Shelah growth bound
  `((· ∘ x) '' C).ncard ≤ ∑_{i ≤ d} C(n |β|, i)` for classes of graph dimension at most `d`.
- `IsPseudoCube.image_precomp`: injective coordinate projections of pseudo-cubes are pseudo-cubes.
- `IsPseudoCube.two_pow_card_le_card`: every pseudo-cube on `ι` has at least `2 ^ |ι|` elements.
- `isPseudoCube_iff_eq_univ_of_card_eq_two`, `dsDim_eq_evcDim`: on two-element label spaces (and
  `Bool`), pseudo-cubes are full Boolean hypercubes and `dsDim C = evcDim C`.
- `DSShatters.finite`: only finite sets can be DS-shattered.
- `NatarajanShatters.dsShatters`, `DSShatters.graphShatters`, `natarajanDim_le_dsDim`,
  `dsDim_le_graphDim`: the multiclass shattering and dimension hierarchy
  `natarajanDim C ≤ dsDim C ≤ graphDim C`.
- `GraphShatters.two_pow_card_le_natarajanSum`, `card_le_of_graphShatters`,
  `graphDim_le_mul_natarajanDim`, `hasFiniteDSDim_iff_hasFiniteNatarajanDim`,
  `hasFiniteGraphDim_iff_hasFiniteNatarajanDim`: over finite label spaces,
  `graphDim C ≤ 4 * natarajanDim C * (⌊log₂ |β|⌋ + 2)`, so finiteness of all three dimensions is
  equivalent.
- `natarajanDim_hexagonClass`, `dsDim_hexagonClass`, `graphDim_hexagonClass`: `1 < 2 = 2` on
  `Fin 2 → Fin 3`.
- `natarajanDim_revealingSetClass`, `dsDim_revealingSetClass`,
  `graphDim_revealingSetClass_of_infinite`: `1 = 1 < ⊤` on infinite domains.

## References

* [S. Ben-David, N. Cesa-Bianchi, D. Haussler, P. M. Long, *Characterizations of Learnability for
  Classes of `{0, …, n}`-Valued Functions*][BenDavidCesaBianchiHausslerLong1995]
* [N. Brukhim, D. Carmon, I. Dinur, S. Moran, A. Yehudayoff, *A Characterization of Multiclass
  Learnability*][BrukhimCarmonDinurMoranYehudayoff2022]
* [A. Daniely, S. Shalev-Shwartz, *Optimal Learners for Multiclass
  Problems*][DanielyShalevShwartz2014]
* [B. K. Natarajan, *On Learning Sets and Functions*][Natarajan1989]
* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014]
-/

public section

open Finset

namespace Cslib.MachineLearning.PACLearning

variable {α β γ ι κ : Type*}

/-! ### Graph shattering and the graph dimension -/

/-- A concept class `C` *G-shatters* (graph-shatters) a set `W` if there is a reference labeling
`f : α → β` such that for every `B ⊆ W` some concept `c ∈ C` agrees with `f` on `B` and disagrees
with `f` at every point of `W \ B` [Natarajan1989; BenDavidCesaBianchiHausslerLong1995]. -/
@[expose] def GraphShatters (C : ConceptClass α β) (W : Set α) : Prop :=
  ∃ f : α → β, ∀ B ⊆ W, ∃ c ∈ C, (∀ x ∈ B, c x = f x) ∧ ∀ x ∈ W \ B, c x ≠ f x

/-- The *graph dimension* of `C` is the supremum in `ℕ∞` of the sizes of finite G-shattered sets. -/
noncomputable def graphDim (C : ConceptClass α β) : ℕ∞ :=
  ⨆ W : Finset α, ⨆ _ : GraphShatters C ↑W, (W.card : ℕ∞)

/-- The graph dimension is finite. -/
@[expose] def HasFiniteGraphDim (C : ConceptClass α β) : Prop := graphDim C ≠ ⊤

theorem GraphShatters.subset {C : ConceptClass α β} {W V : Set α}
    (hW : GraphShatters C W) (hVW : V ⊆ W) : GraphShatters C V :=
  let ⟨f, h⟩ := hW
  ⟨f, fun B hB => let ⟨c, hc, h₀, h₁⟩ := h B (hB.trans hVW)
    ⟨c, hc, h₀, fun x hx => h₁ x ⟨hVW hx.1, hx.2⟩⟩⟩

theorem GraphShatters.superset {C C' : ConceptClass α β} {W : Set α}
    (hW : GraphShatters C W) (hCC' : C ⊆ C') : GraphShatters C' W :=
  let ⟨f, h⟩ := hW
  ⟨f, fun B hB => let ⟨c, hc, h₀, h₁⟩ := h B hB; ⟨c, hCC' hc, h₀, h₁⟩⟩

theorem GraphShatters.nonempty {C : ConceptClass α β} {W : Set α}
    (hW : GraphShatters C W) : C.Nonempty :=
  let ⟨_, h⟩ := hW
  let ⟨c, hc, _⟩ := h ∅ (Set.empty_subset W)
  ⟨c, hc⟩

theorem graphShatters_empty {C : ConceptClass α β} (hC : C.Nonempty) :
    GraphShatters C ∅ :=
  let ⟨c, hc⟩ := hC
  ⟨c, fun _ hB => ⟨c, hc, fun _ hx => (hB hx).elim, fun _ hx => hx.1.elim⟩⟩

theorem GraphShatters.card_le_graphDim {C : ConceptClass α β} {W : Finset α}
    (hW : GraphShatters C ↑W) : (W.card : ℕ∞) ≤ graphDim C :=
  le_iSup₂_of_le W hW le_rfl

theorem graphDim_le_iff {C : ConceptClass α β} {d : ℕ∞} :
    graphDim C ≤ d ↔ ∀ W : Finset α, GraphShatters C ↑W → (W.card : ℕ∞) ≤ d :=
  iSup₂_le_iff

private theorem iSup_ne_top_iff {P : Finset α → Prop} :
    (⨆ W : Finset α, ⨆ _ : P W, (W.card : ℕ∞)) ≠ ⊤ ↔
      ∃ n : ℕ, ∀ W : Finset α, P W → W.card ≤ n :=
  ⟨fun h => let ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h
    ⟨n, fun W hW => Nat.cast_le.mp (hn ▸ le_iSup₂_of_le W hW le_rfl)⟩,
   fun ⟨n, hn⟩ => ne_top_of_le_ne_top (ENat.natCast_ne_top n)
    (iSup₂_le_iff.mpr fun W hW => Nat.cast_le.mpr (hn W hW))⟩

theorem hasFiniteGraphDim_iff {C : ConceptClass α β} :
    HasFiniteGraphDim C ↔ ∃ n : ℕ, ∀ W : Finset α, GraphShatters C ↑W → W.card ≤ n :=
  iSup_ne_top_iff

theorem hasFiniteGraphDim_of_finite [Finite α] (C : ConceptClass α β) :
    HasFiniteGraphDim C :=
  have := Fintype.ofFinite α
  hasFiniteGraphDim_iff.mpr ⟨Fintype.card α, fun W _ => W.card_le_univ⟩

private theorem exists_finset_card_eq_of_iSup {P : Finset α → Prop} {d : ℕ}
    (hd : (⨆ W : Finset α, ⨆ _ : P W, (W.card : ℕ∞)) = d) (hpos : 0 < d) :
    ∃ W : Finset α, W.card = d ∧ P W := by
  rcases d with _ | n
  · cases hpos
  · obtain ⟨W, hlt⟩ := lt_iSup_iff.mp <|
      (show (n : ℕ∞) < (n + 1 : ℕ) by exact_mod_cast Nat.lt_succ_self n).trans_eq hd.symm
    obtain ⟨hW, hlt⟩ := lt_iSup_iff.mp hlt
    exact ⟨W, (Nat.cast_le.mp (hd ▸ le_iSup₂_of_le W hW le_rfl)).antisymm (Nat.cast_lt.mp hlt), hW⟩

theorem exists_graphShatters_card_eq {C : ConceptClass α β} {d : ℕ}
    (hd : graphDim C = d) (hpos : 0 < d) :
    ∃ W : Finset α, W.card = d ∧ GraphShatters C ↑W :=
  exists_finset_card_eq_of_iSup hd hpos

/-- Binary concept-graph class `{(x, y) ↦ decide (c x = y) | c ∈ C}` on `α × β`. -/
@[expose] def conceptGraph (C : ConceptClass α β) [DecidableEq β] :
    ConceptClass (α × β) Bool :=
  (fun c (p : α × β) => decide (c p.1 = p.2)) '' C

/-- The graph dimension of `C` equals the extended VC dimension of `conceptGraph C`. -/
theorem graphDim_eq_evcDim_conceptGraph (C : ConceptClass α β) [DecidableEq β] :
    graphDim C = evcDim (conceptGraph C) := by
  classical
  refine le_antisymm (graphDim_le_iff.mpr fun W hW => ?_) (evcDim_le_iff.mpr fun S hS => ?_)
  · obtain ⟨f, hf⟩ := hW
    let emb : α ↪ α × β := ⟨fun x => (x, f x), fun _ _ h => congrArg Prod.fst h⟩
    have hsh : SetShatters (conceptGraph C) ↑(W.map emb) := fun T hT => by
      obtain ⟨c, hc, h₀, h₁⟩ := hf {x ∈ (↑W : Set α) | (x, f x) ∈ T} fun _ hx => hx.1
      refine ⟨fun p => decide (c p.1 = p.2), ⟨c, hc, rfl⟩, Set.ext fun p => ?_⟩
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, decide_eq_true_iff]
      refine ⟨fun ⟨hp_eq, hpS⟩ => ?_, fun hpT => ?_⟩
      · rcases mem_map.mp hpS with ⟨x, hxW, rfl⟩
        exact by_contra fun hxT => h₁ x ⟨hxW, fun h => hxT h.2⟩ hp_eq
      · rcases mem_map.mp (hT hpT) with ⟨x, hxW, rfl⟩
        exact ⟨h₀ x ⟨hxW, hpT⟩, hT hpT⟩
    simpa only [card_map] using hsh.card_le_evcDim
  · rcases S.eq_empty_or_nonempty with rfl | ⟨_, _⟩
    · simp
    · obtain ⟨_, ⟨c₀, _, rfl⟩, hcS⟩ := hS ↑S Set.Subset.rfl
      have hc_eq : ∀ p ∈ (↑S : Set (α × β)), c₀ p.1 = p.2 := fun p hp =>
        of_decide_eq_true (show p ∈ (fun p : α × β => decide (c₀ p.1 = p.2)) ⁻¹' {true} ∩ ↑S from
          hcS.symm ▸ hp).1
      have hinj : Set.InjOn Prod.fst (↑S : Set (α × β)) := fun p₁ hp₁ p₂ hp₂ hf_eq =>
        Prod.ext hf_eq ((hc_eq p₁ hp₁).symm.trans ((congrArg c₀ hf_eq).trans (hc_eq p₂ hp₂)))
      let W := S.image Prod.fst
      let f : α → β := fun x => if h : ∃ y, (x, y) ∈ S then h.choose else c₀ x
      have hf_mem : ∀ x ∈ W, (x, f x) ∈ S := fun x hx => by
        rcases mem_image.mp hx with ⟨⟨x', y⟩, hp, rfl⟩
        simpa only [f, show ∃ y', (x', y') ∈ S from ⟨y, hp⟩, ↓reduceDIte] using
          (show ∃ y', (x', y') ∈ S from ⟨y, hp⟩).choose_spec
      have hW_sh : GraphShatters C ↑W := ⟨f, fun B hB => by
        obtain ⟨_, ⟨c, hc, rfl⟩, hcT⟩ := hS {p ∈ (↑S : Set (α × β)) | p.1 ∈ B} fun _ hp => hp.1
        refine ⟨c, hc, fun x hxB => ?_, fun x hx hceq => ?_⟩
        · exact of_decide_eq_true
            (show (x, f x) ∈ (fun p : α × β => decide (c p.1 = p.2)) ⁻¹' {true} ∩ ↑S from
              hcT ▸ ⟨hf_mem x (hB hxB), hxB⟩).1
        · exact hx.2 (show (x, f x) ∈ {p ∈ (↑S : Set (α × β)) | p.1 ∈ B} from
            hcT ▸ ⟨decide_eq_true hceq, hf_mem x hx.1⟩).2⟩
      rw [← card_image_of_injOn hinj]
      exact hW_sh.card_le_graphDim

/-- With `Bool` labels, graph shattering coincides with ordinary VC shattering. -/
theorem graphShatters_iff_setShatters {C : ConceptClass α Bool} {W : Set α} :
    GraphShatters C W ↔ SetShatters C W := by
  classical
  constructor
  · rintro ⟨f, h⟩ W' hW'
    obtain ⟨c, hc, h₀, h₁⟩ := h {x ∈ W | f x = decide (x ∈ W')} fun _ hx => hx.1
    refine ⟨c, hc, Set.ext fun x => ?_⟩
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    refine ⟨fun ⟨hcx, hx⟩ => ?_, fun hx => ⟨?_, hW' hx⟩⟩ <;>
      by_cases hB : f x = decide (x ∈ W')
    · simpa [hB, hcx] using (h₀ x ⟨hx, hB⟩).symm
    · have := h₁ x ⟨hx, fun hm => hB hm.2⟩
      cases hf : f x <;> cases hd : decide (x ∈ W') <;> simp_all
    · simpa [hx] using (h₀ x ⟨hW' hx, hB⟩).trans hB
    · have := h₁ x ⟨hW' hx, fun hm => hB hm.2⟩
      cases hf : f x <;> cases hc' : c x <;> simp_all
  · intro h
    refine ⟨fun _ => true, fun B hB => ?_⟩
    obtain ⟨c, hc, hcB⟩ := h B hB
    exact ⟨c, hc, fun x hx => (show x ∈ c ⁻¹' {true} ∩ W from hcB ▸ hx).1,
      fun x hx => by simpa [hx.1] using (show x ∉ c ⁻¹' {true} ∩ W from hcB ▸ hx.2)⟩

/-- With `Bool` labels, the graph and extended VC dimensions agree. -/
theorem graphDim_eq_evcDim (C : ConceptClass α Bool) : graphDim C = evcDim C := by
  simp only [graphDim, evcDim, graphShatters_iff_setShatters]

/-- **Sauer–Shelah growth bound for graph dimension** [Natarajan1989;
BenDavidCesaBianchiHausslerLong1995]: if `graphDim C ≤ d` and `β` is finite, `C` realizes at most
`∑_{i ≤ d} C(n |β|, i)` labelings on any `n` points `x : Fin n → α`. -/
theorem ncard_restriction_le_sum_choose_graphDim [Fintype β] {C : ConceptClass α β} {d : ℕ}
    (hd : graphDim C ≤ d) {n : ℕ} (x : Fin n → α) :
    ((· ∘ x) '' C).ncard ≤ ∑ i ∈ range (d + 1), (n * Fintype.card β).choose i := by
  classical
  let e : Fin (n * Fintype.card β) ≃ Fin n × β :=
    (finProdFinEquiv.symm.trans (Equiv.prodCongr (Equiv.refl _) (Fintype.equivFin β).symm))
  let pts : Fin (n * Fintype.card β) → α × β := fun j => ((x (e j).1), (e j).2)
  let encode : (Fin n → β) → (Fin (n * Fintype.card β) → Bool) :=
    fun v j => decide (v (e j).1 = (e j).2)
  have hinj : Function.Injective encode := fun v₁ v₂ heq => funext fun i => by
    have h := congrFun heq (e.symm (i, v₁ i))
    simp only [encode, Equiv.apply_symm_apply] at h
    exact (of_decide_eq_true h.symm).symm
  have hsub : encode '' ((· ∘ x) '' C) ⊆ restriction (conceptGraph C) pts := by
    rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    exact mem_restriction.mpr ⟨fun p => decide (c p.1 = p.2), ⟨c, hc, rfl⟩, fun _ => rfl⟩
  have hevc : ∀ W : Finset (α × β), SetShatters (conceptGraph C) ↑W → W.card ≤ d := fun W hW =>
    Nat.cast_le.mp (hW.card_le_evcDim.trans ((graphDim_eq_evcDim_conceptGraph C).symm.le.trans hd))
  calc ((· ∘ x) '' C).ncard
      = (encode '' ((· ∘ x) '' C)).ncard := (Set.ncard_image_of_injective _ hinj).symm
    _ ≤ (restriction (conceptGraph C) pts).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ growthFunction (conceptGraph C) (n * Fintype.card β) :=
        ncard_restriction_le_growthFunction (conceptGraph C) pts
    _ ≤ ∑ i ∈ range (d + 1), (n * Fintype.card β).choose i :=
        growthFunction_le_sum_choose hevc _

/-! ### Pseudo-cubes and the Daniely–Shalev-Shwartz (DS) dimension -/

/-- A finite set `P` of labelings `ι → β` is a **pseudo-cube** on `ι` if it is nonempty and every
`f ∈ P` and coordinate `i : ι` admits an *`i`-neighbor* `g ∈ P` differing from `f` exclusively at
coordinate `i` [DanielyShalevShwartz2014; BrukhimCarmonDinurMoranYehudayoff2022]. -/
@[expose] def IsPseudoCube (P : Finset (ι → β)) : Prop :=
  P.Nonempty ∧ ∀ f ∈ P, ∀ i : ι, ∃ g ∈ P, g i ≠ f i ∧ ∀ j, j ≠ i → g j = f j

/-- Precomposing along an injection projects a pseudo-cube onto a smaller coordinate set. -/
theorem IsPseudoCube.image_precomp [DecidableEq (κ → β)] {P : Finset (ι → β)}
    (hP : IsPseudoCube P) {e : κ → ι} (he : Function.Injective e) :
    IsPseudoCube (P.image (· ∘ e)) := by
  rcases hP with ⟨hne, hnbr⟩
  refine ⟨hne.image _, fun h hh k => ?_⟩
  rcases mem_image.mp hh with ⟨f, hfP, rfl⟩
  obtain ⟨g, hgP, hne_k, heq⟩ := hnbr f hfP (e k)
  exact ⟨g ∘ e, mem_image_of_mem _ hgP, hne_k, fun k' hk' => heq (e k') (he.ne hk')⟩

private theorem card_pseudoCube_fin :
    ∀ {n : ℕ} {P : Finset (Fin n → β)}, IsPseudoCube P → 2 ^ n ≤ P.card
  | 0, _, ⟨hne, _⟩ => by simpa using Finset.card_pos.mpr hne
  | n + 1, P, hP => by
    classical
    let P' : Finset (Fin n → β) := P.image (· ∘ Fin.succ)
    have hfib : ∀ t ∈ P', 2 ≤ (P.filter fun f => f ∘ Fin.succ = t).card := fun t ht => by
      rcases mem_image.mp ht with ⟨f, hfP, rfl⟩
      obtain ⟨g, hgP, h0, hother⟩ := hP.2 f hfP 0
      exact Finset.one_lt_card_iff.mpr ⟨g, f,
        mem_filter.mpr ⟨hgP, funext fun j => hother j.succ (Fin.succ_ne_zero j)⟩,
        mem_filter.mpr ⟨hfP, rfl⟩, fun heq => h0 (congrFun heq 0)⟩
    calc 2 ^ (n + 1)
        = 2 * 2 ^ n := by ring
      _ ≤ 2 * P'.card :=
          Nat.mul_le_mul_left 2 (card_pseudoCube_fin (hP.image_precomp (Fin.succ_injective n)))
      _ = ∑ _t ∈ P', 2 := by rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ t ∈ P', (P.filter fun f => f ∘ Fin.succ = t).card := sum_le_sum hfib
      _ = P.card := (card_eq_sum_card_fiberwise fun f hf => mem_image_of_mem _ hf).symm

/-- Every pseudo-cube on a finite coordinate set `ι` has at least `2 ^ |ι|` elements. -/
theorem IsPseudoCube.two_pow_card_le_card [Fintype ι] {P : Finset (ι → β)}
    (hP : IsPseudoCube P) : 2 ^ Fintype.card ι ≤ P.card := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hinj : Function.Injective (fun f : ι → β => f ∘ e) :=
    fun _ _ h => funext fun i => by simpa using congrFun h (e.symm i)
  exact (card_pseudoCube_fin (hP.image_precomp e.injective)).trans_eq
    (card_image_of_injective P hinj)

/-- Over a two-element label space, a finite family on `ι` is a pseudo-cube iff it is the entire
hypercube `Finset.univ`. -/
theorem isPseudoCube_iff_eq_univ_of_card_eq_two [DecidableEq ι] [Fintype ι] [Fintype β]
    (hβ : Fintype.card β = 2) (P : Finset (ι → β)) :
    IsPseudoCube P ↔ P = Finset.univ := by
  classical
  constructor
  · intro hP
    refine eq_univ_of_card P (le_antisymm (card_le_univ P) ?_)
    have hcard : Fintype.card (ι → β) = 2 ^ Fintype.card ι := by
      rw [Fintype.card_pi, prod_const, card_univ, hβ]
    exact hcard ▸ hP.two_pow_card_le_card
  · rintro rfl
    have : Nonempty β := Fintype.card_pos_iff.mp (by omega)
    refine ⟨univ_nonempty, fun f _ i => ?_⟩
    obtain ⟨b, hb⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card β) (f i)
    exact ⟨Function.update f i b, mem_univ _, by simp [hb],
      fun _ hj => Function.update_of_ne hj b f⟩

/-- A concept class `C` *DS-shatters* a set `W` if the restriction of `C` to `W` contains a
pseudo-cube on `W` [DanielyShalevShwartz2014; BrukhimCarmonDinurMoranYehudayoff2022]. -/
@[expose] def DSShatters (C : ConceptClass α β) (W : Set α) : Prop :=
  ∃ P : Finset (W → β), (↑P : Set (W → β)) ⊆ (fun c (x : W) => c x.1) '' C ∧ IsPseudoCube P

/-- The *Daniely–Shalev-Shwartz (DS) dimension* of `C` is the supremum in `ℕ∞` of the sizes of
finite DS-shattered sets [DanielyShalevShwartz2014; BrukhimCarmonDinurMoranYehudayoff2022]. -/
noncomputable def dsDim (C : ConceptClass α β) : ℕ∞ :=
  ⨆ W : Finset α, ⨆ _ : DSShatters C ↑W, (W.card : ℕ∞)

/-- The DS dimension is finite. -/
@[expose] def HasFiniteDSDim (C : ConceptClass α β) : Prop := dsDim C ≠ ⊤

/-- Only finite sets can be DS-shattered: each coordinate of `W` requires a distinct `i`-neighbor in
the finite pseudo-cube `P`. -/
theorem DSShatters.finite {C : ConceptClass α β} {W : Set α} (hW : DSShatters C W) :
    W.Finite := by
  obtain ⟨P, _, ⟨f, hfP⟩, hnbr⟩ := hW
  choose g hgP hne heq using hnbr f hfP
  have : Finite W := Finite.of_injective (fun x : W => (⟨g x, hgP x⟩ : P)) fun x₁ x₂ h =>
    by_contra fun hx => hne x₁ ((congrFun (congrArg Subtype.val h) x₁).trans (heq x₂ x₁ hx))
  exact Set.toFinite W

theorem DSShatters.subset {C : ConceptClass α β} {W V : Set α}
    (hW : DSShatters C W) (hVW : V ⊆ W) : DSShatters C V := by
  classical
  obtain ⟨P, hPsub, hP⟩ := hW
  refine ⟨P.image (· ∘ Set.inclusion hVW), fun _ hg => ?_,
    hP.image_precomp (Set.inclusion_injective hVW)⟩
  rcases mem_image.mp (mem_coe.mp hg) with ⟨_, hfP, rfl⟩
  obtain ⟨c, hc, rfl⟩ := hPsub hfP
  exact ⟨c, hc, rfl⟩

theorem DSShatters.superset {C C' : ConceptClass α β} {W : Set α}
    (hW : DSShatters C W) (hCC' : C ⊆ C') : DSShatters C' W :=
  let ⟨P, hPsub, hP⟩ := hW; ⟨P, hPsub.trans (Set.image_mono hCC'), hP⟩

theorem DSShatters.nonempty {C : ConceptClass α β} {W : Set α}
    (hW : DSShatters C W) : C.Nonempty :=
  let ⟨_, hPsub, ⟨_, hfP⟩, _⟩ := hW
  let ⟨c, hc, _⟩ := hPsub hfP
  ⟨c, hc⟩

theorem dsShatters_empty {C : ConceptClass α β} (hC : C.Nonempty) :
    DSShatters C ∅ :=
  let ⟨c, hc⟩ := hC
  ⟨{fun x : (∅ : Set α) => c x.1}, by simpa using ⟨c, hc, rfl⟩,
    singleton_nonempty _, fun _ _ i => i.2.elim⟩

/-- DS-shattering transfers along restrictions `e : γ → α`: if `(· ∘ e) '' C` DS-shatters `W`,
then `e` is injective on `W` and `C` DS-shatters `e '' W`. -/
theorem DSShatters.of_restrict {C : ConceptClass α β} {e : γ → α} {W : Set γ}
    (hW : DSShatters ((· ∘ e) '' C) W) : Set.InjOn e W ∧ DSShatters C (e '' W) := by
  classical
  obtain ⟨P, hPsub, ⟨f₀, hf₀⟩, hnbr⟩ := hW
  have hinj : Set.InjOn e W := fun i hi j hj hij => by_contra fun hne => by
    obtain ⟨g, hgP, hgi, hgj⟩ := hnbr f₀ hf₀ ⟨i, hi⟩
    obtain ⟨_, ⟨c₁, _, rfl⟩, hc₁⟩ := hPsub hf₀
    obtain ⟨_, ⟨c₂, _, rfl⟩, hc₂⟩ := hPsub hgP
    have hneq : (⟨j, hj⟩ : W) ≠ ⟨i, hi⟩ := fun h => hne (Subtype.mk.inj h).symm
    have h1 : c₁ (e i) = f₀ ⟨i, hi⟩ := congrFun hc₁ ⟨i, hi⟩
    have h2 : c₁ (e j) = f₀ ⟨j, hj⟩ := congrFun hc₁ ⟨j, hj⟩
    have h3 : c₂ (e i) = g ⟨i, hi⟩ := congrFun hc₂ ⟨i, hi⟩
    have h4 : c₂ (e j) = g ⟨j, hj⟩ := congrFun hc₂ ⟨j, hj⟩
    exact hgi (by rw [← h3, hij, h4, hgj ⟨j, hj⟩ hneq, ← h2, ← hij, h1])
  let eqv : W ≃ (e '' W) := Equiv.Set.imageOfInjOn e W hinj
  refine ⟨hinj, P.image (· ∘ eqv.symm), fun _ hg => ?_,
    IsPseudoCube.image_precomp ⟨⟨f₀, hf₀⟩, hnbr⟩ eqv.symm.injective⟩
  rcases mem_image.mp (mem_coe.mp hg) with ⟨_, hfP, rfl⟩
  obtain ⟨_, ⟨c, hc, rfl⟩, rfl⟩ := hPsub hfP
  exact ⟨c, hc, funext fun y => congrArg (fun z : e '' W => c z.1) (eqv.apply_symm_apply y).symm⟩

theorem DSShatters.card_le_dsDim {C : ConceptClass α β} {W : Finset α}
    (hW : DSShatters C ↑W) : (W.card : ℕ∞) ≤ dsDim C :=
  le_iSup₂_of_le W hW le_rfl

theorem dsDim_le_iff {C : ConceptClass α β} {d : ℕ∞} :
    dsDim C ≤ d ↔ ∀ W : Finset α, DSShatters C ↑W → (W.card : ℕ∞) ≤ d :=
  iSup₂_le_iff

theorem hasFiniteDSDim_iff {C : ConceptClass α β} :
    HasFiniteDSDim C ↔ ∃ n : ℕ, ∀ W : Finset α, DSShatters C ↑W → W.card ≤ n :=
  iSup_ne_top_iff

theorem hasFiniteDSDim_of_finite [Finite α] (C : ConceptClass α β) :
    HasFiniteDSDim C :=
  have := Fintype.ofFinite α
  hasFiniteDSDim_iff.mpr ⟨Fintype.card α, fun W _ => W.card_le_univ⟩

theorem exists_dsShatters_card_eq {C : ConceptClass α β} {d : ℕ}
    (hd : dsDim C = d) (hpos : 0 < d) :
    ∃ W : Finset α, W.card = d ∧ DSShatters C ↑W :=
  exists_finset_card_eq_of_iSup hd hpos

/-- For a finite set `W` and `Bool` labels, DS-shattering coincides with ordinary VC shattering. -/
theorem dsShatters_iff_setShatters {C : ConceptClass α Bool} {W : Finset α} :
    DSShatters C ↑W ↔ SetShatters C ↑W := by
  classical
  constructor
  · rintro ⟨P, hPsub, hP⟩ T hT
    have hPuniv : P = Finset.univ :=
      (isPseudoCube_iff_eq_univ_of_card_eq_two Fintype.card_bool P).mp hP
    obtain ⟨c, hc, hcf⟩ := hPsub (hPuniv ▸ mem_univ fun x : (↑W : Set α) => decide (x.1 ∈ T))
    refine ⟨c, hc, Set.ext fun x => ?_⟩
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun ⟨hcx, hxW⟩ => by simpa [hcx] using (congrFun hcf ⟨x, hxW⟩).symm,
      fun hxT => ⟨by simpa [hxT] using congrFun hcf ⟨x, hT hxT⟩, hT hxT⟩⟩
  · intro hsh
    refine ⟨Finset.univ, fun f _ => ?_,
      (isPseudoCube_iff_eq_univ_of_card_eq_two Fintype.card_bool _).mpr rfl⟩
    obtain ⟨c, hc, hcT⟩ :=
      hsh {x ∈ (↑W : Set α) | ∃ hx : x ∈ W, f ⟨x, hx⟩ = true} fun _ hx => hx.1
    refine ⟨c, hc, funext fun ⟨x, hxW⟩ => ?_⟩
    by_cases hfx : f ⟨x, hxW⟩ = true
    · exact (show x ∈ c ⁻¹' {true} ∩ ↑W from hcT ▸ ⟨hxW, hxW, hfx⟩).1.trans hfx.symm
    · have hnot : x ∉ c ⁻¹' {true} ∩ ↑W := fun hm =>
        let ⟨_, _, ht⟩ := hcT ▸ hm; hfx ht
      cases hcx : c x
      · exact hcx.trans (Bool.eq_false_iff.mpr hfx).symm
      · exact (hnot ⟨hcx, hxW⟩).elim

/-- With `Bool` labels, the DS and extended VC dimensions agree. -/
theorem dsDim_eq_evcDim (C : ConceptClass α Bool) : dsDim C = evcDim C := by
  simp only [dsDim, evcDim, dsShatters_iff_setShatters]

/-! ### The multiclass dimension hierarchy `natarajanDim ≤ dsDim ≤ graphDim` -/

/-- Every finite N-shattered set is DS-shattered via its embedded `2 ^ |W|` Boolean hypercube. -/
theorem NatarajanShatters.dsShatters {C : ConceptClass α β} {W : Finset α}
    (hW : NatarajanShatters C ↑W) : DSShatters C ↑W := by
  classical
  obtain ⟨f₀, f₁, hne, h⟩ := hW
  let cubeMap : Finset α → (↑W → β) := fun B x => if x.1 ∈ B then f₀ x.1 else f₁ x.1
  refine ⟨W.powerset.image cubeMap, fun _ hg => ?_,
    ⟨⟨cubeMap ∅, mem_image_of_mem _ (empty_mem_powerset W)⟩, fun _ hg i => ?_⟩⟩
  · rcases mem_image.mp (mem_coe.mp hg) with ⟨B, hBW, rfl⟩
    obtain ⟨c, hc, h₀, h₁⟩ := h ↑B (coe_subset.mpr (mem_powerset.mp hBW))
    refine ⟨c, hc, funext fun ⟨x, hxW⟩ => ?_⟩
    by_cases hxB : x ∈ B
    · simpa [cubeMap, hxB] using h₀ x hxB
    · simpa [cubeMap, hxB] using h₁ x ⟨hxW, hxB⟩
  · rcases mem_image.mp hg with ⟨B, hBW, rfl⟩
    let B' : Finset α := if i.1 ∈ B then B.erase i.1 else insert i.1 B
    have hB'W : B' ∈ W.powerset := mem_powerset.mpr <| by
      dsimp only [B']
      split_ifs
      · exact (erase_subset _ _).trans (mem_powerset.mp hBW)
      · exact insert_subset i.2 (mem_powerset.mp hBW)
    refine ⟨cubeMap B', mem_image_of_mem _ hB'W, ?_, fun j hj => ?_⟩
    · by_cases hiB : i.1 ∈ B <;> simp [cubeMap, B', hiB, hne i.1 i.2, (hne i.1 i.2).symm]
    · have hij : j.1 ≠ i.1 := fun heq => hj (Subtype.ext heq)
      by_cases hiB : i.1 ∈ B <;> simp [cubeMap, B', hiB, hij]

/-- Every finite DS-shattered set is G-shattered: starting from any anchor `f₀ ∈ P`, walking along
coordinate neighbors one element of `W \ B` at a time produces a labeling in `P` agreeing with `f₀`
on `B` and disagreeing with `f₀` on `W \ B`. -/
theorem DSShatters.graphShatters {C : ConceptClass α β} {W : Finset α}
    (hW : DSShatters C ↑W) : GraphShatters C ↑W := by
  classical
  obtain ⟨P, hPsub, ⟨f₀, hf₀⟩, hnbr⟩ := hW
  obtain ⟨c₀, _, hcf₀⟩ := hPsub hf₀
  have hwalk : ∀ D : Finset (↑W : Set α),
      ∃ h ∈ P, (∀ x ∈ D, h x ≠ f₀ x) ∧ ∀ x ∉ D, h x = f₀ x := fun D => by
    induction D using Finset.induction with
    | empty => exact ⟨f₀, hf₀, fun _ hx => (notMem_empty _ hx).elim, fun _ _ => rfl⟩
    | insert i D hiD ih =>
      obtain ⟨h, hhP, hneD, heqD⟩ := ih
      obtain ⟨h', hh'P, h'i, h'other⟩ := hnbr h hhP i
      refine ⟨h', hh'P, fun x hx => ?_, fun x hx => ?_⟩
      · rcases mem_insert.mp hx with rfl | hxD
        · exact heqD x hiD ▸ h'i
        · exact h'other x (fun heq => hiD (heq ▸ hxD)) ▸ hneD x hxD
      · exact (h'other x (fun heq => hx (heq ▸ mem_insert_self i D))).trans
          (heqD x fun hm => hx (mem_insert_of_mem hm))
  refine ⟨c₀, fun B hB => ?_⟩
  let D : Finset (↑W : Set α) := Finset.univ.filter fun x => x.1 ∉ B
  obtain ⟨h, hhP, hneD, heqD⟩ := hwalk D
  obtain ⟨c, hc, hch⟩ := hPsub hhP
  exact ⟨c, hc, fun x hxB =>
      (congrFun hch ⟨x, hB hxB⟩).trans
        ((heqD ⟨x, hB hxB⟩ (by simp [D, hxB])).trans (congrFun hcf₀ ⟨x, hB hxB⟩).symm),
    fun x hx => by
      have h1 : c x = h ⟨x, hx.1⟩ := congrFun hch ⟨x, hx.1⟩
      have h2 : c₀ x = f₀ ⟨x, hx.1⟩ := congrFun hcf₀ ⟨x, hx.1⟩
      rw [h1, h2]; exact hneD ⟨x, hx.1⟩ (by simp [D, hx.2])⟩

/-- Every N-shattered set is G-shattered. -/
theorem NatarajanShatters.graphShatters {C : ConceptClass α β} {W : Set α}
    (hW : NatarajanShatters C W) : GraphShatters C W :=
  let ⟨f₀, _, hne, h⟩ := hW
  ⟨f₀, fun B hB => let ⟨c, hc, h₀, h₁⟩ := h B hB
    ⟨c, hc, h₀, fun x hx => h₁ x hx ▸ (hne x hx.1).symm⟩⟩

/-- The Natarajan dimension never exceeds the Daniely–Shalev-Shwartz dimension. -/
theorem natarajanDim_le_dsDim (C : ConceptClass α β) : natarajanDim C ≤ dsDim C :=
  natarajanDim_le_iff.mpr fun _ hW => hW.dsShatters.card_le_dsDim

/-- The Daniely–Shalev-Shwartz dimension never exceeds the graph dimension. -/
theorem dsDim_le_graphDim (C : ConceptClass α β) : dsDim C ≤ graphDim C :=
  dsDim_le_iff.mpr fun _ hW => hW.graphShatters.card_le_graphDim

/-- The Natarajan dimension never exceeds the graph dimension. -/
theorem natarajanDim_le_graphDim (C : ConceptClass α β) : natarajanDim C ≤ graphDim C :=
  (natarajanDim_le_dsDim C).trans (dsDim_le_graphDim C)

/-! ### Quantitative equivalence over finite label spaces (`O(d log |β|)`) -/

/-- If `C` G-shatters `W` and N-shatters no finite set of size exceeding `d`, then
`2 ^ |W| ≤ natarajanSum |W| |β| d`. -/
theorem GraphShatters.two_pow_card_le_natarajanSum [Fintype β] {C : ConceptClass α β}
    {W : Finset α} {d : ℕ} (hW : GraphShatters C ↑W)
    (hd : ∀ V : Finset α, NatarajanShatters C ↑V → V.card ≤ d) :
    2 ^ W.card ≤ natarajanSum W.card (Fintype.card β) d := by
  classical
  obtain ⟨f, hf⟩ := hW
  let e : Fin W.card → α := fun i => (W.equivFin.symm i).1
  let proj : (Fin W.card → β) → Finset (Fin W.card) :=
    fun g => Finset.univ.filter fun i => g i = f (e i)
  have hsurj : (Set.univ : Set (Finset (Fin W.card))) ⊆ proj '' ((· ∘ e) '' C) := fun s _ => by
    obtain ⟨c, hc, h₀, h₁⟩ := hf {x ∈ (↑W : Set α) | ∃ i ∈ s, e i = x} fun _ hx => hx.1
    refine ⟨c ∘ e, ⟨c, hc, rfl⟩, ext fun i => ?_⟩
    simp only [proj, mem_filter, mem_univ, true_and, Function.comp_apply]
    refine ⟨fun hceq => by_contra fun his => h₁ (e i) ⟨(W.equivFin.symm i).2, ?_⟩ hceq,
      fun his => h₀ (e i) ⟨(W.equivFin.symm i).2, i, his, rfl⟩⟩
    rintro ⟨_, ⟨j, hjs, hej⟩⟩
    exact his (W.equivFin.symm.injective (Subtype.ext hej) ▸ hjs)
  calc 2 ^ W.card
      = (Set.univ : Set (Finset (Fin W.card))).ncard := by simp [Set.ncard_univ]
    _ ≤ (proj '' ((· ∘ e) '' C)).ncard := Set.ncard_le_ncard hsurj (Set.toFinite _)
    _ ≤ ((· ∘ e) '' C).ncard := Set.ncard_image_le (Set.toFinite _)
    _ ≤ natarajanSum W.card (Fintype.card β) d := ncard_restriction_le_natarajanSum hd e

/-- **Ben-David–Cesa-Bianchi–Haussler–Long `O(d log |β|)` graph-dimension bound**
[BenDavidCesaBianchiHausslerLong1995]: over a finite label space `β`, if every finite N-shattered
set of `C` has size at most `d`, then every finite G-shattered set of `C` has size at most
`4 * d * (⌊log₂ |β|⌋ + 2)`. -/
theorem card_le_of_graphShatters [Fintype β] {C : ConceptClass α β} {W : Finset α} {d : ℕ}
    (hW : GraphShatters C ↑W) (hd : ∀ V : Finset α, NatarajanShatters C ↑V → V.card ≤ d) :
    W.card ≤ 4 * d * (Nat.log 2 (Fintype.card β) + 2) := by
  set k := Fintype.card β
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · have : IsEmpty β := Fintype.card_eq_zero_iff.mp hk0
    rcases W.eq_empty_or_nonempty with rfl | ⟨x, _⟩
    · simp
    · exact isEmptyElim (hW.choose x)
  rcases Nat.eq_zero_or_pos d with rfl | hdpos
  · have h := hW.two_pow_card_le_natarajanSum hd
    rw [natarajanSum_zero_right] at h
    by_contra hne
    have : 1 < 2 ^ W.card := Nat.one_lt_pow (by omega) (by decide)
    omega
  set s := 2 * d * (Nat.log 2 k + 2)
  suffices hlt : W.card < 2 * s by
    have : 2 * s = 4 * d * (Nat.log 2 k + 2) := by dsimp only [s]; ring
    omega
  by_contra hge
  obtain ⟨V, hVW, hVcard⟩ := exists_subset_card_eq (not_lt.mp hge)
  have hsum : 2 ^ (2 * s) ≤ natarajanSum (2 * s) k d := by
    simpa only [hVcard] using (hW.subset (coe_subset.mpr hVW)).two_pow_card_le_natarajanSum hd
  have hchoose2 : k.choose 2 ≤ k ^ 2 := by
    rw [Nat.choose_two_right, sq]
    exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  have hnatar :
      natarajanSum (2 * s) k d ≤ (∑ i ∈ range (d + 1), (2 * s).choose i) * k ^ (2 * d) := by
    calc natarajanSum (2 * s) k d
        ≤ ∑ i ∈ range (d + 1), (2 * s).choose i * (k ^ 2) ^ d :=
          sum_le_sum fun i hi => Nat.mul_le_mul_left _ <|
            (Nat.pow_le_pow_left hchoose2 i).trans
              (Nat.pow_le_pow_right (by positivity) (Nat.lt_succ_iff.mp (mem_range.mp hi)))
      _ = _ := by rw [← sum_mul, ← pow_mul]
  have hmul3 : 2 ^ (2 * s) * 3 ^ (2 * s) ≤ 3 ^ d * 4 ^ (2 * s) * k ^ (2 * d) := by
    calc 2 ^ (2 * s) * 3 ^ (2 * s)
        ≤ (∑ i ∈ range (d + 1), (2 * s).choose i) * 3 ^ (2 * s) * k ^ (2 * d) := by
          have := Nat.mul_le_mul_right (3 ^ (2 * s)) (hsum.trans hnatar)
          linarith
      _ ≤ 3 ^ d * 4 ^ (2 * s) * k ^ (2 * d) :=
          Nat.mul_le_mul_right _ (Cslib.sum_range_choose_mul_pow_le 3 (2 * s) d)
  have h9le : 9 ^ s ≤ 4 ^ s * (3 ^ d * k ^ (2 * d)) := by
    refine Nat.le_of_mul_le_mul_left ?_ (by positivity : 0 < 2 ^ (2 * s))
    have h4 : (4 : ℕ) ^ (2 * s) = 2 ^ (2 * s) * 4 ^ s := by
      rw [pow_mul, show (4 : ℕ) ^ 2 = 2 ^ 2 * 4 by decide, mul_pow, ← pow_mul]
    have h9 : (3 : ℕ) ^ (2 * s) = 9 ^ s := by rw [pow_mul]; rfl
    rw [h4, h9] at hmul3; linarith
  have hcoeff_lt : 3 ^ d * k ^ (2 * d) < 2 ^ s := by
    have h3lt : 3 ^ d < 2 ^ (2 * d) := by
      rw [pow_mul]
      exact Nat.pow_lt_pow_left (by decide) hdpos.ne'
    have hkle : k ^ (2 * d) ≤ 2 ^ ((Nat.log 2 k + 1) * (2 * d)) :=
      (Nat.pow_le_pow_left (Nat.lt_pow_succ_log_self (by decide : 1 < 2) k).le _).trans_eq
        (pow_mul ..).symm
    calc 3 ^ d * k ^ (2 * d)
        < 2 ^ (2 * d) * k ^ (2 * d) := Nat.mul_lt_mul_of_pos_right h3lt (by positivity)
      _ ≤ 2 ^ (2 * d) * 2 ^ ((Nat.log 2 k + 1) * (2 * d)) := Nat.mul_le_mul_left _ hkle
      _ = 2 ^ s := by
        rw [← pow_add]
        congr 1
        dsimp only [s]
        ring
  have h9lt8 : 9 ^ s < 8 ^ s :=
    h9le.trans_lt <|
      (Nat.mul_lt_mul_of_pos_left hcoeff_lt (by positivity)).trans_eq (mul_pow 4 2 s).symm
  exact absurd h9lt8 (not_lt_of_ge (Nat.pow_le_pow_left (by decide : 8 ≤ 9) s))

/-- Over a finite label space, `graphDim C ≤ 4 * natarajanDim C * (⌊log₂ |β|⌋ + 2)`. -/
theorem graphDim_le_mul_natarajanDim [Fintype β] (C : ConceptClass α β) :
    graphDim C ≤ 4 * natarajanDim C * (Nat.log 2 (Fintype.card β) + 2) := by
  rcases eq_or_ne (natarajanDim C) ⊤ with htop | hfin
  · simp [htop]
  · obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp hfin
    rw [← hd]
    refine graphDim_le_iff.mpr fun W hW => ?_
    exact_mod_cast card_le_of_graphShatters hW fun V hV =>
      Nat.cast_le.mp (hd ▸ hV.card_le_natarajanDim)

/-- Over a finite label space, `dsDim C ≤ 4 * natarajanDim C * (⌊log₂ |β|⌋ + 2)`. -/
theorem dsDim_le_mul_natarajanDim [Fintype β] (C : ConceptClass α β) :
    dsDim C ≤ 4 * natarajanDim C * (Nat.log 2 (Fintype.card β) + 2) :=
  (dsDim_le_graphDim C).trans (graphDim_le_mul_natarajanDim C)

/-- Over a finite label space, `graphDim C` is finite iff `natarajanDim C` is finite. -/
theorem hasFiniteGraphDim_iff_hasFiniteNatarajanDim [Finite β] (C : ConceptClass α β) :
    HasFiniteGraphDim C ↔ HasFiniteNatarajanDim C := by
  have := Fintype.ofFinite β
  refine ⟨fun h => ne_top_of_le_ne_top h (natarajanDim_le_graphDim C), fun h => ?_⟩
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp h
  refine ne_top_of_le_ne_top (ENat.natCast_ne_top (4 * d * (Nat.log 2 (Fintype.card β) + 2))) ?_
  simpa only [← hd, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using graphDim_le_mul_natarajanDim C

/-- Over a finite label space, `dsDim C` is finite iff `natarajanDim C` is finite. -/
theorem hasFiniteDSDim_iff_hasFiniteNatarajanDim [Finite β] (C : ConceptClass α β) :
    HasFiniteDSDim C ↔ HasFiniteNatarajanDim C :=
  ⟨fun h => ne_top_of_le_ne_top h (natarajanDim_le_dsDim C),
    fun h => ne_top_of_le_ne_top ((hasFiniteGraphDim_iff_hasFiniteNatarajanDim C).mpr h)
      (dsDim_le_graphDim C)⟩

/-! ### Separation 1: Finite-label (`|β| = 3`) separation `natarajanDim < dsDim` -/

/-- The 6-cycle ("hexagon") concept class `{f : Fin 2 → Fin 3 | f 0 ≠ f 1}` on two points and
three labels [DanielyShalevShwartz2014; BrukhimCarmonDinurMoranYehudayoff2022]. -/
@[expose] def hexagonClass : ConceptClass (Fin 2) (Fin 3) :=
  {f | f 0 ≠ f 1}

/-- `hexagonClass` has Natarajan dimension `1`: no `2 × 2` Cartesian product fits inside the
off-diagonal of `Fin 3 × Fin 3`. -/
theorem natarajanDim_hexagonClass : natarajanDim hexagonClass = 1 := by
  refine le_antisymm (natarajanDim_le_iff.mpr fun W hW => ?_) ?_
  · by_contra hgt
    have hcard2 : 2 ≤ W.card := by
      have : ¬ W.card ≤ 1 := fun h => hgt (by exact_mod_cast h)
      omega
    obtain rfl : W = Finset.univ :=
      eq_univ_of_card W (le_antisymm (card_le_univ W) (by simpa using hcard2))
    obtain ⟨f₀, f₁, hne, h⟩ := hW
    obtain ⟨_, hc_all, ha₀, _⟩ := h ↑(Finset.univ : Finset (Fin 2)) Set.Subset.rfl
    obtain ⟨_, hc_emp, _, he₁⟩ := h ∅ (Set.empty_subset _)
    obtain ⟨_, hc_0, h0₀, h0₁⟩ := h {0} (by simp)
    obtain ⟨_, hc_1, h1₀, h1₁⟩ := h {1} (by simp)
    let S₀ : Finset (Fin 3) := {f₀ 0, f₁ 0}
    let S₁ : Finset (Fin 3) := {f₀ 1, f₁ 1}
    have hdisj : Disjoint S₀ S₁ := Finset.disjoint_left.mpr fun y hy0 hy1 => by
      simp only [S₀, S₁, mem_insert, mem_singleton] at hy0 hy1
      rcases hy0 with rfl | rfl <;> rcases hy1 with h | h
      · exact (by rwa [← ha₀ 0 (by simp), ← ha₀ 1 (by simp)] : f₀ 0 ≠ f₀ 1) h
      · exact (by rwa [← h0₀ 0 rfl, ← h0₁ 1 ⟨by simp, by decide⟩] : f₀ 0 ≠ f₁ 1) h
      · exact (by rwa [← h1₁ 0 ⟨by simp, by decide⟩, ← h1₀ 1 rfl] : f₁ 0 ≠ f₀ 1) h
      · exact (by rwa [← he₁ 0 (by simp), ← he₁ 1 (by simp)] : f₁ 0 ≠ f₁ 1) h
    have hcard4 : (S₀ ∪ S₁).card = 4 := by
      rw [card_union_of_disjoint hdisj, card_pair (hne 0 (by simp)), card_pair (hne 1 (by simp))]
    have hle3 : (S₀ ∪ S₁).card ≤ 3 := (card_le_univ _).trans_eq (by simp)
    omega
  · have hsh : NatarajanShatters hexagonClass (↑({0} : Finset (Fin 2)) : Set (Fin 2)) := by
      refine ⟨fun _ => 0, fun _ => 1, fun _ _ => by simp, fun B hB => ?_⟩
      by_cases h0B : (0 : Fin 2) ∈ B
      · exact ⟨![0, 2], by simp [hexagonClass],
          fun x hx => by simp [show x = 0 by simpa using hB hx],
          fun x hx => ((show x = 0 by simpa using hx.1) ▸ hx.2 <| h0B).elim⟩
      · exact ⟨![1, 2], by simp [hexagonClass],
          fun x hx => (h0B <| (show x = 0 by simpa using hB hx) ▸ hx).elim,
          fun x hx => by simp [show x = 0 by simpa using hx.1]⟩
    simpa using hsh.card_le_natarajanDim

/-- `hexagonClass` DS-shatters `{0, 1}` as a 2-dimensional 6-cycle pseudo-cube, so
`dsDim hexagonClass = 2`. -/
theorem dsDim_hexagonClass : dsDim hexagonClass = 2 := by
  refine le_antisymm
    (dsDim_le_iff.mpr fun W _ => by exact_mod_cast (card_le_univ W).trans_eq (by simp)) ?_
  classical
  let W : Finset (Fin 2) := Finset.univ
  let x₀ : (↑W : Set (Fin 2)) := ⟨0, mem_univ 0⟩
  let x₁ : (↑W : Set (Fin 2)) := ⟨1, mem_univ 1⟩
  let P : Finset (↑W → Fin 3) := Finset.univ.filter fun g => g x₀ ≠ g x₁
  have hsh : DSShatters hexagonClass ↑W := by
    refine ⟨P, fun g hg => ⟨fun u => g ⟨u, mem_univ u⟩, (mem_filter.mp hg).2,
        funext fun ⟨_, _⟩ => rfl⟩,
      ⟨⟨fun x => if x = x₀ then 0 else 1, by simp [P, x₀, x₁]⟩, fun f _ i => ?_⟩⟩
    obtain ⟨b, hb0, hb1⟩ := (by decide : ∀ a b : Fin 3, ∃ c : Fin 3, c ≠ a ∧ c ≠ b) (f x₀) (f x₁)
    refine ⟨Function.update f i b, mem_filter.mpr ⟨mem_univ _, ?_⟩, ?_,
      fun _ hj => Function.update_of_ne hj b f⟩
    · rcases i with ⟨u, _⟩; fin_cases u
      · change Function.update f x₀ b x₀ ≠ Function.update f x₀ b x₁
        rw [Function.update_self, Function.update_of_ne (by decide : x₁ ≠ x₀)]
        exact hb1
      · change Function.update f x₁ b x₀ ≠ Function.update f x₁ b x₁
        rw [Function.update_self, Function.update_of_ne (by decide : x₀ ≠ x₁)]
        exact hb0.symm
    · rcases i with ⟨u, _⟩; fin_cases u
      · exact hb0
      · exact hb1
  simpa [W] using hsh.card_le_dsDim

/-- `hexagonClass` also has graph dimension `2`. -/
theorem graphDim_hexagonClass : graphDim hexagonClass = 2 :=
  le_antisymm (graphDim_le_iff.mpr fun W _ => by exact_mod_cast (card_le_univ W).trans_eq (by simp))
    (dsDim_hexagonClass ▸ dsDim_le_graphDim hexagonClass)

/-! ### Separation 2: Infinite-label separation `dsDim = 1 < ⊤ = graphDim` -/

/-- Revealing-subset concept associated with `B : Finset α`: outputs `none` on `B` and reveals the
entire active set `some B` outside `B` [BenDavidCesaBianchiHausslerLong1995;
DanielyShalevShwartz2014]. -/
@[expose] def revealingConcept [DecidableEq α] (B : Finset α) (x : α) : Option (Finset α) :=
  if x ∈ B then none else some B

/-- The *revealing-subset class* `{revealingConcept B | B : Finset α}`: every finite subset is
G-shattered against constant `none`, yet any non-`none` label uniquely identifies `B`, preventing
any 2-dimensional pseudo-cube. -/
@[expose] def revealingSetClass (α : Type*) [DecidableEq α] :
    ConceptClass α (Option (Finset α)) :=
  Set.range revealingConcept

/-- `revealingSetClass α` G-shatters every finite subset `W : Finset α`. -/
theorem graphShatters_revealingSetClass [DecidableEq α] (W : Finset α) :
    GraphShatters (revealingSetClass α) ↑W := by
  classical
  refine ⟨fun _ => none, fun B₀ hB₀ => ?_⟩
  let B : Finset α := W.filter (· ∈ B₀)
  exact ⟨revealingConcept B, ⟨B, rfl⟩,
    fun x hx => by have hxW : x ∈ W := hB₀ hx; simp [revealingConcept, B, hxW, hx],
    fun x hx => by simp [revealingConcept, B, hx.2]⟩

/-- On any infinite domain, `revealingSetClass α` has infinite graph dimension (`⊤`). -/
theorem graphDim_revealingSetClass_of_infinite [DecidableEq α] [Infinite α] :
    graphDim (revealingSetClass α) = ⊤ := by
  by_contra hne
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne
  obtain ⟨W, hWcard⟩ := Infinite.exists_subset_card_eq α (n + 1)
  have hle : ((n + 1 : ℕ) : ℕ∞) ≤ n := by
    simpa only [hWcard, ← hn] using (graphShatters_revealingSetClass W).card_le_graphDim
  exact absurd (Nat.cast_le.mp hle) (by omega)

/-- No set of two or more points is DS-shattered by `revealingSetClass α`. -/
theorem card_le_one_of_dsShatters_revealingSetClass [DecidableEq α] {W : Finset α}
    (hW : DSShatters (revealingSetClass α) ↑W) : W.card ≤ 1 := by
  by_contra hgt
  obtain ⟨x₁, hx₁, x₂, hx₂, hxne⟩ := one_lt_card.mp (by omega : 1 < W.card)
  let i₁ : (↑W : Set α) := ⟨x₁, hx₁⟩
  let i₂ : (↑W : Set α) := ⟨x₂, hx₂⟩
  have hine : i₁ ≠ i₂ := fun h => hxne (Subtype.mk.inj h)
  obtain ⟨P, hPsub, ⟨g₀, hg₀⟩, hnbr⟩ := hW
  have no_some : ∀ g ∈ P, ∀ (i : ↑W) (B : Finset α), g i ≠ some B := fun g hg i B hgi => by
    let j : (↑W : Set α) := if i = i₁ then i₂ else i₁
    have hji : j ≠ i := by
      by_cases hi : i = i₁
      · subst hi; simpa [j] using hine.symm
      · simpa [j, hi] using Ne.symm hi
    obtain ⟨g', hg'P, hgj_ne, hgj_eq⟩ := hnbr g hg j
    obtain ⟨_, ⟨B₁, rfl⟩, hB₁⟩ := hPsub hg
    obtain ⟨_, ⟨B₂, rfl⟩, hB₂⟩ := hPsub hg'P
    have hinv : ∀ {B' : Finset α}, revealingConcept B' i.1 = some B → B' = B := fun h => by
      simp only [revealingConcept] at h
      split_ifs at h
      exact Option.some.inj h
    have hB₁_eq : B₁ = B := hinv ((congrFun hB₁ i).trans hgi)
    have hB₂_eq : B₂ = B := hinv ((congrFun hB₂ i).trans ((hgj_eq i hji.symm).trans hgi))
    have hgg' : g' = g := by rw [← hB₂, hB₂_eq, ← hB₁_eq, hB₁]
    exact hgj_ne (congrFun hgg' j)
  cases hg0_val : g₀ i₁ with
  | some B => exact no_some g₀ hg₀ i₁ B hg0_val
  | none =>
    obtain ⟨g₁, hg₁, hg₁_ne, _⟩ := hnbr g₀ hg₀ i₁
    cases hg1_val : g₁ i₁ with
    | none => exact hg₁_ne (hg1_val.trans hg0_val.symm)
    | some B => exact no_some g₁ hg₁ i₁ B hg1_val

private theorem natarajanShatters_singleton_revealingSetClass [DecidableEq α] (x₀ : α) :
    NatarajanShatters (revealingSetClass α) (↑({x₀} : Finset α) : Set α) := by
  refine ⟨fun _ => none, fun _ => some ∅, fun _ _ => by simp, fun B hB => ?_⟩
  by_cases hxB : x₀ ∈ B
  · exact ⟨revealingConcept {x₀}, ⟨{x₀}, rfl⟩,
      fun x hx => by simp [revealingConcept, show x = x₀ by simpa using hB hx],
      fun x hx => ((show x = x₀ by simpa using hx.1) ▸ hx.2 <| hxB).elim⟩
  · exact ⟨revealingConcept ∅, ⟨∅, rfl⟩,
      fun x hx => (hxB <| (show x = x₀ by simpa using hB hx) ▸ hx).elim,
      fun _ _ => by simp [revealingConcept]⟩

/-- On any nonempty domain, `revealingSetClass α` has DS dimension `1`. -/
theorem dsDim_revealingSetClass [DecidableEq α] [Nonempty α] :
    dsDim (revealingSetClass α) = 1 := by
  obtain ⟨x₀⟩ := ‹Nonempty α›
  have hle1 : dsDim (revealingSetClass α) ≤ 1 :=
    dsDim_le_iff.mpr fun W hW => by exact_mod_cast card_le_one_of_dsShatters_revealingSetClass hW
  have hge1 : (1 : ℕ∞) ≤ natarajanDim (revealingSetClass α) := by
    simpa using (natarajanShatters_singleton_revealingSetClass x₀).card_le_natarajanDim
  exact le_antisymm hle1 (hge1.trans (natarajanDim_le_dsDim _))

/-- On any nonempty domain, `revealingSetClass α` has Natarajan dimension `1`. -/
theorem natarajanDim_revealingSetClass [DecidableEq α] [Nonempty α] :
    natarajanDim (revealingSetClass α) = 1 := by
  obtain ⟨x₀⟩ := ‹Nonempty α›
  exact le_antisymm
    ((natarajanDim_le_dsDim _).trans_eq dsDim_revealingSetClass)
    (by simpa using (natarajanShatters_singleton_revealingSetClass x₀).card_le_natarajanDim)

end Cslib.MachineLearning.PACLearning
