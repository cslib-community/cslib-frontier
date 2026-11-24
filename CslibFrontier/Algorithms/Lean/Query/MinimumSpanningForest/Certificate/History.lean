/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.Certificate.Correctness
public import CslibFrontier.Foundations.Combinatorics.MaximaVectors
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.PathMaxima
-- `import all` only to unfold the preference rule (`pref`, `PrefersFind`, `Projectable`, `spokes`,
-- `State.proj`) and `prefSeq`, which their modules do not expose.
import all CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.Certificate.Correctness
import all CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.Certificate.Instance
import all CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.Certificate.State
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Sqrt
import CslibFrontier.Foundations.Data.Nat.Choose.Real
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Choose.Vandermonde

/-!
# Histories of the certificate procedure

The history bound of [Khanna, Putterman and Song][KhannaPuttermanSong2026] (§3.4, Definition 3.8,
p. 18, and Lemma 3.10, pp. 19–20) for the program `Cslib.Query.Certificate.certificate`. These are
steps in the proof of [KhannaPuttermanSong2026] Theorem 4.1 (#8325), not results of their own.

The **history** of a call (Definition 3.8) records, at the start of each of its `t²` rounds, the
spokes `σᵢ`, the forest `Fᵢ` and the vector `aᵢ` of true preferred actions of its edges
(`Cslib.Query.Certificate.HistoryRound`, `Cslib.Query.Certificate.history`). It determines the bad
rounds of every edge. Lemma 3.10 bounds the number of histories that can occur, as the weights
vary, by a family `Cslib.Query.Certificate.histories γ inst` that depends only on the
combinatorial data of the instance: `log |𝓗| ≤ 7 t² √(m n)`
(`Cslib.Query.Certificate.log_card_histories_le`). The actual history under the comparison oracle
of any injective weights lies in it (`Cslib.Query.Certificate.history_mem_histories`).

The family is the product over the rounds of the following choices, as in the paper:

* the spokes, `∏ (deg v + 1)` choices (`Cslib.Query.Certificate.spokeChoices`);
* the forest, a set of at most `n - 1` edges, `C(m + n - 1, n - 1)` choices
  (`Cslib.Query.Certificate.forestChoices`);
* given the spokes and the forest, the preference vector, from the family
  `Cslib.Query.Certificate.prefFamily` of at most `C(m + 2n, 2n)` vectors.

**Preference vectors** (p. 20). Given the spokes and the forest, the preference of an edge `e` with
ends `u, v` is forced to *find* when it is not projectable, and to *project* when it is
projectable but `F` does not join `u` and `v`. For the remaining, *contested* edges
(`Cslib.Query.Certificate.Contested`), the preference is *find* exactly when the maximum of the set
`S_e` (`Cslib.Query.Certificate.candidates`) is a spoke, where `S_e` consists of the spokes `σ(u)`,
`σ(v)` and the forest edges of the path from `u` to `v`, for the order of the weights in which
spokes win ties (`Cslib.Query.Certificate.fst_eq_true_iff_prefersFind`). Lemma 3.9 then bounds the
number of such vectors (`Cslib.exists_maxima_vectors_card_le_choose`).

Two choices make this precise.

* **A tagged ground set.** A spoke can also be a forest edge, so the ground set is
  `Bool × E`, spokes tagged `true` and forest edges `false`, ordered by
  `Cslib.Query.Certificate.tagKey`: weight first, then tag. Spokes then win ties in a genuine
  linear order.
* **Path edges without paths.** The forest edges of the path between the ends of `e` are the forest
  edges whose removal separates them (`Cslib.Query.Certificate.pathEdges`), a definition that does
  not depend on the weights. For an acyclic forest joining the ends, the forest edges no heavier
  than `k` join the ends exactly when every path edge is no heavier than `k`
  (`Cslib.Query.Certificate.joins_le_iff_forall_mem_pathEdges`); the bottleneck edge of M2 is a
  path edge.

The family `prefFamily st I` is defined for any set `I` of edges, so that the estimator of §3.5
(`Cslib.Query.Certificate.estimator`) uses it on the edges acting in a round.

## Main definitions

* `Cslib.Query.Certificate.pathEdges`, `Cslib.Query.Certificate.Contested`,
  `Cslib.Query.Certificate.candidates`, `Cslib.Query.Certificate.tagKey`.
* `Cslib.Query.Certificate.prefVector`: the true preferences on a set of edges, *find* elsewhere.
* `Cslib.Query.Certificate.prefFamily`: the preference vectors that the spokes and the forest
  allow.
* `Cslib.Query.Certificate.HistoryRound`, `Cslib.Query.Certificate.history`,
  `Cslib.Query.Certificate.histories`.

## Main results

* `Cslib.Query.Certificate.fst_eq_true_iff_prefersFind`: a contested edge prefers *find* exactly
  when the maximum of its candidate set is a spoke (p. 20).
* `Cslib.Query.Certificate.prefVector_mem_prefFamily`,
  `Cslib.Query.Certificate.card_prefFamily_le_choose`: the true preferences are in the family, of
  at most `C(|I| + 2n, 2n)` vectors (p. 20, via Lemma 3.9).
* `Cslib.Query.Certificate.history_mem_histories`: the actual history is in the family.
* `Cslib.Query.Certificate.log_card_histories_le`: **Lemma 3.10**, `log |𝓗| ≤ 7 t² √(m n)`.

## References

* [S. Khanna, A. Putterman and J. Song, *A Deterministic Linear Time Algorithm for Minimum
  Spanning Tree*][KhannaPuttermanSong2026], §3.4, pp. 18–20.
-/

public section

namespace Cslib.Query.Certificate

open Finset Multigraph

variable {V E W : Type} [DecidableEq V] [DecidableEq E]

/-! ### Path edges and contested edges -/

section Path

open scoped Classical in
/-- The **path edges** of `e`: the forest edges whose removal separates the ends of `e`. When the
forest is acyclic and joins the ends, these are the edges of the path between them. -/
noncomputable def pathEdges (st : State V E) (e : E) : Finset E :=
  {f ∈ st.forest | ∀ a b, st.ends e = s(a, b) → ¬Joins st.ends ((st.forest : Set E) \ {f}) a b}

omit [DecidableEq V] [DecidableEq E] in
theorem mem_pathEdges {st : State V E} {e f : E} :
    f ∈ pathEdges st e ↔ f ∈ st.forest ∧
      ∀ a b, st.ends e = s(a, b) → ¬Joins st.ends ((st.forest : Set E) \ {f}) a b := by
  classical
  simp [pathEdges]

omit [DecidableEq V] [DecidableEq E] in
theorem pathEdges_subset (st : State V E) (e : E) : pathEdges st e ⊆ st.forest :=
  fun _ hf => (mem_pathEdges.1 hf).1

variable [LinearOrder W] {w : E → W}

omit [DecidableEq V] [DecidableEq E] in
/-- In an acyclic set of edges, a bottleneck edge between `u` and `v` separates them. -/
private theorem not_joins_sdiff_of_bottleneck {ends : E → Sym2 V} {F : Set E}
    (hw : Function.Injective w) (hF : IsAcyclic ends F) {g : E} (hg : g ∈ F) {u v : V}
    (hle : Joins ends {x | x ∈ F ∧ w x ≤ w g} u v)
    (hlt : ¬Joins ends {x | x ∈ F ∧ w x < w g} u v) :
    ¬Joins ends (F \ {g}) u v := by
  intro h
  have hsub : {x | x ∈ F ∧ w x ≤ w g} ⊆ insert g {x | x ∈ F ∧ w x < w g} := by
    rintro x ⟨hx, hxg⟩
    rcases hxg.lt_or_eq with hxg | hxg
    · exact Set.mem_insert_of_mem _ ⟨hx, hxg⟩
    · rw [hw hxg]
      exact Set.mem_insert _ _
  have hL : {x | x ∈ F ∧ w x < w g} ⊆ F \ {g} := by
    rintro x ⟨hx, hxg⟩
    refine ⟨hx, fun hxe => ?_⟩
    rw [Set.mem_singleton_iff.1 hxe] at hxg
    exact lt_irrefl _ hxg
  rcases joins_insert_iff.1 (hle.mono hsub) with h' | ⟨x, y, hxy, hux, hyv⟩
  · exact hlt h'
  · exact isAcyclic_iff.1 hF g hg x y hxy ((hux.mono hL).symm.trans (h.trans (hyv.mono hL).symm))

omit [DecidableEq E] in
/-- **Threshold connectivity through the path edges.** For an acyclic forest joining the ends
`u, v` of `e`, the forest edges no heavier than `k` join `u` and `v` exactly when every path edge
of `e` is no heavier than `k`. -/
theorem joins_le_iff_forall_mem_pathEdges (hw : Function.Injective w) {st : State V E}
    (hF : IsAcyclic st.ends (st.forest : Set E)) {e : E} {u v : V} (huv : st.ends e = s(u, v))
    (hj : Joins st.ends (st.forest : Set E) u v) (k : W) :
    Joins st.ends {f | f ∈ st.forest ∧ w f ≤ k} u v ↔ ∀ f ∈ pathEdges st e, w f ≤ k := by
  constructor
  · intro h f hf
    by_contra hk
    refine (mem_pathEdges.1 hf).2 u v huv (h.mono ?_)
    rintro g ⟨hg, hgk⟩
    refine ⟨hg, fun hgf => hk ?_⟩
    rw [Set.mem_singleton_iff.1 hgf] at hgk
    exact hgk
  · intro h
    by_cases hne : u = v
    · subst hne
      exact Joins.refl _
    obtain ⟨g, hgF, hgle, hglt⟩ := exists_bottleneck (w := w) hne hj
    have hg : g ∈ pathEdges st e := by
      refine mem_pathEdges.2 ⟨hgF, fun a b hab hj' => ?_⟩
      rw [huv] at hab
      rcases Sym2.eq_iff.1 hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact not_joins_sdiff_of_bottleneck hw hF hgF hgle hglt hj'
      · exact not_joins_sdiff_of_bottleneck hw hF hgF hgle hglt hj'.symm
    refine hgle.mono ?_
    rintro f ⟨hf, hfg⟩
    exact ⟨hf, hfg.trans (h g hg)⟩

end Path

/-- The edge `e` is **contested** (p. 20, case (3)): it is projectable, and the forest joins its
ends. The preference of an edge that is not contested is determined by the spokes and the forest
alone. -/
def Contested (st : State V E) (e : E) : Prop :=
  Projectable st e ∧ ∀ a b, st.ends e = s(a, b) → Joins st.ends (st.forest : Set E) a b

open scoped Classical in
/-- The contested edges of `I`. -/
noncomputable def contested (st : State V E) (I : Finset E) : Finset E :=
  {e ∈ I | Contested st e}

omit [DecidableEq E] in
theorem mem_contested {st : State V E} {I : Finset E} {e : E} :
    e ∈ contested st I ↔ e ∈ I ∧ Contested st e := by
  classical
  simp [contested]

/-! ### Candidate maxima and the tagged order -/

/-- The **candidate maxima** `S_e` of `e` (p. 20): its spokes, tagged `true`, and its path edges,
tagged `false`. -/
noncomputable def candidates (st : State V E) (e : E) : Finset (Bool × E) :=
  (spokes st e).image (Prod.mk true) ∪ (pathEdges st e).image (Prod.mk false)

/-- The **ground set** of the edges `I` (p. 20): their spokes, tagged `true`, and the forest edges,
tagged `false`. -/
noncomputable def groundSet (st : State V E) (I : Finset E) : Finset (Bool × E) :=
  (I.biUnion (spokes st)).image (Prod.mk true) ∪ st.forest.image (Prod.mk false)

theorem candidates_subset_groundSet {st : State V E} {I : Finset E} {e : E} (he : e ∈ I) :
    candidates st e ⊆ groundSet st I :=
  union_subset_union (image_subset_image (subset_biUnion_of_mem _ he))
    (image_subset_image (pathEdges_subset st e))

section Order

variable [LinearOrder W]

omit [DecidableEq E] in
/-- **The tagged order** on `Bool × E` (p. 20): by weight, then by tag, so that a spoke (tagged
`true`) beats a forest edge (tagged `false`) of the same weight, which is the same edge when the
weights are injective. -/
def tagKey (w : E → W) (p : Bool × E) : W ×ₗ Bool :=
  toLex (w p.2, p.1)

omit [DecidableEq E] [LinearOrder W] in
theorem tagKey_injective {w : E → W} (hw : Function.Injective w) : Function.Injective (tagKey w) := by
  rintro ⟨b, e⟩ ⟨b', e'⟩ h
  simp only [tagKey, toLex_inj, Prod.mk.injEq] at h
  rw [hw h.1, h.2]

omit [DecidableEq E] in
theorem tagKey_false_le_true {w : E → W} {f s : E} :
    tagKey w (false, f) ≤ tagKey w (true, s) ↔ w f ≤ w s := by
  simp only [tagKey, Prod.Lex.toLex_le_toLex, Bool.false_le, and_true]
  exact le_iff_lt_or_eq.symm

omit [DecidableEq E] in
theorem tagKey_true_le_false {w : E → W} {f s : E} :
    tagKey w (true, s) ≤ tagKey w (false, f) ↔ w s < w f := by
  simp [tagKey, Prod.Lex.toLex_le_toLex]

end Order

/-! ### The characterization of the preferences -/

section Pref

variable [LinearOrder W] {w : E → W}

omit [DecidableEq E] in
/-- The spokes of a projectable edge with ends `u, v`. -/
private theorem exists_spokes_of_projectable {st : State V E} {e : E} (he : Projectable st e)
    {u v : V} (huv : st.ends e = s(u, v)) :
    ∃ su sv, st.spoke u = some su ∧ st.spoke v = some sv ∧ st.proj u ≠ st.proj v := by
  obtain ⟨su, hsu⟩ := Option.isSome_iff_exists.1
    (he.isSome_spoke (by rw [huv]; exact Sym2.mem_mk_left u v))
  obtain ⟨sv, hsv⟩ := Option.isSome_iff_exists.1
    (he.isSome_spoke (by rw [huv]; exact Sym2.mem_mk_right u v))
  have hne := he.not_isDiag
  rw [huv, Sym2.map_mk, Sym2.mk_isDiag_iff] at hne
  exact ⟨su, sv, hsu, hsv, hne⟩

theorem candidates_nonempty {st : State V E} {e : E} (he : Contested st e) :
    (candidates st e).Nonempty := by
  obtain ⟨⟨u, v⟩, huv⟩ := Quot.exists_rep (st.ends e)
  obtain ⟨su, sv, hsu, -, -⟩ := exists_spokes_of_projectable he.1 huv.symm
  refine ⟨(true, su), mem_union_left _ (mem_image_of_mem _ ?_)⟩
  rw [mem_spokes]
  exact ⟨u, by rw [← huv]; exact Sym2.mem_mk_left u v, hsu⟩

/-- **Preferences as maxima** (Lemma 3.10, p. 20). For an acyclic forest and injective weights, a
contested edge `e` prefers *find* exactly when the maximum `y` of its candidate set `S_e`, for the
tagged order, is a spoke. -/
theorem fst_eq_true_iff_prefersFind (hw : Function.Injective w) {st : State V E}
    (hF : IsAcyclic st.ends (st.forest : Set E)) {e : E} (he : Contested st e)
    {y : Bool × E} (hy : y ∈ candidates st e)
    (hmax : ∀ z ∈ candidates st e, tagKey w z ≤ tagKey w y) :
    y.1 = true ↔ PrefersFind w st e := by
  obtain ⟨⟨u, v⟩, huv⟩ := Quot.exists_rep (st.ends e)
  replace huv : st.ends e = s(u, v) := huv.symm
  obtain ⟨su, sv, hsu, hsv, hne⟩ := exists_spokes_of_projectable he.1 huv
  have hspokes : spokes st e = {su, sv} := by
    rw [spokes_eq huv, hsu, hsv]
    rfl
  rw [prefersFind_iff huv hsu hsv, or_iff_right hne,
    joins_le_iff_forall_mem_pathEdges hw hF huv (he.2 u v huv)]
  have hmem : ∀ z, z ∈ candidates st e ↔
      (z.1 = true ∧ (z.2 = su ∨ z.2 = sv)) ∨ (z.1 = false ∧ z.2 ∈ pathEdges st e) := by
    rintro ⟨b, z⟩
    simp only [candidates, hspokes, mem_union, mem_image, mem_insert, mem_singleton,
      Prod.mk.injEq]
    constructor
    · rintro (⟨x, hx, rfl, rfl⟩ | ⟨x, hx, rfl, rfl⟩)
      · exact Or.inl ⟨rfl, hx⟩
      · exact Or.inr ⟨rfl, hx⟩
    · rintro (⟨rfl, hx⟩ | ⟨rfl, hx⟩)
      · exact Or.inl ⟨z, hx, rfl, rfl⟩
      · exact Or.inr ⟨z, hx, rfl, rfl⟩
  obtain ⟨b, x⟩ := y
  rcases (hmem _).1 hy with ⟨rfl, hx⟩ | ⟨rfl, hx⟩
  · simp only [true_iff]
    intro f hf
    have := tagKey_false_le_true.1 (hmax (false, f) ((hmem _).2 (Or.inr ⟨rfl, hf⟩)))
    rcases hx with rfl | rfl
    · exact this.trans (le_max_left _ _)
    · exact this.trans (le_max_right _ _)
  · simp only [Bool.false_eq_true, false_iff]
    intro h
    rcases le_max_iff.1 (h x hx) with hxs | hxs
    · exact absurd hxs (not_le.2
        (tagKey_true_le_false.1 (hmax (true, su) ((hmem _).2 (Or.inl ⟨rfl, Or.inl rfl⟩)))))
    · exact absurd hxs (not_le.2
        (tagKey_true_le_false.1 (hmax (true, sv) ((hmem _).2 (Or.inl ⟨rfl, Or.inr rfl⟩)))))

/-- A projectable edge whose ends the forest does not join prefers *project* (p. 20). -/
theorem not_prefersFind_of_not_contested {st : State V E} {e : E} (hp : Projectable st e)
    (hc : ¬Contested st e) : ¬PrefersFind w st e := by
  unfold PrefersFind
  rintro (h | h)
  · exact h hp
  · refine hc ⟨hp, fun a b hab => (h a b hab).mono ?_⟩
    rintro f ⟨hf, -⟩
    exact hf

end Pref

/-! ### The family of preference vectors -/

section Family

variable [LinearOrder W]

/-- The vectors of maxima of the candidate sets of the contested edges of `I`, for all injective
weights at once (Lemma 3.9 on the tagged ground set). -/
noncomputable def maximaVectors (st : State V E) (I : Finset E) :
    Finset (contested st I → Bool × E) :=
  (exists_maxima_vectors_card_le_choose.{0} (groundSet st I)
    (fun e : contested st I => candidates st e)
    (fun e => candidates_subset_groundSet (mem_contested.1 e.2).1) le_rfl).choose

theorem card_maximaVectors_le (st : State V E) (I : Finset E) :
    #(maximaVectors st I) ≤
      (#(groundSet st I) + #(contested st I) - 1).choose #(contested st I) := by
  have := (exists_maxima_vectors_card_le_choose.{0} (groundSet st I)
    (fun e : contested st I => candidates st e)
    (fun e => candidates_subset_groundSet (mem_contested.1 e.2).1) le_rfl).choose_spec.1
  exact this.trans_eq (by rw [Fintype.card_coe])

theorem mem_maximaVectors {st : State V E} {I : Finset E} {w : E → W}
    (hw : Function.Injective w) {x : contested st I → Bool × E}
    (hx : ∀ e : contested st I,
      x e ∈ candidates st e ∧ ∀ y ∈ candidates st e, tagKey w y ≤ tagKey w (x e)) :
    x ∈ maximaVectors st I :=
  (exists_maxima_vectors_card_le_choose.{0} (groundSet st I)
    (fun e : contested st I => candidates st e)
    (fun e => candidates_subset_groundSet (mem_contested.1 e.2).1) le_rfl).choose_spec.2
    (tagKey w) (tagKey_injective hw).injOn x hx

open scoped Classical in
/-- The preference vector read off a vector of maxima: on a contested edge, *find* when its
maximum is a spoke; on the other edges of `I`, *project* when projectable and *find* otherwise;
*find* outside `I`. -/
noncomputable def decodePrefs (st : State V E) (I : Finset E) (x : contested st I → Bool × E)
    (e : E) : Action :=
  if h : e ∈ contested st I then (if (x ⟨e, h⟩).1 then .find else .project)
  else if e ∈ I ∧ Projectable st e then .project else .find

open scoped Classical in
/-- **The family of preference vectors** of the edges `I` that the spokes and the forest of `st`
allow (p. 20 and p. 22): the family `A` of §3.5. -/
noncomputable def prefFamily (st : State V E) (I : Finset E) : Finset (E → Action) :=
  (maximaVectors st I).image (decodePrefs st I)

open scoped Classical in
/-- The **true preference vector** of the edges `I` at the state `st`, *find* outside `I`. -/
noncomputable def prefVector (w : E → W) (st : State V E) (I : Finset E) (e : E) : Action :=
  if e ∈ I then pref w st e else .find

theorem prefVector_of_mem {w : E → W} {st : State V E} {I : Finset E} {e : E} (he : e ∈ I) :
    prefVector w st I e = pref w st e := by
  simp [prefVector, he]

/-- **The true preferences are in the family** (p. 20): for injective weights and an acyclic
forest. -/
theorem prefVector_mem_prefFamily {w : E → W} (hw : Function.Injective w) {st : State V E}
    (hF : IsAcyclic st.ends (st.forest : Set E)) (I : Finset E) :
    prefVector w st I ∈ prefFamily st I := by
  classical
  have hex := fun e : contested st I =>
    (candidates st e).exists_max_image (tagKey w)
      (candidates_nonempty (mem_contested.1 e.2).2)
  let x : contested st I → Bool × E := fun e => (hex e).choose
  have hx : ∀ e : contested st I,
      x e ∈ candidates st e ∧ ∀ y ∈ candidates st e, tagKey w y ≤ tagKey w (x e) :=
    fun e => (hex e).choose_spec
  refine mem_image.2 ⟨x, mem_maximaVectors hw hx, funext fun e => ?_⟩
  unfold decodePrefs prefVector
  by_cases hc : e ∈ contested st I
  · obtain ⟨heI, hce⟩ := mem_contested.1 hc
    have key := fst_eq_true_iff_prefersFind hw hF hce (hx ⟨e, hc⟩).1 (hx ⟨e, hc⟩).2
    simp only [hc, heI, ↓reduceDIte, ↓reduceIte]
    by_cases hb : (x ⟨e, hc⟩).1 = true
    · simp only [hb, ↓reduceIte, pref_eq_find_iff.2 (key.1 hb)]
    · simp only [hb, Bool.false_eq_true, ↓reduceIte, pref_eq_project_iff.2 (mt key.2 hb)]
  · simp only [hc, ↓reduceDIte]
    by_cases heI : e ∈ I
    · by_cases hp : Projectable st e
      · simp only [heI, hp, and_self, ↓reduceIte, pref_eq_project_iff.2
          (not_prefersFind_of_not_contested hp fun h => hc (mem_contested.2 ⟨heI, h⟩))]
      · simp only [heI, hp, and_false, ↓reduceIte, pref_eq_find_iff.2 (Or.inl hp)]
    · simp only [heI, false_and, ↓reduceIte]

omit [DecidableEq V] in
private theorem choose_le_choose_add {a b a' b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') :
    (a + b).choose b ≤ (a' + b').choose b' := by
  calc (a + b).choose b = (a + b).choose a := Nat.choose_symm_add.symm
    _ ≤ (a + b').choose a := Nat.choose_le_choose a (by omega)
    _ = (a + b').choose b' := Nat.choose_symm_add
    _ ≤ (a' + b').choose b' := Nat.choose_le_choose b' (by omega)

/-- The spokes at the ends of the edges of `I` are spokes of vertices of `X`, when only vertices
of `X` have spokes. -/
private theorem card_biUnion_spokes_le {st : State V E} {X : Finset V}
    (hσ : ∀ v s, st.spoke v = some s → v ∈ X) (I : Finset E) : #(I.biUnion (spokes st)) ≤ #X := by
  have hsub : I.biUnion (spokes st) ⊆ X.biUnion fun v => (st.spoke v).toFinset := by
    intro s hs
    obtain ⟨e, -, hs⟩ := mem_biUnion.1 hs
    obtain ⟨x, -, hx⟩ := mem_spokes.1 hs
    exact mem_biUnion.2 ⟨x, hσ x s hx, by simp [hx]⟩
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  calc ∑ v ∈ X, #(st.spoke v).toFinset ≤ ∑ _v ∈ X, 1 :=
        sum_le_sum fun v _ => by cases st.spoke v <;> simp
    _ = #X := by simp

/-- **The size of the family** (p. 20, via Lemma 3.9): when only vertices of `X` have spokes and the
forest has at most `|X|` edges, the ground set has at most `2 |X|` elements, so there are at most
`C(|I| + 2|X|, 2|X|)` preference vectors. -/
theorem card_prefFamily_le_choose {st : State V E} {X : Finset V}
    (hσ : ∀ v s, st.spoke v = some s → v ∈ X) (hF : #st.forest ≤ #X) (I : Finset E) :
    #(prefFamily st I) ≤ (#I + 2 * #X).choose (2 * #X) := by
  have hg : #(groundSet st I) ≤ 2 * #X := by
    refine (card_union_le _ _).trans ?_
    have h1 := (card_image_le (s := I.biUnion (spokes st)) (f := Prod.mk true)).trans
      (card_biUnion_spokes_le hσ I)
    have h2 := card_image_le (s := st.forest) (f := Prod.mk false)
    omega
  have hc : #(contested st I) ≤ #I := card_le_card fun e he => (mem_contested.1 he).1
  calc #(prefFamily st I) ≤ #(maximaVectors st I) := by
        classical
        exact card_image_le
    _ ≤ (#(groundSet st I) + #(contested st I) - 1).choose #(contested st I) :=
        card_maximaVectors_le st I
    _ ≤ (#(groundSet st I) + #(contested st I)).choose #(contested st I) :=
        Nat.choose_le_choose _ (Nat.sub_le _ _)
    _ ≤ (2 * #X + #I).choose #I := choose_le_choose_add hg hc
    _ = (#I + 2 * #X).choose (2 * #X) := by rw [add_comm, ← Nat.choose_symm_add]

end Family

/-! ### Histories (Definition 3.8) and Lemma 3.10 -/

section History

variable [LinearOrder W]

/-- One round of a **history** (Definition 3.8, p. 18): the spokes and the forest at the start of
the round, and the true preferred actions of the edges. -/
structure HistoryRound (V E : Type) where
  /-- The spokes `σᵢ`. -/
  spoke : V → Option E
  /-- The forest `Fᵢ`. -/
  forest : Finset E
  /-- The true preferred actions `aᵢ`. -/
  pref : E → Action

variable (cfg : Config V E) (w : E → W)

/-- **The history** of the call on `inst` under the comparison oracle of `w` (Definition 3.8,
p. 18). -/
noncomputable def history (inst : Instance V E) :
    Fin (levelT cfg.γ inst.level ^ 2) → HistoryRound V E := fun i =>
  ⟨(snapshot cfg (LEQuery.keyOracle w) inst i).state.spoke,
    (snapshot cfg (LEQuery.keyOracle w) inst i).state.forest,
    prefVector w (snapshot cfg (LEQuery.keyOracle w) inst i).state inst.edges⟩

/-- The preferences of the edges of the call in the history are the true preferences. -/
theorem pref_history_of_mem {inst : Instance V E} (i : Fin (levelT cfg.γ inst.level ^ 2)) {e : E}
    (he : e ∈ inst.edges) : (history cfg w inst i).pref e = prefSeq cfg w inst e i :=
  prefVector_of_mem he

/-- The state on the vertices and ends of `inst` with the spokes `σ` and the forest `F`, and no
portals: the preferences depend on nothing else. -/
@[expose] def Instance.stateOf (inst : Instance V E) (σ : V → Option E) (F : Finset E) :
    State V E :=
  ⟨inst.vertices, inst.ends, ∅, σ, F⟩

/-- The preferences at a state depend only on its ends, spokes and forest. -/
theorem pref_congr {st st' : State V E} (he : st.ends = st'.ends) (hs : st.spoke = st'.spoke)
    (hf : st.forest = st'.forest) : pref w st = pref w st' := by
  obtain ⟨X, ends, P, σ, F⟩ := st
  obtain ⟨X', ends', P', σ', F'⟩ := st'
  simp only at he hs hf
  subst he hs hf
  funext e
  rfl

open scoped Classical in
/-- The spoke choices (p. 19): every vertex has no spoke or an incident edge of the instance. -/
noncomputable def spokeChoices (inst : Instance V E) : Finset (V → Option E) :=
  (inst.vertices.pi fun v => insertNone {e ∈ inst.edges | v ∈ inst.ends e}).image
    fun f v => if h : v ∈ inst.vertices then f v h else none

/-- The forest choices (p. 20): sets of at most `n - 1` edges of the instance. -/
noncomputable def forestChoices (inst : Instance V E) : Finset (Finset E) :=
  {F ∈ inst.edges.powerset | #F ≤ #inst.vertices - 1}

open scoped Classical in
/-- The choices of one round of a history: spokes, a forest, and a preference vector that they
allow. -/
noncomputable def roundChoices (inst : Instance V E) : Finset (HistoryRound V E) :=
  (spokeChoices inst ×ˢ forestChoices inst).biUnion fun p =>
    (prefFamily (inst.stateOf p.1 p.2) inst.edges).image fun a => ⟨p.1, p.2, a⟩

/-- **The family of histories** of a call on `inst` (Lemma 3.10, p. 19): every round is one of the
`Cslib.Query.Certificate.roundChoices`. It depends only on `γ` and the combinatorial data of the
instance, not on the weights. -/
noncomputable def histories (γ : ℕ) (inst : Instance V E) :
    Finset (Fin (levelT γ inst.level ^ 2) → HistoryRound V E) :=
  Fintype.piFinset fun _ => roundChoices inst

omit [DecidableEq E] in
theorem mem_spokeChoices {inst : Instance V E} {σ : V → Option E}
    (hσ : ∀ v s, σ v = some s → v ∈ inst.vertices ∧ s ∈ inst.edges ∧ v ∈ inst.ends s) :
    σ ∈ spokeChoices inst := by
  classical
  refine mem_image.2 ⟨fun v _ => σ v, mem_pi.2 fun v _ => ?_, funext fun v => ?_⟩
  · rcases h : σ v with _ | s
    · exact none_mem_insertNone
    · obtain ⟨-, hs, hv⟩ := hσ v s h
      exact some_mem_insertNone.2 (mem_filter.2 ⟨hs, hv⟩)
  · by_cases hv : v ∈ inst.vertices
    · simp [hv]
    · rcases h : σ v with _ | s
      · simp [hv]
      · exact absurd (hσ v s h).1 hv

omit [DecidableEq E] in
theorem spoke_mem_of_mem_spokeChoices {inst : Instance V E} {σ : V → Option E}
    (hσ : σ ∈ spokeChoices inst) {v : V} {s : E} (hs : σ v = some s) : v ∈ inst.vertices := by
  classical
  obtain ⟨f, -, rfl⟩ := mem_image.1 hσ
  by_contra hv
  simp [hv] at hs

/-- **The actual history is a candidate** (Lemma 3.10, p. 19): for injective weights, a correct
exact minimum spanning forest subroutine and a well-formed instance, the history of the call
under the comparison oracle of the weights is in `histories cfg.γ inst`. -/
theorem history_mem_histories (hw : Function.Injective w) (hmsf : cfg.ExactMsf w)
    {inst : Instance V E} (hwf : inst.WellFormed) :
    history cfg w inst ∈ histories cfg.γ inst := by
  classical
  refine Fintype.mem_piFinset.2 fun i => ?_
  set st := (snapshot cfg (LEQuery.keyOracle w) inst i).state
  have hinv := invariant_snapshot hw hmsf hwf i
  have hends : st.ends = inst.ends := ends_snapshot _ _ _ _
  have hvx : st.vertices = inst.vertices := vertices_snapshot _ _ _ _
  refine mem_biUnion.2 ⟨(st.spoke, st.forest), mem_product.2 ⟨?_, ?_⟩, mem_image.2 ⟨_,
    prefVector_mem_prefFamily hw (st := inst.stateOf st.spoke st.forest) ?_ inst.edges, ?_⟩⟩
  · refine mem_spokeChoices fun v s hs => ⟨?_, hinv.spoke_mem v s hs, ?_⟩
    · rw [← hvx]
      exact hinv.state.mem_vertices_of_spoke v s hs
    · rw [← hends]
      exact hinv.state.mem_ends_spoke v s hs
  · refine mem_filter.2 ⟨mem_powerset.2 hinv.forest_subset, ?_⟩
    have := hinv.state.card_forest_le
    rwa [hvx] at this
  · have := hinv.state.forest_acyclic
    rwa [hends] at this
  · have : prefVector w (inst.stateOf st.spoke st.forest) inst.edges =
        prefVector w st inst.edges := by
      funext e
      unfold prefVector
      rw [pref_congr w (st := inst.stateOf st.spoke st.forest) (st' := st) hends.symm rfl rfl]
    rw [this]
    rfl

/-! #### Counting -/

omit [DecidableEq V] [DecidableEq E] [LinearOrder W] in
private theorem log_natCast_le_log {a b : ℕ} (h : a ≤ b) : Real.log a ≤ Real.log b := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simpa using Real.log_natCast_nonneg b
  · exact Real.log_le_log (by exact_mod_cast ha) (by exact_mod_cast h)

omit [DecidableEq V] [DecidableEq E] [LinearOrder W] in
/-- `∑_{k ≤ K} C(m, k) ≤ C(m + K, K)`, by Vandermonde's identity. -/
private theorem sum_range_choose_le_add_choose (m K : ℕ) :
    ∑ k ∈ range (K + 1), m.choose k ≤ (m + K).choose K := by
  rw [Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  exact sum_le_sum fun k hk =>
    Nat.le_mul_of_pos_right _ (Nat.choose_pos (Nat.sub_le K k))

omit [LinearOrder W] [DecidableEq V] in
theorem card_forestChoices_le (inst : Instance V E) :
    #(forestChoices inst) ≤ (#inst.edges + (#inst.vertices - 1)).choose (#inst.vertices - 1) := by
  set K := #inst.vertices - 1
  have hsub : forestChoices inst ⊆ (range (K + 1)).biUnion fun k => inst.edges.powersetCard k := by
    intro F hF
    obtain ⟨hFS, hFK⟩ := mem_filter.1 hF
    exact mem_biUnion.2 ⟨#F, mem_range.2 (by omega),
      mem_powersetCard.2 ⟨mem_powerset.1 hFS, rfl⟩⟩
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  simp only [card_powersetCard]
  exact sum_range_choose_le_add_choose _ _

omit [LinearOrder W] [DecidableEq E] in
theorem card_spokeChoices_le (inst : Instance V E) :
    #(spokeChoices inst) ≤ ∏ v ∈ inst.vertices, (#{e ∈ inst.edges | v ∈ inst.ends e} + 1) := by
  classical
  refine card_image_le.trans ?_
  rw [card_pi]
  simp

omit [LinearOrder W] [DecidableEq E] in
/-- The degrees sum to at most `2m`. -/
private theorem sum_degree_le (inst : Instance V E) :
    ∑ v ∈ inst.vertices, #{e ∈ inst.edges | v ∈ inst.ends e} ≤ 2 * #inst.edges := by
  calc ∑ v ∈ inst.vertices, #{e ∈ inst.edges | v ∈ inst.ends e}
      = ∑ e ∈ inst.edges, #{v ∈ inst.vertices | v ∈ inst.ends e} := by
        simp only [card_filter]
        exact sum_comm
    _ ≤ ∑ _e ∈ inst.edges, 2 := sum_le_sum fun e _ => by
        obtain ⟨⟨a, b⟩, hab⟩ := Quot.exists_rep (inst.ends e)
        calc #{v ∈ inst.vertices | v ∈ inst.ends e} ≤ #({a, b} : Finset V) := by
              refine card_le_card fun v hv => ?_
              have := (mem_filter.1 hv).2
              rw [← hab] at this
              rcases Sym2.mem_iff.1 this with rfl | rfl <;> simp
          _ ≤ 2 := card_le_two
    _ = 2 * #inst.edges := by rw [sum_const, smul_eq_mul, mul_comm]

omit [LinearOrder W] [DecidableEq E] in
/-- The logarithm of the number of spoke choices (p. 20): `∑ log (deg v + 1) ≤ ∑ √(deg v) ≤
√(2 m n)`, by `log (x + 1) ≤ √x` and Cauchy–Schwarz. -/
private theorem log_card_spokeChoices_le (inst : Instance V E) :
    Real.log #(spokeChoices inst) ≤ √(2 * #inst.edges * #inst.vertices) := by
  set deg : V → ℕ := fun v => #{e ∈ inst.edges | v ∈ inst.ends e}
  refine (log_natCast_le_log (card_spokeChoices_le inst)).trans ?_
  push_cast
  rw [Real.log_prod (fun v _ => by positivity)]
  calc ∑ v ∈ inst.vertices, Real.log ((deg v : ℝ) + 1)
      ≤ ∑ v ∈ inst.vertices, √(deg v : ℝ) * √1 :=
        sum_le_sum fun v _ => by
          rw [Real.sqrt_one, mul_one]
          exact Real.log_add_one_le_sqrt (by positivity)
    _ ≤ √(∑ v ∈ inst.vertices, (deg v : ℝ)) * √(∑ _v ∈ inst.vertices, (1 : ℝ)) :=
        Real.sum_sqrt_mul_sqrt_le _ (fun _ => by positivity) fun _ => zero_le_one
    _ ≤ √(2 * #inst.edges) * √(#inst.vertices : ℝ) := by
        gcongr
        · exact_mod_cast sum_degree_le inst
        · simp
    _ = √(2 * #inst.edges * #inst.vertices) := (Real.sqrt_mul (by positivity) _).symm

/-- **Lemma 3.10** ([KhannaPuttermanSong2026], §3.4, p. 19). The family of histories of a call on
`n` vertices and `m` edges at level `d`, with `t = γ d³`, has `log |𝓗| ≤ 7 t² √(m n)`. A step in the
proof of [KhannaPuttermanSong2026] Theorem 4.1 (#8325).

The paper's three factors per round are `∏ (deg v + 1)` spokes (`√(2 m n)` after logarithms),
`C(m + n - 1, n - 1)` forests (`2 √(m n)`) and `C(m + 2n - 1, m)` preference vectors
(`2 √(2 m n)`); here the last is the slightly larger `C(m + 2n, 2n)`, with the same bound. The sum
`(2 + 3 √2) √(m n)` is at most `7 √(m n)`. -/
theorem log_card_histories_le (γ : ℕ) (inst : Instance V E) :
    Real.log #(histories γ inst) ≤
      7 * (levelT γ inst.level : ℝ) ^ 2 * √(#inst.edges * #inst.vertices) := by
  classical
  set m := #inst.edges
  set n := #inst.vertices
  set C := (m + 2 * n).choose (2 * n)
  -- one round
  have hround : #(roundChoices inst) ≤
      #(spokeChoices inst) * (m + n).choose n * C := by
    refine card_biUnion_le.trans ?_
    calc ∑ p ∈ spokeChoices inst ×ˢ forestChoices inst,
          #((prefFamily (inst.stateOf p.1 p.2) inst.edges).image
            fun a => (⟨p.1, p.2, a⟩ : HistoryRound V E))
        ≤ ∑ _p ∈ spokeChoices inst ×ˢ forestChoices inst, C := by
          refine sum_le_sum fun p hp => card_image_le.trans ?_
          obtain ⟨hσ, hF⟩ := mem_product.1 hp
          exact card_prefFamily_le_choose (X := inst.vertices)
            (fun v s hs => spoke_mem_of_mem_spokeChoices hσ hs)
            (((mem_filter.1 hF).2).trans (Nat.sub_le _ _)) _
      _ = #(spokeChoices inst) * #(forestChoices inst) * C := by
          rw [sum_const, smul_eq_mul, card_product]
      _ ≤ #(spokeChoices inst) * (m + n).choose n * C := by
          gcongr
          refine (card_forestChoices_le inst).trans ?_
          exact choose_le_choose_add le_rfl (Nat.sub_le _ _)
  have hspoke := log_card_spokeChoices_le inst
  have hforest := Cslib.log_add_choose_le_two_mul_sqrt m n
  have hpref := Cslib.log_add_choose_le_two_mul_sqrt m (2 * n)
  have hpos1 : 0 < #(spokeChoices inst) :=
    card_pos.2 ⟨fun _ => none, mem_spokeChoices fun _ _ h => by cases h⟩
  have hpos2 : 0 < (m + n).choose n := Nat.choose_pos (by omega)
  have hpos3 : 0 < C := Nat.choose_pos (by omega)
  have hlogR : Real.log #(roundChoices inst) ≤ 7 * √(m * n) := by
    refine (log_natCast_le_log hround).trans ?_
    push_cast
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
    have hs2 : √2 ≤ 5 / 3 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
    have e1 : √(2 * m * n) = √2 * √(m * n) := by
      rw [mul_assoc, Real.sqrt_mul (by norm_num)]
    have e2 : √(m * ((2 * n : ℕ) : ℝ)) = √2 * √(m * n) := by
      push_cast
      rw [show (m : ℝ) * (2 * n) = 2 * (m * n) by ring, Real.sqrt_mul (by norm_num)]
    rw [e1] at hspoke
    rw [e2] at hpref
    have : 0 ≤ √((m : ℝ) * n) := Real.sqrt_nonneg _
    nlinarith
  unfold histories
  rw [Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin, Nat.cast_pow,
    Real.log_pow]
  have hlogR0 : 0 ≤ Real.log #(roundChoices inst) := Real.log_natCast_nonneg _
  calc ((levelT γ inst.level ^ 2 : ℕ) : ℝ) * Real.log #(roundChoices inst)
      ≤ ((levelT γ inst.level ^ 2 : ℕ) : ℝ) * (7 * √(m * n)) := by gcongr
    _ = 7 * (levelT γ inst.level : ℝ) ^ 2 * √(m * n) := by push_cast; ring

end History

end Cslib.Query.Certificate
