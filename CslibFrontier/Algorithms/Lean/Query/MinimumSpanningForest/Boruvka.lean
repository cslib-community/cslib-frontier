/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Query.Sort.LEQuery.KeyOracle
public import CslibFrontier.Foundations.Combinatorics.Multigraph.MinimumSpanningForest
public import Cslib.Algorithms.Lean.Query.FreeM
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Borůvka steps as comparison programs

A **Borůvka step** ([Borůvka][Boruvka1926]; Definition 2.8 of
[Khanna, Putterman and Song][KhannaPuttermanSong2026], p. 12) selects, for every vertex, its
lightest incident edge other than a self-loop. In the comparison model `FreeM (LEQuery E)`,
`Cslib.Query.boruvkaStep ends S` scans the edges of `S` once and offers each edge to its two ends,
each of which keeps the lighter of its current choice and the offered edge; this makes at most two
comparisons per edge (`Cslib.Query.countQueries_boruvkaStep_le`). Against the comparison oracle of
weights `w`, every selected edge is in the minimum spanning forest, by the cut property
(`Cslib.Query.boruvkaStep_subset_msf`). Whatever the oracle answers, every non-isolated vertex
selects an edge, so contracting the selected edges at least halves the number of non-isolated
vertices (`Cslib.Query.two_mul_card_support_boruvkaStep_le`).

`Cslib.Query.boruvka ends S k` performs `k` steps, contracting the selected edges after each and
dropping the edges that became self-loops. It returns a `Cslib.Query.BoruvkaResult`: the selected
edges `chosen`, the contraction map `proj` of the vertices (which stay in `V`), and the remaining
edges `rest`. Then

* it makes at most `2 * k * |S|` comparisons against every oracle
  (`Cslib.Query.countQueries_boruvka_le`);
* `rest ⊆ S`, no edge of `rest` is a self-loop of the contracted multigraph
  `Sym2.map proj ∘ ends`, and `proj` identifies exactly the vertices joined by `chosen`
  (`Cslib.Query.BoruvkaResult.IsContraction`, `Cslib.Query.isContraction_boruvka`);
* the contracted multigraph has at most `n / 2 ^ k` non-isolated vertices, where `n` is the number
  of non-isolated vertices of `S` (`Cslib.Query.card_support_boruvka_le`);
* with distinct weights, `msf S = chosen ∪ msf rest`, the latter in the contracted multigraph
  (`Cslib.Query.msf_eq_union_boruvka`): the paper's `MSF(G) = S ∪ MSF(G/S)` (p. 12).

The comparison bounds and the halving hold for every oracle; only the identity with the minimum
spanning forest needs the oracle of weights, and distinct weights.

These programs and their properties are steps in the proof of Theorem 4.1 of
[KhannaPuttermanSong2026] (§4, p. 25), tracked in #8325, whose final algorithm begins with Borůvka
steps (Algorithm 2, lines 1–3, p. 25).

## Main definitions

* `Cslib.Query.boruvkaStep`: one Borůvka step, returning the selected edges.
* `Cslib.Query.BoruvkaResult`, `Cslib.Query.boruvka`: `k` Borůvka steps with contraction.
* `Cslib.Query.BoruvkaResult.IsContraction`: what the result of the steps satisfies.

## Main results

* `Cslib.Query.countQueries_boruvkaStep_le`, `Cslib.Query.boruvkaStep_subset_msf`,
  `Cslib.Query.two_mul_card_support_boruvkaStep_le`: one step costs at most `2 |S|` comparisons,
  selects edges of the minimum spanning forest, and halves the non-isolated vertices.
* `Cslib.Query.countQueries_boruvka_le`, `Cslib.Query.isContraction_boruvka`,
  `Cslib.Query.card_support_boruvka_le`, `Cslib.Query.msf_eq_union_boruvka`: the same for `k`
  steps.

## References

* [O. Borůvka, *O jistém problému minimálním*][Boruvka1926].
* [S. Khanna, A. Putterman and J. Song, *A Deterministic Linear Time Algorithm for Minimum
  Spanning Tree*][KhannaPuttermanSong2026], §2, Definition 2.8, p. 12.
-/

public section

namespace Cslib.Query

open Finset Multigraph

variable {W : Type*} {V E : Type} [DecidableEq V] [LinearOrder W]

/-! ### One step -/

/-- Offer the edge `e` to the vertex `v`: if `v` has chosen an edge `f`, it keeps the lighter of
`f` and `e`, by one comparison; otherwise it chooses `e`. -/
private def offer (best : V → Option E) (v : V) (e : E) : FreeM (LEQuery E) (V → Option E) :=
  match best v with
  | none => pure (Function.update best v (some e))
  | some f => do
    if ← LEQuery.ask f e then pure best else pure (Function.update best v (some e))

/-- Offer every edge of the list, other than self-loops, to both of its ends. -/
private noncomputable def scan (ends : E → Sym2 V) :
    List E → (V → Option E) → FreeM (LEQuery E) (V → Option E)
  | [], best => pure best
  | e :: es, best =>
    if (ends e).IsDiag then scan ends es best else do
      let best ← offer best (Quot.out (ends e)).1 e
      let best ← offer best (Quot.out (ends e)).2 e
      scan ends es best

open scoped Classical in
/-- **One Borůvka step** (Definition 2.8, p. 12): the edges of `S` that some vertex selects as its
lightest incident edge other than a self-loop. -/
noncomputable def boruvkaStep (ends : E → Sym2 V) (S : Finset E) : FreeM (LEQuery E) (Finset E) :=
  do
    let best ← scan ends S.toList fun _ => none
    return {e ∈ S | ∃ v, best v = some e}

private theorem countQueries_offer_le (oracle : {ι : Type} → LEQuery E ι → ι)
    (best : V → Option E) (v : V) (e : E) : (offer best v e).countQueries oracle ≤ 1 := by
  unfold offer
  cases best v with
  | none => simp
  | some f => simp only [FreeM.countQueries_bind]; split <;> simp

/-- The result of offering `e` to `v`: `v` chooses `e` or keeps its choice, and against an oracle
of weights it keeps the lighter one. -/
private theorem eval_offer (oracle : {ι : Type} → LEQuery E ι → ι) (best : V → Option E) (v : V)
    (e : E) : ∃ x, (offer best v e).eval oracle = Function.update best v (some x) ∧
      (x = e ∨ best v = some x) ∧ ∀ w : E → W, (∀ a b, oracle (.le a b) = decide (w a ≤ w b)) →
        w x ≤ w e ∧ ∀ g, best v = some g → w x ≤ w g := by
  unfold offer
  cases hb : best v with
  | none => exact ⟨e, by simp, Or.inl rfl, fun w _ => ⟨le_rfl, by simp⟩⟩
  | some f =>
    by_cases h : oracle (.le f e) = true
    · refine ⟨f, ?_, Or.inr rfl, fun w hw => ?_⟩
      · simp [h, ← hb]
      · rw [hw, decide_eq_true_iff] at h
        exact ⟨h, by simp⟩
    · refine ⟨e, ?_, Or.inl rfl, fun w hw => ?_⟩
      · simp [h]
      · rw [hw, decide_eq_true_iff, not_le] at h
        exact ⟨le_rfl, by simp only [Option.some.injEq]; rintro g rfl; exact h.le⟩

private theorem countQueries_scan_le (ends : E → Sym2 V) (oracle : {ι : Type} → LEQuery E ι → ι)
    (L : List E) (best : V → Option E) :
    (scan ends L best).countQueries oracle ≤ 2 * L.length := by
  induction L generalizing best with
  | nil => simp [scan]
  | cons e es ih =>
    unfold scan
    split
    · exact (ih best).trans (by simp)
    · simp only [FreeM.countQueries_bind, List.length_cons]
      have h₁ := countQueries_offer_le oracle best (Quot.out (ends e)).1 e
      have h₂ := countQueries_offer_le oracle ((offer best (Quot.out (ends e)).1 e).eval oracle)
        (Quot.out (ends e)).2 e
      have h₃ := ih (((offer ((offer best (Quot.out (ends e)).1 e).eval oracle)
        (Quot.out (ends e)).2 e)).eval oracle)
      omega

/-- Against every oracle, offering `e` to `v` changes only the choice of `v`, to `e` or its
earlier choice, and leaves `v` with a choice. -/
private theorem offer_choice (oracle : {ι : Type} → LEQuery E ι → ι) (best : V → Option E)
    (v : V) (e : E) :
    (∀ u y, (offer best v e).eval oracle u = some y → best u = some y ∨ (y = e ∧ u = v)) ∧
    (∀ u, best u ≠ none ∨ u = v → (offer best v e).eval oracle u ≠ none) := by
  obtain ⟨x, h, hx, -⟩ := eval_offer (W := ℕ) oracle best v e
  rw [h]
  refine ⟨fun u y hy => ?_, fun u hu => ?_⟩
  · by_cases huv : u = v
    · subst huv
      simp only [Function.update_self, Option.some.injEq] at hy
      subst hy
      rcases hx with rfl | hx
      · exact Or.inr ⟨rfl, rfl⟩
      · exact Or.inl hx
    · rw [Function.update_of_ne huv] at hy
      exact Or.inl hy
  · by_cases huv : u = v
    · subst huv; simp
    · rw [Function.update_of_ne huv]
      exact hu.resolve_right huv

/-- Against an oracle of weights `w`, offering `e` to `v` never makes a choice heavier, and leaves
`v` with a choice no heavier than `e`. -/
private theorem offer_le (oracle : {ι : Type} → LEQuery E ι → ι) (w : E → W)
    (hw : ∀ a b, oracle (.le a b) = decide (w a ≤ w b)) (best : V → Option E) (v : V) (e : E) :
    (∀ u g, best u = some g → ∃ y, (offer best v e).eval oracle u = some y ∧ w y ≤ w g) ∧
    ∃ y, (offer best v e).eval oracle v = some y ∧ w y ≤ w e := by
  obtain ⟨x, h, -, hle⟩ := eval_offer (W := W) oracle best v e
  obtain ⟨hxe, hxg⟩ := hle w hw
  rw [h]
  refine ⟨fun u g hg => ?_, ⟨x, by simp, hxe⟩⟩
  by_cases huv : u = v
  · subst huv
    exact ⟨x, by simp, hxg g hg⟩
  · exact ⟨g, by rw [Function.update_of_ne huv, hg], le_rfl⟩

/-- After the scan, a vertex's choice is its earlier choice or an edge of the list at it that is
not a self-loop; and every vertex that had a choice, or has such an edge in the list, has a
choice. This holds against every oracle. -/
private theorem scan_spec (ends : E → Sym2 V) (oracle : {ι : Type} → LEQuery E ι → ι)
    (L : List E) (best : V → Option E) :
    (∀ v x, (scan ends L best).eval oracle v = some x →
      best v = some x ∨ (x ∈ L ∧ ¬(ends x).IsDiag ∧ v ∈ ends x)) ∧
    (∀ v, (best v ≠ none ∨ ∃ e ∈ L, ¬(ends e).IsDiag ∧ v ∈ ends e) →
      (scan ends L best).eval oracle v ≠ none) := by
  induction L generalizing best with
  | nil => simp [scan]
  | cons e es ih =>
    unfold scan
    split
    · next hloop =>
      refine ⟨fun v x hx => ?_, fun v hv => (ih best).2 v ?_⟩
      · rcases (ih best).1 v x hx with h | ⟨hx, h⟩
        · exact Or.inl h
        · exact Or.inr ⟨List.mem_cons_of_mem _ hx, h⟩
      · rcases hv with hv | ⟨f, hf, hfd, hvf⟩
        · exact Or.inl hv
        · rcases List.mem_cons.1 hf with rfl | hf
          · exact absurd hloop hfd
          · exact Or.inr ⟨f, hf, hfd, hvf⟩
    · next hloop =>
      simp only [FreeM.eval_bind]
      set a := (Quot.out (ends e)).1
      set b := (Quot.out (ends e)).2
      have hab : ends e = s(a, b) := (Sym2.mk_fst_out_snd_out _).symm
      have hmem : ∀ v, v = a ∨ v = b → v ∈ ends e := by
        rintro v (rfl | rfl) <;> simp [hab]
      obtain ⟨c₁, k₁⟩ := offer_choice oracle best a e
      set best₁ := (offer best a e).eval oracle
      obtain ⟨c₂, k₂⟩ := offer_choice oracle best₁ b e
      set best₂ := (offer best₁ b e).eval oracle
      refine ⟨fun v x hx => ?_, fun v hv => ?_⟩
      · rcases (ih best₂).1 v x hx with h | ⟨hx, h⟩
        · rcases c₂ v x h with h | ⟨rfl, rfl⟩
          · rcases c₁ v x h with h | ⟨rfl, rfl⟩
            · exact Or.inl h
            · exact Or.inr ⟨List.mem_cons_self, hloop, hmem _ (Or.inl rfl)⟩
          · exact Or.inr ⟨List.mem_cons_self, hloop, hmem _ (Or.inr rfl)⟩
        · exact Or.inr ⟨List.mem_cons_of_mem _ hx, h⟩
      · have hkeep : best v ≠ none ∨ v = a ∨ v = b → best₂ v ≠ none := by
          rintro (h | h | h)
          · exact k₂ v (Or.inl (k₁ v (Or.inl h)))
          · exact k₂ v (Or.inl (k₁ v (Or.inr h)))
          · exact k₂ v (Or.inr h)
        rcases hv with hv | ⟨f, hf, hfd, hvf⟩
        · exact (ih best₂).2 v (Or.inl (hkeep (Or.inl hv)))
        · rcases List.mem_cons.1 hf with rfl | hf
          · rw [hab, Sym2.mem_iff] at hvf
            exact (ih best₂).2 v (Or.inl (hkeep (Or.inr hvf)))
          · exact (ih best₂).2 v (Or.inr ⟨f, hf, hfd, hvf⟩)

/-- Against an oracle of weights `w`, the scan leaves each vertex with a choice no heavier than
its earlier choice and than every edge of the list at it other than a self-loop. -/
private theorem scan_le (ends : E → Sym2 V) (oracle : {ι : Type} → LEQuery E ι → ι) (w : E → W)
    (hw : ∀ a b, oracle (.le a b) = decide (w a ≤ w b)) (L : List E) (best : V → Option E)
    (v : V) (x : E) (hx : (scan ends L best).eval oracle v = some x) :
    (∀ g, best v = some g → w x ≤ w g) ∧
      ∀ f ∈ L, ¬(ends f).IsDiag → v ∈ ends f → w x ≤ w f := by
  induction L generalizing best with
  | nil =>
    simp only [scan, FreeM.eval_pure] at hx
    exact ⟨fun g hg => by rw [hx] at hg; cases hg; exact le_rfl, by simp⟩
  | cons e es ih =>
    unfold scan at hx
    split at hx
    · next hloop =>
      obtain ⟨h₁, h₂⟩ := ih best hx
      refine ⟨h₁, fun f hf hfd hvf => ?_⟩
      rcases List.mem_cons.1 hf with rfl | hf
      · exact absurd hloop hfd
      · exact h₂ f hf hfd hvf
    · next hloop =>
      simp only [FreeM.eval_bind] at hx
      set a := (Quot.out (ends e)).1
      set b := (Quot.out (ends e)).2
      have hab : ends e = s(a, b) := (Sym2.mk_fst_out_snd_out _).symm
      obtain ⟨m₁, n₁⟩ := offer_le oracle w hw best a e
      set best₁ := (offer best a e).eval oracle
      obtain ⟨m₂, n₂⟩ := offer_le oracle w hw best₁ b e
      set best₂ := (offer best₁ b e).eval oracle
      obtain ⟨h₁, h₂⟩ := ih best₂ hx
      refine ⟨fun g hg => ?_, fun f hf hfd hvf => ?_⟩
      · obtain ⟨y₁, hy₁, hy₁g⟩ := m₁ v g hg
        obtain ⟨y₂, hy₂, hy₂g⟩ := m₂ v y₁ hy₁
        exact (h₁ y₂ hy₂).trans (hy₂g.trans hy₁g)
      · rcases List.mem_cons.1 hf with rfl | hf
        · rw [hab, Sym2.mem_iff] at hvf
          rcases hvf with rfl | rfl
          · obtain ⟨y₁, hy₁, hy₁e⟩ := n₁
            obtain ⟨y₂, hy₂, hy₂g⟩ := m₂ _ y₁ hy₁
            exact (h₁ y₂ hy₂).trans (hy₂g.trans hy₁e)
          · obtain ⟨y₂, hy₂, hy₂e⟩ := n₂
            exact (h₁ y₂ hy₂).trans hy₂e
        · exact h₂ f hf hfd hvf

private theorem mem_boruvkaStep {ends : E → Sym2 V} {S : Finset E}
    {oracle : {ι : Type} → LEQuery E ι → ι} {e : E} :
    e ∈ (boruvkaStep ends S).eval oracle ↔
      e ∈ S ∧ ∃ v, (scan ends S.toList fun _ => none).eval oracle v = some e := by
  simp [boruvkaStep]

/-- One Borůvka step makes at most two comparisons per edge, against every oracle. -/
theorem countQueries_boruvkaStep_le (ends : E → Sym2 V) (S : Finset E)
    (oracle : {ι : Type} → LEQuery E ι → ι) :
    (boruvkaStep ends S).countQueries oracle ≤ 2 * #S := by
  simpa [boruvkaStep] using countQueries_scan_le ends oracle S.toList fun _ => none

/-- Against the comparison oracle of weights `w`, every edge selected by a Borůvka step is in the
minimum spanning forest: it is the lightest edge leaving the vertex that selects it, so the cut
property applies (§2, p. 12). -/
theorem boruvkaStep_subset_msf (ends : E → Sym2 V) (S : Finset E) (w : E → W) :
    (boruvkaStep ends S).eval (LEQuery.keyOracle w) ⊆ msf ends w S := by
  intro e he
  obtain ⟨heS, v, hv⟩ := mem_boruvkaStep.1 he
  obtain ⟨-, hmin⟩ := scan_le ends _ w (fun _ _ => rfl) S.toList (fun _ => none) v e hv
  rcases (scan_spec ends _ S.toList fun _ => none).1 v e hv with h | ⟨-, hloop, hve⟩
  · simp at h
  obtain ⟨u, hu⟩ := Sym2.mem_iff_exists.1 hve
  have hne : v ≠ u := fun h => hloop (by rw [hu, h]; exact Sym2.mk_isDiag_iff.2 rfl)
  refine mem_msf_of_mem_edgeCut (P := {v}) w heS
    (Graph.mem_edgeCut_iff.2 ⟨v, u, hu, rfl, Ne.symm hne⟩) fun f hf hcut => ?_
  obtain ⟨x, y, hxy, hx, hy⟩ := Graph.mem_edgeCut_iff.1 hcut
  rw [toGraph_isLink] at hxy
  rw [Set.mem_singleton_iff] at hx hy
  subst hx
  refine hmin f (mem_toList.2 hf) ?_ (by simp [hxy])
  rw [hxy, Sym2.mk_isDiag_iff]
  exact fun h => hy h.symm

/-- **Halving**: contracting the edges selected by a Borůvka step leaves at most half as many
non-isolated vertices, against every oracle. Every non-isolated vertex selects an edge, so each
class of the contraction that meets a non-isolated vertex has at least two of them. -/
theorem two_mul_card_support_boruvkaStep_le [DecidableEq E] (ends : E → Sym2 V) (S : Finset E)
    (oracle : {ι : Type} → LEQuery E ι → ι) {C : Finset E}
    (hC : (boruvkaStep ends S).eval oracle = C) :
    2 * #(support (Sym2.map (contract ends C) ∘ ends) (S \ C)) ≤ #(support ends S) := by
  set q := contract ends (C : Set E)
  set X := support ends S
  have hsub : support (Sym2.map q ∘ ends) (S \ C) ⊆ X.image q := by
    intro v' hv'
    obtain ⟨e, he, hloop, hv'e⟩ := mem_support.1 hv'
    rw [Function.comp_apply, Sym2.mem_map] at hv'e
    obtain ⟨a, ha, rfl⟩ := hv'e
    have hl : ¬(ends e).IsDiag := fun h => hloop (by simpa using h.map (f := q))
    exact mem_image_of_mem q (mem_support.2 ⟨e, (mem_sdiff.1 he).1, hl, ha⟩)
  have hhalf : 2 * #(X.image q) ≤ #X := by
    refine mul_card_image_le_card X 2 fun b hb => ?_
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hb
    obtain ⟨e, heS, hloop, hae⟩ := mem_support.1 ha
    obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.1
      ((scan_spec ends oracle S.toList fun _ => none).2 a
      (Or.inr ⟨e, mem_toList.2 heS, hloop, hae⟩))
    rcases (scan_spec ends oracle S.toList fun _ => none).1 a x hx with h | ⟨hxS, hxl, hax⟩
    · cases h
    obtain ⟨u, hu⟩ := Sym2.mem_iff_exists.1 hax
    have hne : a ≠ u := fun h => hxl (by rw [hu, h]; exact Sym2.mk_isDiag_iff.2 rfl)
    have hxC : x ∈ C := hC ▸ mem_boruvkaStep.2 ⟨mem_toList.1 hxS, a, hx⟩
    have hqu : q u = q a := contract_eq_contract_iff.2 (Joins.of_mem hxC (hu.trans Sym2.eq_swap))
    have huX : u ∈ X := mem_support.2 ⟨x, mem_toList.1 hxS, hxl, by simp [hu]⟩
    calc 2 = #{a, u} := (card_pair hne).symm
      _ ≤ _ := card_le_card fun y hy => by
        rcases mem_insert.1 hy with rfl | hy
        · simp [ha]
        · rw [mem_singleton.1 hy]; simp [huX, hqu]
  exact (Nat.mul_le_mul_left 2 (card_le_card hsub)).trans hhalf

/-! ### `k` steps -/

/-- The outcome of Borůvka steps on the edges `S` of a multigraph `ends`. -/
structure BoruvkaResult (V E : Type) where
  /-- The edges selected by the steps. -/
  chosen : Finset E
  /-- The contraction of the vertices: the contracted multigraph is `Sym2.map proj ∘ ends`. -/
  proj : V → V
  /-- The remaining edges. -/
  rest : Finset E

/-- `r` describes a contraction of the edges `S` of `ends`: the remaining edges are edges of `S`
that are not self-loops after contraction, the selected edges are edges of `S`, and `proj`
identifies exactly the vertices joined by the selected edges. -/
structure BoruvkaResult.IsContraction (ends : E → Sym2 V) (S : Finset E) (r : BoruvkaResult V E) :
    Prop where
  /-- The selected edges are edges of `S`. -/
  chosen_subset : r.chosen ⊆ S
  /-- The remaining edges are edges of `S`. -/
  rest_subset : r.rest ⊆ S
  /-- No remaining edge is a self-loop of the contracted multigraph. -/
  not_isDiag : ∀ e ∈ r.rest, ¬(Sym2.map r.proj (ends e)).IsDiag
  /-- `proj` identifies exactly the vertices joined by the selected edges. -/
  proj_eq_iff : ∀ u v, r.proj u = r.proj v ↔ Joins ends r.chosen u v

variable [DecidableEq E]

/-- **`k` Borůvka steps** (§4, Algorithm 2, lines 1–2, p. 25): select edges, contract them, drop
the edges that became self-loops, and repeat on the contracted multigraph. -/
noncomputable def boruvka (ends : E → Sym2 V) (S : Finset E) :
    ℕ → FreeM (LEQuery E) (BoruvkaResult V E)
  | 0 => pure ⟨∅, id, {e ∈ S | ¬(ends e).IsDiag}⟩
  | k + 1 => do
    let C ← boruvkaStep ends S
    let q := contract ends C
    let r ← boruvka (Sym2.map q ∘ ends) {e ∈ S \ C | ¬(Sym2.map q (ends e)).IsDiag} k
    return ⟨C ∪ r.chosen, r.proj ∘ q, r.rest⟩

private theorem eval_boruvka_succ (ends : E → Sym2 V) (S : Finset E) (k : ℕ)
    (oracle : {ι : Type} → LEQuery E ι → ι) :
    (boruvka ends S (k + 1)).eval oracle =
      let C := (boruvkaStep ends S).eval oracle
      let q := contract ends C
      let r := (boruvka (Sym2.map q ∘ ends) {e ∈ S \ C | ¬(Sym2.map q (ends e)).IsDiag} k).eval
        oracle
      ⟨C ∪ r.chosen, r.proj ∘ q, r.rest⟩ := by
  simp [boruvka]

omit [DecidableEq V] [DecidableEq E] in
private theorem map_comp_map {f g : V → V} (ends : E → Sym2 V) :
    Sym2.map g ∘ (Sym2.map f ∘ ends) = Sym2.map (g ∘ f) ∘ ends :=
  funext fun _ => Sym2.map_map _

/-- `k` Borůvka steps make at most `2 k |S|` comparisons, against every oracle. -/
theorem countQueries_boruvka_le (ends : E → Sym2 V) (S : Finset E) (k : ℕ)
    (oracle : {ι : Type} → LEQuery E ι → ι) :
    (boruvka ends S k).countQueries oracle ≤ 2 * k * #S := by
  induction k generalizing ends S with
  | zero => simp [boruvka]
  | succ k ih =>
    set C := (boruvkaStep ends S).eval oracle with hC
    have hk : (boruvka ends S (k + 1)).countQueries oracle =
        (boruvkaStep ends S).countQueries oracle +
          (boruvka (Sym2.map (contract ends (C : Set E)) ∘ ends)
            {e ∈ S \ C | ¬(Sym2.map (contract ends (C : Set E)) (ends e)).IsDiag} k).countQueries
              oracle := by
      simp [boruvka, hC]
    rw [hk]
    have h₁ := countQueries_boruvkaStep_le ends S oracle
    have h₂ := ih (Sym2.map (contract ends C) ∘ ends)
      {e ∈ S \ C | ¬(Sym2.map (contract ends C) (ends e)).IsDiag}
    have h₃ : #{e ∈ S \ C | ¬(Sym2.map (contract ends C) (ends e)).IsDiag} ≤ #S :=
      card_le_card ((filter_subset _ _).trans sdiff_subset)
    have h₄ := Nat.mul_le_mul_left (2 * k) h₃
    exact (Nat.add_le_add h₁ (h₂.trans h₄)).trans
      (le_of_eq (by rw [Nat.mul_add, Nat.mul_one, Nat.add_mul, Nat.add_comm]))

/-- The result of `k` Borůvka steps is a contraction of `S`, against every oracle. -/
theorem isContraction_boruvka (ends : E → Sym2 V) (S : Finset E) (k : ℕ)
    (oracle : {ι : Type} → LEQuery E ι → ι) :
    ((boruvka ends S k).eval oracle).IsContraction ends S := by
  induction k generalizing ends S with
  | zero =>
    refine ⟨by simp [boruvka], by simp [boruvka], fun e he => ?_, fun u v => ?_⟩
    · simp only [boruvka, FreeM.eval_pure, mem_filter] at he ⊢
      simpa [Sym2.map_id] using he.2
    · simp [boruvka]
  | succ k ih =>
    rw [eval_boruvka_succ]
    set C := (boruvkaStep ends S).eval oracle
    set q := contract ends (C : Set E)
    set S₁ := {e ∈ S \ C | ¬(Sym2.map q (ends e)).IsDiag}
    have hS₁ : S₁ ⊆ S := (filter_subset _ _).trans sdiff_subset
    have hCS : C ⊆ S := fun e he => (mem_boruvkaStep.1 he).1
    obtain ⟨hch, hre, hdiag, hproj⟩ := ih (Sym2.map q ∘ ends) S₁
    refine ⟨union_subset hCS (hch.trans hS₁), hre.trans hS₁, fun e he => ?_, fun u v => ?_⟩
    · simpa [Sym2.map_map] using hdiag e he
    · simp only [Function.comp_apply]
      rw [hproj, joins_map_iff fun _ _ => contract_eq_contract_iff, coe_union, Set.union_comm]

/-- **Halving over `k` steps**: after `k` Borůvka steps, the contracted multigraph has at most
`n / 2 ^ k` non-isolated vertices, where `n` is the number of non-isolated vertices of `S`,
against every oracle (§4, p. 25). -/
theorem card_support_boruvka_le (ends : E → Sym2 V) (S : Finset E) (k : ℕ)
    (oracle : {ι : Type} → LEQuery E ι → ι) {r : BoruvkaResult V E}
    (hr : (boruvka ends S k).eval oracle = r) :
    #(support (Sym2.map r.proj ∘ ends) r.rest) ≤ #(support ends S) / 2 ^ k := by
  subst hr
  induction k generalizing ends S with
  | zero =>
    simp only [boruvka, FreeM.eval_pure, pow_zero, Nat.div_one, Sym2.map_id, Function.id_comp]
    rw [support_filter_not_isDiag]
  | succ k ih =>
    rw [eval_boruvka_succ]
    set C := (boruvkaStep ends S).eval oracle
    set q := contract ends (C : Set E)
    have h := ih (Sym2.map q ∘ ends) {e ∈ S \ C | ¬(Sym2.map q (ends e)).IsDiag}
    rw [map_comp_map] at h
    have hhalf := two_mul_card_support_boruvkaStep_le ends S oracle (C := C) rfl
    have hfilter := support_filter_not_isDiag (Sym2.map q ∘ ends) (S \ C)
    simp only [Function.comp_apply] at hfilter
    rw [hfilter] at h
    calc _ ≤ _ := h
      _ ≤ #(support ends S) / 2 / 2 ^ k :=
        Nat.div_le_div_right ((Nat.le_div_iff_mul_le two_pos).2 (by rw [Nat.mul_comm]; exact hhalf))
      _ = #(support ends S) / 2 ^ (k + 1) := by rw [Nat.div_div_eq_div_mul, pow_succ']

/-- **Correctness of `k` Borůvka steps**, a step in the proof of Theorem 4.1 of
[KhannaPuttermanSong2026] (§2, p. 12, by the paper's Facts 2.2 and 2.4): with distinct weights,
against the comparison oracle of `w`, the minimum spanning forest of `S` is the selected edges
together with the minimum spanning forest of the remaining edges in the contracted multigraph. -/
theorem msf_eq_union_boruvka (ends : E → Sym2 V) (S : Finset E) (k : ℕ) (w : E → W)
    (hw : Function.Injective w) {r : BoruvkaResult V E}
    (hr : (boruvka ends S k).eval (LEQuery.keyOracle w) = r) :
    msf ends w S = r.chosen ∪ msf (Sym2.map r.proj ∘ ends) w r.rest := by
  subst hr
  induction k generalizing ends S with
  | zero =>
    simp only [boruvka, FreeM.eval_pure, empty_union, Sym2.map_id, Function.id_comp]
    rw [msf_filter_not_isDiag]
  | succ k ih =>
    rw [eval_boruvka_succ]
    set C := (boruvkaStep ends S).eval (LEQuery.keyOracle w)
    set q := contract ends (C : Set E)
    have h := ih (Sym2.map q ∘ ends) {e ∈ S \ C | ¬(Sym2.map q (ends e)).IsDiag}
    rw [map_comp_map] at h
    have hfilter := msf_filter_not_isDiag w (Sym2.map q ∘ ends) (S \ C)
    simp only [Function.comp_apply] at hfilter
    rw [hfilter] at h
    rw [msf_eq_union_msf_map w hw (boruvkaStep_subset_msf ends S w)
      fun _ _ => contract_eq_contract_iff, h, union_assoc]

end Cslib.Query
