/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.MaxFlow.VertexSeparator
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.OddCycleTransversal

/-!
# Odd cycle transversal by iterative compression

`Cslib.Algorithms.Lean.IterativeCompression.oct G k` decides whether a simple graph `G` on `Fin n`
has an odd cycle transversal (`SimpleGraph.IsOddCycleTransversal`) of at most `k` vertices. When
one exists it returns one, together with a Boolean colouring that is proper on the edges outside
it. This is the iterative compression algorithm of Reed, Smith and Vetta [ReedSmithVetta2004], with
the three-way guess of [Hueffner2009, Section 3] and [CyganEtAl2015, Section 4.4].

## Algorithm

*Iteration* (`Cslib.Algorithms.Lean.IterativeCompression.loop`). The vertices are added one at a
time. The state after `i` vertices is an odd cycle transversal `S`, `|S| ≤ k`, of the subgraph
`prefixGraph G i` spanned by the first `i` vertices, with a colouring proper off `S`. Adding
vertex `i` to `S` gives an odd cycle transversal `W` of `prefixGraph G (i + 1)`. If `|W| ≤ k`, it
is the new state. Otherwise `|W| = k + 1` and the compression step either shrinks `W` to at most
`k` vertices or proves that `prefixGraph G (i + 1)` has no odd cycle transversal of at most `k`
vertices. Then neither has `G`, and the algorithm stops.

*Compression* (`Cslib.Algorithms.Lean.IterativeCompression.compress`). Given `W` and a colouring
`c₀` proper off `W`, enumerate the `3 ^ |W|` guesses `g : Fin n → Option Bool` that are `none`
off `W` (`Cslib.Algorithms.Lean.IterativeCompression.guesses`). A vertex `w ∈ W` with
`g w = none` is deleted, and `g w = some b` colours it `b`. For a guess that is proper on the kept
part of `W`, compute a minimum separator `X` of the keep terminals from the flip terminals in
`G - W`. Accept if the deleted part of `W` and `X` together have at most `k` vertices. Correctness
is the compression lemma `SimpleGraph.exists_isOddCycleTransversal_card_le_iff` and its two
directions.

This module defines the pure mathematical algorithm and proves its soundness and completeness; the
Word-RAM running-time theorem lives in `CslibFrontier.Algorithms.WordRAM.OddCycleTransversal`.

## Main definitions

* `Cslib.Algorithms.Lean.IterativeCompression.prefixGraph`: the subgraph on the first `m` vertices.
* `Cslib.Algorithms.Lean.IterativeCompression.IsProperOff`: a colouring vector is proper on the
  edges outside a list of vertices.
* `Cslib.Algorithms.Lean.IterativeCompression.guesses`: the `3 ^ |W|` guesses on `W`.
* `Cslib.Algorithms.Lean.IterativeCompression.leaf`: one guess, solved by a minimum separator.
* `Cslib.Algorithms.Lean.IterativeCompression.compress`: the compression step.
* `Cslib.Algorithms.Lean.IterativeCompression.step`,
  `Cslib.Algorithms.Lean.IterativeCompression.loop`: one step of the iteration, and the iteration.
* `Cslib.Algorithms.Lean.IterativeCompression.oct`: odd cycle transversal of size at most `k`.

## Main results

* `Cslib.Algorithms.Lean.IterativeCompression.length_guesses`,
  `Cslib.Algorithms.Lean.IterativeCompression.mem_guesses`: the guesses are exactly the
  `Option Bool` labellings that are `none` off `W`, and there are `3 ^ |W|` of them.
* `Cslib.Algorithms.Lean.IterativeCompression.compress_sound`,
  `Cslib.Algorithms.Lean.IterativeCompression.compress_complete`: the compression step.
* `Cslib.Algorithms.Lean.IterativeCompression.oct_sound`,
  `Cslib.Algorithms.Lean.IterativeCompression.oct_isOddCycleTransversal`,
  `Cslib.Algorithms.Lean.IterativeCompression.oct_eq_none`,
  `Cslib.Algorithms.Lean.IterativeCompression.oct_isSome_iff`: correctness.

## References

* [B. Reed, K. Smith, A. Vetta, *Finding odd cycle transversals*][ReedSmithVetta2004]
* [F. Hüffner, *Algorithm engineering for optimal graph bipartization*][Hueffner2009]
* [M. Cygan, F. V. Fomin, Ł. Kowalik, D. Lokshtanov, D. Marx, M. Pilipczuk, M. Pilipczuk,
  S. Saurabh, *Parameterized Algorithms*][CyganEtAl2015]
-/

public section

namespace Cslib.Algorithms.Lean.IterativeCompression

open SimpleGraph SimpleGraph.OddCycleTransversal Cslib.Algorithms.Lean.MaxFlow

variable {n : ℕ}

/-! ### Prefix subgraphs -/

/-- The subgraph of `G` spanned by the vertices `0, …, m - 1`. The other vertices are isolated. -/
@[expose] def prefixGraph (G : SimpleGraph (Fin n)) (m : ℕ) : SimpleGraph (Fin n) where
  Adj u v := G.Adj u v ∧ u.1 < m ∧ v.1 < m
  symm := ⟨fun _ _ ⟨hadj, hu, hv⟩ => ⟨hadj.symm, hv, hu⟩⟩
  loopless := ⟨fun v h => G.loopless.irrefl v h.1⟩

@[simp]
theorem prefixGraph_adj {G : SimpleGraph (Fin n)} {m : ℕ} {u v : Fin n} :
    (prefixGraph G m).Adj u v ↔ G.Adj u v ∧ u.1 < m ∧ v.1 < m :=
  Iff.rfl

instance (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (m : ℕ) :
    DecidableRel (prefixGraph G m).Adj :=
  fun u v => inferInstanceAs (Decidable (G.Adj u v ∧ u.1 < m ∧ v.1 < m))

theorem prefixGraph_le (G : SimpleGraph (Fin n)) (m : ℕ) : prefixGraph G m ≤ G :=
  fun _ _ h => h.1

theorem prefixGraph_mono (G : SimpleGraph (Fin n)) {m m' : ℕ} (h : m ≤ m') :
    prefixGraph G m ≤ prefixGraph G m' :=
  fun _ _ ⟨hadj, hu, hv⟩ => ⟨hadj, Nat.lt_of_lt_of_le hu h, Nat.lt_of_lt_of_le hv h⟩

theorem prefixGraph_of_le (G : SimpleGraph (Fin n)) {m : ℕ} (h : n ≤ m) : prefixGraph G m = G := by
  ext u v
  simp only [prefixGraph_adj, and_iff_left_iff_imp]
  exact fun _ => ⟨by omega, by omega⟩

/-! ### Guesses -/

/-- The `3 ^ |ws|` guesses on `ws`: the vectors `g` with `g v = none` off `ws` and `g w ∈
{none, some false, some true}` on `ws`. -/
def guesses : List (Fin n) → List (Vector (Option Bool) n)
  | [] => [Vector.replicate n none]
  | w :: ws => (guesses ws).flatMap fun g =>
      [vset g w none, vset g w (some false), vset g w (some true)]

theorem length_guesses (ws : List (Fin n)) : (guesses ws).length = 3 ^ ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    rw [guesses, List.length_flatMap]
    simp only [List.length_cons, List.length_nil, List.map_const', List.sum_replicate, ih,
      smul_eq_mul, pow_succ]

theorem mem_guesses {ws : List (Fin n)} {g : Vector (Option Bool) n}
    (hg : ∀ v, v ∉ ws → vget g v = none) : g ∈ guesses ws := by
  induction ws generalizing g with
  | nil =>
    obtain rfl : g = Vector.replicate n none := Vector.ext fun i hi => by
      rw [Vector.getElem_replicate]; exact hg ⟨i, hi⟩ List.not_mem_nil
    exact List.mem_singleton_self _
  | cons w ws ih =>
    have hg' : vset g w none ∈ guesses ws := ih fun v hv => by
      by_cases hvw : w = v
      · rw [hvw, vget_vset_self]
      · rw [vget_vset_ne _ _ hvw]
        exact hg v fun h => (List.mem_cons.mp h).elim (fun h' => hvw h'.symm) hv
    have hset : vset (vset g w none) w (vget g w) = g := by
      refine Vector.ext fun i hi => ?_
      simp only [vset, vget, Vector.getElem_set]
      split_ifs with h <;> (try subst h) <;> rfl
    have hmem : ∀ x : Option Bool, vset (vset g w none) w x ∈
        [vset (vset g w none) w none, vset (vset g w none) w (some false),
          vset (vset g w none) w (some true)] := by
      rintro (_ | _ | _) <;> simp
    rw [guesses, List.mem_flatMap]
    refine ⟨_, hg', ?_⟩
    have := hmem (vget g w)
    rwa [hset] at this

/-! ### Terminal tables -/

/-- The membership table of `W`. -/
def memTable (W : List (Fin n)) : Vector Bool n :=
  Vector.ofFn fun v => decide (v ∈ W)

/-- The keep terminals of a guess `g` relative to the colouring `c₀`: the vertices `v ∉ W` with a
neighbour `w ∈ W` such that `g w = some b` and `b ≠ c₀ v`. -/
def keepTable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (W : List (Fin n))
    (g : Vector (Option Bool) n) (c₀ : Vector Bool n) : Vector Bool n :=
  Vector.ofFn fun v => decide (v ∉ W ∧
    ∃ w ∈ W, (vget g w).isSome ∧ G.Adj w v ∧ (vget g w).getD false ≠ vget c₀ v)

/-- The flip terminals of a guess `g` relative to the colouring `c₀`: the vertices `v ∉ W` with a
neighbour `w ∈ W` such that `g w = some b` and `b = c₀ v`. -/
def flipTable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (W : List (Fin n))
    (g : Vector (Option Bool) n) (c₀ : Vector Bool n) : Vector Bool n :=
  Vector.ofFn fun v => decide (v ∉ W ∧
    ∃ w ∈ W, (vget g w).isSome ∧ G.Adj w v ∧ (vget g w).getD false = vget c₀ v)

/-- The colouring produced by a guess `g` and a side labelling: `g` on `W`; off `W`, keep the
colour `c₀ v` where `side v = true` and flip it where `side v = false`. -/
def newColour (W : List (Fin n)) (g : Vector (Option Bool) n) (c₀ side : Vector Bool n) :
    Vector Bool n :=
  Vector.ofFn fun v => if v ∈ W then (vget g v).getD false else (vget c₀ v == vget side v)

private theorem vget_ofFn {α : Type*} (f : Fin n → α) (v : Fin n) : vget (Vector.ofFn f) v = f v :=
  Vector.getElem_ofFn _

@[simp]
theorem vget_memTable (W : List (Fin n)) (v : Fin n) : vget (memTable W) v = decide (v ∈ W) :=
  vget_ofFn _ v

/-- The guess `g` deletes `D` and colours `W \ D` by `σ`. -/
private def Encodes (W : List (Fin n)) (g : Vector (Option Bool) n) (D : Set (Fin n))
    (σ : Fin n → Bool) : Prop :=
  ∀ w ∈ W, (w ∈ D ↔ vget g w = none) ∧ (w ∉ D → vget g w = some (σ w))

private theorem terminal_iff {W : List (Fin n)} {g : Vector (Option Bool) n} {D : Set (Fin n)}
    {σ : Fin n → Bool} (h : Encodes W g D σ) (p : Bool → Prop) {w : Fin n} (hw : w ∈ W) :
    ((vget g w).isSome ∧ p ((vget g w).getD false)) ↔ (w ∉ D ∧ p (σ w)) := by
  by_cases hD : w ∈ D
  · have hg := (h w hw).1.mp hD
    simp only [hg, Option.isSome_none, Bool.false_eq_true, false_and, hD, not_true_eq_false]
  · have hg := (h w hw).2 hD
    simp only [hg, Option.isSome_some, Option.getD_some, true_and, hD, not_false_eq_true]

private theorem keepTable_iff (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {W : List (Fin n)}
    {g : Vector (Option Bool) n} {D : Set (Fin n)} {σ : Fin n → Bool} (h : Encodes W g D σ)
    (c₀ : Vector Bool n) (v : Fin n) :
    vget (keepTable G W g c₀) v = true ↔
      v ∈ keepTerminals G {w | w ∈ W} D σ fun u => vget c₀ u := by
  rw [keepTable, vget_ofFn, decide_eq_true_iff, mem_keepTerminals]
  refine and_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨w, hw, hs, hadj, hne⟩
    obtain ⟨hD, hσ⟩ := (terminal_iff h (fun b => b ≠ vget c₀ v) hw).mp ⟨hs, hne⟩
    exact ⟨w, hw, hD, hadj, hσ⟩
  · rintro ⟨w, hw, hD, hadj, hσ⟩
    obtain ⟨hs, hne⟩ := (terminal_iff h (fun b => b ≠ vget c₀ v) hw).mpr ⟨hD, hσ⟩
    exact ⟨w, hw, hs, hadj, hne⟩

private theorem flipTable_iff (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {W : List (Fin n)}
    {g : Vector (Option Bool) n} {D : Set (Fin n)} {σ : Fin n → Bool} (h : Encodes W g D σ)
    (c₀ : Vector Bool n) (v : Fin n) :
    vget (flipTable G W g c₀) v = true ↔
      v ∈ flipTerminals G {w | w ∈ W} D σ fun u => vget c₀ u := by
  rw [flipTable, vget_ofFn, decide_eq_true_iff, mem_flipTerminals]
  refine and_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨w, hw, hs, hadj, heq⟩
    obtain ⟨hD, hσ⟩ := (terminal_iff h (fun b => b = vget c₀ v) hw).mp ⟨hs, heq⟩
    exact ⟨w, hw, hD, hadj, hσ⟩
  · rintro ⟨w, hw, hD, hadj, hσ⟩
    obtain ⟨hs, heq⟩ := (terminal_iff h (fun b => b = vget c₀ v) hw).mpr ⟨hD, hσ⟩
    exact ⟨w, hw, hs, hadj, heq⟩

/-! ### The compression step -/

/-- A colouring `c` is proper on the edges of `G` with both endpoints outside `S`. -/
abbrev IsProperOff (G : SimpleGraph (Fin n)) (c : Vector Bool n) (S : List (Fin n)) : Prop :=
  ∀ ⦃u v⦄, G.Adj u v → u ∉ S → v ∉ S → vget c u ≠ vget c v

variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-- One leaf of the compression step: the guess `g` on `W`. If `g` is proper on the kept part of
`W`, compute a minimum separator of its keep terminals from its flip terminals in `G - W`, and
accept if the deleted part of `W` and the separator have at most `k` vertices together. -/
@[expose] def leaf (k : ℕ) (W : List (Fin n)) (c₀ : Vector Bool n) (g : Vector (Option Bool) n) :
    Option (List (Fin n) × Vector Bool n) :=
  if ∀ u ∈ W, ∀ v ∈ W, G.Adj u v → ∀ a b, vget g u = some a → vget g v = some b → a ≠ b then
    let out := minSeparator G (memTable W) (keepTable G W g c₀) (flipTable G W g c₀)
    let D := W.filter fun w => (vget g w).isNone
    if D.length + out.sep.length ≤ k then some (D ++ out.sep, newColour W g c₀ out.side)
    else none
  else
    none

/-- **Compression step.** Given an odd cycle transversal `W` of `G` with a colouring `c₀` proper
off `W`, look for an odd cycle transversal of at most `k` vertices: run `leaf` on the
`3 ^ |W|` guesses on `W`. -/
@[expose] def compress (k : ℕ) (W : List (Fin n)) (c₀ : Vector Bool n) :
    Option (List (Fin n) × Vector Bool n) :=
  (guesses W).findSome? (leaf G k W c₀)

variable {G}

/-- Soundness of a leaf. -/
private theorem leaf_sound {k : ℕ} {W : List (Fin n)} {c₀ : Vector Bool n}
    {g : Vector (Option Bool) n} (hc₀ : IsProperOff G c₀ W) (hW : W.Nodup)
    {S : List (Fin n)} {c : Vector Bool n} (h : leaf G k W c₀ g = some (S, c)) :
    S.Nodup ∧ S.length ≤ k ∧ IsProperOff G c S := by
  unfold leaf at h
  split_ifs at h with hprop
  · dsimp only at h
    set out := minSeparator G (memTable W) (keepTable G W g c₀) (flipTable G W g c₀)
      with hout
    set D := W.filter fun w => (vget g w).isNone with hD
    split_ifs at h with hk
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have hmemD : ∀ {w}, w ∈ D ↔ w ∈ W ∧ vget g w = none := fun {w} => by
      simp only [hD, List.mem_filter, Option.isNone_iff_eq_none]
    have hsepW : ∀ {v}, v ∈ out.sep → v ∉ W := fun {v} hv => by
      have := minSeparator_vget_eq_false_of_mem_sep hv
      rwa [vget_memTable, decide_eq_false_iff_not] at this
    refine ⟨List.nodup_append.mpr ⟨hW.filter _, minSeparator_nodup_sep _ _ _ _,
      fun a ha b hb hab => hsepW (hab ▸ hb) (hmemD.mp ha).1⟩,
      (List.length_append).trans_le hk, ?_⟩
    have henc : Encodes W g {w | w ∈ W ∧ vget g w = none} fun w => (vget g w).getD false :=
      fun w hw => ⟨by simp only [Set.mem_ofPred_eq, hw, true_and],
        fun hD' => (Option.getD_of_ne_none (fun h' => hD' ⟨hw, h'⟩) false).symm⟩
    have hprop' : ∀ ⦃u v⦄, G.Adj u v → u ∈ {w | w ∈ W} → v ∈ {w | w ∈ W} →
        u ∉ {w | w ∈ W ∧ vget g w = none} → v ∉ {w | w ∈ W ∧ vget g w = none} →
        (vget g u).getD false ≠ (vget g v).getD false := fun u v huv hu hv hu' hv' =>
      hprop u hu v hv huv _ _ (Option.getD_of_ne_none (fun h' => hu' ⟨hu, h'⟩) false).symm
        (Option.getD_of_ne_none (fun h' => hv' ⟨hv, h'⟩) false).symm
    have hZ : ∀ {v}, v ∉ ({w | w ∈ W} : Set (Fin n)) → vget (memTable W) v = false :=
      fun {v} hv => (vget_memTable W v).trans (decide_eq_false hv)
    have key := proper_of_side (X := {v | v ∈ out.sep}) (side := fun v => vget out.side v)
      (c := fun v => vget (newColour W g c₀ out.side) v) (fun u v huv hu hv => hc₀ huv hu hv)
      hprop' (fun u v huv hu hv hus hvs => minSeparator_side_eq_of_adj huv (hZ hu) (hZ hv) hus hvs)
      (fun v hv hvs => minSeparator_side_eq_true ((keepTable_iff G henc c₀ v).mpr hv)
        (hZ (mem_keepTerminals.mp hv).1) hvs)
      (fun v hv _ => minSeparator_side_eq_false ((flipTable_iff G henc c₀ v).mpr hv))
      (fun v hv => by simp only [newColour, vget_ofFn, show v ∈ W from hv, ↓reduceIte])
      (fun v hv => by simp only [newColour, vget_ofFn, show v ∉ W from hv, ↓reduceIte])
    exact fun u v huv hu hv => key huv (fun h' => hu (List.mem_append.mpr (Or.imp hmemD.mpr id h')))
      (fun h' => hv (List.mem_append.mpr (Or.imp hmemD.mpr id h')))

/-- **Compression step, soundness.** An output of `compress` is an odd cycle transversal of at most
`k` vertices, without repetitions, with a colouring proper off it. -/
theorem compress_sound {k : ℕ} {W : List (Fin n)} {c₀ : Vector Bool n}
    (hc₀ : IsProperOff G c₀ W) (hW : W.Nodup) {S : List (Fin n)} {c : Vector Bool n}
    (h : compress G k W c₀ = some (S, c)) :
    S.Nodup ∧ S.length ≤ k ∧ IsProperOff G c S := by
  unfold compress at h
  obtain ⟨g, -, hg⟩ := List.exists_of_findSome?_eq_some h
  exact leaf_sound hc₀ hW hg

/-- **Compression step, completeness.** If `compress` finds nothing, then every odd cycle
transversal of `G` has more than `k` vertices. -/
theorem compress_complete {k : ℕ} {W : List (Fin n)} {c₀ : Vector Bool n}
    (hc₀ : IsProperOff G c₀ W) (hW : W.Nodup) (h : compress G k W c₀ = none)
    (T : Finset (Fin n)) (hT : G.IsOddCycleTransversal T) : k < T.card := by
  classical
  by_contra hk
  push Not at hk
  simp only [compress, List.findSome?_eq_none_iff] at h
  obtain ⟨cT, hcT⟩ := isOddCycleTransversal_iff_exists_bool.mp hT
  set g : Vector (Option Bool) n := Vector.ofFn fun v => if v ∈ W ∧ v ∉ T then some (cT v) else none
    with hg
  have hgv : ∀ v, vget g v = if v ∈ W ∧ v ∉ T then some (cT v) else none := fun v => vget_ofFn _ v
  have henc : Encodes W g ((T : Set (Fin n)) ∩ {w | w ∈ W}) cT := fun w hw => by
    by_cases hwT : w ∈ T <;> simp [hgv, hwT, hw]
  have hleaf := h g (mem_guesses fun v hv => by rw [hgv]; simp only [hv, false_and, ↓reduceIte])
  have hprop : ∀ u ∈ W, ∀ v ∈ W, G.Adj u v → ∀ a b, vget g u = some a → vget g v = some b →
      a ≠ b := fun u _ v _ huv a b ha hb => by
    rw [hgv] at ha hb
    split_ifs at ha hb with hu' hv'
    cases ha; cases hb
    exact hcT huv hu'.2 hv'.2
  unfold leaf at hleaf
  split_ifs at hleaf
  dsimp only at hleaf
  split_ifs at hleaf with hlen
  apply hlen
  -- The deleted part of `W` is `T ∩ W`.
  have hD : (W.filter fun w => (vget g w).isNone).length ≤ (T ∩ W.toFinset).card := by
    rw [← List.toFinset_card_of_nodup (hW.filter _)]
    refine Finset.card_le_card fun w hw => ?_
    simp only [List.mem_toFinset, List.mem_filter, hgv, Option.isNone_iff_eq_none] at hw
    obtain ⟨hwW, hw⟩ := hw
    split_ifs at hw with h'
    exact Finset.mem_inter.mpr ⟨by tauto, List.mem_toFinset.mpr hwW⟩
  -- The rest of `T` separates the terminals.
  have hsep := isSeparator_of_proper (S := (T : Set (Fin n))) (W := {w | w ∈ W})
    (c₀ := fun v => vget c₀ v) (σ := cT) (fun u v huv hu hv => hc₀ huv hu hv) hcT
    fun _ _ _ => rfl
  have hkeep : {v | vget (keepTable G W g c₀) v = true} =
      keepTerminals G {w | w ∈ W} ((T : Set (Fin n)) ∩ {w | w ∈ W}) cT fun u => vget c₀ u :=
    Set.ext fun v => keepTable_iff G henc c₀ v
  have hflip : {v | vget (flipTable G W g c₀) v = true} =
      flipTerminals G {w | w ∈ W} ((T : Set (Fin n)) ∩ {w | w ∈ W}) cT fun u => vget c₀ u :=
    Set.ext fun v => flipTable_iff G henc c₀ v
  have hZ : {v | vget (memTable W) v = true} ∪ ↑(T \ W.toFinset) = {w | w ∈ W} ∪ (T : Set _) := by
    ext v
    simp only [vget_memTable, decide_eq_true_iff, Set.mem_union, Set.mem_ofPred_eq,
      Finset.coe_sdiff, Set.mem_sdiff, Finset.mem_coe, List.coe_toFinset]
    tauto
  rw [← hkeep, ← hflip, ← hZ] at hsep
  have hX := minSeparator_length_sep_le hsep
  have hcard := Finset.card_inter_add_card_sdiff T W.toFinset
  omega

/-! ### The iteration -/

variable (G)

/-- One step of the iteration: add vertex `i` to the odd cycle transversal `S` of
`prefixGraph G i`, and compress if the result has `k + 1` vertices. -/
@[expose] def step (k : ℕ) (i : Fin n) :
    Option (List (Fin n) × Vector Bool n) → Option (List (Fin n) × Vector Bool n)
  | none => none
  | some (S, c) =>
    let W := if i ∈ S then S else i :: S
    if W.length ≤ k then some (W, c)
    else compress (prefixGraph G (i.1 + 1)) k W c

/-- The first `i` steps of the iteration, starting from `∅` and the all-`false` colouring. -/
@[expose] def loop (k : ℕ) : (i : ℕ) → i ≤ n → Option (List (Fin n) × Vector Bool n)
  | 0, _ => some ([], Vector.replicate n false)
  | i + 1, h => step G k ⟨i, h⟩ (loop k i (by omega))

/-- **Odd cycle transversal by iterative compression** [ReedSmithVetta2004] [Hueffner2009]: an odd
cycle transversal of `G` with at most `k` vertices and a colouring proper off it, or `none` if
there is no such transversal. -/
@[expose] def oct (k : ℕ) : Option (List (Fin n) × Vector Bool n) :=
  loop G k n le_rfl

variable {G}

/-- The loop invariant after `i` steps. -/
private def Inv (G : SimpleGraph (Fin n)) (k i : ℕ) : Option (List (Fin n) × Vector Bool n) → Prop
  | none => ∀ T : Finset (Fin n), (prefixGraph G i).IsOddCycleTransversal T → k < T.card
  | some (S, c) => S.Nodup ∧ S.length ≤ k ∧ IsProperOff (prefixGraph G i) c S

private theorem inv_step {k : ℕ} {i : Fin n} {r : Option (List (Fin n) × Vector Bool n)}
    (h : Inv G k i.1 r) : Inv G k (i.1 + 1) (step G k i r) := by
  rcases r with _ | ⟨S, c⟩
  · exact fun T hT => h T (hT.anti (prefixGraph_mono G (Nat.le_succ _)))
  obtain ⟨hS, _, hc⟩ := h
  set W := if i ∈ S then S else i :: S with hWdef
  have hWS : ∀ v, v ∈ W ↔ v = i ∨ v ∈ S := fun v => by
    by_cases hi : i ∈ S
    · simp only [hWdef, hi, ↓reduceIte, iff_or_self]
      exact fun h => h ▸ hi
    · simp only [hWdef, hi, ↓reduceIte, List.mem_cons]
  have hW : W.Nodup := by
    by_cases hi : i ∈ S
    · simpa only [hWdef, hi, ↓reduceIte] using hS
    · simpa only [hWdef, hi, ↓reduceIte] using List.nodup_cons.mpr ⟨hi, hS⟩
  have hcW : IsProperOff (prefixGraph G (i.1 + 1)) c W := by
    intro u v ⟨hadj, hu_lt, hv_lt⟩ hu hv
    rw [hWS, not_or] at hu hv
    exact hc ⟨hadj, by have := Fin.val_ne_of_ne hu.1; omega,
      by have := Fin.val_ne_of_ne hv.1; omega⟩ hu.2 hv.2
  dsimp only [step]
  rw [← hWdef]
  split_ifs with hk
  · exact ⟨hW, hk, hcW⟩
  · rcases hr : compress (prefixGraph G (i.1 + 1)) k W c with _ | ⟨S', c'⟩
    · exact compress_complete hcW hW hr
    · exact compress_sound hcW hW hr

private theorem inv_loop (k : ℕ) : ∀ (i : ℕ) (hi : i ≤ n), Inv G k i (loop G k i hi)
  | 0, _ => ⟨List.nodup_nil, Nat.zero_le _, fun _ _ ⟨_, hu, _⟩ => absurd hu (Nat.not_lt_zero _)⟩
  | i + 1, hi => inv_step (i := ⟨i, by omega⟩) (inv_loop k i (by omega))

/-- **Soundness.** An output `(S, c)` of `oct` has no repetitions, at most `k` vertices, and `c`
is proper on the edges of `G` outside `S`. -/
theorem oct_sound {k : ℕ} {S : List (Fin n)} {c : Vector Bool n}
    (h : oct G k = some (S, c)) : S.Nodup ∧ S.length ≤ k ∧ IsProperOff G c S := by
  have hinv := inv_loop (G := G) k n le_rfl
  rw [← oct, h] at hinv
  obtain ⟨hS, hk, hc⟩ := hinv
  rw [prefixGraph_of_le G le_rfl] at hc
  exact ⟨hS, hk, hc⟩

/-- **Soundness.** An output of `oct` is an odd cycle transversal of at most `k` vertices. -/
theorem oct_isOddCycleTransversal {k : ℕ} {S : List (Fin n)} {c : Vector Bool n}
    (h : oct G k = some (S, c)) :
    G.IsOddCycleTransversal {v | v ∈ S} ∧ S.length ≤ k := by
  obtain ⟨-, hk, hc⟩ := oct_sound h
  exact ⟨isOddCycleTransversal_iff_exists_bool.mpr ⟨fun v => vget c v, hc⟩, hk⟩

/-- **Completeness.** If `oct` returns `none`, every odd cycle transversal of `G` has more than
`k` vertices. -/
theorem oct_eq_none {k : ℕ} (h : oct G k = none) (T : Finset (Fin n))
    (hT : G.IsOddCycleTransversal T) : k < T.card := by
  have hinv := inv_loop (G := G) k n le_rfl
  rw [← oct, h] at hinv
  exact hinv T ((prefixGraph_of_le G le_rfl).symm ▸ hT)

/-- **Correctness.** `oct G k` succeeds exactly when `G` has an odd cycle transversal of at most
`k` vertices. -/
theorem oct_isSome_iff {k : ℕ} :
    (oct G k).isSome ↔ ∃ T : Finset (Fin n), G.IsOddCycleTransversal T ∧ T.card ≤ k := by
  classical
  constructor
  · intro h
    obtain ⟨⟨S, c⟩, hSc⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨hS, hk⟩ := oct_isOddCycleTransversal hSc
    refine ⟨S.toFinset, ?_, (List.toFinset_card_le S).trans hk⟩
    simpa only [List.coe_toFinset] using hS
  · rintro ⟨T, hT, hk⟩
    rcases hr : oct G k with _ | _
    · exact absurd (oct_eq_none hr T hT) (Nat.not_lt.mpr hk)
    · rfl

end Cslib.Algorithms.Lean.IterativeCompression
