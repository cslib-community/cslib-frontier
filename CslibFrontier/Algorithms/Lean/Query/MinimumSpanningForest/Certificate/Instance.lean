/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.Certificate.State
public import CslibFrontier.Algorithms.Lean.Query.Sort.LEQuery.KeyOracle
public import Mathlib.Data.PNat.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
# Instances, projection records and preferences of the certificate procedure

This file sets up the vocabulary of Algorithm 1 of
[Khanna, Putterman and Song][KhannaPuttermanSong2026] (§3.1, pp. 12–14) and of its analysis
(§3.3, pp. 16–18). The program itself is `Cslib.Query.Certificate.certificate`.

**Instances.** Following the program's shared design, every instance of the recursion has the
root's edge type `E` and vertex type `V`. A call receives an `Instance`: its recursion level
`d : ℕ+` (the root has level `1`, so that `t = γ d³ ≥ 1` once `γ ≥ 1`), its vertex set, its
ends map, its edges, and the *projection record* of each edge. The child built in a round from
the state `st` of its parent and the projected edges `S` (`Cslib.Query.Certificate.Instance.child`)
has the portals as vertices, the ends
`s(π u, π v)` in place of `s(u, v)`, and the record of each edge extended by the spokes at its ends
(Algorithm 1, lines 12–15).

**Records and admissibility** (p. 13). The record of an edge lists, for each preceding level, the
set of spokes at its ends used to project it (two spokes, or one when both ends share it). The edge
is `Cslib.Query.Certificate.Admissible` when every spoke in the record weighs at most the edge.
The admissibility test `Cslib.Query.Certificate.admissibilityTest` scans the record from the root
with `Cslib.Query.Certificate.findInvalid`, which returns the index of the first invalid entry
(`Cslib.Query.Certificate.firstInvalid`; the entry of index `k` is the projection made at level
`k + 1`) and stops there, so that it costs at most two comparisons per entry scanned
(`Cslib.Query.Certificate.countQueries_findInvalid_le_of_eq_some`).

**Preferences** (p. 13 and p. 17). At the start of a round, with spokes `σ`, portals `π` and
forest `F`, the preferred action of an edge `e` with ends `u, v` is *find* if an end has no spoke,
if `π u = π v`, or if `F≤p(e)` joins `u` and `v`, where `p(e)` is the heavier spoke; otherwise it
is *project* (`Cslib.Query.Certificate.pref`). The first two cases are the edges that are not
`Cslib.Query.Certificate.Projectable`. The algorithm only estimates preferences; its estimate is
forced to *find* on edges that are not projectable (`Cslib.Query.Certificate.maskAction`), which
is the one property the paper requires of the estimate (p. 13).

**Parameters and bad rounds.** A call at level `d` has `t = γ d³` blocks of `t` rounds and
`r = 8 t³` (p. 13, restated on p. 22): `Cslib.Query.Certificate.levelT`,
`Cslib.Query.Certificate.levelR`. The generic parts of Algorithm 1 — the schedule, the preference
estimator and the exact minimum spanning forest subroutine — are the fields of
`Cslib.Query.Certificate.Config`. Definition 3.4 (p. 17) of the bad rounds of an edge depends only
on its sequence of preferences: `Cslib.Query.Certificate.BadRound`, with at most `2t` bad rounds
(`Cslib.Query.Certificate.card_badRound_le`).

## Main definitions

* `Cslib.Query.Certificate.Action`, `Cslib.Query.Certificate.Instance`,
  `Cslib.Query.Certificate.Instance.root`, `Cslib.Query.Certificate.Instance.child`,
  `Cslib.Query.Certificate.Instance.WellFormed`.
* `Cslib.Query.Certificate.Admissible`, `Cslib.Query.Certificate.firstInvalid`,
  `Cslib.Query.Certificate.findInvalid`, `Cslib.Query.Certificate.admissibilityTest`.
* `Cslib.Query.Certificate.spokes`, `Cslib.Query.Certificate.Projectable`,
  `Cslib.Query.Certificate.PrefersFind`, `Cslib.Query.Certificate.pref`,
  `Cslib.Query.Certificate.maskAction`.
* `Cslib.Query.Certificate.Config`, `Cslib.Query.Certificate.BadRound`.

## Main results

* `Cslib.Query.Certificate.eval_findInvalid`, `Cslib.Query.Certificate.eval_admissibilityTest`:
  the test computes `firstInvalid` and admissibility against the comparison oracle of the weights.
* `Cslib.Query.Certificate.countQueries_findInvalid_le`,
  `Cslib.Query.Certificate.countQueries_findInvalid_le_of_eq_some`: `O(d)` comparisons, and
  `2 (k + 1)` when the first invalid entry has index `k` (p. 24).
* `Cslib.Query.Certificate.card_badRound_le`: at most `2t` bad rounds (p. 17).
* `Cslib.Query.Certificate.prefersFind_iff`, `Cslib.Query.Certificate.Projectable.exists_spokes`,
  `Cslib.Query.Certificate.prefersFind_of_not_projectable`,
  `Cslib.Query.Certificate.not_prefersFind_of_not_joins`, `Cslib.Query.Certificate.pref_congr`: the
  interface of the preference rule (p. 13), so that clients need not unfold it.

## References

* [S. Khanna, A. Putterman and J. Song, *A Deterministic Linear Time Algorithm for Minimum
  Spanning Tree*][KhannaPuttermanSong2026], §3.1 and §3.3, pp. 12–18.
-/

public section

namespace Cslib.Query.Certificate

open Finset Multigraph

variable {V E W : Type}

/-- The two actions of an edge in its round (§3.1, p. 13): *find* sends it to the batch of the
block, *project* sends its projection to the child instance of the round. -/
inductive Action where
  /-- Search for a valid projection: the edge joins the batch `B`. -/
  | find
  /-- Project the edge to `(π u, π v)` and pass it to the child instance. -/
  | project
  deriving DecidableEq

/-- An instance of the certificate procedure (§3.1, pp. 12–14): one call of the recursion. -/
structure Instance (V E : Type) where
  /-- The recursion level `d ≥ 1`; the root has level `1`. -/
  level : ℕ+
  /-- The vertex set of the instance. -/
  vertices : Finset V
  /-- The ends of the edges; a child instance has projected ends. -/
  ends : E → Sym2 V
  /-- The edges of the instance, a subset of the root's edges. -/
  edges : Finset E
  /-- The projection record of each edge: for each preceding level, root first, the spokes at its
  ends used to project it. -/
  record : E → List (Finset E)

namespace Instance

/-- The root instance on the vertices `X` and edges `S` of the multigraph `ends`: level `1` and
empty records. -/
@[expose, simps]
def root (X : Finset V) (ends : E → Sym2 V) (S : Finset E) : Instance V E :=
  ⟨1, X, ends, S, fun _ => []⟩

/-- An instance is well formed when its edges have their ends among its vertices, and the record
of each edge has one entry of at most two spokes per preceding level. -/
structure WellFormed (inst : Instance V E) : Prop where
  /-- The ends of the edges are vertices of the instance. -/
  ends_mem : ∀ e ∈ inst.edges, ∀ v ∈ inst.ends e, v ∈ inst.vertices
  /-- The record of an edge has one entry per preceding level. -/
  length_record : ∀ e ∈ inst.edges, (inst.record e).length = (inst.level : ℕ) - 1
  /-- Each entry of a record has at most two spokes. -/
  card_record_le : ∀ e ∈ inst.edges, ∀ P ∈ inst.record e, #P ≤ 2

/-- A root instance is well formed when its edges have their ends among its vertices. -/
theorem wellFormed_root {X : Finset V} {ends : E → Sym2 V} {S : Finset E}
    (h : ∀ e ∈ S, ∀ v ∈ ends e, v ∈ X) : (root X ends S).WellFormed where
  ends_mem := h
  length_record := by simp
  card_record_le := by simp

end Instance

/-! ### Projection records and the admissibility test -/

section Record

variable [LinearOrder W]

/-- The edge `e` is **admissible** for the record `rec` when every spoke in it weighs at most `e`,
that is, when all its projections at preceding levels are valid (p. 13). -/
def Admissible (w : E → W) (rec : List (Finset E)) (e : E) : Prop :=
  ∀ P ∈ rec, ∀ s ∈ P, w s ≤ w e

theorem admissible_iff {w : E → W} {rec : List (Finset E)} {e : E} :
    Admissible w rec e ↔ ∀ P ∈ rec, ∀ s ∈ P, w s ≤ w e := Iff.rfl

/-- A spoke in the record of an admissible edge weighs at most the edge. -/
theorem Admissible.le {w : E → W} {rec : List (Finset E)} {e : E} (h : Admissible w rec e)
    {P : Finset E} (hP : P ∈ rec) {s : E} (hs : s ∈ P) : w s ≤ w e :=
  h P hP s hs

instance (w : E → W) (rec : List (Finset E)) (e : E) : Decidable (Admissible w rec e) :=
  inferInstanceAs (Decidable (∀ P ∈ rec, ∀ s ∈ P, w s ≤ w e))

/-- The index of the first entry of the record `rec` holding a spoke heavier than `e`: the first
invalid projection of `e`, made at level `k + 1` for the index `k`. It is `none` when `e` is
admissible. -/
def firstInvalid (w : E → W) (rec : List (Finset E)) (e : E) : Option ℕ :=
  rec.findIdx? fun P => decide (∃ s ∈ P, w e < w s)

theorem firstInvalid_eq_none_iff {w : E → W} {rec : List (Finset E)} {e : E} :
    firstInvalid w rec e = none ↔ Admissible w rec e := by
  simp [firstInvalid, Admissible, List.findIdx?_eq_none_iff]

theorem firstInvalid_nil (w : E → W) (e : E) : firstInvalid w [] e = none := by
  simp [firstInvalid]

theorem firstInvalid_cons (w : E → W) (P : Finset E) (rec : List (Finset E)) (e : E) :
    firstInvalid w (P :: rec) e =
      if ∃ s ∈ P, w e < w s then some 0 else (firstInvalid w rec e).map (· + 1) := by
  simp [firstInvalid, List.findIdx?_cons]

/-- An edge whose record is extended by one entry: an invalid entry found before the new one is
the first invalid entry of the old record. -/
theorem firstInvalid_of_append_eq_some {w : E → W} {rec : List (Finset E)} {P : Finset E} {e : E}
    {k : ℕ} (h : firstInvalid w (rec ++ [P]) e = some k) (hk : k ≠ rec.length) :
    firstInvalid w rec e = some k := by
  unfold firstInvalid at h ⊢
  rw [List.findIdx?_append] at h
  rcases h' : rec.findIdx? (fun P => decide (∃ s ∈ P, w e < w s)) with _ | j
  · rw [h'] at h
    simp only [Option.none_or, List.findIdx?_singleton] at h
    split at h <;> simp_all
  · rw [h'] at h
    simpa using h

/-- An edge whose extended record has its first invalid entry at the new one is admissible for the
old record. -/
theorem admissible_of_append_eq_some {w : E → W} {rec : List (Finset E)} {P : Finset E} {e : E}
    (h : firstInvalid w (rec ++ [P]) e = some rec.length) : Admissible w rec e := by
  rw [← firstInvalid_eq_none_iff]
  unfold firstInvalid at h ⊢
  rw [List.findIdx?_append] at h
  rcases h' : rec.findIdx? (fun P => decide (∃ s ∈ P, w e < w s)) with _ | j
  · rfl
  · rw [h'] at h
    obtain ⟨hj, -⟩ := List.findIdx?_eq_some_iff_getElem.1 h'
    simp only [Option.some_or, Option.some.injEq] at h
    omega

/-- An edge whose extended record has its first invalid entry at the new one has a spoke heavier
than it in that entry: its projection at the new level is invalid. -/
theorem exists_lt_of_append_eq_some {w : E → W} {rec : List (Finset E)} {P : Finset E} {e : E}
    (h : firstInvalid w (rec ++ [P]) e = some rec.length) : ∃ s ∈ P, w e < w s := by
  unfold firstInvalid at h
  obtain ⟨hlt, hP, -⟩ := List.findIdx?_eq_some_iff_getElem.1 h
  simpa using hP

/-- An admissible edge stays admissible for a prefix of its record. -/
theorem Admissible.of_append {w : E → W} {rec rec' : List (Finset E)} {e : E}
    (h : Admissible w (rec ++ rec') e) : Admissible w rec e :=
  fun P hP => h P (List.mem_append_left _ hP)

/-- Whether every edge of the list weighs at most `e`, one comparison per edge, stopping at the
first heavier edge. -/
@[expose] def allLe (e : E) : List E → FreeM (LEQuery E) Bool
  | [] => pure true
  | s :: l => do if ← LEQuery.ask s e then allLe e l else pure false

/-- **The scan of a projection record** (p. 13): the index of its first invalid entry, scanning
from the root and stopping there. -/
@[expose] noncomputable def findInvalid (e : E) : List (Finset E) → FreeM (LEQuery E) (Option ℕ)
  | [] => pure none
  | P :: rec => do
    if ← allLe e P.toList then
      let k ← findInvalid e rec
      pure (k.map (· + 1))
    else pure (some 0)

/-- **The admissibility test** (p. 13): whether the scan finds no invalid entry. -/
@[expose] noncomputable def admissibilityTest (rec : List (Finset E)) (e : E) :
    FreeM (LEQuery E) Bool := do
  let k ← findInvalid e rec
  pure k.isNone

theorem eval_allLe (w : E → W) (e : E) (l : List E) :
    (allLe e l).eval (LEQuery.keyOracle w) = decide (∀ s ∈ l, w s ≤ w e) := by
  induction l with
  | nil => simp [allLe]
  | cons s l ih =>
    by_cases h : w s ≤ w e <;> simp [allLe, h, ih]

theorem countQueries_allLe_le (o : {ι : Type} → LEQuery E ι → ι) (e : E) (l : List E) :
    (allLe e l).countQueries o ≤ l.length := by
  induction l with
  | nil => simp [allLe]
  | cons s l ih =>
    simp only [allLe, FreeM.countQueries_bind, FreeM.countQueries_lift, List.length_cons]
    split
    · omega
    · simp

private theorem eval_allLe_toList (w : E → W) (e : E) (P : Finset E) :
    (allLe e P.toList).eval (LEQuery.keyOracle w) = !decide (∃ s ∈ P, w e < w s) := by
  rw [eval_allLe, ← decide_not, decide_eq_decide]
  simp

theorem eval_findInvalid (w : E → W) (e : E) (rec : List (Finset E)) :
    (findInvalid e rec).eval (LEQuery.keyOracle w) = firstInvalid w rec e := by
  induction rec with
  | nil => simp [findInvalid, firstInvalid_nil]
  | cons P rec ih =>
    rw [firstInvalid_cons]
    by_cases h : ∃ s ∈ P, w e < w s
    · simp [findInvalid, eval_allLe_toList, h]
    · simp [findInvalid, eval_allLe_toList, h, ih]

theorem eval_admissibilityTest (w : E → W) (rec : List (Finset E)) (e : E) :
    (admissibilityTest rec e).eval (LEQuery.keyOracle w) = decide (Admissible w rec e) := by
  simp only [admissibilityTest, FreeM.eval_bind, FreeM.eval_pure, eval_findInvalid]
  by_cases h : Admissible w rec e
  · simp [firstInvalid_eq_none_iff.2 h, h]
  · rcases h' : firstInvalid w rec e with _ | k
    · exact absurd (firstInvalid_eq_none_iff.1 h') h
    · simp [h]

/-- The scan makes at most two comparisons per entry of at most two spokes. -/
theorem countQueries_findInvalid_le (o : {ι : Type} → LEQuery E ι → ι) (e : E)
    {rec : List (Finset E)} (hrec : ∀ P ∈ rec, #P ≤ 2) :
    (findInvalid e rec).countQueries o ≤ 2 * rec.length := by
  induction rec with
  | nil => simp [findInvalid]
  | cons P rec ih =>
    have hP := (countQueries_allLe_le o e P.toList).trans_eq (length_toList P)
    have h1 := hrec P List.mem_cons_self
    have h2 := ih fun Q hQ => hrec Q (List.mem_cons_of_mem _ hQ)
    simp only [findInvalid, FreeM.countQueries_bind, List.length_cons]
    split <;> simp <;> omega

/-- **The cost of a failed test** (p. 24): when the first invalid entry has index `k`, the scan
makes at most `2 (k + 1)` comparisons, whatever the length of the record. -/
theorem countQueries_findInvalid_le_of_eq_some (w : E → W) (e : E) {rec : List (Finset E)}
    (hrec : ∀ P ∈ rec, #P ≤ 2) {k : ℕ} (hk : firstInvalid w rec e = some k) :
    (findInvalid e rec).countQueries (LEQuery.keyOracle w) ≤ 2 * (k + 1) := by
  induction rec generalizing k with
  | nil => simp [firstInvalid_nil] at hk
  | cons P rec ih =>
    have hP := (countQueries_allLe_le (LEQuery.keyOracle w) e P.toList).trans_eq (length_toList P)
    have h1 := hrec P List.mem_cons_self
    rw [firstInvalid_cons] at hk
    by_cases h : ∃ s ∈ P, w e < w s
    · simp only [h, ↓reduceIte, Option.some.injEq] at hk
      subst hk
      simp only [findInvalid, FreeM.countQueries_bind, eval_allLe_toList]
      simp [h]
      omega
    · simp only [h, ↓reduceIte, Option.map_eq_some_iff] at hk
      obtain ⟨j, hj, rfl⟩ := hk
      have h2 := ih (fun Q hQ => hrec Q (List.mem_cons_of_mem _ hQ)) hj
      simp only [findInvalid, FreeM.countQueries_bind, eval_allLe_toList]
      simp [h]
      omega

/-- The test costs exactly what the scan costs. -/
theorem countQueries_admissibilityTest (o : {ι : Type} → LEQuery E ι → ι)
    (rec : List (Finset E)) (e : E) :
    (admissibilityTest rec e).countQueries o = (findInvalid e rec).countQueries o := by
  simp [admissibilityTest]

end Record

/-! ### Spokes, projections and preferences -/

section Pref

variable [DecidableEq V] [DecidableEq E]

/-- The spokes at the ends of `e`: `{σ(u), σ(v)}` for the ends `u, v` that have one. -/
def spokes (st : State V E) (e : E) : Finset E :=
  (st.ends e).toFinset.biUnion fun x => (st.spoke x).toFinset

theorem mem_spokes {st : State V E} {e s : E} :
    s ∈ spokes st e ↔ ∃ x ∈ st.ends e, st.spoke x = some s := by
  simp [spokes, Sym2.mem_toFinset, eq_comm]

/-- The spokes at the ends `u, v` of `e` are `σ(u)` and `σ(v)`. -/
theorem spokes_eq {st : State V E} {e : E} {u v : V} (h : st.ends e = s(u, v)) :
    spokes st e = (st.spoke u).toFinset ∪ (st.spoke v).toFinset := by
  ext s
  simp only [mem_spokes, h, Sym2.mem_iff, mem_union, Option.mem_toFinset, Option.mem_def]
  constructor
  · rintro ⟨x, rfl | rfl, hx⟩ <;> simp [hx]
  · rintro (hs | hs)
    · exact ⟨u, Or.inl rfl, hs⟩
    · exact ⟨v, Or.inr rfl, hs⟩

/-- An edge has at most two spokes at its ends. -/
theorem card_spokes_le (st : State V E) (e : E) : #(spokes st e) ≤ 2 := by
  obtain ⟨⟨u, v⟩, h⟩ := Quot.exists_rep (st.ends e)
  rw [spokes_eq h.symm]
  refine (card_union_le _ _).trans ?_
  have hu : #(st.spoke u).toFinset ≤ 1 := by cases st.spoke u <;> simp
  have hv : #(st.spoke v).toFinset ≤ 1 := by cases st.spoke v <;> simp
  omega

omit [DecidableEq E] in
/-- Both ends of `e` have spokes and they lead to distinct portals, so that `e` can be projected to
an edge that is not a self-loop. An edge that is not projectable prefers *find* (p. 13). -/
def Projectable (st : State V E) (e : E) : Prop :=
  (∀ x ∈ st.ends e, (st.spoke x).isSome) ∧ ¬(Sym2.map st.proj (st.ends e)).IsDiag

omit [DecidableEq E] in
theorem Projectable.isSome_spoke {st : State V E} {e : E} (h : Projectable st e) {x : V}
    (hx : x ∈ st.ends e) : (st.spoke x).isSome :=
  h.1 x hx

omit [DecidableEq E] in
/-- The projection of a projectable edge is not a self-loop. -/
theorem Projectable.not_isDiag {st : State V E} {e : E} (h : Projectable st e) :
    ¬(Sym2.map st.proj (st.ends e)).IsDiag :=
  h.2

omit [DecidableEq E] in
/-- **The spokes of a projectable edge**: both ends `u, v` have spokes, leading to distinct
portals. -/
theorem Projectable.exists_spokes {st : State V E} {e : E} (h : Projectable st e) {u v : V}
    (huv : st.ends e = s(u, v)) :
    ∃ su sv, st.spoke u = some su ∧ st.spoke v = some sv ∧ st.proj u ≠ st.proj v := by
  obtain ⟨su, hsu⟩ := Option.isSome_iff_exists.1
    (h.isSome_spoke (by rw [huv]; exact Sym2.mem_mk_left u v))
  obtain ⟨sv, hsv⟩ := Option.isSome_iff_exists.1
    (h.isSome_spoke (by rw [huv]; exact Sym2.mem_mk_right u v))
  have hne := h.not_isDiag
  rw [huv, Sym2.map_mk, Sym2.mk_isDiag_iff] at hne
  exact ⟨su, sv, hsu, hsv, hne⟩

variable [LinearOrder W]

/-- The edge `e` **prefers find** at the state `st` (p. 13 and p. 17): it is not projectable, or
the forest edges no heavier than one of its spokes, `F≤p(e)`, join its ends. -/
def PrefersFind (w : E → W) (st : State V E) (e : E) : Prop :=
  ¬Projectable st e ∨ ∀ a b, st.ends e = s(a, b) →
    Joins st.ends {f | f ∈ st.forest ∧ ∃ s ∈ spokes st e, w f ≤ w s} a b

/-- An edge that is not projectable prefers *find* (p. 13). -/
theorem prefersFind_of_not_projectable {w : E → W} {st : State V E} {e : E}
    (h : ¬Projectable st e) : PrefersFind w st e :=
  Or.inl h

/-- A projectable edge whose ends the forest does not join prefers *project* (p. 13): no
threshold `p(e)` can make `F≤p(e)` join them. -/
theorem not_prefersFind_of_not_joins {w : E → W} {st : State V E} {e : E} (hp : Projectable st e)
    (hj : ¬∀ a b, st.ends e = s(a, b) → Joins st.ends (st.forest : Set E) a b) :
    ¬PrefersFind w st e := by
  rintro (h | h)
  · exact h hp
  · exact hj fun a b hab => (h a b hab).mono (by rintro f ⟨hf, -⟩; exact hf)

/-- **The preference rule with both spokes present** (p. 13): for an edge with ends `u, v` and
spokes `σ(u) = su`, `σ(v) = sv`, *find* is preferred exactly when `π u = π v` or `F≤p(e)` joins
`u` and `v`, where `p(e) = max (w su) (w sv)`. -/
theorem prefersFind_iff {w : E → W} {st : State V E} {e : E} {u v : V}
    (h : st.ends e = s(u, v)) {su sv : E} (hu : st.spoke u = some su)
    (hv : st.spoke v = some sv) :
    PrefersFind w st e ↔ st.proj u = st.proj v ∨
      Joins st.ends {f | f ∈ st.forest ∧ w f ≤ max (w su) (w sv)} u v := by
  have hproj : Projectable st e ↔ st.proj u ≠ st.proj v := by
    unfold Projectable
    rw [h, Sym2.map_mk, Sym2.mk_isDiag_iff]
    constructor
    · exact fun h => h.2
    · intro hne
      refine ⟨fun x hx => ?_, hne⟩
      rcases Sym2.mem_iff.1 hx with rfl | rfl
      · simp [hu]
      · simp [hv]
  have hset : {f | f ∈ st.forest ∧ ∃ s ∈ spokes st e, w f ≤ w s} =
      {f | f ∈ st.forest ∧ w f ≤ max (w su) (w sv)} := by
    ext f
    simp only [Set.mem_ofPred_eq, spokes_eq h, hu, hv, Option.toFinset_some, mem_union,
      mem_singleton, le_max_iff]
    constructor
    · rintro ⟨hf, s, rfl | rfl, hs⟩
      · exact ⟨hf, Or.inl hs⟩
      · exact ⟨hf, Or.inr hs⟩
    · rintro ⟨hf, hs | hs⟩
      · exact ⟨hf, su, Or.inl rfl, hs⟩
      · exact ⟨hf, sv, Or.inr rfl, hs⟩
  unfold PrefersFind
  rw [hproj, hset, not_not]
  refine or_congr Iff.rfl ⟨fun H => H u v h, fun H a b hab => ?_⟩
  rw [h] at hab
  rcases Sym2.eq_iff.1 hab.symm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact H
  · exact H.symm

open scoped Classical in
/-- The **true preferred action** of `e` at the state `st` (p. 13 and p. 17). -/
noncomputable def pref (w : E → W) (st : State V E) (e : E) : Action :=
  if PrefersFind w st e then .find else .project

theorem pref_eq_find_iff {w : E → W} {st : State V E} {e : E} :
    pref w st e = .find ↔ PrefersFind w st e := by
  unfold pref
  split <;> simp_all

theorem pref_eq_project_iff {w : E → W} {st : State V E} {e : E} :
    pref w st e = .project ↔ ¬PrefersFind w st e := by
  unfold pref
  split <;> simp_all

/-- The preferences at a state depend only on its ends, spokes and forest, not on its vertices
or portals. -/
theorem pref_congr {w : E → W} {st st' : State V E} (he : st.ends = st'.ends)
    (hs : st.spoke = st'.spoke) (hf : st.forest = st'.forest) : pref w st = pref w st' := by
  obtain ⟨X, ends, P, σ, F⟩ := st
  obtain ⟨X', ends', P', σ', F'⟩ := st'
  simp only at he hs hf
  subst he hs hf
  have hproj : State.proj ⟨X, ends, P, σ, F⟩ = State.proj ⟨X', ends, P', σ, F⟩ := by
    funext v
    rcases h : σ v with _ | s
    · rw [State.proj_of_spoke_eq_none (st := ⟨X, ends, P, σ, F⟩) h,
        State.proj_of_spoke_eq_none (st := ⟨X', ends, P', σ, F⟩) h]
    · rw [State.proj_of_spoke_eq_some (st := ⟨X, ends, P, σ, F⟩) h,
        State.proj_of_spoke_eq_some (st := ⟨X', ends, P', σ, F⟩) h]
  funext e
  have hpf : PrefersFind w ⟨X, ends, P, σ, F⟩ e ↔ PrefersFind w ⟨X', ends, P', σ, F⟩ e := by
    unfold PrefersFind Projectable spokes
    rw [hproj]
  by_cases h : PrefersFind w ⟨X, ends, P, σ, F⟩ e
  · rw [pref_eq_find_iff.2 h, pref_eq_find_iff.2 (hpf.1 h)]
  · rw [pref_eq_project_iff.2 h, pref_eq_project_iff.2 (mt hpf.2 h)]

omit [LinearOrder W] in
open scoped Classical in
/-- The action used by the algorithm: the estimate `a`, forced to *find* on edges that are not
projectable (p. 13: "its estimate is always find when a spoke is missing or both spokes lead to
the same portal"). -/
noncomputable def maskAction (st : State V E) (a : E → Action) (e : E) : Action :=
  if Projectable st e then a e else .find

omit [LinearOrder W] [DecidableEq E] in
theorem projectable_of_maskAction_eq_project {st : State V E} {a : E → Action} {e : E}
    (h : maskAction st a e = .project) : Projectable st e := by
  unfold maskAction at h
  split at h
  · assumption
  · cases h

/-- Masking never introduces an estimation error: where the action used differs from the true
preference, so does the raw estimate. -/
theorem ne_of_maskAction_ne {w : E → W} {st : State V E} {a : E → Action} {e : E}
    (h : maskAction st a e ≠ pref w st e) : a e ≠ pref w st e := by
  unfold maskAction at h
  split at h
  · exact h
  · exact absurd (pref_eq_find_iff.2 (Or.inl ‹_›)).symm h

omit [LinearOrder W] in
/-- **The child instance** of a round (Algorithm 1, lines 12–15): the portals as vertices, the
projected ends `s(π u, π v)`, the projected edges `S`, and records extended by the spokes at the
ends. -/
@[expose, simps]
def Instance.child (inst : Instance V E) (st : State V E) (S : Finset E) : Instance V E where
  level := inst.level + 1
  vertices := st.portals
  ends e := Sym2.map st.proj (st.ends e)
  edges := S
  record e := inst.record e ++ [spokes st e]

end Pref

/-! ### Parameters and the generic parts of Algorithm 1 -/

/-- The parameter `t = γ d³` of level `d` (p. 13): the number of blocks of a call and of rounds
per block. -/
@[expose] def levelT (γ d : ℕ) : ℕ := γ * d ^ 3

/-- The parameter `r = 8 t³` of level `d` (p. 13). By Lemma 3.2 (p. 15), a batch selects at most
`2n / r` new portals and declares at most `r²` edges per vertex. -/
@[expose] def levelR (γ d : ℕ) : ℕ := 8 * levelT γ d ^ 3

/-- The generic parts of Algorithm 1. -/
structure Config (V E : Type) where
  /-- The constant `γ` of the parameters `t = γ d³` and `r = 8 t³`. -/
  γ : ℕ
  /-- **The schedule** (line 5): the round, among the `t²` rounds, in which each edge acts. It is a
  function of the instance alone, not of the weights, so it costs no comparisons; §3.4 chooses it
  by an exhaustive search (Lemma 3.11, p. 21). -/
  sched : (inst : Instance V E) → E → Fin (levelT γ inst.level ^ 2)
  /-- **The preference estimator** (line 10): a comparison program that, from the instance, the
  state at the start of a round and the edges acting in it, estimates their preferred actions
  (§3.5, p. 22). The algorithm forces the estimate to *find* on edges that are not projectable. -/
  est : Instance V E → State V E → Finset E → FreeM (LEQuery E) (E → Action)
  /-- **The exact minimum spanning forest subroutine** (lines 19 and 21), for the given ends. -/
  msfSub : (E → Sym2 V) → Finset E → FreeM (LEQuery E) (Finset E)

/-! ### Bad rounds -/

/-- **Bad rounds** (Definition 3.4, p. 17). Among `t²` rounds in `t` blocks of `t`, for the
sequence `a` of preferred actions of an edge, round `i` is bad when it is the last round of its
block with a *project* preference, or when its preference is *find* and its block is the last one
containing a *find* preference. -/
@[expose] def BadRound (t : ℕ) (a : ℕ → Action) (i : ℕ) : Prop :=
  (a i = .project ∧ ∀ j, i < j → j / t = i / t → a j = .find) ∨
    (a i = .find ∧ ∀ j < t ^ 2, i / t < j / t → a j = .project)

open scoped Classical in
/-- **At most `2t` bad rounds** (Definition 3.4, p. 17): one *project* round per block, and the
*find* rounds of a single block. -/
theorem card_badRound_le (t : ℕ) (a : ℕ → Action) :
    #{i ∈ range (t ^ 2) | BadRound t a i} ≤ 2 * t := by
  set Bp := {i ∈ range (t ^ 2) | a i = .project ∧ ∀ j, i < j → j / t = i / t → a j = .find}
  set Bf := {i ∈ range (t ^ 2) | a i = .find ∧ ∀ j < t ^ 2, i / t < j / t → a j = .project}
  have hsub : {i ∈ range (t ^ 2) | BadRound t a i} ⊆ Bp ∪ Bf := by
    intro i hi
    rw [mem_filter] at hi
    unfold BadRound at hi
    rcases hi.2 with h | h
    · exact mem_union_left _ (mem_filter.2 ⟨hi.1, h⟩)
    · exact mem_union_right _ (mem_filter.2 ⟨hi.1, h⟩)
  have hdiv : ∀ i ∈ range (t ^ 2), i / t < t := fun i hi => by
    rw [mem_range] at hi
    exact Nat.div_lt_of_lt_mul (by rw [sq] at hi; exact hi)
  -- one *project* round per block
  have hp : #Bp ≤ t := by
    have : Set.InjOn (· / t) (Bp : Set ℕ) := by
      intro i hi i' hi' hii'
      simp only [coe_filter, Set.mem_ofPred_eq, Bp] at hi hi'
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · have := hi.2.2 i' h hii'.symm
        rw [hi'.2.1] at this
        cases this
      · have := hi'.2.2 i h hii'
        rw [hi.2.1] at this
        cases this
    calc #Bp ≤ #(range t) := card_le_card_of_injOn (· / t)
          (fun i hi => mem_coe.2 (mem_range.2 (hdiv i (mem_filter.1 hi).1))) this
      _ = t := card_range t
  -- the *find* rounds lie in one block
  have hf : #Bf ≤ t := by
    rcases Bf.eq_empty_or_nonempty with h | ⟨i₀, hi₀⟩
    · simp [h]
    · have hblock : Bf ⊆ Ico (i₀ / t * t) (i₀ / t * t + t) := by
        intro i hi
        have hi' := hi
        simp only [mem_filter, Bf] at hi hi₀
        have heq : i / t = i₀ / t := by
          by_contra hne
          rcases lt_or_gt_of_ne hne with h | h
          · have := hi.2.2 i₀ (mem_range.1 hi₀.1) h
            rw [hi₀.2.1] at this
            cases this
          · have := hi₀.2.2 i (mem_range.1 hi.1) h
            rw [hi.2.1] at this
            cases this
        rw [mem_Ico, ← heq]
        exact ⟨Nat.div_mul_le_self i t, by
          have := Nat.lt_div_mul_add (a := i) (b := t)
          rcases Nat.eq_zero_or_pos t with ht | ht
          · subst ht
            simp at hi
          · exact Nat.lt_div_mul_add ht⟩
      calc #Bf ≤ #(Ico (i₀ / t * t) (i₀ / t * t + t)) := card_le_card hblock
        _ = t := by simp
  calc #{i ∈ range (t ^ 2) | BadRound t a i} ≤ #(Bp ∪ Bf) := card_le_card hsub
    _ ≤ #Bp + #Bf := card_union_le _ _
    _ ≤ 2 * t := by omega

end Cslib.Query.Certificate
