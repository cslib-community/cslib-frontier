/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Combinatorics.Multidigraph.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.List.Chain
import Mathlib.Data.Fintype.Card

/-!
# Directed paths, cuts, and separators in multidigraphs

Pure graph-theoretic notions for Menger's theorem in directed multigraphs `src tgt : E → V` (where
parallel arcs and self-loops are permitted):

* `Cslib.Multidigraph.IsDipath`: simple directed `s`–`t` paths as lists of arcs `q : List E`
  whose visited vertices `s :: q.map tgt` are duplicate-free, with conversions to and from vertex
  paths (`Cslib.Multidigraph.IsDipath.isChain_toDigraph`,
  `Cslib.Multidigraph.isDipath_pmap_zip_tail`).
* `Cslib.Multidigraph.IsArcCut`, `Cslib.Multidigraph.outArcs`,
  `Cslib.Multidigraph.IsVertexCut`, `Cslib.Multidigraph.IsSeparator`: arc cuts, outgoing arc cuts
  `δ^out(S)`, single-terminal vertex cuts, and `A`–`B` vertex separators.
* Cut/separator certificates (`isArcCut_outArcs`, `isSeparator_of_forall_src_tgt`,
  `isVertexCut_of_forall_src_tgt`) and weak duality for arc-disjoint, internally disjoint, and
  vertex-disjoint paths.

## Main definitions

* `Cslib.Multidigraph.IsDipath`, `Cslib.Multidigraph.InternallyDisjoint`: simple directed paths and
  internal vertex-disjointness.
* `Cslib.Multidigraph.IsArcCut`, `Cslib.Multidigraph.outArcs`, `Cslib.Multidigraph.IsVertexCut`,
  `Cslib.Multidigraph.IsSeparator`: directed arc and vertex cuts / separators.

## Main results

* `Cslib.Multidigraph.IsDipath.nodup`, `Cslib.Multidigraph.IsDipath.zip_tail_vertices`,
  `Cslib.Multidigraph.IsDipath.isChain_toDigraph`,
  `Cslib.Multidigraph.IsDipath.reflTransGen_toDigraph`,
  `Cslib.Multidigraph.isDipath_pmap_zip_tail`,
  `Cslib.Multidigraph.exists_isDipath_iff_reflTransGen`: arc duplicate-freeness, correspondence
  between arc dipaths and vertex chains, and equivalence with reachability in `toDigraph`.
* `Cslib.Multidigraph.isArcCut_outArcs`, `Cslib.Multidigraph.isSeparator_of_forall_src_tgt`,
  `Cslib.Multidigraph.isVertexCut_of_forall_src_tgt`: certificates for arc cuts, separators, and
  vertex cuts.
* `Cslib.Multidigraph.card_le_card_of_disjoint_of_isArcCut`,
  `Cslib.Multidigraph.card_le_card_of_internallyDisjoint_of_isVertexCut`,
  `Cslib.Multidigraph.card_le_card_of_disjoint_of_isSeparator`: weak duality.

## References

* [K. Menger, *Zur allgemeinen Kurventheorie*][Menger1927]
* [A. Schrijver, *A Course in Combinatorial Optimization*][Schrijver2017], §4.1, Corollary 4.1b
-/

public section

namespace Cslib.Multidigraph

variable {V E : Type*} (src tgt : E → V)

/-- `q` is a simple directed `s`–`t` path of arcs in the multidigraph `src tgt : E → V`: each arc
ends where the next begins, the path starts at `s` and ends at `t`, and the visited vertex list
`s :: q.map tgt` is duplicate-free. -/
@[expose] def IsDipath (s t : V) (q : List E) : Prop :=
  q.IsChain (fun a b => tgt a = src b) ∧
    (s :: q.map tgt).Nodup ∧
    (∀ e ∈ q.head?, src e = s) ∧
    (q = [] → s = t) ∧
    ∀ e ∈ q.getLast?, tgt e = t

instance instDecidableIsDipath [DecidableEq V] (s t : V) (q : List E) :
    Decidable (IsDipath src tgt s t q) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

section DipathVertices

variable {src tgt}

/-- The visited vertex list `s :: q.map tgt` of an `s`–`t` dipath ends at `t`. -/
theorem IsDipath.getLast?_vertices {s t : V} {q : List E} (hq : IsDipath src tgt s t q) :
    (s :: q.map tgt).getLast? = some t := by
  rcases q with _ | ⟨e, qs⟩
  · simp [hq.2.2.2.1 rfl]
  · rw [List.map_cons, List.getLast?_cons_cons, ← List.map_cons, List.getLast?_map]
    cases hlast : (e :: qs).getLast? with
    | none => simp at hlast
    | some el => exact congrArg some (hq.2.2.2.2 el hlast)

private theorem zip_tail_vertices_aux :
    ∀ {q : List E} {s : V}, q.IsChain (fun a b => tgt a = src b) →
      (∀ e ∈ q.head?, src e = s) →
      (s :: q.map tgt).zip (s :: q.map tgt).tail = q.map fun e => (src e, tgt e)
  | [], _, _, _ => rfl
  | [e], s, _, hhd => by
    have hs := hhd e rfl
    simp [hs]
  | e₁ :: e₂ :: rest, s, hchain, hhd => by
    rw [List.isChain_cons_cons] at hchain
    have hs := hhd e₁ rfl
    have ih := zip_tail_vertices_aux (q := e₂ :: rest) (s := tgt e₁) hchain.2
      fun e he => (Option.some.inj he).symm ▸ hchain.1.symm
    simpa [hs] using ih

/-- Consecutive vertex pairs of `s :: q.map tgt` along a dipath `q` are `(src e, tgt e)`. -/
theorem IsDipath.zip_tail_vertices {s t : V} {q : List E} (hq : IsDipath src tgt s t q) :
    (s :: q.map tgt).zip (s :: q.map tgt).tail = q.map fun e => (src e, tgt e) :=
  zip_tail_vertices_aux hq.1 hq.2.2.1

/-- The visited vertex list `s :: q.map tgt` of a multidigraph dipath forms a chain in
`toDigraph src tgt`. -/
theorem IsDipath.isChain_toDigraph {s t : V} {q : List E} (hq : IsDipath src tgt s t q) :
    (s :: q.map tgt).IsChain (toDigraph src tgt).Adj := by
  have hzip := hq.zip_tail_vertices
  have hall : ∀ p ∈ (s :: q.map tgt).zip (s :: q.map tgt).tail, (toDigraph src tgt).Adj p.1 p.2 :=
    fun p hp => by
      rw [hzip, List.mem_map] at hp
      obtain ⟨e, _, rfl⟩ := hp
      exact ⟨e, rfl, rfl⟩
  clear hq hzip
  generalize s :: q.map tgt = vs at hall
  induction vs with
  | nil => exact List.isChain_nil
  | cons x xs ih =>
    cases xs with
    | nil => exact List.isChain_singleton x
    | cons y ys =>
      exact List.isChain_cons_cons.mpr ⟨hall (x, y) List.mem_cons_self,
        ih fun p hp => hall p (List.mem_cons_of_mem (x, y) hp)⟩

/-- Every simple directed path `IsDipath src tgt s t q` uses each arc at most once (`q.Nodup`),
because its visited target vertices `q.map tgt` are duplicate-free. -/
theorem IsDipath.nodup {s t : V} {q : List E} (hq : IsDipath src tgt s t q) : q.Nodup :=
  (List.nodup_cons.mp hq.2.1).2.of_map tgt

private theorem reflTransGen_of_isChain_adj {R : V → V → Prop} :
    ∀ {l : List V} {u v : V}, l.IsChain R → l.head? = some u → l.getLast? = some v →
      Relation.ReflTransGen R u v
  | [], _, _, _, hu, _ => by simp at hu
  | [x], _, _, _, hu, hv => by
    obtain rfl := Option.some.inj hu
    obtain rfl := Option.some.inj hv
    exact .refl
  | x :: y :: rest, u, v, hc, hu, hv => by
    obtain rfl : x = u := Option.some.inj hu
    rw [List.isChain_cons_cons] at hc
    exact .head hc.1 (reflTransGen_of_isChain_adj hc.2 rfl (by simpa using hv))

/-- Every multidigraph dipath from `s` to `t` witnesses reachability in `toDigraph src tgt`. -/
theorem IsDipath.reflTransGen_toDigraph {s t : V} {q : List E} (hq : IsDipath src tgt s t q) :
    Relation.ReflTransGen (toDigraph src tgt).Adj s t :=
  reflTransGen_of_isChain_adj hq.isChain_toDigraph rfl hq.getLast?_vertices

private theorem isDipath_tail_of_mem_map_tgt {b v a : V} :
    ∀ {q : List E}, IsDipath src tgt b v q → a ∈ q.map tgt → ∃ q', IsDipath src tgt a v q'
  | [], _, hmem => by simp at hmem
  | e :: qs, hq, hmem => by
    simp only [List.map_cons, List.mem_cons] at hmem
    have hnd_cons : (b :: tgt e :: qs.map tgt).Nodup := hq.2.1
    have hnd_tail : (tgt e :: qs.map tgt).Nodup := (List.nodup_cons.mp hnd_cons).2
    have hchain_qs : qs.IsChain (fun x y => tgt x = src y) := by
      rcases qs with _ | ⟨e', rest⟩
      · exact List.isChain_nil
      · exact (List.isChain_cons_cons.mp hq.1).2
    have hhd_qs : ∀ x ∈ qs.head?, src x = tgt e := by
      rcases qs with _ | ⟨e', rest⟩
      · intro _ h; simp at h
      · intro x hx
        obtain rfl : e' = x := Option.some.inj hx
        exact (List.isChain_cons_cons.mp hq.1).1.symm
    have hnil_qs : qs = [] → tgt e = v := fun hnil => by
      subst hnil
      exact hq.2.2.2.2 e rfl
    have hlast_qs : ∀ x ∈ qs.getLast?, tgt x = v := by
      rcases qs with _ | ⟨e', rest⟩
      · intro _ h; simp at h
      · intro x hx
        exact hq.2.2.2.2 x (by simpa using hx)
    have hq_tail : IsDipath src tgt (tgt e) v qs :=
      ⟨hchain_qs, hnd_tail, hhd_qs, hnil_qs, hlast_qs⟩
    rcases hmem with rfl | hmem_qs
    · exact ⟨qs, hq_tail⟩
    · exact isDipath_tail_of_mem_map_tgt hq_tail hmem_qs

/-- A simple directed `s`–`t` path of arcs exists in `(src, tgt)` if and only if `t` is reachable
from `s` in `toDigraph src tgt` (loop removal shortcuts any directed walk to a simple dipath). -/
theorem exists_isDipath_iff_reflTransGen {s t : V} :
    (∃ q, IsDipath src tgt s t q) ↔ Relation.ReflTransGen (toDigraph src tgt).Adj s t := by
  classical
  refine ⟨fun ⟨q, hq⟩ => hq.reflTransGen_toDigraph, fun h => ?_⟩
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    exact ⟨[], List.isChain_nil, List.nodup_singleton _, fun _ h => by simp at h,
      fun _ => rfl, fun _ h => by simp at h⟩
  | @head a b hab _ ih =>
    obtain ⟨e, hsrc, htgt⟩ := hab
    obtain ⟨q, hq⟩ := ih
    by_cases hab_eq : a = b
    · subst hab_eq
      exact ⟨q, hq⟩
    · by_cases hmem : a ∈ q.map tgt
      · exact isDipath_tail_of_mem_map_tgt hq hmem
      · refine ⟨e :: q, ?_, ?_, ?_, by simp, ?_⟩
        · rcases q with _ | ⟨e', qs⟩
          · exact List.isChain_singleton e
          · exact List.isChain_cons_cons.mpr ⟨htgt.trans (hq.2.2.1 e' rfl).symm, hq.1⟩
        · rw [List.map_cons, htgt]
          exact List.nodup_cons.mpr ⟨by simp [hab_eq, hmem], hq.2.1⟩
        · intro x hx
          obtain rfl : e = x := Option.some.inj hx
          exact hsrc
        · rcases q with _ | ⟨e', qs⟩
          · intro x hx
            obtain rfl : e = x := Option.some.inj hx
            exact htgt.trans (hq.2.2.2.1 rfl)
          · intro x hx
            exact hq.2.2.2.2 x (by simpa using hx)

end DipathVertices

private theorem isDipath_pmap_zip_tail_aux {S : V × V → Prop}
    (f : ∀ e, S e → E) (hf : ∀ e (he : S e), src (f e he) = e.1 ∧ tgt (f e he) = e.2) :
    ∀ {p : List V}, p.Nodup →
      ∀ {s t : V}, p.head? = some s → p.getLast? = some t →
      ∀ (hS : ∀ e ∈ p.zip p.tail, S e),
      let q := (p.zip p.tail).pmap f hS
      q.IsChain (fun a b => tgt a = src b) ∧
      (s :: q.map tgt) = p ∧
      (∀ e ∈ q.head?, src e = s) ∧
      (q = [] → s = t) ∧
      (∀ e ∈ q.getLast?, tgt e = t)
  | [], _, _, _, hs, _, _ => by simp at hs
  | [x], _, s, t, hs, ht, _ => by
    obtain rfl : s = x := (Option.some.inj hs).symm
    obtain rfl : t = s := (Option.some.inj ht).symm
    exact ⟨List.isChain_nil, rfl, (fun _ h => by nomatch h), (fun _ => rfl),
      (fun _ h => by nomatch h)⟩
  | x :: y :: rest', hp, s, t, hs, ht, hS => by
    obtain rfl : s = x := (Option.some.inj hs).symm
    have he0_eq := hf (s, y) (hS (s, y) (by simp))
    rcases rest' with _ | ⟨z, zs⟩
    · obtain rfl : t = y := (Option.some.inj ht).symm
      refine ⟨List.isChain_singleton _, by simp [he0_eq.2], fun e he => ?_, by simp, fun e he => ?_⟩
      · cases show some (f (s, t) _) = some e from he; exact he0_eq.1
      · cases show some (f (s, t) _) = some e from he; exact he0_eq.2
    · obtain ⟨hchain', hmap', hhd', _, hlt'⟩ := isDipath_pmap_zip_tail_aux f hf
        (List.nodup_cons.mp hp).2 rfl (by simpa using ht)
        fun e he => hS e (List.mem_cons_of_mem (s, y) he)
      refine ⟨List.isChain_cons_cons.mpr ⟨he0_eq.2.trans
          (hhd' (f (y, z) _) rfl).symm, hchain'⟩,
        ?_, fun e he => ?_, by simp, hlt'⟩
      · simpa [List.pmap, he0_eq.2] using congrArg (s :: ·) hmap'
      · cases show some (f (s, y) _) = some e from he; exact he0_eq.1

/-- Lifting a duplicate-free vertex list `p` from `s` to `t` along arc witnesses `f` on
`p.zip p.tail` produces a multidigraph dipath whose visited vertices are `p`. -/
theorem isDipath_pmap_zip_tail {S : V × V → Prop}
    (f : ∀ e, S e → E) (hf : ∀ e (he : S e), src (f e he) = e.1 ∧ tgt (f e he) = e.2)
    {p : List V} (hnd : p.Nodup) {s t : V} (hs : p.head? = some s) (ht : p.getLast? = some t)
    (hS : ∀ e ∈ p.zip p.tail, S e) :
    let q := (p.zip p.tail).pmap f hS
    IsDipath src tgt s t q ∧ s :: q.map tgt = p ∧
      q.map (fun e => (src e, tgt e)) = p.zip p.tail := by
  obtain ⟨hc, hm, hhd, hnil, hlt⟩ := isDipath_pmap_zip_tail_aux src tgt f hf hnd hs ht hS
  refine ⟨⟨hc, hm.symm ▸ hnd, hhd, hnil, hlt⟩, hm, ?_⟩
  rw [List.map_pmap]
  have hid : ∀ e (he : S e), (src (f e he), tgt (f e he)) = e := fun e he =>
    Prod.ext (hf e he).1 (hf e he).2
  simp only [hid, List.pmap_eq_map, List.map_id']

/-! ### Arc cuts, vertex cuts, separators, and weak duality -/

/-- `C` is an `s`–`t` arc cut in the multidigraph `src tgt`: every simple directed `s`–`t` path
uses an arc of `C`. -/
@[expose] def IsArcCut (s t : V) (C : Finset E) : Prop :=
  ∀ q, IsDipath src tgt s t q → ∃ e ∈ q, e ∈ C

/-- The arcs of the multidigraph `src tgt` leaving a vertex set `S` (`δ^out(S)`). -/
@[expose] def outArcs [Fintype E] [DecidableEq V] (S : Finset V) : Finset E :=
  Finset.univ.filter fun e => src e ∈ S ∧ tgt e ∉ S

theorem mem_outArcs [Fintype E] [DecidableEq V] {S : Finset V} {e : E} :
    e ∈ outArcs src tgt S ↔ src e ∈ S ∧ tgt e ∉ S := by
  simp [outArcs]

private theorem exists_boundary_mem_arcList {S : V → Prop} :
    ∀ {q : List E} {s t : V}, q.IsChain (fun a b => tgt a = src b) →
      (∀ e ∈ q.head?, src e = s) → (q = [] → s = t) → (∀ e ∈ q.getLast?, tgt e = t) →
      S s → ¬ S t → ∃ e ∈ q, S (src e) ∧ ¬ S (tgt e)
  | [], s, t, _, _, hnil, _, hSs, hSt => absurd (hnil rfl ▸ hSs) hSt
  | [e], s, t, _, hhd, _, hlt, hSs, hSt => by
    have hs := hhd e (by simp)
    have ht := hlt e (by simp)
    exact ⟨e, List.mem_cons_self, hs ▸ hSs, ht ▸ hSt⟩
  | e₁ :: e₂ :: rest, s, t, hchain, hhd, _, hlt, hSs, hSt => by
    rw [List.isChain_cons_cons] at hchain
    have hs : src e₁ = s := hhd e₁ (by simp)
    by_cases hy : S (tgt e₁)
    · obtain ⟨e, he, hbd⟩ := exists_boundary_mem_arcList (q := e₂ :: rest) (s := tgt e₁) (t := t)
        hchain.2 (fun e h => (Option.some.inj (List.head?_cons ▸ h)).symm ▸ hchain.1.symm)
        (fun h => by simp at h) (fun x hx => hlt x (by simpa using hx)) hy hSt
      exact ⟨e, List.mem_cons_of_mem e₁ he, hbd⟩
    · exact ⟨e₁, List.mem_cons_self, hs ▸ hSs, hy⟩

/-- `outArcs src tgt S` is an `s`–`t` arc cut whenever `s ∈ S` and `t ∉ S`. -/
theorem isArcCut_outArcs [Fintype E] [DecidableEq V] {s t : V} {S : Finset V}
    (hs : s ∈ S) (ht : t ∉ S) : IsArcCut src tgt s t (outArcs src tgt S) := by
  rintro q ⟨hchain, _, hhd, hnil, hlt⟩
  obtain ⟨e, he, heS, heS'⟩ :=
    exists_boundary_mem_arcList src tgt hchain hhd hnil hlt hs ht
  exact ⟨e, he, (mem_outArcs src tgt).mpr ⟨heS, heS'⟩⟩

/-- **Weak duality for arc-disjoint paths in a multidigraph**: `k` pairwise arc-disjoint simple
`s`–`t` paths require at least `k` arcs in every `s`–`t` arc cut. -/
theorem card_le_card_of_disjoint_of_isArcCut {s t : V} {k : ℕ} {Q : Fin k → List E}
    (hQ : ∀ i, IsDipath src tgt s t (Q i))
    (hdisj : Pairwise fun i j => (Q i).Disjoint (Q j))
    {C : Finset E} (hC : IsArcCut src tgt s t C) : k ≤ C.card := by
  choose e he heC using fun i => hC (Q i) (hQ i)
  have hinj : Function.Injective fun i => (⟨e i, heC i⟩ : C) := by
    intro i j hij
    by_contra hne
    have heq : e i = e j := congrArg Subtype.val hij
    exact hdisj hne (he i) (heq ▸ he j)
  simpa using Fintype.card_le_of_injective _ hinj

omit src in
/-- The arc lists `Q i` are pairwise internally vertex-disjoint with respect to `s` and `t`: two
distinct paths share no visited vertex in `s :: (Q i).map tgt` other than `s` and `t`. -/
@[expose] def InternallyDisjoint {ι : Type*} (s t : V) (Q : ι → List E) : Prop :=
  Pairwise fun i j => ∀ v ∈ s :: (Q i).map tgt, v ∈ s :: (Q j).map tgt → v = s ∨ v = t

/-- `Y` separates `A` from `B` in `src tgt`: every simple directed `A`–`B` path visits a vertex of
`Y`. -/
@[expose] def IsSeparator (A B Y : Set V) : Prop :=
  ∀ ⦃a⦄, a ∈ A → ∀ ⦃b⦄, b ∈ B → ∀ q, IsDipath src tgt a b q → ∃ v ∈ a :: q.map tgt, v ∈ Y

/-- `T` is an `s`–`t` vertex cut in `src tgt`: it avoids `s` and `t`, and every simple directed
`s`–`t` path visits a vertex of `T`. -/
@[expose] def IsVertexCut (s t : V) (T : Finset V) : Prop :=
  s ∉ T ∧ t ∉ T ∧ ∀ q, IsDipath src tgt s t q → ∃ v ∈ s :: q.map tgt, v ∈ T

theorem isVertexCut_iff_isSeparator {s t : V} {T : Finset V} :
    IsVertexCut src tgt s t T ↔ s ∉ T ∧ t ∉ T ∧ IsSeparator src tgt {s} {t} ↑T := by
  refine ⟨fun ⟨hs, ht, h⟩ => ⟨hs, ht, ?_⟩, fun ⟨hs, ht, h⟩ => ⟨hs, ht, ?_⟩⟩
  · rintro _ rfl _ rfl q hq
    exact h q hq
  · intro q hq
    exact h (Set.mem_singleton s) (Set.mem_singleton t) q hq

/-- **Closed-set certificate for multidigraph separators**: if `S` holds on `A \ Y`, fails on
`B \ Y`, and every arc leaving `S` enters `Y`, then `Y` separates `A` from `B`. -/
theorem isSeparator_of_forall_src_tgt {A B Y : Set V} (S : V → Prop)
    (hstep : ∀ e, S (src e) → tgt e ∉ Y → S (tgt e))
    (hA : ∀ a ∈ A, a ∉ Y → S a) (hB : ∀ b ∈ B, b ∉ Y → ¬ S b) :
    IsSeparator src tgt A B Y := by
  intro a ha b hb q hq
  by_contra hno
  push Not at hno
  have hSa : S a := hA a ha (hno a List.mem_cons_self)
  have hSb : ¬ S b := hB b hb (hno b (List.mem_of_getLast? hq.getLast?_vertices))
  obtain ⟨e, he, heS, heS'⟩ :=
    exists_boundary_mem_arcList src tgt hq.1 hq.2.2.1 hq.2.2.2.1 hq.2.2.2.2 hSa hSb
  exact heS' (hstep e heS (hno (tgt e) (List.mem_cons_of_mem a (List.mem_map_of_mem he))))

/-- Closed-set certificate for a multidigraph vertex cut. -/
theorem isVertexCut_of_forall_src_tgt {s t : V} {S T : Finset V} (hs : s ∈ S) (ht : t ∉ S)
    (hsT : s ∉ T) (htT : t ∉ T) (hST : ∀ e, src e ∈ S → tgt e ∉ S → tgt e ∈ T) :
    IsVertexCut src tgt s t T := by
  refine (isVertexCut_iff_isSeparator src tgt).mpr
    ⟨hsT, htT, isSeparator_of_forall_src_tgt src tgt (· ∈ S) ?_ ?_ ?_⟩
  · intro e hu hv
    by_contra hvS
    exact hv (Finset.mem_coe.mpr (hST e hu hvS))
  · rintro _ rfl _; exact hs
  · rintro _ rfl _; exact ht

/-- **Weak duality for internally disjoint paths in a multidigraph**: `k` pairwise internally
disjoint simple `s`–`t` paths require at least `k` vertices in every `s`–`t` vertex cut. -/
theorem card_le_card_of_internallyDisjoint_of_isVertexCut {s t : V} {k : ℕ} {Q : Fin k → List E}
    (hQ : ∀ i, IsDipath src tgt s t (Q i))
    (hdisj : InternallyDisjoint tgt s t Q)
    {T : Finset V} (hT : IsVertexCut src tgt s t T) : k ≤ T.card := by
  choose v hv hvT using fun i => hT.2.2 (Q i) (hQ i)
  have hinj : Function.Injective fun i => (⟨v i, hvT i⟩ : T) := by
    intro i j hij
    by_contra hne
    have heq : v i = v j := congrArg Subtype.val hij
    rcases hdisj hne (v i) (hv i) (heq ▸ hv j) with h | h
    · exact hT.1 (h ▸ hvT i)
    · exact hT.2.1 (h ▸ hvT i)
  simpa using Fintype.card_le_of_injective _ hinj

/-- **Weak duality for vertex-disjoint `A`–`B` paths in a multidigraph**. -/
theorem card_le_card_of_disjoint_of_isSeparator {A B : Set V} {k : ℕ} {Q : Fin k → List E}
    {a b : Fin k → V} (ha : ∀ i, a i ∈ A) (hb : ∀ i, b i ∈ B)
    (hQ : ∀ i, IsDipath src tgt (a i) (b i) (Q i))
    (hdisj : Pairwise fun i j => (a i :: (Q i).map tgt).Disjoint (a j :: (Q j).map tgt))
    {Y : Finset V} (hY : IsSeparator src tgt A B ↑Y) : k ≤ Y.card := by
  choose v hv hvY using fun i => hY (ha i) (hb i) (Q i) (hQ i)
  have hinj : Function.Injective fun i => (⟨v i, hvY i⟩ : Y) := by
    intro i j hij
    by_contra hne
    have heq : v i = v j := congrArg Subtype.val hij
    exact hdisj hne (hv i) (heq ▸ hv j)
  simpa using Fintype.card_le_of_injective _ hinj

end Cslib.Multidigraph
