/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.CertificateCycles
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.VertexMerge
import CslibFrontier.Computability.Complexity.Problems.Graph.DartConnectivity
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.EdgeDeletionTransport
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.VertexJoinGenus
import CslibFrontier.Foundations.GroupTheory.Perm.CycleSurgery
import CslibFrontier.Foundations.GroupTheory.Perm.InvariantPredicate

/-!
# Joining both ends of two edges

The two endpoint pairs of nonloop marker edges in different components can be identified
by vertex-corner swaps. The first swap joins their components and makes the two opposite
marker darts cofacial. The second identification then preserves numerical genus zero.
Deleting the duplicate marker then yields the actual glued rotation. Its successor is
described in the original dart coordinates by the two swaps and one possible skip.
The two rooted cyclic words at the retained marker also use the original dart coordinates.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

open Equiv RotationCertificate Perm.CycleSurgery

private theorem faceNext_reverse {G : Graph} (r : RotationSystem G) (d : Dart G) :
    r.faceNext d.reverse = r.rotate.symm d :=
  congrArg r.rotate.symm (Dart.reverse_reverse d)

private theorem vertex_rotate_symm {G : Graph} (r : RotationSystem G) (d : Dart G) :
    (r.rotate.symm d).vertex = d.vertex := by
  rw [← r.vertex_rotate (r.rotate.symm d), r.rotate.apply_symm_apply]

private theorem faceNext_reverse_vertex {G : Graph} (r : RotationSystem G) (d : Dart G) :
    (r.faceNext d.reverse).vertex = d.vertex := by
  rw [faceNext_reverse, vertex_rotate_symm]

private theorem mergeDartEquiv_reverse_vertices {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) (a b : Dart G)
    (hb : b.vertex ≠ b.reverse.vertex) (hsep : ¬SameComponent G a.vertex b.vertex) :
    let h := r.faceNext a.reverse
    let k := r.faceNext b.reverse
    let e := mergeDartEquiv h k
    (e a.reverse).vertex = a.reverse.vertex ∧ (e b.reverse).vertex = b.reverse.vertex := by
  have unchanged (d : Dart G) (hd : d.vertex ≠ b.vertex) :
      (mergeDartEquiv (r.faceNext a.reverse) (r.faceNext b.reverse) d).vertex = d.vertex := by
    simp only [vertex_mergeDartEquiv, faceNext_reverse_vertex, Function.update_of_ne hd, id_eq]
  exact ⟨unchanged a.reverse (fun he => hsep (he ▸ sameComponent_reverse hG a)),
    unchanged b.reverse hb.symm⟩

private theorem sameCycle_after_join_swap {α : Type} [Finite α] [DecidableEq α]
    (f : Equiv.Perm α) {x y : α} (hne : x ≠ y) (hsep : ¬f.SameCycle x y) :
    (Equiv.swap x y * f).SameCycle x y := by
  let g := Equiv.swap x y * f
  by_contra hn
  have joined := (card_orbits_swap_mul f x y hne).2 hsep
  have undo := (card_orbits_swap_mul g x y hne).2 hn
  rw [Equiv.swap_mul_self_mul] at undo
  change Nat.card (Quotient (Perm.SameCycle.setoid g)) + 1 = _ at joined
  omega

/-- Identify corresponding ends of two nonloop marker edges in different components. The
first join swaps the clockwise successors immediately preceding the forward marker darts.
Their reverse darts then lie on one face, allowing the second join at those darts. Both
indexed markers remain in the result with corresponding endpoints identified, and the
constructed rotation has numerical genus zero. -/
theorem numericalGenusZero_mergeEdgeEnds {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) (hr : r.NumericalGenusZero)
    (a b : Dart G) (ha : a.vertex ≠ a.reverse.vertex) (hb : b.vertex ≠ b.reverse.vertex)
    (hsep : ¬SameComponent G a.vertex b.vertex) :
    let h := r.faceNext a.reverse
    let k := r.faceNext b.reverse
    let e := mergeDartEquiv h k
    let a' := e a.reverse
    let b' := e b.reverse
    ∃ (h₁ : h.vertex ≠ k.vertex) (h₂ : a'.vertex ≠ b'.vertex),
      let f := e.trans (mergeDartEquiv a' b')
      ((r.mergeVertices h k h₁).mergeVertices a' b' h₂).NumericalGenusZero ∧
        (f a).vertex = (f b).vertex ∧ (f a.reverse).vertex = (f b.reverse).vertex ∧
        (f a).vertex ≠ (f a.reverse).vertex := by
  classical
  dsimp only
  let h := r.faceNext a.reverse
  let k := r.faceNext b.reverse
  let e := mergeDartEquiv h k
  let a' := e a.reverse
  let b' := e b.reverse
  have hh : h.vertex = a.vertex := faceNext_reverse_vertex r a
  have hk : k.vertex = b.vertex := faceNext_reverse_vertex r b
  have hnot : ¬SameComponent G h.vertex k.vertex := hh.symm ▸ hk.symm ▸ hsep
  have h₁ : h.vertex ≠ k.vertex := fun he => hnot (he ▸ .refl (vertex_mem hG h))
  have differentFaces : ¬r.faceNext.SameCycle h k :=
    fun he => hnot (r.sameComponent_of_sameFace hG he)
  obtain ⟨av, bv⟩ := mergeDartEquiv_reverse_vertices r hG a b hb hsep
  have h₂ : a'.vertex ≠ b'.vertex := fun he => hsep ((sameComponent_reverse hG a).trans
    ((av.symm.trans (he.trans bv)).symm ▸ (sameComponent_reverse hG b).symm))
  let s := r.mergeVertices h k h₁
  let g := Equiv.swap h k * r.faceNext
  have hg : g.SameCycle h k :=
    sameCycle_after_join_swap r.faceNext (fun he => h₁ (congrArg Dart.vertex he)) differentFaces
  have semiconj : Function.Semiconj e g s.faceNext :=
    fun d => (r.faceNext_mergeVertices h k h₁ d).symm
  have cofacial : s.faceNext.SameCycle a' b' := by
    have fa : s.faceNext a' = e k :=
      (semiconj a.reverse).symm.trans (congrArg e (swap_apply_left h k))
    have fb : s.faceNext b' = e h :=
      (semiconj b.reverse).symm.trans (congrArg e (swap_apply_right h k))
    exact Perm.sameCycle_apply_right.mp <| Perm.sameCycle_apply_left.mp <|
      fa.symm ▸ fb.symm ▸ (hg.map_of_semiconj semiconj).symm
  have endpoint := vertex_mergeDartEquiv a' b'
  refine ⟨h₁, h₂, s.numericalGenusZero_mergeVertices (mergeGraph_endpoints_declared h k hG)
    (r.numericalGenusZero_mergeVertices_of_not_sameComponent hG hr h k h₁ hnot) a' b' h₂ cofacial,
    ?_, ?_, ?_⟩
  · rw [Equiv.trans_apply, Equiv.trans_apply, endpoint, endpoint,
      vertex_mergeDartEquiv h k a, vertex_mergeDartEquiv h k b, ← hh, ← hk,
      Function.update_self, Function.update_of_ne h₁, id_eq]
  · rw [Equiv.trans_apply, Equiv.trans_apply, endpoint, endpoint,
      Function.update_self, Function.update_of_ne h₂, id_eq]
  · have frontA : (e a).vertex = a.vertex := by
      simp only [e, vertex_mergeDartEquiv, Function.update_of_ne (mt hh.trans h₁), id_eq]
    have otherB : a.vertex ≠ b'.vertex :=
      bv.symm ▸ fun he => hsep (he.symm ▸ (sameComponent_reverse hG b).symm)
    rwa [Equiv.trans_apply, Equiv.trans_apply, endpoint, endpoint, frontA,
      Function.update_of_ne otherB, Function.update_of_ne h₂, id_eq, av]

private theorem lifted_rotationWord_eq {G H : Graph} (s : RotationSystem H)
    (lift : Dart H ↪ Dart G) (root : Dart H) (tail : List ℕ)
    (hn : ((lift root).index :: tail).Nodup)
    (hstep : ∀ d, d.vertex = root.vertex →
      ((lift root).index :: tail).formPerm (lift d).index = (lift (s.rotate d)).index) :
    (List.range (Function.minimalPeriod s.rotate root)).map
      (fun n => (lift (s.rotate^[n] root)).index) = (lift root).index :: tail := by
  let word := (lift root).index :: tail
  have hpow (n : ℕ) :
      (word.formPerm ^ n) (lift root).index = (lift (s.rotate^[n] root)).index := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', Perm.mul_apply, ih, Function.iterate_succ_apply']
      exact hstep _ (Perm.iterate_eq_pow s.rotate n ▸
        (s.sameCycle_iff _ _).mp ((Perm.SameCycle.refl s.rotate root).pow_left (n := n)))
  have hi : Function.Injective (fun d => (lift d).index) := fun _ _ h =>
    lift.injective ((Dart.indexEquiv G).injective (Fin.ext h))
  have hrecur (n : ℕ) : s.rotate^[n] root = root ↔ word.length ∣ n := by
    rw [← hi.eq_iff, ← hpow n, List.formPerm_pow_apply_head _ _ hn]
    have hpos : 0 < word.length := Nat.zero_lt_succ _
    have hm := Nat.mod_lt n hpos
    change word[n % word.length] = word[0] ↔ _
    rw [hn.getElem_inj_iff, Nat.dvd_iff_mod_eq_zero]
  have hlen : Function.minimalPeriod s.rotate root = word.length :=
    Nat.dvd_antisymm
      (Function.isPeriodicPt_iff_minimalPeriod_dvd.mp ((hrecur word.length).mpr dvd_rfl))
      ((hrecur _).mp Function.iterate_minimalPeriod)
  change _ = word
  refine List.ext_getElem (by simp [hlen]) fun n hn₁ hn₂ => ?_
  simp only [List.getElem_map, List.getElem_range, ← hpow n,
    List.formPerm_pow_apply_head _ _ hn, word, Nat.mod_eq_of_lt hn₂]

private theorem lifted_rotationWord_of_skip {G H : Graph} (s : RotationSystem H)
    (lift : Dart H ↪ Dart G) {names : ℕ → ℕ} {splice f : Perm (Dart G)}
    {b x y : Dart G} {w : Dart H} {p : Dart G → Prop} {tail : List ℕ}
    (hcoords : ∀ d, d.vertex = names (lift d).vertex)
    (hrange : ∀ d, d ∈ Set.range lift ↔ d.1 ≠ b.1)
    (hstep : ∀ u v, s.rotate u = v ↔ splice (lift u) = lift v ∨
      ∃ tag, splice (lift u) = (b.1, tag) ∧ splice (b.1, tag) = lift v)
    (hw : lift w = x) (hname : ∀ d : Dart G, names d.vertex = x.vertex ↔ p d)
    (hpx : p x) (hy_edge : y.1 = b.1) (hpy : p y) (hpy' : ¬p y.reverse)
    (hagree : ∀ d, p d → splice d = f d) (hmem : ∀ d, p d → p (f d))
    (hn : (x.index :: tail).Nodup)
    (hform : ∀ d c, p d → d ≠ y → c ≠ y → (f d = c ∨ f d = y ∧ f y = c) →
      (x.index :: tail).formPerm d.index = c.index) :
    (List.range (Function.minimalPeriod s.rotate w)).map
      (fun i => (lift (s.rotate^[i] w)).index) = x.index :: tail := by
  have hwv : w.vertex = x.vertex := (hcoords w).trans ((hname _).mpr (hw.symm ▸ hpx))
  have hne (d : Dart H) : lift d ≠ y :=
    fun he => (hrange (lift d)).mp ⟨d, rfl⟩ ((congrArg Prod.fst he).trans hy_edge)
  refine (lifted_rotationWord_eq s lift w tail (by simpa only [hw] using hn) fun d hd => ?_).trans
    (by rw [hw])
  have hpd : p (lift d) := (hname _).mp ((hcoords d).symm.trans (hd.trans hwv))
  have hskip : f (lift d) = lift (s.rotate d) ∨ f (lift d) = y ∧ f y = lift (s.rotate d) := by
    rcases (hstep d (s.rotate d)).mp rfl with h1 | ⟨tag, h1, h2⟩
    · exact Or.inl ((hagree _ hpd).symm.trans h1)
    · rw [hagree _ hpd] at h1
      have htag : (b.1, tag) = y :=
        (Dart.eq_or_eq_reverse_of_edge_eq (d := (b.1, tag)) (e := y) hy_edge.symm).resolve_right
          fun hrev => hpy' (hrev ▸ h1 ▸ hmem _ hpd)
      exact Or.inr ⟨h1.trans htag, by rw [← hagree y hpy, ← htag]; exact h2⟩
  rw [hw]
  exact hform (lift d) (lift (s.rotate d)) hpd (hne d) (hne (s.rotate d)) hskip

open Classical in
/-- Glue two nonloop marker edges from different components, retaining `a` and deleting `b`.
The graph identifies the two pairs of endpoint names and keeps the original edge list with
only the selected occurrence removed. In the original dart coordinates, the successor
swaps at the two predecessors of the forward markers and at the two reverse markers;
when the result points to a deleted end, it continues through that end. Every surviving
dart has a unique preimage in the glued rotation. The rooted words at the retained marker
list the two old tails in forward order at its first end and reversed block order at its
other end, with the direction of each tail preserved. -/
theorem exists_numericalGenusZero_glueMarkerEdges {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) (hr : r.NumericalGenusZero)
    (a b : Dart G) (ha : a.vertex ≠ a.reverse.vertex) (hb : b.vertex ≠ b.reverse.vertex)
    (hsep : ¬SameComponent G a.vertex b.vertex) :
    let names := Function.update id b.reverse.vertex a.reverse.vertex ∘
      Function.update id b.vertex a.vertex
    let splice := r.rotate * swap (r.faceNext a.reverse) (r.faceNext b.reverse) *
      swap a.reverse b.reverse
    let word (d : Dart G) := cycleWord (ofRotation r) d.index
    ∃ (H : Graph) (s : RotationSystem H) (lift : Dart H ↪ Dart G),
      H.vertices = (G.relabel names).vertices ∧
      H.edges = (G.relabel names).edges.eraseIdx b.1.val ∧ s.NumericalGenusZero ∧
      (∀ d, d.vertex = names (lift d).vertex ∧ (lift d).2 = d.2 ∧
        (lift d).1.val = if d.1.val < b.1.val then d.1.val else d.1.val + 1) ∧
      (∀ d, d ∈ Set.range lift ↔ d.1 ≠ b.1) ∧
      (∀ x y, s.rotate x = y ↔ splice (lift x) = lift y ∨
        ∃ tag, splice (lift x) = (b.1, tag) ∧ splice (b.1, tag) = lift y) ∧
      ∃ u, lift u = a ∧ lift u.reverse = a.reverse ∧
        ((List.range (Function.minimalPeriod s.rotate u)).map
          (fun i => (lift (s.rotate^[i] u)).index)) =
          a.index :: ((word a).tail ++ (word b).tail) ∧
        ((List.range (Function.minimalPeriod s.rotate u.reverse)).map
          (fun i => (lift (s.rotate^[i] u.reverse)).index)) =
          a.reverse.index :: ((word b.reverse).tail ++ (word a.reverse).tail) := by
  dsimp only
  let h := r.faceNext a.reverse
  let k := r.faceNext b.reverse
  let e := mergeDartEquiv h k
  let a' := e a.reverse
  let b' := e b.reverse
  let f := e.trans (mergeDartEquiv a' b')
  let names := Function.update id b.reverse.vertex a.reverse.vertex ∘
    Function.update id b.vertex a.vertex
  let splice := r.rotate * swap h k * swap a.reverse b.reverse
  obtain ⟨h₁, h₂, hgenus, hfront, hback, hnonloop⟩ :=
    r.numericalGenusZero_mergeEdgeEnds hG hr a b ha hb hsep
  let t := (r.mergeVertices h k h₁).mergeVertices a' b' h₂
  have hh : h.vertex = a.vertex := faceNext_reverse_vertex r a
  have hk : k.vertex = b.vertex := faceNext_reverse_vertex r b
  obtain ⟨av, bv⟩ : a'.vertex = a.reverse.vertex ∧ b'.vertex = b.reverse.vertex :=
    mergeDartEquiv_reverse_vertices r hG a b hb hsep
  have hgraph : mergeGraph a' b' = G.relabel names := by
    change (G.relabel (Function.update id k.vertex h.vertex)).relabel
      (Function.update id b'.vertex a'.vertex) = G.relabel names
    rw [hh, hk, av, bv]
    exact Graph.ext (by simp [Graph.relabel, names])
      (by simp [Graph.relabel, names, Function.comp_def])
  have hcoords (d : Dart G) : (f d).vertex = names d.vertex := by
    simp [f, e, vertex_mergeDartEquiv, av, bv, hh, hk, names]
  have hrotate (d : Dart G) : t.rotate (f d) = f (splice d) := by
    change ((r.mergeVertices h k h₁).mergeVertices a' b' h₂).rotate
      (mergeDartEquiv a' b' (e d)) = mergeDartEquiv a' b' (e (splice d))
    rw [rotate_mergeVertices, permCongr_apply, symm_apply_apply, Perm.mul_apply,
      (e.injective.map_swap a.reverse b.reverse d).symm,
      rotate_mergeVertices, permCongr_apply, symm_apply_apply]
    rfl
  have hb' : (f b).vertex ≠ (f b.reverse).vertex := hfront ▸ hback ▸ hnonloop
  have htag (tag : Bool) : f (b.1, tag) = ((f b).1, tag) := by cases tag <;> rfl
  have hnb : Dart.vertex (G := mergeGraph a' b') ((f b).1, false) ≠
      Dart.vertex ((f b).1, true) := by
    rw [← htag false, ← htag true]
    rcases b with ⟨i, _ | _⟩ <;> first | exact hb' | exact hb'.symm
  obtain ⟨H, s, e', hV, hEdges, hz, he', hstep⟩ := t.exists_numericalGenusZero_deleteNonloopEdge
    (mergeGraph_endpoints_declared a' b' (mergeGraph_endpoints_declared h k hG))
    hgenus (f b).1 hnb
  let lift := e'.trans f.symm.toEmbedding
  have hLift (d : Dart H) : f (lift d) = e' d := f.apply_symm_apply _
  have coords (d : Dart H) : d.vertex = names (lift d).vertex ∧ (lift d).2 = d.2 ∧
      (lift d).1.val = if d.1.val < b.1.val then d.1.val else d.1.val + 1 := by
    have hc := he' d
    rw [← hLift d, hcoords] at hc
    exact ⟨hc.1.symm, hc.2.1, hc.2.2⟩
  have hEdges' : H.edges = (G.relabel names).edges.eraseIdx b.1.val := hgraph ▸ hEdges
  have hSize : H.edges.length + 1 = G.edges.length := by
    have := b.1.isLt
    rw [hEdges', List.length_eraseIdx_of_lt (by simp [Graph.relabel])]
    simp only [Graph.relabel, List.length_map]; omega
  let castIndex := finCongr hSize.symm
  let removed := castIndex b.1
  have hskipIndex (d : Dart H) : castIndex (lift d).1 = removed.succAbove d.1 := by
    ext
    simp only [castIndex, finCongr_apply, Fin.val_cast, (coords d).2.2, Fin.succAbove,
      Fin.lt_def, Fin.val_castSucc, removed]
    split_ifs <;> rfl
  have hrange (d : Dart G) : d ∈ Set.range lift ↔ d.1 ≠ b.1 := by
    have hsurvivor : castIndex d.1 ∈ Set.range removed.succAbove ↔ d.1 ≠ b.1 := by
      simp [Fin.range_succAbove, removed]
    rw [← hsurvivor]
    exact ⟨fun ⟨x, hx⟩ => ⟨x.1, hx ▸ (hskipIndex x).symm⟩, fun ⟨j, hj⟩ =>
      ⟨(j, d.2), Prod.ext (castIndex.injective ((hskipIndex (j, d.2)).trans hj))
        (coords (j, d.2)).2.1⟩⟩
  have hstep (x y : Dart H) : s.rotate x = y ↔ splice (lift x) = lift y ∨
      ∃ tag, splice (lift x) = (b.1, tag) ∧ splice (b.1, tag) = lift y := by
    simpa only [← hLift, ← htag, hrotate, f.injective.eq_iff] using hstep x y
  -- Each swap acts only at one of the two pairs of endpoint fibers.
  have differentEnds {x y : Dart G} (hx : SameComponent G a.vertex x.vertex)
      (hy : SameComponent G b.vertex y.vertex) : x.vertex ≠ y.vertex :=
    fun he => hsep (hx.trans (he.symm ▸ hy.symm))
  have hab := differentEnds (.refl (vertex_mem hG a)) (.refl (vertex_mem hG b))
  have hab' := differentEnds (.refl (vertex_mem hG a)) (sameComponent_reverse hG b)
  have ha'b := differentEnds (sameComponent_reverse hG a) (.refl (vertex_mem hG b))
  have ha'b' := differentEnds (sameComponent_reverse hG a) (sameComponent_reverse hG b)
  let front (d : Dart G) := d.vertex = a.vertex ∨ d.vertex = b.vertex
  let back (d : Dart G) := d.vertex = a.reverse.vertex ∨ d.vertex = b.reverse.vertex
  have disjoint (d : Dart G) (hf : front d) (hb' : back d) : False := by
    rcases hf with he | he <;> rcases hb' with hr' | hr'
    exacts [ha (he.symm.trans hr'), hab' (he.symm.trans hr'),
      ha'b (hr'.symm.trans he), hb (he.symm.trans hr')]
  have nameFront (d : Dart G) : names d.vertex = a.vertex ↔ front d := by
    by_cases hf : d.vertex = b.vertex <;> by_cases hb' : d.vertex = b.reverse.vertex <;>
      simp [names, front, hf, hb', hb.symm, ha.symm, hab', hab'.symm]
  have nameBack (d : Dart G) : names d.vertex = a.reverse.vertex ↔ back d := by
    by_cases hf : d.vertex = b.vertex <;> by_cases hb' : d.vertex = b.reverse.vertex <;>
      simp [names, back, hf, hb', hab', ha, ha'b.symm, hb, hb.symm]
  let before := r.rotate * swap (r.rotate.symm a) (r.rotate.symm b)
  let after := r.rotate * swap a.reverse b.reverse
  have hswapMem (p : Dart G → Prop) (d x y : Dart G)
      (hx : p x) (hy : p y) (hd : p d) : p (swap x y d) :=
    (Equiv.predicate_swap p x y (iff_of_true hx hy) d).mpr hd
  have hbefore (d : Dart G) (hd : front d) : splice d = before d := by
    have hda : d ≠ a.reverse := fun he => disjoint d hd (Or.inl (congrArg Dart.vertex he))
    have hdb : d ≠ b.reverse := fun he => disjoint d hd (Or.inr (congrArg Dart.vertex he))
    change (r.rotate * swap h k) (swap a.reverse b.reverse d) = _
    rw [swap_apply_of_ne_of_ne hda hdb]
    simp only [h, k, faceNext_reverse, before]
  have hafter (d : Dart G) (hd : back d) : splice d = after d := by
    let e := swap a.reverse b.reverse d
    have he : back e := hswapMem back d a.reverse b.reverse (Or.inl rfl) (Or.inr rfl) hd
    have heh : e ≠ h := fun he' => disjoint e (Or.inl ((congrArg Dart.vertex he').trans hh)) he
    have hek : e ≠ k := fun he' => disjoint e (Or.inr ((congrArg Dart.vertex he').trans hk)) he
    change r.rotate (swap h k e) = r.rotate e
    rw [swap_apply_of_ne_of_ne heh hek]
  have beforeMem (d : Dart G) (hd : front d) : front (before d) := by
    simpa only [before, Perm.mul_apply, front, r.vertex_rotate] using
      hswapMem front d (r.rotate.symm a) (r.rotate.symm b)
        (Or.inl (vertex_rotate_symm r a)) (Or.inr (vertex_rotate_symm r b)) hd
  have afterMem (d : Dart G) (hd : back d) : back (after d) := by
    simpa only [after, Perm.mul_apply, back, r.vertex_rotate] using
      hswapMem back d a.reverse b.reverse (Or.inl rfl) (Or.inr rfl) hd
  have ret : a.1 ≠ b.1 := fun he =>
    (Dart.eq_or_eq_reverse_of_edge_eq he).elim (fun h => hab (congrArg Dart.vertex h))
      (fun h => hab' (congrArg Dart.vertex h))
  obtain ⟨u, hu⟩ := (hrange a).mpr ret
  have hv : lift u.reverse = a.reverse := by
    rw [← hu]
    exact Prod.ext (Fin.ext ((coords u.reverse).2.2.trans (coords u).2.2.symm))
      ((coords u.reverse).2.1.trans (congrArg Bool.not (coords u).2.1.symm))
  let word (d : Dart G) := cycleWord (ofRotation r) d.index
  have hc : verifyRotation G (ofRotation r) = true := verifyRotation_ofRotation r hG
  have nodupHeads (x y : Dart G) (hxy : x.vertex ≠ y.vertex) :
      (x.index :: ((word x).tail ++ (word y).tail)).Nodup ∧
      (x.index :: ((word y).tail ++ (word x).tail)).Nodup := by
    have hn : (word x ++ (word y).tail).Nodup := List.nodup_append'.mpr
      ⟨nodup_cycleWord hc x, (nodup_cycleWord hc y).sublist (List.tail_sublist _),
        List.disjoint_left.mpr fun _ hx hy =>
          List.disjoint_left.mp (disjoint_cycleWord hc x y hxy) hx (List.mem_of_mem_tail hy)⟩
    exact ⟨hn, (List.Perm.cons _ List.perm_append_comm).nodup_iff.mp hn⟩
  refine ⟨H, s, lift, hV.trans (congrArg Graph.vertices hgraph), hEdges', hz, coords, hrange,
    hstep, u, hu, hv, ?_, ?_⟩
  · exact lifted_rotationWord_of_skip s lift (fun d => (coords d).1) hrange hstep hu nameFront
      (Or.inl rfl) rfl (Or.inr rfl) (fun hb' => disjoint b.reverse hb' (Or.inr rfl))
      hbefore beforeMem (nodupHeads a b hab).1 fun d c hfd hd hc' hs =>
        (formPerm_cycleWord_join_skip_iff r hG a b d c hab hfd hd hc').1.mpr hs
  · exact lifted_rotationWord_of_skip s lift (y := b.reverse) (fun d => (coords d).1) hrange
      hstep hv nameBack (Or.inl rfl) rfl (Or.inr rfl)
      (fun hb' => disjoint b (Or.inr rfl) (by simpa only [Dart.reverse_reverse] using hb'))
      hafter afterMem (nodupHeads a.reverse b.reverse ha'b').2 fun d c hbd hd hc' hs =>
        (formPerm_cycleWord_join_skip_iff r hG a.reverse b.reverse d c ha'b' hbd hd hc').2.mpr hs

end Cslib.Complexity.Graph.RotationSystem
