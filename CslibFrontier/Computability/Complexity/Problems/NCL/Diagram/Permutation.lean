/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.CrossingLabels
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Measure
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.CheckGens
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Nodup

/-!
# Colored wire permutations

`reorder` moves labels to their requested order using adjacent swaps. It repeatedly moves the
next requested label left and recurses on the remaining labels. Colors follow labels, and the
returned labeling tracks every wire through the resulting diagram.

## Main definitions

* `Diagram.Wiring`: a diagram consisting of wires and swaps, with a boundary labeling.
* `Diagram.reorder`: a computable colored wiring for two permuted label lists.

## Main results

* `Diagram.Wiring.no_inner`: a wiring creates no new wires.
* `Diagram.Wiring.legal`: its graph imposes no vertex constraints.
* `Diagram.crossingPairs_reorder_nodup`: actual reordering crosses each pair at most once.
* `Diagram.owner_bounds_crossingPairs_reorder`: row-sorted boundaries give only local swaps.
-/

public section

namespace Cslib.Complexity.NCL.Diagram

variable {Γ : List Color → List Color → Type} {Label : Type*} {a b c d : List Color}

/-- A labeled wiring, built from identity wires and crossings. -/
structure Wiring (Γ : List Color → List Color → Type) (a b : List Color) (x y : List Label) where
  /-- The underlying colored diagram. -/
  diagram : Diagram Γ a b
  /-- The identities of its wires at both boundaries. -/
  labeling : Labeling diagram x y
  /-- No generator appears in the diagram. -/
  noGens : diagram.checkGens (fun _ => false) = true

namespace Wiring

variable {x y z x' y' : List Label}

/-- Transport the boundary color lists of a wiring along equalities. -/
@[expose] def cast {a' b' : List Color} (ha : a = a') (hb : b = b') (D : Wiring Γ a b x y) :
    Wiring Γ a' b' x y := ha ▸ hb ▸ D

/-- Boundary transport preserves the crossing count. -/
theorem swapCount_cast {a' b' : List Color} (ha : a = a') (hb : b = b')
    (D : Wiring Γ a b x y) : swapCount (D.cast ha hb).diagram = swapCount D.diagram := by
  cases ha
  cases hb
  rfl

/-- Straight labeled wires. -/
@[expose] def id (a : List Color) (x : List Label) (h : x.length = a.length) : Wiring Γ a a x x :=
  ⟨Diagram.id a, Labeling.id a x h, rfl⟩

/-- Stack two compatible wirings. -/
@[expose] def comp (D : Wiring Γ a b x y) (D' : Wiring Γ b c y z) : Wiring Γ a c x z :=
  ⟨D.diagram.comp D'.diagram, D.labeling.comp D'.labeling,
    by simp only [checkGens, D.noGens, D'.noGens, Bool.true_and]⟩

/-- Juxtapose wirings. -/
@[expose] def tensor (D : Wiring Γ a b x y) (D' : Wiring Γ c d x' y') :
    Wiring Γ (a ++ c) (b ++ d) (x ++ x') (y ++ y') :=
  ⟨D.diagram.tensor D'.diagram, D.labeling.tensor D'.labeling,
    by simp only [checkGens, D.noGens, D'.noGens, Bool.true_and]⟩

/-- Move one labeled wire left across a bundle. -/
@[expose] def moveLeft (x : Color) (tag : Label) (r : List Color) (rs : List Label)
    (hrs : rs.length = r.length) (l : List Color) (ls : List Label)
    (hls : ls.length = l.length) :
    Wiring Γ (l ++ x :: r) (x :: (l ++ r)) (ls ++ tag :: rs) (tag :: (ls ++ rs)) :=
  ⟨Diagram.moveLeft l x r, Labeling.moveLeft x tag r rs hrs l ls hls,
    checkGens_moveLeft _ l x r⟩

/-- Boundary color transport preserves every labeled crossing event. -/
theorem crossingPairs_cast {a' b' : List Color} (ha : a = a') (hb : b = b')
    (D : Wiring Γ a b x y) :
    (D.cast ha hb).diagram.crossingPairs (D.cast ha hb).labeling.label =
      D.diagram.crossingPairs D.labeling.label := by
  cases ha
  cases hb
  rfl

/-- Stacking wirings concatenates their labeled crossing events. -/
private theorem crossingPairs_comp (D : Wiring Γ a b x y) (D' : Wiring Γ b c y z) :
    (D.comp D').diagram.crossingPairs (D.comp D').labeling.label =
      D.diagram.crossingPairs D.labeling.label ++ D'.diagram.crossingPairs D'.labeling.label :=
  Labeling.crossingPairs_comp D.labeling D'.labeling

/-- Juxtaposition concatenates the labeled crossing events. -/
private theorem crossingPairs_tensor (D : Wiring Γ a b x y) (D' : Wiring Γ c d x' y') :
    (D.tensor D').diagram.crossingPairs (D.tensor D').labeling.label =
      D.diagram.crossingPairs D.labeling.label ++ D'.diagram.crossingPairs D'.labeling.label :=
  Labeling.crossingPairs_tensor D.labeling D'.labeling

/-- Moving one labeled wire left crosses each preceding label exactly once. -/
private theorem crossingPairs_moveLeft (x : Color) (tag : Label) (r : List Color) (rs : List Label)
    (hrs : rs.length = r.length) (l : List Color) (ls : List Label) (hls : ls.length = l.length) :
    (moveLeft (Γ := Γ) x tag r rs hrs l ls hls).diagram.crossingPairs
      (moveLeft x tag r rs hrs l ls hls).labeling.label = ls.reverse.map (·, tag) :=
  Labeling.crossingPairs_moveLeft x tag r rs hrs l ls hls

private theorem no_inner_of_noGens : ∀ {a b : List Color} (D : Diagram Γ a b),
    D.checkGens (fun _ => false) = true → IsEmpty D.Inner
  | _, _, .gen _, h => by cases h
  | _, _, .id _, _ => ⟨Empty.elim⟩
  | _, _, .swap .., _ => ⟨Empty.elim⟩
  | _, _, .comp D₁ D₂, h | _, _, .tensor D₁ D₂, h =>
    let h' := Bool.and_eq_true_iff.1 h
    letI := no_inner_of_noGens D₁ h'.1
    letI := no_inner_of_noGens D₂ h'.2
    show IsEmpty (D₁.Inner ⊕ D₂.Inner) from inferInstance

private theorem checks_of_noGens (test : ∀ {a b : List Color}, Γ a b → Bool) :
    ∀ {a b : List Color} (D : Diagram Γ a b), D.checkGens (fun _ => false) = true →
      D.checkGens test = true
  | _, _, .gen _, h => by cases h
  | _, _, .id _, _ => rfl
  | _, _, .swap .., _ => rfl
  | _, _, .comp D₁ D₂, h | _, _, .tensor D₁ D₂, h =>
    congrArg₂ (· && ·) (checks_of_noGens test D₁ (Bool.and_eq_true_iff.1 h).1)
      (checks_of_noGens test D₂ (Bool.and_eq_true_iff.1 h).2)

/-- All generator checks pass on a wiring. -/
theorem all_checks (D : Wiring Γ a b x y)
    (test : ∀ {a b : List Color}, Γ a b → Bool) : D.diagram.checkGens test = true :=
  checks_of_noGens test D.diagram D.noGens

/-- A wiring creates no new edges; every edge comes from the top boundary. -/
theorem no_inner (D : Wiring Γ a b x y) : IsEmpty D.diagram.Inner :=
  no_inner_of_noGens D.diagram D.noGens

private theorem legal_of_noGens (I : Interp Γ) :
    ∀ {a b : List Color} (D : Diagram Γ a b), D.checkGens (fun _ => false) = true →
      ∀ s, (D.graph I).Legal s
  | _, _, .gen _, h, _ => by cases h
  | _, _, .id _, _, _ => fun v => v.elim
  | _, _, .swap .., _, _ => fun v => v.elim
  | _, _, .comp D₁ D₂, h, s =>
    (legal_comp_iff D₁ D₂ s).2
      ⟨legal_of_noGens I D₁ (Bool.and_eq_true_iff.1 h).1 _,
        legal_of_noGens I D₂ (Bool.and_eq_true_iff.1 h).2 _⟩
  | _, _, .tensor D₁ D₂, h, s =>
    (legal_tensor_iff D₁ D₂ s).2
      ⟨legal_of_noGens I D₁ (Bool.and_eq_true_iff.1 h).1 _,
        legal_of_noGens I D₂ (Bool.and_eq_true_iff.1 h).2 _⟩

/-- A wiring imposes no vertex constraints. -/
theorem legal (D : Wiring Γ a b x y) (I : Interp Γ) (s : D.diagram.Edge → Bool) :
    (D.diagram.graph I).Legal s := legal_of_noGens I D.diagram D.noGens s

end Wiring

end Cslib.Complexity.NCL.Diagram

end

public section

namespace Cslib.Complexity.NCL.Diagram

variable {Γ : List Color → List Color → Type} {Label : Type*} [DecidableEq Label]

private structure Split (tag : Label) (xs : List Label) where
  before : List Label
  after : List Label
  eq_list : xs = before ++ tag :: after

private def splitAt (tag : Label) : (xs : List Label) → tag ∈ xs → Split tag xs
  | [], h => (List.not_mem_nil h).elim
  | x :: xs, h =>
    if he : x = tag then ⟨[], xs, by simp only [he, List.nil_append]⟩
    else
      let r := splitAt tag xs ((List.mem_cons.1 h).resolve_left (Ne.symm he))
      ⟨x :: r.before, r.after, congrArg (x :: ·) r.eq_list⟩

private structure CrossingTrace (xs ys : List Label) (pairs : List (Label × Label)) : Prop where
  supports : ∀ a b, (a, b) ∈ pairs → [a, b].Sublist xs ∧ [b, a].Sublist ys
  nodup : xs.Nodup → pairs.Nodup

omit [DecidableEq Label] in
private theorem pull_front_trace {pre post ys : List Label} {y : Label}
    {pairs : List (Label × Label)} (hp : (pre ++ post).Perm ys)
    (ht : CrossingTrace (pre ++ post) ys pairs) :
    CrossingTrace (pre ++ y :: post) (y :: ys) (pre.reverse.map (·, y) ++ pairs) := by
  have hsub : (pre ++ post).Sublist (pre ++ y :: post) :=
    (List.Sublist.refl pre).append ((List.Sublist.refl post).cons y)
  constructor
  · intro a b hab
    rcases List.mem_append.mp hab with hab | hab
    · obtain ⟨z, hz, hzy⟩ := List.mem_map.mp hab
      obtain ⟨ha, hb⟩ := Prod.mk.inj hzy
      subst a
      subst b
      have hz' : z ∈ pre := List.mem_reverse.mp hz
      have hzy : z ∈ ys := hp.mem_iff.mp (List.mem_append_left post hz')
      exact ⟨(List.singleton_sublist.mpr hz').append (.cons_cons y (List.nil_sublist _)),
        (List.singleton_sublist.mpr hzy).cons_cons y⟩
    · obtain ⟨hx, hy⟩ := ht.supports a b hab
      exact ⟨hx.trans hsub, hy.cons y⟩
  · intro hn
    have hn' : (y :: (pre ++ post)).Nodup := List.perm_middle.nodup_iff.mp hn
    obtain ⟨hy, htail⟩ := List.nodup_cons.mp hn'
    have hpre : pre.Nodup := htail.sublist (List.sublist_append_left _ _)
    have hfront : (pre.reverse.map (·, y)).Nodup :=
      List.Nodup.map (fun a b h => congrArg Prod.fst h) (List.nodup_reverse.mpr hpre)
    refine List.nodup_append.mpr ⟨hfront, ht.nodup htail, ?_⟩
    intro e he f hf hef
    obtain ⟨z, _hz, rfl⟩ := List.mem_map.mp he
    subst f
    have hyin := (ht.supports z y hf).1.subset (show y ∈ [z, y] from by simp)
    exact hy hyin

private structure BoundedWiring (a b : List Color) (xs ys : List Label) where
  wiring : Wiring Γ a b xs ys
  bound : swapCount wiring.diagram ≤ ys.length ^ 2
  trace : CrossingTrace xs ys (wiring.diagram.crossingPairs wiring.labeling.label)

private def reorderBounded (color : Label → Color) : (ys xs : List Label) → xs.Perm ys →
    BoundedWiring (Γ := Γ) (xs.map color) (ys.map color) xs ys
  | [], xs, h => by
    have hx : xs = [] := List.perm_nil.1 h
    subst xs
    exact ⟨Wiring.id [] [] rfl, Nat.zero_le _,
      ⟨fun _ _ h => (List.not_mem_nil h).elim, fun _ => List.nodup_nil⟩⟩
  | y :: ys, xs, h => by
    obtain ⟨pre, post, rfl⟩ := splitAt y xs (h.mem_iff.mpr (List.mem_cons_self ..))
    have htail : (pre ++ post).Perm ys := (List.perm_middle.symm.trans h).cons_inv
    let first := Wiring.moveLeft (Γ := Γ) (color y) y (post.map color) post
      (List.length_map ..).symm (pre.map color) pre (List.length_map ..).symm
    let rest : BoundedWiring (Γ := Γ) (pre.map color ++ post.map color)
        (ys.map color) (pre ++ post) ys := by
      simpa only [List.map_append] using reorderBounded color ys (pre ++ post) htail
    let out := first.comp ((Wiring.id [color y] [y] rfl).tensor rest.wiring)
    have hout : out.diagram.crossingPairs out.labeling.label =
        pre.reverse.map (·, y) ++
          rest.wiring.diagram.crossingPairs rest.wiring.labeling.label := by
      simp only [out, first, Wiring.crossingPairs_comp, Wiring.crossingPairs_tensor,
        Wiring.crossingPairs_moveLeft, Wiring.id, crossingPairs, List.nil_append]
    have hcount : swapCount out.diagram = pre.length + swapCount rest.wiring.diagram := by
      rw [← length_crossingPairs out.diagram out.labeling.label, hout,
        List.length_append, List.length_map, List.length_reverse, length_crossingPairs]
    have hpre : pre.length ≤ ys.length := by
      have hlen := htail.length_eq
      rw [List.length_append] at hlen
      omega
    have hbound : swapCount out.diagram ≤ (y :: ys).length ^ 2 := by
      rw [hcount]
      have hr := rest.bound
      simp only [List.length_cons, pow_two, Nat.add_mul, Nat.mul_add,
        Nat.one_mul, Nat.mul_one] at hr ⊢
      omega
    have htrace : CrossingTrace (pre ++ y :: post) (y :: ys)
        (out.diagram.crossingPairs out.labeling.label) := by
      rw [hout]
      exact pull_front_trace htail rest.trace
    simpa only [List.map_append, List.map_cons, List.singleton_append] using
      (show BoundedWiring (Γ := Γ) (pre.map color ++ color y :: post.map color)
        (color y :: ys.map color) (pre ++ y :: post) (y :: ys) from ⟨out, hbound, htrace⟩)

/-- Route a list of colored labels to any specified permutation, using only adjacent swaps. -/
def reorder (color : Label → Color) (ys xs : List Label) (h : xs.Perm ys) :
    Wiring Γ (xs.map color) (ys.map color) xs ys :=
  (reorderBounded color ys xs h).wiring

/-- The canonical colored reordering uses at most quadratically many crossings. -/
theorem swapCount_reorder_le (color : Label → Color) (ys xs : List Label) (h : xs.Perm ys) :
    swapCount (reorder (Γ := Γ) color ys xs h).diagram ≤ ys.length ^ 2 :=
  (reorderBounded color ys xs h).bound

/-- Each actual crossing reverses the order of its two labels between the two boundaries. -/
private theorem crossingPairs_reorder_sublist (color : Label → Color) (ys xs : List Label)
    (h : xs.Perm ys) {a b : Label}
    (hp : (a, b) ∈ (reorder (Γ := Γ) color ys xs h).diagram.crossingPairs
      (reorder color ys xs h).labeling.label) : [a, b].Sublist xs ∧ [b, a].Sublist ys :=
  (reorderBounded color ys xs h).trace.supports a b hp

/-- A canonical reordering of distinct labels crosses each ordered pair at most once. -/
theorem crossingPairs_reorder_nodup (color : Label → Color) (ys xs : List Label)
    (h : xs.Perm ys) (hn : xs.Nodup) :
    ((reorder (Γ := Γ) color ys xs h).diagram.crossingPairs
      (reorder color ys xs h).labeling.label).Nodup :=
  (reorderBounded color ys xs h).trace.nodup hn

/-- Every wire at a canonical crossing belongs to the original boundary list. -/
theorem mem_crossingPairs_reorder (color : Label → Color) (ys xs : List Label)
    (h : xs.Perm ys) {a b : Label}
    (hp : (a, b) ∈ (reorder (Γ := Γ) color ys xs h).diagram.crossingPairs
      (reorder color ys xs h).labeling.label) : a ∈ xs ∧ b ∈ xs := by
  have hs := (crossingPairs_reorder_sublist color ys xs h hp).1
  exact ⟨hs.subset (by simp), hs.subset (by simp)⟩

/-- Source-row and owner-row sorting make every actual crossing local to adjacent owner rows. -/
theorem owner_bounds_crossingPairs_reorder (color : Label → Color) (ys xs : List Label)
    (h : xs.Perm ys) (srcRow ownerRow : Label → ℕ)
    (hxs : xs.Pairwise (fun a b => srcRow a ≤ srcRow b))
    (hys : ys.Pairwise (fun a b => ownerRow a ≤ ownerRow b))
    (hrow : ∀ a ∈ xs, ownerRow a ≤ srcRow a ∧ srcRow a ≤ ownerRow a + 1) {a b : Label}
    (hp : (a, b) ∈ (reorder (Γ := Γ) color ys xs h).diagram.crossingPairs
      (reorder color ys xs h).labeling.label) :
    ownerRow b ≤ ownerRow a ∧ ownerRow a ≤ ownerRow b + 1 := by
  obtain ⟨hab, hba⟩ := crossingPairs_reorder_sublist color ys xs h hp
  have hs := hxs.sublist hab
  have ho := hys.sublist hba
  simp only [List.pairwise_cons, List.mem_singleton, forall_eq] at hs ho
  obtain ⟨ha, hb⟩ := mem_crossingPairs_reorder color ys xs h hp
  exact ⟨ho.1, (hrow a ha).1.trans (hs.1.trans (hrow b hb).2)⟩

end Cslib.Complexity.NCL.Diagram
