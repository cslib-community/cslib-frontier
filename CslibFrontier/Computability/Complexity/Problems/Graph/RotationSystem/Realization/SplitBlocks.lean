/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.EdgeContraction
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.IntervalOrder
public import CslibFrontier.Foundations.GroupTheory.Perm.RemoveTwo

/-!
# The two retained blocks at a contracted edge

Cut a source vertex cycle at the actual dart of the edge being contracted. Its other
darts have the literal successive ranks one through period minus one. A singleton
source cycle gives an empty block. Indexed parallel occurrences and both ends of loops
are retained as distinct darts.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

/-- Lift a retained contracted dart to its actual source edge occurrence and end tag. -/
@[expose] def contractionLift (G : Graph) (u v : ℕ)
    (d : Dart (contractLastEdgeGraph G u v)) : Dart (lastEdgeGraph G u v) :=
  ((contractLastEdgeDartEquiv G u v).trans
    (lastEdgeDartEquiv (contractLastEdgeGraph G u v) v v)).symm (some (some d))

/-- The retained coordinate has exactly its original double-`some` tag. -/
theorem contractionLift_coordinates (G : Graph) (u v : ℕ)
    (d : Dart (contractLastEdgeGraph G u v)) :
    ((contractLastEdgeDartEquiv G u v).trans
      (lastEdgeDartEquiv (contractLastEdgeGraph G u v) v v)) (contractionLift G u v d) =
        some (some d) := Equiv.apply_symm_apply _ _

/-- A retained edge keeps its literal old index and Boolean end tag under the lift. -/
theorem contractionLift_relabelEquiv (G : Graph) (u v : ℕ) (d : Dart G) :
    contractionLift G u v (Dart.relabelEquiv G (Function.update id u v) d) =
      retainedLastEdgeDart G u v d := by
  refine ((contractLastEdgeDartEquiv G u v).trans
    (lastEdgeDartEquiv (contractLastEdgeGraph G u v) v v)).injective ?_
  refine (contractionLift_coordinates G u v _).trans (Eq.symm ?_)
  exact (Equiv.congr_fun (contractLastEdge_coordinates G u v) _).trans
    (congrArg (Dart.relabelEquiv G (Function.update id u v)).optionCongr.optionCongr
      ((lastEdgeDartEquiv G u v).apply_symm_apply (some (some d))))

/-- Distinct retained ends lift to distinct source ends, including ends of a target loop. -/
theorem contractionLift_injective (G : Graph) (u v : ℕ) :
    Function.Injective (contractionLift G u v) := by
  intro a b h
  have heq := congrArg ((contractLastEdgeDartEquiv G u v).trans
    (lastEdgeDartEquiv (contractLastEdgeGraph G u v) v v)) h
  simpa only [contractionLift_coordinates, Option.some.injEq] using heq

/-- A retained dart is never either deleted end of the selected source edge. -/
theorem contractionLift_ne_lastEdgeDart (G : Graph) (u v : ℕ)
    (d : Dart (contractLastEdgeGraph G u v)) (side : Bool) :
    contractionLift G u v d ≠ lastEdgeDart G u v side := by
  intro h
  have heq := congrArg ((contractLastEdgeDartEquiv G u v).trans
    (lastEdgeDartEquiv (contractLastEdgeGraph G u v) v v)) h
  rw [contractionLift_coordinates, contractLastEdge_coordinates_last] at heq
  cases side <;> simp at heq

/-- Source endpoint names undergo exactly the prescribed directed identification. -/
theorem vertex_contractionLift (G : Graph) (u v : ℕ)
    (d : Dart (contractLastEdgeGraph G u v)) :
    Function.update id u v (contractionLift G u v d).vertex = d.vertex := by
  have he : contractLastEdgeDartEquiv G u v (contractionLift G u v d) =
      retainedLastEdgeDart (contractLastEdgeGraph G u v) v v d :=
    (lastEdgeDartEquiv (contractLastEdgeGraph G u v) v v).injective <| by
      simpa only [Equiv.trans_apply, retainedLastEdgeDart, Equiv.apply_symm_apply] using
        contractionLift_coordinates G u v d
  simpa only [vertex_contractLastEdgeDartEquiv, vertex_retainedLastEdgeDart] using
    congrArg Dart.vertex he

/-- Retained darts at the contracted name originate from precisely the two source
endpoint fibers. This includes both occurrences of a source edge that became a loop. -/
theorem contractionLift_vertex_eq_iff (G : Graph) (u v : ℕ)
    (d : Dart (contractLastEdgeGraph G u v)) :
    d.vertex = v ↔ (contractionLift G u v d).vertex = u ∨
      (contractionLift G u v d).vertex = v := by
  rw [← vertex_contractionLift G u v d]
  by_cases h : (contractionLift G u v d).vertex = u <;> simp [h]

/-- Exactly the two selected source darts are omitted by contraction. The retained
correspondence is an equivalence of actual occurrences, without identifying loop ends. -/
@[expose] noncomputable def contractionRetainedEquiv (G : Graph) (u v : ℕ) :
    Dart (contractLastEdgeGraph G u v) ≃
      {a : Dart (lastEdgeGraph G u v) // ∀ side, a ≠ lastEdgeDart G u v side} :=
  Equiv.ofBijective (fun d => ⟨contractionLift G u v d,
    contractionLift_ne_lastEdgeDart G u v d⟩) ⟨by
      intro a b h
      exact contractionLift_injective G u v (congrArg Subtype.val h), by
      intro a
      let e := (contractLastEdgeDartEquiv G u v).trans
        (lastEdgeDartEquiv (contractLastEdgeGraph G u v) v v)
      cases ha : e a.val with
      | none =>
        exact False.elim (a.property true (e.injective
          (ha.trans (contractLastEdge_coordinates_last G u v true).symm)))
      | some s =>
        cases s with
        | none =>
          exact False.elim (a.property false (e.injective
            (ha.trans (contractLastEdge_coordinates_last G u v false).symm)))
        | some d =>
          refine ⟨d, Subtype.ext ?_⟩
          apply e.injective
          exact (contractionLift_coordinates G u v d).trans ha.symm⟩

/-- The retained equivalence lifts to the original indexed source dart. -/
theorem contractionRetainedEquiv_apply_val (G : Graph) (u v : ℕ)
    (d : Dart (contractLastEdgeGraph G u v)) :
    (contractionRetainedEquiv G u v d).val = contractionLift G u v d := rfl

/-- The two source blocks of a retained contracted-vertex dart. The first block is
the retained `v` cycle and the second is the retained `u` cycle, both in their
original forward ranks after the deleted dart. -/
@[expose] noncomputable def contractionBlock {G : Graph} {u v : ℕ}
    (r : RotationSystem (lastEdgeGraph G u v))
    (d : {d : Dart (contractLastEdgeGraph G u v) // d.vertex = v}) :
    Fin (Function.minimalPeriod r.rotate (lastEdgeDart G u v true) - 1) ⊕
      Fin (Function.minimalPeriod r.rotate (lastEdgeDart G u v false) - 1) :=
  if hv : (contractionLift G u v d.val).vertex = v then
    Sum.inl (r.sourceTailEquiv (lastEdgeDart G u v true)
      ⟨contractionLift G u v d.val, by simpa using hv,
        contractionLift_ne_lastEdgeDart G u v d.val true⟩)
  else
    Sum.inr (r.sourceTailEquiv (lastEdgeDart G u v false)
      ⟨contractionLift G u v d.val, by
        have hu := ((contractionLift_vertex_eq_iff G u v d.val).mp d.property).resolve_right hv
        simpa using hu,
        contractionLift_ne_lastEdgeDart G u v d.val false⟩)

/-- Source block ranks distinguish every retained occurrence of the contracted vertex. -/
theorem contractionBlock_injective {G : Graph} {u v : ℕ}
    (r : RotationSystem (lastEdgeGraph G u v)) : Function.Injective r.contractionBlock := by
  intro a b heq
  apply Subtype.ext
  apply contractionLift_injective G u v
  unfold contractionBlock at heq
  split_ifs at heq
  · exact congrArg Subtype.val ((r.sourceTailEquiv _).injective (Sum.inl.inj heq))
  · exact congrArg Subtype.val ((r.sourceTailEquiv _).injective (Sum.inr.inj heq))

/-- Every entry of either retained source block is an actual contracted-vertex dart.
An empty block remains empty; no corner or port is supplied for it. -/
theorem contractionBlock_surjective {G : Graph} {u v : ℕ}
    (r : RotationSystem (lastEdgeGraph G u v)) (huv : u ≠ v) :
    Function.Surjective r.contractionBlock := by
  intro s
  cases s with
  | inl i =>
    let a := (r.sourceTailEquiv (lastEdgeDart G u v true)).symm i
    have hav : a.val.vertex = v := by
      simpa only [vertex_lastEdgeDart, ↓reduceIte] using a.property.1
    have ha : ∀ side, a.val ≠ lastEdgeDart G u v side := fun
      | false, h =>
        huv ((vertex_lastEdgeDart G u v false).symm.trans ((congrArg Dart.vertex h).symm.trans hav))
      | true, h => a.property.2 h
    let d := (contractionRetainedEquiv G u v).symm ⟨a.val, ha⟩
    have hlift : contractionLift G u v d = a.val :=
      congrArg Subtype.val ((contractionRetainedEquiv G u v).apply_symm_apply ⟨a.val, ha⟩)
    have hd : d.vertex = v := (contractionLift_vertex_eq_iff G u v d).mpr
      (Or.inr (hlift ▸ hav))
    refine ⟨⟨d, hd⟩, ?_⟩
    unfold contractionBlock
    rw [dite_eq_left (hlift ▸ hav)]
    apply congrArg Sum.inl
    calc
      _ = r.sourceTailEquiv (lastEdgeDart G u v true) a :=
        congrArg _ (Subtype.ext hlift)
      _ = i := (r.sourceTailEquiv _).apply_symm_apply i
  | inr i =>
    let a := (r.sourceTailEquiv (lastEdgeDart G u v false)).symm i
    have hau : a.val.vertex = u := by
      simpa only [vertex_lastEdgeDart, Bool.false_eq_true, ↓reduceIte] using a.property.1
    have ha : ∀ side, a.val ≠ lastEdgeDart G u v side := fun
      | false, h => a.property.2 h
      | true, h =>
        huv (hau.symm.trans ((congrArg Dart.vertex h).trans (vertex_lastEdgeDart G u v true)))
    let d := (contractionRetainedEquiv G u v).symm ⟨a.val, ha⟩
    have hlift : contractionLift G u v d = a.val :=
      congrArg Subtype.val ((contractionRetainedEquiv G u v).apply_symm_apply ⟨a.val, ha⟩)
    have hd : d.vertex = v := (contractionLift_vertex_eq_iff G u v d).mpr
      (Or.inl (hlift ▸ hau))
    have hdv : (contractionLift G u v d).vertex ≠ v := by rw [hlift, hau]; exact huv
    refine ⟨⟨d, hd⟩, ?_⟩
    unfold contractionBlock
    rw [dite_eq_right hdv]
    apply congrArg Sum.inr
    calc
      _ = r.sourceTailEquiv (lastEdgeDart G u v false) a :=
        congrArg _ (Subtype.ext hlift)
      _ = i := (r.sourceTailEquiv _).apply_symm_apply i

/-- Exact source block coordinates for every dart at the contracted vertex. -/
@[expose] noncomputable def contractionBlockEquiv {G : Graph} {u v : ℕ}
    (r : RotationSystem (lastEdgeGraph G u v)) (huv : u ≠ v) :
    {d : Dart (contractLastEdgeGraph G u v) // d.vertex = v} ≃
      Fin (Function.minimalPeriod r.rotate (lastEdgeDart G u v true) - 1) ⊕
        Fin (Function.minimalPeriod r.rotate (lastEdgeDart G u v false) - 1) :=
  Equiv.ofBijective r.contractionBlock ⟨r.contractionBlock_injective,
    r.contractionBlock_surjective huv⟩

/-- The actual contracted successor is first return in the literal outgoing-swapped
source rotation. The directed paths are obtained from the constructor, not assumed
as a block-order or splitter premise. -/
theorem contractionLift_rotate_paths {G : Graph} {u v : ℕ}
    (r : RotationSystem (lastEdgeGraph G u v)) (huv : u ≠ v)
    (d : Dart (contractLastEdgeGraph G u v)) :
    let σ := r.rotate * Equiv.swap (lastEdgeDart G u v true) (lastEdgeDart G u v false)
    let a := contractionLift G u v d
    let b := contractionLift G u v ((r.contractLastEdge huv).rotate d)
    σ a = b ∨
      (σ a = lastEdgeDart G u v true ∧ σ (lastEdgeDart G u v true) = b) ∨
      (σ a = lastEdgeDart G u v false ∧ σ (lastEdgeDart G u v false) = b) ∨
      (σ a = lastEdgeDart G u v true ∧
        σ (lastEdgeDart G u v true) = lastEdgeDart G u v false ∧
        σ (lastEdgeDart G u v false) = b) ∨
      (σ a = lastEdgeDart G u v false ∧
        σ (lastEdgeDart G u v false) = lastEdgeDart G u v true ∧
        σ (lastEdgeDart G u v true) = b) := by
  let e := (contractLastEdgeDartEquiv G u v).trans
    (lastEdgeDartEquiv (contractLastEdgeGraph G u v) v v)
  let σ := r.rotate * Equiv.swap (lastEdgeDart G u v true) (lastEdgeDart G u v false)
  have hpaths := Equiv.Perm.removeNone_removeNone_paths (e.permCongr σ) d
  have hT : e (lastEdgeDart G u v true) = none := contractLastEdge_coordinates_last G u v true
  have hF : e (lastEdgeDart G u v false) = some none :=
    contractLastEdge_coordinates_last G u v false
  dsimp only at hpaths ⊢
  rw [← r.rotate_contractLastEdge huv, ← contractionLift_coordinates G u v d,
    ← contractionLift_coordinates G u v _, ← hT, ← hF] at hpaths
  dsimp only [e] at hpaths
  simpa only [Equiv.permCongr_apply, Equiv.symm_apply_apply, Equiv.apply_eq_iff_eq] using hpaths

/-- The outgoing swap joins the retained `v` block to the retained `u` block.
The three-step alternatives skip a unary source cycle; their order is literal. -/
theorem contractionLift_rotate_cases {G : Graph} {u v : ℕ}
    (r : RotationSystem (lastEdgeGraph G u v)) (huv : u ≠ v)
    (d : Dart (contractLastEdgeGraph G u v)) :
    let a := contractionLift G u v d
    let b := contractionLift G u v ((r.contractLastEdge huv).rotate d)
    r.rotate a = b ∨
      (r.rotate a = lastEdgeDart G u v true ∧ r.rotate (lastEdgeDart G u v false) = b) ∨
      (r.rotate a = lastEdgeDart G u v false ∧ r.rotate (lastEdgeDart G u v true) = b) ∨
      (r.rotate a = lastEdgeDart G u v true ∧
        r.rotate (lastEdgeDart G u v false) = lastEdgeDart G u v false ∧
        r.rotate (lastEdgeDart G u v true) = b) ∨
      (r.rotate a = lastEdgeDart G u v false ∧
        r.rotate (lastEdgeDart G u v true) = lastEdgeDart G u v true ∧
        r.rotate (lastEdgeDart G u v false) = b) := by
  have hs : Equiv.swap (lastEdgeDart G u v true) (lastEdgeDart G u v false)
      (contractionLift G u v d) = contractionLift G u v d :=
    Equiv.swap_apply_of_ne_of_ne (contractionLift_ne_lastEdgeDart G u v d true)
      (contractionLift_ne_lastEdgeDart G u v d false)
  simpa only [Equiv.Perm.mul_apply, hs, Equiv.swap_apply_left,
    Equiv.swap_apply_right] using r.contractionLift_rotate_paths huv d

/-- Consecutive retained source-block ranks, with the `v` block first. -/
@[expose] noncomputable def contractionRank {G : Graph} {u v : ℕ}
    (r : RotationSystem (lastEdgeGraph G u v))
    (d : {d : Dart (contractLastEdgeGraph G u v) // d.vertex = v}) :
    Fin ((Function.minimalPeriod r.rotate (lastEdgeDart G u v true) - 1) +
      (Function.minimalPeriod r.rotate (lastEdgeDart G u v false) - 1)) :=
  finSumFinEquiv (r.contractionBlock d)

/-- The rank is the original first-hit rank minus the deleted dart, with an offset
for the second source block. No contracted distance is reused. -/
theorem val_contractionRank {G : Graph} {u v : ℕ}
    (r : RotationSystem (lastEdgeGraph G u v))
    (d : {d : Dart (contractLastEdgeGraph G u v) // d.vertex = v}) :
    (r.contractionRank d).val =
      if (contractionLift G u v d.val).vertex = v then
        r.rotationDistance (lastEdgeDart G u v true) (contractionLift G u v d.val) - 1
      else (Function.minimalPeriod r.rotate (lastEdgeDart G u v true) - 1) +
        (r.rotationDistance (lastEdgeDart G u v false) (contractionLift G u v d.val) - 1) := by
  unfold contractionRank contractionBlock
  split_ifs <;> rfl

/-- Within either source block, retained rank comparisons are original rank comparisons. -/
theorem contractionRank_lt_iff_sourceDistance_lt {G : Graph} {u v : ℕ}
    (r : RotationSystem (lastEdgeGraph G u v)) (huv : u ≠ v)
    (a b : {d : Dart (contractLastEdgeGraph G u v) // d.vertex = v}) (side : Bool)
    (ha : (contractionLift G u v a.val).vertex = (lastEdgeDart G u v side).vertex)
    (hb : (contractionLift G u v b.val).vertex = (lastEdgeDart G u v side).vertex) :
    (r.contractionRank a).val < (r.contractionRank b).val ↔
      r.rotationDistance (lastEdgeDart G u v side) (contractionLift G u v a.val) <
        r.rotationDistance (lastEdgeDart G u v side) (contractionLift G u v b.val) := by
  have hapos := r.rotationDistance_pos_of_ne _ _ ha.symm
    (contractionLift_ne_lastEdgeDart G u v a.val side)
  have hbpos := r.rotationDistance_pos_of_ne _ _ hb.symm
    (contractionLift_ne_lastEdgeDart G u v b.val side)
  rw [r.val_contractionRank, r.val_contractionRank]
  cases side
  · have hau : (contractionLift G u v a.val).vertex = u := by
      simpa only [vertex_lastEdgeDart, Bool.false_eq_true, ↓reduceIte] using ha
    have hbu : (contractionLift G u v b.val).vertex = u := by
      simpa only [vertex_lastEdgeDart, Bool.false_eq_true, ↓reduceIte] using hb
    rw [ite_eq_right (fun h => huv (hau.symm.trans h)),
      ite_eq_right (fun h => huv (hbu.symm.trans h))]
    omega
  · have hav : (contractionLift G u v a.val).vertex = v := by
      simpa only [vertex_lastEdgeDart, ↓reduceIte] using ha
    have hbv : (contractionLift G u v b.val).vertex = v := by
      simpa only [vertex_lastEdgeDart, ↓reduceIte] using hb
    rw [ite_eq_left hav, ite_eq_left hbv]
    omega

/-- Source block ranks are an equivalence onto one finite consecutive interval. -/
@[expose] noncomputable def contractionRankEquiv {G : Graph} {u v : ℕ}
    (r : RotationSystem (lastEdgeGraph G u v)) (huv : u ≠ v) :
    {d : Dart (contractLastEdgeGraph G u v) // d.vertex = v} ≃
      Fin ((Function.minimalPeriod r.rotate (lastEdgeDart G u v true) - 1) +
        (Function.minimalPeriod r.rotate (lastEdgeDart G u v false) - 1)) :=
  (r.contractionBlockEquiv huv).trans finSumFinEquiv

/-- The actual contracted rotation traverses the two original retained blocks
consecutively, in their original direction. Empty blocks are skipped automatically. -/
theorem val_contractionRank_rotate {G : Graph} {u v : ℕ}
    (r : RotationSystem (lastEdgeGraph G u v)) (huv : u ≠ v)
    (d : {d : Dart (contractLastEdgeGraph G u v) // d.vertex = v}) :
    let d' : {d : Dart (contractLastEdgeGraph G u v) // d.vertex = v} :=
      ⟨(r.contractLastEdge huv).rotate d.val, by rw [(r.contractLastEdge huv).vertex_rotate,
        d.property]⟩
    (r.contractionRank d').val = ((r.contractionRank d).val + 1) %
      ((Function.minimalPeriod r.rotate (lastEdgeDart G u v true) - 1) +
        (Function.minimalPeriod r.rotate (lastEdgeDart G u v false) - 1)) := by
  let d' : {d : Dart (contractLastEdgeGraph G u v) // d.vertex = v} :=
    ⟨(r.contractLastEdge huv).rotate d.val, by rw [(r.contractLastEdge huv).vertex_rotate,
      d.property]⟩
  let a := contractionLift G u v d.val
  let b := contractionLift G u v d'.val
  let oV := lastEdgeDart G u v true
  let oU := lastEdgeDart G u v false
  let nV := Function.minimalPeriod r.rotate oV - 1
  let nU := Function.minimalPeriod r.rotate oU - 1
  let k := (r.contractionRank d).val
  let l := (r.contractionRank d').val
  change l = (k + 1) % (nV + nU)
  have hk : k = if a.vertex = v then r.rotationDistance oV a - 1
      else nV + (r.rotationDistance oU a - 1) := r.val_contractionRank d
  have hl : l = if b.vertex = v then r.rotationDistance oV b - 1
      else nV + (r.rotationDistance oU b - 1) := r.val_contractionRank d'
  have hbl : l < nV + nU := (r.contractionRank d').isLt
  have hvV : oV.vertex = v := vertex_lastEdgeDart G u v true
  have hvU : oU.vertex = u := vertex_lastEdgeDart G u v false
  have haV : a ≠ oV := contractionLift_ne_lastEdgeDart G u v d.val true
  have haU : a ≠ oU := contractionLift_ne_lastEdgeDart G u v d.val false
  have hbV : b ≠ oV := contractionLift_ne_lastEdgeDart G u v d'.val true
  have hbU : b ≠ oU := contractionLift_ne_lastEdgeDart G u v d'.val false
  have vrot {x y : Dart (lastEdgeGraph G u v)} (h : r.rotate x = y) : x.vertex = y.vertex :=
    (r.vertex_rotate x).symm.trans (congrArg Dart.vertex h)
  have first {o : Dart (lastEdgeGraph G u v)} (h' : r.rotate o = b) (hb : b ≠ o) :
      r.rotationDistance o b = 1 := by
    simpa only [h', r.rotationDistance_self, zero_add] using
      r.rotationDistance_rotate_of_ne o o rfl (h' ▸ hb)
  have next (h : l = k + 1) : l = (k + 1) % (nV + nU) := by
    rw [← h, Nat.mod_eq_of_lt hbl]
  have wrap (h : k + 1 = nV + nU) (hzero : l = 0) : l = (k + 1) % (nV + nU) := by
    rw [h, Nat.mod_self, hzero]
  have lastDist {o : Dart (lastEdgeGraph G u v)} (hoa : o.vertex = a.vertex) (ha : a ≠ o)
      (h : r.rotate a = o) :
      r.rotationDistance o a - 1 + 1 = Function.minimalPeriod r.rotate o - 1 := by
    have hlast := r.rotationDistance_of_rotate_eq o a hoa h
    have hpos := r.rotationDistance_pos_of_ne o a hoa ha
    omega
  rcases r.contractionLift_rotate_cases huv d.val with h | ⟨h, h'⟩ | ⟨h, h'⟩ |
    ⟨h, hfix, h'⟩ | ⟨h, hfix, h'⟩
  · have hab := vrot h
    change r.rotate a = b at h
    by_cases hav : a.vertex = v
    · have hbv : b.vertex = v := hab.symm.trans hav
      have hoa : oV.vertex = a.vertex := hvV.trans hav.symm
      have hsucc := h ▸ r.rotationDistance_rotate_of_ne oV a hoa (h ▸ hbV)
      have hpos := r.rotationDistance_pos_of_ne oV a hoa haV
      simp only [ite_eq_left hav, ite_eq_left hbv] at hk hl
      exact next (by omega)
    · have hau : a.vertex = u := ((contractionLift_vertex_eq_iff G u v d.val).mp
        d.property).resolve_right hav
      have hbv : b.vertex ≠ v := fun heq => hav (hab.trans heq)
      have hoa : oU.vertex = a.vertex := hvU.trans hau.symm
      have hsucc := h ▸ r.rotationDistance_rotate_of_ne oU a hoa (h ▸ hbU)
      have hpos := r.rotationDistance_pos_of_ne oU a hoa haU
      simp only [ite_eq_right hav, ite_eq_right hbv] at hk hl
      exact next (by omega)
  · have hav : a.vertex = v := (vrot h).trans hvV
    have hbu : b.vertex = u := (vrot h').symm.trans hvU
    have hbv : b.vertex ≠ v := fun heq => huv (hbu.symm.trans heq)
    have hlast := lastDist (hvV.trans hav.symm) haV h
    have hfirst := first h' hbU
    simp only [ite_eq_left hav, ite_eq_right hbv] at hk hl
    dsimp only [nV, nU, oV, oU] at *
    exact next (by omega)
  · have hau : a.vertex = u := (vrot h).trans hvU
    have hav : a.vertex ≠ v := fun heq => huv (hau.symm.trans heq)
    have hbv : b.vertex = v := (vrot h').symm.trans hvV
    have hlast := lastDist (hvU.trans hau.symm) haU h
    have hfirst := first h' hbV
    simp only [ite_eq_right hav, ite_eq_left hbv] at hk hl
    dsimp only [nV, nU, oV, oU] at *
    exact wrap (by omega) (by omega)
  · have hav : a.vertex = v := (vrot h).trans hvV
    have hbv : b.vertex = v := (vrot h').symm.trans hvV
    have hlast := lastDist (hvV.trans hav.symm) haV h
    have hfirst := first h' hbV
    have hU : nU = 0 := by simp [nU, oU, Function.minimalPeriod_eq_one_iff_isFixedPt.mpr hfix]
    simp only [ite_eq_left hav, ite_eq_left hbv] at hk hl
    dsimp only [nV, nU, oV, oU] at *
    exact wrap (by omega) (by omega)
  · have hau : a.vertex = u := (vrot h).trans hvU
    have hav : a.vertex ≠ v := fun heq => huv (hau.symm.trans heq)
    have hbu : b.vertex = u := (vrot h').symm.trans hvU
    have hbv : b.vertex ≠ v := fun heq => huv (hbu.symm.trans heq)
    have hlast := lastDist (hvU.trans hau.symm) haU h
    have hfirst := first h' hbU
    have hV : nV = 0 := by simp [nV, oV, Function.minimalPeriod_eq_one_iff_isFixedPt.mpr hfix]
    simp only [ite_eq_right hav, ite_eq_right hbv] at hk hl
    dsimp only [nV, nU, oV, oU] at *
    exact wrap (by omega) (by omega)

/-- Whenever the contracted vertex has a retained dart, its block rank zero is an
actual cycle origin, and all first-hit distances from it are the consecutive block ranks. -/
theorem exists_contractionRank_origin {G : Graph} {u v : ℕ}
    (r : RotationSystem (lastEdgeGraph G u v)) (huv : u ≠ v)
    (a : {d : Dart (contractLastEdgeGraph G u v) // d.vertex = v}) :
    ∃ o : {d : Dart (contractLastEdgeGraph G u v) // d.vertex = v},
      ∀ d : {d : Dart (contractLastEdgeGraph G u v) // d.vertex = v},
        (r.contractLastEdge huv).rotationDistance o.val d.val = (r.contractionRank d).val := by
  let N := (Function.minimalPeriod r.rotate (lastEdgeDart G u v true) - 1) +
    (Function.minimalPeriod r.rotate (lastEdgeDart G u v false) - 1)
  let s := r.contractLastEdge huv
  let S : Equiv.Perm {d : Dart (contractLastEdgeGraph G u v) // d.vertex = v} :=
    s.rotate.subtypePerm (fun d => by rw [s.vertex_rotate])
  have hN : 0 < N := (Nat.zero_le _).trans_lt (r.contractionRank a).isLt
  let o := (r.contractionRankEquiv huv).symm ⟨0, hN⟩
  have hinj : Function.Injective r.contractionRank :=
    finSumFinEquiv.injective.comp r.contractionBlock_injective
  have ho : (r.contractionRank o).val = 0 :=
    congrArg Fin.val ((r.contractionRankEquiv huv).apply_symm_apply ⟨0, hN⟩)
  have hstep (d) : (r.contractionRank (S d)).val = ((r.contractionRank d).val + 1) % N :=
    r.val_contractionRank_rotate huv d
  have hpow (n : ℕ) (d) : (r.contractionRank ((S ^ n) d)).val =
      ((r.contractionRank d).val + n) % N := by
    induction n with
    | zero =>
      simpa only [pow_zero, Equiv.Perm.one_apply, add_zero] using
        (Nat.mod_eq_of_lt (r.contractionRank d).isLt).symm
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, hstep, ih, Nat.mod_add_mod, Nat.add_assoc]
  have hval (n : ℕ) (d) : ((S ^ n) d).val = (s.rotate ^ n) d.val := by
    rw [Equiv.Perm.subtypePerm_pow]; rfl
  refine ⟨o, fun d => s.rotationDistance_eq o.val d.val (o.property.trans d.property.symm)
    (r.contractionRank d).val ?_ ?_⟩
  · refine (hval _ o).symm.trans (congrArg Subtype.val (hinj (Fin.ext ?_)))
    rw [hpow, ho, zero_add, Nat.mod_eq_of_lt (r.contractionRank d).isLt]
  · intro k hk heq
    have heq' : (S ^ k) o = d := Subtype.ext ((hval k o).trans heq)
    have hrank := congrArg (fun d => (r.contractionRank d).val) heq'
    rw [hpow, ho, zero_add, Nat.mod_eq_of_lt (hk.trans (r.contractionRank d).isLt)] at hrank
    omega

/-- The literal contracted rotation interval is precisely the cyclic order of the
two consecutive retained source blocks. Both empty-block conventions are internal. -/
theorem mem_rotationInterval_contractLastEdge_iff_ranks {G : Graph} {u v : ℕ}
    (r : RotationSystem (lastEdgeGraph G u v)) (huv : u ≠ v)
    (a b c : {d : Dart (contractLastEdgeGraph G u v) // d.vertex = v})
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    b.val ∈ (r.contractLastEdge huv).rotationInterval a.val c.val ↔
      ((r.contractionRank a).val < (r.contractionRank b).val ∧
        (r.contractionRank b).val < (r.contractionRank c).val) ∨
      ((r.contractionRank b).val < (r.contractionRank c).val ∧
        (r.contractionRank c).val < (r.contractionRank a).val) ∨
      ((r.contractionRank c).val < (r.contractionRank a).val ∧
        (r.contractionRank a).val < (r.contractionRank b).val) := by
  obtain ⟨o, ho⟩ := r.exists_contractionRank_origin huv a
  have h := (r.contractLastEdge huv).mem_rotationInterval_iff_ranks o.val a.val b.val c.val
    (o.property.trans a.property.symm) (o.property.trans b.property.symm)
    (o.property.trans c.property.symm) (fun h => hab (Subtype.ext h))
    (fun h => hbc (Subtype.ext h)) (fun h => hac (Subtype.ext h))
  simpa only [ho] using h

end Cslib.Complexity.Graph.RotationSystem
