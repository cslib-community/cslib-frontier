/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.BoundaryTransport

/-!
# Adjacent identification inside an ordered boundary

Positive cyclic transport exposes a selected adjacent pair and restores the exact inherited
survivor word. The actual body is relabeled once by the prescribed quotient map. No body
degree, distinctness, connectedness, or occurrence requirement is imposed.
-/

public section

namespace Cslib.Complexity.CSP.OrderedBoundary

open Cslib.Logic.PL

variable {Rel V W : Type} [DecidableEq V] [DecidableEq W]

/-- Identify an adjacent pair after any initial block, deleting its first marker and
retaining the exact mapped order of all other markers. The selected-pair kernel is needed
only on occurring and boundary names; unused names are unrestricted. -/
noncomputable def Witness.identifyMiddle {F : CSP Rel V} {left right : List V} {x y : V}
    (w : Witness F (left ++ x :: y :: right)) (f : V → W)
    (hn : (left ++ x :: y :: right).Nodup) (hxy : x ≠ y)
    (hk : ∀ a ∈ F.vars ++ (left ++ x :: y :: right),
      ∀ b ∈ F.vars ++ (left ++ x :: y :: right),
        f a = f b ↔ Function.update id y x a = Function.update id y x b)
    (ht : ((left ++ y :: right).map f).Nodup) :
    Witness (F.relabel f) ((left ++ y :: right).map f) := by
  let wr := w.rotateAppend hn
  let wr' : Witness F (x :: y :: (right ++ left)) :=
    ⟨wr.certificate, by simpa only [List.cons_append] using wr.accepted⟩
  have hperm : (left ++ y :: right).Perm (y :: (right ++ left)) := by
    simpa only [List.cons_append] using List.perm_append_comm (l₁ := left) (l₂ := y :: right)
  let h := wr'.identifyHead f hxy (by
    intro a ha b hb
    exact hk a (by
      simpa only [List.mem_append, List.mem_cons, or_assoc, or_comm, or_left_comm] using ha)
      b (by
        simpa only [List.mem_append, List.mem_cons, or_assoc, or_comm, or_left_comm] using hb))
    (ht.perm (hperm.map f))
  let h' : Witness (F.relabel f) ((y :: right).map f ++ left.map f) :=
    ⟨h.certificate, by
      simpa only [List.map_append, List.map_cons, List.cons_append] using h.accepted⟩
  let out := h'.rotateAppend (by
    simpa only [List.map_append, List.map_cons, List.cons_append] using ht.perm (hperm.map f))
  exact ⟨out.certificate, by simpa only [List.map_append] using out.accepted⟩

/-- Identify the last and first boundary markers, deleting the last marker. This is the
wrap convention: the first marker and the inherited order of its tail survive literally. -/
noncomputable def Witness.identifyWrap {F : CSP Rel V} {middle : List V} {x y : V}
    (w : Witness F ((y :: middle) ++ [x])) (f : V → W)
    (hn : ((y :: middle) ++ [x]).Nodup) (hxy : x ≠ y)
    (hk : ∀ a ∈ F.vars ++ ((y :: middle) ++ [x]),
      ∀ b ∈ F.vars ++ ((y :: middle) ++ [x]),
        f a = f b ↔ Function.update id y x a = Function.update id y x b)
    (ht : ((y :: middle).map f).Nodup) :
    Witness (F.relabel f) ((y :: middle).map f) := by
  let wr := w.rotateAppend hn
  let wr' : Witness F (x :: y :: middle) :=
    ⟨wr.certificate, by simpa only [List.singleton_append] using wr.accepted⟩
  exact wr'.identifyHead f hxy (by
    intro a ha b hb
    exact hk a (by
      simpa only [List.mem_append, List.mem_cons, List.mem_singleton,
        List.not_mem_nil, or_false, false_or, or_assoc, or_comm, or_left_comm] using ha)
      b (by
        simpa only [List.mem_append, List.mem_cons, List.mem_singleton,
          List.not_mem_nil, or_false, false_or, or_assoc, or_comm, or_left_comm] using hb)) ht

/-- Identify any nonwrapping adjacent pair, deleting exactly its first list position.
Both selected positions must exist. Boundary names are distinct; body occurrences may repeat.
The resulting boundary is the literal mapped `eraseIdx`, with no survivor permutation. -/
noncomputable def Witness.identifyAt {F : CSP Rel V} {ports : List V}
    (w : Witness F ports) (f : V → W) (i : ℕ) (hi : i + 1 < ports.length)
    (hn : ports.Nodup)
    (hk : ∀ a ∈ F.vars ++ ports, ∀ b ∈ F.vars ++ ports,
      f a = f b ↔ Function.update id ports[i + 1] ports[i] a =
        Function.update id ports[i + 1] ports[i] b)
    (ht : ((ports.eraseIdx i).map f).Nodup) :
    Witness (F.relabel f) ((ports.eraseIdx i).map f) := by
  have hi' : i < ports.length := by omega
  let left := ports.take i
  let right := ports.drop (i + 2)
  have hword : left ++ ports[i] :: ports[i + 1] :: right = ports := by
    change ports.take i ++ ports[i] :: ports[i + 1] :: ports.drop (i + 1 + 1) = ports
    rw [← List.drop_eq_getElem_cons hi, ← List.drop_eq_getElem_cons hi', List.take_append_drop]
  have hsurvivor : left ++ ports[i + 1] :: right = ports.eraseIdx i := by
    rw [List.eraseIdx_eq_take_drop_succ, List.drop_eq_getElem_cons hi]
  let w' : Witness F (left ++ ports[i] :: ports[i + 1] :: right) :=
    ⟨w.certificate, by rw [hword]; exact w.accepted⟩
  have hxy : ports[i] ≠ ports[i + 1] := by
    intro he
    have := hn.eq_of_getElem_eq hi' hi he
    omega
  let h := w'.identifyMiddle f (by rw [hword]; exact hn) hxy
    (by rw [hword]; exact hk) (by rw [hsurvivor]; exact ht)
  exact ⟨h.certificate, by rw [← hsurvivor]; exact h.accepted⟩

end Cslib.Complexity.CSP.OrderedBoundary
