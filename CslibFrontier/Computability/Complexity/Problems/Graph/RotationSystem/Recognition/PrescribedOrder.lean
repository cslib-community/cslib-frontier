/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.Input
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.IntervalOrder
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup

/-! # Directed intervals of prescribed rotations

A complete word fixes the successor at every dart of its vertex. Starting at the first entry,
the actual rotation reaches each indexed occurrence at its word position. This identifies
the rotation's directed intervals with cyclic comparison in the word.
-/

public section

namespace Cslib.Complexity.Graph.RotationRecognition

/-- A dart in a prescribed complete word has that word's center. -/
theorem fixedWord_dart_vertex {I : FixedRotationInput} (hI : Valid I) {v : ℕ}
    {word : List ℕ} (hw : I.orders.getD v none = some word)
    {d : Dart I.graph} (hd : d.index ∈ word) : d.vertex = v := by
  have hf := (hI.2.2.2 v word hw).2 d.index |>.mp hd
  exact (Dart.vertex_index d).symm.trans (mem_fiber.mp hf).2

/-- At a prescribed vertex, a realizing rotation's directed intervals are exactly the
literal cyclic order of the prescribed indexed word. The three darts must be distinct. -/
theorem Realizes.mem_rotationInterval_iff_fixedWord {I : FixedRotationInput}
    {r : RotationSystem I.graph} (hfixed : Realizes I r) (hI : Valid I)
    {v : ℕ} {word : List ℕ} (hw : I.orders.getD v none = some word)
    {a b c : Dart I.graph} (ha : a.index ∈ word) (hb : b.index ∈ word) (hc : c.index ∈ word)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    b ∈ r.rotationInterval a c ↔
      (word.idxOf a.index < word.idxOf b.index ∧ word.idxOf b.index < word.idxOf c.index) ∨
      (word.idxOf b.index < word.idxOf c.index ∧ word.idxOf c.index < word.idxOf a.index) ∨
      (word.idxOf c.index < word.idxOf a.index ∧ word.idxOf a.index < word.idxOf b.index) := by
  have hnonempty : 0 < word.length := List.length_pos_of_mem ha
  have hfirst : word[0] ∈ word := List.getElem_mem hnonempty
  have hbound : word[0] < 2 * I.graph.edges.length :=
    (mem_fiber.mp (((hI.2.2.2 v word hw).2 _).mp hfirst)).1
  let first : Dart I.graph := (Dart.indexEquiv I.graph).symm ⟨word[0], hbound⟩
  have hstart : first.index = word[0] :=
    congrArg Fin.val ((Dart.indexEquiv I.graph).apply_symm_apply ⟨word[0], hbound⟩)
  have hfirstv : first.vertex = v := fixedWord_dart_vertex hI hw (hstart.symm ▸ hfirst)
  have hiterate (i : ℕ) (hi : i < word.length) : ((r.rotate ^ i) first).index = word[i] := by
    induction i with
    | zero => exact hstart
    | succ i ih =>
      have hi' : i < word.length := Nat.lt_of_succ_lt hi
      rw [pow_succ', Equiv.Perm.mul_apply]
      rw [hfixed v word hw i hi' _ (by rw [List.getD_eq_getElem _ _ hi']; exact ih hi')]
      simp only [nextInWord, hi, ite_true, List.getD_eq_getElem _ _ hi]
  have hrank (d : Dart I.graph) (hd : d.index ∈ word) :
      r.rotationDistance first d = word.idxOf d.index := by
    have hi := List.idxOf_lt_length_of_mem hd
    apply r.rotationDistance_eq first d (hfirstv.trans (fixedWord_dart_vertex hI hw hd).symm)
    · apply (Dart.indexEquiv I.graph).injective
      exact Fin.ext ((hiterate _ hi).trans (List.getElem_idxOf hi))
    · intro j hj heq
      have hh := (hiterate j (hj.trans hi)).symm.trans (congrArg Dart.index heq)
      have he := (hI.2.2.2 v word hw).1.idxOf_getElem j (hj.trans hi)
      rw [hh] at he
      exact (Nat.ne_of_lt hj) he.symm
  have hv {d : Dart I.graph} (hd : d.index ∈ word) : first.vertex = d.vertex :=
    hfirstv.trans (fixedWord_dart_vertex hI hw hd).symm
  rw [r.mem_rotationInterval_iff_ranks first a b c (hv ha) (hv hb) (hv hc) hab hbc hac,
    hrank a ha, hrank b hb, hrank c hc]

end Cslib.Complexity.Graph.RotationRecognition
