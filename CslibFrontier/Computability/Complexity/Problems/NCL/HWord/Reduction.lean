/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.Problem
public import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.Planarized
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.PlaneWord.Reachability
import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.Metadata.Input
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Mathlib.Data.List.GetD

/-!
# The actual H-word to planar AND/OR instance map

The shared two-list H-word input determines a closed standard planar word and its canonical
initial and target configurations. Different endpoint lengths map to a fixed rejected input.

## Main definitions

* `HWord.Planarized.reduce`: the total instance map.

## Main results

* `HWord.Planarized.reduce_mem_iff`: exact correctness for the standard input languages.
* `HWord.Planarized.computableInPolyTime_reduce`: standard encoded polynomial-time reduction.
-/

public section

namespace Cslib.Complexity.NCL.HWord.Planarized

open _root_.Turing.MultiTapeTM

variable {q : ℕ} (H : Digraph (Fin q)) [DecidableRel H.Adj] (hq : 0 < q)

private def targetWord (x : Instance q) : Fin x.source.length → Fin q :=
  fun i => x.target.getD i.val ⟨0, hq⟩

private theorem ofFn_targetWord (x : Instance q) (h : x.source.length = x.target.length) :
    List.ofFn (targetWord hq x) = x.target := by
  apply List.ext_getElem
  · exact List.length_ofFn.trans h
  · intro i hi hj
    simp only [List.getElem_ofFn, targetWord]
    exact List.getD_eq_getElem _ _ hj

omit [DecidableRel H.Adj] in
private theorem language_iff (x : Instance q) : x ∈ language H ↔
    x.source.length = x.target.length ∧ Legal H x.source.get ∧
      Reachable H x.source.get (targetWord hq x) := by
  constructor
  · rintro ⟨t, ht, hs, hr⟩
    have hlen : x.source.length = x.target.length := List.length_ofFn.symm.trans
      (congrArg List.length ht)
    have heq : t = targetWord hq x := List.ofFn_inj.mp (ht.trans (ofFn_targetWord hq x hlen).symm)
    exact ⟨hlen, hs, heq ▸ hr⟩
  · rintro ⟨hlen, hs, hr⟩
    exact ⟨targetWord hq x, ofFn_targetWord hq x hlen, hs, hr⟩

private def rejected : PlaneWordAndOrNCL.Instance := ⟨[], [], [true]⟩

private theorem rejected_not_mem : rejected ∉ PlaneWordAndOrNCL := by
  intro h
  have hlen := h.2.2.2.2.1
  change 1 = 0 at hlen
  omega

/-- Compile the shared two-list H-word instance into the actual standard planar NCL instance. -/
def reduce (x : Instance q) : PlaneWordAndOrNCL.Instance :=
  if x.source.length = x.target.length then
    ⟨word (n := x.source.length) H hq, bits H hq x.source.get, bits H hq (targetWord hq x)⟩
  else rejected

/-- Equal-length endpoints use the actual planar word and its canonical configurations. -/
theorem reduce_of_length_eq (x : Instance q) (h : x.source.length = x.target.length) :
    reduce H hq x = ⟨word (n := x.source.length) H hq, bits H hq x.source.get,
      bits H hq (fun i : Fin x.source.length => x.target.getD i.val ⟨0, hq⟩)⟩ :=
  ite_eq_left h

/-- Every source input emits a word passing the plane-layer check. -/
theorem checkPlane_reduce (x : Instance q) : (reduce H hq x).word.checkPlane = true := by
  unfold reduce
  split
  · exact checkPlane_word H hq
  · rfl

/-- Every source input emits a closed well-typed word. -/
theorem wellTyped_reduce (x : Instance q) : (reduce H hq x).word.WellTyped [] [] := by
  unfold reduce
  split
  · exact wellTyped_word H hq
  · rfl

/-- The actual total instance map preserves and reflects the shared H-word language. -/
theorem reduce_mem_iff (x : Instance q) : reduce H hq x ∈ PlaneWordAndOrNCL ↔ x ∈ language H := by
  rw [language_iff H hq]
  by_cases hlen : x.source.length = x.target.length
  · rw [reduce, ite_eq_left hlen]
    change (word H hq).checkPlane = true ∧ (word H hq).WellTyped [] [] ∧ _ ↔ _
    rw [and_iff_right (checkPlane_word H hq), and_iff_right (wellTyped_word H hq),
      mem_compile_iff H hq, and_iff_right hlen]
  · rw [reduce, ite_eq_right hlen]
    exact iff_of_false rejected_not_mem (fun h => hlen h.1)

/-- The actual H-word to plane-word instance map is polynomial-time in the shared encodings. -/
theorem computableInPolyTime_reduce : ComputableInPolyTime (reduce H hq) (encInstance q)
    encPlaneWordAndOrNCL := by
  have hs := encInstance_source_polyTime q
    (ComputableInPolyTime.id' (encIn := encInstance q))
  have ht := encInstance_target_polyTime q
    (ComputableInPolyTime.id' (encIn := encInstance q))
  have htest : ComputableInPolyTime (fun x : Instance q =>
      decide (x.source.length = x.target.length)) (encInstance q) encBool := by fun_prop
  have hcompile : ComputableInPolyTime (fun x : Instance q =>
      Planar.Embedding.PolyTime.compile (Metadata.toInput H hq x)) (encInstance q)
      encPlaneWordAndOrNCL := by
    simpa only [Function.comp_def] using Planar.Embedding.PolyTime.computableInPolyTime_compile.comp
      (Metadata.computableInPolyTime_toInput H hq)
  have h := ComputableInPolyTime.ite_decide htest hcompile (ComputableInPolyTime.const rejected)
  apply h.of_enc_eq
  intro x
  by_cases hlen : x.source.length = x.target.length
  · simp only [reduce, hlen, ite_true, Metadata.compile_toInput]
    rfl
  · simp only [reduce, hlen, ite_false]

end Cslib.Complexity.NCL.HWord.Planarized
