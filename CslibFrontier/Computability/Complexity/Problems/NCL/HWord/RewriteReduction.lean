/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.Problem
public import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.RewriteEquivalence
public import CslibFrontier.Computability.Complexity.Reduction
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Polynomial-time reduction from fixed source rewriting to fixed H-words

The compiler zips adjacent source letters and inserts the two end markers. Empty pairs map to a
constant accepting instance; words of different lengths map to a constant rejecting instance.
Both languages use the standard framed encoding of two lists over fixed finite alphabets.

## Main definitions

* `HWord.RewriteGadget.sourceLanguage`: reachability for the standard semi-Thue relation.
* `HWord.RewriteGadget.toHWord`: the total canonical list compiler.

## Main results

* `HWord.RewriteGadget.polyTimeReducible_sourceLanguage`: the standard polynomial-time reduction.

## References

* [M. Wrochna, *Reconfiguration in bounded bandwidth and treedepth*][Wrochna2014],
  arXiv:1405.0847v1, Section 3, proof of Theorem 3.
-/

public section

namespace Cslib.Complexity.NCL.HWord.RewriteGadget

open Cslib.PostCorrespondence _root_.Turing.MultiTapeTM

variable {q r : ℕ}

/-- Reachability under the fixed symmetric family of two-letter source rules. -/
@[expose] def sourceLanguage (rules : Fin r → Rule q) : Set (Instance q) :=
  {x | Relation.ReflTransGen (Rewrites (RuleSet rules)) x.source x.target}

private noncomputable def yesInstance : Instance (Fintype.card (Symbol q r)) :=
  ⟨[code .start], [code .start]⟩

private noncomputable def noInstance : Instance (Fintype.card (Symbol q r)) :=
  ⟨[code .start, code .start], [code .start, code .start]⟩

/-- Compile all source instances into the same fixed target alphabet. -/
noncomputable def toHWord (x : Instance q) : Instance (Fintype.card (Symbol q r)) :=
  if x.source.isEmpty then
    if x.target.isEmpty then yesInstance else noInstance
  else if x.source.length == x.target.length then
    ⟨wordList x.source, wordList x.target⟩
  else noInstance

private theorem yesInstance_mem (rules : Fin r → Rule q) :
    yesInstance ∈ language (compatibility rules) := by
  have hw : List.ofFn (fun _ : Fin 1 => (code .start : Fin (Fintype.card (Symbol q r)))) =
      [code .start] := by simp [List.ofFn_succ]
  unfold yesInstance
  rw [← hw, language_ofFn]
  refine ⟨fun i j _ => ?_, .refl⟩
  have := i.isLt
  have := j.isLt
  omega

private theorem noInstance_not_mem (rules : Fin r → Rule q) :
    noInstance ∉ language (compatibility rules) := by
  rintro ⟨_, _, hlegal, _⟩
  unfold noInstance at hlegal
  exact (compatibility_adj rules .start .start).mp (hlegal 0 1 rfl)

private theorem wordList_mem_iff (rules : Fin r → Rule q) (s t : List (Fin q))
    (hne : 0 < s.length) (hlen : s.length = t.length) :
    Instance.mk (wordList s) (wordList t) ∈ language (compatibility rules) ↔
      Relation.ReflTransGen (Rewrites (RuleSet rules)) s t := by
  induction s using List.ofFnRec with
  | h n s =>
    induction t using List.ofFnRec with
    | h m t =>
      simp only [List.length_ofFn] at hne hlen
      subst m
      rw [wordList_ofFn, wordList_ofFn, language_ofFn]
      exact (and_iff_right (word_legal rules s hne)).trans (word_reachable_iff rules hne s t)

/-- The total list compiler preserves and reflects source reachability on every input. -/
theorem toHWord_mem_iff (rules : Fin r → Rule q) (x : Instance q) :
    toHWord (r := r) x ∈ language (compatibility rules) ↔ x ∈ sourceLanguage rules := by
  by_cases hs : x.source.isEmpty
  · have hs' : x.source = [] := List.isEmpty_iff.mp hs
    by_cases ht : x.target.isEmpty
    · simp only [toHWord, hs', List.isEmpty_iff.mp ht, List.isEmpty_nil, ite_true,
        sourceLanguage, Set.mem_ofPred_eq]
      exact ⟨fun _ => .refl, fun _ => yesInstance_mem rules⟩
    · have hnot : x ∉ sourceLanguage rules := fun hr => ht <| List.isEmpty_iff.mpr <|
        List.length_eq_zero_iff.mp (by simpa [hs'] using source_path_length rules hr)
      simp [toHWord, hs, ht, noInstance_not_mem rules, hnot]
  · by_cases hlen : x.source.length = x.target.length
    · have hn : 0 < x.source.length :=
        List.length_pos_iff.mpr fun h => hs (List.isEmpty_iff.mpr h)
      simpa only [toHWord, hs, Bool.false_eq_true, ite_false, hlen, beq_self_eq_true, ite_true,
        sourceLanguage, Set.mem_ofPred_eq] using wordList_mem_iff rules x.source x.target hn hlen
    · have hnot : x ∉ sourceLanguage rules := fun hr =>
        hlen (source_path_length rules hr).symm
      simp [toHWord, hs, hlen, noInstance_not_mem rules, hnot]

/-- The canonical word compiler uses polynomial-time list operations and a fixed finite table. -/
@[fun_prop]
theorem computableInPolyTime_wordList :
    ComputableInPolyTime (wordList (q := q) (r := r)) (encWord q)
      (encWord (Fintype.card (Symbol q r))) := by
  have hs : ComputableInPolyTime (List.map (some : Fin q → Option (Fin q))) (encWord q)
      (encList (encOption (encFinEnum (Fin q)))) :=
    (ComputableInPolyTime.of_finite _).map
  have hp : ComputableInPolyTime
      (fun p : Option (Fin q) × Option (Fin q) => (code (.pair p.1 p.2) :
        Fin (Fintype.card (Symbol q r))))
      (encPair (encOption (encFinEnum (Fin q))) (encOption (encFinEnum (Fin q))))
      (encFinEnum (Fin (Fintype.card (Symbol q r)))) := .of_finite _
  have hz := (ComputableInPolyTime.zip _ _).comp
    (((ComputableInPolyTime.const none).cons' hs).prod
      (hs.listAppend' (ComputableInPolyTime.const [none])))
  exact ((ComputableInPolyTime.const (code .start)).cons' (hp.map.comp hz)).listAppend'
    (ComputableInPolyTime.const [code .finish])

/-- The total instance compiler is polynomial-time under the standard two-list encodings. -/
@[fun_prop]
theorem computableInPolyTime_toHWord :
    ComputableInPolyTime (toHWord (q := q) (r := r)) (encInstance q)
      (encInstance (Fintype.card (Symbol q r))) := by
  unfold toHWord
  fun_prop

/-- Fixed source rewriting reduces to the fixed compatibility graph in standard polynomial time. -/
theorem polyTimeReducible_sourceLanguage (rules : Fin r → Rule q) :
    PolyTimeReducible (encInstance q) (encInstance (Fintype.card (Symbol q r)))
      (sourceLanguage rules) (language (compatibility rules)) :=
  ⟨toHWord, computableInPolyTime_toHWord, fun x => (toHWord_mem_iff rules x).symm⟩

end Cslib.Complexity.NCL.HWord.RewriteGadget
