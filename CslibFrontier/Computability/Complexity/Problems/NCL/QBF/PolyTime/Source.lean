/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.Normalize
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Polynomial-time source preprocessing

Generate the quantifier list and literal masks from upstream alternating prenex CNF data.
An indexed mask scan connects each variable name only at its innermost binding position.
The list index and lookup operations supply its polynomial-time bound.

## Main definitions

* `Cslib.Complexity.NCL.QBF.Source.encQuantifier`: one bit for each quantifier kind.
* `Cslib.Complexity.NCL.QBF.Source.prepare`: normalized quantifiers and literal masks.

## Main results

* `Cslib.Complexity.NCL.QBF.Source.computableInPolyTime_clauseMask`: the shadowing-aware scan.
* `Cslib.Complexity.NCL.QBF.Source.computableInPolyTime_prepare`: the complete frontend.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.QBF.Source

open Cslib.Logic.PL Cslib.Logic.PL.QBF _root_.Turing.MultiTapeTM

/-- A quantifier kind encoded by a single Boolean symbol. -/
@[expose] def encQuantifier : Quantifier ↪ List Bool where
  toFun
    | .ex => [false]
    | .all => [true]
  inj' := by intro a b h; cases a <;> cases b <;> simp_all

/-- The prepared prefix and mask matrix use framed lists of quantifier and Boolean symbols. -/
@[expose] def encPrepared : (List Quantifier × List (List Bool)) ↪ List Bool :=
  encPair (encList encQuantifier) (encList (encList encBool))

/-- Prepare the normalized source's prefix and matrix masks for circuit emission. -/
@[expose] def prepare (x : PrenexCNF) : List Quantifier × List (List Bool) :=
  (quantifiers (normalize x).rounds, masks (normalize x).rounds (normalize x).matrix)

private abbrev clauseEncoding := encList (encPair encNat encBool)

private theorem clauseMask_eq_zipIdx (vs : List ℕ) (c : Clause ℕ) :
    clauseMask vs c = vs.zipIdx.flatMap (fun ⟨v, i⟩ =>
      [decide (vs.idxOf v = i) && c.contains (v, true),
        decide (vs.idxOf v = i) && c.contains (v, false)]) := by
  induction vs generalizing c with
  | nil => rfl
  | cons v vs ih =>
    simp only [clauseMask, List.zipIdx_cons', List.flatMap_cons,
      List.idxOf_cons_self, decide_true, Bool.true_and, List.cons_append,
      List.nil_append, ih, List.flatMap_map]
    refine congrArg (_ :: _ :: ·) (List.flatMap_congr fun ⟨w, i⟩ _ => ?_)
    by_cases h : w = v
    · subst w
      simp [List.idxOf_cons_self, List.mem_filter]
    · simp [h, Ne.symm h, List.mem_filter]

/-- Literal masks with shadowed names are computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_clauseMask {α : Type} {input : α ↪ List Bool}
    {vs : α → List ℕ} {c : α → Clause ℕ}
    (hv : ComputableInPolyTime vs input (encList encNat))
    (hc : ComputableInPolyTime c input (encList (encPair encNat encBool))) :
    ComputableInPolyTime (fun x => clauseMask (vs x) (c x)) input (encList encBool) := by
  have hz := (ComputableInPolyTime.zipIdx encNat).comp hv
  have hp := ComputableInPolyTime.fst input (encPair encNat encUnary)
  have hw : ComputableInPolyTime (fun p : α × (ℕ × ℕ) => p.2.1)
      (encPair input (encPair encNat encUnary)) encNat := by fun_prop
  have hi : ComputableInPolyTime (fun p : α × (ℕ × ℕ) => p.2.2)
      (encPair input (encPair encNat encUnary)) encUnary := by fun_prop
  have hfirst := (ComputableInPolyTime.idxOfWithInput (hv.comp hp) hw).decide_eq' hi
  have hb (b : Bool) : ComputableInPolyTime
      (fun p : α × (ℕ × ℕ) => (c p.1).contains (p.2.1, b))
      (encPair input (encPair encNat encUnary)) encBool := by
    have he : ComputableInPolyTime (fun p : ℕ × (ℕ × Bool) => (p.1, b) == p.2)
        (encPair encNat (encPair encNat encBool)) encBool :=
      ComputableInPolyTime.beq
        (show ComputableInPolyTime (fun p : ℕ × (ℕ × Bool) => (p.1, b))
          (encPair encNat (encPair encNat encBool)) (encPair encNat encBool) by fun_prop)
        (ComputableInPolyTime.snd encNat (encPair encNat encBool))
    simpa only [List.contains_eq_any_beq, Function.comp_def] using
      ComputableInPolyTime.anyWithEncoding he hw (hc.comp hp)
  simpa only [clauseMask_eq_zipIdx, Function.comp_def] using
    ComputableInPolyTime.flatMapWithInput hz
      ((hfirst.bool_and' (hb true)).cons'
        ((hfirst.bool_and' (hb false)).cons' (ComputableInPolyTime.const [])))

private theorem quantifiers_eq_flatMap (ps : List (ℕ × ℕ)) :
    quantifiers ps = ps.flatMap (fun _ => [Quantifier.ex, Quantifier.all]) := by
  induction ps with
  | nil => rfl
  | cons _ _ ih => simp [quantifiers, ih]

/-- Every upstream round emits its existential and universal quantifiers in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_quantifiers :
    ComputableInPolyTime (fun ps : List (ℕ × ℕ) => quantifiers ps)
      (encList (encPair encNat encNat)) (encList encQuantifier) := by
  simpa only [← quantifiers_eq_flatMap] using
    (show ComputableInPolyTime
      (fun ps : List (ℕ × ℕ) => ps.flatMap fun _ => [Quantifier.ex, Quantifier.all])
      (encList (encPair encNat encNat)) (encList encQuantifier) by fun_prop)

/-- Compile all source clauses to literal masks in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_masks :
    ComputableInPolyTime (fun x : PrenexCNF => masks x.rounds x.matrix) encPrenexCNF
      (encList (encList encBool)) := by
  have hv : ComputableInPolyTime (fun x : PrenexCNF => (roundVars x.rounds).reverse)
      encPrenexCNF (encList encNat) := by
    unfold roundVars
    fun_prop
  exact ComputableInPolyTime.mapWithInput
    (show ComputableInPolyTime (fun x : PrenexCNF => x.matrix) encPrenexCNF
      (encList clauseEncoding) by fun_prop)
    (computableInPolyTime_clauseMask
      (hv.comp (ComputableInPolyTime.fst encPrenexCNF clauseEncoding))
      (ComputableInPolyTime.snd encPrenexCNF clauseEncoding))

/-- Normalization, prefix generation, and shadowing-aware masks form a polynomial-time frontend. -/
@[fun_prop]
theorem computableInPolyTime_prepare : ComputableInPolyTime prepare encPrenexCNF encPrepared := by
  have hn := computableInPolyTime_normalize
  exact (computableInPolyTime_quantifiers.comp (by fun_prop)).prod
    (computableInPolyTime_masks.comp hn)

end Cslib.Complexity.NCL.QBF.Source
