/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.Normalize
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length

/-!
# Polynomial-time source preprocessing

Generate the quantifier list and literal masks from upstream alternating prenex CNF data.
The mask scan removes processed names from the remaining clause and appends two bits per
binder. Its encoded accumulator grows by at most six bits per step.

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
@[expose] def prepare (x : Input) : List Quantifier × List (List Bool) :=
  (quantifiers (normalize x).1, masks (normalize x).1 (normalize x).2)

private abbrev clauseEncoding := encList (encPair encNat encBool)
private abbrev maskEncoding := encPair clauseEncoding (encList encBool)
private abbrev maskInputEncoding := encPair (encList encNat) clauseEncoding

private def maskStep (state : Clause ℕ × List Bool) (v : ℕ) : Clause ℕ × List Bool :=
  (state.1.filter (fun l => l.1 != v),
    state.2 ++ [state.1.contains (v, true), state.1.contains (v, false)])

private theorem maskFold_eq (vs : List ℕ) (c : Clause ℕ) (bits : List Bool) :
    (vs.foldl maskStep (c, bits)).2 = bits ++ clauseMask vs c := by
  induction vs generalizing c bits with
  | nil => simp [clauseMask]
  | cons v vs ih =>
    simp only [List.foldl_cons, maskStep]
    rw [ih, clauseMask, List.append_assoc]
    rfl

private theorem computableInPolyTime_maskStep :
    ComputableInPolyTime (fun p : (Clause ℕ × List Bool) × ℕ => maskStep p.1 p.2)
      (encPair maskEncoding encNat) maskEncoding := by
  let input := encPair maskEncoding encNat
  have hc : ComputableInPolyTime (fun p : (Clause ℕ × List Bool) × ℕ => p.1.1)
      input clauseEncoding := by unfold input maskEncoding; fun_prop
  have hv : ComputableInPolyTime (fun p : (Clause ℕ × List Bool) × ℕ => p.2)
      input encNat := by unfold input; fun_prop
  have ht : ComputableInPolyTime (fun p : ((Clause ℕ × List Bool) × ℕ) × (ℕ × Bool) =>
      p.2.1 != p.1.2) (encPair input (encPair encNat encBool)) encBool := by
    have h₁ : ComputableInPolyTime (fun p : ((Clause ℕ × List Bool) × ℕ) × (ℕ × Bool) =>
        p.2.1) (encPair input (encPair encNat encBool)) encNat := by fun_prop
    have h₂ := hv.comp (ComputableInPolyTime.fst input (encPair encNat encBool))
    exact ComputableInPolyTime.decide_ne h₁ h₂
  have hf := ComputableInPolyTime.filterWithInput
    (test := fun p l => l.1 != p.2) hc ht
  have hb (b : Bool) : ComputableInPolyTime
      (fun p : (Clause ℕ × List Bool) × ℕ => p.1.1.contains (p.2, b)) input encBool := by
    have he : ComputableInPolyTime (fun p : ℕ × (ℕ × Bool) => (p.1, b) == p.2)
        (encPair encNat (encPair encNat encBool)) encBool := by
      have h₁ := ComputableInPolyTime.snd encNat (encPair encNat encBool)
      have h₂ : ComputableInPolyTime (fun p : ℕ × (ℕ × Bool) => (p.1, b))
          (encPair encNat (encPair encNat encBool)) (encPair encNat encBool) := by fun_prop
      exact ComputableInPolyTime.beq h₂ h₁
    simpa only [List.contains_eq_any_beq] using
      (ComputableInPolyTime.anyWithEncoding he hv hc)
  have hs : ComputableInPolyTime (fun p : (Clause ℕ × List Bool) × ℕ => p.1.2)
      input (encList encBool) := by unfold input maskEncoding; fun_prop
  have hpos := hb true
  have hneg := hb false
  unfold maskStep maskEncoding
  exact hf.prod (hs.listAppend' (hpos.cons' (hneg.cons' (ComputableInPolyTime.const []))))

private theorem maskStep_growth (state : Clause ℕ × List Bool) (v : ℕ) :
    (maskEncoding (maskStep state v)).length ≤ (maskEncoding state).length + 6 := by
  unfold maskStep
  have hc : (clauseEncoding (state.1.filter (fun l => l.1 != v))).length ≤
      (clauseEncoding state.1).length :=
    length_encList_sublist (encPair encNat encBool) List.filter_sublist
  simp only [maskEncoding, length_encPair, encList_append, List.length_append,
    encList_cons, length_frame, encBool_apply, List.length_singleton, encList_nil,
    List.length_nil]
  apply (Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hc) 1) _).trans
  omega

private theorem computableInPolyTime_maskFold :
    ComputableInPolyTime (fun x : List ℕ × Clause ℕ => x.1.foldl maskStep (x.2, []))
      maskInputEncoding maskEncoding := by
  have hl : ComputableInPolyTime (fun x : List ℕ × Clause ℕ => x.1)
      maskInputEncoding (encList encNat) := by
    unfold maskInputEncoding
    fun_prop
  have hi : ComputableInPolyTime (fun x : List ℕ × Clause ℕ => (x.2, []))
      maskInputEncoding maskEncoding := by
    unfold maskInputEncoding maskEncoding
    fun_prop
  exact ComputableInPolyTime.foldl_of_bounded_growth hl hi computableInPolyTime_maskStep
    maskStep_growth

/-- Literal masks with shadowed names are computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_clauseMask {α : Type} {input : α ↪ List Bool}
    {vs : α → List ℕ} {c : α → Clause ℕ}
    (hv : ComputableInPolyTime vs input (encList encNat))
    (hc : ComputableInPolyTime c input (encList (encPair encNat encBool))) :
    ComputableInPolyTime (fun x => clauseMask (vs x) (c x)) input (encList encBool) := by
  have hf := computableInPolyTime_maskFold
  unfold maskEncoding at hf
  have hb := hf.snd'
  have hm : ComputableInPolyTime (fun x : List ℕ × Clause ℕ => clauseMask x.1 x.2)
      maskInputEncoding (encList encBool) := by
    simpa only [maskFold_eq, List.nil_append] using hb
  exact hm.comp (hv.prod hc)

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
  have h : ComputableInPolyTime
      (fun ps : List (ℕ × ℕ) => ps.flatMap (fun _ => [Quantifier.ex, Quantifier.all]))
      (encList (encPair encNat encNat)) (encList encQuantifier) := by fun_prop
  simpa only [← quantifiers_eq_flatMap] using h

/-- Compile all source clauses to literal masks in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_masks :
    ComputableInPolyTime (fun x : Input => masks x.1 x.2) encPrenexCNF
      (encList (encList encBool)) := by
  have hv : ComputableInPolyTime (fun x : Input => (roundVars x.1).reverse)
      encPrenexCNF (encList encNat) := by
    unfold roundVars encPrenexCNF encCNF
    fun_prop
  have hc : ComputableInPolyTime (fun x : Input => x.2) encPrenexCNF
      (encList (encList (encPair encNat encBool))) := by
    unfold encPrenexCNF encCNF
    fun_prop
  have hm : ComputableInPolyTime (fun p : Input × Clause ℕ =>
      clauseMask (roundVars p.1.1).reverse p.2)
      (encPair encPrenexCNF clauseEncoding) (encList encBool) :=
    computableInPolyTime_clauseMask
      (hv.comp (ComputableInPolyTime.fst encPrenexCNF clauseEncoding))
      (ComputableInPolyTime.snd encPrenexCNF clauseEncoding)
  exact ComputableInPolyTime.mapWithInput hc hm

/-- Normalization, prefix generation, and shadowing-aware masks form a polynomial-time frontend. -/
@[fun_prop]
theorem computableInPolyTime_prepare : ComputableInPolyTime prepare encPrenexCNF encPrepared := by
  unfold prepare encPrepared
  fun_prop

end Cslib.Complexity.NCL.QBF.Source
