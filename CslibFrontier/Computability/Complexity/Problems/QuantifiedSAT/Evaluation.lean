/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.TQBF.QuantifierFree
public import CslibFrontier.Computability.Complexity.Classes.PH.QBF
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString

/-!
# Word assignments for quantified SAT

The truth values assigned by a word to a list of variables are computed by searching the
reversed zipped lists. This respects shadowing: the last assignment to a variable wins.
The resulting list of true variables feeds the existing polynomial-time Boolean-formula scan.
-/

public section

namespace Cslib.Complexity.QuantifiedSAT

open Cslib.Logic.PL Turing.MultiTapeTM ComputableInPolyTime

/-- The last value assigned to `v` by the zipped variables and word; `none` if unassigned. -/
private def assigned (vs : List ℕ) (w : List Bool) (v : ℕ) : Option Bool :=
  (((vs.zip w).reverse.find? fun p => p.1 == v).map Prod.snd)

private theorem updates_assigned (vs : List ℕ) (w : List Bool) (σ : ℕ → Bool) (v : ℕ) :
    QBF.updates σ vs w v = (assigned vs w v).getD (σ v) := by
  induction vs generalizing σ w with
  | nil => simp [QBF.updates, assigned]
  | cons x vs ih =>
    cases w with
    | nil => simp [QBF.updates, assigned]
    | cons b w =>
      rw [QBF.updates, ih]
      simp only [assigned, List.zip_cons_cons, List.reverse_cons, List.find?_append,
        List.find?_cons, List.find?_nil]
      cases (vs.zip w).reverse.find? (fun p => p.1 == v) with
      | none =>
        rcases eq_or_ne x v with rfl | h
        · simp
        · simp [Ne.symm h, beq_eq_false_iff_ne.mpr h]
      | some _ => simp

/-- A list whose indicator is the assignment made by `w` along `vs`, starting with every
variable false. Duplicate variable names obey the usual last-assignment convention. -/
def trueVars (vs : List ℕ) (w : List Bool) : List ℕ :=
  vs.filter fun v => (assigned vs w v).getD false

private theorem assigned_none_of_notMem {vs : List ℕ} {v : ℕ} (h : v ∉ vs) (w : List Bool) :
    assigned vs w v = none := by
  simp only [assigned, Option.map_eq_none_iff, List.find?_eq_none, List.mem_reverse, beq_iff_eq]
  rintro p hp rfl
  exact h (List.of_mem_zip hp).1

/-- The indicator list computes the assignment made by the word. -/
theorem contains_trueVars (vs : List ℕ) (w : List Bool) (v : ℕ) :
    (trueVars vs w).contains v = QBF.updates (fun _ => false) vs w v := by
  rw [updates_assigned]
  by_cases hv : v ∈ vs <;> simp [trueVars, hv, assigned_none_of_notMem]

private theorem assigned_polyTime :
    ComputableInPolyTime (fun p : (List ℕ × List Bool) × ℕ => assigned p.1.1 p.1.2 p.2)
      (encPair (encPair (encList encNat) encBits) encNat) (encOption encBool) := by
  unfold assigned
  have hzip := (ComputableInPolyTime.zip encNat encBool).comp
    ((fst _ _).prod ((bitsToList).comp (snd _ _)))
  have hfind : ComputableInPolyTime
      (fun p : (List ℕ × List Bool) × ℕ =>
        ((p.1.1.zip p.1.2).reverse.find? fun q => q.1 == p.2))
      (encPair (encPair (encList encNat) encBits) encNat) (encOption (encPair encNat encBool)) :=
    findWithInput (listReverseWithInput (hzip.comp (fst _ _))) (by fun_prop)
  fun_prop

/-- Constructing the indicator list of a word assignment is polynomial-time. -/
theorem trueVars_polyTime :
    ComputableInPolyTime (fun p : List ℕ × List Bool => trueVars p.1 p.2)
      (encPair (encList encNat) encBits) (encList encNat) := by
  unfold trueVars
  have h := assigned_polyTime
  fun_prop

end Cslib.Complexity.QuantifiedSAT
