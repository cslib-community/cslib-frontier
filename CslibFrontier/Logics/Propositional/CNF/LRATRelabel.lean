/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.LRAT

/-! # Renaming the variables of an LRAT certificate

Renaming the variables of a formula along an injective map `g`, and the literals of a certificate
along the same map, does not change whether the checker accepts the certificate
(`Cslib.Logic.PL.CNF.checkLRAT_relabel`). The checker only compares literals for equality and
looks clauses up by number, and an injective renaming preserves both. A solver can therefore work
on a formula whose variables have been renamed, for example to `0, …, k - 1`, and translate its
certificate back to the original variables.

## Main definitions

* `Cslib.Logic.PL.relabelDIMACS`: a DIMACS literal renamed along `g`.
* `Cslib.Logic.PL.relabelAction`: a certificate step with its literals renamed.

## Main results

* `Cslib.Logic.PL.CNF.checkLRAT_relabel`: the checker accepts a renamed certificate for the
  renamed formula exactly when it accepts the original.
-/

@[expose] public section

namespace Cslib.Logic.PL

open Std.Tactic.BVDecide (LRAT.IntAction)

/-- A DIMACS literal renamed along `g`: the variable `v`, written `±(v + 1)`, becomes `g v`, with
the same sign; `0` stays `0`. -/
def relabelDIMACS (g : ℕ → ℕ) (i : Int) : Int :=
  if 0 < i then ((g (i.natAbs - 1) + 1 : ℕ) : Int)
  else if i < 0 then -((g (i.natAbs - 1) + 1 : ℕ) : Int)
  else 0

/-- A certificate step with the literals of its clause renamed along `g`. Clause numbers and
hints are unchanged. -/
def relabelAction (g : ℕ → ℕ) : LRAT.IntAction → LRAT.IntAction
  | .addEmpty i hints => .addEmpty i hints
  | .addRup i c hints => .addRup i (c.map (relabelDIMACS g)) hints
  | .addRat i c pivot rupHints ratHints =>
    .addRat i (c.map (relabelDIMACS g)) (Prod.map g _root_.id pivot) rupHints ratHints
  | .del ids => .del ids

theorem Literal.ofDIMACS_relabelInt (g : ℕ → ℕ) (i : Int) :
    Literal.ofDIMACS (relabelDIMACS g i) = (Literal.ofDIMACS i).map (Prod.map g id) := by
  unfold relabelDIMACS Literal.ofDIMACS
  by_cases hp : 0 < i
  · simp only [hp, ite_true, Option.map_some,
      show (0 : Int) < ((g (i.natAbs - 1) + 1 : ℕ) : Int) by omega,
      Int.natAbs_natCast, Nat.add_sub_cancel, Prod.map]
    rfl
  · by_cases hn : i < 0
    · simp only [hp, hn, ite_false, ite_true, Option.map_some,
        show ¬ (0 : Int) < -((g (i.natAbs - 1) + 1 : ℕ) : Int) by omega,
        show -((g (i.natAbs - 1) + 1 : ℕ) : Int) < 0 by omega,
        Int.natAbs_neg, Int.natAbs_natCast, Nat.add_sub_cancel, Prod.map]
      rfl
    · simp [hp, hn]

theorem Clause.ofDIMACS_map_relabelDIMACS (g : ℕ → ℕ) (c : List Int) :
    Clause.ofDIMACS (c.map (relabelDIMACS g)) = (Clause.ofDIMACS c).relabel g := by
  simp only [Clause.ofDIMACS, Clause.relabel, List.filterMap_map, Function.comp_def,
    Literal.ofDIMACS_relabelInt, List.map_filterMap]

section Relabel

variable {g : ℕ → ℕ}

/-- Renaming commutes with negation. -/
theorem Literal.negate_prodMap (l : Literal ℕ) :
    Std.Sat.Literal.negate (Prod.map g id l) = Prod.map g id (Std.Sat.Literal.negate l) := rfl

theorem contains_map_prodMap (hg : Function.Injective g) (trail : List (Literal ℕ))
    (l : Literal ℕ) :
    (trail.map (Prod.map g id)).contains (Prod.map g id l) = trail.contains l := by
  simp only [List.contains_eq_mem, List.mem_map, decide_eq_decide]
  exact ⟨fun ⟨_, ha, he⟩ => (hg.prodMap Function.injective_id) he ▸ ha, fun h => ⟨l, h, rfl⟩⟩

/-- Unit propagation along hints is unchanged by an injective renaming of the database and the
starting literals. -/
theorem CNF.propagateHints_relabel (hg : Function.Injective g) (db : List (ℕ × Clause ℕ))
    (trail : List (Literal ℕ)) (hs : List ℕ) :
    CNF.propagateHints (db.map fun e => (e.1, e.2.relabel g)) (trail.map (Prod.map g id)) hs =
      CNF.propagateHints db trail hs := by
  have hinj : Function.Injective (Prod.map g id : Literal ℕ → Literal ℕ) :=
    hg.prodMap Function.injective_id
  induction hs generalizing trail with
  | nil => rfl
  | cons h hs ih =>
    rw [CNF.propagateHints_cons, CNF.propagateHints_cons]
    simp only [List.find?_map, Function.comp_def]
    cases hf : db.find? (·.1 == h) with
    | none => rfl
    | some e =>
      simp only [Option.map_some, Clause.residual, Clause.relabel, List.filter_map,
        Function.comp_def, Literal.negate_prodMap, contains_map_prodMap hg]
      cases e.2.filter fun l => !trail.contains (Std.Sat.Literal.negate l) with
      | nil => rfl
      | cons l ls =>
        simp only [List.map_cons]
        have hall : (ls.map (Prod.map g id)).all (· == Prod.map g id l) = ls.all (· == l) := by
          simp only [List.all_map, Function.comp_def]
          exact congrArg ls.all (funext fun _ => Bool.eq_iff_iff.2 (by simp [hinj.eq_iff]))
        rw [hall]
        cases ls.all (· == l)
        · rfl
        · exact ih (l :: trail)

theorem CNF.checkLRATAux_relabel (hg : Function.Injective g) (db : List (ℕ × Clause ℕ))
    (cert : List LRAT.IntAction) :
    CNF.checkLRATAux (db.map fun e => (e.1, e.2.relabel g)) (cert.map (relabelAction g)) =
      CNF.checkLRATAux db cert := by
  induction cert generalizing db with
  | nil => rfl
  | cons a cert ih =>
    cases a with
    | addEmpty i hints =>
      exact CNF.propagateHints_relabel hg db [] hints.toList
    | addRup i c hints =>
      simp only [List.map_cons, relabelAction, CNF.checkLRATAux, Array.toList_map,
        Clause.ofDIMACS_map_relabelDIMACS]
      have htrail : ((Clause.ofDIMACS c.toList).relabel g).map Std.Sat.Literal.negate =
          ((Clause.ofDIMACS c.toList).map Std.Sat.Literal.negate).map (Prod.map g id) := by
        simp [Clause.relabel, Function.comp_def, Literal.negate_prodMap]
      rw [htrail, CNF.propagateHints_relabel hg]
      exact congrArg _ (ih ((i, Clause.ofDIMACS c.toList) :: db))
    | addRat => rfl
    | del ids =>
      simp only [List.map_cons, relabelAction, CNF.checkLRATAux, List.filter_map,
        Function.comp_def]
      exact ih _

/-- **The checker is invariant under injective renaming**: it accepts a certificate with its
literals renamed along an injective `g` for the renamed formula exactly when it accepts the
original certificate for the original formula. -/
theorem CNF.checkLRAT_relabel (hg : Function.Injective g) (φ : CNF ℕ)
    (cert : Array LRAT.IntAction) :
    (φ.relabel g).checkLRAT (cert.map (relabelAction g)) = φ.checkLRAT cert := by
  unfold CNF.checkLRAT CNF.lratDB
  have hdb : (CNF.relabel g φ).zipIdx.map (fun e => (e.2 + 1, e.1)) =
      (φ.zipIdx.map fun e => (e.2 + 1, e.1)).map fun e => (e.1, e.2.relabel g) := by
    simp [CNF.relabel, List.zipIdx_map, Function.comp_def]
  rw [hdb, Array.toList_map]
  exact CNF.checkLRATAux_relabel hg _ _

end Relabel

end Cslib.Logic.PL
