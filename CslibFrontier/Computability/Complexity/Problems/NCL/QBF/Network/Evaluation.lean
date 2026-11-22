/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.Network
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Realization

/-!
# Executing a CNF network

Build a legal orientation evaluating every row, clause and conjunction on its incoming literal
directions. Every literal continuation keeps its input value. The output of the network is
exactly `ms.all (hits · ls)`, including empty clauses and empty conjunctions.

The static realizations are turned into execution paths by creation-order activation. Starting
with the given top directions and all created wires false, activate the true bits of the
evaluation. This gives the completeness direction of [HearnDemaine2005, Lemma 2, page 6] for
the actual network diagrams. The input is an arbitrary vector of literal directions; relating
it to quantifier memories is handled by the chain and matrix modules.

## Main definitions

* `Cslib.Complexity.NCL.QBF.Network.evalRow`, `Cslib.Complexity.NCL.QBF.Network.evalClause`,
  `Cslib.Complexity.NCL.QBF.Network.evalConjoin`: explicit evaluations of the network parts.
* `Cslib.Complexity.NCL.QBF.Network.evalNetwork`: an explicit legal evaluation of the whole CNF.

## Main results

* `Cslib.Complexity.NCL.QBF.Network.reachable_evalNetwork_within`: evaluate the CNF while
  keeping every input direction fixed.
* `Cslib.Complexity.NCL.QBF.Network.reachable_evalNetwork`: reach the exact evaluation from
  the inactive network with the same inputs.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.QBF.Network

open Diagram Gate

local notation "R" => Color.red
local notation "B" => Color.blue

attribute [local instance] Diagram.decidableLegal

/-- Collect a literal, preserving its direction and copying it to the accumulator. -/
@[expose] def evalTapFirst (l : Bool) : Realization Gate.interp tapFirst [l] [l, l] where
  orient := fun e => l && [0, 1, 3, 4, 5].contains (tapFirst.num e)
  legal := by cases l <;> decide +kernel
  top_eq := by cases l <;> decide +kernel
  bot_eq := by cases l <;> decide +kernel

/-- Collect another literal and disjoin it with the accumulator. -/
@[expose] def evalTap (acc l : Bool) : Realization Gate.interp tap [acc, l] [l, acc || l] where
  orient := fun e => if tap.num e = 0 then acc else if tap.num e = 8 then acc || l
    else l && [1, 2, 4, 5, 6].contains (tap.num e)
  legal := by cases acc <;> cases l <;> decide +kernel
  top_eq := by cases acc <;> cases l <;> decide +kernel
  bot_eq := by cases acc <;> cases l <;> decide +kernel

/-- Evaluate a blue conjunction gate. -/
@[expose] def evalConj (x y : Bool) : Realization Gate.interp conj [x, y] [x && y] where
  orient := fun e => if [0, 2].contains (conj.num e) then x
    else if [1, 4].contains (conj.num e) then y else (conj.num e == 6) && (x && y)
  legal := by cases x <;> cases y <;> decide +kernel
  top_eq := by cases x <;> cases y <;> decide +kernel
  bot_eq := by cases x <;> cases y <;> decide +kernel

/-- Collect a marked literal, or cross it, preserving its direction. -/
@[expose] def evalStep (b acc l : Bool) :
    Realization Gate.interp (step b) [acc, l] [l, acc || (b && l)] :=
  match b with
  | true => evalTap acc l
  | false => by
    simpa only [step, Bool.false_eq_true, ite_false, Bool.false_and, Bool.or_false] using
      (Realization.swap (I := Gate.interp) B R acc l)

/-- Evaluate a row on `ls`, starting with accumulator `acc` and carrying the tail `rs`. -/
@[expose] def evalRow (r : List Color) (rs : List Bool) (hrs : rs.length = r.length) :
    (ls m : List Bool) → (acc : Bool) →
      Realization Gate.interp (row r ls.length m) (acc :: (ls ++ rs))
        (ls ++ ((acc || hits m ls) :: rs))
  | [], m, acc => by
    simpa only [row, List.length_nil, List.nil_append, hits_nil_right, Bool.or_false] using
      (Realization.id (I := Gate.interp) ([B] ++ r) (acc :: rs) (by simp [hrs]))
  | l :: ls, m, acc => by
    have hfirst := (evalStep (m.headD false) acc l).tensor
      (Realization.id (I := Gate.interp) (bundle ls.length ++ r) (ls ++ rs) (by simp [hrs]))
    have hrest := (Realization.id (I := Gate.interp) [R] [l] rfl).tensor
      (evalRow r rs hrs ls m.tail (acc || (m.headD false && l)))
    simpa only [row, List.length_cons, List.cons_append, List.nil_append, hits_cons,
      Bool.or_assoc] using hfirst.comp hrest

/-- Evaluate a clause, preserving all incoming literal directions. -/
@[expose] def evalClause (r : List Color) (rs : List Bool) (hrs : rs.length = r.length) :
    (ls m : List Bool) → Realization Gate.interp (clause r ls.length m) (ls ++ rs)
      (ls ++ (hits m ls :: rs))
  | [], m => by
    simpa only [clause, List.length_nil, List.nil_append, List.cons_append, hits_nil_right] using
      (show Realization Gate.interp (node [] [B]) [] [false] from
        .zeros _ (by decide +kernel)).tensor (.id r rs hrs)
  | l :: ls, m => by
    by_cases hm : m.headD false = true
    · have hfirst := (evalTapFirst l).tensor
        (Realization.id (I := Gate.interp) (bundle ls.length ++ r) (ls ++ rs) (by simp [hrs]))
      have hrest := (Realization.id (I := Gate.interp) [R] [l] rfl).tensor
        (evalRow r rs hrs ls m.tail l)
      simpa only [clause, List.length_cons, hm, ite_true, List.cons_append, List.nil_append,
        hits_cons, Bool.true_and] using hfirst.comp hrest
    · have h := (Realization.id (I := Gate.interp) [R] [l] rfl).tensor
        (evalClause r rs hrs ls m.tail)
      simpa only [clause, List.length_cons, hm, ite_false, Bool.false_eq_true,
        List.cons_append, List.nil_append,
        hits_cons, Bool.eq_false_iff.2 hm, Bool.false_and, Bool.false_or] using h

/-- Conjoin the remaining clauses with the current value `w`. -/
@[expose]
def evalConjoin (r : List Color) (rs : List Bool) (hrs : rs.length = r.length) (ls : List Bool) :
    (ms : List (List Bool)) → (w : Bool) →
      Realization Gate.interp (conjoin r ls.length ms) (ls ++ (w :: rs))
        (ls ++ ((w && ms.all (hits · ls)) :: rs))
  | [], w => by
    simpa only [conjoin, List.all_nil, Bool.and_true] using
      (Realization.id (I := Gate.interp) (bundle ls.length ++ ([B] ++ r)) (ls ++ (w :: rs))
        (by simp [hrs]))
  | m :: ms, w => by
    have hc := evalClause ([B] ++ r) (w :: rs) (by simp [hrs]) ls m
    have ha := (Realization.id (I := Gate.interp) (bundle ls.length) ls (by simp)).tensor
      ((evalConj (hits m ls) w).tensor (.id r rs hrs))
    have h := (hc.comp ha).comp (evalConjoin r rs hrs ls ms (hits m ls && w))
    simpa only [conjoin, List.all_cons, Bool.and_assoc, Bool.and_left_comm] using h

/-- An explicit legal evaluation of an arbitrary CNF, with literal continuations unchanged. -/
@[expose]
def evalNetwork (r : List Color) (rs : List Bool) (hrs : rs.length = r.length) (ls : List Bool) :
    (ms : List (List Bool)) → Realization Gate.interp (network r ls.length ms) (ls ++ rs)
      (ls ++ (ms.all (hits · ls) :: rs))
  | [] => (Realization.id (I := Gate.interp) (bundle ls.length) ls (by simp)).tensor
      ((show Realization Gate.interp (gen start) [] [true] from
        { orient := fun _ => true
          legal := by decide +kernel
          top_eq := rfl
          bot_eq := rfl }).tensor (.id r rs hrs))
  | m :: ms => (evalClause r rs hrs ls m).comp (evalConjoin r rs hrs ls ms (hits m ls))

private theorem row_zero (r : List Color) : ∀ (n : ℕ) (m : List Bool),
    ((row r n m).graph Gate.interp).Legal (fun _ => false)
  | 0, _ => fun v => v.elim
  | n + 1, m => (legal_comp_iff _ _ _).2 ⟨
      (legal_tensor_iff _ _ _).2 ⟨by
        change ((step (m.headD false)).graph Gate.interp).Legal (fun _ => false)
        cases m.headD false <;> decide +kernel, fun v => v.elim⟩,
      (legal_tensor_iff _ _ _).2 ⟨fun v => v.elim, row_zero r n m.tail⟩⟩

private theorem clause_zero (r : List Color) : ∀ (n : ℕ) (m : List Bool),
    ((clause r n m).graph Gate.interp).Legal (fun _ => false)
  | 0, _ => (legal_tensor_iff _ _ _).2 ⟨by
      change ((node [] [B]).graph Gate.interp).Legal (fun _ => false)
      decide +kernel, fun v => v.elim⟩
  | n + 1, m => by
    simp only [Network.clause]
    by_cases hm : m.headD false = true
    · rw [ite_eq_left hm]
      exact (legal_comp_iff _ _ _).2 ⟨
        (legal_tensor_iff _ _ _).2 ⟨by
          change (tapFirst.graph Gate.interp).Legal (fun _ => false)
          decide +kernel, fun v => v.elim⟩,
        (legal_tensor_iff _ _ _).2 ⟨fun v => v.elim, row_zero r n m.tail⟩⟩
    · rw [ite_eq_right hm]
      exact (legal_tensor_iff _ _ _).2 ⟨fun v => v.elim, clause_zero r n m.tail⟩

private theorem conjoin_zero (r : List Color) (n : ℕ) : ∀ (ms : List (List Bool)),
    ((conjoin r n ms).graph Gate.interp).Legal (fun _ => false)
  | [] => fun v => v.elim
  | m :: ms => (legal_comp_iff _ _ _).2 ⟨(legal_comp_iff _ _ _).2 ⟨clause_zero _ n m,
      (legal_tensor_iff _ _ _).2 ⟨fun v => v.elim,
        (legal_tensor_iff _ _ _).2 ⟨by
          change (conj.graph Gate.interp).Legal (fun _ => false)
          decide +kernel, fun v => v.elim⟩⟩⟩, conjoin_zero r n ms⟩

/-- The CNF network with every edge false satisfies every inflow constraint. -/
theorem legal_network_zero (r : List Color) (n : ℕ) : ∀ (ms : List (List Bool)),
    ((network r n ms).graph Gate.interp).Legal (fun _ => false)
  | [] => (legal_tensor_iff _ _ _).2 ⟨fun v => v.elim,
      (legal_tensor_iff _ _ _).2 ⟨by
        change ((gen start).graph Gate.interp).Legal (fun _ => false)
        decide +kernel, fun v => v.elim⟩⟩
  | m :: ms => (legal_comp_iff _ _ _).2 ⟨clause_zero r n m, conjoin_zero r n ms⟩

/-- Evaluate the CNF in creation order while keeping every input direction fixed. -/
theorem reachable_evalNetwork_within (r : List Color) (rs : List Bool) (hrs : rs.length = r.length)
    (ls : List Bool) (ms : List (List Bool)) :
    Relation.ReflTransGen (Within ((network r ls.length ms).graph Gate.interp).Step
      (fun u => (network r ls.length ms).topList u = ls ++ rs))
      ((network r ls.length ms).off (evalNetwork r rs hrs ls ms).orient)
      (evalNetwork r rs hrs ls ms).orient := by
  refine reachable_of_le_within Gate.interp_forward
    (network r ls.length ms) (legal_off Gate.interp_forward _
      (legal_network_zero r ls.length ms) (evalNetwork r rs hrs ls ms).legal)
    (evalNetwork r rs hrs ls ms).legal (fun e => ?_) (fun u hlow hhigh => ?_)
  · rcases e with i | e
    · exact le_rfl
    · exact Bool.false_le _
  · exact (List.ofFn_inj.2 (funext fun i => le_antisymm (hhigh (.inl i)) (hlow (.inl i)))).trans
      (evalNetwork r rs hrs ls ms).top_eq

/-- Activate a CNF evaluation from its inputs with all created wires false. The endpoint
preserves every literal continuation and computes exactly the marked conjunction. -/
theorem reachable_evalNetwork (r : List Color) (rs : List Bool) (hrs : rs.length = r.length)
    (ls : List Bool) (ms : List (List Bool)) :
    ((network r ls.length ms).graph Gate.interp).Reachable
      ((network r ls.length ms).off (evalNetwork r rs hrs ls ms).orient)
      (evalNetwork r rs hrs ls ms).orient :=
  Relation.ReflTransGen.mono (fun _ _ h => h.2) _ _ (reachable_evalNetwork_within r rs hrs ls ms)

end Cslib.Complexity.NCL.QBF.Network
