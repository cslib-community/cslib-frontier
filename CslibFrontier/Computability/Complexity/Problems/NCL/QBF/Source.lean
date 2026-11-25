/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.Matrix
public import CslibFrontier.Computability.Complexity.Classes.Alternation.TQBF

/-!
# Source CNF formulas and the quantifier circuit

Compile the upstream CNF syntax into masks in the chain's physical literal order. Names are
read from the innermost binder outward. Once a name has been connected, its literals are removed
before processing earlier binders, so repeated names implement ordinary quantifier shadowing.
No distinctness assumption or search for a satisfying assignment is needed.

## Main definitions

* `Cslib.Complexity.NCL.QBF.Source.clauseMask`: connect a clause to the innermost matching names.
* `Cslib.Complexity.NCL.QBF.Source.masks`: compile a CNF using the source's quantifier rounds.
* `Cslib.Complexity.NCL.QBF.Source.quantifiers`: the chain's quantifiers for those rounds.

## Main results

* `Cslib.Complexity.NCL.QBF.Source.truth_iff_eval`: the compiled chain predicate agrees with
  upstream QBF evaluation, including repeated binders and empty matrices and clauses.
* `Cslib.Complexity.NCL.QBF.Source.eval_of_reachable`: success of the actual circuit body
  implies truth of the closed source formula.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.QBF.Source

open Cslib.Logic.PL Cslib.Logic.PL.QBF Diagram

variable {V : Type*} [DecidableEq V]

/-- A clause mask in innermost-first order. Earlier occurrences of an already bound name
receive no connections. Each pair selects the positive, then the negative literal wire. -/
@[expose] def clauseMask : List V → Clause V → List Bool
  | [], _ => []
  | v :: vs, c => c.contains (v, true) :: c.contains (v, false) ::
      clauseMask vs (c.filter fun l => l.1 != v)

/-- The masks of a source CNF, with innermost binders connected first. -/
@[expose] def masks (ps : List (V × V)) (φ : CNF V) : List (List Bool) :=
  φ.map (clauseMask (roundVars ps).reverse)

/-- The actual chain uses an existential and then a universal quantifier for every round. -/
@[expose] def quantifiers : List (V × V) → List Quantifier
  | [] => []
  | _ :: ps => .ex :: .all :: quantifiers ps

private theorem updates_append (vs : List V) (values : List Bool)
    (h : vs.length = values.length) (v : V) (b : Bool) (σ : V → Bool) :
    updates σ (vs ++ [v]) (values ++ [b]) =
      Function.update (updates σ vs values) v b := by
  induction vs generalizing values σ with
  | nil =>
    obtain rfl := List.eq_nil_of_length_eq_zero h.symm
    rfl
  | cons w vs ih =>
    cases values with
    | nil => simp at h
    | cons c values =>
      exact ih values (by simpa using h) (Function.update σ w c)

private theorem eval_update (σ : V → Bool) (v : V) (b : Bool) (c : Clause V) :
    c.eval (Function.update σ v b) =
      ((c.contains (v, true) && b) || (c.contains (v, false) && !b) ||
        Clause.eval σ (c.filter fun l => l.1 != v)) := by
  rw [Bool.eq_iff_iff, Clause.eval_eq_true_iff]
  simp only [Bool.or_eq_true, Bool.and_eq_true, List.contains_iff_mem,
    Clause.eval_eq_true_iff, List.mem_filter, bne_iff_ne]
  constructor
  · rintro ⟨⟨w, p⟩, hl, h⟩
    by_cases hw : w = v
    · subst w
      cases b <;> cases p <;> simp_all [Function.update_self]
    · exact Or.inr ⟨(w, p), ⟨hl, hw⟩, (Function.update_of_ne hw b σ).symm.trans h⟩
  · rintro ((⟨hl, rfl⟩ | ⟨hl, hb⟩) | ⟨l, ⟨hl, hv⟩, h⟩)
    · exact ⟨(v, true), hl, Function.update_self ..⟩
    · exact ⟨(v, false), hl, by simpa using hb⟩
    · exact ⟨l, hl, (Function.update_of_ne hv b σ).trans h⟩

private theorem hits_clauseMask (vs : List V) (values : List Bool) (c : Clause V)
    (hlen : vs.length = values.length) (hbound : ∀ l ∈ c, l.1 ∈ vs) (σ : V → Bool) :
    Network.hits (clauseMask vs c) (values.flatMap fun b => [b, !b]) =
      c.eval (updates σ vs.reverse values.reverse) := by
  induction vs generalizing values c with
  | nil =>
    obtain rfl := List.eq_nil_iff_forall_not_mem.2 fun l hl => List.not_mem_nil (hbound l hl)
    cases values <;> simp_all [clauseMask, Clause.eval, updates]
  | cons v vs ih =>
    rcases values with _ | ⟨b, values⟩
    · simp at hlen
    · simp only [clauseMask, List.flatMap_cons, List.cons_append, List.nil_append,
        Network.hits, List.reverse_cons]
      rw [updates_append _ _ (by simpa using hlen), ih values _ (by simpa using hlen) fun l hl =>
        let ⟨hc, hv⟩ := List.mem_filter.1 hl
        (List.mem_cons.1 (hbound l hc)).resolve_left (bne_iff_ne.1 hv), eval_update]
      exact (Bool.or_assoc ..).symm

private theorem satisfies_iff (vs : List V) (values : List Bool) (φ : CNF V)
    (hlen : vs.length = values.length) (hbound : ∀ v ∈ φ.vars, v ∈ vs) (σ : V → Bool) :
    Matrix.Satisfies (φ.map (clauseMask vs.reverse)) values ↔
      φ.eval (updates σ vs values) = true := by
  unfold Matrix.Satisfies CNF.eval Chain.literalValues
  simp only [List.all_map, Function.comp_def, List.all_eq_true]
  refine forall₂_congr fun c hc => ?_
  rw [hits_clauseMask _ _ _ (by simpa using hlen) (fun l hl =>
    List.mem_reverse.2 (hbound l.1 (List.mem_map.2 ⟨l, List.mem_flatten.2 ⟨c, hc, hl⟩, rfl⟩))) σ]
  simp only [List.reverse_reverse]

private theorem truth_rounds (ps : List (V × V)) (vs : List V) (values : List Bool)
    (φ : CNF V) (hlen : vs.length = values.length)
    (hbound : ∀ v ∈ φ.vars, v ∈ vs ++ roundVars ps) (σ : V → Bool) :
    Chain.Truth (Matrix.Satisfies
      (φ.map (clauseMask (vs ++ roundVars ps).reverse)))
      (quantifiers ps) values ↔
        (rounds ps (ofCNF φ)).eval (updates σ vs values) = true := by
  induction ps generalizing vs values with
  | nil =>
    simpa only [quantifiers, Chain.Truth, rounds, roundVars,
      List.foldr_nil, List.flatMap_nil, List.append_nil, eval_ofCNF]
      using satisfies_iff vs values φ hlen (by simpa [roundVars] using hbound) σ
  | cons p ps ih =>
    simp only [quantifiers, Chain.Truth, rounds, List.foldr_cons,
      eval_ex_eq_true_iff, eval_all_eq_true_iff]
    refine exists_congr fun b => forall_congr' fun c => ?_
    have h := ih (vs ++ [p.1] ++ [p.2]) (values ++ [b] ++ [c]) (by simp [hlen])
      (by simpa only [roundVars, List.flatMap_cons, List.cons_append, List.nil_append,
        List.append_assoc] using hbound)
    rw [updates_append (vs ++ [p.1]) (values ++ [b]) (by simp [hlen]),
      updates_append vs values hlen] at h
    simpa only [rounds, roundVars, List.flatMap_cons, List.cons_append,
      List.nil_append, List.append_assoc] using h

/-- A closed source formula and its compiled masks have the same quantified truth value.
Repeated variables are allowed, including both binders of a single round sharing a name. -/
theorem truth_iff_eval (ps : List (V × V)) (φ : CNF V)
    (hclosed : (rounds ps (ofCNF φ)).Closed) (σ : V → Bool) :
    Chain.Truth (Matrix.Satisfies (masks ps φ)) (quantifiers ps) [] ↔
      (rounds ps (ofCNF φ)).eval σ = true :=
  truth_rounds ps [] [] φ rfl (fun v hv => by
    obtain ⟨c, hc, p, hl⟩ := CNF.mem_vars.1 hv
    exact List.mem_append_right _ ((closed_rounds_ofCNF_iff ps φ).1 hclosed c hc (v, p) hl)) σ

/-- **Source soundness of the actual circuit body.** From any legal inactive start in any
containing diagram, reaching success implies truth of the closed upstream QBF. -/
theorem eval_of_reachable (ps : List (V × V)) (φ : CNF V)
    (hclosed : (rounds ps (ofCNF φ)).Closed)
    {a b : List Color} {D : Diagram Gate a b}
    (o : Occurrence (Matrix.body (quantifiers ps) (masks ps φ)) D)
    {s t : D.Edge → Bool} (hs : (D.graph Gate.interp).Legal s)
    (hstart : s (o.emb (.inl 1)) = false) (h : (D.graph Gate.interp).Reachable s t)
    (hsat : t (o.emb (.inl 0)) = false) (σ : V → Bool) :
    (rounds ps (ofCNF φ)).eval σ = true :=
  (truth_iff_eval ps φ hclosed σ).1
    (Matrix.truth_of_reachable (quantifiers ps) (masks ps φ) o hs hstart h hsat)

end Cslib.Complexity.NCL.QBF.Source
