/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.OneInThreeSAT.Reduction
public import CslibFrontier.Computability.Complexity.Classes.NP.Witness
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Data.List.GetD

/-!
# Exact Cover by 3-sets

An instance of *3-Exact Cover* (3XC) is a sequence `C` of sets of exactly three elements; it is a
yes-instance when some sub-collection of `C` covers every element of the union of `C` exactly once
(`Cslib.Complexity.ThreeExactCover`). Goldreich's Proposition 2.25 says that 3XC is NP-complete
[Goldreich, Section 2.3.3][Goldreich2006DraftR1]. Sets are lists of three distinct natural numbers,
and instances are encoded by `encThreeExactCover`, with binary element labels.

Membership in NP selects the sets of the cover (`Cslib.Complexity.ThreeExactCover_mem_NP`).
Hardness is a reduction from positive exact-one satisfiability with exactly three distinct
variables per clause and at most three occurrences per variable
(`Cslib.Complexity.PositiveOneInExactThreeSATThree`), which is NP-complete. For a formula with `m`
clauses, the clauses are the elements `0, …, m - 1`, and `2m` dummy elements `m, …, 3m - 1` are
added. A variable `v` occurring in the clauses `O_v` (one to three of them) contributes every set
`O_v ∪ P` with `P` a set of `3 - |O_v|` dummy elements, and every triple of dummy elements is a set.
This is the padding of the last step of Goldreich's proof (the reduction from 3XC′, with `K = m`),
applied directly to the occurrence sets.

* An exact-one assignment makes the occurrence sets of its true variables a partition of the
  clauses. There are at most `m` of them, so they need `3k - m ≤ 2m` dummy elements for `k` true
  variables; the remaining `3(m - k)` dummy elements are covered by triples
  (`Cslib.Complexity.ThreeExactCover.mem_of_oneSatisfiable`).
* Conversely, a set of an exact cover containing a clause consists of the occurrences of some
  variable and of dummy elements. Several variables may occur in exactly the same clauses; the
  least of them is set true (`Cslib.Complexity.ThreeExactCover.oneSatisfiable_of_mem`).

The draft's proof composes three reductions, from 3SAT with at most three occurrences per variable
through set cover with sets of size at most three and exact cover with sets of size at most three.
The reduction here starts instead from the exact-one problem, whose NP-hardness is already in the
library, and uses only the last of these steps.

## Main definitions

* `Cslib.Complexity.IsExactCover`: a sub-collection covers the union exactly once.
* `Cslib.Complexity.ThreeExactCover`, `Cslib.Complexity.encThreeExactCover`: the problem and its
  encoding.
* `Cslib.Complexity.ThreeExactCover.reduce`: the reduction.

## Main results

* `Cslib.Complexity.ThreeExactCover_mem_NP`: 3XC is in NP.
* `Cslib.Complexity.ThreeExactCover.reduce_mem_iff`: the reduction is correct.
* `Cslib.Complexity.ThreeExactCover_npComplete`: **3XC is NP-complete** (Goldreich,
  Proposition 2.25).

## References

* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, draft of December 2006,
  Proposition 2.25][Goldreich2006DraftR1]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-- The sub-collection `D` of sets exactly covers the union of the sets `C`: every element of a set
of `C` belongs to exactly one set of `D`. -/
def IsExactCover (C : List (List ℕ)) (D : Finset (List ℕ)) : Prop :=
  ∀ u ∈ C.flatten, (D.filter (u ∈ ·)).card = 1

/-- **Exact Cover by 3-sets** (3XC): a sequence `C` of sets of exactly three elements each, some
sub-collection of which covers every element of their union exactly once. Sets are lists of three
distinct natural numbers. -/
def ThreeExactCover : Set (List (List ℕ)) :=
  {C | (∀ S ∈ C, S.length = 3 ∧ S.Nodup) ∧ ∃ D : Finset (List ℕ), (∀ S ∈ D, S ∈ C) ∧
    IsExactCover C D}

/-- The binary encoding of 3XC instances: a list of lists of binary natural numbers. -/
abbrev encThreeExactCover : List (List ℕ) ↪ List Bool := encList (encList encNat)

namespace ThreeExactCover

/-- A set of three distinct elements. -/
def isTriple (S : List ℕ) : Bool :=
  (S.length == 3) && (S.getD 0 0 != S.getD 1 0) && (S.getD 0 0 != S.getD 2 0) &&
    (S.getD 1 0 != S.getD 2 0)

/-- `isTriple` checks for three distinct elements. -/
theorem isTriple_iff (S : List ℕ) : isTriple S = true ↔ S.length = 3 ∧ S.Nodup := by
  rcases S with _ | ⟨a, _ | ⟨b, _ | ⟨d, _ | ⟨e, t⟩⟩⟩⟩
  all_goals simp [isTriple, List.getD, List.nodup_cons, and_assoc, and_left_comm, and_comm]

/-- The verifier's check of a selection `x.2` of sets of the instance `x.1`: every set of the
instance has three elements, and every element of their union lies in exactly one selected set. -/
def check (x : List (List ℕ) × List (List ℕ)) : Bool :=
  x.1.all isTriple && x.1.flatten.all fun u => (x.2.filter fun S => decide (u ∈ S)).length == 1

/-- The dummy elements `m, …, 3m - 1`. -/
def pool (m : ℕ) : List ℕ := (List.range (2 * m)).map (m + ·)

/-- The pairs `[a, b]` of dummy elements with `a < b`. -/
def pairs (m : ℕ) : List (List ℕ) :=
  (pool m).flatMap fun a => ((pool m).filter (a < ·)).map fun b => [a, b]

/-- The triples `[a, b, c]` of dummy elements with `a < b < c`. -/
def triples (m : ℕ) : List (List ℕ) :=
  (pool m).flatMap fun a => ((pool m).filter (a < ·)).flatMap fun b =>
    ((pool m).filter (b < ·)).map fun c => [a, b, c]

/-- The indices of the clauses of `φ` in which the variable `v` occurs. -/
def occ (φ : CNF ℕ) (v : ℕ) : List ℕ :=
  (List.range φ.length).filter fun j => decide (v ∈ (φ.getD j []).map Prod.fst)

/-- The sets of a variable occurring in the clauses `O`, padded to three elements by dummy
elements in every possible way. -/
def gadget (m : ℕ) (O : List ℕ) : List (List ℕ) :=
  if O.length == 3 then [O]
  else if O.length == 2 then (pool m).map fun d => O ++ [d]
  else if O.length == 1 then (pairs m).map fun p => O ++ p
  else []

open ComputableInPolyTime

private theorem computableInPolyTime_pool :
    ComputableInPolyTime pool encUnary (encList encNat) := by
  unfold pool
  fun_prop

attribute [local fun_prop] computableInPolyTime_pool

private theorem computableInPolyTime_pairs :
    ComputableInPolyTime pairs encUnary (encList (encList encNat)) := by
  unfold pairs
  fun_prop

private theorem computableInPolyTime_triples :
    ComputableInPolyTime triples encUnary (encList (encList encNat)) := by
  unfold triples
  fun_prop

private theorem computableInPolyTime_occ_unary :
    ComputableInPolyTime (fun p : CNF ℕ × ℕ => occ p.1 p.2) (encPair encCNF encNat)
      (encList encUnary) := by
  unfold occ
  refine ComputableInPolyTime.filterWithInput (encA := encUnary) ?_ ?_
  · fun_prop
  · have h1 : ComputableInPolyTime (fun q : (CNF ℕ × ℕ) × ℕ => (q.1.1.getD q.2 []).map Prod.fst)
        (encPair (encPair encCNF encNat) encUnary) (encList encNat) := by
      unfold encCNF
      fun_prop
    fun_prop

private theorem computableInPolyTime_occ :
    ComputableInPolyTime (fun p : CNF ℕ × ℕ => occ p.1 p.2) (encPair encCNF encNat)
      (encList encNat) := by
  have h := (ComputableInPolyTime.map (encA := encUnary) (encB := encNat) (f := fun n => n)
    ComputableInPolyTime.unary_to_binary).comp computableInPolyTime_occ_unary
  simpa using h

attribute [local fun_prop] computableInPolyTime_pairs

private theorem computableInPolyTime_gadget :
    ComputableInPolyTime (fun p : ℕ × List ℕ => gadget p.1 p.2) (encPair encUnary (encList encNat))
      (encList (encList encNat)) := by
  unfold gadget
  fun_prop

attribute [local fun_prop] computableInPolyTime_gadget computableInPolyTime_occ
  computableInPolyTime_triples

private theorem computableInPolyTime_isTriple :
    ComputableInPolyTime isTriple (encList encNat) encBool := by
  unfold isTriple
  fun_prop

attribute [local fun_prop] computableInPolyTime_isTriple

/-- The verifier's check is computable in polynomial time. -/
theorem computableInPolyTime_check :
    ComputableInPolyTime check (encPair encThreeExactCover (encList (encList encNat))) encBool := by
  unfold check
  fun_prop

/-- A fixed no-instance: `{0, 1, 2, 3}` is not exactly covered by `{0, 1, 2}` and `{0, 1, 3}`. -/
def noInstance : List (List ℕ) := [[0, 1, 2], [0, 1, 3]]

/-- The reduction from positive exact-three exact-one SAT with at most three occurrences per
variable. -/
def reduce (φ : CNF ℕ) : List (List ℕ) :=
  if PositiveOneInExactThreeSATThree.syntaxCheck φ then
    φ.vars.flatMap (fun v => gadget φ.length (occ φ v)) ++ triples φ.length
  else noInstance

/-- The reduction is computable in polynomial time. -/
theorem computableInPolyTime_reduce : ComputableInPolyTime reduce encCNF encThreeExactCover := by
  unfold reduce CNF.vars
  fun_prop

/-! ### Membership in NP -/

private theorem check_iff (C l : List (List ℕ)) (hl : l.Nodup) :
    check (C, l) = true ↔ (∀ S ∈ C, S.length = 3 ∧ S.Nodup) ∧ IsExactCover C l.toFinset := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, isTriple_iff, beq_iff_eq, IsExactCover]
  refine and_congr Iff.rfl (forall₂_congr fun u _ => ?_)
  have h := List.toFinset_card_of_nodup (hl.filter fun S => decide (u ∈ S))
  rw [List.toFinset_filter] at h
  simp only [decide_eq_true_eq] at h
  rw [h]

/-! ### The shape of the reduced instance -/

private theorem mem_pool {m d : ℕ} : d ∈ pool m ↔ m ≤ d ∧ d < 3 * m := by
  simp only [pool, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    omega
  · rintro ⟨h₁, h₂⟩
    exact ⟨d - m, by omega, by omega⟩

private theorem mem_pairs {m : ℕ} {p : List ℕ} :
    p ∈ pairs m ↔ ∃ a b, p = [a, b] ∧ a < b ∧ m ≤ a ∧ b < 3 * m := by
  simp only [pairs, List.mem_flatMap, List.mem_map, List.mem_filter, mem_pool, decide_eq_true_eq]
  constructor
  · rintro ⟨a, ⟨ha, -⟩, b, ⟨⟨-, hb⟩, hab⟩, rfl⟩
    exact ⟨a, b, rfl, hab, ha, hb⟩
  · rintro ⟨a, b, rfl, hab, ha, hb⟩
    exact ⟨a, ⟨ha, by omega⟩, b, ⟨⟨by omega, hb⟩, hab⟩, rfl⟩

private theorem mem_triples {m : ℕ} {p : List ℕ} :
    p ∈ triples m ↔ ∃ a b c, p = [a, b, c] ∧ a < b ∧ b < c ∧ m ≤ a ∧ c < 3 * m := by
  simp only [triples, List.mem_flatMap, List.mem_map, List.mem_filter, mem_pool,
    decide_eq_true_eq]
  constructor
  · rintro ⟨a, ⟨ha, -⟩, b, ⟨⟨-, -⟩, hab⟩, c, ⟨⟨-, hc⟩, hbc⟩, rfl⟩
    exact ⟨a, b, c, rfl, hab, hbc, ha, hc⟩
  · rintro ⟨a, b, c, rfl, hab, hbc, ha, hc⟩
    exact ⟨a, ⟨ha, by omega⟩, b, ⟨⟨by omega, by omega⟩, hab⟩, c, ⟨⟨by omega, hc⟩, hbc⟩, rfl⟩

private theorem mem_occ {φ : CNF ℕ} {v j : ℕ} :
    j ∈ occ φ v ↔ j < φ.length ∧ v ∈ (φ.getD j []).map Prod.fst := by
  simp [occ]

private theorem nodup_occ (φ : CNF ℕ) (v : ℕ) : (occ φ v).Nodup :=
  List.nodup_range.filter _

/-- A set of the gadget of `O` is `O` padded by distinct dummy elements to three elements. -/
private theorem exists_pad_of_mem_gadget {m : ℕ} {O S : List ℕ} (h : S ∈ gadget m O) :
    ∃ P, S = O ++ P ∧ O.length + P.length = 3 ∧ (∀ d ∈ P, m ≤ d ∧ d < 3 * m) ∧ P.Nodup := by
  unfold gadget at h
  split_ifs at h with h₃ h₂ h₁
  · rw [List.mem_singleton] at h
    exact ⟨[], by simp [h], by simpa using h₃, by simp, List.nodup_nil⟩
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp h
    exact ⟨[d], rfl, by simpa using h₂, by simpa using mem_pool.mp hd, List.nodup_singleton d⟩
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
    obtain ⟨a, b, rfl, hab, ha, hb⟩ := mem_pairs.mp hp
    refine ⟨[a, b], rfl, by simpa using h₁, ?_, by simp; omega⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro d (rfl | rfl) <;> omega
  · simp at h

/-- Padding `O` by consecutive dummy elements gives a set of its gadget. -/
private theorem append_range_mem_gadget {m off : ℕ} {O : List ℕ} (h₁ : 1 ≤ O.length)
    (h₃ : O.length ≤ 3) (hoff : ∀ i < 3 - O.length, m + off + i < 3 * m) :
    O ++ (List.range (3 - O.length)).map (m + off + ·) ∈ gadget m O := by
  unfold gadget
  obtain h | h | h : O.length = 3 ∨ O.length = 2 ∨ O.length = 1 := by omega
  · simp [h]
  · simp only [h, beq_self_eq_true, ite_true, show (2 : ℕ) ≠ 3 by decide, beq_iff_eq, ite_false]
    exact List.mem_map.mpr ⟨m + off, mem_pool.mpr ⟨by omega, by simpa using hoff 0 (by omega)⟩,
      by simp⟩
  · simp only [h, beq_self_eq_true, ite_true, show (1 : ℕ) ≠ 3 by decide,
      show (1 : ℕ) ≠ 2 by decide, beq_iff_eq, ite_false]
    refine List.mem_map.mpr ⟨[m + off, m + off + 1], mem_pairs.mpr ⟨_, _, rfl, by omega,
      by omega, hoff 1 (by omega)⟩, ?_⟩
    simp [List.range_succ]

/-! ### Occurrences under the syntax guard -/

private theorem length_filter_range_getD {α : Type*} (l : List α) (d : α) (p : α → Bool) :
    ((List.range l.length).filter fun j => p (l.getD j d)).length = l.countP p := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.filter_cons, List.filter_map,
      List.countP_cons, ← ih]
    simp only [List.getD_cons_zero, Function.comp_def, List.getD_cons_succ]
    split <;> simp

private theorem vars_cons (c : Clause ℕ) (φ : CNF ℕ) :
    CNF.vars (c :: φ) = c.map Prod.fst ++ φ.vars := by
  simp [CNF.vars]

private theorem mem_vars {φ : CNF ℕ} {v : ℕ} : v ∈ φ.vars ↔ ∃ c ∈ φ, v ∈ c.map Prod.fst := by
  induction φ with
  | nil => simp [CNF.vars]
  | cons c φ ih => simp [vars_cons, ih]

/-- A variable occurs in at most as many clauses as it has occurrences. -/
private theorem length_occ_le_count (φ : CNF ℕ) (v : ℕ) : (occ φ v).length ≤ φ.vars.count v := by
  rw [occ, length_filter_range_getD φ [] fun c => decide (v ∈ c.map Prod.fst)]
  induction φ with
  | nil => simp
  | cons c φ ih =>
    rw [List.countP_cons, vars_cons, List.count_append]
    split_ifs with h
    · have := List.count_pos_iff.mpr (of_decide_eq_true h)
      omega
    · omega

private theorem getD_eq_getElem' {φ : CNF ℕ} {j : ℕ} (hj : j < φ.length) : φ.getD j [] = φ[j] :=
  List.getD_eq_getElem _ _ hj

private theorem mem_occ_of_mem {φ : CNF ℕ} {v j : ℕ} (hj : j < φ.length)
    (hv : v ∈ φ[j].map Prod.fst) :
    j ∈ occ φ v :=
  mem_occ.mpr ⟨hj, by rwa [getD_eq_getElem' hj]⟩

private theorem one_le_length_occ {φ : CNF ℕ} {v : ℕ} (hv : v ∈ φ.vars) : 1 ≤ (occ φ v).length := by
  obtain ⟨c, hc, hvc⟩ := mem_vars.mp hv
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
  exact List.length_pos_of_mem (mem_occ_of_mem hj hvc)

private theorem reduce_of_syntaxCheck {φ : CNF ℕ}
    (hs : PositiveOneInExactThreeSATThree.syntaxCheck φ = true) :
    reduce φ = φ.vars.flatMap (fun v => gadget φ.length (occ φ v)) ++ triples φ.length := by
  simp [reduce, hs]

private theorem lt_of_mem_reduce {φ : CNF ℕ}
    (hs : PositiveOneInExactThreeSATThree.syntaxCheck φ = true)
    {S : List ℕ} {x : ℕ} (hS : S ∈ reduce φ) (hx : x ∈ S) : x < 3 * φ.length := by
  rw [reduce_of_syntaxCheck hs, List.mem_append, List.mem_flatMap] at hS
  rcases hS with ⟨v, -, hS⟩ | hS
  · obtain ⟨P, rfl, -, hP, -⟩ := exists_pad_of_mem_gadget hS
    rcases List.mem_append.mp hx with hx | hx
    · have := (mem_occ.mp hx).1
      omega
    · exact (hP x hx).2
  · obtain ⟨a, b, c, rfl, hab, hbc, -, hc⟩ := mem_triples.mp hS
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    omega

/-- Every set of a reduced instance has exactly three elements. -/
private theorem isTriple_of_mem_reduce (φ : CNF ℕ) {S : List ℕ} (hS : S ∈ reduce φ) :
    S.length = 3 ∧ S.Nodup := by
  by_cases hs : PositiveOneInExactThreeSATThree.syntaxCheck φ = true
  · rw [reduce_of_syntaxCheck hs, List.mem_append, List.mem_flatMap] at hS
    rcases hS with ⟨v, -, hS⟩ | hS
    · obtain ⟨P, rfl, hlen, hP, hPn⟩ := exists_pad_of_mem_gadget hS
      refine ⟨by simpa using hlen, List.nodup_append.mpr ⟨nodup_occ φ v, hPn, ?_⟩⟩
      intro a ha b hb
      have := (mem_occ.mp ha).1
      have := (hP b hb).1
      omega
    · obtain ⟨a, b, c, rfl, hab, hbc, -, -⟩ := mem_triples.mp hS
      simp only [List.length_cons, List.length_nil, List.nodup_cons, List.mem_cons,
        List.not_mem_nil, or_false, List.nodup_nil, not_false_eq_true, and_true, true_and]
      omega
  · simp only [reduce, hs, Bool.false_eq_true, ite_false, noInstance, List.mem_cons,
      List.not_mem_nil, or_false] at hS
    rcases hS with rfl | rfl <;> decide

/-! ### Correctness of the reduction -/

/-- Under positive literals, the true literal occurrences of a clause are its true variables. -/
private theorem countP_eval_eq {σ : ℕ → Bool} {c : Clause ℕ} (hpos : ∀ l ∈ c, l.2 = true) :
    c.countP (Literal.eval σ) = (c.map Prod.fst).countP σ := by
  rw [List.countP_map]
  refine List.countP_congr fun l hl => ?_
  simp [Literal.eval, hpos l hl]

private theorem countP_eq_one_of_unique {l : List ℕ} {p : ℕ → Bool} {a : ℕ} (hl : l.Nodup)
    (ha : a ∈ l) (hpa : p a = true) (huniq : ∀ b ∈ l, p b = true → b = a) : l.countP p = 1 := by
  classical
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hl.filter p)]
  refine Finset.card_eq_one.mpr ⟨a, Finset.ext fun b => ?_⟩
  simp only [List.mem_toFinset, List.mem_filter, Finset.mem_singleton]
  exact ⟨fun ⟨hb, hpb⟩ => huniq b hb hpb, fun h => h ▸ ⟨ha, hpa⟩⟩

private theorem eq_of_countP_eq_one {l : List ℕ} {p : ℕ → Bool} (h : l.countP p = 1) {a b : ℕ}
    (ha : a ∈ l) (hpa : p a = true) (hb : b ∈ l) (hpb : p b = true) : a = b := by
  classical
  by_contra hab
  have hsub : ({a, b} : Finset ℕ) ⊆ (l.filter p).toFinset := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp [*]
  have := (Finset.card_le_card hsub).trans (List.toFinset_card_le _)
  rw [Finset.card_pair hab, ← List.countP_eq_length_filter, h] at this
  omega

/-- If the sets of `L` have no common element, each element of a set of `L` lies in exactly one
of them. -/
private theorem card_filter_toFinset_eq_one {L : List (List ℕ)} (hL : L.flatten.Nodup) {u : ℕ}
    (hu : u ∈ L.flatten) : (L.toFinset.filter (u ∈ ·)).card = 1 := by
  obtain ⟨S, hS, huS⟩ := List.mem_flatten.mp hu
  have hpw := (List.nodup_flatten.mp hL).2
  refine Finset.card_eq_one.mpr ⟨S, Finset.ext fun S' => ?_⟩
  simp only [Finset.mem_filter, List.mem_toFinset, Finset.mem_singleton]
  constructor
  · rintro ⟨hS', huS'⟩
    by_contra hne
    exact List.disjoint_left.mp (hpw.forall hS' hS hne) huS' huS
  · rintro rfl
    exact ⟨hS, huS⟩

/-- The clause indices of a set of a reduced instance are the occurrences of a variable: every
set containing a clause index comes from the gadget of a variable. -/
private theorem exists_occ_of_mem_reduce {φ : CNF ℕ}
    (hs : PositiveOneInExactThreeSATThree.syntaxCheck φ = true) {S : List ℕ} {j : ℕ}
    (hS : S ∈ reduce φ) (hjS : j ∈ S) (hj : j < φ.length) :
    ∃ w ∈ φ.vars, S.filter (· < φ.length) = occ φ w := by
  rw [reduce_of_syntaxCheck hs, List.mem_append, List.mem_flatMap] at hS
  rcases hS with ⟨w, hw, hS⟩ | hS
  · obtain ⟨P, rfl, -, hP, -⟩ := exists_pad_of_mem_gadget hS
    refine ⟨w, hw, ?_⟩
    rw [List.filter_append, List.filter_eq_self.mpr fun a ha => by
        simpa using (mem_occ.mp ha).1,
      List.filter_eq_nil_iff.mpr fun a ha => by simpa using (hP a ha).1, List.append_nil]
  · obtain ⟨a, b, c, rfl, hab, hbc, ha, -⟩ := mem_triples.mp hS
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hjS
    omega

/-- **Exact covers give exact-one assignments.** A variable is set true when a set of the cover
consists of its occurrences and it is the least variable with these occurrences. -/
theorem oneSatisfiable_of_mem {φ : CNF ℕ}
    (hs : PositiveOneInExactThreeSATThree.syntaxCheck φ = true)
    (h : reduce φ ∈ ThreeExactCover) : φ.OneSatisfiable := by
  classical
  obtain ⟨hcl, hpos, hcount⟩ := (PositiveOneInExactThreeSATThree.syntaxCheck_iff φ).mp hs
  rw [OneSAT.positiveCheck_iff] at hpos
  obtain ⟨-, D, hDC, hD⟩ := h
  set m := φ.length with hm
  let σ : ℕ → Bool := fun v => decide (∃ S ∈ D, S.filter (· < m) = occ φ v ∧
    ∀ w ∈ φ.vars, occ φ w = occ φ v → v ≤ w)
  refine ⟨σ, ?_⟩
  simp only [CNF.evalOne, List.all_eq_true, Clause.evalOne, beq_iff_eq]
  intro c hc
  rw [countP_eval_eq (hpos c hc)]
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
  have hvars : ∀ v ∈ φ[j].map Prod.fst, v ∈ φ.vars := fun v hv => mem_vars.mpr ⟨_, hc, hv⟩
  -- the clause index `j` is covered by exactly one set `S₀` of the cover
  obtain ⟨w, hw⟩ : ∃ w, w ∈ φ[j].map Prod.fst :=
    List.exists_mem_of_length_pos (l := φ[j].map Prod.fst)
      (by rw [List.length_map, (hcl _ hc).1]; omega)
  have hjw := mem_occ_of_mem hj hw
  have hocc₁ := one_le_length_occ (hvars w hw)
  have hocc₃ := (length_occ_le_count φ w).trans (hcount w)
  have hjC : j ∈ (reduce φ).flatten := by
    refine List.mem_flatten.mpr ⟨occ φ w ++ (List.range (3 - (occ φ w).length)).map (m + 0 + ·),
      ?_, List.mem_append_left _ hjw⟩
    rw [reduce_of_syntaxCheck hs]
    refine List.mem_append_left _ (List.mem_flatMap.mpr ⟨w, hvars w hw, ?_⟩)
    exact append_range_mem_gadget (off := 0) hocc₁ hocc₃ fun i hi => by omega
  obtain ⟨S₀, hS₀⟩ := Finset.card_eq_one.mp (hD j hjC)
  have hmem : S₀ ∈ D.filter (j ∈ ·) := hS₀ ▸ Finset.mem_singleton_self S₀
  obtain ⟨hS₀D, hjS₀⟩ := Finset.mem_filter.mp hmem
  have huniq : ∀ S ∈ D, j ∈ S → S = S₀ := fun S hS hjS =>
    Finset.mem_singleton.mp (hS₀ ▸ Finset.mem_filter.mpr ⟨hS, hjS⟩)
  obtain ⟨w', hw', hS₀occ⟩ := exists_occ_of_mem_reduce hs (hDC S₀ hS₀D) hjS₀ hj
  -- the true variable of the clause is the least one with the occurrences of `S₀`
  have hP : ∃ n, n ∈ φ.vars ∧ occ φ n = occ φ w' := ⟨w', hw', rfl⟩
  obtain ⟨hvs, hvocc⟩ := Nat.find_spec hP
  have hjocc : j ∈ occ φ (Nat.find hP) := by
    rw [hvocc, ← hS₀occ]
    exact List.mem_filter.mpr ⟨hjS₀, by simpa using hj⟩
  have hvj : Nat.find hP ∈ φ[j].map Prod.fst := by
    have := (mem_occ.mp hjocc).2
    rwa [getD_eq_getElem' hj] at this
  refine countP_eq_one_of_unique (hcl _ hc).2 hvj ?_ fun v hv hσv => ?_
  · refine decide_eq_true ⟨S₀, hS₀D, hS₀occ.trans hvocc.symm, fun u hu hocc => ?_⟩
    exact Nat.find_min' hP ⟨hu, hocc.trans hvocc⟩
  · obtain ⟨S, hSD, hSocc, hmin⟩ := of_decide_eq_true hσv
    have hjS : j ∈ S := (List.mem_filter.mp (hSocc ▸ mem_occ_of_mem hj hv)).1
    have hoccv : occ φ v = occ φ w' := by rw [← hSocc, huniq S hSD hjS, hS₀occ]
    exact le_antisymm (hmin _ hvs (hvocc.trans hoccv.symm))
      (Nat.find_min' hP ⟨hvars v hv, hoccv⟩)

/-- The occurrence lists `Os`, each padded to three elements by consecutive dummy elements, the
first from `m + off` on. -/
private def padBlocks (m : ℕ) : List (List ℕ) → ℕ → List (List ℕ)
  | [], _ => []
  | O :: Os, off =>
    (O ++ (List.range (3 - O.length)).map (m + off + ·)) :: padBlocks m Os (off + (3 - O.length))

/-- The number of dummy elements needed to pad the lists `Os`. -/
private def deficit (Os : List (List ℕ)) : ℕ := (Os.map fun O => 3 - O.length).sum

/-- `q` consecutive triples of dummy elements from `start` on. -/
private def restTriples (start q : ℕ) : List (List ℕ) :=
  (List.range q).map fun t => [start + 3 * t, start + 3 * t + 1, start + 3 * t + 2]

private theorem perm_flatten_padBlocks (m : ℕ) (Os : List (List ℕ)) (off : ℕ) :
    (padBlocks m Os off).flatten.Perm
      (Os.flatten ++ (List.range (deficit Os)).map (m + off + ·)) := by
  induction Os generalizing off with
  | nil => simp [padBlocks, deficit]
  | cons O Os ih =>
    have hr : (List.range (deficit (O :: Os))).map (m + off + ·) =
        (List.range (3 - O.length)).map (m + off + ·) ++
          (List.range (deficit Os)).map (m + (off + (3 - O.length)) + ·) := by
      rw [show deficit (O :: Os) = (3 - O.length) + deficit Os by simp [deficit],
        List.range_add, List.map_append, List.map_map]
      congr 1
      exact List.map_congr_left fun i _ => by simp only [Function.comp_apply]; omega
    simp only [padBlocks, List.flatten_cons, List.append_assoc, hr]
    refine List.Perm.append_left O ?_
    refine ((ih _).append_left _).trans ?_
    exact List.perm_iff_count.mpr fun a => by simp only [List.count_append]; omega

private theorem flatten_restTriples (start q : ℕ) :
    (restTriples start q).flatten = (List.range (3 * q)).map (start + ·) := by
  induction q with
  | zero => simp [restTriples]
  | succ q ih =>
    rw [restTriples, List.range_succ, List.map_append, List.flatten_append, ← restTriples, ih,
      show 3 * (q + 1) = 3 * q + 3 by ring, List.range_add, List.map_append, List.map_map]
    simp [List.range_succ, Function.comp_def, Nat.add_assoc]

private theorem deficit_add_sum (Os : List (List ℕ)) (h : ∀ O ∈ Os, O.length ≤ 3) :
    deficit Os + (Os.map List.length).sum = 3 * Os.length := by
  induction Os with
  | nil => simp [deficit]
  | cons O Os ih =>
    have h₀ := h O List.mem_cons_self
    have := ih fun O' hO' => h O' (List.mem_cons_of_mem _ hO')
    simp only [deficit, List.map_cons, List.sum_cons, List.length_cons] at this ⊢
    omega

private theorem length_le_sum (Os : List (List ℕ)) (h : ∀ O ∈ Os, 1 ≤ O.length) :
    Os.length ≤ (Os.map List.length).sum := by
  induction Os with
  | nil => simp
  | cons O Os ih =>
    have h₀ := h O List.mem_cons_self
    have := ih fun O' hO' => h O' (List.mem_cons_of_mem _ hO')
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

private theorem mem_padBlocks {m : ℕ} {Os : List (List ℕ)} {off : ℕ} {S : List ℕ}
    (h : S ∈ padBlocks m Os off) :
    ∃ O ∈ Os, ∃ off', S = O ++ (List.range (3 - O.length)).map (m + off' + ·) := by
  induction Os generalizing off with
  | nil => simp [padBlocks] at h
  | cons O Os ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨O, List.mem_cons_self, off, rfl⟩
    · obtain ⟨O', hO', off', rfl⟩ := ih h
      exact ⟨O', List.mem_cons_of_mem _ hO', off', rfl⟩

/-- **Exact-one assignments give exact covers.** The true variables of the clauses have disjoint
occurrence lists covering all clause indices; padding them with distinct dummy elements and
covering the remaining dummy elements by triples gives an exact cover. -/
theorem mem_of_oneSatisfiable {φ : CNF ℕ}
    (hs : PositiveOneInExactThreeSATThree.syntaxCheck φ = true) (h : φ.OneSatisfiable) :
    reduce φ ∈ ThreeExactCover := by
  classical
  obtain ⟨hcl, hpos, hcount⟩ := (PositiveOneInExactThreeSATThree.syntaxCheck_iff φ).mp hs
  rw [OneSAT.positiveCheck_iff] at hpos
  obtain ⟨σ, hσ⟩ := h
  set m := φ.length with hm
  -- every clause has exactly one true variable
  have hone : ∀ j (hj : j < m), (φ[j].map Prod.fst).countP σ = 1 := fun j hj => by
    have := List.all_eq_true.mp hσ _ (List.getElem_mem hj)
    simpa [Clause.evalOne, countP_eval_eq (hpos _ (List.getElem_mem hj))] using this
  let T := φ.vars.dedup.filter fun v => σ v
  have hT : ∀ v, v ∈ T ↔ v ∈ φ.vars ∧ σ v = true := fun v => by simp [T]
  let Os := T.map (occ φ)
  have hOsle : ∀ O ∈ Os, 1 ≤ O.length ∧ O.length ≤ 3 := by
    simp only [Os, List.mem_map]
    rintro O ⟨v, hv, rfl⟩
    exact ⟨one_le_length_occ ((hT v).mp hv).1, (length_occ_le_count φ v).trans (hcount v)⟩
  have hmemj : ∀ {v j}, j ∈ occ φ v → ∃ hj : j < m, v ∈ φ[j].map Prod.fst := fun {v j} h => by
    obtain ⟨hj, hv⟩ := mem_occ.mp h
    exact ⟨hj, by rwa [getD_eq_getElem' hj] at hv⟩
  have hOs_nodup : Os.flatten.Nodup := by
    refine List.nodup_flatten.mpr ⟨by simp [Os, nodup_occ], ?_⟩
    refine List.pairwise_map.mpr
      (((List.nodup_dedup _).filter _).imp_of_mem fun {u v} hu hv huv => ?_)
    refine List.disjoint_left.mpr fun {j} hju hjv => huv ?_
    obtain ⟨hj, hu'⟩ := hmemj hju
    obtain ⟨_, hv'⟩ := hmemj hjv
    exact eq_of_countP_eq_one (hone j hj) hu' ((hT u).mp hu).2 hv' ((hT v).mp hv).2
  have hOs_mem : ∀ j, j ∈ Os.flatten ↔ j < m := fun j => by
    constructor
    · intro h
      obtain ⟨O, hO, hjO⟩ := List.mem_flatten.mp h
      obtain ⟨v, -, rfl⟩ := List.mem_map.mp hO
      exact (hmemj hjO).1
    · intro hj
      obtain ⟨v, hv, hσv⟩ := List.countP_pos_iff.mp (by rw [hone j hj]; omega)
      exact List.mem_flatten.mpr ⟨occ φ v, List.mem_map.mpr
        ⟨v, (hT v).mpr ⟨mem_vars.mpr ⟨_, List.getElem_mem hj, hv⟩, hσv⟩, rfl⟩,
        mem_occ_of_mem hj hv⟩
  have hperm_O : Os.flatten.Perm (List.range m) :=
    (List.perm_ext_iff_of_nodup hOs_nodup List.nodup_range).mpr fun j => by
      rw [hOs_mem, List.mem_range]
  have hsum : (Os.map List.length).sum = m := by
    rw [← List.length_flatten, hperm_O.length_eq, List.length_range]
  have hdef := deficit_add_sum Os fun O hO => (hOsle O hO).2
  have hTm := length_le_sum Os fun O hO => (hOsle O hO).1
  rw [hsum] at hdef hTm
  -- the exact cover
  let L := padBlocks m Os 0 ++ restTriples (m + deficit Os) (m - Os.length)
  have hL : L.flatten.Perm (List.range (3 * m)) := by
    have e₁ := ((perm_flatten_padBlocks m Os 0).trans (hperm_O.append_right _)).append
      (List.Perm.refl (restTriples (m + deficit Os) (m - Os.length)).flatten)
    rw [List.flatten_append]
    refine e₁.trans (List.Perm.of_eq ?_)
    rw [flatten_restTriples, List.append_assoc,
      show 3 * m = m + (deficit Os + 3 * (m - Os.length)) by omega, List.range_add,
      List.range_add, List.map_append, List.map_map]
    congr 1
    congr 1
    exact List.map_congr_left fun i _ => by simp only [Function.comp_apply]; omega
  have hLnodup : L.flatten.Nodup := hL.nodup_iff.mpr List.nodup_range
  have hLlt : ∀ S ∈ L, ∀ x ∈ S, x < 3 * m := fun S hS x hx =>
    List.mem_range.mp (hL.subset (List.mem_flatten.mpr ⟨S, hS, hx⟩))
  have hLC : ∀ S ∈ L, S ∈ reduce φ := by
    intro S hS
    rw [reduce_of_syntaxCheck hs]
    rcases List.mem_append.mp hS with hS' | hS'
    · obtain ⟨O, hO, off, rfl⟩ := mem_padBlocks hS'
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hO
      refine List.mem_append_left _ (List.mem_flatMap.mpr ⟨v, ((hT v).mp hv).1, ?_⟩)
      refine append_range_mem_gadget (hOsle _ hO).1 (hOsle _ hO).2 fun i hi => ?_
      exact hLlt _ hS _ (List.mem_append_right _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))
    · obtain ⟨t, -, rfl⟩ := List.mem_map.mp hS'
      refine List.mem_append_right _ (mem_triples.mpr ⟨_, _, _, rfl, by omega, by omega, by omega,
        hLlt _ hS _ (by simp)⟩)
  refine ⟨fun S hS => isTriple_of_mem_reduce φ hS, L.toFinset,
    fun S hS => hLC S (List.mem_toFinset.mp hS),
    fun u hu => card_filter_toFinset_eq_one hLnodup ?_⟩
  obtain ⟨S, hS, huS⟩ := List.mem_flatten.mp hu
  exact hL.symm.subset (List.mem_range.mpr (lt_of_mem_reduce hs hS huS))

private theorem noInstance_notMem : noInstance ∉ ThreeExactCover := by
  rintro ⟨-, D, hDC, hD⟩
  have hmem : ∀ S ∈ D, S = [0, 1, 2] ∨ S = [0, 1, 3] := fun S hS => by
    simpa [noInstance] using hDC S hS
  have h0 := hD 0 (by simp [noInstance])
  rw [Finset.filter_true_of_mem fun S hS => by rcases hmem S hS with rfl | rfl <;> simp] at h0
  obtain ⟨S, rfl⟩ := Finset.card_eq_one.mp h0
  rcases hmem S (Finset.mem_singleton_self S) with rfl | rfl
  · have h := hD 3 (by simp [noInstance])
    simp [Finset.filter_singleton] at h
  · have h := hD 2 (by simp [noInstance])
    simp [Finset.filter_singleton] at h

/-- The reduction is correct. -/
theorem reduce_mem_iff (φ : CNF ℕ) :
    reduce φ ∈ ThreeExactCover ↔ φ ∈ PositiveOneInExactThreeSATThree := by
  rw [PositiveOneInExactThreeSATThree.mem_iff_syntaxCheck]
  by_cases hs : PositiveOneInExactThreeSATThree.syntaxCheck φ = true
  · exact ⟨fun h => ⟨hs, oneSatisfiable_of_mem hs h⟩, fun h => mem_of_oneSatisfiable hs h.2⟩
  · rw [Bool.not_eq_true] at hs
    simp only [reduce, hs, Bool.false_eq_true, ↓reduceIte, false_and, iff_false]
    exact noInstance_notMem

end ThreeExactCover

open ThreeExactCover in
/-- 3XC is in NP: a certificate selects the sets of the exact cover. -/
theorem ThreeExactCover_mem_NP : ThreeExactCover ∈ NP encThreeExactCover := by
  have h := mem_NP_of_subsetWitness (enc := encThreeExactCover) (encγ := encList encNat)
    (vs := fun C => C) (check := check)
    (P := fun C D => (∀ S ∈ C, S.length = 3 ∧ S.Nodup) ∧ IsExactCover C D)
    (by fun_prop) computableInPolyTime_check fun C l hl _ => check_iff C l hl
  convert h using 1
  ext C
  simp only [ThreeExactCover, Set.mem_ofPred_eq]
  tauto

open ThreeExactCover in
/-- Positive exact-three exact-one SAT with at most three occurrences per variable reduces to
3XC. -/
theorem polyTimeReducible_PositiveOneInExactThreeSATThree_ThreeExactCover :
    PolyTimeReducible encCNF encThreeExactCover PositiveOneInExactThreeSATThree ThreeExactCover :=
  ⟨reduce, computableInPolyTime_reduce, fun φ => (reduce_mem_iff φ).symm⟩

/-- 3XC is NP-hard. -/
theorem ThreeExactCover_npHard : NPHard encThreeExactCover ThreeExactCover :=
  PositiveOneInExactThreeSATThree_npHard.trans
    polyTimeReducible_PositiveOneInExactThreeSATThree_ThreeExactCover

/-- **3-Exact Cover is NP-complete** [Goldreich, Proposition 2.25][Goldreich2006DraftR1]. -/
theorem ThreeExactCover_npComplete : NPComplete encThreeExactCover ThreeExactCover :=
  ⟨ThreeExactCover_mem_NP, ThreeExactCover_npHard⟩

end Cslib.Complexity
