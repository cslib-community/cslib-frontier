/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.DFS.SCC
public import CslibFrontier.Computability.Complexity.Problems.TwoSAT
import CslibFrontier.Foundations.Data.List.Fold

/-!
# 2-SAT via strongly connected components

The 2-SAT decision and witness-construction algorithm of
[Aspvall, Plass and Tarjan][AspvallPlassTarjan1979], built as a client of Kosaraju's strongly
connected components (`CslibFrontier.Algorithms.Lean.DFS.SCC`) and connected to
`Cslib.Complexity.TwoSAT` (`CslibFrontier.Computability.Complexity.Problems.TwoSAT`). For the
linear-time `O(n + |φ|)` word-RAM realization on `CNF (Fin n)`, see
`CslibFrontier.Algorithms.WordRAM.TwoSAT`.

Given a list `vs` covering a finite variable type `V` and a formula `φ : CNF V`:
1. `checkClauses φ` checks that every clause has length `1` or `2`;
2. `implicationAdj φ` builds the adjacency lists of `φ`'s implication graph (`a ∨ b` contributes
   `¬a → b` and `¬b → a`; a unit clause `a` contributes `¬a → a`), with at most `2 * |φ|` arcs;
3. `DFS.sccs` and `DFS.indexComponents` compute the topological component index `compIdx` of
   every literal;
4. `extractAssignment` rejects if some variable shares a component with its negation, and
   otherwise sets `σ v := decide (compIdx (v, false) < compIdx (v, true))`.

For formulas `φ : CNF ℕ` with arbitrary binary variable labels, `solveNat` compacts occurring
variables into `Fin (φ.vars.length + 1)`, deciding `φ ∈ Cslib.Complexity.TwoSAT` and producing a
satisfying assignment `ℕ → Bool`.

## Main definitions

* `Cslib.Algorithms.Lean.TwoSAT.implicationAdj`: implication-graph adjacency lists of a
  width-at-most-2 formula.
* `Cslib.Algorithms.Lean.TwoSAT.solve`: 2-SAT solver over a finite variable list `vs`.
* `Cslib.Algorithms.Lean.TwoSAT.solveFin`: specialization to `CNF (Fin n)`.
* `Cslib.Algorithms.Lean.TwoSAT.solveNat`: solver on `CNF ℕ` connected to
  `Cslib.Complexity.TwoSAT`.

## Main results

* `Cslib.Algorithms.Lean.TwoSAT.solve_eq_some`, `Cslib.Algorithms.Lean.TwoSAT.isSome_solve_iff`:
  soundness and completeness of `solve`.
* `Cslib.Algorithms.Lean.TwoSAT.solveFin_eq_some`,
  `Cslib.Algorithms.Lean.TwoSAT.isSome_solveFin_iff`: soundness and completeness on `CNF (Fin n)`.
* `Cslib.Algorithms.Lean.TwoSAT.isSome_solveNat_iff`,
  `Cslib.Algorithms.Lean.TwoSAT.solveNat_eq_some`: exact equivalence with
  `φ ∈ Cslib.Complexity.TwoSAT` and witness validity.

## References

* [B. Aspvall, M. F. Plass, R. E. Tarjan, *A linear-time algorithm for testing the truth of
  certain quantified boolean formulas*][AspvallPlassTarjan1979]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.TwoSAT

open Cslib.Logic.PL Cslib.Algorithms.Lean.DFS

variable {V : Type*}

/-! ### Clause-width guard and literal enumeration -/

/-- Predicate checking whether a clause has width `1` or `2`. -/
def isValidTwoClause (c : Clause V) : Bool :=
  decide (1 ≤ c.length ∧ c.length ≤ 2)

/-- Check that every clause of `φ` has length `1` or `2`. -/
def checkClauses (φ : CNF V) : Bool :=
  φ.foldl (fun ok c => ok && isValidTwoClause c) true

theorem checkClauses_eq_true_iff (φ : CNF V) :
    checkClauses φ = true ↔ (∀ c ∈ φ, c.length ≤ 2) ∧ [] ∉ φ := by
  simp only [checkClauses, foldl_and_eq_and_all, Bool.true_and, List.all_eq_true,
    isValidTwoClause, decide_eq_true_eq]
  exact ⟨fun h => ⟨fun c hc => (h c hc).2, fun hnil => by simpa using (h [] hnil).1⟩,
    fun ⟨hw, hnil⟩ c hc => ⟨List.length_pos_iff.2 fun h => hnil (h ▸ hc), hw c hc⟩⟩

/-- Enumerate both polarities `(v, false)` and `(v, true)` for each `v ∈ vs`. -/
def literalList : List V → List (Literal V)
  | [] => []
  | v :: vs => (v, false) :: (v, true) :: literalList vs

theorem length_literalList (vs : List V) : (literalList vs).length = 2 * vs.length := by
  induction vs with
  | nil => rfl
  | cons _ vs ih =>
    simp only [literalList, List.length_cons, ih]
    omega

theorem mem_literalList_iff {vs : List V} {ℓ : Literal V} :
    ℓ ∈ literalList vs ↔ ℓ.1 ∈ vs := by
  induction vs with
  | nil => simp [literalList]
  | cons v vs ih =>
    rcases ℓ with ⟨u, b⟩
    simp only [literalList, List.mem_cons, Prod.mk.injEq, ih]
    cases b <;> tauto

theorem mem_literalList {vs : List V} (hvs : ∀ v, v ∈ vs) (ℓ : Literal V) :
    ℓ ∈ literalList vs :=
  mem_literalList_iff.2 (hvs ℓ.1)

theorem nodup_literalList {vs : List V} (hnd : vs.Nodup) : (literalList vs).Nodup := by
  induction vs with
  | nil => simp [literalList]
  | cons v vs ih =>
    rw [List.nodup_cons] at hnd
    simp only [literalList, List.nodup_cons, List.mem_cons, Prod.mk.injEq, Bool.false_eq_true,
      and_false, false_or, mem_literalList_iff]
    exact ⟨hnd.1, hnd.1, ih hnd.2⟩

/-! ### Implication-graph adjacency lists -/

/-- Add the implication arcs of a single clause `c` of width `1` or `2`. -/
def addClauseEdges [DecidableEq V] (adj : Literal V → List (Literal V)) :
    Clause V → Literal V → List (Literal V)
  | [] => adj
  | [a] => Function.update adj a.negate (a :: adj a.negate)
  | [a, b] =>
    let adj₁ := Function.update adj a.negate (b :: adj a.negate)
    Function.update adj₁ b.negate (a :: adj₁ b.negate)
  | _ :: _ :: _ :: _ => adj

/-- Build the implication-graph adjacency lists of `φ`. -/
def implicationAdj [DecidableEq V] (φ : CNF V) : Literal V → List (Literal V) :=
  φ.foldl addClauseEdges (fun _ => [])

section ImplicationGraph

variable [DecidableEq V]

private theorem mem_addClauseEdges {adj : Literal V → List (Literal V)} {c : Clause V}
    (hc1 : 1 ≤ c.length) (hc2 : c.length ≤ 2) (ℓ ℓ' : Literal V) :
    ℓ' ∈ addClauseEdges adj c ℓ ↔
      ℓ' ∈ adj ℓ ∨ (ℓ.negate ∈ c ∧ ℓ' ∈ c ∧ ∀ m ∈ c, m = ℓ.negate ∨ m = ℓ') := by
  have hneg : ∀ a : Literal V, ℓ = a.negate ↔ ℓ.negate = a := fun a =>
    ⟨fun h => h ▸ negate_negate a, fun h => h ▸ (negate_negate ℓ).symm⟩
  rcases c with _ | ⟨a, _ | ⟨b, _ | ⟨d, cs⟩⟩⟩
  · simp at hc1
  · simp only [addClauseEdges, Function.update_apply, hneg, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq]
    obtain rfl | ha := eq_or_ne ℓ.negate a <;> simp [*, or_comm]
  · simp only [addClauseEdges, Function.update_apply, hneg, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq]
    obtain rfl | ha := eq_or_ne ℓ.negate a <;> obtain rfl | hb := eq_or_ne ℓ.negate b <;>
      simp [*] <;> grind
  · simp at hc2

private theorem foldl_addClauseEdges_mem :
    ∀ (cs : CNF V) (adj : Literal V → List (Literal V)),
      (∀ c ∈ cs, 1 ≤ c.length ∧ c.length ≤ 2) →
      ∀ (ℓ ℓ' : Literal V),
        ℓ' ∈ cs.foldl addClauseEdges adj ℓ ↔ ℓ' ∈ adj ℓ ∨ cs.Implies ℓ ℓ'
  | [], adj, _, ℓ, ℓ' => by simp [CNF.Implies]
  | c :: cs, adj, hcs, ℓ, ℓ' => by
    obtain ⟨hc, hrest⟩ := List.forall_mem_cons.1 hcs
    rw [List.foldl_cons, foldl_addClauseEdges_mem cs _ hrest, mem_addClauseEdges hc.1 hc.2]
    simp only [CNF.Implies, List.mem_cons, exists_eq_or_imp, or_assoc]

/-- When `φ` has no empty clause and all clauses have width at most `2`, `implicationAdj φ`
realizes `φ.Implies`. -/
theorem edge_implicationAdj_iff {φ : CNF V} (hw : ∀ c ∈ φ, c.length ≤ 2) (hnil : [] ∉ φ)
    (ℓ ℓ' : Literal V) :
    Edge (implicationAdj φ) ℓ ℓ' ↔ φ.Implies ℓ ℓ' := by
  have hcs : ∀ c ∈ φ, 1 ≤ c.length ∧ c.length ≤ 2 := fun c hc =>
    ⟨List.length_pos_iff.2 fun h => hnil (h ▸ hc), hw c hc⟩
  simpa [Edge, implicationAdj] using foldl_addClauseEdges_mem φ (fun _ => []) hcs ℓ ℓ'

private theorem sum_addClauseEdges_le [Fintype V] (adj : Literal V → List (Literal V))
    (c : Clause V) :
    (∑ w, (addClauseEdges adj c w).length) ≤ (∑ w, (adj w).length) + 2 := by
  rcases c with _ | ⟨a, _ | ⟨b, _ | ⟨d, cs⟩⟩⟩
  · exact Nat.le_add_right _ _
  · change (∑ w, (Function.update adj a.negate (a :: adj a.negate) w).length) ≤ _
    rw [sum_length_update_cons]
    omega
  · change (∑ w, (Function.update (Function.update adj a.negate (b :: adj a.negate))
        b.negate (a :: Function.update adj a.negate (b :: adj a.negate) b.negate) w).length) ≤ _
    rw [sum_length_update_cons, sum_length_update_cons]
  · exact Nat.le_add_right _ _

private theorem sum_foldl_addClauseEdges_le [Fintype V] :
    ∀ (cs : CNF V) (adj : Literal V → List (Literal V)),
      (∑ w, (cs.foldl addClauseEdges adj w).length) ≤ (∑ w, (adj w).length) + 2 * cs.length
  | [], adj => by simp
  | c :: cs, adj => by
    rw [List.foldl_cons, List.length_cons]
    have h₁ := sum_addClauseEdges_le adj c
    have h₂ := sum_foldl_addClauseEdges_le cs (addClauseEdges adj c)
    omega

theorem sum_length_implicationAdj_le [Fintype V] (φ : CNF V) :
    (∑ w, (implicationAdj φ w).length) ≤ 2 * φ.length := by
  simpa [implicationAdj] using sum_foldl_addClauseEdges_le φ (fun _ => [])

end ImplicationGraph

/-! ### Extracting the truth assignment from SCC topological indices -/

/-- Check that no variable in `vs` shares an SCC index with its negation, and return the
topological truth assignment `v ↦ decide (compIdx (v, false) < compIdx (v, true))`. -/
def extractAssignment (vs : List V) (compIdx : Literal V → ℕ) : Option (V → Bool) :=
  if vs.foldl (fun ok v => ok && decide (compIdx (v, true) ≠ compIdx (v, false))) true then
    some fun v => decide (compIdx (v, false) < compIdx (v, true))
  else
    none

/-! ### 2-SAT solver -/

/-- **Aspvall–Plass–Tarjan 2-SAT solver**: returns `some σ` satisfying `φ` when every clause of `φ`
has width at most `2` and `φ` is satisfiable, and `none` otherwise. -/
def solve [DecidableEq V] (vs : List V) (φ : CNF V) : Option (V → Bool) :=
  if checkClauses φ then
    let lits := literalList vs
    let adj := implicationAdj φ
    let comps := sccs adj lits
    let compIdx := indexComponents comps
    extractAssignment vs compIdx
  else
    none

section SolveCorrectness

variable [DecidableEq V] {vs : List V} {φ : CNF V}

omit [DecidableEq V] in
private theorem literal_false_lt {compIdx : Literal V → ℕ}
    (hne : ∀ v, compIdx (v, true) ≠ compIdx (v, false)) (ℓ : Literal V)
    (hf : Literal.eval (fun v => decide (compIdx (v, false) < compIdx (v, true))) ℓ = false) :
    compIdx ℓ < compIdx ℓ.negate := by
  rcases ℓ with ⟨v, b⟩
  cases b
  · simp only [Literal.eval, beq_false, Bool.not_eq_false', decide_eq_true_eq] at hf
    simpa [Std.Sat.Literal.negate] using hf
  · simp only [Literal.eval, beq_true, decide_eq_false_iff_not] at hf
    simpa [Std.Sat.Literal.negate] using Nat.lt_of_le_of_ne (Nat.le_of_not_lt hf) (hne v)

/-- **Soundness of `solve`**: whenever `solve vs φ = some σ` (with `vs` covering `V`), every clause
of `φ` has width at most `2` and `σ` satisfies `φ`. -/
theorem solve_eq_some (hvs : ∀ v, v ∈ vs) {σ : V → Bool} (h : solve vs φ = some σ) :
    (∀ c ∈ φ, c.length ≤ 2) ∧ φ.eval σ = true := by
  dsimp only [solve] at h
  split_ifs at h with hchk
  · obtain ⟨hw, hnil⟩ := (checkClauses_eq_true_iff φ).1 hchk
    set lits := literalList vs
    set adj := implicationAdj φ
    set comps := sccs adj lits
    set compIdx := indexComponents comps
    have hcond : IsSCCCondensation adj comps := isSCCCondensation_sccs (mem_literalList hvs)
    dsimp only [extractAssignment] at h
    split_ifs at h with hdist
    · obtain rfl := Option.some.inj h
      have hdist_all : ∀ v, compIdx (v, true) ≠ compIdx (v, false) := by
        rw [foldl_and_eq_and_all, Bool.true_and, List.all_eq_true] at hdist
        exact fun v => of_decide_eq_true (hdist v (hvs v))
      have hle : ∀ ℓ ℓ', φ.Implies ℓ ℓ' → compIdx ℓ ≤ compIdx ℓ' := fun _ _ h =>
        hcond.indexComponents_le_of_edge ((edge_implicationAdj_iff hw hnil _ _).2 h)
      refine ⟨hw, (CNF.eval_eq_true_iff _ _).2 fun c hc => ?_⟩
      have hc2 : c.length ≤ 2 := hw c hc
      rcases c with _ | ⟨a, _ | ⟨b, _ | ⟨d, cs⟩⟩⟩
      · exact absurd hc hnil
      · by_contra hceval
        have hlt := literal_false_lt hdist_all a
          (Bool.eq_false_iff.2 fun he => hceval (by simp [Clause.eval, he]))
        have := hle a.negate a ⟨[a], hc, by simp, by simp, fun m hm => .inl (by simpa using hm)⟩
        omega
      · by_contra hceval
        have hlta := literal_false_lt hdist_all a
          (Bool.eq_false_iff.2 fun he => hceval (by simp [Clause.eval, he]))
        have hltb := literal_false_lt hdist_all b
          (Bool.eq_false_iff.2 fun he => hceval (by simp [Clause.eval, he]))
        have := hle a.negate b ⟨[a, b], hc, by simp, by simp, fun m hm => by simpa using hm⟩
        have := hle b.negate a
          ⟨[a, b], hc, by simp, by simp, fun m hm => by simpa [or_comm] using hm⟩
        omega
      · simp at hc2

private theorem reach_iff_implies (hw : ∀ c ∈ φ, c.length ≤ 2) (hnil : [] ∉ φ)
    {ℓ ℓ' : Literal V} :
    Relation.ReflTransGen (Edge (implicationAdj φ)) ℓ ℓ' ↔
      Relation.ReflTransGen φ.Implies ℓ ℓ' := by
  simp only [funext₂ fun a b => propext (edge_implicationAdj_iff hw hnil a b)]

/-- **Completeness and characterization of `solve`**: when `vs` covers `V`, `(solve vs φ).isSome`
holds if and only if every clause of `φ` has width at most `2` and `φ` is satisfiable. -/
theorem isSome_solve_iff (hvs : ∀ v, v ∈ vs) :
    (solve vs φ).isSome ↔ (∀ c ∈ φ, c.length ≤ 2) ∧ φ.Satisfiable := by
  constructor
  · intro hs
    obtain ⟨σ, hσ⟩ := Option.isSome_iff_exists.1 hs
    exact (solve_eq_some hvs hσ).imp_right fun h => ⟨σ, h⟩
  · rintro ⟨hw, hsat⟩
    have hnil : [] ∉ φ := fun hnil => CNF.not_satisfiable_of_nil_mem hnil hsat
    have hchk : checkClauses φ = true := (checkClauses_eq_true_iff φ).2 ⟨hw, hnil⟩
    have hcond : IsSCCCondensation (implicationAdj φ) (sccs (implicationAdj φ) (literalList vs)) :=
      isSCCCondensation_sccs (mem_literalList hvs)
    simp only [solve, hchk, ↓reduceIte, extractAssignment]
    rw [ite_eq_left, Option.isSome_some]
    rw [foldl_and_eq_and_all, Bool.true_and, List.all_eq_true]
    intro v _
    refine decide_eq_true fun heq => ?_
    obtain ⟨h₁, h₂⟩ := (hcond.indexComponents_eq_iff (v, true) (v, false)).1 heq
    exact CNF.not_satisfiable_of_reach (ℓ := (v, true))
      ((reach_iff_implies hw hnil).1 h₁) ((reach_iff_implies hw hnil).1 h₂) hsat

end SolveCorrectness

/-! ### Specialization to `CNF (Fin n)` and bridge to `Cslib.Complexity.TwoSAT` -/

/-- 2-SAT solver on `CNF (Fin n)`. -/
def solveFin (n : ℕ) (φ : CNF (Fin n)) : Option (Fin n → Bool) :=
  solve (List.finRange n) φ

theorem solveFin_eq_some {n : ℕ} {φ : CNF (Fin n)} {σ : Fin n → Bool}
    (h : solveFin n φ = some σ) : (∀ c ∈ φ, c.length ≤ 2) ∧ φ.eval σ = true :=
  solve_eq_some List.mem_finRange h

theorem isSome_solveFin_iff (n : ℕ) (φ : CNF (Fin n)) :
    (solveFin n φ).isSome ↔ (∀ c ∈ φ, c.length ≤ 2) ∧ φ.Satisfiable :=
  isSome_solve_iff List.mem_finRange

/-- Map a natural-number variable to its compact index in `Fin (φ.vars.length + 1)`. -/
def toFinVar (φ : CNF ℕ) (v : ℕ) : Fin (φ.vars.length + 1) :=
  if h : φ.vars.idxOf v < φ.vars.length then ⟨φ.vars.idxOf v, Nat.lt_succ_of_lt h⟩ else 0

/-- Relabel `φ : CNF ℕ` into `CNF (Fin (φ.vars.length + 1))`. -/
def toFinCNF (φ : CNF ℕ) : CNF (Fin (φ.vars.length + 1)) :=
  φ.relabel (toFinVar φ)

/-- Solve a `CNF ℕ` instance of `Cslib.Complexity.TwoSAT`, returning `some σ` when `φ ∈ TwoSAT` and
`none` otherwise. -/
def solveNat (φ : CNF ℕ) : Option (ℕ → Bool) :=
  (solveFin (φ.vars.length + 1) (toFinCNF φ)).map fun σ v => σ (toFinVar φ v)

private theorem width_toFinCNF_iff (φ : CNF ℕ) :
    (∀ c ∈ toFinCNF φ, c.length ≤ 2) ↔ ∀ c ∈ φ, c.length ≤ 2 := by
  simp [toFinCNF, CNF.relabel, Clause.relabel]

private theorem satisfiable_toFinCNF_iff (φ : CNF ℕ) :
    (toFinCNF φ).Satisfiable ↔ φ.Satisfiable := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨σ ∘ toFinVar φ, by simpa only [toFinCNF, CNF.eval_relabel] using hσ⟩
  · rintro ⟨τ, hτ⟩
    refine ⟨fun i => φ.vars[i.val]?.elim false τ, ?_⟩
    rw [toFinCNF, CNF.eval_relabel]
    refine (CNF.eval_congr fun v hv => ?_).trans hτ
    have hlt : φ.vars.idxOf v < φ.vars.length := List.idxOf_lt_length_of_mem hv
    simp [toFinVar, hlt]

/-- **Soundness of `solveNat`**: any returned assignment witnesses `φ ∈ Cslib.Complexity.TwoSAT`. -/
theorem solveNat_eq_some {φ : CNF ℕ} {σ : ℕ → Bool} (h : solveNat φ = some σ) :
    (∀ c ∈ φ, c.length ≤ 2) ∧ φ.eval σ = true := by
  obtain ⟨σ₀, hσ₀, rfl⟩ := Option.map_eq_some_iff.1 h
  exact (solveFin_eq_some hσ₀).imp (width_toFinCNF_iff φ).1
    (by simpa only [toFinCNF, CNF.eval_relabel, Function.comp_def] using ·)

/-- **Exact equivalence with `Cslib.Complexity.TwoSAT`**. -/
theorem isSome_solveNat_iff (φ : CNF ℕ) :
    (solveNat φ).isSome ↔ φ ∈ Cslib.Complexity.TwoSAT := by
  rw [solveNat, Option.isSome_map, isSome_solveFin_iff, width_toFinCNF_iff,
    satisfiable_toFinCNF_iff, Cslib.Complexity.mem_TwoSAT]

end Cslib.Algorithms.Lean.TwoSAT
