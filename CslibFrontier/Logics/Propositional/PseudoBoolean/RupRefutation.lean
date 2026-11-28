/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.PseudoBoolean.Redundance
import CslibFrontier.Logics.Propositional.PseudoBoolean.CompileCuttingPlanes
import CslibFrontier.Logics.Propositional.PseudoBoolean.Fast
import CslibFrontier.Logics.Propositional.PseudoBoolean.RupComplete

/-!
# Refuting a database by a decision tree of `rup` steps

A database without a 0/1 solution, over the variables `vs`, is refuted by the decision tree that
splits on the variables of `vs` in order (`Cslib.Logic.PL.VeriPB.refuteSteps`). Each node of the
tree is the list `K` of the literals decided on the way to it, and derives by `rup` its *blocking
clause* `∑_{ℓ ∈ K} ¬ℓ ≥ 1` (`Cslib.Logic.PL.VeriPB.blocking`), which says that some decision of
`K` fails:

* at a leaf, `K` decides every variable of `vs`, and the hints are the negated clause, which puts
  the literals of `K` on the trail, and the first constraint of the database that the assignment
  of `K` violates, which then has negative slack;
* at an inner node, splitting on `x`, the hints are the negated clause and the clauses of the two
  children: the clause of `x :: K` propagates `¬x` under `K`, and the clause of `¬x :: K` is then
  in conflict.

The steps are in post-order, the children of a node before it, so the root clause `0 ≥ 1`, a
contradiction, comes last (`Cslib.Logic.PL.VeriPB.runSteps_refuteSteps`). The refutation has
`2 ^ (|vs| + 1) - 1` steps (`Cslib.Logic.PL.VeriPB.length_refuteSteps`), each a `rup` step of a
clause with at most `|vs|` literals, all of variables of `vs`, and at most three hints, each the
number of a constraint of the database or below `n + 2 ^ (|vs| + 1) - 1`
(`Cslib.Logic.PL.VeriPB.exists_eq_rup_of_mem_refuteSteps`). These counts of steps, literals and
hints do not depend on the constraints of the database. The length of the proof as text does,
through the digits of the numbers it prints: a hint at a leaf names a constraint of the database,
and a literal names its variable. This is the exponential, but total and simple, refutation strategy
that the producers of `CslibFrontier.Logics.Propositional.PseudoBoolean.Completeness` use: it
needs no cutting planes reasoning and is accepted for any database, including ones with repeated
variables in `vs` or unnormalized constraints.

## Main definitions

* `Cslib.Logic.PL.VeriPB.blocking`: the clause that some literal of a list is false.
* `Cslib.Logic.PL.VeriPB.refuteSteps`: the decision-tree refutation.

## Main results

* `Cslib.Logic.PL.VeriPB.runSteps_refuteSteps`: the refutation runs and names a contradiction.
* `Cslib.Logic.PL.VeriPB.length_refuteSteps`,
  `Cslib.Logic.PL.VeriPB.exists_eq_rup_of_mem_refuteSteps`: its numbers of steps, literals and
  hints.
-/

@[expose] public section

namespace Cslib.Logic.PL.VeriPB

open PBConstr

/-! ### Blocking clauses -/

/-- **The blocking clause** `∑_{ℓ ∈ ρ} ¬ℓ ≥ 1` of the literals `ρ`: some literal of `ρ` is false. -/
def blocking (ρ : List (Literal ℕ)) : PBConstr := Clause.toPB (ρ.map Std.Sat.Literal.negate)

/-- The blocking clause holds exactly when some literal of `ρ` is false. -/
theorem holds_blocking (σ : ℕ → Bool) (ρ : List (Literal ℕ)) :
    (blocking ρ).Holds σ ↔ ¬ Consistent σ ρ := by
  simp only [blocking, Clause.holds_toPB_iff, Clause.eval_eq_true_iff, List.mem_map,
    Consistent, not_forall]
  constructor
  · rintro ⟨_, ⟨l, hl, rfl⟩, h⟩
    refine ⟨l, hl, ?_⟩
    obtain ⟨v, b⟩ := l
    cases b <;> simp_all [Std.Sat.Literal.negate]
  · rintro ⟨l, hl, h⟩
    refine ⟨_, ⟨l, hl, rfl⟩, ?_⟩
    obtain ⟨v, b⟩ := l
    cases b <;> simp_all [Std.Sat.Literal.negate]

/-- The blocking clause of no literal is the contradiction `0 ≥ 1`. -/
private theorem isContradiction_normalize_blocking_nil :
    (blocking []).normalize.IsContradiction := by
  decide

/-! ### The tree -/

/-- The number of the first constraint of `db` that `σ` violates, and `0` if there is none. -/
private def violatedId (db : List (ℕ × PBConstr)) (σ : ℕ → Bool) : ℕ :=
  ((db.find? fun e => !decide (e.2.Holds σ)).map (·.1)).getD 0

/-- **The decision tree** below the decisions `K` over the variables `xs`, its first step numbered
`n`, with the leaf hints read from the database `db`: the trees of `x :: K` and `¬x :: K` over
the rest of the variables, then the blocking clause of `K` by `rup`. A tree over `k` variables has
`2 ^ (k + 1) - 1` steps. -/
private def treeSteps (db : List (ℕ × PBConstr)) : ℕ → List (Literal ℕ) → List ℕ → List Step
  | _, K, [] => [.rup (blocking K) [.neg, .id (violatedId db (assignOf K))]]
  | n, K, x :: xs =>
    let m := n + (2 ^ (xs.length + 1) - 1)
    treeSteps db n ((x, true) :: K) xs ++ treeSteps db m ((x, false) :: K) xs ++
      [.rup (blocking K) [.neg, .id (m - 1), .id (m + (2 ^ (xs.length + 1) - 1) - 1)]]

/-- **The decision-tree refutation** of the database `db`, whose next number is `n`, over the
variables `vs`. Its body, which calls the private recursive worker, is not exposed: clients that
evaluate it in the kernel import this module with `import all`. -/
@[no_expose]
def refuteSteps (db : List (ℕ × PBConstr)) (n : ℕ) (vs : List ℕ) : List Step :=
  treeSteps db n [] vs

/-! ### Size -/

private theorem one_le_size (k : ℕ) : 1 ≤ 2 ^ (k + 1) - 1 := by
  have := Nat.one_lt_two_pow (n := k + 1) (by omega)
  omega

private theorem size_succ (k : ℕ) : 2 ^ (k + 1 + 1) - 1 = 2 * (2 ^ (k + 1) - 1) + 1 := by
  have := Nat.one_le_two_pow (n := k + 1)
  rw [pow_succ]
  omega

/-- A tree over `k` variables has `2 ^ (k + 1) - 1` steps. -/
private theorem length_treeSteps (db : List (ℕ × PBConstr)) :
    ∀ (n : ℕ) (K : List (Literal ℕ)) (xs : List ℕ),
      (treeSteps db n K xs).length = 2 ^ (xs.length + 1) - 1
  | _, _, [] => rfl
  | n, K, x :: xs => by
    rw [treeSteps, List.length_append, List.length_append, length_treeSteps,
      length_treeSteps]
    simp only [List.length_cons, List.length_nil, size_succ]
    omega

/-- **The refutation has `2 ^ (|vs| + 1) - 1` steps.** -/
theorem length_refuteSteps (db : List (ℕ × PBConstr)) (n : ℕ) (vs : List ℕ) :
    (refuteSteps db n vs).length = 2 ^ (vs.length + 1) - 1 :=
  length_treeSteps db n [] vs

/-- The first violated constraint is `0` or the number of a constraint of the database. -/
private theorem violatedId_mem (db : List (ℕ × PBConstr)) (σ : ℕ → Bool) :
    violatedId db σ = 0 ∨ violatedId db σ ∈ db.map (·.1) := by
  unfold violatedId
  cases h : db.find? fun e => !decide (e.2.Holds σ) with
  | none => simp
  | some e => exact .inr (List.mem_map_of_mem (List.mem_of_find?_eq_some h))

/-- Each step of a tree is a `rup` step of a blocking clause of its decisions and of literals of
the variables below, with at most three hints, each the number of a constraint of the database or
below the number after the tree. -/
private theorem exists_eq_rup_of_mem_treeSteps (db : List (ℕ × PBConstr)) :
    ∀ (n : ℕ) (K : List (Literal ℕ)) (xs : List ℕ), ∀ st ∈ treeSteps db n K xs,
      ∃ K' hs, st = .rup (blocking K') hs ∧ K'.length ≤ K.length + xs.length ∧ hs.length ≤ 3 ∧
        (∀ l ∈ K', l ∈ K ∨ l.1 ∈ xs) ∧
        ∀ j, Hint.id j ∈ hs → j < n + (2 ^ (xs.length + 1) - 1) ∨ j ∈ db.map (·.1)
  | n, K, [], st, hst => by
    simp only [treeSteps, List.mem_singleton] at hst
    refine ⟨K, _, hst, by simp, by simp, fun l hl => .inl hl, fun j hj => ?_⟩
    simp only [List.mem_cons, reduceCtorEq, Hint.id.injEq, List.not_mem_nil, or_false,
      false_or] at hj
    subst hj
    rcases violatedId_mem db (assignOf K) with h | h
    · exact .inl (by simp [h])
    · exact .inr h
  | n, K, x :: xs, st, hst => by
    have hS := one_le_size xs.length
    have hsz : 2 ^ ((x :: xs).length + 1) - 1 = 2 * (2 ^ (xs.length + 1) - 1) + 1 := by
      rw [List.length_cons, size_succ]
    rw [hsz]
    simp only [treeSteps, List.mem_append, List.mem_singleton] at hst
    rcases hst with (hst | hst) | hst
    -- The root step first, then the two subtrees by the same argument.
    rotate_right
    · refine ⟨K, _, hst, by simp, by simp, fun l hl => .inl hl, fun j hj => .inl ?_⟩
      simp only [List.mem_cons, reduceCtorEq, Hint.id.injEq, List.not_mem_nil, or_false,
        false_or] at hj
      omega
    all_goals
      obtain ⟨K', hs, h, hK, hh, hl, hj⟩ := exists_eq_rup_of_mem_treeSteps db _ _ xs st hst
      refine ⟨K', hs, h, by simp at hK ⊢; omega, hh, fun l hl' => ?_, fun j hj' => ?_⟩
      · rcases hl l hl' with h | h
        · simp only [List.mem_cons] at h ⊢
          rcases h with rfl | h
          · exact .inr (.inl rfl)
          · exact .inl h
        · exact .inr (List.mem_cons_of_mem _ h)
      · rcases hj j hj' with h | h
        · exact .inl (by omega)
        · exact .inr h

/-- **Each step of the refutation is a `rup` step** of a blocking clause of at most `|vs|`
literals, each of a variable of `vs`, with at most three hints, each the number of a constraint
of `db` or below `n + 2 ^ (|vs| + 1) - 1`, the number after the refutation. -/
theorem exists_eq_rup_of_mem_refuteSteps {db : List (ℕ × PBConstr)} {n : ℕ} {vs : List ℕ}
    {st : Step} (h : st ∈ refuteSteps db n vs) :
    ∃ K hs, st = .rup (blocking K) hs ∧ K.length ≤ vs.length ∧ hs.length ≤ 3 ∧
      (∀ l ∈ K, l.1 ∈ vs) ∧
      ∀ j, Hint.id j ∈ hs → j < n + (2 ^ (vs.length + 1) - 1) ∨ j ∈ db.map (·.1) := by
  obtain ⟨K, hs, h, hK, hh, hl, hj⟩ := exists_eq_rup_of_mem_treeSteps db n [] vs st h
  exact ⟨K, hs, h, by simpa using hK, hh, fun l h => by simpa using hl l h, hj⟩

/-! ### Acceptance -/

private theorem runStep_rup {db : List (ℕ × PBConstr)} {n : ℕ} {c : PBConstr} {hs : List Hint}
    (h : rup db c hs = true) : runStep db n (.rup c hs) = some ((n, c.normalize) :: db, n + 1) := by
  simp [runStep, h]

/-- A trail containing an inconsistent list of literals is not consistent. -/
private theorem rupOk_of_not_trailConsistent {db : List (ℕ × PBConstr)} {neg : PBConstr}
    {hs : List Hint} {K : List (Literal ℕ)} (hK : ¬ TrailConsistent K) : RupOk db neg hs K :=
  fun _ hρ hKρ => absurd (fun l hl hn => hρ l (hKρ l hl) (hKρ _ hn)) hK

/-- The assignment of a consistent list of literals makes them true. -/
private theorem consistent_assignOf {K : List (Literal ℕ)} (hK : TrailConsistent K) :
    Consistent (assignOf K) K := by
  rintro ⟨v, b⟩ hl
  cases b
  · have : (v, true) ∉ K := hK _ hl
    simp [assignOf, this]
  · simp [assignOf, hl]

/-- **A constraint decided by the trail**: if a consistent list `K` of literals decides every
variable of `c` and its assignment violates `c`, propagation of `c` on any consistent trail
containing `K` is a conflict. -/
private theorem propagate_eq_none_of_decides {c : PBConstr} {K ρ : List (Literal ℕ)}
    (hK : TrailConsistent K) (hρ : TrailConsistent ρ) (hKρ : ∀ l ∈ K, l ∈ ρ)
    (hall : ∀ t ∈ c.terms, t.2 ∈ K ∨ Std.Sat.Literal.negate t.2 ∈ K)
    (hc : ¬ c.Holds (assignOf K)) : propagate ρ c = none := by
  have hσ := consistent_assignOf hK
  have hf : (c.terms.filter fun t => !falsified ρ t) =
      c.terms.filter fun t => Literal.eval (assignOf K) t.2 := by
    refine List.filter_congr fun t ht => ?_
    rcases hall t ht with h | h
    · have hn : Std.Sat.Literal.negate t.2 ∉ ρ := hρ _ (hKρ _ h)
      simp [falsified, hn, hσ _ h]
    · have he := hσ _ h
      rw [Literal.eval_negate, Bool.not_eq_true'] at he
      simp [falsified, hKρ _ h, he]
  have hl := lhs_eq_coeffSum_filter (assignOf K) c.terms
  unfold Holds at hc
  have hs : slack ρ c < 0 := by
    unfold slack
    rw [hf, ← hl]
    omega
  simp [propagate, hs]

private theorem consistent_cons_iff {σ : ℕ → Bool} {l : Literal ℕ} {K : List (Literal ℕ)} :
    Consistent σ (l :: K) ↔ Literal.eval σ l = true ∧ Consistent σ K := by
  simp [Consistent]

/-- The negated blocking clause of `K` puts `K` on the trail. -/
private theorem rupOk_neg {db : List (ℕ × PBConstr)} {K : List (Literal ℕ)} {hs : List Hint}
    (h : RupOk db (blocking K).negate hs K) : RupOk db (blocking K).negate (.neg :: hs) [] :=
  RupOk.imp (L := K) rfl (nodup_vars_negate _) (fun σ _ hn => by
    rw [holds_negate, holds_blocking, not_not] at hn
    exact hn) (by simpa using h)

/-- **A leaf**: the blocking clause of a list `K` deciding every variable of the database is
accepted with the hints `~` and the number of a constraint that the assignment of `K` violates. -/
private theorem rup_leaf {db₀ E : List (ℕ × PBConstr)} {n₀ : ℕ} {vs : List ℕ}
    (hid : IdOk db₀ n₀) (hvs : ∀ e ∈ db₀, e.2.vars ⊆ vs) (h : ¬ ∃ σ, AllHold σ db₀)
    (hE : ∀ e ∈ E, n₀ ≤ e.1) {K : List (Literal ℕ)}
    (hK : ∀ x ∈ vs, (x, true) ∈ K ∨ (x, false) ∈ K) :
    rup (E ++ db₀) (blocking K) [.neg, .id (violatedId db₀ (assignOf K))] = true := by
  refine rup_of_rupOk (rupOk_neg ?_)
  by_cases hc : TrailConsistent K
  swap
  · exact rupOk_of_not_trailConsistent hc
  obtain ⟨e, he, hne⟩ : ∃ e ∈ db₀, ¬ e.2.Holds (assignOf K) := by
    by_contra hne
    push Not at hne
    exact h ⟨_, hne⟩
  obtain ⟨e', he'⟩ := Option.isSome_iff_exists.1
    (List.find?_isSome.2 ⟨e, he, by simpa using hne⟩ :
      (db₀.find? fun e => !decide (e.2.Holds (assignOf K))).isSome)
  have hm := List.mem_of_find?_eq_some he'
  have hv : ¬ e'.2.Holds (assignOf K) := by simpa using List.find?_some he'
  have hlook : lookup (E ++ db₀) (violatedId db₀ (assignOf K)) = some e'.2 := by
    rw [violatedId, he', Option.map_some, Option.getD_some, lookup_append_of_notMem]
    · exact hid.lookup_eq hm
    · intro hi
      obtain ⟨e'', he'', hi⟩ := List.mem_map.1 hi
      have := hE e'' he''
      have := hid.lt e' hm
      omega
  intro ρ hρ hKρ
  have hconf : propagate ρ e'.2 = none := by
    refine propagate_eq_none_of_decides hc hρ (fun l hl => hKρ l (by simpa using hl)) ?_ hv
    intro t ht
    obtain ⟨a, v, b⟩ := t
    rcases hK v (hvs e' hm (List.mem_map_of_mem (f := termVar) ht)) with hv | hv <;>
      cases b <;> simp_all [Std.Sat.Literal.negate]
  simp [rupHints, resolve, hlook, hconf]

/-- **An inner node**: the blocking clause of `K` is accepted with the hints `~` and the blocking
clauses of `x :: K` and `¬x :: K`. -/
private theorem rup_node {db : List (ℕ × PBConstr)} {K : List (Literal ℕ)} {x a b : ℕ}
    (ha : lookup db a = some (blocking ((x, true) :: K)).normalize)
    (hb : lookup db b = some (blocking ((x, false) :: K)).normalize) :
    rup db (blocking K) [.neg, .id a, .id b] = true := by
  refine rup_of_rupOk (rupOk_neg ?_)
  refine RupOk.imp (L := [(x, false)]) ha (nodup_termVar_normalize _) (fun σ hσ hc => ?_) ?_
  · rw [holds_normalize, holds_blocking, consistent_cons_iff] at hc
    have hx : Literal.eval σ (x, true) = false := by
      by_contra hx
      exact hc ⟨Bool.not_eq_false _ ▸ hx, hσ⟩
    simp only [Literal.eval_mk, beq_eq_false_iff_ne, ne_eq, Bool.not_eq_true] at hx
    simp [Consistent, hx]
  · refine RupOk.conflict hb (nodup_termVar_normalize _) fun σ hσ hc => ?_
    rw [holds_normalize, holds_blocking] at hc
    exact hc fun l hl => hσ l (by simpa using hl)

/-- **The tree runs**: from a database extending `db₀` by constraints numbered from `n₀` on, the
tree below the decisions `K` over `xs`, where `K` and `xs` together cover `vs`, adds constraints
numbered from `n` on and ends with the blocking clause of `K`. -/
private theorem runSteps_treeSteps {db₀ : List (ℕ × PBConstr)} {n₀ : ℕ} {vs : List ℕ}
    (hid : IdOk db₀ n₀) (hvs : ∀ e ∈ db₀, e.2.vars ⊆ vs) (h : ¬ ∃ σ, AllHold σ db₀) :
    ∀ (xs : List ℕ) (K : List (Literal ℕ)) (E : List (ℕ × PBConstr)) (n : ℕ),
      (∀ x ∈ vs, x ∈ xs ∨ (x, true) ∈ K ∨ (x, false) ∈ K) → IdOk (E ++ db₀) n →
      (∀ e ∈ E, n₀ ≤ e.1) → n₀ ≤ n →
      ∃ E' : List (ℕ × PBConstr),
        runSteps (E ++ db₀) n (treeSteps db₀ n K xs) =
          some ((n + (2 ^ (xs.length + 1) - 1) - 1, (blocking K).normalize) :: (E' ++ E ++ db₀),
            n + (2 ^ (xs.length + 1) - 1)) ∧
        IdOk ((n + (2 ^ (xs.length + 1) - 1) - 1, (blocking K).normalize) :: (E' ++ E ++ db₀))
          (n + (2 ^ (xs.length + 1) - 1)) ∧
        ∀ e ∈ E', n ≤ e.1
  | [], K, E, n, hcov, hidE, hE, _ => by
    have hK : ∀ x ∈ vs, (x, true) ∈ K ∨ (x, false) ∈ K := fun x hx => by
      simpa using hcov x hx
    refine ⟨[], ?_, ?_, by simp⟩
    · rw [treeSteps, runSteps, runStep_rup (rup_leaf hid hvs h hE hK)]
      simp [runSteps]
    · simpa using hidE.cons le_rfl (blocking K).normalize
  | x :: xs, K, E, n, hcov, hidE, hE, hn => by
    have hS1 := one_le_size xs.length
    have hsz : 2 ^ ((x :: xs).length + 1) - 1 = 2 * (2 ^ (xs.length + 1) - 1) + 1 := by
      rw [List.length_cons, size_succ]
    obtain ⟨E₁, hrun₁, hid₁, hE₁⟩ := runSteps_treeSteps hid hvs h xs ((x, true) :: K) E n
      (fun y hy => by
        have := hcov y hy
        simp only [List.mem_cons] at this ⊢
        tauto) hidE hE hn
    obtain ⟨E₂, hrun₂, hid₂, hE₂⟩ := runSteps_treeSteps hid hvs h xs ((x, false) :: K)
      ((n + (2 ^ (xs.length + 1) - 1) - 1, (blocking ((x, true) :: K)).normalize) :: (E₁ ++ E))
      (n + (2 ^ (xs.length + 1) - 1))
      (fun y hy => by
        have := hcov y hy
        simp only [List.mem_cons] at this ⊢
        tauto) (by simpa using hid₁)
      (fun e he => by
        rcases List.mem_cons.1 he with rfl | he
        · simp only; omega
        · rcases List.mem_append.1 he with he | he
          · have := hE₁ e he; omega
          · exact hE e he) (by omega)
    rw [hsz]
    simp only [treeSteps]
    generalize 2 ^ (xs.length + 1) - 1 = S at *
    simp only [List.append_assoc, List.cons_append] at hrun₁ hrun₂ hid₂ ⊢
    set B₁ := (blocking ((x, true) :: K)).normalize
    set B₂ := (blocking ((x, false) :: K)).normalize
    set D₂ := (n + S + S - 1, B₂) :: (E₂ ++ (n + S - 1, B₁) :: (E₁ ++ (E ++ db₀)))
    have hlook₁ : lookup D₂ (n + S - 1) = some B₁ := by
      rw [lookup_cons, lookup_append_of_notMem, lookup_cons]
      · simp [show n + S + S - 1 ≠ n + S - 1 by omega]
      intro hi
      obtain ⟨e, he, hi⟩ := List.mem_map.1 hi
      have := hE₂ e he
      omega
    have hlook₂ : lookup D₂ (n + S + S - 1) = some B₂ := by
      simp [D₂, lookup_cons]
    have hnode := rup_node (db := D₂) (K := K) hlook₁ hlook₂
    have hidD : IdOk D₂ (n + S + S) := by
      simpa only [D₂, List.append_assoc, List.cons_append] using hid₂
    refine ⟨(n + S + S - 1, B₂) :: (E₂ ++ (n + S - 1, B₁) :: E₁), ?_, ?_, ?_⟩
    · rw [runSteps_append, hrun₁, Option.bind_some]
      simp only
      rw [runSteps_append, hrun₂, Option.bind_some]
      simp only [runSteps]
      rw [runStep_rup hnode]
      rw [show n + (2 * S + 1) - 1 = n + S + S by omega, show n + (2 * S + 1) = n + S + S + 1 by
        omega]
      simp [D₂]
    · have := hidD.cons (m := n + S + S) le_rfl (blocking K).normalize
      simp only [D₂, List.cons_append, List.append_assoc] at this ⊢
      rw [show n + (2 * S + 1) - 1 = n + S + S by omega, show n + (2 * S + 1) = n + S + S + 1 by
        omega]
      exact this
    · intro e he
      simp only [List.mem_cons, List.mem_append] at he
      rcases he with rfl | he | rfl | he
      · simp only; omega
      · have := hE₂ e he; omega
      · simp only; omega
      · exact hE₁ e he

/-- **The decision-tree refutation is accepted**: from a database `db` with distinct numbers
below `n`, over the variables `vs` and without a solution, the steps `refuteSteps db n vs` run and
reach a database that names the contradiction `0 ≥ 1` by the number of their last step,
`n + 2 ^ (|vs| + 1) - 2`. -/
theorem runSteps_refuteSteps {db : List (ℕ × PBConstr)} {n : ℕ} {vs : List ℕ} (hid : IdOk db n)
    (hvs : ∀ e ∈ db, e.2.vars ⊆ vs) (h : ¬ ∃ σ, AllHold σ db) :
    ∃ db', runSteps db n (refuteSteps db n vs) = some (db', n + (2 ^ (vs.length + 1) - 1)) ∧
      IdOk db' (n + (2 ^ (vs.length + 1) - 1)) ∧
      namesContra db' (n + (2 ^ (vs.length + 1) - 1) - 1) = true := by
  obtain ⟨E', hrun, hid', -⟩ := runSteps_treeSteps hid hvs h vs [] [] n (fun x hx => .inl hx)
    (by simpa using hid) (by simp) le_rfl
  refine ⟨_, by simpa only [refuteSteps, List.nil_append] using hrun, hid', ?_⟩
  simp [namesContra, lookup_cons, isContradiction_normalize_blocking_nil]

end Cslib.Logic.PL.VeriPB

end
