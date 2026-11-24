/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Algorithms.Lean.Query.Sort.LEQuery

/-!
# Synthesizing a comparison program from a finite table

The bounded search for small graphs in [PettieRamachandran2002], §4.1, can test trees as
it constructs them. At each node only rows compatible with the path so far need to be searched.
The output is a comparison program in CSLib's query model. The depth bound counts queries
on every legal table row.
-/

public section

namespace Cslib.Query.LEQuery

variable {E O X : Type} [DecidableEq O] [Inhabited O]

/-- Return a leaf precisely when all promised rows admit a common output. -/
@[expose] def leaf? (out : X → O) (rows : List X) : Option (FreeM (LEQuery E) O) :=
  match rows with
  | [] => some (.pure default)
  | x :: xs => if xs.all (fun y => decide (out y = out x)) then some (.pure (out x)) else none

private theorem leaf?_of_const {out : X → O} {rows : List X} {o : O}
    (same : ∀ x ∈ rows, out x = o) : (leaf? (E := E) out rows).isSome := by
  cases rows with
  | nil => rfl
  | cons x xs =>
    have a : ∀ y ∈ xs, out y = out x := fun y hy =>
      (same y (List.mem_cons_of_mem x hy)).trans (same x (List.mem_cons_self ..)).symm
    simpa [leaf?, List.all_eq_true] using a

private theorem leaf?_spec {out : X → O} {rows : List X} {p : FreeM (LEQuery E) O}
    (hp : leaf? out rows = some p) (x : X) (hx : x ∈ rows) (ask : E → E → Bool) :
    p.eval (oracleOf ask) = out x ∧ p.countQueries (oracleOf ask) = 0 := by
  cases rows with
  | nil => simp at hx
  | cons y ys =>
    simp only [leaf?] at hp
    split at hp
    next h =>
      obtain rfl := Option.some.inj hp
      rcases List.mem_cons.mp hx with rfl | hx
      · simp
      · simp [of_decide_eq_true ((List.all_eq_true.mp h) _ hx)]
    next => contradiction

/-- Combine two successful subtrees under a comparison. -/
@[expose] def join? (q : E × E) (yes no : Option (FreeM (LEQuery E) O)) :
    Option (FreeM (LEQuery E) O) := do
  let a ← yes
  let b ← no
  return .liftBind (.le q.1 q.2) (fun bit => if bit then a else b)

/-- Finite-table search up to the supplied depth. An empty promise has a constant solution.
Each allowed pair names one binary query. -/
@[expose] def boundedSearch (pairs : List (E × E)) (ask : X → E → E → Bool) (out : X → O) :
    ℕ → List X → Option (FreeM (LEQuery E) O)
  | 0, rows => leaf? out rows
  | d+1, rows => (leaf? out rows).orElse fun _ => pairs.findSome? fun q =>
      join? q (boundedSearch pairs ask out d (rows.filter fun r => ask r q.1 q.2))
        (boundedSearch pairs ask out d (rows.filter fun r => !(ask r q.1 q.2)))

/-- Any output of bounded search meets the answer and query budget on each supplied row. -/
theorem boundedSearch_spec {pairs : List (E × E)} {ask : X → E → E → Bool} {out : X → O}
    {d : ℕ} {rows : List X} {p : FreeM (LEQuery E) O} (hp : boundedSearch pairs ask out d rows = some p)
    {x : X} (hx : x ∈ rows) :
    p.eval (oracleOf (ask x)) = out x ∧ p.countQueries (oracleOf (ask x)) ≤ d := by
  induction d generalizing rows p with
  | zero =>
    obtain ⟨a,b⟩ := leaf?_spec hp x hx (ask x)
    exact ⟨a,b.le⟩
  | succ d ih =>
    rw [boundedSearch] at hp
    cases e : leaf? (E := E) out rows with
    | some a =>
      simp [e] at hp
      subst a
      obtain ⟨v,c⟩ := leaf?_spec e x hx (ask x)
      exact ⟨v,by omega⟩
    | none =>
      simp only [e, Option.orElse_none] at hp
      obtain ⟨q, _, hq⟩ := List.exists_of_findSome?_eq_some hp
      unfold join? at hq
      cases hy : boundedSearch pairs ask out d (rows.filter fun r => ask r q.1 q.2) <;>
        simp [hy] at hq
      next a =>
        cases hn : boundedSearch pairs ask out d (rows.filter fun r => !(ask r q.1 q.2)) <;>
          simp [hn] at hq
        next b =>
          subst p
          cases he : ask x q.1 q.2
          · obtain ⟨v,c⟩ := ih hn (List.mem_filter.mpr ⟨hx,by simp [he]⟩)
            simp [he,v]; omega
          · obtain ⟨v,c⟩ := ih hy (List.mem_filter.mpr ⟨hx,he⟩)
            simp [he,v]; omega

/-- If a comparison program computes the table with the indicated budget, bounded search
succeeds. The premise concerns actual query counts, including programs with unreachable
syntactically deep branches. -/
theorem boundedSearch_complete {pairs : List (E × E)} (all : ∀ q, q ∈ pairs)
    {ask : X → E → E → Bool} {out : X → O} {d : ℕ} {rows : List X}
    (p : FreeM (LEQuery E) O) (ok : ∀ x ∈ rows,
      p.eval (oracleOf (ask x)) = out x ∧ p.countQueries (oracleOf (ask x)) ≤ d) :
    (boundedSearch pairs ask out d rows).isSome := by
  induction d generalizing p rows with
  | zero =>
    cases p with
    | pure o => exact leaf?_of_const (o := o) fun x hx => (ok x hx).1.symm
    | liftBind op cont =>
      cases rows with
      | nil => rfl
      | cons x xs =>
        have h := (ok x (List.mem_cons_self ..)).2
        simp at h
  | succ d ih =>
    rw [boundedSearch]
    cases p with
    | pure o =>
      have h := leaf?_of_const (E := E) (o := o) (rows := rows) (out := out)
        (fun x hx => (ok x hx).1.symm)
      cases hh : leaf? (E := E) out rows <;> simp_all
    | liftBind op cont =>
      cases op with
      | le a b =>
        cases hleaf : leaf? (E := E) out rows with
        | some t => rfl
        | none =>
          simp only [Option.orElse_none]
          apply List.findSome?_isSome_iff.mpr
          refine ⟨(a,b),all _,?_⟩
          have split (bit : Bool) : (boundedSearch pairs ask out d
              (rows.filter fun x => ask x a b == bit)).isSome := by
            apply ih (cont bit)
            intro x hx
            obtain ⟨mem,answer⟩ := List.mem_filter.mp hx
            have h := ok x mem
            simp [beq_iff_eq.mp answer] at h
            exact ⟨h.1,by omega⟩
          have ht := split true
          have hf := split false
          simp at ht hf
          dsimp
          simp [join?, Option.isSome_bind, ht, hf]

/-- Search successive budgets, retaining the first successful program and its budget. -/
@[expose] def firstFeasible (run : ℕ → Option P) : ℕ → Option (ℕ × P)
  | 0 => (run 0).map (0, ·)
  | d + 1 => (firstFeasible run d).orElse fun _ => (run (d + 1)).map (d + 1, ·)

theorem firstFeasible_isSome (run : ℕ → Option P) (d : ℕ) (hit : (run d).isSome) :
    (firstFeasible run d).isSome := by
  cases d with
  | zero => simpa [firstFeasible] using hit
  | succ d => cases h : firstFeasible run d <;> simp_all [firstFeasible]

theorem firstFeasible_spec {run : ℕ → Option P} {d k : ℕ} {p : P}
    (hit : firstFeasible run d = some (k, p)) :
    run k = some p ∧ k ≤ d ∧ ∀ j ≤ d, (run j).isSome → k ≤ j := by
  induction d with
  | zero =>
    cases h : run 0 <;> simp [firstFeasible, h] at hit
    obtain ⟨rfl, rfl⟩ := hit
    simp [h]
  | succ d ih =>
    cases h : firstFeasible run d with
    | some prev =>
      have eq : prev = (k,p) := by simpa [firstFeasible, h] using hit
      obtain ⟨valid, bound, small⟩ := ih (h.trans (congrArg some eq))
      refine ⟨valid, by omega, fun j hj good => ?_⟩
      by_cases h' : j ≤ d
      · exact small j h' good
      · omega
    | none =>
      cases e : run (d+1) <;> simp [firstFeasible,h,e] at hit
      obtain ⟨rfl, rfl⟩ := hit
      refine ⟨e, le_rfl, fun j hj good => ?_⟩
      by_contra! bad
      have hjd : j ≤ d := by omega
      have mono (a b : ℕ) (hab : a ≤ b) (ha : (firstFeasible run a).isSome) :
          (firstFeasible run b).isSome := by
        induction hab with
        | refl => exact ha
        | step _ ih =>
          cases eq : firstFeasible run _ <;> simp_all [firstFeasible]
      have yes := mono j d hjd (firstFeasible_isSome run j good)
      simp [h] at yes

/-- Query the finite list of edge pairs, recording the answers before evaluating a function
of the resulting comparison table. -/
@[expose] def queryPairs [DecidableEq E] (finish : (E → E → Bool) → O) :
    List (E × E) → (E → E → Bool) → FreeM (LEQuery E) O
  | [], known => .pure (finish known)
  | q :: qs, known => .liftBind (.le q.1 q.2) fun b =>
      queryPairs finish qs (fun x y => if (x,y) = q then b else known x y)

omit [DecidableEq O] [Inhabited O] in
theorem queryPairs_spec [DecidableEq E] (finish : (E → E → Bool) → O) (qs : List (E × E))
    (known ask : E → E → Bool) (h : ∀ x y, (x,y) ∉ qs → known x y = ask x y) :
    (queryPairs finish qs known).eval (oracleOf ask) = finish ask ∧
    (queryPairs finish qs known).countQueries (oracleOf ask) = qs.length := by
  induction qs generalizing known with
  | nil =>
    have eq : known = ask := funext fun x => funext fun y => h x y (by simp)
    simp [queryPairs, eq]
  | cons q qs ih =>
    obtain ⟨a,b⟩ := q
    have agree (x y : E) (absent : (x,y) ∉ qs) :
        (if (x,y) = (a,b) then ask a b else known x y) = ask x y := by
      by_cases eq : (x,y) = (a,b)
      · obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
        simp
      · simpa [eq] using h x y (by simp [eq, absent])
    obtain ⟨v,c⟩ := ih _ agree
    simp only [Prod.mk.injEq] at v c
    simp [queryPairs,v,c,Nat.add_comm]

end Cslib.Query.LEQuery
