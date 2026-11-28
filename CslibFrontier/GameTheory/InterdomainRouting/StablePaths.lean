/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Card
import CslibFrontier.Foundations.Combinatorics.FunctionalGraph
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.FinCases

/-!
# The Stable Paths Problem and Interdomain Routing (BGP)

The **Stable Paths Problem** (`SPP`) models policy-based interdomain routing in the Border Gateway
Protocol (BGP) ([GriffinShepherdWilfong2002]; [FeigenbaumSchapiraShenker2007], Chapter 14).
A finite collection of autonomous systems (ASes) forms an undirected graph `G` with a distinguished
destination `d`. Each AS `u` specifies a set of permitted simple paths from `u` to `d` and a ranking
function `rank u : Option (List V) → ℕ` that places no path (`none`) strictly below every permitted
path and strictly orders permitted paths that use distinct next hops.

A path assignment `π : V → Option (List V)` is **stable** (`SPP.IsStable`) when `d` selects `[d]`
and every other AS `u` selects the highest-ranked permitted path `u :: q` extending a neighbor's
assigned path `π w = some q` (or `none` if no neighbor offers a permitted path). Equivalently,
stability is a fixed point of per-node best-response path selection
(`SPP.isStable_iff_bestResponse`).

A **dispute wheel** (`DisputeWheel`) is a cyclic preference conflict among ASes `u₀, …, u_{k-1}`
with permitted pivot paths `Rᵢ` and nonempty rim prefixes `Qᵢ` such that each `uᵢ` permits
`Qᵢ ++ R_{i+1}` and strictly prefers `Qᵢ ++ R_{i+1}` to `Rᵢ`.

## Main definitions

* `Cslib.GameTheory.InterdomainRouting.IsSimplePath`: a loopless path of adjacent vertices between
  two endpoints in a `SimpleGraph`.
* `Cslib.GameTheory.InterdomainRouting.SPP`: an instance of the Stable Paths Problem.
* `Cslib.GameTheory.InterdomainRouting.SPP.IsChoice`: paths available to an AS under an assignment.
* `Cslib.GameTheory.InterdomainRouting.SPP.IsStable`: a stable path assignment (pure Nash
  equilibrium of BGP path selection).
* `Cslib.GameTheory.InterdomainRouting.DisputeWheel`: a cyclic preference conflict in an `SPP`.
* `Cslib.GameTheory.InterdomainRouting.SPP.bestResponse`, `SPP.run`, `IsFair`: asynchronous
  per-node atomic best-response BGP dynamics ([FeigenbaumSchapiraShenker2007], Chapter 14) under a
  fair activation schedule.
* `Cslib.GameTheory.InterdomainRouting.badGadget`: the classic 4-node (`BAD GADGET`) instance with
  a dispute wheel and no stable path assignment.
* `Cslib.GameTheory.InterdomainRouting.disagree`: the classic 3-node (`DISAGREE`) instance with a
  dispute wheel and two distinct stable path assignments.

## Main results

* `Cslib.GameTheory.InterdomainRouting.SPP.exists_isStable_of_isEmpty_disputeWheel`:
  **Griffin–Shepherd–Wilfong existence** ([GriffinShepherdWilfong2002]): if an `SPP` has no
  dispute wheel, then a stable path assignment exists.
* `Cslib.GameTheory.InterdomainRouting.SPP.nonempty_disputeWheel_of_isStable_ne` and
  `Cslib.GameTheory.InterdomainRouting.SPP.existsUnique_isStable_of_isEmpty_disputeWheel`:
  **Griffin–Shepherd–Wilfong uniqueness** ([GriffinShepherdWilfong2002]): two distinct stable path
  assignments yield an explicit dispute wheel, so absence of a dispute wheel implies a unique
  stable path assignment.
* `Cslib.GameTheory.InterdomainRouting.SPP.exists_converges_of_isEmpty_disputeWheel`:
  **Griffin–Shepherd–Wilfong safety** ([GriffinShepherdWilfong2002]; atomic best-response model
  of [FeigenbaumSchapiraShenker2007], Chapter 14): without a dispute wheel, asynchronous per-node
  atomic best-response dynamics from the initial destination-only state converge under every fair
  activation schedule to the unique stable path assignment.
* `Cslib.GameTheory.InterdomainRouting.not_exists_isStable_badGadget`: `badGadget` has no stable
  path assignment.
* `Cslib.GameTheory.InterdomainRouting.exists_two_isStable_disagree`: `disagree` has two distinct
  stable path assignments.

## References

* [FeigenbaumSchapiraShenker2007]
* [GriffinShepherdWilfong2002]
-/

public section

namespace Cslib.GameTheory.InterdomainRouting

open Function

variable {V : Type*}

/-! ### Simple paths in a `SimpleGraph` -/

/-- A simple path from `u` to `v` in `G`, represented as its nonempty duplicate-free vertex list
starting at `u`, ending at `v`, with consecutive vertices adjacent in `G`. -/
@[expose] def IsSimplePath (G : SimpleGraph V) (u v : V) (p : List V) : Prop :=
  p.head? = some u ∧ p.getLast? = some v ∧ p.IsChain G.Adj ∧ p.Nodup

theorem IsSimplePath.ne_nil {G : SimpleGraph V} {u v : V} {p : List V}
    (hp : IsSimplePath G u v p) : p ≠ [] := by
  intro h
  have := hp.1
  simp [h] at this

theorem IsSimplePath.eq_singleton_of_eq {G : SimpleGraph V} {d : V} {p : List V}
    (hp : IsSimplePath G d d p) : p = [d] := by
  rcases hp with ⟨hhead, hlast, _, hnodup⟩
  cases p with
  | nil => simp at hhead
  | cons a t =>
    simp only [List.head?_cons, Option.some.injEq] at hhead
    cases hhead
    cases t with
    | nil => rfl
    | cons b r =>
      have hd_mem : d ∈ b :: r := by
        have h1 : (b :: r).getLast? = some d := by
          simpa only [List.getLast?_cons_cons] using hlast
        exact List.mem_of_getLast? h1
      exact ((List.nodup_cons.mp hnodup).1 hd_mem).elim

theorem IsSimplePath.length_le_card [Fintype V] {G : SimpleGraph V} {u v : V} {p : List V}
    (hp : IsSimplePath G u v p) : p.length ≤ Fintype.card V :=
  hp.2.2.2.length_le_card

private theorem isChain_adj_of_append {R : V → V → Prop} {q : List V} {x y : V} {t : List V}
    (h : (q ++ x :: y :: t).IsChain R) : R x y :=
  (List.isChain_cons_cons.mp h.right_of_append).1

private theorem exists_split_not_mem_mem {A : Finset V} :
    ∀ {p : List V} {u d : V}, p.head? = some u → p.getLast? = some d → u ∉ A → d ∈ A →
      ∃ Q x y t, p = Q ++ x :: y :: t ∧ x ∉ A ∧ y ∈ A
  | [], _, _, hhead, _, _, _ => by simp at hhead
  | [a], u, d, hhead, hlast, hu, hd => by
    simp only [List.head?_cons, Option.some.injEq] at hhead
    simp only [List.getLast?_singleton, Option.some.injEq] at hlast
    cases hhead; cases hlast
    exact (hu hd).elim
  | a :: b :: rest, u, d, hhead, hlast, hu, hd => by
    classical
    simp only [List.head?_cons, Option.some.injEq] at hhead
    cases hhead
    by_cases hb : b ∈ A
    · exact ⟨[], a, b, rest, rfl, hu, hb⟩
    · have hlast' : (b :: rest).getLast? = some d := by
        simpa only [List.getLast?_cons_cons] using hlast
      obtain ⟨Q, x, y, t, hsplit, hx, hy⟩ :=
        exists_split_not_mem_mem (p := b :: rest) rfl hlast' hb hd
      exact ⟨a :: Q, x, y, t, by simp [hsplit], hx, hy⟩

/-! ### The Stable Paths Problem (`SPP`) -/

/-- An instance of the Stable Paths Problem ([GriffinShepherdWilfong2002]): a finite undirected
graph of autonomous systems, a distinguished destination `dest`, per-AS permitted simple paths to
`dest`, and per-AS preference rankings (`0` for no path `none`; higher is preferred) satisfying
GSW strictness (distinct next hops at a node receive distinct ranks). -/
structure SPP (V : Type*) [Fintype V] [DecidableEq V] where
  /-- The undirected peering graph of autonomous systems. -/
  graph : SimpleGraph V
  /-- The distinguished destination autonomous system. -/
  dest : V
  /-- Permitted simple paths from each AS to `dest`. -/
  permitted : V → List V → Prop
  /-- Every permitted path at `u` is a simple path in `graph` from `u` to `dest`. -/
  permitted_isSimplePath : ∀ u p, permitted u p → IsSimplePath graph u dest p
  /-- The trivial one-vertex path `[dest]` is permitted at the destination. -/
  permitted_dest : permitted dest [dest]
  /-- Preference ranking (`0` for `none`; higher rank means strictly more preferred). -/
  rank : V → Option (List V) → ℕ
  /-- The empty route `none` has rank `0`. -/
  rank_none : ∀ u, rank u none = 0
  /-- Every permitted path is strictly preferred to `none`. -/
  rank_pos : ∀ u p, permitted u p → 0 < rank u (some p)
  /-- Strictness: equal-ranked permitted paths at `u` must have the same next hop. -/
  strict : ∀ u p₁ p₂, permitted u p₁ → permitted u p₂ →
    rank u (some p₁) = rank u (some p₂) → p₁.tail.head? = p₂.tail.head?

namespace SPP

variable [Fintype V] [DecidableEq V]

/-- At `dest`, the only permitted path is `[dest]`. -/
theorem permitted_dest_iff (S : SPP V) {p : List V} : S.permitted S.dest p ↔ p = [S.dest] :=
  ⟨fun hp => (S.permitted_isSimplePath S.dest p hp).eq_singleton_of_eq,
   fun hp => hp ▸ S.permitted_dest⟩

/-- Every permitted path at `u ≠ dest` has at least two vertices, with the second adjacent to
`u`. -/
theorem exists_cons_cons_of_permitted (S : SPP V) {u : V} {p : List V} (hu : u ≠ S.dest)
    (hp : S.permitted u p) :
    ∃ v t, p = u :: v :: t ∧ S.graph.Adj u v := by
  have hs := S.permitted_isSimplePath u p hp
  rcases hs with ⟨hhead, hlast, hchain, _⟩
  cases p with
  | nil => simp at hhead
  | cons a r =>
    simp only [List.head?_cons, Option.some.injEq] at hhead
    cases hhead
    cases r with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hlast
      exact (hu hlast).elim
    | cons v t =>
      exact ⟨v, t, rfl, (List.isChain_cons_cons.mp hchain).1⟩

/-- An option `o` is an available choice for `u` under path assignment `π`: either `none` (no
route), or `some (u :: q)` permitted at `u` extending some neighbor `w`'s assigned route `π w`. -/
@[expose] def IsChoice (S : SPP V) (π : V → Option (List V)) (u : V) (o : Option (List V)) : Prop :=
  o = none ∨
    ∃ p, o = some p ∧ S.permitted u p ∧ ∃ w q, S.graph.Adj u w ∧ π w = some q ∧ p = u :: q

theorem isChoice_none (S : SPP V) (π : V → Option (List V)) (u : V) : S.IsChoice π u none :=
  Or.inl rfl

/-- A path assignment `π` is **stable** if `dest` selects `[dest]` and every other AS selects a
highest-ranked path among its available choices under `π`. -/
@[expose] def IsStable (S : SPP V) (π : V → Option (List V)) : Prop :=
  π S.dest = some [S.dest] ∧
    ∀ u, u ≠ S.dest → S.IsChoice π u (π u) ∧ ∀ o, S.IsChoice π u o → S.rank u o ≤ S.rank u (π u)

/-- In a stable assignment, every assigned route `some p` is permitted at its node. -/
theorem IsStable.permitted_of_eq_some {S : SPP V} {π : V → Option (List V)} (hπ : S.IsStable π)
    {u : V} {p : List V} (h : π u = some p) : S.permitted u p := by
  by_cases hu : u = S.dest
  · subst hu
    rw [hπ.1] at h
    exact (Option.some.inj h) ▸ S.permitted_dest
  · rcases (hπ.2 u hu).1 with hnone | ⟨p', hp', hperm, _⟩
    · rw [h] at hnone; cases hnone
    · rw [h] at hp'; exact (Option.some.inj hp') ▸ hperm

/-- If every assigned path starts at its owning node (e.g. for any stable assignment), then two
choices at `u` of equal rank must be identical. -/
private theorem eq_of_isChoice_rank_eq (S : SPP V) {π : V → Option (List V)}
    (hhead : ∀ w q, π w = some q → q.head? = some w)
    {u : V} {o₁ o₂ : Option (List V)}
    (h₁ : S.IsChoice π u o₁) (h₂ : S.IsChoice π u o₂)
    (hr : S.rank u o₁ = S.rank u o₂) : o₁ = o₂ := by
  rcases h₁ with rfl | ⟨p₁, rfl, hp₁, w₁, q₁, _, hπ₁, rfl⟩
  · rcases h₂ with rfl | ⟨p₂, rfl, hp₂, _⟩
    · rfl
    · have hpos := S.rank_pos u p₂ hp₂
      rw [S.rank_none] at hr
      omega
  · rcases h₂ with rfl | ⟨p₂, rfl, hp₂, w₂, q₂, _, hπ₂, rfl⟩
    · have hpos := S.rank_pos u (u :: q₁) hp₁
      rw [S.rank_none] at hr
      omega
    · have hnext := S.strict u (u :: q₁) (u :: q₂) hp₁ hp₂ hr
      simp only [List.tail_cons] at hnext
      rw [hhead w₁ q₁ hπ₁, hhead w₂ q₂ hπ₂] at hnext
      have hw : w₁ = w₂ := Option.some.inj hnext
      subst hw
      rw [hπ₁] at hπ₂
      have hq : q₁ = q₂ := Option.some.inj hπ₂
      rw [hq]

/-- In a stable assignment, any path `π u = some p` follows `π` at every suffix along `p`. -/
private theorem IsStable.suffix_eq_some {S : SPP V} {π : V → Option (List V)} (hπ : S.IsStable π) :
    ∀ {p : List V} {u : V}, π u = some p →
      ∀ {q x t}, p = q ++ x :: t → π x = some (x :: t) := by
  intro p
  induction p with
  | nil =>
    intro u hu
    have hperm := hπ.permitted_of_eq_some hu
    exact ((S.permitted_isSimplePath u [] hperm).ne_nil rfl).elim
  | cons a r ih =>
    intro u hu q x t hsplit
    have hperm := hπ.permitted_of_eq_some hu
    have ha : a = u := Option.some.inj (S.permitted_isSimplePath u (a :: r) hperm).1
    cases ha
    cases q with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hsplit
      rcases hsplit with ⟨rfl, rfl⟩
      exact hu
    | cons a' q' =>
      simp only [List.cons_append, List.cons.injEq] at hsplit
      rcases hsplit with ⟨_, hr⟩
      have ha_ne : a ≠ S.dest := by
        intro hEq
        subst hEq
        have := S.permitted_dest_iff.mp hperm
        simp only [List.cons.injEq] at this
        rw [this.2] at hr
        exact List.append_ne_nil_of_right_ne_nil q' (List.cons_ne_nil x t) hr.symm
      rcases (hπ.2 a ha_ne).1 with hnone | ⟨p', hp', _, w, q₀, _, hπw, hp'eq⟩
      · rw [hu] at hnone; cases hnone
      · rw [hu] at hp'
        have h1 : a :: r = a :: q₀ := (Option.some.inj hp').trans hp'eq
        have hr_eq : r = q₀ := (List.cons.inj h1).2
        rw [← hr_eq] at hπw
        exact ih hπw hr

end SPP

/-! ### Dispute wheels -/

/-- A **dispute wheel** in an `SPP` instance ([GriffinShepherdWilfong2002];
[FeigenbaumSchapiraShenker2007], Chapter 14): a cyclic list of `size > 0` autonomous systems
`node i`, permitted pivot paths `pivot i`, and nonempty rim prefixes `rim i` such that each
`node i` permits `rim i ++ pivot (next i)` and strictly prefers it to `pivot i`. -/
structure DisputeWheel {V : Type*} [Fintype V] [DecidableEq V] (S : SPP V) where
  /-- Number of spokes in the dispute wheel. -/
  size : ℕ
  /-- A dispute wheel has at least one spoke (in fact at least two; see `two_le_size`). -/
  size_pos : 0 < size
  /-- The pivot autonomous system at each spoke. -/
  node : Fin size → V
  /-- The pivot path at each spoke, permitted at `node i`. -/
  pivot : Fin size → List V
  /-- The nonempty rim prefix from `node i` to just before `node (next i)`. -/
  rim : Fin size → List V
  /-- Every rim prefix is nonempty. -/
  rim_nonempty : ∀ i, rim i ≠ []
  /-- Each pivot path is permitted at its spoke node. -/
  pivot_permitted : ∀ i, S.permitted (node i) (pivot i)
  /-- Concatenating `rim i` with `pivot (next i)` yields a permitted path at `node i`. -/
  rim_pivot_permitted :
    ∀ i, S.permitted (node i) (rim i ++ pivot ⟨(i.val + 1) % size, Nat.mod_lt _ size_pos⟩)
  /-- Each spoke node strictly prefers its rim-plus-next-pivot path over its own pivot path. -/
  prefers :
    ∀ i, S.rank (node i) (some (pivot i)) <
      S.rank (node i) (some (rim i ++ pivot ⟨(i.val + 1) % size, Nat.mod_lt _ size_pos⟩))

namespace DisputeWheel

variable [Fintype V] [DecidableEq V] {S : SPP V}

/-- Cyclic successor index around a dispute wheel. -/
@[expose] def next (W : DisputeWheel S) (i : Fin W.size) : Fin W.size :=
  ⟨(i.val + 1) % W.size, Nat.mod_lt _ W.size_pos⟩

/-- Every spoke node of a dispute wheel differs from the destination. -/
theorem node_ne_dest (W : DisputeWheel S) (i : Fin W.size) : W.node i ≠ S.dest := by
  intro hEq
  have hperm := W.rim_pivot_permitted i
  rw [hEq, S.permitted_dest_iff] at hperm
  have hlen : (W.rim i ++ W.pivot (W.next i)).length = 1 := congrArg List.length hperm
  have hr : 0 < (W.rim i).length := List.length_pos_of_ne_nil (W.rim_nonempty i)
  have hp : 0 < (W.pivot (W.next i)).length :=
    List.length_pos_of_ne_nil
      (S.permitted_isSimplePath _ _ (W.pivot_permitted (W.next i))).ne_nil
  rw [List.length_append] at hlen
  omega

/-- Adjacent spoke nodes around a dispute wheel are distinct. -/
theorem node_ne_next (W : DisputeWheel S) (i : Fin W.size) :
    W.node i ≠ W.node (W.next i) := by
  intro hEq
  have hs := S.permitted_isSimplePath _ _ (W.rim_pivot_permitted i)
  have hnodup := hs.2.2.2
  have hhead_rim : (W.rim i).head? = some (W.node i) := by
    have h1 := hs.1
    rw [List.head?_append_of_ne_nil _ (W.rim_nonempty i)] at h1
    exact h1
  have hmem_rim : W.node i ∈ W.rim i := List.mem_of_head? hhead_rim
  have hhead_piv : (W.pivot (W.next i)).head? = some (W.node (W.next i)) :=
    (S.permitted_isSimplePath _ _ (W.pivot_permitted (W.next i))).1
  have hmem_piv : W.node i ∈ W.pivot (W.next i) := by
    rw [hEq]
    exact List.mem_of_head? hhead_piv
  exact (List.nodup_append.mp hnodup).2.2 _ hmem_rim _ hmem_piv rfl

/-- Every dispute wheel has at least two spokes. -/
theorem two_le_size (W : DisputeWheel S) : 2 ≤ W.size := by
  by_contra hlt
  have h1 : W.size = 1 := by have := W.size_pos; omega
  let i₀ : Fin W.size := ⟨0, W.size_pos⟩
  have hnext : W.next i₀ = i₀ := by
    apply Fin.ext
    simp [next, i₀, h1]
  exact W.node_ne_next i₀ (by rw [hnext])

end DisputeWheel

/-! ### Cycle extraction helper (reusing `Cslib.FunctionalGraph`) -/

private theorem exists_disputeWheel_of_step {V α : Type*} [Fintype V] [DecidableEq V]
    [Finite α] [Nonempty α] {S : SPP V}
    (nodeOf : α → V) (pivotOf : α → List V) (step : α → α) (rimOf : α → List V)
    (hpiv : ∀ a, S.permitted (nodeOf a) (pivotOf a))
    (hrim_ne : ∀ a, rimOf a ≠ [])
    (hrim_perm : ∀ a, S.permitted (nodeOf a) (rimOf a ++ pivotOf (step a)))
    (hpref : ∀ a, S.rank (nodeOf a) (some (pivotOf a)) <
      S.rank (nodeOf a) (some (rimOf a ++ pivotOf (step a)))) :
    Nonempty (DisputeWheel S) := by
  obtain ⟨a₀⟩ := ‹Nonempty α›
  let x₀ := step^[Cslib.FunctionalGraph.transientDepth step a₀] a₀
  let k := Cslib.FunctionalGraph.cycleLength step a₀
  have hk : 0 < k := Cslib.FunctionalGraph.cycleLength_pos step a₀
  have hper : step^[k] x₀ = x₀ := Cslib.FunctionalGraph.isPeriodicPt_cycleLength step a₀
  let cyc : Fin k → α := fun i => step^[i.val] x₀
  have hcyc_next : ∀ i : Fin k, step (cyc i) = cyc ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩ := by
    intro i
    change step (step^[i.val] x₀) = step^[(i.val + 1) % k] x₀
    rw [← Function.iterate_succ_apply' step i.val x₀, Nat.succ_eq_add_one]
    by_cases h : i.val + 1 < k
    · rw [Nat.mod_eq_of_lt h]
    · have heq : i.val + 1 = k := by omega
      rw [heq, Nat.mod_self, hper]
      rfl
  exact ⟨{
    size := k
    size_pos := hk
    node := fun i => nodeOf (cyc i)
    pivot := fun i => pivotOf (cyc i)
    rim := fun i => rimOf (cyc i)
    rim_nonempty := fun i => hrim_ne (cyc i)
    pivot_permitted := fun i => hpiv (cyc i)
    rim_pivot_permitted := fun i => by
      rw [← hcyc_next i]
      exact hrim_perm (cyc i)
    prefers := fun i => by
      rw [← hcyc_next i]
      exact hpref (cyc i)
  }⟩

/-! ### Griffin–Shepherd–Wilfong uniqueness -/

namespace SPP

section Uniqueness

variable [Fintype V] [DecidableEq V]

/-- Given two distinct stable assignments `π₁` and `π₂` and a node `u` where they disagree with
`rank u (π₁ u) ≤ rank u (π₂ u)`, walking along `π₂ u` finds a disagreeing node `x` with nonempty
prefix `Q` such that `π₂ u = some (Q ++ R)` with `π₂ x = some R` and
`rank x (π₂ x) < rank x (π₁ x)`. -/
private theorem exists_flip_along_better (S : SPP V) {π₁ π₂ : V → Option (List V)}
    (h₁ : S.IsStable π₁) (h₂ : S.IsStable π₂)
    {u : V} (hne : π₁ u ≠ π₂ u) (hle : S.rank u (π₁ u) ≤ S.rank u (π₂ u)) :
    ∃ x Q R, Q ≠ [] ∧ π₁ x ≠ π₂ x ∧ π₂ x = some R ∧ π₂ u = some (Q ++ R) ∧
      S.rank x (π₂ x) < S.rank x (π₁ x) := by
  classical
  obtain ⟨p₂, hp₂⟩ : ∃ p₂, π₂ u = some p₂ := by
    cases h : π₂ u with
    | some p₂ => exact ⟨p₂, rfl⟩
    | none =>
      cases h' : π₁ u with
      | none => exact (hne (h'.trans h.symm)).elim
      | some p₁ =>
        have hpos := S.rank_pos u p₁ (h₁.permitted_of_eq_some h')
        rw [h, h', S.rank_none] at hle
        omega
  let A : Finset V := Finset.univ.filter fun v => π₁ v = π₂ v
  have huA : u ∉ A := by simp [A, hne]
  have hdA : S.dest ∈ A := by simp [A, h₁.1, h₂.1]
  have hsp := S.permitted_isSimplePath u p₂ (h₂.permitted_of_eq_some hp₂)
  obtain ⟨Q, x, y, t, hsplit, hxA, hyA⟩ := exists_split_not_mem_mem hsp.1 hsp.2.1 huA hdA
  have hx_ne : π₁ x ≠ π₂ x := by simpa [A] using hxA
  have hy_eq : π₁ y = π₂ y := by simpa [A] using hyA
  have hπ₂x : π₂ x = some (x :: y :: t) := h₂.suffix_eq_some hp₂ hsplit
  have hπ₂y : π₂ y = some (y :: t) :=
    h₂.suffix_eq_some hp₂ (by rw [hsplit, show Q ++ x :: y :: t = (Q ++ [x]) ++ y :: t by simp])
  have hπ₁y : π₁ y = some (y :: t) := hy_eq.trans hπ₂y
  have hadj : S.graph.Adj x y := isChain_adj_of_append (hsplit ▸ hsp.2.2.1)
  have hperm_x : S.permitted x (x :: y :: t) := h₂.permitted_of_eq_some hπ₂x
  have hchoice₁ : S.IsChoice π₁ x (some (x :: y :: t)) :=
    Or.inr ⟨x :: y :: t, rfl, hperm_x, y, y :: t, hadj, hπ₁y, rfl⟩
  have hx_ne_dest : x ≠ S.dest := by
    intro hEq; subst hEq; exact hx_ne (h₁.1.trans h₂.1.symm)
  have hle_x : S.rank x (π₂ x) ≤ S.rank x (π₁ x) := by
    rw [hπ₂x]
    exact (h₁.2 x hx_ne_dest).2 _ hchoice₁
  have hlt_x : S.rank x (π₂ x) < S.rank x (π₁ x) := by
    refine lt_of_le_of_ne hle_x ?_
    intro heq
    have hhead₁ : ∀ w q, π₁ w = some q → q.head? = some w := fun w q hw =>
      (S.permitted_isSimplePath w q (h₁.permitted_of_eq_some hw)).1
    have hEq := S.eq_of_isChoice_rank_eq hhead₁ hchoice₁ (h₁.2 x hx_ne_dest).1
      (by rwa [← hπ₂x])
    exact hx_ne (hEq.symm.trans hπ₂x.symm)
  have hQ_ne : Q ≠ [] := by
    rintro rfl
    obtain rfl : x = u := by simpa [hsplit] using hsp.1
    omega
  exact ⟨x, Q, x :: y :: t, hQ_ne, hx_ne, hπ₂x, by rwa [← hsplit], hlt_x⟩

/-- **Griffin–Shepherd–Wilfong uniqueness (contrapositive)** ([GriffinShepherdWilfong2002]):
any two distinct stable path assignments yield a dispute wheel. -/
theorem nonempty_disputeWheel_of_isStable_ne (S : SPP V) {π₁ π₂ : V → Option (List V)}
    (h₁ : S.IsStable π₁) (h₂ : S.IsStable π₂) (hne : π₁ ≠ π₂) :
    Nonempty (DisputeWheel S) := by
  classical
  let State := { s : Bool × V //
    π₁ s.2 ≠ π₂ s.2 ∧
    (if s.1 then (∃ R, π₁ s.2 = some R) ∧ S.rank s.2 (π₁ s.2) < S.rank s.2 (π₂ s.2)
     else (∃ R, π₂ s.2 = some R) ∧ S.rank s.2 (π₂ s.2) < S.rank s.2 (π₁ s.2)) }
  have hne_state : Nonempty State := by
    obtain ⟨u, hu⟩ : ∃ u, π₁ u ≠ π₂ u := by
      by_contra hall
      push Not at hall
      exact hne (funext hall)
    rcases le_total (S.rank u (π₁ u)) (S.rank u (π₂ u)) with hle | hle
    · obtain ⟨x, _, R, _, hx_ne, hπ₂x, _, hlt⟩ := exists_flip_along_better S h₁ h₂ hu hle
      exact ⟨⟨(false, x), hx_ne, ⟨R, hπ₂x⟩, hlt⟩⟩
    · obtain ⟨x, _, R, _, hx_ne, hπ₁x, _, hlt⟩ :=
        exists_flip_along_better S h₂ h₁ (Ne.symm hu) hle
      exact ⟨⟨(true, x), Ne.symm hx_ne, ⟨R, hπ₁x⟩, hlt⟩⟩
  have hpivot_exists : ∀ s : State, ∃ R, (if s.1.1 then π₁ s.1.2 else π₂ s.1.2) = some R := by
    intro s
    have h := s.2.2
    cases hb : s.1.1 <;> simp_all
  let pivotOf : State → List V := fun s => (hpivot_exists s).choose
  have hpivot_eq : ∀ s : State,
      (if s.1.1 then π₁ s.1.2 else π₂ s.1.2) = some (pivotOf s) :=
    fun s => (hpivot_exists s).choose_spec
  have hstep_exists : ∀ s : State,
      ∃ s' : State, ∃ Q : List V, Q ≠ [] ∧
        (if s.1.1 then π₂ s.1.2 else π₁ s.1.2) = some (Q ++ pivotOf s') := by
    intro ⟨⟨b, u⟩, hu_ne, hb⟩
    cases b with
    | true =>
      simp only [ite_true] at hb ⊢
      obtain ⟨x, Q, R', hQ, hx_ne, hπ₂x, hπ₂u, hlt⟩ :=
        exists_flip_along_better S h₁ h₂ hu_ne hb.2.le
      let s' : State := ⟨(false, x), hx_ne, ⟨R', hπ₂x⟩, hlt⟩
      have hp' : π₂ x = some (pivotOf s') := by simpa [s'] using hpivot_eq s'
      have hR' : R' = pivotOf s' := Option.some.inj (hπ₂x.symm.trans hp')
      exact ⟨s', Q, hQ, hR' ▸ hπ₂u⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hb ⊢
      obtain ⟨x, Q, R', hQ, hx_ne, hπ₁x, hπ₁u, hlt⟩ :=
        exists_flip_along_better S h₂ h₁ (Ne.symm hu_ne) hb.2.le
      let s' : State := ⟨(true, x), Ne.symm hx_ne, ⟨R', hπ₁x⟩, hlt⟩
      have hp' : π₁ x = some (pivotOf s') := by simpa [s'] using hpivot_eq s'
      have hR' : R' = pivotOf s' := Option.some.inj (hπ₁x.symm.trans hp')
      exact ⟨s', Q, hQ, hR' ▸ hπ₁u⟩
  let step : State → State := fun s => (hstep_exists s).choose
  let rimOf : State → List V := fun s => (hstep_exists s).choose_spec.choose
  have hbetter_eq : ∀ s : State,
      (if s.1.1 then π₂ s.1.2 else π₁ s.1.2) = some (rimOf s ++ pivotOf (step s)) :=
    fun s => (hstep_exists s).choose_spec.choose_spec.2
  exact exists_disputeWheel_of_step (fun s => s.1.2) pivotOf step rimOf
    (fun s => by
      have hp := hpivot_eq s
      split_ifs at hp
      exacts [h₁.permitted_of_eq_some hp, h₂.permitted_of_eq_some hp])
    (fun s => (hstep_exists s).choose_spec.choose_spec.1)
    (fun s => by
      have hbt := hbetter_eq s
      split_ifs at hbt
      exacts [h₂.permitted_of_eq_some hbt, h₁.permitted_of_eq_some hbt])
    (fun s => by
      have hp := hpivot_eq s
      have hbt := hbetter_eq s
      have hlt := s.2.2
      split_ifs at hp hbt hlt <;> rw [← hp, ← hbt] <;> exact hlt.2)

/-- Without a dispute wheel, an `SPP` has at most one stable path assignment. -/
theorem subsingleton_isStable_of_isEmpty_disputeWheel (S : SPP V)
    (hfree : IsEmpty (DisputeWheel S)) {π₁ π₂ : V → Option (List V)}
    (h₁ : S.IsStable π₁) (h₂ : S.IsStable π₂) : π₁ = π₂ := by
  by_contra hne
  obtain ⟨W⟩ := S.nonempty_disputeWheel_of_isStable_ne h₁ h₂ hne
  exact hfree.false W

end Uniqueness

/-! ### Griffin–Shepherd–Wilfong existence and fair best-response convergence (safety) -/

/-- Every nonempty suffix `x :: t` of `p` satisfies `π x = some (x :: t)`. -/
private def AllSuffixesMatch (π : V → Option (List V)) : List V → Prop
  | [] => True
  | x :: t => π x = some (x :: t) ∧ AllSuffixesMatch π t

/-- Every nonempty suffix `x :: t` of `p` starting at a node `x ∈ A` agrees with `π x`. -/
private def SuffixesAgreeOn (A : Finset V) (π : V → Option (List V)) : List V → Prop
  | [] => True
  | x :: t => (x ∈ A → π x = some (x :: t)) ∧ SuffixesAgreeOn A π t

private theorem suffixesAgreeOn_append_right {A : Finset V} {π : V → Option (List V)} :
    ∀ {q s : List V}, SuffixesAgreeOn A π (q ++ s) → SuffixesAgreeOn A π s
  | [], _, h => h
  | _ :: _, _, h => suffixesAgreeOn_append_right h.2

private theorem suffixesAgreeOn_of_allSuffixesMatch {A : Finset V} {π : V → Option (List V)} :
    ∀ {p : List V}, AllSuffixesMatch π p → SuffixesAgreeOn A π p
  | [], _ => trivial
  | _ :: _, h => ⟨fun _ => h.1, suffixesAgreeOn_of_allSuffixesMatch h.2⟩

section ExistenceAndSafety

variable [Fintype V] [DecidableEq V]

/-- Every nonempty suffix `x :: t` of `p` is permitted at `x`. -/
private def AllSuffixesPermitted (S : SPP V) : List V → Prop
  | [] => True
  | x :: t => S.permitted x (x :: t) ∧ AllSuffixesPermitted S t

private theorem allSuffixesPermitted_append_right (S : SPP V) :
    ∀ {q s : List V}, AllSuffixesPermitted S (q ++ s) → AllSuffixesPermitted S s
  | [], _, h => h
  | _ :: _, _, h => allSuffixesPermitted_append_right S h.2

/-- A path `p` from `u` survives relative to a settled subset `(A, π)` if `p` is permitted at `u`,
every suffix of `p` is permitted at its starting node, and every suffix of `p.tail` starting inside
`A` agrees with `π`. -/
private def Surviving (S : SPP V) (A : Finset V) (π : V → Option (List V))
    (u : V) (p : List V) : Prop :=
  S.permitted u p ∧ AllSuffixesPermitted S p ∧ SuffixesAgreeOn A π p.tail

/-- An intermediate state of the Griffin–Shepherd–Wilfong greedy elimination construction. -/
private structure ElimState (S : SPP V) where
  settled : Finset V
  assign : V → Option (List V)
  dest_mem : S.dest ∈ settled
  assign_dest : assign S.dest = some [S.dest]
  assign_some_of_mem : ∀ v ∈ settled, ∃ p,
    assign v = some p ∧ S.permitted v p ∧ AllSuffixesPermitted S p ∧
    (∀ x ∈ p, x ∈ settled) ∧ AllSuffixesMatch assign p
  assign_none_of_not_mem : ∀ v ∉ settled, assign v = none
  optimal : ∀ v ∈ settled, v ≠ S.dest → ∀ p,
    Surviving S settled assign v p → S.rank v (some p) ≤ S.rank v (assign v)

private def initElimState (S : SPP V) : ElimState S where
  settled := {S.dest}
  assign := fun u => if u = S.dest then some [S.dest] else none
  dest_mem := Finset.mem_singleton_self _
  assign_dest := by simp
  assign_some_of_mem := fun v hv => by
    have hv' : v = S.dest := Finset.mem_singleton.mp hv
    subst hv'
    exact ⟨[S.dest], by simp, S.permitted_dest, ⟨S.permitted_dest, trivial⟩,
      fun x hx => by simpa using hx, ⟨by simp, trivial⟩⟩
  assign_none_of_not_mem := fun v hv => by
    have hne : v ≠ S.dest := by simpa using hv
    simp [hne]
  optimal := fun v hv hvne => (hvne (Finset.mem_singleton.mp hv)).elim

/-- Direct candidates for an unsettled node `u ∉ st.settled` extending a settled neighbor. -/
private def IsDirectCand {S : SPP V} (st : ElimState S) (u : V) (p : List V) : Prop :=
  u ∉ st.settled ∧ S.permitted u p ∧ ∃ w ∈ st.settled, ∃ q,
    S.graph.Adj u w ∧ st.assign w = some q ∧ p = u :: q

/-- Extending a settled node's assigned route by a permitted first hop gives a surviving path. -/
private theorem surviving_cons {S : SPP V} {st : ElimState S} {u w : V} {q : List V}
    (hw : w ∈ st.settled) (hqw : st.assign w = some q) (hperm : S.permitted u (u :: q)) :
    Surviving S st.settled st.assign u (u :: q) := by
  obtain ⟨_, hpw, _, hall_w, _, hmatch_w⟩ := st.assign_some_of_mem w hw
  obtain rfl := Option.some.inj (hqw.symm.trans hpw)
  exact ⟨hperm, ⟨hperm, hall_w⟩, suffixesAgreeOn_of_allSuffixesMatch hmatch_w⟩

private theorem isDirectCand_surviving {S : SPP V} {st : ElimState S} {u : V} {p : List V}
    (hc : IsDirectCand st u p) : Surviving S st.settled st.assign u p := by
  rcases hc with ⟨_, hperm, w, hw, q, _, hqw, rfl⟩
  exact surviving_cons hw hqw hperm

/-- If no unsettled node has a direct candidate, `st.assign` is already stable. -/
private theorem isStable_of_no_directCand {S : SPP V} (st : ElimState S)
    (hempty : ∀ u p, ¬ IsDirectCand st u p) : S.IsStable st.assign := by
  refine ⟨st.assign_dest, fun u hu => ?_⟩
  by_cases huA : u ∈ st.settled
  · obtain ⟨p, hp, hperm, _, _, hmatch⟩ := st.assign_some_of_mem u huA
    obtain ⟨v, t, rfl, hadj⟩ := S.exists_cons_cons_of_permitted hu hperm
    have hchoice : S.IsChoice st.assign u (st.assign u) := by
      rw [hp]
      exact Or.inr ⟨u :: v :: t, rfl, hperm, v, v :: t, hadj, hmatch.2.1, rfl⟩
    refine ⟨hchoice, fun o ho => ?_⟩
    rcases ho with rfl | ⟨p', rfl, hp', w, q, _, hqw, rfl⟩
    · rw [S.rank_none]; exact Nat.zero_le _
    · have hwA : w ∈ st.settled := by_contra fun h => by simp [st.assign_none_of_not_mem w h] at hqw
      exact st.optimal u huA hu (u :: q) (surviving_cons hwA hqw hp')
  · have hnone := st.assign_none_of_not_mem u huA
    refine ⟨by rw [hnone]; exact S.isChoice_none _ _, fun o ho => ?_⟩
    rcases ho with rfl | ⟨p, rfl, hperm, w, q, hadj, hqw, rfl⟩
    · simp [hnone]
    · have hwA : w ∈ st.settled := by_contra fun h => by simp [st.assign_none_of_not_mem w h] at hqw
      exact (hempty u (u :: q) ⟨huA, hperm, w, hwA, q, hadj, hqw, rfl⟩).elim

/-- Every unsettled node with at least one direct candidate has a highest-ranked direct
candidate. -/
private theorem exists_bestDirectCand {S : SPP V} (st : ElimState S) {u : V}
    (h : ∃ p, IsDirectCand st u p) :
    ∃ p, IsDirectCand st u p ∧ ∀ p', IsDirectCand st u p' →
      S.rank u (some p') ≤ S.rank u (some p) := by
  classical
  let W : Finset V := Finset.univ.filter fun w =>
    w ∈ st.settled ∧ S.graph.Adj u w ∧ ∃ q, st.assign w = some q ∧ S.permitted u (u :: q)
  have hW : W.Nonempty := by
    obtain ⟨_, _, hperm, w, hw, q, hadj, hqw, rfl⟩ := h
    exact ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw, hadj, q, hqw, hperm⟩⟩
  let score : V → ℕ := fun w =>
    match st.assign w with
    | none => 0
    | some q => S.rank u (some (u :: q))
  obtain ⟨w₀, hw₀W, hw₀_max⟩ := W.exists_max_image score hW
  have hw₀_spec : w₀ ∈ st.settled ∧ S.graph.Adj u w₀ ∧
      ∃ q, st.assign w₀ = some q ∧ S.permitted u (u :: q) :=
    (Finset.mem_filter.mp hw₀W).2
  obtain ⟨hw₀A, hadj₀, q₀, hqw₀, hperm₀⟩ := hw₀_spec
  obtain ⟨_, huA, _⟩ := h
  refine ⟨u :: q₀, ⟨huA, hperm₀, w₀, hw₀A, q₀, hadj₀, hqw₀, rfl⟩, fun p' hp' => ?_⟩
  rcases hp' with ⟨_, hperm', w', hw'A, q', hadj', hqw', rfl⟩
  have hw'W : w' ∈ W :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw'A, hadj', q', hqw', hperm'⟩
  have hle := hw₀_max w' hw'W
  simpa [score, hqw', hqw₀] using hle

/-- Adding a node whose best direct candidate dominates all its surviving paths yields a larger
`ElimState`. -/
private def extendElimState {S : SPP V} (st : ElimState S) (u : V) (p : List V)
    (hdir : IsDirectCand st u p)
    (hopt : ∀ p', Surviving S st.settled st.assign u p' →
      S.rank u (some p') ≤ S.rank u (some p)) :
    ElimState S :=
  let settled' := insert u st.settled
  let assign' := Function.update st.assign u (some p)
  have huA : u ∉ st.settled := hdir.1
  have hu_ne_dest : u ≠ S.dest := fun h => huA (h ▸ st.dest_mem)
  have hsurv_mono : ∀ v q, Surviving S settled' assign' v q →
      Surviving S st.settled st.assign v q := by
    intro v q ⟨hperm, hall, hagr⟩
    refine ⟨hperm, hall, ?_⟩
    clear hperm hall
    generalize q.tail = l at hagr ⊢
    induction l with
    | nil => trivial
    | cons x t ih =>
      refine ⟨fun hx => ?_, ih hagr.2⟩
      have hx' : x ∈ settled' := Finset.mem_insert_of_mem hx
      have hx_ne : x ≠ u := fun h => huA (h ▸ hx)
      have h1 := hagr.1 hx'
      simpa [assign', Function.update_of_ne hx_ne] using h1
  have hall_p : AllSuffixesPermitted S p := (isDirectCand_surviving hdir).2.1
  have hsub_p : ∀ x ∈ p, x ∈ settled' := by
    rcases hdir with ⟨_, _, w, hw, q, _, hqw, rfl⟩
    obtain ⟨p_w, hpw, _, _, hsub_w, _⟩ := st.assign_some_of_mem w hw
    rw [hqw] at hpw
    have hq_eq : q = p_w := Option.some.inj hpw
    subst hq_eq
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hxq
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (hsub_w x hxq)
  have haux : ∀ r, (∀ x ∈ r, x ∈ st.settled) → AllSuffixesMatch st.assign r →
      AllSuffixesMatch assign' r := by
    intro r
    induction r with
    | nil => intro _ _; trivial
    | cons a t ih =>
      intro hsub hm
      have ha_ne : a ≠ u := fun h => huA (h ▸ hsub a List.mem_cons_self)
      exact ⟨by simpa [assign', Function.update_of_ne ha_ne] using hm.1,
        ih (fun x hx => hsub x (List.mem_cons_of_mem a hx)) hm.2⟩
  have hmatch_p : AllSuffixesMatch assign' p := by
    rcases hdir with ⟨_, _, w, hw, q, _, hqw, rfl⟩
    obtain ⟨p_w, hpw, _, _, hsub_w, hmatch_w⟩ := st.assign_some_of_mem w hw
    rw [hqw] at hpw
    have hq_eq : q = p_w := Option.some.inj hpw
    subst hq_eq
    refine ⟨by simp [assign'], ?_⟩
    exact haux q hsub_w hmatch_w
  { settled := settled'
    assign := assign'
    dest_mem := Finset.mem_insert_of_mem st.dest_mem
    assign_dest := by simp [assign', Function.update_of_ne hu_ne_dest.symm, st.assign_dest]
    assign_some_of_mem := fun v hv => by
      rcases Finset.mem_insert.mp hv with rfl | hvA
      · exact ⟨p, by simp [assign'], hdir.2.1, hall_p, hsub_p, hmatch_p⟩
      · have hv_ne : v ≠ u := fun h => huA (h ▸ hvA)
        obtain ⟨pv, hpv, hperm_v, hall_v, hsub_v, hmatch_v⟩ := st.assign_some_of_mem v hvA
        exact ⟨pv, by simpa [assign', Function.update_of_ne hv_ne] using hpv, hperm_v, hall_v,
          fun x hx => Finset.mem_insert_of_mem (hsub_v x hx), haux pv hsub_v hmatch_v⟩
    assign_none_of_not_mem := fun v hv => by
      have hv_ne : v ≠ u := fun h => hv (h ▸ Finset.mem_insert_self _ _)
      have hvA : v ∉ st.settled := fun h => hv (Finset.mem_insert_of_mem h)
      simpa [assign', Function.update_of_ne hv_ne] using st.assign_none_of_not_mem v hvA
    optimal := fun v hv hvne p' hp' => by
      have hp'_old := hsurv_mono v p' hp'
      rcases Finset.mem_insert.mp hv with rfl | hvA
      · simpa [assign'] using hopt p' hp'_old
      · have hv_ne : v ≠ u := fun h => huA (h ▸ hvA)
        simpa [assign', Function.update_of_ne hv_ne] using st.optimal v hvA hvne p' hp'_old }

/-- Splitting a surviving path from an unsettled node at its first transition into `st.settled`
yields a suffix starting at an unsettled node that is a direct candidate for `st`. -/
private theorem surviving_split_directCand {S : SPP V} (st : ElimState S) {v : V} {p : List V}
    (hvA : v ∉ st.settled) (hsurv : Surviving S st.settled st.assign v p) :
    ∃ Q x y t, p = Q ++ x :: y :: t ∧ x ∉ st.settled ∧ y ∈ st.settled ∧
      S.graph.Adj x y ∧ S.permitted x (x :: y :: t) ∧ st.assign y = some (y :: t) := by
  have hsp := S.permitted_isSimplePath v p hsurv.1
  obtain ⟨Q, x, y, t, hsplit, hxA, hyA⟩ :=
    exists_split_not_mem_mem hsp.1 hsp.2.1 hvA st.dest_mem
  have hadj : S.graph.Adj x y := isChain_adj_of_append (hsplit ▸ hsp.2.2.1)
  have hperm_x : S.permitted x (x :: y :: t) :=
    (allSuffixesPermitted_append_right S (q := Q) (s := x :: y :: t) (hsplit ▸ hsurv.2.1)).1
  have hπy : st.assign y = some (y :: t) := by
    cases Q with
    | nil =>
      rw [List.nil_append] at hsplit
      have hagr := hsurv.2.2
      rw [hsplit, List.tail_cons] at hagr
      exact hagr.1 hyA
    | cons a Q' =>
      rw [List.cons_append] at hsplit
      have hagr := hsurv.2.2
      rw [hsplit, List.tail_cons] at hagr
      have hagr' := suffixesAgreeOn_append_right
        (q := Q' ++ [x]) (s := y :: t) (by simpa only [List.append_assoc, List.cons_append,
          List.nil_append] using hagr)
      exact hagr'.1 hyA
  exact ⟨Q, x, y, t, hsplit, hxA, hyA, hadj, hperm_x, hπy⟩

/-- When a nonempty frontier of direct candidates exists and there is no dispute wheel, some
frontier node's best direct candidate dominates every surviving path for that node. -/
private theorem exists_extendable_of_isEmpty_disputeWheel {S : SPP V} (st : ElimState S)
    (hfree : IsEmpty (DisputeWheel S)) (hne : ∃ u p, IsDirectCand st u p) :
    ∃ u p, IsDirectCand st u p ∧
      ∀ p', Surviving S st.settled st.assign u p' → S.rank u (some p') ≤ S.rank u (some p) := by
  classical
  by_contra hno
  push Not at hno
  let Cand := { uw : V × V // uw.1 ∉ st.settled ∧ uw.2 ∈ st.settled ∧ S.graph.Adj uw.1 uw.2 ∧
    ∃ q, st.assign uw.2 = some q ∧ S.permitted uw.1 (uw.1 :: q) }
  have hCand : Nonempty Cand := by
    obtain ⟨u, _, huA, hperm, w, hwA, q, hadj, hqw, rfl⟩ := hne
    exact ⟨⟨(u, w), huA, hwA, hadj, q, hqw, hperm⟩⟩
  let pivotOf : Cand → List V := fun c =>
    c.1.1 :: c.2.2.2.2.choose
  have hpivot_dir : ∀ c : Cand, IsDirectCand st c.1.1 (pivotOf c) := fun c =>
    ⟨c.2.1, c.2.2.2.2.choose_spec.2, c.1.2, c.2.2.1, c.2.2.2.2.choose, c.2.2.2.1,
      c.2.2.2.2.choose_spec.1, rfl⟩
  have hstep_exists : ∀ c : Cand,
      ∃ c' : Cand, ∃ Q : List V, Q ≠ [] ∧
        S.permitted c.1.1 (Q ++ pivotOf c') ∧
        S.rank c.1.1 (some (pivotOf c)) < S.rank c.1.1 (some (Q ++ pivotOf c')) := by
    intro c
    obtain ⟨pbest, hbest_dir, hbest_max⟩ := exists_bestDirectCand st ⟨pivotOf c, hpivot_dir c⟩
    obtain ⟨p', hp'_surv, hlt_best⟩ := hno c.1.1 pbest hbest_dir
    have hlt : S.rank c.1.1 (some (pivotOf c)) < S.rank c.1.1 (some p') :=
      lt_of_le_of_lt (hbest_max (pivotOf c) (hpivot_dir c)) hlt_best
    obtain ⟨Q, x, y, t, hsplit, hxA, hyA, hadj, hperm_x, hπy⟩ :=
      surviving_split_directCand st c.2.1 hp'_surv
    have hQ_ne : Q ≠ [] := by
      intro hQ
      rw [hQ, List.nil_append] at hsplit
      have hsp := S.permitted_isSimplePath c.1.1 p' hp'_surv.1
      have hxu : x = c.1.1 := Option.some.inj (by simpa [hsplit] using hsp.1)
      have hdir' : IsDirectCand st c.1.1 p' :=
        ⟨c.2.1, hp'_surv.1, y, hyA, y :: t, hxu ▸ hadj, hπy, hxu ▸ hsplit⟩
      have hle := hbest_max p' hdir'
      omega
    let c' : Cand := ⟨(x, y), hxA, hyA, hadj, y :: t, hπy, hperm_x⟩
    have hpiv' : pivotOf c' = x :: y :: t := by
      have h1 : st.assign y = some c'.2.2.2.2.choose := c'.2.2.2.2.choose_spec.1
      have hq : c'.2.2.2.2.choose = y :: t := Option.some.inj (h1.symm.trans hπy)
      change x :: c'.2.2.2.2.choose = x :: y :: t
      rw [hq]
    refine ⟨c', Q, hQ_ne, ?_, ?_⟩
    · rw [hpiv', ← hsplit]; exact hp'_surv.1
    · rw [hpiv', ← hsplit]; exact hlt
  obtain ⟨W⟩ := exists_disputeWheel_of_step
    (fun c : Cand => c.1.1) pivotOf (fun c => (hstep_exists c).choose)
    (fun c => (hstep_exists c).choose_spec.choose)
    (fun c => (hpivot_dir c).2.1)
    (fun c => (hstep_exists c).choose_spec.choose_spec.1)
    (fun c => (hstep_exists c).choose_spec.choose_spec.2.1)
    (fun c => (hstep_exists c).choose_spec.choose_spec.2.2)
  exact hfree.false W

/-- **Griffin–Shepherd–Wilfong existence** ([GriffinShepherdWilfong2002]): if an `SPP` instance has
no dispute wheel, then it admits a stable path assignment. -/
theorem exists_isStable_of_isEmpty_disputeWheel (S : SPP V) (hfree : IsEmpty (DisputeWheel S)) :
    ∃ π, S.IsStable π := by
  suffices h : ∀ n (st : ElimState S), Fintype.card V - st.settled.card ≤ n → ∃ π, S.IsStable π by
    exact h (Fintype.card V) (initElimState S) (Nat.sub_le _ _)
  intro n
  induction n with
  | zero =>
    intro st hle
    have hcard : st.settled.card = Fintype.card V :=
      le_antisymm (Finset.card_le_univ _) (by omega)
    have hall : ∀ u, u ∈ st.settled := by simp [Finset.eq_univ_of_card st.settled hcard]
    exact ⟨st.assign, isStable_of_no_directCand st fun u _ hdir => hdir.1 (hall u)⟩
  | succ n ih =>
    intro st hle
    by_cases hne : ∃ u p, IsDirectCand st u p
    · obtain ⟨u, p, hdir, hopt⟩ := exists_extendable_of_isEmpty_disputeWheel st hfree hne
      let st' := extendElimState st u p hdir hopt
      have hcard' : st'.settled.card = st.settled.card + 1 := by
        dsimp only [st', extendElimState]
        exact Finset.card_insert_of_notMem hdir.1
      exact ih st' (by omega)
    · push Not at hne
      exact ⟨st.assign, isStable_of_no_directCand st hne⟩

/-- **Griffin–Shepherd–Wilfong theorem** ([GriffinShepherdWilfong2002]): if an `SPP` instance has no
dispute wheel, then it admits a unique stable path assignment. -/
theorem existsUnique_isStable_of_isEmpty_disputeWheel (S : SPP V)
    (hfree : IsEmpty (DisputeWheel S)) : ∃! π, S.IsStable π := by
  obtain ⟨π, hπ⟩ := S.exists_isStable_of_isEmpty_disputeWheel hfree
  exact ⟨π, hπ, fun π' hπ' => S.subsingleton_isStable_of_isEmpty_disputeWheel hfree hπ' hπ⟩

/-! ### Asynchronous best-response dynamics and safety -/

/-- The best-response path choice of node `u` given current assignment `π`. For `u = dest` this is
always `some [dest]`; for `u ≠ dest` it is a rank-maximizing available choice (unique whenever
neighbors hold routes starting at themselves). -/
noncomputable def bestResponse (S : SPP V) (π : V → Option (List V)) (u : V) : Option (List V) := by
  classical
  exact if u = S.dest then some [S.dest]
  else
    let W : Finset V := Finset.univ.filter fun w =>
      S.graph.Adj u w ∧ ∃ q, π w = some q ∧ S.permitted u (u :: q)
    if hW : W.Nonempty then
      let score : V → ℕ := fun w =>
        match π w with
        | none => 0
        | some q => S.rank u (some (u :: q))
      let w₀ := (W.exists_max_image score hW).choose
      (π w₀).map (u :: ·)
    else none

theorem bestResponse_dest (S : SPP V) (π : V → Option (List V)) :
    S.bestResponse π S.dest = some [S.dest] := by
  simp [bestResponse]

theorem bestResponse_isChoice (S : SPP V) (π : V → Option (List V)) {u : V} (hu : u ≠ S.dest) :
    S.IsChoice π u (S.bestResponse π u) := by
  classical
  simp only [bestResponse, hu, ↓reduceIte]
  let W : Finset V := Finset.univ.filter fun w =>
    S.graph.Adj u w ∧ ∃ q, π w = some q ∧ S.permitted u (u :: q)
  change S.IsChoice π u (if hW : W.Nonempty then
    let score : V → ℕ := fun w => match π w with | none => 0 | some q => S.rank u (some (u :: q))
    (π (W.exists_max_image score hW).choose).map (u :: ·)
  else none)
  split_ifs with hW
  · set score : V → ℕ := fun w => match π w with | none => 0 | some q => S.rank u (some (u :: q))
    have hw₀ := (W.exists_max_image score hW).choose_spec.1
    have hspec : S.graph.Adj u (W.exists_max_image score hW).choose ∧
        ∃ q, π (W.exists_max_image score hW).choose = some q ∧ S.permitted u (u :: q) :=
      (Finset.mem_filter.mp hw₀).2
    obtain ⟨hadj, q, hq, hperm⟩ := hspec
    dsimp only
    rw [hq]
    exact Or.inr ⟨u :: q, rfl, hperm, _, q, hadj, hq, rfl⟩
  · exact S.isChoice_none π u

theorem rank_le_bestResponse (S : SPP V) (π : V → Option (List V)) {u : V} (hu : u ≠ S.dest)
    {o : Option (List V)} (ho : S.IsChoice π u o) :
    S.rank u o ≤ S.rank u (S.bestResponse π u) := by
  classical
  simp only [bestResponse, hu, ↓reduceIte]
  rcases ho with rfl | ⟨p, rfl, hperm, w, q, hadj, hq, rfl⟩
  · rw [S.rank_none]; exact Nat.zero_le _
  · let W : Finset V := Finset.univ.filter fun w =>
      S.graph.Adj u w ∧ ∃ q, π w = some q ∧ S.permitted u (u :: q)
    change S.rank u (some (u :: q)) ≤ S.rank u (if hW : W.Nonempty then
      let score : V → ℕ := fun w => match π w with | none => 0 | some q => S.rank u (some (u :: q))
      (π (W.exists_max_image score hW).choose).map (u :: ·)
    else none)
    have hwW : w ∈ W := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj, q, hq, hperm⟩
    have hW : W.Nonempty := ⟨w, hwW⟩
    split_ifs
    set score : V → ℕ := fun w => match π w with | none => 0 | some q => S.rank u (some (u :: q))
    have hspec := (W.exists_max_image score hW).choose_spec
    have hle := hspec.2 w hwW
    have hw₀ : S.graph.Adj u (W.exists_max_image score hW).choose ∧
        ∃ q₀, π (W.exists_max_image score hW).choose = some q₀ ∧ S.permitted u (u :: q₀) :=
      (Finset.mem_filter.mp hspec.1).2
    obtain ⟨_, q₀, hq₀, _⟩ := hw₀
    simpa [score, hq, hq₀] using hle

/-- A path assignment is stable if and only if it is a fixed point of `bestResponse`. -/
theorem isStable_iff_bestResponse (S : SPP V) (π : V → Option (List V)) :
    S.IsStable π ↔ ∀ u, S.bestResponse π u = π u := by
  constructor
  · intro hπ u
    by_cases hu : u = S.dest
    · subst hu; rw [S.bestResponse_dest, hπ.1]
    · have hle₁ := S.rank_le_bestResponse π hu (hπ.2 u hu).1
      have hle₂ := (hπ.2 u hu).2 _ (S.bestResponse_isChoice π hu)
      have hhead : ∀ w q, π w = some q → q.head? = some w := fun w q hw =>
        (S.permitted_isSimplePath w q (hπ.permitted_of_eq_some hw)).1
      exact S.eq_of_isChoice_rank_eq hhead (S.bestResponse_isChoice π hu) (hπ.2 u hu).1
        (le_antisymm hle₂ hle₁)
  · intro hfix
    refine ⟨(hfix S.dest).symm.trans (S.bestResponse_dest π), fun u hu => ?_⟩
    rw [← hfix u]
    exact ⟨S.bestResponse_isChoice π hu, fun o ho => S.rank_le_bestResponse π hu ho⟩

/-- The standard initial assignment: `dest` advertises `[dest]` and all other ASes have `none`. -/
@[expose] def initAssignment (S : SPP V) : V → Option (List V) :=
  fun u => if u = S.dest then some [S.dest] else none

/-- Asynchronous best-response execution along activation schedule `sched`, starting from `π₀`.
This models asynchronous per-node atomic best-response activation ([FeigenbaumSchapiraShenker2007],
Chapter 14), rather than the asynchronous link-queue message-passing protocol (`SPVP`) of
[GriffinShepherdWilfong2002]. -/
@[expose] noncomputable def run (S : SPP V) (sched : ℕ → V) (π₀ : V → Option (List V)) :
    ℕ → V → Option (List V)
  | 0 => π₀
  | t + 1 => Function.update (S.run sched π₀ t) (sched t)
      (S.bestResponse (S.run sched π₀ t) (sched t))

/-- An activation schedule is **fair** if every AS is activated infinitely often. -/
@[expose] def IsFair (sched : ℕ → V) : Prop :=
  ∀ v t, ∃ s ≥ t, sched s = v

omit [Fintype V] [DecidableEq V] in
private theorem isFair_exists_all_activated [Finite V] {sched : ℕ → V} (hfair : IsFair sched)
    (t : ℕ) : ∃ t' ≥ t, ∀ v, ∃ s, t ≤ s ∧ s < t' ∧ sched s = v := by
  classical
  have : Fintype V := Fintype.ofFinite V
  choose f hf_ge hf_eq using fun v => hfair v t
  let M := Finset.univ.sup f + 1
  refine ⟨max t M, le_max_left _ _, fun v => ⟨f v, hf_ge v, ?_, hf_eq v⟩⟩
  have hfv : f v ≤ Finset.univ.sup f := Finset.le_sup (Finset.mem_univ v)
  omega

private theorem run_dest_eq (S : SPP V) (sched : ℕ → V) (t : ℕ) :
    S.run sched S.initAssignment t S.dest = some [S.dest] := by
  induction t with
  | zero => simp [run, initAssignment]
  | succ t ih =>
    simp only [run]
    by_cases h : sched t = S.dest
    · rw [h, Function.update_self, S.bestResponse_dest]
    · rw [Function.update_of_ne (Ne.symm h), ih]

private theorem run_surviving_init (S : SPP V) (sched : ℕ → V) (t : ℕ) :
    ∀ v p, S.run sched S.initAssignment t v = some p →
      Surviving S (initElimState S).settled (initElimState S).assign v p := by
  induction t with
  | zero =>
    intro v p hp
    simp only [run, initAssignment] at hp
    split_ifs at hp with hv
    subst hv
    obtain rfl := Option.some.inj hp
    exact ⟨S.permitted_dest, ⟨S.permitted_dest, trivial⟩, trivial⟩
  | succ t ih =>
    intro v p hp
    simp only [run] at hp
    by_cases hv : v = sched t
    · subst hv
      rw [Function.update_self] at hp
      by_cases hd : sched t = S.dest
      · rw [hd, S.bestResponse_dest] at hp
        obtain rfl := Option.some.inj hp
        rw [hd]
        exact ⟨S.permitted_dest, ⟨S.permitted_dest, trivial⟩, trivial⟩
      · rcases S.bestResponse_isChoice (S.run sched S.initAssignment t) hd with
            hnone | ⟨p', hp', hperm, w, q, _, hqw, rfl⟩
        · rw [hp] at hnone; cases hnone
        · obtain rfl := Option.some.inj (hp'.symm.trans hp)
          have hsurv_w := ih w q hqw
          refine ⟨hperm, ⟨hperm, hsurv_w.2.1⟩, ?_⟩
          cases q with
          | nil =>
            exact ((S.permitted_isSimplePath w [] hsurv_w.1).ne_nil rfl).elim
          | cons a r =>
            have ha : a = w := Option.some.inj (S.permitted_isSimplePath w (a :: r) hsurv_w.1).1
            cases ha
            refine ⟨fun hw => ?_, hsurv_w.2.2⟩
            obtain rfl : w = S.dest := Finset.mem_singleton.mp hw
            rw [S.run_dest_eq] at hqw
            simpa [initElimState] using hqw
    · rw [Function.update_of_ne hv] at hp
      exact ih v p hp

/-- **Griffin–Shepherd–Wilfong safety** ([GriffinShepherdWilfong2002], proved here for the
asynchronous per-node atomic best-response activation model `SPP.run` of
[FeigenbaumSchapiraShenker2007], Chapter 14, rather than FIFO link-queue `SPVP`): if an `SPP`
instance has no dispute wheel, then asynchronous best-response dynamics from `initAssignment`
converge under every fair activation schedule to the unique stable path assignment. -/
theorem exists_converges_of_isEmpty_disputeWheel (S : SPP V) (hfree : IsEmpty (DisputeWheel S))
    (sched : ℕ → V) (hfair : IsFair sched) :
    ∃ π, S.IsStable π ∧ ∃ T, ∀ t ≥ T, S.run sched S.initAssignment t = π := by
  have hhead_run : ∀ t w q, S.run sched S.initAssignment t w = some q → q.head? = some w :=
    fun t w q hq => (S.permitted_isSimplePath w q (S.run_surviving_init sched t w q hq).1).1
  suffices h : ∀ n (st : ElimState S), Fintype.card V - st.settled.card ≤ n →
      ∀ T, (∀ t ≥ T, ∀ v ∈ st.settled, S.run sched S.initAssignment t v = st.assign v) →
      (∀ t ≥ T, ∀ v p, S.run sched S.initAssignment t v = some p →
        Surviving S st.settled st.assign v p) →
      ∃ π, S.IsStable π ∧ ∃ T', ∀ t ≥ T', S.run sched S.initAssignment t = π by
    exact h (Fintype.card V) (initElimState S) (Nat.sub_le _ _) 0
      (fun t _ v hv => by
        have hv' : v = S.dest := Finset.mem_singleton.mp hv
        subst hv'
        simpa [initElimState] using S.run_dest_eq sched t)
      (fun t _ => S.run_surviving_init sched t)
  intro n
  induction n with
  | zero =>
    intro st hle T hlock _
    have hcard : st.settled.card = Fintype.card V :=
      le_antisymm (Finset.card_le_univ _) (by omega)
    have hall : ∀ u, u ∈ st.settled := by simp [Finset.eq_univ_of_card st.settled hcard]
    refine ⟨st.assign, isStable_of_no_directCand st fun u _ hdir => hdir.1 (hall u), T,
      fun t ht => funext fun v => hlock t ht v (hall v)⟩
  | succ n ih =>
    intro st hle T hlock hsurv
    by_cases hne : ∃ u p, IsDirectCand st u p
    · obtain ⟨u, p, hdir, hopt⟩ := exists_extendable_of_isEmpty_disputeWheel st hfree hne
      let st' := extendElimState st u p hdir hopt
      have hu_ne_dest : u ≠ S.dest := fun hEq => hdir.1 (hEq ▸ st.dest_mem)
      have hbr_u : ∀ t ≥ T, S.bestResponse (S.run sched S.initAssignment t) u = some p := by
        intro t ht
        rcases hdir with ⟨_, hperm_p, w, hwA, q, hadj, hqw, hp_eq⟩
        have hchoice_p : S.IsChoice (S.run sched S.initAssignment t) u (some p) :=
          Or.inr ⟨p, rfl, hperm_p, w, q, hadj, (hlock t ht w hwA).trans hqw, hp_eq⟩
        have hle₁ := S.rank_le_bestResponse (S.run sched S.initAssignment t) hu_ne_dest hchoice_p
        have hbr_choice := S.bestResponse_isChoice (S.run sched S.initAssignment t) hu_ne_dest
        have hle₂ : S.rank u (S.bestResponse (S.run sched S.initAssignment t) u) ≤
            S.rank u (some p) := by
          rcases hbr_choice with hnone | ⟨p', hp', hperm', w', q', _, hqw', rfl⟩
          · rw [hnone, S.rank_none]; exact Nat.zero_le _
          · rw [hp']
            have hsurv_w' := hsurv t ht w' q' hqw'
            have hsurv_p' : Surviving S st.settled st.assign u (u :: q') := by
              refine ⟨hperm', ⟨hperm', hsurv_w'.2.1⟩, ?_⟩
              cases q' with
              | nil => exact ((S.permitted_isSimplePath w' [] hsurv_w'.1).ne_nil rfl).elim
              | cons a r =>
                have ha : a = w' :=
                  Option.some.inj (S.permitted_isSimplePath w' (a :: r) hsurv_w'.1).1
                cases ha
                exact ⟨fun hw'A => (hlock t ht w' hw'A).symm.trans hqw', hsurv_w'.2.2⟩
            exact hopt (u :: q') hsurv_p'
        exact S.eq_of_isChoice_rank_eq (hhead_run t) hbr_choice hchoice_p (le_antisymm hle₂ hle₁)
      obtain ⟨s₁, hs₁_ge, hs₁_eq⟩ := hfair u T
      let T₁ := s₁ + 1
      have hlock_u : ∀ t ≥ T₁, S.run sched S.initAssignment t u = some p := by
        intro t ht
        induction t, ht using Nat.le_induction with
        | base =>
          simp only [T₁, run, hs₁_eq, Function.update_self]
          exact hbr_u s₁ hs₁_ge
        | succ k hk ihk =>
          simp only [run]
          by_cases hku : sched k = u
          · rw [hku, Function.update_self]
            exact hbr_u k (by omega)
          · rw [Function.update_of_ne (Ne.symm hku), ihk]
      have hlock' : ∀ t ≥ T₁, ∀ v ∈ st'.settled,
          S.run sched S.initAssignment t v = st'.assign v := by
        intro t ht v hv
        dsimp only [st', extendElimState] at hv ⊢
        rcases Finset.mem_insert.mp hv with rfl | hvA
        · simpa using hlock_u t ht
        · have hv_ne : v ≠ u := fun h => hdir.1 (h ▸ hvA)
          simpa [Function.update_of_ne hv_ne] using hlock t (by omega) v hvA
      have hpurge : ∀ L, 1 ≤ L → ∃ T_L ≥ T₁, ∀ t ≥ T_L, ∀ v q,
          S.run sched S.initAssignment t v = some q →
          ∀ pref suff, q = pref ++ u :: suff → pref.length < L → u :: suff = p := by
        intro L hL
        induction L, hL using Nat.le_induction with
        | base =>
          refine ⟨T₁, le_rfl, fun t ht v q hq pref suff hsplit hlen => ?_⟩
          obtain rfl : pref = [] := List.eq_nil_of_length_eq_zero (by omega)
          obtain rfl : u = v := by simpa [hsplit] using hhead_run t v q hq
          rw [hlock_u t ht] at hq
          exact hsplit.symm.trans (Option.some.inj hq).symm
        | succ L hL ihL =>
          obtain ⟨T_L, hTL_ge, hTL⟩ := ihL
          obtain ⟨T_next, hTn_ge, hTn⟩ := isFair_exists_all_activated hfair T_L
          have hstep_good : ∀ s ≥ T_L, ∀ v q,
              S.bestResponse (S.run sched S.initAssignment s) v = some q →
              ∀ pref suff, q = pref ++ u :: suff → pref.length < L + 1 → u :: suff = p := by
            intro s hs v q hbr pref suff hsplit hlen
            by_cases hvd : v = S.dest
            · subst hvd
              rw [S.bestResponse_dest] at hbr
              obtain rfl := Option.some.inj hbr
              rcases pref with _ | ⟨a, r⟩
              · exact (hu_ne_dest (List.cons.inj hsplit).1.symm).elim
              · have := congrArg List.length hsplit
                simp only [List.length_cons, List.length_nil, List.length_append] at this
                omega
            · by_cases hvu : v = u
              · rw [hvu, hbr_u s (by omega)] at hbr
                obtain rfl := Option.some.inj hbr
                have hp_nodup := (S.permitted_isSimplePath u p hdir.2.1).2.2.2
                have hp_head := (S.permitted_isSimplePath u p hdir.2.1).1
                cases pref with
                | nil => simpa using hsplit.symm
                | cons a r =>
                  rw [List.cons_append] at hsplit
                  have ha : a = u := Option.some.inj (by simpa [hsplit] using hp_head)
                  subst ha
                  rw [hsplit] at hp_nodup
                  have hu_mem : a ∈ r ++ a :: suff := List.mem_append_right r List.mem_cons_self
                  exact ((List.nodup_cons.mp hp_nodup).1 hu_mem).elim
              · rcases S.bestResponse_isChoice (S.run sched S.initAssignment s) hvd with
                    hnone | ⟨p', hp', _, w, qw, _, hqw, rfl⟩
                · rw [hbr] at hnone; cases hnone
                · obtain rfl := Option.some.inj (hp'.symm.trans hbr)
                  cases pref with
                  | nil =>
                    simp only [List.nil_append, List.cons.injEq] at hsplit
                    exact (hvu hsplit.1).elim
                  | cons a r =>
                    simp only [List.cons_append, List.cons.injEq] at hsplit
                    simp only [List.length_cons] at hlen
                    exact hTL s hs w qw hqw r suff hsplit.2 (by omega)
          have hbase : ∀ v q, S.run sched S.initAssignment T_next v = some q →
              ∀ pref suff, q = pref ++ u :: suff → pref.length < L + 1 → u :: suff = p := by
            intro v
            have hact : ∃ s, T_L ≤ s ∧ s < T_next ∧ sched s = v ∧
                ∀ r, s < r → r < T_next → sched r ≠ v := by
              let S_act := (Finset.Ico T_L T_next).filter fun s => sched s = v
              have hS_ne : S_act.Nonempty := by
                obtain ⟨s, hs1, hs2, hs3⟩ := hTn v
                exact ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hs1, hs2⟩, hs3⟩⟩
              let s := S_act.max' hS_ne
              have hs_mem := Finset.mem_filter.mp (Finset.max'_mem S_act hS_ne)
              have hs_ico := Finset.mem_Ico.mp hs_mem.1
              refine ⟨s, hs_ico.1, hs_ico.2, hs_mem.2, fun r hr1 hr2 hrv => ?_⟩
              have hr_mem : r ∈ S_act :=
                Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, hr2⟩, hrv⟩
              have hle_max := Finset.le_max' S_act r hr_mem
              omega
            obtain ⟨s, hs1, hs2, hs3, hlast⟩ := hact
            have hrun_eq : S.run sched S.initAssignment T_next v =
                S.bestResponse (S.run sched S.initAssignment s) v := by
              have hstay : ∀ m, s + 1 ≤ m → m ≤ T_next →
                  S.run sched S.initAssignment m v = S.run sched S.initAssignment (s + 1) v := by
                intro m hm1 hm2
                induction m, hm1 using Nat.le_induction with
                | base => rfl
                | succ k hk ihk =>
                  have hne_k : sched k ≠ v := hlast k (by omega) (by omega)
                  simp only [run, Function.update_of_ne (Ne.symm hne_k)]
                  exact ihk (by omega)
              rw [hstay T_next (by omega) le_rfl]
              simp only [run, hs3, Function.update_self]
            intro q hq
            rw [hrun_eq] at hq
            exact hstep_good s hs1 v q hq
          refine ⟨T_next, le_trans hTL_ge hTn_ge, fun t ht => ?_⟩
          induction t, ht using Nat.le_induction with
          | base => exact hbase
          | succ k hk ihk =>
            intro v q hq
            simp only [run] at hq
            by_cases hkv : v = sched k
            · subst hkv
              rw [Function.update_self] at hq
              exact hstep_good k (by omega) (sched k) q hq
            · rw [Function.update_of_ne hkv] at hq
              exact ihk v q hq
      have hcard_pos : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨S.dest⟩
      obtain ⟨T', hT'_ge, hT'⟩ := hpurge (Fintype.card V) hcard_pos
      have hsurv' : ∀ t ≥ T', ∀ v q, S.run sched S.initAssignment t v = some q →
          Surviving S st'.settled st'.assign v q := by
        intro t ht v q hq
        have hold := hsurv t (by omega) v q hq
        refine ⟨hold.1, hold.2.1, ?_⟩
        have hlen_q : q.length ≤ Fintype.card V :=
          (S.permitted_isSimplePath v q hold.1).length_le_card
        have haux : ∀ pref r, q = pref ++ r → SuffixesAgreeOn st.settled st.assign r →
            SuffixesAgreeOn st'.settled st'.assign r := by
          intro pref r hsplit hagr
          induction r generalizing pref with
          | nil => trivial
          | cons x rest ihr =>
            refine ⟨fun hx => ?_, ihr (pref ++ [x]) (by simp [hsplit]) hagr.2⟩
            dsimp only [st', extendElimState] at hx ⊢
            rcases Finset.mem_insert.mp hx with rfl | hxA
            · have hpref_lt : pref.length < Fintype.card V := by
                have h1 := congrArg List.length hsplit
                simp only [List.length_append, List.length_cons] at h1
                omega
              have heq := hT' t ht v q hq pref rest hsplit hpref_lt
              simpa using heq.symm
            · have hx_ne : x ≠ u := fun h => hdir.1 (h ▸ hxA)
              simpa [Function.update_of_ne hx_ne] using hagr.1 hxA
        cases q with
        | nil => exact ((S.permitted_isSimplePath v [] hold.1).ne_nil rfl).elim
        | cons a r => exact haux [a] r rfl hold.2.2
      have hcard' : st'.settled.card = st.settled.card + 1 := by
        dsimp only [st', extendElimState]
        exact Finset.card_insert_of_notMem hdir.1
      exact ih st' (by omega) T' (fun t ht => hlock' t (le_trans hT'_ge ht)) hsurv'
    · push Not at hne
      refine ⟨st.assign, isStable_of_no_directCand st hne, T, fun t ht => funext fun v => ?_⟩
      by_cases hvA : v ∈ st.settled
      · exact hlock t ht v hvA
      · rw [st.assign_none_of_not_mem v hvA]
        cases hq : S.run sched S.initAssignment t v with
        | none => rfl
        | some p =>
          exfalso
          obtain ⟨_, x, y, r, _, hxA, hyA, hadj, hperm_x, hπy⟩ :=
            surviving_split_directCand st hvA (hsurv t ht v p hq)
          exact hne x (x :: y :: r) ⟨hxA, hperm_x, y, hyA, y :: r, hadj, hπy, rfl⟩

end ExistenceAndSafety

end SPP

/-! ### Classic counterexamples: `BAD GADGET` and `DISAGREE` -/

/-- The classic 4-node `BAD GADGET` ([GriffinShepherdWilfong2002];
[FeigenbaumSchapiraShenker2007], Chapter 14): destination `0`, with nodes `1, 2, 3` each
preferring a two-hop detour through the next node cyclically (`1 → 2 → 0`, `2 → 3 → 0`,
`3 → 1 → 0`) over their direct path to `0`. -/
def badGadget : SPP (Fin 4) where
  graph := ⊤
  dest := 0
  permitted u p :=
    (u = 0 ∧ p = [0]) ∨
    (u = 1 ∧ (p = [1, 2, 0] ∨ p = [1, 0])) ∨
    (u = 2 ∧ (p = [2, 3, 0] ∨ p = [2, 0])) ∨
    (u = 3 ∧ (p = [3, 1, 0] ∨ p = [3, 0]))
  permitted_isSimplePath := by
    intro u p hp
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ <;>
      refine ⟨rfl, rfl, by simp, by decide⟩
  permitted_dest := Or.inl ⟨rfl, rfl⟩
  rank _ o :=
    match o with
    | none => 0
    | some p => p.length
  rank_none _ := rfl
  rank_pos := by
    intro u p hp
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ <;>
      decide
  strict := by
    intro u p₁ p₂ h₁ h₂ hr
    rcases h₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ <;>
      rcases h₂ with ⟨h, rfl⟩ | ⟨h, rfl | rfl⟩ | ⟨h, rfl | rfl⟩ | ⟨h, rfl | rfl⟩ <;>
      simp_all

/-- Explicit 3-spoke dispute wheel in `badGadget`. -/
def badGadgetDisputeWheel : DisputeWheel badGadget where
  size := 3
  size_pos := by decide
  node := ![1, 2, 3]
  pivot := ![[1, 0], [2, 0], [3, 0]]
  rim := ![[1], [2], [3]]
  rim_nonempty := fun i => by fin_cases i <;> decide
  pivot_permitted := fun i => by fin_cases i <;> simp [badGadget]
  rim_pivot_permitted := fun i => by fin_cases i <;> simp [badGadget]
  prefers := fun i => by fin_cases i <;> decide

@[simp] theorem badGadgetDisputeWheel_size : badGadgetDisputeWheel.size = 3 := by
  dsimp [badGadgetDisputeWheel]

/-- `badGadget` has no stable path assignment ([GriffinShepherdWilfong2002]). -/
theorem not_exists_isStable_badGadget : ¬ ∃ π, badGadget.IsStable π := by
  rintro ⟨π, hπ⟩
  have h0 : π 0 = some [0] := hπ.1
  -- `u ≠ 0` ranks `π u` at least as high as any permitted extension of a neighbour's route
  have hle : ∀ u w q, u ≠ 0 → u ≠ w → π w = some q → badGadget.permitted u (u :: q) →
      (u :: q).length ≤ badGadget.rank u (π u) := fun u w q hu huw hw hp =>
    (hπ.2 u hu).2 _ (Or.inr ⟨_, rfl, hp, w, q, huw, hw, rfl⟩)
  -- since its direct path `[u, 0]` is available, every `u ≠ 0` selects a permitted path
  have hroute : ∀ u, u ≠ 0 → ∃ p, π u = some p ∧ badGadget.permitted u p := fun u hu => by
    rcases (hπ.2 u hu).1 with hnone | ⟨p, hp, hperm, _⟩
    · have := hle u 0 [0] hu hu h0 (by simp [badGadget]; omega)
      simp [hnone, badGadget] at this
    · exact ⟨p, hp, hperm⟩
  obtain ⟨p₁, h1, hp₁⟩ := hroute 1 (by decide)
  obtain ⟨p₂, h2, hp₂⟩ := hroute 2 (by decide)
  obtain ⟨p₃, h3, hp₃⟩ := hroute 3 (by decide)
  obtain rfl | rfl : p₁ = [1, 2, 0] ∨ p₁ = [1, 0] := by simpa [badGadget] using hp₁
  · have h2' : π 2 = some [2, 0] := hπ.suffix_eq_some h1 (q := [1]) (x := 2) (t := [0]) rfl
    obtain rfl | rfl : p₃ = [3, 1, 0] ∨ p₃ = [3, 0] := by simpa [badGadget] using hp₃
    · have := hπ.suffix_eq_some h3 (q := [3]) (x := 1) (t := [0]) rfl
      simp [h1] at this
    · have := hle 2 3 [3, 0] (by decide) (by decide) h3 (by simp [badGadget])
      simp [h2', badGadget] at this
  · have h3' : π 3 = some [3, 1, 0] := by
      have := hle 3 1 [1, 0] (by decide) (by decide) h1 (by simp [badGadget])
      obtain rfl | rfl : p₃ = [3, 1, 0] ∨ p₃ = [3, 0] := by simpa [badGadget] using hp₃
      · exact h3
      · simp [h3, badGadget] at this
    obtain rfl | rfl : p₂ = [2, 3, 0] ∨ p₂ = [2, 0] := by simpa [badGadget] using hp₂
    · have := hπ.suffix_eq_some h2 (q := [2]) (x := 3) (t := [0]) rfl
      simp [h3'] at this
    · have := hle 1 2 [2, 0] (by decide) (by decide) h2 (by simp [badGadget])
      simp [h1, badGadget] at this

/-- The classic 3-node `DISAGREE` instance ([GriffinShepherdWilfong2002]): destination `0`, with
nodes `1` and `2` each preferring to route through the other (`1 → 2 → 0` over `1 → 0`, and
`2 → 1 → 0` over `2 → 0`). -/
def disagree : SPP (Fin 3) where
  graph := ⊤
  dest := 0
  permitted u p :=
    (u = 0 ∧ p = [0]) ∨
    (u = 1 ∧ (p = [1, 2, 0] ∨ p = [1, 0])) ∨
    (u = 2 ∧ (p = [2, 1, 0] ∨ p = [2, 0]))
  permitted_isSimplePath := by
    intro u p hp
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ <;>
      refine ⟨rfl, rfl, by simp, by decide⟩
  permitted_dest := Or.inl ⟨rfl, rfl⟩
  rank _ o :=
    match o with
    | none => 0
    | some p => p.length
  rank_none _ := rfl
  rank_pos := by
    intro u p hp
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ <;> decide
  strict := by
    intro u p₁ p₂ h₁ h₂ hr
    rcases h₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ <;>
      rcases h₂ with ⟨h, rfl⟩ | ⟨h, rfl | rfl⟩ | ⟨h, rfl | rfl⟩ <;>
      simp_all

/-- Explicit 2-spoke dispute wheel in `disagree`. -/
def disagreeDisputeWheel : DisputeWheel disagree where
  size := 2
  size_pos := by decide
  node := ![1, 2]
  pivot := ![[1, 0], [2, 0]]
  rim := ![[1], [2]]
  rim_nonempty := fun i => by fin_cases i <;> decide
  pivot_permitted := fun i => by fin_cases i <;> simp [disagree]
  rim_pivot_permitted := fun i => by fin_cases i <;> simp [disagree]
  prefers := fun i => by fin_cases i <;> decide

@[simp] theorem disagreeDisputeWheel_size : disagreeDisputeWheel.size = 2 := by
  dsimp [disagreeDisputeWheel]

/-- `disagree` admits two distinct stable path assignments ([GriffinShepherdWilfong2002]). -/
theorem exists_two_isStable_disagree :
    ∃ π₁ π₂, disagree.IsStable π₁ ∧ disagree.IsStable π₂ ∧ π₁ ≠ π₂ := by
  let π₁ : Fin 3 → Option (List (Fin 3)) := ![some [0], some [1, 2, 0], some [2, 0]]
  let π₂ : Fin 3 → Option (List (Fin 3)) := ![some [0], some [1, 0], some [2, 1, 0]]
  refine ⟨π₁, π₂, ?_, ?_, ?_⟩
  · refine ⟨rfl, fun u hu => ?_⟩
    fin_cases u
    · exact (hu rfl).elim
    · refine ⟨Or.inr ⟨[1, 2, 0], rfl, by simp [disagree], 2, [2, 0], by simp [disagree], rfl, rfl⟩,
        fun o ho => ?_⟩
      rcases ho with rfl | ⟨p, rfl, hperm, _⟩
      · decide
      · obtain rfl | rfl : p = [1, 2, 0] ∨ p = [1, 0] := by simpa [disagree] using hperm
        all_goals decide
    · refine ⟨Or.inr ⟨[2, 0], rfl, by simp [disagree], 0, [0], by simp [disagree], rfl, rfl⟩,
        fun o ho => ?_⟩
      rcases ho with rfl | ⟨p, rfl, hperm, w, q, _, hqw, rfl⟩
      · decide
      · obtain rfl | rfl : q = [1, 0] ∨ q = [0] := by simpa [disagree] using hperm
        · fin_cases w <;> simp [π₁] at hqw
        · decide
  · refine ⟨rfl, fun u hu => ?_⟩
    fin_cases u
    · exact (hu rfl).elim
    · refine ⟨Or.inr ⟨[1, 0], rfl, by simp [disagree], 0, [0], by simp [disagree], rfl, rfl⟩,
        fun o ho => ?_⟩
      rcases ho with rfl | ⟨p, rfl, hperm, w, q, _, hqw, rfl⟩
      · decide
      · obtain rfl | rfl : q = [2, 0] ∨ q = [0] := by simpa [disagree] using hperm
        · fin_cases w <;> simp [π₂] at hqw
        · decide
    · refine ⟨Or.inr ⟨[2, 1, 0], rfl, by simp [disagree], 1, [1, 0], by simp [disagree], rfl, rfl⟩,
        fun o ho => ?_⟩
      rcases ho with rfl | ⟨p, rfl, hperm, _⟩
      · decide
      · obtain rfl | rfl : p = [2, 1, 0] ∨ p = [2, 0] := by simpa [disagree] using hperm
        all_goals decide
  · intro hEq
    have h1 := congrFun hEq 1
    simp [π₁, π₂] at h1

end Cslib.GameTheory.InterdomainRouting
