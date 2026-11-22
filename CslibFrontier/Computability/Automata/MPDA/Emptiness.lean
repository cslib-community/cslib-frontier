/-
Copyright (c) 2026 Sparsa Roychowdhury. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sparsa Roychowdhury
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Automata.MPDA.WellNested
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Order.FixedPoints
public import CslibFrontier.Foundations.Relation.FiniteClosure
import CslibFrontier.Foundations.Order.FiniteFixedPoint
import CslibFrontier.Foundations.Data.List.ListsUpTo

/-! # Computing well-nested reachability

The emptiness procedure for hole-bounded MPDAs, Algorithm 1 of
[AkshayGastinKrishnaRoychowdhury2020], starts from the set `WR` of pairs of control states joined
by a well-nested run, computed by Algorithm 2 (`WellNestedReach`, Appendix B). This file computes
`WR` for an MPDA with finitely many control states, letters and stack symbols and a decidable
transition relation.

`MPDA.wellNestedPairs M` iterates the closure rules of `MPDA.WellNestedReach` on finite sets of
pairs, as many times as there are pairs. Algorithm 2 alternates a transitive closure with a
push-pop step until nothing changes; any order of applying the rules reaches the same least fixed
point, and the number of iterations is not part of the statements here.

The file then defines the search of **repaired Algorithm 1** (`MPDA.isEmpty`). It differs from
the printed algorithm in two ways.
- `HSᵢ` is the reflexive-transitive closure of `AHSᵢ`, where line 9 of Algorithm 1 takes the
  transitive closure. This lets `AddPop` remove a hole whose last atomic segment is popped. It
  also lets `AddHole` open a hole `(i, s, s)` without taking a transition, even from a state with
  no push; such a hole is realized by the empty factor, while Definition 1 counts nonempty
  factors. It only uses up one of the `K` holes, and soundness allows the empty realization.
- The search starts from the states reached from an initial state by a well-nested run, not from
  the initial state alone (line 10).

Starting from the initial state alone is not complete: the module client test
`CslibFrontierTests.MPDA.Emptiness` defines this printed-start variant and checks a
counterexample.

## Main definitions

- `MPDA.wellNestedPairs`: the set `WR` of Algorithm 2, as a computable `Finset`.
- `MPDA.atomicHoles`, `MPDA.holeSegments`: the sets `AHSᵢ` and `HSᵢ` of Algorithm 1.
- `MPDA.isEmpty`: repaired Algorithm 1.

## Main results

- `MPDA.mem_wellNestedPairs`: `(s, s') ∈ WR` exactly when `MPDA.WellNestedReach M s s'`. With
  `MPDA.wellNestedReach_iff`, this is Lemma 1 of [AkshayGastinKrishnaRoychowdhury2020] for the
  computed set.

## References

* [S. Akshay, P. Gastin, S. Krishna, S. Roychowdhury,
  *Revisiting Underapproximate Reachability for Multipushdown Systems*]
  [AkshayGastinKrishnaRoychowdhury2020]
-/

public section

namespace Cslib.Automata.MPDA

variable {n : ℕ} {State Symbol Γ : Type*}

/-! ## The closure rules of `WR` as a monotone map -/

/-- One application of the closure rules of `WellNestedReach` to a relation `R`: reflexive pairs,
a `nop` transition followed by `R`, and a push followed by `R`, a matching pop and `R`. -/
@[expose] def wellNestedRule (M : MPDA n State Symbol Γ) (R : Set (State × State)) :
    Set (State × State) :=
  {p | p.1 = p.2 ∨ (∃ a s₂, M.Tr p.1 (a, .nop) s₂ ∧ (s₂, p.2) ∈ R) ∨
    ∃ (a b : Symbol) (i : Fin n) (γ : Γ) (s₂ s₃ s₄ : State), M.Tr p.1 (a, .push i γ) s₂ ∧
      (s₂, s₃) ∈ R ∧ M.Tr s₃ (b, .pop i γ) s₄ ∧ (s₄, p.2) ∈ R}

/-- The closure rules of `WellNestedReach` as a monotone map on relations. -/
@[expose] def wellNestedRuleHom (M : MPDA n State Symbol Γ) :
    Set (State × State) →o Set (State × State) where
  toFun := M.wellNestedRule
  monotone' R R' hR p hp := by
    rcases hp with h | ⟨a, s₂, ht, hr⟩ | ⟨a, b, i, γ, s₂, s₃, s₄, h₁, h₂, h₃, h₄⟩
    · exact .inl h
    · exact .inr (.inl ⟨a, s₂, ht, hR hr⟩)
    · exact .inr (.inr ⟨a, b, i, γ, s₂, s₃, s₄, h₁, hR h₂, h₃, hR h₄⟩)

/-- The least fixed point of the closure rules is `WellNestedReach`. -/
theorem lfp_wellNestedRuleHom (M : MPDA n State Symbol Γ) :
    M.wellNestedRuleHom.lfp = {p | M.WellNestedReach p.1 p.2} := by
  apply le_antisymm
  · refine OrderHom.lfp_le _ fun p hp => ?_
    rcases hp with h | ⟨a, s₂, ht, hr⟩ | ⟨a, b, i, γ, s₂, s₃, s₄, h₁, h₂, h₃, h₄⟩
    · obtain ⟨s, s'⟩ := p
      simp only at h
      subst h
      exact .refl s
    · exact .nop ht hr
    · exact .pushPop h₁ h₂ h₃ h₄
  · rintro ⟨s, s'⟩ h
    simp only [Set.mem_ofPred_eq] at h
    induction h with
    | refl s =>
      rw [← OrderHom.map_lfp]
      exact .inl rfl
    | nop ht _ ih =>
      rw [← OrderHom.map_lfp]
      exact .inr (.inl ⟨_, _, ht, ih⟩)
    | pushPop h₁ _ h₃ _ ih ih' =>
      rw [← OrderHom.map_lfp]
      exact .inr (.inr ⟨_, _, _, _, _, _, _, h₁, ih, h₃, ih'⟩)

/-! ## Computing `WR` -/

section Compute

variable [Fintype State] [DecidableEq State] [Fintype Symbol] [Fintype Γ]
  (M : MPDA n State Symbol Γ) [∀ s μ s', Decidable (M.Tr s μ s')]

/-- One application of the closure rules of `WellNestedReach` to a finite relation. -/
@[expose] def wellNestedStep (R : Finset (State × State)) : Finset (State × State) :=
  Finset.univ.filter fun p => p.1 = p.2 ∨ (∃ a s₂, M.Tr p.1 (a, .nop) s₂ ∧ (s₂, p.2) ∈ R) ∨
    ∃ (a b : Symbol) (i : Fin n) (γ : Γ) (s₂ s₃ s₄ : State), M.Tr p.1 (a, .push i γ) s₂ ∧
      (s₂, s₃) ∈ R ∧ M.Tr s₃ (b, .pop i γ) s₄ ∧ (s₄, p.2) ∈ R

/-- The set `WR` of Algorithm 2 of [AkshayGastinKrishnaRoychowdhury2020]: the closure rules of
`WellNestedReach`, iterated from the empty relation once for each pair of control states. -/
@[expose] def wellNestedPairs : Finset (State × State) :=
  (M.wellNestedStep^[Fintype.card (State × State)]) ∅

theorem coe_wellNestedStep (R : Finset (State × State)) :
    (M.wellNestedStep R : Set (State × State)) = M.wellNestedRule R := by
  ext p
  simp [wellNestedStep, wellNestedRule]

theorem coe_iterate_wellNestedStep (k : ℕ) :
    ((M.wellNestedStep^[k] ∅ : Finset (State × State)) : Set (State × State)) =
      (M.wellNestedRuleHom^[k]) ⊥ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', coe_wellNestedStep, ih]
    rfl

/-- **Lemma 1 for the computed set**: `(s, s') ∈ WR` exactly when the MPDA has a well-nested run
from `s` to `s'` (`MPDA.wellNestedReach_iff`). -/
theorem mem_wellNestedPairs {s s' : State} :
    (s, s') ∈ M.wellNestedPairs ↔ M.WellNestedReach s s' := by
  rw [← Finset.mem_coe, wellNestedPairs, coe_iterate_wellNestedStep,
    OrderHom.iterate_card_bot_eq_lfp, lfp_wellNestedRuleHom]
  rfl

end Compute

/-! ## Hole segments -/

/-- An atomic hole segment `(s, α, s')`: a push of `α` from `s`, followed by a well-nested run to
`s'`. The stack of the push is the index of the set `AHSᵢ` that contains the segment. -/
structure AtomicHole (State Γ : Type*) where
  /-- The state where the push starts. -/
  src : State
  /-- The pushed stack symbol. -/
  sym : Γ
  /-- The state where the well-nested run after the push ends. -/
  dst : State
  deriving DecidableEq

/-- Atomic hole segments are in bijection with the triples of their fields. -/
@[expose] def AtomicHole.equivProd (State Γ : Type*) : AtomicHole State Γ ≃ State × Γ × State where
  toFun h := (h.src, h.sym, h.dst)
  invFun := fun (s, γ, s') => ⟨s, γ, s'⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Fintype State] [Fintype Γ] : Fintype (AtomicHole State Γ) :=
  Fintype.ofEquiv _ (AtomicHole.equivProd State Γ).symm

section Holes

variable [Fintype State] [DecidableEq State] [Fintype Symbol] [Fintype Γ]
  (M : MPDA n State Symbol Γ) [∀ s μ s', Decidable (M.Tr s μ s')]

/-- The atomic hole segments `AHSᵢ` of stack `i` (Algorithm 1, lines 5–8, of
[AkshayGastinKrishnaRoychowdhury2020]): the segments `(s, α, s')` such that a push of `α` on stack
`i` from `s`, followed by a well-nested run, reaches `s'`. -/
@[expose] def atomicHoles (i : Fin n) : Finset (AtomicHole State Γ) :=
  let wr := M.wellNestedPairs
  Finset.univ.filter fun h => ∃ (a : Symbol) (s₁ : State), M.Tr h.src (a, .push i h.sym) s₁ ∧
    (s₁, h.dst) ∈ wr

theorem mem_atomicHoles {i : Fin n} {s s' : State} {γ : Γ} :
    ⟨s, γ, s'⟩ ∈ M.atomicHoles i ↔
      ∃ (a : Symbol) (s₁ : State), M.Tr s (a, .push i γ) s₁ ∧ M.WellNestedReach s₁ s' := by
  simp [atomicHoles, mem_wellNestedPairs]

/-- An atomic hole segment is a push of `α` on stack `i` followed by a well-nested run. -/
theorem mem_atomicHoles_iff_mTr {i : Fin n} {s s' : State} {γ : Γ} :
    ⟨s, γ, s'⟩ ∈ M.atomicHoles i ↔ ∃ (a : Symbol) (w : List (Symbol × Op n Γ)),
      WellNested w ∧ M.MTr s ((a, .push i γ) :: w) s' := by
  rw [mem_atomicHoles]
  constructor
  · rintro ⟨a, s₁, ht, hw⟩
    obtain ⟨w, hw, hrun⟩ := wellNestedReach_iff.mp hw
    exact ⟨a, w, hw, .stepL ht hrun⟩
  · rintro ⟨a, w, hw, hrun⟩
    obtain ⟨s₁, ht, hrun⟩ := LTS.MTr.cons_iff.mp hrun
    exact ⟨a, s₁, ht, wellNestedReach_iff.mpr ⟨w, hw, hrun⟩⟩

/-- The hole segments `HSᵢ` of stack `i` (Algorithm 1, line 9): the reflexive-transitive closure of
the atomic hole segments, forgetting the pushed symbols. The source writes `TransitiveClosure`;
the closure must be reflexive, since `AddPop` (Algorithm 4) splits off the only atomic segment of
a hole through a triple `(i, s, s)`. Reflexivity also lets `AddHole` (Algorithm 3) open a hole
`(i, s, s)` without taking a transition, even from a state with no push; such a hole is realized
by the empty factor. -/
@[expose] def holeSegments [DecidableEq Γ] (i : Fin n) : Finset (State × State) :=
  let ahs := M.atomicHoles i
  Relation.reflTransGenFinset fun s s' => ∃ γ, ⟨s, γ, s'⟩ ∈ ahs

theorem mem_holeSegments [DecidableEq Γ] {i : Fin n} {s s' : State} :
    (s, s') ∈ M.holeSegments i ↔
      Relation.ReflTransGen (fun s s' => ∃ γ, ⟨s, γ, s'⟩ ∈ M.atomicHoles i) s s' :=
  Relation.mem_reflTransGenFinset _

end Holes

/-! ## Lists and the search -/

/-- A hole triple `(i, s, s')` of a list of the search: an open hole of stack `i`, abstracted by a
hole segment from `s` to `s'`. -/
structure HoleTriple (n : ℕ) (State : Type*) where
  /-- The stack of the hole. -/
  stack : Fin n
  /-- The state where the hole starts, the source of its first push. -/
  src : State
  /-- The state where the hole segment ends. -/
  dst : State
  deriving DecidableEq

/-- Hole triples are in bijection with the triples of their fields. -/
@[expose] def HoleTriple.equivProd (n : ℕ) (State : Type*) :
    HoleTriple n State ≃ Fin n × State × State where
  toFun h := (h.stack, h.src, h.dst)
  invFun := fun (i, s, s') => ⟨i, s, s'⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Fintype State] : Fintype (HoleTriple n State) :=
  Fintype.ofEquiv _ (HoleTriple.equivProd n State).symm

/-- A list of the search of Algorithm 1 of [AkshayGastinKrishnaRoychowdhury2020]: the open hole
triples, oldest first, and the last control state. The source's lists also start with the initial
state, which the search does not need. -/
structure HoleList (n : ℕ) (State : Type*) where
  /-- The open hole triples, oldest first. -/
  holes : List (HoleTriple n State)
  /-- The last control state. -/
  last : State
  deriving DecidableEq

/-- Split a list of hole triples at its last triple of stack `i`, `l = pre ++ ⟨i, s, s'⟩ :: post`
where `post` has no triple of stack `i`: the result is `pre`, the endpoints `(s, s')` and `post`.
This is `lastHoleᵢ` of Algorithm 4. -/
@[expose] def splitLastHole (i : Fin n) :
    List (HoleTriple n State) → Option (List (HoleTriple n State) × (State × State) ×
      List (HoleTriple n State))
  | [] => none
  | h :: t =>
    match splitLastHole i t with
    | some (pre, x, post) => some (h :: pre, x, post)
    | none => if h.stack = i then some ([], (h.src, h.dst), t) else none

theorem splitLastHole_eq_some {i : Fin n} :
    ∀ {l pre post : List (HoleTriple n State)} {s s' : State},
      splitLastHole i l = some (pre, (s, s'), post) →
        l = pre ++ ⟨i, s, s'⟩ :: post ∧ ∀ h ∈ post, h.stack ≠ i
  | [], _, _, _, _, h => by simp [splitLastHole] at h
  | ⟨j, a, b⟩ :: t, pre, post, s, s', hs => by
    unfold splitLastHole at hs
    rcases ht : splitLastHole i t with _ | ⟨pre', ⟨x, x'⟩, post'⟩
    · rw [ht] at hs
      simp only at hs
      split_ifs at hs with hi
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, ⟨rfl, rfl⟩, rfl⟩ := hs
      subst hi
      exact ⟨rfl, fun h' hh' hh => splitLastHole_none_of_mem ht h' hh' hh⟩
    · rw [ht] at hs
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, ⟨rfl, rfl⟩, rfl⟩ := hs
      obtain ⟨rfl, hpost⟩ := splitLastHole_eq_some ht
      exact ⟨rfl, hpost⟩
where
  /-- If `splitLastHole` fails, no triple has stack `i`. -/
  splitLastHole_none_of_mem {i : Fin n} : ∀ {l : List (HoleTriple n State)},
      splitLastHole i l = none → ∀ h ∈ l, h.stack = i → False
    | [], _, _, hh, _ => by simp at hh
    | h :: t, hs, h', hh', hi => by
      unfold splitLastHole at hs
      rcases ht : splitLastHole i t with _ | ⟨pre', x', post'⟩
      · rw [ht] at hs
        simp only at hs
        split_ifs at hs with hhi
        rcases List.mem_cons.mp hh' with rfl | hh'
        · exact hhi hi
        · exact splitLastHole_none_of_mem ht h' hh' hi
      · rw [ht] at hs
        simp at hs

section Search

variable [Fintype State] [DecidableEq State] [Fintype Symbol] [Fintype Γ] [DecidableEq Γ]
  (M : MPDA n State Symbol Γ) [∀ s μ s', Decidable (M.Tr s μ s')]

/-- `AddHoleᵢ` (Algorithm 3 of [AkshayGastinKrishnaRoychowdhury2020]): extend the list with a hole
segment of stack `i` that starts at its last state. Since `HSᵢ` is reflexive here, this includes
the empty hole `(i, s, s)` at the last state `s`, opened without a transition. -/
@[expose] def addHole (i : Fin n) (μ : HoleList n State) : Finset (HoleList n State) :=
  ((M.holeSegments i).filter fun p => p.1 = μ.last).image fun p =>
    ⟨μ.holes ++ [⟨i, p.1, p.2⟩], p.2⟩

/-- `AddPopᵢ` (Algorithm 4): a pop from stack `i` at the last state that matches the last pending
push of the last open hole `(i, s₁, s₃)` of stack `i`. The hole splits into a hole segment
`(i, s₁, s₂)` and an atomic hole segment `(s₂, α, s₃)` pushing `α`, the pop of `α` leads to `s'`,
and a well-nested run continues to `s''`. The hole shrinks to `(i, s₁, s₂)`; when `s₁ = s₂` it may
also be removed. Without an open hole of stack `i` there is no successor. -/
@[expose] def addPop (i : Fin n) (μ : HoleList n State) : Finset (HoleList n State) :=
  match splitLastHole i μ.holes with
  | none => ∅
  | some (pre, (s₁, s₃), post) =>
    let hs := M.holeSegments i
    let ahs := M.atomicHoles i
    let wr := M.wellNestedPairs
    let ok : State × Γ × State × State → Prop := fun (s₂, γ, s', s'') =>
      (s₁, s₂) ∈ hs ∧ ⟨s₂, γ, s₃⟩ ∈ ahs ∧ (∃ b, M.Tr μ.last (b, .pop i γ) s') ∧ (s', s'') ∈ wr
    (Finset.univ.filter ok).image (fun (s₂, _, _, s'') => ⟨pre ++ ⟨i, s₁, s₂⟩ :: post, s''⟩) ∪
      ((Finset.univ.filter fun t => ok t ∧ t.1 = s₁).image fun (_, _, _, s'') => ⟨pre ++ post, s''⟩)

/-- The children of a list in the search: holes while fewer than `K` are open, and pops. -/
@[expose] def successors (K : ℕ) (μ : HoleList n State) : Finset (HoleList n State) :=
  (if μ.holes.length < K then Finset.univ.biUnion fun i => M.addHole i μ else ∅) ∪
    Finset.univ.biUnion fun i => M.addPop i μ

/-- The worklist loop of Algorithm 1: add the new children of the lists to do, until there are
none, or the fuel runs out. -/
@[expose] def explore (K : ℕ) :
    ℕ → Finset (HoleList n State) → Finset (HoleList n State) → Finset (HoleList n State)
  | 0, visited, _ => visited
  | k + 1, visited, todo =>
    if todo = ∅ then visited else
      let new := todo.biUnion (M.successors K) \ visited
      explore K k (visited ∪ new) new

/-- The initial lists of the repaired search: a state reached from an initial state by a
well-nested run, and no holes. The search as printed starts from the initial state itself (line
10 of Algorithm 1), and so misses runs whose first hole push follows a nonempty well-nested
factor. -/
@[expose] def initialLists [DecidablePred (· ∈ M.start)] : Finset (HoleList n State) :=
  (Finset.univ.filter fun s => ∃ s₀, s₀ ∈ M.start ∧ (s₀, s) ∈ M.wellNestedPairs).image
    fun s => ⟨[], s⟩

/-- A bound on the number of lists with at most `K` holes, used as the fuel of the search. -/
@[expose] def listBound (n : ℕ) (State : Type*) [Fintype State] (K : ℕ) : ℕ :=
  (n * Fintype.card State ^ 2 + 1) ^ K * Fintype.card State + 1

/-- The search of Algorithm 1 from the lists `init`: `true` when no list reached without open
holes reaches an accepting state through a well-nested run. The source checks the initial state
before the loop (line 3) and each new list obtained by a pop (line 25); both checks are this
one. -/
@[expose] def isEmptyFrom [DecidablePred (· ∈ M.accept)] (init : Finset (HoleList n State))
    (K : ℕ) : Bool :=
  decide (¬∃ μ ∈ M.explore K (listBound n State K) init init,
    μ.holes = [] ∧ ∃ f ∈ (Finset.univ.filter (· ∈ M.accept)), (μ.last, f) ∈ M.wellNestedPairs)

/-- **Repaired Algorithm 1** of [AkshayGastinKrishnaRoychowdhury2020]. It differs from the
printed algorithm in two ways: the search starts from the states reached from an initial state by
a well-nested run (`initialLists`), not from the initial state alone; and `HSᵢ` is the
reflexive-transitive closure of `AHSᵢ` (`holeSegments`). -/
@[expose] def isEmpty [DecidablePred (· ∈ M.start)] [DecidablePred (· ∈ M.accept)] (K : ℕ) :
    Bool :=
  M.isEmptyFrom M.initialLists K

end Search

/-! ## The search computes the reachable lists -/

section Reach

variable [Fintype State] [DecidableEq State] [Fintype Symbol] [Fintype Γ] [DecidableEq Γ]
  (M : MPDA n State Symbol Γ) [∀ s μ s', Decidable (M.Tr s μ s')]

/-- The lists the search of Algorithm 1 reaches from the lists `init`: closed under
`successors`. -/
inductive Reachable (K : ℕ) (init : Finset (HoleList n State)) : HoleList n State → Prop where
  | init {μ : HoleList n State} : μ ∈ init → Reachable K init μ
  | step {μ ν : HoleList n State} : Reachable K init μ → ν ∈ M.successors K μ →
    Reachable K init ν

variable {M}

omit [DecidableEq Γ] in
theorem mem_initialLists [DecidablePred (· ∈ M.start)] {μ : HoleList n State} :
    μ ∈ M.initialLists ↔
      μ.holes = [] ∧ ∃ s₀ ∈ M.start, (s₀, μ.last) ∈ M.wellNestedPairs := by
  obtain ⟨holes, last⟩ := μ
  simp [initialLists, eq_comm, and_comm]

theorem length_holes_le_of_mem_successors {K : ℕ} {μ ν : HoleList n State}
    (hμ : μ.holes.length ≤ K) (hν : ν ∈ M.successors K μ) : ν.holes.length ≤ K := by
  simp only [successors, Finset.mem_union] at hν
  rcases hν with hν | hν
  · split_ifs at hν with hK
    · obtain ⟨i, -, hν⟩ := Finset.mem_biUnion.mp hν
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hν
      simp only [List.length_append, List.length_singleton]
      omega
    · simp at hν
  · obtain ⟨i, -, hν⟩ := Finset.mem_biUnion.mp hν
    unfold addPop at hν
    rcases hs : splitLastHole i μ.holes with _ | ⟨pre, ⟨s₁, s₃⟩, post⟩
    · simp [hs] at hν
    · obtain ⟨hl, -⟩ := splitLastHole_eq_some hs
      rw [hl] at hμ
      simp only [hs, Finset.mem_union, Finset.mem_image] at hν
      rcases hν with ⟨t, -, rfl⟩ | ⟨t, -, rfl⟩ <;>
        simp only [List.length_append, List.length_cons] at hμ ⊢ <;> omega

theorem Reachable.length_le {K : ℕ} {init : Finset (HoleList n State)}
    (hinit : ∀ μ ∈ init, μ.holes = []) {μ : HoleList n State} (h : M.Reachable K init μ) :
    μ.holes.length ≤ K := by
  induction h with
  | init hμ => simp [hinit _ hμ]
  | step _ hν ih => exact length_holes_le_of_mem_successors ih hν

/-- The lists with at most `K` holes, as a finite set. -/
private noncomputable def listsUpTo (n : ℕ) (State : Type*) [Fintype State] [DecidableEq State]
    (K : ℕ) : Finset (HoleList n State) :=
  (((Finset.univ : Finset (HoleTriple n State)).toList.listsUpTo K).toFinset ×ˢ
    (Finset.univ : Finset State)).image fun p => ⟨p.1, p.2⟩

private theorem mem_listsUpTo_of_length_le {K : ℕ} {μ : HoleList n State}
    (h : μ.holes.length ≤ K) : μ ∈ listsUpTo n State K := by
  refine Finset.mem_image.mpr ⟨(μ.holes, μ.last), ?_, rfl⟩
  simp [List.mem_listsUpTo, h]

private theorem card_listsUpTo_le (K : ℕ) :
    (listsUpTo n State K).card + 1 ≤ listBound n State K := by
  unfold listsUpTo listBound
  refine Nat.add_le_add_right ((Finset.card_image_le).trans ?_) 1
  rw [Finset.card_product, Finset.card_univ]
  refine Nat.mul_le_mul_right _ ((List.toFinset_card_le _).trans
    ((List.length_listsUpTo_le _ _).trans ?_))
  simp [Fintype.card_congr (HoleTriple.equivProd n State), Fintype.card_prod, pow_two]

/-- A set of lists that contains the initial lists, is closed under `successors` and only contains
reachable lists is the set of reachable lists. -/
private theorem mem_iff_reachable_of_closed {K : ℕ} {init visited : Finset (HoleList n State)}
    (hreach : ∀ μ ∈ visited, M.Reachable K init μ) (hinit : init ⊆ visited)
    (hclosed : ∀ μ ∈ visited, M.successors K μ ⊆ visited) (μ : HoleList n State) :
    μ ∈ visited ↔ M.Reachable K init μ := by
  refine ⟨hreach μ, fun h => ?_⟩
  induction h with
  | init hμ => exact hinit hμ
  | step _ hν ih => exact hclosed _ ih hν

/-- The worklist loop returns the reachable lists, as long as the fuel exceeds the number of lists
that could still be added while work remains. -/
private theorem mem_explore_iff {K : ℕ} {init : Finset (HoleList n State)}
    (hinit₀ : ∀ μ ∈ init, μ.holes = []) (f : ℕ) :
    ∀ (visited todo : Finset (HoleList n State)),
      (∀ μ ∈ visited, M.Reachable K init μ) → todo ⊆ visited → init ⊆ visited →
      (∀ μ ∈ visited, μ ∉ todo → M.successors K μ ⊆ visited) →
      (todo.Nonempty → (listsUpTo n State K).card < f + visited.card) →
      ∀ μ, μ ∈ M.explore K f visited todo ↔ M.Reachable K init μ := by
  induction f with
  | zero =>
    intro visited todo hreach htodo hinit hclosed hfuel μ
    rcases Finset.eq_empty_or_nonempty todo with rfl | hne
    · exact mem_iff_reachable_of_closed hreach hinit
        (fun ν hν => hclosed ν hν (Finset.notMem_empty _)) μ
    · have hcard : visited.card ≤ (listsUpTo n State K).card := Finset.card_le_card
        fun ν hν => mem_listsUpTo_of_length_le ((hreach ν hν).length_le hinit₀)
      have := hfuel hne
      omega
  | succ f ih =>
    intro visited todo hreach htodo hinit hclosed hfuel μ
    unfold explore
    split_ifs with hempty
    · subst hempty
      exact mem_iff_reachable_of_closed hreach hinit
        (fun ν hν => hclosed ν hν (Finset.notMem_empty _)) μ
    · set new := todo.biUnion (M.successors K) \ visited with hnew
      refine ih (visited ∪ new) new ?_ Finset.subset_union_right
        (hinit.trans Finset.subset_union_left) ?_ ?_ μ
      · intro ν hν
        rcases Finset.mem_union.mp hν with hν | hν
        · exact hreach ν hν
        · obtain ⟨hν, -⟩ := Finset.mem_sdiff.mp hν
          obtain ⟨ρ, hρ, hν⟩ := Finset.mem_biUnion.mp hν
          exact .step (hreach ρ (htodo hρ)) hν
      · intro ρ hρ hρnew ν hν
        rcases Finset.mem_union.mp hρ with hρ | hρ
        · by_cases hρt : ρ ∈ todo
          · by_cases hνv : ν ∈ visited
            · exact Finset.mem_union_left _ hνv
            · exact Finset.mem_union_right _
                (Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨ρ, hρt, hν⟩, hνv⟩)
          · exact Finset.mem_union_left _ (hclosed ρ hρ hρt hν)
        · exact absurd hρ hρnew
      · intro hne
        rw [Finset.card_union_of_disjoint Finset.disjoint_sdiff]
        have := hfuel (Finset.nonempty_iff_ne_empty.mpr hempty)
        have hpos := hne.card_pos
        rw [hnew] at hpos
        omega

/-- The search of Algorithm 1 returns exactly the reachable lists: the fuel `listBound` is never
exhausted. -/
theorem mem_explore {K : ℕ} {init : Finset (HoleList n State)}
    (hinit : ∀ μ ∈ init, μ.holes = []) {μ : HoleList n State} :
    μ ∈ M.explore K (listBound n State K) init init ↔ M.Reachable K init μ := by
  refine mem_explore_iff hinit _ _ _ (fun ν hν => .init hν) subset_rfl subset_rfl
    (fun ν hν hνt => absurd hν hνt) (fun _ => ?_) μ
  · have := card_listsUpTo_le (n := n) (State := State) K
    omega

end Reach

end Cslib.Automata.MPDA
