/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Analysis.Convex.ExtendedFormulation.StableSet
public import CslibFrontier.Foundations.Analysis.Convex.ExtendedFormulation.TourSplit
public import CslibFrontier.Foundations.Data.List.ConsecutivePairs
import CslibFrontier.Tactic.FinIndex
import Mathlib.Tactic.FinCases

/-!
# Directed Hamiltonian gadget for the correlation polytope

This module formalizes Steps (i) and (ii) of [FioriniMassarPokuttaTiwaryDeWolf2015, Lemma 11],
encoding the correlation equations `C_{ij} = C_{ii} ∧ C_{jj}` for `i < j` as a `3`-SAT formula
and realizing its satisfying assignments via Sipser's diamond–clause directed graph `CorrDigraph`
on `O(p²)` vertices (`card_corrDigraphV_le`).

## Main definitions

* `CorrVar`, `CorrDigraphV`, `corrDigraphAdj`: Sipser's directed Hamiltonian-cycle gadget graph
  for the correlation equations on `Fin p`.
* `slotClause`: maps each variable-chain slot `(v, ℓ)` to at most one `(clause, polarity)`.

## Main results

* `card_corrDigraphV_le`: `Fintype.card (CorrDigraphV p) ≤ 23 * p ^ 2` for `1 ≤ p`.
* `exists_dirTour_of_assignment`: every `b : Finset (Fin p)` yields a directed Hamiltonian tour
  whose `(chain v 1, chain v 0)` arcs encode `b bᵀ`.
* `exists_assignment_of_dirTour`: every directed Hamiltonian tour of `corrDigraphAdj p`
  encodes `b bᵀ` for some `b : Finset (Fin p)`.

## References

* [FioriniMassarPokuttaTiwaryDeWolf2015], Section 3.4 (Lemma 11, Steps (i)–(ii)).
-/


public section

/-- Variables of the correlation `3`-SAT formula on `Fin p`: diagonal `C_{ii}` and
upper-triangular off-diagonal `C_{ij}` (`i < j`). -/
inductive CorrVar (p : ℕ) : Type
  | diag (i : Fin p)
  | off (e : CorrPairIdx p)
  deriving DecidableEq

/-- Equivalence between `CorrVar p` and `Fin p ⊕ CorrPairIdx p`. -/
def corrVarEquivSum (p : ℕ) : CorrVar p ≃ Fin p ⊕ CorrPairIdx p where
  toFun
    | .diag i => Sum.inl i
    | .off e => Sum.inr e
  invFun
    | Sum.inl i => .diag i
    | Sum.inr e => .off e
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with i | e <;> rfl

instance (p : ℕ) : Fintype (CorrVar p) :=
  Fintype.ofEquiv _ (corrVarEquivSum p).symm

instance (p : ℕ) [NeZero p] : Nonempty (CorrVar p) := ⟨.diag 0⟩

/-- Number of occurrence slots in the chain of `v : CorrVar p`. -/
@[expose] def chainSlots (p : ℕ) : CorrVar p → ℕ
  | .diag _ => 4 * p
  | .off _ => 4

/-- Number of chain vertices in the diamond gadget of `v : CorrVar p` (`3 * slots + 1`). -/
@[expose] def chainLen (p : ℕ) (v : CorrVar p) : ℕ :=
  3 * chainSlots p v + 1

theorem two_le_chainLen {p : ℕ} (hp : 1 ≤ p) (v : CorrVar p) : 2 ≤ chainLen p v := by
  cases v <;> simp only [chainLen, chainSlots] <;> omega

/-- Cyclic next variable in `CorrVar p` (`p ≥ 1`). -/
noncomputable def varNext {p : ℕ} (hp : 1 ≤ p) (v : CorrVar p) : CorrVar p :=
  have : NeZero (Fintype.card (CorrVar p)) := ⟨@Fintype.card_ne_zero _ _ ⟨.diag ⟨0, hp⟩⟩⟩
  let e := Fintype.equivFin (CorrVar p)
  e.symm (e v + 1)

theorem varNext_bijective {p : ℕ} (hp : 1 ≤ p) : Function.Bijective (varNext hp) := by
  have : NeZero (Fintype.card (CorrVar p)) := ⟨@Fintype.card_ne_zero _ _ ⟨.diag ⟨0, hp⟩⟩⟩
  exact ((Fintype.equivFin _).symm.bijective.comp (Equiv.addRight 1).bijective).comp
    (Fintype.equivFin (CorrVar p)).bijective

/-- Vertices of the directed correlation gadget `D_p`
[FioriniMassarPokuttaTiwaryDeWolf2015, Section 3.4, Step (ii)]. -/
inductive CorrDigraphV (p : ℕ) : Type
  | gate (v : CorrVar p)
  | chain (v : CorrVar p) (k : Fin (chainLen p v))
  | clause (e : CorrPairIdx p) (c : Fin 4)
  deriving DecidableEq

/-- Equivalence unpacking `CorrDigraphV p` into sums and products for cardinality bounds. -/
def corrDigraphVEquiv (p : ℕ) :
    CorrDigraphV p ≃ CorrVar p ⊕ (Σ v : CorrVar p, Fin (chainLen p v)) ⊕ (CorrPairIdx p × Fin 4)
    where
  toFun
    | .gate v => Sum.inl v
    | .chain v k => Sum.inr (Sum.inl ⟨v, k⟩)
    | .clause e c => Sum.inr (Sum.inr (e, c))
  invFun
    | Sum.inl v => .gate v
    | Sum.inr (Sum.inl ⟨v, k⟩) => .chain v k
    | Sum.inr (Sum.inr (e, c)) => .clause e c
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with v | ⟨v, k⟩ | ⟨e, c⟩ <;> rfl

instance (p : ℕ) : Fintype (CorrDigraphV p) :=
  Fintype.ofEquiv _ (corrDigraphVEquiv p).symm

instance (p : ℕ) [NeZero p] : Nonempty (CorrDigraphV p) := ⟨.gate (.diag 0)⟩

/-- Quadratic vertex-count bound `|V(D_p)| ≤ 23 p²` for `p ≥ 1`. -/
theorem card_corrDigraphV_le {p : ℕ} (hp : 1 ≤ p) : Fintype.card (CorrDigraphV p) ≤ 23 * p ^ 2 := by
  have hcard_pair : 2 * Fintype.card (CorrPairIdx p) ≤ p ^ 2 := by
    have hle := Fintype.card_le_of_injective
      (Sum.elim (fun e : CorrPairIdx p => (e.fst, e.snd)) fun e : CorrPairIdx p => (e.snd, e.fst))
      (by
        rintro (⟨a, b, h⟩ | ⟨a, b, h⟩) (⟨a', b', h'⟩ | ⟨a', b', h'⟩) heq <;>
          simp only [Sum.elim_inl, Sum.elim_inr, Prod.mk.injEq] at heq <;>
          obtain ⟨rfl, rfl⟩ := heq <;> first | rfl | exact absurd h (lt_asymm h'))
    rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] at hle
    nlinarith
  have hsig : ∑ v : CorrVar p, chainLen p v =
      p * (12 * p + 1) + Fintype.card (CorrPairIdx p) * 13 := by
    rw [← (corrVarEquivSum p).symm.sum_comp, Fintype.sum_sum_type]
    simp [corrVarEquivSum, chainLen, chainSlots, ← mul_assoc]
  simp only [Fintype.card_congr (corrDigraphVEquiv p), Fintype.card_sum,
    Fintype.card_congr (corrVarEquivSum p), Fintype.card_fin, Fintype.card_sigma,
    Fintype.card_prod, hsig]
  nlinarith

theorem three_le_card_corrDigraphV {p : ℕ} (hp : 1 ≤ p) : 3 ≤ Fintype.card (CorrDigraphV p) := by
  have h := Fintype.card_le_of_injective (CorrDigraphV.chain (.diag ⟨0, hp⟩))
    fun _ _ he => by cases he; rfl
  rw [Fintype.card_fin, chainLen, chainSlots] at h
  omega

theorem two_le_card_corrDigraphV {p : ℕ} (hp : 1 ≤ p) : 2 ≤ Fintype.card (CorrDigraphV p) :=
  by have := three_le_card_corrDigraphV hp; omega

/-- Polarity of literal 1 (`C_{ii}`), literal 2 (`C_{jj}`), and literal 3 (`C_{ij}`) in the
four clauses enforcing `C_{ij} = C_{ii} ∧ C_{jj}`
[FioriniMassarPokuttaTiwaryDeWolf2015, Step (i)]. -/
@[expose] def clauseLit₁ : Fin 4 → Bool
  | 0 => false
  | 1 => true
  | 2 => true
  | 3 => false

/-- Polarity of literal 2 (`C_{jj}`) in the four clauses enforcing `C_{ij} = C_{ii} ∧ C_{jj}`
[FioriniMassarPokuttaTiwaryDeWolf2015, Step (i)]. -/
@[expose] def clauseLit₂ : Fin 4 → Bool
  | 0 => false
  | 1 => true
  | 2 => false
  | 3 => true

/-- Polarity of literal 3 (`C_{ij}`) in the four clauses enforcing `C_{ij} = C_{ii} ∧ C_{jj}`
[FioriniMassarPokuttaTiwaryDeWolf2015, Step (i)]. -/
@[expose] def clauseLit₃ : Fin 4 → Bool
  | 0 => true
  | 1 => false
  | 2 => false
  | 3 => false

theorem forall_clause_iff_eq_and (bi bj be : Bool) :
    (∀ c : Fin 4, bi = clauseLit₁ c ∨ bj = clauseLit₂ c ∨ be = clauseLit₃ c) ↔
      be = (bi && bj) := by
  revert bi bj be
  decide

/-- Unique clause and literal polarity attached to slot `(v, ℓ)`, if any. -/
def slotClause (p : ℕ) :
    (v : CorrVar p) → Fin (chainSlots p v) → Option ((CorrPairIdx p × Fin 4) × Bool)
  | .diag i, ℓ =>
      let j : Fin p := ⟨ℓ.1 / 4, by have := ℓ.2; simp only [chainSlots] at this; omega⟩
      let c : Fin 4 := ⟨ℓ.1 % 4, by omega⟩
      if h1 : i < j then some ((⟨i, j, h1⟩, c), clauseLit₁ c)
      else if h2 : j < i then some ((⟨j, i, h2⟩, c), clauseLit₂ c)
      else none
  | .off e, ℓ => some ((e, ℓ), clauseLit₃ ℓ)

theorem slotClause_eq_some_iff {p : ℕ} {v : CorrVar p} {ℓ : Fin (chainSlots p v)}
    {e : CorrPairIdx p} {c : Fin 4} {lit : Bool} :
    slotClause p v ℓ = some ((e, c), lit) ↔
      (v = .diag e.fst ∧ ℓ.1 = 4 * Fin.val e.snd + c.1 ∧ lit = clauseLit₁ c) ∨
      (v = .diag e.snd ∧ ℓ.1 = 4 * Fin.val e.fst + c.1 ∧ lit = clauseLit₂ c) ∨
      (v = .off e ∧ ℓ.1 = c.1 ∧ lit = clauseLit₃ c) := by
  cases v with
  | diag i =>
      obtain ⟨a, b, hab⟩ := e
      -- The slot `ℓ = 4 * j + c'` carries clause `c'` of the pair `{i, j}`.
      obtain ⟨j, c', hℓ, hsc⟩ : ∃ (j : Fin p) (c' : Fin 4), ℓ.1 = 4 * j.1 + c'.1 ∧
          slotClause p (.diag i) ℓ =
            if h1 : i < j then some ((⟨i, j, h1⟩, c'), clauseLit₁ c')
            else if h2 : j < i then some ((⟨j, i, h2⟩, c'), clauseLit₂ c') else none :=
        ⟨_, _, by dsimp only; omega, rfl⟩
      rw [hsc, hℓ]
      split_ifs with h1 h2 <;> grind
  | off e' =>
      simp only [slotClause, Option.some.injEq, Prod.mk.injEq, reduceCtorEq, false_and, false_or,
        CorrVar.off.injEq]
      exact ⟨by rintro ⟨⟨rfl, rfl⟩, rfl⟩; exact ⟨rfl, rfl, rfl⟩,
        by rintro ⟨rfl, hc, rfl⟩; cases Fin.ext hc; exact ⟨rfl, rfl⟩⟩

/-- Directed adjacency of `D_p` [FioriniMassarPokuttaTiwaryDeWolf2015, §3.4, Step (ii)]. -/
@[expose] def corrDigraphAdj (p : ℕ) (hp : 1 ≤ p) : CorrDigraphV p → CorrDigraphV p → Prop
  | .gate v, .chain v' k => v = v' ∧ (k.1 = 0 ∨ k.1 + 1 = chainLen p v)
  | .chain v' k, .gate v => v = varNext hp v' ∧ (k.1 = 0 ∨ k.1 + 1 = chainLen p v')
  | .chain v₁ k₁, .chain v₂ k₂ => v₁ = v₂ ∧ (k₁.1 + 1 = k₂.1 ∨ k₂.1 + 1 = k₁.1)
  | .chain v k, .clause e c =>
      ∃ (ℓ : Fin (chainSlots p v)) (lit : Bool), slotClause p v ℓ = some ((e, c), lit) ∧
        ((lit = false ∧ k.1 = 3 * ℓ.1 + 1) ∨ (lit = true ∧ k.1 = 3 * ℓ.1 + 2))
  | .clause e c, .chain v k =>
      ∃ (ℓ : Fin (chainSlots p v)) (lit : Bool), slotClause p v ℓ = some ((e, c), lit) ∧
        ((lit = false ∧ k.1 = 3 * ℓ.1 + 2) ∨ (lit = true ∧ k.1 = 3 * ℓ.1 + 1))
  | _, _ => False

theorem corrDigraphAdj_irrefl {p : ℕ} (hp : 1 ≤ p) (u : CorrDigraphV p) :
    ¬ corrDigraphAdj p hp u u := by
  cases u <;> simp [corrDigraphAdj]

section TourAssignment

private theorem chainSlots_pos {p : ℕ} (hp : 1 ≤ p) (v : CorrVar p) : 0 < chainSlots p v := by
  cases v <;> simp only [chainSlots] <;> omega

/-- `chain_lt` proves that an index is in the range of a chain: it unfolds `chainLen` and calls
`omega`. -/
local macro "chain_lt" : tactic => `(tactic| (simp only [chainLen]; omega))

/-- `ch(v, n)` is the chain vertex of `v` with index `n`. The bound `n < chainLen p v` is proved
by `chain_lt`, with `chainSlots_pos` when it needs the chain to have a slot. -/
local macro "ch(" v:term ", " n:term ")" : term =>
  `(CorrDigraphV.chain $v
    ⟨$n, by first | chain_lt | (have := chainSlots_pos (by assumption) $v; chain_lt)⟩)

/-- Equal chain vertices of one variable have equal indices. -/
private theorem chain_inj {p : ℕ} {v : CorrVar p} {a b : ℕ} {ha : a < chainLen p v}
    {hb : b < chainLen p v} (h : CorrDigraphV.chain v ⟨a, ha⟩ = .chain v ⟨b, hb⟩) : a = b :=
  congrArg Fin.val (eq_of_heq (CorrDigraphV.chain.inj h).2)

private theorem val_head_finRange {n : ℕ} (h : List.finRange n ≠ []) :
    ((List.finRange n).head h).1 = 0 := by
  simp [List.head_eq_getElem]

private theorem val_getLast_finRange {n : ℕ} (h : List.finRange n ≠ []) :
    ((List.finRange n).getLast h).1 = n - 1 := by
  simp [List.getLast_eq_getElem]

private theorem val_succ_of_mem_consecutivePairs_finRange {n : ℕ} {i j : Fin n}
    (h : (i, j) ∈ (List.finRange n).consecutivePairs) : i.1 + 1 = j.1 := by
  obtain ⟨k, hk, rfl, rfl⟩ := List.mem_consecutivePairs_iff_exists_getElem.1 h
  simp

/-- The consecutive pairs of a contiguous sublist are consecutive pairs of the list. -/
private theorem consecutivePairs_subset_of_infix {α : Type*} {l₁ l₂ : List α} (h : l₁ <:+: l₂) :
    l₁.consecutivePairs ⊆ l₂.consecutivePairs := by
  obtain ⟨s, t, rfl⟩ := h
  rintro ⟨x, y⟩ hxy
  obtain ⟨i, hi, rfl, rfl⟩ := List.mem_consecutivePairs_iff_exists_getElem.1 hxy
  have hi' : i < l₁.length := by omega
  exact List.mem_consecutivePairs_iff_exists_getElem.2
    ⟨s.length + i, by simp; omega, by simp [hi'], by simp [add_assoc, hi]⟩

/-- A duplicate-free list of all elements of a nonempty finite type is a cyclic enumeration `τ`
whose steps `τ t → τ (t + 1)` are the consecutive pairs of the list and the pair from its last
to its first element. -/
private theorem exists_tour_of_list {α : Type*} [Fintype α] [Nonempty α] {l : List α}
    (hnd : l.Nodup) (hmem : ∀ x, x ∈ l) (hl : l ≠ []) (h2 : 2 ≤ Fintype.card α) :
    ∃ τ : Fin (Fintype.card α) ≃ α, ∀ x y, (∃ t, τ t = x ∧ τ (t + 1) = y) ↔
      (x, y) ∈ (l.getLast hl, l.head hl) :: l.consecutivePairs := by
  classical
  have hlen : l.length = Fintype.card α := by
    rw [← List.toFinset_card_of_nodup hnd,
      Finset.eq_univ_iff_forall.2 fun x => List.mem_toFinset.2 (hmem x), Finset.card_univ]
  have key (n : ℕ) [NeZero n] (hn : l.length = n) (h2 : 2 ≤ n) :
      ∃ τ : Fin n ≃ α, ∀ x y, (∃ t, τ t = x ∧ τ (t + 1) = y) ↔
        (x, y) ∈ (l.getLast hl, l.head hl) :: l.consecutivePairs := by
    subst hn
    exact ⟨hnd.getEquivOfForallMemList l hmem, fun x y => List.cyclicPairs_mem_iff l hl h2⟩
  exact key _ hlen h2

private noncomputable def varAt (p : ℕ)
    (k : Fin (Fintype.card (CorrVar p))) : CorrVar p :=
  (Fintype.equivFin (CorrVar p)).symm k

private theorem varNext_varAt {p : ℕ} [NeZero p] (hp : 1 ≤ p)
    (k : Fin (Fintype.card (CorrVar p))) :
    varNext hp (varAt p k) = varAt p (k + 1) := by
  simp only [varNext, varAt, Equiv.apply_symm_apply]

private def assignVarVal {p : ℕ} (b : Finset (Fin p)) : CorrVar p → Bool
  | .diag i => decide (i ∈ b)
  | .off e => decide (e.fst ∈ b ∧ e.snd ∈ b)

private def clauseOwner {p : ℕ} (b : Finset (Fin p)) (q : CorrPairIdx p × Fin 4) :
    (v : CorrVar p) × Fin (chainSlots p v) :=
  let e := q.1
  let c := q.2
  if h1 : assignVarVal b (.diag e.fst) = clauseLit₁ c then
    ⟨.diag e.fst, ⟨4 * e.snd.1 + c.1, by simp only [chainSlots]; omega⟩⟩
  else if h2 : assignVarVal b (.diag e.snd) = clauseLit₂ c then
    ⟨.diag e.snd, ⟨4 * e.fst.1 + c.1, by simp only [chainSlots]; omega⟩⟩
  else
    ⟨.off e, ⟨c.1, by simp only [chainSlots]; omega⟩⟩

/-- The slot that owns a clause carries that clause, with the value of its variable as the
literal. -/
private theorem slotClause_clauseOwner {p : ℕ} {b : Finset (Fin p)} {q : CorrPairIdx p × Fin 4}
    {v : CorrVar p} {ℓ : Fin (chainSlots p v)} (hq : clauseOwner b q = ⟨v, ℓ⟩) :
    slotClause p v ℓ = some (q, assignVarVal b v) := by
  obtain ⟨e, c⟩ := q
  rw [slotClause_eq_some_iff]
  dsimp only [clauseOwner] at hq
  split_ifs at hq with h1 h2 <;> cases hq
  · exact .inl ⟨rfl, rfl, h1⟩
  · exact .inr (.inl ⟨rfl, rfl, h2⟩)
  · exact .inr (.inr ⟨rfl, rfl, (((forall_clause_iff_eq_and _ _ _).2
      (by simp [assignVarVal]) c).resolve_left h1).resolve_left h2⟩)

private def slotDetour {p : ℕ} (b : Finset (Fin p)) (v : CorrVar p)
    (ℓ : Fin (chainSlots p v)) : List (CorrDigraphV p) :=
  match slotClause p v ℓ with
  | some (q, _) => if clauseOwner b q = ⟨v, ℓ⟩ then [.clause q.1 q.2] else []
  | none => []

private theorem mem_slotDetour_iff {p : ℕ} (b : Finset (Fin p)) (v : CorrVar p)
    (ℓ : Fin (chainSlots p v)) (x : CorrDigraphV p) :
    x ∈ slotDetour b v ℓ ↔
      ∃ q, x = .clause q.1 q.2 ∧ clauseOwner b q = ⟨v, ℓ⟩ := by
  unfold slotDetour
  refine ⟨fun hx => ?_, by rintro ⟨q, rfl, hq⟩; simp [slotClause_clauseOwner hq, hq]⟩
  split at hx
  · split_ifs at hx with ho
    · exact ⟨_, List.mem_singleton.1 hx, ho⟩
    · cases hx
  · cases hx

private def slotVisit {p : ℕ} (_hp : 1 ≤ p) (b : Finset (Fin p)) (v : CorrVar p)
    (ℓ : Fin (chainSlots p v)) : List (CorrDigraphV p) :=
  let k₀ : Fin (chainLen p v) := ⟨3 * ℓ.1, by simp only [chainLen]; omega⟩
  let k₁ : Fin (chainLen p v) := ⟨3 * ℓ.1 + 1, by simp only [chainLen]; omega⟩
  let k₂ : Fin (chainLen p v) := ⟨3 * ℓ.1 + 2, by simp only [chainLen]; omega⟩
  if assignVarVal b v = false then
    [.chain v k₀, .chain v k₁] ++ slotDetour b v ℓ ++ [.chain v k₂]
  else
    [.chain v k₂] ++ slotDetour b v ℓ ++ [.chain v k₁, .chain v k₀]

private theorem slotVisit_ne_nil {p : ℕ} (_hp : 1 ≤ p) (b : Finset (Fin p)) (v : CorrVar p)
    (ℓ : Fin (chainSlots p v)) : slotVisit _hp b v ℓ ≠ [] := by
  unfold slotVisit; split_ifs <;> simp

private def varBlock {p : ℕ} (hp : 1 ≤ p) (b : Finset (Fin p)) (v : CorrVar p) :
    List (CorrDigraphV p) :=
  let kEnd : Fin (chainLen p v) := ⟨3 * chainSlots p v, by simp only [chainLen]; omega⟩
  if assignVarVal b v = false then
    [.gate v] ++ ((List.finRange (chainSlots p v)).flatMap (slotVisit hp b v)) ++ [.chain v kEnd]
  else
    [.gate v, .chain v kEnd] ++
      (((List.finRange (chainSlots p v)).map Fin.rev).flatMap (slotVisit hp b v))

private theorem varBlock_ne_nil {p : ℕ} (hp : 1 ≤ p) (b : Finset (Fin p)) (v : CorrVar p) :
    varBlock hp b v ≠ [] := by unfold varBlock; split_ifs <;> simp

private theorem head_varBlock {p : ℕ} (hp : 1 ≤ p) (b : Finset (Fin p)) (v : CorrVar p) :
    (varBlock hp b v).head (varBlock_ne_nil hp b v) = .gate v := by
  unfold varBlock; split_ifs <;> simp

private theorem List.consecutivePairs_slotVisit_mem {p : ℕ} (hp : 1 ≤ p) (b : Finset (Fin p))
    (v : CorrVar p) (ℓ : Fin (chainSlots p v)) {x y : CorrDigraphV p}
    (hmem : (x, y) ∈ List.consecutivePairs (slotVisit hp b v ℓ)) :
    corrDigraphAdj p hp x y := by
  have hchain {i j : Fin (chainLen p v)} (h : i.1 + 1 = j.1 ∨ j.1 + 1 = i.1) :
      corrDigraphAdj p hp (.chain v i) (.chain v j) := ⟨rfl, h⟩
  -- The clause visited by its owner slot carries the variable's value as its literal.
  have hown {q : CorrPairIdx p × Fin 4} {lit : Bool} (hs : slotClause p v ℓ = some (q, lit))
      (ho : clauseOwner b q = ⟨v, ℓ⟩) : lit = assignVarVal b v :=
    (Prod.mk.inj (Option.some.inj (hs.symm.trans (slotClause_clauseOwner ho)))).2
  -- A visit walks the slot's three chain vertices upwards (value `false`) or downwards (`true`),
  -- detouring through the slot's clause between `3ℓ + 1` and `3ℓ + 2` when the slot owns it.
  dsimp only [slotVisit, slotDetour] at hmem
  cases hval : assignVarVal b v <;> rcases hs : slotClause p v ℓ with _ | ⟨q, lit⟩ <;>
    simp only [hval, hs, Bool.true_eq_false, ↓reduceIte] at hmem <;>
    try split_ifs at hmem with ho
  all_goals
    simp only [List.append_nil, List.cons_append, List.nil_append,
      List.consecutivePairs_cons_cons, List.consecutivePairs_singleton, List.mem_cons,
      Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
    casesm* _ ∨ _ <;> obtain ⟨rfl, rfl⟩ := hmem <;>
    first
      | exact hchain (.inl rfl)
      | exact hchain (.inr rfl)
      | exact ⟨ℓ, lit, hs, .inl ⟨(hown hs ho).trans hval, rfl⟩⟩
      | exact ⟨ℓ, lit, hs, .inr ⟨(hown hs ho).trans hval, rfl⟩⟩

private theorem head_slotVisit {p : ℕ} (_hp : 1 ≤ p) (b : Finset (Fin p)) (v : CorrVar p)
    (ℓ : Fin (chainSlots p v)) :
    (slotVisit _hp b v ℓ).head (slotVisit_ne_nil _hp b v ℓ) =
      if assignVarVal b v = false then ch(v, 3 * ℓ.1) else ch(v, 3 * ℓ.1 + 2) := by
  unfold slotVisit; split_ifs <;> simp

private theorem getLast_slotVisit {p : ℕ} (_hp : 1 ≤ p) (b : Finset (Fin p)) (v : CorrVar p)
    (ℓ : Fin (chainSlots p v)) :
    (slotVisit _hp b v ℓ).getLast (slotVisit_ne_nil _hp b v ℓ) =
      if assignVarVal b v = false then ch(v, 3 * ℓ.1 + 2) else ch(v, 3 * ℓ.1) := by
  unfold slotVisit; split_ifs <;> simp

private theorem getLast_varBlock {p : ℕ} (hp : 1 ≤ p) (b : Finset (Fin p)) (v : CorrVar p) :
    (varBlock hp b v).getLast (varBlock_ne_nil hp b v) =
      if assignVarVal b v = false then ch(v, 3 * chainSlots p v) else ch(v, 0) := by
  have hs := chainSlots_pos hp v
  have hrev : (List.finRange (chainSlots p v)).map Fin.rev ≠ [] := by simp [hs.ne']
  have hsv {L : List (Fin (chainSlots p v))} : ∀ ℓ ∈ L, slotVisit hp b v ℓ ≠ [] :=
    fun ℓ _ => slotVisit_ne_nil hp b v ℓ
  unfold varBlock
  split_ifs with hval
  · simp
  · rw [List.getLast_append_of_ne_nil _ (List.flatMap_ne_nil hrev hsv),
      List.getLast_flatMap hrev hsv, getLast_slotVisit]
    simp [hval, val_getLast_finRange]; omega

private theorem List.consecutivePairs_varBlock_mem {p : ℕ} (hp : 1 ≤ p) (b : Finset (Fin p))
    (v : CorrVar p) {x y : CorrDigraphV p}
    (hmem : (x, y) ∈ List.consecutivePairs (varBlock hp b v)) :
    corrDigraphAdj p hp x y := by
  have hs := chainSlots_pos hp v
  have hfr : List.finRange (chainSlots p v) ≠ [] := mt List.finRange_eq_nil_iff.1 hs.ne'
  have hrev : (List.finRange (chainSlots p v)).map Fin.rev ≠ [] := mt List.map_eq_nil_iff.1 hfr
  have hsv {L : List (Fin (chainSlots p v))} : ∀ ℓ ∈ L, slotVisit hp b v ℓ ≠ [] :=
    fun ℓ _ => slotVisit_ne_nil hp b v ℓ
  -- Inside the slot visits the tour stays in one visit or passes to the next slot of the list.
  have hflat {L : List (Fin (chainSlots p v))} (hL : L ≠ [])
      (hstep : ∀ ℓ₁ ℓ₂, (ℓ₁, ℓ₂) ∈ L.consecutivePairs →
        if assignVarVal b v = false then ℓ₁.1 + 1 = ℓ₂.1 else ℓ₂.1 + 1 = ℓ₁.1)
      (h : (x, y) ∈ (L.flatMap (slotVisit hp b v)).consecutivePairs) :
      corrDigraphAdj p hp x y := by
    rw [List.mem_consecutivePairs_flatMap hL (slotVisit_ne_nil hp b v)] at h
    rcases h with ⟨ℓ, _, hxy⟩ | ⟨⟨ℓ₁, ℓ₂⟩, hadj, rfl, rfl⟩
    · exact List.consecutivePairs_slotVisit_mem hp b v ℓ hxy
    · have := hstep _ _ hadj
      rw [getLast_slotVisit, head_slotVisit]
      split_ifs at this ⊢ <;> exact ⟨rfl, by dsimp only; omega⟩
  unfold varBlock at hmem
  split_ifs at hmem with hval
  · -- gate, slots `0, 1, …` upwards, last chain vertex
    rw [List.append_assoc, List.consecutivePairs_append (List.cons_ne_nil _ _)
        (List.append_ne_nil_of_left_ne_nil (List.flatMap_ne_nil hfr hsv) _),
      List.consecutivePairs_append (List.flatMap_ne_nil hfr hsv) (List.cons_ne_nil _ _)] at hmem
    simp only [List.consecutivePairs_singleton, List.nil_append, List.mem_append, List.mem_cons,
      Prod.mk.injEq, List.not_mem_nil, or_false, List.getLast_singleton,
      List.head_append_of_ne_nil (List.flatMap_ne_nil hfr hsv), List.head_cons] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | h | ⟨rfl, rfl⟩
    · simp [List.head_flatMap hfr hsv, head_slotVisit, hval, corrDigraphAdj, val_head_finRange]
    · exact hflat hfr (fun _ _ h => by
        simpa only [hval, ↓reduceIte] using val_succ_of_mem_consecutivePairs_finRange h) h
    · simp [List.getLast_flatMap hfr hsv, getLast_slotVisit, hval, corrDigraphAdj,
        val_getLast_finRange]
      omega
  · -- gate, last chain vertex, slots downwards
    rw [List.consecutivePairs_append (List.cons_ne_nil _ _) (List.flatMap_ne_nil hrev hsv)] at hmem
    simp only [List.consecutivePairs_cons_cons, List.consecutivePairs_singleton,
      List.nil_append, List.cons_append, List.getLast_cons (List.cons_ne_nil _ _),
      List.getLast_singleton, List.mem_cons, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | h
    · simp [corrDigraphAdj, chainLen]
    · simp [List.head_flatMap hrev hsv, head_slotVisit, hval, corrDigraphAdj, val_head_finRange]
      omega
    · refine hflat hrev (fun ℓ₁ ℓ₂ h => ?_) h
      obtain ⟨i, hi, rfl, rfl⟩ := List.mem_consecutivePairs_iff_exists_getElem.1 h
      simp [hval] at hi ⊢
      omega

private theorem mem_slotVisit_iff {p : ℕ} (_hp : 1 ≤ p) (b : Finset (Fin p)) (v : CorrVar p)
    (ℓ : Fin (chainSlots p v)) (x : CorrDigraphV p) :
    x ∈ slotVisit _hp b v ℓ ↔
      (x = ch(v, 3 * ℓ.1) ∨ x = ch(v, 3 * ℓ.1 + 1) ∨ x = ch(v, 3 * ℓ.1 + 2)) ∨
      ∃ q, x = .clause q.1 q.2 ∧ clauseOwner b q = ⟨v, ℓ⟩ := by
  -- Both orientations list the same vertices, in opposite orders.
  unfold slotVisit
  split_ifs <;> simp [mem_slotDetour_iff] <;> grind

private theorem slotVisit_nodup {p : ℕ} (_hp : 1 ≤ p) (b : Finset (Fin p)) (v : CorrVar p)
    (ℓ : Fin (chainSlots p v)) : (slotVisit _hp b v ℓ).Nodup := by
  unfold slotVisit slotDetour
  rcases slotClause p v ℓ with _ | ⟨_, _⟩ <;> dsimp only <;> split_ifs <;> simp

private theorem slotVisit_disjoint {p : ℕ} (_hp : 1 ≤ p) (b : Finset (Fin p)) (v : CorrVar p)
    {ℓ₁ ℓ₂ : Fin (chainSlots p v)} (hne : ℓ₁ ≠ ℓ₂) :
    List.Disjoint (slotVisit _hp b v ℓ₁) (slotVisit _hp b v ℓ₂) := by
  intro x h₁ h₂
  rw [mem_slotVisit_iff] at h₁ h₂
  rcases h₁ with (rfl | rfl | rfl) | ⟨⟨e₁, c₁⟩, rfl, hq₁⟩ <;>
    rcases h₂ with (h | h | h) | ⟨⟨e₂, c₂⟩, h, hq₂⟩ <;>
    first | exact hne (Fin.ext (by have := chain_inj h; omega)) | cases h
  exact hne (eq_of_heq (Sigma.mk.inj (hq₁.symm.trans hq₂)).2)

private theorem mem_varBlock_iff {p : ℕ} (hp : 1 ≤ p) (b : Finset (Fin p)) (v : CorrVar p)
    (x : CorrDigraphV p) :
    x ∈ varBlock hp b v ↔
      x = .gate v ∨
      (∃ k : Fin (chainLen p v), x = .chain v k) ∨
      (∃ q, x = .clause q.1 q.2 ∧ (clauseOwner b q).1 = v) := by
  have hblock : x ∈ varBlock hp b v ↔
      x = .gate v ∨ x = ch(v, 3 * chainSlots p v) ∨ ∃ ℓ, x ∈ slotVisit hp b v ℓ := by
    have hrev (ℓ : Fin (chainSlots p v)) : ℓ ∈ (List.finRange (chainSlots p v)).map Fin.rev :=
      List.mem_map.2 ⟨ℓ.rev, List.mem_finRange _, Fin.rev_rev ℓ⟩
    unfold varBlock
    split_ifs <;> simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false,
      List.mem_flatMap, List.mem_finRange, true_and, hrev] <;> tauto
  simp only [hblock, mem_slotVisit_iff]
  refine ⟨by rintro (rfl | rfl | ⟨ℓ, (rfl | rfl | rfl) | ⟨q, rfl, hq⟩⟩) <;> simp [*], ?_⟩
  rintro (rfl | ⟨k, rfl⟩ | ⟨q, rfl, rfl⟩)
  · exact .inl rfl
  · by_cases hk : k.1 = 3 * chainSlots p v
    · exact .inr (.inl (congrArg _ (Fin.ext hk)))
    · exact .inr (.inr ⟨⟨k.1 / 3, by have := k.2; simp only [chainLen] at this; omega⟩,
        .inl (by simp only [CorrDigraphV.chain.injEq, heq_eq_eq, true_and, Fin.ext_iff]; omega)⟩)
  · exact .inr (.inr ⟨_, .inr ⟨q, rfl, rfl⟩⟩)

private theorem varBlock_nodup {p : ℕ} (hp : 1 ≤ p) (b : Finset (Fin p)) (v : CorrVar p) :
    (varBlock hp b v).Nodup := by
  have hflat {L : List (Fin (chainSlots p v))} (hL : L.Nodup) :
      (L.flatMap (slotVisit hp b v)).Nodup :=
    List.nodup_flatMap.2 ⟨fun ℓ _ => slotVisit_nodup hp b v ℓ,
      hL.imp fun hne => slotVisit_disjoint hp b v hne⟩
  have hgate (ℓ) : .gate v ∉ slotVisit hp b v ℓ := by simp [mem_slotVisit_iff]
  have hend (ℓ) : ch(v, 3 * chainSlots p v) ∉ slotVisit hp b v ℓ := by
    simp [mem_slotVisit_iff]; omega
  unfold varBlock
  split_ifs
  · simp [List.nodup_append', hflat (List.nodup_finRange _), hgate, hend]
  · simp [hflat ((List.nodup_finRange _).map Fin.rev_injective), hgate, hend]

/-- The block of `v` contains the first chain edge of `v`, traversed upwards when `v` is false and
downwards when `v` is true. -/
private theorem chain_zero_one_infix {p : ℕ} (hp : 1 ≤ p) (b : Finset (Fin p)) (v : CorrVar p) :
    (if assignVarVal b v = false then [ch(v, 0), ch(v, 1)] else [ch(v, 1), ch(v, 0)]) <:+:
      varBlock hp b v := by
  have hs := chainSlots_pos hp v
  unfold varBlock
  split_ifs with hval
  · refine .trans ?_ ((List.infix_of_mem_flatten (List.mem_map_of_mem
      (List.mem_finRange ⟨0, hs⟩))).trans (List.infix_append _ _ _))
    simp only [slotVisit, hval, ↓reduceIte, List.append_assoc]
    exact (List.prefix_append _ _).isInfix
  · refine .trans ?_ ((List.infix_of_mem_flatten (List.mem_map_of_mem (List.mem_map.2
      ⟨Fin.rev ⟨0, hs⟩, List.mem_finRange _, Fin.rev_rev _⟩))).trans
      (List.suffix_append _ _).isInfix)
    simp only [slotVisit, hval, Bool.true_eq_false, ↓reduceIte]
    exact (List.suffix_append _ _).isInfix

section TourBasics

variable {p : ℕ} [NeZero p] {τ : Fin (Fintype.card (CorrDigraphV p)) ≃ CorrDigraphV p}

/-! Successor `τ (τ.symm x + 1)` and predecessor `τ (τ.symm x - 1)` of a vertex `x` on a cyclic
enumeration `τ` of the vertices. -/

private theorem tour_prev_of_next {x y : CorrDigraphV p} (h : τ (τ.symm x + 1) = y) :
    τ (τ.symm y - 1) = x := by
  rw [← h, τ.symm_apply_apply, add_sub_cancel_right, τ.apply_symm_apply]

private theorem tour_next_of_prev {x y : CorrDigraphV p} (h : τ (τ.symm y - 1) = x) :
    τ (τ.symm x + 1) = y := by
  rw [← h, τ.symm_apply_apply, sub_add_cancel, τ.apply_symm_apply]

/-- The predecessor and the successor of a vertex are distinct: there are at least three
vertices. -/
private theorem tour_nb_ne (u : CorrDigraphV p) : τ (τ.symm u - 1) ≠ τ (τ.symm u + 1) := fun h =>
  fin_sub_one_ne_add_one (three_le_card_corrDigraphV NeZero.one_le) _ (τ.injective h)

private theorem tour_exists_iff {x y : CorrDigraphV p} :
    (∃ t, τ t = x ∧ τ (t + 1) = y) ↔ τ (τ.symm x + 1) = y :=
  ⟨by rintro ⟨t, rfl, rfl⟩; rw [τ.symm_apply_apply], fun h => ⟨_, τ.apply_symm_apply x, h⟩⟩

end TourBasics

/-- Every vertex subset `b : Finset (Fin p)` (`1 ≤ p`) determines a satisfying assignment of the
correlation `3`-SAT formula and hence a directed Hamiltonian tour `τ` of `corrDigraphAdj p hp`
whose `chain v 1 → chain v 0` arcs realize `b` on diagonals and `b × b` on off-diagonals
[FioriniMassarPokuttaTiwaryDeWolf2015, Lemma 11, Steps (i)–(ii)]. -/
theorem exists_dirTour_of_assignment {p : ℕ} [NeZero p] (hp : 1 ≤ p) (b : Finset (Fin p)) :
    ∃ τ : Fin (Fintype.card (CorrDigraphV p)) ≃ CorrDigraphV p,
      IsDirTour (corrDigraphAdj p hp) τ ∧
      (∀ i : Fin p,
        (∃ t : Fin (Fintype.card (CorrDigraphV p)),
          τ t = .chain (.diag i) ⟨1, by have := two_le_chainLen hp (.diag i); omega⟩ ∧
          τ (t + 1) = .chain (.diag i) ⟨0, by have := two_le_chainLen hp (.diag i); omega⟩) ↔
          i ∈ b) ∧
      (∀ e : CorrPairIdx p,
        (∃ t : Fin (Fintype.card (CorrDigraphV p)),
          τ t = .chain (.off e) ⟨1, by have := two_le_chainLen hp (.off e); omega⟩ ∧
          τ (t + 1) = .chain (.off e) ⟨0, by have := two_le_chainLen hp (.off e); omega⟩) ↔
          e.fst ∈ b ∧ e.snd ∈ b) := by
  let M := Fintype.card (CorrVar p)
  have hM_pos : 0 < M := Fintype.card_pos
  have hM_ne : List.finRange M ≠ [] := mt List.finRange_eq_nil_iff.1 hM_pos.ne'
  let tourList : List (CorrDigraphV p) :=
    (List.finRange M).flatMap fun k => varBlock hp b (varAt p k)
  have hne (k : Fin M) : varBlock hp b (varAt p k) ≠ [] := varBlock_ne_nil hp b _
  -- Every vertex lies in the block of exactly one variable, so the blocks enumerate the vertices.
  have hblock (v : CorrVar p) : varBlock hp b v <:+: tourList := by
    have h := List.infix_of_mem_flatten (List.mem_map_of_mem
      (f := fun k => varBlock hp b (varAt p k)) (List.mem_finRange (Fintype.equivFin _ v)))
    rwa [show varAt p (Fintype.equivFin _ v) = v from Equiv.symm_apply_apply _ v] at h
  have hown {x : CorrDigraphV p} {v w : CorrVar p} (hv : x ∈ varBlock hp b v)
      (hw : x ∈ varBlock hp b w) : v = w := by
    rw [mem_varBlock_iff] at hv hw
    rcases hv with rfl | ⟨k, rfl⟩ | ⟨⟨e, c⟩, rfl, rfl⟩ <;>
      rcases hw with h | ⟨k', h⟩ | ⟨⟨e', c'⟩, h, rfl⟩ <;> cases h <;> rfl
  have htl_mem (x : CorrDigraphV p) : x ∈ tourList := by
    obtain ⟨v, hv⟩ : ∃ v, x ∈ varBlock hp b v := by cases x <;> simp [mem_varBlock_iff]
    exact (hblock v).subset hv
  have htl_nd : tourList.Nodup := List.nodup_flatMap.2 ⟨fun k _ => varBlock_nodup hp b _,
    (List.nodup_finRange M).imp fun hk x hx₁ hx₂ =>
      hk ((Fintype.equivFin (CorrVar p)).symm.injective (hown hx₁ hx₂))⟩
  have htl_ne : tourList ≠ [] := List.flatMap_ne_nil hM_ne fun k _ => hne k
  obtain ⟨τ, hpair⟩ := exists_tour_of_list htl_nd htl_mem htl_ne (two_le_card_corrDigraphV hp)
  -- Consecutive variable blocks are linked from a chain end to the next gate.
  have hlink (k₁ k₂ : Fin M) (h : (k₁.1 + 1) % M = k₂.1) :
      corrDigraphAdj p hp ((varBlock hp b (varAt p k₁)).getLast (hne k₁))
        ((varBlock hp b (varAt p k₂)).head (hne k₂)) := by
    obtain rfl : k₁ + 1 = k₂ := Fin.ext (by rw [Fin.val_add, Fin.val_one', Nat.add_mod_mod, h])
    rw [getLast_varBlock, head_varBlock, ← varNext_varAt hp]
    split_ifs <;> simp [corrDigraphAdj, chainLen]
  have hstep {x y : CorrDigraphV p} (h : [x, y] <:+: tourList) : τ (τ.symm x + 1) = y :=
    tour_exists_iff.1 ((hpair x y).2 (List.mem_cons_of_mem _
      (consecutivePairs_subset_of_infix h List.mem_cons_self)))
  have h10 (v : CorrVar p) :
      τ (τ.symm ch(v, 1) + 1) = ch(v, 0) ↔ assignVarVal b v = true := by
    have h := (chain_zero_one_infix hp b v).trans (hblock v)
    split_ifs at h with hval
    · exact iff_of_false (fun h' => tour_nb_ne _ ((tour_prev_of_next (hstep h)).trans h'.symm))
        (by simp [hval])
    · exact iff_of_true (hstep h) (by simpa using hval)
  refine ⟨τ, fun t => ?_, fun i => ?_, fun e => ?_⟩
  · have hmem := (hpair _ _).1 ⟨t, rfl, rfl⟩
    rw [List.mem_cons, Prod.mk.injEq, List.mem_consecutivePairs_flatMap hM_ne hne] at hmem
    rcases hmem with ⟨h1, h2⟩ | ⟨k, _, hxy⟩ | ⟨⟨k₁, k₂⟩, hadj, h1, h2⟩
    · rw [h1, h2, List.getLast_flatMap hM_ne fun k _ => hne k,
        List.head_flatMap hM_ne fun k _ => hne k]
      exact hlink _ _ (by
        rw [val_getLast_finRange, val_head_finRange, Nat.sub_add_cancel hM_pos, Nat.mod_self])
    · exact List.consecutivePairs_varBlock_mem hp b _ hxy
    · rw [h1, h2]
      exact hlink _ _ (by
        rw [val_succ_of_mem_consecutivePairs_finRange hadj, Nat.mod_eq_of_lt k₂.2])
  all_goals simp [tour_exists_iff, h10, assignVarVal]

section Tour

variable {p : ℕ} [NeZero p] {hp : 1 ≤ p}
  {τ : Fin (Fintype.card (CorrDigraphV p)) ≃ CorrDigraphV p}

omit [NeZero p] in
/-- An out-neighbor of a gate is one of the two ends of its chain. -/
private theorem corrDigraphAdj_gate_out (hp : 1 ≤ p) {v : CorrVar p} {x : CorrDigraphV p}
    (h : corrDigraphAdj p hp (.gate v) x) {ℓ : ℕ} (hℓ : ℓ + 1 = chainSlots p v) :
    x = ch(v, 0) ∨ x = ch(v, 3 * ℓ + 3) := by
  rcases x with _ | ⟨v', k⟩ | _
  · exact h.elim
  · obtain ⟨rfl, h | h⟩ := h
    · exact .inl (congrArg _ (Fin.ext h))
    · exact .inr (congrArg _ (by fin_index [chainLen]))
  · exact h.elim

omit [NeZero p] in
/-- At an endpoint `k` of the chain of `v` (its first or last vertex) with interior neighbor `k'`,
an in-neighbor is the gate of `v` or `k'`, and an out-neighbor is the next gate or `k'`. -/
private theorem corrDigraphAdj_chainEnd (hp : 1 ≤ p) (v : CorrVar p)
    {k k' : Fin (chainLen p v)} (hk : k.1 = 0 ∨ k.1 + 1 = chainLen p v)
    (hk' : k'.1 + 1 = k.1 ∨ k.1 + 1 = k'.1) (x : CorrDigraphV p) :
    (corrDigraphAdj p hp x (.chain v k) → x = .gate v ∨ x = .chain v k') ∧
      (corrDigraphAdj p hp (.chain v k) x → x = .gate (varNext hp v) ∨ x = .chain v k') := by
  rcases x with v' | ⟨v', j⟩ | ⟨e, c⟩
  · exact ⟨fun h => .inl (congrArg _ h.1), fun h => .inl (congrArg _ h.1)⟩
  · constructor <;> rintro ⟨rfl, h⟩ <;> exact .inr (congrArg _ (Fin.ext (by omega)))
  · simp only [chainLen] at hk
    constructor <;> rintro ⟨ℓ, lit, _, ⟨_, h⟩ | ⟨_, h⟩⟩ <;> omega

omit [NeZero p] in
/-- No clause is attached to an interior chain vertex whose index is a multiple of three: a
neighbor, in either direction, is one of its two chain neighbors. -/
private theorem corrDigraphAdj_mul3 (hp : 1 ≤ p) (v : CorrVar p) {ℓ : ℕ}
    (hℓ : ℓ + 1 < chainSlots p v) {x : CorrDigraphV p}
    (h : corrDigraphAdj p hp ch(v, 3 * ℓ + 3) x ∨ corrDigraphAdj p hp x ch(v, 3 * ℓ + 3)) :
    x = ch(v, 3 * ℓ + 2) ∨ x = ch(v, 3 * ℓ + 4) := by
  rcases x with v' | ⟨v', j⟩ | ⟨e, c⟩
  · rcases h with ⟨_, h⟩ | ⟨rfl, h⟩ <;> fin_index [chainLen]
  · rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;>
      simp only [CorrDigraphV.chain.injEq, heq_eq_eq, true_and, Fin.ext_iff] at h ⊢ <;> omega
  · rcases h with ⟨ℓ', _, _, ⟨_, h⟩ | ⟨_, h⟩⟩ | ⟨ℓ', _, _, ⟨_, h⟩ | ⟨_, h⟩⟩ <;> fin_index

omit [NeZero p] in
/-- A slot vertex `3ℓ + r` (`r ∈ {1, 2}`) leaves to a chain neighbor, or to the clause of its slot
when the slot literal is `false` (`r = 1`) or `true` (`r = 2`). -/
private theorem corrDigraphAdj_slot_out (hp : 1 ≤ p) (v : CorrVar p) {ℓ : ℕ}
    (hℓ : ℓ < chainSlots p v) {r : ℕ} (hr : r = 1 ∨ r = 2) {x : CorrDigraphV p}
    (h : corrDigraphAdj p hp ch(v, 3 * ℓ + r) x) :
    (∃ q, slotClause p v ⟨ℓ, hℓ⟩ = some (q, decide (r = 2))) ∨
      x = ch(v, 3 * ℓ + r - 1) ∨ x = ch(v, 3 * ℓ + r + 1) := by
  rcases x with v' | ⟨v', j⟩ | ⟨e, c⟩
  · obtain ⟨_, h⟩ := h
    fin_index [chainLen]
  · obtain ⟨rfl, h⟩ := h
    simp only [CorrDigraphV.chain.injEq, heq_eq_eq, true_and, Fin.ext_iff] at h ⊢
    omega
  · obtain ⟨ℓ', lit, hs, hk⟩ := h
    obtain rfl : ℓ' = ⟨ℓ, hℓ⟩ := by fin_index
    refine .inl ⟨(e, c), ?_⟩
    rcases hr with rfl | rfl <;> rcases hk with ⟨rfl, hk⟩ | ⟨rfl, hk⟩ <;>
      first | exact hs | fin_index

private theorem tour_pred_adj (hτ : IsDirTour (corrDigraphAdj p hp) τ) (u : CorrDigraphV p) :
    corrDigraphAdj p hp (τ (τ.symm u - 1)) u := by
  simpa only [sub_add_cancel, τ.apply_symm_apply] using hτ (τ.symm u - 1)

private theorem tour_succ_adj (hτ : IsDirTour (corrDigraphAdj p hp) τ) (u : CorrDigraphV p) :
    corrDigraphAdj p hp u (τ (τ.symm u + 1)) := by
  simpa only [τ.apply_symm_apply] using hτ (τ.symm u)

/-- If the tour leaves `g` to `a`, where `a` and `b` are distinct, `a` leaves to `g'` or `aN`, and
`b` is entered from `g` or `bN` and leaves to `g'` or `bN`, then the tour runs
`g → a → aN`, `bN → b → g'`. -/
private theorem tour_gate_branch {g g' a aN b bN : CorrDigraphV p} (hab : a ≠ b)
    (hg : τ (τ.symm g + 1) = a) (ha : τ (τ.symm a + 1) = g' ∨ τ (τ.symm a + 1) = aN)
    (hb : τ (τ.symm b - 1) = g ∨ τ (τ.symm b - 1) = bN)
    (hb' : τ (τ.symm b + 1) = g' ∨ τ (τ.symm b + 1) = bN) :
    τ (τ.symm a + 1) = aN ∧ τ (τ.symm b - 1) = bN := by
  have hbN := hb.resolve_left fun h => hab (hg.symm.trans (tour_next_of_prev h))
  have hbg := hb'.resolve_right fun h => tour_nb_ne b (hbN.trans h.symm)
  exact ⟨ha.resolve_left fun h =>
    hab ((tour_prev_of_next h).symm.trans (tour_prev_of_next hbg)), hbN⟩

/-- The tour runs along the chain of `v` upwards at both ends or downwards at both ends. -/
private theorem tour_ends (hτ : IsDirTour (corrDigraphAdj p hp) τ) (v : CorrVar p) {ℓ : ℕ}
    (hℓ : ℓ + 1 = chainSlots p v) :
    (τ (τ.symm ch(v, 0) + 1) = ch(v, 1) ∧ τ (τ.symm ch(v, 3 * ℓ + 3) - 1) = ch(v, 3 * ℓ + 2)) ∨
    (τ (τ.symm ch(v, 0) - 1) = ch(v, 1) ∧ τ (τ.symm ch(v, 3 * ℓ + 3) + 1) = ch(v, 3 * ℓ + 2)) := by
  have h0 := corrDigraphAdj_chainEnd hp v (k := ⟨0, by chain_lt⟩) (k' := ⟨1, by chain_lt⟩)
    (.inl rfl) (.inr rfl)
  have hL := corrDigraphAdj_chainEnd hp v (k := ⟨3 * ℓ + 3, by chain_lt⟩)
    (k' := ⟨3 * ℓ + 2, by chain_lt⟩) (.inr (by simp only [chainLen]; omega)) (.inl rfl)
  have hne : (ch(v, 0) : CorrDigraphV p) ≠ ch(v, 3 * ℓ + 3) := fun h =>
    absurd (chain_inj h) (by omega)
  rcases corrDigraphAdj_gate_out hp (tour_succ_adj hτ (.gate v)) hℓ with hg | hg
  · exact .inl (tour_gate_branch hne hg ((h0 _).2 (tour_succ_adj hτ _))
      ((hL _).1 (tour_pred_adj hτ _)) ((hL _).2 (tour_succ_adj hτ _)))
  · exact .inr (tour_gate_branch hne.symm hg ((hL _).2 (tour_succ_adj hτ _))
      ((h0 _).1 (tour_pred_adj hτ _)) ((h0 _).2 (tour_succ_adj hτ _))).symm

/-- The tour passes straight through an interior chain vertex whose index is a multiple of
three. -/
private theorem tour_mul3 (hτ : IsDirTour (corrDigraphAdj p hp) τ) (v : CorrVar p) {ℓ : ℕ}
    (hℓ : ℓ + 1 < chainSlots p v) :
    (τ (τ.symm ch(v, 3 * ℓ + 3) - 1) = ch(v, 3 * ℓ + 2) ∧
      τ (τ.symm ch(v, 3 * ℓ + 3) + 1) = ch(v, 3 * ℓ + 4)) ∨
    (τ (τ.symm ch(v, 3 * ℓ + 3) - 1) = ch(v, 3 * ℓ + 4) ∧
      τ (τ.symm ch(v, 3 * ℓ + 3) + 1) = ch(v, 3 * ℓ + 2)) := by
  have hne := tour_nb_ne (τ := τ) ch(v, 3 * ℓ + 3)
  rcases corrDigraphAdj_mul3 hp v hℓ (.inr (tour_pred_adj hτ _)) with h | h <;>
    rcases corrDigraphAdj_mul3 hp v hℓ (.inl (tour_succ_adj hτ _)) with h' | h' <;>
    first | exact .inl ⟨h, h'⟩ | exact .inr ⟨h, h'⟩ | exact absurd (h.trans h'.symm) hne

/-- The two inner vertices of a slot are not both entered from outside the slot: they would
both have to leave to the slot's clause. -/
private theorem tour_no_clash (hτ : IsDirTour (corrDigraphAdj p hp) τ) (v : CorrVar p) {ℓ : ℕ}
    (hℓ : ℓ < chainSlots p v) (h1 : τ (τ.symm ch(v, 3 * ℓ + 1) - 1) = ch(v, 3 * ℓ))
    (h2 : τ (τ.symm ch(v, 3 * ℓ + 2) - 1) = ch(v, 3 * ℓ + 3)) : False := by
  rcases corrDigraphAdj_slot_out hp v hℓ (.inl rfl) (tour_succ_adj hτ _) with ⟨q₁, hs₁⟩ | h | h
  · rcases corrDigraphAdj_slot_out hp v hℓ (.inr rfl) (tour_succ_adj hτ _) with ⟨q₂, hs₂⟩ | h | h
    · cases hs₁.symm.trans hs₂
    · exact absurd (chain_inj (h1.symm.trans (tour_prev_of_next h))) (by omega)
    · exact tour_nb_ne _ (h2.trans h.symm)
  · exact tour_nb_ne _ (h1.trans h.symm)
  · exact absurd (chain_inj (h2.symm.trans (tour_prev_of_next h))) (by omega)

/-- If the tour does not run down the first edge of the chain of `v`, it runs up the first and the
last edge of every slot. -/
private theorem tour_fwd (hτ : IsDirTour (corrDigraphAdj p hp) τ) (v : CorrVar p)
    (hf : τ (τ.symm ch(v, 1) + 1) ≠ ch(v, 0)) : ∀ (ℓ : ℕ) (hℓ : ℓ < chainSlots p v),
    τ (τ.symm ch(v, 3 * ℓ) + 1) = ch(v, 3 * ℓ + 1) ∧
      τ (τ.symm ch(v, 3 * ℓ + 2) + 1) = ch(v, 3 * ℓ + 3) := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_one.2 (chainSlots_pos hp v)
  obtain ⟨h0, hL⟩ := (tour_ends hτ v hm.symm).resolve_right fun h => hf (tour_next_of_prev h.1)
  have step (ℓ : ℕ) (hℓ : ℓ < chainSlots p v)
      (h : τ (τ.symm ch(v, 3 * ℓ) + 1) = ch(v, 3 * ℓ + 1)) :
      τ (τ.symm ch(v, 3 * ℓ + 2) + 1) = ch(v, 3 * ℓ + 3) := by
    by_cases hlast : ℓ = m
    · subst hlast
      exact tour_next_of_prev hL
    · rcases tour_mul3 hτ v (ℓ := ℓ) (by omega) with ⟨h', _⟩ | ⟨_, h'⟩
      · exact tour_next_of_prev h'
      · exact (tour_no_clash hτ v hℓ (tour_prev_of_next h) (tour_prev_of_next h')).elim
  intro ℓ
  induction ℓ with
  | zero => exact fun hℓ => ⟨h0, step 0 hℓ h0⟩
  | succ ℓ ih =>
      intro hℓ
      have h3 : τ (τ.symm ch(v, 3 * ℓ + 3) + 1) = ch(v, 3 * ℓ + 4) := by
        rcases tour_mul3 hτ v hℓ with ⟨_, h⟩ | ⟨h, _⟩
        · exact h
        · exact absurd (chain_inj ((tour_prev_of_next (ih (by omega)).2).symm.trans h)) (by omega)
      exact ⟨h3, step (ℓ + 1) hℓ h3⟩

/-- If the tour runs down the first edge of the chain of `v`, it runs down the last and the first
edge of every slot. -/
private theorem tour_bwd (hτ : IsDirTour (corrDigraphAdj p hp) τ) (v : CorrVar p)
    (hb : τ (τ.symm ch(v, 1) + 1) = ch(v, 0)) : ∀ (ℓ : ℕ) (hℓ : ℓ < chainSlots p v),
    τ (τ.symm ch(v, 3 * ℓ + 3) + 1) = ch(v, 3 * ℓ + 2) ∧
      τ (τ.symm ch(v, 3 * ℓ + 1) + 1) = ch(v, 3 * ℓ) := by
  have step (ℓ : ℕ) (hℓ : ℓ < chainSlots p v)
      (h : τ (τ.symm ch(v, 3 * ℓ + 3) + 1) = ch(v, 3 * ℓ + 2)) :
      τ (τ.symm ch(v, 3 * ℓ + 1) + 1) = ch(v, 3 * ℓ) := by
    rcases ℓ with _ | ℓ
    · exact hb
    · rcases tour_mul3 hτ v hℓ with ⟨_, h'⟩ | ⟨h', _⟩
      · exact (tour_no_clash hτ v hℓ (tour_prev_of_next h') (tour_prev_of_next h)).elim
      · exact tour_next_of_prev h'
  -- Downward induction from the last slot `ℓ + 1 = chainSlots p v`.
  have down (d : ℕ) : ∀ (ℓ : ℕ) (hd : ℓ + d + 1 = chainSlots p v),
      τ (τ.symm ch(v, 3 * ℓ + 3) + 1) = ch(v, 3 * ℓ + 2) := by
    induction d with
    | zero => exact fun ℓ hd => ((tour_ends hτ v hd).resolve_left fun h =>
        tour_nb_ne _ ((tour_prev_of_next h.1).trans hb.symm)).2
    | succ d ih =>
        intro ℓ hd
        rcases tour_mul3 hτ v (ℓ := ℓ) (by omega) with ⟨h, _⟩ | ⟨_, h⟩
        · have h' := tour_prev_of_next (step (ℓ + 1) (by omega) (ih (ℓ + 1) (by omega)))
          exact absurd (chain_inj (h.symm.trans h')) (by omega)
        · exact h
  intro ℓ hℓ
  have h3 := down (chainSlots p v - 1 - ℓ) ℓ (by omega)
  exact ⟨h3, step ℓ hℓ h3⟩

/-- The tour runs down the chain of `C_{ij}` iff it runs down the chains of `C_{ii}` and
`C_{jj}`: the predecessor of each clause vertex is a slot vertex whose literal is the direction
of its chain, so the directions satisfy the four clauses. -/
private theorem tour_off_iff (hτ : IsDirTour (corrDigraphAdj p hp) τ) (e : CorrPairIdx p) :
    τ (τ.symm ch(.off e, 1) + 1) = ch(.off e, 0) ↔
      τ (τ.symm ch(.diag e.fst, 1) + 1) = ch(.diag e.fst, 0) ∧
      τ (τ.symm ch(.diag e.snd, 1) + 1) = ch(.diag e.snd, 0) := by
  have key : decide (τ (τ.symm ch(.off e, 1) + 1) = ch(.off e, 0)) =
      (decide (τ (τ.symm ch(.diag e.fst, 1) + 1) = ch(.diag e.fst, 0)) &&
        decide (τ (τ.symm ch(.diag e.snd, 1) + 1) = ch(.diag e.snd, 0))) := by
    refine (forall_clause_iff_eq_and _ _ _).1 fun c => ?_
    have hcl := tour_pred_adj hτ (.clause e c)
    rcases hu : τ (τ.symm (.clause e c) - 1) with _ | ⟨v, ⟨n, hn⟩⟩ | _ <;> rw [hu] at hcl
    · cases hcl
    · obtain ⟨ℓ, lit, hsc, hk⟩ := hcl
      have hnext := tour_next_of_prev hu
      have hval : decide (τ (τ.symm ch(v, 1) + 1) = ch(v, 0)) = lit := by
        by_cases hb : τ (τ.symm ch(v, 1) + 1) = ch(v, 0) <;>
          rcases hk with ⟨rfl, hk⟩ | ⟨rfl, hk⟩ <;> obtain rfl : n = _ := hk <;>
          simp only [hb, decide_true, decide_false]
        · cases hnext.symm.trans (tour_bwd hτ v hb ℓ.1 ℓ.2).2
        · cases hnext.symm.trans (tour_fwd hτ v hb ℓ.1 ℓ.2).2
      rcases slotClause_eq_some_iff.1 hsc with ⟨rfl, _, rfl⟩ | ⟨rfl, _, rfl⟩ | ⟨rfl, _, rfl⟩
      · exact .inl hval
      · exact .inr (.inl hval)
      · exact .inr (.inr hval)
    · cases hcl
  simpa using Bool.eq_iff_iff.1 key

end Tour

/-- Every directed Hamiltonian tour `τ` of `corrDigraphAdj p hp` induces an assignment
`b : Finset (Fin p)` such that `chain v 1 → chain v 0` occurs in `τ` iff `v` evaluates to `true`
on `b bᵀ` [FioriniMassarPokuttaTiwaryDeWolf2015, Lemma 11, Steps (i)–(ii)]. -/
theorem exists_assignment_of_dirTour {p : ℕ} [NeZero p] (hp : 1 ≤ p)
    {τ : Fin (Fintype.card (CorrDigraphV p)) ≃ CorrDigraphV p}
    (hτ : IsDirTour (corrDigraphAdj p hp) τ) :
    ∃ b : Finset (Fin p),
      (∀ i : Fin p,
        (∃ t : Fin (Fintype.card (CorrDigraphV p)),
          τ t = .chain (.diag i) ⟨1, by have := two_le_chainLen hp (.diag i); omega⟩ ∧
          τ (t + 1) = .chain (.diag i) ⟨0, by have := two_le_chainLen hp (.diag i); omega⟩) ↔
          i ∈ b) ∧
      (∀ e : CorrPairIdx p,
        (∃ t : Fin (Fintype.card (CorrDigraphV p)),
          τ t = .chain (.off e) ⟨1, by have := two_le_chainLen hp (.off e); omega⟩ ∧
          τ (t + 1) = .chain (.off e) ⟨0, by have := two_le_chainLen hp (.off e); omega⟩) ↔
          e.fst ∈ b ∧ e.snd ∈ b) := by
  refine ⟨Finset.univ.filter fun i => τ (τ.symm ch(.diag i, 1) + 1) = ch(.diag i, 0),
    fun i => ?_, fun e => ?_⟩
  · simp only [tour_exists_iff, Finset.mem_filter, Finset.mem_univ, true_and]
  · simp only [tour_exists_iff, Finset.mem_filter, Finset.mem_univ, true_and, tour_off_iff hτ e]
