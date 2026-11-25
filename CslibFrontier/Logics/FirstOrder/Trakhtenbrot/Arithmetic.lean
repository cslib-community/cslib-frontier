/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Raw.Basic
import CslibFrontier.Tactic.FinIndex
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Ring

/-!
# Arithmetic on finite initial segments, axiomatized by raw sentences

The proof of Trakhtenbrot's theorem describes computations inside finite structures, so it needs
arithmetic on a finite initial segment `{0, …, N - 1}` of `ℕ`. On such a segment the successor
and pairing functions are not total, so they are axiomatized as **relations**: symbol `0` is
`<`, symbol `1` is "is zero", symbol `2` is the successor graph `b = a + 1` and symbol `3` is
the graph `Nat.pair a b = p`. The axioms `arithAxioms` say that `<` is a strict linear order,
zero is its least element, the successor graph is its immediate-successor relation, and the
pairing graph satisfies the recursion of the `Nat.pair` enumeration: `(0, 0) ↦ 0`, and if
`(a', b') ↦ p'` then the pair enumerated right after `(a', b')` maps to `p' + 1`. No addition or
multiplication is needed.

**Faithfulness** (`arithModel_faithful`): every finite model of `arithAxioms` is isomorphic to
the standard initial segment `Fin N` with its order, zero, successor graph and `Nat.pair` graph.
The isomorphism is the rank (number of `<`-predecessors). Conversely the standard relations
satisfy the axioms on every `Fin N` (`arithModel_of_std`), so the axioms are consistent with every
finite size.

## Main definitions

* `Cslib.Logic.FO.Trakhtenbrot.arithAxioms`: the arithmetic axioms, as raw sentences.
* `Cslib.Logic.FO.Trakhtenbrot.ArithModel`: their semantic content.
* `Cslib.Logic.FO.Trakhtenbrot.StdArith`: the standard relations on `Fin N`.

## Main results

* `Cslib.Logic.FO.Trakhtenbrot.realize_arithAxioms`: the sentences express `ArithModel`.
* `Cslib.Logic.FO.Trakhtenbrot.arithModel_faithful`: finite models are standard initial segments.
* `Cslib.Logic.FO.Trakhtenbrot.arithModel_of_std`, `arithModel_stdArith`: the standard
  relations are a model.
-/

public section

namespace Cslib.Logic.FO.Trakhtenbrot

open RawFormula

variable {M : Type*}

/-! ### The axioms -/

/-- Relation symbol code for `<` (`[a, b]`). -/
private abbrev ltSym : ℕ := 0

/-- Relation symbol code for "is zero" (`[a]`). -/
private abbrev zeroSym : ℕ := 1

/-- Relation symbol code for the successor graph `b = a + 1` (`[a, b]`). -/
private abbrev succSym : ℕ := 2

/-- Relation symbol code for the pairing graph `Nat.pair a b = p` (`[a, b, p]`). -/
private abbrev pairSym : ℕ := 3

/-- `<` is irreflexive. -/
def axIrrefl : RawFormula := all 0 (neg (rel ltSym [0, 0]))

/-- `<` is transitive. -/
def axTrans : RawFormula :=
  all 0 (all 1 (all 2
    (imp (rel ltSym [0, 1]) (imp (rel ltSym [1, 2]) (rel ltSym [0, 2])))))

/-- `<` is total. -/
def axTotal : RawFormula :=
  all 0 (all 1 (disj (rel ltSym [0, 1]) (disj (equal 0 1) (rel ltSym [1, 0]))))

/-- Zero is the `<`-least element. -/
def axZero : RawFormula := all 0 (iff (rel zeroSym [0]) (all 1 (neg (rel ltSym [1, 0]))))

/-- The successor graph is the immediate-successor relation of `<`. -/
def axSucc : RawFormula :=
  all 0 (all 1 (iff (rel succSym [0, 1])
    (conj (rel ltSym [0, 1]) (all 2 (neg (conj (rel ltSym [0, 2]) (rel ltSym [2, 1])))))))

/-- In variables `a = 0, b = 1, a' = 3, b' = 4`: `(a, b)` is the pair enumerated right after
`(a', b')` by `Nat.pair`. -/
def nextF : RawFormula :=
  disj (conj (rel succSym [3, 0]) (conj (rel ltSym [0, 4]) (equal 1 4)))
    (disj (conj (rel succSym [3, 4]) (conj (equal 0 4) (rel zeroSym [1])))
      (disj (conj (rel ltSym [4, 3]) (conj (equal 0 3) (rel succSym [4, 1])))
        (conj (equal 3 4) (conj (rel zeroSym [0]) (rel succSym [4, 1])))))

/-- The pairing graph is defined by recursion along the `Nat.pair` enumeration. -/
def axPair : RawFormula :=
  all 0 (all 1 (all 2 (iff (rel pairSym [0, 1, 2])
    (disj (conj (rel zeroSym [2]) (conj (rel zeroSym [0]) (rel zeroSym [1])))
      (ex 3 (ex 4 (ex 5
        (conj (rel succSym [5, 2]) (conj (rel pairSym [3, 4, 5]) nextF)))))))))

/-- The arithmetic axioms. -/
def arithAxioms : List RawFormula := [axIrrefl, axTrans, axTotal, axZero, axSucc, axPair]

/-- Semantic version of `nextF`. -/
def NextSem (I : ℕ → List M → Prop) (a' b' a b : M) : Prop :=
  (I succSym [a', a] ∧ I ltSym [a, b'] ∧ b = b') ∨
    (I succSym [a', b'] ∧ a = b' ∧ I zeroSym [b]) ∨
    (I ltSym [b', a'] ∧ a = a' ∧ I succSym [b', b]) ∨
    (a' = b' ∧ I zeroSym [a] ∧ I succSym [b', b])

/-- Semantic content of `arithAxioms`. -/
structure ArithModel (I : ℕ → List M → Prop) : Prop where
  irrefl : ∀ a, ¬I 0 [a, a]
  trans : ∀ a b c, I 0 [a, b] → I 0 [b, c] → I 0 [a, c]
  total : ∀ a b, I 0 [a, b] ∨ a = b ∨ I 0 [b, a]
  zero : ∀ a, I 1 [a] ↔ ∀ b, ¬I 0 [b, a]
  succ : ∀ a b, I 2 [a, b] ↔ I 0 [a, b] ∧ ∀ c, I 0 [a, c] → ¬I 0 [c, b]
  pair : ∀ a b p, I 3 [a, b, p] ↔ (I 1 [p] ∧ I 1 [a] ∧ I 1 [b]) ∨
    ∃ a' b' p', I 2 [p', p] ∧ I 3 [a', b', p'] ∧ NextSem I a' b' a b

/-- `nextF` expresses `NextSem` on variables `a' = 3, b' = 4, a = 0, b = 1`. -/
theorem realize_nextF {I : ℕ → List M → Prop} {v : ℕ → M} :
    nextF.Realize I v ↔ NextSem I (v 3) (v 4) (v 0) (v 1) := by
  simp [nextF, NextSem]

/-- The sentences `arithAxioms` express the `ArithModel` structure. -/
theorem realize_arithAxioms {I : ℕ → List M → Prop} {v : ℕ → M} :
    (∀ φ ∈ arithAxioms, φ.Realize I v) ↔ ArithModel I := by
  suffices (∀ a, ¬I 0 [a, a]) ∧ (∀ a b c, I 0 [a, b] → I 0 [b, c] → I 0 [a, c]) ∧
      (∀ a b, I 0 [a, b] ∨ a = b ∨ I 0 [b, a]) ∧ (∀ a, I 1 [a] ↔ ∀ b, ¬I 0 [b, a]) ∧
      (∀ a b, I 2 [a, b] ↔ I 0 [a, b] ∧ ∀ c, I 0 [a, c] → ¬I 0 [c, b]) ∧
      (∀ a b p, I 3 [a, b, p] ↔ (I 1 [p] ∧ I 1 [a] ∧ I 1 [b]) ∨
        ∃ a' b' p', I 2 [p', p] ∧ I 3 [a', b', p'] ∧ NextSem I a' b' a b) ↔ ArithModel I by
    simpa [arithAxioms, axIrrefl, axTrans, axTotal, axZero, axSucc, axPair, realize_nextF, not_and]
  exact ⟨fun ⟨h1, h2, h3, h4, h5, h6⟩ => ⟨h1, h2, h3, h4, h5, h6⟩,
    fun ⟨h1, h2, h3, h4, h5, h6⟩ => ⟨h1, h2, h3, h4, h5, h6⟩⟩

/-! ### Faithfulness: finite models are standard initial segments -/

/-- The successor of a pair in the `Nat.pair` enumeration. -/
private def NextNat (a' b' a b : ℕ) : Prop :=
  (a = a' + 1 ∧ a < b' ∧ b = b') ∨ (b' = a' + 1 ∧ a = b' ∧ b = 0) ∨
    (b' < a' ∧ a = a' ∧ b = b' + 1) ∨ (a' = b' ∧ a = 0 ∧ b = b' + 1)

private theorem pair_of_nextNat {a' b' a b : ℕ} (h : NextNat a' b' a b) :
    Nat.pair a b = Nat.pair a' b' + 1 := by
  rcases h with ⟨rfl, h1, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨h1, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  all_goals simp only [Nat.pair]; split_ifs <;> first | omega | ring1

private theorem pair_eq_succ_iff {a b q : ℕ} :
    Nat.pair a b = q + 1 ↔ ∃ a' b', Nat.pair a' b' = q ∧ NextNat a' b' a b := by
  refine ⟨fun h => ⟨q.unpair.1, q.unpair.2, Nat.pair_unpair q, ?_⟩,
    fun ⟨_, _, h1, h2⟩ => h1 ▸ pair_of_nextNat h2⟩
  obtain ⟨a0, b0, h0⟩ : ∃ a0 b0, NextNat q.unpair.1 q.unpair.2 a0 b0 :=
    if h1 : q.unpair.1 + 1 < q.unpair.2 then ⟨_, _, Or.inl ⟨rfl, h1, rfl⟩⟩
    else if h2 : q.unpair.2 = q.unpair.1 + 1 then ⟨_, _, Or.inr <| Or.inl ⟨h2, rfl, rfl⟩⟩
    else if h3 : q.unpair.2 < q.unpair.1 then ⟨_, _, Or.inr <| Or.inr <| Or.inl ⟨h3, rfl, rfl⟩⟩
    else ⟨_, _, Or.inr <| Or.inr <| Or.inr ⟨by omega, rfl, rfl⟩⟩
  have h1 := pair_of_nextNat h0
  rw [Nat.pair_unpair, ← h, Nat.pair_eq_pair] at h1
  exact h1.1 ▸ h1.2 ▸ h0

/-- The defining recursion of `axPair`, on numbers below `N`. -/
private theorem pair_eq_iff {N a b p : ℕ} (hp : p < N) :
    Nat.pair a b = p ↔ (p = 0 ∧ a = 0 ∧ b = 0) ∨
      ∃ a' < N, ∃ b' < N, ∃ p' < N, p = p' + 1 ∧ Nat.pair a' b' = p' ∧ NextNat a' b' a b := by
  rcases p with _ | q
  · exact ⟨fun h => Or.inl ⟨rfl, by
        have := Nat.left_le_pair a b
        have := Nat.right_le_pair a b
        omega⟩,
      by rintro (⟨-, rfl, rfl⟩ | ⟨_, _, _, _, _, _, h, -⟩); exacts [rfl, by omega]⟩
  · rw [pair_eq_succ_iff]
    refine ⟨fun ⟨a', b', h1, h2⟩ => Or.inr ⟨a', ?_, b', ?_, q, by omega, rfl, h1, h2⟩, ?_⟩
    · have := Nat.left_le_pair a' b'; omega
    · have := Nat.right_le_pair a' b'; omega
    · rintro (⟨h, -⟩ | ⟨a', -, b', -, p', -, h, h1, h2⟩)
      · omega
      · exact ⟨a', b', by omega, h2⟩

section Faithful

variable {I : ℕ → List M → Prop}

private theorem forall_fin_val {N : ℕ} (e : M ≃ Fin N) {P : ℕ → Prop} :
    (∀ c, P (e c)) ↔ ∀ i < N, P i :=
  ⟨fun h i hi => by simpa using h (e.symm ⟨i, hi⟩), fun h c => h _ (e c).2⟩

private lemma zero_iff_forall_not_lt {N : ℕ} (e : M ≃ Fin N) (a : M) :
    (∀ b, ¬(e b : ℕ) < e a) ↔ (e a : ℕ) = 0 := by
  rw [forall_fin_val e (P := fun i => ¬i < (e a : ℕ))]
  exact ⟨fun H => by_contra fun hne => H 0 (by omega) (by omega), fun H i _ => by omega⟩

private lemma succ_iff_lt_forall {N : ℕ} (e : M ≃ Fin N) (a b : M) :
    ((e a : ℕ) < e b ∧ ∀ c, (e a : ℕ) < e c → ¬(e c : ℕ) < e b) ↔ (e b : ℕ) = e a + 1 := by
  rw [forall_fin_val e (P := fun i => (e a : ℕ) < i → ¬i < e b)]
  exact ⟨fun ⟨hab, H⟩ => by_contra fun hne =>
    H (e a + 1) (by have := (e b).2; omega) (by omega) (by omega),
    fun H => ⟨by omega, fun i _ _ => by omega⟩⟩

private theorem nextSem_iff {N : ℕ} (e : M ≃ Fin N) (hlt : ∀ a b, I 0 [a, b] ↔ (e a : ℕ) < e b)
    (hz : ∀ a, I 1 [a] ↔ (e a : ℕ) = 0) (hs : ∀ a b, I 2 [a, b] ↔ (e b : ℕ) = e a + 1)
    {a' b' a b : M} : NextSem I a' b' a b ↔ NextNat (e a') (e b') (e a) (e b) := by
  have heq : ∀ x y : M, x = y ↔ (e x : ℕ) = e y := fun x y => by
    rw [Fin.val_inj, e.apply_eq_iff_eq]
  simp only [NextSem, NextNat, hlt, hz, hs, heq]

/-- Given a standard order, zero and successor, the pairing axiom forces the standard graph of
`Nat.pair`. -/
theorem pair_faithful (h : ArithModel I) {N : ℕ} (e : M ≃ Fin N)
    (hlt : ∀ a b, I 0 [a, b] ↔ (e a : ℕ) < e b) (hz : ∀ a, I 1 [a] ↔ (e a : ℕ) = 0)
    (hs : ∀ a b, I 2 [a, b] ↔ (e b : ℕ) = e a + 1) :
    ∀ a b p, I 3 [a, b, p] ↔ Nat.pair (e a) (e b) = e p := by
  suffices H : ∀ q a b p, (e p : ℕ) = q → (I 3 [a, b, p] ↔ Nat.pair (e a) (e b) = q)
    from fun a b p => H _ a b p rfl
  intro q
  induction q using Nat.strong_induction_on with | _ q ih =>
  intro a b p hp
  rw [h.pair, pair_eq_iff (hp ▸ (e p).2)]
  simp only [hz, hs, nextSem_iff e hlt hz hs, hp]
  exact ⟨Or.imp_right fun ⟨a', b', p', h1, h2, h3⟩ =>
      ⟨e a', (e a').2, e b', (e b').2, e p', (e p').2, h1, (ih _ (by omega) a' b' p' rfl).1 h2, h3⟩,
    Or.imp_right fun ⟨a', ha', b', hb', p', hp', h1, h2, h3⟩ =>
      ⟨e.symm ⟨a', ha'⟩, e.symm ⟨b', hb'⟩, e.symm ⟨p', hp'⟩, by simpa using h1,
        (ih p' (by omega) _ _ _ (by simp)).2 (by simpa using h2), by simpa using h3⟩⟩

variable [Finite M]

/-- The number of `<`-predecessors. -/
private noncomputable def rank (I : ℕ → List M → Prop) (x : M) : ℕ := {y | I 0 [y, x]}.ncard

private theorem rank_lt_rank (h : ArithModel I) {a b : M} (hab : I 0 [a, b]) :
    rank I a < rank I b :=
  Set.ncard_lt_ncard ⟨fun y hy => h.trans y a b hy hab, fun hsub => h.irrefl a (hsub hab)⟩
    (Set.toFinite _)

private theorem rank_lt_card (h : ArithModel I) (a : M) : rank I a < Nat.card M := by
  rw [← Set.ncard_univ]
  exact Set.ncard_lt_ncard ⟨Set.subset_univ _, fun hsub => h.irrefl a (hsub (Set.mem_univ a))⟩
    (Set.toFinite _)

private theorem lt_iff_rank_lt (h : ArithModel I) {a b : M} : I 0 [a, b] ↔ rank I a < rank I b :=
  ⟨rank_lt_rank h, fun hr => (h.total a b).elim id fun h' => h'.elim
    (fun e => absurd (e ▸ hr) (lt_irrefl _)) (fun hba => absurd (rank_lt_rank h hba) (by omega))⟩

private theorem rank_injective (h : ArithModel I) : Function.Injective (rank I) := fun a b hab =>
  (h.total a b).elim (fun h1 => absurd (rank_lt_rank h h1) (by omega))
    (fun h' => h'.elim id fun h1 => absurd (rank_lt_rank h h1) (by omega))

/-- The rank bijection onto an initial segment. -/
private noncomputable def rankEquiv (h : ArithModel I) : M ≃ Fin (Nat.card M) :=
  Equiv.ofBijective (fun a => ⟨rank I a, rank_lt_card h a⟩) <| by
    have := Fintype.ofFinite M
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨fun a b hab => rank_injective h (congrArg Fin.val hab),
      by simp [Nat.card_eq_fintype_card]⟩

/-- **Faithfulness of the arithmetic axioms.** Every finite model of `arithAxioms` is isomorphic
to a standard initial segment `{0, …, N - 1}` of `ℕ` with its order, zero, successor graph and
`Nat.pair` graph. -/
theorem arithModel_faithful (h : ArithModel I) : ∃ (N : ℕ) (e : M ≃ Fin N),
    (∀ a b, I 0 [a, b] ↔ (e a : ℕ) < e b) ∧ (∀ a, I 1 [a] ↔ (e a : ℕ) = 0) ∧
      (∀ a b, I 2 [a, b] ↔ (e b : ℕ) = e a + 1) ∧
        ∀ a b p, I 3 [a, b, p] ↔ Nat.pair (e a) (e b) = e p := by
  let e := rankEquiv h
  have hlt : ∀ a b, I 0 [a, b] ↔ (e a : ℕ) < e b := fun a b => lt_iff_rank_lt h
  have hz : ∀ a, I 1 [a] ↔ (e a : ℕ) = 0 := fun a => by
    simpa only [h.zero, hlt] using zero_iff_forall_not_lt e a
  have hs : ∀ a b, I 2 [a, b] ↔ (e b : ℕ) = e a + 1 := fun a b => by
    simpa only [h.succ, hlt] using succ_iff_lt_forall e a b
  exact ⟨_, e, hlt, hz, hs, pair_faithful h e hlt hz hs⟩

end Faithful

/-- The standard arithmetic relations on `Fin N`. -/
@[expose] def StdArith (N : ℕ) : ℕ → List (Fin N) → Prop
  | 0, [a, b] => (a : ℕ) < b
  | 1, [a] => (a : ℕ) = 0
  | 2, [a, b] => (b : ℕ) = a + 1
  | 3, [a, b, p] => Nat.pair a b = p
  | _, _ => False

/-- Any interpretation agreeing with the standard relations on symbols `0`–`3` is an
`ArithModel`; in particular the axioms are consistent with every finite size. -/
theorem arithModel_of_std {N : ℕ} {I : ℕ → List (Fin N) → Prop}
    (h0 : ∀ a b : Fin N, I 0 [a, b] ↔ (a : ℕ) < b) (h1 : ∀ a : Fin N, I 1 [a] ↔ (a : ℕ) = 0)
    (h2 : ∀ a b : Fin N, I 2 [a, b] ↔ (b : ℕ) = a + 1)
    (h3 : ∀ a b p : Fin N, I 3 [a, b, p] ↔ Nat.pair a b = p) : ArithModel I := by
  refine ⟨fun a => by simp [h0], fun a b c => by simp only [h0]; omega,
    fun a b => by fin_index [h0],
    fun a => by simpa only [h1, h0, Equiv.refl_apply] using
      (zero_iff_forall_not_lt (Equiv.refl _) a).symm,
    fun a b => by simpa only [h2, h0, Equiv.refl_apply] using
      (succ_iff_lt_forall (Equiv.refl _) a b).symm,
    fun a b p => ?_⟩
  rw [h3, pair_eq_iff p.2]
  simp only [h1, h2, nextSem_iff (Equiv.refl _) h0 h1 h2]
  exact ⟨Or.imp_right fun ⟨a', ha', b', hb', p', hp', h4, h5, h6⟩ =>
      ⟨⟨a', ha'⟩, ⟨b', hb'⟩, ⟨p', hp'⟩, h4, (h3 _ _ _).2 h5, h6⟩,
    Or.imp_right fun ⟨a', b', p', h4, h5, h6⟩ =>
      ⟨a', a'.2, b', b'.2, p', p'.2, h4, (h3 _ _ _).1 h5, h6⟩⟩

/-- The standard arithmetic relations `StdArith N` form an `ArithModel`. -/
theorem arithModel_stdArith (N : ℕ) : ArithModel (StdArith N) :=
  arithModel_of_std (fun _ _ => Iff.rfl) (fun _ => Iff.rfl) (fun _ _ => Iff.rfl)
    (fun _ _ _ => Iff.rfl)

end Cslib.Logic.FO.Trakhtenbrot
