/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.EhrenfeuchtFraisse.Hintikka
public import CslibFrontier.Logics.FirstOrder.FiniteVariable.PebbleGame

/-!
# Pebble games and finite-variable logic

For a language with finitely many relation symbols, the `k`-variable rank-`n` type of a position
`(S, a)` is finite combinatorial data (`Cslib.Logic.FO.PebbleType`): the atomic facts about the
placed pebbles and, if `n > 0`, for each pebble index `i` the set of rank-`(n - 1)` types reached
by moving pebble `i`. Two positions have the same type exactly when Duplicator wins the `n`-round
`k`-pebble game between them (`pebbleType_eq_iff`), and every type is defined by a `k`-variable
Hintikka formula of quantifier rank at most `n` whose free variables are placed
(`realize_pebbleHintikka`, `quantifierRank_pebbleHintikka_le`, `freeVars_pebbleHintikka_subset`).
Together with the easy direction `PebbleWins.realize_iff`, this gives the **pebble-game
characterization of `FO^k`**: Duplicator wins the `n`-round `k`-pebble game from `(S, a, b)`
exactly when `a` and `b` satisfy the same `k`-variable formulas of quantifier rank at most `n` with
free variables in `S` (`pebbleWins_iff_forall_realize_iff`). On finite structures the infinite game
corresponds to all `k`-variable formulas (`pebbleWinsForever_iff_forall_realize_iff`).

The construction follows `CslibFrontier.Logics.FirstOrder.EhrenfeuchtFraisse.Hintikka` and reuses
its atomic formulas `Cslib.Logic.FO.AtomicIndex`. The difference is that a position of the pebble
game has a fixed number of pebbles and a set of placed ones, while a position of the
Ehrenfeucht–Fraïssé game grows by one element per round, so the types and Hintikka formulas are
indexed differently. Every atomic index is a `k`-variable atomic formula
(`AtomicIndex.toFiniteVariable`), and `partialIsoOn_iff_holds` is the placed-pebble form of
`partialIso_iff_holds`.

The hypothesis `[Finite (Σ l, L.Relations l)]` is used only by the Hintikka direction; the
structures are arbitrary, except that the infinite game needs finite structures. As explained at
`PebbleWins`, positions are total assignments, so for `k > 0` these statements say nothing about
empty structures. `DuplicatorWins.pebbleWins`, which passes from the Ehrenfeucht–Fraïssé game to
the pebble game, is a direct game argument and holds in every language.

## Main definitions

* `Cslib.Logic.FO.AtomicIndex.toFiniteVariable`: an atomic index as a `k`-variable formula.
* `Cslib.Logic.FO.pebbleAtoms`: the atomic facts about the placed pebbles.
* `Cslib.Logic.FO.PebbleType`, `Cslib.Logic.FO.pebbleType`: `k`-variable rank-`n` types and the
  type of a position.
* `Cslib.Logic.FO.pebbleAtomicDiagram`, `Cslib.Logic.FO.pebbleHintikka`: the defining formulas of
  atomic types and of `k`-variable rank-`n` types.

## Main results

* `Cslib.Logic.FO.pebbleAtoms_eq_iff`: equal atomic facts are exactly partial isomorphisms on the
  placed pebbles.
* `Cslib.Logic.FO.pebbleType_eq_iff`: equal types are exactly winning positions of the `n`-round
  `k`-pebble game.
* `Cslib.Logic.FO.realize_pebbleHintikka`: the Hintikka formula of a type defines it.
* `Cslib.Logic.FO.pebbleWins_of_forall_realize_iff`: **pebble games, hard direction**.
* `Cslib.Logic.FO.pebbleWins_iff_forall_realize_iff`,
  `Cslib.Logic.FO.pebbleWinsForever_iff_forall_realize_iff`: **the pebble-game characterization of
  `FO^k`**, for finite games and, on finite structures, for the infinite game.
* `Cslib.Logic.FO.DuplicatorWins.pebbleWins`: a winning position of the Ehrenfeucht–Fraïssé game
  wins the pebble game with the same number of rounds, in every language
  (`DuplicatorWins.pebbleWins_comp` reads the position through a reindexing of the pebbles).

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999], Theorem 6.10: the characterization for
  `FO^k` of rank `m`, from a `k`-configuration, over a finite relational vocabulary and arbitrary
  structures, which is the setting here. Its proof uses the finiteness of rank-`m` formulas up to
  equivalence (Exercise 6.11); the Hintikka formulas here make that finiteness explicit.
* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004], Theorem 11.5 and Corollary 11.9,
  stated for `L^k_∞ω` on finite structures; the remark before Proposition 11.8 reduces rank `n` to
  `FO^k`, and Proposition 11.8 gives the infinite game.
-/

public section

universe u v w w'

open FirstOrder Language Structure

namespace Cslib.Logic.FO

variable {L : Language.{u, v}} {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N] {k : ℕ}

/-! ### Atomic types of placed pebbles -/

/-- The `k`-variable atomic formula with index `i`. -/
def AtomicIndex.toFiniteVariable : AtomicIndex L k → FiniteVariable.Formula L k
  | .inl ⟨(i, j)⟩ => .equal i j
  | .inr ⟨⟨_, R⟩, f⟩ => .rel R f

@[simp] theorem AtomicIndex.realize_toFiniteVariable (i : AtomicIndex L k) (a : Fin k → M) :
    i.toFiniteVariable.Realize a ↔ i.Holds a := by
  rcases i with ⟨⟨_, _⟩⟩ | ⟨⟨_, _⟩, _⟩ <;>
    simp only [toFiniteVariable, FiniteVariable.GenFormula.realize_equal,
      FiniteVariable.GenFormula.realize_rel, holds_inl, holds_inr]

@[simp] theorem AtomicIndex.quantifierRank_toFiniteVariable (i : AtomicIndex L k) :
    i.toFiniteVariable.quantifierRank = 0 := by
  rcases i with ⟨⟨_, _⟩⟩ | ⟨⟨_, _⟩, _⟩ <;>
    simp only [toFiniteVariable, FiniteVariable.GenFormula.quantifierRank_equal,
      FiniteVariable.GenFormula.quantifierRank_rel]

/-- The pebbles in `S` define a partial isomorphism exactly when both assignments satisfy the
same atomic formulas whose variables lie in `S`. -/
theorem partialIsoOn_iff_holds {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N} :
    PartialIsoOn L S a b ↔
      ∀ i : AtomicIndex L k, ↑i.toFiniteVariable.freeVars ⊆ S → (i.Holds a ↔ i.Holds b) := by
  constructor
  · rintro ⟨heq, hrel⟩ (⟨⟨i, j⟩⟩ | ⟨⟨_, R⟩, f⟩) hS
    · simp only [AtomicIndex.toFiniteVariable, FiniteVariable.GenFormula.freeVars_equal,
        Finset.coe_insert, Finset.coe_singleton, Set.insert_subset_iff,
        Set.singleton_subset_iff] at hS
      simpa only [AtomicIndex.holds_inl] using heq i hS.1 j hS.2
    · simp only [AtomicIndex.toFiniteVariable, FiniteVariable.GenFormula.freeVars_rel,
        Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.range_subset_iff] at hS
      simpa only [AtomicIndex.holds_inr] using hrel R f hS
  · intro h
    refine ⟨fun i hi j hj => by simpa only [AtomicIndex.holds_inl] using h (.inl ⟨(i, j)⟩) (by
        simp only [AtomicIndex.toFiniteVariable, FiniteVariable.GenFormula.freeVars_equal,
          Finset.coe_insert, Finset.coe_singleton, Set.insert_subset_iff,
          Set.singleton_subset_iff]; exact ⟨hi, hj⟩),
      fun R f hf => by simpa only [AtomicIndex.holds_inr] using h (.inr ⟨⟨_, R⟩, f⟩) (by
        simp only [AtomicIndex.toFiniteVariable, FiniteVariable.GenFormula.freeVars_rel,
          Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.range_subset_iff]; exact hf)⟩

/-- With all pebbles placed, a partial isomorphism on the placed pebbles is a partial isomorphism
in the sense of the Ehrenfeucht–Fraïssé game. -/
theorem partialIsoOn_univ_iff {a : Fin k → M} {b : Fin k → N} :
    PartialIsoOn L Set.univ a b ↔ PartialIso L a b := by
  simp only [partialIsoOn_iff_holds, partialIso_iff_holds, Set.subset_univ, forall_const]

/-- The atomic facts about the pebbles in `S` that hold of `a`: the atomic formulas whose variables
lie in `S` and that `a` satisfies. -/
def pebbleAtoms (S : Set (Fin k)) (a : Fin k → M) : Set (AtomicIndex L k) :=
  {i | ↑i.toFiniteVariable.freeVars ⊆ S ∧ i.Holds a}

@[simp] theorem mem_pebbleAtoms {S : Set (Fin k)} {a : Fin k → M} {i : AtomicIndex L k} :
    i ∈ pebbleAtoms S a ↔ ↑i.toFiniteVariable.freeVars ⊆ S ∧ i.Holds a :=
  Iff.rfl

/-- Two positions have the same atomic facts about the pebbles in `S` exactly when those pebbles
define a partial isomorphism. -/
theorem pebbleAtoms_eq_iff {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N} :
    pebbleAtoms (L := L) S a = pebbleAtoms S b ↔ PartialIsoOn L S a b := by
  simp only [partialIsoOn_iff_holds, Set.ext_iff, mem_pebbleAtoms, and_congr_right_iff]

/-! ### Types of positions -/

variable (L) in
/-- The `k`-variable rank-`n` types, as combinatorial data: a rank-`0` type is a set of atomic
facts, and a rank-`(n + 1)` type is a set of atomic facts together with, for each pebble index
`i`, the set of rank-`n` types reached by moving pebble `i`. The body is exposed: statements about
types use its shape. -/
@[expose] def PebbleType (k : ℕ) : ℕ → Type v
  | 0 => Set (AtomicIndex L k)
  | n + 1 => Set (AtomicIndex L k) × (Fin k → Set (PebbleType k n))

/-- For finitely many relation symbols, there are finitely many `k`-variable rank-`n` types. -/
instance PebbleType.finite [Finite (Σ l, L.Relations l)] (k : ℕ) : ∀ n, Finite (PebbleType L k n)
  | 0 => inferInstanceAs (Finite (Set _))
  | n + 1 =>
    have := PebbleType.finite k n
    inferInstanceAs (Finite (Set _ × (Fin k → Set _)))

/-- The `k`-variable rank-`n` type of the position `(S, a)`: the atomic facts about the placed
pebbles and, for `n + 1`, the types reached by moving each pebble. -/
def pebbleType : ∀ (n : ℕ), Set (Fin k) → (Fin k → M) → PebbleType L k n
  | 0, S, a => pebbleAtoms S a
  | n + 1, S, a => (pebbleAtoms S a,
      fun j => Set.range fun c : M => pebbleType n (insert j S) (Function.update a j c))

theorem pebbleType_zero (S : Set (Fin k)) (a : Fin k → M) :
    pebbleType (L := L) 0 S a = pebbleAtoms S a := by
  rw [pebbleType]

theorem pebbleType_succ {n : ℕ} (S : Set (Fin k)) (a : Fin k → M) :
    pebbleType (L := L) (n + 1) S a = (pebbleAtoms S a,
      fun j => Set.range fun c : M => pebbleType n (insert j S) (Function.update a j c)) := by
  rw [pebbleType]

/-- Equality of rank-`(n + 1)` types is componentwise. -/
theorem PebbleType.succ_ext_iff {n : ℕ} {T T' : PebbleType L k (n + 1)} :
    T = T' ↔ T.1 = T'.1 ∧ ∀ j, T.2 j = T'.2 j :=
  Prod.ext_iff.trans (and_congr Iff.rfl funext_iff)

/-- Two positions have the same `k`-variable rank-`n` type exactly when Duplicator wins the
`n`-round `k`-pebble game between them. -/
theorem pebbleType_eq_iff : ∀ {n : ℕ} {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N},
    pebbleType (L := L) n S a = pebbleType n S b ↔ PebbleWins L n S a b
  | 0, _, _, _ => by rw [pebbleWins_zero]; exact pebbleAtoms_eq_iff
  | n + 1, _, _, _ => by
    rw [pebbleWins_succ, PebbleType.succ_ext_iff, pebbleType_succ, pebbleType_succ,
      pebbleAtoms_eq_iff]
    simp only [Set.Subset.antisymm_iff, Set.range_subset_iff, Set.mem_range, forall_and]
    exact and_congr Iff.rfl (and_congr
      (forall_congr' fun _ => forall_congr' fun _ => exists_congr fun _ =>
        eq_comm.trans pebbleType_eq_iff)
      (forall_congr' fun _ => forall_congr' fun _ => exists_congr fun _ => pebbleType_eq_iff))

/-! ### Hintikka formulas -/

open scoped Classical in
/-- The conjunction of the atomic facts in `T` about the pebbles in `S` and the negations of
those not in `T`. Atomic facts in `T` that mention unplaced pebbles make the formula false. -/
noncomputable def pebbleAtomicDiagram [Finite (Σ l, L.Relations l)] (S : Set (Fin k))
    (T : Set (AtomicIndex L k)) : FiniteVariable.Formula L k :=
  FiniteVariable.GenFormula.iInf fun i : AtomicIndex L k =>
    if ↑i.toFiniteVariable.freeVars ⊆ S then
      (if i ∈ T then i.toFiniteVariable else i.toFiniteVariable.not)
    else (if i ∈ T then ⊥ else ⊤)

theorem realize_pebbleAtomicDiagram [Finite (Σ l, L.Relations l)] (S : Set (Fin k))
    (T : Set (AtomicIndex L k)) (a : Fin k → M) :
    (pebbleAtomicDiagram S T).Realize a ↔ pebbleAtoms S a = T := by
  classical
  simp only [pebbleAtomicDiagram, FiniteVariable.GenFormula.realize_iInf, Set.ext_iff,
    mem_pebbleAtoms]
  refine forall_congr' fun i => ?_
  by_cases hS : ↑i.toFiniteVariable.freeVars ⊆ S <;> by_cases hT : i ∈ T <;> simp [hS, hT]

theorem quantifierRank_pebbleAtomicDiagram [Finite (Σ l, L.Relations l)] (S : Set (Fin k))
    (T : Set (AtomicIndex L k)) : (pebbleAtomicDiagram S T).quantifierRank = 0 := by
  classical
  refine Nat.le_zero.1 (FiniteVariable.GenFormula.quantifierRank_iInf_le fun i => ?_)
  by_cases hS : ↑i.toFiniteVariable.freeVars ⊆ S <;> by_cases hT : i ∈ T <;> simp [hS, hT]

theorem freeVars_pebbleAtomicDiagram_subset [Finite (Σ l, L.Relations l)] (S : Set (Fin k))
    (T : Set (AtomicIndex L k)) : ↑(pebbleAtomicDiagram S T).freeVars ⊆ S := by
  classical
  refine FiniteVariable.GenFormula.freeVars_iInf_subset fun i => ?_
  by_cases hS : ↑i.toFiniteVariable.freeVars ⊆ S <;> by_cases hT : i ∈ T <;> simp [hS, hT]

/-- The `k`-variable Hintikka formula of a rank-`n` type of positions with placed pebbles `S`: a
`k`-variable formula of quantifier rank at most `n` with free variables in `S`, satisfied exactly
by the positions of that type. For `n + 1` it states the atomic diagram and, for each pebble `j`,
that every type in `T.2 j` is reached by moving pebble `j` and that every move of pebble `j`
reaches one of them. -/
noncomputable def pebbleHintikka [Finite (Σ l, L.Relations l)] :
    ∀ {n : ℕ}, Set (Fin k) → PebbleType L k n → FiniteVariable.Formula L k
  | 0, S, T => pebbleAtomicDiagram S T
  | _ + 1, S, T =>
    pebbleAtomicDiagram S T.1 ⊓ FiniteVariable.GenFormula.iInf fun j : Fin k =>
      FiniteVariable.GenFormula.iInf (fun T' : T.2 j => .ex j (pebbleHintikka (insert j S) T'.1)) ⊓
        .all j (FiniteVariable.GenFormula.iSup fun T' : T.2 j => pebbleHintikka (insert j S) T'.1)

theorem realize_pebbleHintikka [Finite (Σ l, L.Relations l)] :
    ∀ {n : ℕ} (S : Set (Fin k)) (T : PebbleType L k n) (a : Fin k → M),
      (pebbleHintikka S T).Realize a ↔ pebbleType n S a = T
  | 0, S, T, a => realize_pebbleAtomicDiagram S T a
  | _ + 1, S, T, a => by
    rw [PebbleType.succ_ext_iff, pebbleType_succ, pebbleHintikka]
    simp only [FiniteVariable.GenFormula.realize_inf, FiniteVariable.GenFormula.realize_iInf,
      FiniteVariable.GenFormula.realize_ex, FiniteVariable.GenFormula.realize_all,
      FiniteVariable.GenFormula.realize_iSup, realize_pebbleHintikka, realize_pebbleAtomicDiagram,
      Subtype.forall, Subtype.exists, exists_prop, exists_eq_right', Set.range_eq_iff, forall_and]
    exact and_congr Iff.rfl and_comm

theorem quantifierRank_pebbleHintikka_le [Finite (Σ l, L.Relations l)] :
    ∀ {n : ℕ} (S : Set (Fin k)) (T : PebbleType L k n), (pebbleHintikka S T).quantifierRank ≤ n
  | 0, S, T => (quantifierRank_pebbleAtomicDiagram S T).le
  | _ + 1, S, T => by
    rw [pebbleHintikka, FiniteVariable.GenFormula.quantifierRank_inf,
      quantifierRank_pebbleAtomicDiagram, max_le_iff]
    refine ⟨Nat.zero_le _, FiniteVariable.GenFormula.quantifierRank_iInf_le fun j => ?_⟩
    rw [FiniteVariable.GenFormula.quantifierRank_inf, max_le_iff,
      FiniteVariable.GenFormula.quantifierRank_all]
    exact ⟨FiniteVariable.GenFormula.quantifierRank_iInf_le fun T' => by
        rw [FiniteVariable.GenFormula.quantifierRank_ex]
        exact Nat.succ_le_succ (quantifierRank_pebbleHintikka_le _ T'.1),
      Nat.succ_le_succ (FiniteVariable.GenFormula.quantifierRank_iSup_le fun T' =>
        quantifierRank_pebbleHintikka_le _ T'.1)⟩

theorem freeVars_pebbleHintikka_subset [Finite (Σ l, L.Relations l)] :
    ∀ {n : ℕ} (S : Set (Fin k)) (T : PebbleType L k n), ↑(pebbleHintikka S T).freeVars ⊆ S
  | 0, S, T => freeVars_pebbleAtomicDiagram_subset S T
  | _ + 1, S, T => by
    rw [pebbleHintikka, FiniteVariable.GenFormula.freeVars_inf, Finset.coe_union,
      Set.union_subset_iff]
    refine ⟨freeVars_pebbleAtomicDiagram_subset S T.1,
      FiniteVariable.GenFormula.freeVars_iInf_subset fun j => ?_⟩
    rw [FiniteVariable.GenFormula.freeVars_inf, Finset.coe_union, Set.union_subset_iff,
      FiniteVariable.GenFormula.freeVars_all, Finset.coe_erase, Set.sdiff_subset_iff,
      ← Set.insert_eq]
    exact ⟨FiniteVariable.GenFormula.freeVars_iInf_subset fun T' => by
        rw [FiniteVariable.GenFormula.freeVars_ex, Finset.coe_erase, Set.sdiff_subset_iff,
          ← Set.insert_eq]
        exact freeVars_pebbleHintikka_subset _ T'.1,
      FiniteVariable.GenFormula.freeVars_iSup_subset fun T' =>
        freeVars_pebbleHintikka_subset _ T'.1⟩

/-! ### The pebble-game characterization of `FO^k` -/

/-- **Pebble games, hard direction.** For a language with finitely many relation symbols, if `a`
and `b` satisfy the same `k`-variable formulas of quantifier rank at most `n` with free variables
in `S`, then Duplicator wins the `n`-round `k`-pebble game from `(S, a, b)`. Only the Hintikka
formula of the type of `(S, a)` is used. -/
theorem pebbleWins_of_forall_realize_iff [Finite (Σ l, L.Relations l)] {n : ℕ}
    {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N}
    (h : ∀ φ : FiniteVariable.Formula L k, φ.quantifierRank ≤ n → ↑φ.freeVars ⊆ S →
      (φ.Realize a ↔ φ.Realize b)) : PebbleWins L n S a b := by
  rw [← pebbleType_eq_iff]
  have hb := (h _ (quantifierRank_pebbleHintikka_le S (pebbleType (L := L) n S a))
    (freeVars_pebbleHintikka_subset S _)).1 ((realize_pebbleHintikka S _ a).2 rfl)
  exact ((realize_pebbleHintikka S _ b).1 hb).symm

/-- **The pebble-game characterization of `FO^k`** ([Immerman1999], Theorem 6.10; [Libkin2004],
Theorem 11.5 and Corollary 11.9 with the remark before Proposition 11.8). For a language with
finitely many relation symbols, Duplicator wins the `n`-round `k`-pebble game from `(S, a, b)`
exactly when `a` and `b` satisfy the same `k`-variable formulas of quantifier rank at most `n` with
free variables in `S`. -/
theorem pebbleWins_iff_forall_realize_iff [Finite (Σ l, L.Relations l)] {n : ℕ}
    {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N} :
    PebbleWins L n S a b ↔ ∀ φ : FiniteVariable.Formula L k, φ.quantifierRank ≤ n →
      ↑φ.freeVars ⊆ S → (φ.Realize a ↔ φ.Realize b) :=
  ⟨fun h _ hr hS => h.realize_iff hr hS, pebbleWins_of_forall_realize_iff⟩

/-- **The infinite pebble game and `FO^k`** ([Libkin2004], Theorem 11.5(b), Proposition 11.8 and
Corollary 11.9). For a language with finitely many relation symbols and finite structures,
Duplicator wins the infinite `k`-pebble game from `(S, a, b)` exactly when `a` and `b` satisfy the
same `k`-variable formulas with free variables in `S`. -/
theorem pebbleWinsForever_iff_forall_realize_iff [Finite (Σ l, L.Relations l)] [Finite M]
    [Finite N] {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N} :
    PebbleWinsForever L S a b ↔ ∀ φ : FiniteVariable.Formula L k, ↑φ.freeVars ⊆ S →
      (φ.Realize a ↔ φ.Realize b) := by
  rw [pebbleWinsForever_iff_forall_pebbleWins]
  exact ⟨fun h _ hS => (h _).realize_iff le_rfl hS,
    fun h _ => pebbleWins_of_forall_realize_iff fun φ _ hS => h φ hS⟩

/-! ### From the Ehrenfeucht–Fraïssé game to the pebble game -/

/-- A partial isomorphism between `m`-tuples, read through a reindexing `σ : Fin k → Fin m` of the
pebbles, is a partial isomorphism on every set of placed pebbles. -/
theorem PartialIso.partialIsoOn_comp {m : ℕ} {a : Fin m → M} {b : Fin m → N}
    (h : PartialIso L a b) (σ : Fin k → Fin m) (S : Set (Fin k)) :
    PartialIsoOn L S (a ∘ σ) (b ∘ σ) :=
  ⟨fun i _ j _ => h.eq_iff (σ i) (σ j), fun R f _ => h.relMap_iff R (σ ∘ f)⟩

/-- Moving pebble `i` to the new element `c` of an Ehrenfeucht–Fraïssé position read through `σ`
is the extended position read through `σ` with `i` sent to the new index. -/
private theorem snoc_comp_update {m : ℕ} (σ : Fin k → Fin m) (i : Fin k) {α : Type*}
    (x : Fin m → α) (c : α) :
    (Fin.snoc x c : Fin (m + 1) → α) ∘ Function.update (Fin.castSucc ∘ σ) i (Fin.last m) =
      Function.update (x ∘ σ) i c := by
  funext j
  by_cases hj : j = i <;> simp [hj, Function.update_of_ne]

/-- A winning position `(a, b)` of the `n`-round Ehrenfeucht–Fraïssé game, read through any
reindexing `σ : Fin k → Fin m`, wins the `n`-round `k`-pebble game from `(S, a ∘ σ, b ∘ σ)`. When
pebble `i` moves, `σ` is extended by sending `i` to the element added in the Ehrenfeucht–Fraïssé
game. -/
theorem DuplicatorWins.pebbleWins_comp :
    ∀ {n m : ℕ} {a : Fin m → M} {b : Fin m → N}, DuplicatorWins L n a b →
      ∀ (σ : Fin k → Fin m) (S : Set (Fin k)), PebbleWins L n S (a ∘ σ) (b ∘ σ)
  | 0, _, _, _, h, σ, S => pebbleWins_zero.2 (h.partialIso.partialIsoOn_comp σ S)
  | _ + 1, m, _, _, h, σ, S => pebbleWins_succ.2 ⟨h.partialIso.partialIsoOn_comp σ S,
      fun i c => let ⟨d, hd⟩ := h.forth c; ⟨d, by
        simpa only [snoc_comp_update] using
          hd.pebbleWins_comp (Function.update (Fin.castSucc ∘ σ) i (Fin.last m)) (insert i S)⟩,
      fun i d => let ⟨c, hc⟩ := h.back d; ⟨c, by
        simpa only [snoc_comp_update] using
          hc.pebbleWins_comp (Function.update (Fin.castSucc ∘ σ) i (Fin.last m)) (insert i S)⟩⟩

/-- A winning position of the `n`-round Ehrenfeucht–Fraïssé game from `(a, b)` wins the `n`-round
`k`-pebble game from `(S, a, b)` for every set `S` of placed pebbles, in every language. -/
theorem DuplicatorWins.pebbleWins {n : ℕ} {a : Fin k → M} {b : Fin k → N}
    (h : DuplicatorWins L n a b) (S : Set (Fin k)) : PebbleWins L n S a b :=
  h.pebbleWins_comp id S

end Cslib.Logic.FO
