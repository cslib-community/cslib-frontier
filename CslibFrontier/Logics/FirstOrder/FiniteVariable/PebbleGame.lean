/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.FiniteVariable.Basic
import CslibFrontier.Foundations.Data.Set.EqOnUpdate
import CslibFrontier.Foundations.Order.AntitoneSwap

/-!
# Pebble games

The `k`-pebble game on two `L`-structures `M` and `N` is played with `k` pairs of pebbles. In each
round Spoiler picks a pebble index `i`, places the `M`-pebble or the `N`-pebble of pair `i` on an
element of that structure (lifting it first if it was already placed), and Duplicator places the
other pebble of pair `i` in the other structure. Duplicator wins a play when, after every round,
the placed pairs define a partial isomorphism. Unlike the Ehrenfeucht–Fraïssé game, pebbles are
reused, and the game may continue for any number of rounds, even forever.

A position is a set `S : Set (Fin k)` of placed pebble indices together with assignments
`a : Fin k → M` and `b : Fin k → N`; only the values on `S` matter (`pebbleWins_congr`). Moving
pebble `i` to `c` and `d` gives the position `(insert i S, update a i c, update b i d)`. These are
exactly the assignments of the `k`-variable formulas of
`CslibFrontier.Logics.FirstOrder.FiniteVariable.Basic`, whose quantifiers `ex i` and `all i` update
variable `i`.

`PebbleWins L n S a b` says that Duplicator wins the `n`-round game from the position, and
`PebbleWinsForever L S a b` that she wins the game that continues forever, witnessed by a
back-and-forth invariant. `PebbleWins.realize_iff` is the easy direction of the pebble-game
characterization of `FO^k`: a winning position satisfies the same `k`-variable formulas of
quantifier rank at most `n` whose free variables are placed. The converse needs finitely many
relation symbols and is proved in `CslibFrontier.Logics.FirstOrder.FiniteVariable.Hintikka`.

## Main definitions

* `Cslib.Logic.FO.PartialIsoOn`: the pebbles in `S` define a partial isomorphism.
* `Cslib.Logic.FO.PebbleWins`: Duplicator wins the `n`-round `k`-pebble game from a position.
* `Cslib.Logic.FO.IsPebbleBackAndForth`: invariants that Duplicator can maintain forever.
* `Cslib.Logic.FO.PebbleWinsForever`: Duplicator wins the infinite `k`-pebble game.

## Main results

* `Cslib.Logic.FO.PebbleWins.mono`, `Cslib.Logic.FO.PebbleWins.of_subset`,
  `Cslib.Logic.FO.pebbleWins_congr`, `Cslib.Logic.FO.partialIsoOn_comp_equiv_iff`: monotonicity in
  the number of rounds and in the placed pebbles, independence of unplaced pebbles, and pebble
  reindexing.
* `Cslib.Logic.FO.PebbleWins.refl`, `Cslib.Logic.FO.PebbleWins.symm`,
  `Cslib.Logic.FO.PebbleWins.trans`, `FirstOrder.Language.Equiv.pebbleWins`: the
  equivalence-relation laws and invariance under isomorphism.
* `Cslib.Logic.FO.IsPebbleBackAndForth.pebbleWinsForever`: a back-and-forth invariant wins the
  infinite game.
* `Cslib.Logic.FO.PebbleWinsForever.pebbleWins`,
  `Cslib.Logic.FO.pebbleWinsForever_iff_forall_pebbleWins`: the infinite game is won exactly when
  every finite game is, on finite structures.
* `Cslib.Logic.FO.PebbleWins.realize_iff`, `Cslib.Logic.FO.PebbleWinsForever.realize_iff`: the
  easy direction of the pebble-game characterization of `FO^k`.

## References

* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004], Section 11.2, Definition 11.4
  and the remark before Proposition 11.8.
* [N. Immerman, *Descriptive Complexity*][Immerman1999], Definition 6.2.
-/

public section

universe u v w w' w''

open FirstOrder Language Structure

namespace Cslib.Logic.FO

variable {L : Language.{u, v}} {M : Type w} {N : Type w'} {P : Type w''}
  [L.Structure M] [L.Structure N] [L.Structure P] {k : ℕ}

/-! ### Partial isomorphisms on placed pebbles -/

variable (L) in
/-- The pebbles with indices in `S` define a partial isomorphism `a i ↦ b i`: the map is well
defined and injective, and it preserves and reflects every relation among placed pebbles. -/
structure PartialIsoOn (S : Set (Fin k)) (a : Fin k → M) (b : Fin k → N) : Prop where
  /-- Two placed pebbles coincide in `M` exactly when they coincide in `N`. -/
  eq_iff : ∀ i ∈ S, ∀ j ∈ S, a i = a j ↔ b i = b j
  /-- Every relation holds of placed pebbles in `M` exactly when it holds of them in `N`. -/
  relMap_iff : ∀ {l} (R : L.Relations l) (f : Fin l → Fin k), (∀ t, f t ∈ S) →
    (RelMap R (a ∘ f) ↔ RelMap R (b ∘ f))

theorem PartialIsoOn.refl (S : Set (Fin k)) (a : Fin k → M) : PartialIsoOn L S a a :=
  ⟨fun _ _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl⟩

theorem PartialIsoOn.symm {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N}
    (h : PartialIsoOn L S a b) : PartialIsoOn L S b a :=
  ⟨fun i hi j hj => (h.eq_iff i hi j hj).symm, fun R f hf => (h.relMap_iff R f hf).symm⟩

theorem PartialIsoOn.trans {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N} {c : Fin k → P}
    (h₁ : PartialIsoOn L S a b) (h₂ : PartialIsoOn L S b c) : PartialIsoOn L S a c :=
  ⟨fun i hi j hj => (h₁.eq_iff i hi j hj).trans (h₂.eq_iff i hi j hj),
    fun R f hf => (h₁.relMap_iff R f hf).trans (h₂.relMap_iff R f hf)⟩

theorem PartialIsoOn.mono {S T : Set (Fin k)} {a : Fin k → M} {b : Fin k → N} (hST : S ⊆ T)
    (h : PartialIsoOn L T a b) : PartialIsoOn L S a b :=
  ⟨fun i hi j hj => h.eq_iff i (hST hi) j (hST hj),
    fun R f hf => h.relMap_iff R f fun t => hST (hf t)⟩

/-- A partial isomorphism on `S` depends only on the values of the pebbles in `S`. -/
theorem PartialIsoOn.congr {S : Set (Fin k)} {a a' : Fin k → M} {b b' : Fin k → N}
    (ha : Set.EqOn a a' S) (hb : Set.EqOn b b' S) (h : PartialIsoOn L S a b) :
    PartialIsoOn L S a' b' :=
  ⟨fun i hi j hj => ha hi ▸ ha hj ▸ hb hi ▸ hb hj ▸ h.eq_iff i hi j hj, fun R f hf => by
    have haf : a' ∘ f = a ∘ f := funext fun t => (ha (hf t)).symm
    have hbf : b' ∘ f = b ∘ f := funext fun t => (hb (hf t)).symm
    simpa only [haf, hbf] using h.relMap_iff R f hf⟩

/-- With no pebbles placed, every position is a partial isomorphism, provided `L` has no nullary
relation symbols: these are sentences that the two structures would have to agree on. -/
theorem partialIsoOn_empty [IsEmpty (L.Relations 0)] (a : Fin k → M) (b : Fin k → N) :
    PartialIsoOn L ∅ a b :=
  ⟨fun _ hi => absurd hi (Set.notMem_empty _), fun {l} R f hf => by
    cases l with
    | zero => exact isEmptyElim R
    | succ _ => exact absurd (hf 0) (Set.notMem_empty _)⟩

/-- Reindexing pebble names along a bijection preserves partial isomorphisms. -/
theorem partialIsoOn_comp_equiv_iff {k' : ℕ} (σ : Fin k' ≃ Fin k) {S : Set (Fin k)}
    {a : Fin k → M} {b : Fin k → N} :
    PartialIsoOn L (σ ⁻¹' S) (a ∘ σ) (b ∘ σ) ↔ PartialIsoOn L S a b := by
  refine ⟨fun h => ⟨fun i hi j hj => by
      simpa only [Function.comp_apply, σ.apply_symm_apply] using
        h.eq_iff (σ.symm i) (by simpa using hi) (σ.symm j) (by simpa using hj),
    fun R f hf => ?_⟩, fun h => ⟨fun i hi j hj => h.eq_iff (σ i) hi (σ j) hj,
    fun R f hf => h.relMap_iff R (σ ∘ f) fun t => hf t⟩⟩
  simpa [Function.comp_def] using h.relMap_iff R (σ.symm ∘ f) fun t => by simpa using hf t

/-- Updating pebble `i` to an already-placed pebble `a j₀` (`j₀ ∈ S`) preserves `PartialIsoOn`
when paired with `b j₀`. -/
theorem PartialIsoOn.update_of_mem {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N}
    (h : PartialIsoOn L S a b) {i j₀ : Fin k} (hj₀ : j₀ ∈ S) {c : M} (hc : a j₀ = c) :
    PartialIsoOn L (insert i S) (Function.update a i c) (Function.update b i (b j₀)) := by
  let g : Fin k → Fin k := Function.update id i j₀
  have hgS (r : Fin k) (hr : r ∈ insert i S) : g r ∈ S := by
    rcases eq_or_ne r i with rfl | hri <;> simp_all [g]
  have ha : Function.update a i c = a ∘ g := hc ▸ (Function.comp_update a id i j₀).symm
  have hb : Function.update b i (b j₀) = b ∘ g := (Function.comp_update b id i j₀).symm
  rw [ha, hb]
  exact ⟨fun r hr s hs => h.eq_iff (g r) (hgS r hr) (g s) (hgS s hs),
    fun R f hf => h.relMap_iff R (g ∘ f) fun t => hgS (f t) (hf t)⟩

/-- Equality preservation on `insert i S` when updating pebble `i` to fresh elements `c` and `d`
outside `{a j | j ∈ S ∧ j ≠ i}` and `{b j | j ∈ S ∧ j ≠ i}`. -/
theorem PartialIsoOn.update_eq_iff_of_fresh {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N}
    (h : PartialIsoOn L S a b) {i : Fin k} {c : M} {d : N}
    (hc : ∀ j ∈ S, j ≠ i → a j ≠ c) (hd : ∀ j ∈ S, j ≠ i → d ≠ b j)
    {r : Fin k} (hr : r ∈ insert i S) {q : Fin k} (hq : q ∈ insert i S) :
    Function.update a i c r = Function.update a i c q ↔
      Function.update b i d r = Function.update b i d q := by
  by_cases hri : r = i <;> by_cases hqi : q = i
  · simp [hri, hqi]
  · simp only [hri, Function.update_self, Function.update_of_ne hqi]
    exact iff_of_false (fun hca => hc q ((Set.mem_insert_iff.1 hq).resolve_left hqi) hqi hca.symm)
      (hd q ((Set.mem_insert_iff.1 hq).resolve_left hqi) hqi)
  · simp only [hqi, Function.update_self, Function.update_of_ne hri]
    exact iff_of_false (hc r ((Set.mem_insert_iff.1 hr).resolve_left hri) hri)
      fun hbd => hd r ((Set.mem_insert_iff.1 hr).resolve_left hri) hri hbd.symm
  · simp only [Function.update_of_ne hri, Function.update_of_ne hqi]
    exact h.eq_iff r ((Set.mem_insert_iff.1 hr).resolve_left hri)
      q ((Set.mem_insert_iff.1 hq).resolve_left hqi)

/-! ### The game -/

variable (L) in
/-- Duplicator wins the `n`-round `k`-pebble game from the position `(S, a, b)`, where `S` is the
set of placed pebble indices and `a`, `b` give their positions in `M` and `N`: the placed pebbles
define a partial isomorphism and, if a round remains, for every pebble index `i` and every
placement of the `M`-pebble (or `N`-pebble) of pair `i`, Duplicator can place the other pebble of
pair `i` so that she wins the remaining rounds.

The values of `a` and `b` outside `S` do not matter (`pebbleWins_congr`). Since positions are
total assignments `Fin k → M` and `Fin k → N`, a position exists only when `k = 0` or both
structures are nonempty: for `k > 0` and empty `M` or `N` the statement is vacuous, and results
about games starting with no pebbles placed (`S = ∅`) say nothing about empty structures. -/
def PebbleWins : ℕ → Set (Fin k) → (Fin k → M) → (Fin k → N) → Prop
  | 0, S, a, b => PartialIsoOn L S a b
  | n + 1, S, a, b => PartialIsoOn L S a b ∧
      (∀ i (c : M), ∃ d : N,
        PebbleWins n (insert i S) (Function.update a i c) (Function.update b i d)) ∧
      (∀ i (d : N), ∃ c : M,
        PebbleWins n (insert i S) (Function.update a i c) (Function.update b i d))

theorem pebbleWins_zero {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N} :
    PebbleWins L 0 S a b ↔ PartialIsoOn L S a b :=
  Iff.rfl

theorem pebbleWins_succ {n : ℕ} {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N} :
    PebbleWins L (n + 1) S a b ↔ PartialIsoOn L S a b ∧
      (∀ i (c : M), ∃ d : N,
        PebbleWins L n (insert i S) (Function.update a i c) (Function.update b i d)) ∧
      (∀ i (d : N), ∃ c : M,
        PebbleWins L n (insert i S) (Function.update a i c) (Function.update b i d)) :=
  Iff.rfl

theorem PebbleWins.partialIsoOn {n : ℕ} {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N}
    (h : PebbleWins L n S a b) : PartialIsoOn L S a b := by
  rcases n with _ | n
  exacts [h, h.1]

theorem PebbleWins.forth {n : ℕ} {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N}
    (h : PebbleWins L (n + 1) S a b) (i : Fin k) (c : M) :
    ∃ d : N, PebbleWins L n (insert i S) (Function.update a i c) (Function.update b i d) :=
  (pebbleWins_succ.1 h).2.1 i c

theorem PebbleWins.back {n : ℕ} {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N}
    (h : PebbleWins L (n + 1) S a b) (i : Fin k) (d : N) :
    ∃ c : M, PebbleWins L n (insert i S) (Function.update a i c) (Function.update b i d) :=
  (pebbleWins_succ.1 h).2.2 i d

/-! ### Basic properties of the game -/

/-- Winning a game implies winning every shorter game. -/
theorem PebbleWins.mono : ∀ {m n : ℕ} {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N},
    m ≤ n → PebbleWins L n S a b → PebbleWins L m S a b
  | 0, _, _, _, _, _, h => pebbleWins_zero.2 h.partialIsoOn
  | _ + 1, _ + 1, _, _, _, hmn, h => pebbleWins_succ.2 ⟨h.partialIsoOn,
      fun i c => (h.forth i c).imp fun _ hd => hd.mono (by omega),
      fun i d => (h.back i d).imp fun _ hc => hc.mono (by omega)⟩
  | _ + 1, 0, _, _, _, hmn, _ => absurd hmn (by omega)

/-- Lifting placed pebbles keeps the position winning. -/
theorem PebbleWins.of_subset : ∀ {n : ℕ} {S T : Set (Fin k)} {a : Fin k → M} {b : Fin k → N},
    S ⊆ T → PebbleWins L n T a b → PebbleWins L n S a b
  | 0, _, _, _, _, hST, h => pebbleWins_zero.2 (h.partialIsoOn.mono hST)
  | _ + 1, _, _, _, _, hST, h => pebbleWins_succ.2 ⟨h.partialIsoOn.mono hST,
      fun i c => (h.forth i c).imp fun _ hd => hd.of_subset (Set.insert_subset_insert hST),
      fun i d => (h.back i d).imp fun _ hc => hc.of_subset (Set.insert_subset_insert hST)⟩

/-- Winning depends only on the positions of the placed pebbles. -/
theorem pebbleWins_congr : ∀ {n : ℕ} {S : Set (Fin k)} {a a' : Fin k → M} {b b' : Fin k → N},
    Set.EqOn a a' S → Set.EqOn b b' S → PebbleWins L n S a b → PebbleWins L n S a' b'
  | 0, _, _, _, _, _, ha, hb, h => pebbleWins_zero.2 (h.partialIsoOn.congr ha hb)
  | _ + 1, _, _, _, _, _, ha, hb, h => pebbleWins_succ.2 ⟨h.partialIsoOn.congr ha hb,
      fun i c => (h.forth i c).imp fun d hd =>
        pebbleWins_congr (ha.update_insert i c) (hb.update_insert i d) hd,
      fun i d => (h.back i d).imp fun c hc =>
        pebbleWins_congr (ha.update_insert i c) (hb.update_insert i d) hc⟩

theorem PebbleWins.refl :
    ∀ (n : ℕ) (S : Set (Fin k)) (a : Fin k → M), PebbleWins L n S a a
  | 0, S, a => pebbleWins_zero.2 (PartialIsoOn.refl S a)
  | n + 1, S, a => pebbleWins_succ.2 ⟨PartialIsoOn.refl S a,
      fun _ c => ⟨c, PebbleWins.refl n _ _⟩, fun _ d => ⟨d, PebbleWins.refl n _ _⟩⟩

theorem PebbleWins.symm : ∀ {n : ℕ} {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N},
    PebbleWins L n S a b → PebbleWins L n S b a
  | 0, _, _, _, h => pebbleWins_zero.2 h.partialIsoOn.symm
  | _ + 1, _, _, _, h => pebbleWins_succ.2 ⟨h.partialIsoOn.symm,
      fun i d => (h.back i d).imp fun _ hc => hc.symm,
      fun i c => (h.forth i c).imp fun _ hd => hd.symm⟩

theorem PebbleWins.trans :
    ∀ {n : ℕ} {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N} {c : Fin k → P},
      PebbleWins L n S a b → PebbleWins L n S b c → PebbleWins L n S a c
  | 0, _, _, _, _, h₁, h₂ => pebbleWins_zero.2 (h₁.partialIsoOn.trans h₂.partialIsoOn)
  | _ + 1, _, _, _, _, h₁, h₂ => pebbleWins_succ.2 ⟨h₁.partialIsoOn.trans h₂.partialIsoOn,
      fun i x => (h₁.forth i x).elim fun y hy => (h₂.forth i y).imp fun _ => hy.trans,
      fun i z => (h₂.back i z).elim fun y hy => (h₁.back i y).imp fun _ hx => hx.trans hy⟩

/-! ### Back-and-forth invariants and the infinite game -/

variable (L) in
/-- A back-and-forth invariant for the `k`-pebble game: a set of positions, each a partial
isomorphism on its placed pebbles, such that every move of Spoiler from a position in the set has
an answer leading back into the set. -/
structure IsPebbleBackAndForth (I : Set (Fin k) → (Fin k → M) → (Fin k → N) → Prop) : Prop where
  /-- Every position of the invariant is a partial isomorphism on its placed pebbles. -/
  partialIsoOn : ∀ {S a b}, I S a b → PartialIsoOn L S a b
  /-- Every move of Spoiler in `M` has an answer in `N` staying in the invariant. -/
  forth : ∀ {S a b}, I S a b → ∀ i (c : M), ∃ d : N,
    I (insert i S) (Function.update a i c) (Function.update b i d)
  /-- Every move of Spoiler in `N` has an answer in `M` staying in the invariant. -/
  back : ∀ {S a b}, I S a b → ∀ i (d : N), ∃ c : M,
    I (insert i S) (Function.update a i c) (Function.update b i d)

/-- Every position of a back-and-forth invariant is won by Duplicator in every finite game. -/
theorem IsPebbleBackAndForth.pebbleWins {I : Set (Fin k) → (Fin k → M) → (Fin k → N) → Prop}
    (hI : IsPebbleBackAndForth L I) :
    ∀ {n : ℕ} {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N}, I S a b → PebbleWins L n S a b
  | 0, _, _, _, h => pebbleWins_zero.2 (hI.partialIsoOn h)
  | _ + 1, _, _, _, h => pebbleWins_succ.2 ⟨hI.partialIsoOn h,
      fun i c => (hI.forth h i c).imp fun _ hd => hI.pebbleWins hd,
      fun i d => (hI.back h i d).imp fun _ hc => hI.pebbleWins hc⟩

variable (L) in
/-- Duplicator wins the `k`-pebble game that continues forever from the position `(S, a, b)`:
the position belongs to a back-and-forth invariant. As for `PebbleWins`, the statement is vacuous
for `k > 0` when `M` or `N` is empty. -/
def PebbleWinsForever (S : Set (Fin k)) (a : Fin k → M) (b : Fin k → N) : Prop :=
  ∃ I : Set (Fin k) → (Fin k → M) → (Fin k → N) → Prop, IsPebbleBackAndForth L I ∧ I S a b

/-- Unfolds `PebbleWinsForever` into existence of a `k`-pebble back-and-forth invariant. -/
theorem pebbleWinsForever_iff_exists_isPebbleBackAndForth {S : Set (Fin k)} {a : Fin k → M}
    {b : Fin k → N} :
    PebbleWinsForever L S a b ↔
      ∃ I : Set (Fin k) → (Fin k → M) → (Fin k → N) → Prop,
        IsPebbleBackAndForth L I ∧ I S a b :=
  Iff.rfl

/-- Every position of a back-and-forth invariant is won by Duplicator in the infinite game. -/
theorem IsPebbleBackAndForth.pebbleWinsForever
    {I : Set (Fin k) → (Fin k → M) → (Fin k → N) → Prop} (hI : IsPebbleBackAndForth L I)
    {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N} (h : I S a b) :
    PebbleWinsForever L S a b :=
  ⟨I, hI, h⟩

/-- Winning the infinite game implies winning every finite game. -/
theorem PebbleWinsForever.pebbleWins {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N}
    (h : PebbleWinsForever L S a b) (n : ℕ) : PebbleWins L n S a b :=
  let ⟨_, hI, hS⟩ := h
  hI.pebbleWins hS

/-- **The infinite pebble game on finite structures.** On finite structures, Duplicator wins the
`k`-pebble game that continues forever exactly when she wins the `n`-round game for every `n`
[Libkin2004] (remark before Proposition 11.8). On infinite structures only the forward
implication holds in general. -/
theorem pebbleWinsForever_iff_forall_pebbleWins [Finite M] [Finite N] {S : Set (Fin k)}
    {a : Fin k → M} {b : Fin k → N} : PebbleWinsForever L S a b ↔ ∀ n, PebbleWins L n S a b := by
  refine ⟨PebbleWinsForever.pebbleWins, fun h => ⟨fun S a b => ∀ n, PebbleWins L n S a b,
    ⟨fun h => (h 0).partialIsoOn, fun {S a b} h i c => ?_, fun {S a b} h i d => ?_⟩, h⟩⟩
  · exact (Finite.forall_exists_iff_exists_forall_of_antitone fun _ _ _ hmn hd => hd.mono hmn).1
      fun n => (h (n + 1)).forth i c
  · exact (Finite.forall_exists_iff_exists_forall_of_antitone fun _ _ _ hmn hc => hc.mono hmn).1
      fun n => (h (n + 1)).back i d

/-- Duplicator wins the infinite game between a structure and an isomorphic copy, from a position
and its image. -/
theorem _root_.FirstOrder.Language.Equiv.pebbleWinsForever (e : M ≃[L] N) (S : Set (Fin k))
    (a : Fin k → M) : PebbleWinsForever L S a (e ∘ a) := by
  refine ⟨fun _ a b => b = e ∘ a, ⟨?_, fun h i c => ⟨e c, h ▸ (Function.comp_update e _ i c).symm⟩,
    fun h i d => ⟨e.symm d, by rw [h, Function.comp_update, e.apply_symm_apply]⟩⟩, rfl⟩
  rintro S a b rfl
  exact ⟨fun _ _ _ _ => e.injective.eq_iff.symm,
    fun R f _ => by rw [Function.comp_assoc, e.map_rel]⟩

/-- Duplicator wins every finite game between a structure and an isomorphic copy, from a position
and its image. -/
theorem _root_.FirstOrder.Language.Equiv.pebbleWins (e : M ≃[L] N) (n : ℕ) (S : Set (Fin k))
    (a : Fin k → M) : PebbleWins L n S a (e ∘ a) :=
  (e.pebbleWinsForever S a).pebbleWins n

/-! ### The easy direction of the pebble-game characterization of `FO^k` -/

/-- Generic quantifier-rank induction for preserving `GenFormula` truth across a family of
`n`-round game positions `R n S a b`. Base positions must form partial isomorphisms on `S`, and
stepping from `n + 1` to `n` at `i` must preserve each quantifier `q : Q`. -/
theorem FiniteVariable.GenFormula.realize_iff_of_step {Q : Type}
    [FiniteVariable.Quantifier Q M] [FiniteVariable.Quantifier Q N]
    (R : ℕ → Set (Fin k) → (Fin k → M) → (Fin k → N) → Prop)
    (h0 : ∀ {n S a b}, R n S a b → PartialIsoOn L S a b)
    (hquant : ∀ {n S a b} (q : Q) (i : Fin k) (pM : M → Prop) (pN : N → Prop),
      R (n + 1) S a b →
      (∀ {c d}, R n (insert i S) (Function.update a i c) (Function.update b i d) →
        (pM c ↔ pN d)) →
      (FiniteVariable.Quantifier.eval q pM ↔ FiniteVariable.Quantifier.eval q pN))
    {n : ℕ} {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N} (h : R n S a b)
    {φ : FiniteVariable.GenFormula Q L k} (hr : φ.quantifierRank ≤ n) (hS : ↑φ.freeVars ⊆ S) :
    φ.Realize a ↔ φ.Realize b := by
  induction φ generalizing n S a b with
  | falsum => simp only [FiniteVariable.GenFormula.realize_falsum]
  | equal i j =>
    simp only [FiniteVariable.GenFormula.freeVars_equal, Finset.coe_insert, Finset.coe_singleton,
      Set.insert_subset_iff, Set.singleton_subset_iff] at hS
    simp only [FiniteVariable.GenFormula.realize_equal]
    exact (h0 h).eq_iff i hS.1 j hS.2
  | rel R' f =>
    simp only [FiniteVariable.GenFormula.realize_rel]
    exact (h0 h).relMap_iff R' f fun t => hS (by simp)
  | imp φ ψ ihφ ihψ =>
    simp only [FiniteVariable.GenFormula.quantifierRank_imp, max_le_iff] at hr
    simp only [FiniteVariable.GenFormula.freeVars_imp, Finset.coe_union, Set.union_subset_iff] at hS
    simp only [FiniteVariable.GenFormula.realize_imp]
    exact imp_congr (ihφ h hr.1 hS.1) (ihψ h hr.2 hS.2)
  | quant q i φ ih =>
    simp only [FiniteVariable.GenFormula.quantifierRank_quant] at hr
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [FiniteVariable.GenFormula.freeVars_quant, Finset.coe_erase, Set.sdiff_subset_iff,
      ← Set.insert_eq] at hS
    rw [FiniteVariable.GenFormula.realize_quant, FiniteVariable.GenFormula.realize_quant]
    exact hquant q i _ _ h fun hc => ih hc (by omega) hS

/-- **Pebble games, easy direction.** If Duplicator wins the `n`-round `k`-pebble game from
`(S, a, b)`, then `a` and `b` satisfy the same `k`-variable formulas of quantifier rank at most `n`
whose free variables are placed pebbles. No finiteness assumption is needed. -/
theorem PebbleWins.realize_iff {n : ℕ} {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N}
    (h : PebbleWins L n S a b) {φ : FiniteVariable.Formula L k} (hr : φ.quantifierRank ≤ n)
    (hS : ↑φ.freeVars ⊆ S) : φ.Realize a ↔ φ.Realize b :=
  FiniteVariable.GenFormula.realize_iff_of_step (PebbleWins L) PebbleWins.partialIsoOn
    (fun q i _ _ hstep ih => by
      cases q
      simp only [FiniteVariable.ExistentialQuant.eval_ex]
      exact ⟨fun ⟨c, hc⟩ => let ⟨d, hd⟩ := hstep.forth i c; ⟨d, (ih hd).1 hc⟩,
        fun ⟨d, hd⟩ => let ⟨c, hc⟩ := hstep.back i d; ⟨c, (ih hc).2 hd⟩⟩)
    h hr hS

/-- **Infinite pebble games, easy direction.** If Duplicator wins the infinite `k`-pebble game
from `(S, a, b)`, then `a` and `b` satisfy the same `k`-variable formulas whose free variables are
placed pebbles. -/
theorem PebbleWinsForever.realize_iff {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N}
    (h : PebbleWinsForever L S a b) {φ : FiniteVariable.Formula L k} (hS : ↑φ.freeVars ⊆ S) :
    φ.Realize a ↔ φ.Realize b :=
  (h.pebbleWins _).realize_iff le_rfl hS

end Cslib.Logic.FO
