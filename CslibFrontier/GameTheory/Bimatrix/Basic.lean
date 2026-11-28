/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.MixedStrategy
public import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.Finite.Range
import Mathlib.Tactic.Linarith

/-!
# Bimatrix games

A *bimatrix game* (`Cslib.GameTheory.BimatrixGame`) is a finite two-player game in strategic form,
given by two payoff matrices `A B : Matrix M N ℝ`: if player 1 plays the row `i` and player 2 the
column `j`, they receive `A i j` and `B i j`, which they maximize. A *mixed strategy* is a
probability vector (`Cslib.GameTheory.IsMixedStrategy`, in
`CslibFrontier.GameTheory.MixedStrategy`), and the expected payoffs of mixed strategies `x` and `y`
are `xᵀ A y` and `xᵀ B y`. A pair `(x, y)` is a (mixed) *Nash equilibrium* (`BimatrixGame.IsNash`)
if each strategy is a best response to the other. We follow the conventions of [vonStengel2007],
Section 3.2.

## Main definitions

* `Cslib.GameTheory.BimatrixGame`: a bimatrix game, with expected payoffs `payoff₁` and `payoff₂`.
* `BimatrixGame.swap`: the game with the roles of the two players exchanged (`⟨Bᵀ, Aᵀ⟩`).
* `BimatrixGame.IsBestResponse₁`, `BimatrixGame.IsBestResponse₂`: mixed best responses.
* `BimatrixGame.IsPureBestResponse₁`, `BimatrixGame.IsPureBestResponse₂`: pure best responses.
* `BimatrixGame.IsNash`: a mixed Nash equilibrium.
* `BimatrixGame.IsNondegenerate`: no mixed strategy with support of size `k` has more than `k`
  pure best responses ([vonStengel2007], Definition 3.2).
* `BimatrixGame.addConst`: the game with a constant added to all payoffs.

## Main results

* `BimatrixGame.isBestResponse₁_iff`, `BimatrixGame.isBestResponse₂_iff`: the *best response
  condition*, a mixed strategy is a best response iff every pure strategy in its support is a pure
  best response ([vonStengel2007], Proposition 3.1).
* `BimatrixGame.IsNash.ncard_support_eq`: in a Nash equilibrium of a nondegenerate game both
  strategies have supports of the same size ([vonStengel2007], Proposition 3.3).
* `BimatrixGame.isNash_addConst`, `BimatrixGame.isNondegenerate_addConst`: adding a constant to
  all payoffs changes neither the Nash equilibria nor nondegeneracy, and
  `BimatrixGame.exists_addConst_pos` makes all payoffs positive.

## References

* [B. von Stengel, *Equilibrium computation for two-player games in strategic and extensive
  form*][vonStengel2007]
-/

public section

open Finset Matrix

namespace Cslib.GameTheory

/-- A *bimatrix game*: a finite two-player game in strategic form. Player 1 chooses a row `i : M`,
player 2 a column `j : N`, and they receive the payoffs `A i j` and `B i j`, which they
maximize. -/
structure BimatrixGame (M N : Type*) where
  /-- The payoff matrix of player 1, the row player. -/
  A : Matrix M N ℝ
  /-- The payoff matrix of player 2, the column player. -/
  B : Matrix M N ℝ

namespace BimatrixGame

section SwapBasic

variable {M N : Type*} (G : BimatrixGame M N)

/-- The game with the roles of the two players exchanged: player 1's payoff matrix becomes `Bᵀ` and
player 2's becomes `Aᵀ`. -/
def swap : BimatrixGame N M :=
  ⟨G.Bᵀ, G.Aᵀ⟩

@[simp] theorem swap_mk (A B : Matrix M N ℝ) :
    ({ A := A, B := B } : BimatrixGame M N).swap = { A := Bᵀ, B := Aᵀ } := by
  rw [swap]

@[simp] theorem swap_A : G.swap.A = G.Bᵀ := by
  rw [swap]

@[simp] theorem swap_B : G.swap.B = G.Aᵀ := by
  rw [swap]

@[simp] theorem swap_swap : G.swap.swap = G := by
  cases G
  simp only [swap, transpose_transpose]

end SwapBasic

variable {M N : Type*} [Fintype M] [Fintype N] (G : BimatrixGame M N)

/-- The expected payoff `xᵀ A y` of player 1. -/
def payoff₁ (x : M → ℝ) (y : N → ℝ) : ℝ := x ⬝ᵥ (G.A *ᵥ y)

/-- The expected payoff `xᵀ B y` of player 2. -/
def payoff₂ (x : M → ℝ) (y : N → ℝ) : ℝ := x ⬝ᵥ (G.B *ᵥ y)

/-- `x` is a *best response* of player 1 to `y`: a mixed strategy maximizing `payoff₁ · y` over all
mixed strategies. -/
def IsBestResponse₁ (x : M → ℝ) (y : N → ℝ) : Prop :=
  IsMixedStrategy x ∧ ∀ x', IsMixedStrategy x' → G.payoff₁ x' y ≤ G.payoff₁ x y

/-- `y` is a *best response* of player 2 to `x`: a mixed strategy maximizing `payoff₂ x ·` over all
mixed strategies. -/
def IsBestResponse₂ (y : N → ℝ) (x : M → ℝ) : Prop :=
  IsMixedStrategy y ∧ ∀ y', IsMixedStrategy y' → G.payoff₂ x y' ≤ G.payoff₂ x y

/-- `(x, y)` is a (mixed) *Nash equilibrium*: each strategy is a best response to the other. -/
def IsNash (x : M → ℝ) (y : N → ℝ) : Prop :=
  G.IsBestResponse₁ x y ∧ G.IsBestResponse₂ y x

/-- The row `i` is a *pure best response* of player 1 to `y`: it maximizes the expected payoff
`(A *ᵥ y) i`. -/
def IsPureBestResponse₁ (y : N → ℝ) (i : M) : Prop :=
  ∀ i', (G.A *ᵥ y) i' ≤ (G.A *ᵥ y) i

/-- The column `j` is a *pure best response* of player 2 to `x`: it maximizes the expected payoff
`(x ᵥ* B) j`. -/
def IsPureBestResponse₂ (x : M → ℝ) (j : N) : Prop :=
  ∀ j', (x ᵥ* G.B) j' ≤ (x ᵥ* G.B) j

/-- A bimatrix game is *nondegenerate* if no mixed strategy with support of size `k` has more than
`k` pure best responses ([vonStengel2007], Definition 3.2). -/
def IsNondegenerate : Prop :=
  (∀ x, IsMixedStrategy x → {j | G.IsPureBestResponse₂ x j}.ncard ≤ (Function.support x).ncard) ∧
    ∀ y, IsMixedStrategy y → {i | G.IsPureBestResponse₁ y i}.ncard ≤ (Function.support y).ncard

variable {G} {x : M → ℝ} {y : N → ℝ}

/-- Express player 1's expected payoff as the dot product `x ⬝ᵥ (G.A *ᵥ y)`. -/
theorem payoff₁_eq_dotProduct (x : M → ℝ) (y : N → ℝ) : G.payoff₁ x y = x ⬝ᵥ (G.A *ᵥ y) := by
  rw [payoff₁]

/-- Express player 2's expected payoff as the dot product `y ⬝ᵥ (x ᵥ* G.B)`. -/
theorem payoff₂_eq_dotProduct (x : M → ℝ) (y : N → ℝ) : G.payoff₂ x y = y ⬝ᵥ (x ᵥ* G.B) := by
  rw [payoff₂, dotProduct_mulVec, dotProduct_comm]

@[simp]
theorem payoff₁_swap (G : BimatrixGame M N) (y : N → ℝ) (x : M → ℝ) :
    G.swap.payoff₁ y x = G.payoff₂ x y := by
  rw [payoff₁, swap_A, mulVec_transpose, payoff₂_eq_dotProduct]

@[simp]
theorem payoff₂_swap (G : BimatrixGame M N) (y : N → ℝ) (x : M → ℝ) :
    G.swap.payoff₂ y x = G.payoff₁ x y := by
  rw [← payoff₁_swap, swap_swap]

/-- Unfolding characterization of `IsNash`: each player plays a best response to the other. -/
theorem isNash_iff : G.IsNash x y ↔ G.IsBestResponse₁ x y ∧ G.IsBestResponse₂ y x := Iff.rfl

omit [Fintype M] in
/-- Unfolding characterization of a pure best response for player 1. -/
theorem isPureBestResponse₁_iff {i : M} :
    G.IsPureBestResponse₁ y i ↔ ∀ i', (G.A *ᵥ y) i' ≤ (G.A *ᵥ y) i := Iff.rfl

omit [Fintype N] in
/-- Unfolding characterization of a pure best response for player 2. -/
theorem isPureBestResponse₂_iff {j : N} :
    G.IsPureBestResponse₂ x j ↔ ∀ j', (x ᵥ* G.B) j' ≤ (x ᵥ* G.B) j := Iff.rfl

omit [Fintype N] in
@[simp]
theorem isPureBestResponse₁_swap {j : N} :
    G.swap.IsPureBestResponse₁ x j ↔ G.IsPureBestResponse₂ x j := by
  simp only [IsPureBestResponse₁, IsPureBestResponse₂, swap_A, mulVec_transpose]

omit [Fintype M] in
@[simp]
theorem isPureBestResponse₂_swap {i : M} :
    G.swap.IsPureBestResponse₂ y i ↔ G.IsPureBestResponse₁ y i := by
  rw [← isPureBestResponse₁_swap, swap_swap]

@[simp]
theorem isBestResponse₁_swap : G.swap.IsBestResponse₁ y x ↔ G.IsBestResponse₂ y x := by
  simp only [IsBestResponse₁, IsBestResponse₂, payoff₁_swap]

@[simp]
theorem isBestResponse₂_swap : G.swap.IsBestResponse₂ x y ↔ G.IsBestResponse₁ x y := by
  rw [← isBestResponse₁_swap, swap_swap]

/-- Swapping the players swaps the coordinates of a Nash equilibrium. -/
@[simp]
theorem isNash_swap : G.swap.IsNash y x ↔ G.IsNash x y := by
  simp only [IsNash, isBestResponse₁_swap, isBestResponse₂_swap, and_comm]

/-- Unfolding characterization of nondegeneracy in terms of support and pure best-response
cardinalities. -/
theorem isNondegenerate_iff : G.IsNondegenerate ↔
    (∀ x, IsMixedStrategy x → {j | G.IsPureBestResponse₂ x j}.ncard ≤ (Function.support x).ncard) ∧
      ∀ y, IsMixedStrategy y → {i | G.IsPureBestResponse₁ y i}.ncard ≤ (Function.support y).ncard :=
  Iff.rfl

/-- Swapping the players preserves nondegeneracy. -/
@[simp]
theorem isNondegenerate_swap : G.swap.IsNondegenerate ↔ G.IsNondegenerate := by
  simp only [IsNondegenerate, isPureBestResponse₁_swap, isPureBestResponse₂_swap, and_comm]

/-- A best response of player 1 is a mixed strategy. -/
theorem IsBestResponse₁.isMixedStrategy (h : G.IsBestResponse₁ x y) : IsMixedStrategy x := h.1

/-- A best response of player 2 is a mixed strategy. -/
theorem IsBestResponse₂.isMixedStrategy (h : G.IsBestResponse₂ y x) : IsMixedStrategy y := h.1

/-- **Best response condition** for player 1 ([vonStengel2007], Proposition 3.1): a mixed strategy
is a best response iff every row it plays with positive probability is a pure best response. -/
theorem isBestResponse₁_iff :
    G.IsBestResponse₁ x y ↔ IsMixedStrategy x ∧ ∀ i, 0 < x i → G.IsPureBestResponse₁ y i :=
  ⟨fun h => ⟨h.1, h.1.forall_dotProduct_le_iff.1 h.2⟩,
    fun h => ⟨h.1, h.1.forall_dotProduct_le_iff.2 h.2⟩⟩

/-- **Best response condition** for player 2 ([vonStengel2007], Proposition 3.1). -/
theorem isBestResponse₂_iff :
    G.IsBestResponse₂ y x ↔ IsMixedStrategy y ∧ ∀ j, 0 < y j → G.IsPureBestResponse₂ x j := by
  rw [← isBestResponse₁_swap, isBestResponse₁_iff]
  simp only [isPureBestResponse₁_swap]

/-- Against `y`, a best response earns the payoff of each row in its support. -/
theorem IsBestResponse₁.payoff₁_eq_of_pos (h : G.IsBestResponse₁ x y) {i : M} (hi : 0 < x i) :
    G.payoff₁ x y = (G.A *ᵥ y) i :=
  h.1.dotProduct_eq_of_forall_pos fun i' hi' =>
    le_antisymm ((isBestResponse₁_iff.1 h).2 i hi i') ((isBestResponse₁_iff.1 h).2 i' hi' i)

/-- Against `y`, a best response earns at least the payoff of every row. -/
theorem IsBestResponse₁.le_payoff₁ (h : G.IsBestResponse₁ x y) (i : M) :
    (G.A *ᵥ y) i ≤ G.payoff₁ x y := by
  classical
  have := h.2 _ (isMixedStrategy_single i)
  rwa [payoff₁, single_dotProduct, one_mul] at this

/-- Against `x`, a best response earns the payoff of each column in its support. -/
theorem IsBestResponse₂.payoff₂_eq_of_pos (h : G.IsBestResponse₂ y x) {j : N} (hj : 0 < y j) :
    G.payoff₂ x y = (x ᵥ* G.B) j := by
  simpa only [payoff₁_swap, swap_A, mulVec_transpose] using
    (isBestResponse₁_swap.2 h).payoff₁_eq_of_pos hj

/-- Against `x`, a best response earns at least the payoff of every column. -/
theorem IsBestResponse₂.le_payoff₂ (h : G.IsBestResponse₂ y x) (j : N) :
    (x ᵥ* G.B) j ≤ G.payoff₂ x y := by
  simpa only [payoff₁_swap, swap_A, mulVec_transpose] using
    (isBestResponse₁_swap.2 h).le_payoff₁ j

/-- A mixed strategy is a best response to `y` iff no row earns more against `y` than it does. -/
theorem isBestResponse₁_iff_le_payoff₁ :
    G.IsBestResponse₁ x y ↔ IsMixedStrategy x ∧ ∀ i, (G.A *ᵥ y) i ≤ G.payoff₁ x y := by
  refine ⟨fun h => ⟨h.isMixedStrategy, h.le_payoff₁⟩, fun h => ⟨h.1, fun x' hx' => ?_⟩⟩
  rw [payoff₁_eq_dotProduct x' y]
  exact hx'.dotProduct_le_of_forall_le h.2

/-- A mixed strategy is a best response to `x` iff no column earns more against `x` than it
does. -/
theorem isBestResponse₂_iff_le_payoff₂ :
    G.IsBestResponse₂ y x ↔ IsMixedStrategy y ∧ ∀ j, (x ᵥ* G.B) j ≤ G.payoff₂ x y := by
  rw [← isBestResponse₁_swap, isBestResponse₁_iff_le_payoff₁]
  simp only [payoff₁_swap, swap_A, mulVec_transpose]

/-- With positive payoffs, player 1 earns a positive expected payoff. -/
theorem payoff₁_pos (hA : ∀ i j, 0 < G.A i j) (hx : IsMixedStrategy x) (hy : IsMixedStrategy y) :
    0 < G.payoff₁ x y :=
  hx.dotProduct_pos fun i => by
    change 0 < G.A i ⬝ᵥ y
    rw [dotProduct_comm]
    exact hy.dotProduct_pos (hA i)

/-- With positive payoffs, player 2 earns a positive expected payoff. -/
theorem payoff₂_pos (hB : ∀ i j, 0 < G.B i j) (hx : IsMixedStrategy x) (hy : IsMixedStrategy y) :
    0 < G.payoff₂ x y := by
  exact payoff₁_swap G y x ▸ G.swap.payoff₁_pos (fun j i => hB i j) hy hx

private theorem IsNash.ncard_support_le (hG : G.IsNondegenerate) (h : G.IsNash x y) :
    (Function.support x).ncard ≤ (Function.support y).ncard :=
  (Set.ncard_le_ncard (fun i hi =>
    (isBestResponse₁_iff.1 h.1).2 i (lt_of_le_of_ne (h.1.1.nonneg i) (Ne.symm hi)))
    (Set.toFinite _)).trans (hG.2 y h.2.1)

/-- In a Nash equilibrium of a nondegenerate bimatrix game, both strategies have supports of the
same size ([vonStengel2007], Proposition 3.3). -/
theorem IsNash.ncard_support_eq (hG : G.IsNondegenerate) (h : G.IsNash x y) :
    (Function.support x).ncard = (Function.support y).ncard :=
  le_antisymm (h.ncard_support_le hG)
    ((isNash_swap.2 h).ncard_support_le (isNondegenerate_swap.2 hG))

/-! ### Adding a constant to all payoffs -/

variable (G) in
/-- The game with the constant `c` added to every payoff of both players. -/
def addConst (c : ℝ) : BimatrixGame M N :=
  ⟨G.A + of fun _ _ => c, G.B + of fun _ _ => c⟩

omit [Fintype M] [Fintype N] in
@[simp]
theorem swap_addConst (G : BimatrixGame M N) (c : ℝ) :
    (G.addConst c).swap = G.swap.addConst c := by
  simp only [swap, addConst, transpose_add]
  rfl

omit [Fintype M] [Fintype N] in
@[simp]
theorem addConst_A_apply (c : ℝ) (i : M) (j : N) : (G.addConst c).A i j = G.A i j + c := by
  rw [addConst]
  rfl

omit [Fintype M] [Fintype N] in
@[simp]
theorem addConst_B_apply (c : ℝ) (i : M) (j : N) : (G.addConst c).B i j = G.B i j + c := by
  rw [addConst]
  rfl

omit [Fintype M] in
/-- Adding `c` to every payoff shifts player 1's pure-row payoff vector by the constant
`c * ∑ j, y j`. -/
theorem addConst_A_mulVec (c : ℝ) (y : N → ℝ) :
    (G.addConst c).A *ᵥ y = G.A *ᵥ y + fun _ => c * ∑ j, y j := by
  rw [addConst, add_mulVec]
  ext i
  simp [mulVec, dotProduct, mul_sum]

omit [Fintype N] in
/-- Adding `c` to every payoff shifts player 2's pure-column payoff vector by the constant
`c * ∑ i, x i`. -/
theorem vecMul_addConst_B (c : ℝ) (x : M → ℝ) :
    x ᵥ* (G.addConst c).B = x ᵥ* G.B + fun _ => c * ∑ i, x i := by
  rw [← mulVec_transpose, ← swap_A, swap_addConst, addConst_A_mulVec, swap_A, mulVec_transpose]

omit [Fintype M] in
/-- Adding a constant to all payoffs does not change player 1's pure best responses. -/
@[simp]
theorem isPureBestResponse₁_addConst {c : ℝ} {i : M} :
    (G.addConst c).IsPureBestResponse₁ y i ↔ G.IsPureBestResponse₁ y i := by
  simp [IsPureBestResponse₁, addConst_A_mulVec]

omit [Fintype N] in
/-- Adding a constant to all payoffs does not change player 2's pure best responses. -/
@[simp]
theorem isPureBestResponse₂_addConst {c : ℝ} {j : N} :
    (G.addConst c).IsPureBestResponse₂ x j ↔ G.IsPureBestResponse₂ x j := by
  rw [← isPureBestResponse₁_swap, swap_addConst, isPureBestResponse₁_addConst,
    isPureBestResponse₁_swap]

/-- Adding a constant to all payoffs does not change the Nash equilibria. -/
@[simp]
theorem isNash_addConst {c : ℝ} : (G.addConst c).IsNash x y ↔ G.IsNash x y := by
  simp [IsNash, isBestResponse₁_iff, isBestResponse₂_iff]

/-- Adding a constant to all payoffs does not change nondegeneracy. -/
@[simp]
theorem isNondegenerate_addConst {c : ℝ} :
    (G.addConst c).IsNondegenerate ↔ G.IsNondegenerate := by
  simp [IsNondegenerate]

omit [Fintype M] [Fintype N] in
variable (G) in
/-- A large enough constant makes all payoffs positive. -/
theorem exists_addConst_pos [Finite M] [Finite N] :
    ∃ c, (∀ i j, 0 < (G.addConst c).A i j) ∧ ∀ i j, 0 < (G.addConst c).B i j := by
  obtain ⟨c, hc⟩ :=
    (Set.toFinite (Set.range fun p : M × N => max (-G.A p.1 p.2) (-G.B p.1 p.2))).bddAbove
  refine ⟨c + 1, fun i j => ?_, fun i j => ?_⟩
  · linarith [G.addConst_A_apply (c + 1) i j, (le_max_left _ _).trans (hc ⟨(i, j), rfl⟩)]
  · linarith [G.addConst_B_apply (c + 1) i j, (le_max_right _ _).trans (hc ⟨(i, j), rfl⟩)]

end BimatrixGame

end Cslib.GameTheory
