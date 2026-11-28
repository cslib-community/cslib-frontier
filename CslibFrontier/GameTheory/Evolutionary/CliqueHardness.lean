/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Clique
public import CslibFrontier.Computability.Complexity.Problems.SAT
public import CslibFrontier.Computability.Complexity.Reduction
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.GameTheory.Bimatrix.FNP
public import CslibFrontier.GameTheory.Evolutionary.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique
import CslibFrontier.Computability.Complexity.CookLevin.Completeness
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Data.Fintype.Option
import Mathlib.Data.List.GetD
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Computational complexity of evolutionarily stable strategies

This module formalizes Nisan's clique reduction for evolutionarily stable strategies (ESS) and the
resulting `NP`-hardness and `coNP`-hardness theorems from [Suri2007], Section 29.2 (pp. 720–723)
and Exercise 29.5 (p. 735).

Given a finite simple graph `G` on vertex type `V` and a positive integer `k`, the symmetric
two-player game `BimatrixGame.cliqueESSGame G k` has pure strategy set `Option V`, where `none`
is strategy `0` and `some v` represents vertex `v`:

* `A (some u) (some v) = 1 / 2` when `u = v`, `1` when `G.Adj u v`, and `0` otherwise;
* `A none _ = A _ none = 1 - 1 / (2 * k)`;
* `B = Aᵀ` (and in fact `Aᵀ = A`).

The reduction yields an exact correspondence between the clique number `G.cliqueNum` and the
evolutionarily stable strategies of `cliqueESSGame G k`:

* every strategy `s` with `s none = 0` earns self-fitness at most `1 - 1 / (2 * G.cliqueNum)`,
  with equality iff `s` is uniform on a maximum clique ([Suri2007], Lemma 29.3);
* the uniform strategy on any maximal clique of size greater than `k` is an ESS
  ([Suri2007], Lemma 29.4);
* pure strategy `none` is an ESS iff `G.cliqueNum < k` ([Suri2007], Lemmas 29.5 and 29.6);
* when `G.cliqueNum ≤ k`, no strategy other than pure `none` is an ESS ([Suri2007], Lemma 29.7
  and Exercise 29.5);
* consequently, `cliqueESSGame G k` has an ESS iff `G.cliqueNum ≠ k`.

Representing symmetric two-player rational games on `BimatrixCode` (`encBimatrix`) as well-formed
square games with `B = Aᵀ` (`BimatrixCode.IsSymmetric`), we define the decision problems
`BimatrixCode.SymGameHasESS` (ESS existence) and `BimatrixCode.SymGameIsESS` (ESS recognition on
`SymGameStrategyInstance` under `encSymGameStrategyInstance`). Explicit multi-tape Turing-machine
polynomial-time reductions prove:

* `Clique ≤ₚ SymGameHasESS` (capping `k ≤ |V(G)|` before taking the disjoint union `G ⊔ K_{k-1}`
  so that binary targets `k` stay polynomial-time), giving `NP`-hardness of ESS existence;
* `UNSAT ≤ₚ SymGameHasESS` via the complement of Karp's `SAT.toIndependentSet` graph (whose clique
  number is always at most the clause count `m` and equals `m` iff the formula is satisfiable),
  giving `coNP`-hardness of ESS existence ([Suri2007], Theorem 29.8);
* `Cliqueᶜ ≤ₚ SymGameIsESS`, giving `coNP`-hardness of ESS recognition ([Suri2007], Theorem 29.9).

## Main definitions

* `Cslib.GameTheory.BimatrixGame.cliqueESSGame`: Nisan's clique-to-ESS symmetric game
  ([Suri2007], Section 29.2, p. 721).
* `Cslib.GameTheory.BimatrixGame.cliqueUniformStrategy`: uniform mixed strategy on a vertex set.
* `Cslib.GameTheory.BimatrixCode.IsSymmetric`, `Cslib.GameTheory.BimatrixCode.toSymGame`:
  symmetric rational bimatrix codes (`B = Aᵀ`) and their induced symmetric games.
* `Cslib.GameTheory.BimatrixCode.SymGameHasESS`: existence of an ESS in a symmetric rational game.
* `Cslib.GameTheory.SymGameStrategyInstance`, `Cslib.GameTheory.encSymGameStrategyInstance`,
  `Cslib.GameTheory.BimatrixCode.SymGameIsESS`: recognition of an ESS in a symmetric rational game.

## Main results

* `Cslib.GameTheory.BimatrixGame.payoff₁_self_cliqueESSGame_le`,
  `Cslib.GameTheory.BimatrixGame.payoff₁_self_cliqueESSGame_eq_iff`: upper bound and equality
  characterization for strategies supported on vertices ([Suri2007], Lemma 29.3).
* `Cslib.GameTheory.BimatrixGame.isESS_cliqueESSGame_of_maximalClique`: uniform distribution on a
  maximal clique larger than `k` is an ESS ([Suri2007], Lemma 29.4).
* `Cslib.GameTheory.BimatrixGame.isESS_cliqueESSGame_pureNone_iff`: pure strategy `none` is an ESS
  iff `G.cliqueNum < k` ([Suri2007], Lemmas 29.5 and 29.6).
* `Cslib.GameTheory.BimatrixGame.not_isESS_cliqueESSGame_of_cliqueNum_le`: no strategy other than
  pure `none` is an ESS when `G.cliqueNum ≤ k` ([Suri2007], Lemma 29.7, Exercise 29.5).
* `Cslib.GameTheory.BimatrixGame.exists_isESS_cliqueESSGame_iff`: `cliqueESSGame G k` has an ESS
  iff `G.cliqueNum ≠ k`.
* `Cslib.GameTheory.BimatrixCode.polyTimeReducible_Clique_SymGameHasESS`,
  `Cslib.GameTheory.BimatrixCode.polyTimeReducible_UNSAT_SymGameHasESS`,
  `Cslib.GameTheory.BimatrixCode.SymGameHasESS_npHard`,
  `Cslib.GameTheory.BimatrixCode.SymGameHasESS_coNPHard`: deciding whether a symmetric rational
  two-player game has an ESS is both `NP`-hard and `coNP`-hard ([Suri2007], Theorem 29.8).
* `Cslib.GameTheory.BimatrixCode.polyTimeReducible_Clique_compl_SymGameIsESS`,
  `Cslib.GameTheory.BimatrixCode.SymGameIsESS_coNPHard`: deciding whether a given rational
  strategy is an ESS of a symmetric rational two-player game is `coNP`-hard
  ([Suri2007], Theorem 29.9).

## References

* [S. Suri, *Computational Evolutionary Game Theory*][Suri2007], Section 29.2, pp. 720–723, and
  Exercise 29.5, p. 735
-/

public section

open Finset Matrix

namespace Cslib.GameTheory.BimatrixGame

/-! ### Section 1: Nisan's clique-to-ESS symmetric game -/

section CliqueGame

variable {V : Type*} [DecidableEq V]

/-- Nisan's symmetric two-player game attached to a simple graph `G` and parameter `k`
([Suri2007], Section 29.2, p. 721). Pure strategies are `Option V`, where `none` plays the role
of pure strategy `0` and `some v` represents vertex `v`. Payoffs are `1 / 2` on the vertex
diagonal, `1` on edges of `G`, `0` on non-edges, and `1 - 1 / (2 * k)` on the entire `none` row
and column; `B = Aᵀ`. -/
noncomputable def cliqueESSGame (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    BimatrixGame (Option V) (Option V) :=
  let A : Matrix (Option V) (Option V) ℝ := Matrix.of fun x y =>
    match x, y with
    | none, _ => 1 - 1 / (2 * (k : ℝ))
    | _, none => 1 - 1 / (2 * (k : ℝ))
    | some u, some v => if u = v then 1 / 2 else if G.Adj u v then 1 else 0
  ⟨A, Aᵀ⟩

@[simp]
theorem cliqueESSGame_A_none_left (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (y : Option V) :
    (cliqueESSGame G k).A none y = 1 - 1 / (2 * (k : ℝ)) := by
  cases y <;> simp [cliqueESSGame]

@[simp]
theorem cliqueESSGame_A_none_right (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (x : Option V) :
    (cliqueESSGame G k).A x none = 1 - 1 / (2 * (k : ℝ)) := by
  cases x <;> simp [cliqueESSGame]

@[simp]
theorem cliqueESSGame_A_some_some (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (u v : V) :
    (cliqueESSGame G k).A (some u) (some v) =
      if u = v then 1 / 2 else if G.Adj u v then 1 else 0 := by
  simp [cliqueESSGame]

/-- `cliqueESSGame G k` is a symmetric bimatrix game (`B = Aᵀ`). -/
theorem cliqueESSGame_B (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    (cliqueESSGame G k).B = (cliqueESSGame G k).Aᵀ := by
  rw [cliqueESSGame]

/-- Player 1's payoff matrix in `cliqueESSGame G k` is itself symmetric (`Aᵀ = A`). -/
theorem cliqueESSGame_A_transpose (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    (cliqueESSGame G k).Aᵀ = (cliqueESSGame G k).A := by
  ext x y
  rcases x with _ | u <;> rcases y with _ | v
  · simp
  · simp
  · simp
  · simp only [transpose_apply, cliqueESSGame_A_some_some]
    by_cases huv : u = v
    · subst huv; simp
    · have hvu : v ≠ u := Ne.symm huv
      simp [huv, hvu, G.adj_comm]

/-- The strategy assigning uniform probability `1 / #C` to each `some v` with `v ∈ C` and `0` to
`none` and to vertices outside `C`. -/
noncomputable def cliqueUniformStrategy (C : Finset V) : Option V → ℝ
  | none => 0
  | some v => if v ∈ C then 1 / (C.card : ℝ) else 0

@[simp]
theorem cliqueUniformStrategy_none (C : Finset V) : cliqueUniformStrategy C none = 0 := by
  rw [cliqueUniformStrategy]

@[simp]
theorem cliqueUniformStrategy_some (C : Finset V) (v : V) :
    cliqueUniformStrategy C (some v) = if v ∈ C then 1 / (C.card : ℝ) else 0 := by
  rw [cliqueUniformStrategy]

/-- The uniform strategy on a nonempty vertex set is a mixed strategy on `Option V`. -/
theorem isMixedStrategy_cliqueUniformStrategy [Fintype V] {C : Finset V} (hC : C.Nonempty) :
    IsMixedStrategy (cliqueUniformStrategy C) := by
  have hcard : (C.card : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_pos.2 hC).ne'
  refine isMixedStrategy_iff.2 ⟨fun x => ?_, ?_⟩
  · cases x with
    | none => exact le_rfl
    | some v => dsimp only [cliqueUniformStrategy]; split_ifs <;> positivity
  · rw [Fintype.sum_option, cliqueUniformStrategy_none, zero_add]
    simp only [cliqueUniformStrategy_some, Finset.sum_ite_mem, Finset.univ_inter,
      Finset.sum_const, nsmul_eq_mul, mul_one_div_cancel hcard]

/-! ### Section 2: Quadratic form and Lemma 29.3 -/

/-- The vertex-block quadratic form `F(s|s) = (1 / 2) ∑ x_v^2 + xᵀ A_G x` on `V → ℝ`. -/
private noncomputable def cliqueQuad [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : V → ℝ) : ℝ :=
  (1 / 2 : ℝ) * (∑ u : V, x u ^ 2) + x ⬝ᵥ G.adjMatrix ℝ *ᵥ x

/-- Any strategy with `s none = 0` has self-payoff equal to `cliqueQuad G (s ∘ some)`. -/
private theorem payoff₁_self_eq_cliqueQuad [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) {s : Option V → ℝ} (hs0 : s none = 0) :
    (cliqueESSGame G k).payoff₁ s s = cliqueQuad G (fun v => s (some v)) := by
  rw [payoff₁_eq_dotProduct, cliqueQuad]
  simp only [dotProduct, mulVec, Fintype.sum_option, hs0, zero_mul, mul_zero, zero_add,
    cliqueESSGame_A_some_some]
  have hentry (u v : V) :
      (if u = v then (1 / 2 : ℝ) else if G.Adj u v then 1 else 0) =
        (if u = v then 1 / 2 else 0) + (G.adjMatrix ℝ u v) := by
    simp only [SimpleGraph.adjMatrix_apply]
    by_cases huv : u = v
    · subst huv; simp
    · by_cases hadj : G.Adj u v <;> simp [huv, hadj]
  have hinner (u : V) :
      ∑ v : V, (if u = v then (1 / 2 : ℝ) else if G.Adj u v then 1 else 0) * s (some v) =
        (1 / 2 : ℝ) * s (some u) + ∑ v : V, G.adjMatrix ℝ u v * s (some v) := by
    simp only [hentry, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte]
  simp only [hinner, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun u _ => by ring

omit [DecidableEq V] in
/-- On a clique `C`, any probability vector supported inside `C` satisfies the exact identity
`cliqueQuad G x = 1 - 1 / (2 * #C) - (1 / 2) * ∑ v ∈ C, (x v - 1 / #C)^2`. -/
private theorem cliqueQuad_eq_of_isClique [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {C : Finset V} (hC : G.IsClique (C : Set V)) {x : V → ℝ}
    (hxout : ∀ v, v ∉ C → x v = 0) (hx1 : ∑ v : V, x v = 1) :
    cliqueQuad G x =
      1 - 1 / (2 * (C.card : ℝ)) - (1 / 2 : ℝ) * ∑ v ∈ C, (x v - 1 / (C.card : ℝ)) ^ 2 := by
  classical
  have hsumC : ∑ v ∈ C, x v = 1 :=
    (Finset.sum_subset (Finset.subset_univ C) fun v _ hv => hxout v hv).trans hx1
  have hCne : C.Nonempty := Finset.nonempty_of_sum_ne_zero (by rw [hsumC]; exact one_ne_zero)
  have hcard : (C.card : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_pos.2 hCne).ne'
  have hsq : ∑ v : V, x v ^ 2 = ∑ v ∈ C, x v ^ 2 :=
    (Finset.sum_subset (Finset.subset_univ C) fun v _ hv => by simp [hxout v hv]).symm
  have hadj : x ⬝ᵥ G.adjMatrix ℝ *ᵥ x = 1 - ∑ v ∈ C, x v ^ 2 := by
    have hterm (u v : V) :
        x u * (G.adjMatrix ℝ u v * x v) =
          x u * x v - if u = v then x u ^ 2 else 0 := by
      by_cases hmem : u ∈ C ∧ v ∈ C
      · by_cases huv : u = v
        · subst huv; simp [SimpleGraph.adjMatrix_apply, sq]
        · simp [SimpleGraph.adjMatrix_apply, hC hmem.1 hmem.2 huv, huv]
      · rcases not_and_or.1 hmem with hu | hv
        · simp [hxout u hu]
        · by_cases huv : u = v
          · subst huv; simp [hxout u hv]
          · simp [hxout v hv, huv]
    calc x ⬝ᵥ G.adjMatrix ℝ *ᵥ x
        = ∑ u : V, ∑ v : V, x u * (G.adjMatrix ℝ u v * x v) := by
            simp only [dotProduct, mulVec, Finset.mul_sum]
      _ = ∑ u : V, ∑ v : V, (x u * x v - if u = v then x u ^ 2 else 0) :=
            Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => hterm u v
      _ = (∑ u : V, x u) * (∑ v : V, x v) - ∑ u : V, x u ^ 2 := by
            simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
              ← Finset.mul_sum, ← Finset.sum_mul]
      _ = 1 - ∑ v ∈ C, x v ^ 2 := by rw [hx1, hsq, one_mul]
  have hvar :
      ∑ v ∈ C, (x v - 1 / (C.card : ℝ)) ^ 2 = (∑ v ∈ C, x v ^ 2) - 1 / (C.card : ℝ) := by
    have hexp :
        ∑ v ∈ C, (x v - 1 / (C.card : ℝ)) ^ 2 =
          (∑ v ∈ C, x v ^ 2) - 2 / (C.card : ℝ) * (∑ v ∈ C, x v) +
            ∑ _v ∈ C, (1 / (C.card : ℝ)) ^ 2 := by
      simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
      congr 2
      refine Finset.sum_congr rfl fun v _ => by ring
    rw [hexp, hsumC, Finset.sum_const, nsmul_eq_mul]
    field_simp [hcard]
    ring
  rw [cliqueQuad, hsq, hadj, hvar]
  field_simp [hcard]
  ring

/-- Moving mass `t` from `v` to `u` along a non-edge `(u, v)` changes `cliqueQuad` by
`2 * t * ((A_G x)_u - (A_G x)_v) + t * (x_u - x_v) + t^2`. -/
private theorem cliqueQuad_add_smul [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v : V} (huv : u ≠ v) (hadj : ¬ G.Adj u v) (x : V → ℝ) (t : ℝ) :
    let d : V → ℝ := Pi.single u 1 - Pi.single v 1
    cliqueQuad G (x + t • d) =
      cliqueQuad G x + 2 * t * ((G.adjMatrix ℝ *ᵥ x) u - (G.adjMatrix ℝ *ᵥ x) v) +
        t * (x u - x v) + t ^ 2 := by
  intro d
  set A := G.adjMatrix ℝ
  have hsymm : Aᵀ = A := G.transpose_adjMatrix
  have hd (y : V → ℝ) : d ⬝ᵥ y = y u - y v := by
    simp only [d, Pi.sub_apply, dotProduct, Pi.single_apply, sub_mul, Finset.sum_sub_distrib,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hdAd : d ⬝ᵥ (A *ᵥ d) = 0 := by
    have hrow (w : V) : (A *ᵥ d) w = A w u - A w v := by
      simp only [d, mulVec, dotProduct, Pi.sub_apply, Pi.single_apply, mul_sub,
        Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte]
    rw [hd, hrow u, hrow v]
    simp only [A, SimpleGraph.adjMatrix_apply, G.loopless.irrefl, hadj, G.adj_comm v u, ↓reduceIte,
      sub_self]
  have hquadA :
      (x + t • d) ⬝ᵥ A *ᵥ (x + t • d) =
        x ⬝ᵥ A *ᵥ x + 2 * t * ((A *ᵥ x) u - (A *ᵥ x) v) := by
    have hdx : d ⬝ᵥ (A *ᵥ x) = (A *ᵥ x) u - (A *ᵥ x) v := hd (A *ᵥ x)
    have hxd : x ⬝ᵥ (A *ᵥ d) = d ⬝ᵥ (A *ᵥ x) := by
      rw [dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose, hsymm]
    calc (x + t • d) ⬝ᵥ A *ᵥ (x + t • d)
        = (x + t • d) ⬝ᵥ (A *ᵥ x + t • (A *ᵥ d)) := by rw [mulVec_add, mulVec_smul]
      _ = x ⬝ᵥ (A *ᵥ x) + t * (x ⬝ᵥ (A *ᵥ d)) + t * (d ⬝ᵥ (A *ᵥ x)) +
            t * (t * (d ⬝ᵥ (A *ᵥ d))) := by
          simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
            smul_eq_mul]
          ring
      _ = x ⬝ᵥ A *ᵥ x + 2 * t * ((A *ᵥ x) u - (A *ᵥ x) v) := by
          rw [hxd, hdx, hdAd]; ring
  have hsqDiff :
      ∑ w : V, (x + t • d) w ^ 2 - ∑ w : V, x w ^ 2 = 2 * t * (x u - x v) + 2 * t ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    have hterm (w : V) :
        (x + t • d) w ^ 2 - x w ^ 2 =
          (if w = u then 2 * t * x u + t ^ 2 else 0) +
            (if w = v then -(2 * t * x v) + t ^ 2 else 0) := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, d, Pi.sub_apply, Pi.single_apply]
      by_cases hwu : w = u
      · subst hwu; simp only [↓reduceIte, huv, sub_zero, mul_one, add_zero]; ring
      · by_cases hwv : w = v
        · subst hwv; simp only [hwu, ↓reduceIte, zero_sub, mul_neg, mul_one, zero_add]; ring
        · simp [hwu, hwv]
    simp only [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    ring
  rw [cliqueQuad, cliqueQuad, hquadA]
  linarith

omit [DecidableEq V] in
private theorem one_div_two_cliqueNum_le [Finite V] (G : SimpleGraph V) {S : Finset V}
    (hSne : S.Nonempty) (hclique : G.IsClique (S : Set V)) :
    1 / (2 * (G.cliqueNum : ℝ)) ≤ 1 / (2 * (S.card : ℝ)) := by
  have hScard_pos : (0 : ℝ) < 2 * (S.card : ℝ) := by
    have : 0 < S.card := Finset.card_pos.2 hSne
    positivity
  have hScard_le : 2 * (S.card : ℝ) ≤ 2 * (G.cliqueNum : ℝ) := by
    have hle : (S.card : ℝ) ≤ (G.cliqueNum : ℝ) := mod_cast hclique.card_le_cliqueNum
    linarith
  exact one_div_le_one_div_of_le hScard_pos hScard_le

omit [DecidableEq V] in
/-- Induction core of Lemma 29.3: every probability vector `x : V → ℝ` satisfies
`cliqueQuad G x ≤ 1 - 1 / (2 * G.cliqueNum)`, and the inequality is strict whenever its support
is not a clique. -/
private theorem cliqueQuad_le_and_lt_of_not_isClique [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {x : V → ℝ} (hx0 : ∀ v, 0 ≤ x v) (hx1 : ∑ v, x v = 1) :
    cliqueQuad G x ≤ 1 - 1 / (2 * (G.cliqueNum : ℝ)) ∧
      (¬ G.IsClique (({v | x v ≠ 0} : Finset V) : Set V) →
        cliqueQuad G x < 1 - 1 / (2 * (G.cliqueNum : ℝ))) := by
  classical
  set S : Finset V := Finset.univ.filter fun v => x v ≠ 0
  have hxout : ∀ v, v ∉ S → x v = 0 := fun v hv => by
    simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hv
  have hsumS : ∑ v ∈ S, x v = 1 :=
    (Finset.sum_subset (Finset.subset_univ S) fun v _ hv => hxout v hv).trans hx1
  have hSne : S.Nonempty := Finset.nonempty_of_sum_ne_zero (by rw [hsumS]; exact one_ne_zero)
  by_cases hclique : G.IsClique (S : Set V)
  · refine ⟨?_, fun h => absurd hclique h⟩
    rw [cliqueQuad_eq_of_isClique G hclique hxout hx1]
    have hvar : 0 ≤ ∑ v ∈ S, (x v - 1 / (S.card : ℝ)) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith [one_div_two_cliqueNum_le G hSne hclique]
  · have hnot := hclique
    simp only [SimpleGraph.IsClique, Set.Pairwise, Finset.mem_coe, not_forall] at hnot
    obtain ⟨u, huS, v, hvS, huv, hadj⟩ := hnot
    have hxu : 0 < x u := lt_of_le_of_ne (hx0 u) (Ne.symm (by simpa [S] using huS))
    have hxv : 0 < x v := lt_of_le_of_ne (hx0 v) (Ne.symm (by simpa [S] using hvS))
    let d : V → ℝ := Pi.single u 1 - Pi.single v 1
    have hstep (t : ℝ) (ht1 : 0 ≤ x u + t) (ht2 : 0 ≤ x v - t) :
        (∀ w, 0 ≤ (x + t • d) w) ∧ ∑ w, (x + t • d) w = 1 := by
      refine ⟨fun w => ?_, ?_⟩
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, d, Pi.sub_apply, Pi.single_apply]
        by_cases hwu : w = u
        · subst hwu; simp only [↓reduceIte, huv, sub_zero, mul_one]; exact ht1
        · by_cases hwv : w = v
          · subst hwv; simp only [hwu, ↓reduceIte, zero_sub, mul_neg, mul_one]; linarith
          · simp only [hwu, hwv, ↓reduceIte, sub_self, mul_zero, add_zero]; exact hx0 w
      · simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, d, Finset.sum_add_distrib,
          Finset.sum_sub_distrib, ← Finset.mul_sum, hx1]
    have hlt_supp (t : ℝ) (hzero : (x + t • d) u = 0 ∨ (x + t • d) v = 0) :
        (Finset.univ.filter fun w => (x + t • d) w ≠ 0).card < S.card := by
      refine Finset.card_lt_card ⟨fun w hw => ?_, fun hsub => ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
        by_contra hxw
        have hxw0 := hxout w hxw
        have hwu : w ≠ u := fun h => hxu.ne' (h ▸ hxw0)
        have hwv : w ≠ v := fun h => hxv.ne' (h ▸ hxw0)
        exact hw (by simp [d, hxw0, hwu, hwv])
      · rcases hzero with h | h
        · exact (Finset.mem_filter.1 (hsub huS)).2 h
        · exact (Finset.mem_filter.1 (hsub hvS)).2 h
    have hlt_goal : cliqueQuad G x < 1 - 1 / (2 * (G.cliqueNum : ℝ)) := by
      rcases le_total ((G.adjMatrix ℝ *ᵥ x) v) ((G.adjMatrix ℝ *ᵥ x) u) with hle | hle
      · have ht := hstep (x v) (by linarith) (by linarith)
        have hlt := hlt_supp (x v) (Or.inr (by simp [d, Ne.symm huv]))
        have hih := (cliqueQuad_le_and_lt_of_not_isClique G ht.1 ht.2).1
        have hlin := cliqueQuad_add_smul G huv hadj x (x v)
        have hpos1 : 0 ≤ 2 * x v * ((G.adjMatrix ℝ *ᵥ x) u - (G.adjMatrix ℝ *ᵥ x) v) :=
          mul_nonneg (by linarith) (sub_nonneg.2 hle)
        have hpos2 : 0 < x u * x v := mul_pos hxu hxv
        have halg : x v * (x u - x v) + x v ^ 2 = x u * x v := by ring
        linarith
      · have ht := hstep (-x u) (by linarith) (by linarith)
        have hlt := hlt_supp (-x u) (Or.inl (by simp [d, huv]))
        have hih := (cliqueQuad_le_and_lt_of_not_isClique G ht.1 ht.2).1
        have hlin := cliqueQuad_add_smul G huv hadj x (-x u)
        have hpos1 : 0 ≤ 2 * x u * ((G.adjMatrix ℝ *ᵥ x) v - (G.adjMatrix ℝ *ᵥ x) u) :=
          mul_nonneg (by linarith) (sub_nonneg.2 hle)
        have hpos2 : 0 < x u * x v := mul_pos hxu hxv
        have halg : (-x u) * (x u - x v) + (-x u) ^ 2 = x u * x v := by ring
        linarith
    exact ⟨hlt_goal.le, fun _ => hlt_goal⟩
termination_by (Finset.univ.filter fun w => x w ≠ 0).card
decreasing_by all_goals assumption

/-- **Upper bound on vertex-supported strategies** ([Suri2007], Lemma 29.3, p. 721): any mixed
strategy `s` with `s none = 0` satisfies `F(s|s) ≤ 1 - 1 / (2 * G.cliqueNum)`. -/
theorem payoff₁_self_cliqueESSGame_le [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) {s : Option V → ℝ} (hs : IsMixedStrategy s) (hs0 : s none = 0) :
    (cliqueESSGame G k).payoff₁ s s ≤ 1 - 1 / (2 * (G.cliqueNum : ℝ)) := by
  rw [payoff₁_self_eq_cliqueQuad G k hs0]
  have hsum : ∑ v : V, s (some v) = 1 := by
    have h := hs.sum_eq_one
    rwa [Fintype.sum_option, hs0, zero_add] at h
  exact (cliqueQuad_le_and_lt_of_not_isClique G (fun v => hs.nonneg (some v)) hsum).1

/-- **Equality characterization for vertex-supported strategies** ([Suri2007], Lemma 29.3, p. 721):
a mixed strategy `s` with `s none = 0` achieves `F(s|s) = 1 - 1 / (2 * G.cliqueNum)` if and only
if `s` is the uniform distribution over a maximum clique of `G`. -/
theorem payoff₁_self_cliqueESSGame_eq_iff [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) {s : Option V → ℝ} (hs : IsMixedStrategy s) (hs0 : s none = 0) :
    (cliqueESSGame G k).payoff₁ s s = 1 - 1 / (2 * (G.cliqueNum : ℝ)) ↔
      ∃ C : Finset V, G.IsNClique G.cliqueNum C ∧ s = cliqueUniformStrategy C := by
  rw [payoff₁_self_eq_cliqueQuad G k hs0]
  have hx0 : ∀ v : V, 0 ≤ s (some v) := fun v => hs.nonneg (some v)
  have hx1 : ∑ v : V, s (some v) = 1 := by
    have h := hs.sum_eq_one
    rwa [Fintype.sum_option, hs0, zero_add] at h
  constructor
  · intro heq
    set S : Finset V := Finset.univ.filter fun v => s (some v) ≠ 0
    have hxout : ∀ v, v ∉ S → s (some v) = 0 := fun v hv => by
      simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hv
    have hclique : G.IsClique (S : Set V) := by
      by_contra hnot
      exact ne_of_lt ((cliqueQuad_le_and_lt_of_not_isClique G hx0 hx1).2 hnot) heq
    have hsumS : ∑ v ∈ S, s (some v) = 1 :=
      (Finset.sum_subset (Finset.subset_univ S) fun v _ hv => hxout v hv).trans hx1
    have hSne : S.Nonempty := Finset.nonempty_of_sum_ne_zero (by rw [hsumS]; exact one_ne_zero)
    have hdiv := one_div_two_cliqueNum_le G hSne hclique
    have hvar_nonneg : 0 ≤ ∑ v ∈ S, (s (some v) - 1 / (S.card : ℝ)) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    rw [cliqueQuad_eq_of_isClique G hclique hxout hx1] at heq
    have hdiv_eq : 1 / (2 * (S.card : ℝ)) = 1 / (2 * (G.cliqueNum : ℝ)) := by linarith
    have hcard_eq_real : (2 : ℝ) * (S.card : ℝ) = 2 * (G.cliqueNum : ℝ) := by
      have h := congrArg Inv.inv hdiv_eq
      simpa only [one_div, inv_inv] using h
    have hcard_eq : S.card = G.cliqueNum := by
      have : (S.card : ℝ) = (G.cliqueNum : ℝ) := by linarith
      exact Nat.cast_injective this
    have hvar_zero : ∑ v ∈ S, (s (some v) - 1 / (S.card : ℝ)) ^ 2 = 0 := by linarith
    have hvar_each := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).1 hvar_zero
    refine ⟨S, ⟨hclique, hcard_eq⟩, funext fun x => ?_⟩
    cases x with
    | none => exact hs0
    | some v =>
      rw [cliqueUniformStrategy_some]
      by_cases hv : v ∈ S
      · simp only [hv, ↓reduceIte]
        have hsq0 := hvar_each v hv
        exact sub_eq_zero.1 (sq_eq_zero_iff.1 hsq0)
      · simp only [hv, ↓reduceIte]
        exact hxout v hv
  · rintro ⟨C, hC, rfl⟩
    have hCne : C.Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      subst hempty
      simp [cliqueUniformStrategy] at hx1
    rw [cliqueQuad_eq_of_isClique G hC.isClique (fun v hv => by simp [cliqueUniformStrategy, hv])
      hx1, hC.card_eq]
    have hzero : ∑ v ∈ C, (cliqueUniformStrategy C (some v) - 1 / (C.card : ℝ)) ^ 2 = 0 :=
      Finset.sum_eq_zero fun v hv => by simp [cliqueUniformStrategy, hv]
    rw [← hC.card_eq, hzero, mul_zero, sub_zero]

/-! ### Section 3: Lemmas 29.4–29.7 and ESS characterizations -/

/-- **Maximal cliques larger than `k` yield ESSs** ([Suri2007], Lemma 29.4, p. 722): if `C` is a
maximal clique of `G` with `k < #C` and `0 < k`, then the uniform distribution on `C` is an ESS
of `cliqueESSGame G k`. -/
theorem isESS_cliqueESSGame_of_maximalClique [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (hk : 0 < k) {C : Finset V}
    (hC : Maximal (fun S : Finset V => G.IsClique (S : Set V)) C) (hcard : k < C.card) :
    (cliqueESSGame G k).IsESS (cliqueUniformStrategy C) := by
  set s := cliqueUniformStrategy C
  have hCne : C.Nonempty := Finset.card_pos.1 (by omega)
  have hcard_pos : (0 : ℝ) < (C.card : ℝ) := Nat.cast_pos.2 (Finset.card_pos.2 hCne)
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.2 hk
  have hk_lt_C : (k : ℝ) < (C.card : ℝ) := Nat.cast_lt.2 hcard
  have hs : IsMixedStrategy s := isMixedStrategy_cliqueUniformStrategy hCne
  have hmul_none : ((cliqueESSGame G k).A *ᵥ s) none = 1 - 1 / (2 * (k : ℝ)) := by
    simp only [mulVec, dotProduct, cliqueESSGame_A_none_left, ← Finset.mul_sum, hs.sum_eq_one,
      mul_one]
  have hmul_mem {u : V} (hu : u ∈ C) :
      ((cliqueESSGame G k).A *ᵥ s) (some u) = 1 - 1 / (2 * (C.card : ℝ)) := by
    simp only [mulVec, dotProduct, Fintype.sum_option, cliqueUniformStrategy_none, mul_zero,
      zero_add, cliqueESSGame_A_some_some, cliqueUniformStrategy_some, s]
    have hsub :
        ∑ v : V, (if u = v then (1 / 2 : ℝ) else if G.Adj u v then 1 else 0) *
            (if v ∈ C then 1 / (C.card : ℝ) else 0) =
          ∑ v ∈ C, (if u = v then (1 / 2 : ℝ) else 1) * (1 / (C.card : ℝ)) := by
      rw [← Finset.sum_subset (Finset.subset_univ C) fun v _ hv => by simp [hv]]
      refine Finset.sum_congr rfl fun v hv => ?_
      simp only [hv, ↓reduceIte]
      by_cases huv : u = v
      · simp [huv]
      · simp [huv, hC.prop hu hv huv]
    rw [hsub, ← Finset.sum_mul]
    have hsplit : ∑ v ∈ C, (if u = v then (1 / 2 : ℝ) else 1) = (C.card : ℝ) - 1 / 2 := by
      have hterm (v : V) :
          (if u = v then (1 / 2 : ℝ) else 1) = 1 - (if u = v then (1 / 2 : ℝ) else 0) := by
        split_ifs <;> ring
      simp only [hterm, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
        Finset.sum_ite_eq, hu, ↓reduceIte]
    rw [hsplit]
    field_simp [hcard_pos.ne']
  have hmul_notMem {u : V} (hu : u ∉ C) :
      ((cliqueESSGame G k).A *ᵥ s) (some u) < 1 - 1 / (2 * (C.card : ℝ)) := by
    have hnotCl : ¬ G.IsClique ((insert u C : Finset V) : Set V) := fun hcl =>
      hu (hC.le_of_ge hcl (Finset.subset_insert u C) (Finset.mem_insert_self u C))
    rw [Finset.coe_insert, SimpleGraph.isClique_insert] at hnotCl
    have hnotAll : ¬ ∀ v ∈ C, u ≠ v → G.Adj u v := fun hall => hnotCl ⟨hC.prop, hall⟩
    push Not at hnotAll
    obtain ⟨v₀, hv₀C, huv₀, hnadj⟩ := hnotAll
    simp only [mulVec, dotProduct, Fintype.sum_option, cliqueUniformStrategy_none, mul_zero,
      zero_add, cliqueESSGame_A_some_some, cliqueUniformStrategy_some, s]
    have hsub :
        ∑ v : V, (if u = v then (1 / 2 : ℝ) else if G.Adj u v then 1 else 0) *
            (if v ∈ C then 1 / (C.card : ℝ) else 0) =
          (∑ v ∈ C, (if G.Adj u v then (1 : ℝ) else 0)) * (1 / (C.card : ℝ)) := by
      rw [← Finset.sum_subset (Finset.subset_univ C) fun v _ hv => by simp [hv], Finset.sum_mul]
      refine Finset.sum_congr rfl fun v hv => ?_
      have huv : u ≠ v := fun h => hu (h ▸ hv)
      simp [huv, hv]
    rw [hsub]
    have hsum_le : ∑ v ∈ C, (if G.Adj u v then (1 : ℝ) else 0) ≤ (C.card : ℝ) - 1 := by
      have hterm_le (v : V) :
          (if G.Adj u v then (1 : ℝ) else 0) ≤ if v = v₀ then 0 else 1 := by
        by_cases hvv₀ : v = v₀
        · subst hvv₀; simp [hnadj]
        · split_ifs <;> norm_num
      have hle := Finset.sum_le_sum (s := C) fun v _ => hterm_le v
      have hsum_rhs : ∑ v ∈ C, (if v = v₀ then (0 : ℝ) else 1) = (C.card : ℝ) - 1 := by
        have hrewrite (v : V) :
            (if v = v₀ then (0 : ℝ) else (1 : ℝ)) = 1 - if v = v₀ then 1 else 0 := by
          split_ifs <;> ring
        simp only [hrewrite, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
          Finset.sum_ite_eq', hv₀C, ↓reduceIte]
      linarith
    have hdiv_le :
        (∑ v ∈ C, (if G.Adj u v then (1 : ℝ) else 0)) * (1 / (C.card : ℝ)) ≤
          1 - 1 / (C.card : ℝ) := by
      calc (∑ v ∈ C, (if G.Adj u v then (1 : ℝ) else 0)) * (1 / (C.card : ℝ))
          ≤ ((C.card : ℝ) - 1) * (1 / (C.card : ℝ)) :=
            mul_le_mul_of_nonneg_right hsum_le (by positivity)
        _ = 1 - 1 / (C.card : ℝ) := by field_simp [hcard_pos.ne']
    have hgap : 1 / (2 * (C.card : ℝ)) < 1 / (C.card : ℝ) :=
      one_div_lt_one_div_of_lt hcard_pos (by linarith)
    linarith
  have hnone_lt : ((cliqueESSGame G k).A *ᵥ s) none < 1 - 1 / (2 * (C.card : ℝ)) := by
    rw [hmul_none]
    have := one_div_lt_one_div_of_lt (by positivity : (0 : ℝ) < 2 * (k : ℝ))
      (by linarith : 2 * (k : ℝ) < 2 * (C.card : ℝ))
    linarith
  have hle_all : ∀ x : Option V, ((cliqueESSGame G k).A *ᵥ s) x ≤ 1 - 1 / (2 * (C.card : ℝ)) := by
    intro x
    cases x with
    | none => exact hnone_lt.le
    | some u =>
      by_cases hu : u ∈ C
      · exact (hmul_mem hu).le
      · exact (hmul_notMem hu).le
  have hself : (cliqueESSGame G k).payoff₁ s s = 1 - 1 / (2 * (C.card : ℝ)) := by
    rw [payoff₁_eq_dotProduct]
    refine hs.dotProduct_eq_of_forall_pos fun x hx => ?_
    cases x with
    | none => simp [s] at hx
    | some u =>
      by_cases hu : u ∈ C
      · exact hmul_mem hu
      · simp [s, hu] at hx
  rw [isESS_iff_forall_lt_or]
  refine ⟨hs, fun t ht hne => ?_⟩
  by_cases hsupp : t none = 0 ∧ ∀ u, u ∉ C → t (some u) = 0
  · refine Or.inr ⟨?_, ?_⟩
    · rw [payoff₁_eq_dotProduct, hself]
      refine ht.dotProduct_eq_of_forall_pos fun x hx => ?_
      cases x with
      | none => linarith [hsupp.1]
      | some u =>
        by_cases hu : u ∈ C
        · exact hmul_mem hu
        · linarith [hsupp.2 u hu]
    · have hst : (cliqueESSGame G k).payoff₁ s t = 1 - 1 / (2 * (C.card : ℝ)) := by
        have hsym : (cliqueESSGame G k).payoff₁ s t = (cliqueESSGame G k).payoff₁ t s := by
          rw [payoff₁_eq_dotProduct, payoff₁_eq_dotProduct, dotProduct_mulVec, dotProduct_comm,
            ← mulVec_transpose, cliqueESSGame_A_transpose]
        rw [hsym, payoff₁_eq_dotProduct]
        refine ht.dotProduct_eq_of_forall_pos fun x hx => ?_
        cases x with
        | none => linarith [hsupp.1]
        | some u =>
          by_cases hu : u ∈ C
          · exact hmul_mem hu
          · linarith [hsupp.2 u hu]
      have ht1 : ∑ v : V, t (some v) = 1 := by
        have h := ht.sum_eq_one
        rwa [Fintype.sum_option, hsupp.1, zero_add] at h
      rw [hst, payoff₁_self_eq_cliqueQuad G k hsupp.1,
        cliqueQuad_eq_of_isClique G hC.prop hsupp.2 ht1]
      have hne_entry : ∃ v ∈ C, t (some v) ≠ 1 / (C.card : ℝ) := by
        by_contra hall
        push Not at hall
        apply hne
        funext x
        cases x with
        | none => exact hsupp.1
        | some v =>
          simp only [s, cliqueUniformStrategy_some]
          by_cases hv : v ∈ C
          · simp [hv, hall v hv]
          · simp [hv, hsupp.2 v hv]
      obtain ⟨v, hvC, hvt⟩ := hne_entry
      have hvar_pos : 0 < ∑ w ∈ C, (t (some w) - 1 / (C.card : ℝ)) ^ 2 :=
        Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨v, hvC, sq_pos_of_ne_zero (sub_ne_zero.2 hvt)⟩
      linarith
  · refine Or.inl ?_
    rw [payoff₁_eq_dotProduct, hself]
    have hlt_exists : ∃ x : Option V, 0 < t x ∧
        ((cliqueESSGame G k).A *ᵥ s) x < 1 - 1 / (2 * (C.card : ℝ)) := by
      by_cases h0 : t none = 0
      · have hnotall : ¬ ∀ u, u ∉ C → t (some u) = 0 := fun hall => hsupp ⟨h0, hall⟩
        push Not at hnotall
        obtain ⟨u, huC, hut⟩ := hnotall
        exact ⟨some u, lt_of_le_of_ne (ht.nonneg (some u)) (Ne.symm hut), hmul_notMem huC⟩
      · exact ⟨none, lt_of_le_of_ne (ht.nonneg none) (Ne.symm h0), hnone_lt⟩
    obtain ⟨x₀, hx₀pos, hx₀lt⟩ := hlt_exists
    calc t ⬝ᵥ ((cliqueESSGame G k).A *ᵥ s)
        = ∑ x : Option V, t x * ((cliqueESSGame G k).A *ᵥ s) x := rfl
      _ < ∑ x : Option V, t x * (1 - 1 / (2 * (C.card : ℝ))) :=
          Finset.sum_lt_sum (fun x _ => mul_le_mul_of_nonneg_left (hle_all x) (ht.nonneg x))
            ⟨x₀, Finset.mem_univ _, mul_lt_mul_of_pos_left hx₀lt hx₀pos⟩
      _ = 1 - 1 / (2 * (C.card : ℝ)) := by rw [← Finset.sum_mul, ht.sum_eq_one, one_mul]

/-- Pure strategy `none` earns `1 - 1 / (2 * k)` against every mixed strategy. -/
private theorem payoff₁_pureNone_left [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) {t : Option V → ℝ} (ht : IsMixedStrategy t) :
    (cliqueESSGame G k).payoff₁ (Pi.single none 1) t = 1 - 1 / (2 * (k : ℝ)) := by
  rw [payoff₁_eq_dotProduct, single_dotProduct, one_mul]
  simp only [mulVec, dotProduct, cliqueESSGame_A_none_left, ← Finset.mul_sum, ht.sum_eq_one,
    mul_one]

/-- Every mixed strategy earns `1 - 1 / (2 * k)` against pure strategy `none`. -/
private theorem payoff₁_pureNone_right [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) {t : Option V → ℝ} (ht : IsMixedStrategy t) :
    (cliqueESSGame G k).payoff₁ t (Pi.single none 1) = 1 - 1 / (2 * (k : ℝ)) := by
  simp only [payoff₁_eq_dotProduct, dotProduct, mulVec, mul_ite, mul_one, mul_zero,
    Pi.single_apply, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    cliqueESSGame_A_none_right, ← Finset.sum_mul, ht.sum_eq_one, one_mul]

/-- Any mixed strategy `t ≠ Pi.single none 1` has `t none < 1` and decomposes into `none` plus a
vertex-supported mixed strategy `t*` satisfying
`c - F(t|t) = (1 - t none)^2 * (c - F(t*|t*))` where `c = 1 - 1 / (2 * k)`. -/
private theorem exists_vertex_decomp_of_ne_pureNone [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (k : ℕ) {t : Option V → ℝ} (ht : IsMixedStrategy t)
    (hne : t ≠ Pi.single none 1) :
    ∃ t' : Option V → ℝ, IsMixedStrategy t' ∧ t' none = 0 ∧ 0 < 1 - t none ∧
      (1 - 1 / (2 * (k : ℝ))) - (cliqueESSGame G k).payoff₁ t t =
        (1 - t none) ^ 2 * ((1 - 1 / (2 * (k : ℝ))) - (cliqueESSGame G k).payoff₁ t' t') := by
  set α := t none
  set c : ℝ := 1 - 1 / (2 * (k : ℝ))
  have hα_lt : α < 1 := by
    have hle : α ≤ 1 := by
      have h := ht.sum_eq_one
      rw [Fintype.sum_option] at h
      have hnn : 0 ≤ ∑ v : V, t (some v) := Finset.sum_nonneg fun v _ => ht.nonneg (some v)
      linarith
    refine lt_of_le_of_ne hle fun h1 => hne ?_
    have hsum0 : ∑ v : V, t (some v) = 0 := by
      have h := ht.sum_eq_one
      rw [Fintype.sum_option] at h
      linarith
    have hall0 := (Finset.sum_eq_zero_iff_of_nonneg fun v _ => ht.nonneg (some v)).1 hsum0
    funext x
    cases x with
    | none => simpa [α] using h1
    | some v => simp [hall0 v (Finset.mem_univ v)]
  have h1α : 0 < 1 - α := sub_pos.2 hα_lt
  let t' : Option V → ℝ := fun
    | none => 0
    | some v => t (some v) / (1 - α)
  have ht'_mix : IsMixedStrategy t' := by
    refine isMixedStrategy_iff.2 ⟨fun x => ?_, ?_⟩
    · cases x with
      | none => exact le_rfl
      | some v => exact div_nonneg (ht.nonneg (some v)) h1α.le
    · rw [Fintype.sum_option]
      dsimp only [t']
      rw [zero_add, ← Finset.sum_div]
      have h := ht.sum_eq_one
      rw [Fintype.sum_option] at h
      exact (div_eq_one_iff_eq h1α.ne').2 (by linarith)
  have hdecomp : t = α • (Pi.single none (1 : ℝ)) + (1 - α) • t' := by
    funext x
    cases x with
    | none => simp [t', α]
    | some v =>
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, reduceCtorEq,
        ↓reduceIte, mul_zero, zero_add, t']
      exact (mul_div_cancel₀ _ h1α.ne').symm
  have h00 : (cliqueESSGame G k).payoff₁ (Pi.single none 1) (Pi.single none 1) = c :=
    payoff₁_pureNone_left G k (isMixedStrategy_single none)
  have h0t' : (cliqueESSGame G k).payoff₁ (Pi.single none 1) t' = c :=
    payoff₁_pureNone_left G k ht'_mix
  have ht'0 : (cliqueESSGame G k).payoff₁ t' (Pi.single none 1) = c :=
    payoff₁_pureNone_right G k ht'_mix
  have hbilin :
      (cliqueESSGame G k).payoff₁ t t =
        (2 * α - α ^ 2) * c + (1 - α) ^ 2 * (cliqueESSGame G k).payoff₁ t' t' := by
    simp only [payoff₁_eq_dotProduct] at h00 h0t' ht'0 ⊢
    conv_lhs => rw [hdecomp]
    simp only [mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, h00, h0t', ht'0]
    ring
  refine ⟨t', ht'_mix, rfl, h1α, ?_⟩
  rw [hbilin]
  ring

/-- **Pure strategy `none` is an ESS iff `G.cliqueNum < k`** ([Suri2007], Lemmas 29.5 and 29.6,
p. 722): when `0 < k`, playing strategy `0` (`none`) is evolutionarily stable in
`cliqueESSGame G k` if and only if the maximum clique size of `G` is strictly smaller than `k`. -/
theorem isESS_cliqueESSGame_pureNone_iff [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (hk : 0 < k) :
    (cliqueESSGame G k).IsESS (Pi.single none 1) ↔ G.cliqueNum < k := by
  rw [isESS_iff_forall_lt_or]
  constructor
  · rintro ⟨-, h⟩
    by_contra hlt
    have hle : k ≤ G.cliqueNum := Nat.le_of_not_lt hlt
    obtain ⟨C, hC⟩ := G.exists_isNClique_cliqueNum
    have hCne : C.Nonempty := Finset.card_pos.1 (by rw [hC.card_eq]; omega)
    set t := cliqueUniformStrategy C
    have ht : IsMixedStrategy t := isMixedStrategy_cliqueUniformStrategy hCne
    have hne : t ≠ Pi.single none 1 := fun heq => by
      have h0 := congrFun heq none
      simp [t] at h0
    have hte0 : (cliqueESSGame G k).payoff₁ t (Pi.single none 1) =
        (cliqueESSGame G k).payoff₁ (Pi.single none 1) (Pi.single none 1) := by
      rw [payoff₁_pureNone_right G k ht, payoff₁_pureNone_left G k (isMixedStrategy_single none)]
    have he0t : (cliqueESSGame G k).payoff₁ (Pi.single none 1) t = 1 - 1 / (2 * (k : ℝ)) :=
      payoff₁_pureNone_left G k ht
    have htt : (cliqueESSGame G k).payoff₁ t t = 1 - 1 / (2 * (G.cliqueNum : ℝ)) :=
      (payoff₁_self_cliqueESSGame_eq_iff G k ht rfl).2 ⟨C, hC, rfl⟩
    have hdiv : 1 / (2 * (G.cliqueNum : ℝ)) ≤ 1 / (2 * (k : ℝ)) :=
      one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 2 * (k : ℝ))
        (by have : (k : ℝ) ≤ (G.cliqueNum : ℝ) := mod_cast hle; linarith)
    rcases h t ht hne with h1 | ⟨-, h2⟩ <;> linarith
  · intro hlt
    refine ⟨isMixedStrategy_single none, fun t ht hne => Or.inr ⟨?_, ?_⟩⟩
    · rw [payoff₁_pureNone_right G k ht, payoff₁_pureNone_left G k (isMixedStrategy_single none)]
    · obtain ⟨t', ht', ht'0, h1α, hdecomp⟩ :=
        exists_vertex_decomp_of_ne_pureNone G k ht hne
      have hV : Nonempty V := by
        by_contra hempty
        rw [not_nonempty_iff] at hempty
        have hsum := ht'.sum_eq_one
        rw [Fintype.sum_option, ht'0] at hsum
        simp at hsum
      have hω_pos : 0 < G.cliqueNum := Nat.pos_of_ne_zero G.cliqueNum_ne_zero_of_finite
      have hle' := payoff₁_self_cliqueESSGame_le G k ht' ht'0
      have hgap : 1 / (2 * (k : ℝ)) < 1 / (2 * (G.cliqueNum : ℝ)) :=
        one_div_lt_one_div_of_lt (by positivity : (0 : ℝ) < 2 * (G.cliqueNum : ℝ))
          (by have : (G.cliqueNum : ℝ) < (k : ℝ) := mod_cast hlt; linarith)
      have hpos : 0 < (1 - t none) ^ 2 *
          ((1 - 1 / (2 * (k : ℝ))) - (cliqueESSGame G k).payoff₁ t' t') :=
        mul_pos (sq_pos_of_pos h1α) (by linarith)
      rw [payoff₁_pureNone_left G k ht]
      linarith

/-- **No non-zero strategy is an ESS when `G.cliqueNum ≤ k`** ([Suri2007], Lemma 29.7, p. 722, and
Exercise 29.5, p. 735): if the maximum clique size of `G` is at most `k`, then no strategy other
than pure strategy `none` is evolutionarily stable in `cliqueESSGame G k`. -/
theorem not_isESS_cliqueESSGame_of_cliqueNum_le [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {k : ℕ} (hω : G.cliqueNum ≤ k) {s : Option V → ℝ}
    (hne : s ≠ Pi.single none 1) :
    ¬ (cliqueESSGame G k).IsESS s := by
  intro hESS
  have hs : IsMixedStrategy s := hESS.isMixedStrategy
  obtain ⟨s', hs', hs'0, _, hdecomp⟩ := exists_vertex_decomp_of_ne_pureNone G k hs hne
  have hV : Nonempty V := by
    by_contra hempty
    rw [not_nonempty_iff] at hempty
    have hsum := hs'.sum_eq_one
    rw [Fintype.sum_option, hs'0] at hsum
    simp at hsum
  have hω_pos : 0 < G.cliqueNum := Nat.pos_of_ne_zero G.cliqueNum_ne_zero_of_finite
  have hle' := payoff₁_self_cliqueESSGame_le G k hs' hs'0
  have hdiv : 1 / (2 * (k : ℝ)) ≤ 1 / (2 * (G.cliqueNum : ℝ)) :=
    one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 2 * (G.cliqueNum : ℝ))
      (by have : (G.cliqueNum : ℝ) ≤ (k : ℝ) := mod_cast hω; linarith)
  have hnn : 0 ≤ (1 - s none) ^ 2 *
      ((1 - 1 / (2 * (k : ℝ))) - (cliqueESSGame G k).payoff₁ s' s') :=
    mul_nonneg (sq_nonneg _) (by linarith)
  have hss_le : (cliqueESSGame G k).payoff₁ s s ≤ 1 - 1 / (2 * (k : ℝ)) := by linarith
  have h0s := payoff₁_pureNone_left G k hs
  have hs0 := payoff₁_pureNone_right G k hs
  have h00 := payoff₁_pureNone_left G k (isMixedStrategy_single none)
  rcases (isESS_iff_forall_lt_or.1 hESS).2 (Pi.single none 1) (isMixedStrategy_single none)
      hne.symm with h1 | ⟨-, h2⟩ <;> linarith

/-- **Existence of an ESS characterizes `G.cliqueNum ≠ k`** ([Suri2007], Section 29.2, pp. 721–723,
combining Lemmas 29.4–29.7): for `0 < k`, `cliqueESSGame G k` has an evolutionarily stable strategy
if and only if the clique number of `G` is not equal to `k`. -/
theorem exists_isESS_cliqueESSGame_iff [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (hk : 0 < k) :
    (∃ s, (cliqueESSGame G k).IsESS s) ↔ G.cliqueNum ≠ k := by
  constructor
  · rintro ⟨s, hs⟩ heq
    by_cases h0 : s = Pi.single none 1
    · subst h0
      exact lt_irrefl k (heq ▸ (isESS_cliqueESSGame_pureNone_iff G hk).1 hs)
    · exact not_isESS_cliqueESSGame_of_cliqueNum_le G heq.le h0 hs
  · intro hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ⟨Pi.single none 1, (isESS_cliqueESSGame_pureNone_iff G hk).2 hlt⟩
    · obtain ⟨C, hC⟩ := G.exists_isNClique_cliqueNum
      have hmax : Maximal (fun S : Finset V => G.IsClique (S : Set V)) C :=
        ⟨hC.isClique, fun T hT hCT =>
          (Finset.eq_of_subset_of_card_le hCT (hC.card_eq ▸ hT.card_le_cliqueNum)).symm.subset⟩
      exact ⟨cliqueUniformStrategy C,
        isESS_cliqueESSGame_of_maximalClique G hk hmax (hC.card_eq ▸ hgt)⟩

end CliqueGame

/-- Relabeling pure strategies by an equivalence `e : α ≃ β` preserves evolutionary stability. -/
theorem isESS_relabel {α β : Type*} [Fintype α] [Fintype β]
    {G₁ : BimatrixGame α α} {G₂ : BimatrixGame β β} (e : α ≃ β)
    (hA : ∀ i j, G₁.A i j = G₂.A (e i) (e j)) {s : β → ℝ} :
    G₁.IsESS (s ∘ e) ↔ G₂.IsESS s := by
  have hmix : ∀ x : β → ℝ, IsMixedStrategy (x ∘ e) ↔ IsMixedStrategy x := fun x => by
    simp only [isMixedStrategy_iff, Function.comp_apply, e.forall_congr_left,
      Equiv.apply_symm_apply, Fintype.sum_equiv e _ _ (fun _ => rfl)]
  have hpay : ∀ x y : β → ℝ, G₁.payoff₁ (x ∘ e) (y ∘ e) = G₂.payoff₁ x y := fun x y => by
    simp only [payoff₁_eq_dotProduct, dotProduct, mulVec, Function.comp_apply, hA]
    exact Fintype.sum_equiv e _ _ fun i => by
      congr 1
      exact Fintype.sum_equiv e _ _ fun j => rfl
  simp only [isESS_iff_forall_lt_or, hmix]
  refine and_congr_right fun _ => ⟨fun h t ht hne => ?_, fun h t ht hne => ?_⟩
  · have hne' : t ∘ e ≠ s ∘ e := fun heq => hne (funext fun b => by
      simpa using congrFun heq (e.symm b))
    simpa only [hpay] using h (t ∘ e) ((hmix t).2 ht) hne'
  · let t' : β → ℝ := t ∘ e.symm
    have ht'_eq : t' ∘ e = t := funext fun a => by simp [t']
    have ht' : IsMixedStrategy t' := (hmix t').1 (by rwa [ht'_eq])
    have hne' : t' ≠ s := fun heq => hne (by rw [← ht'_eq, heq])
    simpa only [← ht'_eq, hpay] using h t' ht' hne'

end Cslib.GameTheory.BimatrixGame

/-! ### Section 4: Encoded symmetric rational games and hardness theorems -/

namespace Cslib.GameTheory

open Cslib Cslib.Complexity Cslib.GameTheory.BimatrixGame Cslib.Logic.PL
open Turing.MultiTapeTM ComputableInPolyTime

/-- An instance of the evolutionarily stable strategy recognition problem: an explicitly presented
two-player rational bimatrix game paired with a candidate rational mixed strategy. -/
@[ext]
structure SymGameStrategyInstance where
  /-- The explicitly presented two-player rational payoff matrices. -/
  game : BimatrixCode
  /-- The candidate rational mixed strategy as a list of probabilities. -/
  strategy : List ℚ
  deriving DecidableEq, Repr

/-- Framed `encBimatrix` followed by `encList encRat`, encoding `SymGameStrategyInstance`. -/
enc_structure encSymGameStrategyInstance : SymGameStrategyInstance where
  game : encBimatrix,
  strategy : (encList encRat)

attribute [fun_prop] encSymGameStrategyInstance_game_polyTime
  encSymGameStrategyInstance_strategy_polyTime encSymGameStrategyInstance_mk_polyTime

namespace BimatrixCode

/-- Predicate asserting that `c : BimatrixCode` encodes a finite symmetric two-player game:
nonempty, square (`rows = cols`), and with player 2's payoff matrix equal to the transpose of
player 1's (`B = Aᵀ`). -/
@[expose] def IsSymmetric (c : BimatrixCode) : Prop :=
  c.WellFormed ∧ c.rows = c.cols ∧
    ∀ i j : Fin c.rows, (c.matB.getD i.1 []).getD j.1 0 = (c.matA.getD j.1 []).getD i.1 0

/-- The symmetric two-player game `⟨A, Aᵀ⟩` on `Fin c.rows` extracted from player 1's payoff
matrix `c.matA`. When `c.IsSymmetric`, this coincides with `c.toGame` up to casting
`Fin c.rows` to `Fin c.cols`. -/
@[expose] noncomputable def toSymGame (c : BimatrixCode) :
    BimatrixGame (Fin c.rows) (Fin c.rows) :=
  let A : Matrix (Fin c.rows) (Fin c.rows) ℝ :=
    fun i j => ((c.matA.getD i.1 []).getD j.1 0 : ℝ)
  ⟨A, Aᵀ⟩

/-- The decision problem **ESS Existence** for two-player symmetric rational games
([Suri2007], Theorem 29.8, p. 723): well-formed symmetric bimatrix codes (`B = Aᵀ`) admitting an
evolutionarily stable strategy. -/
@[expose] def SymGameHasESS : Set BimatrixCode :=
  {c | c.IsSymmetric ∧ ∃ s, c.toSymGame.IsESS s}

/-- The decision problem **ESS Recognition** for two-player symmetric rational games
([Suri2007], Theorem 29.9, p. 723): pairs `(game, strategy)` where `game` is a well-formed
symmetric bimatrix code (`B = Aᵀ`) and `strategy` is a rational strategy vector of length
`game.rows` forming an evolutionarily stable strategy of `game.toSymGame`. -/
@[expose] def SymGameIsESS : Set SymGameStrategyInstance :=
  {x | x.game.IsSymmetric ∧ x.strategy.length = x.game.rows ∧
    x.game.toSymGame.IsESS (BimatrixCode.strategyVec x.strategy)}

/-! #### Relabeling invariance of ESS existence -/

private theorem exists_isESS_relabel {α β : Type*} [Fintype α] [Fintype β]
    {G₁ : BimatrixGame α α} {G₂ : BimatrixGame β β} (e : α ≃ β)
    (hA : ∀ i j, G₁.A i j = G₂.A (e i) (e j)) :
    (∃ s, G₁.IsESS s) ↔ (∃ s, G₂.IsESS s) :=
  ⟨fun ⟨s, hs⟩ => ⟨s ∘ e.symm, (isESS_relabel e hA).1 (by
      have heq : (s ∘ e.symm) ∘ e = s := funext fun a => by simp
      rwa [heq])⟩,
    fun ⟨s, hs⟩ => ⟨s ∘ e, (isESS_relabel e hA).2 hs⟩⟩

/-! #### Fixed `2 × 2` YES and NO instances -/

/-- A fixed `2 × 2` symmetric game (`!![1, 0; 0, 1]`) in which `[1, 0]` is an ESS. -/
private def yesGameCode : BimatrixCode :=
  ⟨[[1, 0], [0, 1]], [[1, 0], [0, 1]]⟩

/-- A fixed `2 × 2` zero symmetric game (`!![0, 0; 0, 0]`), which has no ESS. -/
private def noGameCode : BimatrixCode :=
  ⟨[[0, 0], [0, 0]], [[0, 0], [0, 0]]⟩

private theorem yesGameCode_isSymmetric : yesGameCode.IsSymmetric := by
  refine ⟨⟨by decide, by decide, rfl, ?_, ?_⟩, rfl, fun i j => ?_⟩
  · intro r hr; simp only [yesGameCode, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> rfl
  · intro r hr; simp only [yesGameCode, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> rfl
  · fin_cases i <;> fin_cases j <;> rfl

private theorem yesGameCode_mem_SymGameHasESS : yesGameCode ∈ SymGameHasESS := by
  let G₂ : BimatrixGame (Fin 2) (Fin 2) := ⟨!![1, 0; 0, 1], !![1, 0; 0, 1]ᵀ⟩
  have hG : G₂.IsESS ![1, 0] := by
    rw [isESS_fin_two_iff]
    refine ⟨isMixedStrategy_iff.2 ⟨fun i => by fin_cases i <;> norm_num,
      by norm_num [Fin.sum_univ_two]⟩, Or.inl ⟨rfl, Or.inl ?_⟩⟩
    norm_num [G₂]
  have hrel : (∃ s, yesGameCode.toSymGame.IsESS s) ↔ (∃ s, G₂.IsESS s) :=
    exists_isESS_relabel (finCongr (rfl : yesGameCode.rows = 2)) fun i j => by
      fin_cases i <;> fin_cases j <;> norm_num [toSymGame, yesGameCode, G₂, finCongr, Fin.cast]
  exact ⟨yesGameCode_isSymmetric, hrel.2 ⟨![1, 0], hG⟩⟩

private theorem noGameCode_notMem_SymGameHasESS : noGameCode ∉ SymGameHasESS := by
  rintro ⟨-, hs⟩
  let G₂ : BimatrixGame (Fin 2) (Fin 2) := ⟨0, 0⟩
  have hrel : (∃ s, noGameCode.toSymGame.IsESS s) ↔ (∃ s, G₂.IsESS s) :=
    exists_isESS_relabel (finCongr (rfl : noGameCode.rows = 2)) fun i j => by
      fin_cases i <;> fin_cases j <;> norm_num [toSymGame, noGameCode, G₂]
  have h2 : ∃ s, G₂.IsESS s := hrel.1 hs
  rw [exists_isESS_fin_two_iff] at h2
  rcases h2 with h | h <;> exact h rfl

private theorem noGameStrategy_notMem_SymGameIsESS :
    (⟨noGameCode, [1, 0]⟩ : SymGameStrategyInstance) ∉ SymGameIsESS :=
  fun ⟨hsym, _, hESS⟩ => noGameCode_notMem_SymGameHasESS ⟨hsym, _, hESS⟩

/-! #### Computable Nisan matrix encoding for `Graph` -/

/-- Entry `(u, v)` of the vertex block in Nisan's matrix for `G`. -/
private def nisanEntry (G : Graph) (u v : ℕ) : ℚ :=
  if u = v then (1 / 2 : ℚ) else if G.adjBool u v then 1 else 0

/-- Row list of Nisan's `(n + 1) × (n + 1)` symmetric rational matrix for `(G, k)` on
`G.distinctVertices`. -/
private def nisanRows (G : Graph) (k : ℕ) : List (List ℚ) :=
  let vs := G.distinctVertices
  let c : ℚ := 1 - 1 / (2 * (k : ℚ))
  List.replicate (vs.length + 1) c ::
    vs.map fun u => c :: vs.map fun v => nisanEntry G u v

/-- The symmetric `BimatrixCode` encoding Nisan's game for `(G, k)`. -/
private def nisanGameCode (G : Graph) (k : ℕ) : BimatrixCode :=
  let M := nisanRows G k
  ⟨M, M⟩

private theorem nisanGameCode_rows (G : Graph) (k : ℕ) :
    (nisanGameCode G k).rows = G.distinctVertices.length + 1 := by
  simp [nisanGameCode, rows, nisanRows]

private theorem nisanGameCode_isSymmetric (G : Graph) (k : ℕ) :
    (nisanGameCode G k).IsSymmetric := by
  have hrows : (nisanGameCode G k).rows = G.distinctVertices.length + 1 :=
    nisanGameCode_rows G k
  have hcols : (nisanGameCode G k).cols = G.distinctVertices.length + 1 := by
    simp [nisanGameCode, cols, nisanRows]
  have hlen : ∀ r ∈ nisanRows G k, r.length = G.distinctVertices.length + 1 := by
    intro r hr
    simp only [nisanRows, List.mem_cons, List.mem_map] at hr
    rcases hr with rfl | ⟨u, _, rfl⟩ <;> simp
  refine ⟨⟨by omega, by omega, rfl, fun r hr => (hlen r hr).trans hcols.symm,
      fun r hr => (hlen r hr).trans hcols.symm⟩, hrows.trans hcols.symm, fun i j => ?_⟩
  change ((nisanRows G k).getD i.1 []).getD j.1 0 = ((nisanRows G k).getD j.1 []).getD i.1 0
  have hi : i.1 < G.distinctVertices.length + 1 := hrows ▸ i.2
  have hj : j.1 < G.distinctVertices.length + 1 := hrows ▸ j.2
  rcases i with ⟨_ | i', hi'⟩ <;> rcases j with ⟨_ | j', hj'⟩
  · rfl
  · have hjlt : j' < G.distinctVertices.length := by omega
    simp [nisanRows, List.getD_eq_getElem?_getD, hjlt]
  · have hilt : i' < G.distinctVertices.length := by omega
    simp [nisanRows, List.getD_eq_getElem?_getD, hilt]
  · have hilt : i' < G.distinctVertices.length := by omega
    have hjlt : j' < G.distinctVertices.length := by omega
    simp only [nisanRows, List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.getElem?_map,
      List.getElem?_eq_getElem hilt, List.getElem?_eq_getElem hjlt, Option.map_some,
      Option.getD_some, nisanEntry]
    by_cases huv : G.distinctVertices[i'] = G.distinctVertices[j']
    · simp [huv]
    · have hvu : G.distinctVertices[j'] ≠ G.distinctVertices[i'] := Ne.symm huv
      have hadj : G.adjBool G.distinctVertices[i'] G.distinctVertices[j'] =
          G.adjBool G.distinctVertices[j'] G.distinctVertices[i'] := by
        rw [Bool.eq_iff_iff, G.adjBool_eq_true_iff, G.adjBool_eq_true_iff,
          G.toSimpleGraph.adj_comm]
      simp only [huv, hvu, ↓reduceIte]
      rw [hadj]

/-- Equivalence identifying `Fin (nisanGameCode G k).rows` with `Option {v // v ∈ G.vertices}`,
sending `0` to `none` and `i + 1` to `some (G.vertexEquiv i)`. -/
private def nisanEquiv (G : Graph) (k : ℕ) :
    Fin (nisanGameCode G k).rows ≃ Option {v // v ∈ G.vertices} :=
  (finCongr (nisanGameCode_rows G k)).trans
    ((finSuccEquiv G.distinctVertices.length).trans (Equiv.optionCongr G.vertexEquiv))

private theorem nisanEquiv_zero (G : Graph) (k : ℕ) :
    nisanEquiv G k ⟨0, by rw [nisanGameCode_rows]; omega⟩ = none := by
  simp [nisanEquiv]

private theorem nisanGameCode_A_eq (G : Graph) (k : ℕ)
    (i j : Fin (nisanGameCode G k).rows) :
    (nisanGameCode G k).toSymGame.A i j =
      (cliqueESSGame G.induced k).A (nisanEquiv G k i) (nisanEquiv G k j) := by
  have hrows := nisanGameCode_rows G k
  have hi : i.1 < G.distinctVertices.length + 1 := hrows ▸ i.2
  have hj : j.1 < G.distinctVertices.length + 1 := hrows ▸ j.2
  rcases i with ⟨_ | i', hi'⟩ <;> rcases j with ⟨_ | j', hj'⟩
  · rw [nisanEquiv_zero G k, cliqueESSGame_A_none_left]
    simp [toSymGame, nisanGameCode, nisanRows]
  · have hjlt : j' < G.distinctVertices.length := by omega
    rw [nisanEquiv_zero G k, cliqueESSGame_A_none_left]
    simp [toSymGame, nisanGameCode, nisanRows, List.getD_eq_getElem?_getD, hjlt]
  · have hilt : i' < G.distinctVertices.length := by omega
    rw [nisanEquiv_zero G k, cliqueESSGame_A_none_right]
    simp [toSymGame, nisanGameCode, nisanRows, List.getD_eq_getElem?_getD, hilt]
  · have hilt : i' < G.distinctVertices.length := by omega
    have hjlt : j' < G.distinctVertices.length := by omega
    have hval (a : Fin G.distinctVertices.length) :
        (G.vertexEquiv a : ℕ) = G.distinctVertices[a.1] := by
      rw [G.vertexEquiv_apply a, List.getD_eq_getElem _ _ a.2]
    have heq_i : nisanEquiv G k ⟨i' + 1, hi'⟩ = some (G.vertexEquiv ⟨i', hilt⟩) := by
      simp [nisanEquiv]
    have heq_j : nisanEquiv G k ⟨j' + 1, hj'⟩ = some (G.vertexEquiv ⟨j', hjlt⟩) := by
      simp [nisanEquiv]
    rw [heq_i, heq_j, cliqueESSGame_A_some_some]
    change (((nisanRows G k).getD (i' + 1) []).getD (j' + 1) 0 : ℝ) = _
    simp only [nisanRows, List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.getElem?_map,
      List.getElem?_eq_getElem hilt, List.getElem?_eq_getElem hjlt, Option.map_some,
      Option.getD_some, nisanEntry]
    have hveq : G.vertexEquiv ⟨i', hilt⟩ = G.vertexEquiv ⟨j', hjlt⟩ ↔
        G.distinctVertices[i'] = G.distinctVertices[j'] := by
      rw [Subtype.ext_iff, hval ⟨i', hilt⟩, hval ⟨j', hjlt⟩]
    have hvadj : G.induced.Adj (G.vertexEquiv ⟨i', hilt⟩) (G.vertexEquiv ⟨j', hjlt⟩) ↔
        G.adjBool G.distinctVertices[i'] G.distinctVertices[j'] = true := by
      rw [Graph.induced_adj, hval ⟨i', hilt⟩, hval ⟨j', hjlt⟩, G.adjBool_eq_true_iff]
    by_cases huv : G.distinctVertices[i'] = G.distinctVertices[j']
    · have hv : G.vertexEquiv ⟨i', hilt⟩ = G.vertexEquiv ⟨j', hjlt⟩ := hveq.2 huv
      simp [huv, hv]
    · have hv : G.vertexEquiv ⟨i', hilt⟩ ≠ G.vertexEquiv ⟨j', hjlt⟩ := fun h => huv (hveq.1 h)
      by_cases hadj : G.adjBool G.distinctVertices[i'] G.distinctVertices[j'] = true
      · simp only [huv, hv, hadj, hvadj, ↓reduceIte, Rat.cast_one]
      · have hfalse : G.adjBool G.distinctVertices[i'] G.distinctVertices[j'] = false :=
          Bool.eq_false_iff.2 hadj
        simp only [huv, hv, hfalse, hvadj, Bool.false_eq_true, ↓reduceIte, Rat.cast_zero]

private theorem nisanGameCode_mem_SymGameHasESS_iff (G : Graph) {k : ℕ} (hk : 0 < k) :
    nisanGameCode G k ∈ SymGameHasESS ↔ G.cliqueNum ≠ k := by
  change (nisanGameCode G k).IsSymmetric ∧ (∃ s, (nisanGameCode G k).toSymGame.IsESS s) ↔ _
  rw [and_iff_right (nisanGameCode_isSymmetric G k),
    exists_isESS_relabel (nisanEquiv G k) (nisanGameCode_A_eq G k),
    exists_isESS_cliqueESSGame_iff G.induced hk, Graph.cliqueNum]

private theorem nisanGameCode_pureZero_mem_SymGameIsESS_iff (G : Graph) {k : ℕ} (hk : 0 < k) :
    (⟨nisanGameCode G k, (1 : ℚ) :: List.replicate G.distinctVertices.length 0⟩ :
        SymGameStrategyInstance) ∈ SymGameIsESS ↔
      G.cliqueNum < k := by
  set strat : List ℚ := (1 : ℚ) :: List.replicate G.distinctVertices.length 0
  have hlen : strat.length = (nisanGameCode G k).rows := by
    simp [strat, nisanGameCode_rows]
  change (nisanGameCode G k).IsSymmetric ∧ strat.length = (nisanGameCode G k).rows ∧
      (nisanGameCode G k).toSymGame.IsESS (strategyVec strat) ↔ _
  rw [and_iff_right (nisanGameCode_isSymmetric G k), and_iff_right hlen]
  have hvec : strategyVec (n := (nisanGameCode G k).rows) strat =
      (Pi.single none (1 : ℝ)) ∘ nisanEquiv G k := by
    funext i
    have hrows := nisanGameCode_rows G k
    have hi : i.1 < G.distinctVertices.length + 1 := hrows ▸ i.2
    rcases i with ⟨_ | i', hi'⟩
    · have h0 := nisanEquiv_zero G k
      simp [strategyVec, strat, nisanEquiv]
    · have hilt : i' < G.distinctVertices.length := by omega
      simp [strategyVec, strat, nisanEquiv, List.getD_eq_getElem?_getD, hilt]
  rw [hvec, isESS_relabel (nisanEquiv G k) (nisanGameCode_A_eq G k),
    isESS_cliqueESSGame_pureNone_iff G.induced hk, Graph.cliqueNum]

@[local fun_prop]
private theorem computableInPolyTime_nisanRows :
    ComputableInPolyTime (fun p : Graph × ℕ => nisanRows p.1 p.2)
      (encPair encGraph encNat) (encList (encList encRat)) := by
  unfold nisanRows nisanEntry
  fun_prop

@[local fun_prop]
private theorem computableInPolyTime_nisanGameCode :
    ComputableInPolyTime (fun p : Graph × ℕ => nisanGameCode p.1 p.2)
      (encPair encGraph encNat) encBimatrix := by
  unfold nisanGameCode
  exact encBimatrix_mk_polyTime computableInPolyTime_nisanRows computableInPolyTime_nisanRows

/-! #### Disjoint union `G ⊔ K_r` for the `Clique ≤ₚ SymGameHasESS` reduction -/

/-- Disjoint union of `G` (placed on even vertex labels `2 * v`) and a clique `K_r` (placed on odd
vertex labels `2 * i + 1` for `i < r`). -/
private def addDisjointClique (G : Graph) (r : ℕ) : Graph :=
  ⟨G.distinctVertices.map (fun v => 2 * v) ++ (List.range r).map (fun i => 2 * i + 1),
    G.edges.map (fun e => (2 * e.1, 2 * e.2)) ++
      (List.range r).flatMap fun i =>
        ((List.range r).filter fun j => decide (i ≠ j)).map fun j => (2 * i + 1, 2 * j + 1)⟩

private theorem addDisjointClique_adj_even_even (G : Graph) (r u v : ℕ) :
    (addDisjointClique G r).toSimpleGraph.Adj (2 * u) (2 * v) ↔ G.toSimpleGraph.Adj u v := by
  have hedge (a b : ℕ) : (2 * a, 2 * b) ∈ (addDisjointClique G r).edges ↔ (a, b) ∈ G.edges := by
    simp only [addDisjointClique, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_filter,
      List.mem_range, decide_eq_true_eq, Prod.mk.injEq]
    constructor
    · rintro (⟨⟨x, y⟩, hxy, h1, h2⟩ | ⟨i, _, j, _, h1, _⟩)
      · have hx : x = a := by omega
        have hy : y = b := by omega
        rwa [← hx, ← hy]
      · omega
    · intro h; exact Or.inl ⟨(a, b), h, rfl, rfl⟩
  simp only [Graph.toSimpleGraph_adj, hedge]
  constructor
  · rintro ⟨hne, h⟩; exact ⟨by omega, h⟩
  · rintro ⟨hne, h⟩; exact ⟨by omega, h⟩

private theorem addDisjointClique_not_adj_even_odd (G : Graph) (r u i : ℕ) :
    ¬ (addDisjointClique G r).toSimpleGraph.Adj (2 * u) (2 * i + 1) := by
  simp only [Graph.toSimpleGraph_adj, addDisjointClique, List.mem_append, List.mem_map,
    List.mem_flatMap, List.mem_filter, List.mem_range, decide_eq_true_eq, Prod.mk.injEq, not_and]
  intro _ h
  rcases h with (⟨⟨x, y⟩, _, h1, h2⟩ | ⟨a, _, b, _, h1, h2⟩) |
      (⟨⟨x, y⟩, _, h1, h2⟩ | ⟨a, _, b, _, h1, h2⟩) <;> omega

private theorem addDisjointClique_adj_odd_odd (G : Graph) (r : ℕ) {i j : ℕ}
    (hi : i < r) (hj : j < r) :
    (addDisjointClique G r).toSimpleGraph.Adj (2 * i + 1) (2 * j + 1) ↔ i ≠ j := by
  have hedge (a b : ℕ) (ha : a < r) (hb : b < r) :
      (2 * a + 1, 2 * b + 1) ∈ (addDisjointClique G r).edges ↔ a ≠ b := by
    simp only [addDisjointClique, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_filter,
      List.mem_range, decide_eq_true_eq, Prod.mk.injEq]
    constructor
    · rintro (⟨⟨x, y⟩, _, h1, _⟩ | ⟨p, _, q, ⟨_, hpq⟩, h1, h2⟩)
      · omega
      · omega
    · intro hab; exact Or.inr ⟨a, ha, b, ⟨hb, hab⟩, rfl, rfl⟩
  simp only [Graph.toSimpleGraph_adj, hedge i j hi hj, hedge j i hj hi]
  constructor
  · rintro ⟨hne, _⟩; omega
  · intro hij; exact ⟨by omega, Or.inl hij⟩

private theorem cliqueNum_addDisjointClique (G : Graph) (r : ℕ) :
    (addDisjointClique G r).cliqueNum = max G.cliqueNum r := by
  refine le_antisymm ?_ ?_
  · have hle : ∀ m, (⟨addDisjointClique G r, m⟩ : CliqueInstance) ∈ Clique →
        m ≤ max G.cliqueNum r := by
      intro m hm
      obtain ⟨S, hSV, hS⟩ := mem_Clique_iff.1 hm
      by_cases heven : ∃ w ∈ S, w % 2 = 0
      · obtain ⟨w₀, hw₀S, hw₀⟩ := heven
        have hall_even : ∀ w ∈ S, w % 2 = 0 := fun w hw => by
          by_contra hodd
          have hw_odd : w % 2 = 1 := by omega
          have hne : w₀ ≠ w := by omega
          have hadj := hS.isClique hw₀S hw hne
          have hw0eq : w₀ = 2 * (w₀ / 2) := by omega
          have hweq : w = 2 * (w / 2) + 1 := by omega
          rw [hw0eq, hweq] at hadj
          exact addDisjointClique_not_adj_even_odd G r (w₀ / 2) (w / 2) hadj
        let T : Finset ℕ := S.image (· / 2)
        have hinj : Set.InjOn (· / 2) (S : Set ℕ) := fun a ha b hb hab => by
          dsimp only at hab
          have ha' := hall_even a ha; have hb' := hall_even b hb; omega
        have hT_mem : ∀ v ∈ T, v ∈ G.vertices := fun v hv => by
          obtain ⟨w, hwS, rfl⟩ := Finset.mem_image.1 hv
          have hwV := hSV w hwS
          simp only [addDisjointClique, List.mem_append, List.mem_map, List.mem_range] at hwV
          rcases hwV with ⟨u, hu, rfl⟩ | ⟨i, _, hi⟩
          · simpa [Nat.mul_div_right _ (by decide : 0 < 2)] using Graph.mem_distinctVertices.1 hu
          · have := hall_even w hwS; omega
        have hT_cl : G.toSimpleGraph.IsNClique m T := by
          refine ⟨fun u hu v hv huv => ?_, ?_⟩
          · obtain ⟨a, haS, rfl⟩ := Finset.mem_image.1 hu
            obtain ⟨b, hbS, rfl⟩ := Finset.mem_image.1 hv
            have hae : a = 2 * (a / 2) := by have := hall_even a haS; omega
            have hbe : b = 2 * (b / 2) := by have := hall_even b hbS; omega
            have hab : a ≠ b := fun h => huv (congrArg (· / 2) h)
            have hadj := hS.isClique haS hbS hab
            rw [hae, hbe] at hadj
            exact (addDisjointClique_adj_even_even G r (a / 2) (b / 2)).1 hadj
          · rw [Finset.card_image_of_injOn hinj, hS.card_eq]
        exact (Graph.le_cliqueNum_iff.2 (mem_Clique_iff.2 ⟨T, hT_mem, hT_cl⟩)).trans
          (le_max_left _ _)
      · push Not at heven
        have hsub : S ⊆ (Finset.range r).image fun i => 2 * i + 1 := fun w hw => by
          have hwV := hSV w hw
          simp only [addDisjointClique, List.mem_append, List.mem_map, List.mem_range] at hwV
          rcases hwV with ⟨u, _, rfl⟩ | ⟨i, hir, rfl⟩
          · exact absurd (by omega : 2 * u % 2 = 0) (heven (2 * u) hw)
          · exact Finset.mem_image.2 ⟨i, Finset.mem_range.2 hir, rfl⟩
        have hcard : m ≤ r := by
          have hcard_eq : S.card = m := hS.card_eq
          rw [← hcard_eq]
          exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp))
        exact hcard.trans (le_max_right _ _)
    exact hle _ (Graph.le_cliqueNum_iff.1 le_rfl)
  · refine max_le ?_ ?_
    · rw [Graph.le_cliqueNum_iff, mem_Clique_iff]
      obtain ⟨S, hSV, hS⟩ := mem_Clique_iff.1 (Graph.le_cliqueNum_iff.1 (le_rfl : G.cliqueNum ≤ _))
      have hinj : Function.Injective (fun v : ℕ => 2 * v) := fun a b h => by dsimp only at h; omega
      refine ⟨S.image (fun v => 2 * v), fun w hw => ?_, ⟨fun a ha b hb hab => ?_, ?_⟩⟩
      · obtain ⟨v, hvS, rfl⟩ := Finset.mem_image.1 hw
        simp only [addDisjointClique, List.mem_append, List.mem_map]
        exact Or.inl ⟨v, Graph.mem_distinctVertices.2 (hSV v hvS), rfl⟩
      · obtain ⟨u, huS, rfl⟩ := Finset.mem_image.1 ha
        obtain ⟨v, hvS, rfl⟩ := Finset.mem_image.1 hb
        exact (addDisjointClique_adj_even_even G r u v).2
          (hS.isClique huS hvS (fun h => hab (by omega)))
      · rw [Finset.card_image_of_injective S hinj, hS.card_eq]
    · rw [Graph.le_cliqueNum_iff, mem_Clique_iff]
      have hinj : Function.Injective (fun i : ℕ => 2 * i + 1) := fun a b h => by
        dsimp only at h; omega
      refine ⟨(Finset.range r).image (fun i => 2 * i + 1), fun w hw => ?_,
        ⟨fun a ha b hb hab => ?_, ?_⟩⟩
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hw
        simp only [addDisjointClique, List.mem_append, List.mem_map, List.mem_range]
        exact Or.inr ⟨i, Finset.mem_range.1 hi, rfl⟩
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ha
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hb
        exact (addDisjointClique_adj_odd_odd G r (Finset.mem_range.1 hi)
          (Finset.mem_range.1 hj)).2 (fun h => hab (by omega))
      · rw [Finset.card_image_of_injective _ hinj, Finset.card_range]

private theorem computableInPolyTime_addDisjointClique :
    ComputableInPolyTime (fun p : Graph × ℕ => addDisjointClique p.1 p.2)
      (encPair encGraph encUnary) encGraph := by
  have h2bin : ComputableInPolyTime (fun v : ℕ => 2 * v) encNat encNat :=
    binary_mul' (const 2) id'
  have hodd : ComputableInPolyTime (fun i : ℕ => 2 * i + 1) encUnary encNat :=
    unary_to_binary.comp (unary_add' (unary_mul' (const 2) id') (const 1))
  have hGvs : ComputableInPolyTime (fun p : Graph × ℕ => p.1.distinctVertices.map fun v => 2 * v)
      (encPair encGraph encUnary) (encList encNat) :=
    (map h2bin).comp (Graph.computableInPolyTime_distinctVertices.comp (fst encGraph encUnary))
  have hKvs : ComputableInPolyTime (fun p : Graph × ℕ => (List.range p.2).map fun i => 2 * i + 1)
      (encPair encGraph encUnary) (encList encNat) :=
    (map hodd).comp (range.comp (snd encGraph encUnary))
  have hverts : ComputableInPolyTime (fun p : Graph × ℕ => (addDisjointClique p.1 p.2).vertices)
      (encPair encGraph encUnary) (encList encNat) :=
    (listAppend encNat).comp (hGvs.prod hKvs)
  have hGe : ComputableInPolyTime (fun p : Graph × ℕ => p.1.edges.map fun e => (2 * e.1, 2 * e.2))
      (encPair encGraph encUnary) (encList (encPair encNat encNat)) :=
    (map ((h2bin.comp (fst encNat encNat)).prod (h2bin.comp (snd encNat encNat)))).comp
      ((encGraph_edges_polyTime .id').comp (fst encGraph encUnary))
  have hKe_inner : ComputableInPolyTime
      (fun q : (Graph × ℕ) × ℕ =>
        ((List.range (Prod.snd q.1)).filter fun j => decide (q.2 ≠ j)).map fun j =>
          (2 * q.2 + 1, 2 * j + 1))
      (encPair (encPair encGraph encUnary) encUnary) (encList (encPair encNat encNat)) := by
    have hr : ComputableInPolyTime (fun q : (Graph × ℕ) × ℕ => List.range (Prod.snd q.1))
        (encPair (encPair encGraph encUnary) encUnary) (encList encUnary) :=
      range.comp ((snd encGraph encUnary).comp (fst _ _))
    have hne : ComputableInPolyTime
        (fun s : ((Graph × ℕ) × ℕ) × ℕ => decide (Prod.snd s.1 ≠ s.2))
        (encPair (encPair (encPair encGraph encUnary) encUnary) encUnary) encBool :=
      (bool_not.comp (decide_eq' ((snd _ _).comp (fst _ _)) (snd _ _))).of_enc_eq fun s =>
        congrArg encBool (by simp)
    have hfilt := filterWithInput (test := fun (q : (Graph × ℕ) × ℕ) (j : ℕ) => decide (q.2 ≠ j))
      hr hne
    refine mapWithInput (encA := encUnary) hfilt ?_
    exact (hodd.comp ((snd _ _).comp (fst _ _))).prod (hodd.comp (snd _ _))
  have hKe : ComputableInPolyTime
      (fun p : Graph × ℕ =>
        (List.range p.2).flatMap fun i =>
          ((List.range p.2).filter fun j => decide (i ≠ j)).map fun j =>
            (2 * i + 1, 2 * j + 1))
      (encPair encGraph encUnary) (encList (encPair encNat encNat)) :=
    flatMapWithInput (range.comp (snd encGraph encUnary)) hKe_inner
  have hedges : ComputableInPolyTime (fun p : Graph × ℕ => (addDisjointClique p.1 p.2).edges)
      (encPair encGraph encUnary) (encList (encPair encNat encNat)) :=
    (listAppend (encPair encNat encNat)).comp (hGe.prod hKe)
  exact encGraph_mk_polyTime hverts hedges

/-! #### Reduction 1: `Clique ≤ₚ SymGameHasESS` (Theorem 29.8, NP-hardness) -/

/-- Polynomial-time many-one reduction from `Clique` to `SymGameHasESS`. When `2 ≤ k ≤ |V(G)|`,
it forms `G ⊔ K_{k-1}` (of size at most `2 |V(G)|`, using `min |V(G)| k - 1` in unary) and applies
Nisan's reduction with threshold `k - 1`. -/
private def cliqueToSymGameHasESS (x : CliqueInstance) : BimatrixCode :=
  let n := x.graph.distinctVertices.length
  if x.m = 0 then yesGameCode
  else if x.m = 1 then if n = 0 then noGameCode else yesGameCode
  else if n < x.m then noGameCode
  else nisanGameCode (addDisjointClique x.graph (min n x.m - 1)) (x.m - 1)

private theorem cliqueToSymGameHasESS_mem_iff (x : CliqueInstance) :
    x ∈ Clique ↔ cliqueToSymGameHasESS x ∈ SymGameHasESS := by
  rcases x with ⟨G, k⟩
  dsimp only [cliqueToSymGameHasESS]
  set n := G.distinctVertices.length
  have hn_card : n = G.vertices.toFinset.card := Graph.length_distinctVertices G
  by_cases hk0 : k = 0
  · subst hk0
    simp only [↓reduceIte]
    exact iff_of_true (Graph.le_cliqueNum_iff.1 (Nat.zero_le _)) yesGameCode_mem_SymGameHasESS
  · simp only [hk0, ↓reduceIte]
    by_cases hk1 : k = 1
    · subst hk1
      simp only [↓reduceIte]
      by_cases hn0 : n = 0
      · simp only [hn0, ↓reduceIte]
        have hnot : (⟨G, 1⟩ : CliqueInstance) ∉ Clique := fun h => by
          have := Graph.le_card_of_mem_Clique h; omega
        exact iff_of_false hnot noGameCode_notMem_SymGameHasESS
      · simp only [hn0, ↓reduceIte]
        have hne : G.distinctVertices ≠ [] := fun h => hn0 (by simp [n, h])
        obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil _ hne
        have hin : (⟨G, 1⟩ : CliqueInstance) ∈ Clique :=
          mem_Clique_iff.2 ⟨{v}, fun u hu => by
            rw [Finset.mem_singleton] at hu; exact hu ▸ Graph.mem_distinctVertices.1 hv, by simp⟩
        exact iff_of_true hin yesGameCode_mem_SymGameHasESS
    · simp only [hk1, ↓reduceIte]
      by_cases hlt : n < k
      · simp only [hlt, ↓reduceIte]
        have hnot : (⟨G, k⟩ : CliqueInstance) ∉ Clique := fun h => by
          have := Graph.le_card_of_mem_Clique h; omega
        exact iff_of_false hnot noGameCode_notMem_SymGameHasESS
      · simp only [hlt, ↓reduceIte]
        have hmin : min n k = k := min_eq_right (Nat.le_of_not_lt hlt)
        rw [hmin, nisanGameCode_mem_SymGameHasESS_iff _ (by omega : 0 < k - 1),
          cliqueNum_addDisjointClique, ← Graph.le_cliqueNum_iff]
        omega

private theorem computableInPolyTime_cliqueDistinctLen :
    ComputableInPolyTime (fun x : CliqueInstance => x.graph.distinctVertices.length)
      encCliqueInstance encUnary :=
  (length_list encNat).comp
    (Graph.computableInPolyTime_distinctVertices.comp (encCliqueInstance_graph_polyTime .id'))

private theorem computableInPolyTime_cliqueToSymGameHasESS :
    ComputableInPolyTime cliqueToSymGameHasESS encCliqueInstance encBimatrix := by
  have hg := encCliqueInstance_graph_polyTime .id'
  have hm := encCliqueInstance_m_polyTime .id'
  have h1 := computableInPolyTime_cliqueDistinctLen
  have h2 := binary_lt' (unary_to_binary.comp h1) hm
  have h3 := unary_sub' (binary_min_unary' h1 hm) (const 1)
  have h4 := computableInPolyTime_nisanGameCode.comp
    ((computableInPolyTime_addDisjointClique.comp (hg.prod h3)).prod
      (binary_sub' hm (const 1)))
  have hite := ite' (decide_eq' hm (const 0)) (const yesGameCode)
    (ite' (decide_eq' hm (const 1))
      (ite' (decide_eq' h1 (const 0)) (const noGameCode) (const yesGameCode))
      (ite' h2 (const noGameCode) h4))
  exact hite.of_enc_eq fun x => congrArg encBimatrix <| by
    dsimp only [cliqueToSymGameHasESS, Function.comp_apply]
    by_cases h0 : x.m = 0
    · simp only [h0, ↓reduceIte, decide_true]
    · simp only [h0, ↓reduceIte, decide_false, Bool.false_eq_true]
      by_cases h1' : x.m = 1
      · simp only [h1', ↓reduceIte, decide_true]
        by_cases hn0 : x.graph.distinctVertices.length = 0
        · simp only [hn0, ↓reduceIte, decide_true]
        · simp only [hn0, ↓reduceIte, decide_false, Bool.false_eq_true]
      · simp only [h1', ↓reduceIte, decide_false, Bool.false_eq_true]
        by_cases hlt : x.graph.distinctVertices.length < x.m
        · simp only [hlt, ↓reduceIte, decide_true]
        · simp only [hlt, ↓reduceIte, decide_false, Bool.false_eq_true]

/-- Polynomial-time many-one reduction `Clique ≤ₚ SymGameHasESS`. -/
theorem polyTimeReducible_Clique_SymGameHasESS :
    PolyTimeReducible encCliqueInstance encBimatrix Clique SymGameHasESS :=
  ⟨cliqueToSymGameHasESS, computableInPolyTime_cliqueToSymGameHasESS,
    cliqueToSymGameHasESS_mem_iff⟩

/-- **Deciding whether a symmetric rational two-player game has an ESS is `NP`-hard**
([Suri2007], Theorem 29.8, p. 723, `NP`-hardness half). -/
theorem SymGameHasESS_npHard : NPHard encBimatrix SymGameHasESS :=
  Clique_npHard.trans polyTimeReducible_Clique_SymGameHasESS

/-! #### Reduction 2: `UNSAT ≤ₚ SymGameHasESS` (Theorem 29.8, coNP-hardness) -/

/-- Polynomial-time many-one reduction from `UNSAT` to `SymGameHasESS`: for a nonempty CNF formula
`φ`, apply Nisan's game to the complement of Karp's independent-set graph `(SAT.toIndependentSet φ)`
with target `φ.length`. Since that graph's clique number is always at most `φ.length` and equals
`φ.length` iff `φ ∈ SAT`, it differs from `φ.length` iff `φ ∈ UNSAT`. -/
private def unsatToSymGameHasESS (φ : CNF ℕ) : BimatrixCode :=
  let inst := SAT.toIndependentSet φ
  if inst.m = 0 then noGameCode else nisanGameCode inst.graph.compl inst.m

private theorem unsatToSymGameHasESS_mem_iff (φ : CNF ℕ) :
    φ ∈ UNSAT ↔ unsatToSymGameHasESS φ ∈ SymGameHasESS := by
  dsimp only [unsatToSymGameHasESS]
  have hm : (SAT.toIndependentSet φ).m = φ.length := rfl
  rw [hm]
  by_cases h0 : φ.length = 0
  · simp only [h0, ↓reduceIte]
    have hsat : φ ∈ SAT := by
      have hnil : φ = [] := List.eq_nil_of_length_eq_zero h0
      subst hnil
      exact ⟨fun _ => false, rfl⟩
    exact iff_of_false (fun h => h hsat) noGameCode_notMem_SymGameHasESS
  · simp only [h0, ↓reduceIte]
    have hpos : 0 < φ.length := Nat.pos_of_ne_zero h0
    rw [nisanGameCode_mem_SymGameHasESS_iff _ hpos, Graph.cliqueNum_compl]
    have hle_len : (SAT.toIndependentSet φ).graph.indepNum ≤ φ.length := by
      obtain ⟨σ, hσ⟩ := (SAT.le_indepNum_toIndependentSet_iff φ _).1 le_rfl
      omega
    have heq_iff : (SAT.toIndependentSet φ).graph.indepNum = φ.length ↔ φ ∈ SAT := by
      constructor
      · intro h
        exact (SAT.toIndependentSet_mem_iff φ).1
          (by simpa [SAT.toIndependentSet] using Graph.le_indepNum_iff.1 h.ge)
      · intro hsat
        have hge : φ.length ≤ (SAT.toIndependentSet φ).graph.indepNum :=
          Graph.le_indepNum_iff.2 (by simpa [SAT.toIndependentSet] using
            (SAT.toIndependentSet_mem_iff φ).2 hsat)
        omega
    change ¬ φ.Satisfiable ↔ _
    exact (not_congr heq_iff).symm

private theorem computableInPolyTime_unsatToSymGameHasESS :
    ComputableInPolyTime unsatToSymGameHasESS encCNF encBimatrix := by
  have hinst := SAT.computableInPolyTime_toIndependentSet
  have hm : ComputableInPolyTime (fun φ : CNF ℕ => (SAT.toIndependentSet φ).m) encCNF encNat :=
    encIndependentSetInstance_m_polyTime hinst
  have hg : ComputableInPolyTime (fun φ : CNF ℕ => (SAT.toIndependentSet φ).graph.compl)
      encCNF encGraph :=
    Graph.computableInPolyTime_compl.comp (encIndependentSetInstance_graph_polyTime hinst)
  have hite := ite' (decide_eq' hm (const 0)) (const noGameCode)
    (computableInPolyTime_nisanGameCode.comp (hg.prod hm))
  exact hite.of_enc_eq fun φ => congrArg encBimatrix (by simp [unsatToSymGameHasESS])

/-- Polynomial-time many-one reduction `UNSAT ≤ₚ SymGameHasESS`. -/
theorem polyTimeReducible_UNSAT_SymGameHasESS :
    PolyTimeReducible encCNF encBimatrix UNSAT SymGameHasESS :=
  ⟨unsatToSymGameHasESS, computableInPolyTime_unsatToSymGameHasESS, unsatToSymGameHasESS_mem_iff⟩

/-- **Deciding whether a symmetric rational two-player game has an ESS is `coNP`-hard**
([Suri2007], Theorem 29.8, p. 723, `coNP`-hardness half). -/
theorem SymGameHasESS_coNPHard : coNPHard encBimatrix SymGameHasESS :=
  CookLevin.UNSAT_coNPComplete.2.trans polyTimeReducible_UNSAT_SymGameHasESS

/-! #### Reduction 3: `Cliqueᶜ ≤ₚ SymGameIsESS` (Theorem 29.9, coNP-hardness) -/

/-- Polynomial-time many-one reduction from `Cliqueᶜ` to `SymGameIsESS`. -/
private def cliqueComplToSymGameIsESS (x : CliqueInstance) : SymGameStrategyInstance :=
  if x.m = 0 then ⟨noGameCode, [1, 0]⟩
  else ⟨nisanGameCode x.graph x.m, (1 : ℚ) :: List.replicate x.graph.distinctVertices.length 0⟩

private theorem cliqueComplToSymGameIsESS_mem_iff (x : CliqueInstance) :
    x ∈ Cliqueᶜ ↔ cliqueComplToSymGameIsESS x ∈ SymGameIsESS := by
  rcases x with ⟨G, k⟩
  dsimp only [cliqueComplToSymGameIsESS]
  by_cases hk0 : k = 0
  · subst hk0
    simp only [↓reduceIte]
    exact iff_of_false (not_not.2 (Graph.le_cliqueNum_iff.1 (Nat.zero_le _)))
      noGameStrategy_notMem_SymGameIsESS
  · simp only [hk0, ↓reduceIte]
    rw [nisanGameCode_pureZero_mem_SymGameIsESS_iff G (Nat.pos_of_ne_zero hk0),
      Set.mem_compl_iff, ← Graph.le_cliqueNum_iff, not_le]

private theorem computableInPolyTime_cliqueComplToSymGameIsESS :
    ComputableInPolyTime cliqueComplToSymGameIsESS encCliqueInstance
      encSymGameStrategyInstance := by
  have hg := encCliqueInstance_graph_polyTime .id'
  have hm := encCliqueInstance_m_polyTime .id'
  have hgame := computableInPolyTime_nisanGameCode.comp (hg.prod hm)
  have hstrat :=
    (ComputableInPolyTime.cons encRat).comp
      ((const (1 : ℚ)).prod (replicate computableInPolyTime_cliqueDistinctLen (const (0 : ℚ))))
  have hite := ite' (decide_eq' hm (const 0))
    (const (⟨noGameCode, [1, 0]⟩ : SymGameStrategyInstance))
    (encSymGameStrategyInstance_mk_polyTime hgame hstrat)
  exact hite.of_enc_eq fun x => congrArg encSymGameStrategyInstance <| by
    dsimp only [cliqueComplToSymGameIsESS, Function.comp_apply]
    by_cases h0 : x.m = 0
    · simp only [h0, ↓reduceIte, decide_true]
    · simp only [h0, ↓reduceIte, decide_false, Bool.false_eq_true]

/-- Polynomial-time many-one reduction `Cliqueᶜ ≤ₚ SymGameIsESS`. -/
theorem polyTimeReducible_Clique_compl_SymGameIsESS :
    PolyTimeReducible encCliqueInstance encSymGameStrategyInstance Cliqueᶜ SymGameIsESS :=
  ⟨cliqueComplToSymGameIsESS, computableInPolyTime_cliqueComplToSymGameIsESS,
    cliqueComplToSymGameIsESS_mem_iff⟩

/-- **Deciding whether a given rational strategy is an ESS of a symmetric rational two-player game
is `coNP`-hard** ([Suri2007], Theorem 29.9, p. 723). -/
theorem SymGameIsESS_coNPHard : coNPHard encSymGameStrategyInstance SymGameIsESS :=
  Clique_npHard.compl.trans polyTimeReducible_Clique_compl_SymGameIsESS

end BimatrixCode

end Cslib.GameTheory
