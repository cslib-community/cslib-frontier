/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.Initial
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Dealing.ScriptSize
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Dealing.Tables
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.GroupProgram.Time
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.Laws
public import CslibFrontier.Foundations.GroupTheory.SLTower.Tower
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cutting.Pieces
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.FinalTables
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.InitialCounts
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.Start
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.BaseChange
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Trees.Existence
import CslibFrontier.Foundations.Data.Nat.Power

/-!
# The pieces of a computation

Proposition J.2 of [AnthropicVPVNP2026] (p. 52): for a tape automaton `mu` over `R` and a scale
`v`, the value of the automaton in `K * T` steps is a sum of products of the values of at most
`k Λ` pieces, `Λ = (lg v) ^ C`, and a program computes the pieces. `Cutting.ComputationPieces`
records the data of the proposition for `K` blocks of `T` steps and the cut by `k`: the units, the
moves of the relay and the laws with the plan of their outcomes, the pieces of the parties and the
straight-line program (`Dealing.SlpTab`) that computes them and what each table does, and

* the value of the automaton as a sum of products of the values of the pieces
  (`ComputationPieces.value`);
* at most `k Λ` pieces, each with at most `C K / k` base parties, at most `K T Λ / v ^ 300` bits
  in units with exactly one holder in it, and at most `K T Λ / k` bits that its parties ever hold
  and its roles read, for good outcomes and valid numbers of initial units;
* numbers, digits and steps of the program below `v ^ C`.

`Cutting.exists_computationPieces` is the proposition, for the laws of Theorem G.2 at the vertices
of the tower of `U_h` with `1 + 8 C₁ ≤ h / 4`, over every algebra and for every injective code of
the symbols: there are `a` and `e ≥ 300` such that for every automaton there are `C` and `v₀` with
`K = v ^ e` for `v ≥ v₀`, for all `T ≥ v ^ a` and `2 ≤ k ≤ v ^ 64`. The proof (p. 53) takes the
thin trees of Theorem H.2 (`Trees.exists_thinTrees`) for `M = 2 K` nodes, units of
`⌊T / v ^ a'⌋` bits and the bound of Lemma I.2 for the units of a base party, and their pieces
(`Trees.ThinTrees.piece`). The value of the automaton is that of Lemma I.2
(`Cut.runVal_eq_sum_value_initial`), the value of thin trees (`Trees.ThinTrees.value`) and the
regrouping of the parties into the pieces (`Play.value_groups`); numbers of initial units that give
a base party more than `load` units contribute nothing (`Cut.sum_count_le_of_initialTable_ne_zero`).

## Main definitions

* `Cutting.ComputationPieces`: the pieces of a computation.

## Main results

* `Cutting.exists_computationPieces`: Proposition J.2.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Proposition J.2 (p. 52) and its proof (p. 53); module `Paper.Pieces`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Cutting

open Finset Cut Interpreter Dealing GroupProgram TowerPlan Trees

variable {R : Type} [CommRing R] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S]
  [DecidableEq S] [Fintype Q] [DecidableEq Q]

/-- **The pieces of a computation** (Proposition J.2 of [AnthropicVPVNP2026], p. 52) of the tape
automaton `mu` whose symbols are coded by `cb`, at the scale `v`, for `K` blocks of `T` steps and
the cut by `k`, with the moves of the relay and the laws `laws`, the bound `b` and the integer `G`
of the test of the law moves, and the exponent `C` (`Λ = lg v ^ C`). Units have `ub ≤ T` bits, at
most `load` units start at a base party, and the moves `moves` on the `K + K` base parties and
`A'` more parties have a plan `plan` that obeys the rules. The parties are divided into `num`
pieces by `piece`, which a program `program` over the numbers below `D` with `steps` steps
computes with what each table does, and which checks that the numbers of initial units are
valid: at most `load` units at every base party. -/
structure ComputationPieces (laws : List (Law R)) (mu : Tape.Letter S Unit Γ → Matrix Q Q R)
    {c : ℕ} (cb : Option Γ → BitString c) (b G v K T k C : ℕ) where
  /-- The bits of a unit. -/
  ub : ℕ
  ub_pos : 0 < ub
  ub_le : ub ≤ T
  /-- The bound for the units at a base party at the beginning. -/
  load : ℕ
  load_mul_ub_le : load * ub ≤ T * lg v ^ C
  /-- The number of parties that are not base parties. -/
  A' : ℕ
  /-- The number of moves. -/
  E : ℕ
  /-- The outcomes are below `U1`. -/
  U1 : ℕ
  /-- The moves. -/
  moves : Moves R (K + K + A') E
  /-- The plan: the units given in the moves, their numbers, and the good outcomes. -/
  plan : Plan moves load U1
  [decidableGood : ∀ n o x, Decidable (plan.Good n o x)]
  /-- The bound for the units of a move. -/
  cap : ℕ
  /-- The plan obeys the rules. -/
  ok : plan.Ok cap
  /-- The law moves; the other moves are relays. -/
  isLaw : Fin E → Bool
  law_mem : ∀ x, isLaw x = true → moves.law x ∈ laws
  law_eq_relay : ∀ x, isLaw x = false → moves.law x = relayLaw R
  /-- The good outcomes, as in Theorem H.2. -/
  good_iff : ∀ n o x, plan.Good n o x ↔ if isLaw x then
      b * ∑ ν, (o ⟨x, ν⟩ : ℕ) ^ 2 ≤ G * plan.count n o x ^ 2 ∧ ∀ ν, plan.count n o x ≤ o ⟨x, ν⟩
    else ∀ ν, (o ⟨x, ν⟩ : ℕ) = plan.count n o x
  /-- Every possible outcome is good. -/
  good_of_possible : ∀ n o x, plan.Possible n o ub x → plan.Good n o x
  /-- The number of pieces. -/
  num : ℕ
  /-- The piece of a party, for the numbers of initial units and the outcomes. -/
  piece : PlanInput moves load U1 → Fin (K + K + A') → Fin num
  /-- The numbers of the program are below `D`. -/
  D : ℕ
  /-- The number of inputs of the program. -/
  nI : ℕ
  /-- The number of steps of the program. -/
  steps : ℕ
  /-- The program of the pieces. -/
  program : SlpTab plan piece D nI steps
  valid_iff : ∀ n, program.Valid n ↔ ∀ p, ∑ a, ((n p a : ℕ) + n a p) ≤ load
  /-- The value of the automaton in `K * T` steps on a word `u` of at most `K * ℓ` letters,
  `ℓ ≤ T`: the sum, over the states between the blocks, the valid row data, the numbers of
  initial units that give every base party at most `load` units, the good outcomes and the
  contents of the units whose holders are in different pieces, of the product of the values of
  the pieces. -/
  value : ∀ (i e : Q) (u : Unit → List Γ) (ℓ : ℕ), ℓ ≤ T → (u ()).length ≤ K * ℓ →
    Tape.runVal mu i e (K * T) u = ∑ q : Fin (K + 1) → Q, if q 0 = i ∧ q (Fin.last K) = e then
      ∑ ρ : Option S → Fin (K + K) → RowData (K + K), if ValidRows ρ then
        ∑ n : Fin (K + K) → Fin (K + K) → Fin (load + 1),
          if ∀ p, ∑ a, ((n p a : ℕ) + n a p) ≤ load then
            ∑ o : moves.Channel → Fin U1, if ∀ x, plan.Good n o x then
              ∑ y ∈ Play.common (none : UnitContent ub) (Play.cutUnits
                  (UnitId.holder moves.channelParty) (piece ⟨n, o⟩) (plan.cur n o E)),
                ∏ g, plan.groupValue mu T cb q (parts ℓ (u ())) ρ n o (piece ⟨n, o⟩) g y
            else 0
          else 0
        else 0
      else 0
  /-- At most `k Λ` pieces. -/
  num_le : num ≤ k * lg v ^ C
  /-- At most `C K / k` base parties in a piece. -/
  card_base_le : ∀ n o, program.Valid n → (∀ x, plan.Good n o x) → ∀ g,
    #{p : Fin (K + K) | piece ⟨n, o⟩ (Fin.castAdd A' p) = g} * k ≤ C * K
  /-- At most `K T Λ / v ^ 300` bits in the units with exactly one holder in a piece. -/
  card_oneIn_le : ∀ n o, program.Valid n → (∀ x, plan.Good n o x) → ∀ g,
    #((plan.cur n o E).filter (OneIn (UnitId.holder moves.channelParty) (piece ⟨n, o⟩) g)) * ub *
      v ^ 300 ≤ K * T * lg v ^ C
  /-- At most `K T Λ / k` bits that the parties of a piece ever hold and that its roles read. -/
  count_le : ∀ n o, program.Valid n → (∀ x, plan.Good n o x) → ∀ g,
    (cellCount n o (piece ⟨n, o⟩) g + roleUnitCount plan n o (piece ⟨n, o⟩) g) * ub * k ≤
      K * T * lg v ^ C
  load_lt_D : load < D
  U1_le_D : U1 ≤ D
  num_le_D : num ≤ D
  one_lt_D : 1 < D
  D_le : D ≤ v ^ C
  steps_le : steps ≤ v ^ C
  parties_le : K + K + A' ≤ v ^ C
  moves_le : E ≤ v ^ C
  load_le : load ≤ v ^ C
  U1_le : U1 ≤ v ^ C
  card_channel_le : Fintype.card moves.Channel ≤ v ^ C

attribute [instance] ComputationPieces.decidableGood

/-- The gain of the root: units at one node against all units, if `w ^ q ≤ M` and
`γ = 1 / log₂ 2 ^ q`. -/
private theorem mul_le_of_le_rpow {M N Λ q w X : ℕ} (hq : 0 < q) (hM : 0 < M) (hw : w ^ q ≤ M)
    (hX : (X : ℝ) ≤ (Λ : ℕ) * (M : ℝ) ^ (1 - 1 / Real.logb 2 ((2 ^ q : ℕ) : ℝ)) *
      (N + (M : ℝ) ^ 2)) : X * w ≤ Λ * M * (N + M ^ 2) := by
  have e : Real.logb 2 ((2 ^ q : ℕ) : ℝ) = q := by
    push_cast
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
  rw [e] at hX
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have h1 : (w : ℝ) ≤ (M : ℝ) ^ (1 / (q : ℝ)) := by
    have := Real.rpow_le_rpow (by positivity) (show (w : ℝ) ^ q ≤ M by exact_mod_cast hw)
      (show (0 : ℝ) ≤ (q : ℝ)⁻¹ by positivity)
    rwa [Real.pow_rpow_inv_natCast (Nat.cast_nonneg w) hq.ne', ← one_div] at this
  have : ((X * w : ℕ) : ℝ) ≤ ((Λ * M * (N + M ^ 2) : ℕ) : ℝ) := by
    push_cast
    calc (X : ℝ) * w ≤ Λ * (M : ℝ) ^ (1 - 1 / (q : ℝ)) * (N + (M : ℝ) ^ 2) *
          (M : ℝ) ^ (1 / (q : ℝ)) := mul_le_mul hX h1 (by positivity) (by positivity)
      _ = Λ * M * (N + (M : ℝ) ^ 2) := by
          rw [mul_right_comm, mul_assoc (Λ : ℝ), ← Real.rpow_add hM0, sub_add_cancel,
            Real.rpow_one]
  exact_mod_cast this

/-- **The pieces of a computation** (Proposition J.2 of [AnthropicVPVNP2026], p. 52, and its
proof, p. 53). For laws at the vertices of the tower of `U_h` (Theorem G.2) whose contraction
satisfies `1 + 8 C₁ ≤ h / 4` there are `a` and `e ≥ 300` such that for every algebra `R` over
their ring, every tape automaton `mu` over `R` and every injective code `cb` of its symbols by
`c > 0` bits there are `C` and `v₀`, and for every `v ≥ v₀` a `K` with `v ^ e ≤ K ≤ C v ^ e`, such
that for all `T ≥ v ^ a` and `2 ≤ k ≤ v ^ 64` the computation has pieces
(`ComputationPieces`) with the laws mapped to `R`, the bound `2 ^ e(h)` and the integer
`lengthBound` of the test of the law moves. The proposition also asks `lg T ≤ (lg v) ^ 2`, which
is not needed, and takes `K = v ^ e`. -/
theorem exists_computationPieces {A₀ : Type*} [CommSemiring A₀] {h : ℕ} [NeZero h] (h3 : 3 ≤ h)
    (FL : VertexLaws A₀ (SLTower.tower h 0 (by omega)))
    (hgain : 1 + 8 * FL.contraction ≤ (h : ℝ) / 4) :
    ∃ a e : ℕ, 300 ≤ e ∧ ∀ (R : Type) [CommRing R] [Algebra A₀ R] (Γ S Q : Type) [Fintype Γ]
      [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q]
      (mu : Tape.Letter S Unit Γ → Matrix Q Q R) {c : ℕ} (cb : Option Γ → BitString c),
      Function.Injective cb → 0 < c →
      ∃ C v₀ : ℕ, ∀ v, v₀ ≤ v → ∃ K, v ^ e ≤ K ∧ K ≤ C * v ^ e ∧ ∀ T k, v ^ a ≤ T → 2 ≤ k →
        k ≤ v ^ 64 → Nonempty (ComputationPieces
          (((univ : Finset FL.Kind).toList.map FL.law).map fun L => L.map (algebraMap A₀ R)) mu
          cb (2 ^ SLTower.ee h) FL.lengthBound v K T k C) := by
  obtain ⟨C₀, htree⟩ := exists_thinTrees h3 FL hgain
  set q := SLTower.ee h
  have hq : 0 < q := by
    simp only [q, SLTower.ee]
    have : 3 * 2 ≤ h * (h - 1) := Nat.mul_le_mul h3 (by omega)
    omega
  obtain ⟨e, he⟩ : ∃ e, e = 300 * q + 64 := ⟨_, rfl⟩
  obtain ⟨a', ha'⟩ : ∃ a', a' = (e + 2) * (C₀ + 2) + 300 := ⟨_, rfl⟩
  obtain ⟨bY, hbY⟩ : ∃ bY, bY = (e + a' + 2) * (C₀ + 2) := ⟨_, rfl⟩
  have he2 : 2 * (e + 1) ≤ a' := by
    have := Nat.mul_le_mul_left (e + 2) (show 2 ≤ C₀ + 2 by omega)
    omega
  have he3 : (e + 1) * C₀ + 300 ≤ a' := by
    have := Nat.mul_le_mul (show e + 1 ≤ e + 2 by omega) (show C₀ ≤ C₀ + 2 by omega)
    omega
  have hbY' : (e + a' + 2) * C₀ + 2 * (e + 1) + (a' + 1) + 64 ≤ bY := by
    have := Nat.mul_add (e + a' + 2) C₀ 2
    omega
  refine ⟨a' + e + 3, e, by omega, fun R _ _ Γ S Q _ _ _ _ _ _ mu c cb hcb hc => ?_⟩
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = Fintype.card S + 1 := ⟨_, rfl⟩
  obtain ⟨Ee, hEe'⟩ : ∃ Ee, Ee = (e + 1) ^ C₀ := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = (C₀ + 1) * ((4 * c + 5) * Ee) := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W, W = 10 * (2 ^ q + 1) * P := ⟨_, rfl⟩
  have hEe : 1 ≤ Ee := hEe' ▸ Nat.one_le_pow _ _ (by omega)
  have h2q : 1 ≤ 2 ^ q := Nat.one_le_two_pow
  have hPC : C₀ + 1 ≤ P := hP ▸ Nat.le_mul_of_pos_right _ (Nat.mul_pos (by omega) hEe)
  have hPE : Ee ≤ P := hP ▸ (Nat.le_mul_of_pos_left Ee (by omega)).trans
    (Nat.le_mul_of_pos_left _ (by omega))
  have hPc : 4 * c + 5 ≤ P := hP ▸ (Nat.le_mul_of_pos_right _ hEe).trans
    (Nat.le_mul_of_pos_left _ (by omega))
  have hP2 : P = C₀ * ((4 * c + 5) * Ee) + (4 * c + 5) * Ee := by rw [hP, add_one_mul]
  have hP3 := Nat.mul_le_mul_right Ee (show 4 * c + 4 ≤ 4 * c + 5 by omega)
  have hW8 : 8 * P + 2 * C₀ ≤ W ∧ 1 + C₀ + 2 ^ q * Ee ≤ W := by
    rw [hW]
    constructor <;> nlinarith [Nat.mul_le_mul_right P h2q, Nat.mul_le_mul_left (2 ^ q) hPE]
  refine ⟨W + C₀ + 15 * bY, 8 * c + σ + C₀ + 2 ^ q + 16, fun v hv => ⟨v ^ e, le_rfl,
    Nat.le_mul_of_pos_left _ (by omega), fun T k hT hk hkv => ?_⟩⟩
  obtain ⟨K, hKe⟩ : ∃ K, K = v ^ e := ⟨_, rfl⟩
  rw [← hKe]
  have vp {x y : ℕ} (hxy : x ≤ y) : v ^ x ≤ v ^ y := Nat.pow_le_pow_right (by omega) hxy
  have hK : 0 < K := hKe ▸ Nat.pow_pos (by omega)
  have hMv : K + K ≤ v ^ (e + 1) := by
    rw [pow_succ, ← hKe, ← Nat.mul_two]
    exact Nat.mul_le_mul_left K (by omega)
  have hkv' : k ≤ v ^ 300 := hkv.trans (vp (by omega))
  have hkK : k ≤ K := hkv'.trans (hKe ▸ vp (by omega))
  -- the units: `ub` bits, at most `load` at a base party
  obtain ⟨ub, hubd⟩ : ∃ ub, ub = T / v ^ a' := ⟨_, rfl⟩
  obtain ⟨load, hloadd⟩ : ∃ l, l = 2 * ((T + (K + K) * σ) * c / ub + (K + K)) := ⟨_, rfl⟩
  have hva : 0 < v ^ a' := Nat.pow_pos (by omega)
  have hub : 0 < ub := hubd ▸ Nat.div_pos ((vp (by omega)).trans hT) hva
  have hubT : ub * v ^ a' ≤ T := hubd ▸ Nat.div_mul_le_self _ _
  have hTub : T < (ub + 1) * v ^ a' := by
    rw [hubd, add_mul, one_mul]
    exact Nat.lt_div_mul_add hva
  have hmul {d : ℕ} (hd : d ≤ a') : v ^ d * ub ≤ T :=
    (Nat.mul_comm _ _).le.trans ((Nat.mul_le_mul_left ub (vp hd)).trans hubT)
  have hM2 : (K + K) ^ 2 * ub ≤ T := (Nat.mul_le_mul_right ub ((Nat.pow_le_pow_left hMv 2).trans_eq
    (pow_mul v (e + 1) 2).symm)).trans (hmul (by omega))
  have hMub : (K + K) * ub ≤ T :=
    (Nat.mul_le_mul_right ub (Nat.le_self_pow (by norm_num) _)).trans hM2
  have hdead : (K + K) ^ C₀ * v ^ 300 * ub ≤ T := by
    refine (Nat.mul_le_mul_right ub (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hMv C₀))).trans ?_
    rw [← pow_mul, ← pow_add]
    exact hmul he3
  have hσT : (K + K) * σ ≤ T := (Nat.mul_le_mul hMv (show σ ≤ v by omega)).trans
    ((pow_succ v (e + 1)).symm.le.trans ((vp (by omega)).trans hT))
  have hload : load * ub ≤ (4 * c + 4) * T := by
    have h1 := Nat.div_mul_le_self ((T + (K + K) * σ) * c) ub
    have h2 : (T + (K + K) * σ) * c ≤ 2 * T * c := Nat.mul_le_mul_right c (by omega)
    have e1 : load * ub = 2 * ((T + (K + K) * σ) * c / ub * ub) + 2 * ((K + K) * ub) := by
      rw [hloadd]; ring
    have e2 : (4 * c + 4) * T = 2 * (2 * T * c) + 4 * T := by ring
    omega
  have hloadv : load ≤ v ^ (a' + 1) := by
    have h1 : (T + (K + K) * σ) * c / ub ≤ 4 * c * v ^ a' := by
      refine Nat.div_le_of_le_mul ((Nat.mul_le_mul_right c (show T + (K + K) * σ ≤ 2 * T by
        omega)).trans ?_)
      calc 2 * T * c ≤ 2 * ((ub + ub) * v ^ a') * c := Nat.mul_le_mul_right c
            (Nat.mul_le_mul_left 2 (hTub.le.trans (Nat.mul_le_mul_right _ (by omega))))
        _ = ub * (4 * c * v ^ a') := by ring
    have h2 := hMv.trans (vp (show e + 1 ≤ a' by omega))
    calc load ≤ 2 * (4 * c * v ^ a' + v ^ a') := by rw [hloadd]; omega
      _ = (8 * c + 2) * v ^ a' := by ring
      _ ≤ v * v ^ a' := Nat.mul_le_mul_right _ (by omega)
      _ = v ^ (a' + 1) := (pow_succ' v a').symm
  have hload1 : 1 ≤ load :=
    hloadd ▸ Nat.mul_pos two_pos (Nat.add_pos_right _ (Nat.add_pos_left hK K))
  -- the thin trees and their program
  obtain ⟨TT⟩ := htree R (K + K) (K + K) load ub (by omega) le_rfl hload1 hub
  have hMN : ((K + K) * load) ^ C₀ ≤ v ^ ((e + a' + 2) * C₀) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left ((Nat.mul_le_mul hMv hloadv).trans (by
      rw [← pow_add]; exact vp (by omega))) C₀
  have hMNY : ((K + K) * load) ^ C₀ ≤ v ^ bY := hMN.trans (vp (by omega))
  have hdepth : TT.depth ≤ v ^ bY := TT.depth_le.trans ((Nat.pow_le_pow_left
    ((Nat.succ_le_of_lt (Nat.log_lt_self 2 (by omega))).trans (Nat.le_mul_of_pos_right _
      hload1)) C₀).trans hMNY)
  have hchan : Fintype.card TT.moves.Channel ≤ ((K + K) * load) ^ C₀ :=
    (Fintype.card_le_of_injective (fun ν => (.new ν ⟨0, TT.U1_pos⟩ : UnitId (K + K) load
      TT.moves.Channel TT.U1)) fun _ _ h => by cases h; rfl).trans TT.card_unit_le
  have hin : (K + K) * (K + K) + Fintype.card TT.moves.Channel ≤ v ^ bY := by
    set Z := (e + a' + 2) * C₀ + 2 * (e + 1)
    have h1 : (K + K) * (K + K) ≤ v ^ Z :=
      (Nat.mul_le_mul hMv hMv).trans (by rw [← pow_add]; exact vp (by omega))
    have h2 := hchan.trans (hMN.trans (vp (show _ ≤ Z by omega)))
    calc _ ≤ v ^ Z * v := by
          have := Nat.mul_le_mul_left (v ^ Z) (show 2 ≤ v by omega)
          omega
      _ = v ^ (Z + 1) := (pow_succ _ _).symm
      _ ≤ v ^ bY := vp (by omega)
  have hk0 : 0 < k := by omega
  obtain ⟨nI, pS, tab, hpS, hvalid⟩ := TT.exists_slpTab hk0 (Y := v ^ bY)
    ((by omega : 6 ≤ v).trans (Nat.le_self_pow (by omega) v)) hMNY (hloadv.trans (vp (by omega)))
    hdepth hin
  -- the bounds of the pieces, with `Λ = lg v ^ (W + C₀ + 15 * bY)`
  have hL2 : 2 ≤ lg v := lg_ge_two (by omega)
  have hlgK : lg (K + K) ^ C₀ ≤ Ee * lg v ^ C₀ := by
    rw [hEe', ← mul_pow]
    exact Nat.pow_le_pow_left ((lg_mono hMv).trans (lg_pow_le (by omega))) C₀
  have hLC {x : ℕ} (hx : x ≤ W) : x * lg v ^ C₀ ≤ lg v ^ (W + C₀ + 15 * bY) :=
    Nat.mul_pow_le_pow_of_add_le hL2 (by omega)
  have hL1 : 1 ≤ lg v ^ C₀ := Nat.one_le_pow _ _ (by omega)
  have hYh : lg (K + K) ^ C₀ * (K + K) * (load + (K + K) ^ 2) * ub ≤
      2 * (4 * c + 5) * Ee * lg v ^ C₀ * (K * T) :=
    calc _ = lg (K + K) ^ C₀ * (K + K) * (load * ub + (K + K) ^ 2 * ub) := by ring
      _ ≤ Ee * lg v ^ C₀ * (K + K) * ((4 * c + 4) * T + T) := by gcongr
      _ = _ := by ring
  have hw (X : ℕ) (hX : (X : ℝ) ≤ (lg (K + K) ^ C₀ : ℕ) * ((K + K : ℕ) : ℝ) ^
      (1 - 1 / Real.logb 2 ((2 ^ q : ℕ) : ℝ)) * (load + ((K + K : ℕ) : ℝ) ^ 2)) :
      X * v ^ 300 ≤ lg (K + K) ^ C₀ * (K + K) * (load + (K + K) ^ 2) :=
    have : (v ^ 300) ^ q ≤ K + K := by
      rw [← pow_mul, hKe]
      exact (vp (by omega)).trans (Nat.le_add_right _ _)
    mul_le_of_le_rpow hq (by omega) this hX
  have hvY : v ≤ v ^ bY := Nat.le_self_pow (by omega) v
  have hY4 : v ^ bY < (v ^ bY) ^ 4 :=
    lt_of_eq_of_lt (pow_one _).symm (Nat.pow_lt_pow_right (by omega) (by norm_num))
  have hC (x : ℕ) (hx : x ≤ 15 * bY) : v ^ x ≤ v ^ (W + C₀ + 15 * bY) := vp (by omega)
  refine ⟨{
    ub := ub, ub_pos := hub, ub_le := (Nat.le_mul_of_pos_right ub hva).trans hubT, load := load,
    load_mul_ub_le := ?_, A' := TT.A', E := TT.E, U1 := TT.U1, moves := TT.moves, plan := TT.plan,
    cap := TT.cap, ok := TT.ok, isLaw := TT.isLaw, law_mem := TT.law_mem,
    law_eq_relay := TT.law_eq_relay, good_iff := TT.good_iff,
    good_of_possible := TT.good_of_possible, num := TT.pieceCount k,
    piece := fun x => TT.piece hk0 x.counts x.outcomes, D := (v ^ bY) ^ 4, nI := nI, steps := pS,
    program := tab, valid_iff := hvalid, value := ?_, num_le := ?_, card_base_le := ?_,
    card_oneIn_le := ?_, count_le := ?_, load_lt_D := ?_, U1_le_D := ?_, num_le_D := ?_,
    one_lt_D := ?_, D_le := ?_, steps_le := ?_, parties_le := ?_, moves_le := ?_, load_le := ?_,
    U1_le := ?_, card_channel_le := ?_ }⟩
  · rw [Nat.mul_comm T]
    exact hload.trans (Nat.mul_le_mul_right T ((Nat.le_mul_of_pos_right _ hL1).trans
      (hLC (by omega))))
  · -- Lemma I.2, then Theorem H.2 and the pieces as groups; too many units give nothing
    intro i e u ℓ hℓ hu
    have hU : (T + (Fintype.card S + 1)) * c / ub + 1 ≤ load := by
      have := Nat.div_le_div_right (c := ub) (Nat.mul_le_mul_right c (Nat.add_le_add_left
        (Nat.le_mul_of_pos_left σ (by omega : 0 < K + K)) T))
      rw [hloadd, ← hσ]
      omega
    rw [runVal_eq_sum_value_initial (U1 := TT.U1) hcb hc hub hU TT.moves.channelParty i e u hℓ hu]
    refine sum_congr rfl fun q _ => ite_congr rfl (fun _ => sum_congr rfl fun ρ _ =>
      ite_congr rfl (fun _ => sum_congr rfl fun n _ => ?_) fun _ => rfl) fun _ => rfl
    split_ifs with hn
    · rw [show (fun y : Fin (K + K + TT.A') → _ => ∏ p : Fin (K + K),
          initialTable mu T cb q (parts ℓ (u ())) (fun s => ρ s p) (fun a b => n a b) p
            (y (Fin.castAdd TT.A' p))) =
          fun y => ∏ a, initialTables mu T cb TT.A' q (parts ℓ (u ())) ρ n a (y a) from
        funext fun y => by simp [initialTables, Fin.prod_univ_add],
        TT.value n _ (fun a y y' h => ?_) fun a y h => initialTables_ne_none h]
      · exact sum_congr rfl fun o _ =>
          ite_congr rfl (fun _ => Play.value_groups _ _ _ _ _ _) fun _ => rfl
      · induction a using Fin.addCases with
        | left p =>
          simp only [initialTables, Fin.addCases_left]
          exact initialTable_congr h
        | right p => simp only [initialTables, Fin.addCases_right]
    · push Not at hn
      obtain ⟨p, hp⟩ := hn
      rw [Play.value_eq_sum_filter]
      refine sum_eq_zero fun y _ => prod_eq_zero (mem_univ p) (of_not_not fun h0 => hp.not_ge ?_)
      exact (sum_count_le_of_initialTable_ne_zero (fun κ => (length_parts_le _ _ _).trans hℓ)
        h0).trans (by rw [hloadd, hσ])
  · calc TT.pieceCount k = 1 + C₀ + 2 ^ q * (TT.depth * k) := rfl
      _ ≤ (1 + C₀) * (k * lg v ^ C₀) + 2 ^ q * (Ee * lg v ^ C₀ * k) :=
          Nat.add_le_add (Nat.le_mul_of_pos_right _ (Nat.mul_pos hk0 hL1))
            (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right k (TT.depth_le.trans hlgK)))
      _ = k * ((1 + C₀ + 2 ^ q * Ee) * lg v ^ C₀) := by ring
      _ ≤ _ := Nat.mul_le_mul_left k (hLC hW8.2)
  · refine fun n o hn hg g => (TT.card_base_piece_le hk0 (by omega) (by omega) g).trans ?_
    rw [show 4 * (K + K) = 8 * K by ring]
    exact Nat.mul_le_mul_right K (by omega)
  · intro n o hn hg g
    have hT1 : T ≤ lg v ^ C₀ * (K * T) :=
      (Nat.le_mul_of_pos_left T hK).trans (Nat.le_mul_of_pos_left _ hL1)
    rw [Nat.mul_right_comm]
    refine (Nat.mul_le_mul_right ub (TT.card_oneIn_piece_le hk0 ((hvalid n).1 hn) hg hw g)).trans ?_
    rw [add_mul]
    refine (Nat.add_le_add hYh (hdead.trans hT1)).trans ?_
    have hc' : 2 * ((4 * c + 5) * Ee) + 1 ≤ W := by omega
    calc _ = (2 * ((4 * c + 5) * Ee) + 1) * lg v ^ C₀ * (K * T) := by ring
      _ ≤ lg v ^ (W + C₀ + 15 * bY) * (K * T) := Nat.mul_le_mul_right _ (hLC hc')
      _ = _ := by ring
  · intro n o hn hg g
    have hT1 : T ≤ lg v ^ C₀ * (K * T) :=
      (Nat.le_mul_of_pos_left T hK).trans (Nat.le_mul_of_pos_left _ hL1)
    have h2 : (K + K) ^ C₀ * k * ub ≤ T :=
      (Nat.mul_le_mul_right ub (Nat.mul_le_mul_left _ hkv')).trans hdead
    rw [Nat.mul_right_comm]
    refine (Nat.mul_le_mul_right ub (TT.cellCount_add_roleUnitCount_le hk0 (by omega) (by omega)
      ((hvalid n).1 hn) hg hkv' hw g)).trans ?_
    have hc' : 8 * (C₀ * ((4 * c + 5) * Ee)) + 8 * ((4 * c + 4) * Ee) + 2 * C₀ ≤ W := by omega
    calc _ = 4 * C₀ * (lg (K + K) ^ C₀ * (K + K) * (load + (K + K) ^ 2) * ub) +
          8 * K * lg (K + K) ^ C₀ * (load * ub) + 2 * C₀ * ((K + K) ^ C₀ * k * ub) := by ring
      _ ≤ 4 * C₀ * (2 * (4 * c + 5) * Ee * lg v ^ C₀ * (K * T)) +
          8 * K * (Ee * lg v ^ C₀) * ((4 * c + 4) * T) + 2 * C₀ * (lg v ^ C₀ * (K * T)) :=
        Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ hYh)
          (Nat.mul_le_mul (Nat.mul_le_mul_left _ hlgK) hload))
          (Nat.mul_le_mul_left _ (h2.trans hT1))
      _ = (8 * (C₀ * ((4 * c + 5) * Ee)) + 8 * ((4 * c + 4) * Ee) + 2 * C₀) * lg v ^ C₀ *
          (K * T) := by ring
      _ ≤ lg v ^ (W + C₀ + 15 * bY) * (K * T) := Nat.mul_le_mul_right _ (hLC hc')
      _ = _ := by ring
  -- the numbers and the program
  · exact (hloadv.trans (vp (by omega))).trans_lt hY4
  · exact (TT.U1_le.trans hMNY).trans hY4.le
  · have hk' : k ≤ v ^ bY := hkv.trans (vp (by omega))
    generalize v ^ bY = Y at hvY hY4 hdepth hk'
    calc 1 + C₀ + 2 ^ q * (TT.depth * k) ≤ Y + Y * (Y * Y) :=
          Nat.add_le_add (by omega) (Nat.mul_le_mul (by omega) (Nat.mul_le_mul hdepth hk'))
      _ ≤ 2 * (Y * (Y * Y)) := by
          have : Y ≤ Y * (Y * Y) := Nat.le_mul_of_pos_right Y (Nat.mul_pos (by omega) (by omega))
          omega
      _ ≤ Y * (Y * (Y * Y)) := Nat.mul_le_mul_right _ (by omega)
      _ = Y ^ 4 := by ring
  · exact (by omega : 1 < v ^ bY).trans hY4
  · exact (pow_mul v bY 4).symm.le.trans (hC _ (by omega))
  · exact hpS.trans ((pow_mul v bY 15).symm.le.trans (hC _ (by omega)))
  · exact TT.parties_le.trans (hMN.trans (hC _ (by omega)))
  · exact TT.moves_le.trans (hMN.trans (hC _ (by omega)))
  · exact hloadv.trans (hC _ (by omega))
  · exact TT.U1_le.trans (hMN.trans (hC _ (by omega)))
  · exact hchan.trans (hMN.trans (hC _ (by omega)))

end Cslib.Circuits.Arithmetic.Separation.Cutting
