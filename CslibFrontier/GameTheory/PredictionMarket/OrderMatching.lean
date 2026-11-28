/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Problems.SAT
public import CslibFrontier.Computability.Complexity.Reduction
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Rat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import Mathlib.Basic.Real.Basic
import CslibFrontier.Computability.Complexity.Classes.NP.Witness
import CslibFrontier.Computability.Complexity.CookLevin.Completeness
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary.Decode
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Foundations.LinearAlgebra.Matrix.BasicSolution
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Farkas
import CslibFrontier.Logics.Propositional.CNF.PolyTime
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.GetD
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Compound Prediction Market Order Matching and `coNP`-Completeness

This module formalizes compound conditional securities, indivisible and divisible order matching,
the linear-programming and small-support Farkas dual characterizations, and the native
`coNP`-completeness of divisible compound order matching from
[PennockSami2007, §26.3–§26.3.1, pp. 658–661].

## Model and conventions

Base events are indexed by natural numbers (`ℕ`), so a state of the world is a Boolean assignment
`ω : ℕ → Bool`. Following the library's canonical SAT representation (`Cslib.Logic.PL.CNF ℕ`,
`Cslib.Complexity.encCNF`), each conditional security `S_{φ|ψ}` in a `CompoundOrder` specifies
an event formula `φ : CNF ℕ` and a conditioning formula `ψ : CNF ℕ` (with `[] : CNF ℕ` representing
the unconditional tautology `⊤`), together with rational quantity `q : ℚ` (`q > 0` for a buy order,
`q < 0` for a sell order) and rational unit limit price `p : ℚ`.

* **Order payoff** (`orderPayoff`, §26.3.1.1, p. 659):
  `ϒ(ω) = q * 1_{ω ∈ ψ} * (1_{ω ∈ φ} - p)`.
* **Auctioneer surplus** (`auctioneerPayoff`, §26.3.1.2, p. 659):
  for acceptance fractions `α : Fin O.length → ℝ`,
  `ϒ_auc(ω) = ∑ i, -(α i) * orderPayoff O[i] ω`.
* **Indivisible and divisible matching** (`HasIndivisibleMatch`, Definition 26.3, p. 659;
  `HasDivisibleMatch`, Definition 26.5, p. 660): whether there exist acceptance fractions `α`
  in `{0, 1}` (resp. `[0, 1]`) with at least one `α i > 0` and `∀ ω, 0 ≤ auctioneerPayoff O α ω`.

## Theorem 26.6(i) and Theorem 26.6(ii)

* **Theorem 26.6(i) LP equivalence** (`hasDivisibleMatch_iff_exists_pos_sum`,
  `hasDivisibleMatch_iff_exists_unit_sum`): `HasDivisibleMatch O` holds iff the finite-variable
  linear program `0 ≤ α i ≤ 1`, `∀ ω, 0 ≤ auctioneerPayoff O α ω` admits a solution with strictly
  positive objective `0 < ∑ i, α i` (equivalently `0 ≤ α`, `∑ i, α i = 1`, `∀ ω, ...`), where only
  assignments to the base variables occurring in `O` matter. Polynomial-time LP solving on Turing
  machines (for `O(log n)` base events) is not formalized here (open under `#7789`).
* **Small-support Farkas / Carathéodory characterization**
  (`not_hasDivisibleMatch_iff_exists_small_farkas`,
  `not_hasDivisibleMatch_iff_exists_small_subset`): by Farkas' lemma
  (`Matrix.not_exists_mulVec_le_iff`) and basic solutions
  (`Matrix.exists_nonneg_mulVec_eq_forall_mulVec_eq_zero`), `¬ HasDivisibleMatch O` holds iff there
  exists a set `S` of **at most `O.length`** states (a fortiori `≤ O.length + 1`,
  [PennockSami2007, p. 661]) admitting a nonnegative rational Farkas dual certificate
  `w : (ℕ → Bool) → ℚ` with `∀ i, 0 < ∑ ω ∈ S, w ω * orderPayoff O[i] ω` (and equivalently
  `¬ HasDivisibleMatchOn O S`).
* **Theorem 26.6(ii) native `coNP`-completeness** (`DivisibleOrderMatching_coNPComplete`):
  - **Upper bound (`DivisibleOrderMatching_mem_coNP`)**: clearing rational denominators order by
    order and applying `Matrix.exists_int_nonneg_mulVec_eq` yields a polynomial-bit-size integer
    Farkas certificate on at most `O.length` states, verified natively in polynomial time on
    multi-tape Turing machines via `Cslib.Complexity.mem_NP_of_check`.
  - **Lower bound (`DivisibleOrderMatching_coNPHard`)**: the single-order polynomial-time
    reduction `φ ↦ [⟨1, 1 / 2, φ, []⟩]` reduces `UNSAT` to `DivisibleOrderMatching`
    [PennockSami2007, p. 661].

## Main definitions

* `Cslib.GameTheory.PredictionMarket.CompoundOrder`,
  `Cslib.GameTheory.PredictionMarket.encCompoundOrder`,
  `Cslib.GameTheory.PredictionMarket.encOrderList`: compound conditional orders and their
  multi-tape TM binary encoding.
* `Cslib.GameTheory.PredictionMarket.orderPayoff`,
  `Cslib.GameTheory.PredictionMarket.auctioneerPayoff`: trader payoff and auctioneer surplus.
* `Cslib.GameTheory.PredictionMarket.HasIndivisibleMatch`,
  `Cslib.GameTheory.PredictionMarket.HasDivisibleMatch`,
  `Cslib.GameTheory.PredictionMarket.HasDivisibleMatchOn`,
  `Cslib.GameTheory.PredictionMarket.DivisibleOrderMatching`: indivisible and divisible matching
  decision problems [PennockSami2007, Definitions 26.3 and 26.5, pp. 659–660].

## Main results

* `Cslib.GameTheory.PredictionMarket.hasDivisibleMatch_of_hasIndivisibleMatch`: every indivisible
  match is a divisible match.
* `Cslib.GameTheory.PredictionMarket.hasDivisibleMatch_iff_exists_pos_sum`,
  `Cslib.GameTheory.PredictionMarket.hasDivisibleMatch_iff_exists_unit_sum`: LP objective and
  simplex-normalized feasibility characterizations [PennockSami2007, Theorem 26.6(i), pp. 660–661].
* `Cslib.GameTheory.PredictionMarket.not_hasDivisibleMatch_iff_exists_small_farkas`,
  `Cslib.GameTheory.PredictionMarket.not_hasDivisibleMatch_iff_exists_small_subset`: at most
  `O.length` (hence `≤ O.length + 1`) states certify infeasibility via a rational Farkas dual
  [PennockSami2007, Theorem 26.6(ii), p. 661].
* `Cslib.GameTheory.PredictionMarket.polyTimeReducible_UNSAT_DivisibleOrderMatching`,
  `Cslib.GameTheory.PredictionMarket.DivisibleOrderMatching_coNPHard`,
  `Cslib.GameTheory.PredictionMarket.DivisibleOrderMatching_mem_coNP`,
  `Cslib.GameTheory.PredictionMarket.DivisibleOrderMatching_coNPComplete`: native
  `coNP`-completeness of divisible compound order matching
  [PennockSami2007, Theorem 26.6(ii), pp. 660–661].

## References

* [D. M. Pennock, R. Sami, *Computational Aspects of Prediction Markets*, Chapter 26 of
  *Algorithmic Game Theory*, §26.3–§26.3.1, pp. 658–661][PennockSami2007]
-/

public section

open Finset Matrix Cslib.Logic.PL Cslib.Complexity Turing.MultiTapeTM ComputableInPolyTime

namespace Cslib.GameTheory.PredictionMarket

/-! ### Compound conditional orders and payoffs (§26.3.1.1–26.3.1.2, pp. 659–660) -/

/-- A compound conditional order "`quantity` units of security `S_{event | condition}` at unit
limit price `price`" [PennockSami2007, §26.3.1.1, p. 659]. Positive `quantity` represents a buy
order and negative `quantity` represents a sell order; `condition = []` represents the
unconditional tautology `⊤`. -/
@[ext]
structure CompoundOrder where
  /-- Signed order quantity `q` (`q > 0` buy, `q < 0` sell). -/
  quantity : ℚ
  /-- Unit limit price `p`. -/
  price : ℚ
  /-- Event formula `φ` paying `$1` when satisfied under `condition`. -/
  event : CNF ℕ
  /-- Conditioning formula `ψ` (the order is cancelled and refunded if `ψ` is false). -/
  condition : CNF ℕ
  deriving DecidableEq, Repr

/-- Framed `encRat` (quantity), framed `encRat` (price), framed `encCNF` (event), and `encCNF`
(condition), encoding `CompoundOrder`. -/
enc_structure encCompoundOrder : CompoundOrder where
  quantity : encRat,
  price : encRat,
  event : encCNF,
  condition : encCNF

attribute [fun_prop] encCompoundOrder_quantity_polyTime encCompoundOrder_price_polyTime
  encCompoundOrder_event_polyTime encCompoundOrder_condition_polyTime encCompoundOrder_mk_polyTime

/-- Encoded list of compound orders: `encList encCompoundOrder`. -/
abbrev encOrderList : List CompoundOrder ↪ List Bool :=
  encList encCompoundOrder

/-- Trader payoff `ϒ^ω = q · 1_{ω ∈ ψ} · (1_{ω ∈ φ} - p)` of compound order `o` in state `ω`
[PennockSami2007, §26.3.1.1, p. 659]. -/
@[expose] noncomputable def orderPayoff (o : CompoundOrder) (ω : ℕ → Bool) : ℝ :=
  if o.condition.eval ω then
    (o.quantity : ℝ) * ((if o.event.eval ω then (1 : ℝ) else 0) - (o.price : ℝ))
  else 0

/-- Auctioneer payoff (surplus) `ϒ_auc^ω = ∑ i, -(α i) * ϒ_i^ω` under acceptance vector `α` in
state `ω` [PennockSami2007, §26.3.1.2, p. 659]. -/
@[expose] noncomputable def auctioneerPayoff (O : List CompoundOrder) (α : Fin O.length → ℝ)
    (ω : ℕ → Bool) : ℝ :=
  ∑ i : Fin O.length, -(α i) * orderPayoff O[i] ω

/-- **Indivisible matching problem** [PennockSami2007, Definition 26.3, p. 659]: there exist
`α_i ∈ {0, 1}`, not all zero, such that the auctioneer never loses money in any state `ω`. -/
@[expose] def HasIndivisibleMatch (O : List CompoundOrder) : Prop :=
  ∃ α : Fin O.length → ℝ, (∀ i, α i = 0 ∨ α i = 1) ∧ (∃ i, α i = 1) ∧
    ∀ ω : ℕ → Bool, 0 ≤ auctioneerPayoff O α ω

/-- **Divisible matching problem** [PennockSami2007, Definition 26.5, p. 660]: there exist
`α_i ∈ [0, 1]`, not all zero, such that the auctioneer never loses money in any state `ω`. -/
@[expose] def HasDivisibleMatch (O : List CompoundOrder) : Prop :=
  ∃ α : Fin O.length → ℝ, (∀ i, 0 ≤ α i ∧ α i ≤ 1) ∧ (∃ i, 0 < α i) ∧
    ∀ ω : ℕ → Bool, 0 ≤ auctioneerPayoff O α ω

/-- Divisible matching restricted to a finite set `S` of states: the auctioneer breaks even on
every state `ω ∈ S`. -/
@[expose] def HasDivisibleMatchOn (O : List CompoundOrder) (S : Finset (ℕ → Bool)) : Prop :=
  ∃ α : Fin O.length → ℝ, (∀ i, 0 ≤ α i ∧ α i ≤ 1) ∧ (∃ i, 0 < α i) ∧
    ∀ ω ∈ S, 0 ≤ auctioneerPayoff O α ω

/-- Decision problem **Divisible Compound Order Matching**
[PennockSami2007, Definition 26.5 & Theorem 26.6, pp. 660–661]: lists of compound orders admitting
a divisible match. -/
@[expose] def DivisibleOrderMatching : Set (List CompoundOrder) :=
  {O | HasDivisibleMatch O}

/-- Every indivisible match is in particular a divisible match. -/
theorem hasDivisibleMatch_of_hasIndivisibleMatch {O : List CompoundOrder}
    (h : HasIndivisibleMatch O) : HasDivisibleMatch O := by
  obtain ⟨α, h01, ⟨i₀, hi₀⟩, hpay⟩ := h
  refine ⟨α, fun i => ?_, ⟨i₀, by linarith⟩, hpay⟩
  rcases h01 i with h0 | h1 <;> constructor <;> linarith

/-! ### Linear-programming characterizations (Theorem 26.6(i), pp. 660–661) -/

/-- **LP objective equivalence** [PennockSami2007, Theorem 26.6(i) proof, pp. 660–661]:
`HasDivisibleMatch O` holds if and only if the linear program `0 ≤ α i ≤ 1`,
`∀ ω, 0 ≤ auctioneerPayoff O α ω` attains a strictly positive total volume `0 < ∑ i, α i`. -/
theorem hasDivisibleMatch_iff_exists_pos_sum (O : List CompoundOrder) :
    HasDivisibleMatch O ↔
      ∃ α : Fin O.length → ℝ, (∀ i, 0 ≤ α i ∧ α i ≤ 1) ∧
        (∀ ω : ℕ → Bool, 0 ≤ auctioneerPayoff O α ω) ∧ 0 < ∑ i, α i := by
  constructor
  · rintro ⟨α, hbounds, ⟨i₀, hi₀⟩, hpay⟩
    exact ⟨α, hbounds, hpay, sum_pos' (fun i _ => (hbounds i).1) ⟨i₀, mem_univ i₀, hi₀⟩⟩
  · rintro ⟨α, hbounds, hpay, hpos⟩
    obtain ⟨i₀, -, hi₀⟩ := (sum_pos_iff_of_nonneg fun i _ => (hbounds i).1).mp hpos
    exact ⟨α, hbounds, ⟨i₀, hi₀⟩, hpay⟩

/-- **Simplex-normalized LP feasibility equivalence**: by homogeneity of `auctioneerPayoff`,
`HasDivisibleMatch O` holds if and only if there exists a probability vector `α ≥ 0` with
`∑ i, α i = 1` and `∀ ω, 0 ≤ auctioneerPayoff O α ω`. -/
theorem hasDivisibleMatch_iff_exists_unit_sum (O : List CompoundOrder) :
    HasDivisibleMatch O ↔
      ∃ α : Fin O.length → ℝ, (∀ i, 0 ≤ α i) ∧ ∑ i, α i = 1 ∧
        ∀ ω : ℕ → Bool, 0 ≤ auctioneerPayoff O α ω := by
  rw [hasDivisibleMatch_iff_exists_pos_sum]
  constructor
  · rintro ⟨α, hbounds, hpay, hpos⟩
    set S : ℝ := ∑ i, α i
    refine ⟨fun i => α i / S, fun i => div_nonneg (hbounds i).1 hpos.le, ?_, fun ω => ?_⟩
    · rw [← sum_div, div_self hpos.ne']
    · have hscale : auctioneerPayoff O (fun i => α i / S) ω = auctioneerPayoff O α ω / S := by
        simp only [auctioneerPayoff, sum_div]
        exact sum_congr rfl fun i _ => by ring
      rw [hscale]
      exact div_nonneg (hpay ω) hpos.le
  · rintro ⟨α, hnn, hsum, hpay⟩
    refine ⟨α, fun i => ⟨hnn i, ?_⟩, hpay, by linarith⟩
    exact (single_le_sum (fun j _ => hnn j) (mem_univ i)).trans_eq hsum

/-! ### Finite-variable projection, Farkas duality, and small integer certificates -/

/-- All variable occurrences across all event and conditioning formulas of `O`. -/
private def orderVars (O : List CompoundOrder) : List ℕ :=
  O.flatMap fun o => o.event.vars ++ o.condition.vars

/-- Assignment described by a certificate bit-list `bits` along the variable occurrences
`orderVars O` (analogous to `SAT.assignment`). -/
private def orderAssignment (O : List CompoundOrder) (bits : List Bool) (v : ℕ) : Bool :=
  bits.getD ((orderVars O).idxOf v) false

/-- Integer-scaled trader payoff `(q.den * p.den) * orderPayoff o ω`, avoiding rational division
during certificate verification. -/
private def intOrderPayoff (o : CompoundOrder) (ω : ℕ → Bool) : ℤ :=
  if o.condition.eval ω then
    o.quantity.num * ((if o.event.eval ω then (o.price.den : ℤ) else 0) - o.price.num)
  else 0

private theorem intOrderPayoff_cast_eq (o : CompoundOrder) (ω : ℕ → Bool) :
    (intOrderPayoff o ω : ℝ) =
      (o.quantity.den : ℝ) * (o.price.den : ℝ) * orderPayoff o ω := by
  have hqd : (o.quantity.den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr o.quantity.den_nz
  have hpd : (o.price.den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr o.price.den_nz
  have hq : (o.quantity : ℝ) = (o.quantity.num : ℝ) / (o.quantity.den : ℝ) := by
    exact_mod_cast (Rat.num_div_den o.quantity).symm
  have hp : (o.price : ℝ) = (o.price.num : ℝ) / (o.price.den : ℝ) := by
    exact_mod_cast (Rat.num_div_den o.price).symm
  simp only [intOrderPayoff, orderPayoff]
  split_ifs with hc he
  · push_cast
    rw [hq, hp]
    field_simp [hqd, hpd]
  · push_cast
    rw [hq, hp]
    field_simp [hqd, hpd]
    ring
  · simp

private theorem orderPayoff_congr {o : CompoundOrder} {ω₁ ω₂ : ℕ → Bool}
    (h : ∀ v ∈ o.event.vars ++ o.condition.vars, ω₁ v = ω₂ v) :
    orderPayoff o ω₁ = orderPayoff o ω₂ := by
  have he : o.event.eval ω₁ = o.event.eval ω₂ :=
    CNF.eval_congr fun v hv => h v (List.mem_append_left _ hv)
  have hc : o.condition.eval ω₁ = o.condition.eval ω₂ :=
    CNF.eval_congr fun v hv => h v (List.mem_append_right _ hv)
  simp only [orderPayoff, he, hc]

private theorem orderAssignment_vars_map (O : List CompoundOrder) (ω : ℕ → Bool) {v : ℕ}
    (hv : v ∈ orderVars O) :
    orderAssignment O ((orderVars O).map ω) v = ω v := by
  simp [orderAssignment, List.getD_eq_getElem?_getD, List.idxOf_lt_length_iff.mpr hv]

/-- Assignment corresponding to a finite Boolean table `s : Fin (orderVars O).length → Bool`. -/
private def evalState (O : List CompoundOrder) (s : Fin (orderVars O).length → Bool) :
    ℕ → Bool :=
  orderAssignment O (List.ofFn s)

private theorem exists_evalState_eq_orderPayoff (O : List CompoundOrder) (ω : ℕ → Bool) :
    ∃ s : Fin (orderVars O).length → Bool,
      ∀ o ∈ O, orderPayoff o (evalState O s) = orderPayoff o ω := by
  refine ⟨fun k => ω (orderVars O)[k.1], fun o ho => ?_⟩
  have hofFn : List.ofFn (fun k : Fin (orderVars O).length => ω (orderVars O)[k.1]) =
      (orderVars O).map ω := by
    apply List.ext_getElem (by simp)
    intro i hi _
    simp
  refine orderPayoff_congr fun v hv => ?_
  have hvO : v ∈ orderVars O := List.mem_flatMap.mpr ⟨o, ho, hv⟩
  rw [evalState, hofFn, orderAssignment_vars_map O ω hvO]

private theorem length_orderVars_le (O : List CompoundOrder) :
    (orderVars O).length ≤ (encOrderList O).length := by
  have h1 : (orderVars O).length =
      (O.map fun o => o.event.vars.length + o.condition.vars.length).sum := by
    simp only [orderVars, List.length_flatMap, List.length_append]
  rw [h1]
  refine (List.sum_le_sum fun o _ => ?_).trans (sum_length_le_length_encList encCompoundOrder O)
  have he := SAT.length_vars_le o.event
  have hc := SAT.length_vars_le o.condition
  have hord : (encCompoundOrder o).length =
      2 * (encRat o.quantity).length + 1 +
        (2 * (encRat o.price).length + 1 +
          (2 * (encCNF o.event).length + 1 + (encCNF o.condition).length)) := by
    simp only [encCompoundOrder_apply, length_encPair]
  omega

private theorem abs_intOrderPayoff_le {O : List CompoundOrder} {o : CompoundOrder} (ho : o ∈ O)
    (ω : ℕ → Bool) :
    |intOrderPayoff o ω| ≤ ((2 ^ (2 * (encOrderList O).length + 1) : ℕ) : ℤ) := by
  set L := (encOrderList O).length
  have ho_le : (encCompoundOrder o).length ≤ L :=
    length_le_encList_of_mem encCompoundOrder ho
  have hq_len : (encRat o.quantity).length ≤ L :=
    (encCompoundOrder_quantity_length_le o).trans ho_le
  have hp_len : (encRat o.price).length ≤ L :=
    (encCompoundOrder_price_length_le o).trans ho_le
  have hq_num : o.quantity.num.natAbs ≤ 2 ^ L :=
    (natAbs_num_lt_two_pow_length_encRat o.quantity).le.trans
      (Nat.pow_le_pow_right (by decide) hq_len)
  have hp_num : o.price.num.natAbs ≤ 2 ^ L :=
    (natAbs_num_lt_two_pow_length_encRat o.price).le.trans
      (Nat.pow_le_pow_right (by decide) hp_len)
  have hp_den : o.price.den ≤ 2 ^ L :=
    (den_lt_two_pow_length_encRat o.price).le.trans
      (Nat.pow_le_pow_right (by decide) hp_len)
  have hq_abs : |o.quantity.num| ≤ ((2 ^ L : ℕ) : ℤ) := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast hq_num
  have hp_abs : |o.price.num| ≤ ((2 ^ L : ℕ) : ℤ) := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast hp_num
  have hpd_abs : (o.price.den : ℤ) ≤ ((2 ^ L : ℕ) : ℤ) := by exact_mod_cast hp_den
  have hdiff : |((if o.event.eval ω then (o.price.den : ℤ) else 0) - o.price.num)| ≤
      2 * ((2 ^ L : ℕ) : ℤ) := by
    split_ifs
    · exact (abs_sub _ _).trans (by rw [abs_of_nonneg (Nat.cast_nonneg _)]; linarith)
    · rw [zero_sub, abs_neg]; linarith
  by_cases hc : o.condition.eval ω = true
  · simp only [intOrderPayoff, hc, ↓reduceIte, abs_mul]
    have hmul := mul_le_mul hq_abs hdiff (abs_nonneg _) (Nat.cast_nonneg _)
    have hpow : ((2 ^ L : ℕ) : ℤ) * (2 * ((2 ^ L : ℕ) : ℤ)) =
        ((2 ^ (2 * L + 1) : ℕ) : ℤ) := by
      push_cast
      rw [show 2 * L + 1 = L + L + 1 by omega, pow_succ, pow_add]
      ring
    linarith
  · simp only [intOrderPayoff, ite_eq_right hc, abs_zero]
    exact Nat.cast_nonneg _

/-- Core small-support integer Farkas certificate extraction: if `¬ HasDivisibleMatch O`, then
there exists a subset `T` of at most `O.length` finite-variable assignments together with
nonnegative integer weights `p : T → ℤ` bounded by `2 ^ ((5 * L + 3) * (4 * L))` (where
`L = (encOrderList O).length`) certifying
`∀ i, 0 < ∑ s ∈ T, p s * intOrderPayoff O[i] (evalState O s)`. -/
private theorem exists_small_int_farkas (O : List CompoundOrder) (hno : ¬ HasDivisibleMatch O) :
    ∃ (T : Finset (Fin (orderVars O).length → Bool))
      (w : (Fin (orderVars O).length → Bool) → ℤ),
      T.card ≤ O.length ∧
      (∀ s ∈ T, 0 ≤ w s ∧
        w s ≤ ((2 ^ ((5 * (encOrderList O).length + 3) * (4 * (encOrderList O).length)) : ℕ) : ℤ)) ∧
      ∀ i : Fin O.length, 0 < ∑ s ∈ T, w s * intOrderPayoff O[i] (evalState O s) := by
  classical
  set N := (orderVars O).length
  set m := O.length
  set L := (encOrderList O).length
  -- Step 1: Farkas' lemma on the finite state space `Fin N → Bool`.
  let U : Matrix (Fin N → Bool) (Fin m) ℝ :=
    Matrix.of fun s i => orderPayoff O[i] (evalState O s)
  let A : Matrix ((Fin N → Bool) ⊕ Fin m ⊕ Unit) (Fin m) ℝ :=
    Matrix.of fun r i =>
      match r with
      | .inl s => U s i
      | .inr (.inl j) => if j = i then -1 else 0
      | .inr (.inr ()) => -1
  let b : (Fin N → Bool) ⊕ Fin m ⊕ Unit → ℝ :=
    Sum.elim 0 (Sum.elim 0 (fun _ => -1))
  have hsys_infeas : ¬ ∃ α : Fin m → ℝ, A *ᵥ α ≤ b := by
    rintro ⟨α, hα⟩
    apply hno
    have hnn : ∀ i : Fin m, 0 ≤ α i := fun i => by
      have h := hα (.inr (.inl i))
      simp only [A, b, mulVec, dotProduct, Matrix.of_apply, Sum.elim_inr, Sum.elim_inl,
        Pi.zero_apply, ite_mul, neg_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
        ↓reduceIte] at h
      linarith
    have hsum1 : 1 ≤ ∑ i : Fin m, α i := by
      have h := hα (.inr (.inr ()))
      simp only [A, b, mulVec, dotProduct, Matrix.of_apply, Sum.elim_inr, neg_mul, one_mul,
        Finset.sum_neg_distrib] at h
      linarith
    have hsum_pos : 0 < ∑ i : Fin m, α i := by linarith
    rw [hasDivisibleMatch_iff_exists_unit_sum]
    refine ⟨fun i => α i / ∑ j, α j, fun i => div_nonneg (hnn i) hsum_pos.le,
      by rw [← sum_div, div_self hsum_pos.ne'], fun ω => ?_⟩
    obtain ⟨s, hs⟩ := exists_evalState_eq_orderPayoff O ω
    have hU : (U *ᵥ α) s ≤ 0 := by
      simpa only [A, b, mulVec, dotProduct, Matrix.of_apply, Sum.elim_inl, Pi.zero_apply] using
        hα (.inl s)
    have hpay : auctioneerPayoff O (fun i => α i / ∑ j, α j) ω = -((U *ᵥ α) s) / ∑ j, α j := by
      simp only [auctioneerPayoff, U, mulVec, dotProduct, Matrix.of_apply, neg_div,
        ← Finset.sum_neg_distrib, sum_div]
      refine sum_congr rfl fun i _ => ?_
      rw [← hs O[i] (List.getElem_mem i.2)]
      ring
    rw [hpay]
    exact div_nonneg (neg_nonneg.mpr hU) hsum_pos.le
  obtain ⟨y, hy, hyA, hyb⟩ := (Matrix.not_exists_mulVec_le_iff A b).mp hsys_infeas
  set t : ℝ := y (.inr (.inr ()))
  have ht_pos : 0 < t := by
    have hdot : y ⬝ᵥ b = -t := by
      simp only [dotProduct, Fintype.sum_sum_type, b, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
        mul_zero, Finset.sum_const_zero, zero_add, Fintype.sum_unique, mul_neg, mul_one, t]
    linarith
  let lam : (Fin N → Bool) → ℝ := fun s => y (.inl s) / t
  have hlam_nn : ∀ s, 0 ≤ lam s := fun s => div_nonneg (hy (.inl s)) ht_pos.le
  have hlam_ge : ∀ i : Fin m, 1 ≤ ∑ s : Fin N → Bool, U s i * lam s := fun i => by
    have hcol := congrFun hyA i
    simp only [vecMul, dotProduct, Fintype.sum_sum_type, A, Matrix.of_apply, Pi.zero_apply,
      mul_ite, mul_neg, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
      Fintype.sum_unique] at hcol
    have hmu : 0 ≤ y (.inr (.inl i)) := hy (.inr (.inl i))
    have hsum_eq : ∑ s : Fin N → Bool, U s i * lam s = (∑ s, y (.inl s) * U s i) / t := by
      rw [sum_div]
      exact sum_congr rfl fun s _ => by simp only [lam]; ring
    rw [hsum_eq, le_div_iff₀ ht_pos]
    linarith
  -- Step 2: Basic solution shrinks support from `2^N` states to `T.card ≤ m`.
  let M : Matrix (Fin m) ((Fin N → Bool) ⊕ Fin m) ℝ :=
    Matrix.of fun i k =>
      match k with
      | .inl s => U s i
      | .inr j => if i = j then -1 else 0
  let x₀ : (Fin N → Bool) ⊕ Fin m → ℝ :=
    Sum.elim lam fun i => (∑ s : Fin N → Bool, U s i * lam s) - 1
  have hx₀_nn : 0 ≤ x₀ := by
    rintro (s | i)
    · exact hlam_nn s
    · exact sub_nonneg.mpr (hlam_ge i)
  have hMx₀ : M *ᵥ x₀ = fun _ => 1 := by
    funext i
    simp only [M, x₀, mulVec, dotProduct, Fintype.sum_sum_type, Matrix.of_apply, Sum.elim_inl,
      Sum.elim_inr, ite_mul, neg_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      ↓reduceIte]
    ring
  obtain ⟨z, hz_nn, hMz, -, hz_min⟩ :=
    Matrix.exists_nonneg_mulVec_eq_forall_mulVec_eq_zero hx₀_nn hMx₀
  set T : Finset (Fin N → Bool) := Finset.univ.filter fun s => z (.inl s) ≠ 0
  have hT_card : T.card ≤ m := by
    let φ : (T → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
      { toFun := fun v i => ∑ s : T, U s.1 i * v s
        map_add' := fun u v => funext fun i => by simp only [Pi.add_apply, mul_add, sum_add_distrib]
        map_smul' := fun r v => funext fun i => by
          simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_left_comm _ r, ← mul_sum] }
    have hinj : Function.Injective φ := by
      rw [injective_iff_map_eq_zero]
      intro v hv
      let w : (Fin N → Bool) ⊕ Fin m → ℝ := fun
        | .inl s => if h : s ∈ T then v ⟨s, h⟩ else 0
        | .inr _ => 0
      have hw_supp : ∀ k, z k = 0 → w k = 0 := by
        rintro (s | j) hk
        · have hsT : s ∉ T := by simp [T, hk]
          simp [w, hsT]
        · rfl
      have hMw : M *ᵥ w = 0 := by
        funext i
        have hvi : ∑ s : T, U s.1 i * v s = 0 := congrFun hv i
        simp only [M, w, mulVec, dotProduct, Fintype.sum_sum_type, Matrix.of_apply, mul_zero,
          Finset.sum_const_zero, add_zero, Pi.zero_apply]
        calc ∑ s : Fin N → Bool, U s i * (if h : s ∈ T then v ⟨s, h⟩ else 0)
            = ∑ s ∈ T, U s i * (if h : s ∈ T then v ⟨s, h⟩ else 0) :=
              (Finset.sum_subset (Finset.subset_univ T) fun s _ hs => by simp [hs]).symm
          _ = ∑ s : T, U s.1 i * v s := by
              rw [← Finset.sum_attach T]
              exact sum_congr rfl fun s _ => by simp [s.2]
          _ = 0 := hvi
      have hw0 := hz_min w hw_supp hMw
      funext s
      have := congrFun hw0 (.inl s.1)
      simpa [w, s.2] using this
    calc T.card = Fintype.card T := (Fintype.card_coe T).symm
      _ = Module.finrank ℝ (T → ℝ) := (Module.finrank_fintype_fun_eq_card ℝ).symm
      _ ≤ Module.finrank ℝ (Fin m → ℝ) := LinearMap.finrank_le_finrank_of_injective hinj
      _ = m := Module.finrank_fin_fun ℝ
  -- Step 3: Clear denominators to an `m × (|T| + m)` integer system for a small integer solution.
  let Aint : Matrix (Fin m) (T ⊕ Fin m) ℤ :=
    Matrix.of fun i k =>
      match k with
      | .inl s => intOrderPayoff O[i] (evalState O s.1)
      | .inr j => if i = j then -1 else 0
  let bint : Fin m → ℤ := fun _ => 1
  have hT_ge : ∀ i : Fin m,
      1 ≤ ∑ s : T, (intOrderPayoff O[i] (evalState O s.1) : ℝ) * z (.inl s.1) := fun i => by
    have hrow := congrFun hMz i
    simp only [M, mulVec, dotProduct, Fintype.sum_sum_type, Matrix.of_apply, ite_mul, neg_mul,
      one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte] at hrow
    have hge1 : 1 ≤ ∑ s : Fin N → Bool, U s i * z (.inl s) := by
      have hzi : 0 ≤ z (.inr i) := hz_nn (.inr i)
      linarith
    have hsub : ∑ s : Fin N → Bool, U s i * z (.inl s) = ∑ s : T, U s.1 i * z (.inl s.1) := by
      rw [← Finset.sum_subset (Finset.subset_univ T) fun s _ hs => by
        have h0 : z (.inl s) = 0 := by simpa [T] using hs
        simp [h0]]
      exact (Finset.sum_attach T (fun s => U s i * z (.inl s))).symm
    have hD_ge : (1 : ℝ) ≤ (O[i].quantity.den : ℝ) * (O[i].price.den : ℝ) := by
      have h1 : (1 : ℝ) ≤ O[i].quantity.den := by exact_mod_cast O[i].quantity.pos
      have h2 : (1 : ℝ) ≤ O[i].price.den := by exact_mod_cast O[i].price.pos
      nlinarith
    have hscale : ∑ s : T, (intOrderPayoff O[i] (evalState O s.1) : ℝ) * z (.inl s.1) =
        (O[i].quantity.den : ℝ) * (O[i].price.den : ℝ) * ∑ s : T, U s.1 i * z (.inl s.1) := by
      rw [Finset.mul_sum]
      refine sum_congr rfl fun s _ => ?_
      simp only [U, Matrix.of_apply, intOrderPayoff_cast_eq]
      ring
    rw [hsub] at hge1
    rw [hscale]
    nlinarith
  let xint : T ⊕ Fin m → ℝ :=
    Sum.elim (fun s => z (.inl s.1))
      fun i => (∑ s : T, (intOrderPayoff O[i] (evalState O s.1) : ℝ) * z (.inl s.1)) - 1
  have hxint_nn : 0 ≤ xint := by
    rintro (s | i)
    · exact hz_nn (.inl s.1)
    · exact sub_nonneg.mpr (hT_ge i)
  have hAxint : Aint.map (Int.cast : ℤ → ℝ) *ᵥ xint = fun i => (bint i : ℝ) := by
    funext i
    simp only [Aint, bint, xint, mulVec, dotProduct, Fintype.sum_sum_type, Matrix.map_apply,
      Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, Int.cast_one]
    have hdiag : ∑ j : Fin m, ((if i = j then (-1 : ℤ) else 0 : ℤ) : ℝ) *
        ((∑ s : T, (intOrderPayoff O[j] (evalState O s.1) : ℝ) * z (.inl s.1)) - 1) =
        -((∑ s : T, (intOrderPayoff O[i] (evalState O s.1) : ℝ) * z (.inl s.1)) - 1) := by
      have h1 : ∀ j : Fin m, ((if i = j then (-1 : ℤ) else 0 : ℤ) : ℝ) =
          if i = j then -1 else 0 := fun j => by split_ifs <;> simp
      simp only [h1, ite_mul, neg_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
        ↓reduceIte]
    linarith
  set B : ℕ := 2 ^ (2 * L + 1)
  have hB1 : 1 ≤ B := Nat.one_le_two_pow
  have hAint_le : ∀ i k, |Aint i k| ≤ (B : ℤ) := by
    intro i k
    rcases k with s | j
    · exact abs_intOrderPayoff_le (List.getElem_mem i.2) (evalState O s.1)
    · simp only [Aint, Matrix.of_apply]
      split_ifs
      · rw [abs_neg, abs_one]; exact_mod_cast hB1
      · rw [abs_zero]; exact Nat.cast_nonneg _
  have hbint_le : ∀ i, |bint i| ≤ (B : ℤ) := fun i => by
    simp only [bint, abs_one]; exact_mod_cast hB1
  obtain ⟨d, p, hd, hp_nn, hAp, -, hp_le⟩ :=
    Matrix.exists_int_nonneg_mulVec_eq hAint_le hbint_le hxint_nn hAxint
  -- Step 4: Bound `p (.inl s)` by `2 ^ ((5 * L + 3) * (4 * L))`.
  have hm_le : m ≤ L := length_le_length_encList encCompoundOrder O
  have hcard_col : Fintype.card (T ⊕ Fin m) ≤ 2 * L := by
    rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_fin]
    omega
  have hbound_nat :
      Nat.factorial (Fintype.card (T ⊕ Fin m)) *
          (Fintype.card (Fin m) * B ^ 2 + 1) ^ Fintype.card (T ⊕ Fin m) ≤
        2 ^ ((5 * L + 3) * (4 * L)) := by
    set K := Fintype.card (T ⊕ Fin m)
    set R := 2 ^ (5 * L + 3)
    have hR1 : 1 ≤ R := Nat.one_le_two_pow
    have hKR : K ≤ R :=
      (by omega : K ≤ 5 * L + 3).trans Nat.lt_two_pow_self.le
    have hbase : Fintype.card (Fin m) * B ^ 2 + 1 ≤ R := by
      rw [Fintype.card_fin]
      have hBsq : B ^ 2 = 2 ^ (4 * L + 2) := by
        simp only [B, ← pow_mul]
        congr 1; omega
      have h1 : m * B ^ 2 + 1 ≤ (m + 1) * B ^ 2 := by
        have : 1 ≤ B ^ 2 := Nat.one_le_pow _ _ (by omega)
        nlinarith
      have h2 : m + 1 ≤ 2 ^ (L + 1) :=
        (by omega : m + 1 ≤ L + 1).trans Nat.lt_two_pow_self.le
      calc m * B ^ 2 + 1 ≤ (m + 1) * B ^ 2 := h1
        _ ≤ 2 ^ (L + 1) * 2 ^ (4 * L + 2) := by rw [hBsq]; exact Nat.mul_le_mul_right _ h2
        _ = R := by simp only [R, ← pow_add]; congr 1; omega
    calc Nat.factorial K * (Fintype.card (Fin m) * B ^ 2 + 1) ^ K
        ≤ R ^ K * R ^ K :=
          Nat.mul_le_mul ((Nat.factorial_le_pow K).trans (Nat.pow_le_pow_left hKR K))
            (Nat.pow_le_pow_left hbase K)
      _ = R ^ (2 * K) := by rw [← pow_add, two_mul]
      _ ≤ R ^ (4 * L) := Nat.pow_le_pow_right hR1 (by omega)
      _ = 2 ^ ((5 * L + 3) * (4 * L)) := by simp only [R, ← pow_mul]
  let w : (Fin N → Bool) → ℤ := fun s => if h : s ∈ T then p (.inl ⟨s, h⟩) else 0
  refine ⟨T, w, hT_card, fun s hs => ?_, fun i => ?_⟩
  · simp only [w, hs, ↓reduceDIte]
    exact ⟨hp_nn (.inl ⟨s, hs⟩), (hp_le (.inl ⟨s, hs⟩)).trans (by exact_mod_cast hbound_nat)⟩
  · have hrow := congrFun hAp i
    simp only [Aint, bint, mulVec, dotProduct, Fintype.sum_sum_type, Matrix.of_apply,
      Pi.smul_apply, smul_eq_mul, mul_one, ite_mul, neg_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte] at hrow
    have hpi : 0 ≤ p (.inr i) := hp_nn (.inr i)
    have hsum_eq : ∑ s ∈ T, w s * intOrderPayoff O[i] (evalState O s) =
        ∑ s : T, intOrderPayoff O[i] (evalState O s.1) * p (.inl s) := by
      rw [← Finset.sum_attach T]
      exact sum_congr rfl fun s _ => by simp only [w, s.2, ↓reduceDIte, mul_comm]
    linarith

/-! ### Small-support Farkas & subset-infeasibility characterizations (p. 661) -/

private theorem not_hasDivisibleMatchOn_of_farkas {O : List CompoundOrder}
    {S : Finset (ℕ → Bool)} {w : (ℕ → Bool) → ℚ}
    (hw_nn : ∀ ω ∈ S, 0 ≤ w ω)
    (hw_pos : ∀ i : Fin O.length, 0 < ∑ ω ∈ S, (w ω : ℝ) * orderPayoff O[i] ω) :
    ¬ HasDivisibleMatchOn O S := by
  rintro ⟨α, hbounds, ⟨i₀, hi₀⟩, hpay⟩
  have hpos : 0 < ∑ i : Fin O.length, α i * ∑ ω ∈ S, (w ω : ℝ) * orderPayoff O[i] ω :=
    sum_pos' (fun i _ => mul_nonneg (hbounds i).1 (hw_pos i).le)
      ⟨i₀, mem_univ i₀, mul_pos hi₀ (hw_pos i₀)⟩
  have hnonneg : 0 ≤ ∑ ω ∈ S, (w ω : ℝ) * auctioneerPayoff O α ω :=
    sum_nonneg fun ω hω => mul_nonneg (by exact_mod_cast hw_nn ω hω) (hpay ω hω)
  have hrel : ∑ ω ∈ S, (w ω : ℝ) * auctioneerPayoff O α ω =
      -(∑ i : Fin O.length, α i * ∑ ω ∈ S, (w ω : ℝ) * orderPayoff O[i] ω) := by
    simp only [auctioneerPayoff, Finset.mul_sum, ← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    exact sum_congr rfl fun i _ => sum_congr rfl fun ω _ => by ring
  linarith

/-- **Small-support rational Farkas certificate** [PennockSami2007, Theorem 26.6(ii) proof,
p. 661]: a list of `m = O.length` compound orders admits no divisible match if and only if there
exist at most `m` states `S` (hence `S.card ≤ m + 1`) and nonnegative rational weights
`w : (ℕ → Bool) → ℚ` such that every order has strictly positive weighted payoff on `S`. -/
theorem not_hasDivisibleMatch_iff_exists_small_farkas (O : List CompoundOrder) :
    ¬ HasDivisibleMatch O ↔
      ∃ (S : Finset (ℕ → Bool)) (w : (ℕ → Bool) → ℚ),
        S.card ≤ O.length ∧ (∀ ω ∈ S, 0 ≤ w ω) ∧
        ∀ i : Fin O.length, 0 < ∑ ω ∈ S, (w ω : ℝ) * orderPayoff O[i] ω := by
  classical
  constructor
  · intro hno
    obtain ⟨T, wint, hTcard, hw_nn, hw_pos⟩ := exists_small_int_farkas O hno
    let S : Finset (ℕ → Bool) := T.image (evalState O)
    let w : (ℕ → Bool) → ℚ := fun ω =>
      ∑ s ∈ T.filter fun s => evalState O s = ω, (wint s : ℚ)
    refine ⟨S, w, Finset.card_image_le.trans hTcard, fun ω _ =>
      sum_nonneg fun s hs => by exact_mod_cast (hw_nn s (mem_filter.mp hs).1).1, fun i => ?_⟩
    have hD_pos : (0 : ℝ) < (O[i].quantity.den : ℝ) * (O[i].price.den : ℝ) :=
      mul_pos (Nat.cast_pos.mpr O[i].quantity.pos) (Nat.cast_pos.mpr O[i].price.pos)
    have hsum_eq : ∑ ω ∈ S, (w ω : ℝ) * orderPayoff O[i] ω =
        (∑ s ∈ T, (wint s : ℝ) * orderPayoff O[i] (evalState O s)) := by
      have hfib : ∑ ω ∈ S, ∑ s ∈ T.filter (fun s => evalState O s = ω),
            (wint s : ℝ) * orderPayoff O[i] (evalState O s) =
          ∑ s ∈ T, (wint s : ℝ) * orderPayoff O[i] (evalState O s) :=
        Finset.sum_fiberwise_of_maps_to (fun s hs => mem_image_of_mem _ hs) _
      rw [← hfib]
      refine sum_congr rfl fun ω _ => ?_
      simp only [w, Rat.cast_sum, Rat.cast_intCast, sum_mul]
      exact sum_congr rfl fun s hs => by rw [(mem_filter.mp hs).2]
    have hmul_eq : (O[i].quantity.den : ℝ) * (O[i].price.den : ℝ) *
        ∑ ω ∈ S, (w ω : ℝ) * orderPayoff O[i] ω =
        ((∑ s ∈ T, wint s * intOrderPayoff O[i] (evalState O s) : ℤ) : ℝ) := by
      rw [hsum_eq, Finset.mul_sum]
      push_cast
      refine sum_congr rfl fun s _ => ?_
      rw [intOrderPayoff_cast_eq]
      ring
    have hpos_int :
        (0 : ℝ) < ((∑ s ∈ T, wint s * intOrderPayoff O[i] (evalState O s) : ℤ) : ℝ) := by
      exact_mod_cast hw_pos i
    nlinarith
  · rintro ⟨S, w, -, hw_nn, hw_pos⟩ ⟨α, hbounds, hpos, hpay⟩
    exact not_hasDivisibleMatchOn_of_farkas hw_nn hw_pos ⟨α, hbounds, hpos, fun ω _ => hpay ω⟩

/-- **Small-constraint infeasibility characterization** [PennockSami2007, Theorem 26.6(ii) proof,
p. 661]: no divisible match exists for `m = O.length` orders if and only if there exists a subset
`S` of at most `m` states (hence at most `m + 1` state constraints) that already forbids every
divisible match (`¬ HasDivisibleMatchOn O S`). -/
theorem not_hasDivisibleMatch_iff_exists_small_subset (O : List CompoundOrder) :
    ¬ HasDivisibleMatch O ↔
      ∃ S : Finset (ℕ → Bool), S.card ≤ O.length ∧ ¬ HasDivisibleMatchOn O S := by
  constructor
  · intro hno
    obtain ⟨S, w, hcard, hw_nn, hw_pos⟩ :=
      (not_hasDivisibleMatch_iff_exists_small_farkas O).mp hno
    exact ⟨S, hcard, not_hasDivisibleMatchOn_of_farkas hw_nn hw_pos⟩
  · rintro ⟨S, -, hnoS⟩ ⟨α, hbounds, hpos, hpay⟩
    exact hnoS ⟨α, hbounds, hpos, fun ω _ => hpay ω⟩

/-! ### Native `coNP`-membership of `DivisibleOrderMatching` (Theorem 26.6(ii) upper bound) -/

/-- Encoding of an integer Farkas certificate `List (List Bool × ℤ)` pairing raw assignment bit
lists with signed-binary integer weights. -/
private abbrev encFarkasCert : List (List Bool × ℤ) ↪ List Bool :=
  encList (encPair encBits encIntBin)

/-- The `coNP` check for `DivisibleOrderMatchingᶜ`: every certificate weight is nonnegative and
every order has strictly positive integer-scaled weighted payoff across the certified states. -/
private def farkasCertCheck : List CompoundOrder × List (List Bool × ℤ) → Bool
  | (O, cert) =>
    cert.all (fun p => decide (0 ≤ p.2)) &&
      O.all fun o =>
        decide (0 < (cert.map fun p => p.2 * intOrderPayoff o (orderAssignment O p.1)).sum)

private theorem cert_scale_eq (O : List CompoundOrder) (o : CompoundOrder)
    (cert : List (List Bool × ℤ)) :
    (o.quantity.den : ℝ) * (o.price.den : ℝ) *
        (cert.map fun p => (p.2 : ℝ) * orderPayoff o (orderAssignment O p.1)).sum =
      ((cert.map fun p => p.2 * intOrderPayoff o (orderAssignment O p.1)).sum : ℝ) := by
  induction cert with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons, Int.cast_add, Int.cast_mul, mul_add]
    rw [ih, intOrderPayoff_cast_eq]
    ring

private theorem cert_auctioneer_sum_eq (O : List CompoundOrder) (α : Fin O.length → ℝ)
    (cert : List (List Bool × ℤ)) :
    (cert.map fun p => (p.2 : ℝ) * auctioneerPayoff O α (orderAssignment O p.1)).sum =
      -(∑ i : Fin O.length, α i *
        (cert.map fun p => (p.2 : ℝ) * orderPayoff O[i] (orderAssignment O p.1)).sum) := by
  induction cert with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons, ih, mul_add, Finset.sum_add_distrib, neg_add]
    congr 1
    simp only [auctioneerPayoff, Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact sum_congr rfl fun i _ => by ring

private theorem notMem_of_farkasCertCheck {O : List CompoundOrder}
    {cert : List (List Bool × ℤ)} (h : farkasCertCheck (O, cert) = true) :
    O ∉ DivisibleOrderMatching := by
  simp only [farkasCertCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨hnn, hpos⟩ := h
  rintro ⟨α, hbounds, ⟨i₀, hi₀⟩, hpay⟩
  have hord_pos (i : Fin O.length) :
      0 < (cert.map fun p => (p.2 : ℝ) * orderPayoff O[i] (orderAssignment O p.1)).sum := by
    have hi := hpos O[i] (List.getElem_mem i.2)
    have hD_pos : (0 : ℝ) < (O[i].quantity.den : ℝ) * (O[i].price.den : ℝ) :=
      mul_pos (Nat.cast_pos.mpr O[i].quantity.pos) (Nat.cast_pos.mpr O[i].price.pos)
    have hscale := cert_scale_eq O O[i] cert
    have hiR : (0 : ℝ) <
        ((cert.map fun p => p.2 * intOrderPayoff O[i] (orderAssignment O p.1)).sum : ℝ) := by
      exact_mod_cast hi
    nlinarith
  have hsum_pos :
      0 < ∑ i : Fin O.length, α i *
        (cert.map fun p => (p.2 : ℝ) * orderPayoff O[i] (orderAssignment O p.1)).sum :=
    sum_pos' (fun i _ => mul_nonneg (hbounds i).1 (hord_pos i).le)
      ⟨i₀, mem_univ i₀, mul_pos hi₀ (hord_pos i₀)⟩
  have hnonneg :
      0 ≤ (cert.map fun p => (p.2 : ℝ) * auctioneerPayoff O α (orderAssignment O p.1)).sum := by
    have hmem : ∀ x ∈ cert.map fun p => (p.2 : ℝ) * auctioneerPayoff O α (orderAssignment O p.1),
        0 ≤ x := by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      exact mul_nonneg (by exact_mod_cast hnn p hp) (hpay (orderAssignment O p.1))
    exact List.sum_nonneg hmem
  have hrel := cert_auctioneer_sum_eq O α cert
  linarith

private theorem length_encIntBin_le_of_le {z : ℤ} {E : ℕ} (h0 : 0 ≤ z)
    (hz : z ≤ ((2 ^ E : ℕ) : ℤ)) :
    (encIntBin z).length ≤ E + 2 := by
  rw [length_encIntBin]
  have h1 : z.natAbs ≤ 2 ^ E := by omega
  have h2 : z.natAbs.size ≤ E + 1 :=
    Nat.size_le.mpr (h1.trans_lt (Nat.pow_lt_pow_right (by decide) (by omega)))
  omega

/-- Polynomial bounding the encoded size of a small integer Farkas certificate. -/
private noncomputable def certPoly : Polynomial ℕ :=
  Polynomial.X * (2 * ((5 * Polynomial.X + 3) * (4 * Polynomial.X) + 2 * Polynomial.X + 3) + 1)

private theorem eval_certPoly (L : ℕ) :
    certPoly.eval L = L * (2 * ((5 * L + 3) * (4 * L) + 2 * L + 3) + 1) := by
  simp [certPoly]

private theorem exists_farkasCertCheck_of_notMem {O : List CompoundOrder}
    (hO : O ∉ DivisibleOrderMatching) :
    ∃ cert : List (List Bool × ℤ), farkasCertCheck (O, cert) = true ∧
      (encFarkasCert cert).length ≤ certPoly.eval (encOrderList O).length := by
  classical
  set L := (encOrderList O).length
  set E := (5 * L + 3) * (4 * L)
  obtain ⟨T, w, hTcard, hw_bound, hw_pos⟩ := exists_small_int_farkas O hO
  let cert : List (List Bool × ℤ) := T.toList.map fun s => (List.ofFn s, w s)
  refine ⟨cert, ?_, ?_⟩
  · simp only [farkasCertCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
    refine ⟨fun p hp => ?_, fun o ho => ?_⟩
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hp
      exact (hw_bound s (Finset.mem_toList.mp hs)).1
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ho
      have hsum : (cert.map fun p => p.2 * intOrderPayoff O[i] (orderAssignment O p.1)).sum =
          ∑ s ∈ T, w s * intOrderPayoff O[i] (evalState O s) := by
        simp only [cert, List.map_map, Function.comp_def, evalState]
        rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]
        rfl
      rw [hsum]
      exact hw_pos ⟨i, hi⟩
  · rw [eval_certPoly]
    have hvars_le : (orderVars O).length ≤ L := length_orderVars_le O
    have hcert_len : cert.length ≤ L := by
      calc cert.length = T.toList.length := List.length_map _
        _ = T.card := Finset.length_toList T
        _ ≤ O.length := hTcard
        _ ≤ L := length_le_length_encList encCompoundOrder O
    refine (length_encList_le (encPair encBits encIntBin) cert (b := E + 2 * L + 3) ?_).trans ?_
    · intro p hp
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hp
      have hsT : s ∈ T := Finset.mem_toList.mp hs
      rw [length_encPair, encBits_apply, List.length_ofFn]
      dsimp only
      have hw_len : (encIntBin (w s)).length ≤ E + 2 :=
        length_encIntBin_le_of_le (hw_bound s hsT).1 (hw_bound s hsT).2
      omega
    · exact Nat.mul_le_mul_right _ hcert_len

@[local fun_prop]
private theorem computableInPolyTime_orderVars :
    ComputableInPolyTime orderVars encOrderList (encList encNat) := by
  unfold orderVars
  fun_prop

@[local fun_prop]
private theorem computableInPolyTime_orderAssignment :
    ComputableInPolyTime
      (fun p : (List CompoundOrder × List Bool) × ℕ => orderAssignment p.1.1 p.1.2 p.2)
      (encPair (encPair encOrderList encBits) encNat) encBool := by
  have hvars :
      ComputableInPolyTime (fun p : (List CompoundOrder × List Bool) × ℕ => orderVars p.1.1)
        (encPair (encPair encOrderList encBits) encNat) (encList encNat) := by fun_prop
  have hidx := ComputableInPolyTime.idxOfWithInput hvars
    (ComputableInPolyTime.snd (encPair encOrderList encBits) encNat)
  exact ComputableInPolyTime.bitsGetDWithInput (by fun_prop) hidx false

@[local fun_prop]
private theorem computableInPolyTime_intOrderPayoff :
    ComputableInPolyTime
      (fun p : (List CompoundOrder × List Bool) × CompoundOrder =>
        intOrderPayoff p.2 (orderAssignment p.1.1 p.1.2))
      (encPair (encPair encOrderList encBits) encCompoundOrder) encIntBin := by
  have hassign : ComputableInPolyTime
      (fun q : ((List CompoundOrder × List Bool) × CompoundOrder) × ℕ =>
        orderAssignment q.1.1.1 q.1.1.2 q.2)
      (encPair (encPair (encPair encOrderList encBits) encCompoundOrder) encNat) encBool :=
    computableInPolyTime_orderAssignment.comp
      (by fun_prop : ComputableInPolyTime
        (fun q : ((List CompoundOrder × List Bool) × CompoundOrder) × ℕ => (q.1.1, q.2))
        (encPair (encPair (encPair encOrderList encBits) encCompoundOrder) encNat)
        (encPair (encPair encOrderList encBits) encNat))
  have heval (sel : CompoundOrder → CNF ℕ)
      (hsel : ComputableInPolyTime
        (fun p : (List CompoundOrder × List Bool) × CompoundOrder => sel p.2)
        (encPair (encPair encOrderList encBits) encCompoundOrder) encCNF) :
      ComputableInPolyTime
        (fun p : (List CompoundOrder × List Bool) × CompoundOrder =>
          (sel p.2).eval (orderAssignment p.1.1 p.1.2))
        (encPair (encPair encOrderList encBits) encCompoundOrder) encBool :=
    CNF.computableInPolyTime_eval (encV := encNat) hsel hassign
  have heval_cond := heval CompoundOrder.condition (by fun_prop)
  have heval_event := heval CompoundOrder.event (by fun_prop)
  have hqnum : ComputableInPolyTime
      (fun p : (List CompoundOrder × List Bool) × CompoundOrder => p.2.quantity.num)
      (encPair (encPair encOrderList encBits) encCompoundOrder) encIntBin := by fun_prop
  have hpden : ComputableInPolyTime
      (fun p : (List CompoundOrder × List Bool) × CompoundOrder => (p.2.price.den : ℤ))
      (encPair (encPair encOrderList encBits) encCompoundOrder) encIntBin := by fun_prop
  have hpnum : ComputableInPolyTime
      (fun p : (List CompoundOrder × List Bool) × CompoundOrder => p.2.price.num)
      (encPair (encPair encOrderList encBits) encCompoundOrder) encIntBin := by fun_prop
  have hinner := intBin_mul' hqnum (intBin_sub' (ite' heval_event hpden (const 0)) hpnum)
  exact (ite' heval_cond hinner (const 0)).of_enc_eq fun p => congrArg encIntBin (by
    simp only [intOrderPayoff])

private theorem computableInPolyTime_farkasCertCheck :
    ComputableInPolyTime farkasCertCheck (encPair encOrderList encFarkasCert) encBool := by
  have hdef : farkasCertCheck = fun x =>
      x.2.all (fun p => decide (0 ≤ p.2)) &&
        x.1.all fun o =>
          decide (0 < (x.2.map fun p => p.2 * intOrderPayoff o (orderAssignment x.1 p.1)).sum) :=
    rfl
  rw [hdef]
  apply bool_and'
  · apply allWithInput (by fun_prop)
    fun_prop
  · apply allWithInput (by fun_prop)
    have hmap : ComputableInPolyTime
        (fun q : (List CompoundOrder × List (List Bool × ℤ)) × CompoundOrder =>
          q.1.2.map fun p => p.2 * intOrderPayoff q.2 (orderAssignment q.1.1 p.1))
        (encPair (encPair encOrderList encFarkasCert) encCompoundOrder) (encList encIntBin) := by
      apply mapWithInput (by fun_prop)
      have harg : ComputableInPolyTime
          (fun r : ((List CompoundOrder × List (List Bool × ℤ)) × CompoundOrder) ×
              (List Bool × ℤ) => ((r.1.1.1, r.2.1), r.1.2))
          (encPair (encPair (encPair encOrderList encFarkasCert) encCompoundOrder)
            (encPair encBits encIntBin))
          (encPair (encPair encOrderList encBits) encCompoundOrder) := by fun_prop
      have hpay := computableInPolyTime_intOrderPayoff.comp harg
      have hwt : ComputableInPolyTime
          (fun r : ((List CompoundOrder × List (List Bool × ℤ)) × CompoundOrder) ×
              (List Bool × ℤ) => r.2.2)
          (encPair (encPair (encPair encOrderList encFarkasCert) encCompoundOrder)
            (encPair encBits encIntBin)) encIntBin := by fun_prop
      exact intBin_mul' hwt hpay
    exact intBin_lt' (const 0) (intBin_sum.comp hmap)

/-- **Divisible compound order matching belongs to `coNP`**
[PennockSami2007, Theorem 26.6(ii), pp. 660–661]: every non-matchable order list has a
polynomial-size integer Farkas certificate supported on at most `O.length` states, verified
natively in polynomial time on multi-tape Turing machines. -/
theorem DivisibleOrderMatching_mem_coNP :
    DivisibleOrderMatching ∈ coNP encOrderList :=
  mem_NP_of_check (.list (.pair .bits .intBin)) computableInPolyTime_farkasCertCheck
    (fun _ _ h => notMem_of_farkasCertCheck h)
    fun _ hO => exists_farkasCertCheck_of_notMem hO

/-! ### Native `coNP`-hardness and `coNP`-completeness (Theorem 26.6(ii), p. 661) -/

/-- The single-order reduction `φ ↦ [⟨1, 1 / 2, φ, []⟩]` from `UNSAT` to
`DivisibleOrderMatching` [PennockSami2007, Theorem 26.6(ii) proof, p. 661]. -/
private def unsatToOrderMatching (φ : CNF ℕ) : List CompoundOrder :=
  [⟨1, 1 / 2, φ, []⟩]

private theorem unsatToOrderMatching_mem_iff (φ : CNF ℕ) :
    φ ∈ UNSAT ↔ unsatToOrderMatching φ ∈ DivisibleOrderMatching := by
  let o : CompoundOrder := ⟨1, 1 / 2, φ, []⟩
  change ¬ φ.Satisfiable ↔ HasDivisibleMatch [o]
  have hpay_single (α : Fin [o].length → ℝ) (ω : ℕ → Bool) :
      auctioneerPayoff [o] α ω = -(α ⟨0, by simp⟩) * orderPayoff o ω := by
    simp only [auctioneerPayoff]
    exact Fin.sum_univ_one fun i : Fin 1 => -(α i) * orderPayoff [o][i] ω
  constructor
  · intro hunsat
    refine ⟨fun _ => 1, fun _ => ⟨by norm_num, le_rfl⟩, ⟨⟨0, by simp⟩, by norm_num⟩, fun ω => ?_⟩
    have hfalse : φ.eval ω = false := by
      cases h : φ.eval ω
      · rfl
      · exact absurd ⟨ω, h⟩ hunsat
    rw [hpay_single]
    simp only [orderPayoff, o, CNF.eval_nil, ↓reduceIte, hfalse, Bool.false_eq_true]
    norm_num
  · rintro ⟨α, -, ⟨⟨k, hk⟩, hi₀⟩, hpay⟩ ⟨ω, hω⟩
    have hk0 : k = 0 := by simp only [List.length_singleton] at hk; omega
    subst hk0
    have h := hpay ω
    rw [hpay_single] at h
    simp only [orderPayoff, o, CNF.eval_nil, ↓reduceIte, hω] at h
    have h0 : (⟨0, hk⟩ : Fin [o].length) = 0 := rfl
    rw [h0] at hi₀
    norm_num at h
    linarith

private theorem computableInPolyTime_unsatToOrderMatching :
    ComputableInPolyTime unsatToOrderMatching encCNF encOrderList := by
  have hord : ComputableInPolyTime (fun φ : CNF ℕ => (⟨1, 1 / 2, φ, []⟩ : CompoundOrder))
      encCNF encCompoundOrder :=
    encCompoundOrder_mk_polyTime (const (1 : ℚ)) (const (1 / 2 : ℚ)) id' (const ([] : CNF ℕ))
  exact ((ComputableInPolyTime.cons encCompoundOrder).comp (hord.prod (const []))).of_enc_eq
    fun _ => rfl

/-- Polynomial-time many-one reduction `UNSAT ≤ₚ DivisibleOrderMatching`
[PennockSami2007, Theorem 26.6(ii) proof, p. 661]. -/
theorem polyTimeReducible_UNSAT_DivisibleOrderMatching :
    PolyTimeReducible encCNF encOrderList UNSAT DivisibleOrderMatching :=
  ⟨unsatToOrderMatching, computableInPolyTime_unsatToOrderMatching, unsatToOrderMatching_mem_iff⟩

/-- **Divisible compound order matching is `coNP`-hard**
[PennockSami2007, Theorem 26.6(ii), pp. 660–661]. -/
theorem DivisibleOrderMatching_coNPHard :
    coNPHard encOrderList DivisibleOrderMatching :=
  CookLevin.UNSAT_coNPComplete.2.trans polyTimeReducible_UNSAT_DivisibleOrderMatching

/-- **Theorem 26.6(ii)** ([PennockSami2007, pp. 660–661]): the divisible order-matching problem
for compound conditional securities with unlimited base events is **`coNP`-complete**. -/
theorem DivisibleOrderMatching_coNPComplete :
    coNPComplete encOrderList DivisibleOrderMatching :=
  ⟨DivisibleOrderMatching_mem_coNP, DivisibleOrderMatching_coNPHard⟩

end Cslib.GameTheory.PredictionMarket
