/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Demand
public import CslibFrontier.Computability.Circuit.Frontier.Reduction
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Logb
import CslibFrontier.Tactic.LinarithCast

/-!
# The frontier lower bound

**Main theorem** (`eventually_lt_mul_multiarySize`). Fix a fan-in bound `r ≥ 2`, and suppose that
the graphs of maximum degree `r + 1` have layouts of width `(A + o(1)) β₁ + o(|V|)`, where `β₁` is
the cycle rank (the layout hypothesis `LayoutBound (r + 1) A`). Let `S_n ⊆ U^n` be
`K_n`-rectangle-free sets over a finite alphabet `U`, with `log K_n = o(n)` and
`|S_n| ≥ |U| ^ (n - o(n))`. Then for every `ε > 0` and all large `n`, every circuit deciding
`S_n` over any basis of fan-in at most `r` on `U` has `s` multiary gates (`arity ≥ 2`) with

`(r - 1) s > (1 + 1/A - ε) n`.

Constant and unary gates (`arity ≤ 1`) are not counted: deduplicating unary wires bounds the total
gate count cleanly in `s` and `n`, and unary gates contribute zero to the cycle rank and read-input
budget of the compiled network. For fan-in two (`eventually_lt_multiarySize`) the graphs are
subcubic and the bound reads `s > (1 + 1/A - ε) n`. The corresponding `innerSize` statements
(`eventually_lt_mul_innerSize`, `eventually_lt_innerSize`) follow immediately from
`c.multiarySize ≤ c.innerSize`.

The proof is the reduction theorem followed by the comparison of demand and supply
(`eventually_lt_of_demand`). A circuit with `s` multiary gates gives a graph of cycle rank about
`(r - 1) s - n`, all of whose layouts have width about `n`: that is the demand. The layout
hypothesis provides a layout of width about `A ((r - 1) s - n)`: that is the supply. So
`n ≤ A ((r - 1) s - n) + o(n)`, that is, `(r - 1) s ≥ (1 + 1/A - o(1)) n`.

The theorems of this file are conditional on the layout hypothesis, which is stated as
`LayoutBound`; any instance of it yields an unconditional lower bound.

**The worst-case claims** (`MultiaryLowerBound L` and `CircuitLowerBound L`) bundle the statement
for fan-in two with coefficient `L`, so that each layout theorem reads as one line:
`multiaryLowerBound_of_layoutBound : LayoutBound 3 A → MultiaryLowerBound (1 + 1/A)`.

## Main definitions

* `Cslib.Circuits.Frontier.DenseRectangleFree`: the hypotheses on the problem, that `S_n` is
  eventually `K_n`-rectangle-free with `log K_n = o(n)` and `|S_n| ≥ |U| ^ (n - o(n))`.
* `Cslib.Circuits.Frontier.MultiaryLowerBound`: for a coefficient `L` and every `ε > 0`, circuits
  of fan-in at most two deciding dense rectangle-free sets on `n` inputs need more than `(L - ε) n`
  multiary gates (`arity = 2`; constant and unary gates are free).
* `Cslib.Circuits.Frontier.CircuitLowerBound`: the same statement for `innerSize` (gates of
  positive arity).

## Main results

* `Cslib.Circuits.Frontier.eventually_lt_of_frontier`: the comparison of demand and supply with
  the error terms of the problem and a sublinear slack, shared by all frontier lower bounds.
* `Cslib.Circuits.Frontier.eventually_lt_of_graph`: the comparison of demand and supply for any
  family of graphs with the bounds of the reduction theorem.
* `Cslib.Circuits.Frontier.eventually_lt_mul_multiarySize`,
  `Cslib.Circuits.Frontier.eventually_lt_mul_innerSize`: the frontier lower bound for fan-in at
  most `r`.
* `Cslib.Circuits.Frontier.eventually_lt_multiarySize`,
  `Cslib.Circuits.Frontier.eventually_lt_innerSize`: the frontier lower bound for fan-in two.
* `Cslib.Circuits.Frontier.multiaryLowerBound_of_layoutBound`,
  `Cslib.Circuits.Frontier.circuitLowerBound_of_layoutBound`: the same, as bundled claims.
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

open Set Filter Asymptotics

universe u v

variable {U : Type u} [Finite U] [Nontrivial U]

/-- A set of inputs has at most `|U| ^ n` elements: `log_|U| |S| ≤ n`. -/
theorem logb_ncard_le_self {n : ℕ} {S : Set (Fin n → U)} (hS : S.Nonempty) :
    Real.logb (Nat.card U) S.ncard ≤ n := by
  have hq : (1 : ℝ) < Nat.card U := by exact_mod_cast Finite.one_lt_card
  have hle : (S.ncard : ℝ) ≤ (Nat.card U : ℝ) ^ n := by
    simpa [Nat.card_fun] using (Nat.cast_le (α := ℝ)).2 (ncard_le_card S)
  have hpos : (0 : ℝ) < S.ncard := by exact_mod_cast (ncard_pos (toFinite S)).mpr hS
  calc Real.logb (Nat.card U) S.ncard ≤ Real.logb (Nat.card U) ((Nat.card U : ℝ) ^ n) :=
        Real.logb_le_logb_of_le hq hpos hle
    _ = n := Real.logb_self_pow (zero_lt_one.trans hq) hq.ne' n

omit [Finite U] [Nontrivial U] in
/-- **Dense rectangle-free families**, the hypotheses on the problem in every frontier lower
bound: for all large `n` the set `S_n ⊆ U^n` is `K_n`-rectangle-free, `log K_n = o(n)`, and
`n log |U| - log |S_n| = o(n)`, that is, `|S_n| ≥ |U| ^ (n - o(n))`. -/
structure DenseRectangleFree (S : ∀ n, Set (Fin n → U)) (K : ℕ → ℕ) : Prop where
  /-- For all large `n`, `S_n` is `K_n`-rectangle-free. -/
  eventually_rectangleFree : ∀ᶠ n in atTop, RectangleFree (S n) (K n)
  /-- The rectangle bound is subexponential: `log K_n = o(n)`. -/
  isLittleO_log : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ)
  /-- The sets are dense: `n log |U| - log |S_n| = o(n)`. -/
  isLittleO_deficit :
    (fun n => n * Real.log (Nat.card U) - Real.log (S n).ncard) =o[atTop] fun n => (n : ℝ)

variable {S : ∀ n, Set (Fin n → U)} {K : ℕ → ℕ}

/-- A dense family of sets has `n - log_|U| |S_n| = o(n)`. -/
theorem isLittleO_sub_logb_ncard
    (hdense : (fun n => n * Real.log (Nat.card U) - Real.log (S n).ncard) =o[atTop]
      fun n => (n : ℝ)) :
    (fun n : ℕ => (n : ℝ) - Real.logb (Nat.card U) (S n).ncard) =o[atTop] fun n => (n : ℝ) := by
  have hL : 0 < Real.log (Nat.card U) := Real.log_pos (by exact_mod_cast Finite.one_lt_card)
  refine (hdense.const_mul_left (1 / Real.log (Nat.card U))).congr_left fun n => ?_
  simp only [Real.logb]
  field_simp

/-- A dense family of rectangle-free sets is eventually large enough for the reduction:
`|U| K_n ^ 2 ≤ |S_n|`. -/
theorem eventually_card_mul_sq_le_ncard (hSK : DenseRectangleFree S K) :
    ∀ᶠ n in atTop, Nat.card U * K n ^ 2 ≤ (S n).ncard := by
  set q := Nat.card U
  have hq : (1 : ℝ) < q := by exact_mod_cast Finite.one_lt_card
  have hL : 0 < Real.log q := Real.log_pos hq
  have hlog : (fun n : ℕ => Real.log q + 2 * Real.log (K n) +
      (n * Real.log q - Real.log (S n).ncard)) =o[atTop] fun n => (n : ℝ) :=
    ((isLittleO_const_left.mpr
      (Or.inr (tendsto_norm_atTop_atTop.comp tendsto_natCast_atTop_atTop))).add
      (hSK.isLittleO_log.const_mul_left 2)).add hSK.isLittleO_deficit
  filter_upwards [hlog.bound (show 0 < Real.log q / 2 by positivity),
    hSK.eventually_rectangleFree, eventually_ge_atTop 1] with n hn hfreen hn1
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hK1 : (1 : ℝ) ≤ K n := by exact_mod_cast hfreen.pos
  have hlogK : 0 ≤ Real.log (K n) := Real.log_nonneg hK1
  simp only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)] at hn
  -- `log |S| ≥ log q + 2 log K + (n / 2) log q > log (q K ^ 2)`.
  have hSlog : Real.log q + 2 * Real.log (K n) < Real.log (S n).ncard := by
    nlinarith [le_abs_self (Real.log q + 2 * Real.log (K n) +
      (n * Real.log q - Real.log (S n).ncard))]
  have hSpos : (0 : ℝ) < (S n).ncard :=
    Nat.cast_pos.2 (Nat.pos_of_ne_zero fun h0 => by simp [h0] at hSlog; linarith)
  have : Real.log (q * K n ^ 2 : ℝ) ≤ Real.log (S n).ncard := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    cast_linarith
  exact_mod_cast (Real.log_le_log_iff (by positivity) hSpos).mp this

private theorem eventually_lt_of_frontier_of_bound {A M : ℝ} (hA : 0 < A) (hM : 0 ≤ M) (d : ℝ)
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    (hdense : (fun n => n * Real.log (Nat.card U) - Real.log (S n).ncard) =o[atTop]
      fun n => (n : ℝ))
    {β : ℕ → ℝ} (hβ : β =o[atTop] fun n => (n : ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ C : ℝ, ∀ᶠ n : ℕ in atTop, ∀ s v ρ w : ℝ, 0 ≤ s → 0 ≤ v →
      v ≤ M * (n + s + 1) →
      ρ ≤ s - Real.logb (Nat.card U) (S n).ncard + 2 * Real.logb (Nat.card U) (K n) +
        Real.logb (Nat.card U) (v + 1) + β n + 1 →
      Real.logb (Nat.card U) (S n).ncard ≤
        w + d + 3 * Real.logb (Nat.card U) (K n) + Real.logb (Nat.card U) (v + 1) + β n →
      w ≤ (A + η) * ρ + η * v + C →
      (1 + 1 / A - ε) * n < s := by
  set q := Nat.card U
  have hq : (1 : ℝ) < q := by exact_mod_cast Finite.one_lt_card
  have h2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hL2 : Real.log 2 ≤ Real.log q :=
    Real.log_le_log two_pos (by exact_mod_cast Finite.one_lt_card)
  set κ : ℝ := M + (A + 2) / Real.log 2
  have hκ : 0 ≤ κ := by positivity
  set e : ℕ → ℝ := fun n => (n - Real.logb q (S n).ncard) + 4 * Real.logb q (K n) + β n +
    (|d| + 3)
  have he : e =o[atTop] fun n => (n : ℝ) := by
    have h1 : (fun n : ℕ => 4 * Real.logb q (K n)) =o[atTop] fun n => (n : ℝ) :=
      (hK.const_mul_left (4 / Real.log q)).congr_left fun n => by
        simp only [Real.logb]
        ring
    have h3 : (fun _ : ℕ => |d| + 3) =o[atTop] fun n => (n : ℝ) :=
      isLittleO_const_left.mpr
        (Or.inr (tendsto_norm_atTop_atTop.comp tendsto_natCast_atTop_atTop))
    exact (((isLittleO_sub_logb_ncard hdense).add h1).add hβ).add h3
  obtain ⟨η₀, hη₀, H⟩ := eventually_lt_of_demand hA hκ hε
  set η := min η₀ 1
  have hη : 0 < η := lt_min hη₀ one_pos
  have hη1 : η ≤ 1 := min_le_right _ _
  refine ⟨η, hη, fun C => ?_⟩
  filter_upwards [H η hη (min_le_left _ _) C e he] with n hn
  intro s v ρ w hs hv hvs hρ hw hsupply
  have hlogK : 0 ≤ Real.logb q (K n) :=
    div_nonneg (Real.log_natCast_nonneg _) (Real.log_nonneg hq.le)
  have hlog0 : 0 ≤ Real.log (v + 1) := Real.log_nonneg (by linarith)
  have hlogV0 : 0 ≤ Real.logb q (v + 1) := Real.logb_nonneg hq (by linarith)
  have hlogV : (A + η + 1) * Real.logb q (v + 1) ≤ κ * Real.log (v + 1) := by
    have h1 : Real.logb q (v + 1) ≤ Real.log (v + 1) / Real.log 2 :=
      div_le_div_of_nonneg_left hlog0 h2 hL2
    calc (A + η + 1) * Real.logb q (v + 1) ≤ (A + 2) * (Real.log (v + 1) / Real.log 2) :=
          mul_le_mul (by linarith) h1 hlogV0 (by linarith)
      _ ≤ κ * Real.log (v + 1) :=
          ((mul_div_assoc' (A + 2) _ _).trans (div_mul_eq_mul_div (A + 2) _ _).symm).trans_le
            (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hM) hlog0)
  have hvκ : v ≤ κ * (n + s + 1) :=
    hvs.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity))
      (by linarith [Nat.cast_nonneg (α := ℝ) n]))
  refine hn s v (w - (A + η) * Real.logb q (v + 1)) hs hv hvκ ?_ ?_
  · simp only [e]
    nlinarith [le_abs_self d]
  · have hρ' : ρ ≤ s - n + e n + Real.logb q (v + 1) := by
      simp only [e]
      linarith [abs_nonneg d]
    nlinarith [mul_le_mul_of_nonneg_left hρ' (by linarith : 0 ≤ A + η)]

/-- **Demand against supply for the frontier method**, with the error terms of the problem and
a sublinear slack. Let `S_n` be dense sets with `log K_n = o(n)`, let `β(n) = o(n)`, let `d` be a
constant and `A > 0`. For every `ε > 0` there is a slack `η > 0` of the layout hypothesis such
that, for every constant `C` and all large `n`, the following holds for reals `s, v ≥ 0` (a gate
budget and a number of vertices with `v ≤ 7 s + 3 n + 3`) and `ρ, w`, where `q = |U|`:

* if `ρ ≤ s - log_q |S_n| + 2 log_q K_n + log_q (v + 1) + β(n) + 1` (a cycle rank: the graph
  reads almost all inputs),
* and `log_q |S_n| ≤ w + d + 3 log_q K_n + log_q (v + 1) + β(n)` (the demand: some frontier is
  wide),
* and `w ≤ (A + η) ρ + η v + C` (the supply of the layout hypothesis),

then `s > (1 + 1/A - ε) n`.

This is the numerical half of every frontier lower bound in this library: the circuit lower
bounds apply it to `s = (r - 1)` times the number of gates. -/
theorem eventually_lt_of_frontier {A : ℝ} (hA : 0 < A) (d : ℝ)
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    (hdense : (fun n => n * Real.log (Nat.card U) - Real.log (S n).ncard) =o[atTop]
      fun n => (n : ℝ))
    {β : ℕ → ℝ} (hβ : β =o[atTop] fun n => (n : ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ C : ℝ, ∀ᶠ n : ℕ in atTop, ∀ s v ρ w : ℝ, 0 ≤ s → 0 ≤ v →
      v ≤ 7 * s + 3 * n + 3 →
      ρ ≤ s - Real.logb (Nat.card U) (S n).ncard + 2 * Real.logb (Nat.card U) (K n) +
        Real.logb (Nat.card U) (v + 1) + β n + 1 →
      Real.logb (Nat.card U) (S n).ncard ≤
        w + d + 3 * Real.logb (Nat.card U) (K n) + Real.logb (Nat.card U) (v + 1) + β n →
      w ≤ (A + η) * ρ + η * v + C →
      (1 + 1 / A - ε) * n < s := by
  obtain ⟨η, hη, H⟩ := eventually_lt_of_frontier_of_bound (M := 7) hA (by norm_num) d hK hdense
    hβ hε
  refine ⟨η, hη, fun C => ?_⟩
  filter_upwards [H C] with n hn s v ρ w hs hv hvs hρ hw hsupply
  exact hn s v ρ w hs hv (by linarith [Nat.cast_nonneg (α := ℝ) n]) hρ hw hsupply

private theorem eventually_lt_of_graph_of_bound {r : ℕ} (hr : 2 ≤ r) {A M : ℝ} (hA : 0 < A)
    (hM : 0 ≤ M) (hlayout : LayoutBound (r + 1) A) (hSK : DenseRectangleFree S K)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (g : ℕ) (V E : Type) [Finite V] [Finite E] (G : Multigraph V E),
      G.toSimpleGraph.Connected → G.Loopless → G.MaxDegreeLE (r + 1) →
      (Nat.card V : ℝ) ≤ M * (n + (r - 1) * g + 1) →
      (G.cycleRank : ℝ) ≤ (r - 1) * g - n + Real.logb (Nat.card U) (K n) + 1 →
      (∀ π : Layout V, Real.logb (Nat.card U) (S n).ncard ≤
        G.width π + (r + 2) + 3 * Real.logb (Nat.card U) (K n) +
          Real.logb (Nat.card U) (Nat.card V + 1)) →
      (1 + 1 / A - ε) * n < (r - 1) * g := by
  set q := Nat.card U
  have hq : (1 : ℝ) < q := by exact_mod_cast Finite.one_lt_card
  obtain ⟨η, hη, H⟩ := eventually_lt_of_frontier_of_bound (M := M) hA hM (r + 2)
    hSK.isLittleO_log hSK.isLittleO_deficit (isLittleO_zero (fun n : ℕ => (n : ℝ)) atTop) hε
  obtain ⟨C, hC⟩ := hlayout η hη
  filter_upwards [H C, hSK.eventually_rectangleFree, eventually_card_mul_sq_le_ncard hSK] with
    n hn hfreen hbign g V E _ _ G hconn hloop hdeg hV hrank hwidth
  obtain ⟨π, hπ⟩ := hC V E G hconn hloop hdeg
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hSne : (S n).Nonempty := (ncard_pos (toFinite _)).mp
    ((Nat.mul_pos Nat.card_pos (pow_pos hfreen.pos 2)).trans_le hbign)
  have hlogS := logb_ncard_le_self hSne
  have hlogK : 0 ≤ Real.logb q (K n) :=
    div_nonneg (Real.log_natCast_nonneg _) (Real.log_nonneg hq.le)
  have hlogV : 0 ≤ Real.logb q (Nat.card V + 1) :=
    Real.logb_nonneg hq (by linarith [Nat.cast_nonneg (α := ℝ) (Nat.card V)])
  refine hn ((r - 1) * g) (Nat.card V) G.cycleRank (G.width π)
    (mul_nonneg (by linarith) (Nat.cast_nonneg g)) (Nat.cast_nonneg _) hV ?_
    (by simpa using hwidth π) hπ
  linarith [show (0 : ℕ → ℝ) n = 0 from rfl]

/-- **Demand against supply for graphs.** Assume the layout hypothesis for maximum degree `r + 1`
with coefficient `A > 0`, and let `S_n` be dense `K_n`-rectangle-free sets with
`log K_n = o(n)`. For every `ε > 0` and all large `n`: every connected, loopless graph of maximum
degree `r + 1` with the bounds of the reduction theorem for `g` gates (at most `2 r g + 3`
vertices, cycle rank at most `(r - 1) g - n + log_q K_n + 1`, and every layout of width at least
`log_q |S_n| - 3 log_q K_n - log_q (|V| + 1) - (r + 2)`) has `(r - 1) g > (1 + 1/A - ε) n`.

This is the numerical half of the lower bound, independent of circuits: the comparison of demand
and supply `eventually_lt_of_frontier`, with the layout hypothesis as the supply. -/
theorem eventually_lt_of_graph {r : ℕ} (hr : 2 ≤ r) {A : ℝ} (hA : 0 < A)
    (hlayout : LayoutBound (r + 1) A) (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (g : ℕ) (V E : Type) [Finite V] [Finite E] (G : Multigraph V E),
      G.toSimpleGraph.Connected → G.Loopless → G.MaxDegreeLE (r + 1) →
      Nat.card V ≤ 2 * r * g + 3 →
      (G.cycleRank : ℝ) ≤ (r - 1) * g - n + Real.logb (Nat.card U) (K n) + 1 →
      (∀ π : Layout V, Real.logb (Nat.card U) (S n).ncard ≤
        G.width π + (r + 2) + 3 * Real.logb (Nat.card U) (K n) +
          Real.logb (Nat.card U) (Nat.card V + 1)) →
      (1 + 1 / A - ε) * n < (r - 1) * g := by
  filter_upwards [eventually_lt_of_graph_of_bound (M := 7) hr hA (by norm_num) hlayout hSK hε] with
    n hn g V E _ _ G hconn hloop hdeg hV hrank hwidth
  refine hn g V E G hconn hloop hdeg ?_ hrank hwidth
  cast_nlinarith [hV, hr]

/-- **The frontier lower bound, charging only multiary gates.** Let `r ≥ 2` and assume the layout
hypothesis for maximum degree `r + 1` with coefficient `A > 0`. Let `S_n ⊆ U^n` be
`K_n`-rectangle-free sets over a finite alphabet `U` with at least two symbols, with
`log K_n = o(n)` and `n log |U| - log |S_n| = o(n)`. Then for every `ε > 0` and all large `n`,
every circuit of fan-in at most `r` deciding `S_n`, over any basis and interpretation on `U`, has
`s` multiary gates (`arity ≥ 2`; constant and unary gates are free) with
`(r - 1) s > (1 + 1/A - ε) n`. -/
theorem eventually_lt_mul_multiarySize {r : ℕ} (hr : 2 ≤ r) {A : ℝ} (hA : 0 < A)
    (hlayout : LayoutBound (r + 1) A) (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost r → c.Decides I Acc (S n) →
        (1 + 1 / A - ε) * n < (r - 1) * c.multiarySize := by
  set q := Nat.card U
  set M : ℝ := 2 * r * (1 + q + (q : ℝ) ^ q) + 3
  filter_upwards [eventually_lt_of_graph_of_bound (M := M) hr hA (by positivity) hlayout hSK hε,
    hSK.eventually_rectangleFree, eventually_card_mul_sq_le_ncard hSK] with n hn hfreen hbign
  intro σ I Acc c hfan hS
  obtain ⟨V, E, _, _, G, hc, hl, hd, hV, hrank, hw⟩ :=
    exists_graph_of_decides_multiarySize hr hfan hS hfreen hbign
  refine hn c.multiarySize V E G hc hl hd ?_ hrank hw
  have hV' : (Nat.card V : ℝ) ≤
      2 * r * (c.multiarySize + q + (c.multiarySize + n) * (q : ℝ) ^ q) + 3 := mod_cast hV
  have hr' : (2 : ℝ) ≤ r := mod_cast hr
  have hg_le : (c.multiarySize : ℝ) ≤ (r - 1) * c.multiarySize :=
    le_mul_of_one_le_left (Nat.cast_nonneg _) (by linarith)
  have hinner : (c.multiarySize : ℝ) + q + (c.multiarySize + n) * (q : ℝ) ^ q ≤
      (1 + q + (q : ℝ) ^ q) * (n + ((r - 1) * c.multiarySize) + 1) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) c.multiarySize,
      Nat.cast_nonneg (α := ℝ) q, pow_nonneg (Nat.cast_nonneg (α := ℝ) q) q]
  dsimp only [M]
  linarith [mul_le_mul_of_nonneg_left hinner (by positivity : (0 : ℝ) ≤ 2 * r),
    Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) c.multiarySize]

/-- **The frontier lower bound.** Let `r ≥ 2` and assume the layout hypothesis for maximum degree
`r + 1` with coefficient `A > 0`. Let `S_n ⊆ U^n` be `K_n`-rectangle-free sets over a finite
alphabet `U` with at least two symbols, with `log K_n = o(n)` and
`n log |U| - log |S_n| = o(n)`. Then for every `ε > 0` and all large `n`, every circuit of fan-in
at most `r` deciding `S_n`, over any basis and interpretation on `U`, has `s` inner gates with
`(r - 1) s > (1 + 1/A - ε) n`. -/
theorem eventually_lt_mul_innerSize {r : ℕ} (hr : 2 ≤ r) {A : ℝ} (hA : 0 < A)
    (hlayout : LayoutBound (r + 1) A) (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost r → c.Decides I Acc (S n) →
        (1 + 1 / A - ε) * n < (r - 1) * c.innerSize := by
  filter_upwards [eventually_lt_mul_multiarySize.{u, v} hr hA hlayout hSK hε] with
    n hn σ I Acc c hfan hS
  refine (hn σ I Acc c hfan hS).trans_le ?_
  have hr' : (0 : ℝ) ≤ (r : ℝ) - 1 := by cast_linarith [hr]
  exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr c.multiarySize_le_innerSize) hr'

/-- **The frontier lower bound for fan-in two, charging only multiary gates.** Assume the layout
hypothesis for subcubic graphs with coefficient `A > 0`. Under the hypotheses of
`eventually_lt_mul_multiarySize`, for every `ε > 0` and all large `n`, every circuit of fan-in at
most two deciding `S_n`, over any basis and interpretation on `U`, has more than
`(1 + 1/A - ε) n` gates of arity two (constant and unary gates are free). -/
theorem eventually_lt_multiarySize {A : ℝ} (hA : 0 < A) (hlayout : LayoutBound 3 A)
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 2 → c.Decides I Acc (S n) →
        (1 + 1 / A - ε) * n < c.multiarySize := by
  filter_upwards [eventually_lt_mul_multiarySize le_rfl hA hlayout hSK hε] with n hn σ I Acc c
    hfan hS
  simpa only [Nat.cast_ofNat, show (2 : ℝ) - 1 = 1 by norm_num, one_mul] using
    hn σ I Acc c hfan hS

/-- **The frontier lower bound for fan-in two.** Assume the layout hypothesis for subcubic graphs
with coefficient `A > 0`. Under the hypotheses of `eventually_lt_mul_innerSize`, for every
`ε > 0` and all large `n`, every circuit of fan-in at most two deciding `S_n`, over any basis and
interpretation on `U`, has more than `(1 + 1/A - ε) n` inner gates. -/
theorem eventually_lt_innerSize {A : ℝ} (hA : 0 < A) (hlayout : LayoutBound 3 A)
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 2 → c.Decides I Acc (S n) →
        (1 + 1 / A - ε) * n < c.innerSize := by
  filter_upwards [eventually_lt_multiarySize.{u, v} hA hlayout hSK hε] with n hn σ I Acc c hfan hS
  exact (hn σ I Acc c hfan hS).trans_le (Nat.cast_le.mpr c.multiarySize_le_innerSize)

/-- **The worst-case multiary claim with coefficient `L`.** Let `U` be a finite alphabet with at
least two symbols, and let `S_n ⊆ U^n` be `K_n`-rectangle-free sets with `log K_n = o(n)` and
`n log |U| - log |S_n| = o(n)`. Then for every `ε > 0` and all large `n`, every circuit of fan-in
at most two deciding `S_n`, over any basis and interpretation on `U`, has more than `(L - ε) n`
multiary gates (`arity = 2`; constant and unary gates are free).

The alphabet lives in the universe `u` and the basis in the universe `v`. -/
def MultiaryLowerBound (L : ℝ) : Prop :=
  ∀ (U : Type u) [Finite U] [Nontrivial U] (S : ∀ n, Set (Fin n → U)) (K : ℕ → ℕ),
    DenseRectangleFree S K →
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 2 → c.Decides I Acc (S n) →
        (L - ε) * n < c.multiarySize

/-- A multiary circuit lower bound holds for every smaller coefficient. -/
theorem MultiaryLowerBound.mono {L L' : ℝ} (h : MultiaryLowerBound.{u, v} L) (hL : L' ≤ L) :
    MultiaryLowerBound.{u, v} L' := by
  intro U _ _ S K hSK ε hε
  filter_upwards [h U S K hSK ε hε] with n hn σ I Acc c hfan hS
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (sub_le_sub_right hL ε) (Nat.cast_nonneg n))
    (hn σ I Acc c hfan hS)

/-- **The worst-case claim with coefficient `L`.** Let `U` be a finite alphabet with at least
two symbols, and let `S_n ⊆ U^n` be `K_n`-rectangle-free sets with `log K_n = o(n)` and
`n log |U| - log |S_n| = o(n)`. Then for every `ε > 0` and all large `n`, every circuit of fan-in
at most two deciding `S_n`, over any basis and interpretation on `U`, has more than `(L - ε) n`
gates of positive arity.

The alphabet lives in the universe `u` and the basis in the universe `v`. -/
def CircuitLowerBound (L : ℝ) : Prop :=
  ∀ (U : Type u) [Finite U] [Nontrivial U] (S : ∀ n, Set (Fin n → U)) (K : ℕ → ℕ),
    DenseRectangleFree S K →
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 2 → c.Decides I Acc (S n) →
        (L - ε) * n < c.innerSize

/-- Every multiary lower bound implies the corresponding `innerSize` lower bound. -/
theorem MultiaryLowerBound.circuitLowerBound {L : ℝ} (h : MultiaryLowerBound.{u, v} L) :
    CircuitLowerBound.{u, v} L := by
  intro U _ _ S K hSK ε hε
  filter_upwards [h U S K hSK ε hε] with n hn σ I Acc c hfan hS
  exact (hn σ I Acc c hfan hS).trans_le (Nat.cast_le.mpr c.multiarySize_le_innerSize)

/-- A circuit lower bound holds for every smaller coefficient. -/
theorem CircuitLowerBound.mono {L L' : ℝ} (h : CircuitLowerBound.{u, v} L) (hL : L' ≤ L) :
    CircuitLowerBound.{u, v} L' := by
  intro U _ _ S K hSK ε hε
  filter_upwards [h U S K hSK ε hε] with n hn σ I Acc c hfan hS
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (sub_le_sub_right hL ε) (Nat.cast_nonneg n))
    (hn σ I Acc c hfan hS)

/-- **The multiary frontier lower bound as a bundled claim.** If subcubic graphs have layouts of
width `(A + o(1)) β₁ + o(|V|)` (`LayoutBound 3 A`), then circuits of fan-in at most two deciding
dense rectangle-free sets need more than `(1 + 1/A - ε) n` multiary gates. -/
theorem multiaryLowerBound_of_layoutBound {A : ℝ} (hA : 0 < A) (hlayout : LayoutBound 3 A) :
    MultiaryLowerBound.{u, v} (1 + 1 / A) :=
  fun _ _ _ _ _ hSK _ hε => eventually_lt_multiarySize hA hlayout hSK hε

/-- **The frontier lower bound as a bundled claim.** If subcubic graphs have layouts of width
`(A + o(1)) β₁ + o(|V|)` (`LayoutBound 3 A`), then circuits of fan-in at most two deciding dense
rectangle-free sets need more than `(1 + 1/A - ε) n` inner gates. -/
theorem circuitLowerBound_of_layoutBound {A : ℝ} (hA : 0 < A) (hlayout : LayoutBound 3 A) :
    CircuitLowerBound.{u, v} (1 + 1 / A) :=
  (multiaryLowerBound_of_layoutBound hA hlayout).circuitLowerBound

end Cslib.Circuits.Frontier
