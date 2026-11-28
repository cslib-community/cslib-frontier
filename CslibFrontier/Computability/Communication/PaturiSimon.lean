/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.SignRank
public import CslibFrontier.Computability.Communication.UnboundedError
import CslibFrontier.Foundations.Data.BitString.Basic
import CslibFrontier.Foundations.Data.Nat.Power
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Rank

/-!
# The Paturi–Simon theorem

The unbounded-error communication complexity of a Boolean function `f` on finite sets is
determined, up to an additive constant, by the sign-rank of `f`
[Paturi and Simon][PaturiSimon1986]: in the form of
[Sherstov and Wu, Theorem 2.16][SherstovWu2019], `log rk±(f) ≤ UPP(f) ≤ log rk±(f) + 2`. Here
`⌈log₂ (signRank f)⌉ ≤ uppComplexityFun f ≤ ⌊log₂ (signRank f)⌋ + 2`
(`PrivateCoin.clog_signRank_le_uppComplexityFun_le`).

*Lower bound.* For a private-coin protocol, the number of random strings `(s, t)` on which it
reaches a leaf factors as a product of a count depending on Alice's input and one depending on
Bob's. Hence the signed vote `∑ s, ∑ t, ±1` of the protocol is a matrix of rank at most the number
of leaves (`Protocol.rank_sum_comp_run_le`), and when the error is less than `1 / 2` it
sign-represents `f` (`PrivateCoin.errorProb_lt_half_iff`). So a protocol of depth `d` has
`signRank f ≤ 2 ^ d` (`PrivateCoin.signRank_le_leafCount`,
`PrivateCoin.clog_signRank_le_uppComplexityFun`). Moreover, because the output at each leaf is fixed
by the transcript, every subtree of depth at most one depends on at most one player and contributes
a matrix of rank at most one, sharpening the rank bound to `2 ^ (d - 1)`
(`Protocol.rank_sum_comp_run_le_two_pow_sub_one`) and giving
`⌈log₂ (signRank f)⌉ + 1 ≤ uppComplexityFun f` whenever `2 ≤ signRank f`
(`PrivateCoin.clog_signRank_add_one_le_depth`,
`PrivateCoin.clog_signRank_add_one_le_uppComplexityFun`). The lower bounds need only Bob's inputs
to be finite.

*Upper bound.* Take an integer sign-representation `U * V` through `r = signRank f` dimensions
(`exists_int_mul_signRepresents`). Alice draws an index from `Option (Fin r)` with dyadic
probabilities affine in her row of `U`, and sends it in `⌈log₂ (r + 1)⌉` bits; Bob answers `true`
with a dyadic probability affine in his column of `V`. The bias of the answer is a positive multiple
of `(U * V) x y`, so it has the right sign (`PrivateCoin.exists_solvesUnbounded_depth_le`,
`PrivateCoin.uppComplexityFun_le_log_signRank_add_two`). All probabilities are dyadic, so finitely
many private random bits suffice; the lower bound holds for any finite number of them.

As a consequence equality on a finite set `X`, which needs `⌈log₂ |X|⌉ + 1` bits deterministically
when `|X| ≥ 2` (`ecomplexityFun_equality`), needs at most three with unbounded error
(`PrivateCoin.uppComplexityFun_equality_le_three`), and on three or more inputs it costs three bits
(`PrivateCoin.uppComplexityFun_equality_eq_three`).

The cost model is that of `PrivateCoin`: the depth of the protocol tree, with the output at the
leaves known to both players and private random strings of finite, unbounded length. Sherstov and
Wu allow unlimited private random bits and let Bob output locally without sending the final bit;
the bounds proved here are stated for leaf-output protocols with finitely many random bits.

## Main results

* `Cslib.Communication.Protocol.rank_sum_comp_run_le`,
  `Cslib.Communication.Protocol.rank_sum_comp_run_le_two_pow_sub_one`: the leaf and depth rank
  bounds for averaged protocols.
* `Cslib.Communication.PrivateCoin.errorProb_lt_half_iff`: unbounded-error correctness as a sign
  condition on the signed vote.
* `Cslib.Communication.PrivateCoin.signRank_le_leafCount`,
  `Cslib.Communication.PrivateCoin.clog_signRank_le_uppComplexityFun`,
  `Cslib.Communication.PrivateCoin.clog_signRank_add_one_le_uppComplexityFun`: the lower bounds.
* `Cslib.Communication.PrivateCoin.exists_solvesUnbounded_depth_le`,
  `Cslib.Communication.PrivateCoin.uppComplexityFun_le_log_signRank_add_two`: the upper bound.
* `Cslib.Communication.PrivateCoin.clog_signRank_le_uppComplexityFun_le`: the Paturi–Simon theorem.
* `Cslib.Communication.PrivateCoin.uppComplexityFun_equality_le_three`,
  `Cslib.Communication.PrivateCoin.uppComplexityFun_equality_eq_three`: equality with unbounded
  error.

## References

* [R. Paturi and J. Simon, *Probabilistic communication complexity*][PaturiSimon1986]
* [A. A. Sherstov and P. Wu, *Near-optimal lower bounds on the threshold degree and sign-rank of
  AC⁰*][SherstovWu2019]
-/

open Finset Matrix

public section

namespace Cslib.Communication

variable {X Y X' Y' Z : Type*}

namespace Protocol

/-- **The rank bound for averaged protocols.** For a protocol `p`, finite sets `S` and `T` of
random choices, maps `α` and `β` into Alice's and Bob's inputs and a relabelling `g` of the
outputs, the matrix with entry `∑ s, ∑ t, g (p.run (α x s) (β y t))` at `x` and `y` has rank at
most the number of leaves of `p`: on each leaf rectangle the sum factors as the number of `s` with
`α x s` on Alice's side times the number of `t` with `β y t` on Bob's side. -/
theorem rank_sum_comp_run_le {S T : Type*} [Fintype S] [Fintype T] [Finite Y]
    (p : Protocol X' Y' Z) (α : X → S → X') (β : Y → T → Y') (g : Z → ℝ) :
    (Matrix.of fun x y => ∑ s, ∑ t, g (p.run (α x s) (β y t))).rank ≤ p.leafCount := by
  classical
  let U : Matrix X (Fin p.leafCount) ℝ := Matrix.of fun x i => #{s | α x s ∈ p.leafAlice i}
  let V : Matrix (Fin p.leafCount) Y ℝ :=
    Matrix.of fun i y => #{t | β y t ∈ p.leafBob i} * g (p.leafOutput i)
  have hUV : (Matrix.of fun x y => ∑ s, ∑ t, g (p.run (α x s) (β y t))) = U * V := by
    ext x y
    have key : ∀ s t, g (p.run (α x s) (β y t)) = ∑ i, (if α x s ∈ p.leafAlice i then (1 : ℝ)
        else 0) * ((if β y t ∈ p.leafBob i then 1 else 0) * g (p.leafOutput i)) := by
      intro s t
      simp only [ite_mul, one_mul, zero_mul, ← ite_and, ← leaf_eq_iff, sum_ite_eq, mem_univ,
        ite_true]
      rw [run_eq_leafOutput_leaf]
    simp only [Matrix.of_apply, Matrix.mul_apply, U, V, key, natCast_card_filter, sum_mul,
      mul_sum]
    exact ((sum_congr rfl fun s _ => sum_comm).trans sum_comm).trans
      (sum_congr rfl fun i _ => sum_comm)
  rw [hUV]
  exact (rank_mul_le_left U V).trans ((rank_le_card_width U).trans_eq (Fintype.card_fin _))

private theorem eq_output_of_depth_eq_zero {p : Protocol X' Y' Z} (h : p.depth = 0) :
    ∃ z, p = .output z := by
  cases p with
  | output z => exact ⟨z, rfl⟩
  | alice _ _ _ | bob _ _ _ => simp only [depth_alice, depth_bob] at h; omega

private theorem rank_sum_mul_comp_run_le {S T : Type*} [Fintype S] [Fintype T] [Finite Y]
    (p : Protocol X' Y' Z) (α : X → S → X') (β : Y → T → Y')
    (wA : X → S → ℝ) (wB : Y → T → ℝ) (g : Z → ℝ) :
    (Matrix.of fun x y => ∑ s, ∑ t, wA x s * (wB y t * g (p.run (α x s) (β y t)))).rank ≤
      2 ^ (p.depth - 1) := by
  have rank_le (F : X → Y → S → T → ℝ) (u : X → S → ℝ) (v : Y → T → ℝ) {k : ℕ}
      (h : ∀ x y s t, F x y s t = u x s * v y t) :
      (Matrix.of fun x y => ∑ s, ∑ t, F x y s t).rank ≤ 2 ^ k := by
    simp only [h, ← sum_mul_sum]
    exact (Matrix.rank_vecMulVec_le (fun x => ∑ s, u x s) fun y => ∑ t, v y t).trans
      Nat.one_le_two_pow
  induction p generalizing wA wB with
  | output z => exact rank_le _ wA (fun y t => wB y t * g z) fun _ _ _ _ => rfl
  | alice send p₀ p₁ ih₀ ih₁ =>
    by_cases hd : max p₀.depth p₁.depth = 0
    · obtain ⟨z₀, rfl⟩ := eq_output_of_depth_eq_zero (by omega : p₀.depth = 0)
      obtain ⟨z₁, rfl⟩ := eq_output_of_depth_eq_zero (by omega : p₁.depth = 0)
      exact rank_le _ (fun x s => wA x s * g (cond (send (α x s)) z₁ z₀)) wB fun _ _ _ _ => by
        simp only [run_alice, run_output]; ring
    · let wA₀ : X → S → ℝ := fun x s => if send (α x s) then 0 else wA x s
      let wA₁ : X → S → ℝ := fun x s => if send (α x s) then wA x s else 0
      have hsplit : (Matrix.of fun x y =>
            ∑ s, ∑ t, wA x s * (wB y t * g (run (.alice send p₀ p₁) (α x s) (β y t)))) =
          (Matrix.of fun x y => ∑ s, ∑ t, wA₀ x s * (wB y t * g (p₀.run (α x s) (β y t)))) +
            Matrix.of fun x y => ∑ s, ∑ t, wA₁ x s * (wB y t * g (p₁.run (α x s) (β y t))) := by
        ext x y
        simp only [Matrix.of_apply, Matrix.add_apply, ← sum_add_distrib]
        refine sum_congr rfl fun s _ => sum_congr rfl fun t _ => ?_
        cases h : send (α x s) <;> simp [wA₀, wA₁, h]
      rw [hsplit, depth_alice]
      exact (Matrix.rank_add_le _ _).trans
        ((Nat.add_le_two_pow_max_succ (ih₀ wA₀ wB) (ih₁ wA₁ wB)).trans_eq (by congr 1; omega))
  | bob send p₀ p₁ ih₀ ih₁ =>
    by_cases hd : max p₀.depth p₁.depth = 0
    · obtain ⟨z₀, rfl⟩ := eq_output_of_depth_eq_zero (by omega : p₀.depth = 0)
      obtain ⟨z₁, rfl⟩ := eq_output_of_depth_eq_zero (by omega : p₁.depth = 0)
      exact rank_le _ wA (fun y t => wB y t * g (cond (send (β y t)) z₁ z₀)) fun _ _ _ _ => rfl
    · let wB₀ : Y → T → ℝ := fun y t => if send (β y t) then 0 else wB y t
      let wB₁ : Y → T → ℝ := fun y t => if send (β y t) then wB y t else 0
      have hsplit : (Matrix.of fun x y =>
            ∑ s, ∑ t, wA x s * (wB y t * g (run (.bob send p₀ p₁) (α x s) (β y t)))) =
          (Matrix.of fun x y => ∑ s, ∑ t, wA x s * (wB₀ y t * g (p₀.run (α x s) (β y t)))) +
            Matrix.of fun x y => ∑ s, ∑ t, wA x s * (wB₁ y t * g (p₁.run (α x s) (β y t))) := by
        ext x y
        simp only [Matrix.of_apply, Matrix.add_apply, ← sum_add_distrib]
        refine sum_congr rfl fun s _ => sum_congr rfl fun t _ => ?_
        cases h : send (β y t) <;> simp [wB₀, wB₁, h]
      rw [hsplit, depth_bob]
      exact (Matrix.rank_add_le _ _).trans
        ((Nat.add_le_two_pow_max_succ (ih₀ wA wB₀) (ih₁ wA wB₁)).trans_eq (by congr 1; omega))

/-- For a leaf-output protocol `p`, finite sets `S` and `T` of random choices, maps `α` and `β`
into Alice's and Bob's inputs and a relabelling `g` of the outputs, the matrix with entry
`∑ s, ∑ t, g (p.run (α x s) (β y t))` at `x` and `y` has rank at most `2 ^ (p.depth - 1)`: every
subtree of depth at most one depends on at most one player, so it contributes a matrix of rank at
most one. -/
theorem rank_sum_comp_run_le_two_pow_sub_one {S T : Type*} [Fintype S] [Fintype T] [Finite Y]
    (p : Protocol X' Y' Z) (α : X → S → X') (β : Y → T → Y') (g : Z → ℝ) :
    (Matrix.of fun x y => ∑ s, ∑ t, g (p.run (α x s) (β y t))).rank ≤ 2 ^ (p.depth - 1) := by
  simpa only [one_mul] using
    rank_sum_mul_comp_run_le p α β (fun _ _ => 1) (fun _ _ => 1) g

end Protocol

private theorem exists_le_two_pow (K : ℤ) : ∃ α : ℕ, K ≤ 2 ^ α :=
  ⟨K.toNat, (Int.self_le_toNat K).trans (by exact_mod_cast (Nat.lt_two_pow_self).le)⟩

/-- **Weights from an integer factorization.** From integer matrices `U` and `V` through `r`
dimensions, build weights `w x j ≥ 0` summing to `2 ^ α` over `j : Option (Fin r)` and thresholds
`0 ≤ c y j ≤ 2 ^ β` with `∑ j, w x j * (2 ^ β - 2 * c y j) = 2 ^ (α + 1) * (U * V) x y`. With `T`
and `Q` bounding the entries of `U` and `V`, take `w x (some i) = U x i + T`, put the remaining
weight on `none`, and let `c y j` be `2 ^ L + T * ∑ i, V i y`, minus `2 ^ α * V i y` when
`j = some i`. -/
private theorem exists_int_weights [Finite X] [Finite Y] {r : ℕ} (U : Matrix X (Fin r) ℤ)
    (V : Matrix (Fin r) Y ℤ) :
    ∃ (α β : ℕ) (w : X → Option (Fin r) → ℤ) (c : Y → Option (Fin r) → ℤ),
      (∀ x j, 0 ≤ w x j) ∧ (∀ x, ∑ j, w x j = 2 ^ α) ∧ (∀ y j, 0 ≤ c y j ∧ c y j ≤ 2 ^ β) ∧
      ∀ x y, ∑ j, w x j * (2 ^ β - 2 * c y j) = 2 ^ (α + 1) * (U * V) x y := by
  have := Fintype.ofFinite X
  have := Fintype.ofFinite Y
  set T : ℤ := ∑ x, ∑ i, |U x i| with hT
  set Q : ℤ := ∑ i, ∑ y, |V i y| with hQ
  have hT0 : 0 ≤ T := sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _
  have hUT : ∀ x i, |U x i| ≤ T := fun x i =>
    (single_le_sum (f := fun i => |U x i|) (fun _ _ => abs_nonneg _) (mem_univ i)).trans
      (single_le_sum (f := fun x => ∑ i, |U x i|)
        (fun _ _ => sum_nonneg fun _ _ => abs_nonneg _) (mem_univ x))
  have hVQ : ∀ i y, |V i y| ≤ Q := fun i y =>
    (single_le_sum (f := fun y => |V i y|) (fun _ _ => abs_nonneg _) (mem_univ y)).trans
      (single_le_sum (f := fun i => ∑ y, |V i y|)
        (fun _ _ => sum_nonneg fun _ _ => abs_nonneg _) (mem_univ i))
  have hSQ : ∀ y, |∑ i, V i y| ≤ Q := fun y =>
    (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ =>
      single_le_sum (f := fun y => |V i y|) (fun _ _ => abs_nonneg _) (mem_univ y))
  have hQ0 : 0 ≤ Q := sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _
  obtain ⟨α, hα⟩ := exists_le_two_pow (2 * r * T)
  obtain ⟨L, hL⟩ := exists_le_two_pow (T * Q + 2 ^ α * Q)
  let S : Y → ℤ := fun y => ∑ i, V i y
  refine ⟨α, L + 1,
    fun x j => Option.elim j (2 ^ α - ∑ i, (U x i + T)) fun i => U x i + T,
    fun y j => Option.elim j (2 ^ L + T * S y) fun i => 2 ^ L + T * S y - 2 ^ α * V i y,
    ?_, ?_, ?_, ?_⟩
  · intro x j
    cases j with
    | none =>
      have : ∑ i, (U x i + T) ≤ ∑ _i : Fin r, 2 * T := sum_le_sum fun i _ => by
        linarith [(abs_le.mp (hUT x i)).2]
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at this
      simp only [Option.elim]
      linarith
    | some i =>
      simp only [Option.elim]
      linarith [(abs_le.mp (hUT x i)).1]
  · intro x
    rw [Fintype.sum_option]
    simp only [Option.elim]
    ring
  · intro y j
    have h1 := abs_le.mp (hSQ y)
    have h2 : -(T * Q) ≤ T * S y ∧ T * S y ≤ T * Q :=
      ⟨by nlinarith [h1.1], mul_le_mul_of_nonneg_left h1.2 hT0⟩
    have hα0 : (0 : ℤ) ≤ 2 ^ α := by positivity
    rw [pow_succ]
    cases j with
    | none =>
      simp only [Option.elim]
      constructor <;> nlinarith
    | some i =>
      have h3 := abs_le.mp (hVQ i y)
      have h4 : -(2 ^ α * Q) ≤ 2 ^ α * V i y ∧ 2 ^ α * V i y ≤ 2 ^ α * Q :=
        ⟨by nlinarith [h3.1], mul_le_mul_of_nonneg_left h3.2 hα0⟩
      simp only [Option.elim]
      constructor <;> nlinarith
  · intro x y
    rw [Fintype.sum_option]
    simp only [Option.elim]
    have e1 : ∀ i, (U x i + T) * (2 ^ (L + 1) - 2 * (2 ^ L + T * S y - 2 ^ α * V i y)) =
        (U x i + T) * -(2 * T * S y) +
          (2 ^ (α + 1) * (U x i * V i y) + 2 ^ (α + 1) * T * V i y) := fun i => by ring
    simp only [e1, sum_add_distrib, ← sum_mul, ← mul_sum, Matrix.mul_apply]
    simp only [S]
    ring

namespace PrivateCoin

variable {a b : ℕ}

/-- **The bias identity.** For a private-coin protocol computing a Boolean value, the number of
random strings on which it answers `false`, minus the number on which it answers `true`, multiplied
by the sign of `f x y`, is `2 ^ a * 2 ^ b * (1 - 2 * errorProb)`. -/
theorem signMatrix_mul_sum (P : PrivateCoin a b X Y Bool) (f : X → Y → Bool) (x : X) (y : Y) :
    signMatrix ℝ f x y * ∑ s, ∑ t, BitString.signVal (P.run (x, s) (y, t)) =
      2 ^ a * 2 ^ b * (1 - 2 * P.errorProb (fun x y z => f x y = z) x y) := by
  have h : ∀ s t, signMatrix ℝ f x y * BitString.signVal (P.run (x, s) (y, t)) =
      1 - 2 * (if ¬f x y = P.run (x, s) (y, t) then 1 else 0) := by
    intro s t
    rw [signMatrix_apply_eq_signVal, BitString.signVal_mul_signVal]
    split_ifs <;> norm_num
  rw [errorProb_eq_card, mul_sum]
  simp only [mul_sum, h]
  rw [← Fintype.sum_prod_type' (f := fun s t => 1 - 2 * (if ¬f x y = P.run (x, s) (y, t) then
    (1 : ℝ) else 0)), sum_sub_distrib, ← mul_sum, sum_boole, sum_const, card_univ,
    Fintype.card_prod, BitString.card, BitString.card, nsmul_eq_mul, mul_one]
  have : (0 : ℝ) < 2 ^ a * 2 ^ b := by positivity
  push_cast
  field_simp

/-- A private-coin protocol for `f` has error less than `1 / 2` on `x` and `y` exactly when its
signed vote `∑ s, ∑ t, ±1` has the sign of `signMatrix ℝ f x y`. -/
theorem errorProb_lt_half_iff (P : PrivateCoin a b X Y Bool) (f : X → Y → Bool) (x : X) (y : Y) :
    P.errorProb (fun x y z => f x y = z) x y < 1 / 2 ↔
      0 < signMatrix ℝ f x y * ∑ s, ∑ t, BitString.signVal (P.run (x, s) (y, t)) := by
  rw [signMatrix_mul_sum]
  have : (0 : ℝ) < 2 ^ a * 2 ^ b := by positivity
  rw [mul_pos_iff_of_pos_left this]
  constructor <;> intro h <;> linarith

/-- **Paturi–Simon, lower bound (leaf form).** A private-coin protocol computing `f` with
unbounded error has at least `signRank f` leaves: the signed votes form a matrix that
sign-represents `f` and has rank at most the number of leaves (`Protocol.rank_sum_comp_run_le`). -/
theorem signRank_le_leafCount [Finite Y] {f : X → Y → Bool} (P : PrivateCoin a b X Y Bool)
    (hP : P.SolvesUnbounded (fun x y z => f x y = z) Set.univ Set.univ) :
    signRank f ≤ P.leafCount := by
  refine (signRank_le_rank (A := Matrix.of fun x y => ∑ s, ∑ t,
    BitString.signVal (P.run (x, s) (y, t))) fun x y => ?_).trans
    (Protocol.rank_sum_comp_run_le (X := X) (Y := Y) (p := P) (fun x s => (x, s))
      (fun y t => (y, t)) BitString.signVal)
  exact (errorProb_lt_half_iff P f x y).mp (hP x trivial y trivial)

/-- A private-coin protocol computing `f` with unbounded error sends at least
`⌈log₂ (signRank f)⌉` bits. -/
theorem clog_signRank_le_depth [Finite Y] {f : X → Y → Bool} (P : PrivateCoin a b X Y Bool)
    (hP : P.SolvesUnbounded (fun x y z => f x y = z) Set.univ Set.univ) :
    Nat.clog 2 (signRank f) ≤ P.depth :=
  Nat.clog_le_of_le_pow
    ((signRank_le_leafCount P hP).trans (Protocol.leafCount_le_two_pow_depth P))

/-- **Paturi–Simon, lower bound**: the unbounded-error complexity of `f` is at least
`⌈log₂ (signRank f)⌉` [Sherstov and Wu, Theorem 2.16][SherstovWu2019]. -/
theorem clog_signRank_le_uppComplexityFun [Finite Y] (f : X → Y → Bool) :
    (Nat.clog 2 (signRank f) : ℕ∞) ≤ uppComplexityFun f :=
  le_uppComplexityFun_iff.mpr fun _ _ P hP => by exact_mod_cast clog_signRank_le_depth P hP

/-- When `2 ≤ signRank f`, a private-coin protocol computing `f` with unbounded error sends at
least `⌈log₂ (signRank f)⌉ + 1` bits: its signed vote matrix sign-represents `f` and has rank at
most `2 ^ (P.depth - 1)` (`Protocol.rank_sum_comp_run_le_two_pow_sub_one`). -/
theorem clog_signRank_add_one_le_depth [Finite Y] {f : X → Y → Bool}
    (P : PrivateCoin a b X Y Bool)
    (hP : P.SolvesUnbounded (fun x y z => f x y = z) Set.univ Set.univ) (hf : 2 ≤ signRank f) :
    Nat.clog 2 (signRank f) + 1 ≤ P.depth := by
  have hle : signRank f ≤ 2 ^ (P.depth - 1) :=
    (signRank_le_rank (A := Matrix.of fun x y => ∑ s, ∑ t,
      BitString.signVal (P.run (x, s) (y, t))) fun x y =>
        (errorProb_lt_half_iff P f x y).mp (hP x trivial y trivial)).trans
      (Protocol.rank_sum_comp_run_le_two_pow_sub_one P (fun x s => (x, s))
        (fun y t => (y, t)) BitString.signVal)
  have hd : 1 ≤ P.depth := by
    by_contra h0
    have : P.depth - 1 = 0 := by omega
    rw [this, pow_zero] at hle
    omega
  have hclog : Nat.clog 2 (signRank f) ≤ P.depth - 1 := Nat.clog_le_of_le_pow hle
  omega

/-- In the leaf-output `PrivateCoin` model, when `2 ≤ signRank f`, the unbounded-error complexity
of `f` is at least `⌈log₂ (signRank f)⌉ + 1`. With `uppComplexityFun_le_log_signRank_add_two` this
gives `uppComplexityFun f = ⌊log₂ (signRank f)⌋ + 2` whenever `signRank f` is not a power of two;
`2 ≤ signRank f` is needed since a constant function has sign-rank `1` and complexity `0`. -/
theorem clog_signRank_add_one_le_uppComplexityFun [Finite Y] {f : X → Y → Bool}
    (hf : 2 ≤ signRank f) :
    (Nat.clog 2 (signRank f) + 1 : ℕ∞) ≤ uppComplexityFun f :=
  le_uppComplexityFun_iff.mpr fun _ _ P hP =>
    by exact_mod_cast clog_signRank_add_one_le_depth P hP hf

/-! ### Upper bound -/

/-- **Sampling with dyadic weights.** Weights `w` summing to `2 ^ α` are realized by a map from
`α` random bits: each `i` has exactly `w i` preimages. -/
private theorem exists_sampler {ι : Type*} [Fintype ι] {α : ℕ} (w : ι → ℕ)
    (hw : ∑ i, w i = 2 ^ α) :
    ∃ σ : BitString α → ι, ∀ F : ι → ℝ, ∑ s, F (σ s) = ∑ i, (w i : ℝ) * F i := by
  have hcard : Fintype.card (BitString α) = Fintype.card (Σ i, Fin (w i)) := by
    rw [BitString.card, Fintype.card_sigma]
    simp only [Fintype.card_fin, hw]
  let e := Fintype.equivOfCardEq hcard
  refine ⟨fun s => (e s).1, fun F => ?_⟩
  rw [e.sum_comp (fun p => F p.1), Fintype.sum_sigma]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Simulating weights by a protocol.** Alice draws `i` with probability `w x i / 2 ^ α` and
sends it in `n` bits; Bob answers `true` with probability `c y i / 2 ^ β`. The signed vote of the
protocol is `∑ i, w x i * (2 ^ β - 2 * c y i)`. -/
private theorem exists_protocol_of_weights {ι : Type*} [Fintype ι] [Nonempty ι] {n α β : ℕ}
    (hι : Fintype.card ι ≤ 2 ^ n) (w : X → ι → ℕ) (hw : ∀ x, ∑ i, w x i = 2 ^ α)
    (c : Y → ι → ℕ) (hc : ∀ y i, c y i ≤ 2 ^ β) :
    ∃ P : PrivateCoin α β X Y Bool, P.depth ≤ n + 1 ∧ ∀ x y,
      ∑ s, ∑ t, BitString.signVal (P.run (x, s) (y, t)) =
        ∑ i, (w x i : ℝ) * (2 ^ β - 2 * c y i) := by
  classical
  choose σ hσ using fun x => exists_sampler (w x) (hw x)
  choose τ hτ using fun y i => exists_sampler (α := β)
    (fun b : Bool => if b then c y i else 2 ^ β - c y i)
    (by rw [Fintype.sum_bool]; simp only [ite_true, Bool.false_eq_true, ite_false]
        have := hc y i; omega)
  obtain ⟨e⟩ : Nonempty (ι ↪ BitString n) :=
    Function.Embedding.nonempty_of_card_le (by rwa [BitString.card])
  refine ⟨Protocol.aliceSend n (fun xs => e (σ xs.1 xs.2)) fun m =>
    Protocol.bob (fun yt => τ yt.1 (Function.invFun e m) yt.2) (.output false) (.output true),
    ?_, fun x y => ?_⟩
  · exact Protocol.depth_aliceSend_le fun m => by simp
  · simp only [Protocol.run_aliceSend, Protocol.run_bob, Protocol.run_output,
      Function.leftInverse_invFun e.injective _]
    have hb (i) : ∑ t, BitString.signVal (cond (τ y i t) true false) = 2 ^ β - 2 * c y i := by
      have := hτ y i BitString.signVal
      simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false,
        BitString.signVal_true, BitString.signVal_false, Nat.cast_sub (hc y i)] at this
      simp only [Bool.cond_true_left, Bool.or_false, this]
      push_cast
      ring
    simp only [hb]
    exact hσ x fun i => 2 ^ β - 2 * (c y i : ℝ)

/-- **Paturi–Simon, upper bound (protocol form).** On finite inputs, `f` has a private-coin
protocol with unbounded error that sends at most `⌈log₂ (signRank f + 1)⌉ + 1` bits: Alice sends
an index in `Option (Fin (signRank f))` drawn according to her row of an integer sign-representation
and Bob answers with one biased bit. -/
theorem exists_solvesUnbounded_depth_le [Finite X] [Finite Y] (f : X → Y → Bool) :
    ∃ (a b : ℕ) (P : PrivateCoin a b X Y Bool),
      P.SolvesUnbounded (fun x y z => f x y = z) Set.univ Set.univ ∧
        P.depth ≤ Nat.clog 2 (signRank f + 1) + 1 := by
  obtain ⟨U₀, V₀, h₀⟩ := exists_mul_signRepresents f
  obtain ⟨U, V, hUV⟩ := exists_int_mul_signRepresents h₀
  obtain ⟨α, β, w, c, hw0, hw, hc, hid⟩ := exists_int_weights U V
  have hcard : Fintype.card (Option (Fin (signRank f))) ≤ 2 ^ Nat.clog 2 (signRank f + 1) := by
    rw [Fintype.card_option, Fintype.card_fin]
    exact Nat.le_pow_clog one_lt_two _
  obtain ⟨P, hdepth, hrun⟩ := exists_protocol_of_weights hcard (fun x j => (w x j).toNat)
    (fun x => by
      have : ((∑ j, (w x j).toNat : ℕ) : ℤ) = ((2 ^ α : ℕ) : ℤ) := by
        push_cast
        rw [← hw x]
        exact sum_congr rfl fun j _ => Int.toNat_of_nonneg (hw0 x j)
      exact_mod_cast this)
    (fun y j => (c y j).toNat)
    (fun y j => by
      have : (((c y j).toNat : ℕ) : ℤ) ≤ ((2 ^ β : ℕ) : ℤ) := by grind
      exact_mod_cast this)
  refine ⟨α, β, P, fun x _ y _ => ?_, hdepth⟩
  rw [errorProb_lt_half_iff, hrun]
  have hid' : ∑ j, ((w x j).toNat : ℝ) * (2 ^ β - 2 * ((c y j).toNat : ℝ)) =
      2 ^ (α + 1) * ((U * V) x y : ℝ) := by
    have : ∑ j, ((w x j : ℤ) : ℝ) * (2 ^ β - 2 * ((c y j : ℤ) : ℝ)) =
        2 ^ (α + 1) * ((U * V) x y : ℝ) := by exact_mod_cast hid x y
    rw [← this]
    refine sum_congr rfl fun j _ => ?_
    rw [← Int.cast_natCast, ← Int.cast_natCast (R := ℝ) (c y j).toNat,
      Int.toNat_of_nonneg (hw0 x j), Int.toNat_of_nonneg (hc y j).1]
  rw [hid', mul_left_comm]
  exact mul_pos (by positivity) (hUV x y)

/-- **Paturi–Simon, upper bound**: on finite inputs, the unbounded-error complexity of `f` is at
most `⌊log₂ (signRank f)⌋ + 2` [Sherstov and Wu, Theorem 2.16][SherstovWu2019]. -/
theorem uppComplexityFun_le_log_signRank_add_two [Finite X] [Finite Y] (f : X → Y → Bool) :
    uppComplexityFun f ≤ Nat.log 2 (signRank f) + 2 := by
  obtain ⟨a, b, P, hP, hd⟩ := exists_solvesUnbounded_depth_le f
  refine (uppComplexityFun_le_depth hP).trans ?_
  have : Nat.clog 2 (signRank f + 1) ≤ Nat.log 2 (signRank f) + 1 :=
    Nat.clog_le_of_le_pow (Nat.lt_pow_succ_log_self one_lt_two _)
  exact_mod_cast hd.trans (by omega)

/-- **The Paturi–Simon theorem**: on finite inputs, the unbounded-error communication complexity
of a Boolean function lies between `⌈log₂ (signRank f)⌉` and `⌊log₂ (signRank f)⌋ + 2`
[Sherstov and Wu, Theorem 2.16][SherstovWu2019]. -/
theorem clog_signRank_le_uppComplexityFun_le [Finite X] [Finite Y] (f : X → Y → Bool) :
    (Nat.clog 2 (signRank f) : ℕ∞) ≤ uppComplexityFun f ∧
      uppComplexityFun f ≤ Nat.log 2 (signRank f) + 2 :=
  ⟨clog_signRank_le_uppComplexityFun f, uppComplexityFun_le_log_signRank_add_two f⟩

/-- **Equality is cheap with unbounded error**: on any finite set, three bits suffice, since
equality has sign-rank at most three. Deterministically it needs `⌈log₂ |X|⌉ + 1` bits when
`|X| ≥ 2` (`ecomplexityFun_equality`). -/
theorem uppComplexityFun_equality_le_three [Finite X] [DecidableEq X] :
    uppComplexityFun (equality (X := X)) ≤ 3 := by
  have := Fintype.ofFinite X
  obtain ⟨a, b, P, hP, hd⟩ := exists_solvesUnbounded_depth_le (equality (X := X))
  refine (uppComplexityFun_le_depth hP).trans ?_
  have h4 : Nat.clog 2 (signRank (equality (X := X)) + 1) ≤ 2 :=
    Nat.clog_le_of_le_pow (by have := signRank_equality_le_three (Y := X); omega)
  exact_mod_cast hd.trans (by omega)

private theorem not_alice_solvesUnbounded_equality_fin_three {a b : ℕ}
    (send : Fin 3 × BitString a → Bool)
    (p₀ p₁ : PrivateCoin a b (Fin 3) (Fin 3) Bool) (hp₀ : p₀.depth ≤ 1) (hp₁ : p₁.depth ≤ 1) :
    ¬SolvesUnbounded (a := a) (b := b) (Protocol.alice send p₀ p₁)
      (fun x y z => equality x y = z) Set.univ Set.univ := by
  intro hP
  let V : Fin 3 → Fin 3 → ℝ := fun x y =>
    ∑ s, ∑ t, BitString.signVal ((Protocol.alice send p₀ p₁).run (x, s) (y, t))
  have hsign : SignRepresents (Matrix.of V) equality := fun x y =>
    (errorProb_lt_half_iff _ equality x y).mp (hP x trivial y trivial)
  have hdiag (x : Fin 3) : V x x < 0 := hsign.neg_of_true (by simp [equality])
  have hoff {x y : Fin 3} (hxy : x ≠ y) : 0 < V x y := hsign.pos_of_false (by simp [equality, hxy])
  have sum_depth_le_one (q : PrivateCoin a b (Fin 3) (Fin 3) Bool) (hq : q.depth ≤ 1) :
      (∃ g : Fin 3 → ℝ, ∀ x s y, ∑ t, BitString.signVal (q.run (x, s) (y, t)) = g y) ∨
      (∃ h : Fin 3 → BitString a → ℝ,
        ∀ x s y, ∑ t, BitString.signVal (q.run (x, s) (y, t)) = h x s) := by
    rcases q with z | ⟨sA, q₀, q₁⟩ | ⟨sB, q₀, q₁⟩
    · exact Or.inl ⟨fun _ => ∑ _t : BitString b, BitString.signVal z, fun _ _ _ => rfl⟩
    · simp only [Protocol.depth_alice] at hq
      obtain ⟨z₀, rfl⟩ := Protocol.eq_output_of_depth_eq_zero (by omega : q₀.depth = 0)
      obtain ⟨z₁, rfl⟩ := Protocol.eq_output_of_depth_eq_zero (by omega : q₁.depth = 0)
      exact Or.inr ⟨fun x s => ∑ _t : BitString b, BitString.signVal (cond (sA (x, s)) z₁ z₀),
        fun _ _ _ => rfl⟩
    · simp only [Protocol.depth_bob] at hq
      obtain ⟨z₀, rfl⟩ := Protocol.eq_output_of_depth_eq_zero (by omega : q₀.depth = 0)
      obtain ⟨z₁, rfl⟩ := Protocol.eq_output_of_depth_eq_zero (by omega : q₁.depth = 0)
      exact Or.inl ⟨fun y => ∑ t : BitString b, BitString.signVal (cond (sB (y, t)) z₁ z₀),
        fun _ _ _ => rfl⟩
  have hV (x y : Fin 3) : V x y =
      (∑ s with send (x, s) = false, ∑ t, BitString.signVal (p₀.run (x, s) (y, t))) +
        ∑ s with send (x, s) = true, ∑ t, BitString.signVal (p₁.run (x, s) (y, t)) := by
    classical
    simp only [V, Protocol.run_alice]
    rw [← sum_filter_add_sum_filter_not univ (fun s => send (x, s) = false)]
    congr 1 <;> refine sum_congr (by ext; simp) fun s hs => ?_ <;> rw [(mem_filter.mp hs).2] <;> rfl
  have no_shift (q g w : Fin 3 → ℝ) (hq : ∀ x, 0 ≤ q x)
      (heq : ∀ x y, V x y = q x * g y + w x) : False := by
    rcases le_total (g 0) (g 1) with h | h <;>
      linarith [heq 0 0, heq 0 1, heq 1 0, heq 1 1, hdiag 0, hdiag 1,
        hoff (by decide : (0 : Fin 3) ≠ 1), hoff (by decide : (1 : Fin 3) ≠ 0),
        mul_nonneg (hq 0) (sub_nonneg.2 h), mul_nonneg (hq 1) (sub_nonneg.2 h)]
  classical
  let n₀ : Fin 3 → ℝ := fun x => #{s | send (x, s) = false}
  let n₁ : Fin 3 → ℝ := fun x => #{s | send (x, s) = true}
  have hn₀ (x : Fin 3) : 0 ≤ n₀ x := Nat.cast_nonneg _
  have hn₁ (x : Fin 3) : 0 ≤ n₁ x := Nat.cast_nonneg _
  rcases sum_depth_le_one p₀ hp₀ with ⟨g₀, hg₀⟩ | ⟨h₀, hh₀⟩ <;>
    rcases sum_depth_le_one p₁ hp₁ with ⟨g₁, hg₁⟩ | ⟨h₁, hh₁⟩
  · have hn_sum (x : Fin 3) : n₀ x + n₁ x = 2 ^ a := by
      have hc := card_filter_add_card_filter_not (s := (univ : Finset (BitString a)))
        fun s => send (x, s) = false
      rw [card_univ, BitString.card] at hc
      simpa [n₀, n₁] using congrArg (Nat.cast (R := ℝ)) hc
    have haff (x y : Fin 3) : V x y = (2 ^ a - n₁ x) * g₀ y + n₁ x * g₁ y := by
      rw [hV, ← hn_sum x, add_sub_cancel_right]
      simp only [hg₀, hg₁, sum_const, nsmul_eq_mul]
      rfl
    have no_mid (i j k : Fin 3) (hij : i ≠ j) (hkj : k ≠ j)
        (h₁ : n₁ i ≤ n₁ j) (h₂ : n₁ j ≤ n₁ k) : False := by
      rcases le_total (g₀ j) (g₁ j) with h | h <;>
        linarith [haff i j, haff k j, haff j j, hoff hij, hoff hkj, hdiag j,
          mul_nonneg (sub_nonneg.2 h₁) (sub_nonneg.2 h),
          mul_nonneg (sub_nonneg.2 h₂) (sub_nonneg.2 h)]
    rcases le_total (n₁ 0) (n₁ 1) with h01 | h10 <;>
      rcases le_total (n₁ 1) (n₁ 2) with h12 | h21 <;>
      rcases le_total (n₁ 0) (n₁ 2) with h02 | h20
    · exact no_mid 0 1 2 (by decide) (by decide) h01 h12
    · exact no_mid 2 0 1 (by decide) (by decide) h20 h01
    · exact no_mid 0 2 1 (by decide) (by decide) h02 h21
    · exact no_mid 2 0 1 (by decide) (by decide) h20 h01
    · exact no_mid 1 0 2 (by decide) (by decide) h10 h02
    · exact no_mid 1 2 0 (by decide) (by decide) h12 h20
    · exact no_mid 2 1 0 (by decide) (by decide) h21 h10
    · exact no_mid 2 1 0 (by decide) (by decide) h21 h10
  · refine no_shift n₀ g₀ (fun x => ∑ s with send (x, s) = true, h₁ x s) hn₀ fun x y => ?_
    rw [hV]; simp only [hg₀, hh₁, sum_const, nsmul_eq_mul]; rfl
  · refine no_shift n₁ g₁ (fun x => ∑ s with send (x, s) = false, h₀ x s) hn₁ fun x y => ?_
    rw [hV, add_comm]; simp only [hh₀, hg₁, sum_const, nsmul_eq_mul]; rfl
  · refine no_shift 0 0
      (fun x => (∑ s with send (x, s) = false, h₀ x s) + ∑ s with send (x, s) = true, h₁ x s)
      (fun _ => le_rfl) fun x y => ?_
    rw [hV]; simp [hh₀, hh₁]

/-- In the leaf-output `PrivateCoin` model, computing equality with unbounded error on a finite set
with three or more elements costs three bits. For four or more inputs this follows at once from
`signRank_equality_eq_three` and `clog_signRank_add_one_le_uppComplexityFun`; on three inputs
`signRank` is two, and protocol-tree convexity rules out depth two. On two inputs two bits suffice
(`Fintype.card X = 2`). -/
theorem uppComplexityFun_equality_eq_three [Fintype X] [DecidableEq X] (hX : 2 < Fintype.card X) :
    uppComplexityFun (equality (X := X)) = 3 := by
  refine le_antisymm uppComplexityFun_equality_le_three ?_
  obtain ⟨e⟩ : Nonempty (Fin 3 ↪ X) :=
    Function.Embedding.nonempty_of_card_le (by rw [Fintype.card_fin]; omega)
  have heq : (fun x y : Fin 3 => equality (e x) (e y)) = equality := by
    ext x y; simp [equality, e.injective.eq_iff]
  refine le_trans ?_ (heq ▸ uppComplexityFun_comap_le equality e e)
  refine le_uppComplexityFun_iff.mpr fun a b P hP => ?_
  by_contra! hd
  have hd' : P.depth < 3 := by exact_mod_cast hd
  have h2 : 2 ≤ P.depth := by
    have hsr : 2 ≤ signRank (equality (X := Fin 3)) := two_le_signRank_equality (by decide)
    have := clog_signRank_add_one_le_depth P hP hsr
    have := Nat.clog_pos one_lt_two hsr
    omega
  rcases P with z | ⟨send, p₀, p₁⟩ | ⟨send, p₀, p₁⟩
  · simp only [Protocol.depth_output] at h2; omega
  · simp only [Protocol.depth_alice] at hd'
    exact not_alice_solvesUnbounded_equality_fin_three send p₀ p₁ (by omega) (by omega) hP
  · simp only [Protocol.depth_bob] at hd'
    have hswap : SolvesUnbounded (a := b) (b := a) (Protocol.alice send p₀.swap p₁.swap)
        (fun x y z => equality x y = z) Set.univ Set.univ := by
      intro x _ y _
      rw [errorProb_lt_half_iff (a := b) (b := a)]
      have hyx := (errorProb_lt_half_iff (Protocol.bob send p₀ p₁) equality y x).mp
        (hP y trivial x trivial)
      have heq_s : signMatrix ℝ equality x y = signMatrix ℝ equality y x := by
        simp [equality, eq_comm]
      have heq_r : ∑ t, ∑ s,
          BitString.signVal ((Protocol.alice send p₀.swap p₁.swap).run (x, t) (y, s)) =
          ∑ s, ∑ t, BitString.signVal ((Protocol.bob send p₀ p₁).run (y, s) (x, t)) := by
        rw [sum_comm]
        exact sum_congr rfl fun s _ => sum_congr rfl fun t _ =>
          congrArg BitString.signVal (Protocol.run_swap (Protocol.bob send p₀ p₁) (y, s) (x, t))
      rwa [heq_s, heq_r]
    exact not_alice_solvesUnbounded_equality_fin_three send p₀.swap p₁.swap
      (by rw [Protocol.depth_swap]; omega) (by rw [Protocol.depth_swap]; omega) hswap

end PrivateCoin

end Cslib.Communication

end
