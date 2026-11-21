/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.CountingSimulation.RootContractionFork
public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.Schedule

/-!
# The actual root taper supplies a balanced seed

Writing `q` for the number of source blocks, each row/column degree is bounded by
`Δ = 2(3k+1)m` and there are exactly `qΔ` numbered half-edges. At the depth-zero taper the
variance inequality reduces to `2 · 2^(24a) ≤ q`. The logarithmic block width gives
at most `q³` half-edges for sufficiently large source times, which proves this inequality.
-/

public section

namespace Cslib.Complexity.CountingSimulation

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapePTM _root_.Turing.MultiTapeATM
open Circuits.Frontier.ContractionSchedule

/-- For sufficiently large source clocks the actual depth-zero schedule satisfies the four-wise
variance inequality on the copied, subdivided, numbered root graph. -/
theorem exists_root_variance_threshold (k states : ℕ) : ∃ t₀, ∀ t ≥ t₀,
    let a := slotBits (rootEdges k states t) 0
    2 * (2 * (3 * k + 1) * rootCopies k states t) * (64 ^ (2 * a)) ^ 2 ≤
      rootEdges k states t := by
  obtain ⟨B, hB⟩ := exists_size_pow_le_numBlocks 1
  let G := 2 * (3 * k + 1) * (states + k + 4) * B
  let N := max 2 (2 * G)
  refine ⟨2 ^ (B * (N + 1)), fun t ht => ?_⟩
  let q := numBlocks t
  let M := rootEdges k states t
  let a := slotBits M 0
  have hs := hB t
  change ((t + 2).size + 1) ^ 1 ≤ B * (q + 1) at hs
  rw [pow_one] at hs
  have hbig : B * (N + 1) < (t + 2).size := Nat.lt_size.mpr (by omega)
  have hq : N ≤ q := by
    by_contra! hn
    have hmul : B * (q + 1) ≤ B * (N + 1) := Nat.mul_le_mul_left B (by omega)
    omega
  have htwo : 2 ≤ q := (Nat.le_max_left _ _).trans hq
  have hG : 2 * G ≤ q := (Nat.le_max_right _ _).trans hq
  have hb : blockLength t ≤ B * (q + 1) :=
    (Nat.clog_le_of_le_pow (Nat.lt_size_self (t + 2)).le).trans (by omega)
  have hb' : blockLength t ≤ B * (2 * q) := hb.trans (Nat.mul_le_mul_left B (by omega))
  have hM : M ≤ q ^ 3 := by
    change 2 * (q * (3 * k + 1) * ((states + k + 4) * blockLength t)) ≤ _
    calc
      _ ≤ 2 * (q * (3 * k + 1) * ((states + k + 4) * (B * (2 * q)))) := by gcongr
      _ = (2 * G) * q ^ 2 := by dsimp only [G]; ring
      _ ≤ q * q ^ 2 := Nat.mul_le_mul_right _ hG
      _ = q ^ 3 := by ring
  let l := Nat.log 2 q
  have hlog : Nat.log 2 M ≤ (l + 1) * 3 := by
    apply (Nat.log_le_clog _ _).trans
    apply Nat.clog_le_of_le_pow
    rw [Nat.pow_mul]
    exact hM.trans (Nat.pow_le_pow_left (Nat.lt_pow_succ_log_self (by decide : 1 < 2) q).le 3)
  have hpos : 0 < l := Nat.log_pos (by decide) htwo
  have he : a = 2 * (Nat.log 2 M / 131072) := by
    simp [a, slotBits, prefixBits, taper]
  have hpow : 2 ^ (1 + 24 * a) ≤ q := Nat.pow_le_of_le_log (by omega) (by omega)
  have hradix : 2 * (64 ^ (2 * a)) ^ 2 ≤ q := by
    apply le_trans ?_ hpow
    rw [pow_add, pow_one, show (24 * a) = 6 * (2 * a) * 2 by omega,
      Nat.pow_mul 2 (6 * (2 * a)) 2, Nat.pow_mul 2 6 (2 * a)]
  change 2 * (2 * (3 * k + 1) * rootCopies k states t) * (64 ^ (2 * a)) ^ 2 ≤ M
  calc
    _ = (2 * (64 ^ (2 * a)) ^ 2) * (2 * (3 * k + 1) * rootCopies k states t) := by ring
    _ ≤ q * (2 * (3 * k + 1) * rootCopies k states t) := Nat.mul_le_mul_right _ hradix
    _ = M := by dsimp only [M, rootEdges, RootPredecessorGraph.edgeCount, q]; ring

/-- At the true root label length, every sufficiently large source computation uses the same
physical fork. Its public bit may be any bit of the entire padded acceptance count. -/
theorem exists_scheduled_root_contraction_fork (k states : ℕ) {K : ℕ} {R : Type} [Finite R]
    (i j : Fin K) (hij : i ≠ j) (right : MultiTapeATM K Bool R) :
    ∃ (W : ℕ) (src : Fin W) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM W Bool Q) (C t₀ : ℕ),
      ∀ {State : Type} (M : MultiTapePTM k Bool State) (st : State ≃ Fin states)
        (input : List Bool) (t : ℕ), t₀ ≤ t → ∀ (σ : ℕ) (bit : Fin (paddedTime t + 1))
        (claim : Bool) (budget : ℕ),
        RunsRootContraction src atm i j right M st input t σ (slotBits (rootEdges k states t) 0)
          bit.val claim budget C := by
  obtain ⟨W, src, Q, hQ, atm, C, h⟩ := exists_root_contraction_fork k states i j hij right
  obtain ⟨t₀, hs⟩ := exists_root_variance_threshold k states
  refine ⟨W, src, Q, hQ, atm, C, max 2 t₀, ?_⟩
  intro State M st input t ht σ bit claim budget
  apply h
  · have hp := paddedTime_add_one_le ((Nat.le_max_left 2 t₀).trans ht)
    omega
  · exact hs t ((Nat.le_max_right _ _).trans ht)

end Cslib.Complexity.CountingSimulation
