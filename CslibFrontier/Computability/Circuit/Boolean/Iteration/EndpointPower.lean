/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Iteration.Ranked
public import CslibFrontier.Foundations.Combinatorics.FunctionalGraph.EndpointCheckpoints
public import Mathlib.Analysis.Real.Sqrt
import CslibFrontier.Computability.Circuit.Boolean.BinaryField
import CslibFrontier.Computability.Circuit.Boolean.Iteration.EndpointOptimization
import CslibFrontier.Probability.KWiseIndependent.Minwise
import CslibFrontier.Probability.KWiseIndependent.Polynomial
import Mathlib.Data.Finset.Sort

/-!
# Square-root fixed powering by endpoint checkpoints

An `n`-bit transition circuit of size `s` admits, for each fixed exponent, a De Morgan circuit
of size at most a constant times `min (2^n) (√(2^n * (s + (n+1)^2)))`. All gates, including
constants, are charged. The exponent is unrestricted. The ranking and checkpoint payloads may
depend on the transition table.

The construction combines the closed-window coverage lemma, a five-wise independent quartic
ranking in a binary field, and one sparse lookup shared by the entire prefix. The rank scan
locates its checkpoint without a dictionary probe at each step.
-/

public section

namespace Cslib.Circuits.Boolean.Iteration

open Cslib.FunctionalGraph Cslib.Probability

/-- One quadratic-size rank circuit simultaneously gives a sparse set of endpoint checkpoints
for *all* orbits of `f`. Bit strings are compared in the scan's lexicographic order. -/
theorem exists_endpointRank {n : ℕ} (hn : n ≠ 0) (f : BitString n → BitString n)
    {L : ℕ} (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ (q : Circuit signature n n) (H : Finset (BitString n)),
      q.size ≤ n + 5 * (13 * n ^ 2 + 8 * n) ∧ H.card * L ≤ 512 * 2 ^ n ∧
        ∀ x, x ∈ H ↔ IsEndpointCheckpoint f (fun z => toLex (q.eval interpretation z)) L x := by
  classical
  let B := BinaryField.equivBits hn
  let order := (Fintype.orderIsoFinOfCardEq (Lex (BitString n)) (k := 2 ^ n)
    (Fintype.card_congr (toLex : BitString n ≃ Lex (BitString n)).symm |>.trans
      (BitString.card (n := n)))).symm
  let e := B.toEquiv.trans (toLex.trans order.toEquiv)
  have hh := ((isKWiseIndependentHash_polynomialHash (F := BinaryField n) 5).comp
    B.symm.injective).map_equiv e
  let w (x : BitString n) (j : Fin (L + 1)) := f^[j.val] x
  obtain ⟨coeff, hcount⟩ := hh.exists_card_endpoint_min_le w hL hLN
  obtain ⟨q, hq, hs⟩ := exists_binaryFieldPolynomial_circuit hn coeff
  let rank (x : BitString n) := toLex (q.eval interpretation x)
  have hr (x : BitString n) : e (polynomialHash coeff (B.symm x)) = order (rank x) :=
    congrArg (fun y => order (toLex y)) (hq x).symm
  rw [BitString.card] at hcount
  refine ⟨q, _, hs, hcount, fun x => ?_⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hr, OrderIso.le_iff_le,
    w, Fin.val_zero, Function.iterate_zero_apply, Fin.val_last, IsEndpointCheckpoint, rank]

/-- At window length `L`, the local walk costs `O(L * (s + n²))` gates and its one lookup costs
`O(2^n / L + 2^⌈n/2⌉)` gates. -/
theorem fixed_power_endpoint_tradeoff {n : ℕ} (c : Circuit signature n n) (T L : ℕ)
    (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit signature n n, out.Computes interpretation (c.eval interpretation)^[T] ∧
      out.size ≤ 1600 * (L * (c.size + (n + 1) ^ 2) + 2 ^ n / L + 2 ^ ((n + 1) / 2)) := by
  classical
  rcases eq_or_ne n 0 with rfl | hn
  · obtain ⟨out, hc, hs⟩ := exists_sparseLookup Finset.univ (c.eval interpretation)^[T]
    exact ⟨out, fun x => hc (Finset.mem_univ x), by simp at hs; lia⟩
  let f := c.eval interpretation
  obtain ⟨q, H, hq, hsize, hH⟩ := exists_endpointRank hn f hL hLN
  obtain ⟨p, hp, hpSize⟩ := exists_sparseLookup H f^[T - 2 * L]
  have hcover (x : BitString n) (_ : x ∈ (Set.univ : Set _))
      (hi : Function.Injective (fun i : Fin (2 * L) => f^[i.val] x)) (i : Fin (2 * L))
      (hm : ∀ j : Fin (2 * L), toLex (q.eval interpretation (f^[i.val] x)) ≤
        toLex (q.eval interpretation (f^[j.val] x))) :
      f^[if i.val < L then i.val else i.val - L] x ∈ (H : Set _) :=
    (hH _).mpr (isEndpointCheckpoint_of_min f _ hi i hm)
  obtain ⟨out, ho, hout⟩ := fixed_power_of_ranked_checkpoints c q p Set.univ H T L hL hcover hp
  refine ⟨out, (out.computesOn_univ_iff _ _).mp ho, hout.trans ?_⟩
  have hcard : H.card ≤ 512 * (2 ^ n / L + 1) := by
    apply Nat.le_of_lt
    apply Nat.lt_of_mul_lt_mul_right (a := L)
    nlinarith [Nat.lt_mul_div_succ (2 ^ n) hL]
  have hlocal : 2 * (3 * c.size + q.size + 16 * n + 18 * n + 3) ≤
      160 * (c.size + (n + 1) ^ 2) := by nlinarith
  have hhalf : 1 ≤ 2 ^ ((n + 1) / 2) := Nat.one_le_two_pow
  nlinarith [Nat.mul_le_mul_left L hlocal]

/-- Every fixed power of an arbitrary `n`-bit transition circuit has size at most
`8000 * min (2^n) (√(2^n * (s + (n+1)^2)))`, independently of the exponent. -/
theorem fixed_power_endpoint {n : ℕ} (c : Circuit signature n n) (T : ℕ) :
    ∃ out : Circuit signature n n, out.Computes interpretation (c.eval interpretation)^[T] ∧
      (out.size : ℝ) ≤ 8000 * min ((2 : ℝ) ^ n)
        (Real.sqrt ((2 : ℝ) ^ n * (c.size + (n + 1) ^ 2 : ℕ))) := by
  convert exists_circuit_of_endpoint_tradeoff ((c.eval interpretation)^[T])
    (show 0 < c.size + (n + 1) ^ 2 by positivity) (fixed_power_endpoint_tradeoff c T) using 4
  norm_num

end Cslib.Circuits.Boolean.Iteration
