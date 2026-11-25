/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.MassProduction.Pipeline.Circuit
public import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The composition bound for scheduled line recovery

Split the inputs of `f : BooleanFunction (p + w)` into a prefix of `p` bits and a suffix of `w`
bits, and pack `f` into `copies` copies of a line-parity code on `K ^ ℓ` along an injection
`place` of the prefixes into copies, information points and bit positions. Every bit of every
codeword value is a function of `w` bits, a *resource*; there are `copies * |K| ^ ℓ * b` of them.
If every function of `w` bits has a circuit of size `L`, then `t` independent copies of `f` cost
the scheduler, one circuit of size `L` per resource, and an overhead `pipelineOverhead` for the
metadata lookup, scatter, gather and decoding (`complexity_directProduct_le_of_isScheduler`).
The overhead is quasi-linear in `2 ^ p + t |K| + copies |K| ^ ℓ` (`pipelineOverhead_le`), so the
resources dominate (`complexity_directProduct_le_explicit_of_isScheduler`).

Sizes count all gates, constants and negations included. They bound circuit size only and do
not certify the running time of a circuit constructor.

## Main definitions

* `Cslib.Circuits.Boolean.MassProduction.pipelineOverhead`: the gates of the lookup, scatter,
  gather and decoding stages.

## Main results

* `Cslib.Circuits.Boolean.MassProduction.complexity_directProduct_le_of_isScheduler`: the
  composition bound.
* `Cslib.Circuits.Boolean.MassProduction.pipelineOverhead_le`: the closed-form estimate.
* `Cslib.Circuits.Boolean.MassProduction.complexity_directProduct_le_explicit_of_isScheduler`:
  both combined.

## References

* Adapted from MassProduction/Nonuniform/RuntimeComposition.lean and
  MassProduction/Nonuniform/ScheduledRecovery.lean in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.MassProduction

open Finset Pipeline

/-- The gates of scheduled recovery beyond the scheduler and the resource circuits, for `t`
requests with `p` prefix and `w` suffix bits, `copies` codes on `K ^ ℓ` with `K` of `2 ^ b`
elements and lines of `s` points: one shared lookup of `2 ^ p` metadata entries, a scatter and a
gather between the `t * s` incidences and the `copies * 2 ^ (ℓ * b)` slots, and `t` sums of `s`
bits. -/
def pipelineOverhead (t p w ℓ b s copies : ℕ) : ℕ :=
  48 * (t + 2 ^ p) * (Nat.clog 2 (t + 2 ^ p) + 1) ^ 2 *
      (p + (ℓ * b + (Nat.clog 2 copies + Nat.clog 2 b)) + 1) +
    48 * (copies * 2 ^ (ℓ * b) + t * s + 1) *
      (Nat.clog 2 (copies * 2 ^ (ℓ * b) + t * s) + 1) ^ 2 * (Nat.clog 2 copies + ℓ * b + w + 1) +
    48 * (t * s + copies * 2 ^ (ℓ * b) * b + 1) *
      (Nat.clog 2 (t * s + copies * 2 ^ (ℓ * b) * b) + 1) ^ 2 *
      (Nat.clog 2 copies + ℓ * b + Nat.clog 2 b + 1 + 1) +
    t * (4 * s + 1)

/-- **Composition bound for scheduled line recovery.** Let `place` put every prefix of `p` bits
at a copy, an information point and a bit position of `copies` copies of a line-parity code
`C` on `K ^ ℓ`, where `bits` identifies `K` additively with the bit strings of length `b` and
`scalar` numbers its nonzero elements. Given a scheduler circuit `sched` for `t` requests and a
bound `L` on the circuit size of every function of `w` bits, `t` independent copies of any `f` on
`p + w` bits, each input block read as a prefix followed by a suffix, have circuit size at most
the size of `sched`, plus `L` for each of the `copies * |K| ^ ℓ * b` resources, plus
`pipelineOverhead t p w ℓ b s copies`. Requests may repeat, and `t` may be zero. Size counts
every gate, constants included; it does not bound the running time of a circuit constructor. -/
theorem complexity_directProduct_le_of_isScheduler
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] {ℓ b s t p w copies L : ℕ}
    (bits : K ≃+ BitString b) (scalar : Fin s ≃ {c : K // c ≠ 0})
    (C : LineCode K ℓ) (place : BitString p ↪ Fin copies × C.info × Fin b)
    (sched : Circuit Boolean.signature (t * (ℓ * b)) (t * (s * (ℓ * b))))
    (hsched : IsScheduler bits scalar sched)
    (hL : ∀ g : BooleanFunction w, complexity Boolean.interpretation (single g) ≤ L)
    (f : BooleanFunction (p + w)) :
    complexity Boolean.interpretation (directProduct f t) ≤
      sched.size + copies * Fintype.card K ^ ℓ * b * L + pipelineOverhead t p w ℓ b s copies := by
  choose members hmembers hsize using fun (q : Fin (copies * 2 ^ (ℓ * b))) (r : Fin b) =>
    complexity_le_iff.mp (hL (slotResource bits C place f q r))
  rw [show directProduct f t =
    lineSums t s ∘ (recoveryCircuit bits C place sched members).eval interpretation from
      funext fun x => (lineSums_eval_recoveryCircuit scalar hsched hmembers x).symm]
  have hrecovery := complexity_le_of_computes (I := interpretation)
    (recoveryCircuit bits C place sched members) fun _ => rfl
  rw [size_recoveryCircuit] at hrecovery
  have hbank : ∑ q, ∑ r, (members q r).size ≤ copies * Fintype.card K ^ ℓ * b * L :=
    (sum_le_sum fun q _ => sum_le_sum fun r _ => hsize q r).trans_eq <| by
      simp [card_eq_two_pow bits, ← pow_mul, mul_comm b ℓ, mul_assoc]
  have hlookup := size_batchLookupCircuit_le (metadata bits C place) t
  simp only [metaWidth] at hlookup
  have hscatter : (scatterCircuit t p w ℓ b s copies).size ≤ _ := size_batchOrCircuit_le _ _ _
  have hgather : (gatherCircuit t p w ℓ b s copies).size ≤ _ := size_batchOrCircuit_le _ _ _
  have hsums := complexity_lineSums_le (t := t) (s := s)
  refine (complexity_comp_le _ _).trans ?_
  unfold pipelineOverhead; omega

/-- **Closed-form overhead.** If `s + 1 = 2 ^ b`, the field size, and `ℓ` is positive, the
overhead is at most `1444 N D ^ 4`, where `N = 2 ^ p + t (s + 1) + copies (s + 1) ^ ℓ` bounds the
numbers of table entries, incidences and slots, and `D = p + w + ℓ b + ⌊log₂ (t + copies)⌋ + 2`
bounds the key widths and sorting depths. -/
theorem pipelineOverhead_le {t p w ℓ b s copies : ℕ} (hs : s + 1 = 2 ^ b) (hℓ : 0 < ℓ) :
    pipelineOverhead t p w ℓ b s copies ≤
      1444 * (2 ^ p + t * (s + 1) + copies * (s + 1) ^ ℓ) *
        (p + w + ℓ * b + Nat.log 2 (t + copies) + 2) ^ 4 := by
  set N := 2 ^ p + t * (s + 1) + copies * (s + 1) ^ ℓ with hN
  set lam := Nat.log 2 (t + copies) with hlam
  set D := p + w + ℓ * b + lam + 2 with hD
  have hlog : t + copies < 2 ^ (lam + 1) := Nat.lt_pow_succ_log_self one_lt_two _
  have hcopies : Nat.clog 2 copies ≤ lam + 1 := Nat.clog_le_of_le_pow (by omega)
  have hb : b ≤ ℓ * b := Nat.le_mul_of_pos_left b hℓ
  have hbits : Nat.clog 2 b ≤ ℓ * b := (Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le).trans hb
  have hslots : 2 ^ (ℓ * b) = (s + 1) ^ ℓ := by rw [hs, ← pow_mul, mul_comm]
  have hss : s < 2 ^ (ℓ * b) :=
    (show s < 2 ^ b by omega).trans_le (Nat.pow_le_pow_right (by decide) hb)
  have hp : 1 ≤ 2 ^ p := Nat.one_le_two_pow
  have h1 : Nat.clog 2 (t + 2 ^ p) ≤ D := (Nat.clog_le_of_le_pow (y := lam + 1 + p) <| by
    rw [pow_add]
    have htp := Nat.mul_le_mul_right (2 ^ p) (show t + 1 ≤ 2 ^ (lam + 1) by omega)
    rw [add_one_mul] at htp
    linarith only [htp, Nat.le_mul_of_pos_right t hp]).trans (by omega)
  have hTC : copies * 2 ^ (ℓ * b) + t * s ≤ 2 ^ (lam + 1 + ℓ * b) := by
    rw [pow_add]
    exact (show _ ≤ (t + copies) * 2 ^ (ℓ * b) by
      rw [add_mul]; linarith only [Nat.mul_le_mul_left t hss.le]).trans
        (Nat.mul_le_mul_right _ hlog.le)
  have h2 : Nat.clog 2 (copies * 2 ^ (ℓ * b) + t * s) ≤ D :=
    (Nat.clog_le_of_le_pow hTC).trans (by omega)
  have h3 : Nat.clog 2 (t * s + copies * 2 ^ (ℓ * b) * b) ≤ 2 * D :=
    (Nat.clog_le_of_le_pow (y := lam + 1 + ℓ * b + b) <| by
      rw [pow_add]
      exact (show _ ≤ (copies * 2 ^ (ℓ * b) + t * s) * 2 ^ b by
        rw [add_mul]
        linarith only [Nat.mul_le_mul_left (copies * 2 ^ (ℓ * b)) (Nat.lt_two_pow_self (n := b)).le,
          Nat.le_mul_of_pos_right (t * s) (show 0 < 2 ^ b by positivity)]).trans
        (Nat.mul_le_mul_right _ hTC)).trans (by omega)
  have n1 : t + 2 ^ p ≤ N := by
    rw [hN, mul_add, mul_one]; omega
  have n2 : copies * 2 ^ (ℓ * b) + t * s + 1 ≤ N := by rw [hN, hslots, mul_add, mul_one]; omega
  have hD2 : 2 ≤ D := by omega
  have n3 : t * s + copies * 2 ^ (ℓ * b) * b + 1 ≤ N * D := by
    have hn2D := Nat.mul_le_mul_right D n2
    rw [add_mul, add_mul, one_mul] at hn2D
    linarith only [hn2D, Nat.mul_le_mul_left (copies * 2 ^ (ℓ * b)) (show b ≤ D by omega),
      Nat.le_mul_of_pos_right (t * s) (show 0 < D by omega), (show 1 ≤ D by omega)]
  have n4 : t * (4 * s + 1) ≤ 4 * N := by
    rw [hN, show t * (4 * s + 1) = 4 * (t * s) + t by ring,
      show 4 * (2 ^ p + t * (s + 1) + copies * (s + 1) ^ ℓ) =
        4 * 2 ^ p + (4 * (t * s) + 4 * t) + 4 * (copies * (s + 1) ^ ℓ) by ring]
    omega
  unfold pipelineOverhead
  calc
    _ ≤ 48 * N * (2 * D) ^ 2 * (2 * D) + 48 * N * (2 * D) ^ 2 * D +
        48 * (N * D) * (3 * D) ^ 2 * (2 * D) + 4 * N := by gcongr <;> omega
    _ = 576 * N * D ^ 3 + 864 * N * D ^ 4 + 4 * N := by ring
    _ ≤ 1444 * N * D ^ 4 := by
      simp only [mul_assoc]
      linarith only [Nat.mul_le_mul_left N
        (Nat.pow_le_pow_right (show 1 ≤ D by omega) (show 3 ≤ 4 by decide)),
        Nat.le_mul_of_pos_right N (show 0 < D ^ 4 by positivity)]

/-- **Explicit composition bound.** Under the hypotheses of
`complexity_directProduct_le_of_isScheduler`, `t` independent copies of `f` have circuit size at
most the size of the scheduler, plus `L` for each of the `copies * |K| ^ ℓ * b` resources, plus
`1444 N D ^ 4`, where `N = 2 ^ p + t |K| + copies |K| ^ ℓ` and
`D = p + w + ℓ b + ⌊log₂ (t + copies)⌋ + 2`. No positivity is assumed: without requests the
bound is trivial, and a scheduler for at least one request forces `ℓ > 0`. Size counts every
gate, constants included; it does not bound the running time of a circuit constructor. -/
theorem complexity_directProduct_le_explicit_of_isScheduler
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] {ℓ b s t p w copies L : ℕ}
    (bits : K ≃+ BitString b) (scalar : Fin s ≃ {c : K // c ≠ 0})
    (C : LineCode K ℓ) (place : BitString p ↪ Fin copies × C.info × Fin b)
    (sched : Circuit Boolean.signature (t * (ℓ * b)) (t * (s * (ℓ * b))))
    (hsched : IsScheduler bits scalar sched)
    (hL : ∀ g : BooleanFunction w, complexity Boolean.interpretation (single g) ≤ L)
    (f : BooleanFunction (p + w)) :
    complexity Boolean.interpretation (directProduct f t) ≤
      sched.size + copies * Fintype.card K ^ ℓ * b * L +
        1444 * (2 ^ p + t * Fintype.card K + copies * Fintype.card K ^ ℓ) *
          (p + w + ℓ * b + Nat.log 2 (t + copies) + 2) ^ 4 := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · exact (complexity_le_of_computes (Circuit.wiring signature Fin.elim0)
      fun _ => funext fun i => i.elim0).trans (Nat.zero_le _)
  have hℓ : 0 < ℓ := Nat.pos_of_ne_zero fun h0 => by
    subst h0; obtain ⟨_, hdirs, -⟩ := hsched fun _ => 0
    exact hdirs ⟨0, ht⟩ (funext fun i => i.elim0)
  refine (complexity_directProduct_le_of_isScheduler bits scalar C place sched hsched hL f).trans ?_
  rw [← succ_eq_card scalar]
  exact Nat.add_le_add_left (pipelineOverhead_le (succ_eq_two_pow bits scalar) hℓ) _

end Cslib.Circuits.Boolean.MassProduction
