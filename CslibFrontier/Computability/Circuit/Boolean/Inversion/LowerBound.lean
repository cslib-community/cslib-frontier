/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Inversion.Basic
public import Cslib.Computability.Circuit.Simulation
import CslibFrontier.Computability.Circuit.Program
import CslibFrontier.Computability.Circuit.Monotone.Basic

/-!
# Descent ranks from circuits with few negations

A circuit over the De Morgan basis with `k` NOT gates admits a natural-valued descent rank below
`2 ^ k`: increasing the inputs cannot decrease the rank, and equal ranks force the entire
output vector to increase. This is the circuit invariant in the lower-bound direction of
Markov's inversion theorem [Markov, Lemma 5.2][Markov1963]. The rank-to-chain conversion and
matching synthesis yield the exact minimum in the companion Markov module.

The proof tracks all input and gate values, so a shared subcircuit is charged only once.
An AND, OR or constant gate keeps the rank. Appending a NOT gate replaces `r` by `2 r + b`,
where `b` is the input to that gate. At equal new ranks, both the old rank and `b` agree;
thus the new NOT output also agrees. Distinct old ranks remain ordered after the update.

## Main results

* `Cslib.Circuits.Boolean.exists_descentRank_lt_two_pow_negationCost`: every native circuit
  over the De Morgan basis has a descent rank bounded by the exponential of its NOT-gate count.

## References

* [A. Markov, *On the inversion complexity of a system of Boolean functions*][Markov1963],
  Lemma 5.2, pages 478–479.
-/

public section

namespace Cslib.Circuits.Boolean

variable {n g m : ℕ}

private theorem isDescentRank_gate {p : Program signature n g} {line : Line signature n g}
    {rank : BitString n → ℕ} (h : IsDescentRank id (p.trace interpretation) rank)
    (hgate : ∀ ⦃x y⦄, x ≤ y → rank x = rank y →
      interpretation line.op (p.trace interpretation x ∘ line.wires) ≤
        interpretation line.op (p.trace interpretation y ∘ line.wires)) :
    IsDescentRank id ((p.gate line).trace interpretation) rank where
  monotone := h.monotone
  preserves_eq {x y} hxy heq w := by
    induction w using Wire.lastCases with
    | last =>
      rw [Program.trace_gate_last, Program.trace_gate_last]
      exact hgate hxy heq
    | castSucc w =>
      simpa only [Program.trace_gate_castSucc] using h.preserves_eq hxy heq w

private theorem interpretation_monotone_of_ne_not {op : Op} (hop : op ≠ .not) :
    Monotone (interpretation op) := by
  cases op with
  | const b => exact fun _ _ _ => le_refl b
  | not => exact (hop rfl).elim
  | and => exact fun _ _ h => Cslib.Circuits.Monotone.interpretation_mono .and h
  | or => exact fun _ _ h => Cslib.Circuits.Monotone.interpretation_mono .or h

private theorem program_exists_descentRank (p : Program signature n g) :
    ∃ rank : BitString n → ℕ, IsDescentRank id (p.trace interpretation) rank ∧
      ∀ x, rank x < 2 ^ p.cost negationCost := by
  induction p with
  | empty =>
    refine ⟨fun _ => 0, ⟨fun {_ _} _ => le_rfl, ?_⟩, fun _ => by simp⟩
    intro x y hxy _ w
    cases w with
    | input i => exact hxy i
    | gate i => exact i.elim0
  | @gate g p line ih =>
    obtain ⟨rank, hrank, hbound⟩ := ih
    by_cases hop : line.op = .not
    · obtain ⟨op, wires⟩ := line
      dsimp only at hop
      subst op
      let bit (x : BitString n) := p.trace interpretation x (wires 0)
      let rank' (x : BitString n) := 2 * rank x + (bit x).toNat
      have hle (x : BitString n) : (bit x).toNat ≤ 1 := Bool.toNat_le _
      have heq {x y : BitString n} (h : rank' x = rank' y) : rank x = rank y := by
        have := hle x
        have := hle y
        dsimp only [rank'] at h
        omega
      have hold : IsDescentRank id (p.trace interpretation) rank' := by
        constructor
        · intro x y hxy
          have h := hrank.monotone hxy
          rcases eq_or_lt_of_le h with h | h
          · have hb := hrank.preserves_eq hxy h (wires 0)
            change bit x ≤ bit y at hb
            have := Bool.toNat_le_toNat hb
            dsimp only [rank']
            omega
          · have := hle x
            have := hle y
            dsimp only [rank']
            omega
        · exact fun {_ _} hxy h => hrank.preserves_eq hxy (heq h)
      refine ⟨rank', isDescentRank_gate hold ?_, ?_⟩
      · intro x y _ h
        have hsame := heq h
        have hb : (bit x).toNat = (bit y).toNat := by
          dsimp only [rank'] at h
          omega
        have hb' : bit x = bit y := by
          simpa only [Bool.ofNat_toNat] using congrArg Bool.ofNat hb
        change Bool.not (bit x) ≤ Bool.not (bit y)
        simp only [hb', le_refl]
      · intro x
        have hb := hbound x
        have := hle x
        simp only [Program.cost_gate, negationCost_not, pow_succ]
        dsimp only [rank']
        omega
    · have hcost : negationCost line.op = 0 := by
        cases h : line.op <;> simp_all [negationCost]
      refine ⟨rank, isDescentRank_gate hrank ?_, ?_⟩
      · intro x y hxy heq
        apply interpretation_monotone_of_ne_not hop
        exact fun i => hrank.preserves_eq hxy heq (line.wires i)
      · simpa only [Program.cost_gate, hcost, Nat.add_zero] using hbound

/-- A circuit with `k` NOT gates has a descent rank below `2 ^ k`. This is the rank invariant
in Markov's lower bound, including shared gates and any number of designated outputs. -/
theorem exists_descentRank_lt_two_pow_negationCost (c : Circuit signature n m) :
    ∃ rank : BitString n → ℕ, IsDescentRank id (c.eval interpretation) rank ∧
      ∀ x, rank x < 2 ^ c.program.cost negationCost := by
  obtain ⟨rank, hrank, hbound⟩ := program_exists_descentRank c.program
  exact ⟨rank, ⟨hrank.monotone, fun {_ _} hxy heq o => hrank.preserves_eq hxy heq (c.outputs o)⟩,
    hbound⟩

end Cslib.Circuits.Boolean
