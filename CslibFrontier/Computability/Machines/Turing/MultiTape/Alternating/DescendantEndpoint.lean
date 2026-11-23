/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.DescendantEndpointGround
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.DescendantEndpointTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.ProtectedWordGame
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.DescendantEndpointBounds
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.DescendantEndpointCorrect
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RootEndpointAncestry

/-!
# A closed native controller for compressed descendant endpoints

One finite alternating machine executes every runtime stack of actual seed frames. Its local
round computes the shared child program, consumes quantified choices, and either returns a
Boolean verdict or pops one frame. The original raw schedule is protected during every round;
only the final native terminal reads it.

`exists_evaluator` has no supplied local-segment or root-machine contract. It constructs both
from native polynomial-time programs and proves a clock linear in the raw schedule plus a
polynomial in the initial short metadata and binary schedule length. `exists_actual_evaluator`
identifies accepted queries with the genuine numbered descendants of the block network.
-/

public section

namespace Turing.MultiTapeATM.DescendantEndpoint

open MultiTapeTM MultiTapePTM Cslib.Circuits.Frontier
open MultiTapeTM.DescendantEndpoint SeededChildCounts

private theorem terminal_iff_value (k copies : ℕ) (raw : List Bool) (p : Position)
    (hcopies : p.copies = copies) (hp : player p = none) :
    DescendantEndpointTerminal.check k (raw, p) = true ↔
      value (RootEndpointQuery.endpointQuery k copies raw) p := by
  rw [DescendantEndpointTerminal.check_eq_true_iff]
  apply Iff.trans ?_ (terminal_value _ p hp)
  cases hv : p.verdict <;>
    simp [terminal, hv, Joined.holds, RootEndpointQuery.endpointQuery, hcopies]

/-- Compile the complete compressed endpoint computation. The finite machine and its constants
are chosen before the raw schedule, the frame stack, and every endpoint request. -/
theorem exists_evaluator (k : ℕ) :
    ∃ (U : ℕ) (schedule query : Fin U) (S : Type) (_ : Finite S)
      (atm : MultiTapeATM U Bool S) (C D : ℕ), schedule ≠ query ∧
      ∀ (input raw : List Bool) (copies : ℕ) (frames : List Frame)
        (edge : ℕ) (answer : ℕ × ℕ),
        let p := root copies frames edge answer
        let start := (TwoWordInput.ready schedule query input raw (encPosition p)).withState
          (some atm.toPTM.initial)
        let time := C * (raw.length + ((encPosition p).length + raw.length.size + 1) ^ D + 1)
        atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔
          accepts (RootEndpointQuery.endpointQuery k copies raw) frames edge answer) := by
  obtain ⟨N, ass, qry, Q, hQ, terminal, ct, dt, hne, ht⟩ :=
    DescendantEndpointTerminal.exists_evaluator k
  obtain ⟨U, schedule, query, S, hS, atm, cg, dg, hne', hg⟩ :=
    ProtectedWordGame.exists_evaluator encPosition player MultiTapeTM.DescendantEndpoint.next
      player_polyTime step_polyTime ass qry hne terminal
  obtain ⟨cb, db, hb⟩ := storageBound_polyBounded.exists_le
  let cap (n : ℕ) := cb * (n + 1) ^ db
  let cost (n : ℕ) := (cap n + 1) * (cg * (16 * (cap n + 1) + 1) ^ dg + 2) +
    ct * ((16 * (cap n + 1) + n + 1) ^ dt + 1) + 1
  have hcost : Cslib.PolynomiallyBounded cost := by dsimp [cost, cap]; fun_prop
  obtain ⟨c, d, hc⟩ := Cslib.polynomiallyBounded_iff_le.mp hcost
  refine ⟨U, schedule, query, S, hS, atm, c + ct, d, hne', ?_⟩
  intro input raw copies frames edge answer p start time
  let n := (encPosition p).length + raw.length.size
  let B := storageBound p
  let bound := 16 * (cap n + 1)
  let terminalTime := ct * (raw.length + (bound + n + 1) ^ dt + 1)
  let valid := fun z : Position => Bounded B z ∧ z.copies = copies
  let val := value (RootEndpointQuery.endpointQuery k copies raw)
  have hB : B ≤ cap n := (hb p).trans (Nat.mul_le_mul_left cb
    (Nat.pow_le_pow_left (by dsimp [n]; omega) db))
  have hlength (z : Position) (hz : valid z) : (encPosition z).length ≤ bound :=
    hz.1.length_encPosition_le.trans (Nat.mul_le_mul_left 16 (Nat.add_le_add_right hB 1))
  have hvalid (z : Position) (hz : valid z) (owner : Bool) (_ : player z = some owner)
      (move : Bool) : valid (MultiTapeTM.DescendantEndpoint.next z move) :=
    ⟨hz.1.next move, (next_copies z move).trans hz.2⟩
  have hterminal (z : Position) (hz : valid z) (hplayer : player z = none) :
      let initial := (TwoWordInput.ready ass qry input raw (encPosition z)).withState
        (some terminal.toPTM.initial)
      terminal.HaltsWithin terminalTime initial ∧
        (terminal.AcceptsWithin terminalTime initial ↔ val z) := by
    have hs := ht input raw z
    have hshort : DescendantEndpointTerminal.shortSize (raw, z) ≤ bound + n + 1 := by
      have hl := hlength z hz
      change (encPosition z).length + raw.length.size + 1 ≤
        bound + ((encPosition p).length + raw.length.size) + 1
      omega
    have htime : ct * (raw.length + DescendantEndpointTerminal.shortSize (raw, z) ^ dt + 1) ≤
        terminalTime :=
      Nat.mul_le_mul_left ct (Nat.add_le_add_right
        (Nat.add_le_add_left (Nat.pow_le_pow_left hshort dt) raw.length) 1)
    refine ⟨hs.1.mono htime, ?_⟩
    exact (Iff.intro (fun h => hs.2.mp (h.of_halted_stepCoins hs.1))
      (fun h => (hs.2.mpr h).mono htime)).trans (terminal_iff_value k copies raw z hz.2 hplayer)
  have hp : valid p := ⟨bounded_root copies frames edge answer, rfl⟩
  have hs := hg input raw valid val rank bound terminalTime hlength hvalid
    (fun z _ owner ho move => rank_next_lt z owner move ho)
    (fun z _ owner ho => value_iff_next _ z owner ho) hterminal p hp
  have hrank : rank p ≤ cap n := by
    apply le_trans ?_ hB
    change rank (root copies frames edge answer) ≤ storageBound (root copies frames edge answer)
    rw [rank_root]
    simp only [storageBound, root]
    omega
  have htime : (rank p + 1) * (cg * (bound + 1) ^ dg + 2) + terminalTime + 1 ≤ time := by
    change _ ≤ (c + ct) * (raw.length + (n + 1) ^ d + 1)
    have hr := Nat.mul_le_mul_right (cg * (bound + 1) ^ dg + 2)
      (Nat.add_le_add_right hrank 1)
    calc
      _ ≤ (cap n + 1) * (cg * (bound + 1) ^ dg + 2) + terminalTime + 1 :=
        Nat.add_le_add_right (Nat.add_le_add_right hr terminalTime) 1
      _ = ct * raw.length + cost n := by dsimp only [terminalTime, cost, bound]; ring
      _ ≤ ct * raw.length + c * (n + 1) ^ d := Nat.add_le_add_left (hc n) _
      _ ≤ ct * (raw.length + (n + 1) ^ d + 1) + c * (raw.length + (n + 1) ^ d + 1) :=
        Nat.add_le_add (Nat.mul_le_mul_left ct (by omega)) (Nat.mul_le_mul_left c (by omega))
      _ = (c + ct) * (raw.length + (n + 1) ^ d + 1) := by ring
  refine ⟨hs.1.mono htime, ?_⟩
  exact (Iff.intro (fun h => hs.2.mp (h.of_halted_stepCoins hs.1))
    (fun h => (hs.2.mpr h).mono htime)).trans
      (value_root (RootEndpointQuery.endpointQuery k copies raw) copies frames edge answer)

/-- The same fixed finite controller accepts exactly genuine descendant endpoints of the
copied and subdivided block network. Only seeds and short frame metadata are encoded; the
mathematical edge lists specify the result and never occur on its input tapes. -/
theorem exists_actual_evaluator (k : ℕ) :
    ∃ (U : ℕ) (schedule query : Fin U) (S : Type) (_ : Finite S)
      (atm : MultiTapeATM U Bool S) (C D : ℕ), schedule ≠ query ∧
      ∀ {R : Type} (source : MultiTapePTM k Bool R) (word : List Bool)
        (b q copies σ : ℕ) (code : BlockLetter k R b → Fin copies → Bool)
        (frames : List Frame) (vertices : ℕ) (edges : List (ℕ × ℕ)),
        Represents (RootPredecessorGraph.vertexCount k q copies)
          (RootPortGraph.ends (q := q) source word b σ code) frames vertices edges →
        ∀ (input : List Bool) (edge : ℕ) (answer : ℕ × ℕ),
          let raw := ScheduleBits.rows (List.ofFn (scheduleOfNat k q σ))
          let p := root copies frames edge answer
          let start := (TwoWordInput.ready schedule query input raw (encPosition p)).withState
            (some atm.toPTM.initial)
          let time := C * (raw.length + ((encPosition p).length + raw.length.size + 1) ^ D + 1)
          atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔
            edge < edges.length ∧ edges.getD edge (0, 0) = answer) := by
  obtain ⟨U, schedule, query, S, hS, atm, C, D, hne, hrun⟩ := exists_evaluator k
  refine ⟨U, schedule, query, S, hS, atm, C, D, hne, ?_⟩
  intro R source word b q copies σ code frames vertices edges hframes
    input edge answer raw p start time
  have hs := hrun input raw copies frames edge answer
  have hbase := RootEndpointQuery.represents_descendant (q := q) source word b σ code []
  exact ⟨hs.1, hs.2.trans (accepts_iff_of_represents _ hbase hframes edge answer)⟩

end Turing.MultiTapeATM.DescendantEndpoint
