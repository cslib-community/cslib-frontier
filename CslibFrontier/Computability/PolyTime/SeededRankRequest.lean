/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.SeededRankChallenge
public import CslibFrontier.Computability.Circuit.Boolean.CarryLookahead.Query.CountingInput
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Sum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option

/-!
# Converting the balance challenge to one native count request

A terminal branch with value `b` is the constant claim that the zero-term sum has bit
zero equal to `!b`. This permits one count-bit machine to implement both terminal and
nonterminal branches from encoded data, without branching on the result of an ATM.
-/

public section

namespace Cslib.SeededRankRequest

open Turing.MultiTapeTM ComputableInPolyTime Circuits.Boolean.CarryLookahead.Query

/-- The selected root edge followed by the count-bit parameters. -/
abbrev encOutput := encPair encNat CountingInput.encInput

/-- Make a single count request, with zero terms for a terminal answer. -/
@[expose] def run (p : SeededRankChallenge.Input) : ℕ × CountingInput.Input :=
  let result := SeededRankChallenge.run p
  let r := result.getRight?.getD ⟨0, 0, false⟩
  if result.isLeft then (0, ⟨0, ⟨1, 0, !result.getLeft?.getD false⟩⟩)
  else (r.edge, ⟨p.edges, ⟨Nat.clog 2 p.edges, r.bit, r.claim⟩⟩)

/-- Resolving a terminal answer never reads a predicate leaf. -/
theorem run_of_terminal (p : SeededRankChallenge.Input) (b : Bool)
    (h : SeededRankChallenge.run p = .inl b) :
    run p = (0, ⟨0, ⟨1, 0, !b⟩⟩) := by simp [run, h]

/-- A genuine challenge retains the selected edge, bit and claimed rank value. -/
theorem run_of_query (p : SeededRankChallenge.Input) (r : SeededRankChallenge.Request)
    (h : SeededRankChallenge.run p = .inr r) :
    run p = (r.edge, ⟨p.edges, ⟨Nat.clog 2 p.edges, r.bit, r.claim⟩⟩) := by simp [run, h]

private theorem query_bounds (p : SeededRankChallenge.Input) (r : SeededRankChallenge.Request)
    (h : SeededRankChallenge.run p = .inr r) : r.edge < p.edges ∧ r.bit < Nat.clog 2 p.edges := by
  unfold SeededRankChallenge.run SeededRankChallenge.dispatch at h
  dsimp only at h
  split_ifs at h with he _ hj
  cases h
  exact ⟨he, hj⟩

/-- Every choice word, including one of arbitrary length, yields an in-range bit. -/
theorem valid_bit (p : SeededRankChallenge.Input) :
    (run p).2.query.bit < (run p).2.query.width := by
  cases h : SeededRankChallenge.run p with
  | inl b => rw [run_of_terminal p b h]; exact Nat.zero_lt_one
  | inr r => rw [run_of_query p r h]; exact (query_bounds p r h).2

/-- The chosen edge is bounded by the supplied numeric universe on every branch. -/
theorem edge_le (p : SeededRankChallenge.Input) : (run p).1 ≤ p.edges := by
  cases h : SeededRankChallenge.run p with
  | inl b => rw [run_of_terminal p b h]; exact Nat.zero_le _
  | inr r => rw [run_of_query p r h]; exact (query_bounds p r h).1.le

/-- The count width is logarithmic in the edge universe, and the number of counted terms
is at most the number of edges. -/
theorem parameter_sizes (p : SeededRankChallenge.Input) :
    (run p).2.count.size ≤ p.edges.size ∧ (run p).2.query.width.size ≤ p.edges.size + 1 := by
  cases h : SeededRankChallenge.run p with
  | inl b => rw [run_of_terminal p b h]; simp
  | inr r =>
    rw [run_of_query p r h]
    have hw : Nat.clog 2 p.edges ≤ p.edges.size := Nat.clog_le_of_le_pow (Nat.lt_size_self _).le
    exact ⟨le_rfl, (Nat.size_le_self _).trans (hw.trans (Nat.le_succ _))⟩

/-- Prepare the edge number and exact native count-input encoding in polynomial time on the
short choices and numeric parameters. -/
theorem computableInPolyTime_run : ComputableInPolyTime run SeededRankChallenge.encInput
    encOutput := by
  have hr := SeededRankChallenge.computableInPolyTime_run
  have hright := optionGetDWithInput
    ((ComputableInO.getRight?_deg encBool SeededRankChallenge.encRequest).computableInPolyTime.comp
      hr) (const ⟨0, 0, false⟩)
  have hb := optionGetDWithInput
    ((ComputableInO.getLeft?_deg encBool SeededRankChallenge.encRequest).computableInPolyTime.comp
      hr) (const false)
  have hn := SeededRankChallenge.encInput_edges_deg.computableInPolyTime
  have ht := (const (encOut := encNat) (0 : ℕ)).prod (CountingInput.encInput_mk_polyTime (const 0)
    (Initial.encInput_mk_polyTime (const 1) (const 0) (bool_not.comp hb)))
  have hq := (SeededRankChallenge.encRequest_edge_polyTime hright).prod
    (CountingInput.encInput_mk_polyTime hn (Initial.encInput_mk_polyTime
      (binary_clog_two_nat.comp hn) (SeededRankChallenge.encRequest_bit_polyTime hright)
      (SeededRankChallenge.encRequest_claim_polyTime hright)))
  exact ite ((ComputableInO.isLeft_deg encBool SeededRankChallenge.encRequest
    ).computableInPolyTime.comp hr) ht hq

end Cslib.SeededRankRequest
