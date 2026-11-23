/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.IntervalCountNative
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.SeededChildWitness
import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.QuantifiedWord.Append
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryOrder
import CslibFrontier.Foundations.Data.List.SumIndicator

/-!
# Native exact counts of seeded vertex prefixes

The proposed number of retained vertices is supplied in binary. Existential subtotals and
universal half choices reduce its verification to one native evaluation of the shared seed.
The flag word depends only on the binary vertex universe, so the same word can follow any
previously chosen parent vertex. Empty prefixes, bounds beyond the universe, and incorrect
proposed totals use the same deterministic terminal.

`computableInPolyTime_flags` and `computableInPolyTime_program` provide the native initializer
and terminal. `plays_program` identifies their quantified computation with the retained-vertex
rank used by the child numbering. No parent endpoint query is required.
-/

public section

namespace Turing.MultiTapeATM.SeededVertexRank

open Cslib BalancedSchedules Circuits.Frontier.NativeChild EndpointQuery
open MultiTapeTM ComputableInPolyTime QuantifiedWord IntervalCountGame

/-- One exact prefix-count claim for a group of a represented shared seed. -/
structure Query where
  /-- Binary universe and seed coefficients, with unary label length. -/
  context : SeededPredecessor.Context
  /-- Radix-64 coordinate, in unary. -/
  coordinate : ℕ
  /-- Selected group, in binary. -/
  group : ℕ
  /-- Exclusive parent-vertex prefix bound, in binary. -/
  bound : ℕ
  /-- Proposed number of retained vertices in the prefix, in binary. -/
  value : ℕ

/-- Framed shared context, unary coordinate, binary group and prefix bound, then binary total. -/
enc_structure encQuery : Query where context : SeededPredecessor.encContext,
  coordinate : encUnary, group : encNat, bound : encNat, value : encNat

/-- Choose the actual seed and split coordinate without materializing the parent vertices. -/
@[expose] def Query.ofSeed {U a : ℕ} (seed : SeededLabels.Seed U (6 * a)) (i : Fin a)
    (group bound value : ℕ) : Query :=
  ⟨⟨U, a, seed 0, seed 1, seed 2, seed 3, 0, 0⟩, i.val, group, bound, value⟩

/-- The shape depends only on the binary vertex universe, independently of the prefix claim. -/
@[expose] def flags (U : ℕ) : List Bool := rounds (U.size + 1) U.size

private def test (q : Query) (vertex : ℕ) : Bool :=
  decide (vertex < min q.bound q.context.universeSize) &&
    decide (RootPortFinish.symbol q.context q.coordinate vertex = q.group)

/-- Reconstruct the chosen singleton and compare its subtotal with the native seeded test. -/
def program (p : Query × List Bool) : Bool :=
  let q := p.1
  let U := q.context.universeSize
  (walk (U.size + 1) U.size 0 q.value p.2).elim false
    (fun kv => decide (kv.2 = (test q kv.1).toNat))

/-- The complete subdivision word has polynomial cost in the binary universe length. -/
theorem computableInPolyTime_flags : ComputableInPolyTime flags encNat encBits :=
  IntervalCountGame.computableInPolyTime_rounds (unary_add' binary_size (const 1)) binary_size

private theorem test_polyTime : ComputableInPolyTime (Function.uncurry test)
    (encPair encQuery encNat) encBool := by
  have hq := fst encQuery encNat
  have hv := snd encQuery encNat
  have hc := encQuery_context_polyTime hq
  have hn := binary_min' (encQuery_bound_polyTime hq)
    (SeededPredecessor.encContext_universeSize_polyTime hc)
  have hs := RootPortFinish.computableInPolyTime_symbol hc (encQuery_coordinate_polyTime hq) hv
  exact bool_and' (binary_lt' hv hn) (decide_eq' hs (encQuery_group_polyTime hq))

/-- Every terminal operation runs on binary vertex keys and totals. Only the label length
and coordinate are unary; the counted vertex universe is never enumerated. -/
theorem computableInPolyTime_program : ComputableInPolyTime program (encPair encQuery encBits)
    encBool := by
  let enc := encPair encQuery encBits
  have hq := fst encQuery encBits
  have hc := encQuery_context_polyTime hq
  have hh := binary_size.comp (SeededPredecessor.encContext_universeSize_polyTime hc)
  have hw := unary_add' hh (const 1)
  have hr := computableInPolyTime_walk hw hh (encQuery_value_polyTime hq)
    (snd encQuery encBits)
  let e := encPair encNat encNat
  have hp := fst enc e
  have hv := snd enc e
  have ht := test_polyTime.comp ((hq.comp hp).prod hv.fst')
  have hb : ComputableInPolyTime Bool.toNat encBool encNat := of_finite Bool.toNat
  exact optionElimWithInput
    (body := fun (p : Query × List Bool) (kv : ℕ × ℕ) => decide (kv.2 = (test p.1 kv.1).toNat))
    hr (const false) (decide_eq' hv.snd' (hb.comp ht))

/-- Every represented query has its literal native prefix-count meaning, even when its
coefficients or coordinate are not supplied by the actual-seed constructor. -/
theorem plays_program_iff (q : Query) :
    plays (fun xs => program (q, xs) = true) [] (flags q.context.universeSize) ↔
      q.value = (List.range (min q.bound q.context.universeSize)).countP
        (fun j => decide (RootPortFinish.symbol q.context q.coordinate j = q.group)) := by
  let U := q.context.universeSize
  let n := min q.bound U
  let f := fun j => decide (RootPortFinish.symbol q.context q.coordinate j = q.group)
  have he (xs : List Bool) : program (q, xs) = true ↔
      verdict (fun j => decide (j < n) && f j)
        (walk (U.size + 1) U.size 0 q.value xs) := by
    change (walk (U.size + 1) U.size 0 q.value xs).elim false
      (fun kv => decide (kv.2 = (test q kv.1).toNat)) = true ↔ _
    cases walk (U.size + 1) U.size 0 q.value xs <;> simp [verdict, test, n, U, f]
  have hp := plays_congr_length
    (fun xs => program (q, xs) = true)
    (fun xs => verdict (fun j => decide (j < n) && f j)
      (walk (U.size + 1) U.size 0 q.value xs)) [] (flags U)
    (fun xs _ => by simpa only [List.nil_append] using he xs)
  rw [hp, flags, plays_rounds _ _ _ _ _ (Nat.lt_succ_self U.size),
    total_padded f n U.size
      ((Nat.min_le_right q.bound U).trans (Nat.lt_size_self U).le),
    ← List.countP_range_eq_sum]

/-- Quantifying the native word verifies exactly the retained rank of the actual shared seed.
Taking `bound = U` checks the total retained count with the identical flag shape. -/
theorem plays_program {U a : ℕ} (seed : SeededLabels.Seed U (6 * a)) (i : Fin a)
    (group bound value : ℕ) (parent : EndpointQuery) :
    plays (fun xs => program (Query.ofSeed seed i group bound value, xs) = true) [] (flags U) ↔
      value = ((Labels.ofSeed U a seed i group).split parent).vertexRank bound := by
  change plays (fun xs => program (Query.ofSeed seed i group bound value, xs) = true) []
    (flags (Query.ofSeed seed i group bound value).context.universeSize) ↔ _
  refine (plays_program_iff (Query.ofSeed seed i group bound value)).trans ?_
  have he : (List.range (min bound U)).countP
      (fun j => decide (RootPortFinish.symbol (Query.ofSeed seed i group bound value).context
        i.val j = group)) = ((Labels.ofSeed U a seed i group).split parent).vertexRank bound := by
    apply List.countP_congr
    intro j hj
    have hU := (List.mem_range.mp hj).trans_le (Nat.min_le_right bound U)
    have hs := SeededChildCounts.symbol_of_seed seed i group 0 ⟨j, hU⟩ parent
    change (decide (RootPortFinish.symbol (Query.ofSeed seed i group bound value).context
      i.val j = group) = true) ↔
        (decide (((Labels.ofSeed U a seed i group).split parent).label j = group) = true)
    exact (congrArg (fun n => decide (n = group) = true) hs).to_iff
  exact (congrArg (fun n => value = n) he).to_iff

end Turing.MultiTapeATM.SeededVertexRank
