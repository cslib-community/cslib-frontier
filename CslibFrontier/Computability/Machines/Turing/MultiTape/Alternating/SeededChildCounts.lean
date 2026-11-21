/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.SeededChildEndpoints
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarryLookaheadCountingRawLeaves
import CslibFrontier.Foundations.Data.List.OfFn

/-!
# Counting subqueries of a recursive child endpoint

A retained vertex prefix, a side-specific port prefix and a packing-class rank use the same
counting controller. For a genuine edge, either sign of a port or class test admits one
parent endpoint witness. The physical controller hands this test to one alternating leaf per
branch, with a clock additive in the supplied leaf time.
-/

public section

namespace Turing.MultiTapeATM.SeededChildCounts

open Cslib Cslib.Circuits.Frontier.NativeChild Cslib.Circuits.Boolean.CarryLookahead.Query
open MultiTapeTM EndpointQuery CountingLeaf

/-- The three distinct prefix counts in the native child endpoint formula. -/
inductive Request where
  | vertex (bound : ℕ)
  | port (column : Bool) (bound : ℕ)
  | pack (edge : ℕ) (ends : ℕ × ℕ)

/-- The exact number of terms for a runtime prefix or class count. -/
@[expose] def Request.size (r : Request) (q : EndpointQuery) (l : Labels) : ℕ :=
  match r with
  | .vertex bound => min bound l.vertices
  | .port _ bound => bound
  | .pack _ _ => q.size

/-- The value used by the recursive endpoint and packet witnesses. -/
@[expose] noncomputable def Request.value (r : Request) (q : EndpointQuery) (l : Labels) : ℕ :=
  match r with
  | .vertex bound => (l.split q).vertexRank bound
  | .port col bound => q.portCount (l.split q) (if col then Prod.snd else Prod.fst) bound
  | .pack e p => q.classCount l e p

/-- Check a single parent endpoint and evaluate a Boolean test on its two keys. -/
noncomputable def atEndpoint (q : EndpointQuery) (j : ℕ) (f : ℕ × ℕ → Bool) : Bool := by
  classical exact decide (∃ p, q.accepts j p ∧ f p = true)

/-- For either claimed truth value, a genuine edge needs just its own two-key witness. -/
theorem atEndpoint_eq_iff {q : EndpointQuery} {es} (hq : q.Represents es) {j : ℕ}
    (hj : j < q.size) (f : ℕ × ℕ → Bool) (claim : Bool) :
    atEndpoint q j f = claim ↔ ∃ p, q.accepts j p ∧ f p = claim := by
  classical
  rw [hq.1] at hj
  simp only [atEndpoint, hq.2, hj, true_and, exists_eq_left', Bool.decide_eq_true]

/-- A vertex query reads the common seed directly. A port or class query checks a single
parent candidate at its genuine edge index. -/
noncomputable def Request.test (r : Request) (q : EndpointQuery) (l : Labels) (j : ℕ) : Bool :=
  match r with
  | .vertex _ => decide ((l.split q).label j = l.group)
  | .port col _ => atEndpoint q j fun p =>
      decide ((l.split q).label (if col then p.2 else p.1) = l.group)
  | .pack e p => decide (j < e) && atEndpoint q j fun x =>
      decide (l.code x.1 = l.code p.1 ∧ l.code x.2 = l.code p.2)

private theorem countP_range (n : ℕ) (f : ℕ → Bool) :
    (List.range n).countP f = ∑ j ∈ Finset.range n, (f j).toNat := by
  rw [List.countP_range_eq_card_filter, Finset.card_eq_sum_ones, Finset.sum_filter,
    ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  cases f i <;> rfl

/-- The identical carry-lookahead input convention serves all three counts. -/
theorem Request.value_eq (r : Request) (q : EndpointQuery) (l : Labels) :
    r.value q l = ∑ j ∈ Finset.range (r.size q l), (r.test q l j).toNat := by
  classical
  cases r with
  | vertex bound =>
    simp only [value, size, Split.vertexRank, countP_range, test, Labels.split]
    apply Finset.sum_congr rfl
    intro j _
    congr 2
  | port col bound =>
    cases col <;> simp only [value, size, portCount, countP_range, test, atEndpoint, Labels.split,
      Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq]
  | pack e p =>
    simp only [value, size, classCount, test, atEndpoint, decide_eq_true_eq]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j < e <;> simp [hj]

/-- Decoded recursive counting context shared by all bit queries. -/
abbrev Context := EndpointQuery × Labels × Request

/-- Common label assignment used to interpret a recursive count. -/
abbrev Context.labels (ctx : Context) : Labels := ctx.2.1

/-- The count selected by the decoded context. -/
abbrev Context.request (ctx : Context) : Request := ctx.2.2

/-- A single alternating counter checks recursive vertex, port, and class-rank bits. The
interpretation of context words and its alternating six-tape leaf are chosen before all runtime
requests. Leaf correctness and time on the concrete layout are explicit premises. -/
theorem exists_evaluator (decode : List Bool → Context) {k : ℕ} {S : Type}
    [Finite S] (next : Bool → MultiTapeATM (6 + (k + 2)) Bool S) :
    let predicate := fun x : List Bool × ℕ =>
      let d := decode x.1
      d.request.test d.1 d.labels x.2
    ∃ (scratch r t : ℕ) (Q : Type) (_ : Finite Q)
      (atm : MultiTapeATM (CarryLookaheadCountingPrepare.size scratch k r t) Bool Q) (A D : ℕ),
      ∀ (input context : List Bool) (w : ℕ) (bit : Fin w) (claim : Bool) (baseTime : ℕ),
        let d := decode context
        let n := d.request.size d.1 d.labels
        let budget := CarrySaveCountingRoot.sizeBudget n w
        CarryLookaheadCountingRawLeaves.RawSpec next predicate input context
          (encNat n) (encNat w) budget baseTime →
        let params : CountingInput.Input := ⟨n, ⟨w, bit.val, claim⟩⟩
        let start := (CarryLookaheadCountingPrepare.initial scratch k r t input context
          params).withState (some atm.toPTM.initial)
        let time := A * (n.size + w.size + 1) ^ D + (budget + 3) + baseTime
        atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔
          (d.request.value d.1 d.labels).testBit bit.val = claim) := by
  intro predicate
  obtain ⟨s, r, t, Q, hQ, atm, A, D, h⟩ :=
    CarryLookaheadCountingRawLeaves.exists_evaluator next predicate
  refine ⟨s, r, t, Q, hQ, atm, A, D, ?_⟩
  intro input context w bit claim baseTime d n budget hraw
  rw [Request.value_eq]
  exact h input context n w bit claim baseTime hraw

end Turing.MultiTapeATM.SeededChildCounts
