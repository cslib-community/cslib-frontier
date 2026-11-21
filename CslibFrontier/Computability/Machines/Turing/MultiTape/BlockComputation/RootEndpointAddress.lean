/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.ExplicitBlockNetwork.Graph
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Sum
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Sum

/-!
# Binary arithmetic for root endpoint requests

Each admitted root half-edge has a known subdivision column. Its row is either known directly
or is found by a single work-head query. Classification uses only the binary pair count, copy
count and half-edge index. The raw movement table is needed only for the work-head continuation.
-/

public section

namespace Turing.MultiTapeTM.RootEndpointAddress

open MultiTapePTM ComputableInPolyTime

/-- Binary addresses of one root half-edge. -/
structure Input where
  /-- Number of two-bit movements in all complete rows. -/
  pairs : ℕ
  /-- Boolean copies of each block edge. -/
  copies : ℕ
  /-- Number of the requested half-edge. -/
  edge : ℕ
  deriving DecidableEq

/-- Framed binary pair and copy counts followed by the binary edge number. -/
enc_structure encInput : Input where pairs : encNat, copies : encNat, edge : encNat

/-- The remaining scanner parameters and its fallback row for an exhausted search. -/
structure Work where
  /-- Work head and port, numbered by `3 * head + port`. -/
  selector : ℕ
  /-- Current interval, excluded from the forward search. -/
  interval : ℕ
  /-- Sink for this particular block edge. -/
  sink : ℕ
  deriving DecidableEq

/-- Framed binary selector and interval followed by the binary sink. -/
enc_structure encWork : Work where selector : encNat, interval : encNat, sink : encNat

/-- One tag followed by a direct binary row or by its encoded work request. -/
abbrev encRow : ℕ ⊕ Work ↪ List Bool := encSum encNat encWork

/-- The two endpoints still to be resolved, with an already numbered column. -/
structure Address where
  /-- Row endpoint, either ready or waiting for the scanner. -/
  row : ℕ ⊕ Work
  /-- Number of the subdivision vertex for this copy. -/
  column : ℕ
  deriving DecidableEq

/-- Framed tagged row followed by the binary column. -/
enc_structure encAddress : Address where row : encRow, column : encNat

/-- Optional encoded address. The empty word denotes rejection. -/
abbrev encResult := encOption encAddress

/-- Number of complete intervals, from a binary count of the movement pairs. -/
@[expose] def intervals (k : ℕ) (a : Input) : ℕ := a.pairs / (k + 1)

/-- Number of edges after copying and subdividing. -/
@[expose] def edgeCount (k : ℕ) (a : Input) : ℕ := 2 * (intervals k a * (3 * k + 1) * a.copies)

/-- Control targets are known directly. Work targets give the scanner a head/port and interval. -/
@[expose] def targetRow (k q n : ℕ) : ℕ ⊕ Work :=
  if n < q then .inl (if n + 1 < q then n + 1 else q + n)
  else .inr ⟨(n - q) % (k * 3), (n - q) / (k * 3), q + n⟩

/-- A genuine work edge requests an existing head, port and interval, and its fallback row
lies in the original (unsubdivided) vertex universe. -/
private theorem targetRow_work_bounds {k q n : ℕ} {w : Work} (hn : n < q * (3 * k + 1))
    (hw : targetRow k q n = .inr w) :
    w.selector < 3 * k ∧ w.interval < q ∧ w.sink < q * (3 * k + 2) := by
  by_cases h : n < q
  · simp [targetRow, h] at hw
  · simp only [targetRow, h, ↓reduceIte, Sum.inr.injEq] at hw
    subst w
    have hq : n - q < q * (k * 3) := by
      rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm 3 k] at hn
      omega
    have hk : 0 < k * 3 := by
      by_cases hzero : k * 3 = 0
      · simp [hzero] at hq
      · omega
    refine ⟨?_, (Nat.div_lt_iff_lt_mul hk).2 hq, ?_⟩
    · simpa only [Nat.mul_comm 3 k] using Nat.mod_lt (n - q) hk
    · rw [Nat.mul_add, Nat.mul_one] at hn
      rw [Nat.mul_add, Nat.mul_two]
      dsimp
      omega

/-- Classify an edge after checking the actual universe, before dividing by the copy count. -/
@[expose] def query (k : ℕ) (a : Input) : Option Address :=
  if a.edge < edgeCount k a then
    let q := intervals k a
    let half := q * (3 * k + 1) * a.copies
    let row := if a.edge < half then .inl (blockSrcNum k q (a.edge / a.copies))
      else targetRow k q ((a.edge - half) / a.copies)
    some ⟨row, explicitTgtNum k q a.copies a.edge⟩
  else none

/-- Rejected addresses are exactly the padded or empty-universe addresses. -/
theorem query_isSome (k : ℕ) (a : Input) :
    (query k a).isSome = decide (a.edge < edgeCount k a) := by
  by_cases h : a.edge < edgeCount k a <;> simp [query, h]

/-- Only genuine work selectors, intervals and sinks are returned by classification. -/
theorem query_work_bounds {k : ℕ} {a : Input} {w : Work} {column : ℕ}
    (h : query k a = some ⟨.inr w, column⟩) :
    w.selector < 3 * k ∧ w.interval < intervals k a ∧
      w.sink < intervals k a * (3 * k + 2) := by
  let q := intervals k a
  let half := q * (3 * k + 1) * a.copies
  have he : a.edge < 2 * half := by
    by_cases h' : a.edge < edgeCount k a
    · exact h'
    · simp [query, h'] at h
  have hc : 0 < a.copies := by
    cases hz : a.copies with
    | zero => simp [half, hz] at he
    | succ => omega
  have hrow := congrArg (Option.map Address.row) h
  change (if a.edge < 2 * half then _ else none).map _ = _ at hrow
  simp only [he, ↓reduceIte, Option.map_some, Option.some.injEq] at hrow
  change (if a.edge < half then .inl (blockSrcNum k q (a.edge / a.copies)) else
    targetRow k q ((a.edge - half) / a.copies)) = .inr w at hrow
  by_cases hs : a.edge < half
  · simp [hs] at hrow
  · apply targetRow_work_bounds (q := q) (n := (a.edge - half) / a.copies)
    · apply (Nat.div_lt_iff_lt_mul hc).2
      change a.edge - half < half
      omega
    · simpa only [hs, ↓reduceIte] using hrow

/-- Exact size of a classifier input, including its two framed binary numbers. -/
theorem length_encInput (a : Input) :
    (encInput a).length = 2 * a.pairs.bits.length + 2 * a.copies.bits.length +
      a.edge.bits.length + 2 := by
  simp only [encInput_apply, encInputFields, length_encPair, encNat_apply]
  omega

private theorem targetRow_polyTime {α : Type} {inp : α ↪ List Bool} (k : ℕ) {q n : α → ℕ}
    (hq : ComputableInPolyTime q inp encNat) (hn : ComputableInPolyTime n inp encNat) :
    ComputableInPolyTime (fun a => targetRow k (q a) (n a)) inp encRow := by
  let hd := binary_sub' hn hq
  let hk : ComputableInPolyTime (fun _ : α => k * 3) inp encNat := const _
  let hs := binary_add' hq hn
  let hn' := binary_add' hn (const 1)
  exact ite_decide (binary_lt' hn hq)
    ((sumInl encNat encWork).comp (ite_decide (binary_lt' hn' hq) hn' hs))
    ((sumInr encNat encWork).comp (encWork_mk_polyTime (binary_mod' hd hk) (binary_div' hd hk) hs))

/-- One polynomial-time classifier on the three binary numbers. Its certificate charges no
operation to the length of the raw table itself. -/
theorem query_polyTime (k : ℕ) : ComputableInPolyTime (query k) encInput encResult := by
  have hp : ComputableInPolyTime Input.pairs encInput encNat := by fun_prop
  have hc : ComputableInPolyTime Input.copies encInput encNat := by fun_prop
  have he : ComputableInPolyTime Input.edge encInput encNat := by fun_prop
  have hq : ComputableInPolyTime (intervals k) encInput encNat := binary_div' hp (const _)
  let hh := binary_mul' (binary_mul' hq (const (3 * k + 1))) hc
  let hs := binary_div' he hc
  let ht := binary_sub' he hh
  have hb := binary_lt' he hh
  have hrow := ite_decide (binary_lt' hs hq) hs (binary_div' (binary_sub' hs hq) (const (k * 3)))
  unfold query
  refine ite_decide (binary_lt' he (binary_mul' (const 2) hh)) ?_ (const none)
  apply (optionSome encAddress).comp
  apply encAddress_mk_polyTime
  · exact ite_decide hb ((sumInl encNat encWork).comp hrow)
      (targetRow_polyTime k hq (binary_div' ht hc))
  · exact binary_add' (binary_mul' hq (const (3 * k + 2))) (ite_decide hb he ht)

/-- Binary scanner indices. Direct and rejected addresses supply harmless zeros. -/
@[expose] def scanIndices (a : Option Address) : ℕ × ℕ :=
  let w := (a.getD ⟨.inl 0, 0⟩).row.getRight?.getD ⟨0, 0, 0⟩
  (w.selector, w.interval)

/-- A work address supplies precisely its selected runtime scanner indices. -/
@[simp] theorem scanIndices_work (w : Work) (column : ℕ) :
    scanIndices (some ⟨.inr w, column⟩) = (w.selector, w.interval) := rfl

/-- The scanner consumes binary keys computed only from the short classifier result. -/
theorem computableInPolyTime_scanIndices :
    ComputableInPolyTime scanIndices encResult (encPair encNat encNat) := by
  have ha : ComputableInPolyTime (fun a : Option Address => a.getD ⟨.inl 0, 0⟩)
      encResult encAddress := optionGetDWithInput .id' (.const _)
  have hr := (ComputableInO.getRight?_deg encNat encWork).computableInPolyTime.comp
    (encAddress_row_polyTime ha)
  have hw := optionGetDWithInput hr (.const ⟨0, 0, 0⟩)
  exact (encWork_selector_polyTime hw).prod (encWork_interval_polyTime hw)

end Turing.MultiTapeTM.RootEndpointAddress
