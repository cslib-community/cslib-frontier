/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Sort.AdjacentTrace
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Prefix
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size

/-!
# Plain native cost of stable adjacent trace generation

`encResult` stores binary original keys followed by binary request positions, with the
ordinary pair/list framing. The joint insertion certificate covers EVERY raw accumulator,
including huge arbitrary old requests. The outer fold establishes its own storage bound:
keys retain their encoded mass, there are at most quadratically many requests, and request
widths are at most the actual input list length. Shifting/copying the trace is charged, not
just the insertion sort comparison count. This is original instrumentation cost analysis.
-/

public section

namespace Cslib.AdjacentSortTrace

open Turing.MultiTapeTM Cslib.BitString

/-- Binary sorted original keys first (framed), then binary requests; each list uses the
standard framed element encoding. No unary key or binary-value-funded clock is used. -/
enc_structure encResult : Result where
  sortedKeys : (encList encNat),
  requests : (encList encNat)

private theorem insert_polyTime :
    ComputableInPolyTime (fun p : Result × ℕ => insert p.2 p.1)
      (encPair encResult encNat) encResult := by
  have ha := ComputableInPolyTime.snd encResult encNat
  have hk : ComputableInPolyTime (fun p : Result × ℕ => p.1.sortedKeys)
      (encPair encResult encNat) (encList encNat) := by fun_prop
  have hp : ComputableInPolyTime
      (fun p : (Result × ℕ) × ℕ => decide (p.2 < p.1.2))
      (encPair (encPair encResult encNat) encNat) encBool := by fun_prop
  have ht := ComputableInPolyTime.takeWhileWithInput (pred := fun p b => decide (b < p.2)) hk hp
  have hd := ComputableInPolyTime.dropWhileWithInput (pred := fun p b => decide (b < p.2)) hk hp
  have ho : ComputableInPolyTime
      (fun p : Result × ℕ => List.orderedInsert (· ≤ ·) p.2 p.1.sortedKeys)
      (encPair encResult encNat) (encList encNat) := by
    convert ComputableInPolyTime.listAppend' ht (ComputableInPolyTime.cons' ha hd) using 1
    funext p
    simp [List.orderedInsert_eq_take_drop]
  have hn : ComputableInPolyTime
      (fun p : Result × ℕ => (p.1.sortedKeys.takeWhile (fun b => b<p.2)).length)
      (encPair encResult encNat) encUnary := by fun_prop
  have hru := ComputableInPolyTime.range.comp hn
  have hnew : ComputableInPolyTime
      (fun p : Result × ℕ => List.range (p.1.sortedKeys.takeWhile (fun b => b<p.2)).length)
      (encPair encResult encNat) (encList encNat) := by
    convert (ComputableInPolyTime.mapWithInput (f := fun (_ : Result × ℕ) (n : ℕ) => n) hru
        (ComputableInPolyTime.unary_to_binary.comp
          (ComputableInPolyTime.snd (encPair encResult encNat) encUnary))) using 1
    funext p
    simp
  have hold : ComputableInPolyTime
      (fun p : Result × ℕ => p.1.requests.map Nat.succ)
      (encPair encResult encNat) (encList encNat) := by
    apply ComputableInPolyTime.mapWithInput (by fun_prop)
    simpa only [Nat.succ_eq_add_one] using
      (ComputableInPolyTime.binary_add' (ComputableInPolyTime.snd _ _)
        (ComputableInPolyTime.const 1))
  exact encResult_mk_polyTime ho (ComputableInPolyTime.listAppend' hold hnew)

private def budget (keys : List ℕ) : ℕ :=
  16 * ((encList encNat keys).length+1)^3

private theorem prefix_size (keys consumed : List ℕ) (hp : consumed <+: keys.reverse) :
    (encResult (compute consumed.reverse)).length ≤ budget keys := by
  let S := (encList encNat keys).length
  let P := keys.length
  have hPS : P ≤ S := SizedListEncoding.length_le encNat keys
  have hq : consumed.length ≤ P := by simpa only [List.length_reverse] using hp.length_le
  have hc := components_compute consumed.reverse
  have hmass : (encList encNat (compute consumed.reverse).sortedKeys).length ≤ S := by
    rw [hc.1]
    have hperm := (List.perm_insertionSort (· ≤ ·) consumed.reverse).flatMap_right
      (Turing.MultiTapeTM.frame ∘ encNat)
    change ((consumed.reverse.insertionSort (· ≤ ·)).flatMap
      (Turing.MultiTapeTM.frame ∘ encNat)).length ≤ S
    rw [hperm.length_eq]
    apply length_encList_sublist encNat
    simpa only [List.reverse_reverse] using hp.sublist.reverse
  have hcount : (compute consumed.reverse).requests.length ≤ P*P := by
    have hchoose : consumed.length.choose 2 ≤ consumed.length*consumed.length := by
      rw [Nat.choose_two_right]
      exact (Nat.div_le_self _ _).trans
        (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
    exact (hc.2.1.trans (by simpa only [List.length_reverse] using hchoose)).trans
      (Nat.mul_le_mul hq hq)
  have hwidth : ∀ j ∈ (compute consumed.reverse).requests, (encNat j).length ≤ P := by
    intro j hj
    have hv := hc.2.2 j hj
    rw [encNat_apply, Nat.size_eq_bits_len]
    have hs := Nat.size_le_self j
    simp only [List.length_reverse] at hv
    omega
  have hrequests := length_encList_le encNat (compute consumed.reverse).requests hwidth
  have hrequests' : (encList encNat (compute consumed.reverse).requests).length ≤
      (S*S)*(2*S+1) :=
    hrequests.trans ((Nat.mul_le_mul_right _ hcount).trans
      (Nat.mul_le_mul (Nat.mul_le_mul hPS hPS) (by omega)))
  rw [encResult_apply, encResultFields, length_encPair]
  change 2*(encList encNat (compute consumed.reverse).sortedKeys).length+1+
    (encList encNat (compute consumed.reverse).requests).length ≤ budget keys
  apply (Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.mul_le_mul_left 2 hmass) 1) _).trans
  apply (Nat.add_le_add_left hrequests' _).trans
  dsimp [budget]
  change 2*S+1+S*S*(2*S+1) ≤ 16*(S+1)^3
  nlinarith [Nat.zero_le (S*S*S), Nat.zero_le (S*S)]

/-- Generate the actual stable trace on EVERY binary key list in plain polynomial time.
The actual list length clocks the fold/scans/ranges; reachable key mass, quadratic request
count and linear index width prove the accumulator bound internally. -/
theorem computableInPolyTime_compute :
    ComputableInPolyTime compute (encList encNat) encResult := by
  have hr : ComputableInPolyTime (fun keys : List ℕ => keys.reverse)
      (encList encNat) (encList encNat) :=
    ComputableInPolyTime.listReverseWithInput ComputableInPolyTime.id'
  have hb : PolyBounded (fun keys : List ℕ => (encList encNat keys).length) budget :=
    (PolyBounded.const 16).mul ((PolyBounded.self.add (.const 1)).pow 3)
  exact (ComputableInPolyTime.foldl_spec hr (ComputableInPolyTime.const (⟨[], []⟩ : Result))
    insert_polyTime
    (fun _ consumed state => state=consumed.foldl (fun r a => insert a r) ⟨[], []⟩)
    (fun _ => rfl)
    (fun _ consumed state value _ hs => by
      simp only [hs, List.foldl_append, List.foldl_cons, List.foldl_nil])
    hb (fun keys consumed state hp hs => by
      rw [hs]
      simpa only [compute, List.reverse_reverse] using prefix_size keys consumed hp)).1

end Cslib.AdjacentSortTrace
