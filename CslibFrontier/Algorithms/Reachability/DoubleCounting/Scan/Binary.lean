/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Reachability.DoubleCounting.Scan
public import CslibFrontier.Foundations.Data.BitString.List.Binary
import Mathlib.Data.Nat.Size

/-!
# Canonical binary scan traces

Vertex IDs use `Nat.size N` bits, most significant first. Zero means skip and one means
select. A selected walk is a sequence of one/ID blocks terminated by zero; the source is
implicit. The walk budget bounds the number of destinations, without padding. Exactly `N`
segments occur, in increasing vertex order, and the complete decoder requires end of input.
The width is the bit length of `N`, so power-of-two carrier sizes have a leading zero digit.
`N = 0` has no segments and accepts only the empty word.

## Main results

* `decode_eq_some_iff`: exact bounded canonical decoding.
* `decode_encode_append`: rejection of any nonempty final suffix.
* `length_encode_le`: at most `N * (k * (N.size + 1) + 2)` bits.
* `replay_expected_eq_some_iff`: exact typed passing-transcript and answer-bit contract.
* `successfulTraces`, `successfulTranscripts`: multiplicity-preserving bijections.

The ordinary-import client is `CslibFrontierTests.DoubleCountingScanBinary`.
The existing `binaryWord` and `binaryValue` APIs provide fixed-width ID encoding and decoding;
unary `encFinEnum` would give a different resource contract.

This original finite-word codec connects to typed scan replay. It is not a native machine or a
workspace certificate and does not establish first-halting native replay; those obligations
remain in [#6747](https://github.com/cslib-community/cslib-frontier/issues/6747).
-/

public section

namespace Cslib.DoubleCounting.Scan.Binary

open Cslib.BitString

variable {N : ℕ}

/-- Fixed-width most-significant-first vertex ID. -/
@[expose] def vertex (v : Fin N) : List Bool := binaryWord N.size v.val

private theorem vertex_lt (v : Fin N) : v.val < 2 ^ N.size :=
  v.isLt.trans (Nat.lt_size_self N)

/-- Every ID has the declared width. -/
@[simp] theorem length_vertex (v : Fin N) : (vertex v).length = N.size :=
  length_binaryWord (vertex_lt v)

/-- Decode a whole ID, rejecting wrong widths and out-of-range values. -/
@[expose] def decodeVertex (bits : List Bool) : Option (Fin N) :=
  if bits.length = N.size then
    if h : binaryValue bits < N then some ⟨binaryValue bits, h⟩ else none
  else none

/-- Exact canonical ID decoding. -/
theorem decodeVertex_eq_some_iff (bits : List Bool) (v : Fin N) :
    decodeVertex bits = some v ↔ bits = vertex v := by
  refine ⟨fun h => ?_, ?_⟩
  · simp only [decodeVertex, Option.ite_none_right_eq_some, Option.dite_none_right_eq_some,
      Option.some.injEq] at h
    obtain ⟨hlen, _, rfl⟩ := h
    exact binaryValue_injective_of_length_eq (hlen.trans (length_vertex _).symm) (by simp [vertex])
  · rintro rfl
    rw [decodeVertex, ite_eq_left (length_vertex v)]
    simp [vertex]

/-- Correctly sized out-of-range IDs are rejected, as are wrong widths. -/
theorem decodeVertex_out_of_range (bits : List Bool) (h : N ≤ binaryValue bits) :
    decodeVertex (N := N) bits = none := by
  simp [decodeVertex, Nat.not_lt.mpr h]

/-- Read exactly one ID and retain the suffix. -/
@[expose] def readVertex (bits : List Bool) : Option (Fin N × List Bool) :=
  (decodeVertex (bits.take N.size)).map (fun v => (v, bits.drop N.size))

/-- Prefix decoding recovers precisely the ID and its suffix. -/
theorem readVertex_eq_some_iff (bits rest : List Bool) (v : Fin N) :
    readVertex bits = some (v, rest) ↔ bits = vertex v ++ rest := by
  simp only [readVertex, Option.map_eq_some_iff, Prod.mk.injEq,
    decodeVertex_eq_some_iff]
  refine ⟨?_, fun h => ⟨v, by simp [h], rfl, by simp [h]⟩⟩
  rintro ⟨_, ha, rfl, rfl⟩
  exact ha ▸ (List.take_append_drop N.size bits).symm

/-- Destinations followed by a stop bit; the source is implicit. -/
@[expose] def destinations : List (Fin N) → List Bool
  | [] => [false]
  | v :: vs => true :: (vertex v ++ destinations vs)

/-- Budgeted prefix parser. Continuing after exhausting the budget rejects. -/
@[expose] def readDestinations : ℕ → List Bool → Option (List (Fin N) × List Bool)
  | _, [] => none
  | _, false :: rest => some ([], rest)
  | 0, true :: _ => none
  | k + 1, true :: rest => do
    let (v, rest) ← readVertex rest
    let (vs, rest) ← readDestinations k rest
    return (v :: vs, rest)

/-- Successful destination parsing is canonical and budgeted. -/
theorem readDestinations_eq_some_iff (k : ℕ) (bits rest : List Bool)
    (vs : List (Fin N)) :
    readDestinations k bits = some (vs, rest) ↔
      vs.length ≤ k ∧ bits = destinations vs ++ rest := by
  induction k generalizing bits rest vs with
  | zero =>
    rcases bits with _ | ⟨_ | _, bits⟩ <;> cases vs <;> simp [readDestinations, destinations]
  | succ k ih =>
    rcases bits with _ | ⟨_ | _, bits⟩
    · cases vs <;> simp [readDestinations, destinations]
    · cases vs <;> simp [readDestinations, destinations]
    · cases vs with
      | nil => simp [readDestinations, destinations, Option.bind_eq_some_iff]
      | cons v vs =>
        simp only [readDestinations, bind, Option.bind_eq_some_iff, pure,
          Option.some.injEq, Prod.mk.injEq, readVertex_eq_some_iff, ih, Prod.exists,
          List.cons.injEq, destinations, List.cons_append, List.length_cons,
          Nat.add_le_add_iff_right, true_and]
        constructor
        · rintro ⟨_, tail, rfl, _, _, ⟨hl, rfl⟩, ⟨rfl, rfl⟩, rfl⟩
          exact ⟨hl, (List.append_assoc _ _ _).symm⟩
        · rintro ⟨hl, rfl⟩
          exact ⟨v, destinations vs ++ rest, List.append_assoc _ _ _,
            vs, rest, ⟨hl, rfl⟩, ⟨rfl, rfl⟩, rfl⟩

/-- Skip is zero; select is one followed by a terminated destination list. -/
@[expose] def segment : Option (List (Fin N)) → List Bool
  | none => [false]
  | some vs => true :: destinations vs

/-- Prefix parser for one skip/select segment. -/
@[expose] def readSegment (k : ℕ) : List Bool → Option (Option (List (Fin N)) × List Bool)
  | [] => none
  | false :: rest => some (none, rest)
  | true :: rest => (readDestinations k rest).map (fun (vs, rest) => (some vs, rest))

/-- Segment parsing has no alternative successful representations. -/
theorem readSegment_eq_some_iff (k : ℕ) (bits rest : List Bool)
    (s : Option (List (Fin N))) :
    readSegment k bits = some (s, rest) ↔
      (∀ vs, s = some vs → vs.length ≤ k) ∧ bits = segment s ++ rest := by
  cases bits with
  | nil => cases s <;> simp [readSegment, segment]
  | cons b bits =>
    cases b <;> cases s <;>
      simp [readSegment, segment, Option.map_eq_some_iff, readDestinations_eq_some_iff]

/-- Encode consecutive segments without a final padding block. -/
@[expose] def entries : List (Option (List (Fin N))) → List Bool
  | [] => []
  | s :: ss => segment s ++ entries ss

/-- Read exactly the declared number of segments. -/
@[expose] def readEntries (k : ℕ) : ℕ → List Bool →
    Option (List (Option (List (Fin N))) × List Bool)
  | 0, bits => some ([], bits)
  | n + 1, bits => do
    let (s, rest) ← readSegment k bits
    let (ss, rest) ← readEntries k n rest
    return (s :: ss, rest)

/-- Exact prefix contract for a fixed number of bounded segments. -/
theorem readEntries_eq_some_iff (k n : ℕ) (bits rest : List Bool)
    (ss : List (Option (List (Fin N)))) :
    readEntries k n bits = some (ss, rest) ↔
      ss.length = n ∧ (∀ s ∈ ss, ∀ vs, s = some vs → vs.length ≤ k) ∧
        bits = entries ss ++ rest := by
  induction n generalizing bits rest ss with
  | zero => cases ss <;> simp [readEntries, entries, eq_comm]
  | succ n ih =>
    cases ss with
    | nil => simp [readEntries, Option.bind_eq_some_iff]
    | cons s ss =>
      simp only [readEntries, bind, Option.bind_eq_some_iff, pure,
        Option.some.injEq, Prod.mk.injEq, readSegment_eq_some_iff, ih, Prod.exists,
        List.cons.injEq, entries, List.length_cons, Nat.add_right_cancel_iff,
        List.mem_cons, forall_eq_or_imp]
      constructor
      · rintro ⟨_, tail, ⟨hseg, rfl⟩, _, _, ⟨hl, hs, rfl⟩, ⟨rfl, rfl⟩, rfl⟩
        exact ⟨hl, ⟨hseg, hs⟩, (List.append_assoc _ _ _).symm⟩
      · rintro ⟨hl, ⟨hseg, hs⟩, rfl⟩
        exact ⟨s, entries ss ++ rest, ⟨hseg, List.append_assoc _ _ _⟩,
          ss, rest, ⟨hl, hs, rfl⟩, ⟨rfl, rfl⟩, rfl⟩

/-- Encode the branch in increasing vertex order. -/
@[expose] def encode (b : Branch N) : List Bool := entries (List.ofFn b)

/-- Whole-word decoder. Extra bits after the final vertex reject. -/
@[expose] def decode (k : ℕ) (bits : List Bool) : Option (Branch N) := do
  let (ss, rest) ← readEntries k N bits
  if h : ss.length = N then
    if rest = [] then return fun v => ss[v.val]'(by omega)
    else none
  else none

/-- Canonical whole-word decoding is equivalent to bounded encoding with no suffix. -/
theorem decode_eq_some_iff (k : ℕ) (bits : List Bool) (b : Branch N) :
    decode k bits = some b ↔ Bounded k b ∧ bits = encode b := by
  constructor
  · intro h
    unfold decode at h
    simp only [bind, Option.bind_eq_some_iff, Prod.exists] at h
    obtain ⟨ss, rest, hs, hb⟩ := h
    split at hb
    · split at hb
      · subst rest
        obtain rfl : ss = List.ofFn b :=
          List.ext_getElem (by simp [*]) fun _ _ _ => by simp [← Option.some.inj hb]
        obtain ⟨_, hbound, hbits⟩ := (readEntries_eq_some_iff k N bits [] (List.ofFn b)).mp hs
        exact ⟨fun v vs hv => hbound (b v) (List.mem_ofFn.mpr ⟨v, rfl⟩) vs hv,
          by simpa [encode] using hbits⟩
      · cases hb
    · cases hb
  · rintro ⟨hbound, rfl⟩
    have hp : readEntries k N (encode b) = some (List.ofFn b, []) :=
      (readEntries_eq_some_iff _ _ _ _ _).mpr
        ⟨by simp, by simpa [Bounded] using hbound, by simp [encode]⟩
    simp [decode, hp]

/-- Every bounded branch decodes from its encoding. -/
theorem decode_encode (k : ℕ) (b : Branch N) (hb : Bounded k b) :
    decode k (encode b) = some b := (decode_eq_some_iff _ _ _).mpr ⟨hb, rfl⟩

/-- Distinct bounded branches remain distinct binary traces. -/
theorem encode_injective (k : ℕ) {a b : Branch N}
    (ha : Bounded k a) (hb : Bounded k b) (h : encode a = encode b) : a = b :=
  Option.some.inj ((decode_encode k a ha).symm.trans (h ▸ decode_encode k b hb))

/-- Any nonempty suffix after a bounded branch is rejected, including zero padding. -/
theorem decode_encode_append (k : ℕ) (b : Branch N) (hb : Bounded k b)
    (rest : List Bool) :
    decode k (encode b ++ rest) = if rest = [] then some b else none := by
  have hp : readEntries k N (encode b ++ rest) = some (List.ofFn b, rest) :=
    (readEntries_eq_some_iff _ _ _ _ _).mpr
      ⟨by simp, by simpa [Bounded] using hb, rfl⟩
  simp [decode, hp]

/-- Exact bit count of a destination stream, including its stop marker. -/
theorem length_destinations (vs : List (Fin N)) :
    (destinations vs).length = vs.length * (N.size + 1) + 1 := by
  induction vs with
  | nil => simp [destinations]
  | cons v vs ih => simp [destinations, ih, Nat.add_mul]; omega

private theorem length_segment_le (s : Option (List (Fin N))) (k : ℕ)
    (h : ∀ vs, s = some vs → vs.length ≤ k) :
    (segment s).length ≤ k * (N.size + 1) + 2 := by
  cases s with
  | none => simp [segment]
  | some vs =>
    have hm := Nat.mul_le_mul_right (N.size + 1) (h vs rfl)
    simp only [segment, List.length_cons, length_destinations]
    omega

private theorem length_entries_le (ss : List (Option (List (Fin N)))) (k : ℕ)
    (h : ∀ s ∈ ss, ∀ vs, s = some vs → vs.length ≤ k) :
    (entries ss).length ≤ ss.length * (k * (N.size + 1) + 2) := by
  induction ss with
  | nil => simp [entries]
  | cons s ss ih =>
    have hs := length_segment_le s k (h s (by simp))
    have ht := ih (fun t ht => h t (by simp [ht]))
    simp only [entries, List.length_append, List.length_cons, Nat.succ_mul]
    omega

/-- Uniform binary trace bound for bounded branches. No rejected-ID wraparound is used. -/
theorem length_encode_le (k : ℕ) (b : Branch N) (hb : Bounded k b) :
    (encode b).length ≤ N * (k * (N.size + 1) + 2) := by
  simpa [encode] using length_entries_le (List.ofFn b) k (by simpa [Bounded] using hb)

/-- Decode and replay the existing typed scanner. `some false` is successful rejection-free
negative membership; `none` covers malformed words and failed typed checks. -/
@[expose] def replay (edge : Fin N → Fin N → Bool) (source target : Fin N)
    (k : ℕ) (totals : Tally) (bits : List Bool) : Option Bool :=
  (decode k bits).bind (Scan.run edge source target k totals)

/-- Binary success means one canonical bounded typed branch with the same result. -/
theorem replay_eq_some_iff (edge : Fin N → Fin N → Bool) (source target : Fin N)
    (k : ℕ) (totals : Tally) (bits : List Bool) (hit : Bool) :
    replay edge source target k totals bits = some hit ↔
      ∃ b : Branch N, Bounded k b ∧ bits = encode b ∧
        Scan.run edge source target k totals b = some hit := by
  simp only [replay, Option.bind_eq_some_iff, decode_eq_some_iff]
  exact ⟨fun ⟨b, ⟨hb, he⟩, hr⟩ => ⟨b, hb, he, hr⟩,
    fun ⟨b, hb, he, hr⟩ => ⟨b, ⟨hb, he⟩, hr⟩⟩

/-- With exact totals, binary success is precisely the existing passing-transcript contract.
This statement retains the answer bit, including successful `false`. -/
theorem replay_expected_eq_some_iff (edge : Fin N → Fin N → Bool) (source target : Fin N)
    (k : ℕ) (bits : List Bool) (hit : Bool) :
    replay edge source target k (expected (fun u v => edge u v = true) source k) bits =
        some hit ↔
      ∃ b : Branch N, bits = encode b ∧
        Passes (fun u v => edge u v = true) source k (transcript source b) ∧
        (b target).isSome = hit := by
  rw [replay_eq_some_iff]
  exact ⟨fun ⟨b, _, he, hr⟩ => ⟨b, he, (Scan.run_eq_some_iff ..).mp hr⟩,
    fun ⟨b, he, hp, hh⟩ => ⟨b, bounded_of_passes source k b hp, he,
      (Scan.run_eq_some_iff ..).mpr ⟨hp, hh⟩⟩⟩

/-- Encoding commutes with typed replay, without collapsing negative answers into rejection. -/
theorem replay_encode (edge : Fin N → Fin N → Bool) (source target : Fin N)
    (k : ℕ) (totals : Tally) (b : Branch N) (hb : Bounded k b) :
    replay edge source target k totals (encode b) = Scan.run edge source target k totals b := by
  simp [replay, decode_encode k b hb]

private theorem bounded_of_success (edge : Fin N → Fin N → Bool) (source target : Fin N)
    (k : ℕ) (b : Branch N)
    (h : (Scan.run edge source target k
      (expected (fun u v => edge u v = true) source k) b).isSome) : Bounded k b := by
  obtain ⟨hit, hh⟩ := Option.isSome_iff_exists.mp h
  exact bounded_of_passes source k b ((Scan.run_eq_some_iff _ _ _ _ _ _).mp hh).1

/-- A bijection of successful branches, rather than just a correspondence of answer sets.
Consequently equal verdicts from distinct branches retain their multiplicity. -/
noncomputable def successfulTraces (edge : Fin N → Fin N → Bool) (source target : Fin N)
    (k : ℕ) :
    {b : Branch N // (Scan.run edge source target k
      (expected (fun u v => edge u v = true) source k) b).isSome} ≃
    {bits : List Bool // (replay edge source target k
      (expected (fun u v => edge u v = true) source k) bits).isSome} :=
  Equiv.ofBijective
    (fun b => ⟨encode b.val, by
      rw [replay_encode _ _ _ _ _ _ (bounded_of_success _ _ _ _ _ b.property)]
      exact b.property⟩)
    ⟨fun a b h => Subtype.ext (encode_injective k
        (bounded_of_success _ _ _ _ _ a.property)
        (bounded_of_success _ _ _ _ _ b.property) (congrArg Subtype.val h)), by
      intro bits
      obtain ⟨hit, hh⟩ := Option.isSome_iff_exists.mp bits.property
      obtain ⟨b, _, he, hr⟩ := (replay_eq_some_iff _ _ _ _ _ _ _).mp hh
      exact ⟨⟨b, Option.isSome_iff_exists.mpr ⟨hit, hr⟩⟩, Subtype.ext he.symm⟩⟩

/-- Exact successful binary trace / passing transcript equivalence, reusing the typed scan
bijection. This is a finite replay theorem, not a native first-halting compiler theorem. -/
noncomputable def successfulTranscripts (edge : Fin N → Fin N → Bool)
    (source target : Fin N) (k : ℕ) :
    {bits : List Bool // (replay edge source target k
      (expected (fun u v => edge u v = true) source k) bits).isSome} ≃
    {w : Transcript (Fin N) // Passes (fun u v => edge u v = true) source k w} :=
  (successfulTraces edge source target k).symm.trans (Scan.successfulBranches edge source target k)

end Cslib.DoubleCounting.Scan.Binary
