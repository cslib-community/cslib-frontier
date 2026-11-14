/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Comparison
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Conditional
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.StreamFold

/-!
# Named native streaming first-match lookup

This module retains a generic first-match table scan. The required input is a table paired with a
key. A retained marshalling compiler copies it to the stream layout, then a concrete `streamTM`
reads each framed entry once. The callback state keeps the search key and whether a prior entry
matched; only the first matching value is emitted.

The peak callback workspace and encoded state/entry size are explicit finite suprema over the
actual rounds. Thus lookup time includes input marshalling and every scanned table occurrence;
there is no semantic list search or uncharged fixed-table callback.

## Main definitions

* `Turing.MultiTapeTM.Internal.NativeCompiler.firstMatch`: first matching value in table order.
* `Turing.MultiTapeTM.Internal.NativeCompiler.firstMatchNextCompiler`,
  `.firstMatchEmitCompiler`: retained scan callbacks.
* `Turing.MultiTapeTM.Internal.NativeCompiler.firstMatchCompiler`: retained marshalling and
  streaming lookup machine.
-/

public section

namespace Turing.MultiTapeTM.Internal.NativeCompiler

universe u

variable {Key Value : Type u} [DecidableEq Key]

/-- First value whose stored key equals the search key. -/
@[expose] def firstMatch (input : List (Key × Value) × Key) : Option Value :=
  (input.1.find? fun entry => entry.1 = input.2).map Prod.snd

/-- Streaming state: the fixed search key and whether a prior entry matched. -/
abbrev FirstMatchState := Key × Bool

/-- Advance the first-match state after one table entry. -/
@[expose] def firstMatchNext (input : FirstMatchState × (Key × Value)) : FirstMatchState :=
  (input.1.1, input.1.2 || decide (input.2.1 = input.1.1))

/-- Emit a value exactly when this is the first matching entry. -/
@[expose] def firstMatchEmit (input : FirstMatchState × (Key × Value)) : Option Value :=
  if input.1.2 then none else if input.2.1 = input.1.1 then some input.2.2 else none

/-- A completed table scan emits the first match, unless a prior prefix had already matched. -/
theorem streamEmit_firstMatch (encValue : Value ↪ List Bool) (query : Key) :
    ∀ (found : Bool) (table : List (Key × Value)),
      streamEmit firstMatchNext (fun input => encOption encValue (firstMatchEmit input))
        (query, found) table =
      if found then [] else encOption encValue (firstMatch (table, query))
  | _, [] => by simp [firstMatch, firstMatchEmit]
  | found, entry :: table => by
      by_cases hfound : found
      · simp [hfound, firstMatchEmit, firstMatchNext,
          streamEmit_firstMatch encValue query true table]
      · by_cases heq : entry.1 = query
        · simp [hfound, heq, firstMatchEmit, firstMatchNext,
            streamEmit_firstMatch encValue query true table, firstMatch]
        · simp [hfound, heq, firstMatchEmit, firstMatchNext,
            streamEmit_firstMatch encValue query false table, firstMatch]

/-- Retained next-state callback for first-match scanning. -/
@[expose] noncomputable def firstMatchNextCompiler (encKey : Key ↪ List Bool)
    (encValue : Value ↪ List Bool) :
    NativeCompiler firstMatchNext
      (encPair (encPair encKey encBool) (encPair encKey encValue))
      (encPair encKey encBool) := by
  let encState := encPair encKey encBool
  let encEntry := encPair encKey encValue
  let state := first encState encEntry
  let entry := second encState encEntry
  let query := (first encKey encBool).comp state
  let found := (second encKey encBool).comp state
  let entryKey := (first encKey encValue).comp entry
  let keys := entryKey.pair query
  let equal := (wordEqBool encKey).comp keys
  let foundTest := boolToTest.comp found
  let keepTrue := const (encPair encState encEntry) encBool true
  let foundOrEqual := ite foundTest keepTrue equal
  exact query.pair foundOrEqual

/-- Retained emission callback for first-match scanning. -/
@[expose] noncomputable def firstMatchEmitCompiler (encKey : Key ↪ List Bool)
    (encValue : Value ↪ List Bool) :
    NativeCompiler firstMatchEmit
      (encPair (encPair encKey encBool) (encPair encKey encValue))
      (encOption encValue) := by
  let encState := encPair encKey encBool
  let encEntry := encPair encKey encValue
  let state := first encState encEntry
  let entry := second encState encEntry
  let query := (first encKey encBool).comp state
  let found := (second encKey encBool).comp state
  let entryKey := (first encKey encValue).comp entry
  let value := (second encKey encValue).comp entry
  let keys := entryKey.pair query
  let equalTest := (wordEqTest encKey).comp keys
  let foundTest := boolToTest.comp found
  let emitValue := (optionSome encValue).comp value
  let emitNone := const (encPair encState encEntry) (encOption encValue) none
  exact ite foundTest emitNone (ite equalTest emitValue emitNone)

/-- Finalization emits no additional match. -/
@[expose] noncomputable def firstMatchFinishCompiler (encKey : Key ↪ List Bool)
    (encValue : Value ↪ List Bool) :
    NativeCompiler (Function.const FirstMatchState (none : Option Value))
      (encPair encKey encBool) (encOption encValue) :=
  const (encPair encKey encBool) (encOption encValue) none

/-- Explicit peak lifted-callback workspace over the actual scan rounds. -/
@[expose] noncomputable def firstMatchSMax (encKey : Key ↪ List Bool)
    (encValue : Value ↪ List Bool) (input : FirstMatchState × List (Key × Value)) : ℕ :=
  let nextCompiler := firstMatchNextCompiler encKey encValue
  let emitCompiler := firstMatchEmitCompiler encKey encValue
  let finishCompiler := firstMatchFinishCompiler encKey encValue
  let K := streamFoldPairTapeCount nextCompiler emitCompiler finishCompiler
  (Finset.range input.2.length).sup fun j =>
    if hj : j < input.2.length then
      let pair := (streamState input.1 firstMatchNext input.2 j, input.2[j])
      inputFromWordWorkspace K emitCompiler pair +
        onWordsWorkspace K (streamFramedNext nextCompiler) pair
    else 0

/-- Explicit peak encoded state/entry length over the actual scan rounds. -/
@[expose] def firstMatchLMax (encKey : Key ↪ List Bool) (encValue : Value ↪ List Bool)
    (input : FirstMatchState × List (Key × Value)) : ℕ :=
  max
    ((Finset.range (input.2.length + 1)).sup fun j =>
      if hj : j ≤ input.2.length then
        ((encPair encKey encBool) (streamState input.1 firstMatchNext input.2 j)).length
      else 0)
    ((Finset.range input.2.length).sup fun j =>
      if hj : j < input.2.length then
        ((encPair encKey encValue) input.2[j]).length
      else 0)

/-- The retained stream before input marshalling. -/
@[expose] noncomputable def firstMatchStreamCompiler (encKey : Key ↪ List Bool)
    (encValue : Value ↪ List Bool) :
    NativeCompiler
      (fun input : FirstMatchState × List (Key × Value) =>
        if input.1.2 then none else firstMatch (input.2, input.1.1))
      (encPair (encPair encKey encBool) (encList (encPair encKey encValue)))
      (encOption encValue) := by
  let nextCompiler := firstMatchNextCompiler encKey encValue
  let emitCompiler := firstMatchEmitCompiler encKey encValue
  let finishCompiler := firstMatchFinishCompiler encKey encValue
  apply streamFoldPair nextCompiler emitCompiler finishCompiler
    (sMax := firstMatchSMax encKey encValue) (lMax := firstMatchLMax encKey encValue)
  · intro input
    rw [streamEmit_firstMatch encValue input.1.1 input.1.2 input.2]
    simp [firstMatchFinishCompiler]
  · intro input j hj
    have hsup := Finset.le_sup
      (s := Finset.range input.2.length)
      (f := fun j => if hj : j < input.2.length then
        let pair := (streamState input.1 firstMatchNext input.2 j, input.2[j])
        inputFromWordWorkspace
            (streamFoldPairTapeCount nextCompiler emitCompiler finishCompiler)
            emitCompiler pair +
          onWordsWorkspace
            (streamFoldPairTapeCount nextCompiler emitCompiler finishCompiler)
            (streamFramedNext nextCompiler) pair
        else 0)
      (Finset.mem_range.mpr hj)
    simpa only [firstMatchSMax, nextCompiler, emitCompiler, finishCompiler, hj, dite_true]
      using hsup
  · intro input j hj
    have hsup := Finset.le_sup
      (s := Finset.range (input.2.length + 1))
      (f := fun j => if hj : j ≤ input.2.length then
        ((encPair encKey encBool) (streamState input.1 firstMatchNext input.2 j)).length
        else 0)
      (Finset.mem_range.mpr (by omega : j < input.2.length + 1))
    exact (by simpa only [hj, dite_true] using hsup).trans
      (Nat.le_max_left _ _)
  · intro input j hj
    have hsup := Finset.le_sup
      (s := Finset.range input.2.length)
      (f := fun j => if hj : j < input.2.length then
        ((encPair encKey encValue) input.2[j]).length else 0)
      (Finset.mem_range.mpr hj)
    exact (by simpa only [hj, dite_true] using hsup).trans
      (Nat.le_max_right _ _)

/-- Retained marshalling from `(table, key)` to the stream's `((key, false), table)` layout. -/
@[expose] noncomputable def firstMatchMarshalCompiler (encKey : Key ↪ List Bool)
    (encValue : Value ↪ List Bool) :
    NativeCompiler
      (fun input : List (Key × Value) × Key => ((input.2, false), input.1))
      (encPair (encList (encPair encKey encValue)) encKey)
      (encPair (encPair encKey encBool) (encList (encPair encKey encValue))) := by
  let encEntry := encPair encKey encValue
  let encInput := encPair (encList encEntry) encKey
  let table := first (encList encEntry) encKey
  let key := second (encList encEntry) encKey
  let isNew := const encInput encBool false
  exact (key.pair isNew).pair table

/-- Retained first-match lookup, including the charged table/key marshalling pass. -/
@[expose] noncomputable def firstMatchCompiler (encKey : Key ↪ List Bool)
    (encValue : Value ↪ List Bool) :
    NativeCompiler firstMatch
      (encPair (encList (encPair encKey encValue)) encKey) (encOption encValue) :=
  ((firstMatchStreamCompiler encKey encValue).comp
    (firstMatchMarshalCompiler encKey encValue)).ofOutputEq fun input => by
      simp [firstMatch]

/-- First-match retains the direct composition of streaming scan after input marshalling. -/
theorem machine_firstMatchCompiler (encKey : Key ↪ List Bool) (encValue : Value ↪ List Bool) :
    (firstMatchCompiler encKey encValue).machine =
      (firstMatchStreamCompiler encKey encValue).machine.comp
        (firstMatchMarshalCompiler encKey encValue).machine true :=
  rfl

/-- The first-match clock exposes marshalling, streaming, intermediate copying and composition
overhead separately. -/
theorem time_firstMatchCompiler (encKey : Key ↪ List Bool) (encValue : Value ↪ List Bool)
    (input : List (Key × Value) × Key) :
    (firstMatchCompiler encKey encValue).time input =
      (firstMatchMarshalCompiler encKey encValue).time input +
        (firstMatchStreamCompiler encKey encValue).time ((input.2, false), input.1) +
        4 * ((encPair (encPair encKey encBool) (encList (encPair encKey encValue)))
          ((input.2, false), input.1)).length + 9 :=
  rfl

/-- The streaming scan clock includes every encoded table occurrence, independently of whether
an earlier entry matched. -/
theorem tableBits_le_time_firstMatchStreamCompiler (encKey : Key ↪ List Bool)
    (encValue : Value ↪ List Bool) (input : FirstMatchState × List (Key × Value)) :
    (encList (encPair encKey encValue) input.2).length ≤
      (firstMatchStreamCompiler encKey encValue).time input := by
  rw [time_streamFoldPair]
  simp only [streamFoldPairTime]
  omega

/-- Consequently, the complete lookup clock includes every encoded table occurrence as well as
the charged marshalling pass. -/
theorem tableBits_le_time_firstMatchCompiler (encKey : Key ↪ List Bool)
    (encValue : Value ↪ List Bool) (input : List (Key × Value) × Key) :
    (encList (encPair encKey encValue) input.1).length ≤
      (firstMatchCompiler encKey encValue).time input := by
  rw [time_firstMatchCompiler]
  have h := tableBits_le_time_firstMatchStreamCompiler encKey encValue
    ((input.2, false), input.1)
  omega

end Turing.MultiTapeTM.Internal.NativeCompiler
