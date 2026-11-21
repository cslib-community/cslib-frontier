/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.GammaToken
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.RunsBetween
public import CslibFrontier.Foundations.Combinatorics.SparseModeTuple
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Streaming consecutive gamma tokens

A fixed finite controller checks the current source cell, runs a gamma-token scan and repeats.
Its clock on any concatenation is at most three times the compressed length plus one, including
all tests. Applied to the sparse tuple encoding it crosses every occupied row and entry.
-/

public section

namespace Turing.MultiTapeTM.GammaStream

open Cslib.BitString Cslib.SparseModeTuple Finset

/-- Loop over the source tape until the cursor reaches the final blank. -/
noncomputable def machine (keep : Bool) : MultiTapeTM 2 Bool (Bool ⊕ Unit) :=
  whileCond (fun _ work => (work 0).isSome) (GammaToken.machine keep)

/-- The bits emitted for one successful token. Skipping emits only the success marker. -/
@[expose] def tokenOutput (keep : Bool) (n : ℕ) : List Bool :=
  (if keep then lowBits (Nat.log 2 n) n else []) ++ [true]

/-- Persistent heads and output between tokens. -/
@[expose] def storage {input : List Bool} (ip : Fin (input.length + 2))
    (out word : List Bool) (p : ℕ) : Cfg 2 Bool Unit input :=
  (GammaToken.config ip out word p 0 none).withState none

/-- Sum of the individual token lengths along the physical scan. -/
theorem sum_lengths (values : List ℕ) :
    ∑ i ∈ range values.length, (eliasGamma (values.getD i 0)).length =
      (values.flatMap eliasGamma).length := by
  induction values with
  | nil => simp
  | cons v vs ih =>
    rw [List.length_cons, sum_range_succ', List.flatMap_cons, List.length_append, add_comm]
    simp only [List.getD_cons_succ, List.getD_cons_zero, ih]

/-- Every gamma token occupies at least one source cell. -/
theorem count_le_length (values : List ℕ) :
    values.length ≤ (values.flatMap eliasGamma).length := by
  induction values with
  | nil => simp
  | cons v vs ih =>
    have h := List.length_pos_iff.mpr (eliasGamma_ne_nil v)
    simp only [List.length_cons, List.flatMap_cons, List.length_append]
    omega

/-- The same machine scans every token sequence. The time includes loop dispatch, and the
charged workspace counts the two visited work-head paths. -/
theorem runsBetween (keep : Bool) {input : List Bool} (ip : Fin (input.length + 2))
    (out pre : List Bool) (values : List ℕ) :
    let raw := values.flatMap eliasGamma
    let clock := 3 * raw.length + 1
    RunsBetween (machine keep) (storage ip out (pre ++ raw) pre.length)
      (storage ip (out ++ values.flatMap (tokenOutput keep)) (pre ++ raw) (pre.length + raw.length))
      clock (2 * (clock + 1)) := by
  let raw := values.flatMap eliasGamma
  let word := pre ++ raw
  let sofar := fun i => pre ++ (values.take i).flatMap eliasGamma
  let written := fun i => out ++ (values.take i).flatMap (tokenOutput keep)
  let cfg := fun i => storage ip (written i) word (sofar i).length
  let t := fun i => (eliasGamma (values.getD i 0)).length + 1
  let s := fun i => 2 * (t i + 1)
  have hround (i : ℕ) (hi : i < values.length) :
      ((cfg i).workTapeSymbols 0).isSome = true ∧
        RunsBetween (GammaToken.machine keep) (cfg i) (cfg (i + 1)) (t i) (s i) := by
    let v := values[i]
    let rest := (values.drop (i + 1)).flatMap eliasGamma
    have heq : word = sofar i ++ eliasGamma v ++ rest := by
      have hl := List.take_append_drop i values
      rw [List.drop_eq_getElem_cons hi] at hl
      simpa only [word, raw, sofar, v, rest, List.flatMap_append, List.flatMap_cons,
        List.append_assoc] using
        (congrArg (fun w => pre ++ w.flatMap eliasGamma) hl).symm
    have hpre : sofar (i + 1) = sofar i ++ eliasGamma v := by
      simp only [sofar, v, List.take_succ_eq_append_getElem hi, List.flatMap_append,
        List.flatMap_singleton, List.append_assoc]
    have hout : written (i + 1) = written i ++ tokenOutput keep v := by
      simp only [written, v, List.take_succ_eq_append_getElem hi, List.flatMap_append,
        List.flatMap_singleton, List.append_assoc]
    have hv : values.getD i 0 = v := by simp [v, hi]
    constructor
    · have hlen : (sofar i).length < word.length := by
        have := List.length_pos_iff.mpr (eliasGamma_ne_nil v)
        rw [heq]
        simp only [List.length_append]
        omega
      simp [cfg, storage, GammaToken.config, Cfg.workTapeSymbols, Cfg.withState, hlen]
    · apply RunsBetween.of_runFrom
      have h := GammaToken.runFrom_word keep ip (written i) (sofar i) rest v
      change (GammaToken.machine keep).runFrom
        (GammaToken.config ip (written i) word (sofar i).length 0
          (some (GammaToken.machine keep).q₀))
        (t i) = GammaToken.config ip (written (i + 1)) word (sofar (i + 1)).length 0 none
      simpa only [t, hv, hpre, List.length_append, hout, tokenOutput, List.append_assoc,
        ← heq] using h
  have hstop : ((cfg values.length).workTapeSymbols 0).isSome = false := by
    have hlast : sofar values.length = word := by simp only [sofar, word, raw, List.take_length]
    change (tapeOfList word ((sofar values.length).length : ℕ)).isSome = false
    rw [hlast]
    simp
  have hall := runsBetween_whileCond (c := fun _ work => (work 0).isSome)
    (tm := GammaToken.machine keep) cfg values.length t s hround hstop
  have ht : ∑ i ∈ range values.length, (t i + 1) + 1 ≤ 3 * raw.length + 1 := by
    have hlen := count_le_length values
    have heq := sum_lengths values
    simp only [t, sum_add_distrib, sum_const, card_range, nsmul_eq_mul, Nat.cast_id, mul_one]
    dsimp only [raw]
    omega
  have hfull := RunsBetween.of_runFrom ((hall.mono ht le_rfl).1)
  simpa only [machine, cfg, written, sofar, raw, word, List.take_zero, List.flatMap_nil,
    List.append_nil, List.take_length, List.length_append, List.length_nil, Nat.add_zero]
    using hfull

/-- Positive gamma fields of one entry, in their physical order. -/
@[expose] def entryFields (e : Entry) : List ℕ := [e.skip + 1, e.extra + 1]

/-- The colour gap and occupied weight count, followed by the nonzero entries. -/
@[expose] def rowFields (r : Row) : List ℕ :=
  (r.skip + 1) :: (r.rest.length + 1) :: (r.first :: r.rest).flatMap entryFields

/-- Numerical token stream of the canonical sparse table. -/
@[expose] def fields (rows : List Row) : List ℕ := (rows.length + 1) :: rows.flatMap rowFields

/-- The tuple encoding consists exactly of this stream of tokens. -/
theorem flatMap_fields (rows : List Row) : (fields rows).flatMap eliasGamma = encode rows := by
  have he : (fun e => (entryFields e).flatMap eliasGamma) = encodeEntry := by
    funext e
    simp [entryFields, encodeEntry]
  have hr : (fun r => (rowFields r).flatMap eliasGamma) = encodeRow := by
    funext r
    simp only [rowFields, encodeRow, List.flatMap_cons, List.flatMap_append, List.flatMap_assoc,
      List.append_assoc, he, congrFun he r.first]
  simp only [fields, encode, List.flatMap_cons, List.flatMap_assoc, hr]

/-- A complete scan of a canonical sparse table skips every token on a linear native clock. -/
theorem runsBetween_sparse {input : List Bool} (ip : Fin (input.length + 2))
    (out pre : List Bool) (rows : List Row) :
    let raw := encode rows
    let clock := 3 * raw.length + 1
    RunsBetween (machine false) (storage ip out (pre ++ raw) pre.length)
      (storage ip (out ++ List.replicate (fields rows).length true) (pre ++ raw)
        (pre.length + raw.length)) clock (2 * (clock + 1)) := by
  have h := runsBetween false ip out pre (fields rows)
  have ho (xs : List ℕ) : xs.flatMap (tokenOutput false) = List.replicate xs.length true := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [tokenOutput, ih, List.replicate_succ]
  simpa only [flatMap_fields, ho] using h

end Turing.MultiTapeTM.GammaStream
