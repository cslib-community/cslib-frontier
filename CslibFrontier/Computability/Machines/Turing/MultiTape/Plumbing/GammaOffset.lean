/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.GammaStream
import Mathlib.Tactic.FinCases

/-!
# Selecting one gamma token by its ordinal

The third work tape holds one cell for each token to skip. The other heads scan complete tokens
and retain the payload of the requested token. The host input and all three work tapes are
read-only. Suffix cells after the selected token, including zero padding, cost no transitions.
-/

public section

namespace Turing.MultiTapeTM.GammaOffset

open Cslib.BitString Finset

/-- Extend a scanner configuration, including a possibly displaced marker, by its tally tape. -/
@[expose] def storageAt {input : List Bool} (ip : Fin (input.length + 2))
    (out word : List Bool) (p d : ℕ) (tally : List Bool) (j : ℕ) : Cfg 3 Bool Unit input :=
  let c := GammaToken.config ip out word p d none
  ⟨none, ip, Fin.lastCases (tapeOfList tally) c.workTapes,
    Fin.lastCases (j : ℤ) c.workTapePos, out⟩

/-- The configuration at the beginning or end of a canonical token. -/
@[expose] def storage {input : List Bool} (ip : Fin (input.length + 2)) (out word : List Bool)
    (p : ℕ) (tally : List Bool) (j : ℕ) : Cfg 3 Bool Unit input :=
  storageAt ip out word p 0 tally j

/-- One gamma-token scanner acting on the first two tapes. -/
@[expose] noncomputable def scan (keep : Bool) : MultiTapeTM 3 Bool Bool :=
  (GammaToken.machine keep).extendTapes Fin.castSuccEmb

/-- Advance the tally head once, preserving all tape contents. -/
@[expose] def advance : MultiTapeTM 3 Bool Unit :=
  .ofTr () fun _ _ _ => ⟨0, fun i => (none, if i = Fin.last 2 then 1 else 0), none, none⟩

/-- Skip one complete token per occupied tally cell and then read one payload. -/
@[expose] noncomputable def machine :=
  (whileCond (fun _ work => (work (Fin.last 2)).isSome) ((scan false).seq advance)).seq (scan true)

private theorem last_two {α : Type*} (x : α) (f : Fin 2 → α) :
    Fin.lastCases (motive := fun _ => α) x f (2 : Fin 3) = x :=
  Fin.lastCases_last

private theorem cast_ne_two (i : Fin 2) : i.castSucc ≠ (2 : Fin 3) := Fin.castSucc_ne_last i

/-- Lift any physical token run to the three-tape selector, leaving the tally in place. -/
theorem runsBetween_scan_of (keep : Bool) {input : List Bool} (ip : Fin (input.length + 2))
    (out out' word tally : List Bool) (p d p' d' j t : ℕ)
    (h : (GammaToken.machine keep).runFrom (GammaToken.config ip out word p d
      (some (GammaToken.machine keep).q₀)) t = GammaToken.config ip out' word p' d' none) :
    RunsBetween (scan keep) (storageAt ip out word p d tally j)
      (storageAt ip out' word p' d' tally j) t (3 * (t + 1)) := by
  apply RunsBetween.of_runFrom
  rw [scan, runFrom_extendTapes, extendTapes_q₀, embed_castSucc]
  have hv : viewCfg Fin.castSuccEmb ((storageAt ip out word p d tally j).withState
      (some (GammaToken.machine keep).q₀)) =
      GammaToken.config ip out word p d (some (GammaToken.machine keep).q₀) := by
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> simp [viewCfg, storageAt,
      Cfg.withState, GammaToken.config]
  rw [hv, h]
  apply Cfg.ext <;> simp [storageAt, Cfg.withState, GammaToken.config, last_two]

private theorem runs_scan (keep : Bool) {input : List Bool} (ip : Fin (input.length + 2))
    (out pre suffix tally : List Bool) (j v : ℕ) :
    let token := eliasGamma v
    let word := pre ++ token ++ suffix
    let time := token.length + 1
    RunsBetween (scan keep) (storage ip out word pre.length tally j)
      (storage ip (out ++ GammaStream.tokenOutput keep v) word (pre.length + token.length) tally j)
      time (3 * (time + 1)) := by
  apply runsBetween_scan_of
  simpa only [GammaStream.tokenOutput, List.append_assoc, Nat.cast_zero] using
    GammaToken.runFrom_word keep ip out pre suffix v

/-- The tally advance costs one transition, even after a failed token. -/
theorem runsBetween_advance {input : List Bool} (ip : Fin (input.length + 2))
    (out word : List Bool) (p d : ℕ) (tally : List Bool) (j : ℕ) :
    RunsBetween advance (storageAt ip out word p d tally j)
      (storageAt ip out word p d tally (j + 1)) 1 6 := by
  apply RunsBetween.of_runFrom
  rw [runFrom_one, step_of_state rfl]
  apply Cfg.ext <;> try solve | simp [advance, Action.apply, storageAt, Cfg.withState, funext_iff]
  funext i
  induction i using Fin.lastCases <;>
    simp [advance, Action.apply, storageAt, Cfg.withState, last_two, cast_ne_two]

/-- One fixed controller selects a token from any prefix, leaving the host and suffix untouched.
Its clock charges every cell crossed and includes the test and advance for every skipped token.
Each skipped token emits one success bit before the selected little-endian number. -/
theorem runsBetween {input : List Bool} (ip : Fin (input.length + 2)) (out pre suffix : List Bool)
    (before : List ℕ) (v : ℕ) :
    let skipped := before.flatMap eliasGamma
    let token := eliasGamma v
    let tally := List.replicate before.length true
    let word := (pre ++ skipped) ++ token ++ suffix
    let time := 4 * skipped.length + token.length + 2
    RunsBetween machine (storage ip out word pre.length tally 0)
      (storage ip ((out ++ tally) ++ GammaStream.tokenOutput true v) word
        (pre.length + skipped.length + token.length) tally before.length)
      time (3 * (time + 1)) := by
  let skipped := before.flatMap eliasGamma
  let word := (pre ++ skipped) ++ eliasGamma v ++ suffix
  let tally := List.replicate before.length true
  let scanned := fun i => pre ++ (before.take i).flatMap eliasGamma
  let written := fun i => out ++ List.replicate i true
  let cfg := fun i => storage ip (written i) word (scanned i).length tally i
  let t := fun i => (eliasGamma (before.getD i 0)).length + 2
  let s := fun i => 3 * (t i + 1)
  have hround (i : ℕ) (hi : i < before.length) :
      ((cfg i).workTapeSymbols (Fin.last 2)).isSome = true ∧
        RunsBetween ((scan false).seq advance) (cfg i) (cfg (i + 1)) (t i) (s i) := by
    let a := before[i]
    let rem := (before.drop (i + 1)).flatMap eliasGamma ++ eliasGamma v ++ suffix
    have heq : word = scanned i ++ eliasGamma a ++ rem := by
      have hl := List.take_append_drop i before
      rw [List.drop_eq_getElem_cons hi] at hl
      have hb := congrArg (fun xs => xs.flatMap eliasGamma) hl
      simp only [List.flatMap_append, List.flatMap_cons] at hb
      simp only [word, skipped, scanned, rem, a, ← hb, List.append_assoc]
    have hnext : scanned (i + 1) = scanned i ++ eliasGamma a := by
      simp only [scanned, a, List.take_succ_eq_append_getElem hi, List.flatMap_append,
        List.flatMap_singleton, List.append_assoc]
    have hw : written (i + 1) = written i ++ [true] := by
      simp only [written, List.replicate_succ', List.append_assoc]
    have ha : before.getD i 0 = a := by simp [a, hi]
    constructor
    · simp [cfg, storage, storageAt, Cfg.workTapeSymbols, tally, last_two, hi]
    · have hs := runs_scan false ip (written i) (scanned i) rem tally i a
      dsimp only at hs
      rw [← heq] at hs
      simp only [GammaStream.tokenOutput, Bool.false_eq_true, ↓reduceIte, List.nil_append,
        ← hw, ← List.length_append, ← hnext] at hs
      have hr := hs.seq (runsBetween_advance ip (written (i + 1)) word (scanned (i + 1)).length
        0 tally i)
      apply RunsBetween.of_runFrom
      simpa only [cfg, storage, ha, t, Nat.add_assoc, Nat.reduceAdd] using hr.1
  have hstop : ((cfg before.length).workTapeSymbols (Fin.last 2)).isSome = false := by
    simp [cfg, storage, storageAt, Cfg.workTapeSymbols, tally, last_two]
  have hall := runsBetween_whileCond (c := fun _ work => (work (Fin.last 2)).isSome)
    (tm := (scan false).seq advance) cfg before.length t s hround hstop
  have ht : ∑ i ∈ range before.length, (t i + 1) + 1 ≤ 4 * skipped.length + 1 := by
    have hc := GammaStream.count_le_length before
    have hl := GammaStream.sum_lengths before
    simp only [t, sum_add_distrib, sum_const, card_range, nsmul_eq_mul, Nat.cast_id, mul_one]
    dsimp only [skipped]
    omega
  have hfinal := runs_scan true ip (out ++ tally) (pre ++ skipped) suffix tally before.length v
  have hprefix := hall.mono ht le_rfl
  simp only [cfg, written, scanned, List.take_zero, List.flatMap_nil, List.replicate_zero,
    List.append_nil, List.take_length, List.length_append] at hprefix
  dsimp only at hfinal
  simp only [List.length_append] at hfinal
  have hr := hprefix.seq hfinal
  apply RunsBetween.of_runFrom
  simpa only [machine, word, tally, skipped, List.length_append, Nat.add_assoc, Nat.add_comm 1,
    Nat.add_left_comm 1, List.length_nil, Nat.add_zero, Nat.reduceAdd] using hr.1

end Turing.MultiTapeTM.GammaOffset
