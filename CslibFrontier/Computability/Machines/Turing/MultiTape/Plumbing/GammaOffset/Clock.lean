/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.GammaOffset

/-!
# A linear clock on arbitrary source words and field ordinals

Across all skipped and selected fields, the source head only moves forward. Charging the
actual number of cells consumed on each round gives a linear clock even for a truncated
gamma stream or an ordinal past the last field.
-/

public section

namespace Turing.MultiTapeTM.GammaOffset

open Finset

private structure Cursor where
  pos : ℕ
  marker : ℕ
  output : List Bool

private structure Scanned (keep : Bool) {input : List Bool} (ip : Fin (input.length + 2))
    (word : List Bool) (c : Cursor) where
  n : ℕ
  marker : ℕ
  output : List Bool
  le_remaining : n ≤ word.length - c.pos
  run : (GammaToken.machine keep).runFrom (GammaToken.config ip c.output word c.pos c.marker
    (some (GammaToken.machine keep).q₀)) (n + 1) =
    GammaToken.config ip output word (c.pos + n : ℕ) marker none

private noncomputable def scanData (keep : Bool) {input : List Bool} (ip : Fin (input.length + 2))
    (word : List Bool) (c : Cursor) : Scanned keep ip word c := Classical.choice (by
  obtain ⟨n, out, d, hn, h⟩ := GammaToken.exists_run keep (GammaToken.machine keep).q₀ ip
    c.output word c.pos c.marker
  exact ⟨⟨n, d, out, hn, h⟩⟩)

private def Scanned.cursor {keep : Bool} {input : List Bool} {ip : Fin (input.length + 2)}
    {word : List Bool} {c : Cursor} (s : Scanned keep ip word c) : Cursor :=
  ⟨c.pos + s.n, s.marker, s.output⟩

private theorem tally_symbol {input : List Bool} (ip : Fin (input.length + 2))
    (out word : List Bool) (p d : ℕ) (tally : List Bool) (j : ℕ) :
    (storageAt ip out word p d tally j).workTapeSymbols (Fin.last 2) = tapeOfList tally j := by
  simp only [Cfg.workTapeSymbols, storageAt, Fin.lastCases_last]

/-- The actual selector always halts, from any tape words and initial scanner heads. The
entire source traversal is charged once, with three further transitions per tally cell. -/
theorem exists_runsBetween_le {input : List Bool} (ip : Fin (input.length + 2))
    (out word : List Bool) (p d : ℕ) (tally : List Bool) :
    let time := word.length - p + 3 * tally.length + 2
    ∃ (q marker : ℕ) (result : List Bool), p ≤ q ∧ q - p ≤ word.length - p ∧
      RunsBetween machine (storageAt ip out word p d tally 0)
        (storageAt ip result word q marker tally tally.length) time (3 * (time + 1)) := by
  let init : Cursor := ⟨p, d, out⟩
  let next (c : Cursor) := (scanData false ip word c).cursor
  let states (i : ℕ) := (next^[i]) init
  let data (i : ℕ) := scanData false ip word (states i)
  let n (i : ℕ) := (data i).n
  let cfg (i : ℕ) := storageAt ip (states i).output word (states i).pos (states i).marker tally i
  let t (i : ℕ) := n i + 2
  let s (i : ℕ) := 3 * (t i + 1)
  have hnext (i : ℕ) : states (i + 1) = (data i).cursor := by
    simp only [states, Function.iterate_succ_apply', next, data]
  have hpos (i : ℕ) : (states (i + 1)).pos = (states i).pos + n i := by rw [hnext]; rfl
  have hround (i : ℕ) (hi : i < tally.length) :
      ((cfg i).workTapeSymbols (Fin.last 2)).isSome = true ∧
        RunsBetween ((scan false).seq advance) (cfg i) (cfg (i + 1)) (t i) (s i) := by
    constructor
    · simp only [cfg, tally_symbol, tapeOfList_ofNat]
      simp [hi]
    · have hs := runsBetween_scan_of false ip _ _ _ tally _ _ _ _ i _ (data i).run
      have hr := hs.seq (runsBetween_advance ip (data i).output word ((states i).pos + n i)
        (data i).marker tally i)
      apply RunsBetween.of_runFrom
      simpa only [cfg, hnext, Scanned.cursor, t, n, Nat.add_assoc] using hr.1
  have hstop : ((cfg tally.length).workTapeSymbols (Fin.last 2)).isSome = false := by
    simp only [cfg, tally_symbol, tapeOfList_ofNat]
    simp
  have loop := runsBetween_whileCond (c := fun _ work => (work (Fin.last 2)).isSome)
    (tm := (scan false).seq advance) cfg tally.length t s hround hstop
  let final := scanData true ip word (states tally.length)
  have hf := runsBetween_scan_of true ip _ _ _ tally _ _ _ _ tally.length _ final.run
  have run := loop.seq hf
  have hprefix (i : ℕ) : p + ∑ k ∈ range i, n k = (states i).pos := by
    induction i with
    | zero => simp [states, init]
    | succ i ih => rw [sum_range_succ, hpos, ← ih, Nat.add_assoc]
  have hremaining (i : ℕ) : (∑ k ∈ range i, n k) + (word.length - (states i).pos) =
      word.length - p := by
    induction i with
    | zero => simp [states, init]
    | succ i ih =>
      have hn := (data i).le_remaining
      change n i ≤ _ at hn
      rw [sum_range_succ, hpos]
      omega
  have ht : (∑ i ∈ range tally.length, (t i + 1)) + 1 + (final.n + 1) ≤
      word.length - p + 3 * tally.length + 2 := by
    have hr := hremaining tally.length
    have hn := final.le_remaining
    simp only [t, sum_add_distrib, sum_const, card_range, nsmul_eq_mul, Nat.cast_id, mul_one]
    omega
  have hq := hprefix tally.length
  have hr := hremaining tally.length
  have hn := final.le_remaining
  refine ⟨(states tally.length).pos + final.n, final.marker, final.output, by omega, by omega, ?_⟩
  have bound := RunsBetween.of_runFrom ((run.mono ht le_rfl).1)
  simpa only [machine, cfg, states, Function.iterate_zero_apply, init] using bound

end Turing.MultiTapeTM.GammaOffset
