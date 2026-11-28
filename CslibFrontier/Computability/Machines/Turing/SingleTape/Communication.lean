/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.SingleTape.CrossingSequence
public import Mathlib.Data.Nat.Log

/-!
# Crossing sequences on a communication rectangle

For inputs `leftWord x ++ middle ++ rightWord y`, equal crossing sequences at a boundary
of the common middle block preserve a common Boolean verdict under splicing. This applies
to rejection even when the two runs halt over different nonaccepting symbols.

The sum of the crossing lengths over any finite family of runs is bounded by the sum of
their running times. Together these facts let communication lower bounds use native
single-tape runs without repeating the cut-and-paste or double-counting arguments.

## Main results

* `Cslib.Turing.SingleTapeTM.crossings_splice_verdict`: equal crossing sequences and equal
  verdicts preserve the verdict of a mixed input pair.
* `Cslib.Turing.SingleTapeTM.AbsCfg.card_mul_le_sum_time`: a common lower bound on the total
  crossing length at each boundary gives a lower bound on the total running time.
-/

public section

open Cslib Cslib.Turing

namespace Cslib.Turing.SingleTapeTM

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol] {tm : SingleTapeTM Symbol}
  {α : Type*} {ι : α → Symbol} {A : Language α} {yes : Symbol} {T : ℕ → ℕ}

/-- Splicing two runs with the same crossing sequence and Boolean verdict preserves that
verdict, including when their final scanned symbols differ. -/
private theorem splice_verdict (hdec : tm.DecidesByHeadInTime ι A yes T)
    {u₁ v₁ u₂ v₂ : List α} (hu : u₁ = [] ↔ u₂ = []) {z : Bool}
    (h₁ : u₁ ++ v₁ ∈ A ↔ z = true) (h₂ : u₂ ++ v₂ ∈ A ↔ z = true)
    (hc : (tm.absInit ((u₁ ++ v₁).map ι)).crossings u₁.length (T (u₁ ++ v₁).length) =
      (tm.absInit ((u₂ ++ v₂).map ι)).crossings u₂.length (T (u₂ ++ v₂).length)) :
    u₁ ++ v₂ ∈ A ↔ z = true := by
  obtain ⟨hL, hLy⟩ := hdec.absRun (u₁ ++ v₁)
  obtain ⟨hR, hRy⟩ := hdec.absRun (u₂ ++ v₂)
  obtain ⟨hM, hMy⟩ := hdec.absRun (u₁ ++ v₂)
  simp only [List.map_append] at hL hLy hR hRy hM hMy hc
  have hu' : u₁.map ι = [] ↔ u₂.map ι = [] := by
    simpa only [List.map_eq_nil_iff] using hu
  have hc' : (tm.absInit (u₁.map ι ++ v₁.map ι)).crossings (u₁.map ι).length
      (T (u₁ ++ v₁).length) =
      (tm.absInit (u₂.map ι ++ v₂.map ι)).crossings (u₂.map ι).length
        (T (u₂ ++ v₂).length) := by
    simpa only [List.length_map] using hc
  obtain ⟨hC, -, -, hhead⟩ := cut_and_paste_run hu' hL hR hc'
  rw [AbsCfg.run_eq_of_halted _ hC hM] at hhead
  rw [← hMy]
  rcases hhead with h | h
  · rw [h]
    exact hLy.trans h₁
  · rw [h]
    exact hRy.trans h₂

/-- At any boundary of a common middle word, inputs with equal prefix lengths, equal crossing
sequences and equal Boolean verdicts give the same verdict on the mixed pair. No bound on
the lengths of the suffixes is needed. -/
theorem crossings_splice_verdict {X Y : Type*} {f : X → Y → Bool}
    (hdec : tm.DecidesByHeadInTime ι A yes T)
    (leftWord : X → List α) (middle : List α) (rightWord : Y → List α)
    (hA : ∀ x y, leftWord x ++ middle ++ rightWord y ∈ A ↔ f x y = true)
    {x₁ x₂ : X} {y₁ y₂ : Y} {m i : ℕ} (hi : i ≤ middle.length)
    (h₁ : (leftWord x₁).length = m) (h₂ : (leftWord x₂).length = m)
    (hz : f x₁ y₁ = f x₂ y₂)
    (hc : (tm.absInit ((leftWord x₁ ++ middle ++ rightWord y₁).map ι)).crossings
        ((m + i : ℕ) : ℤ) (T (leftWord x₁ ++ middle ++ rightWord y₁).length) =
      (tm.absInit ((leftWord x₂ ++ middle ++ rightWord y₂).map ι)).crossings
        ((m + i : ℕ) : ℤ) (T (leftWord x₂ ++ middle ++ rightWord y₂).length)) :
    f x₁ y₂ = f x₁ y₁ := by
  have hsplit (x : X) (y : Y) :
      (leftWord x ++ middle.take i) ++ (middle.drop i ++ rightWord y) =
        leftWord x ++ middle ++ rightWord y := by
    simp only [List.append_assoc]
    rw [← List.append_assoc (middle.take i), List.take_append_drop]
  have hlen₁ : (leftWord x₁ ++ middle.take i).length = m + i := by
    simp [h₁, List.length_take, Nat.min_eq_left hi]
  have hlen₂ : (leftWord x₂ ++ middle.take i).length = m + i := by
    simp [h₂, List.length_take, Nat.min_eq_left hi]
  have hu : leftWord x₁ ++ middle.take i = [] ↔ leftWord x₂ ++ middle.take i = [] := by
    rw [← List.length_eq_zero_iff, ← List.length_eq_zero_iff, hlen₁, hlen₂]
  have hcolor₁ :
      (leftWord x₁ ++ middle.take i) ++ (middle.drop i ++ rightWord y₁) ∈ A ↔
        f x₁ y₁ = true := by rw [hsplit, hA]
  have hcolor₂ :
      (leftWord x₂ ++ middle.take i) ++ (middle.drop i ++ rightWord y₂) ∈ A ↔
        f x₁ y₁ = true := by rw [hsplit, hA, hz]
  have hc' : (tm.absInit (((leftWord x₁ ++ middle.take i) ++
        (middle.drop i ++ rightWord y₁)).map ι)).crossings
        (leftWord x₁ ++ middle.take i).length
        (T ((leftWord x₁ ++ middle.take i) ++ (middle.drop i ++ rightWord y₁)).length) =
      (tm.absInit (((leftWord x₂ ++ middle.take i) ++
        (middle.drop i ++ rightWord y₂)).map ι)).crossings
        (leftWord x₂ ++ middle.take i).length
        (T ((leftWord x₂ ++ middle.take i) ++ (middle.drop i ++ rightWord y₂)).length) := by
    simpa only [hsplit, hlen₁, hlen₂] using hc
  have h := splice_verdict hdec hu hcolor₁ hcolor₂ hc'
  rw [hsplit, hA] at h
  exact Bool.eq_iff_iff.mpr h

/-- If each selected boundary has total crossing length at least `b` across a finite family
of runs, their total running time is at least the number of boundaries times `b`. The runs
may have different lengths, need not halt and may start in arbitrary configurations. -/
theorem AbsCfg.card_mul_le_sum_time {κ : Type*} (cfg : κ → tm.AbsCfg) (time : κ → ℕ)
    (S : Finset κ) (K : Finset ℤ) {b : ℕ}
    (h : ∀ k ∈ K, b ≤ ∑ p ∈ S, ((cfg p).crossings k (time p)).length) :
    K.card * b ≤ ∑ p ∈ S, time p := by
  calc K.card * b = ∑ _k ∈ K, b := by simp
    _ ≤ ∑ k ∈ K, ∑ p ∈ S, ((cfg p).crossings k (time p)).length :=
      Finset.sum_le_sum h
    _ = ∑ p ∈ S, ∑ k ∈ K, ((cfg p).crossings k (time p)).length := Finset.sum_comm
    _ ≤ ∑ p ∈ S, time p := Finset.sum_le_sum fun p _ =>
      (cfg p).sum_length_crossings_le K (time p)

/-- Choosing a crossing-length threshold from `bits` after reserving `r` bits bounds the
short-sequence count factor by `2 ^ bits` while losing at most a factor of two from rounding. -/
theorem exists_crossing_length_of_bits (tm : SingleTapeTM Symbol) {r bits : ℕ} (hr : 1 ≤ r)
    (hbits : 2 * Nat.clog 2 (Fintype.card tm.State + 2) + 2 * (r - 1) ≤ bits) :
    ∃ L, 2 ^ r * (Fintype.card (Option tm.State) + 1) ^ L ≤ 2 ^ bits ∧
      bits ≤ 2 * (Nat.clog 2 (Fintype.card tm.State + 2) * L) := by
  let d := Nat.clog 2 (Fintype.card tm.State + 2)
  let L := (bits - r) / d
  have hd : 0 < d := Nat.clog_pos one_lt_two (by omega)
  have hpow : Fintype.card (Option tm.State) + 1 ≤ 2 ^ d := by
    rw [Fintype.card_option]
    exact Nat.le_pow_clog one_lt_two _
  have hdiv : d * L + (bits - r) % d = bits - r := Nat.div_add_mod (bits - r) d
  have hmod := Nat.mod_lt (bits - r) hd
  have hbits' : 2 * d + 2 * (r - 1) ≤ bits := hbits
  have hbitsL : bits ≤ 2 * (d * L) := by omega
  refine ⟨L, ?_, hbitsL⟩
  calc 2 ^ r * (Fintype.card (Option tm.State) + 1) ^ L
      ≤ 2 ^ r * (2 ^ d) ^ L := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpow L)
    _ = 2 ^ (r + d * L) := by rw [← pow_mul, ← pow_add]
    _ ≤ 2 ^ bits := Nat.pow_le_pow_right (Nat.succ_pos 1) (by omega)

end Cslib.Turing.SingleTapeTM
