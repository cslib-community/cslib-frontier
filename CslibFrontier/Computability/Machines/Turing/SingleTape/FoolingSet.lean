/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.FoolingSet
public import CslibFrontier.Computability.Machines.Turing.SingleTape.CrossingSequence
public import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Ring

/-!
# Communication fooling sets give single-tape time lower bounds

Suppose the restriction of a language to words `leftWord x ++ middle ++ rightWord y` is the Boolean
function `f x y`. A communication fooling set for either value of `f` forces distinct crossing
sequences at every boundary in the common middle word. If two sequences agreed, cut-and-paste
would give both mixed pairs the same verdict as the original pairs, contradicting the fooling
property. Rejection needs no distinguished rejecting symbol: both possible final scanned symbols
fail to equal the accepting symbol.

For a fooling set of cardinality `q`, fixed prefix length and total input length `n`, this gives

`(middle.length + 1) * (q - (|Q| + 2)^L) * L ≤ q * T n`

for every threshold `L`, where `Q` is the machine's state type. Crossing sequences shorter than
`L` are counted with the existing finite-list bound, and all selected boundaries together cost
at most the actual native run time. If `2 * (|Q| + 2)^L ≤ q`, the bound simplifies to
`(middle.length + 1) * L ≤ 2 * T n`.

This is an original library transfer lemma combining the existing communication fooling-set
notion and single-tape cut-and-paste theorem. The machine is the native deterministic
`Cslib.Turing.SingleTapeTM`, with the answer under its head and an unrestricted final tape.
The prefix may be empty, the common middle word may be empty, and `f` need not be equality.

## Main results

* `Cslib.Turing.SingleTapeTM.crossings_injOn_of_isFoolingSet`: crossing sequences distinguish
  every pair in a fooling set at every boundary in the common middle word.
* `Cslib.Turing.SingleTapeTM.crossing_foolingSet_bound`: the finite-cardinality lower bound.
* `Cslib.Turing.SingleTapeTM.crossing_foolingSet_half_bound`: its half-count specialization.
* `Cslib.Turing.SingleTapeTM.crossing_foolingSet_bit_bound`: an exponential fooling set gives
  a bound in its bit length, with the machine's state dependence logarithmic.
-/

public section

open Cslib Cslib.Turing

namespace Cslib.Turing.SingleTapeTM

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol] {tm : SingleTapeTM Symbol}
  {α : Type*} {ι : α → Symbol} {A : Language α} {yes : Symbol} {T : ℕ → ℕ}

/-- Splicing two runs with the same crossing sequence and Boolean verdict preserves that
verdict, including when neither final scanned symbol is the accepting symbol. -/
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

variable {X Y : Type*} {f : X → Y → Bool} {z : Bool} {S : Finset (X × Y)}
  (hdec : tm.DecidesByHeadInTime ι A yes T) (hS : Communication.IsFoolingSet f z S)
  (leftWord : X → List α) (middle : List α) (rightWord : Y → List α)
  (hA : ∀ x y, leftWord x ++ middle ++ rightWord y ∈ A ↔ f x y = true)
  {m n : ℕ} (hprefix : ∀ p ∈ S, (leftWord p.1).length = m)

include hdec hS hA hprefix

/-- A fooling set for either Boolean value injects into the crossing sequences at any boundary
of the common middle word. Only the prefix lengths must agree; the runs may have different
lengths and time bounds. -/
theorem crossings_injOn_of_isFoolingSet {i : ℕ} (hi : i ≤ middle.length) :
    Set.InjOn (fun p : X × Y =>
      (tm.absInit ((leftWord p.1 ++ middle ++ rightWord p.2).map ι)).crossings
        ((m + i : ℕ) : ℤ) (T (leftWord p.1 ++ middle ++ rightWord p.2).length))
      (S : Set (X × Y)) := by
  have hsplit (x : X) (y : Y) :
      (leftWord x ++ middle.take i) ++ (middle.drop i ++ rightWord y) =
        leftWord x ++ middle ++ rightWord y := by
    simp only [List.append_assoc]
    rw [← List.append_assoc (middle.take i), List.take_append_drop]
  have hlen (p : X × Y) (hp : p ∈ S) : (leftWord p.1 ++ middle.take i).length = m + i := by
    simp [hprefix p hp, List.length_take, Nat.min_eq_left hi]
  have hmix (p q : X × Y) (hp : p ∈ S) (hq : q ∈ S)
      (hc : (tm.absInit ((leftWord p.1 ++ middle ++ rightWord p.2).map ι)).crossings
          ((m + i : ℕ) : ℤ) (T (leftWord p.1 ++ middle ++ rightWord p.2).length) =
        (tm.absInit ((leftWord q.1 ++ middle ++ rightWord q.2).map ι)).crossings
          ((m + i : ℕ) : ℤ) (T (leftWord q.1 ++ middle ++ rightWord q.2).length)) :
      f p.1 q.2 = z := by
    have hu : leftWord p.1 ++ middle.take i = [] ↔ leftWord q.1 ++ middle.take i = [] := by
      rw [← List.length_eq_zero_iff, ← List.length_eq_zero_iff, hlen p hp, hlen q hq]
    have hcolor (a : X × Y) (ha : a ∈ S) :
        (leftWord a.1 ++ middle.take i) ++ (middle.drop i ++ rightWord a.2) ∈ A ↔ z = true := by
      rw [hsplit, hA, hS.1 a ha]
    have hc' : (tm.absInit (((leftWord p.1 ++ middle.take i) ++
          (middle.drop i ++ rightWord p.2)).map ι)).crossings
          (leftWord p.1 ++ middle.take i).length
          (T ((leftWord p.1 ++ middle.take i) ++ (middle.drop i ++ rightWord p.2)).length) =
        (tm.absInit (((leftWord q.1 ++ middle.take i) ++
          (middle.drop i ++ rightWord q.2)).map ι)).crossings
          (leftWord q.1 ++ middle.take i).length
          (T ((leftWord q.1 ++ middle.take i) ++ (middle.drop i ++ rightWord q.2)).length) := by
      simpa only [hsplit, hlen p hp, hlen q hq] using hc
    have h := splice_verdict hdec hu (hcolor p hp) (hcolor q hq) hc'
    rw [hsplit, hA] at h
    exact Bool.eq_iff_iff.mpr h
  intro p hp q hq hc
  exact hS.2 p hp q hq (hmix p q hp hq hc) (hmix q p hq hp hc.symm)

variable (hlength : ∀ p ∈ S, (leftWord p.1 ++ middle ++ rightWord p.2).length = n)

include hlength

/-- Summing over the fooling set and all boundaries in the common middle word gives a native
running-time lower bound. The finite-list counting term also handles an empty fooling set and
threshold zero without separate nonemptiness hypotheses. -/
theorem crossing_foolingSet_bound (L : ℕ) :
    (middle.length + 1) * (S.card - (Fintype.card (Option tm.State) + 1) ^ L) * L ≤
      S.card * T n := by
  classical
  let cs : ℕ → X × Y → List (Option tm.State) := fun i p =>
    (tm.absInit ((leftWord p.1 ++ middle ++ rightWord p.2).map ι)).crossings ((m + i : ℕ) : ℤ) (T n)
  have hinj (i : ℕ) (hi : i ≤ middle.length) : Set.InjOn (cs i) (S : Set (X × Y)) := by
    intro p hp q hq hc
    apply crossings_injOn_of_isFoolingSet hdec hS leftWord middle rightWord hA hprefix hi hp hq
    simpa only [cs, hlength p hp, hlength q hq] using hc
  have hgood (i : ℕ) (hi : i ≤ middle.length) :
      (S.card - (Fintype.card (Option tm.State) + 1) ^ L) * L ≤ ∑ p ∈ S, (cs i p).length :=
    card_sub_pow_mul_le_sum_length (hinj i hi) L
  have hupper (p : X × Y) :
      ∑ i ∈ Finset.range (middle.length + 1), (cs i p).length ≤ T n := by
    have h := AbsCfg.sum_length_crossings_le
      ((Finset.range (middle.length + 1)).image fun i : ℕ => ((m + i : ℕ) : ℤ))
      (tm.absInit ((leftWord p.1 ++ middle ++ rightWord p.2).map ι)) (T n)
    rwa [Finset.sum_image fun i _ j _ hij => by omega] at h
  calc (middle.length + 1) * (S.card - (Fintype.card (Option tm.State) + 1) ^ L) * L
      = ∑ _i ∈ Finset.range (middle.length + 1),
          (S.card - (Fintype.card (Option tm.State) + 1) ^ L) * L := by simp [Nat.mul_assoc]
    _ ≤ ∑ i ∈ Finset.range (middle.length + 1), ∑ p ∈ S, (cs i p).length :=
      Finset.sum_le_sum fun i hi =>
        hgood i (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi)
    _ = ∑ p ∈ S, ∑ i ∈ Finset.range (middle.length + 1), (cs i p).length := Finset.sum_comm
    _ ≤ ∑ _p ∈ S, T n := Finset.sum_le_sum fun p _ => hupper p
    _ = S.card * T n := by simp

/-- If the short crossing sequences can cover at most half the fooling set, the machine spends
at least `L / 2` steps per boundary of the common middle word, averaged over the hard inputs. -/
theorem crossing_foolingSet_half_bound (L : ℕ)
    (hL : 2 * (Fintype.card (Option tm.State) + 1) ^ L ≤ S.card) :
    (middle.length + 1) * L ≤ 2 * T n := by
  have h := crossing_foolingSet_bound hdec hS leftWord middle rightWord hA hprefix hlength L
  have hpow : 0 < (Fintype.card (Option tm.State) + 1) ^ L := pow_pos (Nat.succ_pos _) _
  have hpos : 0 < S.card := by omega
  have h2 : S.card ≤ 2 * (S.card - (Fintype.card (Option tm.State) + 1) ^ L) := by omega
  refine Nat.le_of_mul_le_mul_left ?_ hpos
  calc S.card * ((middle.length + 1) * L)
      ≤ 2 * (S.card - (Fintype.card (Option tm.State) + 1) ^ L) *
          ((middle.length + 1) * L) := Nat.mul_le_mul_right _ h2
    _ = 2 * ((middle.length + 1) * (S.card - (Fintype.card (Option tm.State) + 1) ^ L) * L) :=
      by ring
    _ ≤ 2 * (S.card * T n) := Nat.mul_le_mul_left _ h
    _ = S.card * (2 * T n) := by ring

/-- A fooling set of at least `2 ^ bits` pairs forces time proportional to the length of the
common middle word times `bits`, divided by the logarithm of the state count. The lower bound
on `bits` absorbs the rounding and short-sequence terms. -/
theorem crossing_foolingSet_bit_bound (bits : ℕ)
    (hbits : 2 * Nat.clog 2 (Fintype.card tm.State + 2) ≤ bits) (hcard : 2 ^ bits ≤ S.card) :
    (middle.length + 1) * bits ≤ 4 * Nat.clog 2 (Fintype.card tm.State + 2) * T n := by
  let d := Nat.clog 2 (Fintype.card tm.State + 2)
  let L := (bits - 1) / d
  have hd : 0 < d := Nat.clog_pos one_lt_two (by omega)
  have hpow : Fintype.card (Option tm.State) + 1 ≤ 2 ^ d := by
    rw [Fintype.card_option]
    exact Nat.le_pow_clog one_lt_two _
  have hdiv : d * L + (bits - 1) % d = bits - 1 := Nat.div_add_mod (bits - 1) d
  have hmod := Nat.mod_lt (bits - 1) hd
  have hbits' : 2 * d ≤ bits := hbits
  have hL : 2 * (Fintype.card (Option tm.State) + 1) ^ L ≤ 2 ^ bits := by
    calc 2 * (Fintype.card (Option tm.State) + 1) ^ L
        ≤ 2 * (2 ^ d) ^ L := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpow L)
      _ = 2 ^ (d * L + 1) := by rw [← pow_mul]; ring
      _ ≤ 2 ^ bits := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h := crossing_foolingSet_half_bound hdec hS leftWord middle rightWord hA hprefix hlength L
    (hL.trans hcard)
  have hbitsL : bits ≤ 2 * (d * L) := by omega
  calc (middle.length + 1) * bits ≤ (middle.length + 1) * (2 * (d * L)) :=
      Nat.mul_le_mul_left _ hbitsL
    _ = 2 * d * ((middle.length + 1) * L) := by ring
    _ ≤ 2 * d * (2 * T n) := Nat.mul_le_mul_left _ h
    _ = 4 * Nat.clog 2 (Fintype.card tm.State + 2) * T n := by ring

end Cslib.Turing.SingleTapeTM
