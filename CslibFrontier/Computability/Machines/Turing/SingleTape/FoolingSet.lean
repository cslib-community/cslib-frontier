/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.FoolingSet
public import CslibFrontier.Computability.Machines.Turing.SingleTape.Communication
public import Mathlib.Data.Nat.Log
import CslibFrontier.Foundations.Data.List.LengthCounting
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
  intro p hp q hq hc
  have hz : f p.1 p.2 = f q.1 q.2 := (hS.1 p hp).trans (hS.1 q hq).symm
  have hpq := crossings_splice_verdict hdec leftWord middle rightWord hA hi
    (hprefix p hp) (hprefix q hq) hz hc
  have hqp := crossings_splice_verdict hdec leftWord middle rightWord hA hi
    (hprefix q hq) (hprefix p hp) hz.symm hc.symm
  exact hS.2 p hp q hq (hpq.trans (hS.1 p hp)) (hqp.trans (hS.1 q hq))

variable (hlength : ∀ p ∈ S, (leftWord p.1 ++ middle ++ rightWord p.2).length = n)

include hlength

/-- Summing over the fooling set and all boundaries in the common middle word gives a native
running-time lower bound. The finite-list counting term also handles an empty fooling set and
threshold zero without separate nonemptiness hypotheses. -/
theorem crossing_foolingSet_bound (L : ℕ) :
    (middle.length + 1) * (S.card - (Fintype.card (Option tm.State) + 1) ^ L) * L ≤
      S.card * T n := by
  classical
  let cs (i : ℕ) (p : X × Y) : List (Option tm.State) :=
    (tm.absInit ((leftWord p.1 ++ middle ++ rightWord p.2).map ι)).crossings
      ((m + i : ℕ) : ℤ) (T n)
  have hinj (i : ℕ) (hi : i ≤ middle.length) : Set.InjOn (cs i) (S : Set (X × Y)) :=
    fun p hp q hq hc => crossings_injOn_of_isFoolingSet hdec hS leftWord middle rightWord hA
      hprefix hi hp hq (by simpa only [cs, hlength p hp, hlength q hq] using hc)
  let K := (Finset.range (middle.length + 1)).image fun i : ℕ => ((m + i : ℕ) : ℤ)
  have hcard : K.card = middle.length + 1 :=
    (Finset.card_image_of_injective _ fun _ _ h => by omega).trans (Finset.card_range _)
  simpa only [hcard, Finset.sum_const, smul_eq_mul, Nat.mul_assoc] using
    AbsCfg.card_mul_le_sum_time
      (fun p : X × Y => tm.absInit ((leftWord p.1 ++ middle ++ rightWord p.2).map ι))
      (fun _ => T n) S K (b := (S.card - (Fintype.card (Option tm.State) + 1) ^ L) * L)
      fun k hk => let ⟨i, hi, heq⟩ := Finset.mem_image.mp hk
        heq ▸ Finset.card_sub_pow_mul_le_sum_length
          (hinj i (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi)) L

/-- If the short crossing sequences can cover at most half the fooling set, the machine spends
at least `L / 2` steps per boundary of the common middle word, averaged over the hard inputs. -/
theorem crossing_foolingSet_half_bound (L : ℕ)
    (hL : 2 * (Fintype.card (Option tm.State) + 1) ^ L ≤ S.card) :
    (middle.length + 1) * L ≤ 2 * T n := by
  have h := crossing_foolingSet_bound hdec hS leftWord middle rightWord hA hprefix hlength L
  have hpow : 0 < (Fintype.card (Option tm.State) + 1) ^ L := pow_pos (Nat.succ_pos _) _
  refine Nat.le_of_mul_le_mul_left ?_ (by omega : 0 < S.card)
  calc S.card * ((middle.length + 1) * L)
      ≤ 2 * (S.card - (Fintype.card (Option tm.State) + 1) ^ L) *
          ((middle.length + 1) * L) := Nat.mul_le_mul_right _ (by omega)
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
  have hL : 2 * (Fintype.card (Option tm.State) + 1) ^ L ≤ 2 ^ bits := by
    calc 2 * (Fintype.card (Option tm.State) + 1) ^ L
        ≤ 2 * (2 ^ d) ^ L := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpow L)
      _ = 2 ^ (d * L + 1) := by rw [← pow_mul]; ring
      _ ≤ 2 ^ bits := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h := crossing_foolingSet_half_bound hdec hS leftWord middle rightWord hA hprefix hlength L
    (hL.trans hcard)
  calc (middle.length + 1) * bits ≤ (middle.length + 1) * (2 * (d * L)) :=
      Nat.mul_le_mul_left _ (by omega)
    _ = 2 * d * ((middle.length + 1) * L) := by ring
    _ ≤ 2 * d * (2 * T n) := Nat.mul_le_mul_left _ h
    _ = 4 * Nat.clog 2 (Fintype.card tm.State + 2) * T n := by ring

end Cslib.Turing.SingleTapeTM
