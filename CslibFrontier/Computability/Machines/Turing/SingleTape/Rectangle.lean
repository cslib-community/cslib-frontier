/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.SingleTape.Communication
public import Mathlib.Data.Nat.Log
import CslibFrontier.Foundations.Data.List.LengthCounting
import Mathlib.Tactic.Ring

/-!
# Monochromatic rectangle size gives single-tape time lower bounds

Suppose language membership on `leftWord x ++ middle ++ rightWord y` represents `f x y`.
If every monochromatic rectangle of `f`, of either color, has at most `R` pairs, then at a
boundary in the common middle block each crossing sequence occurs on at most `2 R` selected
inputs. Indeed, the pairs sharing that sequence and a verdict lie inside the rectangle formed
by their two projections, and cut-and-paste makes this rectangle monochromatic.

For a finite family of `q` selected pairs and any threshold `L`, summing crossing lengths gives

`(middle.length + 1) * (q - 2 * R * (|Q| + 2)^L) * L ≤ ∑ p, time p`.

The individual halting times may differ, and only the selected prefixes need have equal
lengths. For inputs of a common total length `n`, choosing `time p = T n` gives `q * T n`
on the right.
On the full finite product, a rectangle size at most a `2^(-bits)` fraction of the inputs
therefore gives `(middle.length + 1) * bits ≤ 4 * ⌈log₂ (|Q| + 2)⌉ * T n`, once
`bits ≥ 2 * ⌈log₂ (|Q| + 2)⌉ + 2`.

This is an original library transfer of monochromatic-rectangle bounds to native deterministic
single-tape runs. It requires no fooling set and no communication protocol supplied by the
caller. The machine's only tape initially holds the input, its answer is under the halting
head, and the rest of the final tape is unrestricted.

## Main results

* `Cslib.Turing.SingleTapeTM.crossing_rectangle_sum_bound`: a lower bound on the sum of
  individual running times, including families with different total input lengths.
* `Cslib.Turing.SingleTapeTM.crossing_rectangle_bound`: the equal-length worst-case bound.
* `Cslib.Turing.SingleTapeTM.crossing_rectangle_bit_sum_bound`: the uniform-average bound.
* `Cslib.Turing.SingleTapeTM.crossing_rectangle_bit_bound`: the exponential rectangle-size
  specialization used for inner product.
-/

public section

open Cslib Cslib.Turing

namespace Cslib.Turing.SingleTapeTM

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol] {tm : SingleTapeTM Symbol}
  {α : Type*} {ι : α → Symbol} {A : Language α} {yes : Symbol} {T : ℕ → ℕ}
  {X Y : Type*} {f : X → Y → Bool} {S : Finset (X × Y)} {R m n : ℕ}
  (hdec : tm.DecidesByHeadInTime ι A yes T)
  (leftWord : X → List α) (middle : List α) (rightWord : Y → List α)
  (hA : ∀ x y, leftWord x ++ middle ++ rightWord y ∈ A ↔ f x y = true)
  (hprefix : ∀ p ∈ S, (leftWord p.1).length = m)
  (hrectangle : ∀ (U : Finset X) (V : Finset Y) (z : Bool),
    (∀ x ∈ U, ∀ y ∈ V, f x y = z) → U.card * V.card ≤ R)

include hdec hA hprefix hrectangle

/-- Monochromatic rectangle size bounds the sum of the individual halting times on a selected
finite family of inputs. Empty families, threshold zero and rectangle bound zero are included.
The times refer to the native machine's absolute-coordinate run, which is step-exact with its
configuration transition relation. -/
theorem crossing_rectangle_sum_bound (time : X × Y → ℕ)
    (htime : ∀ p ∈ S,
      ((tm.absInit ((leftWord p.1 ++ middle ++ rightWord p.2).map ι)).run (time p)).state = none)
    (L : ℕ) :
    (middle.length + 1) * (S.card - 2 * R * (Fintype.card (Option tm.State) + 1) ^ L) * L ≤
      ∑ p ∈ S, time p := by
  classical
  let cfg (p : X × Y) := tm.absInit ((leftWord p.1 ++ middle ++ rightWord p.2).map ι)
  let cs (i : ℕ) (p : X × Y) := (cfg p).crossings ((m + i : ℕ) : ℤ) (time p)
  have hcs (i : ℕ) (p : X × Y) (hp : p ∈ S) : cs i p =
      (cfg p).crossings ((m + i : ℕ) : ℤ) (T (leftWord p.1 ++ middle ++ rightWord p.2).length) :=
    AbsCfg.crossings_eq_of_halted _ _ (htime p hp) (hdec.absRun _).1
  have hfiber (i : ℕ) (hi : i ≤ middle.length) (s : List (Option tm.State)) :
      (S.filter fun p => cs i p = s).card ≤ 2 * R := by
    have hcolor (z : Bool) : (S.filter fun p => cs i p = s ∧ f p.1 p.2 = z).card ≤ R := by
      let F := S.filter fun p => cs i p = s ∧ f p.1 p.2 = z
      let U := F.image Prod.fst
      let V := F.image Prod.snd
      have hmono : ∀ x ∈ U, ∀ y ∈ V, f x y = z := by
        intro x hx y hy
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
        obtain ⟨hpS, hps, hpz⟩ := Finset.mem_filter.mp hp
        obtain ⟨hqS, hqs, hqz⟩ := Finset.mem_filter.mp hq
        exact (crossings_splice_verdict hdec leftWord middle rightWord hA hi
          (hprefix p hpS) (hprefix q hqS) (hpz.trans hqz.symm)
          (by rw [← hcs i p hpS, ← hcs i q hqS, hps, hqs])).trans hpz
      calc F.card ≤ (U ×ˢ V).card := Finset.card_le_card Finset.subset_product
        _ = U.card * V.card := Finset.card_product U V
        _ ≤ R := hrectangle U V z hmono
    let F := S.filter fun p => cs i p = s
    calc F.card = ∑ z : Bool, (F.filter fun p => f p.1 p.2 = z).card :=
          Finset.card_eq_sum_card_fiberwise fun _ _ => Finset.mem_univ _
      _ ≤ ∑ _z : Bool, R := Finset.sum_le_sum fun z _ => by
          simpa only [F, Finset.filter_filter] using hcolor z
      _ = 2 * R := by simp
  let K := (Finset.range (middle.length + 1)).image fun i : ℕ => ((m + i : ℕ) : ℤ)
  have hcard : K.card = middle.length + 1 := by
    dsimp only [K]
    rw [Finset.card_image_of_injective _ (fun i j h => by omega), Finset.card_range]
  have h := AbsCfg.card_mul_le_sum_time cfg time S K
    (b := (S.card - 2 * R * (Fintype.card (Option tm.State) + 1) ^ L) * L) fun k hk => by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
      exact Finset.card_sub_mul_pow_mul_le_sum_length (f := cs i) (fun s =>
        hfiber i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) s) L
  simpa only [hcard, Nat.mul_assoc] using h

/-- When the selected inputs all have length `n`, the rectangle argument gives a lower bound
on the native worst-case time bound at `n`. The finite family need not itself be a rectangle. -/
theorem crossing_rectangle_bound
    (hlength : ∀ p ∈ S, (leftWord p.1 ++ middle ++ rightWord p.2).length = n) (L : ℕ) :
    (middle.length + 1) * (S.card - 2 * R * (Fintype.card (Option tm.State) + 1) ^ L) * L ≤
      S.card * T n := by
  calc _ ≤ ∑ p ∈ S, T (leftWord p.1 ++ middle ++ rightWord p.2).length :=
      crossing_rectangle_sum_bound hdec leftWord middle rightWord hA hprefix hrectangle
        (fun p => T (leftWord p.1 ++ middle ++ rightWord p.2).length)
        (fun p _ => (hdec.absRun _).1) L
    _ = ∑ _p ∈ S, T n := Finset.sum_congr rfl fun p hp => congrArg T (hlength p hp)
    _ = S.card * T n := by simp

omit hprefix hrectangle in
/-- Exponentially small monochromatic rectangles force a lower bound on the sum of the
individual native halting times across the whole input product. This is the division-free
uniform-average form, and it also includes empty input domains. -/
theorem crossing_rectangle_bit_sum_bound [Fintype X] [Fintype Y]
    (hprefix : ∀ x, (leftWord x).length = m)
    (hrectangle : ∀ (U : Finset X) (V : Finset Y) (z : Bool),
      (∀ x ∈ U, ∀ y ∈ V, f x y = z) → U.card * V.card ≤ R)
    (bits : ℕ) (hbits : 2 * Nat.clog 2 (Fintype.card tm.State + 2) + 2 ≤ bits)
    (hcard : 2 ^ bits * R ≤ Fintype.card X * Fintype.card Y)
    (time : X × Y → ℕ)
    (htime : ∀ p,
      ((tm.absInit ((leftWord p.1 ++ middle ++ rightWord p.2).map ι)).run (time p)).state = none) :
    (Fintype.card X * Fintype.card Y) * ((middle.length + 1) * bits) ≤
      4 * Nat.clog 2 (Fintype.card tm.State + 2) * ∑ p, time p := by
  classical
  let d := Nat.clog 2 (Fintype.card tm.State + 2)
  let L := (bits - 2) / d
  let q := Fintype.card X * Fintype.card Y
  let short := 2 * R * (Fintype.card (Option tm.State) + 1) ^ L
  have hd : 0 < d := Nat.clog_pos one_lt_two (by omega)
  have hpow : Fintype.card (Option tm.State) + 1 ≤ 2 ^ d := by
    rw [Fintype.card_option]
    exact Nat.le_pow_clog one_lt_two _
  have hdiv : d * L + (bits - 2) % d = bits - 2 := Nat.div_add_mod (bits - 2) d
  have hmod := Nat.mod_lt (bits - 2) hd
  have hsmall : 4 * (Fintype.card (Option tm.State) + 1) ^ L ≤ 2 ^ bits := by
    calc 4 * (Fintype.card (Option tm.State) + 1) ^ L
        ≤ 4 * (2 ^ d) ^ L := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpow L)
      _ = 2 ^ (d * L + 2) := by rw [← pow_mul, pow_add]; ring
      _ ≤ 2 ^ bits := Nat.pow_le_pow_right (by omega) (by omega)
  have hshort : 2 * short ≤ q := by
    calc 2 * short = (4 * (Fintype.card (Option tm.State) + 1) ^ L) * R := by ring
      _ ≤ 2 ^ bits * R := Nat.mul_le_mul_right R hsmall
      _ ≤ q := hcard
  have h := crossing_rectangle_sum_bound hdec leftWord middle rightWord hA
    (S := Finset.univ) (fun p _ => hprefix p.1) hrectangle time (fun p _ => htime p) L
  calc q * ((middle.length + 1) * bits)
      ≤ (2 * (q - short)) * ((middle.length + 1) * (2 * (d * L))) :=
        Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ (by omega))
    _ = 4 * d * ((middle.length + 1) * (q - short) * L) := by ring
    _ ≤ 4 * d * ∑ p, time p :=
        Nat.mul_le_mul_left _ (by simpa only [Finset.card_univ, Fintype.card_prod] using h)

omit hprefix hrectangle in
/-- If every monochromatic rectangle has at most a `2^(-bits)` fraction of the full input
product, the machine needs time proportional to `bits` times the middle-block length, with
only a logarithmic dependence on its number of states. Both domains must be nonempty. -/
theorem crossing_rectangle_bit_bound [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
    (hprefix : ∀ x, (leftWord x).length = m)
    (hlength : ∀ x y, (leftWord x ++ middle ++ rightWord y).length = n)
    (hrectangle : ∀ (U : Finset X) (V : Finset Y) (z : Bool),
      (∀ x ∈ U, ∀ y ∈ V, f x y = z) → U.card * V.card ≤ R)
    (bits : ℕ) (hbits : 2 * Nat.clog 2 (Fintype.card tm.State + 2) + 2 ≤ bits)
    (hcard : 2 ^ bits * R ≤ Fintype.card X * Fintype.card Y) :
    (middle.length + 1) * bits ≤ 4 * Nat.clog 2 (Fintype.card tm.State + 2) * T n := by
  have htime (p : X × Y) :
      ((tm.absInit ((leftWord p.1 ++ middle ++ rightWord p.2).map ι)).run (T n)).state = none := by
    simpa only [hlength] using (hdec.absRun (leftWord p.1 ++ middle ++ rightWord p.2)).1
  have h := crossing_rectangle_bit_sum_bound hdec leftWord middle rightWord hA hprefix
    hrectangle bits hbits hcard (fun _ => T n) htime
  have hq : 0 < Fintype.card X * Fintype.card Y := Nat.mul_pos Fintype.card_pos Fintype.card_pos
  apply Nat.le_of_mul_le_mul_left (c := Fintype.card X * Fintype.card Y) ?_ hq
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, smul_eq_mul,
    Nat.mul_left_comm, Nat.mul_assoc] using h

end Cslib.Turing.SingleTapeTM
