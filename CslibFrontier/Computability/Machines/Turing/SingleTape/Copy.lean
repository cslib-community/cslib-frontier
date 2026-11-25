/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Languages.Copy
public import CslibFrontier.Computability.Machines.Turing.SingleTape.FoolingSet
import CslibFrontier.Computability.Communication.Functions
import Mathlib.Tactic.Linarith

/-!
# A quadratic single-tape lower bound for the copy language

A deterministic single-tape machine deciding the ordinary binary language `{x ++ x}` needs
quadratic time at every sufficiently large even input length. There is no delimiter and no
promised input format. The machine halts on all inputs and answers under its head; the rest of
the final tape is unrestricted. Its input is on its only tape, so this is not a lower bound for
a machine with a separate input tape and a work tape.

For a half-length `n`, let `m = n / 2` and `r = n - m`. Restrict inputs to
`x ++ falseʳ ++ y ++ falseʳ`, where `x` and `y` have length `m`. Such a word belongs to the copy
language exactly when `x = y`. The diagonal equality fooling set has `2 ^ m` pairs and a common
middle block of length `r`. The communication-to-crossing transfer therefore gives the lower
bound, without another machine-specific splicing or counting proof.

This is an application of Hennie's crossing-sequence method [Hennie1965, §II.B and §III.A].
His §III.A studies the different padded language `x 2^|x| x`; the theorem here is for unmarked
binary copying, with the explicit native-model constant below. The statement concerns even
lengths because all words of odd length are outside the copy language.

## Main results

* `Cslib.Turing.SingleTapeTM.copy_lower_bound`: with `d = ⌈log₂ (|Q| + 2)⌉`, every
  `n ≥ 4d` satisfies `(2n)² ≤ 64d T(2n)`.

## References

* [F. C. Hennie, *One-tape, off-line Turing machine computations*][Hennie1965]
-/

public section

open Cslib Cslib.Turing

namespace Cslib.Turing.SingleTapeTM

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol] {tm : SingleTapeTM Symbol}

/-- Every sufficiently large even input length has a quadratic worst-case lower bound for a
single-tape decider of the unmarked binary copy language. The input occupies the machine's only
tape, and the answer is read under the head at halting. The explicit constant depends only on
the finite state set, not on the tape alphabet or the letter map. -/
theorem copy_lower_bound {ι : Bool → Symbol} {yes : Symbol} {T : ℕ → ℕ}
    (hdec : tm.DecidesByHeadInTime ι (Cslib.Language.copy Bool) yes T) {n : ℕ}
    (hn : 4 * Nat.clog 2 (Fintype.card tm.State + 2) ≤ n) :
    (2 * n) ^ 2 ≤ 64 * Nat.clog 2 (Fintype.card tm.State + 2) * T (2 * n) := by
  classical
  let d := Nat.clog 2 (Fintype.card tm.State + 2)
  let m := n / 2
  let r := n - m
  have hd : 0 < d := Nat.clog_pos one_lt_two (by omega)
  have hmle : m ≤ n := Nat.div_le_self _ _
  have hsum : m + r = n := by dsimp [r]; omega
  have hm : 2 * d ≤ m := by dsimp [m, d] at *; omega
  let S := (Finset.univ : Finset (Fin m → Bool)).image fun x => (x, x)
  have hcard : S.card = 2 ^ m := by
    dsimp [S]
    rw [Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)]
    simp
  have hA (x y : Fin m → Bool) :
      List.ofFn x ++ List.replicate r false ++ (List.ofFn y ++ List.replicate r false) ∈
        Cslib.Language.copy Bool ↔ Communication.equality x y = true := by
    have h := Cslib.Language.append_mem_copy_iff
      (u := List.ofFn x ++ List.replicate r false)
      (v := List.ofFn y ++ List.replicate r false) (by simp)
    simpa only [List.append_assoc, List.append_left_inj, List.ofFn_inj,
      Communication.equality, decide_eq_true_eq] using h
  have h := crossing_foolingSet_bit_bound hdec
    (Communication.isFoolingSet_equality (Finset.univ : Finset (Fin m → Bool)))
    List.ofFn (List.replicate r false) (fun y => List.ofFn y ++ List.replicate r false)
    hA (m := m) (n := 2 * n) (fun _ _ => by simp)
    (fun _ _ => by simp only [List.length_append, List.length_ofFn, List.length_replicate]; omega)
    m hm (by change 2 ^ m ≤ S.card; rw [hcard])
  simp only [List.length_replicate] at h
  have hquad : n ^ 2 ≤ 4 * (r + 1) * m := by
    have hrem := Nat.mod_lt n (by decide : 0 < 2)
    have hdiv := Nat.div_add_mod n 2
    change 2 * m + n % 2 = n at hdiv
    rcases (by omega : n = 2 * m ∨ n = 2 * m + 1) with hn' | hn' <;> nlinarith
  nlinarith

end Cslib.Turing.SingleTapeTM
