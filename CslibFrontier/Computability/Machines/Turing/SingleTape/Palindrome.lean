/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.SingleTape.CrossingSequence
public import Mathlib.Data.List.Palindrome
public import Mathlib.Data.Nat.Log
import CslibFrontier.Computability.Communication.Functions
import CslibFrontier.Computability.Machines.Turing.SingleTape.FoolingSet
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Single-tape machines need quadratic time for palindromes

The classical quadratic lower bound for palindromes, proved with Hennie's crossing-sequence
method: a deterministic single-tape Turing machine (`Cslib.Turing.SingleTapeTM`) that decides
palindromes needs `Ω(n²)` steps on some input of each large length `n`.

The proof uses crossing sequences (`CrossingSequence.lean`). Fix `m` and `r` and consider the
`2 ^ m` hard inputs `palWord r x = x ++ falseʳ ++ reverse x` for bit strings `x` of length `m`.
All of them are palindromes. If two distinct hard inputs had the same crossing sequence at a
boundary inside the middle block, the cut-and-paste lemma would make the machine accept a
non-palindrome. So at every such boundary the `2 ^ m` crossing sequences are distinct. Fewer than
half of them can be shorter than about `m / log |Q|`. Since the crossing sequences of one run have
total length at most its running time, some hard input needs time proportional to
`r · m / log |Q|`.

The lower bound is stated for deciders that answer under the head (`DecidesByHeadInTime`): the
machine halts within the time bound, and the cell under the head then holds `yes` exactly on
palindromes. The rest of the final tape is unconstrained. Deciders in cslib's canonical output
form (`DecidesPalindromesInTime`) are a special case.

## Main definitions

* `Cslib.Turing.SingleTapeTM.DecidesPalindromesInTime tm a b yes T`: on every word over the
  letters `a, b`, `tm` halts within `T n` steps and its output begins with `yes` exactly when
  the input is a palindrome. Halting goes through `OutputsWithinTime`, so the final tape holds
  only the output, with the head on its first cell.
* `Cslib.Turing.SingleTapeTM.bitSymbol a b`: the letter map writing `false, true` as `a, b`.
* `Cslib.Turing.SingleTapeTM.palWord r x`: the hard inputs.

## Main results

* `Cslib.Turing.SingleTapeTM.DecidesPalindromesInTime.decidesByHeadInTime`: a canonical-output
  palindrome decider answers under the head, through `bitSymbol a b`.
* `Cslib.Turing.SingleTapeTM.crossings_palWord_injective`: distinct hard inputs have distinct
  crossing sequences at every boundary inside the middle block.
* `Cslib.Turing.SingleTapeTM.crossing_bound`: if `2 (|Q| + 2) ^ L ≤ 2 ^ m`, then
  `(r + 1) L ≤ 2 T (2m + r)`.
* `Cslib.Turing.SingleTapeTM.palindrome_lower_bound`: with `d = ⌈log₂ (|Q| + 2)⌉`, every
  `n ≥ 8d` satisfies `n² ≤ 64 d T(n)`.
* `Cslib.Turing.SingleTapeTM.not_decidesByHeadInTime_palindromes_linear` and
  `Cslib.Turing.SingleTapeTM.not_decidesPalindromesInTime_linear`: no single-tape machine
  decides palindromes within time `c (n + 1)`.

## References

* [F. C. Hennie, *One-tape, off-line Turing machine computations*][Hennie1965]
* [M. Li and P. Vitányi, *An Introduction to Kolmogorov Complexity and Its
  Applications*][LiVitanyi2019], Chapter 6 (an incompressibility version of the same argument)
-/

public section

open Cslib Cslib.Turing

namespace Cslib.Turing.SingleTapeTM

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol] {tm : SingleTapeTM Symbol}

omit [Inhabited Symbol] [Fintype Symbol] in
private lemma palindrome_append_replicate_append_reverse {u : List Symbol} {c : Symbol} {r : ℕ}
    {w : List Symbol} (hw : w.length = u.length) :
    (u ++ List.replicate r c ++ w.reverse).Palindrome ↔ w = u := by
  rw [List.Palindrome.iff_reverse_eq]
  simp only [List.reverse_append, List.reverse_reverse, List.reverse_replicate, List.append_assoc]
  constructor
  · intro h
    exact (List.append_inj h hw).1
  · rintro rfl
    rfl

variable (tm) in
/-- `tm` decides palindromes over the letters `a, b` within time `T`: on every word over
`{a, b}` of length `n` it halts within `T n` steps, and its output begins with `yes` exactly
when the word is a palindrome. Symbols other than `a` and `b` may occur in the alphabet and on
the tape; inputs containing them are unconstrained.

The output is in cslib's canonical form: `OutputsWithinTime w o` requires reaching
`haltCfg o`, so the machine must erase everything except `o` and halt with the head on the first
cell of `o`. This is narrower than acceptance by state; a decider that halts with other symbols
left on the tape is not covered. -/
@[expose] def DecidesPalindromesInTime (a b yes : Symbol) (T : ℕ → ℕ) : Prop :=
  ∀ w : List Symbol, (∀ x ∈ w, x = a ∨ x = b) →
    ∃ o, tm.OutputsWithinTime w o (T w.length) ∧ (o.head? = some yes ↔ w.Palindrome)

/-- The letter map writing `false` as `a` and `true` as `b`. -/
@[expose] def bitSymbol (a b : Symbol) (β : Bool) : Symbol := if β then b else a

omit [Inhabited Symbol] [Fintype Symbol] in
lemma bitSymbol_injective {a b : Symbol} (hab : a ≠ b) : Function.Injective (bitSymbol a b) := by
  intro β γ h
  cases β <;> cases γ <;> simp_all [bitSymbol, eq_comm]

omit [Inhabited Symbol] [Fintype Symbol] in
private lemma palindrome_map_iff {β γ : Type*} {f : β → γ} (hf : Function.Injective f)
    {w : List β} : (w.map f).Palindrome ↔ w.Palindrome := by
  rw [List.Palindrome.iff_reverse_eq, List.Palindrome.iff_reverse_eq, ← List.map_reverse]
  exact (List.map_injective_iff.mpr hf).eq_iff

/-- A palindrome decider in canonical output form also decides palindromes over `Bool`, written
with the letters `a ≠ b`, answering under the head. -/
theorem DecidesPalindromesInTime.decidesByHeadInTime {a b yes : Symbol} (hab : a ≠ b)
    {T : ℕ → ℕ} (h : tm.DecidesPalindromesInTime a b yes T) :
    tm.DecidesByHeadInTime (bitSymbol a b) {w : List Bool | w.Palindrome} yes T := by
  intro w
  obtain ⟨o, ho, hyes⟩ := h (w.map (bitSymbol a b)) fun x hx => by
    obtain ⟨β, -, rfl⟩ := List.mem_map.mp hx
    cases β <;> simp [bitSymbol]
  rw [List.length_map] at ho
  refine ⟨tm.haltCfg o, ho, rfl, ?_⟩
  simp only [haltCfg, BiTape.head_mk₁]
  rw [hyes]
  exact palindrome_map_iff (bitSymbol_injective hab)

/-- The hard inputs: `x`, a block of `r` copies of `false`, then `x` reversed. -/
@[expose] def palWord (r : ℕ) (x : List Bool) : List Bool :=
  x ++ List.replicate r false ++ x.reverse

@[simp] lemma length_palWord (r : ℕ) (x : List Bool) :
    (palWord r x).length = 2 * x.length + r := by
  simp [palWord]; omega

/-- Distinct hard inputs have distinct crossing sequences at every boundary inside the middle
block. -/
theorem crossings_palWord_injective {ι : Bool → Symbol} {yes : Symbol} {T : ℕ → ℕ}
    (hdec : tm.DecidesByHeadInTime ι {w : List Bool | w.Palindrome} yes T) {r i : ℕ}
    (hi : i ≤ r) {x y : List Bool} (hxy : y.length = x.length)
    (h : (tm.absInit ((palWord r x).map ι)).crossings ((x.length + i : ℕ) : ℤ)
        (T (2 * x.length + r)) =
      (tm.absInit ((palWord r y).map ι)).crossings ((x.length + i : ℕ) : ℤ)
        (T (2 * x.length + r))) :
    x = y := by
  classical
  let X := {u : List Bool // u.length = x.length}
  let a : X := ⟨x, rfl⟩
  let b : X := ⟨y, hxy⟩
  have hinj := crossings_injOn_of_isFoolingSet hdec
    (Communication.isFoolingSet_equality ({a, b} : Finset X))
    Subtype.val (List.replicate r false) (fun v : X => v.val.reverse)
    (fun u v => by
      change (u.val ++ List.replicate r false ++ v.val.reverse).Palindrome ↔ _
      rw [palindrome_append_replicate_append_reverse (v.2.trans u.2.symm),
        Communication.equality, decide_eq_true_eq]
      exact ⟨fun h => Subtype.ext h.symm, fun h => congrArg Subtype.val h.symm⟩)
    (fun p _ => p.1.2) (by simpa only [List.length_replicate] using hi)
  refine congrArg (fun p : X × X => p.1.val) (hinj (by simp) (by simp) ?_ : (a, a) = (b, b))
  change (tm.absInit ((palWord r x).map ι)).crossings ((x.length + i : ℕ) : ℤ)
      (T (palWord r x).length) =
    (tm.absInit ((palWord r y).map ι)).crossings ((x.length + i : ℕ) : ℤ)
      (T (palWord r y).length)
  simpa only [length_palWord, hxy] using h

private lemma palindrome_ofFn_mix_iff (m r : ℕ) (x y : Fin m → Bool) :
    (List.ofFn x ++ List.replicate r false ++ (List.ofFn y).reverse).Palindrome ↔
      Communication.equality x y = true := by
  rw [palindrome_append_replicate_append_reverse (by simp)]
  simp [Communication.equality, List.ofFn_inj, eq_comm]

/-- **Averaging step.** If at most half of the `2 ^ m` hard inputs can have a crossing sequence
shorter than `L` at any boundary, some hard input of length `2m + r` crosses the `r + 1` middle
boundaries at least `(r + 1) L / 2` times in total. -/
theorem crossing_bound {ι : Bool → Symbol} {yes : Symbol} {T : ℕ → ℕ}
    (hdec : tm.DecidesByHeadInTime ι {w : List Bool | w.Palindrome} yes T) (m r L : ℕ)
    (hL : 2 * (Fintype.card (Option tm.State) + 1) ^ L ≤ 2 ^ m) :
    (r + 1) * L ≤ 2 * T (2 * m + r) := by
  classical
  let S := (Finset.univ : Finset (Fin m → Bool)).image fun x => (x, x)
  have hcard : S.card = 2 ^ m := by
    dsimp only [S]
    rw [Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)]
    simp
  have hbound := crossing_foolingSet_half_bound hdec
    (Communication.isFoolingSet_equality (Finset.univ : Finset (Fin m → Bool)))
    List.ofFn (List.replicate r false) (fun y : Fin m → Bool => (List.ofFn y).reverse)
    (palindrome_ofFn_mix_iff m r)
    (m := m) (n := 2 * m + r) (fun _ _ => List.length_ofFn)
    (fun _ _ => by simp; omega) L (by
      change 2 * (Fintype.card (Option tm.State) + 1) ^ L ≤ S.card
      rwa [hcard])
  simpa only [List.length_replicate] using hbound

/-- **Quadratic lower bound for palindromes** (via Hennie's crossing sequences). Let
`d = ⌈log₂ (|Q| + 2)⌉` where `Q` is the state set. If a single-tape machine decides the
palindromes over `Bool` within time `T`, answering under the head (`DecidesByHeadInTime`, with any
letter map `ι`), then `n ^ 2 ≤ 64 d T(n)` for every `n ≥ 8 d`. Canonical-output deciders are
covered through `DecidesPalindromesInTime.decidesByHeadInTime`. -/
theorem palindrome_lower_bound {ι : Bool → Symbol} {yes : Symbol} {T : ℕ → ℕ}
    (hdec : tm.DecidesByHeadInTime ι {w : List Bool | w.Palindrome} yes T) {n : ℕ}
    (hn : 8 * Nat.clog 2 (Fintype.card tm.State + 2) ≤ n) :
    n ^ 2 ≤ 64 * Nat.clog 2 (Fintype.card tm.State + 2) * T n := by
  obtain ⟨d, hd_def⟩ : ∃ d, d = Nat.clog 2 (Fintype.card tm.State + 2) := ⟨_, rfl⟩
  rw [← hd_def] at hn ⊢
  have hd : 0 < d := hd_def ▸ Nat.clog_pos one_lt_two (by omega)
  obtain ⟨m, hm⟩ : ∃ m, m = n / 4 := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = n - 2 * m := ⟨_, rfl⟩
  have hm2 : 2 * d ≤ m := by omega
  have h3 : (r + 1) * m ≤ 4 * d * T n := by
    classical
    have h := crossing_foolingSet_bit_bound hdec
      (Communication.isFoolingSet_equality (Finset.univ : Finset (Fin m → Bool)))
      List.ofFn (List.replicate r false) (fun y : Fin m → Bool => (List.ofFn y).reverse)
      (palindrome_ofFn_mix_iff m r) (m := m) (n := n) (fun _ _ => List.length_ofFn)
      (fun _ _ => by simp; omega) m (by simpa only [← hd_def] using hm2) (by
        rw [Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)]
        simp)
    simpa only [List.length_replicate, ← hd_def] using h
  have h4 : n + 2 ≤ 2 * (r + 1) := by omega
  have h5 : n ≤ 4 * m + 3 := by omega
  have h6 : 8 ≤ n := by omega
  have F1 := Nat.mul_le_mul_right (4 * m) h4
  have F2 := Nat.mul_le_mul_left (n + 2) h5
  have F3 := Nat.mul_le_mul_right (n + 6) h6
  nlinarith [F1, F2, F3, h3]

/-- No single-tape machine decides the palindromes over `Bool` in linear time, even answering
under the head. -/
theorem not_decidesByHeadInTime_palindromes_linear (ι : Bool → Symbol) (yes : Symbol) (c : ℕ) :
    ¬ tm.DecidesByHeadInTime ι {w : List Bool | w.Palindrome} yes fun n => c * (n + 1) := by
  intro hdec
  obtain ⟨d, hd_def⟩ : ∃ d, d = Nat.clog 2 (Fintype.card tm.State + 2) := ⟨_, rfl⟩
  have hd : 0 < d := hd_def ▸ Nat.clog_pos one_lt_two (by omega)
  have h := palindrome_lower_bound hdec (n := 8 * d + 64 * d * c + 2) (by omega)
  rw [← hd_def] at h
  have key : ∀ M N : ℕ, M + 2 ≤ N → N ^ 2 ≤ M * (N + 1) → False := fun M N h1 h2 => by
    have := Nat.mul_le_mul_right N h1
    nlinarith
  refine key (64 * d * c) (8 * d + 64 * d * c + 2) (by omega) ?_
  calc (8 * d + 64 * d * c + 2) ^ 2 ≤ 64 * d * (c * (8 * d + 64 * d * c + 2 + 1)) := h
    _ = 64 * d * c * (8 * d + 64 * d * c + 2 + 1) := by ring

/-- No single-tape machine decides palindromes over two letters in linear time. -/
theorem not_decidesPalindromesInTime_linear {a b yes : Symbol} (hab : a ≠ b) (c : ℕ) :
    ¬ DecidesPalindromesInTime tm a b yes fun n => c * (n + 1) := fun hdec =>
  not_decidesByHeadInTime_palindromes_linear _ _ c (hdec.decidesByHeadInTime hab)

end Cslib.Turing.SingleTapeTM
