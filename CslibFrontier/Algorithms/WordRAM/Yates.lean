/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Yates
public import CslibFrontier.Computability.WordRAM.ListOutput
public import CslibFrontier.Computability.WordRAM.Signed.Encoding
import CslibFrontier.Computability.WordRAM.Realization.FramedLoop
import CslibFrontier.Computability.WordRAM.Realization.ProgFrame
import CslibFrontier.Computability.WordRAM.Realization.Program.Standard
import CslibFrontier.Computability.WordRAM.Realization.Signed
import CslibFrontier.Computability.WordRAM.Realization.Structure
import CslibFrontier.DataStructure.StateTransition
import CslibFrontier.Foundations.Data.List.RowMajor
import CslibFrontier.Tactic.Realize
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
# Yates's fast zeta and Möbius transforms on the word RAM

Checked standard-basis word-RAM (`Cslib.WordRAM.Basis.standard`) implementations of Yates's
algorithm (`CslibFrontier.Algorithms.Lean.Yates`) running in `O((n + 1) · 2 ^ n)` instructions:

* **Unsigned `ℕ` fast zeta transform (`exists_zetaNat_program`)**: transforms an encoded table
  `I : NatInstance` (`I.n :: I.entries.toList`) in place to `(Yates.zeta I.entries).toList` in at
  most `C * ((I.n + 1) * 2 ^ I.n)` instructions (`Program.ComputesListInTime`) at every width `w`
  with `I.FitsWidth w`, using a single uniform width-blind deterministic program
  (`¬prog.ReadsWidth`, `prog.IsRandFree`).
* **Signed `ℤ` fast zeta and Möbius transforms (`exists_zetaInt_program`,
  `exists_mobiusInt_program`)**: transforms an encoded integer table `I : IntInstance`
  (`I.n :: I.entries.toList.map Signed.encode`) in place via `Realization.Signed.signedAddProg`
  and `Realization.Signed.signedSubProg` to `(Yates.zeta I.entries).toList.map Signed.encode` and
  `(Yates.mobius I.entries).toList.map Signed.encode`, each in at most
  `C * ((I.n + 1) * 2 ^ I.n)` instructions (`Program.ComputesListInTime`) at every width `w` with
  `I.FitsWidth w`, using uniform width-blind deterministic programs (`¬prog.ReadsWidth`,
  `prog.IsRandFree`).

All three transforms instantiate one parameterized `Memory.Prog` in-place butterfly
(`butterflyProg`) realized via `realize` and lifted to `Basis.standard`. Each coordinate pass
`0 ≤ i < n` visits the `2 ^ (n - 1)` aligned pairs `(loIdx (2 ^ i) p, hiIdx (2 ^ i) p)` without
bitwise instructions, updating the input buffer starting at address `2` in place, writing the
output length `2 ^ n` to address `1`, and returning `1`. The in-place word-RAM butterfly
realization, memory layout, and word-size envelopes are original to this formalization over
[BjorklundHusfeldtKoivisto2009] and [Williams2014].

## Word-size conditions

* For `NatInstance`, every intermediate and final zeta entry is a sum of distinct entries of
  `I.entries`, hence at most `I.totalSum = ∑ k, I.entries[k]`. The envelope
  `I.wordBound = 4 * (2 ^ I.n + I.totalSum + 16)` covers all table entries, addresses, and loop
  counters (`I.FitsWidth w` means `Fits w I.wordBound`, so `w` of order
  `n + log (I.totalSum + 2)` bits suffices).
* For `IntInstance`, every intermediate and final zeta or Möbius entry is a `(±1)`-weighted sum
  of distinct entries of `I.entries`, hence has magnitude at most
  `I.sumAbs = ∑ k, I.entries[k].natAbs`. The envelope
  `I.wordBound = 8 * (2 ^ I.n + I.sumAbs + 16)` covers all `Signed.encode` words, intermediate
  signed additions and subtractions, addresses, and loop counters (`w` of order
  `n + log (I.sumAbs + 2)` bits suffices).

## Main definitions

* `Cslib.Algorithms.WordRAM.Yates.NatInstance`: unsigned `2 ^ n`-entry `ℕ` table instance with
  `encode`, `totalSum`, `wordBound`, and `FitsWidth`.
* `Cslib.Algorithms.WordRAM.Yates.IntInstance`: signed `2 ^ n`-entry `ℤ` table instance with
  `encode`, `sumAbs`, `wordBound`, and `FitsWidth`.

## Main results

* `Cslib.Algorithms.WordRAM.Yates.NatInstance.inputFits`,
  `Cslib.Algorithms.WordRAM.Yates.IntInstance.inputFits`: width admissibility implies `InputFits`.
* `Cslib.Algorithms.WordRAM.Yates.exists_zetaNat_program`: uniform width-blind deterministic
  standard-basis Word-RAM program computing the unsigned fast zeta transform in
  `C * ((I.n + 1) * 2 ^ I.n)` instructions.
* `Cslib.Algorithms.WordRAM.Yates.exists_zetaInt_program`: uniform width-blind deterministic
  standard-basis Word-RAM program computing the signed fast zeta transform in
  `C * ((I.n + 1) * 2 ^ I.n)` instructions.
* `Cslib.Algorithms.WordRAM.Yates.exists_mobiusInt_program`: uniform width-blind deterministic
  standard-basis Word-RAM program computing the signed fast Möbius transform in
  `C * ((I.n + 1) * 2 ^ I.n)` instructions.

## References

* [A. Björklund, T. Husfeldt, M. Koivisto, *Set Partitioning via
  Inclusion–Exclusion*][BjorklundHusfeldtKoivisto2009], Section 2.2
* [R. Williams, *Nonuniform ACC Circuit Lower Bounds*][Williams2014], Lemma 4.2
-/

namespace Cslib.Algorithms.WordRAM.Yates

open Cslib.Algorithms.Lean.Yates
open Cslib.BitString
open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization
open Cslib.WordRAM.Realization.Signed
open Finset

/-! ## Problem instances -/

public section

/-- A table of `2 ^ n` natural numbers for the unsigned fast zeta transform. -/
structure NatInstance where
  /-- Number of coordinates `n`. -/
  n : ℕ
  /-- Table entries indexed by `k < 2 ^ n` (`maskSet n k`). -/
  entries : Vector ℕ (2 ^ n)

namespace NatInstance

/-- Flat Word-RAM input `[n] ++ entries.toList`. -/
@[expose] def encode (I : NatInstance) : List ℕ :=
  I.n :: I.entries.toList

/-- Sum of all table entries, bounding every intermediate and final zeta entry. -/
@[expose] def totalSum (I : NatInstance) : ℕ :=
  ∑ k : Fin (2 ^ I.n), I.entries[k.val]

/-- Word-size envelope covering indices, addresses, and all intermediate zeta sums. -/
@[expose] def wordBound (I : NatInstance) : ℕ :=
  4 * (2 ^ I.n + I.totalSum + 16)

/-- Width admissibility predicate for `NatInstance`. -/
abbrev FitsWidth (I : NatInstance) (w : ℕ) : Prop :=
  Fits w I.wordBound

@[simp] theorem length_encode (I : NatInstance) : I.encode.length = 2 ^ I.n + 1 := by
  simp [encode]

/-- Every table entry is bounded by `I.totalSum`. -/
theorem entry_le_totalSum (I : NatInstance) (k : Fin (2 ^ I.n)) :
    I.entries[k.val] ≤ I.totalSum :=
  Finset.single_le_sum (f := fun j : Fin (2 ^ I.n) => I.entries[j.val])
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)

/-- Every width satisfying `I.FitsWidth w` admits the flat input `I.encode`. -/
theorem inputFits (I : NatInstance) {w : ℕ} (hfit : I.FitsWidth w) : InputFits w I.encode := by
  have hpow2 : 1 ≤ 2 ^ I.n := Nat.one_le_two_pow
  refine ⟨hfit.of_le (by simp only [length_encode]; unfold wordBound; omega), ?_⟩
  intro x hx
  simp only [encode, List.mem_cons, Vector.mem_toList_iff] at hx
  rcases hx with rfl | hx
  · exact hfit.of_le (by
      have hn : I.n < 2 ^ I.n := Nat.lt_two_pow_self
      unfold wordBound; omega)
  · obtain ⟨k, hk, rfl⟩ := Vector.mem_iff_getElem.mp hx
    have hle := I.entry_le_totalSum ⟨k, hk⟩
    dsimp only at hle
    exact hfit.of_le (by unfold wordBound; omega)

end NatInstance

/-- A table of `2 ^ n` signed integers for the signed fast zeta and Möbius transforms. -/
structure IntInstance where
  /-- Number of coordinates `n`. -/
  n : ℕ
  /-- Integer table entries indexed by `k < 2 ^ n` (`maskSet n k`). -/
  entries : Vector ℤ (2 ^ n)

namespace IntInstance

/-- Flat Word-RAM input `[n] ++ entries.toList.map Signed.encode`. -/
@[expose] def encode (I : IntInstance) : List ℕ :=
  I.n :: I.entries.toList.map Cslib.WordRAM.Signed.encode

/-- Sum of absolute values of all entries, bounding every intermediate zeta or Möbius entry. -/
@[expose] def sumAbs (I : IntInstance) : ℕ :=
  ∑ k : Fin (2 ^ I.n), I.entries[k.val].natAbs

/-- Word-size envelope covering `Signed.encode` words, intermediate signed operations, indices,
and addresses. -/
@[expose] def wordBound (I : IntInstance) : ℕ :=
  8 * (2 ^ I.n + I.sumAbs + 16)

/-- Width admissibility predicate for `IntInstance`. -/
abbrev FitsWidth (I : IntInstance) (w : ℕ) : Prop :=
  Fits w I.wordBound

@[simp] theorem length_encode (I : IntInstance) : I.encode.length = 2 ^ I.n + 1 := by
  simp [encode]

/-- Every entry's magnitude is bounded by `I.sumAbs`. -/
theorem natAbs_le_sumAbs (I : IntInstance) (k : Fin (2 ^ I.n)) :
    I.entries[k.val].natAbs ≤ I.sumAbs :=
  Finset.single_le_sum (f := fun j : Fin (2 ^ I.n) => I.entries[j.val].natAbs)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)

/-- Every width satisfying `I.FitsWidth w` admits the flat input `I.encode`. -/
theorem inputFits (I : IntInstance) {w : ℕ} (hfit : I.FitsWidth w) : InputFits w I.encode := by
  have hpow2 : 1 ≤ 2 ^ I.n := Nat.one_le_two_pow
  refine ⟨hfit.of_le (by simp only [length_encode]; unfold wordBound; omega), ?_⟩
  intro x hx
  simp only [encode, List.mem_cons, List.mem_map, Vector.mem_toList_iff] at hx
  rcases hx with rfl | ⟨z, hz, rfl⟩
  · have hn : I.n < 2 ^ I.n := Nat.lt_two_pow_self
    exact hfit.of_le (by unfold wordBound; omega)
  · obtain ⟨k, hk, rfl⟩ := Vector.mem_iff_getElem.mp hz
    have h := Cslib.WordRAM.Signed.encode_le_two_mul_add_one
      (z := I.entries[k]) (I.natAbs_le_sumAbs ⟨k, hk⟩)
    exact hfit.of_le (by unfold wordBound; omega)

end IntInstance

end

/-! ## Butterfly index arithmetic -/

private theorem testBit_even_odd_block {i q j : ℕ} (hj : j < 2 ^ i) (r : ℕ) :
    (2 ^ i * (2 * q) + j).testBit r =
        (if r < i then j.testBit r else if r = i then false else q.testBit (r - i - 1)) ∧
      (2 ^ i * (2 * q + 1) + j).testBit r =
        (if r < i then j.testBit r else if r = i then true else q.testBit (r - i - 1)) := by
  rw [Nat.testBit_two_pow_mul_add _ hj, Nat.testBit_two_pow_mul_add _ hj]
  split_ifs with hlt heq
  · exact ⟨rfl, rfl⟩
  · subst heq
    simp [Nat.testBit_zero]
  · have hsucc : r - i = (r - i - 1).succ := by omega
    have hd0 : 2 * q / 2 = q := by omega
    have hd1 : (2 * q + 1) / 2 = q := by omega
    rw [hsucc, Nat.testBit_succ, Nat.testBit_succ, hd0, hd1]
    exact ⟨rfl, rfl⟩

private theorem xor_two_pow_of_block {i q j : ℕ} (hj : j < 2 ^ i) :
    (2 ^ i * (2 * q + 1) + j) ^^^ 2 ^ i = 2 ^ i * (2 * q) + j := by
  refine Nat.eq_of_testBit_eq fun r => ?_
  obtain ⟨heven, hodd⟩ := testBit_even_odd_block hj r
  rw [Nat.testBit_xor, Nat.testBit_two_pow, hodd, heven]
  split_ifs with hlt heq
  · simp [Nat.ne_of_gt hlt]
  · simp [heq]
  · simp [Ne.symm heq]

private def loIdx (step p : ℕ) : ℕ :=
  p + (p / step) * step

private def hiIdx (step p : ℕ) : ℕ :=
  loIdx step p + step

private theorem loIdx_eq_block (step p : ℕ) :
    loIdx step p = step * (2 * (p / step)) + p % step := by
  have hdiv := Nat.div_add_mod p step
  unfold loIdx
  linarith [show step * (2 * (p / step)) = step * (p / step) + (p / step) * step by ring]

private theorem hiIdx_eq_block (step p : ℕ) :
    hiIdx step p = step * (2 * (p / step) + 1) + p % step := by
  unfold hiIdx
  rw [loIdx_eq_block]
  ring

private theorem hiIdx_lt_two_pow {n i p : ℕ} (hi : i < n) (hp : p < 2 ^ (n - 1)) :
    hiIdx (2 ^ i) p < 2 ^ n := by
  have hpos : 0 < 2 ^ i := Nat.two_pow_pos i
  have hpow_half : 2 ^ (n - 1) = 2 ^ i * 2 ^ (n - 1 - i) := by
    rw [← pow_add, show i + (n - 1 - i) = n - 1 by omega]
  have hq : p / 2 ^ i < 2 ^ (n - 1 - i) :=
    Nat.div_lt_of_lt_mul (by rw [← hpow_half]; exact hp)
  have hj : p % 2 ^ i < 2 ^ i := Nat.mod_lt p hpos
  have hpow_full : 2 ^ i * (2 * 2 ^ (n - 1 - i)) = 2 ^ n := by
    calc
      2 ^ i * (2 * 2 ^ (n - 1 - i)) = 2 * (2 ^ i * 2 ^ (n - 1 - i)) := by ring
      _ = 2 * 2 ^ (n - 1) := by rw [← hpow_half]
      _ = 2 ^ n := by rw [← pow_succ', show n - 1 + 1 = n by omega]
  have hblock : 2 ^ i * (2 * (p / 2 ^ i) + 2) ≤ 2 ^ n := by
    rw [← hpow_full]
    exact Nat.mul_le_mul_left _ (by omega)
  rw [hiIdx_eq_block]
  linarith [show 2 ^ i * (2 * (p / 2 ^ i) + 2) = 2 ^ i * (2 * (p / 2 ^ i) + 1) + 2 ^ i by ring]

private theorem loIdx_lt_hiIdx {step : ℕ} (hpos : 0 < step) (p : ℕ) :
    loIdx step p < hiIdx step p := by
  unfold hiIdx
  omega

private theorem loIdx_testBit_false (i p : ℕ) :
    (loIdx (2 ^ i) p).testBit i = false := by
  rw [loIdx_eq_block]
  simpa using (testBit_even_odd_block (q := p / 2 ^ i) (Nat.mod_lt _ (Nat.two_pow_pos i)) i).1

private theorem hiIdx_testBit_true (i p : ℕ) :
    (hiIdx (2 ^ i) p).testBit i = true := by
  rw [hiIdx_eq_block]
  simpa using (testBit_even_odd_block (q := p / 2 ^ i) (Nat.mod_lt _ (Nat.two_pow_pos i)) i).2

private theorem hiIdx_xor_two_pow (i p : ℕ) :
    hiIdx (2 ^ i) p ^^^ 2 ^ i = loIdx (2 ^ i) p := by
  rw [hiIdx_eq_block, loIdx_eq_block]
  exact xor_two_pow_of_block (Nat.mod_lt _ (Nat.two_pow_pos i))

private theorem hiIdx_strictMono (step : ℕ) : StrictMono (hiIdx step) := by
  intro p₁ p₂ hp
  unfold hiIdx loIdx
  have hle : (p₁ / step) * step ≤ (p₂ / step) * step :=
    Nat.mul_le_mul_right step (Nat.div_le_div_right hp.le)
  omega

private theorem exists_hiIdx_iff_testBit {n i m : ℕ} (hi : i < n) (hm : m < 2 ^ n) :
    (∃ p < 2 ^ (n - 1), hiIdx (2 ^ i) p = m) ↔ m.testBit i = true := by
  constructor
  · rintro ⟨p, _, rfl⟩
    exact hiIdx_testBit_true i p
  · intro hbit
    have hpos : 0 < 2 ^ i := Nat.two_pow_pos i
    set b := m / 2 ^ i
    set j := m % 2 ^ i
    have hm_eq : 2 ^ i * b + j = m := Nat.div_add_mod m (2 ^ i)
    have hj : j < 2 ^ i := Nat.mod_lt m hpos
    have hb_odd : b % 2 = 1 := by
      have hb0 := Nat.testBit_two_pow_mul_add b hj i
      rw [hm_eq, hbit] at hb0
      simpa [Nat.testBit_zero] using hb0.symm
    set q := b / 2
    have hb_eq : b = 2 * q + 1 := by omega
    have hpow_half : 2 ^ i * 2 ^ (n - 1 - i) = 2 ^ (n - 1) := by
      rw [← pow_add, show i + (n - 1 - i) = n - 1 by omega]
    have hpow_full : 2 ^ i * (2 * 2 ^ (n - 1 - i)) = 2 ^ n := by
      calc
        2 ^ i * (2 * 2 ^ (n - 1 - i)) = 2 * (2 ^ i * 2 ^ (n - 1 - i)) := by ring
        _ = 2 * 2 ^ (n - 1) := by rw [hpow_half]
        _ = 2 ^ n := by rw [← pow_succ', show n - 1 + 1 = n by omega]
    have hb_lt : b < 2 * 2 ^ (n - 1 - i) :=
      Nat.div_lt_of_lt_mul (by rw [hpow_full]; exact hm)
    have hq_lt : q < 2 ^ (n - 1 - i) := by omega
    refine ⟨2 ^ i * q + j, ?_, ?_⟩
    · have hq1 : 2 ^ i * (q + 1) ≤ 2 ^ (n - 1) := by
        rw [← hpow_half]
        exact Nat.mul_le_mul_left _ hq_lt
      linarith [show 2 ^ i * (q + 1) = 2 ^ i * q + 2 ^ i by ring]
    · have hp_div : (2 ^ i * q + j) / 2 ^ i = q := by
        rw [show 2 ^ i * q + j = j + q * 2 ^ i by ring,
          Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hj, zero_add]
      have hp_mod : (2 ^ i * q + j) % 2 ^ i = j := by
        rw [show 2 ^ i * q + j = j + q * 2 ^ i by ring,
          Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
      rw [hiIdx_eq_block, hp_div, hp_mod, ← hb_eq, hm_eq]

/-! ## `Memory.Prog` butterfly client and `Realizes` certificates -/

private def pow2Step (x : Unit × ℕ) : Memory.Prog ℕ :=
  pure (Prod.snd x + Prod.snd x)

private abbrev Pow2StepSafe (w : ℕ) (x : Unit × ℕ) (_ : Memory.State) : Prop :=
  Fits w (Prod.snd x + Prod.snd x)

private theorem pow2Step_realizes :
    Realizes .exact pow2Step WordEncoding.encode WordEncoding.encode
      Pow2StepSafe (fun _ _ => 0) := by
  unfold pow2Step
  realize
  exact h

private def pow2Prog (n : ℕ) : Memory.Prog ℕ :=
  iterate pow2Step () n 1

private abbrev Pow2ProgSafe (w n : ℕ) (s : Memory.State) : Prop :=
  Fits w 1 ∧ iterationSafe pow2Step Pow2StepSafe w () n 1 s

private theorem pow2Prog_realizes :
    Realizes .exact pow2Prog wordWords wordWords Pow2ProgSafe (fun n _ => n) := by
  unfold pow2Prog
  realize [pow2Step_realizes]
  · exact h.1
  · exact iterationSafe_imp h.2 (fun _ => rfl) (fun _ _ hs => hs)
  · simp only [iterationWork_zero]
    exact le_rfl

private theorem pow2Prog_spec {w : ℕ} (n : ℕ) (s₀ : Memory.State) (hfit : Fits w (2 ^ n)) :
    Pow2ProgSafe w n s₀ ∧
      Memory.FramedTriple w s₀ (pow2Prog n) 0 ∅ fun r t => r = 2 ^ n ∧ t = s₀ := by
  obtain ⟨hsafe, h⟩ := Memory.FramedTriple.iterate (body := pow2Step) (safe := Pow2StepSafe)
    (d := ()) (c := 0) (n := n) (a₀ := 1) (S := ∅) (Q := fun r t => r = 2 ^ n ∧ t = s₀)
    (fun k acc t => acc = 2 ^ k ∧ t = s₀) ⟨rfl, rfl⟩
    (fun k hk acc t ⟨hacc, ht⟩ _ => by
      subst hacc ht
      refine ⟨hfit.of_le ?_, Memory.FramedTriple.pure ⟨?_, rfl⟩⟩
      · rw [← two_mul, ← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) hk
      · change 2 ^ k + 2 ^ k = 2 ^ (k + 1); rw [pow_succ', two_mul])
    fun _ _ h _ => h
  exact ⟨⟨hfit.of_le Nat.one_le_two_pow, hsafe⟩, h.mono (by simp) fun _ _ => id⟩

private structure PassArgs where
  step : ℕ
  half : ℕ

private word_enc_structure encPassArgs : PassArgs where
  step : wordWords, half : wordWords

private instance : WordEncoding PassArgs := ⟨2, encPassArgs⟩

private def passStep (opProg : ℕ × ℕ → Memory.Prog ℕ) (x : PassArgs × ℕ) : Memory.Prog ℕ := do
  let env := Prod.fst x
  let p := Prod.snd x
  let lo := 2 + loIdx env.step p
  let hi := 2 + hiIdx env.step p
  let vHi ← Memory.read hi
  let vLo ← Memory.read lo
  let vNew ← opProg (vHi, vLo)
  Memory.write hi vNew
  pure (p + 1)

private abbrev PassStepSafe (opSafe : ℕ → ℕ × ℕ → Memory.State → Prop)
    (w : ℕ) (x : PassArgs × ℕ) (s : Memory.State) : Prop :=
  let env := Prod.fst x
  let p := Prod.snd x
  let lo := 2 + loIdx env.step p
  let hi := 2 + hiIdx env.step p
  env.step ≠ 0 ∧ Fits w hi ∧ Fits w (p + 1) ∧ opSafe w (s.mem hi, s.mem lo) s

private theorem passStep_realizes {opProg : ℕ × ℕ → Memory.Prog ℕ}
    {opSafe : ℕ → ℕ × ℕ → Memory.State → Prop}
    (hop : Realizes .exact opProg (appendWords wordWords wordWords) wordWords opSafe
      (fun _ _ => 0)) :
    Realizes .exact (passStep opProg) (appendWords encPassArgs wordWords) wordWords
      (PassStepSafe opSafe) (fun _ _ => 0) := by
  unfold passStep hiIdx loIdx
  realize [hop]
  all_goals
    first
    | exact h.1
    | exact h.2.1
    | exact h.2.2.1
    | exact h.2.2.2
    | exact h.2.1.of_le (by
        unfold hiIdx loIdx
        have := Nat.div_mul_le_self d.2 d.1.step
        omega)

private def passProg (opProg : ℕ × ℕ → Memory.Prog ℕ) (a : PassArgs) : Memory.Prog ℕ :=
  iterate (passStep opProg) a a.half 0

private theorem passProg_realizes {opProg : ℕ × ℕ → Memory.Prog ℕ}
    {opSafe : ℕ → ℕ × ℕ → Memory.State → Prop}
    (hop : Realizes .exact opProg (appendWords wordWords wordWords) wordWords opSafe
      (fun _ _ => 0)) :
    Realizes .exact (passProg opProg) encPassArgs wordWords
      (fun w a s => iterationSafe (passStep opProg) (PassStepSafe opSafe) w a a.half 0 s)
      (fun _ _ => 0) := by
  unfold passProg
  realize [passStep_realizes hop]
  exact h

private def outerStep (opProg : ℕ × ℕ → Memory.Prog ℕ) (x : ℕ × ℕ) : Memory.Prog ℕ := do
  let half := Prod.fst x
  let step := Prod.snd x
  let _ ← passProg opProg ⟨step, half⟩
  pure (step + step)

private abbrev OuterStepSafe (opProg : ℕ × ℕ → Memory.Prog ℕ)
    (opSafe : ℕ → ℕ × ℕ → Memory.State → Prop) (w : ℕ) (x : ℕ × ℕ) (s : Memory.State) : Prop :=
  let half := Prod.fst x
  let step := Prod.snd x
  iterationSafe (passStep opProg) (PassStepSafe opSafe) w ⟨step, half⟩ half 0 s ∧
    Fits w (step + step)

private theorem outerStep_realizes {opProg : ℕ × ℕ → Memory.Prog ℕ}
    {opSafe : ℕ → ℕ × ℕ → Memory.State → Prop}
    (hop : Realizes .exact opProg (appendWords wordWords wordWords) wordWords opSafe
      (fun _ _ => 0)) :
    Realizes .exact (outerStep opProg) (appendWords wordWords wordWords) wordWords
      (OuterStepSafe opProg opSafe) (fun _ _ => 0) := by
  unfold outerStep
  realize [passProg_realizes hop]
  all_goals first | exact h.1 | exact h.2

private def butterflyProg (opProg : ℕ × ℕ → Memory.Prog ℕ) (n : ℕ) : Memory.Prog ℕ := do
  let sz ← pow2Prog n
  Memory.write 1 sz
  let _ ← iterate (outerStep opProg) (sz / 2) n 1
  pure 1

private abbrev ButterflyProgSafe (opProg : ℕ × ℕ → Memory.Prog ℕ)
    (opSafe : ℕ → ℕ × ℕ → Memory.State → Prop) (w n : ℕ) (s : Memory.State) : Prop :=
  let sz := (Memory.spec 0).clientResult s (pow2Prog n)
  let s₁ := (Memory.spec 0).clientState s (pow2Prog n)
  let s₂ : Memory.State := ⟨Function.update s₁.mem 1 sz, s₁.frontier⟩
  Fits w 2 ∧ Pow2ProgSafe w n s ∧
    iterationSafe (outerStep opProg) (OuterStepSafe opProg opSafe) w (sz / 2) n 1 s₂

private theorem butterflyProg_realizes {opProg : ℕ × ℕ → Memory.Prog ℕ}
    {opSafe : ℕ → ℕ × ℕ → Memory.State → Prop}
    (hop : Realizes .exact opProg (appendWords wordWords wordWords) wordWords opSafe
      (fun _ _ => 0)) :
    Realizes .exact (butterflyProg opProg) wordWords wordWords
      (ButterflyProgSafe opProg opSafe) (fun n _ => 2 * n) := by
  unfold butterflyProg
  realize [pow2Prog_realizes, outerStep_realizes hop]
  · exact h.2.1
  · exact h.1.of_le (by omega)
  · exact iterationSafe_imp h.2.2 (fun _ => rfl) (fun _ _ hs => ⟨⟨by omega, h.1⟩, hs⟩)
  · simp only [iterationWork_zero]
    omega

/-! ## Semantic invariant and cost bound for `butterflyProg` -/

private def tablePass {α : Type*} {n : ℕ} (op : α → α → α)
    (t : Fin (2 ^ n) → α) (i : Fin n) (k : Fin (2 ^ n)) : α :=
  if k.val.testBit i.val then
    op (t k) (t ⟨k.val ^^^ 2 ^ i.val, Nat.xor_lt_two_pow k.isLt
      (Nat.pow_lt_pow_right (by norm_num) i.isLt)⟩)
  else t k

private theorem tablePass_hom {α β : Type*} {n : ℕ} (f : α → β)
    (op₁ : α → α → α) (op₂ : β → β → β)
    (hop : ∀ x y, op₂ (f x) (f y) = f (op₁ x y))
    (t : Fin (2 ^ n) → α) (i : Fin n) :
    tablePass op₂ (fun k => f (t k)) i = fun k => f (tablePass op₁ t i k) := by
  funext k
  dsimp only [tablePass]
  split_ifs <;> simp [hop]

private theorem passProg_spec {w n : ℕ}
    {opProg : ℕ × ℕ → Memory.Prog ℕ} {opSafe : ℕ → ℕ × ℕ → Memory.State → Prop}
    (opWord : ℕ → ℕ → ℕ)
    (prev : Fin (2 ^ n) → ℕ)
    (i : Fin n)
    (Pval : ℕ → Prop)
    (hop_exec : ∀ (s : Memory.State) (u v : ℕ), Pval u → Pval v →
      opSafe w (u, v) s ∧ Fits w (opWord u v) ∧
        Memory.FramedTriple w s (opProg (u, v)) 0 ∅ fun r t => r = opWord u v ∧ t = s)
    (hP_prev : ∀ k, Pval (prev k))
    (s₀ : Memory.State)
    (hfr : 2 + 2 ^ n ≤ s₀.frontier)
    (hfit_addr : Fits w (2 + 2 ^ n))
    (harr : ∀ k : Fin (2 ^ n), s₀.mem (2 + k.val) = prev k) :
    let a : PassArgs := ⟨2 ^ i.val, 2 ^ (n - 1)⟩
    iterationSafe (passStep opProg) (PassStepSafe opSafe) w a a.half 0 s₀ ∧
      Memory.FramedTriple w s₀ (passProg opProg a) (3 * 2 ^ (n - 1)) {x | 2 ≤ x}
        fun _ t => ∀ k : Fin (2 ^ n), t.mem (2 + k.val) = tablePass opWord prev i k := by
  intro a
  simp only [a]
  let next := tablePass opWord prev i
  refine Memory.FramedTriple.iterate (fun p cur t => cur = p ∧ ∀ k : Fin (2 ^ n),
        t.mem (2 + k.val) = if ∃ r < p, hiIdx (2 ^ i.val) r = k.val then next k else prev k)
    ⟨rfl, fun k => by simpa using harr k⟩ (fun p hp cur s ⟨hcur, hs_arr⟩ ⟨hs_fr, _⟩ => ?_)
    fun _ s' ⟨_, harr'⟩ _ k => ?_
  · subst cur
    have hhi_lt : hiIdx (2 ^ i.val) p < 2 ^ n := hiIdx_lt_two_pow i.isLt hp
    have hlo_lt : loIdx (2 ^ i.val) p < 2 ^ n :=
      lt_trans (loIdx_lt_hiIdx (Nat.two_pow_pos i.val) p) hhi_lt
    let kHi : Fin (2 ^ n) := ⟨hiIdx (2 ^ i.val) p, hhi_lt⟩
    let kLo : Fin (2 ^ n) := ⟨loIdx (2 ^ i.val) p, hlo_lt⟩
    have hnot_hi : ¬∃ r < p, hiIdx (2 ^ i.val) r = kHi.val := by
      rintro ⟨r, hr, heq⟩
      exact Nat.ne_of_lt (hiIdx_strictMono (2 ^ i.val) hr) heq
    have hnot_lo : ¬∃ r < p, hiIdx (2 ^ i.val) r = kLo.val := by
      rintro ⟨r, _, heq⟩
      have hb1 := hiIdx_testBit_true i.val r
      have hb2 := loIdx_testBit_false i.val p
      dsimp only [kLo] at heq
      rw [heq, hb2] at hb1
      cases hb1
    have hmem_hi : s.mem (2 + hiIdx (2 ^ i.val) p) = prev kHi := by
      simpa [kHi, hnot_hi] using hs_arr kHi
    have hmem_lo : s.mem (2 + loIdx (2 ^ i.val) p) = prev kLo := by
      simpa [kLo, hnot_lo] using hs_arr kLo
    obtain ⟨hop_safe, hop_fit, hop⟩ := hop_exec s (s.mem (2 + hiIdx (2 ^ i.val) p))
      (s.mem (2 + loIdx (2 ^ i.val) p)) (hmem_hi ▸ hP_prev kHi) (hmem_lo ▸ hP_prev kLo)
    have hnext_hi : opWord (prev kHi) (prev kLo) = next kHi := by
      dsimp only [next, tablePass]
      rw [ite_eq_left (hiIdx_testBit_true i.val p)]
      have hxor : (⟨kHi.val ^^^ 2 ^ i.val, Nat.xor_lt_two_pow kHi.isLt
          (Nat.pow_lt_pow_right (by norm_num) i.isLt)⟩ : Fin (2 ^ n)) = kLo :=
        Fin.ext (hiIdx_xor_two_pow i.val p)
      rw [hxor]
    have hfit_p1 : Fits w (p + 1) := hfit_addr.of_le (by
      have : 2 ^ (n - 1) ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le n 1)
      omega)
    refine ⟨⟨Nat.ne_of_gt (Nat.two_pow_pos i.val), by region_omega, hfit_p1, hop_safe⟩, ?_⟩
    unfold passStep
    framed_triple
    · refine ⟨rfl, fun k => ?_⟩
      simp only [hmem_hi, hmem_lo, hnext_hi]
      by_cases hk : k = kHi
      · have hex : ∃ r < p + 1, hiIdx (2 ^ i.val) r = k.val := ⟨p, Nat.lt_succ_self p, by rw [hk]⟩
        rw [hk, Function.update_self, ite_eq_left (hk ▸ hex)]
      · have hne_val : k.val ≠ hiIdx (2 ^ i.val) p := fun h => hk (Fin.ext h)
        rw [Function.update_of_ne (by omega), hs_arr k]
        simp only [Nat.exists_lt_succ_right, Ne.symm hne_val, or_false]
  · simp only [harr' k, exists_hiIdx_iff_testBit i.isLt k.isLt]
    by_cases hbit : k.val.testBit i.val = true
    · simp [hbit, next]
    · simp [hbit, next, tablePass]

private theorem butterflyProg_spec {w n : ℕ}
    {opProg : ℕ × ℕ → Memory.Prog ℕ} {opSafe : ℕ → ℕ × ℕ → Memory.State → Prop}
    (opWord : ℕ → ℕ → ℕ)
    (Pval : ℕ → Prop)
    (t₀ : Fin (2 ^ n) → ℕ)
    (hop_exec : ∀ (s : Memory.State) (u v : ℕ), Pval u → Pval v →
      opSafe w (u, v) s ∧ Fits w (opWord u v) ∧
        Memory.FramedTriple w s (opProg (u, v)) 0 ∅ fun r t => r = opWord u v ∧ t = s)
    (hP_fold : ∀ m ≤ n, ∀ k,
      Pval (((List.finRange n).take m).foldl (tablePass opWord) t₀ k))
    (s₀ : Memory.State)
    (hfr : 2 + 2 ^ n ≤ s₀.frontier)
    (hfit_addr : Fits w (2 + 2 ^ n))
    (harr : ∀ k : Fin (2 ^ n), s₀.mem (2 + k.val) = t₀ k) :
    let outWords := List.ofFn ((List.finRange n).foldl (tablePass opWord) t₀)
    ButterflyProgSafe opProg opSafe w n s₀ ∧
      Memory.FramedTriple w s₀ (butterflyProg opProg n) (3 * n * 2 ^ n + 1) {x | 1 ≤ x}
        fun r t => outputList t.mem r = outWords ∧ Fits w (r + outWords.length) := by
  have hfit_2n : Fits w (2 ^ n) := hfit_addr.of_le (Nat.le_add_left _ _)
  have hfit_2 : Fits w 2 := hfit_addr.of_le (Nat.le_add_right _ _)
  obtain ⟨hp_safe, hp⟩ := pow2Prog_spec n s₀ hfit_2n
  let s₂ : Memory.State := ⟨Function.update s₀.mem 1 (2 ^ n), s₀.frontier⟩
  let half := 2 ^ n / 2
  obtain ⟨hit_safe, hloop⟩ := Memory.FramedTriple.iterate (body := outerStep opProg)
    (safe := OuterStepSafe opProg opSafe) (d := half) (n := n) (c := 3 * 2 ^ (n - 1)) (a₀ := 1)
    (s := s₂) (S := {x | 2 ≤ x}) (Q := fun _ t => t.mem 1 = 2 ^ n ∧
      ∀ k : Fin (2 ^ n), t.mem (2 + k.val) = (List.finRange n).foldl (tablePass opWord) t₀ k)
    (fun i step t => step = 2 ^ i ∧ ∀ k : Fin (2 ^ n),
      t.mem (2 + k.val) = ((List.finRange n).take i).foldl (tablePass opWord) t₀ k)
    ⟨rfl, fun k => (Function.update_of_ne (by omega) _ _).trans (harr k)⟩
    (fun i hi step s ⟨hstep_eq, hs_arr⟩ ⟨hs_fr, _⟩ => by
      subst hstep_eq
      have hhalf : half = 2 ^ (n - 1) := by
        simpa only [pow_one] using Nat.pow_div (show 1 ≤ n by omega) (show 0 < 2 by norm_num)
      obtain ⟨hpass_safe, hpass⟩ := passProg_spec (w := w) opWord _ ⟨i, hi⟩ Pval hop_exec
        (fun k => hP_fold i (Nat.le_of_lt hi) k) s (by dsimp only [s₂] at hs_fr; omega)
        hfit_addr hs_arr
      have hfit_step2 : Fits w (2 ^ i + 2 ^ i) := hfit_2n.of_le (by
        rw [← two_mul, ← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) hi)
      refine ⟨by simpa only [OuterStepSafe, hhalf] using And.intro hpass_safe hfit_step2, ?_⟩
      simp only [outerStep, hhalf]
      refine (Memory.FramedTriple.call hpass subset_rfl fun _ t hs' _ =>
        Memory.FramedTriple.pure (c := 0) ⟨by ring, fun k => ?_⟩).mono (Nat.add_zero _).le
          fun _ _ => id
      rw [hs' k, List.take_succ_finRange hi, List.foldl_append]
      rfl)
    fun _ t ⟨_, hs'⟩ ⟨_, hframe⟩ =>
      ⟨(hframe 1 (by dsimp only [s₂]; omega) (by simp)).trans
        (Function.update_self 1 (2 ^ n) s₀.mem), fun k => by
          rw [hs' k, List.take_of_length_le (by simp)]⟩
  have hp_post := hp.post
  rw [clientResult_width, clientState_width] at hp_post
  refine ⟨⟨hfit_2, hp_safe, by simpa only [hp_post.1, hp_post.2, half, s₂] using hit_safe⟩, ?_⟩
  have h2le : 2 ^ (n - 1) ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le n 1)
  have hmul : 3 * 2 ^ (n - 1) * n ≤ 3 * n * 2 ^ n :=
    (Nat.mul_right_comm 3 _ n).trans_le (Nat.mul_le_mul_left _ h2le)
  unfold butterflyProg
  refine (Memory.FramedTriple.call_eq hp (Set.empty_subset _)
    (Memory.FramedTriple.write_bind_of_mem (by omega) hfit_2n (by simp)
      (Memory.FramedTriple.call hloop (fun x hx => by region_omega) fun _ t h _ =>
        Memory.FramedTriple.pure (c := 0) ⟨?_, ?_⟩))).mono (by omega) fun _ _ => id
  · rw [outputList_eq_iff]
    refine ⟨by simp [h.1], fun k => ?_⟩
    have hk_lt : k.val < 2 ^ n := by simpa using k.isLt
    change t.mem (1 + 1 + k.val) =
      (List.ofFn ((List.finRange n).foldl (tablePass opWord) t₀))[k.val]
    rw [show 1 + 1 + k.val = 2 + k.val by omega, List.getElem_ofFn, h.2 ⟨k.val, hk_lt⟩]
  · rw [List.length_ofFn]
    exact hfit_addr.of_le (by omega)

/-! ## Pure Yates intermediate-value bounds -/

private theorem foldl_yatesPass_eq_of_fn {M R : Type*} [AddCommMonoid M] [Monoid R]
    [DistribMulAction R M] {n : ℕ} (c : R) (f₀ : Finset (Fin n) → M) :
    ∀ (l : List (Fin n)) (k : Fin (2 ^ n)),
      (l.foldl (tablePass (fun a b => a + c • b)) (fun m => f₀ (maskSet n m.val))) k =
      yatesTransform c l f₀ (maskSet n k.val)
  | [], _ => rfl
  | i :: l, k => by
    simp only [List.foldl_cons, yatesTransform_cons]
    have hstep : tablePass (fun a b => a + c • b) (fun m => f₀ (maskSet n m.val)) i =
        fun m : Fin (2 ^ n) => yatesPass c i f₀ (maskSet n m.val) := by
      funext m
      simp only [tablePass, yatesPass, mem_maskSet]
      split_ifs with hm
      · rw [maskSet_xor_two_pow hm]
      · rfl
    rw [hstep]
    exact foldl_yatesPass_eq_of_fn c (yatesPass c i f₀) l k

private theorem injOn_maskIndex_sdiff {n k : ℕ} (A : Finset (Fin n)) :
    Set.InjOn (fun U : Finset (Fin n) => maskIndex (maskSet n k \ U))
      ↑(maskSet n k ∩ A).powerset := by
  intro U₁ hU₁ U₂ hU₂ hEq
  have hU₁S : U₁ ⊆ maskSet n k := (Finset.mem_powerset.mp hU₁).trans Finset.inter_subset_left
  have hU₂S : U₂ ⊆ maskSet n k := (Finset.mem_powerset.mp hU₂).trans Finset.inter_subset_left
  have hset : maskSet n k \ U₁ = maskSet n k \ U₂ := by
    have := congrArg (fun x => maskSet n x.val) hEq
    simpa [maskSet_maskIndex] using this
  calc
    U₁ = maskSet n k \ (maskSet n k \ U₁) := (Finset.sdiff_sdiff_eq_self hU₁S).symm
    _ = maskSet n k \ (maskSet n k \ U₂) := by rw [hset]
    _ = U₂ := Finset.sdiff_sdiff_eq_self hU₂S

private theorem nat_yatesTransform_le (I : NatInstance) {l : List (Fin I.n)} (hl : l.Nodup)
    (k : Fin (2 ^ I.n)) :
    yatesTransform (1 : ℕ) l (fun S => I.entries[(maskIndex S).val]) (maskSet I.n k.val) ≤
      I.totalSum := by
  rw [yatesTransform_apply (1 : ℕ) hl]
  simp only [one_pow, one_smul]
  let φ : Finset (Fin I.n) → Fin (2 ^ I.n) := fun U => maskIndex (maskSet I.n k.val \ U)
  have hinj := injOn_maskIndex_sdiff (k := k.val) l.toFinset
  calc
    ∑ U ∈ (maskSet I.n k.val ∩ l.toFinset).powerset, I.entries[(φ U).val]
        ≤ ∑ m : Fin (2 ^ I.n), I.entries[m.val] := by
          rw [← Finset.sum_image (f := fun m : Fin (2 ^ I.n) => I.entries[m.val])
            (fun _ h₁ _ h₂ => hinj h₁ h₂)]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun _ _ _ => Nat.zero_le _)
    _ = I.totalSum := rfl

private theorem int_yatesTransform_natAbs_le (I : IntInstance) (c : ℤ) (hc : c.natAbs = 1)
    {l : List (Fin I.n)} (hl : l.Nodup) (k : Fin (2 ^ I.n)) :
    (yatesTransform c l (fun S => I.entries[(maskIndex S).val]) (maskSet I.n k.val)).natAbs ≤
      I.sumAbs := by
  rw [yatesTransform_apply c hl]
  let φ : Finset (Fin I.n) → Fin (2 ^ I.n) := fun U => maskIndex (maskSet I.n k.val \ U)
  have hinj := injOn_maskIndex_sdiff (k := k.val) l.toFinset
  have htri : (∑ U ∈ (maskSet I.n k.val ∩ l.toFinset).powerset,
        c ^ #U • I.entries[(φ U).val]).natAbs ≤
      ∑ U ∈ (maskSet I.n k.val ∩ l.toFinset).powerset, I.entries[(φ U).val].natAbs := by
    refine (Int.natAbs_sum_le _ _).trans (Finset.sum_le_sum fun U _ => ?_)
    rw [smul_eq_mul, Int.natAbs_mul, Int.natAbs_pow, hc, one_pow, one_mul]
  calc
    (∑ U ∈ (maskSet I.n k.val ∩ l.toFinset).powerset, c ^ #U • I.entries[(φ U).val]).natAbs
        ≤ ∑ U ∈ (maskSet I.n k.val ∩ l.toFinset).powerset, I.entries[(φ U).val].natAbs := htri
    _ ≤ ∑ m : Fin (2 ^ I.n), I.entries[m.val].natAbs := by
        rw [← Finset.sum_image (f := fun m : Fin (2 ^ I.n) => I.entries[m.val].natAbs)
          (fun _ h₁ _ h₂ => hinj h₁ h₂)]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => Nat.zero_le _)
    _ = I.sumAbs := rfl

private theorem foldl_nat_eq_zeta (I : NatInstance) :
    List.ofFn ((List.finRange I.n).foldl (tablePass (· + ·))
      (fun m : Fin (2 ^ I.n) => I.entries[m.val])) =
      (Cslib.Algorithms.Lean.Yates.zeta I.entries).toList := by
  refine List.ext_getElem (by simp) fun k hk _ => ?_
  have hk' : k < 2 ^ I.n := by simpa using hk
  rw [List.getElem_ofFn, Vector.getElem_toList]
  have heq := foldl_yatesPass_eq_of_fn (1 : ℕ) (fun S => I.entries[(maskIndex S).val])
    (List.finRange I.n) ⟨k, hk'⟩
  simp only [one_smul] at heq
  have hbase : (fun m : Fin (2 ^ I.n) => I.entries[(maskIndex (maskSet I.n m.val)).val]) =
      fun m : Fin (2 ^ I.n) => I.entries[m.val] := by
    funext m; simp
  rw [hbase] at heq
  rw [heq, yatesTransform_one_apply (List.nodup_finRange I.n) _ (by simp),
    ← getElem_zeta I.entries (fun S => I.entries[(maskIndex S).val])
      (getElem_eq_maskIndex_maskSet I.entries) k hk']

private def signedTableOp (c : ℤ) (wa wb : ℕ) : ℕ :=
  Cslib.WordRAM.Signed.encode
    (Cslib.WordRAM.Signed.decode wa + c * Cslib.WordRAM.Signed.decode wb)

private theorem foldl_int_yatesPass_eq {n : ℕ} (c : ℤ) (F₀ : Finset (Fin n) → ℤ)
    (l : List (Fin n)) (k : Fin (2 ^ n)) :
    (l.foldl (tablePass (signedTableOp c))
      (fun m => Cslib.WordRAM.Signed.encode (F₀ (maskSet n m.val)))) k =
      Cslib.WordRAM.Signed.encode (yatesTransform c l F₀ (maskSet n k.val)) := by
  have hhom := List.foldl_hom
    (fun (t : Fin (2 ^ n) → ℤ) m => Cslib.WordRAM.Signed.encode (t m))
    (g₁ := tablePass (fun a b : ℤ => a + c • b))
    (g₂ := tablePass (signedTableOp c))
    (l := l) (init := fun m => F₀ (maskSet n m.val))
    fun t i => tablePass_hom Cslib.WordRAM.Signed.encode _ _
      (fun x y => by simp [signedTableOp, Cslib.WordRAM.Signed.decode_encode]) t i
  exact (congrFun hhom k).trans
    (congrArg Cslib.WordRAM.Signed.encode (foldl_yatesPass_eq_of_fn c F₀ l k))

private theorem foldl_int_eq_transform (I : IntInstance) (c : ℤ) (hc : c = 1 ∨ c = -1) :
    List.ofFn ((List.finRange I.n).foldl (tablePass (signedTableOp c))
      (fun m : Fin (2 ^ I.n) => Cslib.WordRAM.Signed.encode I.entries[m.val])) =
      (if c = 1 then Cslib.Algorithms.Lean.Yates.zeta I.entries
       else Cslib.Algorithms.Lean.Yates.mobius I.entries).toList.map
        Cslib.WordRAM.Signed.encode := by
  have h0 : (fun m : Fin (2 ^ I.n) => Cslib.WordRAM.Signed.encode I.entries[m.val]) =
      fun m => Cslib.WordRAM.Signed.encode (I.entries[(maskIndex (maskSet I.n m.val)).val]) := by
    funext m; simp
  rcases hc with rfl | rfl
  · simp only [↓reduceIte]
    refine List.ext_getElem (by simp) fun k hk _ => ?_
    have hk' : k < 2 ^ I.n := by simpa using hk
    rw [List.getElem_ofFn, List.getElem_map, Vector.getElem_toList]
    have hlift := foldl_int_yatesPass_eq (1 : ℤ) (fun S => I.entries[(maskIndex S).val])
      (List.finRange I.n) ⟨k, hk'⟩
    rw [← h0] at hlift
    rw [hlift]
    congr 1
    rw [yatesTransform_apply_of_subset (1 : ℤ) (List.nodup_finRange I.n) _ (by simp)]
    simp only [one_pow, one_smul]
    rw [getElem_zeta I.entries (fun S => I.entries[(maskIndex S).val])
      (getElem_eq_maskIndex_maskSet I.entries) k hk', subsetZeta]
  · simp only [show (-1 : ℤ) ≠ 1 by decide, ↓reduceIte]
    refine List.ext_getElem (by simp) fun k hk _ => ?_
    have hk' : k < 2 ^ I.n := by simpa using hk
    rw [List.getElem_ofFn, List.getElem_map, Vector.getElem_toList]
    have hlift := foldl_int_yatesPass_eq (-1 : ℤ) (fun S => I.entries[(maskIndex S).val])
      (List.finRange I.n) ⟨k, hk'⟩
    rw [← h0] at hlift
    rw [hlift]
    congr 1
    rw [yatesTransform_neg_one_apply (List.nodup_finRange I.n) _ (by simp),
      ← getElem_mobius I.entries (fun S => I.entries[(maskIndex S).val])
        (getElem_eq_maskIndex_maskSet I.entries) k hk']

/-! ## Lifting to deterministic standard-basis `Program .standard` -/

private theorem exists_yates_program_of_spec {Inst : Type}
    {opProg : ℕ × ℕ → Memory.Prog ℕ} {opSafe : ℕ → ℕ × ℕ → Memory.State → Prop}
    (hop : Realizes .exact opProg (appendWords wordWords wordWords) wordWords opSafe
      (fun _ _ => 0))
    (nOf : Inst → ℕ) (encode : Inst → List ℕ) (FitsW : Inst → ℕ → Prop)
    (expected : Inst → List ℕ)
    (hlayout : ∀ I, (encode I).getD 0 0 = nOf I)
    (hlen : ∀ I, 1 ≤ (encode I).length)
    (hfit_len : ∀ I {w}, FitsW I w → Fits w ((encode I).length + 1))
    (hspec : ∀ (I : Inst) {w : ℕ}, FitsW I w →
      ButterflyProgSafe opProg opSafe w (nOf I) (Memory.State.init (encode I)) ∧
        Memory.FramedTriple w (Memory.State.init (encode I)) (butterflyProg opProg (nOf I))
          (3 * nOf I * 2 ^ nOf I + 1) {x | 1 ≤ x} fun r t =>
            outputList t.mem r = expected I ∧ Fits w (r + (expected I).length)) :
    ∃ r C : ℕ, ∃ prog : Program .standard r, ¬prog.ReadsWidth ∧ prog.IsRandFree ∧
      prog.ComputesListInTime (fun _ I => encode I)
        (fun I _ => C * ((nOf I + 1) * 2 ^ nOf I)) FitsW expected := by
  obtain ⟨r, C₁, pc, prog₀, hnw₀, frontier, _, he⟩ :=
    (butterflyProg_realizes hop).exists_standard_basis_init_program_state_from_words (0 : Fin 1)
  refine ⟨r, 5 * C₁ + 1, stripRand prog₀, not_readsWidth_stripRand hnw₀,
    isRandFree_stripRand prog₀, fun I w hfw hin_fits => ?_⟩
  have hs := hspec I hfw
  obtain ⟨y, m, hruns, hhalt, hmem, _, hsteps⟩ :=
    he w (nOf I) (encode I)
      (by rintro ⟨_ | _, hj⟩; exacts [hlayout I, by omega])
      (hlen I) (hfit_len I hfw) hin_fits hs.1 hs.2.validHistory
  dsimp only [wordWords] at hhalt
  have hymem : y.mem = ((Memory.spec w).clientState (Memory.State.init (encode I))
      (butterflyProg opProg (nOf I))).mem := congrArg Memory.State.mem hmem
  refine ⟨m + 1, ⟨⟨pc, y⟩, m, _, runs_stripRand hruns, step_stripRand_of_halt hhalt,
    hymem ▸ hs.2.post.1, hs.2.post.2, rfl⟩, ?_⟩
  have hmc := (framedTriple_iff_realization.mp hs.2).2.1
  have hpow1 : 1 ≤ 2 ^ nOf I := Nat.one_le_two_pow
  have hn_le : nOf I ≤ nOf I * 2 ^ nOf I := Nat.le_mul_of_pos_right _ hpow1
  have hpos : 1 ≤ (nOf I + 1) * 2 ^ nOf I := by nlinarith
  have hbudget :
      memoryCost (butterflyProg opProg (nOf I)) (Memory.State.init (encode I)) +
        2 * nOf I + 1 ≤ 5 * ((nOf I + 1) * 2 ^ nOf I) := by
    nlinarith [hmc, hpow1, hn_le]
  have hmul :
      C₁ * (memoryCost (butterflyProg opProg (nOf I)) (Memory.State.init (encode I)) +
        2 * nOf I + 1) ≤ C₁ * (5 * ((nOf I + 1) * 2 ^ nOf I)) :=
    Nat.mul_le_mul_left C₁ hbudget
  have hring : C₁ * (5 * ((nOf I + 1) * 2 ^ nOf I)) + (nOf I + 1) * 2 ^ nOf I =
      (5 * C₁ + 1) * ((nOf I + 1) * 2 ^ nOf I) := by ring
  linarith only [hsteps, hmul, hpos, hring]

private def natAddProg (d : ℕ × ℕ) : Memory.Prog ℕ :=
  pure (Prod.fst d + Prod.snd d)

private theorem natAddProg_realizes :
    Realizes .exact natAddProg (appendWords wordWords wordWords) wordWords
      (fun w d _ => Fits w (Prod.fst d + Prod.snd d)) (fun _ _ => 0) := by
  unfold natAddProg
  realize
  exact h

private theorem init_mem_entry {xs : List ℕ} (n : ℕ) (hxs : xs.length = 2 ^ n)
    (k : Fin (2 ^ n)) :
    (Memory.State.init (n :: xs)).mem (2 + k.val) = xs[k.val]'(by omega) := by
  unfold Memory.State.init
  dsimp only
  rw [show 2 + k.val = (k.val + 1) + 1 by omega, Data.init_mem_succ, List.getD_cons_succ,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  rfl

/-! ## Public running-time theorems -/

public section

/-- **Unsigned fast zeta transform on the word RAM (`O((n + 1) · 2 ^ n)`).** There is a uniform
width-blind deterministic standard-basis program (`Program .standard r`, `¬prog.ReadsWidth`,
`prog.IsRandFree`) that computes `(Yates.zeta I.entries).toList` on input `I.encode` within
`C * ((I.n + 1) * 2 ^ I.n)` instructions (`Program.ComputesListInTime`) at every word width `w`
satisfying `I.FitsWidth w`. -/
theorem exists_zetaNat_program :
    ∃ r C : ℕ, ∃ prog : Program .standard r, ¬prog.ReadsWidth ∧ prog.IsRandFree ∧
      prog.ComputesListInTime (fun _ I => I.encode) (fun I _ => C * ((I.n + 1) * 2 ^ I.n))
        NatInstance.FitsWidth (fun I => (Cslib.Algorithms.Lean.Yates.zeta I.entries).toList) := by
  refine exists_yates_program_of_spec natAddProg_realizes NatInstance.n NatInstance.encode
    NatInstance.FitsWidth (fun I => (Cslib.Algorithms.Lean.Yates.zeta I.entries).toList)
    (fun _ => rfl) (fun I => by simp [NatInstance.encode])
    (fun I {w} hfit => by
      have := Nat.one_le_two_pow (n := I.n)
      exact hfit.of_le (by
        simp only [NatInstance.length_encode]
        unfold NatInstance.wordBound; omega))
    fun I {w} hfit => ?_
  let t₀ : Fin (2 ^ I.n) → ℕ := fun m => I.entries[m.val]
  have hP_fold : ∀ m ≤ I.n, ∀ k,
      ((List.finRange I.n).take m).foldl (tablePass (· + ·)) t₀ k ≤ I.totalSum := by
    intro m _ k
    have heq := foldl_yatesPass_eq_of_fn (1 : ℕ) (fun S => I.entries[(maskIndex S).val])
      ((List.finRange I.n).take m) k
    simp only [one_smul] at heq
    have hbase :
        (fun x : Fin (2 ^ I.n) => I.entries[(maskIndex (maskSet I.n x.val)).val]) = t₀ := by
      funext x; simp [t₀]
    rw [hbase] at heq
    rw [heq]
    exact nat_yatesTransform_le I ((List.nodup_finRange I.n).take) k
  have hbf := butterflyProg_spec (w := w) (n := I.n) (opProg := natAddProg)
    (opSafe := fun w d _ => Fits w (Prod.fst d + Prod.snd d))
    (· + ·) (fun v => v ≤ I.totalSum) t₀
    (fun s u v hu hv => by
      have hfit_uv : Fits w (u + v) := hfit.of_le (by
        have := Nat.one_le_two_pow (n := I.n)
        unfold NatInstance.wordBound; omega)
      exact ⟨hfit_uv, hfit_uv, Memory.FramedTriple.pure ⟨rfl, rfl⟩⟩)
    hP_fold (Memory.State.init I.encode)
    (by simp only [Memory.State.init, NatInstance.length_encode]; omega)
    (hfit.of_le (by unfold NatInstance.wordBound; omega))
    (fun k => by
      have hk := init_mem_entry I.n (xs := I.entries.toList) (by simp) k
      simpa only [NatInstance.encode, t₀, Vector.getElem_toList] using hk)
  rwa [foldl_nat_eq_zeta I] at hbf

end

private theorem signed_butterfly_spec (isMobius : Bool) (I : IntInstance) {w : ℕ}
    (hfit : I.FitsWidth w) :
    let opProg := if isMobius then signedSubProg else signedAddProg
    let opSafe : ℕ → ℕ × ℕ → Memory.State → Prop :=
      if isMobius then
        fun w d _ => Fits w 2 ∧ Fits w (Prod.snd d + 1) ∧
          Fits w (2 * (Prod.fst d / 2 + Prod.snd d / 2) + 1)
      else
        fun w d _ => Fits w 2 ∧ Fits w (2 * (Prod.fst d / 2 + Prod.snd d / 2) + 1)
    let s₀ := Memory.State.init I.encode
    let expected := (if isMobius then Cslib.Algorithms.Lean.Yates.mobius I.entries
      else Cslib.Algorithms.Lean.Yates.zeta I.entries).toList.map Cslib.WordRAM.Signed.encode
    ButterflyProgSafe opProg opSafe w I.n s₀ ∧
      Memory.FramedTriple w s₀ (butterflyProg opProg I.n) (3 * I.n * 2 ^ I.n + 1) {x | 1 ≤ x}
        fun r t => outputList t.mem r = expected ∧ Fits w (r + expected.length) := by
  let opProg := if isMobius then signedSubProg else signedAddProg
  let opSafe : ℕ → ℕ × ℕ → Memory.State → Prop :=
    if isMobius then
      fun w d _ => Fits w 2 ∧ Fits w (Prod.snd d + 1) ∧
        Fits w (2 * (Prod.fst d / 2 + Prod.snd d / 2) + 1)
    else
      fun w d _ => Fits w 2 ∧ Fits w (2 * (Prod.fst d / 2 + Prod.snd d / 2) + 1)
  let c : ℤ := if isMobius then -1 else 1
  have hc_abs : c.natAbs = 1 := by cases isMobius <;> simp [c]
  let t₀ : Fin (2 ^ I.n) → ℕ := fun m => Cslib.WordRAM.Signed.encode I.entries[m.val]
  let Pval (u : ℕ) : Prop := ∃ z : ℤ, z.natAbs ≤ I.sumAbs ∧ u = Cslib.WordRAM.Signed.encode z
  have hP_fold : ∀ m ≤ I.n, ∀ k,
      Pval (((List.finRange I.n).take m).foldl (tablePass (signedTableOp c)) t₀ k) := by
    intro m _ k
    have h0 : t₀ = fun x => Cslib.WordRAM.Signed.encode
        (I.entries[(maskIndex (maskSet I.n x.val)).val]) := by
      funext x; simp [t₀]
    have hlift := foldl_int_yatesPass_eq c (fun S => I.entries[(maskIndex S).val])
      ((List.finRange I.n).take m) k
    rw [← h0] at hlift
    exact ⟨_, int_yatesTransform_natAbs_le I c hc_abs ((List.nodup_finRange I.n).take) k, hlift⟩
  have hfit_2 : Fits w 2 := hfit.of_le (by
    have := Nat.one_le_two_pow (n := I.n)
    unfold IntInstance.wordBound; omega)
  have hop_exec : ∀ (s : Memory.State) (u v : ℕ), Pval u → Pval v →
      opSafe w (u, v) s ∧ Fits w (signedTableOp c u v) ∧
        Memory.FramedTriple w s (opProg (u, v)) 0 ∅ fun r t =>
          r = signedTableOp c u v ∧ t = s := by
    intro s u v ⟨za, hza, hu⟩ ⟨zb, hzb, hv⟩
    subst hu; subst hv
    have hpow2 : 1 ≤ 2 ^ I.n := Nat.one_le_two_pow
    have hdiv : 2 * (Cslib.WordRAM.Signed.encode za / 2 +
        Cslib.WordRAM.Signed.encode zb / 2) + 1 ≤ I.wordBound := by
      simp only [Cslib.WordRAM.Signed.encode_div_two]
      unfold IntInstance.wordBound; omega
    have hop_w : signedTableOp c (Cslib.WordRAM.Signed.encode za) (Cslib.WordRAM.Signed.encode zb) =
        Cslib.WordRAM.Signed.encode (za + c * zb) := by
      simp [signedTableOp, Cslib.WordRAM.Signed.decode_encode]
    have hfit_res : Fits w (signedTableOp c (Cslib.WordRAM.Signed.encode za)
        (Cslib.WordRAM.Signed.encode zb)) := by
      rw [hop_w]
      have hcb : (c * zb).natAbs = zb.natAbs := by rw [Int.natAbs_mul, hc_abs, one_mul]
      have hab : (za + c * zb).natAbs ≤ za.natAbs + zb.natAbs := by
        have := Int.natAbs_add_le za (c * zb); omega
      have henc := Cslib.WordRAM.Signed.encode_le_two_mul_add_one hab
      exact hfit.of_le (by unfold IntInstance.wordBound; omega)
    cases isMobius
    · dsimp only [opProg, opSafe, Bool.false_eq_true, ↓reduceIte]
      exact ⟨⟨hfit_2, hfit.of_le hdiv⟩, hfit_res, framedTriple_iff_realization.mpr
        ⟨validHistory_signedAddProg w s _, (memoryCost_signedAddProg _ s).le,
          (congrArg (Memory.Modifies ∅ s) (clientState_signedAddProg s _)).mpr (.refl ∅ s),
          (clientResult_signedAddProg s za zb).trans (by simpa [c] using hop_w.symm),
          clientState_signedAddProg s _⟩⟩
    · dsimp only [opProg, opSafe, ↓reduceIte]
      have hb1 : Cslib.WordRAM.Signed.encode zb + 1 ≤ I.wordBound := by
        have := Cslib.WordRAM.Signed.encode_le_two_mul_add_one hzb
        unfold IntInstance.wordBound; omega
      exact ⟨⟨hfit_2, hfit.of_le hb1, hfit.of_le hdiv⟩, hfit_res, framedTriple_iff_realization.mpr
        ⟨validHistory_signedSubProg w s _, (memoryCost_signedSubProg _ s).le,
          (congrArg (Memory.Modifies ∅ s) (clientState_signedSubProg s _)).mpr (.refl ∅ s),
          (clientResult_signedSubProg s za zb).trans (by
            simpa [c, sub_eq_add_neg] using hop_w.symm), clientState_signedSubProg s _⟩⟩
  have hlist : List.ofFn ((List.finRange I.n).foldl (tablePass (signedTableOp c)) t₀) =
      (if isMobius then Cslib.Algorithms.Lean.Yates.mobius I.entries
       else Cslib.Algorithms.Lean.Yates.zeta I.entries).toList.map
        Cslib.WordRAM.Signed.encode := by
    cases isMobius
    · have h1 := foldl_int_eq_transform I 1 (Or.inl rfl)
      simp only [↓reduceIte] at h1
      simpa only [Bool.false_eq_true, ↓reduceIte, c, t₀] using h1
    · have h1 := foldl_int_eq_transform I (-1) (Or.inr rfl)
      simp only [show (-1 : ℤ) ≠ 1 by decide, ↓reduceIte] at h1
      simpa only [↓reduceIte, c, t₀] using h1
  have hbf := butterflyProg_spec (w := w) (n := I.n) (opProg := opProg) (opSafe := opSafe)
    (signedTableOp c) Pval t₀ hop_exec hP_fold (Memory.State.init I.encode)
    (by simp only [Memory.State.init, IntInstance.length_encode]; omega)
    (hfit.of_le (by unfold IntInstance.wordBound; omega))
    (fun k => by
      have hk := init_mem_entry I.n (xs := I.entries.toList.map Cslib.WordRAM.Signed.encode)
        (by simp) k
      simpa [IntInstance.encode, t₀] using hk)
  rwa [hlist] at hbf

public section

/-- **Signed fast zeta transform on the word RAM (`O((n + 1) · 2 ^ n)`).** There is a uniform
width-blind deterministic standard-basis program (`Program .standard r`, `¬prog.ReadsWidth`,
`prog.IsRandFree`) that computes `(Yates.zeta I.entries).toList.map Signed.encode` on input
`I.encode` within `C * ((I.n + 1) * 2 ^ I.n)` instructions (`Program.ComputesListInTime`) at every
word width `w` satisfying `I.FitsWidth w`. -/
theorem exists_zetaInt_program :
    ∃ r C : ℕ, ∃ prog : Program .standard r, ¬prog.ReadsWidth ∧ prog.IsRandFree ∧
      prog.ComputesListInTime (fun _ I => I.encode) (fun I _ => C * ((I.n + 1) * 2 ^ I.n))
        IntInstance.FitsWidth
        (fun I => (Cslib.Algorithms.Lean.Yates.zeta I.entries).toList.map
          Cslib.WordRAM.Signed.encode) :=
  exists_yates_program_of_spec signedAddProg_realizes IntInstance.n IntInstance.encode
    IntInstance.FitsWidth
    (fun I => (Cslib.Algorithms.Lean.Yates.zeta I.entries).toList.map Cslib.WordRAM.Signed.encode)
    (fun _ => rfl) (fun I => by simp [IntInstance.encode])
    (fun I {w} hfit => by
      have := Nat.one_le_two_pow (n := I.n)
      exact hfit.of_le (by
        simp only [IntInstance.length_encode]
        unfold IntInstance.wordBound; omega))
    (fun I {_} hfit => signed_butterfly_spec false I hfit)

/-- **Signed fast Möbius transform on the word RAM (`O((n + 1) · 2 ^ n)`).** There is a uniform
width-blind deterministic standard-basis program (`Program .standard r`, `¬prog.ReadsWidth`,
`prog.IsRandFree`) that computes `(Yates.mobius I.entries).toList.map Signed.encode` on input
`I.encode` within `C * ((I.n + 1) * 2 ^ I.n)` instructions (`Program.ComputesListInTime`) at every
word width `w` satisfying `I.FitsWidth w`. -/
theorem exists_mobiusInt_program :
    ∃ r C : ℕ, ∃ prog : Program .standard r, ¬prog.ReadsWidth ∧ prog.IsRandFree ∧
      prog.ComputesListInTime (fun _ I => I.encode) (fun I _ => C * ((I.n + 1) * 2 ^ I.n))
        IntInstance.FitsWidth
        (fun I => (Cslib.Algorithms.Lean.Yates.mobius I.entries).toList.map
          Cslib.WordRAM.Signed.encode) :=
  exists_yates_program_of_spec signedSubProg_realizes IntInstance.n IntInstance.encode
    IntInstance.FitsWidth
    (fun I => (Cslib.Algorithms.Lean.Yates.mobius I.entries).toList.map
      Cslib.WordRAM.Signed.encode)
    (fun _ => rfl) (fun I => by simp [IntInstance.encode])
    (fun I {w} hfit => by
      have := Nat.one_le_two_pow (n := I.n)
      exact hfit.of_le (by
        simp only [IntInstance.length_encode]
        unfold IntInstance.wordBound; omega))
    (fun I {_} hfit => signed_butterfly_spec true I hfit)

end

end Cslib.Algorithms.WordRAM.Yates
