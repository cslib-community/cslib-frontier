/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.TSP.HamiltonianCount
public import CslibFrontier.Computability.WordRAM.Function
public import CslibFrontier.Computability.WordRAM.Realization.Program.Standard
import CslibFrontier.Computability.WordRAM.InputArray
import CslibFrontier.Computability.WordRAM.Realization.ProgFrame
import CslibFrontier.Computability.WordRAM.Realization.Structure
import CslibFrontier.DataStructure.StateTransition
import CslibFrontier.Foundations.Data.Matrix.PairChunks
import CslibFrontier.Foundations.Data.Nat.Bitwise.Carry
import CslibFrontier.Tactic.Realize
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Karp–Bax inclusion–exclusion Hamiltonian path counting on the word RAM

Checked standard-basis word-RAM (`Cslib.WordRAM.Basis.standard`) realization of Karp and Bax's
inclusion–exclusion Hamiltonian-path counter (`CslibFrontier.Algorithms.Lean.TSP.HamiltonianCount`)
[Karp1982] [Bax1993] ([FominKratsch2010], Section 4.2.2, Theorem 4.5 and Eq. (4.4)), built as a
`Cslib.DataStructure.Memory.Prog` client certified via `Cslib.Tactic.Realize` (`realize`) and
lowered along `Realizes.exists_standard_basis_init_program_state_from_words`:

* **`program`**: given an `n`-vertex directed graph `I : Instance` encoded as `I.n` followed by
  the `n × n` row-major adjacency matrix (`0`/`1` words), computes `#(hamPaths I.adj)` in
  `O((I.n ^ 3 + 1) * 2 ^ I.n)` instructions at every width `w` with `I.FitsWidth w`.
* **`decideProgram`**: decides `(hamPaths I.adj).Nonempty` (returning `1` or `0`) within the same
  `O((I.n ^ 3 + 1) * 2 ^ I.n)` instruction bound.

Subsets `S ⊆ Fin n` are enumerated in place using an `n`-word binary odometer `inMask[0..n-1]`
and parity bit `maskParity = #S % 2`, allocating `3 * n` working words (`inMask`, `cur`, `next`)
via `Memory.allocDirty`. Neither program reads the machine word size (`¬ReadsWidth`).

## Word-size condition

During every mask `k < 2 ^ n` and round `r < n`, every entry `walkCountFrom I.adj S r u` is at
most `n ^ r`, so `totalWalkCount I.adj S ≤ (n + 1) ^ n` and both partial sums `evenSum` and
`oddSum` stay at most `2 ^ n * (n + 1) ^ n`. The envelope
`I.wordBound = 4 * (2 ^ I.n * (I.n + 1) ^ I.n + (I.n + 1) ^ 2 + 16)` (requiring `O(n log n)`-bit
words, matching [FominKratsch2010], Section 4.2.2) covers the input, all working addresses, and all
accumulated walk counts.

## Main definitions

* `Cslib.Algorithms.WordRAM.HamiltonianCount.Instance`: directed graph instance and flat
  word-RAM encoding (`Instance.encode`, `Instance.wordBound`, `Instance.FitsWidth`).
* `Cslib.Algorithms.WordRAM.HamiltonianCount.program`: deterministic width-blind standard-basis
  Word-RAM program counting Hamiltonian paths.
* `Cslib.Algorithms.WordRAM.HamiltonianCount.decideProgram`: deterministic width-blind
  standard-basis Word-RAM program deciding existence of a Hamiltonian path.

## Main results

* `Cslib.Algorithms.WordRAM.HamiltonianCount.not_readsWidth_program`,
  `Cslib.Algorithms.WordRAM.HamiltonianCount.not_readsWidth_decideProgram`: width-blindness.
* `Cslib.Algorithms.WordRAM.HamiltonianCount.computesInTime_program`,
  `Cslib.Algorithms.WordRAM.HamiltonianCount.computesInTime_decideProgram`:
  `O((I.n ^ 3 + 1) * 2 ^ I.n)` instruction bounds for counting and deciding Hamiltonian paths.

## References

* [E. T. Bax, *Inclusion and exclusion algorithm for the Hamiltonian path problem*][Bax1993]
* [F. V. Fomin and D. Kratsch, *Exact Exponential Algorithms*][FominKratsch2010], Section 4.2.2
* [R. M. Karp, *Dynamic programming meets the principle of inclusion and exclusion*][Karp1982]
-/

public section

namespace Cslib.Algorithms.WordRAM.HamiltonianCount

open Cslib.Algorithms.Lean.TSP
open Cslib.Algorithms.Lean.Yates
open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization
open Finset

attribute [local client_simps] StateTransitionSpec.clientState
  StateTransitionSpec.runClient_pure'
  runClient_read runClient_write runClient_allocDirty runClient_ite
  prog_clientState_ite

private def finPrefSum {n : ℕ} (f : Fin n → ℕ) (k : ℕ) : ℕ :=
  ∑ v : Fin n, if v.1 < k then f v else 0

private theorem finPrefSum_zero {n : ℕ} (f : Fin n → ℕ) : finPrefSum f 0 = 0 := by
  simp [finPrefSum]

private theorem finPrefSum_eq_sum {n : ℕ} (f : Fin n → ℕ) :
    finPrefSum f n = ∑ v : Fin n, f v :=
  Finset.sum_congr rfl fun v _ => by simp [v.isLt]

private theorem finPrefSum_mono {n : ℕ} (f : Fin n → ℕ) {k₁ k₂ : ℕ} (h : k₁ ≤ k₂) :
    finPrefSum f k₁ ≤ finPrefSum f k₂ := by
  refine Finset.sum_le_sum fun v _ => ?_
  split_ifs <;> first | exact le_rfl | exact Nat.zero_le _ | omega

private theorem finPrefSum_succ {n : ℕ} (f : Fin n → ℕ) {k : ℕ} (hk : k < n) :
    finPrefSum f (k + 1) = finPrefSum f k + f ⟨k, hk⟩ := by
  have hsplit : ∀ v : Fin n,
      (if v.1 < k + 1 then f v else 0) =
        (if v.1 < k then f v else 0) + (if v = ⟨k, hk⟩ then f v else 0) := fun v => by
    rcases lt_trichotomy v.1 k with hlt | heq | hgt
    · have hne : v ≠ ⟨k, hk⟩ := fun h => by
        have := congrArg Fin.val h; dsimp at this; omega
      simp [hlt, hlt.trans (Nat.lt_succ_self k), hne]
    · have hv : v = ⟨k, hk⟩ := Fin.ext heq
      subst hv
      simp
    · have hne : v ≠ ⟨k, hk⟩ := fun h => by
        have := congrArg Fin.val h; dsimp at this; omega
      simp [hne, show ¬ v.1 < k by omega, show ¬ v.1 < k + 1 by omega]
  simp only [finPrefSum, hsplit, Finset.sum_add_distrib]
  congr 1
  simp

private theorem totalWalkCount_zero_vertices {n : ℕ} (hn : n = 0)
    (adj : Fin n → Fin n → Bool) (S : Finset (Fin n)) : totalWalkCount adj S = 1 := by
  subst hn
  rfl

private theorem totalWalkCount_succ_vertices {n : ℕ} (hn : 0 < n)
    (adj : Fin n → Fin n → Bool) (S : Finset (Fin n)) :
    (∑ u : Fin n, walkCountFrom adj S (n - 1) u) = totalWalkCount adj S := by
  cases n with
  | zero => omega
  | succ m => rfl

/-! ## Encoded instances and walk-count bounds -/

/-- A directed graph on `Fin n` given by its boolean adjacency matrix. -/
structure Instance where
  /-- Number of vertices `n`. -/
  n : ℕ
  /-- Adjacency predicate `adj u v = true` when `(u, v)` is an arc. -/
  adj : Fin n → Fin n → Bool

namespace Instance

/-- Flat Word-RAM input `[n] ++ rowMajor adj`. -/
@[expose] def encode (I : Instance) : List ℕ :=
  I.n :: (List.finRange I.n).flatMap fun u =>
    List.ofFn fun v => if I.adj u v then 1 else 0

/-- Word-size envelope covering the input matrix, `O(n²)` working addresses, and `n^n`-scale walk
counts accumulated across `2 ^ n` subsets. -/
@[expose] def wordBound (I : Instance) : ℕ :=
  4 * (2 ^ I.n * (I.n + 1) ^ I.n + (I.n + 1) ^ 2 + 16)

/-- Width admissibility predicate for `Instance`. -/
abbrev FitsWidth (I : Instance) (w : ℕ) : Prop :=
  Fits w I.wordBound

private theorem one_le_word_prod (n : ℕ) : 1 ≤ 2 ^ n * (n + 1) ^ n :=
  Nat.mul_pos Nat.one_le_two_pow (Nat.one_le_pow _ _ (by omega))

@[simp] theorem length_encode (I : Instance) : I.encode.length = I.n * I.n + 1 := by
  simp [encode, List.length_flatMap]

theorem inputFits (I : Instance) {w : ℕ} (hfit : I.FitsWidth w) : InputFits w I.encode := by
  have h1 := one_le_word_prod I.n
  rw [Instance.encode, ← List.singleton_append]
  simp only [List.ofFn_eq_map]
  exact InputFits.flatMap_finRange [I.n] (fun u v => if I.adj u v then 1 else 0)
    (hfit.of_le (by simp only [List.length_singleton]; unfold wordBound; nlinarith))
    (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx
      exact hfit.of_le (by unfold wordBound; nlinarith))
    (fun _ _ => by
      split_ifs
      · exact hfit.of_le (by unfold wordBound; nlinarith)
      · exact fits_zero w)

private theorem init_mem_n (I : Instance) : (Memory.State.init I.encode).mem 1 = I.n := rfl

private theorem init_mem_adj (I : Instance) (u v : Fin I.n) :
    (Memory.State.init I.encode).mem (2 + u.1 * I.n + v.1) = if I.adj u v then 1 else 0 := by
  change (Data.init (r := 0) I.encode).mem (2 + u.1 * I.n + v.1) = _
  rw [show (2 : ℕ) + u.1 * I.n + v.1 = [I.n].length + 1 + (u.1 * I.n + v.1) by simp [Nat.add_assoc],
    Instance.encode, ← List.singleton_append]
  simp only [List.ofFn_eq_map]
  exact Data.init_mem_flatMap_finRange [I.n] (fun u' v' => if I.adj u' v' then 1 else 0) u v

private theorem init_frontier (I : Instance) :
    (Memory.State.init I.encode).frontier = I.n * I.n + 2 := by
  simp [Memory.State.init, length_encode]

end Instance

private theorem walkCountFrom_le_pow {n : ℕ} (adj : Fin n → Fin n → Bool) (S : Finset (Fin n))
    (r : ℕ) (u : Fin n) : walkCountFrom adj S r u ≤ n ^ r := by
  induction r generalizing u with
  | zero =>
    simp only [walkCountFrom, pow_zero]
    split_ifs <;> omega
  | succ r ih =>
    rw [walkCountFrom, pow_succ']
    calc
      ∑ v : Fin n, (if u ∈ S ∧ adj u v then walkCountFrom adj S r v else 0)
          ≤ ∑ _v : Fin n, n ^ r := by
            refine Finset.sum_le_sum fun v _ => ?_
            split_ifs
            · exact ih v
            · exact Nat.zero_le _
      _ = n * n ^ r := by simp

private theorem totalWalkCount_le {n : ℕ} (adj : Fin n → Fin n → Bool) (S : Finset (Fin n)) :
    totalWalkCount adj S ≤ (n + 1) ^ n := by
  cases n with
  | zero => simp [totalWalkCount]
  | succ m =>
    rw [totalWalkCount]
    calc
      ∑ u : Fin (m + 1), walkCountFrom adj S m u
          ≤ ∑ _u : Fin (m + 1), (m + 1) ^ m :=
            Finset.sum_le_sum fun u _ => walkCountFrom_le_pow adj S m u
      _ = (m + 1) * (m + 1) ^ m := by simp
      _ = (m + 1) ^ (m + 1) := by rw [← pow_succ']
      _ ≤ (m + 2) ^ (m + 1) := Nat.pow_le_pow_left (by omega) _

/-! ## Pure binary odometer and inclusion–exclusion lemmas -/

private theorem card_maskSet_succ_prefix_mod {n k t : ℕ}
    (h1 : ∀ j < t, k.testBit j = true)
    (h0 : t = n ∨ (t < n ∧ k.testBit t = false)) :
    (maskSet n (k + 1)).card % 2 =
      ((maskSet n k).card + if t = n then n else t + 1) % 2 := by
  rcases h0 with htn | ⟨htn, h0t⟩
  · subst htn
    have hfull : maskSet t k = Finset.univ := by
      ext u; simp [mem_maskSet, h1 u.1 u.isLt]
    have hempty : maskSet t (k + 1) = ∅ := by
      ext u
      simp only [mem_maskSet, Finset.notMem_empty, iff_false]
      rw [Nat.testBit_add_one_eq_ite_forall]
      have hall : ∀ j < u.1, k.testBit j = true := fun j hj => h1 j (hj.trans u.isLt)
      rw [ite_eq_left hall]
      simp [h1 u.1 u.isLt]
    rw [hempty, hfull, Finset.card_empty, Finset.card_univ, Fintype.card_fin]
    simp [← two_mul]
  · have hsplit : (maskSet n (k + 1)).card + t = (maskSet n k).card + 1 := by
      let tFin : Fin n := ⟨t, htn⟩
      let S1 : Finset (Fin n) := Finset.Iio tFin
      have ht_not : tFin ∉ maskSet n k := by simp [mem_maskSet, h0t, tFin]
      have hS1_sub : S1 ⊆ maskSet n k := fun u hu => by
        simp only [S1, Finset.mem_Iio, Fin.lt_def, tFin] at hu
        exact mem_maskSet.2 (h1 u.1 hu)
      have hS1_card : S1.card = t := Fin.card_Iio tFin
      have hset_eq : maskSet n (k + 1) = insert tFin (maskSet n k \ S1) := by
        ext u
        simp only [Finset.mem_insert, Finset.mem_sdiff, mem_maskSet, S1, Finset.mem_Iio,
          Nat.testBit_add_one_of_lowest h0t h1]
        rcases lt_trichotomy u.1 t with hlt | heq | hgt
        · have hne : u ≠ tFin := fun h => by
            have := congrArg Fin.val h; dsimp [tFin] at this; omega
          have hltF : u < tFin := Fin.lt_def.2 hlt
          simp [hlt.le, hltF, hne, h1 u.1 hlt]
        · have hu_eq : u = tFin := Fin.ext heq
          subst hu_eq
          simp [tFin, h0t]
        · have hne : u ≠ tFin := fun h => by
            have := congrArg Fin.val h; dsimp [tFin] at this; omega
          have hnot : ¬ u < tFin := fun h => by
            have := Fin.lt_def.1 h; dsimp [tFin] at this; omega
          simp [hne, hnot, show ¬ u.1 ≤ t by omega]
      have ht_not_diff : tFin ∉ maskSet n k \ S1 := fun h => ht_not (Finset.mem_sdiff.1 h).1
      rw [hset_eq, Finset.card_insert_of_notMem ht_not_diff, Finset.card_sdiff_of_subset hS1_sub,
        hS1_card]
      have hle : t ≤ (maskSet n k).card := hS1_card ▸ Finset.card_le_card hS1_sub
      omega
    have hif : (if t = n then n else t + 1) = t + 1 := ite_eq_right htn.ne
    rw [hif]
    have h2 : (maskSet n (k + 1)).card + 2 * t = (maskSet n k).card + (t + 1) := by omega
    rw [← h2, Nat.add_mul_mod_self_left]

private def evenPart (I : Instance) (m : ℕ) : ℕ :=
  ∑ j ∈ Finset.range m,
    if (maskSet I.n j).card % 2 = I.n % 2 then totalWalkCount I.adj (maskSet I.n j) else 0

private def oddPart (I : Instance) (m : ℕ) : ℕ :=
  ∑ j ∈ Finset.range m,
    if (maskSet I.n j).card % 2 ≠ I.n % 2 then totalWalkCount I.adj (maskSet I.n j) else 0

private theorem evenPart_succ (I : Instance) (k : ℕ) :
    evenPart I (k + 1) = evenPart I k +
      if (maskSet I.n k).card % 2 = I.n % 2 then totalWalkCount I.adj (maskSet I.n k) else 0 :=
  Finset.sum_range_succ _ k

private theorem oddPart_succ (I : Instance) (k : ℕ) :
    oddPart I (k + 1) = oddPart I k +
      if (maskSet I.n k).card % 2 ≠ I.n % 2 then totalWalkCount I.adj (maskSet I.n k) else 0 :=
  Finset.sum_range_succ _ k

private theorem part_le_mul (I : Instance) {m : ℕ} (hm : m ≤ 2 ^ I.n) :
    evenPart I m ≤ 2 ^ I.n * (I.n + 1) ^ I.n ∧ oddPart I m ≤ 2 ^ I.n * (I.n + 1) ^ I.n := by
  have hbound : ∀ (p : ℕ → Prop) [DecidablePred p],
      ∑ j ∈ Finset.range m, (if p j then totalWalkCount I.adj (maskSet I.n j) else 0) ≤
        2 ^ I.n * (I.n + 1) ^ I.n := fun p _ => by
    calc ∑ j ∈ Finset.range m, (if p j then totalWalkCount I.adj (maskSet I.n j) else 0)
        ≤ ∑ _j ∈ Finset.range m, (I.n + 1) ^ I.n := by
          refine Finset.sum_le_sum fun j _ => ?_
          split_ifs
          · exact totalWalkCount_le I.adj _
          · exact Nat.zero_le _
      _ = m * (I.n + 1) ^ I.n := by simp
      _ ≤ 2 ^ I.n * (I.n + 1) ^ I.n := Nat.mul_le_mul_right _ hm
  exact ⟨hbound _, hbound _⟩

private theorem evenPart_sub_oddPart (I : Instance) :
    (evenPart I (2 ^ I.n) : ℤ) - (oddPart I (2 ^ I.n) : ℤ) = #(hamPaths I.adj) := by
  have hcast : ∀ (m : ℕ), (evenPart I m : ℤ) - (oddPart I m : ℤ) =
      ∑ j ∈ Finset.range m,
        (-1 : ℤ) ^ (I.n - (maskSet I.n j).card) * (totalWalkCount I.adj (maskSet I.n j) : ℤ) := by
    intro m
    induction m with
    | zero => simp [evenPart, oddPart]
    | succ m ih =>
      rw [evenPart_succ, oddPart_succ, Finset.sum_range_succ]
      push_cast
      have hcard_le : (maskSet I.n m).card ≤ I.n := by
        simpa [Fintype.card_fin] using Finset.card_le_univ (maskSet I.n m)
      have hpar : ((-1 : ℤ) ^ (I.n - (maskSet I.n m).card)) =
          if (maskSet I.n m).card % 2 = I.n % 2 then 1 else -1 := by
        have hdiff : Even (I.n - (maskSet I.n m).card) ↔ (maskSet I.n m).card % 2 = I.n % 2 := by
          rw [Nat.even_iff]
          omega
        by_cases hp : (maskSet I.n m).card % 2 = I.n % 2
        · simp [hp, (hdiff.2 hp).neg_one_pow]
        · have hodd : Odd (I.n - (maskSet I.n m).card) := by
            rw [Nat.odd_iff]
            have : ¬ Even (I.n - (maskSet I.n m).card) := fun h => hp (hdiff.1 h)
            rw [Nat.even_iff] at this
            omega
          simp [hp, hodd.neg_one_pow]
      by_cases hp : (maskSet I.n m).card % 2 = I.n % 2
      · simp only [hp, ↓reduceIte, ne_eq, not_true_eq_false] at hpar ⊢
        rw [hpar, one_mul]
        omega
      · simp only [hp, ↓reduceIte, ne_eq, not_false_eq_true] at hpar ⊢
        rw [hpar]
        omega
  rw [hcast, ← countHamPaths_eq I.adj, countHamPaths, fin_foldl_eq_sum]
  have hsum_fin :
      (∑ k : Fin (2 ^ I.n),
        (-1 : ℤ) ^ (I.n - maskCard I.n k) * (subsetWalks I.adj k : ℤ)) =
      ∑ k : Fin (2 ^ I.n),
        (-1 : ℤ) ^ (I.n - (maskSet I.n k.1).card) *
          (totalWalkCount I.adj (maskSet I.n k.1) : ℤ) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [maskCard_eq_card_maskSet, subsetWalks_eq]
  rw [hsum_fin, Finset.sum_range]

private theorem oddPart_le_evenPart (I : Instance) :
    oddPart I (2 ^ I.n) ≤ evenPart I (2 ^ I.n) := by
  have h := evenPart_sub_oddPart I
  omega

private theorem evenPart_sub_oddPart_nat (I : Instance) :
    evenPart I (2 ^ I.n) - oddPart I (2 ^ I.n) = #(hamPaths I.adj) := by
  have h := evenPart_sub_oddPart I
  omega

/-! ## Word-size envelope arithmetic helpers -/

private theorem n_le_wordBound (I : Instance) : I.n ≤ I.wordBound := by
  have h1 := Instance.one_le_word_prod I.n
  unfold Instance.wordBound
  nlinarith

private theorem sq_add_three_n_add_two_le_wordBound (I : Instance) :
    I.n * I.n + 2 + 3 * I.n ≤ I.wordBound := by
  have h1 := Instance.one_le_word_prod I.n
  unfold Instance.wordBound
  nlinarith

private theorem totalWalkCount_le_wordBound (I : Instance) (S : Finset (Fin I.n)) :
    totalWalkCount I.adj S ≤ I.wordBound := by
  have hle := totalWalkCount_le I.adj S
  have hpow : (I.n + 1) ^ I.n ≤ 2 ^ I.n * (I.n + 1) ^ I.n :=
    Nat.le_mul_of_pos_left _ Nat.one_le_two_pow
  unfold Instance.wordBound
  omega

private theorem walkCountFrom_le_wordBound (I : Instance) (S : Finset (Fin I.n))
    {r : ℕ} (hr : r ≤ I.n) (u : Fin I.n) :
    walkCountFrom I.adj S r u ≤ I.wordBound := by
  have hle := walkCountFrom_le_pow I.adj S r u
  have hpow : I.n ^ r ≤ (I.n + 1) ^ I.n :=
    (Nat.pow_le_pow_left (Nat.le_succ _) r).trans
      (Nat.pow_le_pow_right (Nat.succ_pos _) hr)
  have hprod : (I.n + 1) ^ I.n ≤ 2 ^ I.n * (I.n + 1) ^ I.n :=
    Nat.le_mul_of_pos_left _ Nat.one_le_two_pow
  unfold Instance.wordBound
  omega

/-! ## Memory client sub-programs and `realize` certificates -/

-- 1. Zeroing a slice `base[0..len-1]`

private structure ZeroArgs where
  base : ℕ
  len : ℕ

private word_enc_structure encZeroArgs : ZeroArgs where
  base : wordWords, len : wordWords

private instance : WordEncoding ZeroArgs := ⟨2, encZeroArgs⟩

private def zeroStep (x : ZeroArgs × ℕ) : Memory.Prog ℕ := do
  let env := Prod.fst x
  let i := Prod.snd x
  Memory.write (env.base + i) 0
  pure (i + 1)

private abbrev ZeroStepSafe (w : ℕ) (x : ZeroArgs × ℕ) (_ : Memory.State) : Prop :=
  Fits w (Prod.fst x).base ∧ Fits w ((Prod.fst x).base + Prod.snd x) ∧ Fits w (Prod.snd x + 1)

private theorem zeroStep_realizes :
    Realizes .exact zeroStep (appendWords encZeroArgs wordWords) wordWords
      ZeroStepSafe (fun _ _ => 0) := by
  unfold zeroStep
  realize
  all_goals
    obtain ⟨hb, hbi, hi⟩ := h
    first | exact hbi | exact hi

private def zeroWordsProg (a : ZeroArgs) : Memory.Prog ℕ :=
  iterate zeroStep a a.len 0

private theorem zeroWordsProg_realizes :
    Realizes .exact zeroWordsProg encZeroArgs wordWords
      (fun w a s => iterationSafe zeroStep ZeroStepSafe w a a.len 0 s)
      (fun _ _ => 0) := by
  unfold zeroWordsProg
  realize [zeroStep_realizes]
  exact h

private theorem zeroWordsProg_spec {w : ℕ} (a : ZeroArgs) (s₀ : Memory.State)
    (hbound : a.base + a.len ≤ s₀.frontier)
    (hfit : Fits w (a.base + a.len)) :
    iterationSafe zeroStep ZeroStepSafe w a a.len 0 s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (zeroWordsProg a)) ∧
      memoryCost (zeroWordsProg a) s₀ ≤ a.len ∧
      ((Memory.spec 0).clientState s₀ (zeroWordsProg a)).frontier = s₀.frontier ∧
      (∀ x, ¬ (a.base ≤ x ∧ x < a.base + a.len) →
        ((Memory.spec 0).clientState s₀ (zeroWordsProg a)).mem x = s₀.mem x) ∧
      ∀ i < a.len, ((Memory.spec 0).clientState s₀ (zeroWordsProg a)).mem (a.base + i) = 0 := by
  have hspec := iterate_spec zeroStep ZeroStepSafe w a 1 a.len
    (fun k idx s => idx = k ∧ s.frontier = s₀.frontier ∧
      (∀ i < k, s.mem (a.base + i) = 0))
    (fun x => a.base ≤ x ∧ x < a.base + a.len)
    (fun k hk idx s ⟨hidx, hfr, hpre⟩ => by
      have haddr : a.base + k < s.frontier := by omega
      have hfb : Fits w a.base := hfit.of_le (by omega)
      have hfbi : Fits w (a.base + k) := hfit.of_le (by omega)
      have hfi : Fits w (k + 1) := hfit.of_le (by omega)
      refine ⟨⟨hfb, hidx ▸ hfbi, hidx ▸ hfi⟩, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hidx]
        exact validHistory_write_bind haddr (fits_zero w) (validHistory_pure w _ _)
      · simp only [zeroStep, memoryCost_bind', memoryCost_write, memoryCost_pure, add_zero,
          le_refl]
      · simp [zeroStep, client_simps, hfr]
      · intro x hx
        have hupd : Function.update s.mem (a.base + k) 0 x = s.mem x :=
          Function.update_of_ne (by omega) 0 s.mem
        simp [zeroStep, client_simps, hidx, hupd]
      · refine ⟨?_, ?_, ?_⟩
        · simp [zeroStep, client_simps, hidx]
        · simp [zeroStep, client_simps, hfr]
        · intro i hi
          by_cases hik : i = k
          · subst hik
            simp [zeroStep, client_simps, hidx]
          · have hupd : Function.update s.mem (a.base + k) 0 (a.base + i) = s.mem (a.base + i) :=
              Function.update_of_ne (by omega) 0 s.mem
            simp [zeroStep, client_simps, hidx, hupd, hpre i (by omega)])
    0 s₀ ⟨rfl, rfl, fun i hi => by omega⟩
  exact ⟨hspec.1, hspec.2.1, by simpa only [zeroWordsProg, one_mul] using hspec.2.2.1,
    hspec.2.2.2.1, hspec.2.2.2.2.1, hspec.2.2.2.2.2.2.2⟩

-- 2. Copying a slice `src[0..len-1] → dst[0..len-1]`

private structure CopyArgs where
  src : ℕ
  dst : ℕ
  len : ℕ

private word_enc_structure encCopyArgs : CopyArgs where
  src : wordWords, dst : wordWords, len : wordWords

private instance : WordEncoding CopyArgs := ⟨3, encCopyArgs⟩

private def copyStep (x : CopyArgs × ℕ) : Memory.Prog ℕ := do
  let env := Prod.fst x
  let i := Prod.snd x
  let v ← Memory.read (env.src + i)
  Memory.write (env.dst + i) v
  pure (i + 1)

private abbrev CopyStepSafe (w : ℕ) (x : CopyArgs × ℕ) (s : Memory.State) : Prop :=
  let env := Prod.fst x
  let i := Prod.snd x
  Fits w (env.src + i) ∧ Fits w (env.dst + i) ∧ Fits w (i + 1) ∧ Fits w (s.mem (env.src + i))

private theorem copyStep_realizes :
    Realizes .exact copyStep (appendWords encCopyArgs wordWords) wordWords
      CopyStepSafe (fun _ _ => 0) := by
  unfold copyStep
  realize
  all_goals
    obtain ⟨hs, hd, hi, hv⟩ := h
    first | exact hs | exact hd | exact hi

private def copySliceProg (a : CopyArgs) : Memory.Prog ℕ :=
  iterate copyStep a a.len 0

private theorem copySliceProg_realizes :
    Realizes .exact copySliceProg encCopyArgs wordWords
      (fun w a s => iterationSafe copyStep CopyStepSafe w a a.len 0 s)
      (fun _ _ => 0) := by
  unfold copySliceProg
  realize [copyStep_realizes]
  exact h

private theorem copySliceProg_spec {w : ℕ} (a : CopyArgs) (s₀ : Memory.State)
    (hdisj : ∀ i < a.len, ∀ j < a.len, a.dst + i ≠ a.src + j)
    (hsrc_lt : a.src + a.len ≤ s₀.frontier) (hdst_lt : a.dst + a.len ≤ s₀.frontier)
    (hfit_s : Fits w (a.src + a.len)) (hfit_d : Fits w (a.dst + a.len))
    (hfit_vals : ∀ i < a.len, Fits w (s₀.mem (a.src + i))) :
    iterationSafe copyStep CopyStepSafe w a a.len 0 s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (copySliceProg a)) ∧
      memoryCost (copySliceProg a) s₀ ≤ 2 * a.len ∧
      ((Memory.spec 0).clientState s₀ (copySliceProg a)).frontier = s₀.frontier ∧
      (∀ x, ¬ (a.dst ≤ x ∧ x < a.dst + a.len) →
        ((Memory.spec 0).clientState s₀ (copySliceProg a)).mem x = s₀.mem x) ∧
      ∀ i < a.len,
        ((Memory.spec 0).clientState s₀ (copySliceProg a)).mem (a.dst + i) =
          s₀.mem (a.src + i) := by
  have hspec := iterate_spec copyStep CopyStepSafe w a 2 a.len
    (fun k idx s => idx = k ∧ s.frontier = s₀.frontier ∧
      (∀ i < a.len, s.mem (a.src + i) = s₀.mem (a.src + i)) ∧
      (∀ i < k, s.mem (a.dst + i) = s₀.mem (a.src + i)))
    (fun x => a.dst ≤ x ∧ x < a.dst + a.len)
    (fun k hk idx s ⟨hidx, hfr, hsrc_eq, hpre⟩ => by
      have has : a.src + k < s.frontier := by omega
      have had : a.dst + k < s.frontier := by omega
      have hval_k : s.mem (a.src + k) = s₀.mem (a.src + k) := hsrc_eq k hk
      have hfv : Fits w (s.mem (a.src + k)) := hval_k ▸ hfit_vals k hk
      have hfs_k : Fits w (a.src + k) := hfit_s.of_le (by omega)
      have hfd_k : Fits w (a.dst + k) := hfit_d.of_le (by omega)
      have hfk1 : Fits w (k + 1) := hfit_d.of_le (by omega)
      refine ⟨⟨hidx ▸ hfs_k, hidx ▸ hfd_k, hidx ▸ hfk1, hidx ▸ hfv⟩, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hidx]
        exact validHistory_read_bind has
          (validHistory_write_bind had hfv (validHistory_pure w _ _))
      · simp only [copyStep, memoryCost_bind', memoryCost_read, memoryCost_write,
          memoryCost_pure, add_zero, clientResult_read, le_refl]
      · simp [copyStep, client_simps, hfr]
      · intro x hx
        have hupd : Function.update s.mem (a.dst + k) (s.mem (a.src + k)) x = s.mem x :=
          Function.update_of_ne (by omega) _ s.mem
        simp [copyStep, client_simps, hidx, hupd]
      · refine ⟨?_, ?_, ?_, ?_⟩
        · simp [copyStep, client_simps, hidx]
        · simp [copyStep, client_simps, hfr]
        · intro i hi
          have hupd : Function.update s.mem (a.dst + k) (s.mem (a.src + k)) (a.src + i) =
              s.mem (a.src + i) :=
            Function.update_of_ne (hdisj k hk i hi).symm _ s.mem
          simp [copyStep, client_simps, hidx, hupd, hsrc_eq i hi]
        · intro i hi
          by_cases hik : i = k
          · subst hik
            simp [copyStep, client_simps, hidx, hval_k]
          · have hupd : Function.update s.mem (a.dst + k) (s.mem (a.src + k)) (a.dst + i) =
                s.mem (a.dst + i) :=
              Function.update_of_ne (by omega) _ s.mem
            simp [copyStep, client_simps, hidx, hupd, hpre i (by omega)])
    0 s₀ ⟨rfl, rfl, fun _ _ => rfl, fun i hi => by omega⟩
  exact ⟨hspec.1, hspec.2.1, by simpa only [copySliceProg] using hspec.2.2.1,
    hspec.2.2.2.1, hspec.2.2.2.2.1, hspec.2.2.2.2.2.2.2.2⟩

-- 3. Inner matrix-vector dot step `stepInnerProg`

private structure StepInnerArgs where
  n : ℕ
  u : ℕ
  curBase : ℕ

private word_enc_structure encStepInnerArgs : StepInnerArgs where
  n : wordWords, u : wordWords, curBase : wordWords

private instance : WordEncoding StepInnerArgs := ⟨3, encStepInnerArgs⟩

private structure StepInnerState where
  v : ℕ
  acc : ℕ

private word_enc_structure encStepInnerState : StepInnerState where
  v : wordWords, acc : wordWords

private instance : WordEncoding StepInnerState := ⟨2, encStepInnerState⟩

private def stepInnerStep (x : StepInnerArgs × StepInnerState) : Memory.Prog StepInnerState := do
  let env := Prod.fst x
  let st := Prod.snd x
  let a ← Memory.read (2 + env.u * env.n + st.v)
  if a = 1 then
    let c ← Memory.read (env.curBase + st.v)
    pure ⟨st.v + 1, st.acc + c⟩
  else
    pure ⟨st.v + 1, st.acc⟩

private abbrev StepInnerSafe (w : ℕ) (x : StepInnerArgs × StepInnerState)
    (s : Memory.State) : Prop :=
  let env := Prod.fst x
  let st := Prod.snd x
  Fits w 1 ∧ Fits w (2 + env.u * env.n + st.v) ∧ Fits w (env.curBase + st.v) ∧
    Fits w (st.v + 1) ∧
    (s.mem (2 + env.u * env.n + st.v) = 1 → Fits w (st.acc + s.mem (env.curBase + st.v)))

private theorem stepInnerStep_realizes :
    Realizes .exact stepInnerStep (appendWords encStepInnerArgs encStepInnerState)
      encStepInnerState StepInnerSafe (fun _ _ => 0) := by
  unfold stepInnerStep
  realize
  all_goals
    obtain ⟨h1, hadj, hcur, hv, hacc⟩ := h
    first
    | exact h1
    | exact hadj
    | exact hcur
    | exact hv
    | exact hacc (by assumption)

private def stepInnerProg (a : StepInnerArgs) : Memory.Prog ℕ :=
  StepInnerState.acc <$> iterate stepInnerStep a a.n ⟨0, 0⟩

private theorem stepInnerProg_realizes :
    Realizes .exact stepInnerProg encStepInnerArgs wordWords
      (fun w a s => iterationSafe stepInnerStep StepInnerSafe w a a.n ⟨0, 0⟩ s)
      (fun _ _ => 0) := by
  unfold stepInnerProg
  realize [stepInnerStep_realizes]
  exact h

private theorem stepInnerProg_spec {w : ℕ} (I : Instance) (hfit : I.FitsWidth w)
    (u : Fin I.n) (curBase : ℕ) (vec : Fin I.n → ℕ)
    (s₀ : Memory.State)
    (hs₀_fr : 2 + I.n * I.n ≤ s₀.frontier) (hcur_fr : curBase + I.n ≤ s₀.frontier)
    (hcur_fit : Fits w (curBase + I.n))
    (hadj_mem : ∀ x y : Fin I.n,
      s₀.mem (2 + x.1 * I.n + y.1) = if I.adj x y then 1 else 0)
    (hcur_mem : ∀ v : Fin I.n, s₀.mem (curBase + v.1) = vec v)
    (hsum_fit : Fits w (∑ v : Fin I.n, if I.adj u v then vec v else 0)) :
    let env : StepInnerArgs := ⟨I.n, u.1, curBase⟩
    iterationSafe stepInnerStep StepInnerSafe w env I.n ⟨0, 0⟩ s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (stepInnerProg env)) ∧
      memoryCost (stepInnerProg env) s₀ ≤ 2 * I.n ∧
      (Memory.spec 0).clientState s₀ (stepInnerProg env) = s₀ ∧
      (Memory.spec 0).clientResult s₀ (stepInnerProg env) =
        ∑ v : Fin I.n, if I.adj u v then vec v else 0 := by
  intro env
  have h1_fit : Fits w 1 := hfit.of_le (by unfold Instance.wordBound; omega)
  let rowFn : Fin I.n → ℕ := fun v => if I.adj u v then vec v else 0
  have hpref_n : finPrefSum rowFn I.n = ∑ v : Fin I.n, if I.adj u v then vec v else 0 :=
    finPrefSum_eq_sum rowFn
  have hspec := iterate_spec stepInnerStep StepInnerSafe w env 2 I.n
    (fun k st s => st = ⟨k, finPrefSum rowFn k⟩ ∧ s = s₀)
    (fun _ => False)
    (fun k hk st s ⟨hst, hs⟩ => by
      let vFin : Fin I.n := ⟨k, hk⟩
      have hidx_lt : u.1 * I.n + k < I.n * I.n := Cslib.Matrix.pairIndex_lt (u, vFin)
      have ha_lt : 2 + u.1 * I.n + k < s₀.frontier := by omega
      have hc_lt : curBase + k < s₀.frontier := by omega
      have ha_fit : Fits w (2 + u.1 * I.n + k) :=
        hfit.of_le ((by omega : 2 + u.1 * I.n + k ≤ I.n * I.n + 2 + 3 * I.n).trans
          (sq_add_three_n_add_two_le_wordBound I))
      have hc_fit : Fits w (curBase + k) := hcur_fit.of_le (by omega)
      have hk1_fit : Fits w (k + 1) := hfit.of_le (by
        have h1 := Instance.one_le_word_prod I.n
        unfold Instance.wordBound
        nlinarith)
      have hadj_v : s₀.mem (2 + u.1 * I.n + k) = if I.adj u vFin then 1 else 0 :=
        hadj_mem u vFin
      have hcur_v : s₀.mem (curBase + k) = vec vFin := hcur_mem vFin
      have hstep_pref :
          finPrefSum rowFn (k + 1) = finPrefSum rowFn k + if I.adj u vFin then vec vFin else 0 :=
        finPrefSum_succ rowFn hk
      have hacc_fit : s₀.mem (2 + u.1 * I.n + k) = 1 →
          Fits w (finPrefSum rowFn k + s₀.mem (curBase + k)) := by
        intro ha1
        rw [hadj_v] at ha1
        have hadj_true : I.adj u vFin = true := by
          cases h : I.adj u vFin <;> simp [h] at ha1 ⊢
        rw [hcur_v]
        refine hsum_fit.of_le ?_
        rw [← hpref_n]
        have h1 : finPrefSum rowFn k + vec vFin = finPrefSum rowFn (k + 1) := by
          rw [hstep_pref, hadj_true]; simp
        rw [h1]
        exact finPrefSum_mono rowFn hk
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hst, hs]
        exact ⟨h1_fit, ha_fit, hc_fit, hk1_fit, hacc_fit⟩
      · rw [hst, hs]
        refine validHistory_read_bind ha_lt (validHistory_ite ?_ ?_)
        · intro _
          exact validHistory_read_bind hc_lt (validHistory_pure w _ _)
        · intro _
          exact validHistory_pure w _ _
      · rw [hst, hs]
        simp only [stepInnerStep, memoryCost_bind', memoryCost_read, clientResult_read,
          memoryCost_ite, memoryCost_pure, add_zero]
        split_ifs <;> omega
      · rw [hs]
        simp only [stepInnerStep, client_simps]
        split_ifs <;> simp only [client_simps]
      · intro x _
        rw [hs]
        simp only [stepInnerStep, client_simps]
        split_ifs <;> simp only [client_simps]
      · refine ⟨?_, ?_⟩
        · rw [hst, hs]
          dsimp only [env]
          cases hadj : I.adj u vFin <;>
            simp [stepInnerStep, client_simps, hadj_v, hcur_v, hstep_pref, hadj]
        · rw [hs]
          simp only [stepInnerStep, client_simps]
          split_ifs <;> simp only [client_simps])
    ⟨0, 0⟩ s₀ ⟨by simp [finPrefSum_zero], rfl⟩
  have heq_s : (Memory.spec 0).clientState s₀ (stepInnerProg env) = s₀ := by
    rw [stepInnerProg, StateTransitionSpec.clientState_map]
    exact hspec.2.2.2.2.2.2
  refine ⟨hspec.1, StateTransitionSpec.validHistory_map hspec.2.1, ?_, heq_s, ?_⟩
  · rw [stepInnerProg, memoryCost_map]
    exact hspec.2.2.1
  · rw [stepInnerProg, StateTransitionSpec.clientResult_map, hspec.2.2.2.2.2.1, hpref_n]

-- 4. One round of restricted matrix–vector multiplication `stepVecProg`

private structure StepVecArgs where
  n : ℕ
  inMaskBase : ℕ
  curBase : ℕ
  nextBase : ℕ

private word_enc_structure encStepVecArgs : StepVecArgs where
  n : wordWords, inMaskBase : wordWords, curBase : wordWords, nextBase : wordWords

private instance : WordEncoding StepVecArgs := ⟨4, encStepVecArgs⟩

private def stepCellStep (x : StepVecArgs × ℕ) : Memory.Prog ℕ := do
  let env := Prod.fst x
  let u := Prod.snd x
  let inU ← Memory.read (env.inMaskBase + u)
  if inU = 1 then
    let acc ← stepInnerProg ⟨env.n, u, env.curBase⟩
    Memory.write (env.nextBase + u) acc
    pure (u + 1)
  else
    Memory.write (env.nextBase + u) 0
    pure (u + 1)

private abbrev StepCellSafe (w : ℕ) (x : StepVecArgs × ℕ) (s : Memory.State) : Prop :=
  let env := Prod.fst x
  let u := Prod.snd x
  Fits w 1 ∧ Fits w (env.inMaskBase + u) ∧ Fits w (env.nextBase + u) ∧ Fits w (u + 1) ∧
    (s.mem (env.inMaskBase + u) = 1 →
      Fits w env.n ∧ Fits w u ∧ Fits w env.curBase ∧
      iterationSafe stepInnerStep StepInnerSafe w ⟨env.n, u, env.curBase⟩ env.n ⟨0, 0⟩ s ∧
      Fits w ((Memory.spec 0).clientResult s (stepInnerProg ⟨env.n, u, env.curBase⟩)))

private theorem stepCellStep_realizes :
    Realizes .exact stepCellStep (appendWords encStepVecArgs wordWords) wordWords
      StepCellSafe (fun _ _ => 0) := by
  unfold stepCellStep
  realize [stepInnerProg_realizes]
  all_goals
    obtain ⟨h1, hin, hnext, hu, hbr⟩ := h
    first
    | exact h1
    | exact hin
    | exact hnext
    | exact hu
    | exact (hbr (by assumption)).2.2.2.1

private def stepVecProg (a : StepVecArgs) : Memory.Prog ℕ := do
  let _ ← iterate stepCellStep a a.n 0
  copySliceProg ⟨a.nextBase, a.curBase, a.n⟩

private theorem stepVecProg_realizes :
    Realizes .exact stepVecProg encStepVecArgs wordWords
      (fun w a s => Fits w a.n ∧ Fits w a.curBase ∧ Fits w a.nextBase ∧
        iterationSafe stepCellStep StepCellSafe w a a.n 0 s ∧
        iterationSafe copyStep CopyStepSafe w ⟨a.nextBase, a.curBase, a.n⟩ a.n 0
          ((Memory.spec 0).clientState s (iterate stepCellStep a a.n 0)))
      (fun _ _ => 0) := by
  unfold stepVecProg
  realize [stepCellStep_realizes, copySliceProg_realizes]
  all_goals
    obtain ⟨hn, hcur, hnext, hiter, hcopy⟩ := h
    first | exact hiter | exact hcopy

private theorem stepVecProg_spec {w : ℕ} (I : Instance) (hfit : I.FitsWidth w)
    (S : Finset (Fin I.n)) (inMaskBase curBase nextBase : ℕ)
    (vec : Fin I.n → ℕ) (s₀ : Memory.State)
    (hdisj_nc : ∀ i < I.n, ∀ j < I.n, curBase + i ≠ nextBase + j)
    (hdisj_ni : ∀ i < I.n, ∀ j < I.n, nextBase + i ≠ inMaskBase + j)
    (hdisj_na : ∀ i < I.n, ∀ x y : Fin I.n, nextBase + i ≠ 2 + x.1 * I.n + y.1)
    (hs₀_fr : 2 + I.n * I.n ≤ s₀.frontier)
    (hin_fr : inMaskBase + I.n ≤ s₀.frontier)
    (hcur_fr : curBase + I.n ≤ s₀.frontier)
    (hnext_fr : nextBase + I.n ≤ s₀.frontier)
    (hin_fit : Fits w (inMaskBase + I.n))
    (hcur_fit : Fits w (curBase + I.n))
    (hnext_fit : Fits w (nextBase + I.n))
    (hadj_mem : ∀ x y : Fin I.n,
      s₀.mem (2 + x.1 * I.n + y.1) = if I.adj x y then 1 else 0)
    (hin_mem : ∀ u : Fin I.n, s₀.mem (inMaskBase + u.1) = if u ∈ S then 1 else 0)
    (hcur_mem : ∀ u : Fin I.n, s₀.mem (curBase + u.1) = vec u)
    (hnext_fit_vals : ∀ u : Fin I.n,
      Fits w (∑ v : Fin I.n, if u ∈ S ∧ I.adj u v then vec v else 0)) :
    let env : StepVecArgs := ⟨I.n, inMaskBase, curBase, nextBase⟩
    (Fits w I.n ∧ Fits w curBase ∧ Fits w nextBase ∧
      iterationSafe stepCellStep StepCellSafe w env I.n 0 s₀ ∧
      iterationSafe copyStep CopyStepSafe w ⟨nextBase, curBase, I.n⟩ I.n 0
        ((Memory.spec 0).clientState s₀ (iterate stepCellStep env I.n 0))) ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (stepVecProg env)) ∧
      memoryCost (stepVecProg env) s₀ ≤ (2 * I.n + 2) * I.n + 2 * I.n ∧
      ((Memory.spec 0).clientState s₀ (stepVecProg env)).frontier = s₀.frontier ∧
      (∀ x, ¬ ((curBase ≤ x ∧ x < curBase + I.n) ∨ (nextBase ≤ x ∧ x < nextBase + I.n)) →
        ((Memory.spec 0).clientState s₀ (stepVecProg env)).mem x = s₀.mem x) ∧
      ∀ u : Fin I.n, ((Memory.spec 0).clientState s₀ (stepVecProg env)).mem (curBase + u.1) =
        ∑ v : Fin I.n, if u ∈ S ∧ I.adj u v then vec v else 0 := by
  intro env
  have h1_fit : Fits w 1 := hfit.of_le (by unfold Instance.wordBound; omega)
  have hn_fit : Fits w I.n := hfit.of_le (n_le_wordBound I)
  let nextVec : Fin I.n → ℕ := fun u => ∑ v : Fin I.n, if u ∈ S ∧ I.adj u v then vec v else 0
  have hiter := iterate_spec stepCellStep StepCellSafe w env (2 * I.n + 2) I.n
    (fun k idx s => idx = k ∧ s.frontier = s₀.frontier ∧
      (∀ x, ¬ (nextBase ≤ x ∧ x < nextBase + k) → s.mem x = s₀.mem x) ∧
      (∀ i, i < k → ∀ hi_n : i < I.n, s.mem (nextBase + i) = nextVec ⟨i, hi_n⟩))
    (fun x => nextBase ≤ x ∧ x < nextBase + I.n)
    (fun k hk idx s ⟨hidx, hfr, hpres, hpref⟩ => by
      let uFin : Fin I.n := ⟨k, hk⟩
      have hin_lt : inMaskBase + k < s.frontier := by omega
      have hnext_lt : nextBase + k < s.frontier := by omega
      have hpres_in : s.mem (inMaskBase + k) = if uFin ∈ S then 1 else 0 := by
        rw [hpres (inMaskBase + k) (fun ⟨hlo, hhi⟩ =>
          hdisj_ni (inMaskBase + k - nextBase) (by omega) k hk (by omega))]
        exact hin_mem uFin
      have hpres_adj : ∀ x y : Fin I.n,
          s.mem (2 + x.1 * I.n + y.1) = if I.adj x y then 1 else 0 := fun x y => by
        rw [hpres (2 + x.1 * I.n + y.1) (fun ⟨hlo, hhi⟩ =>
          hdisj_na (2 + x.1 * I.n + y.1 - nextBase) (by omega) x y (by omega))]
        exact hadj_mem x y
      have hpres_cur : ∀ v : Fin I.n, s.mem (curBase + v.1) = vec v := fun v => by
        rw [hpres (curBase + v.1) (fun ⟨hlo, hhi⟩ =>
          hdisj_nc v.1 v.isLt (curBase + v.1 - nextBase) (by omega) (by omega))]
        exact hcur_mem v
      have hinner (huS : uFin ∈ S) := stepInnerProg_spec I hfit uFin curBase vec s (by omega)
        (by omega) hcur_fit hpres_adj hpres_cur (by simpa [nextVec, huS] using hnext_fit_vals uFin)
      have hbr_safe : s.mem (inMaskBase + k) = 1 →
          Fits w I.n ∧ Fits w k ∧ Fits w curBase ∧
          iterationSafe stepInnerStep StepInnerSafe w ⟨I.n, k, curBase⟩ I.n ⟨0, 0⟩ s ∧
          Fits w ((Memory.spec 0).clientResult s (stepInnerProg ⟨I.n, k, curBase⟩)) := by
        intro hu1
        rw [hpres_in] at hu1
        have huS : uFin ∈ S := by
          by_contra hnot
          simp [hnot] at hu1
        have hinn := hinner huS
        refine ⟨hn_fit, hn_fit.of_le hk.le, hcur_fit.of_le (by omega), hinn.1, ?_⟩
        rw [hinn.2.2.2.2]
        simpa [nextVec, huS] using hnext_fit_vals uFin
      have hnext_u_fit : Fits w (nextVec uFin) := hnext_fit_vals uFin
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hidx]
        dsimp only [StepCellSafe, env]
        exact ⟨h1_fit, hin_fit.of_le (by omega), hnext_fit.of_le (by omega),
          hnext_fit.of_le (by omega), hbr_safe⟩
      · rw [hidx]
        refine validHistory_read_bind hin_lt (validHistory_ite ?_ ?_)
        · intro hu1
          have huS : uFin ∈ S := by
            rw [hpres_in] at hu1
            by_contra hnot
            simp [hnot] at hu1
          have hinn := hinner huS
          refine validHistory_bind_step hinn.2.1 ?_
          rw [hinn.2.2.2.1, hinn.2.2.2.2]
          have hval_fit : Fits w (∑ v : Fin I.n, if I.adj uFin v then vec v else 0) := by
            simpa [nextVec, huS] using hnext_u_fit
          exact validHistory_write_bind hnext_lt hval_fit (validHistory_pure w _ _)
        · intro _
          exact validHistory_write_bind hnext_lt (fits_zero w) (validHistory_pure w _ _)
      · rw [hidx]
        dsimp only [env]
        simp only [stepCellStep, memoryCost_bind', memoryCost_read, clientResult_read,
          memoryCost_ite, memoryCost_write, memoryCost_pure, add_zero, client_simps]
        split_ifs with hu1
        · have huS : uFin ∈ S := by
            rw [hpres_in] at hu1
            by_contra hnot
            simp [hnot] at hu1
          have hinn := hinner huS
          have h1 := hinn.2.2.1
          change 1 + (memoryCost (stepInnerProg ⟨I.n, uFin.1, curBase⟩) s + 1) ≤ 2 * I.n + 2
          omega
        · omega
      · dsimp only [env]
        by_cases hu1 : s.mem (inMaskBase + k) = 1
        · have huS : uFin ∈ S := by
            rw [hpres_in] at hu1
            by_contra hnot
            simp [hnot] at hu1
          have hst : (Memory.spec 0).clientState s (stepInnerProg ⟨I.n, k, curBase⟩) = s :=
            (hinner huS).2.2.2.1
          simp [stepCellStep, client_simps, hidx, hu1, hst, hfr]
        · simp [stepCellStep, client_simps, hidx, hu1, hfr]
      · intro x hx
        dsimp only [env]
        have hne : x ≠ nextBase + k := by omega
        by_cases hu1 : s.mem (inMaskBase + k) = 1
        · have huS : uFin ∈ S := by
            rw [hpres_in] at hu1
            by_contra hnot
            simp [hnot] at hu1
          have hst : (Memory.spec 0).clientState s (stepInnerProg ⟨I.n, k, curBase⟩) = s :=
            (hinner huS).2.2.2.1
          simp [stepCellStep, client_simps, hidx, hu1, hst, Function.update_of_ne hne]
        · simp [stepCellStep, client_simps, hidx, hu1, Function.update_of_ne hne]
      · refine ⟨?_, ?_, ?_, ?_⟩
        · dsimp only [env]
          simp [stepCellStep, client_simps, hidx]
        · dsimp only [env]
          by_cases hu1 : s.mem (inMaskBase + k) = 1
          · have huS : uFin ∈ S := by
              rw [hpres_in] at hu1
              by_contra hnot
              simp [hnot] at hu1
            have hst : (Memory.spec 0).clientState s (stepInnerProg ⟨I.n, k, curBase⟩) = s :=
              (hinner huS).2.2.2.1
            simp [stepCellStep, client_simps, hidx, hu1, hst, hfr]
          · simp [stepCellStep, client_simps, hidx, hu1, hfr]
        · intro x hx
          have hne : x ≠ nextBase + k := by
            intro heq
            exact hx ⟨by omega, by omega⟩
          have hnot_pre : ¬ (nextBase ≤ x ∧ x < nextBase + k) := fun ⟨h1, h2⟩ =>
            hx ⟨h1, by omega⟩
          dsimp only [env]
          by_cases hu1 : s.mem (inMaskBase + k) = 1
          · have huS : uFin ∈ S := by
              rw [hpres_in] at hu1
              by_contra hnot
              simp [hnot] at hu1
            have hst : (Memory.spec 0).clientState s (stepInnerProg ⟨I.n, k, curBase⟩) = s :=
              (hinner huS).2.2.2.1
            simp [stepCellStep, client_simps, hidx, hu1, hst,
              Function.update_of_ne hne, hpres x hnot_pre]
          · simp [stepCellStep, client_simps, hidx, hu1, Function.update_of_ne hne,
              hpres x hnot_pre]
        · intro i hi hi_n
          dsimp only [env]
          by_cases hik : i = k
          · subst hik
            by_cases huS : uFin ∈ S
            · have hu1 : s.mem (inMaskBase + i) = 1 := by simp [hpres_in, huS]
              have hinn := hinner huS
              have hst : (Memory.spec 0).clientState s (stepInnerProg ⟨I.n, i, curBase⟩) = s :=
                hinn.2.2.2.1
              have hres : (Memory.spec 0).clientResult s (stepInnerProg ⟨I.n, i, curBase⟩) =
                  ∑ v : Fin I.n, if I.adj uFin v then vec v else 0 := hinn.2.2.2.2
              simp [stepCellStep, client_simps, hidx, hu1, hst, hres, nextVec, huS, uFin]
            · have hu0 : s.mem (inMaskBase + i) ≠ 1 := by simp [hpres_in, huS]
              simp [stepCellStep, client_simps, hidx, hu0, nextVec, huS, uFin]
          · have hne : nextBase + i ≠ nextBase + k := by omega
            by_cases hu1 : s.mem (inMaskBase + k) = 1
            · have huS : uFin ∈ S := by
                rw [hpres_in] at hu1
                by_contra hnot
                simp [hnot] at hu1
              have hst : (Memory.spec 0).clientState s (stepInnerProg ⟨I.n, k, curBase⟩) = s :=
                (hinner huS).2.2.2.1
              simp [stepCellStep, client_simps, hidx, hu1, hst,
                Function.update_of_ne hne, hpref i (by omega) hi_n]
            · simp [stepCellStep, client_simps, hidx, hu1, Function.update_of_ne hne,
                hpref i (by omega) hi_n])
    0 s₀ ⟨rfl, rfl, fun _ _ => rfl, fun i hi => by omega⟩
  let s1 := (Memory.spec 0).clientState s₀ (iterate stepCellStep env I.n 0)
  have hs1_fr : s1.frontier = s₀.frontier := hiter.2.2.2.1
  have hs1_next : ∀ i (hi : i < I.n), s1.mem (nextBase + i) = nextVec ⟨i, hi⟩ :=
    fun i hi => hiter.2.2.2.2.2.2.2.2 i hi hi
  have hcopy := copySliceProg_spec ⟨nextBase, curBase, I.n⟩ s1
    hdisj_nc (by dsimp only; omega) (by dsimp only; omega) hnext_fit hcur_fit (fun i hi => by
      rw [hs1_next i hi]
      exact hnext_fit_vals ⟨i, hi⟩)
  refine ⟨⟨hn_fit, hcur_fit.of_le (by omega), hnext_fit.of_le (by omega), hiter.1, hcopy.1⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact validHistory_bind_step hiter.2.1 hcopy.2.1
  · dsimp only [stepVecProg, env]
    rw [memoryCost_bind']
    have hc1 := hiter.2.2.1
    have hc2 := hcopy.2.2.1
    dsimp only [env] at hc1
    change memoryCost (iterate stepCellStep ⟨I.n, inMaskBase, curBase, nextBase⟩ I.n 0) s₀ +
      memoryCost (copySliceProg ⟨nextBase, curBase, I.n⟩) s1 ≤ (2 * I.n + 2) * I.n + 2 * I.n
    dsimp only [s1] at hc1 hc2 ⊢
    omega
  · dsimp only [stepVecProg]
    rw [StateTransitionSpec.clientState_bind]
    exact hcopy.2.2.2.1.trans hs1_fr
  · intro x hx
    have hnot_cur : ¬ (curBase ≤ x ∧ x < curBase + I.n) := fun h => hx (Or.inl h)
    have hnot_next : ¬ (nextBase ≤ x ∧ x < nextBase + I.n) := fun h => hx (Or.inr h)
    dsimp only [stepVecProg]
    rw [StateTransitionSpec.clientState_bind, hcopy.2.2.2.2.1 x hnot_cur,
      hiter.2.2.2.2.1 x hnot_next]
  · intro u
    dsimp only [stepVecProg]
    rw [StateTransitionSpec.clientState_bind, hcopy.2.2.2.2.2 u.1 u.isLt, hs1_next u.1 u.isLt]

-- 5. Running `numRounds` matrix–vector rounds `roundsProg`

private structure RoundsArgs where
  n : ℕ
  inMaskBase : ℕ
  curBase : ℕ
  nextBase : ℕ
  numRounds : ℕ

private word_enc_structure encRoundsArgs : RoundsArgs where
  n : wordWords, inMaskBase : wordWords, curBase : wordWords,
  nextBase : wordWords, numRounds : wordWords

private instance : WordEncoding RoundsArgs := ⟨5, encRoundsArgs⟩

private def roundStep (x : RoundsArgs × ℕ) : Memory.Prog ℕ := do
  let env := Prod.fst x
  let r := Prod.snd x
  let _ ← Memory.read 0
  let _ ← stepVecProg ⟨env.n, env.inMaskBase, env.curBase, env.nextBase⟩
  pure (r + 1)

private abbrev RoundStepSafe (w : ℕ) (x : RoundsArgs × ℕ) (s : Memory.State) : Prop :=
  let env := Prod.fst x
  let r := Prod.snd x
  Fits w env.inMaskBase ∧ Fits w (r + 1) ∧ Fits w env.n ∧ Fits w env.curBase ∧
    Fits w env.nextBase ∧
    iterationSafe stepCellStep StepCellSafe w
      ⟨env.n, env.inMaskBase, env.curBase, env.nextBase⟩ env.n 0 s ∧
    iterationSafe copyStep CopyStepSafe w ⟨env.nextBase, env.curBase, env.n⟩ env.n 0
      ((Memory.spec 0).clientState s
        (iterate stepCellStep ⟨env.n, env.inMaskBase, env.curBase, env.nextBase⟩ env.n 0))

private theorem roundStep_realizes :
    Realizes .exact roundStep (appendWords encRoundsArgs wordWords) wordWords
      RoundStepSafe (fun _ _ => 0) := by
  unfold roundStep
  realize [stepVecProg_realizes]
  all_goals
    obtain ⟨hin, hr, hn, hcur, hnext, hcell, hcopy⟩ := h
    first
    | exact hr
    | exact hn
    | exact hcur
    | exact hnext
    | exact hcell
    | exact hcopy

private def roundsProg (a : RoundsArgs) : Memory.Prog ℕ :=
  iterate roundStep a a.numRounds 0

private theorem roundsProg_realizes :
    Realizes .exact roundsProg encRoundsArgs wordWords
      (fun w a s => iterationSafe roundStep RoundStepSafe w a a.numRounds 0 s)
      (fun _ _ => 0) := by
  unfold roundsProg
  realize [roundStep_realizes]
  exact h

private theorem roundsProg_spec {w : ℕ} (I : Instance) (hfit : I.FitsWidth w)
    (S : Finset (Fin I.n)) (inMaskBase curBase nextBase numRounds : ℕ)
    (hrounds : numRounds ≤ I.n) (s₀ : Memory.State)
    (hdisj_nc : ∀ i < I.n, ∀ j < I.n, curBase + i ≠ nextBase + j)
    (hdisj_ni : ∀ i < I.n, ∀ j < I.n, nextBase + i ≠ inMaskBase + j)
    (hdisj_na : ∀ i < I.n, ∀ x y : Fin I.n, nextBase + i ≠ 2 + x.1 * I.n + y.1)
    (hdisj_ci : ∀ i < I.n, ∀ j < I.n, curBase + i ≠ inMaskBase + j)
    (hdisj_ca : ∀ i < I.n, ∀ x y : Fin I.n, curBase + i ≠ 2 + x.1 * I.n + y.1)
    (hs₀_fr : 2 + I.n * I.n ≤ s₀.frontier)
    (hin_fr : inMaskBase + I.n ≤ s₀.frontier)
    (hcur_fr : curBase + I.n ≤ s₀.frontier)
    (hnext_fr : nextBase + I.n ≤ s₀.frontier)
    (hin_fit : Fits w (inMaskBase + I.n))
    (hcur_fit : Fits w (curBase + I.n))
    (hnext_fit : Fits w (nextBase + I.n))
    (hadj_mem : ∀ x y : Fin I.n,
      s₀.mem (2 + x.1 * I.n + y.1) = if I.adj x y then 1 else 0)
    (hin_mem : ∀ u : Fin I.n, s₀.mem (inMaskBase + u.1) = if u ∈ S then 1 else 0)
    (hcur0 : ∀ u : Fin I.n, s₀.mem (curBase + u.1) = walkCountFrom I.adj S 0 u) :
    let env : RoundsArgs := ⟨I.n, inMaskBase, curBase, nextBase, numRounds⟩
    iterationSafe roundStep RoundStepSafe w env numRounds 0 s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (roundsProg env)) ∧
      memoryCost (roundsProg env) s₀ ≤ ((2 * I.n + 2) * I.n + 2 * I.n + 1) * numRounds ∧
      ((Memory.spec 0).clientState s₀ (roundsProg env)).frontier = s₀.frontier ∧
      (∀ x, ¬ ((curBase ≤ x ∧ x < curBase + I.n) ∨ (nextBase ≤ x ∧ x < nextBase + I.n)) →
        ((Memory.spec 0).clientState s₀ (roundsProg env)).mem x = s₀.mem x) ∧
      ∀ u : Fin I.n, ((Memory.spec 0).clientState s₀ (roundsProg env)).mem (curBase + u.1) =
        walkCountFrom I.adj S numRounds u := by
  intro env
  have hn_fit : Fits w I.n := hfit.of_le (n_le_wordBound I)
  have hspec := iterate_spec roundStep RoundStepSafe w env
    ((2 * I.n + 2) * I.n + 2 * I.n + 1) numRounds
    (fun k idx s => idx = k ∧ s.frontier = s₀.frontier ∧
      (∀ x, ¬ ((curBase ≤ x ∧ x < curBase + I.n) ∨ (nextBase ≤ x ∧ x < nextBase + I.n)) →
        s.mem x = s₀.mem x) ∧
      (∀ u : Fin I.n, s.mem (curBase + u.1) = walkCountFrom I.adj S k u))
    (fun x => (curBase ≤ x ∧ x < curBase + I.n) ∨ (nextBase ≤ x ∧ x < nextBase + I.n))
    (fun k hk idx s ⟨hidx, hfr, hpres, hcur_k⟩ => by
      have hadj_s : ∀ x y : Fin I.n,
          s.mem (2 + x.1 * I.n + y.1) = if I.adj x y then 1 else 0 := fun x y => by
        rw [hpres (2 + x.1 * I.n + y.1) (by
          rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
          · exact hdisj_ca (2 + x.1 * I.n + y.1 - curBase) (by omega) x y (by omega)
          · exact hdisj_na (2 + x.1 * I.n + y.1 - nextBase) (by omega) x y (by omega))]
        exact hadj_mem x y
      have hin_s : ∀ u : Fin I.n,
          s.mem (inMaskBase + u.1) = if u ∈ S then 1 else 0 := fun u => by
        rw [hpres (inMaskBase + u.1) (by
          rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
          · exact hdisj_ci (inMaskBase + u.1 - curBase) (by omega) u.1 u.isLt (by omega)
          · exact hdisj_ni (inMaskBase + u.1 - nextBase) (by omega) u.1 u.isLt (by omega))]
        exact hin_mem u
      have hnext_fit_s : ∀ u : Fin I.n,
          Fits w (∑ v : Fin I.n,
            if u ∈ S ∧ I.adj u v then walkCountFrom I.adj S k v else 0) := fun u => by
        have hwf : (∑ v : Fin I.n,
            if u ∈ S ∧ I.adj u v then walkCountFrom I.adj S k v else 0) =
            walkCountFrom I.adj S (k + 1) u := rfl
        rw [hwf]
        exact hfit.of_le (walkCountFrom_le_wordBound I S (by omega) u)
      have hsv := stepVecProg_spec I hfit S inMaskBase curBase nextBase
        (walkCountFrom I.adj S k) s hdisj_nc hdisj_ni hdisj_na
        (by omega) (by omega) (by omega) (by omega)
        hin_fit hcur_fit hnext_fit hadj_s hin_s hcur_k hnext_fit_s
      have h0_lt : 0 < s.frontier := by omega
      have hk1_fit : Fits w (k + 1) := hfit.of_le (by
        have h1 := Instance.one_le_word_prod I.n
        unfold Instance.wordBound
        nlinarith)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hidx]
        dsimp only [RoundStepSafe, env]
        exact ⟨hin_fit.of_le (by omega), hk1_fit, hsv.1.1, hsv.1.2.1, hsv.1.2.2.1,
          hsv.1.2.2.2.1, hsv.1.2.2.2.2⟩
      · rw [hidx]
        exact validHistory_read_bind h0_lt
          (validHistory_bind_step hsv.2.1 (validHistory_pure w _ _))
      · dsimp only [env]
        simp only [roundStep, memoryCost_bind', memoryCost_read, memoryCost_pure, add_zero,
          client_simps]
        have hcost := hsv.2.2.1
        omega
      · dsimp only [env]
        simp [roundStep, client_simps, hsv.2.2.2.1]
      · intro x hx
        dsimp only [env]
        simp [roundStep, client_simps, hsv.2.2.2.2.1 x hx]
      · refine ⟨?_, ?_, ?_, ?_⟩
        · simp [roundStep, client_simps, hidx]
        · dsimp only [env]
          simp [roundStep, client_simps, hsv.2.2.2.1, hfr]
        · intro x hx
          dsimp only [env]
          simp [roundStep, client_simps, hsv.2.2.2.2.1 x hx, hpres x hx]
        · intro u
          dsimp only [env]
          have hwf : (∑ v : Fin I.n,
              if u ∈ S ∧ I.adj u v then walkCountFrom I.adj S k v else 0) =
              walkCountFrom I.adj S (k + 1) u := rfl
          simp [roundStep, client_simps, hsv.2.2.2.2.2 u, hwf])
    0 s₀ ⟨rfl, rfl, fun _ _ => rfl, hcur0⟩
  dsimp only [roundsProg, env]
  exact ⟨hspec.1, hspec.2.1, hspec.2.2.1, hspec.2.2.2.1, hspec.2.2.2.2.1,
    hspec.2.2.2.2.2.2.2.2⟩

-- 6. Summing a length-`len` vector `sumVecProg`

private structure SumArgs where
  base : ℕ
  len : ℕ

private word_enc_structure encSumArgs : SumArgs where
  base : wordWords, len : wordWords

private instance : WordEncoding SumArgs := ⟨2, encSumArgs⟩

private structure SumState where
  u : ℕ
  acc : ℕ

private word_enc_structure encSumState : SumState where
  u : wordWords, acc : wordWords

private instance : WordEncoding SumState := ⟨2, encSumState⟩

private def sumStep (x : SumArgs × SumState) : Memory.Prog SumState := do
  let env := Prod.fst x
  let st := Prod.snd x
  let v ← Memory.read (env.base + st.u)
  pure ⟨st.u + 1, st.acc + v⟩

private abbrev SumStepSafe (w : ℕ) (x : SumArgs × SumState) (s : Memory.State) : Prop :=
  let env := Prod.fst x
  let st := Prod.snd x
  Fits w (env.base + st.u) ∧ Fits w (st.u + 1) ∧ Fits w (st.acc + s.mem (env.base + st.u))

private theorem sumStep_realizes :
    Realizes .exact sumStep (appendWords encSumArgs encSumState) encSumState
      SumStepSafe (fun _ _ => 0) := by
  unfold sumStep
  realize
  all_goals
    obtain ⟨hb, hu, hacc⟩ := h
    first | exact hb | exact hu | exact hacc

private def sumVecProg (a : SumArgs) : Memory.Prog ℕ :=
  SumState.acc <$> iterate sumStep a a.len ⟨0, 0⟩

private theorem sumVecProg_realizes :
    Realizes .exact sumVecProg encSumArgs wordWords
      (fun w a s => iterationSafe sumStep SumStepSafe w a a.len ⟨0, 0⟩ s)
      (fun _ _ => 0) := by
  unfold sumVecProg
  realize [sumStep_realizes]
  exact h

private theorem sumVecProg_spec {w : ℕ} (I : Instance) (hfit : I.FitsWidth w)
    (base : ℕ) (vec : Fin I.n → ℕ) (s₀ : Memory.State)
    (hfr : base + I.n ≤ s₀.frontier) (hbase_fit : Fits w (base + I.n))
    (hmem : ∀ u : Fin I.n, s₀.mem (base + u.1) = vec u)
    (hsum_fit : Fits w (∑ u : Fin I.n, vec u)) :
    let env : SumArgs := ⟨base, I.n⟩
    iterationSafe sumStep SumStepSafe w env I.n ⟨0, 0⟩ s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (sumVecProg env)) ∧
      memoryCost (sumVecProg env) s₀ ≤ I.n ∧
      (Memory.spec 0).clientState s₀ (sumVecProg env) = s₀ ∧
      (Memory.spec 0).clientResult s₀ (sumVecProg env) = ∑ u : Fin I.n, vec u := by
  intro env
  have hpref_n : finPrefSum vec I.n = ∑ u : Fin I.n, vec u := finPrefSum_eq_sum vec
  have hspec := iterate_spec sumStep SumStepSafe w env 1 I.n
    (fun k st s => st = ⟨k, finPrefSum vec k⟩ ∧ s = s₀)
    (fun _ => False)
    (fun k hk st s ⟨hst, hs⟩ => by
      let uFin : Fin I.n := ⟨k, hk⟩
      have ha_lt : base + k < s₀.frontier := by omega
      have ha_fit : Fits w (base + k) := hbase_fit.of_le (by omega)
      have hk1_fit : Fits w (k + 1) := hfit.of_le (by
        have h1 := Instance.one_le_word_prod I.n
        unfold Instance.wordBound
        nlinarith)
      have hvec_k : s₀.mem (base + k) = vec uFin := hmem uFin
      have hstep_pref : finPrefSum vec (k + 1) = finPrefSum vec k + vec uFin :=
        finPrefSum_succ vec hk
      have hacc_fit : Fits w (finPrefSum vec k + s₀.mem (base + k)) := by
        rw [hvec_k, ← hstep_pref]
        exact hsum_fit.of_le (hpref_n ▸ finPrefSum_mono vec hk)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hst, hs]
        exact ⟨ha_fit, hk1_fit, hacc_fit⟩
      · rw [hst, hs]
        exact validHistory_read_bind ha_lt (validHistory_pure w _ _)
      · simp only [sumStep, memoryCost_bind', memoryCost_read, memoryCost_pure, add_zero, le_refl]
      · rw [hs]
        simp [sumStep, client_simps]
      · intro x _
        rw [hs]
        simp [sumStep, client_simps]
      · refine ⟨?_, ?_⟩
        · rw [hst, hs]
          dsimp only [env]
          simp [sumStep, client_simps, hvec_k, hstep_pref]
        · rw [hs]
          simp [sumStep, client_simps])
    ⟨0, 0⟩ s₀ ⟨by simp [finPrefSum_zero], rfl⟩
  have heq_s : (Memory.spec 0).clientState s₀ (sumVecProg env) = s₀ := by
    rw [sumVecProg, StateTransitionSpec.clientState_map]
    exact hspec.2.2.2.2.2.2
  refine ⟨hspec.1, StateTransitionSpec.validHistory_map hspec.2.1, ?_, heq_s, ?_⟩
  · rw [sumVecProg, memoryCost_map]
    simpa only [one_mul] using hspec.2.2.1
  · rw [sumVecProg, StateTransitionSpec.clientResult_map, hspec.2.2.2.2.2.1, hpref_n]

-- 7. In-place binary odometer + parity flip `odometerProg`

private structure OdoArgs where
  base : ℕ
  len : ℕ
  parity0 : ℕ

private word_enc_structure encOdoArgs : OdoArgs where
  base : wordWords, len : wordWords, parity0 : wordWords

private instance : WordEncoding OdoArgs := ⟨3, encOdoArgs⟩

private structure OdoState where
  i : ℕ
  carry : ℕ
  parity : ℕ

private word_enc_structure encOdoState : OdoState where
  i : wordWords, carry : wordWords, parity : wordWords

private instance : WordEncoding OdoState := ⟨3, encOdoState⟩

private def odoStep (x : OdoArgs × OdoState) : Memory.Prog OdoState := do
  let env := Prod.fst x
  let st := Prod.snd x
  let b ← Memory.read (env.base + st.i)
  if st.carry = 1 then
    if b = 1 then
      Memory.write (env.base + st.i) 0
      pure ⟨st.i + 1, 1, 1 - st.parity⟩
    else
      Memory.write (env.base + st.i) 1
      pure ⟨st.i + 1, 0, 1 - st.parity⟩
  else
    pure ⟨st.i + 1, 0, st.parity⟩

private abbrev OdoStepSafe (w : ℕ) (x : OdoArgs × OdoState) (_ : Memory.State) : Prop :=
  let env := Prod.fst x
  let st := Prod.snd x
  Fits w 1 ∧ Fits w (env.base + st.i) ∧ Fits w (st.i + 1) ∧
    (st.carry = 1 → st.parity ≤ 1)

private theorem odoStep_realizes :
    Realizes .exact odoStep (appendWords encOdoArgs encOdoState) encOdoState
      OdoStepSafe (fun _ _ => 0) := by
  unfold odoStep
  realize
  all_goals
    obtain ⟨h1, hb, hi, hpar⟩ := h
    first
    | exact h1
    | exact hb
    | exact hi
    | exact hpar (by assumption)

private def odometerProg (a : OdoArgs) : Memory.Prog ℕ :=
  OdoState.parity <$> iterate odoStep a a.len ⟨0, 1, a.parity0⟩

private theorem odometerProg_realizes :
    Realizes .exact odometerProg encOdoArgs wordWords
      (fun w a s => Fits w 1 ∧ iterationSafe odoStep OdoStepSafe w a a.len ⟨0, 1, a.parity0⟩ s)
      (fun _ _ => 0) := by
  unfold odometerProg
  realize [odoStep_realizes]
  all_goals first | exact h.1 | exact h.2

private theorem odometerProg_spec {w : ℕ} (I : Instance) (hfit : I.FitsWidth w)
    (k base : ℕ) (s₀ : Memory.State)
    (hfr : base + I.n ≤ s₀.frontier) (hbase_fit : Fits w (base + I.n))
    (hin_mem : ∀ u : Fin I.n, s₀.mem (base + u.1) = if k.testBit u.1 then 1 else 0) :
    let env : OdoArgs := ⟨base, I.n, (maskSet I.n k).card % 2⟩
    (Fits w 1 ∧ iterationSafe odoStep OdoStepSafe w env I.n ⟨0, 1, (maskSet I.n k).card % 2⟩ s₀) ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (odometerProg env)) ∧
      memoryCost (odometerProg env) s₀ ≤ 2 * I.n ∧
      ((Memory.spec 0).clientState s₀ (odometerProg env)).frontier = s₀.frontier ∧
      (∀ x, ¬ (base ≤ x ∧ x < base + I.n) →
        ((Memory.spec 0).clientState s₀ (odometerProg env)).mem x = s₀.mem x) ∧
      (∀ u : Fin I.n, ((Memory.spec 0).clientState s₀ (odometerProg env)).mem (base + u.1) =
        if (k + 1).testBit u.1 then 1 else 0) ∧
      (Memory.spec 0).clientResult s₀ (odometerProg env) = (maskSet I.n (k + 1)).card % 2 := by
  intro env
  have h1_fit : Fits w 1 := hfit.of_le (by unfold Instance.wordBound; omega)
  let OdoInv : ℕ → OdoState → Memory.State → Prop := fun j st s =>
    st.i = j ∧ s.frontier = s₀.frontier ∧
      (∀ u : Fin I.n, u.1 < j →
        s.mem (base + u.1) = if (k + 1).testBit u.1 then 1 else 0) ∧
      (∀ u : Fin I.n, j ≤ u.1 →
        s.mem (base + u.1) = if k.testBit u.1 then 1 else 0) ∧
      ((st.carry = 1 ∧ (∀ m < j, k.testBit m = true) ∧
          st.parity = ((maskSet I.n k).card + j) % 2) ∨
        (st.carry = 0 ∧ ∃ t < j, (∀ m < t, k.testBit m = true) ∧ k.testBit t = false ∧
          st.parity = ((maskSet I.n k).card + (t + 1)) % 2))
  have hspec := iterate_spec odoStep OdoStepSafe w env 2 I.n OdoInv
    (fun x => base ≤ x ∧ x < base + I.n)
    (fun j hj st s ⟨hi, hfr_s, hlo, hhi, hcase⟩ => by
      let jFin : Fin I.n := ⟨j, hj⟩
      have haddr_lt : base + j < s.frontier := by omega
      have haddr_fit : Fits w (base + j) := hbase_fit.of_le (by omega)
      have hj1_fit : Fits w (j + 1) := hfit.of_le (by
        have h1 := Instance.one_le_word_prod I.n
        unfold Instance.wordBound
        nlinarith)
      have hpar_le : st.carry = 1 → st.parity ≤ 1 := fun hc1 => by
        rcases hcase with ⟨_, _, hp⟩ | ⟨hc0, _⟩
        · omega
        · omega
      have hbit_j : s.mem (base + j) = if k.testBit j then 1 else 0 := hhi jFin (le_refl j)
      have hmem_upd : ∀ x, x ≠ base + j →
          ((Memory.spec 0).clientState s (odoStep (env, st))).mem x = s.mem x := fun x hne => by
        dsimp only [env]
        simp only [odoStep, client_simps, hi]
        split_ifs <;> simp only [client_simps, Function.update_of_ne hne]
      have hres_eq : (Memory.spec 0).clientResult s (odoStep (env, st)) =
          if st.carry = 1 then
            if s.mem (base + j) = 1 then ⟨j + 1, 1, 1 - st.parity⟩
            else ⟨j + 1, 0, 1 - st.parity⟩
          else ⟨j + 1, 0, st.parity⟩ := by
        dsimp only [env]
        simp [odoStep, client_simps, hi]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · dsimp only [OdoStepSafe]
        rw [hi]
        exact ⟨h1_fit, haddr_fit, hj1_fit, hpar_le⟩
      · dsimp only [odoStep]
        rw [hi]
        refine validHistory_read_bind haddr_lt (validHistory_ite ?_ ?_)
        · intro _
          refine validHistory_ite ?_ ?_
          · intro _
            exact validHistory_write_bind haddr_lt (fits_zero w) (validHistory_pure w _ _)
          · intro _
            exact validHistory_write_bind haddr_lt h1_fit (validHistory_pure w _ _)
        · intro _
          exact validHistory_pure w _ _
      · dsimp only [odoStep]
        rw [hi]
        simp only [memoryCost_bind', memoryCost_read, clientResult_read,
          memoryCost_ite, memoryCost_write, memoryCost_pure, add_zero]
        split_ifs <;> omega
      · dsimp only [env]
        simp only [odoStep, client_simps, hi]
        split_ifs <;> simp only [client_simps, hfr_s]
      · intro x hx
        exact hmem_upd x (by omega)
      · have hfr' : ((Memory.spec 0).clientState s (odoStep (env, st))).frontier = s₀.frontier := by
          dsimp only [env]
          simp only [odoStep, client_simps, hi]
          split_ifs <;> simp only [client_simps, hfr_s]
        refine ⟨?_, hfr', ?_, ?_, ?_⟩
        · rw [hres_eq]
          split_ifs <;> rfl
        · intro u hu_lt
          by_cases huj : u.1 = j
          · have hbit_succ : (k + 1).testBit j =
                if ∀ m < j, k.testBit m = true then !(k.testBit j) else k.testBit j :=
              Nat.testBit_add_one_eq_ite_forall k j
            rcases hcase with ⟨hc1, hall1, _⟩ | ⟨hc0, t, htj, hall1, h0t, _⟩
            · dsimp only [env]
              by_cases hkj : k.testBit j = true
              · have hb1 : s.mem (base + j) = 1 := by simp [hbit_j, hkj]
                have hbit1 : (k + 1).testBit j = false := by
                  rw [hbit_succ, ite_eq_left hall1, hkj]; rfl
                simp [odoStep, client_simps, hi, hc1, hb1, huj, hbit1]
              · have hkf : k.testBit j = false := Bool.eq_false_iff.2 hkj
                have hb0 : s.mem (base + j) ≠ 1 := by simp [hbit_j, hkf]
                have hbit1 : (k + 1).testBit j = true := by
                  rw [hbit_succ, ite_eq_left hall1, hkf]; rfl
                simp [odoStep, client_simps, hi, hc1, hb0, huj, hbit1]
            · have hcne : st.carry ≠ 1 := by omega
              have hnot : ¬ ∀ m < j, k.testBit m = true := fun h => by
                have := h t htj
                rw [h0t] at this
                simp at this
              have hst_eq : ((Memory.spec 0).clientState s (odoStep (env, st))).mem (base + j) =
                  s.mem (base + j) := by
                dsimp only [env]
                simp [odoStep, client_simps, hi, hcne]
              rw [huj, hst_eq, hbit_j, hbit_succ, ite_eq_right hnot]
          · have hu_prev : u.1 < j := by omega
            rw [hmem_upd (base + u.1) (by omega)]
            exact hlo u hu_prev
        · intro u hu_ge
          rw [hmem_upd (base + u.1) (by omega)]
          exact hhi u (by omega)
        · rw [hres_eq]
          rcases hcase with ⟨hc1, hall1, hp⟩ | ⟨hc0, t, htj, hall1, h0t, hp⟩
          · by_cases hkj : k.testBit j = true
            · left
              have hb1 : s.mem (base + j) = 1 := by simp [hbit_j, hkj]
              simp only [hc1, ↓reduceIte, hb1]
              refine ⟨trivial, fun m hm => ?_, ?_⟩
              · by_cases hmj : m = j
                · subst hmj; exact hkj
                · exact hall1 m (by omega)
              · have hp_lt : st.parity < 2 := by omega
                have hmod : (1 - st.parity) = (st.parity + 1) % 2 := by omega
                rw [hmod, hp, Nat.mod_add_mod, Nat.add_assoc]
            · right
              have hkf : k.testBit j = false := Bool.eq_false_iff.2 hkj
              have hb0 : s.mem (base + j) ≠ 1 := by simp [hbit_j, hkf]
              simp only [hc1, ↓reduceIte, hb0]
              refine ⟨trivial, j, Nat.lt_succ_self j, hall1, hkf, ?_⟩
              have hp_lt : st.parity < 2 := by omega
              have hmod : (1 - st.parity) = (st.parity + 1) % 2 := by omega
              rw [hmod, hp, Nat.mod_add_mod, Nat.add_assoc]
          · right
            have hcne : st.carry ≠ 1 := by omega
            simp only [hcne, ↓reduceIte]
            exact ⟨trivial, t, Nat.lt_trans htj (Nat.lt_succ_self j), hall1, h0t, hp⟩)
    ⟨0, 1, (maskSet I.n k).card % 2⟩ s₀
    ⟨rfl, rfl, fun u hu => by omega, fun u _ => hin_mem u, Or.inl ⟨rfl, fun m hm => by omega, rfl⟩⟩
  have hpar_eq :
      ((Memory.spec 0).clientResult s₀
        (iterate odoStep env I.n ⟨0, 1, (maskSet I.n k).card % 2⟩)).parity =
        (maskSet I.n (k + 1)).card % 2 := by
    rcases hspec.2.2.2.2.2.2.2.2.2 with ⟨_, hall1, hp⟩ | ⟨_, t, htn, hall1, h0t, hp⟩
    · rw [hp]
      simpa using (card_maskSet_succ_prefix_mod hall1 (Or.inl rfl)).symm
    · rw [hp]
      simpa [htn.ne] using (card_maskSet_succ_prefix_mod hall1 (Or.inr ⟨htn, h0t⟩)).symm
  simp only [odometerProg, memoryCost_map, StateTransitionSpec.fst_snd_runClient_map,
    StateTransitionSpec.clientResult_map]
  exact ⟨⟨h1_fit, hspec.1⟩, StateTransitionSpec.validHistory_map hspec.2.1, hspec.2.2.1,
    hspec.2.2.2.1, hspec.2.2.2.2.1, fun u => hspec.2.2.2.2.2.2.2.1 u u.isLt, hpar_eq⟩

-- 8. Computing `2 ^ n` via `n`-step doubling (`pow2Prog`)

private def pow2Step (x : ℕ × ℕ) : Memory.Prog ℕ := do
  let _ ← Memory.read 0
  pure (Prod.snd x + Prod.snd x)

private abbrev Pow2StepSafe (w : ℕ) (x : ℕ × ℕ) (_ : Memory.State) : Prop :=
  Fits w (Prod.snd x + Prod.snd x)

private theorem pow2Step_realizes :
    Realizes .exact pow2Step (appendWords wordWords wordWords) wordWords
      Pow2StepSafe (fun _ _ => 0) := by
  unfold pow2Step
  realize
  exact h

private def pow2Prog (n : ℕ) : Memory.Prog ℕ :=
  iterate pow2Step n n 1

private theorem pow2Prog_realizes :
    Realizes .exact pow2Prog wordWords wordWords
      (fun w n s => Fits w 1 ∧ iterationSafe pow2Step Pow2StepSafe w n n 1 s)
      (fun _ _ => 0) := by
  unfold pow2Prog
  realize [pow2Step_realizes]
  all_goals first | exact h.1 | exact h.2

private theorem pow2Prog_spec {w : ℕ} (I : Instance) (hfit : I.FitsWidth w)
    (s₀ : Memory.State) (hs₀_fr : 0 < s₀.frontier) :
    iterationSafe pow2Step Pow2StepSafe w I.n I.n 1 s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (pow2Prog I.n)) ∧
      memoryCost (pow2Prog I.n) s₀ ≤ I.n ∧
      (Memory.spec 0).clientState s₀ (pow2Prog I.n) = s₀ ∧
      (Memory.spec 0).clientResult s₀ (pow2Prog I.n) = 2 ^ I.n := by
  have h2n_fit : Fits w (2 ^ I.n) := by
    have hpow : 2 ^ I.n ≤ 2 ^ I.n * (I.n + 1) ^ I.n :=
      Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (by omega))
    exact hfit.of_le (by unfold Instance.wordBound; omega)
  have hspec := iterate_spec pow2Step Pow2StepSafe w I.n 1 I.n
    (fun k p s => p = 2 ^ k ∧ s = s₀)
    (fun _ => False)
    (fun k hk p s ⟨hp, hs⟩ => by
      have hfit_2p : Fits w (2 ^ k + 2 ^ k) := by
        rw [← two_mul, ← pow_succ']
        exact h2n_fit.of_le (Nat.pow_le_pow_right (by decide) hk)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hp]; exact hfit_2p
      · rw [hs]; exact validHistory_read_bind hs₀_fr (validHistory_pure w _ _)
      · dsimp only [pow2Step]
        rw [memoryCost_bind', memoryCost_pure, add_zero]
        exact le_rfl
      · rw [hs]
        simp [pow2Step, client_simps]
      · intro x _
        rw [hs]
        simp [pow2Step, client_simps]
      · refine ⟨?_, ?_⟩
        · rw [hp]
          simp [pow2Step, client_simps, pow_succ', two_mul]
        · rw [hs]
          simp [pow2Step, client_simps])
    1 s₀ ⟨by simp, rfl⟩
  have heq_s : (Memory.spec 0).clientState s₀ (pow2Prog I.n) = s₀ := by
    have hfr := hspec.2.2.2.1
    have hmem := hspec.2.2.2.2.1
    ext a
    · exact hmem a (by simp)
    · exact hfr
  refine ⟨hspec.1, hspec.2.1, ?_, heq_s, hspec.2.2.2.2.2.1⟩
  simpa only [pow2Prog, one_mul] using hspec.2.2.1

-- 9. Full Karp–Bax inclusion–exclusion client `countHamProg` & `decideHamProg`

private structure MaskArgs where
  n : ℕ
  ws : ℕ
  lim : ℕ

private word_enc_structure encMaskArgs : MaskArgs where
  n : wordWords, ws : wordWords, lim : wordWords

private instance : WordEncoding MaskArgs := ⟨3, encMaskArgs⟩

private structure MaskState where
  evenSum : ℕ
  oddSum : ℕ
  parity : ℕ

private word_enc_structure encMaskState : MaskState where
  evenSum : wordWords, oddSum : wordWords, parity : wordWords

private instance : WordEncoding MaskState := ⟨3, encMaskState⟩

private def maskStep (x : MaskArgs × MaskState) : Memory.Prog MaskState := do
  let env := Prod.fst x
  let st := Prod.snd x
  let _ ← Memory.read 0
  let inB := env.ws
  let curB := env.ws + env.n
  let nextB := env.ws + 2 * env.n
  let walks ←
    if env.n = 0 then
      pure 1
    else
      let _ ← copySliceProg ⟨inB, curB, env.n⟩
      let _ ← roundsProg ⟨env.n, inB, curB, nextB, env.n - 1⟩
      sumVecProg ⟨curB, env.n⟩
  let newParity ← odometerProg ⟨inB, env.n, st.parity⟩
  if env.n % 2 = st.parity then
    pure ⟨st.evenSum + walks, st.oddSum, newParity⟩
  else
    pure ⟨st.evenSum, st.oddSum + walks, newParity⟩

private abbrev MaskStepSafe (w : ℕ) (x : MaskArgs × MaskState) (s : Memory.State) : Prop :=
  let env := Prod.fst x
  let st := Prod.snd x
  let inB := env.ws
  let curB := env.ws + env.n
  let nextB := env.ws + 2 * env.n
  Fits w 2 ∧ Fits w curB ∧ Fits w nextB ∧ Fits w (env.n % 2) ∧
    (if env.n = 0 then Fits w 1 else
      Fits w (env.n - 1) ∧
      iterationSafe copyStep CopyStepSafe w ⟨inB, curB, env.n⟩ env.n 0 s ∧
      iterationSafe roundStep RoundStepSafe w ⟨env.n, inB, curB, nextB, env.n - 1⟩
        (env.n - 1) 0 ((Memory.spec 0).clientState s (copySliceProg ⟨inB, curB, env.n⟩)) ∧
      iterationSafe sumStep SumStepSafe w ⟨curB, env.n⟩ env.n ⟨0, 0⟩
        ((Memory.spec 0).clientState
          ((Memory.spec 0).clientState s (copySliceProg ⟨inB, curB, env.n⟩))
          (roundsProg ⟨env.n, inB, curB, nextB, env.n - 1⟩))) ∧
    let walks :=
      if env.n = 0 then 1 else
        (Memory.spec 0).clientResult
          ((Memory.spec 0).clientState
            ((Memory.spec 0).clientState s (copySliceProg ⟨inB, curB, env.n⟩))
            (roundsProg ⟨env.n, inB, curB, nextB, env.n - 1⟩))
          (sumVecProg ⟨curB, env.n⟩)
    let s1 :=
      if env.n = 0 then s else
        (Memory.spec 0).clientState
          ((Memory.spec 0).clientState
            ((Memory.spec 0).clientState s (copySliceProg ⟨inB, curB, env.n⟩))
            (roundsProg ⟨env.n, inB, curB, nextB, env.n - 1⟩))
          (sumVecProg ⟨curB, env.n⟩)
    Fits w 1 ∧
      iterationSafe odoStep OdoStepSafe w ⟨inB, env.n, st.parity⟩ env.n ⟨0, 1, st.parity⟩ s1 ∧
      if env.n % 2 = st.parity then Fits w (st.evenSum + walks) else Fits w (st.oddSum + walks)

private theorem maskStep_realizes :
    Realizes .exact maskStep (appendWords encMaskArgs encMaskState) encMaskState
      MaskStepSafe (fun _ _ => 0) := by
  unfold maskStep
  realize [copySliceProg_realizes, roundsProg_realizes, sumVecProg_realizes, odometerProg_realizes]
  all_goals
    obtain ⟨h2, hcur, hnext, hmod, hbr, hodo1, hodo, hsum⟩ := h
    first
    | exact hcur
    | exact hnext
    | exact h2
    | exact h2.of_le (by omega)
    | omega
    | exact (by
        have h' := hbr
        simp only [*, ↓reduceIte] at h'
        first
        | exact h'.2.1
        | exact h'.2.2.1
        | exact h'.2.2.2)
    | (simp only [*, ↓reduceIte, client_simps] at hodo ⊢
       exact hodo)
    | (simp only [*, ↓reduceIte, client_simps] at hsum ⊢
       first
       | exact hsum
       | (simp only [Nat.zero_mod] at hsum
          split_ifs at hsum with hp
          · first | exact hsum | (have h0 := hp.symm; clear hp; simp_all only [Nat.zero_mod])
          · first | exact hsum | simp_all only [Nat.zero_mod]))

private def maskLoopProg (a : MaskArgs) : Memory.Prog ℕ := do
  let res ← iterate maskStep a a.lim ⟨0, 0, 0⟩
  pure (res.evenSum - res.oddSum)

private theorem maskLoopProg_realizes :
    Realizes .exact maskLoopProg encMaskArgs wordWords
      (fun w a s =>
        iterationSafe maskStep MaskStepSafe w a a.lim ⟨0, 0, 0⟩ s ∧
        let res := (Memory.spec 0).clientResult s (iterate maskStep a a.lim ⟨0, 0, 0⟩)
        res.oddSum ≤ res.evenSum)
      (fun _ _ => 0) := by
  unfold maskLoopProg
  realize [maskStep_realizes]
  all_goals first | exact h.1 | exact h.2

private def countHamProg (n : ℕ) : Memory.Prog ℕ := do
  let ws ← Memory.allocDirty (3 * n)
  let _ ← zeroWordsProg ⟨ws, n⟩
  let lim ← pow2Prog n
  maskLoopProg ⟨n, ws, lim⟩

private abbrev CountHamSafe (w : ℕ) (n : ℕ) (s : Memory.State) : Prop :=
  let ws := s.frontier
  let s1 := ⟨s.mem, s.frontier + 3 * n⟩
  let s2 := (Memory.spec 0).clientState s1 (zeroWordsProg ⟨ws, n⟩)
  let lim := (Memory.spec 0).clientResult s2 (pow2Prog n)
  let s3 := (Memory.spec 0).clientState s2 (pow2Prog n)
  let res := (Memory.spec 0).clientResult s3 (iterate maskStep ⟨n, ws, lim⟩ lim ⟨0, 0, 0⟩)
  Fits w (s.frontier + 3 * n) ∧ Fits w 3 ∧ Fits w (3 * n) ∧
    iterationSafe zeroStep ZeroStepSafe w ⟨ws, n⟩ n 0 s1 ∧
    iterationSafe pow2Step Pow2StepSafe w n n 1 s2 ∧
    iterationSafe maskStep MaskStepSafe w ⟨n, ws, lim⟩ lim ⟨0, 0, 0⟩ s3 ∧
    res.oddSum ≤ res.evenSum

private theorem countHamProg_realizes :
    Realizes .exact countHamProg wordWords wordWords CountHamSafe (fun _ _ => 0) := by
  unfold countHamProg
  realize [zeroWordsProg_realizes, pow2Prog_realizes, maskLoopProg_realizes]
  all_goals
    obtain ⟨hfr, h3, h3n, hzero, hpow, hmask, hsub⟩ := h
    first
    | exact h3.of_le (by decide)
    | exact h3n
    | exact hzero
    | exact hpow
    | exact hmask
    | exact hsub

private def decideHamProg (n : ℕ) : Memory.Prog ℕ := do
  let c ← countHamProg n
  pure (if 0 < c then 1 else 0)

private theorem decideHamProg_realizes :
    Realizes .exact decideHamProg wordWords wordWords
      (fun w n s => CountHamSafe w n s ∧ Fits w 1)
      (fun _ _ => 0) := by
  unfold decideHamProg
  realize [countHamProg_realizes]
  all_goals
    obtain ⟨hc, h1⟩ := h
    first | exact hc | exact h1

private theorem maskStep_spec {w : ℕ} (I : Instance) (hfit : I.FitsWidth w)
    (ws lim k : ℕ) (hk : k < 2 ^ I.n) (s : Memory.State)
    (hws_eq : ws = I.n * I.n + 2)
    (hs_fr : s.frontier = ws + 3 * I.n)
    (hadj_s : ∀ x y : Fin I.n,
      s.mem (2 + x.1 * I.n + y.1) = if I.adj x y then 1 else 0)
    (hin_s : ∀ u : Fin I.n,
      s.mem (ws + u.1) = if k.testBit u.1 then 1 else 0) :
    let env : MaskArgs := ⟨I.n, ws, lim⟩
    let st : MaskState := ⟨evenPart I k, oddPart I k, (maskSet I.n k).card % 2⟩
    MaskStepSafe w (env, st) s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (maskStep (env, st))) ∧
      memoryCost (maskStep (env, st)) s ≤ 13 * (I.n ^ 3 + 1) ∧
      ((Memory.spec 0).clientState s (maskStep (env, st))).frontier = s.frontier ∧
      (∀ x y : Fin I.n,
        ((Memory.spec 0).clientState s (maskStep (env, st))).mem (2 + x.1 * I.n + y.1) =
          if I.adj x y then 1 else 0) ∧
      (∀ u : Fin I.n,
        ((Memory.spec 0).clientState s (maskStep (env, st))).mem (ws + u.1) =
          if (k + 1).testBit u.1 then 1 else 0) ∧
      (Memory.spec 0).clientResult s (maskStep (env, st)) =
        ⟨evenPart I (k + 1), oddPart I (k + 1), (maskSet I.n (k + 1)).card % 2⟩ := by
  intro env st
  let inB := ws
  let curB := ws + I.n
  let nextB := ws + 2 * I.n
  let S := maskSet I.n k
  have h1_fit : Fits w 1 := hfit.of_le (by unfold Instance.wordBound; omega)
  have h2_fit : Fits w 2 := hfit.of_le (by unfold Instance.wordBound; omega)
  have hws_fit : Fits w (ws + 3 * I.n) := hfit.of_le (by
    rw [hws_eq]; exact sq_add_three_n_add_two_le_wordBound I)
  have hin_fit : Fits w (inB + I.n) := hws_fit.of_le (by dsimp [inB]; omega)
  have hcur_fit : Fits w (curB + I.n) := hws_fit.of_le (by dsimp [curB]; omega)
  have hnext_fit : Fits w (nextB + I.n) := hws_fit.of_le (by dsimp [nextB]; omega)
  have hcurB_fit : Fits w curB := hws_fit.of_le (by dsimp [curB]; omega)
  have hnextB_fit : Fits w nextB := hws_fit.of_le (by dsimp [nextB]; omega)
  have hmod_fit : Fits w (I.n % 2) := h2_fit.of_le (Nat.mod_lt I.n (by decide)).le
  have hin_S : ∀ u : Fin I.n, s.mem (inB + u.1) = if u ∈ S then 1 else 0 := fun u => by
    simp only [S, mem_maskSet, inB, hin_s u]
  have hwalks_fit : Fits w (totalWalkCount I.adj S) :=
    hfit.of_le (totalWalkCount_le_wordBound I S)
  have hk1_le : k + 1 ≤ 2 ^ I.n := hk
  have hpart_k := part_le_mul I hk.le
  have hpart_k1 := part_le_mul I hk1_le
  have hpart_sum_fit :
      if I.n % 2 = (maskSet I.n k).card % 2 then
        Fits w (evenPart I k + totalWalkCount I.adj S)
      else Fits w (oddPart I k + totalWalkCount I.adj S) := by
    split_ifs with hp
    · refine hfit.of_le ?_
      have hsucc : evenPart I (k + 1) = evenPart I k + totalWalkCount I.adj S := by
        dsimp only [S]
        simp [evenPart_succ, hp.symm]
      rw [← hsucc]
      have hle := hpart_k1.1
      unfold Instance.wordBound
      omega
    · refine hfit.of_le ?_
      have hsucc : oddPart I (k + 1) = oddPart I k + totalWalkCount I.adj S := by
        dsimp only [S]
        simp [oddPart_succ, Ne.symm hp]
      rw [← hsucc]
      have hle := hpart_k1.2
      unfold Instance.wordBound
      omega
  have hdisj_ci : ∀ i < I.n, ∀ j < I.n, curB + i ≠ inB + j := fun i hi j hj => by
    dsimp [curB, inB]; omega
  have hdisj_nc : ∀ i < I.n, ∀ j < I.n, curB + i ≠ nextB + j := fun i hi j hj => by
    dsimp [curB, nextB]; omega
  have hdisj_ni : ∀ i < I.n, ∀ j < I.n, nextB + i ≠ inB + j := fun i hi j hj => by
    dsimp [nextB, inB]; omega
  have hdisj_na : ∀ i < I.n, ∀ x y : Fin I.n, nextB + i ≠ 2 + x.1 * I.n + y.1 :=
    fun i hi x y => by
      have hlt : x.1 * I.n + y.1 < I.n * I.n := Cslib.Matrix.pairIndex_lt (x, y)
      dsimp [nextB]; rw [hws_eq]; omega
  have hdisj_ca : ∀ i < I.n, ∀ x y : Fin I.n, curB + i ≠ 2 + x.1 * I.n + y.1 :=
    fun i hi x y => by
      have hlt : x.1 * I.n + y.1 < I.n * I.n := Cslib.Matrix.pairIndex_lt (x, y)
      dsimp [curB]; rw [hws_eq]; omega
  by_cases hn0 : I.n = 0
  · have htw0 : totalWalkCount I.adj S = 1 := totalWalkCount_zero_vertices hn0 I.adj S
    have hodo := odometerProg_spec I hfit k inB s (by omega) hin_fit (fun u => hin_s u)
    have hsafe_cond :
        if I.n = 0 then Fits w 1 else
          Fits w (I.n - 1) ∧
          iterationSafe copyStep CopyStepSafe w ⟨inB, curB, I.n⟩ I.n 0 s ∧
          iterationSafe roundStep RoundStepSafe w ⟨I.n, inB, curB, nextB, I.n - 1⟩
            (I.n - 1) 0 ((Memory.spec 0).clientState s (copySliceProg ⟨inB, curB, I.n⟩)) ∧
          iterationSafe sumStep SumStepSafe w ⟨curB, I.n⟩ I.n ⟨0, 0⟩
            ((Memory.spec 0).clientState
              ((Memory.spec 0).clientState s (copySliceProg ⟨inB, curB, I.n⟩))
              (roundsProg ⟨I.n, inB, curB, nextB, I.n - 1⟩)) := by
      simpa [hn0] using h1_fit
    have hsafe_odo :
        iterationSafe odoStep OdoStepSafe w ⟨inB, I.n, st.parity⟩ I.n ⟨0, 1, st.parity⟩ s :=
      hodo.1.2
    have hsafe_sum :
        if I.n % 2 = st.parity then Fits w (st.evenSum + 1) else Fits w (st.oddSum + 1) := by
      simpa [S, htw0, st] using hpart_sum_fit
    refine
      ⟨⟨h2_fit, hcurB_fit, hnextB_fit, hmod_fit, hsafe_cond, ?_, ?_, ?_⟩,
        ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [hn0, ↓reduceIte] using h1_fit
    · simpa only [hn0, ↓reduceIte, env, inB, curB, nextB] using hsafe_odo
    · simpa only [hn0, ↓reduceIte, env] using hsafe_sum
    · dsimp only [maskStep, env, st]
      rw [ite_eq_left hn0]
      refine validHistory_read_bind (by omega) ?_
      simp only [pure_bind]
      exact validHistory_bind_step hodo.2.1 (validHistory_ite (fun _ => validHistory_pure w _ _)
        (fun _ => validHistory_pure w _ _))
    · have hcost_step :
          memoryCost (maskStep (env, st)) s =
            1 + memoryCost (odometerProg ⟨ws, I.n, #(maskSet I.n k) % 2⟩) s := by
        dsimp only [maskStep, env, st]
        rw [ite_eq_left hn0]
        simp [memoryCost_bind', memoryCost_read, memoryCost_ite, memoryCost_pure, client_simps]
      have hc : memoryCost (odometerProg ⟨ws, I.n, #(maskSet I.n k) % 2⟩) s ≤ 2 * I.n :=
        hodo.2.2.1
      rw [hcost_step]
      omega
    · dsimp only [maskStep, env, st]
      rw [ite_eq_left hn0]
      simp only [client_simps]
      split_ifs <;> simpa only [client_simps] using hodo.2.2.2.1
    · intro x y
      exact Fin.elim0 (hn0 ▸ x)
    · intro u
      exact Fin.elim0 (hn0 ▸ u)
    · have hres_odo : (Memory.spec 0).clientResult s
          (odometerProg ⟨ws, I.n, #(maskSet I.n k) % 2⟩) = #(maskSet I.n (k + 1)) % 2 :=
        hodo.2.2.2.2.2.2
      dsimp only [maskStep, env, st]
      rw [ite_eq_left hn0]
      simp only [client_simps]
      dsimp only [S] at htw0
      split_ifs with hp
      · have hp' : (maskSet I.n k).card % 2 = I.n % 2 := hp.symm
        have heven : evenPart I (k + 1) = evenPart I k + 1 := by
          rw [evenPart_succ, ite_eq_left hp', htw0]
        have hodd : oddPart I (k + 1) = oddPart I k := by
          rw [oddPart_succ, ite_eq_right (not_not.2 hp'), add_zero]
        rw [heven, hodd]
        simp [hres_odo]
      · have hp' : (maskSet I.n k).card % 2 ≠ I.n % 2 := Ne.symm hp
        have heven : evenPart I (k + 1) = evenPart I k := by
          rw [evenPart_succ, ite_eq_right hp', add_zero]
        have hodd : oddPart I (k + 1) = oddPart I k + 1 := by
          rw [oddPart_succ, ite_eq_left hp', htw0]
        rw [heven, hodd]
        simp [hres_odo]
  · have hn_pos : 0 < I.n := Nat.pos_of_ne_zero hn0
    have hn1_fit : Fits w (I.n - 1) := hfit.of_le ((by omega : I.n - 1 ≤ I.n).trans
      (n_le_wordBound I))
    have hcopy := copySliceProg_spec ⟨inB, curB, I.n⟩ s
      hdisj_ci (by dsimp only [inB]; omega) (by dsimp only [curB]; omega) hin_fit hcur_fit
      (fun i hi => by
        rw [hin_s ⟨i, hi⟩]
        split_ifs
        · exact h1_fit
        · exact fits_zero w)
    let s1 := (Memory.spec 0).clientState s (copySliceProg ⟨inB, curB, I.n⟩)
    have hs1_fr : s1.frontier = s.frontier := hcopy.2.2.2.1
    have hs1_adj : ∀ x y : Fin I.n,
        s1.mem (2 + x.1 * I.n + y.1) = if I.adj x y then 1 else 0 := fun x y => by
      rw [hcopy.2.2.2.2.1 _ (fun ⟨h1, h2⟩ => by
        dsimp only at h1 h2
        exact hdisj_ca (2 + x.1 * I.n + y.1 - curB) (by dsimp only [curB]; omega) x y
          (by dsimp only [curB]; omega))]
      exact hadj_s x y
    have hs1_in : ∀ u : Fin I.n, s1.mem (inB + u.1) = if u ∈ S then 1 else 0 := fun u => by
      rw [hcopy.2.2.2.2.1 _ (fun ⟨h1, h2⟩ => by
        dsimp only at h1 h2
        have := u.isLt
        dsimp only [inB, curB] at h1
        omega)]
      exact hin_S u
    have hs1_cur0 : ∀ u : Fin I.n, s1.mem (curB + u.1) = walkCountFrom I.adj S 0 u := fun u => by
      rw [hcopy.2.2.2.2.2 u.1 u.isLt, hin_S u]
      rfl
    have hrounds := roundsProg_spec I hfit S inB curB nextB (I.n - 1) (by omega) s1
      hdisj_nc hdisj_ni hdisj_na hdisj_ci hdisj_ca
      (by omega) (by omega) (by omega) (by omega)
      hin_fit hcur_fit hnext_fit hs1_adj hs1_in hs1_cur0
    let s2 := (Memory.spec 0).clientState s1 (roundsProg ⟨I.n, inB, curB, nextB, I.n - 1⟩)
    have hs2_fr : s2.frontier = s.frontier := hrounds.2.2.2.1.trans hs1_fr
    have hs2_cur : ∀ u : Fin I.n, s2.mem (curB + u.1) = walkCountFrom I.adj S (I.n - 1) u :=
      hrounds.2.2.2.2.2
    have htw_eq : (∑ u : Fin I.n, walkCountFrom I.adj S (I.n - 1) u) = totalWalkCount I.adj S :=
      totalWalkCount_succ_vertices hn_pos I.adj S
    have hsum := sumVecProg_spec I hfit curB (walkCountFrom I.adj S (I.n - 1)) s2
      (by omega) hcur_fit hs2_cur (htw_eq ▸ hwalks_fit)
    let s3 := (Memory.spec 0).clientState s2 (sumVecProg ⟨curB, I.n⟩)
    have hs3_eq : s3 = s2 := hsum.2.2.2.1
    have hs3_in : ∀ u : Fin I.n, s3.mem (inB + u.1) = if k.testBit u.1 then 1 else 0 := fun u => by
      rw [hs3_eq]
      dsimp [s2]
      rw [hrounds.2.2.2.2.1 (inB + u.1) (by
        rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact hdisj_ci (inB + u.1 - curB) (by omega) u.1 u.isLt (by omega)
        · exact hdisj_ni (inB + u.1 - nextB) (by omega) u.1 u.isLt (by omega))]
      simpa [S, mem_maskSet] using hs1_in u
    have hodo := odometerProg_spec I hfit k inB s3
      (by rw [hs3_eq, hs2_fr]; dsimp only [inB]; omega) hin_fit hs3_in
    have hwalks_res : (Memory.spec 0).clientResult s2 (sumVecProg ⟨curB, I.n⟩) =
        totalWalkCount I.adj S := by
      rw [hsum.2.2.2.2, htw_eq]
    have hs3_unfold :
        (Memory.spec 0).clientState
          ((Memory.spec 0).clientState
            ((Memory.spec 0).clientState s (copySliceProg ⟨ws, ws + I.n, I.n⟩))
            (roundsProg ⟨I.n, ws, ws + I.n, ws + 2 * I.n, I.n - 1⟩))
          (sumVecProg ⟨ws + I.n, I.n⟩) = s3 := rfl
    have hwalks_unfold :
        (Memory.spec 0).clientResult
          ((Memory.spec 0).clientState
            ((Memory.spec 0).clientState s (copySliceProg ⟨ws, ws + I.n, I.n⟩))
            (roundsProg ⟨I.n, ws, ws + I.n, ws + 2 * I.n, I.n - 1⟩))
          (sumVecProg ⟨ws + I.n, I.n⟩) = totalWalkCount I.adj S := hwalks_res
    refine ⟨⟨h2_fit, hcurB_fit, hnextB_fit, hmod_fit, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · dsimp only [env]
      rw [ite_eq_right hn0]
      exact ⟨hn1_fit, hcopy.1, hrounds.1, hsum.1⟩
    · exact hodo.1.1
    · dsimp only [env]
      rw [ite_eq_right hn0]
      exact hodo.1.2
    · dsimp only [env]
      rw [ite_eq_right hn0, hwalks_res]
      exact hpart_sum_fit
    · dsimp only [maskStep, env]
      rw [ite_eq_right hn0]
      refine validHistory_read_bind (by omega) ?_
      dsimp only [inB, curB, nextB] at hcopy hrounds hsum hodo
      let branchProg : Memory.Prog MaskState := do
        let _ ← copySliceProg ⟨ws, ws + I.n, I.n⟩
        let _ ← roundsProg ⟨I.n, ws, ws + I.n, ws + 2 * I.n, I.n - 1⟩
        let walks ← sumVecProg ⟨ws + I.n, I.n⟩
        let newParity ← odometerProg ⟨ws, I.n, st.parity⟩
        if I.n % 2 = st.parity then
          pure ⟨st.evenSum + walks, st.oddSum, newParity⟩
        else
          pure ⟨st.evenSum, st.oddSum + walks, newParity⟩
      change (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s branchProg)
      refine validHistory_bind_step hcopy.2.1 ?_
      refine validHistory_bind_step hrounds.2.1 ?_
      refine validHistory_bind_step hsum.2.1 ?_
      exact validHistory_bind_step hodo.2.1 (validHistory_ite (fun _ => validHistory_pure w _ _)
        (fun _ => validHistory_pure w _ _))
    · simp only [maskStep, memoryCost_bind', memoryCost_read, memoryCost_ite, memoryCost_pure,
        client_simps]
      dsimp only [env]
      rw [ite_eq_right hn0]
      have hc1 := hcopy.2.2.1
      have hc2 := hrounds.2.2.1
      have hc3 := hsum.2.2.1
      have hc_odo := hodo.2.2.1
      have hmul_mono : ((2 * I.n + 2) * I.n + 2 * I.n + 1) * (I.n - 1) ≤
          ((2 * I.n + 2) * I.n + 2 * I.n + 1) * I.n :=
        Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      have hpoly : 1 + (2 * I.n + ((2 * I.n + 2) * I.n + 2 * I.n + 1) * I.n + I.n) + 2 * I.n ≤
          13 * (I.n ^ 3 + 1) := by
        have h1 : I.n ≤ I.n ^ 3 := Nat.le_self_pow (by omega) I.n
        have h2 : I.n ^ 2 ≤ I.n ^ 3 := Nat.pow_le_pow_right hn_pos (by omega)
        nlinarith
      have htot :
          1 + (memoryCost (copySliceProg ⟨inB, curB, I.n⟩) s +
            (memoryCost (roundsProg ⟨I.n, inB, curB, nextB, I.n - 1⟩) s1 +
              (memoryCost (sumVecProg ⟨curB, I.n⟩) s2 +
                (memoryCost (odometerProg ⟨inB, I.n, st.parity⟩) s3 + 0)))) ≤
            13 * (I.n ^ 3 + 1) := by
        dsimp only [CopyArgs.len] at hc1
        linarith
      dsimp only [inB, curB, nextB, s1, s2, s3] at htot
      split_ifs <;> exact htot
    · dsimp only [env, st]
      simp only [maskStep, client_simps, hn0, ↓reduceIte, hs3_unfold]
      have hodo_fr := hodo.2.2.2.1
      dsimp only [inB] at hodo_fr
      simp only [client_simps] at hodo_fr
      split_ifs <;> rw [hodo_fr, hs3_eq, hs2_fr]
    · intro x y
      dsimp only [env]
      simp only [maskStep, client_simps, hn0, ↓reduceIte, hs3_unfold]
      have hlt : x.1 * I.n + y.1 < I.n * I.n := Cslib.Matrix.pairIndex_lt (x, y)
      have hnot_in : ¬ (inB ≤ 2 + x.1 * I.n + y.1 ∧ 2 + x.1 * I.n + y.1 < inB + I.n) := by
        dsimp [inB]; rw [hws_eq]; omega
      have hs3_adj : s3.mem (2 + x.1 * I.n + y.1) = if I.adj x y then 1 else 0 := by
        rw [hs3_eq]
        dsimp [s2]
        rw [hrounds.2.2.2.2.1 (2 + x.1 * I.n + y.1) (by
          rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
          · exact hdisj_ca (2 + x.1 * I.n + y.1 - curB) (by omega) x y (by omega)
          · exact hdisj_na (2 + x.1 * I.n + y.1 - nextB) (by omega) x y (by omega))]
        exact hs1_adj x y
      have hmem_x : ((Memory.spec 0).clientState s3 (odometerProg ⟨ws, I.n, st.parity⟩)).mem
          (2 + x.1 * I.n + y.1) = s3.mem (2 + x.1 * I.n + y.1) := by
        simpa only [inB] using hodo.2.2.2.2.1 _ hnot_in
      simp only [client_simps] at hmem_x
      by_cases hp : I.n % 2 = st.parity
      · simp only [hp, ↓reduceIte]
        rw [hmem_x, hs3_adj]
      · simp only [hp, ↓reduceIte]
        rw [hmem_x, hs3_adj]
    · dsimp only [env, st]
      intro u
      simp only [maskStep, client_simps, hn0, ↓reduceIte, hs3_unfold]
      have hodo_u := hodo.2.2.2.2.2.1 u
      dsimp only [inB] at hodo_u
      by_cases hp : I.n % 2 = #(maskSet I.n k) % 2
      · simp only [hp, ↓reduceIte]; exact hodo_u
      · simp only [hp, ↓reduceIte]; exact hodo_u
    · dsimp only [env, st]
      simp only [maskStep, client_simps, hn0, ↓reduceIte, hs3_unfold, hwalks_unfold]
      have hres_odo := hodo.2.2.2.2.2.2
      dsimp only [inB] at hres_odo
      dsimp only [S]
      split_ifs with hp
      · rw [evenPart_succ, oddPart_succ, ite_eq_left hp.symm, ite_eq_right (not_not.2 hp.symm)]
        simp [hres_odo]
      · rw [evenPart_succ, oddPart_succ, ite_eq_right (Ne.symm hp), ite_eq_left (Ne.symm hp)]
        simp [hres_odo]

private theorem countHamProg_spec {w : ℕ} (I : Instance) (hfit : I.FitsWidth w) :
    let s₀ := Memory.State.init I.encode
    CountHamSafe w I.n s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (countHamProg I.n)) ∧
      memoryCost (countHamProg I.n) s₀ ≤ 16 * ((I.n ^ 3 + 1) * 2 ^ I.n) ∧
      (Memory.spec 0).clientResult s₀ (countHamProg I.n) = #(hamPaths I.adj) := by
  intro s₀
  let ws := s₀.frontier
  have hfr0 : ws = I.n * I.n + 2 := I.init_frontier
  have hs1_fit : Fits w (ws + 3 * I.n) := by
    rw [hfr0]
    exact hfit.of_le (sq_add_three_n_add_two_le_wordBound I)
  have h3_fit : Fits w 3 := hfit.of_le (by unfold Instance.wordBound; omega)
  have h3n_fit : Fits w (3 * I.n) := hs1_fit.of_le (by omega)
  let s1 : Memory.State := ⟨s₀.mem, ws + 3 * I.n⟩
  have hzero := zeroWordsProg_spec ⟨ws, I.n⟩ s1 (by dsimp only [s1]; omega)
    (hs1_fit.of_le (by dsimp only; omega))
  let s2 := (Memory.spec 0).clientState s1 (zeroWordsProg ⟨ws, I.n⟩)
  have hs2_fr : s2.frontier = ws + 3 * I.n := hzero.2.2.2.1
  have hs2_adj : ∀ x y : Fin I.n,
      s2.mem (2 + x.1 * I.n + y.1) = if I.adj x y then 1 else 0 := fun x y => by
    have hlt : x.1 * I.n + y.1 < I.n * I.n := Cslib.Matrix.pairIndex_lt (x, y)
    have hnot : ¬ (ws ≤ 2 + x.1 * I.n + y.1 ∧ 2 + x.1 * I.n + y.1 < ws + I.n) := by
      rw [hfr0]; omega
    rw [hzero.2.2.2.2.1 _ hnot]
    exact I.init_mem_adj x y
  have hs2_in0 : ∀ u : Fin I.n, s2.mem (ws + u.1) = if (0 : ℕ).testBit u.1 then 1 else 0 :=
    fun u => by
      simp only [Nat.zero_testBit, Bool.false_eq_true, ↓reduceIte]
      exact hzero.2.2.2.2.2 u.1 u.isLt
  have hpow := pow2Prog_spec I hfit s2 (by rw [hs2_fr]; omega)
  let s3 := (Memory.spec 0).clientState s2 (pow2Prog I.n)
  have hs3_eq : s3 = s2 := hpow.2.2.2.1
  have hlim_eq : (Memory.spec 0).clientResult s2 (pow2Prog I.n) = 2 ^ I.n := hpow.2.2.2.2
  have hmask_loop := iterate_spec maskStep MaskStepSafe w ⟨I.n, ws, 2 ^ I.n⟩
    (13 * (I.n ^ 3 + 1)) (2 ^ I.n)
    (fun k st s => st = ⟨evenPart I k, oddPart I k, (maskSet I.n k).card % 2⟩ ∧
      s.frontier = ws + 3 * I.n ∧
      (∀ x y : Fin I.n, s.mem (2 + x.1 * I.n + y.1) = if I.adj x y then 1 else 0) ∧
      (∀ u : Fin I.n, s.mem (ws + u.1) = if k.testBit u.1 then 1 else 0))
    (fun _ => True)
    (fun k hk st s ⟨hst, hfr_s, hadj_s, hin_s⟩ => by
      have hm := maskStep_spec I hfit ws (2 ^ I.n) k hk s hfr0 hfr_s hadj_s hin_s
      refine ⟨?_, ?_, ?_, ?_, fun _ h => absurd trivial h, ?_⟩
      · rw [hst]; exact hm.1
      · rw [hst]; exact hm.2.1
      · rw [hst]; exact hm.2.2.1
      · rw [hst]; exact hm.2.2.2.1
      · refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hst]; exact hm.2.2.2.2.2.2
        · rw [hst, hm.2.2.2.1, hfr_s]
        · rw [hst]; exact hm.2.2.2.2.1
        · rw [hst]; exact hm.2.2.2.2.2.1)
    ⟨0, 0, 0⟩ s3 ⟨by
        have hmt : maskSet I.n 0 = ∅ := by
          ext u; simp [mem_maskSet]
        simp [evenPart, oddPart, hmt],
      by rw [hs3_eq, hs2_fr],
      fun x y => by rw [hs3_eq]; exact hs2_adj x y,
      fun u => by rw [hs3_eq]; exact hs2_in0 u⟩
  have hres_eq :
      (Memory.spec 0).clientResult s3 (iterate maskStep ⟨I.n, ws, 2 ^ I.n⟩ (2 ^ I.n) ⟨0, 0, 0⟩) =
        ⟨evenPart I (2 ^ I.n), oddPart I (2 ^ I.n), (maskSet I.n (2 ^ I.n)).card % 2⟩ :=
    hmask_loop.2.2.2.2.2.1
  have hodd_le : oddPart I (2 ^ I.n) ≤ evenPart I (2 ^ I.n) := oddPart_le_evenPart I
  refine ⟨⟨hs1_fit, h3_fit, h3n_fit, hzero.1, hpow.1, ?_, ?_⟩, ?_, ?_, ?_⟩
  · dsimp only [ws] at hmask_loop
    change iterationSafe maskStep MaskStepSafe w
      ⟨I.n, s₀.frontier, (Memory.spec 0).clientResult s2 (pow2Prog I.n)⟩
      ((Memory.spec 0).clientResult s2 (pow2Prog I.n)) ⟨0, 0, 0⟩ s3
    rw [hlim_eq]
    exact hmask_loop.1
  · dsimp only [ws] at hres_eq
    change ((Memory.spec 0).clientResult s3
      (iterate maskStep ⟨I.n, s₀.frontier, (Memory.spec 0).clientResult s2 (pow2Prog I.n)⟩
        ((Memory.spec 0).clientResult s2 (pow2Prog I.n)) ⟨0, 0, 0⟩)).oddSum ≤
      ((Memory.spec 0).clientResult s3
        (iterate maskStep ⟨I.n, s₀.frontier, (Memory.spec 0).clientResult s2 (pow2Prog I.n)⟩
          ((Memory.spec 0).clientResult s2 (pow2Prog I.n)) ⟨0, 0, 0⟩)).evenSum
    rw [hlim_eq, hres_eq]
    exact hodd_le
  · refine validHistory_allocDirty_bind hs1_fit ?_
    change (Memory.spec w).ValidHistory s1 ((Memory.spec w).clientHistory s1 (do
      let _ ← zeroWordsProg ⟨ws, I.n⟩
      let lim ← pow2Prog I.n
      maskLoopProg ⟨I.n, ws, lim⟩))
    refine validHistory_bind_step hzero.2.1 ?_
    dsimp only [s2] at hpow hmask_loop ⊢
    refine validHistory_bind_step hpow.2.1 ?_
    dsimp only [maskLoopProg]
    rw [hlim_eq]
    exact validHistory_bind_step hmask_loop.2.1 (validHistory_pure w _ _)
  · simp only [countHamProg, memoryCost_bind', memoryCost_allocDirty, clientResult_allocDirty,
      maskLoopProg]
    have hc1 := hzero.2.2.1
    have hc2 := hpow.2.2.1
    have hc3 := hmask_loop.2.2.1
    dsimp only at hc1
    have h2n_pos : 1 ≤ 2 ^ I.n := Nat.one_le_two_pow
    have hlin : 1 + I.n + I.n ≤ 3 * ((I.n ^ 3 + 1) * 2 ^ I.n) := by
      have hn3 : I.n ≤ I.n ^ 3 + 1 := by
        cases h : I.n with
        | zero => omega
        | succ m =>
          have : m + 1 ≤ (m + 1) ^ 3 := Nat.le_self_pow (by omega) (m + 1)
          omega
      nlinarith
    have hmul : 13 * (I.n ^ 3 + 1) * 2 ^ I.n = 13 * ((I.n ^ 3 + 1) * 2 ^ I.n) := by ring
    change 1 + (memoryCost (zeroWordsProg ⟨ws, I.n⟩) s1 +
      (memoryCost (pow2Prog I.n) s2 +
        (memoryCost (iterate maskStep ⟨I.n, ws, (Memory.spec 0).clientResult s2 (pow2Prog I.n)⟩
          ((Memory.spec 0).clientResult s2 (pow2Prog I.n)) ⟨0, 0, 0⟩) s3 + 0))) ≤ _
    rw [hlim_eq]
    omega
  · simp only [countHamProg, StateTransitionSpec.clientResult_bind, clientResult_allocDirty,
      maskLoopProg]
    change (((Memory.spec 0).clientResult s3
      (iterate maskStep ⟨I.n, ws, (Memory.spec 0).clientResult s2 (pow2Prog I.n)⟩
        ((Memory.spec 0).clientResult s2 (pow2Prog I.n)) ⟨0, 0, 0⟩)).evenSum -
      ((Memory.spec 0).clientResult s3
        (iterate maskStep ⟨I.n, ws, (Memory.spec 0).clientResult s2 (pow2Prog I.n)⟩
          ((Memory.spec 0).clientResult s2 (pow2Prog I.n)) ⟨0, 0, 0⟩)).oddSum) = _
    rw [hlim_eq, hres_eq]
    exact evenPart_sub_oddPart_nat I

/-! ## Uniform standard-basis Word-RAM programs and `O((n³ + 1) · 2^n)` bounds -/

private theorem countProgWitness :
    ∃ r C pc : ℕ, ∃ prog : Program .standard r, ¬prog.ReadsWidth ∧
      ∃ frontier : Fin r, ∃ out : Fin 1 → Fin r,
      ∀ w d words, (∀ j : Fin 1, words.getD j.val 0 = wordWords d j) →
        1 ≤ words.length → Fits w (words.length + 1) → InputFits w words →
        CountHamSafe w d (Memory.State.init words) →
        (Memory.spec w).ValidHistory (Memory.State.init words)
          ((Memory.spec w).clientHistory (Memory.State.init words) (countHamProg d)) →
        ∃ y n, Runs w prog (State.init words) ⟨pc, y⟩ n ∧
          step w prog ⟨pc, y⟩ =
            .halt (wordWords
              ((Memory.spec w).clientResult (Memory.State.init words) (countHamProg d)) 0) ∧
          memoryState frontier y =
            (Memory.spec w).clientState (Memory.State.init words) (countHamProg d) ∧
          (∀ j, y.regs (out j) =
            wordWords ((Memory.spec w).clientResult (Memory.State.init words) (countHamProg d)) j) ∧
          n + 1 ≤ C * (memoryCost (countHamProg d) (Memory.State.init words) + 0 + 1) + 1 :=
  countHamProg_realizes.exists_standard_basis_init_program_state_from_words (0 : Fin 1)

private theorem decideProgWitness :
    ∃ r C pc : ℕ, ∃ prog : Program .standard r, ¬prog.ReadsWidth ∧
      ∃ frontier : Fin r, ∃ out : Fin 1 → Fin r,
      ∀ w d words, (∀ j : Fin 1, words.getD j.val 0 = wordWords d j) →
        1 ≤ words.length → Fits w (words.length + 1) → InputFits w words →
        (CountHamSafe w d (Memory.State.init words) ∧ Fits w 1) →
        (Memory.spec w).ValidHistory (Memory.State.init words)
          ((Memory.spec w).clientHistory (Memory.State.init words) (decideHamProg d)) →
        ∃ y n, Runs w prog (State.init words) ⟨pc, y⟩ n ∧
          step w prog ⟨pc, y⟩ =
            .halt (wordWords
              ((Memory.spec w).clientResult (Memory.State.init words) (decideHamProg d)) 0) ∧
          memoryState frontier y =
            (Memory.spec w).clientState (Memory.State.init words) (decideHamProg d) ∧
          (∀ j, y.regs (out j) =
            wordWords
              ((Memory.spec w).clientResult (Memory.State.init words) (decideHamProg d)) j) ∧
          n + 1 ≤ C * (memoryCost (decideHamProg d) (Memory.State.init words) + 0 + 1) + 1 :=
  decideHamProg_realizes.exists_standard_basis_init_program_state_from_words (0 : Fin 1)

/-- Number of registers used by `program`. -/
noncomputable def countRegs : ℕ := countProgWitness.choose

/-- Standard-basis width-blind Word-RAM program computing `#(hamPaths I.adj)` in
`O((I.n ^ 3 + 1) * 2 ^ I.n)` instructions. -/
noncomputable def program : Program .standard countRegs :=
  countProgWitness.choose_spec.choose_spec.choose_spec.choose

/-- Constant factor in `computesInTime_program`. -/
noncomputable def countTimeFactor : ℕ :=
  17 * countProgWitness.choose_spec.choose + 1

/-- Number of registers used by `decideProgram`. -/
noncomputable def decideRegs : ℕ := decideProgWitness.choose

/-- Standard-basis width-blind Word-RAM program deciding `(hamPaths I.adj).Nonempty` (`1` or `0`)
in `O((I.n ^ 3 + 1) * 2 ^ I.n)` instructions. -/
noncomputable def decideProgram : Program .standard decideRegs :=
  decideProgWitness.choose_spec.choose_spec.choose_spec.choose

/-- Constant factor in `computesInTime_decideProgram`. -/
noncomputable def decideTimeFactor : ℕ :=
  17 * decideProgWitness.choose_spec.choose + 1

/-- `program` never reads the machine word size (`¬ReadsWidth`). -/
theorem not_readsWidth_program : ¬ program.ReadsWidth :=
  countProgWitness.choose_spec.choose_spec.choose_spec.choose_spec.1

/-- `decideProgram` never reads the machine word size (`¬ReadsWidth`). -/
theorem not_readsWidth_decideProgram : ¬ decideProgram.ReadsWidth :=
  decideProgWitness.choose_spec.choose_spec.choose_spec.choose_spec.1

/-- Standard-basis `Program.ComputesInTime` certificate for `program`: computes
`#(hamPaths I.adj)` on `I.encode` in `O((I.n ^ 3 + 1) * 2 ^ I.n)` instructions at every word
width `w` satisfying `I.FitsWidth w` (`O(n log n)` bits). -/
theorem computesInTime_program :
    program.ComputesInTime (fun _ => Instance.encode)
      (fun I _ => countTimeFactor * ((I.n ^ 3 + 1) * 2 ^ I.n))
      Instance.FitsWidth (fun I => #(hamPaths I.adj)) := by
  intro I w hfit _
  obtain ⟨frontier, out, he⟩ :=
    countProgWitness.choose_spec.choose_spec.choose_spec.choose_spec.2
  have hspec := countHamProg_spec I hfit
  have hfit_len : Fits w (I.encode.length + 1) := by
    rw [I.length_encode]
    exact hfit.of_le (by have := sq_add_three_n_add_two_le_wordBound I; omega)
  obtain ⟨y, steps, hruns, hhalt, _, _, hbound⟩ :=
    he w I.n I.encode (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j)
      (by simp) hfit_len (I.inputFits hfit) hspec.1 hspec.2.1
  refine ⟨steps + 1, ⟨⟨_, y⟩, steps, hruns, ?_, rfl⟩, ?_⟩
  · rw [clientResult_width, hspec.2.2.2] at hhalt
    exact hhalt
  · have hm : memoryCost (countHamProg I.n) (Memory.State.init I.encode) ≤
        16 * ((I.n ^ 3 + 1) * 2 ^ I.n) := hspec.2.2.1
    have hpos : 1 ≤ (I.n ^ 3 + 1) * 2 ^ I.n := Nat.mul_pos (by omega) Nat.one_le_two_pow
    dsimp only [countTimeFactor]
    nlinarith

/-- Standard-basis `Program.ComputesInTime` certificate for `decideProgram`: decides
`(hamPaths I.adj).Nonempty` (`1` iff nonempty, `0` otherwise) on `I.encode` in
`O((I.n ^ 3 + 1) * 2 ^ I.n)` instructions at every word width `w` satisfying `I.FitsWidth w`
(`O(n log n)` bits). -/
theorem computesInTime_decideProgram :
    decideProgram.ComputesInTime (fun _ => Instance.encode)
      (fun I _ => decideTimeFactor * ((I.n ^ 3 + 1) * 2 ^ I.n))
      Instance.FitsWidth (fun I => if (hamPaths I.adj).Nonempty then 1 else 0) := by
  intro I w hfit _
  obtain ⟨frontier, out, he⟩ :=
    decideProgWitness.choose_spec.choose_spec.choose_spec.choose_spec.2
  have hspec := countHamProg_spec I hfit
  have h1_fit : Fits w 1 := hfit.of_le (by unfold Instance.wordBound; omega)
  have hfit_len : Fits w (I.encode.length + 1) := by
    rw [I.length_encode]
    exact hfit.of_le (by have := sq_add_three_n_add_two_le_wordBound I; omega)
  have hvalid_dec : (Memory.spec w).ValidHistory (Memory.State.init I.encode)
      ((Memory.spec w).clientHistory (Memory.State.init I.encode) (decideHamProg I.n)) :=
    validHistory_bind_step hspec.2.1 (validHistory_pure w _ _)
  obtain ⟨y, steps, hruns, hhalt, _, _, hbound⟩ :=
    he w I.n I.encode (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j)
      (by simp) hfit_len (I.inputFits hfit) ⟨hspec.1, h1_fit⟩ hvalid_dec
  have hres_dec : (Memory.spec w).clientResult (Memory.State.init I.encode) (decideHamProg I.n) =
      if (hamPaths I.adj).Nonempty then 1 else 0 := by
    rw [clientResult_width]
    simp only [decideHamProg, StateTransitionSpec.clientResult_bind,
      StateTransitionSpec.clientResult_pure, hspec.2.2.2, Finset.card_pos]
  refine ⟨steps + 1, ⟨⟨_, y⟩, steps, hruns, ?_, rfl⟩, ?_⟩
  · rw [hres_dec] at hhalt
    exact hhalt
  · have hm : memoryCost (decideHamProg I.n) (Memory.State.init I.encode) ≤
        16 * ((I.n ^ 3 + 1) * 2 ^ I.n) := by
      simp only [decideHamProg, memoryCost_bind', memoryCost_pure, add_zero]
      exact hspec.2.2.1
    have hpos : 1 ≤ (I.n ^ 3 + 1) * 2 ^ I.n := Nat.mul_pos (by omega) Nat.one_le_two_pow
    dsimp only [decideTimeFactor]
    nlinarith

end Cslib.Algorithms.WordRAM.HamiltonianCount
