/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.BitString.Binary
import CslibFrontier.Algorithms.WordRAM.TrimmedYates.TrieRep

/-!
# Bitmasks, trie views, caller registers, and envelopes for trimmed Yates on the word RAM

Shared data definitions and semantic invariants for the Word-RAM implementation of selected entries
of covering product and ranked subset convolution ([ChanItakuraMaYu2026], Theorem 2.2):

* `setMask`: unsigned `d`-bit word representation of `S : Finset (Fin d)`.
* `HoldsTrie`: read-only bounded view of depth-`d` binary tries in flat word memory.
* `numRegs` and `Reg.*`: caller-facing register ABI over the `56`-register bank.
* `lowCount`, `highCount`, `highPeak`, `valueEnvelope`, `solveSpace`: combinatorial domain counts
  and explicit space and word-width envelopes.

## Main definitions

* `Cslib.Algorithms.WordRAM.TrimmedYates.setMask`: `d`-bit unsigned mask of `S : Finset (Fin d)`.
* `Cslib.Algorithms.WordRAM.TrimmedYates.HoldsTrie`: bounded read-only depth-`d` binary trie
  predicate.
* `Cslib.Algorithms.WordRAM.TrimmedYates.numRegs`: total register count (`56`).
* `Cslib.Algorithms.WordRAM.TrimmedYates.lowCount`, `highCount`, `highPeak`, `valueEnvelope`,
  `solveSpace`: combinatorial table sizes and explicit space/width envelopes.

## Main results

* `Cslib.Algorithms.WordRAM.TrimmedYates.setMask_lt`, `testBit_setMask`, `setMask_injective`,
  `setMask_insert`, `setMask_erase`, `setMask_sdiff`: bit-level characterizations of `setMask`.
* `Cslib.Algorithms.WordRAM.TrimmedYates.HoldsTrie.mono_bound`, `HoldsTrie.congr_below`,
  `HoldsTrie.zero_root`: address-bound monotonicity, memory framing, and empty-root rules.
* `Cslib.Algorithms.WordRAM.TrimmedYates.lowCount_pos`, `sum_range_sub_eq_highCount`,
  `highCount_pos`, `le_highPeak_of_mem`, `highPeak_le_of_forall_card_eq`: combinatorial bounds on
  low and high subset domains.

## References

* [T. M. Chan, R. Itakura, Z. Ma, Y. Yu, *3SUM Made Simpler (Without Matrix Multiplication),
  k-SUM Hypothesis Refuted for Odd k, and Real 3SUM/APSP Derandomized*][ChanItakuraMaYu2026]
-/

public section

namespace Cslib.Algorithms.WordRAM.TrimmedYates

open Finset Cslib.BitString

/-! ### Bitmasks of subsets of `Fin d` -/

/-- Unsigned `d`-bit mask of `S ⊆ Fin d`, with bit `i` set iff `i ∈ S`. -/
@[expose] def setMask {d : ℕ} (S : Finset (Fin d)) : ℕ :=
  (BitString.equivFin d fun i => decide (i ∈ S)).val

theorem setMask_lt {d : ℕ} (S : Finset (Fin d)) : setMask S < 2 ^ d :=
  (BitString.equivFin d fun i => decide (i ∈ S)).isLt

@[simp] theorem testBit_setMask {d : ℕ} (S : Finset (Fin d)) (i : Fin d) :
    (setMask S).testBit i.val = decide (i ∈ S) :=
  BitString.testBit_equivFin (fun j => decide (j ∈ S)) i

theorem testBit_setMask_of_ge {d : ℕ} (S : Finset (Fin d)) {k : ℕ} (hk : d ≤ k) :
    (setMask S).testBit k = false :=
  Nat.testBit_lt_two_pow ((setMask_lt S).trans_le (Nat.pow_le_pow_right Nat.two_pos hk))

theorem setMask_injective {d : ℕ} : Function.Injective (setMask (d := d)) := fun _ _ h => by
  ext i
  simpa only [decide_eq_decide] using congrFun ((BitString.equivFin d).injective (Fin.ext h)) i

@[simp] theorem setMask_empty (d : ℕ) : setMask (∅ : Finset (Fin d)) = 0 := by
  simp [setMask]

theorem setMask_insert {d : ℕ} {S : Finset (Fin d)} {c : Fin d} :
    setMask (insert c S) = setMask S ||| (1 <<< c.val) := by
  refine Nat.eq_of_testBit_eq fun k => ?_
  rw [Nat.testBit_or, Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]
  by_cases hk : k < d
  · rw [show k = (⟨k, hk⟩ : Fin d).val from rfl, testBit_setMask, testBit_setMask]
    by_cases hck : c = ⟨k, hk⟩
    · subst hck; simp
    · simp [Ne.symm hck, Fin.val_ne_of_ne hck]
  · simp [testBit_setMask_of_ge _ (Nat.le_of_not_lt hk), (c.isLt.trans_le (not_lt.mp hk)).ne]

theorem setMask_erase {d : ℕ} {S : Finset (Fin d)} {c : Fin d} (hc : c ∈ S) :
    setMask (S.erase c) = setMask S ^^^ (1 <<< c.val) := by
  refine Nat.eq_of_testBit_eq fun k => ?_
  rw [Nat.testBit_xor, Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]
  by_cases hk : k < d
  · rw [show k = (⟨k, hk⟩ : Fin d).val from rfl, testBit_setMask, testBit_setMask]
    by_cases hck : c = ⟨k, hk⟩
    · subst hck; simp [hc]
    · simp [Finset.mem_erase, Ne.symm hck, Fin.val_ne_of_ne hck]
  · simp [testBit_setMask_of_ge _ (Nat.le_of_not_lt hk), (c.isLt.trans_le (not_lt.mp hk)).ne]

theorem setMask_sdiff {d : ℕ} {C Y : Finset (Fin d)} (hY : Y ⊆ C) :
    setMask (C \ Y) = setMask C ^^^ setMask Y := by
  refine Nat.eq_of_testBit_eq fun k => ?_
  rw [Nat.testBit_xor]
  by_cases hk : k < d
  · rw [show k = (⟨k, hk⟩ : Fin d).val from rfl, testBit_setMask, testBit_setMask, testBit_setMask]
    by_cases hy : (⟨k, hk⟩ : Fin d) ∈ Y
    · simp [Finset.mem_sdiff, hy, hY hy]
    · simp [Finset.mem_sdiff, hy]
  · simp [testBit_setMask_of_ge _ (Nat.le_of_not_lt hk)]

/-! ### Depth-`d` binary tries in flat word memory -/

/-- Read-only view of a depth-`d` trie whose nodes all lie in `Ico 1 bound`. -/
def HoldsTrie (mem : ℕ → ℕ) (bound d root : ℕ) (fn : ℕ → ℕ) : Prop :=
  ∃ S ⊆ Set.Ico 1 bound, TrieRep mem d root S fn

/-- Enlarging the address bound preserves `HoldsTrie`. -/
theorem HoldsTrie.mono_bound {mem : ℕ → ℕ} {b b' d root : ℕ} {fn : ℕ → ℕ}
    (h : HoldsTrie mem b d root fn) (hbb : b ≤ b') : HoldsTrie mem b' d root fn := by
  obtain ⟨S, hS, ht⟩ := h
  exact ⟨S, fun a ha => ⟨(hS ha).1, (hS ha).2.trans_le hbb⟩, ht⟩

/-- Memory writes strictly at or above `bound` preserve `HoldsTrie`. -/
theorem HoldsTrie.congr_below {mem mem' : ℕ → ℕ} {bound d root : ℕ} {fn : ℕ → ℕ}
    (h : HoldsTrie mem bound d root fn) (heq : ∀ a < bound, mem' a = mem a) :
    HoldsTrie mem' bound d root fn := by
  obtain ⟨S, hS, ht⟩ := h
  exact ⟨S, hS, ht.congr_mem fun a ha => heq a (hS ha).2⟩

/-- Address `0` represents the identically zero depth-`d` table without allocating nodes. -/
theorem HoldsTrie.zero_root (mem : ℕ → ℕ) (bound d : ℕ) :
    HoldsTrie mem bound d 0 (fun _ => 0) := by
  exact ⟨∅, Set.empty_subset _, TrieRep.zero_root mem d⟩

/-! ### Caller-facing register ABI -/

/-- Total register count (`47` algorithm registers above the `9`-register `WordRAM.Signed` bank). -/
abbrev numRegs : ℕ := 56

namespace Reg

/-- Input register holding universe dimension `d` for `buildInputTrie` and `solveFromTries`. -/
abbrev dim : Fin numRegs := ⟨11, by decide⟩
/-- Input register holding trimming threshold `s` for `solveFromTries`. -/
abbrev thresh : Fin numRegs := ⟨12, by decide⟩
/-- Input/output register holding the bump-allocation pointer for `buildInputTrie` and
`solveFromTries`. -/
abbrev free : Fin numRegs := ⟨13, by decide⟩
/-- Output register holding the length-prefixed answer array header address. -/
abbrev outPtr : Fin numRegs := ⟨15, by decide⟩
/-- Input register holding the base address of `(setMask S, Signed.encode v)` entry pairs for
`buildInputTrie`. -/
abbrev entryPtr : Fin numRegs := ⟨33, by decide⟩
/-- Input register holding the number of sparse `(S, v)` entries for `buildInputTrie`. -/
abbrev entryCount : Fin numRegs := ⟨34, by decide⟩
/-- Output register receiving the allocated root address of `buildInputTrie`. -/
abbrev builtRoot : Fin numRegs := ⟨43, by decide⟩
/-- Input register holding the depth-`d` trie root for `f` (`0` for the identically zero table). -/
abbrev trieF : Fin numRegs := ⟨44, by decide⟩
/-- Input register holding the depth-`d` trie root for `g` (`0` for the identically zero table). -/
abbrev trieG : Fin numRegs := ⟨45, by decide⟩
/-- Input register holding the base address of the query-mask array. -/
abbrev queryPtr : Fin numRegs := ⟨46, by decide⟩
/-- Input register holding the number of queries. -/
abbrev queryCount : Fin numRegs := ⟨47, by decide⟩

end Reg

/-! ### Combinatorial counts and workspace/value envelopes -/

/-- Number of subsets of `Fin d` of size at most `s`: `∑_{j = 0}^s C(d, j)`. -/
@[expose] def lowCount (d s : ℕ) : ℕ :=
  ∑ j ∈ range (s + 1), d.choose j

/-- Number of subsets of an `m`-element set of size at least `s`: `∑_{j = s}^m C(m, j)`. -/
@[expose] def highCount (m s : ℕ) : ℕ :=
  ∑ j ∈ Icc s m, m.choose j

/-- Peak high-subset domain size across a list of queries. -/
@[expose] def highPeak {d : ℕ} (s : ℕ) (Cs : List (Finset (Fin d))) : ℕ :=
  Cs.foldr (fun C acc => max (highCount #C s) acc) 0

/-- Envelope for signed arithmetic and `d`-bit masks at universe dimension `d` and input weight
bound `W`: `8 * (8 ^ d * (W + 1) ^ 2) + 4`. -/
@[expose] def valueEnvelope (d W : ℕ) : ℕ :=
  8 * (8 ^ d * (W + 1) ^ 2) + 4

/-- Workspace upper bound for `solveFromTries` starting from bump pointer `baseFree`. -/
@[expose] def solveSpace (baseFree d s nQ H : ℕ) : ℕ :=
  baseFree + s + nQ + 8 * (d + 1) ^ 2 * (lowCount d s + H + 4)

theorem lowCount_pos (d s : ℕ) : 1 ≤ lowCount d s := by
  rw [lowCount, Finset.sum_range_succ']
  simp only [Nat.choose_zero_right]
  omega

theorem sum_range_sub_eq_highCount {m s : ℕ} (hs : s ≤ m) :
    ∑ j ∈ range (m - s + 1), m.choose j = highCount m s := by
  rw [highCount]
  refine Finset.sum_nbij' (fun j => m - j) (fun j => m - j) ?_ ?_ ?_ ?_ ?_
  · intro j hj; simp only [mem_range, mem_Icc] at hj ⊢; omega
  · intro k hk; simp only [mem_range, mem_Icc] at hk ⊢; omega
  · intro j hj; simp only [mem_range] at hj; omega
  · intro k hk; simp only [mem_Icc] at hk; omega
  · intro j hj
    simp only [mem_range] at hj
    exact (Nat.choose_symm (by omega)).symm

theorem highCount_pos {m s : ℕ} (hs : s ≤ m) : 1 ≤ highCount m s := by
  rw [← sum_range_sub_eq_highCount hs, Finset.sum_range_succ']
  simp only [Nat.choose_zero_right]
  omega

theorem le_highPeak_of_mem {d : ℕ} (s : ℕ) {Cs : List (Finset (Fin d))} {C : Finset (Fin d)}
    (hC : C ∈ Cs) : highCount #C s ≤ highPeak s Cs := by
  induction Cs with
  | nil => simp at hC
  | cons D Ds ih =>
    simp only [highPeak, List.foldr_cons]
    rcases List.mem_cons.mp hC with rfl | hDs
    · exact le_max_left _ _
    · exact (ih hDs).trans (le_max_right _ _)

theorem highPeak_le_of_forall_card_eq {d : ℕ} (s m : ℕ) {Cs : List (Finset (Fin d))}
    (hCs : ∀ C ∈ Cs, #C = m) : highPeak s Cs ≤ highCount m s := by
  induction Cs with
  | nil => simp [highPeak]
  | cons C Ds ih =>
    simp only [highPeak, List.foldr_cons, max_le_iff]
    rw [hCs C List.mem_cons_self]
    exact ⟨le_rfl, ih fun D hD => hCs D (List.mem_cons_of_mem C hD)⟩

end Cslib.Algorithms.WordRAM.TrimmedYates
