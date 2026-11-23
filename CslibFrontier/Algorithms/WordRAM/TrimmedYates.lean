/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.TrimmedYates
public import CslibFrontier.Computability.WordRAM.ListOutput
public import CslibFrontier.Computability.WordRAM.Signed.Arithmetic
public import CslibFrontier.Foundations.Data.BitString.Binary
import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.InputArray
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Selected entries of ranked subset convolution on the word RAM

Word-RAM implementation and running-time bound for [ChanItakuraMaYu2026], Theorem 2.2
(Section 2.1): given sparse integer-weighted set functions `f` and `g` on `Fin d` supported on
sets of sizes `t₁` and `t₂` (with `t₁ = t₂ = t` in Theorem 2.2) and query sets `Cs` of size
`t₁ + t₂`, compute `[subsetConvolution f g C | C ∈ Cs]` using trimmed fast zeta and Möbius passes
at threshold `s ≤ t₁ + t₂`.

Every operation left uncharged in a unit-cost cell model is implemented and charged as concrete
`Basis.standard` instructions:

* **Set representation (`setMask`):** subsets of `Fin d` are `d`-bit unsigned words below `2 ^ d`.
* **Bounded-cardinality enumeration:** subsets of `m` coordinates of size at most `k` are generated
  coordinate-by-coordinate in `O((m + 1) · ∑_{j ≤ k} C(m, j))` instructions, giving both the low
  sets (`#X ≤ s`) in preprocessing and, via complementation in `C`, the high subsets (`X ⊆ C`,
  `s ≤ #X`) in each query without scanning `2 ^ d` masks.
* **Deterministic `O(d + 1)` dictionaries:** stage tables and sparse input tables are binary tries
  of depth `d` in flat word memory, initialized explicitly on allocation so no zeroed-scratch
  assumption is needed across queries.
* **Signed ring arithmetic:** integer weights and intermediate Möbius values use
  `Cslib.WordRAM.Signed` (`add`, `subtract`, `multiply`).

## Main definitions

* `Cslib.Algorithms.WordRAM.TrimmedYates.setMask`: `d`-bit unsigned mask of `S : Finset (Fin d)`.
* `Cslib.Algorithms.WordRAM.TrimmedYates.HoldsTrie`: read-only depth-`d` binary trie representation.
* `Cslib.Algorithms.WordRAM.TrimmedYates.lowCount`, `highCount`, `highPeak`, `solveSpace`,
  `valueEnvelope`: combinatorial table sizes and explicit word-width envelopes.
* `Cslib.Algorithms.WordRAM.TrimmedYates.Instance`, `evalEntries`: sparse weighted set-function
  problem instances over `Fin d` and their mathematical semantics.
* `Cslib.Algorithms.WordRAM.TrimmedYates.buildInputTrie`, `solveFromTries`, `program`: sparse
  input-trie builder, subroutine from pre-built input tries, and complete initialized flat
  `Program .standard 56`.

## Main results

* `Cslib.Algorithms.WordRAM.TrimmedYates.exec_buildInputTrie`, `exec_solveFromTries`,
  `exec_solveFromTries_subsetConvolution`: builds sparse input tries in `O(d · |es|)` instructions
  and, from pre-built input tries, answers all queries within
  `O((d + 1)² · (∑_{j ≤ s} C(d, j) + |Cs| · ∑_{s ≤ j ≤ 2t} C(2t, j)))` instructions.
* `Cslib.Algorithms.WordRAM.TrimmedYates.computesListInTime_program`, `executesList_program`:
  complete flat-program Theorem 2.2 bound
  `O((d + 1)² · (n + ∑_{j ≤ s} C(d, j) + |Cs| · ∑_{s ≤ j ≤ 2t} C(2t, j)))` from
  `State.init inst.encode`, charging sparse input insertion, domain enumeration, trie indexing,
  signed arithmetic, and the final `halt`.

## References

* [A. Björklund, T. Husfeldt, P. Kaski, M. Koivisto, *Fourier meets Möbius: fast subset
  convolution*][BjorklundHusfeldtKaskiKoivisto2007]
* [A. Björklund, T. Husfeldt, P. Kaski, M. Koivisto, *Trimmed Moebius inversion and graphs of
  bounded degree*][BjorklundHusfeldtKaskiKoivisto2010]
* [T. M. Chan, R. Itakura, Z. Ma, Y. Yu, *3SUM Made Simpler (Without Matrix Multiplication),
  k-SUM Hypothesis Refuted for Odd k, and Real 3SUM/APSP Derandomized*][ChanItakuraMaYu2026]
-/

public section

namespace Cslib.Algorithms.WordRAM.TrimmedYates

open Finset Cslib.BitString Cslib.WordRAM Cslib.Algorithms.Lean.TrimmedYates

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

theorem setMask_injective {d : ℕ} : Function.Injective (setMask (d := d)) := by
  intro S₁ S₂ h
  have heq := (BitString.equivFin d).injective (Fin.ext h)
  ext i
  have hi := congrFun heq i
  simpa only [decide_eq_decide] using hi

@[simp] theorem setMask_empty (d : ℕ) : setMask (∅ : Finset (Fin d)) = 0 := by
  simp [setMask]

theorem setMask_insert {d : ℕ} {S : Finset (Fin d)} {c : Fin d} :
    setMask (insert c S) = setMask S ||| (1 <<< c.val) := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_or, Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]
  by_cases hk : k < d
  · let ik : Fin d := ⟨k, hk⟩
    have hik : k = ik.val := rfl
    rw [hik, testBit_setMask, testBit_setMask]
    by_cases hck : c = ik
    · subst hck; simp
    · have hne : c.val ≠ ik.val := fun h => hck (Fin.ext h)
      simp [Ne.symm hck, hne]
  · have hne : c.val ≠ k := by omega
    simp [testBit_setMask_of_ge _ (Nat.le_of_not_lt hk), hne]

theorem setMask_erase {d : ℕ} {S : Finset (Fin d)} {c : Fin d} (hc : c ∈ S) :
    setMask (S.erase c) = setMask S ^^^ (1 <<< c.val) := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_xor, Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]
  by_cases hk : k < d
  · let ik : Fin d := ⟨k, hk⟩
    have hik : k = ik.val := rfl
    rw [hik, testBit_setMask, testBit_setMask]
    by_cases hck : c = ik
    · subst hck; simp [hc]
    · have hne : c.val ≠ ik.val := fun h => hck (Fin.ext h)
      simp [Finset.mem_erase, Ne.symm hck, hne]
  · have hne : c.val ≠ k := by omega
    simp [testBit_setMask_of_ge _ (Nat.le_of_not_lt hk), hne]

theorem setMask_sdiff {d : ℕ} {C Y : Finset (Fin d)} (hY : Y ⊆ C) :
    setMask (C \ Y) = setMask C ^^^ setMask Y := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_xor]
  by_cases hk : k < d
  · let ik : Fin d := ⟨k, hk⟩
    have hik : k = ik.val := rfl
    rw [hik, testBit_setMask, testBit_setMask, testBit_setMask]
    by_cases hy : ik ∈ Y
    · simp [Finset.mem_sdiff, hy, hY hy]
    · simp [Finset.mem_sdiff, hy]
  · simp [testBit_setMask_of_ge _ (Nat.le_of_not_lt hk)]

/-! ### Pure model of coordinate-by-coordinate subset enumeration -/

/-- Subsets of `coords` of cardinality at most `k`, built coordinate by coordinate in the exact
order produced by `genLowSubsets`. -/
private def prefixesUpTo {d : ℕ} (k : ℕ) (coords : List (Fin d)) : List (Finset (Fin d)) :=
  coords.foldl (fun acc c => acc ++ (acc.filter fun S => decide (#S < k)).map (insert c)) [∅]

private theorem prefixesUpTo_append_singleton {d : ℕ} (k : ℕ) (coords : List (Fin d)) (c : Fin d) :
    prefixesUpTo k (coords ++ [c]) =
      let prev := prefixesUpTo k coords
      prev ++ (prev.filter fun S => decide (#S < k)).map (insert c) :=
  List.foldl_append

private theorem prefixesUpTo_spec {d : ℕ} (k : ℕ) :
    ∀ {coords : List (Fin d)}, coords.Nodup →
      (prefixesUpTo k coords).Nodup ∧
      ∀ S, S ∈ prefixesUpTo k coords ↔ S ⊆ coords.toFinset ∧ #S ≤ k := by
  intro coords
  induction coords using List.reverseRecOn with
  | nil =>
    intro _
    simp [prefixesUpTo]
  | append_singleton coords c ih =>
    intro hnd
    have hc_not : c ∉ coords := by
      intro hc
      exact (List.nodup_append.mp hnd).2.2 c hc c (by simp) rfl
    have hnd_prev : coords.Nodup := (List.nodup_append.mp hnd).1
    obtain ⟨hprev_nd, hprev_mem⟩ := ih hnd_prev
    rw [prefixesUpTo_append_singleton]
    dsimp only
    set prev := prefixesUpTo k coords
    have hc_not_in_prev : ∀ S ∈ prev, c ∉ S := fun S hS hcS =>
      hc_not (List.mem_toFinset.mp (((hprev_mem S).mp hS).1 hcS))
    have hmap_nd : ((prev.filter fun S => decide (#S < k)).map (insert c)).Nodup := by
      refine (hprev_nd.filter _).map_on ?_
      intro S₁ h₁ S₂ h₂ heq
      have h₁m := (List.mem_filter.mp h₁).1
      have h₂m := (List.mem_filter.mp h₂).1
      have h₁c := hc_not_in_prev S₁ h₁m
      have h₂c := hc_not_in_prev S₂ h₂m
      ext x
      by_cases hxc : x = c
      · subst hxc; simp [h₁c, h₂c]
      · have hx := Finset.ext_iff.mp heq x
        simpa [Finset.mem_insert, hxc] using hx
    refine ⟨List.nodup_append.mpr ⟨hprev_nd, hmap_nd, ?_⟩, fun S => ?_⟩
    · intro S₁ h₁ S₂ h₂ heq
      rcases List.mem_map.mp h₂ with ⟨T, _, rfl⟩
      exact hc_not_in_prev S₁ h₁ (heq ▸ Finset.mem_insert_self c T)
    · simp only [List.mem_append, List.mem_map, List.mem_filter, decide_eq_true_eq,
        List.toFinset_append, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
        union_singleton]
      constructor
      · rintro (hS | ⟨T, ⟨hT, hTk⟩, rfl⟩)
        · obtain ⟨hsub, hcard⟩ := (hprev_mem S).mp hS
          exact ⟨hsub.trans (subset_insert c _), hcard⟩
        · obtain ⟨hsub, _⟩ := (hprev_mem T).mp hT
          rw [card_insert_of_notMem (hc_not_in_prev T hT)]
          exact ⟨insert_subset_insert c hsub, by omega⟩
      · rintro ⟨hsub, hcard⟩
        by_cases hcS : c ∈ S
        · right
          refine ⟨S.erase c, ⟨(hprev_mem _).mpr ⟨?_, ?_⟩, ?_⟩, insert_erase hcS⟩
          · intro x hx
            have hxS := mem_of_mem_erase hx
            have hne := ne_of_mem_erase hx
            exact (Finset.mem_insert.mp (hsub hxS)).resolve_left hne
          · exact card_erase_le.trans hcard
          · rw [card_erase_of_mem hcS]
            have := Finset.card_pos.mpr ⟨c, hcS⟩
            omega
        · left
          refine (hprev_mem S).mpr ⟨fun x hx => ?_, hcard⟩
          exact (Finset.mem_insert.mp (hsub hx)).resolve_left fun h => hcS (h ▸ hx)

private theorem length_prefixesUpTo {d : ℕ} :
    ∀ (k : ℕ) {coords : List (Fin d)}, coords.Nodup →
      (prefixesUpTo k coords).length = ∑ j ∈ range (k + 1), coords.length.choose j := by
  intro k coords
  induction coords using List.reverseRecOn generalizing k with
  | nil =>
    intro _
    rw [Finset.sum_range_succ']
    simp [prefixesUpTo]
  | append_singleton coords c ih =>
    intro hnd
    have hnd_prev : coords.Nodup := (List.nodup_append.mp hnd).1
    rw [prefixesUpTo_append_singleton]
    dsimp only
    rw [List.length_append, List.length_map, List.length_append, List.length_singleton]
    rcases k with _ | k
    · have hflt : (prefixesUpTo 0 coords).filter (fun S => decide (#S < 0)) = [] := by
        simp
      rw [hflt, List.length_nil, add_zero, ih 0 hnd_prev]
      simp
    · obtain ⟨hp_nd, hp_mem⟩ := prefixesUpTo_spec (k + 1) hnd_prev
      obtain ⟨hk_nd, hk_mem⟩ := prefixesUpTo_spec k hnd_prev
      have hflt_eq : ((prefixesUpTo (k + 1) coords).filter fun S => decide (#S < k + 1)).length =
          (prefixesUpTo k coords).length := by
        rw [← List.toFinset_card_of_nodup (hp_nd.filter _), ← List.toFinset_card_of_nodup hk_nd]
        congr 1
        ext S
        simp only [List.mem_toFinset, List.mem_filter, hp_mem, hk_mem, decide_eq_true_eq]
        exact ⟨fun ⟨⟨hsub, _⟩, hlt⟩ => ⟨hsub, by omega⟩,
          fun ⟨hsub, hle⟩ => ⟨⟨hsub, by omega⟩, by omega⟩⟩
      rw [hflt_eq, ih (k + 1) hnd_prev, ih k hnd_prev, Finset.sum_range_succ' _ (k + 1)]
      simp only [Nat.choose_zero_right]
      have hsum : ∑ j ∈ range (k + 1), coords.length.choose (j + 1) +
          ∑ j ∈ range (k + 1), coords.length.choose j =
          ∑ j ∈ range (k + 1), (coords.length + 1).choose (j + 1) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [add_comm, Nat.choose_succ_succ]
      rw [Finset.sum_range_succ' _ (k + 1)]
      simp only [Nat.choose_zero_right]
      omega

/-! ### Depth-`d` binary tries in flat word memory -/

/-- `TrieRep mem d node S fn`: `node` is the root of a depth-`d` binary trie in `mem` with owned
cell footprint `S`, representing the function `fn : ℕ → ℕ` on low-`d`-bit keys. `node = 0` is the
empty trie returning `0` everywhere. Every allocated node occupies `{node, node + 1}` with
`0 < node`. -/
private def TrieRep (mem : ℕ → ℕ) : ℕ → ℕ → Set ℕ → (ℕ → ℕ) → Prop
  | 0, node, S, fn =>
    (node = 0 ∧ S = ∅ ∧ ∀ m, fn m = 0) ∨
    (0 < node ∧ S = {node, node + 1} ∧ ∀ m, fn m = mem node)
  | d + 1, node, S, fn =>
    (node = 0 ∧ S = ∅ ∧ ∀ m, fn m = 0) ∨
    (0 < node ∧ ∃ S₀ S₁ fn₀ fn₁,
      Disjoint ({node, node + 1} : Set ℕ) (S₀ ∪ S₁) ∧
      Disjoint S₀ S₁ ∧
      S = {node, node + 1} ∪ S₀ ∪ S₁ ∧
      TrieRep mem d (mem node) S₀ fn₀ ∧
      TrieRep mem d (mem (node + 1)) S₁ fn₁ ∧
      ∀ m, fn m = if m % 2 = 0 then fn₀ (m / 2) else fn₁ (m / 2))

private theorem TrieRep.congr_mem {mem mem' : ℕ → ℕ} {d node : ℕ} {S : Set ℕ} {fn : ℕ → ℕ}
    (h : TrieRep mem d node S fn) (heq : ∀ a ∈ S, mem' a = mem a) :
    TrieRep mem' d node S fn := by
  induction d generalizing node S fn with
  | zero =>
    rcases h with ⟨rfl, rfl, hfn⟩ | ⟨hpos, rfl, hfn⟩
    · exact Or.inl ⟨rfl, rfl, hfn⟩
    · refine Or.inr ⟨hpos, rfl, fun m => ?_⟩
      rw [hfn m, heq node (by simp)]
  | succ d ih =>
    rcases h with ⟨rfl, rfl, hfn⟩ | ⟨hpos, S₀, S₁, fn₀, fn₁, hd₀, hd₁, rfl, ht₀, ht₁, hfn⟩
    · exact Or.inl ⟨rfl, rfl, hfn⟩
    · refine Or.inr ⟨hpos, S₀, S₁, fn₀, fn₁, hd₀, hd₁, rfl, ?_, ?_, hfn⟩
      · rw [heq node (by simp)]
        exact ih ht₀ fun a ha => heq a (by simp [ha])
      · rw [heq (node + 1) (by simp)]
        exact ih ht₁ fun a ha => heq a (by simp [ha])

private theorem TrieRep.zero_root (mem : ℕ → ℕ) (d : ℕ) :
    TrieRep mem d 0 ∅ (fun _ => 0) := by
  cases d <;> exact Or.inl ⟨rfl, rfl, fun _ => rfl⟩

private theorem TrieRep.fresh_node {mem : ℕ → ℕ} (d : ℕ) {node : ℕ} (hpos : 0 < node)
    (h0 : mem node = 0) (h1 : mem (node + 1) = 0) :
    TrieRep mem d node {node, node + 1} (fun _ => 0) := by
  cases d with
  | zero => exact Or.inr ⟨hpos, rfl, fun _ => h0.symm⟩
  | succ d =>
    refine Or.inr ⟨hpos, ∅, ∅, fun _ => 0, fun _ => 0, by simp, by simp, by simp, ?_, ?_,
      fun _ => by split_ifs <;> rfl⟩
    · rw [h0]; exact TrieRep.zero_root mem d
    · rw [h1]; exact TrieRep.zero_root mem d

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
    HoldsTrie mem bound d 0 (fun _ => 0) :=
  ⟨∅, Set.empty_subset _, TrieRep.zero_root mem d⟩

/-! ### Register layout and basic subroutines -/

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

private abbrev rZero : Fin numRegs := ⟨9, by decide⟩
private abbrev rOne : Fin numRegs := ⟨10, by decide⟩
private abbrev rDim : Fin numRegs := Reg.dim
private abbrev rThresh : Fin numRegs := Reg.thresh
private abbrev rFree : Fin numRegs := Reg.free
private abbrev rPreFree : Fin numRegs := ⟨14, by decide⟩
private abbrev rOutPtr : Fin numRegs := Reg.outPtr

private abbrev rTrieRoot : Fin numRegs := ⟨16, by decide⟩
private abbrev rTrieKey : Fin numRegs := ⟨17, by decide⟩
private abbrev rTrieVal : Fin numRegs := ⟨18, by decide⟩
private abbrev rTrieCur : Fin numRegs := ⟨19, by decide⟩
private abbrev rTrieRem : Fin numRegs := ⟨20, by decide⟩
private abbrev rTrieBit : Fin numRegs := ⟨21, by decide⟩
private abbrev rTrieTmp : Fin numRegs := ⟨22, by decide⟩

private abbrev rCoordsPtr : Fin numRegs := ⟨23, by decide⟩
private abbrev rCoordsLen : Fin numRegs := ⟨24, by decide⟩
private abbrev rMaxCard : Fin numRegs := ⟨25, by decide⟩
private abbrev rDomPtr : Fin numRegs := ⟨26, by decide⟩
private abbrev rDomLen : Fin numRegs := ⟨27, by decide⟩
private abbrev rGenIdx : Fin numRegs := ⟨28, by decide⟩
private abbrev rGenPos : Fin numRegs := ⟨29, by decide⟩
private abbrev rGenOldLen : Fin numRegs := ⟨30, by decide⟩
private abbrev rGenBitMask : Fin numRegs := ⟨31, by decide⟩
private abbrev rGenTmp : Fin numRegs := ⟨32, by decide⟩

private abbrev rCurDomPtr : Fin numRegs := Reg.entryPtr
private abbrev rCurDomLen : Fin numRegs := Reg.entryCount
private abbrev rStageCutoff : Fin numRegs := ⟨35, by decide⟩
private abbrev rSignMode : Fin numRegs := ⟨36, by decide⟩
private abbrev rRootsOut : Fin numRegs := ⟨37, by decide⟩
private abbrev rFbRoots : Fin numRegs := ⟨38, by decide⟩
private abbrev rStageIdx : Fin numRegs := ⟨39, by decide⟩
private abbrev rCellIdx : Fin numRegs := ⟨40, by decide⟩
private abbrev rStageCurRoot : Fin numRegs := ⟨41, by decide⟩
private abbrev rStageFbRoot : Fin numRegs := ⟨42, by decide⟩
private abbrev rCellSaved : Fin numRegs := Reg.builtRoot

private abbrev rTrieF : Fin numRegs := Reg.trieF
private abbrev rTrieG : Fin numRegs := Reg.trieG
private abbrev rQueryPtr : Fin numRegs := Reg.queryPtr
private abbrev rQueryCount : Fin numRegs := Reg.queryCount
private abbrev rQueryIdx : Fin numRegs := ⟨48, by decide⟩
private abbrev rCellKey : Fin numRegs := ⟨49, by decide⟩
private abbrev rCellCard : Fin numRegs := ⟨50, by decide⟩
private abbrev rPreFsBase : Fin numRegs := ⟨51, by decide⟩
private abbrev rPreGsBase : Fin numRegs := ⟨52, by decide⟩
private abbrev rPreHsBase : Fin numRegs := ⟨53, by decide⟩
private abbrev rQFsBase : Fin numRegs := ⟨54, by decide⟩
private abbrev rQGsBase : Fin numRegs := ⟨55, by decide⟩

/-- Allocate a fresh 2-word zeroed trie root at `rFree`. -/
private def trieInit : Code .standard numRegs := ram[
  rTrieRoot ← rFree;
  *rFree ← rZero;
  rFree ← rFree + rOne;
  *rFree ← rZero;
  rFree ← rFree + rOne ]

private theorem trieInit_preserves (i : Fin numRegs) :
    i ≠ rTrieRoot ∧ i ≠ rFree → trieInit.Preserves i := by
  decide +kernel +revert

private theorem exec_trieInit {w d free : ℕ} (x : Data numRegs)
    (hz : x.regs rZero = 0) (ho : x.regs rOne = 1) (hf : x.regs rFree = free)
    (hpos : 0 < free) (hfit : Fits w (free + 2)) :
    ∃ y, ExecWithin w trieInit x y 5 ∧
      y.regs rTrieRoot = free ∧ y.regs rFree = free + 2 ∧
      TrieRep y.mem d free {free, free + 1} (fun _ => 0) ∧
      (∀ a, a ≠ free ∧ a ≠ free + 1 → y.mem a = x.mem a) ∧
      ∀ i : Fin numRegs, i ≠ rTrieRoot ∧ i ≠ rFree → y.regs i = x.regs i := by
  have hrun : ∃ y, ExecWithin w trieInit x y 5 ∧
      y.regs rTrieRoot = free ∧ y.regs rFree = free + 2 ∧
      y.mem = Function.update (Function.update x.mem free 0) (free + 1) 0 := by
    unfold trieInit
    wram_exec [hz, ho, hf]
    wram_simp
  obtain ⟨y, he, hroot, hfree, hmem⟩ := hrun
  refine ⟨y, he, hroot, hfree, ?_, ?_, fun i hi => he.regs_eq (trieInit_preserves i hi)⟩
  · apply TrieRep.fresh_node d hpos
    · rw [hmem, Function.update_of_ne (by omega), Function.update_self]
    · rw [hmem, Function.update_self]
  · intro a ⟨ha0, ha1⟩
    rw [hmem, Function.update_of_ne ha1, Function.update_of_ne ha0]

/-- One bit-step of `trieGet`. -/
private def trieGetStep : Code .standard numRegs := ram[
  if rTrieCur = rZero then [
    rTrieBit ← rTrieBit + rOne
  ] else [
    rTrieTmp ← rTrieRem &&& rOne;
    rTrieRem ← rTrieRem >>> rOne;
    rTrieTmp ← rTrieCur + rTrieTmp;
    rTrieCur ← *rTrieTmp;
    rTrieBit ← rTrieBit + rOne
  ] ]

/-- Lookup `rTrieKey` in depth-`rDim` trie `rTrieRoot`, placing result in `rTrieVal`. -/
private def trieGet : Code .standard numRegs :=
  .seq (ram[ rTrieCur ← rTrieRoot; rTrieRem ← rTrieKey; rTrieBit ← #0 ])
    (.seq (.loop (.lt rTrieBit rDim) trieGetStep)
      (ram[ if rTrieCur = rZero then [ rTrieVal ← #0 ] else [ rTrieVal ← *rTrieCur ] ]))

private theorem trieGet_preserves (i : Fin numRegs) :
    i.val < 18 ∨ 23 ≤ i.val → trieGet.Preserves i := by
  decide +kernel +revert

private theorem exec_trieGet {w bound d root key : ℕ} {fn : ℕ → ℕ} (x : Data numRegs)
    (hz : x.regs rZero = 0) (ho : x.regs rOne = 1) (hd : x.regs rDim = d)
    (hr : x.regs rTrieRoot = root) (hk : x.regs rTrieKey = key)
    (htrie : HoldsTrie x.mem bound d root fn)
    (hfit_bound : Fits w bound) (hfit_d : Fits w d) (hfit_key : Fits w key) :
    ∃ y, ExecWithin w trieGet x y (9 * d + 8) ∧
      y.regs rTrieVal = fn key ∧ y.mem = x.mem ∧
      ∀ i : Fin numRegs, i.val < 18 ∨ 23 ≤ i.val → y.regs i = x.regs i := by
  have hrun : ∃ y, ExecWithin w trieGet x y (9 * d + 8) ∧
      y.regs rTrieVal = fn key ∧ y.mem = x.mem := by
    let P (b : ℕ) (s : Data numRegs) : Prop :=
      s.regs rZero = 0 ∧ s.regs rOne = 1 ∧ s.regs rDim = d ∧ s.mem = x.mem ∧
      Fits w (s.regs rTrieRem) ∧
      ∃ S ⊆ Set.Ico 1 bound, ∃ subFn,
        TrieRep x.mem (d - b) (s.regs rTrieCur) S subFn ∧ fn key = subFn (s.regs rTrieRem)
    have hbody (s : Data numRegs) (hs : P (s.regs rTrieBit) s) (hlt : s.regs rTrieBit < d) :
        ∃ z, ExecWithin w trieGetStep s z 7 ∧ P (s.regs rTrieBit + 1) z ∧
          z.regs rTrieBit = s.regs rTrieBit + 1 := by
      obtain ⟨hsz, hso, hsd, hsm, hfrem, S, hS, subFn, hrep, hval⟩ := hs
      have hrem_and : Fits w (s.regs rTrieRem &&& 1) :=
        hfit_d.of_le (by rw [Nat.and_one_is_mod]; omega)
      have hrem_shr : Fits w (s.regs rTrieRem >>> 1) := by
        rw [Nat.shiftRight_eq_div_pow]
        exact hfrem.of_le (Nat.div_le_self _ _)
      have hbit_next : Fits w (s.regs rTrieBit + 1) := hfit_d.of_le (by omega)
      have hsplit : d - s.regs rTrieBit = (d - (s.regs rTrieBit + 1)) + 1 := by omega
      rw [hsplit] at hrep
      dsimp only [TrieRep] at hrep
      by_cases hcur0 : s.regs rTrieCur = 0
      · have hfn0 : ∀ m, subFn m = 0 := by
          rcases hrep with ⟨_, _, hf0⟩ | ⟨hp, _⟩
          · exact hf0
          · omega
        have hstep : ∃ z, ExecWithin w trieGetStep s z 7 ∧
            z.regs rZero = 0 ∧ z.regs rOne = 1 ∧ z.regs rDim = d ∧ z.mem = s.mem ∧
            z.regs rTrieCur = 0 ∧ z.regs rTrieRem = s.regs rTrieRem ∧
            z.regs rTrieBit = s.regs rTrieBit + 1 := by
          unfold trieGetStep
          wram_exec [hsz, hso, hcur0]
          wram_simp [hsz, hso, hsd, hcur0]
        obtain ⟨z, hz, hzz, hzo, hzd, hzm, hzc, hzr, hzb⟩ := hstep
        refine ⟨z, hz, ⟨hzz, hzo, hzd, hzm.trans hsm, hzr ▸ hfrem,
          ∅, Set.empty_subset _, fun _ => 0, ?_, ?_⟩, hzb⟩
        · rw [hzc]; exact TrieRep.zero_root x.mem _
        · rw [hval, hfn0]
      · rcases hrep with ⟨hc0, _⟩ | ⟨_, S₀, S₁, fn₀, fn₁, _, _, rfl, ht₀, ht₁, hfn⟩
        · exact absurd hc0 hcur0
        have hcur_bound : s.regs rTrieCur + 1 < bound :=
          (hS (by simp : s.regs rTrieCur + 1 ∈ _)).2
        have hbit_le : (s.regs rTrieRem &&& 1) ≤ 1 := by
          rw [Nat.and_one_is_mod]; omega
        have haddr_fit : Fits w (s.regs rTrieCur + (s.regs rTrieRem &&& 1)) :=
          hfit_bound.of_le (by omega)
        have hstep : ∃ z, ExecWithin w trieGetStep s z 7 ∧
            z.regs rZero = 0 ∧ z.regs rOne = 1 ∧ z.regs rDim = d ∧ z.mem = s.mem ∧
            z.regs rTrieCur = s.mem (s.regs rTrieCur + (s.regs rTrieRem &&& 1)) ∧
            z.regs rTrieRem = s.regs rTrieRem >>> 1 ∧
            z.regs rTrieBit = s.regs rTrieBit + 1 := by
          unfold trieGetStep
          wram_exec [hsz, hso, hcur0]
          wram_simp [hsz, hso, hsd]
        obtain ⟨z, hz, hzz, hzo, hzd, hzm, hzc, hzr, hzb⟩ := hstep
        rw [hsm, Nat.and_one_is_mod] at hzc
        rw [Nat.shiftRight_eq_div_pow, pow_one] at hzr
        refine ⟨z, hz, ⟨hzz, hzo, hzd, hzm.trans hsm, hzr ▸ hrem_shr, ?_⟩, hzb⟩
        by_cases hmod : s.regs rTrieRem % 2 = 0
        · refine ⟨S₀, fun a ha => hS (by simp [ha]), fn₀, ?_, ?_⟩
          · simpa [hzc, hmod] using ht₀
          · rw [hval, hfn, ite_eq_left hmod, hzr]
        · have hmod1 : s.regs rTrieRem % 2 = 1 := by omega
          refine ⟨S₁, fun a ha => hS (by simp [ha]), fn₁, ?_, ?_⟩
          · simpa [hzc, hmod1] using ht₁
          · rw [hval, hfn, ite_eq_right hmod, hzr]
    let x₀ := ((x.set rTrieCur root).set rTrieRem key).set rTrieBit 0
    have hinit : ExecWithin (B := .standard) w
        (ram[ rTrieCur ← rTrieRoot; rTrieRem ← rTrieKey; rTrieBit ← #0 ]) x x₀ 3 := by
      wram_exec [hr, hk]
    obtain ⟨S_init, hS_init, hrep_init⟩ := htrie
    have hx₀ : P (x₀.regs rTrieBit) x₀ := by
      refine ⟨by simp [x₀, hz], by simp [x₀, ho], by simp [x₀, hd], rfl,
        by simpa [x₀] using hfit_key, S_init, hS_init, fn, ?_, by simp [x₀]⟩
      simpa [x₀] using hrep_init
    obtain ⟨u, hloop, huP, _⟩ := ExecWithin.loop_count P (fun s hs => hs.2.2.1) hbody
      (by simp [x₀]) hx₀
    obtain ⟨huz, _, _, hum, _, _, _, subFn, hrep_end, hval_end⟩ := huP
    rw [Nat.sub_self] at hrep_end
    dsimp only [TrieRep] at hrep_end
    have hfin : ∃ y, ExecWithin (B := .standard) w
        (ram[ if rTrieCur = rZero then [ rTrieVal ← #0 ] else [ rTrieVal ← *rTrieCur ] ]) u y 3 ∧
        y.regs rTrieVal = fn key ∧ y.mem = u.mem := by
      rcases hrep_end with ⟨hc0, _, hf0⟩ | ⟨hpos, _, hmem_eq⟩
      · wram_exec [huz, hc0]
        wram_simp [hval_end, hf0]
      · have hne : u.regs rTrieCur ≠ 0 := by omega
        wram_exec [huz, hne]
        wram_simp [hval_end, hmem_eq, hum]
    obtain ⟨y, hfy, hyval, hymem⟩ := hfin
    refine ⟨y, (hinit.seq (hloop.seq hfy)).mono (by simp [x₀]; omega), hyval, hymem.trans hum⟩
  obtain ⟨y, he, hyval, hymem⟩ := hrun
  exact ⟨y, he, hyval, hymem, fun i hi => he.regs_eq (trieGet_preserves i hi)⟩

/-- One bit-step of `trieSet`, allocating a 2-word zeroed child at `rFree` if absent. -/
private def trieSetStep : Code .standard numRegs := ram[
  rTrieTmp ← rTrieRem &&& rOne;
  rTrieRem ← rTrieRem >>> rOne;
  rTrieTmp ← rTrieCur + rTrieTmp;
  rTrieCur ← *rTrieTmp;
  if rTrieCur = rZero then [
    rTrieCur ← rFree;
    *rTrieTmp ← rFree;
    *rFree ← rZero;
    rFree ← rFree + rOne;
    *rFree ← rZero;
    rFree ← rFree + rOne
  ] else [
    rTrieCur ← rTrieCur
  ];
  rTrieBit ← rTrieBit + rOne ]

/-- Set `rTrieKey` to `rTrieVal` in depth-`rDim` trie `rTrieRoot` (`0 < rTrieRoot`). -/
private def trieSet : Code .standard numRegs :=
  .seq (ram[ rTrieCur ← rTrieRoot; rTrieRem ← rTrieKey; rTrieBit ← #0 ])
    (.seq (.loop (.lt rTrieBit rDim) trieSetStep)
      (ram[ *rTrieCur ← rTrieVal ]))

private theorem trieSet_preserves (i : Fin numRegs) :
    i ≠ rFree ∧ (i.val < 19 ∨ 23 ≤ i.val) → trieSet.Preserves i := by
  decide +kernel +revert

private theorem mod_two_pow_succ_eq_iff {a b k : ℕ} :
    a % 2 ^ (k + 1) = b % 2 ^ (k + 1) ↔ a % 2 = b % 2 ∧ (a / 2) % 2 ^ k = (b / 2) % 2 ^ k := by
  rw [pow_succ']
  have hdvd : 2 ∣ 2 * 2 ^ k := dvd_mul_right 2 (2 ^ k)
  constructor
  · intro h
    have h2 : a % 2 = b % 2 := by
      have := congrArg (· % 2) h
      rwa [Nat.mod_mod_of_dvd a hdvd, Nat.mod_mod_of_dvd b hdvd] at this
    refine ⟨h2, ?_⟩
    have ha := Nat.mod_mul_right_div_self a 2 (2 ^ k)
    have hb := Nat.mod_mul_right_div_self b 2 (2 ^ k)
    omega
  · rintro ⟨h2, hdiv⟩
    have ha : a % (2 * 2 ^ k) = a % 2 + 2 * ((a / 2) % 2 ^ k) := by
      have := Nat.div_add_mod (a % (2 * 2 ^ k)) 2
      have hd := Nat.mod_mul_right_div_self a 2 (2 ^ k)
      have hm : (a % (2 * 2 ^ k)) % 2 = a % 2 := Nat.mod_mod_of_dvd a hdvd
      omega
    have hb : b % (2 * 2 ^ k) = b % 2 + 2 * ((b / 2) % 2 ^ k) := by
      have := Nat.div_add_mod (b % (2 * 2 ^ k)) 2
      have hd := Nat.mod_mul_right_div_self b 2 (2 ^ k)
      have hm : (b % (2 * 2 ^ k)) % 2 = b % 2 := Nat.mod_mod_of_dvd b hdvd
      omega
    omega

private theorem exec_trieSetLoop :
    ∀ (k : ℕ) {w lo d b cur rem val free : ℕ} {S : Set ℕ} {fn : ℕ → ℕ} (s : Data numRegs),
      k = d - b → b ≤ d →
      s.regs rZero = 0 → s.regs rOne = 1 → s.regs rDim = d →
      s.regs rTrieBit = b → s.regs rTrieCur = cur → s.regs rTrieRem = rem →
      s.regs rTrieVal = val → s.regs rFree = free →
      1 ≤ lo → lo ≤ free → 0 < cur → S ⊆ Set.Ico lo free →
      TrieRep s.mem k cur S fn →
      Fits w (free + 2 * k) → Fits w d → Fits w rem →
      ∃ y S' free',
        ExecWithin w (.seq (.loop (.lt rTrieBit rDim) trieSetStep) (ram[ *rTrieCur ← rTrieVal ]))
          s y (14 * k + 3) ∧
        y.regs rFree = free' ∧ free ≤ free' ∧ free' ≤ free + 2 * k ∧
        S' ⊆ S ∪ Set.Ico free free' ∧
        (∀ a, a ∉ S ∪ Set.Ico free free' → y.mem a = s.mem a) ∧
        TrieRep y.mem k cur S' (fun m => if m % 2 ^ k = rem % 2 ^ k then val else fn m) := by
  intro k
  induction k with
  | zero =>
    intro w lo d b cur rem val free S fn s hk hle hz ho hd hb hcur hrem hval hfree
      hlo hfree_lo hcur_pos hS hrep hfit_free hfit_d hfit_rem
    obtain rfl : b = d := by omega
    dsimp only [TrieRep] at hrep
    rcases hrep with ⟨hc0, _⟩ | ⟨_, rfl, _⟩
    · omega
    have hexit : Exec w (.loop (.lt rTrieBit rDim) trieSetStep) s s 2 :=
      Exec.loop_exit (by simp [Cond.holds_lt, hb, hd])
    have hst : ∃ y, ExecWithin (B := .standard) w (ram[ *rTrieCur ← rTrieVal ]) s y 1 ∧
        y.regs rFree = free ∧ y.mem = Function.update s.mem cur val := by
      wram_exec [hcur, hval]
      wram_simp [hfree]
    obtain ⟨y, hy, hyfree, hymem⟩ := hst
    refine ⟨y, {cur, cur + 1}, free, (hexit.within.seq hy).mono (by omega), hyfree,
      le_rfl, by omega, Set.subset_union_left, ?_, ?_⟩
    · intro a ha
      rw [hymem, Function.update_of_ne]
      intro hEq; subst hEq; exact ha (by simp)
    · refine Or.inr ⟨hcur_pos, rfl, fun m => ?_⟩
      simp [pow_zero, Nat.mod_one, hymem]
  | succ k ih =>
    intro w lo d b cur rem val free S fn s hk hle hz ho hd hb hcur hrem hval hfree
      hlo hfree_lo hcur_pos hS hrep hfit_free hfit_d hfit_rem
    have hlt_bd : b < d := by omega
    dsimp only [TrieRep] at hrep
    rcases hrep with ⟨hc0, _⟩ | ⟨_, S₀, S₁, fn₀, fn₁, hd_cur, hd_01, hS_eq, ht₀, ht₁, hfn⟩
    · omega
    have hcur_mem : cur ∈ S := by rw [hS_eq]; simp
    have hcur1_mem : cur + 1 ∈ S := by rw [hS_eq]; simp
    have hcur1_lt : cur + 1 < free := (hS hcur1_mem).2
    have hrem_and_fit : Fits w (rem &&& 1) := hfit_d.of_le (by rw [Nat.and_one_is_mod]; omega)
    have hrem_shr_fit : Fits w (rem >>> 1) := by
      rw [Nat.shiftRight_eq_div_pow]
      exact hfit_rem.of_le (Nat.div_le_self _ _)
    have haddr_fit : Fits w (cur + (rem &&& 1)) :=
      hfit_free.of_le (by rw [Nat.and_one_is_mod]; omega)
    have hb1_fit : Fits w (b + 1) := hfit_d.of_le (by omega)
    have hfree2_fit : Fits w (free + 2) := hfit_free.of_le (by omega)
    let bit := rem % 2
    have hbit01 : bit = 0 ∨ bit = 1 := by dsimp [bit]; omega
    have hbit_eq : rem &&& 1 = bit := Nat.and_one_is_mod rem
    let slot := cur + bit
    have hstep : ∃ u, ExecWithin w trieSetStep s u 12 ∧
        u.regs rZero = 0 ∧ u.regs rOne = 1 ∧ u.regs rDim = d ∧
        u.regs rTrieBit = b + 1 ∧ u.regs rTrieRem = rem / 2 ∧ u.regs rTrieVal = val ∧
        ((s.mem slot = 0 ∧ u.regs rTrieCur = free ∧ u.regs rFree = free + 2 ∧
          u.mem = Function.update
            (Function.update (Function.update s.mem slot free) free 0) (free + 1) 0) ∨
         (s.mem slot ≠ 0 ∧ u.regs rTrieCur = s.mem slot ∧
           u.regs rFree = free ∧ u.mem = s.mem)) := by
      by_cases hslot0 : s.mem slot = 0
      · have hload : s.mem (cur + (rem &&& 1)) = 0 := by rwa [hbit_eq]
        unfold trieSetStep
        wram_exec [hz, ho, hcur, hrem, hfree, hload]
        refine ⟨hz, ho, hd, ?_, ?_, hval, Or.inl ⟨hslot0, ?_, ?_, ?_⟩⟩
        · wram_simp [hb]
        · wram_simp; rw [Nat.shiftRight_eq_div_pow, pow_one]
        · wram_simp
        · wram_simp
        · wram_simp [hbit_eq]; rfl
      · have hload : s.mem (cur + (rem &&& 1)) ≠ 0 := by rwa [hbit_eq]
        unfold trieSetStep
        wram_exec [hz, ho, hcur, hrem, hfree, hload]
        refine ⟨hz, ho, hd, ?_, ?_, hval, Or.inr ⟨hslot0, ?_, ?_, ?_⟩⟩
        · wram_simp [hb]
        · wram_simp; rw [Nat.shiftRight_eq_div_pow, pow_one]
        · wram_simp [hbit_eq, slot]
        · wram_simp [hfree]
        · wram_simp
    obtain ⟨u, hstep_exec, huz, huo, hud, hub, hurem, huval, hbranch⟩ := hstep
    have hslot_mem_cur : slot ∈ ({cur, cur + 1} : Set ℕ) := by
      rcases hbit01 with hb0 | hb1
      · simp [slot, hb0]
      · simp [slot, hb1]
    have hother_mem_cur : cur + (1 - bit) ∈ ({cur, cur + 1} : Set ℕ) := by
      rcases hbit01 with hb0 | hb1
      · simp [hb0]
      · simp [hb1]
    have hprep : ∃ child free₁ S_c S_o fn_c fn_o,
        u.regs rTrieCur = child ∧ u.regs rFree = free₁ ∧
        free ≤ free₁ ∧ free₁ ≤ free + 2 ∧ 0 < child ∧
        u.mem slot = child ∧ u.mem (cur + (1 - bit)) = s.mem (cur + (1 - bit)) ∧
        S_c ⊆ S ∪ Set.Ico free free₁ ∧ S_o ⊆ S ∧
        Disjoint ({cur, cur + 1} : Set ℕ) (S_c ∪ S_o) ∧ Disjoint S_c S_o ∧
        S_c ⊆ Set.Ico lo free₁ ∧
        (∀ a, a ∉ ({slot} : Set ℕ) ∪ Set.Ico free free₁ → u.mem a = s.mem a) ∧
        TrieRep u.mem k child S_c fn_c ∧
        TrieRep u.mem k (u.mem (cur + (1 - bit))) S_o fn_o ∧
        (bit = 0 → fn_c = fn₀ ∧ fn_o = fn₁) ∧
        (bit = 1 → fn_c = fn₁ ∧ fn_o = fn₀) := by
      rcases hbranch with ⟨hslot0, hucur, hufree, humem⟩ | ⟨hslot_ne, hucur, hufree, humem⟩
      · refine ⟨free, free + 2, {free, free + 1}, if bit = 0 then S₁ else S₀,
          fun _ => 0, if bit = 0 then fn₁ else fn₀, hucur, hufree, by omega, le_rfl,
          by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [humem, Function.update_of_ne (by dsimp [slot]; omega),
            Function.update_of_ne (by dsimp [slot]; omega), Function.update_self]
        · rw [humem, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by dsimp [slot]; omega)]
        · intro a ha
          rcases ha with rfl | ha1
          · exact Or.inr ⟨le_rfl, by omega⟩
          · have : a = free + 1 := by simpa using ha1
            subst this; exact Or.inr ⟨by omega, by omega⟩
        · intro a ha
          rw [hS_eq]
          rcases hbit01 with hb0 | hb1
          · simp only [hb0, ↓reduceIte] at ha; simp [ha]
          · simp only [hb1, Nat.reduceEqDiff, ↓reduceIte] at ha; simp [ha]
        · rw [Set.disjoint_left]
          intro a ha hso
          have ha_lt : a < free := by
            rcases ha with rfl | ha1
            · omega
            · have : a = cur + 1 := by simpa using ha1
              omega
          rcases hso with hsc | hso
          · rcases hsc with rfl | hsc1
            · omega
            · have : a = free + 1 := by simpa using hsc1
              omega
          · have h01 : a ∈ S₀ ∪ S₁ := by
              rcases hbit01 with hb0 | hb1
              · simp only [hb0, ↓reduceIte] at hso; exact Or.inr hso
              · simp only [hb1, Nat.reduceEqDiff, ↓reduceIte] at hso; exact Or.inl hso
            exact Set.disjoint_left.mp hd_cur ha h01
        · rw [Set.disjoint_left]
          intro a ha hso
          have ha_ge : free ≤ a := by
            rcases ha with rfl | ha1
            · exact le_rfl
            · have : a = free + 1 := by simpa using ha1
              omega
          have haS : a ∈ S := by
            rw [hS_eq]
            rcases hbit01 with hb0 | hb1
            · simp only [hb0, ↓reduceIte] at hso; simp [hso]
            · simp only [hb1, Nat.reduceEqDiff, ↓reduceIte] at hso; simp [hso]
          have := (hS haS).2
          omega
        · intro a ha
          rcases ha with rfl | ha1
          · exact ⟨by omega, by omega⟩
          · have : a = free + 1 := by simpa using ha1
            subst this; exact ⟨by omega, by omega⟩
        · intro a ha
          rw [humem, Function.update_of_ne (by intro h; exact ha (Or.inr ⟨by omega, by omega⟩)),
            Function.update_of_ne (by intro h; exact ha (Or.inr ⟨by omega, by omega⟩)),
            Function.update_of_ne (by intro h; exact ha (Or.inl (by simp [h])))]
        · apply TrieRep.fresh_node k (by omega)
          · rw [humem, Function.update_of_ne (by omega), Function.update_self]
          · rw [humem, Function.update_self]
        · have hu_other : u.mem (cur + (1 - bit)) = s.mem (cur + (1 - bit)) := by
            rw [humem, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by dsimp [slot]; omega)]
          rw [hu_other]
          rcases hbit01 with hb0 | hb1
          · simp only [hb0, ↓reduceIte, Nat.sub_zero]
            refine ht₁.congr_mem fun a ha => ?_
            have ha_lt : a < free := (hS (by rw [hS_eq]; simp [ha])).2
            have ha_ne : a ≠ slot := fun h =>
              Set.disjoint_left.mp hd_cur (h ▸ hslot_mem_cur) (Or.inr ha)
            rw [humem, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne ha_ne]
          · simp only [hb1, Nat.reduceEqDiff, ↓reduceIte, Nat.sub_self, Nat.add_zero]
            refine ht₀.congr_mem fun a ha => ?_
            have ha_lt : a < free := (hS (by rw [hS_eq]; simp [ha])).2
            have ha_ne : a ≠ slot := fun h =>
              Set.disjoint_left.mp hd_cur (h ▸ hslot_mem_cur) (Or.inl ha)
            rw [humem, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne ha_ne]
        · intro hb0
          have hm0 : s.mem cur = 0 := by simpa [slot, hb0] using hslot0
          rw [hm0] at ht₀
          have hfn0_zero : fn₀ = fun _ => 0 := by
            funext m
            cases k <;> {
              dsimp only [TrieRep] at ht₀
              rcases ht₀ with ⟨_, _, hf⟩ | ⟨hp, _⟩
              · exact hf m
              · omega }
          exact ⟨hfn0_zero.symm, by simp [hb0]⟩
        · intro hb1
          have hm1 : s.mem (cur + 1) = 0 := by simpa [slot, hb1] using hslot0
          rw [hm1] at ht₁
          have hfn1_zero : fn₁ = fun _ => 0 := by
            funext m
            cases k <;> {
              dsimp only [TrieRep] at ht₁
              rcases ht₁ with ⟨_, _, hf⟩ | ⟨hp, _⟩
              · exact hf m
              · omega }
          exact ⟨hfn1_zero.symm, by simp [hb1]⟩
      · refine ⟨s.mem slot, free, if bit = 0 then S₀ else S₁, if bit = 0 then S₁ else S₀,
          if bit = 0 then fn₀ else fn₁, if bit = 0 then fn₁ else fn₀,
          hucur, hufree, le_rfl, by omega, by omega, by rw [humem], by rw [humem],
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro a ha
          left; rw [hS_eq]
          rcases hbit01 with hb0 | hb1
          · simp only [hb0, ↓reduceIte] at ha; simp [ha]
          · simp only [hb1, Nat.reduceEqDiff, ↓reduceIte] at ha; simp [ha]
        · intro a ha
          rw [hS_eq]
          rcases hbit01 with hb0 | hb1
          · simp only [hb0, ↓reduceIte] at ha; simp [ha]
          · simp only [hb1, Nat.reduceEqDiff, ↓reduceIte] at ha; simp [ha]
        · rcases hbit01 with hb0 | hb1
          · simp only [hb0, ↓reduceIte]; exact hd_cur
          · simp only [hb1, Nat.reduceEqDiff, ↓reduceIte, Set.union_comm]; exact hd_cur
        · rcases hbit01 with hb0 | hb1
          · simp only [hb0, ↓reduceIte]; exact hd_01
          · simp only [hb1, Nat.reduceEqDiff, ↓reduceIte]; exact hd_01.symm
        · intro a ha
          refine hS ?_
          rw [hS_eq]
          rcases hbit01 with hb0 | hb1
          · simp only [hb0, ↓reduceIte] at ha; simp [ha]
          · simp only [hb1, Nat.reduceEqDiff, ↓reduceIte] at ha; simp [ha]
        · intro a _; rw [humem]
        · rw [humem]
          rcases hbit01 with hb0 | hb1
          · simpa [slot, hb0] using ht₀
          · simpa [slot, hb1] using ht₁
        · rw [humem]
          rcases hbit01 with hb0 | hb1
          · simpa [hb0] using ht₁
          · simpa [hb1] using ht₀
        · intro hb0; simp [hb0]
        · intro hb1; simp [hb1]
    obtain ⟨child, free₁, S_c, S_o, fn_c, fn_o, hucur, hufree, hfree_le1, hfree1_le, hchild_pos,
      humem_slot, _, hSc_sub, hSo_sub, hdisj_cur, hdisj_co, hSc_ico, hu_frame,
      ht_c, ht_o, hbit0_fn, hbit1_fn⟩ := hprep
    obtain ⟨y, S_c', free₂, hrec_exec, hyfree, hfree12, hfree2_le, hSc'_sub, hy_frame, ht_c'⟩ :=
      ih u (by omega) (by omega) huz huo hud hub hucur hurem huval hufree hlo
        (hfree_lo.trans hfree_le1) hchild_pos hSc_ico ht_c
        (hfit_free.of_le (by omega)) hfit_d (hfit_rem.of_le (Nat.div_le_self _ _))
    have hcond : (Cond.lt rTrieBit rDim).Holds s := by simp [Cond.holds_lt, hb, hd, hlt_bd]
    obtain ⟨n_step, hn_step, hex_step⟩ := hstep_exec
    obtain ⟨n_rec, hn_rec, hex_rec⟩ := hrec_exec
    cases hex_rec with
    | seq hex_loop hex_store =>
      have hex_full : ExecWithin w
          (.seq (.loop (.lt rTrieBit rDim) trieSetStep) (ram[ *rTrieCur ← rTrieVal ])) s y
          (14 * (k + 1) + 3) :=
        ⟨_, by omega, Exec.seq (Exec.loop_iter hcond hex_step hex_loop) hex_store⟩
      have hdisj_cur' : Disjoint ({cur, cur + 1} : Set ℕ) (S_c' ∪ S_o) := by
        rw [Set.disjoint_left]
        intro a ha hso
        rcases hso with hsc' | hso
        · rcases hSc'_sub hsc' with hsc | hnew
          · exact Set.disjoint_left.mp hdisj_cur ha (Or.inl hsc)
          · have ha_lt : a < free := by
              rcases ha with rfl | ha1
              · omega
              · have : a = cur + 1 := by simpa using ha1
                omega
            have := hnew.1; omega
        · exact Set.disjoint_left.mp hdisj_cur ha (Or.inr hso)
      have hdisj_co' : Disjoint S_c' S_o := by
        rw [Set.disjoint_left]
        intro a hsc' hso
        rcases hSc'_sub hsc' with hsc | hnew
        · exact Set.disjoint_left.mp hdisj_co hsc hso
        · have ha_lt : a < free := (hS (hSo_sub hso)).2
          have := hnew.1; omega
      have hy_cur_slot : y.mem slot = child := by
        rw [hy_frame slot (by
          intro h; rcases h with hsc | hnew
          · exact Set.disjoint_left.mp hdisj_cur hslot_mem_cur (Or.inl hsc)
          · have : slot < free := by dsimp [slot, bit]; omega
            have := hnew.1; omega), humem_slot]
      have hy_cur_other : y.mem (cur + (1 - bit)) = u.mem (cur + (1 - bit)) := by
        apply hy_frame
        intro h; rcases h with hsc | hnew
        · exact Set.disjoint_left.mp hdisj_cur hother_mem_cur (Or.inl hsc)
        · have : cur + (1 - bit) < free := by dsimp [bit]; omega
          have := hnew.1; omega
      have ht_o' : TrieRep y.mem k (y.mem (cur + (1 - bit))) S_o fn_o := by
        rw [hy_cur_other]
        exact ht_o.congr_mem fun a ha => hy_frame a fun h => by
          rcases h with hsc | hnew
          · exact Set.disjoint_left.mp hdisj_co hsc ha
          · have := (hS (hSo_sub ha)).2; have := hnew.1; omega
      refine ⟨y, {cur, cur + 1} ∪ (if bit = 0 then S_c' else S_o) ∪ (if bit = 0 then S_o else S_c'),
        free₂, hex_full, hyfree, hfree_le1.trans hfree12, by omega, ?_, ?_, ?_⟩
      · intro a ha
        have hsub_c' : S_c' ⊆ S ∪ Set.Ico free free₂ := fun x hx => by
          rcases hSc'_sub hx with hxc | hnew
          · rcases hSc_sub hxc with hxs | hnew0
            · exact Or.inl hxs
            · exact Or.inr ⟨hnew0.1, hnew0.2.trans_le hfree12⟩
          · exact Or.inr ⟨hfree_le1.trans hnew.1, hnew.2⟩
        rcases hbit01 with hb0 | hb1
        · simp only [hb0, ↓reduceIte] at ha
          rcases ha with (ha_cur | ha_c) | ha_o
          · exact Or.inl (by rw [hS_eq]; simp [ha_cur])
          · exact hsub_c' ha_c
          · exact Or.inl (hSo_sub ha_o)
        · simp only [hb1, Nat.reduceEqDiff, ↓reduceIte] at ha
          rcases ha with (ha_cur | ha_o) | ha_c
          · exact Or.inl (by rw [hS_eq]; simp [ha_cur])
          · exact Or.inl (hSo_sub ha_o)
          · exact hsub_c' ha_c
      · intro a ha
        have ha_not_rec : a ∉ S_c ∪ Set.Ico free₁ free₂ := by
          intro h; apply ha
          rcases h with hsc | hnew
          · rcases hSc_sub hsc with hxs | hnew0
            · exact Or.inl hxs
            · exact Or.inr ⟨hnew0.1, hnew0.2.trans_le hfree12⟩
          · exact Or.inr ⟨hfree_le1.trans hnew.1, hnew.2⟩
        rw [hy_frame a ha_not_rec]
        apply hu_frame
        intro h; apply ha
        rcases h with hslot | hnew0
        · have : a = slot := by simpa using hslot
          subst this; left; rw [hS_eq]
          exact Or.inl (Or.inl hslot_mem_cur)
        · exact Or.inr ⟨hnew0.1, hnew0.2.trans_le hfree12⟩
      · dsimp only [TrieRep]
        rcases hbit01 with hb0 | hb1
        · obtain ⟨hc_eq, ho_eq⟩ := hbit0_fn hb0
          subst hc_eq; subst ho_eq
          simp only [hb0, ↓reduceIte]
          have hm0 : y.mem cur = child := by simpa [slot, hb0] using hy_cur_slot
          refine Or.inr ⟨hcur_pos, S_c', S_o, _, fn_o, hdisj_cur', hdisj_co', rfl,
            hm0 ▸ ht_c', by simpa [hb0] using ht_o', fun m => ?_⟩
          simp only [mod_two_pow_succ_eq_iff, hfn m]
          have hrem2 : rem % 2 = 0 := hb0
          by_cases hm2 : m % 2 = 0 <;> simp [hm2, hrem2]
        · obtain ⟨hc_eq, ho_eq⟩ := hbit1_fn hb1
          subst hc_eq; subst ho_eq
          simp only [hb1, Nat.reduceEqDiff, ↓reduceIte]
          have hm1 : y.mem (cur + 1) = child := by simpa [slot, hb1] using hy_cur_slot
          refine Or.inr ⟨hcur_pos, S_o, S_c', fn_o, _,
            by simpa [Set.union_comm] using hdisj_cur', hdisj_co'.symm, rfl,
            by simpa [hb1] using ht_o', hm1 ▸ ht_c', fun m => ?_⟩
          simp only [mod_two_pow_succ_eq_iff, hfn m]
          have hrem2 : rem % 2 = 1 := hb1
          by_cases hm2 : m % 2 = 0
          · simp [hm2, hrem2]
          · have hm2' : m % 2 = 1 := by omega
            simp [hm2', hrem2]

private theorem exec_trieSet {w lo d root key val free : ℕ} {S : Set ℕ} {fn : ℕ → ℕ}
    (x : Data numRegs)
    (hz : x.regs rZero = 0) (ho : x.regs rOne = 1) (hd : x.regs rDim = d)
    (hr : x.regs rTrieRoot = root) (hk : x.regs rTrieKey = key)
    (hv : x.regs rTrieVal = val) (hfree : x.regs rFree = free)
    (hlo : 1 ≤ lo) (hfree_lo : lo ≤ free) (hroot : 0 < root) (hS : S ⊆ Set.Ico lo free)
    (hrep : TrieRep x.mem d root S fn) (hkey_lt : key < 2 ^ d)
    (hfit_free : Fits w (free + 2 * d)) (hfit_d : Fits w d) (hfit_key : Fits w key) :
    ∃ y S' free', ExecWithin w trieSet x y (14 * d + 6) ∧
      y.regs rFree = free' ∧ free ≤ free' ∧ free' ≤ free + 2 * d ∧
      S' ⊆ Set.Ico lo free' ∧
      (∀ a, a < lo ∨ free' ≤ a → y.mem a = x.mem a) ∧
      TrieRep y.mem d root S' (fun m => if m % 2 ^ d = key then val else fn m) ∧
      ∀ i : Fin numRegs, i ≠ rFree ∧ (i.val < 19 ∨ 23 ≤ i.val) → y.regs i = x.regs i := by
  let x₀ := ((x.set rTrieCur root).set rTrieRem key).set rTrieBit 0
  have hinit : ExecWithin (B := .standard) w
      (ram[ rTrieCur ← rTrieRoot; rTrieRem ← rTrieKey; rTrieBit ← #0 ]) x x₀ 3 := by
    wram_exec [hr, hk]
  obtain ⟨y, S', free', hbody, hyfree, hle1, hle2, hS', hyframe, hyrep⟩ :=
    exec_trieSetLoop d (val := val) (free := free) x₀ (by omega) (Nat.zero_le d)
      (by simp [x₀, hz]) (by simp [x₀, ho]) (by simp [x₀, hd])
      (by simp [x₀]) (by simp [x₀]) (by simp [x₀])
      (by simpa [x₀] using hv) (by simpa [x₀] using hfree)
      hlo hfree_lo hroot hS (by simpa [x₀] using hrep) hfit_free hfit_d hfit_key
  have htot : ExecWithin w trieSet x y (14 * d + 6) := (hinit.seq hbody).mono (by omega)
  rw [Nat.mod_eq_of_lt hkey_lt] at hyrep
  refine ⟨y, S', free', htot, hyfree, hle1, hle2, ?_, ?_, hyrep,
    fun i hi => htot.regs_eq (trieSet_preserves i hi)⟩
  · intro a ha
    rcases hS' ha with haS | haNew
    · exact ⟨(hS haS).1, (hS haS).2.trans_le hle1⟩
    · exact ⟨hfree_lo.trans haNew.1, haNew.2⟩
  · intro a ha
    have hnot : a ∉ S ∪ Set.Ico free free' := by
      intro h; rcases h with haS | haNew
      · have h1 := (hS haS).1; have h2 := (hS haS).2
        rcases ha with ha1 | ha2 <;> omega
      · have h1 := haNew.1; have h2 := haNew.2
        rcases ha with ha1 | ha2 <;> omega
    exact hyframe a hnot

/-! ### Signed integer wrappers at physical width `w` and `trieAdd` -/

private theorem width_ge_three_of_fits {w B : ℕ} (hfit : Fits w (8 * B + 4)) : 3 ≤ w := by
  by_contra h
  have hw : w = 0 ∨ w = 1 ∨ w = 2 := by omega
  rcases hw with rfl | rfl | rfl <;> { simp only [Fits] at hfit; omega }

private theorem signedFits_of_natAbs_le {w B : ℕ} (hfit : Fits w (8 * B + 4)) {z : ℤ}
    (hz : z.natAbs ≤ B) : GenericRAM.Signed.Fits (w - 2) z := by
  have hw3 := width_ge_three_of_fits hfit
  have hsub : (w - 2) - 1 = w - 3 := by omega
  have hpow : 2 ^ w = 8 * 2 ^ (w - 3) := by
    have hw_eq : w = (w - 3) + 3 := by omega
    conv_lhs => rw [hw_eq, pow_add]
    ring
  have hlt : 8 * B + 4 < 8 * 2 ^ (w - 3) := by rw [← hpow]; exact hfit
  have hB : B < 2 ^ ((w - 2) - 1) := by rw [hsub]; omega
  have hcast : ((2 ^ ((w - 2) - 1) : ℕ) : ℤ) = (2 : ℤ) ^ ((w - 2) - 1) := by norm_cast
  refine ⟨by omega, ?_, ?_⟩
  · by_cases hz0 : 0 ≤ z
    · omega
    · have := Int.ofNat_natAbs_of_nonpos (by omega : z ≤ 0)
      omega
  · by_cases hz0 : 0 ≤ z
    · have := Int.eq_natAbs_of_nonneg hz0
      omega
    · omega

private theorem exec_signedAdd {w B : ℕ} {a b : ℤ} (hfit : Fits w (8 * B + 4))
    (ha : a.natAbs ≤ B) (hb : b.natAbs ≤ B) (x : Data numRegs)
    (hxa : x.regs (Signed.left (r := 47)) = Signed.encode a)
    (hxb : x.regs (Signed.right (r := 47)) = Signed.encode b) :
    ∃ y, ExecWithin w (Signed.add (r := 47)) x y 15 ∧
      y.regs (Signed.result (r := 47)) = Signed.encode (a + b) ∧
      y.mem = x.mem ∧ ∀ i : Fin numRegs, 9 ≤ i.val → y.regs i = x.regs i := by
  have hw3 := width_ge_three_of_fits hfit
  have hw_eq : (w - 2) + 2 = w := by omega
  obtain ⟨y, he, hyr, hym, hyf⟩ := Signed.exec_add (r := 47)
    (signedFits_of_natAbs_le hfit ha) (signedFits_of_natAbs_le hfit hb) x hxa hxb
  rw [hw_eq] at he
  exact ⟨y, he, hyr, hym, fun i hi => hyf i (Or.inr hi)⟩

private theorem exec_signedSub {w B : ℕ} {a b : ℤ} (hfit : Fits w (8 * B + 4))
    (ha : a.natAbs ≤ B) (hb : b.natAbs ≤ B) (x : Data numRegs)
    (hxa : x.regs (Signed.left (r := 47)) = Signed.encode a)
    (hxb : x.regs (Signed.right (r := 47)) = Signed.encode b) :
    ∃ y, ExecWithin w (Signed.subtract (r := 47)) x y 17 ∧
      y.regs (Signed.result (r := 47)) = Signed.encode (a - b) ∧
      y.mem = x.mem ∧ ∀ i : Fin numRegs, 9 ≤ i.val → y.regs i = x.regs i := by
  have hw3 := width_ge_three_of_fits hfit
  have hw_eq : (w - 2) + 2 = w := by omega
  obtain ⟨y, he, hyr, hym, hyf⟩ := Signed.exec_subtract (r := 47)
    (signedFits_of_natAbs_le hfit ha) (signedFits_of_natAbs_le hfit hb) x hxa hxb
  rw [hw_eq] at he
  exact ⟨y, he, hyr, hym, fun i hi => hyf i (Or.inr hi)⟩

private theorem exec_signedMul {w B : ℕ} {a b : ℤ} (hfit : Fits w (8 * B + 4))
    (ha : a.natAbs ≤ B) (hb : b.natAbs ≤ B) (hab : (a * b).natAbs ≤ B) (x : Data numRegs)
    (hxa : x.regs (Signed.left (r := 47)) = Signed.encode a)
    (hxb : x.regs (Signed.right (r := 47)) = Signed.encode b) :
    ∃ y, ExecWithin w (Signed.multiply (r := 47)) x y 14 ∧
      y.regs (Signed.result (r := 47)) = Signed.encode (a * b) ∧
      y.mem = x.mem ∧ ∀ i : Fin numRegs, 9 ≤ i.val → y.regs i = x.regs i := by
  have hw3 := width_ge_three_of_fits hfit
  have hw_eq : (w - 2) + 2 = w := by omega
  obtain ⟨y, he, hyr, hym, hyf⟩ := Signed.exec_multiply (r := 47)
    (signedFits_of_natAbs_le hfit ha) (signedFits_of_natAbs_le hfit hb)
    (signedFits_of_natAbs_le hfit hab) x hxa hxb
  rw [hw_eq] at he
  exact ⟨y, he, hyr, hym, fun i hi => hyf i (Or.inr hi)⟩

/-- Add `Signed.right` into key `rTrieKey` of depth-`rDim` trie `rTrieRoot`. -/
private def trieAdd : Code .standard numRegs :=
  .seq trieGet
    (.seq (ram[ Signed.left ← rTrieVal ])
      (.seq (Signed.add (r := 47))
        (.seq (ram[ rTrieVal ← Signed.result ]) trieSet)))

private theorem trieAdd_preserves (i : Fin numRegs) :
    9 ≤ i.val ∧ i ≠ rFree ∧ (i.val < 18 ∨ 23 ≤ i.val) → trieAdd.Preserves i := by
  decide +kernel +revert

private theorem exec_trieAdd {w lo d root key free B : ℕ} {delta : ℤ}
    {S : Set ℕ} {fnZ : ℕ → ℤ} (x : Data numRegs)
    (hz : x.regs rZero = 0) (ho : x.regs rOne = 1) (hd : x.regs rDim = d)
    (hr : x.regs rTrieRoot = root) (hk : x.regs rTrieKey = key)
    (hdelta : x.regs (Signed.right (r := 47)) = Signed.encode delta)
    (hfree : x.regs rFree = free)
    (hlo : 1 ≤ lo) (hfree_lo : lo ≤ free) (hroot : 0 < root) (hS : S ⊆ Set.Ico lo free)
    (hrep : TrieRep x.mem d root S (fun m => Signed.encode (fnZ m)))
    (hkey_lt : key < 2 ^ d)
    (hfn_le : ∀ m, (fnZ m).natAbs ≤ B) (hdelta_le : delta.natAbs ≤ B)
    (hfit_val : Fits w (8 * B + 4))
    (hfit_free : Fits w (free + 2 * d)) (hfit_d : Fits w d) (hfit_key : Fits w key) :
    ∃ y S' free', ExecWithin w trieAdd x y (23 * d + 31) ∧
      y.regs rFree = free' ∧ free ≤ free' ∧ free' ≤ free + 2 * d ∧
      S' ⊆ Set.Ico lo free' ∧
      (∀ a, a < lo ∨ free' ≤ a → y.mem a = x.mem a) ∧
      TrieRep y.mem d root S'
        (fun m => Signed.encode (if m % 2 ^ d = key then fnZ key + delta else fnZ m)) ∧
      ∀ i : Fin numRegs, 9 ≤ i.val ∧ i ≠ rFree ∧ (i.val < 18 ∨ 23 ≤ i.val) →
        y.regs i = x.regs i := by
  have htrie_ro : HoldsTrie x.mem free d root (fun m => Signed.encode (fnZ m)) :=
    ⟨S, fun a ha => ⟨hlo.trans (hS ha).1, (hS ha).2⟩, hrep⟩
  obtain ⟨u₁, he₁, hu₁_val, hu₁_mem, hu₁_regs⟩ := exec_trieGet x hz ho hd hr hk htrie_ro
    (hfit_free.of_le (by omega)) hfit_d hfit_key
  let u₂ := u₁.set (Signed.left (r := 47)) (Signed.encode (fnZ key))
  have he₂ : ExecWithin (B := .standard) w (ram[ Signed.left ← rTrieVal ]) u₁ u₂ 1 := by
    wram_exec [hu₁_val]
  have hu₂_right : u₂.regs (Signed.right (r := 47)) = Signed.encode delta := by
    simp only [u₂, Data.set_regs_of_ne (by decide : Signed.right (r := 47) ≠ Signed.left)]
    exact (hu₁_regs _ (Or.inl (by decide))).trans hdelta
  obtain ⟨u₃, he₃, hu₃_res, hu₃_mem, hu₃_regs⟩ := exec_signedAdd hfit_val (hfn_le key) hdelta_le u₂
    (by simp [u₂]) hu₂_right
  let u₄ := u₃.set rTrieVal (Signed.encode (fnZ key + delta))
  have he₄ : ExecWithin (B := .standard) w (ram[ rTrieVal ← Signed.result ]) u₃ u₄ 1 := by
    wram_exec [hu₃_res]
  have hu₄_mem : u₄.mem = x.mem := hu₃_mem.trans hu₁_mem
  have reg_u₄ (i : Fin numRegs) (hi9 : 9 ≤ i.val) (hi18 : i.val < 18 ∨ 23 ≤ i.val) :
      u₄.regs i = x.regs i := by
    have hne_val : i ≠ rTrieVal := by intro h; subst h; simp at hi18
    have hne_left : i ≠ Signed.left (r := 47) := by intro h; subst h; simp at hi9
    simp only [u₄, Data.set_regs_of_ne hne_val]
    rw [hu₃_regs i hi9]
    simp only [u₂, Data.set_regs_of_ne hne_left]
    exact hu₁_regs i hi18
  obtain ⟨y, S', free', he₅, hyfree, hle1, hle2, hS', hyframe, hyrep, _⟩ :=
    exec_trieSet (val := Signed.encode (fnZ key + delta)) (free := free) u₄
      (reg_u₄ rZero (by decide) (Or.inl (by decide)) |>.trans hz)
      (reg_u₄ rOne (by decide) (Or.inl (by decide)) |>.trans ho)
      (reg_u₄ rDim (by decide) (Or.inl (by decide)) |>.trans hd)
      (reg_u₄ rTrieRoot (by decide) (Or.inl (by decide)) |>.trans hr)
      (reg_u₄ rTrieKey (by decide) (Or.inl (by decide)) |>.trans hk)
      (by simp [u₄])
      (reg_u₄ rFree (by decide) (Or.inl (by decide)) |>.trans hfree)
      hlo hfree_lo hroot hS (by rwa [hu₄_mem]) hkey_lt hfit_free hfit_d hfit_key
  have htot : ExecWithin w trieAdd x y (23 * d + 31) :=
    (he₁.seq (he₂.seq (he₃.seq (he₄.seq he₅)))).mono (by omega)
  refine ⟨y, S', free', htot, hyfree, hle1, hle2, hS',
    fun a ha => (hyframe a ha).trans (congrFun hu₄_mem a), ?_,
    fun i hi => htot.regs_eq (trieAdd_preserves i hi)⟩
  convert hyrep using 1
  funext m
  split_ifs <;> rfl

/-! ### Bounded-cardinality subset enumeration (`genLowSubsets`, `extractCoords`, `flipHighDom`) -/

/-- Interleaved `(mask, size)` domain layout at `base`: entry `p` stores `setMask xs[p]` at
`base + 2 * p` and `#xs[p]` at `base + 2 * p + 1`. -/
private def HoldsDom {d : ℕ} (mem : ℕ → ℕ) (base : ℕ) (xs : List (Finset (Fin d))) : Prop :=
  ∀ p (hp : p < xs.length),
    mem (base + 2 * p) = setMask xs[p] ∧ mem (base + 2 * p + 1) = #xs[p]

/-- Inner step of `genLowSubsets`: extend `xs[rGenPos]` with `rGenBitMask` when `#xs[p] < k`. -/
private def genInnerStep : Code .standard numRegs := ram[
  rGenTmp ← rGenPos + rGenPos;
  rGenTmp ← rDomPtr + rGenTmp;
  rTrieTmp ← rGenTmp + rOne;
  rTrieTmp ← *rTrieTmp;
  if rTrieTmp < rMaxCard then [
    rTrieTmp ← rTrieTmp + rOne;
    rCellSaved ← rDomLen + rDomLen;
    rCellSaved ← rDomPtr + rCellSaved;
    rCellSaved ← rCellSaved + rOne;
    *rCellSaved ← rTrieTmp;
    rGenTmp ← *rGenTmp;
    rGenTmp ← rGenTmp ||| rGenBitMask;
    rCellSaved ← rDomLen + rDomLen;
    rCellSaved ← rDomPtr + rCellSaved;
    *rCellSaved ← rGenTmp;
    rDomLen ← rDomLen + rOne
  ] else [
    rDomLen ← rDomLen
  ];
  rGenPos ← rGenPos + rOne ]

/-- Outer step of `genLowSubsets`: process coordinate `coords[rGenIdx]`. -/
private def genOuterStep : Code .standard numRegs :=
  .seq (ram[
    rGenTmp ← rCoordsPtr + rGenIdx;
    rGenTmp ← *rGenTmp;
    rGenBitMask ← rOne <<< rGenTmp;
    rGenOldLen ← rDomLen;
    rGenPos ← #0 ])
  (.seq (.loop (.lt rGenPos rGenOldLen) genInnerStep)
    (ram[ rGenIdx ← rGenIdx + rOne ]))

/-- Generate all subsets of `coords[0 .. rCoordsLen - 1]` of size `≤ rMaxCard` at `rDomPtr`. -/
private def genLowSubsets : Code .standard numRegs :=
  .seq (ram[
    *rDomPtr ← rZero;
    rGenTmp ← rDomPtr + rOne;
    *rGenTmp ← rZero;
    rDomLen ← #1;
    rGenIdx ← #0 ])
  (.loop (.lt rGenIdx rCoordsLen) genOuterStep)

private theorem genLowSubsets_preserves (i : Fin numRegs) :
    i ≠ rTrieTmp ∧ i ≠ rCellSaved ∧ (i.val < 27 ∨ 33 ≤ i.val) → genLowSubsets.Preserves i := by
  decide +kernel +revert

private theorem exec_genLowSubsets {w d coordsPtr domPtr k : ℕ} (coords : List (Fin d))
    (x : Data numRegs)
    (hz : x.regs rZero = 0) (ho : x.regs rOne = 1)
    (hcptr : x.regs rCoordsPtr = coordsPtr) (hclen : x.regs rCoordsLen = coords.length)
    (hk : x.regs rMaxCard = k) (hdptr : x.regs rDomPtr = domPtr)
    (hnd : coords.Nodup)
    (hcoords_mem : ∀ j (hj : j < coords.length), x.mem (coordsPtr + j) = coords[j].val)
    (hdisj : coordsPtr + coords.length ≤ domPtr)
    (hfit_mem : Fits w (domPtr + 2 * ∑ j ∈ range (k + 1), coords.length.choose j))
    (hfit_mask : Fits w (2 ^ d)) :
    let outList := prefixesUpTo k coords
    ∃ y, ExecWithin w genLowSubsets x y
        (coords.length * (20 * (∑ j ∈ range (k + 1), coords.length.choose j) + 12) + 8) ∧
      y.regs rDomLen = outList.length ∧
      HoldsDom y.mem domPtr outList ∧
      (∀ a, a < domPtr ∨ domPtr + 2 * outList.length ≤ a → y.mem a = x.mem a) ∧
      ∀ i : Fin numRegs, i ≠ rTrieTmp ∧ i ≠ rCellSaved ∧ (i.val < 27 ∨ 33 ≤ i.val) →
        y.regs i = x.regs i := by
  intro outList
  set Lmax := ∑ j ∈ range (k + 1), coords.length.choose j with hLmax_def
  have hLmax_pos : 1 ≤ Lmax := by
    rw [hLmax_def, Finset.sum_range_succ']
    simp only [Nat.choose_zero_right]
    omega
  have hrun : ∃ y, ExecWithin w genLowSubsets x y (coords.length * (20 * Lmax + 12) + 8) ∧
      y.regs rDomLen = outList.length ∧
      HoldsDom y.mem domPtr outList ∧
      (∀ a, a < domPtr ∨ domPtr + 2 * outList.length ≤ a → y.mem a = x.mem a) := by
    let P_out (idx : ℕ) (s : Data numRegs) : Prop :=
      s.regs rZero = 0 ∧ s.regs rOne = 1 ∧
      s.regs rCoordsPtr = coordsPtr ∧ s.regs rCoordsLen = coords.length ∧
      s.regs rMaxCard = k ∧ s.regs rDomPtr = domPtr ∧
      s.regs rDomLen = (prefixesUpTo k (coords.take idx)).length ∧
      HoldsDom s.mem domPtr (prefixesUpTo k (coords.take idx)) ∧
      ∀ a, a < domPtr ∨ domPtr + 2 * (prefixesUpTo k (coords.take idx)).length ≤ a →
        s.mem a = x.mem a
    have houter (s : Data numRegs) (hs : P_out (s.regs rGenIdx) s)
        (hlt : s.regs rGenIdx < coords.length) :
        ∃ z, ExecWithin w genOuterStep s z (20 * Lmax + 10) ∧
          P_out (s.regs rGenIdx + 1) z ∧ z.regs rGenIdx = s.regs rGenIdx + 1 := by
      generalize hidx : s.regs rGenIdx = idx at hs hlt ⊢
      dsimp only [P_out] at hs
      obtain ⟨hsz, hso, hscptr, hsclen, hsk, hsdptr, hsdlen, hsdom, hsframe⟩ := hs
      let prev := prefixesUpTo k (coords.take idx)
      change s.regs rDomLen = prev.length at hsdlen
      change HoldsDom s.mem domPtr prev at hsdom
      change ∀ a, a < domPtr ∨ domPtr + 2 * prev.length ≤ a → s.mem a = x.mem a at hsframe
      let c := coords[idx]
      have hnd_take1 : (coords.take (idx + 1)).Nodup := hnd.sublist (List.take_sublist _ _)
      have hnd_take : (coords.take idx).Nodup := hnd.sublist (List.take_sublist _ _)
      have hnext_eq : prefixesUpTo k (coords.take (idx + 1)) =
          prev ++ (prev.filter fun S => decide (#S < k)).map (insert c) := by
        rw [List.take_succ_eq_append_getElem hlt, prefixesUpTo_append_singleton]
      have hnext_len_le : (prefixesUpTo k (coords.take (idx + 1))).length ≤ Lmax := by
        rw [length_prefixesUpTo k hnd_take1, List.length_take_of_le (by omega), hLmax_def]
        exact Finset.sum_le_sum fun j _ => Nat.choose_le_choose j (by omega)
      have hprev_len_le : prev.length ≤ (prefixesUpTo k (coords.take (idx + 1))).length := by
        rw [hnext_eq, List.length_append]; omega
      have hc_not_in_prev : ∀ S ∈ prev, c ∉ S := by
        intro S hS hcS
        have hnd_app : (coords.take idx ++ [c]).Nodup := by
          rwa [← List.take_succ_eq_append_getElem hlt]
        have hc_not : c ∉ coords.take idx := fun hc =>
          (List.nodup_append.mp hnd_app).2.2 c hc c (by simp) rfl
        have hsub : S ⊆ (coords.take idx).toFinset :=
          (((prefixesUpTo_spec k hnd_take).2 S).mp hS).1
        exact hc_not (List.mem_toFinset.mp (hsub hcS))
      have hc_mem_read : s.mem (coordsPtr + idx) = c.val := by
        rw [hsframe _ (Or.inl (by omega)), hcoords_mem idx hlt]
      have hbit_fit : Fits w (1 <<< c.val) := by
        rw [Nat.shiftLeft_eq, one_mul]
        exact hfit_mask.of_le (Nat.pow_le_pow_right Nat.two_pos c.isLt.le)
      have hsetup : ∃ u₀, ExecWithin (B := .standard) w (ram[
          rGenTmp ← rCoordsPtr + rGenIdx;
          rGenTmp ← *rGenTmp;
          rGenBitMask ← rOne <<< rGenTmp;
          rGenOldLen ← rDomLen;
          rGenPos ← #0 ]) s u₀ 5 ∧
          u₀.regs rZero = 0 ∧ u₀.regs rOne = 1 ∧
          u₀.regs rCoordsPtr = coordsPtr ∧ u₀.regs rCoordsLen = coords.length ∧
          u₀.regs rMaxCard = k ∧ u₀.regs rDomPtr = domPtr ∧
          u₀.regs rDomLen = prev.length ∧ u₀.regs rGenOldLen = prev.length ∧
          u₀.regs rGenBitMask = (1 <<< c.val) ∧ u₀.regs rGenIdx = idx ∧
          u₀.regs rGenPos = 0 ∧ u₀.mem = s.mem := by
        have haddr_c : Fits w (coordsPtr + idx) := hfit_mem.of_le (by omega)
        wram_exec [hso, hscptr, hsdlen, hidx, hc_mem_read]
        wram_simp [hsz, hso, hscptr, hsclen, hsk, hsdptr, hsdlen, hidx]
      obtain ⟨u₀, hsetup_ex, hu₀z, hu₀o, hu₀cp, hu₀cl, hu₀k, hu₀dp, hu₀dl, hu₀ol,
        hu₀bm, hu₀idx, hu₀pos, hu₀mem⟩ := hsetup
      let accAt (p : ℕ) := prev ++ ((prev.take p).filter fun S => decide (#S < k)).map (insert c)
      let P_in (p : ℕ) (q : Data numRegs) : Prop :=
        q.regs rZero = 0 ∧ q.regs rOne = 1 ∧
        q.regs rCoordsPtr = coordsPtr ∧ q.regs rCoordsLen = coords.length ∧
        q.regs rMaxCard = k ∧ q.regs rDomPtr = domPtr ∧
        q.regs rGenOldLen = prev.length ∧ q.regs rGenBitMask = (1 <<< c.val) ∧
        q.regs rGenIdx = idx ∧ q.regs rDomLen = (accAt p).length ∧
        HoldsDom q.mem domPtr (accAt p) ∧
        ∀ a, a < domPtr ∨ domPtr + 2 * (accAt p).length ≤ a → q.mem a = x.mem a
      have hinner (q : Data numRegs) (hq : P_in (q.regs rGenPos) q)
          (hp : q.regs rGenPos < prev.length) :
          ∃ q', ExecWithin w genInnerStep q q' 18 ∧
            P_in (q.regs rGenPos + 1) q' ∧ q'.regs rGenPos = q.regs rGenPos + 1 := by
        generalize hp_eq : q.regs rGenPos = p at hq hp ⊢
        dsimp only [P_in] at hq
        obtain ⟨hqz, hqo, hqcp, hqcl, hqk, hqdp, hqol, hqbm, hqidx, hqdl, hqdom, hqframe⟩ := hq
        let acc := accAt p
        change q.regs rDomLen = acc.length at hqdl
        change HoldsDom q.mem domPtr acc at hqdom
        change ∀ a, a < domPtr ∨ domPtr + 2 * acc.length ≤ a → q.mem a = x.mem a at hqframe
        have hp_lt_acc : p < acc.length := by dsimp [acc, accAt]; rw [List.length_append]; omega
        have hacc_p : acc[p] = prev[p] := by dsimp [acc, accAt]; exact List.getElem_append_left hp
        obtain ⟨hmask_p, hsize_p⟩ := hqdom p hp_lt_acc
        rw [hacc_p] at hmask_p hsize_p
        have hc_not_p : c ∉ prev[p] := hc_not_in_prev prev[p] (List.getElem_mem hp)
        by_cases hcard_lt : #prev[p] < k
        · have hacc1_eq : accAt (p + 1) = acc ++ [insert c prev[p]] := by
            dsimp only [accAt, acc]
            rw [List.take_succ_eq_append_getElem hp, List.filter_append, List.map_append]
            simp [hcard_lt]
          have hacc1_len : acc.length + 1 ≤ Lmax := by
            have hle1 : (accAt (p + 1)).length ≤
                (prefixesUpTo k (coords.take (idx + 1))).length := by
              dsimp only [accAt]
              rw [hnext_eq, List.length_append, List.length_append,
                List.length_map, List.length_map]
              have := ((List.take_sublist (p + 1) prev).filter (fun S => decide (#S < k))).length_le
              omega
            rw [hacc1_eq, List.length_append, List.length_singleton] at hle1
            exact hle1.trans hnext_len_le
          have hf_2p : Fits w (p + p) := hfit_mem.of_le (by omega)
          have hf_dp2p : Fits w (domPtr + (p + p)) := hfit_mem.of_le (by omega)
          have hf_dp2p1 : Fits w (domPtr + (p + p) + 1) := hfit_mem.of_le (by omega)
          have hf_sz1 : Fits w (#prev[p] + 1) :=
            hfit_mask.of_le ((by have := Finset.card_le_univ prev[p]; simp at this; omega :
              #prev[p] + 1 ≤ d + 1).trans (by
              have := Nat.lt_two_pow_self (n := d); omega))
          have hf_2l : Fits w (acc.length + acc.length) := hfit_mem.of_le (by omega)
          have hf_dp2l : Fits w (domPtr + (acc.length + acc.length)) := hfit_mem.of_le (by omega)
          have hf_dp2l1 : Fits w (domPtr + (acc.length + acc.length) + 1) :=
            hfit_mem.of_le (by omega)
          have hf_or : Fits w (setMask prev[p] ||| (1 <<< c.val)) := by
            rw [← setMask_insert]; exact hfit_mask.of_le (setMask_lt _).le
          have hf_l1 : Fits w (acc.length + 1) := hfit_mem.of_le (by omega)
          have hf_p1 : Fits w (p + 1) := hfit_mem.of_le (by omega)
          have h2p_eq : p + p = 2 * p := by omega
          have h2l_eq : acc.length + acc.length = 2 * acc.length := by omega
          have hread_sz : q.mem (domPtr + (p + p) + 1) = #prev[p] := by
            simpa only [h2p_eq] using hsize_p
          have hread_mk : q.mem (domPtr + (p + p)) = setMask prev[p] := by
            simpa only [h2p_eq] using hmask_p
          have hstep : ∃ q', ExecWithin w genInnerStep q q' 18 ∧
              q'.regs rZero = 0 ∧ q'.regs rOne = 1 ∧
              q'.regs rCoordsPtr = coordsPtr ∧ q'.regs rCoordsLen = coords.length ∧
              q'.regs rMaxCard = k ∧ q'.regs rDomPtr = domPtr ∧
              q'.regs rGenOldLen = prev.length ∧ q'.regs rGenBitMask = (1 <<< c.val) ∧
              q'.regs rGenIdx = idx ∧ q'.regs rDomLen = acc.length + 1 ∧
              q'.regs rGenPos = p + 1 ∧
              q'.mem = Function.update
                (Function.update q.mem (domPtr + 2 * acc.length + 1) (#prev[p] + 1))
                (domPtr + 2 * acc.length) (setMask (insert c prev[p])) := by
            unfold genInnerStep
            wram_exec [hqo, hqk, hqdp, hqdl, hqbm, hp_eq, hread_sz, hcard_lt, hread_mk]
            refine ⟨hqz, hqo, hqcp, hqcl, hqk, hqdp, hqol, hqbm, hqidx, ?_, ?_, ?_⟩
            · wram_simp [hqdl]
            · wram_simp [hp_eq]
            · wram_simp [h2l_eq, hread_mk, setMask_insert]
          obtain ⟨q', hq'_ex, hq'z, hq'o, hq'cp, hq'cl, hq'k, hq'dp, hq'ol, hq'bm,
            hq'idx, hq'dl, hq'pos, hq'mem⟩ := hstep
          refine ⟨q', hq'_ex, ?_, hq'pos⟩
          dsimp only [P_in]
          rw [hacc1_eq]
          refine ⟨hq'z, hq'o, hq'cp, hq'cl, hq'k, hq'dp, hq'ol, hq'bm, hq'idx,
            by rw [hq'dl]; simp [acc], ?_, ?_⟩
          · intro r hr
            rw [List.length_append, List.length_singleton] at hr
            by_cases hr_eq : r = acc.length
            · subst hr_eq
              simp only [List.getElem_append_right (le_rfl), Nat.sub_self, List.getElem_singleton,
                hq'mem, card_insert_of_notMem hc_not_p]
              refine ⟨Function.update_self _ _ _, ?_⟩
              rw [Function.update_of_ne (by omega), Function.update_self]
            · have hr_lt : r < acc.length := by omega
              simp only [List.getElem_append_left hr_lt, hq'mem]
              refine ⟨?_, ?_⟩
              · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
                exact (hqdom r hr_lt).1
              · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
                exact (hqdom r hr_lt).2
          · intro a ha
            rw [List.length_append, List.length_singleton] at ha
            rw [hq'mem, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact hqframe a (by omega)
        · have hacc1_eq : accAt (p + 1) = acc := by
            dsimp only [accAt, acc]
            rw [List.take_succ_eq_append_getElem hp, List.filter_append, List.map_append]
            simp [hcard_lt]
          have hprev_le : prev.length ≤ Lmax := hprev_len_le.trans hnext_len_le
          have hf_2p : Fits w (p + p) := hfit_mem.of_le (by omega)
          have hf_dp2p : Fits w (domPtr + (p + p)) := hfit_mem.of_le (by omega)
          have hf_dp2p1 : Fits w (domPtr + (p + p) + 1) := hfit_mem.of_le (by omega)
          have hf_p1 : Fits w (p + 1) := hfit_mem.of_le (by omega)
          have h2p_eq : p + p = 2 * p := by omega
          have hread_sz : q.mem (domPtr + (p + p) + 1) = #prev[p] := by
            simpa only [h2p_eq] using hsize_p
          have hstep : ∃ q', ExecWithin w genInnerStep q q' 18 ∧
              q'.regs rZero = 0 ∧ q'.regs rOne = 1 ∧
              q'.regs rCoordsPtr = coordsPtr ∧ q'.regs rCoordsLen = coords.length ∧
              q'.regs rMaxCard = k ∧ q'.regs rDomPtr = domPtr ∧
              q'.regs rGenOldLen = prev.length ∧ q'.regs rGenBitMask = (1 <<< c.val) ∧
              q'.regs rGenIdx = idx ∧ q'.regs rDomLen = acc.length ∧
              q'.regs rGenPos = p + 1 ∧ q'.mem = q.mem := by
            unfold genInnerStep
            wram_exec [hqo, hqk, hqdp, hqdl, hp_eq, hread_sz, hcard_lt]
            wram_simp [hqz, hqo, hqcp, hqcl, hqk, hqdp, hqol, hqbm, hqidx, hqdl, hp_eq]
          obtain ⟨q', hq'_ex, hq'z, hq'o, hq'cp, hq'cl, hq'k, hq'dp, hq'ol, hq'bm,
            hq'idx, hq'dl, hq'pos, hq'mem⟩ := hstep
          refine ⟨q', hq'_ex, ?_, hq'pos⟩
          dsimp only [P_in]
          rw [hacc1_eq, hq'mem]
          exact ⟨hq'z, hq'o, hq'cp, hq'cl, hq'k, hq'dp, hq'ol, hq'bm, hq'idx, hq'dl, hqdom, hqframe⟩
      have hu₀_in : P_in (u₀.regs rGenPos) u₀ := by
        dsimp only [P_in, accAt]
        rw [hu₀pos, List.take_zero, List.filter_nil, List.map_nil, List.append_nil, hu₀mem]
        exact ⟨hu₀z, hu₀o, hu₀cp, hu₀cl, hu₀k, hu₀dp, hu₀ol, hu₀bm, hu₀idx, hu₀dl, hsdom, hsframe⟩
      obtain ⟨u₁, hloop_in, hu₁P, _⟩ := ExecWithin.loop_count P_in
        (fun q hq => hq.2.2.2.2.2.2.1) hinner (by simp [hu₀pos]) hu₀_in
      obtain ⟨hu₁z, hu₁o, hu₁cp, hu₁cl, hu₁k, hu₁dp, _, _, hu₁idx, hu₁dl, hu₁dom, hu₁frame⟩ := hu₁P
      dsimp only [accAt] at hu₁dl hu₁dom hu₁frame
      rw [List.take_length, ← hnext_eq] at hu₁dl hu₁dom hu₁frame
      have hf_idx1 : Fits w (idx + 1) := hfit_mem.of_le (by omega)
      let z := u₁.set rGenIdx (idx + 1)
      have hinc : ExecWithin (B := .standard) w (ram[ rGenIdx ← rGenIdx + rOne ]) u₁ z 1 := by
        wram_exec [hu₁idx, hu₁o]
      have hprev_le_Lmax : prev.length ≤ Lmax := hprev_len_le.trans hnext_len_le
      have hmul_le : 20 * prev.length ≤ 20 * Lmax := Nat.mul_le_mul_left 20 hprev_le_Lmax
      have hcost : 5 + ((prev.length - u₀.regs rGenPos) * (18 + 2) + 2) + 1 ≤ 20 * Lmax + 10 := by
        rw [hu₀pos, Nat.sub_zero, Nat.mul_comm _ 20]
        omega
      refine ⟨z, (hsetup_ex.seq (hloop_in.seq hinc)).mono hcost, ?_, by simp [z]⟩
      dsimp only [P_out]
      exact ⟨by simp [z, hu₁z], by simp [z, hu₁o], by simp [z, hu₁cp], by simp [z, hu₁cl],
        by simp [z, hu₁k], by simp [z, hu₁dp], by simp [z, hu₁dl], hu₁dom, hu₁frame⟩
    have hf_dp1 : Fits w (domPtr + 1) := hfit_mem.of_le (by omega)
    have hinit : ∃ s₀, ExecWithin (B := .standard) w (ram[
        *rDomPtr ← rZero;
        rGenTmp ← rDomPtr + rOne;
        *rGenTmp ← rZero;
        rDomLen ← #1;
        rGenIdx ← #0 ]) x s₀ 5 ∧
        s₀.regs rZero = 0 ∧ s₀.regs rOne = 1 ∧
        s₀.regs rCoordsPtr = coordsPtr ∧ s₀.regs rCoordsLen = coords.length ∧
        s₀.regs rMaxCard = k ∧ s₀.regs rDomPtr = domPtr ∧
        s₀.regs rDomLen = 1 ∧ s₀.regs rGenIdx = 0 ∧
        s₀.mem = Function.update (Function.update x.mem domPtr 0) (domPtr + 1) 0 := by
      wram_exec [hz, ho, hdptr]
      wram_simp [hz, ho, hcptr, hclen, hk, hdptr]
    obtain ⟨s₀, hinit_ex, hs₀z, hs₀o, hs₀cp, hs₀cl, hs₀k, hs₀dp, hs₀dl, hs₀idx, hs₀mem⟩ := hinit
    have hs₀P : P_out (s₀.regs rGenIdx) s₀ := by
      dsimp only [P_out]
      rw [hs₀idx, List.take_zero]
      refine ⟨hs₀z, hs₀o, hs₀cp, hs₀cl, hs₀k, hs₀dp, hs₀dl, ?_, ?_⟩
      · intro p hp
        obtain rfl : p = 0 := by simp [prefixesUpTo] at hp; omega
        simp [prefixesUpTo, hs₀mem]
      · intro a ha
        simp only [prefixesUpTo, List.foldl_nil, List.length_singleton] at ha
        rw [hs₀mem, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    obtain ⟨y, hloop_out, hyP, _⟩ := ExecWithin.loop_count P_out
      (fun s hs => hs.2.2.2.1) houter (by simp [hs₀idx]) hs₀P
    obtain ⟨_, _, _, _, _, _, hydl, hydom, hyframe⟩ := hyP
    rw [List.take_length] at hydl hydom hyframe
    refine ⟨y, (hinit_ex.seq hloop_out).mono (by
      rw [hs₀idx, Nat.sub_zero]
      change 5 + (coords.length * (20 * Lmax + 12) + 2) ≤ coords.length * (20 * Lmax + 12) + 8
      omega),
      hydl, hydom, hyframe⟩
  obtain ⟨y, he, hydl, hydom, hyframe⟩ := hrun
  exact ⟨y, he, hydl, hydom, hyframe, fun i hi => he.regs_eq (genLowSubsets_preserves i hi)⟩

/-- Extract set bits of `rTrieKey = setMask C` into `rCoordsPtr`, leaving `#C` in `rCoordsLen`. -/
private def extractStep : Code .standard numRegs := ram[
  rGenTmp ← rTrieRem &&& rOne;
  rTrieRem ← rTrieRem >>> rOne;
  if rZero < rGenTmp then [
    rGenTmp ← rCoordsPtr + rCoordsLen;
    *rGenTmp ← rGenIdx;
    rCoordsLen ← rCoordsLen + rOne
  ] else [
    rCoordsLen ← rCoordsLen
  ];
  rGenIdx ← rGenIdx + rOne ]

/-- Scan bits `0 .. rDim - 1` of `rTrieKey` and write set indices to `rCoordsPtr`. -/
private def extractCoords : Code .standard numRegs :=
  .seq (ram[ rTrieRem ← rTrieKey; rCoordsLen ← #0; rGenIdx ← #0 ])
    (.loop (.lt rGenIdx rDim) extractStep)

private theorem extractCoords_preserves (i : Fin numRegs) :
    i ≠ rTrieRem ∧ i ≠ rCoordsLen ∧ i ≠ rGenIdx ∧ i ≠ rGenTmp → extractCoords.Preserves i := by
  decide +kernel +revert

private theorem exec_extractCoords {w d coordsPtr : ℕ} (C : Finset (Fin d)) (x : Data numRegs)
    (hz : x.regs rZero = 0) (ho : x.regs rOne = 1) (hd : x.regs rDim = d)
    (hk : x.regs rTrieKey = setMask C) (hcptr : x.regs rCoordsPtr = coordsPtr)
    (hfit_mem : Fits w (coordsPtr + d)) (hfit_mask : Fits w (2 ^ d)) :
    let cList := (List.finRange d).filter (· ∈ C)
    ∃ y, ExecWithin w extractCoords x y (11 * d + 5) ∧
      y.regs rCoordsLen = cList.length ∧
      (∀ j (hj : j < cList.length), y.mem (coordsPtr + j) = cList[j].val) ∧
      (∀ a, a < coordsPtr ∨ coordsPtr + d ≤ a → y.mem a = x.mem a) ∧
      ∀ i : Fin numRegs, i ≠ rTrieRem ∧ i ≠ rCoordsLen ∧ i ≠ rGenIdx ∧ i ≠ rGenTmp →
        y.regs i = x.regs i := by
  intro cList
  have hfit_d : Fits w d := hfit_mask.of_le Nat.lt_two_pow_self.le
  have hrun : ∃ y, ExecWithin w extractCoords x y (11 * d + 5) ∧
      y.regs rCoordsLen = cList.length ∧
      (∀ j (hj : j < cList.length), y.mem (coordsPtr + j) = cList[j].val) ∧
      (∀ a, a < coordsPtr ∨ coordsPtr + d ≤ a → y.mem a = x.mem a) := by
    let curAt (b : ℕ) := ((List.finRange d).take b).filter (· ∈ C)
    let P (b : ℕ) (s : Data numRegs) : Prop :=
      s.regs rZero = 0 ∧ s.regs rOne = 1 ∧ s.regs rDim = d ∧
      s.regs rCoordsPtr = coordsPtr ∧ s.regs rCoordsLen = (curAt b).length ∧
      s.regs rTrieRem = setMask C / 2 ^ b ∧
      (∀ j (hj : j < (curAt b).length), s.mem (coordsPtr + j) = (curAt b)[j].val) ∧
      (∀ a, a < coordsPtr ∨ coordsPtr + (curAt b).length ≤ a → s.mem a = x.mem a)
    have hbody (s : Data numRegs) (hs : P (s.regs rGenIdx) s) (hb : s.regs rGenIdx < d) :
        ∃ z, ExecWithin w extractStep s z 9 ∧ P (s.regs rGenIdx + 1) z ∧
          z.regs rGenIdx = s.regs rGenIdx + 1 := by
      generalize hb_eq : s.regs rGenIdx = b at hs hb ⊢
      dsimp only [P] at hs
      obtain ⟨hsz, hso, hsd, hscp, hscl, hsrem, hsmem, hsframe⟩ := hs
      let cur := curAt b
      change s.regs rCoordsLen = cur.length at hscl
      change ∀ j (hj : j < cur.length), s.mem (coordsPtr + j) = cur[j].val at hsmem
      change ∀ a, a < coordsPtr ∨ coordsPtr + cur.length ≤ a → s.mem a = x.mem a at hsframe
      have hcur_len_le : cur.length ≤ b := by
        calc cur.length ≤ ((List.finRange d).take b).length := List.length_filter_le _ _
          _ ≤ b := by simp
      let ib : Fin d := ⟨b, hb⟩
      have htake1 : (List.finRange d).take (b + 1) = (List.finRange d).take b ++ [ib] := by
        rw [List.take_succ_eq_append_getElem (by simp [hb])]
        simp [ib]
      have hrem_fit : Fits w (s.regs rTrieRem) := by
        rw [hsrem]; exact hfit_mask.of_le ((Nat.div_le_self _ _).trans (setMask_lt C).le)
      have hand_fit : Fits w (s.regs rTrieRem &&& 1) :=
        hfit_d.of_le (by rw [Nat.and_one_is_mod]; omega)
      have hshr_fit : Fits w (s.regs rTrieRem >>> 1) := by
        rw [Nat.shiftRight_eq_div_pow]; exact hrem_fit.of_le (Nat.div_le_self _ _)
      have hb1_fit : Fits w (b + 1) := hfit_d.of_le (by omega)
      have hbit_iff : s.regs rTrieRem &&& 1 = (if ib ∈ C then 1 else 0) := by
        rw [hsrem, Nat.and_one_is_mod]
        have htb := testBit_setMask C ib
        rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_decide] at htb
        change setMask C / 2 ^ b % 2 = if ib ∈ C then 1 else 0
        have hmod2 : setMask C / 2 ^ b % 2 < 2 := Nat.mod_lt _ Nat.two_pos
        by_cases hmemC : ib ∈ C
        · simp only [hmemC, ↓reduceIte]; exact htb.mpr hmemC
        · have h0 : setMask C / 2 ^ b % 2 ≠ 1 := mt htb.mp hmemC
          simp only [hmemC, ↓reduceIte]; omega
      have hshr_eq : s.regs rTrieRem >>> 1 = setMask C / 2 ^ (b + 1) := by
        rw [hsrem, Nat.shiftRight_eq_div_pow, pow_one, Nat.div_div_eq_div_mul, pow_succ]
      by_cases hmemC : ib ∈ C
      · have hbit1 : s.regs rTrieRem &&& 1 = 1 := by simp [hbit_iff, hmemC]
        have hf_addr : Fits w (coordsPtr + cur.length) := hfit_mem.of_le (by omega)
        have hf_cl1 : Fits w (cur.length + 1) := hfit_d.of_le (by omega)
        have hcur1 : curAt (b + 1) = cur ++ [ib] := by
          dsimp only [curAt, cur]
          rw [htake1, List.filter_append, List.filter_cons_of_pos (by simp [hmemC]),
            List.filter_nil]
        have hstep : ∃ z, ExecWithin w extractStep s z 9 ∧
            z.regs rZero = 0 ∧ z.regs rOne = 1 ∧ z.regs rDim = d ∧
            z.regs rCoordsPtr = coordsPtr ∧ z.regs rCoordsLen = cur.length + 1 ∧
            z.regs rTrieRem = setMask C / 2 ^ (b + 1) ∧ z.regs rGenIdx = b + 1 ∧
            z.mem = Function.update s.mem (coordsPtr + cur.length) b := by
          unfold extractStep
          wram_exec [hsz, hso, hscp, hscl, hb_eq, hbit1]
          wram_simp [hsz, hso, hsd, hscp, hscl, hb_eq, hshr_eq]
        obtain ⟨z, hz_ex, hzz, hzo, hzd, hzcp, hzcl, hzrem, hzidx, hzmem⟩ := hstep
        refine ⟨z, hz_ex, ?_, hzidx⟩
        dsimp only [P]
        rw [hcur1]
        refine ⟨hzz, hzo, hzd, hzcp, by simp [hzcl], hzrem, ?_, ?_⟩
        · intro j hj
          rw [List.length_append, List.length_singleton] at hj
          by_cases hj_eq : j = cur.length
          · subst hj_eq
            simp [hzmem, ib]
          · have hj_lt : j < cur.length := by omega
            rw [List.getElem_append_left hj_lt, hzmem, Function.update_of_ne (by omega)]
            exact hsmem j hj_lt
        · intro a ha
          rw [List.length_append, List.length_singleton] at ha
          rw [hzmem, Function.update_of_ne (by omega)]
          exact hsframe a (by omega)
      · have hbit0 : s.regs rTrieRem &&& 1 = 0 := by simp [hbit_iff, hmemC]
        have hcur1 : curAt (b + 1) = cur := by
          dsimp only [curAt, cur]
          rw [htake1, List.filter_append, List.filter_cons_of_neg (by simp [hmemC]),
            List.filter_nil, List.append_nil]
        have hstep : ∃ z, ExecWithin w extractStep s z 9 ∧
            z.regs rZero = 0 ∧ z.regs rOne = 1 ∧ z.regs rDim = d ∧
            z.regs rCoordsPtr = coordsPtr ∧ z.regs rCoordsLen = cur.length ∧
            z.regs rTrieRem = setMask C / 2 ^ (b + 1) ∧ z.regs rGenIdx = b + 1 ∧
            z.mem = s.mem := by
          unfold extractStep
          wram_exec [hsz, hso, hscl, hb_eq, hbit0]
          wram_simp [hsz, hso, hsd, hscp, hscl, hb_eq, hshr_eq]
        obtain ⟨z, hz_ex, hzz, hzo, hzd, hzcp, hzcl, hzrem, hzidx, hzmem⟩ := hstep
        refine ⟨z, hz_ex, ?_, hzidx⟩
        dsimp only [P]
        rw [hcur1, hzmem]
        exact ⟨hzz, hzo, hzd, hzcp, hzcl, hzrem, hsmem, hsframe⟩
    let x₀ := ((x.set rTrieRem (setMask C)).set rCoordsLen 0).set rGenIdx 0
    have hinit : ExecWithin (B := .standard) w
        (ram[ rTrieRem ← rTrieKey; rCoordsLen ← #0; rGenIdx ← #0 ]) x x₀ 3 := by
      wram_exec [hk]
    have hx₀ : P (x₀.regs rGenIdx) x₀ := by
      dsimp only [P, curAt]
      simp [x₀, hz, ho, hd, hcptr]
    obtain ⟨y, hloop, hyP, _⟩ := ExecWithin.loop_count P (fun s hs => hs.2.2.1) hbody
      (by simp [x₀]) hx₀
    obtain ⟨_, _, _, _, hycl, _, hymem, hyframe⟩ := hyP
    have hcur_d : curAt d = cList := by
      dsimp only [curAt, cList]
      rw [List.take_of_length_le (by simp)]
    rw [hcur_d] at hycl hymem hyframe
    have hcList_le : cList.length ≤ d := by
      calc cList.length ≤ (List.finRange d).length := List.length_filter_le _ _
        _ = d := List.length_finRange
    refine ⟨y, (hinit.seq hloop).mono (by simp [x₀]; omega), hycl, hymem,
      fun a ha => hyframe a (by omega)⟩
  obtain ⟨y, he, hycl, hymem, hyframe⟩ := hrun
  exact ⟨y, he, hycl, hymem, hyframe, fun i hi => he.regs_eq (extractCoords_preserves i hi)⟩

/-- Flip `(Y, #Y) ↦ (C \ Y, #C - #Y)` in place at `rDomPtr` for `p < rDomLen`. -/
private def flipStep : Code .standard numRegs := ram[
  rGenTmp ← rGenPos + rGenPos;
  rGenTmp ← rDomPtr + rGenTmp;
  rTrieTmp ← *rGenTmp;
  rTrieTmp ← rTrieKey ^^^ rTrieTmp;
  *rGenTmp ← rTrieTmp;
  rGenTmp ← rGenTmp + rOne;
  rTrieTmp ← *rGenTmp;
  rTrieTmp ← rCoordsLen - rTrieTmp;
  *rGenTmp ← rTrieTmp;
  rGenPos ← rGenPos + rOne ]

/-- Complement every subset in `rDomPtr[0 .. rDomLen - 1]` inside `rTrieKey = setMask C`. -/
private def flipHighDom : Code .standard numRegs :=
  .seq (ram[ rGenPos ← #0 ]) (.loop (.lt rGenPos rDomLen) flipStep)

private theorem flipHighDom_preserves (i : Fin numRegs) :
    i ≠ rTrieTmp ∧ i ≠ rGenPos ∧ i ≠ rGenTmp → flipHighDom.Preserves i := by
  decide +kernel +revert

private theorem exec_flipHighDom {w d domPtr : ℕ} (C : Finset (Fin d))
    (ys : List (Finset (Fin d))) (x : Data numRegs)
    (ho : x.regs rOne = 1) (hk : x.regs rTrieKey = setMask C)
    (hcl : x.regs rCoordsLen = #C) (hdptr : x.regs rDomPtr = domPtr)
    (hdlen : x.regs rDomLen = ys.length)
    (hys_sub : ∀ Y ∈ ys, Y ⊆ C) (hdom : HoldsDom x.mem domPtr ys)
    (hfit_mem : Fits w (domPtr + 2 * ys.length)) (hfit_mask : Fits w (2 ^ d)) :
    ∃ y, ExecWithin w flipHighDom x y (12 * ys.length + 3) ∧
      HoldsDom y.mem domPtr (ys.map (C \ ·)) ∧
      (∀ a, a < domPtr ∨ domPtr + 2 * ys.length ≤ a → y.mem a = x.mem a) ∧
      ∀ i : Fin numRegs, i ≠ rTrieTmp ∧ i ≠ rGenPos ∧ i ≠ rGenTmp → y.regs i = x.regs i := by
  have hrun : ∃ y, ExecWithin w flipHighDom x y (12 * ys.length + 3) ∧
      HoldsDom y.mem domPtr (ys.map (C \ ·)) ∧
      (∀ a, a < domPtr ∨ domPtr + 2 * ys.length ≤ a → y.mem a = x.mem a) := by
    let P (p : ℕ) (s : Data numRegs) : Prop :=
      s.regs rOne = 1 ∧ s.regs rTrieKey = setMask C ∧ s.regs rCoordsLen = #C ∧
      s.regs rDomPtr = domPtr ∧ s.regs rDomLen = ys.length ∧
      (∀ j (hj : j < ys.length), j < p →
        s.mem (domPtr + 2 * j) = setMask (C \ ys[j]) ∧
        s.mem (domPtr + 2 * j + 1) = #(C \ ys[j])) ∧
      (∀ j (hj : j < ys.length), p ≤ j →
        s.mem (domPtr + 2 * j) = setMask ys[j] ∧ s.mem (domPtr + 2 * j + 1) = #ys[j]) ∧
      (∀ a, a < domPtr ∨ domPtr + 2 * ys.length ≤ a → s.mem a = x.mem a)
    have hbody (s : Data numRegs) (hs : P (s.regs rGenPos) s) (hp : s.regs rGenPos < ys.length) :
        ∃ z, ExecWithin w flipStep s z 10 ∧ P (s.regs rGenPos + 1) z ∧
          z.regs rGenPos = s.regs rGenPos + 1 := by
      generalize hp_eq : s.regs rGenPos = p at hs hp ⊢
      dsimp only [P] at hs
      obtain ⟨hso, hsk, hscl, hsdp, hsdl, hdone, htodo, hsframe⟩ := hs
      obtain ⟨hmk_p, hsz_p⟩ := htodo p hp le_rfl
      have hsub_p : ys[p] ⊆ C := hys_sub ys[p] (List.getElem_mem hp)
      have hf_2p : Fits w (p + p) := hfit_mem.of_le (by omega)
      have hf_dp2p : Fits w (domPtr + (p + p)) := hfit_mem.of_le (by omega)
      have hf_dp2p1 : Fits w (domPtr + (p + p) + 1) := hfit_mem.of_le (by omega)
      have hf_xor : Fits w (setMask C ^^^ setMask ys[p]) := by
        rw [← setMask_sdiff hsub_p]; exact hfit_mask.of_le (setMask_lt _).le
      have hf_sub : Fits w (#C - #ys[p]) :=
        hfit_mask.of_le ((by have := Finset.card_le_univ C; simp at this; omega :
          #C - #ys[p] ≤ d).trans Nat.lt_two_pow_self.le)
      have hf_p1 : Fits w (p + 1) := hfit_mem.of_le (by omega)
      have h2p_eq : p + p = 2 * p := by omega
      have hrmk : s.mem (domPtr + (p + p)) = setMask ys[p] := by simpa only [h2p_eq] using hmk_p
      have hrsz : s.mem (domPtr + (p + p) + 1) = #ys[p] := by simpa only [h2p_eq] using hsz_p
      have hstep : ∃ z, ExecWithin w flipStep s z 10 ∧
          z.regs rOne = 1 ∧ z.regs rTrieKey = setMask C ∧ z.regs rCoordsLen = #C ∧
          z.regs rDomPtr = domPtr ∧ z.regs rDomLen = ys.length ∧ z.regs rGenPos = p + 1 ∧
          z.mem = Function.update
            (Function.update s.mem (domPtr + 2 * p) (setMask (C \ ys[p])))
            (domPtr + 2 * p + 1) #(C \ ys[p]) := by
        unfold flipStep
        wram_exec [hso, hsk, hscl, hsdp, hp_eq, hrmk, hrsz]
        refine ⟨hso, hsk, hscl, hsdp, hsdl, ?_, ?_⟩
        · wram_simp [hp_eq]
        · wram_simp [h2p_eq, hrmk, hrsz, setMask_sdiff hsub_p, Finset.card_sdiff_of_subset hsub_p]
      obtain ⟨z, hz_ex, hzo, hzk, hzcl, hzdp, hzdl, hzpos, hzmem⟩ := hstep
      refine ⟨z, hz_ex, ⟨hzo, hzk, hzcl, hzdp, hzdl, ?_, ?_, ?_⟩, hzpos⟩
      · intro j hj hlt_j
        by_cases hjp : j = p
        · subst hjp
          simp only [hzmem]
          exact ⟨by rw [Function.update_of_ne (by omega), Function.update_self],
            Function.update_self _ _ _⟩
        · simp only [hzmem]
          refine ⟨?_, ?_⟩
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact (hdone j hj (by omega)).1
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact (hdone j hj (by omega)).2
      · intro j hj hle
        simp only [hzmem]
        refine ⟨?_, ?_⟩
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact (htodo j hj (by omega)).1
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact (htodo j hj (by omega)).2
      · intro a ha
        rw [hzmem, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hsframe a ha
    let x₀ := x.set rGenPos 0
    have hinit : ExecWithin (B := .standard) w (ram[ rGenPos ← #0 ]) x x₀ 1 := by wram_exec
    have hx₀ : P (x₀.regs rGenPos) x₀ := by
      refine ⟨by simp [x₀, ho], by simp [x₀, hk], by simp [x₀, hcl], by simp [x₀, hdptr],
        by simp [x₀, hdlen], by simp [x₀], fun j hj _ => hdom j hj, fun _ _ => rfl⟩
    obtain ⟨y, hloop, hyP, _⟩ := ExecWithin.loop_count P (fun s hs => hs.2.2.2.2.1) hbody
      (by simp [x₀]) hx₀
    obtain ⟨_, _, _, _, _, hydone, _, hyframe⟩ := hyP
    refine ⟨y, (hinit.seq hloop).mono (by simp [x₀]; omega), ?_, hyframe⟩
    intro j hj
    rw [List.length_map] at hj
    simpa only [List.getElem_map] using hydone j hj hj
  obtain ⟨y, he, hydom, hyframe⟩ := hrun
  exact ⟨y, he, hydom, hyframe, fun i hi => he.regs_eq (flipHighDom_preserves i hi)⟩

/-! ### Domain tabulation, pointwise product, and trimmed Yates passes -/

private abbrev IsCellMod (i : Fin numRegs) : Prop :=
  i.val < 9 ∨ (16 ≤ i.val ∧ i.val ≤ 22) ∨ i = rGenTmp

private abbrev IsTabMod (i : Fin numRegs) : Prop :=
  IsCellMod i ∨ i = rFree ∨ i = rCellIdx ∨ i = rCellSaved ∨ i = rCellKey ∨ i = rCellCard

private def tabulateDomStep (cellBody : Code .standard numRegs) : Code .standard numRegs :=
  .seq (ram[
    rGenTmp ← rCellIdx + rCellIdx;
    rGenTmp ← rCurDomPtr + rGenTmp;
    rCellKey ← *rGenTmp;
    rGenTmp ← rGenTmp + rOne;
    rCellCard ← *rGenTmp ])
  (.seq cellBody
    (.seq (ram[ rTrieRoot ← rCellSaved; rTrieKey ← rCellKey ])
      (.seq trieSet
        (ram[ rCellIdx ← rCellIdx + rOne ]))))

private def tabulateDom (cellBody : Code .standard numRegs) : Code .standard numRegs :=
  .seq trieInit
    (.seq (ram[ rCellSaved ← rTrieRoot; rCellIdx ← #0 ])
      (.loop (.lt rCellIdx rCurDomLen) (tabulateDomStep cellBody)))

private theorem exec_tabulateDom {w d domPtr free T_cell : ℕ}
    {cellBody : Code .standard numRegs} {dom : List (Finset (Fin d))}
    {cellFn : Finset (Fin d) → ℕ} {Inv : Data numRegs → Prop} (x : Data numRegs)
    (hz : x.regs rZero = 0) (ho : x.regs rOne = 1) (hd : x.regs rDim = d)
    (hdp : x.regs rCurDomPtr = domPtr) (hdl : x.regs rCurDomLen = dom.length)
    (hfree : x.regs rFree = free) (hfree_pos : 1 ≤ free)
    (hnd : dom.Nodup) (hdom : HoldsDom x.mem domPtr dom)
    (hdom_below : domPtr + 2 * dom.length ≤ free)
    (hInv_init : Inv x)
    (hInv_congr : ∀ s₁ s₂, (∀ a < free, s₁.mem a = s₂.mem a) →
      (∀ i, ¬ IsTabMod i → s₁.regs i = s₂.regs i) → Inv s₁ → Inv s₂)
    (hcell : ∀ s (p : ℕ) (hp : p < dom.length),
      s.regs rZero = 0 → s.regs rOne = 1 → s.regs rDim = d → Inv s →
      (∀ a < free, s.mem a = x.mem a) →
      s.regs rCellKey = setMask dom[p] → s.regs rCellCard = #dom[p] →
      ∃ u, ExecWithin w cellBody s u T_cell ∧ u.regs rTrieVal = cellFn dom[p] ∧
        u.mem = s.mem ∧ ∀ i, ¬ IsCellMod i → u.regs i = s.regs i)
    (hfit_free : Fits w (free + 2 + 2 * d * dom.length))
    (hfit_mask : Fits w (2 ^ d)) :
    ∃ y free' S' outFn,
      ExecWithin w (tabulateDom cellBody) x y (dom.length * (14 * d + T_cell + 16) + 9) ∧
      y.regs rCellSaved = free ∧ y.regs rFree = free' ∧
      free + 2 ≤ free' ∧ free' ≤ free + 2 + 2 * d * dom.length ∧
      S' ⊆ Set.Ico free free' ∧ TrieRep y.mem d free S' outFn ∧
      (∀ X ∈ dom, outFn (setMask X) = cellFn X) ∧
      (∀ a, a < free ∨ free' ≤ a → y.mem a = x.mem a) := by
  have hfit_d : Fits w d := hfit_mask.of_le Nat.lt_two_pow_self.le
  obtain ⟨s₀, hinit0, hs₀_root, hs₀_free, hs₀_rep, hs₀_frame, hs₀_regs⟩ :=
    exec_trieInit (d := d) x hz ho hfree (by omega) (hfit_free.of_le (by omega))
  let s₁ := (s₀.set rCellSaved free).set rCellIdx 0
  have hinit1 : ExecWithin (B := .standard) w (ram[ rCellSaved ← rTrieRoot; rCellIdx ← #0 ])
      s₀ s₁ 2 := by wram_exec [hs₀_root]
  have hs₁_regs_tab : ∀ i, ¬ IsTabMod i → s₁.regs i = x.regs i := by
    intro i hi
    have hne_idx : i ≠ rCellIdx := fun h => hi (Or.inr (Or.inr (Or.inl h)))
    have hne_sav : i ≠ rCellSaved := fun h => hi (Or.inr (Or.inr (Or.inr (Or.inl h))))
    have hne_root : i ≠ rTrieRoot := fun h =>
      hi (Or.inl (Or.inr (Or.inl (by subst h; decide))))
    have hne_free : i ≠ rFree := fun h => hi (Or.inr (Or.inl h))
    simp only [s₁, Data.set_regs_of_ne hne_idx, Data.set_regs_of_ne hne_sav]
    exact hs₀_regs i ⟨hne_root, hne_free⟩
  let P (p : ℕ) (s : Data numRegs) : Prop :=
    s.regs rZero = 0 ∧ s.regs rOne = 1 ∧ s.regs rDim = d ∧
    s.regs rCurDomPtr = domPtr ∧ s.regs rCurDomLen = dom.length ∧
    s.regs rCellSaved = free ∧ Inv s ∧
    ∃ curFree S fn, s.regs rFree = curFree ∧
      free + 2 ≤ curFree ∧ curFree ≤ free + 2 + 2 * d * p ∧
      S ⊆ Set.Ico free curFree ∧ TrieRep s.mem d free S fn ∧
      (∀ q (hq : q < dom.length), q < p → fn (setMask dom[q]) = cellFn dom[q]) ∧
      (∀ a, a < free ∨ curFree ≤ a → s.mem a = x.mem a)
  have hbody (s : Data numRegs) (hs : P (s.regs rCellIdx) s) (hp : s.regs rCellIdx < dom.length) :
      ∃ z, ExecWithin w (tabulateDomStep cellBody) s z (14 * d + T_cell + 14) ∧
        P (s.regs rCellIdx + 1) z ∧ z.regs rCellIdx = s.regs rCellIdx + 1 := by
    generalize hp_eq : s.regs rCellIdx = p at hs hp ⊢
    dsimp only [P] at hs
    obtain ⟨hsz, hso, hsd, hsdp, hsdl, hssav, hsInv,
      curFree, S, fn, hsfree, hcf_lo, hcf_hi, hS_sub, hsrep, hdone, hsframe⟩ := hs
    obtain ⟨hmk_p, hsz_p⟩ := hdom p hp
    have hrmk : s.mem (domPtr + (p + p)) = setMask dom[p] := by
      have : domPtr + (p + p) = domPtr + 2 * p := by omega
      rw [this, hsframe _ (Or.inl (by omega))]; exact hmk_p
    have hrsz : s.mem (domPtr + (p + p) + 1) = #dom[p] := by
      have : domPtr + (p + p) + 1 = domPtr + 2 * p + 1 := by omega
      rw [this, hsframe _ (Or.inl (by omega))]; exact hsz_p
    have hf_2p : Fits w (p + p) := hfit_free.of_le (by omega)
    have hf_dp2p : Fits w (domPtr + (p + p)) := hfit_free.of_le (by omega)
    have hf_dp2p1 : Fits w (domPtr + (p + p) + 1) := hfit_free.of_le (by omega)
    have hload : ∃ u₀, ExecWithin (B := .standard) w (ram[
        rGenTmp ← rCellIdx + rCellIdx;
        rGenTmp ← rCurDomPtr + rGenTmp;
        rCellKey ← *rGenTmp;
        rGenTmp ← rGenTmp + rOne;
        rCellCard ← *rGenTmp ]) s u₀ 5 ∧
        u₀.regs rCellKey = setMask dom[p] ∧ u₀.regs rCellCard = #dom[p] ∧ u₀.mem = s.mem ∧
        ∀ i : Fin numRegs, i ≠ rGenTmp ∧ i ≠ rCellKey ∧ i ≠ rCellCard → u₀.regs i = s.regs i := by
      have hc_code : ∃ u₀, ExecWithin (B := .standard) w (ram[
          rGenTmp ← rCellIdx + rCellIdx;
          rGenTmp ← rCurDomPtr + rGenTmp;
          rCellKey ← *rGenTmp;
          rGenTmp ← rGenTmp + rOne;
          rCellCard ← *rGenTmp ]) s u₀ 5 ∧
          u₀.regs rCellKey = setMask dom[p] ∧ u₀.regs rCellCard = #dom[p] ∧ u₀.mem = s.mem := by
        wram_exec [hso, hsdp, hp_eq, hrmk, hrsz]
        wram_simp [hrmk, hrsz]
      obtain ⟨u₀, he, hck, hcc, hm⟩ := hc_code
      refine ⟨u₀, he, hck, hcc, hm, fun i hi => he.regs_eq ?_⟩
      revert i hi; decide +kernel
    obtain ⟨u₀, he_load, hu₀_ck, hu₀_cc, hu₀_mem, hu₀_regs⟩ := hload
    have not_load_mod (i : Fin numRegs) (h : ¬ IsTabMod i) :
        i ≠ rGenTmp ∧ i ≠ rCellKey ∧ i ≠ rCellCard :=
      ⟨fun h1 => h (Or.inl (Or.inr (Or.inr h1))),
       fun h1 => h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))),
       fun h1 => h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h1)))))⟩
    have hu₀_Inv : Inv u₀ := hInv_congr s u₀ (fun a _ => (congrFun hu₀_mem a).symm)
      (fun i hi => (hu₀_regs i (not_load_mod i hi)).symm) hsInv
    obtain ⟨u₁, he_cell, hu₁_val, hu₁_mem, hu₁_regs⟩ := hcell u₀ p hp
      ((hu₀_regs rZero (by decide)).trans hsz)
      ((hu₀_regs rOne (by decide)).trans hso)
      ((hu₀_regs rDim (by decide)).trans hsd)
      hu₀_Inv (fun a ha => (congrFun hu₀_mem a).trans (hsframe a (Or.inl ha)))
      hu₀_ck hu₀_cc
    have keep_u₁ (i : Fin numRegs) (hc : ¬ IsCellMod i)
        (hl : i ≠ rGenTmp ∧ i ≠ rCellKey ∧ i ≠ rCellCard) : u₁.regs i = s.regs i :=
      (hu₁_regs i hc).trans (hu₀_regs i hl)
    have hu₁_sav : u₁.regs rCellSaved = free :=
      (keep_u₁ rCellSaved (by decide) (by decide)).trans hssav
    have hu₁_ck : u₁.regs rCellKey = setMask dom[p] :=
      (hu₁_regs rCellKey (by decide)).trans hu₀_ck
    let u₂ := (u₁.set rTrieRoot free).set rTrieKey (setMask dom[p])
    have he_prep : ExecWithin (B := .standard) w
        (ram[ rTrieRoot ← rCellSaved; rTrieKey ← rCellKey ]) u₁ u₂ 2 := by
      wram_exec [hu₁_sav, hu₁_ck]
    have hu₂_mem : u₂.mem = s.mem := hu₁_mem.trans hu₀_mem
    have hcf_fit : Fits w (curFree + 2 * d) := by
      have : curFree + 2 * d ≤ free + 2 + 2 * d * dom.length := by
        calc curFree + 2 * d ≤ free + 2 + 2 * d * p + 2 * d := Nat.add_le_add_right hcf_hi _
          _ = free + 2 + 2 * d * (p + 1) := by ring
          _ ≤ free + 2 + 2 * d * dom.length :=
              Nat.add_le_add_left (Nat.mul_le_mul_left (2 * d) (by omega)) _
      exact hfit_free.of_le this
    obtain ⟨u₃, S', free', he_set, hu₃_free, hcf_le', hfree'_le, hS'_sub, hu₃_frame,
      hu₃_rep, hu₃_regs⟩ :=
      exec_trieSet (root := free) (key := setMask dom[p]) (val := cellFn dom[p])
        (free := curFree) (lo := free) u₂
        (by simpa [u₂] using (keep_u₁ rZero (by decide) (by decide)).trans hsz)
        (by simpa [u₂] using (keep_u₁ rOne (by decide) (by decide)).trans hso)
        (by simpa [u₂] using (keep_u₁ rDim (by decide) (by decide)).trans hsd)
        (by simp [u₂]) (by simp [u₂])
        (by simpa [u₂] using hu₁_val)
        (by simpa [u₂] using (keep_u₁ rFree (by decide) (by decide)).trans hsfree)
        hfree_pos (by omega) (by omega) hS_sub (by rwa [hu₂_mem])
        (setMask_lt _) hcf_fit hfit_d (hfit_mask.of_le (setMask_lt _).le)
    have hu₃_idx : u₃.regs rCellIdx = p := by
      rw [hu₃_regs rCellIdx ⟨by decide, Or.inr (by decide)⟩]
      simp only [u₂, Data.set_regs_of_ne (by decide : rCellIdx ≠ rTrieKey),
        Data.set_regs_of_ne (by decide : rCellIdx ≠ rTrieRoot)]
      exact (keep_u₁ rCellIdx (by decide) (by decide)).trans hp_eq
    have hu₃_one : u₃.regs rOne = 1 := by
      rw [hu₃_regs rOne ⟨by decide, Or.inl (by decide)⟩]
      simp only [u₂, Data.set_regs_of_ne (by decide : rOne ≠ rTrieKey),
        Data.set_regs_of_ne (by decide : rOne ≠ rTrieRoot)]
      exact (keep_u₁ rOne (by decide) (by decide)).trans hso
    have hf_p1 : Fits w (p + 1) := hfit_free.of_le (by omega)
    let z := u₃.set rCellIdx (p + 1)
    have he_inc : ExecWithin (B := .standard) w (ram[ rCellIdx ← rCellIdx + rOne ]) u₃ z 1 := by
      wram_exec [hu₃_idx, hu₃_one]
    have hstep_tot : ExecWithin w (tabulateDomStep cellBody) s z (14 * d + T_cell + 14) :=
      (he_load.seq (he_cell.seq (he_prep.seq (he_set.seq he_inc)))).mono (by omega)
    have hz_regs_tab : ∀ i, ¬ IsTabMod i → z.regs i = s.regs i := by
      intro i hi
      have hne_idx : i ≠ rCellIdx := fun h => hi (Or.inr (Or.inr (Or.inl h)))
      have hne_free : i ≠ rFree := fun h => hi (Or.inr (Or.inl h))
      have hnot_cell : ¬ IsCellMod i := fun h => hi (Or.inl h)
      have hrange : i.val < 19 ∨ 23 ≤ i.val := by
        by_contra hbad
        exact hnot_cell (Or.inr (Or.inl ⟨by omega, by omega⟩))
      have hne_key : i ≠ rTrieKey := fun h =>
        hnot_cell (Or.inr (Or.inl (by subst h; decide)))
      have hne_root : i ≠ rTrieRoot := fun h =>
        hnot_cell (Or.inr (Or.inl (by subst h; decide)))
      simp only [z, Data.set_regs_of_ne hne_idx]
      rw [hu₃_regs i ⟨hne_free, hrange⟩]
      simp only [u₂, Data.set_regs_of_ne hne_key, Data.set_regs_of_ne hne_root]
      exact keep_u₁ i hnot_cell (not_load_mod i hi)
    have hz_frame_below : ∀ a < free, z.mem a = s.mem a :=
      fun a ha => (hu₃_frame a (Or.inl ha)).trans (congrFun hu₂_mem a)
    have hz_sav : z.regs rCellSaved = free := by
      simp only [z, Data.set_regs_of_ne (by decide : rCellSaved ≠ rCellIdx)]
      rw [hu₃_regs rCellSaved ⟨by decide, Or.inr (by decide)⟩]
      simp only [u₂, Data.set_regs_of_ne (by decide : rCellSaved ≠ rTrieKey),
        Data.set_regs_of_ne (by decide : rCellSaved ≠ rTrieRoot)]
      exact hu₁_sav
    refine ⟨z, hstep_tot, ?_, by simp [z]⟩
    dsimp only [P]
    refine ⟨(hz_regs_tab rZero (by decide)).trans hsz,
      (hz_regs_tab rOne (by decide)).trans hso,
      (hz_regs_tab rDim (by decide)).trans hsd,
      (hz_regs_tab rCurDomPtr (by decide)).trans hsdp,
      (hz_regs_tab rCurDomLen (by decide)).trans hsdl,
      hz_sav,
      hInv_congr s z (fun a ha => (hz_frame_below a ha).symm)
        (fun i hi => (hz_regs_tab i hi).symm) hsInv,
      free', S', _, ?_, by omega, ?_, hS'_sub, hu₃_rep, ?_, ?_⟩
    · simp only [z, Data.set_regs_of_ne (by decide : rFree ≠ rCellIdx)]
      exact hu₃_free
    · calc free' ≤ curFree + 2 * d := hfree'_le
        _ ≤ free + 2 + 2 * d * p + 2 * d := Nat.add_le_add_right hcf_hi _
        _ = free + 2 + 2 * d * (p + 1) := by ring
    · intro q hq hqp1
      rw [Nat.mod_eq_of_lt (setMask_lt dom[q])]
      by_cases hqp : q = p
      · subst hqp; simp
      · have hne_dom : dom[q] ≠ dom[p] := fun h => hqp ((hnd.getElem_inj_iff).mp h)
        have hne_mk : setMask dom[q] ≠ setMask dom[p] := fun h => hne_dom (setMask_injective h)
        simp only [hne_mk, ↓reduceIte]
        exact hdone q hq (by omega)
    · intro a ha
      rcases ha with ha_lo | ha_hi
      · exact (hz_frame_below a ha_lo).trans (hsframe a (Or.inl ha_lo))
      · exact (hu₃_frame a (Or.inr ha_hi)).trans
          ((congrFun hu₂_mem a).trans (hsframe a (Or.inr (by omega))))
  have hs₁P : P (s₁.regs rCellIdx) s₁ := by
    dsimp only [P]
    have hs₁_idx : s₁.regs rCellIdx = 0 := by simp [s₁]
    rw [hs₁_idx]
    refine ⟨(hs₁_regs_tab rZero (by decide)).trans hz,
      (hs₁_regs_tab rOne (by decide)).trans ho,
      (hs₁_regs_tab rDim (by decide)).trans hd,
      (hs₁_regs_tab rCurDomPtr (by decide)).trans hdp,
      (hs₁_regs_tab rCurDomLen (by decide)).trans hdl,
      by simp [s₁],
      hInv_congr x s₁ (fun a ha => (hs₀_frame a ⟨by omega, by omega⟩).symm)
        (fun i hi => (hs₁_regs_tab i hi).symm) hInv_init,
      free + 2, {free, free + 1}, fun _ => 0, ?_, le_rfl, by omega, ?_, hs₀_rep,
      by simp, ?_⟩
    · simp only [s₁, Data.set_regs_of_ne (by decide : rFree ≠ rCellIdx),
        Data.set_regs_of_ne (by decide : rFree ≠ rCellSaved)]
      exact hs₀_free
    · intro a ha
      rcases ha with rfl | ha1
      · exact ⟨le_rfl, by omega⟩
      · have : a = free + 1 := by simpa using ha1
        subst this; exact ⟨by omega, by omega⟩
    · intro a ha
      exact hs₀_frame a ⟨by omega, by omega⟩
  obtain ⟨y, hloop, hyP, _⟩ := ExecWithin.loop_count P (fun s hs => hs.2.2.2.2.1) hbody
    (by simp [s₁]) hs₁P
  obtain ⟨_, _, _, _, _, hysav, _, free', S', outFn, hyfree, hlo', hhi', hS', hyrep,
    hydone, hyframe⟩ := hyP
  have htot : ExecWithin w (tabulateDom cellBody) x y
      (dom.length * (14 * d + T_cell + 16) + 9) := by
    refine (hinit0.seq (hinit1.seq hloop)).mono ?_
    have hs₁_idx : s₁.regs rCellIdx = 0 := by simp [s₁]
    rw [hs₁_idx, Nat.sub_zero]
    have h16 : 14 * d + T_cell + 14 + 2 = 14 * d + T_cell + 16 := by omega
    change 5 + (2 + (dom.length * (14 * d + T_cell + 14 + 2) + 2)) ≤
      dom.length * (14 * d + T_cell + 16) + 9
    rw [h16]; omega
  refine ⟨y, free', S', outFn, htot, hysav, hyfree, hlo', hhi', hS', hyrep, ?_, hyframe⟩
  intro X hX
  obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hX
  exact hydone q hq hq

/-- Cell body for pointwise multiplication of `rStageCurRoot` and `rStageFbRoot` at `rCellKey`. -/
private def mulCellBody : Code .standard numRegs :=
  .seq (ram[ rTrieRoot ← rStageCurRoot; rTrieKey ← rCellKey ])
    (.seq trieGet
      (.seq (ram[ Signed.left ← rTrieVal; rTrieRoot ← rStageFbRoot; rTrieKey ← rCellKey ])
        (.seq trieGet
          (.seq (ram[ Signed.right ← rTrieVal ])
            (.seq (Signed.multiply (r := 47))
              (ram[ rTrieVal ← Signed.result ]))))))

private def tabulateMul : Code .standard numRegs := tabulateDom mulCellBody

private theorem mulCellBody_preserves (i : Fin numRegs) :
    ¬ IsCellMod i → mulCellBody.Preserves i := by
  decide +kernel +revert

private theorem tabulateMul_preserves (i : Fin numRegs) :
    ¬ IsTabMod i → tabulateMul.Preserves i := by
  decide +kernel +revert

private theorem exec_tabulateMul {w d domPtr free rootF rootG B : ℕ}
    {dom : List (Finset (Fin d))} {fnF fnG : ℕ → ℕ} {valF valG : Finset (Fin d) → ℤ}
    (x : Data numRegs)
    (hz : x.regs rZero = 0) (ho : x.regs rOne = 1) (hd : x.regs rDim = d)
    (hdp : x.regs rCurDomPtr = domPtr) (hdl : x.regs rCurDomLen = dom.length)
    (hfree : x.regs rFree = free) (hfree_pos : 1 ≤ free)
    (hrF : x.regs rStageCurRoot = rootF) (hrG : x.regs rStageFbRoot = rootG)
    (hnd : dom.Nodup) (hdom : HoldsDom x.mem domPtr dom)
    (hdom_below : domPtr + 2 * dom.length ≤ free)
    (htrieF : HoldsTrie x.mem free d rootF fnF)
    (htrieG : HoldsTrie x.mem free d rootG fnG)
    (hvalF : ∀ X ∈ dom, fnF (setMask X) = Signed.encode (valF X) ∧ (valF X).natAbs ≤ B)
    (hvalG : ∀ X ∈ dom, fnG (setMask X) = Signed.encode (valG X) ∧ (valG X).natAbs ≤ B)
    (hvalFG : ∀ X ∈ dom, (valF X * valG X).natAbs ≤ B)
    (hfit_val : Fits w (8 * B + 4))
    (hfit_free : Fits w (free + 2 + 2 * d * dom.length))
    (hfit_mask : Fits w (2 ^ d)) :
    ∃ y free' outFn,
      ExecWithin w tabulateMul x y (dom.length * (32 * d + 53) + 9) ∧
      y.regs rCellSaved = free ∧ y.regs rFree = free' ∧
      free + 2 ≤ free' ∧ free' ≤ free + 2 + 2 * d * dom.length ∧
      HoldsTrie y.mem free' d free outFn ∧
      (∀ X ∈ dom, outFn (setMask X) = Signed.encode (valF X * valG X)) ∧
      (∀ a, a < free ∨ free' ≤ a → y.mem a = x.mem a) ∧
      ∀ i : Fin numRegs, ¬ IsTabMod i → y.regs i = x.regs i := by
  have hfit_d : Fits w d := hfit_mask.of_le Nat.lt_two_pow_self.le
  let Inv (s : Data numRegs) : Prop :=
    s.regs rStageCurRoot = rootF ∧ s.regs rStageFbRoot = rootG
  have hInv_congr : ∀ s₁ s₂, (∀ a < free, s₁.mem a = s₂.mem a) →
      (∀ i, ¬ IsTabMod i → s₁.regs i = s₂.regs i) → Inv s₁ → Inv s₂ := by
    intro s₁ s₂ _ hregs ⟨h1, h2⟩
    exact ⟨(hregs rStageCurRoot (by decide)).symm.trans h1,
      (hregs rStageFbRoot (by decide)).symm.trans h2⟩
  have hcell : ∀ s (p : ℕ) (hp : p < dom.length),
      s.regs rZero = 0 → s.regs rOne = 1 → s.regs rDim = d → Inv s →
      (∀ a < free, s.mem a = x.mem a) →
      s.regs rCellKey = setMask dom[p] → s.regs rCellCard = #dom[p] →
      ∃ u, ExecWithin w mulCellBody s u (18 * d + 37) ∧
        u.regs rTrieVal = Signed.encode (valF dom[p] * valG dom[p]) ∧
        u.mem = s.mem ∧ ∀ i, ¬ IsCellMod i → u.regs i = s.regs i := by
    intro s p hp hsz hso hsd ⟨hsrF, hsrG⟩ hsmem hsck _
    have hXp : dom[p] ∈ dom := List.getElem_mem hp
    obtain ⟨hf_enc, hf_le⟩ := hvalF dom[p] hXp
    obtain ⟨hg_enc, hg_le⟩ := hvalG dom[p] hXp
    have hfg_le := hvalFG dom[p] hXp
    have htF_s : HoldsTrie s.mem free d rootF fnF := htrieF.congr_below hsmem
    have htG_s : HoldsTrie s.mem free d rootG fnG := htrieG.congr_below hsmem
    let u₀ := (s.set rTrieRoot rootF).set rTrieKey (setMask dom[p])
    have he₀ : ExecWithin (B := .standard) w
        (ram[ rTrieRoot ← rStageCurRoot; rTrieKey ← rCellKey ]) s u₀ 2 := by
      wram_exec [hsrF, hsck]
    obtain ⟨u₁, he₁, hu₁_val, hu₁_mem, hu₁_regs⟩ := exec_trieGet u₀
      (by simp [u₀, hsz]) (by simp [u₀, hso]) (by simp [u₀, hsd])
      (by simp [u₀]) (by simp [u₀]) htF_s
      (hfit_free.of_le (by omega)) hfit_d (hfit_mask.of_le (setMask_lt dom[p]).le)
    rw [hf_enc] at hu₁_val
    have hu₁_srG : u₁.regs rStageFbRoot = rootG := by
      rw [hu₁_regs rStageFbRoot (Or.inr (by decide))]; simp [u₀, hsrG]
    have hu₁_ck : u₁.regs rCellKey = setMask dom[p] := by
      rw [hu₁_regs rCellKey (Or.inr (by decide))]; simp [u₀, hsck]
    let u₂ := ((u₁.set (Signed.left (r := 47)) (Signed.encode (valF dom[p]))).set
      rTrieRoot rootG).set rTrieKey (setMask dom[p])
    have he₂ : ExecWithin (B := .standard) w
        (ram[ Signed.left ← rTrieVal; rTrieRoot ← rStageFbRoot; rTrieKey ← rCellKey ])
        u₁ u₂ 3 := by
      wram_exec [hu₁_val, hu₁_srG, hu₁_ck]
    have htG_u₂ : HoldsTrie u₂.mem free d rootG fnG := by
      change HoldsTrie u₁.mem free d rootG fnG; rwa [hu₁_mem]
    obtain ⟨u₃, he₃, hu₃_val, hu₃_mem, hu₃_regs⟩ := exec_trieGet u₂
      (by simpa [u₂, u₀, hsz] using hu₁_regs rZero (Or.inl (by decide)))
      (by simpa [u₂, u₀, hso] using hu₁_regs rOne (Or.inl (by decide)))
      (by simpa [u₂, u₀, hsd] using hu₁_regs rDim (Or.inl (by decide)))
      (by simp [u₂]) (by simp [u₂]) htG_u₂
      (hfit_free.of_le (by omega)) hfit_d (hfit_mask.of_le (setMask_lt dom[p]).le)
    rw [hg_enc] at hu₃_val
    have hu₃_left : u₃.regs (Signed.left (r := 47)) = Signed.encode (valF dom[p]) := by
      rw [hu₃_regs _ (Or.inl (by decide))]; simp [u₂]
    let u₄ := u₃.set (Signed.right (r := 47)) (Signed.encode (valG dom[p]))
    have he₄ : ExecWithin (B := .standard) w (ram[ Signed.right ← rTrieVal ]) u₃ u₄ 1 := by
      wram_exec [hu₃_val]
    obtain ⟨u₅, he₅, hu₅_res, hu₅_mem, _⟩ := exec_signedMul hfit_val hf_le hg_le hfg_le u₄
      (by simp only [u₄, Data.set_regs_of_ne (by decide :
            Signed.left (r := 47) ≠ Signed.right (r := 47))]; exact hu₃_left)
      (by simp [u₄])
    let u := u₅.set rTrieVal (Signed.encode (valF dom[p] * valG dom[p]))
    have he₆ : ExecWithin (B := .standard) w (ram[ rTrieVal ← Signed.result ]) u₅ u 1 := by
      wram_exec [hu₅_res]
    have htot : ExecWithin w mulCellBody s u (18 * d + 37) :=
      (he₀.seq (he₁.seq (he₂.seq (he₃.seq (he₄.seq (he₅.seq he₆)))))).mono (by omega)
    refine ⟨u, htot, by simp [u], hu₅_mem.trans (hu₃_mem.trans hu₁_mem),
      fun i hi => htot.regs_eq (mulCellBody_preserves i hi)⟩
  obtain ⟨y, free', S', outFn, he, hysav, hyfree, hlo', hhi', hS', hyrep, hydom, hyframe⟩ :=
    exec_tabulateDom (cellBody := mulCellBody)
      (cellFn := fun X => Signed.encode (valF X * valG X))
      (T_cell := 18 * d + 37) x hz ho hd hdp hdl hfree hfree_pos
      hnd hdom hdom_below ⟨hrF, hrG⟩ hInv_congr hcell hfit_free hfit_mask
  have he' : ExecWithin w tabulateMul x y (dom.length * (32 * d + 53) + 9) :=
    he.mono (by
      have : 14 * d + (18 * d + 37) + 16 = 32 * d + 53 := by omega
      rw [this])
  exact ⟨y, free', outFn, he', hysav, hyfree, hlo', hhi',
    ⟨S', fun a ha => ⟨hfree_pos.trans (hS' ha).1, (hS' ha).2⟩, hyrep⟩, hydom, hyframe,
    fun i hi => he'.regs_eq (tabulateMul_preserves i hi)⟩

private theorem natAbs_yatesTransform_le {d : ℕ} {c : ℤ} (hc : c.natAbs ≤ 1)
    {l : List (Fin d)} (hl : l.Nodup) {G : Finset (Fin d) → ℤ} {B₀ : ℕ}
    (hG : ∀ T, (G T).natAbs ≤ B₀) (S : Finset (Fin d)) :
    (yatesTransform c l G S).natAbs ≤ 2 ^ d * B₀ := by
  rw [yatesTransform_apply c hl G S]
  calc (∑ U ∈ (S ∩ l.toFinset).powerset, c ^ #U • G (S \ U)).natAbs
      ≤ ∑ U ∈ (S ∩ l.toFinset).powerset, (c ^ #U * G (S \ U)).natAbs := by
        simpa only [smul_eq_mul] using Int.natAbs_sum_le _ _
    _ ≤ ∑ _U ∈ (S ∩ l.toFinset).powerset, B₀ := by
        refine Finset.sum_le_sum fun U _ => ?_
        rw [Int.natAbs_mul, Int.natAbs_pow]
        calc c.natAbs ^ #U * (G (S \ U)).natAbs
            ≤ 1 ^ #U * B₀ := Nat.mul_le_mul (Nat.pow_le_pow_left hc _) (hG _)
          _ = B₀ := by simp
    _ = 2 ^ #(S ∩ l.toFinset) * B₀ := by simp
    _ ≤ 2 ^ d * B₀ := by
        refine Nat.mul_le_mul_right B₀ (Nat.pow_le_pow_right Nat.two_pos ?_)
        simpa using Finset.card_le_univ (S ∩ l.toFinset)

private theorem yatesTransform_natOne_eq_intOne {d : ℕ} (l : List (Fin d))
    (G : Finset (Fin d) → ℤ) :
    yatesTransform (1 : ℕ) l G = yatesTransform (1 : ℤ) l G := by
  induction l generalizing G with
  | nil => rfl
  | cons i l ih =>
    have hpass : yatesPass (1 : ℕ) i G = yatesPass (1 : ℤ) i G := by
      funext S; simp [yatesPass]
    rw [yatesTransform_cons, yatesTransform_cons, hpass, ih]

/-- Cell body for one trimmed Yates pass in coordinate `rGenBitMask = 1 <<< k`, with cutoff
`rStageCutoff`, current stage `rStageCurRoot`, fallback stage `rStageFbRoot`, and sign mode
`rSignMode` (`0` for `+1`, `1` for `-1`). -/
private def passCellBody : Code .standard numRegs :=
  .seq (ram[ rTrieRoot ← rStageCurRoot; rTrieKey ← rCellKey ])
    (.seq trieGet
      (.seq (ram[ rGenTmp ← rCellKey &&& rGenBitMask ])
        (.branch (.eq rGenTmp rZero)
          (ram[ rTrieVal ← rTrieVal ])
          (.seq (ram[
              Signed.left ← rTrieVal;
              rTrieKey ← rCellKey ^^^ rGenBitMask;
              if rStageCutoff < rCellCard then [
                rTrieRoot ← rStageCurRoot
              ] else [
                rTrieRoot ← rStageFbRoot
              ] ])
            (.seq trieGet
              (.seq (ram[ Signed.right ← rTrieVal ])
                (.seq (.branch (.eq rSignMode rZero)
                    (Signed.add (r := 47))
                    (Signed.subtract (r := 47)))
                  (ram[ rTrieVal ← Signed.result ]))))))))

private def passCode : Code .standard numRegs := tabulateDom passCellBody

private theorem passCellBody_preserves (i : Fin numRegs) :
    ¬ IsCellMod i → passCellBody.Preserves i := by
  decide +kernel +revert

private theorem passCode_preserves (i : Fin numRegs) :
    ¬ IsTabMod i → passCode.Preserves i := by
  decide +kernel +revert

private theorem exec_passCode {w d domPtr free curRoot fbRoot cutoff signMode B : ℕ}
    {coord : Fin d} {dom : List (Finset (Fin d))} {P_low : Finset (Fin d) → Prop}
    {curFn fbFn : ℕ → ℕ} {G_k : Finset (Fin d) → ℤ} (x : Data numRegs)
    (hz : x.regs rZero = 0) (ho : x.regs rOne = 1) (hd : x.regs rDim = d)
    (hdp : x.regs rCurDomPtr = domPtr) (hdl : x.regs rCurDomLen = dom.length)
    (hfree : x.regs rFree = free) (hfree_pos : 1 ≤ free)
    (hbm : x.regs rGenBitMask = (1 <<< coord.val))
    (hcut : x.regs rStageCutoff = cutoff) (hsm : x.regs rSignMode = signMode)
    (hcr : x.regs rStageCurRoot = curRoot) (hfbr : x.regs rStageFbRoot = fbRoot)
    (hnd : dom.Nodup) (hdom : HoldsDom x.mem domPtr dom)
    (hdom_below : domPtr + 2 * dom.length ≤ free)
    (hdom_closed : ∀ X ∈ dom, coord ∈ X →
      (cutoff ≤ #(X.erase coord) → X.erase coord ∈ dom) ∧
      (#(X.erase coord) < cutoff → P_low (X.erase coord)))
    (htrie_cur : HoldsTrie x.mem free d curRoot curFn)
    (htrie_fb : HoldsTrie x.mem free d fbRoot fbFn)
    (hcur_eq : ∀ X ∈ dom, curFn (setMask X) = Signed.encode (G_k X))
    (hfb_eq : ∀ Y, #Y < cutoff → P_low Y → fbFn (setMask Y) = Signed.encode (G_k Y))
    (hG_le : ∀ Y, (G_k Y).natAbs ≤ B)
    (hfit_val : Fits w (8 * B + 4))
    (hfit_free : Fits w (free + 2 + 2 * d * dom.length))
    (hfit_mask : Fits w (2 ^ d)) :
    let c : ℤ := if signMode = 0 then 1 else -1
    ∃ y free' S' outFn,
      ExecWithin w passCode x y (dom.length * (32 * d + 63) + 9) ∧
      y.regs rCellSaved = free ∧ y.regs rFree = free' ∧
      free + 2 ≤ free' ∧ free' ≤ free + 2 + 2 * d * dom.length ∧
      S' ⊆ Set.Ico free free' ∧ TrieRep y.mem d free S' outFn ∧
      (∀ X ∈ dom, outFn (setMask X) = Signed.encode (yatesPass c coord G_k X)) ∧
      (∀ a, a < free ∨ free' ≤ a → y.mem a = x.mem a) ∧
      ∀ i : Fin numRegs, ¬ IsTabMod i → y.regs i = x.regs i := by
  intro c
  have hfit_d : Fits w d := hfit_mask.of_le Nat.lt_two_pow_self.le
  let Inv (s : Data numRegs) : Prop :=
    s.regs rGenBitMask = (1 <<< coord.val) ∧ s.regs rStageCutoff = cutoff ∧
    s.regs rSignMode = signMode ∧ s.regs rStageCurRoot = curRoot ∧
    s.regs rStageFbRoot = fbRoot
  have hInv_congr : ∀ s₁ s₂, (∀ a < free, s₁.mem a = s₂.mem a) →
      (∀ i, ¬ IsTabMod i → s₁.regs i = s₂.regs i) → Inv s₁ → Inv s₂ := by
    intro s₁ s₂ _ hregs ⟨h1, h2, h3, h4, h5⟩
    exact ⟨(hregs rGenBitMask (by decide)).symm.trans h1,
      (hregs rStageCutoff (by decide)).symm.trans h2,
      (hregs rSignMode (by decide)).symm.trans h3,
      (hregs rStageCurRoot (by decide)).symm.trans h4,
      (hregs rStageFbRoot (by decide)).symm.trans h5⟩
  have hcell : ∀ s (p : ℕ) (hp : p < dom.length),
      s.regs rZero = 0 → s.regs rOne = 1 → s.regs rDim = d → Inv s →
      (∀ a < free, s.mem a = x.mem a) →
      s.regs rCellKey = setMask dom[p] → s.regs rCellCard = #dom[p] →
      ∃ u, ExecWithin w passCellBody s u (18 * d + 47) ∧
        u.regs rTrieVal = Signed.encode (yatesPass c coord G_k dom[p]) ∧
        u.mem = s.mem ∧ ∀ i, ¬ IsCellMod i → u.regs i = s.regs i := by
    intro s p hp hsz hso hsd ⟨hsbm, hscut, hssm, hscr, hsfbr⟩ hsmem hsck hscc
    let X := dom[p]
    change s.regs rCellKey = setMask X at hsck
    change s.regs rCellCard = #X at hscc
    have hX_mem : X ∈ dom := List.getElem_mem hp
    have ht_cur_s : HoldsTrie s.mem free d curRoot curFn := htrie_cur.congr_below hsmem
    have ht_fb_s : HoldsTrie s.mem free d fbRoot fbFn := htrie_fb.congr_below hsmem
    let u₀ := (s.set rTrieRoot curRoot).set rTrieKey (setMask X)
    have he₀ : ExecWithin (B := .standard) w
        (ram[ rTrieRoot ← rStageCurRoot; rTrieKey ← rCellKey ]) s u₀ 2 := by
      wram_exec [hscr, hsck]
    obtain ⟨u₁, he₁, hu₁_val, hu₁_mem, hu₁_regs⟩ :=
      exec_trieGet (root := curRoot) (key := setMask X) u₀
        (by simp [u₀, hsz]) (by simp [u₀, hso]) (by simp [u₀, hsd])
        (by simp [u₀]) (by simp [u₀]) ht_cur_s
        (hfit_free.of_le (by omega)) hfit_d (hfit_mask.of_le (setMask_lt _).le)
    rw [hcur_eq X hX_mem] at hu₁_val
    have hand_eq : setMask X &&& (1 <<< coord.val) =
        (if coord ∈ X then 2 ^ coord.val else 0) := by
      apply Nat.eq_of_testBit_eq
      intro j
      rw [Nat.testBit_and, Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]
      by_cases hj : j = coord.val
      · subst hj
        rw [testBit_setMask]
        by_cases hcX : coord ∈ X <;> simp [hcX]
      · have hne : coord.val ≠ j := Ne.symm hj
        by_cases hcX : coord ∈ X <;> simp [hcX, hne]
    have hf_and : Fits w (setMask X &&& (1 <<< coord.val)) :=
      hfit_mask.of_le (Nat.and_le_left.trans (setMask_lt X).le)
    have hu₁_ck : u₁.regs rCellKey = setMask X := by
      rw [hu₁_regs rCellKey (Or.inr (by decide))]; simp [u₀, hsck]
    have hu₁_bm : u₁.regs rGenBitMask = (1 <<< coord.val) := by
      rw [hu₁_regs rGenBitMask (Or.inr (by decide))]; simp [u₀, hsbm]
    let u₂ := u₁.set rGenTmp (setMask X &&& (1 <<< coord.val))
    have he₂ : ExecWithin (B := .standard) w
        (ram[ rGenTmp ← rCellKey &&& rGenBitMask ]) u₁ u₂ 1 := by
      wram_exec [hu₁_ck, hu₁_bm]
    have hu₂_z : u₂.regs rZero = 0 := by
      simp only [u₂, Data.set_regs_of_ne (by decide : rZero ≠ rGenTmp)]
      rw [hu₁_regs rZero (Or.inl (by decide))]; simp [u₀, hsz]
    by_cases hcX : coord ∈ X
    · have hgt_ne : u₂.regs rGenTmp ≠ u₂.regs rZero := by
        rw [hu₂_z]; simp only [u₂, Data.set_regs_self, hand_eq, hcX, ↓reduceIte]
        exact (Nat.two_pow_pos coord.val).ne'
      have hcard_er : #(X.erase coord) + 1 = #X := Finset.card_erase_add_one hcX
      have hf_xor : Fits w (setMask X ^^^ (1 <<< coord.val)) := by
        rw [← setMask_erase hcX]; exact hfit_mask.of_le (setMask_lt _).le
      have hu₂_val : u₂.regs rTrieVal = Signed.encode (G_k X) := by
        simp only [u₂, Data.set_regs_of_ne (by decide : rTrieVal ≠ rGenTmp)]; exact hu₁_val
      have hu₂_ck : u₂.regs rCellKey = setMask X := by
        simp only [u₂, Data.set_regs_of_ne (by decide : rCellKey ≠ rGenTmp)]; exact hu₁_ck
      have hu₂_bm : u₂.regs rGenBitMask = (1 <<< coord.val) := by
        simp only [u₂, Data.set_regs_of_ne (by decide : rGenBitMask ≠ rGenTmp)]; exact hu₁_bm
      have hu₂_cut : u₂.regs rStageCutoff = cutoff := by
        simp only [u₂, Data.set_regs_of_ne (by decide : rStageCutoff ≠ rGenTmp)]
        rw [hu₁_regs rStageCutoff (Or.inr (by decide))]; simp [u₀, hscut]
      have hu₂_cc : u₂.regs rCellCard = #X := by
        simp only [u₂, Data.set_regs_of_ne (by decide : rCellCard ≠ rGenTmp)]
        rw [hu₁_regs rCellCard (Or.inr (by decide))]; simp [u₀, hscc]
      have hu₂_cr : u₂.regs rStageCurRoot = curRoot := by
        simp only [u₂, Data.set_regs_of_ne (by decide : rStageCurRoot ≠ rGenTmp)]
        rw [hu₁_regs rStageCurRoot (Or.inr (by decide))]; simp [u₀, hscr]
      have hu₂_fbr : u₂.regs rStageFbRoot = fbRoot := by
        simp only [u₂, Data.set_regs_of_ne (by decide : rStageFbRoot ≠ rGenTmp)]
        rw [hu₁_regs rStageFbRoot (Or.inr (by decide))]; simp [u₀, hsfbr]
      have hsel : ∃ u₃ selRoot selFn,
          ExecWithin (B := .standard) w (ram[
            Signed.left ← rTrieVal;
            rTrieKey ← rCellKey ^^^ rGenBitMask;
            if rStageCutoff < rCellCard then [
              rTrieRoot ← rStageCurRoot
            ] else [
              rTrieRoot ← rStageFbRoot
            ] ]) u₂ u₃ 5 ∧
          u₃.regs (Signed.left (r := 47)) = Signed.encode (G_k X) ∧
          u₃.regs rTrieKey = setMask (X.erase coord) ∧
          u₃.regs rTrieRoot = selRoot ∧
          u₃.regs rZero = 0 ∧ u₃.regs rOne = 1 ∧ u₃.regs rDim = d ∧
          u₃.regs rSignMode = signMode ∧ u₃.mem = u₂.mem ∧
          HoldsTrie u₃.mem free d selRoot selFn ∧
          selFn (setMask (X.erase coord)) = Signed.encode (G_k (X.erase coord)) := by
        have hu₂_o : u₂.regs rOne = 1 := by
          simp only [u₂, Data.set_regs_of_ne (by decide : rOne ≠ rGenTmp)]
          rw [hu₁_regs rOne (Or.inl (by decide))]; simp [u₀, hso]
        have hu₂_d : u₂.regs rDim = d := by
          simp only [u₂, Data.set_regs_of_ne (by decide : rDim ≠ rGenTmp)]
          rw [hu₁_regs rDim (Or.inl (by decide))]; simp [u₀, hsd]
        have hu₂_sm : u₂.regs rSignMode = signMode := by
          simp only [u₂, Data.set_regs_of_ne (by decide : rSignMode ≠ rGenTmp)]
          rw [hu₁_regs rSignMode (Or.inr (by decide))]; simp [u₀, hssm]
        by_cases hlt_cut : cutoff < #X
        · have hst : ∃ u₃, ExecWithin (B := .standard) w (ram[
              Signed.left ← rTrieVal;
              rTrieKey ← rCellKey ^^^ rGenBitMask;
              if rStageCutoff < rCellCard then [
                rTrieRoot ← rStageCurRoot
              ] else [
                rTrieRoot ← rStageFbRoot
              ] ]) u₂ u₃ 5 ∧
              u₃.regs (Signed.left (r := 47)) = Signed.encode (G_k X) ∧
              u₃.regs rTrieKey = setMask (X.erase coord) ∧
              u₃.regs rTrieRoot = curRoot ∧
              u₃.regs rZero = 0 ∧ u₃.regs rOne = 1 ∧ u₃.regs rDim = d ∧
              u₃.regs rSignMode = signMode ∧ u₃.mem = u₂.mem := by
            wram_exec [hu₂_val, hu₂_ck, hu₂_bm, hu₂_cut, hu₂_cc, hu₂_cr, hlt_cut]
            wram_simp [setMask_erase hcX, hu₂_z, hu₂_o, hu₂_d, hu₂_sm]
          obtain ⟨u₃, he₃, hl₃, hk₃, hr₃, hz₃, ho₃, hd₃, hsm₃, hm₃⟩ := hst
          refine ⟨u₃, curRoot, curFn, he₃, hl₃, hk₃, hr₃, hz₃, ho₃, hd₃, hsm₃, hm₃, ?_,
            hcur_eq _ ((hdom_closed X hX_mem hcX).1 (by omega))⟩
          rw [hm₃]; change HoldsTrie u₁.mem free d curRoot curFn; rwa [hu₁_mem]
        · have hst : ∃ u₃, ExecWithin (B := .standard) w (ram[
              Signed.left ← rTrieVal;
              rTrieKey ← rCellKey ^^^ rGenBitMask;
              if rStageCutoff < rCellCard then [
                rTrieRoot ← rStageCurRoot
              ] else [
                rTrieRoot ← rStageFbRoot
              ] ]) u₂ u₃ 5 ∧
              u₃.regs (Signed.left (r := 47)) = Signed.encode (G_k X) ∧
              u₃.regs rTrieKey = setMask (X.erase coord) ∧
              u₃.regs rTrieRoot = fbRoot ∧
              u₃.regs rZero = 0 ∧ u₃.regs rOne = 1 ∧ u₃.regs rDim = d ∧
              u₃.regs rSignMode = signMode ∧ u₃.mem = u₂.mem := by
            wram_exec [hu₂_val, hu₂_ck, hu₂_bm, hu₂_cut, hu₂_cc, hu₂_fbr, hlt_cut]
            wram_simp [setMask_erase hcX, hu₂_z, hu₂_o, hu₂_d, hu₂_sm]
          obtain ⟨u₃, he₃, hl₃, hk₃, hr₃, hz₃, ho₃, hd₃, hsm₃, hm₃⟩ := hst
          refine ⟨u₃, fbRoot, fbFn, he₃, hl₃, hk₃, hr₃, hz₃, ho₃, hd₃, hsm₃, hm₃, ?_,
            hfb_eq _ (by omega) ((hdom_closed X hX_mem hcX).2 (by omega))⟩
          rw [hm₃]; change HoldsTrie u₁.mem free d fbRoot fbFn; rwa [hu₁_mem]
      obtain ⟨u₃, selRoot, selFn, he₃, hl₃, hk₃, hr₃, hz₃, ho₃, hd₃, hsm₃, hm₃, htsel, hval_er⟩ :=
        hsel
      obtain ⟨u₄, he₄, hu₄_val, hu₄_mem, hu₄_regs⟩ := exec_trieGet u₃ hz₃ ho₃ hd₃ hr₃ hk₃ htsel
        (hfit_free.of_le (by omega)) hfit_d (hfit_mask.of_le (setMask_lt _).le)
      rw [hval_er] at hu₄_val
      have hu₄_left : u₄.regs (Signed.left (r := 47)) = Signed.encode (G_k X) :=
        (hu₄_regs _ (Or.inl (by decide))).trans hl₃
      have hu₄_sm : u₄.regs rSignMode = signMode :=
        (hu₄_regs _ (Or.inr (by decide))).trans hsm₃
      have hu₄_z : u₄.regs rZero = 0 :=
        (hu₄_regs _ (Or.inl (by decide))).trans hz₃
      let u₅ := u₄.set (Signed.right (r := 47)) (Signed.encode (G_k (X.erase coord)))
      have he₅ : ExecWithin (B := .standard) w (ram[ Signed.right ← rTrieVal ]) u₄ u₅ 1 := by
        wram_exec [hu₄_val]
      have harith : ∃ u₆, ExecWithin w
          (.branch (.eq rSignMode rZero) (Signed.add (r := 47)) (Signed.subtract (r := 47)))
          u₅ u₆ 19 ∧
          u₆.regs (Signed.result (r := 47)) = Signed.encode (yatesPass c coord G_k X) ∧
          u₆.mem = u₅.mem := by
        by_cases hsm0 : signMode = 0
        · have hcond : (Cond.eq rSignMode rZero).Holds u₅ := by
            simp [Cond.holds_eq, u₅, hu₄_sm, hu₄_z, hsm0]
          obtain ⟨u₆, he₆, hres₆, hmem₆, _⟩ :=
            exec_signedAdd hfit_val (hG_le X) (hG_le (X.erase coord)) u₅
              (by simp only [u₅, Data.set_regs_of_ne (by decide :
                    Signed.left (r := 47) ≠ Signed.right (r := 47))]; exact hu₄_left)
              (by simp [u₅])
          refine ⟨u₆, (he₆.branch_pos hcond).mono (by omega), ?_, hmem₆⟩
          simpa [yatesPass, hcX, c, hsm0] using hres₆
        · have hcond : ¬ (Cond.eq rSignMode rZero).Holds u₅ := by
            simp [Cond.holds_eq, u₅, hu₄_sm, hu₄_z, hsm0]
          obtain ⟨u₆, he₆, hres₆, hmem₆, _⟩ :=
            exec_signedSub hfit_val (hG_le X) (hG_le (X.erase coord)) u₅
              (by simp only [u₅, Data.set_regs_of_ne (by decide :
                    Signed.left (r := 47) ≠ Signed.right (r := 47))]; exact hu₄_left)
              (by simp [u₅])
          refine ⟨u₆, (he₆.branch_neg hcond).mono (by omega), ?_, hmem₆⟩
          simpa [yatesPass, hcX, c, hsm0, sub_eq_add_neg] using hres₆
      obtain ⟨u₆, he₆, hres₆, hm₆⟩ := harith
      let u := u₆.set rTrieVal (Signed.encode (yatesPass c coord G_k X))
      have he₇ : ExecWithin (B := .standard) w (ram[ rTrieVal ← Signed.result ]) u₆ u 1 := by
        wram_exec [hres₆]
      have helse : ExecWithin w
          (.seq (ram[
              Signed.left ← rTrieVal;
              rTrieKey ← rCellKey ^^^ rGenBitMask;
              if rStageCutoff < rCellCard then [
                rTrieRoot ← rStageCurRoot
              ] else [
                rTrieRoot ← rStageFbRoot
              ] ])
            (.seq trieGet
              (.seq (ram[ Signed.right ← rTrieVal ])
                (.seq (.branch (.eq rSignMode rZero)
                    (Signed.add (r := 47))
                    (Signed.subtract (r := 47)))
                  (ram[ rTrieVal ← Signed.result ])))))
          u₂ u (9 * d + 34) :=
        (he₃.seq (he₄.seq (he₅.seq (he₆.seq he₇)))).mono (by omega)
      have hbr : ExecWithin w
          (.branch (.eq rGenTmp rZero) (ram[ rTrieVal ← rTrieVal ]) _) u₂ u (9 * d + 36) :=
        (helse.branch_neg (by simpa [Cond.holds_eq] using hgt_ne)).mono (by omega)
      have htot : ExecWithin w passCellBody s u (18 * d + 47) :=
        (he₀.seq (he₁.seq (he₂.seq hbr))).mono (by omega)
      refine ⟨u, htot, by simp [u, X], hm₆.trans (hu₄_mem.trans (hm₃.trans hu₁_mem)),
        fun i hi => htot.regs_eq (passCellBody_preserves i hi)⟩
    · have hgt_eq : u₂.regs rGenTmp = u₂.regs rZero := by
        rw [hu₂_z]; simp [u₂, hand_eq, hcX]
      have hu₂_val : u₂.regs rTrieVal = Signed.encode (G_k X) := by
        simp only [u₂, Data.set_regs_of_ne (by decide : rTrieVal ≠ rGenTmp)]; exact hu₁_val
      let u := u₂.set rTrieVal (Signed.encode (G_k X))
      have hnop : ExecWithin (B := .standard) w (ram[ rTrieVal ← rTrieVal ]) u₂ u 1 := by
        wram_exec [hu₂_val]
      have htot : ExecWithin w passCellBody s u (18 * d + 47) :=
        (he₀.seq (he₁.seq (he₂.seq
          (hnop.branch_pos (by simpa [Cond.holds_eq] using hgt_eq))))).mono (by omega)
      refine ⟨u, htot, by simp [u, X, yatesPass, hcX], hu₁_mem,
        fun i hi => htot.regs_eq (passCellBody_preserves i hi)⟩
  obtain ⟨y, free', S', outFn, he, hysav, hyfree, hlo', hhi', hS', hyrep, hydom, hyframe⟩ :=
    exec_tabulateDom (cellBody := passCellBody)
      (cellFn := fun X => Signed.encode (yatesPass c coord G_k X))
      (T_cell := 18 * d + 47) x hz ho hd hdp hdl hfree hfree_pos
      hnd hdom hdom_below ⟨hbm, hcut, hsm, hcr, hfbr⟩ hInv_congr hcell hfit_free hfit_mask
  have he' : ExecWithin w passCode x y (dom.length * (32 * d + 63) + 9) :=
    he.mono (by
      have : 14 * d + (18 * d + 47) + 16 = 32 * d + 63 := by omega
      rw [this])
  exact ⟨y, free', S', outFn, he', hysav, hyfree, hlo', hhi', hS', hyrep, hydom, hyframe,
    fun i hi => he'.regs_eq (passCode_preserves i hi)⟩

/-- Depth-`d` trie in `Ico 1 bound` whose footprint avoids `Ico exclLo exclHi` (used for the
`(d + 1)`-word stage-root array allocated at the start of `stagesCode`). -/
private def HoldsTrieOutside (mem : ℕ → ℕ) (exclLo exclHi bound d root : ℕ) (fn : ℕ → ℕ) : Prop :=
  ∃ S ⊆ Set.Ico 1 bound, Disjoint S (Set.Ico exclLo exclHi) ∧ TrieRep mem d root S fn

private theorem HoldsTrieOutside.toHoldsTrie {mem : ℕ → ℕ} {exclLo exclHi bound d root : ℕ}
    {fn : ℕ → ℕ} (h : HoldsTrieOutside mem exclLo exclHi bound d root fn) :
    HoldsTrie mem bound d root fn :=
  let ⟨S, hS, _, hrep⟩ := h; ⟨S, hS, hrep⟩

private theorem HoldsTrie.toOutside_of_le {mem : ℕ → ℕ} {b exclLo exclHi bound d root : ℕ}
    {fn : ℕ → ℕ} (h : HoldsTrie mem b d root fn) (hb_excl : b ≤ exclLo) (hb_bound : b ≤ bound) :
    HoldsTrieOutside mem exclLo exclHi bound d root fn := by
  obtain ⟨S, hS, hrep⟩ := h
  refine ⟨S, fun a ha => ⟨(hS ha).1, (hS ha).2.trans_le hb_bound⟩, Set.disjoint_left.mpr ?_, hrep⟩
  intro a ha hexcl
  have := (hS ha).2; have := hexcl.1; omega

private abbrev IsStageMod (i : Fin numRegs) : Prop :=
  IsTabMod i ∨ i = rRootsOut ∨ i = rStageIdx ∨ i = rGenBitMask ∨
    i = rStageCurRoot ∨ i = rStageFbRoot

private def stagesStep : Code .standard numRegs :=
  .seq (ram[
    rGenTmp ← rRootsOut + rStageIdx;
    rStageCurRoot ← *rGenTmp;
    if rStageCutoff = rZero then [
      rStageFbRoot ← #0
    ] else [
      rGenTmp ← rFbRoots + rStageIdx;
      rStageFbRoot ← *rGenTmp
    ];
    rGenBitMask ← rOne <<< rStageIdx ])
  (.seq passCode
    (ram[
      rStageIdx ← rStageIdx + rOne;
      rGenTmp ← rRootsOut + rStageIdx;
      *rGenTmp ← rCellSaved ]))

/-- Allocate `(d + 1)` stage-root slots at `rFree` (returned in `rRootsOut`), store `rStageCurRoot`
as stage `0`, and run `d` trimmed passes over `dom`. -/
private def stagesCode : Code .standard numRegs :=
  .seq (ram[
    rRootsOut ← rFree;
    rGenTmp ← rDim + rOne;
    rFree ← rFree + rGenTmp;
    *rRootsOut ← rStageCurRoot;
    rStageIdx ← #0 ])
  (.loop (.lt rStageIdx rDim) stagesStep)

private theorem stagesCode_preserves (i : Fin numRegs) :
    ¬ IsStageMod i → stagesCode.Preserves i := by
  decide +kernel +revert

private theorem exec_stagesCode {w d domPtr free initRoot fbBase cutoff signMode B₀ B : ℕ}
    {dom : List (Finset (Fin d))} {P_low : Finset (Fin d) → Prop}
    {initFn : ℕ → ℕ} {G : Finset (Fin d) → ℤ} (x : Data numRegs)
    (hz : x.regs rZero = 0) (ho : x.regs rOne = 1) (hd : x.regs rDim = d)
    (hdp : x.regs rCurDomPtr = domPtr) (hdl : x.regs rCurDomLen = dom.length)
    (hcut : x.regs rStageCutoff = cutoff) (hsm : x.regs rSignMode = signMode)
    (hfbb : x.regs rFbRoots = fbBase)
    (hir : x.regs rStageCurRoot = initRoot) (hfree : x.regs rFree = free)
    (hfree_pos : 1 ≤ free)
    (hnd : dom.Nodup) (hdom : HoldsDom x.mem domPtr dom)
    (hdom_below : domPtr + 2 * dom.length ≤ free)
    (hdom_closed : ∀ X ∈ dom, ∀ coord : Fin d, coord ∈ X →
      (cutoff ≤ #(X.erase coord) → X.erase coord ∈ dom) ∧
      (#(X.erase coord) < cutoff → P_low (X.erase coord)))
    (htrie_init : HoldsTrie x.mem free d initRoot initFn)
    (hinit_eq : ∀ X ∈ dom, initFn (setMask X) = Signed.encode (G X))
    (hfb_valid : 0 < cutoff → fbBase + d ≤ free ∧
      ∀ k < d, ∃ fbFn, HoldsTrie x.mem free d (x.mem (fbBase + k)) fbFn ∧
        ∀ Y, #Y < cutoff → P_low Y →
          fbFn (setMask Y) = Signed.encode
            (yatesTransform (if signMode = 0 then (1 : ℤ) else -1)
              ((List.finRange d).take k) G Y))
    (hG_le : ∀ Y, (G Y).natAbs ≤ B₀) (hB : 2 ^ d * B₀ ≤ B)
    (hfit_val : Fits w (8 * B + 4))
    (hfit_free : Fits w (free + d + 1 + d * (2 * d * dom.length + 2)))
    (hfit_mask : Fits w (2 ^ d)) :
    let c : ℤ := if signMode = 0 then 1 else -1
    ∃ y endFree,
      ExecWithin w stagesCode x y (d * (dom.length * (32 * d + 63) + 22) + 7) ∧
      y.regs rRootsOut = free ∧ y.regs rFree = endFree ∧
      free + d + 1 ≤ endFree ∧ endFree ≤ free + d + 1 + d * (2 * d * dom.length + 2) ∧
      (∀ k ≤ d, ∃ stFn, HoldsTrie y.mem endFree d (y.mem (free + k)) stFn ∧
        ∀ X ∈ dom, stFn (setMask X) =
          Signed.encode (yatesTransform c ((List.finRange d).take k) G X)) ∧
      (∀ a, a < free ∨ endFree ≤ a → y.mem a = x.mem a) ∧
      ∀ i : Fin numRegs, ¬ IsStageMod i → y.regs i = x.regs i := by
  intro c
  have hc_abs : c.natAbs ≤ 1 := by dsimp [c]; split_ifs <;> decide
  have hfit_d : Fits w d := hfit_mask.of_le Nat.lt_two_pow_self.le
  let exclHi := free + d + 1
  let P (k : ℕ) (s : Data numRegs) : Prop :=
    s.regs rZero = 0 ∧ s.regs rOne = 1 ∧ s.regs rDim = d ∧
    s.regs rCurDomPtr = domPtr ∧ s.regs rCurDomLen = dom.length ∧
    s.regs rStageCutoff = cutoff ∧ s.regs rSignMode = signMode ∧
    s.regs rFbRoots = fbBase ∧ s.regs rRootsOut = free ∧
    ∃ curFree, s.regs rFree = curFree ∧
      exclHi ≤ curFree ∧ curFree ≤ exclHi + k * (2 * d * dom.length + 2) ∧
      (∀ j ≤ k, ∃ stFn, HoldsTrieOutside s.mem free exclHi curFree d (s.mem (free + j)) stFn ∧
        ∀ X ∈ dom, stFn (setMask X) =
          Signed.encode (yatesTransform c ((List.finRange d).take j) G X)) ∧
      (∀ a, a < free ∨ curFree ≤ a → s.mem a = x.mem a)
  have hbody (s : Data numRegs) (hs : P (s.regs rStageIdx) s) (hk : s.regs rStageIdx < d) :
      ∃ z, ExecWithin w stagesStep s z (dom.length * (32 * d + 63) + 20) ∧
        P (s.regs rStageIdx + 1) z ∧ z.regs rStageIdx = s.regs rStageIdx + 1 := by
    generalize hk_eq : s.regs rStageIdx = k at hs hk ⊢
    dsimp only [P] at hs
    obtain ⟨hsz, hso, hsd, hsdp, hsdl, hscut, hssm, hsfbb, hsro,
      curFree, hsfree, hcf_lo, hcf_hi, hstages, hsframe⟩ := hs
    let coord : Fin d := ⟨k, hk⟩
    let G_k := yatesTransform c ((List.finRange d).take k) G
    obtain ⟨curFn, hcur_out, hcur_eq⟩ := hstages k le_rfl
    have hcur_trie : HoldsTrie s.mem curFree d (s.mem (free + k)) curFn := hcur_out.toHoldsTrie
    have hG_k_le : ∀ Y, (G_k Y).natAbs ≤ B := fun Y =>
      (natAbs_yatesTransform_le hc_abs ((List.nodup_finRange d).sublist (List.take_sublist _ _))
        hG_le Y).trans hB
    have hf_ro_k : Fits w (free + k) := hfit_free.of_le (by dsimp [exclHi] at *; omega)
    have hf_shl : Fits w (1 <<< k) := by
      rw [Nat.shiftLeft_eq, one_mul]
      exact hfit_mask.of_le (Nat.pow_le_pow_right Nat.two_pos hk.le)
    have hsetup : ∃ u₀ fbRoot fbFn,
        ExecWithin (B := .standard) w (ram[
          rGenTmp ← rRootsOut + rStageIdx;
          rStageCurRoot ← *rGenTmp;
          if rStageCutoff = rZero then [
            rStageFbRoot ← #0
          ] else [
            rGenTmp ← rFbRoots + rStageIdx;
            rStageFbRoot ← *rGenTmp
          ];
          rGenBitMask ← rOne <<< rStageIdx ]) s u₀ 8 ∧
        u₀.regs rZero = 0 ∧ u₀.regs rOne = 1 ∧ u₀.regs rDim = d ∧
        u₀.regs rCurDomPtr = domPtr ∧ u₀.regs rCurDomLen = dom.length ∧
        u₀.regs rStageCutoff = cutoff ∧ u₀.regs rSignMode = signMode ∧
        u₀.regs rFbRoots = fbBase ∧ u₀.regs rRootsOut = free ∧
        u₀.regs rStageIdx = k ∧ u₀.regs rFree = curFree ∧
        u₀.regs rStageCurRoot = s.mem (free + k) ∧
        u₀.regs rStageFbRoot = fbRoot ∧ u₀.regs rGenBitMask = (1 <<< coord.val) ∧
        u₀.mem = s.mem ∧ HoldsTrie s.mem curFree d fbRoot fbFn ∧
        (∀ Y, #Y < cutoff → P_low Y → fbFn (setMask Y) = Signed.encode (G_k Y)) := by
      by_cases hcut0 : cutoff = 0
      · have hst : ∃ u₀, ExecWithin (B := .standard) w (ram[
            rGenTmp ← rRootsOut + rStageIdx;
            rStageCurRoot ← *rGenTmp;
            if rStageCutoff = rZero then [
              rStageFbRoot ← #0
            ] else [
              rGenTmp ← rFbRoots + rStageIdx;
              rStageFbRoot ← *rGenTmp
            ];
            rGenBitMask ← rOne <<< rStageIdx ]) s u₀ 8 ∧
            u₀.regs rZero = 0 ∧ u₀.regs rOne = 1 ∧ u₀.regs rDim = d ∧
            u₀.regs rCurDomPtr = domPtr ∧ u₀.regs rCurDomLen = dom.length ∧
            u₀.regs rStageCutoff = cutoff ∧ u₀.regs rSignMode = signMode ∧
            u₀.regs rFbRoots = fbBase ∧ u₀.regs rRootsOut = free ∧
            u₀.regs rStageIdx = k ∧ u₀.regs rFree = curFree ∧
            u₀.regs rStageCurRoot = s.mem (free + k) ∧
            u₀.regs rStageFbRoot = 0 ∧ u₀.regs rGenBitMask = (1 <<< coord.val) ∧
            u₀.mem = s.mem := by
          wram_exec [hsz, hso, hsro, hk_eq, hscut, hcut0]
          wram_simp [hsz, hso, hsd, hsdp, hsdl, hscut, hssm, hsfbb, hsro, hk_eq, hsfree, coord]
        obtain ⟨u₀, he₀, hzz, hzo, hzd, hzdp, hzdl, hzcut, hzsm, hzfbb, hzro, hzk, hzfr,
          hzcr, hzfbr, hzbm, hzm⟩ := hst
        refine ⟨u₀, 0, fun _ => 0, he₀, hzz, hzo, hzd, hzdp, hzdl, hzcut, hzsm, hzfbb, hzro,
          hzk, hzfr, hzcr, hzfbr, hzbm, hzm, HoldsTrie.zero_root _ _ _, fun _ hY _ => by omega⟩
      · obtain ⟨hfbb_le, hfb_all⟩ := hfb_valid (by omega)
        obtain ⟨fbFn, hfb_tr, hfb_eq⟩ := hfb_all k hk
        have hf_fbb_k : Fits w (fbBase + k) := hfit_free.of_le (by dsimp [exclHi] at *; omega)
        have hs_fbb_read : s.mem (fbBase + k) = x.mem (fbBase + k) :=
          hsframe _ (Or.inl (by omega))
        have hfb_tr_s : HoldsTrie s.mem curFree d (s.mem (fbBase + k)) fbFn := by
          rw [hs_fbb_read]
          exact (hfb_tr.congr_below fun a ha => hsframe a (Or.inl ha)).mono_bound
            (by dsimp [exclHi] at hcf_lo; omega)
        have hst : ∃ u₀, ExecWithin (B := .standard) w (ram[
            rGenTmp ← rRootsOut + rStageIdx;
            rStageCurRoot ← *rGenTmp;
            if rStageCutoff = rZero then [
              rStageFbRoot ← #0
            ] else [
              rGenTmp ← rFbRoots + rStageIdx;
              rStageFbRoot ← *rGenTmp
            ];
            rGenBitMask ← rOne <<< rStageIdx ]) s u₀ 8 ∧
            u₀.regs rZero = 0 ∧ u₀.regs rOne = 1 ∧ u₀.regs rDim = d ∧
            u₀.regs rCurDomPtr = domPtr ∧ u₀.regs rCurDomLen = dom.length ∧
            u₀.regs rStageCutoff = cutoff ∧ u₀.regs rSignMode = signMode ∧
            u₀.regs rFbRoots = fbBase ∧ u₀.regs rRootsOut = free ∧
            u₀.regs rStageIdx = k ∧ u₀.regs rFree = curFree ∧
            u₀.regs rStageCurRoot = s.mem (free + k) ∧
            u₀.regs rStageFbRoot = s.mem (fbBase + k) ∧
            u₀.regs rGenBitMask = (1 <<< coord.val) ∧ u₀.mem = s.mem := by
          wram_exec [hsz, hso, hsro, hk_eq, hscut, hcut0, hsfbb]
          wram_simp [hsz, hso, hsd, hsdp, hsdl, hscut, hssm, hsfbb, hsro, hk_eq, hsfree, coord]
        obtain ⟨u₀, he₀, hzz, hzo, hzd, hzdp, hzdl, hzcut, hzsm, hzfbb, hzro, hzk, hzfr,
          hzcr, hzfbr, hzbm, hzm⟩ := hst
        exact ⟨u₀, s.mem (fbBase + k), fbFn, he₀, hzz, hzo, hzd, hzdp, hzdl, hzcut, hzsm,
          hzfbb, hzro, hzk, hzfr, hzcr, hzfbr, hzbm, hzm, hfb_tr_s, hfb_eq⟩
    obtain ⟨u₀, fbRoot, fbFn, he₀, hu₀z, hu₀o, hu₀d, hu₀dp, hu₀dl, hu₀cut, hu₀sm, hu₀fbb,
      hu₀ro, hu₀k, hu₀fr, hu₀cr, hu₀fbr, hu₀bm, hu₀mem, hfb_tr, hfb_eq⟩ := hsetup
    have hpass_fit : Fits w (curFree + 2 + 2 * d * dom.length) := by
      have : curFree + 2 + 2 * d * dom.length ≤
          free + d + 1 + d * (2 * d * dom.length + 2) := by
        calc curFree + 2 + 2 * d * dom.length
            ≤ exclHi + k * (2 * d * dom.length + 2) + (2 * d * dom.length + 2) := by omega
          _ = exclHi + (k + 1) * (2 * d * dom.length + 2) := by ring
          _ ≤ exclHi + d * (2 * d * dom.length + 2) :=
              Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
      exact hfit_free.of_le this
    have hdom_u₀ : HoldsDom u₀.mem domPtr dom := by
      rw [hu₀mem]
      intro p hp
      rw [hsframe _ (Or.inl (by omega)), hsframe _ (Or.inl (by omega))]
      exact hdom p hp
    obtain ⟨u₁, free', S_new, outFn, he_pass, hu₁_sav, hu₁_free, hcf_le', hfree'_le,
      hS_new, hrep_new, hout_eq, hu₁_frame, hu₁_regs⟩ :=
      exec_passCode (coord := coord) (P_low := P_low) (G_k := G_k) (B := B) u₀
        hu₀z hu₀o hu₀d hu₀dp hu₀dl hu₀fr (by dsimp [exclHi] at hcf_lo; omega)
        hu₀bm hu₀cut hu₀sm hu₀cr hu₀fbr hnd hdom_u₀ (by dsimp [exclHi] at hcf_lo; omega)
        (fun X hX hc => hdom_closed X hX coord hc)
        (by rwa [hu₀mem]) (by rwa [hu₀mem]) hcur_eq hfb_eq hG_k_le
        hfit_val hpass_fit hfit_mask
    have hu₁_k : u₁.regs rStageIdx = k :=
      (hu₁_regs rStageIdx (by decide)).trans hu₀k
    have hu₁_o : u₁.regs rOne = 1 :=
      (hu₁_regs rOne (by decide)).trans hu₀o
    have hu₁_ro : u₁.regs rRootsOut = free :=
      (hu₁_regs rRootsOut (by decide)).trans hu₀ro
    have hf_k1 : Fits w (k + 1) := hfit_d.of_le (by omega)
    have hf_ro_k1 : Fits w (free + (k + 1)) := hfit_free.of_le (by dsimp [exclHi] at *; omega)
    have hstore : ∃ z, ExecWithin (B := .standard) w (ram[
        rStageIdx ← rStageIdx + rOne;
        rGenTmp ← rRootsOut + rStageIdx;
        *rGenTmp ← rCellSaved ]) u₁ z 3 ∧
        z.regs rStageIdx = k + 1 ∧
        z.mem = Function.update u₁.mem (free + (k + 1)) curFree ∧
        ∀ i : Fin numRegs, i ≠ rStageIdx ∧ i ≠ rGenTmp → z.regs i = u₁.regs i := by
      have hst : ∃ z, ExecWithin (B := .standard) w (ram[
          rStageIdx ← rStageIdx + rOne;
          rGenTmp ← rRootsOut + rStageIdx;
          *rGenTmp ← rCellSaved ]) u₁ z 3 ∧
          z.regs rStageIdx = k + 1 ∧
          z.mem = Function.update u₁.mem (free + (k + 1)) curFree := by
        wram_exec [hu₁_k, hu₁_o, hu₁_ro, hu₁_sav]
        wram_simp
      obtain ⟨z, hez, hzk, hzm⟩ := hst
      refine ⟨z, hez, hzk, hzm, fun i hi => hez.regs_eq ?_⟩
      revert i hi; decide +kernel
    obtain ⟨z, he_st, hz_k, hz_mem, hz_regs⟩ := hstore
    have hstep_tot : ExecWithin w stagesStep s z (dom.length * (32 * d + 63) + 20) :=
      (he₀.seq (he_pass.seq he_st)).mono (by omega)
    have reg_z (i : Fin numRegs) (ht : ¬ IsTabMod i) (hs : i ≠ rStageIdx ∧ i ≠ rGenTmp) :
        z.regs i = u₀.regs i := (hz_regs i hs).trans (hu₁_regs i ht)
    refine ⟨z, hstep_tot, ?_, hz_k⟩
    dsimp only [P]
    refine ⟨(reg_z rZero (by decide) (by decide)).trans hu₀z,
      (reg_z rOne (by decide) (by decide)).trans hu₀o,
      (reg_z rDim (by decide) (by decide)).trans hu₀d,
      (reg_z rCurDomPtr (by decide) (by decide)).trans hu₀dp,
      (reg_z rCurDomLen (by decide) (by decide)).trans hu₀dl,
      (reg_z rStageCutoff (by decide) (by decide)).trans hu₀cut,
      (reg_z rSignMode (by decide) (by decide)).trans hu₀sm,
      (reg_z rFbRoots (by decide) (by decide)).trans hu₀fbb,
      (reg_z rRootsOut (by decide) (by decide)).trans hu₀ro,
      free', (hz_regs rFree (by decide)).trans hu₁_free, by omega, ?_, ?_, ?_⟩
    · calc free' ≤ curFree + (2 * d * dom.length + 2) := by omega
        _ ≤ exclHi + k * (2 * d * dom.length + 2) + (2 * d * dom.length + 2) :=
            Nat.add_le_add_right hcf_hi _
        _ = exclHi + (k + 1) * (2 * d * dom.length + 2) := by ring
    · intro j hj
      by_cases hjk : j = k + 1
      · subst hjk
        have hroot_at : z.mem (free + (k + 1)) = curFree := by simp [hz_mem]
        rw [hroot_at]
        have hdisj_excl : Disjoint S_new (Set.Ico free exclHi) := by
          rw [Set.disjoint_left]
          intro a ha hexcl
          have := (hS_new ha).1; have := hexcl.2; omega
        have hrep_z : TrieRep z.mem d curFree S_new outFn :=
          hrep_new.congr_mem fun a ha => by
            have := (hS_new ha).1
            rw [hz_mem, Function.update_of_ne (by dsimp [exclHi] at hcf_lo; omega)]
        refine ⟨outFn, ⟨S_new, fun a ha => ⟨by
          dsimp [exclHi] at hcf_lo; have := (hS_new ha).1; omega,
          (hS_new ha).2⟩, hdisj_excl, hrep_z⟩, fun X hX => ?_⟩
        have htake1 : (List.finRange d).take (k + 1) = (List.finRange d).take k ++ [coord] := by
          rw [List.take_succ_eq_append_getElem (by simp [hk])]
          simp [coord]
        rw [htake1, yatesTransform_append, yatesTransform_cons, yatesTransform_nil]
        exact hout_eq X hX
      · obtain ⟨stFn, ⟨S_j, hSj_sub, hSj_disj, hSj_rep⟩, hst_eq⟩ := hstages j (by omega)
        have hslot_eq : z.mem (free + j) = s.mem (free + j) := by
          rw [hz_mem, Function.update_of_ne (by omega),
            hu₁_frame _ (Or.inl (by dsimp [exclHi] at hcf_lo; omega)), hu₀mem]
        rw [hslot_eq]
        have hrep_z : TrieRep z.mem d (s.mem (free + j)) S_j stFn :=
          hSj_rep.congr_mem fun a ha => by
            have ha_not_slot : a ≠ free + (k + 1) := fun h =>
              Set.disjoint_left.mp hSj_disj ha
                (by subst h; exact ⟨by omega, by dsimp [exclHi]; omega⟩)
            have ha_lt_cf : a < curFree := (hSj_sub ha).2
            rw [hz_mem, Function.update_of_ne ha_not_slot, hu₁_frame a (Or.inl ha_lt_cf), hu₀mem]
        exact ⟨stFn, ⟨S_j, fun a ha => ⟨(hSj_sub ha).1, (hSj_sub ha).2.trans_le (by omega)⟩,
          hSj_disj, hrep_z⟩, hst_eq⟩
    · intro a ha
      have ha_ne : a ≠ free + (k + 1) := by
        rcases ha with h1 | h2 <;> { dsimp [exclHi] at *; omega }
      rw [hz_mem, Function.update_of_ne ha_ne]
      rcases ha with ha_lo | ha_hi
      · rw [hu₁_frame a (Or.inl (by dsimp [exclHi] at hcf_lo; omega)), hu₀mem]
        exact hsframe a (Or.inl ha_lo)
      · rw [hu₁_frame a (Or.inr ha_hi), hu₀mem]
        exact hsframe a (Or.inr (by omega))
  have hf_d1 : Fits w (d + 1) := hfit_free.of_le (by omega)
  have hf_excl : Fits w (free + (d + 1)) := hfit_free.of_le (by omega)
  have hf_free0 : Fits w free := hfit_free.of_le (by omega)
  have hinit : ∃ s₀, ExecWithin (B := .standard) w (ram[
      rRootsOut ← rFree;
      rGenTmp ← rDim + rOne;
      rFree ← rFree + rGenTmp;
      *rRootsOut ← rStageCurRoot;
      rStageIdx ← #0 ]) x s₀ 5 ∧
      s₀.regs rZero = 0 ∧ s₀.regs rOne = 1 ∧ s₀.regs rDim = d ∧
      s₀.regs rCurDomPtr = domPtr ∧ s₀.regs rCurDomLen = dom.length ∧
      s₀.regs rStageCutoff = cutoff ∧ s₀.regs rSignMode = signMode ∧
      s₀.regs rFbRoots = fbBase ∧ s₀.regs rRootsOut = free ∧
      s₀.regs rFree = exclHi ∧ s₀.regs rStageIdx = 0 ∧
      s₀.mem = Function.update x.mem free initRoot := by
    wram_exec [ho, hd, hir, hfree]
    refine ⟨hz, ho, hd, hdp, hdl, hcut, hsm, hfbb, ?_, ?_, ?_, ?_⟩
    · wram_simp
    · wram_simp [exclHi]; omega
    · wram_simp
    · wram_simp
  obtain ⟨s₀, hinit_ex, hs₀z, hs₀o, hs₀d, hs₀dp, hs₀dl, hs₀cut, hs₀sm, hs₀fbb,
    hs₀ro, hs₀fr, hs₀k, hs₀mem⟩ := hinit
  have hs₀P : P (s₀.regs rStageIdx) s₀ := by
    dsimp only [P]
    rw [hs₀k]
    refine ⟨hs₀z, hs₀o, hs₀d, hs₀dp, hs₀dl, hs₀cut, hs₀sm, hs₀fbb, hs₀ro,
      exclHi, hs₀fr, le_rfl, by omega, ?_, ?_⟩
    · intro j hj
      obtain rfl : j = 0 := by omega
      simp only [Nat.add_zero, List.take_zero, yatesTransform_nil]
      have hroot0 : s₀.mem free = initRoot := by simp [hs₀mem]
      rw [hroot0]
      have ht_s₀ : HoldsTrie s₀.mem free d initRoot initFn :=
        htrie_init.congr_below fun a ha => by rw [hs₀mem, Function.update_of_ne (by omega)]
      exact ⟨initFn, ht_s₀.toOutside_of_le le_rfl (by dsimp [exclHi]; omega), hinit_eq⟩
    · intro a ha
      rw [hs₀mem, Function.update_of_ne
        (by rcases ha with h1 | h2 <;> { dsimp [exclHi] at *; omega })]
  obtain ⟨y, hloop, hyP, _⟩ := ExecWithin.loop_count P (fun s hs => hs.2.2.1) hbody
    (by simp [hs₀k]) hs₀P
  obtain ⟨_, _, _, _, _, _, _, _, hyro, endFree, hyfr, hlo_ef, hhi_ef, hystages, hyframe⟩ := hyP
  have htot : ExecWithin w stagesCode x y (d * (dom.length * (32 * d + 63) + 22) + 7) := by
    refine (hinit_ex.seq hloop).mono ?_
    rw [hs₀k, Nat.sub_zero]
    have h22 : dom.length * (32 * d + 63) + 20 + 2 = dom.length * (32 * d + 63) + 22 := by omega
    rw [h22]; omega
  refine ⟨y, endFree, htot, hyro, hyfr, hlo_ef, hhi_ef,
    fun k hk => let ⟨stFn, hout, heq⟩ := hystages k hk; ⟨stFn, hout.toHoldsTrie, heq⟩,
    hyframe, fun i hi => htot.regs_eq (stagesCode_preserves i hi)⟩

/-- Write `[0, 1, ..., d - 1]` (`List.finRange d`) to `rCoordsPtr[0 .. rDim - 1]`. -/
private def initCoordsStep : Code .standard numRegs := ram[
  rGenTmp ← rCoordsPtr + rGenIdx;
  *rGenTmp ← rGenIdx;
  rGenIdx ← rGenIdx + rOne ]

private def initIdentityCoords : Code .standard numRegs :=
  .seq (ram[ rGenIdx ← #0 ]) (.loop (.lt rGenIdx rDim) initCoordsStep)

private theorem initIdentityCoords_preserves (i : Fin numRegs) :
    i ≠ rGenIdx ∧ i ≠ rGenTmp → initIdentityCoords.Preserves i := by
  decide +kernel +revert

private theorem exec_initIdentityCoords {w d coordsPtr : ℕ} (x : Data numRegs)
    (ho : x.regs rOne = 1) (hd : x.regs rDim = d) (hcptr : x.regs rCoordsPtr = coordsPtr)
    (hfit_mem : Fits w (coordsPtr + d)) (hfit_d : Fits w d) :
    ∃ y, ExecWithin w initIdentityCoords x y (5 * d + 3) ∧
      (∀ j (hj : j < (List.finRange d).length),
        y.mem (coordsPtr + j) = (List.finRange d)[j].val) ∧
      (∀ a, a < coordsPtr ∨ coordsPtr + d ≤ a → y.mem a = x.mem a) ∧
      ∀ i : Fin numRegs, i ≠ rGenIdx ∧ i ≠ rGenTmp → y.regs i = x.regs i := by
  have hrun : ∃ y, ExecWithin w initIdentityCoords x y (5 * d + 3) ∧
      (∀ j (hj : j < d), y.mem (coordsPtr + j) = j) ∧
      (∀ a, a < coordsPtr ∨ coordsPtr + d ≤ a → y.mem a = x.mem a) := by
    let P (b : ℕ) (s : Data numRegs) : Prop :=
      s.regs rOne = 1 ∧ s.regs rDim = d ∧ s.regs rCoordsPtr = coordsPtr ∧
      (∀ j < b, s.mem (coordsPtr + j) = j) ∧
      (∀ a, a < coordsPtr ∨ coordsPtr + b ≤ a → s.mem a = x.mem a)
    have hbody (s : Data numRegs) (hs : P (s.regs rGenIdx) s) (hb : s.regs rGenIdx < d) :
        ∃ z, ExecWithin w initCoordsStep s z 3 ∧ P (s.regs rGenIdx + 1) z ∧
          z.regs rGenIdx = s.regs rGenIdx + 1 := by
      generalize hb_eq : s.regs rGenIdx = b at hs hb ⊢
      obtain ⟨hso, hsd, hscp, hdone, hsframe⟩ := hs
      have hf_addr : Fits w (coordsPtr + b) := hfit_mem.of_le (by omega)
      have hf_b1 : Fits w (b + 1) := hfit_d.of_le (by omega)
      have hst : ∃ z, ExecWithin w initCoordsStep s z 3 ∧
          z.regs rOne = 1 ∧ z.regs rDim = d ∧ z.regs rCoordsPtr = coordsPtr ∧
          z.regs rGenIdx = b + 1 ∧ z.mem = Function.update s.mem (coordsPtr + b) b := by
        unfold initCoordsStep
        wram_exec [hso, hscp, hb_eq]
        wram_simp [hso, hsd, hscp, hb_eq]
      obtain ⟨z, hez, hzo, hzd, hzcp, hzb, hzm⟩ := hst
      refine ⟨z, hez, ⟨hzo, hzd, hzcp, ?_, ?_⟩, hzb⟩
      · intro j hj
        by_cases hjb : j = b
        · subst hjb; simp [hzm]
        · rw [hzm, Function.update_of_ne (by omega)]; exact hdone j (by omega)
      · intro a ha
        rw [hzm, Function.update_of_ne (by omega)]; exact hsframe a (by omega)
    let x₀ := x.set rGenIdx 0
    have hinit : ExecWithin (B := .standard) w (ram[ rGenIdx ← #0 ]) x x₀ 1 := by wram_exec
    have hx₀ : P (x₀.regs rGenIdx) x₀ :=
      ⟨by simp [x₀, ho], by simp [x₀, hd], by simp [x₀, hcptr],
       by simp [x₀], fun _ _ => rfl⟩
    obtain ⟨y, hloop, hyP, _⟩ := ExecWithin.loop_count P (fun s hs => hs.2.1) hbody
      (by simp [x₀]) hx₀
    obtain ⟨_, _, _, hydone, hyframe⟩ := hyP
    exact ⟨y, (hinit.seq hloop).mono (by simp [x₀]; omega), hydone, hyframe⟩
  obtain ⟨y, he, hydone, hyframe⟩ := hrun
  refine ⟨y, he, fun j hj => ?_, hyframe,
    fun i hi => he.regs_eq (initIdentityCoords_preserves i hi)⟩
  rw [List.length_finRange] at hj
  simpa using hydone j hj

/-! ### Combinatorial counts, envelopes, and the 3-transform kernel -/

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

private theorem mask_fits_of_valueEnvelope {w d W : ℕ} (h : Fits w (valueEnvelope d W)) :
    Fits w (2 ^ d) := by
  refine h.of_le ?_
  dsimp only [valueEnvelope]
  have h28 : 2 ^ d ≤ 8 ^ d := Nat.pow_le_pow_left (by decide) d
  have h1 : 1 ≤ (W + 1) ^ 2 := Nat.one_le_pow 2 (W + 1) (Nat.succ_pos W)
  have hmul : 2 ^ d ≤ 8 ^ d * (W + 1) ^ 2 :=
    h28.trans (Nat.le_mul_of_pos_right _ h1)
  omega

private def tripleSpace (d L : ℕ) : ℕ :=
  3 * (d + 1 + d * (2 * d * L + 2)) + (2 + 2 * d * L)

private def tripleTime (d L : ℕ) : ℕ :=
  3 * (d * (L * (32 * d + 63) + 22) + 7) + (L * (32 * d + 53) + 9) + 15

private theorem tripleSpace_le (d L : ℕ) :
    d + 2 * L + tripleSpace d L ≤ 6 * (d + 1) ^ 2 * (L + 1) + 4 * (d + 1) ^ 2 := by
  dsimp only [tripleSpace]
  rw [sq]
  nlinarith

private theorem phaseTime_le {d L : ℕ} (hL : 1 ≤ L) :
    d * (20 * L + 12) + 8 + (12 * L + 3) + (11 * d + 5) + (9 * d + 8) + tripleTime d L + 35 ≤
      180 * (d + 1) ^ 2 * L := by
  obtain ⟨Lp, rfl⟩ : ∃ Lp, L = Lp + 1 := ⟨L - 1, (Nat.sub_add_cancel hL).symm⟩
  dsimp only [tripleTime]
  have hid :
      (d * (20 * (Lp + 1) + 12) + 8 + (12 * (Lp + 1) + 3) + (11 * d + 5) + (9 * d + 8) +
        (3 * (d * ((Lp + 1) * (32 * d + 63) + 22) + 7) +
          ((Lp + 1) * (32 * d + 53) + 9) + 15) + 35) +
      (84 * d ^ 2 + 21 * d + 11 + Lp * (84 * d ^ 2 + 119 * d + 115)) =
      180 * (d + 1) ^ 2 * (Lp + 1) := by ring
  omega

private abbrev IsTripleMod (i : Fin numRegs) : Prop :=
  IsStageMod i ∨ i = rSignMode ∨ i = rFbRoots ∨ i = rQFsBase ∨ i = rQGsBase

/-- Run the 3 trimmed transforms (`f` with `+1`, `g` with `+1`, pointwise product `h₀ = f_d * g_d`,
and `h` with `-1`) on `dom` at `rCurDomPtr[0 .. rCurDomLen - 1]`. Leaves the three stage-root base
addresses in `rQFsBase`, `rQGsBase`, and `rRootsOut`. -/
private def runTransformTriple : Code .standard numRegs :=
  .seq (ram[
    rStageCurRoot ← rTrieF;
    rFbRoots ← rPreFsBase;
    rSignMode ← #0 ])
  (.seq stagesCode
    (.seq (ram[
      rQFsBase ← rRootsOut;
      rStageCurRoot ← rTrieG;
      rFbRoots ← rPreGsBase;
      rSignMode ← #0 ])
    (.seq stagesCode
      (.seq (ram[
        rQGsBase ← rRootsOut;
        rGenTmp ← rQFsBase + rDim;
        rStageCurRoot ← *rGenTmp;
        rGenTmp ← rQGsBase + rDim;
        rStageFbRoot ← *rGenTmp ])
      (.seq tabulateMul
        (.seq (ram[
          rStageCurRoot ← rCellSaved;
          rFbRoots ← rPreHsBase;
          rSignMode ← #1 ])
        stagesCode))))))

private theorem runTransformTriple_preserves (i : Fin numRegs) :
    ¬ IsTripleMod i → runTransformTriple.Preserves i := by
  decide +kernel +revert

private theorem exec_runTransformTriple {w d domPtr free rootF rootG preFs preGs preHs cutoff W : ℕ}
    {dom : List (Finset (Fin d))} {P_low : Finset (Fin d) → Prop}
    {fnF fnG : ℕ → ℕ} {f g : Finset (Fin d) → ℤ} (x : Data numRegs)
    (hz : x.regs rZero = 0) (ho : x.regs rOne = 1) (hd : x.regs rDim = d)
    (hdp : x.regs rCurDomPtr = domPtr) (hdl : x.regs rCurDomLen = dom.length)
    (hcut : x.regs rStageCutoff = cutoff)
    (htF_reg : x.regs rTrieF = rootF) (htG_reg : x.regs rTrieG = rootG)
    (hpFs : x.regs rPreFsBase = preFs) (hpGs : x.regs rPreGsBase = preGs)
    (hpHs : x.regs rPreHsBase = preHs)
    (hfree : x.regs rFree = free) (hfree_pos : 1 ≤ free)
    (hnd : dom.Nodup) (hdom : HoldsDom x.mem domPtr dom)
    (hdom_below : domPtr + 2 * dom.length ≤ free)
    (hdom_closed : ∀ X ∈ dom, ∀ coord : Fin d, coord ∈ X →
      (cutoff ≤ #(X.erase coord) → X.erase coord ∈ dom) ∧
      (#(X.erase coord) < cutoff → P_low (X.erase coord)))
    (htrieF : HoldsTrie x.mem free d rootF fnF)
    (htrieG : HoldsTrie x.mem free d rootG fnG)
    (hf_eq : ∀ S : Finset (Fin d), fnF (setMask S) = Signed.encode (f S))
    (hg_eq : ∀ S : Finset (Fin d), fnG (setMask S) = Signed.encode (g S))
    (hf_le : ∀ S, (f S).natAbs ≤ W) (hg_le : ∀ S, (g S).natAbs ≤ W)
    (hfb_valid : 0 < cutoff →
      preFs + d ≤ free ∧ preGs + d ≤ free ∧ preHs + d ≤ free ∧
      (∀ k < d, ∃ fbFn, HoldsTrie x.mem free d (x.mem (preFs + k)) fbFn ∧
        ∀ Y, #Y < cutoff → P_low Y →
          fbFn (setMask Y) =
            Signed.encode (yatesTransform (1 : ℤ) ((List.finRange d).take k) f Y)) ∧
      (∀ k < d, ∃ fbFn, HoldsTrie x.mem free d (x.mem (preGs + k)) fbFn ∧
        ∀ Y, #Y < cutoff → P_low Y →
          fbFn (setMask Y) =
            Signed.encode (yatesTransform (1 : ℤ) ((List.finRange d).take k) g Y)) ∧
      (∀ k < d, ∃ fbFn, HoldsTrie x.mem free d (x.mem (preHs + k)) fbFn ∧
        ∀ Y, #Y < cutoff → P_low Y →
          fbFn (setMask Y) = Signed.encode (yatesTransform (-1 : ℤ) ((List.finRange d).take k)
            (fun S => subsetZeta f S * subsetZeta g S) Y)))
    (hfit_val : Fits w (valueEnvelope d W))
    (hfit_free : Fits w (free + tripleSpace d dom.length)) :
    let H : Finset (Fin d) → ℤ := fun S => subsetZeta f S * subsetZeta g S
    ∃ y fsBase gsBase hsBase endFree,
      ExecWithin w runTransformTriple x y (tripleTime d dom.length) ∧
      y.regs rQFsBase = fsBase ∧ y.regs rQGsBase = gsBase ∧
      y.regs rRootsOut = hsBase ∧ y.regs rFree = endFree ∧
      free ≤ endFree ∧ endFree ≤ free + tripleSpace d dom.length ∧
      fsBase + d < endFree ∧ gsBase + d < endFree ∧ hsBase + d < endFree ∧
      (∀ k ≤ d, ∃ stFn, HoldsTrie y.mem endFree d (y.mem (fsBase + k)) stFn ∧
        ∀ X ∈ dom, stFn (setMask X) =
          Signed.encode (yatesTransform (1 : ℤ) ((List.finRange d).take k) f X)) ∧
      (∀ k ≤ d, ∃ stFn, HoldsTrie y.mem endFree d (y.mem (gsBase + k)) stFn ∧
        ∀ X ∈ dom, stFn (setMask X) =
          Signed.encode (yatesTransform (1 : ℤ) ((List.finRange d).take k) g X)) ∧
      (∀ k ≤ d, ∃ stFn, HoldsTrie y.mem endFree d (y.mem (hsBase + k)) stFn ∧
        ∀ X ∈ dom, stFn (setMask X) =
          Signed.encode (yatesTransform (-1 : ℤ) ((List.finRange d).take k) H X)) ∧
      (∃ outFn, HoldsTrie y.mem endFree d (y.mem (hsBase + d)) outFn ∧
        ∀ X ∈ dom, outFn (setMask X) = Signed.encode (coveringProduct f g X)) ∧
      (∀ a, a < free ∨ endFree ≤ a → y.mem a = x.mem a) ∧
      ∀ i : Fin numRegs, ¬ IsTripleMod i → y.regs i = x.regs i := by
  intro H
  let B := 8 ^ d * (W + 1) ^ 2
  have hfit_B : Fits w (8 * B + 4) := hfit_val
  have hfit_mask : Fits w (2 ^ d) := mask_fits_of_valueEnvelope hfit_val
  have hB_fg : 2 ^ d * W ≤ B := by
    dsimp only [B]
    have h28 : 2 ^ d ≤ 8 ^ d := Nat.pow_le_pow_left (by decide) d
    have hW : W ≤ (W + 1) ^ 2 := by rw [sq]; nlinarith
    exact Nat.mul_le_mul h28 hW
  have hH_le : ∀ S, (H S).natAbs ≤ 4 ^ d * W ^ 2 := by
    intro S
    dsimp only [H]
    have hzf : subsetZeta f S = yatesTransform (1 : ℤ) (List.finRange d) f S := by
      rw [← yatesTransform_natOne_eq_intOne,
        yatesTransform_one_apply (List.nodup_finRange d) f (by intro i _; simp)]
    have hzg : subsetZeta g S = yatesTransform (1 : ℤ) (List.finRange d) g S := by
      rw [← yatesTransform_natOne_eq_intOne,
        yatesTransform_one_apply (List.nodup_finRange d) g (by intro i _; simp)]
    have h1 : (subsetZeta f S).natAbs ≤ 2 ^ d * W := by
      rw [hzf]; exact natAbs_yatesTransform_le (by decide) (List.nodup_finRange d) hf_le S
    have h2 : (subsetZeta g S).natAbs ≤ 2 ^ d * W := by
      rw [hzg]; exact natAbs_yatesTransform_le (by decide) (List.nodup_finRange d) hg_le S
    rw [Int.natAbs_mul]
    calc (subsetZeta f S).natAbs * (subsetZeta g S).natAbs
        ≤ (2 ^ d * W) * (2 ^ d * W) := Nat.mul_le_mul h1 h2
      _ = (2 * 2) ^ d * W ^ 2 := by rw [Nat.mul_pow]; ring
      _ = 4 ^ d * W ^ 2 := rfl
  have hB_H : 2 ^ d * (4 ^ d * W ^ 2) ≤ B := by
    dsimp only [B]
    have h248 : 2 ^ d * 4 ^ d = 8 ^ d := by rw [← Nat.mul_pow]
    calc 2 ^ d * (4 ^ d * W ^ 2) = (2 ^ d * 4 ^ d) * W ^ 2 := by ring
      _ = 8 ^ d * W ^ 2 := by rw [h248]
      _ ≤ 8 ^ d * (W + 1) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
  -- Phase 1: f stages
  let u₀ := ((x.set rStageCurRoot rootF).set rFbRoots preFs).set rSignMode 0
  have he₀ : ExecWithin (B := .standard) w
      (ram[ rStageCurRoot ← rTrieF; rFbRoots ← rPreFsBase; rSignMode ← #0 ]) x u₀ 3 := by
    wram_exec [htF_reg, hpFs]
  obtain ⟨u₁, free₁, he_stF, hu₁_ro, hu₁_free, hlo₁, hhi₁, hstF, hfr₁, hreg₁⟩ :=
    exec_stagesCode (initRoot := rootF) (fbBase := preFs) (signMode := 0)
      (P_low := P_low) (G := f) (B₀ := W) (B := B) u₀
      (by simp [u₀, hz]) (by simp [u₀, ho]) (by simp [u₀, hd])
      (by simp [u₀, hdp]) (by simp [u₀, hdl])
      (by simp [u₀, hcut]) (by simp [u₀]) (by simp [u₀])
      (by simp [u₀]) (by simp [u₀, hfree]) hfree_pos
      hnd hdom hdom_below hdom_closed htrieF (fun X _ => hf_eq X)
      (fun hpos => ⟨(hfb_valid hpos).1, (hfb_valid hpos).2.2.2.1⟩)
      hf_le hB_fg hfit_B (hfit_free.of_le (by dsimp [tripleSpace]; omega)) hfit_mask
  -- Phase 2: g stages
  have hu₁_tG : u₁.regs rTrieG = rootG := by
    rw [hreg₁ rTrieG (by decide)]; simp [u₀, htG_reg]
  have hu₁_pGs : u₁.regs rPreGsBase = preGs := by
    rw [hreg₁ rPreGsBase (by decide)]; simp [u₀, hpGs]
  let u₂ := (((u₁.set rQFsBase free).set rStageCurRoot rootG).set rFbRoots preGs).set rSignMode 0
  have he₂ : ExecWithin (B := .standard) w (ram[
      rQFsBase ← rRootsOut;
      rStageCurRoot ← rTrieG;
      rFbRoots ← rPreGsBase;
      rSignMode ← #0 ]) u₁ u₂ 4 := by
    wram_exec [hu₁_ro, hu₁_tG, hu₁_pGs]
  have hdom_u₂ : HoldsDom u₂.mem domPtr dom := by
    intro p hp
    change u₁.mem _ = _ ∧ u₁.mem _ = _
    rw [hfr₁ _ (Or.inl (by omega)), hfr₁ _ (Or.inl (by omega))]
    exact hdom p hp
  have htrieG_u₂ : HoldsTrie u₂.mem free₁ d rootG fnG :=
    (htrieG.congr_below fun a ha => hfr₁ a (Or.inl ha)).mono_bound (by omega)
  have hfbG_u₂ : 0 < cutoff → preGs + d ≤ free₁ ∧
      ∀ k < d, ∃ fbFn, HoldsTrie u₂.mem free₁ d (u₂.mem (preGs + k)) fbFn ∧
        ∀ Y, #Y < cutoff → P_low Y →
          fbFn (setMask Y) =
            Signed.encode (yatesTransform (1 : ℤ) ((List.finRange d).take k) g Y) := by
    intro hpos
    obtain ⟨_, hpg_le, _, _, hfbG, _⟩ := hfb_valid hpos
    refine ⟨by omega, fun k hk => ?_⟩
    obtain ⟨fbFn, htr, heq⟩ := hfbG k hk
    have hm_eq : u₂.mem (preGs + k) = x.mem (preGs + k) := hfr₁ _ (Or.inl (by omega))
    rw [hm_eq]
    exact ⟨fbFn, (htr.congr_below fun a ha => hfr₁ a (Or.inl ha)).mono_bound (by omega), heq⟩
  have keep_u₀_u₁ (i : Fin numRegs) (h1 : ¬ IsStageMod i)
      (h0 : i ≠ rStageCurRoot ∧ i ≠ rFbRoots ∧ i ≠ rSignMode) : u₁.regs i = x.regs i := by
    rw [hreg₁ i h1]
    simp [u₀, Data.set_regs_of_ne h0.1, Data.set_regs_of_ne h0.2.1, Data.set_regs_of_ne h0.2.2]
  obtain ⟨u₃, free₂, he_stG, hu₃_ro, hu₃_free, hlo₂, hhi₂, hstG, hfr₂, hreg₃⟩ :=
    exec_stagesCode (initRoot := rootG) (fbBase := preGs) (signMode := 0)
      (P_low := P_low) (G := g) (B₀ := W) (B := B) u₂
      (by simpa [u₂] using (keep_u₀_u₁ rZero (by decide) (by decide)).trans hz)
      (by simpa [u₂] using (keep_u₀_u₁ rOne (by decide) (by decide)).trans ho)
      (by simpa [u₂] using (keep_u₀_u₁ rDim (by decide) (by decide)).trans hd)
      (by simpa [u₂] using (keep_u₀_u₁ rCurDomPtr (by decide) (by decide)).trans hdp)
      (by simpa [u₂] using (keep_u₀_u₁ rCurDomLen (by decide) (by decide)).trans hdl)
      (by simpa [u₂] using (keep_u₀_u₁ rStageCutoff (by decide) (by decide)).trans hcut)
      (by simp [u₂]) (by simp [u₂]) (by simp [u₂])
      (by simp [u₂, hu₁_free]) (by omega)
      hnd hdom_u₂ (by omega) hdom_closed htrieG_u₂ (fun X _ => hg_eq X)
      hfbG_u₂ hg_le hB_fg hfit_B (hfit_free.of_le (by dsimp [tripleSpace]; omega)) hfit_mask
  -- Phase 3: tabulateMul on stage d of f and g
  have hu₃_qFs : u₃.regs rQFsBase = free := by
    rw [hreg₃ rQFsBase (by decide)]; simp [u₂]
  have hu₃_d : u₃.regs rDim = d := by
    rw [hreg₃ rDim (by decide)]
    simpa [u₂] using (keep_u₀_u₁ rDim (by decide) (by decide)).trans hd
  have hf_f0_d : Fits w (free + d) := hfit_free.of_le (by dsimp [tripleSpace]; omega)
  have hf_f1_d : Fits w (free₁ + d) := hfit_free.of_le (by dsimp [tripleSpace] at *; omega)
  have hprep_mul : ∃ u₄, ExecWithin (B := .standard) w (ram[
      rQGsBase ← rRootsOut;
      rGenTmp ← rQFsBase + rDim;
      rStageCurRoot ← *rGenTmp;
      rGenTmp ← rQGsBase + rDim;
      rStageFbRoot ← *rGenTmp ]) u₃ u₄ 5 ∧
      u₄.regs rQGsBase = free₁ ∧
      u₄.regs rStageCurRoot = u₃.mem (free + d) ∧
      u₄.regs rStageFbRoot = u₃.mem (free₁ + d) ∧
      u₄.mem = u₃.mem ∧
      ∀ i : Fin numRegs, i ≠ rQGsBase ∧ i ≠ rGenTmp ∧ i ≠ rStageCurRoot ∧ i ≠ rStageFbRoot →
        u₄.regs i = u₃.regs i := by
    have hst : ∃ u₄, ExecWithin (B := .standard) w (ram[
        rQGsBase ← rRootsOut;
        rGenTmp ← rQFsBase + rDim;
        rStageCurRoot ← *rGenTmp;
        rGenTmp ← rQGsBase + rDim;
        rStageFbRoot ← *rGenTmp ]) u₃ u₄ 5 ∧
        u₄.regs rQGsBase = free₁ ∧
        u₄.regs rStageCurRoot = u₃.mem (free + d) ∧
        u₄.regs rStageFbRoot = u₃.mem (free₁ + d) ∧ u₄.mem = u₃.mem := by
      wram_exec [hu₃_ro, hu₃_qFs, hu₃_d]
      wram_simp
    obtain ⟨u₄, he₄, hqg, hcr, hfbr, hm⟩ := hst
    refine ⟨u₄, he₄, hqg, hcr, hfbr, hm, fun i hi => he₄.regs_eq ?_⟩
    revert i hi; decide +kernel
  obtain ⟨u₄, he₄, hu₄_qGs, hu₄_cr, hu₄_fbr, hu₄_mem, hreg₄⟩ := hprep_mul
  obtain ⟨stFnF_d, htrF_d, heqF_d⟩ := hstF d le_rfl
  obtain ⟨stFnG_d, htrG_d, heqG_d⟩ := hstG d le_rfl
  have hm_f_d : u₃.mem (free + d) = u₁.mem (free + d) := hfr₂ _ (Or.inl (by omega))
  have htrF_d_u₄ : HoldsTrie u₄.mem free₂ d (u₃.mem (free + d)) stFnF_d := by
    rw [hu₄_mem, hm_f_d]
    exact (htrF_d.congr_below fun a ha => hfr₂ a (Or.inl ha)).mono_bound (by omega)
  have htrG_d_u₄ : HoldsTrie u₄.mem free₂ d (u₃.mem (free₁ + d)) stFnG_d := by
    rwa [hu₄_mem]
  have hzetaF_eq : ∀ X ∈ dom, stFnF_d (setMask X) = Signed.encode (subsetZeta f X) ∧
      (subsetZeta f X).natAbs ≤ B := by
    intro X hX
    have htake : (List.finRange d).take d = List.finRange d := by simp
    have hzf : yatesTransform (1 : ℤ) ((List.finRange d).take d) f X = subsetZeta f X := by
      rw [htake, ← yatesTransform_natOne_eq_intOne,
        yatesTransform_one_apply (List.nodup_finRange d) f (by intro i _; simp)]
    refine ⟨by rw [heqF_d X hX]; simp only [↓reduceIte, hzf], ?_⟩
    rw [← hzf]
    exact (natAbs_yatesTransform_le (by decide)
      ((List.nodup_finRange d).sublist (List.take_sublist _ _)) hf_le X).trans hB_fg
  have hzetaG_eq : ∀ X ∈ dom, stFnG_d (setMask X) = Signed.encode (subsetZeta g X) ∧
      (subsetZeta g X).natAbs ≤ B := by
    intro X hX
    have htake : (List.finRange d).take d = List.finRange d := by simp
    have hzg : yatesTransform (1 : ℤ) ((List.finRange d).take d) g X = subsetZeta g X := by
      rw [htake, ← yatesTransform_natOne_eq_intOne,
        yatesTransform_one_apply (List.nodup_finRange d) g (by intro i _; simp)]
    refine ⟨by rw [heqG_d X hX]; simp only [↓reduceIte, hzg], ?_⟩
    rw [← hzg]
    exact (natAbs_yatesTransform_le (by decide)
      ((List.nodup_finRange d).sublist (List.take_sublist _ _)) hg_le X).trans hB_fg
  have hdom_u₄ : HoldsDom u₄.mem domPtr dom := by
    rw [hu₄_mem]
    intro p hp
    rw [hfr₂ _ (Or.inl (by omega)), hfr₂ _ (Or.inl (by omega))]
    exact hdom_u₂ p hp
  have keep_u₃_x (i : Fin numRegs) (h1 : ¬ IsStageMod i)
      (h0 : i ≠ rStageCurRoot ∧ i ≠ rFbRoots ∧ i ≠ rSignMode ∧ i ≠ rQFsBase) :
      u₃.regs i = x.regs i := by
    rw [hreg₃ i h1]
    simp only [u₂, Data.set_regs_of_ne h0.2.2.1, Data.set_regs_of_ne h0.2.1,
      Data.set_regs_of_ne h0.1, Data.set_regs_of_ne h0.2.2.2]
    exact keep_u₀_u₁ i h1 ⟨h0.1, h0.2.1, h0.2.2.1⟩
  obtain ⟨u₅, free₃, h0Fn, he_mul, hu₅_sav, hu₅_free, hlo₃, hhi₃, htr_h0, heq_h0,
    hfr₃, hreg₅⟩ :=
    exec_tabulateMul (valF := subsetZeta f) (valG := subsetZeta g) (B := B) u₄
      ((hreg₄ rZero (by decide)).trans ((keep_u₃_x rZero (by decide) (by decide)).trans hz))
      ((hreg₄ rOne (by decide)).trans ((keep_u₃_x rOne (by decide) (by decide)).trans ho))
      ((hreg₄ rDim (by decide)).trans hu₃_d)
      ((hreg₄ rCurDomPtr (by decide)).trans
        ((keep_u₃_x rCurDomPtr (by decide) (by decide)).trans hdp))
      ((hreg₄ rCurDomLen (by decide)).trans
        ((keep_u₃_x rCurDomLen (by decide) (by decide)).trans hdl))
      ((hreg₄ rFree (by decide)).trans hu₃_free) (by omega)
      hu₄_cr hu₄_fbr hnd hdom_u₄ (by omega) htrF_d_u₄ htrG_d_u₄
      hzetaF_eq hzetaG_eq
      (fun X _ => (hH_le X).trans (le_trans (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos d)) hB_H))
      hfit_B (hfit_free.of_le (by dsimp [tripleSpace] at *; omega)) hfit_mask
  -- Phase 4: H stages with signMode = 1 (-1)
  have hu₅_pHs : u₅.regs rPreHsBase = preHs := by
    rw [hreg₅ rPreHsBase (by decide), hreg₄ rPreHsBase (by decide)]
    exact (keep_u₃_x rPreHsBase (by decide) (by decide)).trans hpHs
  let u₆ := ((u₅.set rStageCurRoot free₂).set rFbRoots preHs).set rSignMode 1
  have he₆ : ExecWithin (B := .standard) w
      (ram[ rStageCurRoot ← rCellSaved; rFbRoots ← rPreHsBase; rSignMode ← #1 ]) u₅ u₆ 3 := by
    wram_exec [hu₅_sav, hu₅_pHs]
  have below_u₅_x : ∀ a < free, u₅.mem a = x.mem a := fun a ha => by
    rw [hfr₃ a (Or.inl (by omega)), hu₄_mem, hfr₂ a (Or.inl (by omega))]
    change u₁.mem a = x.mem a
    rw [hfr₁ a (Or.inl ha)]
    rfl
  have hdom_u₆ : HoldsDom u₆.mem domPtr dom := by
    intro p hp
    change u₅.mem _ = _ ∧ u₅.mem _ = _
    rw [below_u₅_x _ (by omega), below_u₅_x _ (by omega)]
    exact hdom p hp
  have hfbH_u₆ : 0 < cutoff → preHs + d ≤ free₃ ∧
      ∀ k < d, ∃ fbFn, HoldsTrie u₆.mem free₃ d (u₆.mem (preHs + k)) fbFn ∧
        ∀ Y, #Y < cutoff → P_low Y →
          fbFn (setMask Y) =
            Signed.encode (yatesTransform (-1 : ℤ) ((List.finRange d).take k) H Y) := by
    intro hpos
    obtain ⟨_, _, hph_le, _, _, hfbH⟩ := hfb_valid hpos
    refine ⟨by omega, fun k hk => ?_⟩
    obtain ⟨fbFn, htr, heq⟩ := hfbH k hk
    have hm_eq : u₆.mem (preHs + k) = x.mem (preHs + k) := below_u₅_x _ (by omega)
    rw [hm_eq]
    exact ⟨fbFn, (htr.congr_below below_u₅_x).mono_bound (by omega), heq⟩
  have keep_u₅ (i : Fin numRegs) (ht : ¬ IsTabMod i)
      (h4 : i ≠ rQGsBase ∧ i ≠ rGenTmp ∧ i ≠ rStageCurRoot ∧ i ≠ rStageFbRoot) :
      u₅.regs i = u₃.regs i :=
    (hreg₅ i ht).trans (hreg₄ i h4)
  have hu₆_z : u₆.regs rZero = 0 := by
    simpa [u₆] using (keep_u₅ rZero (by decide) (by decide)).trans
      ((keep_u₃_x rZero (by decide) (by decide)).trans hz)
  have hu₆_o : u₆.regs rOne = 1 := by
    simpa [u₆] using (keep_u₅ rOne (by decide) (by decide)).trans
      ((keep_u₃_x rOne (by decide) (by decide)).trans ho)
  have hu₆_d : u₆.regs rDim = d := by
    simpa [u₆] using (keep_u₅ rDim (by decide) (by decide)).trans hu₃_d
  have hu₆_dp : u₆.regs rCurDomPtr = domPtr := by
    simpa [u₆] using (keep_u₅ rCurDomPtr (by decide) (by decide)).trans
      ((keep_u₃_x rCurDomPtr (by decide) (by decide)).trans hdp)
  have hu₆_dl : u₆.regs rCurDomLen = dom.length := by
    simpa [u₆] using (keep_u₅ rCurDomLen (by decide) (by decide)).trans
      ((keep_u₃_x rCurDomLen (by decide) (by decide)).trans hdl)
  have hu₆_cut : u₆.regs rStageCutoff = cutoff := by
    simpa [u₆] using (keep_u₅ rStageCutoff (by decide) (by decide)).trans
      ((keep_u₃_x rStageCutoff (by decide) (by decide)).trans hcut)
  obtain ⟨y, endFree, he_stH, hy_ro, hy_free, hlo₄, hhi₄, hstH, hfr₄, hreg_y⟩ :=
    exec_stagesCode (initRoot := free₂) (fbBase := preHs) (signMode := 1)
      (P_low := P_low) (G := H) (B₀ := 4 ^ d * W ^ 2) (B := B) u₆
      hu₆_z hu₆_o hu₆_d hu₆_dp hu₆_dl hu₆_cut
      (by simp [u₆]) (by simp [u₆]) (by simp [u₆])
      (by simp [u₆, hu₅_free]) (by omega)
      hnd hdom_u₆ (by omega) hdom_closed htr_h0 heq_h0 hfbH_u₆
      hH_le hB_H hfit_B (hfit_free.of_le (by dsimp [tripleSpace] at *; omega)) hfit_mask
  have htot : ExecWithin w runTransformTriple x y (tripleTime d dom.length) :=
    (he₀.seq (he_stF.seq (he₂.seq (he_stG.seq (he₄.seq (he_mul.seq (he₆.seq he_stH))))))).mono
      (by dsimp [tripleTime]; omega)
  have hy_qFs : y.regs rQFsBase = free := by
    rw [hreg_y rQFsBase (by decide)]
    simpa [u₆] using (keep_u₅ rQFsBase (by decide) (by decide)).trans hu₃_qFs
  have hy_qGs : y.regs rQGsBase = free₁ := by
    rw [hreg_y rQGsBase (by decide)]
    simpa [u₆] using (hreg₅ rQGsBase (by decide)).trans hu₄_qGs
  have y_eq_u₃ : ∀ a < free₂, y.mem a = u₃.mem a := fun a ha => by
    rw [hfr₄ a (Or.inl (by omega))]
    change u₅.mem a = u₃.mem a
    rw [hfr₃ a (Or.inl ha), hu₄_mem]
  have y_eq_u₁ : ∀ a < free₁, y.mem a = u₁.mem a := fun a ha => by
    rw [y_eq_u₃ a (by omega), hfr₂ a (Or.inl ha)]
    rfl
  refine ⟨y, free, free₁, free₃, endFree, htot, hy_qFs, hy_qGs, hy_ro, hy_free,
    by omega, by dsimp [tripleSpace]; omega, by omega, by omega, by omega,
    ?_, ?_, hstH, ?_, ?_, fun i hi => htot.regs_eq (runTransformTriple_preserves i hi)⟩
  · intro k hk
    obtain ⟨stFn, htr, heq⟩ := hstF k hk
    rw [y_eq_u₁ (free + k) (by omega)]
    exact ⟨stFn, (htr.congr_below fun a ha => y_eq_u₁ a ha).mono_bound (by omega), heq⟩
  · intro k hk
    obtain ⟨stFn, htr, heq⟩ := hstG k hk
    rw [y_eq_u₃ (free₁ + k) (by omega)]
    exact ⟨stFn, (htr.congr_below fun a ha => y_eq_u₃ a ha).mono_bound (by omega), heq⟩
  · obtain ⟨outFn, htr, heq⟩ := hstH d le_rfl
    refine ⟨outFn, htr, fun X hX => ?_⟩
    rw [heq X hX]
    congr 1
    have htake : (List.finRange d).take d = List.finRange d := by simp
    simp only [one_ne_zero, ↓reduceIte]
    rw [htake, yatesTransform_neg_one_apply (List.nodup_finRange d) H (by intro i _; simp),
      coveringProduct_eq_subsetMobius]
  · intro a ha
    rcases ha with ha_lo | ha_hi
    · rw [y_eq_u₁ a (by omega), hfr₁ a (Or.inl ha_lo)]
      rfl
    · rw [hfr₄ a (Or.inr ha_hi)]
      change u₅.mem a = x.mem a
      rw [hfr₃ a (Or.inr (by omega)), hu₄_mem, hfr₂ a (Or.inr (by omega))]
      change u₁.mem a = x.mem a
      rw [hfr₁ a (Or.inr (by omega))]
      rfl

/-! ### `solveFromTries`: preprocessing and query loop from pre-built input tries -/

private theorem solveSpace_split {baseFree d s nQ L_low H_pk : ℕ} (hL : lowCount d s = L_low) :
    baseFree + (d + 2 * L_low + tripleSpace d L_low) + 1 + nQ +
      (d + 2 * max 1 H_pk + tripleSpace d (max 1 H_pk)) ≤
      solveSpace baseFree d s nQ H_pk := by
  have ht1 := tripleSpace_le d L_low
  have ht2 := tripleSpace_le d (max 1 H_pk)
  have hhp : max 1 H_pk ≤ H_pk + 1 := by omega
  have hsq : 1 ≤ (d + 1) ^ 2 := Nat.one_le_pow 2 (d + 1) (Nat.succ_pos d)
  dsimp only [solveSpace]
  rw [hL]
  generalize (d + 1) ^ 2 = sqVal at ht1 ht2 hsq ⊢
  nlinarith

private theorem tripleSpace_mono {d a b : ℕ} (hab : a ≤ b) :
    tripleSpace d a ≤ tripleSpace d b := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
  dsimp only [tripleSpace]
  have hid :
      (3 * (d + 1 + d * (2 * d * a + 2)) + (2 + 2 * d * a)) + k * (6 * d ^ 2 + 2 * d) =
      3 * (d + 1 + d * (2 * d * (a + k) + 2)) + (2 + 2 * d * (a + k)) := by ring
  omega

private theorem shortBranch_budget_le {d H_pos : ℕ} (hH : 1 ≤ H_pos) {n_b : ℕ}
    (hn : n_b ≤ 2 + (9 * d + 8)) :
    n_b + 1 ≤ 180 * (d + 1) ^ 2 * H_pos - (5 + (11 * d + 5) + 3) := by
  have hpt := phaseTime_le (d := d) hH
  dsimp only [tripleTime] at hpt
  rw [sq] at hpt ⊢
  omega

private theorem longBranch_budget_le {d cl H_q H_pos : ℕ} (hH : 1 ≤ H_pos)
    (hcl : cl ≤ d) (hHq : H_q ≤ H_pos) {n_el : ℕ}
    (hn : n_el ≤ 2 + (cl * (20 * H_q + 12) + 8 +
      (12 * H_q + 3 + (5 + (tripleTime d H_q + (4 + (9 * d + 8))))))) :
    n_el + 2 ≤ 180 * (d + 1) ^ 2 * H_pos - (5 + (11 * d + 5) + 3) := by
  have hpt := phaseTime_le (d := d) hH
  have hcl_le : cl * (20 * H_q + 12) ≤ d * (20 * H_pos + 12) :=
    Nat.mul_le_mul hcl (by omega)
  have htr_le : tripleTime d H_q ≤ tripleTime d H_pos := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hHq
    dsimp only [tripleTime]
    have hid :
        (3 * (d * (H_q * (32 * d + 63) + 22) + 7) + (H_q * (32 * d + 53) + 9) + 15) +
        k * (96 * d ^ 2 + 221 * d + 53) =
        3 * (d * ((H_q + k) * (32 * d + 63) + 22) + 7) +
          ((H_q + k) * (32 * d + 53) + 9) + 15 := by ring
    omega
  omega

private theorem queryStep_base_le {d H_pos : ℕ} (hH : 1 ≤ H_pos) :
    5 + (11 * d + 5) + 3 ≤ 180 * (d + 1) ^ 2 * H_pos := by
  have hpt := phaseTime_le (d := d) hH
  dsimp only [tripleTime] at hpt
  omega

private theorem solve_total_time_le {d nQ L_low H_pos : ℕ} (hL : 1 ≤ L_low) (hH : 1 ≤ H_pos) :
    4 + (5 * d + 3 + (3 + (d * (20 * L_low + 12) + 8 +
      (5 + (tripleTime d L_low + (8 + (nQ * (180 * (d + 1) ^ 2 * H_pos + 2) + 2))))))) ≤
      200 * (d + 1) ^ 2 * (L_low + nQ * H_pos) := by
  have hpre := phaseTime_le (d := d) hL
  have hsq_pos : 1 ≤ (d + 1) ^ 2 := Nat.one_le_pow 2 (d + 1) (Nat.succ_pos d)
  have hq_step : nQ * (180 * (d + 1) ^ 2 * H_pos + 2) ≤
      nQ * (200 * (d + 1) ^ 2 * H_pos) :=
    Nat.mul_le_mul_left nQ (by nlinarith)
  nlinarith

private def qLoadCode : Code .standard numRegs := ram[
  rFree ← rPreFree;
  rGenTmp ← rQueryPtr + rQueryIdx;
  rTrieKey ← *rGenTmp;
  rCoordsPtr ← rFree;
  rFree ← rFree + rDim ]

private theorem qLoadCode_preserves (i : Fin numRegs) :
    i ≠ rFree ∧ i ≠ rGenTmp ∧ i ≠ rTrieKey ∧ i ≠ rCoordsPtr → qLoadCode.Preserves i := by
  decide +kernel +revert

private def qShortLoadCode : Code .standard numRegs := ram[
  rGenTmp ← rPreHsBase + rDim;
  rTrieRoot ← *rGenTmp ]

private theorem qShortLoadCode_preserves (i : Fin numRegs) :
    i ≠ rGenTmp ∧ i ≠ rTrieRoot → qShortLoadCode.Preserves i := by
  decide +kernel +revert

private def qHighPrepCode : Code .standard numRegs := ram[
  rCurDomPtr ← rDomPtr;
  rCurDomLen ← rDomLen;
  rGenTmp ← rDomLen + rDomLen;
  rFree ← rDomPtr + rGenTmp;
  rStageCutoff ← rThresh ]

private theorem qHighPrepCode_preserves (i : Fin numRegs) :
    i ≠ rCurDomPtr ∧ i ≠ rCurDomLen ∧ i ≠ rGenTmp ∧ i ≠ rFree ∧ i ≠ rStageCutoff →
      qHighPrepCode.Preserves i := by
  decide +kernel +revert

private def qHighReadCode : Code .standard numRegs := ram[
  rGenTmp ← rQueryPtr + rQueryIdx;
  rTrieKey ← *rGenTmp;
  rGenTmp ← rRootsOut + rDim;
  rTrieRoot ← *rGenTmp ]

private theorem qHighReadCode_preserves (i : Fin numRegs) :
    i ≠ rGenTmp ∧ i ≠ rTrieKey ∧ i ≠ rTrieRoot → qHighReadCode.Preserves i := by
  decide +kernel +revert

private def qBranchCode : Code .standard numRegs :=
  .branch (.lt rCoordsLen rThresh)
    (.seq qShortLoadCode trieGet)
    (.seq (ram[ rMaxCard ← rCoordsLen - rThresh; rDomPtr ← rFree ])
      (.seq genLowSubsets
        (.seq flipHighDom
          (.seq qHighPrepCode
            (.seq runTransformTriple
              (.seq qHighReadCode trieGet))))))

private theorem qBranchCode_preserves_one : qBranchCode.Preserves rOne := by decide +kernel
private theorem qBranchCode_preserves_out : qBranchCode.Preserves rOutPtr := by decide +kernel
private theorem qBranchCode_preserves_qi : qBranchCode.Preserves rQueryIdx := by decide +kernel

private def qWriteCode : Code .standard numRegs := ram[
  rQueryIdx ← rQueryIdx + rOne;
  rGenTmp ← rOutPtr + rQueryIdx;
  *rGenTmp ← rTrieVal ]

private def queryStep : Code .standard numRegs :=
  .seq qLoadCode (.seq extractCoords (.seq qBranchCode qWriteCode))

private abbrev IsQueryKept (i : Fin numRegs) : Prop :=
  i = rZero ∨ i = rOne ∨ i = rDim ∨ i = rThresh ∨ i = rOutPtr ∨ i = rPreFree ∨
    i = rTrieF ∨ i = rTrieG ∨ i = rQueryPtr ∨ i = rQueryCount ∨
    i = rPreFsBase ∨ i = rPreGsBase ∨ i = rPreHsBase

private theorem queryStep_preserves (i : Fin numRegs) :
    IsQueryKept i → queryStep.Preserves i := by
  decide +kernel +revert

private def preSaveCode : Code .standard numRegs := ram[
  rPreFsBase ← rQFsBase;
  rPreGsBase ← rQGsBase;
  rPreHsBase ← rRootsOut;
  rOutPtr ← rFree;
  *rOutPtr ← rQueryCount;
  rPreFree ← rFree + rOne;
  rPreFree ← rPreFree + rQueryCount;
  rQueryIdx ← #0 ]

private theorem preSaveCode_preserves (i : Fin numRegs) :
    i ≠ rPreFsBase ∧ i ≠ rPreGsBase ∧ i ≠ rPreHsBase ∧
      i ≠ rOutPtr ∧ i ≠ rPreFree ∧ i ≠ rQueryIdx → preSaveCode.Preserves i := by
  decide +kernel +revert

/-- Answer all queries in `Reg.queryPtr[0 .. Reg.queryCount - 1]` from pre-built depth-`Reg.dim`
tries `Reg.trieF` and `Reg.trieG`, allocating preprocessing tables and the length-prefixed answer
array above `Reg.free` (returning the answer array header address in `Reg.outPtr`). -/
def solveFromTries : Code .standard numRegs :=
  .seq (ram[
    rZero ← #0;
    rOne ← #1;
    rCoordsPtr ← rFree;
    rFree ← rFree + rDim ])
  (.seq initIdentityCoords
    (.seq (ram[
        rCoordsLen ← rDim;
        rMaxCard ← rThresh;
        rDomPtr ← rFree ])
      (.seq genLowSubsets
        (.seq (ram[
            rCurDomPtr ← rDomPtr;
            rCurDomLen ← rDomLen;
            rGenTmp ← rDomLen + rDomLen;
            rFree ← rDomPtr + rGenTmp;
            rStageCutoff ← #0 ])
          (.seq runTransformTriple
            (.seq preSaveCode
              (.loop (.lt rQueryIdx rQueryCount) queryStep)))))))

private def solvePreStageCode : Code .standard numRegs := ram[
  rCurDomPtr ← rDomPtr;
  rCurDomLen ← rDomLen;
  rGenTmp ← rDomLen + rDomLen;
  rFree ← rDomPtr + rGenTmp;
  rStageCutoff ← #0 ]

private theorem solvePreStageCode_preserves (i : Fin numRegs) :
    i ≠ rCurDomPtr ∧ i ≠ rCurDomLen ∧ i ≠ rGenTmp ∧ i ≠ rFree ∧ i ≠ rStageCutoff →
      solvePreStageCode.Preserves i := by
  decide +kernel +revert

private theorem HoldsTrie.congr_root {mem : ℕ → ℕ} {bound d r₁ r₂ : ℕ} {fn : ℕ → ℕ}
    (hr : r₁ = r₂) (h : HoldsTrie mem bound d r₂ fn) : HoldsTrie mem bound d r₁ fn :=
  hr ▸ h

private theorem exec_qLongBranch {w d s baseFree outBase qWorkStart rootF rootG qPtr q
    preFs preGs preHs W H_pos spVal : ℕ}
    {fnF fnG : ℕ → ℕ} {f g : Finset (Fin d) → ℤ}
    {C : Finset (Fin d)} {cList : List (Fin d)}
    {initMem preMem stMem : ℕ → ℕ}
    (u₁ : Data numRegs)
    (hz : u₁.regs rZero = 0) (ho : u₁.regs rOne = 1) (hd : u₁.regs rDim = d)
    (hs_reg : u₁.regs rThresh = s) (hkey : u₁.regs rTrieKey = setMask C)
    (hcp : u₁.regs rCoordsPtr = qWorkStart) (hclen : u₁.regs rCoordsLen = #C)
    (hfr : u₁.regs rFree = qWorkStart + d)
    (htF_reg : u₁.regs rTrieF = rootF) (htG_reg : u₁.regs rTrieG = rootG)
    (hqp : u₁.regs rQueryPtr = qPtr) (hqi : u₁.regs rQueryIdx = q)
    (hpFs : u₁.regs rPreFsBase = preFs) (hpGs : u₁.regs rPreGsBase = preGs)
    (hpHs : u₁.regs rPreHsBase = preHs)
    (hcList_nd : cList.Nodup) (hcList_tf : cList.toFinset = C)
    (hcList_len : cList.length = #C)
    (hcmem : ∀ j (hj : j < cList.length), u₁.mem (qWorkStart + j) = cList[j].val)
    (hu₁_below_qw : ∀ a < qWorkStart, u₁.mem a = stMem a)
    (hs_pre : ∀ a < outBase, stMem a = preMem a)
    (hpre_below_bf : ∀ a < baseFree, preMem a = initMem a)
    (hob_gt_bf : baseFree < outBase) (hob_le_qw : outBase < qWorkStart)
    (hq_lt : qPtr + q < qWorkStart) (hread_q : stMem (qPtr + q) = setMask C)
    (htrieF : HoldsTrie initMem baseFree d rootF fnF)
    (htrieG : HoldsTrie initMem baseFree d rootG fnG)
    (hf_eq : ∀ S : Finset (Fin d), fnF (setMask S) = Signed.encode (f S))
    (hg_eq : ∀ S : Finset (Fin d), fnG (setMask S) = Signed.encode (g S))
    (hf_le : ∀ S, (f S).natAbs ≤ W) (hg_le : ∀ S, (g S).natAbs ≤ W)
    (hpFs_lt : preFs + d < outBase) (hpGs_lt : preGs + d < outBase)
    (hpHs_lt : preHs + d < outBase)
    (hpreF_st : ∀ k ≤ d, ∃ stFn, HoldsTrie preMem outBase d (preMem (preFs + k)) stFn ∧
      ∀ Y : Finset (Fin d), #Y ≤ s →
        stFn (setMask Y) = Signed.encode (yatesTransform (1 : ℤ) ((List.finRange d).take k) f Y))
    (hpreG_st : ∀ k ≤ d, ∃ stFn, HoldsTrie preMem outBase d (preMem (preGs + k)) stFn ∧
      ∀ Y : Finset (Fin d), #Y ≤ s →
        stFn (setMask Y) = Signed.encode (yatesTransform (1 : ℤ) ((List.finRange d).take k) g Y))
    (hpreH_st : ∀ k ≤ d, ∃ stFn, HoldsTrie preMem outBase d (preMem (preHs + k)) stFn ∧
      ∀ Y : Finset (Fin d), #Y ≤ s →
        stFn (setMask Y) = Signed.encode (yatesTransform (-1 : ℤ) ((List.finRange d).take k)
          (fun S => subsetZeta f S * subsetZeta g S) Y))
    (hsC : s ≤ #C) (hH_pos1 : 1 ≤ H_pos) (hC_H : highCount #C s ≤ H_pos)
    (hqw_bound : qWorkStart + (d + 2 * H_pos + tripleSpace d H_pos) ≤ spVal)
    (hfit_space : Fits w spVal) (hfit_val : Fits w (valueEnvelope d W)) :
    ∃ u_ans,
      ExecWithin w qBranchCode u₁ u_ans
        (180 * (d + 1) ^ 2 * H_pos - (5 + (11 * d + 5) + 3)) ∧
      u_ans.regs rTrieVal = Signed.encode (coveringProduct f g C) ∧
      (∀ a < qWorkStart, u_ans.mem a = stMem a) := by
  have hfit_mask : Fits w (2 ^ d) := mask_fits_of_valueEnvelope hfit_val
  have hfit_d : Fits w d := hfit_mask.of_le Nat.lt_two_pow_self.le
  have hlt_Cs : ¬ #C < s := Nat.not_lt_of_ge hsC
  have hcond : ¬ (Cond.lt rCoordsLen rThresh).Holds u₁ := by
    simp [Cond.holds_lt, hclen, hs_reg, hlt_Cs]
  let highDomBase := qWorkStart + d
  have hf_sub : Fits w (#C - s) :=
    hfit_d.of_le ((by have := Finset.card_le_univ C; simp at this; omega : #C - s ≤ d))
  have hw0_st : ∃ w₀, ExecWithin (B := .standard) w
      (ram[ rMaxCard ← rCoordsLen - rThresh; rDomPtr ← rFree ]) u₁ w₀ 2 ∧
      w₀.regs rZero = 0 ∧ w₀.regs rOne = 1 ∧ w₀.regs rThresh = s ∧
      w₀.regs rTrieKey = setMask C ∧ w₀.regs rCoordsPtr = qWorkStart ∧
      w₀.regs rCoordsLen = #C ∧ w₀.regs rMaxCard = #C - s ∧
      w₀.regs rDomPtr = highDomBase ∧ w₀.regs rDim = d ∧
      w₀.regs rTrieF = rootF ∧ w₀.regs rTrieG = rootG ∧
      w₀.regs rQueryPtr = qPtr ∧ w₀.regs rQueryIdx = q ∧
      w₀.regs rPreFsBase = preFs ∧ w₀.regs rPreGsBase = preGs ∧
      w₀.regs rPreHsBase = preHs ∧ w₀.mem = u₁.mem := by
    wram_exec [hclen, hs_reg, hfr]
    wram_simp [hz, ho, hs_reg, hkey, hcp, hclen, hd, htF_reg, htG_reg, hqp, hqi,
      hpFs, hpGs, hpHs, highDomBase]
  obtain ⟨w₀, he_w0, hw₀z, hw₀o, hw₀s, hw₀key, hw₀cp, hw₀cl, hw₀mc, hw₀dp,
    hw₀d, hw₀tF, hw₀tG, hw₀qp, hw₀qi, hw₀pFs, hw₀pGs, hw₀pHs, hw₀mem⟩ := hw0_st
  obtain ⟨H_q, hHq_def⟩ : ∃ H_q, highCount #C s = H_q := ⟨_, rfl⟩
  have hHq_le : H_q ≤ H_pos := hHq_def ▸ hC_H
  have hts_mono : tripleSpace d H_q ≤ tripleSpace d H_pos := tripleSpace_mono hHq_le
  have hsum_Hq : ∑ j ∈ range (#C - s + 1), cList.length.choose j = H_q := by
    rw [hcList_len, sum_range_sub_eq_highCount hsC, hHq_def]
  clear hHq_def
  have hcList_le_d : cList.length ≤ d := by
    rw [hcList_len]; simpa using Finset.card_le_univ C
  obtain ⟨w₁, he_ghigh_raw, hw₁_dlen, hw₁_dom, hw₁_fr, hw₁_regs⟩ :=
    exec_genLowSubsets cList w₀ hw₀z hw₀o hw₀cp (hw₀cl.trans hcList_len.symm)
      hw₀mc hw₀dp hcList_nd (by rwa [hw₀mem]) (by dsimp only [highDomBase]; omega)
      (by rw [hsum_Hq]; exact hfit_space.of_le (by dsimp only [highDomBase]; omega))
      hfit_mask
  have he_ghigh : ExecWithin w genLowSubsets w₀ w₁ (cList.length * (20 * H_q + 12) + 8) := by
    rwa [hsum_Hq] at he_ghigh_raw
  clear he_ghigh_raw
  have hys_len_raw : (prefixesUpTo (#C - s) cList).length = H_q := by
    rw [length_prefixesUpTo (#C - s) hcList_nd, hsum_Hq]
  clear hsum_Hq
  have hys_spec_raw := prefixesUpTo_spec (#C - s) hcList_nd
  generalize hys_def : prefixesUpTo (#C - s) cList = ys
    at hw₁_dlen hw₁_dom hys_len_raw hys_spec_raw
  have hys_len : ys.length = H_q := hys_len_raw
  have hys_spec := hys_spec_raw
  have hys_sub : ∀ Y ∈ ys, Y ⊆ C := by
    intro Y hY
    have hsub := ((hys_spec.2 Y).mp hY).1
    rwa [hcList_tf] at hsub
  obtain ⟨w₂, he_flip, hw₂_dom, hw₂_fr, hw₂_regs⟩ :=
    exec_flipHighDom C ys w₁
      ((hw₁_regs rOne (by decide)).trans hw₀o)
      ((hw₁_regs rTrieKey (by decide)).trans hw₀key)
      ((hw₁_regs rCoordsLen (by decide)).trans hw₀cl)
      ((hw₁_regs rDomPtr (by decide)).trans hw₀dp)
      hw₁_dlen hys_sub hw₁_dom
      (by rw [hys_len]; exact hfit_space.of_le (by dsimp only [highDomBase]; omega))
      hfit_mask
  have hhigh_len_raw : (ys.map (C \ ·)).length = H_q := by simp [hys_len]
  have hhigh_nd_raw : (ys.map (C \ ·)).Nodup := by
    refine hys_spec.1.map_on fun Y₁ h₁ Y₂ h₂ heq => ?_
    have h₁C := hys_sub Y₁ h₁
    have h₂C := hys_sub Y₂ h₂
    calc Y₁ = C \ (C \ Y₁) := (Finset.sdiff_sdiff_eq_self h₁C).symm
      _ = C \ (C \ Y₂) := by rw [heq]
      _ = Y₂ := Finset.sdiff_sdiff_eq_self h₂C
  have hhigh_mem_raw : ∀ X, X ∈ ys.map (C \ ·) ↔ X ⊆ C ∧ s ≤ #X := by
    intro X
    simp only [List.mem_map]
    constructor
    · rintro ⟨Y, hY, rfl⟩
      have hYC := hys_sub Y hY
      have hYcard := ((hys_spec.2 Y).mp hY).2
      rw [Finset.card_sdiff_of_subset hYC]
      exact ⟨sdiff_subset, by omega⟩
    · rintro ⟨hXC, hsX⟩
      refine ⟨C \ X, (hys_spec.2 _).mpr ⟨?_, ?_⟩, Finset.sdiff_sdiff_eq_self hXC⟩
      · rw [hcList_tf]; exact sdiff_subset
      · rw [Finset.card_sdiff_of_subset hXC]; omega
  generalize hhigh_def : ys.map (C \ ·) = highDom
    at hw₂_dom hhigh_len_raw hhigh_nd_raw hhigh_mem_raw
  have hhigh_len : highDom.length = H_q := hhigh_len_raw
  have hhigh_nd : highDom.Nodup := hhigh_nd_raw
  have hhigh_mem_iff : ∀ X, X ∈ highDom ↔ X ⊆ C ∧ s ≤ #X := hhigh_mem_raw
  let qTrStart := highDomBase + 2 * H_q
  have hf_2Hq : Fits w (H_q + H_q) := hfit_space.of_le (by omega)
  have hf_qts : Fits w (highDomBase + (H_q + H_q)) :=
    hfit_space.of_le (by dsimp only [highDomBase]; omega)
  have hw₂_dp : w₂.regs rDomPtr = highDomBase :=
    (hw₂_regs rDomPtr (by decide)).trans ((hw₁_regs rDomPtr (by decide)).trans hw₀dp)
  have hw₂_dl : w₂.regs rDomLen = H_q := by
    rw [hw₂_regs rDomLen (by decide), hw₁_dlen, hys_len]
  have hw₂_s : w₂.regs rThresh = s :=
    (hw₂_regs rThresh (by decide)).trans ((hw₁_regs rThresh (by decide)).trans hw₀s)
  have hst3 : ∃ w₃, ExecWithin w qHighPrepCode w₂ w₃ 5 ∧
      w₃.regs rCurDomPtr = highDomBase ∧ w₃.regs rCurDomLen = highDom.length ∧
      w₃.regs rFree = qTrStart ∧ w₃.regs rStageCutoff = s ∧ w₃.mem = w₂.mem := by
    unfold qHighPrepCode
    wram_exec [hw₂_dp, hw₂_dl, hw₂_s]
    refine ⟨rfl, hhigh_len.symm, ?_, rfl, rfl⟩
    wram_simp [qTrStart]; omega
  obtain ⟨w₃, he_w3, hw₃_cdp, hw₃_cdl, hw₃_fr, hw₃_cut, hw₃_mem⟩ := hst3
  have hw₃_regs : ∀ i,
      i ≠ rCurDomPtr ∧ i ≠ rCurDomLen ∧ i ≠ rGenTmp ∧ i ≠ rFree ∧ i ≠ rStageCutoff →
        w₃.regs i = w₂.regs i :=
    fun i hi => he_w3.regs_eq (qHighPrepCode_preserves i hi)
  have w₃_below_qw : ∀ a < qWorkStart, w₃.mem a = stMem a := fun a ha => by
    rw [hw₃_mem, hw₂_fr a (Or.inl (by dsimp only [highDomBase]; omega)),
      hw₁_fr a (Or.inl (by dsimp only [highDomBase]; omega)), hw₀mem]
    exact hu₁_below_qw a ha
  have w₃_below_ob : ∀ a < outBase, w₃.mem a = preMem a := fun a ha =>
    (w₃_below_qw a (by omega)).trans (hs_pre a ha)
  have w₃_below_bf : ∀ a < baseFree, w₃.mem a = initMem a := fun a ha =>
    (w₃_below_ob a (by omega)).trans (hpre_below_bf a ha)
  have hhigh_closed : ∀ X ∈ highDom, ∀ coord : Fin d, coord ∈ X →
      (s ≤ #(X.erase coord) → X.erase coord ∈ highDom) ∧
      (#(X.erase coord) < s → #(X.erase coord) ≤ s) := by
    intro X hX coord _
    have hXC := ((hhigh_mem_iff X).mp hX).1
    exact ⟨fun hge => (hhigh_mem_iff _).mpr ⟨(erase_subset _ _).trans hXC, hge⟩,
      fun _ => by omega⟩
  have hfb_q : 0 < s →
      preFs + d ≤ qTrStart ∧ preGs + d ≤ qTrStart ∧ preHs + d ≤ qTrStart ∧
      (∀ k < d, ∃ fbFn, HoldsTrie w₃.mem qTrStart d (w₃.mem (preFs + k)) fbFn ∧
        ∀ Y, #Y < s → #Y ≤ s →
          fbFn (setMask Y) =
            Signed.encode (yatesTransform (1 : ℤ) ((List.finRange d).take k) f Y)) ∧
      (∀ k < d, ∃ fbFn, HoldsTrie w₃.mem qTrStart d (w₃.mem (preGs + k)) fbFn ∧
        ∀ Y, #Y < s → #Y ≤ s →
          fbFn (setMask Y) =
            Signed.encode (yatesTransform (1 : ℤ) ((List.finRange d).take k) g Y)) ∧
      (∀ k < d, ∃ fbFn, HoldsTrie w₃.mem qTrStart d (w₃.mem (preHs + k)) fbFn ∧
        ∀ Y, #Y < s → #Y ≤ s →
          fbFn (setMask Y) =
            Signed.encode (yatesTransform (-1 : ℤ) ((List.finRange d).take k)
              (fun S => subsetZeta f S * subsetZeta g S) Y)) := by
    intro _
    have hlt_qts : outBase ≤ qTrStart := by dsimp only [qTrStart, highDomBase]; omega
    refine ⟨by omega, by omega, by omega, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
    · obtain ⟨fbFn, htr, heq⟩ := hpreF_st k hk.le
      exact ⟨fbFn,
        ((htr.congr_below w₃_below_ob).mono_bound hlt_qts).congr_root
          (w₃_below_ob (preFs + k) (by omega)),
        fun Y _ hYle => heq Y hYle⟩
    · obtain ⟨fbFn, htr, heq⟩ := hpreG_st k hk.le
      exact ⟨fbFn,
        ((htr.congr_below w₃_below_ob).mono_bound hlt_qts).congr_root
          (w₃_below_ob (preGs + k) (by omega)),
        fun Y _ hYle => heq Y hYle⟩
    · obtain ⟨fbFn, htr, heq⟩ := hpreH_st k hk.le
      exact ⟨fbFn,
        ((htr.congr_below w₃_below_ob).mono_bound hlt_qts).congr_root
          (w₃_below_ob (preHs + k) (by omega)),
        fun Y _ hYle => heq Y hYle⟩
  have kw₃_w₀ (i : Fin numRegs)
      (h3 : i ≠ rCurDomPtr ∧ i ≠ rCurDomLen ∧ i ≠ rGenTmp ∧ i ≠ rFree ∧ i ≠ rStageCutoff)
      (h2 : i ≠ rTrieTmp ∧ i ≠ rGenPos ∧ i ≠ rGenTmp)
      (h1g : i ≠ rTrieTmp ∧ i ≠ rCellSaved ∧ (i.val < 27 ∨ 33 ≤ i.val)) :
      w₃.regs i = w₀.regs i :=
    (hw₃_regs i h3).trans ((hw₂_regs i h2).trans (hw₁_regs i h1g))
  obtain ⟨w₄, _, _, qHs, qEndFree, he_qtr, _, _, hw₄_ro, _, _, hqef_hi,
    _, _, hqHs_lt, _, _, _, ⟨qOutFn, hqOut_tr, hqOut_eq⟩, hw₄_frame, hw₄_regs⟩ :=
    exec_runTransformTriple (P_low := fun Y => #Y ≤ s) (W := W) w₃
      ((kw₃_w₀ rZero (by decide) (by decide) (by decide)).trans hw₀z)
      ((kw₃_w₀ rOne (by decide) (by decide) (by decide)).trans hw₀o)
      ((kw₃_w₀ rDim (by decide) (by decide) (by decide)).trans hw₀d)
      hw₃_cdp hw₃_cdl hw₃_cut
      ((kw₃_w₀ rTrieF (by decide) (by decide) (by decide)).trans hw₀tF)
      ((kw₃_w₀ rTrieG (by decide) (by decide) (by decide)).trans hw₀tG)
      ((kw₃_w₀ rPreFsBase (by decide) (by decide) (by decide)).trans hw₀pFs)
      ((kw₃_w₀ rPreGsBase (by decide) (by decide) (by decide)).trans hw₀pGs)
      ((kw₃_w₀ rPreHsBase (by decide) (by decide) (by decide)).trans hw₀pHs)
      hw₃_fr (by dsimp only [qTrStart, highDomBase]; omega)
      hhigh_nd (by rwa [hw₃_mem]) (by rw [hhigh_len]) hhigh_closed
      ((htrieF.congr_below w₃_below_bf).mono_bound (by dsimp only [qTrStart, highDomBase]; omega))
      ((htrieG.congr_below w₃_below_bf).mono_bound (by dsimp only [qTrStart, highDomBase]; omega))
      hf_eq hg_eq hf_le hg_le hfb_q hfit_val
      (by
        rw [hhigh_len]
        refine hfit_space.of_le ?_
        dsimp only [qTrStart, highDomBase]
        omega)
  have hw₄_qp : w₄.regs rQueryPtr = qPtr :=
    (hw₄_regs rQueryPtr (by decide)).trans
      ((kw₃_w₀ rQueryPtr (by decide) (by decide) (by decide)).trans hw₀qp)
  have hw₄_qi : w₄.regs rQueryIdx = q :=
    (hw₄_regs rQueryIdx (by decide)).trans
      ((kw₃_w₀ rQueryIdx (by decide) (by decide) (by decide)).trans hw₀qi)
  have hw₄_d : w₄.regs rDim = d :=
    (hw₄_regs rDim (by decide)).trans
      ((kw₃_w₀ rDim (by decide) (by decide) (by decide)).trans hw₀d)
  have hw₄_below_qw : ∀ a < qWorkStart, w₄.mem a = stMem a := fun a ha =>
    (hw₄_frame a (Or.inl (by dsimp only [qTrStart, highDomBase]; omega))).trans
      (w₃_below_qw a ha)
  have hw₄_read_q : w₄.mem (qPtr + q) = setMask C := by
    rw [hw₄_below_qw _ hq_lt]; exact hread_q
  have hf_qef : Fits w qEndFree := by
    rw [hhigh_len] at hqef_hi
    exact hfit_space.of_le (by dsimp only [qTrStart, highDomBase] at hqef_hi; omega)
  have hf_qhs_d : Fits w (qHs + d) := hf_qef.of_le (by omega)
  have hst5 : ∃ w₅, ExecWithin w qHighReadCode w₄ w₅ 4 ∧
      w₅.regs rTrieKey = setMask C ∧ w₅.regs rTrieRoot = w₄.mem (qHs + d) ∧
      w₅.mem = w₄.mem := by
    unfold qHighReadCode
    wram_exec [hw₄_qp, hw₄_qi, hw₄_ro, hw₄_d, hw₄_read_q]
    wram_simp [hw₄_read_q]
  obtain ⟨w₅, he_w5, hw₅_key, hw₅_root, hw₅_mem⟩ := hst5
  have hw₅_regs : ∀ i, i ≠ rGenTmp ∧ i ≠ rTrieKey ∧ i ≠ rTrieRoot →
      w₅.regs i = w₄.regs i :=
    fun i hi => he_w5.regs_eq (qHighReadCode_preserves i hi)
  obtain ⟨w₆, he_get, hw₆_val, hw₆_mem, _⟩ :=
    exec_trieGet w₅
      ((hw₅_regs rZero (by decide)).trans ((hw₄_regs rZero (by decide)).trans
        ((kw₃_w₀ rZero (by decide) (by decide) (by decide)).trans hw₀z)))
      ((hw₅_regs rOne (by decide)).trans ((hw₄_regs rOne (by decide)).trans
        ((kw₃_w₀ rOne (by decide) (by decide) (by decide)).trans hw₀o)))
      ((hw₅_regs rDim (by decide)).trans hw₄_d)
      hw₅_root hw₅_key (by rwa [hw₅_mem]) hf_qef hfit_d (hfit_mask.of_le (setMask_lt C).le)
  rw [hqOut_eq C ((hhigh_mem_iff C).mpr ⟨subset_rfl, hsC⟩)] at hw₆_val
  have helse_ex := he_w0.seq (he_ghigh.seq (he_flip.seq (he_w3.seq
    (he_qtr.seq (he_w5.seq he_get)))))
  obtain ⟨n_el, hn_el, hex_el⟩ := helse_ex
  rw [hys_len, hhigh_len] at hn_el
  refine ⟨w₆, ⟨n_el + 2, longBranch_budget_le hH_pos1 hcList_le_d hHq_le hn_el,
    Exec.branch_neg hcond hex_el⟩, hw₆_val,
    fun a ha => (congrFun (hw₆_mem.trans hw₅_mem) a).trans (hw₄_below_qw a ha)⟩

private def QueryInv {d : ℕ} (s outBase rootF rootG qPtr preFs preGs preHs : ℕ)
    (f g : Finset (Fin d) → ℤ) (Cs : List (Finset (Fin d))) (preMem : ℕ → ℕ)
    (q : ℕ) (st : Data numRegs) : Prop :=
  st.regs rZero = 0 ∧ st.regs rOne = 1 ∧ st.regs rDim = d ∧ st.regs rThresh = s ∧
  st.regs rOutPtr = outBase ∧ st.regs rPreFree = outBase + 1 + Cs.length ∧
  st.regs rTrieF = rootF ∧ st.regs rTrieG = rootG ∧
  st.regs rQueryPtr = qPtr ∧ st.regs rQueryCount = Cs.length ∧
  st.regs rPreFsBase = preFs ∧ st.regs rPreGsBase = preGs ∧ st.regs rPreHsBase = preHs ∧
  (∀ a < outBase, st.mem a = preMem a) ∧
  st.mem outBase = Cs.length ∧
  (∀ j (hj : j < Cs.length), j < q →
    st.mem (outBase + 1 + j) = Signed.encode (coveringProduct f g Cs[j]))

private theorem exec_queryStep {w d s baseFree outBase rootF rootG qPtr preFs preGs preHs
    W H_pos spVal : ℕ}
    {fnF fnG preOutFn : ℕ → ℕ} {f g : Finset (Fin d) → ℤ} {Cs : List (Finset (Fin d))}
    {initMem preMem : ℕ → ℕ}
    (hob_gt_bf : baseFree < outBase)
    (hq_below : qPtr + Cs.length ≤ baseFree)
    (hq_mem : ∀ j (hj : j < Cs.length), initMem (qPtr + j) = setMask Cs[j])
    (hpre_below_bf : ∀ a < baseFree, preMem a = initMem a)
    (htrieF : HoldsTrie initMem baseFree d rootF fnF)
    (htrieG : HoldsTrie initMem baseFree d rootG fnG)
    (hf_eq : ∀ S : Finset (Fin d), fnF (setMask S) = Signed.encode (f S))
    (hg_eq : ∀ S : Finset (Fin d), fnG (setMask S) = Signed.encode (g S))
    (hf_le : ∀ S, (f S).natAbs ≤ W) (hg_le : ∀ S, (g S).natAbs ≤ W)
    (hpFs_lt : preFs + d < outBase) (hpGs_lt : preGs + d < outBase)
    (hpHs_lt : preHs + d < outBase)
    (hpreF_st : ∀ k ≤ d, ∃ stFn, HoldsTrie preMem outBase d (preMem (preFs + k)) stFn ∧
      ∀ Y : Finset (Fin d), #Y ≤ s →
        stFn (setMask Y) = Signed.encode (yatesTransform (1 : ℤ) ((List.finRange d).take k) f Y))
    (hpreG_st : ∀ k ≤ d, ∃ stFn, HoldsTrie preMem outBase d (preMem (preGs + k)) stFn ∧
      ∀ Y : Finset (Fin d), #Y ≤ s →
        stFn (setMask Y) = Signed.encode (yatesTransform (1 : ℤ) ((List.finRange d).take k) g Y))
    (hpreH_st : ∀ k ≤ d, ∃ stFn, HoldsTrie preMem outBase d (preMem (preHs + k)) stFn ∧
      ∀ Y : Finset (Fin d), #Y ≤ s →
        stFn (setMask Y) = Signed.encode (yatesTransform (-1 : ℤ) ((List.finRange d).take k)
          (fun S => subsetZeta f S * subsetZeta g S) Y))
    (hpreOut_tr : HoldsTrie preMem outBase d (preMem (preHs + d)) preOutFn)
    (hpreOut_eq : ∀ Y : Finset (Fin d), #Y ≤ s →
      preOutFn (setMask Y) = Signed.encode (coveringProduct f g Y))
    (hH_pos1 : 1 ≤ H_pos) (hCs_H : ∀ C ∈ Cs, highCount #C s ≤ H_pos)
    (hqw_bound : outBase + 1 + Cs.length + (d + 2 * H_pos + tripleSpace d H_pos) ≤ spVal)
    (hfit_space : Fits w spVal)
    (hfit_val : Fits w (valueEnvelope d W))
    (st : Data numRegs)
    (hst : QueryInv s outBase rootF rootG qPtr preFs preGs preHs f g Cs preMem
      (st.regs rQueryIdx) st)
    (hq : st.regs rQueryIdx < Cs.length) :
    ∃ z, ExecWithin w queryStep st z (180 * (d + 1) ^ 2 * H_pos) ∧
      QueryInv s outBase rootF rootG qPtr preFs preGs preHs f g Cs preMem
        (st.regs rQueryIdx + 1) z ∧
      z.regs rQueryIdx = st.regs rQueryIdx + 1 := by
  have hfit_mask : Fits w (2 ^ d) := mask_fits_of_valueEnvelope hfit_val
  have hfit_d : Fits w d := hfit_mask.of_le Nat.lt_two_pow_self.le
  let qWorkStart := outBase + 1 + Cs.length
  have hf_ob : Fits w outBase := hfit_space.of_le (by omega)
  have hf_qw : Fits w qWorkStart := hfit_space.of_le (by dsimp only [qWorkStart]; omega)
  generalize hq_eq : st.regs rQueryIdx = q at hst hq ⊢
  dsimp only [QueryInv] at hst
  obtain ⟨hsz, hso, hsd, hss, hsout, hspf, hstF, hstG, hsqp, hsqc,
    hspFs, hspGs, hspHs, hs_pre, hs_ob, hs_ans⟩ := hst
  generalize hC_def : Cs[q] = C
  have hC_mem : C ∈ Cs := hC_def ▸ List.getElem_mem hq
  have hread_q : st.mem (qPtr + q) = setMask C := by
    rw [hs_pre _ (by omega), hpre_below_bf _ (by omega), ← hC_def]; exact hq_mem q hq
  have hf_qp_q : Fits w (qPtr + q) := hfit_space.of_le (by omega)
  have hf_qw_d : Fits w (qWorkStart + d) := hfit_space.of_le (by dsimp only [qWorkStart]; omega)
  have hq0_st : ∃ u₀, ExecWithin w qLoadCode st u₀ 5 ∧
      u₀.regs rTrieKey = setMask C ∧ u₀.regs rCoordsPtr = qWorkStart ∧
      u₀.regs rFree = qWorkStart + d ∧ u₀.mem = st.mem := by
    unfold qLoadCode
    wram_exec [hspf, hsqp, hq_eq, hsd, hread_q]
    wram_simp [hread_q, qWorkStart]
  obtain ⟨u₀, he_q0, hu₀_key, hu₀_cp, hu₀_fr, hu₀_mem⟩ := hq0_st
  have hu₀_regs : ∀ i, i ≠ rFree ∧ i ≠ rGenTmp ∧ i ≠ rTrieKey ∧ i ≠ rCoordsPtr →
      u₀.regs i = st.regs i :=
    fun i hi => he_q0.regs_eq (qLoadCode_preserves i hi)
  obtain ⟨u₁, he_ext, hu₁_clen, hu₁_cmem, hu₁_cfr, hu₁_regs⟩ :=
    exec_extractCoords C u₀
      ((hu₀_regs rZero (by decide)).trans hsz)
      ((hu₀_regs rOne (by decide)).trans hso)
      ((hu₀_regs rDim (by decide)).trans hsd)
      hu₀_key hu₀_cp hf_qw_d hfit_mask
  have hcList_nd_raw : ((List.finRange d).filter (· ∈ C)).Nodup :=
    (List.nodup_finRange d).filter _
  have hcList_tf_raw : ((List.finRange d).filter (· ∈ C)).toFinset = C := by ext i; simp
  generalize hcList_def : (List.finRange d).filter (· ∈ C) = cList
    at hu₁_clen hu₁_cmem hcList_nd_raw hcList_tf_raw
  have hcList_nd : cList.Nodup := hcList_nd_raw
  have hcList_toFinset : cList.toFinset = C := hcList_tf_raw
  have hcList_len : cList.length = #C := by
    rw [← List.toFinset_card_of_nodup hcList_nd, hcList_toFinset]
  rw [hcList_len] at hu₁_clen
  have keep_u₁ (i : Fin numRegs)
      (h1 : i ≠ rTrieRem ∧ i ≠ rCoordsLen ∧ i ≠ rGenIdx ∧ i ≠ rGenTmp)
      (h0 : i ≠ rFree ∧ i ≠ rGenTmp ∧ i ≠ rTrieKey ∧ i ≠ rCoordsPtr) :
      u₁.regs i = st.regs i :=
    (hu₁_regs i h1).trans (hu₀_regs i h0)
  have u₁_below_qw : ∀ a < qWorkStart, u₁.mem a = st.mem a :=
    fun a ha => (hu₁_cfr a (Or.inl ha)).trans (congrFun hu₀_mem a)
  have u₁_below_ob : ∀ a < outBase, u₁.mem a = preMem a :=
    fun a ha => (u₁_below_qw a (by dsimp only [qWorkStart]; omega)).trans (hs_pre a ha)
  have hu₁_s : u₁.regs rThresh = s := (keep_u₁ rThresh (by decide) (by decide)).trans hss
  have hbr_eval : ∃ u_ans,
      ExecWithin w qBranchCode u₁ u_ans
        (180 * (d + 1) ^ 2 * H_pos - (5 + (11 * d + 5) + 3)) ∧
      u_ans.regs rTrieVal = Signed.encode (coveringProduct f g C) ∧
      (∀ a < qWorkStart, u_ans.mem a = st.mem a) := by
    by_cases hlt_Cs : #C < s
    · have hcond : (Cond.lt rCoordsLen rThresh).Holds u₁ := by
        simp [Cond.holds_lt, hu₁_clen, hu₁_s, hlt_Cs]
      have hf_phs_d : Fits w (preHs + d) := hfit_space.of_le (by omega)
      have hu₁_pHs : u₁.regs rPreHsBase = preHs :=
        (keep_u₁ rPreHsBase (by decide) (by decide)).trans hspHs
      have hu₁_d : u₁.regs rDim = d :=
        (keep_u₁ rDim (by decide) (by decide)).trans hsd
      have hread_phs : u₁.mem (preHs + d) = preMem (preHs + d) :=
        u₁_below_ob _ hpHs_lt
      have hst0 : ∃ v₀, ExecWithin w qShortLoadCode u₁ v₀ 2 ∧
          v₀.regs rTrieRoot = preMem (preHs + d) ∧ v₀.mem = u₁.mem := by
        unfold qShortLoadCode
        wram_exec [hu₁_pHs, hu₁_d, hread_phs]
        wram_simp [hread_phs]
      obtain ⟨v₀, he_ld, hv₀_root, hv₀_mem⟩ := hst0
      have hv₀_regs : ∀ i, i ≠ rGenTmp ∧ i ≠ rTrieRoot → v₀.regs i = u₁.regs i :=
        fun i hi => he_ld.regs_eq (qShortLoadCode_preserves i hi)
      have htr_v₀ : HoldsTrie v₀.mem outBase d (preMem (preHs + d)) preOutFn := by
        rw [hv₀_mem]; exact hpreOut_tr.congr_below u₁_below_ob
      have hv₀_key : v₀.regs rTrieKey = setMask C :=
        (hv₀_regs rTrieKey (by decide)).trans ((hu₁_regs rTrieKey (by decide)).trans hu₀_key)
      obtain ⟨v₁, he_get, hv₁_val, hv₁_mem, _⟩ :=
        exec_trieGet v₀
          ((hv₀_regs rZero (by decide)).trans
            ((keep_u₁ rZero (by decide) (by decide)).trans hsz))
          ((hv₀_regs rOne (by decide)).trans
            ((keep_u₁ rOne (by decide) (by decide)).trans hso))
          ((hv₀_regs rDim (by decide)).trans hu₁_d)
          hv₀_root hv₀_key htr_v₀ hf_ob hfit_d (hfit_mask.of_le (setMask_lt C).le)
      rw [hpreOut_eq C (by omega)] at hv₁_val
      obtain ⟨n_b, hn_b, hex_b⟩ := he_ld.seq he_get
      refine ⟨v₁, ⟨n_b + 1, shortBranch_budget_le hH_pos1 hn_b,
        Exec.branch_pos hcond hex_b⟩, hv₁_val,
        fun a ha => (congrFun (hv₁_mem.trans hv₀_mem) a).trans (u₁_below_qw a ha)⟩
    · exact exec_qLongBranch u₁
        ((keep_u₁ rZero (by decide) (by decide)).trans hsz)
        ((keep_u₁ rOne (by decide) (by decide)).trans hso)
        ((keep_u₁ rDim (by decide) (by decide)).trans hsd)
        hu₁_s
        ((hu₁_regs rTrieKey (by decide)).trans hu₀_key)
        ((hu₁_regs rCoordsPtr (by decide)).trans hu₀_cp)
        hu₁_clen
        ((hu₁_regs rFree (by decide)).trans hu₀_fr)
        ((keep_u₁ rTrieF (by decide) (by decide)).trans hstF)
        ((keep_u₁ rTrieG (by decide) (by decide)).trans hstG)
        ((keep_u₁ rQueryPtr (by decide) (by decide)).trans hsqp)
        ((keep_u₁ rQueryIdx (by decide) (by decide)).trans hq_eq)
        ((keep_u₁ rPreFsBase (by decide) (by decide)).trans hspFs)
        ((keep_u₁ rPreGsBase (by decide) (by decide)).trans hspGs)
        ((keep_u₁ rPreHsBase (by decide) (by decide)).trans hspHs)
        hcList_nd hcList_toFinset hcList_len hu₁_cmem u₁_below_qw hs_pre hpre_below_bf
        hob_gt_bf (by dsimp only [qWorkStart]; omega) (by dsimp only [qWorkStart]; omega) hread_q
        htrieF htrieG hf_eq hg_eq hf_le hg_le hpFs_lt hpGs_lt hpHs_lt
        hpreF_st hpreG_st hpreH_st
        (Nat.le_of_not_lt hlt_Cs) hH_pos1 (hCs_H C hC_mem) hqw_bound hfit_space hfit_val
  obtain ⟨u_ans, he_br, hu_val, hu_below⟩ := hbr_eval
  have hu_one : u_ans.regs rOne = 1 :=
    (he_br.regs_eq qBranchCode_preserves_one).trans
      ((keep_u₁ rOne (by decide) (by decide)).trans hso)
  have hu_out : u_ans.regs rOutPtr = outBase :=
    (he_br.regs_eq qBranchCode_preserves_out).trans
      ((keep_u₁ rOutPtr (by decide) (by decide)).trans hsout)
  have hu_qi : u_ans.regs rQueryIdx = q :=
    (he_br.regs_eq qBranchCode_preserves_qi).trans
      ((keep_u₁ rQueryIdx (by decide) (by decide)).trans hq_eq)
  have hf_q1 : Fits w (q + 1) := hfit_space.of_le (by omega)
  have hf_out_q1 : Fits w (outBase + (q + 1)) := hf_qw.of_le (by dsimp only [qWorkStart]; omega)
  have hst_w : ∃ z, ExecWithin w qWriteCode u_ans z 3 ∧
      z.regs rQueryIdx = q + 1 ∧
      z.mem = Function.update u_ans.mem (outBase + (q + 1))
        (Signed.encode (coveringProduct f g C)) := by
    unfold qWriteCode
    wram_exec [hu_qi, hu_one, hu_out, hu_val]
    wram_simp
  obtain ⟨z, he_wr, hz_qi, hz_mem⟩ := hst_w
  have hpt_pos := queryStep_base_le (d := d) hH_pos1
  have hqstep_tot : ExecWithin w queryStep st z (180 * (d + 1) ^ 2 * H_pos) :=
    (he_q0.seq (he_ext.seq (he_br.seq he_wr))).mono (by omega)
  have kq (i : Fin numRegs) (hi : IsQueryKept i) : z.regs i = st.regs i :=
    hqstep_tot.regs_eq (queryStep_preserves i hi)
  refine ⟨z, hqstep_tot, ?_, hz_qi⟩
  dsimp only [QueryInv]
  refine ⟨(kq rZero (by decide)).trans hsz,
    (kq rOne (by decide)).trans hso,
    (kq rDim (by decide)).trans hsd,
    (kq rThresh (by decide)).trans hss,
    (kq rOutPtr (by decide)).trans hsout,
    (kq rPreFree (by decide)).trans hspf,
    (kq rTrieF (by decide)).trans hstF,
    (kq rTrieG (by decide)).trans hstG,
    (kq rQueryPtr (by decide)).trans hsqp,
    (kq rQueryCount (by decide)).trans hsqc,
    (kq rPreFsBase (by decide)).trans hspFs,
    (kq rPreGsBase (by decide)).trans hspGs,
    (kq rPreHsBase (by decide)).trans hspHs,
    ?_, ?_, ?_⟩
  · intro a ha
    rw [hz_mem, Function.update_of_ne (by omega),
      hu_below a (by dsimp only [qWorkStart]; omega)]
    exact hs_pre a ha
  · rw [hz_mem, Function.update_of_ne (by omega),
      hu_below outBase (by dsimp only [qWorkStart]; omega)]
    exact hs_ob
  · intro j hj hj_lt
    by_cases hjq : j = q
    · subst hjq
      have : outBase + 1 + j = outBase + (j + 1) := by omega
      rw [this, hz_mem, Function.update_self, ← hC_def]
    · rw [hz_mem, Function.update_of_ne (by omega),
        hu_below (outBase + 1 + j) (by dsimp only [qWorkStart]; omega)]
      exact hs_ans j hj (by omega)

/-- **Pre-built input tries bound.** From depth-`d` tries representing `f` and `g` below `baseFree`
and query masks `Cs` at `qPtr`, `solveFromTries` writes the encoded covering-product answers as a
length-prefixed array at `Reg.outPtr` within
`200 * (d + 1) ^ 2 * (lowCount d s + Cs.length * max 1 (highPeak s Cs))` instructions. -/
theorem exec_solveFromTries {w d s baseFree rootF rootG qPtr W : ℕ}
    {fnF fnG : ℕ → ℕ} {f g : Finset (Fin d) → ℤ} {Cs : List (Finset (Fin d))}
    (x : Data numRegs)
    (hd : x.regs Reg.dim = d) (hs : x.regs Reg.thresh = s)
    (hfree : x.regs Reg.free = baseFree) (hbf_pos : 1 ≤ baseFree)
    (htF_reg : x.regs Reg.trieF = rootF) (htG_reg : x.regs Reg.trieG = rootG)
    (hqptr : x.regs Reg.queryPtr = qPtr) (hqcnt : x.regs Reg.queryCount = Cs.length)
    (hq_below : qPtr + Cs.length ≤ baseFree)
    (hq_mem : ∀ j (hj : j < Cs.length), x.mem (qPtr + j) = setMask Cs[j])
    (htrieF : HoldsTrie x.mem baseFree d rootF fnF)
    (htrieG : HoldsTrie x.mem baseFree d rootG fnG)
    (hf_eq : ∀ S : Finset (Fin d), fnF (setMask S) = Signed.encode (f S))
    (hg_eq : ∀ S : Finset (Fin d), fnG (setMask S) = Signed.encode (g S))
    (hf_le : ∀ S, (f S).natAbs ≤ W) (hg_le : ∀ S, (g S).natAbs ≤ W)
    (hfit_space : Fits w (solveSpace baseFree d s Cs.length (highPeak s Cs)))
    (hfit_val : Fits w (valueEnvelope d W)) :
    ∃ y, ExecWithin w solveFromTries x y
        (200 * (d + 1) ^ 2 * (lowCount d s + Cs.length * max 1 (highPeak s Cs))) ∧
      outputList y.mem (y.regs Reg.outPtr) = (Cs.map (coveringProduct f g)).map Signed.encode ∧
      Fits w (y.regs Reg.outPtr + Cs.length) ∧
      (∀ a < baseFree, y.mem a = x.mem a) := by
  have hfit_mask : Fits w (2 ^ d) := mask_fits_of_valueEnvelope hfit_val
  have hfit_d : Fits w d := hfit_mask.of_le Nat.lt_two_pow_self.le
  generalize hL_low_def : lowCount d s = L_low
  generalize hH_pk_def : highPeak s Cs = H_pk at hfit_space ⊢
  generalize hH_pos_def : max 1 H_pk = H_pos
  have hL_pos : 1 ≤ L_low := hL_low_def ▸ lowCount_pos d s
  have hH_pos1 : 1 ≤ H_pos := hH_pos_def ▸ le_max_left 1 H_pk
  have hH_pk_le : H_pk ≤ H_pos := hH_pos_def ▸ le_max_right 1 H_pk
  have hCs_H : ∀ C ∈ Cs, highCount #C s ≤ H_pos :=
    fun C hC => (hH_pk_def ▸ le_highPeak_of_mem s hC).trans hH_pk_le
  have hsp_bound : baseFree + (d + 2 * L_low + tripleSpace d L_low) + 1 + Cs.length +
      (d + 2 * H_pos + tripleSpace d H_pos) ≤
      solveSpace baseFree d s Cs.length H_pk := by
    rw [← hH_pos_def]
    exact solveSpace_split hL_low_def
  generalize hsp_val : solveSpace baseFree d s Cs.length H_pk = spVal at hfit_space hsp_bound
  clear hH_pk_def hH_pos_def hsp_val
  -- Step 1: allocate coordsBuf [baseFree, baseFree + d)
  let lowDomBase := baseFree + d
  have hf_ldb : Fits w (baseFree + d) := hfit_space.of_le (by omega)
  have hsetup0 : ∃ s₀, ExecWithin (B := .standard) w (ram[
      rZero ← #0;
      rOne ← #1;
      rCoordsPtr ← rFree;
      rFree ← rFree + rDim ]) x s₀ 4 ∧
      s₀.regs rZero = 0 ∧ s₀.regs rOne = 1 ∧ s₀.regs rDim = d ∧ s₀.regs rThresh = s ∧
      s₀.regs rCoordsPtr = baseFree ∧ s₀.regs rFree = lowDomBase ∧
      s₀.regs rTrieF = rootF ∧ s₀.regs rTrieG = rootG ∧
      s₀.regs rQueryPtr = qPtr ∧ s₀.regs rQueryCount = Cs.length ∧
      s₀.mem = x.mem := by
    wram_exec [hd, hfree]
    wram_simp [hd, hs, hfree, htF_reg, htG_reg, hqptr, hqcnt, lowDomBase]
  obtain ⟨s₀, he_s0, hs₀z, hs₀o, hs₀d, hs₀s, hs₀cp, hs₀fr,
    hs₀tF, hs₀tG, hs₀qp, hs₀qc, hs₀mem⟩ := hsetup0
  -- Step 2: initIdentityCoords at baseFree
  obtain ⟨s₁, he_ic, hs₁_coords, hs₁_fr, hs₁_regs⟩ :=
    exec_initIdentityCoords s₀ hs₀o hs₀d hs₀cp hf_ldb hfit_d
  -- Step 3: genLowSubsets on List.finRange d at lowDomBase
  have hs₁_d : s₁.regs rDim = d := (hs₁_regs rDim (by decide)).trans hs₀d
  have hs₁_s : s₁.regs rThresh = s := (hs₁_regs rThresh (by decide)).trans hs₀s
  have hs₁_f : s₁.regs rFree = lowDomBase := (hs₁_regs rFree (by decide)).trans hs₀fr
  have hp2_st : ∃ s₂, ExecWithin (B := .standard) w
      (ram[ rCoordsLen ← rDim; rMaxCard ← rThresh; rDomPtr ← rFree ]) s₁ s₂ 3 ∧
      s₂.regs rZero = 0 ∧ s₂.regs rOne = 1 ∧ s₂.regs rDim = d ∧ s₂.regs rThresh = s ∧
      s₂.regs rCoordsPtr = baseFree ∧ s₂.regs rCoordsLen = d ∧ s₂.regs rMaxCard = s ∧
      s₂.regs rDomPtr = lowDomBase ∧ s₂.regs rTrieF = rootF ∧ s₂.regs rTrieG = rootG ∧
      s₂.regs rQueryPtr = qPtr ∧ s₂.regs rQueryCount = Cs.length ∧ s₂.mem = s₁.mem := by
    wram_exec [hs₁_d, hs₁_s, hs₁_f]
    refine ⟨(hs₁_regs rZero (by decide)).trans hs₀z,
      (hs₁_regs rOne (by decide)).trans hs₀o, hs₁_d, hs₁_s,
      (hs₁_regs rCoordsPtr (by decide)).trans hs₀cp, ?_, ?_, ?_,
      (hs₁_regs rTrieF (by decide)).trans hs₀tF,
      (hs₁_regs rTrieG (by decide)).trans hs₀tG,
      (hs₁_regs rQueryPtr (by decide)).trans hs₀qp,
      (hs₁_regs rQueryCount (by decide)).trans hs₀qc, ?_⟩ <;> wram_simp
  obtain ⟨s₂, he_p2, hs₂z, hs₂o, hs₂d, hs₂s, hs₂cp, hs₂cl, hs₂mc, hs₂dp,
    hs₂tF, hs₂tG, hs₂qp, hs₂qc, hs₂mem⟩ := hp2_st
  have hfr_len : (List.finRange d).length = d := List.length_finRange
  obtain ⟨s₃, he_glow_raw, hs₃_dlen, hs₃_dom, hs₃_fr, hs₃_regs⟩ :=
    exec_genLowSubsets (List.finRange d) s₂ hs₂z hs₂o hs₂cp
      (hs₂cl.trans hfr_len.symm) hs₂mc hs₂dp
      (List.nodup_finRange d) (by rwa [hs₂mem]) (by simp [lowDomBase])
      (by
        rw [hfr_len, ← lowCount, hL_low_def]
        refine hfit_space.of_le ?_
        dsimp only [lowDomBase]
        omega)
      hfit_mask
  have he_glow : ExecWithin w genLowSubsets s₂ s₃ (d * (20 * L_low + 12) + 8) := by
    rwa [hfr_len, ← lowCount, hL_low_def] at he_glow_raw
  clear he_glow_raw
  have hlow_spec_raw := prefixesUpTo_spec s (List.nodup_finRange d)
  have hlow_len_raw : (prefixesUpTo s (List.finRange d)).length = L_low := by
    rw [length_prefixesUpTo s (List.nodup_finRange d), List.length_finRange, ← lowCount, hL_low_def]
  clear hL_low_def
  generalize hlowDom_def : prefixesUpTo s (List.finRange d) = lowDom
    at hs₃_dlen hs₃_dom hlow_spec_raw hlow_len_raw
  have hlow_len : lowDom.length = L_low := hlow_len_raw
  have hlow_mem_iff : ∀ X : Finset (Fin d), X ∈ lowDom ↔ #X ≤ s := by
    intro X
    rw [hlow_spec_raw.2 X]
    exact ⟨fun h => h.2, fun h => ⟨by intro a _; simp, h⟩⟩
  -- Step 4: runTransformTriple on lowDom
  let preStart := lowDomBase + 2 * L_low
  have hf_2L : Fits w (L_low + L_low) :=
    hfit_space.of_le (by omega)
  have hf_ps : Fits w (lowDomBase + (L_low + L_low)) :=
    hfit_space.of_le (by dsimp only [lowDomBase]; omega)
  have hs₃_dp : s₃.regs rDomPtr = lowDomBase :=
    (hs₃_regs rDomPtr (by decide)).trans hs₂dp
  have hdl_eq : s₃.regs rDomLen = L_low := hs₃_dlen.trans hlow_len
  have hp4_st : ∃ s₄, ExecWithin w solvePreStageCode s₃ s₄ 5 ∧
      s₄.regs rCurDomPtr = lowDomBase ∧ s₄.regs rCurDomLen = lowDom.length ∧
      s₄.regs rFree = preStart ∧ s₄.regs rStageCutoff = 0 ∧ s₄.mem = s₃.mem := by
    unfold solvePreStageCode
    wram_exec [hs₃_dp, hdl_eq]
    refine ⟨rfl, hlow_len.symm, ?_, rfl, rfl⟩
    wram_simp [preStart]; omega
  obtain ⟨s₄, he_p4, hs₄_cdp, hs₄_cdl, hs₄_fr, hs₄_cut, hs₄_mem⟩ := hp4_st
  have hs₄_regs : ∀ i,
      i ≠ rCurDomPtr ∧ i ≠ rCurDomLen ∧ i ≠ rGenTmp ∧ i ≠ rFree ∧ i ≠ rStageCutoff →
        s₄.regs i = s₃.regs i :=
    fun i hi => he_p4.regs_eq (solvePreStageCode_preserves i hi)
  have keep_s₄_s₂ (i : Fin numRegs)
      (h4 : i ≠ rCurDomPtr ∧ i ≠ rCurDomLen ∧ i ≠ rGenTmp ∧ i ≠ rFree ∧ i ≠ rStageCutoff)
      (h3 : i ≠ rTrieTmp ∧ i ≠ rCellSaved ∧ (i.val < 27 ∨ 33 ≤ i.val)) :
      s₄.regs i = s₂.regs i :=
    (hs₄_regs i h4).trans (hs₃_regs i h3)
  have mem_s₄_below_bf : ∀ a < baseFree, s₄.mem a = x.mem a := fun a ha => by
    rw [hs₄_mem, hs₃_fr a (Or.inl (by dsimp [lowDomBase]; omega)), hs₂mem,
      hs₁_fr a (Or.inl ha), hs₀mem]
  have htrieF_s₄ : HoldsTrie s₄.mem preStart d rootF fnF :=
    (htrieF.congr_below mem_s₄_below_bf).mono_bound (by dsimp [preStart, lowDomBase]; omega)
  have htrieG_s₄ : HoldsTrie s₄.mem preStart d rootG fnG :=
    (htrieG.congr_below mem_s₄_below_bf).mono_bound (by dsimp [preStart, lowDomBase]; omega)
  have hlow_closed : ∀ X ∈ lowDom, ∀ coord : Fin d, coord ∈ X →
      (0 ≤ #(X.erase coord) → X.erase coord ∈ lowDom) ∧
      (#(X.erase coord) < 0 → False) := by
    intro X hX coord _
    have hXs := (hlow_mem_iff X).mp hX
    exact ⟨fun _ => (hlow_mem_iff _).mpr (card_erase_le.trans hXs), by omega⟩
  have hf_pre_tr : Fits w (preStart + tripleSpace d lowDom.length) := by
    rw [hlow_len]
    exact hfit_space.of_le (by dsimp only [preStart, lowDomBase]; omega)
  obtain ⟨s₅, preFs, preGs, preHs, outBase, he_pre, hs₅_qFs, hs₅_qGs, hs₅_ro, hs₅_fr,
    hpf_lo, hpf_hi, hpFs_lt, hpGs_lt, hpHs_lt, hpreF_st, hpreG_st, hpreH_st,
    ⟨preOutFn, hpreOut_tr, hpreOut_eq⟩, hs₅_frame, hs₅_regs⟩ :=
    exec_runTransformTriple (preFs := s₄.regs rPreFsBase) (preGs := s₄.regs rPreGsBase)
      (preHs := s₄.regs rPreHsBase) (P_low := fun _ => False) (W := W) s₄
      ((keep_s₄_s₂ rZero (by decide) (by decide)).trans hs₂z)
      ((keep_s₄_s₂ rOne (by decide) (by decide)).trans hs₂o)
      ((keep_s₄_s₂ rDim (by decide) (by decide)).trans hs₂d)
      hs₄_cdp hs₄_cdl hs₄_cut
      ((keep_s₄_s₂ rTrieF (by decide) (by decide)).trans hs₂tF)
      ((keep_s₄_s₂ rTrieG (by decide) (by decide)).trans hs₂tG)
      rfl rfl rfl hs₄_fr (by dsimp [preStart, lowDomBase]; omega)
      hlow_spec_raw.1 (by rwa [hs₄_mem]) (by rw [hlow_len])
      hlow_closed htrieF_s₄ htrieG_s₄ hf_eq hg_eq hf_le hg_le
      (fun hpos => by omega) hfit_val hf_pre_tr
  -- Step 5: allocate output array at outBase and set qWorkStart = outBase + 1 + Cs.length
  let qWorkStart := outBase + 1 + Cs.length
  have hqw_bound : qWorkStart + (d + 2 * H_pos + tripleSpace d H_pos) ≤ spVal := by
    rw [hlow_len] at hpf_hi
    dsimp only [qWorkStart, preStart, lowDomBase] at hpf_hi ⊢
    omega
  have hf_ob : Fits w outBase := hfit_space.of_le (by dsimp [qWorkStart] at hqw_bound; omega)
  have hf_ob1 : Fits w (outBase + 1) :=
    hfit_space.of_le (by dsimp [qWorkStart] at hqw_bound; omega)
  have hf_qw : Fits w (outBase + 1 + Cs.length) :=
    hfit_space.of_le (by dsimp [qWorkStart] at hqw_bound; omega)
  have keep_s₅_s₂ (i : Fin numRegs) (h5 : ¬ IsTripleMod i)
      (h4 : i ≠ rCurDomPtr ∧ i ≠ rCurDomLen ∧ i ≠ rGenTmp ∧ i ≠ rFree ∧ i ≠ rStageCutoff)
      (h3 : i ≠ rTrieTmp ∧ i ≠ rCellSaved ∧ (i.val < 27 ∨ 33 ≤ i.val)) :
      s₅.regs i = s₂.regs i :=
    (hs₅_regs i h5).trans (keep_s₄_s₂ i h4 h3)
  have hs₅_o : s₅.regs rOne = 1 :=
    (keep_s₅_s₂ rOne (by decide) (by decide) (by decide)).trans hs₂o
  have hs₅_qc : s₅.regs rQueryCount = Cs.length :=
    (keep_s₅_s₂ rQueryCount (by decide) (by decide) (by decide)).trans hs₂qc
  have hp5_st : ∃ s₆, ExecWithin w preSaveCode s₅ s₆ 8 ∧
      s₆.regs rPreFsBase = preFs ∧ s₆.regs rPreGsBase = preGs ∧
      s₆.regs rPreHsBase = preHs ∧ s₆.regs rOutPtr = outBase ∧
      s₆.regs rPreFree = qWorkStart ∧ s₆.regs rQueryIdx = 0 ∧
      s₆.mem = Function.update s₅.mem outBase Cs.length := by
    unfold preSaveCode
    wram_exec [hs₅_qFs, hs₅_qGs, hs₅_ro, hs₅_fr, hs₅_o, hs₅_qc]
    wram_simp [qWorkStart]
  obtain ⟨s₆, he_p5, hs₆_pFs, hs₆_pGs, hs₆_pHs, hs₆_out, hs₆_pf, hs₆_qi, hs₆_mem⟩ := hp5_st
  have hs₆_regs : ∀ i, i ≠ rPreFsBase ∧ i ≠ rPreGsBase ∧ i ≠ rPreHsBase ∧
      i ≠ rOutPtr ∧ i ≠ rPreFree ∧ i ≠ rQueryIdx → s₆.regs i = s₅.regs i :=
    fun i hi => he_p5.regs_eq (preSaveCode_preserves i hi)
  have s₅_below_bf : ∀ a < baseFree, s₅.mem a = x.mem a := fun a ha =>
    (hs₅_frame a (Or.inl (by dsimp [preStart, lowDomBase]; omega))).trans (mem_s₄_below_bf a ha)
  -- Step 6: query loop
  have hob_gt_bf : baseFree < outBase := by dsimp only [preStart, lowDomBase] at hpf_lo; omega
  let P_q := QueryInv s outBase rootF rootG qPtr preFs preGs preHs f g Cs s₅.mem
  have hqbody (st : Data numRegs) (hst : P_q (st.regs rQueryIdx) st)
      (hq : st.regs rQueryIdx < Cs.length) :
      ∃ z, ExecWithin w queryStep st z (180 * (d + 1) ^ 2 * H_pos) ∧
        P_q (st.regs rQueryIdx + 1) z ∧ z.regs rQueryIdx = st.regs rQueryIdx + 1 :=
    exec_queryStep hob_gt_bf hq_below hq_mem s₅_below_bf htrieF htrieG hf_eq hg_eq hf_le hg_le
      hpFs_lt hpGs_lt hpHs_lt
      (fun k hk => by
        obtain ⟨stFn, htr, heq⟩ := hpreF_st k hk
        exact ⟨stFn, htr, fun Y hY => heq Y ((hlow_mem_iff Y).mpr hY)⟩)
      (fun k hk => by
        obtain ⟨stFn, htr, heq⟩ := hpreG_st k hk
        exact ⟨stFn, htr, fun Y hY => heq Y ((hlow_mem_iff Y).mpr hY)⟩)
      (fun k hk => by
        obtain ⟨stFn, htr, heq⟩ := hpreH_st k hk
        exact ⟨stFn, htr, fun Y hY => heq Y ((hlow_mem_iff Y).mpr hY)⟩)
      hpreOut_tr (fun Y hY => hpreOut_eq Y ((hlow_mem_iff Y).mpr hY))
      hH_pos1 hCs_H hqw_bound hfit_space hfit_val st hst hq
  have hs₆P : P_q (s₆.regs rQueryIdx) s₆ := by
    dsimp only [P_q, QueryInv]
    rw [hs₆_qi]
    refine ⟨(hs₆_regs rZero (by decide)).trans
        ((keep_s₅_s₂ rZero (by decide) (by decide) (by decide)).trans hs₂z),
      (hs₆_regs rOne (by decide)).trans hs₅_o,
      (hs₆_regs rDim (by decide)).trans
        ((keep_s₅_s₂ rDim (by decide) (by decide) (by decide)).trans hs₂d),
      (hs₆_regs rThresh (by decide)).trans
        ((keep_s₅_s₂ rThresh (by decide) (by decide) (by decide)).trans hs₂s),
      hs₆_out, hs₆_pf,
      (hs₆_regs rTrieF (by decide)).trans
        ((keep_s₅_s₂ rTrieF (by decide) (by decide) (by decide)).trans hs₂tF),
      (hs₆_regs rTrieG (by decide)).trans
        ((keep_s₅_s₂ rTrieG (by decide) (by decide) (by decide)).trans hs₂tG),
      (hs₆_regs rQueryPtr (by decide)).trans
        ((keep_s₅_s₂ rQueryPtr (by decide) (by decide) (by decide)).trans hs₂qp),
      (hs₆_regs rQueryCount (by decide)).trans hs₅_qc,
      hs₆_pFs, hs₆_pGs, hs₆_pHs,
      fun a ha => by rw [hs₆_mem, Function.update_of_ne (by omega)],
      by simp [hs₆_mem],
      by simp⟩
  obtain ⟨y, hloop_q, hyP, _⟩ := ExecWithin.loop_count P_q
    (fun st hst => hst.2.2.2.2.2.2.2.2.2.1) hqbody (by simp [hs₆_qi]) hs₆P
  obtain ⟨_, _, _, _, hy_out, _, _, _, _, _, _, _, _, hy_pre, hy_ob, hy_ans⟩ := hyP
  have htot : ExecWithin w solveFromTries x y
      (200 * (d + 1) ^ 2 * (L_low + Cs.length * H_pos)) := by
    change ExecWithin w (.seq _ (.seq initIdentityCoords (.seq _ (.seq genLowSubsets
      (.seq solvePreStageCode (.seq runTransformTriple (.seq preSaveCode _))))))) x y _
    refine (he_s0.seq (he_ic.seq (he_p2.seq (he_glow.seq (he_p4.seq
      (he_pre.seq (he_p5.seq hloop_q))))))).mono ?_
    rw [hs₆_qi, Nat.sub_zero, hlow_len]
    exact solve_total_time_le hL_pos hH_pos1
  refine ⟨y, htot, ?_, ?_, ?_⟩
  · rw [hy_out]
    refine List.ext_getElem (by simp [hy_ob]) fun j hj1 _ => ?_
    rw [getElem_outputList]
    have hj_cs : j < Cs.length := by simpa [hy_ob] using hj1
    simpa using hy_ans j hj_cs hj_cs
  · rw [hy_out]
    exact hf_qw.of_le (by omega)
  · intro a ha
    exact (hy_pre a (by omega)).trans (s₅_below_bf a ha)

/-- **Ranked subset-convolution bound from pre-built input tries** ([ChanItakuraMaYu2026],
Theorem 2.2 core): when `f` is supported on sets of size `t₁`, `g` on sets of size `t₂`, and every
query `C ∈ Cs` has size `t₁ + t₂` with `s ≤ t₁ + t₂` (`t₁ = t₂ = t` in Theorem 2.2),
`solveFromTries` returns `(Cs.map (subsetConvolution f g)).map Signed.encode` within
`200 * (d + 1) ^ 2 * (lowCount d s + Cs.length * highCount (t₁ + t₂) s)` instructions. -/
theorem exec_solveFromTries_subsetConvolution {w d s t₁ t₂ baseFree rootF rootG qPtr W : ℕ}
    {fnF fnG : ℕ → ℕ} {f g : Finset (Fin d) → ℤ} {Cs : List (Finset (Fin d))}
    (x : Data numRegs)
    (hd : x.regs Reg.dim = d) (hs_reg : x.regs Reg.thresh = s)
    (hfree : x.regs Reg.free = baseFree) (hbf_pos : 1 ≤ baseFree)
    (htF_reg : x.regs Reg.trieF = rootF) (htG_reg : x.regs Reg.trieG = rootG)
    (hqptr : x.regs Reg.queryPtr = qPtr) (hqcnt : x.regs Reg.queryCount = Cs.length)
    (hq_below : qPtr + Cs.length ≤ baseFree)
    (hq_mem : ∀ j (hj : j < Cs.length), x.mem (qPtr + j) = setMask Cs[j])
    (htrieF : HoldsTrie x.mem baseFree d rootF fnF)
    (htrieG : HoldsTrie x.mem baseFree d rootG fnG)
    (hf_eq : ∀ S : Finset (Fin d), fnF (setMask S) = Signed.encode (f S))
    (hg_eq : ∀ S : Finset (Fin d), fnG (setMask S) = Signed.encode (g S))
    (hf_le : ∀ S, (f S).natAbs ≤ W) (hg_le : ∀ S, (g S).natAbs ≤ W)
    (hf_rank : ∀ A, f A ≠ 0 → #A = t₁) (hg_rank : ∀ B, g B ≠ 0 → #B = t₂)
    (hCs_card : ∀ C ∈ Cs, #C = t₁ + t₂) (hs_le : s ≤ t₁ + t₂)
    (hfit_space : Fits w (solveSpace baseFree d s Cs.length (highCount (t₁ + t₂) s)))
    (hfit_val : Fits w (valueEnvelope d W)) :
    ∃ y, ExecWithin w solveFromTries x y
        (200 * (d + 1) ^ 2 * (lowCount d s + Cs.length * highCount (t₁ + t₂) s)) ∧
      outputList y.mem (y.regs Reg.outPtr) = (Cs.map (subsetConvolution f g)).map Signed.encode ∧
      Fits w (y.regs Reg.outPtr + Cs.length) ∧
      (∀ a < baseFree, y.mem a = x.mem a) := by
  have hpk_le : highPeak s Cs ≤ highCount (t₁ + t₂) s :=
    highPeak_le_of_forall_card_eq s (t₁ + t₂) hCs_card
  have hhc_pos : 1 ≤ highCount (t₁ + t₂) s := highCount_pos hs_le
  have hmax_le : max 1 (highPeak s Cs) ≤ highCount (t₁ + t₂) s := max_le hhc_pos hpk_le
  have hsp' : Fits w (solveSpace baseFree d s Cs.length (highPeak s Cs)) :=
    hfit_space.of_le (by
      dsimp only [solveSpace]
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _)
  obtain ⟨y, he, hlist, hfit_out, hframe⟩ :=
    exec_solveFromTries x hd hs_reg hfree hbf_pos htF_reg htG_reg hqptr hqcnt
      hq_below hq_mem htrieF htrieG hf_eq hg_eq hf_le hg_le hsp' hfit_val
  refine ⟨y, he.mono (Nat.mul_le_mul_left _ (Nat.add_le_add_left
      (Nat.mul_le_mul_left _ hmax_le) _)), ?_, hfit_out, hframe⟩
  rw [hlist]
  congr 1
  exact List.map_congr_left fun C hC =>
    coveringProduct_eq_subsetConvolution hf_rank hg_rank (hCs_card C hC)

/-! ### Complete initialized flat `Program .standard 56` and [ChanItakuraMaYu2026], Theorem 2.2 -/

/-- Set function represented by a list of sparse `(set, weight)` entries, summing duplicate keys. -/
@[expose] def evalEntries {d : ℕ} (es : List (Finset (Fin d) × ℤ)) (S : Finset (Fin d)) : ℤ :=
  es.foldl (fun fn p X => if X = p.1 then fn X + p.2 else fn X) (fun _ => 0) S

theorem evalEntries_eq_sum_filter {d : ℕ} (es : List (Finset (Fin d) × ℤ)) (S : Finset (Fin d)) :
    evalEntries es S = ((es.filter fun p => decide (p.1 = S)).map Prod.snd).sum := by
  induction es using List.reverseRecOn with
  | nil => rfl
  | append_singleton es p ih =>
    rcases p with ⟨A, v⟩
    simp only [evalEntries, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.filter_append, List.filter_cons, List.filter_nil, List.map_append, List.sum_append]
    rw [← evalEntries, ih]
    by_cases hSA : S = A
    · subst hSA; simp
    · have hAS : A ≠ S := Ne.symm hSA
      simp [hSA, hAS]

theorem evalEntries_ranked {d t : ℕ} {es : List (Finset (Fin d) × ℤ)}
    (hes : ∀ p ∈ es, p.2 ≠ 0 → #p.1 = t) (S : Finset (Fin d)) (hS : evalEntries es S ≠ 0) :
    #S = t := by
  by_contra hne
  apply hS
  rw [evalEntries_eq_sum_filter]
  apply List.sum_eq_zero
  intro v hv
  obtain ⟨p, hp_flt, rfl⟩ := List.mem_map.mp hv
  obtain ⟨hp_es, hp_eq⟩ := List.mem_filter.mp hp_flt
  have hpS : p.1 = S := of_decide_eq_true hp_eq
  by_contra hv0
  exact hne (hpS ▸ hes p hp_es hv0)

/-- Sum of `|v|` across sparse `(set, v)` entries. -/
@[expose] def entryAbsSum {d : ℕ} (es : List (Finset (Fin d) × ℤ)) : ℕ :=
  (es.map fun p => p.2.natAbs).sum

theorem natAbs_evalEntries_le {d : ℕ} (es : List (Finset (Fin d) × ℤ))
    (S : Finset (Fin d)) : (evalEntries es S).natAbs ≤ entryAbsSum es := by
  induction es using List.reverseRecOn with
  | nil => simp [evalEntries, entryAbsSum]
  | append_singleton es p ih =>
    rcases p with ⟨A, v⟩
    simp only [evalEntries, List.foldl_append, List.foldl_cons, List.foldl_nil,
      entryAbsSum, List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil, add_zero]
    rw [← evalEntries, ← entryAbsSum]
    by_cases hSA : S = A
    · subst hSA
      simp only [↓reduceIte]
      exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add_right ih _)
    · simp only [hSA, ↓reduceIte]
      exact ih.trans (Nat.le_add_right _ _)

/-- Word encoding of a sparse `(set, weight)` list: `[setMask S₀, Signed.encode v₀, ...]`. -/
@[expose] def encodeEntries {d : ℕ} (es : List (Finset (Fin d) × ℤ)) : List ℕ :=
  es.flatMap fun p => [setMask p.1, Signed.encode p.2]

@[simp] theorem length_encodeEntries {d : ℕ} (es : List (Finset (Fin d) × ℤ)) :
    (encodeEntries es).length = 2 * es.length := by
  induction es with
  | nil => rfl
  | cons p es ih =>
    simp only [encodeEntries, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil]
    rw [← encodeEntries, ih]; omega

private theorem getElem_encodeEntries {d : ℕ} (es : List (Finset (Fin d) × ℤ))
    (p : ℕ) (hp : p < es.length) :
    (encodeEntries es)[2 * p]'(by simp; omega) = setMask es[p].1 ∧
    (encodeEntries es)[2 * p + 1]'(by simp; omega) = Signed.encode es[p].2 := by
  induction es generalizing p with
  | nil => simp at hp
  | cons hd tl ih =>
    rcases p with _ | p
    · simp [encodeEntries]
    · have hp' : p < tl.length := by simp at hp; omega
      obtain ⟨h0, h1⟩ := ih p hp'
      have heq : encodeEntries (hd :: tl) = [setMask hd.1, Signed.encode hd.2] ++
          encodeEntries tl := rfl
      refine ⟨?_, ?_⟩
      · simp only [heq]
        rw [List.getElem_append_right (by simp only [List.length_cons, List.length_nil]; omega)]
        simpa [Nat.mul_add] using h0
      · simp only [heq]
        rw [List.getElem_append_right (by simp only [List.length_cons, List.length_nil]; omega)]
        simpa [Nat.mul_add] using h1

/-- Sparse weighted set-function instance over `Fin d` with threshold `s` and query sets `queries`.
In the ranked setting of [ChanItakuraMaYu2026], Problem 2.1 / Theorem 2.2, `leftEntries` are
supported on sets of size `t₁`, `rightEntries` on sets of size `t₂`, and `queries` have size
`t₁ + t₂` (`t₁ = t₂ = t` in Theorem 2.2). -/
structure Instance where
  /-- Universe dimension `d` (ground set `Fin d`). -/
  d : ℕ
  /-- Trimming threshold `s`. -/
  s : ℕ
  /-- Sparse `(set, weight)` pairs summing to the left input function `f`. -/
  leftEntries : List (Finset (Fin d) × ℤ)
  /-- Sparse `(set, weight)` pairs summing to the right input function `g`. -/
  rightEntries : List (Finset (Fin d) × ℤ)
  /-- Query subsets `Cs` at which to evaluate the covering product / subset convolution. -/
  queries : List (Finset (Fin d))

/-- Left input set function `f : Finset (Fin inst.d) → ℤ`. -/
@[expose] def Instance.leftFn (inst : Instance) : Finset (Fin inst.d) → ℤ :=
  evalEntries inst.leftEntries

/-- Right input set function `g : Finset (Fin inst.d) → ℤ`. -/
@[expose] def Instance.rightFn (inst : Instance) : Finset (Fin inst.d) → ℤ :=
  evalEntries inst.rightEntries

/-- Total number of sparse input entries `n = |leftEntries| + |rightEntries|`. -/
@[expose] def Instance.numEntries (inst : Instance) : ℕ :=
  inst.leftEntries.length + inst.rightEntries.length

/-- Sum of `|v|` over all sparse input entries. -/
@[expose] def Instance.weightSum (inst : Instance) : ℕ :=
  entryAbsSum inst.leftEntries + entryAbsSum inst.rightEntries

/-- Flat word encoding `[d, s, |leftEntries|, |rightEntries|, |queries|, leftEntries...,
rightEntries..., queryMasks...]`. -/
@[expose] def Instance.encode (inst : Instance) : List ℕ :=
  [inst.d, inst.s, inst.leftEntries.length, inst.rightEntries.length, inst.queries.length] ++
    encodeEntries inst.leftEntries ++
    encodeEntries inst.rightEntries ++
    inst.queries.map setMask

@[simp] theorem Instance.length_encode (inst : Instance) :
    inst.encode.length = 5 + 2 * inst.numEntries + inst.queries.length := by
  simp only [Instance.encode, Instance.numEntries, List.length_append, List.length_cons,
    List.length_nil, length_encodeEntries, List.length_map]
  omega

/-- Peak address bound for executing `program` on `inst`. -/
@[expose] def Instance.spaceBound (inst : Instance) : ℕ :=
  solveSpace (10 + 2 * (inst.d + 1) * inst.numEntries + inst.queries.length)
    inst.d inst.s inst.queries.length (highPeak inst.s inst.queries)

/-- Running-time bound for executing `program` on `inst` (including the final `halt`). -/
@[expose] def Instance.timeBound (inst : Instance) : ℕ :=
  250 * (inst.d + 1) ^ 2 *
    (inst.numEntries + lowCount inst.d inst.s +
      inst.queries.length * max 1 (highPeak inst.s inst.queries))

/-- Word-width admissibility predicate for `inst`. -/
@[expose] def Instance.FitsWidth (inst : Instance) (w : ℕ) : Prop :=
  Fits w inst.spaceBound ∧ Fits w (valueEnvelope inst.d inst.weightSum)

private theorem signedEncode_le_valueEnvelope {d W : ℕ} {z : ℤ} (hz : z.natAbs ≤ W) :
    Signed.encode z ≤ valueEnvelope d W := by
  dsimp only [valueEnvelope, Signed.encode]
  have h1 : 1 ≤ 8 ^ d := Nat.one_le_pow _ _ (by decide)
  have hW : W + 1 ≤ (W + 1) ^ 2 := by rw [sq]; nlinarith
  have hmul : W + 1 ≤ 8 ^ d * (W + 1) ^ 2 :=
    hW.trans (Nat.le_mul_of_pos_left _ h1)
  split_ifs <;> omega

/-- Any word width satisfying `inst.FitsWidth w` also fits every word of `inst.encode`. -/
theorem Instance.FitsWidth.inputFits {inst : Instance} {w : ℕ} (h : inst.FitsWidth w) :
    InputFits w inst.encode := by
  obtain ⟨hsp, hval⟩ := h
  have hmask : Fits w (2 ^ inst.d) := mask_fits_of_valueEnvelope hval
  have hnum_le : 2 * inst.numEntries ≤ 2 * (inst.d + 1) * inst.numEntries :=
    Nat.mul_le_mul_right _ (by omega)
  have hlen : inst.encode.length ≤ inst.spaceBound := by
    rw [inst.length_encode]
    dsimp only [Instance.spaceBound, solveSpace]
    omega
  refine ⟨hsp.of_le hlen, fun v hv => ?_⟩
  simp only [Instance.encode, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    encodeEntries, List.mem_flatMap, List.mem_map] at hv
  rcases hv with (((rfl | rfl | rfl | rfl | rfl) | ⟨p, hp, rfl | rfl⟩) | ⟨p, hp, rfl | rfl⟩) |
      ⟨C, _, rfl⟩
  · exact hmask.of_le Nat.lt_two_pow_self.le
  · exact hsp.of_le (by dsimp [Instance.spaceBound, solveSpace]; omega)
  · exact hsp.of_le (by
      dsimp [Instance.spaceBound, solveSpace, Instance.numEntries] at hnum_le ⊢; omega)
  · exact hsp.of_le (by
      dsimp [Instance.spaceBound, solveSpace, Instance.numEntries] at hnum_le ⊢; omega)
  · exact hsp.of_le (by dsimp [Instance.spaceBound, solveSpace]; omega)
  · exact hmask.of_le (setMask_lt p.1).le
  · have hp_le : p.2.natAbs ≤ inst.weightSum :=
      (List.le_sum_of_mem (List.mem_map_of_mem (f := fun x => x.2.natAbs) hp)).trans
        (Nat.le_add_right _ _)
    exact hval.of_le (signedEncode_le_valueEnvelope hp_le)
  · exact hmask.of_le (setMask_lt p.1).le
  · have hp_le : p.2.natAbs ≤ inst.weightSum :=
      (List.le_sum_of_mem (List.mem_map_of_mem (f := fun x => x.2.natAbs) hp)).trans
        (Nat.le_add_left _ _)
    exact hval.of_le (signedEncode_le_valueEnvelope hp_le)
  · exact hmask.of_le (setMask_lt C).le

private def buildInputLoadCode : Code .standard numRegs := ram[
  rGenTmp ← rCellIdx + rCellIdx;
  rGenTmp ← rCurDomPtr + rGenTmp;
  rTrieKey ← *rGenTmp;
  rGenTmp ← rGenTmp + rOne;
  Signed.right ← *rGenTmp;
  rTrieRoot ← rCellSaved ]

private theorem buildInputLoadCode_preserves (i : Fin numRegs) :
    i ≠ rGenTmp ∧ i ≠ rTrieKey ∧ i ≠ Signed.right (r := 47) ∧ i ≠ rTrieRoot →
      buildInputLoadCode.Preserves i := by
  decide +kernel +revert

private def buildInputStep : Code .standard numRegs :=
  .seq buildInputLoadCode
    (.seq trieAdd
      (ram[ rCellIdx ← rCellIdx + rOne ]))

/-- Build a depth-`d` binary trie accumulating the sparse `(S, v)` pairs stored as `2 * |es|` words
`[setMask S₀, Signed.encode v₀, …]` starting at `Reg.entryPtr`, writing the allocated root to
`Reg.builtRoot` and advancing `Reg.free`. -/
def buildInputTrie : Code .standard numRegs :=
  .seq (ram[ rZero ← #0; rOne ← #1 ])
    (.seq trieInit
      (.seq (ram[ rCellSaved ← rTrieRoot; rCellIdx ← #0 ])
        (.loop (.lt rCellIdx rCurDomLen) buildInputStep)))

private theorem buildInputTrie_preserves (i : Fin numRegs) :
    ((11 ≤ i.val ∧ i.val ≤ 15 ∧ i ≠ Reg.free) ∨
      (44 ≤ i.val ∧ i.val ≤ 55) ∨ i = Reg.entryPtr ∨ i = Reg.entryCount) →
      buildInputTrie.Preserves i := by
  decide +kernel +revert

/-- Build a depth-`d` `HoldsTrie` from `es.length` sparse `(S, v)` pairs in memory within
`es.length * (23 * d + 40) + 11` standard-basis instructions, preserving caller registers and all
memory outside `Ico free free'`. -/
theorem exec_buildInputTrie {w d entryPtr free W : ℕ}
    (es : List (Finset (Fin d) × ℤ)) (x : Data numRegs)
    (hd : x.regs Reg.dim = d)
    (hep : x.regs Reg.entryPtr = entryPtr) (hel : x.regs Reg.entryCount = es.length)
    (hfree : x.regs Reg.free = free) (hfree_pos : 1 ≤ free)
    (he_below : entryPtr + 2 * es.length ≤ free)
    (he_mem : ∀ p (hp : p < es.length),
      x.mem (entryPtr + 2 * p) = setMask es[p].1 ∧
      x.mem (entryPtr + 2 * p + 1) = Signed.encode es[p].2)
    (hes_W : entryAbsSum es ≤ W)
    (hfit_val : Fits w (valueEnvelope d W))
    (hfit_free : Fits w (free + 2 + 2 * d * es.length)) :
    ∃ y free' outFn,
      ExecWithin w buildInputTrie x y (es.length * (23 * d + 40) + 11) ∧
      y.regs Reg.builtRoot = free ∧ y.regs Reg.free = free' ∧
      free + 2 ≤ free' ∧ free' ≤ free + 2 + 2 * d * es.length ∧
      HoldsTrie y.mem free' d free outFn ∧
      (∀ S : Finset (Fin d), outFn (setMask S) = Signed.encode (evalEntries es S)) ∧
      (∀ a, a < free ∨ free' ≤ a → y.mem a = x.mem a) ∧
      ∀ i : Fin numRegs,
        ((11 ≤ i.val ∧ i.val ≤ 15 ∧ i ≠ Reg.free) ∨
          (44 ≤ i.val ∧ i.val ≤ 55) ∨ i = Reg.entryPtr ∨ i = Reg.entryCount) →
          y.regs i = x.regs i := by
  let B := 8 ^ d * (W + 1) ^ 2
  have hfit_B : Fits w (8 * B + 4) := hfit_val
  have hfit_1 : Fits w 1 := hfit_B.of_le (by omega)
  have hfit_mask : Fits w (2 ^ d) := mask_fits_of_valueEnvelope hfit_val
  have hfit_d : Fits w d := hfit_mask.of_le Nat.lt_two_pow_self.le
  have hW_le_B : W ≤ B := by
    dsimp only [B]
    have h1 : 1 ≤ 8 ^ d := Nat.one_le_pow _ _ (by decide)
    have hW : W ≤ (W + 1) ^ 2 := by rw [sq]; nlinarith
    exact hW.trans (Nat.le_mul_of_pos_left _ h1)
  let x₀ := (x.set rZero 0).set rOne 1
  have hinit_zo : ExecWithin (B := .standard) w (ram[ rZero ← #0; rOne ← #1 ]) x x₀ 2 := by
    wram_exec
  obtain ⟨s₀, hinit0, hs₀_root, hs₀_free, hs₀_rep, hs₀_frame, hs₀_regs⟩ :=
    exec_trieInit (d := d) x₀ (by simp [x₀]) (by simp [x₀]) (by simpa [x₀] using hfree)
      (by omega) (hfit_free.of_le (by omega))
  let s₁ := (s₀.set rCellSaved free).set rCellIdx 0
  have hinit1 : ExecWithin (B := .standard) w
      (ram[ rCellSaved ← rTrieRoot; rCellIdx ← #0 ]) s₀ s₁ 2 := by
    wram_exec [hs₀_root]
  let P (p : ℕ) (s : Data numRegs) : Prop :=
    s.regs rZero = 0 ∧ s.regs rOne = 1 ∧ s.regs rDim = d ∧
    s.regs rCurDomPtr = entryPtr ∧ s.regs rCurDomLen = es.length ∧
    s.regs rCellSaved = free ∧
    ∃ (curFree : ℕ) (S : Set ℕ) (fnZ : ℕ → ℤ), s.regs rFree = curFree ∧
      free + 2 ≤ curFree ∧ curFree ≤ free + 2 + 2 * d * p ∧
      S ⊆ Set.Ico free curFree ∧
      TrieRep s.mem d free S (fun m => Signed.encode (fnZ m)) ∧
      (∀ m, (fnZ m).natAbs ≤ entryAbsSum (es.take p)) ∧
      (∀ X : Finset (Fin d), fnZ (setMask X) = evalEntries (es.take p) X) ∧
      (∀ a, a < free ∨ curFree ≤ a → s.mem a = x.mem a)
  have hbody (s : Data numRegs) (hs : P (s.regs rCellIdx) s) (hp : s.regs rCellIdx < es.length) :
      ∃ z, ExecWithin w buildInputStep s z (23 * d + 38) ∧
        P (s.regs rCellIdx + 1) z ∧ z.regs rCellIdx = s.regs rCellIdx + 1 := by
    generalize hp_eq : s.regs rCellIdx = p at hs hp ⊢
    dsimp only [P] at hs
    obtain ⟨hsz, hso, hsd, hsep, hsel, hssav, curFree, S, fnZ, hsfr, hcf_lo, hcf_hi,
      hS_sub, hsrep, hfnZ_abs, hfnZ_eq, hsframe⟩ := hs
    obtain ⟨hmk_p, hv_p⟩ := he_mem p hp
    have hrmk : s.mem (entryPtr + (p + p)) = setMask es[p].1 := by
      have : entryPtr + (p + p) = entryPtr + 2 * p := by omega
      rw [this, hsframe _ (Or.inl (by omega))]; exact hmk_p
    have hrv : s.mem (entryPtr + (p + p) + 1) = Signed.encode es[p].2 := by
      have : entryPtr + (p + p) + 1 = entryPtr + 2 * p + 1 := by omega
      rw [this, hsframe _ (Or.inl (by omega))]; exact hv_p
    have hf_2p : Fits w (p + p) := hfit_free.of_le (by omega)
    have hf_ep2p : Fits w (entryPtr + (p + p)) := hfit_free.of_le (by omega)
    have hf_ep2p1 : Fits w (entryPtr + (p + p) + 1) := hfit_free.of_le (by omega)
    have hst : ∃ u₀, ExecWithin w buildInputLoadCode s u₀ 6 ∧
        u₀.regs rTrieKey = setMask es[p].1 ∧
        u₀.regs (Signed.right (r := 47)) = Signed.encode es[p].2 ∧
        u₀.regs rTrieRoot = free ∧ u₀.mem = s.mem := by
      unfold buildInputLoadCode
      wram_exec [hso, hsep, hp_eq, hssav, hrmk, hrv]
      wram_simp [hrmk, hrv]
    obtain ⟨u₀, he_ld, hu₀_key, hu₀_right, hu₀_root, hu₀_mem⟩ := hst
    have hu₀_regs : ∀ i,
        i ≠ rGenTmp ∧ i ≠ rTrieKey ∧ i ≠ Signed.right (r := 47) ∧ i ≠ rTrieRoot →
          u₀.regs i = s.regs i :=
      fun i hi => he_ld.regs_eq (buildInputLoadCode_preserves i hi)
    have htake_sum : entryAbsSum (es.take p) + es[p].2.natAbs = entryAbsSum (es.take (p + 1)) := by
      rw [List.take_succ_eq_append_getElem hp]
      simp only [entryAbsSum, List.map_append, List.map_cons, List.map_nil,
        List.sum_append, List.sum_cons, List.sum_nil, add_zero]
    have htake1_le_W : entryAbsSum (es.take (p + 1)) ≤ W := by
      refine le_trans ?_ hes_W
      dsimp only [entryAbsSum]
      conv_rhs => rw [← List.take_append_drop (p + 1) es]
      rw [List.map_append, List.sum_append]
      exact Nat.le_add_right _ _
    have hcf_fit : Fits w (curFree + 2 * d) := by
      have : curFree + 2 * d ≤ free + 2 + 2 * d * es.length := by
        calc curFree + 2 * d ≤ free + 2 + 2 * d * p + 2 * d := Nat.add_le_add_right hcf_hi _
          _ = free + 2 + 2 * d * (p + 1) := by ring
          _ ≤ free + 2 + 2 * d * es.length :=
              Nat.add_le_add_left (Nat.mul_le_mul_left (2 * d) (by omega)) _
      exact hfit_free.of_le this
    obtain ⟨u₁, S', free', he_add, hu₁_fr, hcf_le', hfree'_le, hS'_sub, hu₁_frame,
      hu₁_rep, hu₁_regs⟩ :=
      exec_trieAdd (root := free) (key := setMask es[p].1) (delta := es[p].2)
        (free := curFree) (B := B) (fnZ := fnZ) (lo := free) u₀
        ((hu₀_regs rZero (by decide)).trans hsz)
        ((hu₀_regs rOne (by decide)).trans hso)
        ((hu₀_regs rDim (by decide)).trans hsd)
        hu₀_root hu₀_key hu₀_right
        ((hu₀_regs rFree (by decide)).trans hsfr)
        hfree_pos (by omega) (by omega) hS_sub (by rwa [hu₀_mem])
        (setMask_lt _)
        (fun m => (hfnZ_abs m).trans (by omega))
        (by omega)
        hfit_B hcf_fit hfit_d (hfit_mask.of_le (setMask_lt _).le)
    have hu₁_idx : u₁.regs rCellIdx = p :=
      (hu₁_regs rCellIdx ⟨by decide, by decide, Or.inr (by decide)⟩).trans
        ((hu₀_regs rCellIdx (by decide)).trans hp_eq)
    have hu₁_o : u₁.regs rOne = 1 :=
      (hu₁_regs rOne ⟨by decide, by decide, Or.inl (by decide)⟩).trans
        ((hu₀_regs rOne (by decide)).trans hso)
    have hf_p1 : Fits w (p + 1) := hfit_free.of_le (by omega)
    let z := u₁.set rCellIdx (p + 1)
    have he_inc : ExecWithin (B := .standard) w (ram[ rCellIdx ← rCellIdx + rOne ]) u₁ z 1 := by
      wram_exec [hu₁_idx, hu₁_o]
    have hstep_tot : ExecWithin w buildInputStep s z (23 * d + 38) :=
      (he_ld.seq (he_add.seq he_inc)).mono (by omega)
    have kz (i : Fin numRegs) (hi_ne : i ≠ rCellIdx)
        (ha : 9 ≤ i.val ∧ i ≠ rFree ∧ (i.val < 18 ∨ 23 ≤ i.val))
        (hl : i ≠ rGenTmp ∧ i ≠ rTrieKey ∧ i ≠ Signed.right (r := 47) ∧ i ≠ rTrieRoot) :
        z.regs i = s.regs i := by
      simp only [z, Data.set_regs_of_ne hi_ne]
      exact (hu₁_regs i ha).trans (hu₀_regs i hl)
    refine ⟨z, hstep_tot, ?_, by simp [z]⟩
    dsimp only [P]
    refine ⟨(kz rZero (by decide) ⟨by decide, by decide, Or.inl (by decide)⟩ (by decide)).trans hsz,
      (kz rOne (by decide) ⟨by decide, by decide, Or.inl (by decide)⟩ (by decide)).trans hso,
      (kz rDim (by decide) ⟨by decide, by decide, Or.inl (by decide)⟩ (by decide)).trans hsd,
      (kz rCurDomPtr (by decide) ⟨by decide, by decide, Or.inr (by decide)⟩ (by decide)).trans hsep,
      (kz rCurDomLen (by decide) ⟨by decide, by decide, Or.inr (by decide)⟩ (by decide)).trans hsel,
      (kz rCellSaved (by decide) ⟨by decide, by decide, Or.inr (by decide)⟩ (by decide)).trans
        hssav,
      free', S', fun m => if m % 2 ^ d = setMask es[p].1 then fnZ (setMask es[p].1) + es[p].2
        else fnZ m,
      by simp [z, hu₁_fr], by omega, ?_, hS'_sub, hu₁_rep, ?_, ?_, ?_⟩
    · calc free' ≤ curFree + 2 * d := hfree'_le
        _ ≤ free + 2 + 2 * d * p + 2 * d := Nat.add_le_add_right hcf_hi _
        _ = free + 2 + 2 * d * (p + 1) := by ring
    · intro m
      dsimp only
      rw [← htake_sum]
      split_ifs
      · exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add_right (hfnZ_abs _) _)
      · exact (hfnZ_abs m).trans (Nat.le_add_right _ _)
    · intro X
      dsimp only
      rw [Nat.mod_eq_of_lt (setMask_lt X), List.take_succ_eq_append_getElem hp]
      simp only [evalEntries, List.foldl_append, List.foldl_cons, List.foldl_nil,
        setMask_injective.eq_iff]
      rw [← evalEntries]
      by_cases hX : X = es[p].1
      · subst hX; simp [hfnZ_eq]
      · simp [hX, hfnZ_eq]
    · intro a ha
      rcases ha with ha_lo | ha_hi
      · exact (hu₁_frame a (Or.inl ha_lo)).trans
          ((congrFun hu₀_mem a).trans (hsframe a (Or.inl ha_lo)))
      · exact (hu₁_frame a (Or.inr ha_hi)).trans
          ((congrFun hu₀_mem a).trans (hsframe a (Or.inr (by omega))))
  have hs₁P : P (s₁.regs rCellIdx) s₁ := by
    dsimp only [P]
    have hs₁_idx : s₁.regs rCellIdx = 0 := by simp [s₁]
    rw [hs₁_idx, List.take_zero]
    refine ⟨by simpa [s₁, x₀] using hs₀_regs rZero (by decide),
      by simpa [s₁, x₀] using hs₀_regs rOne (by decide),
      by simpa [s₁, x₀] using (hs₀_regs rDim (by decide)).trans (by simpa [x₀] using hd),
      by simpa [s₁, x₀] using (hs₀_regs rCurDomPtr (by decide)).trans (by simpa [x₀] using hep),
      by simpa [s₁, x₀] using (hs₀_regs rCurDomLen (by decide)).trans (by simpa [x₀] using hel),
      by simp [s₁],
      free + 2, {free, free + 1}, fun _ => 0,
      by simp [s₁, hs₀_free], le_rfl, by omega, ?_, hs₀_rep, by simp [entryAbsSum],
      by simp [evalEntries], fun a ha => hs₀_frame a ⟨by omega, by omega⟩⟩
    intro a ha
    rcases ha with rfl | ha1
    · exact ⟨le_rfl, by omega⟩
    · have : a = free + 1 := by simpa using ha1
      subst this; exact ⟨by omega, by omega⟩
  obtain ⟨y, hloop, hyP, _⟩ := ExecWithin.loop_count P (fun s hs => hs.2.2.2.2.1) hbody
    (by simp [s₁]) hs₁P
  obtain ⟨_, _, _, _, _, hysav, free', S', fnZ, hyfr, hlo', hhi', hS', hyrep, _, hfnZ_eq,
    hyframe⟩ :=
    hyP
  rw [List.take_length] at hfnZ_eq
  have htot : ExecWithin w buildInputTrie x y (es.length * (23 * d + 40) + 11) := by
    refine (hinit_zo.seq (hinit0.seq (hinit1.seq hloop))).mono ?_
    have hs₁_idx : s₁.regs rCellIdx = 0 := by simp [s₁]
    rw [hs₁_idx, Nat.sub_zero]
    have h40 : 23 * d + 38 + 2 = 23 * d + 40 := by omega
    rw [h40]; omega
  refine ⟨y, free', fun m => Signed.encode (fnZ m), htot, hysav, hyfr, hlo', hhi',
    ⟨S', fun a ha => ⟨hfree_pos.trans (hS' ha).1, (hS' ha).2⟩, hyrep⟩,
    fun S => by dsimp only; rw [hfnZ_eq S], hyframe,
    fun i hi => htot.regs_eq (buildInputTrie_preserves i hi)⟩

private def inputPrepRightCode : Code .standard numRegs := ram[
  rTrieF ← rCellSaved;
  rGenTmp ← rCurDomLen + rCurDomLen;
  rCurDomPtr ← rCurDomPtr + rGenTmp;
  rGenTmp ← #4;
  rCurDomLen ← *rGenTmp ]

private theorem inputPrepRightCode_preserves (i : Fin numRegs) :
    i ≠ rTrieF ∧ i ≠ rGenTmp ∧ i ≠ rCurDomPtr ∧ i ≠ rCurDomLen →
      inputPrepRightCode.Preserves i := by
  decide +kernel +revert

private def inputPrepSolveCode : Code .standard numRegs := ram[
  rTrieG ← rCellSaved;
  rGenTmp ← rCurDomLen + rCurDomLen;
  rQueryPtr ← rCurDomPtr + rGenTmp ]

private theorem inputPrepSolveCode_preserves (i : Fin numRegs) :
    i ≠ rTrieG ∧ i ≠ rGenTmp ∧ i ≠ rQueryPtr → inputPrepSolveCode.Preserves i := by
  decide +kernel +revert

/-- Decode `Instance.encode` from `Data.init`, build the sparse input tries for `leftEntries` and
`rightEntries`, and invoke `solveFromTries`. -/
private def inputCode : Code .standard numRegs :=
  .seq (ram[
    rZero ← #0;
    rOne ← #1;
    rFree ← *rZero;
    rFree ← rFree + rOne;
    rGenTmp ← #1;
    rDim ← *rGenTmp;
    rGenTmp ← #2;
    rThresh ← *rGenTmp;
    rGenTmp ← #3;
    rCurDomLen ← *rGenTmp;
    rGenTmp ← #5;
    rQueryCount ← *rGenTmp;
    rCurDomPtr ← #6 ])
  (.seq buildInputTrie
    (.seq inputPrepRightCode
      (.seq buildInputTrie
        (.seq inputPrepSolveCode
          solveFromTries))))

/-- Complete flat `Program .standard 56` evaluating selected entries of covering product / ranked
subset convolution from `State.init inst.encode`. -/
def program : Program .standard numRegs :=
  inputCode.program Reg.outPtr

private theorem input_left_space_le (d s nL nR nQ H : ℕ) :
    (6 + 2 * (nL + nR) + nQ) + 2 + 2 * d * nL ≤
      solveSpace (10 + 2 * (d + 1) * (nL + nR) + nQ) d s nQ H := by
  dsimp only [solveSpace]; rw [sq]; nlinarith

private theorem input_right_space_le {d s nL nR nQ H free₁ : ℕ}
    (h1 : free₁ ≤ (6 + 2 * (nL + nR) + nQ) + 2 + 2 * d * nL) :
    free₁ + 2 + 2 * d * nR ≤
      solveSpace (10 + 2 * (d + 1) * (nL + nR) + nQ) d s nQ H := by
  dsimp only [solveSpace]; rw [sq]; nlinarith

private theorem input_bf_le {d nL nR nQ free₁ bf : ℕ}
    (h1 : free₁ ≤ (6 + 2 * (nL + nR) + nQ) + 2 + 2 * d * nL)
    (h2 : bf ≤ free₁ + 2 + 2 * d * nR) :
    bf ≤ 10 + 2 * (d + 1) * (nL + nR) + nQ := by
  nlinarith

private theorem input_total_time_le {d nL nR nQ L H : ℕ} (hL : 1 ≤ L) :
    13 + (nL * (23 * d + 40) + 11 + (5 + (nR * (23 * d + 40) + 11 +
      (3 + 200 * (d + 1) ^ 2 * (L + nQ * H))))) ≤
      250 * (d + 1) ^ 2 * (nL + nR + L + nQ * H) - 1 := by
  obtain ⟨Lp, rfl⟩ : ∃ Lp, L = Lp + 1 := ⟨L - 1, (Nat.sub_add_cancel hL).symm⟩
  have hid :
      (13 + (nL * (23 * d + 40) + 11 + (5 + (nR * (23 * d + 40) + 11 +
        (3 + 200 * (d + 1) ^ 2 * ((Lp + 1) + nQ * H))))) + 1) +
      ((nL + nR) * (250 * d ^ 2 + 477 * d + 210) + (50 * d ^ 2 + 100 * d + 6) +
        Lp * (50 * (d + 1) ^ 2) + nQ * H * (50 * (d + 1) ^ 2)) =
      250 * (d + 1) ^ 2 * (nL + nR + (Lp + 1) + nQ * H) := by ring
  omega

private theorem exec_inputCode (inst : Instance) {w : ℕ} (hw : inst.FitsWidth w) :
    ∃ y, ExecWithin w inputCode (.init inst.encode) y (inst.timeBound - 1) ∧
      outputList y.mem (y.regs Reg.outPtr) =
        (inst.queries.map (coveringProduct inst.leftFn inst.rightFn)).map Signed.encode ∧
      Fits w (y.regs Reg.outPtr + inst.queries.length) := by
  obtain ⟨hsp, hval⟩ := hw
  let x : Data numRegs := .init inst.encode
  generalize hnL_def : inst.leftEntries.length = nL
  generalize hnR_def : inst.rightEntries.length = nR
  generalize hnQ_def : inst.queries.length = nQ
  have hnum_eq : inst.numEntries = nL + nR := by
    rw [Instance.numEntries, hnL_def, hnR_def]
  let initFree := 6 + 2 * (nL + nR) + nQ
  have hx0 : x.mem 0 = 5 + 2 * (nL + nR) + nQ := by
    rw [Data.init_mem_zero, inst.length_encode, hnum_eq, hnQ_def]
  have hhdr : (Block.mk 1 5).Realizes x.mem
      [inst.d, inst.s, nL, nR, nQ].get := by
    rw [← hnL_def, ← hnR_def, ← hnQ_def]
    simpa [x, Instance.encode, List.append_assoc] using
      Data.init_realizes_append (r := numRegs) []
        [inst.d, inst.s, inst.leftEntries.length, inst.rightEntries.length, inst.queries.length]
        (encodeEntries inst.leftEntries ++ encodeEntries inst.rightEntries ++
          inst.queries.map setMask)
  have hm1 : x.mem 1 = inst.d := hhdr ⟨0, by decide⟩
  have hm2 : x.mem 2 = inst.s := hhdr ⟨1, by decide⟩
  have hm3 : x.mem 3 = nL := hhdr ⟨2, by decide⟩
  have hm4 : x.mem 4 = nR := hhdr ⟨3, by decide⟩
  have hm5 : x.mem 5 = nQ := hhdr ⟨4, by decide⟩
  have hleft_blk : (Block.mk 6 (encodeEntries inst.leftEntries).length).Realizes x.mem
      (encodeEntries inst.leftEntries).get := by
    simpa [x, Instance.encode, List.append_assoc] using
      Data.init_realizes_append (r := numRegs)
        [inst.d, inst.s, inst.leftEntries.length, inst.rightEntries.length, inst.queries.length]
        (encodeEntries inst.leftEntries)
        (encodeEntries inst.rightEntries ++ inst.queries.map setMask)
  have hright_blk : (Block.mk (6 + 2 * nL) (encodeEntries inst.rightEntries).length).Realizes x.mem
      (encodeEntries inst.rightEntries).get := by
    have hpre_len : ([inst.d, inst.s, inst.leftEntries.length, inst.rightEntries.length,
        inst.queries.length] ++ encodeEntries inst.leftEntries).length + 1 =
        6 + 2 * nL := by simp [hnL_def]; omega
    rw [← hpre_len]
    simpa [x, Instance.encode, List.append_assoc] using
      Data.init_realizes_append (r := numRegs)
        ([inst.d, inst.s, inst.leftEntries.length, inst.rightEntries.length,
          inst.queries.length] ++ encodeEntries inst.leftEntries)
        (encodeEntries inst.rightEntries)
        (inst.queries.map setMask)
  have hquery_blk :
      (Block.mk (6 + 2 * (nL + nR)) (inst.queries.map setMask).length).Realizes
        x.mem (inst.queries.map setMask).get := by
    have hpre_len : ([inst.d, inst.s, inst.leftEntries.length, inst.rightEntries.length,
        inst.queries.length] ++ encodeEntries inst.leftEntries ++
        encodeEntries inst.rightEntries).length + 1 = 6 + 2 * (nL + nR) := by
      simp [hnL_def, hnR_def]; omega
    rw [← hpre_len]
    simpa [x, Instance.encode, List.append_assoc] using
      Data.init_realizes_append (r := numRegs)
        ([inst.d, inst.s, inst.leftEntries.length, inst.rightEntries.length,
          inst.queries.length] ++ encodeEntries inst.leftEntries ++
          encodeEntries inst.rightEntries)
        (inst.queries.map setMask) []
  have hleft_mem : ∀ p (hp : p < inst.leftEntries.length),
      x.mem (6 + 2 * p) = setMask inst.leftEntries[p].1 ∧
      x.mem (6 + 2 * p + 1) = Signed.encode inst.leftEntries[p].2 := by
    intro p hp
    obtain ⟨h0, h1⟩ := getElem_encodeEntries inst.leftEntries p hp
    have hr0 : x.mem (6 + 2 * p) = (encodeEntries inst.leftEntries)[2 * p]'(by simp; omega) :=
      hleft_blk ⟨2 * p, by simp; omega⟩
    have hr1 : x.mem (6 + (2 * p + 1)) =
        (encodeEntries inst.leftEntries)[2 * p + 1]'(by simp; omega) :=
      hleft_blk ⟨2 * p + 1, by simp; omega⟩
    rw [← Nat.add_assoc] at hr1
    exact ⟨hr0.trans h0, hr1.trans h1⟩
  have hright_mem : ∀ p (hp : p < inst.rightEntries.length),
      x.mem (6 + 2 * nL + 2 * p) = setMask inst.rightEntries[p].1 ∧
      x.mem (6 + 2 * nL + 2 * p + 1) = Signed.encode inst.rightEntries[p].2 := by
    intro p hp
    obtain ⟨h0, h1⟩ := getElem_encodeEntries inst.rightEntries p hp
    have hr0 : x.mem (6 + 2 * nL + 2 * p) =
        (encodeEntries inst.rightEntries)[2 * p]'(by simp; omega) :=
      hright_blk ⟨2 * p, by simp; omega⟩
    have hr1 : x.mem (6 + 2 * nL + (2 * p + 1)) =
        (encodeEntries inst.rightEntries)[2 * p + 1]'(by simp; omega) :=
      hright_blk ⟨2 * p + 1, by simp; omega⟩
    rw [← Nat.add_assoc] at hr1
    exact ⟨hr0.trans h0, hr1.trans h1⟩
  have hquery_mem : ∀ j (hj : j < inst.queries.length),
      x.mem (6 + 2 * (nL + nR) + j) = setMask inst.queries[j] := by
    intro j hj
    have hr : x.mem (6 + 2 * (nL + nR) + j) =
        (inst.queries.map setMask)[j]'(by simp; omega) :=
      hquery_blk ⟨j, by simp; omega⟩
    simpa using hr
  -- Header decode
  have hsp_eq : inst.spaceBound = solveSpace (10 + 2 * (inst.d + 1) * (nL + nR) + nQ)
      inst.d inst.s nQ (highPeak inst.s inst.queries) := by
    rw [Instance.spaceBound, hnum_eq, hnQ_def]
  have hsp' : Fits w (solveSpace (10 + 2 * (inst.d + 1) * (nL + nR) + nQ)
      inst.d inst.s nQ (highPeak inst.s inst.queries)) := hsp_eq ▸ hsp
  have hleft_sp := input_left_space_le inst.d inst.s nL nR nQ (highPeak inst.s inst.queries)
  have hf_if : Fits w initFree := hsp'.of_le (by dsimp [initFree]; omega)
  have hf_6 : Fits w 6 := hf_if.of_le (by dsimp [initFree]; omega)
  have hf_5 : Fits w 5 := hf_6.of_le (by omega)
  have hf_4 : Fits w 4 := hf_6.of_le (by omega)
  have hf_3 : Fits w 3 := hf_6.of_le (by omega)
  have hf_2 : Fits w 2 := hf_6.of_le (by omega)
  have hf_1 : Fits w 1 := hf_6.of_le (by omega)
  have hdec : ∃ u₀, ExecWithin (B := .standard) w (ram[
      rZero ← #0;
      rOne ← #1;
      rFree ← *rZero;
      rFree ← rFree + rOne;
      rGenTmp ← #1;
      rDim ← *rGenTmp;
      rGenTmp ← #2;
      rThresh ← *rGenTmp;
      rGenTmp ← #3;
      rCurDomLen ← *rGenTmp;
      rGenTmp ← #5;
      rQueryCount ← *rGenTmp;
      rCurDomPtr ← #6 ]) x u₀ 13 ∧
      u₀.regs rZero = 0 ∧ u₀.regs rOne = 1 ∧ u₀.regs rDim = inst.d ∧
      u₀.regs rThresh = inst.s ∧ u₀.regs rFree = initFree ∧
      u₀.regs rCurDomPtr = 6 ∧ u₀.regs rCurDomLen = inst.leftEntries.length ∧
      u₀.regs rQueryCount = inst.queries.length ∧ u₀.mem = x.mem := by
    wram_exec [hx0, hm1, hm2, hm3, hm5]
    refine ⟨rfl, rfl, rfl, rfl, ?_, rfl, hnL_def.symm, hnQ_def.symm, rfl⟩
    wram_simp [hx0, initFree]; omega
  obtain ⟨u₀, he_dec, hu₀z, hu₀o, hu₀d, hu₀s, hu₀fr, hu₀cdp, hu₀cdl, hu₀qc, hu₀mem⟩ := hdec
  -- Build left input trie
  have hf_left : Fits w (initFree + 2 + 2 * inst.d * inst.leftEntries.length) := by
    rw [hnL_def]; exact hsp'.of_le hleft_sp
  obtain ⟨u₁, free₁, fnF, he_bL, hu₁_sav, hu₁_fr, hlo_L, hhi_L, htrF, hf_eq, hfr_L, hreg_L⟩ :=
    exec_buildInputTrie (W := inst.weightSum) inst.leftEntries u₀
      hu₀d hu₀cdp hu₀cdl hu₀fr (by dsimp [initFree]; omega)
      (by rw [hnL_def]; dsimp [initFree]; omega)
      (by rwa [hu₀mem]) (Nat.le_add_right _ _) hval hf_left
  -- Prepare right input trie
  have hu₁_cdl : u₁.regs rCurDomLen = nL :=
    (hreg_L rCurDomLen (by decide)).trans (hu₀cdl.trans hnL_def)
  have hu₁_cdp : u₁.regs rCurDomPtr = 6 := (hreg_L rCurDomPtr (by decide)).trans hu₀cdp
  have hu₁_m4 : u₁.mem 4 = nR := by rw [hfr_L 4 (Or.inl (by dsimp [initFree]; omega)), hu₀mem, hm4]
  have hf_2nL : Fits w (nL + nL) := hf_if.of_le (by dsimp [initFree]; omega)
  have hf_6_2nL : Fits w (6 + (nL + nL)) := hf_if.of_le (by dsimp [initFree]; omega)
  have hp_R_st : ∃ u₂, ExecWithin w inputPrepRightCode u₁ u₂ 5 ∧
      u₂.regs rTrieF = initFree ∧ u₂.regs rCurDomPtr = 6 + 2 * nL ∧
      u₂.regs rCurDomLen = inst.rightEntries.length ∧ u₂.mem = u₁.mem := by
    unfold inputPrepRightCode
    wram_exec [hu₁_sav, hu₁_cdl, hu₁_cdp, hu₁_m4]
    refine ⟨rfl, ?_, ?_, rfl⟩
    · wram_simp; omega
    · wram_simp [hu₁_m4]; exact hnR_def.symm
  obtain ⟨u₂, he_pR, hu₂_tF, hu₂_cdp, hu₂_cdl, hu₂_mem⟩ := hp_R_st
  have hreg_pR : ∀ i, i ≠ rTrieF ∧ i ≠ rGenTmp ∧ i ≠ rCurDomPtr ∧ i ≠ rCurDomLen →
      u₂.regs i = u₁.regs i :=
    fun i hi => he_pR.regs_eq (inputPrepRightCode_preserves i hi)
  -- Build right input trie
  rw [hnL_def] at hhi_L
  have hright_sp := input_right_space_le (s := inst.s) (H := highPeak inst.s inst.queries) hhi_L
  have hf_right : Fits w (free₁ + 2 + 2 * inst.d * inst.rightEntries.length) := by
    rw [hnR_def]; exact hsp'.of_le hright_sp
  have hright_mem_u₂ : ∀ p (hp : p < inst.rightEntries.length),
      u₂.mem (6 + 2 * nL + 2 * p) = setMask inst.rightEntries[p].1 ∧
      u₂.mem (6 + 2 * nL + 2 * p + 1) = Signed.encode inst.rightEntries[p].2 := by
    intro p hp
    have hpR : p < nR := hnR_def ▸ hp
    rw [hu₂_mem, hfr_L _ (Or.inl (by dsimp [initFree]; omega)),
      hfr_L _ (Or.inl (by dsimp [initFree]; omega)), hu₀mem]
    exact hright_mem p hp
  obtain ⟨u₃, baseFree, fnG, he_bR, hu₃_sav, hu₃_fr, hlo_R, hhi_R, htrG, hg_eq, hfr_R, hreg_R⟩ :=
    exec_buildInputTrie (W := inst.weightSum) inst.rightEntries u₂
      ((hreg_pR rDim (by decide)).trans ((hreg_L rDim (by decide)).trans hu₀d))
      hu₂_cdp hu₂_cdl
      ((hreg_pR rFree (by decide)).trans hu₁_fr) (by dsimp [initFree] at hlo_L; omega)
      (by rw [hnR_def]; dsimp [initFree] at hlo_L; omega)
      hright_mem_u₂ (Nat.le_add_left _ _) hval hf_right
  -- Prepare solveFromTries
  have hu₃_cdl : u₃.regs rCurDomLen = nR :=
    (hreg_R rCurDomLen (by decide)).trans (hu₂_cdl.trans hnR_def)
  have hu₃_cdp : u₃.regs rCurDomPtr = 6 + 2 * nL :=
    (hreg_R rCurDomPtr (by decide)).trans hu₂_cdp
  have hf_2nR : Fits w (nR + nR) := hf_if.of_le (by dsimp [initFree]; omega)
  have hf_qptr : Fits w (6 + 2 * nL + (nR + nR)) := hf_if.of_le (by dsimp [initFree]; omega)
  have hp_S_st : ∃ u₄, ExecWithin w inputPrepSolveCode u₃ u₄ 3 ∧
      u₄.regs rTrieG = free₁ ∧ u₄.regs rQueryPtr = 6 + 2 * (nL + nR) ∧
      u₄.mem = u₃.mem := by
    unfold inputPrepSolveCode
    wram_exec [hu₃_sav, hu₃_cdl, hu₃_cdp]
    refine ⟨rfl, ?_, rfl⟩
    wram_simp; omega
  obtain ⟨u₄, he_pS, hu₄_tG, hu₄_qp, hu₄_mem⟩ := hp_S_st
  have hreg_pS : ∀ i, i ≠ rTrieG ∧ i ≠ rGenTmp ∧ i ≠ rQueryPtr → u₄.regs i = u₃.regs i :=
    fun i hi => he_pS.regs_eq (inputPrepSolveCode_preserves i hi)
  rw [hnR_def] at hhi_R
  have hbf_le := input_bf_le hhi_L hhi_R
  have hf_solve_sp : Fits w (solveSpace baseFree inst.d inst.s inst.queries.length
      (highPeak inst.s inst.queries)) := by
    rw [hnQ_def]
    exact hsp'.of_le (by dsimp [solveSpace]; omega)
  have htrF_u₄ : HoldsTrie u₄.mem baseFree inst.d initFree fnF := by
    rw [hu₄_mem]
    refine (htrF.congr_below fun a ha => ?_).mono_bound (by omega)
    rw [hfr_R a (Or.inl ha), hu₂_mem]
  have hq_mem_u₄ : ∀ j (hj : j < inst.queries.length),
      u₄.mem (6 + 2 * (nL + nR) + j) = setMask inst.queries[j] := by
    intro j hj
    have hjQ : j < nQ := hnQ_def ▸ hj
    rw [hu₄_mem, hfr_R _ (Or.inl (by dsimp [initFree] at hlo_L hlo_R; omega)),
      hu₂_mem, hfr_L _ (Or.inl (by dsimp [initFree]; omega)), hu₀mem]
    exact hquery_mem j hj
  obtain ⟨y, he_solve, hy_list, hy_fit, _⟩ :=
    exec_solveFromTries (W := inst.weightSum) (f := inst.leftFn) (g := inst.rightFn) u₄
      ((hreg_pS Reg.dim (by decide)).trans ((hreg_R Reg.dim (by decide)).trans
        ((hreg_pR Reg.dim (by decide)).trans ((hreg_L Reg.dim (by decide)).trans hu₀d))))
      ((hreg_pS Reg.thresh (by decide)).trans ((hreg_R Reg.thresh (by decide)).trans
        ((hreg_pR Reg.thresh (by decide)).trans ((hreg_L Reg.thresh (by decide)).trans hu₀s))))
      ((hreg_pS Reg.free (by decide)).trans hu₃_fr)
      (by dsimp [initFree] at hlo_L hlo_R; omega)
      ((hreg_pS Reg.trieF (by decide)).trans ((hreg_R Reg.trieF (by decide)).trans hu₂_tF))
      hu₄_tG hu₄_qp
      ((hreg_pS Reg.queryCount (by decide)).trans ((hreg_R Reg.queryCount (by decide)).trans
        ((hreg_pR Reg.queryCount (by decide)).trans
          ((hreg_L Reg.queryCount (by decide)).trans hu₀qc))))
      (by rw [hnQ_def]; dsimp [initFree] at hlo_L hlo_R; omega)
      hq_mem_u₄ htrF_u₄ (by rwa [hu₄_mem]) hf_eq hg_eq
      (fun S => (natAbs_evalEntries_le _ S).trans (Nat.le_add_right _ _))
      (fun S => (natAbs_evalEntries_le _ S).trans (Nat.le_add_left _ _))
      hf_solve_sp hval
  have htot : ExecWithin w inputCode x y (inst.timeBound - 1) := by
    refine (he_dec.seq (he_bL.seq (he_pR.seq (he_bR.seq (he_pS.seq he_solve))))).mono ?_
    rw [Instance.timeBound, hnum_eq, hnL_def, hnR_def, hnQ_def]
    exact input_total_time_le (lowCount_pos inst.d inst.s)
  exact ⟨y, htot, hy_list, hnQ_def ▸ hy_fit⟩

/-- `program` computes the encoded covering-product query answers within `Instance.timeBound`
instructions on every width satisfying `Instance.FitsWidth`. -/
theorem computesListInTime_program :
    program.ComputesListInTime (fun _ => Instance.encode) (fun inst _ => inst.timeBound)
      Instance.FitsWidth
      (fun inst => (inst.queries.map (coveringProduct inst.leftFn inst.rightFn)).map
        Signed.encode) := by
  have hraw := Code.computesListInTime_program inputCode Reg.outPtr
    (encode := fun _ => Instance.encode) (time := fun inst _ => inst.timeBound - 1)
    (allowed := Instance.FitsWidth)
    (f := fun inst =>
      (inst.queries.map (coveringProduct inst.leftFn inst.rightFn)).map Signed.encode)
    fun inst w hw _ => by simpa using exec_inputCode inst hw
  refine hraw.mono (fun inst _ => ?_) (fun _ _ h => h)
  have hpos : 0 < inst.timeBound := by
    dsimp only [Instance.timeBound]
    have h1 : 0 < 250 * (inst.d + 1) ^ 2 :=
      Nat.mul_pos (by decide) (Nat.pow_pos (Nat.succ_pos inst.d))
    have h2 : 0 < inst.numEntries + lowCount inst.d inst.s +
        inst.queries.length * max 1 (highPeak inst.s inst.queries) := by
      have := lowCount_pos inst.d inst.s
      omega
    exact Nat.mul_pos h1 h2
  omega

/-- **Complete initialized Word-RAM bound for [ChanItakuraMaYu2026], Theorem 2.2 / Problem 2.1.**
Given a sparse weighted set-function instance `inst` over `Fin inst.d` where `leftEntries` have
size `t₁`, `rightEntries` have size `t₂`, and `queries` have size `t₁ + t₂` with
`inst.s ≤ t₁ + t₂` (set `t₁ = t₂ = t` for Theorem 2.2), running `program` from
`State.init inst.encode` halts via `ExecutesList` with the encoded subset-convolution answers in at
most `250 * (inst.d + 1) ^ 2 * (inst.numEntries + lowCount inst.d inst.s +
inst.queries.length * highCount (t₁ + t₂) inst.s)` instructions. -/
theorem executesList_program (inst : Instance) {t₁ t₂ w : ℕ}
    (hleft : ∀ p ∈ inst.leftEntries, p.2 ≠ 0 → #p.1 = t₁)
    (hright : ∀ p ∈ inst.rightEntries, p.2 ≠ 0 → #p.1 = t₂)
    (hqueries : ∀ C ∈ inst.queries, #C = t₁ + t₂)
    (hs : inst.s ≤ t₁ + t₂)
    (hfit_space : Fits w (solveSpace
      (10 + 2 * (inst.d + 1) * inst.numEntries + inst.queries.length)
      inst.d inst.s inst.queries.length (highCount (t₁ + t₂) inst.s)))
    (hfit_val : Fits w (valueEnvelope inst.d inst.weightSum)) :
    ∃ n, ExecutesList w program (.init inst.encode)
        ((inst.queries.map (subsetConvolution inst.leftFn inst.rightFn)).map Signed.encode) n ∧
      n ≤ 250 * (inst.d + 1) ^ 2 *
        (inst.numEntries + lowCount inst.d inst.s +
          inst.queries.length * highCount (t₁ + t₂) inst.s) := by
  have hpk_le : highPeak inst.s inst.queries ≤ highCount (t₁ + t₂) inst.s :=
    highPeak_le_of_forall_card_eq inst.s (t₁ + t₂) hqueries
  have hhc_pos : 1 ≤ highCount (t₁ + t₂) inst.s := highCount_pos hs
  have hmax_le : max 1 (highPeak inst.s inst.queries) ≤ highCount (t₁ + t₂) inst.s :=
    max_le hhc_pos hpk_le
  have hw : inst.FitsWidth w :=
    ⟨hfit_space.of_le (by
      dsimp only [Instance.spaceBound, solveSpace]
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _), hfit_val⟩
  obtain ⟨n, hex, hn⟩ := computesListInTime_program inst w hw hw.inputFits
  dsimp only at hex hn
  have heq_conv : inst.queries.map (coveringProduct inst.leftFn inst.rightFn) =
      inst.queries.map (subsetConvolution inst.leftFn inst.rightFn) :=
    List.map_congr_left fun C hC =>
      coveringProduct_eq_subsetConvolution (evalEntries_ranked hleft) (evalEntries_ranked hright)
        (hqueries C hC)
  rw [heq_conv] at hex
  refine ⟨n, hex, hn.trans ?_⟩
  dsimp only [Instance.timeBound]
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.mul_le_mul_left _ hmax_le) _)

end Cslib.Algorithms.WordRAM.TrimmedYates
