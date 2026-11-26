/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import CslibFrontier.Crypto.Primitives.PRF.PrefixFreeEncoding
public import CslibFrontier.Foundations.Data.BitString.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import CslibFrontier.Foundations.Data.BitString.Binary
import CslibFrontier.Foundations.Data.BitString.List.Rows

/-!
# Common block extensions for flat queries

These are query preparation steps of [BonehShoup2023], v0.6, Theorems 7.3 and 7.4
(printed pp. 258–260). For a pair, the choice uses the first block after the shorter word.
For a batch, it searches for a block absent from the complete rows of all words.

## Main definitions

* `Cslib.Crypto.PRF.separatingWordBlock`: choose a shared block of the given width.
* `Cslib.Crypto.PRF.freshBatchWordBlock`: search for a block absent from a batch of flat words.

## Main results

* `Cslib.Crypto.PRF.separatingWordBlock_prefix_incomparable`: at positive width, appending the
  chosen block to two distinct aligned queries makes their words prefix-incomparable.
* `Cslib.Crypto.PRF.computableInPolyTime_separatingWordBlock`: the choice runs in polynomial time
  on all inputs.
* `Cslib.Crypto.PRF.freshBatchWordBlock_eq_map_freshBatchBlock`: the flat and indexed searches
  agree after splitting the messages into blocks.
* `Cslib.Crypto.PRF.isPrefixFree_append_of_freshBatchWordBlock_eq_some`: extending aligned words
  by the returned block makes a prefix-free set.
* `Cslib.Crypto.PRF.freshBatchWordBlock_isSome_of_sum_div_lt`: the search succeeds when
  the alphabet is larger than the total number of complete blocks.
* `Cslib.Crypto.PRF.computableInPolyTime_freshBatchWordBlock`: deterministic polynomial time
  with unary width and a framed list of words.
-/

public section

namespace Cslib.Crypto.PRF

open Turing.MultiTapeTM

/-- Choose a common extension block from the all-zero and all-one blocks for two flat queries.
Only the complete input blocks inform the choice. -/
@[expose] def separatingWordBlock (width : ℕ) (u v : List Bool) : List Bool :=
  separatingBlock (List.replicate width false) (List.replicate width true)
    (BitString.listRows (u.length / width) width u)
    (BitString.listRows (v.length / width) width v)

/-- The result has the declared width on every input. -/
@[simp] theorem length_separatingWordBlock (width : ℕ) (u v : List Bool) :
    (separatingWordBlock width u v).length = width := by
  simp [separatingWordBlock, separatingBlock, apply_ite]

/-- The common extension makes two distinct, block-aligned queries prefix-incomparable
as bit lists. -/
theorem separatingWordBlock_prefix_incomparable {width : ℕ} (hwidth : 0 < width)
    {u v : List Bool} (hu : width ∣ u.length) (hv : width ∣ v.length) (hne : u ≠ v) :
    let c := separatingWordBlock width u v
    (¬ u ++ c <+: v ++ c) ∧ (¬ v ++ c <+: u ++ c) := by
  let us := BitString.listRows (u.length / width) width u
  let vs := BitString.listRows (v.length / width) width v
  let c := separatingWordBlock width u v
  have huf : us.flatten = u := BitString.flatten_listRows_of_length (Nat.div_mul_cancel hu).symm
  have hvf : vs.flatten = v := BitString.flatten_listRows_of_length (Nat.div_mul_cancel hv).symm
  have hblocks : List.replicate width false ≠ List.replicate width true := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hwidth.ne'
    simp [List.replicate_succ]
  have hsep := separatingBlock_prefix_incomparable hblocks
    fun he => hne (huf.symm.trans ((congrArg List.flatten he).trans hvf))
  have rowWidth {rows : List (List Bool)} (h : ∀ row ∈ rows, row.length = width) :
      ∀ row ∈ rows ++ [c], row.length = width := by
    simpa only [List.forall_mem_append, List.forall_mem_singleton] using
      ⟨h, length_separatingWordBlock width u v⟩
  have hus := rowWidth (rows := us) fun _ => BitString.length_of_mem_listRows
  have hvs := rowWidth (rows := vs) fun _ => BitString.length_of_mem_listRows
  change (¬ u ++ c <+: v ++ c) ∧ (¬ v ++ c <+: u ++ c)
  rw [← huf, ← hvf, ← List.flatten_singleton (l := c),
    ← List.flatten_append, ← List.flatten_append]
  exact ⟨fun hp => hsep.1 (BitString.prefix_of_flatten_prefix hwidth hus hvs hp),
    fun hp => hsep.2 (BitString.prefix_of_flatten_prefix hwidth hvs hus hp)⟩

open ComputableInPolyTime in
/-- The input is a framed unary width, the framed first raw word, and the second raw word.
The common block is returned as a raw word in deterministic polynomial time. -/
theorem computableInPolyTime_separatingWordBlock :
    ComputableInPolyTime (fun p => separatingWordBlock p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encBits encBits)) encBits := by
  have hw := fst encUnary (encPair encBits encBits)
  have hu := (snd encUnary (encPair encBits encBits)).fst'
  have hv := (snd encUnary (encPair encBits encBits)).snd'
  have hnu := unary_div' hu.length_bits_comp hw
  have hnv := unary_div' hv.length_bits_comp hw
  have hru := bitsRowsWithInput hnu hw hu
  have hrv := bitsRowsWithInput hnv hw hv
  have hzero := (bitsReplicate false).comp hw
  have hone := (bitsReplicate true).comp hw
  have hnext := ite_decide (unary_le' hnu hnv)
    (optionGetDWithInput (getElem? hrv hnu) hzero)
    (optionGetDWithInput (getElem? hru hnv) hzero)
  simpa only [separatingWordBlock, separatingBlock, BitString.length_listRows,
    List.getD_eq_getElem?_getD, Function.comp_def] using ite' (beq hnext hzero) hone hzero

private def completeRows (width : ℕ) (word : List Bool) : List (List Bool) :=
  BitString.listRows (word.length / width) width word

/-- Find a fresh block for a batch of flat messages, reading only complete blocks.
The bounded search uses the little-endian order of `BitString.equivFin`. -/
def freshBatchWordBlock (width : ℕ) (messages : List (List Bool)) : Option (List Bool) :=
  findFreshBlock (size := 2 ^ width) (fun i => BitString.lowBits width i.val)
    (messages.flatMap (completeRows width))

/-- A block returned by the flat search has exactly the requested width. -/
theorem length_freshBatchWordBlock_of_eq_some {width : ℕ} {messages : List (List Bool)}
    {block : List Bool} (hblock : freshBatchWordBlock width messages = some block) :
    block.length = width := by
  unfold freshBatchWordBlock findFreshBlock at hblock
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hblock)
  simp

/-- Appending a block returned by the flat search makes the batch prefix-free at positive
width, provided each original word consists of complete blocks. -/
theorem isPrefixFree_append_of_freshBatchWordBlock_eq_some {width : ℕ}
    {messages : List (List Bool)} {block : List Bool} (hwidth : 0 < width)
    (haligned : ∀ word ∈ messages, width ∣ word.length)
    (hblock : freshBatchWordBlock width messages = some block) :
    InformationTheory.IsPrefixFree ((fun msg => msg ++ block) '' {msg | msg ∈ messages}) := by
  have hlen := length_freshBatchWordBlock_of_eq_some hblock
  unfold freshBatchWordBlock findFreshBlock at hblock
  have hprefix : InformationTheory.IsPrefixFree
      ((fun rows => rows ++ [block]) '' {rows | rows ∈ messages.map (completeRows width)}) :=
    isPrefixFree_append_of_notMem_flatten (by
      simpa only [List.flatten_eq_flatMap, List.flatMap_map, Function.comp_def, id_eq] using
        (show block ∉ messages.flatMap (completeRows width) by simpa using List.find?_some hblock))
  let extend (word : List Bool) := completeRows width word ++ [block]
  have hrows (word : List Bool) (row : List Bool) (hrow : row ∈ extend word) :
      row.length = width :=
    (List.mem_append.mp hrow).elim BitString.length_of_mem_listRows
      fun h => (List.mem_singleton.mp h).symm ▸ hlen
  have hflatten (word : List Bool) (hm : word ∈ messages) :
      (extend word).flatten = word ++ block := by
    simp only [extend, List.flatten_append, List.flatten_singleton, completeRows,
      BitString.flatten_listRows_of_length (Nat.div_mul_cancel (haligned word hm)).symm]
  rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ hpre
  dsimp only at hpre ⊢
  rw [← hflatten u hu, ← hflatten v hv] at hpre ⊢
  exact congrArg List.flatten (hprefix _ ⟨_, List.mem_map_of_mem hu, rfl⟩
    _ ⟨_, List.mem_map_of_mem hv, rfl⟩
    (BitString.prefix_of_flatten_prefix hwidth (hrows u) (hrows v) hpre))

/-- The word search returns the bit list of the same block as the indexed search, after splitting
each input into complete blocks. For aligned inputs this splitting represents the entire word. -/
theorem freshBatchWordBlock_eq_map_freshBatchBlock (width : ℕ) (messages : List (List Bool)) :
    freshBatchWordBlock width messages =
      (freshBatchBlock (messages.map fun word =>
        (BitString.listRows (word.length / width) width word).map (BitString.ofList width))).map
          List.ofFn := by
  let used := messages.flatMap (completeRows width)
  have hrows : (used.map (BitString.ofList width)).map List.ofFn = used := by
    rw [List.map_map]
    calc
      _ = used.map id := List.map_congr_left fun row hr => by
        obtain ⟨_, _, hrow⟩ := List.mem_flatMap.mp hr
        exact BitString.ofFn_ofList (BitString.length_of_mem_listRows hrow)
      _ = used := List.map_id used
  have hflatten : (messages.map fun word => (completeRows width word).map
      (BitString.ofList width)).flatten = used.map (BitString.ofList width) := by
    simp only [used, List.map_flatMap, List.flatMap_map, List.flatten_eq_flatMap, id_eq]
  have hcontains (block : BitString width) :
      used.contains (List.ofFn block) = (used.map (BitString.ofList width)).contains block := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.contains_iff_mem]
    conv_lhs => rw [← hrows, List.mem_map]
    exact ⟨fun ⟨other, hm, he⟩ => (List.ofFn_injective he) ▸ hm,
      fun hm => ⟨block, hm, rfl⟩⟩
  change findFreshBlock (size := 2 ^ width) (fun i => BitString.lowBits width i.val) used =
    (freshBatchBlock (messages.map fun word => (completeRows width word).map
      (BitString.ofList width))).map List.ofFn
  rw [freshBatchBlock, hflatten]
  simp only [findFreshBlock, List.find?_map, Option.map_map, Function.comp_def,
    BitString.lowBits_eq_ofFn_equivFin_symm, hcontains]
  have hsearch (count : ℕ) (hcount : count ≤ 2 ^ width) :
      ((List.finRange count).find? fun x => !(used.map (BitString.ofList width)).contains
        ((BitString.equivFin width).symm (Fin.castLE hcount x))).map
        (fun i => List.ofFn ((BitString.equivFin width).symm (Fin.castLE hcount i))) =
      ((List.range count).map (BitString.lowBits width)).find?
        (fun block => !used.contains block) := by
    rw [← List.map_coe_finRange_eq_range, List.map_map, List.find?_map]
    simp only [Function.comp_def, ← hcontains, ← BitString.lowBits_eq_ofFn_equivFin_symm,
      Fin.val_castLE]
  calc
    _ = ((List.range (min (2 ^ width) (used.length + 1))).map
        (BitString.lowBits width)).find? (fun block => !used.contains block) :=
      hsearch _ (min_le_left _ _)
    _ = _ := by
      refine Eq.trans ?_ (hsearch _ (min_le_left _ _)).symm
      rw [List.length_map]

/-- With more alphabet elements than complete block occurrences, the flat search succeeds. -/
theorem freshBatchWordBlock_isSome_of_sum_div_lt {width : ℕ} {messages : List (List Bool)}
    (hsize : (messages.map fun word => word.length / width).sum < 2 ^ width) :
    (freshBatchWordBlock width messages).isSome := by
  obtain ⟨block, hblock, _⟩ := isPrefixFree_append_freshBatchBlock
    (messages := messages.map fun word =>
      (BitString.listRows (word.length / width) width word).map (BitString.ofList width)) <| by
    simpa only [List.length_flatten, List.map_map, Function.comp_def, List.length_map,
      BitString.length_listRows] using hsize
  simp [freshBatchWordBlock_eq_map_freshBatchBlock, hblock]

open ComputableInPolyTime in
/-- The flat-word search runs in deterministic polynomial time. The input is a framed unary
width followed by a framed list of raw words, and the output is an option containing a raw word. -/
theorem computableInPolyTime_freshBatchWordBlock :
    ComputableInPolyTime (fun p => freshBatchWordBlock p.1 p.2)
      (encPair encUnary (encList encBits)) (encOption encBits) := by
  let input := encPair encUnary (encList encBits)
  have hw := fst encUnary (encList encBits)
  have hmessages := snd encUnary (encList encBits)
  have hrows : ComputableInPolyTime (fun p : ℕ × List Bool => completeRows p.1 p.2)
      (encPair encUnary encBits) (encList encBits) := by
    unfold completeRows
    fun_prop
  have hused := flatMapWith hrows hw hmessages
  have hcount : ComputableInPolyTime (fun p : ℕ × List (List Bool) =>
      min (2 ^ p.1) ((p.2.flatMap (completeRows p.1)).length + 1)) input encUnary := by
    simpa only [min_comm (2 ^ _), Function.comp_def] using binary_min_unary'
      (unary_add' ((length_list encBits).comp hused) (const 1)) (binary_two_pow.comp hw)
  have hcandidates := mapWithInput (f := fun (p : ℕ × List (List Bool)) i =>
    BitString.lowBits p.1 i) (range.comp hcount)
    (bitsLow (hw.comp (fst input encUnary)) (unary_to_binary.comp (snd input encUnary)))
  have hsearch := findWithInput (test := fun (p : ℕ × List (List Bool)) block =>
    !(p.2.flatMap (completeRows p.1)).contains block) hcandidates
    (bool_not.comp (contains (hused.comp (fst input encBits)) (snd input encBits)))
  simpa only [freshBatchWordBlock, findFreshBlock, ← List.map_coe_finRange_eq_range,
    List.map_map, Function.comp_def, Fin.val_castLE] using hsearch

end Cslib.Crypto.PRF
