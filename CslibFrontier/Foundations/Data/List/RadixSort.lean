/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate (Mathlib Data/List)

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn

/-!
# Radix sort and the check of neighbours

Records are pairs of a flag (`false`: table entry, `true`: lookup) and a key of `n` letters over
an arbitrary alphabet `B`. After one stable bucket pass for each letter (`srt`), records with equal
keys sit in contiguous blocks preserving their original order (`srt_eq`). Hence every lookup
belongs to the table if and only if, after sorting, every lookup has the same key as the record
immediately preceding it (`chk_table`).

This generic multi-letter alphabet formulation is separate from the unsigned binary-word
imperative radix sort in `CslibFrontier.Algorithms.WordRAM.RadixSort`.

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `Nc.Sort.Radix`.

## Main definitions

* `List.RadixSort.Rc`: a record pairing a lookup/entry flag with a `Fin n → B` key.
* `List.RadixSort.pass`: one stable distribution-and-collection pass along key coordinate `j`.
* `List.RadixSort.srt`: iterate `pass` over the first `j` coordinates.
* `List.RadixSort.keys`: all `j`-letter keys over `bs` in radix order.
* `List.RadixSort.chk`, `List.RadixSort.headOk`: neighbour equality and leading-entry predicates.

## Main results

* `List.RadixSort.srt_eq`: exact bucket-filter expansion of `srt`.
* `List.RadixSort.chk_srt`: neighbour check after `n` passes equals `headOk` on every key group.
* `List.RadixSort.chk_table`: after sorting a table followed by lookups, `chk` holds iff every
  lookup is in the table.
* `List.RadixSort.length_srt`: `srt` preserves list length.
-/

public section

namespace List.RadixSort

variable {n : ℕ} {B : Type*} [DecidableEq B]

/-- A record: a flag (`false` for a table entry, `true` for a lookup) and a key of length `n`. -/
abbrev Rc (n : ℕ) (B : Type*) := Bool × (Fin n → B)

/-- One radix pass: distribute records into buckets indexed by `bs` at position `j`. -/
@[expose] def pass (bs : List B) (j : Fin n) (l : List (Rc n B)) : List (Rc n B) :=
  bs.flatMap fun b => l.filter fun r => r.2 j = b

/-- The list after the first `j` radix passes. -/
@[expose] def srt (bs : List B) (l : List (Rc n B)) : ℕ → List (Rc n B)
  | 0 => l
  | j + 1 => if h : j < n then pass bs ⟨j, h⟩ (srt bs l j) else srt bs l j

/-- The length-`j` keys over `bs`, in the order produced by `srt`. -/
@[expose] def keys (bs : List B) : ℕ → List (List B)
  | 0 => [[]]
  | j + 1 => bs.flatMap fun b => (keys bs j).map fun k => k ++ [b]

omit [DecidableEq B] in
theorem mem_keys {bs : List B} (hbs : ∀ b, b ∈ bs) (j : ℕ) (k : List B) :
    k ∈ keys bs j ↔ k.length = j := by
  induction j generalizing k with
  | zero => simp [keys]
  | succ j ih =>
    simp only [keys, List.mem_flatMap, List.mem_map, ih]
    refine ⟨?_, fun h => ?_⟩
    · rintro ⟨_, -, _, rfl, rfl⟩
      simp
    · rcases List.eq_nil_or_concat k with rfl | ⟨k', b, rfl⟩
      · simp at h
      · exact ⟨b, hbs b, k', by simpa using h, by simp⟩

omit [DecidableEq B] in
theorem keys_nodup {bs : List B} (hn : bs.Nodup) (j : ℕ) : (keys bs j).Nodup := by
  induction j with
  | zero => simp [keys]
  | succ j ih =>
    rw [keys, List.nodup_flatMap]
    refine ⟨fun b _ => ih.map fun a b' h => by simpa using h, hn.imp fun {b b'} hne => ?_⟩
    simp only [Function.onFun, List.disjoint_left, List.mem_map]
    rintro _ ⟨a, -, rfl⟩ ⟨a', -, h⟩
    exact hne (by simpa using (List.append_inj' h rfl).2.symm)

theorem srt_eq (bs : List B) (l : List (Rc n B)) (j : ℕ) (hj : j ≤ n) :
    srt bs l j = (keys bs j).flatMap fun k =>
      l.filter fun r => (List.ofFn r.2).take j = k := by
  induction j with
  | zero => simp [srt, keys]
  | succ j ih =>
    have hlt : j < n := hj
    rw [srt, dite_eq_left hlt, ih hlt.le, pass, keys, List.flatMap_assoc]
    refine List.flatMap_congr fun b _ => ?_
    rw [List.filter_flatMap, List.flatMap_map]
    refine List.flatMap_congr fun k _ => ?_
    rw [List.filter_filter]
    refine List.filter_congr fun r _ => ?_
    rw [List.take_succ_eq_append_getElem (by simpa using hlt)]
    simp only [List.getElem_ofFn]
    by_cases e1 : (List.ofFn r.2).take j = k
    · subst e1; simp
    · simp [e1]

/-- Neighbour check: every lookup (`r.1 = true`) shares the key of its immediate predecessor `p`. -/
@[expose] def chk : Option (Fin n → B) → List (Rc n B) → Prop
  | _, [] => True
  | p, r :: l => (r.1 = false ∨ p = some r.2) ∧ chk (some r.2) l

/-- The first record of a non-empty list is a table entry (`r.1 = false`). -/
@[expose] def headOk : List (Rc n B) → Prop
  | [] => True
  | r :: _ => r.1 = false

omit [DecidableEq B] in
theorem chk_same (k : Fin n → B) (g l : List (Rc n B)) (hg : ∀ r ∈ g, r.2 = k) :
    chk (some k) (g ++ l) ↔ chk (some k) l := by
  induction g with
  | nil => rfl
  | cons r g ih =>
    rw [List.cons_append, chk, hg r List.mem_cons_self]
    simp [ih fun r' hr' => hg r' (List.mem_cons_of_mem r hr')]

omit [DecidableEq B] in
theorem chk_groups (K : List (Fin n → B)) (hK : K.Nodup) (g : (Fin n → B) → List (Rc n B))
    (hg : ∀ k, ∀ r ∈ g k, r.2 = k) (p : Option (Fin n → B)) (hp : ∀ k ∈ K, p ≠ some k) :
    chk p (K.flatMap g) ↔ ∀ k ∈ K, headOk (g k) := by
  induction K generalizing p with
  | nil => simp [chk]
  | cons k K ih =>
    rw [List.nodup_cons] at hK
    rw [List.flatMap_cons, List.forall_mem_cons]
    rcases hgk : g k with _ | ⟨r, g'⟩
    · simp [headOk, ih hK.2 p fun k' hk' => hp k' (List.mem_cons_of_mem k hk')]
    · rw [List.cons_append, chk, hg k r (by simp [hgk]),
        chk_same k _ _ fun r' hr' => hg k r' (by simp [hgk, hr']),
        ih hK.2 (some k) fun k' hk' h => hK.1 (Option.some_injective _ h ▸ hk')]
      simp [headOk, hp k List.mem_cons_self]

omit [DecidableEq B] in
private theorem flatMap_pmap_eq {α β γ : Type*} {P : α → Prop} (f : ∀ a, P a → β)
    (g : β → List γ) (g' : α → List γ) (l : List α) (H : ∀ a ∈ l, P a)
    (h : ∀ a (ha : P a), g (f a ha) = g' a) :
    (l.pmap f H).flatMap g = l.flatMap g' := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.pmap_cons, List.flatMap_cons, List.flatMap_cons, h, ih]

theorem chk_srt {bs : List B} (hbs : ∀ b, b ∈ bs) (hn : bs.Nodup) (l : List (Rc n B)) :
    chk none (srt bs l n) ↔ ∀ k, headOk (l.filter fun r => r.2 = k) := by
  have e : srt bs l n =
      ((keys bs n).pmap (fun k (hk : k.length = n) => fun i : Fin n => k.get (i.cast hk.symm))
        fun k hk => (mem_keys hbs n k).1 hk).flatMap fun k =>
          l.filter fun r => r.2 = k := by
    rw [srt_eq bs l n le_rfl]
    symm
    refine flatMap_pmap_eq _ _ _ _ _ fun k hk => List.filter_congr fun r _ => ?_
    simp only [List.take_of_length_le (by simp : (List.ofFn r.2).length ≤ n), decide_eq_decide]
    subst hk
    exact ⟨fun h => h ▸ List.ofFn_get k,
      fun h => funext fun i => by simpa using List.get_of_eq h (i.cast (by simp))⟩
  rw [e, chk_groups]
  · exact ⟨fun h k => h k (List.mem_pmap.2 ⟨List.ofFn k, (mem_keys hbs _ _).2 (by simp),
      funext fun i => by simp⟩), fun h k _ => h k⟩
  · exact (keys_nodup hn n).pmap fun a ha b hb h =>
      List.ext_get (ha.trans hb.symm) fun i h1 _ => by simpa using congrFun h ⟨i, ha ▸ h1⟩
  · exact fun k r hr => by simpa using (List.mem_filter.1 hr).2
  · simp

/-- Table entries followed by lookups: the sorted neighbour check succeeds iff every lookup is in
the table. -/
theorem chk_table {bs : List B} (hbs : ∀ b, b ∈ bs) (hn : bs.Nodup) (T L : List (Fin n → B)) :
    chk none (srt bs (T.map (fun x => (false, x)) ++ L.map fun x => (true, x)) n) ↔
      ∀ x ∈ L, x ∈ T := by
  rw [chk_srt hbs hn]
  have h1 (k : Fin n → B) : (T.map (fun x => ((false, x) : Rc n B)) ++
      L.map fun x => (true, x)).filter (fun r => r.2 = k) =
      (T.filter (· = k)).map (fun x => (false, x)) ++
        (L.filter (· = k)).map fun x => (true, x) := by
    rw [List.filter_append, List.filter_map, List.filter_map]
    rfl
  simp only [h1]
  refine ⟨fun h x hx => by_contra fun hT => ?_, fun h k => ?_⟩
  · have hkx := h x
    have he : T.filter (· = x) = [] :=
      List.filter_eq_nil_iff.2 fun a ha hax => hT (of_decide_eq_true hax ▸ ha)
    rw [he] at hkx
    rcases hL : L.filter (· = x) with _ | ⟨a, l⟩
    · exact List.not_mem_nil (hL ▸ List.mem_filter.2 ⟨hx, by simp⟩)
    · simp [hL, headOk] at hkx
  · rcases hT : T.filter (· = k) with _ | ⟨a, l⟩
    · rw [List.filter_eq_nil_iff.2 fun a ha => by
        simp only [decide_eq_true_eq]
        rintro rfl
        exact List.not_mem_nil (hT ▸ List.mem_filter.2 ⟨h a ha, by simp⟩)]
      simp [headOk]
    · simp [headOk]

theorem sum_filter [Fintype B] (j : Fin n) (l : List (Rc n B)) :
    ∑ b, (l.filter fun r => r.2 j = b).length = l.length := by
  induction l with
  | nil => simp
  | cons r l ih =>
    have hstep (b : B) : ((r :: l).filter fun r' => r'.2 j = b).length =
        (if r.2 j = b then 1 else 0) + (l.filter fun r' => r'.2 j = b).length := by
      rw [List.filter_cons]
      by_cases h : r.2 j = b <;> simp [h, add_comm]
    simp [hstep, Finset.sum_add_distrib, ih, add_comm]

theorem length_pass {bs : List B} (hbs : ∀ b, b ∈ bs) (hn : bs.Nodup) (j : Fin n)
    (l : List (Rc n B)) : (pass bs j l).length = l.length := by
  let f : Fintype B := ⟨bs.toFinset, fun b => List.mem_toFinset.2 (hbs b)⟩
  rw [pass, List.length_flatMap, ← List.sum_toFinset _ hn]
  exact @sum_filter n B _ f j l

theorem length_srt {bs : List B} (hbs : ∀ b, b ∈ bs) (hn : bs.Nodup)
    (l : List (Rc n B)) (j : ℕ) : (srt bs l j).length = l.length := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [srt]
    split_ifs <;> simp [length_pass hbs hn, ih]

end List.RadixSort
