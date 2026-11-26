/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.AhoCorasick.Search
public import CslibFrontier.Algorithms.Lean.KMP.Search
import Mathlib.Data.List.Sort

/-!
# Aho–Corasick with One Keyword: the Knuth–Morris–Pratt Special Case

For a single keyword `p`, the pattern matching machine of `[AhoCorasick1975]` is the
Knuth–Morris–Pratt automaton (`[KnuthMorrisPratt1977]`): the failure state of the prefix of length
`q` is the prefix of length `borderLen p q` (the KMP prefix function), and the Aho–Corasick search
reports exactly the KMP match shifts, each shifted to its end position.

## Main results

* `Cslib.Algorithms.Lean.AhoCorasick.failure_singleton_take`:
  `failure [p] (p.take q) = p.take (KMP.borderLen p q)` for `1 ≤ q ≤ p.length`.
* `Cslib.Algorithms.Lean.AhoCorasick.mem_occurrences_singleton_iff`:
  `(s + p.length, p) ∈ occurrences [p] t ↔ s ∈ KMP.kmpMatchesList p t` for `p ≠ []`.
* `Cslib.Algorithms.Lean.AhoCorasick.search_singleton`:
  `search [p] t = (KMP.kmpMatchesList p t).map fun s => (s + p.length, p)` for `p ≠ []`.

## References

* [A. V. Aho and M. J. Corasick, *Efficient String Matching: An Aid to Bibliographic
  Search*][AhoCorasick1975]
* [D. E. Knuth, J. H. Morris, Jr., and V. R. Pratt, *Fast Pattern Matching in
  Strings*][KnuthMorrisPratt1977]
-/

public section

namespace Cslib.Algorithms.Lean.AhoCorasick

open Cslib.Algorithms.Lean.KMP

variable {α : Type*} [DecidableEq α]

/-- For one keyword, the failure function is the KMP prefix function: the failure state of the
prefix of length `q` is its longest proper border. -/
theorem failure_singleton_take {p : List α} {q : ℕ} (hq : 0 < q) (hqp : q ≤ p.length) :
    failure [p] (p.take q) = p.take (borderLen p q) := by
  have hlen : (p.take q).length = q := List.length_take_of_le hqp
  have hne : p.take q ≠ [] := fun h => by rw [h, List.length_nil] at hlen; omega
  have hb : IsProperBorderLen (p.take q) (borderLen p q) :=
    isProperBorderLen_maxBorderLen (by omega)
  have hbq : borderLen p q < q := hb.1.trans_eq hlen
  have hsuf : p.take (borderLen p q) <:+ p.take q := by
    simpa only [List.take_take, Nat.min_eq_left hbq.le] using hb.2
  refine ((eq_failure_iff hne).mpr ⟨hsuf, (List.length_take_of_le (by omega)).trans_lt hb.1,
    isNode_take List.mem_cons_self _, fun x hx hlt hxn => ?_⟩).symm
  rcases hxn with rfl | ⟨r, hr, hxr⟩
  · exact Nat.zero_le _
  · rw [List.mem_singleton.mp hr] at hxr
    have hxt : (p.take q).take x.length = x :=
      (List.prefix_iff_eq_take.mp (List.prefix_take_iff.mpr ⟨hxr, by omega⟩)).symm
    rw [List.length_take_of_le (by omega)]
    exact le_maxBorderLen_of_isProperBorderLen ⟨hlt, hxt.symm ▸ hx⟩

/-- For one nonempty keyword, its occurrences ending at `s + p.length` are its KMP matches at
shift `s`. -/
theorem mem_occurrences_singleton_iff {p t : List α} (hp : p ≠ []) {s : ℕ} :
    (s + p.length, p) ∈ occurrences [p] t ↔ s ∈ kmpMatchesList p t := by
  rw [mem_occurrences_iff, mem_kmpMatchesList_iff, IsOccurrence, List.take_add]
  constructor
  · rintro ⟨hlen, -, -, hsuf⟩
    have hs : (t.take s).length = s := List.length_take_of_le (by omega)
    have hd : ((t.drop s).take p.length).length = p.length := by
      rw [List.length_take_of_le (by rw [List.length_drop]; omega)]
    have hp' : p = (t.drop s).take p.length := by
      have h := List.suffix_iff_eq_drop.mp hsuf
      rwa [List.length_append, hs, hd, Nat.add_sub_cancel, List.drop_left' hs] at h
    exact ⟨by omega, List.prefix_iff_eq_take.mpr hp'⟩
  · rintro ⟨hs, hpref⟩
    have hle := hpref.length_le
    rw [List.length_drop] at hle
    refine ⟨by omega, hp, List.mem_singleton_self p, ?_⟩
    rw [← List.prefix_iff_eq_take.mp hpref]
    exact List.suffix_append _ _

/-- For one nonempty keyword, the Aho–Corasick search reports exactly the KMP matches, in the same
order, each as its end position. -/
theorem search_singleton {p : List α} (hp : p ≠ []) (t : List α) :
    search [p] t = (kmpMatchesList p t).map fun s => (s + p.length, p) := by
  rw [search_eq]
  let R : ℕ × List α → ℕ × List α → Prop := fun x y => x.1 < y.1
  have : Std.Irrefl R := ⟨fun x => Nat.lt_irrefl x.1⟩
  have h1 : (occurrences [p] t).Pairwise R :=
    (pairwise_occurrences [p] t).imp_of_mem fun {x y} hx hy h =>
      h.resolve_right fun ⟨_, hlt⟩ => by
        rw [List.mem_singleton.mp (mem_occurrences_iff.mp hx).2.2.1,
          List.mem_singleton.mp (mem_occurrences_iff.mp hy).2.2.1] at hlt
        exact Nat.lt_irrefl _ hlt
  have h2 : ((kmpMatchesList p t).map fun s => (s + p.length, p)).Pairwise R :=
    List.pairwise_map.mpr ((pairwise_lt_kmpMatchesList p t).imp fun h => Nat.add_lt_add_right h _)
  refine h1.eq_of_mem_iff h2 fun ⟨i, y⟩ => ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨hi, -, hyP, hyt⟩ := mem_occurrences_iff.mp h
    rw [List.mem_singleton] at hyP
    subst hyP
    have hle : y.length ≤ i := by have := hyt.length_le; rw [List.length_take] at this; omega
    refine List.mem_map.mpr ⟨i - y.length, ?_, by rw [Nat.sub_add_cancel hle]⟩
    rw [← mem_occurrences_singleton_iff hp, Nat.sub_add_cancel hle]
    exact h
  · obtain ⟨s, hs, hsi⟩ := List.mem_map.mp h
    rw [← hsi]
    exact (mem_occurrences_singleton_iff hp).mpr hs

end Cslib.Algorithms.Lean.AhoCorasick
