/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.SMN
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Tactic.EncLen

/-!
# Encoded size of the s-m-n construction

The existing description transformation `Turing.MultiTapeTM.Universal.hardwire d p` builds the
prefix `p` into the description `d`. This module accounts for the size of the description it
constructs. The exact decomposition follows its writing, copying, rewinding and redirected
transition tables; the arithmetic endpoint is quadratic in the framed encoding of `(d, p)`.

These are rigorous lengths in `Turing.MultiTapeTM.Universal.eDesc`. That encoding uses unary state
and symbol numbers, so the bounds are model-dependent code lengths, not implementation byte counts
or tight estimates for another compiler. The transformation itself is offline: its polynomial-time
uniformity is `Turing.MultiTapeTM.Universal.computableInPolyTime_hardwire`, while the compiler's
runtime is not charged to a hardwired program unless another construction executes the compiler.

## Main definitions

This module adds no representation: it measures the existing
`Turing.MultiTapeTM.Universal.hardwire` construction with
`Turing.MultiTapeTM.Universal.descLen`, which is exactly the length of `eDesc`.

## Main results

* `Turing.MultiTapeTM.Universal.Hardwire.descLen_hardwire_eq`: the exact structural decomposition
  of a generated description's encoded length.
* `Turing.MultiTapeTM.Universal.Hardwire.descLen_hardwire_le`: a concrete quadratic upper bound in
  the encoded input length.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Lemma 6.1][Sipser2013]
-/

public section

namespace Turing.MultiTapeTM.Universal

namespace Hardwire

open Redirect

/-- There are three writing transitions for the marker and for each prefix bit. -/
theorem length_writeEntries (p : List Bool) (k : ℕ) :
    (writeEntries p k).length = 3 * (p.length + 1) := by
  simp [writeEntries, bitSyms, List.length_flatMap, List.sum_replicate, Nat.mul_comm]
  omega

/-- The input-copying table has transitions for the two bits and the final blank. -/
theorem length_copyEntries (k : ℕ) : (copyEntries k).length = 3 := rfl

/-- The rewinding table has transitions for a blank, the two bits and the marker. -/
theorem length_rewindEntries (q : ℕ) (r : Option ℕ) (rest : List (Option ℕ)) (next : ℕ) :
    (rewindEntries q r rest next).length = 4 := by
  simp [rewindEntries, bitSyms]

private theorem length_vlift_le (i : Option ℕ) : (vlift i).length ≤ 2 := by
  rcases i with _ | i
  · rfl
  · simp only [vlift]
    split <;> simp

private theorem length_redirect_le (table : List (Key × Act)) :
    (redirect (fun q => 2 * q + 1) none [] 0 id table).length ≤ 2 * table.length := by
  induction table with
  | nil => rfl
  | cons e table ih =>
    rw [redirect, List.flatMap_cons, List.length_append, List.length_map, ← redirect]
    have := length_vlift_le e.1.input
    simp only [List.length_cons]
    omega

/-- The exact encoded length of a hardwired description, split into the preparation tables and
the redirected source table. Each table is measured by its actual framed encoding. -/
theorem descLen_hardwire_eq (d : Desc) (p : List Bool) :
    descLen (hardwire d p) = 2 * (d.tapes + 1) + 2 +
      (encList (encPair eKey eAct) (writeEntries p d.tapes)).length +
      (encList (encPair eKey eAct) (copyEntries d.tapes)).length +
      (encList (encPair eKey eAct)
        (rewindEntries 2 none (List.replicate d.tapes none) (2 * d.q₀ + 1))).length +
      (encList (encPair eKey eAct)
        (redirect (fun q => 2 * q + 1) none [] 0 id d.table)).length := by
  enc_len [descLen, hardwire, eDesc_apply, encList_append]

private theorem length_encSign_le (m : SignType) : (encSign m).length ≤ 1 := by
  cases m <;> decide

private theorem length_redirectEntry_le (e : Key × Act) (s : Option ℕ)
    (hs : s ∈ vlift e.1.input) :
    (encPair eKey eAct (redirectEntry (fun q => 2 * q + 1) none [] 0 id e s)).length ≤
      50 * ((encPair eKey eAct e).length + 1) := by
  rcases e with ⟨⟨q, i, work⟩, ⟨move, actions, output, next⟩⟩
  have hs_le : (eSym s).length ≤ (eSym i).length + 3 := by
    rcases i with _ | b
    · rcases (by simpa [vlift] using hs : s = some marker ∨ s = none) with rfl | rfl <;> decide
    · obtain ⟨-, rfl⟩ : b ≠ marker ∧ s = some b := by simpa [vlift] using hs
      omega
  have hvm := length_encSign_le (vmove s move)
  have hnext : (eSym (next.map fun q => 2 * q + 1)).length ≤ 2 * (eSym next).length := by
    cases next <;> enc_len [Option.map_none, Option.map_some]
  enc_len [redirectEntry_hardwire, eKey_apply, eAct_apply, show encSign .zero = [] from rfl]

private theorem length_encList_redirect_le (d : Desc) :
    (encList (encPair eKey eAct)
      (redirect (fun q => 2 * q + 1) none [] 0 id d.table)).length ≤
        (2 * d.table.length) * (2 * (50 * (descLen d + 1)) + 1) := by
  refine (length_encList_le (encPair eKey eAct) _ (b := 50 * (descLen d + 1)) ?_).trans
    (Nat.mul_le_mul_right _ (length_redirect_le d.table))
  intro e' he'
  simp only [redirect, List.mem_flatMap, List.mem_map] at he'
  obtain ⟨e, he, s, hs, rfl⟩ := he'
  have htable : (encList (encPair eKey eAct) d.table).length ≤ descLen d := by
    enc_len [descLen, eDesc_apply]
  exact (length_redirectEntry_le e s hs).trans (Nat.mul_le_mul_left 50
    (Nat.add_le_add_right ((length_le_encList_of_mem (encPair eKey eAct) he).trans htable) 1))

private theorem length_eSym_of_mem_bitSyms {s : Option ℕ} (hs : s ∈ bitSyms) :
    (eSym s).length ≤ 2 := by
  rcases (by simpa [bitSyms] using hs : s = _ ∨ s = _ ∨ s = _) with rfl | rfl | rfl <;> decide

private theorem length_prepEntry_of_bounds {q k next : ℕ} {r s : Option ℕ} {mv : SignType}
    {acts : List TapeAct} {B : ℕ} (hq : q ≤ 2 * B + 4) (hk : k ≤ B) (hnext : next ≤ 2 * B + 4)
    (hr : (eSym r).length ≤ 2) (hs : (eSym s).length ≤ 3)
    (hacts : (encList eTA acts).length ≤ 21) :
    (encPair eKey eAct (⟨q, r, s :: List.replicate k none⟩,
      ⟨mv, acts, none, some next⟩)).length ≤ 100 * (B + 1) := by
  have hmv := length_encSign_le mv
  have hrep : (encList eSym (List.replicate k none)).length = k := by simp [length_encList]
  enc_len [eKey_apply, eAct_apply, hrep]

private theorem length_prepEntry_le {d : Desc} {p : List Bool} {e : Key × Act}
    (he : e ∈ prep d p) :
    (encPair eKey eAct e).length ≤ 100 * (descLen d + p.length + 1) := by
  have htapes := tapes_le d
  have hq₀ := q₀_le d
  simp only [prep, writeEntries, copyEntries, rewindEntries, List.mem_append,
    List.mem_map, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with ((⟨r, hr, rfl⟩ | ⟨⟨b, i⟩, hbi, r, hr, rfl⟩) | he) | (⟨s, hs, rfl⟩ | rfl)
  · exact length_prepEntry_of_bounds (by omega) (by omega) (by omega)
      (length_eSym_of_mem_bitSyms hr) (by decide) (by decide)
  · rw [List.mem_zipIdx_iff_getElem?] at hbi
    have hi : i < p.length := by
      simpa only [List.length_reverse] using (List.getElem?_eq_some_iff.mp hbi).1
    exact length_prepEntry_of_bounds (by omega) (by omega) (by omega)
      (length_eSym_of_mem_bitSyms hr) (by decide) (by cases b <;> dsimp <;> decide)
  · rcases he with rfl | rfl | rfl <;>
      exact length_prepEntry_of_bounds (by omega) (by omega) (by omega)
        (by decide) (by decide) (by decide)
  · exact length_prepEntry_of_bounds (by omega) (by omega) (by omega)
      (by decide) ((length_eSym_of_mem_bitSyms hs).trans (by decide)) (by decide)
  · exact length_prepEntry_of_bounds (by omega) (by omega) (by omega)
      (by decide) (by decide) (by decide)

private theorem length_prep (d : Desc) (p : List Bool) :
    (prep d p).length = 3 * p.length + 10 := by
  simp only [prep, List.length_append, length_writeEntries, length_copyEntries,
    length_rewindEntries]
  omega

private theorem length_encList_prep_le (d : Desc) (p : List Bool) :
    (encList (encPair eKey eAct) (prep d p)).length ≤
      (3 * p.length + 10) * (2 * (100 * (descLen d + p.length + 1)) + 1) := by
  rw [← length_prep]
  exact length_encList_le (encPair eKey eAct) _ fun _ he => length_prepEntry_le he

/-- The encoded hardwired description has quadratic size in the encoded source description and
the prefix. The constant `2500` is a proved coarse upper bound, not a tightness claim. Both sides
use the library's unary `eDesc` coding, not an implementation-size estimate. -/
theorem descLen_hardwire_le (d : Desc) (p : List Bool) :
    descLen (hardwire d p) ≤
      2500 * ((encPair eDesc encBits (d, p)).length) ^ 2 := by
  have hprep := length_encList_prep_le d p
  have hredirect := length_encList_redirect_le d
  have htapes := tapes_le d
  have htable := table_le d
  have hinput : descLen d + p.length + 1 ≤ (encPair eDesc encBits (d, p)).length := by
    enc_len [descLen]
  rw [descLen_hardwire_eq]
  simp only [prep, encList_append, List.length_append] at hprep
  nlinarith [sq_nonneg (descLen d + p.length + 1),
    sq_nonneg ((encPair eDesc encBits (d, p)).length)]

end Hardwire

end Turing.MultiTapeTM.Universal
