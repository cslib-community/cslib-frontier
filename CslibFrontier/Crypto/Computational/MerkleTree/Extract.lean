/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MerkleTree.Binding
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Tactic.PolyTime
import Mathlib.Data.List.GetD

/-!
# Multi-opening Merkle-tree commitment extraction

Given any list of claimed openings against a Merkle root `rt` at depth `d`,
`merkleExtractVector` reconstructs a committed vector of length `len` by reading the first accepted
opening of each index (and filling unqueried slots with a default word), while
`merkleVectorBindingOutput` searches for two accepted openings of the same index to different
leaves:

* If `merkleVectorBindingOutput` finds any conflicting pair among accepted openings whose leaves
  lie in `leafSpace n`, then it breaks `merkleBreaksBinding`
  (`merkleBreaksBinding_merkleVectorBindingOutput`),
  and `extractMerkleCollision` extracts a collision on `merkleHashDomain leafSpace`.
* Otherwise every accepted opening below `len` agrees with `merkleExtractVector` at its index
  (`getD_merkleExtractVector_eq_of_conflict_eq_none`).

All extraction and conflict-search functions carry `ComputableInPolyTime` certificates, and
`merkleVectorBindingOutput` produces a `MerkleBindingOutput` satisfying `merkleBreaksBinding` for
downstream standard-model binding reductions via `CollisionResistantOn.merklePositionBinding` or
`merklePositionBinding_of_hashFamily`.

## Main definitions

* `Cslib.Crypto.MerkleIndexedOpening`, `Cslib.Crypto.encMerkleIndexedOpening`: indexed Merkle
  openings and their framing encoding.
* `Cslib.Crypto.merkleVerifiedOpenings`, `Cslib.Crypto.merkleExtractVector`: filtering verified
  openings and reconstructing the committed leaf vector.
* `Cslib.Crypto.merkleOpeningConflict`, `Cslib.Crypto.merkleVectorBindingOutput`: finding a
  disagreeing pair of openings as a `MerkleBindingOutput`.

## Main results

* `Cslib.Crypto.length_merkleExtractVector`: the extracted vector has length `len`.
* `Cslib.Crypto.merkleBreaksBinding_merkleVectorBindingOutput`,
  `Cslib.Crypto.getD_merkleExtractVector_eq_of_conflict_eq_none`,
  `Cslib.Crypto.getD_merkleExtractVector_or_merkleBreaksBinding`: either all verified openings
  below `len` agree with the extracted vector, or `merkleVectorBindingOutput` breaks position
  binding (and yields a hash collision on `merkleHashDomain leafSpace`).
* `Cslib.Crypto.computableInPolyTime_merkleVerifiedOpenings`,
  `Cslib.Crypto.computableInPolyTime_merkleExtractVector`,
  `Cslib.Crypto.computableInPolyTime_merkleVectorBindingOutput`: uniform polynomial-time
  certificates for multi-opening extraction and conflict detection.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 8.9.1 (Definitions 8.3 and 8.4, Attack Game 8.2, Theorem 8.8).
* [B. Barak, O. Goldreich, *Universal Arguments and their Applications*][BarakGoldreich2001],
  Construction 3.4 (locator not re-verified against primary PDF).
-/

@[expose] public section

namespace Cslib.Crypto

open Turing.MultiTapeTM

/-- An indexed Merkle opening pairs a leaf position with a bit-string leaf opening. -/
@[ext]
structure MerkleIndexedOpening where
  /-- The leaf index opened. -/
  position : ℕ
  /-- The claimed bit-string leaf and authentication path. -/
  opening : MerkleOpening (List Bool)
  deriving DecidableEq, Repr, Inhabited

/-- The encoding of an indexed Merkle opening: the unary index, then the bit-string opening. -/
enc_structure encMerkleIndexedOpening : MerkleIndexedOpening where
  position : encUnary, opening : encMerkleOpening

section Extract

/-- Keep only openings whose index is below `len` and whose opening passes `merkleVerify`. -/
def merkleVerifiedOpenings (H : List Bool → List Bool → List Bool) (k : List Bool) (d len : ℕ)
    (root : List Bool) (openings : List MerkleIndexedOpening) : List MerkleIndexedOpening :=
  openings.filter fun entry =>
    decide (entry.position < len) && entry.opening.verify H k id d root entry.position

/-- Reconstruct a `len`-entry leaf vector from `openings` by taking the first opening matching
each index below `len`, falling back to `defaultLeaf` at unopened positions. -/
def merkleExtractVector (len : ℕ) (defaultLeaf : List Bool)
    (openings : List MerkleIndexedOpening) : List (List Bool) :=
  (List.range len).map fun j =>
    (openings.find? fun entry => entry.position == j).elim defaultLeaf fun entry =>
      entry.opening.leaf

/-- Find the first pair of entries in `openings` that open the same index to different leaves. -/
def merkleOpeningConflict (openings : List MerkleIndexedOpening) :
    Option (MerkleIndexedOpening × MerkleIndexedOpening) :=
  (openings.flatMap fun o₁ => openings.map fun o₂ => (o₁, o₂)).find? fun pair =>
    let (first, second) := pair
    first.position == second.position && first.opening.leaf != second.opening.leaf

/-- Convert the first conflict in `openings` against `root` into a `MerkleBindingOutput`. -/
def merkleVectorBindingOutput (root : List Bool) (openings : List MerkleIndexedOpening) :
    MerkleBindingOutput :=
  (merkleOpeningConflict openings).elim
    { root, position := 0, first := ⟨[], []⟩, second := ⟨[], []⟩ }
    fun pair =>
      let (first, second) := pair
      { root, position := first.position, first := first.opening, second := second.opening }

@[simp]
theorem length_merkleExtractVector (len : ℕ) (defaultLeaf : List Bool)
    (openings : List MerkleIndexedOpening) :
    (merkleExtractVector len defaultLeaf openings).length = len := by
  simp [merkleExtractVector]

@[simp]
theorem mem_merkleVerifiedOpenings {H : List Bool → List Bool → List Bool} {k : List Bool}
    {d len : ℕ} {root : List Bool} {openings : List MerkleIndexedOpening}
    {entry : MerkleIndexedOpening} :
    entry ∈ merkleVerifiedOpenings H k d len root openings ↔
      entry ∈ openings ∧ entry.position < len ∧
        entry.opening.verify H k id d root entry.position = true := by
  simp [merkleVerifiedOpenings]

/-- If every entry in `openings` is verified at depth `d` against `root` and lies in
`leafSpace n`, then any conflicting pair at the same index makes `merkleVectorBindingOutput` break
position binding. -/
theorem merkleBreaksBinding_merkleVectorBindingOutput {H : List Bool → List Bool → List Bool}
    {leafSpace : ℕ → List Bool → Bool} {n : ℕ} {k : List Bool} {d : ℕ} {root : List Bool}
    {openings : List MerkleIndexedOpening}
    (hvalid : ∀ entry ∈ openings,
      leafSpace n entry.opening.leaf = true ∧
        entry.opening.verify H k id d root entry.position = true)
    {o₁ o₂ : MerkleIndexedOpening} (ho₁ : o₁ ∈ openings) (ho₂ : o₂ ∈ openings)
    (hpos : o₁.position = o₂.position) (hle : o₁.opening.leaf ≠ o₂.opening.leaf) :
    merkleBreaksBinding H leafSpace n k (merkleVectorBindingOutput root openings) = true := by
  have hsome : (merkleOpeningConflict openings).isSome = true := by
    refine List.find?_isSome.mpr ⟨(o₁, o₂),
      List.mem_flatMap.mpr ⟨o₁, ho₁, List.mem_map.mpr ⟨o₂, ho₂, rfl⟩⟩, ?_⟩
    simp [hpos, hle]
  obtain ⟨⟨p₁, p₂⟩, hfind⟩ := Option.isSome_iff_exists.mp hsome
  have hp := List.find?_some hfind
  obtain ⟨q₁, hq₁, hq⟩ := List.mem_flatMap.mp (List.mem_of_find?_eq_some hfind)
  obtain ⟨q₂, hq₂, hqeq⟩ := List.mem_map.mp hq
  simp only [Prod.mk.injEq] at hqeq
  obtain ⟨rfl, rfl⟩ := hqeq
  obtain ⟨hl₁, hv₁⟩ := hvalid q₁ hq₁
  obtain ⟨hl₂, hv₂⟩ := hvalid q₂ hq₂
  have hd : q₁.opening.path.length = d :=
    (merkleVerify_eq_true_iff.mp (by simpa using hv₁)).1
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hp
  rw [← hp.1] at hv₂
  rw [merkleVectorBindingOutput, hfind]
  simp only [Option.elim_some, merkleBreaksBinding, Bool.and_eq_true, bne_iff_ne, ne_eq,
    hd, hl₁, hl₂, hv₁, hv₂, hp.2, and_self, not_false_eq_true]

/-- When `merkleOpeningConflict openings = none`, every entry below `len` agrees with
`merkleExtractVector`. -/
theorem getD_merkleExtractVector_eq_of_conflict_eq_none (len : ℕ) (defaultLeaf : List Bool)
    {openings : List MerkleIndexedOpening} (hnone : merkleOpeningConflict openings = none)
    {entry : MerkleIndexedOpening} (hent : entry ∈ openings) (hlt : entry.position < len) :
    (merkleExtractVector len defaultLeaf openings).getD entry.position defaultLeaf =
      entry.opening.leaf := by
  have hsome : (openings.find? fun e => e.position == entry.position).isSome = true :=
    List.find?_isSome.mpr ⟨entry, hent, by simp⟩
  obtain ⟨found, hfind⟩ := Option.isSome_iff_exists.mp hsome
  have hfound_mem := List.mem_of_find?_eq_some hfind
  have hfound_pos : found.position = entry.position := by
    simpa using List.find?_some hfind
  have hno := List.find?_eq_none.mp hnone (found, entry)
    (List.mem_flatMap.mpr ⟨found, hfound_mem, List.mem_map.mpr ⟨entry, hent, rfl⟩⟩)
  have hleaf : found.opening.leaf = entry.opening.leaf := by
    by_contra hne
    exact hno (by simp [hfound_pos, hne])
  simp only [merkleExtractVector, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hlt, Option.map_some, Option.getD_some, hfind, Option.elim_some]
  exact hleaf

/-- **Commitment-vector consistency or position-binding break**: filtering `openings` to verified
openings below `len`, either every verified opening in `openings` below `len` agrees with the
reconstructed vector `merkleExtractVector`, or `merkleVectorBindingOutput` breaks
`merkleBreaksBinding` (assuming verified openings have leaves in `leafSpace n`). -/
theorem getD_merkleExtractVector_or_merkleBreaksBinding
    {H : List Bool → List Bool → List Bool} {leafSpace : ℕ → List Bool → Bool} {n : ℕ}
    {k : List Bool} {d len : ℕ} {root : List Bool} (defaultLeaf : List Bool)
    {openings : List MerkleIndexedOpening}
    (hleaf : ∀ entry ∈ merkleVerifiedOpenings H k d len root openings,
      leafSpace n entry.opening.leaf = true) :
    let verified := merkleVerifiedOpenings H k d len root openings
    merkleBreaksBinding H leafSpace n k (merkleVectorBindingOutput root verified) = true ∨
      ∀ entry ∈ verified,
        (merkleExtractVector len defaultLeaf verified).getD entry.position defaultLeaf =
          entry.opening.leaf := by
  intro verified
  cases hconf : merkleOpeningConflict verified with
  | none =>
    refine Or.inr fun entry hent => ?_
    exact getD_merkleExtractVector_eq_of_conflict_eq_none len defaultLeaf hconf hent
      (mem_merkleVerifiedOpenings.mp hent).2.1
  | some pair =>
    rcases pair with ⟨p₁, p₂⟩
    have hp := List.find?_some hconf
    obtain ⟨q₁, hq₁, hq⟩ := List.mem_flatMap.mp (List.mem_of_find?_eq_some hconf)
    obtain ⟨q₂, hq₂, hqeq⟩ := List.mem_map.mp hq
    simp only [Prod.mk.injEq] at hqeq
    obtain ⟨rfl, rfl⟩ := hqeq
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hp
    refine Or.inl (merkleBreaksBinding_merkleVectorBindingOutput (d := d) ?_ hq₁ hq₂ hp.1 hp.2)
    intro e he
    exact ⟨hleaf e he, (mem_merkleVerifiedOpenings.mp he).2.2⟩

end Extract

section Efficiency

variable {H : List Bool → List Bool → List Bool} {γ : Type} {encIn : γ ↪ List Bool}

/-- Filtering verified indexed openings takes polynomial time. -/
@[program_certificate]
theorem computableInPolyTime_merkleVerifiedOpenings
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k x, (H k x).length = k.length)
    {k root : γ → List Bool} {d len : γ → ℕ} {openings : γ → List MerkleIndexedOpening}
    (hk : ComputableInPolyTime k encIn encBits)
    (hd : ComputableInPolyTime d encIn encUnary)
    (hlenVec : ComputableInPolyTime len encIn encUnary)
    (hroot : ComputableInPolyTime root encIn encBits)
    (hopenings : ComputableInPolyTime openings encIn (encList encMerkleIndexedOpening)) :
    ComputableInPolyTime
      (fun a => merkleVerifiedOpenings H (k a) (d a) (len a) (root a) (openings a))
      encIn (encList encMerkleIndexedOpening) := by
  have hm := computableInPolyTime_merkleVerify hH hlen
  unfold merkleVerifiedOpenings
  refine ComputableInPolyTime.filterWithInput hopenings ?_
  have ha := ComputableInPolyTime.fst encIn encMerkleIndexedOpening
  have hlt : ComputableInPolyTime
      (fun p : γ × MerkleIndexedOpening => decide (p.2.position < len p.1))
      (encPair encIn encMerkleIndexedOpening) encBool :=
    ComputableInPolyTime.unary_lt' (by fun_prop) (hlenVec.comp ha)
  have hargs : ComputableInPolyTime
      (fun p : γ × MerkleIndexedOpening =>
        ((k p.1, d p.1), (root p.1, p.2.position), (p.2.opening.leaf, p.2.opening.path)))
      (encPair encIn encMerkleIndexedOpening)
      (encPair (encPair encBits encUnary)
        (encPair (encPair encBits encUnary) (encPair encBits (encList encBits)))) := by
    fun_prop
  have hver := hm.comp hargs
  exact ComputableInPolyTime.bool_and.comp (hlt.prod hver)

/-- Reconstructing `merkleExtractVector` from indexed openings takes polynomial time. -/
@[program_certificate]
theorem computableInPolyTime_merkleExtractVector
    {len : γ → ℕ} {defaultLeaf : γ → List Bool} {openings : γ → List MerkleIndexedOpening}
    (hlenVec : ComputableInPolyTime len encIn encUnary)
    (hdefault : ComputableInPolyTime defaultLeaf encIn encBits)
    (hopenings : ComputableInPolyTime openings encIn (encList encMerkleIndexedOpening)) :
    ComputableInPolyTime
      (fun a => merkleExtractVector (len a) (defaultLeaf a) (openings a))
      encIn (encList encBits) := by
  unfold merkleExtractVector
  refine ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp hlenVec) ?_
  have ha := ComputableInPolyTime.fst encIn encUnary
  have hj := ComputableInPolyTime.snd encIn encUnary
  have hfind : ComputableInPolyTime
      (fun q : γ × ℕ => (openings q.1).find? fun entry => entry.position == q.2)
      (encPair encIn encUnary) (encOption encMerkleIndexedOpening) :=
    ComputableInPolyTime.findWithInput (hopenings.comp ha)
      (ComputableInPolyTime.beq (encB := encUnary) (by fun_prop) (by fun_prop))
  exact hfind.optionElimWithInput (hdefault.comp ha) (by fun_prop)

/-- Searching `openings` for a conflicting leaf pair takes polynomial time. -/
@[program_certificate]
theorem computableInPolyTime_merkleOpeningConflict
    {openings : γ → List MerkleIndexedOpening}
    (hopenings : ComputableInPolyTime openings encIn (encList encMerkleIndexedOpening)) :
    ComputableInPolyTime (fun a => merkleOpeningConflict (openings a)) encIn
      (encOption (encPair encMerkleIndexedOpening encMerkleIndexedOpening)) := by
  unfold merkleOpeningConflict
  have hpairs : ComputableInPolyTime
      (fun a => (openings a).flatMap fun o₁ => (openings a).map fun o₂ => (o₁, o₂))
      encIn (encList (encPair encMerkleIndexedOpening encMerkleIndexedOpening)) := by
    refine ComputableInPolyTime.flatMapWithInput hopenings ?_
    exact ComputableInPolyTime.mapWithInput
      (hopenings.comp (ComputableInPolyTime.fst encIn encMerkleIndexedOpening))
      (by fun_prop)
  exact ComputableInPolyTime.findWithInput hpairs (by fun_prop)

/-- Constructing `merkleVectorBindingOutput` takes polynomial time. -/
@[program_certificate]
theorem computableInPolyTime_merkleVectorBindingOutput
    {root : γ → List Bool} {openings : γ → List MerkleIndexedOpening}
    (hroot : ComputableInPolyTime root encIn encBits)
    (hopenings : ComputableInPolyTime openings encIn (encList encMerkleIndexedOpening)) :
    ComputableInPolyTime (fun a => merkleVectorBindingOutput (root a) (openings a))
      encIn encMerkleBindingOutput := by
  unfold merkleVectorBindingOutput
  have hconf := computableInPolyTime_merkleOpeningConflict hopenings
  have hempty : ComputableInPolyTime
      (fun _ : γ => (⟨[], []⟩ : MerkleOpening (List Bool))) encIn encMerkleOpening :=
    ComputableInPolyTime.const _
  exact hconf.optionElimWithInput
    (encMerkleBindingOutput_mk_polyTime hroot (ComputableInPolyTime.const 0) hempty hempty)
    (by fun_prop)

end Efficiency

end Cslib.Crypto
