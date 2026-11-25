/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.CollisionResistant
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Foundations.Data.Nat.Log
import CslibFrontier.Tactic.PolyTime
import Mathlib.Data.List.GetD
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Tactic.EncLen

/-!
# Merkle trees

A Merkle tree hashes a list of leaves to a single root so that each leaf can later be opened
against the root with a short authentication path ([Merkle1989], Section 6; [BonehShoup2023],
Section 8.9). Here the hash is a keyed function `H : List Bool → List Bool → List Bool`, as in
`CollisionResistant`. As in both sources, a leaf `x` becomes the node `H k x`, and the parent of
nodes `l` and `r` is `H k (encPair encBits encBits (l, r))`. The pairing `encPair` is injective,
so nodes of any length can be paired without ambiguity.

The tree over `leaves` has depth `Nat.clog 2 leaves.length`, the least `d` with
`leaves.length ≤ 2 ^ d`. Missing leaves read as the empty word, padding the tree to `2 ^ d` leaves
as [BonehShoup2023] suggests. For `2 ^ d` leaves this is Merkle's `H(1, 2 ^ d, Y)`, with his
`Y_i` as `leaves.getD (i - 1) []`. For other leaf counts it differs from Merkle's recursion, which
splits at the midpoint without padding.

An authentication path for position `i` lists the sibling of each node on the way from leaf `i`
to the root. `merkleRootOfPath` recomputes a root from a leaf, a position and a path. Its
correctness is `merkleRootOfPath_merklePath`. Binding is `isCollision_extractMerkleCollision`: two
openings of the same position to different leaves, along paths of equal length and with the same
recomputed root, contain a collision of `H k`, found deterministically by
`extractMerkleCollision`. This is the reduction behind [BonehShoup2023], Theorem 8.8.

**What a verifier must check.** Leaves and internal nodes are hashed with the same `H k`, with no
domain separation, so a recomputed root alone binds nothing. A verifier must fix the path length
to the depth `d` and check `i < 2 ^ d`:

* with a shorter path, an internal node's hash input opens as a leaf; for leaves `[a, b]`, the
  "leaf" `encPair encBits encBits (H k a, H k b)` at position `0` with path `[]` recomputes the
  root;
* `merkleRootOfPath` reads only the low `path.length` bits of `i`, so positions wrap modulo
  `2 ^ path.length`;
* the root does not fix the number of leaves: `[a, b, c]` and `[a, b, c, []]` have the same root.

To bind under collision resistance of the hash on its domain only, the leaves and the pairs of
digests (`isDigestPair`, [BonehShoup2023], Section 8.9), a verifier must also check that every
label is a digest: then every hash input met while recomputing a root is the leaf or a pair of
digests (`eq_or_isDigestPair_of_mem_merkleInputs`), and so is every collision that
`extractMerkleCollision` finds (`mem_merkleInputs_of_extractMerkleCollision`).

The root, the path, root recomputation and extraction have plain polynomial-time certificates for
hash families whose digests have the length of the key. Positions are unary in these
certificates, which suits trees with polynomially many leaves.

## Main definitions

* `Cslib.Crypto.merkleParents`, `Cslib.Crypto.merkleLevel`: one level of the tree from the one
  below, and level `j` counted from the hashed leaves.
* `Cslib.Crypto.merkleRoot`, `Cslib.Crypto.merklePath`: the root and the authentication path of
  a position.
* `Cslib.Crypto.merkleInputs`, `Cslib.Crypto.merkleRootOfPath`: the hash inputs met while
  recomputing a root from an opening, and the recomputed root.
* `Cslib.Crypto.extractMerkleCollision`: the first differing pair of hash inputs of two openings.
* `Cslib.Crypto.isDigestPair`: the hash inputs of internal nodes, pairs of digests.

## Main results

* `Cslib.Crypto.length_merkleLevel`, `Cslib.Crypto.length_merklePath`: level sizes and path
  length.
* `Cslib.Crypto.merkleRootOfPath_merklePath`: an honest opening recomputes the root.
* `Cslib.Crypto.isCollision_extractMerkleCollision`: a second opening of a position yields a
  collision.
* `Cslib.Crypto.eq_or_isDigestPair_of_mem_merkleInputs`,
  `Cslib.Crypto.mem_merkleInputs_of_extractMerkleCollision`: the hash inputs of an opening whose
  labels are digests lie in the hash's domain, and so do the collisions extracted from it.
* `Cslib.Crypto.computableInPolyTime_merkleRoot`, `Cslib.Crypto.computableInPolyTime_merklePath`,
  `Cslib.Crypto.computableInPolyTime_merkleInputs`,
  `Cslib.Crypto.computableInPolyTime_merkleRootOfPath`,
  `Cslib.Crypto.computableInPolyTime_extractMerkleCollision`: plain polynomial-time certificates.

## References

* [R. C. Merkle, *A Certified Digital Signature*][Merkle1989], Section 6.
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Section 8.9,
  Figure 8.12 and Theorem 8.8.
-/

@[expose] public section

namespace Cslib.Crypto

open Turing.MultiTapeTM

variable (H : List Bool → List Bool → List Bool) (k : List Bool)

/-! ### The tree -/

/-- The hashed leaves of the tree over `leaves`, padded with the empty word to `2 ^ d` leaves for
`d = Nat.clog 2 leaves.length`. -/
def merkleLeafLevel (leaves : List (List Bool)) : List (List Bool) :=
  (List.range (2 ^ Nat.clog 2 leaves.length)).map fun i => H k (leaves.getD i [])

/-- The parents of a level: node `i` hashes the pair of nodes `2 * i` and `2 * i + 1`. -/
def merkleParents (level : List (List Bool)) : List (List Bool) :=
  (List.range (level.length / 2)).map fun i =>
    H k (encPair encBits encBits (level.getD (2 * i) [], level.getD (2 * i + 1) []))

/-- Level `j` of the tree over `leaves`, counted from the hashed leaves at level `0`. -/
def merkleLevel (leaves : List (List Bool)) (j : ℕ) : List (List Bool) :=
  (merkleParents H k)^[j] (merkleLeafLevel H k leaves)

/-- The root of the Merkle tree over `leaves` ([BonehShoup2023], Section 8.9). -/
def merkleRoot (leaves : List (List Bool)) : List Bool :=
  (merkleLevel H k leaves (Nat.clog 2 leaves.length)).headD []

/-- The position of the sibling of node `p` within its level. -/
def merkleSibling (p : ℕ) : ℕ :=
  if p % 2 = 0 then p + 1 else p - 1

/-- One step of `merklePath`: record the sibling of the current node, then move to the parent
level and position. -/
def merklePathStep (state : List (List Bool) × ℕ × List (List Bool)) :
    List (List Bool) × ℕ × List (List Bool) :=
  let (level, pos, path) := state
  (merkleParents H k level, pos / 2,
    path ++ [level.getD (merkleSibling pos) []])

/-- The authentication path of position `i`: the sibling of each node on the way from leaf `i` up
to the root, starting at the leaves ([BonehShoup2023], Figure 8.12). -/
def merklePath (leaves : List (List Bool)) (i : ℕ) : List (List Bool) :=
  let (_, _, path) :=
    (merklePathStep H k)^[Nat.clog 2 leaves.length] (merkleLeafLevel H k leaves, i, [])
  path

/-! ### Recomputing a root from an opening -/

/-- One step of `merkleInputs`: hash the current input to a node and pair it with `sibling`,
putting the node on the left when the current position is even. -/
def merkleInputsStep (state : List (List Bool) × ℕ) (sibling : List Bool) :
    List (List Bool) × ℕ :=
  let node := H k (state.1.headD [])
  ((if state.2 % 2 = 0 then encPair encBits encBits (node, sibling)
    else encPair encBits encBits (sibling, node)) :: state.1, state.2 / 2)

/-- The hash inputs met while recomputing a root from `leaf` at position `i` along `path`, from
the input of the root down to `leaf` itself. -/
def merkleInputs (leaf : List Bool) (i : ℕ) (path : List (List Bool)) : List (List Bool) :=
  (path.foldl (merkleInputsStep H k) ([leaf], i)).1

/-- The root recomputed from `leaf` at position `i` along the authentication path `path`
([BonehShoup2023], (8.16)). Only the low `path.length` bits of `i` are read, and nothing checks
the path length: a verifier must fix `path.length` to the depth `d` and check `i < 2 ^ d` (see
the module documentation). -/
def merkleRootOfPath (leaf : List Bool) (i : ℕ) (path : List (List Bool)) : List Bool :=
  H k ((merkleInputs H k leaf i path).headD [])

/-- The first pair of differing hash inputs, from the root down, of two openings of position `i`,
or `([], [])` if there is none. -/
def extractMerkleCollision (leaf₁ leaf₂ : List Bool) (i : ℕ) (path₁ path₂ : List (List Bool)) :
    List Bool × List Bool :=
  (((merkleInputs H k leaf₁ i path₁).zip (merkleInputs H k leaf₂ i path₂)).find?
    (fun p => p.1 != p.2)).getD ([], [])

variable {H k}

/-! ### Shape of the tree -/

/-- The tree over `leaves` has `2 ^ Nat.clog 2 leaves.length` hashed leaves. -/
@[simp]
theorem length_merkleLeafLevel (leaves : List (List Bool)) :
    (merkleLeafLevel H k leaves).length = 2 ^ Nat.clog 2 leaves.length := by
  simp [merkleLeafLevel]

/-- A level has half as many parents as nodes, rounded down. -/
@[simp]
theorem length_merkleParents (level : List (List Bool)) :
    (merkleParents H k level).length = level.length / 2 := by
  simp [merkleParents]

/-- Parent `i` hashes the pair of nodes `2 * i` and `2 * i + 1`. -/
theorem getD_merkleParents {level : List (List Bool)} {i : ℕ} (hi : i < level.length / 2) :
    (merkleParents H k level).getD i [] =
      H k (encPair encBits encBits (level.getD (2 * i) [], level.getD (2 * i + 1) [])) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp [merkleParents]

/-- Level `j` of the tree of depth `d = Nat.clog 2 leaves.length` has `2 ^ d / 2 ^ j` nodes. -/
theorem length_merkleLevel (leaves : List (List Bool)) (j : ℕ) :
    (merkleLevel H k leaves j).length = 2 ^ Nat.clog 2 leaves.length / 2 ^ j := by
  induction j with
  | zero => simp [merkleLevel]
  | succ j ih =>
    rw [merkleLevel, Function.iterate_succ_apply', ← merkleLevel, length_merkleParents, ih,
      Nat.div_div_eq_div_mul, ← pow_succ]

/-- Each level consists of the parents of the level below. -/
theorem merkleLevel_succ (leaves : List (List Bool)) (j : ℕ) :
    merkleLevel H k leaves (j + 1) = merkleParents H k (merkleLevel H k leaves j) := by
  rw [merkleLevel, Function.iterate_succ_apply', ← merkleLevel]

private theorem merklePathStep_iterate (leaves : List (List Bool)) (i j : ℕ) :
    (merklePathStep H k)^[j] (merkleLeafLevel H k leaves, i, []) =
      (merkleLevel H k leaves j, i / 2 ^ j, (List.range j).map fun t =>
        (merkleLevel H k leaves t).getD (merkleSibling (i / 2 ^ t)) []) := by
  induction j with
  | zero => simp [merkleLevel]
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [merklePathStep, merkleLevel_succ, Nat.div_div_eq_div_mul, ← pow_succ,
      List.range_succ, List.map_append, List.map_cons, List.map_nil]

/-- The authentication path of position `i` lists, for each level `t` below the root, the sibling
of the ancestor of leaf `i` at level `t`. -/
theorem merklePath_eq (leaves : List (List Bool)) (i : ℕ) :
    merklePath H k leaves i = (List.range (Nat.clog 2 leaves.length)).map fun t =>
      (merkleLevel H k leaves t).getD (merkleSibling (i / 2 ^ t)) [] := by
  rw [merklePath, merklePathStep_iterate]

/-- An authentication path has one sibling per level below the root. -/
@[simp]
theorem length_merklePath (leaves : List (List Bool)) (i : ℕ) :
    (merklePath H k leaves i).length = Nat.clog 2 leaves.length := by
  simp [merklePath_eq]

/-- Hashed leaves have `ℓ` bits when every digest of `H k` does. -/
theorem length_of_mem_merkleLeafLevel {ℓ : ℕ} (hlen : ∀ x, (H k x).length = ℓ)
    {leaves : List (List Bool)} {y : List Bool} (hy : y ∈ merkleLeafLevel H k leaves) :
    y.length = ℓ := by
  simp only [merkleLeafLevel, List.mem_map] at hy
  obtain ⟨_, _, rfl⟩ := hy
  exact hlen _

/-- Parents have `ℓ` bits when every digest of `H k` does. -/
theorem length_of_mem_merkleParents {ℓ : ℕ} (hlen : ∀ x, (H k x).length = ℓ)
    {level : List (List Bool)} {y : List Bool} (hy : y ∈ merkleParents H k level) :
    y.length = ℓ := by
  simp only [merkleParents, List.mem_map] at hy
  obtain ⟨_, _, rfl⟩ := hy
  exact hlen _

/-! ### Correctness of honest openings -/

private theorem merkleInputs_append (leaf : List Bool) (i : ℕ) (path : List (List Bool))
    (sibling : List Bool) :
    (path ++ [sibling]).foldl (merkleInputsStep H k) ([leaf], i) =
      merkleInputsStep H k (path.foldl (merkleInputsStep H k) ([leaf], i)) sibling :=
  List.foldl_concat _ _ _ _

/-- After folding `merkleInputsStep` along `path` from `(leaf, i)`, the position component is
`i / 2 ^ path.length`. -/
theorem snd_foldl_merkleInputsStep (leaf : List Bool) (i : ℕ) (path : List (List Bool)) :
    (path.foldl (merkleInputsStep H k) ([leaf], i)).2 = i / 2 ^ path.length := by
  induction path using List.reverseRecOn with
  | nil => simp
  | append_singleton path sibling ih =>
    rw [merkleInputs_append]
    simp only [merkleInputsStep, ih, List.length_append, List.length_singleton,
      Nat.div_div_eq_div_mul, ← pow_succ]

/-- Opening leaf `i < 2 ^ d` with its honest path recomputes, after `j` steps, the ancestor of
the leaf at level `j`. -/
private theorem hash_head_merkleInputs_take (leaves : List (List Bool)) {i : ℕ}
    (hi : i < 2 ^ Nat.clog 2 leaves.length) (j : ℕ) (hj : j ≤ Nat.clog 2 leaves.length) :
    H k ((((merklePath H k leaves i).take j).foldl (merkleInputsStep H k)
      ([leaves.getD i []], i)).1.headD []) =
      (merkleLevel H k leaves j).getD (i / 2 ^ j) [] := by
  set d := Nat.clog 2 leaves.length
  induction j with
  | zero =>
    have hlt : i < (merkleLeafLevel H k leaves).length := by simpa using hi
    simp only [List.take_zero, List.foldl_nil, List.headD_cons, merkleLevel,
      Function.iterate_zero, id, pow_zero, Nat.div_one]
    rw [List.getD_eq_getElem _ _ hlt]
    simp only [merkleLeafLevel, List.getElem_map, List.getElem_range]
  | succ j ih =>
    have hjd : j < d := hj
    have hpath : j < (merklePath H k leaves i).length := by simpa using hjd
    rw [List.take_succ_eq_append_getElem hpath, merkleInputs_append]
    have hsnd := snd_foldl_merkleInputsStep (H := H) (k := k) (leaves.getD i []) i
      ((merklePath H k leaves i).take j)
    rw [List.length_take_of_le hpath.le] at hsnd
    simp only [merkleInputsStep, List.headD_cons, hsnd, ih hjd.le]
    have hsib : (merklePath H k leaves i)[j] =
        (merkleLevel H k leaves j).getD (merkleSibling (i / 2 ^ j)) [] := by
      simp [merklePath_eq]
    rw [hsib, merkleLevel_succ]
    have hlevel := length_merkleLevel (H := H) (k := k) leaves j
    have hq : i / 2 ^ (j + 1) < (merkleLevel H k leaves j).length / 2 := by
      rw [hlevel, Nat.div_div_eq_div_mul, ← pow_succ]
      exact Nat.div_lt_div_of_lt_of_dvd (pow_dvd_pow 2 (by omega)) hi
    rw [getD_merkleParents hq]
    have hdiv : i / 2 ^ (j + 1) = i / 2 ^ j / 2 := by rw [pow_succ, Nat.div_div_eq_div_mul]
    rw [hdiv]
    rcases Nat.mod_two_eq_zero_or_one (i / 2 ^ j) with hp | hp
    · have h1 : 2 * (i / 2 ^ j / 2) = i / 2 ^ j := by omega
      simp only [hp, ↓reduceIte, merkleSibling, h1]
    · have h1 : 2 * (i / 2 ^ j / 2) = i / 2 ^ j - 1 := by omega
      have h2 : 2 * (i / 2 ^ j / 2) + 1 = i / 2 ^ j := by omega
      rw [h2, h1]
      simp only [hp, one_ne_zero, ↓reduceIte, merkleSibling]

/-- **Correctness**: opening leaf `i` with its authentication path recomputes the root. -/
theorem merkleRootOfPath_merklePath (leaves : List (List Bool)) {i : ℕ}
    (hi : i < 2 ^ Nat.clog 2 leaves.length) :
    merkleRootOfPath H k (leaves.getD i []) i (merklePath H k leaves i) =
      merkleRoot H k leaves := by
  have h := hash_head_merkleInputs_take (H := H) (k := k) leaves hi _ le_rfl
  rw [← length_merklePath (H := H) (k := k) leaves i, List.take_length] at h
  rw [merkleRootOfPath, merkleInputs, h, merkleRoot, length_merklePath,
    Nat.div_eq_of_lt hi, List.headD_eq_getD]

/-! ### Binding -/

/-- The property preserved by each step of two openings of one position: when the current hash
inputs hash to the same node, the scan of `extractMerkleCollision` finds a collision. -/
private def ScanFinds (H : List Bool → List Bool → List Bool) (k : List Bool)
    (inputs₁ inputs₂ : List (List Bool)) : Prop :=
  H k (inputs₁.headD []) = H k (inputs₂.headD []) →
    ∃ x₁ x₂, (inputs₁.zip inputs₂).find? (fun p => p.1 != p.2) = some (x₁, x₂) ∧
      H k x₁ = H k x₂

private theorem scanFinds_cons {inputs₁ inputs₂ : List (List Bool)} {a b : List Bool}
    (h : ScanFinds H k inputs₁ inputs₂)
    (hab : a = b → H k (inputs₁.headD []) = H k (inputs₂.headD [])) :
    ScanFinds H k (a :: inputs₁) (b :: inputs₂) := by
  intro hhash
  rw [List.headD_cons, List.headD_cons] at hhash
  rw [List.zip_cons_cons, List.find?_cons]
  by_cases hab' : a = b
  · subst hab'
    simp only [bne_self_eq_false]
    exact h (hab rfl)
  · simp only [bne_iff_ne.mpr hab']
    exact ⟨a, b, rfl, hhash⟩

private theorem scanFinds_step {inputs₁ inputs₂ : List (List Bool)} {i : ℕ}
    (h : ScanFinds H k inputs₁ inputs₂) (sibling₁ sibling₂ : List Bool) :
    ScanFinds H k (merkleInputsStep H k (inputs₁, i) sibling₁).1
      (merkleInputsStep H k (inputs₂, i) sibling₂).1 := by
  have hinj := (encPair encBits encBits).injective
  by_cases hi : i % 2 = 0
  · simp only [merkleInputsStep, hi, ↓reduceIte]
    exact scanFinds_cons h fun hab => congrArg Prod.fst (hinj hab)
  · simp only [merkleInputsStep, hi, ↓reduceIte]
    exact scanFinds_cons h fun hab => congrArg Prod.snd (hinj hab)

private theorem scanFinds_foldl {inputs₁ inputs₂ : List (List Bool)} {i : ℕ}
    (h : ScanFinds H k inputs₁ inputs₂) (path₁ path₂ : List (List Bool))
    (hlen : path₁.length = path₂.length) :
    ScanFinds H k (path₁.foldl (merkleInputsStep H k) (inputs₁, i)).1
      (path₂.foldl (merkleInputsStep H k) (inputs₂, i)).1 := by
  induction path₁ generalizing path₂ inputs₁ inputs₂ i with
  | nil =>
    rw [List.length_nil, eq_comm, List.length_eq_zero_iff] at hlen
    subst hlen
    exact h
  | cons sibling₁ path₁ ih =>
    cases path₂ with
    | nil => simp at hlen
    | cons sibling₂ path₂ =>
      simp only [List.foldl_cons]
      have hstep := scanFinds_step (i := i) h sibling₁ sibling₂
      exact ih hstep path₂ (by simpa using hlen)

/-- **Binding**, the deterministic reduction behind [BonehShoup2023], Theorem 8.8: two openings
of position `i` to different leaves, along paths of equal length and with the same recomputed
root, contain a collision of `H k`, which `extractMerkleCollision` finds. Equal path lengths are
essential, since leaves and internal nodes are not domain-separated; a verifier that fixes the
path length to the depth `d` and checks `i < 2 ^ d` gives this hypothesis. -/
theorem isCollision_extractMerkleCollision {leaf₁ leaf₂ : List Bool} {i : ℕ}
    {path₁ path₂ : List (List Bool)} (n : ℕ) (hlen : path₁.length = path₂.length)
    (hne : leaf₁ ≠ leaf₂)
    (hroot : merkleRootOfPath H k leaf₁ i path₁ = merkleRootOfPath H k leaf₂ i path₂) :
    isCollision H (fun _ _ => true) n k (extractMerkleCollision H k leaf₁ leaf₂ i path₁ path₂).1
      (extractMerkleCollision H k leaf₁ leaf₂ i path₁ path₂).2 = true := by
  have hbase : ScanFinds H k [leaf₁] [leaf₂] := by
    intro hhash
    exact ⟨leaf₁, leaf₂, by simp [hne], by simpa using hhash⟩
  obtain ⟨x₁, x₂, hfind, hhash⟩ := scanFinds_foldl (i := i) hbase path₁ path₂ hlen hroot
  have hne' : x₁ ≠ x₂ := by
    have := List.find?_some hfind
    simpa using this
  rw [extractMerkleCollision, merkleInputs, merkleInputs, hfind, Option.getD_some]
  simp [isCollision, hne', hhash]

/-! ### The hash inputs of a tree -/

/-- `x` pairs two `ℓ`-bit words: `x = encPair encBits encBits (l, r)` with `l` and `r` of `ℓ` bits
(`isDigestPair_eq_true_iff`). For `ℓ` the digest length, these are the hash inputs of internal
nodes, the pairs of digests `Y²` in the domain of the hash of [BonehShoup2023], Section 8.9. -/
def isDigestPair (ℓ : ℕ) (x : List Bool) : Bool :=
  (unframe x).length == ℓ && (dropFrame x).length == ℓ &&
    encPair encBits encBits (unframe x, dropFrame x) == x

/-- A pairing is a digest pair exactly when both components have `ℓ` bits. -/
theorem isDigestPair_encPair (ℓ : ℕ) (l r : List Bool) :
    isDigestPair ℓ (encPair encBits encBits (l, r)) = (l.length == ℓ && r.length == ℓ) := by
  simp [isDigestPair, encPair_apply]

/-- The digest pairs are exactly the pairings of two `ℓ`-bit words. -/
theorem isDigestPair_eq_true_iff {ℓ : ℕ} {x : List Bool} :
    isDigestPair ℓ x = true ↔
      ∃ l r, l.length = ℓ ∧ r.length = ℓ ∧ encPair encBits encBits (l, r) = x := by
  constructor
  · intro h
    simp only [isDigestPair, Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨_, _, h.1.1, h.1.2, h.2⟩
  · rintro ⟨l, r, hl, hr, rfl⟩
    rw [isDigestPair_encPair, hl, hr, beq_self_eq_true, Bool.and_self]

/-- **Every hash input of an opening lies in the hash's domain**: when every digest of `H k` and
every label of `path` has `ℓ` bits, each hash input met while recomputing a root is the opened
leaf or a pair of `ℓ`-bit digests. -/
theorem eq_or_isDigestPair_of_mem_merkleInputs {ℓ : ℕ} (hlen : ∀ x, (H k x).length = ℓ)
    {leaf : List Bool} {i : ℕ} {path : List (List Bool)} (hpath : ∀ s ∈ path, s.length = ℓ)
    {x : List Bool} (hx : x ∈ merkleInputs H k leaf i path) :
    x = leaf ∨ isDigestPair ℓ x = true := by
  suffices h : ∀ (path : List (List Bool)) (state : List (List Bool) × ℕ),
      (∀ s ∈ path, s.length = ℓ) → (∀ y ∈ state.1, y = leaf ∨ isDigestPair ℓ y = true) →
        ∀ y ∈ (path.foldl (merkleInputsStep H k) state).1, y = leaf ∨ isDigestPair ℓ y = true from
    h path ([leaf], i) hpath (by simp) x hx
  intro path
  induction path with
  | nil => exact fun _ _ hstate => hstate
  | cons s path ih =>
    intro state hs hstate
    refine ih _ (fun t ht => hs t (List.mem_cons_of_mem _ ht)) fun y hy => ?_
    simp only [merkleInputsStep, List.mem_cons] at hy
    rcases hy with rfl | hy
    · right
      split <;> rw [isDigestPair_encPair] <;> simp [hlen, hs s List.mem_cons_self]
    · exact hstate y hy

/-- The two words found by `extractMerkleCollision`, when they differ, are hash inputs of the two
openings. -/
theorem mem_merkleInputs_of_extractMerkleCollision {leaf₁ leaf₂ : List Bool} {i : ℕ}
    {path₁ path₂ : List (List Bool)}
    (hne : (extractMerkleCollision H k leaf₁ leaf₂ i path₁ path₂).1 ≠
      (extractMerkleCollision H k leaf₁ leaf₂ i path₁ path₂).2) :
    (extractMerkleCollision H k leaf₁ leaf₂ i path₁ path₂).1 ∈ merkleInputs H k leaf₁ i path₁ ∧
      (extractMerkleCollision H k leaf₁ leaf₂ i path₁ path₂).2 ∈
        merkleInputs H k leaf₂ i path₂ := by
  unfold extractMerkleCollision at hne ⊢
  cases hfind : ((merkleInputs H k leaf₁ i path₁).zip (merkleInputs H k leaf₂ i path₂)).find?
      (fun p => p.1 != p.2) with
  | none => simp [hfind] at hne
  | some p =>
    rw [Option.getD_some]
    exact List.of_mem_zip (List.mem_of_find?_eq_some hfind)

/-! ### Polynomial time -/

section PolyTime

variable {γ : Type} {encIn : γ ↪ List Bool}

private theorem pow_clog_two_le (L : ℕ) : 2 ^ Nat.clog 2 L ≤ 2 * L + 1 := by
  rcases eq_or_ne L 0 with rfl | hL
  · simp
  · exact (Nat.pow_clog_le_mul (by norm_num) hL).trans (Nat.le_succ _)

private def LevelInv (key : List Bool) (L : ℕ) (level : List (List Bool)) : Prop :=
  (∀ y ∈ level, y.length = key.length) ∧ level.length ≤ 2 ^ Nat.clog 2 L

private theorem levelInv_merkleLeafLevel (hlen : ∀ k x, (H k x).length = k.length)
    (key : List Bool) (leaves : List (List Bool)) :
    LevelInv key leaves.length (merkleLeafLevel H key leaves) :=
  ⟨fun _ hy => length_of_mem_merkleLeafLevel (hlen key) hy, (length_merkleLeafLevel leaves).le⟩

private theorem LevelInv.merkleParents {key : List Bool} {L : ℕ} {level : List (List Bool)}
    (h : LevelInv key L level) (hlen : ∀ k x, (H k x).length = k.length) :
    LevelInv key L (Cslib.Crypto.merkleParents H key level) :=
  ⟨fun _ hy => length_of_mem_merkleParents (hlen key) hy,
    (length_merkleParents level).le.trans ((Nat.div_le_self _ _).trans h.2)⟩

private theorem length_encList_level_le {L : ℕ} {key : List Bool} {level : List (List Bool)}
    (hy : ∀ y ∈ level, y.length ≤ key.length) (hL : level.length ≤ 2 ^ Nat.clog 2 L) :
    (encList encBits level).length ≤ (2 * L + 1) * (2 * key.length + 1) :=
  (length_encList_le encBits _ hy).trans (Nat.mul_le_mul_right _ (hL.trans (pow_clog_two_le L)))

@[local fun_prop]
private theorem computableInPolyTime_merkleLeafLevel
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    {k : γ → List Bool} {leaves : γ → List (List Bool)}
    (hk : ComputableInPolyTime k encIn encBits)
    (hleaves : ComputableInPolyTime leaves encIn (encList encBits)) :
    ComputableInPolyTime (fun a => merkleLeafLevel H (k a) (leaves a)) encIn
      (encList encBits) := by
  polytime [merkleLeafLevel]

@[local fun_prop]
private theorem computableInPolyTime_merkleParents
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    {k : γ → List Bool} {level : γ → List (List Bool)}
    (hk : ComputableInPolyTime k encIn encBits)
    (hlevel : ComputableInPolyTime level encIn (encList encBits)) :
    ComputableInPolyTime (fun a => merkleParents H (k a) (level a)) encIn
      (encList encBits) := by
  dsimp only [merkleParents]
  apply ComputableInPolyTime.mapWithInput (encA := encUnary) (by polytime)
  polytime

private theorem computableInPolyTime_iterate_merkleParents
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k x, (H k x).length = k.length) :
    ComputableInPolyTime (fun p : List Bool × List (List Bool) =>
      (merkleParents H p.1)^[Nat.clog 2 p.2.length] (merkleLeafLevel H p.1 p.2))
      (encPair encBits (encList encBits)) (encList encBits) := by
  refine (ComputableInPolyTime.iterateWith_spec
    (par := fun p : List Bool × List (List Bool) => p.1)
    (count := fun p => Nat.clog 2 p.2.length)
    (step := fun k level => merkleParents H k level)
    (by polytime) (by polytime) (by polytime) (by polytime)
    (fun p _ level => LevelInv p.1 p.2.length level)
    (fun p => levelInv_merkleLeafLevel hlen p.1 p.2)
    (fun _ _ _ _ hinv => hinv.merkleParents hlen)
    (size := fun p => (2 * p.2.length + 1) * (2 * p.1.length + 1))
    (by growth_poly)
    (fun _ _ _ _ hinv => length_encList_level_le (fun y hy => (hinv.1 y hy).le) hinv.2)).1

/-- Computing the root of a Merkle tree is polynomial-time for a polynomial-time keyed hash whose
digests have the length of the key. -/
@[program_certificate]
theorem computableInPolyTime_merkleRoot
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k x, (H k x).length = k.length) :
    ComputableInPolyTime (fun p : List Bool × List (List Bool) => merkleRoot H p.1 p.2)
      (encPair encBits (encList encBits)) encBits :=
  ComputableInPolyTime.listHeadDWithInput
    (computableInPolyTime_iterate_merkleParents hH hlen) (.const [])

private theorem computableInPolyTime_merklePathStep
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits) :
    ComputableInPolyTime
      (fun p : List Bool × (List (List Bool) × ℕ × List (List Bool)) => merklePathStep H p.1 p.2)
      (encPair encBits (encPair (encList encBits) (encPair encUnary (encList encBits))))
      (encPair (encList encBits) (encPair encUnary (encList encBits))) := by
  polytime [merklePathStep, merkleSibling]

/-- Computing an authentication path is polynomial-time for a polynomial-time keyed hash whose
digests have the length of the key. -/
@[program_certificate]
theorem computableInPolyTime_merklePath
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k x, (H k x).length = k.length) :
    ComputableInPolyTime
      (fun p : List Bool × List (List Bool) × ℕ => merklePath H p.1 p.2.1 p.2.2)
      (encPair encBits (encPair (encList encBits) encUnary)) (encList encBits) := by
  have hiter := (ComputableInPolyTime.iterateWith_spec
    (encIn := encPair encBits (encPair (encList encBits) encUnary))
    (par := fun p : List Bool × List (List Bool) × ℕ => p.1)
    (count := fun p => Nat.clog 2 p.2.1.length)
    (init := fun p => (merkleLeafLevel H p.1 p.2.1, p.2.2, []))
    (step := fun k state => merklePathStep H k state)
    (by polytime) (by polytime) (by polytime) (computableInPolyTime_merklePathStep hH)
    (fun p j state => LevelInv p.1 p.2.1.length state.1 ∧ state.2.1 ≤ p.2.2 ∧
      (∀ y ∈ state.2.2, y.length ≤ p.1.length) ∧ state.2.2.length ≤ j)
    (fun p => ⟨levelInv_merkleLeafLevel hlen p.1 p.2.1, le_rfl, by simp, by simp⟩)
    (fun p j state _ hinv => ⟨hinv.1.merkleParents hlen,
      (Nat.div_le_self _ _).trans hinv.2.1,
      by
        intro y hy
        simp only [merklePathStep, List.mem_append, List.mem_singleton] at hy
        rcases hy with hy | rfl
        · exact hinv.2.2.1 y hy
        · rcases List.getD_mem_or state.1 (merkleSibling state.2.1) [] with hmem | hnil
          · exact (hinv.1.1 _ hmem).le
          · simp only [hnil, List.length_nil, zero_le],
      by simpa [merklePathStep] using hinv.2.2.2⟩)
    (size := fun p => 3 * ((2 * p.2.1.length + 1) * (2 * p.1.length + 1)) + 2 * p.2.2 + 2)
    (by growth_poly) ?_).1
  · exact (ComputableInPolyTime.snd _ _).comp
      ((ComputableInPolyTime.snd _ _).comp hiter)
  · intro p j state hj hinv
    have hlevel := length_encList_level_le (fun y hy => (hinv.1.1 y hy).le) hinv.1.2
    have hpath := length_encList_level_le hinv.2.2.1
      (hinv.2.2.2.trans (hj.trans (Nat.lt_pow_self (by norm_num)).le))
    simp only [encPair_apply, encUnary_apply, List.length_append, length_frame,
      List.length_replicate]
    have := hinv.2.1
    omega

/-- Computing the list of hash inputs along a Merkle authentication path is polynomial-time for a
polynomial-time keyed hash whose digests have the length of the key. -/
@[program_certificate]
theorem computableInPolyTime_merkleInputs
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k x, (H k x).length = k.length)
    {k leaf : γ → List Bool} {i : γ → ℕ} {path : γ → List (List Bool)}
    (hk : ComputableInPolyTime k encIn encBits)
    (hleaf : ComputableInPolyTime leaf encIn encBits)
    (hi : ComputableInPolyTime i encIn encUnary)
    (hpath : ComputableInPolyTime path encIn (encList encBits)) :
    ComputableInPolyTime (fun a => merkleInputs H (k a) (leaf a) (i a) (path a)) encIn
      (encList encBits) := by
  have hfold := ComputableInPolyTime.foldlWith_of_bounded_growth
    (encA := encBits) (encL := encList encBits) (encP := encBits)
    (encB := encPair (encList encBits) encUnary)
    (init := fun a => ([leaf a], i a))
    (step := fun k state sibling => merkleInputsStep H k state sibling)
    hk hpath (by polytime) (by polytime [merkleInputsStep])
    (growth := fun a => 8 * (k a).length + 8 * (encList encBits (path a)).length + 6)
    ((((PolyBounded.const 8).mul hk.polyBounded_length).add
      ((PolyBounded.const 8).mul hpath.polyBounded_length)).add (.const 6))
    (by
      intro a state sibling hmem
      have hsib : sibling.length ≤ (encList encBits (path a)).length := by
        have := List.le_sum_of_mem (List.mem_map_of_mem (f := fun x : List Bool => x.length) hmem)
        exact this.trans ((sum_length_le_length_encList encBits (path a)).trans_eq' (by simp))
      have hnode := hlen (k a) (state.1.headD [])
      unfold merkleInputsStep
      split_ifs <;>
      · simp only [encPair_apply, encBits_apply, encUnary_apply, encList_cons, List.length_append,
          length_frame, List.length_replicate, hnode]
        have := Nat.div_le_self state.2 2
        omega)
  exact (ComputableInPolyTime.fst _ _).comp hfold

attribute [local fun_prop] computableInPolyTime_merkleInputs

/-- Recomputing a root from an opening is polynomial-time for a polynomial-time keyed hash whose
digests have the length of the key. -/
@[program_certificate]
theorem computableInPolyTime_merkleRootOfPath
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k x, (H k x).length = k.length) :
    ComputableInPolyTime
      (fun p : List Bool × List Bool × ℕ × List (List Bool) =>
        merkleRootOfPath H p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair encBits (encPair encBits (encPair encUnary (encList encBits)))) encBits := by
  polytime [merkleRootOfPath]

/-- Extracting a collision from two openings is polynomial-time for a polynomial-time keyed hash
whose digests have the length of the key. -/
@[program_certificate]
theorem computableInPolyTime_extractMerkleCollision
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k x, (H k x).length = k.length) :
    ComputableInPolyTime
      (fun p : List Bool × (List Bool × List Bool) × ℕ × List (List Bool) × List (List Bool) =>
        extractMerkleCollision H p.1 p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
      (encPair encBits (encPair (encPair encBits encBits)
        (encPair encUnary (encPair (encList encBits) (encList encBits)))))
      (encPair encBits encBits) := by
  let E := encPair encBits (encPair (encPair encBits encBits)
    (encPair encUnary (encPair (encList encBits) (encList encBits))))
  have hinputs₁ : ComputableInPolyTime
      (fun p => merkleInputs H p.1 p.2.1.1 p.2.2.1 p.2.2.2.1) E (encList encBits) := by polytime
  have hinputs₂ : ComputableInPolyTime
      (fun p => merkleInputs H p.1 p.2.1.2 p.2.2.1 p.2.2.2.2) E (encList encBits) := by polytime
  have hzip := (ComputableInPolyTime.zip encBits encBits).comp (hinputs₁.prod hinputs₂)
  exact ComputableInPolyTime.optionGetDWithInput
    (ComputableInPolyTime.findWithInput (test := fun _ p => p.1 != p.2) hzip (by polytime))
    (.const ([], []))

end PolyTime

end Cslib.Crypto
