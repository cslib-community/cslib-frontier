/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Transcript
import Mathlib.Data.Nat.Bitwise

/-!
# MQOM correlated-tree indices and validation transcripts

The correlated-tree variant of MQOM v3 uses a perfect binary tree with `N = 2 ^ height` leaves
and the one-based heap convention of Algorithms 21--23 in [MQOM2026, Section 2.5.4, pp. 32--33].
Leaf `i` is node `N + i`. Its opening lists one sibling per level, starting at the leaf: replace
the current node by `node ^^^ 1`, then move the hidden node to `node / 2`.
The revealed sibling nodes are disjoint from the entire hidden path, including the challenged
leaf and the root. The generic Merkle API instead uses zero-based positions local to each level;
these declarations keep the source's global heap indices rather than identify the representations.

The PGOW-MQ validation oracle in [MQOM2026, Definition 2, pp. 69--70] returns true exactly when a
candidate is the designated secret prefix. `validationTranscript` records chronological calls
using the library's existing reverse-chronological `Cslib.OracleComp.Transcript` convention.
`ValidationRun.accepted` checks the final output separately: the final challenger check is not an
extra adversary query and the output need not have appeared in the transcript.

This module contains no node labels, seed expansion, MQ arithmetic or sampled game. In
particular, it states no runtime, success-probability, hardness or unforgeability result.

## Main definitions

* `Cslib.Crypto.MQOM.leafNode`: the one-based heap node of a correlated-tree leaf.
* `Cslib.Crypto.MQOM.siblingPathNodes`: the bottom-up node indices in an opening.
* `Cslib.Crypto.MQOM.validationReply`: the exact-equality validation oracle.
* `Cslib.Crypto.MQOM.validationTranscript`: replies in the existing typed transcript format.
* `Cslib.Crypto.MQOM.ValidationRun`: prior calls and the separately checked final output.

## Main results

* `Cslib.Crypto.MQOM.siblingNode_parent_eq_hiddenNode_succ`: a path entry's parent is the next
  hidden ancestor.
* `Cslib.Crypto.MQOM.siblingNode_pos`, `.siblingNode_lt`: path entries lie in the tree array.
* `Cslib.Crypto.MQOM.siblingNode_ne_hiddenNode`: no path entry is the challenged leaf or any of
  its hidden ancestors.

## References

* [R. Benadjila, C. Bouillaguet, T. Feneuil, M. Rivain, *MQOM: MQ on my Mind, Algorithm
  Specifications and Supporting Documentation*, version 3.0][MQOM2026]
-/

public section

namespace Cslib.Crypto.MQOM

/-! ### Correlated-tree indices -/

/-- The `N = 2 ^ height` leaf positions of an MQOM correlated tree. -/
abbrev LeafIndex (height : Nat) := Fin (2 ^ height)

/-- One-based heap index `N + i` of leaf `i`, as in Algorithms 22--23. -/
@[expose] def leafNode {height : Nat} (leaf : LeafIndex height) : Nat :=
  2 ^ height + leaf

/-- Move a one-based heap node towards the root by repeated parent steps. -/
@[expose] def ancestorNode (node : Nat) : Nat → Nat
  | 0 => node
  | level + 1 => ancestorNode node level / 2

/-- The hidden node after `level` parent steps. The root is available at level `height`. -/
@[expose] def hiddenNode {height : Nat} (leaf : LeafIndex height)
    (level : Fin (height + 1)) : Nat :=
  ancestorNode (leafNode leaf) level

/-- The sibling revealed at a bottom-up opening level. -/
@[expose] def siblingNode {height : Nat} (leaf : LeafIndex height)
    (level : Fin height) : Nat :=
  hiddenNode leaf (Fin.castSucc level) ^^^ 1

/-- Algorithms 22--23's sibling indices, ordered from the leaf level towards the root. -/
@[expose] def siblingPathNodes {height : Nat} (leaf : LeafIndex height) : List Nat :=
  List.ofFn (siblingNode leaf)

@[simp] theorem ancestorNode_zero (node : Nat) : ancestorNode node 0 = node := rfl

@[simp] theorem ancestorNode_succ (node level : Nat) :
    ancestorNode node (level + 1) = ancestorNode node level / 2 := rfl

theorem ancestorNode_le (node level : Nat) : ancestorNode node level ≤ node := by
  induction level with
  | zero => exact le_rfl
  | succ level ih =>
    rw [ancestorNode]
    exact (Nat.div_le_self _ _).trans ih

theorem ancestorNode_eq_div_pow (node level : Nat) :
    ancestorNode node level = node / 2 ^ level := by
  induction level with
  | zero => simp only [ancestorNode_zero, pow_zero, Nat.div_one]
  | succ level ih => rw [ancestorNode, ih, Nat.div_div_eq_div_mul, Nat.pow_succ]

theorem leafNode_lt {height : Nat} (leaf : LeafIndex height) :
    leafNode leaf < 2 * 2 ^ height := by
  have hleaf := leaf.isLt
  simp only [leafNode] at *
  omega

@[simp] theorem hiddenNode_zero {height : Nat} (leaf : LeafIndex height) :
    hiddenNode leaf (0 : Fin (height + 1)) = leafNode leaf := rfl

/-- One more source loop iteration moves the hidden node to its parent. -/
theorem hiddenNode_succ {height : Nat} (leaf : LeafIndex height) (level : Fin height) :
    hiddenNode leaf level.succ = hiddenNode leaf (Fin.castSucc level) / 2 := rfl

theorem hiddenNode_lt {height : Nat} (leaf : LeafIndex height)
    (level : Fin (height + 1)) : hiddenNode leaf level < 2 * 2 ^ height :=
  (ancestorNode_le (leafNode leaf) level).trans_lt (leafNode_lt leaf)

private theorem siblingNode_cases {height : Nat} (leaf : LeafIndex height) (level : Fin height) :
    2 ≤ hiddenNode leaf (Fin.castSucc level) ∧
      ∃ k, (hiddenNode leaf (Fin.castSucc level) = 2 * k ∧ siblingNode leaf level = 2 * k + 1) ∨
        (hiddenNode leaf (Fin.castSucc level) = 2 * k + 1 ∧ siblingNode leaf level = 2 * k) := by
  refine ⟨?_, ?_⟩
  · simp only [hiddenNode, ancestorNode_eq_div_pow, Nat.le_div_iff_mul_le (Nat.two_pow_pos _),
      ← Nat.pow_succ']
    exact (Nat.pow_le_pow_right (by decide) (Nat.succ_le_iff.mpr level.isLt)).trans
      (Nat.le_add_right _ _)
  · rcases Nat.even_or_odd (hiddenNode leaf (Fin.castSucc level)) with ⟨k, hk⟩ | ⟨k, hk⟩
    · refine ⟨k, .inl ⟨by omega, ?_⟩⟩
      rw [siblingNode, Nat.xor_one_of_even ⟨k, hk⟩]
      omega
    · refine ⟨k, .inr ⟨hk, ?_⟩⟩
      rw [siblingNode, Nat.xor_one_of_odd ⟨k, hk⟩]
      omega

/-- A sibling-path index is nonzero, as required by the source tree array. -/
theorem siblingNode_pos {height : Nat} (leaf : LeafIndex height) (level : Fin height) :
    0 < siblingNode leaf level := by
  obtain ⟨_, _, ⟨_, _⟩ | ⟨_, _⟩⟩ := siblingNode_cases leaf level <;> omega

/-- A sibling-path index is at most the final source tree-array index `2N - 1`. -/
theorem siblingNode_lt {height : Nat} (leaf : LeafIndex height) (level : Fin height) :
    siblingNode leaf level < 2 * 2 ^ height := by
  have := hiddenNode_lt leaf (Fin.castSucc level)
  obtain ⟨_, _, ⟨_, _⟩ | ⟨_, _⟩⟩ := siblingNode_cases leaf level <;> omega

/-- The revealed node and the hidden node are the two children of the same parent. -/
theorem siblingNode_parent {height : Nat} (leaf : LeafIndex height) (level : Fin height) :
    siblingNode leaf level / 2 = hiddenNode leaf (Fin.castSucc level) / 2 := by
  obtain ⟨_, _, ⟨_, _⟩ | ⟨_, _⟩⟩ := siblingNode_cases leaf level <;> omega

/-- After revealing the sibling, the source loop moves the hidden node to their common parent. -/
theorem siblingNode_parent_eq_hiddenNode_succ {height : Nat} (leaf : LeafIndex height)
    (level : Fin height) : siblingNode leaf level / 2 = hiddenNode leaf level.succ := by
  rw [siblingNode_parent, hiddenNode_succ]

private theorem hiddenNode_le_div_two_of_lt {height : Nat} (leaf : LeafIndex height)
    {lower higher : Fin (height + 1)} (hlevel : lower < higher) :
    hiddenNode leaf higher ≤ hiddenNode leaf lower / 2 := by
  simp only [hiddenNode, ancestorNode_eq_div_pow, Nat.div_div_eq_div_mul, ← Nat.pow_succ]
  exact Nat.div_le_div_left (Nat.pow_le_pow_right (by decide) hlevel) (Nat.two_pow_pos _)

/-- No sibling-path entry is the challenged leaf or any node on its hidden path. -/
theorem siblingNode_ne_hiddenNode {height : Nat} (leaf : LeafIndex height)
    (level : Fin height) (hiddenLevel : Fin (height + 1)) :
    siblingNode leaf level ≠ hiddenNode leaf hiddenLevel := by
  obtain ⟨h2, _, hpar⟩ := siblingNode_cases leaf level
  rcases lt_trichotomy (Fin.castSucc level) hiddenLevel with hlt | rfl | hgt
  · have := hiddenNode_le_div_two_of_lt leaf hlt
    rcases hpar with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
  · rcases hpar with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
  · have := (Nat.le_div_iff_mul_le (by decide : 0 < 2)).1 (hiddenNode_le_div_two_of_lt leaf hgt)
    rcases hpar with ⟨_, _⟩ | ⟨_, _⟩ <;> omega

/-! ### Validation-oracle transcripts -/

/-- A candidate for the `k` field coordinates in the PGOW-MQ validation oracle. -/
abbrev ValidationPrefix (Coordinate : Type) (width : Nat) := Fin width → Coordinate

/-- The validation interface returns one Boolean for every candidate prefix. -/
abbrev ValidationResponse (Coordinate : Type) (width : Nat) :
    ValidationPrefix Coordinate width → Type :=
  fun _ => Bool

/-- Definition 2's validation oracle: accept exactly the designated secret prefix. -/
@[expose] def validationReply {Coordinate : Type} [DecidableEq Coordinate] {width : Nat}
    (secret candidate : ValidationPrefix Coordinate width) : Bool :=
  decide (candidate = secret)

theorem validationReply_eq_true_iff {Coordinate : Type} [DecidableEq Coordinate] {width : Nat}
    {secret candidate : ValidationPrefix Coordinate width} :
    validationReply secret candidate = true ↔ candidate = secret := by
  simp only [validationReply, decide_eq_true_eq]

theorem validationReply_eq_false_iff {Coordinate : Type} [DecidableEq Coordinate] {width : Nat}
    {secret candidate : ValidationPrefix Coordinate width} :
    validationReply secret candidate = false ↔ candidate ≠ secret := by
  simp only [validationReply, decide_eq_false_iff_not]

/-- The replies to chronological calls, stored newest first as `OracleComp.withTranscript` does.
Wrong and repeated candidates remain present and therefore remain charged queries. -/
@[expose] def validationTranscript {Coordinate : Type} [DecidableEq Coordinate] {width : Nat}
    (secret : ValidationPrefix Coordinate width)
    (queries : List (ValidationPrefix Coordinate width)) :
    OracleComp.Transcript (ValidationResponse Coordinate width) :=
  queries.reverse.map fun candidate => ⟨candidate, validationReply secret candidate⟩

/-- Earlier chronological calls form the suffix of the stored transcript. -/
theorem validationTranscript_append {Coordinate : Type} [DecidableEq Coordinate] {width : Nat}
    (secret : ValidationPrefix Coordinate width)
    (earlier later : List (ValidationPrefix Coordinate width)) :
    validationTranscript secret (earlier ++ later) =
      validationTranscript secret later ++ validationTranscript secret earlier := by
  simp only [validationTranscript, List.reverse_append, List.map_append]

/-- A newly appended chronological call becomes the head of the stored transcript. -/
theorem validationTranscript_append_singleton {Coordinate : Type} [DecidableEq Coordinate]
    {width : Nat} (secret : ValidationPrefix Coordinate width)
    (queries : List (ValidationPrefix Coordinate width))
    (candidate : ValidationPrefix Coordinate width) :
    validationTranscript secret (queries ++ [candidate]) =
      ⟨candidate, validationReply secret candidate⟩ :: validationTranscript secret queries := by
  rw [validationTranscript_append]
  rfl

/-- Forgetting replies recovers the calls in the reverse-chronological storage order. -/
theorem queries_validationTranscript {Coordinate : Type} [DecidableEq Coordinate] {width : Nat}
    (secret : ValidationPrefix Coordinate width)
    (queries : List (ValidationPrefix Coordinate width)) :
    (validationTranscript secret queries).map (fun entry => entry.1) = queries.reverse := by
  simp only [validationTranscript, List.map_map, Function.comp_def, List.map_id_fun', id_eq]

/-- The observable part of a PGOW validation run. `queries` are chronological adversary calls;
`output` is checked by the challenger after those calls. -/
structure ValidationRun (Coordinate : Type) (width : Nat) where
  /-- Chronological validation-oracle calls, including failed and repeated candidates. -/
  queries : List (ValidationPrefix Coordinate width)
  /-- The final candidate returned to the challenger. -/
  output : ValidationPrefix Coordinate width

namespace ValidationRun

variable {Coordinate : Type} [DecidableEq Coordinate] {width : Nat}

/-- The exact transcript observable from the run's adversary calls. -/
@[expose] def transcript (run : ValidationRun Coordinate width)
    (secret : ValidationPrefix Coordinate width) :
    OracleComp.Transcript (ValidationResponse Coordinate width) :=
  validationTranscript secret run.queries

/-- The source resource `Q`: adversary oracle calls, excluding the final challenger check. -/
@[expose] def queryCount (run : ValidationRun Coordinate width) : Nat := run.queries.length

/-- Whether the separately returned final candidate is accepted. -/
@[expose] def accepted (run : ValidationRun Coordinate width)
    (secret : ValidationPrefix Coordinate width) : Bool :=
  validationReply secret run.output

theorem accepted_eq_true_iff (run : ValidationRun Coordinate width)
    (secret : ValidationPrefix Coordinate width) :
    run.accepted secret = true ↔ run.output = secret := by
  exact validationReply_eq_true_iff

end ValidationRun

end Cslib.Crypto.MQOM
