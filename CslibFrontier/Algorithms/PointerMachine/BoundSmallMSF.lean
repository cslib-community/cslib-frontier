/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.PointerMachine.BindMSF
import all CslibFrontier.Algorithms.PointerMachine.SmallMSF

/-!
# Reusing one compiled MSF topology across aligned inputs

An unweighted topology determines all tree and output records. After their construction,
the same address layout accepts further edge lists aligned with the local labels. The program
binds the input weights, traverses the optimal comparison tree, and marks the selected physical
input records. The structure of the entire table survives each run.

See [Pettie and Ramachandran, §6][PettieRamachandran2002].
-/

public section

namespace Cslib.PointerMachine.ComparisonTree.Binding

open Cslib.Query Cslib.Multigraph

variable {W : Type} [Inhabited W] [LinearOrder W] {m n : ℕ}

/-- A reusable tree representation. Every attainable leaf has a materialized list of local
edge labels in the heap. Attainability here includes tied weight orders. -/
structure Ready (ends : Fin m → Sym2 (Fin n)) (H : List (Record (model W) layout))
    (root : ℕ) (out : Finset (Fin m) → Pointer) : Prop where
  /-- The tree's comparison and child pointers, independent of weight values. -/
  stored : Stored H Fin.val out (optimalMSFProgram ends) root
  /-- The list at the returned leaf reports its local edge labels. -/
  answers : ∀ w : Fin m → W, ∃ es : List (Fin m),
    EdgeList H (out ((optimalMSFProgram ends).eval (LEQuery.keyOracle w))) es ∧
      es.toFinset = (optimalMSFProgram ends).eval (LEQuery.keyOracle w) ∧ es.Nodup

/-- Rebinding does not invalidate a compiled topology or its leaves. -/
theorem Ready.preserve {ends : Fin m → Sym2 (Fin n)} {H K : List (Record (model W) layout)}
    {root : ℕ} {out : Finset (Fin m) → Pointer} (t : Ready ends H root out)
    (keep : Preserves H K) : Ready ends K root out := by
  refine ⟨keep.stored t.stored, ?_⟩
  intro w
  obtain ⟨es, list, labels, length⟩ := t.answers w
  exact ⟨es, keep.edgeList list, labels, length⟩

/-- Append one compiled topology and its leaf lists to storage reserved for the edge slots
and inputs. The caller can use its root and output map with any subsequently aligned input. -/
def compile (ends : Fin m → Sym2 (Fin n)) (before : List (Record (model W) layout)) :
    List (Record (model W) layout) × ℕ × (Finset (Fin m) → Pointer) :=
  let p := optimalMSFProgram ends
  let entries := outputs before (leaves p)
  (entries.1 ++ encode Fin.val entries.2 p entries.1.length, entries.1.length, entries.2)

/-- Compiling the topology once yields a reusable physical table. Old heap addresses retain
their records, so data lists loaded in advance keep their representation. -/
theorem compile_spec (ends : Fin m → Sym2 (Fin n)) (before : List (Record (model W) layout)) :
    let (heap, root, out) := compile ends before
    Ready ends heap root out ∧ ∃ extra, heap = before ++ extra := by
  let p := optimalMSFProgram ends
  let entries := outputs before (leaves p)
  let tree := encode (W := W) Fin.val entries.2 p entries.1.length
  obtain ⟨⟨extra, pre⟩, payloads⟩ := outputs_spec before (leaves p)
  refine ⟨⟨?_, ?_⟩, ⟨extra ++ tree, ?_⟩⟩
  · simpa [compile, entries, p] using stored_encode (W := W) Fin.val entries.2 p entries.1 []
  · intro w
    let F := p.eval (LEQuery.keyOracle w)
    refine ⟨edgeLabels F, (payloads F (eval_mem_leaves p w)).append tree, labels_eq F, ?_⟩
    exact (List.nodup_finRange m).filter _
  · change entries.1 ++ tree = _
    change entries.1 = before ++ extra at pre
    rw [pre, List.append_assoc]

/-- Given aligned lists, the input-edge flags after the run specify the actual original MSF
when initially clear. The bound charges the binding loop, optimal comparisons, and physical
output decoding; all comparison and leaf records remain ready for the next instance. -/
theorem Ready.solve {ends : Fin m → Sym2 (Fin n)} {root : ℕ} {out : Finset (Fin m) → Pointer}
    (w : Fin m → W) (hw : Function.Injective w) (actual : Fin m → ℕ)
    (unique : Function.Injective actual) (apart : ∀ i, m ≤ actual i)
    (x : State (model W) layout) (ready : Ready ends x.heap root out) (pc : x.pc = 12)
    (node : x.ptr 0 = some root) (zero : x.ptr 3 = none)
    (chain : Aligned x.heap (x.ptr 1) (x.ptr 2) (items actual w)) :
    let Q := (optimalMSFProgram ends).countQueries (LEQuery.keyOracle w)
    let F := msf ends w Finset.univ
    ∃ y, Executes (program W) x y (instructionCount m Q F.card) ∧
      Ready ends y.heap root out ∧ ∀ i, Flagged y.heap (actual i) ↔
        Flagged x.heap (actual i) ∨ i ∈ msf ends w Finset.univ := by
  obtain ⟨es, leaf, labels, nodup⟩ := ready.answers w
  obtain ⟨y, run, frame, flags⟩ := executes (optimalMSFProgram ends) w actual apart x root out
    pc node zero chain ready.stored leaf
  have correct := (optimalMSFProgram_spec ends w hw).1
  have size := List.toFinset_card_of_nodup nodup
  rw [labels, correct] at size
  refine ⟨y, size ▸ run, ready.preserve frame, ?_⟩
  intro i
  rw [flags _ (apart i)]
  apply or_congr_right
  rw [← correct, ← labels, List.mem_toFinset]
  exact ⟨fun ⟨e, he, eq⟩ => unique eq ▸ he, fun h => ⟨i, h, rfl⟩⟩

end Cslib.PointerMachine.ComparisonTree.Binding
