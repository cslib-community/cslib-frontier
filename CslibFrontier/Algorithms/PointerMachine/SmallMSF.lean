/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.PointerMachine.ComparisonTree
public import CslibFrontier.Algorithms.Lean.MinimumSpanningForest.OptimalTree

/-!
# A pointer-machine instance of the optimal small-graph solver

Keys occupy one record per labeled edge. A leaf's output is a linked list of pointers to
the selected edge records. The input builder lays out keys, result lists, and the comparison
tree. Once loaded, a fixed pointer program returns a list denoting the actual minimum
spanning forest. Only the traversal and halt are covered by the instruction bound.
The construction realizes one topology at a time in the local decision-tree stage of
[PettieRamachandran2002], §§4.1 and 6.
-/

public section

namespace Cslib.PointerMachine.ComparisonTree

open Cslib.Query Cslib.Multigraph

variable {W : Type} [Inhabited W] [LinearOrder W] {m n : ℕ}

private abbrev Rec (W : Type) [Inhabited W] [LinearOrder W] := Record (model W) layout

/-- A null pointer denotes an empty result. Each nonempty result node points to an edge
record in field 0 and the next node in field 1. -/
inductive EdgeList (H : List (Record (model W) layout)) : Pointer → List (Fin m) → Prop where
  | nil : EdgeList H none []
  | cons {i e r rest es} (read : H[i]? = some r) (key : r.ptr 0 = some e.val)
      (next : r.ptr 1 = rest) (tail : EdgeList H rest es) : EdgeList H (some i) (e :: es)

private theorem read_append {H : List (Rec W)} {i : ℕ} {r : Rec W} (h : H[i]? = some r)
    (extra : List (Rec W)) :
    (H ++ extra)[i]? = some r := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).choose]
  exact h

private theorem EdgeList.append {H : List (Rec W)} {ptr : Pointer} {es : List (Fin m)}
    (h : EdgeList H ptr es) (extra : List (Rec W)) : EdgeList (H ++ extra) ptr es := by
  induction h with
  | nil => exact .nil
  | cons read key next _ ih => exact .cons (read_append read extra) key next ih

private def start (base : ℕ) (xs : List (Fin m)) : Pointer :=
  if xs.isEmpty then none else some base

private def payload (base : ℕ) : List (Fin m) → List (Rec W)
  | [] => []
  | e :: es =>
    ⟨fun f => if f = 0 then some e.val else start (base+1) es, fun _ => default⟩ ::
      payload (base+1) es

private theorem payload_spec (before : List (Rec W)) (es : List (Fin m)) :
    EdgeList (before ++ payload before.length es) (start before.length es) es := by
  induction es generalizing before with
  | nil => exact .nil
  | cons e es ih =>
    let r : Rec W := ⟨fun f => if f = 0 then some e.val else start (before.length+1) es,
      fun _ => default⟩
    refine .cons (r := r) ?_ rfl rfl ?_
    · simp [payload, r]
    · simpa [payload, r, List.append_assoc] using ih (before ++ [r])

private def edgeLabels (F : Finset (Fin m)) := (List.finRange m).filter fun i => i ∈ F

private theorem labels_eq (F : Finset (Fin m)) : (edgeLabels F).toFinset = F := by
  ext i
  simp [edgeLabels]

private def leaves {E O : Type} : FreeM (LEQuery E) O → List O
  | .pure o => [o]
  | .liftBind (.le _ _) k => leaves (k true) ++ leaves (k false)

omit [Inhabited W] in
private theorem eval_mem_leaves {E O : Type} (p : FreeM (LEQuery E) O) (w : E → W) :
    p.eval (LEQuery.keyOracle w) ∈ leaves p := by
  induction p using FreeM.rec with
  | pure o => exact List.mem_cons_self
  | liftBind op k ih =>
    cases op with
    | le a b =>
      by_cases h : w a ≤ w b
      · simpa [leaves, h] using Or.inl (b := _ ∈ leaves (k false)) (ih true)
      · simpa [leaves, h] using Or.inr (a := _ ∈ leaves (k true)) (ih false)

private def outputs (before : List (Rec W)) : List (Finset (Fin m)) →
    List (Rec W) × (Finset (Fin m) → Pointer)
  | [] => (before, fun _ => none)
  | f :: fs =>
    let more := outputs (before ++ payload before.length (edgeLabels f)) fs
    (more.1, fun g => if g = f then start before.length (edgeLabels f) else more.2 g)

private theorem outputs_spec (before : List (Rec W)) (fs : List (Finset (Fin m))) :
    (∃ extra, (outputs before fs).1 = before ++ extra) ∧
      ∀ f ∈ fs, EdgeList (outputs before fs).1 ((outputs before fs).2 f) (edgeLabels f) := by
  induction fs generalizing before with
  | nil => exact ⟨⟨[], (List.append_nil before).symm⟩, fun _ h => False.elim (List.not_mem_nil h)⟩
  | cons f fs ih =>
    let more := payload (W := W) before.length (edgeLabels f)
    obtain ⟨⟨t, ht⟩, valid⟩ := ih (before ++ more)
    refine ⟨⟨more ++ t, ht.trans (List.append_assoc ..)⟩, ?_⟩
    intro g hg
    by_cases eq : g = f
    · subst g
      simpa [outputs, ← ht, more] using (payload_spec before (edgeLabels f)).append t
    · have mem : g ∈ fs := (List.mem_cons.mp hg).resolve_left eq
      simpa [outputs, more, eq] using valid g mem

private def keyRecords (w : Fin m → W) : List (Rec W) :=
  List.ofFn fun i : Fin m => ⟨fun _ => none, fun _ => w i⟩

private theorem holds_keyRecords (w : Fin m → W) (extra : List (Rec W)) :
    HoldsKeys (keyRecords w ++ extra) Fin.val w := by
  intro i
  exact ⟨⟨fun _ => none, fun _ => w i⟩, read_append (by simp [keyRecords]) extra, rfl⟩

/-- A loaded comparison tree with a key per edge and materialized result lists. The layout
of the tree and of every output list depends only on the unweighted endpoints. -/
def smallMSFInput (ends : Fin m → Sym2 (Fin n)) (w : Fin m → W) : State (model W) layout :=
  let p := optimalMSFProgram ends
  let pre := outputs (keyRecords w) (leaves p)
  { pc := 0, ptr := fun r => if r = 0 then some pre.1.length else none, data := fun _ => default,
    heap := pre.1 ++ encode Fin.val pre.2 p pre.1.length }

/-- The interpreter returns a linked list of the original edge records of the MSF, and halts
within eight times the optimal comparison budget plus four instructions after loading. -/
theorem smallMSF_executes (ends : Fin m → Sym2 (Fin n)) (w : Fin m → W)
    (hw : Function.Injective w) :
    ∃ y t es, Executes (code W) (smallMSFInput ends w) y t ∧
      t ≤ 8 * optimalMSFComparisons ends + 4 ∧ EdgeList y.heap (y.ptr 0) es ∧
      es.toFinset = msf ends w Finset.univ := by
  let p := optimalMSFProgram ends
  let x := smallMSFInput ends w
  let pre := outputs (keyRecords w) (leaves p)
  let tree := encode (W := W) Fin.val pre.2 p pre.1.length
  obtain ⟨⟨extra, he⟩, all⟩ := outputs_spec (keyRecords w) (leaves p)
  have stored : Stored x.heap Fin.val pre.2 p pre.1.length := by
    simpa [x, smallMSFInput, p, pre] using stored_encode (W := W) Fin.val pre.2 p pre.1 []
  have keys : HoldsKeys x.heap Fin.val w := by
    change HoldsKeys (pre.1 ++ tree) _ _
    change pre.1 = keyRecords w ++ extra at he
    rw [he, List.append_assoc]
    exact holds_keyRecords w _
  obtain ⟨y, run, ans, same⟩ := stored.executes keys x rfl rfl (by simp [x, smallMSFInput, pre, p])
    (by simp [x, smallMSFInput])
  obtain ⟨correct, cost⟩ := optimalMSFProgram_spec ends w hw
  refine ⟨y, _, edgeLabels (p.eval (LEQuery.keyOracle w)), run,
    Nat.add_le_add_right (Nat.mul_le_mul_left 8 cost) 4, ?_, ?_⟩
  · rw [ans, same]
    exact (all _ (eval_mem_leaves p w)).append tree
  · exact (labels_eq _).trans correct

end Cslib.PointerMachine.ComparisonTree
