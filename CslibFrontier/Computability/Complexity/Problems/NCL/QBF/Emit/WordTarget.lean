/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.Emit.Basic

/-!
# Source emission into arbitrary word alphabets

A word interpretation preserves identity, stacking and juxtaposition, including wire offsets.
The source instruction correctness theorem is shared by primitive and marked word emission.

## Main definitions

* `Cslib.Complexity.NCL.QBF.Emit.Interpretation.WordTarget`: an interpretation into list words.

## Main results

* `Cslib.Complexity.NCL.QBF.Emit.Interpretation.WordTarget.expand_circuit`: exact source emission.
-/

public section

namespace Cslib.Complexity.NCL.QBF.Emit.Interpretation

open Diagram

/-- A word-valued interpretation preserving the three diagram operations and their offsets. -/
structure WordTarget (α : Type) where
  /-- Emit a source diagram at a wire offset. -/
  map : {a b : List Color} → Diagram Gate a b → ℕ → List α
  /-- Identity wires emit no layers. -/
  map_id (a : List Color) (k : ℕ) : map (Diagram.id a) k = []
  /-- Sequential parts emit consecutive words. -/
  map_comp {a b c : List Color} (D₁ : Diagram Gate a b) (D₂ : Diagram Gate b c) (k : ℕ) :
    map (D₁.comp D₂) k = map D₁ k ++ map D₂ k
  /-- The right parallel part starts after the left part's output wires. -/
  map_tensor {a b c d : List Color} (D₁ : Diagram Gate a b) (D₂ : Diagram Gate c d) (k : ℕ) :
    map (D₁.tensor D₂) k = map D₁ k ++ map D₂ (k + b.length)

variable {α : Type}

/-- Emit one of the fixed source fragments. -/
@[expose] def WordTarget.opcodeWord (T : WordTarget α) (op : Opcode) (k : ℕ) : List α :=
  let ⟨_, _, diagram⟩ := op.gateFragment
  T.map diagram k

/-- Interpret a source program in the chosen word alphabet. -/
@[expose] def WordTarget.expand (T : WordTarget α) (p : Program) : List α :=
  p.flatMap fun i => T.opcodeWord i.2 i.1

namespace WordTarget

private theorem expand_append (T : WordTarget α) (p q : QBF.Emit.Program) :
    T.expand (p ++ q) = T.expand p ++ T.expand q := by
  exact List.flatMap_append

private theorem expand_singleton (T : WordTarget α) (k : ℕ) (op : Opcode) :
    T.expand [(k, op)] = (T.map op.gateFragment.2.2) k := by
  simp only [WordTarget.expand,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rfl

variable (T : WordTarget α)

private theorem expand_scan_row (r : List Color) (n : ℕ) (m : List Bool) (k : ℕ) :
    T.expand (scan k n m true) = (T.map (Network.row r n m)) k := by
  induction n generalizing m k with
  | zero =>
    change T.expand [] = (T.map (Diagram.id ([Color.blue] ++ r))) k
    rw [T.map_id]
    rfl
  | succ n ih =>
    rw [scan_succ, T.expand_append]
    simp only [collect, ite_true, Bool.true_or, T.expand_singleton]
    rw [ih]
    simp only [Network.row, T.map_comp, T.map_tensor, T.map_id,
      List.append_nil, List.nil_append, List.length_singleton]
    cases h : m.headD false <;>
      simp only [Network.step, Bool.false_eq_true, ite_false, ite_true, Opcode.gateFragment] <;> rfl

private theorem expand_scan_clause (r : List Color) (n : ℕ) (m : List Bool) (k : ℕ) :
    T.expand (scan k n m false) =
      (T.map (Network.clause r n m)) k := by
  induction n generalizing m k with
  | zero =>
    change T.expand [(k, .fixed)] =
      (T.map ((Gate.node [] [.blue]).tensor (Diagram.id r))) k
    rw [T.expand_singleton, T.map_tensor, T.map_id]
    simp only [List.append_nil]
    rfl
  | succ n ih =>
    rw [scan_succ, T.expand_append]
    cases h : m.headD false
    · simp only [collect, Bool.false_eq_true, ite_false, Bool.false_or, WordTarget.expand,
        List.flatMap_nil, List.nil_append]
      change T.expand (scan (k + 1) n m.tail false) = _
      rw [ih]
      simp only [Network.clause, h, Bool.false_eq_true, ite_false, T.map_tensor, T.map_id,
        List.nil_append, List.length_singleton]
    · simp only [collect, Bool.false_eq_true, ite_false, ite_true, Bool.false_or]
      rw [expand_scan_row T r, T.expand_singleton]
      simp only [Opcode.gateFragment, Network.clause, h, ite_true, T.map_comp, T.map_tensor,
      T.map_id,
        List.append_nil, List.nil_append, List.length_singleton]


private theorem expand_conjoin (r : List Color) (k n : ℕ) (ms : List (List Bool)) :
    T.expand (conjoin k n ms) =
      (T.map (Network.conjoin r n ms)) k := by
  induction ms with
  | nil =>
    change T.expand [] =
      (T.map (Diagram.id (Network.bundle n ++ ([Color.blue] ++ r)))) k
    rw [T.map_id]
    rfl
  | cons m ms ih =>
    simp only [conjoin, List.flatMap_cons, T.expand_append]
    rw [expand_scan_clause T ([Color.blue] ++ r), T.expand_singleton]
    change _ ++ _ ++ T.expand (conjoin k n ms) = _
    rw [ih]
    simp only [Network.conjoin, T.map_comp, T.map_tensor, T.map_id, List.nil_append,
      List.append_nil,
      Network.bundle, List.length_replicate, Opcode.gateFragment]

private theorem expand_network (r : List Color) (k n : ℕ) (ms : List (List Bool)) :
    T.expand (network k n ms) =
      (T.map (Network.network r n ms)) k := by
  cases ms with
  | nil =>
    simp only [network, T.expand_singleton, Opcode.gateFragment, Network.network,
      T.map_tensor, T.map_id, List.nil_append, List.append_nil, Network.bundle,
      List.length_replicate]
  | cons m ms =>
    simp only [network, T.expand_append, expand_scan_clause T r, expand_conjoin T r,
      Network.network,
      T.map_comp]

private theorem expand_chain (r : List Color) (k : ℕ) (qs : List Quantifier) :
    T.expand (chain k qs) = (T.map (Chain.diagram r qs)) k := by
  induction qs generalizing r with
  | nil =>
    change T.expand [] =
      (T.map (Diagram.id ([Color.blue, Color.blue] ++ r))) k
    rw [T.map_id]
    rfl
  | cons q qs ih =>
    simp only [chain, List.map_cons, WordTarget.expand, List.flatMap_cons]
    change _ ++ T.expand (chain k qs) = _
    rw [ih ([Color.red, Color.red] ++ r)]
    cases q
    all_goals
      change T.opcodeWord _ k ++ _ =
        (T.map (Diagram.comp (Diagram.tensor (_ : Diagram Gate [Color.blue, Color.blue]
          [Color.blue, Color.blue, Color.red,
      Color.red]) (Diagram.id r)) (Chain.diagram ([Color.red, Color.red] ++ r) qs))) k
      rw [T.map_comp, T.map_tensor, T.map_id]
      simp only [List.append_nil]
      rfl

private theorem terminal_word (p : ℕ) (qs : List Quantifier) (ms : List (List Bool)) (k : ℕ) :
    (T.map (Matrix.terminal p qs ms)) k =
      (T.map (Matrix.terminalBase (p + qs.length) ms)) k := by
  induction qs generalizing p with
  | nil => rfl
  | cons q qs ih =>
    change (T.map (Matrix.terminal (p + 1) qs ms)) k = _
    have hp : p + (q :: qs).length = (p + 1) + qs.length := by
      simp only [List.length_cons]
      omega
    rw [hp]
    exact ih (p + 1)


private theorem expand_caps (r : List Color) (k p : ℕ) :
    T.expand (List.replicate p (k, Opcode.cap)) =
      (T.map (Matrix.caps r p)) k := by
  induction p with
  | zero =>
    change T.expand [] = (T.map (Diagram.id r)) k
    rw [T.map_id]
    rfl
  | succ p ih =>
    simp only [List.replicate_succ, WordTarget.expand, List.flatMap_cons]
    change _ ++ T.expand (List.replicate p (k, Opcode.cap)) = _
    rw [ih]
    change _ = (T.map ((gen Gate.cap).tensor (Matrix.caps r p))) k
    rw [T.map_tensor]
    rfl

private theorem expand_swapRedBlue (T : WordTarget α) (k : ℕ) :
    T.expand [(k, Opcode.swapRedBlue)] = (T.map (Diagram.swap .red .blue)) k := by
  rw [WordTarget.expand, List.flatMap_singleton]
  rfl

private theorem expand_moveLeft (n : ℕ) (r : List Color) (k : ℕ) :
    T.expand ((List.range n).reverse.map fun i => (k + i, Opcode.swapRedBlue)) =
      (T.map (moveLeft (Network.bundle n) Color.blue r)) k := by
  induction n generalizing k with
  | zero =>
    change T.expand [] = (T.map (Diagram.id ([Color.blue] ++ r))) k
    rw [T.map_id]
    rfl
  | succ n ih =>
    simp only [List.range_succ_eq_map, List.reverse_cons, ← List.map_reverse,
      List.map_append, List.map_map, List.map_singleton, T.expand_append]
    dsimp only [Function.comp_def]
    have hk : (fun i : ℕ => (k + i.succ, Opcode.swapRedBlue)) =
        (fun i => ((k + 1) + i, Opcode.swapRedBlue)) := by
      funext i
      congr 1
      omega
    rw [hk, Nat.add_zero, ih, T.expand_swapRedBlue]
    change _ = (T.map (((Diagram.id [Color.red]).tensor
      (moveLeft (Network.bundle n) Color.blue r)).comp
        ((Diagram.swap Color.red Color.blue).tensor (Diagram.id (Network.bundle n ++ r))))) k
    rw [T.map_comp, T.map_tensor, T.map_tensor]
    simp only [T.map_id]
    simp only [List.nil_append, List.length_singleton]
    have hid := T.map_id (Network.bundle n ++ r) (k + [Color.blue, Color.red].length)
    simpa only [List.append_nil, Nat.add_zero] using
      congrArg (fun w =>
        (T.map (moveLeft (Network.bundle n) Color.blue r)) (k + 1) ++
          ((T.map (Diagram.swap Color.red Color.blue)) k ++ w)) hid.symm

/-- Interpretation commutes with terminal emission. -/
theorem expand_terminal (k p : ℕ) (ms : List (List Bool)) :
    T.expand (terminal k p ms) =
      (T.map (Matrix.terminalBase p ms)) k := by
  have hm := expand_moveLeft T (2 * p) [] (k + 2)
  simp only [terminal, T.expand_append]
  change T.expand (network (k + 2) (2 * p) ms) ++ _ ++
    T.expand [(k, .returnGate)] ++ T.expand (List.replicate p (k, .cap)) = _
  rw [expand_network T [], hm, T.expand_singleton, expand_caps T []]
  change _ = (T.map (((Diagram.id [Color.blue, Color.blue]).tensor
    (Network.network [] (2 * p) ms)).comp
      ((Diagram.id [Color.blue, Color.blue]).tensor
        (moveLeft (Network.bundle (2 * p)) Color.blue [])) |>.comp
          (Matrix.returnGate.tensor (Matrix.caps [] p)))) k
  rw [T.map_comp, T.map_comp, T.map_tensor, T.map_tensor, T.map_tensor]
  simp only [T.map_id]
  simp only [List.nil_append, List.length_cons, List.length_nil, Nat.zero_add,
    Nat.add_zero, Opcode.gateFragment, List.append_assoc]

/-- Interpretation commutes with complete circuit emission. -/
theorem expand_circuit (qs : List Quantifier) (ms : List (List Bool)) :
    T.expand (circuit qs ms) =
      (T.map (OutputLatch.diagram.comp (Matrix.body qs ms))) 0 := by
  simp only [circuit, T.expand_append]
  rw [T.expand_singleton, expand_chain T [], expand_terminal T]
  change _ = (T.map (OutputLatch.diagram.comp
    ((Chain.diagram [] qs).comp (Matrix.terminal 0 qs ms)))) 0
  rw [T.map_comp, T.map_comp]
  simp only [List.append_assoc]
  have ht := terminal_word T 0 qs ms 0
  have he : (T.map (Matrix.terminalBase (0 + qs.length) ms)) 0 =
      (T.map (Matrix.terminalBase qs.length ms)) 0 :=
    congrArg (fun p => (T.map (Matrix.terminalBase p ms)) 0)
      (Nat.zero_add qs.length)
  have hf := ht.trans he
  exact congrArg (fun w => (T.map OutputLatch.diagram) 0 ++
    ((T.map (Chain.diagram [] qs)) 0 ++ w)) hf.symm

end WordTarget

end Cslib.Complexity.NCL.QBF.Emit.Interpretation
