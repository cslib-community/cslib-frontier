/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.BitMap
public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.Emit.Interpretation
public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.Initial

/-!
# Emitting canonical configurations through an interpretation

The fixed fragment table includes the canonical configurations of quantifiers and controls.
All matrix wires start inactive. Compositional bit maps concatenate these local bit lists in
the same order as the colored instruction emitter.

## Main definitions

* `Cslib.Complexity.NCL.QBF.Emit.Interpretation.opcodeBits`: a fragment's canonical bits.
* `Cslib.Complexity.NCL.QBF.Emit.Interpretation.configurationBits`: concatenated instruction bits.

## Main results

* `Cslib.Complexity.NCL.QBF.Emit.Interpretation.configurationBits_circuit`: canonical circuit bits.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.QBF.Emit.Interpretation

open Diagram

/-- Canonical created-edge directions of a fixed fragment, including both swap color orders. -/
@[expose] def opcodeBits (B : BitMap Gate) (recorded : Bool) : Option Opcode → List Bool
  | some .output => B.bits OutputLatch.diagram (OutputLatch.canonical recorded true false).orient
  | some .ex => B.bits existsGadget Initial.existsInitial.orient
  | some .all => B.bits forallGadget Initial.forallInitial.orient
  | some .tapFirst => B.bits Network.tapFirst (fun _ => false)
  | some .tap => B.bits Network.tap (fun _ => false)
  | some .conj => B.bits Network.conj (fun _ => false)
  | some .returnGate => B.bits Matrix.returnGate Initial.returnInitial.orient
  | some .cap => B.bits (.gen Gate.cap) (fun _ => false)
  | some .start => B.bits (.gen Gate.start) (fun _ => false)
  | some .fixed => B.bits (Gate.node [] [.blue]) (fun _ => false)
  | some .swap => B.bits (Diagram.swap .blue .red) (fun _ => false)
  | none => B.bits (Diagram.swap .red .blue) (fun _ => false)

/-- Concatenate canonical fragment bits in edge-creation order. -/
@[expose] def configurationBits (B : BitMap Gate) (recorded : Bool) (p : Program) : List Bool :=
  p.flatMap fun i => opcodeBits B recorded i.2

private def sourceBits (B : BitMap Gate) (recorded : Bool) (p : Emit.Program) : List Bool :=
  configurationBits B recorded (lift p)

variable (B : BitMap Gate)

private theorem sourceBits_append (recorded : Bool) (p q : Emit.Program) :
    sourceBits B recorded (p ++ q) = sourceBits B recorded p ++ sourceBits B recorded q := by
  simp only [sourceBits, configurationBits, lift, List.map_append, List.flatMap_append]

private theorem sourceBits_singleton (recorded : Bool) (k : ℕ) (op : Opcode) :
    sourceBits B recorded [(k, op)] = opcodeBits B recorded (some op) := by
  simp only [sourceBits, configurationBits, lift, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]

private theorem zeroBits_sweep {a : List Color} (D : Diagram Gate a [.red, .blue])
    (r : List Color) (n : ℕ) (m : List Bool) :
    B.bits
      ((D.tensor (.id (Network.bundle n ++ r))).comp
        ((Diagram.id [Color.red]).tensor (Network.row r n m))) (fun _ => false) =
      B.bits D (fun _ => false) ++
        B.bits (Network.row r n m) (fun _ => false) := by
  calc
    _ = _ := B.bits_comp_zero _ _
    _ = (B.bits D (fun _ => false) ++ B.bits (Diagram.id (Network.bundle n ++ r))
        (fun _ => false)) ++ (B.bits (Diagram.id [Color.red]) (fun _ => false) ++
          B.bits (Network.row r n m) (fun _ => false)) :=
      congrArg₂ List.append (B.bits_tensor_zero D (.id (Network.bundle n ++ r)))
        (B.bits_tensor_zero (.id [Color.red]) (Network.row r n m))
    _ = _ := by rw [B.bits_id, B.bits_id]; simp

private theorem configurationBits_row (recorded : Bool) (r : List Color)
    (n : ℕ) (m : List Bool) (k : ℕ) :
    sourceBits B recorded (scan k n m true) =
      B.bits (Network.row r n m) (fun _ => false) := by
  induction n generalizing m k with
  | zero =>
    change sourceBits B recorded [] = B.bits (Diagram.id ([Color.blue] ++ r)) (fun _ => false)
    exact (B.bits_id _ _).symm
  | succ n ih =>
    rw [scan_succ, sourceBits_append B]
    simp only [collect, ite_true, Bool.true_or, sourceBits_singleton B]
    rw [ih]
    calc
      _ = B.bits (Network.step (m.headD false)) (fun _ => false) ++
          B.bits (Network.row r n m.tail) (fun _ => false) := by
        cases h : m.headD false <;> rfl
      _ = _ := (zeroBits_sweep B (Network.step (m.headD false)) r n m.tail).symm

private theorem configurationBits_clause (recorded : Bool) (r : List Color)
    (n : ℕ) (m : List Bool) (k : ℕ) :
    sourceBits B recorded (scan k n m false) =
      B.bits (Network.clause r n m) (fun _ => false) := by
  induction n generalizing m k with
  | zero =>
    simp only [scan, List.range_zero, List.flatMap_nil, List.take_zero, List.any_nil,
      Bool.false_or, Bool.false_eq_true, ite_false, List.nil_append, Nat.add_zero,
      sourceBits_singleton B]
    change _ = B.bits ((Gate.node [] [.blue]).tensor (.id r)) (fun _ => false)
    rw [B.bits_tensor_zero, B.bits_id, List.append_nil]
    rfl
  | succ n ih =>
    rw [scan_succ, sourceBits_append B]
    cases h : m.headD false
    · simp only [collect, Bool.false_eq_true, ite_false, Bool.false_or, sourceBits,
      configurationBits, lift, List.map_nil,
        List.flatMap_nil, List.nil_append]
      change sourceBits B recorded (scan (k + 1) n m.tail false) = _
      rw [ih]
      have heq : Network.clause r (n + 1) m =
          (Diagram.id [Color.red]).tensor (Network.clause r n m.tail) := by
        simp only [Network.clause, h, Bool.false_eq_true, ite_false]
      rw [heq]
      have ht := B.bits_tensor_zero (.id [Color.red]) (Network.clause r n m.tail)
      rw [B.bits_id, List.nil_append] at ht
      exact ht.symm
    · simp only [collect, Bool.false_eq_true, ite_false, ite_true, Bool.false_or]
      rw [configurationBits_row B recorded r, sourceBits_singleton B]
      have heq : Network.clause r (n + 1) m =
          (Network.tapFirst.tensor (.id (Network.bundle n ++ r))).comp
            ((Diagram.id [Color.red]).tensor (Network.row r n m.tail)) := by
        simp only [Network.clause, h, ite_true]
      rw [heq]
      exact (zeroBits_sweep B Network.tapFirst r n m.tail).symm

private theorem zeroBits_id_tensor (l : List Color) {a b : List Color} (D : Diagram Gate a b) :
    B.bits ((Diagram.id l).tensor D) (fun _ => false) =
      B.bits D (fun _ => false) := by
  calc
    _ = _ := B.bits_tensor_zero _ _
    _ = _ := by rw [B.bits_id, List.nil_append]

private theorem zeroBits_tensor_id {a b : List Color} (D : Diagram Gate a b) (r : List Color) :
    B.bits (D.tensor (.id r)) (fun _ => false) =
      B.bits D (fun _ => false) := by
  calc
    _ = _ := B.bits_tensor_zero _ _
    _ = _ := by rw [B.bits_id, List.append_nil]

private theorem configurationBits_conjoin (recorded : Bool) (r : List Color)
    (k n : ℕ) (ms : List (List Bool)) :
    sourceBits B recorded (conjoin k n ms) =
      B.bits (Network.conjoin r n ms) (fun _ => false) := by
  induction ms with
  | nil => exact (B.bits_id _ _).symm
  | cons m ms ih =>
    simp only [conjoin, List.flatMap_cons, sourceBits_append B]
    rw [configurationBits_clause B recorded ([Color.blue] ++ r), sourceBits_singleton B]
    change _ ++ _ ++ sourceBits B recorded (conjoin k n ms) = _
    rw [ih]
    symm
    calc
      _ = _ := B.bits_comp_zero _ _
      _ = _ := congrArg₂ List.append (B.bits_comp_zero _ _) rfl
      _ = _ := by
        rw [zeroBits_id_tensor B]
        exact congrArg (fun bits =>
          (B.bits (Network.clause ([Color.blue] ++ r) n m) (fun _ => false) ++ bits) ++
            B.bits (Network.conjoin r n ms) (fun _ => false))
          (zeroBits_tensor_id B Network.conj r)

private theorem zeroBits_network_nil (r : List Color) (n : ℕ) :
    B.bits (Network.network r n []) (fun _ => false) =
      B.bits (Diagram.gen Gate.start) (fun _ => false) := by
  have h₁ := zeroBits_id_tensor B (Network.bundle n) ((Diagram.gen Gate.start).tensor (.id r))
  have h₂ := zeroBits_tensor_id B (Diagram.gen Gate.start) r
  exact h₁.trans h₂

private theorem configurationBits_network_nil (recorded : Bool) (r : List Color) (k n : ℕ) :
    sourceBits B recorded (network k n []) =
      B.bits (Network.network r n []) (fun _ => false) := by
  change sourceBits B recorded [(k + n, Opcode.start)] = _
  rw [sourceBits_singleton B]
  exact (zeroBits_network_nil B r n).symm

private theorem configurationBits_network_cons (recorded : Bool) (r : List Color)
    (k n : ℕ) (m : List Bool) (ms : List (List Bool)) :
    sourceBits B recorded (network k n (m :: ms)) =
      B.bits (Network.network r n (m :: ms)) (fun _ => false) := by
  change sourceBits B recorded (scan k n m false ++ conjoin k n ms) =
    B.bits ((Network.clause r n m).comp (Network.conjoin r n ms)) (fun _ => false)
  rw [sourceBits_append B, configurationBits_clause B recorded r,
    configurationBits_conjoin B recorded r]
  exact (B.bits_comp_zero (Network.clause r n m) (Network.conjoin r n ms)).symm

private theorem configurationBits_network (recorded : Bool) (r : List Color)
    (k n : ℕ) (ms : List (List Bool)) :
    sourceBits B recorded (network k n ms) =
      B.bits (Network.network r n ms) (fun _ => false) := by
  cases ms with
  | nil => exact configurationBits_network_nil B recorded r k n
  | cons m ms => exact configurationBits_network_cons B recorded r k n m ms

private theorem configurationBits_chain (recorded : Bool) (r : List Color) (qs : List Quantifier) :
    sourceBits B recorded (chain 0 qs) =
      B.bits (Chain.diagram r qs) (Initial.chain r qs).orient := by
  induction qs generalizing r with
  | nil => exact (B.bits_id _ _).symm
  | cons q qs ih =>
    simp only [chain, List.map_cons, sourceBits, configurationBits, lift, List.map_cons,
      List.flatMap_cons]
    change _ ++ sourceBits B recorded (chain 0 qs) = _
    rw [ih ([Color.red, Color.red] ++ r)]
    let R : Diagram.Realization Gate.interp (q.gadget.tensor (.id r))
        (Initial.controls r) (Initial.controls ([Color.red, Color.red] ++ r)) :=
      (Initial.quantifier q).tensor (.id r (List.replicate r.length false) (by simp))
    change _ = B.bits
      ((q.gadget.tensor (.id r)).comp (Chain.diagram ([Color.red, Color.red] ++ r) qs))
      (R.comp (Initial.chain ([Color.red, Color.red] ++ r) qs)).orient
    rw [B.bits_comp_realization]
    dsimp only [R]
    rw [B.bits_tensor_realization, B.bits_id, List.append_nil]
    cases q <;> rfl


private theorem configurationBits_caps (recorded : Bool) (r : List Color) (k p : ℕ) :
    sourceBits B recorded (List.replicate p (k, Opcode.cap)) =
      B.bits (Matrix.caps r p) (fun _ => false) := by
  induction p with
  | zero => exact (B.bits_id _ _).symm
  | succ p ih =>
    simp only [List.replicate_succ, sourceBits, configurationBits, lift, List.map_cons,
      List.flatMap_cons]
    change _ ++ sourceBits B recorded (List.replicate p (k, Opcode.cap)) = _
    rw [ih]
    exact (B.bits_tensor_zero (.gen Gate.cap) (Matrix.caps r p)).symm


private theorem configurationBits_append (recorded : Bool) (p q : Program) :
    configurationBits B recorded (p ++ q) =
      configurationBits B recorded p ++ configurationBits B recorded q := List.flatMap_append

private theorem configurationBits_none (recorded : Bool) (k : ℕ) :
    configurationBits B recorded [(k, none)] =
      B.bits (Diagram.swap Color.red Color.blue) (fun _ => false) := by
  simp only [configurationBits, List.flatMap_cons, List.flatMap_nil, List.append_nil, opcodeBits]

private theorem configurationBits_moveLeft (recorded : Bool) (n : ℕ) (r : List Color) (k : ℕ) :
    configurationBits B recorded ((List.range n).reverse.map fun i => (k + i, none)) =
      B.bits (moveLeft (Network.bundle n) Color.blue r) (fun _ => false) := by
  induction n generalizing k with
  | zero => exact (B.bits_id _ _).symm
  | succ n ih =>
    simp only [List.range_succ_eq_map, List.reverse_cons, ← List.map_reverse,
      List.map_append, List.map_map, List.map_singleton, configurationBits_append B]
    dsimp only [Function.comp_def]
    have hk : (fun i : ℕ => (k + i.succ, (none : Option Opcode))) =
        (fun i => ((k + 1) + i, none)) := by
      funext i
      congr 1
      omega
    rw [hk, Nat.add_zero, ih, configurationBits_none B]
    change _ = B.bits (((Diagram.id [Color.red]).tensor
      (moveLeft (Network.bundle n) Color.blue r)).comp
        ((Diagram.swap Color.red Color.blue).tensor (.id (Network.bundle n ++ r))))
          (fun _ => false)
    calc
      _ = _ := (congrArg₂ List.append
        (zeroBits_id_tensor B [Color.red] (moveLeft (Network.bundle n) Color.blue r))
        (zeroBits_tensor_id B (Diagram.swap Color.red Color.blue) (Network.bundle n ++ r))).symm
      _ = _ := (B.bits_comp_zero _ _).symm

private theorem configurationBits_terminal (recorded : Bool) (k p : ℕ) (ms : List (List Bool)) :
    configurationBits B recorded (terminal k p ms) =
      B.bits (Matrix.terminalBase p ms) (Initial.terminalBase p ms).orient := by
  let Rnet := Realization.zeros (I := Gate.interp) (Network.network [] (2 * p) ms)
    (Network.legal_network_zero [] (2 * p) ms)
  let Rmove := Realization.zeros (I := Gate.interp)
    (moveLeft (Network.bundle (2 * p)) .blue [])
    (Initial.legal_moveLeft_zero (Network.bundle (2 * p)) .blue [])
  let Rctrl := Realization.id (I := Gate.interp) [.blue, .blue] [true, false] rfl
  let Rlast := Initial.returnInitial.tensor
    (Realization.zeros (I := Gate.interp) (Matrix.caps [] p) (Initial.legal_caps_zero [] p))
  change _ = B.bits
    ((((Diagram.id [.blue, .blue]).tensor (Network.network [] (2 * p) ms)).comp
      ((Diagram.id [.blue, .blue]).tensor (moveLeft (Network.bundle (2 * p)) .blue []))).comp
      (Matrix.returnGate.tensor (Matrix.caps [] p)))
    (((Rctrl.tensor Rnet).comp (Rctrl.tensor Rmove)).comp Rlast).orient
  rw [B.bits_comp_realization, B.bits_comp_realization]
  dsimp only [Rlast]
  rw [B.bits_tensor_realization, B.bits_tensor_realization, B.bits_tensor_realization, B.bits_id]
  dsimp only [Rnet, Rmove, Realization.zeros]
  unfold terminal
  simp only [configurationBits_append B]
  change sourceBits B recorded (network (k + 2) (2 * p) ms) ++ _ ++
    sourceBits B recorded [(k, .returnGate)] ++
      sourceBits B recorded (List.replicate p (k, .cap)) = _
  rw [configurationBits_network B recorded [],
    configurationBits_moveLeft B recorded (2 * p) [] (k + 2),
    sourceBits_singleton B, configurationBits_caps B recorded []]
  simp only [opcodeBits, List.nil_append, List.append_assoc]

private theorem extendedBits_terminal (p : ℕ) (qs : List Quantifier) (ms : List (List Bool)) :
    B.bits (Matrix.terminal p qs ms) (Initial.terminal p qs ms).orient =
      B.bits (Matrix.terminalBase (p + qs.length) ms)
        (Initial.terminalBase (p + qs.length) ms).orient := by
  induction qs generalizing p with
  | nil => rfl
  | cons q qs ih =>
    change B.bits (Matrix.terminal (p + 1) qs ms)
      (Initial.terminal (p + 1) qs ms).orient = _
    have hp : p + (q :: qs).length = (p + 1) + qs.length := by
      simp only [List.length_cons]
      omega
    rw [hp]
    exact ih (p + 1)

/-- The emitted body bits equal the canonical configuration under the bit map. -/
theorem configurationBits_body (recorded : Bool) (qs : List Quantifier) (ms : List (List Bool)) :
    configurationBits B recorded (lift (chain 0 qs) ++ terminal 0 qs.length ms) =
      B.bits (Matrix.body qs ms) (Initial.body qs ms).orient := by
  rw [configurationBits_append B]
  change sourceBits B recorded (chain 0 qs) ++ _ = _
  rw [configurationBits_chain B recorded [], configurationBits_terminal B]
  have hb := B.bits_comp_realization (Initial.chain [] qs) (Initial.terminal 0 qs ms)
  rw [extendedBits_terminal B, Nat.zero_add] at hb
  exact hb.symm

/-- The emitted bits equal the canonical configuration of the interpreted complete circuit. -/
theorem configurationBits_circuit (recorded : Bool) (qs : List Quantifier)
    (ms : List (List Bool)) :
    configurationBits B recorded (circuit qs ms) =
      B.bits (OutputLatch.diagram.comp (Matrix.body qs ms))
        ((OutputLatch.canonical recorded true false).comp (Initial.body qs ms)).orient := by
  unfold circuit
  rw [List.append_assoc, configurationBits_append B, configurationBits_body B]
  change sourceBits B recorded [(0, .output)] ++ _ = _
  rw [sourceBits_singleton B]
  exact (B.bits_comp_realization (OutputLatch.canonical recorded true false)
    (Initial.body qs ms)).symm

end Cslib.Complexity.NCL.QBF.Emit.Interpretation
