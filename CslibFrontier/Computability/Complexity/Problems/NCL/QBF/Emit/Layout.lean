/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.Emit.Basic

/-!
# Assembly of the source circuit from fixed instructions

Each occurrence of a fragment specifies its gate diagram, instruction offset and canonical
orientation. Stacking and juxtaposition assemble these together. A single decomposition of the
source circuit supports word emission, configuration emission and structural checks.

## Main definitions

* `QBF.Emit.Layout`: a diagram with its canonical orientation and emitted instructions.

## Main results

* `QBF.Emit.Layout.circuit`: layout of the complete source circuit.
-/

public section

namespace Cslib.Complexity.NCL.QBF.Emit

open Diagram

/-- A source diagram decomposed into oriented instructions at their wire offsets. -/
inductive Layout (recorded : Bool) : {a b : List Color} → (D : Diagram Gate a b) →
    (D.Edge → Bool) → ℕ → Program → Prop
  /-- Identity wires contribute no instructions. -/
  | id (a : List Color) (s) (k) : Layout recorded (Diagram.id a) s k []
  /-- A named fragment contributes one instruction and its prescribed orientation. -/
  | cell (op : Opcode) (k) :
      Layout recorded op.data.diagram (op.data.orient recorded) k [(k, op)]
  /-- The lower diagram follows the upper diagram at the same offset. -/
  | comp {a b c} {A : Diagram Gate a b} {B : Diagram Gate b c} {s k p q} :
      Layout recorded A (s ∘ compLeft A B) k p → Layout recorded B (s ∘ compRight A B) k q →
      Layout recorded (A.comp B) s k (p ++ q)
  /-- The right diagram follows the left diagram after its output wires. -/
  | tensor {a b c d} {A : Diagram Gate a b} {B : Diagram Gate c d} {s k p q} :
      Layout recorded A (s ∘ tensorLeft A B) k p →
      Layout recorded B (s ∘ tensorRight A B) (k + b.length) q →
      Layout recorded (A.tensor B) s k (p ++ q)

namespace Layout

variable {recorded : Bool} {a b c d : List Color} {k : ℕ} {p q : Program}

private theorem compReal {A : Diagram Gate a b} {B : Diagram Gate b c} {x y z : List Bool}
    {u : Realization Gate.interp A x y} {v : Realization Gate.interp B y z}
    (hu : Layout recorded A u.orient k p) (hv : Layout recorded B v.orient k q) :
    Layout recorded (A.comp B) (u.comp v).orient k (p ++ q) :=
  .comp (by simpa only [Realization.comp_orient_compLeft] using hu)
    (by simpa only [Realization.comp_orient_compRight] using hv)

private theorem tensorReal {A : Diagram Gate a b} {B : Diagram Gate c d} {x y z w : List Bool}
    {u : Realization Gate.interp A x y} {v : Realization Gate.interp B z w}
    (hu : Layout recorded A u.orient k p) (hv : Layout recorded B v.orient (k + b.length) q) :
    Layout recorded (A.tensor B) (u.tensor v).orient k (p ++ q) :=
  .tensor (by simpa only [Realization.tensor_orient_tensorLeft] using hu)
    (by simpa only [Realization.tensor_orient_tensorRight] using hv)

private theorem padRight {D : Diagram Gate a b} (r : List Color)
    (h : Layout recorded D (fun _ => false) k p) :
    Layout recorded (D.tensor (.id r)) (fun _ => false) k p := by
  simpa only [List.append_nil] using
    (Layout.tensor (s := fun _ => false) h (.id r _ _))

private theorem padLeft (l : List Color) {D : Diagram Gate a b}
    (h : Layout recorded D (fun _ => false) (k + l.length) p) :
    Layout recorded ((Diagram.id l).tensor D) (fun _ => false) k p :=
  Layout.tensor (s := fun _ => false) (.id l _ k) h

private theorem row (r : List Color) (n : ℕ) (m : List Bool) (k : ℕ) :
    Layout recorded (Network.row r n m) (fun _ => false) k (scan k n m true) := by
  induction n generalizing m k with
  | zero => exact .id _ _ _
  | succ n ih =>
    rw [scan_succ]
    have h : Layout recorded (Network.step (m.headD false)) (fun _ => false) k
        (collect k true (m.headD false)) := by
      cases m.headD false
      · exact .cell .swapBlueRed _
      · exact .cell .tap _
    exact .comp (p := collect k true (m.headD false)) (padRight _ h)
      (padLeft [.red] (ih m.tail (k + 1)))

private theorem clause (r : List Color) (n : ℕ) (m : List Bool) (k : ℕ) :
    Layout recorded (Network.clause r n m) (fun _ => false) k (scan k n m false) := by
  induction n generalizing m k with
  | zero => exact padRight r (.cell .fixed k)
  | succ n ih =>
    rw [scan_succ, Network.clause]
    cases h : m.headD false
    · exact padLeft [.red] (ih m.tail (k + 1))
    · exact .comp (p := [(k, .tapFirst)]) (padRight _ (.cell .tapFirst k))
        (padLeft [.red] (row r n m.tail (k + 1)))

private theorem conjoin (r : List Color) (n k : ℕ) (ms : List (List Bool)) :
    Layout recorded (Network.conjoin r n ms) (fun _ => false) k (Emit.conjoin k n ms) := by
  induction ms with
  | nil => exact .id _ _ _
  | cons m ms ih =>
    have hj := padLeft (k := k) (Network.bundle n) (padRight r
      (Layout.cell (recorded := recorded) .conj (k + (Network.bundle n).length)))
    simp only [Network.bundle, List.length_replicate] at hj
    exact .comp (.comp (clause (.blue :: r) n m k) hj) ih

private theorem network (r : List Color) (n k : ℕ) (ms : List (List Bool)) :
    Layout recorded (Network.network r n ms) (fun _ => false) k (Emit.network k n ms) := by
  cases ms with
  | nil => simpa only [Network.bundle, List.length_replicate] using!
      (padLeft (k := k) (Network.bundle n) (padRight r (.cell .start _)))
  | cons m ms => exact .comp (clause r n m k) (conjoin r n k ms)

private theorem chain (r : List Color) (qs : List Quantifier) (k : ℕ) :
    Layout recorded (Chain.diagram r qs) (Initial.chain r qs).orient k (Emit.chain k qs) := by
  induction qs generalizing r with
  | nil => exact .id _ _ _
  | cons q qs ih =>
    have h : Layout recorded q.gadget (Initial.quantifier q).orient k
        [(k, match q with | .ex => .ex | .all => .all)] := by
      cases q
      · exact .cell .ex _
      · exact .cell .all _
    exact compReal (tensorReal h (.id _ _ _)) (ih ([.red, .red] ++ r))

private theorem caps (r : List Color) (n k : ℕ) :
    Layout recorded (Matrix.caps r n) (fun _ => false) k (List.replicate n (k, .cap)) := by
  induction n with
  | zero => exact .id _ _ _
  | succ n ih =>
    rw [List.replicate_succ]
    exact .tensor (p := [(k, .cap)]) (.cell .cap k) ih

private theorem moveLeft (r : List Color) (n k : ℕ) :
    Layout recorded (Diagram.moveLeft (Network.bundle n) .blue r) (fun _ => false) k
      ((List.range n).reverse.map fun i => (k + i, .swapRedBlue)) := by
  induction n generalizing k with
  | zero => exact .id _ _ _
  | succ n ih =>
    simpa only [List.range_succ_eq_map, List.reverse_cons, ← List.map_reverse, List.map_append,
      List.map_map, List.map_singleton, Function.comp_def, Nat.add_zero, Nat.add_right_comm,
      Nat.add_succ, Nat.succ_add] using!
      (Layout.comp (s := fun _ => false) (.tensor (.id [.red] _ k) (ih (k + 1)))
        (padRight (Network.bundle n ++ r) (.cell .swapRedBlue k)))

/-- Assemble the matrix, the return gate and the literal caps. -/
theorem terminalBase (k p : ℕ) (ms : List (List Bool)) :
    Layout recorded (Matrix.terminalBase p ms) (Initial.terminalBase p ms).orient k
      (Emit.terminal k p ms) := by
  let ctrl := Realization.id (I := Gate.interp) [.blue, .blue] [true, false] rfl
  let net := Realization.zeros (I := Gate.interp) _ (Network.legal_network_zero [] (2 * p) ms)
  let move := Realization.zeros (I := Gate.interp) _
    (Initial.legal_moveLeft_zero (Network.bundle (2 * p)) .blue [])
  let cap := Realization.zeros (I := Gate.interp) _ (Initial.legal_caps_zero [] p)
  have h := compReal (compReal
    (tensorReal (u := ctrl) (v := net) (.id _ _ k) (network [] (2 * p) (k + 2) ms))
    (tensorReal (u := ctrl) (v := move) (.id _ _ k) (moveLeft [] (2 * p) (k + 2))))
    (tensorReal (u := Initial.returnInitial) (v := cap) (.cell .returnGate k)
      (caps (recorded := recorded) [] p k))
  simpa only [Emit.terminal, List.nil_append, List.append_assoc] using! h

private theorem terminal (p : ℕ) (qs : List Quantifier) (ms : List (List Bool)) :
    Layout recorded (Matrix.terminal p qs ms) (Initial.terminal p qs ms).orient 0
      (Emit.terminal 0 (p + qs.length) ms) := by
  induction qs generalizing p with
  | nil => exact terminalBase 0 p ms
  | cons q qs ih => simpa only [List.length_cons, Nat.add_succ, Nat.succ_add] using! ih (p + 1)

/-- Assemble the quantifier chain and terminal with their inactive directions. -/
theorem body (qs : List Quantifier) (ms : List (List Bool)) :
    Layout recorded (Matrix.body qs ms) (Initial.body qs ms).orient 0
      (Emit.chain 0 qs ++ Emit.terminal 0 qs.length ms) :=
  compReal (chain [] qs 0) (by simpa only [Nat.zero_add] using terminal 0 qs ms)

/-- Assemble the output latch and the body in either canonical record state. -/
theorem circuit (recorded : Bool) (qs : List Quantifier) (ms : List (List Bool)) :
    Layout recorded (OutputLatch.diagram.comp (Matrix.body qs ms))
      ((OutputLatch.canonical recorded true false).comp (Initial.body qs ms)).orient 0
      (Emit.circuit qs ms) := by
  unfold Emit.circuit
  rw [List.append_assoc]
  exact compReal (.cell .output 0) (body qs ms)

end Layout
end Cslib.Complexity.NCL.QBF.Emit
