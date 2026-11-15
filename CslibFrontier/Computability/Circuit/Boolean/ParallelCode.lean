/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.CodeComposition
public import CslibFrontier.Computability.Circuit.Replication

/-!
# Native code for circuit families on disjoint inputs

`parallelFamilyCode n m codes` runs an arbitrary list of `n`-input, `m`-output circuit codes on
consecutive disjoint input blocks and concatenates their output blocks.  The fold mirrors
`Circuit.parallelFamily`: it retains each member's internal sharing and never compiles a truth
table.

## Main definitions

* `Cslib.Circuits.Boolean.parallelFamilyCode`: raw code for a list of disjoint-input circuits.

## Main results

* `Cslib.Circuits.Boolean.parallelFamilyCode_code`: exact agreement with
  `Circuit.parallelFamily` for every finite family.

These code-composition results are original infrastructure.
-/

public section

namespace Cslib.Circuits.Boolean

local notation "Code" => List (Op × List ℕ) × List ℕ

/-- Run two raw circuit codes on consecutive disjoint input blocks.  This binary constructor is
kept private as the implementation step of the list-level family compiler. -/
private def parallelCode (leftInputs rightInputs : ℕ) (left right : Code) : Code :=
  appendCode (leftInputs + rightInputs)
    (compCode (leftInputs + rightInputs) left ([], List.range leftInputs))
    (compCode (leftInputs + rightInputs) right
      ([], (List.range rightInputs).map (leftInputs + ·)))

private theorem parallelCode_code {n m p q : ℕ}
    (left : Circuit signature n m) (right : Circuit signature p q) :
    parallelCode n p left.code right.code = (left.parallel right).code := by
  rw [parallelCode, Circuit.parallel]
  rw [show ([], List.range n) = (Circuit.wiring signature (Fin.castAdd p)).code by
    symm
    simpa using Circuit.code_wiring_eq_map
      (σ := signature) (f := Fin.castAdd p) (g := id) (fun _ => rfl)]
  rw [show ([], (List.range p).map (n + ·)) =
      (Circuit.wiring signature (Fin.natAdd n)).code by
    symm
    simpa using Circuit.code_wiring_eq_map
      (σ := signature) (f := Fin.natAdd n) (g := (n + ·)) (fun _ => rfl)]
  rw [compCode_code, compCode_code, appendCode_code]

/-- Run a list of raw `n`-input, `m`-output circuit codes on consecutive disjoint input blocks,
preserving the list order in the output blocks. -/
@[expose] def parallelFamilyCode (n m : ℕ) (codes : List Code) : Code :=
  (codes.foldl (fun state code =>
    let k := state.1
    let inputCount := (k + 1) * n
    let outputCount := (k + 1) * m
    let combined := appendCode (k * n + n)
      (compCode (k * n + n) state.2 ([], List.range (k * n)))
      (compCode (k * n + n) code ([], (List.range n).map (k * n + ·)))
    (k + 1,
      compCode inputCount ([], List.range outputCount)
        (compCode inputCount combined ([], List.range inputCount)))) (0, ([], []))).2

private theorem fold_parallelFamilyCodeStep_code {k n m : ℕ}
    (cs : Fin k → Circuit signature n m) :
    (List.ofFn fun j => (cs j).code).foldl (fun state code =>
      let k := state.1
      let inputCount := (k + 1) * n
      let outputCount := (k + 1) * m
      let combined := appendCode (k * n + n)
        (compCode (k * n + n) state.2 ([], List.range (k * n)))
        (compCode (k * n + n) code ([], (List.range n).map (k * n + ·)))
      (k + 1,
        compCode inputCount ([], List.range outputCount)
          (compCode inputCount combined ([], List.range inputCount)))) (0, ([], [])) =
      (k, (Circuit.parallelFamily cs).code) := by
  induction k with
  | zero => simp [Circuit.parallelFamily, Circuit.code_wiring]
  | succ k ih =>
    rw [List.ofFn_succ_last, List.foldl_append, ih (fun j => cs j.castSucc)]
    simp only [List.foldl_cons, List.foldl_nil]
    have hout : (Circuit.wiring signature (Fin.cast (Nat.succ_mul k m))).code =
        ([], List.range ((k + 1) * m)) := by
      simpa [Nat.succ_eq_add_one, Nat.succ_mul] using Circuit.code_wiring_eq_map
        (σ := signature) (f := Fin.cast (Nat.succ_mul k m)) (g := id) fun _ => rfl
    have hin : (Circuit.wiring signature (Fin.cast (Nat.succ_mul k n).symm)).code =
        ([], List.range ((k + 1) * n)) := by
      simpa [Nat.succ_eq_add_one, Nat.succ_mul] using Circuit.code_wiring_eq_map
        (σ := signature) (f := Fin.cast (Nat.succ_mul k n).symm) (g := id) fun _ => rfl
    have hparallel :
        appendCode (k * n + n)
          (compCode (k * n + n) (Circuit.parallelFamily fun j => cs j.castSucc).code
            ([], List.range (k * n)))
          (compCode (k * n + n) (cs (Fin.last k)).code
            ([], (List.range n).map (k * n + ·))) =
          ((Circuit.parallelFamily fun j => cs j.castSucc).parallel
            (cs (Fin.last k))).code := by
      simpa only [parallelCode] using parallelCode_code
        (Circuit.parallelFamily fun j => cs j.castSucc) (cs (Fin.last k))
    rw [← hout, ← hin, hparallel, compCode_code, compCode_code]
    rfl

/-- Compiling the codes of a typed finite family gives exactly the code of its disjoint-input
parallel composition, including the empty family. -/
theorem parallelFamilyCode_code {k n m : ℕ} (cs : Fin k → Circuit signature n m) :
    parallelFamilyCode n m (List.ofFn fun j => (cs j).code) =
      (Circuit.parallelFamily cs).code := by
  unfold parallelFamilyCode
  rw [fold_parallelFamilyCodeStep_code]

end Cslib.Circuits.Boolean
