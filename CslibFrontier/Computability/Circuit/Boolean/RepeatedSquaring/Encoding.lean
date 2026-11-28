/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Boolean.RepeatedSquaring
public import CslibFrontier.Computability.Circuit.Encoding.Combinators

/-!
# Gate addresses for Boolean matrix squaring

The circuit for one square puts the gates for an output entry consecutively. Its first `N`
gates test two-step walks through the possible intermediate vertices, and its last gate takes
their disjunction. The address formulas identify the wires that a serialized circuit generator
must emit.

## Main results

* `code_squareCircuit_comp` gives the native gate and output code of a squaring after an
  arbitrary input circuit.
* `code_iterate_squareCircuit` gives the gate list and all output addresses after any number
  of squarings.

## References

The matrix-powering construction is [Arora and Barak, Chapter 6, Exercise 9(b–c),
2007 draft][AroraBarak07]. The address formulas describe this library’s serialization.
-/

public section

namespace Cslib.Circuits

private theorem code_pi_blocks {σ : Signature} {n k : ℕ} (cs : Fin k → Circuit σ n 1)
    (s : ℕ) (hs : ∀ i, (cs i).size = s) :
    (Circuit.pi cs).code =
      ((List.ofFn fun i => (Circuit.shiftCode n (i.val * s) (cs i).code).1).flatten,
       (List.ofFn fun i => (Circuit.shiftCode n (i.val * s) (cs i).code).2).flatten) := by
  rw [Circuit.code_pi_bundle cs s hs]
  have hzip : (List.ofFn fun j => (cs j).code).zipIdx =
      List.ofFn fun j => ((cs j).code, j.val) :=
    List.ext_getElem (by simp) fun _ _ _ => by simp
  simp only [Circuit.bundleCode, hzip, List.flatMap, List.map_ofFn, Function.comp_def]

namespace Boolean

private def andLine (N i j k : ℕ) : Unbounded.Op × List ℕ :=
  (.and 2, [k + N * i, j + N * k])

private def orLine (N offset : ℕ) : Unbounded.Op × List ℕ :=
  (.or N, List.ofFn fun k : Fin N => offset + k.val)

private theorem code_entry {N : ℕ} (i j : Fin N) :
    ((Circuit.oneGate (σ := Unbounded.signature) (Unbounded.Op.or N) (id : Fin N → Fin N)).comp
      (Circuit.pi fun k =>
        Circuit.oneGate (Unbounded.Op.and 2)
          ![finProdFinEquiv (i, k), finProdFinEquiv (k, j)])).code =
      ((List.ofFn fun k : Fin N => andLine N i j k) ++ [orLine N (N * N)], [N * N + N]) := by
  rw [Circuit.code_comp, Circuit.code_oneGate, Circuit.code_pi_oneGate]
  simp [Circuit.compCode, Circuit.compCodeWire, andLine, orLine,
    List.ofFn_succ, finProdFinEquiv, Function.comp_def, List.getD_eq_getElem?_getD]

/-- The serialized gate list and output indices of one squaring. Each output row-column pair
has an equally sized block of conjunctions and one disjunction. -/
private theorem code_squareCircuit_aux (N : ℕ) :
    (squareCircuit N).code =
      ((List.ofFn fun o : Fin (N * N) =>
        (List.ofFn fun k : Fin N => andLine N (o.val / N) (o.val % N) k) ++
          [orLine N (N * N + o.val * (N + 1))]).flatten,
       List.ofFn fun o : Fin (N * N) => N * N + o.val * (N + 1) + N) := by
  unfold squareCircuit
  rw [code_pi_blocks _ (N + 1) (fun _ => by simp)]
  simp only [code_entry, Circuit.shiftCode, List.map_append, List.map_cons, List.map_nil,
    List.map_ofFn, Function.comp_def, andLine, orLine]
  have he (i j : Fin N) : j.val + N * i.val < N * N := (finProdFinEquiv (i, j)).isLt
  have hs {a b : ℕ} : Circuit.shiftCodeWire (N * N) a (N * N + b) = N * N + a + b := by
    simp [Circuit.shiftCodeWire, Nat.add_right_comm]
  have hsingle {α : Type} {k : ℕ} (f : Fin k → α) :
      (List.ofFn fun i => [f i]).flatten = List.ofFn f := by
    simpa only [List.flatMap, List.map_ofFn, Function.comp_def] using
      List.flatMap_singleton' (List.ofFn f)
  simp only [hs]
  simp only [Circuit.shiftCodeWire, he, ↓reduceIte, hsingle]
  rfl

/-- Gate list of one Boolean square. The numerical address `offset` is the first fresh wire
and `input` names the wires carrying the entries of the input matrix. Blocks are in row-major
order and intermediate vertices within a block occur in numerical order. -/
@[expose] def squareGateList (N offset : ℕ) (input : Fin (N * N) → ℕ) :
    List (Unbounded.Op × List ℕ) :=
  (List.ofFn fun o : Fin (N * N) =>
    let (i, j) := finProdFinEquiv.symm o
    (List.ofFn fun k : Fin N => (Unbounded.Op.and 2,
      [input (finProdFinEquiv (i, k)), input (finProdFinEquiv (k, j))])) ++
      [(Unbounded.Op.or N, List.ofFn fun k : Fin N => offset + o.val * (N + 1) + k.val)]).flatten

/-- Appending a matrix squaring uses the current output wire addresses as its inputs.
Its output wires are the disjunctions at the ends of the successive blocks. -/
theorem code_squareCircuit_comp {n N : ℕ} (c : Circuit Unbounded.signature n (N * N)) :
    ((squareCircuit N).comp c).code =
      (c.code.1 ++ squareGateList N (n + c.size) (fun i => (c.outputs i).toNat),
        List.ofFn fun o : Fin (N * N) => n + c.size + o.val * (N + 1) + N) := by
  have hinput (i j : Fin N) :
      Circuit.compCodeWire n c.code (j.val + N * i.val) =
        (c.outputs (finProdFinEquiv (i, j))).toNat := by
    have hlt : j.val + N * i.val < N * N := (finProdFinEquiv (i, j)).isLt
    change Circuit.compCodeWire n c.code (finProdFinEquiv (i, j)).val = _
    simp [Circuit.compCodeWire, Circuit.code, List.getD_eq_getElem?_getD, hlt, finProdFinEquiv]
  have hgate (j l : ℕ) :
      Circuit.compCodeWire n c.code (N * N + j * (N + 1) + l) =
        n + c.size + j * (N + 1) + l := by
    have hlen : c.code.2.length = N * N := List.length_ofFn
    have hsize : c.code.1.length = c.size := Circuit.length_code_fst c
    simp [Circuit.compCodeWire, hlen, hsize, Nat.add_assoc]
  rw [Circuit.code_comp, code_squareCircuit_aux]
  simp only [Circuit.compCode, orLine, andLine, squareGateList, List.map_flatten,
    List.map_append, List.map_cons, List.map_nil, List.map_ofFn, Function.comp_def, hgate]
  have h (o : Fin (N * N)) (k : Fin N) :
      Circuit.compCodeWire n c.code (k.val + N * (o.val / N)) =
        (c.outputs (finProdFinEquiv ((finProdFinEquiv.symm o).1, k))).toNat :=
    hinput (finProdFinEquiv.symm o).1 k
  have h' (o : Fin (N * N)) (k : Fin N) :
      Circuit.compCodeWire n c.code (o.val % N + N * k.val) =
        (c.outputs (finProdFinEquiv (k, (finProdFinEquiv.symm o).2))).toNat :=
    hinput k (finProdFinEquiv.symm o).2
  simp only [h, h']

/-- Address of a matrix entry after `t` squarings, with `N * N` input wires. At zero the entry
is still an input. At positive `t` its wire is the final disjunction of its last block. -/
@[expose] def squareOutputWire (N t i : ℕ) : ℕ :=
  if t = 0 then i else N * N + (t - 1) * (N ^ 2 * (N + 1)) + i * (N + 1) + N

/-- All gates and designated output wires in the native serialization of iterated squaring.
The gate list concatenates one block of `N²(N+1)` gates per round. -/
theorem code_iterate_squareCircuit (N t : ℕ) :
    ((squareCircuit N).iterate t).code =
      ((List.ofFn fun r : Fin t => squareGateList N (N * N + r.val * (N ^ 2 * (N + 1)))
        (fun i => squareOutputWire N r.val i.val)).flatten,
       List.ofFn fun i : Fin (N * N) => squareOutputWire N t i.val) := by
  induction t with
  | zero =>
    simp only [Circuit.iterate, Circuit.id, Circuit.code_wiring, List.ofFn_zero, List.flatten_nil]
    rfl
  | succ t ih =>
    have houts : (fun i => (((squareCircuit N).iterate t).outputs i).toNat) =
        (fun i => squareOutputWire N t i.val) := List.ofFn_injective (congrArg Prod.snd ih)
    rw [Circuit.iterate, code_squareCircuit_comp, houts, ih]
    simp only [Circuit.size_iterate, size_squareCircuit, List.ofFn_succ_last, Fin.val_castSucc,
      Fin.val_last, List.flatten_append, List.flatten_singleton, squareOutputWire,
      Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]

end Boolean
end Cslib.Circuits
