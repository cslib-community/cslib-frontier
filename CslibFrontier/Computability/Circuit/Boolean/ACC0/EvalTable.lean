/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.ACC0.Gadgets
public import CslibFrontier.Computability.Circuit.Boolean.Unbounded.Encoding
public import CslibFrontier.Computability.Circuit.Encoding.Combinators
import CslibFrontier.Computability.Circuit.Boolean.Simps
import CslibFrontier.Computability.Circuit.CompositionDepth
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Copies of a circuit with hardwired prefixes, with polynomial-time codes

For a circuit `G` on `n + a` inputs over `Unbounded.extSignature` and a family of `P` prefixes
`bits p : BitString n`, the circuit `evalTable G P bits` on the `a` live inputs has `P` outputs: its
output `p` is `G` evaluated on `bits p` followed by the live inputs. It is `P` copies of the
construction `hardwirePrefix`, sharing the inputs; each copy has its own two constant gates
(`Unbounded.substituteCircuit` with `prependInputs`). The circuit
`withInputs E` lists the outputs of `E` followed by its inputs.

The raw code builders `evalTableCode` and `withInputsCode` are total list computations that agree
with the codes of the typed circuits. The number `a` of live inputs is unary in the polynomial-time
certificates, since the code of `withInputs E` lists all `a` input wires.

## Main definitions

* `Cslib.Circuits.Boolean.Unbounded.evalTable`: `G` on each hardwired prefix, on shared inputs.
* `Cslib.Circuits.Boolean.Unbounded.withInputs`: the outputs of a circuit followed by its inputs.
* `Cslib.Circuits.Boolean.Unbounded.evalTableCode`,
  `Cslib.Circuits.Boolean.Unbounded.withInputsCode`: their raw codes.

## Main results

* `Cslib.Circuits.Boolean.Unbounded.eval_evalTable`,
  `Cslib.Circuits.Boolean.Unbounded.depth_evalTable_le`: what `evalTable` computes, at depth at most
  one more than `G`.
* `Cslib.Circuits.Boolean.Unbounded.eval_withInputs`,
  `Cslib.Circuits.Boolean.Unbounded.depth_withInputs_le`: what `withInputs` computes, at no extra
  depth.
* `Cslib.Circuits.Boolean.Unbounded.code_evalTable`,
  `Cslib.Circuits.Boolean.Unbounded.code_withInputs`: the codes of the typed circuits.
* `Cslib.Circuits.Boolean.Unbounded.computableInPolyTime_evalTableCode`,
  `Cslib.Circuits.Boolean.Unbounded.computableInPolyTime_withInputsCode`: the codes are computable
  in polynomial time.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Unbounded

open Turing.MultiTapeTM ComputableInPolyTime

/-! ### Typed circuits -/

/-- `P` copies of `G` on shared live inputs: output `p` is `G` on the prefix `bits p` followed by
the live inputs. -/
def evalTable {n a : ℕ} (G : Circuit extSignature (n + a) 1) (P : ℕ)
    (bits : Fin P → BitString n) : Circuit extSignature a P :=
  Circuit.pi fun p =>
    G.comp (substituteCircuit toExt (prependInputs (bits p)))

/-- Output `p` of `evalTable G P bits` is `G` on `bits p` followed by the live inputs. -/
theorem eval_evalTable (q : ℕ) {n a : ℕ} (G : Circuit extSignature (n + a) 1) (P : ℕ)
    (bits : Fin P → BitString n) (x : BitString a) (p : Fin P) :
    (evalTable G P bits).eval (extInterpretation (modGate q)) x p =
      G.eval (extInterpretation (modGate q)) (Fin.append (bits p) x) 0 := by
  simp only [evalTable, Circuit.eval_pi, Circuit.eval_comp,
    eval_substituteCircuit, substitute_prependInputs]

/-- `evalTable G P bits` is at most one layer deeper than `G`. -/
theorem depth_evalTable_le {n a : ℕ} (G : Circuit extSignature (n + a) 1) (P : ℕ)
    (bits : Fin P → BitString n) : (evalTable G P bits).depth ≤ G.depth + 1 := by
  circuit_bound [evalTable]

/-- The outputs of `E` followed by its inputs. -/
def withInputs {a P : ℕ} (E : Circuit extSignature a P) : Circuit extSignature a (P + a) :=
  E.append (Circuit.wiring extSignature id)

/-- `withInputs E` lists the outputs of `E`, then the inputs. -/
theorem eval_withInputs (q : ℕ) {a P : ℕ} (E : Circuit extSignature a P) (x : BitString a) :
    (withInputs E).eval (extInterpretation (modGate q)) x =
      Fin.append (E.eval (extInterpretation (modGate q)) x) x := by
  simp only [withInputs, Circuit.eval_append, Circuit.eval_wiring]
  rfl

/-- `withInputs E` is no deeper than `E`. -/
theorem depth_withInputs_le {a P : ℕ} (E : Circuit extSignature a P) :
    (withInputs E).depth ≤ E.depth := by
  circuit_bound [withInputs]

/-! ### Raw codes -/

/-- The raw code of `withInputs E` from the raw code of `E`: the code of `E` and the identity
wiring on the `a` inputs, on shared inputs. -/
def withInputsCode (a : ℕ) (code : List (ExtOp × List ℕ) × List ℕ) :
    List (ExtOp × List ℕ) × List ℕ :=
  Circuit.appendCode a code ([], List.range a)

/-- The code of `withInputs E` is `withInputsCode a E.code`. -/
theorem code_withInputs {a P : ℕ} (E : Circuit extSignature a P) :
    (withInputs E).code = withInputsCode a E.code := by
  simp only [withInputs, withInputsCode, Circuit.code_append, Circuit.code_wiring_id]

/-- The raw code of the two constant gates on `a` inputs, a constant `false` gate and a constant
`true` gate, with each output of `z` wired to one of them. -/
def constsCode (a : ℕ) (z : List Bool) : List (ExtOp × List ℕ) × List ℕ :=
  ([(ExtOp.ac (.or 0), []), (ExtOp.ac (.and 0), [])], z.map fun b => if b then a + 1 else a)

/-- The code of `substituteCircuit toExt (prependInputs z)` on `a` live inputs is `constsCode` of
the bits of `z`, followed by the identity wiring on the live inputs. -/
theorem code_substituteCircuit_prependInputs {a m : ℕ} (z : BitString m) :
    (substituteCircuit (n := a) toExt (prependInputs z)).code =
      withInputsCode a (constsCode a (List.ofFn z)) := by
  have ht : (constCircuit (n := a) toExt true).code = ([(ExtOp.ac (.and 0), [])], [a]) := rfl
  have hf : (constCircuit (n := a) toExt false).code = ([(ExtOp.ac (.or 0), [])], [a]) := rfl
  simp only [substituteCircuit, projectionCircuit, Circuit.code_comp, Circuit.code_append,
    Circuit.code_wiring, withInputsCode, constsCode, Circuit.compCode, Circuit.appendCode, ht, hf]
  refine Prod.ext (by simp) ?_
  simp only [List.map_ofFn, List.map_append]
  rw [List.ofFn_add]
  congr 1
  · simp only [List.length_nil, List.map_cons, List.map_nil, List.length_cons, zero_add,
      List.cons_append, List.nil_append, id_eq, Circuit.shiftCodeWire, lt_self_iff_false,
      ↓reduceIte, add_zero, add_lt_iff_neg_left, not_lt_zero, prependInputs, Function.comp_apply,
      Circuit.compCodeWire, Fin.append_left', Sum.elim_inr, Fin.val_natAdd, List.length_append,
      List.length_ofFn, Nat.reduceAdd, add_lt_add_iff_left, Order.lt_two_iff,
      List.getD_eq_getElem?_getD, add_le_add_iff_left, Fin.is_le', Nat.sub_eq_zero_of_le,
      List.ofFn_inj]
    funext i
    cases hz : z i <;> simp [constIndex, hz]
  · refine List.ext_getElem (by simp) fun i h1 h2 => ?_
    simp only [List.length_nil, List.map_cons, List.map_nil, List.length_cons, zero_add,
      List.cons_append, List.nil_append, id_eq, Circuit.shiftCodeWire, lt_self_iff_false,
      ↓reduceIte, add_zero, add_lt_iff_neg_left, not_lt_zero, prependInputs, Function.comp_apply,
      Circuit.compCodeWire, Fin.append_right, Sum.elim_inl, Fin.val_castAdd, List.length_append,
      List.length_ofFn, Nat.reduceAdd, List.getD_eq_getElem?_getD, List.getElem_ofFn,
      List.getElem_map, List.getElem_range]
    have : i < a := by simpa using h2
    simp only [this, show i < a + 2 by omega, ↓reduceIte]
    rw [List.getElem?_append_left (by simpa using this)]
    simp [this]

/-- The raw code of `evalTable G P bits` from the raw code of `G` and the prefixes. -/
def evalTableCode (a : ℕ) (Gcode : List (ExtOp × List ℕ) × List ℕ) (bits : List (List Bool)) :
    List (ExtOp × List ℕ) × List ℕ :=
  Circuit.appendCodes a
    (bits.map fun b => Circuit.compCode a Gcode (withInputsCode a (constsCode a b)))

/-- The code of `evalTable G P bits` is `evalTableCode` of the codes of `G` and the prefixes. -/
theorem code_evalTable {n a : ℕ} (G : Circuit extSignature (n + a) 1) (P : ℕ)
    (bits : Fin P → BitString n) :
    (evalTable G P bits).code =
      evalTableCode a G.code (List.ofFn fun p => List.ofFn (bits p)) := by
  simp only [evalTable, evalTableCode, Circuit.code_pi, Circuit.code_comp,
    code_substituteCircuit_prependInputs, List.map_ofFn, Function.comp_def]

/-! ### Polynomial-time certificates -/

section PolyTime

variable {α : Type} {enc : α ↪ List Bool}

/-- The code of `withInputs E` is computable in polynomial time from a unary input count and the
code of `E`. -/
theorem computableInPolyTime_withInputsCode {a : α → ℕ}
    {code : α → List (ExtOp × List ℕ) × List ℕ}
    (ha : ComputableInPolyTime a enc encUnary)
    (hc : ComputableInPolyTime code enc (Circuit.encCode encExtOp)) :
    ComputableInPolyTime (fun z => withInputsCode (a z) (code z)) enc
      (Circuit.encCode encExtOp) := by
  have hr := unary_to_binary.map.comp (range.comp ha)
  have hrange : ComputableInPolyTime
      (fun z => (([] : List (ExtOp × List ℕ)), List.range (a z))) enc
      (Circuit.encCode encExtOp) := by
    simpa only [Function.comp_def, List.map_id_fun', id_eq] using
      (const ([] : List (ExtOp × List ℕ))).prod hr
  exact Circuit.computableInPolyTime_appendCode (unary_to_binary.comp ha) hc hrange

/-- `constsCode` is computable in polynomial time from a binary input count and the bits. -/
theorem computableInPolyTime_constsCode {a : α → ℕ} {z : α → List Bool}
    (ha : ComputableInPolyTime a enc encNat)
    (hz : ComputableInPolyTime z enc (encList encBool)) :
    ComputableInPolyTime (fun w => constsCode (a w) (z w)) enc (Circuit.encCode encExtOp) := by
  have hf : ComputableInPolyTime (fun q : ℕ × Bool => if q.2 then q.1 + 1 else q.1)
      (encPair encNat encBool) encNat := by
    fun_prop
  exact (const [(ExtOp.ac (.or 0), []), (ExtOp.ac (.and 0), [])]).prod (mapWith hf ha hz)

/-- The code of `evalTable G P bits` is computable in polynomial time from a unary count of live
inputs, the code of `G` and the prefixes as bit strings. -/
theorem computableInPolyTime_evalTableCode {a : α → ℕ}
    {Gcode : α → List (ExtOp × List ℕ) × List ℕ} {bits : α → List (List Bool)}
    (ha : ComputableInPolyTime a enc encUnary)
    (hG : ComputableInPolyTime Gcode enc (Circuit.encCode encExtOp))
    (hbits : ComputableInPolyTime bits enc (encList encBits)) :
    ComputableInPolyTime (fun z => evalTableCode (a z) (Gcode z) (bits z)) enc
      (Circuit.encCode encExtOp) := by
  have hbin : ComputableInPolyTime a enc encNat := unary_to_binary.comp ha
  have hblock : ComputableInPolyTime
      (fun p : α × List Bool =>
        Circuit.compCode (a p.1) (Gcode p.1) (withInputsCode (a p.1) (constsCode (a p.1) p.2)))
      (encPair enc encBits) (Circuit.encCode encExtOp) := by
    have hfst := fst enc encBits
    have hb := (bits_encList_polyTime encBool).1.comp (snd enc encBits)
    exact Circuit.computableInPolyTime_compCode (hbin.comp hfst) (hG.comp hfst)
      (computableInPolyTime_withInputsCode (ha.comp hfst)
        (computableInPolyTime_constsCode (hbin.comp hfst) hb))
  exact Circuit.computableInPolyTime_appendCodes hbin (mapWithInput hbits hblock)

end PolyTime

end Cslib.Circuits.Boolean.Unbounded
