/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Encoding.Check
public import CslibFrontier.Computability.Complexity.Classes.MIP.Arithmetization
public import CslibFrontier.Computability.Complexity.Reduction
import CslibFrontier.Computability.Circuit.Boolean.Encoding.Certificate
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Foundations.Data.List.Lookup

/-!
# Polynomial reductions to succinct 3-CNF decoder codes

A succinct decoder outputs three literals for each clause address. Each literal consists of its
variable address and required Boolean value. The two address widths are given in unary, and the
circuit is supplied as a list of gates and output wire numbers. This encoding lets a verifier
check circuit syntax and read the gate and output counts before running a proof protocol.
The gate count and both widths also determine the sumcheck dimensions and prime search bound.

[Proposition 4.2 of Babai, Fortnow and Lund][BabaiFortnowLund1991] encodes tableau consistency
as a Boolean formula with three oracle values. This formulation represents a three-literal clause
by the decoder's three address/sign pairs.

## Main definitions

* `Succinct3CNFInstance` contains the two address widths and the raw De Morgan circuit code.
* `Succinct3SAT` consists of valid codes whose expanded formula has a satisfying assignment.
* `Succinct3CNFInstance.signWires` and `addressWires` select the output wires of the three literals.

## Main results

* `Succinct3CNFInstance.valid_eq_true_iff` characterizes the polynomial-time syntax check.
* `Succinct3CNFInstance.signWires_eq` and `addressWires_eq` recover the typed decoder outputs.
* `polyTimeHard_positiveLabelSuccinct3SAT` reduces every native `NEXP` language to succinct
  satisfiability with positive label width.

## References

* [L. Babai, L. Fortnow and C. Lund, *Non-deterministic exponential time has two-prover
  interactive protocols*, §4.2, Proposition 4.2][BabaiFortnowLund1991]
-/

public section

namespace Cslib.Complexity.MIP

open Cslib.Circuits Cslib.Circuits.Boolean Turing.MultiTapeTM ComputableInPolyTime

/-- The clause and variable address widths and raw gates and output wires of a succinct decoder. -/
structure Succinct3CNFInstance where
  /-- Number of input bits indexing a clause. -/
  clauseBits : ℕ
  /-- Number of address bits in each of the three output literals. -/
  labelBits : ℕ
  /-- Decoder gates in program order followed by the interleaved address and sign outputs. -/
  code : List (Op × List ℕ) × List ℕ

/-- Framed unary clause and label widths followed by the Boolean circuit code, which numbers
all argument and output wires in binary. -/
enc_structure encSuccinct3CNF : Succinct3CNFInstance where
  clauseBits : encUnary, labelBits : encUnary, code : encCode

attribute [fun_prop] encSuccinct3CNF_mk_polyTime encSuccinct3CNF_clauseBits_polyTime
  encSuccinct3CNF_labelBits_polyTime encSuccinct3CNF_code_polyTime

/-- Satisfiability of the formula obtained by expanding a well-formed succinct decoder. -/
def Succinct3SAT : Set Succinct3CNFInstance :=
  {x | ∃ c : Circuit signature x.clauseBits (3 * (x.labelBits + 1)),
    c.code = x.code ∧ (SuccinctVerifier.toCNF c).Satisfiable}

/-- Check the gate list, output count and output references of a raw decoder. -/
@[expose] def Succinct3CNFInstance.valid (x : Succinct3CNFInstance) : Bool :=
  codeCheck signature x.clauseBits x.code.1 &&
    decide (x.code.2.length = 3 * (x.labelBits + 1)) &&
    x.code.2.all (· < x.clauseBits + x.code.1.length)

/-- Validity is equivalent to the existence of a typed decoder with precisely these gates
and output wires. -/
theorem Succinct3CNFInstance.valid_eq_true_iff (x : Succinct3CNFInstance) :
    x.valid = true ↔ ∃ c : Circuit signature x.clauseBits (3 * (x.labelBits + 1)),
      c.code = x.code := by
  rw [show (∃ c : Circuit signature x.clauseBits (3 * (x.labelBits + 1)), c.code = x.code) ↔
      (Circuit.ofCode x.clauseBits (3 * (x.labelBits + 1)) x.code :
        Option (Circuit signature _ _)).isSome from ?_, Circuit.isSome_ofCode_iff]
  · simp [valid, codeCheck_eq_true_iff, and_assoc]
  · constructor
    · rintro ⟨c, hc⟩
      rw [← hc, Circuit.ofCode_code]
      rfl
    · intro h
      exact ⟨_, Circuit.code_of_ofCode_eq_some (Option.some_get h).symm⟩

/-- The syntax of a succinct decoder can be checked in polynomial time, including on malformed
codes and on instances with no clause or variable address bits. -/
@[fun_prop] theorem Succinct3CNFInstance.computableInPolyTime_valid :
    ComputableInPolyTime Succinct3CNFInstance.valid encSuccinct3CNF encBool := by
  unfold valid
  fun_prop

namespace Succinct3CNFInstance

/-- Number of sumcheck variables: one Boolean coordinate per input and per gate. -/
@[expose] def sumcheckVars (x : Succinct3CNFInstance) : ℕ := x.clauseBits + x.code.1.length

/-- Individual degree bound of the succinct tableau constraint with a multilinear assignment. -/
@[expose] def sumcheckDegree (x : Succinct3CNFInstance) : ℕ :=
  1 + 3 * x.code.1.length + 3 * (x.labelBits + 1)

/-- Lower bound used to select the prime field for assignment testing and sumcheck. -/
@[expose] def fieldBound (x : Succinct3CNFInstance) : ℕ :=
  1000 * (x.labelBits + 1) ^ 3 + 100 * (x.sumcheckVars + 1) * (x.sumcheckDegree + 1)

/-- The field search has a positive lower endpoint on every raw instance. -/
theorem fieldBound_pos (x : Succinct3CNFInstance) : 0 < x.fieldBound := by
  unfold fieldBound
  positivity

/-- The sumcheck dimension can be produced in unary in polynomial time. -/
@[fun_prop] theorem computableInPolyTime_sumcheckVars :
    ComputableInPolyTime sumcheckVars encSuccinct3CNF encUnary := by unfold sumcheckVars; fun_prop

/-- The degree bound can be produced in unary in polynomial time. -/
@[fun_prop] theorem computableInPolyTime_sumcheckDegree :
    ComputableInPolyTime sumcheckDegree encSuccinct3CNF encUnary := by
  unfold sumcheckDegree
  fun_prop

/-- Compute the unary parameter for the verifier's prime search in polynomial time. -/
@[fun_prop] theorem computableInPolyTime_fieldBound :
    ComputableInPolyTime fieldBound encSuccinct3CNF encUnary := by
  unfold fieldBound
  fun_prop

/-- Output wire numbers for the required Boolean values of the three literals. A missing output
of a malformed code supplies wire zero. -/
@[expose] def signWires (x : Succinct3CNFInstance) : List ℕ :=
  (List.range 3).map fun j => x.code.2.getD (j * (x.labelBits + 1) + x.labelBits) 0

/-- Output wires for literal `j`'s variable address, in low-bit-first order. A missing output
of a malformed code supplies wire zero. -/
@[expose] def addressWires (x : Succinct3CNFInstance) (j : ℕ) : List ℕ :=
  (List.range x.labelBits).map fun i => x.code.2.getD (j * (x.labelBits + 1) + i) 0

/-- Read the three sign wires from the raw decoder in polynomial time. -/
@[fun_prop] theorem computableInPolyTime_signWires :
    ComputableInPolyTime signWires encSuccinct3CNF (encList encNat) := by
  unfold signWires
  apply mapWithInput (const (encOut := encList encUnary) (List.range 3))
  fun_prop

/-- Read the address-wire list of a literal with a unary index in polynomial time. -/
@[fun_prop] theorem computableInPolyTime_addressWires {α : Type} {enc : α ↪ List Bool}
    {x : α → Succinct3CNFInstance} {j : α → ℕ} (hx : ComputableInPolyTime x enc encSuccinct3CNF)
    (hj : ComputableInPolyTime j enc encUnary) :
    ComputableInPolyTime (fun a => (x a).addressWires (j a)) enc (encList encNat) := by
  unfold addressWires
  apply mapWithInput (range.comp (encSuccinct3CNF_labelBits_polyTime hx))
  apply listGetDWithInput
  · exact (snd _ _).comp ((encSuccinct3CNF_code_polyTime hx).comp (fst _ _))
  · exact unary_add' (unary_mul' (hj.comp (fst _ _))
      (unary_add' ((encSuccinct3CNF_labelBits_polyTime hx).comp (fst _ _)) (const 1))) (snd _ _)

/-- The three selected sign wires are exactly those used by the typed arithmetization. -/
theorem signWires_eq {x : Succinct3CNFInstance}
    (c : Circuit signature x.clauseBits (3 * (x.labelBits + 1))) (hc : c.code = x.code) :
    x.signWires =
      List.ofFn fun j => (c.outputs (SuccinctVerifier.signWire x.labelBits j)).toNat := by
  apply List.ext_getElem (by simp [signWires])
  intro i hi _
  have hj : i < 3 := by simpa [signWires] using hi
  simp only [signWires, List.getElem_map, List.getElem_range, List.getElem_ofFn, ← hc, Circuit.code]
  exact List.getD_ofFn _ (SuccinctVerifier.signWire x.labelBits ⟨i, hj⟩) 0

/-- A typed decoder's selected address wires are those of its `j`th literal. -/
theorem addressWires_eq {x : Succinct3CNFInstance}
    (c : Circuit signature x.clauseBits (3 * (x.labelBits + 1))) (hc : c.code = x.code)
    (j : Fin 3) : x.addressWires j =
      List.ofFn fun i => (c.outputs (SuccinctVerifier.addressWire x.labelBits j i)).toNat := by
  apply List.ext_getElem (by simp [addressWires])
  intro i hi _
  have hi' : i < x.labelBits := by simpa [addressWires] using hi
  simp only [addressWires, List.getElem_map, List.getElem_range, List.getElem_ofFn, ← hc,
    Circuit.code]
  exact List.getD_ofFn _ (SuccinctVerifier.addressWire x.labelBits j ⟨i, hi'⟩) 0

end Succinct3CNFInstance

/-- Every native nondeterministic exponential-time language reduces in polynomial time to
satisfiability of a succinct 3-CNF decoder with positive variable address width. -/
theorem polyTimeHard_positiveLabelSuccinct3SAT :
    PolyTimeHard @NEXP encSuccinct3CNF {x | x ∈ Succinct3SAT ∧ 0 < x.labelBits} := by
  intro α enc A hA
  obtain ⟨k, State, hfin, hdec, tm, n, T, hcode, hQ, hL, h⟩ :=
    exists_succinctDecoder_of_mem_NEXP hA
  let f (a : α) : Succinct3CNFInstance :=
    ⟨Tableau.clauseBits k State (T a), Tableau.labelBits k State (T a),
      Tableau.Decoder.decoderCode tm (frame (enc a), n a, T a)⟩
  refine ⟨f, ?_, fun a => ?_⟩
  · exact encSuccinct3CNF_mk_polyTime hQ hL hcode
  · obtain ⟨hx, hn, hsat, c, hc, _, hdecode⟩ := h a
    have hiff := satisfiable_toCNF_iff_succinctCNF tm hn hx c hdecode
    change a ∈ A ↔ (∃ d : Circuit signature _ _, d.code = _ ∧
      (SuccinctVerifier.toCNF d).Satisfiable) ∧ _
    constructor
    · intro ha
      exact ⟨⟨c, hc, hiff.2 (hsat.1 ha)⟩, by simp [f, Tableau.labelBits]⟩
    · rintro ⟨⟨d, hd, hdSat⟩, _⟩
      have hdc : d = c := Circuit.code_injective (hd.trans hc.symm)
      exact hsat.2 (hiff.1 (hdc ▸ hdSat))

end Cslib.Complexity.MIP
