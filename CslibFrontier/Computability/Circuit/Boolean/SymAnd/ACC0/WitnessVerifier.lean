/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.SuccinctVerifier
public import CslibFrontier.Computability.Circuit.Boolean.SymAnd.ACC0.SAT
public import CslibFrontier.Computability.Complexity.Classes.Hierarchy.FineNondeterministicExponentialTime
public import CslibFrontier.Foundations.Data.BitString.List.Binary
import CslibFrontier.Computability.Circuit.CompositionDepth
import CslibFrontier.Computability.Circuit.Encoding.Check
import CslibFrontier.Computability.Circuit.Encoding.Combinators
import CslibFrontier.Computability.Circuit.Encoding.PolyTime
import CslibFrontier.Computability.Complexity.Classes.Time.Verifier
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.TwoPow
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.NthRoot
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Frame
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Foundations.Data.Nat.LogRpow
import CslibFrontier.Foundations.Data.Nat.NthRootGrowth
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Witness verification and `NTIME` diagonalization transfer for `ACC⁰`

This module formalizes the constant-depth witness-verification and nondeterministic-time
diagonalization bridge from Williams's proof that `ACC⁰-SAT` algorithms imply witness-circuit lower
bounds ([Williams2014], Section 3, Theorem 3.2, statement p. 8 and proof p. 13 of the author's
July 31, 2012 version).

Given a succinct 3-CNF decoder circuit `D` over `Unbounded.extSignature` (`ACC⁰[m]`) on `q` inputs
describing `2 ^ q` clauses over `2 ^ r` variables in the interleaved address/sign layout of
`Cslib.Circuits.Boolean.SuccinctVerifier`, and a candidate witness circuit `W` on `r` inputs:

1. **Constant-depth bad-clause verifier (`badClauseExt`)**: plugs three copies of `W` and one copy
   of `D` into the embedded 3-literal violation test `SuccinctVerifier.violationTest`. The resulting
   `ACC⁰[m]` circuit has `q` inputs, `D.size + 3 * W.size + 17` gates, depth at most
   `D.depth + W.depth + 5`, and is unsatisfiable precisely when `W`'s truth table satisfies
   `toCNFExt m D` (`not_mem_SignatureCircuitSAT_badClauseExt_iff`).
2. **Depth-capped certificate compilation (`decodeExtWitness`, `certificateCircuitExt`)**: decodes
   a framed canonical circuit code at the start of a bit string to a valid depth-`≤ d` witness
   circuit `W` (rejecting non-canonical or malformed codes and circuits exceeding depth `d` by
   emitting the always-satisfiable constant-`true` circuit), with a native polynomial-time
   compilation certificate (`computableInPolyTime_certificateCircuitExt`).
3. **Subexponential-savings `NTIME` simulation (`smallACC0WitnessLanguage_mem_NTIME_of_acc0SAT`)**:
   combines `certificateCircuitExt` with Williams's `ACC⁰-SAT` algorithm (`exists_acc0SAT_decider`,
   [Williams2014], Theorem 4.1) to decide in `NTIME(⌊2 ^ (n - c₀ * n ^ δ)⌋₊)` whether a quasilinear
   uniform depth-`≤ dD` `ACC⁰[m]` succinct 3-CNF has a satisfying assignment computable by a
   depth-`≤ dW` `ACC⁰[m]` circuit of code length at most `2 ^ Nat.nthRoot r_w n`.
4. **Hard-witness transfer (`exists_hard_acc0Witness_of_quasilinear_reduction`)**: combines the
   simulation with the fine nondeterministic exponential time hierarchy at arbitrarily large
   lengths (`Cslib.Complexity.exists_mem_NTIME_two_pow_forall_exists_length_ge`, [Zak1983]) to
   produce a single language `H ∈ NTIME(2 ^ n)` such that every polynomial-time
   uniform depth-`≤ dD` `ACC⁰[m]` quasilinear succinct 3-CNF reduction of `H` has satisfiable
   instances `x ∈ H` of every sufficiently large length admitting no depth-`≤ dW`,
   code-length-`≤ 2 ^ Nat.nthRoot r_w |x|` `ACC⁰[m]` satisfying witness circuit.
5. **Checked decoders (`CheckedACC0Decoders`, `checkedACC0WitnessLanguage_mem_NTIME_of_acc0SAT`,
   `exists_hard_checkedACC0Witness`)**: the same simulation and transfer when the decoder
   `D (x, e)` depends on a guessed certificate `e` of polynomial length `ℓ x`, which a second
   constant-depth `ACC⁰[m]` circuit `C₁ (x, e)` must certify by being unsatisfiable. The machine
   guesses `e` and the witness certificate, pads `C₁ (x, e)` and `certificateCircuitExt (D (x, e))`
   to a common input count, and runs `exists_acc0SAT_decider` once on their disjunction. Items 3
   and 4 are the case without a certificate, with the constant `false` check circuit.

## Scope note

This module proves the witness-verifier and diagonalization-transfer steps unconditionally. The
quasilinear succinct 3-CNF reduction for `NTIME(2 ^ n)` ([Williams2014], Fact 3.1) is
`Cslib.Complexity.CookLevin.Quasilinear.exists_polySuccinctReduction`, and the compression of its
decoders into checked `ACC⁰` decoders ([Williams2014], Lemma 3.1) is
`SymAnd.exists_checkedDecoders`; `SymAnd.ENPNotACC0` combines them with
`exists_hard_checkedACC0Witness` into `E^NP ⊄ ACC⁰` (`SymAnd.not_forall_ENP_mem_ACC0`).
`NEXP ⊄ ACC⁰` ([Williams2014], Theorem 1.1) also needs the easy-witness lemma of
Impagliazzo, Kabanets and Wigderson; `SymAnd.NEXPNotACC0` applies it to the formulas of the same
reduction.

## Main definitions

* `Cslib.Circuits.Boolean.SymAnd.clauseExt`, `Cslib.Circuits.Boolean.SymAnd.toCNFExt`:
  succinct 3-CNF represented by an `ACC⁰[m]` decoder circuit.
* `Cslib.Circuits.Boolean.SymAnd.variableIndex`: the number of a variable of `r` bits.
* `Cslib.Circuits.Boolean.SymAnd.CheckedACC0Decoders`: polynomial-time uniform constant-depth
  decoders `D (x, e)` with check circuits `C₁ (x, e)`, for a certificate `e` of polynomial length.
* `Cslib.Circuits.Boolean.SymAnd.badClauseExt`: constant-depth `ACC⁰[m]` bad-clause verifier.
* `Cslib.Circuits.Boolean.SymAnd.decodeExtWitness`,
  `Cslib.Circuits.Boolean.SymAnd.certificateCircuitExt`: depth-capped witness decoder and total
  verifier circuit compiler.
* `Cslib.Circuits.Boolean.SymAnd.smallACC0WitnessLanguage`: language of inputs whose succinct
  3-CNF admits a small constant-depth `ACC⁰[m]` satisfying witness circuit.
* `Cslib.Circuits.Boolean.SymAnd.checkedACC0WitnessLanguage`: the checked-decoder variant, where
  the decoder depends on a certificate `e` that a second circuit `C₁ (x, e)` must reject.

## Main results

* `Cslib.Circuits.Boolean.SymAnd.size_badClauseExt`,
  `Cslib.Circuits.Boolean.SymAnd.depth_badClauseExt_le`,
  `Cslib.Circuits.Boolean.SymAnd.eval_badClauseExt`,
  `Cslib.Circuits.Boolean.SymAnd.not_mem_SignatureCircuitSAT_badClauseExt_iff`: size, depth, and
  correctness of `badClauseExt`.
* `Cslib.Circuits.Boolean.SymAnd.exists_cert_not_mem_SignatureCircuitSAT_iff`,
  `Cslib.Circuits.Boolean.SymAnd.computableInPolyTime_decodeExtWitness`,
  `Cslib.Circuits.Boolean.SymAnd.computableInPolyTime_certificateCircuitExt`: witness equivalence
  and native polynomial-time decoding and compilation.
* `Cslib.Circuits.Boolean.SymAnd.smallACC0WitnessLanguage_mem_NTIME_of_acc0SAT`: unconditional
  `NTIME(⌊2 ^ (n - c₀ * n ^ δ)⌋₊)` upper bound via `exists_acc0SAT_decider`.
* `Cslib.Circuits.Boolean.SymAnd.exists_hard_acc0Witness_of_quasilinear_reduction`: witness-circuit
  lower bound for every quasilinear `ACC⁰[m]` succinct 3-CNF reduction of a hard language in
  `NTIME(2 ^ n)`.
* `Cslib.Circuits.Boolean.SymAnd.checkedACC0WitnessLanguage_mem_NTIME_of_acc0SAT`,
  `Cslib.Circuits.Boolean.SymAnd.exists_hard_checkedACC0Witness`: the same `NTIME` upper bound and
  hard-witness lower bound for checked decoders.

## References

* [R. Williams, *Non-Uniform ACC Circuit Lower Bounds*, July 31, 2012 version, Section 3,
  Theorem 3.2 (pp. 8, 13) and Section 4, Theorem 4.1 (p. 17)][Williams2014]
* [S. Žák, *A Turing Machine Time Hierarchy*][Zak1983]
-/

public section

namespace Cslib.Circuits.Boolean.SymAnd

open Turing.MultiTapeTM Cslib.Circuits Cslib.Circuits.Boolean Cslib.Complexity Cslib.Logic.PL Filter

/-! ### 1. Succinct 3-CNF over `Unbounded.extSignature` and `badClauseExt` -/

section BadClause

variable {q r : ℕ}

/-- The clause at address `x` decoded by an `ACC⁰[m]` circuit `D` on `q` inputs, using the
interleaved address/sign layout of `SuccinctVerifier`. -/
@[expose] def clauseExt (m : ℕ) (D : Circuit Unbounded.extSignature q (3 * (r + 1)))
    (x : BitString q) : Clause (BitString r) :=
  List.ofFn fun j : Fin 3 =>
    (fun i => D.eval (Unbounded.extInterpretation (modGate m)) x
        (SuccinctVerifier.addressWire r j i),
      D.eval (Unbounded.extInterpretation (modGate m)) x (SuccinctVerifier.signWire r j))

/-- Expand every `q`-bit clause address of an `ACC⁰[m]` decoder `D` into a 3-CNF on `2 ^ r`
variables. -/
@[expose] def toCNFExt (m : ℕ) (D : Circuit Unbounded.extSignature q (3 * (r + 1))) :
    CNF (BitString r) :=
  (BitString.enum q).map (clauseExt m D)

/-- The number of an `r`-bit variable: its bits read most significant first. -/
@[expose] def variableIndex {r : ℕ} (v : BitString r) : ℕ :=
  Cslib.BitString.binaryValue (List.ofFn v)

/-- The expanded formula `toCNFExt m D` holds on an assignment `a` iff every clause address is
satisfied. -/
theorem eval_toCNFExt_eq_true_iff (m : ℕ) (D : Circuit Unbounded.extSignature q (3 * (r + 1)))
    (a : BitString r → Bool) :
    (toCNFExt m D).eval a = true ↔ ∀ x : BitString q, (clauseExt m D x).eval a = true := by
  simp [toCNFExt, CNF.eval_map_eq_true_iff]

/-- The De Morgan signature embedded into `Unbounded.extSignature`. -/
private def deMorganToExt : Boolean.signature.Hom Unbounded.extSignature :=
  Unbounded.toExt.comp Unbounded.deMorganToUnbounded

private instance preserves_deMorganToExt (m : ℕ) :
    deMorganToExt.Preserves Boolean.interpretation (Unbounded.extInterpretation (modGate m)) :=
  Signature.Hom.Preserves.comp (Unbounded.preserves_toExt (modGate m))
    Unbounded.preserves_deMorganToUnbounded

/-- Fixed 17-gate, depth-5 three-literal violation test over `Unbounded.extSignature`, lifted from
`SuccinctVerifier.violationTest`. -/
private def violationTestExt : Circuit Unbounded.extSignature 6 1 :=
  SuccinctVerifier.violationTest.toCircuit.mapOp deMorganToExt

private theorem size_violationTestExt : violationTestExt.size = 17 := by
  simp [violationTestExt, Circuit.size_mapOp]

private theorem depth_violationTestExt_le : violationTestExt.depth ≤ 5 := by
  rw [violationTestExt, Circuit.depth_mapOp]
  exact SuccinctVerifier.violationTest.depth_toCircuit_le.trans (by decide)

private theorem eval_violationTestExt (m : ℕ) (values signs : Fin 3 → Bool) :
    violationTestExt.eval (Unbounded.extInterpretation (modGate m))
      (Fin.append values signs) 0 =
      ((values 0 ^^ signs 0) && ((values 1 ^^ signs 1) && (values 2 ^^ signs 2))) := by
  rw [violationTestExt,
    @Circuit.eval_mapOp _ _ _ _ _ deMorganToExt Boolean.interpretation
      (Unbounded.extInterpretation (modGate m)) (preserves_deMorganToExt m),
    Formula.eval_toCircuit]
  exact SuccinctVerifier.eval_violationTest values signs

/-- **Constant-depth `ACC⁰` bad-clause circuit**: evaluates the decoder `D` once, feeds each of
the three decoded variable addresses into a copy of `W`, and checks whether all three literals of
the addressed clause are violated. -/
def badClauseExt (D : Circuit Unbounded.extSignature q (3 * (r + 1)))
    (W : Circuit Unbounded.extSignature r 1) : Circuit Unbounded.extSignature q 1 :=
  (violationTestExt.comp
    ((Circuit.pi fun j : Fin 3 =>
        W.comp (Circuit.wiring Unbounded.extSignature (SuccinctVerifier.addressWire r j))).append
      (Circuit.wiring Unbounded.extSignature (SuccinctVerifier.signWire r)))).comp D

/-- **Exact gate count of `badClauseExt`.** -/
@[simp] theorem size_badClauseExt (D : Circuit Unbounded.extSignature q (3 * (r + 1)))
    (W : Circuit Unbounded.extSignature r 1) :
    (badClauseExt D W).size = D.size + 3 * W.size + 17 := by
  simp [badClauseExt, size_violationTestExt, Finset.sum_const, Nat.mul_comm, Nat.add_assoc]

/-- **Constant additive depth overhead of `badClauseExt`.** -/
theorem depth_badClauseExt_le (D : Circuit Unbounded.extSignature q (3 * (r + 1)))
    (W : Circuit Unbounded.extSignature r 1) :
    (badClauseExt D W).depth ≤ D.depth + W.depth + 5 := by
  unfold badClauseExt
  let wAddr (j : Fin 3) := Circuit.wiring Unbounded.extSignature (SuccinctVerifier.addressWire r j)
  let wSign := Circuit.wiring Unbounded.extSignature (SuccinctVerifier.signWire r)
  let piC := Circuit.pi fun j : Fin 3 => W.comp (wAddr j)
  have hpi : piC.depth ≤ W.depth :=
    Circuit.depth_pi_le _ fun j => by simpa [wAddr] using Circuit.depth_comp_le W (wAddr j)
  have happ : (piC.append wSign).depth ≤ W.depth :=
    hpi.trans' (by simpa [wSign] using Circuit.depth_append_le piC wSign)
  have houter := Circuit.depth_comp_le (violationTestExt.comp (piC.append wSign)) D
  have hmid := Circuit.depth_comp_le violationTestExt (piC.append wSign)
  have hv := depth_violationTestExt_le
  change ((violationTestExt.comp (piC.append wSign)).comp D).depth ≤ _
  omega

/-- **Pointwise correctness of `badClauseExt`**: returns `true` on clause address `x` iff `W`'s
truth table violates clause `x`. -/
theorem eval_badClauseExt (m : ℕ) (D : Circuit Unbounded.extSignature q (3 * (r + 1)))
    (W : Circuit Unbounded.extSignature r 1) (x : BitString q) :
    (badClauseExt D W).eval (Unbounded.extInterpretation (modGate m)) x 0 =
      !(clauseExt m D x).eval
        (fun y => W.eval (Unbounded.extInterpretation (modGate m)) y 0) := by
  simp only [badClauseExt, Circuit.eval_comp, Circuit.eval_append, Circuit.eval_pi,
    Circuit.eval_wiring, eval_violationTestExt, Function.comp_def]
  simp only [clauseExt, List.ofFn_succ, List.ofFn_zero, Clause.eval_cons, Clause.eval_nil,
    Literal.eval_mk, Bool.or_false]
  simp only [← Bool.bne_eq_xor, bne, Bool.not_or, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]

/-- **Verification by `ACC⁰` circuit unsatisfiability**: `badClauseExt D W` is unsatisfiable iff
`W`'s truth table satisfies `toCNFExt m D`. -/
theorem not_mem_SignatureCircuitSAT_badClauseExt_iff (m : ℕ)
    (D : Circuit Unbounded.extSignature q (3 * (r + 1)))
    (W : Circuit Unbounded.extSignature r 1) :
    (⟨q, badClauseExt D W⟩ ∉ SignatureCircuitSAT (Unbounded.extInterpretation (modGate m))) ↔
      (toCNFExt m D).eval
        (fun y => W.eval (Unbounded.extInterpretation (modGate m)) y 0) = true := by
  simp [mem_SignatureCircuitSAT, eval_badClauseExt, eval_toCNFExt_eq_true_iff]

end BadClause

/-! ### 2. Total certificate decoding and polynomial-time verifier compilation -/

section CertDecode

/-- Bijective inverse of `Unbounded.ExtOp.toNat` on `ℕ`. -/
private def extOpOfNat : ℕ → Unbounded.ExtOp
  | 0 => .ac .not
  | n + 1 =>
    match n % 3 with
    | 0 => .ac (.and (n / 3))
    | 1 => .ac (.or (n / 3))
    | _ => .gate (n / 3)

private theorem extOpOfNat_toNat (op : Unbounded.ExtOp) : extOpOfNat op.toNat = op := by
  rcases op with (_ | m | m) | m <;> simp only [Unbounded.ExtOp.toNat, extOpOfNat]
  · simp [Nat.mul_mod_right, Nat.mul_div_right _ (by decide : 0 < 3)]
  · rw [show (3 * m + 1) % 3 = 1 by omega, show (3 * m + 1) / 3 = m by omega]; rfl
  · rw [show (3 * m + 2) % 3 = 2 by omega, show (3 * m + 2) / 3 = m by omega]; rfl

private theorem toNat_extOpOfNat (k : ℕ) : (extOpOfNat k).toNat = k := by
  rcases k with _ | n
  · rfl
  · simp only [extOpOfNat]
    have := Nat.div_add_mod n 3
    have := Nat.mod_lt n (by decide : 0 < 3)
    rcases hm : n % 3 with _ | _ | _ | r <;> simp only [Unbounded.ExtOp.toNat] <;> omega

/-- Total polynomial-time decoder for `Unbounded.encExtOp`. -/
private def decExtOp : Decoder Unbounded.encExtOp :=
  Decoder.map Decoder.unary extOpOfNat Unbounded.ExtOp.toNat extOpOfNat_toNat fun k =>
    congrArg encUnary (toNat_extOpOfNat k)

/-- Total polynomial-time decoder for raw `Unbounded.extSignature` circuit codes. -/
private def decExtCode : Decoder (Circuit.encCode Unbounded.encExtOp) :=
  Decoder.pair (Decoder.list (Decoder.pair decExtOp (Decoder.list Decoder.nat)))
    (Decoder.list Decoder.nat)

private theorem extArity_eq (op : Unbounded.ExtOp) :
    Unbounded.extSignature.Arity op = if op.toNat = 0 then 1 else (op.toNat - 1) / 3 := by
  rcases op with (_ | m | m) | m
  · rfl
  · simp [Unbounded.ExtOp.arity, Unbounded.Op.arity, Unbounded.ExtOp.toNat]
  · simp [Unbounded.ExtOp.arity, Unbounded.Op.arity, Unbounded.ExtOp.toNat]; omega
  · simp [Unbounded.ExtOp.arity, Unbounded.ExtOp.toNat]; omega

private theorem computableInPolyTime_extArity :
    ComputableInPolyTime Unbounded.extSignature.Arity Unbounded.encExtOp encNat := by
  have h1 : ComputableInPolyTime (fun op : Unbounded.ExtOp =>
      if op.toNat = 0 then 1 else (op.toNat - 1) / 3) Unbounded.encExtOp encUnary := by
    have htest : ComputableInPolyTime (fun op : Unbounded.ExtOp => decide (op.toNat = 0))
        Unbounded.encExtOp encBool := by fun_prop
    have hdiv : ComputableInPolyTime (fun op : Unbounded.ExtOp => (op.toNat - 1) / 3)
        Unbounded.encExtOp encUnary :=
      (ComputableInPolyTime.unary_div_const 3).comp (by fun_prop)
    exact (htest.ite (ComputableInPolyTime.const 1) hdiv).of_enc_eq fun op => by
      simp only [decide_eq_true_eq]
  exact (ComputableInPolyTime.unary_to_binary.comp h1).of_enc_eq fun op =>
    congrArg encNat (extArity_eq op)

/-- Decode a raw certificate bit string `w` into a valid `r`-input single-output `ACC⁰` witness
circuit of depth at most `d`, reading the canonical framed code at the start of `w` via `unframe w`.
Returns `none` on non-canonical words, malformed codes, wrong output count, out-of-range wires,
or depth `> d`. -/
def decodeExtWitness (d r : ℕ) (w : List Bool) :
    Option (Circuit Unbounded.extSignature r 1) :=
  let u := unframe w
  let code := decExtCode.decode u
  if Circuit.encCode Unbounded.encExtOp code = u then
    match Circuit.ofCode (σ := Unbounded.extSignature) r 1 code with
    | some W => if W.depth ≤ d then some W else none
    | none => none
  else none

/-- Decoding a framed encoding of a valid depth-`≤ d` circuit recovers it regardless of trailing
padding bits. -/
theorem decodeExtWitness_frame_append {d r : ℕ} (W : Circuit Unbounded.extSignature r 1)
    (hdepth : W.depth ≤ d) (pad : List Bool) :
    decodeExtWitness d r (frame (Circuit.encCode Unbounded.encExtOp W.code) ++ pad) = some W := by
  simp only [decodeExtWitness, unframe_frame_append, decExtCode.decode_enc, ↓reduceIte,
    Circuit.ofCode_code, hdepth]

/-- Decoding rejects a valid circuit whose depth exceeds the cap `d`. -/
theorem decodeExtWitness_eq_none_of_depth_gt {d r : ℕ} (W : Circuit Unbounded.extSignature r 1)
    (hdepth : d < W.depth) (pad : List Bool) :
    decodeExtWitness d r (frame (Circuit.encCode Unbounded.encExtOp W.code) ++ pad) = none := by
  have hnot : ¬ W.depth ≤ d := Nat.not_le.mpr hdepth
  simp only [decodeExtWitness, unframe_frame_append, decExtCode.decode_enc, ↓reduceIte,
    Circuit.ofCode_code, hnot]

/-- Decoding rejects the empty (non-canonical) certificate word. -/
theorem decodeExtWitness_nil (d r : ℕ) : decodeExtWitness d r [] = none := by
  unfold decodeExtWitness
  dsimp only [unframe]
  split_ifs with h
  · have := congrArg List.length h
    simp [Circuit.encCode] at this
  · rfl

/-- Any circuit returned by `decodeExtWitness d r w` has depth at most `d` and canonical code
length at most `w.length / 2`. -/
theorem depth_and_codeLength_of_decodeExtWitness_eq_some {d r : ℕ} {w : List Bool}
    {W : Circuit Unbounded.extSignature r 1} (h : decodeExtWitness d r w = some W) :
    W.depth ≤ d ∧ 2 * (Circuit.encCode Unbounded.encExtOp W.code).length ≤ w.length := by
  unfold decodeExtWitness at h
  dsimp only at h
  split_ifs at h with hcan
  rcases hof : Circuit.ofCode (σ := Unbounded.extSignature) r 1 (decExtCode.decode (unframe w))
    with _ | W'
  · simp [hof] at h
  · simp only [hof] at h
    split_ifs at h with hd
    obtain rfl := Option.some.inj h
    rw [Circuit.code_of_ofCode_eq_some hof, hcan]
    have := length_unframe_add_dropFrame_le w
    exact ⟨hd, by omega⟩

/-- The constant `true` circuit is always satisfiable. -/
private theorem constCircuit_true_mem_SignatureCircuitSAT (m q : ℕ) :
    ⟨q, Unbounded.constCircuit Unbounded.toExt true⟩ ∈
      SignatureCircuitSAT (Unbounded.extInterpretation (modGate m)) := by
  rw [mem_SignatureCircuitSAT]
  exact ⟨fun _ => false, Unbounded.eval_constCircuit _ _ _⟩

/-- The constant `false` circuit is never satisfiable. -/
private theorem constCircuit_false_not_mem_SignatureCircuitSAT (m q : ℕ) :
    ⟨q, Unbounded.constCircuit Unbounded.toExt false⟩ ∉
      SignatureCircuitSAT (Unbounded.extInterpretation (modGate m)) := by
  rw [mem_SignatureCircuitSAT]
  rintro ⟨x, hx⟩
  rw [Unbounded.eval_constCircuit] at hx
  exact Bool.false_ne_true hx

/-- **Total depth-capped verifier circuit**: decodes `w` as a depth-`≤ d` witness circuit `W` and
emits `badClauseExt D W`; if `w` is malformed or exceeds depth `d`, emits the always-satisfiable
constant-`true` circuit so the verifier rejects `w`. -/
def certificateCircuitExt {q r : ℕ}
    (D : Circuit Unbounded.extSignature q (3 * (r + 1))) (d : ℕ) (w : List Bool) :
    Circuit Unbounded.extSignature q 1 :=
  match decodeExtWitness d r w with
  | some W => badClauseExt D W
  | none => Unbounded.constCircuit Unbounded.toExt true

/-- `certificateCircuitExt D d w` always has depth at most `D.depth + d + 5`. -/
theorem depth_certificateCircuitExt_le {q r : ℕ}
    (D : Circuit Unbounded.extSignature q (3 * (r + 1))) (d : ℕ) (w : List Bool) :
    (certificateCircuitExt D d w).depth ≤ D.depth + d + 5 := by
  unfold certificateCircuitExt
  cases h : decodeExtWitness d r w with
  | none => exact (Unbounded.depth_constCircuit_le true).trans (by omega)
  | some W =>
    have hW := (depth_and_codeLength_of_decodeExtWitness_eq_some h).1
    exact (depth_badClauseExt_le D W).trans (by omega)

/-- `certificateCircuitExt D d w` is unsatisfiable iff `w` decodes to a depth-`≤ d` witness
circuit whose truth table satisfies `toCNFExt m D`. -/
theorem not_mem_SignatureCircuitSAT_certificateCircuitExt_iff {q r : ℕ} (m : ℕ)
    (D : Circuit Unbounded.extSignature q (3 * (r + 1))) (d : ℕ) (w : List Bool) :
    (⟨q, certificateCircuitExt D d w⟩ ∉
        SignatureCircuitSAT (Unbounded.extInterpretation (modGate m))) ↔
      ∃ W : Circuit Unbounded.extSignature r 1, decodeExtWitness d r w = some W ∧
        (toCNFExt m D).eval
          (fun y => W.eval (Unbounded.extInterpretation (modGate m)) y 0) = true := by
  unfold certificateCircuitExt
  cases h : decodeExtWitness d r w with
  | none =>
    simp [constCircuit_true_mem_SignatureCircuitSAT]
  | some W =>
    simp only [Option.some.injEq, exists_eq_left']
    exact not_mem_SignatureCircuitSAT_badClauseExt_iff m D W

/-- **Certificate-length witness equivalence**: a certificate `w` of exact length `2 * L + 1` makes
`certificateCircuitExt D d w` unsatisfiable iff there is a depth-`≤ d` `ACC⁰[m]` witness circuit
`W` of code length at most `L` whose truth table satisfies `toCNFExt m D`. -/
theorem exists_cert_not_mem_SignatureCircuitSAT_iff {q r : ℕ} (m : ℕ)
    (D : Circuit Unbounded.extSignature q (3 * (r + 1))) (d L : ℕ) :
    (∃ w : List Bool, w.length = 2 * L + 1 ∧
      ⟨q, certificateCircuitExt D d w⟩ ∉
        SignatureCircuitSAT (Unbounded.extInterpretation (modGate m))) ↔
    ∃ W : Circuit Unbounded.extSignature r 1,
      W.depth ≤ d ∧ (Circuit.encCode Unbounded.encExtOp W.code).length ≤ L ∧
      (toCNFExt m D).eval
        (fun y => W.eval (Unbounded.extInterpretation (modGate m)) y 0) = true := by
  constructor
  · rintro ⟨w, hwlen, hunsat⟩
    obtain ⟨W, hdec, hsat⟩ :=
      (not_mem_SignatureCircuitSAT_certificateCircuitExt_iff m D d w).1 hunsat
    obtain ⟨hdepth, hlen⟩ := depth_and_codeLength_of_decodeExtWitness_eq_some hdec
    exact ⟨W, hdepth, by omega, hsat⟩
  · rintro ⟨W, hdepth, hlen, hsat⟩
    set u := Circuit.encCode Unbounded.encExtOp W.code
    set w := frame u ++ List.replicate (2 * L + 1 - (frame u).length) false
    have hflen : (frame u).length ≤ 2 * L + 1 := by rw [length_frame]; omega
    refine ⟨w, ?_, (not_mem_SignatureCircuitSAT_certificateCircuitExt_iff m D d w).2
      ⟨W, decodeExtWitness_frame_append W hdepth _, hsat⟩⟩
    simp only [w, List.length_append, List.length_replicate]
    omega

/-- Raw code builder matching `(badClauseExt D W).code`. -/
private def badClauseExtCode (q r : ℕ)
    (Dcode Wcode : List (Unbounded.ExtOp × List ℕ) × List ℕ) :
    List (Unbounded.ExtOp × List ℕ) × List ℕ :=
  let nMid := 3 * (r + 1)
  let c0 := Circuit.compCode nMid Wcode ([], (List.range r).map fun i => 0 * (r + 1) + i)
  let c1 := Circuit.compCode nMid Wcode ([], (List.range r).map fun i => 1 * (r + 1) + i)
  let c2 := Circuit.compCode nMid Wcode ([], (List.range r).map fun i => 2 * (r + 1) + i)
  let piCode := Circuit.appendCodes nMid [c0, c1, c2]
  let signCode : List (Unbounded.ExtOp × List ℕ) × List ℕ :=
    ([], [0 * (r + 1) + r, 1 * (r + 1) + r, 2 * (r + 1) + r])
  let appCode := Circuit.appendCode nMid piCode signCode
  let midCode := Circuit.compCode nMid violationTestExt.code appCode
  Circuit.compCode q midCode Dcode

private theorem code_badClauseExt {q r : ℕ}
    (D : Circuit Unbounded.extSignature q (3 * (r + 1)))
    (W : Circuit Unbounded.extSignature r 1) :
    (badClauseExt D W).code = badClauseExtCode q r D.code W.code := by
  have haddr (j : Fin 3) :
      (Circuit.wiring Unbounded.extSignature (SuccinctVerifier.addressWire r j)).code =
        ([], (List.range r).map fun i => j.1 * (r + 1) + i) :=
    Circuit.code_wiring_eq_map fun _ => rfl
  have hsign : (Circuit.wiring Unbounded.extSignature (SuccinctVerifier.signWire r)).code =
      ([], [0 * (r + 1) + r, 1 * (r + 1) + r, 2 * (r + 1) + r]) := by
    simp only [Circuit.code_wiring, List.ofFn_succ, List.ofFn_zero, SuccinctVerifier.signWire,
      Fin.val_zero, Fin.succ_zero_eq_one, Fin.val_one, Fin.succ_one_eq_two, Fin.val_two]
  unfold badClauseExt badClauseExtCode
  simp only [Circuit.code_comp, Circuit.code_append, Circuit.code_pi, hsign,
    List.ofFn_succ, List.ofFn_zero, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, haddr,
    Fin.val_zero, Fin.val_one, Fin.val_two]

private theorem validRaw_iff {r : ℕ} (code : List (Unbounded.ExtOp × List ℕ) × List ℕ) :
    (codeCheck Unbounded.extSignature r code.1 && decide (code.2.length = 1) &&
        decide (code.2.getD 0 0 < r + code.1.length)) = true ↔
      (Circuit.ofCode (σ := Unbounded.extSignature) r 1 code).isSome := by
  rw [Circuit.isSome_ofCode_iff, Bool.and_eq_true, Bool.and_eq_true, codeCheck_eq_true_iff]
  rcases code.2 with _ | ⟨a, _ | _⟩ <;> simp

private theorem computableInPolyTime_badClauseExtCode :
    ComputableInPolyTime
      (fun p : (ℕ × ℕ) × ((List (Unbounded.ExtOp × List ℕ) × List ℕ) ×
          (List (Unbounded.ExtOp × List ℕ) × List ℕ)) =>
        badClauseExtCode p.1.1 p.1.2 p.2.1 p.2.2)
      (encPair (encPair encUnary encUnary)
        (encPair (Circuit.encCode Unbounded.encExtOp) (Circuit.encCode Unbounded.encExtOp)))
      (Circuit.encCode Unbounded.encExtOp) := by
  let Code := List (Unbounded.ExtOp × List ℕ) × List ℕ
  let In := (ℕ × ℕ) × (Code × Code)
  let encC := Circuit.encCode Unbounded.encExtOp
  let encIn := encPair (encPair encUnary encUnary) (encPair encC encC)
  have hqBin : ComputableInPolyTime (fun p : In => p.1.1) encIn encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  have hr : ComputableInPolyTime (fun p : In => p.1.2) encIn encUnary := by fun_prop
  have hD : ComputableInPolyTime (fun p : In => p.2.1) encIn encC := by fun_prop
  have hW : ComputableInPolyTime (fun p : In => p.2.2) encIn encC := by fun_prop
  have hnMidBin : ComputableInPolyTime (fun p : In => 3 * (p.1.2 + 1)) encIn encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  have haddr (k : ℕ) : ComputableInPolyTime
      (fun p : In => (([] : List (Unbounded.ExtOp × List ℕ)),
        (List.range p.1.2).map fun i => k * (p.1.2 + 1) + i)) encIn encC :=
    (ComputableInPolyTime.const []).prod <|
      ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp hr)
        (ComputableInPolyTime.unary_to_binary.comp
          (show ComputableInPolyTime (fun q : ((ℕ × ℕ) × (Code × Code)) × ℕ =>
            k * (q.1.1.2 + 1) + q.2) _ _ by fun_prop))
  have hc (k : ℕ) := Circuit.computableInPolyTime_compCode hnMidBin hW (haddr k)
  have hpi := Circuit.computableInPolyTime_appendCodes hnMidBin
    ((hc 0).cons' ((hc 1).cons' ((hc 2).cons' (.const []))))
  have hs (k : ℕ) : ComputableInPolyTime (fun p : In => k * (p.1.2 + 1) + p.1.2) encIn encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  have hsign : ComputableInPolyTime
      (fun p : In => (([] : List (Unbounded.ExtOp × List ℕ)),
        [0 * (p.1.2 + 1) + p.1.2, 1 * (p.1.2 + 1) + p.1.2, 2 * (p.1.2 + 1) + p.1.2]))
      encIn encC :=
    (ComputableInPolyTime.const []).prod ((hs 0).cons' ((hs 1).cons' ((hs 2).cons' (.const []))))
  exact Circuit.computableInPolyTime_compCode hqBin
    (Circuit.computableInPolyTime_compCode hnMidBin (.const violationTestExt.code)
      (Circuit.computableInPolyTime_appendCode hnMidBin hpi hsign)) hD

attribute [local irreducible] ComputableInPolyTime in
/-- Decoding the certificate `w a` into a depth-`≤ d` witness circuit is computable in polynomial
time. -/
theorem computableInPolyTime_decodeExtWitness {α : Type} {enc : α ↪ List Bool}
    {r : α → ℕ} {w : α → List Bool} (hr : ComputableInPolyTime r enc encUnary)
    (hw : ComputableInPolyTime w enc encBits) (d : ℕ) :
    ComputableInPolyTime
      (fun a : α => (decodeExtWitness d (r a) (w a)).map
        fun W => (⟨r a, W⟩ : Σ n, Circuit Unbounded.extSignature n 1))
      enc (encOption (Unbounded.encExtCircuit 1)) := by
  let encC := Circuit.encCode Unbounded.encExtOp
  let encRaw := encPair encUnary encC
  let dec (a : α) := decExtCode.decode (unframe (w a))
  have hrP : ComputableInPolyTime (fun a : α => r a) enc encUnary := hr
  have hu : ComputableInPolyTime (fun a : α => unframe (w a)) enc encBits :=
    Internal.DecoderWords.unframe_degree.computableInPolyTime.comp hw
  have hcode : ComputableInPolyTime dec enc encC := decExtCode.computableInPolyTime.comp hu
  have hcan : ComputableInPolyTime
      (fun a : α => decide (Circuit.encCode Unbounded.encExtOp (dec a) = unframe (w a)))
      enc encBool :=
    ComputableInPolyTime.decide_eq' (hcode.of_enc_eq (encD := encBits) fun _ => rfl) hu
  have hck := Circuits.computableInPolyTime_codeCheck computableInPolyTime_extArity hrP hcode.fst'
  have hlen1 : ComputableInPolyTime (fun a : α => decide ((dec a).2.length = 1)) enc encBool :=
    ComputableInPolyTime.decide_eq'
      ((ComputableInPolyTime.length encNat).comp hcode.snd') (.const 1)
  have hhead0 : ComputableInPolyTime (fun a : α => (dec a).2.getD 0 0) enc encNat :=
    ((ComputableInPolyTime.headD (encA := encNat) (encL := encList encNat) 0).comp
      hcode.snd').of_enc_eq fun a => congrArg encNat <| by
        dsimp only [Function.comp_apply, dec]
        cases (dec a).2 <;> rfl
  have houtLt : ComputableInPolyTime
      (fun a : α => decide ((dec a).2.getD 0 0 < r a + (dec a).1.length)) enc encBool :=
    ComputableInPolyTime.binary_lt' hhead0
      (ComputableInPolyTime.unary_to_binary.comp
        (ComputableInPolyTime.unary_add' hrP
          ((ComputableInPolyTime.length (Circuit.encGate Unbounded.encExtOp)).comp hcode.fst')))
  have hvalid := ComputableInPolyTime.bool_and' hcan
    (ComputableInPolyTime.bool_and' (ComputableInPolyTime.bool_and' hck hlen1) houtLt)
  let rawOpt (a : α) : Option (Σ n, Circuit Unbounded.extSignature n 1) :=
    if Circuit.encCode Unbounded.encExtOp (dec a) = unframe (w a) then
      (Circuit.ofCode (σ := Unbounded.extSignature) (r a) 1 (dec a)).map fun W => ⟨r a, W⟩
    else none
  have hrawOpt : ComputableInPolyTime rawOpt enc (encOption (Unbounded.encExtCircuit 1)) := by
    refine (hvalid.ite ((ComputableInPolyTime.optionSome encRaw).comp (hrP.prod hcode))
      (.const none)).of_enc_eq fun a => ?_
    dsimp only [rawOpt, Function.comp_apply]
    by_cases hcanp : Circuit.encCode Unbounded.encExtOp (dec a) = unframe (w a)
    · have hval : (codeCheck Unbounded.extSignature (r a) (dec a).1 &&
          decide ((dec a).2.length = 1) &&
          decide ((dec a).2.getD 0 0 < r a + (dec a).1.length)) =
          (Circuit.ofCode (σ := Unbounded.extSignature) (r a) 1 (dec a)).isSome :=
        Bool.eq_iff_iff.mpr (validRaw_iff _)
      simp only [hcanp, ↓reduceIte, decide_true, Bool.true_and, hval]
      rcases hof : Circuit.ofCode (σ := Unbounded.extSignature) (r a) 1 (dec a) with _ | W
      · simp
      · simp [Unbounded.encExtCircuit, Circuit.encCircuit_apply,
          Circuit.code_of_ofCode_eq_some hof, encRaw, encC, dec]
    · simp only [hcanp, ↓reduceIte, decide_false, Bool.false_and, Bool.false_eq_true,
        encOption_none]
  let witnessOpt : α → Option (Σ n, Circuit Unbounded.extSignature n 1) :=
    fun a => (decodeExtWitness d (r a) (w a)).map fun W => ⟨r a, W⟩
  have hwitnessOpt : ComputableInPolyTime witnessOpt enc
      (encOption (Unbounded.encExtCircuit 1)) := by
    have hbody : ComputableInPolyTime
        (fun q : α × (Σ n, Circuit Unbounded.extSignature n 1) =>
          if decide (q.2.2.depth ≤ d) then some q.2 else none)
        (encPair enc (Unbounded.encExtCircuit 1)) (encOption (Unbounded.encExtCircuit 1)) :=
      (ComputableInPolyTime.unary_le'
          (computableInPolyTime_extCircuit_depth.comp (ComputableInPolyTime.snd _ _))
          (ComputableInPolyTime.const d)).ite
        ((ComputableInPolyTime.optionSome _).comp (ComputableInPolyTime.snd _ _))
        (ComputableInPolyTime.const none)
    have helim := hrawOpt.optionElimWithInput
      (body := fun _ c => if decide (c.2.depth ≤ d) then some c else none)
      (ComputableInPolyTime.const none) hbody
    refine helim.of_enc_eq fun a => congrArg (encOption (Unbounded.encExtCircuit 1)) ?_
    dsimp only [witnessOpt, rawOpt, decodeExtWitness, dec]
    split_ifs with hcanp
    · cases hof : Circuit.ofCode (σ := Unbounded.extSignature) (r a) 1
          (decExtCode.decode (unframe (w a))) with
      | none => rfl
      | some W =>
        simp only [Option.map_some, Option.elim_some, decide_eq_true_eq]
        split_ifs <;> rfl
    · rfl
  exact hwitnessOpt

/-- The code of the constant-`true` circuit on `q a` inputs is polynomial-time computable. -/
private theorem computableInPolyTime_constTrue_raw {α : Type} {enc : α ↪ List Bool}
    {q : α → ℕ} (hq : ComputableInPolyTime q enc encUnary) :
    ComputableInPolyTime
      (fun a : α => (q a, (Unbounded.constCircuit Unbounded.toExt true : Circuit _ (q a) 1).code))
      enc (encPair encUnary (Circuit.encCode Unbounded.encExtOp)) := by
  have h1 : ComputableInPolyTime
      (fun a : α => (Unbounded.constCircuit Unbounded.toExt true : Circuit _ (q a) 1).code)
      enc (Circuit.encCode Unbounded.encExtOp) := by
    have hcodeConst (k : ℕ) :
        (Unbounded.constCircuit Unbounded.toExt true : Circuit _ k 1).code =
          ([(Unbounded.ExtOp.ac (.and 0), [])], [k]) := rfl
    simp only [hcodeConst]
    exact (ComputableInPolyTime.const [(Unbounded.ExtOp.ac (.and 0), ([] : List ℕ))]).prod
      ((ComputableInPolyTime.unary_to_binary.comp hq).cons' (ComputableInPolyTime.const []))
  exact hq.prod h1

/-- The code of `badClauseExt (D a) W` is polynomial-time computable from `a` and `W`. -/
private theorem computableInPolyTime_badClauseExt_raw {α : Type} {enc : α ↪ List Bool}
    {q r : α → ℕ} (D : (a : α) → Circuit Unbounded.extSignature (q a) (3 * (r a + 1)))
    (hq : ComputableInPolyTime q enc encUnary) (hr : ComputableInPolyTime r enc encUnary)
    (hD : ComputableInPolyTime (fun a => (D a).code) enc (Circuit.encCode Unbounded.encExtOp)) :
    ComputableInPolyTime
      (fun s : α × (Σ n, Circuit Unbounded.extSignature n 1) =>
        (q s.1, badClauseExtCode (q s.1) (r s.1) (D s.1).code s.2.2.code))
      (encPair enc (Unbounded.encExtCircuit 1))
      (encPair encUnary (Circuit.encCode Unbounded.encExtOp)) := by
  have hWcode : ComputableInPolyTime
      (fun s : α × (Σ n, Circuit Unbounded.extSignature n 1) => s.2.2.code)
      (encPair enc (Unbounded.encExtCircuit 1)) (Circuit.encCode Unbounded.encExtOp) :=
    (Circuit.computableInPolyTime_arity_code (σ := Unbounded.extSignature)
      Unbounded.encExtOp 1).snd'.comp (ComputableInPolyTime.snd _ _)
  have hqS := hq.comp (ComputableInPolyTime.fst enc (Unbounded.encExtCircuit 1))
  have hrS := hr.comp (ComputableInPolyTime.fst enc (Unbounded.encExtCircuit 1))
  have hDS := hD.comp (ComputableInPolyTime.fst enc (Unbounded.encExtCircuit 1))
  exact hqS.prod
    (computableInPolyTime_badClauseExtCode.comp ((hqS.prod hrS).prod (hDS.prod hWcode)))

/-- Compiling `a ↦ ⟨q a, certificateCircuitExt (D a) d (w a)⟩` is computable in polynomial time
for a polynomial-time uniform family of decoders `D` and a polynomial-time certificate map `w`. -/
private theorem computableInPolyTime_certificateCircuitExt_of {α : Type} {enc : α ↪ List Bool}
    {q r : α → ℕ}
    (D : (a : α) → Circuit Unbounded.extSignature (q a) (3 * (r a + 1))) {w : α → List Bool}
    (hq : ComputableInPolyTime q enc encUnary)
    (hr : ComputableInPolyTime r enc encUnary)
    (hD : ComputableInPolyTime (fun a => (D a).code) enc (Circuit.encCode Unbounded.encExtOp))
    (hw : ComputableInPolyTime w enc encBits) (d : ℕ) :
    ComputableInPolyTime
      (fun a : α =>
        (⟨q a, certificateCircuitExt (D a) d (w a)⟩ : Σ n, Circuit Unbounded.extSignature n 1))
      enc (Unbounded.encExtCircuit 1) := by
  let witnessOpt : α → Option (Σ n, Circuit Unbounded.extSignature n 1) :=
    fun a => (decodeExtWitness d (r a) (w a)).map fun W => ⟨r a, W⟩
  have hwitnessOpt : ComputableInPolyTime witnessOpt enc
      (encOption (Unbounded.encExtCircuit 1)) :=
    computableInPolyTime_decodeExtWitness hr hw d
  have hconstCode := computableInPolyTime_constTrue_raw hq
  have hbadBody := computableInPolyTime_badClauseExt_raw D hq hr hD
  have hfinal : ComputableInPolyTime
      (fun a : α => (witnessOpt a).elim
        (q a, (Unbounded.constCircuit Unbounded.toExt true : Circuit _ (q a) 1).code)
        (fun c => (q a, badClauseExtCode (q a) (r a) (D a).code c.2.code)))
      enc (encPair encUnary (Circuit.encCode Unbounded.encExtOp)) :=
    ComputableInPolyTime.optionElimWithInput (value := witnessOpt)
      (fallback := fun a : α =>
        (q a, (Unbounded.constCircuit Unbounded.toExt true : Circuit _ (q a) 1).code))
      (body := fun a c => (q a, badClauseExtCode (q a) (r a) (D a).code c.2.code))
      hwitnessOpt hconstCode hbadBody
  refine ComputableInPolyTime.of_enc_eq (encD := Unbounded.encExtCircuit 1)
    (g := fun a : α =>
      (⟨q a, certificateCircuitExt (D a) d (w a)⟩ : Σ n, Circuit Unbounded.extSignature n 1))
    hfinal fun a => ?_
  dsimp only [witnessOpt, certificateCircuitExt]
  cases h : decodeExtWitness d (r a) (w a) with
  | none =>
    simp only [Option.map_none, Option.elim_none, Unbounded.encExtCircuit, Circuit.encCircuit_apply]
  | some W =>
    simp only [Option.map_some, Option.elim_some, Unbounded.encExtCircuit, Circuit.encCircuit_apply,
      code_badClauseExt]

/-- **Native polynomial-time compilation of `certificateCircuitExt`**: given any polynomial-time
uniform family of `ACC⁰` succinct 3-CNF decoders `D` and fixed depth cap `d`, compiling `(x, w)`
to `⟨q x, certificateCircuitExt (D x) d w⟩` is computable in polynomial time. -/
theorem computableInPolyTime_certificateCircuitExt
    {q r : List Bool → ℕ}
    (D : (x : List Bool) → Circuit Unbounded.extSignature (q x) (3 * (r x + 1)))
    (hq : ComputableInPolyTime q encBits encUnary)
    (hr : ComputableInPolyTime r encBits encUnary)
    (hD : ComputableInPolyTime (fun x => (D x).code) encBits (Circuit.encCode Unbounded.encExtOp))
    (d : ℕ) :
    ComputableInPolyTime
      (fun p : List Bool × List Bool =>
        (⟨q p.1, certificateCircuitExt (D p.1) d p.2⟩ : Σ n, Circuit Unbounded.extSignature n 1))
      (encPair encBits encBits) (Unbounded.encExtCircuit 1) := by
  exact computableInPolyTime_certificateCircuitExt_of (fun p : List Bool × List Bool => D p.1)
    (hq.comp (ComputableInPolyTime.fst encBits encBits))
    (hr.comp (ComputableInPolyTime.fst encBits encBits))
    (hD.comp (ComputableInPolyTime.fst encBits encBits)) (ComputableInPolyTime.snd encBits encBits)
    d


end CertDecode

/-! ### 3. Input padding and asymptotic estimates -/

section PadAndAsymptotics

/-- Pad a single-output circuit on `q` inputs with unused dummy inputs up to `N ≥ q`. -/
private def padTo {q : ℕ} (C : Circuit Unbounded.extSignature q 1) (N : ℕ) (h : q ≤ N) :
    Circuit Unbounded.extSignature N 1 :=
  C.comp (Circuit.wiring Unbounded.extSignature (Fin.castLE h))

private theorem depth_padTo_le {q : ℕ} (C : Circuit Unbounded.extSignature q 1) (N : ℕ)
    (h : q ≤ N) : (padTo C N h).depth ≤ C.depth := by
  unfold padTo
  have h := Circuit.depth_comp_le C (Circuit.wiring Unbounded.extSignature (Fin.castLE h))
  simpa only [Circuit.depth_wiring, Nat.add_zero] using h

private theorem padTo_mem_SignatureCircuitSAT_iff {q : ℕ} (m : ℕ)
    (C : Circuit Unbounded.extSignature q 1) (N : ℕ) (h : q ≤ N) :
    (⟨N, padTo C N h⟩ ∈ SignatureCircuitSAT (Unbounded.extInterpretation (modGate m))) ↔
      ⟨q, C⟩ ∈ SignatureCircuitSAT (Unbounded.extInterpretation (modGate m)) := by
  simp only [mem_SignatureCircuitSAT, padTo, Circuit.eval_comp, Circuit.eval_wiring]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨fun i => x (Fin.castLE h i), hx⟩
  · rintro ⟨y, hy⟩
    refine ⟨fun i => if hi : i.1 < q then y ⟨i.1, hi⟩ else false, ?_⟩
    have hfun : (fun i : Fin q =>
        if hi : (Fin.castLE h i).1 < q then y ⟨(Fin.castLE h i).1, hi⟩
        else false) = y := by
      funext i
      simp [i.isLt]
    simpa only [Function.comp_def, hfun] using hy

private theorem code_padTo {q : ℕ} (C : Circuit Unbounded.extSignature q 1) (N : ℕ)
    (h : q ≤ N) : (padTo C N h).code = Circuit.compCode N C.code ([], List.range q) := by
  have hw : (Circuit.wiring Unbounded.extSignature (Fin.castLE h)).code =
      ([], List.range q) := by
    simpa using Circuit.code_wiring_eq_map (σ := Unbounded.extSignature)
      (f := Fin.castLE h) (g := id) fun _ => rfl
  simp only [padTo, Circuit.code_comp, hw]

/-- The binary disjunction gate on two wires. -/
private def orGate : Circuit Unbounded.extSignature 2 1 :=
  Circuit.oneGate (σ := Unbounded.extSignature) (.ac (.or 2)) fun i => i

/-- Disjunction of two single-output circuits on the same inputs. -/
private def orExt {n : ℕ} (A B : Circuit Unbounded.extSignature n 1) :
    Circuit Unbounded.extSignature n 1 :=
  orGate.comp (A.append B)

private theorem depth_orExt_le {n : ℕ} (A B : Circuit Unbounded.extSignature n 1) :
    (orExt A B).depth ≤ max A.depth B.depth + 1 := by
  have h1 := Circuit.depth_comp_le orGate (A.append B)
  have h2 := Circuit.depth_append_le A B
  have h3 : orGate.depth = 1 := Circuit.depth_oneGate _ _
  unfold orExt
  omega

private theorem orExt_mem_SignatureCircuitSAT_iff {n : ℕ} (m : ℕ)
    (A B : Circuit Unbounded.extSignature n 1) :
    (⟨n, orExt A B⟩ ∈ SignatureCircuitSAT (Unbounded.extInterpretation (modGate m))) ↔
      ⟨n, A⟩ ∈ SignatureCircuitSAT (Unbounded.extInterpretation (modGate m)) ∨
        ⟨n, B⟩ ∈ SignatureCircuitSAT (Unbounded.extInterpretation (modGate m)) := by
  simp only [mem_SignatureCircuitSAT, orExt, orGate, Circuit.eval_comp, Circuit.eval_oneGate,
    Circuit.eval_append, Unbounded.extInterpretation_ac, Unbounded.interpretation_or,
    Fin.exists_fin_two, ← exists_or]
  refine exists_congr fun x => ?_
  have h0 : ∀ f g : Fin 1 → Bool, Fin.append f g (0 : Fin (1 + 1)) = f 0 := fun f g => rfl
  have h1 : ∀ f g : Fin 1 → Bool, Fin.append f g (1 : Fin (1 + 1)) = g 0 := fun f g => rfl
  simp only [h0, h1, decide_eq_true_eq]

private theorem code_orExt {n : ℕ} (A B : Circuit Unbounded.extSignature n 1) :
    (orExt A B).code = Circuit.compCode n orGate.code (Circuit.appendCode n A.code B.code) := by
  simp only [orExt, Circuit.code_comp, Circuit.code_append]

/-- The padded disjunction of a check circuit `C₁` on `q₁` inputs and the certificate verifier
`certificateCircuitExt D dW w`, both lifted to `N` inputs. -/
private def checkedCircuit {q₁ q r : ℕ} (C₁ : Circuit Unbounded.extSignature q₁ 1)
    (D : Circuit Unbounded.extSignature q (3 * (r + 1))) (dW : ℕ) (w : List Bool) (N : ℕ)
    (h₁ : q₁ ≤ N) (h₂ : q ≤ N) : Circuit Unbounded.extSignature N 1 :=
  orExt (padTo C₁ N h₁) (padTo (certificateCircuitExt D dW w) N h₂)

private theorem depth_checkedCircuit_le {q₁ q r : ℕ} (C₁ : Circuit Unbounded.extSignature q₁ 1)
    (D : Circuit Unbounded.extSignature q (3 * (r + 1))) (dW : ℕ) (w : List Bool) (N : ℕ)
    (h₁ : q₁ ≤ N) (h₂ : q ≤ N) :
    (checkedCircuit C₁ D dW w N h₁ h₂).depth ≤ max C₁.depth (D.depth + dW + 5) + 1 := by
  have h := depth_orExt_le (padTo C₁ N h₁) (padTo (certificateCircuitExt D dW w) N h₂)
  have h3 := depth_padTo_le C₁ N h₁
  have h4 := depth_padTo_le (certificateCircuitExt D dW w) N h₂
  have h5 := depth_certificateCircuitExt_le D dW w
  unfold checkedCircuit
  omega

private theorem checkedCircuit_not_mem_SignatureCircuitSAT_iff {q₁ q r : ℕ} (m : ℕ)
    (C₁ : Circuit Unbounded.extSignature q₁ 1)
    (D : Circuit Unbounded.extSignature q (3 * (r + 1))) (dW : ℕ) (w : List Bool) (N : ℕ)
    (h₁ : q₁ ≤ N) (h₂ : q ≤ N) :
    (⟨N, checkedCircuit C₁ D dW w N h₁ h₂⟩ ∉
        SignatureCircuitSAT (Unbounded.extInterpretation (modGate m))) ↔
      (⟨q₁, C₁⟩ ∉ SignatureCircuitSAT (Unbounded.extInterpretation (modGate m))) ∧
        ⟨q, certificateCircuitExt D dW w⟩ ∉
          SignatureCircuitSAT (Unbounded.extInterpretation (modGate m)) := by
  simp only [checkedCircuit, orExt_mem_SignatureCircuitSAT_iff, padTo_mem_SignatureCircuitSAT_iff,
    not_or]

private theorem code_checkedCircuit {q₁ q r : ℕ} (C₁ : Circuit Unbounded.extSignature q₁ 1)
    (D : Circuit Unbounded.extSignature q (3 * (r + 1))) (dW : ℕ) (w : List Bool) (N : ℕ)
    (h₁ : q₁ ≤ N) (h₂ : q ≤ N) :
    (checkedCircuit C₁ D dW w N h₁ h₂).code =
      Circuit.compCode N orGate.code
        (Circuit.appendCode N (Circuit.compCode N C₁.code ([], List.range q₁))
          (Circuit.compCode N (certificateCircuitExt D dW w).code ([], List.range q))) := by
  simp only [checkedCircuit, code_orExt, code_padTo]

/-- The maximum of two unary polynomial-time computable quantities. -/
private theorem computableInPolyTime_max_unary {α : Type} {enc : α ↪ List Bool} {f g : α → ℕ}
    (hf : ComputableInPolyTime f enc encUnary) (hg : ComputableInPolyTime g enc encUnary) :
    ComputableInPolyTime (fun a => max (f a) (g a)) enc encUnary :=
  ((ComputableInPolyTime.unary_le' hf hg).ite hg hf).of_enc_eq fun a =>
    congrArg encUnary (by
      simp only [decide_eq_true_eq]
      split_ifs with h
      · rw [Nat.max_eq_right h]
      · rw [Nat.max_eq_left (Nat.le_of_not_ge h)])

/-- The padded checked-decoder circuit for the certificate `p.2 = e ++ w` with `|e| = ℓ p.1`: the
check circuit `C₁ (p.1, e)` and the certificate verifier of the decoder `D (p.1, e)` for the
witness `w`, lifted to `max (max (q₁ p.1) (q p.1)) |p.1|` inputs. -/
private def checkedPad {q₁ q r ℓ : List Bool → ℕ} (dW : ℕ)
    (C₁ : (p : List Bool × List Bool) → Circuit Unbounded.extSignature (q₁ p.1) 1)
    (D : (p : List Bool × List Bool) → Circuit Unbounded.extSignature (q p.1) (3 * (r p.1 + 1)))
    (p : List Bool × List Bool) : Σ n, Circuit Unbounded.extSignature n 1 :=
  ⟨max (max (q₁ p.1) (q p.1)) p.1.length,
    checkedCircuit (C₁ (p.1, p.2.take (ℓ p.1))) (D (p.1, p.2.take (ℓ p.1))) dW
      (p.2.drop (ℓ p.1)) _ ((le_max_left _ _).trans (le_max_left _ _))
      ((le_max_right _ _).trans (le_max_left _ _))⟩

attribute [local irreducible] ComputableInPolyTime in
private theorem computableInPolyTime_checkedPad {q₁ q r ℓ : List Bool → ℕ}
    (C₁ : (p : List Bool × List Bool) → Circuit Unbounded.extSignature (q₁ p.1) 1)
    (D : (p : List Bool × List Bool) → Circuit Unbounded.extSignature (q p.1) (3 * (r p.1 + 1)))
    (hq₁ : ComputableInPolyTime q₁ encBits encUnary) (hq : ComputableInPolyTime q encBits encUnary)
    (hr : ComputableInPolyTime r encBits encUnary) (hℓ : ComputableInPolyTime ℓ encBits encUnary)
    (hC₁ : ComputableInPolyTime (fun p => (C₁ p).code) (encPair encBits encBits)
      (Circuit.encCode Unbounded.encExtOp))
    (hD : ComputableInPolyTime (fun p => (D p).code) (encPair encBits encBits)
      (Circuit.encCode Unbounded.encExtOp)) (dW : ℕ) :
    ComputableInPolyTime (checkedPad (ℓ := ℓ) dW C₁ D) (encPair encBits encBits)
      (Unbounded.encExtCircuit 1) := by
  let encP := encPair encBits encBits
  have hfst : ComputableInPolyTime (fun p : List Bool × List Bool => p.1) encP encBits :=
    ComputableInPolyTime.fst encBits encBits
  have hsnd : ComputableInPolyTime (fun p : List Bool × List Bool => p.2) encP encBits :=
    ComputableInPolyTime.snd encBits encBits
  have hq₁P : ComputableInPolyTime (fun p : List Bool × List Bool => q₁ p.1) encP encUnary :=
    hq₁.comp hfst
  have hqP : ComputableInPolyTime (fun p : List Bool × List Bool => q p.1) encP encUnary :=
    hq.comp hfst
  have hrP : ComputableInPolyTime (fun p : List Bool × List Bool => r p.1) encP encUnary :=
    hr.comp hfst
  have hℓP : ComputableInPolyTime (fun p : List Bool × List Bool => ℓ p.1) encP encUnary :=
    hℓ.comp hfst
  have hlenP : ComputableInPolyTime (fun p : List Bool × List Bool => p.1.length) encP encUnary :=
    ((ComputableInPolyTime.encoding_length encBits).comp hfst).of_enc_eq fun _ => rfl
  have he : ComputableInPolyTime (fun p : List Bool × List Bool => p.2.take (ℓ p.1)) encP
      encBits := ComputableInPolyTime.bitsTakeWithInput hsnd hℓP
  have hwc : ComputableInPolyTime (fun p : List Bool × List Bool => p.2.drop (ℓ p.1)) encP
      encBits := ComputableInPolyTime.bitsDropWithInput hsnd hℓP
  have hpe : ComputableInPolyTime
      (fun p : List Bool × List Bool => (p.1, p.2.take (ℓ p.1))) encP encP := hfst.prod he
  have hC₁c : ComputableInPolyTime
      (fun p : List Bool × List Bool => (C₁ (p.1, p.2.take (ℓ p.1))).code) encP
      (Circuit.encCode Unbounded.encExtOp) := hC₁.comp hpe
  have hDc : ComputableInPolyTime
      (fun p : List Bool × List Bool => (D (p.1, p.2.take (ℓ p.1))).code) encP
      (Circuit.encCode Unbounded.encExtOp) := hD.comp hpe
  have hcert := computableInPolyTime_certificateCircuitExt_of (enc := encP)
    (q := fun p : List Bool × List Bool => q p.1) (r := fun p : List Bool × List Bool => r p.1)
    (fun p : List Bool × List Bool => D (p.1, p.2.take (ℓ p.1))) hqP hrP hDc hwc dW
  have hcertCode : ComputableInPolyTime
      (fun p : List Bool × List Bool =>
        (certificateCircuitExt (D (p.1, p.2.take (ℓ p.1))) dW (p.2.drop (ℓ p.1))).code)
      encP (Circuit.encCode Unbounded.encExtOp) :=
    (Circuit.computableInPolyTime_arity_code (σ := Unbounded.extSignature)
      Unbounded.encExtOp 1).snd'.comp hcert
  have hmax : ComputableInPolyTime
      (fun p : List Bool × List Bool => max (max (q₁ p.1) (q p.1)) p.1.length) encP encUnary :=
    computableInPolyTime_max_unary (computableInPolyTime_max_unary hq₁P hqP) hlenP
  have hmaxBin : ComputableInPolyTime
      (fun p : List Bool × List Bool => max (max (q₁ p.1) (q p.1)) p.1.length) encP encNat :=
    (ComputableInPolyTime.unary_to_binary.comp hmax).of_enc_eq fun _ => rfl
  have hrange (f : List Bool × List Bool → ℕ) (hf : ComputableInPolyTime f encP encUnary) :
      ComputableInPolyTime
        (fun p : List Bool × List Bool => (([] : List (Unbounded.ExtOp × List ℕ)),
          List.range (f p))) encP (Circuit.encCode Unbounded.encExtOp) :=
    (ComputableInPolyTime.const []).prod
      ((ComputableInPolyTime.unary_to_binary.map.comp
        (ComputableInPolyTime.range.comp hf)).of_enc_eq fun p =>
        congrArg (encList encNat) (by simp only [Function.comp_apply, List.map_id']))
  have hc1 := Circuit.computableInPolyTime_compCode hmaxBin hC₁c (hrange _ hq₁P)
  have hc2 := Circuit.computableInPolyTime_compCode hmaxBin hcertCode (hrange _ hqP)
  have happ := Circuit.computableInPolyTime_appendCode hmaxBin hc1 hc2
  have hcode := Circuit.computableInPolyTime_compCode hmaxBin
    (ComputableInPolyTime.const orGate.code) happ
  exact (hmax.prod hcode).of_enc_eq fun p => by
    rw [Unbounded.encExtCircuit, Circuit.encCircuit_apply, checkedPad, code_checkedCircuit]

private theorem nthRoot_le_rpow_real {r_w : ℕ} (hr : 0 < r_w) (n : ℕ) :
    (Nat.nthRoot r_w n : ℝ) ≤ (n : ℝ) ^ ((r_w : ℝ)⁻¹) := by
  have hpow : (Nat.nthRoot r_w n : ℝ) ^ r_w ≤ (n : ℝ) := by
    exact_mod_cast Nat.pow_nthRoot_le (n := r_w) (a := n) (Or.inl hr.ne')
  calc (Nat.nthRoot r_w n : ℝ)
      = ((Nat.nthRoot r_w n : ℝ) ^ r_w) ^ ((r_w : ℝ)⁻¹) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _),
          mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hr.ne'), Real.rpow_one]
    _ ≤ (n : ℝ) ^ ((r_w : ℝ)⁻¹) :=
        Real.rpow_le_rpow (pow_nonneg (Nat.cast_nonneg _) _) hpow (by positivity)

/-- For any real exponents `a < b` and real constant `c`, `c * n ^ a ≤ n ^ b` eventually. -/
private theorem eventually_mul_rpow_le_rpow {a b : ℝ} (hab : a < b) (c : ℝ) :
    ∀ᶠ n : ℕ in atTop, c * (n : ℝ) ^ a ≤ (n : ℝ) ^ b := by
  have ht := (tendsto_rpow_atTop (sub_pos.mpr hab)).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_ge_atTop c, eventually_ge_atTop 1] with n hn h1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  calc c * (n : ℝ) ^ a
      ≤ (n : ℝ) ^ (b - a) * (n : ℝ) ^ a :=
        mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg hn0.le a)
    _ = (n : ℝ) ^ b := by rw [← Real.rpow_add hn0, sub_add_cancel]

/-- For `(r_w : ℝ)⁻¹ < ε`, any `C * (n + 1) ^ d * 2 ^ (d * Nat.nthRoot r_w n)` is eventually
bounded by `2 ^ (n ^ ε)`. -/
private theorem eventually_poly_mul_two_pow_nthRoot_le {r_w : ℕ} (hr : 0 < r_w) {ε : ℝ}
    (hlt : (r_w : ℝ)⁻¹ < ε) (C d : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ((C * (n + 1) ^ d * 2 ^ (d * Nat.nthRoot r_w n) : ℕ) : ℝ) ≤
        (2 : ℝ) ^ ((n : ℝ) ^ ε) := by
  have hε : 0 < ε := lt_trans (by positivity) hlt
  have hlog := Nat.eventually_mul_log_add_pow_le_rpow (b := 2) Nat.one_lt_two 1 1 1
    (K := (2 * (C.size + d + 1) : ℝ)) (by positivity) hε
  have hbound := eventually_mul_rpow_le_rpow hlt (2 * ((d : ℝ) + 1))
  filter_upwards [hlog, hbound] with n hln hsn
  have hnat : C * (n + 1) ^ d * 2 ^ (d * Nat.nthRoot r_w n) ≤
      2 ^ (C.size + d * (Nat.log 2 (n + 1) + 1) + d * Nat.nthRoot r_w n) := by
    rw [pow_add _ (C.size + _)]
    exact Nat.mul_le_mul_right _ (Nat.mul_pow_succ_le_two_pow C d n)
  have hcast : ((C * (n + 1) ^ d * 2 ^ (d * Nat.nthRoot r_w n) : ℕ) : ℝ) ≤
      (2 : ℝ) ^ (((C.size + d * (Nat.log 2 (n + 1) + 1) + d * Nat.nthRoot r_w n : ℕ) : ℝ)) := by
    rw [Real.rpow_natCast]
    exact_mod_cast hnat
  refine hcast.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
  rw [pow_one] at hln
  push_cast at hln ⊢
  have hlog_nn : (0 : ℝ) ≤ Nat.log 2 (n + 1) := Nat.cast_nonneg _
  have hnr_nn : (0 : ℝ) ≤ Nat.nthRoot r_w n := Nat.cast_nonneg _
  have hmul : 2 * ((d : ℝ) + 1) * (Nat.nthRoot r_w n : ℝ) ≤ (n : ℝ) ^ ε :=
    (mul_le_mul_of_nonneg_left (nthRoot_le_rpow_real hr n) (by positivity)).trans hsn
  have hCsz : (C.size : ℝ) ≤ (C.size : ℝ) * ((Nat.log 2 (n + 1) : ℝ) + 1) :=
    le_mul_of_one_le_right (Nat.cast_nonneg _) (by linarith)
  nlinarith

/-- For `0 < ε < δ < 1`, `0 < c₀`, and `c : ℕ`, eventually:
(a) `(n : ℝ) ^ ε ≤ (n : ℝ) - (c₀ / 2) * (n : ℝ) ^ δ`,
(b) `c * (log₂(n + 2) + 1) ≤ (c₀ / 2) * (n : ℝ) ^ δ`, and
(c) `1 ≤ (2 : ℝ) ^ ((n : ℝ) - (c₀ / 2) * (n : ℝ) ^ δ)`. -/
private theorem eventually_subexp_envelope {ε δ c₀ : ℝ} (hε : 0 < ε) (hεδ : ε < δ) (hδ1 : δ < 1)
    (hc₀ : 0 < c₀) (c : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ ε ≤ (n : ℝ) - (c₀ / 2) * (n : ℝ) ^ δ ∧
      (c : ℝ) * ((Nat.log 2 (n + 2) : ℝ) + 1) ≤ (c₀ / 2) * (n : ℝ) ^ δ ∧
      (1 : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) - (c₀ / 2) * (n : ℝ) ^ δ) := by
  have hδ : 0 < δ := lt_trans hε hεδ
  have hlog := Nat.eventually_mul_log_add_pow_le_rpow (b := 2) Nat.one_lt_two 2 1 1
    (K := (2 * ((c : ℝ) + 1)) / c₀) (by positivity) hδ
  have hs1 := eventually_mul_rpow_le_rpow (lt_trans hεδ hδ1) (2 : ℝ)
  have hs2 := eventually_mul_rpow_le_rpow hδ1 (c₀ + 1)
  filter_upwards [hlog, hs1, hs2] with n hln h1 h2
  rw [Real.rpow_one] at h1 h2
  have hc0le : (c₀ / 2) * (n : ℝ) ^ δ ≤ (1 / 2 : ℝ) * (n : ℝ) := by
    have hnn : (0 : ℝ) ≤ (n : ℝ) ^ δ := Real.rpow_nonneg (Nat.cast_nonneg _) _
    nlinarith
  have hpart1 : (n : ℝ) ^ ε ≤ (n : ℝ) - (c₀ / 2) * (n : ℝ) ^ δ := by linarith
  have hpart2 : (c : ℝ) * ((Nat.log 2 (n + 2) : ℝ) + 1) ≤ (c₀ / 2) * (n : ℝ) ^ δ := by
    rw [pow_one] at hln
    have hmul := mul_le_mul_of_nonneg_left hln (show (0 : ℝ) ≤ c₀ / 2 by positivity)
    have hcancel : (c₀ / 2) * (2 * ((c : ℝ) + 1) / c₀) = (c : ℝ) + 1 := by
      field_simp
    rw [← mul_assoc, hcancel] at hmul
    have hnn : (0 : ℝ) ≤ (Nat.log 2 (n + 2) : ℝ) + 1 := by positivity
    nlinarith
  have hpart3 : (1 : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) - (c₀ / 2) * (n : ℝ) ^ δ) :=
    Real.one_le_rpow (by norm_num) (by linarith [Real.rpow_nonneg (Nat.cast_nonneg n) ε])
  exact ⟨hpart1, hpart2, hpart3⟩

end PadAndAsymptotics

/-! ### 4. Unconditional `NTIME` simulation and hard-witness transfer -/

section WitnessTransfer

/-- **Small-`ACC⁰`-witness language** of a succinct 3-CNF family `D`: the set of inputs `x` whose
represented 3-CNF `toCNFExt m (D x)` has a satisfying assignment computable by an `ACC⁰[m]` circuit
of depth at most `dW` and canonical code length at most `L x`. -/
@[expose] def smallACC0WitnessLanguage (m dW : ℕ) {q r : List Bool → ℕ}
    (D : (x : List Bool) → Circuit Unbounded.extSignature (q x) (3 * (r x + 1)))
    (L : List Bool → ℕ) : Set (List Bool) :=
  {x | ∃ W : Circuit Unbounded.extSignature (r x) 1,
    W.depth ≤ dW ∧ (Circuit.encCode Unbounded.encExtOp W.code).length ≤ L x ∧
    (toCNFExt m (D x)).eval
      (fun y => W.eval (Unbounded.extInterpretation (modGate m)) y 0) = true}

/-- The unary witness-budget length `2 * 2 ^ Nat.nthRoot r_w |x| + 1` is computable with time
at most `C * (|x| + 1) ^ d * 2 ^ (d * Nat.nthRoot r_w |x|)`. -/
private theorem exists_computableInO_witnessLength {r_w : ℕ} (hr : 0 < r_w) :
    ∃ (T S : List Bool → ℕ) (C d : ℕ),
      ComputableInO (fun x : List Bool => 2 * 2 ^ Nat.nthRoot r_w x.length + 1)
        encBits encUnary T S ∧
      ∀ x : List Bool, T x ≤ C * (x.length + 1) ^ d * 2 ^ (d * Nat.nthRoot r_w x.length) := by
  have hnr_self (k : ℕ) : Nat.nthRoot r_w k ≤ k :=
    (Nat.le_self_pow hr.ne' _).trans (Nat.pow_nthRoot_le (n := r_w) (a := k) (Or.inl hr.ne'))
  have hroot : ComputableInPolyTime (fun x : List Bool => Nat.nthRoot r_w x.length)
      encBits encUnary := by
    have hlen_bits : ComputableInPolyTime (fun x : List Bool => x.length) encBits encUnary := by
      fun_prop
    have hbin := ComputableInPolyTime.binary_nthRoot'
      (ComputableInPolyTime.const (encIn := encBits) r_w)
      (ComputableInPolyTime.unary_to_binary.comp hlen_bits)
    exact ComputableInPolyTime.binary_to_unary_bounded hbin hlen_bits
      (fun x => hnr_self x.length)
  obtain ⟨Tr, Sr, hTr, hSr, hrootO⟩ := hroot.exists_computableInO
  obtain ⟨Cr, dr, hTr_le⟩ := hTr.exists_le
  have hpowO := ComputableInO.unary_two_pow.comp hrootO
  have h2p1_poly : ComputableInPolyTime (fun k : ℕ => 2 * k + 1) encUnary encUnary := by fun_prop
  obtain ⟨Tm, Sm, hTm, hSm, hmO⟩ := h2p1_poly.exists_computableInO
  obtain ⟨Cm, dm, hTm_le⟩ := hTm.exists_le
  have hℓO : ComputableInO (fun x : List Bool => 2 * 2 ^ Nat.nthRoot r_w x.length + 1)
      encBits encUnary _ _ := hmO.comp hpowO
  refine ⟨_, _, Cr + 1 + Cm * 2 ^ dm, dr + dm + 1, hℓO, fun x => ?_⟩
  set n := x.length with hn
  set P := 2 ^ Nat.nthRoot r_w n with hP
  have hP1 : 1 ≤ P := Nat.one_le_two_pow
  set E := (n + 1) ^ (dr + dm + 1) * 2 ^ ((dr + dm + 1) * Nat.nthRoot r_w n) with hE
  have hn1 : n + 1 ≤ (n + 1) ^ (dr + dm + 1) := Nat.le_self_pow (by omega) _
  have h2P : P ≤ 2 ^ ((dr + dm + 1) * Nat.nthRoot r_w n) := by
    rw [hP]
    exact Nat.pow_le_pow_right Nat.one_lt_two.le (Nat.le_mul_of_pos_left _ (by omega))
  have h2one : 1 ≤ 2 ^ ((dr + dm + 1) * Nat.nthRoot r_w n) := Nat.one_le_two_pow
  have hTr_b : Tr x ≤ Cr * E := by
    have h1 : (n + 1) ^ dr ≤ E :=
      (Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)).trans (Nat.le_mul_of_pos_right _ h2one)
    have := hTr_le x
    simp only [encBits_apply, ← hn] at this
    exact this.trans (Nat.mul_le_mul_left Cr h1)
  have hExp_b : (Nat.nthRoot r_w n + 1) * P ≤ E :=
    Nat.mul_le_mul ((Nat.add_le_add_right (hnr_self n) 1).trans hn1) h2P
  have hTm_b : Tm P ≤ Cm * 2 ^ dm * E := by
    have h1 := hTm_le P
    simp only [encUnary_apply, List.length_replicate] at h1
    have hP2 : (P + 1) ^ dm ≤ 2 ^ dm * P ^ dm := by
      rw [← Nat.mul_pow]
      exact Nat.pow_le_pow_left (by omega) dm
    have h3 : P ^ dm ≤ E := by
      have h4 : P ^ dm ≤ 2 ^ ((dr + dm + 1) * Nat.nthRoot r_w n) := by
        rw [hP, ← pow_mul]
        exact Nat.pow_le_pow_right Nat.one_lt_two.le (by
          rw [Nat.mul_comm (Nat.nthRoot r_w n) dm]
          exact Nat.mul_le_mul_right _ (by omega))
      exact h4.trans (Nat.le_mul_of_pos_left _ (Nat.pow_pos (Nat.succ_pos n)))
    calc Tm P ≤ Cm * (P + 1) ^ dm := h1
      _ ≤ Cm * (2 ^ dm * P ^ dm) := Nat.mul_le_mul_left Cm hP2
      _ = Cm * 2 ^ dm * P ^ dm := by ring
      _ ≤ Cm * 2 ^ dm * E := Nat.mul_le_mul_left _ h3
  have heq : (Cr + 1 + Cm * 2 ^ dm) * E = Cr * E + E + Cm * 2 ^ dm * E := by ring
  have hfin : (Cr + 1 + Cm * 2 ^ dm) * (n + 1) ^ (dr + dm + 1) *
      2 ^ ((dr + dm + 1) * Nat.nthRoot r_w n) = (Cr + 1 + Cm * 2 ^ dm) * E := by
    rw [hE, Nat.mul_assoc]
  omega

/-- **Shared `NTIME` simulation of padded unsatisfiability checks.** Suppose a language `L` is
the set of `x` for which some certificate `w` of length `ℓ x` makes the padded `ACC⁰[m]` circuit
`g (x, w)` of depth at most `d0` unsatisfiable, where `g` is polynomial-time computable, the input
count of `g (x, w)` is quasilinear, and the certificate length, the encoding size and the time to
compute `ℓ` are bounded by `a * (|x| + 1) ^ a * 2 ^ (a * Nat.nthRoot r_w |x|)`. Then `L` is in
`NTIME(⌊2 ^ (n - c₀ * n ^ δ)⌋₊)`, for `r_w`, `δ`, `c₀` depending only on `d0` and `m`. -/
private theorem exists_ntime_of_padded_unsat (d0 : ℕ) {m : ℕ} (hm : 0 < m) :
    ∃ (r_w : ℕ) (δ c₀ : ℝ), 0 < r_w ∧ 0 < δ ∧ δ < 1 ∧ 0 < c₀ ∧
      ∀ {ℓ Sℓ : List Bool → ℕ}
        (g : List Bool × List Bool → Σ n, Circuit Unbounded.extSignature n 1)
        (L : Set (List Bool)) (a c : ℕ), 0 < a →
        ComputableInO ℓ encBits encUnary
          (fun x => a * ((x.length + 1) ^ a * 2 ^ (a * Nat.nthRoot r_w x.length))) Sℓ →
        ComputableInPolyTime g (encPair encBits encBits) (Unbounded.encExtCircuit 1) →
        (∀ x w, w.length = ℓ x → (encPair encBits encBits (x, w)).length + 1 ≤
          a * ((x.length + 1) ^ a * 2 ^ (a * Nat.nthRoot r_w x.length))) →
        (∀ x w, (g (x, w)).2.depth ≤ d0) →
        (∀ x w, x.length ≤ (g (x, w)).1) →
        (∀ x w, (g (x, w)).1 ≤ x.length + c * Nat.log 2 (x.length + 2) + c) →
        (∀ x, x ∈ L ↔ ∃ w : List Bool, w.length = ℓ x ∧
          g (x, w) ∉ SignatureCircuitSAT (Unbounded.extInterpretation (modGate m))) →
        L ∈ NTIME encBits fun n => ⌊(2 : ℝ) ^ ((n : ℝ) - c₀ * (n : ℝ) ^ δ)⌋₊ := by
  classical
  obtain ⟨ε, δ, c₀, hε, hεδ, hδ1, hc₀, decideSAT, T_sat, hSAT_O, hSAT_corr, M_sat, hSAT_time⟩ :=
    exists_acc0SAT_decider d0 hm
  set r_w : ℕ := Nat.ceil (2 / ε) + 1
  have hrw_pos : 0 < r_w := Nat.succ_pos _
  have hrw_lt : (r_w : ℝ)⁻¹ < ε := by
    rw [inv_lt_comm₀ (by positivity) hε]
    have : 2 / ε ≤ (Nat.ceil (2 / ε) : ℝ) := Nat.le_ceil _
    have : 1 / ε < 2 / ε := by
      gcongr
      norm_num
    dsimp only [r_w]
    push_cast
    linarith [one_div ε]
  refine ⟨r_w, δ, c₀ / 2, hrw_pos, lt_trans hε hεδ, hδ1, by positivity, ?_⟩
  intro ℓ Sℓ g L a c ha hℓO₀ hg_poly hpair₀ hdepth hn_le hq_le hL
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℕ → ℕ, ∀ n, Φ n = (n + 1) ^ a * 2 ^ (a * Nat.nthRoot r_w n) :=
    ⟨_, fun _ => rfl⟩
  have hℓO : ComputableInO ℓ encBits encUnary (fun x => a * Φ x.length) Sℓ := by
    simpa only [hΦ] using hℓO₀
  have hpair : ∀ x w, w.length = ℓ x →
      (encPair encBits encBits (x, w)).length + 1 ≤ a * Φ x.length := fun x w hw => by
    rw [hΦ]; exact hpair₀ x w hw
  obtain ⟨Tc, Sc, hTc, hSc, hpadO⟩ := hg_poly.exists_computableInO
  obtain ⟨_, d_out, hdeg⟩ := hg_poly.exists_degree
  obtain ⟨C_out, hC_out⟩ := hdeg.2
  obtain ⟨Ct, dt, hTc_le⟩ := hTc.exists_le
  have hΦ1 (n : ℕ) : 1 ≤ Φ n := by
    rw [hΦ]; exact Nat.mul_pos (Nat.pow_pos (Nat.succ_pos _)) (Nat.pow_pos (by norm_num))
  have hΦpow (n k : ℕ) :
      Φ n ^ k = (n + 1) ^ (a * k) * 2 ^ ((a * k) * Nat.nthRoot r_w n) := by
    rw [hΦ, mul_pow, ← pow_mul, ← pow_mul, Nat.mul_right_comm a (Nat.nthRoot r_w n) k]
  have hnΦ (n : ℕ) : n ≤ Φ n := by
    rw [hΦ]
    exact (Nat.le_succ n).trans ((Nat.le_self_pow ha.ne' _).trans
      (Nat.le_mul_of_pos_right _ (Nat.pow_pos (by norm_num))))
  -- 2. Asymptotic threshold `M₀` where `|enc (g (x, w))| ≤ 2 ^ (n ^ ε)`
  let C_enc : ℕ := C_out * a ^ d_out
  have henc_ev := eventually_poly_mul_two_pow_nthRoot_le hrw_pos hrw_lt C_enc (a * d_out)
  obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.mp henc_ev
  have hpad_len_bound (x w : List Bool) (hw : w.length = ℓ x) :
      (Unbounded.encExtCircuit 1 (g (x, w))).length ≤
        C_enc * (x.length + 1) ^ (a * d_out) *
          2 ^ ((a * d_out) * Nat.nthRoot r_w x.length) := by
    calc (Unbounded.encExtCircuit 1 (g (x, w))).length
        ≤ C_out * ((encPair encBits encBits (x, w)).length + 1) ^ d_out := hC_out (x, w)
      _ ≤ C_out * (a * Φ x.length) ^ d_out :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (hpair x w hw) d_out)
      _ = C_enc * Φ x.length ^ d_out := by simp only [C_enc, Nat.mul_pow, Nat.mul_assoc]
      _ = _ := by rw [hΦpow, ← Nat.mul_assoc]
  have hpad_guarded (x w : List Bool) (hx : M₀ ≤ x.length) (hw : w.length = ℓ x) :
      (g (x, w)).2.depth ≤ d0 ∧
        ((Unbounded.encExtCircuit 1 (g (x, w))).length : ℝ) ≤
          (2 : ℝ) ^ (((g (x, w)).1 : ℝ) ^ ε) := by
    refine ⟨hdepth x w, ?_⟩
    have h1 : ((Unbounded.encExtCircuit 1 (g (x, w))).length : ℝ) ≤
        ((C_enc * (x.length + 1) ^ (a * d_out) *
          2 ^ ((a * d_out) * Nat.nthRoot r_w x.length) : ℕ) : ℝ) := by
      exact_mod_cast hpad_len_bound x w hw
    have h2 := hM₀ x.length hx
    have h3 : (2 : ℝ) ^ ((x.length : ℝ) ^ ε) ≤ (2 : ℝ) ^ (((g (x, w)).1 : ℝ) ^ ε) := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      refine Real.rpow_le_rpow (Nat.cast_nonneg _) ?_ hε.le
      exact_mod_cast hn_le x w
    exact (h1.trans h2).trans h3
  -- 3. Finite lookup table for `x.length < M₀`, and verifier `V`
  let S_fin : List (List Bool) :=
    ((List.range M₀).flatMap BitString.enumList).filter fun x => decide (x ∈ L)
  have hS_fin (x : List Bool) (hx : x.length < M₀) : x ∈ S_fin ↔ x ∈ L := by
    simp only [S_fin, List.mem_filter, List.mem_flatMap, List.mem_range, BitString.mem_enumList,
      decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨⟨x.length, hx, rfl⟩, h⟩⟩
  let V : List Bool × List Bool → Bool := fun p =>
    if p.1.length < M₀ then decide (p.1 ∈ S_fin) else !decideSAT (g p)
  have hguard_poly : ComputableInPolyTime
      (fun p : List Bool × List Bool => decide (p.1.length < M₀))
      (encPair encBits encBits) encBool := by fun_prop
  obtain ⟨Tg, Sg, hTg, hSg, hguardO⟩ := hguard_poly.exists_computableInO
  obtain ⟨Cg, dg, hTg_le⟩ := hTg.exists_le
  have hfin_poly : ComputableInPolyTime (fun p : List Bool × List Bool => decide (p.1 ∈ S_fin))
      (encPair encBits encBits) encBool :=
    ComputableInPolyTime.decide_mem (ComputableInPolyTime.const S_fin)
      (ComputableInPolyTime.fst encBits encBits)
  obtain ⟨Tf, Sf, hTf, hSf, hfinO⟩ := hfin_poly.exists_computableInO
  obtain ⟨Cf, df, hTf_le⟩ := hTf.exists_le
  have hnotSAT : ComputableInO (fun p : List Bool × List Bool => !decideSAT (g p))
      (encPair encBits encBits) encBool _ _ :=
    (ComputableInDegree.of_finite (encIn := encBool) (encMid := encBool)
      fun b : Bool => !b).inO_one.comp (hSAT_O.comp hpadO)
  have hVO := (hguardO.ite hfinO hnotSAT).of_enc_eq (g := V) fun p => congrArg encBool (by
    simp only [V, decide_eq_true_eq])
  -- 4. Exactness of the verifier language
  have hlang : {x | ∃ w : List Bool, w.length = ℓ x ∧ V (x, w) = true} = L := by
    ext x
    simp only [Set.mem_ofPred_eq]
    by_cases hx : x.length < M₀
    · simp only [V, hx, ↓reduceIte, decide_eq_true_eq, hS_fin x hx]
      exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨List.replicate (ℓ x) false, by simp, h⟩⟩
    · have hxge : M₀ ≤ x.length := Nat.le_of_not_lt hx
      simp only [V, hx, ↓reduceIte, Bool.not_eq_true']
      rw [hL x]
      constructor
      · rintro ⟨w, hw, hsatf⟩
        obtain ⟨hd, hl⟩ := hpad_guarded x w hxge hw
        refine ⟨w, hw, ?_⟩
        rw [← hSAT_corr _ hd hl, hsatf]; decide
      · rintro ⟨w, hw, hnot⟩
        obtain ⟨hd, hl⟩ := hpad_guarded x w hxge hw
        refine ⟨w, hw, ?_⟩
        cases hb : decideSAT (g (x, w))
        · rfl
        · exact absurd ((hSAT_corr _ hd hl).1 hb) hnot
  -- 5. Uniform time envelope for `setOf_exists_mem_NTIME`
  let D_all : ℕ := dg + df + dt + 1
  let C_poly : ℕ := a + 1 + Cg * a ^ dg + Cf * a ^ df + Ct * a ^ dt + 2
  have hev_poly := eventually_poly_mul_two_pow_nthRoot_le hrw_pos hrw_lt C_poly (a * D_all)
  have hev_env := eventually_subexp_envelope hε hεδ hδ1 hc₀ c
  obtain ⟨M₁, hM₁⟩ := Filter.eventually_atTop.mp (hev_poly.and hev_env)
  set M_cut := max M₀ M₁
  let tBound : ℕ → ℕ := fun n => ⌊(2 : ℝ) ^ ((n : ℝ) - (c₀ / 2) * (n : ℝ) ^ δ)⌋₊
  let polyEnv : ℕ → ℕ := fun n =>
    C_poly * (n + 1) ^ (a * D_all) * 2 ^ ((a * D_all) * Nat.nthRoot r_w n)
  let satEnv : ℕ → ℕ := fun n =>
    (M_sat + 1) * 2 ^ (n + c * Nat.log 2 (n + 2) + c) + M_sat + 1
  let B_fin : ℕ := (Finset.range M_cut).sup fun n => polyEnv n + satEnv n + 4
  let C_total : ℕ := max (2 * M_sat + 4) (B_fin + M_sat + 4)
  change L ∈ NTIME encBits tBound
  rw [← hlang]
  refine setOf_exists_mem_NTIME hℓO hVO (C := C_total) fun x w hw => ?_
  set n := x.length with hn
  have hpair' := hpair x w hw
  rw [← hn] at hpair'
  have hΦ1' := hΦ1 n
  have hnΦ' := hnΦ n
  have hΦX : Φ n ≤ Φ n ^ D_all := Nat.le_self_pow (by dsimp only [D_all]; omega) _
  have hX1 : 1 ≤ Φ n ^ D_all := hΦ1'.trans hΦX
  have hPairPow (k : ℕ) (hk : k ≤ D_all) :
      ((encPair encBits encBits (x, w)).length + 1) ^ k ≤ a ^ k * Φ n ^ D_all :=
    calc ((encPair encBits encBits (x, w)).length + 1) ^ k ≤ (a * Φ n) ^ k :=
          Nat.pow_le_pow_left hpair' k
      _ = a ^ k * Φ n ^ k := Nat.mul_pow _ _ _
      _ ≤ a ^ k * Φ n ^ D_all := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hΦ1' hk)
  have hPairB {T : List Bool × List Bool → ℕ} {C d : ℕ}
      (hT : ∀ p, T p ≤ C * ((encPair encBits encBits p).length + 1) ^ d) (hd : d ≤ D_all) :
      T (x, w) ≤ C * a ^ d * Φ n ^ D_all := by
    rw [Nat.mul_assoc]
    exact (hT (x, w)).trans (Nat.mul_le_mul_left C (hPairPow d hd))
  have hTg_b := hPairB hTg_le (by dsimp only [D_all]; omega)
  have hTf_b := hPairB hTf_le (by dsimp only [D_all]; omega)
  have hTc_b := hPairB hTc_le (by dsimp only [D_all]; omega)
  have hpolyEnv : polyEnv n = C_poly * Φ n ^ D_all := by
    simp only [polyEnv]; rw [hΦpow, Nat.mul_assoc]
  have hpoly_sum : n + a * Φ n + (Tg (x, w) + max (Tf (x, w)) (Tc (x, w) + 2)) ≤ polyEnv n := by
    have hmax_le : max (Tf (x, w)) (Tc (x, w) + 2) ≤ Tf (x, w) + Tc (x, w) + 2 := by omega
    have haX : a * Φ n ≤ a * Φ n ^ D_all := Nat.mul_le_mul_left a hΦX
    have heq : C_poly * Φ n ^ D_all = a * Φ n ^ D_all + Φ n ^ D_all + Cg * a ^ dg * Φ n ^ D_all +
        Cf * a ^ df * Φ n ^ D_all + Ct * a ^ dt * Φ n ^ D_all + 2 * Φ n ^ D_all := by
      simp only [C_poly]; ring
    rw [hpolyEnv, heq]
    omega
  -- Split on `n < M_cut` vs `M_cut ≤ n`
  simp only [encBits_apply, encBool_apply, List.length_singleton]
  rw [← hn]
  by_cases hsmall : n < M_cut
  · -- Small `n < M_cut`: either `n < M₀` (finite lookup) or `M₀ ≤ n < M_cut` (guarded SAT)
    have hB : polyEnv n + satEnv n + 4 ≤ B_fin :=
      Finset.le_sup (f := fun k => polyEnv k + satEnv k + 4) (Finset.mem_range.mpr hsmall)
    by_cases hlt0 : n < M₀
    · simp only [hlt0, decide_true, ↓reduceIte]
      have hCge : B_fin ≤ C_total := by dsimp only [C_total]; omega
      omega
    · simp only [hlt0, decide_false, Bool.false_eq_true, ↓reduceIte]
      have hge0 : M₀ ≤ n := Nat.le_of_not_lt hlt0
      obtain ⟨hd, hl⟩ := hpad_guarded x w hge0 hw
      have hsatR := hSAT_time (g (x, w)) hd hl
      have hq'le : ((g (x, w)).1 : ℝ) ≤ ((n + c * Nat.log 2 (n + 2) + c : ℕ) : ℝ) :=
        mod_cast hq_le x w
      have hpowR : (2 : ℝ) ^ (((g (x, w)).1 : ℝ) - c₀ * ((g (x, w)).1 : ℝ) ^ δ) ≤
          (2 : ℝ) ^ (n + c * Nat.log 2 (n + 2) + c) := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (by
            have hnn := mul_nonneg hc₀.le (Real.rpow_nonneg (Nat.cast_nonneg (g (x, w)).1) δ)
            linarith)
      have hTsat_nat : T_sat (g (x, w)) ≤ satEnv n := mod_cast
        (by
          have hmul := mul_le_mul_of_nonneg_left hpowR (Nat.cast_nonneg (α := ℝ) M_sat)
          dsimp only [satEnv]
          push_cast
          linarith [show (0 : ℝ) ≤ (2 : ℝ) ^ (n + c * Nat.log 2 (n + 2) + c) by positivity] :
          (T_sat (g (x, w)) : ℝ) ≤ (satEnv n : ℝ))
      have hCge : B_fin ≤ C_total := by dsimp only [C_total]; omega
      omega
  · -- Large `n ≥ M_cut`: both `M₀ ≤ n` and `M₁ ≤ n` hold!
    have hge_cut : M_cut ≤ n := Nat.le_of_not_lt hsmall
    have hge0 : M₀ ≤ n := (le_max_left M₀ M₁).trans hge_cut
    have hge1 : M₁ ≤ n := (le_max_right M₀ M₁).trans hge_cut
    have hnotlt0 : ¬ n < M₀ := by omega
    simp only [hnotlt0, decide_false, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨hpolyR, hε_le, hlog_le, htarget_ge1⟩ := hM₁ n hge1
    set target : ℝ := (2 : ℝ) ^ ((n : ℝ) - (c₀ / 2) * (n : ℝ) ^ δ)
    have htarget_le_floor : target ≤ 2 * (tBound n : ℝ) := by
      have hlt : target < (tBound n : ℝ) + 1 := Nat.lt_floor_add_one target
      have h1nat : 1 ≤ tBound n :=
        Nat.le_floor (by simpa only [Nat.cast_one] using htarget_ge1)
      have h1 : (1 : ℝ) ≤ (tBound n : ℝ) := by exact_mod_cast h1nat
      linarith
    have hpoly_le_target : (polyEnv n : ℝ) ≤ target :=
      hpolyR.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) hε_le)
    obtain ⟨hd, hl⟩ := hpad_guarded x w hge0 hw
    have hsatR := hSAT_time (g (x, w)) hd hl
    have hq'_ge : n ≤ (g (x, w)).1 := hn_le x w
    have hq'_le : (g (x, w)).1 ≤ n + c * Nat.log 2 (n + 2) + c :=
      hq_le x w
    have hexp_sat : ((g (x, w)).1 : ℝ) - c₀ * ((g (x, w)).1 : ℝ) ^ δ ≤
        (n : ℝ) - (c₀ / 2) * (n : ℝ) ^ δ := by
      have h1 : ((g (x, w)).1 : ℝ) ≤ (n : ℝ) + (c : ℝ) * ((Nat.log 2 (n + 2) : ℝ) + 1) := by
        have hcast : ((g (x, w)).1 : ℝ) ≤ ((n + c * Nat.log 2 (n + 2) + c : ℕ) : ℝ) := by
          exact_mod_cast hq'_le
        push_cast at hcast
        linarith
      have h2 : (n : ℝ) ^ δ ≤ ((g (x, w)).1 : ℝ) ^ δ :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hq'_ge) (lt_trans hε hεδ).le
      have h3 : c₀ * (n : ℝ) ^ δ ≤ c₀ * ((g (x, w)).1 : ℝ) ^ δ :=
        mul_le_mul_of_nonneg_left h2 hc₀.le
      linarith
    have hsat_le_target : (T_sat (g (x, w)) : ℝ) ≤ (M_sat : ℝ) * target + (M_sat : ℝ) :=
      hsatR.trans (by
        have h2 := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp_sat
        have := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (α := ℝ) M_sat)
        linarith)
    have hsum_nat : polyEnv n + T_sat (g (x, w)) + 2 ≤
        (2 * M_sat + 4) * tBound n + (M_sat + 4) := by
      have hR : ((polyEnv n + T_sat (g (x, w)) + 2 : ℕ) : ℝ) ≤
          (((2 * M_sat + 4) * tBound n + (M_sat + 4) : ℕ) : ℝ) := by
        push_cast
        have hMnn : (0 : ℝ) ≤ (M_sat : ℝ) := Nat.cast_nonneg _
        have htb_nn : (0 : ℝ) ≤ (tBound n : ℝ) := Nat.cast_nonneg _
        nlinarith only [hpoly_le_target, hsat_le_target, htarget_le_floor, hMnn, htb_nn]
      exact_mod_cast hR
    have hC1 : 2 * M_sat + 4 ≤ C_total := le_max_left _ _
    have hC2 : M_sat + 4 ≤ C_total :=
      (by omega : M_sat + 4 ≤ B_fin + M_sat + 4).trans (le_max_right _ _)
    have hmul : (2 * M_sat + 4) * tBound n ≤ C_total * tBound n := Nat.mul_le_mul_right _ hC1
    omega

/-- **Checked `ACC⁰` decoders of a succinct 3-CNF**: for an instance `x`, a certificate `e` of
length `certLength x`, polynomial in `|x|`, selects a decoder `decoder (x, e)` of `J x` output bits
on `q x` inputs and a check circuit `check (x, e)` on `q₁ x` inputs; the decoder is only to be
trusted when the check circuit is unsatisfiable. Both families are polynomial-time uniform and of
constant depth. This is the form in which Williams compresses the polynomial-size decoders of a
succinct reduction into `ACC⁰[m]` under `P ⊆ ACC⁰` ([Williams2014], Lemma 3.1);
`exists_checkedDecoders` builds it. -/
structure CheckedACC0Decoders (dC dD : ℕ) (q₁ q J : List Bool → ℕ) where
  /-- The length of the certificate `e` of an instance. -/
  certLength : List Bool → ℕ
  /-- The constant in the polynomial bound on the certificate length. -/
  slack : ℕ
  /-- The check circuit `check (x, e)`; the certificate `e` is good when it is unsatisfiable. -/
  check : (p : List Bool × List Bool) → Circuit Unbounded.extSignature (q₁ p.1) 1
  /-- The decoder `decoder (x, e)` of the bits of a clause from its address. -/
  decoder : (p : List Bool × List Bool) → Circuit Unbounded.extSignature (q p.1) (J p.1)
  /-- The certificate length is computable in unary in polynomial time. -/
  certLength_polyTime : ComputableInPolyTime certLength encBits encUnary
  /-- The certificate length is polynomial. -/
  certLength_le : ∀ x, certLength x ≤ slack * (x.length + 1) ^ slack
  /-- The code of the check circuit is computable in polynomial time. -/
  check_polyTime : ComputableInPolyTime (fun p => (check p).code) (encPair encBits encBits)
    (Circuit.encCode Unbounded.encExtOp)
  /-- The code of the decoder is computable in polynomial time. -/
  decoder_polyTime : ComputableInPolyTime (fun p => (decoder p).code) (encPair encBits encBits)
    (Circuit.encCode Unbounded.encExtOp)
  /-- The check circuits have depth at most `dC`. -/
  depth_check_le : ∀ p, (check p).depth ≤ dC
  /-- The decoders have depth at most `dD`. -/
  depth_decoder_le : ∀ p, (decoder p).depth ≤ dD

/-- **Checked-decoder small-witness language**: inputs `x` with a certificate `e` of length
`ℓ x` such that the check circuit `C₁ (x, e)` is unsatisfiable and the formula of the decoder
`D (x, e)` has a satisfying assignment computable by an `ACC⁰[m]` circuit of depth at most `dW` and
canonical code length at most `L x`. -/
@[expose] def checkedACC0WitnessLanguage (m dW : ℕ) {q₁ q r : List Bool → ℕ}
    (C₁ : (p : List Bool × List Bool) → Circuit Unbounded.extSignature (q₁ p.1) 1)
    (D : (p : List Bool × List Bool) → Circuit Unbounded.extSignature (q p.1) (3 * (r p.1 + 1)))
    (ℓ L : List Bool → ℕ) : Set (List Bool) :=
  {x | ∃ e : List Bool, e.length = ℓ x ∧
    (⟨q₁ x, C₁ (x, e)⟩ ∉ SignatureCircuitSAT (Unbounded.extInterpretation (modGate m))) ∧
    ∃ W : Circuit Unbounded.extSignature (r x) 1, W.depth ≤ dW ∧
      (Circuit.encCode Unbounded.encExtOp W.code).length ≤ L x ∧
      (toCNFExt m (D (x, e))).eval
        (fun y => W.eval (Unbounded.extInterpretation (modGate m)) y 0) = true}

/-- **Subexponential-savings `NTIME` simulation of checked small `ACC⁰` witnesses**: the
checked-decoder analogue of `smallACC0WitnessLanguage_mem_NTIME_of_acc0SAT`. The decoder
`R.decoder (x, e)` may depend on a certificate `e` of polynomial length `R.certLength x`, which a
second constant-depth `ACC⁰[m]` circuit `R.check (x, e)` must certify by being unsatisfiable. For
every depth bounds `dC`, `dD`, `dW` and modulus `m > 0` there are `r_w > 0`, `0 < δ < 1`, `c₀ > 0`
such that for every polynomial-time uniform such family with quasilinear input counts `q₁`, `q`
the language `checkedACC0WitnessLanguage m dW R.check R.decoder R.certLength
(fun x => 2 ^ Nat.nthRoot r_w |x|)` lies in `NTIME(⌊2 ^ (n - c₀ * n ^ δ)⌋₊)`. The machine guesses
`e` and the witness circuit and runs the `ACC⁰-SAT` algorithm once on the disjunction of the two
padded circuits. -/
theorem checkedACC0WitnessLanguage_mem_NTIME_of_acc0SAT (dC dD dW : ℕ) {m : ℕ} (hm : 0 < m) :
    ∃ (r_w : ℕ) (δ c₀ : ℝ), 0 < r_w ∧ 0 < δ ∧ δ < 1 ∧ 0 < c₀ ∧
      ∀ {q₁ q r : List Bool → ℕ} (R : CheckedACC0Decoders dC dD q₁ q fun x => 3 * (r x + 1))
        (c : ℕ),
        ComputableInPolyTime q₁ encBits encUnary →
        ComputableInPolyTime q encBits encUnary →
        ComputableInPolyTime r encBits encUnary →
        (∀ x, q₁ x ≤ x.length + c * Nat.log 2 (x.length + 2) + c) →
        (∀ x, q x ≤ x.length + c * Nat.log 2 (x.length + 2) + c) →
        checkedACC0WitnessLanguage m dW R.check R.decoder R.certLength
          (fun x => 2 ^ Nat.nthRoot r_w x.length) ∈
          NTIME encBits fun n => ⌊(2 : ℝ) ^ ((n : ℝ) - c₀ * (n : ℝ) ^ δ)⌋₊ := by
  obtain ⟨r_w, δ, c₀, hrw_pos, hδ0, hδ1, hc₀, hgen⟩ :=
    exists_ntime_of_padded_unsat (max dC (dD + dW + 5) + 1) hm
  refine ⟨r_w, δ, c₀, hrw_pos, hδ0, hδ1, hc₀, ?_⟩
  intro q₁ q r R c₁ hq₁ hq hr hq₁_le₀ hq_le₀
  obtain ⟨ℓ, cℓ, C₁, D, hℓ, hℓ_le₀, hC₁, hD, hdC, hdD⟩ := R
  obtain ⟨c, hq₁_le, hq_le, hℓ_le⟩ : ∃ c : ℕ,
      (∀ x, q₁ x ≤ x.length + c * Nat.log 2 (x.length + 2) + c) ∧
      (∀ x, q x ≤ x.length + c * Nat.log 2 (x.length + 2) + c) ∧
      ∀ x, ℓ x ≤ c * (x.length + 1) ^ c := by
    refine ⟨c₁ + cℓ, fun x => ?_, fun x => ?_, fun x => ?_⟩
    · have := hq₁_le₀ x
      rw [Nat.add_mul]
      omega
    · have := hq_le₀ x
      rw [Nat.add_mul]
      omega
    · exact (hℓ_le₀ x).trans (Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (Nat.succ_pos _)
        (by omega)))
  have hpad_poly := computableInPolyTime_checkedPad (ℓ := ℓ) C₁ D hq₁ hq hr hℓ hC₁ hD dW
  obtain ⟨T, S, C, d, hℓ₂O, hT⟩ := exists_computableInO_witnessLength hrw_pos
  obtain ⟨Tℓ, Sℓ, hTℓ, hSℓ, hℓaO⟩ := hℓ.exists_computableInO
  obtain ⟨Cℓ, dℓ, hTℓ_le⟩ := hTℓ.exists_le
  obtain ⟨Ta, Sa, hTa, hSa, haddO⟩ := ComputableInPolyTime.unary_add.exists_computableInO
  obtain ⟨Ca, da, hTa_le⟩ := hTa.exists_le
  have hΛO : ComputableInO (fun x : List Bool => ℓ x + (2 * 2 ^ Nat.nthRoot r_w x.length + 1))
      encBits encUnary _ _ := haddO.comp (hℓaO.prod hℓ₂O)
  let a : ℕ := (c + d + dℓ + 8) * (da + 1)
  let K : ℕ := Cℓ + C + Ca * (2 * c + 7) ^ da
  have ha1 : c + d + dℓ + 8 ≤ a := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have ha2 : (c + 1) * da ≤ a := by
    dsimp only [a]
    nlinarith [Nat.zero_le da, Nat.zero_le c, Nat.zero_le d, Nat.zero_le dℓ]
  have ha3 : da ≤ a := by
    dsimp only [a]
    nlinarith [Nat.zero_le da, Nat.zero_le c, Nat.zero_le d, Nat.zero_le dℓ]
  have hbound : ∀ x : List Bool,
      Tℓ x + T x + Ta (ℓ x, 2 * 2 ^ Nat.nthRoot r_w x.length + 1) ≤
        K * ((x.length + 1) ^ a * 2 ^ (a * Nat.nthRoot r_w x.length)) := by
    intro x
    have hlx := hℓ_le x
    have h1 := hTℓ_le x
    have h2 := hT x
    have h3 := hTa_le (ℓ x, 2 * 2 ^ Nat.nthRoot r_w x.length + 1)
    simp only [encBits_apply] at h1
    simp only [length_encPair, encUnary_apply, List.length_replicate] at h3
    set n := x.length with hn
    set P := 2 ^ Nat.nthRoot r_w n with hP
    have hP1 : 1 ≤ P := Nat.one_le_two_pow
    have hn1 : n + 1 ≤ (n + 1) ^ (c + 1) := Nat.le_self_pow (by omega) _
    set Y := (n + 1) ^ (c + 1) * P with hY
    have hY1 : n + 1 ≤ Y := hn1.trans (Nat.le_mul_of_pos_right _ hP1)
    have hcY : c * (n + 1) ^ c ≤ c * Y := by
      refine Nat.mul_le_mul_left c ?_
      calc (n + 1) ^ c ≤ (n + 1) ^ (c + 1) := Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
        _ ≤ Y := Nat.le_mul_of_pos_right _ hP1
    have hPY : P ≤ Y := Nat.le_mul_of_pos_left _ (Nat.pow_pos (Nat.succ_pos _))
    have hlen : (2 * ℓ x + (2 * P + 1)) + 1 + 1 ≤ (2 * c + 7) * Y := by
      have : (2 * c + 7) * Y = 2 * (c * Y) + 7 * Y := by ring
      omega
    have e1 : (n + 1) ^ dℓ ≤ (n + 1) ^ a * 2 ^ (a * Nat.nthRoot r_w n) :=
      (Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)).trans
        (Nat.le_mul_of_pos_right _ Nat.one_le_two_pow)
    have e2 : (n + 1) ^ d * 2 ^ (d * Nat.nthRoot r_w n) ≤
        (n + 1) ^ a * 2 ^ (a * Nat.nthRoot r_w n) :=
      Nat.mul_le_mul (Nat.pow_le_pow_right (Nat.succ_pos _) (by omega))
        (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ (by omega)))
    have e3 : Y ^ da ≤ (n + 1) ^ a * 2 ^ (a * Nat.nthRoot r_w n) := by
      calc Y ^ da = ((n + 1) ^ (c + 1)) ^ da * P ^ da := Nat.mul_pow _ _ _
        _ = (n + 1) ^ ((c + 1) * da) * 2 ^ (Nat.nthRoot r_w n * da) := by
          rw [← pow_mul, hP, ← pow_mul]
        _ ≤ _ := Nat.mul_le_mul (Nat.pow_le_pow_right (Nat.succ_pos _) ha2)
          (Nat.pow_le_pow_right (by norm_num) (by
            rw [Nat.mul_comm a]; exact Nat.mul_le_mul_left _ ha3))
    have h3' : Ta (ℓ x, 2 * P + 1) ≤ Ca * ((2 * c + 7) ^ da * Y ^ da) := by
      refine h3.trans (Nat.mul_le_mul_left _ ?_)
      rw [← Nat.mul_pow]
      exact Nat.pow_le_pow_left (by omega) da
    generalize (n + 1) ^ a * 2 ^ (a * Nat.nthRoot r_w n) = Φ at e1 e2 e3 ⊢
    have h1' : Tℓ x ≤ Cℓ * Φ := h1.trans (Nat.mul_le_mul_left _ e1)
    have h2' : T x ≤ C * Φ := by
      rw [Nat.mul_assoc] at h2
      exact h2.trans (Nat.mul_le_mul_left _ e2)
    have h3'' : Ta (ℓ x, 2 * P + 1) ≤ Ca * (2 * c + 7) ^ da * Φ := by
      calc _ ≤ Ca * ((2 * c + 7) ^ da * Y ^ da) := h3'
        _ ≤ Ca * ((2 * c + 7) ^ da * Φ) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ e3)
        _ = _ := by ring
    have heq : K * Φ = Cℓ * Φ + C * Φ + Ca * (2 * c + 7) ^ da * Φ := by
      simp only [K]; ring
    omega
  have hΛO' := hΛO.mono_time (T' := fun x => a * ((x.length + 1) ^ a *
      2 ^ (a * Nat.nthRoot r_w x.length))) K fun x => by
    refine (hbound x).trans ?_
    generalize (x.length + 1) ^ a * 2 ^ (a * Nat.nthRoot r_w x.length) = Φ
    have ha : 0 < a := by omega
    exact Nat.mul_le_mul_left K ((Nat.le_mul_of_pos_left Φ ha).trans (Nat.le_succ _))
  refine hgen (checkedPad (ℓ := ℓ) dW C₁ D) (checkedACC0WitnessLanguage m dW C₁ D ℓ
    fun x => 2 ^ Nat.nthRoot r_w x.length) a c (by omega) hΛO' hpad_poly ?_ ?_ ?_ ?_ ?_
  · intro x w hw
    have hw' : w.length = ℓ x + (2 * 2 ^ Nat.nthRoot r_w x.length + 1) := hw
    have hlx := hℓ_le x
    set n := x.length with hn
    set P := 2 ^ Nat.nthRoot r_w n with hP
    have hP1 : 1 ≤ P := Nat.one_le_two_pow
    have hn1 : n + 1 ≤ (n + 1) ^ (c + 1) := Nat.le_self_pow (by omega) _
    have hcY : c * (n + 1) ^ c ≤ c * ((n + 1) ^ (c + 1) * P) := by
      refine Nat.mul_le_mul_left c ?_
      calc (n + 1) ^ c ≤ (n + 1) ^ (c + 1) := Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
        _ ≤ _ := Nat.le_mul_of_pos_right _ hP1
    have hY1 : n + 1 ≤ (n + 1) ^ (c + 1) * P := hn1.trans (Nat.le_mul_of_pos_right _ hP1)
    have hPY : P ≤ (n + 1) ^ (c + 1) * P := Nat.le_mul_of_pos_left _ (Nat.pow_pos (Nat.succ_pos _))
    have hY : (n + 1) ^ (c + 1) * P ≤ (n + 1) ^ a * 2 ^ (a * Nat.nthRoot r_w n) :=
      Nat.mul_le_mul (Nat.pow_le_pow_right (Nat.succ_pos _) (by omega))
        (Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_left _ (by omega)))
    have hlen : (encPair encBits encBits (x, w)).length + 1 ≤
        (c + 7) * ((n + 1) ^ (c + 1) * P) := by
      simp only [length_encPair, encBits_apply, hw']
      have : (c + 7) * ((n + 1) ^ (c + 1) * P) =
          c * ((n + 1) ^ (c + 1) * P) + 7 * ((n + 1) ^ (c + 1) * P) := by ring
      omega
    exact hlen.trans (Nat.mul_le_mul (by omega) hY)
  · intro x w
    refine (depth_checkedCircuit_le (C₁ (x, w.take (ℓ x))) (D (x, w.take (ℓ x))) dW
      (w.drop (ℓ x)) _ ((le_max_left _ _).trans (le_max_left _ _))
      ((le_max_right _ _).trans (le_max_left _ _))).trans ?_
    have h2 := hdC (x, w.take (ℓ x))
    have h3 := hdD (x, w.take (ℓ x))
    omega
  · intro x w
    exact le_max_right _ _
  · intro x w
    exact max_le (max_le (hq₁_le x) (hq_le x)) (by change x.length ≤ _; omega)
  · intro x
    have hmem (w' : List Bool) :
        (checkedPad (ℓ := ℓ) dW C₁ D (x, w') ∉
            SignatureCircuitSAT (Unbounded.extInterpretation (modGate m))) ↔
          (⟨q₁ x, C₁ (x, w'.take (ℓ x))⟩ ∉
              SignatureCircuitSAT (Unbounded.extInterpretation (modGate m))) ∧
            ⟨q x, certificateCircuitExt (D (x, w'.take (ℓ x))) dW (w'.drop (ℓ x))⟩ ∉
              SignatureCircuitSAT (Unbounded.extInterpretation (modGate m)) :=
      checkedCircuit_not_mem_SignatureCircuitSAT_iff m _ _ dW _ _ _ _
    constructor
    · rintro ⟨e, he, hC, W, hWd, hWl, hWs⟩
      obtain ⟨w, hw, hcert⟩ := (exists_cert_not_mem_SignatureCircuitSAT_iff m (D (x, e)) dW
        (2 ^ Nat.nthRoot r_w x.length)).2 ⟨W, hWd, hWl, hWs⟩
      refine ⟨e ++ w, by simp only [List.length_append, he, hw], (hmem _).2 ?_⟩
      rw [List.take_left' he, List.drop_left' he]
      exact ⟨hC, hcert⟩
    · rintro ⟨w', hw', hunsat⟩
      obtain ⟨h1, h2⟩ := (hmem w').1 hunsat
      have hw'' : w'.length = ℓ x + (2 * 2 ^ Nat.nthRoot r_w x.length + 1) := hw'
      have hlen1 : (w'.take (ℓ x)).length = ℓ x := by rw [List.length_take]; omega
      have hlen2 : (w'.drop (ℓ x)).length = 2 * 2 ^ Nat.nthRoot r_w x.length + 1 := by
        rw [List.length_drop]; omega
      exact ⟨w'.take (ℓ x), hlen1, h1,
        (exists_cert_not_mem_SignatureCircuitSAT_iff m (D (x, w'.take (ℓ x))) dW
          (2 ^ Nat.nthRoot r_w x.length)).1 ⟨w'.drop (ℓ x), hlen2, h2⟩⟩

/-- **Hard-witness transfer for checked quasilinear `ACC⁰` succinct 3-CNF reductions**: the
checked-decoder analogue of `exists_hard_acc0Witness_of_quasilinear_reduction`. For every depth
bounds `dC`, `dD`, `dW` and modulus `m > 0` there are `r_w > 0` and a language
`H ∈ NTIME encBits (2 ^ n)` such that whenever checked decoders `R` with quasilinear input counts
`q₁`, `q` reduce `H` in the sense that every certificate `e` of length `R.certLength x` passing the
check `R.check (x, e)` and whose formula `toCNFExt m (R.decoder (x, e))` is satisfiable puts `x`
in `H`, there are `x ∈ H` of arbitrarily large length with no certificate `e` passing the check
and admitting a depth-`≤ dW`, code-length-`≤ 2 ^ Nat.nthRoot r_w |x|` `ACC⁰[m]` satisfying
witness circuit. -/
theorem exists_hard_checkedACC0Witness (dC dD dW : ℕ) {m : ℕ} (hm : 0 < m) :
    ∃ (r_w : ℕ) (H : Set (List Bool)), 0 < r_w ∧ H ∈ NTIME encBits (fun n => 2 ^ n) ∧
      ∀ {q₁ q r : List Bool → ℕ} (R : CheckedACC0Decoders dC dD q₁ q fun x => 3 * (r x + 1))
        (c : ℕ),
        ComputableInPolyTime q₁ encBits encUnary →
        ComputableInPolyTime q encBits encUnary →
        ComputableInPolyTime r encBits encUnary →
        (∀ x, q₁ x ≤ x.length + c * Nat.log 2 (x.length + 2) + c) →
        (∀ x, q x ≤ x.length + c * Nat.log 2 (x.length + 2) + c) →
        (∀ x e, e.length = R.certLength x →
          ⟨q₁ x, R.check (x, e)⟩ ∉ SignatureCircuitSAT (Unbounded.extInterpretation (modGate m)) →
          (toCNFExt m (R.decoder (x, e))).Satisfiable → x ∈ H) →
        ∀ N₀ : ℕ, ∃ x ∈ H, N₀ ≤ x.length ∧ ¬ ∃ e : List Bool, e.length = R.certLength x ∧
          (⟨q₁ x, R.check (x, e)⟩ ∉ SignatureCircuitSAT (Unbounded.extInterpretation (modGate m))) ∧
          ∃ W : Circuit Unbounded.extSignature (r x) 1, W.depth ≤ dW ∧
            (Circuit.encCode Unbounded.encExtOp W.code).length ≤ 2 ^ Nat.nthRoot r_w x.length ∧
            (toCNFExt m (R.decoder (x, e))).eval
              (fun y => W.eval (Unbounded.extInterpretation (modGate m)) y 0) = true := by
  obtain ⟨r_w, δ, c₀, hrw_pos, hδ, _, hc₀, hsim⟩ :=
    checkedACC0WitnessLanguage_mem_NTIME_of_acc0SAT dC dD dW hm
  obtain ⟨H, hH_mem, hH_ne⟩ := exists_mem_NTIME_two_pow_forall_exists_length_ge hδ hc₀
  refine ⟨r_w, H, hrw_pos, hH_mem, ?_⟩
  intro q₁ q r R c hq₁ hq hr hq₁_le hq_le hred N₀
  obtain ⟨x, hx, hne⟩ := hH_ne _ (hsim R c hq₁ hq hr hq₁_le hq_le) N₀
  have hsub : x ∈ checkedACC0WitnessLanguage m dW R.check R.decoder R.certLength
      (fun x => 2 ^ Nat.nthRoot r_w x.length) → x ∈ H :=
    fun ⟨e, he, hC, W, _, _, hsat⟩ =>
      hred x e he hC ⟨fun y => W.eval (Unbounded.extInterpretation (modGate m)) y 0, hsat⟩
  by_cases hxH : x ∈ H
  · exact ⟨x, hxH, hx, fun hW => hne ⟨fun _ => hW, fun _ => hxH⟩⟩
  · exact absurd (hne ⟨fun h => absurd h hxH, fun h => absurd (hsub h) hxH⟩) id

/-- The checked decoders of an unchecked family `D`: no certificate, and the constant `false`
check circuit, which is unsatisfiable. -/
private def uncheckedDecoders {dD : ℕ} {q r : List Bool → ℕ}
    (D : (x : List Bool) → Circuit Unbounded.extSignature (q x) (3 * (r x + 1)))
    (hD : ComputableInPolyTime (fun x => (D x).code) encBits (Circuit.encCode Unbounded.encExtOp))
    (hdepth : ∀ x, (D x).depth ≤ dD) :
    CheckedACC0Decoders 1 dD (fun _ => 0) q fun x => 3 * (r x + 1) where
  certLength _ := 0
  slack := 0
  check _ := Unbounded.constCircuit Unbounded.toExt false
  decoder p := D p.1
  certLength_polyTime := ComputableInPolyTime.const 0
  certLength_le _ := Nat.zero_le _
  check_polyTime := ComputableInPolyTime.const _
  decoder_polyTime := hD.comp (ComputableInPolyTime.fst encBits encBits)
  depth_check_le _ := Unbounded.depth_constCircuit_le false
  depth_decoder_le p := hdepth p.1

/-- **Subexponential-savings `NTIME` simulation of small `ACC⁰` witnesses** ([Williams2014],
Theorem 3.2 witness-checking step combined with Theorem 4.1 `exists_acc0SAT_decider`): for every
constant decoder depth `dD`, witness depth `dW`, and modulus `m > 0`, there exist `r_w > 0`,
`0 < δ < 1`, and `c₀ > 0` (depending only on `dD`, `dW`, and `m`) such that for every
polynomial-time uniform depth-`≤ dD` `ACC⁰[m]` succinct 3-CNF family `D` with quasilinear
clause-index count `q x ≤ |x| + c * Nat.log 2 (|x| + 2) + c`, deciding whether `toCNFExt m (D x)`
has a depth-`≤ dW`, code-length-`≤ 2 ^ Nat.nthRoot r_w |x|` `ACC⁰[m]` satisfying witness lies in
`NTIME(⌊2 ^ (n - c₀ * n ^ δ)⌋₊)`. This is the checked version
(`checkedACC0WitnessLanguage_mem_NTIME_of_acc0SAT`) with no certificate `e` and the check circuit
the constant `false`. -/
theorem smallACC0WitnessLanguage_mem_NTIME_of_acc0SAT (dD dW : ℕ) {m : ℕ} (hm : 0 < m) :
    ∃ (r_w : ℕ) (δ c₀ : ℝ), 0 < r_w ∧ 0 < δ ∧ δ < 1 ∧ 0 < c₀ ∧
      ∀ {q r : List Bool → ℕ}
        (D : (x : List Bool) → Circuit Unbounded.extSignature (q x) (3 * (r x + 1)))
        (c : ℕ),
        ComputableInPolyTime q encBits encUnary →
        ComputableInPolyTime r encBits encUnary →
        ComputableInPolyTime (fun x => (D x).code) encBits (Circuit.encCode Unbounded.encExtOp) →
        (∀ x, (D x).depth ≤ dD) →
        (∀ x, q x ≤ x.length + c * Nat.log 2 (x.length + 2) + c) →
        smallACC0WitnessLanguage m dW D (fun x => 2 ^ Nat.nthRoot r_w x.length) ∈
          NTIME encBits fun n => ⌊(2 : ℝ) ^ ((n : ℝ) - c₀ * (n : ℝ) ^ δ)⌋₊ := by
  obtain ⟨r_w, δ, c₀, hrw, hδ0, hδ1, hc₀, hsim⟩ :=
    checkedACC0WitnessLanguage_mem_NTIME_of_acc0SAT 1 dD dW hm
  refine ⟨r_w, δ, c₀, hrw, hδ0, hδ1, hc₀, ?_⟩
  intro q r D c hq hr hD hdepth hq_le
  have hset : smallACC0WitnessLanguage m dW D (fun x => 2 ^ Nat.nthRoot r_w x.length) =
      checkedACC0WitnessLanguage m dW (q₁ := fun _ => 0) (q := q) (r := r)
        (uncheckedDecoders D hD hdepth).check (uncheckedDecoders D hD hdepth).decoder
        (uncheckedDecoders D hD hdepth).certLength (fun x => 2 ^ Nat.nthRoot r_w x.length) := by
    ext x
    constructor
    · rintro ⟨W, hW⟩
      exact ⟨[], rfl, constCircuit_false_not_mem_SignatureCircuitSAT m 0, W, hW⟩
    · rintro ⟨e, -, -, W, hW⟩
      exact ⟨W, hW⟩
  rw [hset]
  exact hsim (uncheckedDecoders D hD hdepth) c (ComputableInPolyTime.const 0) hq hr
    (fun _ => Nat.zero_le _) hq_le

/-- **Hard-witness transfer for quasilinear `ACC⁰` succinct 3-CNF reductions** ([Williams2014],
Section 3, Theorem 3.2 diagonalization step): for every constant decoder depth `dD`, witness
depth `dW`, and modulus `m > 0`, there exist `r_w > 0` and a single language
`H ∈ NTIME encBits (2 ^ n)` such that every polynomial-time uniform depth-`≤ dD` `ACC⁰[m]`
quasilinear succinct 3-CNF reduction `D` of `H` has satisfiable instances `x ∈ H` of every
sufficiently large length whose represented 3-CNF `toCNFExt m (D x)` admits **no** satisfying
assignment computable by a depth-`≤ dW` `ACC⁰[m]` circuit of code length at most
`2 ^ Nat.nthRoot r_w x.length`. Hard instances of arbitrarily large length, rather than one, are
what an assumed asymptotic circuit bound can contradict: the witness budget is too small for any
circuit at short lengths. This is the checked version (`exists_hard_checkedACC0Witness`) with no
certificate `e` and the check circuit the constant `false`. -/
theorem exists_hard_acc0Witness_of_quasilinear_reduction (dD dW : ℕ) {m : ℕ} (hm : 0 < m) :
    ∃ (r_w : ℕ) (H : Set (List Bool)), 0 < r_w ∧ H ∈ NTIME encBits (fun n => 2 ^ n) ∧
      ∀ {q r : List Bool → ℕ}
        (D : (x : List Bool) → Circuit Unbounded.extSignature (q x) (3 * (r x + 1)))
        (c : ℕ),
        ComputableInPolyTime q encBits encUnary →
        ComputableInPolyTime r encBits encUnary →
        ComputableInPolyTime (fun x => (D x).code) encBits (Circuit.encCode Unbounded.encExtOp) →
        (∀ x, (D x).depth ≤ dD) →
        (∀ x, q x ≤ x.length + c * Nat.log 2 (x.length + 2) + c) →
        (∀ x, x ∈ H ↔ (toCNFExt m (D x)).Satisfiable) →
        ∀ N₀ : ℕ, ∃ x ∈ H, N₀ ≤ x.length ∧ ¬ ∃ W : Circuit Unbounded.extSignature (r x) 1,
          W.depth ≤ dW ∧
          (Circuit.encCode Unbounded.encExtOp W.code).length ≤ 2 ^ Nat.nthRoot r_w x.length ∧
          (toCNFExt m (D x)).eval
            (fun y => W.eval (Unbounded.extInterpretation (modGate m)) y 0) = true := by
  obtain ⟨r_w, H, hrw, hH, hhard⟩ := exists_hard_checkedACC0Witness 1 dD dW hm
  refine ⟨r_w, H, hrw, hH, ?_⟩
  intro q r D c hq hr hD hdepth hq_le hred N₀
  obtain ⟨x, hxH, hx, hno⟩ := hhard (uncheckedDecoders D hD hdepth) c
    (ComputableInPolyTime.const 0) hq hr (fun _ => Nat.zero_le _) hq_le
    (fun x _ _ _ hsat => (hred x).2 hsat) N₀
  exact ⟨x, hxH, hx, fun ⟨W, hWd, hWl, hWe⟩ =>
    hno ⟨[], rfl, constCircuit_false_not_mem_SignatureCircuitSAT m 0, W, hWd, hWl, hWe⟩⟩

end WitnessTransfer

end Cslib.Circuits.Boolean.SymAnd
