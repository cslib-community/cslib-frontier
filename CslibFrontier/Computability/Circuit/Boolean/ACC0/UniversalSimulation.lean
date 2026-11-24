/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.ACC0.Basic
public import CslibFrontier.Computability.Circuit.Boolean.ACC0.Gadgets
public import CslibFrontier.Computability.Circuit.Boolean.EvaluationTime
public import CslibFrontier.Computability.Circuit.Boolean.PPoly
public import CslibFrontier.Computability.Complexity.Classes.P
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import CslibFrontier.Computability.Circuit.Boolean.EncodingSize
import CslibFrontier.Computability.Circuit.Boolean.Simps
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Size

/-!
# Universal circuit simulation from circuits for `P`

Folklore universal simulation ([Williams2014], Lemma 5.1, Section 5, p. 18 of the July 31, 2012
version): if every language in `P` admits small circuits over a Boolean basis containing the
unbounded fan-in basis `AC⁰`, then every unrestricted fan-in-two De Morgan circuit `C` of size `T`
on `n` inputs has an equivalent circuit over that basis obtained by hardwiring the encoding of `C`
into the circuit for `CircuitEval` at input length `n + O((T + 1) log(n + T + 2))`.

Concretely, `circuitEvalLanguage` encodes a De Morgan gate list and output wire number as a framed
prefix (`evalPrefix C`) followed by the raw input bit string `x`. Evaluating the gate list is in
`P` (`circuitEvalLanguage_mem_P`), and `evalPrefix C` has length
`O((C.size + 1) * (log₂(n + C.size + 1) + 1))` (`length_evalPrefix_le`). Hardwiring `evalPrefix C`
via `Unbounded.constsCircuit` costs two constant gates and at most one layer of depth
(`exists_circuit_of_P_circuits`), yielding in particular that `P ⊆ ACC⁰` implies all of `P/poly`
has polynomial-size `AC⁰[m]` circuits of a single uniform depth `d` and modulus `m ≥ 2`
(`exists_uniform_depth_ACC0_of_P_subset_ACC0`).

## Main definitions

* `Cslib.Circuits.Boolean.evalPrefix`: the framed prefix encoding a single-output De Morgan
  circuit's gate list and output wire for `circuitEvalLanguage`.
* `Cslib.Circuits.Boolean.circuitEvalLanguage`: the polynomial-time De Morgan circuit evaluation
  language on framed circuit prefixes followed by raw input words.

## Main results

* `Cslib.Circuits.Boolean.circuitEvalLanguage_mem_P`: `circuitEvalLanguage ∈ P encBits`.
* `Cslib.Circuits.Boolean.length_evalPrefix_le`: `(evalPrefix C).length` is
  `O((C.size + 1) * (log₂(n + C.size + 1) + 1))`.
* `Cslib.Circuits.Boolean.exists_circuit_of_P_circuits`: [Williams2014], Lemma 5.1 — circuits for
  `P` over any basis containing `AC⁰` simulate arbitrary De Morgan circuits with input length
  `n + O((C.size + 1) * log₂(n + C.size + 2))`, additive depth `+ 1`, and additive size `+ 2`.
* `Cslib.Circuits.Boolean.exists_uniform_depth_ACC0_of_P_subset_ACC0`: [Williams2014], remark
  after Lemma 5.1, p. 19 — if `P ⊆ ACC⁰`, then there exist fixed `d` and `m ≥ 2` such that every
  language in `P/poly` has polynomial-size depth-`d` `AC⁰[m]` circuits.

## References

* [R. Williams, *Non-Uniform ACC Circuit Lower Bounds*, July 31, 2012 version, Section 5,
  Lemma 5.1 and following remark, pp. 18–19][Williams2014]
-/

public section

namespace Cslib.Circuits.Boolean

open Turing.MultiTapeTM Cslib.Complexity

/-! ### Total polynomial-time decoder for De Morgan circuit codes -/

/-- Total left inverse of `Boolean.Op.toNat`, saturating values `≥ 4` to `.or`. -/
private def opOfNat : ℕ → Op
  | 0 => .const false
  | 1 => .const true
  | 2 => .not
  | 3 => .and
  | _ => .or

private theorem opOfNat_toNat (op : Op) : opOfNat op.toNat = op := by
  cases op with
  | const b => cases b <;> rfl
  | not => rfl
  | and => rfl
  | or => rfl

private theorem toNat_opOfNat (n : ℕ) : (opOfNat n).toNat = min n 4 := by
  rcases n with _ | _ | _ | _ | n <;> simp only [opOfNat, Op.toNat] <;> omega

/-- Total polynomial-time decoder for `Boolean.encOp`. -/
private def decOp : Decoder encOp where
  decode w := opOfNat w.length
  decode_enc op := by
    simp only [encOp, Function.Embedding.coeFn_mk, encUnary_apply, List.length_replicate,
      opOfNat_toNat]
  computable := by
    have hmin : ComputableInPolyTime (fun w : List Bool => min w.length 4) encBits encUnary := by
      have hlen : ComputableInPolyTime (fun w : List Bool => w.length) encBits encUnary :=
        ComputableInPolyTime.of_enc_eq (f := fun w : List Bool => w.length)
          Decoder.unary.computableInPolyTime (fun _ => rfl)
      fun_prop
    exact (hmin.of_enc_eq (encD := encOp) (g := fun w : List Bool => opOfNat w.length) fun w => by
      simp only [encOp, Function.Embedding.coeFn_mk, toNat_opOfNat]).exists_degree

/-- Total polynomial-time decoder for `(gates, outputWire)` pairs. -/
private def decGatesOutput : Decoder (encPair (encList encGate) encNat) :=
  Decoder.pair (Decoder.list (Decoder.pair decOp (Decoder.list Decoder.nat))) Decoder.nat

/-! ### The `CircuitEval` language in `P` -/

/-- The framed prefix encoding a single-output De Morgan circuit's gate list and output wire
number. Appending `List.ofFn x` yields a word of length `(evalPrefix C).length + n` whose
membership in `circuitEvalLanguage` equals `C.eval interpretation x 0`. -/
@[expose] def evalPrefix {n : ℕ} (C : Circuit signature n 1) : List Bool :=
  frame (encPair (encList encGate) encNat (C.code.1, (C.outputs 0).toNat))

/-- Total polynomial-time evaluator of a word `frame (enc (gates, o)) ++ x`. -/
private def evalCircuitWord (w : List Bool) : Bool :=
  let go := decGatesOutput.decode (unframe w)
  evalOutput (dropFrame w) go.1 go.2

/-- The De Morgan circuit-evaluation language on words `frame (enc (gates, o)) ++ x`. -/
def circuitEvalLanguage : Language Bool :=
  {w | evalCircuitWord w = true}

/-- **`CircuitEval ∈ P`**: evaluating a framed De Morgan gate list and output wire on the trailing
input bits is computable in polynomial time. -/
theorem circuitEvalLanguage_mem_P : (circuitEvalLanguage : Set (List Bool)) ∈ P encBits := by
  refine ⟨evalCircuitWord, ?_, fun _ => Iff.rfl⟩
  have hdec := decGatesOutput.computableInPolyTime
  unfold evalCircuitWord
  fun_prop

/-- On `evalPrefix C ++ List.ofFn x`, `circuitEvalLanguage` agrees with `C.eval`. -/
theorem mem_circuitEvalLanguage_evalPrefix {n : ℕ} (C : Circuit signature n 1)
    (x : BitString n) :
    evalPrefix C ++ List.ofFn x ∈ circuitEvalLanguage ↔ C.eval interpretation x 0 = true := by
  change evalCircuitWord (evalPrefix C ++ List.ofFn x) = true ↔ _
  rw [evalCircuitWord, evalPrefix, unframe_frame_append, dropFrame_frame_append,
    decGatesOutput.decode_enc, ← C.eval_eq_evalOutput x 0]

/-! ### Tight `O((T + 1) log(n + T + 2))` prefix length bound -/

/-- The framed circuit prefix `evalPrefix C` has length `O((C.size + 1) * log₂(n + C.size + 2))`,
matching the `O(T log T)` description length in [Williams2014], Lemma 5.1. -/
theorem length_evalPrefix_le {n : ℕ} (C : Circuit signature n 1) :
    (evalPrefix C).length ≤ 124 * (C.size + 1) * (Nat.log 2 (n + C.size + 1) + 1) := by
  set L := Nat.log 2 (n + C.size + 1) + 1 with hLdef
  have hL1 : 1 ≤ L := Nat.le_add_left 1 _
  have hwire (w : Wire n C.size) : (encNat w.toNat).length ≤ L := by
    rw [encNat_apply, Nat.size_eq_bits_len]
    have hsz : w.toNat.size ≤ (n + C.size).size := Nat.size_le_size (Wire.toNat_lt w).le
    have hlog : (n + C.size).size ≤ L := by
      rw [hLdef]
      exact (Nat.size_le_size (Nat.le_succ _)).trans (by
        have hlt := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (n + C.size + 1)
        exact Nat.size_le.2 hlt)
    exact hsz.trans hlog
  have hgates : (encList encGate C.code.1).length ≤ C.size * (23 + 8 * L) :=
    length_encList_encGate_le C hwire
  have hout : (encNat (C.outputs 0).toNat).length ≤ L := hwire (C.outputs 0)
  have hpair : (encPair (encList encGate) encNat (C.code.1, (C.outputs 0).toNat)).length ≤
      2 * (C.size * (23 + 8 * L)) + 1 + L := by
    rw [length_encPair]
    dsimp only
    omega
  have hframe : (evalPrefix C).length ≤ 4 * (C.size * (23 + 8 * L)) + 3 + 2 * L := by
    rw [evalPrefix, length_frame]
    omega
  have h23 : 23 + 8 * L ≤ 31 * L := by omega
  have hC1 : C.size * (23 + 8 * L) ≤ C.size * (31 * L) := Nat.mul_le_mul_left _ h23
  have h4 : 4 * (C.size * (23 + 8 * L)) ≤ 124 * C.size * L := by
    calc 4 * (C.size * (23 + 8 * L)) ≤ 4 * (C.size * (31 * L)) := Nat.mul_le_mul_left 4 hC1
      _ = 124 * C.size * L := by ring
  have h5 : 3 + 2 * L ≤ 124 * L := by omega
  calc (evalPrefix C).length ≤ 4 * (C.size * (23 + 8 * L)) + (3 + 2 * L) := by omega
    _ ≤ 124 * C.size * L + 124 * L := Nat.add_le_add h4 h5
    _ = 124 * (C.size + 1) * L := by ring

/-! ### Prefix hardwiring and Williams Lemma 5.1 -/

/-- Hardwire the first `p.length` input wires of `U` to the fixed bits of `p`, leaving the last
`n` wires as live inputs, using two constant gates (`Unbounded.constsCircuit`) and adding at most
one layer of depth. -/
private def hardwirePrefix {σ : Signature} (φ : Unbounded.signature.Hom σ) {n : ℕ}
    (p : List Bool) (U : Circuit σ (p.length + n) 1) : Circuit σ n 1 :=
  U.comp ((Unbounded.constsCircuit φ fun i : Fin p.length => p[i]).append (Circuit.wiring σ id))

private theorem eval_hardwirePrefix {σ : Signature} {φ : Unbounded.signature.Hom σ}
    {I : Interpretation σ Bool} [φ.Preserves Unbounded.interpretation I] {n : ℕ}
    (p : List Bool) (U : Circuit σ (p.length + n) 1) (x : BitString n) :
    (hardwirePrefix φ p U).eval I x =
      U.eval I (BitString.ofList (p.length + n) (p ++ List.ofFn x)) := by
  rw [hardwirePrefix, Circuit.eval_comp, Circuit.eval_append, Unbounded.eval_constsCircuit,
    Circuit.eval_wiring]
  congr 1
  funext k
  have hklt : k.val < (p ++ List.ofFn x).length := by simp
  simp only [BitString.ofList, Fin.append, Fin.addCases, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hklt, Option.getD_some]
  split_ifs with hk
  · simp [List.getElem_append_left hk]
  · simp [List.getElem_append_right (Nat.not_lt.1 hk), Fin.subNat, Fin.cast]

private theorem size_hardwirePrefix {σ : Signature} (φ : Unbounded.signature.Hom σ) {n : ℕ}
    (p : List Bool) (U : Circuit σ (p.length + n) 1) :
    (hardwirePrefix φ p U).size = U.size + 2 := by
  simp [hardwirePrefix]
  omega

private theorem depth_hardwirePrefix_le {σ : Signature} (φ : Unbounded.signature.Hom σ) {n : ℕ}
    (p : List Bool) (U : Circuit σ (p.length + n) 1) :
    (hardwirePrefix φ p U).depth ≤ U.depth + 1 := by
  circuit_bound [hardwirePrefix]

private theorem hardwirePrefix_computes_eval {σ : Signature} {φ : Unbounded.signature.Hom σ}
    {I : Interpretation σ Bool} [φ.Preserves Unbounded.interpretation I] {n : ℕ}
    (C : Circuit signature n 1) (U : Circuit σ ((evalPrefix C).length + n) 1)
    (hUc : U.Computes I (single (circuitEvalLanguage.slice ((evalPrefix C).length + n)))) :
    (hardwirePrefix φ (evalPrefix C) U).Computes I (C.eval interpretation) := by
  intro x
  classical
  funext o
  rw [Subsingleton.elim o 0, eval_hardwirePrefix]
  have hU := congrFun (hUc (BitString.ofList ((evalPrefix C).length + n)
    (evalPrefix C ++ List.ofFn x))) 0
  rw [hU]
  simp only [single, Language.slice]
  rw [BitString.ofFn_ofList (by simp), Bool.eq_iff_iff, decide_eq_true_eq]
  exact mem_circuitEvalLanguage_evalPrefix C x

/-- **Universal circuit simulation from circuits for `P`** ([Williams2014], Lemma 5.1, Section 5,
p. 18 of the July 31, 2012 version): if `circuitEvalLanguage` (in particular every language in `P`)
has circuits over a basis `I` containing the unbounded fan-in basis `AC⁰` of depth at most `d N`
and size at most `S N` at input length `N`, then every single-output De Morgan circuit `C` on `n`
inputs has an equivalent circuit `C'` over `I` of depth at most `d N + 1` and size at most
`S N + 2`, where `N = (evalPrefix C).length + n` satisfies
`N ≤ n + 124 * (C.size + 1) * (log₂(n + C.size + 1) + 1)`.
The two additive constant gates and `+ 1` depth come from hardwiring `evalPrefix C` via
`Unbounded.constsCircuit`. -/
theorem exists_circuit_of_P_circuits {σ : Signature} (φ : Unbounded.signature.Hom σ)
    {I : Interpretation σ Bool} [φ.Preserves Unbounded.interpretation I]
    {d S : ℕ → ℕ}
    (hP : ∀ L : Language Bool, (L : Set (List Bool)) ∈ P encBits →
      ∀ N, ∃ U : Circuit σ N 1,
        U.Computes I (single (L.slice N)) ∧ U.depth ≤ d N ∧ U.size ≤ S N)
    {n : ℕ} (C : Circuit signature n 1) :
    ∃ (N : ℕ) (C' : Circuit σ n 1),
      N ≤ n + 124 * (C.size + 1) * (Nat.log 2 (n + C.size + 1) + 1) ∧
      C'.Computes I (C.eval interpretation) ∧
      C'.depth ≤ d N + 1 ∧
      C'.size ≤ S N + 2 := by
  set p := evalPrefix C with hp
  set N := p.length + n with hN
  obtain ⟨U, hUc, hUd, hUs⟩ := hP circuitEvalLanguage circuitEvalLanguage_mem_P N
  refine ⟨N, hardwirePrefix φ p U, ?_, hardwirePrefix_computes_eval C U hUc, ?_, ?_⟩
  · have hlen := length_evalPrefix_le C
    rw [hN, hp]
    omega
  · exact (depth_hardwirePrefix_le φ p U).trans (Nat.add_le_add_right hUd 1)
  · rw [size_hardwirePrefix]
    exact Nat.add_le_add_right hUs 2

/-- **Uniform-depth `ACC⁰` collapse of `P/poly` when `P ⊆ ACC⁰`** ([Williams2014], remark after
Lemma 5.1, Section 5, p. 19 of the July 31, 2012 version): if `P ⊆ ACC⁰`, then there exist a single
fixed depth `d` and modulus `m ≥ 2` (from the `ACC⁰` circuits for `circuitEvalLanguage`) such that
every language in `P/poly` is decided by polynomial-size, depth-`≤ d` `AC⁰[m]` circuits. In
particular `P/poly ⊆ AC⁰[m] ⊆ ACC⁰`. -/
theorem exists_uniform_depth_ACC0_of_P_subset_ACC0
    (hP : ∀ L : Language Bool, (L : Set (List Bool)) ∈ P encBits → L ∈ ACC0) :
    ∃ (d m : ℕ), 2 ≤ m ∧ ∀ L ∈ PPoly, ∃ s : ℕ → ℕ, PolynomiallyBounded s ∧ ∀ n,
      ∃ C : Circuit Unbounded.extSignature n 1,
        C.Computes (Unbounded.extInterpretation (modGate m)) (single (L.slice n)) ∧
        C.depth ≤ d ∧ C.size ≤ s n := by
  obtain ⟨m, hm, hEval⟩ := mem_ACC0_iff.1 (hP circuitEvalLanguage circuitEvalLanguage_mem_P)
  obtain ⟨d, sE, hsE, hU⟩ := ConstDepth.mem_iff.1 hEval
  obtain ⟨cE, kE, hsE_le⟩ := polynomiallyBounded_iff_le.1 hsE
  refine ⟨d + 1, m, hm, fun L hL => ?_⟩
  obtain ⟨Cfam, p, hp, hCfam⟩ := mem_PPoly_iff_exists_circuits.1 hL
  let Nbound : ℕ → ℕ := fun n => n + 124 * (p n + 1) * (n + p n + 2)
  refine ⟨fun n => cE * (Nbound n + 1) ^ kE + 2, by dsimp [Nbound]; fun_prop, fun n => ?_⟩
  obtain ⟨hCs, hCc⟩ := hCfam n
  set pr := evalPrefix (Cfam n) with hpr
  set N := pr.length + n with hN
  obtain ⟨U, hUc, hUd, hUs⟩ := hU N
  refine ⟨hardwirePrefix Unbounded.toExt pr U, ?_, ?_, ?_⟩
  · intro x
    rw [hardwirePrefix_computes_eval (Cfam n) U hUc x, hCc x]
  · exact (depth_hardwirePrefix_le Unbounded.toExt pr U).trans (Nat.add_le_add_right hUd 1)
  · rw [size_hardwirePrefix]
    have hlog : Nat.log 2 (n + (Cfam n).size + 1) + 1 ≤ n + p n + 2 :=
      Nat.add_le_add_right ((Nat.log_le_self 2 _).trans (by omega)) 1
    have hNle : N ≤ Nbound n := by
      have hlen := length_evalPrefix_le (Cfam n)
      have hmul : 124 * ((Cfam n).size + 1) * (Nat.log 2 (n + (Cfam n).size + 1) + 1) ≤
          124 * (p n + 1) * (n + p n + 2) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 124 (Nat.add_le_add_right hCs 1)) hlog
      dsimp only [Nbound]
      rw [hN, hpr]
      omega
    have hSN : sE N ≤ cE * (Nbound n + 1) ^ kE :=
      (hsE_le N).trans
        (Nat.mul_le_mul_left cE (Nat.pow_le_pow_left (Nat.add_le_add_right hNle 1) kE))
    exact Nat.add_le_add_right (hUs.trans hSN) 2

end Cslib.Circuits.Boolean
