/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.SuccinctVerifier
public import CslibFrontier.Computability.Circuit.Boolean.Tableau.Decoder.Assembly
public import CslibFrontier.Computability.Complexity.Classes.EXP
public import CslibFrontier.Computability.Interactive.Sumcheck
public import CslibFrontier.Foundations.BooleanAnalysis.MultilinearExtension
public import CslibFrontier.Foundations.Data.MvPolynomial.SchwartzZippel
import CslibFrontier.Computability.Circuit.Boolean.CodeComposition
import CslibFrontier.Computability.Circuit.Boolean.CodeTemplate
import CslibFrontier.Computability.Complexity.Classes.NP.Nondeterministic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.ReplayVerdict
import CslibFrontier.Computability.Machines.Turing.MultiTape.Run
import CslibFrontier.Foundations.Data.List.RowMajor
import CslibFrontier.Foundations.Data.Nat.BinarySize
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Rename

/-!
# Arithmetization of `NEXP` via succinct tableau decoding

The tableau argument in [Babai, Fortnow and Lund, §4.2, Proposition 4.2][BabaiFortnowLund1991]
reduces a nondeterministic exponential-time computation to a formula tested with three assignment
oracle calls. Here a circuit returns the three signed variable addresses of an indexed tableau
clause. For the circuit indexing local clauses, see the proof sketch of Theorem 6.1 in
[Williams, p. 20][Williams2010]. The construction provides the following parts of the
two-prover simulation:

1. **Unconditional `NEXP` to succinct tableau CNF reduction** (`exists_succinctCNF_of_mem_NEXP`):
   every language `A ∈ NEXP enc` reduces to satisfiability of the uniform bit-field tableau CNF
   `Cslib.Circuits.Boolean.Tableau.succinctCNF tm (frame (enc a)) (n a) (T a)` for a fixed
   deterministic multi-tape machine `tm` and binary polynomial-time functions `n, T : α → ℕ` whose
   bit widths `colBits (T a)` and `timeBits (T a)` are polynomially bounded in `(enc a).length`.
2. **Uniform polynomial-time decoder construction** (`computableInPolyTime_decoderCode`,
   `exists_succinctDecoder_of_mem_NEXP`): `Tableau.Decoder.decoderCode tm` is computable in
   polynomial time from `(x, n, T)` under `(encBits, encNat, encNat)`—in time polynomial in
   `x.length + log n + log T` even when `n` and `T` are exponential.
3. **Algebraic gate-and-clause arithmetization and sumcheck reduction**:
   given a De Morgan decoder `c : Circuit signature Q (3 * (L + 1))` and an assignment
   polynomial `A : MvPolynomial (Fin L) F`, the polynomial `tableauConstraintPoly c A r` on
   `Q + c.size` variables checks gate consistency (`gateTracePoly R c`), 3-literal clause
   violation (`clauseUnsatPoly c A`), and a random multilinear equality weight (`eqCubePoly r`). It
   has individual degree at most `1 + 3 * c.size + 3 * (L + 1)`, vanishes identically on the cube
   iff `A` induces a satisfying assignment of `SuccinctVerifier.toCNF c` (or `succinctCNF`), and
   on unsatisfiable formulas induces a nonzero multilinear polynomial detected by Schwartz–Zippel
   and `Cslib.Interactive.Sumcheck.proof`.

The proof-oracle verifier in `Cslib.Complexity.NEXP_subset_PCPPoly` applies this arithmetization
to the uniformly constructed succinct decoder for every `NEXP` language.

## Main definitions

* `Cslib.Complexity.MIP.opEvalField`, `Cslib.Complexity.MIP.eqBit`: field-valued De Morgan gate
  semantics and multilinear bit-equality indicator.
* `Cslib.Complexity.MIP.gateTracePoly`, `Cslib.Complexity.MIP.clauseUnsatPoly`,
  `Cslib.Complexity.MIP.eqCubePoly`, `Cslib.Complexity.MIP.tableauConstraintPoly`: algebraic
  arithmetization polynomials for a succinct 3CNF decoder.
* `Cslib.Complexity.MIP.evalGateTraceMod`, `Cslib.Complexity.MIP.evalConstraintMod`: uniform
  natural-number mod-`p` evaluators computable in polynomial time over growing fields `ZMod p`.

## Main results

* `Cslib.Complexity.MIP.exists_succinctCNF_of_mem_NEXP`: unconditional `NEXP` to `succinctCNF`
  reduction.
* `Cslib.Complexity.MIP.computableInPolyTime_decoderCode`: `Tableau.Decoder.decoderCode tm` is
  polynomial-time under binary `(n, T)`.
* `Cslib.Complexity.MIP.exists_succinctDecoder_of_mem_NEXP`: `NEXP` reduction bundled with its
  polynomial-time succinct decoder circuit.
* `Cslib.Complexity.MIP.tableauConstraintPoly_degreeOf_le`: individual degree bound.
* `Cslib.Complexity.MIP.satisfiable_toCNF_iff_forall_eval_base_eq_zero`,
  `Cslib.Complexity.MIP.satisfiable_succinctCNF_iff_forall_eval_base_eq_zero`: exact Boolean
  soundness and completeness of the arithmetized constraint polynomial.
* `Cslib.Complexity.MIP.sumcheck_proof_complete_of_satisfiable`,
  `Cslib.Complexity.MIP.sumcheck_sound_of_not_satisfiable`: completeness and Schwartz–Zippel +
  Sumcheck soundness.
* `Cslib.Complexity.MIP.computableInPolyTime_evalConstraintMod`: uniform polynomial-time
  verification of the final Sumcheck evaluation over `ZMod p`.

## References

* [L. Babai, L. Fortnow, C. Lund, *Non-deterministic exponential time has two-prover interactive
  protocols*][BabaiFortnowLund1991]
* [R. Williams, *Improving exhaustive search implies superpolynomial lower bounds*][Williams2010]
-/

@[expose] public section

namespace Cslib.Complexity.MIP

open Cslib Cslib.BitString Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.Tableau
open Cslib.Logic.PL Cslib.Interactive MvPolynomial Turing Turing.MultiTapeTM
open ComputableInPolyTime
open scoped BigOperators ENNReal

/-! ### Reduction from `NEXP` to succinct tableau CNF -/

/-- **Unconditional `NEXP` to succinct tableau CNF reduction**: every `A ∈ NEXP enc` is decided
by satisfiability of `Tableau.succinctCNF tm (frame (enc a)) (n a) (T a)` for one deterministic
multi-tape machine `tm` and binary polynomial-time bounds `n, T : α → ℕ` whose bit-widths are
polynomially bounded in `(enc a).length`. This is the tableau step from the proof of
[Babai, Fortnow and Lund, §4.2, Proposition 4.2][BabaiFortnowLund1991]. -/
theorem exists_succinctCNF_of_mem_NEXP {α : Type} {enc : α ↪ List Bool} {A : Set α}
    (hA : A ∈ NEXP enc) :
    ∃ (k : ℕ) (State : Type) (_ : Fintype State) (_ : DecidableEq State)
      (tm : MultiTapeTM k Bool State) (n T : α → ℕ),
      ComputableInPolyTime n enc encNat ∧
      ComputableInPolyTime T enc encNat ∧
      PolyBounded (fun a => (enc a).length) (fun a => colBits (T a) + timeBits (T a)) ∧
      ∀ a : α, (frame (enc a)).length ≤ n a ∧ n a < 2 * T a ∧
        (a ∈ A ↔ (Tableau.succinctCNF tm (frame (enc a)) (n a) (T a)).Satisfiable) := by
  obtain ⟨d, c₁, c₂, m, State₀, hfin₀, ntm, hdec⟩ := mem_NEXP_iff.mp hA
  obtain ⟨C, hbigO, -⟩ := MultiTapePTM.computableInO_decide_runClosedCoins (enc := enc)
    ntm.choiceTable
  obtain ⟨k, State, hfin, tm, htm⟩ := hbigO
  let hF : Fintype State := Fintype.ofFinite State
  let hD : DecidableEq State := Classical.decEq State
  let M : ℕ := Nat.card (Turing.Action m Bool State₀)
  let n : α → ℕ := fun a => 2 * (enc a).length + 1 + M * (c₁ * 2 ^ (enc a).length ^ d + c₂)
  let T : α → ℕ := fun a => C * (n a + 1) + n a + 1
  have hn_len (a : α) : (frame (enc a)).length ≤ n a := by
    simp only [n, length_frame]
    omega
  have hn_T (a : α) : n a < 2 * T a := by
    simp only [T]
    omega
  have hpow2 : ComputableInPolyTime (fun a => 2 ^ (enc a).length ^ d) enc encNat :=
    binary_two_pow.comp ((unary_pow d).comp (encoding_length enc))
  have hlen_nat : ComputableInPolyTime (fun a => (enc a).length) enc encNat :=
    unary_to_binary.comp (encoding_length enc)
  have hn_pt : ComputableInPolyTime n enc encNat :=
    binary_add' (binary_add' (binary_mul' (const 2) hlen_nat) (const 1))
      (binary_mul' (const M) (binary_add' (binary_mul' (const c₁) hpow2) (const c₂)))
  have hT_pt : ComputableInPolyTime T enc encNat :=
    binary_add' (binary_add' (binary_mul' (const C) (binary_add' hn_pt (const 1))) hn_pt) (const 1)
  have h2T_pt : ComputableInPolyTime (fun a => 2 * T a) enc encNat := binary_mul' (const 2) hT_pt
  have hbits_poly : PolyBounded (fun a => (enc a).length)
      (fun a => colBits (T a) + timeBits (T a)) := by
    have h1 := h2T_pt.polyBounded_length
    have h2 := hT_pt.polyBounded_length
    have heq : (fun a => colBits (T a) + timeBits (T a)) =
        fun a => (encNat (2 * T a)).length + (encNat (T a)).length := by
      funext a
      simp only [colBits, timeBits, ← length_encNat_eq_size]
    rw [heq]
    exact h1.add h2
  refine ⟨k, State, hF, hD, tm, n, T, hn_pt, hT_pt, hbits_poly, fun a =>
    ⟨hn_len a, hn_T a, ?_⟩⟩
  rw [@Tableau.satisfiable_succinctCNF_iff k State hF hD tm (n a) (T a) (hn_T a)
    (frame (enc a)) (hn_len a), hdec.mem_iff_exists_checkChoices le_rfl]
  constructor
  · rintro ⟨w, hw, hcheck⟩
    have hw_len : w.length = M * (c₁ * 2 ^ (enc a).length ^ d + c₂) := hw
    refine ⟨frame (enc a) ++ w, ?_, List.prefix_append _ _, ?_⟩
    · simp only [n, List.length_append, length_frame, hw_len]
    · have hrun := (htm (a, w)).runFrom_of_le (J := T a) (by
        simp only [T, n, encPair_apply, List.length_append, length_frame, encBits_apply, hw_len]
        omega)
      simp only [encPair_apply, encBits_apply] at hrun
      rw [hrun.2,
        show decide (ntm.choiceTable.runClosedCoins w (enc a) = [true]) = true from hcheck]
      rfl
  · rintro ⟨y, hy, ⟨w, hw⟩, hout⟩
    have hw_len : w.length = M * (c₁ * 2 ^ (enc a).length ^ d + c₂) := by
      have hlen := congrArg List.length hw
      simp only [n, List.length_append, length_frame, hy] at hlen
      omega
    refine ⟨w, hw_len, ?_⟩
    have hrun := (htm (a, w)).runFrom_of_le (J := T a) (by
      simp only [T, n, encPair_apply, List.length_append, length_frame, encBits_apply, hw_len]
      omega)
    have heq : encPair enc encBits (a, w) = y := by
      simpa [encPair_apply, encBits_apply] using hw
    rw [← heq, hrun.2] at hout
    simp only [encBool, OutView.ofList] at hout
    exact OutView.one.inj hout

/-! ### Uniform polynomial-time construction of the succinct decoder -/

section DecoderPolyTime

private abbrev DecoderArg : Type := List Bool × ℕ × ℕ

private abbrev encDecoderArg : DecoderArg ↪ List Bool :=
  encPair encBits (encPair encNat encNat)

private theorem computableInPolyTime_colBits {α : Type} {enc : α ↪ List Bool}
    {T : α → ℕ} (hT : ComputableInPolyTime T enc encNat) :
    ComputableInPolyTime (fun a => colBits (T a)) enc encUnary :=
  binary_size.comp (binary_mul' (const 2) hT)

private theorem computableInPolyTime_timeBits {α : Type} {enc : α ↪ List Bool}
    {T : α → ℕ} (hT : ComputableInPolyTime T enc encNat) :
    ComputableInPolyTime (fun a => timeBits (T a)) enc encUnary :=
  binary_size.comp hT

private theorem computableInPolyTime_argT :
    ComputableInPolyTime (fun a : DecoderArg => a.2.2) encDecoderArg encNat :=
  (snd _ _).comp (snd _ _)

private theorem computableInPolyTime_pWidth (s : ℕ) :
    ComputableInPolyTime (fun a : DecoderArg => s + colBits a.2.2 + timeBits a.2.2)
      encDecoderArg encUnary :=
  unary_add' (unary_add' (const s) (computableInPolyTime_colBits computableInPolyTime_argT))
    (computableInPolyTime_timeBits computableInPolyTime_argT)

private theorem computableInPolyTime_pWidthNat (s : ℕ) :
    ComputableInPolyTime (fun a : DecoderArg => s + colBits a.2.2 + timeBits a.2.2)
      encDecoderArg encNat :=
  unary_to_binary.comp (computableInPolyTime_pWidth s)

private theorem computableInPolyTime_inWidth (s : ℕ) :
    ComputableInPolyTime (fun a : DecoderArg => 4 + (s + colBits a.2.2 + timeBits a.2.2))
      encDecoderArg encUnary :=
  unary_add' (const 4) (computableInPolyTime_pWidth s)

private theorem computableInPolyTime_inWidthNat (s : ℕ) :
    ComputableInPolyTime (fun a : DecoderArg => 4 + (s + colBits a.2.2 + timeBits a.2.2))
      encDecoderArg encNat :=
  unary_to_binary.comp (computableInPolyTime_inWidth s)

private theorem computableInPolyTime_chainBase (s : ℕ) :
    ComputableInPolyTime
      (fun a : DecoderArg => Decoder.chainBase (4 + (s + colBits a.2.2 + timeBits a.2.2)))
      encDecoderArg encNat := by
  unfold Decoder.chainBase
  exact binary_add' (binary_mul' (const 2) (computableInPolyTime_inWidthNat s)) (const 2)

private theorem computableInPolyTime_treeBase (s : ℕ) :
    ComputableInPolyTime
      (fun a : DecoderArg =>
        Decoder.treeBase (4 + (s + colBits a.2.2 + timeBits a.2.2))
          (s + colBits a.2.2 + timeBits a.2.2))
      encDecoderArg encNat := by
  unfold Decoder.treeBase
  exact binary_add' (computableInPolyTime_chainBase s)
    (binary_mul' (const 14) (computableInPolyTime_pWidthNat s))

private theorem computableInPolyTime_chainFields (s j : ℕ) :
    let fn := fun a : DecoderArg =>
      Decoder.chain s (colBits a.2.2) (timeBits a.2.2) a.1.length a.2.1 a.2.2 j
    ComputableInPolyTime (fun a => (fn a).K) encDecoderArg encNat ∧
    ComputableInPolyTime (fun a => (fn a).gt) encDecoderArg encBool ∧
    ComputableInPolyTime (fun a => (fn a).init) encDecoderArg encBool ∧
    ComputableInPolyTime (fun a => (fn a).off) encDecoderArg encNat ∧
    ComputableInPolyTime (fun a => (fn a).width) encDecoderArg encNat := by
  have hx : ComputableInPolyTime (fun a : DecoderArg => a.1) encDecoderArg encBits := fst _ _
  have hn : ComputableInPolyTime (fun a : DecoderArg => a.2.1) encDecoderArg encNat :=
    (fst _ _).comp (snd _ _)
  have hT := computableInPolyTime_argT
  have hxlen : ComputableInPolyTime (fun a : DecoderArg => a.1.length) encDecoderArg encNat :=
    unary_to_binary.comp (length_bits_comp hx)
  have hcbB := unary_to_binary.comp (computableInPolyTime_colBits hT)
  have htbB := unary_to_binary.comp (computableInPolyTime_timeBits hT)
  have hP := computableInPolyTime_pWidth s
  have hPB := computableInPolyTime_pWidthNat s
  have hoff2 := binary_add' (const (4 + s)) hcbB
  have hK1 : ComputableInPolyTime
      (fun a : DecoderArg => 2 ^ (s + colBits a.2.2 + timeBits a.2.2) - 1)
      encDecoderArg encNat :=
    (binary_sub' (binary_two_pow.comp hP) (const 1)).of_enc_eq fun _ => rfl
  have hK5 := binary_add' hn (const 1)
  have hK6 := binary_mul' (const 2) hT
  by_cases h0 : j = 0
  · subst h0
    simp only [Decoder.chain, ↓reduceIte]
    exact ⟨const _, const _, const _, const _, hcbB⟩
  by_cases h1 : j = 1
  · subst h1; simp only [Decoder.chain, one_ne_zero, ↓reduceIte]
    exact ⟨hK1, const _, const _, const _, hcbB⟩
  by_cases h2 : j = 2
  · subst h2; simp only [Decoder.chain, show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega,
      ↓reduceIte]
    exact ⟨const _, const _, const _, hoff2, htbB⟩
  by_cases h3 : j = 3
  · subst h3; simp only [Decoder.chain, show (3 : ℕ) ≠ 0 by omega, show (3 : ℕ) ≠ 1 by omega,
      show (3 : ℕ) ≠ 2 by omega, ↓reduceIte]
    exact ⟨const _, const _, const _, const _, hcbB⟩
  by_cases h4 : j = 4
  · subst h4; simp only [Decoder.chain, show (4 : ℕ) ≠ 0 by omega, show (4 : ℕ) ≠ 1 by omega,
      show (4 : ℕ) ≠ 2 by omega, show (4 : ℕ) ≠ 3 by omega, ↓reduceIte]
    exact ⟨hn, const _, const _, const _, hcbB⟩
  by_cases h5 : j = 5
  · subst h5; simp only [Decoder.chain, show (5 : ℕ) ≠ 0 by omega, show (5 : ℕ) ≠ 1 by omega,
      show (5 : ℕ) ≠ 2 by omega, show (5 : ℕ) ≠ 3 by omega, show (5 : ℕ) ≠ 4 by omega, ↓reduceIte]
    exact ⟨hK5, const _, const _, const _, hcbB⟩
  by_cases h6 : j = 6
  · subst h6; simp only [Decoder.chain, show (6 : ℕ) ≠ 0 by omega, show (6 : ℕ) ≠ 1 by omega,
      show (6 : ℕ) ≠ 2 by omega, show (6 : ℕ) ≠ 3 by omega, show (6 : ℕ) ≠ 4 by omega,
      show (6 : ℕ) ≠ 5 by omega, ↓reduceIte]
    exact ⟨hK6, const _, const _, const _, hcbB⟩
  by_cases h7 : j = 7
  · subst h7; simp only [Decoder.chain, show (7 : ℕ) ≠ 0 by omega, show (7 : ℕ) ≠ 1 by omega,
      show (7 : ℕ) ≠ 2 by omega, show (7 : ℕ) ≠ 3 by omega, show (7 : ℕ) ≠ 4 by omega,
      show (7 : ℕ) ≠ 5 by omega, show (7 : ℕ) ≠ 6 by omega, ↓reduceIte]
    exact ⟨hK6, const _, const _, const _, hcbB⟩
  by_cases h8 : j = 8
  · subst h8; simp only [Decoder.chain, show (8 : ℕ) ≠ 0 by omega, show (8 : ℕ) ≠ 1 by omega,
      show (8 : ℕ) ≠ 2 by omega, show (8 : ℕ) ≠ 3 by omega, show (8 : ℕ) ≠ 4 by omega,
      show (8 : ℕ) ≠ 5 by omega, show (8 : ℕ) ≠ 6 by omega, show (8 : ℕ) ≠ 7 by omega, ↓reduceIte]
    exact ⟨hT, const _, const _, const _, hcbB⟩
  by_cases h9 : j = 9
  · subst h9; simp only [Decoder.chain, show (9 : ℕ) ≠ 0 by omega, show (9 : ℕ) ≠ 1 by omega,
      show (9 : ℕ) ≠ 2 by omega, show (9 : ℕ) ≠ 3 by omega, show (9 : ℕ) ≠ 4 by omega,
      show (9 : ℕ) ≠ 5 by omega, show (9 : ℕ) ≠ 6 by omega, show (9 : ℕ) ≠ 7 by omega,
      show (9 : ℕ) ≠ 8 by omega, ↓reduceIte]
    exact ⟨hT, const _, const _, const _, hcbB⟩
  by_cases h10 : j = 10
  · subst h10; simp only [Decoder.chain, show (10 : ℕ) ≠ 0 by omega, show (10 : ℕ) ≠ 1 by omega,
      show (10 : ℕ) ≠ 2 by omega, show (10 : ℕ) ≠ 3 by omega, show (10 : ℕ) ≠ 4 by omega,
      show (10 : ℕ) ≠ 5 by omega, show (10 : ℕ) ≠ 6 by omega, show (10 : ℕ) ≠ 7 by omega,
      show (10 : ℕ) ≠ 8 by omega, show (10 : ℕ) ≠ 9 by omega, ↓reduceIte]
    exact ⟨hT, const _, const _, hoff2, htbB⟩
  by_cases h11 : j = 11
  · subst h11; simp only [Decoder.chain, show (11 : ℕ) ≠ 0 by omega, show (11 : ℕ) ≠ 1 by omega,
      show (11 : ℕ) ≠ 2 by omega, show (11 : ℕ) ≠ 3 by omega, show (11 : ℕ) ≠ 4 by omega,
      show (11 : ℕ) ≠ 5 by omega, show (11 : ℕ) ≠ 6 by omega, show (11 : ℕ) ≠ 7 by omega,
      show (11 : ℕ) ≠ 8 by omega, show (11 : ℕ) ≠ 9 by omega, show (11 : ℕ) ≠ 10 by omega,
      ↓reduceIte]
    exact ⟨hxlen, const _, const _, const _, hPB⟩
  by_cases h12 : j = 12
  · subst h12; simp only [Decoder.chain, show (12 : ℕ) ≠ 0 by omega, show (12 : ℕ) ≠ 1 by omega,
      show (12 : ℕ) ≠ 2 by omega, show (12 : ℕ) ≠ 3 by omega, show (12 : ℕ) ≠ 4 by omega,
      show (12 : ℕ) ≠ 5 by omega, show (12 : ℕ) ≠ 6 by omega, show (12 : ℕ) ≠ 7 by omega,
      show (12 : ℕ) ≠ 8 by omega, show (12 : ℕ) ≠ 9 by omega, show (12 : ℕ) ≠ 10 by omega,
      show (12 : ℕ) ≠ 11 by omega, ↓reduceIte]
    exact ⟨const _, const _, const _, const _, hPB⟩
  · simp only [Decoder.chain, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, ↓reduceIte]
    exact ⟨const _, const _, const _, const _, hPB⟩

private theorem computableInPolyTime_fieldGates (s : ℕ) :
    ComputableInPolyTime
      (fun a : DecoderArg =>
        Decoder.fieldGates s (colBits a.2.2) (timeBits a.2.2) a.1 a.2.1 a.2.2)
      encDecoderArg (encList encGate) := by
  have hx : ComputableInPolyTime (fun a : DecoderArg => a.1) encDecoderArg encBits := fst _ _
  have hxlenU : ComputableInPolyTime (fun a : DecoderArg => a.1.length) encDecoderArg encUnary :=
    length_bits_comp hx
  have hP := computableInPolyTime_pWidth s
  have hN := computableInPolyTime_inWidth s
  have hNB := computableInPolyTime_inWidthNat s
  have hPB := computableInPolyTime_pWidthNat s
  have hm : ComputableInPolyTime (fun a : DecoderArg => Nat.size a.1.length)
      encDecoderArg encUnary := binary_size.comp (unary_to_binary.comp hxlenU)
  -- Region 1: constants false and true.
  have hconst : ComputableInPolyTime (fun _ : DecoderArg =>
      [(.const false, ([] : List ℕ)), (.const true, [])]) encDecoderArg (encList encGate) :=
    const _
  -- Region 2: negations of inputs.
  have hnot : ComputableInPolyTime (fun a : DecoderArg =>
      (List.range (4 + (s + colBits a.2.2 + timeBits a.2.2))).map (fun i => (Op.not, [i])))
      encDecoderArg (encList encGate) := by
    refine mapWithInput (range.comp hN) ?_
    have hi : ComputableInPolyTime (fun p : DecoderArg × ℕ => p.2)
        (encPair encDecoderArg encUnary) encNat := unary_to_binary.comp (snd _ _)
    exact (const Op.not).prod (hi.cons' (const []))
  -- Region 3: fourteen comparison chains.
  have hchains : ComputableInPolyTime (fun a : DecoderArg =>
      (List.range 14).flatMap fun j =>
        (List.range (s + colBits a.2.2 + timeBits a.2.2)).map
          (Decoder.chainGate (4 + (s + colBits a.2.2 + timeBits a.2.2))
            (s + colBits a.2.2 + timeBits a.2.2) j
            (Decoder.chain s (colBits a.2.2) (timeBits a.2.2) a.1.length a.2.1 a.2.2 j)))
      encDecoderArg (encList encGate) := by
    refine flatMapConst (List.range 14) fun j _ => ?_
    refine mapWithInput (range.comp hP) ?_
    have ha : ComputableInPolyTime (fun p : DecoderArg × ℕ => p.1)
        (encPair encDecoderArg encUnary) encDecoderArg := fst _ _
    have hiU : ComputableInPolyTime (fun p : DecoderArg × ℕ => p.2)
        (encPair encDecoderArg encUnary) encUnary := snd _ _
    have hiB : ComputableInPolyTime (fun p : DecoderArg × ℕ => p.2)
        (encPair encDecoderArg encUnary) encNat := unary_to_binary.comp hiU
    obtain ⟨hKa0, hgt0, hinit0, hoff0, hwidth0⟩ := computableInPolyTime_chainFields s j
    have hKa := hKa0.comp ha
    have hgt := hgt0.comp ha
    have hinit := hinit0.comp ha
    have hoff := hoff0.comp ha
    have hwidth := hwidth0.comp ha
    have haN := hNB.comp ha
    have haP := hPB.comp ha
    have hbit : ComputableInPolyTime (fun p : DecoderArg × ℕ =>
        (Decoder.chain s (colBits p.1.2.2) (timeBits p.1.2.2)
          p.1.1.length p.1.2.1 p.1.2.2 j).K.testBit p.2)
        (encPair encDecoderArg encUnary) encBool := binary_testBit hKa hiU
    have hop : ComputableInPolyTime (fun p : DecoderArg × ℕ =>
        Decoder.andOr ((Decoder.chain s (colBits p.1.2.2) (timeBits p.1.2.2)
          p.1.1.length p.1.2.1 p.1.2.2 j).K.testBit p.2 ^^
          (Decoder.chain s (colBits p.1.2.2) (timeBits p.1.2.2)
            p.1.1.length p.1.2.1 p.1.2.2 j).gt))
        (encPair encDecoderArg encUnary) encOp :=
      (of_finite (encIn := encBool) (encOut := encOp) Decoder.andOr).comp
        (bool_xor.comp (hbit.prod hgt))
    have hoffi := binary_add' hoff hiB
    have harg0 := ite_decide (binary_lt' hiB hwidth)
      (ite' hgt hoffi (binary_add' (binary_add' haN (const 2)) hoffi))
      (ite' hgt haN (binary_add' haN (const 1)))
    have hcbB := binary_add' (binary_mul' (const 2) haN) (const 2)
    have harg1 := ite_decide (decide_eq' hiB (const 0))
      (ite' hinit (binary_add' haN (const 1)) haN)
      (binary_add' (binary_add' hcbB (binary_mul' (const j) haP)) (binary_sub' hiB (const 1)))
    have hg : ComputableInPolyTime (fun p : DecoderArg × ℕ =>
        Decoder.chainGate (4 + (s + colBits p.1.2.2 + timeBits p.1.2.2))
          (s + colBits p.1.2.2 + timeBits p.1.2.2) j
          (Decoder.chain s (colBits p.1.2.2) (timeBits p.1.2.2)
            p.1.1.length p.1.2.1 p.1.2.2 j) p.2)
        (encPair encDecoderArg encUnary) encGate := by
      unfold Decoder.chainGate Decoder.chainBase
      exact hop.prod (harg0.cons' (harg1.cons' (const [])))
    exact hg
  -- Region 4: decoder tree on `m = Nat.size a.1.length`, with `2 ^ ℓ ≤ 2 * a.1.length + 1`.
  have htree : ComputableInPolyTime (fun a : DecoderArg =>
      Decoder.treeGates (4 + (s + colBits a.2.2 + timeBits a.2.2))
        (Decoder.treeBase (4 + (s + colBits a.2.2 + timeBits a.2.2))
          (s + colBits a.2.2 + timeBits a.2.2))
        (Nat.size a.1.length))
      encDecoderArg (encList encGate) := by
    let treeBounded (a : DecoderArg) : List (Op × List ℕ) :=
      (List.range (Nat.size a.1.length + 1)).flatMap fun ℓ =>
        (List.range (min (2 * a.1.length + 1) (2 ^ ℓ))).map
          (Decoder.treeGate (4 + (s + colBits a.2.2 + timeBits a.2.2))
            (Decoder.treeBase (4 + (s + colBits a.2.2 + timeBits a.2.2))
              (s + colBits a.2.2 + timeBits a.2.2)) ℓ)
    have hteq' (a : DecoderArg) :
        Decoder.treeGates (4 + (s + colBits a.2.2 + timeBits a.2.2))
          (Decoder.treeBase (4 + (s + colBits a.2.2 + timeBits a.2.2))
            (s + colBits a.2.2 + timeBits a.2.2))
          (Nat.size a.1.length) = treeBounded a := by
      unfold Decoder.treeGates treeBounded
      refine List.flatMap_congr fun ℓ hℓ => ?_
      rw [List.mem_range] at hℓ
      have hm_pow : 2 ^ a.1.length.size ≤ 2 * a.1.length + 1 := by
        rcases eq_or_ne a.1.length 0 with h0 | hne
        · simp [h0]
        · rw [Nat.size_eq_log_two_add_one hne, Nat.pow_succ']
          have hlog := Nat.pow_log_le_self 2 hne
          omega
      have hle : 2 ^ ℓ ≤ 2 * a.1.length + 1 :=
        (Nat.pow_le_pow_right (by norm_num) (by omega)).trans hm_pow
      rw [min_eq_right hle]
    rw [show (fun a : DecoderArg =>
        Decoder.treeGates (4 + (s + colBits a.2.2 + timeBits a.2.2))
          (Decoder.treeBase (4 + (s + colBits a.2.2 + timeBits a.2.2))
            (s + colBits a.2.2 + timeBits a.2.2))
          (Nat.size a.1.length)) = treeBounded from funext hteq']
    refine flatMapWithInput (range.comp (unary_add' hm (const 1))) ?_
    have ha : ComputableInPolyTime (fun p : DecoderArg × ℕ => p.1)
        (encPair encDecoderArg encUnary) encDecoderArg := fst _ _
    have hℓU : ComputableInPolyTime (fun p : DecoderArg × ℕ => p.2)
        (encPair encDecoderArg encUnary) encUnary := snd _ _
    have hcap : ComputableInPolyTime (fun p : DecoderArg × ℕ => 2 * p.1.1.length + 1)
        (encPair encDecoderArg encUnary) encUnary :=
      unary_add' (unary_mul' (const 2) (hxlenU.comp ha)) (const 1)
    have hpow2U : ComputableInPolyTime (fun p : DecoderArg × ℕ =>
        min (2 * p.1.1.length + 1) (2 ^ p.2))
        (encPair encDecoderArg encUnary) encUnary :=
      binary_min_unary' hcap (binary_two_pow.comp hℓU)
    refine mapWithInput (range.comp hpow2U) ?_
    let encQ := encPair (encPair encDecoderArg encUnary) encUnary
    have hp : ComputableInPolyTime (fun q : (DecoderArg × ℕ) × ℕ => q.1.1) encQ encDecoderArg :=
      (fst _ _).comp (fst _ _)
    have hℓU' : ComputableInPolyTime (fun q : (DecoderArg × ℕ) × ℕ => q.1.2) encQ encUnary :=
      (snd _ _).comp (fst _ _)
    have hqU' : ComputableInPolyTime (fun q : (DecoderArg × ℕ) × ℕ => q.2) encQ encUnary :=
      snd _ _
    have hqB' := unary_to_binary.comp hqU'
    have hℓ1U := unary_sub' hℓU' (const 1)
    have hℓ1B := unary_to_binary.comp hℓ1U
    have hpowPrev := binary_two_pow.comp hℓ1U
    have hN' := hNB.comp hp
    have htbB := (computableInPolyTime_treeBase s).comp hp
    have hbit : ComputableInPolyTime (fun q : (DecoderArg × ℕ) × ℕ => q.2.testBit (q.1.2 - 1))
        encQ encBool := binary_testBit hqB' hℓ1U
    have hbranch : ComputableInPolyTime (fun q : (DecoderArg × ℕ) × ℕ =>
        Decoder.treeGate (4 + (s + colBits q.1.1.2.2 + timeBits q.1.1.2.2))
          (Decoder.treeBase (4 + (s + colBits q.1.1.2.2 + timeBits q.1.1.2.2))
            (s + colBits q.1.1.2.2 + timeBits q.1.1.2.2))
          q.1.2 q.2) encQ encGate := by
      unfold Decoder.treeGate
      have ha0 := binary_add' (binary_add' htbB (binary_sub' hpowPrev (const 1)))
        (binary_mod' hqB' hpowPrev)
      have ha1 := ite' hbit
        (binary_add' (const 4) hℓ1B)
        (binary_add' (binary_add' hN' (const 2)) (binary_add' (const 4) hℓ1B))
      exact ite_decide (unary_eq' hℓU' (const 0))
        (const (Op.const true, ([] : List ℕ)))
        ((const Op.and).prod (ha0.cons' (ha1.cons' (const []))))
    exact hbranch
  -- Region 5: lookup chain across `x.length`.
  have hor : ComputableInPolyTime (fun a : DecoderArg =>
      (List.range a.1.length).map (Decoder.orGate
        (4 + (s + colBits a.2.2 + timeBits a.2.2))
        (Decoder.treeBase (4 + (s + colBits a.2.2 + timeBits a.2.2))
          (s + colBits a.2.2 + timeBits a.2.2))
        (Nat.size a.1.length)
        (Decoder.orBase (4 + (s + colBits a.2.2 + timeBits a.2.2))
          (s + colBits a.2.2 + timeBits a.2.2) (Nat.size a.1.length))
        a.1))
      encDecoderArg (encList encGate) := by
    refine mapWithInput (range.comp hxlenU) ?_
    let encP := encPair encDecoderArg encUnary
    have ha : ComputableInPolyTime (fun p : DecoderArg × ℕ => p.1) encP encDecoderArg := fst _ _
    have hiU : ComputableInPolyTime (fun p : DecoderArg × ℕ => p.2) encP encUnary := snd _ _
    have hiB := unary_to_binary.comp hiU
    have hxbit : ComputableInPolyTime (fun p : DecoderArg × ℕ => p.1.1.getD p.2 false)
        encP encBool := (bitsGetD false).comp ((hx.comp ha).prod hiU)
    have hmU := hm.comp ha
    have hpowm := binary_two_pow.comp hmU
    have hpowm1 := binary_two_pow.comp (unary_add' hmU (const 1))
    have haN := hNB.comp ha
    have htb := (computableInPolyTime_treeBase s).comp ha
    have hob : ComputableInPolyTime (fun p : DecoderArg × ℕ =>
        Decoder.orBase (4 + (s + colBits p.1.2.2 + timeBits p.1.2.2))
          (s + colBits p.1.2.2 + timeBits p.1.2.2) (Nat.size p.1.1.length)) encP encNat := by
      unfold Decoder.orBase
      exact binary_add' htb (binary_sub' hpowm1 (const 1))
    have hor1 : ComputableInPolyTime (fun p : DecoderArg × ℕ =>
        Decoder.orGate (4 + (s + colBits p.1.2.2 + timeBits p.1.2.2))
          (Decoder.treeBase (4 + (s + colBits p.1.2.2 + timeBits p.1.2.2))
            (s + colBits p.1.2.2 + timeBits p.1.2.2))
          (Nat.size p.1.1.length)
          (Decoder.orBase (4 + (s + colBits p.1.2.2 + timeBits p.1.2.2))
            (s + colBits p.1.2.2 + timeBits p.1.2.2) (Nat.size p.1.1.length))
          p.1.1 p.2) encP encGate := by
      unfold Decoder.orGate
      have ha0 := ite_decide (decide_eq' hiB (const 0)) haN
        (binary_add' hob (binary_sub' hiB (const 1)))
      have ha1 := ite' hxbit
        (binary_add' (binary_add' htb (binary_sub' hpowm (const 1))) hiB) haN
      exact (const Op.or).prod (ha0.cons' (ha1.cons' (const [])))
    exact hor1
  -- Combine all five gate regions.
  have h12 := (listAppend encGate).comp (hconst.prod hnot)
  have h123 := (listAppend encGate).comp (h12.prod hchains)
  have h1234 := (listAppend encGate).comp (h123.prod htree)
  exact ((listAppend encGate).comp (h1234.prod hor)).of_enc_eq fun _ => rfl

private theorem computableInPolyTime_aWidth (s : ℕ) :
    ComputableInPolyTime
      (fun a : DecoderArg => Decoder.aWidth s (colBits a.2.2) (timeBits a.2.2) a.1 a.2.1 a.2.2)
      encDecoderArg encUnary := by
  unfold Decoder.aWidth
  exact unary_add' (computableInPolyTime_inWidth s)
    ((length_list encGate).comp (computableInPolyTime_fieldGates s))

private theorem computableInPolyTime_aWidthNat (s : ℕ) :
    ComputableInPolyTime
      (fun a : DecoderArg => Decoder.aWidth s (colBits a.2.2) (timeBits a.2.2) a.1 a.2.1 a.2.2)
      encDecoderArg encNat :=
  unary_to_binary.comp (computableInPolyTime_aWidth s)

private theorem computableInPolyTime_wireNat (s : ℕ) (j : Fin 28) :
    ComputableInPolyTime
      (fun p : DecoderArg × ℕ =>
        Decoder.wireNat s (colBits p.1.2.2) (timeBits p.1.2.2) p.1.1 p.1.2.1 p.1.2.2 p.2 j)
      (encPair encDecoderArg encUnary) encNat := by
  let encP := encPair encDecoderArg encUnary
  have ha : ComputableInPolyTime (fun p : DecoderArg × ℕ => p.1) encP encDecoderArg := fst _ _
  have hoU : ComputableInPolyTime (fun p : DecoderArg × ℕ => p.2) encP encUnary := snd _ _
  have hx : ComputableInPolyTime (fun p : DecoderArg × ℕ => p.1.1) encP encBits :=
    (fst _ _).comp ha
  have hT := computableInPolyTime_argT.comp ha
  have h2T := binary_mul' (const 2) hT
  have hcbU := computableInPolyTime_colBits hT
  have htbU := computableInPolyTime_timeBits hT
  have hcbB := unary_to_binary.comp hcbU
  have htbB := unary_to_binary.comp htbU
  have hPU := (computableInPolyTime_pWidth s).comp ha
  have hPB := (computableInPolyTime_pWidthNat s).comp ha
  have hNB := (computableInPolyTime_inWidthNat s).comp ha
  have haWB := (computableInPolyTime_aWidthNat s).comp ha
  have hcb_base := (computableInPolyTime_chainBase s).comp ha
  have htbB_base := (computableInPolyTime_treeBase s).comp ha
  have hmU := binary_size.comp (unary_to_binary.comp (length_bits_comp hx))
  have hpowm1 := binary_two_pow.comp (unary_add' hmU (const 1))
  have hob_base : ComputableInPolyTime
      (fun p : DecoderArg × ℕ =>
        Decoder.orBase (4 + (s + colBits p.1.2.2 + timeBits p.1.2.2))
          (s + colBits p.1.2.2 + timeBits p.1.2.2) (Nat.size p.1.1.length)) encP encNat := by
    unfold Decoder.orBase
    exact binary_add' htbB_base (binary_sub' hpowm1 (const 1))
  have hxlenB := unary_to_binary.comp (length_bits_comp hx)
  have hlook : ComputableInPolyTime
      (fun p : DecoderArg × ℕ =>
        Decoder.lookW s (colBits p.1.2.2) (timeBits p.1.2.2) p.1.1) encP encNat := by
    unfold Decoder.lookW
    exact ite_decide (decide_eq' hxlenB (const 0)) hNB
      (binary_add' hob_base (binary_sub' hxlenB (const 1)))
  have hstrideU := unary_add' (unary_add' (const 2) hPU) (const 1)
  have hlitU := unary_div' hoU hstrideU
  have hlitB := unary_to_binary.comp hlitU
  have hposU := unary_mod' hoU hstrideU
  have hposB := unary_to_binary.comp hposU
  have hqU := unary_sub' hposU (const 2)
  have hqB := unary_to_binary.comp hqU
  have hqsU := unary_sub' hqU (const s)
  have hqsB := unary_to_binary.comp hqsU
  have hqscU := unary_sub' hqsU hcbU
  have hqscB := unary_to_binary.comp hqscU
  have hbit2T := binary_testBit h2T hqsU
  have hbitT := binary_testBit hT hqscU
  have hmid (off : ℕ) := binary_add' (binary_add' haWB (binary_mul' hlitB (const (13 + s))))
    (const off)
  have hmidPos := binary_add' (binary_add' haWB (binary_mul' hlitB (const (13 + s)))) hposB
  have hconstW {b : DecoderArg × ℕ → Bool} (hb : ComputableInPolyTime b encP encBool) :=
    ite' hb (binary_add' hNB (const 1)) hNB
  have hbitW {hoff hw hq : DecoderArg × ℕ → ℕ}
      (hOff : ComputableInPolyTime hoff encP encNat)
      (hW : ComputableInPolyTime hw encP encNat)
      (hQ : ComputableInPolyTime hq encP encNat) :=
    ite_decide (binary_lt' hQ hW) (binary_add' hOff hQ) hNB
  have hchainW (k : ℕ) {hq : DecoderArg × ℕ → ℕ}
      (hQ : ComputableInPolyTime hq encP encNat) :=
    ite_decide (decide_eq' hQ (const 0)) (binary_add' hNB (const 1))
      (binary_add' (binary_add' hcb_base (binary_mul' (const k) hPB)) (binary_sub' hQ (const 1)))
  have hs_le_q := decide_and (unary_le' (const s) hqU) (unary_lt' hqU (unary_add' (const s) hcbU))
  have hsc_le_q := unary_le' (unary_add' (const s) hcbU) hqU
  let kk := (j.val - 1) / 3
  have huW : ComputableInPolyTime
      (fun p : DecoderArg × ℕ =>
        Decoder.uWire s (colBits p.1.2.2) (timeBits p.1.2.2) p.1.2.2
          (p.2 % (2 + (s + colBits p.1.2.2 + timeBits p.1.2.2) + 1) - 2) kk) encP encNat := by
    by_cases hk0 : kk = 0
    · simp only [Decoder.uWire, eq_true hk0, ↓reduceIte]
      exact binary_add' (const 4) hqB
    by_cases hk1 : kk = 1
    · simp only [Decoder.uWire, eq_false hk0, eq_true hk1, ↓reduceIte, Decoder.bitW]
      exact hbitW (const (4 + s)) hcbB hqB
    by_cases hk5le : kk ≤ 5
    · by_cases hk5 : kk = 5
      · simp only [Decoder.uWire, eq_false hk0, eq_false hk1, eq_true hk5le, eq_true hk5,
          ↓reduceIte, Decoder.constW]
        exact ite_decide hs_le_q (hconstW hbit2T) hNB
      · simp only [Decoder.uWire, eq_false hk0, eq_false hk1, eq_true hk5le, eq_false hk5,
          ↓reduceIte, Decoder.bitW]
        exact ite_decide hs_le_q (hbitW (const (4 + s)) hcbB hqsB) hNB
    by_cases hk8le : kk ≤ 8
    · by_cases hk8 : kk = 8
      · simp only [Decoder.uWire, eq_false hk0, eq_false hk1, eq_false hk5le, eq_true hk8le,
          eq_true hk8, ↓reduceIte, Decoder.constW]
        exact ite_decide hsc_le_q (hconstW hbitT) hNB
      · simp only [Decoder.uWire, eq_false hk0, eq_false hk1, eq_false hk5le, eq_true hk8le,
          eq_false hk8, ↓reduceIte, Decoder.bitW]
        exact ite_decide hsc_le_q (hbitW (binary_add' (const (4 + s)) hcbB) htbB hqscB) hNB
    · simp only [Decoder.uWire, eq_false hk0, eq_false hk1, eq_false hk5le, eq_false hk8le,
        ↓reduceIte]
      exact hNB
  have hvW : ComputableInPolyTime
      (fun p : DecoderArg × ℕ =>
        Decoder.vWire s (colBits p.1.2.2) (timeBits p.1.2.2)
          (p.2 % (2 + (s + colBits p.1.2.2 + timeBits p.1.2.2) + 1) - 2) kk) encP encNat := by
    by_cases hk1 : kk = 1
    · simp only [Decoder.vWire, eq_true hk1, ↓reduceIte, Decoder.chainW]
      exact hchainW 0 hqB
    by_cases hk3 : kk = 3
    · simp only [Decoder.vWire, eq_false hk1, eq_true hk3, ↓reduceIte, Decoder.chainW]
      exact ite_decide hs_le_q (hchainW 0 hqsB) hNB
    by_cases hk4 : kk = 4
    · simp only [Decoder.vWire, eq_false hk1, eq_false hk3, eq_true hk4, ↓reduceIte,
        Decoder.chainW]
      exact ite_decide hs_le_q (hchainW 1 hqsB) hNB
    by_cases hk7 : kk = 7
    · simp only [Decoder.vWire, eq_false hk1, eq_false hk3, eq_false hk4, eq_true hk7, ↓reduceIte,
        Decoder.chainW]
      exact ite_decide hsc_le_q (hchainW 2 hqscB) hNB
    · simp only [Decoder.vWire, eq_false hk1, eq_false hk3, eq_false hk4, eq_false hk7, ↓reduceIte]
      exact hNB
  unfold Decoder.wireNat
  exact ite_decide (unary_lt' hposU (const 2))
    (ite_decide (const (decide (j.val = 0))) hmidPos hNB)
    (ite_decide (unary_lt' hposU (unary_add' (const 2) hPU))
      (ite_decide (const (decide (j.val = 0)))
        (ite_decide (unary_lt' hqU (const s)) hmidPos hNB)
        (ite_decide (const (decide ((j.val - 1) % 3 = 0)))
          (hmid (2 + s + kk))
          (ite_decide (const (decide ((j.val - 1) % 3 = 1))) huW hvW)))
      (ite_decide (const (decide (j.val = 0))) (hmid (2 + s + 9))
        (ite_decide (const (decide (j.val = 1))) (hmid (2 + s + 10))
          (ite_decide (const (decide (j.val = 2))) hlook hNB))))

private theorem computableInPolyTime_keyWires (k : ℕ) (State : Type) [Fintype State] :
    ComputableInPolyTime (fun a : DecoderArg =>
      (([] : List (Op × List ℕ)),
        (List.range (4 + slotBits k State + 14)).map
          (Decoder.keyWire (slotBits k State) (colBits a.2.2) (timeBits a.2.2))))
      encDecoderArg encCode := by
  have hPB := computableInPolyTime_pWidthNat (slotBits k State)
  have hcbB := computableInPolyTime_chainBase (slotBits k State)
  refine (const []).prod (mapConst (List.range (4 + slotBits k State + 14)) fun i _ => ?_)
  unfold Decoder.keyWire
  split_ifs
  · exact const _
  · exact binary_add'
      (binary_add' hcbB (binary_mul' (const (i - (4 + slotBits k State))) hPB))
      (binary_sub' hPB (const 1))

private theorem computableInPolyTime_midCode {k : ℕ} {State : Type} [Fintype State]
    [DecidableEq State] (tm : MultiTapeTM k Bool State) :
    ComputableInPolyTime (fun a : DecoderArg =>
      compCode (4 + (slotBits k State + colBits a.2.2 + timeBits a.2.2))
        (appendCode (Decoder.aWidth (slotBits k State) (colBits a.2.2) (timeBits a.2.2)
            a.1 a.2.1 a.2.2)
          ([], List.range (Decoder.aWidth (slotBits k State) (colBits a.2.2) (timeBits a.2.2)
            a.1 a.2.1 a.2.2))
          (compCode (Decoder.aWidth (slotBits k State) (colBits a.2.2) (timeBits a.2.2)
              a.1 a.2.1 a.2.2)
            (Decoder.tableCircuit tm).code
            ([], (List.range (4 + slotBits k State + 14)).map
              (Decoder.keyWire (slotBits k State) (colBits a.2.2) (timeBits a.2.2)))))
        (Decoder.fieldGates (slotBits k State) (colBits a.2.2) (timeBits a.2.2) a.1 a.2.1 a.2.2,
          List.range (Decoder.aWidth (slotBits k State) (colBits a.2.2) (timeBits a.2.2)
            a.1 a.2.1 a.2.2)))
      encDecoderArg encCode := by
  have hNB := computableInPolyTime_inWidthNat (slotBits k State)
  have haW := computableInPolyTime_aWidth (slotBits k State)
  have haWB := computableInPolyTime_aWidthNat (slotBits k State)
  have haRange : ComputableInPolyTime
      (fun a : DecoderArg =>
        List.range (Decoder.aWidth (slotBits k State) (colBits a.2.2) (timeBits a.2.2)
          a.1 a.2.1 a.2.2))
      encDecoderArg (encList encNat) :=
    (mapWith (unary_to_binary.comp (snd encBool encUnary)) (const true)
      (range.comp haW)).of_enc_eq fun _ => congrArg (encList encNat) (by simp)
  have hfieldCode := (computableInPolyTime_fieldGates (slotBits k State)).prod haRange
  have hconstT : ComputableInPolyTime (fun _ : DecoderArg => (Decoder.tableCircuit tm).code)
      encDecoderArg encCode := const _
  have hid : ComputableInPolyTime (fun a : DecoderArg =>
      (([] : List (Op × List ℕ)),
        List.range (Decoder.aWidth (slotBits k State) (colBits a.2.2) (timeBits a.2.2)
          a.1 a.2.1 a.2.2)))
      encDecoderArg encCode :=
    (const (encOut := encList encGate) []).prod haRange
  have h1 := computableInPolyTime_compCode haWB hconstT (computableInPolyTime_keyWires k State)
  have h2 := computableInPolyTime_appendCode haWB hid h1
  exact computableInPolyTime_compCode hNB h2 hfieldCode

private theorem computableInPolyTime_outStage (k : ℕ) (State : Type) [Fintype State] :
    ComputableInPolyTime (fun a : DecoderArg =>
      appendCodes (Decoder.aWidth (slotBits k State) (colBits a.2.2) (timeBits a.2.2)
          a.1 a.2.1 a.2.2 + 3 * (13 + slotBits k State))
        ((List.range (3 * (2 + (slotBits k State + colBits a.2.2 + timeBits a.2.2) + 1))).map
          fun o => formulaCode (Decoder.aWidth (slotBits k State) (colBits a.2.2) (timeBits a.2.2)
              a.1 a.2.1 a.2.2 + 3 * (13 + slotBits k State))
            Decoder.outTemplate
            (fun j => Decoder.wireNat (slotBits k State) (colBits a.2.2) (timeBits a.2.2)
              a.1 a.2.1 a.2.2 o j)))
      encDecoderArg encCode := by
  have hP := computableInPolyTime_pWidth (slotBits k State)
  have haWB := computableInPolyTime_aWidthNat (slotBits k State)
  have houtCount : ComputableInPolyTime (fun a : DecoderArg =>
      3 * (2 + (slotBits k State + colBits a.2.2 + timeBits a.2.2) + 1))
      encDecoderArg encUnary :=
    unary_mul' (const 3) (unary_add' (unary_add' (const 2) hP) (const 1))
  have houtBlocks : ComputableInPolyTime (fun a : DecoderArg =>
      (List.range (3 * (2 + (slotBits k State + colBits a.2.2 + timeBits a.2.2) + 1))).map
        fun o => formulaCode (Decoder.aWidth (slotBits k State) (colBits a.2.2) (timeBits a.2.2)
            a.1 a.2.1 a.2.2 + 3 * (13 + slotBits k State))
          Decoder.outTemplate
          (fun j => Decoder.wireNat (slotBits k State) (colBits a.2.2) (timeBits a.2.2)
            a.1 a.2.1 a.2.2 o j))
      encDecoderArg (encList encCode) := by
    refine mapWithInput (range.comp houtCount) ?_
    have hwidth : ComputableInPolyTime (fun p : DecoderArg × ℕ =>
        Decoder.aWidth (slotBits k State) (colBits p.1.2.2) (timeBits p.1.2.2)
          p.1.1 p.1.2.1 p.1.2.2 + 3 * (13 + slotBits k State))
        (encPair encDecoderArg encUnary) encNat :=
      binary_add' (haWB.comp (fst _ _)) (const (3 * (13 + slotBits k State)))
    exact computableInPolyTime_formulaCode Decoder.outTemplate hwidth
      (computableInPolyTime_wireNat (slotBits k State))
  exact computableInPolyTime_appendCodes
    (binary_add' haWB (const (3 * (13 + slotBits k State)))) houtBlocks

/-- **Uniform polynomial-time construction of the succinct tableau decoder**: for every multi-tape
machine `tm`, `Tableau.Decoder.decoderCode tm (x, n, T)` is computable in polynomial time in
`x.length + (encNat n).length + (encNat T).length` (`O(|x| + log n + log T)`), without expanding
exponentially large runs or CNFs [Williams, Theorem 6.1][Williams2010]. -/
theorem computableInPolyTime_decoderCode {k : ℕ} {State : Type} [Fintype State] [DecidableEq State]
    (tm : MultiTapeTM k Bool State) :
    ComputableInPolyTime (Decoder.decoderCode tm)
      (encPair encBits (encPair encNat encNat)) encCode := by
  change ComputableInPolyTime (Decoder.decoderCode tm) encDecoderArg encCode
  refine (computableInPolyTime_compCode (computableInPolyTime_inWidthNat (slotBits k State))
    (computableInPolyTime_outStage k State) (computableInPolyTime_midCode tm)).of_enc_eq
      fun a => congrArg encCode ?_
  rcases a with ⟨x, n, T⟩
  rw [Decoder.decoderCode]

/-- Every native `NEXP` language has a polynomial-time succinct decoder. The gate code and both
unary address widths are computable in polynomial time. The frame length and clock bounds let
the caller relate the decoded clauses to the satisfiable tableau of the fixed machine. -/
theorem exists_succinctDecoder_of_mem_NEXP {α : Type} {enc : α ↪ List Bool} {A : Set α}
    (hA : A ∈ NEXP enc) :
    ∃ (k : ℕ) (State : Type) (_ : Fintype State) (_ : DecidableEq State)
      (tm : MultiTapeTM k Bool State) (n T : α → ℕ),
      ComputableInPolyTime (fun a => Decoder.decoderCode tm (frame (enc a), n a, T a))
        enc encCode ∧
      ComputableInPolyTime (fun a => Tableau.clauseBits k State (T a)) enc encUnary ∧
      ComputableInPolyTime (fun a => Tableau.labelBits k State (T a)) enc encUnary ∧
      ∀ a : α, (frame (enc a)).length ≤ n a ∧ n a < 2 * T a ∧
        (a ∈ A ↔ (Tableau.succinctCNF tm (frame (enc a)) (n a) (T a)).Satisfiable) ∧
        ∃ c : Circuit signature (Tableau.clauseBits k State (T a))
          (3 * (Tableau.labelBits k State (T a) + 1)),
          c.code = Decoder.decoderCode tm (frame (enc a), n a, T a) ∧
          c.size ≤ Decoder.sizeConst tm *
            (colBits (T a) + timeBits (T a) + (frame (enc a)).length + 1) ∧
          ∀ idx < 2 ^ Tableau.clauseBits k State (T a),
            List.ofFn (c.eval interpretation fun i => idx.testBit i) =
              (Tableau.clauseAt tm (frame (enc a)) (n a) (T a) idx).flatMap
                (Decoder.litBits (Tableau.labelBits k State (T a))) := by
  obtain ⟨k, State, hfin, hdecEq, tm, n, T, hn_pt, hT_pt, _, hmem⟩ :=
    exists_succinctCNF_of_mem_NEXP hA
  have henc : ComputableInPolyTime enc enc encBits := of_eq fun _ => rfl
  have hframe : ComputableInPolyTime (fun a => frame (enc a)) enc encBits := by fun_prop
  have harg : ComputableInPolyTime (fun a => (frame (enc a), n a, T a)) enc
      (encPair encBits (encPair encNat encNat)) :=
    hframe.prod (hn_pt.prod hT_pt)
  have hp := unary_add' (unary_add' (const (slotBits k State)) (computableInPolyTime_colBits hT_pt))
    (computableInPolyTime_timeBits hT_pt)
  have hQ : ComputableInPolyTime (fun a => Tableau.clauseBits k State (T a)) enc encUnary := by
    unfold Tableau.clauseBits
    exact unary_add' (const 4) hp
  have hL : ComputableInPolyTime (fun a => Tableau.labelBits k State (T a)) enc encUnary := by
    unfold Tableau.labelBits
    exact unary_add' (const 2) hp
  refine ⟨k, State, hfin, hdecEq, tm, n, T,
    (@computableInPolyTime_decoderCode k State hfin hdecEq tm).comp harg, hQ, hL, fun a => ?_⟩
  obtain ⟨hle, hlt, hsat⟩ := hmem a
  exact ⟨hle, hlt, hsat,
    @Decoder.exists_decoder k State hfin hdecEq tm (frame (enc a)) (n a) (T a) hlt hle⟩

end DecoderPolyTime

/-! ### Algebraic arithmetization of decoded succinct 3CNF formulas -/

section AlgebraicArith

/-- Field-valued semantics of a De Morgan gate operation `Op` on two ring elements:
`.const v ↦ bitVal R v`, `.not a _ ↦ 1 - a`, `.and a b ↦ a * b`, `.or a b ↦ a + b - a * b`. -/
def opEvalField {R : Type*} [CommRing R] : Op → R → R → R
  | .const v, _, _ => bitVal R v
  | .not, a, _ => 1 - a
  | .and, a, b => a * b
  | .or, a, b => a + b - a * b

@[simp] theorem opEvalField_bitVal {R : Type*} [CommRing R] (op : Op) (a b : Bool) :
    opEvalField op (bitVal R a) (bitVal R b) = bitVal R (op.value a b) := by
  cases op with
  | const v => cases v <;> simp [opEvalField, Op.value, bitVal]
  | not => cases a <;> cases b <;> simp [opEvalField, Op.value, bitVal]
  | and => cases a <;> cases b <;> simp [opEvalField, Op.value, bitVal]
  | or => cases a <;> cases b <;> simp [opEvalField, Op.value, bitVal]

@[simp] theorem map_opEvalField {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (op : Op) (a b : R) :
    φ (opEvalField op a b) = opEvalField op (φ a) (φ b) := by
  cases op with
  | const v => cases v <;> simp [opEvalField, bitVal]
  | not => simp [opEvalField]
  | and => simp [opEvalField]
  | or => simp [opEvalField]

/-- Multilinear bit-equality indicator `u * v + (1 - u) * (1 - v)`: equals `1` if `u = v` and `0`
if `u ≠ v` for `u, v ∈ {0, 1}`. -/
def eqBit {R : Type*} [CommRing R] (u v : R) : R :=
  u * v + (1 - u) * (1 - v)

@[simp] theorem eqBit_bitVal {R : Type*} [CommRing R] (a b : Bool) :
    eqBit (bitVal R a) (bitVal R b) = if a = b then 1 else 0 := by
  cases a <;> cases b <;> simp [eqBit, bitVal]

@[simp] theorem map_eqBit {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (u v : R) :
    φ (eqBit u v) = eqBit (φ u) (φ v) := by
  simp [eqBit]

/-- Variable `X ⟨w, _⟩` when `w < N`, and `0` otherwise. -/
noncomputable def wireX {R : Type*} [CommRing R] (N w : ℕ) : MvPolynomial (Fin N) R :=
  if h : w < N then X ⟨w, h⟩ else 0

/-- Polynomial checking that every gate `j < c.size` of a De Morgan circuit `c` satisfies its
algebraic gate equation on wires `(idx, w) ∈ F^{Q + c.size}`. -/
noncomputable def gateTracePoly {Q M : ℕ} (R : Type*) [CommRing R]
    (c : Circuit signature Q M) : MvPolynomial (Fin (Q + c.size)) R :=
  ∏ j : Fin c.size,
    let gate := c.code.1.getD j.val (.const false, [])
    let a := wireX (R := R) (Q + c.size) (gate.2.getD 0 0)
    let b := wireX (R := R) (Q + c.size) (gate.2.getD 1 0)
    eqBit (X ⟨Q + j.val, by omega⟩) (opEvalField gate.1 a b)

/-- Polynomial checking that all three decoded literals output by `c` are falsified under the
assignment polynomial `A : MvPolynomial (Fin L) R`. -/
noncomputable def clauseUnsatPoly {Q L : ℕ} {R : Type*} [CommRing R]
    (c : Circuit signature Q (3 * (L + 1))) (A : MvPolynomial (Fin L) R) :
    MvPolynomial (Fin (Q + c.size)) R :=
  ∏ r : Fin 3,
    let addr : Fin L → Fin (Q + c.size) :=
      fun i => ⟨(c.outputs (SuccinctVerifier.addressWire L r i)).toNat, Wire.toNat_lt _⟩
    let sign : MvPolynomial (Fin (Q + c.size)) R :=
      X ⟨(c.outputs (SuccinctVerifier.signWire L r)).toNat, Wire.toNat_lt _⟩
    let val : MvPolynomial (Fin (Q + c.size)) R := rename addr A
    sign * (1 - val) + (1 - sign) * val

/-- Multilinear equality indicator `∏ᵢ (rᵢ Xᵢ + (1 - rᵢ)(1 - Xᵢ))`: on Boolean `y`, evaluates to
`eval r (indicatorPoly y)`. -/
noncomputable def eqCubePoly {N : ℕ} {R : Type*} [CommRing R] (r : Fin N → R) :
    MvPolynomial (Fin N) R :=
  ∏ i : Fin N, (C (r i) * X i + C (1 - r i) * (1 - X i))

/-- Combined arithmetized constraint polynomial
`eqCubePoly r * gateTracePoly c * clauseUnsatPoly c A` for succinct 3CNF verification over `R`. -/
noncomputable def tableauConstraintPoly {Q L : ℕ} {R : Type*} [CommRing R]
    (c : Circuit signature Q (3 * (L + 1))) (A : MvPolynomial (Fin L) R)
    (r : Fin (Q + c.size) → R) : MvPolynomial (Fin (Q + c.size)) R :=
  eqCubePoly r * gateTracePoly R c * clauseUnsatPoly c A

/-! ### Degree bounds -/

private theorem totalDegree_wireX_le {R : Type*} [CommRing R] {N w : ℕ} :
    (wireX (R := R) N w).totalDegree ≤ 1 := by
  unfold wireX
  split_ifs with h
  · exact (totalDegree_monomial_le _ _).trans (by simp)
  · simp

private theorem totalDegree_opEvalField_le {R : Type*} [CommRing R] {op : Op} {N : ℕ}
    {a b : MvPolynomial (Fin N) R} (ha : a.totalDegree ≤ 1) (hb : b.totalDegree ≤ 1) :
    (opEvalField op a b).totalDegree ≤ 2 := by
  cases op with
  | const v =>
    unfold opEvalField
    cases v <;> simp [bitVal]
  | not => exact (totalDegree_sub _ _).trans (max_le (by simp) (ha.trans (by omega)))
  | and => exact (totalDegree_mul _ _).trans (by omega)
  | or =>
    refine (totalDegree_sub _ _).trans (max_le ((totalDegree_add _ _).trans (max_le
      (ha.trans (by omega)) (hb.trans (by omega)))) ((totalDegree_mul _ _).trans (by omega)))

/-- Every variable in `eqCubePoly r` has degree at most `1`. -/
theorem eqCubePoly_degreeOf_le {N : ℕ} {R : Type*} [CommRing R] (r : Fin N → R) (v : Fin N) :
    (eqCubePoly r).degreeOf v ≤ 1 := by
  unfold eqCubePoly
  refine (degreeOf_prod_le v _ _).trans ?_
  have hX (u v : Fin N) :
      degreeOf v (X u : MvPolynomial (Fin N) R) ≤ if u = v then 1 else 0 := by
    classical
    rw [degreeOf_def]
    exact (Multiset.count_le_of_le v (degrees_X' u)).trans (by
      by_cases huv : u = v
      · subst huv; simp
      · simp [huv, Ne.symm huv])
  have hone : degreeOf v (1 : MvPolynomial (Fin N) R) = 0 := by
    classical simp [degreeOf_def, degrees_one]
  calc ∑ i : Fin N, degreeOf v (C (r i) * X i + C (1 - r i) * (1 - X i))
      ≤ ∑ i : Fin N, (if i = v then 1 else 0) := Finset.sum_le_sum fun i _ => by
        refine (degreeOf_add_le v _ _).trans (max_le ?_ ?_)
        · refine (degreeOf_mul_le v _ _).trans ?_
          simpa [degreeOf_C] using hX i v
        · refine (degreeOf_mul_le v _ _).trans ?_
          have h1 : degreeOf v (1 - X i : MvPolynomial (Fin N) R) ≤ if i = v then 1 else 0 :=
            (degreeOf_sub_le v _ _).trans (max_le (by simp [hone]) (hX i v))
          simpa only [degreeOf_C, zero_add] using h1
    _ = 1 := by simp

/-- Total degree of `gateTracePoly R c` is at most `3 * c.size`. -/
theorem gateTracePoly_totalDegree_le {Q M : ℕ} (R : Type*) [CommRing R]
    (c : Circuit signature Q M) :
    (gateTracePoly R c).totalDegree ≤ 3 * c.size := by
  unfold gateTracePoly
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ j : Fin c.size,
        (eqBit (X (⟨Q + j.val, by omega⟩ : Fin (Q + c.size)))
          (opEvalField (c.code.1.getD j.val (.const false, [])).1
            (wireX (R := R) (Q + c.size) ((c.code.1.getD j.val (.const false, [])).2.getD 0 0))
            (wireX (R := R) (Q + c.size)
              ((c.code.1.getD j.val (.const false, [])).2.getD 1 0)))).totalDegree
      ≤ ∑ _j : Fin c.size, 3 := Finset.sum_le_sum fun j _ => by
        dsimp only
        have hw :
            (X ⟨Q + j.val, by omega⟩ : MvPolynomial (Fin (Q + c.size)) R).totalDegree ≤ 1 :=
          (totalDegree_monomial_le _ _).trans (by simp)
        have hg : (opEvalField (c.code.1.getD j.val (.const false, [])).1
            (wireX (R := R) (Q + c.size) ((c.code.1.getD j.val (.const false, [])).2.getD 0 0))
            (wireX (R := R) (Q + c.size)
              ((c.code.1.getD j.val (.const false, [])).2.getD 1 0))).totalDegree ≤ 2 :=
          totalDegree_opEvalField_le totalDegree_wireX_le totalDegree_wireX_le
        unfold eqBit
        refine (totalDegree_add _ _).trans (max_le ((totalDegree_mul _ _).trans (by omega)) ?_)
        refine (totalDegree_mul _ _).trans ?_
        have h1 : (1 - (X ⟨Q + j.val, by omega⟩ :
            MvPolynomial (Fin (Q + c.size)) R)).totalDegree ≤ 1 :=
          (totalDegree_sub _ _).trans (max_le (by simp) hw)
        have h2 : (1 - opEvalField (c.code.1.getD j.val (.const false, [])).1
            (wireX (R := R) (Q + c.size) ((c.code.1.getD j.val (.const false, [])).2.getD 0 0))
            (wireX (R := R) (Q + c.size)
              ((c.code.1.getD j.val (.const false, [])).2.getD 1 0))).totalDegree ≤ 2 :=
          (totalDegree_sub _ _).trans (max_le (by simp) hg)
        omega
    _ = 3 * c.size := by simp [Nat.mul_comm]

/-- If `A ∈ restrictDegree (Fin L) R 1`, then
`(clauseUnsatPoly c A).totalDegree ≤ 3 * (L + 1)`. -/
theorem clauseUnsatPoly_totalDegree_le {Q L : ℕ} {R : Type*} [CommRing R]
    (c : Circuit signature Q (3 * (L + 1))) {A : MvPolynomial (Fin L) R}
    (hA : A ∈ restrictDegree (Fin L) R 1) :
    (clauseUnsatPoly c A).totalDegree ≤ 3 * (L + 1) := by
  have hAtot : A.totalDegree ≤ L := by
    refine Finset.sup_le fun s hs => ?_
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    calc ∑ i : Fin L, s i
        ≤ ∑ _i : Fin L, 1 :=
          Finset.sum_le_sum fun i _ => (mem_restrictDegree _ _ 1).mp hA s hs i
      _ = L := by simp
  unfold clauseUnsatPoly
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ r : Fin 3, _ ≤ ∑ _r : Fin 3, (L + 1) := Finset.sum_le_sum fun r _ => by
        dsimp only
        let addr : Fin L → Fin (Q + c.size) :=
          fun i => ⟨(c.outputs (SuccinctVerifier.addressWire L r i)).toNat, Wire.toNat_lt _⟩
        let sign : MvPolynomial (Fin (Q + c.size)) R :=
          X ⟨(c.outputs (SuccinctVerifier.signWire L r)).toNat, Wire.toNat_lt _⟩
        have hval : (rename addr A).totalDegree ≤ L := (totalDegree_rename_le addr A).trans hAtot
        have hsign : sign.totalDegree ≤ 1 := (totalDegree_monomial_le _ _).trans (by simp)
        have h1val : (1 - rename addr A).totalDegree ≤ L :=
          (totalDegree_sub _ _).trans (max_le (by simp) hval)
        have h1sign : (1 - sign).totalDegree ≤ 1 :=
          (totalDegree_sub _ _).trans (max_le (by simp) hsign)
        refine (totalDegree_add _ _).trans (max_le ?_ ?_)
        · exact (totalDegree_mul _ _).trans ((Nat.add_le_add hsign h1val).trans (by omega))
        · exact (totalDegree_mul _ _).trans ((Nat.add_le_add h1sign hval).trans (by omega))
    _ = 3 * (L + 1) := by simp [Nat.mul_comm]

/-- Individual degree bound on `tableauConstraintPoly c A r`: every variable has degree at most
`1 + 3 * c.size + 3 * (L + 1)`, polynomial in instance length for succinct `NEXP` decoders. -/
theorem tableauConstraintPoly_degreeOf_le {Q L : ℕ} {R : Type*} [CommRing R]
    (c : Circuit signature Q (3 * (L + 1))) {A : MvPolynomial (Fin L) R}
    (hA : A ∈ restrictDegree (Fin L) R 1) (r : Fin (Q + c.size) → R)
    (v : Fin (Q + c.size)) :
    (tableauConstraintPoly c A r).degreeOf v ≤ 1 + 3 * c.size + 3 * (L + 1) := by
  unfold tableauConstraintPoly
  have h1 := eqCubePoly_degreeOf_le r v
  have h2 :=
    (degreeOf_le_totalDegree (gateTracePoly R c) v).trans (gateTracePoly_totalDegree_le R c)
  have h3 := (degreeOf_le_totalDegree (clauseUnsatPoly c A) v).trans
    (clauseUnsatPoly_totalDegree_le c hA)
  refine (degreeOf_mul_le v _ _).trans ?_
  have h12 := degreeOf_mul_le v (eqCubePoly r) (gateTracePoly R c)
  omega

/-! ### Boolean soundness and completeness -/

private theorem isCodeFrom_circuit_code {Q M : ℕ} (c : Circuit signature Q M) :
    Program.IsCodeFrom signature Q 0 c.code.1 := by
  have hs : (Circuit.ofCode (σ := signature) Q M c.code).isSome := by simp
  exact (Circuit.isSome_ofCode_iff.1 hs).1

/-- On a Boolean input `(idx, w) ∈ {0, 1}^{Q + c.size}`, `gateTracePoly R c` equals `1` if `w` is
the exact wire-by-wire evaluation trace of `c` on `idx`, and `0` otherwise. -/
theorem eval_gateTracePoly_bitPoint {Q M : ℕ} (R : Type*) [CommRing R]
    (c : Circuit signature Q M) (idx : Fin Q → Bool) (w : Fin c.size → Bool) :
    MvPolynomial.eval (bitPoint (Fin.append idx w)) (gateTracePoly R c) =
      if (∀ j : Fin c.size,
        w j = (evalCode interpretation false (List.ofFn idx) c.code.1).getD (Q + j.val) false)
      then 1 else 0 := by
  classical
  have hwf := isCodeFrom_circuit_code c
  set trace := evalCode interpretation false (List.ofFn idx) c.code.1
  have htrace_in (i : Fin Q) : trace.getD i.val false = idx i := by
    rw [getD_evalCode_of_lt interpretation false (List.ofFn idx) c.code.1 (by simp)]
    simp
  have htrace_gate (j : Fin c.size) :
      trace.getD (Q + j.val) false =
        (c.code.1[j.val]'(c.length_code_fst.symm ▸ j.isLt)).1.value
          (trace.getD ((c.code.1[j.val]'(c.length_code_fst.symm ▸ j.isLt)).2.getD 0 0) false)
          (trace.getD ((c.code.1[j.val]'(c.length_code_fst.symm ▸ j.isLt)).2.getD 1 0) false) := by
    have hj : j.val < c.code.1.length := c.length_code_fst.symm ▸ j.isLt
    have hwf' : Program.IsCodeFrom signature (List.ofFn idx).length 0 c.code.1 := by
      simpa [List.length_ofFn] using hwf
    have hg := getD_evalCode interpretation false (List.ofFn idx) hwf' (List.getElem?_eq_getElem hj)
    simp only [List.length_ofFn] at hg
    rw [hg, interpretation_eq_value _ (hwf.getElem j.val hj).1 _ false]
  have heval_gate (j : Fin c.size)
      (hagree : ∀ k : ℕ, (hk : k < j.val) →
        w ⟨k, by omega⟩ = trace.getD (Q + k) false) :
      MvPolynomial.eval (bitPoint (Fin.append idx w))
        (opEvalField (c.code.1.getD j.val (.const false, [])).1
          (wireX (R := R) (Q + c.size) ((c.code.1.getD j.val (.const false, [])).2.getD 0 0))
          (wireX (R := R) (Q + c.size)
            ((c.code.1.getD j.val (.const false, [])).2.getD 1 0))) =
        bitVal R (trace.getD (Q + j.val) false) := by
    have hj : j.val < c.code.1.length := c.length_code_fst.symm ▸ j.isLt
    have hgetD : c.code.1.getD j.val (.const false, []) = c.code.1[j.val]'hj := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
    have hargs := (hwf.getElem j.val hj).2
    have hstep (u : ℕ) (hu : u < Q + j.val) :
        MvPolynomial.eval (bitPoint (Fin.append idx w))
          (wireX (R := R) (Q + c.size) u) = bitVal R (trace.getD u false) := by
      simp only [wireX, show u < Q + c.size by omega, ↓reduceDIte, eval_X, bitPoint]
      by_cases huQ : u < Q
      · have hca : (⟨u, show u < Q + c.size by omega⟩ : Fin (Q + c.size)) =
            Fin.castAdd c.size ⟨u, huQ⟩ := rfl
        rw [hca, Fin.append_left, htrace_in ⟨u, huQ⟩]
      · have hk : u - Q < j.val := by omega
        have hna : (⟨u, show u < Q + c.size by omega⟩ : Fin (Q + c.size)) =
            Fin.natAdd Q ⟨u - Q, by omega⟩ := Fin.ext (by simp; omega)
        rw [hna, Fin.append_right, hagree (u - Q) hk, show Q + (u - Q) = u by omega]
    have harg_lt (idx : ℕ) (hidx : idx < signature.Arity (c.code.1[j.val]'hj).1) :
        (c.code.1[j.val]'hj).2.getD idx 0 < Q + j.val := by
      have hlen : idx < (c.code.1[j.val]'hj).2.length := by
        have := (hwf.getElem j.val hj).1; omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, Option.getD_some]
      exact hargs _ (List.getElem_mem hlen)
    rw [hgetD, htrace_gate j]
    cases hop : (c.code.1[j.val]'hj).1 with
    | const v => cases v <;> simp [opEvalField, Op.value, bitVal]
    | not =>
      have h0 : (c.code.1[j.val]'hj).2.getD 0 0 < Q + j.val := harg_lt 0 (by simp [hop])
      simp only [opEvalField, map_sub, map_one]
      rw [hstep _ h0, ← opEvalField_bitVal Op.not]
      simp [opEvalField]
    | and =>
      have h0 : (c.code.1[j.val]'hj).2.getD 0 0 < Q + j.val := harg_lt 0 (by simp [hop])
      have h1 : (c.code.1[j.val]'hj).2.getD 1 0 < Q + j.val := harg_lt 1 (by simp [hop])
      simp only [opEvalField, map_mul]
      rw [hstep _ h0, hstep _ h1, ← opEvalField_bitVal Op.and]
      rfl
    | or =>
      have h0 : (c.code.1[j.val]'hj).2.getD 0 0 < Q + j.val := harg_lt 0 (by simp [hop])
      have h1 : (c.code.1[j.val]'hj).2.getD 1 0 < Q + j.val := harg_lt 1 (by simp [hop])
      simp only [opEvalField, map_sub, map_add, map_mul]
      rw [hstep _ h0, hstep _ h1, ← opEvalField_bitVal Op.or]
      rfl
  rw [gateTracePoly, map_prod]
  split_ifs with hfull
  · refine Finset.prod_eq_one fun j _ => ?_
    have hwj : MvPolynomial.eval (bitPoint (Fin.append idx w))
        (X ⟨Q + j.val, by omega⟩ : MvPolynomial (Fin (Q + c.size)) R) = bitVal R (w j) := by
      have hna : (⟨Q + j.val, by omega⟩ : Fin (Q + c.size)) = Fin.natAdd Q j := Fin.ext rfl
      simp only [eval_X, bitPoint, hna, Fin.append_right]
    simp only [map_eqBit, hwj, heval_gate j fun k hk => hfull ⟨k, by omega⟩, hfull j, eqBit_bitVal,
      ↓reduceIte]
  · push Not at hfull
    have hex : ∃ n : ℕ, ∃ hn : n < c.size, w ⟨n, hn⟩ ≠ trace.getD (Q + n) false := by
      obtain ⟨j, hj⟩ := hfull
      exact ⟨j.val, j.isLt, hj⟩
    let j0 := Nat.find hex
    have hj0_spec : ∃ hn : j0 < c.size, w ⟨j0, hn⟩ ≠ trace.getD (Q + j0) false :=
      Nat.find_spec hex
    obtain ⟨hj0_lt, hj0_ne⟩ := hj0_spec
    have hmin (k : ℕ) (hk : k < j0) : w ⟨k, by omega⟩ = trace.getD (Q + k) false := by
      by_contra hne
      exact Nat.find_min hex hk ⟨by omega, hne⟩
    refine Finset.prod_eq_zero (Finset.mem_univ (⟨j0, hj0_lt⟩ : Fin c.size)) ?_
    have hwj : MvPolynomial.eval (bitPoint (Fin.append idx w))
        (X ⟨Q + j0, by omega⟩ : MvPolynomial (Fin (Q + c.size)) R) =
        bitVal R (w ⟨j0, hj0_lt⟩) := by
      have hna : (⟨Q + j0, by omega⟩ : Fin (Q + c.size)) = Fin.natAdd Q ⟨j0, hj0_lt⟩ :=
        Fin.ext rfl
      simp only [eval_X, bitPoint, hna, Fin.append_right]
    simp only [map_eqBit, hwj, heval_gate ⟨j0, hj0_lt⟩ hmin, eqBit_bitVal, hj0_ne, ↓reduceIte]

/-- At the honest gate trace `w` of circuit `c` on input `idx`, `clauseUnsatPoly c A` evaluates
to the product of the three literal violation weights under `A`. -/
theorem eval_clauseUnsatPoly_trace {Q L : ℕ} {R : Type*} [CommRing R]
    (c : Circuit signature Q (3 * (L + 1))) (A : MvPolynomial (Fin L) R) (idx : Fin Q → Bool)
    {w : Fin c.size → Bool}
    (hw : ∀ j : Fin c.size,
      w j = (evalCode interpretation false (List.ofFn idx) c.code.1).getD (Q + j.val) false) :
    MvPolynomial.eval (bitPoint (Fin.append idx w)) (clauseUnsatPoly c A) =
      ∏ r : Fin 3,
        let v : MvPolynomial (Fin L) R → R := fun P =>
          MvPolynomial.eval (bitPoint fun i => c.eval interpretation idx
            (SuccinctVerifier.addressWire L r i)) P
        if c.eval interpretation idx (SuccinctVerifier.signWire L r) then 1 - v A else v A := by
  have hwire {u : Fin (3 * (L + 1))} :
      (Fin.append idx w ⟨(c.outputs u).toNat, Wire.toNat_lt _⟩) = c.eval interpretation idx u := by
    rw [c.eval_eq_evalOutput idx u, evalOutput]
    set o := (c.outputs u).toNat
    by_cases ho : o < Q
    · have hcast : (⟨o, Wire.toNat_lt _⟩ : Fin (Q + c.size)) = Fin.castAdd c.size ⟨o, ho⟩ := rfl
      rw [hcast, Fin.append_left, getD_evalCode_of_lt interpretation false (List.ofFn idx) c.code.1
        (by simpa [List.length_ofFn] using ho)]
      simp only [show (c.outputs u).toNat < Q from ho, ↓reduceDIte, List.getD_eq_getElem?_getD,
        List.getElem?_ofFn, Option.getD_some]
      rfl
    · have hj : o - Q < c.size := by have := Wire.toNat_lt (c.outputs u); omega
      have hnat : (⟨o, Wire.toNat_lt _⟩ : Fin (Q + c.size)) = Fin.natAdd Q ⟨o - Q, hj⟩ := by
        ext; simp; omega
      rw [hnat, Fin.append_right, hw ⟨o - Q, hj⟩, show Q + (o - Q) = o by omega]
  rw [clauseUnsatPoly, map_prod]
  refine Finset.prod_congr rfl fun r _ => ?_
  simp only [map_add, map_mul, map_sub, map_one, eval_X, eval_rename]
  unfold bitPoint
  simp only [Function.comp_def, hwire]
  cases c.eval interpretation idx (SuccinctVerifier.signWire L r) <;> simp [bitVal]

private theorem satisfiable_toCNF_of_forall_eval_base_eq_zero {Q L : ℕ} {F : Type*} [Field F]
    (c : Circuit signature Q (3 * (L + 1))) (A : MvPolynomial (Fin L) F)
    (hA : ∀ y : Fin (Q + c.size) → Bool,
      MvPolynomial.eval (bitPoint y) (gateTracePoly F c * clauseUnsatPoly c A) = 0) :
    (SuccinctVerifier.toCNF c).Satisfiable := by
  classical
  refine ⟨fun b => decide (MvPolynomial.eval (bitPoint b) A = 1), ?_⟩
  rw [SuccinctVerifier.eval_toCNF_eq_true_iff]
  intro idx
  rw [SuccinctVerifier.eval_clause_eq_true_iff]
  let trace := evalCode interpretation false (List.ofFn idx) c.code.1
  let w : Fin c.size → Bool := fun j => trace.getD (Q + j.val) false
  have hw : ∀ j : Fin c.size, w j = trace.getD (Q + j.val) false := fun _ => rfl
  have h0 := hA (Fin.append idx w)
  rw [map_mul, eval_gateTracePoly_bitPoint] at h0
  split_ifs at h0 with hok
  · rw [one_mul, eval_clauseUnsatPoly_trace c A idx hw] at h0
    obtain ⟨r, -, hr0⟩ := Finset.prod_eq_zero_iff.mp h0
    refine ⟨r, ?_⟩
    dsimp only at hr0
    cases hs : c.eval interpretation idx (SuccinctVerifier.signWire L r)
    · rw [hs] at hr0
      simp only [Bool.false_eq_true, ↓reduceIte] at hr0
      simp [hr0]
    · rw [hs] at hr0
      simp only [↓reduceIte, sub_eq_zero] at hr0
      simp [hr0.symm]
  · exact absurd hw hok

/-- **Exact Boolean soundness and completeness of `gateTracePoly * clauseUnsatPoly`** over any
field `F` against `SuccinctVerifier.toCNF c`: a satisfying assignment exists iff some multilinear
polynomial `A ∈ restrictDegree (Fin L) F 1` makes the product vanish at every Boolean point of
`{0, 1}^{Q + c.size}`. -/
theorem satisfiable_toCNF_iff_forall_eval_base_eq_zero {Q L : ℕ} {F : Type*} [Field F]
    (c : Circuit signature Q (3 * (L + 1))) :
    (SuccinctVerifier.toCNF c).Satisfiable ↔
      ∃ A ∈ restrictDegree (Fin L) F 1,
        ∀ y : Fin (Q + c.size) → Bool,
          MvPolynomial.eval (bitPoint y) (gateTracePoly F c * clauseUnsatPoly c A) = 0 := by
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨multilinearExtension fun b => bitVal F (σ b),
      multilinearExtension_mem_restrictDegree _, fun y => ?_⟩
    obtain ⟨idx, w, rfl⟩ : ∃ (idx : Fin Q → Bool) (w : Fin c.size → Bool),
        y = Fin.append idx w :=
      ⟨fun i => y (Fin.castAdd c.size i), fun j => y (Fin.natAdd Q j), by
        funext u
        induction u using Fin.addCases with
        | left i => simp
        | right j => simp⟩
    rw [map_mul, eval_gateTracePoly_bitPoint]
    split_ifs with htrace
    · rw [one_mul, eval_clauseUnsatPoly_trace c _ idx htrace]
      have hclause : (SuccinctVerifier.clause c idx).eval σ = true := by
        rw [SuccinctVerifier.eval_toCNF_eq_true_iff] at hσ
        exact hσ idx
      obtain ⟨r, hr⟩ := (SuccinctVerifier.eval_clause_eq_true_iff c σ idx).1 hclause
      refine Finset.prod_eq_zero (Finset.mem_univ r) ?_
      dsimp only
      rw [eval_multilinearExtension]
      cases hs : c.eval interpretation idx (SuccinctVerifier.signWire L r) <;>
        simp [hs, hr, bitVal]
    · exact zero_mul _
  · rintro ⟨A, _, hA⟩
    exact satisfiable_toCNF_of_forall_eval_base_eq_zero c A hA

/-- A circuit decoding `clauseAt tm x n T` produces a `SuccinctVerifier.toCNF c` equisatisfiable
with `Tableau.succinctCNF tm x n T`. -/
theorem satisfiable_toCNF_iff_succinctCNF {k : ℕ} {State : Type} [Fintype State] [DecidableEq State]
    (tm : MultiTapeTM k Bool State) {x : List Bool} {n T : ℕ} (hn : n < 2 * T) (hx : x.length ≤ n)
    (c : Circuit signature (Tableau.clauseBits k State T)
      (3 * (Tableau.labelBits k State T + 1)))
    (hc : ∀ idx < 2 ^ Tableau.clauseBits k State T,
      List.ofFn (c.eval interpretation fun i => idx.testBit i) =
        (Tableau.clauseAt tm x n T idx).flatMap
          (Decoder.litBits (Tableau.labelBits k State T))) :
    (SuccinctVerifier.toCNF c).Satisfiable ↔ (Tableau.succinctCNF tm x n T).Satisfiable := by
  let Q := Tableau.clauseBits k State T
  let L := Tableau.labelBits k State T
  have hdec (idx : ℕ) (hidx : idx < 2 ^ Q) (r : Fin 3) :
      let clause := Tableau.clauseAt tm x n T idx
      let lit := clause.getD r.val (0, false)
      (Nat.ofBits fun i : Fin L =>
          c.eval interpretation (fun i => idx.testBit i) (SuccinctVerifier.addressWire L r i)) =
        lit.1 ∧
      c.eval interpretation (fun i => idx.testBit i) (SuccinctVerifier.signWire L r) = lit.2 := by
    have hcl_mem : Tableau.clauseAt tm x n T idx ∈ Tableau.succinctCNF tm x n T := by
      simp only [Tableau.succinctCNF, List.mem_map, List.mem_range]
      exact ⟨idx, hidx, rfl⟩
    have hcl_len : (Tableau.clauseAt tm x n T idx).length = 3 :=
      Tableau.length_of_mem_succinctCNF tm hcl_mem
    have hr_lt : r.val < (Tableau.clauseAt tm x n T idx).length := by omega
    have hvar_lt (l : Literal ℕ) (hl : l ∈ Tableau.clauseAt tm x n T idx) : l.1 < 2 ^ L := by
      apply Tableau.lt_two_pow_labelBits_of_mem_vars tm hn hx
      exact CNF.mem_vars.mpr ⟨_, hcl_mem, l.2, hl⟩
    have hof := hc idx hidx
    have hlits_len : ∀ l ∈ Tableau.clauseAt tm x n T idx,
        (Decoder.litBits L l).length = L + 1 := fun l _ => by simp [Decoder.litBits]
    have hget_lit : (Tableau.clauseAt tm x n T idx).getD r.val (0, false) =
        (Tableau.clauseAt tm x n T idx)[r.val]'hr_lt := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr_lt, Option.getD_some]
    have haddr (i : Fin L) :
        c.eval interpretation (fun j => idx.testBit j) (SuccinctVerifier.addressWire L r i) =
          ((Tableau.clauseAt tm x n T idx).getD r.val (0, false)).1.testBit i.val := by
      have hpos : r.val * (L + 1) + i.val < 3 * (Tableau.labelBits k State T + 1) :=
        (SuccinctVerifier.addressWire L r i).isLt
      have hl := congrArg (fun l : List Bool => l[(SuccinctVerifier.addressWire L r i).val]?) hof
      rw [List.getElem?_ofFn] at hl
      dsimp only [SuccinctVerifier.addressWire] at hl
      simp only [hpos, ↓reduceDIte] at hl
      change some _ = ((Tableau.clauseAt tm x n T idx).flatMap (Decoder.litBits L))[
          r.val * (L + 1) + i.val]? at hl
      rw [List.getElem?_flatMap_mul_add _ _ _ hlits_len hr_lt (Nat.lt_succ_of_lt i.isLt)] at hl
      rw [hget_lit]
      simp only [Decoder.litBits] at hl
      rw [List.getElem?_append_left (by simp)] at hl
      simp only [List.getElem?_ofFn, i.isLt, ↓reduceDIte] at hl
      exact Option.some.inj hl
    have hsign :
        c.eval interpretation (fun j => idx.testBit j) (SuccinctVerifier.signWire L r) =
          ((Tableau.clauseAt tm x n T idx).getD r.val (0, false)).2 := by
      have hpos : r.val * (L + 1) + L < 3 * (Tableau.labelBits k State T + 1) :=
        (SuccinctVerifier.signWire L r).isLt
      have hl := congrArg (fun l : List Bool => l[(SuccinctVerifier.signWire L r).val]?) hof
      rw [List.getElem?_ofFn] at hl
      dsimp only [SuccinctVerifier.signWire] at hl
      simp only [hpos, ↓reduceDIte] at hl
      change some _ = ((Tableau.clauseAt tm x n T idx).flatMap (Decoder.litBits L))[
          r.val * (L + 1) + L]? at hl
      rw [List.getElem?_flatMap_mul_add _ _ _ hlits_len hr_lt (Nat.lt_succ_self L)] at hl
      rw [hget_lit]
      simp only [Decoder.litBits] at hl
      rw [List.getElem?_append_right (by simp)] at hl
      simp only [List.length_ofFn, Nat.sub_self, List.getElem?_cons_zero] at hl
      exact Option.some.inj hl
    have hlt : ((Tableau.clauseAt tm x n T idx).getD r.val (0, false)).1 < 2 ^ L :=
      hvar_lt _ (by rw [hget_lit]; exact List.getElem_mem hr_lt)
    refine ⟨?_, hsign⟩
    have hfun : (fun i : Fin L => c.eval interpretation (fun j => idx.testBit j)
        (SuccinctVerifier.addressWire L r i)) =
        fun i : Fin L => ((Tableau.clauseAt tm x n T idx).getD r.val (0, false)).1.testBit i.val :=
      funext haddr
    rw [hfun, Nat.ofBits_testBit, Nat.mod_eq_of_lt hlt]
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨fun v => σ (fun i : Fin L => v.testBit i), ?_⟩
    rw [Tableau.succinctCNF, CNF.eval_map_eq_true_iff]
    intro idx hidx
    rw [List.mem_range] at hidx
    have hcl_c : (SuccinctVerifier.clause c (fun i => idx.testBit i)).eval σ = true :=
      (SuccinctVerifier.eval_toCNF_eq_true_iff c σ).1 hσ _
    obtain ⟨r, hr⟩ := (SuccinctVerifier.eval_clause_eq_true_iff c σ _).1 hcl_c
    obtain ⟨h1, h2⟩ := hdec idx hidx r
    have hcl_mem : Tableau.clauseAt tm x n T idx ∈ Tableau.succinctCNF tm x n T := by
      simp only [Tableau.succinctCNF, List.mem_map, List.mem_range]
      exact ⟨idx, hidx, rfl⟩
    have hcl_len : (Tableau.clauseAt tm x n T idx).length = 3 :=
      Tableau.length_of_mem_succinctCNF tm hcl_mem
    have hr_lt : r.val < (Tableau.clauseAt tm x n T idx).length := by omega
    have hget_lit : (Tableau.clauseAt tm x n T idx).getD r.val (0, false) =
        (Tableau.clauseAt tm x n T idx)[r.val]'hr_lt := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr_lt, Option.getD_some]
    rw [Clause.eval_eq_true_iff]
    refine ⟨(Tableau.clauseAt tm x n T idx).getD r.val (0, false),
      by rw [hget_lit]; exact List.getElem_mem hr_lt, ?_⟩
    have hfun : (fun i : Fin L => c.eval interpretation (fun j => idx.testBit j)
        (SuccinctVerifier.addressWire L r i)) = fun i : Fin L =>
          ((Tableau.clauseAt tm x n T idx).getD r.val (0, false)).1.testBit i.val := by
      have hvar_lt : ((Tableau.clauseAt tm x n T idx).getD r.val (0, false)).1 < 2 ^ L := by
        apply Tableau.lt_two_pow_labelBits_of_mem_vars tm hn hx
        rw [CNF.mem_vars]
        exact ⟨_, hcl_mem, _, by rw [hget_lit]; exact List.getElem_mem hr_lt⟩
      funext i
      rw [← h1, Nat.testBit_ofBits]
      simp only [i.isLt, ↓reduceDIte]
    rw [← h2, ← hr]
    congr 1
    exact hfun.symm
  · rintro ⟨σ, hσ⟩
    refine ⟨fun b => σ (Nat.ofBits b), ?_⟩
    rw [SuccinctVerifier.eval_toCNF_eq_true_iff]
    intro xbits
    let idx := Nat.ofBits xbits
    have hidx : idx < 2 ^ Q := Nat.ofBits_lt_two_pow xbits
    have htest : (fun i : Fin Q => idx.testBit i.val) = xbits :=
      funext fun i => by
        simp only [idx, Nat.testBit_ofBits,
          show (i : ℕ) < Tableau.clauseBits k State T from i.isLt, ↓reduceDIte, Fin.eta]
    have hcl_t : (Tableau.clauseAt tm x n T idx).eval σ = true := by
      rw [Tableau.succinctCNF, CNF.eval_map_eq_true_iff] at hσ
      exact hσ idx (List.mem_range.mpr hidx)
    obtain ⟨l, hl, hlσ⟩ := (Clause.eval_eq_true_iff σ _).1 hcl_t
    have hcl_len : (Tableau.clauseAt tm x n T idx).length = 3 :=
      Tableau.length_of_mem_succinctCNF tm (by
        simp only [Tableau.succinctCNF, List.mem_map, List.mem_range]
        exact ⟨idx, hidx, rfl⟩)
    obtain ⟨r_nat, hr_lt, rfl⟩ := List.mem_iff_getElem.1 hl
    let r : Fin 3 := ⟨r_nat, by omega⟩
    obtain ⟨h1, h2⟩ := hdec idx hidx r
    rw [SuccinctVerifier.eval_clause_eq_true_iff]
    refine ⟨r, ?_⟩
    have hget_lit : (Tableau.clauseAt tm x n T idx).getD r.val (0, false) =
        (Tableau.clauseAt tm x n T idx)[r_nat]'hr_lt := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr_lt, Option.getD_some]
    rw [← htest, h1, h2, hget_lit]
    exact hlσ

/-- Exact algebraic equivalence for `Tableau.succinctCNF`: `succinctCNF tm x n T` is satisfiable
iff some multilinear polynomial `A ∈ restrictDegree (Fin (labelBits k State T)) F 1` makes
`gateTracePoly F c * clauseUnsatPoly c A` vanish on the Boolean cube `{0, 1}^{Q + c.size}`. -/
theorem satisfiable_succinctCNF_iff_forall_eval_base_eq_zero {k : ℕ} {State : Type} [Fintype State]
    [DecidableEq State] (tm : MultiTapeTM k Bool State) {x : List Bool} {n T : ℕ}
    (hn : n < 2 * T) (hx : x.length ≤ n)
    (c : Circuit signature (Tableau.clauseBits k State T)
      (3 * (Tableau.labelBits k State T + 1)))
    (hc : ∀ idx < 2 ^ Tableau.clauseBits k State T,
      List.ofFn (c.eval interpretation fun i => idx.testBit i) =
        (Tableau.clauseAt tm x n T idx).flatMap
          (Decoder.litBits (Tableau.labelBits k State T)))
    (F : Type*) [Field F] :
    (Tableau.succinctCNF tm x n T).Satisfiable ↔
      ∃ A ∈ restrictDegree (Fin (Tableau.labelBits k State T)) F 1,
        ∀ y : Fin (Tableau.clauseBits k State T + c.size) → Bool,
          MvPolynomial.eval (bitPoint y) (gateTracePoly F c * clauseUnsatPoly c A) = 0 :=
  (satisfiable_toCNF_iff_succinctCNF tm hn hx c hc).symm.trans
    (satisfiable_toCNF_iff_forall_eval_base_eq_zero c)

/-! ### Sumcheck and Schwartz–Zippel soundness -/

/-- For every verifier challenge `r : Fin (Q + c.size) → F`, the sumcheck sum of
`tableauConstraintPoly c A r` over `{0, 1}^{Q + c.size}` equals the multilinear extension of
`gateTracePoly F c * clauseUnsatPoly c A` evaluated at `r`. -/
theorem partialSum_tableauConstraintPoly_eq {Q L : ℕ} {F : Type} [Field F]
    (c : Circuit signature Q (3 * (L + 1))) (A : MvPolynomial (Fin L) F)
    (r : Fin (Q + c.size) → F) :
    Sumcheck.partialSum (tableauConstraintPoly c A r) Fin.elim0 =
      MvPolynomial.eval r (multilinearExtension fun y : Fin (Q + c.size) → Bool =>
        MvPolynomial.eval (bitPoint y) (gateTracePoly F c * clauseUnsatPoly c A)) := by
  simp only [Sumcheck.partialSum, Nat.sub_zero, eval_multilinearExtension_eq_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  have hpt : Sumcheck.point (n := Q + c.size) (Fin.elim0 : Fin 0 → F) y = bitPoint y := by
    funext i
    simp [Sumcheck.point, bitPoint, bitVal]
  rw [hpt, tableauConstraintPoly, mul_assoc, map_mul,
    mul_comm (MvPolynomial.eval (bitPoint y) (gateTracePoly F c * clauseUnsatPoly c A))]
  congr 1
  rw [eqCubePoly, map_prod, eval_indicatorPoly_apply]
  refine Finset.prod_congr rfl fun i _ => ?_
  cases hyi : y i <;> simp [hyi, bitPoint, bitVal]

/-- **Completeness of Sumcheck for the arithmetized succinct 3CNF**: when `SuccinctVerifier.toCNF c`
is satisfiable, some multilinear `A` makes
`Sumcheck.rel (tableauConstraintPoly c A r) 0 ⟨Fin.elim0, 0⟩ ()`
hold for every challenge `r`, and `Sumcheck.proof d (tableauConstraintPoly c A r)` is accepted with
probability `1` whenever `1 + 3 * c.size + 3 * (L + 1) ≤ d`. -/
theorem sumcheck_proof_complete_of_satisfiable {Q L : ℕ} {F : Type} [Field F] [Fintype F]
    [DecidableEq F] (c : Circuit signature Q (3 * (L + 1)))
    (hsat : (SuccinctVerifier.toCNF c).Satisfiable) {d : ℕ}
    (hd : 1 + 3 * c.size + 3 * (L + 1) ≤ d) :
    ∃ A ∈ restrictDegree (Fin L) F 1, ∀ r : Fin (Q + c.size) → F,
      Sumcheck.rel (tableauConstraintPoly c A r) 0 ⟨Fin.elim0, 0⟩ () ∧
      (Sumcheck.proof d (tableauConstraintPoly c A r)).Complete
        Interactive.World.plain (Sumcheck.rel (tableauConstraintPoly c A r) 0)
        Interactive.Accept 0 := by
  obtain ⟨A, hAmem, hA⟩ := (satisfiable_toCNF_iff_forall_eval_base_eq_zero (F := F) c).1 hsat
  refine ⟨A, hAmem, fun r => ⟨?_, Sumcheck.proof_complete d (tableauConstraintPoly c A r)
    fun v => (tableauConstraintPoly_degreeOf_le c hAmem r v).trans hd⟩⟩
  rw [Sumcheck.rel, partialSum_tableauConstraintPoly_eq]
  simp [hA, multilinearExtension]

/-- **Schwartz–Zippel + Sumcheck soundness**: when `SuccinctVerifier.toCNF c` is unsatisfiable, for
EVERY assignment polynomial `A : MvPolynomial (Fin L) F`:
1. at a uniformly random challenge `r : Fin (Q + c.size) → F`, the arithmetized Sumcheck sum
   vanishes with probability at most `(Q + c.size) / |F|`; and
2. for every `r` where the sum does not vanish, `Sumcheck.proof d (tableauConstraintPoly c A r)`
   is `((Q + c.size) * (d / |F|))`-sound against every interactive prover. -/
theorem sumcheck_sound_of_not_satisfiable {Q L : ℕ} {F : Type} [Field F] [Fintype F]
    [DecidableEq F] (c : Circuit signature Q (3 * (L + 1)))
    (hunsat : ¬ (SuccinctVerifier.toCNF c).Satisfiable) (A : MvPolynomial (Fin L) F) {d : ℕ}
    (hd : ∀ r v, (tableauConstraintPoly c A r).degreeOf v ≤ d) :
    ((Finset.univ : Finset (Fin (Q + c.size) → F)).filter fun r =>
        Sumcheck.partialSum (tableauConstraintPoly c A r) Fin.elim0 = 0).card *
        Fintype.card F ≤ (Q + c.size) * Fintype.card F ^ (Q + c.size) ∧
      ∀ r : Fin (Q + c.size) → F,
        Sumcheck.partialSum (tableauConstraintPoly c A r) Fin.elim0 ≠ 0 →
        (Sumcheck.proof d (tableauConstraintPoly c A r)).verifier.Sound
          (oP := OracleSpec.empty) Interactive.World.plain
          (Interactive.language (Sumcheck.rel (tableauConstraintPoly c A r) 0)) Set.univ
          ((Q + c.size) * ((d : ℝ≥0∞) / Fintype.card F)) := by
  let E : MvPolynomial (Fin (Q + c.size)) F := multilinearExtension fun y =>
    MvPolynomial.eval (bitPoint y) (gateTracePoly F c * clauseUnsatPoly c A)
  have hE_ne : E ≠ 0 := by
    intro h0
    have hall : ∀ y : Fin (Q + c.size) → Bool,
        MvPolynomial.eval (bitPoint y) (gateTracePoly F c * clauseUnsatPoly c A) = 0 := by
      intro y
      have := congrArg (MvPolynomial.eval (bitPoint y)) h0
      simpa [E, eval_multilinearExtension] using this
    exact hunsat (satisfiable_toCNF_of_forall_eval_base_eq_zero c A hall)
  constructor
  · have hdeg : E.totalDegree ≤ Q + c.size :=
      (totalDegree_multilinearExtension_le (R := F) fun y : Fin (Q + c.size) → Bool =>
        MvPolynomial.eval (bitPoint y) (gateTracePoly F c * clauseUnsatPoly c A)).trans (by simp)
    have hsz := MvPolynomial.card_filter_eval_eq_zero_mul_card_le hE_ne hdeg
    simpa only [E, partialSum_tableauConstraintPoly_eq] using hsz
  · intro r _
    simpa only [Nat.cast_add] using Sumcheck.proof_sound d (tableauConstraintPoly c A r) (hd r)

/-! ### Uniform polynomial-time verifier evaluation over `ZMod p` -/

/-- Modular multiplication `(x * y) % p`, totalized to `0` at `p = 0`. -/
def mulMod (p x y : ℕ) : ℕ :=
  if p = 0 then 0 else (x * y) % p

/-- At `p = 0`, `mulMod` evaluates to `0`. -/
@[simp]
theorem mulMod_zero_left (x y : ℕ) : mulMod 0 x y = 0 :=
  rfl

private theorem mulMod_le (p x y : ℕ) : mulMod p x y ≤ p := by
  unfold mulMod
  split_ifs with hp
  · omega
  · exact (Nat.mod_lt _ (Nat.pos_of_ne_zero hp)).le

private theorem natCast_mulMod {p : ℕ} (hp : 0 < p) (x y : ℕ) :
    ((mulMod p x y : ℕ) : ZMod p) = (x : ZMod p) * (y : ZMod p) := by
  rw [mulMod]
  simp only [Nat.ne_of_gt hp, ↓reduceIte, ZMod.natCast_mod, Nat.cast_mul]

private theorem foldl_mulMod_le {ι : Type} (p : ℕ) (f : ι → ℕ) (l : List ι)
    {init : ℕ} (hinit : init ≤ p) :
    l.foldl (fun prod a => mulMod p prod (f a)) init ≤ p := by
  induction l generalizing init with
  | nil => exact hinit
  | cons a l ih => exact ih (mulMod_le p init (f a))

private theorem foldl_mulMod_eq {ι : Type} {p : ℕ} (hp : 0 < p) (f : ι → ℕ) (l : List ι)
    (init : ℕ) :
    ((l.foldl (fun prod a => mulMod p prod (f a)) init : ℕ) : ZMod p) =
      (init : ZMod p) * (l.map fun a => (f a : ZMod p)).prod := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons, List.map_cons, List.prod_cons, ih, natCast_mulMod hp, mul_assoc]

private theorem natCast_mod_eq {p : ℕ} (x : ℕ) : ((x % p : ℕ) : ZMod p) = (x : ZMod p) :=
  (ZMod.natCast_eq_natCast_iff _ _ p).mpr (Nat.mod_modEq x p)

private theorem natCast_complementMod {p : ℕ} (hp : 0 < p) (x : ℕ) :
    ((p + 1 - x % p : ℕ) : ZMod p) = 1 - (x : ZMod p) := by
  have hle : x % p ≤ p + 1 := (Nat.mod_lt x hp).le.trans (Nat.le_succ p)
  rw [Nat.cast_sub hle, Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_one, natCast_mod_eq]

private theorem zip_ofFn {α β : Type} {n : ℕ} (f : Fin n → α) (g : Fin n → β) :
    (List.ofFn f).zip (List.ofFn g) = List.ofFn fun i => (f i, g i) := by
  apply List.ext_getElem (by simp)
  intro i hi _
  simp only [List.length_zip, List.length_ofFn, min_self] at hi
  simp

/-- Natural-number mod-`p` evaluation of a De Morgan gate operation, matching `opEvalField` in
`ZMod p` and bounded by `p` even at `p = 0`. -/
def opEvalMod (p : ℕ) : Op → ℕ → ℕ → ℕ
  | .const false, _, _ => 0
  | .const true, _, _ => if p = 0 then 0 else 1 % p
  | .not, a, _ => if p = 0 then 0 else (p + 1 - a % p) % p
  | .and, a, b => if p = 0 then 0 else (a * b) % p
  | .or, a, b => if p = 0 then 0 else (a + b + (p - (a * b) % p)) % p

/-- Multilinear bit-equality mod `p`, matching `eqBit` in `ZMod p`. -/
def eqBitMod (p u v : ℕ) : ℕ :=
  if p = 0 then 0 else (u * v + (p + 1 - u % p) * (p + 1 - v % p)) % p

/-- Multilinear literal-violation factor `s * (1 - v) + (1 - s) * v` mod `p`. -/
def evalLitUnsatMod (p s v : ℕ) : ℕ :=
  if p = 0 then 0 else (s * (p + 1 - v % p) + (p + 1 - s % p) * v) % p

@[simp] theorem natCast_opEvalMod {p : ℕ} (hp : 0 < p) (op : Op) (a b : ℕ) :
    ((opEvalMod p op a b : ℕ) : ZMod p) = opEvalField op (a : ZMod p) (b : ZMod p) := by
  have hp0 : p ≠ 0 := Nat.ne_of_gt hp
  cases op with
  | const v =>
    cases v
    · simp [opEvalMod, opEvalField, bitVal]
    · simp [opEvalMod, opEvalField, bitVal, hp0]
  | not =>
    simp only [opEvalMod, hp0, ↓reduceIte, opEvalField, natCast_mod_eq, natCast_complementMod hp]
  | and =>
    simp only [opEvalMod, hp0, ↓reduceIte, opEvalField, natCast_mod_eq, Nat.cast_mul]
  | or =>
    have hle : (a * b) % p ≤ p := (Nat.mod_lt (a * b) hp).le
    simp only [opEvalMod, hp0, ↓reduceIte, opEvalField]
    rw [natCast_mod_eq, Nat.cast_add, Nat.cast_add, Nat.cast_sub hle, natCast_mod_eq]
    push_cast
    simp [sub_eq_add_neg]

@[simp] theorem natCast_eqBitMod {p : ℕ} (hp : 0 < p) (u v : ℕ) :
    ((eqBitMod p u v : ℕ) : ZMod p) = eqBit (u : ZMod p) (v : ZMod p) := by
  simp only [eqBitMod, Nat.ne_of_gt hp, ↓reduceIte, eqBit, natCast_mod_eq, Nat.cast_add,
    Nat.cast_mul, natCast_complementMod hp]

@[simp] theorem natCast_evalLitUnsatMod {p : ℕ} (hp : 0 < p) (s v : ℕ) :
    ((evalLitUnsatMod p s v : ℕ) : ZMod p) =
      (s : ZMod p) * (1 - (v : ZMod p)) + (1 - (s : ZMod p)) * (v : ZMod p) := by
  simp only [evalLitUnsatMod, Nat.ne_of_gt hp, ↓reduceIte, natCast_mod_eq, Nat.cast_add,
    Nat.cast_mul, natCast_complementMod hp]

/-- Evaluate the product `gateTracePoly` mod `p` on wire residue vector `z : List ℕ`. -/
def evalGateTraceMod (p Q : ℕ) (z : List ℕ) (gates : List (Op × List ℕ)) : ℕ :=
  (gates.foldl (fun (acc : ℕ × ℕ) (g : Op × List ℕ) =>
    let a := z.getD (g.2.getD 0 0) 0
    let b := z.getD (g.2.getD 1 0) 0
    let w := z.getD (Q + acc.1) 0
    (acc.1 + 1, mulMod p acc.2 (eqBitMod p w (opEvalMod p g.1 a b))))
    (0, mulMod p 1 1)).2

/-- Evaluate the multilinear equality indicator `eqCubePoly r` at `z` mod `p`. -/
def eqCubeMod (p : ℕ) (rVec z : List ℕ) : ℕ :=
  (rVec.zip z).foldl (fun prod rz => mulMod p prod (eqBitMod p rz.1 rz.2)) (mulMod p 1 1)

/-- Evaluate the clause falsification product `clauseUnsatPoly` mod `p` given the wire residue
vector `z`, the three sign wire indices `signWires`, and the oracle values `litVals`. -/
def evalClauseUnsatMod (p : ℕ) (z signWires litVals : List ℕ) : ℕ :=
  (signWires.zip litVals).foldl
    (fun prod sl => mulMod p prod (evalLitUnsatMod p (z.getD sl.1 0) sl.2))
    (mulMod p 1 1)

/-- Evaluate the full verifier constraint `tableauConstraintPoly c A r` at `z` mod `p` given
circuit gates `gates`, challenge `rVec`, point `z`, sign output wires `signWires`, and three oracle
evaluations `litVals`. -/
def evalConstraintMod (p Q : ℕ) (gates : List (Op × List ℕ))
    (rVec z signWires litVals : List ℕ) : ℕ :=
  mulMod p (mulMod p (eqCubeMod p rVec z) (evalGateTraceMod p Q z gates))
    (evalClauseUnsatMod p z signWires litVals)

/-- `evalGateTraceMod` agrees with evaluating `gateTracePoly (ZMod p) c` in `ZMod p`. -/
theorem natCast_evalGateTraceMod {p Q M : ℕ} (hp : 0 < p) (c : Circuit signature Q M)
    (z : Fin (Q + c.size) → ℕ) :
    ((evalGateTraceMod p Q (List.ofFn z) c.code.1 : ℕ) : ZMod p) =
      MvPolynomial.eval (fun i => (z i : ZMod p)) (gateTracePoly (ZMod p) c) := by
  let step (acc : ℕ × ℕ) (g : Op × List ℕ) : ℕ × ℕ :=
    let a := (List.ofFn z).getD (g.2.getD 0 0) 0
    let b := (List.ofFn z).getD (g.2.getD 1 0) 0
    let w := (List.ofFn z).getD (Q + acc.1) 0
    (acc.1 + 1, mulMod p acc.2 (eqBitMod p w (opEvalMod p g.1 a b)))
  have hfold (n : ℕ) (hn : n ≤ c.code.1.length) :
      ((c.code.1.take n).foldl step (0, mulMod p 1 1)).1 = n ∧
      ((((c.code.1.take n).foldl step (0, mulMod p 1 1)).2 : ℕ) : ZMod p) =
        ∏ j : Fin n,
          let gate := c.code.1.getD j.val (.const false, [])
          eqBit (z ⟨Q + j.val, by have := c.length_code_fst; omega⟩ : ZMod p)
            (opEvalField gate.1
              (if h : gate.2.getD 0 0 < Q + c.size then (z ⟨gate.2.getD 0 0, h⟩ : ZMod p) else 0)
              (if h : gate.2.getD 1 0 < Q + c.size
                then (z ⟨gate.2.getD 1 0, h⟩ : ZMod p) else 0)) := by
    induction n with
    | zero =>
      refine ⟨rfl, ?_⟩
      simp [natCast_mulMod hp]
    | succ n ih =>
      obtain ⟨h1, h2⟩ := ih (by omega)
      rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
      refine ⟨?_, ?_⟩
      · change ((List.take n c.code.1).foldl step (0, mulMod p 1 1)).1 + 1 = n + 1
        rw [h1]
      · have hlen : c.size = c.code.1.length := c.length_code_fst.symm
        have hget : c.code.1[n]'(by omega) = c.code.1.getD n (.const false, []) := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
        change ((step ((List.take n c.code.1).foldl step (0, mulMod p 1 1)) c.code.1[n]).2 : ZMod p)
          = _
        simp only [step, h1, natCast_mulMod hp, h2]
        rw [Fin.prod_univ_castSucc]
        congr 1
        have hw : ((List.ofFn z).getD (Q + n) 0 : ZMod p) =
            (z ⟨Q + n, by omega⟩ : ZMod p) := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn,
            show Q + n < Q + c.size by omega, ↓reduceDIte, Option.getD_some]
        have hwire (u : ℕ) : ((List.ofFn z).getD u 0 : ZMod p) =
            if h : u < Q + c.size then (z ⟨u, h⟩ : ZMod p) else 0 := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
          split_ifs with hu <;> simp
        rw [natCast_eqBitMod hp, hw, natCast_opEvalMod hp, hget, hwire, hwire]
        rfl
  obtain ⟨_, hdone⟩ := hfold c.code.1.length le_rfl
  rw [List.take_length] at hdone
  change ((List.foldl step (0, mulMod p 1 1) c.code.1).2 : ZMod p) = _
  refine hdone.trans ?_
  rw [gateTracePoly, map_prod]
  refine Fintype.prod_equiv (Fin.castOrderIso c.length_code_fst).toEquiv _ _ fun j => ?_
  simp only [map_eqBit, map_opEvalField, eval_X]
  have hval : ((Fin.castOrderIso c.length_code_fst).toEquiv j).val = j.val := rfl
  simp only [hval]
  congr 1
  congr 1 <;> (unfold wireX; split_ifs <;> simp)

private theorem natCast_foldl_mulMod_zip_ofFn {p N : ℕ} (hp : 0 < p) (f g : Fin N → ℕ)
    (k : ℕ × ℕ → ℕ) :
    ((((List.ofFn f).zip (List.ofFn g)).foldl (fun (prod : ℕ) xy => mulMod p prod (k xy))
        (mulMod p 1 1) : ℕ) : ZMod p) =
      ∏ i : Fin N, (k (f i, g i) : ZMod p) := by
  rw [zip_ofFn, foldl_mulMod_eq hp, natCast_mulMod hp]
  simp only [Nat.cast_one, mul_one, one_mul, List.map_ofFn, List.prod_ofFn]
  rfl

/-- `eqCubeMod` agrees with evaluating `eqCubePoly r` in `ZMod p`. -/
theorem natCast_eqCubeMod {p N : ℕ} (hp : 0 < p) (r z : Fin N → ℕ) :
    ((eqCubeMod p (List.ofFn r) (List.ofFn z) : ℕ) : ZMod p) =
      MvPolynomial.eval (fun i => (z i : ZMod p)) (eqCubePoly fun i => (r i : ZMod p)) := by
  rw [eqCubeMod, natCast_foldl_mulMod_zip_ofFn hp, eqCubePoly, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [natCast_eqBitMod hp, eqBit]

/-- `evalClauseUnsatMod` agrees with evaluating `clauseUnsatPoly c A` in `ZMod p` when supplied
with the three oracle evaluations `val j = eval (addr_j(z)) A`. -/
theorem natCast_evalClauseUnsatMod {p Q L : ℕ} (hp : 0 < p)
    (c : Circuit signature Q (3 * (L + 1))) (A : MvPolynomial (Fin L) (ZMod p))
    (z : Fin (Q + c.size) → ℕ) (val : Fin 3 → ℕ)
    (hval : ∀ r : Fin 3, (val r : ZMod p) =
      MvPolynomial.eval
        (fun i : Fin L =>
          (z ⟨(c.outputs (SuccinctVerifier.addressWire L r i)).toNat, Wire.toNat_lt _⟩ : ZMod p))
        A) :
    ((evalClauseUnsatMod p (List.ofFn z)
        (List.ofFn fun r : Fin 3 => (c.outputs (SuccinctVerifier.signWire L r)).toNat)
        (List.ofFn val) : ℕ) : ZMod p) =
      MvPolynomial.eval (fun i => (z i : ZMod p)) (clauseUnsatPoly c A) := by
  rw [evalClauseUnsatMod, natCast_foldl_mulMod_zip_ofFn hp, clauseUnsatPoly, map_prod]
  refine Finset.prod_congr rfl fun r _ => ?_
  have hs :
      ((List.ofFn z).getD (c.outputs (SuccinctVerifier.signWire L r)).toNat 0 : ZMod p) =
        (z ⟨(c.outputs (SuccinctVerifier.signWire L r)).toNat, Wire.toNat_lt _⟩ : ZMod p) := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, Wire.toNat_lt _, ↓reduceDIte,
      Option.getD_some]
  simp only [Function.comp_def, natCast_evalLitUnsatMod hp, hs, map_add, map_mul, map_sub,
    map_one, eval_X, eval_rename, hval r]

/-- `evalConstraintMod` agrees with evaluating `tableauConstraintPoly c A r` in `ZMod p`. -/
theorem natCast_evalConstraintMod {p Q L : ℕ} (hp : 0 < p)
    (c : Circuit signature Q (3 * (L + 1))) (A : MvPolynomial (Fin L) (ZMod p))
    (r z : Fin (Q + c.size) → ℕ) (val : Fin 3 → ℕ)
    (hval : ∀ j : Fin 3, (val j : ZMod p) =
      MvPolynomial.eval
        (fun i : Fin L =>
          (z ⟨(c.outputs (SuccinctVerifier.addressWire L j i)).toNat, Wire.toNat_lt _⟩ : ZMod p))
        A) :
    ((evalConstraintMod p Q c.code.1 (List.ofFn r) (List.ofFn z)
        (List.ofFn fun j : Fin 3 => (c.outputs (SuccinctVerifier.signWire L j)).toNat)
        (List.ofFn val) : ℕ) : ZMod p) =
      MvPolynomial.eval (fun i => (z i : ZMod p))
        (tableauConstraintPoly c A fun i => (r i : ZMod p)) := by
  rw [evalConstraintMod, natCast_mulMod hp, natCast_mulMod hp, natCast_eqCubeMod hp,
    natCast_evalGateTraceMod hp, natCast_evalClauseUnsatMod hp c A z val hval,
    tableauConstraintPoly, map_mul, map_mul]

section EvalModPolyTime

private theorem computableInPolyTime_mulMod {α : Type} {enc : α ↪ List Bool}
    {p x y : α → ℕ}
    (hp : ComputableInPolyTime p enc encNat)
    (hx : ComputableInPolyTime x enc encNat)
    (hy : ComputableInPolyTime y enc encNat) :
    ComputableInPolyTime (fun a => mulMod (p a) (x a) (y a)) enc encNat := by
  unfold mulMod
  exact ite_decide (decide_eq' hp (const 0)) (const 0)
    (binary_mod' (binary_mul' hx hy) hp)

private theorem computableInPolyTime_opEvalMod {α : Type} {enc : α ↪ List Bool}
    {p : α → ℕ} {op : α → Op} {x y : α → ℕ}
    (hp : ComputableInPolyTime p enc encNat)
    (hop : ComputableInPolyTime op enc encOp)
    (hx : ComputableInPolyTime x enc encNat)
    (hy : ComputableInPolyTime y enc encNat) :
    ComputableInPolyTime (fun a => opEvalMod (p a) (op a) (x a) (y a)) enc encNat := by
  have htn : ComputableInPolyTime (fun a => (op a).toNat) enc encUnary :=
    (of_eq (f := Op.toNat) fun _ => rfl).comp hop
  have h1 : ComputableInPolyTime (fun a => if p a = 0 then 0 else 1 % p a) enc encNat :=
    ite_decide (decide_eq' hp (const 0)) (const 0) (binary_mod' (const 1) hp)
  have hnot : ComputableInPolyTime
      (fun a => if p a = 0 then 0 else (p a + 1 - x a % p a) % p a) enc encNat :=
    ite_decide (decide_eq' hp (const 0)) (const 0)
      (binary_mod' (binary_sub' (binary_add' hp (const 1)) (binary_mod' hx hp)) hp)
  have hand : ComputableInPolyTime
      (fun a => if p a = 0 then 0 else (x a * y a) % p a) enc encNat :=
    ite_decide (decide_eq' hp (const 0)) (const 0) (binary_mod' (binary_mul' hx hy) hp)
  have hor : ComputableInPolyTime
      (fun a => if p a = 0 then 0 else (x a + y a + (p a - (x a * y a) % p a)) % p a)
      enc encNat :=
    ite_decide (decide_eq' hp (const 0)) (const 0)
      (binary_mod'
        (binary_add' (binary_add' hx hy) (binary_sub' hp (binary_mod' (binary_mul' hx hy) hp)))
        hp)
  have hcond :=
    ite_decide (unary_eq' htn (const 0)) (const 0)
      (ite_decide (unary_eq' htn (const 1)) h1
        (ite_decide (unary_eq' htn (const 2)) hnot
          (ite_decide (unary_eq' htn (const 3)) hand hor)))
  refine hcond.of_enc_eq fun a => congrArg encNat ?_
  cases hop_a : op a with
  | const v => cases v <;> simp [opEvalMod, Op.toNat]
  | not => simp [opEvalMod, Op.toNat]
  | and => simp [opEvalMod, Op.toNat]
  | or => simp [opEvalMod, Op.toNat]

private theorem computableInPolyTime_eqBitMod {α : Type} {enc : α ↪ List Bool}
    {p u v : α → ℕ}
    (hp : ComputableInPolyTime p enc encNat)
    (hu : ComputableInPolyTime u enc encNat)
    (hv : ComputableInPolyTime v enc encNat) :
    ComputableInPolyTime (fun a => eqBitMod (p a) (u a) (v a)) enc encNat := by
  unfold eqBitMod
  exact ite_decide (decide_eq' hp (const 0)) (const 0)
    (binary_mod'
      (binary_add' (binary_mul' hu hv)
        (binary_mul' (binary_sub' (binary_add' hp (const 1)) (binary_mod' hu hp))
          (binary_sub' (binary_add' hp (const 1)) (binary_mod' hv hp))))
      hp)

private theorem computableInPolyTime_evalLitUnsatMod {α : Type} {enc : α ↪ List Bool}
    {p s v : α → ℕ}
    (hp : ComputableInPolyTime p enc encNat)
    (hs : ComputableInPolyTime s enc encNat)
    (hv : ComputableInPolyTime v enc encNat) :
    ComputableInPolyTime (fun a => evalLitUnsatMod (p a) (s a) (v a)) enc encNat := by
  unfold evalLitUnsatMod
  exact ite_decide (decide_eq' hp (const 0)) (const 0)
    (binary_mod'
      (binary_add'
        (binary_mul' hs (binary_sub' (binary_add' hp (const 1)) (binary_mod' hv hp)))
        (binary_mul' (binary_sub' (binary_add' hp (const 1)) (binary_mod' hs hp)) hv))
      hp)

private theorem computableInPolyTime_foldlMulMod {γ α π : Type}
    {encIn : γ ↪ List Bool} {encA : α ↪ List Bool} {encL : List α ↪ List Bool}
    {encP : π ↪ List Bool} [ListEncoding encA encL] [SizedListEncoding encA encL]
    {p : γ → ℕ} {par : γ → π} {list : γ → List α} {factor : π → α → ℕ}
    (hp : ComputableInPolyTime p encIn encNat)
    (hpar : ComputableInPolyTime par encIn encP)
    (hlist : ComputableInPolyTime list encIn encL)
    (hfac : ComputableInPolyTime (fun q : π × α => factor q.1 q.2) (encPair encP encA) encNat) :
    ComputableInPolyTime
      (fun x => (list x).foldl (fun prod el => mulMod (p x) prod (factor (par x) el))
        (mulMod (p x) 1 1))
      encIn encNat := by
  let step (q : ℕ × π) (prod : ℕ) (el : α) : ℕ := mulMod q.1 prod (factor q.2 el)
  have hpar' : ComputableInPolyTime (fun x => (p x, par x)) encIn (encPair encNat encP) :=
    hp.prod hpar
  have hinit : ComputableInPolyTime (fun x => mulMod (p x) 1 1) encIn encNat :=
    computableInPolyTime_mulMod hp (const 1) (const 1)
  have hstep : ComputableInPolyTime (fun r : ((ℕ × π) × ℕ) × α => step r.1.1 r.1.2 r.2)
      (encPair (encPair (encPair encNat encP) encNat) encA) encNat := by
    have hq : ComputableInPolyTime (fun r : ((ℕ × π) × ℕ) × α => r.1.1)
        (encPair (encPair (encPair encNat encP) encNat) encA) (encPair encNat encP) :=
      (fst _ _).comp (fst _ _)
    have hprod : ComputableInPolyTime (fun r : ((ℕ × π) × ℕ) × α => r.1.2)
        (encPair (encPair (encPair encNat encP) encNat) encA) encNat :=
      (snd _ _).comp (fst _ _)
    have hel : ComputableInPolyTime (fun r : ((ℕ × π) × ℕ) × α => r.2)
        (encPair (encPair (encPair encNat encP) encNat) encA) encA := snd _ _
    exact computableInPolyTime_mulMod hq.fst' hprod (hfac.comp (hq.snd'.prod hel))
  refine (foldlWith_spec hpar' hlist hinit hstep
    (fun x _ prod => prod ≤ p x)
    (fun x => mulMod_le (p x) 1 1)
    (fun x _ _ _ _ _ => mulMod_le (p x) _ _)
    hp.polyBounded_length
    (fun x _ prod _ hle => length_encNat_mono hle)).1

/-- `eqCubeMod` is computable in polynomial time over growing binary modulus `p`, `rVec`, and
`z`. -/
@[fun_prop]
theorem computableInPolyTime_eqCubeMod {α : Type} {enc : α ↪ List Bool}
    {p : α → ℕ} {rVec z : α → List ℕ}
    (hp : ComputableInPolyTime p enc encNat)
    (hr : ComputableInPolyTime rVec enc (encList encNat))
    (hz : ComputableInPolyTime z enc (encList encNat)) :
    ComputableInPolyTime (fun a => eqCubeMod (p a) (rVec a) (z a)) enc encNat := by
  have h := computableInPolyTime_foldlMulMod (encA := encPair encNat encNat)
    (encL := encList (encPair encNat encNat)) (encP := encNat)
    (factor := fun (p : ℕ) (rz : ℕ × ℕ) => eqBitMod p rz.1 rz.2)
    hp hp ((zip encNat encNat).comp (hr.prod hz))
    (computableInPolyTime_eqBitMod (fst _ _) ((snd _ _).fst') ((snd _ _).snd'))
  exact h.of_enc_eq fun _ => rfl

/-- `evalClauseUnsatMod` is computable in polynomial time over growing binary modulus `p`. -/
@[fun_prop]
theorem computableInPolyTime_evalClauseUnsatMod {α : Type} {enc : α ↪ List Bool}
    {p : α → ℕ} {z signWires litVals : α → List ℕ}
    (hp : ComputableInPolyTime p enc encNat)
    (hz : ComputableInPolyTime z enc (encList encNat))
    (hsign : ComputableInPolyTime signWires enc (encList encNat))
    (hlit : ComputableInPolyTime litVals enc (encList encNat)) :
    ComputableInPolyTime
      (fun a => evalClauseUnsatMod (p a) (z a) (signWires a) (litVals a)) enc encNat := by
  have hfac : ComputableInPolyTime
      (fun q : (ℕ × List ℕ) × (ℕ × ℕ) =>
        evalLitUnsatMod q.1.1 (q.1.2.getD q.2.1 0) q.2.2)
      (encPair (encPair encNat (encList encNat)) (encPair encNat encNat)) encNat := by
    let encQ := encPair (encPair encNat (encList encNat)) (encPair encNat encNat)
    have hpq : ComputableInPolyTime (fun q : (ℕ × List ℕ) × (ℕ × ℕ) => q.1.1) encQ encNat :=
      (fst _ _).comp (fst _ _)
    have hzq : ComputableInPolyTime (fun q : (ℕ × List ℕ) × (ℕ × ℕ) => q.1.2)
        encQ (encList encNat) := (snd _ _).comp (fst _ _)
    have hsw : ComputableInPolyTime (fun q : (ℕ × List ℕ) × (ℕ × ℕ) => q.2.1) encQ encNat :=
      (fst _ _).comp (snd _ _)
    have hval : ComputableInPolyTime (fun q : (ℕ × List ℕ) × (ℕ × ℕ) => q.2.2) encQ encNat :=
      (snd _ _).comp (snd _ _)
    exact computableInPolyTime_evalLitUnsatMod hpq (listGetD_binary 0 hzq hsw) hval
  have h := computableInPolyTime_foldlMulMod (encA := encPair encNat encNat)
    (encL := encList (encPair encNat encNat)) (encP := encPair encNat (encList encNat))
    (factor := fun (q : ℕ × List ℕ) (sl : ℕ × ℕ) =>
      evalLitUnsatMod q.1 (q.2.getD sl.1 0) sl.2)
    hp (hp.prod hz) ((zip encNat encNat).comp (hsign.prod hlit)) hfac
  exact h.of_enc_eq fun _ => rfl

/-- `evalGateTraceMod` is computable in polynomial time uniformly over growing binary modulus
`p`, binary circuit input count `Q`, residue vector `z`, and raw De Morgan code `gates`. -/
@[fun_prop]
theorem computableInPolyTime_evalGateTraceMod {α : Type} {enc : α ↪ List Bool}
    {p Q : α → ℕ} {z : α → List ℕ} {gates : α → List (Op × List ℕ)}
    (hp : ComputableInPolyTime p enc encNat)
    (hQ : ComputableInPolyTime Q enc encNat)
    (hz : ComputableInPolyTime z enc (encList encNat))
    (hgates : ComputableInPolyTime gates enc (encList encGate)) :
    ComputableInPolyTime (fun a => evalGateTraceMod (p a) (Q a) (z a) (gates a)) enc encNat := by
  let parFn (x : α) : ℕ × ℕ × List ℕ := (p x, Q x, z x)
  let stepFn (par : ℕ × ℕ × List ℕ) (acc : ℕ × ℕ) (g : Op × List ℕ) : ℕ × ℕ :=
    let a := par.2.2.getD (g.2.getD 0 0) 0
    let b := par.2.2.getD (g.2.getD 1 0) 0
    let w := par.2.2.getD (par.2.1 + acc.1) 0
    (acc.1 + 1, mulMod par.1 acc.2 (eqBitMod par.1 w (opEvalMod par.1 g.1 a b)))
  have hpar : ComputableInPolyTime parFn enc (encPair encNat (encPair encNat (encList encNat))) :=
    hp.prod (hQ.prod hz)
  have hinit : ComputableInPolyTime (fun x => (0, mulMod (p x) 1 1)) enc
      (encPair encUnary encNat) :=
    (const 0).prod (computableInPolyTime_mulMod hp (const 1) (const 1))
  have hstep : ComputableInPolyTime
      (fun r : ((ℕ × ℕ × List ℕ) × (ℕ × ℕ)) × (Op × List ℕ) =>
        stepFn r.1.1 r.1.2 r.2)
      (encPair (encPair (encPair encNat (encPair encNat (encList encNat)))
        (encPair encUnary encNat)) encGate)
      (encPair encUnary encNat) := by
    let encArg := encPair (encPair (encPair encNat (encPair encNat (encList encNat)))
      (encPair encUnary encNat)) encGate
    have hpar_r : ComputableInPolyTime
        (fun r : ((ℕ × ℕ × List ℕ) × (ℕ × ℕ)) × (Op × List ℕ) => r.1.1)
        encArg (encPair encNat (encPair encNat (encList encNat))) := (fst _ _).comp (fst _ _)
    have hacc_r : ComputableInPolyTime
        (fun r : ((ℕ × ℕ × List ℕ) × (ℕ × ℕ)) × (Op × List ℕ) => r.1.2)
        encArg (encPair encUnary encNat) := (snd _ _).comp (fst _ _)
    have hg_r : ComputableInPolyTime
        (fun r : ((ℕ × ℕ × List ℕ) × (ℕ × ℕ)) × (Op × List ℕ) => r.2)
        encArg encGate := snd _ _
    have hp_r := hpar_r.fst'
    have hQ_r := hpar_r.snd'.fst'
    have hz_r := hpar_r.snd'.snd'
    have hidxU := hacc_r.fst'
    have hidxB := unary_to_binary.comp hidxU
    have hprod := hacc_r.snd'
    have hop := hg_r.fst'
    have hwires := hg_r.snd'
    have ha : ComputableInPolyTime
        (fun r : ((ℕ × ℕ × List ℕ) × (ℕ × ℕ)) × (Op × List ℕ) =>
          r.1.1.2.2.getD (r.2.2.getD 0 0) 0) encArg encNat :=
      listGetD_binary 0 hz_r (listGetDWithInput hwires (const 0) 0)
    have hb : ComputableInPolyTime
        (fun r : ((ℕ × ℕ × List ℕ) × (ℕ × ℕ)) × (Op × List ℕ) =>
          r.1.1.2.2.getD (r.2.2.getD 1 0) 0) encArg encNat :=
      listGetD_binary 0 hz_r (listGetDWithInput hwires (const 1) 0)
    have hw : ComputableInPolyTime
        (fun r : ((ℕ × ℕ × List ℕ) × (ℕ × ℕ)) × (Op × List ℕ) =>
          r.1.1.2.2.getD (r.1.1.2.1 + r.1.2.1) 0) encArg encNat :=
      listGetD_binary 0 hz_r (binary_add' hQ_r hidxB)
    exact (unary_succ.comp hidxU).prod
      (computableInPolyTime_mulMod hp_r hprod
        (computableInPolyTime_eqBitMod hp_r hw (computableInPolyTime_opEvalMod hp_r hop ha hb)))
  have hbound : PolyBounded (fun x => (enc x).length)
      (fun x => 2 * (encList encGate (gates x)).length + 1 + (encNat (p x)).length) :=
    PolyBounded.add (PolyBounded.add (PolyBounded.mul (PolyBounded.const 2)
      hgates.polyBounded_length) (PolyBounded.const 1)) hp.polyBounded_length
  have hfold := (foldlWith_spec hpar hgates hinit hstep
    (fun x consumed acc => acc.1 = consumed.length ∧ acc.2 ≤ p x)
    (fun x => ⟨rfl, mulMod_le (p x) 1 1⟩)
    (fun x consumed acc g _ ⟨h1, _⟩ => ⟨by simp [stepFn, h1], mulMod_le (p x) _ _⟩)
    hbound
    (fun x consumed acc hpref ⟨h1, h2⟩ => by
      have hlen1 : acc.1 ≤ (encList encGate (gates x)).length :=
        h1 ▸ hpref.length_le.trans (SizedListEncoding.length_le (encA := encGate) (gates x))
      have hlen2 : (encNat acc.2).length ≤ (encNat (p x)).length := length_encNat_mono h2
      simp only [length_encPair, encUnary_apply, List.length_replicate]
      omega)).1
  exact hfold.snd'.of_enc_eq fun _ => rfl

/-- **Uniform polynomial-time verifier evaluation of `tableauConstraintPoly`**: evaluates
`eqCubePoly * gateTracePoly * clauseUnsatPoly` mod `p` from
`(p, Q, gates, rVec, z, signWires, litVals)` in time polynomial in their binary lengths. -/
@[fun_prop]
theorem computableInPolyTime_evalConstraintMod {α : Type} {enc : α ↪ List Bool}
    {p Q : α → ℕ} {gates : α → List (Op × List ℕ)} {rVec z signWires litVals : α → List ℕ}
    (hp : ComputableInPolyTime p enc encNat)
    (hQ : ComputableInPolyTime Q enc encNat)
    (hgates : ComputableInPolyTime gates enc (encList encGate))
    (hr : ComputableInPolyTime rVec enc (encList encNat))
    (hz : ComputableInPolyTime z enc (encList encNat))
    (hsign : ComputableInPolyTime signWires enc (encList encNat))
    (hlit : ComputableInPolyTime litVals enc (encList encNat)) :
    ComputableInPolyTime
      (fun a =>
        evalConstraintMod (p a) (Q a) (gates a) (rVec a) (z a) (signWires a) (litVals a))
      enc encNat :=
  (computableInPolyTime_mulMod hp
    (computableInPolyTime_mulMod hp
      (computableInPolyTime_eqCubeMod hp hr hz)
      (computableInPolyTime_evalGateTraceMod hp hQ hz hgates))
    (computableInPolyTime_evalClauseUnsatMod hp hz hsign hlit)).of_enc_eq fun _ => rfl

end EvalModPolyTime

end AlgebraicArith

end Cslib.Complexity.MIP
