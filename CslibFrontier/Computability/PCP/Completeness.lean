/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.NP.Relation
public import CslibFrontier.Computability.Complexity.Classes.PCP.NP
public import Mathlib.Data.Nat.Log
import CslibFrontier.Computability.Complexity.Classes.SharpP.Probability
import CslibFrontier.Computability.Complexity.CookLevin.Levin
import CslibFrontier.Computability.PCP.Encoded.Witness
import CslibFrontier.Computability.PCP.Encoded.Verifier.Reduction
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Log

/-!
# The PCP theorem

`NP = PCP(log n, 1)`: every problem in NP has a polynomial-time verifier that uses `O(log n)`
random bits and reads a constant number of proof bits, accepts some proof of every member on every
random string, and accepts every proof of a non-member on at most half of the random strings. NP
is the library's deterministic-verifier class.

## Proof overview

The inclusion `NP ⊆ PCP(log n, 1)` follows Dinur [Dinur2007]. Every stage after Cook–Levin is a
program on explicit constraint graphs (`Cslib.PCP.Encoded.Graph`), with a polynomial-time
certificate and an exact interpretation as a construction on mathematical constraint graphs
(`Cslib.PCP.ConstraintGraph`), where its soundness is proved.

1. **Cook–Levin** (`Cslib.Complexity.CookLevin.SAT_npHard`) reduces the problem to SAT.
2. **The constraint graph of a formula** (`Cslib.PCP.Encoded.Graph.ofCompactCNF`, after splitting
   clauses with `Cslib.Logic.PL.CNF.to3CNF`) has three edges per clause and the alphabet
   `Fin 3 → Bool`, and is satisfiable exactly when the formula is.
3. **Composition** (`Cslib.PCP.Encoded.Graph.composeSelectedEnumerated`) with the six-query
   Hadamard assignment tester brings the alphabet to the fixed `Cslib.PCP.SelectedAlphabet` of
   `128` symbols, losing at most a factor `840` of the value
   (`Cslib.PCP.ConstraintGraph.le_unsatVal_composeSelected`).
4. **Gap amplification** (`Cslib.PCP.Encoded.Graph.arithmeticAmplify`) runs `⌈log₂ |E|⌉` rounds.
   Each round preprocesses with the explicit arithmetic expanders
   (`Cslib.PCP.ConstraintGraph.preprocessWith`), powers along killed walks
   (`Cslib.PCP.RegularConstraintGraph.power`), and composes back to `SelectedAlphabet`; it doubles
   the value up to the fixed threshold `Cslib.PCP.ConstraintGraph.Amplification.Arithmetic.gap`
   (`Cslib.PCP.ConstraintGraph.min_le_div_unsatVal_power_preprocessWith`). Since an
   unsatisfiable graph with `|E|` edges has value at least `1 / |E|`, the rounds reach the threshold
   (`Cslib.PCP.ConstraintGraph.gap_le_of_min_two_pow_mul_le`). Stages 2 to 4 form
   `Cslib.PCP.Encoded.gapGraph`.
5. **The verifier** (`Cslib.PCP.Encoded.Graph.reductionVerifier`) builds the graph and checks a
   constant number of independently sampled edges, reading the labels of their ends from the proof,
   seven bits each: one for the input label and six for the selected tester's claimed answers. A
   single check rejects with probability at least half the value
   (`Cslib.PCP.Encoded.Graph.unsatVal_div_two_le_rejectProb`), so a constant number of repetitions
   brings the soundness error to one half (`Cslib.PCP.Encoded.Graph.mem_PCP_of_gapReduction`).

The converse inclusion (`Cslib.Complexity.PCP_log_subset_NP`) checks all polynomially many random
strings. Its certificate supplies the bits at all queried addresses, with repeated addresses
sharing one bit.

`Cslib.PCP.Dinur.gapGraph` in `CslibFrontier.Computability.PCP.GapTheorem` renders the same
argument noncomputably, with non-explicit expanders and smaller constants; the theorem here does
not use it. The fixed constants of the explicit construction are enormous, so the result is
asymptotic.

## Main results

* `Cslib.Complexity.exists_pcpVerifier_of_npRelation`: every NP relation has such a PCP verifier
  together with a polynomial-time compiler from its witnesses to accepted compact query tables.
* `Cslib.Complexity.NP_subset_PCP_log`: every problem in NP has such a PCP verifier.
* `Cslib.Complexity.NP_eq_PCP_log`: the class-level PCP theorem.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Chapter 11][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.PCP Cslib.PCP.Encoded HadamardTester Turing.MultiTapeTM
open ConstraintGraph.Amplification.Arithmetic

private def encodeLabel (label : SelectedAlphabet) : Fin (FinEnum.card (Fin 6) + 1) → Bool :=
  Fin.cases label.1 (fun i => label.2 (FinEnum.equiv.symm i))

private def decodeLabel (bits : Fin (FinEnum.card (Fin 6) + 1) → Bool) : SelectedAlphabet :=
  (bits 0, fun query => bits (FinEnum.equiv query).succ)

private theorem decode_encodeLabel : Function.LeftInverse decodeLabel encodeLabel :=
  fun _ => by simp [decodeLabel, encodeLabel]

private theorem exists_pcpVerifier_of_gap {Input : Type} (input : Input ↪ List Bool)
    {A : Set Input} {graph : Input → Graph (SelectedAlphabet → SelectedAlphabet → Bool)}
    {proof : Input × List Bool → List Bool} {W : Input → List Bool → Prop}
    (hgraph : ComputableInPolyTime graph input (Graph.encoding encConstraintTable))
    (hwellFormed : ∀ x, (graph x).WellFormed)
    (hcomplete : ∀ x ∈ A, ((graph x).toGraph id).Satisfiable)
    (hsound : ∀ x ∉ A, gap ≤ ((graph x).toGraph id).unsatVal)
    (hproof : ComputableInPolyTime proof (encPair input encBits) encBits)
    (hproof_eq : ∀ x w, W x w → ∃ labels : List SelectedAlphabet,
      labels.length = (graph x).vertices ∧
      proof (x, w) = Graph.proofOfLabels (FinEnum.card (Fin 6) + 1) (graph x).vertices
        encodeLabel (fun v => labels.getD v defaultSelectedAlphabet) ∧
      ∀ e, ((graph x).toGraph id).Satisfies (fun v => labels.getD v defaultSelectedAlphabet) e) :
    ∃ (V : PCPVerifier Input) (compile : Input × List Bool → List Bool) (c d : ℕ),
      V.PolyTime input ∧
      IsPCPVerifier input (fun n => c * (Nat.log 2 n + 1)) (fun _ => d) V A ∧
      ComputableInPolyTime compile (encPair input encBits) encBits ∧
      (∀ x w, W x w → V.tableVerifier (x, compile (x, w)) = true) := by
  obtain ⟨repeats, hrepeats⟩ := exists_pow_lt_of_lt_one (by norm_num : (0 : ℝ) < 1 / 2)
    (by linarith [gap_pos] : 1 - gap / 2 < 1)
  obtain ⟨c₀, d₀, hbound⟩ :=
    (by fun_prop : ComputableInPolyTime (fun x => (graph x).edges.length) input
      encUnary).polyBounded_length.exists_le
  obtain ⟨constant, hconstant⟩ := PolynomiallyBounded.exists_clog_le_mul_log
    (by fun_prop : PolynomiallyBounded fun n => c₀ * (n + 1) ^ d₀)
  let width := FinEnum.card (Fin 6) + 1
  let V : PCPVerifier Input := Graph.reductionVerifier graph width repeats decodeLabel id
  have heval : ComputableInPolyTime
      (fun p : (SelectedAlphabet → SelectedAlphabet → Bool) ×
        SelectedAlphabet × SelectedAlphabet => p.1 p.2.1 p.2.2)
      (encPair (encPi (encPi encBool))
        (encPair (encPair encBool (encPi encBool)) (encPair encBool (encPi encBool))))
      encBool :=
    Graph.isPolyTime_constraintTableEval (encPair encBool (encPi encBool))
  have hV : V.PolyTime input :=
    Graph.polyTime_reductionVerifier width repeats decodeLabel hgraph heval
  have hcoins (x : Input) : V.coins x ≤ repeats * constant * (Nat.log 2 (input x).length + 1) := by
    change repeats * Nat.clog 2 (graph x).edges.length ≤
      repeats * constant * (Nat.log 2 (input x).length + 1)
    have hb : (graph x).edges.length ≤ c₀ * ((input x).length + 1) ^ d₀ := by
      simpa using hbound x
    calc _ ≤ repeats * Nat.clog 2 (c₀ * ((input x).length + 1) ^ d₀) := by gcongr
      _ ≤ repeats * (constant * (Nat.log 2 (input x).length + 1)) :=
        Nat.mul_le_mul_left _ (hconstant _)
      _ = _ := (Nat.mul_assoc _ _ _).symm
  let compile : Input × List Bool → List Bool :=
    fun p => PCPVerifier.answers (proof p) (V.queryTable p.1)
  refine ⟨V, compile, repeats * constant, repeats * (2 * width), hV, ⟨hcoins, ?_, ?_, ?_⟩,
    by simpa only [compile, Function.comp_def] using
      (PCPVerifier.isPolyTime_answers hV hcoins).comp
        ((ComputableInPolyTime.fst input encBits).prod hproof), ?_⟩
  · intro x random _
    simp only [V, Graph.reductionVerifier, Graph.length_queries_repeatedEdgeVerifier, le_refl]
  · intro x hx
    obtain ⟨labels, hlabels⟩ := hcomplete x hx
    exact ⟨Graph.proofOfLabels width (graph x).vertices encodeLabel labels, fun random _ =>
      Graph.repeated_accepts_proofOfLabels width repeats encodeLabel decodeLabel
        decode_encodeLabel id (hwellFormed x) labels hlabels random⟩
  · intro x hx proofStr
    apply (acceptCount_le_half_iff _ _ _).mpr
    change (((BitString.uniformList (repeats * Nat.clog 2 (graph x).edges.length)).map
      (fun random => (Graph.repeatedEdgeVerifier width repeats decodeLabel id).accepts
        (graph x) proofStr random)) true).toReal ≤ 1 / 2
    rw [Graph.acceptProb_repeatedEdgeVerifier, ENNReal.toReal_pow]
    have := Graph.acceptProb_edgeVerifier_le width decodeLabel id (graph x) proofStr
    exact (pow_le_pow_left₀ ENNReal.toReal_nonneg (by linarith [hsound x hx]) repeats).trans
      hrepeats.le
  · intro x w hw
    obtain ⟨labels, _, hproofEq, hsat⟩ := hproof_eq x w hw
    simpa only [List.append_nil] using
      PCPVerifier.tableVerifier_complete x (proof (x, w)) [] fun ρ _ => by
        rw [PCPVerifier.accepts, hproofEq]
        exact Graph.repeated_accepts_proofOfLabels width repeats encodeLabel decodeLabel
          decode_encodeLabel id (hwellFormed x) _ hsat ρ

/-- Every NP relation has a polynomial-time PCP verifier with logarithmic randomness and constantly
many nonadaptive proof queries, together with a polynomial-time witness compiler sending any
relation witness `(x, w)` to a compact table accepted by `V.tableVerifier`. -/
theorem exists_pcpVerifier_of_npRelation {Input : Type} (input : Input ↪ List Bool)
    (R : NPRelation input) :
    ∃ (V : PCPVerifier Input) (compile : Input × List Bool → List Bool) (c d : ℕ),
      V.PolyTime input ∧
      IsPCPVerifier input (fun n => c * (Nat.log 2 n + 1)) (fun _ => d) V R.language ∧
      ComputableInPolyTime compile (encPair input encBits) encBits ∧
      (∀ x w, R.IsWitness x w → V.tableVerifier (x, compile (x, w)) = true) := by
  obtain ⟨lev⟩ := CookLevin.SAT_levinHard input R
  have hmem (x : Input) : x ∈ R.language ↔ (lev.toFun x).Satisfiable := by
    simpa [SAT, SAT.language_npRelation] using lev.mem_language_iff x
  let labels : Input × List Bool → List SelectedAlphabet :=
    fun p => gapGraphLabels (lev.toFun p.1) (lev.forwardWitness p)
  have hlabels :
      ComputableInPolyTime labels (encPair input encBits) (encList encSelectedAlphabet) :=
    isPolyTime_gapGraphLabels
      (lev.computableInPolyTime_toFun.comp (ComputableInPolyTime.fst input encBits))
      lev.computableInPolyTime_forwardWitness
  refine exists_pcpVerifier_of_gap input
    (isPolyTime_gapGraph lev.computableInPolyTime_toFun)
    (fun x => wellFormed_gapGraph (lev.toFun x))
    (fun x hx => (satisfiable_gapGraph_iff _).mpr ((hmem x).mp hx))
    (fun x hx => gap_le_unsatVal_gapGraph _ fun h => hx ((hmem x).mpr h))
    (Graph.isPolyTime_proofOfLabelList encodeLabel hlabels) fun x w hw => ?_
  have hlen : (labels (x, w)).length = (gapGraph (lev.toFun x)).vertices :=
    length_gapGraphLabels _ _
  refine ⟨labels (x, w), hlen, ?_,
    fun e => satisfies_gapGraphLabels (lev.isWitness_forwardWitness x w hw) e⟩
  simpa only [hlen] using
    Graph.proofOfLabelList_eq_proofOfLabels encodeLabel defaultSelectedAlphabet (labels (x, w))

/-- Every NP language has a polynomial-time verifier with logarithmic randomness and constantly
many nonadaptive proof queries, perfect completeness, and soundness at most one half. -/
theorem NP_subset_PCP_log {Input : Type} (input : Input ↪ List Bool) :
    NP input ⊆ PCP (fun n => Nat.log 2 n + 1) (fun _ => 1) input := by
  intro A hA
  obtain ⟨R, rfl⟩ := (mem_NP_iff_exists_npRelation (enc := input)).mp hA
  obtain ⟨V, _, c, d, hV, hpcp, -, -⟩ := exists_pcpVerifier_of_npRelation input R
  exact ⟨V, c, d, hV, by simpa using hpcp⟩

/-- **The PCP theorem:** NP is exactly logarithmic-randomness, constant-query PCP, with perfect
completeness and soundness at most one half. -/
theorem NP_eq_PCP_log {Input : Type} (input : Input ↪ List Bool) :
    NP input = PCP (fun n => Nat.log 2 n + 1) (fun _ => 1) input :=
  Set.Subset.antisymm (NP_subset_PCP_log input) (PCP_log_subset_NP _)

end Cslib.Complexity
