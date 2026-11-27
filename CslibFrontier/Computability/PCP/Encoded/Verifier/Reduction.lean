/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.Encoded.Verifier.Repetition
public import CslibFrontier.Computability.Complexity.Classes.PCP.Promise
import CslibFrontier.Computability.Complexity.Classes.SharpP.Probability
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Log
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# From efficient gap reductions to PCP verifiers

An efficient reduction to well-formed constraint graphs with a fixed positive gap gives a
polynomial-time verifier with logarithmic randomness and constantly many queries. The verifier
constructs the graph before performing fixed many local checks. Its cost includes that complete
construction, every sampled edge, all copied queries, and every verdict.

The alphabet has a fixed-width binary representation with a decoding left inverse. Completeness
packs one block per declared vertex; soundness interprets every proof, even a short one, as a
consistent labelling. Random strings of arbitrary length remain covered by the cost certificate.

The reduction may be one from a promise problem. Completeness, and well-formedness of the
constructed graph, are then needed only on yes-instances, and the gap only on no-instances.

## Main definitions

* `Cslib.PCP.Encoded.Graph.reductionVerifier`: graph construction followed by repeated local checks.

## Main results

* `Cslib.PCP.Encoded.Graph.polyTime_reductionVerifier`: the verifier is polynomial-time when the
  graph construction and the constraint evaluation are.
* `Cslib.PCP.Encoded.Graph.mem_PromisePCP_of_gapReduction`: a positive-gap reduction from a
  promise problem gives membership in the promise class `PCP(log n, 1)`.
* `Cslib.PCP.Encoded.Graph.mem_PCP_of_gapReduction`: the case of a decision problem.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Chapter 11.
* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
-/

@[expose] public section

namespace Cslib.PCP.Encoded.Graph

open Cslib.Complexity Turing.MultiTapeTM

variable {Input C α : Type}

/-- Construct a constraint graph and perform a fixed number of independent local checks. -/
def reductionVerifier (graph : Input → Graph C) (width repeats : ℕ)
    (decode : (Fin width → Bool) → α) (eval : C → α → α → Bool) : PCPVerifier Input :=
  let check := repeatedEdgeVerifier width repeats decode eval
  { coins := fun x => check.coins (graph x)
    queries := fun p => check.queries (graph p.1, p.2)
    verdict := fun p => check.verdict ((graph p.1.1, p.1.2), p.2) }

/-- Graph construction and each verifier component compose through their ordinary certificates. -/
theorem polyTime_reductionVerifier {graph : Input → Graph C} (width repeats : ℕ)
    (decode : (Fin width → Bool) → α)
    {input : Input ↪ List Bool} {enc : C ↪ List Bool} {alphabet : α ↪ List Bool}
    {eval : C → α → α → Bool}
    (hgraph : ComputableInPolyTime graph input (encoding enc))
    (heval : ComputableInPolyTime (fun p : C × α × α => eval p.1 p.2.1 p.2.2)
      (encEvalInput enc alphabet) encBool) :
    (reductionVerifier graph width repeats decode eval).PolyTime input :=
  have h := polyTime_repeatedEdgeVerifier width repeats decode heval
  { coins := h.coins.comp hgraph
    queries := h.queries.comp (by fun_prop)
    verdict := h.verdict.comp (by fun_prop) }

/-- An efficient graph reduction from a promise problem, well-formed on yes-instances and with a
fixed positive gap on no-instances, gives a promise PCP using logarithmic randomness and
constantly many queries. The alphabet representation precedes the input. -/
theorem mem_PromisePCP_of_gapReduction {graph : Input → Graph C} (width : ℕ)
    (encode : α → Fin width → Bool) (decode : (Fin width → Bool) → α)
    (hdecode : Function.LeftInverse decode encode)
    {input : Input ↪ List Bool} {enc : C ↪ List Bool} {alphabet : α ↪ List Bool}
    {eval : C → α → α → Bool}
    (hgraph : ComputableInPolyTime graph input (encoding enc))
    (heval : ComputableInPolyTime (fun p : C × α × α => eval p.1 p.2.1 p.2.2)
      (encEvalInput enc alphabet) encBool)
    {Q : PromiseProblem Input} (hwellFormed : ∀ x ∈ Q.yes, (graph x).WellFormed)
    (hcomplete : ∀ x ∈ Q.yes, ((graph x).toGraph eval).Satisfiable)
    {gap : ℝ} (hgap : 0 < gap)
    (hsound : ∀ x ∈ Q.no, gap ≤ ((graph x).toGraph eval).unsatVal) :
    Q ∈ PromisePCP (fun n => Nat.log 2 n + 1) (fun _ => 1) input := by
  obtain ⟨repeats, hrepeats⟩ := exists_pow_lt_of_lt_one (by norm_num : (0 : ℝ) < 1 / 2)
    (by linarith : 1 - gap / 2 < 1)
  have hlength : ComputableInPolyTime (fun x => (graph x).edges.length)
      input encUnary := by fun_prop
  obtain ⟨c, d, hbound⟩ := hlength.polyBounded_length.exists_le
  have hpoly : PolynomiallyBounded (fun n => c * (n + 1) ^ d) := by fun_prop
  obtain ⟨constant, hconstant⟩ := hpoly.exists_clog_le_mul_log
  refine ⟨reductionVerifier graph width repeats decode eval,
    repeats * constant, repeats * (2 * width),
    polyTime_reductionVerifier width repeats decode hgraph heval, ?_⟩
  constructor
  case coins_le =>
    intro x
    have hb : (graph x).edges.length ≤ c * ((input x).length + 1) ^ d := by simpa using hbound x
    calc repeats * Nat.clog 2 (graph x).edges.length
      _ ≤ repeats * Nat.clog 2 (c * ((input x).length + 1) ^ d) := by gcongr
      _ ≤ repeats * (constant * (Nat.log 2 (input x).length + 1)) :=
        Nat.mul_le_mul_left _ (hconstant _)
      _ = repeats * constant * (Nat.log 2 (input x).length + 1) := (Nat.mul_assoc _ _ _).symm
  case length_queries_le =>
    intro x random _
    simp only [reductionVerifier, length_queries_repeatedEdgeVerifier, mul_one, le_refl]
  case complete =>
    intro x hx
    obtain ⟨labels, hlabels⟩ := hcomplete x hx
    exact ⟨proofOfLabels width (graph x).vertices encode labels, fun random _ =>
      repeated_accepts_proofOfLabels width repeats encode decode hdecode eval
        (hwellFormed x hx) labels hlabels random⟩
  case sound =>
    intro x hx proof
    refine (acceptCount_le_half_iff _ _ _).mpr ?_
    erw [acceptProb_repeatedEdgeVerifier]
    rw [ENNReal.toReal_pow]
    exact (pow_le_pow_left₀ ENNReal.toReal_nonneg
      (by linarith [acceptProb_edgeVerifier_le width decode eval (graph x) proof, hsound x hx])
      repeats).trans hrepeats.le

/-- An efficient well-formed graph reduction with a fixed positive gap gives a PCP using logarithmic
randomness and constantly many queries. The alphabet representation precedes the input. -/
theorem mem_PCP_of_gapReduction {graph : Input → Graph C} (width : ℕ)
    (encode : α → Fin width → Bool) (decode : (Fin width → Bool) → α)
    (hdecode : Function.LeftInverse decode encode)
    {input : Input ↪ List Bool} {enc : C ↪ List Bool} {alphabet : α ↪ List Bool}
    {eval : C → α → α → Bool}
    (hgraph : ComputableInPolyTime graph input (encoding enc))
    (heval : ComputableInPolyTime (fun p : C × α × α => eval p.1 p.2.1 p.2.2)
      (encEvalInput enc alphabet) encBool)
    (hwellFormed : ∀ x, (graph x).WellFormed) {A : Set Input}
    (hcomplete : ∀ x ∈ A, ((graph x).toGraph eval).Satisfiable)
    {gap : ℝ} (hgap : 0 < gap)
    (hsound : ∀ x ∉ A, gap ≤ ((graph x).toGraph eval).unsatVal) :
    A ∈ PCP (fun n => Nat.log 2 n + 1) (fun _ => 1) input :=
  ofSet_mem_PromisePCP.mp <| mem_PromisePCP_of_gapReduction width encode decode hdecode hgraph
    heval (Q := .ofSet A) (fun x _ => hwellFormed x) hcomplete hgap hsound

end Cslib.PCP.Encoded.Graph
