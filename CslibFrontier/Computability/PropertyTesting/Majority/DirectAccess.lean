/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.Oracle.Time
public import CslibFrontier.Computability.PropertyTesting.Majority.Decision
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.OfBits
import CslibFrontier.Computability.Probabilistic.Oracle.Traverse
import CslibFrontier.Computability.Probabilistic.Repeat
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Languages.Probabilistic.QueryCount.Support
import CslibFrontier.Foundations.Data.BitString.Weight.ZeroExtend
import CslibFrontier.Languages.Probabilistic.Traverse.SupportWith

/-!
# Direct-access strict-majority tester

For [Goldreich2007DraftR5, Exercise 10.9, p. 498], the machine receives the binary length on
its input tape. It samples independent little-endian address words, skips addresses beyond the
input, queries each remaining position, and compares the count of ones against the binary
cutoff. The empty input is rejected without probes.

## Main results

* `Cslib.BitString.majorityDirectAccess_timeAndQueries`: one halting fair-coin machine, with
  polynomial time in the binary header length and a separate constant probe bound.
-/

public section

namespace Cslib.BitString

open Cslib.Probability Turing.MultiTapeTM

/-- Provide one bit at the requested little-endian address, with zero as the total
handler's default outside the input. -/
noncomputable def majorityInputOracle {n : ℕ} (x : BitString n)
    (request : Unit × List Bool) : StateT Unit PMF (List Bool) :=
  fun s => PMF.pure ([if h : ofBits request.2 < n then x ⟨_, h⟩ else false], s)

private def validRequests (n : ℕ) (words : List (List Bool)) : List (List Bool) :=
  words.filter fun word => decide (ofBits word < n)

private def readBit (word : List Bool) : WordOracleComp Unit (List Bool) :=
  List.take 1 <$> ProbOracleComp.query ((), word)

private def decideReplies (k : ℕ) (δ : ℚ) (n : ℕ) (replies : List (List Bool)) : Bool :=
  decide (majoritySampleAccepts n k δ (replies.countP fun reply => reply.headD false))

/-- The strict-majority sampler on a binary length header. Padded samples count as zero
and require no oracle request. -/
noncomputable def majorityDirectAccess (k : ℕ) (δ : ℚ) (n : ℕ) : WordOracleComp Unit Bool :=
  if n = 0 then pure false else do
    let words ← ProbOracleComp.sample (OracleComp.replicate k (sampleList (Nat.log 2 n + 1)))
    decideReplies k δ n <$> (validRequests n words).mapM readBit

private theorem isOraclePPTOn_majorityDirectAccess (k : ℕ) (δ : ℚ) :
    IsOraclePPTOn encNat encBool (majorityDirectAccess k δ) := by
  let wordsEncoding := encList encBits
  have hwidth : ComputableInPolyTime (fun n : ℕ => Nat.log 2 n + 1) encNat encUnary :=
    ComputableInPolyTime.unary_succ.comp ComputableInPolyTime.binary_log_two
  have hsample : IsOraclePPTOn encNat wordsEncoding (fun n =>
      ProbOracleComp.sample (OracleComp.replicate k (sampleList (Nat.log 2 n + 1)))) :=
    (hwidth.sampleList.replicate (ComputableInPolyTime.const k)).isOraclePPTOn
  have hrequests : ComputableInPolyTime (fun p : ℕ × List (List Bool) => validRequests p.1 p.2)
      (encPair encNat wordsEncoding) wordsEncoding := by
    unfold validRequests
    apply ComputableInPolyTime.filterWithInput (ComputableInPolyTime.snd _ _)
    exact ComputableInPolyTime.binary_lt'
      (ComputableInPolyTime.bitsToNat.comp (ComputableInPolyTime.snd _ _))
      ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.fst _ _))
  have hreplies : IsOraclePPTOn (encPair encNat wordsEncoding) wordsEncoding
      (fun p : ℕ × List (List Bool) => (validRequests p.1 p.2).mapM readBit) :=
    IsOraclePPTOn.mapM_query_take () hrequests (ComputableInPolyTime.const 1)
  have hdecide : ComputableInPolyTime
      (fun p : (ℕ × List (List Bool)) × List (List Bool) => decideReplies k δ p.1.1 p.2)
      (encPair (encPair encNat wordsEncoding) wordsEncoding) encBool := by
    unfold decideReplies
    apply (computableInPolyTime_majoritySampleAccepts k δ).comp
    apply ComputableInPolyTime.prod
    · exact (ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.fst _ _)
    · apply ComputableInPolyTime.unary_to_binary.comp
      apply ComputableInPolyTime.countPWithInput (ComputableInPolyTime.snd _ _)
      exact (ComputableInPolyTime.headD false).comp (ComputableInPolyTime.snd _ _)
  unfold majorityDirectAccess
  exact IsOraclePPTOn.ite (by fun_prop)
    ((ComputableInPolyTime.const false).isOraclePPTOn)
    (hsample.bind_with (hreplies.map_with hdecide))

/-- The same fair-coin machine works for every binary length, with a worst-case polynomial
clock and at most `k` external queries independently of that clock. -/
theorem majorityDirectAccess_timeAndQueries (k : ℕ) (δ : ℚ) :
    ∃ t, PolyBounded (fun n => (encNat n).length) t ∧
      ComputesOracleInTimeAndQueriesOn encNat encBool t (fun _ => k)
        (majorityDirectAccess k δ) := by
  obtain ⟨t, ht, htime⟩ := isOraclePPTOn_iff_exists_polyBounded_computesOracleInTimeOn.mp
    (isOraclePPTOn_majorityDirectAccess k δ)
  refine ⟨t, ht, htime, fun n => ?_⟩
  unfold majorityDirectAccess
  split
  · exact .pure _ _
  let coins := OracleComp.replicate k (sampleList (Nat.log 2 n + 1))
  have hlen (words : List (List Bool)) (h : words ∈ (ProbComp.eval coins).support) :
      words.length = k := by
    rw [ProbComp.eval_replicate_sampleList] at h
    obtain ⟨_, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp h
    simp
  have hsample := ProbOracleComp.IsQueryBounded.sample (spec := fun _ : Unit × List Bool =>
    List Bool) coins
  rw [← Nat.zero_add k]
  apply hsample.bind_on_support
  intro words hwords
  have hlen' := hlen words (by simpa only [ProbOracleComp.support_sample] using hwords)
  have htraverse : ((validRequests n words).mapM readBit).IsQueryBounded
      ((validRequests n words).length * 1) :=
    OracleComp.IsCostBounded.mapM fun word _ =>
      (ProbOracleComp.IsQueryBounded.query ((), word)).map (List.take 1)
  exact (htraverse.map (decideReplies k δ n)).mono
    (by simpa only [Nat.mul_one, ← hlen'] using List.length_filter_le _ words)

end Cslib.BitString
