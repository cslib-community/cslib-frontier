/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.Oracle.Time
public import CslibFrontier.Computability.PropertyTesting.Majority.Decision
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.OfBits
import CslibFrontier.Computability.Probabilistic.Oracle.Traverse
import CslibFrontier.Computability.Probabilistic.Repeat
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Languages.Probabilistic.QueryCount.Support
import CslibFrontier.Foundations.Data.BitString.Weight.ZeroExtend
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Languages.Probabilistic.Traverse.SupportWith

/-!
# Direct-access strict-majority tester

For [Goldreich2007DraftR5, Exercise 10.9, p. 498], the machine receives the binary length on
its input tape. It samples independent little-endian address words, skips addresses beyond the
input, queries each remaining position, and compares the count of ones against the binary
cutoff. The empty input is rejected without probes.

## Main results

* `Cslib.BitString.exists_majorityDirectAccess`: a constant-probe tester with
  polylogarithmic direct-access time and error at most one third.
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

private theorem runWith_readBits {n : ℕ} (x : BitString n) (words : List (List Bool)) :
    ProbOracleComp.runWith (majorityInputOracle x) (words.mapM readBit) () =
      PMF.pure (words.map (fun word =>
        [if h : ofBits word < n then x ⟨_, h⟩ else false]), ()) := by
  induction words with
  | nil => simp
  | cons word words ih =>
    simp [List.mapM_cons, readBit, majorityInputOracle, ih]

/-- Under the indexed input handler, the direct-access program has the law of drawing its
address words and applying the cutoff to the retained replies. -/
private theorem runWith_majorityDirectAccess {n : ℕ} (hn : n ≠ 0)
    (x : BitString n) (k : ℕ) (δ : ℚ) :
    ProbOracleComp.runWith (majorityInputOracle x) (majorityDirectAccess k δ n) () =
      (ProbComp.eval (OracleComp.replicate k (sampleList (Nat.log 2 n + 1)))).map
        (fun words => (decideReplies k δ n ((validRequests n words).map fun word =>
          [if h : ofBits word < n then x ⟨_, h⟩ else false]), ())) := by
  rw [majorityDirectAccess, ite_eq_right hn, ProbOracleComp.runWith_sample_bind,
    ← PMF.bind_pure_comp]
  congr 1
  funext words
  rw [ProbOracleComp.runWith_map, runWith_readBits, PMF.pure_map]
  rfl

/-- The oracle program returns the same verdict in law as the local test on a uniform seed. -/
theorem majorityDirectAccess_eq_majorityTester {n k : ℕ} [NeZero n] {δ : ℚ}
    (hk : 0 < k) (hδ : 0 ≤ δ) (x : BitString n) :
    ProbOracleComp.runWith (majorityInputOracle x) (majorityDirectAccess k δ n) () =
      (PMF.uniformOfFintype (Fin k → BitString (Nat.log 2 n + 1))).map
        (fun r => (decide ((majorityTester n k δ).Passes x r), ())) := by
  classical
  rw [runWith_majorityDirectAccess (NeZero.ne n), ProbComp.eval_replicate_sampleList,
    PMF.map_comp]
  congr 1
  funext r
  simp only [Function.comp_apply, decideReplies, validRequests, List.countP_map,
    List.countP_filter, List.map_ofFn, List.countP_ofFn, ofBits_ofFn, List.headD_cons]
  refine congrArg (·, ()) (Bool.eq_iff_iff.mpr ?_)
  rw [decide_eq_true_eq, decide_eq_true_eq, majorityTester_passes_iff_sampleAccepts hk hδ x r]
  apply eq_iff_iff.mp
  congr 2
  ext j
  by_cases hj : (equivFin _ (r j)).val < n <;> simp [zeroExtend, hj]

private theorem isOraclePPTOn_majorityDirectAccess (k : ℕ) (δ : ℚ) :
    IsOraclePPTOn encNat encBool (majorityDirectAccess k δ) := by
  let wordsEncoding := encList encBits
  have hwidth : ComputableInPolyTime (fun n : ℕ => Nat.log 2 n + 1) encNat encUnary :=
    ComputableInPolyTime.unary_succ.comp ComputableInPolyTime.binary_log_two
  have hsample : IsOraclePPTOn (Operation := Unit) encNat wordsEncoding (fun n =>
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
    let encInput := encPair (encPair encNat wordsEncoding) wordsEncoding
    have hlength := (ComputableInPolyTime.fst encNat wordsEncoding).comp
      (ComputableInPolyTime.fst (encPair encNat wordsEncoding) wordsEncoding)
    have hcount := ComputableInPolyTime.countPWithInput (test := fun _ reply => reply.headD false)
      (ComputableInPolyTime.snd (encPair encNat wordsEncoding) wordsEncoding)
      ((ComputableInPolyTime.headD (encA := encBool) false).comp
        (ComputableInPolyTime.snd encInput encBits))
    exact (computableInPolyTime_majoritySampleAccepts k δ).comp
      (hlength.prod (ComputableInPolyTime.unary_to_binary.comp hcount))
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
  change (ProbOracleComp.sample coins >>= fun words =>
    decideReplies k δ n <$> (validRequests n words).mapM readBit).IsQueryBounded k
  suffices h : (ProbOracleComp.sample coins >>= fun words =>
      decideReplies k δ n <$> (validRequests n words).mapM readBit).IsQueryBounded (0 + k) by
    simpa only [Nat.zero_add] using h
  refine hsample.bind_on_support fun words hwords => ?_
  have hlen' := hlen words (by simpa only [ProbOracleComp.support_sample] using hwords)
  have htraverse : ((validRequests n words).mapM readBit).IsQueryBounded
      ((validRequests n words).length * 1) :=
    OracleComp.IsCostBounded.mapM fun word _ => by
      unfold readBit
      rw [map_eq_bind_pure_comp]
      simpa only [Nat.add_zero, Function.comp_def] using
        (ProbOracleComp.IsQueryBounded.query
          (spec := fun _ : Unit × List Bool => List Bool) ((), word)).bind
          (fun reply : List Bool => OracleComp.IsCostBounded.pure (reply.take 1) 0)
  rw [map_eq_bind_pure_comp]
  exact (htraverse.bind fun replies =>
    OracleComp.IsCostBounded.pure (decideReplies k δ n replies) 0).mono
    (by simpa only [Nat.add_zero, Nat.mul_one, validRequests, ← hlen'] using
      List.length_filter_le _ words)

private theorem majorityDirectAccess_acceptProb {n k : ℕ} [NeZero n] {δ : ℚ}
    (hk : 0 < k) (hδ : 0 ≤ δ) (x : BitString n) :
    (ProbOracleComp.acceptProbWith (majorityInputOracle x)
      (majorityDirectAccess k δ n) ()).toReal = (majorityTester n k δ).acceptProb x := by
  classical
  rw [ProbOracleComp.acceptProbWith, majorityDirectAccess_eq_majorityTester hk hδ,
    PMF.map_comp, PMF.toReal_uniformOfFintype_map_apply_true,
    Cslib.PCP.LocalTest.acceptProb_eq_card_div, Finset.dens_eq_card_div_card]
  push_cast
  congr 3
  ext r
  simp

/-- For each positive distance, a single direct-access strict-majority tester has a worst-case
clock polynomial in the binary input length and a constant probe bound. It accepts members
with probability at least two thirds and accepts far inputs with probability at most one third. -/
theorem exists_majorityDirectAccess {δ : ℝ} (hδ : 0 < δ) :
    ∃ (k : ℕ) (t : ℕ → ℕ) (program : ℕ → WordOracleComp Unit Bool),
      PolyBounded (fun n => (encNat n).length) t ∧
      ComputesOracleInTimeAndQueriesOn encNat encBool t (fun _ => k) program ∧
      (∀ n (x : BitString n), strictMajority n x = true →
        2 / 3 ≤ (ProbOracleComp.acceptProbWith (majorityInputOracle x) (program n) ()).toReal) ∧
      (∀ n (x : BitString n),
        (∀ y, strictMajority n y = true → δ * n ≤ hammingDist x y) →
        (ProbOracleComp.acceptProbWith (majorityInputOracle x) (program n) ()).toReal ≤ 1 / 3) := by
  obtain ⟨q, hq, hqδ⟩ := exists_rat_btwn hδ
  obtain ⟨k, hk⟩ := exists_nat_ge (16 / (q : ℝ) ^ 2)
  have hbudget : (16 : ℝ) ≤ k * (q : ℝ) ^ 2 := (div_le_iff₀ (pow_pos hq _)).mp hk
  have hkpos : 0 < k := Nat.pos_of_ne_zero fun h0 => by norm_num [h0] at hbudget
  have hqpos : 0 < q := by exact_mod_cast hq
  obtain ⟨t, ht, hcert⟩ := majorityDirectAccess_timeAndQueries k q
  refine ⟨k, t, majorityDirectAccess k q, ht, hcert, ?_, ?_⟩
  · intro n x hx
    have hn : n ≠ 0 := by
      rintro rfl
      exact absurd (strictMajority_eq_true_iff.mp hx) (not_lt_of_ge (weight_le_length x))
    let _ : NeZero n := ⟨hn⟩
    rw [majorityDirectAccess_acceptProb hkpos hqpos.le]
    exact (majorityTester_spec hqpos hbudget).2.1 x hx
  · intro n x hx
    by_cases hn : n = 0
    · subst n
      simp [majorityDirectAccess, ProbOracleComp.acceptProbWith, PMF.pure_map, PMF.pure_apply]
    · let _ : NeZero n := ⟨hn⟩
      rw [majorityDirectAccess_acceptProb hkpos hqpos.le]
      exact (majorityTester_spec hqpos hbudget).2.2 x fun y hy =>
        (mul_le_mul_of_nonneg_right hqδ.le (Nat.cast_nonneg n)).trans (hx y hy)

end Cslib.BitString
