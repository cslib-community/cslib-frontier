/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.PseudorandomFunction.RandomOracle
public import CslibFrontier.Crypto.Encoding
public import CslibFrontier.Crypto.Primitives.PRF.HashThenPRF
public import CslibFrontier.Crypto.Primitives.UHF.Computational
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.Oracle.Substitution
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Crypto.Game.CloseTo
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Languages.Probabilistic.Oracle.Substitution.QueryCount
import CslibFrontier.Languages.Probabilistic.Oracle.Substitution.RunWith
import CslibFrontier.Languages.Probabilistic.RandomOracle.Probabilistic
import CslibFrontier.Languages.Probabilistic.RandomOracle.Through
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.PMF.UniformPoint
import CslibFrontier.Tactic.PolyTime

/-!
# Computational security of hash-then-PRF on words

The reduction samples a private hash key and forwards the digest of each valid word to its
PRF challenger. Malformed words receive an empty reply without a call. A reply is read only
up to the declared output width, even if the challenger returns a longer word.

This is the real-game step of [BonehShoup2023], v0.6, §7.3, printed p. 264, toward (7.21).
The real law uses two independent uniform keys and the composition `PRF.hashThenPRF` from
(7.18). The hash is given on words with a polynomial-time domain test. Repeated queries are
allowed.

The query collector for Game 2 runs the same adversary against a fresh lazy random function and
outputs the distinct valid queries in its cache. It is strict PPT and its output length is bounded
by the adversary's query budget. Equation (7.22) is the ideal-game comparison: hashing before the
random function changes the adversary's success probability by at most the probability that
Game 2's collected queries contain a hash collision.

The resulting uniform strict oracle-PPT security theorem is the word form of Theorem 7.7.
The PRF key has `n` bits and the independently sampled hash key has `keyLen n` bits. The
ideal random function is sampled lazily on the valid message domain regardless of its size.
The two concrete bounds use the certified multi-query collector and the bounded fair-bit
collision-pair reduction.

## Main definitions

* `Cslib.Crypto.PRF.hashThenPRFWordReduction`: the explicit word-oracle adversary `B_F`.
* `Cslib.Crypto.PRF.hashThenPRFWordRealGame`: the real game under independent keys.
* `Cslib.Crypto.PRF.hashThenPRFWordIdealRun`: the decision and final cache in Game 2.
* `Cslib.Crypto.PRF.hashThenPRFWordIdealQueries`: the word query collector `B'_H` in Game 2.

## Main results

* `Cslib.Crypto.PRF.isOraclePPT_hashThenPRFWordReduction`: uniform strict oracle PPT.
* `Cslib.Crypto.PRF.isQueryBounded_hashThenPRFWordReduction`: at most one call per input query.
* `Cslib.Crypto.PRF.eval_prfRealGame_hashThenPRFWordReduction`: its real PRF run has the law
  of Game 0 of the proof of Theorem 7.7.
* `Cslib.Crypto.PRF.isPPTOn_hashThenPRFWordIdealQueries`: a uniform strict PPT collector.
* `Cslib.Crypto.PRF.nodup_valid_of_mem_support_hashThenPRFWordIdealQueries`: collected queries
  are distinct and valid.
* `Cslib.Crypto.PRF.length_le_of_mem_support_hashThenPRFWordIdealQueries`: output length respects
  the adversary's query bound.
* `Cslib.Crypto.PRF.advantage_prfIdealGame_hashThenPRFWordReduction_le`: the comparison of the
  two ideal games.
* `Cslib.Crypto.PRF.advantage_hashThenPRFWord_le_add_multiQuery` and
  `Cslib.Crypto.PRF.advantage_hashThenPRFWord_le_add_collision`: equations (7.20) and (7.19).
* `Cslib.Crypto.PRF.computableInPolyTime_hashThenPRFWord`: the composition's evaluator.
* `Cslib.Crypto.PRF.hashThenPRFWord_indistinguishable`: the asymptotic word security theorem.
-/

public section

namespace Cslib.Crypto.PRF

open Probability Turing.MultiTapeTM
open scoped ENNReal NNReal

private def hashThenPRFWordHandler (valid : List Bool → Bool)
    (H : List Bool → List Bool) (outLen : ℕ) (request : Unit × List Bool) :
    WordOracleComp Unit (List Bool) :=
  if valid request.2 then List.take outLen <$> ProbOracleComp.query ((), H request.2)
  else pure []

/-- Sample a `keyLen n`-bit hash key and run the adversary. Each valid query is hashed and
forwarded, and the reply prefix of length at most `outLen n` is returned to the adversary. -/
noncomputable def hashThenPRFWordReduction (keyLen outLen : ℕ → ℕ)
    (valid : ℕ → List Bool → Bool) (H : ℕ → List Bool → List Bool → List Bool)
    (A : OracleDistinguisher) : OracleDistinguisher := fun n aux => do
  let key ← ProbOracleComp.sample (BitString.sampleList (keyLen n))
  ProbOracleComp.simulate (hashThenPRFWordHandler (valid n) (H n key) (outLen n)) (A n aux)

/-- The reduction's query budget is at most that of the original adversary. -/
theorem isQueryBounded_hashThenPRFWordReduction (keyLen outLen : ℕ → ℕ)
    (valid : ℕ → List Bool → Bool) (H : ℕ → List Bool → List Bool → List Bool)
    {A : OracleDistinguisher} {n Q : ℕ} {aux : List Bool} (hQ : (A n aux).IsQueryBounded Q) :
    (hashThenPRFWordReduction keyLen outLen valid H A n aux).IsQueryBounded Q := by
  rw [hashThenPRFWordReduction, ← Nat.zero_add Q]
  refine (ProbOracleComp.IsQueryBounded.sample _).bind fun key => hQ.simulate fun request => ?_
  unfold hashThenPRFWordHandler
  split_ifs
  · exact (OracleComp.isCostBounded_map_iff _ _ _).mpr (ProbOracleComp.IsQueryBounded.query _)
  · exact OracleComp.IsCostBounded.pure _ 1

/-- The word reduction is uniform strict oracle PPT when the hash evaluator, domain test and
unary width schedules are polynomial-time, and the original adversary is strict oracle PPT. -/
theorem isOraclePPT_hashThenPRFWordReduction {keyLen outLen : ℕ → ℕ}
    {valid : ℕ → List Bool → Bool} {H : ℕ → List Bool → List Bool → List Bool}
    (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary)
    (houtLen : ComputableInPolyTime outLen encUnary encUnary)
    (hvalid : ComputableInPolyTime (fun p => valid p.1 p.2) (encPair encUnary encBits) encBool)
    (hH : ComputableInPolyTime (fun p => H p.1 p.2.1 p.2.2)
      (encKeyedInput encBits) encBits)
    {A : OracleDistinguisher} (hA : IsOraclePPT encBool A) :
    IsOraclePPT encBool (hashThenPRFWordReduction keyLen outLen valid H A) := by
  let E := encPair encUnary encBits
  let ECaller := encPair E encBits
  let ERequest := encPair (encFinEnum Unit) encBits
  let en := (ComputableInPolyTime.fst ECaller ERequest).fst'.fst'
  let ekey := (ComputableInPolyTime.fst ECaller ERequest).snd'
  let emsg := (ComputableInPolyTime.snd ECaller ERequest).snd'
  have hhandler : IsOraclePPTOn (encPair ECaller ERequest) encBits
      (fun p => hashThenPRFWordHandler (valid p.1.1.1) (H p.1.1.1 p.1.2)
        (outLen p.1.1.1) p.2) := by
    unfold hashThenPRFWordHandler
    exact IsOraclePPTOn.ite (hvalid.comp (en.prod emsg))
      (IsOraclePPTOn.query_take () (hH.comp (en.prod (ekey.prod emsg))) (houtLen.comp en))
      (ComputableInPolyTime.const ([] : List Bool)).isPPTOn.isOraclePPTOn
  have hrun : IsOraclePPTOn ECaller encBool (fun p => ProbOracleComp.simulate
      (hashThenPRFWordHandler (valid p.1.1) (H p.1.1 p.2) (outLen p.1.1)) (A p.1.1 p.1.2)) := by
    simp only [ProbOracleComp.simulate, OracleComp.substitute_eq_interpret]
    exact IsOraclePPTOn.interpret_preprocess_open' (operationEncoding := encFinEnum Unit)
      (prepare := Prod.fst) (resources := fun (p : (ℕ × List Bool) × List Bool) _ => outLen p.1.1)
      hA.on (ComputableInPolyTime.fst E encBits) hhandler
      (houtLen.comp (ComputableInPolyTime.fst ECaller encBits).fst'.fst') (by
        intro p request reply hreply
        unfold hashThenPRFWordHandler at hreply
        split_ifs at hreply
        · obtain ⟨raw, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hreply
          exact List.length_take_le _ raw
        · obtain rfl : reply = [] := by
            simpa only [OracleComp.support, OracleComp.supportWith_pure, Set.mem_singleton_iff]
              using hreply
          exact Nat.zero_le _)
  have hsample := (hkeyLen.comp (ComputableInPolyTime.fst encUnary encBits)).sampleList
  exact (hsample.isOraclePPTOn.bind_with hrun).isOraclePPT

/-- The word real game for (7.18) in [BonehShoup2023], v0.6, §7.3, printed pp. 262–264.
Sample independent uniform hash and PRF keys, giving empty replies to invalid requests. -/
@[expose] noncomputable def hashThenPRFWordRealGame (keyLen : ℕ → ℕ)
    (valid : ℕ → List Bool → Bool) (H : ℕ → List Bool → List Bool → List Bool)
    (F : List Bool → List Bool → List Bool) (A : OracleDistinguisher) (n : ℕ) : ProbComp Bool := do
  let hashKey ← BitString.sampleList (keyLen n)
  let prfKey ← BitString.sampleList n
  (A n []).run fun req => pure (if valid n req.2 then
    hashThenPRF (H n) F (hashKey, prfKey) req.2 else [])

/-- Polynomial-time evaluation of the composition. The unary parameter is framed before the
framed pair of word keys and the message. -/
theorem computableInPolyTime_hashThenPRFWord
    {H : ℕ → List Bool → List Bool → List Bool} {F : List Bool → List Bool → List Bool}
    (hH : ComputableInPolyTime (fun p => H p.1 p.2.1 p.2.2)
      (encKeyedInput encBits) encBits)
    (hF : ComputableInPolyTime (fun p => F p.1 p.2) (encPair encBits encBits) encBits) :
    ComputableInPolyTime (fun (n, keys, msg) => hashThenPRF (H n) F keys msg)
      (encPair encUnary (encPair (encPair encBits encBits) encBits)) encBits := by
  let payload := encPair (encPair encBits encBits) encBits
  let hn := ComputableInPolyTime.fst encUnary payload
  let hp := ComputableInPolyTime.snd encUnary payload
  exact hF.comp (hp.fst'.snd'.prod (hH.comp (hn.prod (hp.fst'.fst'.prod hp.snd'))))

/-- Real-game step of [BonehShoup2023], v0.6, §7.3, printed p. 264. The reduction run against
the real PRF implements `hashThenPRF` under independent uniform keys. The input and output
width hypotheses ensure that the PRF's malformed-request check and reply cap preserve valid
answers. Invalid messages receive the empty word in both experiments. -/
theorem eval_prfRealGame_hashThenPRFWordReduction {keyLen inLen outLen : ℕ → ℕ}
    (valid : ℕ → List Bool → Bool) (H : ℕ → List Bool → List Bool → List Bool)
    (F : List Bool → List Bool → List Bool)
    (hH : ∀ n key msg, key.length = keyLen n → valid n msg = true →
      (H n key msg).length = inLen n)
    (hF : ∀ key query, query.length = inLen key.length → (F key query).length = outLen key.length)
    (A : OracleDistinguisher) (n : ℕ) :
    ProbComp.eval (prfRealGame inLen F (hashThenPRFWordReduction keyLen outLen valid H A) n) =
      ProbComp.eval (hashThenPRFWordRealGame keyLen valid H F A n) := by
  simp only [prfRealGame, hashThenPRFWordRealGame, hashThenPRFWordReduction,
    ProbOracleComp.run_bind,
    ProbOracleComp.run_sample, ProbOracleComp.run_simulate, ProbComp.eval_bind,
    BitString.eval_sampleList]
  rw [PMF.bind_comm]
  refine Probability.PMF.bind_congr_on_support _ _ _ fun hashKey hh => ?_
  refine Probability.PMF.bind_congr_on_support _ _ _ fun prfKey hf => ?_
  have hhashKey := BitString.length_of_mem_support_uniformList hh
  have hprfKey := BitString.length_of_mem_support_uniformList hf
  apply congrArg (fun oracle => ProbComp.eval ((A n []).run oracle))
  funext req
  by_cases hv : valid n req.2 = true
  · have hlen := hH n hashKey req.2 hhashKey hv
    have hcap := hF prfKey (H n hashKey req.2) (hprfKey.symm ▸ hlen)
    rw [hprfKey] at hcap
    simp only [hashThenPRFWordHandler, hv, ite_true, ProbOracleComp.run_map,
      ProbOracleComp.run_query, prfOracle, hlen, map_pure, List.take_of_length_le hcap.le,
      hashThenPRF]
  · simp only [hashThenPRFWordHandler, hv, Bool.false_eq_true, ite_false, ProbOracleComp.run_pure]

/-- Game 2 run for [BonehShoup2023], v0.6, §7.3, printed p. 264. Return the adversary's decision
and the final cache of a lazy random function on valid words. Malformed words receive `[]`. -/
@[expose] noncomputable def hashThenPRFWordIdealRun (outLen : ℕ → ℕ)
    (valid : ℕ → List Bool → Bool) (A : OracleDistinguisher) :
    ℕ × List Bool → ProbComp (Bool × List (List Bool × List Bool)) := fun (n, aux) =>
  ((A n aux).runState fun request =>
    cachedRandomFunctionOracle (valid n) (outLen n) request.2).run []

/-- The query-collecting step of Game 2 in [BonehShoup2023], v0.6, §7.3, printed p. 264.
Return the cache keys from the run against a fresh random function on the valid words. -/
@[expose] noncomputable def hashThenPRFWordIdealQueries (outLen : ℕ → ℕ)
    (valid : ℕ → List Bool → Bool) (A : OracleDistinguisher) :
    ℕ × List Bool → ProbComp (List (List Bool)) := fun p =>
  (fun result => result.2.map Prod.fst) <$> hashThenPRFWordIdealRun outLen valid A p

/-- The query collector is uniform strict PPT when the domain test and unary width schedule are
polynomial-time and the adversary is uniform strict oracle PPT. -/
theorem isPPTOn_hashThenPRFWordIdealQueries {outLen : ℕ → ℕ} {valid : ℕ → List Bool → Bool}
    (houtLen : ComputableInPolyTime outLen encUnary encUnary)
    (hvalid : ComputableInPolyTime (fun p => valid p.1 p.2) (encPair encUnary encBits) encBool)
    {A : OracleDistinguisher} (hA : IsOraclePPT encBool A) :
    IsPPTOn (encPair encUnary encBits) (encList encBits)
      (hashThenPRFWordIdealQueries outLen valid A) := by
  let input := encPair encUnary encBits
  let hparam := (ComputableInPolyTime.fst input encBits).fst'
  let hmsg := ComputableInPolyTime.snd input encBits
  have hrun := isPPTOn_runState_cachedSamplerOracle (prepare := id)
    (valid := fun (p : ℕ × List Bool) q => valid p.1 q)
    (sampleReply := fun p => BitString.sampleList (outLen p.1))
    hA.on ComputableInPolyTime.id' (hvalid.comp (hparam.prod hmsg))
    (houtLen.comp (ComputableInPolyTime.fst encUnary encBits)).sampleList
  exact hrun.map (by fun_prop)

/-- A supported output contains no repeated or invalid words. -/
theorem nodup_valid_of_mem_support_hashThenPRFWordIdealQueries {outLen : ℕ → ℕ}
    {valid : ℕ → List Bool → Bool} {A : OracleDistinguisher} {n : ℕ} {aux : List Bool}
    {ms : List (List Bool)}
    (hms : ms ∈ (ProbComp.eval (hashThenPRFWordIdealQueries outLen valid A (n, aux))).support) :
    ms.Nodup ∧ ∀ msg ∈ ms, valid n msg = true := by
  rw [hashThenPRFWordIdealQueries, ProbComp.eval_map, PMF.mem_support_map_iff] at hms
  obtain ⟨⟨result, cache⟩, hrun, rfl⟩ := hms
  rw [hashThenPRFWordIdealRun, ProbOracleComp.eval_runState] at hrun
  let oracle (request : Unit × List Bool) (s : List (List Bool × List Bool)) :=
    ProbComp.eval (cachedRandomFunctionOracle (valid n) (outLen n) request.2 s)
  let invariant (s : List (List Bool × List Bool)) :=
    (s.map Prod.fst).Nodup ∧ ∀ msg ∈ s.map Prod.fst, valid n msg = true
  change (result, cache) ∈ (ProbOracleComp.runWith oracle (A n aux) []).support at hrun
  change invariant cache
  refine ProbOracleComp.runWith_invariant oracle invariant ?_ (A n aux) []
    (by simp [invariant]) result cache hrun
  intro request s hs reply next hnext
  rcases cachedSamplerOracle_cache_of_mem_support (valid := valid n)
      (sampleReply := BitString.sampleList (outLen n)) (query := request.2) (cache := s)
      (result := (reply, next)) hnext with
    hsame | ⟨hv, hfresh, hcons⟩
  · exact (id hsame : next = s) ▸ hs
  · change next = (request.2, reply) :: s at hcons
    dsimp only [invariant] at hs ⊢
    rw [hcons, List.map_cons, List.nodup_cons]
    refine ⟨⟨fun hmem => ?_, hs.1⟩, fun msg hmem => ?_⟩
    · obtain ⟨entry, he, heq⟩ := List.mem_map.mp hmem
      exact (bne_iff_ne.mp (List.lookup_eq_none_iff.mp hfresh entry he)) heq.symm
    · rcases List.mem_cons.mp hmem with rfl | hmem
      · exact hv
      · exact hs.2 msg hmem

/-- A supported list contains at most as many entries as the adversary can query. -/
theorem length_le_of_mem_support_hashThenPRFWordIdealQueries {outLen : ℕ → ℕ}
    {valid : ℕ → List Bool → Bool} {A : OracleDistinguisher} {n Q : ℕ} {aux : List Bool}
    (hQ : (A n aux).IsQueryBounded Q) {ms : List (List Bool)}
    (hms : ms ∈ (ProbComp.eval (hashThenPRFWordIdealQueries outLen valid A (n, aux))).support) :
    ms.length ≤ Q := by
  rw [hashThenPRFWordIdealQueries, ProbComp.eval_map, PMF.mem_support_map_iff] at hms
  obtain ⟨⟨result, cache⟩, hrun, rfl⟩ := hms
  have hbound := ProbOracleComp.measure_runState_le (cost := fun _ => 1) hQ
    (fun request => cachedRandomFunctionOracle (valid n) (outLen n) request.2) List.length
    (fun _ s z hz => by
      rcases cachedSamplerOracle_cache_of_mem_support hz with hsame | ⟨_, _, hcons⟩
      · rw [hsame]
        exact Nat.le_succ _
      · rw [hcons, List.length_cons]) [] (result, cache) hrun
  simpa only [List.length_map, List.length_nil, Nat.zero_add] using hbound

/-! ### The ideal-game comparison -/

private def validWordProgram (valid : List Bool → Bool) (program : WordOracleComp Unit Bool) :
    ProbOracleComp (fun _ : List Bool => List Bool) Bool :=
  ProbOracleComp.simulate (fun req => if valid req.2 then ProbOracleComp.query req.2 else pure [])
    program

private theorem eval_hashThenPRFWordIdealRun (outLen : ℕ → ℕ)
    (valid : ℕ → List Bool → Bool) (A : OracleDistinguisher) (n : ℕ) (aux : List Bool) :
    ProbComp.eval (hashThenPRFWordIdealRun outLen valid A (n, aux)) =
      ProbOracleComp.runWith (memoize fun _ : List Bool => BitString.uniformList (outLen n))
        (validWordProgram (valid n) (A n aux)) [] := by
  rw [hashThenPRFWordIdealRun, ProbOracleComp.eval_runState, validWordProgram,
    ProbOracleComp.runWith_simulate]
  refine congrArg (fun oracle => ProbOracleComp.runWith oracle (A n aux) [])
    (funext fun req => funext fun cache => ?_)
  by_cases h : valid n req.2 = true <;>
    simp [cachedRandomFunctionOracle, cachedSamplerOracle, h, ProbOracleComp.runWith_query,
      ProbComp.eval_memoize, BitString.eval_sampleList, ProbOracleComp.runWith_pure]

private theorem map_fst_runWith_answer_uniformList_eq_eager (inLen outLen : ℕ)
    (program : ProbOracleComp (fun _ : BitString inLen => List Bool) Bool) :
    (ProbOracleComp.runWith (RandomOracle.answer fun _ => BitString.uniformList outLen)
      program (fun _ => none)).map Prod.fst =
      (PMF.uniformOfFintype (BitString inLen → BitString outLen)).bind fun table =>
        ProbComp.eval (program.run fun q => pure (List.ofFn (table q))) := by
  let dist := fun _ : BitString inLen => BitString.uniformList outLen
  have htable := RandomOracle.interpret_prob_eq_memoize_map
    (Function.Embedding.refl (BitString inLen)) List.ofFn
    (fun _ => PMF.uniformOfFintype (BitString outLen)) dist (fun _ => rfl) program
  have hlazy := congrArg (PMF.map Prod.fst)
    (RandomOracle.run_interpret_memoize_prob dist program [])
  simp only [PMF.map_comp, Function.comp_def, RandomOracle.ofList_nil] at hlazy
  rw [← hlazy]
  simpa only [PMF.pi_uniformOfFintype, PMF.monad_bind_eq_bind, Function.Embedding.refl_apply,
    ProbOracleComp.runWith_eq_run_interpret, ProbOracleComp.eval_run, ProbComp.eval_pure]
    using htable.symm

private theorem eval_prfIdealGame_hashThenPRFWordReduction (keyLen inLen outLen : ℕ → ℕ)
    (valid : ℕ → List Bool → Bool) (H : ℕ → List Bool → List Bool → List Bool)
    (hH : ∀ n key msg, key.length = keyLen n → valid n msg = true →
      (H n key msg).length = inLen n)
    (A : OracleDistinguisher) (n : ℕ) :
    ProbComp.eval (prfIdealGame inLen outLen (hashThenPRFWordReduction keyLen outLen valid H A) n) =
      (PMF.uniformOfFintype (BitString (keyLen n))).bind fun key =>
        (ProbOracleComp.runWith (RandomOracle.answer fun _ => BitString.uniformList (outLen n))
          (ProbOracleComp.simulate (fun msg => ProbOracleComp.query
            (BitString.ofList (inLen n) (H n (List.ofFn key) msg)))
            (validWordProgram (valid n) (A n []))) (fun _ => none)).map Prod.fst := by
  have hsample : ProbComp.eval (BitString.sampleList (keyLen n)) =
      (PMF.uniformOfFintype (BitString (keyLen n))).map List.ofFn := BitString.eval_sampleList _
  simp only [prfIdealGame, hashThenPRFWordReduction, ProbOracleComp.run_bind,
    ProbOracleComp.run_sample, ProbOracleComp.run_simulate, ProbComp.eval_bind,
    ProbComp.eval_uniform, hsample, PMF.bind_map, Function.comp_def]
  rw [PMF.bind_comm]
  refine congrArg (PMF.bind _) (funext fun key => ?_)
  rw [map_fst_runWith_answer_uniformList_eq_eager]
  refine congrArg (PMF.bind _) (funext fun table => ?_)
  simp only [validWordProgram, ProbOracleComp.run_simulate]
  refine congrArg (fun oracle => ProbComp.eval ((A n []).run oracle)) (funext fun req => ?_)
  by_cases hv : valid n req.2 = true
  · have hwidth := hH n (List.ofFn key) req.2 List.length_ofFn hv
    simp [hashThenPRFWordHandler, hv, ProbOracleComp.run_map, ProbOracleComp.run_query,
      randomFunctionOracle, hwidth, List.take_of_length_le List.length_ofFn.le]
  · simp [hashThenPRFWordHandler, hv, ProbOracleComp.run_pure]

/-- Interpret the word hash's fixed-width keys and digests for the computational UHF games.
The public setup supplies the key and digest widths. -/
@[expose] def hashThenPRFWordHash (keyLen inLen : ℕ → ℕ)
    (H : ℕ → List Bool → List Bool → List Bool) (n d : ℕ)
    (key : BitString (keyLen d)) (msg : List Bool) : BitString (inLen d) :=
  BitString.ofList (inLen d) (H n (List.ofFn key) msg)

/-- The word-model ideal-game step (7.22) of [BonehShoup2023], v0.6, §7.3, printed p. 264.
The advantage between a random function called on hashed valid words and a random function
called on the valid words themselves is bounded by the certified collector's success in
Attack Game 7.2. Digests have the PRF's input width. Both games reject invalid words and
answer repetitions consistently. -/
theorem advantage_prfIdealGame_hashThenPRFWordReduction_le {keyLen inLen outLen : ℕ → ℕ}
    (valid : ℕ → List Bool → Bool) (H : ℕ → List Bool → List Bool → List Bool)
    (hH : ∀ n key msg, key.length = keyLen n → valid n msg = true →
      (H n key msg).length = inLen n)
    (A : OracleDistinguisher) (n : ℕ) :
    (Game.advantage
      (ProbComp.eval
        (prfIdealGame inLen outLen (hashThenPRFWordReduction keyLen outLen valid H A) n))
      ((ProbComp.eval (hashThenPRFWordIdealRun outLen valid A (n, []))).map Prod.fst) : ℝ≥0∞) ≤
      UHF.multiQueryGame (fun k => pure k) (fun k _ => valid k) (hashThenPRFWordHash keyLen inLen H)
        (fun p => hashThenPRFWordIdealQueries outLen valid A (p.1, [])) n true := by
  let seed := PMF.uniformOfFintype (BitString (keyLen n))
  let law := ProbComp.eval (hashThenPRFWordIdealRun outLen valid A (n, []))
  let digest := hashThenPRFWordHash keyLen inLen H n n
  have hprob : UHF.multiQueryGame (fun k => pure k) (fun k _ => valid k)
        (hashThenPRFWordHash keyLen inLen H)
        (fun p => hashThenPRFWordIdealQueries outLen valid A (p.1, [])) n true =
      ∑' key, seed key * law.toOuterMeasure
        {x | RandomOracle.HasImageCollision (digest key) x.2} := by
    simp only [UHF.multiQueryGame, ProbComp.eval_pure, Game.withSetup_pure, ProbComp.eval_bind,
      ProbComp.eval_uniform, hashThenPRFWordIdealQueries, ProbComp.eval_map, PMF.bind_map,
      Function.comp_def]
    rw [PMF.bind_comm, PMF.bind_apply]
    refine tsum_congr fun key => congrArg (seed key * ·) ?_
    rw [Probability.PMF.bind_pure_decide_apply_true]
    refine law.toOuterMeasure_apply_eq_of_inter_support_eq (Set.ext fun x => ?_)
    change (_ ∧ x ∈ law.support) ↔ (RandomOracle.HasImageCollision (digest key) x.2 ∧ _)
    rw [RandomOracle.hasImageCollision_iff]
    refine and_congr_left fun hx => ?_
    have hkeys : x.2.map Prod.fst ∈
        (ProbComp.eval (hashThenPRFWordIdealQueries outLen valid A (n, []))).support := by
      rw [hashThenPRFWordIdealQueries, ProbComp.eval_map, PMF.mem_support_map_iff]
      exact ⟨x, hx, rfl⟩
    have hv := (nodup_valid_of_mem_support_hashThenPRFWordIdealQueries hkeys).2
    exact ⟨fun ⟨m, hm, m', hm', hne, _, _, heq⟩ => ⟨m, hm, m', hm', hne, heq⟩,
      fun ⟨m, hm, m', hm', hne, heq⟩ => ⟨m, hm, m', hm', hne, hv m hm, hv m' hm', heq⟩⟩
  rw [Game.advantage_comm, ← Game.closeTo_iff_coe_advantage_le, hprob,
    eval_prfIdealGame_hashThenPRFWordReduction keyLen inLen outLen valid H hH]
  change CloseTo (law.map Prod.fst) _ _
  have hconst : law.map Prod.fst = seed.bind fun _ => law.map Prod.fst := (PMF.bind_const _ _).symm
  nth_rw 1 [hconst]
  exact CloseTo.bind_right_tsum seed fun key _ => by
    simpa only [law, eval_hashThenPRFWordIdealRun, digest, hashThenPRFWordHash] using
      RandomOracle.closeTo_runWith_memoize_simulate_query (digest key)
        (BitString.uniformList (outLen n)) (validWordProgram (valid n) (A n []))

/-! ### Concrete and asymptotic security -/

/-- Equation (7.20) of [BonehShoup2023], v0.6, §7.3, printed p. 263, in the product-key word
model. The advantage of the hash-then-PRF test is bounded by the PRF wrapper's advantage plus
the certified collector's multi-query collision success. -/
theorem advantage_hashThenPRFWord_le_add_multiQuery {keyLen inLen outLen : ℕ → ℕ}
    (valid : ℕ → List Bool → Bool) (H : ℕ → List Bool → List Bool → List Bool)
    (F : List Bool → List Bool → List Bool)
    (hH : ∀ n key msg, key.length = keyLen n → valid n msg = true →
      (H n key msg).length = inLen n)
    (hF : ∀ key query, query.length = inLen key.length → (F key query).length = outLen key.length)
    (A : OracleDistinguisher) (n : ℕ) :
    let B := hashThenPRFWordReduction keyLen outLen valid H A
    Game.advantage (ProbComp.eval (hashThenPRFWordRealGame keyLen valid H F A n))
        ((ProbComp.eval (hashThenPRFWordIdealRun outLen valid A (n, []))).map Prod.fst) ≤
      Game.advantage (ProbComp.eval (prfRealGame inLen F B n))
        (ProbComp.eval (prfIdealGame inLen outLen B n)) +
        Game.succProbability (UHF.multiQueryGame (fun k => pure k) (fun k _ => valid k)
          (hashThenPRFWordHash keyLen inLen H)
          (fun p => hashThenPRFWordIdealQueries outLen valid A (p.1, [])) n) := by
  intro B
  have hcollision := advantage_prfIdealGame_hashThenPRFWordReduction_le
    (outLen := outLen) valid H hH A n
  rw [← Game.coe_succProbability_ennreal] at hcollision
  rw [← eval_prfRealGame_hashThenPRFWordReduction valid H F hH hF A n]
  exact (Game.advantage_triangle _ (ProbComp.eval (prfIdealGame inLen outLen B n)) _).trans
    (add_le_add le_rfl (ENNReal.coe_le_coe.mp hcollision))

/-- Equation (7.19) of [BonehShoup2023], v0.6, §7.3, printed p. 262, in the product-key word
model. The single-pair wrapper uses the strict fair-bit sampler of Lemma 7.1. -/
theorem advantage_hashThenPRFWord_le_add_collision {keyLen inLen outLen : ℕ → ℕ}
    (valid : ℕ → List Bool → Bool) (H : ℕ → List Bool → List Bool → List Bool)
    (F : List Bool → List Bool → List Bool)
    (hH : ∀ n key msg, key.length = keyLen n → valid n msg = true →
      (H n key msg).length = inLen n)
    (hF : ∀ key query, query.length = inLen key.length → (F key query).length = outLen key.length)
    (A : OracleDistinguisher) (n Q : ℕ) (hQ : (A n []).IsQueryBounded Q) :
    let B := hashThenPRFWordReduction keyLen outLen valid H A
    Game.advantage (ProbComp.eval (hashThenPRFWordRealGame keyLen valid H F A n))
        ((ProbComp.eval (hashThenPRFWordIdealRun outLen valid A (n, []))).map Prod.fst) ≤
      Game.advantage (ProbComp.eval (prfRealGame inLen F B n))
        (ProbComp.eval (prfIdealGame inLen outLen B n)) +
        ((Q : ℝ≥0) ^ 2 / 2) * Game.succProbability
          (UHF.collisionGame (fun k => pure k) (fun k _ => valid k)
            (hashThenPRFWordHash keyLen inLen H) (fun p => UHF.collisionPairReduction []
              (hashThenPRFWordIdealQueries outLen valid A (p.1, []))) n) := by
  intro B
  refine (advantage_hashThenPRFWord_le_add_multiQuery valid H F hH hF A n).trans ?_
  refine add_le_add le_rfl (UHF.succProbability_multiQueryGame_le_collisionPairReduction
    (fun k => pure k) (fun k _ => valid k) (hashThenPRFWordHash keyLen inLen H) []
    (fun p => hashThenPRFWordIdealQueries outLen valid A (p.1, [])) n
    fun _ _ _ hms => length_le_of_mem_support_hashThenPRFWordIdealQueries hQ hms)

/-- Theorem 7.7 of [BonehShoup2023], v0.6, §7.3, printed pp. 262–265, for product keys and
uniform strict oracle-PPT tests. The components provide efficient hash evaluation, domain
recognition, unary key and digest width schedules, computational UHF security, and PRF
security. The real game uses the composed evaluator with fresh independent keys. Its ideal
game uses one lazy random function on the same valid words. Invalid queries receive `[]`
in both games and repeated queries are allowed. The composition's evaluator is certified by
`computableInPolyTime_hashThenPRFWord`. -/
theorem hashThenPRFWord_indistinguishable {keyLen inLen outLen : ℕ → ℕ}
    {valid : ℕ → List Bool → Bool} {H : ℕ → List Bool → List Bool → List Bool}
    {F : List Bool → List Bool → List Bool}
    (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary)
    (hinLen : ComputableInPolyTime inLen encUnary encUnary)
    (hvalid : ComputableInPolyTime (fun p => valid p.1 p.2) (encPair encUnary encBits) encBool)
    (hH : ComputableInPolyTime (fun p => H p.1 p.2.1 p.2.2)
      (encKeyedInput encBits) encBits)
    (hwidth : ∀ n key msg, key.length = keyLen n → valid n msg = true →
      (H n key msg).length = inLen n)
    (hUHF : UHF.IsComputationalUHF encUnary encBits (fun k => pure k) (fun k _ => valid k)
      (hashThenPRFWordHash keyLen inLen H))
    (hPRF : PseudorandomFunctionOver inLen outLen F) :
    Game.Indistinguishable
      (fun A n => ProbComp.eval (hashThenPRFWordRealGame keyLen valid H F A n))
      (fun A n => (ProbComp.eval (hashThenPRFWordIdealRun outLen valid A (n, []))).map Prod.fst)
      (IsOraclePPT encBool) := by
  intro A hA
  have houtLen := hPRF.outLen_polyTime hinLen
  let B := hashThenPRFWordReduction keyLen outLen valid H A
  have hB : IsOraclePPT encBool B :=
    isOraclePPT_hashThenPRFWordReduction hkeyLen houtLen hvalid hH hA
  let C (p : ℕ × ℕ) := hashThenPRFWordIdealQueries outLen valid A (p.1, [])
  have hC : IsPPTOn (encPair encUnary encUnary) (encList encBits) C :=
    (isPPTOn_hashThenPRFWordIdealQueries houtLen hvalid hA).preprocess
      ((ComputableInPolyTime.fst _ _).prod (ComputableInPolyTime.const []))
  have hsetup : IsPPTOn encUnary encUnary (fun n => pure n) := ComputableInPolyTime.id'.isPPTOn
  have hcollision := (hUHF.isMultiQueryUHF hsetup).negligible_succProbability C hC
  exact negligible_of_le ((hPRF.secure B hB).add hcollision)
    (fun n => advantage_hashThenPRFWord_le_add_multiQuery valid H F hwidth hPRF.length_eq A n)

end Cslib.Crypto.PRF
