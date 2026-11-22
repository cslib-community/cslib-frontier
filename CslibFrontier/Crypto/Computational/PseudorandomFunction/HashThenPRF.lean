/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.PseudorandomFunction
public import CslibFrontier.Crypto.Primitives.PRF.HashThenPRF
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.Oracle.Substitution
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Languages.Probabilistic.Oracle.Substitution.QueryCount
import CslibFrontier.Probability.PMF.Bind

/-!
# Word PRF reduction for hash-then-PRF

The reduction samples a private hash key and forwards the digest of each valid word to its
PRF challenger. Malformed words receive an empty reply without a call. A reply is read only
up to the declared output width, even if the challenger returns a longer word.

This is the real-game step of [BonehShoup2023], v0.6, §7.3, printed p. 264, toward (7.21).
The real law uses two independent uniform keys and the composition `PRF.hashThenPRF` from
(7.18). The hash is given on words with a polynomial-time domain test. Repeated queries are
allowed. The ideal collision comparison and the security conclusion of Theorem 7.7 are tracked
in [#5790](https://github.com/cslib-community/cslib-frontier/issues/5790).

## Main definitions

* `Cslib.Crypto.PRF.hashThenPRFWordReduction`: the explicit word-oracle adversary `B_F`.

## Main results

* `Cslib.Crypto.PRF.isOraclePPT_hashThenPRFWordReduction`: uniform strict oracle PPT.
* `Cslib.Crypto.PRF.isQueryBounded_hashThenPRFWordReduction`: at most one call per input query.
* `Cslib.Crypto.PRF.eval_prfRealGame_hashThenPRFWordReduction`: its real PRF run has the law
  of Game 0 of the proof of Theorem 7.7.
-/

public section

namespace Cslib.Crypto.PRF

open Probability Turing.MultiTapeTM

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
      (encPair encUnary (encPair encBits encBits)) encBits)
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
        · have : reply = [] := by
            simpa only [OracleComp.support, OracleComp.supportWith_pure, Set.mem_singleton_iff]
              using hreply
          subst reply
          exact Nat.zero_le _)
  have hsample := (hkeyLen.comp (ComputableInPolyTime.fst encUnary encBits)).sampleList
  exact (hsample.isOraclePPTOn.bind_with hrun).isOraclePPT

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
      ProbComp.eval (do
        let hashKey ← BitString.sampleList (keyLen n)
        let prfKey ← BitString.sampleList n
        (A n []).run fun req => pure (if valid n req.2 then
          hashThenPRF (H n) F (hashKey, prfKey) req.2 else [])) := by
  simp only [prfRealGame, hashThenPRFWordReduction, ProbOracleComp.run_bind,
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

end Cslib.Crypto.PRF
