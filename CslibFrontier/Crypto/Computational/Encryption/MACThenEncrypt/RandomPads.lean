/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.MACThenEncrypt
public import CslibFrontier.Crypto.Computational.Encryption.EncryptThenMAC
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Crypto.Computational.PseudorandomFunction.RandomOracle
import CslibFrontier.Languages.Probabilistic.RandomOracle.Programming
import CslibFrontier.Languages.Probabilistic.Oracle.Substitution.RunWith
import CslibFrontier.Languages.Probabilistic.Oracle.Substitution.QueryCount
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair.Projections
import CslibFrontier.Languages.Probabilistic.Oracle.Norm
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.PPT

/-!
# MAC-then-encrypt over the one-block PRF cipher: random pads

This module is a step of the proof of Theorem 9.3 of [BonehShoup2023] (§9.4.4, printed
pp. 373–377); it does not prove Theorem 9.3. That result says that MAC-then-encrypt over randomized
counter mode "provides authenticated encryption assuming `I` is a secure one-time MAC and `F` is a
secure PRF where `1/|X|` is negligible". Its proof starts by replacing "the pseudo-random pads in
the counter-mode cipher by truly independent one-time pads" (Game 1) and bounds the change by
(9.13): `|Pr[W₁] − Pr[W₀]| ≤ PRFadv[B_prf, F] + Q² / (2 |X|)`.

It proves that step, in the direction the proof uses, for `macThenEncrypt` over the cipher
`prfCipher`, which encrypts one PRF block under a fresh IV, and for messages of exactly `n` bits:
`eval_ciGame_macThenEncrypt_prfCipher_le_freshPads` bounds the winning probability of a
ciphertext-integrity adversary with at most `Q n` encryption queries by the PRF advantage of
`mteCIToPrfDistinguisher`, plus `(Q n).choose 2 / 2 ^ ptLen n`, plus its winning probability in
Game 1. The distinguisher has the certificate `isOraclePPT_mteCIToPrfDistinguisher`.

No security statement follows from this module alone: the bound still contains the winning
probability in Game 1, which the later steps (9.14)–(9.17) of the proof bound by one-time MAC
advantages, and those steps are not formalized here (#640). Counter mode over several blocks and
messages of varying length are not covered either (#640).

The proof has the two halves the source describes after (9.13). The PRF half identifies the real
and ideal PRF games of `mteCIToPrfDistinguisher` with the ciphertext-integrity game and with the
same game over a lazily sampled random function. The "forgetful gnome" half is an instance of
`RandomOracle.closeTo_runWith_lazyProgramHandler_overwriteProgramHandler_choose_two`.

## Main definitions

* `mtePlaintextValid`: the check `macThenEncrypt` applies to a decrypted plaintext.
* `mteCIToPrfDistinguisher`: the PRF distinguisher `B_prf`.
* `MteRec`, `MteRec.ct`, `MteState`: query record, its induced ciphertext, and the state of Game 1.
* `mteForgetfulOracle` and `mteIdealFinal`: the encryption oracle and the winning condition of
  Game 1, on the state `MteState` of query records `MteRec`.

## Main results

* `eval_ciGame_macThenEncrypt_prfCipher_le_freshPads`: step (9.13), from the ciphertext-integrity
  game to Game 1 (#640).
* `isOraclePPT_mteCIToPrfDistinguisher`: `B_prf` is `IsOraclePPT` when the adversary is.

## References

* [D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023]
-/

public section

namespace Cslib.Crypto

open Cslib.Probability ProbComp OracleComp BitString Turing.MultiTapeTM
open scoped NNReal ENNReal

/-! ## The plaintext check of `macThenEncrypt` -/

/-- The check `macThenEncrypt` applies to a decrypted plaintext `p`, as a Boolean: `p` is the
canonical encoding of a pair, its message has `M.msgLen n` bits, and its tag verifies under `km`. -/
@[expose] def mtePlaintextValid (M : MACScheme) (n : ℕ) (km p : List Bool) : Bool :=
  (encPair encBits encBits (unframe p, dropFrame p) == p) &&
    ((unframe p).length == M.msgLen n) && M.verify km (unframe p) (dropFrame p)

/-! ## The PRF distinguisher -/

/-- The encryption handler of `mteCIToPrfDistinguisher`: tag with `km`, draw the IV `r`, ask the
PRF oracle for the pad, and log the ciphertext. -/
private noncomputable def mteCIToPrfHandler (M : MACScheme) (n m : ℕ) (km : List Bool)
    (request : Unit × List Bool) : StateT (List (List Bool)) (WordOracleComp Unit) (List Bool) :=
  fun log =>
    if request.2.length == n then do
      let tag ← ProbOracleComp.sample (M.sign km request.2)
      let r ← ProbOracleComp.sample (BitString.sampleList m)
      let pad ← List.take m <$> ProbOracleComp.query ((), r)
      let ct := r ++ List.zipWith xor pad (encPair encBits encBits (request.2, tag))
      pure (ct, ct :: log)
    else
      pure ([], log)

/-- The PRF distinguisher `B_prf` of step (9.13) of the proof of [BonehShoup2023], Theorem 9.3, for
one PRF block and messages of exactly `n` bits. At PRF parameter `m` it recovers `n` with
`ptLen n = m` (and outputs `false` when there is none), draws a MAC key, and runs the
ciphertext-integrity adversary: an `n`-bit message is tagged and encrypted with a fresh `m`-bit IV
under the pad the PRF oracle returns for that IV. It outputs whether the adversary's ciphertext is
new, has `2 * m` bits, and decrypts, with one more oracle call, to a plaintext that passes
`mtePlaintextValid`. -/
noncomputable def mteCIToPrfDistinguisher (M : MACScheme) (ptLen : ℕ → ℕ)
    (adversary : CIAdversary) : OracleDistinguisher :=
  fun m _ =>
    let n := GeneratorReindex.parameter ptLen m
    if ptLen n == m then do
      let km ← ProbOracleComp.sample (M.keyGen n)
      let out ← (OracleComp.interpret
        (OracleComp.sumHandler
          (fun u => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin u)))
          (mteCIToPrfHandler M n m km)) (adversary n [])).run []
      if !out.2.contains out.1 && out.1.length == 2 * m then do
        let pad ← List.take m <$> ProbOracleComp.query ((), out.1.take m)
        pure (mtePlaintextValid M n km (List.zipWith xor pad (out.1.drop m)))
      else
        pure false
    else
      pure false

/-! ## The ideal games -/

/-- A record of one answered encryption query in the ideal games of step (9.13). -/
structure MteRec where
  /-- The initialization vector drawn for the query. -/
  iv : List Bool
  /-- The pad masking the framed `(msg, tag)` pair. -/
  pad : List Bool
  /-- The queried `n`-bit plaintext message. -/
  msg : List Bool
  /-- The MAC tag sampled for `msg`. -/
  tag : List Bool

/-- The ciphertext a record stands for: its IV, then its pair `(msg, tag)` under the first `m`
bits of its pad. -/
@[expose] def MteRec.ct (m : ℕ) (e : MteRec) : List Bool :=
  e.iv ++ List.zipWith xor (e.pad.take m) (encPair encBits encBits (e.msg, e.tag))

/-- State of the ideal games of step (9.13): the cache of `(IV, pad)` pairs and the history of
answered queries, both newest first. -/
structure MteState where
  /-- Lazily sampled or programmed `(IV, pad)` pairs, newest first. -/
  cache : List (List Bool × List Bool) := []
  /-- Answered encryption queries, newest first. -/
  history : List MteRec := []

/-- The encryption oracle of the CI game of `macThenEncrypt` over `prfCipher` with a lazily
sampled random function in place of the PRF: an `n`-bit message is tagged, a fresh `m`-bit IV is
drawn, its pad is looked up in the cache or drawn, and the query is logged. -/
private noncomputable def mteFaithfulOracle (M : MACScheme) (n m : ℕ) (km : List Bool)
    (request : Unit × List Bool) : StateT MteState PMF (List Bool) :=
  fun st =>
    if request.2.length == n then
      (ProbComp.eval (M.sign km request.2)).bind fun tag =>
        (BitString.uniformList m).bind fun r =>
          (memoize (fun _ => BitString.uniformList m) r st.cache).map fun res =>
            (r ++ List.zipWith xor (res.1.take m) (encPair encBits encBits (request.2, tag)),
              ⟨res.2, ⟨r, res.1, request.2, tag⟩ :: st.history⟩)
    else
      PMF.pure ([], st)

/-- The encryption oracle of Game 1 of the proof of [BonehShoup2023], Theorem 9.3 (p. 375), for one
PRF block and messages of exactly `n` bits; a device of that proof (#640), with no security
statement of its own. An `n`-bit message is tagged, a fresh `m`-bit IV and a fresh pad are drawn
whether or not the IV was used before, the reply is `IV ++ (pad ⊕ (msg ‖ tag))`, the pair
`(IV, pad)` is put in front of the cache, and IV, pad, message and tag are logged. Other queries
get `[]`. -/
@[expose] noncomputable def mteForgetfulOracle (M : MACScheme) (n m : ℕ) (km : List Bool)
    (request : Unit × List Bool) : StateT MteState PMF (List Bool) :=
  fun st =>
    if request.2.length == n then
      (ProbComp.eval (M.sign km request.2)).bind fun tag =>
        (BitString.uniformList m).bind fun r =>
          (BitString.uniformList m).map fun pad =>
            (r ++ List.zipWith xor (pad.take m) (encPair encBits encBits (request.2, tag)),
              ⟨(r, pad) :: st.cache, ⟨r, pad, request.2, tag⟩ :: st.history⟩)
    else
      PMF.pure ([], st)

/-- The winning condition of Game 1 of the proof of [BonehShoup2023], Theorem 9.3 (p. 375), for one
PRF block and messages of exactly `n` bits; a device of that proof (#640), with no security
statement of its own. The final ciphertext is new and has `2 * m` bits, and its plaintext passes
`mtePlaintextValid` under the pad of its IV: the first pad the cache holds for that IV, which is
that of the most recent query with it, or a fresh pad when there is none. The source takes the
earliest such query, "for specificity". -/
@[expose] noncomputable def mteIdealFinal (M : MACScheme) (n m : ℕ) (km : List Bool)
    (out : List Bool × MteState) : PMF Bool :=
  if !(out.2.history.map (MteRec.ct m)).contains out.1 && out.1.length == 2 * m then
    (memoize (fun _ => BitString.uniformList m) (out.1.take m) out.2.cache).map fun res =>
      mtePlaintextValid M n km (List.zipWith xor (res.1.take m) (out.1.drop m))
  else
    PMF.pure false

/-! ## The random-function step -/

/-- The coins of one encryption query: the tag of the message, then the IV. -/
private noncomputable def mteCoins (M : MACScheme) (m : ℕ) (km : List Bool)
    (request : Unit × List Bool) : PMF (List Bool × List Bool) :=
  (ProbComp.eval (M.sign km request.2)).bind fun tag =>
    (BitString.uniformList m).map fun r => (tag, r)

/-- The reply to one encryption query and the history entry it adds, from its coins and pad. -/
private def mteFinish (m : ℕ) (request : Unit × List Bool) (coins : List Bool × List Bool)
    (pad : List Bool) (history : List MteRec) : List Bool × List MteRec :=
  (coins.2 ++ List.zipWith xor (pad.take m) (encPair encBits encBits (request.2, coins.1)),
    ⟨coins.2, pad, request.2, coins.1⟩ :: history)

/-- The lazily sampled game represents the programming channel of
`RandomOracle.lazyProgramHandler`. -/
private theorem mteFaithfulOracle_step_lazyProgramHandler (M : MACScheme) (n m : ℕ)
    (km : List Bool) (request : Unit × List Bool)
    (s : List (List Bool × List Bool) × List MteRec) :
    (RandomOracle.lazyProgramHandler (Reply := fun _ : Unit × List Bool => List Bool)
      (Coins := fun _ : Unit × List Bool => List Bool × List Bool) (BitString.uniformList m)
      (fun req => req.2.length == n) (fun _ _ history => PMF.pure ([], history))
      (mteCoins M m km) (fun _ coins => coins.2) (mteFinish m) (.inl request) s).map
        (fun (a, s') => (a, (⟨s'.1, s'.2⟩ : MteState))) =
      mteFaithfulOracle M n m km request ⟨s.1, s.2⟩ := by
  rcases s with ⟨cache, history⟩
  cases hlen : request.2.length == n <;>
    simp [mteFaithfulOracle, RandomOracle.lazyProgramHandler, hlen, mteCoins, mteFinish,
      Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure, PMF.bind_bind,
      PMF.map, Function.comp_def]

/-- Game 1 represents the programming channel of `RandomOracle.overwriteProgramHandler`. -/
private theorem mteForgetfulOracle_step_overwriteProgramHandler (M : MACScheme) (n m : ℕ)
    (km : List Bool) (request : Unit × List Bool)
    (s : List (List Bool × List Bool) × List MteRec) :
    (RandomOracle.overwriteProgramHandler (Reply := fun _ : Unit × List Bool => List Bool)
      (Coins := fun _ : Unit × List Bool => List Bool × List Bool) (BitString.uniformList m)
      (fun req => req.2.length == n) (fun _ _ history => PMF.pure ([], history))
      (mteCoins M m km) (fun _ coins => coins.2) (mteFinish m) (.inl request) s).map
        (fun (a, s') => (a, (⟨s'.1, s'.2⟩ : MteState))) =
      mteForgetfulOracle M n m km request ⟨s.1, s.2⟩ := by
  rcases s with ⟨cache, history⟩
  cases hlen : request.2.length == n <;>
    simp [mteForgetfulOracle, RandomOracle.overwriteProgramHandler, hlen, mteCoins, mteFinish,
      Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure, PMF.bind_bind,
      PMF.map, Function.comp_def]

/-- Replacing the lazily sampled random function by a fresh pad for every query raises the
probability that a final check accepts by at most `Q.choose 2 / 2 ^ m`: an instance of
`RandomOracle.closeTo_runWith_lazyProgramHandler_overwriteProgramHandler_choose_two`, with the
one-oracle program moved to that theorem's two channels by a query on the programming channel. -/
private theorem mteFaithful_bind_apply_le (M : MACScheme) (n m : ℕ) (km : List Bool)
    {program : WordOracleComp Unit (List Bool)} {Q : ℕ} (hq : program.IsQueryBounded Q)
    (next : List Bool × MteState → PMF Bool) :
    ((ProbOracleComp.runWith (mteFaithfulOracle M n m km) program {}).bind next) true ≤
      ((ProbOracleComp.runWith (mteForgetfulOracle M n m km) program {}).bind next)
          true + (Q.choose 2 : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ m) := by
  let embed : (q : Unit × List Bool) →
      ProbOracleComp (OracleSpec.sum (fun _ : Unit × List Bool => List Bool)
        (fun _ : List Bool => List Bool)) (List Bool) :=
    fun q => ProbOracleComp.query (spec := OracleSpec.sum (fun _ : Unit × List Bool => List Bool)
      (fun _ : List Bool => List Bool)) (.inl q)
  have hmin : ∀ req : Unit × List Bool, (req.2.length == n) = true → ∀ r,
      ((mteCoins M m km req).map fun coins => coins.2) r ≤ (1 : ℝ≥0∞) / 2 ^ m := fun req _ r => by
    simp only [mteCoins, PMF.map_bind, PMF.map_comp, Function.comp_def, PMF.map_id', PMF.bind_const]
    exact BitString.uniformList_apply_le m r
  have hqS : IsCostBounded (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (fun _ => 0)))
      (ProbOracleComp.simulate embed program) Q :=
    ProbOracleComp.isCostBounded_simulate (cost := fun _ => 1)
      (cost' := Sum.elim (fun _ => 1) (fun _ => 0)) (handler := embed)
      (fun q => ProbOracleComp.isCostBounded_query _ (Sum.inl q)) hq
  have hqH : IsCostBounded (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) (fun _ => 1)))
      (ProbOracleComp.simulate embed program) 0 :=
    ProbOracleComp.isCostBounded_simulate (cost := fun _ => 0)
      (cost' := Sum.elim (fun _ => 0) (fun _ => 1)) (handler := embed)
      (fun q => ProbOracleComp.isCostBounded_query _ (Sum.inl q))
      (IsCostBounded.of_forall_cost_eq_zero (fun q => by cases q <;> rfl) program)
  have hclose := RandomOracle.closeTo_runWith_lazyProgramHandler_overwriteProgramHandler_choose_two
    (Reply := fun _ : Unit × List Bool => List Bool)
    (Coins := fun _ : Unit × List Bool => List Bool × List Bool) (BitString.uniformList m)
    (fun req => req.2.length == n) (fun _ _ history => PMF.pure ([], history))
    (mteCoins M m km) (fun _ coins => coins.2) (mteFinish m) hmin hqS hqH [] []
  have hrun (oracle : (q : (Unit × List Bool) ⊕ List Bool) →
      StateT (List (List Bool × List Bool) × List MteRec) PMF
      ((OracleSpec.sum (fun _ : Unit × List Bool => List Bool) (fun _ : List Bool => List Bool))
        q)) :
      ProbOracleComp.runWith oracle (ProbOracleComp.simulate embed program) ([], []) =
        ProbOracleComp.runWith (fun q => oracle (.inl q)) program ([], []) := by
    rw [ProbOracleComp.runWith_simulate]
    exact congrArg (fun handler => ProbOracleComp.runWith handler program ([], []))
      (funext fun q => funext fun s => ProbOracleComp.runWith_query oracle (Sum.inl q) s)
  rw [hrun, hrun] at hclose
  have hcloseState := hclose.map (fun (a, s') => (a, (⟨s'.1, s'.2⟩ : MteState)))
  rw [ProbOracleComp.runWith_map_state _ _ (fun s => (⟨s.1, s.2⟩ : MteState))
      (mteFaithfulOracle_step_lazyProgramHandler M n m km) program ([], []),
    ProbOracleComp.runWith_map_state _ _ (fun s => (⟨s.1, s.2⟩ : MteState))
      (mteForgetfulOracle_step_overwriteProgramHandler M n m km) program ([], [])] at hcloseState
  have h := (hcloseState.bind_left next) {true}
  rw [PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_apply_singleton] at h
  simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add] using h

/-! ## The PRF step -/

/-- The real PRF game of `mteCIToPrfDistinguisher` is the ciphertext-integrity game of
`macThenEncrypt` over `prfCipher`. -/
private theorem eval_prfRealGame_mteCIToPrfDistinguisher
    (family : List Bool → List Bool → List Bool)
    (hpoly : ComputableInPolyTime (fun pair => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    (M : MACScheme) (ptLen : ℕ → ℕ) (hptLenPoly : ComputableInPolyTime ptLen encUnary encUnary)
    (hmono : StrictMono ptLen) (hmsgLen : ∀ n, M.msgLen n = n)
    (hpairLen : ∀ n km, km ∈ (ProbComp.eval (M.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ tag ∈ (ProbComp.eval (M.sign km msg)).support,
        (encPair encBits encBits (msg, tag)).length = ptLen n)
    (adversary : CIAdversary) (n : ℕ) :
    ProbComp.eval (prfRealGame id family (mteCIToPrfDistinguisher M ptLen adversary) (ptLen n)) =
      ProbComp.eval ((macThenEncrypt (prfCipher family hpoly hlen) M ptLen hptLenPoly hmsgLen
        hpairLen).ciGame adversary n) := by
  have hparam := GeneratorReindex.parameter_apply_of_strictMono hmono n
  have hkeyGen : ProbComp.eval
      ((macThenEncrypt (prfCipher family hpoly hlen) M ptLen hptLenPoly hmsgLen
        hpairLen).keyGen n) =
      (BitString.uniformList (ptLen n)).bind (fun ke =>
        (ProbComp.eval (M.keyGen n)).bind (fun km =>
          PMF.pure (encPair encBits encBits (ke, km)))) := by
    simp only [macThenEncrypt, prfCipher, ProbComp.eval_bind, ProbComp.eval_pure,
      BitString.eval_sampleList]
  simp only [prfRealGame, id_eq, ProbOracleComp.run, SymmetricCipher.ciGame,
    mteCIToPrfDistinguisher, hparam, beq_self_eq_true, ↓reduceIte, hkeyGen, runWith_norm, pmf_norm]
  rw [BitString.eval_sampleList]
  refine PMF.bind_congr_on_support _ _ _ fun ke hke => ?_
  have hkeLen : ke.length = ptLen n := BitString.length_of_mem_support_uniformList hke
  refine PMF.bind_congr_on_support _ _ _ fun km hkm => ?_
  have horacle :
      (fun (q : Unit × List Bool) (state : List (List Bool)) =>
        evalWith (sumHandler unifOracle fun q : Unit × List Bool =>
            PMF.pure (prfOracle family (ptLen n) ke q.2))
          ((mteCIToPrfHandler M n (ptLen n) km q).run state)) =
      (fun q state => ProbComp.eval
        ((macThenEncrypt (prfCipher family hpoly hlen) M ptLen hptLenPoly hmsgLen
          hpairLen).ciEncryptionOracle n (encPair encBits encBits (ke, km)) q state)) := by
    funext ⟨⟨⟩, msg⟩ log
    unfold mteCIToPrfHandler SymmetricCipher.ciEncryptionOracle
    dsimp only [macThenEncrypt, prfCipher, StateT.run]
    by_cases hmsg : (msg.length == n) = true
    · simp only [hmsg, ↓reduceIte, runWith_norm, pmf_norm, BitString.eval_sampleList,
        unframe_encPair_encBits, dropFrame_encPair_encBits]
      refine PMF.bind_congr_on_support _ _ _ fun tag htag => ?_
      refine PMF.bind_congr_on_support _ _ _ fun r hr => ?_
      have hrLen : r.length = ptLen n := BitString.length_of_mem_support_uniformList hr
      have hpadLen : (family ke r).length = ptLen n := by
        rw [hlen ke r (by rw [hrLen, hkeLen]), hkeLen]
      simp [prfOracle, hrLen, List.take_of_length_le hpadLen.le]
    · simp [hmsg, runWith_norm, pmf_norm]
  rw [horacle]
  refine PMF.bind_congr_on_support _ _ _ fun out _ => ?_
  dsimp only [macThenEncrypt, prfCipher]
  rw [unframe_encPair_encBits, dropFrame_encPair_encBits]
  by_cases hcond : (!out.2.contains out.1 && out.1.length == 2 * ptLen n) = true
  · obtain ⟨hfresh, hlenCt⟩ := Bool.and_eq_true_iff.mp hcond
    have htakeLen : (out.1.take (ptLen n)).length = ptLen n := by
      rw [List.length_take, beq_iff_eq.mp hlenCt]; omega
    have hpadLen : (family ke (out.1.take (ptLen n))).length = ptLen n := by
      rw [hlen _ _ (by rw [htakeLen, hkeLen]), hkeLen]
    simp only [runWith_norm, pmf_norm, prfOracle, htakeLen, ↓reduceIte,
      List.take_of_length_le hpadLen.le, hfresh, hlenCt, Bool.true_and, Option.elim,
      mtePlaintextValid, hmsgLen]
    congr 1
    split_ifs with h
    · exact h
    · exact (Bool.not_eq_true _).mp h
  · simp only [hcond, Bool.false_eq_true, ↓reduceIte, runWith_norm, pmf_norm]
    rcases Bool.and_eq_false_iff.mp (Bool.eq_false_iff.mpr hcond) with hfresh | hlenCt
    · simp only [hfresh, Bool.false_and]
    · simp [hlenCt, Option.elim]

/-- The ideal PRF game of `mteCIToPrfDistinguisher` is the ciphertext-integrity game over a lazily
sampled random function. -/
private theorem eval_prfIdealGame_mteCIToPrfDistinguisher (M : MACScheme) (ptLen : ℕ → ℕ)
    (hmono : StrictMono ptLen) (adversary : CIAdversary) (n : ℕ) :
    ProbComp.eval (prfIdealGame id id (mteCIToPrfDistinguisher M ptLen adversary) (ptLen n)) =
      (ProbComp.eval (M.keyGen n)).bind fun km =>
        (ProbOracleComp.runWith (mteFaithfulOracle M n (ptLen n) km) (adversary n [])
          {}).bind (mteIdealFinal M n (ptLen n) km) := by
  have hparam := GeneratorReindex.parameter_apply_of_strictMono hmono n
  rw [prfIdealGame_eq_cached]
  simp only [mteCIToPrfDistinguisher, hparam, beq_self_eq_true, ↓reduceIte, runWith_norm, pmf_norm]
  refine PMF.bind_congr_on_support _ _ _ fun km _ => ?_
  have hsim := ProbOracleComp.runWith_map_state
    (oracle := mteFaithfulOracle M n (ptLen n) km)
    (oracle' := fun (q : Unit × List Bool)
        (state : List (List Bool) × List (List Bool × List Bool)) =>
      PMF.map (fun x => (x.1.1, x.1.2, x.2))
        (ProbOracleComp.runWith
          (fun (q : Unit × List Bool) state =>
            ProbComp.eval (cachedRandomFunctionOracle (·.length == ptLen n) (ptLen n) q.2 state))
          ((mteCIToPrfHandler M n (ptLen n) km q).run state.1) state.2))
    (represent := fun st : MteState => (st.history.map (MteRec.ct (ptLen n)), st.cache))
    (step := by
      rintro ⟨⟨⟩, msg⟩ ⟨cache, hist⟩
      unfold mteFaithfulOracle mteCIToPrfHandler
      dsimp only [StateT.run]
      by_cases hmsg : (msg.length == n) = true
      · simp only [hmsg, ↓reduceIte, runWith_norm, pmf_norm, BitString.eval_sampleList]
        refine PMF.bind_congr_on_support _ _ _ fun tag _ => ?_
        refine PMF.bind_congr_on_support _ _ _ fun r hr => ?_
        have hrLen : r.length = ptLen n := BitString.length_of_mem_support_uniformList hr
        simp only [cachedRandomFunctionOracle, cachedSamplerOracle, hrLen, beq_self_eq_true,
          ↓reduceIte, ProbComp.eval_memoize, BitString.eval_sampleList]
        rfl
      · simp [hmsg, runWith_norm, pmf_norm])
    (adversary n []) {}
  rw [show (([] : List (List Bool)), ([] : List (List Bool × List Bool))) =
      (fun st : MteState => (st.history.map (MteRec.ct (ptLen n)), st.cache)) {} from rfl,
    ← hsim, PMF.bind_map]
  refine PMF.bind_congr_on_support _ _ _ fun out _ => ?_
  obtain ⟨ct, cache, hist⟩ := out
  unfold mteIdealFinal
  dsimp only [Function.comp_apply]
  by_cases hcond :
      (!(hist.map (MteRec.ct (ptLen n))).contains ct && ct.length == 2 * ptLen n) = true
  · have hlenCt : ct.length = 2 * ptLen n := beq_iff_eq.mp (Bool.and_eq_true_iff.mp hcond).2
    have htakeLen : (ct.take (ptLen n)).length = ptLen n := by
      rw [List.length_take, hlenCt]; omega
    simp only [hcond, ↓reduceIte, runWith_norm, pmf_norm, cachedRandomFunctionOracle,
      cachedSamplerOracle, htakeLen, beq_self_eq_true, ProbComp.eval_memoize,
      BitString.eval_sampleList]
    rfl
  · simp only [hcond, Bool.false_eq_true, ↓reduceIte, runWith_norm, pmf_norm]

/-- A step of the proof of [BonehShoup2023], Theorem 9.3 (§9.4.4, bound (9.13), p. 375), not the
theorem itself (#640), for `macThenEncrypt` over the one-block cipher `prfCipher`, messages of
exactly `n` bits and a polynomial schedule `ptLen`, stated in the direction the proof uses (the
source bounds the absolute difference). For a CI adversary with at most `Q n` encryption queries,
its winning probability is at most the PRF advantage of `mteCIToPrfDistinguisher`, plus
`(Q n).choose 2 / 2 ^ ptLen n` for a repeated IV (the source prints `Q ^ 2 / (2 |X|)`), plus the
winning probability in Game 1, the ideal game with a fresh pad for every query
(`mteForgetfulOracle`, `mteIdealFinal`), whose remaining steps (9.14)–(9.17) and multi-block /
variable-length extensions are open (#640). `StrictMono ptLen` is what `mteCIToPrfDistinguisher`
needs to recover `n` from the PRF parameter `ptLen n`. -/
theorem eval_ciGame_macThenEncrypt_prfCipher_le_freshPads
    (family : List Bool → List Bool → List Bool)
    (hpoly : ComputableInPolyTime (fun pair => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    (M : MACScheme) (ptLen : ℕ → ℕ) (hptLenPoly : ComputableInPolyTime ptLen encUnary encUnary)
    (hmono : StrictMono ptLen) (hmsgLen : ∀ n, M.msgLen n = n)
    (hpairLen : ∀ n km, km ∈ (ProbComp.eval (M.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ tag ∈ (ProbComp.eval (M.sign km msg)).support,
        (encPair encBits encBits (msg, tag)).length = ptLen n)
    (adversary : CIAdversary) (Q : ℕ → ℕ) (n : ℕ)
    (hq : (adversary n []).IsQueryBounded (Q n)) :
    (ProbComp.eval ((macThenEncrypt (prfCipher family hpoly hlen) M ptLen hptLenPoly hmsgLen
        hpairLen).ciGame adversary n)) true ≤
      ((Game.advantage
          (ProbComp.eval
            (prfRealGame id family (mteCIToPrfDistinguisher M ptLen adversary) (ptLen n)))
          (ProbComp.eval
            (prfIdealGame id id (mteCIToPrfDistinguisher M ptLen adversary) (ptLen n))) : ℝ≥0) :
          ℝ≥0∞) +
        ((Q n).choose 2 : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ ptLen n) +
        ((ProbComp.eval (M.keyGen n)).bind fun km =>
          (ProbOracleComp.runWith (mteForgetfulOracle M n (ptLen n) km) (adversary n [])
            {}).bind (mteIdealFinal M n (ptLen n) km)) true := by
  rw [← eval_prfRealGame_mteCIToPrfDistinguisher family hpoly hlen M ptLen hptLenPoly hmono
    hmsgLen hpairLen adversary n]
  have hideal : (ProbComp.eval (prfIdealGame id id (mteCIToPrfDistinguisher M ptLen adversary)
      (ptLen n))) true ≤
      ((ProbComp.eval (M.keyGen n)).bind fun km =>
          (ProbOracleComp.runWith (mteForgetfulOracle M n (ptLen n) km) (adversary n [])
            {}).bind (mteIdealFinal M n (ptLen n) km)) true +
        ((Q n).choose 2 : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ ptLen n) := by
    rw [eval_prfIdealGame_mteCIToPrfDistinguisher M ptLen hmono adversary n]
    exact PMF.bind_apply_le_add_const_on_support _ true fun km _ =>
      mteFaithful_bind_apply_le M n (ptLen n) km hq (mteIdealFinal M n (ptLen n) km)
  exact ((Game.apply_true_le_of_advantage_le le_rfl).1.trans
    (add_le_add hideal le_rfl)).trans_eq (by ring)

/-! ## Efficiency of `B_prf` -/

private theorem computableInPolyTime_mtePlaintextValid (M : MACScheme) :
    ComputableInPolyTime
      (fun a : ℕ × List Bool × List Bool => mtePlaintextValid M a.1 a.2.1 a.2.2)
      (encPair encUnary (encPair encBits encBits)) encBool := by
  polytime [mtePlaintextValid]

private theorem isOraclePPTOn_mteCIToPrfHandler (M : MACScheme) (ptLen : ℕ → ℕ)
    (hptLenPoly : ComputableInPolyTime ptLen encUnary encUnary) :
    IsOraclePPTOn
      (encPair (encPair (encPair encUnary encBits) encBits)
        (encPair (encPair (encFinEnum Unit) encBits) (encList encBits)))
      (encPair encBits (encList encBits))
      (fun p : ((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × List (List Bool)) =>
        mteCIToPrfHandler M (GeneratorReindex.parameter ptLen p.1.1.1) p.1.1.1 p.1.2 p.2.1
          p.2.2) := by
  have hparam : ComputableInPolyTime (GeneratorReindex.parameter ptLen) encUnary encUnary :=
    GeneratorReindex.isPolyTime_parameter hptLenPoly .id'
  ppt [mteCIToPrfHandler]

private theorem isOraclePPTOn_mteCIToPrfPost (M : MACScheme) (ptLen : ℕ → ℕ)
    (hptLenPoly : ComputableInPolyTime ptLen encUnary encUnary) :
    IsOraclePPTOn (Operation := Unit)
      (encPair (encPair (encPair encUnary encBits) encBits) (encPair encBits (encList encBits)))
      encBool
      (fun q : ((ℕ × List Bool) × List Bool) × (List Bool × List (List Bool)) =>
        if !q.2.2.contains q.2.1 && q.2.1.length == 2 * q.1.1.1 then do
          let pad ← List.take q.1.1.1 <$> ProbOracleComp.query ((), q.2.1.take q.1.1.1)
          pure (mtePlaintextValid M (GeneratorReindex.parameter ptLen q.1.1.1) q.1.2
            (List.zipWith xor pad (q.2.1.drop q.1.1.1)))
        else
          pure false) := by
  have hparam : ComputableInPolyTime (GeneratorReindex.parameter ptLen) encUnary encUnary :=
    GeneratorReindex.isPolyTime_parameter hptLenPoly .id'
  have hvalid := computableInPolyTime_mtePlaintextValid M
  ppt

/-- An efficiency certificate for the reduction of step (9.13) of the proof of [BonehShoup2023],
Theorem 9.3 (one PRF block, messages of exactly `n` bits; #640), not a security statement:
`mteCIToPrfDistinguisher` is `IsOraclePPT` when the ciphertext-integrity adversary is. -/
theorem isOraclePPT_mteCIToPrfDistinguisher (M : MACScheme) (ptLen : ℕ → ℕ)
    (hptLenPoly : ComputableInPolyTime ptLen encUnary encUnary)
    {adversary : CIAdversary} (hadversary : IsOraclePPT encBits adversary) :
    IsOraclePPT encBool (mteCIToPrfDistinguisher M ptLen adversary) := by
  have hparam : ComputableInPolyTime (GeneratorReindex.parameter ptLen) encUnary encUnary :=
    GeneratorReindex.isPolyTime_parameter hptLenPoly .id'
  let EStateCaller := encPair (encPair encUnary encBits) encBits
  have hrun : IsOraclePPTOn (Operation := Unit) EStateCaller (encPair encBits (encList encBits))
      (fun p : (ℕ × List Bool) × List Bool =>
        (OracleComp.interpret
          (OracleComp.sumHandler
            (fun u => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin u)))
            (mteCIToPrfHandler M (GeneratorReindex.parameter ptLen p.1.1) p.1.1 p.2))
          (adversary (GeneratorReindex.parameter ptLen p.1.1) [])).run []) := by
    apply hadversary.run_interpret_preprocess_open
      (input := EStateCaller)
      (handler := fun p : (ℕ × List Bool) × List Bool =>
        mteCIToPrfHandler M (GeneratorReindex.parameter ptLen p.1.1) p.1.1 p.2)
      (prepare := fun p : (ℕ × List Bool) × List Bool =>
        (GeneratorReindex.parameter ptLen p.1.1, ([] : List Bool)))
      (initial := fun _ => ([] : List (List Bool)))
      (resources := fun p _ => 4 * p.1.1 + 2)
      (by dsimp only [EStateCaller]; fun_prop) (isOraclePPTOn_mteCIToPrfHandler M ptLen hptLenPoly)
      (ComputableInPolyTime.const []) (fun _ _ => True) (fun _ => trivial)
      (by dsimp only [EStateCaller]; fun_prop)
    intro p request log _ result hresult
    unfold mteCIToPrfHandler at hresult
    dsimp only at hresult
    split_ifs at hresult with hlenEq
    · obtain ⟨tag, _, hresult⟩ := OracleComp.mem_supportWith_bind_iff.mp hresult
      obtain ⟨r, hr, hresult⟩ := OracleComp.mem_supportWith_bind_iff.mp hresult
      have hrLen : r.length = p.1.1 := BitString.length_of_mem_support_uniformList <| by
        rwa [← BitString.eval_sampleList, ← ProbOracleComp.support_sample]
      obtain ⟨pad, hpad, hresult⟩ := OracleComp.mem_supportWith_bind_iff.mp hresult
      obtain ⟨rawPad, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hpad
      cases OracleComp.eq_of_mem_supportWith_pure hresult
      have hpadTake : (List.take p.1.1 rawPad).length ≤ p.1.1 := List.length_take_le _ _
      refine ⟨trivial, ?_, ?_⟩
      · simp only [List.length_append, List.length_zipWith, hrLen]
        lia
      · simp only [encList_cons, List.length_append, length_frame, encBits_apply,
          List.length_zipWith, hrLen]
        lia
    · cases OracleComp.eq_of_mem_supportWith_pure hresult
      exact ⟨trivial, by simp, Nat.le_add_right _ _⟩
  unfold mteCIToPrfDistinguisher
  exact (IsOraclePPTOn.cond (by polytime)
    ((M.keyGen_ppt.preprocess
        (hparam.comp (ComputableInPolyTime.fst encUnary encBits))).isOraclePPTOn.bind_with
      (hrun.bind_with (isOraclePPTOn_mteCIToPrfPost M ptLen hptLenPoly)))
    (ComputableInPolyTime.const false).isOraclePPTOn).isOraclePPT

end Cslib.Crypto
