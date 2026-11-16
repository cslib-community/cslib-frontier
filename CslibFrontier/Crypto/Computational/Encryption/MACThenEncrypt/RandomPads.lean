/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.MACThenEncrypt
public import CslibFrontier.Crypto.Computational.Encryption.EncryptThenMAC
import CslibFrontier.Crypto.Computational.PseudorandomFunction.RandomOracle
import CslibFrontier.Languages.Probabilistic.RandomOracle.Programming
import CslibFrontier.Languages.Probabilistic.Oracle.Substitution.RunWith
import CslibFrontier.Languages.Probabilistic.Oracle.Substitution.QueryCount
import CslibFrontier.Probability.StatisticalDistance.CloseTo
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair.Projections
import CslibFrontier.Languages.Probabilistic.Oracle.Norm
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Probability.BitString.List
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT
import CslibFrontier.Tactic.EncLen

/-!
# MAC-then-encrypt over the one-block PRF cipher: the PRF step (DRAFT)
-/

public section

namespace Cslib.Crypto

open Cslib.Probability ProbComp OracleComp BitString Turing.MultiTapeTM
open scoped NNReal ENNReal

/-! ## The plaintext check of `macThenEncrypt` -/

/-- The check `macThenEncrypt` applies to a decrypted plaintext `p`: canonical pair encoding,
message length, tag verification. -/
def mtePlaintextValid (M : MACScheme) (n : ℕ) (km p : List Bool) : Bool :=
  (encPair encBits encBits (unframe p, dropFrame p) == p) &&
    ((unframe p).length == M.msgLen n) && M.verify km (unframe p) (dropFrame p)

/-! ## The three reductions (programs) -/

/-- `B_prf`'s encryption handler: tag with `km`, draw the IV `r`, ask the PRF oracle for the pad. -/
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

/-- `B_prf` (Theorem 9.3, (9.13)): runs the CI adversary, simulating `macThenEncrypt (prfCipher F)`
with its PRF oracle, then decrypts the forgery with one more oracle call. -/
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

/-- A record of one answered encryption query: IV, pad, message, tag. -/
abbrev MteRec := List Bool × List Bool × List Bool × List Bool

/-- The ciphertext a record stands for. -/
def MteRec.ct (m : ℕ) (e : MteRec) : List Bool :=
  e.1 ++ List.zipWith xor (e.2.1.take m) (encPair encBits encBits (e.2.2.1, e.2.2.2))

/-- State of the ideal games: the random-function cache and the query history, newest first. -/
abbrev MteState := List (List Bool × List Bool) × List MteRec

/-- The coins of one encryption query: the tag of the message, then the IV. -/
private noncomputable def mteCoins (M : MACScheme) (m : ℕ) (km : List Bool)
    (request : Unit × List Bool) : PMF (List Bool × List Bool) :=
  (ProbComp.eval (M.sign km request.2)).bind fun tag =>
    (BitString.uniformList m).map fun r => (tag, r)

/-- The reply to one encryption query and the history entry it adds, from its coins and pad. -/
private def mteFinish (m : ℕ) (request : Unit × List Bool) (coins : List Bool × List Bool)
    (pad : List Bool) (history : List MteRec) : List Bool × List MteRec :=
  (coins.2 ++ List.zipWith xor (pad.take m) (encPair encBits encBits (request.2, coins.1)),
    (coins.2, pad, request.2, coins.1) :: history)

/-- The encryption oracle of the CI game of `macThenEncrypt` over `prfCipher` with a lazily
sampled random function in place of the PRF: an `n`-bit message is tagged, a fresh `m`-bit IV is
drawn, its pad is looked up or drawn, and the query is logged. -/
private noncomputable def mteFaithfulOracle (M : MACScheme) (n m : ℕ) (km : List Bool)
    (request : Unit × List Bool) : StateT MteState PMF (List Bool) :=
  RandomOracle.lazyProgramHandler (Reply := fun _ : Unit × List Bool => List Bool)
    (Coins := fun _ : Unit × List Bool => List Bool × List Bool) (BitString.uniformList m)
    (fun req => req.2.length == n) (fun _ _ history => PMF.pure ([], history))
    (mteCoins M m km) (fun _ coins => coins.2) (mteFinish m) (.inl request)

/-- Game 1 of the proof of [BonehShoup2023], Theorem 9.3 (p. 375): the encryption oracle of the
ideal CI game with a fresh pad for every query. An `n`-bit message is tagged, a fresh `m`-bit IV
and a fresh pad are drawn, the reply is `IV ++ (pad ⊕ (msg ‖ tag))`, and the IV, pad, message and
tag are logged; the pair `(IV, pad)` is put in front of the cache. Other queries get `[]`. -/
noncomputable def mteForgetfulOracle (M : MACScheme) (n m : ℕ) (km : List Bool)
    (request : Unit × List Bool) : StateT MteState PMF (List Bool) :=
  RandomOracle.overwriteProgramHandler (Reply := fun _ : Unit × List Bool => List Bool)
    (Coins := fun _ : Unit × List Bool => List Bool × List Bool) (BitString.uniformList m)
    (fun req => req.2.length == n) (fun _ _ history => PMF.pure ([], history))
    (mteCoins M m km) (fun _ coins => coins.2) (mteFinish m) (.inl request)

/-- The winning condition of the ideal CI games: the final ciphertext is new and has `2 * m` bits,
and its plaintext under the pad of its IV (looked up in the cache, or drawn fresh) passes the check
of `macThenEncrypt`. -/
noncomputable def mteIdealFinal (M : MACScheme) (n m : ℕ) (km : List Bool)
    (out : List Bool × MteState) : PMF Bool :=
  if !(out.2.2.map (MteRec.ct m)).contains out.1 && out.1.length == 2 * m then
    (memoize (fun _ => BitString.uniformList m) (out.1.take m) out.2.1).map fun res =>
      mtePlaintextValid M n km (List.zipWith xor (res.1.take m) (out.1.drop m))
  else
    PMF.pure false

private theorem mteFaithfulOracle_apply (M : MACScheme) (n m : ℕ) (km : List Bool)
    (request : Unit × List Bool) (st : MteState) :
    mteFaithfulOracle M n m km request st =
      if request.2.length == n then
        (ProbComp.eval (M.sign km request.2)).bind fun tag =>
          (BitString.uniformList m).bind fun r =>
            (memoize (fun _ => BitString.uniformList m) r st.1).map fun res =>
              (r ++ List.zipWith xor (res.1.take m) (encPair encBits encBits (request.2, tag)),
                (res.2, (r, res.1, request.2, tag) :: st.2))
      else
        PMF.pure ([], st) := by
  obtain ⟨cache, history⟩ := st
  unfold mteFaithfulOracle RandomOracle.lazyProgramHandler
  by_cases hlen : (request.2.length == n) = true
  · simp only [hlen, ↓reduceDIte, ↓reduceIte, mteCoins, mteFinish,
      Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure, PMF.bind_bind,
      PMF.bind_map, PMF.map, Function.comp_def, PMF.pure_bind]
  · simp [hlen]

/-! ## The random-function step -/

/-- Replacing the lazily sampled random function by a fresh pad for every query moves the
probability of any final event by at most `Q.choose 2 / 2 ^ m`: an instance of
`RandomOracle.closeTo_runWith_lazyProgramHandler_overwriteProgramHandler_choose_two`. -/
private theorem mteFaithful_bind_apply_le (M : MACScheme) (n m : ℕ) (km : List Bool)
    {program : WordOracleComp Unit (List Bool)} {Q : ℕ} (hq : program.IsQueryBounded Q)
    (next : List Bool × MteState → PMF Bool) :
    ((ProbOracleComp.runWith (mteFaithfulOracle M n m km) program ([], [])).bind next) true ≤
      ((ProbOracleComp.runWith (mteForgetfulOracle M n m km) program ([], [])).bind next)
          true + (Q.choose 2 : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ m) := by
  let embed : (q : Unit × List Bool) →
      ProbOracleComp (OracleSpec.sum (fun _ : Unit × List Bool => List Bool)
        (fun _ : List Bool => List Bool)) (List Bool) :=
    fun q => ProbOracleComp.query (spec := OracleSpec.sum (fun _ : Unit × List Bool => List Bool)
      (fun _ : List Bool => List Bool)) (.inl q)
  have hmin : ∀ req : Unit × List Bool, (req.2.length == n) = true → ∀ r,
      ((mteCoins M m km req).map fun coins => coins.2) r ≤ (1 : ℝ≥0∞) / 2 ^ m := by
    intro req _ r
    have hmap : ((mteCoins M m km req).map fun coins => coins.2) = BitString.uniformList m := by
      simp only [mteCoins, PMF.map_bind, PMF.map_comp, Function.comp_def, PMF.map_id']
      exact PMF.bind_const _ _
    rw [hmap]
    exact BitString.uniformList_apply_le m r
  have hqS : IsCostBounded (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (fun _ => 0)))
      (ProbOracleComp.simulate embed program) Q :=
    ProbOracleComp.isCostBounded_simulate (cost := fun _ => 1)
      (fun q => by simpa using ProbOracleComp.isCostBounded_query
        (Sum.elim (fun _ => 1) (fun _ => 0)) (Sum.inl q)) hq
  have hqH : IsCostBounded (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) (fun _ => 1)))
      (ProbOracleComp.simulate embed program) 0 :=
    ProbOracleComp.isCostBounded_simulate (cost := fun _ => 0)
      (fun q => by simpa using ProbOracleComp.isCostBounded_query
        (Sum.elim (fun _ => 0) (fun _ => 1)) (Sum.inl q))
      (IsCostBounded.of_forall_cost_eq_zero (fun q => by cases q <;> rfl) program)
  have hclose := RandomOracle.closeTo_runWith_lazyProgramHandler_overwriteProgramHandler_choose_two
    (Reply := fun _ : Unit × List Bool => List Bool)
    (Coins := fun _ : Unit × List Bool => List Bool × List Bool) (BitString.uniformList m)
    (fun req => req.2.length == n) (fun _ _ history => PMF.pure ([], history))
    (mteCoins M m km) (fun _ coins => coins.2) (mteFinish m) hmin hqS hqH [] []
  have hrun (oracle : (q : (Unit × List Bool) ⊕ List Bool) → StateT MteState PMF
      ((OracleSpec.sum (fun _ : Unit × List Bool => List Bool) (fun _ : List Bool => List Bool))
        q)) :
      ProbOracleComp.runWith oracle (ProbOracleComp.simulate embed program) ([], []) =
        ProbOracleComp.runWith (fun q => oracle (.inl q)) program ([], []) := by
    rw [ProbOracleComp.runWith_simulate]
    simp [embed]
  rw [hrun, hrun] at hclose
  have h := (hclose.bind_left next) {true}
  simpa [PMF.toOuterMeasure_apply_singleton] using h

/-! ## The PRF step -/

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
  by_cases hfresh : (!out.2.contains out.1) = true
  · by_cases hlenCt : (out.1.length == 2 * ptLen n) = true
    · have htakeLen : (out.1.take (ptLen n)).length = ptLen n := by
        rw [List.length_take, beq_iff_eq.mp hlenCt]; omega
      have hpadLen : (family ke (out.1.take (ptLen n))).length = ptLen n := by
        rw [hlen _ _ (by rw [htakeLen, hkeLen]), hkeLen]
      simp only [runWith_norm, pmf_norm, prfOracle, htakeLen, ↓reduceIte,
        List.take_of_length_le hpadLen.le, hfresh, hlenCt, Bool.true_and, Option.elim,
        mtePlaintextValid, hmsgLen]
      congr 1
      split_ifs with h
      · rw [h]; rfl
      · rw [Bool.not_eq_true] at h; rw [h]; rfl
    · have hlenCt' : (out.1.length == 2 * ptLen n) = false := (Bool.not_eq_true _).mp hlenCt
      simp only [hlenCt', Bool.false_eq_true, ↓reduceIte, runWith_norm, pmf_norm, hfresh,
        Bool.true_and, Option.elim, Option.isSome_none]
  · have hfresh' : (!out.2.contains out.1) = false := (Bool.not_eq_true _).mp hfresh
    simp only [Bool.false_eq_true, ↓reduceIte, runWith_norm, pmf_norm, hfresh',
      Bool.false_and]


/-- The ideal PRF game of `B_prf` is the CI game against the lazily sampled random function. -/
private theorem eval_prfIdealGame_mteCIToPrfDistinguisher (M : MACScheme) (ptLen : ℕ → ℕ)
    (hmono : StrictMono ptLen) (adversary : CIAdversary) (n : ℕ) :
    ProbComp.eval (prfIdealGame id id (mteCIToPrfDistinguisher M ptLen adversary) (ptLen n)) =
      (ProbComp.eval (M.keyGen n)).bind fun km =>
        (ProbOracleComp.runWith (mteFaithfulOracle M n (ptLen n) km) (adversary n [])
          ([], [])).bind (mteIdealFinal M n (ptLen n) km) := by
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
            ProbComp.eval (cachedRandomFunctionOracle (ptLen n) q.2 state))
          ((mteCIToPrfHandler M n (ptLen n) km q).run state.1) state.2))
    (represent := fun st : MteState => (st.2.map (MteRec.ct (ptLen n)), st.1))
    (step := by
      rintro ⟨⟨⟩, msg⟩ ⟨cache, hist⟩
      rw [mteFaithfulOracle_apply]
      unfold mteCIToPrfHandler
      dsimp only [StateT.run]
      by_cases hmsg : (msg.length == n) = true
      · simp only [hmsg, ↓reduceIte, runWith_norm, pmf_norm, BitString.eval_sampleList]
        refine PMF.bind_congr_on_support _ _ _ fun tag _ => ?_
        refine PMF.bind_congr_on_support _ _ _ fun r hr => ?_
        have hrLen : r.length = ptLen n := BitString.length_of_mem_support_uniformList hr
        simp only [cachedRandomFunctionOracle, hrLen, ↓reduceIte, ProbComp.eval_memoize,
          BitString.eval_sampleList]
        rfl
      · simp [hmsg, runWith_norm, pmf_norm])
    (adversary n []) ([], [])
  rw [show (([] : List (List Bool)), ([] : List (List Bool × List Bool))) =
      (fun st : MteState => (st.2.map (MteRec.ct (ptLen n)), st.1)) ([], []) from rfl,
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
    simp only [hcond, ↓reduceIte, runWith_norm, pmf_norm, cachedRandomFunctionOracle, htakeLen,
      ProbComp.eval_memoize, BitString.eval_sampleList]
    rfl
  · simp only [hcond, Bool.false_eq_true, ↓reduceIte, runWith_norm, pmf_norm]

/-- **Step (9.13) of the proof of [BonehShoup2023], Theorem 9.3**, for `macThenEncrypt` over the
one-block cipher `prfCipher`, messages of exactly `n` bits and a polynomial schedule `ptLen`; it is
a step of the proof, not the theorem. For a CI adversary with at most `Q n` encryption queries, its
winning probability is at most the PRF advantage of `mteCIToPrfDistinguisher`, plus
`(Q n).choose 2 / 2 ^ ptLen n` for a repeated IV (the source prints `Q ^ 2 / (2 |X|)`), plus the
winning probability in Game 1, the ideal game with a fresh pad for every query
(`mteForgetfulOracle`, `mteIdealFinal`). `StrictMono ptLen` is what `mteCIToPrfDistinguisher`
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
            ([], [])).bind (mteIdealFinal M n (ptLen n) km)) true := by
  rw [← eval_prfRealGame_mteCIToPrfDistinguisher family hpoly hlen M ptLen hptLenPoly hmono
    hmsgLen hpairLen adversary n]
  have hideal : (ProbComp.eval (prfIdealGame id id (mteCIToPrfDistinguisher M ptLen adversary)
      (ptLen n))) true ≤
      ((ProbComp.eval (M.keyGen n)).bind fun km =>
          (ProbOracleComp.runWith (mteForgetfulOracle M n (ptLen n) km) (adversary n [])
            ([], [])).bind (mteIdealFinal M n (ptLen n) km)) true +
        ((Q n).choose 2 : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ ptLen n) := by
    rw [eval_prfIdealGame_mteCIToPrfDistinguisher M ptLen hmono adversary n]
    exact PMF.bind_apply_le_add_const_on_support _ true fun km _ =>
      mteFaithful_bind_apply_le M n (ptLen n) km hq (mteIdealFinal M n (ptLen n) km)
  refine ((Game.apply_true_le_of_advantage_le le_rfl).1.trans
    (add_le_add hideal le_rfl)).trans (le_of_eq ?_)
  ring

/-! ## Efficiency of `B_prf` -/

private theorem computableInPolyTime_mtePlaintextValid (M : MACScheme) :
    ComputableInPolyTime
      (fun a : ℕ × List Bool × List Bool => mtePlaintextValid M a.1 a.2.1 a.2.2)
      (encPair encUnary (encPair encBits encBits)) encBool := by
  let EIn := encPair encUnary (encPair encBits encBits)
  have q_p : ComputableTidilyInPolyTime (fun a : ℕ × List Bool × List Bool => a.2.2)
      EIn encBits := by dsimp only [EIn]; fun_prop
  have q_msg : ComputableTidilyInPolyTime (fun a : ℕ × List Bool × List Bool => unframe a.2.2)
      EIn encBits := ComputableTidilyInPolyTime.unframe.comp q_p
  have q_tag : ComputableTidilyInPolyTime (fun a : ℕ × List Bool × List Bool => dropFrame a.2.2)
      EIn encBits := ComputableTidilyInPolyTime.dropFrame.comp q_p
  have hframeEq : ComputableTidilyInPolyTime
      (fun a : ℕ × List Bool × List Bool =>
        encPair encBits encBits (unframe a.2.2, dropFrame a.2.2) == a.2.2) EIn encBool :=
    (q_msg.prod q_tag).encoded.beq q_p
  have hmsgLen := M.msgLen_polyTime.tidy
  have hverify := M.verify_polyTime.tidy
  have hlen : ComputableTidilyInPolyTime
      (fun a : ℕ × List Bool × List Bool => (unframe a.2.2).length == M.msgLen a.1)
      EIn encBool := by dsimp only [EIn]; fun_prop
  have hver : ComputableTidilyInPolyTime
      (fun a : ℕ × List Bool × List Bool => M.verify a.2.1 (unframe a.2.2) (dropFrame a.2.2))
      EIn encBool := by dsimp only [EIn]; fun_prop
  exact ((hframeEq.bool_and' hlen).bool_and' hver).computableInPolyTime

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
  have hparamT := hparam.tidy
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
  have hparamT := hparam.tidy
  have hvalid := computableInPolyTime_mtePlaintextValid M
  ppt

/-- `B_prf` is strict oracle PPT when the CI adversary is. -/
theorem isOraclePPT_mteCIToPrfDistinguisher (M : MACScheme) (ptLen : ℕ → ℕ)
    (hptLenPoly : ComputableInPolyTime ptLen encUnary encUnary)
    {adversary : CIAdversary} (hadversary : IsOraclePPT encBits adversary) :
    IsOraclePPT encBool (mteCIToPrfDistinguisher M ptLen adversary) := by
  have hparam : ComputableInPolyTime (GeneratorReindex.parameter ptLen) encUnary encUnary :=
    GeneratorReindex.isPolyTime_parameter hptLenPoly .id'
  let ECaller := encPair encUnary encBits
  let EStateCaller := encPair ECaller encBits
  have hhandler := isOraclePPTOn_mteCIToPrfHandler M ptLen hptLenPoly
  have hprepare : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × List Bool =>
        (GeneratorReindex.parameter ptLen p.1.1, ([] : List Bool)))
      EStateCaller ECaller := by
    dsimp only [EStateCaller, ECaller]
    exact ((hparam.comp ((ComputableInPolyTime.fst encUnary encBits).comp
      (ComputableInPolyTime.fst ECaller encBits))).prod
      (ComputableInPolyTime.const ([] : List Bool)))
  have hres : ComputableInPolyTime
      (fun pair : ((ℕ × List Bool) × List Bool) × List Bool => 4 * pair.1.1.1 + 2)
      (encPair EStateCaller encBits) encUnary := by
    dsimp only [EStateCaller, ECaller]; fun_prop
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
      hprepare hhandler (ComputableInPolyTime.const [])
      (fun _ _ => True) (fun _ => trivial) hres
    intro p request log _ result hresult
    unfold mteCIToPrfHandler at hresult
    dsimp only at hresult
    split_ifs at hresult with hlenEq
    · obtain ⟨tag, _, hresult⟩ := OracleComp.mem_supportWith_bind_iff.mp hresult
      obtain ⟨r, hr, hresult⟩ := OracleComp.mem_supportWith_bind_iff.mp hresult
      change r ∈ OracleComp.support
        (ProbOracleComp.sample (BitString.sampleList p.1.1)) at hr
      rw [ProbOracleComp.support_sample, BitString.eval_sampleList] at hr
      have hrLen : r.length = p.1.1 := BitString.length_of_mem_support_uniformList hr
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
  have hkm : IsOraclePPTOn (Operation := Unit) ECaller encBits
      (fun caller : ℕ × List Bool =>
        ProbOracleComp.sample (M.keyGen (GeneratorReindex.parameter ptLen caller.1))) :=
    (M.keyGen_ppt.preprocess
      (hparam.comp (ComputableInPolyTime.fst encUnary encBits))).isOraclePPTOn
  have hpost := isOraclePPTOn_mteCIToPrfPost M ptLen hptLenPoly
  have hinner : IsOraclePPTOn (Operation := Unit) EStateCaller encBool
      (fun p : (ℕ × List Bool) × List Bool => do
        let out ← (OracleComp.interpret
          (OracleComp.sumHandler
            (fun u => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin u)))
            (mteCIToPrfHandler M (GeneratorReindex.parameter ptLen p.1.1) p.1.1 p.2))
          (adversary (GeneratorReindex.parameter ptLen p.1.1) [])).run []
        if !out.2.contains out.1 && out.1.length == 2 * p.1.1 then do
          let pad ← List.take p.1.1 <$> ProbOracleComp.query ((), out.1.take p.1.1)
          pure (mtePlaintextValid M (GeneratorReindex.parameter ptLen p.1.1) p.2
            (List.zipWith xor pad (out.1.drop p.1.1)))
        else
          pure false) :=
    hrun.bind_with hpost
  have hbody : IsOraclePPTOn (Operation := Unit) ECaller encBool
      (fun caller : ℕ × List Bool => do
        let km ← ProbOracleComp.sample (M.keyGen (GeneratorReindex.parameter ptLen caller.1))
        let out ← (OracleComp.interpret
          (OracleComp.sumHandler
            (fun u => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin u)))
            (mteCIToPrfHandler M (GeneratorReindex.parameter ptLen caller.1) caller.1 km))
          (adversary (GeneratorReindex.parameter ptLen caller.1) [])).run []
        if !out.2.contains out.1 && out.1.length == 2 * caller.1 then do
          let pad ← List.take caller.1 <$> ProbOracleComp.query ((), out.1.take caller.1)
          pure (mtePlaintextValid M (GeneratorReindex.parameter ptLen caller.1) km
            (List.zipWith xor pad (out.1.drop caller.1)))
        else
          pure false) :=
    hkm.bind_with hinner
  have houterCond : ComputableInPolyTime
      (fun caller : ℕ × List Bool => ptLen (GeneratorReindex.parameter ptLen caller.1) == caller.1)
      ECaller encBool := by
    have hptT := hptLenPoly.tidy
    have hparamT := hparam.tidy
    dsimp only [ECaller]
    exact (by fun_prop : ComputableTidilyInPolyTime _ ECaller encBool).computableInPolyTime
  have houterNo : IsOraclePPTOn (Operation := Unit) ECaller encBool
      (fun _ : ℕ × List Bool => (pure false : WordOracleComp Unit Bool)) :=
    (ComputableInPolyTime.const false).isOraclePPTOn (Operation := Unit)
  unfold mteCIToPrfDistinguisher
  exact (IsOraclePPTOn.cond' houterCond hbody houterNo).isOraclePPT

end Cslib.Crypto
