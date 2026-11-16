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
