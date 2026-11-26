/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.EncForge
public import CslibFrontier.Crypto.Computational.Encryption.MACThenEncrypt
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair.Projections
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Tactic.PPT
import CslibFrontier.Tactic.EncLen

/-!
# Plaintext integrity of MAC-then-Encrypt

Exercise 9.15 of [BonehShoup2023] (printed p. 395) defines plaintext integrity: "The PI game is
identical to the CI game except that the winning condition is relaxed to: D(k, c) ≠ reject, and
D(k, c) ∉ {m₁, m₂, …}". The library's notion `SymmetricCipher.EncForge` is this game. Part (a)
asks to "Show that MAC-then-Encrypt is both CPA and PI secure." `indcpa_macThenEncrypt` gives the
CPA half; this module gives the PI half: `encForge_macThenEncrypt` proves `EncForge` for
`macThenEncrypt E M …` from `M.EUFCMA` alone, with no hypothesis on the cipher `E`. This is the
argument of part (a) from the library's `MACScheme.EUFCMA`, fresh-message unforgeability with
tagging queries in the message space, which Definition 6.2 implies (`MACScheme.SUFCMA.eufCma`).

The reduction `mteToMACForger` samples the encryption key itself, answers each encryption query by
asking the MAC signing oracle for a tag and encrypting the encoded pair, and decrypts the
adversary's ciphertext to read off its candidate forgery. A plaintext that `macThenEncrypt` accepts
and that the adversary never queried carries a valid tag on a message never signed.

## Main definitions

* `mteToMACForger`: the MAC forger built from a plaintext-integrity adversary.

## Main results

* `isOraclePPT_mteToMACForger`: the reduction is `IsOraclePPT`.
* `succProbability_encForgeGame_macThenEncrypt_le`: the success probability of an adversary in
  `encForgeGame` against `macThenEncrypt E M …` is at most that of `mteToMACForger` in the MAC
  game `eufCmaGame`.
* `encForge_macThenEncrypt`: `M.EUFCMA` implies `(macThenEncrypt E M …).EncForge`.

## References

* [D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023]
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

/-- Oracle handler for `mteToMACForger`: given a plaintext query `((), msg)`, if `msg.length == n`,
queries the MAC signing oracle on `msg`, truncates the tag to `tagBound` bits, and encrypts
`encPair encBits encBits (msg, tag)` under `ke` at parameter `ptLen`. -/
private noncomputable def mteToMACHandler (E : SymmetricCipher) (n ptLen tagBound : ℕ)
    (ke : List Bool) (request : Unit × List Bool) : StateT Unit (WordOracleComp Unit) (List Bool) :=
  fun _ =>
    if request.2.length == n then do
      let tag ← List.take tagBound <$> ProbOracleComp.query ((), request.2)
      let ct ← ProbOracleComp.sample (E.encrypt ptLen ke (encPair encBits encBits (request.2, tag)))
      return (ct, ())
    else
      return ([], ())

/-- Reduction from `encForgeGame` on `macThenEncrypt E M ptLen …` to `M.eufCmaGame`: samples
`ke ← E.keyGen (ptLen n)`, answers encryption queries by signing through the MAC oracle and
encrypting under `ke`, and decrypts the adversary's candidate ciphertext under `ke` to extract a
candidate `(msg, tag)` MAC forgery. -/
noncomputable def mteToMACForger (E : SymmetricCipher) (M : MACScheme) (ptLen tagBound : ℕ → ℕ)
    (adversary : CIAdversary) : Forger :=
  fun n _ => do
    let ke ← ProbOracleComp.sample (E.keyGen (ptLen n))
    (fun out : List Bool × Unit =>
      let dec := E.decrypt (ptLen n) ke out.1
      let pt := dec.getD []
      let msg := unframe pt
      let tag := dropFrame pt
      if dec.isSome && (encPair encBits encBits (msg, tag) == pt) &&
          (msg.length == M.msgLen n) then
        (msg, tag)
      else
        (if M.msgLen n == 0 then [false] else [], [])) <$>
      (OracleComp.interpret
        (OracleComp.sumHandler
          (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
          (mteToMACHandler E n (ptLen n) (tagBound n) ke))
        (adversary n [])).run ()

private theorem isOraclePPTOn_mteToMACHandler (E : SymmetricCipher)
    {ptLen tagBound : ℕ → ℕ}
    (hptLen : ComputableInPolyTime ptLen encUnary encUnary)
    (htagBound : ComputableInPolyTime tagBound encUnary encUnary) :
    IsOraclePPTOn
      (encPair (encPair (encPair encUnary encBits) encBits)
        (encPair (encPair (encFinEnum Unit) encBits) (encFinEnum Unit)))
      (encPair encBits (encFinEnum Unit))
      (fun pair : ((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit) =>
        mteToMACHandler E pair.1.1.1 (ptLen pair.1.1.1) (tagBound pair.1.1.1) pair.1.2
          pair.2.1 pair.2.2) := by
  ppt [mteToMACHandler]

private theorem computableInPolyTime_mteMACResources (ce de : ℕ)
    {ptLen tagBound : ℕ → ℕ}
    (hptLen : ComputableInPolyTime ptLen encUnary encUnary)
    (htagBound : ComputableInPolyTime tagBound encUnary encUnary) :
    ComputableInPolyTime
      (fun pair : ((ℕ × List Bool) × List Bool) × List Bool =>
        ce * (2 * ptLen pair.1.1.1 + 2 * pair.1.2.length +
          (2 * pair.2.length + tagBound pair.1.1.1 + 3) + 3) ^ de)
      (encPair (encPair (encPair encUnary encBits) encBits) encBits) encUnary := by
  polytime

private theorem computableInPolyTime_mteMACPost {S : Type} (encS : S ↪ List Bool)
    (E : SymmetricCipher) (M : MACScheme) {ptLen : ℕ → ℕ}
    (hptLen : ComputableInPolyTime ptLen encUnary encUnary) :
    ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × List Bool) × (List Bool × S) =>
        let dec := E.decrypt (ptLen p.1.1.1) p.1.2 p.2.1
        let pt := dec.getD []
        let msg := unframe pt
        let tag := dropFrame pt
        if dec.isSome && (encPair encBits encBits (msg, tag) == pt) &&
            (msg.length == M.msgLen p.1.1.1) then
          (msg, tag)
        else
          (if M.msgLen p.1.1.1 == 0 then [false] else [], []))
      (encPair (encPair (encPair encUnary encBits) encBits) (encPair encBits encS))
      (encPair encBits encBits) := by
  let ECaller := encPair (encPair encUnary encBits) encBits
  let EPost := encPair ECaller (encPair encBits encS)
  have hdecArg : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × List Bool) × (List Bool × S) =>
        (ptLen p.1.1.1, p.1.2, p.2.1))
      EPost (encPair encUnary (encPair encBits encBits)) := by
    dsimp only [EPost, ECaller]
    exact (hptLen.comp (by fun_prop)).prod (by fun_prop)
  have hdec : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × List Bool) × (List Bool × S) =>
        E.decrypt (ptLen p.1.1.1) p.1.2 p.2.1)
      EPost (encOption encBits) :=
    E.decrypt_polyTime.comp hdecArg
  have hpt := hdec.optionGetDWithInput (ComputableInPolyTime.const [])
  have hmsgLen : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × List Bool) × (List Bool × S) => M.msgLen p.1.1.1)
      EPost encUnary :=
    M.msgLen_polyTime.comp (by dsimp only [EPost, ECaller]; fun_prop)
  have hmsg := ComputableInPolyTime.unframe.comp hpt
  have htag := ComputableInPolyTime.dropFrame.comp hpt
  have hframeEq := (hmsg.prod htag).encoding_comp.beq hpt
  have hlenEq := ((by fun_prop : ComputableInPolyTime (fun x : List Bool => x.length)
    encBits encUnary).comp hmsg).beq hmsgLen
  have hfallback : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × List Bool) × (List Bool × S) =>
        ((if M.msgLen p.1.1.1 == 0 then [false] else []), ([] : List Bool)))
      EPost (encPair encBits encBits) :=
    ((hmsgLen.beq (ComputableInPolyTime.const 0)).ite' (ComputableInPolyTime.const [false])
      (ComputableInPolyTime.const [])).prod (ComputableInPolyTime.const [])
  exact (((hdec.optionIsSome.bool_and' hframeEq).bool_and' hlenEq).ite' (hmsg.prod htag)
    hfallback)

/-- `mteToMACForger` is oracle PPT when the adversary is and `ptLen` and `tagBound` are
polynomial-time computable. -/
theorem isOraclePPT_mteToMACForger (E : SymmetricCipher) (M : MACScheme)
    {ptLen tagBound : ℕ → ℕ}
    (hptLen : ComputableInPolyTime ptLen encUnary encUnary)
    (htagBound : ComputableInPolyTime tagBound encUnary encUnary)
    {adversary : CIAdversary} (hadversary : IsOraclePPT encBits adversary) :
    IsOraclePPT (encPair encBits encBits) (mteToMACForger E M ptLen tagBound adversary) := by
  obtain ⟨ce, de, hlenEnc⟩ := E.encrypt_ppt.length_le
  let ECaller := encPair (encPair encUnary encBits) encBits
  have hke : IsOraclePPTOn (Operation := Unit) (encPair encUnary encBits) encBits
      (fun caller : ℕ × List Bool => ProbOracleComp.sample (E.keyGen (ptLen caller.1))) :=
    (E.keyGen_ppt.preprocess (hptLen.comp (ComputableInPolyTime.fst _ _))).isOraclePPTOn
      (Operation := Unit)
  have hhandler := isOraclePPTOn_mteToMACHandler E hptLen htagBound
  have hprepare : ComputableInPolyTime
      (fun caller : (ℕ × List Bool) × List Bool => (caller.1.1, ([] : List Bool)))
      ECaller (encPair encUnary encBits) := by
    dsimp only [ECaller]; fun_prop
  have hres := computableInPolyTime_mteMACResources ce de hptLen htagBound
  have hrun : IsOraclePPTOn (Operation := Unit) ECaller (encPair encBits (encFinEnum Unit))
      (fun caller : (ℕ × List Bool) × List Bool =>
        (OracleComp.interpret
          (OracleComp.sumHandler
            (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
            (mteToMACHandler E caller.1.1 (ptLen caller.1.1) (tagBound caller.1.1) caller.2))
          (adversary caller.1.1 [])).run ()) := by
    apply hadversary.run_interpret_preprocess_open
      (input := ECaller)
      (handler := fun caller : (ℕ × List Bool) × List Bool =>
        mteToMACHandler E caller.1.1 (ptLen caller.1.1) (tagBound caller.1.1) caller.2)
      (prepare := fun caller : (ℕ × List Bool) × List Bool => (caller.1.1, ([] : List Bool)))
      (initial := fun _ => ())
      (resources := fun caller query =>
        ce * (2 * ptLen caller.1.1 + 2 * caller.2.length +
          (2 * query.length + tagBound caller.1.1 + 3) + 3) ^ de)
      hprepare hhandler (ComputableInPolyTime.const ())
      (fun _ _ => True) (fun _ => trivial) hres
    intro caller request state _ result hresult
    unfold mteToMACHandler at hresult
    split_ifs at hresult with hlenEq
    · obtain ⟨tag, htag, hresult⟩ := OracleComp.mem_supportWith_bind_iff.mp hresult
      obtain ⟨rawTag, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp htag
      obtain ⟨ct, hct, hresult⟩ := OracleComp.mem_supportWith_bind_iff.mp hresult
      obtain rfl := OracleComp.eq_of_mem_supportWith_pure hresult
      change ct ∈ OracleComp.support
        (ProbOracleComp.sample (E.encrypt (ptLen caller.1.1) caller.2
          (encPair encBits encBits (request.2, List.take (tagBound caller.1.1) rawTag)))) at hct
      rw [ProbOracleComp.support_sample] at hct
      have hctLen := hlenEnc (ptLen caller.1.1, caller.2,
        encPair encBits encBits (request.2, List.take (tagBound caller.1.1) rawTag)) ct hct
      simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply] at hctLen
      have htagTake : (List.take (tagBound caller.1.1) rawTag).length ≤ tagBound caller.1.1 :=
        List.length_take_le _ _
      have hpairLenLe : (encPair encBits encBits
          (request.2, List.take (tagBound caller.1.1) rawTag)).length ≤
          2 * request.2.length + tagBound caller.1.1 + 3 := by
        enc_len
      refine ⟨trivial, ?_, by simp⟩
      exact hctLen.trans (Nat.mul_le_mul_left ce (Nat.pow_le_pow_left (by lia) de))
    · obtain rfl := OracleComp.eq_of_mem_supportWith_pure hresult
      exact ⟨trivial, by simp, by simp⟩
  unfold mteToMACForger
  exact (hke.bind_with (hrun.map_with
    (computableInPolyTime_mteMACPost (encFinEnum Unit) E M hptLen))).isOraclePPT

private theorem eval_run_mteToMACHandler_signingOracle_eq (E : SymmetricCipher) (M : MACScheme)
    (ptLen : ℕ → ℕ) (hptLenPoly : ComputableInPolyTime ptLen encUnary encUnary)
    (hmsgLen : ∀ n, M.msgLen n = n)
    (hpairLen : ∀ n km, km ∈ (ProbComp.eval (M.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ tag ∈ (ProbComp.eval (M.sign km msg)).support,
        (encPair encBits encBits (msg, tag)).length = ptLen n)
    (n : ℕ) (tagBound : ℕ → ℕ) (ke km : List Bool)
    (hkm : km ∈ (ProbComp.eval (M.keyGen n)).support)
    (htagBound : ∀ km ∈ (ProbComp.eval (M.keyGen n)).support,
      ∀ c, c.length = M.msgLen n →
      ∀ tag ∈ (ProbComp.eval (M.sign km c)).support, tag.length ≤ tagBound n)
    (prog : WordOracleComp Unit (List Bool)) :
    ((OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifOracle m))
        (fun q s => ProbComp.eval (M.signingOracle n km q s)))
      ((OracleComp.interpret
        (OracleComp.sumHandler
          (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
          (mteToMACHandler E n (ptLen n) (tagBound n) ke))
        prog).run ())).run []) =
    (ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
        ((macThenEncrypt E M ptLen hptLenPoly hmsgLen hpairLen).encForgeOracle n
          (encPair encBits encBits (ke, km))))
      prog).run [])).map (fun (a, s') => ((a, ()), s')) := by
  rw [ProbOracleComp.run_interpret_run_interpret, ProbOracleComp.eval_run_interpret]
  have hsim := ProbOracleComp.run_interpret_map_state
    (oracle := fun q s =>
      ProbComp.eval ((macThenEncrypt E M ptLen hptLenPoly hmsgLen hpairLen).encForgeOracle n
        (encPair encBits encBits (ke, km)) q s))
    (oracle' := fun q (state : Unit × List (List Bool)) =>
      ((OracleComp.interpret
        (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifOracle m))
          (fun q s => ProbComp.eval (M.signingOracle n km q s)))
        (mteToMACHandler E n (ptLen n) (tagBound n) ke q state.1)).run state.2).map
        (fun result => (result.1.1, result.1.2, result.2)))
    (represent := fun s : List (List Bool) => ((), s))
    (step := by
      intro ⟨⟨⟩, msg⟩ queried
      dsimp only
      unfold SymmetricCipher.encForgeOracle mteToMACHandler
      by_cases hlenEq : (msg.length == n) = true
      · have hmsgM : msg.length = M.msgLen n := by rw [hmsgLen]; exact beq_iff_eq.mp hlenEq
        simp only [hlenEq, ↓reduceIte, macThenEncrypt, unframe_encPair_encBits,
          dropFrame_encPair_encBits, ProbComp.eval_bind, ProbComp.eval_pure,
          OracleComp.interpret_bind, StateT.run_bind, OracleComp.interpret_map, StateT.run_map,
          ProbOracleComp.interpret_query, MACScheme.signingOracle, SignatureScheme.signingOracleOn,
          beq_iff_eq.mpr hmsgM, _root_.PMF.monad_map_eq_map, Probability.PMF.monad_bind_eq_bind,
          ProbOracleComp.run_interpret_sample]
        simp only [PMF.map_bind, PMF.bind_map, Function.comp_def, PMF.bind_bind, PMF.pure_bind,
          OracleComp.interpret_pure, PMF.pure_map, StateT.run]
        apply PMF.bind_congr_on_support
        intro tag htag
        rw [List.take_of_length_le (htagBound km hkm msg hmsgM tag htag)]
        dsimp only [Pure.pure, StateT.pure]
        simp only [PMF.pure_map]
      · simp only [hlenEq, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure, PMF.pure_map,
          OracleComp.interpret_pure, StateT.run_pure, Probability.PMF.monad_pure_eq_pure])
    prog []
  have hsim' := congrArg (PMF.map fun result => ((result.1, result.2.1), result.2.2)) hsim
  simp only [PMF.map_comp, Function.comp_def] at hsim'
  exact hsim'.symm

/-- If `tagBound n` bounds every tag on an `n`-bit message, the success probability of `adversary`
in `encForgeGame` against `macThenEncrypt E M ptLen …` is at most that of
`mteToMACForger E M ptLen tagBound adversary` in `M.eufCmaGame`. -/
theorem succProbability_encForgeGame_macThenEncrypt_le (E : SymmetricCipher) (M : MACScheme)
    (ptLen : ℕ → ℕ) (hptLenPoly : ComputableInPolyTime ptLen encUnary encUnary)
    (hmsgLen : ∀ n, M.msgLen n = n)
    (hpairLen : ∀ n km, km ∈ (ProbComp.eval (M.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ tag ∈ (ProbComp.eval (M.sign km msg)).support,
        (encPair encBits encBits (msg, tag)).length = ptLen n)
    (tagBound : ℕ → ℕ) (adversary : CIAdversary) (n : ℕ)
    (htagBound : ∀ km ∈ (ProbComp.eval (M.keyGen n)).support,
      ∀ c, c.length = M.msgLen n →
      ∀ tag ∈ (ProbComp.eval (M.sign km c)).support, tag.length ≤ tagBound n) :
    Game.succProbability (ProbComp.eval
      ((macThenEncrypt E M ptLen hptLenPoly hmsgLen hpairLen).encForgeGame adversary n)) ≤
      Game.succProbability
        (ProbComp.eval (M.eufCmaGame (mteToMACForger E M ptLen tagBound adversary) n)) := by
  simp only [Game.succProbability, SymmetricCipher.encForgeGame, MACScheme.eufCmaGame,
    mteToMACForger, ProbComp.eval_bind, ProbComp.eval_pure, ProbOracleComp.eval_run_interpret]
  simp only [OracleComp.interpret_bind, StateT.run_bind, ProbOracleComp.run_interpret_sample,
    OracleComp.interpret_map, StateT.run_map, Probability.PMF.monad_bind_eq_bind,
    _root_.PMF.monad_map_eq_map, PMF.bind_map, Function.comp_def, PMF.bind_bind]
  rw [PMF.bind_comm (ProbComp.eval (M.keyGen n))]
  have hkeyGen : ProbComp.eval ((macThenEncrypt E M ptLen hptLenPoly hmsgLen hpairLen).keyGen n) =
      (ProbComp.eval (E.keyGen (ptLen n))).bind (fun ke =>
        (ProbComp.eval (M.keyGen n)).bind (fun km =>
          PMF.pure (encPair encBits encBits (ke, km)))) := by
    simp only [macThenEncrypt, ProbComp.eval_bind, ProbComp.eval_pure]
  rw [hkeyGen]
  simp only [PMF.bind_bind, PMF.pure_bind]
  refine ENNReal.toNNReal_mono (PMF.apply_ne_top _ true) ?_
  refine PMF.bind_apply_mono_on_support _ true fun ke _ =>
    PMF.bind_apply_mono_on_support _ true fun km hkm => ?_
  rw [← ProbOracleComp.eval_run_interpret,
    eval_run_mteToMACHandler_signingOracle_eq E M ptLen hptLenPoly hmsgLen hpairLen n tagBound
      ke km hkm htagBound (adversary n []),
    PMF.bind_map]
  refine Probability.PMF.map_true_mono _ fun out _ hwin => ?_
  dsimp only [Function.comp_def, macThenEncrypt] at hwin ⊢
  rw [unframe_encPair_encBits, dropFrame_encPair_encBits] at hwin
  cases hdec : E.decrypt (ptLen n) ke out.1 with
  | none => simp [hdec] at hwin
  | some pt =>
    simp only [hdec, Option.elim_some, Option.getD_some, Option.isSome_some,
      Bool.true_and] at hwin ⊢
    split_ifs at hwin with hcond
    · simp only [Bool.and_eq_true] at hcond
      simp only [hcond.1.1, hcond.1.2, Bool.and_self, ↓reduceIte, hcond.2, Bool.true_and,
        Bool.and_true]
      simpa using hwin
    · simp at hwin

/-- **Plaintext integrity of MAC-then-Encrypt.** If `M` satisfies the library's `MACScheme.EUFCMA`,
then `macThenEncrypt E M …` has plaintext integrity (`EncForge`), for every cipher `E`. This is the
argument of [BonehShoup2023], Exercise 9.15(a) (p. 395). `MACScheme.EUFCMA` keeps tagging queries
in the message space, as Definition 6.2 does, and only asks for a forgery on a new message, so a
MAC secure in the sense of Definition 6.2 satisfies it (`MACScheme.SUFCMA.eufCma`). The reduction
asks for tags on `n`-bit messages only. -/
theorem encForge_macThenEncrypt (E : SymmetricCipher) (M : MACScheme)
    (ptLen : ℕ → ℕ) (hptLenPoly : ComputableInPolyTime ptLen encUnary encUnary)
    (hmsgLen : ∀ n, M.msgLen n = n)
    (hpairLen : ∀ n km, km ∈ (ProbComp.eval (M.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ tag ∈ (ProbComp.eval (M.sign km msg)).support,
        (encPair encBits encBits (msg, tag)).length = ptLen n)
    (heuf : M.EUFCMA) :
    (macThenEncrypt E M ptLen hptLenPoly hmsgLen hpairLen).EncForge := by
  obtain ⟨tagBound, htagBoundPoly, htagBound⟩ := M.exists_tag_length_bound_of_length_eq
  apply SymmetricCipher.EncForge.of_negligible
  intro adversary hadversary
  refine negligible_of_le
    (heuf.negligible (mteToMACForger E M ptLen tagBound adversary)
      (isOraclePPT_mteToMACForger E M hptLenPoly htagBoundPoly hadversary)) fun n => ?_
  exact succProbability_encForgeGame_macThenEncrypt_le E M ptLen hptLenPoly hmsgLen hpairLen
    tagBound adversary n (htagBound n)

end Cslib.Crypto
