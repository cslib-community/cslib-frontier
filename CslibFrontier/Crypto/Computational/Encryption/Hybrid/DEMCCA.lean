/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.Hybrid.CCA
public import CslibFrontier.Crypto.Computational.Encryption.Authenticated
public import CslibFrontier.Crypto.Encoding
public import CslibFrontier.Languages.Probabilistic.Oracle.Substitution
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair.Projections
import CslibFrontier.Languages.Probabilistic.Oracle.Norm
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Computability.Probabilistic.Oracle.Substitution
import CslibFrontier.Tactic.PPT

/-!
# The symmetric-cipher leg of hybrid CCA security

This intermediate experiment uses the symmetric cipher's actual key distribution. Its
distinguished encapsulation component is redirected to that key before and after the challenge.
Its security is the DEM hop of [BonehShoup2023], Exercise 12.5(a): a step toward that exercise,
not the exercise itself. `Cslib.Crypto.Encryption.hybrid_indcca2On` adds the two KEM hops. On the
DEM side, `SymmetricCipher.ctSpace` models the ciphertext space `C` and `OneTimeINDCCA` answers
decryption queries outside `C` with the rejection `[]` (`decrypt_eq_none_of_ctSpace_eq_false`), so
on an efficiently recognizable `C` it matches Attack Game 9.2 (Definition 9.6, printed pp. 362–363).
The full exercise stays open on the KEM side (#5293, #5686).

## Main definitions

* `Cslib.Crypto.Encryption.hybridDEMGame`: the existing two-phase CCA game with a hidden DEM key.
* `Cslib.Crypto.Encryption.hybridDEMHandler`: canonical parsing and bounded oracle forwarding.
* `Cslib.Crypto.Encryption.hybridToOneTimeCCAAdversary`: the one-time symmetric CCA reduction.

## Main results

* `Cslib.Crypto.Encryption.eval_hybridDEMGame`: exact equality with the symmetric experiment.
* `Cslib.Crypto.Encryption.isOraclePPT_hybridToOneTimeCCAAdversary`: native reduction certificate.
* `Cslib.Crypto.Encryption.isPPTOn_hybridDEMGame`: native certificate for the closed game.
* `Cslib.Crypto.SymmetricCipher.OneTimeINDCCA.indistinguishable_hybridDEMGame`:
  the loss-one DEM hop, a step toward Exercise 12.5(a).

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Exercise 12.5(a), printed p. 513.
-/

@[expose] public section

namespace Cslib.Crypto.Encryption

open Probability Turing.MultiTapeTM

/-- The DEM intermediate game. Original KEM keys and encapsulation retain their joint law;
the independently sampled DEM key is used for the distinguished component in both phases.
The source symmetric experiment admits exactly `n`-bit challenge messages. -/
noncomputable def hybridDEMGame (E : SymmetricCipher)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (decaps : ℕ → List Bool → List Bool → Option (List Bool))
    (adversary : WordCCA2Adversary) (bit : Bool) (n : ℕ) : ProbComp Bool := do
  let keys ← keyGen n
  let encapsulated ← encaps n keys.1
  let k ← E.keyGen n
  cca2GameOn (fun n _ m0 m1 => (m0.length == n) && (m1.length == n)) encBits
    (fun _ => pure keys)
    (fun n _ msg => (fun ct => encPair encBits encBits (encapsulated.2, ct)) <$>
      E.encrypt n k msg)
    (hybridDecrypt (fun n sk ct =>
      if ct == encapsulated.2 then some k else decaps n sk ct) E.decrypt)
    adversary bit n

/-- Forward only canonical ciphertexts with the distinguished KEM component. All other
canonical ciphertexts use local decapsulation and decryption. A bounded raw reply preserves
the distinction between rejection (`[]`) and a successful empty message (`[true]`). -/
noncomputable def hybridDEMHandler (E : SymmetricCipher)
    (decaps : ℕ → List Bool → List Bool → Option (List Bool))
    (decBound : ℕ → List Bool → ℕ) (n : ℕ) (sk ctK : List Bool)
    (request : Unit × List Bool) : WordOracleComp Bool (List Bool) :=
  if encPair encBits encBits (unframe request.2, dropFrame request.2) == request.2 then
    if unframe request.2 == ctK then
      List.take (decBound n (dropFrame request.2)) <$>
        ProbOracleComp.query (true, dropFrame request.2)
    else
      pure (encOption encBits (hybridDecrypt decaps E.decrypt n sk request.2))
  else pure []

/-- Both CCA phases for fixed original KEM keys and encapsulation. The hidden symmetric key
is owned by the external oracle and is never an argument to this continuation. -/
noncomputable def hybridDEMContinuation (E : SymmetricCipher)
    (decaps : ℕ → List Bool → List Bool → Option (List Bool))
    (ctBound : ℕ → ℕ) (decBound : ℕ → List Bool → ℕ)
    (adversary : WordCCA2Adversary) (n : ℕ) (pk sk ctK : List Bool) :
    WordOracleComp Bool Bool := do
  let handler := hybridDEMHandler E decaps decBound n sk ctK
  let choice ← ProbOracleComp.simulate handler (adversary.choose n pk)
  if (ChoiceOut.msg₀ choice).length == n && (ChoiceOut.msg₁ choice).length == n then
    let ct ← List.take (ctBound n) <$> ProbOracleComp.query
      (false, encPair encBits encBits (ChoiceOut.msg₀ choice, ChoiceOut.msg₁ choice))
    ProbOracleComp.simulate handler
      (adversary.guess n (ChoiceOut.state choice)
        (encPair encBits encBits (ctK, ct)))
  else pure false

/-- Simulate both public-key CCA phases, making exactly one valid symmetric encryption query
when the selected messages have length `n`. In particular, an empty encryption reply is a
legitimate ciphertext, not a rejection marker. The original encapsulated key is not exposed. -/
noncomputable def hybridToOneTimeCCAAdversary (E : SymmetricCipher)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (decaps : ℕ → List Bool → List Bool → Option (List Bool))
    (ctBound : ℕ → ℕ) (decBound : ℕ → List Bool → ℕ)
    (adversary : WordCCA2Adversary) : CCAAdversary := fun n _ => do
  let keys ← ProbOracleComp.sample (keyGen n)
  let encapsulated ← ProbOracleComp.sample (encaps n keys.1)
  hybridDEMContinuation E decaps ctBound decBound adversary n keys.1 keys.2 encapsulated.2

/-- Before the challenge, the distinguished component uses the hidden DEM key, including
queries made before the adversary has selected its messages. -/
theorem run_hybridDEMHandler_before (E : SymmetricCipher)
    (decaps : ℕ → List Bool → List Bool → Option (List Bool))
    (decBound : ℕ → List Bool → ℕ) (n : ℕ) (sk ctK k : List Bool) (bit : Bool)
    (hbound : ∀ ct, (encOption encBits (E.decrypt n k ct)).length ≤ decBound n ct)
    (request : Unit × List Bool) :
    (OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
        (E.oneTimeCCAOracle n k bit))
      (hybridDEMHandler E decaps decBound n sk ctK request)).run [] =
      pure (encOption encBits (hybridDecrypt
        (fun n sk ct => if ct == ctK then some k else decaps n sk ct)
        E.decrypt n sk request.2), []) := by
  simp only [hybridDEMHandler, hybridDecrypt]
  split_ifs with hcanonical hkem
  · simp only [OracleComp.interpret_map, ProbOracleComp.interpret_query]
    change (pure (List.take (decBound n (dropFrame request.2))
      (encOption encBits (E.decrypt n k (dropFrame request.2))), []) :
        ProbComp (List Bool × List (List Bool))) = _
    rw [List.take_of_length_le (hbound _)]
    rfl
  · simp only [OracleComp.interpret_pure, StateT.run_pure]
  · simp only [OracleComp.interpret_pure, StateT.run_pure, encOption_none]

/-- After the challenge, symmetric challenge rejection agrees with exact hybrid-word
rejection. Canonical framing is essential: another spelling of the same projections is rejected
before it can reach the symmetric oracle. -/
theorem run_hybridDEMHandler_after (E : SymmetricCipher)
    (decaps : ℕ → List Bool → List Bool → Option (List Bool))
    (decBound : ℕ → List Bool → ℕ) (n : ℕ) (sk ctK k ctD : List Bool) (bit : Bool)
    (hbound : ∀ ct, (encOption encBits (E.decrypt n k ct)).length ≤ decBound n ct)
    (request : Unit × List Bool) :
    (OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
        (E.oneTimeCCAOracle n k bit))
      (hybridDEMHandler E decaps decBound n sk ctK request)).run [ctD] =
      pure (if request.2 == encPair encBits encBits (ctK, ctD) then [] else
        encOption encBits (hybridDecrypt
          (fun n sk ct => if ct == ctK then some k else decaps n sk ct)
          E.decrypt n sk request.2), [ctD]) := by
  by_cases hc : encPair encBits encBits (unframe request.2, dropFrame request.2) = request.2
  · by_cases hk : unframe request.2 = ctK
    · have heq : request.2 = encPair encBits encBits (ctK, ctD) ↔
          dropFrame request.2 = ctD := by
        rw [← hc, (encPair encBits encBits).injective.eq_iff, Prod.mk.injEq, hk]
        simp
      have hc' : encPair encBits encBits (ctK, dropFrame request.2) = request.2 := by
        simpa only [hk] using hc
      simp only [hybridDEMHandler, hybridDecrypt, beq_iff_eq, hk, hc', ↓reduceIte,
        OracleComp.interpret_map, ProbOracleComp.interpret_query, heq, StateT.run_map]
      dsimp only [StateT.run, SymmetricCipher.oneTimeCCAOracle]
      by_cases hd : dropFrame request.2 = ctD
      · simp [hd]
      · simp [hd, List.take_of_length_le (hbound _)]
    · have hne : request.2 ≠ encPair encBits encBits (ctK, ctD) :=
        fun h => hk ((congrArg unframe h).trans (unframe_encPair_encBits _ _ _))
      simp only [hybridDEMHandler, hybridDecrypt, beq_iff_eq, hc, hk, hne, ↓reduceIte,
        OracleComp.interpret_pure, StateT.run_pure]
  · have hne : request.2 ≠ encPair encBits encBits (ctK, ctD) := fun h => hc (by simp [h])
    simp only [hybridDEMHandler, hybridDecrypt, beq_iff_eq, hc, hne, ↓reduceIte,
      OracleComp.interpret_pure, StateT.run_pure, encOption_none]

private theorem eval_run_substituted_phase {α : Type}
    (oracle : Bool × List Bool → StateT (List (List Bool)) ProbComp (List Bool))
    (handler : Unit × List Bool → WordOracleComp Bool (List Bool))
    (reply : Unit × List Bool → List Bool) (state : List (List Bool))
    (hstep : ∀ request, (OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m)) oracle)
      (handler request)).run state = pure (reply request, state))
    (program : WordOracleComp Unit α) :
    ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m)) oracle)
      (ProbOracleComp.simulate handler program)).run state) =
      (ProbComp.eval ((OracleComp.interpret
        (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
          (fun request (s : Unit) => pure (reply request, s))) program).run ())).map
            (fun result => (result.1, state)) := by
  have hsim := ProbOracleComp.runWith_map_state
    (fun request (s : Unit) => PMF.pure (reply request, s))
    (fun request => ProbOracleComp.runWith (fun q s => ProbComp.eval (oracle q s))
      (handler request))
    (fun _ : Unit => state) (fun request s => by
      have h := congrArg ProbComp.eval (hstep request)
      simpa only [runWith_norm, pmf_norm] using h.symm) program ()
  simpa only [runWith_norm, pmf_norm] using hsim.symm

private theorem eval_run_hybridDEMContinuation (E : SymmetricCipher)
    (decaps : ℕ → List Bool → List Bool → Option (List Bool))
    (ctBound : ℕ → ℕ) (decBound : ℕ → List Bool → ℕ)
    (adversary : WordCCA2Adversary) (bit : Bool) (n : ℕ) (pk sk ctK k : List Bool)
    (hct : ∀ msg, msg.length = n → ∀ ct ∈ (ProbComp.eval (E.encrypt n k msg)).support,
      ct.length ≤ ctBound n)
    (hdec : ∀ ct, (encOption encBits (E.decrypt n k ct)).length ≤ decBound n ct) :
    ProbComp.eval (do
      let out ← (OracleComp.interpret
        (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
          (E.oneTimeCCAOracle n k bit))
        (hybridDEMContinuation E decaps ctBound decBound adversary n pk sk ctK)).run []
      return out.1) =
    ProbComp.eval (cca2GameOn (fun n _ m0 m1 => (m0.length == n) && (m1.length == n))
      encBits (fun _ => pure (pk, sk))
      (fun n _ msg => (fun ct => encPair encBits encBits (ctK, ct)) <$> E.encrypt n k msg)
      (hybridDecrypt (fun n sk ct => if ct == ctK then some k else decaps n sk ct) E.decrypt)
      adversary bit n) := by
  let decrypt := hybridDecrypt
    (fun n sk ct => if ct == ctK then some k else decaps n sk ct) E.decrypt
  have hchoose := eval_run_substituted_phase (E.oneTimeCCAOracle n k bit)
    (hybridDEMHandler E decaps decBound n sk ctK)
    (fun request => encOption encBits (decrypt n sk request.2)) []
    (run_hybridDEMHandler_before E decaps decBound n sk ctK k bit hdec)
    (adversary.choose n pk)
  simp only [pmf_norm, hybridDEMContinuation, cca2GameOn, OracleComp.interpret_bind,
    StateT.run_bind]
  rw [hchoose]
  simp only [pmf_norm]
  apply PMF.bind_congr_on_support
  intro choice hchoice
  by_cases hvalid : ((ChoiceOut.msg₀ choice.1).length == n &&
      (ChoiceOut.msg₁ choice.1).length == n) = true
  · simp only [pmf_norm, hvalid, ↓reduceIte, OracleComp.interpret_bind, StateT.run_bind,
      OracleComp.interpret_map, ProbOracleComp.interpret_query, StateT.run_map]
    have henc : (E.oneTimeCCAOracle n k bit
        (false, encPair encBits encBits
          (ChoiceOut.msg₀ choice.1, ChoiceOut.msg₁ choice.1))).run [] =
        (do let ct ← E.encrypt n k
              (if bit then ChoiceOut.msg₁ choice.1 else ChoiceOut.msg₀ choice.1)
            return (ct, [ct])) := by
      simp [StateT.run, SymmetricCipher.oneTimeCCAOracle, encPair_apply, encBits_apply,
        unframe_frame_append, dropFrame_frame_append, hvalid]
    rw [henc]
    simp only [pmf_norm]
    apply PMF.bind_congr_on_support
    intro ct hmem
    have hlen : (if bit then ChoiceOut.msg₁ choice.1 else ChoiceOut.msg₀ choice.1).length = n := by
      simp only [Bool.and_eq_true, beq_iff_eq] at hvalid
      cases bit <;> simp [hvalid]
    rw [List.take_of_length_le (hct _ hlen ct hmem)]
    have hguess := eval_run_substituted_phase (E.oneTimeCCAOracle n k bit)
      (hybridDEMHandler E decaps decBound n sk ctK)
      (fun request => if request.2 == encPair encBits encBits (ctK, ct) then [] else
        encOption encBits (decrypt n sk request.2)) [ct]
      (run_hybridDEMHandler_after E decaps decBound n sk ctK k ct bit hdec)
      (adversary.guess n (ChoiceOut.state choice.1) (encPair encBits encBits (ctK, ct)))
    rw [hguess]
    simp only [PMF.bind_map, Function.comp_def]
    congr 5
    funext request s
    unfold cca2Phase2Oracle
    split_ifs <;> rfl
  · simp only [hvalid]
    change (PMF.pure (false, ([] : List (List Bool)))).bind (fun a => PMF.pure a.1) = _
    exact PMF.pure_bind _ _

/-- Exact, loss-one DEM game identity. Bounds apply only to keys in the actual symmetric key
sampler's support and to valid `n`-bit encryption inputs. Neither uniform encoded keys nor KEM
correctness is assumed for this intermediate-game identity. -/
theorem eval_hybridDEMGame (E : SymmetricCipher)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (decaps : ℕ → List Bool → List Bool → Option (List Bool))
    (ctBound : ℕ → ℕ) (decBound : ℕ → List Bool → ℕ)
    (adversary : WordCCA2Adversary) (bit : Bool) (n : ℕ)
    (hct : E.CiphertextLengthLE n (ctBound n))
    (hdec : ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ ct, (encOption encBits (E.decrypt n k ct)).length ≤ decBound n ct) :
    ProbComp.eval (hybridDEMGame E keyGen encaps decaps adversary bit n) =
      ProbComp.eval (E.ccaOneTimeGame
        (hybridToOneTimeCCAAdversary E keyGen encaps decaps ctBound decBound adversary) bit n) := by
  symm
  simp only [hybridDEMGame, SymmetricCipher.ccaOneTimeGame, hybridToOneTimeCCAAdversary,
    runWith_norm, pmf_norm]
  rw [PMF.bind_comm]
  apply PMF.bind_congr_on_support
  intro keys _
  rw [PMF.bind_comm]
  apply PMF.bind_congr_on_support
  intro encapsulated _
  apply PMF.bind_congr_on_support
  intro k hk
  simpa only [ProbComp.eval_bind, ProbComp.eval_pure,
    ProbOracleComp.eval_run_interpret_eq_runWith] using
    eval_run_hybridDEMContinuation E decaps ctBound decBound adversary bit n keys.1 keys.2
      encapsulated.2 k (hct k hk) (hdec k hk)

@[local fun_prop]
private theorem computableInPolyTime_hybridDecrypt_comp {Msg α : Type}
    {encMsg : Msg ↪ List Bool} {input : α ↪ List Bool}
    {decaps : ℕ → List Bool → List Bool → Option (List Bool)}
    {decryptSym : ℕ → List Bool → List Bool → Option Msg}
    (hdecaps : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool =>
      decaps p.1 p.2.1 p.2.2) (encKeyedInput encBits) (encOption encBits))
    (hdecryptSym : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool =>
      decryptSym p.1 p.2.1 p.2.2) (encKeyedInput encBits) (encOption encMsg))
    {n : α → ℕ} {sk ct : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hsk : ComputableInPolyTime sk input encBits)
    (hct : ComputableInPolyTime ct input encBits) :
    ComputableInPolyTime (fun a => hybridDecrypt decaps decryptSym (n a) (sk a) (ct a))
      input (encOption encMsg) :=
  (computableInPolyTime_hybridDecrypt hdecaps hdecryptSym).comp (hn.prod (hsk.prod hct))

/-- Native bounded-read implementation of the canonical forwarding handler. -/
@[fun_prop]
theorem isOraclePPTOn_hybridDEMHandler (E : SymmetricCipher)
    {decaps : ℕ → List Bool → List Bool → Option (List Bool)}
    (hdecaps : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool =>
      decaps p.1 p.2.1 p.2.2) (encKeyedInput encBits) (encOption encBits))
    {decBound : ℕ → List Bool → ℕ}
    (hdecBound : ComputableInPolyTime (fun p : ℕ × List Bool => decBound p.1 p.2)
      (encPair encUnary encBits) encUnary)
    {α : Type} {input : α ↪ List Bool} {n : α → ℕ} {sk ctK request : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hsk : ComputableInPolyTime sk input encBits)
    (hctK : ComputableInPolyTime ctK input encBits)
    (hrequest : ComputableInPolyTime request input encBits) :
    IsOraclePPTOn input encBits (fun a =>
      hybridDEMHandler E decaps decBound (n a) (sk a) (ctK a) ((), request a)) := by
  have := E.decrypt_polyTime
  ppt [hybridDEMHandler]

@[local fun_prop]
private theorem isOraclePPTOn_hybridDEMInterpret (E : SymmetricCipher)
    {decaps : ℕ → List Bool → List Bool → Option (List Bool)}
    (hdecaps : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool =>
      decaps p.1 p.2.1 p.2.2) (encKeyedInput encBits) (encOption encBits))
    {decBound : ℕ → List Bool → ℕ}
    (hdecBound : ComputableInPolyTime (fun p : ℕ × List Bool => decBound p.1 p.2)
      (encPair encUnary encBits) encUnary)
    {α β : Type} {input : α ↪ List Bool} {output : β ↪ List Bool}
    {n : α → ℕ} {sk ctK : α → List Bool} {program : α → WordOracleComp Unit β}
    (hn : ComputableInPolyTime n input encUnary)
    (hsk : ComputableInPolyTime sk input encBits)
    (hctK : ComputableInPolyTime ctK input encBits)
    (hprogram : IsOraclePPTOn input output program) :
    IsOraclePPTOn input output (fun a => ProbOracleComp.simulate
      (hybridDEMHandler E decaps decBound (n a) (sk a) (ctK a)) (program a)) := by
  have := E.decrypt_polyTime
  have hhandler : IsOraclePPTOn (encPair input (encPair (encFinEnum Unit) encBits)) encBits
      (fun p : α × (Unit × List Bool) =>
        hybridDEMHandler E decaps decBound (n p.1) (sk p.1) (ctK p.1) p.2) :=
    isOraclePPTOn_hybridDEMHandler E hdecaps hdecBound
      (by polytime) (by polytime) (by polytime) (by polytime)
  let resources := fun (a : α) (ct : List Bool) => decBound (n a) (dropFrame ct) +
    (encOption encBits (hybridDecrypt decaps E.decrypt (n a) (sk a) ct)).length
  have hres : ComputableInPolyTime (fun p : α × List Bool => resources p.1 p.2)
      (encPair input encBits) encUnary := by
    polytime [resources]
  simp only [ProbOracleComp.simulate, OracleComp.substitute_eq_interpret]
  apply hprogram.interpret_preprocess_open' ComputableInPolyTime.id' hhandler hres
  intro a request reply hreply
  unfold hybridDEMHandler at hreply
  split_ifs at hreply
  · obtain ⟨raw, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hreply
    exact (List.length_take_le _ _).trans (Nat.le_add_right _ _)
  · cases OracleComp.eq_of_mem_supportWith_pure hreply
    exact Nat.le_add_left _ _
  · cases OracleComp.eq_of_mem_supportWith_pure hreply
    exact Nat.zero_le _

/-- Native implementation of both phases with a captured KEM environment. External replies
are read only up to the supplied unary-computable limits. -/
theorem isOraclePPTOn_hybridDEMContinuation (E : SymmetricCipher)
    {decaps : ℕ → List Bool → List Bool → Option (List Bool)}
    (hdecaps : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool =>
      decaps p.1 p.2.1 p.2.2) (encKeyedInput encBits) (encOption encBits))
    {ctBound : ℕ → ℕ} (hctBound : ComputableInPolyTime ctBound encUnary encUnary)
    {decBound : ℕ → List Bool → ℕ}
    (hdecBound : ComputableInPolyTime (fun p : ℕ × List Bool => decBound p.1 p.2)
      (encPair encUnary encBits) encUnary)
    {adversary : WordCCA2Adversary} (hA : adversary.IsPPT)
    {α : Type} {input : α ↪ List Bool} {n : α → ℕ} {pk sk ctK : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hpk : ComputableInPolyTime pk input encBits)
    (hsk : ComputableInPolyTime sk input encBits)
    (hctK : ComputableInPolyTime ctK input encBits) :
    IsOraclePPTOn input encBool (fun a =>
      hybridDEMContinuation E decaps ctBound decBound adversary (n a) (pk a) (sk a) (ctK a)) := by
  have ⟨hchoose, hguess⟩ := hA
  have hchooseOn := hchoose.on
  ppt [hybridDEMContinuation]

attribute [local fun_prop] isOraclePPTOn_hybridDEMContinuation

/-- The complete reduction is uniform strict oracle PPT. Key generation, encapsulation,
local decapsulation/decryption, both adaptive phases, and bounded external reads are charged. -/
theorem isOraclePPT_hybridToOneTimeCCAAdversary (E : SymmetricCipher)
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encaps : ℕ → List Bool → ProbComp (List Bool × List Bool)}
    {decaps : ℕ → List Bool → List Bool → Option (List Bool)}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencaps : IsPPTOn (encPair encUnary encBits) (encPair encBits encBits)
      (fun p => encaps p.1 p.2))
    (hdecaps : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool =>
      decaps p.1 p.2.1 p.2.2) (encKeyedInput encBits) (encOption encBits))
    {ctBound : ℕ → ℕ} (hctBound : ComputableInPolyTime ctBound encUnary encUnary)
    {decBound : ℕ → List Bool → ℕ}
    (hdecBound : ComputableInPolyTime (fun p : ℕ × List Bool => decBound p.1 p.2)
      (encPair encUnary encBits) encUnary)
    {adversary : WordCCA2Adversary} (hA : adversary.IsPPT) :
    IsOraclePPT encBool
      (hybridToOneTimeCCAAdversary E keyGen encaps decaps ctBound decBound adversary) := by
  ppt [hybridToOneTimeCCAAdversary]

/-- The intermediate game itself has a uniform strict-PPT realization, including the hidden
symmetric key sampler and every adaptive decryption reply. -/
@[program_certificate]
theorem isPPTOn_hybridDEMGame (E : SymmetricCipher)
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encaps : ℕ → List Bool → ProbComp (List Bool × List Bool)}
    {decaps : ℕ → List Bool → List Bool → Option (List Bool)}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencaps : IsPPTOn (encPair encUnary encBits) (encPair encBits encBits)
      (fun p => encaps p.1 p.2))
    (hdecaps : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool =>
      decaps p.1 p.2.1 p.2.2) (encKeyedInput encBits) (encOption encBits))
    {adversary : WordCCA2Adversary} (hA : adversary.IsPPT) (bit : Bool) :
    IsPPTOn encUnary encBool (hybridDEMGame E keyGen encaps decaps adversary bit) := by
  obtain ⟨ctBound, hctPoly, hct⟩ := E.exists_ciphertext_length_bound_of_length_eq
  obtain ⟨decBound, hdecPoly, hdec⟩ := E.exists_decryption_length_bound
  have hrun := E.isPPTOn_ccaOneTimeGame
    (isOraclePPT_hybridToOneTimeCCAAdversary E hkeyGen hencaps hdecaps hctPoly hdecPoly hA) bit
  exact hrun.congr fun n =>
    (eval_hybridDEMGame E keyGen encaps decaps ctBound decBound adversary bit n
      (hct n) (hdec n)).symm

/-- One-time symmetric CCA security of `E` makes the two DEM intermediate games `hybridDEMGame`
indistinguishable with loss one: the DEM hop toward [BonehShoup2023], Exercise 12.5(a), not the
cited result, which also needs the two KEM hops (#5293, #5686).

`Cslib.Crypto.Encryption.hybrid_indcca2On` composes this hop with the two KEM hops. The source's
1CCA security (Definition 9.6, printed p. 363) rests on Attack Game 9.2, whose decryption queries
lie in the ciphertext space `C` (printed p. 362). Here `SymmetricCipher.ctSpace` represents `C`,
and `decrypt_eq_none_of_ctSpace_eq_false` forces rejection (`[] = encOption encBits none`) on words
outside `C`; when `E.ctSpace` is efficiently recognizable, an adversary can simulate those
rejections itself, so `OneTimeINDCCA` matches the source's 1CCA game on `C`. Note that `ctSpace`
defaults to `fun _ _ => true` (accepting every word) unless specialized on a cipher. -/
theorem _root_.Cslib.Crypto.SymmetricCipher.OneTimeINDCCA.indistinguishable_hybridDEMGame
    {E : SymmetricCipher} (hsecure : E.OneTimeINDCCA)
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encaps : ℕ → List Bool → ProbComp (List Bool × List Bool)}
    {decaps : ℕ → List Bool → List Bool → Option (List Bool)}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencaps : IsPPTOn (encPair encUnary encBits) (encPair encBits encBits)
      (fun p => encaps p.1 p.2))
    (hdecaps : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool =>
      decaps p.1 p.2.1 p.2.2) (encKeyedInput encBits) (encOption encBits)) :
    Game.Indistinguishable
      (fun A n => ProbComp.eval (hybridDEMGame E keyGen encaps decaps A false n))
      (fun A n => ProbComp.eval (hybridDEMGame E keyGen encaps decaps A true n))
      WordCCA2Adversary.IsPPT := by
  intro adversary hA
  obtain ⟨ctBound, hctPoly, hct⟩ := E.exists_ciphertext_length_bound_of_length_eq
  obtain ⟨decBound, hdecPoly, hdec⟩ := E.exists_decryption_length_bound
  have h := hsecure (hybridToOneTimeCCAAdversary E keyGen encaps decaps ctBound decBound adversary)
    (isOraclePPT_hybridToOneTimeCCAAdversary E hkeyGen hencaps hdecaps hctPoly hdecPoly hA)
  refine h.congr fun n => ?_
  dsimp only
  rw [eval_hybridDEMGame E keyGen encaps decaps ctBound decBound adversary false n (hct n) (hdec n),
    eval_hybridDEMGame E keyGen encaps decaps ctBound decBound adversary true n (hct n) (hdec n)]

end Cslib.Crypto.Encryption
