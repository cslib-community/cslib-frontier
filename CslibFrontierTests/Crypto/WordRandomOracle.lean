/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.Signature.WordRandomOracle
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Probability.PMF.Bind

/-! Actual native word forgers, shared signing/hash caches, freshness, and off-support tapes. -/

namespace CslibFrontierTests.Crypto.WordRandomOracle

open Cslib Cslib.Probability Cslib.Crypto.Protocols.ROMSignature
open Turing Turing.MultiTapeTM Turing.MultiTapePTM

private def machine : MultiTapePTM 0 Bool Bool Bool where
  initial := false
  tr state _ _ answer bit := if state then
    .step { inputTape := 0, workTapes := Fin.elim0, output := answer true, state := none }
      (fun _ => none) (fun _ => 0)
    else .query bit true

private def audit : (q : List Bool ⊕ List Bool) →
    StateT (List (List Bool ⊕ List Bool)) Id
      (ForgerSpec (List Bool) (List Bool) (List Bool) Bool q)
  | .inl word, log => (word, log ++ [.inl word])
  | .inr word, log => (word.headD false, log ++ [.inr word])

-- A short word that is not a canonical pair encoding remains a distinct hash payload.
example : (OracleComp.interpret audit (do
    let _ ← wordQuery encBool true [true]
    let _ ← wordQuery encBool true []
    wordQuery encBool false [true])).run [] =
      ([true], [.inr [true], .inr [], .inl [true]]) := rfl

-- Oversized public keys make no calls, even with an arbitrarily overlong tape.
example (coins : List Bool) :
    (OracleComp.interpret audit
      ((savedCoinForger machine encBool 2 0 0 0 0).forge [true] coins)).run [] =
      (([], []), []) := rfl

-- An empty tape has no output. The existing total decoder handles that malformed pair word.
example : (OracleComp.interpret audit
    ((savedCoinForger machine encBool 2 0 0 0 0).forge [] [])).run [] =
      (([], []), []) := rfl

-- Extra saved bits are ignored at the original two-step cutoff; the selected query is retained.
example (more : List Bool) :
    (OracleComp.interpret audit
      ((savedCoinForger machine encBool 2 0 0 0 0).forge [] ([true, false] ++ more))).run [] =
      (([], []), [.inr []]) := rfl

example : (savedCoinForger machine encBool 2 0 0 0 0).CallBounded 2 2 :=
  callBounded_savedCoinForger machine encBool 2 0 0 0 0

-- The guarded, truncated and decoded replay has a certificate on the entire supplied triple.
example : IsOraclePPTOn (encPair encUnary (encPair encBits encBits)) (encPair encBits encBits)
    (savedWordReplay machine (fun op word => ProbOracleComp.query (op, word)) 2 0 0 0) := by
  fun_prop

private def interaction (fresh : Bool) :
    OracleComp (fun _ : Bool × List Bool => List Bool) (List Bool × List Bool) := do
  let signed ← List.take 1 <$> OracleComp.query (false, [])
  let signedAgain ← List.take 1 <$> OracleComp.query (false, [])
  let signedHash ← List.take 1 <$> OracleComp.query (true, [])
  let newHash ← List.take 1 <$> OracleComp.query (true, [true])
  let newHashAgain ← List.take 1 <$> OracleComp.query (true, [true])
  let stable := signed == signedAgain && signed == signedHash && newHash == newHashAgain
  return if stable then (if fresh then [true] else [], if fresh then newHash else signed)
    else ([], [])

private def nativeForger (fresh : Bool) (_ : ℕ) (_ : List Bool) :
    WordOracleComp Bool (List Bool × List Bool) := OracleComp.liftRight (interaction fresh)

private theorem nativeForger_ppt (fresh : Bool) :
    IsOraclePPT (encPair encBits encBits) (nativeForger fresh) := by
  unfold IsOraclePPT nativeForger interaction
  simp only [OracleComp.liftRight, OracleComp.interpret_bind, OracleComp.interpret_map,
    OracleComp.interpret_query, OracleComp.interpret_pure]
  change IsOraclePPTOn _ _ (fun _ => do
    let signed ← List.take 1 <$> ProbOracleComp.query (false, [])
    let signedAgain ← List.take 1 <$> ProbOracleComp.query (false, [])
    let signedHash ← List.take 1 <$> ProbOracleComp.query (true, [])
    let newHash ← List.take 1 <$> ProbOracleComp.query (true, [true])
    let newHashAgain ← List.take 1 <$> ProbOracleComp.query (true, [true])
    let stable := signed == signedAgain && signed == signedHash && newHash == newHashAgain
    return if stable then (if fresh then [true] else [], if fresh then newHash else signed)
      else ([], []))
  apply IsOraclePPTOn.bind_with (middle := encBits)
  · fun_prop
  apply IsOraclePPTOn.bind_with (middle := encBits)
  · fun_prop
  apply IsOraclePPTOn.bind_with (middle := encBits)
  · fun_prop
  apply IsOraclePPTOn.bind_with (middle := encBits)
  · fun_prop
  apply IsOraclePPTOn.bind_with (middle := encBits)
  · fun_prop
  cases fresh <;> dsimp only <;> fun_prop

private noncomputable def scheme :
    Scheme (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) Bool where
  keyGen := PMF.pure ([], [])
  SignCoins := Unit
  signCoins _ _ := PMF.pure ()
  sign _ msg _ := do
    let digest ← OracleComp.query msg
    return encBool digest
  verify _ msg sig := do
    let digest ← OracleComp.query msg
    return sig == encBool digest

private noncomputable def explicitForger (fresh : Bool) :
    Forger (List Bool) (List Bool) (List Bool) (List Bool) Bool where
  Coins := Unit
  coins := PMF.pure ()
  forge _ _ := OracleComp.interpret (fun q => wordQuery encBool q.1 q.2) (interaction fresh)

/-! A scheme with two valid signatures for one message separates the complete games. -/

private noncomputable def nonUniqueScheme :
    Scheme (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) Bool where
  keyGen := PMF.pure ([], [])
  SignCoins := Unit
  signCoins _ _ := PMF.pure ()
  sign _ _ _ := pure []
  verify _ _ sig := pure (sig == [] || sig == [true])

private def sameMessageNewSignatureInteraction :
    OracleComp (fun _ : Bool × List Bool => List Bool) (List Bool × List Bool) := do
  let _ ← OracleComp.query (false, [])
  return ([], [true])

private def sameMessageNewSignatureForger (_ : List Bool) :
    WordOracleComp Bool (List Bool × List Bool) :=
  OracleComp.liftRight sameMessageNewSignatureInteraction

private noncomputable def sameMessageNewSignatureExplicitForger :
    Forger (List Bool) (List Bool) (List Bool) (List Bool) Bool where
  Coins := Unit
  coins := PMF.pure ()
  forge _ _ := OracleComp.interpret (fun q => wordQuery encBool q.1 q.2)
    sameMessageNewSignatureInteraction

private def exactReplayInteraction :
    OracleComp (fun _ : Bool × List Bool => List Bool) (List Bool × List Bool) := do
  let sig ← OracleComp.query (false, [])
  return ([], sig)

private def exactReplayForger (_ : List Bool) :
    WordOracleComp Bool (List Bool × List Bool) :=
  OracleComp.liftRight exactReplayInteraction

private noncomputable def exactReplayExplicitForger :
    Forger (List Bool) (List Bool) (List Bool) (List Bool) Bool where
  Coins := Unit
  coins := PMF.pure ()
  forge _ _ := OracleComp.interpret (fun q => wordQuery encBool q.1 q.2) exactReplayInteraction

private theorem eufCmaGame_nonUniqueScheme_sameMessageNewSignatureExplicitForger :
    eufCmaGame nonUniqueScheme sameMessageNewSignatureExplicitForger = PMF.pure false := by
  simp only [eufCmaGame, nonUniqueScheme, sameMessageNewSignatureExplicitForger,
    sameMessageNewSignatureInteraction, wordQuery, OracleComp.interpret_bind,
    OracleComp.interpret_query, OracleComp.interpret_pure, StateT.run_bind, StateT.run_pure,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.pure_bind]
  simp [handler, StateT.run]

private theorem sufCmaGame_nonUniqueScheme_sameMessageNewSignatureExplicitForger :
    sufCmaGame nonUniqueScheme sameMessageNewSignatureExplicitForger = PMF.pure true := by
  unfold sufCmaGame
  simp only [nonUniqueScheme, sameMessageNewSignatureExplicitForger, PMF.pure_bind]
  rw [eval_world_worldRealize_liftOracleForger]
  simp [sameMessageNewSignatureInteraction, wordQuery, runLoggedForger, liftOracleForger,
    forgerWorldImpl, logSigning, StateT.run, sumHandler]

private theorem sufCmaGame_nonUniqueScheme_exactReplayExplicitForger :
    sufCmaGame nonUniqueScheme exactReplayExplicitForger = PMF.pure false := by
  unfold sufCmaGame
  simp only [nonUniqueScheme, exactReplayExplicitForger, PMF.pure_bind]
  rw [eval_world_worldRealize_liftOracleForger]
  simp [exactReplayInteraction, wordQuery, runLoggedForger, liftOracleForger,
    forgerWorldImpl, logSigning, StateT.run, sumHandler]

-- Signing and hashing share the cache, including after repeated signing and hash queries.
-- The fresh forgery succeeds; replaying a signed message is rejected despite valid verification.
private theorem eufCmaGame_scheme_explicitForger (fresh : Bool) :
    eufCmaGame scheme (explicitForger fresh) = PMF.pure fresh := by
  simp only [eufCmaGame, scheme, explicitForger, interaction, wordQuery,
    OracleComp.interpret_bind, OracleComp.interpret_query, OracleComp.interpret_map,
    OracleComp.interpret_pure, StateT.run_bind, StateT.run_pure, StateT.run_map,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.monad_map_eq_map, PMF.pure_bind]
  simp only [handler, oracle, OracleComp.interpret_bind, OracleComp.interpret_query,
    OracleComp.interpret_pure, StateT.run_bind, StateT.run_pure,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.pure_bind, PMF.bind_bind]
  cases fresh <;> simp [memoize, StateT.run, encBool_apply, PMF.bind_bind, List.lookup_cons,
    Bool.beq_eq_decide_eq]

-- The actual native program's game `wordEufCmaGame` is that same existing typed game.
private theorem wordEufCmaGame_scheme_nativeForger (fresh : Bool) (n : ℕ) :
    wordEufCmaGame encBool scheme (nativeForger fresh n) =
      eufCmaGame scheme (explicitForger fresh) := by
  rw [eufCmaGame_eq_worldGame]
  simp only [wordEufCmaGame, worldGame, scheme, explicitForger, PMF.monad_bind_eq_bind,
    PMF.pure_bind]
  congr 2 with verified msig pairs : 3
  simp only [List.contains_eq_mem]
  congr 2
  exact decide_eq_decide.mpr Iff.rfl

-- A valid signature on the fresh message `[true]` wins the complete native EUF-CMA game.
example (n : ℕ) : wordEufCmaGame encBool scheme (nativeForger true n) = PMF.pure true :=
  (wordEufCmaGame_scheme_nativeForger true n).trans (eufCmaGame_scheme_explicitForger true)

-- The native strong game uses the same execution as the typed strong game and changes only the
-- final freshness predicate from fresh message to fresh pair.
example (fresh : Bool) (n : ℕ) :
    wordSufCmaGame encBool scheme (nativeForger fresh n) =
      sufCmaGame scheme (explicitForger fresh) := by
  simp only [wordSufCmaGame, sufCmaGame, worldGame, scheme, explicitForger,
    PMF.monad_bind_eq_bind, PMF.pure_bind]
  congr 2 with verified msig pairs : 3
  simp only [List.contains_eq_mem]
  congr 2
  exact decide_eq_decide.mpr Iff.rfl

-- Message freshness implies pair freshness on the same transcript, hence the concrete native
-- EUF-CMA probability never exceeds its SUF-CMA probability.
example (fresh : Bool) (n : ℕ) :
    Game.succProbability (wordEufCmaGame encBool scheme (nativeForger fresh n)) ≤
      Game.succProbability (wordSufCmaGame encBool scheme (nativeForger fresh n)) :=
  succProbability_wordEufCmaGame_le_wordSufCmaGame encBool scheme (nativeForger fresh n)

private theorem wordEufCmaGame_nonUniqueScheme_sameMessageNewSignatureForger :
    wordEufCmaGame encBool nonUniqueScheme sameMessageNewSignatureForger =
      eufCmaGame nonUniqueScheme sameMessageNewSignatureExplicitForger := by
  rw [eufCmaGame_eq_worldGame]
  simp only [wordEufCmaGame, worldGame, nonUniqueScheme,
    sameMessageNewSignatureForger, sameMessageNewSignatureExplicitForger,
    PMF.monad_bind_eq_bind, PMF.pure_bind]
  congr 2 with verified msig pairs : 3
  simp only [List.contains_eq_mem]
  congr 2
  exact decide_eq_decide.mpr Iff.rfl

private theorem wordSufCmaGame_nonUniqueScheme_sameMessageNewSignatureForger :
    wordSufCmaGame encBool nonUniqueScheme sameMessageNewSignatureForger =
      sufCmaGame nonUniqueScheme sameMessageNewSignatureExplicitForger := by
  simp only [wordSufCmaGame, sufCmaGame, worldGame, nonUniqueScheme,
    sameMessageNewSignatureForger, sameMessageNewSignatureExplicitForger,
    PMF.monad_bind_eq_bind, PMF.pure_bind]
  congr 2 with verified msig pairs : 3
  simp only [List.contains_eq_mem]
  congr 2
  exact decide_eq_decide.mpr Iff.rfl

-- The forger asks the signer for `([], [])`, then returns the distinct valid pair `([], [true])`:
-- it loses the complete native EUF-CMA game but wins the complete native SUF-CMA game.
example : wordEufCmaGame encBool nonUniqueScheme sameMessageNewSignatureForger =
    PMF.pure false :=
  wordEufCmaGame_nonUniqueScheme_sameMessageNewSignatureForger.trans
    eufCmaGame_nonUniqueScheme_sameMessageNewSignatureExplicitForger

example : wordSufCmaGame encBool nonUniqueScheme sameMessageNewSignatureForger =
    PMF.pure true :=
  wordSufCmaGame_nonUniqueScheme_sameMessageNewSignatureForger.trans
    sufCmaGame_nonUniqueScheme_sameMessageNewSignatureExplicitForger

private theorem wordSufCmaGame_nonUniqueScheme_exactReplayForger :
    wordSufCmaGame encBool nonUniqueScheme exactReplayForger =
      sufCmaGame nonUniqueScheme exactReplayExplicitForger := by
  simp only [wordSufCmaGame, sufCmaGame, worldGame, nonUniqueScheme, exactReplayForger,
    exactReplayExplicitForger, PMF.monad_bind_eq_bind, PMF.pure_bind]
  congr 2 with verified msig pairs : 3
  simp only [List.contains_eq_mem]
  congr 2
  exact decide_eq_decide.mpr Iff.rfl

-- Returning the exact pair received from signing loses the complete native SUF-CMA game.
example : wordSufCmaGame encBool nonUniqueScheme exactReplayForger = PMF.pure false :=
  wordSufCmaGame_nonUniqueScheme_exactReplayForger.trans
    sufCmaGame_nonUniqueScheme_exactReplayExplicitForger

-- The final bridge applies to actual key generation and an actual efficient oracle forger. The
-- strict-PPT key generator bounds its supported public keys through `IsPPTOn.length_le`.
example (fresh : Bool) : ∃ (k : ℕ) (Control : Type) (_ : Finite Control)
    (replay : MultiTapePTM k Bool Control Bool) (c d keyC keyD : ℕ),
    ∀ n, wordEufCmaGame encBool scheme (nativeForger fresh n) =
      eufCmaGame scheme (savedCoinForger replay encBool c d keyC keyD n) := by
  have hgen : IsPPTOn encUnary (encPair encBits encBits)
      (fun _ => (pure ([], []) : ProbComp (List Bool × List Bool))) := by fun_prop
  obtain ⟨keyC, keyD, hkeys⟩ := hgen.length_le
  have hbound (n : ℕ) (keys : List Bool × List Bool)
      (hmem : keys ∈ (ProbComp.eval (pure ([], []) : ProbComp (List Bool × List Bool))).support) :
      keys.1.length ≤ keyC * (n + 1) ^ keyD := by
    have hk := hkeys n keys hmem
    simp only [encUnary_apply, List.length_replicate] at hk
    exact (length_le_encPair_left encBits encBits keys).trans hk
  obtain ⟨k, Control, hfinite, replay, c, d, _, hgame⟩ :=
    exists_eufCmaGame_savedCoinForger (gen := fun _ => pure ([], [])) hbound
      (nativeForger_ppt fresh)
  exact ⟨k, Control, hfinite, replay, c, d, keyC, keyD, fun n =>
    (hgame n Bool encBool scheme rfl).2⟩

-- The same guarded, total-decoding adapter is exact for the fresh-pair game, with separate
-- signing and hash bounds in `Forger.CallBounded`.
example (fresh : Bool) : ∃ (k : ℕ) (Control : Type) (_ : Finite Control)
    (replay : MultiTapePTM k Bool Control Bool) (c d keyC keyD : ℕ),
    ∀ n, wordSufCmaGame encBool scheme (nativeForger fresh n) =
      sufCmaGame scheme (savedCoinForger replay encBool c d keyC keyD n) := by
  have hgen : IsPPTOn encUnary (encPair encBits encBits)
      (fun _ => (pure ([], []) : ProbComp (List Bool × List Bool))) := by fun_prop
  obtain ⟨keyC, keyD, hkeys⟩ := hgen.length_le
  have hbound (n : ℕ) (keys : List Bool × List Bool)
      (hmem : keys ∈ (ProbComp.eval (pure ([], []) : ProbComp (List Bool × List Bool))).support) :
      keys.1.length ≤ keyC * (n + 1) ^ keyD := by
    have hk := hkeys n keys hmem
    simp only [encUnary_apply, List.length_replicate] at hk
    exact (length_le_encPair_left encBits encBits keys).trans hk
  obtain ⟨k, Control, hfinite, replay, c, d, _, hgame⟩ :=
    exists_sufCmaGame_savedCoinForger (gen := fun _ => pure ([], [])) hbound
      (nativeForger_ppt fresh)
  exact ⟨k, Control, hfinite, replay, c, d, keyC, keyD, fun n =>
    (hgame n Bool encBool scheme rfl).2⟩

end CslibFrontierTests.Crypto.WordRandomOracle
