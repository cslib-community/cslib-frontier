/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

import CslibFrontier.Crypto.Computational.CollisionResistant
import CslibFrontier.Crypto.Computational.IndexedSignature
import CslibFrontier.Crypto.Computational.IndexedSignature.Counter
import CslibFrontier.Crypto.Computational.MAC
import CslibFrontier.Crypto.Computational.MAC.Counter
import CslibFrontier.Crypto.Computational.Signature.WordRandomOracle
import CslibFrontier.Crypto.Computational.TargetCollisionResistant
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Tactic.PPT
import CslibFrontier.Tactic.PolyTime
import CslibFrontierTests.Crypto.KeyedHashFixture

set_option linter.privateModule false

/-!
# Non-vacuity witnesses for hashing, nonce MAC, indexed signature, and ROM signature assumptions

Ordinary `module` test suite supplying refutation non-vacuity checks for:

1. **`CollisionResistantOn`, `CompressionFamily`, and `HashFamily`** (`CollisionResistant.lean`):
   * `zeroHash k _ := List.replicate k.length false` satisfies the deterministic polytime and
     digest-length specifications yet refutes `CollisionResistantOn` (whenever `[false]` and
     `[true]` are valid), `HashFamily`, and `CompressionFamily`.
2. **`KeyedHashFamily.TargetCollisionResistant`** (`TargetCollisionResistant.lean`):
   * Reuses `CslibFrontierTests.Crypto.zeroKeyedHashFamily` to refute `TargetCollisionResistant`.
3. **`NonceMACScheme.EUFCMA`, `NonceMACScheme.SUFCMA`, `NonceMACScheme.CounterSUFCMA`**
   (`MAC.lean`, `MAC/Counter.lean`):
   * `trivialNonceMAC` satisfies `verify_sign` (and rejects `[true]`) while failing `EUFCMA`,
     `SUFCMA`, and `CounterSUFCMA` via a zero-query PPT forger.
4. **`IndexedSignatureScheme.CounterEUFCMA`** (`IndexedSignature/Counter.lean`):
   * `trivialIndexedSig` satisfies `verify_sign` (and rejects `[true]`) while failing
     `CounterEUFCMA`.
5. **`Protocols.ROMSignature.EUFCMA` and `Protocols.ROMSignature.SUFCMA`**
   (`Signature/WordRandomOracle.lean`):
   * `trivialROMScheme` satisfies `ROMSignature.Scheme.Correct` (so it is not vacuously
     always-rejecting) while failing both `EUFCMA` and `SUFCMA`.
-/

namespace CslibFrontierTests.Crypto.HashAndAuthNonvacuity

open Cslib Cslib.Probability Cslib.Crypto Turing.MultiTapeTM
open Cslib.Crypto.Protocols
open scoped NNReal

private theorem succProbability_pure_true : Game.succProbability (PMF.pure true) = 1 := by
  simp [Game.succProbability]

/-! ### 1. `CollisionResistantOn`, `CompressionFamily`, and `HashFamily` -/

/-- Keyed constant-zero compression/hash family: maps every input to `0^{k.length}`. -/
private def zeroHash (k _ : List Bool) : List Bool :=
  List.replicate k.length false

theorem polyTime_zeroHash :
    ComputableInPolyTime (fun p : List Bool × List Bool => zeroHash p.1 p.2)
      (encPair encBits encBits) encBits := by
  have hk : ComputableInPolyTime (fun p : List Bool × List Bool => p.1)
      (encPair encBits encBits) encBits := by fun_prop
  exact (ComputableInPolyTime.bitsReplicate false).comp hk.length_bits_comp

theorem length_eq_zeroHash (k msg : List Bool) :
    (zeroHash k msg).length = k.length :=
  List.length_replicate

/-- `zeroHash` fails `CollisionResistantOn zeroHash valid` whenever `[false]` and `[true]` are
accepted at every security parameter. -/
theorem not_collisionResistantOn_zero {valid : ℕ → List Bool → Bool}
    (hv₀ : ∀ n, valid n [false] = true) (hv₁ : ∀ n, valid n [true] = true) :
    ¬ CollisionResistantOn zeroHash valid := by
  have finderPPT : IsPPT (encPair encBits encBits)
      (fun _ _ => (pure ([false], [true]) : ProbComp (List Bool × List Bool))) :=
    (ComputableInPolyTime.const ([false], [true])).isPPTOn.isPPT
  refine not_collisionResistantOn_of_le_succProbability one_ne_zero
    (fun _ _ => pure ([false], [true])) finderPPT fun n => ?_
  have heval :
      ProbComp.eval (collisionGame zeroHash valid (fun _ _ => pure ([false], [true])) n) =
        PMF.pure true := by
    have hbne : ([false] : List Bool) != [true] := rfl
    simp [collisionGame, isCollision, zeroHash, hv₀ n, hv₁ n, hbne,
      PMF.map, Function.comp_def, PMF.bind_const]
  simp only [heval, succProbability_pure_true, le_refl]

/-- `zeroHash` satisfies all deterministic fields of `HashFamily` yet is not a `HashFamily`. -/
theorem not_hashFamily_zero : ¬ HashFamily zeroHash :=
  fun hHash => not_collisionResistantOn_zero (fun _ => rfl) (fun _ => rfl) hHash.collisionResistant

/-- `zeroHash` satisfies all deterministic fields of `CompressionFamily` yet is not a
`CompressionFamily`. -/
theorem not_compressionFamily_zero : ¬ CompressionFamily zeroHash := by
  intro hComp
  let finder : CollisionFinder := fun n _ =>
    pure (List.replicate (2 * n) false, List.replicate (2 * n) true)
  have finderPPT : IsPPT (encPair encBits encBits) finder := by
    have hn : ComputableInPolyTime (fun p : ℕ × List Bool => 2 * p.1)
        (encPair encUnary encBits) encUnary := by polytime
    have hpair : ComputableInPolyTime
        (fun p : ℕ × List Bool => (List.replicate (2 * p.1) false, List.replicate (2 * p.1) true))
        (encPair encUnary encBits) (encPair encBits encBits) :=
      ((ComputableInPolyTime.bitsReplicate false).comp hn).prod
        ((ComputableInPolyTime.bitsReplicate true).comp hn)
    exact hpair.isPPTOn.isPPT
  have hneg := (hComp.collisionResistant.negligible finder finderPPT).shift 1
  have hone (n : ℕ) :
      Game.succProbability
        (ProbComp.eval (collisionGame zeroHash validCompressionInput finder (n + 1))) = 1 := by
    have hbne :
        (List.replicate (2 * (n + 1)) false != List.replicate (2 * (n + 1)) true) = true := by
      rw [bne_iff_ne]
      intro h
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega, List.replicate_succ,
        List.replicate_succ] at h
      exact Bool.noConfusion (List.cons.inj h).1
    have heval :
        ProbComp.eval (collisionGame zeroHash validCompressionInput finder (n + 1)) =
          PMF.pure true := by
      simp [collisionGame, finder, isCollision, zeroHash, validCompressionInput, hbne,
        PMF.map, Function.comp_def, PMF.bind_const]
    rw [heval]
    exact succProbability_pure_true
  simp only [hone] at hneg
  exact not_negligible_const one_ne_zero hneg

/-! ### 2. `KeyedHashFamily.TargetCollisionResistant` -/

private def constTCFinder : TargetCollisionFinder where
  choose _ := pure ([false], [])
  find _ _ _ := pure [true]

private theorem constTCFinder_isPPT : constTCFinder.IsPPT where
  choose := (ComputableInPolyTime.const ([false], ([] : List Bool))).isPPTOn
  find := (ComputableInPolyTime.const [true]).isPPTOn

/-- `zeroKeyedHashFamily` (from `CslibFrontierTests.Crypto.KeyedHashFixture`) is not target
collision-resistant. -/
theorem not_targetCollisionResistant_zeroKeyedHashFamily :
    ¬ zeroKeyedHashFamily.TargetCollisionResistant := by
  refine not_targetCollisionResistantOn_of_le_succProbability one_ne_zero
    constTCFinder constTCFinder_isPPT fun n => ?_
  have hbne : ([false] : List Bool) != [true] := rfl
  have heval :
      ProbComp.eval (targetCollisionGame zeroKeyedHashFamily.keyLen zeroKeyedHashFamily.eval
        (fun _ _ => true) constTCFinder n) = PMF.pure true := by
    simp [targetCollisionGame, constTCFinder, isCollision, zeroKeyedHashFamily_eval, hbne,
      PMF.map, Function.comp_def, PMF.bind_const]
  rw [heval, succProbability_pure_true]

/-! ### 3. `NonceMACScheme`: `EUFCMA`, `SUFCMA`, `CounterSUFCMA` -/

/-- Trivial complete `NonceMACScheme` accepting `tag = [false]` and rejecting all other tags. -/
private noncomputable def trivialNonceMAC : NonceMACScheme where
  msgLen _ := 1
  nonceLen _ := 1
  msgLen_polyTime := by polytime
  nonceLen_polyTime := by polytime
  keyGen _ := pure []
  sign _ _ _ := pure [false]
  verify _ _ _ tag := decide (tag = [false])
  keyGen_ppt := by ppt
  sign_ppt := by ppt
  verify_polyTime := by
    have htag : ComputableInPolyTime
        (fun p : List Bool × List Bool × List Bool × List Bool => p.2.2.2)
        (encPair encBits encBitsTriple) encBits := by fun_prop
    exact (ComputableInPolyTime.decide_eq' htag (ComputableInPolyTime.const [false])).of_enc_eq
      fun _ => rfl
  verify_sign _ _ _ _ _ _ _ tag htag := by
    simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at htag
    simp [htag]

example : trivialNonceMAC.verify [] [false] [false] [true] = false := rfl

private def constNonceForger : NonceMACForger :=
  fun _ _ => ProbOracleComp.sample (pure (([false], [false]), [false]))

private theorem constNonceForger_isOraclePPT :
    IsOraclePPT encNonceTaggedMessage constNonceForger :=
  (ComputableInPolyTime.const (([false], [false]), [false])).isPPTOn.isOraclePPTOn.isOraclePPT

/-- `trivialNonceMAC` fails `NonceMACScheme.EUFCMA`. -/
theorem not_nonceEufCma_trivialNonceMAC : ¬ trivialNonceMAC.EUFCMA := by
  intro hsec
  have hneg := hsec.negligible constNonceForger constNonceForger_isOraclePPT
  have heval (n : ℕ) :
      Game.succProbability (ProbComp.eval (trivialNonceMAC.eufCmaGame constNonceForger n)) = 1 := by
    simp [NonceMACScheme.eufCmaGame, trivialNonceMAC, constNonceForger, Game.succProbability]
  simp only [heval] at hneg
  exact not_negligible_const one_ne_zero hneg

/-- `trivialNonceMAC` fails `NonceMACScheme.SUFCMA`. -/
theorem not_nonceSufCma_trivialNonceMAC : ¬ trivialNonceMAC.SUFCMA :=
  fun h => not_nonceEufCma_trivialNonceMAC h.eufCma

/-- `trivialNonceMAC` fails `NonceMACScheme.CounterSUFCMA`. -/
theorem not_counterSufCma_trivialNonceMAC : ¬ trivialNonceMAC.CounterSUFCMA := by
  intro hsec
  have hneg := hsec.negligible constNonceForger constNonceForger_isOraclePPT
  have heval (n : ℕ) :
      Game.succProbability (ProbComp.eval (trivialNonceMAC.counterSufCmaGame constNonceForger n)) =
        1 := by
    simp [NonceMACScheme.counterSufCmaGame, trivialNonceMAC, constNonceForger, Game.succProbability]
  simp only [heval] at hneg
  exact not_negligible_const one_ne_zero hneg

/-! ### 4. `IndexedSignatureScheme.CounterEUFCMA` -/

/-- Trivial complete `IndexedSignatureScheme` with capacity `1` accepting `[false]`. -/
private noncomputable def trivialIndexedSig : IndexedSignatureScheme where
  capacity _ := 1
  keyGen _ := pure ([], [])
  sign _ _ _ := pure [false]
  verify _ _ _ sig := decide (sig = [false])
  capacity_polyTime := by polytime
  keyGen_ppt := by ppt
  sign_ppt := by ppt
  verify_polyTime := by
    have hsig : ComputableInPolyTime
        (fun p : List Bool × ℕ × List Bool × List Bool => p.2.2.2)
        (encPair encBits encIndexedSignedMessage) encBits := by fun_prop
    exact (ComputableInPolyTime.decide_eq' hsig (ComputableInPolyTime.const [false])).of_enc_eq
      fun _ => rfl
  verify_sign _ _ _ _ _ _ sig hsig := by
    simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hsig
    simp [hsig]

example : trivialIndexedSig.verify [] 0 [false] [true] = false := rfl

private def constIndexedForger : Forger :=
  fun _ _ => ProbOracleComp.sample (pure ([], encPair encUnary encBits (0, [false])))

private theorem constIndexedForger_isOraclePPT :
    IsOraclePPT (encPair encBits encBits) constIndexedForger :=
  (ComputableInPolyTime.const ([], encPair encUnary encBits (0, [false]))).isPPTOn
    |>.isOraclePPTOn.isOraclePPT

/-- `trivialIndexedSig` fails `IndexedSignatureScheme.CounterEUFCMA`. -/
theorem not_counterEufCma_trivialIndexedSig : ¬ trivialIndexedSig.CounterEUFCMA := by
  intro hsec
  have hneg := hsec.negligible constIndexedForger constIndexedForger_isOraclePPT
  have hdec : IndexedSignatureScheme.requestDecoder.decode [false, false] = (0, [false]) := by
    simpa using IndexedSignatureScheme.requestDecoder.decode_enc (0, [false])
  have heval (n : ℕ) :
      Game.succProbability
        (ProbComp.eval (trivialIndexedSig.counterEufCmaGame constIndexedForger n)) = 1 := by
    simp [IndexedSignatureScheme.counterEufCmaGame, IndexedSignatureScheme.counterVerify,
      trivialIndexedSig, constIndexedForger, hdec, Game.succProbability]
  simp only [heval] at hneg
  exact not_negligible_const one_ne_zero hneg

/-! ### 5. `Protocols.ROMSignature.EUFCMA` and `SUFCMA` -/

/-- Complete ROM signature scheme where honest signatures verify as `[false]` and `[true]` is
rejected. -/
private noncomputable def trivialROMScheme :
    ROMSignature.Scheme (List Bool) Unit (List Bool) (List Bool) (List Bool) Bool where
  keyGen := PMF.pure ([], ())
  SignCoins := Unit
  signCoins _ _ := PMF.pure ()
  sign _ _ _ := pure [false]
  verify _ _ sig := pure (decide (sig = [false]))

/-- `trivialROMScheme` satisfies `ROMSignature.Scheme.Correct` (not vacuously always-rejecting). -/
theorem trivialROMScheme_correct : trivialROMScheme.Correct := by
  intro keys _ m coins _ cache signed hsigned verified hverified
  simp only [trivialROMScheme, OracleComp.interpret_pure, StateT.run_pure,
    PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hsigned hverified
  rw [hverified, hsigned]
  rfl

example : trivialROMScheme.verify [] [false] [true] = pure false := rfl

private def constROMForger (_ : ℕ) (_ : List Bool) : WordOracleComp Bool (List Bool × List Bool) :=
  return ([], [false])

private theorem constROMForger_isOraclePPT :
    IsOraclePPT (encPair encBits encBits) constROMForger :=
  (ComputableInPolyTime.const ([], [false])).isPPTOn.isOraclePPTOn.isOraclePPT

/-- `trivialROMScheme` fails `ROMSignature.EUFCMA`. -/
theorem not_romSignature_eufCMA_trivial :
    ¬ ROMSignature.EUFCMA (fun _ => encBool) (fun _ => trivialROMScheme) := by
  intro hsec
  have hneg := hsec.negligible constROMForger constROMForger_isOraclePPT
  have heval (n : ℕ) :
      ROMSignature.wordEufCmaGame encBool trivialROMScheme (constROMForger n) =
        PMF.pure true := by
    simp only [ROMSignature.wordEufCmaGame, ROMSignature.worldGame, trivialROMScheme,
      PMF.monad_bind_eq_bind, PMF.pure_bind]
    rw [ROMSignature.eval_world_worldRealize]
    simp [constROMForger, ROMSignature.routeWordProgram, ROMSignature.runLoggedForger]
  simp only [heval, succProbability_pure_true] at hneg
  exact not_negligible_const one_ne_zero hneg

/-- `trivialROMScheme` fails `ROMSignature.SUFCMA`. -/
theorem not_romSignature_sufCMA_trivial :
    ¬ ROMSignature.SUFCMA (fun _ => encBool) (fun _ => trivialROMScheme) :=
  fun h => not_romSignature_eufCMA_trivial h.eufCma

end CslibFrontierTests.Crypto.HashAndAuthNonvacuity
