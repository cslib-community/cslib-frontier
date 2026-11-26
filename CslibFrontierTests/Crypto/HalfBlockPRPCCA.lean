/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

import CslibFrontier.Crypto.Computational.Encryption.HalfBlockPRP.CCA
import CslibFrontier.Crypto.Computational.LubyRackoff
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.Negligible
import CslibFrontier.Tactic.PPT
import CslibFrontier.Tactic.PolyTime

set_option linter.privateModule false

/-!
# Module client tests for IND-CCA security of half-block strong-PRP encryption

Exercises the public surface of `CslibFrontier.Crypto.Computational.Encryption.HalfBlockPRP.CCA`
as an ordinary `module` client (with plain `import`s and no `import all`), covering:

* **`Q = 0` boundary on `idCipher`:** a zero-query `CCAAdversary` gives zero query budget on
  `ccaToStrongPRPAdversary`, exact game coincidence
  `eval_strongPRPRealGame_ccaToStrongPRPAdversary`, and a zero additive birthday/switching loss in
  `BlockCipher.advantage_ccaGame_halfBlockCipher_le`.
* **`Q = 2` boundary and non-vacuity of `F.StrongPRP` on `idCipher`:**
  1. Replaying a returned challenge ciphertext directly to the decryption oracle (`(true, ct)`) is
     answered locally with `[]` in both experiments, giving advantage `0`.
  2. Flipping the first bit of the returned `2 * (n + 1)`-bit challenge ciphertext modifies only the
     `n + 1`-bit nonce prefix while producing a fresh ciphertext `ct' ≠ ct`, so a `2`-query
     `IsOraclePPT encBool` CCA adversary recovers the challenge bit with probability `1` against
     `idCipher.halfBlockCipher` (`¬ (idCipher.halfBlockCipher _).INDCCA`), and instantiating
     `BlockCipher.advantage_ccaGame_halfBlockCipher_le` at `Q = 2` (`(2 : ℕ).choose 2 = 1`) forces
     the strong-PRP advantages of `ccaToStrongPRPAdversary false/true` against `idCipher` to sum to
     at least `1 - (2 ^ (n + 1))⁻¹ - 2 * ((2 ^ (n + 1))⁻¹) ^ 2`.
* **Reduction efficiency (`isOraclePPT_ccaToStrongPRPAdversary`):** checked on concrete zero-query
  and adaptive two-query `CCAAdversary` witnesses.
* **Missing plaintext integrity (`not_encForge_halfBlockCipher`) and Boneh–Shoup Exercise 9.12(a) /
  Theorem 9.1 remark (`StrongPRP.indcca_halfBlockCipher`, `exists_indcca_not_integrity`):**
  checked both over an arbitrary strong PRP and over the four-round Feistel strong PRP built from
  any `PseudorandomFunction`.
-/

namespace CslibFrontierTests.Crypto.HalfBlockPRPCCA

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM
open scoped NNReal

/-- Toy identity block cipher on `2 * n`-bit blocks with `n`-bit keys: a permutation for every key,
but not a strong PRP. -/
private def idCipher : BlockCipher where
  keyLen := id
  blockLen n := 2 * n
  keyLen_polyTime := ComputableInPolyTime.id'
  blockLen_polyTime := ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2)
    ComputableInPolyTime.id'
  encrypt _ _ block := block
  decrypt _ _ block := block
  encrypt_polyTime := by polytime
  decrypt_polyTime := by polytime
  length_encrypt _ _ _ _ hblock := hblock
  length_decrypt _ _ _ _ hblock := hblock
  decrypt_encrypt _ _ _ _ _ := rfl
  encrypt_decrypt _ _ _ _ _ := rfl

private theorem blockLen_idCipher (n : ℕ) : idCipher.blockLen n = 2 * n := rfl

private noncomputable abbrev idHalfBlock : SymmetricCipher :=
  idCipher.halfBlockCipher blockLen_idCipher

/-! ### 1. `Q = 0` boundary on `idCipher` -/

/-- Zero-query CCA adversary returning `false`. -/
private def zeroCCAAdversary : CCAAdversary :=
  fun _ _ => pure false

theorem isOraclePPT_zeroCCAAdversary : IsOraclePPT encBool zeroCCAAdversary := by
  have h : IsOraclePPTOn (encPair encUnary encBits) encBool
      (fun p : ℕ × List Bool => zeroCCAAdversary p.1 p.2) := by
    ppt [zeroCCAAdversary]
  exact h.isOraclePPT

example (bit : Bool) :
    IsOraclePPT encBool (ccaToStrongPRPAdversary bit zeroCCAAdversary) :=
  isOraclePPT_ccaToStrongPRPAdversary isOraclePPT_zeroCCAAdversary bit

example (bit : Bool) (n : ℕ) :
    (ccaToStrongPRPAdversary bit zeroCCAAdversary n []).IsQueryBounded 0 :=
  isQueryBounded_ccaToStrongPRPAdversary bit zeroCCAAdversary n [] (.pure false 0)

example (bit : Bool) (n : ℕ) :
    ProbComp.eval (idCipher.strongPRPRealGame (ccaToStrongPRPAdversary bit zeroCCAAdversary) n) =
      PMF.pure false := by
  rw [eval_strongPRPRealGame_ccaToStrongPRPAdversary idCipher blockLen_idCipher]
  have h : ProbComp.eval (idHalfBlock.ccaGame zeroCCAAdversary bit n) =
      (BitString.uniformList n).map (fun _ => false) := by
    simp [SymmetricCipher.ccaGame, zeroCCAAdversary, idCipher, BlockCipher.halfBlockCipher]
  exact h.trans (PMF.map_const _ false)

-- At `Q = 0`, `0.choose 2 = 0`, so the ideal birthday/switching error term in
-- `advantage_ccaGame_halfBlockCipher_le` vanishes identically.
theorem advantage_ccaGame_idHalfBlock_zeroCCAAdversary_le (n : ℕ) :
    (Game.advantage
        (ProbComp.eval (idHalfBlock.ccaGame zeroCCAAdversary false n))
        (ProbComp.eval (idHalfBlock.ccaGame zeroCCAAdversary true n)) : ℝ) ≤
      Game.advantage
        (ProbComp.eval (idCipher.strongPRPRealGame
          (ccaToStrongPRPAdversary false zeroCCAAdversary) n))
        (ProbComp.eval (strongPRPIdealGame idCipher.blockLen
          (ccaToStrongPRPAdversary false zeroCCAAdversary) n)) +
      Game.advantage
        (ProbComp.eval (idCipher.strongPRPRealGame
          (ccaToStrongPRPAdversary true zeroCCAAdversary) n))
        (ProbComp.eval (strongPRPIdealGame idCipher.blockLen
          (ccaToStrongPRPAdversary true zeroCCAAdversary) n)) := by
  simpa using
    idCipher.advantage_ccaGame_halfBlockCipher_le blockLen_idCipher zeroCCAAdversary n 0
      (.pure false 0)

/-! ### 2. `Q = 2` boundary: challenge replay vs. nonce-bit malleability on `idCipher` -/

/-- Two-query CCA adversary that encrypts `(0^n, 1^n)` to obtain `ct` and immediately replays the
same `ct` to the decryption oracle, testing whether the reply is non-empty (`ct != []` rejected as
`[]`). -/
private def replayChallengeCCAAdversary : CCAAdversary :=
  fun n _ => do
    let ct ← List.take (2 * n) <$> ProbOracleComp.query
      (false, encPair encBits encBits (List.replicate n false, List.replicate n true))
    let dec ← List.take (n + 1) <$> ProbOracleComp.query (true, ct)
    return !dec.isEmpty

theorem isQueryBounded_replayChallengeCCAAdversary (n : ℕ) :
    (replayChallengeCCAAdversary n []).IsQueryBounded 2 := by
  unfold replayChallengeCCAAdversary
  refine OracleComp.IsCostBounded.bind (n := 1) (m := 1) ?_ fun ct =>
    OracleComp.IsCostBounded.bind (n := 1) (m := 0) ?_ fun _ => .pure _ 0
  · simp only [OracleComp.isCostBounded_map_iff]
    exact ProbOracleComp.IsQueryBounded.query _
  · simp only [OracleComp.isCostBounded_map_iff]
    exact ProbOracleComp.IsQueryBounded.query _

-- Replaying the returned challenge ciphertext to the decryption oracle answers `[]` in both
-- experiments, so the adversary always outputs `false` and gets advantage `0`.
theorem eval_ccaGame_idHalfBlock_replayChallengeCCAAdversary (bit : Bool) (n : ℕ) :
    ProbComp.eval (idHalfBlock.ccaGame replayChallengeCCAAdversary bit n) = PMF.pure false := by
  simp only [SymmetricCipher.ccaGame, replayChallengeCCAAdversary,
    OracleComp.interpret_bind, OracleComp.interpret_pure, OracleComp.interpret_map,
    ProbOracleComp.interpret_query, StateT.run_bind, StateT.run_pure, StateT.run_map,
    ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_map, PMF.bind_map,
    Function.comp_def]
  dsimp only [SymmetricCipher.ccaOracle, idHalfBlock, idCipher, BlockCipher.halfBlockCipher,
    StateT.run]
  simp only [encPair_apply, encBits_apply, unframe_frame_append, dropFrame_frame_append,
    List.length_replicate, beq_self_eq_true, Bool.and_self, Bool.false_eq_true, ↓reduceIte,
    ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
  refine (PMF.bind_congr_on_support _ _ (fun _ => PMF.pure false) fun k _ => ?_).trans
    (PMF.bind_const _ _)
  refine (PMF.bind_congr_on_support _ _ (fun _ => PMF.pure false) fun r hr => ?_).trans
    (PMF.bind_const _ _)
  rw [BitString.eval_sampleList] at hr
  have hrLen := BitString.length_of_mem_support_uniformList hr
  have hmbLen : (if bit then List.replicate n true else List.replicate n false).length = n := by
    cases bit <;> simp
  have htake : List.take (2 * n)
      (r ++ if bit then List.replicate n true else List.replicate n false) =
      r ++ if bit then List.replicate n true else List.replicate n false :=
    List.take_of_length_le (by rw [List.length_append, hrLen, hmbLen, Nat.two_mul])
  simp [htake]

/-- Two-query CCA adversary that queries `(0^n, 1^n)`, flips the first bit of the returned
ciphertext (a nonce bit when `n ≥ 1`, producing a fresh ciphertext `ct' ≠ ct` that bypasses the
challenge-replay guard while preserving the `n`-bit message suffix under `idCipher`), decrypts
`ct'`, and checks whether the decrypted plaintext is `some (1^n)`. -/
private def flipNonceCCAAdversary : CCAAdversary :=
  fun n _ => do
    let ct ← List.take (2 * n) <$> ProbOracleComp.query
      (false, encPair encBits encBits (List.replicate n false, List.replicate n true))
    let dec ← List.take (n + 1) <$> ProbOracleComp.query (true, (!ct.headD false) :: ct.tail)
    return dec == encOption encBits (some (List.replicate n true))

theorem isQueryBounded_flipNonceCCAAdversary (n : ℕ) :
    (flipNonceCCAAdversary n []).IsQueryBounded 2 := by
  unfold flipNonceCCAAdversary
  refine OracleComp.IsCostBounded.bind (n := 1) (m := 1) ?_ fun ct =>
    OracleComp.IsCostBounded.bind (n := 1) (m := 0) ?_ fun _ => .pure _ 0
  · simp only [OracleComp.isCostBounded_map_iff]
    exact ProbOracleComp.IsQueryBounded.query _
  · simp only [OracleComp.isCostBounded_map_iff]
    exact ProbOracleComp.IsQueryBounded.query _

theorem isOraclePPT_flipNonceCCAAdversary : IsOraclePPT encBool flipNonceCCAAdversary := by
  have h : IsOraclePPTOn (encPair encUnary encBits) encBool
      (fun p : ℕ × List Bool => flipNonceCCAAdversary p.1 p.2) := by
    ppt [flipNonceCCAAdversary]
  exact h.isOraclePPT

theorem isOraclePPT_ccaToStrongPRPAdversary_flipNonce (bit : Bool) :
    IsOraclePPT encBool (ccaToStrongPRPAdversary bit flipNonceCCAAdversary) :=
  isOraclePPT_ccaToStrongPRPAdversary isOraclePPT_flipNonceCCAAdversary bit

-- At security parameter `n + 1`, `flipNonceCCAAdversary` recovers `bit` with certainty against
-- `idCipher.halfBlockCipher`.
theorem eval_ccaGame_idHalfBlock_flipNonceCCAAdversary (bit : Bool) (n : ℕ) :
    ProbComp.eval (idHalfBlock.ccaGame flipNonceCCAAdversary bit (n + 1)) = PMF.pure bit := by
  simp only [SymmetricCipher.ccaGame, flipNonceCCAAdversary,
    OracleComp.interpret_bind, OracleComp.interpret_pure, OracleComp.interpret_map,
    ProbOracleComp.interpret_query, StateT.run_bind, StateT.run_pure, StateT.run_map,
    ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_map, PMF.bind_map,
    Function.comp_def]
  dsimp only [SymmetricCipher.ccaOracle, idHalfBlock, idCipher, BlockCipher.halfBlockCipher,
    StateT.run]
  simp only [encPair_apply, encBits_apply, unframe_frame_append, dropFrame_frame_append,
    List.length_replicate, beq_self_eq_true, Bool.and_self, Bool.false_eq_true, ↓reduceIte,
    ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
  refine (PMF.bind_congr_on_support _ _ (fun _ => PMF.pure bit) fun k _ => ?_).trans
    (PMF.bind_const _ _)
  refine (PMF.bind_congr_on_support _ _ (fun _ => PMF.pure bit) fun r hr => ?_).trans
    (PMF.bind_const _ _)
  rw [BitString.eval_sampleList] at hr
  have hrLen := BitString.length_of_mem_support_uniformList hr
  obtain ⟨r₀, rTail, rfl⟩ : ∃ b tl, r = b :: tl := by
    cases r with
    | nil => simp at hrLen
    | cons b tl => exact ⟨b, tl, rfl⟩
  simp only [List.length_cons, Nat.add_right_cancel_iff] at hrLen
  have hmbLen :
      (if bit then List.replicate (n + 1) true else List.replicate (n + 1) false).length =
        n + 1 := by
    cases bit <;> simp
  have htake : List.take (2 * (n + 1))
      (r₀ :: (rTail ++
        if bit then List.replicate (n + 1) true else List.replicate (n + 1) false)) =
      r₀ :: (rTail ++
        if bit then List.replicate (n + 1) true else List.replicate (n + 1) false) :=
    List.take_of_length_le (by
      rw [List.length_cons, List.length_append, hrLen, hmbLen, Nat.two_mul]
      omega)
  have hne :
      ((!r₀) :: (rTail ++
        if bit then List.replicate (n + 1) true else List.replicate (n + 1) false)) ≠
      (r₀ :: (rTail ++
        if bit then List.replicate (n + 1) true else List.replicate (n + 1) false)) := by
    intro h
    have := List.cons.inj h |>.1
    cases r₀ <;> simp at this
  have hlen' :
      ((!r₀) :: (rTail ++
        if bit then List.replicate (n + 1) true else List.replicate (n + 1) false)).length =
      2 * (n + 1) := by
    rw [List.length_cons, List.length_append, hrLen, hmbLen, Nat.two_mul]
    omega
  have hdrop :
      List.drop (n + 1) ((!r₀) :: (rTail ++
        if bit then List.replicate (n + 1) true else List.replicate (n + 1) false)) =
      (if bit then List.replicate (n + 1) true else List.replicate (n + 1) false) := by
    change List.drop (n + 1) (((!r₀) :: rTail) ++ _) = _
    exact List.drop_left' (by simp [hrLen])
  simp only [List.cons_append, htake, List.headD_cons, List.tail_cons, List.contains_cons,
    List.contains_nil, Bool.or_false, beq_eq_false_iff_ne.mpr hne, Bool.false_eq_true, ↓reduceIte,
    hlen', beq_self_eq_true, ProbComp.eval_pure, hdrop, encOption_some, encBits_apply]
  have htakeDec :
      List.take (n + 1 + 1)
        (true :: if bit then List.replicate (n + 1) true else List.replicate (n + 1) false) =
      (true :: if bit then List.replicate (n + 1) true else List.replicate (n + 1) false) :=
    List.take_of_length_le (by rw [List.length_cons, hmbLen])
  rw [PMF.pure_bind, htakeDec]
  cases bit <;> simp

-- Consequently `idCipher.halfBlockCipher` is NOT `INDCCA`, witnessing that `F.StrongPRP` cannot be
-- omitted in `BlockCipher.StrongPRP.indcca_halfBlockCipher`.
theorem not_indcca_idHalfBlock : ¬ idHalfBlock.INDCCA := by
  intro hcca
  have ht : Filter.Tendsto (fun n : ℕ => Game.advantage
      (ProbComp.eval (idHalfBlock.ccaGame flipNonceCCAAdversary false (n + 1)))
      (ProbComp.eval (idHalfBlock.ccaGame flipNonceCCAAdversary true (n + 1))))
      Filter.atTop (nhds 0) := by
    simpa [Function.comp_def] using
      ((hcca flipNonceCCAAdversary isOraclePPT_flipNonceCCAAdversary) 0).comp
        (Filter.tendsto_add_atTop_nat 1)
  have h1 : (fun n : ℕ => Game.advantage
      (ProbComp.eval (idHalfBlock.ccaGame flipNonceCCAAdversary false (n + 1)))
      (ProbComp.eval (idHalfBlock.ccaGame flipNonceCCAAdversary true (n + 1)))) =
      fun _ => (1 : ℝ≥0) := by
    ext n
    rw [eval_ccaGame_idHalfBlock_flipNonceCCAAdversary false n,
      eval_ccaGame_idHalfBlock_flipNonceCCAAdversary true n]
    simp [Game.advantage, Game.succProbability]
  rw [h1] at ht
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds ht)

-- Concrete `Q = 2` check on `advantage_ccaGame_halfBlockCipher_le`: since `(2 : ℕ).choose 2 = 1`
-- and `flipNonceCCAAdversary` achieves CCA advantage `1` at `n + 1`, the two strong-PRP advantages
-- of `ccaToStrongPRPAdversary false/true flipNonceCCAAdversary` against `idCipher` must make up at
-- least `1 - ((2 ^ (n + 1))⁻¹ + 2 * ((2 ^ (n + 1))⁻¹) ^ 2)`.
theorem one_sub_le_sum_strongPRPAdvantage_flipNonce (n : ℕ) :
    1 - (((2 : ℝ) ^ (n + 1))⁻¹ + 2 * (((2 : ℝ) ^ (n + 1))⁻¹) ^ 2) ≤
      Game.advantage
        (ProbComp.eval (idCipher.strongPRPRealGame
          (ccaToStrongPRPAdversary false flipNonceCCAAdversary) (n + 1)))
        (ProbComp.eval (strongPRPIdealGame idCipher.blockLen
          (ccaToStrongPRPAdversary false flipNonceCCAAdversary) (n + 1))) +
      Game.advantage
        (ProbComp.eval (idCipher.strongPRPRealGame
          (ccaToStrongPRPAdversary true flipNonceCCAAdversary) (n + 1)))
        (ProbComp.eval (strongPRPIdealGame idCipher.blockLen
          (ccaToStrongPRPAdversary true flipNonceCCAAdversary) (n + 1))) := by
  have hle := idCipher.advantage_ccaGame_halfBlockCipher_le blockLen_idCipher
    flipNonceCCAAdversary (n + 1) 2 (isQueryBounded_flipNonceCCAAdversary (n + 1))
  rw [eval_ccaGame_idHalfBlock_flipNonceCCAAdversary false n,
    eval_ccaGame_idHalfBlock_flipNonceCCAAdversary true n] at hle
  have hone : (Game.advantage (PMF.pure false) (PMF.pure true) : ℝ) = 1 := by
    simp [Game.advantage, Game.succProbability]
  have hchoose : ((2 : ℕ).choose 2 : ℝ) = 1 := by norm_num
  rw [hone, hchoose, one_mul, mul_one] at hle
  linarith

/-! ### 3. Missing plaintext integrity and asymptotic security endpoints -/

example (n : ℕ) :
    ProbComp.eval (idHalfBlock.encForgeGame idCipher.allOnesForger n) = PMF.pure true :=
  idCipher.eval_encForgeGame_halfBlockCipher_allOnesForger blockLen_idCipher n

example : ¬ idHalfBlock.EncForge :=
  idCipher.not_encForge_halfBlockCipher blockLen_idCipher

example {F : BlockCipher} (hF : F.StrongPRP) (hblock : ∀ n, F.blockLen n = 2 * n) :
    (F.halfBlockCipher hblock).INDCCA ∧ ¬ (F.halfBlockCipher hblock).EncForge :=
  ⟨hF.indcca_halfBlockCipher hblock, F.not_encForge_halfBlockCipher hblock⟩

example {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family) :
    ∃ E : SymmetricCipher, E.INDCCA ∧ ¬ E.CiphertextIntegrity ∧ ¬ E.EncForge :=
  hprf.exists_indcca_not_integrity

example {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family) :
    let F := lubyRackoff4Cipher family hprf.polyTime hprf.length_eq
    (F.halfBlockCipher (fun _ => rfl)).INDCCA ∧
      ¬ (F.halfBlockCipher (fun _ => rfl)).CiphertextIntegrity ∧
      ¬ (F.halfBlockCipher (fun _ => rfl)).EncForge :=
  ⟨hprf.strongPRP_lubyRackoff4Cipher.indcca_halfBlockCipher (fun _ => rfl),
    BlockCipher.not_ciphertextIntegrity_halfBlockCipher _ (fun _ => rfl),
    BlockCipher.not_encForge_halfBlockCipher _ (fun _ => rfl)⟩

end CslibFrontierTests.Crypto.HalfBlockPRPCCA
