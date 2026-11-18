/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Computational.Encryption.EncryptThenMAC
public import CslibFrontier.Crypto.Computational.Encryption.RepeatingCiphertexts
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Languages.Probabilistic.Oracle.Norm
import CslibFrontier.Probability.PMF.Support
import CslibFrontier.Tactic.PPT
import CslibFrontier.Tactic.PolyTime

/-!
# Tests for Deterministic Ciphers and Repeating Ciphertexts

Exercises `CslibFrontier.Crypto.Computational.Encryption.RepeatingCiphertexts`
([BonehShoup2023], Section 5.3, Example 5.1, p. 182; Section 5.8, Exercise 5.12, p. 211) as an
ordinary `module` client:

* **Expanding deterministic cipher (`expandingOtpCipher`):** encrypts `m` under `k` as
  `true :: (m ⊕ k)` of length `n + 1`, so `CiphertextLength n n` is false for every `n` (ruling
  out `SymmetricCipher.not_indcpa_of_ciphertext_length_eq`), while
  `SymmetricCipher.not_indcpa_of_deterministic` refutes `INDCPA` and
  `SymmetricCipher.advantage_cpaGame_detCPAAdversary` gives CPA advantage `1` for `1 ≤ n`.
* **Repeated-ciphertext reduction on deterministic and randomized ciphers:** a 2-query
  `CIAdversary` (`twoZeroQueries`, exercising polymorphism in the adversary's return type) wins
  `expandingOtpCipher.repeatCiphertextGame` with probability `1`, forcing CPA advantage `≥ 1 / 2`
  for `repeatToCPAAdversary` at all `1 ≤ n` via
  `succProbability_repeatCiphertextGame_le_two_mul_advantage`; at `n = 0` (`|M| = 1`),
  `repeatCiphertextGame` still succeeds with probability `1` while the CPA advantage is `0`,
  confirming `1 ≤ n` is needed. On the randomized `prfCipher`, both the concrete bound
  `succProbability_repeatCiphertextGame_le_two_mul_advantage` and the asymptotic corollary
  `INDCPA.negligible_repeatCiphertextGame` apply.
-/

public section

namespace CslibFrontierTests.Crypto.RepeatingCiphertexts

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.SymmetricCipher Turing.MultiTapeTM
open scoped NNReal

/-! ### Expanding Deterministic Cipher (Example 5.1) -/

/-- Deterministic one-time-pad cipher that prepends a constant tag bit `true`, expanding `n`-bit
messages to `(n + 1)`-bit ciphertexts. -/
noncomputable def expandingOtpCipher : SymmetricCipher where
  keyGen := BitString.sampleList
  encrypt _ k msg := pure (true :: List.zipWith xor msg k)
  decrypt _ k ct := some (List.zipWith xor ct.tail k)
  keyGen_ppt := by ppt
  encrypt_ppt := by ppt
  decrypt_polyTime := by polytime
  decrypt_encrypt := by
    intro n k hk msg hmsg ct hct
    rw [BitString.eval_sampleList] at hk
    have hkLen : k.length = n := BitString.length_of_mem_support_uniformList hk
    rw [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hct
    subst hct
    congr 1
    exact List.ext_getElem (by simp [hmsg, hkLen]) fun i _ _ => by simp

/-- Every supported ciphertext of `expandingOtpCipher` at parameter `n` has length `n + 1`. -/
theorem expandingOtpCipher_ciphertextLength (n : ℕ) :
    expandingOtpCipher.CiphertextLength n (n + 1) := by
  intro k hk msg hmsg ct hct
  dsimp only [expandingOtpCipher] at hk hct
  rw [BitString.eval_sampleList] at hk
  have hkLen : k.length = n := BitString.length_of_mem_support_uniformList hk
  rw [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hct
  subst hct
  simp [hmsg, hkLen]

/-- `expandingOtpCipher` never satisfies `CiphertextLength n n`, so
`not_indcpa_of_ciphertext_length_eq` does not apply to it. -/
example (n : ℕ) : ¬ expandingOtpCipher.CiphertextLength n n := by
  intro hlen
  have hk : List.replicate n false ∈ (ProbComp.eval (expandingOtpCipher.keyGen n)).support := by
    dsimp only [expandingOtpCipher]
    rw [BitString.eval_sampleList, BitString.mem_support_uniformList_iff]
    exact List.length_replicate
  have hct : true :: List.zipWith xor (List.replicate n false) (List.replicate n false) ∈
      (ProbComp.eval
        (expandingOtpCipher.encrypt n (List.replicate n false)
          (List.replicate n false))).support := by
    simp [expandingOtpCipher]
  have heq := hlen _ hk _ List.length_replicate _ hct
  have heqSucc := expandingOtpCipher_ciphertextLength n _ hk _ List.length_replicate _ hct
  omega

/-- `not_indcpa_of_deterministic` refutes `INDCPA` for the expanding cipher `expandingOtpCipher`. -/
theorem not_indcpa_expandingOtpCipher : ¬ expandingOtpCipher.INDCPA :=
  expandingOtpCipher.not_indcpa_of_deterministic 0 fun n _ k _ =>
    ⟨true :: List.zipWith xor (List.replicate n false) k,
      by simp [expandingOtpCipher]⟩

/-- For every `1 ≤ n`, `detCPAAdversary (· + 1)` achieves CPA advantage `1` against
`expandingOtpCipher`. -/
example {n : ℕ} (hn : 1 ≤ n) :
    Game.advantage
      (ProbComp.eval (expandingOtpCipher.cpaGame (detCPAAdversary (· + 1)) false n))
      (ProbComp.eval (expandingOtpCipher.cpaGame (detCPAAdversary (· + 1)) true n)) = 1 :=
  expandingOtpCipher.advantage_cpaGame_detCPAAdversary (· + 1) hn
    (fun k hk m hm c hc => (expandingOtpCipher_ciphertextLength n k hk m hm c hc).le)
    (fun k _ => ⟨true :: List.zipWith xor (List.replicate n false) k,
      by simp [expandingOtpCipher]⟩)

/-! ### Exercise 5.12: Repeating Ciphertexts -/

/-- Two-query `CIAdversary` (`α = List Bool`) querying `0^n` twice. -/
def twoZeroQueries : CIAdversary :=
  fun n _ => do
    let c₁ ← List.take (n + 1) <$> ProbOracleComp.query ((), List.replicate n false)
    let _ ← List.take (n + 1) <$> ProbOracleComp.query ((), List.replicate n false)
    return c₁

theorem isOraclePPT_twoZeroQueries : IsOraclePPT encBits twoZeroQueries := by
  ppt [twoZeroQueries]

theorem isOraclePPT_repeatWrapper_twoZeroQueries :
    IsOraclePPT encBool (repeatToCPAAdversary (· + 1) twoZeroQueries) :=
  isOraclePPT_repeatToCPAAdversary (by fun_prop) isOraclePPT_twoZeroQueries

/-- Against deterministic `expandingOtpCipher`, `twoZeroQueries` triggers a ciphertext collision
with probability `1` at every security parameter `n`. -/
theorem succProbability_repeatCiphertextGame_expandingOtpCipher (n : ℕ) :
    Game.succProbability (expandingOtpCipher.repeatCiphertextGame twoZeroQueries n) = 1 := by
  have hpure : expandingOtpCipher.repeatCiphertextGame twoZeroQueries n = PMF.pure true := by
    simp only [repeatCiphertextGame, twoZeroQueries, ProbOracleComp.eval_runState, runWith_norm,
      pmf_norm]
    refine PMF.bind_eq_pure_of_forall_mem_support fun k _ => ?_
    simp [ciEncryptionOracle, expandingOtpCipher, pmf_norm]
  rw [hpure]
  simp [Game.succProbability]

/-- By `succProbability_repeatCiphertextGame_le_two_mul_advantage`, for every `1 ≤ n`,
`repeatToCPAAdversary (· + 1) twoZeroQueries` achieves CPA advantage at least `1 / 2` against
`expandingOtpCipher`. -/
example {n : ℕ} (hn : 1 ≤ n) :
    (1 : ℝ≥0) / 2 ≤ Game.advantage
      (ProbComp.eval
        (expandingOtpCipher.cpaGame (repeatToCPAAdversary (· + 1) twoZeroQueries) false n))
      (ProbComp.eval
        (expandingOtpCipher.cpaGame (repeatToCPAAdversary (· + 1) twoZeroQueries) true n)) := by
  have h := expandingOtpCipher.succProbability_repeatCiphertextGame_le_two_mul_advantage
    (· + 1) twoZeroQueries hn
    (fun k hk m hm c hc => (expandingOtpCipher_ciphertextLength n k hk m hm c hc).le)
  rw [succProbability_repeatCiphertextGame_expandingOtpCipher n] at h
  exact (div_le_iff₀' (by norm_num : (0 : ℝ≥0) < 2)).mpr h

/-- Hypothesis probe (`1 ≤ n`, i.e. `|M| ≥ 2` in [BonehShoup2023], Exercise 5.12): at `n = 0`
(`|M| = 2^0 = 1`), every valid query pair `(m₀, m₁)` has `m₀ = [] = m₁`, so `cpaGame` at `0` is
independent of the challenge bit and every distinguisher `B` has CPA advantage `0`, while
`twoZeroQueries` still wins `repeatCiphertextGame` at `0` with probability `1`. -/
example (B : OracleDistinguisher) :
    Game.succProbability (expandingOtpCipher.repeatCiphertextGame twoZeroQueries 0) = 1 ∧
      Game.advantage (ProbComp.eval (expandingOtpCipher.cpaGame B false 0))
        (ProbComp.eval (expandingOtpCipher.cpaGame B true 0)) = 0 := by
  refine ⟨succProbability_repeatCiphertextGame_expandingOtpCipher 0, ?_⟩
  have hsame : expandingOtpCipher.cpaEncryptionOracle 0 = fun k _ request s =>
      let m0 := unframe request.2
      let m1 := dropFrame request.2
      if (m0.length == 0) && (m1.length == 0) then do
        let ct ← expandingOtpCipher.encrypt 0 k []
        return (ct, s)
      else
        return ([], s) := by
    funext k bit request s
    unfold cpaEncryptionOracle
    by_cases hv : ((unframe request.2).length == 0 && (dropFrame request.2).length == 0) = true
    · simp only [hv, ↓reduceIte]
      simp only [Bool.and_eq_true, beq_iff_eq, List.length_eq_zero_iff] at hv
      rcases hv with ⟨hm0, hm1⟩
      cases bit <;> simp [hm0, hm1]
    · simp [hv]
  have hgame : expandingOtpCipher.cpaGame B false 0 = expandingOtpCipher.cpaGame B true 0 := by
    simp only [cpaGame, hsame]
  rw [hgame]
  simp [Game.advantage]

/-! ### Randomized `prfCipher` Instance -/

/-- Concrete Exercise 5.12 bound instantiated on `prfCipher` with the key-projection family
`fun key _ => key`. -/
example {α : Type} (A : ℕ → List Bool → WordOracleComp Unit α) {n : ℕ} (hn : 1 ≤ n) :
    Game.succProbability
        ((prfCipher (fun key _ => key) (ComputableInPolyTime.fst encBits encBits)
          (fun _ _ _ => rfl)).repeatCiphertextGame A n) ≤
      2 * Game.advantage
        (ProbComp.eval ((prfCipher (fun key _ => key) (ComputableInPolyTime.fst encBits encBits)
          (fun _ _ _ => rfl)).cpaGame (repeatToCPAAdversary (2 * ·) A) false n))
        (ProbComp.eval ((prfCipher (fun key _ => key) (ComputableInPolyTime.fst encBits encBits)
          (fun _ _ _ => rfl)).cpaGame (repeatToCPAAdversary (2 * ·) A) true n)) :=
  (prfCipher (fun key _ => key) (ComputableInPolyTime.fst encBits encBits)
    (fun _ _ _ => rfl)).succProbability_repeatCiphertextGame_le_two_mul_advantage (2 * ·) A hn
    fun k hk m hm c hc =>
      (prfCipher_ciphertext_length (fun key _ => key) (ComputableInPolyTime.fst encBits encBits)
        (fun _ _ _ => rfl) n k hk m hm c hc).le

/-- Asymptotic Exercise 5.12 instantiated on `prfCipher` for any `PseudorandomFunction`. -/
example {α : Type} {encOut : α ↪ List Bool} {family : List Bool → List Bool → List Bool}
    (hprf : PseudorandomFunction family)
    (A : ℕ → List Bool → WordOracleComp Unit α) (hA : IsOraclePPT encOut A) :
    Negligible fun n =>
      Game.succProbability
        ((prfCipher family hprf.polyTime hprf.length_eq).repeatCiphertextGame A n) :=
  hprf.indcpa_prfCipher.negligible_repeatCiphertextGame A hA

end CslibFrontierTests.Crypto.RepeatingCiphertexts
