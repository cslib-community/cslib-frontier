/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Crypto.Computational.RSASignatureAttacks
import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for the attacks on RSA signatures without a full-domain hash

The toy keys are `N = 33` and the even modulus `N = 6` (`p = 2` is allowed). The tests evaluate the
scheme and the blinding arithmetic of (13.4) on numbers, apply each forger's law and query bound,
give the universal forger's exact loss `1 / φ(N)` with a uniform unit, state (13.9) as printed and
under a key drawn from any law, and certify the blinding maps on an encoded RSA input. The last
section gives a failing case for each added hypothesis and for the conventions of the scheme.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.RSASignatureAttacks

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM

/-- Toy RSA key `N = 3 * 11 = 33`, `e = 3`, `d = 7` (`3 * 7 ≡ 1 [MOD 20]`). -/
def rsa33 : RSADesc :=
  { p := 3, q := 11, e := 3, d := 7, hp := by norm_num, hq := by norm_num, hpq := by decide,
    he := by decide, hed := by decide }

/-- Toy key with an even modulus: `N = 2 * 3 = 6`, `e = 3`, `d = 1` (`3 * 1 ≡ 1 [MOD 2]`). -/
def rsa6 : RSADesc :=
  { p := 2, q := 3, e := 3, d := 1, hp := by norm_num, hq := by norm_num, hpq := by decide,
    he := by decide, hed := by decide }

/-! ### The scheme -/

-- The signature on `4` is `4 ^ 7 % 33 = 16`, and it verifies.
example : rsaInvert 33 7 4 = 16 := by decide
example : (unhashedRSASignature rsa33).verify rsa33.publicKey 4 16 = true := by decide
example : (unhashedRSASignature rsa33).Correct := rsaSignature_correct rsa33 _

/-! ### Existential forgery, no query (p. 536) -/

-- Whatever `σ` is picked, the forger wins; for `σ = 5` it outputs the message `5 ^ 3 % 33 = 26`.
example (pick : ProbComp (Fin 33)) :
    ProbComp.eval ((unhashedRSASignature rsa33).eufCmaExperiment
      fun _ => unhashedRSAExistentialForger rsa33.publicKey pick) = PMF.pure true :=
  eval_eufCmaExperiment_unhashedRSAExistentialForger rsa33 pick

example : rsaEval 33 3 5 = 26 := by decide

-- Hence its success probability is `1`.
example (pick : ProbComp (Fin 33)) :
    Experiment.succProbability ((unhashedRSASignature rsa33).eufCmaExperiment
      fun _ => unhashedRSAExistentialForger rsa33.publicKey pick) = 1 := by
  simp [Experiment.succProbability, Game.succProbability,
    eval_eufCmaExperiment_unhashedRSAExistentialForger rsa33 pick]

example (pick : ProbComp (Fin rsa33.modulus)) :
    (unhashedRSAExistentialForger rsa33.publicKey pick).IsQueryBounded 0 :=
  isQueryBounded_unhashedRSAExistentialForger rsa33.publicKey pick

/-! ### Universal forgery, one query (p. 537) -/

-- To sign `4` with `r = 2`: the blinded message is `4 * 2 ^ 3 % 33 = 32`, its signature is `32`,
-- and `32 / 2 = 16` is the signature on `4`.
example : rsaBlind 33 3 4 2 = 32 := by decide
example : rsaInvert 33 7 32 = 32 := by decide
example : rsaUnblind 33 2 32 = 16 := by
  unfold rsaUnblind BinaryGcd.modInv
  decide

-- Equation (13.4) on these numbers.
example : rsaEval 33 3 (rsaUnblind 33 2 32) = 4 % 33 :=
  rsaEval_rsaUnblind (by decide) (by decide) (by decide)

-- With `r = N - 1 = 32` the forger wins on every message; on `4` it asks for the signature on
-- `4 * 32 ^ 3 % 33 = 29`.
example (m : Fin 33) :
    ProbComp.eval ((unhashedRSASignature rsa33).eufCmaExperiment
      fun _ => unhashedRSAUniversalForger rsa33.publicKey m (pure 32)) = PMF.pure true :=
  eval_eufCmaExperiment_unhashedRSAUniversalForger_sub_one rsa33 m

example : rsaBlind 33 3 4 32 = 29 := by decide

-- No hypothesis on the key: the same for the even modulus `6`, with `r = 5`.
example (m : Fin 6) :
    ProbComp.eval ((unhashedRSASignature rsa6).eufCmaExperiment
      fun _ => unhashedRSAUniversalForger rsa6.publicKey m (pure 5)) = PMF.pure true :=
  eval_eufCmaExperiment_unhashedRSAUniversalForger_sub_one rsa6 m

-- With the book's uniform unit `r`, the forger loses on the unit `4` exactly when `r = 1`: with
-- probability `1 / 20`, since there are `20` units modulo `33`.
example :
    ProbComp.eval ((unhashedRSASignature rsa33).eufCmaExperiment fun _ =>
      unhashedRSAUniversalForger rsa33.publicKey 4
        ((fun u => (rsa33.unitResidue u : ℕ)) <$> ProbComp.uniform (ZMod rsa33.modulus)ˣ)) false =
      (20 : ENNReal)⁻¹ := by
  rw [eval_eufCmaExperiment_unhashedRSAUniversalForger_uniform rsa33 (m := 4) (by decide)]
  have h : Nat.totient rsa33.modulus = 20 := by decide
  rw [h, Nat.cast_ofNat]

-- `p = 2` is allowed: modulo `6` there are two units, and the forger loses on `5` with
-- probability `1 / 2`.
example :
    ProbComp.eval ((unhashedRSASignature rsa6).eufCmaExperiment fun _ =>
      unhashedRSAUniversalForger rsa6.publicKey 5
        ((fun u => (rsa6.unitResidue u : ℕ)) <$> ProbComp.uniform (ZMod rsa6.modulus)ˣ)) false =
      (2 : ENNReal)⁻¹ := by
  rw [eval_eufCmaExperiment_unhashedRSAUniversalForger_uniform rsa6 (m := 5) (by decide)]
  have h : Nat.totient rsa6.modulus = 2 := by decide
  rw [h, Nat.cast_ofNat]

-- A message that is not a unit is signed without a query: the signature `3 ^ 7 % 33 = 9` on `3`
-- is computed from `(N, e)`, and the forger wins whatever `pick` is.
example : rsaNonUnitRoot 33 3 3 = 9 := by
  unfold rsaNonUnitRoot BinaryGcd.modInv
  decide

example : rsaNonUnitRoot 33 3 3 = rsaInvert 33 7 3 :=
  rsaNonUnitRoot_eq_rsaInvert rsa33 (by decide) (by decide)

example (pick : ProbComp ℕ) :
    ProbComp.eval ((unhashedRSASignature rsa33).eufCmaExperiment
      fun _ => unhashedRSAUniversalForger rsa33.publicKey 3 pick) = PMF.pure true :=
  eval_eufCmaExperiment_unhashedRSAUniversalForger_of_not_coprime rsa33 (m := 3) (by decide) pick

example (m : Fin rsa33.modulus) (pick : ProbComp ℕ) :
    (unhashedRSAUniversalForger rsa33.publicKey m pick).IsQueryBounded 1 :=
  isQueryBounded_unhashedRSAUniversalForger rsa33.publicKey m pick

/-! ### Multiplicative forgery, two queries (equation (13.9)) -/

-- The digest `m % 32` signed directly: `15 % 32 = (3 % 32) * (5 % 32)`.
example :
    ProbComp.eval ((rsaSignature rsa33 fun m : ℕ => m % 32).eufCmaExperiment
      fun pk => rsaMultiplicativeForger pk 3 5 15) = PMF.pure true :=
  eval_eufCmaExperiment_rsaMultiplicativeForger rsa33 _ (by decide) (by decide) (by decide)

-- Unhashed RSA signatures are multiplicative: `10 = 2 * 5`.
example :
    ProbComp.eval ((unhashedRSASignature rsa33).eufCmaExperiment
      fun pk => rsaMultiplicativeForger pk 2 5 10) = PMF.pure true :=
  eval_eufCmaExperiment_rsaMultiplicativeForger rsa33 _ (by decide) (by decide) (by decide)

example (pk : RSAPublicKey) :
    (rsaMultiplicativeForger pk (3 : ℕ) 5 15).IsQueryBounded 2 :=
  isQueryBounded_rsaMultiplicativeForger pk 3 5 15

-- Equation (13.9) as printed, with the product taken over the integers.
example (desc : RSADesc) {M : Type} [DecidableEq M] (H : M → ℕ) {m₁ m₂ m₃ : M}
    (hH : H m₃ = H m₁ * H m₂) (h₁ : m₃ ≠ m₁) (h₂ : m₃ ≠ m₂) :
    ProbComp.eval ((rsaSignature desc H).eufCmaExperiment
      fun pk => rsaMultiplicativeForger pk m₁ m₂ m₃) = PMF.pure true :=
  eval_eufCmaExperiment_rsaMultiplicativeForger desc H (hH ▸ Nat.ModEq.refl _) h₁ h₂

-- With (13.9) as printed and both digests at least `2`, the messages are distinct, so the law
-- needs no freshness hypothesis.
example (desc : RSADesc) {M : Type} [DecidableEq M] (H : M → ℕ) {m₁ m₂ m₃ : M}
    (hH : H m₃ = H m₁ * H m₂) (h₁ : 2 ≤ H m₁) (h₂ : 2 ≤ H m₂) :
    ProbComp.eval ((rsaSignature desc H).eufCmaExperiment
      fun pk => rsaMultiplicativeForger pk m₁ m₂ m₃) = PMF.pure true :=
  eval_eufCmaExperiment_rsaMultiplicativeForger desc H (hH ▸ Nat.ModEq.refl _)
    (by rintro rfl; nlinarith) (by rintro rfl; nlinarith)

/-! ### Any law of the key -/

-- The theorems hold for every key, hence for a key drawn from any law `gen`, as in
-- `rsaInversionGame`.
example (gen : PMF RSADesc) (pick : (desc : RSADesc) → ProbComp (Fin desc.modulus)) :
    (gen.bind fun desc => ProbComp.eval ((unhashedRSASignature desc).eufCmaExperiment
      fun _ => unhashedRSAExistentialForger desc.publicKey (pick desc))) = PMF.pure true := by
  simp [eval_eufCmaExperiment_unhashedRSAExistentialForger]

-- Equation (13.9) as printed does not mention the key, so the forger of p. 547 wins for a key
-- drawn from any law.
example (gen : PMF RSADesc) {M : Type} [DecidableEq M] (H : M → ℕ) {m₁ m₂ m₃ : M}
    (hH : H m₃ = H m₁ * H m₂) (h₁ : m₃ ≠ m₁) (h₂ : m₃ ≠ m₂) :
    (gen.bind fun desc => ProbComp.eval ((rsaSignature desc H).eufCmaExperiment
      fun pk => rsaMultiplicativeForger pk m₁ m₂ m₃)) = PMF.pure true := by
  have h (desc : RSADesc) := eval_eufCmaExperiment_rsaMultiplicativeForger desc H
    (hH ▸ Nat.ModEq.refl _ : H m₃ ≡ H m₁ * H m₂ [MOD desc.modulus]) h₁ h₂
  simp [h]

/-! ### The blinding maps on an encoded input -/

-- Blinding the challenge of an encoded RSA input with the factor `N - 1` of the headline forger,
-- and unblinding with the same factor. These certify the two maps, not a forger.
example : ComputableInPolyTime
    (fun x : RSAInput => rsaBlind x.publicKey.N x.publicKey.e x.challenge (x.publicKey.N - 1))
    encRSAInput encNat :=
  computableInPolyTime_rsaBlind (by fun_prop) (by fun_prop) (by fun_prop)
    (ComputableInPolyTime.binary_sub' (by fun_prop) (.const 1)) fun x => x.challenge.pos

example : ComputableInPolyTime
    (fun x : RSAInput => rsaUnblind x.publicKey.N (x.publicKey.N - 1) x.challenge)
    encRSAInput encNat :=
  computableInPolyTime_rsaUnblind (by fun_prop)
    (ComputableInPolyTime.binary_sub' (by fun_prop) (.const 1)) (by fun_prop)

/-! ### Failing cases of the hypotheses, and the conventions of the scheme -/

-- For a digest below `N`, `verify` is the printed test `σ ^ e = H m` on a residue `σ`.
example (desc : RSADesc) {M : Type} (H : M → ℕ) (pk : RSAPublicKey) (m : M) (σ : ℕ)
    (h : H m < pk.N) :
    (rsaSignature desc H).verify pk m σ = true ↔ σ < pk.N ∧ rsaEval pk.N pk.e σ = H m := by
  rw [rsaSignature_verify_iff, Nat.mod_eq_of_lt h]

-- P1 (range check in `verify`): `16 + 33` has the same `e`-th power as the signature `16`, and is
-- rejected.
example : rsaEval 33 3 (16 + 33) = 4 % 33 := by decide
example : (unhashedRSASignature rsa33).verify rsa33.publicKey 4 (16 + 33) = false := by decide

-- P2 (`r` must be a unit in (13.4)): `3` is not a unit modulo `33` and unblinding fails.
example : ¬ Nat.Coprime 3 33 ∧
    rsaEval 33 3 (rsaUnblind 33 3 (rsaInvert 33 7 (rsaBlind 33 3 4 3))) ≠ 4 % 33 := by
  refine ⟨by decide, ?_⟩
  unfold rsaUnblind BinaryGcd.modInv
  decide

-- P2b (`0 < N` in (13.4)): for `N = 0` the other hypotheses hold with `r = 1`, and the
-- conclusion fails.
example : Nat.Coprime 1 0 ∧ rsaEval 0 1 5 = rsaBlind 0 1 5 1 ∧
    rsaEval 0 1 (rsaUnblind 0 1 5) ≠ 5 % 0 := by
  unfold rsaUnblind BinaryGcd.modInv
  decide

-- P3 (`r = 1` blinds nothing): the forger asks for the signature on `4` itself and loses.
example :
    ProbComp.eval ((unhashedRSASignature rsa33).eufCmaExperiment
      fun _ => unhashedRSAUniversalForger rsa33.publicKey 4 (pure 1)) = PMF.pure false := by
  rw [eval_eufCmaExperiment_unhashedRSAUniversalForger rsa33 (m := 4) (by decide) (pure 1)
    (by simp)]
  simp [Nat.ModEq]

-- P3b (`r = 1`): the output is still a valid signature on `4`; only freshness fails.
example : (unhashedRSASignature rsa33).verify rsa33.publicKey 4
    (rsaUnblind 33 1 (rsaInvert 33 7 (rsaBlind 33 3 4 1))) = true := by
  unfold rsaUnblind BinaryGcd.modInv
  decide

-- P4 (the branch for non-units, message `0`): blinding never changes `0`, so a forger that
-- blinds every message cannot win on it.
example (N e r : ℕ) : rsaBlind N e 0 r = 0 := by simp [rsaBlind]

-- P5 (the branch for non-units, a nonzero message): modulo `6` every unit `r` leaves `3` fixed.
example : ∀ r < 6, Nat.Coprime r 6 → rsaBlind 6 3 3 r = 3 := by decide

-- P5b (the message must be a unit for "loses exactly when `r = 1`"): the unit `23` is not `1`
-- modulo `33` and leaves the non-unit message `3` fixed.
example : Nat.Coprime 23 33 ∧ ¬ 23 ≡ 1 [MOD 33] ∧ rsaBlind 33 3 3 23 = 3 := by decide

-- P5c (`rsaNonUnitRoot` signs only non-units): on the unit `4` it returns `1`, not the
-- signature `16`.
example : rsaNonUnitRoot 33 3 4 = 1 ∧ rsaInvert 33 7 4 = 16 := by
  unfold rsaNonUnitRoot BinaryGcd.modInv
  decide

-- P6 (freshness in (13.9)): with `m₃ = m₁` the output is the answer to a query.
example :
    ProbComp.eval ((rsaSignature rsa33 fun m : ℕ => m).eufCmaExperiment
      fun pk => rsaMultiplicativeForger pk 4 1 4) = PMF.pure false := by
  simp [forgeExperiment, ProbOracleComp.runLogWith, rsaMultiplicativeForger, rsaSignature,
    freshMessage]

-- P7 (the product hypothesis in (13.9)): `11 ≠ 2 * 5` modulo `33` and the product of the
-- signatures on `2` and `5` is not a signature on `11`.
example : rsaEval 33 3 (rsaInvert 33 7 2 * rsaInvert 33 7 5 % 33) ≠ 11 % 33 := by decide

-- P7b (`% N` in `verify`): a digest need not be below `N`. The signature on the digest `37` has
-- `e`-th power `4 = 37 % 33`, so a test `σ ^ e % N = H m` without the reduction would reject it.
example : rsaEval 33 3 (rsaInvert 33 7 37) = 4 := by decide
example :
    (rsaSignature rsa33 fun m : ℕ => m).verify rsa33.publicKey 37 (rsaInvert 33 7 37) = true := by
  decide

-- P8 (messages of the unhashed scheme are residues): over `ℕ` with the digest `m ↦ m`, the
-- messages `4` and `37` have the same signature: the answers to the queries `37` and `1` give a
-- forgery on `4`.
example :
    ProbComp.eval ((rsaSignature rsa33 fun m : ℕ => m).eufCmaExperiment
      fun pk => rsaMultiplicativeForger pk 37 1 4) = PMF.pure true :=
  eval_eufCmaExperiment_rsaMultiplicativeForger rsa33 _ (by decide) (by decide) (by decide)

end CslibFrontierTests.Crypto.RSASignatureAttacks
