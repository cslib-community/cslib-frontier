/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.DiscreteLog.SchnorrGroup
import CslibFrontier.Crypto.Computational.DiffieHellman.Static
import CslibFrontier.Probability.PMF.UniformPoint
import Mathlib.Tactic.NormNum.Prime

/-!
# Static Diffie–Hellman and ElGamal key recovery: checked instances and probes

Concrete checks for `CslibFrontier/Crypto/Computational/DiffieHellman/Static.lean` under module
encapsulation:

* In any `ZMod q`-module `G`, a 0-query guess `pure c` wins `sdhExperiment` and (via
  `sdhToElGamalKeyRecovery`) `elGamalKeyRecoveryExperiment` with probability `1 / q`.
* In `ZMod 5` with generator `1`, the 1-query SDH adversary `queryOneSDH 5` wins with probability
  `1`, and `sdhToElGamalKeyRecovery` turns it into a 1-query ElGamal key-recovery adversary with
  advantage `1` whose queries all have second component `0`; `dlToSDH` and
  `elGamalKeyRecoveryToSDH` likewise preserve exact advantages and query budgets.
* Probe 1 shows that negating the first ciphertext component (`(-v, 0)` for `(1 / v, 1)`) is
  essential: querying `(v, 0)` instead drops the advantage of `queryOneSDH 5` from `1` to `1 / 5`.
* Probe 2 shows that the `+ 1` query in `isQueryBounded_elGamalKeyRecoveryToSDH` (`Q + 1`) is
  needed because `ElGamalKeyRecoveryAdversary` receives the public key `α • g` whereas
  `SDHAdversary` receives no initial group element.
* On the Schnorr group `d23` (`p = 23, q = 11, g = 2`), `elGamalSDHCiphertext` and
  `elGamalDecryptDet` recover `2 ^ 3 mod 23 = 8` on the subgroup generator `2`, while Probe 3
  shows that on the quadratic non-residue `5` outside the order-`11` subgroup,
  `elGamalDecryptDet` on `elGamalSDHCiphertext` (`13`) disagrees with `schnorrGroups.smul` (`10`).
-/

public section

namespace CslibFrontierTests.Crypto.StaticDH

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.PrimeOrderGroupFamily Turing.MultiTapeTM
open scoped NNReal ENNReal

section General

variable {G : Type} [AddCommGroup G] (q : ℕ) [NeZero q] [Module (ZMod q) G] (g : G)

/-- A 0-query SDH adversary that guesses a fixed exponent `c` wins with probability `1 / q`. -/
private theorem sdhAdvantage_pure (c : ZMod q) :
    sdhAdvantage q (G := G) (pure c) = (q : ℝ≥0)⁻¹ := by
  simp only [sdhAdvantage, Experiment.succProbability, sdhExperiment, ProbOracleComp.run_pure,
    ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform, PMF.pure_bind]
  rw [Game.succProbability, PMF.uniformOfFintype_bind_decide_eq_apply_true, ZMod.card,
    ENNReal.toNNReal_inv, ENNReal.toNNReal_natCast]

/-- Via `sdhToElGamalKeyRecovery`, the 0-query guess `c` recovers the ElGamal secret key with
probability `1 / q`. -/
private theorem elGamalKeyRecoveryAdvantage_sdhToElGamalKeyRecovery_pure (c : ZMod q) :
    elGamalKeyRecoveryAdvantage q g (sdhToElGamalKeyRecovery (pure c)) = (q : ℝ≥0)⁻¹ := by
  rw [elGamalKeyRecoveryAdvantage_sdhToElGamalKeyRecovery, sdhAdvantage_pure]

end General

/-! ### Concrete checks in `ZMod 5` with generator `1` -/

/-- The 1-query SDH adversary in `ZMod q` that queries `1` and returns the reply `α • 1 = α`. -/
private def queryOneSDH (q : ℕ) : SDHAdversary (ZMod q) q :=
  ProbOracleComp.query (spec := SDHSpec (ZMod q)) 1

private theorem isQueryBounded_queryOneSDH (q : ℕ) : (queryOneSDH q).IsQueryBounded 1 :=
  ProbOracleComp.IsQueryBounded.query 1

private theorem sdhAdvantage_queryOneSDH (q : ℕ) [NeZero q] :
    sdhAdvantage q (queryOneSDH q) = 1 := by
  simp only [sdhAdvantage, Experiment.succProbability, sdhExperiment, queryOneSDH,
    ProbOracleComp.run_query, sdhOracle, ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind,
    smul_eq_mul, mul_one, decide_true, PMF.bind_const]
  simp [Game.succProbability]

-- In `ZMod 5` with generator `1`, `sdhToElGamalKeyRecovery (queryOneSDH 5)` recovers the secret
-- key with probability `1` using `1` decryption query, and its converse `elGamalKeyRecoveryToSDH`
-- has SDH advantage `1` with budget `2 = 1 + 1`.
example :
    elGamalKeyRecoveryAdvantage 5 (1 : ZMod 5) (sdhToElGamalKeyRecovery (queryOneSDH 5)) = 1 ∧
      sdhAdvantage 5
        (elGamalKeyRecoveryToSDH (1 : ZMod 5) (sdhToElGamalKeyRecovery (queryOneSDH 5))) = 1 ∧
      (elGamalKeyRecoveryToSDH (1 : ZMod 5)
        (sdhToElGamalKeyRecovery (queryOneSDH 5))).IsQueryBounded 2 ∧
      ∀ u : ZMod 5, (sdhToElGamalKeyRecovery (queryOneSDH 5) u).IsQueryBounded 1 ∧
        (sdhToElGamalKeyRecovery (queryOneSDH 5) u).QueriesSatisfy (fun ct => ct.2 = 0) :=
  ⟨by rw [elGamalKeyRecoveryAdvantage_sdhToElGamalKeyRecovery, sdhAdvantage_queryOneSDH],
    by rw [sdhAdvantage_elGamalKeyRecoveryToSDH,
        elGamalKeyRecoveryAdvantage_sdhToElGamalKeyRecovery, sdhAdvantage_queryOneSDH],
    isQueryBounded_elGamalKeyRecoveryToSDH (1 : ZMod 5)
      (isQueryBounded_sdhToElGamalKeyRecovery (isQueryBounded_queryOneSDH 5)),
    fun u => ⟨isQueryBounded_sdhToElGamalKeyRecovery (isQueryBounded_queryOneSDH 5) u,
      queriesSatisfy_sdhToElGamalKeyRecovery (queryOneSDH 5) u⟩⟩

-- In `ZMod 5`, `dlToSDH 1 pure` wins `sdhExperiment` with probability `1` and makes `1` query.
example :
    sdhAdvantage 5 (dlToSDH (1 : ZMod 5) pure) = 1 ∧
      (dlToSDH (1 : ZMod 5) pure).IsQueryBounded 1 ∧
      (dlToSDH (1 : ZMod 5) pure).QueriesSatisfy (· = (1 : ZMod 5)) := by
  refine ⟨?_, isQueryBounded_dlToSDH 1 pure, queriesSatisfy_dlToSDH 1 pure⟩
  simp only [sdhAdvantage_dlToSDH, dlAdvantage, Experiment.succProbability, dlExperiment,
    ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind, smul_eq_mul, mul_one, decide_true,
    PMF.bind_const]
  simp [Game.succProbability]

/-! ### Probes for hypotheses and algebraic choices -/

-- Probe 1: negating the first ciphertext component (`(-v, 0)` for `(1 / v, 1)`) is essential.
-- Without negation, decrypting `(v, 0)` returns `-(α • v)`, which differs from `α • v` in `ZMod 5`
-- at `α = 1, v = 1`, and a reduction querying `(v, 0)` on `queryOneSDH 5` wins only when `-α = α`
-- (`α = 0`), with probability `1 / 5` instead of `1`.
example :
    elGamalDecryptValue 5 (1 : ZMod 5) ((1 : ZMod 5), (0 : ZMod 5)) ≠
      (1 : ZMod 5) • (1 : ZMod 5) := by
  decide

/-- A faulty key-recovery reduction that queries `(v, 0)` without negating `v`. -/
private def unnegatedReduction {q : ℕ} {G : Type} [AddCommGroup G] (A : SDHAdversary G q) :
    ElGamalKeyRecoveryAdversary G q :=
  fun _ => ProbOracleComp.simulate (fun v => ProbOracleComp.query (v, 0)) A

private theorem elGamalKeyRecoveryAdvantage_unnegated_queryOneSDH_zmod5 :
    elGamalKeyRecoveryAdvantage 5 (1 : ZMod 5) (unnegatedReduction (queryOneSDH 5)) = 1 / 5 := by
  have hiff (α : ZMod 5) : (-α = α) ↔ (0 : ZMod 5) = α := by decide +revert
  simp only [elGamalKeyRecoveryAdvantage, Experiment.succProbability, elGamalKeyRecoveryExperiment,
    unnegatedReduction, queryOneSDH, ProbOracleComp.run_simulate, ProbOracleComp.run_query,
    elGamalDecryptOracle, elGamalDecryptValue, zero_sub, smul_eq_mul, mul_one,
    ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform, PMF.pure_bind, hiff]
  rw [Game.succProbability, PMF.uniformOfFintype_bind_decide_eq_apply_true, ZMod.card,
    ENNReal.toNNReal_inv, ENNReal.toNNReal_natCast, one_div, Nat.cast_ofNat]

example :
    elGamalKeyRecoveryAdvantage 5 (1 : ZMod 5) (unnegatedReduction (queryOneSDH 5)) = 1 / 5 :=
  elGamalKeyRecoveryAdvantage_unnegated_queryOneSDH_zmod5

-- Probe 2: the extra query in `isQueryBounded_elGamalKeyRecoveryToSDH` (`Q + 1`) is needed
-- because `ElGamalKeyRecoveryAdversary` receives the public key `u = α • g` as input whereas
-- `SDHAdversary` receives no input: in `ZMod 5`, `dlToElGamalKeyRecovery pure` makes `0` decryption
-- queries and wins with probability `1` (and `elGamalKeyRecoveryToSDH 1` turns it into a 1-query
-- SDH adversary with advantage `1`), whereas every 0-query `pure c` SDH adversary wins with
-- probability `1 / 5`.
example (c : ZMod 5) :
    (∀ u : ZMod 5, (dlToElGamalKeyRecovery pure u).IsQueryBounded 0) ∧
      elGamalKeyRecoveryAdvantage 5 (1 : ZMod 5) (dlToElGamalKeyRecovery pure) = 1 ∧
      (elGamalKeyRecoveryToSDH (1 : ZMod 5) (dlToElGamalKeyRecovery pure)).IsQueryBounded 1 ∧
      sdhAdvantage 5 (elGamalKeyRecoveryToSDH (1 : ZMod 5) (dlToElGamalKeyRecovery pure)) = 1 ∧
      sdhAdvantage 5 (G := ZMod 5) (pure c) = 1 / 5 ∧
      elGamalKeyRecoveryAdvantage 5 (1 : ZMod 5) (sdhToElGamalKeyRecovery (pure c)) = 1 / 5 := by
  have hdl : elGamalKeyRecoveryAdvantage 5 (1 : ZMod 5) (dlToElGamalKeyRecovery pure) = 1 := by
    simp only [elGamalKeyRecoveryAdvantage_dlToElGamalKeyRecovery, dlAdvantage,
      Experiment.succProbability, dlExperiment, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.pure_bind, smul_eq_mul, mul_one, decide_true, PMF.bind_const]
    simp [Game.succProbability]
  refine ⟨isQueryBounded_dlToElGamalKeyRecovery pure, hdl,
    isQueryBounded_elGamalKeyRecoveryToSDH (1 : ZMod 5)
      (isQueryBounded_dlToElGamalKeyRecovery pure),
    by rw [sdhAdvantage_elGamalKeyRecoveryToSDH, hdl],
    by rw [sdhAdvantage_pure, one_div, Nat.cast_ofNat],
    by rw [elGamalKeyRecoveryAdvantage_sdhToElGamalKeyRecovery_pure, one_div, Nat.cast_ofNat]⟩

/-! ### Concrete checks and probe on `schnorrGroups` (`p = 23, q = 11, g = 2`) -/

/-- The Schnorr group of order `11` in `(ZMod 23)ˣ`, generated by `2`. -/
def d23 : schnorrGroups.Desc :=
  ⟨(23, 11, 2), ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩

-- Family-level games and polynomial-time certificate instantiated on `schnorrGroups`.
example (setup : ℕ → PMF schnorrGroups.Desc) (adversary : schnorrGroups.SDHAdversary) (n : ℕ) :
    schnorrGroups.elGamalKeyRecoveryGame setup
        (fun m d => sdhToElGamalKeyRecovery (adversary m d)) n =
      schnorrGroups.sdhGame setup adversary n ∧
    schnorrGroups.sdhGame setup
        (fun m d => elGamalKeyRecoveryToSDH (schnorrGroups.generator d)
          (sdhToElGamalKeyRecovery (adversary m d))) n =
      schnorrGroups.sdhGame setup adversary n ∧
    ComputableInPolyTime
      (fun p : schnorrGroups.Desc × List Bool => schnorrGroups.elGamalSDHCiphertext p.1 p.2)
      (encPair schnorrGroups.encDesc encBits) encBits :=
  ⟨schnorrGroups.elGamalKeyRecoveryGame_sdhToElGamalKeyRecovery setup adversary n,
    by rw [schnorrGroups.sdhGame_elGamalKeyRecoveryToSDH,
        schnorrGroups.elGamalKeyRecoveryGame_sdhToElGamalKeyRecovery],
    schnorrGroups.computableInPolyTime_elGamalSDHCiphertext⟩

-- On the subgroup generator `g = 2`, `elGamalDecrypt_neg_zero` and `elGamalDecryptDet` on
-- `elGamalSDHCiphertext` recover `(3 : ZMod 11) • g` (`2 ^ 3 mod 23 = 8`).
example :
    schnorrGroups.elGamalDecrypt d23 3 (-schnorrGroups.generator d23, 0) =
      (3 : ZMod (schnorrGroups.order d23)) • schnorrGroups.generator d23 ∧
    schnorrGroups.elGamalDecryptDet (fun _ => d23) 0 (encNat 3)
      (schnorrGroups.elGamalSDHCiphertext d23
        (schnorrGroups.encode d23 (schnorrGroups.generator d23))) =
      schnorrGroups.encode d23
        ((3 : ZMod (schnorrGroups.order d23)) • schnorrGroups.generator d23) :=
  ⟨schnorrGroups.elGamalDecrypt_neg_zero d23 3 (schnorrGroups.generator d23),
    (schnorrGroups.elGamalDecryptDet_elGamalSDHCiphertext (fun _ => d23) 0
      (encNat 3) (schnorrGroups.generator d23)).trans rfl⟩

-- Concrete bit-level check on `d23`: `elGamalSDHCiphertext d23 (Nat.bits 2)` builds the encoded
-- ciphertext `(12, 1)` (`12 = 2⁻¹ mod 23`), and `elGamalDecryptDet` under secret key `3` returns
-- `Nat.bits 8 = schnorrGroups.smul (d23, 3, Nat.bits 2)`.
example :
    schnorrGroups.elGamalSDHCiphertext d23 (Nat.bits 2) =
      encPair encBits encBits (Nat.bits 12, Nat.bits 1) ∧
    schnorrGroups.elGamalDecryptDet (fun _ => d23) 0 (encNat 3)
      (schnorrGroups.elGamalSDHCiphertext d23 (Nat.bits 2)) = Nat.bits 8 ∧
    schnorrGroups.smul (d23, 3, Nat.bits 2) = Nat.bits 8 := by
  decide

-- Probe 3: `v ∈ Set.range (F.encode d)` is needed in `decodeElGamal_elGamalSDHCiphertext` and
-- `elGamalDecryptDet_elGamalSDHCiphertext`. In `(ZMod 23)ˣ`, `5` has order `22 = 2 * 11`, so
-- `Nat.bits 5` is not in the order-`11` Schnorr subgroup (`5 ^ 11 mod 23 = 22 ≠ 1`): on
-- `Nat.bits 5`, `elGamalDecryptDet` on `elGamalSDHCiphertext` under secret key `3` returns
-- `Nat.bits 13` (`-5 ^ 3 mod 23`), whereas `schnorrGroups.smul (d23, 3, Nat.bits 5)` returns
-- `Nat.bits 10` (`5 ^ 3 mod 23`).
example :
    schnorrGroups.elGamalDecryptDet (fun _ => d23) 0 (encNat 3)
      (schnorrGroups.elGamalSDHCiphertext d23 (Nat.bits 5)) = Nat.bits 13 ∧
    schnorrGroups.smul (d23, 3, Nat.bits 5) = Nat.bits 10 ∧
    schnorrGroups.elGamalDecryptDet (fun _ => d23) 0 (encNat 3)
      (schnorrGroups.elGamalSDHCiphertext d23 (Nat.bits 5)) ≠
      schnorrGroups.smul (d23, 3, Nat.bits 5) := by
  decide

end CslibFrontierTests.Crypto.StaticDH
