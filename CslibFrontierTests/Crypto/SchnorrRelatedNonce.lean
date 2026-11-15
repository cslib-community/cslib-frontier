/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.DiscreteLog.SchnorrGroup
import CslibFrontier.Crypto.Computational.SchnorrRelatedNonce
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF
import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for Schnorr signatures with related nonces

Exercises `relatedNonceExtract` over `ZMod 7` (ordinary special soundness at `a = 1, b = 0`, key
recovery at equal challenges with `a ≠ 1`, and zero output when `c₁ = a * c₀`), probes the
`m₀ ≠ m₁` requirement of `one_sub_inv_card_le_succProbability_relatedNonceGame` over `ZMod 5`
(`relatedNonceGame_same_message`), and evaluates `ofBits_schnorrRelatedNonceExtractWord` on concrete
words in `schnorrGroups`; a word-level attack game is not part of these modules.
-/

namespace CslibFrontierTests.Crypto.SchnorrRelatedNonce

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.Protocols SigmaProtocol OracleComp
  ROMSignature Turing.MultiTapeTM
open scoped ENNReal NNReal

section Algebra

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- `a = 1`, `b = 0` (the same nonce twice) is the extractor of special soundness. -/
example {q : ℕ} (c₀ z₀ c₁ z₁ : ZMod q) :
    relatedNonceExtract 1 0 c₀ z₀ c₁ z₁ =
      linearExtract (Function.Embedding.refl (ZMod q)) (0 : ZMod q) (0 : ZMod q) c₀ z₀ c₁ z₁ := by
  simp [relatedNonceExtract, linearExtract]

/-- A numeric instance over `ZMod 7`: key `3`, nonce `2`, `a = 2`, `b = 5`, challenges `1` and
`4`. -/
example : relatedNonceExtract (2 : ZMod 7) 5 1 (2 + 1 * 3) 4 (2 * 2 + 5 + 4 * 3) = 3 := by
  rw [relatedNonceExtract, inv_mul_eq_iff_eq_mul₀ (by decide)]
  decide

/-- The condition is `a * c₀ ≠ c₁`, not `c₀ ≠ c₁`: equal challenges work when `a ≠ 1`. -/
example : relatedNonceExtract (2 : ZMod 7) 5 1 (2 + 1 * 3) 1 (2 * 2 + 5 + 1 * 3) = 3 := by
  rw [relatedNonceExtract, inv_mul_eq_iff_eq_mul₀ (by decide)]
  decide

/-- Distinct challenges fail when `c₁ = a * c₀`. -/
example : relatedNonceExtract (2 : ZMod 7) 5 1 (2 + 1 * 3) 2 (2 * 2 + 5 + 2 * 3) = 0 :=
  relatedNonceExtract_of_eq 2 5 1 _ _

end Algebra

section SameMessageProbe

variable {q : ℕ} [Fact q.Prime] {G C M : Type} [AddCommGroup G] [Module (ZMod q) G]
  [DecidableEq G] [DecidableEq M] [Fintype C] [Nonempty C]

/-- The same message signed twice with the same nonce (`a = 1`, `b = 0`): the two signatures are
equal, the adversary returns `0`, and it wins exactly when the signing key is `0`. -/
theorem relatedNonceGame_same_message (ι : C ↪ ZMod q) (g : G) (m : M) :
    relatedNonceGame ι g 1 0 m m =
      (PMF.uniformOfFintype (ZMod q)).map fun α => decide ((0 : ZMod q) = α) := by
  have hmiss : ∀ (p : M × G) (cache : List ((M × G) × C)), cache.lookup p = none →
      (oracle C p).run cache =
        (PMF.uniformOfFintype C).bind fun c => PMF.pure (c, (p, c) :: cache) := by
    intro p cache h
    change memoize (fun _ => PMF.uniformOfFintype C) p cache = _
    rw [memoize_of_none _ _ _ h]
    rfl
  have hhit : ∀ (p : M × G) (cache : List ((M × G) × C)) (c : C), cache.lookup p = some c →
      (oracle C p).run cache = PMF.pure (c, cache) := by
    intro p cache c h
    change memoize (fun _ => PMF.uniformOfFintype C) p cache = _
    rw [memoize_of_some _ _ _ _ h]
    rfl
  simp only [relatedNonceGame, relatedNonceAttacker, schnorrROMScheme, fiatShamir, interpret_map,
    interpret_query, interpret_bind, interpret_pure, StateT.run_map, StateT.run_bind,
    StateT.run_pure, pmf_norm, PMF.monad_map_eq_map, PMF.bind_bind, PMF.pure_bind,
    PMF.map, Function.Embedding.refl_apply, schnorrKeyGen, one_mul, add_zero]
  refine congrArg (PMF.bind _) (funext fun α => ?_)
  have hmiss' : ∀ r : ZMod q, (oracle C (m, r • g)).run [] =
      (PMF.uniformOfFintype C).bind fun c => PMF.pure (c, [((m, r • g), c)]) :=
    fun r => hmiss _ [] rfl
  have hhit' : ∀ (r : ZMod q) (c : C), (oracle C (m, r • g)).run [((m, r • g), c)] =
      PMF.pure (c, [((m, r • g), c)]) :=
    fun r c => hhit _ _ c (by simp [List.lookup])
  have hzero : ∀ (c z₀ z₁ : ZMod q), relatedNonceExtract (1 : ZMod q) 0 c z₀ c z₁ = 0 := by
    intro c z₀ z₁
    simp [relatedNonceExtract]
  simp only [hmiss', PMF.bind_bind, PMF.pure_bind, hhit', hzero, PMF.bind_const]

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- With `m₀ = m₁` the bound of `one_sub_inv_card_le_succProbability_relatedNonceGame` fails:
over `ZMod 5` with all five challenges the success probability is `1 / 5`, not at least `4 / 5`. -/
example :
    Game.succProbability (relatedNonceGame (Function.Embedding.refl (ZMod 5)) (1 : ZMod 5) 1 0
      () ()) = 1 / 5 := by
  rw [relatedNonceGame_same_message, Game.succProbability, PMF.map_apply]
  simp only [true_eq_decide_iff, PMF.uniformOfFintype_apply, ZMod.card, Nat.cast_ofNat,
    tsum_fintype, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, ENNReal.toNNReal_inv, one_div,
    inv_inj]
  exact ENNReal.toNNReal_ofNat 5

end SameMessageProbe

section WordExtraction

local instance : Fact (Nat.Prime 11) := ⟨by decide⟩

private def d23 : SchnorrGroup.Desc :=
  ⟨(23, 11, 2), ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩

/-- Word-level extraction in `schnorrGroups` over `d23` (order `11`): with key `3`, nonce `2`,
`a = 2`, `b = 5`, challenges `1` and `4`, responses `z₀ = 5` and `z₁ = 10 ≡ 21 (mod 11)`,
`ofBits_schnorrRelatedNonceExtractWord` decodes the recovered key to `3 : ZMod 11`. -/
example :
    ((ofBits (schnorrGroups.schnorrRelatedNonceExtractWord
      (d23, Nat.bits 2, Nat.bits 5, Nat.bits 1, Nat.bits 5, Nat.bits 4, Nat.bits 10)) : ℕ) :
      ZMod (schnorrGroups.order d23)) = 3 := by
  rw [schnorrGroups.ofBits_schnorrRelatedNonceExtractWord d23 _ _ _ _ _ _ (by decide)]
  change relatedNonceExtract (2 : ZMod 11) 5 1 5 4 10 = 3
  rw [relatedNonceExtract, inv_mul_eq_iff_eq_mul₀ (by decide)]
  decide

end WordExtraction

end CslibFrontierTests.Crypto.SchnorrRelatedNonce
