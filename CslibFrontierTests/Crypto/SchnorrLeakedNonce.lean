/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.SchnorrLeakedNonce
import CslibFrontier.Crypto.Computational.DiscreteLog.SchnorrGroup
import CslibFrontier.Crypto.Protocols.SigmaProtocol.RelatedNonce
import CslibFrontier.Crypto.Protocols.SigmaProtocol.SchnorrSignature
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for Schnorr key recovery from leaked signing randomness

Exercises the typed `a = 0` specializations of `relatedNonceExtract` and `relatedNonceGame`,
the `schnorrROMSign` signing equivalence for `schnorrLeakedNonceWordGame`, concrete word
extraction on `schnorrGroups`, necessity of nonzero challenges and `2 ^ m ≤ F.order d`, and
concrete application of both the PPT certificate and the `1 - 2⁻ᵐ` key-recovery bound.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.SchnorrLeakedNonce

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.Protocols SigmaProtocol ROMSignature
open Turing.MultiTapeTM
open scoped NNReal

section Typed

variable {q : ℕ} [Fact q.Prime] {G C M : Type} [AddCommGroup G] [Module (ZMod q) G]
  [DecidableEq G] [DecidableEq M] [Fintype C] [Nonempty C]

-- Leaking a known nonce `b` specializes Exercise 19.1 (`relatedNonceGame`) to `a = 0`.
example (ι : C ↪ ZMod q) (g : G) (b : ZMod q) {m₀ m₁ : M} (hm : m₀ ≠ m₁) :
    1 - (Fintype.card C : ℝ≥0)⁻¹ ≤ Game.succProbability (relatedNonceGame ι g 0 b m₀ m₁) :=
  one_sub_inv_card_le_succProbability_relatedNonceGame ι g 0 b hm

-- The honest Schnorr response with leaked nonce `r` and nonzero challenge recovers `α`.
example (ι : C ↪ ZMod q) (g u : G) (α r : ZMod q) {c : C} (hc : ι c ≠ 0) :
    relatedNonceExtract 0 r (ι c) ((schnorr ι g).respond α u (0 : ZMod q) c) (ι c)
      ((schnorr ι g).respond α u ((0 : ZMod q) * 0 + r) c) = α :=
  relatedNonceExtract_respond (ι := ι) (g := g) α u 0 0 r (c₀ := c) (c₁ := c)
    (by rw [zero_mul]; exact hc.symm)

-- An accepting transcript with leaked nonce `r` and nonzero challenge extracts a witness for `u`.
example (ι : C ↪ ZMod q) {g u : G} {r : ZMod q} {c : C} {z : ZMod q}
    (hacc : (schnorr ι g).Accepts u (r • g) c z) (hc : ι c ≠ 0) :
    relatedNonceExtract 0 r (ι c) z (ι c) z • g = u :=
  relatedNonceExtract_smul (ι := ι) (g := g) (u := u) (t₀ := r • g) (t₁ := r • g)
    (a := 0) (b := r) hacc hacc (by simp only [zero_smul, zero_add])
    (by rw [zero_mul]; exact hc.symm)

end Typed

-- Zero challenge fails to invert modulo `5`, showing necessity of `ι c ≠ 0`.
example :
    let z :=
      (schnorr (Function.Embedding.refl (ZMod 5)) (1 : ZMod 5)).respond 1 1 (2 : ZMod 5) 0
    relatedNonceExtract (0 : ZMod 5) 2 0 z 0 z ≠ 1 := by
  decide

-- Signing inside `schnorrLeakedNonceWordGame` matches `schnorrROMSign` definitionally.
example (F : PrimeOrderGroupFamily) (n : ℕ) (d : F.Desc) (m : ℕ) (sk msg : List Bool) :
    F.schnorrROMSign n d m sk msg = (do
      let r ← ProbOracleComp.sample (F.sampleExp n d)
      let rBits := (r % F.order d).bits
      let t := F.schnorrCommitBits (d, rBits)
      let answer ← ProbOracleComp.query ((), encPair encBits encBits (msg, t))
      return encPair encBits encBits (F.schnorrSignCoins (d, sk, msg, rBits, answer.take m))) :=
  rfl

private def d23 : schnorrGroups.Desc :=
  ⟨(23, 11, 2), ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩

-- On `d23` (`q = 11`), `schnorrRelatedNonceExtractWord_schnorrSignCoins` recovers `sk = 10`
-- from an honest signature with leaked nonce `r = 4` and challenge `c = 3`.
example :
    schnorrGroups.schnorrRelatedNonceExtractWord
      (d23, [], schnorrGroups.encScalar d23 4, [], [], Nat.bits 3,
        (schnorrGroups.schnorrSignCoins
          (d23, schnorrGroups.encScalar d23 10, [true, false],
            schnorrGroups.encScalar d23 4, Nat.bits 3)).2) =
      schnorrGroups.encScalar d23 10 := by
  apply schnorrGroups.schnorrRelatedNonceExtractWord_schnorrSignCoins
  decide

-- When `2 ^ m > q` (`q = 3, m = 2`), two of the four `m`-bit challenges reduce to `0 mod 3`,
-- so the `1 - 2⁻ᵐ` bound fails (`2 / 4 < 3 / 4`).
example :
    ((Finset.univ : Finset (BitString 2)).filter
      fun c => (ofBits (List.ofFn c) : ZMod 3) ≠ 0).card = 2 := by
  decide

-- Applying the concrete key-recovery bound on `d23` with `m = 3` (`2 ^ 3 ≤ 11`) yields `7 / 8`.
example (n : ℕ) (msg : List Bool) :
    (7 / 8 : ℝ≥0) ≤
      Game.succProbability
        (schnorrGroups.schnorrLeakedNonceWordGame n d23 3 msg
          schnorrGroups.schnorrLeakedNonceWordAdversary) := by
  have hm : 2 ^ 3 ≤ schnorrGroups.order d23 := by decide
  have h := schnorrGroups.one_sub_inv_two_pow_le_succProbability_schnorrLeakedNonceWordGame
    n d23 hm msg
  have hadd : (7 / 8 : ℝ≥0) + (2 ^ 3 : ℝ≥0)⁻¹ ≤ 1 := by norm_num
  exact le_of_add_le_add_right (hadd.trans (tsub_le_iff_right.mp h))

-- Fixing `(d23, 3)` via `IsOraclePPTOn.preprocess` preserves the uniform strict oracle-PPT
-- certificate of `schnorrLeakedNonceWordAdversary`.
example :
    IsOraclePPTOn (encPair encBits (encPair encBits encBits)) encBits
      (fun x : List Bool × List Bool × List Bool =>
        schnorrGroups.schnorrLeakedNonceWordAdversary (d23, 3, x.1, x.2.1, x.2.2)) := by
  have hpre : ComputableInPolyTime
      (fun x : List Bool × List Bool × List Bool => (d23, 3, x.1, x.2.1, x.2.2))
      (encPair encBits (encPair encBits encBits))
      (encPair schnorrGroups.encDesc
        (encPair encUnary (encPair encBits (encPair encBits encBits)))) := by
    fun_prop
  exact (schnorrGroups.isOraclePPTOn_schnorrLeakedNonceWordAdversary).preprocess hpre

end CslibFrontierTests.Crypto.SchnorrLeakedNonce
