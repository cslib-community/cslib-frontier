/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Computational.SchnorrRelatedNonce
public import CslibFrontier.Crypto.Computational.SchnorrSignature.NativeROM
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.WordsRoundTrip
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.OfBits
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.UniformPoint

/-!
# Key recovery from leaked Schnorr signing randomness

In Boneh–Shoup [BonehShoup2023], Section 21.2 (p. 861), leaking the random bits used to
generate a Schnorr signature lets an adversary recover the long-term signing key directly from the
signing equation `z = r + c * α` ([BonehShoup2023], Section 19.2, pp. 762–763).

This module specializes `schnorrRelatedNonceExtractWord` (`a = 0`, `b = r`) to give the word-level
recovery theorem on honest signatures, an explicit one-query `WordOracleComp` adversary with a
uniform strict oracle-PPT certificate `IsOraclePPTOn`, and the concrete random-oracle key-recovery
game and bound.

## Differences from the book

* **Success probability `1 - 2 ^ (-m)`:** Rather than succeeding with probability `1`, the word
  adversary succeeds with probability at least `1 - 2 ^ (-m)` against an `m`-bit random oracle,
  because the oracle can output the all-zero `m`-bit challenge word, on which `z = r` is
  independent of the signing key.
* **Reduced nonce word:** The leaked randomness input is the reduced scalar word
  `(r % F.order d).bits`, which the raw `sampleExp` output `r` determines.
* **Fixed message and omitted public key:** `schnorrLeakedNonceWordGame` signs one fixed message
  `msg` and gives `(d, m, msg, sig, rBits)` without the public key.
* **Standing condition `2 ^ m ≤ F.order d`:** Inherited from `schnorrWordROMScheme`
  (`CslibFrontier/Crypto/Computational/SchnorrSignature/NativeROM.lean`), ensuring distinct `m`-bit
  challenges map to distinct residues modulo `F.order d`.

## Main definitions

* `schnorrLeakedNonceWordAdversary`: one-query word-level random-oracle adversary recovering the
  secret-key word from a signature and leaked nonce word.
* `schnorrLeakedNonceWordGame`: native `WordOracleComp` leaked-randomness key-recovery game over an
  `m`-bit stateful random oracle.

## Main results

* `schnorrRelatedNonceExtractWord_schnorrSignCoins`: `schnorrRelatedNonceExtractWord` at `a = 0`,
  `b = r` recovers `F.encScalar d α` on an honest signature when the challenge word is nonzero
  modulo `F.order d`.
* `isOraclePPTOn_schnorrLeakedNonceWordAdversary`: `schnorrLeakedNonceWordAdversary` is uniform
  strict oracle PPT with unary `m`.
* `one_sub_inv_two_pow_le_succProbability_schnorrLeakedNonceWordGame`: against an `m`-bit stateful
  random oracle with `2 ^ m ≤ F.order d`, `schnorrLeakedNonceWordAdversary` succeeds with
  probability at least `1 - (2 ^ m : ℝ≥0)⁻¹`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 21.2 (p. 861) and Section 19.2 (pp. 762–763).
-/

public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.Protocols SigmaProtocol ROMSignature
open Turing.MultiTapeTM
open scoped NNReal ENNReal

/-- `schnorrRelatedNonceExtractWord` at `a = 0`, `b = r` returns the secret-key word from an
honest signature whose challenge is nonzero modulo `F.order d`. -/
theorem schnorrRelatedNonceExtractWord_schnorrSignCoins (F : PrimeOrderGroupFamily)
    (d : F.Desc) (α r : ZMod (F.order d)) (msg roOut : List Bool)
    (hc : (ofBits roOut : ZMod (F.order d)) ≠ 0) :
    F.schnorrRelatedNonceExtractWord
      (d, [], F.encScalar d r, [], [], roOut,
        (F.schnorrSignCoins (d, F.encScalar d α, msg, F.encScalar d r, roOut)).2) =
      F.encScalar d α := by
  have hnil : (ofBits ([] : List Bool) : ZMod (F.order d)) = 0 := Nat.cast_zero
  have hc' : (ofBits ([] : List Bool) : ZMod (F.order d)) *
      (ofBits ([] : List Bool) : ZMod (F.order d)) ≠ (ofBits roOut : ZMod (F.order d)) := by
    simpa [hnil] using hc.symm
  rw [F.schnorrRelatedNonceExtractWord_eq_encScalar d [] (F.encScalar d r) [] [] roOut _ hc',
    F.schnorrSignCoins_encScalar]
  refine congrArg (F.encScalar d) ?_
  simp only [encScalar, Function.Embedding.coeFn_mk, encNat_apply, ofBits_bits,
    ZMod.natCast_zmod_val, relatedNonceExtract, hnil, mul_zero, zero_add, zero_sub, inv_neg]
  field_simp
  ring

/-- One-query word-level ROM adversary taking `(d, m, msg, sig, rBits)` and recovering the
secret-key word from `sig` and the leaked reduced randomness word `rBits`. -/
def schnorrLeakedNonceWordAdversary (F : PrimeOrderGroupFamily) :
    F.Desc × ℕ × List Bool × List Bool × List Bool → WordOracleComp Unit (List Bool)
  | (d, m, msg, sig, rBits) =>
    let sigPair := (Decoder.bits.pair Decoder.bits).decode sig
    (fun roOut => F.schnorrRelatedNonceExtractWord (d, [], rBits, [], [], roOut, sigPair.2)) <$>
      (List.take m <$> ProbOracleComp.query ((), encPair encBits encBits (msg, sigPair.1)))

/-- Efficiency certificate: `schnorrLeakedNonceWordAdversary` is uniform strict oracle PPT
with `m` encoded in unary. -/
theorem isOraclePPTOn_schnorrLeakedNonceWordAdversary (F : PrimeOrderGroupFamily) :
    IsOraclePPTOn
      (encPair F.encDesc (encPair encUnary (encPair encBits (encPair encBits encBits))))
      encBits F.schnorrLeakedNonceWordAdversary := by
  have hdef : F.schnorrLeakedNonceWordAdversary = fun input =>
      (fun roOut => F.schnorrRelatedNonceExtractWord (input.1, [], input.2.2.2.2, [], [], roOut,
        ((Decoder.bits.pair Decoder.bits).decode input.2.2.2.1).2)) <$>
        (List.take input.2.1 <$> ProbOracleComp.query ((), encPair encBits encBits
          (input.2.2.1, ((Decoder.bits.pair Decoder.bits).decode input.2.2.2.1).1))) := by
    funext ⟨d, m, msg, sig, rBits⟩
    rfl
  rw [hdef]
  let E := encPair F.encDesc (encPair encUnary (encPair encBits (encPair encBits encBits)))
  have hreq : ComputableInPolyTime
      (fun x : F.Desc × ℕ × List Bool × List Bool × List Bool =>
        encPair encBits encBits
          (x.2.2.1, ((Decoder.bits.pair Decoder.bits).decode x.2.2.2.1).1))
      E encBits :=
    ((by fun_prop : ComputableInPolyTime _ E (encPair encBits encBits))).encoding_comp
  refine (IsOraclePPTOn.query_take () hreq (by fun_prop)).map_with ?_
  exact F.computableInPolyTime_schnorrRelatedNonceExtractWord.comp
    (g := fun p : (F.Desc × ℕ × List Bool × List Bool × List Bool) × List Bool =>
      (p.1.1, [], p.1.2.2.2.2, [], [], p.2,
        ((Decoder.bits.pair Decoder.bits).decode p.1.2.2.2.1).2))
    (by fun_prop)

/-- Native `WordOracleComp` leaked-randomness key-recovery game: `schnorrSigKeyGen` draws
`(pk, sk)`, `sampleExp` draws signing randomness `r`, signing executes the exact steps of
`schnorrROMSign` (`CslibFrontier/Crypto/Computational/SchnorrSignature/NativeROM.lean`) against an
`m`-bit stateful random oracle using the reduced nonce word `rBits := (r % F.order d).bits`, and
`adversary (d, m, msg, sig, rBits)` queries the same oracle to recover `sk`. -/
noncomputable def schnorrLeakedNonceWordGame (F : PrimeOrderGroupFamily) (n : ℕ) (d : F.Desc)
    (m : ℕ) (msg : List Bool)
    (adversary : F.Desc × ℕ × List Bool × List Bool × List Bool →
      WordOracleComp Unit (List Bool)) : Game := do
  let keys ← ProbComp.eval (F.schnorrSigKeyGen n d)
  let r ← ProbComp.eval (F.sampleExp n d)
  let rBits := (r % F.order d).bits
  let res ← ProbOracleComp.runWith
    (fun (q : Unit × List Bool) (cache : List (List Bool × BitString m)) =>
      (ROMSignature.oracle (BitString m) q.2 cache).map (Prod.map List.ofFn id))
    (do
      let t := F.schnorrCommitBits (d, rBits)
      let answer ← ProbOracleComp.query ((), encPair encBits encBits (msg, t))
      let sig := encPair encBits encBits
        (F.schnorrSignCoins (d, keys.2, msg, rBits, answer.take m))
      let sk' ← adversary (d, m, msg, sig, rBits)
      return decide (sk' = keys.2))
    []
  return res.1

/-- Concrete success probability of `schnorrLeakedNonceWordAdversary` against an `m`-bit stateful
random oracle when `2 ^ m ≤ F.order d`: the loss `2 ^ (-m)` is the zero-challenge event, on which
`z = r` is independent of the secret key. -/
theorem one_sub_inv_two_pow_le_succProbability_schnorrLeakedNonceWordGame
    (F : PrimeOrderGroupFamily) (n : ℕ) (d : F.Desc) {m : ℕ} (hm : 2 ^ m ≤ F.order d)
    (msg : List Bool) :
    1 - (2 ^ m : ℝ≥0)⁻¹ ≤
      Game.succProbability
        (F.schnorrLeakedNonceWordGame n d m msg F.schnorrLeakedNonceWordAdversary) := by
  rw [← ENNReal.coe_le_coe, Game.coe_succProbability_ennreal]
  push_cast
  unfold schnorrLeakedNonceWordGame
  refine PMF.le_bind_apply_on_support _ fun keys hkeys =>
    PMF.le_bind_apply_on_support _ fun r _ => ?_
  rw [F.eval_schnorrSigKeyGen, PMF.mem_support_map_iff] at hkeys
  obtain ⟨α, _, rfl⟩ := hkeys
  let rZ : ZMod (F.order d) := r
  have hrBits : (r % F.order d).bits = F.encScalar d rZ := by
    simp only [rZ, encScalar, Function.Embedding.coeFn_mk, encNat_apply, ZMod.val_natCast]
  let g : Game :=
    (PMF.uniformOfFintype (BitString m)).bind fun c =>
      PMF.pure (decide (F.schnorrRelatedNonceExtractWord
        (d, [], F.encScalar d rZ, [], [], List.ofFn c,
          (F.schnorrSignCoins (d, F.encScalar d α, msg, F.encScalar d rZ,
            List.ofFn c)).2) = F.encScalar d α))
  have hrun : (ProbOracleComp.runWith
      (fun (q : Unit × List Bool) (cache : List (List Bool × BitString m)) =>
        (ROMSignature.oracle (BitString m) q.2 cache).map (Prod.map List.ofFn id))
      (do
        let t := F.schnorrCommitBits (d, (r % F.order d).bits)
        let answer ← ProbOracleComp.query ((), encPair encBits encBits (msg, t))
        let sig := encPair encBits encBits
          (F.schnorrSignCoins (d, F.encScalar d α, msg, (r % F.order d).bits, answer.take m))
        let sk' ← F.schnorrLeakedNonceWordAdversary
          (d, m, msg, sig, (r % F.order d).bits)
        return decide (sk' = F.encScalar d α))
      []).bind (fun res => PMF.pure res.1) = g := by
    have hor1 (q : List Bool) : oracle (BitString m) q [] =
        (PMF.uniformOfFintype (BitString m)).bind fun c => PMF.pure (c, [(q, c)]) :=
      ROMSignature.run_oracle_of_lookup_eq_none rfl
    have hor2 (q : List Bool) (c : BitString m) : oracle (BitString m) q [(q, c)] =
        PMF.pure (c, [(q, c)]) :=
      ROMSignature.run_oracle_of_lookup_eq_some (by simp [List.lookup])
    simp only [g, hrBits, schnorrLeakedNonceWordAdversary, ProbOracleComp.runWith_bind,
      ProbOracleComp.runWith_map, ProbOracleComp.runWith_query, ProbOracleComp.runWith_pure]
    rw [hor1]
    simp only [PMF.map_bind, PMF.pure_map, PMF.bind_bind, PMF.pure_bind]
    congr 1 with c
    simp only [Prod.map, id_eq, Decoder.decode_enc, F.schnorrCommitBits_encScalar,
      F.schnorrSignCoins_encScalar]
    rw [hor2]
    simp only [PMF.pure_map, PMF.pure_bind, Prod.map, id_eq,
      List.take_of_length_le (List.length_ofFn (f := c)).le]
  dsimp only [Bind.bind, Pure.pure] at hrun ⊢
  rw [hrun]
  let fail : BitString m → Bool := fun c =>
    !(decide (F.schnorrRelatedNonceExtractWord
      (d, [], F.encScalar d rZ, [], [], List.ofFn c,
        (F.schnorrSignCoins (d, F.encScalar d α, msg, F.encScalar d rZ, List.ofFn c)).2) =
      F.encScalar d α))
  have ofBits_eq_zero_of_fail {c : BitString m} (hc : fail c = true) :
      ofBits (List.ofFn c) = 0 := by
    by_contra hne
    have hlt : ofBits (List.ofFn c) < F.order d :=
      lt_of_lt_of_le (by simpa only [List.length_ofFn] using ofBits_lt_two_pow (List.ofFn c)) hm
    have hmod : (ofBits (List.ofFn c) : ZMod (F.order d)) ≠ 0 := fun hz =>
      hne (Nat.eq_zero_of_dvd_of_lt ((CharP.cast_eq_zero_iff _ (F.order d) _).mp hz) hlt)
    simp only [fail, Bool.not_eq_true', decide_eq_false_iff_not] at hc
    exact hc (F.schnorrRelatedNonceExtractWord_schnorrSignCoins d α rZ msg (List.ofFn c) hmod)
  have hsub : {c : BitString m | fail c = true}.Subsingleton := by
    intro c₀ hc₀ c₁ hc₁
    have heq : ofBits (List.ofFn c₀) = ofBits (List.ofFn c₁) :=
      (ofBits_eq_zero_of_fail hc₀).trans (ofBits_eq_zero_of_fail hc₁).symm
    rw [ofBits_ofFn, ofBits_ofFn] at heq
    exact (BitString.equivFin m).injective (Fin.ext heq)
  have hfail := Cslib.Probability.PMF.uniformOfFintype_bind_pure_apply_true_le hsub
  simp only [BitString.card, Nat.cast_pow, Nat.cast_ofNat] at hfail
  have hfalse :
      g false = ((PMF.uniformOfFintype (BitString m)).bind fun c => PMF.pure (fail c)) true := by
    simp only [g, fail, PMF.bind_apply, PMF.pure_apply]
    refine tsum_congr fun c => ?_
    cases decide (F.schnorrRelatedNonceExtractWord (d, [], F.encScalar d rZ, [], [], List.ofFn c,
      (F.schnorrSignCoins (d, F.encScalar d α, msg, F.encScalar d rZ, List.ofFn c)).2) =
        F.encScalar d α) <;> simp
  have hsum : g true + g false = 1 := by
    simpa [tsum_bool, add_comm] using PMF.tsum_coe g
  rw [← hfalse] at hfail
  calc
    (1 - (2 ^ m : ℝ≥0∞)⁻¹ : ℝ≥0∞) ≤ 1 - g false := tsub_le_tsub_left hfail 1
    _ = g true := by rw [← hsum, ENNReal.add_sub_cancel_right (PMF.apply_ne_top _ _)]

end Cslib.Crypto.PrimeOrderGroupFamily
