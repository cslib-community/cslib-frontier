/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
public import CslibFrontier.Crypto.Computational.NaorReingold
public import CslibFrontier.Crypto.Computational.DiffieHellman.Order
public import CslibFrontier.Crypto.Computational.ElGamal.KDF
public import CslibFrontier.Crypto.Computational.PseudorandomFunction.RandomOracle
import CslibFrontier.Computability.Probabilistic.LinearHash
import CslibFrontier.Computability.Probabilistic.Memoize
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.Oracle.RunState
import CslibFrontier.Computability.Probabilistic.Oracle.Substitution
import CslibFrontier.Computability.Probabilistic.Repeat
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Exponential
import CslibFrontier.Crypto.Game.CloseTo
import CslibFrontier.Crypto.Game.Hybrid
import CslibFrontier.Crypto.Game.Statistical
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Languages.Probabilistic.Presample
import CslibFrontier.Languages.Probabilistic.RandomOracle.Probabilistic
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.Product
import CslibFrontier.Probability.StatisticalDistance.Product
import CslibFrontier.Tactic.EncLen
import CslibFrontier.Tactic.GameHop
import CslibFrontier.Tactic.Negligible
import CslibFrontier.Tactic.UniformRelabel

/-!
# Computational security of the Naor–Reingold PRF from DDH

This module completes the efficient lazy-sampling Decisional Diffie–Hellman (`DDH`) reduction and
the universal-hash bit-string pseudorandom-function bridge for the Naor–Reingold PRF over a
`PrimeOrderGroupFamily` ([BonehShoup2023], Section 10.11, Exercises 10.4, 10.8, 10.11, pp. 424–426,
and Section 4.10, Exercise 4.18, p. 172; [NaorReingold2004], Section 4.1, Construction 4.1,
Theorem 4.1, Lemma 4.2, Construction 4.2, Theorem 4.3, and Remark 4.2):

1. **Inverse-order bound from `DDH`:** `DDH.negligible_expected_inv_order`, imported from
   `CslibFrontier.Crypto.Computational.DiffieHellman.Order`, makes the setup-averaged inverse group
   order negligible; it bounds the hashed-PRF error terms below.
2. **Word-level adaptive group-PRF games and lazy-sampling `IsOraclePPT` DDH reduction:**
   `naorReingoldFrontierOracle` memoizes `ddhFixedUWordRerandomize` only on the `k`-bit prefixes
   queried by an `OracleDistinguisher` and evaluates the remaining suffix via
   `naorReingoldWordSuffix`. Choosing `k ← sampleDyadicIndex (inLen n)` yields the uniform strict
   PPT DDH distinguisher `naorReingoldToDDHDistinguisher`, proving both quantitative single-
   distinguisher bounds and asymptotic security under `F.DDH setup` alone: for the keys drawn with
   the fair-coin sampler `sampleNaorReingoldExp` (`DDH.negligible_naorReingoldProbGame`), through
   the ideal-sampling step with exactly uniform keys (`DDH.negligible_naorReingoldWordGame_ideal`).
3. **Universal-hash bit-string Naor–Reingold PRF (after [NaorReingold2004], not checked):**
   composing `naorReingoldWordEval` with `linearHashKDF` under a public universal-hash seed
   (`F.withSeed` and `F.seededSetup`) maps a uniform group element to an `outLen n`-bit string
   that is jointly close to uniform with the public seed, with error bounded by the Leftover Hash
   Lemma; a multi-query Leftover Hash Lemma bound via `PMF.dist_bind_pair_pi_le_sum` yields adaptive
   bit-string PRF security for exponents drawn with the fair-coin sampler
   (`DDH.negligible_naorReingoldHashedProbGame`), through the ideal-key-sampling steps with exactly
   uniform exponents (`DDH.negligible_naorReingoldHashedGame_ideal`,
   `DDH.negligible_naorReingoldHashedGame_ideal_const`).

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.sampleNaorReingoldExp`: executable modular exponent sampler
  with statistical slack `n + (F.encDesc d).length`.
* `Cslib.Crypto.PrimeOrderGroupFamily.naorReingoldWordRealGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.naorReingoldProbRealGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.naorReingoldWordIdealGame`: setup-parameterized word-level
  adaptive Naor–Reingold group-PRF experiments.
* `Cslib.Crypto.PrimeOrderGroupFamily.naorReingoldFrontierOracle`: memoized prefix DDH
  rerandomization followed by `naorReingoldWordSuffix`.
* `Cslib.Crypto.PrimeOrderGroupFamily.naorReingoldDescToDDHDistinguisher`: single-challenge
  uniform strict PPT DDH distinguisher constructed from an adaptive PRF distinguisher that reads the
  group parameters; `Cslib.Crypto.PrimeOrderGroupFamily.naorReingoldToDDHDistinguisher` is its
  instance for an `OracleDistinguisher`, which reads them encoded.
* `Cslib.Crypto.PrimeOrderGroupFamily.naorReingoldHashedWordEval`,
  `Cslib.Crypto.PrimeOrderGroupFamily.naorReingoldHashedRealGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.naorReingoldHashedProbRealGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.naorReingoldHashedGroupIdealGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.naorReingoldHashedIdealGame`: universal-hash bit-string
  Naor–Reingold evaluation and setup-parameterized PRF experiments.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.isPPT_naorReingoldDescToDDHDistinguisher`,
  `Cslib.Crypto.PrimeOrderGroupFamily.isPPT_naorReingoldToDDHDistinguisher`: uniform strict PPT
  certificates for both distinguishers from any oracle PPT distinguisher.
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_naorReingoldProbRealGame_wordRealGame_le`:
  modular-sampling bound between the fair-coin and the exactly uniform keys of the group-PRF.
* `Cslib.Crypto.PrimeOrderGroupFamily.DDH.negligible_naorReingoldProbGame`: asymptotic adaptive
  security of the Naor–Reingold group-PRF with fair-coin keys under `F.DDH setup`.
* `Cslib.Crypto.PrimeOrderGroupFamily.computableInPolyTime_naorReingoldHashedWordEval`,
  `Cslib.Crypto.PrimeOrderGroupFamily.advantage_naorReingoldHashedIdeal_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.DDH.negligible_naorReingoldHashedProbGame`: polynomial-time
  evaluation, multi-query Leftover Hash Lemma bound, and asymptotic bit-string PRF security with
  fair-coin exponents.

## Ideal-sampling steps

* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_naorReingoldWordGame_le_ideal`,
  `Cslib.Crypto.PrimeOrderGroupFamily.DDH.negligible_naorReingoldWordGame_ideal`: the quantitative
  DDH reduction bound and asymptotic security for `naorReingoldWordRealGame`, whose keys are drawn
  exactly uniformly. `DDH.negligible_naorReingoldProbGame` consumes them.
* `Cslib.Crypto.PrimeOrderGroupFamily.DDH.negligible_naorReingoldHashedGame_ideal`,
  `Cslib.Crypto.PrimeOrderGroupFamily.DDH.negligible_naorReingoldHashedGame_ideal_const`:
  asymptotic security of the hashed bit-string PRF for `naorReingoldHashedRealGame`, whose
  exponents are drawn exactly uniformly. `DDH.negligible_naorReingoldHashedProbGame` consumes the
  first, and `CslibFrontier/Crypto/Computational/NaorReingold/PRF.lean` consumes both.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 4.10 (Exercise 4.18, p. 172) and Section 10.11
  (Exercises 10.4, 10.8, and 10.11, pp. 424–426).
* [M. Naor, O. Reingold, *Number-Theoretic Constructions of Efficient Pseudo-Random
  Functions*][NaorReingold2004], Section 4.1 (Construction 4.1, Theorem 4.1, Lemma 4.2,
  Construction 4.2, Theorem 4.3, and Remark 4.2); locators not checked.
-/

public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Probability.PMF Turing.MultiTapeTM
open scoped ENNReal NNReal Cslib.Probability.PMF

variable (F : PrimeOrderGroupFamily)

private instance carrier_finite (F : PrimeOrderGroupFamily) (d : F.Desc) : Finite (F.Carrier d) :=
  Finite.of_surjective _ (F.smul_generator_surjective d)

/-! ### Word-level Naor–Reingold group-PRF games and prefix hybrids -/

/-- Sample a nearly-uniform modular exponent modulo `F.order d` via `F.sampleExp` with
`n + (F.encDesc d).length` statistical slack bits so that the statistical error
`1 / 2 ^ (n + |encDesc d|)` offsets polynomial query counts depending on `|encDesc d|`
(original). -/
noncomputable def sampleNaorReingoldExp (n : ℕ) (d : F.Desc) : ProbComp ℕ :=
  F.sampleExp (n + (F.encDesc d).length) d

/-- Every value supported by `sampleNaorReingoldExp` is strictly less than `F.order d`. -/
theorem lt_order_of_mem_support_sampleNaorReingoldExp {n : ℕ} {d : F.Desc} {v : ℕ}
    (hv : v ∈ (ProbComp.eval (F.sampleNaorReingoldExp n d)).support) :
    v < F.order d := by
  unfold sampleNaorReingoldExp at hv
  simp only [sampleExp, ProbComp.eval_sampleModNat, PMF.mem_support_map_iff] at hv
  obtain ⟨x, _, rfl⟩ := hv
  exact Nat.mod_lt _ (F.prime_order d).pos

/-- Projected to `ZMod (F.order d)`, `sampleNaorReingoldExp n d` has law
`F.sampleModZModLaw (n + (F.encDesc d).length) d`. -/
theorem map_natCast_eval_sampleNaorReingoldExp (n : ℕ) (d : F.Desc) :
    (ProbComp.eval (F.sampleNaorReingoldExp n d)).map (Nat.cast : ℕ → ZMod (F.order d)) =
      F.sampleModZModLaw (n + (F.encDesc d).length) d := by
  unfold sampleNaorReingoldExp
  simp only [sampleExp, sampleModZModLaw, encNat_apply, ← Nat.size_eq_bits_len]
  rw [Nat.add_comm (n + (F.encDesc d).length)]

/-- `sampleNaorReingoldExp` is uniform strict PPT in `(n, d)`. -/
@[fun_prop]
theorem isPPTOn_sampleNaorReingoldExp {α : Type} {input : α ↪ List Bool}
    {param : α → ℕ} {desc : α → F.Desc}
    (hparam : ComputableInPolyTime param input encUnary)
    (hdesc : ComputableInPolyTime desc input F.encDesc) :
    IsPPTOn input encNat (fun a => F.sampleNaorReingoldExp (param a) (desc a)) := by
  unfold sampleNaorReingoldExp
  fun_prop

/-- Deterministic word-level oracle wrapper encoding `fn : BitString m → F.Carrier d` on valid
`m`-bit queries and returning `[]` on malformed queries. -/
@[expose] def naorReingoldWordOracle (d : F.Desc) {m : ℕ} (fn : BitString m → F.Carrier d)
    (query : List Bool) : List Bool :=
  if query.length = m then F.encode d (fn (BitString.ofList m query)) else []

/-- Run a randomized word-level oracle program against `naorReingoldWordOracle d fn`. -/
private noncomputable def naorReingoldWordRun (F : PrimeOrderGroupFamily) (d : F.Desc) {m : ℕ}
    (prog : WordOracleComp Unit Bool) (fn : BitString m → F.Carrier d) : PMF Bool :=
  OracleComp.interpret
    (OracleComp.sumHandler ProbComp.unifOracle fun request =>
      PMF.pure (F.naorReingoldWordOracle d fn request.2))
    prog

/-- Setup-parameterized real Naor–Reingold group-PRF game with exact uniform `ZMod (F.order d)`
exponents ([BonehShoup2023], Exercise 10.4, p. 424; [NaorReingold2004], Construction 4.1 &
Theorem 4.1). -/
@[expose] noncomputable def naorReingoldWordRealGame (setup : ℕ → PMF F.Desc) (inLen : ℕ → ℕ)
    (adversary : OracleDistinguisher) (n : ℕ) : Game := do
  let d ← setup n
  let α₀ ← PMF.uniformOfFintype (ZMod (F.order d))
  let α ← PMF.uniformOfFintype (Fin (inLen n) → ZMod (F.order d))
  OracleComp.interpret
    (OracleComp.sumHandler ProbComp.unifOracle fun request =>
      PMF.pure (F.naorReingoldWordOracle d (F.naorReingoldEval d α₀ α) request.2))
    (adversary n (F.encDesc d))

/-- Setup-parameterized executable Naor–Reingold group-PRF real game sampling modular exponents via
`sampleNaorReingoldExp` (original). -/
@[expose] noncomputable def naorReingoldProbRealGame (setup : ℕ → PMF F.Desc) (inLen : ℕ → ℕ)
    (adversary : OracleDistinguisher) (n : ℕ) : Game := do
  let d ← setup n
  ProbComp.eval (do
    let α₀ ← F.sampleNaorReingoldExp n d
    let αs ← OracleComp.replicate (inLen n) (F.sampleNaorReingoldExp n d)
    OracleComp.interpret
      (OracleComp.sumHandler ProbComp.unifFin fun request =>
        pure (if request.2.length = inLen n then
          F.naorReingoldWordEval d α₀ αs request.2 else []))
      (adversary n (F.encDesc d)))

/-- Setup-parameterized ideal random group-function game against `OracleDistinguisher`
([BonehShoup2023], Exercise 10.4, p. 424; [NaorReingold2004], Theorem 4.1). -/
@[expose] noncomputable def naorReingoldWordIdealGame (setup : ℕ → PMF F.Desc) (inLen : ℕ → ℕ)
    (adversary : OracleDistinguisher) (n : ℕ) : Game := do
  let d ← setup n
  let B ← PMF.uniformOfFintype (BitString (inLen n) → ZMod (F.order d))
  OracleComp.interpret
    (OracleComp.sumHandler ProbComp.unifOracle fun request =>
      PMF.pure (F.naorReingoldWordOracle d (fun x => B x • F.generator d) request.2))
    (adversary n (F.encDesc d))

private noncomputable def naorReingoldWordHybridAt (F : PrimeOrderGroupFamily) (d : F.Desc)
    (m k : ℕ) (prog : WordOracleComp Unit Bool) : Game := do
  let B ← PMF.uniformOfFintype (BitString k → ZMod (F.order d))
  let α ← PMF.uniformOfFintype (Fin m → ZMod (F.order d))
  naorReingoldWordRun F d prog (F.naorReingoldHybridEval d k B α)

private theorem naorReingoldWordHybridAt_zero (F : PrimeOrderGroupFamily) (d : F.Desc) (m : ℕ)
    (prog : WordOracleComp Unit Bool) :
    naorReingoldWordHybridAt F d m 0 prog =
      (do
        let α₀ ← PMF.uniformOfFintype (ZMod (F.order d))
        let α ← PMF.uniformOfFintype (Fin m → ZMod (F.order d))
        naorReingoldWordRun F d prog (F.naorReingoldEval d α₀ α)) := by
  unfold naorReingoldWordHybridAt
  relabel_uniform (Equiv.funUnique (BitString 0) (ZMod (F.order d))).symm with α₀
  congr 1 with α : 1
  refine congrArg (naorReingoldWordRun F d prog) (funext fun x => ?_)
  simp [naorReingoldHybridEval, naorReingoldEval]

private theorem naorReingoldWordHybridAt_self (F : PrimeOrderGroupFamily) (d : F.Desc) (m : ℕ)
    (prog : WordOracleComp Unit Bool) :
    naorReingoldWordHybridAt F d m m prog =
      (do
        let B ← PMF.uniformOfFintype (BitString m → ZMod (F.order d))
        naorReingoldWordRun F d prog (fun x => B x • F.generator d)) := by
  unfold naorReingoldWordHybridAt
  simp only [PMF.monad_bind_eq_bind]
  congr 1; funext B
  rw [show (fun α => naorReingoldWordRun F d prog (F.naorReingoldHybridEval d m B α)) =
      fun _ => naorReingoldWordRun F d prog (fun x => B x • F.generator d) from
    funext fun _ => congrArg _ (funext fun x => by simp [naorReingoldHybridEval]), PMF.bind_const]

private noncomputable def naorReingoldWordLevelTest (F : PrimeOrderGroupFamily) (d : F.Desc)
    {m : ℕ} (k : ℕ) (hk : k < m) (prog : WordOracleComp Unit Bool) (_u : F.Carrier d)
    (T : BitString k → F.Carrier d × F.Carrier d) : PMF Bool := do
  let suffix ← PMF.uniformOfFintype (Fin (m - (k + 1)) → ZMod (F.order d))
  let α : Fin m → ZMod (F.order d) := fun i =>
    if h : k + 1 ≤ i.val then suffix ⟨i.val - (k + 1), by omega⟩ else 1
  naorReingoldWordRun F d prog (F.naorReingoldTableEval d k hk T α)

private theorem naorReingoldSuffixExp_extend_suffix (F : PrimeOrderGroupFamily) (d : F.Desc)
    {m k : ℕ} (α : Fin m → ZMod (F.order d)) (x : BitString m) :
    F.naorReingoldSuffixExp d (k + 1)
      (fun i : Fin m =>
        if h : k + 1 ≤ i.val then α ⟨k + 1 + (i.val - (k + 1)), by omega⟩ else 1) x =
      F.naorReingoldSuffixExp d (k + 1) α x := by
  unfold naorReingoldSuffixExp
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : k + 1 ≤ i.val
  · simp only [hi, ↓reduceDIte, true_and]
    congr 2; ext; dsimp; omega
  · simp [hi]

private theorem naorReingoldWordLevelTest_eq_uniform_full (F : PrimeOrderGroupFamily) (d : F.Desc)
    {m : ℕ} (k : ℕ) (hk : k < m) (prog : WordOracleComp Unit Bool) (u : F.Carrier d) :
    naorReingoldWordLevelTest F d k hk prog u =
      fun T => (PMF.uniformOfFintype (Fin m → ZMod (F.order d))).bind fun α =>
        naorReingoldWordRun F d prog (F.naorReingoldTableEval d k hk T α) := by
  funext T
  let emb : Fin (m - (k + 1)) ↪ Fin m :=
    ⟨fun j => ⟨k + 1 + j.val, by omega⟩, fun a b h => by ext; simpa using Fin.mk.inj h⟩
  unfold naorReingoldWordLevelTest
  simp only [PMF.monad_bind_eq_bind]
  rw [← PMF.uniformOfFintype_pi_map_comp_embedding emb, PMF.bind_map]
  congr 1; funext α
  refine congrArg (naorReingoldWordRun F d prog) (funext fun x => ?_)
  change F.naorReingoldTableEval d k hk T
    (fun i => if h : k + 1 ≤ i.val then α ⟨k + 1 + (i.val - (k + 1)), by omega⟩ else 1) x = _
  rw [naorReingoldTableEval, naorReingoldTableEval, naorReingoldSuffixExp_extend_suffix F d α x]

private theorem multiDDHRealTupleLaw_naorReingoldWordLevelTest (F : PrimeOrderGroupFamily)
    (d : F.Desc) {m : ℕ} (k : ℕ) (hk : k < m) (prog : WordOracleComp Unit Bool) :
    ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun α_k =>
      (F.multiDDHRealTupleLaw d (BitString k) α_k).bind
        (naorReingoldWordLevelTest F d k hk prog (α_k • F.generator d))) =
      naorReingoldWordHybridAt F d m k prog := by
  simp_rw [naorReingoldWordLevelTest_eq_uniform_full F d k hk prog]
  unfold naorReingoldWordHybridAt
  simp only [multiDDHRealTupleLaw, PMF.monad_bind_eq_bind, PMF.bind_map, Function.comp_def]
  rw [PMF.bind_comm (PMF.uniformOfFintype (ZMod (F.order d)))
    (PMF.uniformOfFintype (BitString k → ZMod (F.order d)))]
  congr 1; funext B
  have hfn (α_k : ZMod (F.order d)) (α : Fin m → ZMod (F.order d)) :
      F.naorReingoldTableEval d k hk
        (fun i => (B i • F.generator d, (α_k * B i) • F.generator d)) α =
      F.naorReingoldHybridEval d k B (Function.update α ⟨k, hk⟩ α_k) := by
    funext x
    rw [naorReingoldTableEval, naorReingoldHybridEval,
      F.naorReingoldSuffixExp_eq_mul_succ d hk (Function.update α ⟨k, hk⟩ α_k) x,
      F.naorReingoldSuffixExp_succ_update d hk α α_k x]
    simp only [Function.update_self]
    rcases Bool.eq_false_or_eq_true (x ⟨k, hk⟩) with hxk | hxk
    · simp only [hxk, ↓reduceIte, smul_smul]
      exact congrArg (· • F.generator d) (by ring)
    · simp [hxk, smul_smul, mul_comm]
  simp_rw [hfn]
  symm
  exact PMF.bind_uniformOfFintype_update (⟨k, hk⟩ : Fin m) _

private theorem multiDDHRandomTupleLaw_naorReingoldWordLevelTest (F : PrimeOrderGroupFamily)
    (d : F.Desc) {m : ℕ} (k : ℕ) (hk : k < m) (prog : WordOracleComp Unit Bool) :
    ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun α_k =>
      (F.multiDDHRandomTupleLaw d (BitString k)).bind
        (naorReingoldWordLevelTest F d k hk prog (α_k • F.generator d))) =
      naorReingoldWordHybridAt F d m (k + 1) prog := by
  simp_rw [naorReingoldWordLevelTest_eq_uniform_full F d k hk prog]
  rw [PMF.bind_const]
  unfold naorReingoldWordHybridAt
  simp only [multiDDHRandomTupleLaw]
  relabel_uniform (fun (T : BitString k → ZMod (F.order d) × ZMod (F.order d))
      (p : BitString (k + 1)) =>
    if p (Fin.last k) then (T (Fin.init p)).2 else (T (Fin.init p)).1) with B
  · intro T₁ T₂ h
    funext s
    have hf := congrFun h (Fin.snoc s false)
    have ht := congrFun h (Fin.snoc s true)
    simp only [Fin.snoc_last, Bool.false_eq_true, ↓reduceIte, Fin.init_snoc] at hf ht
    exact Prod.ext hf ht
  · simp only [Fintype.card_pi, Fintype.card_prod, Finset.prod_const, Finset.card_univ, ← sq,
      ← pow_mul]
    congr 1
    simp [pow_succ']
  · congr 1 with α : 1
    refine congrArg (naorReingoldWordRun F d prog) (funext fun x => ?_)
    rw [naorReingoldTableEval, naorReingoldHybridEval, BitString.init_zeroExtend_succ,
      BitString.last_zeroExtend_succ hk]
    rcases Bool.eq_false_or_eq_true (x ⟨k, hk⟩) with hxk | hxk <;>
      simp [hxk, smul_smul, mul_comm]

/-! ### Lazy-sampling frontier oracle and `IsOraclePPT` DDH distinguisher -/

/-- Association-list cache mapping queried `k`-bit prefixes to encoded group-element pairs. -/
abbrev NaorReingoldCache := List (List Bool × (List Bool × List Bool))

/-- Encoding of `NaorReingoldCache`. -/
def naorReingoldCacheEncoding : NaorReingoldCache ↪ List Bool :=
  encList (encPair encBits (encPair encBits encBits))

/-- Executable rerandomized pair sampler for `naorReingoldFrontierOracle`: draw two exponents via
`sampleNaorReingoldExp` and apply `ddhFixedUWordRerandomize`. -/
noncomputable def sampleNaorReingoldPair (n : ℕ) (d : F.Desc) (u v w : List Bool) :
    ProbComp (List Bool × List Bool) := do
  let σ ← F.sampleNaorReingoldExp n d
  let τ ← F.sampleNaorReingoldExp n d
  return F.ddhFixedUWordRerandomize d u v w σ τ

/-- Stateful level-`k` frontier oracle for Naor–Reingold ([BonehShoup2023], Exercises 10.4(b) &
4.18(b); [NaorReingold2004], Theorem 4.1): on a valid `m`-bit query, memoize a freshly
rerandomized DDH pair on `query.take k`, select the `query[k]` child, and evaluate the remaining
suffix with `naorReingoldWordSuffix`. Malformed queries return `[]` without modifying the cache. -/
noncomputable def naorReingoldFrontierOracle (n m k : ℕ) (d : F.Desc) (u v w : List Bool)
    (αs : List ℕ) (query : List Bool) : StateT NaorReingoldCache ProbComp (List Bool) :=
  fun cache =>
    if query.length = m then do
      let (vw, cache') ← memoize (fun _ : List Bool => F.sampleNaorReingoldPair n d u v w)
        (query.take k) cache
      let child := if query.getD k false then vw.2 else vw.1
      return (F.naorReingoldWordSuffix d child αs (query.drop (k + 1)), cache')
    else pure ([], cache)

/-- Single-challenge uniform strict PPT DDH distinguisher constructed from an adaptive PRF
distinguisher `adv` that reads the group parameters directly: sample a hybrid level
`k ← sampleDyadicIndex (inLen n)`, draw suffix exponents `αs`, and run `adv n d` against
`naorReingoldFrontierOracle`, given the encodings of the three DDH elements, from an empty cache
([BonehShoup2023], Exercises 10.4(b) & 10.11; [NaorReingold2004], Theorem 4.1). -/
noncomputable def naorReingoldDescToDDHDistinguisher (inLen : ℕ → ℕ)
    (adv : ℕ → F.Desc → WordOracleComp Unit Bool) : F.DDHDistinguisher :=
  fun n d u v w => do
    let m := inLen n
    let k ← ProbComp.sampleDyadicIndex m
    if k < m then do
      let αs ← OracleComp.replicate (m - (k + 1)) (F.sampleNaorReingoldExp n d)
      Prod.fst <$> (OracleComp.interpret
        (OracleComp.sumHandler (fun r => StateT.lift (ProbComp.unifFin r))
          (fun request => F.naorReingoldFrontierOracle n m k d
            (F.encode d u) (F.encode d v) (F.encode d w) αs request.2))
        (adv n d)).run []
    else pure false

/-- `naorReingoldDescToDDHDistinguisher` for an `OracleDistinguisher`, which reads the encoded
group parameters `F.encDesc d`. -/
noncomputable def naorReingoldToDDHDistinguisher (inLen : ℕ → ℕ)
    (adversary : OracleDistinguisher) : F.DDHDistinguisher :=
  F.naorReingoldDescToDDHDistinguisher inLen fun n d => adversary n (F.encDesc d)

private theorem computableInPolyTime_naorReingoldWordSuffix_comp {F : PrimeOrderGroupFamily}
    {α : Type} {enc : α ↪ List Bool} {d : α → F.Desc} {u : α → List Bool}
    {αs : α → List ℕ} {xs : α → List Bool}
    (hd : ComputableInPolyTime d enc F.encDesc) (hu : ComputableInPolyTime u enc encBits)
    (hαs : ComputableInPolyTime αs enc (encList encNat))
    (hxs : ComputableInPolyTime xs enc encBits) :
    ComputableInPolyTime (fun a => F.naorReingoldWordSuffix (d a) (u a) (αs a) (xs a))
      enc encBits :=
  F.computableInPolyTime_naorReingoldWordSuffix.comp (hd.prod (hu.prod (hαs.prod hxs)))

private theorem computableInPolyTime_naorReingoldWordEval_comp {F : PrimeOrderGroupFamily}
    {α : Type} {enc : α ↪ List Bool} {d : α → F.Desc} {α₀ : α → ℕ}
    {αs : α → List ℕ} {xs : α → List Bool}
    (hd : ComputableInPolyTime d enc F.encDesc) (hα₀ : ComputableInPolyTime α₀ enc encNat)
    (hαs : ComputableInPolyTime αs enc (encList encNat))
    (hxs : ComputableInPolyTime xs enc encBits) :
    ComputableInPolyTime (fun a => F.naorReingoldWordEval (d a) (α₀ a) (αs a) (xs a))
      enc encBits :=
  F.computableInPolyTime_naorReingoldWordEval.comp (hd.prod (hα₀.prod (hαs.prod hxs)))

attribute [local fun_prop]
  computableInPolyTime_naorReingoldWordSuffix_comp
  computableInPolyTime_naorReingoldWordEval_comp

private theorem isPPTOn_sampleNaorReingoldPair {F : PrimeOrderGroupFamily}
    {α : Type} {input : α ↪ List Bool}
    {param : α → ℕ} {desc : α → F.Desc} {u v w : α → List Bool}
    (hparam : ComputableInPolyTime param input encUnary)
    (hdesc : ComputableInPolyTime desc input F.encDesc)
    (hu : ComputableInPolyTime u input encBits)
    (hv : ComputableInPolyTime v input encBits)
    (hw : ComputableInPolyTime w input encBits) :
    IsPPTOn input (encPair encBits encBits)
      (fun a => F.sampleNaorReingoldPair (param a) (desc a) (u a) (v a) (w a)) := by
  unfold sampleNaorReingoldPair
  fun_prop

attribute [local fun_prop] isPPTOn_sampleNaorReingoldPair

private theorem isPPTOn_naorReingoldFrontierOracle {F : PrimeOrderGroupFamily}
    {α : Type} {input : α ↪ List Bool}
    {param m k : α → ℕ} {desc : α → F.Desc} {u v w : α → List Bool}
    {αs : α → List ℕ} {query : α → List Bool} {cache : α → NaorReingoldCache}
    (hparam : ComputableInPolyTime param input encUnary)
    (hm : ComputableInPolyTime m input encUnary)
    (hk : ComputableInPolyTime k input encUnary)
    (hdesc : ComputableInPolyTime desc input F.encDesc)
    (hu : ComputableInPolyTime u input encBits)
    (hv : ComputableInPolyTime v input encBits)
    (hw : ComputableInPolyTime w input encBits)
    (hαs : ComputableInPolyTime αs input (encList encNat))
    (hquery : ComputableInPolyTime query input encBits)
    (hcache : ComputableInPolyTime cache input naorReingoldCacheEncoding) :
    IsPPTOn input (encPair encBits naorReingoldCacheEncoding)
      (fun a => F.naorReingoldFrontierOracle (param a) (m a) (k a) (desc a)
        (u a) (v a) (w a) (αs a) (query a) (cache a)) := by
  have hmemo : IsPPTOn input (encPair (encPair encBits encBits) naorReingoldCacheEncoding)
      (fun a => memoize (fun _ : List Bool =>
        F.sampleNaorReingoldPair (param a) (desc a) (u a) (v a) (w a))
        ((query a).take (k a)) (cache a)) := by
    unfold naorReingoldCacheEncoding; fun_prop
  unfold naorReingoldFrontierOracle
  exact (IsPPTOn.ite (condition := fun a => (query a).length = m a) (by fun_prop)
    (hmemo.bind_with (second := fun a res =>
      pure (F.naorReingoldWordSuffix (desc a)
        (if (query a).getD (k a) false then res.1.2 else res.1.1)
        (αs a) ((query a).drop (k a + 1)), res.2)) (by fun_prop))
    (no := fun a => pure ([], cache a))
    (by fun_prop)).congr fun a => by by_cases h : (query a).length = m a <;> simp [h]

attribute [local fun_prop] isPPTOn_naorReingoldFrontierOracle

private abbrev DDHCaller (F : PrimeOrderGroupFamily) := (F.DDHInput × ℕ) × List ℕ

private def ddhCallerEncoding (F : PrimeOrderGroupFamily) : DDHCaller F ↪ List Bool :=
  encPair (encPair F.encDDHInput encUnary) (encList encNat)

/-- **`naorReingoldDescToDDHDistinguisher` is uniform strict PPT** whenever `inLen` is computable
in polynomial time in unary and `adv` is oracle PPT on the security parameter and group
parameters. -/
theorem isPPT_naorReingoldDescToDDHDistinguisher
    {inLen : ℕ → ℕ} (hinLen : ComputableInPolyTime inLen encUnary encUnary)
    {adv : ℕ → F.Desc → WordOracleComp Unit Bool}
    (hadv : IsOraclePPTOn (encPair encUnary F.encDesc) encBool (fun p => adv p.1 p.2)) :
    (naorReingoldDescToDDHDistinguisher F inLen adv).IsPPT := by
  obtain ⟨cE, eE, hE⟩ := F.exists_length_encode_le
  let elemBound (d : F.Desc) : ℕ := cE * ((F.encDesc d).length + 1) ^ eE
  let isEncodedPair (d : F.Desc) (vw : List Bool × List Bool) : Prop :=
    ∃ x₁ x₂ : F.Carrier d, vw = (F.encode d x₁, F.encode d x₂)
  let resources (caller : DDHCaller F) (query : List Bool) : ℕ :=
    4 * query.length + 6 * elemBound caller.1.1.groupParameters + 7
  have hpair_enc (caller : DDHCaller F) (vw : List Bool × List Bool)
      (hvw : vw ∈ (ProbComp.eval (F.sampleNaorReingoldPair caller.1.1.secParam
        caller.1.1.groupParameters (F.encode caller.1.1.groupParameters caller.1.1.leftPublic)
        (F.encode caller.1.1.groupParameters caller.1.1.rightPublic)
        (F.encode caller.1.1.groupParameters caller.1.1.candidateShared))).support) :
      isEncodedPair caller.1.1.groupParameters vw := by
    simp only [sampleNaorReingoldPair, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hvw
    obtain ⟨σ, _, τ, _, rfl⟩ := hvw
    exact ⟨_, _, F.ddhFixedUWordRerandomize_encode _ _ _ _ σ τ⟩
  let runFrontier (caller : DDHCaller F) : ProbComp (Bool × NaorReingoldCache) :=
    (OracleComp.interpret
      (OracleComp.sumHandler (fun r => StateT.lift (ProbComp.unifFin r))
        (fun request => F.naorReingoldFrontierOracle caller.1.1.secParam
          (inLen caller.1.1.secParam) caller.1.2 caller.1.1.groupParameters
          (F.encode caller.1.1.groupParameters caller.1.1.leftPublic)
          (F.encode caller.1.1.groupParameters caller.1.1.rightPublic)
          (F.encode caller.1.1.groupParameters caller.1.1.candidateShared) caller.2 request.2))
      (adv caller.1.1.secParam caller.1.1.groupParameters)).run []
  have hrun : IsPPTOn (ddhCallerEncoding F) (encPair encBool naorReingoldCacheEncoding)
      runFrontier := by
    refine hadv.isPPTOn_runState (operationEncoding := encFinEnum Unit)
      (prepare := fun caller : DDHCaller F => (caller.1.1.secParam, caller.1.1.groupParameters))
      (resources := resources)
      (by unfold ddhCallerEncoding; fun_prop)
      (by
        unfold ddhCallerEncoding
        exact isPPTOn_naorReingoldFrontierOracle
          (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
          (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop))
      (by fun_prop)
      (fun caller cache => ∀ entry ∈ cache, isEncodedPair caller.1.1.groupParameters entry.2)
      (by simp)
      (by unfold ddhCallerEncoding; dsimp only [resources, elemBound]; fun_prop) ?_
    intro caller request cache hcache result hresult
    let d := caller.1.1.groupParameters
    unfold naorReingoldFrontierOracle at hresult
    by_cases hq : request.2.length = inLen caller.1.1.secParam
    · simp only [hq, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_memoize,
        PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hresult
      obtain ⟨⟨vw, cache'⟩, hvw, rfl⟩ := hresult
      let dist : List Bool → PMF (List Bool × List Bool) := fun _ =>
        ProbComp.eval (F.sampleNaorReingoldPair caller.1.1.secParam d
          (F.encode d caller.1.1.leftPublic) (F.encode d caller.1.1.rightPublic)
          (F.encode d caller.1.1.candidateShared))
      obtain ⟨⟨x₁, x₂, hvw_eq⟩, hcache'⟩ := RandomOracle.memoize_invariant dist
        (fun _ => isEncodedPair d) (request.2.take caller.1.2) cache
        (fun entry hentry => hcache entry hentry) (hpair_enc caller) (vw, cache') hvw
      have hgrowth := memoize_cache_growth_le encBits (encPair encBits encBits) dist
        (request.2.take caller.1.2) cache (3 * elemBound d + 2)
        (fun val hval => by
          obtain ⟨y₁, y₂, rfl⟩ := hpair_enc caller val hval
          rw [length_encPair, encBits_apply, encBits_apply]
          have h1 := hE d y₁; have h2 := hE d y₂
          dsimp only [elemBound, d] at h1 h2 ⊢; omega)
        (vw, cache') hvw
      have hchild : (if request.2.getD caller.1.2 false then vw.2 else vw.1) =
          F.encode d (if request.2.getD caller.1.2 false then x₂ else x₁) := by
        dsimp only at hvw_eq
        rw [hvw_eq]
        split_ifs <;> rfl
      refine ⟨hcache', ?_, ?_⟩
      · rw [hchild, F.naorReingoldWordSuffix_encode]
        exact (hE d _).trans (by dsimp only [resources, d]; lia)
      · dsimp only [naorReingoldCacheEncoding, encMemoCache, encBits_apply, resources, d]
          at hgrowth ⊢
        rw [List.length_take] at hgrowth
        lia
    · simp only [hq, ↓reduceIte, ProbComp.eval_pure, PMF.mem_support_pure_iff] at hresult
      subst result
      exact ⟨hcache, Nat.zero_le _, Nat.le_add_right _ _⟩
  have hrun_fst : IsPPTOn (encPair (encPair F.encDDHInput encUnary) (encList encNat)) encBool
      (fun caller => Prod.fst <$> runFrontier caller) := by
    unfold ddhCallerEncoding at hrun
    exact hrun.map (ComputableInPolyTime.fst _ _)
  unfold DDHDistinguisher.IsPPT naorReingoldDescToDDHDistinguisher
  refine (isPPTOn_sampleDyadicIndex (by fun_prop)).bind_with
    ((IsPPTOn.ite (condition := fun p : F.DDHInput × ℕ => p.2 < inLen p.1.secParam) (by fun_prop)
      ((IsPPTOn.replicate (count := fun p : F.DDHInput × ℕ => inLen p.1.secParam - (p.2 + 1))
        (program := fun p : F.DDHInput × ℕ =>
          F.sampleNaorReingoldExp p.1.secParam p.1.groupParameters)
        (by fun_prop) (by fun_prop)).bind_with
        (second := fun p αs => Prod.fst <$> runFrontier (p, αs)) hrun_fst)
      (no := fun _ => pure false) (by fun_prop)).congr fun p => ?_)
  by_cases h : p.2 < inLen p.1.secParam <;> simp [h, runFrontier]

private theorem isOraclePPTOn_adversary_encDesc {F : PrimeOrderGroupFamily}
    {adversary : OracleDistinguisher} (hadversary : IsOraclePPT encBool adversary) :
    IsOraclePPTOn (encPair encUnary F.encDesc) encBool
      (fun p => adversary p.1 (F.encDesc p.2)) :=
  hadversary.on.preprocess (prepare := fun p : ℕ × F.Desc => (p.1, F.encDesc p.2)) (by fun_prop)

/-- **`naorReingoldToDDHDistinguisher` is uniform strict PPT** whenever `inLen` is computable in
polynomial time in unary and `adversary` satisfies `IsOraclePPT encBool` ([BonehShoup2023],
Exercise 10.4(b); [NaorReingold2004], Theorem 4.1). -/
theorem isPPT_naorReingoldToDDHDistinguisher {inLen : ℕ → ℕ}
    (hinLen : ComputableInPolyTime inLen encUnary encUnary)
    {adversary : OracleDistinguisher} (hadversary : IsOraclePPT encBool adversary) :
    (F.naorReingoldToDDHDistinguisher inLen adversary).IsPPT :=
  isPPT_naorReingoldDescToDDHDistinguisher F hinLen (isOraclePPTOn_adversary_encDesc hadversary)

/-! ### Quantitative and asymptotic DDH security of the Naor–Reingold group-PRF -/

private theorem eval_sampleNaorReingoldExp_eq_map_val (F : PrimeOrderGroupFamily) (n : ℕ)
    (d : F.Desc) :
    ProbComp.eval (F.sampleNaorReingoldExp n d) =
      (F.sampleModZModLaw (n + (F.encDesc d).length) d).map ZMod.val := by
  rw [← F.map_natCast_eval_sampleNaorReingoldExp n d, PMF.map_comp]
  symm
  refine (map_congr_on_support _ _ id fun x hx => ?_).trans (PMF.map_id _)
  dsimp only [Function.comp_apply, id_eq]
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (F.lt_order_of_mem_support_sampleNaorReingoldExp hx)]

private theorem eval_replicate_sampleNaorReingoldExp_eq_iid (F : PrimeOrderGroupFamily)
    (n count : ℕ) (d : F.Desc) :
    ProbComp.eval (OracleComp.replicate count (F.sampleNaorReingoldExp n d)) =
      (PMF.iid (F.sampleModZModLaw (n + (F.encDesc d).length) d) count).map
        (fun s => List.ofFn fun j => (s j).val) := by
  rw [ProbComp.eval_replicate_iid, eval_sampleNaorReingoldExp_eq_map_val, PMF.iid_map, PMF.map_comp]
  rfl

private theorem iid_two_map {α β : Type*} (μ : PMF α) (f : α → α → β) :
    (PMF.iid μ 2).map (fun p => f (p 0) (p 1)) =
      μ.bind fun a => μ.map (fun b => f a b) := by
  simp only [PMF.iid, PMF.monad_bind_eq_bind, PMF.map_bind, PMF.pure_map,
    Fin.cons_zero, Fin.cons_one]
  rfl

private theorem eval_sampleNaorReingoldPair_eq_iid (F : PrimeOrderGroupFamily) (n : ℕ)
    (d : F.Desc) (u v w : List Bool) :
    ProbComp.eval (F.sampleNaorReingoldPair n d u v w) =
      (PMF.iid (F.sampleModZModLaw (n + (F.encDesc d).length) d) 2).map
        (fun p => F.ddhFixedUWordRerandomize d u v w (p 0).val (p 1).val) := by
  unfold sampleNaorReingoldPair
  symm
  refine (iid_two_map (F.sampleModZModLaw (n + (F.encDesc d).length) d)
    (fun a b => F.ddhFixedUWordRerandomize d u v w a.val b.val)).trans ?_
  simp only [ProbComp.eval_bind, ProbComp.eval_pure, eval_sampleNaorReingoldExp_eq_map_val F n d,
    PMF.bind_map, Function.comp_def]
  rfl

private theorem pi_ddhFixedURerandomizeLaw_eq_multi (F : PrimeOrderGroupFamily) (d : F.Desc)
    (ι : Type*) [Fintype ι] [DecidableEq ι] (u₀ v₀ w₀ : F.Carrier d) :
    PMF.pi (fun _ : ι => F.ddhFixedURerandomizeLaw d u₀ v₀ w₀) =
      F.multiDDHRerandomizeLaw d ι u₀ v₀ w₀ := by
  have hcoord : F.ddhFixedURerandomizeLaw d u₀ v₀ w₀ =
      (PMF.uniformOfFintype (ZMod (F.order d) × ZMod (F.order d))).map
        (fun p => F.ddhFixedURerandomize d u₀ v₀ w₀ p.1 p.2) := by
    rw [ddhFixedURerandomizeLaw]
    simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, ← PMF.bind_pure_comp]
    exact PMF.uniformOfFintype_bind_map (F.ddhFixedURerandomize d u₀ v₀ w₀)
  simp_rw [hcoord]
  rw [PMF.pi_map, PMF.pi_uniformOfFintype, multiDDHRerandomizeLaw]

private noncomputable def frontierLevelWithExpLaw (F : PrimeOrderGroupFamily) (d : F.Desc)
    (m k : ℕ) (prog : WordOracleComp Unit Bool) (u v w : List Bool)
    (expLaw : PMF (ZMod (F.order d))) : PMF Bool := do
  let suffix ← PMF.iid expLaw (m - (k + 1))
  let αs := List.ofFn fun j => (suffix j).val
  let pairLaw := (PMF.iid expLaw 2).map fun p =>
    F.ddhFixedUWordRerandomize d u v w (p 0).val (p 1).val
  ((OracleComp.interpret
    (OracleComp.sumHandler (fun r => StateT.lift (ProbComp.unifOracle r))
      fun request cache =>
        if request.2.length = m then do
          let (vw, cache') ← memoize (fun _ : List Bool => pairLaw) (request.2.take k) cache
          let child := if request.2.getD k false then vw.2 else vw.1
          pure (F.naorReingoldWordSuffix d child αs (request.2.drop (k + 1)), cache')
        else pure ([], cache))
    prog).run []).map Prod.fst

private theorem eval_frontierLevel_eq_withExpLaw (F : PrimeOrderGroupFamily) (n m k : ℕ)
    (d : F.Desc) (prog : WordOracleComp Unit Bool) (u v w : List Bool) :
    ProbComp.eval (do
      let αs ← OracleComp.replicate (m - (k + 1)) (F.sampleNaorReingoldExp n d)
      Prod.fst <$> (OracleComp.interpret
        (OracleComp.sumHandler (fun r => StateT.lift (ProbComp.unifFin r))
          (fun request => F.naorReingoldFrontierOracle n m k d u v w αs request.2))
        prog).run []) =
      frontierLevelWithExpLaw F d m k prog u v w
        (F.sampleModZModLaw (n + (F.encDesc d).length) d) := by
  unfold frontierLevelWithExpLaw
  simp only [ProbComp.eval_bind, ProbComp.eval_map, ProbOracleComp.eval_run_interpret_eq_runWith,
    eval_replicate_sampleNaorReingoldExp_eq_iid F n (m - (k + 1)) d,
    PMF.monad_bind_eq_bind, PMF.bind_map, Function.comp_def]
  congr 1; funext suffix
  rw [ProbOracleComp.runWith_eq_run_interpret]
  refine congrArg (PMF.map Prod.fst)
    (congrArg (fun h => StateT.run (OracleComp.interpret h prog) []) ?_)
  funext q
  cases q with
  | inl r => rfl
  | inr request =>
    funext cache
    dsimp only [OracleComp.sumHandler, naorReingoldFrontierOracle]
    by_cases hq : request.2.length = m
    · simp only [hq, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_memoize,
        eval_sampleNaorReingoldPair_eq_iid F n d u v w]
      rfl
    · simp [hq]

private noncomputable def frontierStep (F : PrimeOrderGroupFamily) (d : F.Desc) (m k : ℕ)
    (αs : List ℕ) (fresh : List Bool × List Bool) (request : Unit × List Bool) :
    StateT NaorReingoldCache PMF (List Bool) :=
  fun cache =>
    if request.2.length = m then
      match cache.lookup (request.2.take k) with
      | some vw =>
          PMF.pure (F.naorReingoldWordSuffix d
            (if request.2.getD k false then vw.2 else vw.1) αs (request.2.drop (k + 1)), cache)
      | none =>
          PMF.pure (F.naorReingoldWordSuffix d
            (if request.2.getD k false then fresh.2 else fresh.1) αs (request.2.drop (k + 1)),
            (request.2.take k, fresh) :: cache)
    else PMF.pure ([], cache)

private theorem frontierStep_bind_eq (F : PrimeOrderGroupFamily) (d : F.Desc) (m k : ℕ)
    (αs : List ℕ) (source : PMF (List Bool × List Bool)) (request : Unit × List Bool)
    (cache : NaorReingoldCache) :
    (source.bind fun fresh => frontierStep F d m k αs fresh request cache) =
      (if request.2.length = m then do
        let (vw, cache') ← memoize (fun _ : List Bool => source) (request.2.take k) cache
        let child := if request.2.getD k false then vw.2 else vw.1
        pure (F.naorReingoldWordSuffix d child αs (request.2.drop (k + 1)), cache')
      else pure ([], cache)) := by
  unfold frontierStep memoize
  by_cases hq : request.2.length = m
  · cases cache.lookup (request.2.take k) <;>
      simp [hq, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_const]
  · simp [hq, PMF.monad_pure_eq_pure, PMF.bind_const]

private theorem dist_bind_pair_le {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (a₁ a₂ : PMF α) (b₁ b₂ : PMF β) (k : α × β → PMF γ) :
    dist ((a₁.bind fun x => b₁.map (x, ·)).bind k)
      ((a₂.bind fun x => b₂.map (x, ·)).bind k) ≤
      dist a₁ a₂ + dist b₁ b₂ := by
  have hswap (a : PMF α) (b : PMF β) :
      (a.bind fun x => b.map (x, ·)) = (b.bind fun y => a.map (·, y)) := by
    simp only [PMF.map, Function.comp_def]
    exact PMF.bind_comm a b fun x y => PMF.pure (x, y)
  refine (dist_bind_le _ _ k).trans ((dist_triangle _ (a₂.bind fun x => b₁.map (x, ·)) _).trans ?_)
  refine add_le_add (dist_bind_le a₁ a₂ _) ?_
  rw [hswap a₂ b₁, hswap a₂ b₂]
  exact dist_bind_le b₁ b₂ _

private theorem dist_frontierLevelWithExpLaw_le (F : PrimeOrderGroupFamily) (d : F.Desc)
    (m k Q : ℕ) {prog : WordOracleComp Unit Bool} (hQ : prog.IsQueryBounded Q)
    (u v w : List Bool) (μ₁ μ₂ : PMF (ZMod (F.order d))) :
    dist (frontierLevelWithExpLaw F d m k prog u v w μ₁)
      (frontierLevelWithExpLaw F d m k prog u v w μ₂) ≤
      (m + 2 * Q : ℝ) * dist μ₁ μ₂ := by
  let r := m - (k + 1)
  let detKernel : (Fin r → ZMod (F.order d)) × (Fin Q → Fin 2 → ZMod (F.order d)) → PMF Bool :=
    fun st =>
      let αs := List.ofFn fun j => (st.1 j).val
      let values := List.ofFn fun i =>
        F.ddhFixedUWordRerandomize d u v w (st.2 i 0).val (st.2 i 1).val
      ((ProbOracleComp.runWith (OracleComp.withSampleList ([], []) (frontierStep F d m k αs)) prog
          ([], values)).map fun res => res.1)
  have hlaw (μ : PMF (ZMod (F.order d))) :
      frontierLevelWithExpLaw F d m k prog u v w μ =
        ((PMF.iid μ r).bind fun s => (PMF.iid (PMF.iid μ 2) Q).map (s, ·)).bind detKernel := by
    unfold frontierLevelWithExpLaw
    simp only [PMF.monad_bind_eq_bind, PMF.bind_bind, PMF.bind_map, Function.comp_def]
    congr 1; funext s
    set αs := List.ofFn fun j => (s j).val
    set pairLaw := (PMF.iid μ 2).map fun p =>
      F.ddhFixedUWordRerandomize d u v w (p 0).val (p 1).val
    have hpre := congrArg (PMF.map Prod.fst)
      (hQ.run_interpret_presample pairLaw ([], []) (frontierStep F d m k αs) [])
    trans (((OracleComp.interpret
      (OracleComp.sumHandler (fun r => StateT.lift (ProbComp.unifOracle r))
        fun request cache => pairLaw.bind fun fresh => frontierStep F d m k αs fresh request cache)
      prog).run []).map Prod.fst)
    · refine congrArg (PMF.map Prod.fst)
        (congrArg (fun h => StateT.run (OracleComp.interpret h prog) []) ?_)
      funext q
      cases q with
      | inl _ => rfl
      | inr request =>
        funext cache
        exact (frontierStep_bind_eq F d m k αs pairLaw request cache).symm
    · rw [← hpre, PMF.map_bind, PMF.iid_map, PMF.map_comp, PMF.bind_map]
      congr 1; funext tbl
      simp only [Function.comp_def, PMF.map_comp, detKernel]
      rw [ProbOracleComp.runWith_eq_run_interpret]
  rw [hlaw μ₁, hlaw μ₂]
  have hr_le : (r : ℝ) ≤ m := by exact_mod_cast Nat.sub_le m (k + 1)
  calc dist (((PMF.iid μ₁ r).bind fun s => (PMF.iid (PMF.iid μ₁ 2) Q).map (s, ·)).bind detKernel)
        (((PMF.iid μ₂ r).bind fun s => (PMF.iid (PMF.iid μ₂ 2) Q).map (s, ·)).bind detKernel)
      ≤ dist (PMF.iid μ₁ r) (PMF.iid μ₂ r) +
          dist (PMF.iid (PMF.iid μ₁ 2) Q) (PMF.iid (PMF.iid μ₂ 2) Q) :=
        dist_bind_pair_le _ _ _ _ detKernel
    _ ≤ r * dist μ₁ μ₂ + Q * (2 * dist μ₁ μ₂) := add_le_add (PMF.dist_iid_le μ₁ μ₂ r)
        ((PMF.dist_iid_le _ _ Q).trans
          (mul_le_mul_of_nonneg_left (PMF.dist_iid_le μ₁ μ₂ 2) (Nat.cast_nonneg Q)))
    _ = (r + 2 * Q : ℝ) * dist μ₁ μ₂ := by ring
    _ ≤ (m + 2 * Q : ℝ) * dist μ₁ μ₂ :=
        mul_le_mul_of_nonneg_right (add_le_add_left hr_le _) dist_nonneg

private theorem ofFn_zeroExtend_ofList {m k : ℕ} (hk : k ≤ m) {xs : List Bool}
    (hxs : xs.length = m) :
    List.ofFn (BitString.zeroExtend (d' := k) (BitString.ofList m xs)) = xs.take k := by
  refine List.ext_getElem (by simp [hxs, Nat.min_eq_left hk]) fun i h₁ h₂ => ?_
  simp only [List.length_ofFn] at h₁
  simp only [List.getElem_ofFn, BitString.zeroExtend, show i < m by omega, ↓reduceDIte,
    BitString.ofList, List.getElem_take]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]

private theorem naorReingoldWordSuffix_eq_tableEval (F : PrimeOrderGroupFamily) (d : F.Desc)
    {m : ℕ} (k : ℕ) (hk : k < m) (T : BitString k → F.Carrier d × F.Carrier d)
    (suffix : Fin (m - (k + 1)) → ZMod (F.order d)) {xs : List Bool} (hxs : xs.length = m) :
    let x := BitString.ofList m xs
    let pref := BitString.zeroExtend (d' := k) x
    let child := if xs.getD k false then F.encode d (T pref).2 else F.encode d (T pref).1
    let α : Fin m → ZMod (F.order d) := fun i =>
      if h : k + 1 ≤ i.val then suffix ⟨i.val - (k + 1), by omega⟩ else 1
    F.naorReingoldWordSuffix d child (List.ofFn fun j => (suffix j).val) (xs.drop (k + 1)) =
      F.encode d (F.naorReingoldTableEval d k hk T α x) := by
  dsimp only
  let x := BitString.ofList m xs
  let pref := BitString.zeroExtend (d' := k) x
  let base : F.Carrier d := if x ⟨k, hk⟩ then (T pref).2 else (T pref).1
  have hchild : (if xs.getD k false then F.encode d (T pref).2 else F.encode d (T pref).1) =
      F.encode d base := by
    change (if x ⟨k, hk⟩ then F.encode d (T pref).2 else F.encode d (T pref).1) = F.encode d base
    dsimp only [base]; split_ifs <;> rfl
  rw [hchild, naorReingoldWordSuffix, F.smul_encode, naorReingoldTableEval]
  refine congrArg (F.encode d) (congrArg (· • base) ?_)
  rw [naorReingoldProdNat_cast, Nat.cast_one, one_mul]
  have hzip :
      ((List.ofFn fun j : Fin (m - (k + 1)) => (suffix j).val).zip (xs.drop (k + 1))) =
        List.ofFn fun j : Fin (m - (k + 1)) => ((suffix j).val, x ⟨k + 1 + j.val, by omega⟩) := by
    refine List.ext_getElem (by simp [hxs]) fun j h₁ h₂ => ?_
    simp only [List.length_ofFn] at h₂
    simp only [List.getElem_zip, List.getElem_ofFn, List.getElem_drop, Prod.mk.injEq, true_and]
    dsimp only [x, BitString.ofList]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  rw [hzip, List.map_ofFn, List.prod_ofFn]
  simp only [Function.comp_def, ZMod.natCast_zmod_val]
  let e : Fin (k + 1) ⊕ Fin (m - (k + 1)) ≃ Fin m :=
    (finSumFinEquiv (m := k + 1) (n := m - (k + 1))).trans
      (Fin.castOrderIso (Nat.add_sub_of_le hk)).toEquiv
  rw [naorReingoldSuffixExp, ← Equiv.prod_comp e, Fintype.prod_sum_type]
  have hleft : (∏ i : Fin (k + 1),
      if k + 1 ≤ (e (Sum.inl i)).val ∧ x (e (Sum.inl i)) then
        (if h : k + 1 ≤ (e (Sum.inl i)).val then
          suffix ⟨(e (Sum.inl i)).val - (k + 1), by omega⟩ else 1)
      else 1) = 1 :=
    Finset.prod_eq_one fun i _ => by simp [Nat.not_le.mpr (show (e (.inl i)).val < k + 1 from i.2)]
  rw [hleft, one_mul]
  refine Finset.prod_congr rfl fun j _ => ?_
  have he_eq : e (Sum.inr j) = ⟨k + 1 + j.val, by omega⟩ := by ext; rfl
  simp only [he_eq, Nat.le_add_right, true_and, ↓reduceDIte]
  congr 2; ext; dsimp; omega

private theorem interpret_wordFiltered_eq_memoize_map {K V S : Type} [Fintype K] [Finite V]
    (keyMap : K ↪ List Bool) (valMap : V → S) (distK : K → PMF V)
    (sample' : List Bool → PMF S) (hsample : ∀ k : K, sample' (keyMap k) = (distK k).map valMap)
    {m : ℕ} (extractKey : List Bool → K) (extractRaw : List Bool → List Bool)
    (hkey : ∀ {xs : List Bool}, xs.length = m → keyMap (extractKey xs) = extractRaw xs)
    (post : List Bool → S → List Bool) (prog : WordOracleComp Unit Bool) :
    ((PMF.pi distK).bind fun T =>
      OracleComp.interpret
        (OracleComp.sumHandler ProbComp.unifOracle fun request =>
          PMF.pure (if request.2.length = m then post request.2 (valMap (T (extractKey request.2)))
            else []))
        prog) =
    ((OracleComp.interpret
      (OracleComp.sumHandler (fun r => StateT.lift (ProbComp.unifOracle r))
        fun request (cache : List (List Bool × S)) =>
          if request.2.length = m then
            (memoize sample' (extractRaw request.2) cache).bind fun res =>
              PMF.pure (post request.2 res.1, res.2)
          else PMF.pure ([], cache))
      prog).run []).map Prod.fst := by
  classical
  let adapter := fun xs : List Bool =>
    if xs.length = m then
      (post xs <$> ProbOracleComp.query (extractKey xs) :
        ProbOracleComp (fun _ : K => S) (List Bool))
    else pure []
  have h := RandomOracle.interpret_prob_eq_memoize_map keyMap valMap distK sample' hsample
    (ProbOracleComp.simulate (fun request : Unit × List Bool => adapter request.2) prog)
  have heager (T : K → V) (xs : List Bool) :
      OracleComp.interpret
        (OracleComp.sumHandler ProbComp.unifOracle fun key => PMF.pure (valMap (T key)))
        (adapter xs) =
      PMF.pure (if xs.length = m then post xs (valMap (T (extractKey xs))) else []) := by
    by_cases hq : xs.length = m <;>
      simp [adapter, hq, OracleComp.interpret_map, ProbOracleComp.interpret_query,
        PMF.monad_map_eq_map, PMF.pure_map, PMF.monad_pure_eq_pure]
  have hstep (xs : List Bool) :
      OracleComp.interpret
        (OracleComp.sumHandler (fun r => StateT.lift (ProbComp.unifOracle r))
          fun key => memoize sample' (keyMap key))
        (adapter xs) =
      fun cache =>
        if xs.length = m then
          (memoize sample' (extractRaw xs) cache).bind fun res => PMF.pure (post xs res.1, res.2)
        else PMF.pure ([], cache) := by
    funext cache
    by_cases hq : xs.length = m
    · simp only [adapter, hq, ↓reduceIte, OracleComp.interpret_map, ProbOracleComp.interpret_query,
        hkey hq]
      rfl
    · simp only [adapter, hq, ↓reduceIte, OracleComp.interpret_pure]
      rfl
  simpa only [ProbOracleComp.interpret_simulate, heager, hstep, PMF.monad_bind_eq_bind] using h

private theorem frontierLevelWithExpLaw_uniform_eq_multi (F : PrimeOrderGroupFamily) (d : F.Desc)
    {m : ℕ} (k : ℕ) (hk : k < m) (prog : WordOracleComp Unit Bool) (u₀ v₀ w₀ : F.Carrier d) :
    frontierLevelWithExpLaw F d m k prog (F.encode d u₀) (F.encode d v₀) (F.encode d w₀)
      (PMF.uniformOfFintype (ZMod (F.order d))) =
      (F.multiDDHRerandomizeLaw d (BitString k) u₀ v₀ w₀).bind
        (naorReingoldWordLevelTest F d k hk prog u₀) := by
  have hpairLaw :
      ((PMF.iid (PMF.uniformOfFintype (ZMod (F.order d))) 2).map fun p =>
        F.ddhFixedUWordRerandomize d (F.encode d u₀) (F.encode d v₀) (F.encode d w₀)
          (p 0).val (p 1).val) =
      (F.ddhFixedURerandomizeLaw d u₀ v₀ w₀).map (Prod.map (F.encode d) (F.encode d)) := by
    refine (iid_two_map (PMF.uniformOfFintype (ZMod (F.order d)))
      (fun a b => F.ddhFixedUWordRerandomize d (F.encode d u₀) (F.encode d v₀) (F.encode d w₀)
        a.val b.val)).trans ?_
    simp only [ddhFixedURerandomizeLaw, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
      PMF.map, Function.comp_def, Prod.map, PMF.bind_bind, PMF.pure_bind,
      F.ddhFixedUWordRerandomize_encode, ZMod.natCast_zmod_val]
  unfold frontierLevelWithExpLaw naorReingoldWordLevelTest
  rw [hpairLaw]
  simp only [iid_uniformOfFintype, PMF.monad_bind_eq_bind]
  symm
  rw [PMF.bind_comm]
  congr 1; funext suffix
  let αs := List.ofFn fun j => (suffix j).val
  let valMap : F.Carrier d × F.Carrier d → List Bool × List Bool :=
    Prod.map (F.encode d) (F.encode d)
  let post : List Bool → List Bool × List Bool → List Bool := fun xs vw =>
    F.naorReingoldWordSuffix d (if xs.getD k false then vw.2 else vw.1) αs (xs.drop (k + 1))
  have hmemo := interpret_wordFiltered_eq_memoize_map
    ⟨List.ofFn, List.ofFn_injective⟩ valMap
    (fun _ : BitString k => F.ddhFixedURerandomizeLaw d u₀ v₀ w₀)
    (fun _ => (F.ddhFixedURerandomizeLaw d u₀ v₀ w₀).map valMap) (fun _ => rfl)
    (fun xs => BitString.zeroExtend (d' := k) (BitString.ofList m xs)) (fun xs => xs.take k)
    (fun hq => ofFn_zeroExtend_ofList hk.le hq) post prog
  rw [pi_ddhFixedURerandomizeLaw_eq_multi F d (BitString k) u₀ v₀ w₀] at hmemo
  refine Eq.trans ?_ hmemo
  congr 1; funext T
  dsimp only [naorReingoldWordRun]
  congr 1; funext q
  cases q with
  | inl _ => rfl
  | inr request =>
    dsimp only [OracleComp.sumHandler]
    by_cases hq : request.2.length = m
    · simp only [hq, ↓reduceIte, naorReingoldWordOracle, post, valMap]
      exact congrArg PMF.pure (naorReingoldWordSuffix_eq_tableEval F d k hk T suffix hq).symm
    · simp [hq, naorReingoldWordOracle]

private noncomputable def naorReingoldDescRealGame (F : PrimeOrderGroupFamily)
    (setup : ℕ → PMF F.Desc) (inLen : ℕ → ℕ)
    (adv : ℕ → F.Desc → WordOracleComp Unit Bool) (n : ℕ) : Game := do
  let d ← setup n
  let α₀ ← PMF.uniformOfFintype (ZMod (F.order d))
  let α ← PMF.uniformOfFintype (Fin (inLen n) → ZMod (F.order d))
  naorReingoldWordRun F d (adv n d) (F.naorReingoldEval d α₀ α)

private noncomputable def naorReingoldDescIdealGame (F : PrimeOrderGroupFamily)
    (setup : ℕ → PMF F.Desc) (inLen : ℕ → ℕ)
    (adv : ℕ → F.Desc → WordOracleComp Unit Bool) (n : ℕ) : Game := do
  let d ← setup n
  let B ← PMF.uniformOfFintype (BitString (inLen n) → ZMod (F.order d))
  naorReingoldWordRun F d (adv n d) (fun x => B x • F.generator d)

private theorem eval_naorReingoldDescToDDHDistinguisher (F : PrimeOrderGroupFamily)
    (inLen : ℕ → ℕ) (adv : ℕ → F.Desc → WordOracleComp Unit Bool) (n : ℕ)
    (d : F.Desc) (u v w : F.Carrier d) :
    ProbComp.eval (naorReingoldDescToDDHDistinguisher F inLen adv n d u v w) =
      (PMF.uniformOfFintype (Fin (dyadicSize (inLen n)))).bind fun i =>
        if i.val < inLen n then
          frontierLevelWithExpLaw F d (inLen n) i.val (adv n d) (F.encode d u) (F.encode d v)
            (F.encode d w) (F.sampleModZModLaw (n + (F.encDesc d).length) d)
        else PMF.pure false := by
  unfold naorReingoldDescToDDHDistinguisher
  rw [ProbComp.eval_bind, ProbComp.eval_sampleDyadicIndex, PMF.bind_map]
  congr 1; funext i
  dsimp only [Function.comp_apply]
  by_cases hk : i.val < inLen n
  · simp only [hk, ↓reduceIte]
    exact eval_frontierLevel_eq_withExpLaw F n (inLen n) i.val d (adv n d)
      (F.encode d u) (F.encode d v) (F.encode d w)
  · simp [hk]

private theorem bind_ite_comm {α β γ : Type} (μ : PMF α) (ν : PMF γ) (p : γ → Prop)
    [DecidablePred p] (f : α → γ → PMF β) (fallback : PMF β) :
    (μ.bind fun a => ν.bind fun c => if p c then f a c else fallback) =
      (ν.bind fun c => if p c then μ.bind fun a => f a c else fallback) := by
  rw [PMF.bind_comm]
  congr 1; funext c
  by_cases hc : p c <;> simp [hc, PMF.bind_const]

private theorem advantage_exactDDHRandom_le (F : PrimeOrderGroupFamily)
    (setup : ℕ → PMF F.Desc) (m : ℕ) (adv : F.Desc → WordOracleComp Unit Bool) (n : ℕ) :
    Game.advantage
      ((setup n).bind fun d =>
        (PMF.uniformOfFintype (ZMod (F.order d))).bind fun α =>
          (PMF.uniformOfFintype (ZMod (F.order d))).bind fun β =>
            (PMF.uniformOfFintype (ZMod (F.order d))).bind fun γ =>
              (PMF.uniformOfFintype (Fin (dyadicSize m))).bind fun i =>
                if i.val < m then
                  frontierLevelWithExpLaw F d m i.val (adv d)
                    (F.encode d (α • F.generator d))
                    (F.encode d (β • F.generator d))
                    (F.encode d (γ • F.generator d))
                    (PMF.uniformOfFintype (ZMod (F.order d)))
                else PMF.pure false)
      ((PMF.uniformOfFintype (Fin (dyadicSize m))).bind fun i =>
        if i.val < m then (setup n).bind fun d => naorReingoldWordHybridAt F d m (i.val + 1) (adv d)
        else PMF.pure false) ≤
      (∑' d, setup n d * (F.order d : ℝ≥0∞)⁻¹).toNNReal := by
  rw [← bind_ite_comm (setup n) (PMF.uniformOfFintype (Fin (dyadicSize m)))
    (fun i : Fin (dyadicSize m) => i.val < m)]
  refine F.advantage_bind_le_expected_inv_order (setup n) _ _ fun d => ?_
  simp_rw [bind_ite_comm (PMF.uniformOfFintype (ZMod (F.order d)))
    (PMF.uniformOfFintype (Fin (dyadicSize m))) (fun i : Fin (dyadicSize m) => i.val < m)]
  refine Game.advantage_bind_le_nnreal (PMF.uniformOfFintype (Fin (dyadicSize m))) _ _ fun i => ?_
  by_cases hk : i.val < m
  · simp only [hk, ↓reduceIte,
      frontierLevelWithExpLaw_uniform_eq_multi F d i.val hk (adv d),
      ← multiDDHRandomTupleLaw_naorReingoldWordLevelTest F d i.val hk (adv d)]
    simpa only [pmf_norm, PrimeOrderGroupFamily.ddhRandomTupleLaw] using
      F.advantage_ddhRandomTupleLaw_multiDDHRerandomizeLaw_le d (BitString i.val)
        (naorReingoldWordLevelTest F d i.val hk (adv d))
  · simp [hk]

private theorem advantage_naorReingoldDescGame_le (F : PrimeOrderGroupFamily)
    (setup : ℕ → PMF F.Desc) (inLen : ℕ → ℕ)
    (adv : ℕ → F.Desc → WordOracleComp Unit Bool) (n : ℕ)
    (Q : F.Desc → ℕ) {ε : ℝ≥0}
    (hQ : ∀ d ∈ (setup n).support, (adv n d).IsQueryBounded (Q d))
    (hε : ∀ d ∈ (setup n).support,
      ((inLen n + 2 * Q d : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ (n + (F.encDesc d).length) ≤ ε) :
    Game.advantage
      (naorReingoldDescRealGame F setup inLen adv n)
      (naorReingoldDescIdealGame F setup inLen adv n) ≤
      (dyadicSize (inLen n) : ℝ≥0) *
        (Game.advantage
          (F.ddhRealGame setup (naorReingoldDescToDDHDistinguisher F inLen adv) n)
          (F.ddhRandomGame setup (naorReingoldDescToDDHDistinguisher F inLen adv) n) +
          2 * ε +
          (∑' d, setup n d * (F.order d : ℝ≥0∞)⁻¹).toNNReal) := by
  let m := inLen n
  let cap := dyadicSize m
  let H : ℕ → Game := fun k => (setup n).bind fun d => naorReingoldWordHybridAt F d m k (adv n d)
  have hH0 : H 0 = naorReingoldDescRealGame F setup inLen adv n :=
    congrArg ((setup n).bind ·) (funext fun d => naorReingoldWordHybridAt_zero F d m (adv n d))
  have hHm : H m = naorReingoldDescIdealGame F setup inLen adv n :=
    congrArg ((setup n).bind ·) (funext fun d => naorReingoldWordHybridAt_self F d m (adv n d))
  rw [← hH0, ← hHm, Game.advantage_hybrid_average H m cap (lt_dyadicSize m).le]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  let ddhReal := F.ddhRealGame setup (naorReingoldDescToDDHDistinguisher F inLen adv) n
  let ddhRandom := F.ddhRandomGame setup (naorReingoldDescToDDHDistinguisher F inLen adv) n
  let frontierAt : (d : F.Desc) → ZMod (F.order d) → ZMod (F.order d) → ZMod (F.order d) →
      PMF (ZMod (F.order d)) → Fin cap → Game := fun d α β γ expLaw i =>
    if i.val < m then
      frontierLevelWithExpLaw F d m i.val (adv n d)
        (F.encode d (α • F.generator d)) (F.encode d (β • F.generator d))
        (F.encode d (γ • F.generator d)) expLaw
    else PMF.pure false
  let exactDDHReal : Game :=
    (setup n).bind fun d =>
      (PMF.uniformOfFintype (ZMod (F.order d))).bind fun α =>
        (PMF.uniformOfFintype (ZMod (F.order d))).bind fun β =>
          (PMF.uniformOfFintype (Fin cap)).bind fun i =>
            frontierAt d α β (α * β) (PMF.uniformOfFintype (ZMod (F.order d))) i
  let exactDDHRandom : Game :=
    (setup n).bind fun d =>
      (PMF.uniformOfFintype (ZMod (F.order d))).bind fun α =>
        (PMF.uniformOfFintype (ZMod (F.order d))).bind fun β =>
          (PMF.uniformOfFintype (ZMod (F.order d))).bind fun γ =>
            (PMF.uniformOfFintype (Fin cap)).bind fun i =>
              frontierAt d α β γ (PMF.uniformOfFintype (ZMod (F.order d))) i
  have hEqReal :
      ((PMF.uniformOfFintype (Fin cap)).bind fun i =>
        if i.val < m then H i.val else PMF.pure false) = exactDDHReal := by
    dsimp only [H, exactDDHReal, frontierAt]
    rw [← bind_ite_comm (setup n) (PMF.uniformOfFintype (Fin cap)) (fun i : Fin cap => i.val < m)]
    congr 1; funext d
    symm
    simp_rw [bind_ite_comm (PMF.uniformOfFintype (ZMod (F.order d)))
      (PMF.uniformOfFintype (Fin cap)) (fun i : Fin cap => i.val < m)]
    congr 1; funext i
    by_cases hk : i.val < m
    · simp only [hk, ↓reduceIte, frontierLevelWithExpLaw_uniform_eq_multi F d i.val hk (adv n d),
        F.multiDDHRerandomizeLaw_real d (BitString i.val), PMF.bind_const,
        multiDDHRealTupleLaw_naorReingoldWordLevelTest F d i.val hk (adv n d)]
    · simp [hk]
  have hstep_err :
      ∀ d ∈ (setup n).support, ∀ α β γ i,
        Game.advantage
          (frontierAt d α β γ (PMF.uniformOfFintype (ZMod (F.order d))) i)
          (frontierAt d α β γ (F.sampleModZModLaw (n + (F.encDesc d).length) d) i) ≤ ε := by
    intro d hd α β γ i
    dsimp only [frontierAt]
    by_cases hk : i.val < m
    · simp only [hk, ↓reduceIte]
      refine le_trans ?_ (hε d hd)
      rw [Game.advantage_eq_nndist, ← NNReal.coe_le_coe, coe_nndist]
      calc dist
            (frontierLevelWithExpLaw F d m i.val (adv n d) _ _ _
              (PMF.uniformOfFintype (ZMod (F.order d))))
            (frontierLevelWithExpLaw F d m i.val (adv n d) _ _ _
              (F.sampleModZModLaw (n + (F.encDesc d).length) d))
          ≤ (m + 2 * Q d : ℝ) *
              dist (PMF.uniformOfFintype (ZMod (F.order d)))
                (F.sampleModZModLaw (n + (F.encDesc d).length) d) :=
            dist_frontierLevelWithExpLaw_le F d m i.val (Q d) (hQ d hd) _ _ _ _ _
        _ ≤ (m + 2 * Q d : ℝ) * (1 / 2 ^ (n + (F.encDesc d).length)) :=
            mul_le_mul_of_nonneg_left (F.dist_sampleModZModLaw_le _ d) (by positivity)
        _ = ((((m + 2 * Q d : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ (n + (F.encDesc d).length) : ℝ≥0) : ℝ) := by
            push_cast; ring
    · simp [hk]
  have hAdvRealApprox : Game.advantage exactDDHReal ddhReal ≤ ε := by
    simp only [ddhReal, ddhRealGame, Game.withSetup, eval_ddhRealExperiment,
      eval_naorReingoldDescToDDHDistinguisher F inLen adv n]
    peel_binds d α β i
    exact hstep_err d d_mem α β (α * β) i
  have hAdvRandomApprox : Game.advantage exactDDHRandom ddhRandom ≤ ε := by
    simp only [ddhRandom, ddhRandomGame, Game.withSetup, eval_ddhRandomExperiment,
      eval_naorReingoldDescToDDHDistinguisher F inLen adv n]
    peel_binds d α β γ i
    exact hstep_err d d_mem α β γ i
  game_trans [exactDDHReal, ddhReal, ddhRandom, exactDDHRandom]
    using [hEqReal, hAdvRealApprox, le_rfl, hAdvRandomApprox,
      advantage_exactDDHRandom_le F setup m (adv n) n]

/-- Ideal-sampling step toward [BonehShoup2023], Exercise 10.4 (p. 424), not the cited result:
in `naorReingoldWordRealGame`, whose keys are drawn exactly uniformly from `ZMod (F.order d)`, if
`adversary` makes at most `Q d` queries on `d ∈ (setup n).support` with modular-sampling slack
bounded by `ε`, then its PRF distinguishing advantage is at most `dyadicSize (inLen n)` times the
single-challenge DDH advantage of `naorReingoldToDDHDistinguisher` plus `2 * ε` plus the
setup-averaged inverse group order. With the fair-coin keys of `naorReingoldProbRealGame` the bound
gains the term of `advantage_naorReingoldProbRealGame_wordRealGame_le`. -/
theorem advantage_naorReingoldWordGame_le_ideal (setup : ℕ → PMF F.Desc) (inLen : ℕ → ℕ)
    (adversary : OracleDistinguisher) (n : ℕ) (Q : F.Desc → ℕ) {ε : ℝ≥0}
    (hQ : ∀ d ∈ (setup n).support, (adversary n (F.encDesc d)).IsQueryBounded (Q d))
    (hε : ∀ d ∈ (setup n).support,
      ((inLen n + 2 * Q d : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ (n + (F.encDesc d).length) ≤ ε) :
    Game.advantage
      (F.naorReingoldWordRealGame setup inLen adversary n)
      (F.naorReingoldWordIdealGame setup inLen adversary n) ≤
      (dyadicSize (inLen n) : ℝ≥0) *
        (Game.advantage
          (F.ddhRealGame setup (F.naorReingoldToDDHDistinguisher inLen adversary) n)
          (F.ddhRandomGame setup (F.naorReingoldToDDHDistinguisher inLen adversary) n) +
          2 * ε +
          (∑' d, setup n d * (F.order d : ℝ≥0∞)⁻¹).toNNReal) :=
  advantage_naorReingoldDescGame_le F setup inLen (fun n d => adversary n (F.encDesc d)) n Q hQ hε

/-- Drawing the `m + 1` Naor–Reingold exponents from the modular-sampling law instead of exactly
uniformly changes the distribution of any continuation `detRun` by at most `(m + 1) / 2 ^ n`. -/
private theorem advantage_sampleModZModLaw_bind_le (n : ℕ) (d : F.Desc) {m : ℕ}
    (detRun : ZMod (F.order d) × (Fin m → ZMod (F.order d)) → PMF Bool) :
    Game.advantage
      (((F.sampleModZModLaw (n + (F.encDesc d).length) d).bind fun α₀ =>
        (PMF.iid (F.sampleModZModLaw (n + (F.encDesc d).length) d) m).map (α₀, ·)).bind detRun)
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun α₀ =>
        (PMF.uniformOfFintype (Fin m → ZMod (F.order d))).bind fun α => detRun (α₀, α)) ≤
      ((m + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n := by
  let μ := F.sampleModZModLaw (n + (F.encDesc d).length) d
  let ν := PMF.uniformOfFintype (ZMod (F.order d))
  have hword :
      (ν.bind fun α₀ => (PMF.uniformOfFintype (Fin m → ZMod (F.order d))).bind fun α =>
        detRun (α₀, α)) =
      (ν.bind fun α₀ => (PMF.iid ν m).map (α₀, ·)).bind detRun := by
    rw [iid_uniformOfFintype]
    simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
  rw [hword, Game.advantage_eq_nndist, ← NNReal.coe_le_coe, coe_nndist]
  have hd_step : dist μ ν ≤ 1 / 2 ^ n := by
    rw [dist_comm]
    exact (F.dist_sampleModZModLaw_le (n + (F.encDesc d).length) d).trans <|
      one_div_le_one_div_of_le (by positivity)
        (pow_le_pow_right₀ (by norm_num) (Nat.le_add_right n _))
  calc dist ((μ.bind fun x => (PMF.iid μ m).map (x, ·)).bind detRun)
        ((ν.bind fun x => (PMF.iid ν m).map (x, ·)).bind detRun)
      ≤ dist μ ν + dist (PMF.iid μ m) (PMF.iid ν m) := dist_bind_pair_le μ ν _ _ detRun
    _ ≤ dist μ ν + m * dist μ ν := add_le_add_right (PMF.dist_iid_le μ ν m) _
    _ = (m + 1 : ℝ) * dist μ ν := by ring
    _ ≤ (m + 1 : ℝ) * (1 / 2 ^ n) := mul_le_mul_of_nonneg_left hd_step (by positivity)
    _ = ((((m + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) := by push_cast; ring

private theorem advantage_probNaorReingold_le (F : PrimeOrderGroupFamily)
    (n m : ℕ) (d : F.Desc) (prog : WordOracleComp Unit Bool) (post : List Bool → List Bool) :
    Game.advantage
      (ProbComp.eval (do
        let α₀ ← F.sampleNaorReingoldExp n d
        let αs ← OracleComp.replicate m (F.sampleNaorReingoldExp n d)
        OracleComp.interpret
          (OracleComp.sumHandler ProbComp.unifFin fun request =>
            pure (if request.2.length = m then
              post (F.naorReingoldWordEval d α₀ αs request.2)
            else []))
          prog))
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun α₀ =>
        (PMF.uniformOfFintype (Fin m → ZMod (F.order d))).bind fun α =>
          OracleComp.interpret
            (OracleComp.sumHandler ProbComp.unifOracle fun request =>
              PMF.pure (if request.2.length = m then
                post (F.encode d (F.naorReingoldEval d α₀ α (BitString.ofList m request.2)))
              else []))
            prog) ≤ ((m + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n := by
  let detRun : (ZMod (F.order d) × (Fin m → ZMod (F.order d))) → PMF Bool := fun p =>
    OracleComp.interpret
      (OracleComp.sumHandler ProbComp.unifOracle fun request =>
        PMF.pure (if request.2.length = m then
          post (F.encode d (F.naorReingoldEval d p.1 p.2 (BitString.ofList m request.2)))
        else []))
      prog
  refine Eq.trans_le (congrArg (Game.advantage · _) ?_)
    (F.advantage_sampleModZModLaw_bind_le n d detRun)
  simp only [ProbComp.eval_bind, ProbOracleComp.eval_interpret, ProbComp.eval_pure,
    eval_sampleNaorReingoldExp_eq_map_val F n d,
    eval_replicate_sampleNaorReingoldExp_eq_iid F n m d,
    PMF.bind_bind, PMF.bind_map, Function.comp_def]
  congr 1
  funext α₀
  congr 1
  funext α
  dsimp only [detRun]
  congr 1; funext q
  cases q with
  | inl r => rfl
  | inr request =>
    dsimp only [OracleComp.sumHandler]
    by_cases hq : request.2.length = m
    · simp only [hq, ↓reduceIte]
      have heval := F.naorReingoldWordEval_eq_encode d α₀.val (fun i => (α i).val)
        (BitString.ofList m request.2)
      simp only [ZMod.natCast_zmod_val, BitString.ofFn_ofList hq] at heval
      rw [heval]
    · simp [hq]

/-- **Modular-sampling distance between `naorReingoldProbRealGame` and `naorReingoldWordRealGame`**:
replacing `(inLen n + 1)` calls to `sampleNaorReingoldExp` by exact uniform `ZMod (F.order d)`
exponents changes the output distribution by at most `(inLen n + 1) / 2 ^ n`. -/
theorem advantage_naorReingoldProbRealGame_wordRealGame_le (setup : ℕ → PMF F.Desc)
    (inLen : ℕ → ℕ) (adversary : OracleDistinguisher) (n : ℕ) :
    Game.advantage
      (F.naorReingoldProbRealGame setup inLen adversary n)
      (F.naorReingoldWordRealGame setup inLen adversary n) ≤
      ((inLen n + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n := by
  simp only [naorReingoldProbRealGame, naorReingoldWordRealGame, naorReingoldWordOracle,
    PMF.monad_bind_eq_bind]
  peel_binds d
  simpa only [id_eq] using
    advantage_probNaorReingold_le F n (inLen n) d (adversary n (F.encDesc d)) id

private theorem DDH.negligible_naorReingoldDescGame {F : PrimeOrderGroupFamily}
    {setup : ℕ → PMF F.Desc} {inLen : ℕ → ℕ}
    (hDDH : F.DDH setup) (hinLen : ComputableInPolyTime inLen encUnary encUnary)
    {adv : ℕ → F.Desc → WordOracleComp Unit Bool}
    (hadv : IsOraclePPTOn (encPair encUnary F.encDesc) encBool (fun p => adv p.1 p.2)) :
    Negligible fun n =>
      Game.advantage
        (naorReingoldDescRealGame F setup inLen adv n)
        (naorReingoldDescIdealGame F setup inLen adv n) := by
  obtain ⟨cQ, eQ, hQb⟩ := hadv.query_bounds
  obtain ⟨C, hC⟩ :=
    (show PolynomiallyBounded fun L => (L + 1) ^ eQ by fun_prop).exists_le_mul_two_pow
  let Q : ℕ → F.Desc → ℕ := fun n d =>
    cQ * ((encPair encUnary F.encDesc (n, d)).length + 1) ^ eQ
  let ε : ℕ → ℝ≥0 := fun n =>
    ((inLen n + 2 * cQ * C * (2 * n + 6) ^ eQ : ℕ) : ℝ≥0) * ((2 : ℝ≥0)⁻¹) ^ n
  have hε_supp (n : ℕ) (d : F.Desc) (_ : d ∈ (setup n).support) :
      ((inLen n + 2 * Q n d : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ (n + (F.encDesc d).length) ≤ ε n := by
    let L := (F.encDesc d).length
    have hlen : (encPair encUnary F.encDesc (n, d)).length + 1 ≤ (2 * n + 6) * (L + 1) := by
      simp only [length_encPair, encUnary_apply, List.length_replicate, Nat.add_mul]
      have : 2 * n ≤ 2 * n * (L + 1) := Nat.le_mul_of_pos_right _ (Nat.add_pos_right L zero_lt_one)
      dsimp only [L] at *; omega
    have hQd_le : Q n d ≤ cQ * C * (2 * n + 6) ^ eQ * 2 ^ L := calc
      Q n d ≤ cQ * ((2 * n + 6) * (L + 1)) ^ eQ := by
        dsimp only [Q]
        gcongr
      _ = cQ * ((2 * n + 6) ^ eQ * (L + 1) ^ eQ) := by rw [Nat.mul_pow]
      _ ≤ cQ * ((2 * n + 6) ^ eQ * (C * 2 ^ L)) := by
        gcongr
        exact hC L
      _ = cQ * C * (2 * n + 6) ^ eQ * 2 ^ L := by ring
    have hnum_le : inLen n + 2 * Q n d ≤ (inLen n + 2 * cQ * C * (2 * n + 6) ^ eQ) * 2 ^ L := by
      have := Nat.le_mul_of_pos_right (inLen n) (Nat.two_pow_pos L)
      rw [Nat.add_mul]; nlinarith
    rw [pow_add]
    refine (div_le_div_of_nonneg_right
      (by exact_mod_cast hnum_le : _ ≤ ((inLen n + 2 * cQ * C * (2 * n + 6) ^ eQ : ℕ) : ℝ≥0) *
        (2 : ℝ≥0) ^ L) (by positivity)).trans_eq ?_
    rw [mul_div_mul_right _ _ (by positivity), div_eq_mul_inv, ← inv_pow]
  have hddh_neg := hDDH _ (isPPT_naorReingoldDescToDDHDistinguisher F hinLen hadv)
  have hinv_neg := hDDH.negligible_expected_inv_order
  negligible using fun n =>
    advantage_naorReingoldDescGame_le F setup inLen adv n (Q n) (fun d _ => (hQb (n, d)).1)
      (hε_supp n)

/-- Ideal-sampling step toward [BonehShoup2023], Exercise 10.4 (p. 424), not the cited result: if
`F.DDH setup` holds and `inLen` is computable in polynomial time in unary, no `IsOraclePPT`
adversary can distinguish `naorReingoldWordRealGame`, whose keys are drawn exactly uniformly from
`ZMod (F.order d)`, from `naorReingoldWordIdealGame` with non-negligible advantage. The theorem for
the keys drawn with the fair-coin sampler `sampleNaorReingoldExp` is
`DDH.negligible_naorReingoldProbGame`, which uses this one. -/
theorem DDH.negligible_naorReingoldWordGame_ideal {F : PrimeOrderGroupFamily}
    {setup : ℕ → PMF F.Desc} {inLen : ℕ → ℕ}
    (hDDH : F.DDH setup) (hinLen : ComputableInPolyTime inLen encUnary encUnary)
    {adversary : OracleDistinguisher} (hadversary : IsOraclePPT encBool adversary) :
    Negligible fun n =>
      Game.advantage
        (F.naorReingoldWordRealGame setup inLen adversary n)
        (F.naorReingoldWordIdealGame setup inLen adversary n) := by
  exact hDDH.negligible_naorReingoldDescGame hinLen (isOraclePPTOn_adversary_encDesc hadversary)

private theorem negligible_add_one_div_two_pow {inLen : ℕ → ℕ}
    (hinLen : ComputableInPolyTime inLen encUnary encUnary) :
    Negligible fun n => ((inLen n + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n := by
  negligible

/-- **Asymptotic DDH security of the executable Naor–Reingold group-PRF
(`naorReingoldProbRealGame`)** ([BonehShoup2023], Exercise 10.4; [NaorReingold2004], Theorem 4.1):
if `F.DDH setup` holds and `inLen` is computable in polynomial time in unary, no `IsOraclePPT`
adversary can distinguish `naorReingoldProbRealGame` from `naorReingoldWordIdealGame` with
non-negligible advantage. -/
theorem DDH.negligible_naorReingoldProbGame {F : PrimeOrderGroupFamily}
    {setup : ℕ → PMF F.Desc} {inLen : ℕ → ℕ}
    (hDDH : F.DDH setup) (hinLen : ComputableInPolyTime inLen encUnary encUnary)
    {adversary : OracleDistinguisher} (hadversary : IsOraclePPT encBool adversary) :
    Negligible fun n =>
      Game.advantage
        (F.naorReingoldProbRealGame setup inLen adversary n)
        (F.naorReingoldWordIdealGame setup inLen adversary n) := by
  refine negligible_of_le
    ((negligible_add_one_div_two_pow hinLen).add
      (hDDH.negligible_naorReingoldWordGame_ideal hinLen hadversary)) fun n => ?_
  game_trans [F.naorReingoldWordRealGame setup inLen adversary n]
    using [F.advantage_naorReingoldProbRealGame_wordRealGame_le setup inLen adversary n, le_rfl]

/-! ### Universal-hash bit-string Naor–Reingold PRF -/

/-- Word-level universal-hash Naor–Reingold evaluation (paraphrase of [NaorReingold2004],
Section 4.1, Construction 4.2): evaluate `naorReingoldWordEval` and hash the resulting encoded
group element into `{0, 1}^{outLen}` with `linearHashKDF`. -/
@[expose] def naorReingoldHashedWordEval (outLen : ℕ) (bound : F.Desc → ℕ) (d : F.Desc)
    (seed : List Bool) (α₀ : ℕ) (αs : List ℕ) (xs : List Bool) : List Bool :=
  F.linearHashKDF (fun _ => outLen) bound ((d, seed), F.naorReingoldWordEval d α₀ αs xs)

/-- `naorReingoldHashedWordEval` always outputs `outLen` bits. -/
@[simp] theorem length_naorReingoldHashedWordEval (outLen : ℕ) (bound : F.Desc → ℕ)
    (d : F.Desc) (seed : List Bool) (α₀ : ℕ) (αs : List ℕ) (xs : List Bool) :
    (F.naorReingoldHashedWordEval outLen bound d seed α₀ αs xs).length = outLen := by
  simp [naorReingoldHashedWordEval]

/-- `naorReingoldHashedWordEval` is computable in polynomial time when `outLen` is given in unary
and `bound` is computable in polynomial time in unary from `d`. -/
theorem computableInPolyTime_naorReingoldHashedWordEval {bound : F.Desc → ℕ}
    (hbound : ComputableInPolyTime bound F.encDesc encUnary) :
    ComputableInPolyTime
      (fun input : ℕ × F.Desc × List Bool × ℕ × List ℕ × List Bool =>
        F.naorReingoldHashedWordEval input.1 bound input.2.1 input.2.2.1 input.2.2.2.1
          input.2.2.2.2.1 input.2.2.2.2.2)
      (encPair encUnary
        (encPair F.encDesc
          (encPair encBits (encPair encNat (encPair (encList encNat) encBits)))))
      encBits := by
  unfold naorReingoldHashedWordEval linearHashKDF
  dsimp only [SeededDesc.desc, SeededDesc.seed]
  fun_prop

/-- Setup-parameterized real universal-hash Naor–Reingold bit-string PRF game with exact uniform
`ZMod (F.order d)` exponents and public hash seed `(d, seed)` encoded via `F.withSeed.encDesc`
(paraphrase of [NaorReingold2004], Section 4.1, Construction 4.2, Theorem 4.3, and Remark 4.2). -/
@[expose] noncomputable def naorReingoldHashedRealGame (setup : ℕ → PMF F.Desc)
    (inLen outLen : ℕ → ℕ) (bound : F.Desc → ℕ) (adversary : OracleDistinguisher) (n : ℕ) :
    Game := do
  let ds ← F.seededSetup setup (F.linearHashSeedLen outLen bound) n
  let α₀ ← PMF.uniformOfFintype (ZMod (F.order ds.1))
  let α ← PMF.uniformOfFintype (Fin (inLen n) → ZMod (F.order ds.1))
  OracleComp.interpret
    (OracleComp.sumHandler ProbComp.unifOracle fun request =>
      PMF.pure (if request.2.length = inLen n then
        F.linearHashKDF (fun _ => outLen n) bound
          (ds, F.encode ds.1 (F.naorReingoldEval ds.1 α₀ α
            (BitString.ofList (inLen n) request.2)))
      else []))
    (adversary n (F.withSeed.encDesc ds))

/-- Setup-parameterized executable real universal-hash Naor–Reingold bit-string PRF game sampling
exponents via `sampleNaorReingoldExp` (original). -/
@[expose] noncomputable def naorReingoldHashedProbRealGame (setup : ℕ → PMF F.Desc)
    (inLen outLen : ℕ → ℕ) (bound : F.Desc → ℕ) (adversary : OracleDistinguisher)
    (n : ℕ) : Game := do
  let ds ← F.seededSetup setup (F.linearHashSeedLen outLen bound) n
  ProbComp.eval (do
    let α₀ ← F.sampleNaorReingoldExp n ds.1
    let αs ← OracleComp.replicate (inLen n) (F.sampleNaorReingoldExp n ds.1)
    OracleComp.interpret
      (OracleComp.sumHandler ProbComp.unifFin fun request =>
        pure (if request.2.length = inLen n then
          F.naorReingoldHashedWordEval (outLen n) bound ds.1 ds.2 α₀ αs request.2
        else []))
      (adversary n (F.withSeed.encDesc ds)))

/-- Setup-parameterized ideal bit-string random-function game for universal-hash Naor–Reingold:
sample `(d, seed) ← F.seededSetup setup (F.linearHashSeedLen outLen bound) n`, draw an independent
uniform random function `f : BitString (inLen n) → BitString (outLen n)`, and pass
`F.withSeed.encDesc (d, seed)` to `adversary` (paraphrase of [NaorReingold2004], Section 4.1,
Theorem 4.3 and Remark 4.2). -/
@[expose] noncomputable def naorReingoldHashedIdealGame (setup : ℕ → PMF F.Desc)
    (inLen outLen : ℕ → ℕ) (bound : F.Desc → ℕ) (adversary : OracleDistinguisher) (n : ℕ) :
    Game := do
  let ds ← F.seededSetup setup (F.linearHashSeedLen outLen bound) n
  let f ← PMF.uniformOfFintype (BitString (inLen n) → BitString (outLen n))
  OracleComp.interpret
    (OracleComp.sumHandler ProbComp.unifOracle fun request =>
      PMF.pure (if request.2.length = inLen n then
        List.ofFn (f (BitString.ofList (inLen n) request.2))
      else []))
    (adversary n (F.withSeed.encDesc ds))

/-- Intermediate hybrid game for universal-hash Naor–Reingold: sample `(d, seed)` via `seededSetup`,
draw an independent uniform random group-valued table `B : BitString (inLen n) → ZMod (F.order d)`,
and hash each queried group element `B x • g` with `linearHashKDF` (paraphrase of
[NaorReingold2004], Section 4.1, Theorem 4.3 and Remark 4.2, using Lemma 4.2). -/
@[expose] noncomputable def naorReingoldHashedGroupIdealGame (setup : ℕ → PMF F.Desc)
    (inLen outLen : ℕ → ℕ) (bound : F.Desc → ℕ) (adversary : OracleDistinguisher)
    (n : ℕ) : Game := do
  let ds ← F.seededSetup setup (F.linearHashSeedLen outLen bound) n
  let B ← PMF.uniformOfFintype (BitString (inLen n) → ZMod (F.order ds.1))
  OracleComp.interpret
    (OracleComp.sumHandler ProbComp.unifOracle fun request =>
      PMF.pure (if request.2.length = inLen n then
        F.linearHashKDF (fun _ => outLen n) bound
          (ds, F.encode ds.1 (B (BitString.ofList (inLen n) request.2) • F.generator ds.1))
      else []))
    (adversary n (F.withSeed.encDesc ds))

private theorem run_eager_bitStringTable_eq_presample {m ℓ Q : ℕ}
    {prog : WordOracleComp Unit Bool} (hQ : prog.IsQueryBounded Q)
    (outLaw : PMF (BitString ℓ)) :
    ((PMF.pi (fun _ : BitString m => outLaw)).bind fun f =>
      OracleComp.interpret
        (OracleComp.sumHandler ProbComp.unifOracle fun request =>
          PMF.pure (if request.2.length = m then
            List.ofFn (f (BitString.ofList m request.2))
          else []))
        prog) =
    (PMF.pi (fun _ : Fin Q => outLaw)).bind fun tbl =>
      (((OracleComp.interpret
        (OracleComp.sumHandler (fun r => StateT.lift (ProbComp.unifOracle r))
          (OracleComp.withSampleList []
            (fun (fresh : List Bool) (request : Unit × List Bool)
                (cache : List (List Bool × List Bool)) =>
              if request.2.length = m then
                match cache.lookup request.2 with
                | some v => PMF.pure (v, cache)
                | none => PMF.pure (fresh, (request.2, fresh) :: cache)
              else PMF.pure ([], cache))))
        prog).run ([], List.ofFn fun i => List.ofFn (tbl i))).map fun res => res.1) := by
  let sample' : List Bool → PMF (List Bool) := fun _ => outLaw.map List.ofFn
  let step : List Bool → Unit × List Bool → StateT (List (List Bool × List Bool)) PMF (List Bool) :=
    fun fresh request cache =>
      if request.2.length = m then
        match cache.lookup request.2 with
        | some v => PMF.pure (v, cache)
        | none => PMF.pure (fresh, (request.2, fresh) :: cache)
      else PMF.pure ([], cache)
  have hmemo := interpret_wordFiltered_eq_memoize_map
    ⟨List.ofFn, List.ofFn_injective⟩ (List.ofFn : BitString ℓ → List Bool) (fun _ => outLaw)
    sample' (fun _ => rfl) (BitString.ofList m) (fun xs => xs)
    (fun hq => BitString.ofFn_ofList hq) (fun _ v => v) prog
  have hpre := congrArg (PMF.map Prod.fst)
    (hQ.run_interpret_presample (outLaw.map List.ofFn) [] step [])
  rw [hmemo]
  trans (((OracleComp.interpret
    (OracleComp.sumHandler (fun r => StateT.lift (ProbComp.unifOracle r))
      fun request cache => (outLaw.map List.ofFn).bind fun fresh => step fresh request cache)
    prog).run []).map Prod.fst)
  · refine congrArg (PMF.map Prod.fst)
      (congrArg (fun h => StateT.run (OracleComp.interpret h prog) []) ?_)
    funext q
    cases q with
    | inl r => rfl
    | inr request =>
      funext cache
      by_cases hq : request.2.length = m
      · cases h : cache.lookup request.2 <;>
          simp [OracleComp.sumHandler, hq, step, h, memoize_of_none, memoize_of_some, sample',
            PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_const]
      · simp [OracleComp.sumHandler, hq, step, PMF.bind_const]
  · rw [← hpre, PMF.map_bind, PMF.iid_map, PMF.iid_eq_pi, PMF.map_comp, PMF.bind_map]
    congr 1
    funext tbl
    simp only [Function.comp_def, PMF.map_comp, step]

private theorem advantage_naorReingoldHashedIdeal_at_le (F : PrimeOrderGroupFamily)
    (inLen outLen : ℕ → ℕ) (bound : F.Desc → ℕ) (adversary : OracleDistinguisher)
    (n Q : ℕ) (d : F.Desc)
    (hbound : ∀ x : F.Carrier d, (F.encode d x).length ≤ bound d)
    (hQ : ∀ seed : BitString (outLen n * (2 * bound d + 1)),
      (adversary n (F.withSeed.encDesc (d, List.ofFn seed))).IsQueryBounded Q) :
    Game.advantage
      ((Cslib.BitString.uniformList (F.linearHashSeedLen outLen bound n d)).bind fun seed =>
        (PMF.uniformOfFintype (BitString (inLen n) → ZMod (F.order d))).bind fun B =>
          OracleComp.interpret
            (OracleComp.sumHandler ProbComp.unifOracle fun request =>
              PMF.pure (if request.2.length = inLen n then
                F.linearHashKDF (fun _ => outLen n) bound
                  ((d, seed), F.encode d
                    (B (BitString.ofList (inLen n) request.2) • F.generator d))
              else []))
            (adversary n (F.withSeed.encDesc (d, seed))))
      ((Cslib.BitString.uniformList (F.linearHashSeedLen outLen bound n d)).bind fun seed =>
        (PMF.uniformOfFintype (BitString (inLen n) → BitString (outLen n))).bind fun f =>
          OracleComp.interpret
            (OracleComp.sumHandler ProbComp.unifOracle fun request =>
              PMF.pure (if request.2.length = inLen n then
                List.ofFn (f (BitString.ofList (inLen n) request.2))
              else []))
            (adversary n (F.withSeed.encDesc (d, seed)))) ≤
      (Q : ℝ≥0) * (NNReal.sqrt ((2 : ℝ≥0) ^ (outLen n) / (F.order d : ℝ≥0)) / 2) := by
  set m := inLen n
  set ℓ := outLen n
  let W := 2 * bound d + 1
  let source : PMF (BitString W) :=
    (PMF.uniformOfFintype (ZMod (F.order d))).map (F.paddedGeneratorMultiple bound d)
  let hashSeed : BitString (ℓ * W) → BitString W → BitString ℓ := fun seed =>
    Cslib.BitString.LinearHash.hash (Cslib.BitString.blocksEquiv (m := ℓ) (k := W) seed)
  let seedLaw := PMF.uniformOfFintype (BitString (ℓ * W))
  let tableWith (rowLaw : BitString (ℓ * W) → PMF (BitString ℓ)) :=
    seedLaw.bind fun seed => (PMF.pi (fun _ : Fin Q => rowLaw seed)).map (seed, ·)
  let detKernel : BitString (ℓ * W) × (Fin Q → BitString ℓ) → PMF Bool := fun pair =>
    (((OracleComp.interpret
      (OracleComp.sumHandler (fun r => StateT.lift (ProbComp.unifOracle r))
        (OracleComp.withSampleList []
          (fun (fresh : List Bool) (request : Unit × List Bool)
              (cache : List (List Bool × List Bool)) =>
            if request.2.length = m then
              match cache.lookup request.2 with
              | some v => PMF.pure (v, cache)
              | none => PMF.pure (fresh, (request.2, fresh) :: cache)
            else PMF.pure ([], cache))))
      (adversary n (F.withSeed.encDesc (d, List.ofFn pair.1)))).run
        ([], List.ofFn fun i => List.ofFn (pair.2 i))).map fun res => res.1)
  suffices h : Game.advantage ((tableWith fun seed => source.map (hashSeed seed)).bind detKernel)
      ((tableWith fun _ => PMF.uniformOfFintype (BitString ℓ)).bind detKernel) ≤
      (Q : ℝ≥0) * (NNReal.sqrt ((2 : ℝ≥0) ^ ℓ / (F.order d : ℝ≥0)) / 2) by
    refine Eq.trans_le (congrArg₂ Game.advantage ?_ ?_) h
    · simp only [linearHashSeedLen, Cslib.BitString.uniformList, PMF.bind_map, PMF.bind_bind,
        Function.comp_def, tableWith, seedLaw]
      congr 1; funext seed
      have hpi : PMF.pi (fun _ : BitString m => source.map (hashSeed seed)) =
          (PMF.uniformOfFintype (BitString m → ZMod (F.order d))).map
            (fun B x => hashSeed seed (F.paddedGeneratorMultiple bound d (B x))) := by
        dsimp only [source]
        simp_rw [PMF.map_comp]
        rw [PMF.pi_map, PMF.pi_uniformOfFintype]
        rfl
      rw [← run_eager_bitStringTable_eq_presample (hQ seed) (source.map (hashSeed seed)),
        hpi, PMF.bind_map]
      congr 1
      funext B
      dsimp only [Function.comp_apply]
      congr 1; funext q
      cases q with
      | inl _ => rfl
      | inr request =>
        dsimp only [OracleComp.sumHandler]
        by_cases hq : request.2.length = m
        · simp only [hq, ↓reduceIte, linearHashKDF, SeededDesc.seed,
            ← F.ofFn_paddedGeneratorMultiple hbound (B (BitString.ofList m request.2)),
            Cslib.BitString.LinearHash.wordHash_eq_ofFn, Cslib.BitString.ofList_ofFn,
            Cslib.BitString.blocksEquiv_apply, hashSeed]
        · simp [hq]
    · simp only [linearHashSeedLen, Cslib.BitString.uniformList, PMF.bind_map, PMF.bind_bind,
        Function.comp_def, tableWith, seedLaw]
      congr 1; funext seed
      rw [← PMF.pi_uniformOfFintype, run_eager_bitStringTable_eq_presample (hQ seed)]
  rw [Game.advantage_eq_nndist, ← NNReal.coe_le_coe, coe_nndist]
  have hlhl :
      dist (seedLaw.bind fun seed => (source.map (hashSeed seed)).map (seed, ·))
        (seedLaw.bind fun seed => (PMF.uniformOfFintype (BitString ℓ)).map (seed, ·)) ≤
      Real.sqrt (Fintype.card (BitString ℓ) * collisionProbability source) / 2 := by
    simpa only [seedLaw, seededHash, PMF.map_comp, Function.comp_def] using
      (Cslib.BitString.LinearHash.isTwoUniversal_flat W ℓ).leftover_hash source
  have hcoll : collisionProbability source = (F.order d : ℝ)⁻¹ := by
    simp only [source,
      collisionProbability_map_of_injective _ _ (F.paddedGeneratorMultiple_injective hbound),
      collisionProbability_uniform, ZMod.card]
  calc dist ((tableWith fun seed => source.map (hashSeed seed)).bind detKernel)
        ((tableWith fun _ => PMF.uniformOfFintype (BitString ℓ)).bind detKernel)
      ≤ dist (tableWith fun seed => source.map (hashSeed seed))
          (tableWith fun _ => PMF.uniformOfFintype (BitString ℓ)) := dist_bind_le _ _ _
    _ ≤ ∑ _i : Fin Q,
          dist (seedLaw.bind fun seed => (source.map (hashSeed seed)).map (seed, ·))
            (seedLaw.bind fun seed => (PMF.uniformOfFintype (BitString ℓ)).map (seed, ·)) :=
        PMF.dist_bind_pair_pi_le_sum _ _ _
    _ ≤ ∑ _i : Fin Q, (Real.sqrt (Fintype.card (BitString ℓ) * collisionProbability source) / 2) :=
        Finset.sum_le_sum fun _ _ => hlhl
    _ = (Q : ℝ) * (Real.sqrt ((2 : ℝ) ^ ℓ * (F.order d : ℝ)⁻¹) / 2) := by
        simp [BitString, hcoll]
    _ = ↑((Q : ℝ≥0) * (NNReal.sqrt ((2 : ℝ≥0) ^ ℓ / (F.order d : ℝ≥0)) / 2)) := by
        push_cast; rw [← div_eq_mul_inv]

/-- **Multi-query Leftover Hash Lemma bound for hashed Naor–Reingold** (paraphrase of
[NaorReingold2004], Section 4.1, Lemma 4.2; [BonehShoup2023], Section 8.10.4, Theorem 8.11, p. 334):
if `adversary` makes at most `Q` queries on `(setup n).support` and `qMin ≤ F.order d`, then
replacing hashed random group elements by a uniform random function `BitString (inLen n) →
BitString (outLen n)` changes the output distribution by at most
`Q * (√(2 ^ (outLen n) / qMin) / 2)`. -/
theorem advantage_naorReingoldHashedIdeal_le (setup : ℕ → PMF F.Desc) (inLen outLen : ℕ → ℕ)
    (bound : F.Desc → ℕ) (adversary : OracleDistinguisher) (n Q qMin : ℕ)
    (hq0 : 0 < qMin)
    (hbound : ∀ d ∈ (setup n).support, ∀ x : F.Carrier d, (F.encode d x).length ≤ bound d)
    (hq : ∀ d ∈ (setup n).support, qMin ≤ F.order d)
    (hQ : ∀ d ∈ (setup n).support,
      ∀ seed : BitString (outLen n * (2 * bound d + 1)),
        (adversary n (F.withSeed.encDesc (d, List.ofFn seed))).IsQueryBounded Q) :
    Game.advantage
      (F.naorReingoldHashedGroupIdealGame setup inLen outLen bound adversary n)
      (F.naorReingoldHashedIdealGame setup inLen outLen bound adversary n) ≤
      (Q : ℝ≥0) * (NNReal.sqrt ((2 : ℝ≥0) ^ (outLen n) / (qMin : ℝ≥0)) / 2) := by
  simp only [naorReingoldHashedGroupIdealGame, naorReingoldHashedIdealGame, seededSetup,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]
  peel_binds d
  refine (advantage_naorReingoldHashedIdeal_at_le F inLen outLen bound adversary n Q d
    (hbound d d_mem) (hQ d d_mem)).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  refine div_le_div_of_nonneg_right (NNReal.sqrt_le_sqrt.mpr ?_) (by norm_num)
  exact div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast hq0)
    (by exact_mod_cast hq d d_mem)

private noncomputable def hashedAdvGroup (F : PrimeOrderGroupFamily) (inLen outLen : ℕ → ℕ)
    (bound : F.Desc → ℕ) (adversary : OracleDistinguisher) (n : ℕ)
    (ds : F.withSeed.Desc) : WordOracleComp Unit Bool :=
  OracleComp.interpret
    (OracleComp.sumHandler
      (fun r => ProbOracleComp.sample (ProbComp.unifFin r))
      fun (request : Unit × List Bool) =>
        if request.2.length = inLen n then
          (fun raw => F.linearHashKDF (fun _ => outLen n) bound (ds, raw)) <$>
            (List.take (bound ds.1) <$>
              ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
                ((), request.2))
        else pure [])
    (adversary n (F.withSeed.encDesc ds))

private theorem isOraclePPTOn_hashedAdvGroup (F : PrimeOrderGroupFamily) {inLen outLen : ℕ → ℕ}
    {bound : F.Desc → ℕ}
    (hinLen : ComputableInPolyTime inLen encUnary encUnary)
    (houtLen : ComputableInPolyTime outLen encUnary encUnary)
    (hbound : ComputableInPolyTime bound F.encDesc encUnary)
    {adversary : OracleDistinguisher} (hadversary : IsOraclePPT encBool adversary) :
    IsOraclePPTOn (encPair encUnary F.withSeed.encDesc) encBool
      (fun p => hashedAdvGroup F inLen outLen bound adversary p.1 p.2) := by
  let ECaller := encPair encUnary F.withSeed.encDesc
  let EHandler := encPair ECaller (encPair (encFinEnum Unit) encBits)
  have htake : IsOraclePPTOn EHandler encBits
      (fun pair : (ℕ × F.withSeed.Desc) × (Unit × List Bool) =>
        List.take (bound pair.1.2.1) <$>
          ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool) ((), pair.2.2)) :=
    IsOraclePPTOn.query_take ()
      (request := fun pair : (ℕ × F.withSeed.Desc) × (Unit × List Bool) => pair.2.2)
      (limit := fun pair => bound pair.1.2.1) (by dsimp only [EHandler]; fun_prop)
      (hbound.comp (by dsimp only [EHandler, ECaller, withSeed]; fun_prop))
  have hvalid : IsOraclePPTOn EHandler encBits
      (fun pair : (ℕ × F.withSeed.Desc) × (Unit × List Bool) =>
        (fun raw => F.linearHashKDF (fun _ => outLen pair.1.1) bound (pair.1.2, raw)) <$>
          (List.take (bound pair.1.2.1) <$>
            ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
              ((), pair.2.2))) :=
    htake.map_with (by
      unfold linearHashKDF
      dsimp only [SeededDesc.desc, SeededDesc.seed, EHandler, ECaller, withSeed]
      fun_prop)
  have hhandler : IsOraclePPTOn EHandler encBits
      (fun pair : (ℕ × F.withSeed.Desc) × (Unit × List Bool) =>
        if pair.2.2.length = inLen pair.1.1 then
          (fun raw => F.linearHashKDF (fun _ => outLen pair.1.1) bound (pair.1.2, raw)) <$>
            (List.take (bound pair.1.2.1) <$>
              ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
                ((), pair.2.2))
        else pure []) :=
    IsOraclePPTOn.ite (by dsimp only [EHandler, ECaller]; fun_prop) hvalid
      (by simpa only [ProbOracleComp.sample_pure] using
        (ComputableInPolyTime.const ([] : List Bool)).isPPTOn.isOraclePPTOn (Operation := Unit))
  unfold hashedAdvGroup
  refine hadversary.on.interpret_preprocess_open'
    (operationEncoding := encFinEnum Unit)
    (prepare := fun p : ℕ × F.withSeed.Desc => (p.1, F.withSeed.encDesc p.2))
    (resources := fun p _ => outLen p.1)
    (by fun_prop) hhandler (by dsimp only [ECaller]; fun_prop) ?_
  intro a request reply hreply
  by_cases hq : request.2.length = inLen a.1 <;> simp only [hq, ↓reduceIte] at hreply
  · obtain ⟨raw, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hreply
    simp
  · simp [OracleComp.eq_of_mem_supportWith_pure hreply]

private theorem naorReingoldWordRun_hashedAdvGroup (F : PrimeOrderGroupFamily)
    (inLen outLen : ℕ → ℕ) (bound : F.Desc → ℕ) (adversary : OracleDistinguisher)
    (n : ℕ) (ds : F.withSeed.Desc)
    (hbound : ∀ x : F.Carrier ds.1, (F.encode ds.1 x).length ≤ bound ds.1)
    (fn : BitString (inLen n) → F.Carrier ds.1) :
    naorReingoldWordRun F.withSeed ds (hashedAdvGroup F inLen outLen bound adversary n ds) fn =
      OracleComp.interpret
        (OracleComp.sumHandler ProbComp.unifOracle fun request =>
          PMF.pure (if request.2.length = inLen n then
            F.linearHashKDF (fun _ => outLen n) bound
              (ds, F.encode ds.1 (fn (BitString.ofList (inLen n) request.2)))
          else []))
        (adversary n (F.withSeed.encDesc ds)) := by
  dsimp only [naorReingoldWordRun, hashedAdvGroup]
  rw [OracleComp.interpret_interpret]
  congr 1; funext q
  cases q with
  | inl r =>
    simp [OracleComp.sumHandler, ProbOracleComp.sample, ProbComp.unifFin]
  | inr request =>
    dsimp only [OracleComp.sumHandler, Function.comp_apply]
    by_cases hq : request.2.length = inLen n
    · simp only [hq, ↓reduceIte, OracleComp.interpret_map, ProbOracleComp.interpret_query,
        PMF.monad_map_eq_map, PMF.pure_map, naorReingoldWordOracle,
        List.take_of_length_le (hbound _)]
    · simp [hq, PMF.monad_pure_eq_pure]

private theorem advantage_naorReingoldHashedReal_groupIdeal_eq (F : PrimeOrderGroupFamily)
    (setup : ℕ → PMF F.Desc) (inLen outLen : ℕ → ℕ) (bound : F.Desc → ℕ)
    (adversary : OracleDistinguisher) (n : ℕ)
    (hbound : ∀ d ∈ (setup n).support, ∀ x : F.Carrier d, (F.encode d x).length ≤ bound d) :
    Game.advantage
      (F.naorReingoldHashedRealGame setup inLen outLen bound adversary n)
      (naorReingoldHashedGroupIdealGame F setup inLen outLen bound adversary n) =
    Game.advantage
      (naorReingoldDescRealGame F.withSeed
        (F.seededSetup setup (F.linearHashSeedLen outLen bound)) inLen
        (hashedAdvGroup F inLen outLen bound adversary) n)
      (naorReingoldDescIdealGame F.withSeed
        (F.seededSetup setup (F.linearHashSeedLen outLen bound)) inLen
        (hashedAdvGroup F inLen outLen bound adversary) n) := by
  have hfn (ds : F.withSeed.Desc)
      (hds : ds ∈ (F.seededSetup setup (F.linearHashSeedLen outLen bound) n).support)
      (fn : BitString (inLen n) → F.Carrier ds.1) :
      OracleComp.interpret
        (OracleComp.sumHandler ProbComp.unifOracle fun request =>
          PMF.pure (if request.2.length = inLen n then
            F.linearHashKDF (fun _ => outLen n) bound
              (ds, F.encode ds.1 (fn (BitString.ofList (inLen n) request.2)))
          else []))
        (adversary n (F.withSeed.encDesc ds)) =
      naorReingoldWordRun F.withSeed ds
        (hashedAdvGroup F inLen outLen bound adversary n ds) fn := by
    simp only [seededSetup, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hds
    obtain ⟨d, hd, _, _, rfl⟩ := hds
    exact (naorReingoldWordRun_hashedAdvGroup F inLen outLen bound adversary n (d, _)
      (hbound d hd) fn).symm
  unfold naorReingoldDescRealGame naorReingoldDescIdealGame
  simp only [naorReingoldHashedRealGame, naorReingoldHashedGroupIdealGame, PMF.monad_bind_eq_bind]
  congr 1
  · refine bind_congr_on_support _ _ _ fun ds hds => ?_
    congr 1; funext α₀; congr 1; funext α
    exact hfn ds hds (F.naorReingoldEval ds.1 α₀ α)
  · refine bind_congr_on_support _ _ _ fun ds hds => ?_
    congr 1; funext B
    exact hfn ds hds (fun x => B x • F.generator ds.1)

private theorem exists_queryBound_hashedAdvGroup {F : PrimeOrderGroupFamily}
    {setup : ℕ → PMF F.Desc} {outLen : ℕ → ℕ} {bound : F.Desc → ℕ} {descBound : ℕ → ℕ}
    (houtLen : ComputableInPolyTime outLen encUnary encUnary)
    (hbound_poly : ComputableInPolyTime bound F.encDesc encUnary)
    (hdesc_poly : PolynomiallyBounded descBound)
    (hdesc : ∀ n, ∀ d ∈ (setup n).support, (F.encDesc d).length ≤ descBound n)
    {adversary : OracleDistinguisher} (hadversary : IsOraclePPT encBool adversary) :
    ∃ Q : ℕ → ℕ, PolynomiallyBounded Q ∧
      ∀ n, ∀ d ∈ (setup n).support, ∀ seed : BitString (outLen n * (2 * bound d + 1)),
        (adversary n (F.withSeed.encDesc (d, List.ofFn seed))).IsQueryBounded (Q n) := by
  obtain ⟨cA, eA, hQb⟩ := hadversary.query_bounds
  obtain ⟨cB, eB, hBb⟩ := hbound_poly.polyBounded_length.exists_le
  have hout_poly : PolynomiallyBounded outLen := houtLen.polynomiallyBounded
  refine ⟨fun n =>
    cA * (n + (2 * descBound n + 2 + outLen n * (2 * (cB * (descBound n + 1) ^ eB) + 1)) + 2) ^ eA,
    by fun_prop, fun n d hd seed => ?_⟩
  have hbd : bound d ≤ cB * (descBound n + 1) ^ eB := by
    have h1 := hBb d
    simp only [encUnary_apply, List.length_replicate] at h1
    exact h1.trans (Nat.mul_le_mul_left cB (Nat.pow_le_pow_left
      (Nat.add_le_add_right (hdesc n d hd) 1) eB))
  have hlen :
      (F.withSeed.encDesc (d, List.ofFn seed)).length ≤
        2 * descBound n + 2 + outLen n * (2 * (cB * (descBound n + 1) ^ eB) + 1) := by
    simp only [length_encPair, encBits_apply, List.length_ofFn]
    have hd_len := hdesc n d hd
    have hmul := Nat.mul_le_mul_left (outLen n) (show 2 * bound d + 1 ≤
      2 * (cB * (descBound n + 1) ^ eB) + 1 by lia)
    lia
  exact (hQb n (F.withSeed.encDesc (d, List.ofFn seed))).1.mono
    (Nat.mul_le_mul_left cA (Nat.pow_le_pow_left (by lia) eA))

private theorem negligible_naorReingoldHashedGame_of_ideal_le {F : PrimeOrderGroupFamily}
    {setup : ℕ → PMF F.Desc} {inLen outLen : ℕ → ℕ} {bound : F.Desc → ℕ}
    (hDDH : F.DDH setup)
    (hinLen : ComputableInPolyTime inLen encUnary encUnary)
    (houtLen : ComputableInPolyTime outLen encUnary encUnary)
    (hbound_poly : ComputableInPolyTime bound F.encDesc encUnary)
    (hbound : ∀ n, ∀ d ∈ (setup n).support, ∀ x : F.Carrier d, (F.encode d x).length ≤ bound d)
    {adversary : OracleDistinguisher} (hadversary : IsOraclePPT encBool adversary)
    {gBound : ℕ → ℝ≥0} (hg_neg : Negligible gBound)
    (hg_le : ∀ n,
      Game.advantage
        (naorReingoldHashedGroupIdealGame F setup inLen outLen bound adversary n)
        (F.naorReingoldHashedIdealGame setup inLen outLen bound adversary n) ≤ gBound n) :
    Negligible fun n =>
      Game.advantage
        (F.naorReingoldHashedRealGame setup inLen outLen bound adversary n)
        (F.naorReingoldHashedIdealGame setup inLen outLen bound adversary n) := by
  have hDDH_seed : F.withSeed.DDH (F.seededSetup setup (F.linearHashSeedLen outLen bound)) :=
    hDDH.withSeed (F.computableInPolyTime_linearHashSeedLen houtLen hbound_poly)
  have hstep1_neg := hDDH_seed.negligible_naorReingoldDescGame hinLen
    (isOraclePPTOn_hashedAdvGroup F hinLen houtLen hbound_poly hadversary)
  refine negligible_of_le (hstep1_neg.add hg_neg) fun n => ?_
  game_trans [naorReingoldHashedGroupIdealGame F setup inLen outLen bound adversary n]
    using [le_rfl, hg_le n]
  rw [advantage_naorReingoldHashedReal_groupIdeal_eq F setup inLen outLen bound adversary n
    (hbound n)]
  exact le_rfl

/-- Ideal-key-sampling step, not the cited result: under `F.DDH setup`, when group descriptions on
`(setup n).support` have polynomially bounded bit-length, `bound` bounds encoded group elements,
and `2 ^ (outLen n) / qMin n` is negligible, no `IsOraclePPT` adversary can distinguish
`naorReingoldHashedRealGame`, whose exponents are drawn exactly uniformly from `ZMod (F.order d)`,
from `naorReingoldHashedIdealGame`. The theorem for exponents drawn with the fair-coin sampler
`sampleNaorReingoldExp` is `DDH.negligible_naorReingoldHashedProbGame`, which uses this one. The
construction is after [NaorReingold2004], not checked. -/
theorem DDH.negligible_naorReingoldHashedGame_ideal {F : PrimeOrderGroupFamily}
    {setup : ℕ → PMF F.Desc} {inLen outLen : ℕ → ℕ} {bound : F.Desc → ℕ}
    {descBound qMin : ℕ → ℕ}
    (hDDH : F.DDH setup)
    (hinLen : ComputableInPolyTime inLen encUnary encUnary)
    (houtLen : ComputableInPolyTime outLen encUnary encUnary)
    (hbound_poly : ComputableInPolyTime bound F.encDesc encUnary)
    (hdesc_poly : PolynomiallyBounded descBound)
    (hdesc : ∀ n, ∀ d ∈ (setup n).support, (F.encDesc d).length ≤ descBound n)
    (hbound : ∀ n, ∀ d ∈ (setup n).support, ∀ x : F.Carrier d, (F.encode d x).length ≤ bound d)
    (hq0 : ∀ n, 0 < qMin n)
    (hq : ∀ n, ∀ d ∈ (setup n).support, qMin n ≤ F.order d)
    (hneg : Negligible fun n => (2 : ℝ≥0) ^ (outLen n) / (qMin n : ℝ≥0))
    {adversary : OracleDistinguisher} (hadversary : IsOraclePPT encBool adversary) :
    Negligible fun n =>
      Game.advantage
        (F.naorReingoldHashedRealGame setup inLen outLen bound adversary n)
        (F.naorReingoldHashedIdealGame setup inLen outLen bound adversary n) := by
  obtain ⟨Q, hQ_poly, hQ_supp⟩ :=
    exists_queryBound_hashedAdvGroup houtLen hbound_poly hdesc_poly hdesc hadversary
  have hstep2_neg : Negligible fun n =>
      (Q n : ℝ≥0) * (NNReal.sqrt ((2 : ℝ≥0) ^ (outLen n) / (qMin n : ℝ≥0)) / 2) := by
    negligible
  exact negligible_naorReingoldHashedGame_of_ideal_le hDDH hinLen houtLen hbound_poly hbound
    hadversary hstep2_neg fun n =>
      F.advantage_naorReingoldHashedIdeal_le setup inLen outLen bound adversary n (Q n)
        (qMin n) (hq0 n) (hbound n) (hq n) (hQ_supp n)

/-- **Asymptotic DDH security of the executable universal-hash Naor–Reingold bit-string PRF
(`naorReingoldHashedProbRealGame`)** (paraphrase of [NaorReingold2004], Section 4.1,
Construction 4.2, Theorem 4.3, and Remark 4.2). -/
theorem DDH.negligible_naorReingoldHashedProbGame {F : PrimeOrderGroupFamily}
    {setup : ℕ → PMF F.Desc} {inLen outLen : ℕ → ℕ} {bound : F.Desc → ℕ}
    {descBound qMin : ℕ → ℕ}
    (hDDH : F.DDH setup)
    (hinLen : ComputableInPolyTime inLen encUnary encUnary)
    (houtLen : ComputableInPolyTime outLen encUnary encUnary)
    (hbound_poly : ComputableInPolyTime bound F.encDesc encUnary)
    (hdesc_poly : PolynomiallyBounded descBound)
    (hdesc : ∀ n, ∀ d ∈ (setup n).support, (F.encDesc d).length ≤ descBound n)
    (hbound : ∀ n, ∀ d ∈ (setup n).support, ∀ x : F.Carrier d, (F.encode d x).length ≤ bound d)
    (hq0 : ∀ n, 0 < qMin n)
    (hq : ∀ n, ∀ d ∈ (setup n).support, qMin n ≤ F.order d)
    (hneg : Negligible fun n => (2 : ℝ≥0) ^ (outLen n) / (qMin n : ℝ≥0))
    {adversary : OracleDistinguisher} (hadversary : IsOraclePPT encBool adversary) :
    Negligible fun n =>
      Game.advantage
        (F.naorReingoldHashedProbRealGame setup inLen outLen bound adversary n)
        (F.naorReingoldHashedIdealGame setup inLen outLen bound adversary n) := by
  have hprob_le (n : ℕ) :
      Game.advantage
        (F.naorReingoldHashedProbRealGame setup inLen outLen bound adversary n)
        (F.naorReingoldHashedRealGame setup inLen outLen bound adversary n) ≤
        ((inLen n + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n := by
    simp only [naorReingoldHashedProbRealGame, naorReingoldHashedRealGame,
      naorReingoldHashedWordEval, PMF.monad_bind_eq_bind]
    peel_binds ds
    exact advantage_probNaorReingold_le F n (inLen n) ds.1 (adversary n (F.withSeed.encDesc ds))
      (fun w => F.linearHashKDF (fun _ => outLen n) bound (ds, w))
  refine negligible_of_le
    ((negligible_add_one_div_two_pow hinLen).add
      (hDDH.negligible_naorReingoldHashedGame_ideal hinLen houtLen hbound_poly hdesc_poly hdesc
        hbound hq0 hq hneg hadversary)) fun n => ?_
  game_trans [F.naorReingoldHashedRealGame setup inLen outLen bound adversary n]
    using [hprob_le n, le_rfl]

/-- Ideal-key-sampling step with constant output length, not the cited result: for any constant
output length `c : ℕ` (including `c = 1`), under `F.DDH setup`, the only hardness assumption,
together with the stated polynomial-time length functions and setup-support encoding bounds, no
`IsOraclePPT` adversary can distinguish `naorReingoldHashedRealGame`, whose exponents are drawn
exactly uniformly from `ZMod (F.order d)`, from `naorReingoldHashedIdealGame`. `F.DDH setup`
supplies the inverse-order decay that the Leftover Hash Lemma needs
(`DDH.negligible_expected_inv_order`), so no `qMin` hypothesis is needed. The library has no version
of this theorem for fair-coin exponents (#5293); `DDH.exists_pseudorandomGenerator` in
`CslibFrontier/Crypto/Computational/NaorReingold/PRF.lean` uses this one. The construction is after
[NaorReingold2004], not checked. -/
theorem DDH.negligible_naorReingoldHashedGame_ideal_const {F : PrimeOrderGroupFamily}
    {setup : ℕ → PMF F.Desc} {inLen : ℕ → ℕ} {bound : F.Desc → ℕ} {descBound : ℕ → ℕ}
    (c : ℕ) (hDDH : F.DDH setup)
    (hinLen : ComputableInPolyTime inLen encUnary encUnary)
    (hbound_poly : ComputableInPolyTime bound F.encDesc encUnary)
    (hdesc_poly : PolynomiallyBounded descBound)
    (hdesc : ∀ n, ∀ d ∈ (setup n).support, (F.encDesc d).length ≤ descBound n)
    (hbound : ∀ n, ∀ d ∈ (setup n).support, ∀ x : F.Carrier d, (F.encode d x).length ≤ bound d)
    {adversary : OracleDistinguisher} (hadversary : IsOraclePPT encBool adversary) :
    Negligible fun n =>
      Game.advantage
        (F.naorReingoldHashedRealGame setup inLen (fun _ => c) bound adversary n)
        (F.naorReingoldHashedIdealGame setup inLen (fun _ => c) bound adversary n) := by
  have houtLen : ComputableInPolyTime (fun _ : ℕ => c) encUnary encUnary := by fun_prop
  obtain ⟨Q, hQ_poly, hQ_supp⟩ :=
    exists_queryBound_hashedAdvGroup houtLen hbound_poly hdesc_poly hdesc hadversary
  let ε : ℕ → ℝ≥0 := fun n => (∑' d, setup n d * (F.order d : ℝ≥0∞)⁻¹).toNNReal
  let K : ℝ≥0 := NNReal.sqrt ((2 : ℝ≥0) ^ c) / 2
  have hbound_neg : Negligible fun n => (Q n : ℝ≥0) * K * NNReal.sqrt (ε n) := by
    simpa only [mul_assoc] using
      (hDDH.negligible_expected_inv_order.sqrt.const_mul K).polynomiallyBounded_mul hQ_poly
  refine negligible_naorReingoldHashedGame_of_ideal_le hDDH hinLen houtLen hbound_poly hbound
    hadversary hbound_neg fun n => ?_
  simp only [naorReingoldHashedGroupIdealGame, naorReingoldHashedIdealGame, seededSetup,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]
  let g : F.Desc → ℝ≥0 := fun d => NNReal.sqrt ((F.order d : ℝ≥0)⁻¹)
  have hg_le_one (d : F.Desc) : g d ≤ 1 :=
    NNReal.sqrt_le_one.mpr (inv_le_one_of_one_le₀ (by exact_mod_cast (F.prime_order d).pos))
  have hclose := CloseTo.bind_right_tsum (setup n)
    (err := fun d => (((Q n : ℝ≥0) * K * g d : ℝ≥0) : ℝ≥0∞)) fun d hd => by
      refine Game.closeTo_iff_advantage_le.mpr
        ((advantage_naorReingoldHashedIdeal_at_le F inLen (fun _ => c) bound adversary n (Q n) d
          (hbound n d hd) (hQ_supp n d hd)).trans_eq ?_)
      dsimp only [K, g]
      rw [div_eq_mul_inv ((2 : ℝ≥0) ^ c), NNReal.sqrt_mul, mul_div_right_comm, ← mul_assoc]
  have hadv : (Game.advantage _ _ : ℝ≥0∞) ≤
      (((Q n : ℝ≥0) : ℝ≥0∞) * K) * ∑' d, setup n d * (g d : ℝ≥0∞) :=
    (Game.closeTo_iff_coe_advantage_le.mp hclose).trans_eq (by
      rw [← ENNReal.tsum_mul_left]
      exact tsum_congr fun d => by simp only [ENNReal.coe_mul]; ring)
  have hE_top : (∑' d, setup n d * (g d : ℝ≥0∞)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top <|
      (tsum_le_tsum fun x => mul_le_mul_of_nonneg_left
        (ENNReal.coe_le_one_iff.mpr (hg_le_one x)) zero_le).trans_eq (by simp [(setup n).tsum_coe])
  have hjensen : (∑' d, setup n d * (g d : ℝ≥0∞)).toReal ≤ Real.sqrt (ε n : ℝ) := by
    have hE_eq :
        (∑' d, setup n d * (g d : ℝ≥0∞)).toReal = ∑' d, (setup n d).toReal * (g d : ℝ) := by
      rw [ENNReal.tsum_toReal_eq fun d =>
        ENNReal.mul_ne_top ((setup n).apply_ne_top d) ENNReal.coe_ne_top]
      exact tsum_congr fun d => ENNReal.toReal_mul
    have hε_eq : (ε n : ℝ) = ∑' d, (setup n d).toReal * (g d : ℝ) ^ 2 := by
      change (∑' d, setup n d * (F.order d : ℝ≥0∞)⁻¹).toReal = _
      rw [ENNReal.tsum_toReal_eq fun d => ENNReal.mul_ne_top ((setup n).apply_ne_top d)
        (ENNReal.inv_ne_top.mpr (by exact_mod_cast (F.prime_order d).ne_zero))]
      refine tsum_congr fun d => ?_
      rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
      dsimp only [g]
      rw [← NNReal.coe_pow, NNReal.sq_sqrt, NNReal.coe_inv, NNReal.coe_natCast]
    rw [hE_eq, hε_eq]
    exact Real.le_sqrt_of_sq_le (PMF.sq_tsum_le_tsum_sq (setup n) (fun _ => NNReal.coe_nonneg _)
      fun d => by exact_mod_cast hg_le_one d)
  rw [← NNReal.coe_le_coe]
  calc (Game.advantage _ _ : ℝ)
      ≤ ((((Q n : ℝ≥0) : ℝ≥0∞) * K) * ∑' d, setup n d * (g d : ℝ≥0∞)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top (by finiteness) hE_top) hadv
    _ = ((Q n : ℝ) * (K : ℝ)) * (∑' d, setup n d * (g d : ℝ≥0∞)).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul]; rfl
    _ ≤ ((Q n : ℝ) * (K : ℝ)) * Real.sqrt (ε n : ℝ) := by gcongr
    _ = (((Q n : ℝ≥0) * K * NNReal.sqrt (ε n) : ℝ≥0) : ℝ) := by push_cast; rfl

end Cslib.Crypto.PrimeOrderGroupFamily
