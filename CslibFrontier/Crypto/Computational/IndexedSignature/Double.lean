/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
public import CslibFrontier.Crypto.Computational.IndexedSignature
public import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Probabilistic.Oracle.SubstitutionGrowth
import CslibFrontier.Languages.Probabilistic.Oracle.Norm
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.PPT
import CslibFrontier.Tactic.EncLen
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Tactic.SuppCases

/-!
# Doubling the capacity of an indexed signature scheme

Two independent instances of an indexed signature scheme `S` of capacity at least `1` combine into
an indexed signature scheme `S.double hcap` of constant capacity `2`: key generation samples two
independent key pairs `(k₀, k₁)` from `S.keyGen n`, index `0` signs and verifies at index `0` under
`k₀`, index `1` signs and verifies at index `0` under `k₁`, and verification rejects every index
`u ≥ 2`.

This is the `q = 2` case of the `q`-key construction in [BonehShoup2023], Section 14.6.1,
construction `(14.4)` (generalized from one-time signatures to any indexed scheme with
`1 ≤ S.capacity n`, with randomized signing and arbitrary-length messages as in
`IndexedSignatureScheme`). By the plug-and-pray reduction ([BonehShoup2023], Section 14.6.1,
referring to Exercise 13.2), `doubleForger` plants its challenge verification key at a uniform slot
`b ∈ {false, true}`, generates the other key pair locally, forwards queries at slot `b.toNat` to its
indexed signing oracle at index `0`, and answers queries at the unplanted slot locally. Every valid
forgery against `S.double hcap` lands on `u = 0` or `u = 1` and hits the planted slot with
probability `1 / 2`, losing at most a factor of `2` (`succProbability_indexedEufCmaGame_double_le`,
`IndexedSignatureScheme.IndexedEUFCMA.double`).

In particular, doubling upgrades any capacity-`1` indexed signature scheme to the `2 ≤ capacity n`
hypothesis of `IndexedSignatureScheme.IndexedEUFCMA.exists_eufCMA_of_oneWay`.

Both results are steps toward construction `(14.4)` (printed p. 597) and Exercise 13.2 (printed
p. 575), not those results: the source takes any number `q` of keys, with loss `q`, and only
`q = 2` is formalized here (#5293).

## Main definitions

* `Cslib.Crypto.IndexedSignatureScheme.doubleKeyDecoder`: pair decoder for bundled public and secret
  keys.
* `Cslib.Crypto.IndexedSignatureScheme.doubleKeyGen`,
  `Cslib.Crypto.IndexedSignatureScheme.doubleSign`,
  `Cslib.Crypto.IndexedSignatureScheme.doubleVerify`,
  `Cslib.Crypto.IndexedSignatureScheme.double`: capacity-`2` doubling combinator.
* `Cslib.Crypto.IndexedSignatureScheme.doublePlantPk`,
  `Cslib.Crypto.IndexedSignatureScheme.doubleHandler`,
  `Cslib.Crypto.IndexedSignatureScheme.doubleForgerAt`,
  `Cslib.Crypto.IndexedSignatureScheme.doubleForger`: plug-and-pray reduction to `S`.

## Main results

* `Cslib.Crypto.IndexedSignatureScheme.succProbability_indexedEufCmaGame_double_le`: forging
  probability against `S.double hcap` is at most `2` times that of `doubleForger` against `S`
  (a step).
* `Cslib.Crypto.IndexedSignatureScheme.isOraclePPT_doubleForger`: `doubleForger` is uniformly strict
  oracle PPT.
* `Cslib.Crypto.IndexedSignatureScheme.IndexedEUFCMA.double`: `IndexedEUFCMA` is preserved by
  `S.double hcap` (a step).

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 14.6.1 (construction `(14.4)` at `q = 2`) and Exercise 13.2.
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

namespace IndexedSignatureScheme

/-! ### The capacity-`2` doubled scheme -/

/-- Total decoder for paired public or secret keys `encPair encBits encBits (k₀, k₁)`. -/
@[expose]
def doubleKeyDecoder : Decoder (encPair encBits encBits) :=
  Decoder.bits.pair Decoder.bits

/-- Sample two independent key pairs `(k₀, k₁)` from `S.keyGen n` and bundle their public and secret
halves with `encPair encBits encBits`. -/
@[expose]
def doubleKeyGen (S : IndexedSignatureScheme) (n : ℕ) : ProbComp (List Bool × List Bool) := do
  let k₀ ← S.keyGen n
  let k₁ ← S.keyGen n
  return (encPair encBits encBits (k₀.1, k₁.1), encPair encBits encBits (k₀.2, k₁.2))

/-- Sign `msg` at index `u ∈ {0, 1}` using index `0` of the `u`-th secret key, returning `[]` when
`u ≥ 2`. -/
@[expose]
def doubleSign (S : IndexedSignatureScheme) (sk : List Bool) (u : ℕ) (msg : List Bool) :
    ProbComp (List Bool) :=
  let sks := doubleKeyDecoder.decode sk
  if u = 0 then
    S.sign sks.1 0 msg
  else if u = 1 then
    S.sign sks.2 0 msg
  else
    pure []

/-- Verify `(u, msg, sig)` under bundled public keys `(pk₀, pk₁)`: accept only at `u = 0` under
`pk₀` or at `u = 1` under `pk₁`, always at inner index `0`. -/
@[expose]
def doubleVerify (S : IndexedSignatureScheme) (pk : List Bool) (u : ℕ) (msg sig : List Bool) :
    Bool :=
  let pks := doubleKeyDecoder.decode pk
  (u == 0 && S.verify pks.1 0 msg sig) || (u == 1 && S.verify pks.2 0 msg sig)

/-- **Capacity-`2` doubling combinator** ([BonehShoup2023], Section 14.6.1, construction `(14.4)` at
`q = 2`): combine two independent instances of `S` (with `∀ n, 1 ≤ S.capacity n`) into an
`IndexedSignatureScheme` of capacity `2`. -/
@[expose]
def double (S : IndexedSignatureScheme) (hcap : ∀ n, 1 ≤ S.capacity n) :
    IndexedSignatureScheme where
  capacity := fun _ => 2
  keyGen := S.doubleKeyGen
  sign := S.doubleSign
  verify := S.doubleVerify
  capacity_polyTime := ComputableInPolyTime.const 2
  keyGen_ppt := by ppt [doubleKeyGen]
  sign_ppt := by
    have := doubleKeyDecoder.computableInPolyTime
    ppt [doubleSign]
  verify_polyTime := by
    have := doubleKeyDecoder.computableInPolyTime
    polytime [doubleVerify]
  verify_sign := by
    intro n keys hkeys u hu msg sig hsig
    simp only [doubleKeyGen, ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
      PMF.mem_support_pure_iff] at hkeys
    obtain ⟨k₀, hk₀, k₁, hk₁, rfl⟩ := hkeys
    have h0 : 0 < S.capacity n := hcap n
    by_cases hu0 : u = 0
    · subst hu0
      simp only [doubleSign, ↓reduceIte, doubleKeyDecoder.decode_enc] at hsig
      simp only [doubleVerify, doubleKeyDecoder.decode_enc, beq_self_eq_true, Bool.true_and,
        S.verify_sign n k₀ hk₀ 0 h0 msg sig hsig, Bool.true_or]
    · have hu1 : u = 1 := by omega
      subst hu1
      simp only [doubleSign, Nat.one_ne_zero, ↓reduceIte, doubleKeyDecoder.decode_enc] at hsig
      simp only [doubleVerify, doubleKeyDecoder.decode_enc, beq_self_eq_true, Bool.true_and,
        S.verify_sign n k₁ hk₁ 0 h0 msg sig hsig, Bool.or_true]

@[simp]
theorem capacity_double (S : IndexedSignatureScheme) (hcap : ∀ n, 1 ≤ S.capacity n) (n : ℕ) :
    (S.double hcap).capacity n = 2 := rfl

/-! ### Plug-and-pray reduction -/

/-- Bundle a challenge verification key `vk` at slot `b.toNat` (`false ↦ 0`, `true ↦ 1`) with a
locally generated public key `otherPk` at the complementary slot. -/
@[expose]
def doublePlantPk (b : Bool) (vk otherPk : List Bool) : List Bool :=
  if b then encPair encBits encBits (otherPk, vk)
  else encPair encBits encBits (vk, otherPk)

/-- Stateful signing handler for `doubleForger`: maintains the outer query log `signed` of pairs
`(u, msg)` with `u < 2`. When a fresh index `u < 2` is queried:
* if `u = b.toNat`, forward `(0, msg)` to the external `S`-signing oracle and truncate the reply to
  `bound n msg.length` bits;
* otherwise, sign `(0, msg)` locally under `otherSk`. -/
def doubleHandler (S : IndexedSignatureScheme) (b : Bool) (otherSk : List Bool)
    (bound : ℕ → ℕ → ℕ) (n : ℕ) (request : Unit × List Bool)
    (signed : List (ℕ × List Bool)) :
    WordOracleComp Unit (List Bool × List (ℕ × List Bool)) :=
  let r := requestDecoder.decode request.2
  if r.1 < 2 ∧ r.1 ∉ signed.map Prod.fst then
    if r.1 = b.toNat then
      (fun sig => (sig, r :: signed)) <$>
        (List.take (bound n r.2.length) <$>
          ProbOracleComp.query ((), encPair encUnary encBits (0, r.2)))
    else
      (fun sig => (sig, r :: signed)) <$>
        ProbOracleComp.sample (S.sign otherSk 0 r.2)
  else
    pure ([], signed)

/-- Fixed-slot reduction from `(S.double hcap)` to `S` at slot `b : Bool`. -/
def doubleForgerAt (S : IndexedSignatureScheme) (bound : ℕ → ℕ → ℕ) (adversary : IndexedForger)
    (b : Bool) (n : ℕ) (vk : List Bool) : WordOracleComp Unit (ℕ × List Bool × List Bool) := do
  let other ← ProbOracleComp.sample (S.keyGen n)
  let out ← (OracleComp.interpret
    (OracleComp.sumHandler
      (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
      (S.doubleHandler b other.2 bound n))
    (adversary n (doublePlantPk b vk other.1))).run []
  let (_, msg, sig) := out.1
  return (0, msg, sig)

/-- Plug-and-pray reduction ([BonehShoup2023], Section 14.6.1, Exercise 13.2): sample a fair slot
`b ← ProbComp.uniform Bool` and run `doubleForgerAt`. -/
noncomputable def doubleForger (S : IndexedSignatureScheme) (bound : ℕ → ℕ → ℕ)
    (adversary : IndexedForger) : IndexedForger := fun n vk => do
  let b ← ProbOracleComp.sample (ProbComp.uniform Bool)
  S.doubleForgerAt bound adversary b n vk

/-! ### Exact simulation at each slot -/

/-- Joint handler pairing `doubleHandler`'s outer log with `S.indexedSigningOracle`'s inner log. -/
private noncomputable def doubleJointOracle (S : IndexedSignatureScheme) (b : Bool)
    (challengeSk otherSk : List Bool) (bound : ℕ → ℕ → ℕ) (n : ℕ) (q : Unit × List Bool)
    (state : List (ℕ × List Bool) × List (ℕ × List Bool)) :
    PMF (List Bool × List (ℕ × List Bool) × List (ℕ × List Bool)) :=
  (ProbOracleComp.runWith (fun q' s' => ProbComp.eval (S.indexedSigningOracle n challengeSk q' s'))
      (S.doubleHandler b otherSk bound n q state.1) state.2).map
      (fun r => (r.1.1, r.1.2, r.2))

/-- Invariant relating the outer log `signed` and the inner `S`-oracle log `ext`: `0` has been used
in `ext` iff `b.toNat` has been used in `signed`, and any `(0, m)` in `ext` came from
`(b.toNat, m)` in `signed`. -/
private def doubleLogInv (b : Bool)
    (state : List (ℕ × List Bool) × List (ℕ × List Bool)) : Prop :=
  (0 ∈ state.2.map Prod.fst ↔ b.toNat ∈ state.1.map Prod.fst) ∧
    ∀ m, (0, m) ∈ state.2 → (b.toNat, m) ∈ state.1

private theorem doubleJointOracle_planted {S : IndexedSignatureScheme} {b : Bool}
    {challengeSk otherSk : List Bool} {bound : ℕ → ℕ → ℕ} {n : ℕ} (hcap : 1 ≤ S.capacity n)
    {w : List Bool} {signed ext : List (ℕ × List Bool)}
    (hinv : doubleLogInv b (signed, ext))
    (hfresh : (requestDecoder.decode w).1 < 2 ∧ (requestDecoder.decode w).1 ∉ signed.map Prod.fst)
    (hslot : (requestDecoder.decode w).1 = b.toNat) :
    doubleJointOracle S b challengeSk otherSk bound n ((), w) (signed, ext) =
      (ProbComp.eval (S.sign challengeSk 0 (requestDecoder.decode w).2)).bind fun σ =>
        PMF.pure (List.take (bound n (requestDecoder.decode w).2.length) σ,
          requestDecoder.decode w :: signed, (0, (requestDecoder.decode w).2) :: ext) := by
  have hpos : 0 < S.capacity n := hcap
  have hnot0 : 0 ∉ ext.map Prod.fst := fun h0 => hfresh.2 (hslot ▸ hinv.1.mp h0)
  simp only [doubleJointOracle, doubleHandler, hfresh.1, hfresh.2, not_false_eq_true, and_self,
    ↓reduceIte]
  simp only [hslot, ↓reduceIte, indexedSigningOracle, requestDecoder.decode_enc, hpos, hnot0,
    not_false_eq_true, and_self, runWith_norm, pmf_norm]

private theorem doubleJointOracle_unplanted {S : IndexedSignatureScheme} {b : Bool}
    {challengeSk otherSk : List Bool} {bound : ℕ → ℕ → ℕ} {n : ℕ}
    {w : List Bool} {signed ext : List (ℕ × List Bool)}
    (hfresh : (requestDecoder.decode w).1 < 2 ∧ (requestDecoder.decode w).1 ∉ signed.map Prod.fst)
    (hslot : (requestDecoder.decode w).1 ≠ b.toNat) :
    doubleJointOracle S b challengeSk otherSk bound n ((), w) (signed, ext) =
      (ProbComp.eval (S.sign otherSk 0 (requestDecoder.decode w).2)).bind fun σ =>
        PMF.pure (σ, requestDecoder.decode w :: signed, ext) := by
  simp only [doubleJointOracle, doubleHandler, hfresh.1, hfresh.2, not_false_eq_true, and_self,
    ↓reduceIte, hslot, runWith_norm, pmf_norm]
  rfl

private theorem doubleJointOracle_refused {S : IndexedSignatureScheme} {b : Bool}
    {challengeSk otherSk : List Bool} {bound : ℕ → ℕ → ℕ} {n : ℕ}
    {w : List Bool} {signed ext : List (ℕ × List Bool)}
    (href : ¬ ((requestDecoder.decode w).1 < 2 ∧
      (requestDecoder.decode w).1 ∉ signed.map Prod.fst)) :
    doubleJointOracle S b challengeSk otherSk bound n ((), w) (signed, ext) =
      PMF.pure ([], signed, ext) := by
  simp only [doubleJointOracle, doubleHandler, href, ↓reduceIte, runWith_norm, pmf_norm]

private theorem doubleLogInv_preserve {S : IndexedSignatureScheme} {b : Bool}
    {challengeSk otherSk : List Bool} {bound : ℕ → ℕ → ℕ} {n : ℕ} (hcap : 1 ≤ S.capacity n)
    (q : Unit × List Bool) (state : List (ℕ × List Bool) × List (ℕ × List Bool))
    (hinv : doubleLogInv b state) (reply : List Bool)
    (next : List (ℕ × List Bool) × List (ℕ × List Bool))
    (hmem : (reply, next) ∈
      (doubleJointOracle S b challengeSk otherSk bound n q state).support) :
    doubleLogInv b next := by
  rcases q with ⟨⟨⟩, w⟩
  rcases state with ⟨signed, ext⟩
  by_cases hfresh :
      (requestDecoder.decode w).1 < 2 ∧ (requestDecoder.decode w).1 ∉ signed.map Prod.fst
  · by_cases hslot : (requestDecoder.decode w).1 = b.toNat
    · supp_cases hmem [doubleJointOracle_planted hcap hinv hfresh hslot]
      refine ⟨?_, ?_⟩
      · simp only [List.map_cons, List.mem_cons, true_or, hslot.symm]
      · intro m hm
        rcases List.mem_cons.mp hm with heq | hm
        · rcases Prod.mk.inj heq with ⟨-, rfl⟩
          exact List.mem_cons.mpr (Or.inl (Prod.ext hslot.symm rfl))
        · exact List.mem_cons_of_mem _ (hinv.2 m hm)
    · supp_cases hmem [doubleJointOracle_unplanted hfresh hslot]
      have hne : b.toNat ≠ (requestDecoder.decode w).1 := Ne.symm hslot
      refine ⟨?_, ?_⟩
      · simpa only [doubleLogInv, List.map_cons, List.mem_cons, hne, false_or] using hinv.1
      · exact fun m hm => List.mem_cons_of_mem _ (hinv.2 m hm)
  · supp_cases hmem [doubleJointOracle_refused hfresh]
    exact hinv

/-- Projecting the joint run onto `(output, signed)` recovers `(S.double hcap).indexedSigningOracle`
on the bundled secret key `(sk₀, sk₁)` corresponding to slot `b`. -/
private theorem map_run_doubleJointOracle {S : IndexedSignatureScheme}
    (hcap : ∀ n, 1 ≤ S.capacity n) (b : Bool) {challengeSk otherSk : List Bool}
    {bound : ℕ → ℕ → ℕ} {n : ℕ}
    (hbound : ∀ msg, ∀ σ ∈ (ProbComp.eval (S.sign challengeSk 0 msg)).support,
      σ.length ≤ bound n msg.length)
    {α : Type} (program : WordOracleComp Unit α) :
    let bundledSk := if b then encPair encBits encBits (otherSk, challengeSk)
      else encPair encBits encBits (challengeSk, otherSk)
    ((ProbOracleComp.runWith (doubleJointOracle S b challengeSk otherSk bound n) program
        ([], [])).map (fun r => (r.1, r.2.1)) =
      ProbComp.eval ((OracleComp.interpret
        (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
          ((S.double hcap).indexedSigningOracle n bundledSk))
        program).run [])) ∧
    ∀ r ∈ (ProbOracleComp.runWith (doubleJointOracle S b challengeSk otherSk bound n) program
        ([], [])).support,
      doubleLogInv b r.2 := by
  intro bundledSk
  refine ⟨?_, fun r hr => ProbOracleComp.runWith_invariant
    (oracle := doubleJointOracle S b challengeSk otherSk bound n) (invariant := doubleLogInv b)
    (fun q st hst a next hmem => doubleLogInv_preserve (hcap n) q st hst a next hmem)
    program ([], []) ⟨by simp, by simp⟩ r.1 r.2 hr⟩
  rw [ProbOracleComp.eval_run_interpret_eq_runWith]
  refine ProbOracleComp.runWith_map_state_of_invariant _ _ Prod.fst (doubleLogInv b)
    (fun q st hst a next hmem => doubleLogInv_preserve (hcap n) q st hst a next hmem)
    ?_ program ([], []) ⟨by simp, by simp⟩
  rintro ⟨⟨⟩, w⟩ ⟨signed, ext⟩ hinv
  by_cases hfresh :
      (requestDecoder.decode w).1 < 2 ∧ (requestDecoder.decode w).1 ∉ signed.map Prod.fst
  · by_cases hslot : (requestDecoder.decode w).1 = b.toNat
    · rw [doubleJointOracle_planted (hcap n) hinv hfresh hslot]
      have hdouble :
          (S.double hcap).sign bundledSk (requestDecoder.decode w).1 (requestDecoder.decode w).2 =
            S.sign challengeSk 0 (requestDecoder.decode w).2 := by
        cases b <;> simp [bundledSk, double, doubleSign, doubleKeyDecoder.decode_enc, hslot,
          -encPair_apply]
      simp only [indexedSigningOracle, capacity_double, hfresh.1, hfresh.2, not_false_eq_true,
        and_self, ↓reduceIte, hdouble, pmf_norm]
      refine PMF.bind_congr_on_support _ _ _ fun σ hσ => ?_
      rw [List.take_of_length_le (hbound _ σ hσ)]
    · rw [doubleJointOracle_unplanted hfresh hslot]
      have hob : (requestDecoder.decode w).1 = (!b).toNat := by
        cases b <;> (have := hfresh.1; simp at hslot ⊢; omega)
      have hdouble :
          (S.double hcap).sign bundledSk (requestDecoder.decode w).1 (requestDecoder.decode w).2 =
            S.sign otherSk 0 (requestDecoder.decode w).2 := by
        cases b <;> simp [bundledSk, double, doubleSign, doubleKeyDecoder.decode_enc, hob,
          -encPair_apply]
      simp only [indexedSigningOracle, capacity_double, hfresh.1, hfresh.2, not_false_eq_true,
        and_self, ↓reduceIte, hdouble, pmf_norm]
  · rw [doubleJointOracle_refused hfresh]
    simp only [indexedSigningOracle, capacity_double, hfresh, ↓reduceIte, pmf_norm]

private theorem eval_indexedEufCmaGame_doubleForgerAt (S : IndexedSignatureScheme)
    (bound : ℕ → ℕ → ℕ) (adversary : IndexedForger) (b : Bool) {n : ℕ}
    (hcap : 1 ≤ S.capacity n) :
    ProbComp.eval (S.indexedEufCmaGame (S.doubleForgerAt bound adversary b) n) =
      (ProbComp.eval (S.keyGen n)).bind fun challenge =>
        (ProbComp.eval (S.keyGen n)).bind fun other =>
          (ProbOracleComp.runWith (doubleJointOracle S b challenge.2 other.2 bound n)
              (adversary n (doublePlantPk b challenge.1 other.1)) ([], [])).map fun r =>
              !r.2.2.contains (0, r.1.2.1) && S.verify challenge.1 0 r.1.2.1 r.1.2.2 := by
  simp only [indexedEufCmaGame, doubleForgerAt, runWith_norm, pmf_norm,
    show 0 < S.capacity n from hcap, decide_true, Bool.true_and]
  rfl

/-- Plug-and-pray bound with loss `2` for `S.double hcap`: a step toward the `q`-key bound behind
[BonehShoup2023], construction `(14.4)` and Exercise 13.2, not the cited result, which takes any
number `q` of keys with loss `q`, where this fixes `q = 2` (#5293).

For every indexed forger `adversary` and every security parameter `n`, when `bound n L` covers the
length of every supported `S`-signature at index `0` on an `L`-bit message, the forging probability
against `S.double hcap` is at most `2` times the forging probability of `S.doubleForger` against
`S`. -/
theorem succProbability_indexedEufCmaGame_double_le {S : IndexedSignatureScheme}
    (hcap : ∀ n, 1 ≤ S.capacity n) {bound : ℕ → ℕ → ℕ} {n : ℕ}
    (hbound : ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ msg,
      ∀ σ ∈ (ProbComp.eval (S.sign keys.2 0 msg)).support, σ.length ≤ bound n msg.length)
    (adversary : IndexedForger) :
    Game.succProbability (ProbComp.eval ((S.double hcap).indexedEufCmaGame adversary n)) ≤
      2 * Game.succProbability
        (ProbComp.eval (S.indexedEufCmaGame (S.doubleForger bound adversary) n)) := by
  have hsplit :
      ProbComp.eval (S.indexedEufCmaGame (S.doubleForger bound adversary) n) =
        (ProbComp.eval (ProbComp.uniform Bool)).bind fun b =>
          ProbComp.eval (S.indexedEufCmaGame (S.doubleForgerAt bound adversary b) n) := by
    simp only [indexedEufCmaGame, doubleForger, runWith_norm, pmf_norm]
    exact PMF.bind_comm _ _ _
  have htwo :
      (2 : ℝ≥0∞) * (ProbComp.eval (S.indexedEufCmaGame (S.doubleForger bound adversary) n)) true =
        (ProbComp.eval (S.indexedEufCmaGame (S.doubleForgerAt bound adversary false) n)) true +
          (ProbComp.eval (S.indexedEufCmaGame (S.doubleForgerAt bound adversary true) n)) true := by
    rw [hsplit, PMF.bind_apply, tsum_fintype, Fintype.sum_bool]
    have hunif (b : Bool) : (ProbComp.eval (ProbComp.uniform Bool)) b = (2 : ℝ≥0∞)⁻¹ := by
      simp [ProbComp.eval_uniform, PMF.uniformOfFintype_apply]
    rw [hunif false, hunif true, ← mul_add, ← mul_assoc,
      ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul, add_comm]
  let slotEvent (b : Bool) (k₀ k₁ : List Bool × List Bool) : PMF Bool :=
    (ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
        ((S.double hcap).indexedSigningOracle n (encPair encBits encBits (k₀.2, k₁.2))))
      (adversary n (encPair encBits encBits (k₀.1, k₁.1)))).run [])).map fun out =>
        !out.2.contains (out.1.1, out.1.2.1) && (out.1.1 == b.toNat) &&
          S.verify (if b then k₁.1 else k₀.1) 0 out.1.2.1 out.1.2.2
  have hslot_step {vk : List Bool}
      {r : (ℕ × List Bool × List Bool) × List (ℕ × List Bool) × List (ℕ × List Bool)}
      (b : Bool) (hinv : doubleLogInv b r.2) :
      PMF.pure (!r.2.1.contains (r.1.1, r.1.2.1) && (r.1.1 == b.toNat) &&
        S.verify vk 0 r.1.2.1 r.1.2.2) true ≤
      PMF.pure (!r.2.2.contains (0, r.1.2.1) && S.verify vk 0 r.1.2.1 r.1.2.2) true := by
    cases hwin : !r.2.1.contains (r.1.1, r.1.2.1) && (r.1.1 == b.toNat) &&
        S.verify vk 0 r.1.2.1 r.1.2.2
    · simp
    · simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, beq_iff_eq,
        ← Bool.not_eq_true, List.contains_iff_mem] at hwin
      obtain ⟨⟨hfresh, hu⟩, hv⟩ := hwin
      have hwin' : (!r.2.2.contains (0, r.1.2.1) && S.verify vk 0 r.1.2.1 r.1.2.2) = true := by
        simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
          ← Bool.not_eq_true, List.contains_iff_mem]
        exact ⟨fun hmem => hfresh (hu ▸ hinv.2 _ hmem), hv⟩
      rw [hwin']
  have hslot_pair (b : Bool) (kc ko : List Bool × List Bool)
      (hkc : kc ∈ (ProbComp.eval (S.keyGen n)).support) :
      slotEvent b (if b then ko else kc) (if b then kc else ko) true ≤
        ((ProbOracleComp.runWith (doubleJointOracle S b kc.2 ko.2 bound n)
            (adversary n (doublePlantPk b kc.1 ko.1)) ([], [])).map fun r =>
            !r.2.2.contains (0, r.1.2.1) && S.verify kc.1 0 r.1.2.1 r.1.2.2) true := by
    obtain ⟨heq, hinv⟩ := map_run_doubleJointOracle hcap b (otherSk := ko.2) (hbound kc hkc)
      (adversary n (doublePlantPk b kc.1 ko.1))
    cases b
    · simp only [slotEvent, doublePlantPk, Bool.false_eq_true, ↓reduceIte] at heq ⊢
      rw [← heq, PMF.map_comp, ← PMF.bind_pure_comp, ← PMF.bind_pure_comp]
      exact PMF.bind_apply_mono_on_support _ _ fun r hr => hslot_step false (hinv r hr)
    · simp only [slotEvent, doublePlantPk, ↓reduceIte] at heq ⊢
      rw [← heq, PMF.map_comp, ← PMF.bind_pure_comp, ← PMF.bind_pure_comp]
      exact PMF.bind_apply_mono_on_support _ _ fun r hr => hslot_step true (hinv r hr)
  have hslot (b : Bool) :
      ((ProbComp.eval (S.keyGen n)).bind fun k₀ =>
        (ProbComp.eval (S.keyGen n)).bind fun k₁ => slotEvent b k₀ k₁) true ≤
      (ProbComp.eval (S.indexedEufCmaGame (S.doubleForgerAt bound adversary b) n)) true := by
    rw [eval_indexedEufCmaGame_doubleForgerAt _ _ _ _ (hcap n)]
    cases b
    · apply PMF.bind_apply_mono_on_support; intro k₀ hk₀
      apply PMF.bind_apply_mono_on_support; intro k₁ _
      exact hslot_pair false k₀ k₁ hk₀
    · conv_rhs => rw [PMF.bind_comm]
      apply PMF.bind_apply_mono_on_support; intro k₀ _
      apply PMF.bind_apply_mono_on_support; intro k₁ hk₁
      exact hslot_pair true k₁ k₀ hk₁
  have hgame :
      (ProbComp.eval ((S.double hcap).indexedEufCmaGame adversary n)) true ≤
        ((ProbComp.eval (S.keyGen n)).bind fun k₀ =>
          (ProbComp.eval (S.keyGen n)).bind fun k₁ => slotEvent false k₀ k₁) true +
        ((ProbComp.eval (S.keyGen n)).bind fun k₀ =>
          (ProbComp.eval (S.keyGen n)).bind fun k₁ => slotEvent true k₀ k₁) true := by
    simp only [indexedEufCmaGame, double, doubleKeyGen, slotEvent, ← PMF.bind_pure_comp, pmf_norm]
    refine PMF.bind_apply_le_add_on_support _ true fun k₀ _ =>
      PMF.bind_apply_le_add_on_support _ true fun k₁ _ =>
        PMF.bind_apply_le_add_on_support _ true fun out _ => ?_
    dsimp only [Function.comp_def, doubleVerify]
    cases !out.2.contains (out.1.1, out.1.2.1)
    · simp
    · rcases out with ⟨⟨_ | _ | u, msg, σ⟩, signed⟩ <;>
        simp [doubleKeyDecoder.decode_enc, -encPair_apply]
  have hne : (2 : ℝ≥0∞) *
      (ProbComp.eval (S.indexedEufCmaGame (S.doubleForger bound adversary) n)) true ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofNat_ne_top (PMF.apply_ne_top _ _)
  simpa only [Game.succProbability, ENNReal.toNNReal_mul, ENNReal.toNNReal_ofNat] using
    ENNReal.toNNReal_mono hne (htwo ▸ hgame.trans (add_le_add (hslot false) (hslot true)))

/-! ### Strict oracle-PPT efficiency of `doubleForger` -/

private abbrev DoubleCaller := (ℕ × Bool) × (List Bool × List Bool)

private noncomputable abbrev encDoubleCaller : DoubleCaller ↪ List Bool :=
  encPair (encPair encUnary encBool) (encPair encBits encBits)

private abbrev DoubleHandlerIn :=
  DoubleCaller × ((Unit × List Bool) × List (ℕ × List Bool))

private noncomputable abbrev encDoubleHandlerIn : DoubleHandlerIn ↪ List Bool :=
  encHandlerCall encDoubleCaller (encFinEnum Unit) (encList (encPair encUnary encBits))

private theorem isOraclePPTOn_doubleHandler (S : IndexedSignatureScheme) {bound : ℕ → ℕ → ℕ}
    (hboundPoly : ComputableInPolyTime (fun p : ℕ × ℕ => bound p.1 p.2)
      (encPair encUnary encUnary) encUnary) :
    IsOraclePPTOn encDoubleHandlerIn
      (encPair encBits (encList (encPair encUnary encBits)))
      (fun pair : DoubleHandlerIn =>
        S.doubleHandler pair.1.1.2 pair.1.2.2 bound pair.1.1.1 pair.2.1 pair.2.2) := by
  have hdec := requestDecoder.computableInPolyTime
  have hfreshDec : ComputableInPolyTime
      (fun pair : DoubleHandlerIn =>
        decide ((requestDecoder.decode pair.2.1.2).1 < 2 ∧
          (requestDecoder.decode pair.2.1.2).1 ∉ pair.2.2.map Prod.fst))
      encDoubleHandlerIn encBool := by
    have heq : (fun pair : DoubleHandlerIn =>
        decide ((requestDecoder.decode pair.2.1.2).1 < 2 ∧
          (requestDecoder.decode pair.2.1.2).1 ∉ pair.2.2.map Prod.fst)) =
      fun pair =>
        decide ((requestDecoder.decode pair.2.1.2).1 < 2) &&
          !(pair.2.2.any fun e => (requestDecoder.decode pair.2.1.2).1 == e.1) := by
      funext pair; rw [Bool.eq_iff_iff]
      simp only [decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false,
        List.mem_map, not_exists, not_and, beq_iff_eq, eq_comm (a := (requestDecoder.decode _).1)]
    rw [heq]; polytime
  have hslotDec : ComputableInPolyTime
      (fun pair : DoubleHandlerIn =>
        decide ((requestDecoder.decode pair.2.1.2).1 = pair.1.1.2.toNat))
      encDoubleHandlerIn encBool := by
    have heq : (fun pair : DoubleHandlerIn =>
        decide ((requestDecoder.decode pair.2.1.2).1 = pair.1.1.2.toNat)) =
      fun pair => (requestDecoder.decode pair.2.1.2).1 == (if pair.1.1.2 then 1 else 0) := by
      funext pair; rw [Bool.eq_iff_iff]; cases pair.1.1.2 <;> simp
    rw [heq]; polytime
  ppt [doubleHandler]

/-- `S.doubleForger bound adversary` is uniformly strict oracle PPT for every strict oracle-PPT
`adversary` and every plain polynomial-time bound `bound`. -/
theorem isOraclePPT_doubleForger (S : IndexedSignatureScheme) {bound : ℕ → ℕ → ℕ}
    (hboundPoly : ComputableInPolyTime (fun p : ℕ × ℕ => bound p.1 p.2)
      (encPair encUnary encUnary) encUnary)
    {adversary : IndexedForger}
    (hadversary : IsOraclePPT (encPair encUnary (encPair encBits encBits)) adversary) :
    IsOraclePPT (encPair encUnary (encPair encBits encBits))
      (S.doubleForger bound adversary) := by
  have hrun : IsOraclePPTOn encDoubleCaller
      (encPair (encPair encUnary (encPair encBits encBits))
        (encList (encPair encUnary encBits)))
      (fun caller : DoubleCaller =>
        (OracleComp.interpret
          (OracleComp.sumHandler
            (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
            (S.doubleHandler caller.1.2 caller.2.2 bound caller.1.1))
          (adversary caller.1.1 caller.2.1)).run []) := by
    refine hadversary.run_interpret_preprocess_open_of_bounded_growth
      (prepare := fun caller : DoubleCaller => (caller.1.1, caller.2.1))
      (initial := fun _ => ([] : List (ℕ × List Bool)))
      (growth := fun _ w => 2 * w.length + 12)
      (by fun_prop) (isOraclePPTOn_doubleHandler S hboundPoly) (.const [])
      (fun _ _ => True) (fun _ => trivial) (by growth_poly) ?_
    intro caller request signed _ result hresult
    have hmsg : (requestDecoder.decode request.2).2.length ≤ request.2.length :=
      length_dropFrame_le request.2
    unfold doubleHandler at hresult; dsimp only at hresult
    by_cases hfresh :
        (requestDecoder.decode request.2).1 < 2 ∧
          (requestDecoder.decode request.2).1 ∉ signed.map Prod.fst
    · rw [ite_eq_left hfresh] at hresult
      have hres : result.2 = requestDecoder.decode request.2 :: signed := by
        split_ifs at hresult <;>
          (obtain ⟨_, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hresult; rfl)
      have := hfresh.1
      exact ⟨trivial, by rw [hres]; enc_len⟩
    · rw [ite_eq_right hfresh] at hresult
      obtain rfl := OracleComp.eq_of_mem_supportWith_pure hresult
      exact ⟨trivial, Nat.le_add_right _ _⟩
  ppt [doubleForger, doubleForgerAt, doublePlantPk]

/-! ### Security preservation -/

/-- If `S` is indexed EUF-CMA secure with `∀ n, 1 ≤ S.capacity n`, then so is the capacity-`2`
scheme `S.double hcap`: a step toward [BonehShoup2023], construction `(14.4)`, not the cited
result, since it fixes `q = 2` where the source takes any `q` (#5293).

The source gives construction `(14.4)` from a one-time signature (Section 14.6.1, printed p. 597)
and proves it secure by the plug-and-pray argument of Exercise 13.2 (printed p. 575). Here the base
scheme is any indexed scheme of capacity at least `1`, used at index `0`. -/
theorem IndexedEUFCMA.double {S : IndexedSignatureScheme} (hS : S.IndexedEUFCMA)
    (hcap : ∀ n, 1 ≤ S.capacity n) :
    (S.double hcap).IndexedEUFCMA := by
  obtain ⟨bound, hboundPoly, hbound⟩ := S.exists_sign_length_bound
  apply IndexedEUFCMA.of_negligible
  intro adversary hadversary
  have hneg := hS.negligible (S.doubleForger bound adversary)
    (isOraclePPT_doubleForger S hboundPoly hadversary)
  refine negligible_of_le (hneg.const_mul 2) fun n => ?_
  simpa only [Pi.mul_apply] using
    succProbability_indexedEufCmaGame_double_le hcap
      (fun keys hkeys => hbound n keys hkeys 0 (hcap n)) adversary

end IndexedSignatureScheme

end Cslib.Crypto
