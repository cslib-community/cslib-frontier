/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Pairing.Assumptions
public import CslibFrontier.Crypto.Computational.DiscreteLog.Decodable
public import CslibFrontier.Crypto.Computational.SchnorrProtocol
public import CslibFrontier.Crypto.Computational.Signature.WordRandomOracle
public import CslibFrontier.Probability.IID.Marked
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.PPT.Extension
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Foundations.Data.List.SortedAssoc
import CslibFrontier.Languages.Probabilistic.Oracle.InterpNorm
import CslibFrontier.Languages.Probabilistic.Presample
import CslibFrontier.Probability.IID
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Tactic.PPT

/-!
# The BLS signature scheme in the random-oracle model

This module formalizes the Boneh–Lynn–Shacham (BLS) signature scheme ([BonehShoup2023],
Section 15.5.1, pp. 627–629) in the random-oracle model, together with:

* `DecodablePairingGroupFamily`: a `PairingGroupFamily` whose first source group `G₀` admits a
  canonical polynomial-time recognizable encoding (`DecodablePrimeOrderGroupFamily`), enabling
  native word-level verification that rejects non-canonical group encodings without stand-in
  validity predicates.
* **Typed BLS (`PairingGroupFamily.blsTypedROMScheme`)**: keys `(α • g₁, α)` for uniform `α`,
  signing `σ := α • H(m)`, and verification `e(H(m), pk) = e(σ, g₁)`, proved correct
  (`blsTypedROMScheme_correct`), uniquely verifiable (`blsTypedROMScheme_unique`, yielding
  `sufCmaGame_blsTypedROMScheme_eq_eufCmaGame`), and bounded in the random-oracle EUF-CMA game via
  Coron's biased-coin co-CDH reduction (`succProbability_eufCmaGame_blsTypedROMScheme_le`, matching
  [BonehShoup2023], Theorem 15.1, eq. (15.9), `2.72 · (Q_s + 1)`).
* **Native word BLS (`DecodablePairingGroupFamily.blsNativeROMScheme`, `blsWordSign`,
  `blsWordVerify`)**: native strict-PPT key generation (`P.G₁.toFamily.schnorrSigKeyGen n d`),
  word-level signing and verification, canonical uniqueness
  (`blsNativeROMScheme_unique_of_canonical`), and equality of `wordSufCmaGame` and `wordEufCmaGame`
  (`wordSufCmaGame_blsNativeROMScheme_eq_wordEufCmaGame`).

Notice that `succProbability_eufCmaGame_blsTypedROMScheme_le` bounds a distribution-level reduction
for an explicit typed call-bounded forger with ideal key generation, so it is a step toward
Theorem 15.1. The full asymptotic `ROMSignature.EUFCMA` and `ROMSignature.SUFCMA` theorems with
explicit uniform strict-PPT co-CDH reductions and native key sampling are proved in
`CslibFrontier.Crypto.Computational.Pairing.BLSSecurity`.

## Main definitions

* `Cslib.Crypto.DecodablePairingGroupFamily`: pairing group family with decodable `G₀`.
* `Cslib.Crypto.PairingGroupFamily.blsTypedROMScheme`: typed ROM BLS scheme.
* `Cslib.Crypto.PairingGroupFamily.blsBankedReduction`: presampled Coron co-CDH reduction.
* `Cslib.Crypto.DecodablePairingGroupFamily.blsNativeROMScheme`,
  `Cslib.Crypto.DecodablePairingGroupFamily.blsWordSign`,
  `Cslib.Crypto.DecodablePairingGroupFamily.blsWordVerify`: native word-level BLS scheme and
  strict oracle-PPT algorithms.

## Main results

* `Cslib.Crypto.PairingGroupFamily.blsTypedROMScheme_correct`,
  `Cslib.Crypto.PairingGroupFamily.blsTypedROMScheme_unique`,
  `Cslib.Crypto.PairingGroupFamily.sufCmaGame_blsTypedROMScheme_eq_eufCmaGame`: correctness and
  unique signatures for typed BLS.
* `Cslib.Crypto.PairingGroupFamily.succProbability_eufCmaGame_blsTypedROMScheme_le_of_banked`,
  `Cslib.Crypto.PairingGroupFamily.succProbability_eufCmaGame_blsTypedROMScheme_le`: quantitative
  Coron co-CDH bound ([BonehShoup2023], Theorem 15.1, eq. (15.9)).
* `Cslib.Crypto.DecodablePairingGroupFamily.isOraclePPTOn_blsWordSign`,
  `Cslib.Crypto.DecodablePairingGroupFamily.isOraclePPTOn_blsWordVerify`,
  `Cslib.Crypto.DecodablePairingGroupFamily.blsNativeROMScheme_correct`,
  `Cslib.Crypto.DecodablePairingGroupFamily.wordSufCmaGame_blsNativeROMScheme_eq_wordEufCmaGame`:
  efficiency, correctness, and strong/existential equivalence for native word BLS.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 13.4.1 (Lemma 13.6, p. 543) and Section 15.5.1
  (pp. 627–629, Theorem 15.1).
-/

public section

namespace Cslib.Crypto

open Probability OracleComp Protocols Protocols.ROMSignature Turing.MultiTapeTM
open scoped ENNReal NNReal Cslib.Probability.PMF

/-! ### Pairing group families with decodable `G₀` -/

/-- A pairing group family whose first source group `G₀` admits a canonical polynomial-time
recognizable decoder (`DecodablePrimeOrderGroupFamily`), so arbitrary signature bit strings can be
tested and decoded in polynomial time without external validity stand-ins. -/
structure DecodablePairingGroupFamily extends PairingGroupFamily where
  /-- Decode a bit string as an element of `G₀.Carrier d`, returning `none` if the word is not
  the canonical encoding of any element. -/
  decode₀ : ∀ d : G₀.Desc, List Bool → Option (G₀.Carrier d)
  /-- Decoding the encoding of any element recovers it. -/
  decode₀_encode : ∀ (d : G₀.Desc) (x : G₀.Carrier d), decode₀ d (G₀.encode d x) = some x
  /-- `decode₀` rejects non-canonical encodings. -/
  encode_eq_of_decode₀_eq_some :
    ∀ {d : G₀.Desc} {w : List Bool} {x : G₀.Carrier d}, decode₀ d w = some x → w = G₀.encode d x
  /-- Testing membership in `Set.range (G₀.encode d)` is computable in polynomial time. -/
  computableInPolyTime_isElem₀ :
    ComputableInPolyTime (fun p : G₀.Desc × List Bool => (decode₀ p.1 p.2).isSome)
      (encPair G₀.encDesc encBits) encBool

namespace DecodablePairingGroupFamily

variable (P : DecodablePairingGroupFamily)

/-- View the first source group of `P` as a `DecodablePrimeOrderGroupFamily`. -/
@[expose] def toDecodableG₀ : DecodablePrimeOrderGroupFamily where
  toPrimeOrderGroupFamily := P.G₀
  decode := P.decode₀
  decode_encode := P.decode₀_encode
  encode_eq_of_decode_eq_some := P.encode_eq_of_decode₀_eq_some
  computableInPolyTime_isElem := P.computableInPolyTime_isElem₀

/-- Boolean group-element membership test on `G₀`: `true` iff `P.decode₀ d w` succeeds. -/
@[expose] def isElem₀ (p : P.G₀.Desc × List Bool) : Bool :=
  P.toDecodableG₀.isElem p

@[fun_prop] theorem computableInPolyTime_isElem₀_app {α : Type} {enc : α ↪ List Bool}
    {d : α → P.G₀.Desc} {w : α → List Bool} (hd : ComputableInPolyTime d enc P.G₀.encDesc)
    (hw : ComputableInPolyTime w enc encBits) :
    ComputableInPolyTime (fun a => P.isElem₀ (d a, w a)) enc encBool :=
  DecodablePrimeOrderGroupFamily.computableInPolyTime_isElem_app hd hw

/-- Build a `DecodablePairingGroupFamily` from a `DecodablePrimeOrderGroupFamily` for `G₀` and
the remaining pairing components. -/
abbrev ofDecodable (F₀ : DecodablePrimeOrderGroupFamily)
    (G₁ GT : F₀.toPrimeOrderGroupFamily.Companion)
    (pair : ∀ d,
      F₀.Carrier d →ₗ[ZMod (F₀.order d)] G₁.Carrier d →ₗ[ZMod (F₀.order d)] GT.Carrier d)
    (pair_generator : ∀ d, pair d (F₀.generator d) (G₁.generator d) = GT.generator d)
    (pairEncoded : F₀.Desc × List Bool × List Bool → List Bool)
    (pairEncoded_encode : ∀ d u v,
      pairEncoded (d, F₀.encode d u, G₁.encode d v) = GT.encode d (pair d u v))
    (computableInPolyTime_pairEncoded :
      ComputableInPolyTime pairEncoded (encDescBitsPair F₀.encDesc) encBits) :
    DecodablePairingGroupFamily where
  G₀ := F₀.toPrimeOrderGroupFamily
  G₁ := G₁
  GT := GT
  pair := pair
  pair_generator := pair_generator
  pairEncoded := pairEncoded
  pairEncoded_encode := pairEncoded_encode
  computableInPolyTime_pairEncoded := computableInPolyTime_pairEncoded
  decode₀ := F₀.decode
  decode₀_encode := F₀.decode_encode
  encode_eq_of_decode₀_eq_some := F₀.encode_eq_of_decode_eq_some
  computableInPolyTime_isElem₀ := F₀.computableInPolyTime_isElem

end DecodablePairingGroupFamily

/-! ### Shared memoize preservation and unique-signature helpers -/

private theorem list_lookup_beq_congr {α β : Type} (inst₁ : BEq α) [hL₁ : LawfulBEq α]
    (inst₂ : BEq α) [hL₂ : LawfulBEq α] (k : α) (l : List (α × β)) :
    @List.lookup α β inst₁ k l = @List.lookup α β inst₂ k l := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    have hbeq : @BEq.beq α inst₁ k hd.1 = @BEq.beq α inst₂ k hd.1 :=
      Bool.eq_iff_iff.mpr
        ((@beq_iff_eq α inst₁ hL₁ k hd.1).trans (@beq_iff_eq α inst₂ hL₂ k hd.1).symm)
    simp only [List.lookup, hbeq, ih]

private theorem list_contains_beq_congr {α : Type} (inst₁ : BEq α) [LawfulBEq α]
    (inst₂ : BEq α) [LawfulBEq α] (l : List α) (x : α) :
    @List.contains α inst₁ l x = @List.contains α inst₂ l x :=
  Bool.eq_iff_iff.mpr ((@List.contains_iff_mem α inst₁ _ _ _).trans
    (@List.contains_iff_mem α inst₂ _ _ _).symm)

private theorem list_lookup_map_snd {α β γ : Type} [BEq α] (f : β → γ)
    (l : List (α × β)) (q : α) :
    (l.map fun x => (x.1, f x.2)).lookup q = (l.lookup q).map f := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons, List.lookup]
    cases (q == hd.1) <;> simp [ih]

private theorem mem_support_memoize_lookup_preserve {Query Digest : Type} [DecidableEq Query]
    (compute : Query → PMF Digest) {key q : Query} {cache : List (Query × Digest)} {h : Digest}
    {res : Digest × List (Query × Digest)} (hres : res ∈ (memoize compute key cache).support)
    (hlookup : cache.lookup q = some h) :
    res.2.lookup q = some h := by
  cases hkey : cache.lookup key with
  | some v =>
    rw [memoize_of_some _ _ _ _ hkey, PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hres
    exact hres ▸ hlookup
  | none =>
    rw [memoize_of_none _ _ _ hkey, PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hres
    obtain ⟨v, _, hv⟩ := hres
    rw [PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hv
    subst hv
    have hne : q ≠ key := fun heq => by simp [heq, hkey] at hlookup
    simp only [List.lookup_cons, beq_eq_false_iff_ne.mpr hne, hlookup]

private theorem mem_support_interpret_oracle_lookup_preserve {Query Digest α : Type}
    [DecidableEq Query] [Fintype Digest] [Nonempty Digest]
    (prog : OracleComp (fun _ : Query => Digest) α) {q : Query}
    {cache : List (Query × Digest)} {h : Digest} {res : α × List (Query × Digest)}
    (hres : res ∈ ((interpret (oracle Digest) prog).run cache).support)
    (hlookup : cache.lookup q = some h) :
    res.2.lookup q = some h := by
  induction prog using OracleComp.induction generalizing cache with
  | pure a =>
    simp only [interpret_pure, StateT.run_pure, PMF.monad_pure_eq_pure,
      PMF.mem_support_pure_iff] at hres
    exact hres ▸ hlookup
  | query_bind key cont ih =>
    change res ∈ ((interpret (oracle Digest) (OracleComp.query key >>= cont)).run cache).support
      at hres
    simp only [interpret_bind, interpret_query, StateT.run_bind, PMF.monad_bind_eq_bind,
      PMF.mem_support_bind_iff] at hres
    obtain ⟨step, hstep, hcont⟩ := hres
    exact ih step.1 hcont (mem_support_memoize_lookup_preserve
      (fun _ => PMF.uniformOfFintype Digest) hstep hlookup)

/-- Generic `sufCma = eufCma` bridge for deterministic-verification unique-signature ROM schemes:
whenever `verify` checks `pred d sig` at the single hash query `m`, every `sign sk m` leaves `(m,
sig)` verifying against `m`'s cached digest, and at most one signature verifies per digest,
`sufCma` and `eufCma` coincide on `worldRealize`. -/
private theorem sufCma_worldRealize_eq_eufCma_of_unique {PK SK M Sig Digest : Type}
    [DecidableEq M] [DecidableEq Sig] [Fintype Digest] [Nonempty Digest]
    (scheme : ROMSignature.Scheme PK SK M Sig M Digest)
    (pk : PK) (sk : SK) (pred : Digest → Sig → Bool)
    (hverify : ∀ m σ, scheme.verify pk m σ = (fun d => pred d σ) <$> OracleComp.query m)
    (hsign : ∀ m coins cache res,
      coins ∈ (scheme.signCoins sk m).support →
      res ∈ ((interpret (oracle Digest) (scheme.sign sk m coins)).run cache).support →
        ∃ d, res.2.lookup m = some d ∧ pred d res.1 = true)
    (hunique : ∀ d σ₁ σ₂, pred d σ₁ = true → pred d σ₂ = true → σ₁ = σ₂)
    (forger : ProbOracleComp (ForgerSpec M M Sig Digest) (M × Sig)) :
    Interactive.World.eval (world scheme sk) (worldRealize scheme pk forger
      (fun verified msig pairs => verified && !pairs.contains msig)) =
    Interactive.World.eval (world scheme sk) (worldRealize scheme pk forger
      (fun verified ⟨msg, _⟩ pairs => verified && !(pairs.map Prod.fst).contains msg)) := by
  rw [eval_world_worldRealize, eval_world_worldRealize]
  simp only [PMF.monad_bind_eq_bind]
  have hlogged :
      ∀ res ∈ (ProbOracleComp.runWith (forgerWorldImpl scheme sk)
          (runLoggedForger forger) []).support,
        ∀ p ∈ res.1.2, ∃ d, res.2.lookup p.1 = some d ∧ pred d p.2 = true := by
    intro res hres
    unfold runLoggedForger at hres
    rw [ProbOracleComp.runWith_run_interpret logSigning (forgerWorldImpl scheme sk)
      forger [] [], PMF.mem_support_map_iff] at hres
    obtain ⟨⟨msig, pairs, cache⟩, hmem, rfl⟩ := hres
    refine ProbOracleComp.runWith_invariant _
      (fun st : List (M × Sig) × List (M × Digest) =>
        ∀ p ∈ st.1, ∃ d, st.2.lookup p.1 = some d ∧ pred d p.2 = true)
      (fun q state hs a st' hstep => ?_) forger ([], []) (fun _ h => by cases h)
      msig (pairs, cache) hmem
    rw [PMF.mem_support_map_iff] at hstep
    obtain ⟨⟨⟨a', b⟩, c⟩, hrun, heqc⟩ := hstep
    cases heqc
    rcases q with m | x
    · change ((a, b), c) ∈ (ProbOracleComp.runWith (forgerWorldImpl scheme sk)
        (ProbOracleComp.query (spec := ForgerSpec M M Sig Digest) (Sum.inl m) >>=
          fun sig => pure (sig, (m, sig) :: state.1)) state.2).support at hrun
      simp only [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query,
        ProbOracleComp.runWith_pure, forgerWorldImpl, sumHandler, PMF.monad_bind_eq_bind,
        PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hrun
      obtain ⟨⟨sig, cache₁⟩, ⟨coins, hcoins, hsig⟩, hpair⟩ := hrun
      cases hpair
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hsign m coins state.2 (sig, cache₁) hcoins hsig
      · obtain ⟨d, hd, hpred⟩ := hs p hp
        exact ⟨d, mem_support_interpret_oracle_lookup_preserve
          (scheme.sign sk m coins) hsig hd, hpred⟩
    · change ((a, b), c) ∈ (ProbOracleComp.runWith (forgerWorldImpl scheme sk)
        (ProbOracleComp.query (spec := ForgerSpec M M Sig Digest) (Sum.inr x) >>=
          fun d => pure (d, state.1)) state.2).support at hrun
      simp only [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query,
        ProbOracleComp.runWith_pure, forgerWorldImpl, sumHandler, PMF.monad_bind_eq_bind,
        PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hrun
      obtain ⟨⟨d, cache₁⟩, hd, hpair⟩ := hrun
      cases hpair
      intro p hp
      obtain ⟨dp, hdp, hpred⟩ := hs p hp
      exact ⟨dp, mem_support_memoize_lookup_preserve _ hd hdp, hpred⟩
  refine PMF.bind_congr_on_support _ _ _ fun ⟨⟨msig, pairs⟩, cache⟩ hmem => ?_
  have hinv := hlogged _ hmem
  refine PMF.bind_congr_on_support _ _ _ fun verified hver => ?_
  rw [hverify msig.1 msig.2, interpret_map, interpret_query, StateT.run_map,
    PMF.monad_map_eq_map, PMF.mem_support_map_iff] at hver
  obtain ⟨⟨d, cache'⟩, hd, rfl⟩ := hver
  by_cases hpred : pred d msig.2 = true
  · by_cases hmsg : (pairs.map Prod.fst).contains msig.1 = true
    · obtain ⟨⟨m', sig₀⟩, hpMem, hm'⟩ := List.mem_map.mp (List.contains_iff_mem.mp hmsg)
      dsimp only at hm'
      subst hm'
      obtain ⟨d₀, hd₀, hpred₀⟩ := hinv (msig.1, sig₀) hpMem
      change (d, cache') ∈ ((oracle Digest msig.1).run cache).support at hd
      rw [run_oracle_of_lookup_eq_some hd₀, PMF.mem_support_pure_iff] at hd
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hd
      obtain rfl : msig.2 = sig₀ := hunique _ msig.2 sig₀ hpred hpred₀
      rw [List.contains_iff_mem.mpr (by simpa only [Prod.eta] using hpMem), hmsg]
    · have hpairNotMem : msig ∉ pairs := fun hm =>
        hmsg (List.contains_iff_mem.mpr (List.mem_map.mpr ⟨msig, hm, rfl⟩))
      rw [Bool.eq_false_iff.mpr fun h => hpairNotMem (List.contains_iff_mem.mp h),
        Bool.eq_false_iff.mpr hmsg]
  · simp [hpred]

namespace PairingGroupFamily

variable (P : PairingGroupFamily)

/-- Canonical `Fintype` instance on `P.G₀.Carrier d`, matching `ZMod (P.G₀.order d)` via
`P.G₀.smul_generator_bijective d`. -/
@[instance_reducible]
noncomputable def fintypeG₀ (d : P.G₀.Desc) : Fintype (P.G₀.Carrier d) :=
  Fintype.ofBijective _ (P.G₀.smul_generator_bijective d)

/-! ### Typed BLS scheme in the random-oracle model -/

/-- The typed BLS signature scheme ([BonehShoup2023], Section 15.5.1, pp. 627–628) over `P` and
fixed parameters `d : P.G₀.Desc`, with `H : List Bool → P.G₀.Carrier d` modeled as a random
oracle returning uniform elements of `G₀`. -/
@[expose] noncomputable def blsTypedROMScheme (d : P.G₀.Desc) :
    ROMSignature.Scheme (P.G₁.Carrier d) (ZMod (P.G₀.order d)) (List Bool)
      (P.G₀.Carrier d) (List Bool) (P.G₀.Carrier d) where
  keyGen := (PMF.uniformOfFintype (ZMod (P.G₀.order d))).map fun α => (α • P.G₁.generator d, α)
  SignCoins := Unit
  signCoins _ _ := PMF.pure ()
  sign α msg _ := (fun h => α • h) <$> OracleComp.query msg
  verify u msg σ :=
    (fun h => decide (P.pair d h u = P.pair d σ (P.G₁.generator d))) <$> OracleComp.query msg

/-- **Non-degeneracy / unique-pairing rule**: pairing with `g₁` is injective on `G₀`
(`e(σ₁, g₁) = e(σ₂, g₁) ↔ σ₁ = σ₂`). -/
theorem pair_right_generator_injective (d : P.G₀.Desc) :
    Function.Injective (fun σ : P.G₀.Carrier d => P.pair d σ (P.G₁.generator d)) := by
  intro σ₁ σ₂ h
  obtain ⟨a₁, rfl⟩ := P.G₀.smul_generator_surjective d σ₁
  obtain ⟨a₂, rfl⟩ := P.G₀.smul_generator_surjective d σ₂
  simp only [map_smul, LinearMap.smul_apply, P.pair_generator] at h
  rw [P.GT.toFamily.smul_generator_injective d h]

/-- **Correctness** of the typed BLS signature scheme: every honest signature verifies. -/
theorem blsTypedROMScheme_correct (d : P.G₀.Desc) [Fintype (P.G₀.Carrier d)] :
    (P.blsTypedROMScheme d).Correct := by
  intro keys hkeys m _ _ cache signed hsigned verified hverified
  obtain ⟨α, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hkeys
  simp only [blsTypedROMScheme, interpret_map, interpret_query, StateT.run_map,
    PMF.monad_map_eq_map, PMF.mem_support_map_iff] at hsigned hverified
  obtain ⟨r, hr, rfl⟩ := hsigned
  obtain ⟨r', hr', rfl⟩ := hverified
  change r' ∈ ((oracle (P.G₀.Carrier d) m).run r.2).support at hr'
  rw [run_oracle_of_lookup_eq_some (lookup_of_mem_support_oracle hr), PMF.mem_support_pure_iff]
    at hr'
  subst hr'
  simp only [map_smul, LinearMap.smul_apply, decide_true]

/-- **Unique signatures** for typed BLS: for any public key `u`, hash point `h`, and candidate
signatures `σ₁, σ₂`, if both satisfy the verification equation for `(u, h)` then `σ₁ = σ₂`. -/
theorem blsTypedROMScheme_unique (d : P.G₀.Desc) (u : P.G₁.Carrier d) (h σ₁ σ₂ : P.G₀.Carrier d)
    (h₁ : P.pair d h u = P.pair d σ₁ (P.G₁.generator d))
    (h₂ : P.pair d h u = P.pair d σ₂ (P.G₁.generator d)) :
    σ₁ = σ₂ :=
  P.pair_right_generator_injective d (h₁.symm.trans h₂)

/-- **Strong = existential unforgeability for typed BLS**: because signatures are unique per `(u,
m, H(m))`, `sufCmaGame` and `eufCmaGame` define the exact same distribution for every forger. -/
theorem sufCmaGame_blsTypedROMScheme_eq_eufCmaGame (d : P.G₀.Desc) [Fintype (P.G₀.Carrier d)]
    (A : ROMSignature.Forger (P.G₁.Carrier d) (List Bool) (P.G₀.Carrier d) (List Bool)
      (P.G₀.Carrier d)) :
    sufCmaGame (P.blsTypedROMScheme d) A = eufCmaGame (P.blsTypedROMScheme d) A := by
  rw [eufCmaGame_eq_worldGame]
  unfold sufCmaGame
  refine PMF.bind_congr_on_support _ _ _ fun keys hkeys => ?_
  obtain ⟨α, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hkeys
  refine PMF.bind_congr_on_support _ _ _ fun s _ => ?_
  refine sufCma_worldRealize_eq_eufCma_of_unique (P.blsTypedROMScheme d) (α • P.G₁.generator d) α
    (fun h σ => decide (P.pair d h (α • P.G₁.generator d) = P.pair d σ (P.G₁.generator d)))
    (fun _ _ => rfl) (fun m _ cache res _ hres => ?_)
    (fun h σ₁ σ₂ h₁ h₂ => P.blsTypedROMScheme_unique d (α • P.G₁.generator d) h σ₁ σ₂
      (decide_eq_true_eq.mp h₁) (decide_eq_true_eq.mp h₂)) _
  simp only [blsTypedROMScheme, interpret_map, interpret_query, StateT.run_map,
    PMF.monad_map_eq_map, PMF.mem_support_map_iff] at hres
  obtain ⟨r, hr, rfl⟩ := hres
  refine ⟨r.1, lookup_of_mem_support_oracle hr, ?_⟩
  simp only [map_smul, LinearMap.smul_apply, decide_true]

/-! ### Banked Coron reduction and typed Theorem 15.1 bound -/

/-- Shared handler collapsing signing and hash calls in `blsRunCore`. -/
private def blsCoreHandler (d : P.G₀.Desc) (α : ZMod (P.G₀.order d)) :
    (q : List Bool ⊕ List Bool) →
      StateT (List (List Bool)) (OracleComp (fun _ : List Bool => P.G₀.Carrier d))
        (ForgerSpec (List Bool) (List Bool) (P.G₀.Carrier d) (P.G₀.Carrier d) q)
  | .inl m => fun signed =>
    (fun h => (α • h, m :: signed)) <$>
      OracleComp.query (spec := fun _ : List Bool => P.G₀.Carrier d) m
  | .inr q => fun signed =>
    (fun h => (h, signed)) <$>
      OracleComp.query (spec := fun _ : List Bool => P.G₀.Carrier d) q

/-- Collapse a typed `Forger` run and its final verification query into a single program over
`List Bool → P.G₀.Carrier d`. -/
private def blsRunCore (d : P.G₀.Desc) (α : ZMod (P.G₀.order d))
    (prog : OracleComp (ForgerSpec (List Bool) (List Bool) (P.G₀.Carrier d) (P.G₀.Carrier d))
      (List Bool × P.G₀.Carrier d)) :
    OracleComp (fun _ : List Bool => P.G₀.Carrier d)
      ((List Bool × P.G₀.Carrier d) × List (List Bool) × P.G₀.Carrier d) := do
  let res ← (OracleComp.interpret (P.blsCoreHandler d α) prog).run []
  let hstar ← OracleComp.query (spec := fun _ : List Bool => P.G₀.Carrier d) res.1.1
  return (res.1, res.2, hstar)

private theorem isQueryBounded_blsRunCore (d : P.G₀.Desc) (α : ZMod (P.G₀.order d))
    {prog : OracleComp (ForgerSpec (List Bool) (List Bool) (P.G₀.Carrier d) (P.G₀.Carrier d))
      (List Bool × P.G₀.Carrier d)}
    {Qs Qro : ℕ} (hs : prog.IsCostBounded signingCost Qs)
    (hh : prog.IsCostBounded hashCost Qro) :
    (P.blsRunCore d α prog).IsQueryBounded (Qs + Qro + 1) := by
  have htotal : prog.IsQueryBounded (Qs + Qro) :=
    (hs.add hh).of_le fun q => by cases q <;> simp [signingCost, hashCost]
  have hrun : ((OracleComp.interpret (P.blsCoreHandler d α) prog).run []).IsQueryBounded
      (Qs + Qro) :=
    IsCostBounded.run_interpret (cost' := fun _ => 1)
      (fun q _ => by cases q <;> exact (isCostBounded_map_iff _ _ _).mpr (IsCostBounded.query _))
      htotal []
  exact (IsCostBounded.bind hrun fun _ =>
    IsCostBounded.bind (IsCostBounded.query _) fun _ => IsCostBounded.pure _ 0).mono (by omega)

private theorem run_interpret_blsRunCore (d : P.G₀.Desc) [Fintype (P.G₀.Carrier d)]
    (α : ZMod (P.G₀.order d))
    (prog : OracleComp (ForgerSpec (List Bool) (List Bool) (P.G₀.Carrier d) (P.G₀.Carrier d))
      (List Bool × P.G₀.Carrier d))
    (cache : List (List Bool × P.G₀.Carrier d)) :
    ((interpret (oracle (P.G₀.Carrier d)) (P.blsRunCore d α prog)).run cache).map
        (fun ((msig, signed, hstar), _) =>
          decide (P.pair d hstar (α • P.G₁.generator d) =
            P.pair d msig.2 (P.G₁.generator d)) && !(signed.contains msig.1)) =
      (do
        let forged ← (interpret (handler (P.blsTypedROMScheme d) α) prog).run (cache, [])
        let verified ← (interpret (oracle (P.G₀.Carrier d))
          ((P.blsTypedROMScheme d).verify (α • P.G₁.generator d) forged.1.1 forged.1.2)).run
            forged.2.1
        return verified.1 && !(forged.2.2.contains forged.1.1)) := by
  have hinner :
      ∀ (p : OracleComp (ForgerSpec (List Bool) (List Bool) (P.G₀.Carrier d) (P.G₀.Carrier d))
          (List Bool × P.G₀.Carrier d)) c signed,
      (interpret (oracle (P.G₀.Carrier d))
        ((interpret (P.blsCoreHandler d α) p).run signed)).run c =
      ((interpret (handler (P.blsTypedROMScheme d) α) p).run (c, signed)).map
        fun (res, c', s') => ((res, s'), c') := by
    intro p
    induction p using OracleComp.induction with
    | pure a =>
      intro c s
      simp [interp_norm, pmf_norm]
    | query_bind q cont ih =>
      intro c s
      change (interpret (oracle (P.G₀.Carrier d))
        ((interpret (P.blsCoreHandler d α) (OracleComp.query q >>= cont)).run s)).run c =
        ((interpret (handler (P.blsTypedROMScheme d) α)
          (OracleComp.query q >>= cont)).run (c, s)).map
          fun (res, c', s') => ((res, s'), c')
      cases q <;> (
        simp only [interpret_bind, interpret_query, blsCoreHandler, handler, blsTypedROMScheme,
          StateT.run_bind]
        dsimp only [StateT.run]
        simp only [interpret_map, interpret_query]
        dsimp only [Functor.map, StateT.map]
        simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind,
          PMF.map_bind]
        exact PMF.bind_congr_on_support _ _ _ fun hc _ => ih _ hc.2 _)
  simp only [blsRunCore, StateT.run_bind, interpret_bind, interpret_pure,
    StateT.run_pure, interpret_query, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.map_bind, hinner, PMF.bind_map, blsTypedROMScheme, interpret_map, StateT.run_map,
    PMF.monad_map_eq_map]
  refine PMF.bind_congr_on_support _ _ _ fun ⟨msig, c', s'⟩ _ => ?_
  simp only [Function.comp_def, PMF.map_bind, PMF.pure_map]

/-- Indexed banked step over a fixed list `vals : List Val` and projection `proj : Val → H`,
consuming one step index per query (cache hit or miss) and inserting `(q, (val, step))` on cache
miss. -/
private def bankStepIndexed {Val H : Type} (proj : Val → H) (fallback : Val)
    (vals : List Val) (q : List Bool) (st : List (List Bool × (Val × ℕ)) × ℕ) :
    H × (List (List Bool × (Val × ℕ)) × ℕ) :=
  match st.1.lookup q with
  | some entry => (proj entry.1, (st.1, st.2 + 1))
  | none =>
    let val := vals.getD st.2 fallback
    (proj val, ((q, (val, st.2)) :: st.1, st.2 + 1))

private def bankStepHandler {Val H : Type} (proj : Val → H) (fallback : Val)
    (vals : List Val) (q : List Bool) :
    StateT (List (List Bool × (Val × ℕ)) × ℕ) Id H :=
  fun st => bankStepIndexed proj fallback vals q st

private theorem bankStepIndexed_step_bounds {Val H : Type} (proj : Val → H)
    (fallback : Val) (vals : List Val) (x : List Bool)
    (table : List (List Bool × (Val × ℕ))) (count : ℕ)
    (hidx : ∀ q v i, (q, (v, i)) ∈ table → i < count)
    (hnodup : ∀ q₁ v₁ q₂ v₂ i, table.lookup q₁ = some (v₁, i) →
      table.lookup q₂ = some (v₂, i) → q₁ = q₂) :
    let r := bankStepIndexed proj fallback vals x (table, count)
    let vstar := match table.lookup x with
      | some (v, _) => v
      | none => vals.getD count fallback
    (∀ q v i, (q, (v, i)) ∈ r.2.1 → i < count + 1) ∧
      (∀ q₁ v₁ q₂ v₂ i, r.2.1.lookup q₁ = some (v₁, i) →
        r.2.1.lookup q₂ = some (v₂, i) → q₁ = q₂) ∧
      (∀ q v i, table.lookup q = some (v, i) → r.2.1.lookup q = some (v, i)) ∧
      (∃ i, r.2.1.lookup x = some (vstar, i) ∧ r.1 = proj vstar ∧ i < count + 1) ∧
      r.2.2 = count + 1 := by
  dsimp only [bankStepIndexed]
  cases hlook : table.lookup x with
  | some entry =>
    refine ⟨fun q v i h => Nat.lt_succ_of_lt (hidx q v i h), hnodup, fun _ _ _ h => h,
      ⟨entry.2, hlook, rfl,
        Nat.lt_succ_of_lt (hidx x entry.1 entry.2 (List.mem_of_lookup_eq_some hlook))⟩, rfl⟩
  | none =>
    refine ⟨?_, ?_, ?_, ⟨count, by simp, rfl, Nat.lt_succ_self _⟩, rfl⟩
    · rintro q v i h
      rcases List.mem_cons.mp h with ⟨_, _, rfl⟩ | htail
      · exact Nat.lt_succ_self _
      · exact Nat.lt_succ_of_lt (hidx q v i htail)
    · intro q₁ v₁ q₂ v₂ i h1 h2
      rw [List.lookup_cons_eq_ite] at h1 h2
      split_ifs at h1 h2 with eq1 eq2 eq2
      · exact eq1.trans eq2.symm
      · cases h1
        exact absurd (hidx q₂ v₂ count (List.mem_of_lookup_eq_some h2)) (lt_irrefl _)
      · cases h2
        exact absurd (hidx q₁ v₁ count (List.mem_of_lookup_eq_some h1)) (lt_irrefl _)
      · exact hnodup q₁ v₁ q₂ v₂ i h1 h2
    · intro q v i hq
      have hne : q ≠ x := fun h => by simp [h, hlook] at hq
      simp only [List.lookup_cons, beq_eq_false_iff_ne.mpr hne, hq]

private theorem bankStepIndexed_eq_withSampleList {Val H : Type} (proj : Val → H)
    (fallback : Val) (all : List Val) {γ : Type}
    (prog : OracleComp (fun _ : List Bool => H) γ)
    (table : List (List Bool × (Val × ℕ))) (k : ℕ) :
    PMF.pure ((OracleComp.interpret (bankStepHandler proj fallback all) prog).run (table, k)) =
      ((OracleComp.interpret (withSampleList (spec := fun _ : List Bool => H) (m := PMF)
          fallback fun val q (st : List (List Bool × (Val × ℕ)) × ℕ) =>
          match st.1.lookup q with
          | some entry => PMF.pure (proj entry.1, (st.1, st.2 + 1))
          | none => PMF.pure (proj val, ((q, (val, st.2)) :: st.1, st.2 + 1)))
        prog).run ((table, k), all.drop k)).map fun (a, st, _) => (a, st) := by
  induction prog using OracleComp.induction generalizing table k with
  | pure a =>
    simp only [interpret_pure, StateT.run_pure, PMF.monad_pure_eq_pure, PMF.pure_map]
    rfl
  | query_bind q cont ih =>
    change PMF.pure ((OracleComp.interpret (bankStepHandler proj fallback all)
        (OracleComp.query q >>= cont)).run (table, k)) =
      ((OracleComp.interpret (withSampleList (spec := fun _ : List Bool => H) (m := PMF)
          fallback fun val q (st : List (List Bool × (Val × ℕ)) × ℕ) =>
          match st.1.lookup q with
          | some entry => PMF.pure (proj entry.1, (st.1, st.2 + 1))
          | none => PMF.pure (proj val, ((q, (val, st.2)) :: st.1, st.2 + 1)))
        (OracleComp.query q >>= cont)).run ((table, k), all.drop k)).map fun (a, st, _) =>
          (a, st)
    simp only [StateT.run_bind, interpret_bind, interpret_query]
    dsimp only [bankStepHandler, withSampleList, StateT.run, bankStepIndexed]
    simp only [PMF.monad_map_eq_map, PMF.monad_bind_eq_bind, PMF.map_bind, PMF.bind_map,
      Function.comp_def]
    have hhead : (all.drop k).headD fallback = all.getD k fallback := by
      rw [List.getD_eq_getElem?_getD, List.headD_eq_head?_getD, List.head?_drop]
    have hdrop : (all.drop k).tail = all.drop (k + 1) := by
      simp [List.tail_drop]
    cases hlook : table.lookup q with
    | some entry =>
      simp only [PMF.pure_bind, hdrop]
      exact ih (proj entry.1) table (k + 1)
    | none =>
      simp only [hhead, hdrop, PMF.pure_bind]
      exact ih (proj (all.getD k fallback)) ((q, (all.getD k fallback, k)) :: table) (k + 1)

private noncomputable def bankOnlineHandler (d : P.G₀.Desc) [Fintype (P.G₀.Carrier d)]
    (q : List Bool) :
    StateT (List (List Bool × (P.G₀.Carrier d × ℕ)) × ℕ) PMF (P.G₀.Carrier d) :=
  fun st => (PMF.uniformOfFintype (P.G₀.Carrier d)).bind fun val =>
    match st.1.lookup q with
    | some entry => PMF.pure (entry.1, (st.1, st.2 + 1))
    | none => PMF.pure (val, ((q, (val, st.2)) :: st.1, st.2 + 1))

/-- Online `(bankStepIndexed id)` with fresh uniform draws reproduces `oracle G₀` on projected
caches. -/
private theorem interpret_online_bankStep_eq_oracle (d : P.G₀.Desc) [Fintype (P.G₀.Carrier d)]
    {γ : Type} (prog : OracleComp (fun _ : List Bool => P.G₀.Carrier d) γ)
    (table : List (List Bool × (P.G₀.Carrier d × ℕ))) (k : ℕ) :
    ((interpret (P.bankOnlineHandler d) prog).run (table, k)).map
        (fun (a, st) => (a, st.1.map fun (key, v, _) => (key, v))) =
      (interpret (oracle (P.G₀.Carrier d)) prog).run
        (table.map fun (key, v, _) => (key, v)) := by
  induction prog using OracleComp.induction generalizing table k with
  | pure a => simp [interp_norm, pmf_norm]
  | query_bind q cont ih =>
    change
      ((interpret (P.bankOnlineHandler d) (OracleComp.query q >>= cont)).run (table, k)).map _ =
        (interpret (oracle (P.G₀.Carrier d)) (OracleComp.query q >>= cont)).run _
    simp only [StateT.run_bind, interpret_bind, interpret_query,
      PMF.monad_bind_eq_bind, PMF.map_bind]
    have hlook := (list_lookup_beq_congr List.instBEq instBEqOfDecidableEq q _).symm.trans
      (list_lookup_map_snd Prod.fst table q)
    cases htab : table.lookup q with
    | some entry =>
      rw [htab] at hlook
      rw [run_oracle_of_lookup_eq_some hlook, PMF.pure_bind]
      dsimp only [bankOnlineHandler, StateT.run]
      rw [htab]
      simp only [PMF.pure_bind, PMF.bind_const]
      exact ih entry.1 table (k + 1)
    | none =>
      rw [htab] at hlook
      rw [run_oracle_of_lookup_eq_none hlook]
      dsimp only [bankOnlineHandler, StateT.run]
      rw [htab]
      simp only [PMF.bind_bind]
      refine PMF.bind_congr_on_support _ _ _ fun val _ => ?_
      simp only [PMF.pure_bind]
      exact ih val ((q, (val, k)) :: table) (k + 1)

private def runBankedHandler {Val : Type} (d : P.G₀.Desc) (α : ZMod (P.G₀.order d))
    (proj : Val → P.G₀.Carrier d) (fallback : Val) (vals : List Val) :
    (q : List Bool ⊕ List Bool) →
      StateT (List (List Bool)) (StateT (List (List Bool × (Val × ℕ)) × ℕ) Id)
        (ForgerSpec (List Bool) (List Bool) (P.G₀.Carrier d) (P.G₀.Carrier d) q)
  | .inl m => fun s st =>
    let r := bankStepIndexed proj fallback vals m st
    ((α • r.1, m :: s), r.2)
  | .inr q => fun s st =>
    let r := bankStepIndexed proj fallback vals q st
    ((r.1, s), r.2)

/-- Run the typed BLS forger `prog` with `bankStepIndexed` over `vals : List Val` projected via
`proj : Val → P.G₀.Carrier d`. -/
private def runBankedForge {Val : Type} (d : P.G₀.Desc) (α : ZMod (P.G₀.order d))
    (proj : Val → P.G₀.Carrier d) (fallback : Val) (vals : List Val)
    (prog : OracleComp (ForgerSpec (List Bool) (List Bool) (P.G₀.Carrier d) (P.G₀.Carrier d))
      (List Bool × P.G₀.Carrier d))
    (signed : List (List Bool)) (table : List (List Bool × (Val × ℕ))) (count : ℕ) :
    ((List Bool × P.G₀.Carrier d) × List (List Bool)) ×
      (List (List Bool × (Val × ℕ)) × ℕ) :=
  ((OracleComp.interpret (P.runBankedHandler d α proj fallback vals) prog).run signed).run
    (table, count)

private theorem runBankedForge_query_inl {Val : Type} (d : P.G₀.Desc) (α : ZMod (P.G₀.order d))
    (proj : Val → P.G₀.Carrier d) (fallback : Val) (vals : List Val) (m : List Bool)
    (cont : P.G₀.Carrier d → OracleComp
      (ForgerSpec (List Bool) (List Bool) (P.G₀.Carrier d) (P.G₀.Carrier d))
      (List Bool × P.G₀.Carrier d))
    (signed : List (List Bool)) (table : List (List Bool × (Val × ℕ))) (count : ℕ) :
    runBankedForge P d α proj fallback vals (PFunctor.FreeM.liftBind (.inl m) cont)
        signed table count =
      let r := bankStepIndexed proj fallback vals m (table, count)
      runBankedForge P d α proj fallback vals (cont (α • r.1)) (m :: signed) r.2.1 r.2.2 := by
  change runBankedForge P d α proj fallback vals (OracleComp.query (.inl m) >>= cont)
    signed table count = _
  simp only [runBankedForge, StateT.run_bind, interpret_bind, interpret_query, runBankedHandler]
  rfl

private theorem runBankedForge_query_inr {Val : Type} (d : P.G₀.Desc) (α : ZMod (P.G₀.order d))
    (proj : Val → P.G₀.Carrier d) (fallback : Val) (vals : List Val) (x : List Bool)
    (cont : P.G₀.Carrier d → OracleComp
      (ForgerSpec (List Bool) (List Bool) (P.G₀.Carrier d) (P.G₀.Carrier d))
      (List Bool × P.G₀.Carrier d))
    (signed : List (List Bool)) (table : List (List Bool × (Val × ℕ))) (count : ℕ) :
    runBankedForge P d α proj fallback vals (PFunctor.FreeM.liftBind (.inr x) cont)
        signed table count =
      let r := bankStepIndexed proj fallback vals x (table, count)
      runBankedForge P d α proj fallback vals (cont r.1) signed r.2.1 r.2.2 := by
  change runBankedForge P d α proj fallback vals (OracleComp.query (.inr x) >>= cont)
    signed table count = _
  simp only [runBankedForge, StateT.run_bind, interpret_bind, interpret_query, runBankedHandler]
  rfl

private theorem runBankedForge_eq_interpret_blsRunCore_forge {Val : Type} (d : P.G₀.Desc)
    (α : ZMod (P.G₀.order d)) (proj : Val → P.G₀.Carrier d) (fallback : Val) (vals : List Val)
    (prog : OracleComp (ForgerSpec (List Bool) (List Bool) (P.G₀.Carrier d) (P.G₀.Carrier d))
      (List Bool × P.G₀.Carrier d))
    (signed : List (List Bool)) (table : List (List Bool × (Val × ℕ))) (count : ℕ) :
    (OracleComp.interpret (bankStepHandler proj fallback vals)
      ((OracleComp.interpret (P.blsCoreHandler d α) prog).run signed)).run (table, count) =
      runBankedForge P d α proj fallback vals prog signed table count := by
  induction prog using OracleComp.induction generalizing signed table count with
  | pure a => rfl
  | query_bind q cont ih =>
    change (OracleComp.interpret (bankStepHandler proj fallback vals)
      ((OracleComp.interpret (P.blsCoreHandler d α)
        (OracleComp.query q >>= cont)).run signed)).run (table, count) =
      runBankedForge P d α proj fallback vals (OracleComp.query q >>= cont) signed table count
    cases q <;> (
      simp only [runBankedForge, runBankedHandler, blsCoreHandler, interpret_bind,
        interpret_query, StateT.run_bind]
      exact ih _ _ _ _)

private theorem interpret_bankStep_blsRunCore {Val : Type} (d : P.G₀.Desc)
    (α : ZMod (P.G₀.order d)) (proj : Val → P.G₀.Carrier d) (fallback : Val) (vals : List Val)
    (prog : OracleComp (ForgerSpec (List Bool) (List Bool) (P.G₀.Carrier d) (P.G₀.Carrier d))
      (List Bool × P.G₀.Carrier d)) :
    (OracleComp.interpret (bankStepHandler proj fallback vals)
        (P.blsRunCore d α prog)).run ([], 0) =
      let f := P.runBankedForge d α proj fallback vals prog [] [] 0
      let last := bankStepIndexed proj fallback vals f.1.1.1 f.2
      ((f.1.1, f.1.2, last.1), last.2) := by
  simp only [blsRunCore, StateT.run_bind, interpret_bind, interpret_pure,
    StateT.run_pure, interpret_query, P.runBankedForge_eq_interpret_blsRunCore_forge]
  rfl

private theorem runBankedForge_bounds {Val : Type} (d : P.G₀.Desc) (α : ZMod (P.G₀.order d))
    (proj : Val → P.G₀.Carrier d) (fallback : Val) (vals : List Val)
    {prog : OracleComp (ForgerSpec (List Bool) (List Bool) (P.G₀.Carrier d) (P.G₀.Carrier d))
      (List Bool × P.G₀.Carrier d)}
    {Qs Qro : ℕ} (hs : prog.IsCostBounded signingCost Qs)
    (hh : prog.IsCostBounded hashCost Qro)
    (signed : List (List Bool)) (table : List (List Bool × (Val × ℕ))) (count : ℕ)
    (hidx : ∀ q v i, (q, (v, i)) ∈ table → i < count)
    (hnodup : ∀ q₁ v₁ q₂ v₂ i, table.lookup q₁ = some (v₁, i) →
      table.lookup q₂ = some (v₂, i) → q₁ = q₂)
    (hsigned : ∀ m ∈ signed, ∃ v i, table.lookup m = some (v, i) ∧ i < count) :
    let res := runBankedForge P d α proj fallback vals prog signed table count
    res.1.2.length ≤ signed.length + Qs ∧
      res.2.2 ≤ count + Qs + Qro ∧
      (∀ q v i, (q, (v, i)) ∈ res.2.1 → i < res.2.2) ∧
      (∀ q₁ v₁ q₂ v₂ i, res.2.1.lookup q₁ = some (v₁, i) →
        res.2.1.lookup q₂ = some (v₂, i) → q₁ = q₂) ∧
      (∀ q v i, table.lookup q = some (v, i) → res.2.1.lookup q = some (v, i)) ∧
      (∀ m ∈ res.1.2, ∃ v i, res.2.1.lookup m = some (v, i) ∧ i < res.2.2) ∧
      (∀ q ∈ signed, q ∈ res.1.2) := by
  induction prog generalizing Qs Qro signed table count with
  | pure a =>
    exact ⟨Nat.le_add_right _ _, by
        change count ≤ count + Qs + Qro
        omega,
      hidx, hnodup, fun _ _ _ h => h, hsigned, fun _ h => h⟩
  | liftBind q cont ih =>
    obtain ⟨hQs, hcontS⟩ := IsCostBounded.liftBind_iff.mp hs
    obtain ⟨hQro, hcontH⟩ := IsCostBounded.liftBind_iff.mp hh
    rcases q with m | x
    · dsimp only
      rw [P.runBankedForge_query_inl]
      change 1 ≤ Qs at hQs
      change ∀ r, OracleComp.IsCostBounded signingCost (cont r) (Qs - 1) at hcontS
      change ∀ r, OracleComp.IsCostBounded hashCost (cont r) (Qro - 0) at hcontH
      simp only [Nat.sub_zero] at hcontH
      set r := bankStepIndexed proj fallback vals m (table, count)
      obtain ⟨hidx', hnodup', hpres0, ⟨im, hmLook, _, hmLt⟩, hcnt⟩ :=
        bankStepIndexed_step_bounds proj fallback vals m table count hidx hnodup
      have hsigned' : ∀ q ∈ m :: signed, ∃ v i, r.2.1.lookup q = some (v, i) ∧ i < r.2.2 := by
        intro q hq
        rw [hcnt]
        rcases List.mem_cons.mp hq with rfl | hq
        · exact ⟨_, im, hmLook, hmLt⟩
        · obtain ⟨v, i, hv, hi⟩ := hsigned q hq
          exact ⟨v, i, hpres0 q v i hv, Nat.lt_succ_of_lt hi⟩
      obtain ⟨hlen, htot, hi1, hn1, hp1, hs1, hmono1⟩ :=
        ih (α • r.1) (hcontS (α • r.1)) (hcontH (α • r.1)) (m :: signed) r.2.1 r.2.2
          (hcnt ▸ hidx') hnodup' hsigned'
      refine ⟨le_trans hlen (by simp only [List.length_cons]; omega),
        le_trans htot (by rw [hcnt]; omega), hi1, hn1,
        fun q v i h => hp1 q v i (hpres0 q v i h), hs1,
        fun q hq => hmono1 q (List.mem_cons_of_mem _ hq)⟩
    · dsimp only
      rw [P.runBankedForge_query_inr]
      change ∀ r, OracleComp.IsCostBounded signingCost (cont r) (Qs - 0) at hcontS
      change 1 ≤ Qro at hQro
      change ∀ r, OracleComp.IsCostBounded hashCost (cont r) (Qro - 1) at hcontH
      simp only [Nat.sub_zero] at hcontS
      set r := bankStepIndexed proj fallback vals x (table, count)
      obtain ⟨hidx', hnodup', hpres0, _, hcnt⟩ :=
        bankStepIndexed_step_bounds proj fallback vals x table count hidx hnodup
      have hsigned' : ∀ q ∈ signed, ∃ v i, r.2.1.lookup q = some (v, i) ∧ i < r.2.2 := by
        intro q hq
        rw [hcnt]
        obtain ⟨v, i, hv, hi⟩ := hsigned q hq
        exact ⟨v, i, hpres0 q v i hv, Nat.lt_succ_of_lt hi⟩
      obtain ⟨hlen, htot, hi1, hn1, hp1, hs1, hmono1⟩ :=
        ih r.1 (hcontS r.1) (hcontH r.1) signed r.2.1 r.2.2 (hcnt ▸ hidx') hnodup' hsigned'
      exact ⟨hlen, le_trans htot (by rw [hcnt]; omega), hi1, hn1,
        fun q v i h => hp1 q v i (hpres0 q v i h), hs1, hmono1⟩

/-- Challenge element represented by a Coron sample `(c, ρ) : Bool × ZMod q` relative to
`v₀ : G₀`: `v₀ + ρ • g₀` when `c = true`, and `ρ • g₀` when `c = false`. -/
@[expose] def coronSampleElem (d : P.G₀.Desc) (v₀ : P.G₀.Carrier d)
    (x : Bool × ZMod (P.G₀.order d)) : P.G₀.Carrier d :=
  if x.1 then v₀ + x.2 • P.G₀.generator d else x.2 • P.G₀.generator d

@[simp] private theorem coronSampleElem_default (d : P.G₀.Desc) (v₀ : P.G₀.Carrier d) :
    P.coronSampleElem d v₀ (false, 0) = 0 := by
  simp [coronSampleElem]

/-- Presampled Coron co-CDH step: maintains `(table, aborted, count)` where each new hash point
draws the next `(c, ρ)` from `samples` (`(false, 0)` beyond `samples`). Hash queries return
`coronSampleElem d v₀ (c, ρ)`; signing queries return `ρ • u₀` when `c = false` and mark
`aborted = true` when `c = true`. -/
@[expose] noncomputable def blsBankedReductionStep (d : P.G₀.Desc) (u₀ v₀ : P.G₀.Carrier d)
    (samples : List (Bool × ZMod (P.G₀.order d))) :
    (q : List Bool ⊕ List Bool) →
      StateT (List (List Bool × ((Bool × ZMod (P.G₀.order d)) × ℕ)) × Bool × ℕ) Id
        (ForgerSpec (List Bool) (List Bool) (P.G₀.Carrier d) (P.G₀.Carrier d) q)
  | .inl m => fun (table, aborted, count) =>
    match table.lookup m with
    | some ((c, ρ), _) =>
      if c then (0, (table, true, count + 1))
      else (ρ • u₀, (table, aborted, count + 1))
    | none =>
      let val := samples.getD count (false, 0)
      let table' := (m, (val, count)) :: table
      if val.1 then (0, (table', true, count + 1))
      else (val.2 • u₀, (table', aborted, count + 1))
  | .inr q => fun (table, aborted, count) =>
    match table.lookup q with
    | some (sample, _) => (P.coronSampleElem d v₀ sample, (table, aborted, count + 1))
    | none =>
      let val := samples.getD count (false, 0)
      let table' := (q, (val, count)) :: table
      (P.coronSampleElem d v₀ val, (table', aborted, count + 1))

/-- Finish the banked Coron co-CDH reduction after the forger outputs `msig`. -/
@[expose] def blsBankedReductionFinish (d : P.G₀.Desc) (u₀ : P.G₀.Carrier d)
    (samples : List (Bool × ZMod (P.G₀.order d)))
    (msig : List Bool × P.G₀.Carrier d) :
    List (List Bool × ((Bool × ZMod (P.G₀.order d)) × ℕ)) × Bool × ℕ → P.G₀.Carrier d
  | (table, aborted, count) =>
    if aborted then 0
    else
      let (cstar, rhostar) :=
        match table.lookup msig.1 with
        | some (sample, _) => sample
        | none => samples.getD count (false, 0)
      if cstar then msig.2 - rhostar • u₀ else 0

/-- Distribution-level banked Coron co-CDH reduction for an arbitrary typed `Forger`. -/
@[expose] noncomputable def blsBankedReduction (d : P.G₀.Desc)
    (A : ROMSignature.Forger (P.G₁.Carrier d) (List Bool) (P.G₀.Carrier d) (List Bool)
      (P.G₀.Carrier d))
    (K : ℕ) (coin : PMF Bool)
    (u₀ : P.G₀.Carrier d) (u₁ : P.G₁.Carrier d) (v₀ : P.G₀.Carrier d) :
    PMF (P.G₀.Carrier d) :=
  A.coins.bind fun s =>
    (PMF.iid coin K).bind fun cs =>
      (PMF.iid (PMF.uniformOfFintype (ZMod (P.G₀.order d))) K).map fun rhos =>
        let samples := List.ofFn fun i : Fin K => (cs i, rhos i)
        let res := (OracleComp.interpret (P.blsBankedReductionStep d u₀ v₀ samples)
          (A.forge u₁ s)).run ([], false, 0)
        P.blsBankedReductionFinish d u₀ samples res.1 res.2

/-- Exact deterministic agreement between `runBankedForge` and `blsBankedReductionStep` whenever
every signed message ends up in `table_final` with coin `false`. -/
private theorem blsBankedReductionStep_eq_runBankedForge (d : P.G₀.Desc)
    (α β : ZMod (P.G₀.order d))
    (samples : List (Bool × ZMod (P.G₀.order d)))
    (prog : OracleComp (ForgerSpec (List Bool) (List Bool) (P.G₀.Carrier d) (P.G₀.Carrier d))
      (List Bool × P.G₀.Carrier d))
    {Qs Qro : ℕ} (hs : prog.IsCostBounded signingCost Qs)
    (hh : prog.IsCostBounded hashCost Qro)
    (signed0 : List (List Bool))
    (table0 : List (List Bool × ((Bool × ZMod (P.G₀.order d)) × ℕ))) (count0 : ℕ)
    (hidx0 : ∀ q v i, (q, (v, i)) ∈ table0 → i < count0)
    (hnodup0 : ∀ q₁ v₁ q₂ v₂ i, table0.lookup q₁ = some (v₁, i) →
      table0.lookup q₂ = some (v₂, i) → q₁ = q₂)
    (hsigned0 : ∀ m ∈ signed0, ∃ v i, table0.lookup m = some (v, i) ∧ i < count0)
    (havoid : ∀ m ∈ (runBankedForge P d α (P.coronSampleElem d (β • P.G₀.generator d))
        (false, 0) samples prog signed0 table0 count0).1.2,
      ∀ c ρ i, (runBankedForge P d α (P.coronSampleElem d (β • P.G₀.generator d))
        (false, 0) samples prog signed0 table0 count0).2.1.lookup m = some ((c, ρ), i) →
        c = false) :
    (OracleComp.interpret
        (P.blsBankedReductionStep d (α • P.G₀.generator d) (β • P.G₀.generator d) samples)
        prog).run (table0, false, count0) =
      let r := runBankedForge P d α (P.coronSampleElem d (β • P.G₀.generator d))
        (false, 0) samples prog signed0 table0 count0
      (r.1.1, (r.2.1, false, r.2.2)) := by
  let proj := P.coronSampleElem d (β • P.G₀.generator d)
  induction prog generalizing Qs Qro signed0 table0 count0 with
  | pure a => rfl
  | liftBind q cont ih =>
    obtain ⟨_, hcontS⟩ := IsCostBounded.liftBind_iff.mp hs
    obtain ⟨_, hcontH⟩ := IsCostBounded.liftBind_iff.mp hh
    change (OracleComp.interpret
      (P.blsBankedReductionStep d (α • P.G₀.generator d) (β • P.G₀.generator d) samples)
      (OracleComp.query q >>= cont)).run _ = _
    simp only [StateT.run_bind, interpret_bind, interpret_query]
    dsimp only [StateT.run]
    cases q with
    | inl m =>
      rw [P.runBankedForge_query_inl] at havoid ⊢
      let r := bankStepIndexed proj (false, 0) samples m (table0, count0)
      obtain ⟨hidx', hnodup', hpres0, ⟨im, hmLook, _, hmLt⟩, hcnt⟩ :=
        bankStepIndexed_step_bounds proj (false, 0) samples m table0 count0 hidx0 hnodup0
      have hsigned' : ∀ q ∈ m :: signed0, ∃ v i, r.2.1.lookup q = some (v, i) ∧ i < r.2.2 := by
        intro q hq
        rw [hcnt]
        rcases List.mem_cons.mp hq with rfl | hq
        · exact ⟨_, im, hmLook, hmLt⟩
        · obtain ⟨v, i, hv, hi⟩ := hsigned0 q hq
          exact ⟨v, i, hpres0 q v i hv, Nat.lt_succ_of_lt hi⟩
      obtain ⟨_, _, _, _, hpres1, _, hmono1⟩ := runBankedForge_bounds P d α proj (false, 0) samples
        (hcontS (α • r.1)) (hcontH (α • r.1)) (m :: signed0) r.2.1 r.2.2
        (hcnt ▸ hidx') hnodup' hsigned'
      have hm_final := hpres1 m _ im hmLook
      have hm_signed := hmono1 m List.mem_cons_self
      have hstep_red :
          P.blsBankedReductionStep d (α • P.G₀.generator d) (β • P.G₀.generator d) samples
            (.inl m) (table0, false, count0) = (α • r.1, (r.2.1, false, r.2.2)) := by
        dsimp only [blsBankedReductionStep, r, bankStepIndexed]
        cases hlook : table0.lookup m with
        | some e =>
          rcases e with ⟨⟨cm, ρm⟩, i'⟩
          simp only [hlook] at hm_final
          have hcm_false : cm = false := havoid m hm_signed cm ρm im hm_final
          simp [hcm_false, proj, coronSampleElem, smul_smul, mul_comm]
        | none =>
          simp only [hlook] at hm_final
          rcases hv : samples.getD count0 (false, 0) with ⟨cm, ρm⟩
          rw [hv] at hm_final
          have hcm_false : cm = false := havoid m hm_signed cm ρm im hm_final
          simp [hcm_false, proj, coronSampleElem, smul_smul, mul_comm]
      rw [hstep_red]
      exact ih (α • r.1) (hcontS (α • r.1)) (hcontH (α • r.1)) (m :: signed0) r.2.1 r.2.2
        (hcnt ▸ hidx') hnodup' hsigned' havoid
    | inr x =>
      rw [P.runBankedForge_query_inr] at havoid ⊢
      let r := bankStepIndexed proj (false, 0) samples x (table0, count0)
      obtain ⟨hidx', hnodup', hpres0, _, hcnt⟩ :=
        bankStepIndexed_step_bounds proj (false, 0) samples x table0 count0 hidx0 hnodup0
      have hsigned' : ∀ q ∈ signed0, ∃ v i, r.2.1.lookup q = some (v, i) ∧ i < r.2.2 := by
        intro q hq
        rw [hcnt]
        obtain ⟨v, i, hv, hi⟩ := hsigned0 q hq
        exact ⟨v, i, hpres0 q v i hv, Nat.lt_succ_of_lt hi⟩
      have hstep_red :
          P.blsBankedReductionStep d (α • P.G₀.generator d) (β • P.G₀.generator d) samples
            (.inr x) (table0, false, count0) = (r.1, (r.2.1, false, r.2.2)) := by
        dsimp only [blsBankedReductionStep, r, bankStepIndexed]
        cases table0.lookup x <;> rfl
      rw [hstep_red]
      exact ih r.1 (hcontS r.1) (hcontH r.1) signed0 r.2.1 r.2.2
        (hcnt ▸ hidx') hnodup' hsigned' havoid

/-- Pushing `PMF.uniformOfFintype (ZMod q)` through `coronSampleElem` yields
`PMF.uniformOfFintype (P.G₀.Carrier d)` regardless of `c` and `v₀`. -/
private theorem map_coronSampleElem_uniform (d : P.G₀.Desc) [Fintype (P.G₀.Carrier d)]
    (v₀ : P.G₀.Carrier d) (c : Bool) :
    (PMF.uniformOfFintype (ZMod (P.G₀.order d))).map (fun ρ => P.coronSampleElem d v₀ (c, ρ)) =
      PMF.uniformOfFintype (P.G₀.Carrier d) := by
  have hbi : Function.Bijective fun ρ => P.coronSampleElem d v₀ (c, ρ) := by
    cases c
    · simpa [coronSampleElem] using P.G₀.smul_generator_bijective d
    · simpa [coronSampleElem] using
        (Equiv.addLeft v₀).bijective.comp (P.G₀.smul_generator_bijective d)
  let e := Equiv.ofBijective _ hbi
  ext h
  rw [PMF.map_apply, tsum_eq_single (e.symm h)]
  · simp only [show P.coronSampleElem d v₀ (c, e.symm h) = h from e.apply_symm_apply h,
      ↓reduceIte, PMF.uniformOfFintype_apply, ZMod.card]
    exact congrArg (fun k : ℕ => (k : ℝ≥0∞)⁻¹)
      ((P.G₀.card_carrier d).symm.trans Nat.card_eq_fintype_card)
  · intro ρ hρ
    have hne : h ≠ P.coronSampleElem d v₀ (c, ρ) := fun eq => hρ (e.symm_apply_eq.mpr eq).symm
    simp [hne]

private theorem bankStepIndexed_interpret_mem_val {Val H γ : Type} (proj : Val → H)
    (fallback : Val) (vals : List Val) (p : OracleComp (fun _ : List Bool => H) γ)
    (table : List (List Bool × (Val × ℕ))) (count : ℕ)
    (htable : ∀ q v i, (q, (v, i)) ∈ table → v = vals.getD i fallback) :
    ∀ q v i, (q, (v, i)) ∈ ((OracleComp.interpret (bankStepHandler proj fallback vals) p).run
        (table, count)).2.1 →
      v = vals.getD i fallback := by
  induction p using OracleComp.induction generalizing table count with
  | pure _ => exact htable
  | query_bind x cont ih =>
    intro q v i h
    change (q, (v, i)) ∈ ((OracleComp.interpret (bankStepHandler proj fallback vals)
      (OracleComp.query x >>= cont)).run (table, count)).2.1 at h
    simp only [StateT.run_bind, interpret_bind, interpret_query] at h
    dsimp only [bankStepHandler, StateT.run, bankStepIndexed] at h
    cases hlook : table.lookup x with
    | some entry =>
      rw [hlook] at h
      exact ih (proj entry.1) table (count + 1) htable q v i h
    | none =>
      rw [hlook] at h
      refine ih _ ((x, (vals.getD count fallback, count)) :: table) (count + 1) ?_ q v i h
      rintro q' v' i' hmem
      rcases List.mem_cons.mp hmem with ⟨_, rfl, rfl⟩ | htail
      · rfl
      · exact htable q' v' i' htail

private theorem mul_bind_apply_le {α β : Type} (c : ℝ≥0∞) (p : PMF α) (f g : α → PMF β) (y : β)
    (h : ∀ x, c * f x y ≤ g x y) :
    c * (p.bind f) y ≤ (p.bind g) y := by
  rw [PMF.bind_apply, PMF.bind_apply, ← ENNReal.tsum_mul_left]
  refine tsum_le_tsum fun x => ?_
  rw [← mul_assoc, mul_comm c, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h x) zero_le

/-- **Quantitative Coron bound for typed BLS (`blsTypedROMScheme`)**: for any typed call-bounded
forger `A` (`Qs` signing calls, `Qro` hash calls) and any Bernoulli coin `coin` with
`(coin true).toReal = a⁻¹` and `Qs + 1 ≤ a`, the EUF-CMA success probability is at most
`2.72 * a` times the co-CDH success probability of `P.blsBankedReduction d A (Qs + Qro + 1) coin`.
-/
theorem succProbability_eufCmaGame_blsTypedROMScheme_le_of_banked
    (d : P.G₀.Desc) [Fintype (P.G₀.Carrier d)]
    (A : ROMSignature.Forger (P.G₁.Carrier d) (List Bool) (P.G₀.Carrier d) (List Bool)
      (P.G₀.Carrier d))
    {Qs Qro : ℕ} (hA : A.CallBounded Qs Qro)
    (coin : PMF Bool) {a : ℝ} (hcoin : (coin true).toReal = a⁻¹)
    (ha : (Qs + 1 : ℝ) ≤ a) :
    (Game.succProbability (ROMSignature.eufCmaGame (P.blsTypedROMScheme d) A) : ℝ) ≤
      2.72 * a * (Game.succProbability (do
        let α ← PMF.uniformOfFintype (ZMod (P.G₀.order d))
        let β ← PMF.uniformOfFintype (ZMod (P.G₀.order d))
        let z ← P.blsBankedReduction d A (Qs + Qro + 1) coin
          (α • P.G₀.generator d) (α • P.G₁.generator d) (β • P.G₀.generator d)
        return decide (z = (α * β) • P.G₀.generator d)) : ℝ) := by
  let K := Qs + Qro + 1
  have ha_pos : 0 < a := by linarith [Nat.cast_nonneg (α := ℝ) Qs]
  let resFn (α : ZMod (P.G₀.order d)) (s : A.Coins) (hs : Fin K → P.G₀.Carrier d) :=
    (OracleComp.interpret (bankStepHandler id 0 (List.ofFn hs))
      (P.blsRunCore d α (A.forge (α • P.G₁.generator d) s))).run ([], 0)
  let wonPred (α : ZMod (P.G₀.order d))
      (x : (List Bool × P.G₀.Carrier d) × List (List Bool) × P.G₀.Carrier d) : Bool :=
    decide (P.pair d x.2.2 (α • P.G₁.generator d) =
      P.pair d x.1.2 (P.G₁.generator d)) && !(x.2.1.contains x.1.1)
  let wonFn α s hs := wonPred α (resFn α s hs).1
  let RFn α s hs : Finset (Fin K) :=
    ((resFn α s hs).1.2.1.filterMap fun m =>
      ((resFn α s hs).2.1.lookup m).bind
        fun e => if h : e.2 < K then some ⟨e.2, h⟩ else none).toFinset
  let idxFn α s hs : Fin K :=
    match (resFn α s hs).2.1.lookup (resFn α s hs).1.1.1 with
    | some e => if h : e.2 < K then ⟨e.2, h⟩ else ⟨0, Nat.succ_pos _⟩
    | none => ⟨0, Nat.succ_pos _⟩
  let E_R : Game := do
    let α ← PMF.uniformOfFintype (ZMod (P.G₀.order d))
    let β ← PMF.uniformOfFintype (ZMod (P.G₀.order d))
    let z ← P.blsBankedReduction d A K coin
      (α • P.G₀.generator d) (α • P.G₁.generator d) (β • P.G₀.generator d)
    return decide (z = (α * β) • P.G₀.generator d)
  -- Step 1: Express `eufCmaGame` via `blsRunCore` presampled with `K` uniform `G₀` elements.
  have heuf_eq :
      ROMSignature.eufCmaGame (P.blsTypedROMScheme d) A =
        (PMF.uniformOfFintype (ZMod (P.G₀.order d))).bind fun α =>
          A.coins.bind fun s =>
            (PMF.iid (PMF.uniformOfFintype (P.G₀.Carrier d)) K).map (wonFn α s) := by
    unfold ROMSignature.eufCmaGame
    change ((PMF.uniformOfFintype (ZMod (P.G₀.order d))).map
        fun α => (α • P.G₁.generator d, α)).bind _ = _
    rw [PMF.bind_map]
    refine PMF.bind_congr_on_support _ _ _ fun α _ => ?_
    simp only [Function.comp_apply, PMF.monad_bind_eq_bind]
    refine PMF.bind_congr_on_support _ _ _ fun s _ => ?_
    have hcontainsMsg : ∀ msgs msg,
        @List.contains (List Bool) List.instBEq msgs msg =
          @List.contains (List Bool) instBEqOfDecidableEq msgs msg :=
      @list_contains_beq_congr (List Bool) List.instBEq _ instBEqOfDecidableEq _
    simp only [← hcontainsMsg]
    have hcore := P.run_interpret_blsRunCore d α (A.forge (α • P.G₁.generator d) s) []
    simp only [PMF.monad_bind_eq_bind] at hcore
    rw [← hcore]
    let step : P.G₀.Carrier d → List Bool →
        List (List Bool × (P.G₀.Carrier d × ℕ)) × ℕ →
        PMF (P.G₀.Carrier d × (List (List Bool × (P.G₀.Carrier d × ℕ)) × ℕ)) :=
      fun val q st => match st.1.lookup q with
        | some entry => PMF.pure (entry.1, (st.1, st.2 + 1))
        | none => PMF.pure (val, ((q, (val, st.2)) :: st.1, st.2 + 1))
    have hpre := (P.isQueryBounded_blsRunCore d α
      (hA (α • P.G₁.generator d) s).1 (hA (α • P.G₁.generator d) s).2).run_interpret_presample
        (PMF.uniformOfFintype (P.G₀.Carrier d)) (0 : P.G₀.Carrier d) step ([], 0)
    have honline := P.interpret_online_bankStep_eq_oracle d
      (P.blsRunCore d α (A.forge (α • P.G₁.generator d) s)) [] 0
    dsimp only [List.map] at honline
    have hmap :
        ((interpret (oracle (P.G₀.Carrier d))
          (P.blsRunCore d α (A.forge (α • P.G₁.generator d) s))).run []).map
            (wonPred α ∘ Prod.fst) =
        ((PMF.iid (PMF.uniformOfFintype (P.G₀.Carrier d)) K).map List.ofFn).bind fun values =>
          ((interpret (withSampleList (spec := fun _ : List Bool => P.G₀.Carrier d) (m := PMF)
              (0 : P.G₀.Carrier d) step)
            (P.blsRunCore d α (A.forge (α • P.G₁.generator d) s))).run (([], 0), values)).map
              (wonPred α ∘ Prod.fst) := by
      have h1 := congrArg (PMF.map (wonPred α ∘ Prod.fst)) honline
      rw [PMF.map_comp] at h1
      rw [← h1]
      have hbo : P.bankOnlineHandler d = fun (q : List Bool)
          (st : List (List Bool × (P.G₀.Carrier d × ℕ)) × ℕ) =>
          (PMF.uniformOfFintype (P.G₀.Carrier d)).bind fun val => step val q st := rfl
      rw [hbo, ← hpre, PMF.map_bind]
      congr 1 with values : 1
      rw [PMF.map_comp]; rfl
    change ((interpret (oracle (P.G₀.Carrier d))
      (P.blsRunCore d α (A.forge (α • P.G₁.generator d) s))).run []).map (wonPred α ∘ Prod.fst) = _
    rw [hmap, PMF.bind_map]
    refine PMF.bind_congr_on_support _ _ _ fun hs _ => ?_
    have hdet := bankStepIndexed_eq_withSampleList (id : P.G₀.Carrier d → _) 0 (List.ofFn hs)
      (P.blsRunCore d α (A.forge (α • P.G₁.generator d) s)) [] 0
    simp only [List.drop_zero, id_eq] at hdet
    have hmap2 := congrArg (PMF.map (wonPred α ∘ Prod.fst)) hdet
    rw [PMF.pure_map, PMF.map_comp] at hmap2
    dsimp only [Function.comp_def, wonFn] at hmap2 ⊢
    convert hmap2.symm
    rename_i _ q st
    dsimp only [step]
    cases List.lookup q st.1 <;> rfl
  -- Step 2: Pointwise recovery when `(won = true ∧ cs idxStar = true ∧ ∀ i ∈ R, cs i = false)`.
  have hpointwise (α β : ZMod (P.G₀.order d)) (s : A.Coins)
      (cs : Fin K → Bool) (rhos : Fin K → ZMod (P.G₀.order d)) :
      let samples := List.ofFn fun i : Fin K => (cs i, rhos i)
      let hs : Fin K → P.G₀.Carrier d :=
        fun i => P.coronSampleElem d (β • P.G₀.generator d) (cs i, rhos i)
      (wonFn α s hs = true ∧ cs (idxFn α s hs) = true ∧ ∀ i ∈ RFn α s hs, cs i = false) →
        P.blsBankedReductionFinish d (α • P.G₀.generator d) samples
          ((OracleComp.interpret (P.blsBankedReductionStep d (α • P.G₀.generator d)
              (β • P.G₀.generator d) samples)
            (A.forge (α • P.G₁.generator d) s)).run ([], false, 0)).1
          ((OracleComp.interpret (P.blsBankedReductionStep d (α • P.G₀.generator d)
              (β • P.G₀.generator d) samples)
            (A.forge (α • P.G₁.generator d) s)).run ([], false, 0)).2 =
          (α * β) • P.G₀.generator d := by
    intro samples hs ⟨hwon, hcsStar, hcsR⟩
    let proj := P.coronSampleElem d (β • P.G₀.generator d)
    have hhs : List.ofFn hs = samples.map proj := by
      simp [samples, hs, List.map_ofFn, proj, Function.comp_def]
    -- Relate `bankStepHandler id 0 (samples.map proj)` to `bankStepHandler proj (false, 0)`.
    have hrel_step :
        ∀ (p : OracleComp (fun _ : List Bool => P.G₀.Carrier d)
            ((List Bool × P.G₀.Carrier d) × List (List Bool) × P.G₀.Carrier d)) t cnt,
        let rr := (OracleComp.interpret (bankStepHandler id 0 (samples.map proj)) p).run
            (t.map (fun (k, (v, i)) => (k, (proj v, i))), cnt)
        let rs := (OracleComp.interpret (bankStepHandler proj (false, 0) samples) p).run
            (t, cnt)
        rr.1 = rs.1 ∧ rr.2.1 = rs.2.1.map (fun (k, (v, i)) => (k, (proj v, i))) ∧
          rr.2.2 = rs.2.2 := by
      intro p
      induction p using OracleComp.induction with
      | pure a => intro t cnt; exact ⟨rfl, rfl, rfl⟩
      | query_bind q cont ih =>
        intro t cnt
        have hget : (samples.map proj).getD cnt 0 = proj (samples.getD cnt (false, 0)) := by
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
          cases samples[cnt]? <;> simp [proj]
        have hbind : PFunctor.FreeM.bind
            (OracleComp.query (spec := fun _ : List Bool => P.G₀.Carrier d) q) cont =
            (OracleComp.query q >>= cont) := rfl
        rw [hbind]
        simp only [StateT.run_bind, interpret_bind, interpret_query]
        dsimp only [StateT.run, bankStepHandler, bankStepIndexed, id_eq]
        rw [list_lookup_map_snd (fun e => (proj e.1, e.2)) t q]
        cases t.lookup q with
        | some e => exact ih (proj e.1) t (cnt + 1)
        | none =>
          simp only [Option.map_none, hget]
          exact ih (proj (samples.getD cnt (false, 0)))
            ((q, (samples.getD cnt (false, 0), cnt)) :: t) (cnt + 1)
    -- Relate `res` (with `id, hs`) to `(f1, last)`.
    let f1 := P.runBankedForge d α proj (false, 0) samples
      (A.forge (α • P.G₁.generator d) s) [] [] 0
    have hcore_eq := P.interpret_bankStep_blsRunCore d α proj (false, 0) samples
      (A.forge (α • P.G₁.generator d) s)
    have hbounds := P.runBankedForge_bounds d α proj (false, 0) samples
      (hA (α • P.G₁.generator d) s).1 (hA (α • P.G₁.generator d) s).2 [] [] 0
      (fun _ _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h) (fun _ h => by cases h)
    have hstep1 := bankStepIndexed_step_bounds proj (false, 0) samples f1.1.1.1 f1.2.1 f1.2.2
      hbounds.2.2.1 hbounds.2.2.2.1
    have hmem_val : ∀ q v i,
        (q, (v, i)) ∈ (bankStepIndexed proj (false, 0) samples f1.1.1.1 f1.2).2.1 →
          v = samples.getD i (false, 0) := by
      have hall := bankStepIndexed_interpret_mem_val proj (false, 0) samples
        (P.blsRunCore d α (A.forge (α • P.G₁.generator d) s)) [] 0 (fun _ _ _ h => by cases h)
      intro q v i hmem
      exact hall q v i (hcore_eq.symm ▸ hmem)
    have hget_samples : ∀ {i : ℕ} (hi : i < K),
        samples.getD i (false, 0) = (cs ⟨i, hi⟩, rhos ⟨i, hi⟩) := fun hi => by
      dsimp only [samples]
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp [hi]
    have hr := hrel_step (P.blsRunCore d α (A.forge (α • P.G₁.generator d) s)) [] 0
    simp only [List.map_nil] at hr
    rw [← hhs, hcore_eq] at hr
    obtain ⟨hr1, hr2, _⟩ := hr
    have hf1_lt : f1.2.2 < K := by have h : f1.2.2 ≤ 0 + Qs + Qro := hbounds.2.1; omega
    -- Show every signed message in `f1` has slot coin `false`.
    have havoid : ∀ m ∈ f1.1.2, ∀ c ρ i, f1.2.1.lookup m = some ((c, ρ), i) → c = false := by
      intro m hm c ρ i hmLook
      obtain ⟨_, i', hlook', hi'⟩ := hbounds.2.2.2.2.2.1 m hm
      rw [hmLook, Option.some.injEq] at hlook'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hlook'
      have hiK : i < K := by omega
      have hpres_last := hstep1.2.2.1 m (c, ρ) i hmLook
      have hres_look : (resFn α s hs).2.1.lookup m = some (proj (c, ρ), i) := by
        dsimp only [resFn]
        rw [hr2]
        exact (list_lookup_map_snd (fun e : (Bool × ZMod (P.G₀.order d)) × ℕ => (proj e.1, e.2))
          _ m).trans (by
            dsimp only
            rw [hpres_last]
            rfl)
      have hi_mem : ⟨i, hiK⟩ ∈ RFn α s hs :=
        List.mem_toFinset.mpr (List.mem_filterMap.mpr ⟨m, hr1 ▸ hm, by simp [hres_look, hiK]⟩)
      have hi_eq := (hmem_val m (c, ρ) i (List.mem_of_lookup_eq_some hpres_last)).trans
        (hget_samples hiK)
      exact (Prod.mk.inj hi_eq).1.trans (hcsR ⟨i, hiK⟩ hi_mem)
    rw [P.blsBankedReductionStep_eq_runBankedForge d α β samples
      (A.forge (α • P.G₁.generator d) s) (hA (α • P.G₁.generator d) s).1
      (hA (α • P.G₁.generator d) s).2 [] [] 0
      (fun _ _ _ h => by cases h)
      (fun _ _ _ _ _ h => by cases h)
      (fun _ h => by cases h)
      havoid]
    simp only [blsBankedReductionFinish, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨iStar, hlast_look, hlast_val, hiStar_lt⟩ := hstep1.2.2.2.1
    have hiK : iStar < K := by omega
    have hres_look : (resFn α s hs).2.1.lookup (resFn α s hs).1.1.1 =
        some (proj (match f1.2.1.lookup f1.1.1.1 with
          | some (v, _) => v | none => samples.getD f1.2.2 (false, 0)), iStar) := by
      dsimp only [resFn]
      rw [hr1, hr2]
      exact (list_lookup_map_snd (fun e : (Bool × ZMod (P.G₀.order d)) × ℕ => (proj e.1, e.2))
        _ _).trans (by
          dsimp only
          rw [hlast_look]
          cases f1.2.1.lookup f1.1.1.1 <;> rfl)
    have hidx_eq : idxFn α s hs = ⟨iStar, hiK⟩ := by
      dsimp only [idxFn]
      rw [hres_look]
      simp [hiK]
    have hstar_eq : (match f1.2.1.lookup f1.1.1.1 with
        | some (sample, _) => sample | none => samples.getD f1.2.2 (false, 0)) =
        (true, rhos (idxFn α s hs)) := by
      have hval := (hmem_val _ _ _ (List.mem_of_lookup_eq_some hlast_look)).trans
        (hget_samples hiK)
      rw [← hidx_eq, hcsStar] at hval
      cases hfl : f1.2.1.lookup f1.1.1.1 <;> simpa only [hfl] using hval
    rw [hstar_eq]
    simp only [↓reduceIte]
    have hpair_won : P.pair d (resFn α s hs).1.2.2 (α • P.G₁.generator d) =
        P.pair d f1.1.1.2 (P.G₁.generator d) := by
      have hwon' := ((Bool.and_eq_true _ _).mp hwon).1
      rw [show (resFn α s hs).1.1.2 = f1.1.1.2 from congrArg (fun x => x.1.2) hr1] at hwon'
      exact decide_eq_true_eq.mp hwon'
    have hsig_eq : f1.1.1.2 = α • (resFn α s hs).1.2.2 :=
      (P.pair_right_generator_injective d
        ((by simp only [map_smul, LinearMap.smul_apply] :
          P.pair d (α • (resFn α s hs).1.2.2) (P.G₁.generator d) =
            P.pair d (resFn α s hs).1.2.2 (α • P.G₁.generator d)).trans hpair_won)).symm
    have hlast_h : (resFn α s hs).1.2.2 =
        β • P.G₀.generator d + rhos (idxFn α s hs) • P.G₀.generator d := by
      dsimp only [resFn]
      rw [hr1]
      dsimp only
      rw [hlast_val]
      cases hfl : f1.2.1.lookup f1.1.1.1 <;> (
        simp only [hfl] at hstar_eq ⊢
        rw [hstar_eq]
        rfl)
    rw [hsig_eq, hlast_h, smul_add, ← mul_smul, smul_comm α (rhos _), add_sub_cancel_right]
  -- Step 3: Bound `won` from `one_div_le_toOuterMeasure_iid_marked`, then decouple and transfer.
  have hmarked (α : ZMod (P.G₀.order d)) (s : A.Coins) (hs : Fin K → P.G₀.Carrier d)
      (hwon : wonFn α s hs = true) :
      idxFn α s hs ∉ RFn α s hs ∧ ((RFn α s hs).card : ℝ) + 1 ≤ a := by
    let f0 := P.runBankedForge d α id 0 (List.ofFn hs)
      (A.forge (α • P.G₁.generator d) s) [] [] 0
    have hcore0 := P.interpret_bankStep_blsRunCore d α id 0 (List.ofFn hs)
      (A.forge (α • P.G₁.generator d) s)
    have hbounds0 := P.runBankedForge_bounds d α id 0 (List.ofFn hs)
      (hA (α • P.G₁.generator d) s).1 (hA (α • P.G₁.generator d) s).2 [] [] 0
      (fun _ _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h) (fun _ h => by cases h)
    have hstep0 := bankStepIndexed_step_bounds id 0 (List.ofFn hs) f0.1.1.1 f0.2.1 f0.2.2
      hbounds0.2.2.1 hbounds0.2.2.2.1
    have hf0_lt : f0.2.2 < K := by have h : f0.2.2 ≤ 0 + Qs + Qro := hbounds0.2.1; omega
    have hnotMem : f0.1.1.1 ∉ f0.1.2 := by
      have hc := ((Bool.and_eq_true _ _).mp hwon).2
      dsimp only [wonFn, wonPred, resFn] at hc
      rw [hcore0] at hc
      intro hm
      dsimp only at hc
      cases hc' : f0.1.2.contains f0.1.1.1
      · exact Bool.false_ne_true (hc'.symm.trans (List.contains_iff_mem.mpr hm))
      · rw [hc'] at hc; cases hc
    obtain ⟨iStar, hlookStar, _, hiStar_lt⟩ := hstep0.2.2.2.1
    have hiK : iStar < K := by omega
    have hidx0 : idxFn α s hs = ⟨iStar, hiK⟩ := by
      dsimp only [idxFn, resFn]
      rw [hcore0]
      dsimp only
      rw [hlookStar]
      simp only [hiK, ↓reduceDIte]
    refine ⟨?_, ?_⟩
    · intro hmem
      dsimp only [RFn, resFn] at hmem
      rw [hcore0] at hmem
      dsimp only at hmem
      obtain ⟨m, hm_signed, hm_eq⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp hmem)
      change Option.bind ((bankStepIndexed id 0 (List.ofFn hs) f0.1.1.1 f0.2).2.1.lookup m) _ = _
        at hm_eq
      cases hml : (bankStepIndexed id 0 (List.ofFn hs) f0.1.1.1 f0.2).2.1.lookup m with
      | none =>
        rw [hml] at hm_eq
        cases hm_eq
      | some em =>
        simp only [hml, Option.bind_some] at hm_eq
        split_ifs at hm_eq with hmK
        have hm_idx : em.2 = iStar := by
          have := congrArg Fin.val (Option.some.inj hm_eq)
          simpa only [hidx0] using this
        exact hnotMem (hstep0.2.1 m em.1 f0.1.1.1 _ iStar (hm_idx ▸ hml) hlookStar ▸ hm_signed)
    · have hcard_le : (RFn α s hs).card ≤ Qs := by
        dsimp only [RFn, resFn]
        rw [hcore0]
        refine (List.toFinset_card_le _).trans ((List.length_filterMap_le _ _).trans ?_)
        have h : f0.1.2.length ≤ [].length + Qs := hbounds0.1
        simpa only [List.length_nil, Nat.zero_add] using h
      exact le_trans (by exact_mod_cast Nat.succ_le_succ hcard_le) ha
  have hterm (α : ZMod (P.G₀.order d)) (s : A.Coins) (hs : Fin K → P.G₀.Carrier d) :
      ENNReal.ofReal (1 / (2.72 * a)) * (if wonFn α s hs = true then 1 else 0) ≤
        ((PMF.iid coin K).map fun cs =>
          wonFn α s hs && decide (cs (idxFn α s hs) = true ∧ ∀ i ∈ RFn α s hs, cs i = false))
            true := by
    by_cases hwon : wonFn α s hs = true
    · obtain ⟨hnot, hcard⟩ := hmarked α s hs hwon
      have hcoin_le := Cslib.Probability.PMF.one_div_le_toOuterMeasure_iid_marked coin hcoin
        (RFn α s hs) hcard hnot
      have heq_om :
          ((PMF.iid coin K).map fun cs =>
            wonFn α s hs && decide (cs (idxFn α s hs) = true ∧ ∀ i ∈ RFn α s hs, cs i = false))
              true =
            (PMF.iid coin K).toOuterMeasure
              {cs | cs (idxFn α s hs) = true ∧ ∀ i ∈ RFn α s hs, cs i = false} := by
        rw [PMF.map_apply, PMF.toOuterMeasure_apply]
        refine tsum_congr fun cs => ?_
        by_cases hcs : cs (idxFn α s hs) = true ∧ ∀ i ∈ RFn α s hs, cs i = false
        · rw [Set.indicator_of_mem hcs]
          simp only [hwon, Bool.true_and, decide_eq_true hcs, ↓reduceIte]
        · rw [Set.indicator_of_notMem hcs]
          simp only [hwon, Bool.true_and, decide_eq_false hcs, Bool.true_eq_false, ↓reduceIte]
      calc
        ENNReal.ofReal (1 / (2.72 * a)) * (if wonFn α s hs = true then 1 else 0) =
            ENNReal.ofReal (1 / (2.72 * a)) := by
          simp only [hwon, ↓reduceIte, mul_one]
        _ ≤ (PMF.iid coin K).toOuterMeasure
              {cs | cs (idxFn α s hs) = true ∧ ∀ i ∈ RFn α s hs, cs i = false} :=
          ENNReal.ofReal_le_of_le_toReal hcoin_le
        _ = _ := heq_om.symm
    · simp [hwon]
  have hmap_bind : ∀ {α β : Type} (p : PMF α) (f : α → β),
      p.map f = p.bind fun x => PMF.pure (f x) := fun _ _ => rfl
  have hinner_hs (α β : ZMod (P.G₀.order d)) (s : A.Coins) :
      ENNReal.ofReal (1 / (2.72 * a)) *
          ((PMF.iid (PMF.uniformOfFintype (P.G₀.Carrier d)) K).map (wonFn α s)) true ≤
        ((PMF.iid coin K).bind fun cs =>
          (PMF.iid (PMF.uniformOfFintype (ZMod (P.G₀.order d))) K).map fun rhos =>
            let samples := List.ofFn fun i : Fin K => (cs i, rhos i)
            let res := (OracleComp.interpret (P.blsBankedReductionStep d
              (α • P.G₀.generator d) (β • P.G₀.generator d) samples)
                (A.forge (α • P.G₁.generator d) s)).run ([], false, 0)
            decide (P.blsBankedReductionFinish d (α • P.G₀.generator d) samples res.1 res.2 =
              (α * β) • P.G₀.generator d)) true := by
    have hmap_left :
        ENNReal.ofReal (1 / (2.72 * a)) *
            ((PMF.iid (PMF.uniformOfFintype (P.G₀.Carrier d)) K).map (wonFn α s)) true ≤
          ((PMF.iid (PMF.uniformOfFintype (P.G₀.Carrier d)) K).bind fun hs =>
            (PMF.iid coin K).map fun cs =>
              wonFn α s hs &&
                decide (cs (idxFn α s hs) = true ∧ ∀ i ∈ RFn α s hs, cs i = false)) true := by
      rw [PMF.map_apply, PMF.bind_apply, ← ENNReal.tsum_mul_left]
      refine tsum_le_tsum fun hs => ?_
      cases hwon : wonFn α s hs
      · simp
      · have h := mul_le_mul_of_nonneg_left (hterm α s hs)
          (zero_le : 0 ≤ (PMF.iid (PMF.uniformOfFintype (P.G₀.Carrier d)) K) hs)
        simp only [hwon, ↓reduceIte, mul_one] at h
        simpa only [hwon, ↓reduceIte, mul_comm (ENNReal.ofReal _)] using h
    have hcomm :
        ((PMF.iid (PMF.uniformOfFintype (P.G₀.Carrier d)) K).bind fun hs =>
          (PMF.iid coin K).map fun cs =>
            wonFn α s hs &&
              decide (cs (idxFn α s hs) = true ∧ ∀ i ∈ RFn α s hs, cs i = false)) =
        ((PMF.iid coin K).bind fun cs =>
          (PMF.iid (PMF.uniformOfFintype (P.G₀.Carrier d)) K).map fun hs =>
            wonFn α s hs &&
              decide (cs (idxFn α s hs) = true ∧ ∀ i ∈ RFn α s hs, cs i = false)) := by
      simp_rw [hmap_bind]
      exact PMF.bind_comm _ _ _
    refine hmap_left.trans ?_
    rw [hcomm, PMF.bind_apply, PMF.bind_apply]
    refine tsum_le_tsum fun cs => mul_le_mul_of_nonneg_left ?_ zero_le
    have hiid_proj :
        (PMF.iid (PMF.uniformOfFintype (ZMod (P.G₀.order d))) K).map
            (fun rhos i => P.coronSampleElem d (β • P.G₀.generator d) (cs i, rhos i)) =
          PMF.iid (PMF.uniformOfFintype (P.G₀.Carrier d)) K := by
      rw [← PMF.piFin_const,
        ← PMF.piFin_map (fun _ : Fin K => PMF.uniformOfFintype (ZMod (P.G₀.order d)))
          (fun j ρ => P.coronSampleElem d (β • P.G₀.generator d) (cs j, ρ))]
      simp only [P.map_coronSampleElem_uniform, PMF.piFin_const]
    rw [← hiid_proj, PMF.map_comp, PMF.map_apply, PMF.map_apply]
    refine tsum_le_tsum fun rhos => ?_
    by_cases hpred : (wonFn α s
        (fun i => P.coronSampleElem d (β • P.G₀.generator d) (cs i, rhos i)) &&
        decide (cs (idxFn α s
          (fun i => P.coronSampleElem d (β • P.G₀.generator d) (cs i, rhos i))) = true ∧
          ∀ i ∈ RFn α s (fun i => P.coronSampleElem d (β • P.G₀.generator d) (cs i, rhos i)),
            cs i = false)) = true
    · simp only [Function.comp_apply, hpred, ↓reduceIte]
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hpred
      simp only [decide_eq_true_eq.mpr (hpointwise α β s cs rhos ⟨hpred.1, hpred.2.1, hpred.2.2⟩),
        ↓reduceIte, le_refl]
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hpred
      simp [hpred]
  have henn :
      ENNReal.ofReal (1 / (2.72 * a)) *
          (ROMSignature.eufCmaGame (P.blsTypedROMScheme d) A) true ≤
        E_R true := by
    rw [heuf_eq]
    have hconst :
        ((PMF.uniformOfFintype (ZMod (P.G₀.order d))).bind fun α =>
          A.coins.bind fun s =>
            (PMF.iid (PMF.uniformOfFintype (P.G₀.Carrier d)) K).map (wonFn α s)) =
        (PMF.uniformOfFintype (ZMod (P.G₀.order d))).bind fun α =>
          (PMF.uniformOfFintype (ZMod (P.G₀.order d))).bind fun _ =>
            A.coins.bind fun s =>
              (PMF.iid (PMF.uniformOfFintype (P.G₀.Carrier d)) K).map (wonFn α s) :=
      PMF.bind_congr_on_support _ _ _ fun _ _ => (PMF.bind_const _ _).symm
    have hER : E_R =
        (PMF.uniformOfFintype (ZMod (P.G₀.order d))).bind fun α =>
          (PMF.uniformOfFintype (ZMod (P.G₀.order d))).bind fun β =>
            A.coins.bind fun s =>
              (PMF.iid coin K).bind fun cs =>
                (PMF.iid (PMF.uniformOfFintype (ZMod (P.G₀.order d))) K).map fun rhos =>
                  let samples := List.ofFn fun i : Fin K => (cs i, rhos i)
                  let res := (OracleComp.interpret (P.blsBankedReductionStep d
                    (α • P.G₀.generator d) (β • P.G₀.generator d) samples)
                      (A.forge (α • P.G₁.generator d) s)).run ([], false, 0)
                  decide (P.blsBankedReductionFinish d (α • P.G₀.generator d) samples
                    res.1 res.2 = (α * β) • P.G₀.generator d) := by
      dsimp only [E_R, blsBankedReduction]
      simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, hmap_bind, PMF.bind_bind,
        PMF.pure_bind]
    rw [hconst, hER]
    exact mul_bind_apply_le _ _ _ _ true fun α =>
      mul_bind_apply_le _ _ _ _ true fun β =>
        mul_bind_apply_le _ _ _ _ true fun s => hinner_hs α β s
  have hreal := ENNReal.toReal_mono (E_R.apply_ne_top true) henn
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at hreal
  rw [Game.coe_succProbability, Game.coe_succProbability]
  have hpos : 0 < 2.72 * a := by positivity
  calc
    ((ROMSignature.eufCmaGame (P.blsTypedROMScheme d) A) true).toReal =
        (2.72 * a) * ((1 / (2.72 * a)) *
          ((ROMSignature.eufCmaGame (P.blsTypedROMScheme d) A) true).toReal) := by
      field_simp
    _ ≤ (2.72 * a) * (E_R true).toReal := mul_le_mul_of_nonneg_left hreal hpos.le

/-- **Quantitative Coron co-CDH bound for typed BLS** ([BonehShoup2023], Theorem 15.1, eq. (15.9),
p. 629): for any typed call-bounded forger `A` making at most `Qs` signing queries and `Qro` hash
queries, `succProbability (eufCmaGame (P.blsTypedROMScheme d) A) ≤ 2.72 * (Qs + 1) * ...` for
`P.blsBankedReduction`. -/
theorem succProbability_eufCmaGame_blsTypedROMScheme_le
    (d : P.G₀.Desc) [Fintype (P.G₀.Carrier d)]
    (A : ROMSignature.Forger (P.G₁.Carrier d) (List Bool) (P.G₀.Carrier d) (List Bool)
      (P.G₀.Carrier d))
    {Qs Qro : ℕ} (hA : A.CallBounded Qs Qro) :
    (Game.succProbability (ROMSignature.eufCmaGame (P.blsTypedROMScheme d) A) : ℝ) ≤
      2.72 * (Qs + 1 : ℝ) * (Game.succProbability (do
        let α ← PMF.uniformOfFintype (ZMod (P.G₀.order d))
        let β ← PMF.uniformOfFintype (ZMod (P.G₀.order d))
        let z ← P.blsBankedReduction d A (Qs + Qro + 1)
          ((PMF.uniformOfFintype (Fin (Qs + 1))).map fun i => decide (i.val = 0))
          (α • P.G₀.generator d) (α • P.G₁.generator d) (β • P.G₀.generator d)
        return decide (z = (α * β) • P.G₀.generator d)) : ℝ) := by
  refine P.succProbability_eufCmaGame_blsTypedROMScheme_le_of_banked d A hA
    ((PMF.uniformOfFintype (Fin (Qs + 1))).map fun i => decide (i.val = 0))
    (a := (Qs + 1 : ℝ)) ?_ le_rfl
  rw [PMF.map_apply, tsum_eq_single ⟨0, Nat.succ_pos _⟩]
  · rw [PMF.uniformOfFintype_apply, Fintype.card_fin]
    simp only [decide_true, ↓reduceIte, ENNReal.toReal_inv]
    rw [ENNReal.toReal_natCast, Nat.cast_add, Nat.cast_one]
  · intro i hi
    have hne : i.val ≠ 0 := fun h => hi (Fin.ext h)
    simp [hne]

end PairingGroupFamily

namespace DecodablePairingGroupFamily

variable (P : DecodablePairingGroupFamily)

/-! ### Native word-level BLS algorithms and scheme -/

/-- Native BLS signing on encoded hash digests: query `msg`, reading at most `limit` reply
bits, then scalar-multiply the encoded digest in `G₀` by `ofBits sk`. -/
@[expose] def blsWordSign (d : P.G₀.Desc) (limit : ℕ) (sk msg : List Bool) :
    WordOracleComp Unit (List Bool) := do
  let hBits ← List.take limit <$> ProbOracleComp.query ((), msg)
  return P.G₀.smul (d, ofBits sk, hBits)

/-- Native BLS verification on bit-string signatures: query `msg`, reading at most `limit` reply
bits, test `P.isElem₀ (d, sig)`, and check
`P.pairEncoded (d, hBits, pk) = P.pairEncoded (d, sig, encode g₁)`. -/
@[expose] def blsWordVerify (d : P.G₀.Desc) (limit : ℕ) (pk msg sig : List Bool) :
    WordOracleComp Unit Bool := do
  let hBits ← List.take limit <$> ProbOracleComp.query ((), msg)
  return P.isElem₀ (d, sig) &&
    decide (P.pairEncoded (d, hBits, pk) =
      P.pairEncoded (d, sig, P.G₁.encode d (P.G₁.generator d)))

/-- `blsWordSign` is uniformly strict oracle-PPT in the description, unary reply limit, secret key
and message. -/
theorem isOraclePPTOn_blsWordSign :
    IsOraclePPTOn (encPair P.G₀.encDesc (encPair encUnary (encPair encBits encBits))) encBits
      (fun p : P.G₀.Desc × ℕ × List Bool × List Bool =>
        P.blsWordSign p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  ppt [DecodablePairingGroupFamily.blsWordSign]

/-- `blsWordVerify` is uniformly strict oracle-PPT in the description, unary reply limit, public
key, message and signature. -/
theorem isOraclePPTOn_blsWordVerify :
    IsOraclePPTOn
      (encPair P.G₀.encDesc (encPair encUnary (encPair encBits (encPair encBits encBits))))
      encBool
      (fun p : P.G₀.Desc × ℕ × List Bool × List Bool × List Bool =>
        P.blsWordVerify p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  ppt [DecodablePairingGroupFamily.blsWordVerify]

/-- **The native word-level BLS signature scheme in the random-oracle model**
([BonehShoup2023], Section 15.5.1, pp. 627–628) at security parameter `n` and group parameters
`d`. Key generation samples `sk ← P.G₁.toFamily.sampleExp n d` and sets `pk := encode (sk • g₁)`
via `P.G₁.toFamily.schnorrSigKeyGen n d`. Verification rejects non-canonical signature words via
`P.isElem₀`. -/
@[expose] noncomputable def blsNativeROMScheme (n : ℕ) (d : P.G₀.Desc) :
    ROMSignature.Scheme (List Bool) (List Bool) (List Bool) (List Bool) (List Bool)
      (P.G₀.Carrier d) where
  keyGen := ProbComp.eval (P.G₁.toFamily.schnorrSigKeyGen n d)
  SignCoins := Unit
  signCoins _ _ := PMF.pure ()
  sign sk msg _ :=
    (fun h => P.G₀.smul (d, ofBits sk, P.G₀.encode d h)) <$> OracleComp.query msg
  verify pk msg sig :=
    (fun h => P.isElem₀ (d, sig) &&
      decide (P.pairEncoded (d, P.G₀.encode d h, pk) =
        P.pairEncoded (d, sig, P.G₁.encode d (P.G₁.generator d)))) <$>
      OracleComp.query msg

/-- Exact joint realization of `blsWordSign` against any stateful `G₀` oracle whenever every
canonical digest encoding has length at most `limit`. -/
theorem runWith_blsWordSign (n : ℕ) (d : P.G₀.Desc) {limit : ℕ}
    (hlim : ∀ h : P.G₀.Carrier d, (P.G₀.encode d h).length ≤ limit)
    {Store : Type} (reply : List Bool → StateT Store PMF (P.G₀.Carrier d))
    (sk msg : List Bool) (state : Store) :
    ProbOracleComp.runWith
        (fun (q : Unit × List Bool) st => (reply q.2 st).map (Prod.map (P.G₀.encode d) id))
        (P.blsWordSign d limit sk msg) state =
      OracleComp.runWith reply ((P.blsNativeROMScheme n d).sign sk msg ()) state := by
  simp only [blsWordSign, blsNativeROMScheme, ProbOracleComp.runWith_bind,
    ProbOracleComp.runWith_map, ProbOracleComp.runWith_query, ProbOracleComp.runWith_pure,
    OracleComp.runWith_map, OracleComp.runWith_query, PMF.bind_map]
  refine PMF.bind_congr_on_support _ _ _ fun ⟨h, st'⟩ _ => ?_
  simp only [Function.comp_apply, Prod.map_apply, id_eq, List.take_of_length_le (hlim h)]

/-- Exact joint realization of `blsWordVerify` against any stateful `G₀` oracle whenever every
canonical digest encoding has length at most `limit`. -/
theorem runWith_blsWordVerify (n : ℕ) (d : P.G₀.Desc) {limit : ℕ}
    (hlim : ∀ h : P.G₀.Carrier d, (P.G₀.encode d h).length ≤ limit)
    {Store : Type} (reply : List Bool → StateT Store PMF (P.G₀.Carrier d))
    (pk msg sig : List Bool) (state : Store) :
    ProbOracleComp.runWith
        (fun (q : Unit × List Bool) st => (reply q.2 st).map (Prod.map (P.G₀.encode d) id))
        (P.blsWordVerify d limit pk msg sig) state =
      OracleComp.runWith reply ((P.blsNativeROMScheme n d).verify pk msg sig) state := by
  simp only [blsWordVerify, blsNativeROMScheme, ProbOracleComp.runWith_bind,
    ProbOracleComp.runWith_map, ProbOracleComp.runWith_query, ProbOracleComp.runWith_pure,
    OracleComp.runWith_map, OracleComp.runWith_query, PMF.bind_map]
  refine PMF.bind_congr_on_support _ _ _ fun ⟨h, st'⟩ _ => ?_
  simp only [Function.comp_apply, Prod.map_apply, id_eq, List.take_of_length_le (hlim h)]

private theorem ofBits_encScalar_eq (d : P.G₀.Desc) (α : ZMod (P.G₀.order d)) :
    (ofBits (P.G₁.toFamily.encScalar d α) : ZMod (P.G₀.order d)) = α := by
  change ((ofBits (Turing.MultiTapeTM.encNat α.val) : ℕ) : ZMod (P.G₀.order d)) = α
  have hnat : ofBits (Turing.MultiTapeTM.encNat α.val) = α.val :=
    Turing.MultiTapeTM.Decoder.nat.decode_enc α.val
  rw [hnat, ZMod.natCast_zmod_val]

private theorem blsNativeROMScheme_sign_verifies (n : ℕ) (d : P.G₀.Desc)
    [Fintype (P.G₀.Carrier d)] (α : ZMod (P.G₀.order d)) (m : List Bool)
    (cache : List (List Bool × P.G₀.Carrier d))
    (res : List Bool × List (List Bool × P.G₀.Carrier d))
    (hres : res ∈ ((interpret (oracle (P.G₀.Carrier d))
      ((P.blsNativeROMScheme n d).sign (P.G₁.toFamily.encScalar d α) m ())).run cache).support) :
    ∃ h, @List.lookup _ _ instBEqOfDecidableEq m res.2 = some h ∧
      (P.isElem₀ (d, res.1) &&
        decide (P.pairEncoded (d, P.G₀.encode d h, P.G₁.encode d (α • P.G₁.generator d)) =
          P.pairEncoded (d, res.1, P.G₁.encode d (P.G₁.generator d)))) = true := by
  simp only [blsNativeROMScheme, interpret_map, interpret_query, StateT.run_map,
    PMF.monad_map_eq_map, PMF.mem_support_map_iff] at hres
  obtain ⟨r, hr, rfl⟩ := hres
  refine ⟨r.1, lookup_of_mem_support_oracle hr, ?_⟩
  have hisElem : P.isElem₀ (d, P.G₀.encode d (α • r.1)) = true :=
    DecodablePrimeOrderGroupFamily.isElem_encode P.toDecodableG₀ d (α • r.1)
  rw [P.G₀.smul_encode, P.ofBits_encScalar_eq d α, hisElem, Bool.true_and]
  simp only [P.pairEncoded_encode, map_smul, LinearMap.smul_apply, decide_true]

/-- **Correctness** of `blsNativeROMScheme`: every generated key pair and signature verifies. -/
theorem blsNativeROMScheme_correct (n : ℕ) (d : P.G₀.Desc) [Fintype (P.G₀.Carrier d)] :
    (P.blsNativeROMScheme n d).Correct := by
  intro keys hkeys m _ _ cache signed hsigned verified hverified
  have hkg : (P.blsNativeROMScheme n d).keyGen =
      ProbComp.eval (P.G₁.toFamily.schnorrSigKeyGen n d) := rfl
  rw [hkg, PrimeOrderGroupFamily.eval_schnorrSigKeyGen, PMF.mem_support_map_iff] at hkeys
  obtain ⟨α, _, rfl⟩ := hkeys
  obtain ⟨h, hlookup, hver⟩ := P.blsNativeROMScheme_sign_verifies n d α m cache signed hsigned
  simp only [blsNativeROMScheme, interpret_map, interpret_query, StateT.run_map,
    PMF.monad_map_eq_map, PMF.mem_support_map_iff] at hverified
  obtain ⟨r', hr', rfl⟩ := hverified
  change r' ∈ ((oracle (P.G₀.Carrier d) m).run signed.2).support at hr'
  rw [run_oracle_of_lookup_eq_some hlookup, PMF.mem_support_pure_iff] at hr'
  exact hr' ▸ hver

/-- **Canonical unique signatures** for native BLS verification under a canonical `G₁` public key
`P.G₁.encode d u`: checking `P.isElem₀` and the pairing equation determines `sig : List Bool`
uniquely. -/
theorem blsNativeROMScheme_unique_of_canonical (d : P.G₀.Desc) (u : P.G₁.Carrier d)
    (h : P.G₀.Carrier d) (sig₁ sig₂ : List Bool)
    (h₁ : P.isElem₀ (d, sig₁) = true ∧
      P.pairEncoded (d, P.G₀.encode d h, P.G₁.encode d u) =
        P.pairEncoded (d, sig₁, P.G₁.encode d (P.G₁.generator d)))
    (h₂ : P.isElem₀ (d, sig₂) = true ∧
      P.pairEncoded (d, P.G₀.encode d h, P.G₁.encode d u) =
        P.pairEncoded (d, sig₂, P.G₁.encode d (P.G₁.generator d))) :
    sig₁ = sig₂ := by
  obtain ⟨σ₁, _, hσ₁⟩ := P.toDecodableG₀.exists_decode_eq_some_of_isElem h₁.1
  obtain ⟨σ₂, _, hσ₂⟩ := P.toDecodableG₀.exists_decode_eq_some_of_isElem h₂.1
  change P.G₀.Carrier d at σ₁ σ₂
  change P.G₀.encode d σ₁ = sig₁ at hσ₁
  change P.G₀.encode d σ₂ = sig₂ at hσ₂
  have hp₁ := h₁.2
  have hp₂ := h₂.2
  rw [← hσ₁, P.pairEncoded_encode, P.pairEncoded_encode, (P.GT.encode_injective d).eq_iff] at hp₁
  rw [← hσ₂, P.pairEncoded_encode, P.pairEncoded_encode, (P.GT.encode_injective d).eq_iff] at hp₂
  rw [← hσ₁, ← hσ₂, P.blsTypedROMScheme_unique d u h σ₁ σ₂ hp₁ hp₂]

/-- **Strong = existential unforgeability for native BLS**: for every word forger, `wordSufCmaGame`
and `wordEufCmaGame` coincide. -/
theorem wordSufCmaGame_blsNativeROMScheme_eq_wordEufCmaGame (n : ℕ) (d : P.G₀.Desc)
    [Fintype (P.G₀.Carrier d)]
    (forger : List Bool → WordOracleComp Bool (List Bool × List Bool)) :
    wordSufCmaGame ⟨P.G₀.encode d, P.G₀.encode_injective d⟩ (P.blsNativeROMScheme n d) forger =
      wordEufCmaGame ⟨P.G₀.encode d, P.G₀.encode_injective d⟩ (P.blsNativeROMScheme n d)
        forger := by
  unfold wordSufCmaGame wordEufCmaGame worldGame
  refine PMF.bind_congr_on_support _ _ _ fun keys hkeys => ?_
  rw [show (P.blsNativeROMScheme n d).keyGen =
    ProbComp.eval (P.G₁.toFamily.schnorrSigKeyGen n d) from rfl,
    PrimeOrderGroupFamily.eval_schnorrSigKeyGen, PMF.mem_support_map_iff] at hkeys
  obtain ⟨α, _, rfl⟩ := hkeys
  change ZMod (P.G₀.order d) at α
  have hcontains := @list_contains_beq_congr (List Bool × List Bool)
    (@instBEqProd _ _ List.instBEq List.instBEq) _
    (@instBEqProd _ _ instBEqOfDecidableEq instBEqOfDecidableEq) _
  have hcontainsMsg := @list_contains_beq_congr (List Bool) List.instBEq _ instBEqOfDecidableEq _
  simpa only [hcontains, hcontainsMsg] using sufCma_worldRealize_eq_eufCma_of_unique
    (P.blsNativeROMScheme n d) (P.G₁.encode d (α • P.G₁.generator d)) (P.G₁.toFamily.encScalar d α)
    (fun h sig => P.isElem₀ (d, sig) &&
      decide (P.pairEncoded (d, P.G₀.encode d h, P.G₁.encode d (α • P.G₁.generator d)) =
        P.pairEncoded (d, sig, P.G₁.encode d (P.G₁.generator d))))
    (fun _ _ => rfl)
    (fun m _ cache res _ hres => P.blsNativeROMScheme_sign_verifies n d α m cache res hres)
    (fun h sig₁ sig₂ h₁ h₂ => by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h₁ h₂
      exact P.blsNativeROMScheme_unique_of_canonical d (α • P.G₁.generator d) h sig₁ sig₂ h₁ h₂)
    (routeWordProgram ⟨P.G₀.encode d, P.G₀.encode_injective d⟩
      (forger (P.G₁.encode d (α • P.G₁.generator d))))

/-- **Native BLS SUF-CMA ↔ EUF-CMA**: strong unforgeability and existential unforgeability coincide
in the random-oracle model. -/
theorem sufCma_iff_eufCma_blsNativeROMScheme (description : ℕ → P.G₀.Desc)
    [∀ n, Fintype (P.G₀.Carrier (description n))] :
    ROMSignature.SUFCMA (fun n => ⟨P.G₀.encode (description n), P.G₀.encode_injective _⟩)
      (fun n => P.blsNativeROMScheme n (description n)) ↔
    ROMSignature.EUFCMA (fun n => ⟨P.G₀.encode (description n), P.G₀.encode_injective _⟩)
      (fun n => P.blsNativeROMScheme n (description n)) :=
  ⟨ROMSignature.SUFCMA.eufCma, fun hEuf => ROMSignature.SUFCMA.of_negligible fun prog hprog => by
    simpa only [wordSufCmaGame_blsNativeROMScheme_eq_wordEufCmaGame] using
      hEuf.negligible prog hprog⟩

end DecodablePairingGroupFamily

end Cslib.Crypto
