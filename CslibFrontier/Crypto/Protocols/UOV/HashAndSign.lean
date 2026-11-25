/-
Copyright (c) 2026 Samuel Schlesinger, Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Commitment.Scheme
public import CslibFrontier.Crypto.Game.CloseTo
public import CslibFrontier.Crypto.Protocols.AnonymousToken.Conservation
public import CslibFrontier.Crypto.Protocols.Signature.RandomOracle
public import CslibFrontier.Crypto.Protocols.UOV.Games
public import CslibFrontier.Languages.Probabilistic.RandomOracle.Programming
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Languages.Probabilistic.Oracle.InterpNorm
import CslibFrontier.Languages.Probabilistic.Oracle.Norm
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Languages.Probabilistic.RandomOracle.Probabilistic
import CslibFrontier.Languages.Probabilistic.UntilBad.Flag
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.Product

/-!
# Classical ROM EUF-CMA for deterministic and salted hash-and-sign trapdoor signatures

This module formalizes finite classical random-oracle-model (ROM) existential unforgeability under
adaptive chosen-message attack (EUF-CMA) for **deterministic unsalted** and **salted**
hash-and-sign trapdoor-preimage signature schemes, together with their composition with
extracted-model single-issuer VOLE-ACT credit conservation
(`Cslib.Crypto.AnonymousToken.Conservation`).

## Scope and model boundaries

* **Finite classical ROM, query-bounded reductions.** All adversaries are finite classical
  `ProbOracleComp` or `ROMSignature.Forger` programs with explicit signing-query budget `q_S` and
  hash-query budget `q_H`. Every reduction is an explicit program with a proved query bound; no
  Turing-machine / PPT runtime certificate is claimed (tracked in #7068). No quantum random-oracle
  (QROM) bound is proved here: `[KosugeXagawa2022]` (Theorem 1 and Appendix B.2 Proposition 3)
  motivates the salted variant in the QROM, while the salted theorems proved here are finite
  classical-ROM reductions **after** `[KosugeXagawa2022]` (Theorem 1, classical-ROM specialization
  on p. 18, and Section 2.3, Figure 4 / Definition 7 on p. 10), with explicit deviations: no retry
  (`Option Preimage` failure retained so `q'_sign = q_sign`, omitting retry failure slack),
  classical ROM queries (`(q_H + 1) * INV` rather than QROM `(2 q_qro + 1)^2 * INV`), and explicit
  salt-collision slack `(q_S * q_H + q_S.choose 2) / |Salt|`.
* **Abstract trapdoor preimage systems (`TrapdoorPreimageSystem`).** A system bundles key
  generation, public evaluation `eval : PK → Preimage → Target`, a total finite preimage sampler
  `invert : SK → Target → ProbComp (Option Preimage)` retaining explicit failure (`none`) without
  conditioning, and a secret-free simulated preimage sampler `samplePreimage : PK → ProbComp
  Preimage`. `idealUOVSystem` instantiates this interface with `UOV.idealKeyGen` and uniform
  preimage sampling so that `(idealUOVSystem F v o derive).toRawScheme = UOV.idealRawScheme derive`
  (`idealUOVSystem_toRawScheme`). Concrete round-3 UOV signing and vinegar-retry bounds remain
  tracked in #4987 and #5219.
* **Programmable ROM `Tag`, starting after vinegar derandomization.** `detScheme` models
  deterministic unsalted hash-and-sign (`Σ_Tag` of [VOLEACT2026], Protocol Specification / Tag)
  after per-target derandomization: key generation draws `invTable ← PMF.pi (eval ∘ invert sk)` and
  stores that full `Target → Option Preimage` table in `sk` (replacing it by a PRF or PRG seed is
  outside this model), so repeated signatures on the same target return the same preimage while
  distinct targets are inverted independently, and `Tag` is modeled as a lazy uniform random
  oracle rather than concrete `Keccak-p[800, 12]`. `saltedScheme` models salted hash-and-sign
  (`SignCoins := Salt × (Target → Option Preimage)`), drawing a fresh uniform salt and independent
  preimage on every signing call.
* **Concrete game bounds.** Preimage resistance (`INV`) reuses `Signature.targetExperiment` on
  `sys.toRawScheme` with uniform targets. Preimage simulatability (`PS`) compares
  `psExperimentReal` (sampling uniform `y` and `x ← invert sk y`) against `psExperimentSim`
  (sampling `s ← samplePreimage pk` and returning `(eval pk s, some s)`), adapted from Figure 4 of
  `[KosugeXagawa2022]` with explicit failure retained. All bounds are concrete inequalities relating
  explicit games; no new asymptotic hardness-assumption `Prop` is introduced.

## Main definitions

* `TrapdoorPreimageSystem`, `TrapdoorPreimageSystem.check`, `TrapdoorPreimageSystem.toRawScheme`,
  `idealUOVSystem`: abstract trapdoor-preimage signature core and ideal UOV instantiation.
* `TrapdoorPreimageSystem.sampleRealPair`, `TrapdoorPreimageSystem.sampleSimPair`,
  `PSDistinguisher`, `psExperimentReal`, `psExperimentSim`: preimage simulatability (`PS`)
  experiments after `[KosugeXagawa2022]`, Figure 4.
* `detScheme`, `saltedScheme`: deterministic unsalted and salted hash-and-sign
  `ROMSignature.Scheme` constructions.
* `detPSDistinguisher`, `detPSOneDistinguisher`, `detInverter`: explicit multi-query `PS`,
  single-query `PS`, and `INV` reductions for `detScheme`.
* `saltedPSDistinguisher`, `saltedInverter`: explicit `q_S`-query `PS` and `INV` reductions for
  `saltedScheme`.
* `ROMExtractedAdversary`, `ROMExtractedCallBounded`, `romExtractedConservationExperiment`,
  `romTargetForger`, `detCommitmentBindingReduction`, `saltedCommitmentBindingReduction`:
  lazy-ROM extracted VOLE-ACT credit-conservation game at `tag = Prod.mk` (original to this
  library) and its explicit target-forgery and commitment-binding reductions.

## Main results

* `idealUOVSystem_toRawScheme`: equality between `(idealUOVSystem F v o derive).toRawScheme` and
  `UOV.idealRawScheme derive`.
* `detScheme_correct`, `saltedScheme_correct`: completeness of both ROM schemes when `invert`
  succeeds with valid preimages.
* `detPSDistinguisher_queryBound`, `detPSOneDistinguisher_queryBound`,
  `saltedPSDistinguisher_queryBound`, `romTargetForger_callBounded`: exact query budgets for the
  `PS` and credit-conservation reductions.
* `saltedRomWorldEufCma_succProbability_le`, `eufCmaGame_saltedScheme_succProbability_le`: classical
  ROM EUF-CMA bounds for salted hash-and-sign after `[KosugeXagawa2022]` Theorem 1 (without
  retry), with `(q_H + 1)` `INV` loss, `q_S`-query `PS` advantage, and
  `(q_S * q_H + q_S.choose 2) / |Salt|` salt-collision slack.
* `detRomWorldEufCma_succProbability_le`, `eufCmaGame_detScheme_succProbability_le`: classical ROM
  EUF-CMA bounds for deterministic unsalted hash-and-sign (original to this library, adapting the
  `(q_H + 1)` programming argument) with `(q_H + 1)` loss on `INV + PS_1`, `(q_S + q_H)`-query
  `PS` advantage, and `(q_S + q_H).choose 2 / |Target|` target birthday slack.
* `romExtractedConservationExperiment_succProbability_le`,
  `romExtractedConservationExperiment_detScheme_succProbability_le`,
  `romExtractedConservationExperiment_saltedScheme_succProbability_le`: original end-to-end
  extracted+ROM credit-conservation bounds composing the lazy-ROM EUF-CMA bounds with keyless
  commitment binding at `tag = Prod.mk`.

## References

* [W. Beullens et al., *UOV: Unbalanced Oil and Vinegar, Algorithm Specifications and Supporting
  Documentation*, v3.0, Appendix A, Definition 2, p. 49][UOV2026].
* [*VOLE-ACT*][VOLEACT2026], Protocol Specification / Parameters / Tag and Spending.
* [Baum et al., *PoMFRIT*, USENIX prepublication, Definition 3.1][PoMFRIT2026].
* [H. Kosuge and K. Xagawa, *Probabilistic Hash-and-Sign with Retry in the Quantum Random Oracle
  Model*, ePrint 2022/1359, Figure 4, Theorem 1, and Proposition 3][KosugeXagawa2022].
-/

public section

namespace Cslib.Crypto.UOV.HashAndSign

open Probability OracleComp Protocols
open scoped ENNReal NNReal

/-! ### Trapdoor preimage systems and preimage simulatability (`PS`) -/

section System

variable {PK SK Target Preimage : Type}

/-- An abstract finite trapdoor-preimage relation with explicit inversion failure and a secret-free
simulated preimage distribution. -/
structure TrapdoorPreimageSystem (PK SK Target Preimage : Type) where
  /-- Key-pair generator. -/
  keyGen : ProbComp (PK × SK)
  /-- Public forward map `P : Preimage → Target`. -/
  eval : PK → Preimage → Target
  /-- Trapdoor preimage sampler, returning `none` on failure without conditioning it away. -/
  invert : SK → Target → ProbComp (Option Preimage)
  /-- Secret-free simulated preimage sampler used in preimage simulatability (`PS`). -/
  samplePreimage : PK → ProbComp Preimage

/-- Check a candidate optional preimage against `target`: `none` rejects, `some s` checks
`eval pk s = target`. -/
@[expose] def TrapdoorPreimageSystem.check [DecidableEq Target]
    (sys : TrapdoorPreimageSystem PK SK Target Preimage) (pk : PK) (target : Target) :
    Option Preimage → Bool
  | none => false
  | some s => decide (sys.eval pk s = target)

/-- Package a trapdoor-preimage system as a raw target `Signature.Scheme`, reusing
`Signature.targetExperiment` for preimage resistance (`INV`). -/
@[expose] def TrapdoorPreimageSystem.toRawScheme [DecidableEq Target]
    (sys : TrapdoorPreimageSystem PK SK Target Preimage) :
    Signature.Scheme PK SK Target (Option Preimage) where
  keyGen := sys.keyGen
  sign := sys.invert
  verify := sys.check

/-- A system is inverting-correct when `invert` never fails and every returned preimage maps back
to the requested target on all supported key pairs. -/
@[expose] def TrapdoorPreimageSystem.InvertCorrect
    (sys : TrapdoorPreimageSystem PK SK Target Preimage) : Prop :=
  ∀ keys ∈ (ProbComp.eval sys.keyGen).support, ∀ y opt,
    opt ∈ (ProbComp.eval (sys.invert keys.2 y)).support →
      ∃ s, opt = some s ∧ sys.eval keys.1 s = y

/-- Ideal UOV instantiation of `TrapdoorPreimageSystem`: uses `UOV.idealKeyGen`, the public
multivariate quadratic map, the caller's finite preimage derivation program, and uniform preimage
sampling on `Fin (v + o) → F`. Its `.toRawScheme` equals `UOV.idealRawScheme`
(`idealUOVSystem_toRawScheme`). -/
@[expose] noncomputable def idealUOVSystem (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (v o : ℕ)
    (derivePreimage : IdealKeyMaterial F v o → (Fin o → F) →
      ProbComp (Option (Fin (v + o) → F))) :
    TrapdoorPreimageSystem (MultivariateQuadraticMap F (Fin (v + o)) (Fin o))
      (IdealKeyMaterial F v o) (Fin o → F) (Fin (v + o) → F) where
  keyGen := idealKeyGen F v o
  eval P s := P s
  invert := derivePreimage
  samplePreimage _ := ProbComp.uniform (Fin (v + o) → F)

/-- `(idealUOVSystem F v o derive).toRawScheme` agrees with `UOV.idealRawScheme derive`. -/
theorem idealUOVSystem_toRawScheme (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (v o : ℕ)
    (derivePreimage : IdealKeyMaterial F v o → (Fin o → F) →
      ProbComp (Option (Fin (v + o) → F))) :
    (idealUOVSystem F v o derivePreimage).toRawScheme = UOV.idealRawScheme derivePreimage := by
  simp only [TrapdoorPreimageSystem.toRawScheme, idealUOVSystem, UOV.idealRawScheme]
  congr 1
  funext P y sig
  cases sig <;> rfl

/-- Real preimage-simulatability sample: draw a uniform target `y` and invert it with `sk`. -/
@[expose] noncomputable def TrapdoorPreimageSystem.sampleRealPair [Fintype Target] [Nonempty Target]
    (sys : TrapdoorPreimageSystem PK SK Target Preimage) (sk : SK) :
    ProbComp (Target × Option Preimage) := do
  let y ← ProbComp.uniform Target
  let x ← sys.invert sk y
  return (y, x)

/-- Simulated preimage-simulatability sample: draw `s ← samplePreimage pk` and return
`(eval pk s, some s)`. -/
@[expose] def TrapdoorPreimageSystem.sampleSimPair
    (sys : TrapdoorPreimageSystem PK SK Target Preimage) (pk : PK) :
    ProbComp (Target × Option Preimage) := do
  let s ← sys.samplePreimage pk
  return (sys.eval pk s, some s)

/-- The first marginal of `sampleRealPair` is the exact uniform distribution on `Target`. -/
theorem TrapdoorPreimageSystem.eval_sampleRealPair_map_fst [Fintype Target] [Nonempty Target]
    (sys : TrapdoorPreimageSystem PK SK Target Preimage) (sk : SK) :
    (ProbComp.eval (sys.sampleRealPair sk)).map Prod.fst = PMF.uniformOfFintype Target := by
  simp only [sampleRealPair, ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure,
    PMF.map_bind, PMF.pure_map]
  have hconst (y : Target) :
      ((ProbComp.eval (sys.invert sk y)).bind fun _ => PMF.pure y) = PMF.pure y := by
    have := (ProbComp.eval (sys.invert sk y)).map_const y
    simpa only [PMF.map, Function.comp_def, Function.const_apply] using this
  simp [hconst]

/-- An adaptive distinguisher in the preimage-simulatability (`PS`) game (after
`[KosugeXagawa2022]`, Section 2.3, Figure 4 and Definition 7, adapted to retain `Option Preimage`
failure without retry): given `pk`, it queries a sampling oracle returning `(y, x)` pairs and
outputs a bit. -/
abbrev PSDistinguisher (PK Target Preimage : Type) :=
  PK → ProbOracleComp (fun _ : Unit => Target × Option Preimage) Bool

/-- Real `PS` experiment (`b = 0`): oracle calls return `(y, invert sk y)` for uniform `y`. -/
@[expose] noncomputable def psExperimentReal [Fintype Target] [Nonempty Target]
    (sys : TrapdoorPreimageSystem PK SK Target Preimage)
    (D : PSDistinguisher PK Target Preimage) : Experiment := do
  let keys ← sys.keyGen
  (D keys.1).run fun _ => sys.sampleRealPair keys.2

/-- Simulated `PS` experiment (`b = 1`): oracle calls return `(eval pk s, some s)` for
`s ← samplePreimage pk`. -/
@[expose] def psExperimentSim
    (sys : TrapdoorPreimageSystem PK SK Target Preimage)
    (D : PSDistinguisher PK Target Preimage) : Experiment := do
  let keys ← sys.keyGen
  (D keys.1).run fun _ => sys.sampleSimPair keys.1

end System

/-! ### Deterministic unsalted and salted ROM hash-and-sign schemes -/

section Schemes

variable {PK SK M Target Preimage Salt : Type}

/-- Call budget for a probabilistic ROM forger (`ProbOracleComp`): at most `q_S` signing queries
and at most `q_H` direct hash queries on every execution path. -/
@[expose] def ProbForgerCallBounded {Sig Query Digest : Type}
    (forger : PK → ProbOracleComp (ROMSignature.ForgerSpec M Query Sig Digest) (M × Sig))
    (q_S q_H : ℕ) : Prop :=
  ∀ pk,
    IsCostBounded (Sum.elim (fun _ => 0) ROMSignature.signingCost) (forger pk) q_S ∧
      IsCostBounded (Sum.elim (fun _ => 0) ROMSignature.hashCost) (forger pk) q_H

/-- Lifting a deterministic `ROMSignature.Forger` with `CallBounded q_S q_H` preserves both
signing and hash budgets as a `ProbOracleComp` forger. -/
theorem probForgerCallBounded_liftOracleForger {Sig Query Digest : Type}
    {A : ROMSignature.Forger PK M Sig Query Digest} {q_S q_H : ℕ}
    (hA : A.CallBounded q_S q_H) (coins : A.Coins) :
    ProbForgerCallBounded (fun pk => ROMSignature.liftOracleForger (A.forge pk coins)) q_S q_H := by
  intro pk
  have h1 := (hA pk coins).1
  have h2 := (hA pk coins).2
  refine ⟨?_, ?_⟩
  · unfold ROMSignature.liftOracleForger
    refine h1.interpret fun q => ?_
    exact OracleComp.IsCostBounded.query (cost := Sum.elim (fun _ => 0) ROMSignature.signingCost)
      (Sum.inr q)
  · unfold ROMSignature.liftOracleForger
    refine h2.interpret fun q => ?_
    exact OracleComp.IsCostBounded.query (cost := Sum.elim (fun _ => 0) ROMSignature.hashCost)
      (Sum.inr q)

/-- The EUF-CMA acceptance predicate for `ROMSignature.worldGame`: the signature verifies and the
forged message was never submitted to the signing oracle. -/
@[expose] def eufCmaAccept [DecidableEq M] {Sig : Type}
    (verified : Bool) (msig : M × Sig) (pairs : List (M × Sig)) : Bool :=
  verified && !(pairs.map Prod.fst).contains msig.1

/-- **Deterministic unsalted hash-and-sign scheme (`Σ_Tag`)** in the classical ROM, after
per-target derandomization: `keyGen` draws `invTable ← PMF.pi (eval ∘ invert sk)` and stores the
full `Target → Option Preimage` table in `sk` (replacing it by a PRF or seed is outside this model),
`sign` hashes `m` and returns `invTable (H m)`, and `verify` checks `sys.check pk (H m) sig`. -/
@[expose] noncomputable def detScheme [DecidableEq Target] [Fintype Target] [Finite Preimage]
    (sys : TrapdoorPreimageSystem PK SK Target Preimage) :
    ROMSignature.Scheme PK (SK × (Target → Option Preimage)) M (Option Preimage) M Target where
  keyGen := do
    let keys ← ProbComp.eval sys.keyGen
    let invTable ← PMF.pi fun y => ProbComp.eval (sys.invert keys.2 y)
    return (keys.1, (keys.2, invTable))
  SignCoins := Unit
  signCoins _ _ := PMF.pure ()
  sign sk m _ := do
    let y ← OracleComp.query m
    return sk.2 y
  verify pk m sig := do
    let y ← OracleComp.query m
    return sys.check pk y sig

/-- **Salted hash-and-sign scheme** in the classical ROM: `signCoins` draws a fresh uniform salt
and independent preimage table per signing call, `sign` hashes `(m, r)` and returns `(r, f y)`,
and `verify` hashes `(m, r)` and checks `sys.check pk y sig`. -/
@[expose] noncomputable def saltedScheme [DecidableEq Target] [Fintype Target] [Finite Preimage]
    (sys : TrapdoorPreimageSystem PK SK Target Preimage) (Salt : Type)
    [Fintype Salt] [Nonempty Salt] :
    ROMSignature.Scheme PK SK M (Salt × Option Preimage) (M × Salt) Target where
  keyGen := ProbComp.eval sys.keyGen
  SignCoins := Salt × (Target → Option Preimage)
  signCoins sk _ := do
    let r ← PMF.uniformOfFintype Salt
    let f ← PMF.pi fun y => ProbComp.eval (sys.invert sk y)
    return (r, f)
  sign _ m coins := do
    let y ← OracleComp.query (m, coins.1)
    return (coins.1, coins.2 y)
  verify pk m sig := do
    let y ← OracleComp.query (m, sig.1)
    return sys.check pk y sig.2

/-- Completeness of `detScheme`: when `sys.InvertCorrect`, every signature produced by `detScheme`
verifies under the same random-oracle cache. -/
theorem detScheme_correct [DecidableEq M] [DecidableEq Target] [Fintype Target] [Nonempty Target]
    [Finite Preimage] {sys : TrapdoorPreimageSystem PK SK Target Preimage}
    (hcorr : sys.InvertCorrect) :
    (detScheme (M := M) sys).Correct := by
  intro keys hkeys m _ _ cache signed hsigned verified hverified
  simp only [detScheme, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hkeys
  obtain ⟨⟨pk, sk⟩, hks, invTable, htable, rfl⟩ := hkeys
  rw [PMF.mem_support_pi_iff] at htable
  simp only [detScheme, interp_norm, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hsigned hverified
  obtain ⟨⟨y, cache₁⟩, hy, rfl⟩ := hsigned
  have hlookup := ROMSignature.lookup_of_mem_support_oracle hy
  obtain ⟨⟨y', cache₂⟩, hy', rfl⟩ := hverified
  have hor := ROMSignature.run_oracle_of_lookup_eq_some hlookup
  change (y', cache₂) ∈ ((ROMSignature.oracle Target m).run cache₁).support at hy'
  rw [hor, PMF.mem_support_pure_iff, Prod.mk.injEq] at hy'
  obtain ⟨rfl, rfl⟩ := hy'
  obtain ⟨s, hs, heval⟩ := hcorr (pk, sk) hks y' (invTable y') (htable y')
  simp [TrapdoorPreimageSystem.check, hs, heval]

/-- Completeness of `saltedScheme`: when `sys.InvertCorrect`, every signature produced by
`saltedScheme` verifies under the same random-oracle cache. -/
theorem saltedScheme_correct [DecidableEq M] [DecidableEq Target] [Fintype Target]
    [Nonempty Target] [Finite Preimage] [Fintype Salt] [Nonempty Salt] [DecidableEq Salt]
    {sys : TrapdoorPreimageSystem PK SK Target Preimage} (hcorr : sys.InvertCorrect) :
    (saltedScheme (M := M) sys Salt).Correct := by
  intro keys hkeys m coins hcoins cache signed hsigned verified hverified
  change coins ∈ ((PMF.uniformOfFintype Salt).bind fun r =>
    (PMF.pi fun y => ProbComp.eval (sys.invert keys.2 y)).bind fun f => PMF.pure (r, f)).support
    at hcoins
  obtain ⟨r, -, f, hf, hrc⟩ :
      ∃ r ∈ (PMF.uniformOfFintype Salt).support,
        ∃ f ∈ (PMF.pi fun y => ProbComp.eval (sys.invert keys.2 y)).support,
          coins = (r, f) := by
    have h1 := (PMF.mem_support_bind_iff _ _ _).mp hcoins
    obtain ⟨r, hr, h2⟩ := h1
    obtain ⟨f, hf, h3⟩ := (PMF.mem_support_bind_iff _ _ _).mp h2
    exact ⟨r, hr, f, hf, (PMF.mem_support_pure_iff _ _).mp h3⟩
  subst hrc
  rw [PMF.mem_support_pi_iff] at hf
  simp only [saltedScheme, interp_norm, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hsigned hverified
  obtain ⟨⟨y, cache₁⟩, hy, rfl⟩ := hsigned
  have hlookup := ROMSignature.lookup_of_mem_support_oracle hy
  obtain ⟨⟨y', cache₂⟩, hy', rfl⟩ := hverified
  have hor := ROMSignature.run_oracle_of_lookup_eq_some hlookup
  change (y', cache₂) ∈ ((ROMSignature.oracle Target (m, r)).run cache₁).support at hy'
  rw [hor, PMF.mem_support_pure_iff, Prod.mk.injEq] at hy'
  obtain ⟨rfl, rfl⟩ := hy'
  obtain ⟨s, hs, heval⟩ := hcorr keys hkeys y' (f y') (hf y')
  simp [TrapdoorPreimageSystem.check, hs, heval]

end Schemes

/-! ### Shared Bellare–Rogaway guessing helper -/

section GuessingHelper

private theorem uniform_fin_guess_mul {N : ℕ} [NeZero N] (μ : PMF (Bool × Fin N)) :
    (μ.map Prod.fst) true =
      (N : ℝ≥0∞) *
        ((PMF.uniformOfFintype (Fin N)).bind fun jStar =>
          μ.map fun p => p.1 && decide (p.2 = jStar)) true := by
  have hne0 : (N : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hnetop : (N : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top N
  simp only [PMF.bind_apply, PMF.uniformOfFintype_apply, Fintype.card_fin, PMF.map_apply,
    ENNReal.tsum_mul_left, ← mul_assoc, ENNReal.mul_inv_cancel hne0 hnetop, one_mul]
  rw [tsum_comm]
  refine tsum_congr fun ⟨b, j⟩ => ?_
  rw [tsum_fintype]
  cases b with
  | false => simp
  | true => simp

private theorem targetHit_le_yAtJ_check
    {PK SK Target Preimage : Type} [DecidableEq Target] [Fintype Target] [Nonempty Target]
    (sys : TrapdoorPreimageSystem PK SK Target Preimage) (pk : PK)
    (sigStar : Option Preimage) (notSigned : Bool) {q_H : ℕ} (hCount : ℕ) (jStar : Fin (q_H + 1))
    (yAtJ : Option Target) (hit : Option (Target × Option ℕ))
    (hcount_le : hCount ≤ q_H)
    (hnone : hCount ≤ jStar.val → yAtJ = none)
    (hhit_none : ∀ y, hit = some (y, none) → notSigned = false)
    (hhit_lt : ∀ y k, hit = some (y, some k) → k < hCount)
    (hhit_j : ∀ y, hit = some (y, some jStar.val) → yAtJ = some y) :
    ((match hit with
      | some (y, idxOpt) =>
          PMF.pure ((sys.check pk y sigStar && notSigned) &&
            decide (Fin.ofNat (q_H + 1) (idxOpt.getD hCount) = jStar))
      | none =>
          (PMF.uniformOfFintype Target).map fun y =>
            (sys.check pk y sigStar && notSigned) &&
              decide (Fin.ofNat (q_H + 1) hCount = jStar)) true) ≤
    ((match yAtJ with
      | some yStar => PMF.pure (sys.check pk yStar sigStar)
      | none =>
          (PMF.uniformOfFintype Target).map fun yStar => sys.check pk yStar sigStar) true) := by
  cases hit with
  | some yk =>
    rcases yk with ⟨y, idxOpt⟩
    dsimp only
    by_cases hwin : (sys.check pk y sigStar && notSigned) &&
        decide (Fin.ofNat (q_H + 1) (idxOpt.getD hCount) = jStar) = true
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hwin
      obtain ⟨⟨hchk, hnot_signed⟩, hidx_eq⟩ := hwin
      cases idxOpt with
      | none => exact absurd (hhit_none y rfl) (by simp [hnot_signed])
      | some k =>
        have hk_lt : k < q_H + 1 := Nat.lt_succ_of_le ((hhit_lt y k rfl).le.trans hcount_le)
        have hk_eq : k = jStar.val := by
          have := congrArg Fin.val hidx_eq
          simpa [Fin.val_ofNat, Nat.mod_eq_of_lt hk_lt] using this
        subst hk_eq
        rw [hhit_j y rfl]
        simp [hchk, hnot_signed]
    · have hfalse : ((sys.check pk y sigStar && notSigned) &&
          decide (Fin.ofNat (q_H + 1) (idxOpt.getD hCount) = jStar)) = false :=
        Bool.eq_false_iff.mpr hwin
      rw [hfalse]
      simp only [PMF.pure_apply, Bool.true_eq_false, ↓reduceIte]
      exact zero_le
  | none =>
    dsimp only
    by_cases hidx_eq : Fin.ofNat (q_H + 1) hCount = jStar
    · have hcnt_eq : hCount = jStar.val := by
        have := congrArg Fin.val hidx_eq
        simpa [Fin.val_ofNat, Nat.mod_eq_of_lt (Nat.lt_succ_of_le hcount_le)] using this
      rw [hnone (le_of_eq hcnt_eq)]
      dsimp only
      simp only [hidx_eq, decide_true, Bool.and_true]
      refine PMF.map_true_mono _ fun y _ h => (Bool.and_eq_true_iff.mp h).1
    · have hzero :
          ((PMF.uniformOfFintype Target).map fun y =>
            (sys.check pk y sigStar && notSigned) &&
              decide (Fin.ofNat (q_H + 1) hCount = jStar)) true = 0 := by
        simp only [decide_eq_false hidx_eq, Bool.and_false, PMF.map_apply, Bool.true_eq_false,
          ↓reduceIte, tsum_zero]
      rw [hzero]
      exact zero_le

end GuessingHelper

/-! ### Classical ROM EUF-CMA for salted hash-and-sign -/

section SaltedReduction

variable {PK SK M Target Preimage : Type}

/-- Stateful handler of `saltedPSDistinguisher`: signing draws a uniform salt, queries the `PS`
oracle once for `(y, x)`, and overwrites `((m, r), y)` in the cache; hashing lazily draws uniform
targets. -/
@[expose] noncomputable def saltedPSHandler {Salt : Type} [DecidableEq M] [DecidableEq Salt]
    [Fintype Salt] [Nonempty Salt] [Fintype Target] [Nonempty Target] :
    (q : M ⊕ (M × Salt)) →
      StateT (List ((M × Salt) × Target) × List M)
        (ProbOracleComp (fun _ : Unit => Target × Option Preimage))
        (ROMSignature.ForgerSpec M (M × Salt) (Salt × Option Preimage) Target q)
  | .inl m => fun (cache, signed) => do
      let r ← ProbOracleComp.sample (ProbComp.uniform Salt)
      let yx ← ProbOracleComp.query ()
      return ((r, yx.2), (((m, r), yx.1) :: cache, m :: signed))
  | .inr q => fun (cache, signed) =>
      match cache.lookup q with
      | some y => pure (y, (cache, signed))
      | none => do
          let y ← ProbOracleComp.sample (ProbComp.uniform Target)
          return (y, ((q, y) :: cache, signed))

/-- Explicit `q_S`-query preimage-simulatability (`PS`) distinguisher for `saltedScheme`: runs
`forger` against `saltedPSHandler`, verifies the output against the resulting cache (drawing a
fresh uniform target if unqueried), and accepts iff the forgery verifies on an unsigned message. -/
@[expose] noncomputable def saltedPSDistinguisher [DecidableEq M]
    [DecidableEq Target] [Fintype Target] [Nonempty Target]
    (sys : TrapdoorPreimageSystem PK SK Target Preimage) (Salt : Type)
    [Fintype Salt] [Nonempty Salt] [DecidableEq Salt]
    (forger : PK → ProbOracleComp
      (ROMSignature.ForgerSpec M (M × Salt) (Salt × Option Preimage) Target)
      (M × (Salt × Option Preimage))) :
    PSDistinguisher PK Target Preimage := fun pk => do
  let ((mStar, (rStar, sigStar)), (cache, signed)) ← (OracleComp.interpret
    (OracleComp.sumHandler
      (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
      (saltedPSHandler (M := M) (Salt := Salt) (Target := Target) (Preimage := Preimage)))
    (forger pk)).run ([], [])
  let yStar ←
    match cache.lookup (mStar, rStar) with
    | some y => pure y
    | none => ProbOracleComp.sample (ProbComp.uniform Target)
  return sys.check pk yStar sigStar && !signed.contains mStar

/-- `saltedPSDistinguisher` makes at most `q_S` queries to the `PS` oracle whenever `forger` makes
at most `q_S` signing queries (independent of `q_H`). -/
theorem saltedPSDistinguisher_queryBound {Salt : Type} [DecidableEq M] [DecidableEq Salt]
    [DecidableEq Target] [Fintype Salt] [Nonempty Salt] [Fintype Target] [Nonempty Target]
    (sys : TrapdoorPreimageSystem PK SK Target Preimage)
    (forger : PK → ProbOracleComp
      (ROMSignature.ForgerSpec M (M × Salt) (Salt × Option Preimage) Target)
      (M × (Salt × Option Preimage)))
    {q_S q_H : ℕ} (hforger : ProbForgerCallBounded forger q_S q_H) (pk : PK) :
    (saltedPSDistinguisher sys Salt forger pk).IsQueryBounded q_S := by
  have hbody :
      ((OracleComp.interpret
        (OracleComp.sumHandler
          (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
          (saltedPSHandler (M := M) (Salt := Salt) (Target := Target) (Preimage := Preimage)))
        (forger pk)).run ([], [])).IsQueryBounded q_S := by
    refine OracleComp.IsCostBounded.run_interpret (fun r st => ?_) (hforger pk).1 ([], [])
    rcases r with k | q
    · simpa [OracleComp.sumHandler, StateT.run, StateT.lift] using
        (ProbOracleComp.IsQueryBounded.sample
          (spec := fun _ : Unit => Target × Option Preimage) (ProbComp.unifFin k)).bind
            fun a => OracleComp.IsCostBounded.pure (a, st) 0
    · rcases q with m | hq
      · simp only [OracleComp.sumHandler, Sum.elim_inr, ROMSignature.signingCost, StateT.run,
          saltedPSHandler]
        refine (ProbOracleComp.IsQueryBounded.sample
          (spec := fun _ : Unit => Target × Option Preimage) (ProbComp.uniform Salt)).bind fun r =>
            (ProbOracleComp.IsQueryBounded.query
              (spec := fun _ : Unit => Target × Option Preimage) ()).bind fun yx =>
                OracleComp.IsCostBounded.pure _ 0
      · simp only [OracleComp.sumHandler, Sum.elim_inr, ROMSignature.signingCost, StateT.run,
          saltedPSHandler]
        cases st.1.lookup hq with
        | some y => exact OracleComp.IsCostBounded.pure _ 0
        | none =>
          exact (ProbOracleComp.IsQueryBounded.sample
            (spec := fun _ : Unit => Target × Option Preimage) (ProbComp.uniform Target)).bind
              fun y => OracleComp.IsCostBounded.pure _ 0
  dsimp only [saltedPSDistinguisher]
  rw [← Nat.add_zero q_S]
  refine hbody.bind ?_
  rintro ⟨⟨mStar, rStar, sigStar⟩, cache, signed⟩
  dsimp only
  cases cache.lookup (mStar, rStar) with
  | some y =>
    simpa only [pure_bind] using
      (OracleComp.IsCostBounded.pure (cost := Sum.elim (fun _ => 0) fun _ => 1)
        (sys.check pk y sigStar && !signed.contains mStar) 0)
  | none =>
    simpa only [add_zero] using
      (ProbOracleComp.IsQueryBounded.sample
        (spec := fun _ : Unit => Target × Option Preimage) (ProbComp.uniform Target)).bind
        fun y' => OracleComp.IsCostBounded.pure
          (sys.check pk y' sigStar && !signed.contains mStar) 0

/-- Stateful handler of `saltedInverter`: signing simulates `(y, x) ← sampleSimPair pk` and
overwrites the cache without advancing `hCount`; the `jStar`-th fresh direct hash query embeds
the challenge target `yStar`. -/
@[expose] noncomputable def saltedInvHandler {Salt : Type} [DecidableEq M] [DecidableEq Salt]
    [Fintype Salt] [Nonempty Salt] [Fintype Target] [Nonempty Target]
    (sys : TrapdoorPreimageSystem PK SK Target Preimage) (pk : PK)
    (jStar : ℕ) (yStar : Target) :
    (q : M ⊕ (M × Salt)) →
      StateT (List ((M × Salt) × Target) × ℕ) ProbComp
        (ROMSignature.ForgerSpec M (M × Salt) (Salt × Option Preimage) Target q)
  | .inl m => fun (cache, hCount) => do
      let r ← ProbComp.uniform Salt
      let yx ← sys.sampleSimPair pk
      return ((r, yx.2), (((m, r), yx.1) :: cache, hCount))
  | .inr q => fun (cache, hCount) =>
      match cache.lookup q with
      | some y => pure (y, (cache, hCount))
      | none => do
          let y ← if hCount = jStar then pure yStar else ProbComp.uniform Target
          return (y, ((q, y) :: cache, hCount + 1))

/-- Explicit preimage inverter (`INV` reduction) for `saltedScheme`: guesses the forgery's fresh
direct-hash (or unqueried verification) index `jStar ← Fin (q_H + 1)`, embeds the challenge target
`yStar` there, simulates all signing queries via `sampleSimPair pk`, and outputs the candidate
preimage. -/
@[expose] noncomputable def saltedInverter [DecidableEq M]
    [Fintype Target] [Nonempty Target]
    (sys : TrapdoorPreimageSystem PK SK Target Preimage) (Salt : Type)
    [Fintype Salt] [Nonempty Salt] [DecidableEq Salt] (q_H : ℕ)
    (forger : PK → ProbOracleComp
      (ROMSignature.ForgerSpec M (M × Salt) (Salt × Option Preimage) Target)
      (M × (Salt × Option Preimage)))
    (pk : PK) (yStar : Target) : ProbComp (Option Preimage) := do
  let jStar ← ProbComp.uniform (Fin (q_H + 1))
  let ((_, (_, sigStar)), _) ←
    ((forger pk).runState (saltedInvHandler sys pk jStar.val yStar)).run ([], 0)
  return sigStar

/-! #### Proof of classical ROM EUF-CMA for `saltedScheme` -/

private noncomputable def saltedSamplePre {Salt : Type} [Fintype Target] [Finite Preimage]
    [Fintype Salt] [Nonempty Salt]
    (sys : TrapdoorPreimageSystem PK SK Target Preimage) (sk : SK) (_ : M) :
    PMF (Salt × (Target → Option Preimage)) := do
  let r ← PMF.uniformOfFintype Salt
  let f ← PMF.pi fun y => ProbComp.eval (sys.invert sk y)
  return (r, f)

private theorem saltedSamplePre_minEnt {Salt : Type} [Fintype Target]
    [Finite Preimage] [Fintype Salt] [Nonempty Salt]
    (sys : TrapdoorPreimageSystem PK SK Target Preimage) (sk : SK) (m : M) (q : M × Salt) :
    ((saltedSamplePre sys sk m).map (fun coins => (m, coins.1))) q ≤
      (Fintype.card Salt : ℝ≥0∞)⁻¹ := by
  have hmap : (saltedSamplePre sys sk m).map (fun coins => (m, coins.1)) =
      (PMF.uniformOfFintype Salt).map (fun r => (m, r)) := by
    simp only [saltedSamplePre, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
      PMF.map_bind, PMF.pure_map]
    refine congrArg ((PMF.uniformOfFintype Salt).bind ·) (funext fun r => ?_)
    have := (PMF.pi fun y => ProbComp.eval (sys.invert sk y)).map_const (m, r)
    simpa only [PMF.map, Function.comp_def, Function.const_apply] using this
  rw [hmap]
  have hinj : Function.Injective (fun r : Salt => (m, r)) := fun _ _ h => (Prod.mk.inj h).2
  simpa only [Function.comp_id] using
    RandomOracle.map_comp_apply_le_of_injective (g := id) hinj
      (fun r => by simpa only [PMF.map_id] using le_of_eq (PMF.uniformOfFintype_apply r)) q

/-- Exact game-0 representation of `ROMSignature.worldGame (saltedScheme sys Salt)` via
`RandomOracle.lazyProgramHandler`. -/
private theorem saltedWorldEufCma_eq_lazyProgram {Salt : Type} [DecidableEq M] [DecidableEq Salt]
    [DecidableEq Target] [Fintype Target] [Nonempty Target] [Finite Preimage]
    [Fintype Salt] [Nonempty Salt]
    (sys : TrapdoorPreimageSystem PK SK Target Preimage)
    (forger : PK → ProbOracleComp
      (ROMSignature.ForgerSpec M (M × Salt) (Salt × Option Preimage) Target)
      (M × (Salt × Option Preimage))) :
    ROMSignature.worldGame (saltedScheme sys Salt) forger eufCmaAccept =
      (ProbComp.eval sys.keyGen).bind fun keys =>
        (ProbOracleComp.runWith
          (RandomOracle.lazyProgramHandler
            (PMF.uniformOfFintype Target) (fun _ : M => true)
            (fun _ h => absurd h (by decide))
            (saltedSamplePre sys keys.2) (fun m coins => (m, coins.1))
            (fun m coins y log => ((coins.1, coins.2 y), m :: log)))
          (forger keys.1) ([], [])).bind fun ((mStar, (rStar, sigStar)), (cache, signed)) =>
            ((ROMSignature.oracle Target (mStar, rStar)).run cache).map fun (yStar, _) =>
              sys.check keys.1 yStar sigStar && !signed.contains mStar := by
  unfold ROMSignature.worldGame
  refine PMF.bind_congr_on_support _ _ _ fun ⟨pk, sk⟩ _ => ?_
  rw [ROMSignature.eval_world_worldRealize]
  have hstep :
      (ProbOracleComp.runWith (ROMSignature.forgerWorldImpl (saltedScheme sys Salt) sk)
        (ROMSignature.runLoggedForger (forger pk)) []).map
          (fun ⟨⟨msig, pairs⟩, cache⟩ => (msig, (cache, pairs.map Prod.fst))) =
      ProbOracleComp.runWith
        (RandomOracle.lazyProgramHandler
          (PMF.uniformOfFintype Target) (fun _ : M => true)
          (fun _ h => absurd h (by decide))
          (saltedSamplePre sys sk) (fun m coins => (m, coins.1))
          (fun m coins y log => ((coins.1, coins.2 y), m :: log)))
        (forger pk) ([], []) := by
    rw [ROMSignature.runLoggedForger, ProbOracleComp.runWith_run_interpret, PMF.map_comp]
    refine ProbOracleComp.runWith_map_state _ _
      (fun (st : List (M × (Salt × Option Preimage)) × List ((M × Salt) × Target)) =>
        (st.2, st.1.map Prod.fst))
      (fun q ⟨pairs, cache⟩ => ?_) (forger pk) ([], [])
    cases q with
    | inl m =>
      simp only [ROMSignature.logSigning, ROMSignature.forgerWorldImpl, saltedScheme,
        RandomOracle.lazyProgramHandler, saltedSamplePre, ProbOracleComp.runWith_bind,
        ProbOracleComp.runWith_query, ProbOracleComp.runWith_pure, sumHandler, StateT.run,
        interp_norm, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.map_bind, PMF.bind_bind,
        PMF.pure_bind, PMF.pure_map, ↓reduceDIte, ROMSignature.oracle]
      congr 1 with r : 1
      congr 1 with f : 1
      change ((memoize (fun _ => PMF.uniformOfFintype Target) (m, r) cache).bind
        fun x => PMF.pure ((r, f x.1), x.2)).bind
          (fun a => PMF.pure (a.1, a.2, List.map Prod.fst ((m, a.1) :: pairs))) = _
      rw [PMF.bind_bind]
      simp only [PMF.pure_bind, List.map_cons]
    | inr hq =>
      simp only [ROMSignature.logSigning, ROMSignature.forgerWorldImpl,
        RandomOracle.lazyProgramHandler, ProbOracleComp.runWith_bind,
        ProbOracleComp.runWith_query, ProbOracleComp.runWith_pure, sumHandler, StateT.run,
        PMF.monad_bind_eq_bind, PMF.map_bind, PMF.pure_map, ROMSignature.oracle]
      rfl
  rw [← hstep, PMF.bind_map]
  refine PMF.bind_congr_on_support _ _ _ fun ⟨⟨⟨mStar, rStar, sigStar⟩, pairs⟩, cache⟩ _ => ?_
  simp only [saltedScheme, eufCmaAccept, interp_norm, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]
  rfl

/-- Running an interpreted stateful `ProbOracleComp` against a memoryless `ProbComp` oracle `O`
coincides with `ProbOracleComp.runWith` against the evaluated handler. -/
private theorem eval_run_run_interpret {Q₁ Q₂ σ α : Type} {S₁ : Q₁ → Type} {S₂ : Q₂ → Type}
    (inner : (q : Q₁) → StateT σ (ProbOracleComp S₂) (S₁ q))
    (O : (q : Q₂) → ProbComp (S₂ q))
    (prog : ProbOracleComp S₁ α) (init : σ) :
    ProbComp.eval (((OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
        inner) prog).run init).run O) =
      ProbOracleComp.runWith (fun q s => ProbComp.eval ((inner q s).run O)) prog init := by
  have hunit :
      ∀ {β : Type} (p : ProbOracleComp S₂ β),
        ProbComp.eval (p.run O) =
          (ProbOracleComp.runWith (fun q (u : Unit) => (ProbComp.eval (O q)).map (·, u))
            p ()).map Prod.fst := by
    intro β p
    have h := ProbOracleComp.runWith_readOnly (fun q (_ : Unit) => ProbComp.eval (O q)) p ()
    have hfst := congrArg (PMF.map Prod.fst) h
    simp only [PMF.map_comp, Function.comp_def, PMF.map_id', OracleComp.evalWith_eq_interpret]
      at hfst
    rw [ProbOracleComp.eval_run]
    exact hfst.symm
  rw [hunit, ProbOracleComp.runWith_run_interpret, PMF.map_comp]
  have hmap := ProbOracleComp.runWith_map_state
    (fun q (st : σ × Unit) =>
      (ProbOracleComp.runWith (fun q' (u : Unit) => (ProbComp.eval (O q')).map (·, u))
        ((inner q).run st.1) st.2).map fun ⟨⟨a, b⟩, c⟩ => (a, b, c))
    (fun q s => ProbComp.eval ((inner q s).run O))
    Prod.fst
    (fun q ⟨s, u⟩ => by
      cases u
      rw [PMF.map_comp, hunit (inner q s)]
      rfl)
    prog (init, ())
  simpa only [Function.comp_def] using hmap

/-- Game 1 (overwrite programming) coincides exactly with `psExperimentReal` on
`saltedPSDistinguisher`. -/
private theorem saltedOverwrite_eq_psExperimentReal {Salt : Type} [DecidableEq M] [DecidableEq Salt]
    [DecidableEq Target] [Fintype Target] [Nonempty Target] [Finite Preimage]
    [Fintype Salt] [Nonempty Salt]
    (sys : TrapdoorPreimageSystem PK SK Target Preimage)
    (forger : PK → ProbOracleComp
      (ROMSignature.ForgerSpec M (M × Salt) (Salt × Option Preimage) Target)
      (M × (Salt × Option Preimage))) :
    (ProbComp.eval sys.keyGen).bind (fun keys =>
      (ProbOracleComp.runWith
        (RandomOracle.overwriteProgramHandler
          (PMF.uniformOfFintype Target) (fun _ : M => true)
          (fun _ h => absurd h (by decide))
          (saltedSamplePre sys keys.2) (fun m coins => (m, coins.1))
          (fun m coins y log => ((coins.1, coins.2 y), m :: log)))
        (forger keys.1) ([], [])).bind fun ((mStar, (rStar, sigStar)), (cache, signed)) =>
          ((ROMSignature.oracle Target (mStar, rStar)).run cache).map fun (yStar, _) =>
            sys.check keys.1 yStar sigStar && !signed.contains mStar) =
      ProbComp.eval (psExperimentReal sys (saltedPSDistinguisher sys Salt forger)) := by
  simp only [psExperimentReal, saltedPSDistinguisher, ProbComp.eval_bind,
    ProbOracleComp.run_bind]
  refine PMF.bind_congr_on_support _ _ _ fun ⟨pk, sk⟩ _ => ?_
  have hrun :
      ProbOracleComp.runWith
        (RandomOracle.overwriteProgramHandler
          (PMF.uniformOfFintype Target) (fun _ : M => true)
          (fun _ h => absurd h (by decide))
          (saltedSamplePre sys sk) (fun m coins => (m, coins.1))
          (fun m coins y log => ((coins.1, coins.2 y), m :: log)))
        (forger pk) ([], []) =
      ProbComp.eval (((OracleComp.interpret
        (OracleComp.sumHandler
          (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
          (saltedPSHandler (M := M) (Salt := Salt) (Target := Target) (Preimage := Preimage)))
        (forger pk)).run ([], [])).run fun _ => sys.sampleRealPair sk) := by
    rw [eval_run_run_interpret]
    congr 1
    funext q st
    obtain ⟨cache, signed⟩ := st
    cases q with
    | inl m =>
      simp only [RandomOracle.overwriteProgramHandler, saltedSamplePre, saltedPSHandler,
        TrapdoorPreimageSystem.sampleRealPair, ↓reduceDIte,
        ProbOracleComp.run_bind, ProbOracleComp.run_sample, ProbOracleComp.run_query,
        ProbOracleComp.run_pure, ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure,
        PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]
      congr 1 with r : 1
      rw [PMF.bind_comm]
      congr 1 with y : 1
      have heval := PMF.pi_map_eval (fun t => ProbComp.eval (sys.invert sk t)) y
      rw [← heval, PMF.bind_map]
      rfl
    | inr hq =>
      simp only [RandomOracle.overwriteProgramHandler, saltedPSHandler, memoize]
      cases hlu : cache.lookup hq with
      | some y =>
        simp [ProbOracleComp.run_pure, ProbComp.eval_pure, PMF.pure_map]
      | none =>
        simp only [ProbOracleComp.run_bind, ProbOracleComp.run_sample, ProbOracleComp.run_pure,
          ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure,
          PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.map_bind, PMF.pure_map]
  rw [hrun]
  refine PMF.bind_congr_on_support _ _ _ fun ⟨⟨mStar, rStar, sigStar⟩, cache, signed⟩ _ => ?_
  cases hlu : cache.lookup (mStar, rStar) with
  | some y =>
    rw [ROMSignature.run_oracle_of_lookup_eq_some hlu]
    simp [ProbOracleComp.run_pure, ProbComp.eval_pure]
  | none =>
    rw [ROMSignature.run_oracle_of_lookup_eq_none hlu]
    simp only [ProbOracleComp.run_bind, ProbOracleComp.run_sample, ProbOracleComp.run_pure,
      ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure, PMF.map_bind, PMF.pure_map]

/-- Tracked state for the Bellare–Rogaway guessing step in `saltedScheme`: cache stores each entry
tagged with `some idx` for fresh direct-hash misses and `none` for signing overwrites, alongside
`signed`, `hCount`, and `yAtJ` (the target sampled at step `jStar`, if reached). -/
private structure SaltedTrackState (M Salt Target : Type) where
  cache : List ((M × Salt) × (Target × Option ℕ))
  signed : List M
  hCount : ℕ
  yAtJ : Option Target

private noncomputable def saltedTrackHandler {Salt : Type} [DecidableEq M] [DecidableEq Salt]
    [Fintype Salt] [Nonempty Salt] [Fintype Target] [Nonempty Target]
    (sys : TrapdoorPreimageSystem PK SK Target Preimage) (pk : PK) (jStar : ℕ) :
    (q : M ⊕ (M × Salt)) →
      StateT (SaltedTrackState M Salt Target) PMF
        (ROMSignature.ForgerSpec M (M × Salt) (Salt × Option Preimage) Target q)
  | .inl m => fun st => do
      let r ← PMF.uniformOfFintype Salt
      let yx ← ProbComp.eval (sys.sampleSimPair pk)
      return ((r, yx.2),
        { st with
          cache := ((m, r), (yx.1, none)) :: st.cache
          signed := m :: st.signed })
  | .inr q => fun st =>
      match st.cache.lookup q with
      | some (y, _) => PMF.pure (y, st)
      | none => do
          let y ← PMF.uniformOfFintype Target
          return (y,
            { st with
              cache := (q, (y, some st.hCount)) :: st.cache
              hCount := st.hCount + 1
              yAtJ := if st.hCount = jStar then some y else st.yAtJ })

private noncomputable def saltedEmbedHandler {Salt : Type} [DecidableEq M] [DecidableEq Salt]
    [Fintype Salt] [Nonempty Salt] [Fintype Target] [Nonempty Target]
    (sys : TrapdoorPreimageSystem PK SK Target Preimage) (pk : PK) (jStar : ℕ) :
    (q : M ⊕ (M × Salt)) →
      StateT (SaltedTrackState M Salt Target × Target) PMF
        (ROMSignature.ForgerSpec M (M × Salt) (Salt × Option Preimage) Target q)
  | .inl m => fun (st, yStar) => do
      let r ← PMF.uniformOfFintype Salt
      let yx ← ProbComp.eval (sys.sampleSimPair pk)
      return ((r, yx.2),
        ({ st with
          cache := ((m, r), (yx.1, none)) :: st.cache
          signed := m :: st.signed }, yStar))
  | .inr q => fun (st, yStar) =>
      match st.cache.lookup q with
      | some (y, _) => PMF.pure (y, (st, yStar))
      | none =>
          if st.hCount = jStar then
            PMF.pure (yStar,
              ({ st with
                cache := (q, (yStar, some st.hCount)) :: st.cache
                hCount := st.hCount + 1
                yAtJ := some yStar }, yStar))
          else do
            let y ← PMF.uniformOfFintype Target
            return (y,
              ({ st with
                cache := (q, (y, some st.hCount)) :: st.cache
                hCount := st.hCount + 1 }, yStar))

/-- Invariant of `saltedTrackHandler`: `yAtJ` is `some _` iff `jStar < hCount`, every `none`-tagged
cache entry has its message in `signed`, every `some k`-tagged cache entry has `k < hCount`, and
any `some jStar`-tagged entry matches `yAtJ`. -/
private def SaltedTrackInv {Salt : Type} (jStar : ℕ) (st : SaltedTrackState M Salt Target) : Prop :=
  (st.hCount ≤ jStar → st.yAtJ = none) ∧
  (∀ m r y, ((m, r), (y, none)) ∈ st.cache → m ∈ st.signed) ∧
  (∀ q y k, (q, (y, some k)) ∈ st.cache → k < st.hCount) ∧
  (∀ q y, (q, (y, some jStar)) ∈ st.cache → st.yAtJ = some y)

private theorem saltedTrackInv_init {Salt : Type} (jStar : ℕ) :
    SaltedTrackInv (M := M) (Salt := Salt) (Target := Target) jStar ⟨[], [], 0, none⟩ := by
  refine ⟨fun _ => rfl, by simp, by simp, by simp⟩

private theorem saltedTrackInv_step {Salt : Type} [DecidableEq M] [DecidableEq Salt]
    [Fintype Salt] [Nonempty Salt] [Fintype Target] [Nonempty Target]
    (sys : TrapdoorPreimageSystem PK SK Target Preimage) (pk : PK) (jStar : ℕ)
    (q : M ⊕ (M × Salt)) (st : SaltedTrackState M Salt Target) (hinv : SaltedTrackInv jStar st)
    (a : ROMSignature.ForgerSpec M (M × Salt) (Salt × Option Preimage) Target q)
    (st' : SaltedTrackState M Salt Target)
    (hstep : (a, st') ∈ (saltedTrackHandler sys pk jStar q st).support) :
    SaltedTrackInv jStar st' := by
  obtain ⟨hnone, hsign, hlt, hyj⟩ := hinv
  cases q with
  | inl m =>
    simp only [saltedTrackHandler, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff, Prod.mk.injEq] at hstep
    obtain ⟨r, -, yx, -, -, rfl⟩ := hstep
    refine ⟨hnone, ?_, ?_, ?_⟩
    · intro m' r' y' hmem
      rcases List.mem_cons.mp hmem with heq | hmem
      · obtain ⟨hm, -⟩ := Prod.mk.inj (Prod.mk.inj heq).1
        subst hm; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hsign m' r' y' hmem)
    · intro q' y' k hmem
      rcases List.mem_cons.mp hmem with heq | hmem
      · simp at heq
      · exact hlt q' y' k hmem
    · intro q' y' hmem
      rcases List.mem_cons.mp hmem with heq | hmem
      · simp at heq
      · exact hyj q' y' hmem
  | inr hq =>
    dsimp only [saltedTrackHandler] at hstep
    cases hlu : st.cache.lookup hq with
    | some yk =>
      rw [hlu, PMF.mem_support_pure_iff, Prod.mk.injEq] at hstep
      obtain ⟨-, rfl⟩ := hstep
      exact ⟨hnone, hsign, hlt, hyj⟩
    | none =>
      rw [hlu] at hstep
      simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff,
        PMF.mem_support_pure_iff, Prod.mk.injEq] at hstep
      obtain ⟨y, -, -, rfl⟩ := hstep
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro hle
        dsimp only at hle ⊢
        have hne : st.hCount ≠ jStar := by omega
        simp [hne, hnone (by omega)]
      · intro m' r' y' hmem
        rcases List.mem_cons.mp hmem with heq | hmem
        · simp at heq
        · exact hsign m' r' y' hmem
      · intro q' y' k hmem
        dsimp only at hmem ⊢
        rcases List.mem_cons.mp hmem with heq | hmem
        · have hk := Option.some.inj (Prod.mk.inj (Prod.mk.inj heq).2).2
          subst hk; omega
        · exact Nat.lt_succ_of_lt (hlt q' y' k hmem)
      · intro q' y' hmem
        dsimp only at hmem ⊢
        rcases List.mem_cons.mp hmem with heq | hmem
        · have hy := (Prod.mk.inj (Prod.mk.inj heq).2).1
          have hk := Option.some.inj (Prod.mk.inj (Prod.mk.inj heq).2).2
          subst hy hk
          simp
        · have hne : st.hCount ≠ jStar := by
            have := hlt q' y' jStar hmem
            omega
          simp [hne, hyj q' y' hmem]

/-- Coupling relation between `saltedTrackHandler` (no pre-sampled `yStar`) and
`saltedEmbedHandler` (which embeds `yStar` at `hCount = jStar`). -/
private noncomputable def saltedRelate {Salt : Type} [Fintype Target] [Nonempty Target]
    (st : SaltedTrackState M Salt Target) : PMF (SaltedTrackState M Salt Target × Target) :=
  match st.yAtJ with
  | some y => PMF.pure (st, y)
  | none => (PMF.uniformOfFintype Target).map (st, ·)

private theorem saltedTrack_sim_saltedEmbed {Salt : Type} [DecidableEq M] [DecidableEq Salt]
    [Fintype Salt] [Nonempty Salt] [Fintype Target] [Nonempty Target]
    (sys : TrapdoorPreimageSystem PK SK Target Preimage) (pk : PK) (jStar : ℕ)
    (forger : ProbOracleComp
      (ROMSignature.ForgerSpec M (M × Salt) (Salt × Option Preimage) Target)
      (M × (Salt × Option Preimage))) :
    (ProbOracleComp.runWith (saltedTrackHandler sys pk jStar) forger ⟨[], [], 0, none⟩).bind
        (fun ⟨out, st⟩ => (saltedRelate st).map (out, ·)) =
      (PMF.uniformOfFintype Target).bind fun yStar =>
        ProbOracleComp.runWith (saltedEmbedHandler sys pk jStar) forger
          (⟨[], [], 0, none⟩, yStar) := by
  have hsim := ProbOracleComp.runWith_simulation_of_invariant
    (saltedTrackHandler sys pk jStar) (saltedEmbedHandler sys pk jStar)
    saltedRelate (SaltedTrackInv jStar)
    (saltedTrackInv_step sys pk jStar)
    (fun q st hinv => ?_)
    forger ⟨[], [], 0, none⟩ (saltedTrackInv_init jStar)
  · convert hsim using 1
    simp only [saltedRelate, PMF.bind_map]
    rfl
  · cases q with
    | inl m =>
      dsimp only [saltedTrackHandler, saltedEmbedHandler]
      cases hyj : st.yAtJ with
      | some y0 =>
        simp only [saltedRelate, hyj, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
          PMF.bind_bind, PMF.pure_bind, PMF.pure_map]
      | none =>
        simp only [saltedRelate, hyj, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
          PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]
        have hswap : ∀ r : Salt,
            ((ProbComp.eval (sys.sampleSimPair pk)).bind fun yx =>
              (PMF.uniformOfFintype Target).bind fun yStar =>
                PMF.pure ((r, yx.2),
                  (SaltedTrackState.mk (((m, r), (yx.1, none)) :: st.cache)
                    (m :: st.signed) st.hCount none, yStar))) =
            ((PMF.uniformOfFintype Target).bind fun yStar =>
              (ProbComp.eval (sys.sampleSimPair pk)).bind fun yx =>
                PMF.pure ((r, yx.2),
                  (SaltedTrackState.mk (((m, r), (yx.1, none)) :: st.cache)
                    (m :: st.signed) st.hCount none, yStar))) :=
          fun r => PMF.bind_comm _ _ _
        simp_rw [hswap]
        exact PMF.bind_comm _ _ _
    | inr hq =>
      dsimp only [saltedTrackHandler, saltedEmbedHandler]
      cases hlu : st.cache.lookup hq with
      | some yk =>
        cases hyj : st.yAtJ with
        | some y0 =>
          simp only [hlu, saltedRelate, hyj, PMF.map, PMF.pure_bind, Function.comp_def]
        | none =>
          simp only [saltedRelate, hyj, PMF.map, PMF.bind_bind, PMF.pure_bind, hlu,
            Function.comp_def]
      | none =>
        by_cases heq : st.hCount = jStar
        · have hyj : st.yAtJ = none := hinv.1 (le_of_eq heq)
          simp only [hlu, heq, ↓reduceIte, saltedRelate, hyj, PMF.monad_bind_eq_bind,
            PMF.monad_pure_eq_pure, PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]
        · cases hyj : st.yAtJ with
          | some y0 =>
            simp only [hlu, heq, ↓reduceIte, saltedRelate, hyj, PMF.monad_bind_eq_bind,
              PMF.monad_pure_eq_pure, PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]
          | none =>
            simp only [hlu, heq, ↓reduceIte, saltedRelate, hyj, PMF.monad_bind_eq_bind,
              PMF.monad_pure_eq_pure, PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]
            exact PMF.bind_comm _ _ _

private theorem lookup_map_fst {K A B : Type} [BEq K]
    (l : List (K × A × B)) (q : K) :
    (l.map fun (k, a, _) => (k, a)).lookup q = (l.lookup q).map Prod.fst := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k, a, b⟩
    simp only [List.map_cons, List.lookup_cons]
    cases (q == k) <;> simp [ih]

private theorem mem_of_lookup_eq_some {K V : Type} [DecidableEq K]
    {l : List (K × V)} {k : K} {v : V} (h : l.lookup k = some v) :
    (k, v) ∈ l := by
  induction l with
  | nil => simp at h
  | cons hd tl ih =>
    rcases hd with ⟨k', v'⟩
    simp only [List.lookup_cons] at h
    by_cases heq : k = k'
    · subst heq
      simp only [beq_self_eq_true, Option.some.injEq] at h
      subst h
      exact List.mem_cons_self
    · have hne : (k == k') = false := beq_false_of_ne heq
      rw [hne] at h
      exact List.mem_cons_of_mem _ (ih h)

/-- Key-fixed `G2` (simulated `PS` signing) is bounded by `(q_H + 1)` times the success of
`saltedInverter` on `Signature.targetExperiment`. -/
private theorem saltedSim_le_mul_targetExperiment {Salt : Type} [DecidableEq M] [DecidableEq Salt]
    [DecidableEq Target] [Fintype Salt] [Nonempty Salt] [Fintype Target] [Nonempty Target]
    (sys : TrapdoorPreimageSystem PK SK Target Preimage)
    (forger : PK → ProbOracleComp
      (ROMSignature.ForgerSpec M (M × Salt) (Salt × Option Preimage) Target)
      (M × (Salt × Option Preimage)))
    {q_S q_H : ℕ} (hforger : ProbForgerCallBounded forger q_S q_H) :
    (ProbComp.eval (psExperimentSim sys (saltedPSDistinguisher sys Salt forger))) true ≤
      ((q_H + 1 : ℕ) : ℝ≥0∞) *
        (ProbComp.eval (Signature.targetExperiment sys.toRawScheme
          (fun _ => ProbComp.uniform Target) (saltedInverter sys Salt q_H forger))) true := by
  unfold psExperimentSim Signature.targetExperiment
  dsimp only [TrapdoorPreimageSystem.toRawScheme]
  rw [ProbComp.eval_bind, ProbComp.eval_bind, PMF.bind_apply, PMF.bind_apply,
    ← ENNReal.tsum_mul_left]
  refine tsum_le_tsum fun ⟨pk, sk⟩ => ?_
  rw [← mul_assoc, mul_comm ((q_H + 1 : ℕ) : ℝ≥0∞), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  -- Express `psExperimentSim` at `pk` via `saltedTrackHandler` (with arbitrary `jStar`, say 0)
  let trackProj (jStar : Fin (q_H + 1)) :
      PMF (Bool × Fin (q_H + 1)) :=
    (ProbOracleComp.runWith (saltedTrackHandler sys pk jStar.val) (forger pk)
      ⟨[], [], 0, none⟩).bind fun ⟨⟨mStar, rStar, sigStar⟩, st⟩ =>
        match st.cache.lookup (mStar, rStar) with
        | some (y, idxOpt) =>
          PMF.pure (sys.check pk y sigStar && !st.signed.contains mStar,
            Fin.ofNat (q_H + 1) (idxOpt.getD st.hCount))
        | none =>
          (PMF.uniformOfFintype Target).map fun y =>
            (sys.check pk y sigStar && !st.signed.contains mStar,
              Fin.ofNat (q_H + 1) st.hCount)
  -- Wait: `trackProj jStar` has `PMF` independent of `jStar`!
  have htrack_indep (jStar : Fin (q_H + 1)) :
      (ProbOracleComp.runWith (saltedTrackHandler sys pk jStar.val) (forger pk)
        ⟨[], [], 0, none⟩).map (fun ⟨out, st⟩ => (out, (st.cache, st.signed, st.hCount))) =
      (ProbOracleComp.runWith (saltedTrackHandler sys pk 0) (forger pk)
        ⟨[], [], 0, none⟩).map (fun ⟨out, st⟩ => (out, (st.cache, st.signed, st.hCount))) := by
    have hmap (j : ℕ) :
        (ProbOracleComp.runWith (saltedTrackHandler sys pk j) (forger pk)
          ⟨[], [], 0, none⟩).map (fun ⟨out, st⟩ => (out, (st.cache, st.signed, st.hCount))) =
        ProbOracleComp.runWith
          (fun q ((cache, signed, hCount) :
              List ((M × Salt) × (Target × Option ℕ)) × List M × ℕ) =>
            match q with
            | .inl m => do
                let r ← PMF.uniformOfFintype Salt
                let yx ← ProbComp.eval (sys.sampleSimPair pk)
                return ((r, yx.2), (((m, r), (yx.1, none)) :: cache, m :: signed, hCount))
            | .inr hq =>
                match cache.lookup hq with
                | some (y, _) => PMF.pure (y, (cache, signed, hCount))
                | none => do
                    let y ← PMF.uniformOfFintype Target
                    return (y, ((hq, (y, some hCount)) :: cache, signed, hCount + 1)))
          (forger pk) ([], [], 0) := by
      refine ProbOracleComp.runWith_map_state _ _
        (fun (st : SaltedTrackState M Salt Target) => (st.cache, st.signed, st.hCount))
        (fun q st => ?_) (forger pk) (⟨[], [], 0, none⟩ : SaltedTrackState M Salt Target)
      cases q with
      | inl m =>
        simp [saltedTrackHandler, PMF.map_bind, PMF.pure_map]
      | inr hq =>
        dsimp only [saltedTrackHandler]
        cases st.cache.lookup hq <;> simp [PMF.map_bind, PMF.pure_map]
    rw [hmap jStar.val, hmap 0]
  have htrack_eq (jStar : Fin (q_H + 1)) : trackProj jStar = trackProj 0 := by
    dsimp only [trackProj]
    have h1 (j : Fin (q_H + 1)) :
        (ProbOracleComp.runWith (saltedTrackHandler sys pk j.val) (forger pk)
          ⟨[], [], 0, none⟩).bind (fun ⟨⟨mStar, rStar, sigStar⟩, st⟩ =>
            match st.cache.lookup (mStar, rStar) with
            | some (y, idxOpt) =>
              PMF.pure (sys.check pk y sigStar && !st.signed.contains mStar,
                Fin.ofNat (q_H + 1) (idxOpt.getD st.hCount))
            | none =>
              (PMF.uniformOfFintype Target).map fun y =>
                (sys.check pk y sigStar && !st.signed.contains mStar,
                  Fin.ofNat (q_H + 1) st.hCount)) =
        ((ProbOracleComp.runWith (saltedTrackHandler sys pk j.val) (forger pk)
          ⟨[], [], 0, none⟩).map (fun ⟨out, st⟩ => (out, (st.cache, st.signed, st.hCount)))).bind
          fun ⟨⟨mStar, rStar, sigStar⟩, (cache, signed, hCount)⟩ =>
            match cache.lookup (mStar, rStar) with
            | some (y, idxOpt) =>
              PMF.pure (sys.check pk y sigStar && !signed.contains mStar,
                Fin.ofNat (q_H + 1) (idxOpt.getD hCount))
            | none =>
              (PMF.uniformOfFintype Target).map fun y =>
                (sys.check pk y sigStar && !signed.contains mStar,
                  Fin.ofNat (q_H + 1) hCount) := by
      rw [PMF.bind_map]
      rfl
    rw [h1 jStar, h1 0, htrack_indep jStar]
    rfl
  -- Next, relate `psExperimentSim` at `pk` to `(trackProj 0).map Prod.fst`
  have hps_eq :
      (ProbComp.eval ((saltedPSDistinguisher sys Salt forger pk).run
        fun _ => sys.sampleSimPair pk)) = (trackProj 0).map Prod.fst := by
    have hproj :
        (ProbOracleComp.runWith (saltedTrackHandler sys pk 0) (forger pk)
          ⟨[], [], 0, none⟩).map
            (fun ⟨out, st⟩ => (out, (st.cache.map fun (k, y, _) => (k, y), st.signed))) =
        ProbComp.eval (((OracleComp.interpret
          (OracleComp.sumHandler
            (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
            (saltedPSHandler (M := M) (Salt := Salt) (Target := Target) (Preimage := Preimage)))
          (forger pk)).run ([], [])).run fun _ => sys.sampleSimPair pk) := by
      rw [eval_run_run_interpret]
      refine ProbOracleComp.runWith_map_state _ _
        (fun (st : SaltedTrackState M Salt Target) =>
          (st.cache.map fun (k, y, _) => (k, y), st.signed))
        (fun q st => ?_) (forger pk) ⟨[], [], 0, none⟩
      cases q with
      | inl m =>
        simp only [saltedTrackHandler, saltedPSHandler, ProbOracleComp.run_bind,
          ProbOracleComp.run_sample, ProbOracleComp.run_query, ProbOracleComp.run_pure,
          ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure, PMF.monad_bind_eq_bind,
          PMF.monad_pure_eq_pure, PMF.map_bind, PMF.pure_map]
        rfl
      | inr hq =>
        dsimp only [saltedTrackHandler, saltedPSHandler]
        rw [lookup_map_fst]
        cases st.cache.lookup hq with
        | some yk => simp [ProbOracleComp.run_pure, ProbComp.eval_pure, PMF.pure_map]
        | none =>
          simp only [Option.map_none, ProbOracleComp.run_bind, ProbOracleComp.run_sample,
            ProbOracleComp.run_pure, ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure,
            PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.map_bind, PMF.pure_map]
          rfl
    simp only [saltedPSDistinguisher, ProbOracleComp.run_bind, ProbComp.eval_bind, ← hproj,
      PMF.bind_map, trackProj, PMF.map_bind]
    refine PMF.bind_congr_on_support _ _ _ fun ⟨⟨mStar, rStar, sigStar⟩, st⟩ _ => ?_
    dsimp only [Function.comp_def]
    rw [lookup_map_fst]
    cases st.cache.lookup (mStar, rStar) with
    | some yk =>
      simp [ProbOracleComp.run_pure, ProbComp.eval_pure]
    | none =>
      simp only [Option.map_none, ProbOracleComp.run_bind, ProbOracleComp.run_sample,
        ProbOracleComp.run_pure, ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure,
        PMF.map_comp, Function.comp_def]
      exact (PMF.bind_pure_comp _ _).symm
  rw [hps_eq, uniform_fin_guess_mul (trackProj 0)]
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  -- Rewrite RHS to bind `jStar` on the outside and `yStar` inside
  have hrhs_swap :
      (ProbComp.eval (do
        let y ← ProbComp.uniform Target
        let s ← saltedInverter sys Salt q_H forger pk y
        return sys.check pk y s)) =
      (PMF.uniformOfFintype (Fin (q_H + 1))).bind fun jStar =>
        (PMF.uniformOfFintype Target).bind fun yStar =>
          (ProbComp.eval (((forger pk).runState
            (saltedInvHandler sys pk jStar.val yStar)).run ([], 0))).bind
              fun ⟨⟨_, _, sigStar⟩, _⟩ => PMF.pure (sys.check pk yStar sigStar) := by
    simp only [saltedInverter, ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure,
      PMF.bind_bind, PMF.pure_bind]
    exact PMF.bind_comm _ _ _
  rw [hrhs_swap, PMF.bind_apply, PMF.bind_apply]
  refine tsum_le_tsum fun jStar => mul_le_mul_of_nonneg_left ?_ zero_le
  rw [← htrack_eq jStar]
  -- Use `saltedTrack_sim_saltedEmbed` to equate `trackProj jStar` with the embedded run
  have hbound_hCount : ∀ out st,
      (out, st) ∈ (ProbOracleComp.runWith (saltedTrackHandler sys pk jStar.val) (forger pk)
        ⟨[], [], 0, none⟩).support → st.hCount ≤ q_H ∧ SaltedTrackInv jStar.val st := by
    intro out st hmem
    have h1 : st.hCount ≤ (⟨[], [], 0, none⟩ : SaltedTrackState M Salt Target).hCount + q_H := by
      have hcost := (hforger pk).2
      refine hcost.measure_le
        (oracle := OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n))
          (saltedTrackHandler sys pk jStar.val))
        (size := fun s : SaltedTrackState M Salt Target => s.hCount)
        (hstep := ?_)
        (s := ⟨[], [], 0, none⟩) (result := out) (s' := st)
        (hmem := by simpa [ProbOracleComp.runWith_eq_run_interpret] using hmem)
      intro q s a s' hx
      cases q with
      | inl n =>
        simp only [OracleComp.sumHandler, StateT.lift, PMF.monad_bind_eq_bind,
          PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff,
          Prod.mk.injEq] at hx
        obtain ⟨_, -, -, rfl⟩ := hx
        exact le_rfl
      | inr oq =>
        cases oq with
        | inl m =>
          simp only [OracleComp.sumHandler, saltedTrackHandler, PMF.monad_bind_eq_bind,
            PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff,
            Prod.mk.injEq] at hx
          obtain ⟨_, -, _, -, -, rfl⟩ := hx
          exact le_rfl
        | inr hq =>
          simp only [OracleComp.sumHandler, saltedTrackHandler] at hx
          cases hlu : s.cache.lookup hq with
          | some yk =>
            rw [hlu, PMF.mem_support_pure_iff, Prod.mk.injEq] at hx
            obtain ⟨-, rfl⟩ := hx
            exact Nat.le_succ _
          | none =>
            rw [hlu] at hx
            simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
              PMF.mem_support_bind_iff, PMF.mem_support_pure_iff, Prod.mk.injEq] at hx
            obtain ⟨_, -, -, rfl⟩ := hx
            exact le_rfl
    have h2 := ProbOracleComp.runWith_invariant (saltedTrackHandler sys pk jStar.val)
      (SaltedTrackInv jStar.val) (saltedTrackInv_step sys pk jStar.val)
      (forger pk) ⟨[], [], 0, none⟩ (saltedTrackInv_init jStar.val) out st hmem
    exact ⟨by simpa using h1, h2⟩
  -- Relate `saltedEmbedHandler` to `saltedInvHandler` using invariant `st.2 = yStar`
  have hembed_to_inv (yStar : Target) :
      (ProbOracleComp.runWith (saltedEmbedHandler sys pk jStar.val) (forger pk)
        (⟨[], [], 0, none⟩, yStar)).map (fun ⟨(_, _, sigStar), _⟩ => sigStar) =
      (ProbComp.eval (((forger pk).runState
        (saltedInvHandler sys pk jStar.val yStar)).run ([], 0))).map
        (fun ⟨(_, _, sigStar), _⟩ => sigStar) := by
    rw [ProbOracleComp.eval_runState]
    have hproj := ProbOracleComp.runWith_map_state_of_invariant
      (saltedEmbedHandler sys pk jStar.val)
      (fun q s => ProbComp.eval (saltedInvHandler sys pk jStar.val yStar q s))
      (fun (st : SaltedTrackState M Salt Target × Target) =>
        (st.1.cache.map fun (k, y, _) => (k, y), st.1.hCount))
      (fun st => st.2 = yStar)
      (fun q ⟨st, yS⟩ hyS a ⟨st', yS'⟩ hstep => by
        subst hyS
        cases q with
        | inl m =>
          simp only [saltedEmbedHandler, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
            PMF.mem_support_bind_iff, PMF.mem_support_pure_iff, Prod.mk.injEq] at hstep
          obtain ⟨_, -, _, -, -, -, rfl⟩ := hstep
          rfl
        | inr hq =>
          dsimp only [saltedEmbedHandler] at hstep
          cases hlu : st.cache.lookup hq with
          | some yk =>
            rw [hlu, PMF.mem_support_pure_iff, Prod.mk.injEq] at hstep
            obtain ⟨-, -, rfl⟩ := hstep; rfl
          | none =>
            rw [hlu] at hstep
            split_ifs at hstep with heq
            · rw [PMF.mem_support_pure_iff, Prod.mk.injEq] at hstep
              obtain ⟨-, -, rfl⟩ := hstep; rfl
            · simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
                PMF.mem_support_bind_iff, PMF.mem_support_pure_iff, Prod.mk.injEq] at hstep
              obtain ⟨_, -, -, -, rfl⟩ := hstep; rfl)
      (fun q ⟨st, yS⟩ hyS => by
        subst hyS
        cases q with
        | inl m =>
          simp only [saltedEmbedHandler, saltedInvHandler, ProbComp.eval_bind,
            ProbComp.eval_uniform, ProbComp.eval_pure, PMF.monad_bind_eq_bind,
            PMF.monad_pure_eq_pure, PMF.map_bind, PMF.pure_map]
          rfl
        | inr hq =>
          dsimp only [saltedEmbedHandler, saltedInvHandler]
          rw [lookup_map_fst]
          cases st.cache.lookup hq with
          | some yk => simp [ProbComp.eval_pure, PMF.pure_map]
          | none =>
            by_cases heq : st.hCount = jStar.val
            · simp [Option.map_none, heq, ProbComp.eval_pure, PMF.pure_map]
            · simp only [Option.map_none, heq, ↓reduceIte, ProbComp.eval_bind,
                ProbComp.eval_uniform, ProbComp.eval_pure, PMF.monad_bind_eq_bind,
                PMF.monad_pure_eq_pure, PMF.map_bind, PMF.pure_map]
              rfl)
      (forger pk) (⟨[], [], 0, none⟩, yStar) rfl
    have hcongr := congrArg (PMF.map fun ((_, _, sigStar), _) => sigStar) hproj
    simpa only [PMF.map_comp, Function.comp_def, List.map_nil] using hcongr
  -- Now compare `(trackProj jStar).map (fun p => p.1 && decide (p.2 = jStar)) true` with
  -- `((PMF.uniformOfFintype Target).bind fun yStar => ... check pk yStar sigStar) true`
  have hcheck_rhs :
      ((PMF.uniformOfFintype Target).bind fun yStar =>
        (ProbComp.eval (((forger pk).runState
          (saltedInvHandler sys pk jStar.val yStar)).run ([], 0))).bind
            fun ⟨⟨_, _, sigStar⟩, _⟩ => PMF.pure (sys.check pk yStar sigStar)) true =
      ((PMF.uniformOfFintype Target).bind fun yStar =>
        (ProbOracleComp.runWith (saltedEmbedHandler sys pk jStar.val) (forger pk)
          (⟨[], [], 0, none⟩, yStar)).map fun ⟨⟨_, _, sigStar⟩, _⟩ =>
            sys.check pk yStar sigStar) true := by
    congr 1
    refine congrArg ((PMF.uniformOfFintype Target).bind ·) (funext fun yStar => ?_)
    have h1 := congrArg (PMF.map (sys.check pk yStar)) (hembed_to_inv yStar)
    simpa only [PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def] using h1.symm
  rw [hcheck_rhs]
  have hsim_eq := congrArg
    (PMF.map fun ⟨⟨_, _, sigStar⟩, _, yStar⟩ => sys.check pk yStar sigStar)
    (saltedTrack_sim_saltedEmbed sys pk jStar.val (forger pk))
  have hrhs_track :
      ((PMF.uniformOfFintype Target).bind fun yStar =>
        (ProbOracleComp.runWith (saltedEmbedHandler sys pk jStar.val) (forger pk)
          (⟨[], [], 0, none⟩, yStar)).map fun ⟨⟨_, _, sigStar⟩, _⟩ =>
            sys.check pk yStar sigStar) =
      (ProbOracleComp.runWith (saltedTrackHandler sys pk jStar.val) (forger pk)
        ⟨[], [], 0, none⟩).bind fun ⟨⟨_, _, sigStar⟩, st⟩ =>
          (saltedRelate st).map fun ⟨_, yStar⟩ => sys.check pk yStar sigStar := by
    have h1 :
        ((PMF.uniformOfFintype Target).bind fun yStar =>
          (ProbOracleComp.runWith (saltedEmbedHandler sys pk jStar.val) (forger pk)
            (⟨[], [], 0, none⟩, yStar)).map fun ⟨⟨_, _, sigStar⟩, _⟩ =>
              sys.check pk yStar sigStar) =
        ((PMF.uniformOfFintype Target).bind fun yStar =>
          ProbOracleComp.runWith (saltedEmbedHandler sys pk jStar.val) (forger pk)
            (⟨[], [], 0, none⟩, yStar)).map
              (fun ⟨⟨_, _, sigStar⟩, _, yS⟩ => sys.check pk yS sigStar) := by
      rw [PMF.map_bind]
      refine PMF.bind_congr_on_support _ _ _ fun yStar _ => ?_
      simp only [PMF.map]
      refine PMF.bind_congr_on_support _ _ _ fun ⟨out, st, yS⟩ hmem => ?_
      have hyS : yS = yStar := ProbOracleComp.runWith_invariant
        (saltedEmbedHandler sys pk jStar.val) (fun s => s.2 = yStar)
        (fun q ⟨st, y'⟩ hy' a ⟨st', y''⟩ hstep => by
          subst hy'
          cases q with
          | inl m =>
            simp only [saltedEmbedHandler, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
              PMF.mem_support_bind_iff, PMF.mem_support_pure_iff, Prod.mk.injEq] at hstep
            obtain ⟨_, -, _, -, -, -, rfl⟩ := hstep; rfl
          | inr hq =>
            dsimp only [saltedEmbedHandler] at hstep
            cases hlu : st.cache.lookup hq with
            | some yk =>
              rw [hlu, PMF.mem_support_pure_iff, Prod.mk.injEq] at hstep
              obtain ⟨-, -, rfl⟩ := hstep; rfl
            | none =>
              rw [hlu] at hstep
              split_ifs at hstep with heq
              · rw [PMF.mem_support_pure_iff, Prod.mk.injEq] at hstep
                obtain ⟨-, -, rfl⟩ := hstep; rfl
              · simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
                  PMF.mem_support_bind_iff, PMF.mem_support_pure_iff, Prod.mk.injEq] at hstep
                obtain ⟨_, -, -, -, rfl⟩ := hstep; rfl)
        (forger pk) (⟨[], [], 0, none⟩, yStar) rfl out (st, yS) hmem
      simp [hyS]
    rw [h1, ← hsim_eq, PMF.map_bind]
    refine PMF.bind_congr_on_support _ _ _ fun ⟨⟨_, _, sigStar⟩, st⟩ _ => ?_
    simp [PMF.map_comp, Function.comp_def]
  rw [hrhs_track]
  dsimp only [trackProj]
  rw [PMF.map_bind]
  refine PMF.bind_apply_mono_on_support _ _ fun ⟨⟨mStar, rStar, sigStar⟩, st⟩ hmem => ?_
  obtain ⟨hcount_le, hnone, hsign, hlt, hyj⟩ := hbound_hCount (mStar, (rStar, sigStar)) st hmem
  have hL :
      ((match st.cache.lookup (mStar, rStar) with
        | some (y, idxOpt) =>
            PMF.pure (sys.check pk y sigStar && !st.signed.contains mStar,
              Fin.ofNat (q_H + 1) (idxOpt.getD st.hCount))
        | none =>
            (PMF.uniformOfFintype Target).map fun y =>
              (sys.check pk y sigStar && !st.signed.contains mStar,
                Fin.ofNat (q_H + 1) st.hCount)).map
        fun (p : Bool × Fin (q_H + 1)) => p.1 && decide (p.2 = jStar)) true =
      ((match st.cache.lookup (mStar, rStar) with
        | some (y, idxOpt) =>
            PMF.pure ((sys.check pk y sigStar && !st.signed.contains mStar) &&
              decide (Fin.ofNat (q_H + 1) (idxOpt.getD st.hCount) = jStar))
        | none =>
            (PMF.uniformOfFintype Target).map fun y =>
              (sys.check pk y sigStar && !st.signed.contains mStar) &&
                decide (Fin.ofNat (q_H + 1) st.hCount = jStar)) true) := by
    cases st.cache.lookup (mStar, rStar) <;>
      simp [PMF.pure_map, PMF.map_comp, Function.comp_def]
  have hR :
      ((saltedRelate st).map fun ⟨_, yStar⟩ => sys.check pk yStar sigStar) true =
      ((match st.yAtJ with
        | some yStar => PMF.pure (sys.check pk yStar sigStar)
        | none => (PMF.uniformOfFintype Target).map fun yStar => sys.check pk yStar sigStar)
        true) := by
    cases hy : st.yAtJ <;>
      simp [saltedRelate, hy, PMF.pure_map, PMF.map_comp, Function.comp_def]
  rw [hL, hR]
  refine targetHit_le_yAtJ_check sys pk sigStar (!st.signed.contains mStar) st.hCount jStar
    st.yAtJ (st.cache.lookup (mStar, rStar)) hcount_le hnone ?_ ?_ ?_
  · intro y hlu
    simp [hsign mStar rStar y (mem_of_lookup_eq_some hlu)]
  · intro y k hlu
    exact hlt (mStar, rStar) y k (mem_of_lookup_eq_some hlu)
  · intro y hlu
    exact hyj (mStar, rStar) y (mem_of_lookup_eq_some hlu)

/-- **Classical ROM EUF-CMA reduction for salted hash-and-sign (`ProbOracleComp` form)**,
after `[KosugeXagawa2022]`, Theorem 1 (classical-ROM specialization, p. 18) and Figure 4, adapted
for finite classical adversaries with explicit `Option Preimage` failure (no retry, so `q'_sign =
q_sign`) and concrete salt-collision slack: for any probabilistic ROM forger making at most `q_S`
signing queries and `q_H` direct hash queries,
`Pr[EUF-CMA] ≤ (q_H + 1) * Pr[INV(saltedInverter)] + Adv^PS(saltedPSDistinguisher) +`
`(q_S * q_H + q_S.choose 2) / |Salt|`.
Every reduction is an explicit finite program with query bounds (no runtime certificate claimed;
tracked in #7068). -/
theorem saltedRomWorldEufCma_succProbability_le {Salt : Type} [DecidableEq M] [DecidableEq Salt]
    [DecidableEq Target] [Fintype Salt] [Nonempty Salt] [Fintype Target] [Nonempty Target]
    [Finite Preimage]
    (sys : TrapdoorPreimageSystem PK SK Target Preimage)
    (forger : PK → ProbOracleComp
      (ROMSignature.ForgerSpec M (M × Salt) (Salt × Option Preimage) Target)
      (M × (Salt × Option Preimage)))
    {q_S q_H : ℕ} (hforger : ProbForgerCallBounded forger q_S q_H) :
    Game.succProbability
        (ROMSignature.worldGame (saltedScheme sys Salt) forger eufCmaAccept) ≤
      (q_H + 1 : ℝ≥0) *
        Experiment.succProbability
          (Signature.targetExperiment sys.toRawScheme (fun _ => ProbComp.uniform Target)
            (saltedInverter sys Salt q_H forger)) +
      Experiment.advantage
        (psExperimentReal sys (saltedPSDistinguisher sys Salt forger))
        (psExperimentSim sys (saltedPSDistinguisher sys Salt forger)) +
      ((q_S * q_H + q_S.choose 2 : ℕ) : ℝ≥0) * (Fintype.card Salt : ℝ≥0)⁻¹ := by
  have h_enn :
      (ROMSignature.worldGame (saltedScheme sys Salt) forger eufCmaAccept) true ≤
        ((q_H + 1 : ℕ) : ℝ≥0∞) *
          (ProbComp.eval (Signature.targetExperiment sys.toRawScheme
            (fun _ => ProbComp.uniform Target) (saltedInverter sys Salt q_H forger))) true +
        (Experiment.advantage
          (psExperimentReal sys (saltedPSDistinguisher sys Salt forger))
          (psExperimentSim sys (saltedPSDistinguisher sys Salt forger)) : ℝ≥0∞) +
        ((q_S * q_H + q_S.choose 2 : ℕ) : ℝ≥0∞) * (Fintype.card Salt : ℝ≥0∞)⁻¹ := by
    -- Hop 0 → 1: lazy → overwrite via `Programming.lean`
    have hclose01 :
        CloseTo
          (ROMSignature.worldGame (saltedScheme sys Salt) forger eufCmaAccept)
          (ProbComp.eval (psExperimentReal sys (saltedPSDistinguisher sys Salt forger)))
          ((q_S * q_H + q_S.choose 2 : ℕ) * (Fintype.card Salt : ℝ≥0∞)⁻¹) := by
      rw [saltedWorldEufCma_eq_lazyProgram, ← saltedOverwrite_eq_psExperimentReal]
      refine CloseTo.bind_right (ProbComp.eval sys.keyGen) fun ⟨pk, sk⟩ _ => ?_
      have hprog :=
        RandomOracle.closeTo_runWith_lazyProgramHandler_overwriteProgramHandler_choose_two
        (PMF.uniformOfFintype Target) (fun _ : M => true)
        (fun _ h => absurd h (by decide))
        (saltedSamplePre sys sk) (fun m coins => (m, coins.1))
        (fun m coins y log => ((coins.1, coins.2 y), m :: log))
        (fun m _ q => saltedSamplePre_minEnt sys sk m q)
        ((hforger pk).1.of_le fun q => by rcases q with _ | _ | _ <;> rfl)
        ((hforger pk).2.of_le fun q => by rcases q with _ | _ | _ <;> rfl) [] []
      simpa only [List.length_nil, mul_zero, zero_add] using hprog.bind_left _
    have h01 :
        (ROMSignature.worldGame (saltedScheme sys Salt) forger eufCmaAccept) true ≤
          (ProbComp.eval (psExperimentReal sys (saltedPSDistinguisher sys Salt forger))) true +
            ((q_S * q_H + q_S.choose 2 : ℕ) : ℝ≥0∞) * (Fintype.card Salt : ℝ≥0∞)⁻¹ := by
      simpa only [PMF.toOuterMeasure_apply_singleton] using hclose01 {true}
    -- Hop 1 → 2: `psExperimentReal` → `psExperimentSim`
    have h12 :
        (ProbComp.eval (psExperimentReal sys (saltedPSDistinguisher sys Salt forger))) true ≤
          (ProbComp.eval (psExperimentSim sys (saltedPSDistinguisher sys Salt forger))) true +
            (Experiment.advantage
              (psExperimentReal sys (saltedPSDistinguisher sys Salt forger))
              (psExperimentSim sys (saltedPSDistinguisher sys Salt forger)) : ℝ≥0∞) := by
      have hc := (Game.closeTo_iff_coe_advantage_le
        (game1 := ProbComp.eval (psExperimentReal sys (saltedPSDistinguisher sys Salt forger)))
        (game2 := ProbComp.eval (psExperimentSim sys (saltedPSDistinguisher sys Salt forger)))).mpr
        le_rfl
      simpa only [PMF.toOuterMeasure_apply_singleton] using hc {true}
    -- Hop 2 → 3: `psExperimentSim` → `(q_H + 1) * INV`
    have h23 := saltedSim_le_mul_targetExperiment sys forger hforger
    calc (ROMSignature.worldGame (saltedScheme sys Salt) forger eufCmaAccept) true
        ≤ (ProbComp.eval (psExperimentReal sys (saltedPSDistinguisher sys Salt forger))) true +
            ((q_S * q_H + q_S.choose 2 : ℕ) : ℝ≥0∞) * (Fintype.card Salt : ℝ≥0∞)⁻¹ := h01
      _ ≤ ((ProbComp.eval (psExperimentSim sys (saltedPSDistinguisher sys Salt forger))) true +
            (Experiment.advantage
              (psExperimentReal sys (saltedPSDistinguisher sys Salt forger))
              (psExperimentSim sys (saltedPSDistinguisher sys Salt forger)) : ℝ≥0∞)) +
            ((q_S * q_H + q_S.choose 2 : ℕ) : ℝ≥0∞) * (Fintype.card Salt : ℝ≥0∞)⁻¹ :=
          add_le_add h12 le_rfl
      _ ≤ (((q_H + 1 : ℕ) : ℝ≥0∞) *
            (ProbComp.eval (Signature.targetExperiment sys.toRawScheme
              (fun _ => ProbComp.uniform Target) (saltedInverter sys Salt q_H forger))) true +
            (Experiment.advantage
              (psExperimentReal sys (saltedPSDistinguisher sys Salt forger))
              (psExperimentSim sys (saltedPSDistinguisher sys Salt forger)) : ℝ≥0∞)) +
            ((q_S * q_H + q_S.choose 2 : ℕ) : ℝ≥0∞) * (Fintype.card Salt : ℝ≥0∞)⁻¹ :=
          add_le_add (add_le_add h23 le_rfl) le_rfl
  rw [← ENNReal.coe_le_coe]
  have hcast :
      (((q_H + 1 : ℝ≥0) *
        Experiment.succProbability
          (Signature.targetExperiment sys.toRawScheme (fun _ => ProbComp.uniform Target)
            (saltedInverter sys Salt q_H forger)) +
        Experiment.advantage
          (psExperimentReal sys (saltedPSDistinguisher sys Salt forger))
          (psExperimentSim sys (saltedPSDistinguisher sys Salt forger)) +
        ((q_S * q_H + q_S.choose 2 : ℕ) : ℝ≥0) * (Fintype.card Salt : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) =
      ((q_H + 1 : ℕ) : ℝ≥0∞) *
        (ProbComp.eval (Signature.targetExperiment sys.toRawScheme
          (fun _ => ProbComp.uniform Target) (saltedInverter sys Salt q_H forger))) true +
        (Experiment.advantage
          (psExperimentReal sys (saltedPSDistinguisher sys Salt forger))
          (psExperimentSim sys (saltedPSDistinguisher sys Salt forger)) : ℝ≥0∞) +
        ((q_S * q_H + q_S.choose 2 : ℕ) : ℝ≥0∞) * (Fintype.card Salt : ℝ≥0∞)⁻¹ := by
    have hcard_ne : (Fintype.card Salt : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp only [Experiment.succProbability, Game.coe_succProbability_ennreal, ENNReal.coe_add,
      ENNReal.coe_mul, ENNReal.coe_natCast, ENNReal.coe_one, ENNReal.coe_inv hcard_ne]
    simp only [Nat.cast_add, Nat.cast_one]
  rw [Game.coe_succProbability_ennreal, hcast]
  exact h_enn

/-- Lift a `ROMSignature.Forger` whose coin distribution is realized by `coinSampler : ProbComp`
into a `ProbOracleComp` forger. -/
@[expose] def liftForger {PK M Sig Query Digest : Type}
    (A : ROMSignature.Forger PK M Sig Query Digest) (coinSampler : ProbComp A.Coins)
    (pk : PK) : ProbOracleComp (ROMSignature.ForgerSpec M Query Sig Digest) (M × Sig) := do
  let coins ← ProbOracleComp.sample coinSampler
  ROMSignature.liftOracleForger (A.forge pk coins)

/-- `liftForger` preserves both signing and hash call budgets. -/
theorem probForgerCallBounded_liftForger {PK M Sig Query Digest : Type}
    {A : ROMSignature.Forger PK M Sig Query Digest} (coinSampler : ProbComp A.Coins)
    {q_S q_H : ℕ} (hA : A.CallBounded q_S q_H) :
    ProbForgerCallBounded (liftForger A coinSampler) q_S q_H := by
  intro pk
  refine ⟨?_, ?_⟩
  · simpa only [liftForger, zero_add] using
      (ProbOracleComp.isCostBounded_sample ROMSignature.signingCost coinSampler).bind
        fun coins => (probForgerCallBounded_liftOracleForger hA coins pk).1
  · simpa only [liftForger, zero_add] using
      (ProbOracleComp.isCostBounded_sample ROMSignature.hashCost coinSampler).bind
        fun coins => (probForgerCallBounded_liftOracleForger hA coins pk).2

/-- When `A.coins = ProbComp.eval coinSampler`, `ROMSignature.eufCmaGame scheme A` equals
`ROMSignature.worldGame scheme (liftForger A coinSampler) eufCmaAccept`. -/
theorem eufCmaGame_eq_worldGame_liftForger {PK SK M Sig Query Digest : Type}
    [DecidableEq M] [DecidableEq Query] [Fintype Digest] [Nonempty Digest]
    (scheme : ROMSignature.Scheme PK SK M Sig Query Digest)
    (A : ROMSignature.Forger PK M Sig Query Digest) (coinSampler : ProbComp A.Coins)
    (hcoins : A.coins = ProbComp.eval coinSampler) :
    ROMSignature.eufCmaGame scheme A =
      ROMSignature.worldGame scheme (liftForger A coinSampler) eufCmaAccept := by
  rw [ROMSignature.eufCmaGame_eq_worldGame, hcoins]
  unfold ROMSignature.worldGame
  refine PMF.bind_congr_on_support _ _ _ fun ⟨pk, sk⟩ _ => ?_
  simp only [ROMSignature.eval_world_worldRealize, liftForger, ROMSignature.runLoggedForger,
    eufCmaAccept, ProbOracleComp.runWith_bind, OracleComp.interpret_bind, StateT.run_bind]
  have hsample :
      ProbOracleComp.runWith (ROMSignature.forgerWorldImpl scheme sk)
        ((OracleComp.interpret
          (OracleComp.sumHandler
            (fun n => StateT.lift (ProbOracleComp.sample
              (spec := ROMSignature.ForgerSpec M Query Sig Digest) (ProbComp.unifFin n)))
            (ROMSignature.logSigning (M := M) (Sig := Sig) (Query := Query) (Digest := Digest)))
          (ProbOracleComp.sample
            (spec := ROMSignature.ForgerSpec M Query Sig Digest) coinSampler)).run []) [] =
      (ProbComp.eval coinSampler).map fun c => ((c, ([] : List (M × Sig))), []) := by
    rw [ProbOracleComp.runWith_run_interpret, ProbOracleComp.runWith_sample, PMF.map_comp]
    rfl
  rw [hsample, PMF.bind_map]
  simp only [PMF.monad_bind_eq_bind, PMF.bind_bind]
  rfl

/-- **Classical ROM EUF-CMA reduction for salted hash-and-sign (`ROMSignature.eufCmaGame` form)**,
after `[KosugeXagawa2022]`, Theorem 1 (classical-ROM specialization, p. 18), without retry.
Applies to `ROMSignature.Forger` adversaries whose coin distribution `A.coins` is realized by a
finite `ProbComp A.Coins` sampler (`hcoins : A.coins = ProbComp.eval coinSampler`). -/
theorem eufCmaGame_saltedScheme_succProbability_le {Salt : Type} [DecidableEq M] [DecidableEq Salt]
    [DecidableEq Target] [Fintype Salt] [Nonempty Salt] [Fintype Target] [Nonempty Target]
    [Finite Preimage]
    (sys : TrapdoorPreimageSystem PK SK Target Preimage)
    (A : ROMSignature.Forger PK M (Salt × Option Preimage) (M × Salt) Target)
    (coinSampler : ProbComp A.Coins) (hcoins : A.coins = ProbComp.eval coinSampler)
    {q_S q_H : ℕ} (hA : A.CallBounded q_S q_H) :
    Game.succProbability (ROMSignature.eufCmaGame (saltedScheme sys Salt) A) ≤
      (q_H + 1 : ℝ≥0) *
        Experiment.succProbability
          (Signature.targetExperiment sys.toRawScheme (fun _ => ProbComp.uniform Target)
            (saltedInverter sys Salt q_H (liftForger A coinSampler))) +
      Experiment.advantage
        (psExperimentReal sys (saltedPSDistinguisher sys Salt (liftForger A coinSampler)))
        (psExperimentSim sys (saltedPSDistinguisher sys Salt (liftForger A coinSampler))) +
      ((q_S * q_H + q_S.choose 2 : ℕ) : ℝ≥0) * (Fintype.card Salt : ℝ≥0)⁻¹ := by
  rw [eufCmaGame_eq_worldGame_liftForger (saltedScheme sys Salt) A coinSampler hcoins]
  exact saltedRomWorldEufCma_succProbability_le sys (liftForger A coinSampler)
    (probForgerCallBounded_liftForger coinSampler hA)

end SaltedReduction

/-! ### Classical ROM EUF-CMA for deterministic unsalted hash-and-sign -/

section DetReduction

variable {PK SK M Target Preimage : Type}

/-- Adding two `OracleComp.IsCostBounded` bounds bounds the pointwise sum of costs. -/
private theorem isCostBounded_add {ι : Type} {spec : ι → Type} {α : Type}
    {c₁ c₂ : ι → ℕ} {p : OracleComp spec α} {k₁ k₂ : ℕ}
    (h₁ : OracleComp.IsCostBounded c₁ p k₁) (h₂ : OracleComp.IsCostBounded c₂ p k₂) :
    OracleComp.IsCostBounded (fun q => c₁ q + c₂ q) p (k₁ + k₂) := by
  induction p generalizing k₁ k₂ with
  | pure a => exact .pure a (k₁ + k₂)
  | liftBind q cont ih =>
    obtain ⟨h1le, h1c⟩ := OracleComp.IsCostBounded.liftBind_iff.mp h₁
    obtain ⟨h2le, h2c⟩ := OracleComp.IsCostBounded.liftBind_iff.mp h₂
    refine OracleComp.IsCostBounded.liftBind_iff.mpr ⟨by omega, fun a => ?_⟩
    have hsub : k₁ - c₁ q + (k₂ - c₂ q) = k₁ + k₂ - (c₁ q + c₂ q) := by omega
    rw [← hsub]
    exact ih a (h1c a) (h2c a)

/-- Any `ProbForgerCallBounded forger q_S q_H` makes at most `q_S + q_H` total external queries. -/
theorem ProbForgerCallBounded.isQueryBounded {Sig Query Digest : Type}
    {forger : PK → ProbOracleComp (ROMSignature.ForgerSpec M Query Sig Digest) (M × Sig)}
    {q_S q_H : ℕ} (hforger : ProbForgerCallBounded forger q_S q_H) (pk : PK) :
    (forger pk).IsQueryBounded (q_S + q_H) := by
  have hadd := isCostBounded_add (hforger pk).1 (hforger pk).2
  have hcost : (fun q : ℕ ⊕ (M ⊕ Query) =>
      Sum.elim (fun _ => 0) (ROMSignature.signingCost (M := M) (Query := Query)) q +
        Sum.elim (fun _ => 0) (ROMSignature.hashCost (M := M) (Query := Query)) q) =
      Sum.elim (fun _ => 0) (fun _ => 1) := by
    funext q
    rcases q with n | (m | hq) <;> rfl
  simpa only [ProbOracleComp.IsQueryBounded, hcost] using hadd

/-- Stateful `PS`-oracle handler simulating `detScheme` for `detPSDistinguisher`. Every fresh
message `m` (whether queried via `Sign` or `H`) draws one `(y, x)` pair from the `PS` oracle and
caches `(m, (y, x))` for consistent replay across both oracles. -/
@[expose] def detPSHandler [DecidableEq M] :
    (q : M ⊕ M) →
      StateT (List (M × (Target × Option Preimage)) × List M)
        (ProbOracleComp (fun _ : Unit => Target × Option Preimage))
        (ROMSignature.ForgerSpec M M (Option Preimage) Target q)
  | .inl m => fun (cache, signed) =>
    match cache.lookup m with
    | some (_, x) => pure (x, (cache, m :: signed))
    | none => do
        let yx ← ProbOracleComp.query ()
        pure (yx.2, ((m, yx) :: cache, m :: signed))
  | .inr m => fun (cache, signed) =>
    match cache.lookup m with
    | some (y, _) => pure (y, (cache, signed))
    | none => do
        let yx ← ProbOracleComp.query ()
        pure (yx.1, ((m, yx) :: cache, signed))

/-- Multi-query `PS` distinguisher (`D_ps`) for deterministic unsalted hash-and-sign: runs the
forger using `detPSHandler` (at most `q_S + q_H` `PS` queries) and returns whether the forgery
verifies on an unsigned message. -/
@[expose] noncomputable def detPSDistinguisher [DecidableEq M] [DecidableEq Target]
    [Fintype Target] [Nonempty Target]
    (sys : TrapdoorPreimageSystem PK SK Target Preimage)
    (forger : PK → ProbOracleComp
      (ROMSignature.ForgerSpec M M (Option Preimage) Target) (M × Option Preimage)) :
    PSDistinguisher PK Target Preimage := fun pk => do
  let ((mStar, sigStar), (cache, signed)) ←
    (OracleComp.interpret
      (OracleComp.sumHandler
        (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
        (detPSHandler (M := M) (Target := Target) (Preimage := Preimage)))
      (forger pk)).run ([], [])
  let yStar ←
    match cache.lookup mStar with
    | some (y, _) => pure y
    | none => ProbOracleComp.sample (ProbComp.uniform Target)
  return sys.check pk yStar sigStar && !signed.contains mStar

/-- `detPSDistinguisher` makes at most `q_S + q_H` queries to the `PS` oracle. -/
theorem detPSDistinguisher_queryBound [DecidableEq M] [DecidableEq Target]
    [Fintype Target] [Nonempty Target]
    (sys : TrapdoorPreimageSystem PK SK Target Preimage)
    (forger : PK → ProbOracleComp
      (ROMSignature.ForgerSpec M M (Option Preimage) Target) (M × Option Preimage))
    {q_S q_H : ℕ} (hforger : ProbForgerCallBounded forger q_S q_H) (pk : PK) :
    (detPSDistinguisher sys forger pk).IsQueryBounded (q_S + q_H) := by
  have hstep :
      ∀ (q : ℕ ⊕ (M ⊕ M)) (st : List (M × (Target × Option Preimage)) × List M),
        ProbOracleComp.IsQueryBounded
          ((OracleComp.sumHandler
            (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
            (detPSHandler (M := M) (Target := Target) (Preimage := Preimage)) q).run st)
          (Sum.elim (fun _ => 0) (fun _ => 1) q) := by
    have hbranch : ∀ {α : Type} (cache : List (M × (Target × Option Preimage))) (m : M)
        (onSome onNone : Target × Option Preimage →
          α × (List (M × (Target × Option Preimage)) × List M)),
        ProbOracleComp.IsQueryBounded
          (match cache.lookup m with
          | some (y, x) => pure (onSome (y, x))
          | none => do
              let yx ← ProbOracleComp.query
                (spec := fun _ : Unit => Target × Option Preimage) ()
              pure (onNone yx)) 1 := by
      intro α cache m onSome onNone
      cases cache.lookup m with
      | some yx => exact OracleComp.IsCostBounded.pure _ 1
      | none =>
        simpa only [add_zero] using
          (ProbOracleComp.IsQueryBounded.query
            (spec := fun _ : Unit => Target × Option Preimage) ()).bind
            fun yx => OracleComp.IsCostBounded.pure _ 0
    rintro (n | (m | m)) ⟨cache, signed⟩
    · simpa only [OracleComp.sumHandler, StateT.run_lift, Sum.elim_inl, add_zero] using
        (ProbOracleComp.IsQueryBounded.sample
          (spec := fun _ : Unit => Target × Option Preimage) (ProbComp.unifFin n)).bind
          fun a => OracleComp.IsCostBounded.pure (a, (cache, signed)) 0
    · dsimp only [OracleComp.sumHandler, detPSHandler, StateT.run, Sum.elim_inr]
      exact hbranch cache m (fun yx => (yx.2, (cache, m :: signed)))
        (fun yx => (yx.2, ((m, yx) :: cache, m :: signed)))
    · dsimp only [OracleComp.sumHandler, detPSHandler, StateT.run, Sum.elim_inr]
      exact hbranch cache m (fun yx => (yx.1, (cache, signed)))
        (fun yx => (yx.1, ((m, yx) :: cache, signed)))
  have hmain :
      ProbOracleComp.IsQueryBounded
        ((OracleComp.interpret
          (OracleComp.sumHandler
            (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
            (detPSHandler (M := M) (Target := Target) (Preimage := Preimage)))
          (forger pk)).run ([], []))
        (q_S + q_H) :=
    OracleComp.IsCostBounded.run_interpret hstep (hforger.isQueryBounded pk) ([], [])
  have hpost :
      ∀ res : (M × Option Preimage) × List (M × (Target × Option Preimage)) × List M,
        ProbOracleComp.IsQueryBounded
          (match res with
          | ((mStar, sigStar), (cache, signed)) => do
            let yStar ←
              match cache.lookup mStar with
              | some (y, _) => pure y
              | none => (ProbOracleComp.sample
                  (spec := fun _ : Unit => Target × Option Preimage) (ProbComp.uniform Target))
            return sys.check pk yStar sigStar && !signed.contains mStar) 0 := by
    rintro ⟨⟨mStar, sigStar⟩, cache, signed⟩
    dsimp only
    cases cache.lookup mStar with
    | some yx =>
      simpa only [pure_bind] using
        (OracleComp.IsCostBounded.pure (cost := Sum.elim (fun _ => 0) fun _ => 1)
          (sys.check pk yx.1 sigStar && !signed.contains mStar) 0)
    | none =>
      simpa only [add_zero] using
        (ProbOracleComp.IsQueryBounded.sample
          (spec := fun _ : Unit => Target × Option Preimage) (ProbComp.uniform Target)).bind
          fun y' => OracleComp.IsCostBounded.pure _ 0
  simpa only [detPSDistinguisher, add_zero] using hmain.bind hpost

/-- Stateful handler for `detPSOneDistinguisher`: embeds a pre-drawn target `yStar` at the
`jStar`-th fresh direct hash query (storing `none` as its preimage slot so a later `Sign` on that
message returns `none`), while answering all other fresh queries with `sys.sampleSimPair pk`. -/
@[expose] def detPSOneSimHandler [DecidableEq M]
    (sys : TrapdoorPreimageSystem PK SK Target Preimage) (pk : PK) (jStar : ℕ) (yStar : Target)
    (q : M ⊕ M)
    (st : List (M × (Target × Option (Option Preimage) × Option ℕ)) × List M × ℕ) :
    ProbComp ((ROMSignature.ForgerSpec M M (Option Preimage) Target q) ×
      (List (M × (Target × Option (Option Preimage) × Option ℕ)) × List M × ℕ)) :=
  let (cache, signed, hCount) := st
  match q with
  | .inl m =>
    match cache.lookup m with
    | some (_, some x, _) => pure (x, (cache, m :: signed, hCount))
    | some (_, none, _) => pure (none, (cache, m :: signed, hCount))
    | none => do
        let yx ← sys.sampleSimPair pk
        pure (yx.2, ((m, (yx.1, some yx.2, none)) :: cache, m :: signed, hCount))
  | .inr m =>
    match cache.lookup m with
    | some (y, _, _) => pure (y, (cache, signed, hCount))
    | none =>
        if hCount = jStar then
          pure (yStar, ((m, (yStar, none, some hCount)) :: cache, signed, hCount + 1))
        else do
          let yx ← sys.sampleSimPair pk
          pure (yx.1, ((m, (yx.1, some yx.2, some hCount)) :: cache, signed, hCount + 1))

/-- 1-query `PS` distinguisher (`D_ps,1`) for deterministic unsalted hash-and-sign: queries the
`PS` oracle once upfront, uses only its target component `yStar`, guesses `jStar ← Fin (q_H + 1)`,
embeds `yStar` at the `jStar`-th fresh direct hash query (returning `none` if `Sign` is later
called on that message), and outputs whether the forgery succeeds at index `jStar`. -/
@[expose] noncomputable def detPSOneDistinguisher [DecidableEq M] [DecidableEq Target]
    [Fintype Target] [Nonempty Target]
    (sys : TrapdoorPreimageSystem PK SK Target Preimage) (q_H : ℕ)
    (forger : PK → ProbOracleComp
      (ROMSignature.ForgerSpec M M (Option Preimage) Target) (M × Option Preimage)) :
    PSDistinguisher PK Target Preimage := fun pk => do
  let yxStar ← ProbOracleComp.query ()
  let jStar ← ProbOracleComp.sample (ProbComp.uniform (Fin (q_H + 1)))
  let ((mStar, sigStar), (cache, signed, hCount)) ←
    ProbOracleComp.sample (((forger pk).runState
      (detPSOneSimHandler sys pk jStar.val yxStar.1)).run ([], [], 0))
  match cache.lookup mStar with
  | some (y, _, idxOpt) =>
    return (sys.check pk y sigStar && !signed.contains mStar) &&
      decide (Fin.ofNat (q_H + 1) (idxOpt.getD hCount) = jStar)
  | none =>
    let y ← ProbOracleComp.sample (ProbComp.uniform Target)
    return (sys.check pk y sigStar && !signed.contains mStar) &&
      decide (Fin.ofNat (q_H + 1) hCount = jStar)

/-- `detPSOneDistinguisher` makes at most `1` query to the `PS` oracle. -/
theorem detPSOneDistinguisher_queryBound [DecidableEq M] [DecidableEq Target]
    [Fintype Target] [Nonempty Target]
    (sys : TrapdoorPreimageSystem PK SK Target Preimage) (q_H : ℕ)
    (forger : PK → ProbOracleComp
      (ROMSignature.ForgerSpec M M (Option Preimage) Target) (M × Option Preimage)) (pk : PK) :
    (detPSOneDistinguisher sys q_H forger pk).IsQueryBounded 1 := by
  have hpost (jStar : Fin (q_H + 1)) :
      ∀ res : (M × Option Preimage) ×
        (List (M × (Target × Option (Option Preimage) × Option ℕ)) × List M × ℕ),
      ProbOracleComp.IsQueryBounded
        (match res with
        | ((mStar, sigStar), (cache, signed, hCount)) =>
          match cache.lookup mStar with
          | some (y, _, idxOpt) =>
            pure ((sys.check pk y sigStar && !signed.contains mStar) &&
              decide (Fin.ofNat (q_H + 1) (idxOpt.getD hCount) = jStar))
          | none => do
            let y ← (ProbOracleComp.sample
              (spec := fun _ : Unit => Target × Option Preimage) (ProbComp.uniform Target))
            return (sys.check pk y sigStar && !signed.contains mStar) &&
              decide (Fin.ofNat (q_H + 1) hCount = jStar)) 0 := by
    rintro ⟨⟨mStar, sigStar⟩, cache, signed, hCount⟩
    dsimp only
    cases cache.lookup mStar with
    | some _ => exact OracleComp.IsCostBounded.pure _ 0
    | none =>
      simpa only [add_zero] using
        (ProbOracleComp.IsQueryBounded.sample
          (spec := fun _ : Unit => Target × Option Preimage) (ProbComp.uniform Target)).bind
          fun _ => OracleComp.IsCostBounded.pure _ 0
  have hmid (yxStar : Target × Option Preimage) (jStar : Fin (q_H + 1)) :
      ProbOracleComp.IsQueryBounded
        (do
          let ((mStar, sigStar), (cache, signed, hCount)) ←
            (ProbOracleComp.sample (spec := fun _ : Unit => Target × Option Preimage)
              (((forger pk).runState
                (detPSOneSimHandler sys pk jStar.val yxStar.1)).run ([], [], 0)))
          match cache.lookup mStar with
          | some (y, _, idxOpt) =>
            return (sys.check pk y sigStar && !signed.contains mStar) &&
              decide (Fin.ofNat (q_H + 1) (idxOpt.getD hCount) = jStar)
          | none =>
            let y ← (ProbOracleComp.sample
              (spec := fun _ : Unit => Target × Option Preimage) (ProbComp.uniform Target))
            return (sys.check pk y sigStar && !signed.contains mStar) &&
              decide (Fin.ofNat (q_H + 1) hCount = jStar)) 0 := by
    simpa only [add_zero] using
      (ProbOracleComp.IsQueryBounded.sample
        (spec := fun _ : Unit => Target × Option Preimage)
        (((forger pk).runState
          (detPSOneSimHandler sys pk jStar.val yxStar.1)).run ([], [], 0))).bind (hpost jStar)
  have hrest (yxStar : Target × Option Preimage) :
      ProbOracleComp.IsQueryBounded
        (do
          let jStar ← (ProbOracleComp.sample
            (spec := fun _ : Unit => Target × Option Preimage) (ProbComp.uniform (Fin (q_H + 1))))
          let ((mStar, sigStar), (cache, signed, hCount)) ←
            (ProbOracleComp.sample (spec := fun _ : Unit => Target × Option Preimage)
              (((forger pk).runState
                (detPSOneSimHandler sys pk jStar.val yxStar.1)).run ([], [], 0)))
          match cache.lookup mStar with
          | some (y, _, idxOpt) =>
            return (sys.check pk y sigStar && !signed.contains mStar) &&
              decide (Fin.ofNat (q_H + 1) (idxOpt.getD hCount) = jStar)
          | none =>
            let y ← (ProbOracleComp.sample
              (spec := fun _ : Unit => Target × Option Preimage) (ProbComp.uniform Target))
            return (sys.check pk y sigStar && !signed.contains mStar) &&
              decide (Fin.ofNat (q_H + 1) hCount = jStar)) 0 := by
    simpa only [add_zero] using
      (ProbOracleComp.IsQueryBounded.sample
        (spec := fun _ : Unit => Target × Option Preimage)
        (ProbComp.uniform (Fin (q_H + 1)))).bind (hmid yxStar)
  simpa only [detPSOneDistinguisher, add_zero] using
    (ProbOracleComp.IsQueryBounded.query
      (spec := fun _ : Unit => Target × Option Preimage) ()).bind hrest

/-- Stateful inverter handler for deterministic unsalted hash-and-sign: embeds the challenge
target `yStar` at the `jStar`-th fresh direct hash query (returning `none` if `Sign` is later
called on that message), and simulates all other fresh queries with `sys.sampleSimPair pk`. -/
@[expose] def detInvHandler [DecidableEq M]
    (sys : TrapdoorPreimageSystem PK SK Target Preimage) (pk : PK) (jStar : ℕ) (yStar : Target)
    (q : M ⊕ M) (st : List (M × (Target × Option (Option Preimage))) × ℕ) :
    ProbComp ((ROMSignature.ForgerSpec M M (Option Preimage) Target q) ×
      (List (M × (Target × Option (Option Preimage))) × ℕ)) :=
  let (cache, hCount) := st
  match q with
  | .inl m =>
    match cache.lookup m with
    | some (_, some x) => pure (x, (cache, hCount))
    | some (_, none) => pure (none, (cache, hCount))
    | none => do
        let yx ← sys.sampleSimPair pk
        pure (yx.2, ((m, (yx.1, some yx.2)) :: cache, hCount))
  | .inr m =>
    match cache.lookup m with
    | some (y, _) => pure (y, (cache, hCount))
    | none =>
        if hCount = jStar then
          pure (yStar, ((m, (yStar, none)) :: cache, hCount + 1))
        else do
          let yx ← sys.sampleSimPair pk
          pure (yx.1, ((m, (yx.1, some yx.2)) :: cache, hCount + 1))

/-- Explicit target inverter (`B_inv`) for deterministic unsalted hash-and-sign: guesses
`jStar ← Fin (q_H + 1)`, embeds `yStar` at the `jStar`-th fresh direct hash query, and outputs the
forger's candidate preimage `sigStar`. -/
@[expose] noncomputable def detInverter [DecidableEq M]
    (sys : TrapdoorPreimageSystem PK SK Target Preimage) (q_H : ℕ)
    (forger : PK → ProbOracleComp
      (ROMSignature.ForgerSpec M M (Option Preimage) Target) (M × Option Preimage))
    (pk : PK) (yStar : Target) : ProbComp (Option Preimage) := do
  let jStar ← ProbComp.uniform (Fin (q_H + 1))
  let ((_, sigStar), _) ←
    ((forger pk).runState (detInvHandler sys pk jStar.val yStar)).run ([], 0)
  return sigStar

/-- Helper: uniform hit probability of `List.lookup` being `some` on an association list `l` is at
most `l.length / |α|`. -/
private theorem uniform_toOuterMeasure_lookup_isSome_le {α β : Type} [DecidableEq α]
    [Fintype α] [Nonempty α] (l : List (α × β)) :
    (PMF.uniformOfFintype α).toOuterMeasure {y | (l.lookup y).isSome = true} ≤
      (l.length : ℝ≥0∞) * (Fintype.card α : ℝ≥0∞)⁻¹ := by
  have hsub : {y : α | (l.lookup y).isSome = true} ⊆ ↑(l.map Prod.fst).toFinset := by
    intro y hy
    change (l.lookup y).isSome = true at hy
    rw [Finset.mem_coe, List.mem_toFinset]
    cases hlu : l.lookup y with
    | none => rw [hlu] at hy; simp at hy
    | some v => exact List.mem_map.mpr ⟨(y, v), mem_of_lookup_eq_some hlu, rfl⟩
  calc
    (PMF.uniformOfFintype α).toOuterMeasure {y | (l.lookup y).isSome = true}
      ≤ (PMF.uniformOfFintype α).toOuterMeasure ↑(l.map Prod.fst).toFinset :=
          (PMF.uniformOfFintype α).toOuterMeasure.mono hsub
    _ = ((l.map Prod.fst).toFinset.card : ℝ≥0∞) * (Fintype.card α : ℝ≥0∞)⁻¹ := by
          rw [PMF.toOuterMeasure_apply_finset]
          simp [PMF.uniformOfFintype_apply]
    _ ≤ (l.length : ℝ≥0∞) * (Fintype.card α : ℝ≥0∞)⁻¹ := by
          refine mul_le_mul_of_nonneg_right ?_ zero_le
          exact_mod_cast (List.toFinset_card_le (l.map Prod.fst)).trans (by simp)

/-- Intermediate `ProbOracleComp` over the inversion table `Target → Option Preimage` used in
Hop 0→1 to switch `invTable ← PMF.pi (eval ∘ invert sk)` from eager to lazy via
`RandomOracle.interpret_prob_eq_memoize`. -/
private noncomputable def detEagerHandler [DecidableEq M] [Fintype Target] [Nonempty Target] :
    (q : M ⊕ M) →
      StateT (List (M × (Target × Option Preimage)) × List M)
        (ProbOracleComp (fun _ : Target => Option Preimage))
        (ROMSignature.ForgerSpec M M (Option Preimage) Target q)
  | .inl m => fun (cache, signed) =>
    match cache.lookup m with
    | some (_, x) => pure (x, (cache, m :: signed))
    | none => do
        let y ← ProbOracleComp.sample (ProbComp.uniform Target)
        let x ← ProbOracleComp.query y
        pure (x, ((m, (y, x)) :: cache, m :: signed))
  | .inr m => fun (cache, signed) =>
    match cache.lookup m with
    | some (y, _) => pure (y, (cache, signed))
    | none => do
        let y ← ProbOracleComp.sample (ProbComp.uniform Target)
        let x ← ProbOracleComp.query y
        pure (y, ((m, (y, x)) :: cache, signed))

private noncomputable def detEagerProg [DecidableEq M] [DecidableEq Target]
    [Fintype Target] [Nonempty Target]
    (sys : TrapdoorPreimageSystem PK SK Target Preimage) (pk : PK)
    (forger : PK → ProbOracleComp
      (ROMSignature.ForgerSpec M M (Option Preimage) Target) (M × Option Preimage)) :
    ProbOracleComp (fun _ : Target => Option Preimage) Bool := do
  let ((mStar, sigStar), (cache, signed)) ←
    (OracleComp.interpret
      (OracleComp.sumHandler
        (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
        (detEagerHandler (M := M) (Target := Target) (Preimage := Preimage)))
      (forger pk)).run ([], [])
  let yStar ←
    match cache.lookup mStar with
    | some (y, _) => pure y
    | none => ProbOracleComp.sample (ProbComp.uniform Target)
  return sys.check pk yStar sigStar && !signed.contains mStar

/-- Flagged lazy-inversion step for Hop 0→1: reuses `invCache.lookup y` on a target collision and
raises the bad flag. -/
private noncomputable def detLazyInvStep [DecidableEq M] [DecidableEq Target]
    [Fintype Target] [Nonempty Target]
    (sys : TrapdoorPreimageSystem PK SK Target Preimage) (sk : SK)
    (q : M ⊕ M)
    (st : List (M × (Target × Option Preimage)) × List M × List (Target × Option Preimage)) :
    PMF (ROMSignature.ForgerSpec M M (Option Preimage) Target q ×
      ((List (M × (Target × Option Preimage)) × List M × List (Target × Option Preimage)) ×
        Bool)) :=
  let (cache, signed, invCache) := st
  match q with
  | .inl m =>
    match cache.lookup m with
    | some (_, x) => PMF.pure (x, ((cache, m :: signed, invCache), false))
    | none =>
      (PMF.uniformOfFintype Target).bind fun y =>
        match invCache.lookup y with
        | some x => PMF.pure (x, (((m, (y, x)) :: cache, m :: signed, invCache), true))
        | none =>
          (ProbComp.eval (sys.invert sk y)).map fun x =>
            (x, (((m, (y, x)) :: cache, m :: signed, (y, x) :: invCache), false))
  | .inr m =>
    match cache.lookup m with
    | some (y, _) => PMF.pure (y, ((cache, signed, invCache), false))
    | none =>
      (PMF.uniformOfFintype Target).bind fun y =>
        match invCache.lookup y with
        | some x => PMF.pure (y, (((m, (y, x)) :: cache, signed, invCache), true))
        | none =>
          (ProbComp.eval (sys.invert sk y)).map fun x =>
            (y, (((m, (y, x)) :: cache, signed, (y, x) :: invCache), false))

/-- Flagged fresh-inversion step for Hop 0→1: always draws a fresh `x ← invert sk y` (matching
`sampleRealPair sk`) and raises the bad flag whenever `invCache.lookup y` is `some`. -/
private noncomputable def detFreshInvStep [DecidableEq M] [DecidableEq Target]
    [Fintype Target] [Nonempty Target]
    (sys : TrapdoorPreimageSystem PK SK Target Preimage) (sk : SK)
    (q : M ⊕ M)
    (st : List (M × (Target × Option Preimage)) × List M × List (Target × Option Preimage)) :
    PMF (ROMSignature.ForgerSpec M M (Option Preimage) Target q ×
      ((List (M × (Target × Option Preimage)) × List M × List (Target × Option Preimage)) ×
        Bool)) :=
  let (cache, signed, invCache) := st
  match q with
  | .inl m =>
    match cache.lookup m with
    | some (_, x) => PMF.pure (x, ((cache, m :: signed, invCache), false))
    | none =>
      (PMF.uniformOfFintype Target).bind fun y =>
        (ProbComp.eval (sys.invert sk y)).map fun x =>
          (x, (((m, (y, x)) :: cache, m :: signed, (y, x) :: invCache),
            (invCache.lookup y).isSome))
  | .inr m =>
    match cache.lookup m with
    | some (y, _) => PMF.pure (y, ((cache, signed, invCache), false))
    | none =>
      (PMF.uniformOfFintype Target).bind fun y =>
        (ProbComp.eval (sys.invert sk y)).map fun x =>
          (y, (((m, (y, x)) :: cache, signed, (y, x) :: invCache),
            (invCache.lookup y).isSome))

/-- Hop 0→1 for `detScheme`: replacing the shared eager `invTable` with independent
`sampleRealPair sk` draws per fresh message (`psExperimentReal sys (detPSDistinguisher ...)`)
costs at most `(q_S + q_H).choose 2 / |Target|` (target birthday collisions). -/
private theorem detWorld_le_detPSReal_add_birthday [DecidableEq M] [DecidableEq Target]
    [Fintype Target] [Nonempty Target] [Finite Preimage]
    (sys : TrapdoorPreimageSystem PK SK Target Preimage)
    (forger : PK → ProbOracleComp
      (ROMSignature.ForgerSpec M M (Option Preimage) Target) (M × Option Preimage))
    {q_S q_H : ℕ} (hforger : ProbForgerCallBounded forger q_S q_H) :
    (ROMSignature.worldGame (detScheme sys) forger eufCmaAccept) true ≤
      (ProbComp.eval (psExperimentReal sys (detPSDistinguisher sys forger))) true +
        ((q_S + q_H).choose 2 : ℕ) * (Fintype.card Target : ℝ≥0∞)⁻¹ := by
  unfold ROMSignature.worldGame psExperimentReal
  have hkg : (detScheme (M := M) sys).keyGen =
      (ProbComp.eval sys.keyGen).bind fun keys =>
        (PMF.pi fun y => ProbComp.eval (sys.invert keys.2 y)).bind fun invTable =>
          PMF.pure (keys.1, (keys.2, invTable)) := rfl
  rw [hkg]
  simp only [PMF.monad_bind_eq_bind, PMF.bind_bind, PMF.pure_bind, ProbComp.eval_bind]
  rw [PMF.bind_apply, PMF.bind_apply]
  have hrhs_add :
      (∑' x : PK × SK, (ProbComp.eval sys.keyGen) x *
          (ProbComp.eval ((detPSDistinguisher sys forger x.1).run
            fun _ => sys.sampleRealPair x.2)) true) +
        ((q_S + q_H).choose 2 : ℕ) * (Fintype.card Target : ℝ≥0∞)⁻¹ =
      ∑' x : PK × SK, (ProbComp.eval sys.keyGen) x *
        ((ProbComp.eval ((detPSDistinguisher sys forger x.1).run
            fun _ => sys.sampleRealPair x.2)) true +
          ((q_S + q_H).choose 2 : ℕ) * (Fintype.card Target : ℝ≥0∞)⁻¹) := by
    simp only [mul_add, tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  rw [hrhs_add]
  refine tsum_le_tsum fun ⟨pk, sk⟩ => ?_
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  -- Step 1a: For fixed `(pk, sk, invTable)`, match `worldGame` body to `detEagerProg`.
  have heager (invTable : Target → Option Preimage) :
      Interactive.World.eval (ROMSignature.world (detScheme sys) (sk, invTable))
        (ROMSignature.worldRealize (detScheme sys) pk (forger pk) eufCmaAccept) =
      OracleComp.interpret
        (OracleComp.sumHandler ProbComp.unifOracle fun y => PMF.pure (invTable y))
        (detEagerProg sys pk forger) := by
    rw [ROMSignature.eval_world_worldRealize]
    have hrun_eager :
        OracleComp.interpret
          (OracleComp.sumHandler ProbComp.unifOracle fun y => PMF.pure (invTable y))
          (detEagerProg sys pk forger) =
        (ProbOracleComp.runWith
          (fun q (st : List (M × (Target × Option Preimage)) × List M) =>
            let (cache, signed) := st
            match q with
            | .inl m =>
              match cache.lookup m with
              | some (_, x) => PMF.pure (x, (cache, m :: signed))
              | none =>
                (PMF.uniformOfFintype Target).map fun y =>
                  (invTable y, ((m, (y, invTable y)) :: cache, m :: signed))
            | .inr m =>
              match cache.lookup m with
              | some (y, _) => PMF.pure (y, (cache, signed))
              | none =>
                (PMF.uniformOfFintype Target).map fun y =>
                  (y, ((m, (y, invTable y)) :: cache, signed)))
          (forger pk) ([], [])).bind fun ((mStar, sigStar), (cache, signed)) =>
            match cache.lookup mStar with
            | some (y, _) => PMF.pure (sys.check pk y sigStar && !signed.contains mStar)
            | none =>
              (PMF.uniformOfFintype Target).map fun y =>
                sys.check pk y sigStar && !signed.contains mStar := by
      unfold detEagerProg
      simp only [OracleComp.interpret_bind]
      have hro := ProbOracleComp.runWith_readOnly (α := (M × Option Preimage) ×
          (List (M × (Target × Option Preimage)) × List M))
        (fun y (_ : Unit) => PMF.pure (invTable y))
        ((OracleComp.interpret
          (OracleComp.sumHandler
            (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
            (detEagerHandler (M := M) (Target := Target) (Preimage := Preimage)))
          (forger pk)).run ([], [])) ()
      have hleft :
          OracleComp.interpret
            (OracleComp.sumHandler ProbComp.unifOracle fun y => PMF.pure (invTable y))
            ((OracleComp.interpret
              (OracleComp.sumHandler
                (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
                (detEagerHandler (M := M) (Target := Target) (Preimage := Preimage)))
              (forger pk)).run ([], [])) =
          ProbOracleComp.runWith
            (fun q (st : List (M × (Target × Option Preimage)) × List M) =>
              let (cache, signed) := st
              match q with
              | .inl m =>
                match cache.lookup m with
                | some (_, x) => PMF.pure (x, (cache, m :: signed))
                | none =>
                  (PMF.uniformOfFintype Target).map fun y =>
                    (invTable y, ((m, (y, invTable y)) :: cache, m :: signed))
              | .inr m =>
                match cache.lookup m with
                | some (y, _) => PMF.pure (y, (cache, signed))
                | none =>
                  (PMF.uniformOfFintype Target).map fun y =>
                    (y, ((m, (y, invTable y)) :: cache, signed)))
            (forger pk) ([], []) := by
        have hstep1 :
            (ProbOracleComp.runWith
              (fun y (_ : Unit) => (PMF.pure (invTable y)).map (·, ()))
              ((OracleComp.interpret
                (OracleComp.sumHandler
                  (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
                  (detEagerHandler (M := M) (Target := Target) (Preimage := Preimage)))
                (forger pk)).run ([], [])) ()).map Prod.fst =
            OracleComp.interpret
              (OracleComp.sumHandler ProbComp.unifOracle fun y => PMF.pure (invTable y))
              ((OracleComp.interpret
                (OracleComp.sumHandler
                  (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
                  (detEagerHandler (M := M) (Target := Target) (Preimage := Preimage)))
                (forger pk)).run ([], [])) := by
          rw [hro, PMF.map_comp]
          simp [Function.comp_def, OracleComp.evalWith_eq_interpret, PMF.map_id']
        rw [← hstep1, ProbOracleComp.runWith_run_interpret]
        have hdrop := ProbOracleComp.runWith_map_state
          (fun q (st : (List (M × (Target × Option Preimage)) × List M) × Unit) =>
            (ProbOracleComp.runWith
              (fun y (_ : Unit) => (PMF.pure (invTable y)).map (·, ()))
              ((detEagerHandler (M := M) (Target := Target) (Preimage := Preimage) q).run st.1)
              st.2).map fun ⟨⟨a, b⟩, c⟩ => (a, b, c))
          (fun q (st : List (M × (Target × Option Preimage)) × List M) =>
            let (cache, signed) := st
            match q with
            | .inl m =>
              match cache.lookup m with
              | some (_, x) => PMF.pure (x, (cache, m :: signed))
              | none =>
                (PMF.uniformOfFintype Target).map fun y =>
                  (invTable y, ((m, (y, invTable y)) :: cache, m :: signed))
            | .inr m =>
              match cache.lookup m with
              | some (y, _) => PMF.pure (y, (cache, signed))
              | none =>
                (PMF.uniformOfFintype Target).map fun y =>
                  (y, ((m, (y, invTable y)) :: cache, signed)))
          Prod.fst
          (fun q ⟨⟨cache, signed⟩, _⟩ => by
            cases q with
            | inl m =>
              dsimp only [detEagerHandler, StateT.run]
              cases cache.lookup m with
              | some yx => simp [ProbOracleComp.runWith_pure, PMF.pure_map]
              | none =>
                simp only [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_sample,
                  ProbOracleComp.runWith_query, ProbOracleComp.runWith_pure, ProbComp.eval_uniform,
                  PMF.map_bind, PMF.pure_map, PMF.pure_bind, PMF.bind_map, Function.comp_apply]
                exact (PMF.bind_pure_comp _ _).symm
            | inr m =>
              dsimp only [detEagerHandler, StateT.run]
              cases cache.lookup m with
              | some yx => simp [ProbOracleComp.runWith_pure, PMF.pure_map]
              | none =>
                simp only [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_sample,
                  ProbOracleComp.runWith_query, ProbOracleComp.runWith_pure, ProbComp.eval_uniform,
                  PMF.map_bind, PMF.pure_map, PMF.pure_bind, PMF.bind_map, Function.comp_apply]
                exact (PMF.bind_pure_comp _ _).symm)
          (forger pk) (([], []), ())
        simpa only [PMF.map_comp, Function.comp_def, Prod.map] using hdrop
      rw [hleft]
      refine PMF.bind_congr_on_support _ _ _ fun ⟨⟨mStar, sigStar⟩, cache, signed⟩ _ => ?_
      cases cache.lookup mStar with
      | some yx =>
        simp [OracleComp.interpret_pure]
      | none =>
        have hsample :
            OracleComp.interpret
              (OracleComp.sumHandler ProbComp.unifOracle fun y => PMF.pure (invTable y))
              (ProbOracleComp.sample (spec := fun _ : Target => Option Preimage)
                (ProbComp.uniform Target)) =
            PMF.uniformOfFintype Target := by
          have := ProbOracleComp.runWith_readOnly
            (fun y (_ : Unit) => PMF.pure (invTable y))
            (ProbOracleComp.sample (spec := fun _ : Target => Option Preimage)
              (ProbComp.uniform Target)) ()
          have h2 := congrArg (PMF.map Prod.fst) this
          simp only [ProbOracleComp.runWith_sample, ProbComp.eval_uniform, PMF.map_comp,
            Function.comp_def, PMF.map_id', OracleComp.evalWith_eq_interpret] at h2
          exact h2.symm
        simp only [OracleComp.interpret_bind, OracleComp.interpret_pure, hsample]
        exact (PMF.bind_pure_comp _ _).symm
    rw [hrun_eager]
    -- Project the worldGame execution to `(cache, signed)` via invariant `x = invTable y`.
    have hworld_run :
        ProbOracleComp.runWith (ROMSignature.forgerWorldImpl (detScheme sys) (sk, invTable))
          (ROMSignature.runLoggedForger (forger pk)) [] =
        (ProbOracleComp.runWith
          (fun q ((pairs, cache) : List (M × Option Preimage) × List (M × Target)) =>
            match q with
            | .inl m =>
              match cache.lookup m with
              | some y => PMF.pure (invTable y, ((m, invTable y) :: pairs, cache))
              | none =>
                (PMF.uniformOfFintype Target).map fun y =>
                  (invTable y, ((m, invTable y) :: pairs, (m, y) :: cache))
            | .inr m =>
              match cache.lookup m with
              | some y => PMF.pure (y, (pairs, cache))
              | none =>
                (PMF.uniformOfFintype Target).map fun y =>
                  (y, (pairs, (m, y) :: cache)))
          (forger pk) ([], [])).map fun (out, (pairs, cache)) => ((out, pairs), cache) := by
      simp only [ROMSignature.runLoggedForger, ProbOracleComp.runWith_run_interpret]
      have hbody :
          (fun (q : M ⊕ M) (state : List (M × Option Preimage) × List (M × Target)) =>
            PMF.map (fun ((a, b), c) => (a, b, c))
              (ProbOracleComp.runWith (ROMSignature.forgerWorldImpl (detScheme sys) (sk, invTable))
                ((ROMSignature.logSigning q).run state.1) state.2)) =
          (fun (q : M ⊕ M) ((pairs, cache) : List (M × Option Preimage) × List (M × Target)) =>
            match q with
            | .inl m =>
              match cache.lookup m with
              | some y => PMF.pure (invTable y, ((m, invTable y) :: pairs, cache))
              | none =>
                (PMF.uniformOfFintype Target).map fun y =>
                  (invTable y, ((m, invTable y) :: pairs, (m, y) :: cache))
            | .inr m =>
              match cache.lookup m with
              | some y => PMF.pure (y, (pairs, cache))
              | none =>
                (PMF.uniformOfFintype Target).map fun y =>
                  (y, (pairs, (m, y) :: cache)) :
            (q : M ⊕ M) → StateT (List (M × Option Preimage) × List (M × Target)) PMF
              (ROMSignature.ForgerSpec M M (Option Preimage) Target q)) := by
        funext q ⟨pairs, cache⟩
        cases q with
        | inl m =>
          simp only [ROMSignature.logSigning, StateT.run, ProbOracleComp.runWith_bind,
            ProbOracleComp.runWith_query, ProbOracleComp.runWith_pure, ROMSignature.forgerWorldImpl,
            detScheme, interp_norm, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.pure_bind]
          change PMF.map (fun ((a, b), c) => (a, b, c))
            ((((ROMSignature.oracle Target m).run cache).bind fun x =>
              PMF.pure (invTable x.1, x.2)).bind fun x =>
              PMF.pure ((x.1, (m, x.1) :: pairs), x.2)) = _
          cases hlu : cache.lookup m with
          | some y =>
            rw [ROMSignature.run_oracle_of_lookup_eq_some hlu]
            simp [PMF.pure_bind, PMF.pure_map]
          | none =>
            rw [ROMSignature.run_oracle_of_lookup_eq_none hlu]
            simp only [PMF.bind_bind, PMF.pure_bind, PMF.map_bind, PMF.pure_map]
            exact (PMF.bind_pure_comp _ _).symm
        | inr m =>
          simp only [ROMSignature.logSigning, StateT.run, ProbOracleComp.runWith_bind,
            ProbOracleComp.runWith_query, ProbOracleComp.runWith_pure, ROMSignature.forgerWorldImpl,
            detScheme, interp_norm, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.pure_bind]
          change PMF.map (fun ((a, b), c) => (a, b, c))
            (((ROMSignature.oracle Target m).run cache).bind fun x =>
              PMF.pure ((x.1, pairs), x.2)) = _
          cases hlu : cache.lookup m with
          | some y =>
            rw [ROMSignature.run_oracle_of_lookup_eq_some hlu]
            simp [PMF.pure_bind, PMF.pure_map]
          | none =>
            rw [ROMSignature.run_oracle_of_lookup_eq_none hlu]
            simp only [PMF.bind_bind, PMF.pure_bind, PMF.map_bind, PMF.pure_map]
            exact (PMF.bind_pure_comp _ _).symm
      rw [hbody]
    -- Compare the two `runWith` distributions projected to `(out, (cache.map ..., signed))`.
    have hproj_world :
        (ProbOracleComp.runWith (ROMSignature.forgerWorldImpl (detScheme sys) (sk, invTable))
          (ROMSignature.runLoggedForger (forger pk)) []).map
            (fun ((out, pairs), cache) => (out, (cache, pairs.map Prod.fst))) =
        (ProbOracleComp.runWith
          (fun q (st : List (M × (Target × Option Preimage)) × List M) =>
            let (cache, signed) := st
            match q with
            | .inl m =>
              match cache.lookup m with
              | some (_, x) => PMF.pure (x, (cache, m :: signed))
              | none =>
                (PMF.uniformOfFintype Target).map fun y =>
                  (invTable y, ((m, (y, invTable y)) :: cache, m :: signed))
            | .inr m =>
              match cache.lookup m with
              | some (y, _) => PMF.pure (y, (cache, signed))
              | none =>
                (PMF.uniformOfFintype Target).map fun y =>
                  (y, ((m, (y, invTable y)) :: cache, signed)))
          (forger pk) ([], [])).map
            (fun (out, (cache, signed)) =>
              (out, (cache.map fun (m, y, _) => (m, y), signed))) := by
      have h1 :
          (ProbOracleComp.runWith (ROMSignature.forgerWorldImpl (detScheme sys) (sk, invTable))
            (ROMSignature.runLoggedForger (forger pk)) []).map
              (fun ((out, pairs), cache) => (out, (cache, pairs.map Prod.fst))) =
          ProbOracleComp.runWith
            (fun q ((cache, signed) : List (M × Target) × List M) =>
              match q with
              | .inl m =>
                match cache.lookup m with
                | some y => PMF.pure (invTable y, (cache, m :: signed))
                | none =>
                  (PMF.uniformOfFintype Target).map fun y =>
                    (invTable y, ((m, y) :: cache, m :: signed))
              | .inr m =>
                match cache.lookup m with
                | some y => PMF.pure (y, (cache, signed))
                | none =>
                  (PMF.uniformOfFintype Target).map fun y =>
                    (y, ((m, y) :: cache, signed)))
            (forger pk) ([], []) := by
        rw [hworld_run, PMF.map_comp]
        exact ProbOracleComp.runWith_map_state _ _
          (fun (st : List (M × Option Preimage) × List (M × Target)) =>
            (st.2, st.1.map Prod.fst))
          (fun q ⟨pairs, cache⟩ => by
            cases q with
            | inl m =>
              cases hlu : cache.lookup m <;> simp [hlu, PMF.pure_map, PMF.map_comp,
                Function.comp_def]
            | inr m =>
              cases hlu : cache.lookup m <;> simp [hlu, PMF.pure_map, PMF.map_comp,
                Function.comp_def])
          (forger pk) ([], [])
      rw [h1]
      symm
      refine ProbOracleComp.runWith_map_state_of_invariant _ _
        (fun (st : List (M × (Target × Option Preimage)) × List M) =>
          (st.1.map fun (m, y, _) => (m, y), st.2))
        (fun (st : List (M × (Target × Option Preimage)) × List M) =>
          ∀ m y x, (m, (y, x)) ∈ st.1 → x = invTable y)
        ?_ ?_ (forger pk) ([], []) (by intro m y x hm; cases hm)
      · have hbranch : ∀ {α : Type} {cache cache' : List (M × (Target × Option Preimage))}
            {m : M} {signedOut signed' : List M} {a : α}
            (hinv : ∀ m' y' x', (m', (y', x')) ∈ cache → x' = invTable y')
            {outSome : Target × Option Preimage → α} {outNone : Target → α},
            (a, (cache', signed')) ∈ (match cache.lookup m with
              | some (y, x) => PMF.pure (outSome (y, x), (cache, signedOut))
              | none => (PMF.uniformOfFintype Target).map fun y =>
                  (outNone y, ((m, (y, invTable y)) :: cache, signedOut))).support →
            ∀ m' y' x', (m', (y', x')) ∈ cache' → x' = invTable y' := by
          intro α cache cache' m signedOut signed' a hinv outSome outNone hstep
          cases hlu : cache.lookup m with
          | some yx =>
            rw [hlu, PMF.mem_support_pure_iff, Prod.mk.injEq, Prod.mk.injEq] at hstep
            obtain ⟨-, rfl, -⟩ := hstep
            exact hinv
          | none =>
            rw [hlu, PMF.mem_support_map_iff] at hstep
            obtain ⟨y, -, heq⟩ := hstep
            rw [Prod.mk.injEq, Prod.mk.injEq] at heq
            obtain ⟨-, rfl, -⟩ := heq
            intro m' y' x' hm'
            rcases List.mem_cons.mp hm' with hhd | htl
            · injection hhd with _ h2
              injection h2 with hy hx
              subst hy hx
              rfl
            · exact hinv m' y' x' htl
        rintro q ⟨cache, signed⟩ hinv a ⟨cache', signed'⟩ hstep
        cases q with
        | inl m =>
          dsimp only at hinv hstep
          exact hbranch (m := m) (signedOut := m :: signed) (signed' := signed')
            (outSome := fun (_, x) => x) (outNone := invTable) hinv hstep
        | inr m =>
          dsimp only at hinv hstep
          exact hbranch (m := m) (signedOut := signed) (signed' := signed')
            (outSome := fun (y, _) => y) (outNone := fun y => y) hinv hstep
      · rintro q ⟨cache, signed⟩ hinv
        cases q with
        | inl m =>
          dsimp only
          rw [lookup_map_fst]
          cases hlu : cache.lookup m with
          | some yx =>
            have hx : yx.2 = invTable yx.1 := hinv m yx.1 yx.2 (mem_of_lookup_eq_some hlu)
            simp [hx, PMF.pure_map]
          | none =>
            simp [PMF.map_comp, Function.comp_def]
        | inr m =>
          dsimp only
          rw [lookup_map_fst]
          cases hlu : cache.lookup m with
          | some yx => simp [PMF.pure_map]
          | none => simp [PMF.map_comp, Function.comp_def]
    -- Now rewrite both sides through `hproj_world`.
    have hL :
        (ProbOracleComp.runWith (ROMSignature.forgerWorldImpl (detScheme sys) (sk, invTable))
          (ROMSignature.runLoggedForger (forger pk)) []).bind
            (fun ((out, pairs), cache) =>
              ((OracleComp.interpret (ROMSignature.oracle Target)
                ((detScheme sys).verify pk out.1 out.2)).run cache).bind fun (v, _) =>
                  PMF.pure (eufCmaAccept v out pairs)) =
        ((ProbOracleComp.runWith (ROMSignature.forgerWorldImpl (detScheme sys) (sk, invTable))
          (ROMSignature.runLoggedForger (forger pk)) []).map
            (fun ((out, pairs), cache) => (out, (cache, pairs.map Prod.fst)))).bind
            fun ((mStar, sigStar), (cache, signed)) =>
              match cache.lookup mStar with
              | some y => PMF.pure (sys.check pk y sigStar && !signed.contains mStar)
              | none =>
                (PMF.uniformOfFintype Target).map fun y =>
                  sys.check pk y sigStar && !signed.contains mStar := by
      rw [PMF.bind_map]
      refine PMF.bind_congr_on_support _ _ _ fun ⟨⟨⟨mStar, sigStar⟩, pairs⟩, cache⟩ _ => ?_
      dsimp only [Function.comp_def, detScheme, eufCmaAccept, interp_norm]
      change (((ROMSignature.oracle Target mStar).run cache).bind fun x =>
        PMF.pure (sys.check pk x.1 sigStar, x.2)).bind
          (fun x => PMF.pure (x.1 && !(pairs.map Prod.fst).contains mStar)) = _
      cases hlu : cache.lookup mStar with
      | some y =>
        rw [ROMSignature.run_oracle_of_lookup_eq_some hlu]
        simp [PMF.pure_bind]
      | none =>
        rw [ROMSignature.run_oracle_of_lookup_eq_none hlu]
        simp only [PMF.bind_bind, PMF.pure_bind]
        exact (PMF.bind_pure_comp _ _).symm
    simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
    rw [hL, hproj_world, PMF.bind_map]
    refine PMF.bind_congr_on_support _ _ _ fun ⟨⟨mStar, sigStar⟩, cache, signed⟩ _ => ?_
    dsimp only [Function.comp_def]
    rw [lookup_map_fst]
    cases cache.lookup mStar <;> rfl
  have heager_bind :
      ((PMF.pi fun y => ProbComp.eval (sys.invert sk y)).bind fun invTable =>
        Interactive.World.eval (ROMSignature.world (detScheme sys) (sk, invTable))
          (ROMSignature.worldRealize (detScheme sys) pk (forger pk) eufCmaAccept)) =
      (ProbOracleComp.runWith (memoize fun y => ProbComp.eval (sys.invert sk y))
        (detEagerProg sys pk forger) []).map Prod.fst := by
    have h1 := PMF.bind_congr_on_support (PMF.pi fun y => ProbComp.eval (sys.invert sk y))
      _ _ fun invTable _ => heager invTable
    exact h1.trans (RandomOracle.interpret_prob_eq_memoize
      (fun y => ProbComp.eval (sys.invert sk y)) (detEagerProg sys pk forger))
  rw [heager_bind]
  -- Step 1b: Expand `runWith memoize (detEagerProg ...)` via `withBadFlag (detLazyInvStep ...)`.
  let post : (M × Option Preimage) ×
      ((List (M × (Target × Option Preimage)) × List M × List (Target × Option Preimage)) × Bool) →
      PMF Bool :=
    fun ((mStar, sigStar), ((cache, signed, _), _)) =>
      match cache.lookup mStar with
      | some (y, _) => PMF.pure (sys.check pk y sigStar && !signed.contains mStar)
      | none =>
        (PMF.uniformOfFintype Target).map fun y =>
          sys.check pk y sigStar && !signed.contains mStar
  have hlazy_eq :
      (ProbOracleComp.runWith (memoize fun y => ProbComp.eval (sys.invert sk y))
        (detEagerProg sys pk forger) []).map Prod.fst =
      (ProbOracleComp.runWith (OracleComp.withBadFlag (detLazyInvStep sys sk)) (forger pk)
        (([], [], []), false)).bind post := by
    have hdrop := ProbOracleComp.runWith_withBadFlag_map_fst (detLazyInvStep sys sk)
      (fun q ((cache, signed, invCache) :
          List (M × (Target × Option Preimage)) × List M × List (Target × Option Preimage)) =>
        match q with
        | .inl m =>
          match cache.lookup m with
          | some (_, x) => PMF.pure (x, (cache, m :: signed, invCache))
          | none =>
            (PMF.uniformOfFintype Target).bind fun y =>
              match invCache.lookup y with
              | some x => PMF.pure (x, ((m, (y, x)) :: cache, m :: signed, invCache))
              | none =>
                (ProbComp.eval (sys.invert sk y)).map fun x =>
                  (x, ((m, (y, x)) :: cache, m :: signed, (y, x) :: invCache))
        | .inr m =>
          match cache.lookup m with
          | some (y, _) => PMF.pure (y, (cache, signed, invCache))
          | none =>
            (PMF.uniformOfFintype Target).bind fun y =>
              match invCache.lookup y with
              | some x => PMF.pure (y, ((m, (y, x)) :: cache, signed, invCache))
              | none =>
                (ProbComp.eval (sys.invert sk y)).map fun x =>
                  (y, ((m, (y, x)) :: cache, signed, (y, x) :: invCache)))
      (fun q ⟨cache, signed, invCache⟩ => by
        cases q with
        | inl m =>
          dsimp only [detLazyInvStep]
          cases cache.lookup m with
          | some yx => simp [PMF.pure_map]
          | none =>
            rw [PMF.map_bind]
            refine PMF.bind_congr_on_support _ _ _ fun y _ => ?_
            cases invCache.lookup y <;> simp [PMF.pure_map, PMF.map_comp, Function.comp_def]
        | inr m =>
          dsimp only [detLazyInvStep]
          cases cache.lookup m with
          | some yx => simp [PMF.pure_map]
          | none =>
            rw [PMF.map_bind]
            refine PMF.bind_congr_on_support _ _ _ fun y _ => ?_
            cases invCache.lookup y <;> simp [PMF.pure_map, PMF.map_comp, Function.comp_def])
      (forger pk) ([], [], []) false
    have hreassoc :
        ProbOracleComp.runWith (memoize fun y => ProbComp.eval (sys.invert sk y))
          ((OracleComp.interpret
            (OracleComp.sumHandler
              (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
              (detEagerHandler (M := M) (Target := Target) (Preimage := Preimage)))
            (forger pk)).run ([], [])) [] =
        (ProbOracleComp.runWith
          (fun q ((cache, signed, invCache) :
              List (M × (Target × Option Preimage)) × List M × List (Target × Option Preimage)) =>
            match q with
            | .inl m =>
              match cache.lookup m with
              | some (_, x) => PMF.pure (x, (cache, m :: signed, invCache))
              | none =>
                (PMF.uniformOfFintype Target).bind fun y =>
                  match invCache.lookup y with
                  | some x => PMF.pure (x, ((m, (y, x)) :: cache, m :: signed, invCache))
                  | none =>
                    (ProbComp.eval (sys.invert sk y)).map fun x =>
                      (x, ((m, (y, x)) :: cache, m :: signed, (y, x) :: invCache))
            | .inr m =>
              match cache.lookup m with
              | some (y, _) => PMF.pure (y, (cache, signed, invCache))
              | none =>
                (PMF.uniformOfFintype Target).bind fun y =>
                  match invCache.lookup y with
                  | some x => PMF.pure (y, ((m, (y, x)) :: cache, signed, invCache))
                  | none =>
                    (ProbComp.eval (sys.invert sk y)).map fun x =>
                      (y, ((m, (y, x)) :: cache, signed, (y, x) :: invCache)))
          (forger pk) ([], [], [])).map
          fun (out, (cache, signed, invCache)) => ((out, (cache, signed)), invCache) := by
      rw [ProbOracleComp.runWith_run_interpret]
      have hstep_map :
          (ProbOracleComp.runWith
            (fun q ((cache, signed, invCache) :
                List (M × (Target × Option Preimage)) × List M × List (Target × Option Preimage)) =>
              match q with
              | .inl m =>
                match cache.lookup m with
                | some (_, x) => PMF.pure (x, (cache, m :: signed, invCache))
                | none =>
                  (PMF.uniformOfFintype Target).bind fun y =>
                    match invCache.lookup y with
                    | some x => PMF.pure (x, ((m, (y, x)) :: cache, m :: signed, invCache))
                    | none =>
                      (ProbComp.eval (sys.invert sk y)).map fun x =>
                        (x, ((m, (y, x)) :: cache, m :: signed, (y, x) :: invCache))
              | .inr m =>
                match cache.lookup m with
                | some (y, _) => PMF.pure (y, (cache, signed, invCache))
                | none =>
                  (PMF.uniformOfFintype Target).bind fun y =>
                    match invCache.lookup y with
                    | some x => PMF.pure (y, ((m, (y, x)) :: cache, signed, invCache))
                    | none =>
                      (ProbComp.eval (sys.invert sk y)).map fun x =>
                        (y, ((m, (y, x)) :: cache, signed, (y, x) :: invCache)))
            (forger pk) ([], [], [])).map
              (fun (out, (cache, signed, invCache)) => (out, ((cache, signed), invCache))) =
          ProbOracleComp.runWith
            (fun q (state :
                (List (M × (Target × Option Preimage)) × List M) ×
                  List (Target × Option Preimage)) =>
              PMF.map (fun ((a, b), c) => (a, b, c))
                (ProbOracleComp.runWith (memoize fun y => ProbComp.eval (sys.invert sk y))
                  ((detEagerHandler (M := M) (Target := Target) (Preimage := Preimage) q).run
                    state.1)
                  state.2))
            (forger pk) (([], []), []) := by
        refine ProbOracleComp.runWith_map_state _ _
          (fun (st : List (M × (Target × Option Preimage)) × List M ×
              List (Target × Option Preimage)) =>
            let (cache, signed, invCache) := st
            ((cache, signed), invCache))
          ?_ (forger pk) ([], [], [])
        rintro (m | m) ⟨cache, signed, invCache⟩ <;>
        · dsimp only [detEagerHandler, StateT.run]
          cases cache.lookup m with
          | some yx => simp [ProbOracleComp.runWith_pure, PMF.pure_map]
          | none =>
            simp only [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_sample,
              ProbOracleComp.runWith_query, ProbOracleComp.runWith_pure, ProbComp.eval_uniform,
              PMF.map_bind, PMF.bind_map, memoize]
            refine PMF.bind_congr_on_support _ _ _ fun y _ => ?_
            cases hinv : invCache.lookup y with
            | some x => simp [hinv, PMF.pure_map, PMF.pure_bind]
            | none =>
              simp only [hinv, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind,
                PMF.pure_bind, PMF.map_bind, PMF.pure_map, PMF.map_comp, Function.comp_def]
              exact (PMF.bind_pure_comp _ _)
      have hcongr := congrArg (PMF.map fun (a, (b, c)) => ((a, b), c)) hstep_map
      simpa only [PMF.map_comp, Function.comp_def] using hcongr.symm
    unfold detEagerProg
    rw [ProbOracleComp.runWith_bind, hreassoc, PMF.map_bind, PMF.bind_map, ← hdrop, PMF.bind_map]
    refine PMF.bind_congr_on_support _ _ _ fun res _ => ?_
    rcases res with ⟨⟨mStar, sigStar⟩, ⟨⟨cache, signed, invCache⟩, _⟩⟩
    dsimp only [post, Function.comp_def, Prod.map]
    cases hlu : cache.lookup mStar with
    | some yx =>
      simp [hlu, ProbOracleComp.runWith_pure, PMF.pure_map]
    | none =>
      simp [hlu, ProbOracleComp.runWith_map, ProbOracleComp.runWith_sample,
        ProbComp.eval_uniform, PMF.map_comp, Function.comp_def]
  -- Step 1c: Match `psExperimentReal` at `(pk, sk)` to `withBadFlag (detFreshInvStep sys sk)`.
  have hfresh_eq :
      ProbComp.eval ((detPSDistinguisher sys forger pk).run fun _ => sys.sampleRealPair sk) =
      (ProbOracleComp.runWith (OracleComp.withBadFlag (detFreshInvStep sys sk)) (forger pk)
        (([], [], []), false)).bind post := by
    have hdrop_fresh :
        (ProbOracleComp.runWith (OracleComp.withBadFlag (detFreshInvStep sys sk)) (forger pk)
          (([], [], []), false)).map
            (fun (out, ((cache, signed, _), _)) => (out, (cache, signed))) =
        ProbComp.eval (((OracleComp.interpret
          (OracleComp.sumHandler
            (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
            (detPSHandler (M := M) (Target := Target) (Preimage := Preimage)))
          (forger pk)).run ([], [])).run fun _ => sys.sampleRealPair sk) := by
      rw [eval_run_run_interpret]
      refine ProbOracleComp.runWith_map_state _ _
        (fun (st : (List (M × (Target × Option Preimage)) × List M ×
            List (Target × Option Preimage)) × Bool) =>
          let ((cache, signed, _), _) := st
          (cache, signed))
        ?_ (forger pk) (([], [], []), false)
      rintro q ⟨⟨cache, signed, invCache⟩, b⟩
      cases q with
      | inl m =>
        dsimp only [OracleComp.withBadFlag, detFreshInvStep, detPSHandler]
        cases cache.lookup m with
        | some yx =>
          simp [ProbOracleComp.run_pure, ProbComp.eval_pure, PMF.pure_map]
        | none =>
          simp only [ProbOracleComp.run_bind, ProbOracleComp.run_query,
            ProbOracleComp.run_pure, ProbComp.eval_bind, ProbComp.eval_pure,
            TrapdoorPreimageSystem.sampleRealPair, ProbComp.eval_uniform,
            PMF.map_bind, PMF.bind_bind, PMF.pure_bind,
            PMF.map_comp, Function.comp_def, Prod.map]
          refine PMF.bind_congr_on_support _ _ _ fun y _ => ?_
          exact (PMF.bind_pure_comp _ _).symm
      | inr m =>
        dsimp only [OracleComp.withBadFlag, detFreshInvStep, detPSHandler]
        cases cache.lookup m with
        | some yx =>
          simp [ProbOracleComp.run_pure, ProbComp.eval_pure, PMF.pure_map]
        | none =>
          simp only [ProbOracleComp.run_bind, ProbOracleComp.run_query,
            ProbOracleComp.run_pure, ProbComp.eval_bind, ProbComp.eval_pure,
            TrapdoorPreimageSystem.sampleRealPair, ProbComp.eval_uniform,
            PMF.map_bind, PMF.bind_bind, PMF.pure_bind,
            PMF.map_comp, Function.comp_def, Prod.map]
          refine PMF.bind_congr_on_support _ _ _ fun y _ => ?_
          exact (PMF.bind_pure_comp _ _).symm
    simp only [detPSDistinguisher, ProbOracleComp.run_bind, ProbComp.eval_bind, ← hdrop_fresh,
      PMF.bind_map]
    refine PMF.bind_congr_on_support _ _ _ fun ⟨⟨mStar, sigStar⟩, ⟨⟨cache, signed, _⟩, _⟩⟩ _ => ?_
    dsimp only [post, Function.comp_def]
    cases cache.lookup mStar with
    | some yx => simp [ProbOracleComp.run_pure, ProbComp.eval_pure]
    | none =>
      simp [ProbOracleComp.run_sample, ProbComp.eval_uniform]
  rw [hlazy_eq, hfresh_eq]
  -- Step 1d: IdenticalUntilBad + `toOuterMeasure_bad_choose_two_le`.
  have hiub : ProbOracleComp.IdenticalUntilBad
      (OracleComp.withBadFlag (detLazyInvStep (M := M) sys sk))
      (OracleComp.withBadFlag (detFreshInvStep (M := M) sys sk))
      OracleComp.FlagBad := by
    refine ProbOracleComp.identicalUntilBad_withBadFlag _ _
      fun q ⟨cache, signed, invCache⟩ a s' => ?_
    cases q with
    | inl m =>
      dsimp only [detLazyInvStep, detFreshInvStep]
      cases cache.lookup m with
      | some yx => rfl
      | none =>
        simp only [PMF.bind_apply]
        refine tsum_congr fun y => ?_
        congr 1
        cases hlu : invCache.lookup y with
        | some x =>
          simp only [Option.isSome_some, PMF.pure_apply, PMF.map_apply]
          have h0 :
              (a, (s', false)) ≠ (x, ((m, (y, x)) :: cache, m :: signed, invCache), true) := by
            intro h; cases h
          have h1 : ∀ x', ¬((a, (s', false)) =
              (x', ((m, (y, x')) :: cache, m :: signed, (y, x') :: invCache), true)) := by
            intro x' h; cases h
          simp [h0, h1]
        | none =>
          simp
    | inr m =>
      dsimp only [detLazyInvStep, detFreshInvStep]
      cases cache.lookup m with
      | some yx => rfl
      | none =>
        simp only [PMF.bind_apply]
        refine tsum_congr fun y => ?_
        congr 1
        cases hlu : invCache.lookup y with
        | some x =>
          simp only [Option.isSome_some, PMF.pure_apply, PMF.map_apply]
          have h0 : (a, (s', false)) ≠ (y, ((m, (y, x)) :: cache, signed, invCache), true) := by
            intro h; cases h
          have h1 : ∀ x', ¬((a, (s', false)) =
              (y, ((m, (y, x')) :: cache, signed, (y, x') :: invCache), true)) := by
            intro x' h; cases h
          simp [h0, h1]
        | none =>
          simp
  have hdiff := hiub.bind_apply_le (forger pk) (([], [], []), false) post true
  rw [hiub.bad_eq] at hdiff
  refine hdiff.trans (add_le_add le_rfl ?_)
  have hbad := ProbOracleComp.toOuterMeasure_bad_choose_two_le
    (handler := OracleComp.withBadFlag (detFreshInvStep sys sk))
    (bad := OracleComp.FlagBad)
    (size := fun ((_, _, invCache), _) => invCache.length)
    (δ := (Fintype.card Target : ℝ≥0∞)⁻¹)
    (hstep := by
      rintro q ⟨⟨cache, signed, invCache⟩, b⟩ hb
      have hbf : b = false := Bool.eq_false_iff.mpr hb
      subst hbf
      rw [OracleComp.withBadFlag_false]
      cases q with
      | inl m =>
        dsimp only [detFreshInvStep]
        cases cache.lookup m with
        | some yx =>
          have h0 : (PMF.pure (yx.2, ((cache, m :: signed, invCache), false))).toOuterMeasure
              {x | OracleComp.FlagBad x.2} = 0 := by
            rw [PMF.toOuterMeasure_apply_eq_zero_iff]
            exact Set.disjoint_left.mpr fun x hx hbad => by
              rw [PMF.mem_support_pure_iff] at hx; subst hx; exact Bool.false_ne_true hbad
          rw [h0]; exact zero_le
        | none =>
          have heq :
              ((PMF.uniformOfFintype Target).bind fun y =>
                (ProbComp.eval (sys.invert sk y)).map fun x =>
                  (x, (((m, (y, x)) :: cache, m :: signed, (y, x) :: invCache),
                    (invCache.lookup y).isSome))).toOuterMeasure {x | OracleComp.FlagBad x.2} =
              (PMF.uniformOfFintype Target).toOuterMeasure
                {y | (invCache.lookup y).isSome = true} := by
            rw [PMF.toOuterMeasure_bind_apply]
            have hinner (y : Target) :
                ((ProbComp.eval (sys.invert sk y)).map fun x =>
                  (x, (((m, (y, x)) :: cache, m :: signed, (y, x) :: invCache),
                    (invCache.lookup y).isSome))).toOuterMeasure {x | OracleComp.FlagBad x.2} =
                if (invCache.lookup y).isSome = true then 1 else 0 := by
              rw [PMF.toOuterMeasure_map_apply]
              by_cases hy : (invCache.lookup y).isSome = true
              · simp [OracleComp.FlagBad, hy, PMF.toOuterMeasure_apply, PMF.tsum_coe]
              · simp [OracleComp.FlagBad, hy]
            simp only [hinner]
            rw [PMF.toOuterMeasure_apply]
            refine tsum_congr fun y => ?_
            by_cases hy : (invCache.lookup y).isSome = true
            · simp only [Set.indicator, Set.mem_ofPred_eq, hy, ↓reduceIte, mul_one]
            · simp only [Set.indicator, Set.mem_ofPred_eq, Bool.eq_false_iff.mpr hy,
                Bool.false_eq_true, ↓reduceIte, mul_zero]
          rw [heq]
          exact uniform_toOuterMeasure_lookup_isSome_le invCache
      | inr m =>
        dsimp only [detFreshInvStep]
        cases cache.lookup m with
        | some yx =>
          have h0 : (PMF.pure (yx.1, ((cache, signed, invCache), false))).toOuterMeasure
              {x | OracleComp.FlagBad x.2} = 0 := by
            rw [PMF.toOuterMeasure_apply_eq_zero_iff]
            exact Set.disjoint_left.mpr fun x hx hbad => by
              rw [PMF.mem_support_pure_iff] at hx; subst hx; exact Bool.false_ne_true hbad
          rw [h0]; exact zero_le
        | none =>
          have heq :
              ((PMF.uniformOfFintype Target).bind fun y =>
                (ProbComp.eval (sys.invert sk y)).map fun x =>
                  (y, (((m, (y, x)) :: cache, signed, (y, x) :: invCache),
                    (invCache.lookup y).isSome))).toOuterMeasure {x | OracleComp.FlagBad x.2} =
              (PMF.uniformOfFintype Target).toOuterMeasure
                {y | (invCache.lookup y).isSome = true} := by
            rw [PMF.toOuterMeasure_bind_apply]
            have hinner (y : Target) :
                ((ProbComp.eval (sys.invert sk y)).map fun x =>
                  (y, (((m, (y, x)) :: cache, signed, (y, x) :: invCache),
                    (invCache.lookup y).isSome))).toOuterMeasure {x | OracleComp.FlagBad x.2} =
                if (invCache.lookup y).isSome = true then 1 else 0 := by
              rw [PMF.toOuterMeasure_map_apply]
              by_cases hy : (invCache.lookup y).isSome = true
              · simp [OracleComp.FlagBad, hy, PMF.toOuterMeasure_apply, PMF.tsum_coe]
              · simp [OracleComp.FlagBad, hy]
            simp only [hinner]
            rw [PMF.toOuterMeasure_apply]
            refine tsum_congr fun y => ?_
            by_cases hy : (invCache.lookup y).isSome = true
            · simp only [Set.indicator, Set.mem_ofPred_eq, hy, ↓reduceIte, mul_one]
            · simp only [Set.indicator, Set.mem_ofPred_eq, Bool.eq_false_iff.mpr hy,
                Bool.false_eq_true, ↓reduceIte, mul_zero]
          rw [heq]
          exact uniform_toOuterMeasure_lookup_isSome_le invCache)
    (hgrow := by
      rintro q ⟨⟨cache, signed, invCache⟩, b⟩ hb x hx _
      have hbf : b = false := Bool.eq_false_iff.mpr hb
      subst hbf
      rw [OracleComp.withBadFlag_false] at hx
      cases q with
      | inl m =>
        dsimp only [detFreshInvStep] at hx
        cases hlu : cache.lookup m with
        | some yx =>
          rw [hlu, PMF.mem_support_pure_iff] at hx; subst hx; dsimp only; omega
        | none =>
          rw [hlu, PMF.mem_support_bind_iff] at hx
          obtain ⟨y, -, hx⟩ := hx
          rw [PMF.mem_support_map_iff] at hx
          obtain ⟨p, -, rfl⟩ := hx
          simp
      | inr m =>
        dsimp only [detFreshInvStep] at hx
        cases hlu : cache.lookup m with
        | some yx =>
          rw [hlu, PMF.mem_support_pure_iff] at hx; subst hx; dsimp only; omega
        | none =>
          rw [hlu, PMF.mem_support_bind_iff] at hx
          obtain ⟨y, -, hx⟩ := hx
          rw [PMF.mem_support_map_iff] at hx
          obtain ⟨p, -, rfl⟩ := hx
          simp)
    (hforger.isQueryBounded pk) (s := (([], [], []), false)) (by simp [OracleComp.FlagBad])
  simpa only [List.length_nil, mul_zero, zero_add] using hbad

/-- Tracked state for the Bellare–Rogaway guess and zero-loss abort hop (`G2 → G3`) in
`detScheme`. -/
private structure DetTrackState (M Target Preimage : Type) where
  cache : List (M × (Target × Option Preimage × Option ℕ))
  signed : List M
  hCount : ℕ
  badSignJ : Bool

private noncomputable def detTrackHandler [DecidableEq M]
    (sys : TrapdoorPreimageSystem PK SK Target Preimage) (pk : PK) (jStar : ℕ)
    (q : M ⊕ M) (st : DetTrackState M Target Preimage) :
    PMF (ROMSignature.ForgerSpec M M (Option Preimage) Target q ×
      DetTrackState M Target Preimage) :=
  match q with
  | .inl m =>
    match st.cache.lookup m with
    | some (_, x, idxOpt) =>
      PMF.pure (x, { st with
        signed := m :: st.signed
        badSignJ := st.badSignJ || (idxOpt == some jStar) })
    | none =>
      (ProbComp.eval (sys.sampleSimPair pk)).map fun yx =>
        (yx.2, { st with
          cache := (m, (yx.1, yx.2, none)) :: st.cache
          signed := m :: st.signed })
  | .inr m =>
    match st.cache.lookup m with
    | some (y, _, _) => PMF.pure (y, st)
    | none =>
      (ProbComp.eval (sys.sampleSimPair pk)).map fun yx =>
        (yx.1, { st with
          cache := (m, (yx.1, yx.2, some st.hCount)) :: st.cache
          hCount := st.hCount + 1 })

private noncomputable def detAbortHandler [DecidableEq M]
    (sys : TrapdoorPreimageSystem PK SK Target Preimage) (pk : PK) (jStar : ℕ)
    (q : M ⊕ M) (st : DetTrackState M Target Preimage) :
    PMF (ROMSignature.ForgerSpec M M (Option Preimage) Target q ×
      DetTrackState M Target Preimage) :=
  match q with
  | .inl m =>
    match st.cache.lookup m with
    | some (_, x, idxOpt) =>
      if idxOpt = some jStar then
        PMF.pure (none, { st with signed := m :: st.signed, badSignJ := true })
      else
        PMF.pure (x, { st with signed := m :: st.signed })
    | none =>
      (ProbComp.eval (sys.sampleSimPair pk)).map fun yx =>
        (yx.2, { st with
          cache := (m, (yx.1, yx.2, none)) :: st.cache
          signed := m :: st.signed })
  | .inr m =>
    match st.cache.lookup m with
    | some (y, _, _) => PMF.pure (y, st)
    | none =>
      (ProbComp.eval (sys.sampleSimPair pk)).map fun yx =>
        (yx.1, { st with
          cache := (m, (yx.1, yx.2, some st.hCount)) :: st.cache
          hCount := st.hCount + 1 })

private theorem detCache_cons_indexed {M Target Payload : Type}
    {cache : List (M × (Target × Payload × Option ℕ))} {signed : List M} {hCount : ℕ}
    (m : M) (y : Target) (p : Payload)
    (hsign : ∀ m' y' p', (m', (y', p', none)) ∈ cache → m' ∈ signed)
    (hlt : ∀ m' y' p' k, (m', (y', p', some k)) ∈ cache → k < hCount) :
    (∀ m' y' p', (m', (y', p', none)) ∈ (m, (y, p, some hCount)) :: cache → m' ∈ signed) ∧
    (∀ m' y' p' k, (m', (y', p', some k)) ∈ (m, (y, p, some hCount)) :: cache →
      k < hCount + 1) := by
  refine ⟨?_, ?_⟩
  · intro m' y' p' hm'
    rcases List.mem_cons.mp hm' with hhd | htl
    · injection hhd with _ h2; injection h2 with _ h3; injection h3 with _ h4; cases h4
    · exact hsign m' y' p' htl
  · intro m' y' p' k hm'
    rcases List.mem_cons.mp hm' with hhd | htl
    · injection hhd with _ h2; injection h2 with _ h3; injection h3 with _ h4
      injection h4 with hk; subst hk; omega
    · exact Nat.lt_succ_of_lt (hlt m' y' p' k htl)

private theorem detCache_cons_unindexed {M Target Payload : Type}
    {cache : List (M × (Target × Payload × Option ℕ))} {signed : List M} {hCount : ℕ}
    (m : M) (y : Target) (p : Payload)
    (hsign : ∀ m' y' p', (m', (y', p', none)) ∈ cache → m' ∈ signed)
    (hlt : ∀ m' y' p' k, (m', (y', p', some k)) ∈ cache → k < hCount) :
    (∀ m' y' p', (m', (y', p', none)) ∈ (m, (y, p, none)) :: cache → m' ∈ m :: signed) ∧
    (∀ m' y' p' k, (m', (y', p', some k)) ∈ (m, (y, p, none)) :: cache → k < hCount) := by
  refine ⟨?_, ?_⟩
  · intro m' y' p' hm'
    rcases List.mem_cons.mp hm' with hhd | htl
    · injection hhd with hm' _; subst hm'; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hsign m' y' p' htl)
  · intro m' y' p' k hm'
    rcases List.mem_cons.mp hm' with hhd | htl
    · injection hhd with _ h2; injection h2 with _ h3; injection h3 with _ h4; cases h4
    · exact hlt m' y' p' k htl

private def DetTrackInv {M Target Preimage : Type} (jStar : ℕ)
    (st : DetTrackState M Target Preimage) : Prop :=
  (∀ m y x, (m, (y, x, none)) ∈ st.cache → m ∈ st.signed) ∧
  (∀ m y x k, (m, (y, x, some k)) ∈ st.cache → k < st.hCount) ∧
  (∀ m₁ y₁ x₁ m₂ y₂ x₂, (m₁, (y₁, x₁, some jStar)) ∈ st.cache →
    (m₂, (y₂, x₂, some jStar)) ∈ st.cache → m₁ = m₂) ∧
  (st.badSignJ = true → jStar < st.hCount ∧
    ∀ m y x, (m, (y, x, some jStar)) ∈ st.cache → m ∈ st.signed)

private theorem detTrackInv_init {M Target Preimage : Type} (jStar : ℕ) :
    DetTrackInv (M := M) (Target := Target) (Preimage := Preimage) jStar ⟨[], [], 0, false⟩ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m y x hm; cases hm
  · intro m y x k hm; cases hm
  · intro m₁ y₁ x₁ m₂ y₂ x₂ hm₁; cases hm₁
  · intro hb; exact absurd hb Bool.false_ne_true

private theorem detTrackInv_step [DecidableEq M]
    (sys : TrapdoorPreimageSystem PK SK Target Preimage) (pk : PK) (jStar : ℕ) :
    ∀ q (st : DetTrackState M Target Preimage), DetTrackInv jStar st →
      ∀ a st', (a, st') ∈ (detTrackHandler sys pk jStar q st).support → DetTrackInv jStar st' := by
  rintro q st ⟨hsign, hlt, huniq, hbad⟩ a st' hstep
  cases q with
  | inl m =>
    dsimp only [detTrackHandler] at hstep
    cases hlu : st.cache.lookup m with
    | some yxk =>
      rcases yxk with ⟨y, x, idxOpt⟩
      rw [hlu, PMF.mem_support_pure_iff, Prod.mk.injEq] at hstep
      obtain ⟨-, rfl⟩ := hstep
      refine ⟨fun m' y' x' hm' => List.mem_cons_of_mem _ (hsign m' y' x' hm'), hlt, huniq, ?_⟩
      intro hb
      simp only [Bool.or_eq_true, beq_iff_eq] at hb
      rcases hb with hb_old | hidx
      · obtain ⟨hgt, hs⟩ := hbad hb_old
        exact ⟨hgt, fun m' y' x' hm' => List.mem_cons_of_mem _ (hs m' y' x' hm')⟩
      · subst hidx
        have hmem := mem_of_lookup_eq_some hlu
        refine ⟨hlt m y x jStar hmem, fun m' y' x' hm' => ?_⟩
        have hm_eq : m' = m := huniq m' y' x' m y x hm' hmem
        subst hm_eq
        exact List.mem_cons_self
    | none =>
      rw [hlu, PMF.mem_support_map_iff] at hstep
      obtain ⟨yx, -, heq⟩ := hstep
      rw [Prod.mk.injEq] at heq
      obtain ⟨-, rfl⟩ := heq
      obtain ⟨hsign', hlt'⟩ := detCache_cons_unindexed m yx.1 yx.2 hsign hlt
      refine ⟨hsign', hlt', ?_, ?_⟩
      · intro m₁ y₁ x₁ m₂ y₂ x₂ hm₁ hm₂
        rcases List.mem_cons.mp hm₁ with hhd | htl₁
        · injection hhd with _ h2; injection h2 with _ h3; injection h3 with _ h4; cases h4
        rcases List.mem_cons.mp hm₂ with hhd | htl₂
        · injection hhd with _ h2; injection h2 with _ h3; injection h3 with _ h4; cases h4
        exact huniq m₁ y₁ x₁ m₂ y₂ x₂ htl₁ htl₂
      · intro hb
        obtain ⟨hgt, hs⟩ := hbad hb
        refine ⟨hgt, fun m' y' x' hm' => ?_⟩
        rcases List.mem_cons.mp hm' with hhd | htl
        · injection hhd with _ h2; injection h2 with _ h3; injection h3 with _ h4; cases h4
        · exact List.mem_cons_of_mem _ (hs m' y' x' htl)
  | inr m =>
    dsimp only [detTrackHandler] at hstep
    cases hlu : st.cache.lookup m with
    | some yxk =>
      rcases yxk with ⟨y, x, idxOpt⟩
      rw [hlu, PMF.mem_support_pure_iff, Prod.mk.injEq] at hstep
      obtain ⟨-, rfl⟩ := hstep
      exact ⟨hsign, hlt, huniq, hbad⟩
    | none =>
      rw [hlu, PMF.mem_support_map_iff] at hstep
      obtain ⟨yx, -, heq⟩ := hstep
      rw [Prod.mk.injEq] at heq
      obtain ⟨-, rfl⟩ := heq
      obtain ⟨hsign', hlt'⟩ := detCache_cons_indexed m yx.1 yx.2 hsign hlt
      refine ⟨hsign', hlt', ?_, ?_⟩
      · intro m₁ y₁ x₁ m₂ y₂ x₂ hm₁ hm₂
        rcases List.mem_cons.mp hm₁ with hhd₁ | htl₁ <;>
          rcases List.mem_cons.mp hm₂ with hhd₂ | htl₂
        · injection hhd₁ with hm1 _; injection hhd₂ with hm2 _; exact hm1.trans hm2.symm
        · injection hhd₁ with _ h2; injection h2 with _ h3; injection h3 with _ h4
          injection h4 with hj; have := hlt m₂ y₂ x₂ jStar htl₂; omega
        · injection hhd₂ with _ h2; injection h2 with _ h3; injection h3 with _ h4
          injection h4 with hj; have := hlt m₁ y₁ x₁ jStar htl₁; omega
        · exact huniq m₁ y₁ x₁ m₂ y₂ x₂ htl₁ htl₂
      · intro hb
        obtain ⟨hgt, hs⟩ := hbad hb
        refine ⟨Nat.lt_succ_of_lt hgt, fun m' y' x' hm' => ?_⟩
        rcases List.mem_cons.mp hm' with hhd | htl
        · injection hhd with _ h2; injection h2 with _ h3; injection h3 with _ h4
          injection h4 with hj; exact absurd hj (by omega)
        · exact hs m' y' x' htl

private theorem detTrack_identicalUntilBad_detAbort [DecidableEq M]
    (sys : TrapdoorPreimageSystem PK SK Target Preimage) (pk : PK) (jStar : ℕ) :
    ProbOracleComp.IdenticalUntilBad
      (detTrackHandler (M := M) sys pk jStar)
      (detAbortHandler (M := M) sys pk jStar)
      (fun st => st.badSignJ = true) := by
  refine OracleComp.IdenticalUntilBad.probOracleComp
    { agree := by
        intro q st hst a st' hst'
        have hbf : st.badSignJ = false := Bool.eq_false_iff.mpr hst
        have hbf' : st'.badSignJ = false := Bool.eq_false_iff.mpr hst'
        cases q with
        | inl m =>
          dsimp only [detTrackHandler, detAbortHandler]
          cases st.cache.lookup m with
          | none => rfl
          | some yxk =>
            rcases yxk with ⟨y, x, idxOpt⟩
            by_cases hidx : idxOpt = some jStar
            · subst hidx
              simp only [beq_self_eq_true, Bool.or_true, ↓reduceIte, PMF.pure_apply]
              have hne1 :
                  (a, st') ≠ (x, { st with signed := m :: st.signed, badSignJ := true }) := by
                intro h; have := congrArg (fun p => p.2.badSignJ) h; simp [hbf'] at this
              have hne2 :
                  (a, st') ≠ (none, { st with signed := m :: st.signed, badSignJ := true }) := by
                intro h; have := congrArg (fun p => p.2.badSignJ) h; simp [hbf'] at this
              simp [hne1, hne2]
            · have hbeq : (idxOpt == some jStar) = false := beq_false_of_ne hidx
              simp [hidx, hbeq, hbf]
        | inr m => rfl
      absorb_first := by
        intro q st hst x hx
        cases q with
        | inl m =>
          dsimp only [detTrackHandler] at hx
          cases hlu : st.cache.lookup m with
          | some yxk =>
            rw [hlu, PMF.mem_support_pure_iff] at hx; subst hx; simp [hst]
          | none =>
            rw [hlu, PMF.mem_support_map_iff] at hx
            obtain ⟨_, -, rfl⟩ := hx; exact hst
        | inr m =>
          dsimp only [detTrackHandler] at hx
          cases hlu : st.cache.lookup m with
          | some yxk => rw [hlu, PMF.mem_support_pure_iff] at hx; subst hx; exact hst
          | none =>
            rw [hlu, PMF.mem_support_map_iff] at hx
            obtain ⟨_, -, rfl⟩ := hx; exact hst
      absorb_second := by
        intro q st hst x hx
        cases q with
        | inl m =>
          dsimp only [detAbortHandler] at hx
          cases hlu : st.cache.lookup m with
          | some yxk =>
            rcases yxk with ⟨y, x', idxOpt⟩
            rw [hlu] at hx
            dsimp only at hx
            split_ifs at hx with hidx
            · rw [PMF.mem_support_pure_iff] at hx; subst hx; rfl
            · rw [PMF.mem_support_pure_iff] at hx; subst hx; exact hst
          | none =>
            rw [hlu, PMF.mem_support_map_iff] at hx
            obtain ⟨_, -, rfl⟩ := hx; exact hst
        | inr m =>
          dsimp only [detAbortHandler] at hx
          cases hlu : st.cache.lookup m with
          | some yxk => rw [hlu, PMF.mem_support_pure_iff] at hx; subst hx; exact hst
          | none =>
            rw [hlu, PMF.mem_support_map_iff] at hx
            obtain ⟨_, -, rfl⟩ := hx; exact hst }

/-- State for the unified one-point embedding simulation (`detOneTrackHandler` /
`detOneEmbedHandler`), reused for both `μ_star = (sampleSimPair pk).map Prod.fst` (G3) and
`μ_star = uniform Target` (G4). -/
private structure DetOneState (M Target Preimage : Type) where
  cache : List (M × (Target × Option (Option Preimage) × Option ℕ))
  signed : List M
  hCount : ℕ
  yAtJ : Option Target

private noncomputable def detOneTrackHandler [DecidableEq M]
    (sys : TrapdoorPreimageSystem PK SK Target Preimage) (pk : PK) (jStar : ℕ)
    (μStar : PMF Target) (q : M ⊕ M) (st : DetOneState M Target Preimage) :
    PMF (ROMSignature.ForgerSpec M M (Option Preimage) Target q ×
      DetOneState M Target Preimage) :=
  match q with
  | .inl m =>
    match st.cache.lookup m with
    | some (_, some x, _) => PMF.pure (x, { st with signed := m :: st.signed })
    | some (_, none, _) => PMF.pure (none, { st with signed := m :: st.signed })
    | none =>
      (ProbComp.eval (sys.sampleSimPair pk)).map fun yx =>
        (yx.2, { st with
          cache := (m, (yx.1, some yx.2, none)) :: st.cache
          signed := m :: st.signed })
  | .inr m =>
    match st.cache.lookup m with
    | some (y, _, _) => PMF.pure (y, st)
    | none =>
      if st.hCount = jStar then
        μStar.map fun y =>
          (y, { st with
            cache := (m, (y, none, some st.hCount)) :: st.cache
            hCount := st.hCount + 1
            yAtJ := some y })
      else
        (ProbComp.eval (sys.sampleSimPair pk)).map fun yx =>
          (yx.1, { st with
            cache := (m, (yx.1, some yx.2, some st.hCount)) :: st.cache
            hCount := st.hCount + 1 })

private noncomputable def detOneEmbedHandler [DecidableEq M]
    (sys : TrapdoorPreimageSystem PK SK Target Preimage) (pk : PK) (jStar : ℕ)
    (q : M ⊕ M) (stY : DetOneState M Target Preimage × Target) :
    PMF (ROMSignature.ForgerSpec M M (Option Preimage) Target q ×
      (DetOneState M Target Preimage × Target)) :=
  let (st, yStar) := stY
  match q with
  | .inl m =>
    match st.cache.lookup m with
    | some (_, some x, _) => PMF.pure (x, ({ st with signed := m :: st.signed }, yStar))
    | some (_, none, _) => PMF.pure (none, ({ st with signed := m :: st.signed }, yStar))
    | none =>
      (ProbComp.eval (sys.sampleSimPair pk)).map fun yx =>
        (yx.2, ({ st with
          cache := (m, (yx.1, some yx.2, none)) :: st.cache
          signed := m :: st.signed }, yStar))
  | .inr m =>
    match st.cache.lookup m with
    | some (y, _, _) => PMF.pure (y, (st, yStar))
    | none =>
      if st.hCount = jStar then
        PMF.pure (yStar, ({ st with
          cache := (m, (yStar, none, some st.hCount)) :: st.cache
          hCount := st.hCount + 1
          yAtJ := some yStar }, yStar))
      else
        (ProbComp.eval (sys.sampleSimPair pk)).map fun yx =>
          (yx.1, ({ st with
            cache := (m, (yx.1, some yx.2, some st.hCount)) :: st.cache
            hCount := st.hCount + 1 }, yStar))

private noncomputable def detOneRelate {M Target Preimage : Type} (μStar : PMF Target)
    (st : DetOneState M Target Preimage) : PMF (DetOneState M Target Preimage × Target) :=
  match st.yAtJ with
  | some y => PMF.pure (st, y)
  | none => μStar.map (st, ·)

private theorem detOneRelate_proj_state {M Target Preimage : Type}
    (dist : PMF ((M × Option Preimage) × DetOneState M Target Preimage)) (μ : PMF Target) :
    (dist.bind (fun (out, st) => (detOneRelate μ st).map (out, ·))).map
      (fun (out, (st, _)) => (out, (st.cache, st.signed, st.hCount))) =
    dist.map (fun (out, st) => (out, (st.cache, st.signed, st.hCount))) := by
  rw [PMF.map_bind]
  refine (PMF.bind_congr_on_support _ _ _ fun ⟨out, st⟩ _ => ?_).trans
    (PMF.bind_pure_comp _ _).symm
  cases hyj : st.yAtJ with
  | some y => simp [detOneRelate, hyj, PMF.pure_map]
  | none =>
    simp only [detOneRelate, hyj, PMF.map_comp, Function.comp_def]
    exact PMF.map_const _ _

private def DetOneInv {M Target Preimage : Type} (jStar : ℕ)
    (st : DetOneState M Target Preimage) : Prop :=
  (st.hCount ≤ jStar → st.yAtJ = none) ∧
  (∀ m y xOpt, (m, (y, xOpt, none)) ∈ st.cache → m ∈ st.signed) ∧
  (∀ m y xOpt k, (m, (y, xOpt, some k)) ∈ st.cache → k < st.hCount) ∧
  (∀ m y xOpt, (m, (y, xOpt, some jStar)) ∈ st.cache → st.yAtJ = some y)

private theorem detOneInv_init {M Target Preimage : Type} (jStar : ℕ) :
    DetOneInv (M := M) (Target := Target) (Preimage := Preimage) jStar ⟨[], [], 0, none⟩ := by
  refine ⟨fun _ => rfl, ?_, ?_, ?_⟩
  · intro m y xOpt hm; cases hm
  · intro m y xOpt k hm; cases hm
  · intro m y xOpt hm; cases hm

private theorem detOneInv_cons_cache {M Target Preimage : Type} {jStar : ℕ}
    {st : DetOneState M Target Preimage} {m : M} {y : Target} {xOpt : Option (Option Preimage)}
    {yAtJ' : Option Target}
    (hsign : ∀ m' y' x', (m', (y', x', none)) ∈ st.cache → m' ∈ st.signed)
    (hlt : ∀ m' y' x' k, (m', (y', x', some k)) ∈ st.cache → k < st.hCount)
    (hnone' : st.hCount + 1 ≤ jStar → yAtJ' = none)
    (hyj' : ∀ m' y' x', (m', (y', x', some jStar)) ∈ (m, (y, xOpt, some st.hCount)) :: st.cache →
      yAtJ' = some y') :
    DetOneInv jStar
      ⟨(m, (y, xOpt, some st.hCount)) :: st.cache, st.signed, st.hCount + 1, yAtJ'⟩ :=
  let ⟨hsign', hlt'⟩ := detCache_cons_indexed m y xOpt hsign hlt
  ⟨hnone', hsign', hlt', hyj'⟩

private theorem detOneInv_step [DecidableEq M]
    (sys : TrapdoorPreimageSystem PK SK Target Preimage) (pk : PK) (jStar : ℕ)
    (μStar : PMF Target) :
    ∀ q (st : DetOneState M Target Preimage), DetOneInv jStar st →
      ∀ a st', (a, st') ∈ (detOneTrackHandler sys pk jStar μStar q st).support →
        DetOneInv jStar st' := by
  rintro q st ⟨hnone, hsign, hlt, hyj⟩ a st' hstep
  cases q with
  | inl m =>
    dsimp only [detOneTrackHandler] at hstep
    cases hlu : st.cache.lookup m with
    | some yxk =>
      rcases yxk with ⟨y, xOpt, idxOpt⟩
      cases xOpt with
      | some x =>
        rw [hlu, PMF.mem_support_pure_iff, Prod.mk.injEq] at hstep
        obtain ⟨-, rfl⟩ := hstep
        exact ⟨hnone, fun m' y' x' hm' => List.mem_cons_of_mem _ (hsign m' y' x' hm'), hlt, hyj⟩
      | none =>
        rw [hlu, PMF.mem_support_pure_iff, Prod.mk.injEq] at hstep
        obtain ⟨-, rfl⟩ := hstep
        exact ⟨hnone, fun m' y' x' hm' => List.mem_cons_of_mem _ (hsign m' y' x' hm'), hlt, hyj⟩
    | none =>
      rw [hlu, PMF.mem_support_map_iff] at hstep
      obtain ⟨yx, -, heq⟩ := hstep
      rw [Prod.mk.injEq] at heq
      obtain ⟨-, rfl⟩ := heq
      obtain ⟨hsign', hlt'⟩ := detCache_cons_unindexed m yx.1 (some yx.2) hsign hlt
      refine ⟨hnone, hsign', hlt', ?_⟩
      · intro m' y' x' hm'
        rcases List.mem_cons.mp hm' with hhd | htl
        · injection hhd with _ h2; injection h2 with _ h3; injection h3 with _ h4; cases h4
        · exact hyj m' y' x' htl
  | inr m =>
    dsimp only [detOneTrackHandler] at hstep
    cases hlu : st.cache.lookup m with
    | some yxk =>
      rw [hlu, PMF.mem_support_pure_iff, Prod.mk.injEq] at hstep
      obtain ⟨-, rfl⟩ := hstep
      exact ⟨hnone, hsign, hlt, hyj⟩
    | none =>
      rw [hlu] at hstep
      split_ifs at hstep with heq
      · rw [PMF.mem_support_map_iff] at hstep
        obtain ⟨y, -, hpair⟩ := hstep
        rw [Prod.mk.injEq] at hpair
        obtain ⟨-, rfl⟩ := hpair
        refine detOneInv_cons_cache hsign hlt (fun hle => by omega) ?_
        intro m' y' x' hm'
        rcases List.mem_cons.mp hm' with hhd | htl
        · injection hhd with _ h2; injection h2 with hy' _; subst hy'; rfl
        · have := hlt m' y' x' jStar htl; omega
      · rw [PMF.mem_support_map_iff] at hstep
        obtain ⟨yx, -, hpair⟩ := hstep
        rw [Prod.mk.injEq] at hpair
        obtain ⟨-, rfl⟩ := hpair
        refine detOneInv_cons_cache hsign hlt (fun hle => hnone (Nat.le_of_succ_le hle)) ?_
        intro m' y' x' hm'
        rcases List.mem_cons.mp hm' with hhd | htl
        · injection hhd with _ h2; injection h2 with _ h3; injection h3 with _ h4
          injection h4 with hk; exact absurd hk.symm heq
        · exact hyj m' y' x' htl

/-- Unified upfront-vs-lazy embedding simulation for `detScheme`, parameterized by any `μStar`. -/
private theorem detOneTrack_sim_detOneEmbed [DecidableEq M]
    (sys : TrapdoorPreimageSystem PK SK Target Preimage) (pk : PK) (jStar : ℕ)
    (μStar : PMF Target)
    (forger : PK → ProbOracleComp
      (ROMSignature.ForgerSpec M M (Option Preimage) Target) (M × Option Preimage)) :
    (ProbOracleComp.runWith (detOneTrackHandler sys pk jStar μStar) (forger pk)
      ⟨[], [], 0, none⟩).bind
      (fun (out, st) => (detOneRelate μStar st).map (out, ·)) =
    μStar.bind fun yStar =>
      ProbOracleComp.runWith (detOneEmbedHandler sys pk jStar) (forger pk)
        (⟨[], [], 0, none⟩, yStar) := by
  have hsim := ProbOracleComp.runWith_simulation_of_invariant
    (detOneTrackHandler sys pk jStar μStar)
    (detOneEmbedHandler sys pk jStar)
    (detOneRelate μStar)
    (DetOneInv jStar)
    (detOneInv_step sys pk jStar μStar)
    (fun q st hinv => by
      cases q with
      | inl m =>
        dsimp only [detOneTrackHandler, detOneEmbedHandler]
        cases hlu : st.cache.lookup m with
        | some yxk =>
          rcases yxk with ⟨y, xOpt, idxOpt⟩
          cases xOpt with
          | some x =>
            cases hyj : st.yAtJ with
            | some y0 =>
              simp only [detOneEmbedHandler, hlu, detOneRelate, hyj, PMF.map, PMF.pure_bind,
                Function.comp_def]
            | none =>
              simp only [detOneEmbedHandler, hlu, detOneRelate, hyj, PMF.map, PMF.bind_bind,
                PMF.pure_bind, Function.comp_def]
          | none =>
            cases hyj : st.yAtJ with
            | some y0 =>
              simp only [detOneEmbedHandler, hlu, detOneRelate, hyj, PMF.map, PMF.pure_bind,
                Function.comp_def]
            | none =>
              simp only [detOneEmbedHandler, hlu, detOneRelate, hyj, PMF.map, PMF.bind_bind,
                PMF.pure_bind, Function.comp_def]
        | none =>
          cases hyj : st.yAtJ with
          | some y0 =>
            simp only [detOneEmbedHandler, hlu, detOneRelate, hyj, PMF.map, PMF.bind_bind,
              PMF.pure_bind, Function.comp_def]
          | none =>
            simp only [detOneEmbedHandler, hlu, detOneRelate, hyj, PMF.map, PMF.bind_bind,
              PMF.pure_bind, Function.comp_def]
            exact PMF.bind_comm _ _ _
      | inr m =>
        dsimp only [detOneTrackHandler, detOneEmbedHandler]
        cases hlu : st.cache.lookup m with
        | some yxk =>
          cases hyj : st.yAtJ with
          | some y0 =>
            simp only [detOneEmbedHandler, hlu, detOneRelate, hyj, PMF.map, PMF.pure_bind,
              Function.comp_def]
          | none =>
            simp only [detOneEmbedHandler, hlu, detOneRelate, hyj, PMF.map, PMF.bind_bind,
              PMF.pure_bind, Function.comp_def]
        | none =>
          by_cases heq : st.hCount = jStar
          · have hyj_none : st.yAtJ = none := hinv.1 (le_of_eq heq)
            simp only [detOneEmbedHandler, hlu, heq, ↓reduceIte, detOneRelate, hyj_none, PMF.map,
              PMF.bind_bind, PMF.pure_bind, Function.comp_def]
          · cases hyj : st.yAtJ with
            | some y0 =>
              simp only [detOneEmbedHandler, hlu, heq, ↓reduceIte, detOneRelate, hyj, PMF.map,
                PMF.bind_bind, PMF.pure_bind, Function.comp_def]
            | none =>
              simp only [detOneEmbedHandler, hlu, heq, ↓reduceIte, detOneRelate, hyj, PMF.map,
                PMF.bind_bind, PMF.pure_bind, Function.comp_def]
              exact PMF.bind_comm _ _ _)
    (forger pk) ⟨[], [], 0, none⟩ (detOneInv_init jStar)
  simpa only [detOneRelate, PMF.bind_map, Function.comp_def] using hsim

private theorem lookup_map_det_erase {K A B : Type} [BEq K] (jStar : ℕ)
    (l : List (K × A × B × Option ℕ)) (q : K) :
    (l.map fun (k, y, x, idxOpt) =>
      (k, (y, if idxOpt = some jStar then none else some x, idxOpt))).lookup q =
    (l.lookup q).map fun (y, x, idxOpt) =>
      (y, if idxOpt = some jStar then none else some x, idxOpt) := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k, y, x, idxOpt⟩
    simp only [List.map_cons, List.lookup_cons]
    cases (q == k) <;> simp [ih]

private theorem lookup_map_det_strip {K A B : Type} [BEq K]
    (l : List (K × A × B × Option ℕ)) (q : K) :
    (l.map fun (k, y, x, _) => (k, (y, x))).lookup q =
    (l.lookup q).map fun (y, x, _) => (y, x) := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k, y, x, idxOpt⟩
    simp only [List.map_cons, List.lookup_cons]
    cases (q == k) <;> simp [ih]

private theorem detOneEmbedHandler_yStar_step [DecidableEq M]
    (sys : TrapdoorPreimageSystem PK SK Target Preimage) (pk : PK) (jStar : ℕ) (yStar : Target)
    (q : M ⊕ M) (s : DetOneState M Target Preimage × Target) (hyS : s.2 = yStar)
    (a : ROMSignature.ForgerSpec M M (Option Preimage) Target q)
    (s' : DetOneState M Target Preimage × Target)
    (hstep : (a, s') ∈ (detOneEmbedHandler sys pk jStar q s).support) :
    s'.2 = yStar := by
  rcases s with ⟨st, yS⟩
  rcases s' with ⟨st', yS'⟩
  dsimp only at hyS ⊢
  subst hyS
  cases q with
  | inl m =>
    dsimp only [detOneEmbedHandler] at hstep
    cases hlu : st.cache.lookup m with
    | some yxk =>
      rcases yxk with ⟨y, xOpt, idxOpt⟩
      cases xOpt <;>
        (rw [hlu, PMF.mem_support_pure_iff, Prod.mk.injEq, Prod.mk.injEq] at hstep;
          obtain ⟨-, -, rfl⟩ := hstep; rfl)
    | none =>
      rw [hlu, PMF.mem_support_map_iff] at hstep
      obtain ⟨_, -, heq⟩ := hstep
      rw [Prod.mk.injEq, Prod.mk.injEq] at heq
      obtain ⟨-, -, rfl⟩ := heq; rfl
  | inr m =>
    dsimp only [detOneEmbedHandler] at hstep
    cases hlu : st.cache.lookup m with
    | some yxk =>
      rw [hlu, PMF.mem_support_pure_iff, Prod.mk.injEq, Prod.mk.injEq] at hstep
      obtain ⟨-, -, rfl⟩ := hstep; rfl
    | none =>
      rw [hlu] at hstep
      split_ifs at hstep with heq
      · rw [PMF.mem_support_pure_iff, Prod.mk.injEq, Prod.mk.injEq] at hstep
        obtain ⟨-, -, rfl⟩ := hstep; rfl
      · rw [PMF.mem_support_map_iff] at hstep
        obtain ⟨_, -, heq2⟩ := hstep
        rw [Prod.mk.injEq, Prod.mk.injEq] at heq2
        obtain ⟨-, -, rfl⟩ := heq2; rfl

private theorem detOneEmbed_map_eq_detPSOneSim [DecidableEq M]
    (sys : TrapdoorPreimageSystem PK SK Target Preimage) (pk : PK) (jStar : ℕ) (yStar : Target)
    (forger : PK → ProbOracleComp
      (ROMSignature.ForgerSpec M M (Option Preimage) Target) (M × Option Preimage)) :
    (ProbOracleComp.runWith (detOneEmbedHandler sys pk jStar) (forger pk)
      (⟨[], [], 0, none⟩, yStar)).map
      (fun (out, (st, _)) => (out, (st.cache, st.signed, st.hCount))) =
    ProbComp.eval (((forger pk).runState
      (detPSOneSimHandler sys pk jStar yStar)).run ([], [], 0)) := by
  rw [ProbOracleComp.eval_runState]
  refine ProbOracleComp.runWith_map_state_of_invariant
    (detOneEmbedHandler sys pk jStar)
    (fun q s => ProbComp.eval (detPSOneSimHandler sys pk jStar yStar q s))
    (fun (st, _) => (st.cache, st.signed, st.hCount))
    (fun (_, yS) => yS = yStar)
    (detOneEmbedHandler_yStar_step sys pk jStar yStar) ?_ (forger pk)
    (⟨[], [], 0, none⟩, yStar) rfl
  rintro q ⟨st, yS⟩ hyS
  subst hyS
  cases q with
  | inl m =>
    dsimp only [detOneEmbedHandler, detPSOneSimHandler]
    cases st.cache.lookup m with
    | some yxk =>
      rcases yxk with ⟨y, xOpt, idxOpt⟩
      cases xOpt <;> simp [ProbComp.eval_pure, PMF.pure_map]
    | none =>
      simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.map_comp, Function.comp_def]
      exact (PMF.bind_pure_comp _ _).symm
  | inr m =>
    dsimp only [detOneEmbedHandler, detPSOneSimHandler]
    cases st.cache.lookup m with
    | some yxk => simp [ProbComp.eval_pure, PMF.pure_map]
    | none =>
      by_cases heq : st.hCount = jStar
      · simp [heq, ProbComp.eval_pure, PMF.pure_map]
      · simp only [heq, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure, PMF.map_comp,
          Function.comp_def]
        exact (PMF.bind_pure_comp _ _).symm

private noncomputable def detHitCheck {Target Preimage : Type}
    [Fintype Target] [Nonempty Target]
    (check : Target → Option Preimage → Bool) (sigStar : Option Preimage) (fresh : Bool)
    {q_H : ℕ} (hCount : ℕ) (jStar : Fin (q_H + 1))
    (hit : Option (Target × Option ℕ)) : PMF Bool :=
  match hit with
  | some (y, idxOpt) =>
    PMF.pure ((check y sigStar && fresh) &&
      decide (Fin.ofNat (q_H + 1) (idxOpt.getD hCount) = jStar))
  | none =>
    (PMF.uniformOfFintype Target).map fun y =>
      (check y sigStar && fresh) &&
        decide (Fin.ofNat (q_H + 1) hCount = jStar)

private noncomputable def detStateHitCheck {M Target Preimage Payload : Type} [DecidableEq M]
    [Fintype Target] [Nonempty Target]
    (check : Target → Option Preimage → Bool) (q_H : ℕ) (jStar : Fin (q_H + 1))
    (mStar : M) (sigStar : Option Preimage)
    (cache : List (M × (Target × Payload × Option ℕ)))
    (signed : List M) (hCount : ℕ) : PMF Bool :=
  detHitCheck check sigStar (!signed.contains mStar) hCount jStar
    ((cache.lookup mStar).map fun (y, _, idxOpt) => (y, idxOpt))

private theorem eval_detPSOneDistinguisher [DecidableEq M] [DecidableEq Target]
    [Fintype Target] [Nonempty Target]
    (sys : TrapdoorPreimageSystem PK SK Target Preimage) (q_H : ℕ)
    (forger : PK → ProbOracleComp
      (ROMSignature.ForgerSpec M M (Option Preimage) Target) (M × Option Preimage))
    (pk : PK) (pairComp : ProbComp (Target × Option Preimage)) :
    ProbComp.eval ((detPSOneDistinguisher sys q_H forger pk).run fun _ => pairComp) =
    (PMF.uniformOfFintype (Fin (q_H + 1))).bind fun jStar =>
      ((ProbComp.eval pairComp).map Prod.fst).bind fun yStar =>
        (ProbComp.eval (((forger pk).runState
          (detPSOneSimHandler sys pk jStar.val yStar)).run ([], [], 0))).bind
          fun ((mStar, sigStar), (cache, signed, hCount)) =>
            detStateHitCheck (sys.check pk) q_H jStar mStar sigStar cache signed hCount := by
  unfold detPSOneDistinguisher
  simp only [ProbOracleComp.run_bind, ProbOracleComp.run_query, ProbOracleComp.run_sample,
    ProbComp.eval_bind, ProbComp.eval_uniform, PMF.bind_map]
  rw [PMF.bind_comm]
  refine PMF.bind_congr_on_support _ _ _ fun jStar _ => ?_
  refine PMF.bind_congr_on_support _ _ _ fun yxStar _ => ?_
  refine PMF.bind_congr_on_support _ _ _ fun
      ⟨⟨mStar, sigStar⟩, cache, signed, hCount⟩ _ => ?_
  dsimp only [detStateHitCheck, detHitCheck]
  cases cache.lookup mStar with
  | some yxk => simp [ProbOracleComp.run_pure, ProbComp.eval_pure]
  | none =>
    simp only [ProbOracleComp.run_bind, ProbOracleComp.run_sample, ProbOracleComp.run_pure,
      ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure]
    exact (PMF.bind_pure_comp _ _).symm

/-- Hop 2→3 for `detScheme`: Bellare–Rogaway guessing over `Fin (q_H + 1)` fresh direct-hash
indices + zero-loss abort on `Sign(m_{jStar})` bounds `G2` (`psExperimentSim` on
`detPSDistinguisher`) by `(q_H + 1)` times `psExperimentSim` on 1-query `detPSOneDistinguisher`. -/
private theorem detSim_le_mul_detPSOneSim [DecidableEq M] [DecidableEq Target]
    [Fintype Target] [Nonempty Target]
    (sys : TrapdoorPreimageSystem PK SK Target Preimage)
    (forger : PK → ProbOracleComp
      (ROMSignature.ForgerSpec M M (Option Preimage) Target) (M × Option Preimage))
    {q_S q_H : ℕ} (hforger : ProbForgerCallBounded forger q_S q_H) :
    (ProbComp.eval (psExperimentSim sys (detPSDistinguisher sys forger))) true ≤
      ((q_H + 1 : ℕ) : ℝ≥0∞) *
        (ProbComp.eval (psExperimentSim sys (detPSOneDistinguisher sys q_H forger))) true := by
  unfold psExperimentSim
  rw [ProbComp.eval_bind, ProbComp.eval_bind, PMF.bind_apply, PMF.bind_apply,
    ← ENNReal.tsum_mul_left]
  refine tsum_le_tsum fun ⟨pk, sk⟩ => ?_
  rw [← mul_assoc, mul_comm ((q_H + 1 : ℕ) : ℝ≥0∞), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  -- Express `psExperimentSim` on `detPSDistinguisher` via `detTrackHandler` at `jStar = 0`.
  let trackProj (jStar : Fin (q_H + 1)) : PMF (Bool × Fin (q_H + 1)) :=
    (ProbOracleComp.runWith (detTrackHandler sys pk jStar.val) (forger pk)
      ⟨[], [], 0, false⟩).bind fun ((mStar, sigStar), st) =>
        match st.cache.lookup mStar with
        | some (y, _, idxOpt) =>
          PMF.pure (sys.check pk y sigStar && !st.signed.contains mStar,
            Fin.ofNat (q_H + 1) (idxOpt.getD st.hCount))
        | none =>
          (PMF.uniformOfFintype Target).map fun y =>
            (sys.check pk y sigStar && !st.signed.contains mStar,
              Fin.ofNat (q_H + 1) st.hCount)
  have htrack_indep (jStar : Fin (q_H + 1)) :
      (ProbOracleComp.runWith (detTrackHandler sys pk jStar.val) (forger pk)
        ⟨[], [], 0, false⟩).map (fun (out, st) => (out, (st.cache, st.signed, st.hCount))) =
      (ProbOracleComp.runWith (detTrackHandler sys pk 0) (forger pk)
        ⟨[], [], 0, false⟩).map (fun (out, st) => (out, (st.cache, st.signed, st.hCount))) := by
    have hmap (j : ℕ) :
        (ProbOracleComp.runWith (detTrackHandler sys pk j) (forger pk)
          ⟨[], [], 0, false⟩).map (fun (out, st) => (out, (st.cache, st.signed, st.hCount))) =
        ProbOracleComp.runWith
          (fun q ((cache, signed, hCount) :
              List (M × (Target × Option Preimage × Option ℕ)) × List M × ℕ) =>
            match q with
            | .inl m =>
              match cache.lookup m with
              | some (_, x, _) => PMF.pure (x, (cache, m :: signed, hCount))
              | none =>
                (ProbComp.eval (sys.sampleSimPair pk)).map fun yx =>
                  (yx.2, ((m, (yx.1, yx.2, none)) :: cache, m :: signed, hCount))
            | .inr m =>
              match cache.lookup m with
              | some (y, _, _) => PMF.pure (y, (cache, signed, hCount))
              | none =>
                (ProbComp.eval (sys.sampleSimPair pk)).map fun yx =>
                  (yx.1, ((m, (yx.1, yx.2, some hCount)) :: cache, signed, hCount + 1)))
          (forger pk) ([], [], 0) := by
      refine ProbOracleComp.runWith_map_state _ _
        (fun (st : DetTrackState M Target Preimage) => (st.cache, st.signed, st.hCount))
        ?_ (forger pk) ⟨[], [], 0, false⟩
      intro q st
      cases q with
      | inl m =>
        dsimp only [detTrackHandler]
        cases st.cache.lookup m <;> simp [PMF.pure_map, PMF.map_comp, Function.comp_def]
      | inr m =>
        dsimp only [detTrackHandler]
        cases st.cache.lookup m <;> simp [PMF.pure_map, PMF.map_comp, Function.comp_def]
    rw [hmap jStar.val, hmap 0]
  have htrack_eq (jStar : Fin (q_H + 1)) : trackProj jStar = trackProj 0 := by
    dsimp only [trackProj]
    have h1 (j : Fin (q_H + 1)) :
        (ProbOracleComp.runWith (detTrackHandler sys pk j.val) (forger pk)
          ⟨[], [], 0, false⟩).bind (fun ((mStar, sigStar), st) =>
            match st.cache.lookup mStar with
            | some (y, _, idxOpt) =>
              PMF.pure (sys.check pk y sigStar && !st.signed.contains mStar,
                Fin.ofNat (q_H + 1) (idxOpt.getD st.hCount))
            | none =>
              (PMF.uniformOfFintype Target).map fun y =>
                (sys.check pk y sigStar && !st.signed.contains mStar,
                  Fin.ofNat (q_H + 1) st.hCount)) =
        ((ProbOracleComp.runWith (detTrackHandler sys pk j.val) (forger pk)
          ⟨[], [], 0, false⟩).map (fun (out, st) => (out, (st.cache, st.signed, st.hCount)))).bind
          fun ((mStar, sigStar), (cache, signed, hCount)) =>
            match cache.lookup mStar with
            | some (y, _, idxOpt) =>
              PMF.pure (sys.check pk y sigStar && !signed.contains mStar,
                Fin.ofNat (q_H + 1) (idxOpt.getD hCount))
            | none =>
              (PMF.uniformOfFintype Target).map fun y =>
                (sys.check pk y sigStar && !signed.contains mStar,
                  Fin.ofNat (q_H + 1) hCount) := by
      rw [PMF.bind_map]
      rfl
    rw [h1 jStar, h1 0, htrack_indep jStar]
    rfl
  have hps_eq :
      ProbComp.eval ((detPSDistinguisher sys forger pk).run fun _ => sys.sampleSimPair pk) =
      (trackProj 0).map Prod.fst := by
    have hproj :
        (ProbOracleComp.runWith (detTrackHandler sys pk 0) (forger pk)
          ⟨[], [], 0, false⟩).map
            (fun (out, st) => (out, (st.cache.map fun (m, y, x, _) => (m, (y, x)), st.signed))) =
        ProbComp.eval (((OracleComp.interpret
          (OracleComp.sumHandler
            (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
            (detPSHandler (M := M) (Target := Target) (Preimage := Preimage)))
          (forger pk)).run ([], [])).run fun _ => sys.sampleSimPair pk) := by
      rw [eval_run_run_interpret]
      refine ProbOracleComp.runWith_map_state _ _
        (fun (st : DetTrackState M Target Preimage) =>
          (st.cache.map fun (m, y, x, _) => (m, (y, x)), st.signed))
        ?_ (forger pk) ⟨[], [], 0, false⟩
      intro q st
      cases q with
      | inl m =>
        dsimp only [detTrackHandler, detPSHandler]
        rw [lookup_map_det_strip]
        cases st.cache.lookup m with
        | some yxk => simp [ProbOracleComp.run_pure, ProbComp.eval_pure, PMF.pure_map]
        | none =>
          simp only [Option.map_none, ProbOracleComp.run_bind, ProbOracleComp.run_query,
            ProbOracleComp.run_pure, ProbComp.eval_bind, ProbComp.eval_pure, PMF.map_comp,
            Function.comp_def]
          exact (PMF.bind_pure_comp _ _).symm
      | inr m =>
        dsimp only [detTrackHandler, detPSHandler]
        rw [lookup_map_det_strip]
        cases st.cache.lookup m with
        | some yxk => simp [ProbOracleComp.run_pure, ProbComp.eval_pure, PMF.pure_map]
        | none =>
          simp only [Option.map_none, ProbOracleComp.run_bind, ProbOracleComp.run_query,
            ProbOracleComp.run_pure, ProbComp.eval_bind, ProbComp.eval_pure, PMF.map_comp,
            Function.comp_def]
          exact (PMF.bind_pure_comp _ _).symm
    simp only [detPSDistinguisher, ProbOracleComp.run_bind, ProbComp.eval_bind, ← hproj,
      PMF.bind_map, trackProj, PMF.map_bind]
    refine PMF.bind_congr_on_support _ _ _ fun ⟨⟨mStar, sigStar⟩, st⟩ _ => ?_
    dsimp only [Function.comp_def]
    rw [lookup_map_det_strip]
    cases st.cache.lookup mStar with
    | some yxk => simp [ProbOracleComp.run_pure, ProbComp.eval_pure]
    | none =>
      simp only [Option.map_none, ProbOracleComp.run_bind, ProbOracleComp.run_sample,
        ProbOracleComp.run_pure, ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure,
        PMF.map_comp, Function.comp_def]
      exact (PMF.bind_pure_comp _ _).symm
  rw [hps_eq, uniform_fin_guess_mul (trackProj 0)]
  -- Expand RHS `detPSOneDistinguisher` under `sampleSimPair pk`.
  have hrhs_expand :
      (ProbComp.eval ((detPSOneDistinguisher sys q_H forger pk).run
        fun _ => sys.sampleSimPair pk)) true =
      ((PMF.uniformOfFintype (Fin (q_H + 1))).bind fun jStar =>
        ((ProbComp.eval (sys.sampleSimPair pk)).map Prod.fst).bind fun yStar =>
          (ProbComp.eval (((forger pk).runState
            (detPSOneSimHandler sys pk jStar.val yStar)).run ([], [], 0))).bind
            fun ((mStar, sigStar), (cache, signed, hCount)) =>
              detStateHitCheck (sys.check pk) q_H jStar mStar sigStar
                cache signed hCount) true := by
    rw [eval_detPSOneDistinguisher]
  rw [hrhs_expand]
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  rw [PMF.bind_apply, PMF.bind_apply]
  refine tsum_le_tsum fun jStar => ?_
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  rw [← htrack_eq jStar]
  -- Bound `hCount ≤ q_H` + `DetTrackInv` on `detTrackHandler`.
  have hbound_track : ∀ out (st : DetTrackState M Target Preimage),
      (out, st) ∈ (ProbOracleComp.runWith (detTrackHandler sys pk jStar.val) (forger pk)
        ⟨[], [], 0, false⟩).support →
      st.hCount ≤ q_H ∧ DetTrackInv jStar.val st := by
    intro out st hmem
    have h1 := OracleComp.IsCostBounded.measure_le (hforger pk).2
      (oracle := OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n))
        (detTrackHandler sys pk jStar.val))
      (size := fun (s : DetTrackState M Target Preimage) => s.hCount)
      (hstep := by
        intro q s a s' hx
        cases q with
        | inl n =>
          change (a, s') ∈ ((ProbComp.unifOracle n).map (·, s)).support at hx
          obtain ⟨_, -, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
          rw [Prod.mk.injEq] at heq; obtain ⟨-, rfl⟩ := heq; simp
        | inr q =>
          cases q with
          | inl m =>
            dsimp only [OracleComp.sumHandler, detTrackHandler, Sum.elim_inr,
              ROMSignature.hashCost] at hx ⊢
            cases hlu : s.cache.lookup m with
            | some yxk =>
              rw [hlu, PMF.mem_support_pure_iff, Prod.mk.injEq] at hx
              obtain ⟨-, rfl⟩ := hx; simp
            | none =>
              rw [hlu, PMF.mem_support_map_iff] at hx
              obtain ⟨_, -, heq⟩ := hx
              rw [Prod.mk.injEq] at heq; obtain ⟨-, rfl⟩ := heq; simp
          | inr m =>
            dsimp only [OracleComp.sumHandler, detTrackHandler, Sum.elim_inr,
              ROMSignature.hashCost] at hx ⊢
            cases hlu : s.cache.lookup m with
            | some yxk =>
              rw [hlu, PMF.mem_support_pure_iff, Prod.mk.injEq] at hx
              obtain ⟨-, rfl⟩ := hx; omega
            | none =>
              rw [hlu, PMF.mem_support_map_iff] at hx
              obtain ⟨_, -, heq⟩ := hx
              rw [Prod.mk.injEq] at heq; obtain ⟨-, rfl⟩ := heq; dsimp only; omega)
      (s := ⟨[], [], 0, false⟩) (result := out) (s' := st)
      (hmem := by rwa [← ProbOracleComp.runWith_eq_run_interpret])
    have h2 := ProbOracleComp.runWith_invariant (detTrackHandler sys pk jStar.val)
      (DetTrackInv jStar.val) (detTrackInv_step sys pk jStar.val)
      (forger pk) ⟨[], [], 0, false⟩ (detTrackInv_init jStar.val) out st hmem
    exact ⟨by simpa using h1, h2⟩
  -- Step 2a: Zero-loss switch from `detTrackHandler` to `detAbortHandler` via `IdenticalUntilBad`.
  let winCheck : (M × Option Preimage) × DetTrackState M Target Preimage → PMF Bool :=
    fun ((mStar, sigStar), st) =>
      detStateHitCheck (sys.check pk) q_H jStar mStar sigStar st.cache st.signed st.hCount
  have htrack_eq_win :
      ((trackProj jStar).map fun p => p.1 && decide (p.2 = jStar)) true =
      ((ProbOracleComp.runWith (detTrackHandler sys pk jStar.val) (forger pk)
        ⟨[], [], 0, false⟩).bind winCheck) true := by
    dsimp only [trackProj, winCheck, detStateHitCheck, detHitCheck]
    rw [PMF.map_bind]
    congr 1
    refine PMF.bind_congr_on_support _ _ _ fun ⟨⟨mStar, sigStar⟩, st⟩ _ => ?_
    cases st.cache.lookup mStar <;> simp [PMF.pure_map, PMF.map_comp, Function.comp_def]
  rw [htrack_eq_win]
  have habort_le :
      ((ProbOracleComp.runWith (detTrackHandler sys pk jStar.val) (forger pk)
        ⟨[], [], 0, false⟩).bind winCheck) true ≤
      ((ProbOracleComp.runWith (detAbortHandler sys pk jStar.val) (forger pk)
        ⟨[], [], 0, false⟩).bind winCheck) true := by
    rw [PMF.bind_apply, PMF.bind_apply]
    refine tsum_le_tsum fun ⟨⟨mStar, sigStar⟩, st⟩ => ?_
    by_cases hmem : ((mStar, sigStar), st) ∈
        (ProbOracleComp.runWith (detTrackHandler sys pk jStar.val) (forger pk)
          ⟨[], [], 0, false⟩).support
    · by_cases hbad : st.badSignJ = true
      · -- Whenever `st.badSignJ = true`, `winCheck ((mStar, sigStar), st) true = 0`!
        obtain ⟨hcount_le, hsign, hlt, _, hbad_inv⟩ := hbound_track (mStar, sigStar) st hmem
        obtain ⟨hgt, hs_j⟩ := hbad_inv hbad
        have hzero : winCheck ((mStar, sigStar), st) true = 0 := by
          dsimp only [winCheck, detStateHitCheck, detHitCheck, Option.map]
          cases hlu : st.cache.lookup mStar with
          | some yxk =>
            rcases yxk with ⟨y, x, idxOpt⟩
            dsimp only
            have hpmem := mem_of_lookup_eq_some hlu
            have hfalse : ((sys.check pk y sigStar && !st.signed.contains mStar) &&
                decide (Fin.ofNat (q_H + 1) (idxOpt.getD st.hCount) = jStar)) = false := by
              rw [Bool.eq_false_iff]
              intro hwin
              simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
                decide_eq_false_iff_not, decide_eq_true_eq] at hwin
              obtain ⟨⟨_, hnot_s⟩, hidx_eq⟩ := hwin
              cases idxOpt with
              | none => exact hnot_s (hsign mStar y x hpmem)
              | some k =>
                have hk_lt : k < q_H + 1 := Nat.lt_succ_of_le
                  ((hlt mStar y x k hpmem).le.trans hcount_le)
                have hk_eq : k = jStar.val := by
                  have := congrArg Fin.val hidx_eq
                  simpa [Fin.val_ofNat, Nat.mod_eq_of_lt hk_lt] using this
                subst hk_eq
                exact hnot_s (hs_j mStar y x hpmem)
            rw [hfalse]
            simp
          | none =>
            dsimp only
            have hne : Fin.ofNat (q_H + 1) st.hCount ≠ jStar := by
              intro hidx_eq
              have hcnt_eq : st.hCount = jStar.val := by
                have := congrArg Fin.val hidx_eq
                simpa [Fin.val_ofNat, Nat.mod_eq_of_lt (Nat.lt_succ_of_le hcount_le)] using this
              omega
            simp only [decide_eq_false hne, Bool.and_false, PMF.map_apply, Bool.true_eq_false,
              ↓reduceIte, tsum_zero]
        rw [hzero, mul_zero]
        exact zero_le
      · have heq := (detTrack_identicalUntilBad_detAbort sys pk jStar.val).run_apply (forger pk)
          ⟨[], [], 0, false⟩ (mStar, sigStar) st hbad
        rw [heq]
    · have h0 : (ProbOracleComp.runWith (detTrackHandler sys pk jStar.val) (forger pk)
          ⟨[], [], 0, false⟩) ((mStar, sigStar), st) = 0 :=
        (PMF.apply_eq_zero_iff _ _).mpr hmem
      rw [h0, zero_mul]
      exact zero_le
  refine habort_le.trans (le_of_eq ?_)
  -- Step 2b: Project `detAbortHandler` to `detOneTrackHandler` with `μSim = sampleSimPair.map fst`,
  -- then apply `detOneTrack_sim_detOneEmbed` and project to `detPSOneSimHandler`.
  let μSim : PMF Target := (ProbComp.eval (sys.sampleSimPair pk)).map Prod.fst
  have habort_to_one :
      (ProbOracleComp.runWith (detAbortHandler sys pk jStar.val) (forger pk)
        ⟨[], [], 0, false⟩).map (fun (out, st) =>
          (out, (st.cache.map fun (m, y, x, idxOpt) =>
            (m, (y, if idxOpt = some jStar.val then none else some x, idxOpt)),
            st.signed, st.hCount))) =
      (ProbOracleComp.runWith (detOneTrackHandler sys pk jStar.val μSim) (forger pk)
        ⟨[], [], 0, none⟩).map (fun (out, st) => (out, (st.cache, st.signed, st.hCount))) := by
    let erase (st : DetTrackState M Target Preimage) :
        List (M × (Target × Option (Option Preimage) × Option ℕ)) × List M × ℕ :=
      (st.cache.map fun (m, y, x, idxOpt) =>
        (m, (y, if idxOpt = some jStar.val then none else some x, idxOpt)),
        st.signed, st.hCount)
    let midHandler : (q : M ⊕ M) →
        StateT (List (M × (Target × Option (Option Preimage) × Option ℕ)) × List M × ℕ) PMF
          (ROMSignature.ForgerSpec M M (Option Preimage) Target q) :=
      fun q (cache, signed, hCount) =>
        match q with
        | .inl m =>
          match cache.lookup m with
          | some (_, some x, _) => PMF.pure (x, (cache, m :: signed, hCount))
          | some (_, none, _) => PMF.pure (none, (cache, m :: signed, hCount))
          | none =>
            (ProbComp.eval (sys.sampleSimPair pk)).map fun yx =>
              (yx.2, ((m, (yx.1, some yx.2, none)) :: cache, m :: signed, hCount))
        | .inr m =>
          match cache.lookup m with
          | some (y, _, _) => PMF.pure (y, (cache, signed, hCount))
          | none =>
            if hCount = jStar.val then
              μSim.map fun y =>
                (y, ((m, (y, none, some hCount)) :: cache, signed, hCount + 1))
            else
              (ProbComp.eval (sys.sampleSimPair pk)).map fun yx =>
                (yx.1, ((m, (yx.1, some yx.2, some hCount)) :: cache, signed, hCount + 1))
    have hL_mid :
        (ProbOracleComp.runWith (detAbortHandler sys pk jStar.val) (forger pk)
          ⟨[], [], 0, false⟩).map (fun (out, st) => (out, erase st)) =
        ProbOracleComp.runWith midHandler (forger pk) ([], [], 0) := by
      refine ProbOracleComp.runWith_map_state _ _ erase ?_ (forger pk) ⟨[], [], 0, false⟩
      intro q st
      cases q with
      | inl m =>
        dsimp only [detAbortHandler, midHandler, erase]
        rw [lookup_map_det_erase]
        cases st.cache.lookup m with
        | some yxk =>
          rcases yxk with ⟨y, x, idxOpt⟩
          by_cases hidx : idxOpt = some jStar.val <;> simp [hidx, PMF.pure_map]
        | none =>
          simp [PMF.map_comp, Function.comp_def]
      | inr m =>
        dsimp only [detAbortHandler, midHandler, erase]
        rw [lookup_map_det_erase]
        cases st.cache.lookup m with
        | some yxk => simp [PMF.pure_map]
        | none =>
          by_cases hcnt : st.hCount = jStar.val
          · simp [hcnt, μSim, PMF.map_comp, Function.comp_def]
          · simp [hcnt, PMF.map_comp, Function.comp_def]
    have hR_mid :
        (ProbOracleComp.runWith (detOneTrackHandler sys pk jStar.val μSim) (forger pk)
          ⟨[], [], 0, none⟩).map (fun (out, st) => (out, (st.cache, st.signed, st.hCount))) =
        ProbOracleComp.runWith midHandler (forger pk) ([], [], 0) := by
      refine ProbOracleComp.runWith_map_state _ _
        (fun (st : DetOneState M Target Preimage) => (st.cache, st.signed, st.hCount))
        ?_ (forger pk) ⟨[], [], 0, none⟩
      intro q st
      cases q with
      | inl m =>
        dsimp only [detOneTrackHandler, midHandler]
        cases st.cache.lookup m with
        | some yxk =>
          rcases yxk with ⟨y, xOpt, idxOpt⟩
          cases xOpt <;> simp [PMF.pure_map]
        | none => simp [PMF.map_comp, Function.comp_def]
      | inr m =>
        dsimp only [detOneTrackHandler, midHandler]
        cases st.cache.lookup m with
        | some yxk => simp [PMF.pure_map]
        | none =>
          by_cases hcnt : st.hCount = jStar.val <;> simp [hcnt, PMF.map_comp, Function.comp_def]
    exact hL_mid.trans hR_mid.symm
  have hone_to_psOne :
      (ProbOracleComp.runWith (detOneTrackHandler sys pk jStar.val μSim) (forger pk)
        ⟨[], [], 0, none⟩).map (fun (out, st) => (out, (st.cache, st.signed, st.hCount))) =
      μSim.bind fun yStar =>
        ProbComp.eval (((forger pk).runState
          (detPSOneSimHandler sys pk jStar.val yStar)).run ([], [], 0)) := by
    have hsim := congrArg (PMF.map fun (out, (st, _)) => (out, (st.cache, st.signed, st.hCount)))
      (detOneTrack_sim_detOneEmbed sys pk jStar.val μSim forger)
    rw [detOneRelate_proj_state, PMF.map_bind] at hsim
    rw [hsim]
    refine PMF.bind_congr_on_support _ _ _ fun yStar _ => ?_
    exact detOneEmbed_map_eq_detPSOneSim sys pk jStar.val yStar forger
  let postOne : (M × Option Preimage) ×
      (List (M × (Target × Option (Option Preimage) × Option ℕ)) × List M × ℕ) → PMF Bool :=
    fun ((mStar, sigStar), (cache, signed, hCount)) =>
      detStateHitCheck (sys.check pk) q_H jStar mStar sigStar cache signed hCount
  have hL_post :
      (ProbOracleComp.runWith (detAbortHandler sys pk jStar.val) (forger pk)
        ⟨[], [], 0, false⟩).bind winCheck =
      ((ProbOracleComp.runWith (detAbortHandler sys pk jStar.val) (forger pk)
        ⟨[], [], 0, false⟩).map (fun (out, st) =>
          (out, (st.cache.map fun (m, y, x, idxOpt) =>
            (m, (y, if idxOpt = some jStar.val then none else some x, idxOpt)),
            st.signed, st.hCount)))).bind postOne := by
    rw [PMF.bind_map]
    refine PMF.bind_congr_on_support _ _ _ fun ⟨⟨mStar, sigStar⟩, st⟩ _ => ?_
    dsimp only [winCheck, postOne, detStateHitCheck, Function.comp_def]
    rw [lookup_map_det_erase]
    cases st.cache.lookup mStar <;> rfl
  rw [hL_post, habort_to_one, hone_to_psOne, PMF.bind_bind]

/-- Hop 3→4 for `detScheme`: `psExperimentReal` on 1-query `detPSOneDistinguisher` is bounded by
`Signature.targetExperiment` on `detInverter`. -/
private theorem detPSOneReal_le_targetExperiment [DecidableEq M] [DecidableEq Target]
    [Fintype Target] [Nonempty Target]
    (sys : TrapdoorPreimageSystem PK SK Target Preimage)
    (forger : PK → ProbOracleComp
      (ROMSignature.ForgerSpec M M (Option Preimage) Target) (M × Option Preimage))
    {q_S q_H : ℕ} (hforger : ProbForgerCallBounded forger q_S q_H) :
    (ProbComp.eval (psExperimentReal sys (detPSOneDistinguisher sys q_H forger))) true ≤
      (ProbComp.eval (Signature.targetExperiment sys.toRawScheme
        (fun _ => ProbComp.uniform Target) (detInverter sys q_H forger))) true := by
  unfold psExperimentReal Signature.targetExperiment
  dsimp only [TrapdoorPreimageSystem.toRawScheme]
  rw [ProbComp.eval_bind, ProbComp.eval_bind, PMF.bind_apply, PMF.bind_apply]
  refine tsum_le_tsum fun ⟨pk, sk⟩ => ?_
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  -- Rewrite LHS using `eval_sampleRealPair_map_fst` so `yStar ~ uniformOfFintype Target`.
  have hlhs_eq :
      (ProbComp.eval ((detPSOneDistinguisher sys q_H forger pk).run
        fun _ => sys.sampleRealPair sk)) =
      (PMF.uniformOfFintype (Fin (q_H + 1))).bind fun jStar =>
        (PMF.uniformOfFintype Target).bind fun yStar =>
          (ProbComp.eval (((forger pk).runState
            (detPSOneSimHandler sys pk jStar.val yStar)).run ([], [], 0))).bind
            fun ((mStar, sigStar), (cache, signed, hCount)) =>
              detStateHitCheck (sys.check pk) q_H jStar mStar sigStar
                cache signed hCount := by
    rw [eval_detPSOneDistinguisher, sys.eval_sampleRealPair_map_fst sk]
  have hrhs_eq :
      ProbComp.eval (do
        let target ← ProbComp.uniform Target
        let sig ← detInverter sys q_H forger pk target
        pure (sys.check pk target sig)) =
      (PMF.uniformOfFintype (Fin (q_H + 1))).bind fun jStar =>
        (PMF.uniformOfFintype Target).bind fun yStar =>
          (ProbComp.eval (((forger pk).runState
            (detInvHandler sys pk jStar.val yStar)).run ([], 0))).map
            fun ((_, sigStar), _) => sys.check pk yStar sigStar := by
    unfold detInverter
    simp only [ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure, PMF.bind_bind,
      PMF.pure_bind]
    rw [PMF.bind_comm]
    refine PMF.bind_congr_on_support _ _ _ fun jStar _ => ?_
    refine PMF.bind_congr_on_support _ _ _ fun yStar _ => ?_
    exact (PMF.bind_pure_comp _ _).symm
  rw [hlhs_eq, hrhs_eq, PMF.bind_apply, PMF.bind_apply]
  refine tsum_le_tsum fun jStar => ?_
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  -- Relate `detPSOneSimHandler` and `detInvHandler` both to `detOneEmbedHandler`!
  have hpsOne_from_embed (yStar : Target) :
      (ProbOracleComp.runWith (detOneEmbedHandler sys pk jStar.val) (forger pk)
        (⟨[], [], 0, none⟩, yStar)).map
        (fun (out, (st, _)) => (out, (st.cache, st.signed, st.hCount))) =
      ProbComp.eval (((forger pk).runState
        (detPSOneSimHandler sys pk jStar.val yStar)).run ([], [], 0)) :=
    detOneEmbed_map_eq_detPSOneSim sys pk jStar.val yStar forger
  have hinv_from_embed (yStar : Target) :
      (ProbOracleComp.runWith (detOneEmbedHandler sys pk jStar.val) (forger pk)
        (⟨[], [], 0, none⟩, yStar)).map (fun ((_, sigStar), _) => sigStar) =
      (ProbComp.eval (((forger pk).runState
        (detInvHandler sys pk jStar.val yStar)).run ([], 0))).map
        (fun ((_, sigStar), _) => sigStar) := by
    rw [ProbOracleComp.eval_runState]
    have hproj := ProbOracleComp.runWith_map_state_of_invariant
      (detOneEmbedHandler sys pk jStar.val)
      (fun q s => ProbComp.eval (detInvHandler sys pk jStar.val yStar q s))
      (fun (st, _) => (st.cache.map fun (m, y, xOpt, _) => (m, (y, xOpt)), st.hCount))
      (fun (_, yS) => yS = yStar)
      (detOneEmbedHandler_yStar_step sys pk jStar.val yStar) ?_ (forger pk)
      (⟨[], [], 0, none⟩, yStar) rfl
    · have hcongr := congrArg (PMF.map fun ((_, sigStar), _) => sigStar) hproj
      simpa only [PMF.map_comp, Function.comp_def, List.map_nil] using hcongr
    · rintro q ⟨st, yS⟩ hyS
      subst hyS
      cases q with
      | inl m =>
        dsimp only [detOneEmbedHandler, detInvHandler]
        rw [lookup_map_det_strip]
        cases st.cache.lookup m with
        | some yxk =>
          rcases yxk with ⟨y, xOpt, idxOpt⟩
          cases xOpt <;> simp [ProbComp.eval_pure, PMF.pure_map]
        | none =>
          simp only [Option.map_none, ProbComp.eval_bind, ProbComp.eval_pure, PMF.map_comp,
            Function.comp_def]
          exact (PMF.bind_pure_comp _ _).symm
      | inr m =>
        dsimp only [detOneEmbedHandler, detInvHandler]
        rw [lookup_map_det_strip]
        cases st.cache.lookup m with
        | some yxk => simp [ProbComp.eval_pure, PMF.pure_map]
        | none =>
          by_cases heq : st.hCount = jStar.val
          · simp [Option.map_none, heq, ProbComp.eval_pure, PMF.pure_map]
          · simp only [Option.map_none, heq, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
              PMF.map_comp, Function.comp_def]
            exact (PMF.bind_pure_comp _ _).symm
  -- Rewrite both sides through `detOneTrack_sim_detOneEmbed` with uniform `μStar`.
  have hsim := detOneTrack_sim_detOneEmbed sys pk jStar.val (PMF.uniformOfFintype Target) forger
  have hlhs_track :
      ((PMF.uniformOfFintype Target).bind fun yStar =>
        (ProbComp.eval (((forger pk).runState
          (detPSOneSimHandler sys pk jStar.val yStar)).run ([], [], 0))).bind
          fun ((mStar, sigStar), (cache, signed, hCount)) =>
            detStateHitCheck (sys.check pk) q_H jStar mStar sigStar cache signed hCount) =
      (ProbOracleComp.runWith
        (detOneTrackHandler sys pk jStar.val (PMF.uniformOfFintype Target)) (forger pk)
        ⟨[], [], 0, none⟩).bind fun ((mStar, sigStar), st) =>
          detStateHitCheck (sys.check pk) q_H jStar mStar sigStar
            st.cache st.signed st.hCount := by
    have hdist :
        ((PMF.uniformOfFintype Target).bind fun yStar =>
          ProbComp.eval (((forger pk).runState
            (detPSOneSimHandler sys pk jStar.val yStar)).run ([], [], 0))) =
        (ProbOracleComp.runWith
          (detOneTrackHandler sys pk jStar.val (PMF.uniformOfFintype Target)) (forger pk)
          ⟨[], [], 0, none⟩).map (fun (out, st) => (out, (st.cache, st.signed, st.hCount))) := by
      have hproj :=
        congrArg (PMF.map fun (out, (st, _)) => (out, (st.cache, st.signed, st.hCount))) hsim
      rw [detOneRelate_proj_state, PMF.map_bind] at hproj
      rw [hproj]
      refine PMF.bind_congr_on_support _ _ _ fun yStar _ => ?_
      exact (hpsOne_from_embed yStar).symm
    rw [← PMF.bind_bind, hdist, PMF.bind_map]
    rfl
  have hrhs_track :
      ((PMF.uniformOfFintype Target).bind fun yStar =>
        (ProbComp.eval (((forger pk).runState
          (detInvHandler sys pk jStar.val yStar)).run ([], 0))).map
          fun ((_, sigStar), _) => sys.check pk yStar sigStar) =
      (ProbOracleComp.runWith
        (detOneTrackHandler sys pk jStar.val (PMF.uniformOfFintype Target)) (forger pk)
        ⟨[], [], 0, none⟩).bind fun ((_, sigStar), st) =>
          (detOneRelate (PMF.uniformOfFintype Target) st).map fun (_, yStar) =>
            sys.check pk yStar sigStar := by
    have h1 :
        ((PMF.uniformOfFintype Target).bind fun yStar =>
          (ProbComp.eval (((forger pk).runState
            (detInvHandler sys pk jStar.val yStar)).run ([], 0))).map
            fun ((_, sigStar), _) => sys.check pk yStar sigStar) =
        ((PMF.uniformOfFintype Target).bind fun yStar =>
          ProbOracleComp.runWith (detOneEmbedHandler sys pk jStar.val) (forger pk)
            (⟨[], [], 0, none⟩, yStar)).map
            fun ((_, sigStar), (_, yStar)) => sys.check pk yStar sigStar := by
      rw [PMF.map_bind]
      refine PMF.bind_congr_on_support _ _ _ fun yStar _ => ?_
      have hsub :
          (ProbComp.eval (((forger pk).runState
            (detInvHandler sys pk jStar.val yStar)).run ([], 0))).map
            (fun ((_, sigStar), _) => sys.check pk yStar sigStar) =
          (ProbOracleComp.runWith (detOneEmbedHandler sys pk jStar.val) (forger pk)
            (⟨[], [], 0, none⟩, yStar)).map
            (fun ((_, sigStar), _) => sys.check pk yStar sigStar) := by
        have hc := congrArg (PMF.map (sys.check pk yStar)) (hinv_from_embed yStar).symm
        simpa only [PMF.map_comp, Function.comp_def] using hc
      rw [hsub]
      refine PMF.map_congr_on_support _ _ _ fun ⟨⟨_, sigStar⟩, ⟨st, yS⟩⟩ hmem => ?_
      have hyS : yS = yStar := ProbOracleComp.runWith_invariant
        (detOneEmbedHandler sys pk jStar.val) (fun (_, y) => y = yStar)
        (fun q ⟨st, yS⟩ hyS a ⟨st', yS'⟩ hstep => by
          subst hyS
          cases q with
          | inl m =>
            dsimp only [detOneEmbedHandler] at hstep
            cases hlu : st.cache.lookup m with
            | some yxk =>
              rcases yxk with ⟨y, xOpt, idxOpt⟩
              cases xOpt <;>
                (rw [hlu, PMF.mem_support_pure_iff, Prod.mk.injEq, Prod.mk.injEq] at hstep;
                  obtain ⟨-, -, rfl⟩ := hstep; rfl)
            | none =>
              rw [hlu, PMF.mem_support_map_iff] at hstep
              obtain ⟨_, -, heq⟩ := hstep
              rw [Prod.mk.injEq, Prod.mk.injEq] at heq
              obtain ⟨-, -, rfl⟩ := heq; rfl
          | inr m =>
            dsimp only [detOneEmbedHandler] at hstep
            cases hlu : st.cache.lookup m with
            | some yxk =>
              rw [hlu, PMF.mem_support_pure_iff, Prod.mk.injEq, Prod.mk.injEq] at hstep
              obtain ⟨-, -, rfl⟩ := hstep; rfl
            | none =>
              rw [hlu] at hstep
              split_ifs at hstep with heq
              · rw [PMF.mem_support_pure_iff, Prod.mk.injEq, Prod.mk.injEq] at hstep
                obtain ⟨-, -, rfl⟩ := hstep; rfl
              · rw [PMF.mem_support_map_iff] at hstep
                obtain ⟨_, -, heq2⟩ := hstep
                rw [Prod.mk.injEq, Prod.mk.injEq] at heq2
                obtain ⟨-, -, rfl⟩ := heq2; rfl)
        (forger pk) (⟨[], [], 0, none⟩, yStar) rfl _ _ hmem
      simp [hyS]
    rw [h1, ← hsim, PMF.map_bind]
    refine PMF.bind_congr_on_support _ _ _ fun ⟨⟨_, sigStar⟩, st⟩ _ => ?_
    simp [PMF.map_comp, Function.comp_def]
  rw [hlhs_track, hrhs_track]
  -- Pointwise comparison on `detOneTrackHandler`'s support using `hCount ≤ q_H` and `DetOneInv`.
  have hbound_one : ∀ out (st : DetOneState M Target Preimage),
      (out, st) ∈ (ProbOracleComp.runWith
        (detOneTrackHandler sys pk jStar.val (PMF.uniformOfFintype Target)) (forger pk)
        ⟨[], [], 0, none⟩).support →
      st.hCount ≤ q_H ∧ DetOneInv jStar.val st := by
    intro out st hmem
    have h1 := OracleComp.IsCostBounded.measure_le (hforger pk).2
      (oracle := OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n))
        (detOneTrackHandler sys pk jStar.val (PMF.uniformOfFintype Target)))
      (size := fun (s : DetOneState M Target Preimage) => s.hCount)
      (hstep := by
        intro q s a s' hx
        cases q with
        | inl n =>
          change (a, s') ∈ ((ProbComp.unifOracle n).map (·, s)).support at hx
          obtain ⟨_, -, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
          rw [Prod.mk.injEq] at heq; obtain ⟨-, rfl⟩ := heq; simp
        | inr q =>
          cases q with
          | inl m =>
            dsimp only [OracleComp.sumHandler, detOneTrackHandler, Sum.elim_inr,
              ROMSignature.hashCost] at hx ⊢
            cases hlu : s.cache.lookup m with
            | some yxk =>
              rcases yxk with ⟨y, xOpt, idxOpt⟩
              cases xOpt <;>
                (rw [hlu, PMF.mem_support_pure_iff, Prod.mk.injEq] at hx;
                  obtain ⟨-, rfl⟩ := hx; simp)
            | none =>
              rw [hlu, PMF.mem_support_map_iff] at hx
              obtain ⟨_, -, heq⟩ := hx
              rw [Prod.mk.injEq] at heq; obtain ⟨-, rfl⟩ := heq; simp
          | inr m =>
            dsimp only [OracleComp.sumHandler, detOneTrackHandler, Sum.elim_inr,
              ROMSignature.hashCost] at hx ⊢
            cases hlu : s.cache.lookup m with
            | some yxk =>
              rw [hlu, PMF.mem_support_pure_iff, Prod.mk.injEq] at hx
              obtain ⟨-, rfl⟩ := hx; omega
            | none =>
              rw [hlu] at hx
              split_ifs at hx with heq <;>
                (rw [PMF.mem_support_map_iff] at hx; obtain ⟨_, -, heq2⟩ := hx;
                  rw [Prod.mk.injEq] at heq2; obtain ⟨-, rfl⟩ := heq2; dsimp only; omega))
      (s := ⟨[], [], 0, none⟩) (result := out) (s' := st)
      (hmem := by rwa [← ProbOracleComp.runWith_eq_run_interpret])
    have h2 := ProbOracleComp.runWith_invariant
      (detOneTrackHandler sys pk jStar.val (PMF.uniformOfFintype Target))
      (DetOneInv jStar.val) (detOneInv_step sys pk jStar.val (PMF.uniformOfFintype Target))
      (forger pk) ⟨[], [], 0, none⟩ (detOneInv_init jStar.val) out st hmem
    exact ⟨by simpa using h1, h2⟩
  refine PMF.bind_apply_mono_on_support _ _ fun ⟨⟨mStar, sigStar⟩, st⟩ hmem => ?_
  obtain ⟨hcount_le, hnone, hsign, hlt, hyj⟩ := hbound_one (mStar, sigStar) st hmem
  dsimp only
  let hit : Option (Target × Option ℕ) :=
    (st.cache.lookup mStar).map fun ⟨y, _, idxOpt⟩ => (y, idxOpt)
  have hL :
      (detStateHitCheck (sys.check pk) q_H jStar mStar sigStar
        st.cache st.signed st.hCount) true =
      ((match hit with
        | some (y, idxOpt) =>
            PMF.pure ((sys.check pk y sigStar && !st.signed.contains mStar) &&
              decide (Fin.ofNat (q_H + 1) (idxOpt.getD st.hCount) = jStar))
        | none =>
            (PMF.uniformOfFintype Target).map fun y =>
              (sys.check pk y sigStar && !st.signed.contains mStar) &&
                decide (Fin.ofNat (q_H + 1) st.hCount = jStar)) true) := rfl
  have hR :
      ((detOneRelate (PMF.uniformOfFintype Target) st).map fun (_, yStar) =>
          sys.check pk yStar sigStar) true =
      ((match st.yAtJ with
        | some yStar => PMF.pure (sys.check pk yStar sigStar)
        | none => (PMF.uniformOfFintype Target).map fun yStar => sys.check pk yStar sigStar)
        true) := by
    cases hy : st.yAtJ <;>
      simp [detOneRelate, hy, PMF.pure_map, PMF.map_comp, Function.comp_def]
  rw [hL, hR]
  refine targetHit_le_yAtJ_check sys pk sigStar (!st.signed.contains mStar) st.hCount jStar
    st.yAtJ hit hcount_le hnone
    ?_ ?_ ?_
  · intro y hlu
    rcases Option.map_eq_some_iff.mp hlu with ⟨⟨y', xOpt, idxOpt⟩, hlu', hpair⟩
    cases hpair
    simp [hsign mStar y xOpt (mem_of_lookup_eq_some hlu')]
  · intro y k hlu
    rcases Option.map_eq_some_iff.mp hlu with ⟨⟨y', xOpt, idxOpt⟩, hlu', hpair⟩
    cases hpair
    exact hlt mStar y xOpt k (mem_of_lookup_eq_some hlu')
  · intro y hlu
    rcases Option.map_eq_some_iff.mp hlu with ⟨⟨y', xOpt, idxOpt⟩, hlu', hpair⟩
    cases hpair
    exact hyj mStar y xOpt (mem_of_lookup_eq_some hlu')

/-- **Classical ROM EUF-CMA reduction for deterministic unsalted hash-and-sign
(`ProbOracleComp` form)**, original to this library (adapting the `(q_H + 1)` programming
argument after `[KosugeXagawa2022]` to unsalted `detScheme`): for any probabilistic ROM forger
making at most `q_S` signing queries and `q_H` direct hash queries,
`Pr[EUF-CMA] ≤ (q_H + 1) * (Pr[INV(detInverter)] + Adv^PS(detPSOneDistinguisher)) +`
`Adv^PS(detPSDistinguisher) + (q_S + q_H).choose 2 / |Target|`.
Every reduction is an explicit finite program with proved query bounds (`detPSDistinguisher`
makes at most `q_S + q_H` `PS` queries, `detPSOneDistinguisher` makes at most `1` `PS` query;
no runtime certificate claimed, tracked in #7068). -/
theorem detRomWorldEufCma_succProbability_le [DecidableEq M] [DecidableEq Target]
    [Fintype Target] [Nonempty Target] [Finite Preimage]
    (sys : TrapdoorPreimageSystem PK SK Target Preimage)
    (forger : PK → ProbOracleComp
      (ROMSignature.ForgerSpec M M (Option Preimage) Target) (M × Option Preimage))
    {q_S q_H : ℕ} (hforger : ProbForgerCallBounded forger q_S q_H) :
    Game.succProbability
        (ROMSignature.worldGame (detScheme sys) forger eufCmaAccept) ≤
      (q_H + 1 : ℝ≥0) *
        (Experiment.succProbability
          (Signature.targetExperiment sys.toRawScheme (fun _ => ProbComp.uniform Target)
            (detInverter sys q_H forger)) +
        Experiment.advantage
          (psExperimentReal sys (detPSOneDistinguisher sys q_H forger))
          (psExperimentSim sys (detPSOneDistinguisher sys q_H forger))) +
      Experiment.advantage
        (psExperimentReal sys (detPSDistinguisher sys forger))
        (psExperimentSim sys (detPSDistinguisher sys forger)) +
      ((q_S + q_H).choose 2 : ℝ≥0) * (Fintype.card Target : ℝ≥0)⁻¹ := by
  have h01 := detWorld_le_detPSReal_add_birthday sys forger hforger
  have h23 := detSim_le_mul_detPSOneSim sys forger hforger
  have h34 := detPSOneReal_le_targetExperiment sys forger hforger
  have hcard_ne : (Fintype.card Target : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hcard_top : (Fintype.card Target : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  -- Convert the `ENNReal` bounds to `NNReal`.
  have h01_nn :
      Game.succProbability (ROMSignature.worldGame (detScheme sys) forger eufCmaAccept) ≤
        Experiment.succProbability (psExperimentReal sys (detPSDistinguisher sys forger)) +
          ((q_S + q_H).choose 2 : ℝ≥0) * (Fintype.card Target : ℝ≥0)⁻¹ := by
    rw [← ENNReal.coe_le_coe]
    have hcoe :
        (((Experiment.succProbability (psExperimentReal sys (detPSDistinguisher sys forger)) +
            ((q_S + q_H).choose 2 : ℝ≥0) * (Fintype.card Target : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞)) =
          (ProbComp.eval (psExperimentReal sys (detPSDistinguisher sys forger))) true +
            ((q_S + q_H).choose 2 : ℕ) * (Fintype.card Target : ℝ≥0∞)⁻¹ := by
      simp only [ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_natCast,
        ENNReal.coe_inv (Nat.cast_ne_zero.mpr Fintype.card_ne_zero),
        Experiment.succProbability, Game.succProbability,
        ENNReal.coe_toNNReal (PMF.apply_ne_top _ _)]
    rw [hcoe]
    simpa only [Game.succProbability, ENNReal.coe_toNNReal (PMF.apply_ne_top _ _)] using h01
  have h12_nn :
      Experiment.succProbability (psExperimentReal sys (detPSDistinguisher sys forger)) ≤
        Experiment.succProbability (psExperimentSim sys (detPSDistinguisher sys forger)) +
          Experiment.advantage
            (psExperimentReal sys (detPSDistinguisher sys forger))
            (psExperimentSim sys (detPSDistinguisher sys forger)) := by
    rw [Experiment.advantage]
    have h := le_abs_self
      ((Experiment.succProbability (psExperimentReal sys (detPSDistinguisher sys forger)) : ℝ) -
        (Experiment.succProbability (psExperimentSim sys (detPSDistinguisher sys forger)) : ℝ))
    exact_mod_cast (by linarith :
      (Experiment.succProbability (psExperimentReal sys (detPSDistinguisher sys forger)) : ℝ) ≤
        (Experiment.succProbability (psExperimentSim sys (detPSDistinguisher sys forger)) : ℝ) +
          |(Experiment.succProbability (psExperimentReal sys (detPSDistinguisher sys forger)) : ℝ) -
            (Experiment.succProbability (psExperimentSim sys (detPSDistinguisher sys forger)) : ℝ)|)
  have h23_nn :
      Experiment.succProbability (psExperimentSim sys (detPSDistinguisher sys forger)) ≤
        (q_H + 1 : ℝ≥0) *
          Experiment.succProbability
            (psExperimentSim sys (detPSOneDistinguisher sys q_H forger)) := by
    rw [← ENNReal.coe_le_coe]
    simpa only [ENNReal.coe_mul, ENNReal.coe_add, ENNReal.coe_natCast, ENNReal.coe_one,
      Experiment.succProbability, Game.succProbability, ENNReal.coe_toNNReal (PMF.apply_ne_top _ _),
      Nat.cast_add, Nat.cast_one] using h23
  have h3_adv_nn :
      Experiment.succProbability (psExperimentSim sys (detPSOneDistinguisher sys q_H forger)) ≤
        Experiment.succProbability (psExperimentReal sys (detPSOneDistinguisher sys q_H forger)) +
          Experiment.advantage
            (psExperimentReal sys (detPSOneDistinguisher sys q_H forger))
            (psExperimentSim sys (detPSOneDistinguisher sys q_H forger)) := by
    rw [Experiment.advantage]
    have h := neg_le_abs
      ((Experiment.succProbability
        (psExperimentReal sys (detPSOneDistinguisher sys q_H forger)) : ℝ) -
        (Experiment.succProbability
          (psExperimentSim sys (detPSOneDistinguisher sys q_H forger)) : ℝ))
    exact_mod_cast (by linarith :
      (Experiment.succProbability
          (psExperimentSim sys (detPSOneDistinguisher sys q_H forger)) : ℝ) ≤
        (Experiment.succProbability
          (psExperimentReal sys (detPSOneDistinguisher sys q_H forger)) : ℝ) +
          |(Experiment.succProbability
              (psExperimentReal sys (detPSOneDistinguisher sys q_H forger)) : ℝ) -
            (Experiment.succProbability
              (psExperimentSim sys (detPSOneDistinguisher sys q_H forger)) : ℝ)|)
  have h34_nn :
      Experiment.succProbability (psExperimentReal sys (detPSOneDistinguisher sys q_H forger)) ≤
        Experiment.succProbability
          (Signature.targetExperiment sys.toRawScheme (fun _ => ProbComp.uniform Target)
            (detInverter sys q_H forger)) := by
    rw [← ENNReal.coe_le_coe]
    simpa only [Experiment.succProbability, Game.succProbability,
      ENNReal.coe_toNNReal (PMF.apply_ne_top _ _)] using h34
  have h24_nn :
      Experiment.succProbability (psExperimentSim sys (detPSDistinguisher sys forger)) ≤
        (q_H + 1 : ℝ≥0) *
          (Experiment.succProbability
            (Signature.targetExperiment sys.toRawScheme (fun _ => ProbComp.uniform Target)
              (detInverter sys q_H forger)) +
          Experiment.advantage
            (psExperimentReal sys (detPSOneDistinguisher sys q_H forger))
            (psExperimentSim sys (detPSOneDistinguisher sys q_H forger))) :=
    h23_nn.trans (mul_le_mul_of_nonneg_left (h3_adv_nn.trans (add_le_add h34_nn le_rfl)) zero_le)
  calc
    Game.succProbability (ROMSignature.worldGame (detScheme sys) forger eufCmaAccept)
      ≤ Experiment.succProbability (psExperimentReal sys (detPSDistinguisher sys forger)) +
          ((q_S + q_H).choose 2 : ℝ≥0) * (Fintype.card Target : ℝ≥0)⁻¹ := h01_nn
    _ ≤ (Experiment.succProbability (psExperimentSim sys (detPSDistinguisher sys forger)) +
          Experiment.advantage
            (psExperimentReal sys (detPSDistinguisher sys forger))
            (psExperimentSim sys (detPSDistinguisher sys forger))) +
          ((q_S + q_H).choose 2 : ℝ≥0) * (Fintype.card Target : ℝ≥0)⁻¹ :=
        add_le_add h12_nn le_rfl
    _ ≤ ((q_H + 1 : ℝ≥0) *
          (Experiment.succProbability
            (Signature.targetExperiment sys.toRawScheme (fun _ => ProbComp.uniform Target)
              (detInverter sys q_H forger)) +
          Experiment.advantage
            (psExperimentReal sys (detPSOneDistinguisher sys q_H forger))
            (psExperimentSim sys (detPSOneDistinguisher sys q_H forger))) +
          Experiment.advantage
            (psExperimentReal sys (detPSDistinguisher sys forger))
            (psExperimentSim sys (detPSDistinguisher sys forger))) +
          ((q_S + q_H).choose 2 : ℝ≥0) * (Fintype.card Target : ℝ≥0)⁻¹ :=
        add_le_add (add_le_add h24_nn le_rfl) le_rfl

/-- **Classical ROM EUF-CMA reduction for deterministic unsalted hash-and-sign
(`ROMSignature.eufCmaGame` form)**, original to this library. Applies to `ROMSignature.Forger`
adversaries whose coin distribution `A.coins` is realized by a finite `ProbComp A.Coins` sampler
(`hcoins : A.coins = ProbComp.eval coinSampler`). -/
theorem eufCmaGame_detScheme_succProbability_le [DecidableEq M] [DecidableEq Target]
    [Fintype Target] [Nonempty Target] [Finite Preimage]
    (sys : TrapdoorPreimageSystem PK SK Target Preimage)
    (A : ROMSignature.Forger PK M (Option Preimage) M Target)
    (coinSampler : ProbComp A.Coins) (hcoins : A.coins = ProbComp.eval coinSampler)
    {q_S q_H : ℕ} (hA : A.CallBounded q_S q_H) :
    Game.succProbability (ROMSignature.eufCmaGame (detScheme sys) A) ≤
      (q_H + 1 : ℝ≥0) *
        (Experiment.succProbability
          (Signature.targetExperiment sys.toRawScheme (fun _ => ProbComp.uniform Target)
            (detInverter sys q_H (liftForger A coinSampler))) +
        Experiment.advantage
          (psExperimentReal sys (detPSOneDistinguisher sys q_H (liftForger A coinSampler)))
          (psExperimentSim sys (detPSOneDistinguisher sys q_H (liftForger A coinSampler)))) +
      Experiment.advantage
        (psExperimentReal sys (detPSDistinguisher sys (liftForger A coinSampler)))
        (psExperimentSim sys (detPSDistinguisher sys (liftForger A coinSampler))) +
      ((q_S + q_H).choose 2 : ℝ≥0) * (Fintype.card Target : ℝ≥0)⁻¹ := by
  rw [eufCmaGame_eq_worldGame_liftForger (detScheme sys) A coinSampler hcoins]
  exact detRomWorldEufCma_succProbability_le sys (liftForger A coinSampler)
    (probForgerCallBounded_liftForger coinSampler hA)

end DetReduction

/-! ### Extracted-model VOLE-ACT credit conservation in the lazy ROM -/

section ROMConservation

variable {Nullifier Context Opening Commitment PK SK Sig Query Digest : Type}

/-- An adaptive adversary in the extracted single-issuer VOLE-ACT credit-conservation game in the
lazy random-oracle model: given the issuer's public key `pk`, it queries the extracted issuer
oracle (`Request → Option Sig`) and the random oracle (`Query → Digest`), and outputs the target
context `ctx*` it claims is overspent. -/
abbrev ROMExtractedAdversary
    (Nullifier Context Opening Commitment PK Sig Query Digest : Type) :=
  PK → ProbOracleComp
    ((fun _ : AnonymousToken.Conservation.Request Nullifier Context Opening Commitment Sig =>
      Option Sig) ⊕ₒ (fun _ : Query => Digest))
    Context

/-- Cost function counting issuer requests (`.inl`) of a `ROMExtractedAdversary`. -/
@[expose] def romRequestCost
    {Nullifier Context Opening Commitment Sig Query : Type} :
    AnonymousToken.Conservation.Request Nullifier Context Opening Commitment Sig ⊕ Query → ℕ
  | .inl _ => 1
  | .inr _ => 0

/-- Cost function counting direct random-oracle queries (`.inr`) of a `ROMExtractedAdversary`. -/
@[expose] def romDirectHashCost
    {Nullifier Context Opening Commitment Sig Query : Type} :
    AnonymousToken.Conservation.Request Nullifier Context Opening Commitment Sig ⊕ Query → ℕ
  | .inl _ => 0
  | .inr _ => 1

/-- Separate issuer-request (`q_R`) and direct random-oracle (`q_H`) call budgets for a
`ROMExtractedAdversary`. -/
@[expose] def ROMExtractedCallBounded
    (A : ROMExtractedAdversary Nullifier Context Opening Commitment PK Sig Query Digest)
    (q_R q_H : ℕ) : Prop :=
  ∀ pk,
    IsCostBounded (Sum.elim (fun _ => 0) romRequestCost) (A pk) q_R ∧
    IsCostBounded (Sum.elim (fun _ => 0) romDirectHashCost) (A pk) q_H

/-- Lazy-ROM extracted single-issuer VOLE-ACT handler at `tag = Prod.mk`:
- On an issuance request, checks `com nf ctx T r = c`; if valid, signs `(c, 0)` using the shared
  lazy random oracle and appends the request to the accepted log.
- On a spend request, checks `(V2)` change commitment opening, `(V3)` natural-number balance
  `t + x = t' + d`, nullifier freshness, and `(V1)` `scheme.verify` against the shared lazy random
  oracle; if all hold, signs `(c', x')` and appends the request to the accepted log.
- On a direct random-oracle query, answers via `ROMSignature.oracle Digest`. -/
@[expose] noncomputable def romExtractedIssuerHandler
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    [DecidableEq Query] [Fintype Digest] [Nonempty Digest]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (scheme : ROMSignature.Scheme PK SK (Commitment × ℕ) Sig Query Digest)
    (keys : PK × SK) :
    (q : AnonymousToken.Conservation.Request Nullifier Context Opening Commitment Sig ⊕ Query) →
      StateT
        (List (Query × Digest) ×
          List (AnonymousToken.Conservation.Request Nullifier Context Opening Commitment Sig))
        PMF
        (((fun _ : AnonymousToken.Conservation.Request Nullifier Context Opening Commitment Sig =>
          Option Sig) ⊕ₒ (fun _ : Query => Digest)) q)
  | .inl (.issue ir) => fun (cache, accepted) =>
      if decide (com ir.nullifier ir.ctx ir.amount ir.opening = ir.commitment) then do
        let coins ← scheme.signCoins keys.2 (ir.commitment, 0)
        let (sig, cache') ← (interpret (ROMSignature.oracle Digest)
          (scheme.sign keys.2 (ir.commitment, 0) coins)).run cache
        return (some sig, (cache', accepted ++ [.issue ir]))
      else
        return (none, (cache, accepted))
  | .inl (.spend sr) => fun (cache, accepted) =>
      if decide (com sr.newNullifier sr.ctx sr.newCredit sr.newOpening = sr.changeCommitment) &&
          decide (sr.oldCredit + sr.oldRefund = sr.newCredit + sr.debit) &&
          !AnonymousToken.Conservation.hasSpentNullifier accepted sr.ctx sr.nullifier then do
        let (ok, cache₁) ← (interpret (ROMSignature.oracle Digest)
          (scheme.verify keys.1
            (AnonymousToken.Credit.target com Prod.mk sr.inputNote sr.oldOpening)
            sr.signature)).run cache
        if ok then do
          let coins ← scheme.signCoins keys.2 (sr.changeCommitment, sr.refund)
          let (sig, cache₂) ← (interpret (ROMSignature.oracle Digest)
            (scheme.sign keys.2 (sr.changeCommitment, sr.refund) coins)).run cache₁
          return (some sig, (cache₂, accepted ++ [.spend sr]))
        else
          return (none, (cache₁, accepted))
      else
        return (none, (cache, accepted))
  | .inr x => fun (cache, accepted) => do
      let (d, cache') ← (ROMSignature.oracle Digest x).run cache
      return (d, (cache', accepted))

/-- Execute `A` in the lazy-ROM extracted VOLE-ACT credit-conservation game at `tag = Prod.mk`,
returning the target context, final RO cache, and oldest-first list of accepted requests. -/
@[expose] noncomputable def runROMExtractedConservation
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    [DecidableEq Query] [Fintype Digest] [Nonempty Digest]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (scheme : ROMSignature.Scheme PK SK (Commitment × ℕ) Sig Query Digest)
    (A : ROMExtractedAdversary Nullifier Context Opening Commitment PK Sig Query Digest) :
    PMF (Context × List (Query × Digest) ×
      List (AnonymousToken.Conservation.Request Nullifier Context Opening Commitment Sig)) := do
  let keys ← scheme.keyGen
  ProbOracleComp.runWith (romExtractedIssuerHandler com scheme keys) (A keys.1) ([], [])

/-- Extracted-model single-issuer VOLE-ACT credit-conservation experiment in the lazy classical
ROM at `tag = Prod.mk`, original to this library: the adversary wins if, in its chosen context
`targetCtx`, total accepted spend debits strictly exceed total accepted issued credit plus granted
refunds. As in `AnonymousToken.Conservation`, VOLEitH witness extraction error and `(V4)` range
checks are outside this extracted-model game. -/
@[expose] noncomputable def romExtractedConservationExperiment
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    [DecidableEq Query] [Fintype Digest] [Nonempty Digest]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (scheme : ROMSignature.Scheme PK SK (Commitment × ℕ) Sig Query Digest)
    (A : ROMExtractedAdversary Nullifier Context Opening Commitment PK Sig Query Digest) :
    PMF Bool :=
  (runROMExtractedConservation com scheme A).map fun (targetCtx, _, accepted) =>
    decide (AnonymousToken.Conservation.issuedAmount accepted targetCtx +
      AnonymousToken.Conservation.grantedRefund accepted targetCtx <
      AnonymousToken.Conservation.spentDebit accepted targetCtx)

/-- Stateful handler used by `romTargetForger`: simulates the lazy-ROM extracted issuer using an
external `ROMSignature.ForgerSpec (Commitment × ℕ) Query Sig Digest` oracle, forwarding `(V1)`
verification hash calls and direct hash queries to `.inr` and accepted `(c, x)` signing calls to
`.inl`. -/
@[expose] def romTargetForgerHandler
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (scheme : ROMSignature.Scheme PK SK (Commitment × ℕ) Sig Query Digest) (pk : PK) :
    (q : AnonymousToken.Conservation.Request Nullifier Context Opening Commitment Sig ⊕ Query) →
      StateT
        (List (AnonymousToken.Conservation.Request Nullifier Context Opening Commitment Sig))
        (ProbOracleComp (ROMSignature.ForgerSpec (Commitment × ℕ) Query Sig Digest))
        (((fun _ : AnonymousToken.Conservation.Request Nullifier Context Opening Commitment Sig =>
          Option Sig) ⊕ₒ (fun _ : Query => Digest)) q)
  | .inl (.issue ir) => fun accepted =>
      if decide (com ir.nullifier ir.ctx ir.amount ir.opening = ir.commitment) then do
        let sig ← ProbOracleComp.query
          (spec := ROMSignature.ForgerSpec (Commitment × ℕ) Query Sig Digest)
          (.inl (ir.commitment, 0))
        return (some sig, accepted ++ [.issue ir])
      else
        return (none, accepted)
  | .inl (.spend sr) => fun accepted =>
      if decide (com sr.newNullifier sr.ctx sr.newCredit sr.newOpening = sr.changeCommitment) &&
          decide (sr.oldCredit + sr.oldRefund = sr.newCredit + sr.debit) &&
          !AnonymousToken.Conservation.hasSpentNullifier accepted sr.ctx sr.nullifier then do
        let ok ← interpret
          (fun x => ProbOracleComp.query
            (spec := ROMSignature.ForgerSpec (Commitment × ℕ) Query Sig Digest) (.inr x))
          (scheme.verify pk
            (AnonymousToken.Credit.target com Prod.mk sr.inputNote sr.oldOpening) sr.signature)
        if ok then do
          let sig ← ProbOracleComp.query
            (spec := ROMSignature.ForgerSpec (Commitment × ℕ) Query Sig Digest)
            (.inl (sr.changeCommitment, sr.refund))
          return (some sig, accepted ++ [.spend sr])
        else
          return (none, accepted)
      else
        return (none, accepted)
  | .inr x => fun accepted => do
      let d ← ProbOracleComp.query
        (spec := ROMSignature.ForgerSpec (Commitment × ℕ) Query Sig Digest) (.inr x)
      return (d, accepted)

/-- Explicit target-forgery reduction from `ROMExtractedAdversary` to a `ProbOracleComp` forger
against `ROMSignature.worldGame scheme _ eufCmaAccept` on messages `Commitment × ℕ`. -/
@[expose] def romTargetForger
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    [Inhabited Commitment] [Inhabited Sig]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (scheme : ROMSignature.Scheme PK SK (Commitment × ℕ) Sig Query Digest)
    (A : ROMExtractedAdversary Nullifier Context Opening Commitment PK Sig Query Digest) :
    PK → ProbOracleComp (ROMSignature.ForgerSpec (Commitment × ℕ) Query Sig Digest)
      ((Commitment × ℕ) × Sig) := fun pk => do
  let (_, accepted) ← (interpret
    (sumHandler
      (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
      (romTargetForgerHandler com scheme pk))
    (A pk)).run []
  match AnonymousToken.Conservation.findNoteForgery accepted with
  | some tok =>
      return (AnonymousToken.Credit.target com Prod.mk tok.payload.message tok.payload.opening,
        tok.signature)
  | none => return ((default, 0), default)

private theorem isCostBounded_interpret_verify_signingCost
    (prog : OracleComp (fun _ : Query => Digest) Bool) :
    IsCostBounded
      (Sum.elim (fun _ => 0)
        (ROMSignature.signingCost (M := Commitment × ℕ) (Query := Query)))
      (interpret
        (fun x => ProbOracleComp.query
          (spec := ROMSignature.ForgerSpec (Commitment × ℕ) Query Sig Digest) (.inr x))
        prog)
      0 := by
  induction prog with
  | pure b => exact IsCostBounded.pure b 0
  | liftBind x k ih =>
    exact IsCostBounded.liftBind_iff.mpr ⟨by simp [ROMSignature.signingCost], fun d => ih d⟩

private theorem isCostBounded_interpret_verify_hashCost
    {vQ : ℕ} (prog : OracleComp (fun _ : Query => Digest) Bool)
    (hprog : prog.IsQueryBounded vQ) :
    IsCostBounded
      (Sum.elim (fun _ => 0)
        (ROMSignature.hashCost (M := Commitment × ℕ) (Query := Query)))
      (interpret
        (fun x => ProbOracleComp.query
          (spec := ROMSignature.ForgerSpec (Commitment × ℕ) Query Sig Digest) (.inr x))
        prog)
      vQ := by
  refine hprog.interpret fun x => ?_
  exact OracleComp.IsCostBounded.query
    (cost := Sum.elim (fun _ => 0) (ROMSignature.hashCost (M := Commitment × ℕ) (Query := Query)))
    (Sum.inr (.inr x))

/-- Query bound for `romTargetForger`: if `A` makes at most `q_R` issuer requests and `q_H` direct
random-oracle queries, and `scheme.verify` makes at most `vQ` random-oracle queries per call, then
`romTargetForger` makes at most `q_R` signing calls and `q_H + q_R * vQ` random-oracle calls. -/
theorem romTargetForger_callBounded
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    [Inhabited Commitment] [Inhabited Sig]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (scheme : ROMSignature.Scheme PK SK (Commitment × ℕ) Sig Query Digest)
    (A : ROMExtractedAdversary Nullifier Context Opening Commitment PK Sig Query Digest)
    {q_R q_H vQ : ℕ}
    (hA : ROMExtractedCallBounded A q_R q_H)
    (hver : ∀ pk m sig, (scheme.verify pk m sig).IsQueryBounded vQ) :
    ProbForgerCallBounded (romTargetForger com scheme A) q_R (q_H + q_R * vQ) := by
  intro pk
  refine ⟨?_, ?_⟩
  · have hbody :
        IsCostBounded
          (Sum.elim (fun _ => 0)
            (ROMSignature.signingCost (M := Commitment × ℕ) (Query := Query)))
          ((interpret
            (sumHandler
              (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
              (romTargetForgerHandler com scheme pk))
            (A pk)).run [])
          q_R := by
      refine OracleComp.IsCostBounded.run_interpret (fun r accepted => ?_) (hA pk).1 []
      rcases r with n | reqOrX
      · simp only [sumHandler, Sum.elim_inl, StateT.run, StateT.lift, ProbOracleComp.sample,
          ProbComp.unifFin]
        exact (OracleComp.IsCostBounded.query
          (cost := Sum.elim (fun _ => 0)
            (ROMSignature.signingCost (M := Commitment × ℕ) (Query := Query)))
          (Sum.inl n)).bind fun a => OracleComp.IsCostBounded.pure (a, accepted) 0
      · rcases reqOrX with req | x
        · cases req with
          | issue ir =>
            simp only [sumHandler, Sum.elim_inr, StateT.run, romTargetForgerHandler,
              romRequestCost]
            split_ifs
            · exact (OracleComp.IsCostBounded.query
                (cost := Sum.elim (fun _ => 0)
                  (ROMSignature.signingCost (M := Commitment × ℕ) (Query := Query)))
                (Sum.inr (.inl (ir.commitment, 0)))).bind fun sig =>
                  OracleComp.IsCostBounded.pure (some sig, accepted ++ [.issue ir]) 0
            · exact OracleComp.IsCostBounded.pure (none, accepted) 1
          | spend sr =>
            simp only [sumHandler, Sum.elim_inr, StateT.run, romTargetForgerHandler,
              romRequestCost]
            split_ifs
            · refine ((isCostBounded_interpret_verify_signingCost _).bind (m := 1)
                fun ok => ?_).mono (by omega)
              split_ifs
              · exact (OracleComp.IsCostBounded.query
                  (cost := Sum.elim (fun _ => 0)
                    (ROMSignature.signingCost (M := Commitment × ℕ) (Query := Query)))
                  (Sum.inr (.inl (sr.changeCommitment, sr.refund)))).bind fun sig =>
                    OracleComp.IsCostBounded.pure (some sig, accepted ++ [.spend sr]) 0
              · exact OracleComp.IsCostBounded.pure (none, accepted) 1
            · exact OracleComp.IsCostBounded.pure (none, accepted) 1
        · simp only [sumHandler, Sum.elim_inr, StateT.run, romTargetForgerHandler, romRequestCost]
          exact (OracleComp.IsCostBounded.query
            (cost := Sum.elim (fun _ => 0)
              (ROMSignature.signingCost (M := Commitment × ℕ) (Query := Query)))
            (Sum.inr (.inr x))).bind fun d => OracleComp.IsCostBounded.pure (d, accepted) 0
    refine (hbody.bind (m := 0) fun ⟨_, accepted⟩ => ?_).mono (by omega)
    dsimp only
    cases AnonymousToken.Conservation.findNoteForgery accepted <;>
      exact OracleComp.IsCostBounded.pure _ 0
  · have hscale :
        IsCostBounded (fun q => Sum.elim (fun _ => 0) romRequestCost q * vQ)
          (A pk) (q_R * vQ) := by
      have h := (hA pk).1
      generalize hprog : A pk = prog at h ⊢
      clear hprog hA A
      induction prog generalizing q_R with
      | pure a => exact OracleComp.IsCostBounded.pure a (q_R * vQ)
      | liftBind q k ih =>
        obtain ⟨hle, hk⟩ := OracleComp.IsCostBounded.liftBind_iff.mp h
        refine OracleComp.IsCostBounded.liftBind_iff.mpr ⟨?_, fun a => ?_⟩
        · exact Nat.mul_le_mul_right vQ hle
        · have hsub : q_R * vQ - Sum.elim (fun _ => 0) romRequestCost q * vQ =
              (q_R - Sum.elim (fun _ => 0) romRequestCost q) * vQ := (Nat.sub_mul _ _ _).symm
          rw [hsub]
          exact ih a (hk a)
    have hcomb :
        IsCostBounded
          (Sum.elim (fun _ => 0) (fun q => romDirectHashCost q + romRequestCost q * vQ))
          (A pk) (q_H + q_R * vQ) := by
      refine ((hA pk).2.add hscale).of_le fun q => ?_
      cases q <;> simp
    have hbody :
        IsCostBounded
          (Sum.elim (fun _ => 0)
            (ROMSignature.hashCost (M := Commitment × ℕ) (Query := Query)))
          ((interpret
            (sumHandler
              (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
              (romTargetForgerHandler com scheme pk))
            (A pk)).run [])
          (q_H + q_R * vQ) := by
      refine OracleComp.IsCostBounded.run_interpret (fun r accepted => ?_) hcomb []
      rcases r with n | reqOrX
      · simp only [sumHandler, Sum.elim_inl, StateT.run, StateT.lift, ProbOracleComp.sample,
          ProbComp.unifFin]
        exact (OracleComp.IsCostBounded.query
          (cost := Sum.elim (fun _ => 0)
            (ROMSignature.hashCost (M := Commitment × ℕ) (Query := Query)))
          (Sum.inl n)).bind fun a => OracleComp.IsCostBounded.pure (a, accepted) 0
      · rcases reqOrX with req | x
        · cases req with
          | issue ir =>
            simp only [sumHandler, Sum.elim_inr, StateT.run, romTargetForgerHandler,
              romDirectHashCost, romRequestCost, zero_add, one_mul]
            split_ifs
            · exact ((OracleComp.IsCostBounded.query
                (cost := Sum.elim (fun _ => 0)
                  (ROMSignature.hashCost (M := Commitment × ℕ) (Query := Query)))
                (Sum.inr (.inl (ir.commitment, 0)))).bind fun sig =>
                  OracleComp.IsCostBounded.pure (some sig, accepted ++ [.issue ir]) 0).mono
                (by simp [ROMSignature.hashCost])
            · exact OracleComp.IsCostBounded.pure (none, accepted) vQ
          | spend sr =>
            simp only [sumHandler, Sum.elim_inr, StateT.run, romTargetForgerHandler,
              romDirectHashCost, romRequestCost, zero_add, one_mul]
            split_ifs
            · have hvb := isCostBounded_interpret_verify_hashCost
                (Commitment := Commitment) (Sig := Sig) _
                (hver pk
                  (AnonymousToken.Credit.target com Prod.mk sr.inputNote sr.oldOpening)
                  sr.signature)
              refine (hvb.bind (m := 0) fun ok => ?_).mono (by omega)
              split_ifs
              · exact (OracleComp.IsCostBounded.query
                  (cost := Sum.elim (fun _ => 0)
                    (ROMSignature.hashCost (M := Commitment × ℕ) (Query := Query)))
                  (Sum.inr (.inl (sr.changeCommitment, sr.refund)))).bind fun sig =>
                    OracleComp.IsCostBounded.pure (some sig, accepted ++ [.spend sr]) 0
              · exact OracleComp.IsCostBounded.pure (none, accepted) 0
            · exact OracleComp.IsCostBounded.pure (none, accepted) vQ
        · simp only [sumHandler, Sum.elim_inr, StateT.run, romTargetForgerHandler,
            romDirectHashCost, romRequestCost, zero_mul, add_zero]
          exact (OracleComp.IsCostBounded.query
            (cost := Sum.elim (fun _ => 0)
              (ROMSignature.hashCost (M := Commitment × ℕ) (Query := Query)))
            (Sum.inr (.inr x))).bind fun d => OracleComp.IsCostBounded.pure (d, accepted) 0
    refine (hbody.bind (m := 0) fun ⟨_, accepted⟩ => ?_).mono (by omega)
    dsimp only
    cases AnonymousToken.Conservation.findNoteForgery accepted <;>
      exact OracleComp.IsCostBounded.pure _ 0

/-- Extract a commitment-binding collision over `(nullifier, context, credit)` from an accepted
VOLE-ACT transcript `accepted` when the first uncertified spend shares its `(c, x)` target with an
accepted request; returns a trivial non-collision otherwise. -/
def romFindBindingCollision
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    [Inhabited Nullifier] [Inhabited Context] [Inhabited Opening]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (accepted :
      List (AnonymousToken.Conservation.Request Nullifier Context Opening Commitment Sig)) :
    Crypto.Commitment.BindingCollision (Nullifier × Context × ℕ) Commitment Opening :=
  AnonymousToken.Conservation.noteBindingCollisionOrTrivial com
    ((AnonymousToken.Conservation.findNoteForgery accepted).bind fun tok =>
      let tgt := AnonymousToken.Credit.target com Prod.mk tok.payload.message tok.payload.opening
      (accepted.find? fun r => decide (r.signedMessage Prod.mk = tgt)).map
        fun r => ⟨tok.payload, r.outputPayload⟩)

/-- Generic ROM commitment-binding experiment induced by `runROMExtractedConservation` against a
keyless commitment scheme `CS`. -/
noncomputable def romBindingExperiment
    {K : Type} [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    [DecidableEq Query] [Fintype Digest] [Nonempty Digest]
    [Inhabited Nullifier] [Inhabited Context] [Inhabited Opening]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (CS : Crypto.Commitment.Scheme K (Nullifier × Context × ℕ) Commitment Opening)
    (scheme : ROMSignature.Scheme PK SK (Commitment × ℕ) Sig Query Digest)
    (A : ROMExtractedAdversary Nullifier Context Opening Commitment PK Sig Query Digest) :
    PMF Bool := do
  let k ← ProbComp.eval CS.keyGen
  let (_, _, accepted) ← runROMExtractedConservation com scheme A
  return CS.isBindingCollision k (romFindBindingCollision com accepted)

private def CacheExtends (c₁ c₂ : List (Query × Digest)) [DecidableEq Query] : Prop :=
  ∀ q d, c₁.lookup q = some d → c₂.lookup q = some d

private theorem cacheExtends_refl [DecidableEq Query] (c : List (Query × Digest)) :
    CacheExtends c c := fun _ _ h => h

private theorem cacheExtends_trans [DecidableEq Query]
    {c₁ c₂ c₃ : List (Query × Digest)} (h₁₂ : CacheExtends c₁ c₂) (h₂₃ : CacheExtends c₂ c₃) :
    CacheExtends c₁ c₃ := fun q d h => h₂₃ q d (h₁₂ q d h)

private theorem cacheExtends_of_mem_support_oracle
    [DecidableEq Query] [Fintype Digest] [Nonempty Digest]
    {q : Query} {c c' : List (Query × Digest)} {d : Digest}
    (h : (d, c') ∈ (ROMSignature.oracle Digest q c).support) :
    CacheExtends c c' ∧ c'.lookup q = some d := by
  refine ⟨?_, ROMSignature.lookup_of_mem_support_oracle h⟩
  cases hl : c.lookup q with
  | some d₀ =>
    have heq := ROMSignature.run_oracle_of_lookup_eq_some (Digest := Digest) hl
    change (d, c') ∈ ((ROMSignature.oracle Digest q).run c).support at h
    rw [heq, PMF.mem_support_pure_iff, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact cacheExtends_refl _
  | none =>
    have heq := ROMSignature.run_oracle_of_lookup_eq_none (Digest := Digest) hl
    change (d, c') ∈ ((ROMSignature.oracle Digest q).run c).support at h
    rw [heq, PMF.mem_support_bind_iff] at h
    obtain ⟨d₁, -, hpure⟩ := h
    rw [PMF.mem_support_pure_iff, Prod.mk.injEq] at hpure
    obtain ⟨rfl, rfl⟩ := hpure
    intro q' d' hq'
    by_cases hqq' : q' = q
    · subst hqq'; rw [hl] at hq'; cases hq'
    · simpa [List.lookup, beq_false_of_ne hqq'] using hq'

private theorem interpret_oracle_extends
    [DecidableEq Query] [Fintype Digest] [Nonempty Digest]
    {α : Type} (prog : OracleComp (fun _ : Query => Digest) α)
    {c c' : List (Query × Digest)} {a : α}
    (h : (a, c') ∈ ((interpret (ROMSignature.oracle Digest) prog).run c).support) :
    CacheExtends c c' := by
  induction prog generalizing c with
  | pure x =>
    change (a, c') ∈ (PMF.pure (x, c)).support at h
    rw [PMF.mem_support_pure_iff, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact cacheExtends_refl _
  | liftBind q k ih =>
    change (a, c') ∈ (((ROMSignature.oracle Digest q).run c).bind fun (d, c₁) =>
      (interpret (ROMSignature.oracle Digest) (k d)).run c₁).support at h
    rw [PMF.mem_support_bind_iff] at h
    obtain ⟨⟨d, c₁⟩, h₁, h₂⟩ := h
    exact cacheExtends_trans (cacheExtends_of_mem_support_oracle h₁).1 (ih d h₂)

private theorem interpret_oracle_replay
    [DecidableEq Query] [Fintype Digest] [Nonempty Digest]
    {α : Type} (prog : OracleComp (fun _ : Query => Digest) α)
    {c c' c_final : List (Query × Digest)} {a : α}
    (h : (a, c') ∈ ((interpret (ROMSignature.oracle Digest) prog).run c).support)
    (hext : CacheExtends c' c_final) :
    (interpret (ROMSignature.oracle Digest) prog).run c_final = PMF.pure (a, c_final) := by
  induction prog generalizing c with
  | pure x =>
    change (a, c') ∈ (PMF.pure (x, c)).support at h
    rw [PMF.mem_support_pure_iff, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    rfl
  | liftBind q k ih =>
    change (a, c') ∈ (((ROMSignature.oracle Digest q).run c).bind fun (d, c₁) =>
      (interpret (ROMSignature.oracle Digest) (k d)).run c₁).support at h
    rw [PMF.mem_support_bind_iff] at h
    obtain ⟨⟨d, c₁⟩, h₁, h₂⟩ := h
    have ⟨_, hlu₁⟩ := cacheExtends_of_mem_support_oracle h₁
    have hext₁ := interpret_oracle_extends (k d) h₂
    have hlu_final : c_final.lookup q = some d := hext q d (hext₁ q d hlu₁)
    change ((ROMSignature.oracle Digest q).run c_final).bind (fun (d', c₁') =>
      (interpret (ROMSignature.oracle Digest) (k d')).run c₁') = _
    rw [ROMSignature.run_oracle_of_lookup_eq_some hlu_final, PMF.pure_bind]
    exact ih d h₂

private def ROMAcceptedInv
    [DecidableEq Query] [Fintype Digest] [Nonempty Digest]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (scheme : ROMSignature.Scheme PK SK (Commitment × ℕ) Sig Query Digest) (pk : PK)
    (st : List (Query × Digest) ×
      List (AnonymousToken.Conservation.Request Nullifier Context Opening Commitment Sig)) :
    Prop :=
  let (cache, accepted) := st
  (∀ r ∈ accepted, match r with
    | .issue ir => com ir.nullifier ir.ctx ir.amount ir.opening = ir.commitment
    | .spend sr =>
      com sr.newNullifier sr.ctx sr.newCredit sr.newOpening = sr.changeCommitment ∧
      sr.oldCredit + sr.oldRefund = sr.newCredit + sr.debit ∧
      (interpret (ROMSignature.oracle Digest)
        (scheme.verify pk
          (AnonymousToken.Credit.target com Prod.mk sr.inputNote sr.oldOpening)
          sr.signature)).run cache = PMF.pure (true, cache)) ∧
  ((AnonymousToken.Conservation.spends accepted).map fun s => (s.ctx, s.nullifier)).Nodup

private theorem romAcceptedInv_replay
    [DecidableEq Query] [Fintype Digest] [Nonempty Digest]
    {com : Nullifier → Context → ℕ → Opening → Commitment}
    {scheme : ROMSignature.Scheme PK SK (Commitment × ℕ) Sig Query Digest} {pk : PK}
    {c c' : List (Query × Digest)}
    {accepted : List (AnonymousToken.Conservation.Request Nullifier Context Opening Commitment Sig)}
    (hinv : ROMAcceptedInv com scheme pk (c, accepted))
    (hext : CacheExtends c c') :
    ROMAcceptedInv com scheme pk (c', accepted) := by
  refine ⟨fun r hr => ?_, hinv.2⟩
  have h := hinv.1 r hr
  cases r with
  | issue ir => exact h
  | spend sr =>
    obtain ⟨hcom, hbal, hrep⟩ := h
    refine ⟨hcom, hbal, ?_⟩
    have hsupp : (true, c) ∈ ((interpret (ROMSignature.oracle Digest)
        (scheme.verify pk
          (AnonymousToken.Credit.target com Prod.mk sr.inputNote sr.oldOpening)
          sr.signature)).run c).support := by
      rw [hrep]
      simp
    exact interpret_oracle_replay _ hsupp hext

private theorem spends_append
    (xs ys : List (AnonymousToken.Conservation.Request Nullifier Context Opening Commitment Sig)) :
    AnonymousToken.Conservation.spends (xs ++ ys) =
      AnonymousToken.Conservation.spends xs ++ AnonymousToken.Conservation.spends ys := by
  simp [AnonymousToken.Conservation.spends, List.filterMap_append]

private theorem romExtractedIssuerHandler_invariant
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    [DecidableEq Query] [Fintype Digest] [Nonempty Digest]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (scheme : ROMSignature.Scheme PK SK (Commitment × ℕ) Sig Query Digest) (keys : PK × SK)
    (A : ROMExtractedAdversary Nullifier Context Opening Commitment PK Sig Query Digest)
    {ctx : Context} {cache : List (Query × Digest)}
    {accepted : List (AnonymousToken.Conservation.Request Nullifier Context Opening Commitment Sig)}
    (hsupp : (ctx, (cache, accepted)) ∈
      (ProbOracleComp.runWith (romExtractedIssuerHandler com scheme keys) (A keys.1)
        ([], [])).support) :
    ROMAcceptedInv com scheme keys.1 (cache, accepted) := by
  refine ProbOracleComp.runWith_invariant
    (romExtractedIssuerHandler com scheme keys)
    (ROMAcceptedInv com scheme keys.1)
    ?_ (A keys.1) ([], []) ⟨by simp, by simp [AnonymousToken.Conservation.spends]⟩
    ctx (cache, accepted) hsupp
  rintro q ⟨c, acc⟩ hinv a ⟨c', acc'⟩ hstep
  cases q with
  | inr x =>
    simp only [romExtractedIssuerHandler, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff, Prod.mk.injEq] at hstep
    obtain ⟨⟨d, c₁⟩, h₁, rfl, rfl, rfl⟩ := hstep
    exact romAcceptedInv_replay hinv (cacheExtends_of_mem_support_oracle h₁).1
  | inl req =>
    cases req with
    | issue ir =>
      dsimp only [romExtractedIssuerHandler] at hstep
      split_ifs at hstep with hcom
      · simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff,
          PMF.mem_support_pure_iff, Prod.mk.injEq] at hstep
        obtain ⟨coins, -, ⟨sig, c₁⟩, hsign, rfl, rfl, rfl⟩ := hstep
        have hext := interpret_oracle_extends _ hsign
        have hprev := romAcceptedInv_replay hinv hext
        refine ⟨fun r hr => ?_, ?_⟩
        · rcases List.mem_append.mp hr with hr | hr
          · exact hprev.1 r hr
          · obtain rfl := List.mem_singleton.mp hr
            exact of_decide_eq_true hcom
        · rw [spends_append]
          simpa [AnonymousToken.Conservation.spends] using hprev.2
      · simp only [PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff, Prod.mk.injEq] at hstep
        obtain ⟨_, rfl, rfl⟩ := hstep
        exact hinv
    | spend sr =>
      dsimp only [romExtractedIssuerHandler] at hstep
      split_ifs at hstep with hpre
      · simp only [PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hstep
        obtain ⟨⟨ok, c₁⟩, hver, hcont⟩ := hstep
        have hext₁ := interpret_oracle_extends _ hver
        cases ok with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, PMF.monad_pure_eq_pure,
            PMF.mem_support_pure_iff, Prod.mk.injEq] at hcont
          obtain ⟨_, rfl, rfl⟩ := hcont
          exact romAcceptedInv_replay hinv hext₁
        | true =>
          simp only [↓reduceIte, PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff,
            PMF.mem_support_pure_iff, Prod.mk.injEq] at hcont
          obtain ⟨coins, -, ⟨sig, c₂⟩, hsign, rfl, rfl, rfl⟩ := hcont
          have hext₂ := interpret_oracle_extends _ hsign
          have hprev := romAcceptedInv_replay hinv (cacheExtends_trans hext₁ hext₂)
          simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hpre
          obtain ⟨⟨hcom, hbal⟩, hfresh⟩ := hpre
          refine ⟨fun r hr => ?_, ?_⟩
          · rcases List.mem_append.mp hr with hr | hr
            · exact hprev.1 r hr
            · obtain rfl := List.mem_singleton.mp hr
              exact ⟨hcom, hbal, interpret_oracle_replay _ hver hext₂⟩
          · rw [spends_append, List.map_append]
            change ((AnonymousToken.Conservation.spends acc).map (fun s => (s.ctx, s.nullifier)) ++
              [(sr.ctx, sr.nullifier)]).Nodup
            rw [List.nodup_append]
            refine ⟨hprev.2, List.nodup_singleton _, fun p hp₁ p' hp₂ heq => ?_⟩
            obtain rfl := List.mem_singleton.mp hp₂
            subst heq
            obtain ⟨s, hs, hsp⟩ := List.mem_map.mp hp₁
            have hmem_acc : AnonymousToken.Conservation.Request.spend s ∈ acc := by
              simp only [AnonymousToken.Conservation.spends, List.mem_filterMap] at hs
              obtain ⟨r, hr, hsome⟩ := hs
              cases r with
              | issue _ => simp at hsome
              | spend sr' => cases hsome; exact hr
            have hhas : AnonymousToken.Conservation.hasSpentNullifier acc sr.ctx sr.nullifier =
                true := by
              simp only [AnonymousToken.Conservation.hasSpentNullifier, List.any_eq_true]
              refine ⟨.spend s, hmem_acc, decide_eq_true ?_⟩
              exact Prod.mk.inj hsp
            rw [hhas] at hfresh
            cases hfresh
      · simp only [PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff, Prod.mk.injEq] at hstep
        obtain ⟨_, rfl, rfl⟩ := hstep
        exact hinv

private theorem rom_worldGame_targetForger_eq
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    [DecidableEq Query] [Fintype Digest] [Nonempty Digest]
    [Inhabited Commitment] [Inhabited Sig]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (scheme : ROMSignature.Scheme PK SK (Commitment × ℕ) Sig Query Digest)
    (A : ROMExtractedAdversary Nullifier Context Opening Commitment PK Sig Query Digest)
    (pk : PK) (sk : SK) :
    Interactive.World.eval (ROMSignature.world scheme sk)
      (ROMSignature.worldRealize scheme pk (romTargetForger com scheme A pk) eufCmaAccept) =
    (ProbOracleComp.runWith (romExtractedIssuerHandler com scheme (pk, sk)) (A pk) ([], [])).bind
      fun (_, cache, accepted) =>
        let msig : (Commitment × ℕ) × Sig :=
          match AnonymousToken.Conservation.findNoteForgery accepted with
          | some tok =>
              (AnonymousToken.Credit.target com Prod.mk tok.payload.message tok.payload.opening,
                tok.signature)
          | none => ((default, 0), default)
        ((interpret (ROMSignature.oracle Digest) (scheme.verify pk msig.1 msig.2)).run cache).map
          fun (ok, _) =>
            ok && !(accepted.map (fun r => r.signedMessage Prod.mk)).contains msig.1 := by
  rw [ROMSignature.eval_world_worldRealize]
  simp only [ROMSignature.runLoggedForger, romTargetForger, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure]
  rw [ProbOracleComp.runWith_run_interpret, PMF.bind_map]
  simp only [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_run_interpret]
  let innerH :=
    fun (q : AnonymousToken.Conservation.Request Nullifier Context Opening Commitment Sig ⊕ Query)
      (st : List (AnonymousToken.Conservation.Request Nullifier Context Opening Commitment Sig) ×
        (List ((Commitment × ℕ) × Sig) × List (Query × Digest))) =>
      (ProbOracleComp.runWith
        (fun q' s =>
          (ProbOracleComp.runWith (ROMSignature.forgerWorldImpl scheme sk)
            (ROMSignature.logSigning q' s.1) s.2).map fun ((a, b), c) => (a, b, c))
        ((romTargetForgerHandler com scheme pk q).run st.1) st.2).map
          fun ((a, b), c) => (a, b, c)
  have hlog_inl : ∀ (m : Commitment × ℕ) (pairs : List ((Commitment × ℕ) × Sig))
      (c : List (Query × Digest)),
      (ProbOracleComp.runWith (ROMSignature.forgerWorldImpl scheme sk)
        (ROMSignature.logSigning (.inl m) pairs) c).map (fun ((a, b), c') => (a, b, c')) =
      (scheme.signCoins sk m).bind fun coins =>
        ((interpret (ROMSignature.oracle Digest) (scheme.sign sk m coins)).run c).map
          fun (sig, c') => (sig, ((m, sig) :: pairs, c')) := by
    intro m pairs c
    simp only [ROMSignature.logSigning, ROMSignature.forgerWorldImpl, sumHandler,
      ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query, ProbOracleComp.runWith_pure,
      PMF.monad_bind_eq_bind, PMF.map_bind, PMF.bind_bind, PMF.pure_map]
    refine PMF.bind_congr_on_support _ _ _ fun coins _ => ?_
    exact (PMF.bind_pure_comp _ _).symm
  have hlog_inr : ∀ (x : Query) (pairs : List ((Commitment × ℕ) × Sig))
      (c : List (Query × Digest)),
      (ProbOracleComp.runWith (ROMSignature.forgerWorldImpl scheme sk)
        (ROMSignature.logSigning (.inr x) pairs) c).map (fun ((a, b), c') => (a, b, c')) =
      ((ROMSignature.oracle Digest x).run c).map fun (d, c') => (d, (pairs, c')) := by
    intro x pairs c
    simp only [ROMSignature.logSigning, ROMSignature.forgerWorldImpl, sumHandler,
      ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query, ProbOracleComp.runWith_pure,
      PMF.monad_bind_eq_bind, PMF.map_bind, PMF.pure_map]
    exact (PMF.bind_pure_comp _ _).symm
  have hverify_run : ∀ (pairs₀ : List ((Commitment × ℕ) × Sig))
      (prog : OracleComp (fun _ : Query => Digest) Bool) (c : List (Query × Digest)),
      ProbOracleComp.runWith
        (fun q' (s : List ((Commitment × ℕ) × Sig) × List (Query × Digest)) =>
          (ProbOracleComp.runWith (ROMSignature.forgerWorldImpl scheme sk)
            (ROMSignature.logSigning q' s.1) s.2).map fun ((a, b), c) => (a, b, c))
        (interpret
          (fun x => ProbOracleComp.query
            (spec := ROMSignature.ForgerSpec (Commitment × ℕ) Query Sig Digest) (.inr x))
          prog)
        (pairs₀, c) =
      ((interpret (ROMSignature.oracle Digest) prog).run c).map
        fun (b, c') => (b, (pairs₀, c')) := by
    intro pairs₀ prog
    induction prog with
    | pure b => intro c; simp [ProbOracleComp.runWith_pure, PMF.pure_map]
    | liftBind x k ih =>
      intro c
      change (ProbOracleComp.runWith
        (fun q' (s : List ((Commitment × ℕ) × Sig) × List (Query × Digest)) =>
          (ProbOracleComp.runWith (ROMSignature.forgerWorldImpl scheme sk)
            (ROMSignature.logSigning q' s.1) s.2).map fun ((a, b), c) => (a, b, c))
        (do
          let d ← ProbOracleComp.query
            (spec := ROMSignature.ForgerSpec (Commitment × ℕ) Query Sig Digest) (.inr x)
          interpret
            (fun x' => ProbOracleComp.query
              (spec := ROMSignature.ForgerSpec (Commitment × ℕ) Query Sig Digest) (.inr x'))
            (k d))
        (pairs₀, c)) = _
      rw [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query, hlog_inr, PMF.bind_map]
      change ((ROMSignature.oracle Digest x).run c).bind _ =
        (((ROMSignature.oracle Digest x).run c).bind fun (d, c') =>
          (interpret (ROMSignature.oracle Digest) (k d)).run c').map _
      rw [PMF.map_bind]
      refine PMF.bind_congr_on_support _ _ _ fun ⟨d, c'⟩ _ => ih d c'
  have hinv_pairs : ∀ ctx acc pairs cache,
      (ctx, (acc, (pairs, cache))) ∈ (ProbOracleComp.runWith innerH (A pk) ([], ([], []))).support →
      pairs.map Prod.fst = (acc.map (fun r => r.signedMessage Prod.mk)).reverse := by
    intro ctx acc pairs cache hsupp
    refine ProbOracleComp.runWith_invariant innerH
      (fun (acc, (pairs, _)) =>
        pairs.map Prod.fst = (acc.map (fun r => r.signedMessage Prod.mk)).reverse)
      ?_ (A pk) ([], ([], [])) rfl ctx (acc, (pairs, cache)) hsupp
    rintro q ⟨acc₀, pairs₀, c₀⟩ hinv₀ a ⟨acc₁, pairs₁, c₁⟩ hstep
    cases q with
    | inr x =>
      dsimp only [innerH, romTargetForgerHandler, StateT.run] at hstep
      rw [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query, hlog_inr, PMF.bind_map,
        PMF.map_bind] at hstep
      simp only [Function.comp_def, ProbOracleComp.runWith_pure, PMF.pure_map,
        PMF.mem_support_bind_iff, PMF.mem_support_pure_iff, Prod.mk.injEq] at hstep
      obtain ⟨⟨d, c'⟩, -, _, rfl, rfl, rfl⟩ := hstep
      exact hinv₀
    | inl req =>
      cases req with
      | issue ir =>
        dsimp only [innerH, romTargetForgerHandler, StateT.run] at hstep
        split_ifs at hstep
        · rw [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query, hlog_inl, PMF.bind_bind,
            PMF.map_bind] at hstep
          simp only [PMF.bind_map, PMF.map_bind, Function.comp_def, ProbOracleComp.runWith_pure,
            PMF.pure_map, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff, Prod.mk.injEq]
            at hstep
          obtain ⟨coins, -, ⟨sig, c'⟩, -, _, rfl, rfl, rfl⟩ := hstep
          simp [hinv₀, List.map_append, AnonymousToken.Conservation.Request.signedMessage]
        · simp only [ProbOracleComp.runWith_pure, PMF.pure_map, PMF.mem_support_pure_iff,
            Prod.mk.injEq] at hstep
          obtain ⟨_, rfl, rfl, rfl⟩ := hstep
          exact hinv₀
      | spend sr =>
        dsimp only [innerH, romTargetForgerHandler, StateT.run] at hstep
        split_ifs at hstep
        · rw [ProbOracleComp.runWith_bind, hverify_run, PMF.bind_map, PMF.map_bind] at hstep
          simp only [Function.comp_def, PMF.mem_support_bind_iff] at hstep
          obtain ⟨⟨ok, c'⟩, -, hcont⟩ := hstep
          cases ok with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte, ProbOracleComp.runWith_pure, PMF.pure_map,
              PMF.mem_support_pure_iff, Prod.mk.injEq] at hcont
            obtain ⟨_, rfl, rfl, rfl⟩ := hcont
            exact hinv₀
          | true =>
            simp only [↓reduceIte] at hcont
            rw [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query, hlog_inl,
              PMF.bind_bind, PMF.map_bind] at hcont
            simp only [PMF.bind_map, PMF.map_bind, Function.comp_def, ProbOracleComp.runWith_pure,
              PMF.pure_map, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff, Prod.mk.injEq]
              at hcont
            obtain ⟨coins, -, ⟨sig, c''⟩, -, _, rfl, rfl, rfl⟩ := hcont
            simp [hinv₀, List.map_append, AnonymousToken.Conservation.Request.signedMessage]
        · simp only [ProbOracleComp.runWith_pure, PMF.pure_map, PMF.mem_support_pure_iff,
            Prod.mk.injEq] at hstep
          obtain ⟨_, rfl, rfl, rfl⟩ := hstep
          exact hinv₀
  have hproj :
      (ProbOracleComp.runWith innerH (A pk) ([], ([], []))).map
        (fun (ctx, (acc, (_, cache))) => (ctx, (cache, acc))) =
      ProbOracleComp.runWith (romExtractedIssuerHandler com scheme (pk, sk)) (A pk) ([], []) := by
    refine ProbOracleComp.runWith_map_state innerH (romExtractedIssuerHandler com scheme (pk, sk))
      (fun (acc, (_, cache)) => (cache, acc)) ?_ (A pk) ([], ([], []))
    rintro q ⟨acc₀, pairs₀, c₀⟩
    cases q with
    | inr x =>
      dsimp only [innerH, romTargetForgerHandler, romExtractedIssuerHandler, StateT.run]
      rw [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query, hlog_inr, PMF.bind_map,
        PMF.map_bind, PMF.map_bind]
      simp only [Function.comp_def, ProbOracleComp.runWith_pure, PMF.pure_map,
        PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
      rfl
    | inl req =>
      cases req with
      | issue ir =>
        dsimp only [innerH, romTargetForgerHandler, romExtractedIssuerHandler, StateT.run]
        split_ifs
        · rw [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query, hlog_inl, PMF.bind_bind,
            PMF.map_bind, PMF.map_bind]
          simp only [PMF.bind_map, PMF.map_bind, Function.comp_def, ProbOracleComp.runWith_pure,
            PMF.pure_map, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
          rfl
        · simp [ProbOracleComp.runWith_pure, PMF.pure_map]
      | spend sr =>
        dsimp only [innerH, romTargetForgerHandler, romExtractedIssuerHandler, StateT.run]
        split_ifs
        · rw [ProbOracleComp.runWith_bind, hverify_run, PMF.bind_map, PMF.map_bind, PMF.map_bind]
          simp only [Function.comp_def, PMF.monad_bind_eq_bind]
          refine PMF.bind_congr_on_support _ _ _ fun ⟨ok, c₁⟩ _ => ?_
          cases ok with
          | false => simp [ProbOracleComp.runWith_pure, PMF.pure_map]
          | true =>
            simp only [↓reduceIte]
            rw [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query, hlog_inl,
              PMF.bind_bind, PMF.map_bind, PMF.map_bind]
            simp only [PMF.bind_map, PMF.map_bind, Function.comp_def, ProbOracleComp.runWith_pure,
              PMF.pure_map, PMF.monad_pure_eq_pure]
            rfl
        · simp [ProbOracleComp.runWith_pure, PMF.pure_map]
  rw [← hproj]
  simp only [PMF.bind_map, PMF.bind_bind]
  refine PMF.bind_congr_on_support _ _ _ fun ⟨ctx, acc, pairs, cache⟩ hsupp => ?_
  have hp := hinv_pairs ctx acc pairs cache hsupp
  dsimp only [Function.comp_def, eufCmaAccept]
  have hcont : ∀ (m : Commitment × ℕ),
      (pairs.map Prod.fst).contains m =
        (acc.map (fun r => r.signedMessage Prod.mk)).contains m := by
    intro m
    simp [hp, List.contains_eq_mem]
  cases hfn : AnonymousToken.Conservation.findNoteForgery acc with
  | none =>
    simp only [ProbOracleComp.runWith_pure, PMF.pure_bind, hcont]
    exact (PMF.bind_pure_comp _ _).symm
  | some tok =>
    simp only [ProbOracleComp.runWith_pure, PMF.pure_bind, hcont]
    exact (PMF.bind_pure_comp _ _).symm

/-- **Generic lazy-ROM extracted credit-conservation reduction** at `tag = Prod.mk`, original to
this library: for any ROM signature scheme
`scheme : ROMSignature.Scheme PK SK (Commitment × ℕ) Sig Query Digest`, any keyless commitment
scheme `CS` whose verifier checks `com nf ctx t o = c` under every key, and any
`ROMExtractedAdversary A`, overspending in `romExtractedConservationExperiment` is bounded by the
ROM EUF-CMA success of `romTargetForger com scheme A` plus the commitment-binding probability
`romBindingExperiment com CS scheme A`. -/
theorem romExtractedConservationExperiment_succProbability_le
    {K : Type} [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    [DecidableEq Query] [Fintype Digest] [Nonempty Digest]
    [Inhabited Nullifier] [Inhabited Context] [Inhabited Opening] [Inhabited Commitment]
    [Inhabited Sig]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (CS : Crypto.Commitment.Scheme K (Nullifier × Context × ℕ) Commitment Opening)
    (hverify : ∀ k nf ctx t c o, CS.verify k (nf, ctx, t) c o = decide (com nf ctx t o = c))
    (scheme : ROMSignature.Scheme PK SK (Commitment × ℕ) Sig Query Digest)
    (A : ROMExtractedAdversary Nullifier Context Opening Commitment PK Sig Query Digest) :
    Game.succProbability (romExtractedConservationExperiment com scheme A) ≤
      Game.succProbability
        (ROMSignature.worldGame scheme (romTargetForger com scheme A) eufCmaAccept) +
      Game.succProbability (romBindingExperiment com CS scheme A) := by
  rw [← ENNReal.coe_le_coe, ENNReal.coe_add]
  simp only [Game.succProbability, ENNReal.coe_toNNReal (PMF.apply_ne_top _ _)]
  have hcons :
      (romExtractedConservationExperiment com scheme A) true =
      ∑' keys : PK × SK, scheme.keyGen keys *
        ∑' res : Context × List (Query × Digest) ×
            List (AnonymousToken.Conservation.Request Nullifier Context Opening Commitment Sig),
          ProbOracleComp.runWith (romExtractedIssuerHandler com scheme keys) (A keys.1)
              ([], []) res *
            (let (ctx, _, acc) := res
             if decide (AnonymousToken.Conservation.issuedAmount acc ctx +
                AnonymousToken.Conservation.grantedRefund acc ctx <
                AnonymousToken.Conservation.spentDebit acc ctx) = true then 1 else 0) := by
    simp only [romExtractedConservationExperiment, runROMExtractedConservation, PMF.map_bind,
      PMF.monad_bind_eq_bind, PMF.bind_apply]
    refine tsum_congr fun keys => ?_
    congr 1
    rw [PMF.map_apply]
    refine tsum_congr fun ⟨ctx, cache, acc⟩ => ?_
    by_cases h :
        decide (AnonymousToken.Conservation.issuedAmount acc ctx +
          AnonymousToken.Conservation.grantedRefund acc ctx <
          AnonymousToken.Conservation.spentDebit acc ctx) = true
    · simp [h]
    · simp [h]
  have hworld :
      (ROMSignature.worldGame scheme (romTargetForger com scheme A) eufCmaAccept) true =
      ∑' keys : PK × SK, scheme.keyGen keys *
        ∑' res : Context × List (Query × Digest) ×
            List (AnonymousToken.Conservation.Request Nullifier Context Opening Commitment Sig),
          ProbOracleComp.runWith (romExtractedIssuerHandler com scheme keys) (A keys.1)
              ([], []) res *
            (let (_, cache, acc) := res
             let msig : (Commitment × ℕ) × Sig :=
               match AnonymousToken.Conservation.findNoteForgery acc with
               | some tok =>
                   (AnonymousToken.Credit.target com Prod.mk
                     tok.payload.message tok.payload.opening, tok.signature)
               | none => ((default, 0), default)
             (((interpret (ROMSignature.oracle Digest)
               (scheme.verify keys.1 msig.1 msig.2)).run cache).map
               fun (ok, _) =>
                 ok && !(acc.map (fun r => r.signedMessage Prod.mk)).contains msig.1)
               true) := by
    simp only [ROMSignature.worldGame, PMF.monad_bind_eq_bind, PMF.bind_apply]
    refine tsum_congr fun ⟨pk, sk⟩ => ?_
    congr 1
    rw [rom_worldGame_targetForger_eq, PMF.bind_apply]
  have hbind :
      (romBindingExperiment com CS scheme A) true =
      ∑' k : K, (ProbComp.eval CS.keyGen) k *
        ∑' keys : PK × SK, scheme.keyGen keys *
          ∑' res : Context × List (Query × Digest) ×
              List (AnonymousToken.Conservation.Request Nullifier Context Opening Commitment Sig),
            ProbOracleComp.runWith (romExtractedIssuerHandler com scheme keys) (A keys.1)
                ([], []) res *
              (let (_, _, acc) := res
               if CS.isBindingCollision k (romFindBindingCollision com acc) = true
                 then 1 else 0) := by
    simp only [romBindingExperiment, runROMExtractedConservation, PMF.monad_bind_eq_bind,
      PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.bind_apply]
    refine tsum_congr fun k => ?_
    congr 1
    refine tsum_congr fun keys => ?_
    congr 1
    refine tsum_congr fun ⟨ctx, cache, acc⟩ => ?_
    simp only [PMF.pure_apply]
    by_cases h : CS.isBindingCollision k (romFindBindingCollision com acc) = true
    · simp [h]
    · simp [h]
  have hcons_k :
      (romExtractedConservationExperiment com scheme A) true =
      ∑' k : K, (ProbComp.eval CS.keyGen) k *
        (romExtractedConservationExperiment com scheme A) true := by
    rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  have hworld_k :
      (ROMSignature.worldGame scheme (romTargetForger com scheme A) eufCmaAccept) true =
      ∑' k : K, (ProbComp.eval CS.keyGen) k *
        (ROMSignature.worldGame scheme (romTargetForger com scheme A) eufCmaAccept) true := by
    rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  rw [hcons_k, hworld_k, hcons, hworld, hbind, ← tsum_add]
  refine tsum_le_tsum fun k => ?_
  rw [← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  rw [← tsum_add]
  refine tsum_le_tsum fun ⟨pk, sk⟩ => ?_
  rw [← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  rw [← tsum_add]
  refine tsum_le_tsum fun ⟨ctx, cache, accepted⟩ => ?_
  rw [← mul_add]
  by_cases hsupp :
      (ctx, (cache, accepted)) ∈
        (ProbOracleComp.runWith (romExtractedIssuerHandler com scheme (pk, sk)) (A pk)
          ([], [])).support
  · refine mul_le_mul_of_nonneg_left ?_ zero_le
    dsimp only
    by_cases hwin :
        decide (AnonymousToken.Conservation.issuedAmount accepted ctx +
          AnonymousToken.Conservation.grantedRefund accepted ctx <
          AnonymousToken.Conservation.spentDebit accepted ctx) = true
    · simp only [hwin, ↓reduceIte]
      have hinv := romExtractedIssuerHandler_invariant com scheme (pk, sk) A hsupp
      have hbal : ∀ s ∈ AnonymousToken.Conservation.spends accepted,
          s.oldCredit + s.oldRefund = s.newCredit + s.debit := by
        intro s hs
        have hmem : AnonymousToken.Conservation.Request.spend s ∈ accepted := by
          simp only [AnonymousToken.Conservation.spends, List.mem_filterMap] at hs
          obtain ⟨r, hr, hsome⟩ := hs
          cases r with
          | issue _ => simp at hsome
          | spend sr => cases hsome; exact hr
        obtain ⟨_, hbal_s, _⟩ := hinv.1 (.spend s) hmem
        exact hbal_s
      cases hfn : AnonymousToken.Conservation.findNoteForgery accepted with
      | none =>
        exfalso
        have hcert := (AnonymousToken.Conservation.findNoteForgery_eq_none_iff accepted).mp hfn
        have hle := AnonymousToken.Conservation.spentDebit_le_of_certified accepted hbal hinv.2
          hcert ctx
        have hlt := of_decide_eq_true hwin
        exact (Nat.not_le.mpr hlt) hle
      | some tok =>
        obtain ⟨s, hs, rfl, hnotmem⟩ := AnonymousToken.Conservation.findNoteForgery_eq_some hfn
        let tgt := AnonymousToken.Credit.target com Prod.mk s.inputNote s.oldOpening
        by_cases hmem_tgt : (accepted.map (fun r => r.signedMessage Prod.mk)).contains tgt
        · -- Case 2: target collision -> commitment binding collision!
          have hmem_list : tgt ∈ accepted.map (fun r => r.signedMessage Prod.mk) :=
            List.contains_iff_mem.mp hmem_tgt
          obtain ⟨r₀, hr₀, hr₀_eq⟩ := List.mem_map.mp hmem_list
          have hfind_isSome :
              (accepted.find? fun r' => decide (r'.signedMessage Prod.mk = tgt)).isSome = true := by
            rw [List.find?_isSome]
            exact ⟨r₀, hr₀, decide_eq_true hr₀_eq⟩
          obtain ⟨r, hr_find⟩ := Option.isSome_iff_exists.mp hfind_isSome
          have hr_mem := List.mem_of_find?_eq_some hr_find
          have hr_eq : r.signedMessage Prod.mk = tgt := by
            have := List.find?_some
              (p := fun r' : AnonymousToken.Conservation.Request Nullifier Context Opening
                Commitment Sig => decide (r'.signedMessage Prod.mk = tgt))
              hr_find
            exact of_decide_eq_true this
          have hr_tgt :
              AnonymousToken.Credit.target com Prod.mk r.outputPayload.message
                r.outputPayload.opening = r.signedMessage Prod.mk := by
            have hloc := hinv.1 r hr_mem
            cases r with
            | issue ir =>
              simp only [AnonymousToken.Credit.target,
                AnonymousToken.Conservation.Request.outputPayload,
                AnonymousToken.Conservation.Request.signedMessage, hloc]
            | spend sr =>
              simp only [AnonymousToken.Credit.target,
                AnonymousToken.Conservation.Request.outputPayload,
                AnonymousToken.Conservation.Request.signedMessage, hloc.1]
          have hbw :
              AnonymousToken.checkBindingWitness (AnonymousToken.Credit.target com Prod.mk)
                ⟨s.inputPayload, r.outputPayload⟩ = true := by
            simp only [AnonymousToken.checkBindingWitness, decide_eq_true_eq]
            refine ⟨?_, ?_⟩
            · intro heq
              apply hnotmem
              exact List.mem_map.mpr ⟨r, hr_mem, heq.symm⟩
            · exact (hr_tgt.trans hr_eq).symm
          have ⟨_, hne, hcom_eq⟩ :=
            (AnonymousToken.Conservation.checkBindingWitness_prod_mk_iff com
              ⟨s.inputPayload, r.outputPayload⟩).mp hbw
          have hcoll :
              CS.isBindingCollision k (romFindBindingCollision com accepted) = true := by
            dsimp only [tgt] at hr_find
            simp only [romFindBindingCollision, hfn, Option.bind_some, hr_find, Option.map_some,
              AnonymousToken.Conservation.noteBindingCollisionOrTrivial,
              AnonymousToken.Conservation.noteBindingCollision,
              AnonymousToken.Conservation.SpendRequest.inputPayload,
              Crypto.Commitment.Scheme.isBindingCollision, Bool.and_eq_true, decide_eq_true_eq]
            refine ⟨⟨hne, ?_⟩, ?_⟩
            · rw [hverify]; exact decide_eq_true rfl
            · rw [hverify]; exact decide_eq_true hcom_eq.symm
          simp only [hcoll, ↓reduceIte]
          exact le_add_self
        · -- Case 1: fresh target -> winning ROM EUF-CMA forgery!
          have hmem_s : AnonymousToken.Conservation.Request.spend s ∈ accepted := by
            simp only [AnonymousToken.Conservation.spends, List.mem_filterMap] at hs
            obtain ⟨r, hr, hsome⟩ := hs
            cases r with
            | issue _ => simp at hsome
            | spend sr => cases hsome; exact hr
          obtain ⟨_, _, hrep⟩ := hinv.1 (.spend s) hmem_s
          have hnot_cont :
              (accepted.map (fun r => r.signedMessage Prod.mk)).contains tgt = false :=
            Bool.eq_false_iff.mpr hmem_tgt
          have hworld_one :
              (((interpret (ROMSignature.oracle Digest)
                (scheme.verify pk tgt s.signature)).run cache).map
                fun (ok, _) =>
                  ok && !(accepted.map (fun r => r.signedMessage Prod.mk)).contains tgt)
                true = 1 := by
            rw [hrep, PMF.pure_map, hnot_cont]
            simp
          exact le_trans (le_of_eq hworld_one.symm) le_self_add
    · simp only [hwin]
      exact zero_le
  · rw [PMF.mem_support_iff, not_not] at hsupp
    simp [hsupp]

/-! ### Concrete `ProbComp` commitment-binding reductions and end-to-end UOV conservation -/

/-- Verification of `detScheme` makes at most `1` random-oracle query. -/
theorem detScheme_verify_isQueryBounded
    {Target Preimage : Type} [DecidableEq Target] [Fintype Target]
    [Finite Preimage]
    (sys : TrapdoorPreimageSystem PK SK Target Preimage)
    (pk : PK) (m : Commitment × ℕ) (sig : Option Preimage) :
    ((detScheme (M := Commitment × ℕ) sys).verify pk m sig).IsQueryBounded 1 := by
  dsimp only [detScheme]
  exact OracleComp.IsCostBounded.liftBind_iff.mpr
    ⟨le_rfl, fun _ => OracleComp.IsCostBounded.pure _ 0⟩

/-- Verification of `saltedScheme` makes at most `1` random-oracle query. -/
theorem saltedScheme_verify_isQueryBounded
    {Salt Target Preimage : Type} [DecidableEq Target]
    [Fintype Salt] [Nonempty Salt] [Fintype Target] [Finite Preimage]
    (sys : TrapdoorPreimageSystem PK SK Target Preimage)
    (pk : PK) (m : Commitment × ℕ) (sig : Salt × Option Preimage) :
    ((saltedScheme (M := Commitment × ℕ) sys Salt).verify pk m sig).IsQueryBounded 1 := by
  dsimp only [saltedScheme]
  exact OracleComp.IsCostBounded.liftBind_iff.mpr
    ⟨le_rfl, fun _ => OracleComp.IsCostBounded.pure _ 0⟩

private noncomputable def lookupOrSampleTarget {Q Target : Type}
    [DecidableEq Q] [Fintype Target] [Nonempty Target]
    (q : Q) (cache : List (Q × Target)) : ProbComp (Target × List (Q × Target)) :=
  match cache.lookup q with
  | some y => pure (y, cache)
  | none => do
      let y ← ProbComp.uniform Target
      return (y, (q, y) :: cache)

private theorem eval_lookupOrSampleTarget {Q Target : Type}
    [DecidableEq Q] [Fintype Target] [Nonempty Target]
    (q : Q) (cache : List (Q × Target)) :
    ProbComp.eval (lookupOrSampleTarget q cache) =
      (ROMSignature.oracle Target q).run cache := by
  dsimp only [lookupOrSampleTarget]
  cases hlu : cache.lookup q with
  | some y =>
    rw [ROMSignature.run_oracle_of_lookup_eq_some hlu, ProbComp.eval_pure]
  | none =>
    rw [ROMSignature.run_oracle_of_lookup_eq_none hlu, ProbComp.eval_bind]
    simp [ProbComp.eval_uniform, ProbComp.eval_pure]

/-- Stateful handler for `detCommitmentBindingReduction`: simulates `romExtractedIssuerHandler` for
`detScheme sys` by sampling uniform RO digests lazily and querying an external
`Target → Option Preimage` inversion oracle. -/
private noncomputable def detBindingProgHandler
    {Target Preimage : Type}
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    [DecidableEq Target] [Fintype Target] [Nonempty Target]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (sys : TrapdoorPreimageSystem PK SK Target Preimage) (pk : PK) :
    (q : AnonymousToken.Conservation.Request Nullifier Context Opening Commitment
        (Option Preimage) ⊕ (Commitment × ℕ)) →
      StateT
        (List ((Commitment × ℕ) × Target) ×
          List (AnonymousToken.Conservation.Request Nullifier Context Opening Commitment
            (Option Preimage)))
        (ProbOracleComp (fun _ : Target => Option Preimage))
        (((fun _ : AnonymousToken.Conservation.Request Nullifier Context Opening Commitment
            (Option Preimage) => Option (Option Preimage)) ⊕ₒ
          (fun _ : Commitment × ℕ => Target)) q)
  | .inl (.issue ir) => fun (cache, accepted) =>
      if decide (com ir.nullifier ir.ctx ir.amount ir.opening = ir.commitment) then do
        let (y, cache') ← ProbOracleComp.sample (lookupOrSampleTarget (ir.commitment, 0) cache)
        let sig ← ProbOracleComp.query (spec := fun _ : Target => Option Preimage) y
        return (some sig, (cache', accepted ++ [.issue ir]))
      else
        return (none, (cache, accepted))
  | .inl (.spend sr) => fun (cache, accepted) =>
      if decide (com sr.newNullifier sr.ctx sr.newCredit sr.newOpening = sr.changeCommitment) &&
          decide (sr.oldCredit + sr.oldRefund = sr.newCredit + sr.debit) &&
          !AnonymousToken.Conservation.hasSpentNullifier accepted sr.ctx sr.nullifier then do
        let tgt := AnonymousToken.Credit.target com Prod.mk sr.inputNote sr.oldOpening
        let (y₁, cache₁) ← ProbOracleComp.sample (lookupOrSampleTarget tgt cache)
        if sys.check pk y₁ sr.signature then do
          let (y₂, cache₂) ←
            ProbOracleComp.sample (lookupOrSampleTarget (sr.changeCommitment, sr.refund) cache₁)
          let sig ← ProbOracleComp.query (spec := fun _ : Target => Option Preimage) y₂
          return (some sig, (cache₂, accepted ++ [.spend sr]))
        else
          return (none, (cache₁, accepted))
      else
        return (none, (cache, accepted))
  | .inr m => fun (cache, accepted) => do
      let (y, cache') ← ProbOracleComp.sample (lookupOrSampleTarget m cache)
      return (y, (cache', accepted))

/-- Oracle program used by `detCommitmentBindingReduction` to simulate `runROMExtractedConservation`
for `detScheme sys` with a `Target → Option Preimage` oracle. -/
private noncomputable def detBindingProg
    {Target Preimage : Type}
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    [DecidableEq Target] [Fintype Target] [Nonempty Target]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (sys : TrapdoorPreimageSystem PK SK Target Preimage) (pk : PK)
    (A : ROMExtractedAdversary Nullifier Context Opening Commitment PK (Option Preimage)
      (Commitment × ℕ) Target) :
    ProbOracleComp (fun _ : Target => Option Preimage)
      (List (AnonymousToken.Conservation.Request Nullifier Context Opening Commitment
        (Option Preimage))) := do
  let (_, _, accepted) ← (interpret
    (sumHandler
      (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
      (detBindingProgHandler com sys pk))
    (A pk)).run ([], [])
  return accepted

/-- Explicit `ProbComp` commitment-binding reduction for `detScheme sys`: simulates the lazy-ROM
extracted issuer with a lazy memoization table for `sys.invert sk` (matching upfront `PMF.pi`
derandomization identically) and returns `romFindBindingCollision com accepted`. -/
noncomputable def detCommitmentBindingReduction
    {K Target Preimage : Type}
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    [DecidableEq Target] [Fintype Target] [Nonempty Target]
    [Inhabited Nullifier] [Inhabited Context] [Inhabited Opening]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (sys : TrapdoorPreimageSystem PK SK Target Preimage)
    (A : ROMExtractedAdversary Nullifier Context Opening Commitment PK (Option Preimage)
      (Commitment × ℕ) Target) :
    K → ProbComp
      (Crypto.Commitment.BindingCollision (Nullifier × Context × ℕ) Commitment Opening) :=
  fun _ => do
    let (pk, sk) ← sys.keyGen
    let (accepted, _) ← ((detBindingProg com sys pk A).runState
      (fun (y : Target) (invCache : List (Target × Option Preimage)) =>
        match invCache.lookup y with
        | some x => pure (x, invCache)
        | none => do
            let x ← sys.invert sk y
            return (x, (y, x) :: invCache))).run []
    return romFindBindingCollision com accepted

private theorem romBindingExperiment_detScheme_eq
    {K Target Preimage : Type}
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    [DecidableEq Target] [Fintype Target] [Nonempty Target] [Finite Preimage]
    [Inhabited Nullifier] [Inhabited Context] [Inhabited Opening]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (CS : Crypto.Commitment.Scheme K (Nullifier × Context × ℕ) Commitment Opening)
    (sys : TrapdoorPreimageSystem PK SK Target Preimage)
    (A : ROMExtractedAdversary Nullifier Context Opening Commitment PK (Option Preimage)
      (Commitment × ℕ) Target) :
    romBindingExperiment com CS (detScheme (M := Commitment × ℕ) sys) A =
      ProbComp.eval (CS.bindingExperiment (detCommitmentBindingReduction com sys A)) := by
  simp only [romBindingExperiment, runROMExtractedConservation,
    Crypto.Commitment.Scheme.bindingExperiment, detCommitmentBindingReduction,
    ProbComp.eval_bind, ProbComp.eval_pure, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  refine PMF.bind_congr_on_support _ _ _ fun k _ => ?_
  have hkg : (detScheme (M := Commitment × ℕ) sys).keyGen =
      (ProbComp.eval sys.keyGen).bind fun (pk, sk) =>
        (PMF.pi fun y => ProbComp.eval (sys.invert sk y)).map fun invTable =>
          (pk, (sk, invTable)) := rfl
  rw [hkg, PMF.bind_bind, PMF.bind_bind, PMF.bind_bind]
  refine PMF.bind_congr_on_support (ProbComp.eval sys.keyGen) _ _ fun ⟨pk, sk⟩ _ => ?_
  rw [PMF.bind_map, PMF.bind_bind]
  simp only [PMF.pure_bind, Function.comp_def]
  have heager : ∀ (invTable : Target → Option Preimage),
      (ProbOracleComp.runWith
        (romExtractedIssuerHandler com (detScheme sys) (pk, (sk, invTable))) (A pk) ([], [])).map
        (fun (_, _, accepted) => accepted) =
      OracleComp.interpret
        (OracleComp.sumHandler ProbComp.unifOracle fun y => PMF.pure (invTable y))
        (detBindingProg com sys pk A) := by
    intro invTable
    have hro :
        OracleComp.interpret
          (OracleComp.sumHandler ProbComp.unifOracle fun y => PMF.pure (invTable y))
          (detBindingProg com sys pk A) =
        (ProbOracleComp.runWith (fun y (_ : Unit) => (PMF.pure (invTable y)).map (·, ()))
          (detBindingProg com sys pk A) ()).map Prod.fst := by
      have h := ProbOracleComp.runWith_readOnly
        (fun y (_ : Unit) => PMF.pure (invTable y)) (detBindingProg com sys pk A) ()
      have h2 := congrArg (PMF.map Prod.fst) h
      simp only [PMF.map_comp, Function.comp_def, PMF.map_id',
        OracleComp.evalWith_eq_interpret] at h2
      exact h2.symm
    rw [hro]
    dsimp only [detBindingProg]
    rw [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_run_interpret]
    have hdrop := ProbOracleComp.runWith_map_state
      (fun q (st : (List ((Commitment × ℕ) × Target) ×
          List (AnonymousToken.Conservation.Request Nullifier Context Opening Commitment
            (Option Preimage))) × Unit) =>
        (ProbOracleComp.runWith (fun y (_ : Unit) => (PMF.pure (invTable y)).map (·, ()))
          ((detBindingProgHandler com sys pk q).run st.1) st.2).map fun ((a, b), c) => (a, b, c))
      (romExtractedIssuerHandler com (detScheme sys) (pk, (sk, invTable)))
      Prod.fst
      (fun q ⟨⟨cache, accepted⟩, _⟩ => by
        cases q with
        | inr m =>
          dsimp only [detBindingProgHandler, romExtractedIssuerHandler, StateT.run]
          simp only [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_sample,
            ProbOracleComp.runWith_pure, eval_lookupOrSampleTarget, PMF.map_bind, PMF.bind_map,
            PMF.pure_map, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, Function.comp_def]
          rfl
        | inl req =>
          cases req with
          | issue ir =>
            dsimp only [detBindingProgHandler, romExtractedIssuerHandler, StateT.run]
            split_ifs
            · simp only [detScheme, interp_norm, ProbOracleComp.runWith_bind,
                ProbOracleComp.runWith_sample, ProbOracleComp.runWith_query,
                ProbOracleComp.runWith_pure, eval_lookupOrSampleTarget, PMF.map_bind,
                PMF.bind_map, PMF.pure_bind, PMF.pure_map, PMF.monad_bind_eq_bind,
                PMF.monad_pure_eq_pure, Function.comp_def]
              change _ = (((ROMSignature.oracle Target (ir.commitment, 0)).run cache).bind
                fun a => PMF.pure (invTable a.1, a.2)).bind _
              simp [PMF.bind_bind, PMF.pure_bind]
            · simp [ProbOracleComp.runWith_pure, PMF.pure_map]
          | spend sr =>
            dsimp only [detBindingProgHandler, romExtractedIssuerHandler, StateT.run]
            split_ifs
            · simp only [detScheme, interp_norm, ProbOracleComp.runWith_bind,
                ProbOracleComp.runWith_sample, eval_lookupOrSampleTarget, PMF.map_bind,
                PMF.bind_map, PMF.pure_bind, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
                Function.comp_def]
              change _ = (((ROMSignature.oracle Target
                  (AnonymousToken.Credit.target com Prod.mk sr.inputNote sr.oldOpening)).run
                  cache).bind fun a => PMF.pure (sys.check pk a.1 sr.signature, a.2)).bind _
              rw [PMF.bind_bind]
              refine PMF.bind_congr_on_support _ _ _ fun ⟨y₁, c₁⟩ _ => ?_
              rw [PMF.pure_bind]
              split_ifs
              · simp only [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_sample,
                  ProbOracleComp.runWith_query, ProbOracleComp.runWith_pure,
                  eval_lookupOrSampleTarget, PMF.map_bind, PMF.bind_map,
                  PMF.pure_bind, PMF.pure_map, Function.comp_def]
                change _ = (((ROMSignature.oracle Target
                    (sr.changeCommitment, sr.refund)).run c₁).bind
                  fun a => PMF.pure (invTable a.1, a.2)).bind _
                simp [PMF.bind_bind, PMF.pure_bind]
              · simp [ProbOracleComp.runWith_pure, PMF.pure_map]
            · simp [ProbOracleComp.runWith_pure, PMF.pure_map])
      (A pk) (([], []), ())
    rw [← hdrop, PMF.map_comp, PMF.map_bind, PMF.bind_map, ← PMF.bind_pure_comp]
    refine PMF.bind_congr_on_support _ _ _ fun ⟨ctx, ⟨cache, accepted⟩, u⟩ _ => ?_
    cases u
    simp [ProbOracleComp.runWith_pure, PMF.pure_map]
  have hacc_eq :
      ((PMF.pi fun y => ProbComp.eval (sys.invert sk y)).bind fun invTable =>
        (ProbOracleComp.runWith
          (romExtractedIssuerHandler com (detScheme sys) (pk, (sk, invTable))) (A pk)
          ([], [])).map fun (_, _, accepted) => accepted) =
      (ProbComp.eval (((detBindingProg com sys pk A).runState
        (fun (y : Target) (invCache : List (Target × Option Preimage)) =>
          match invCache.lookup y with
          | some x => pure (x, invCache)
          | none => do
              let x ← sys.invert sk y
              return (x, (y, x) :: invCache))).run [])).map Prod.fst := by
    have h1 := PMF.bind_congr_on_support (PMF.pi fun y => ProbComp.eval (sys.invert sk y))
      _ _ fun invTable _ => heager invTable
    have h2 := h1.trans (RandomOracle.interpret_prob_eq_memoize
      (fun y => ProbComp.eval (sys.invert sk y)) (detBindingProg com sys pk A))
    rw [h2, ProbOracleComp.eval_runState]
    congr 1
    congr 1
    funext y invCache
    cases hlu : invCache.lookup y with
    | some x =>
      simp [memoize_of_some _ _ _ _ hlu, ProbComp.eval_pure]
    | none =>
      simp only [memoize_of_none _ _ _ hlu, ProbComp.eval_bind, ProbComp.eval_pure,
        PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  have hL :
      ((PMF.pi fun y => ProbComp.eval (sys.invert sk y)).bind fun invTable =>
        (ProbOracleComp.runWith
          (romExtractedIssuerHandler com (detScheme sys) (pk, (sk, invTable))) (A pk)
          ([], [])).bind fun (_, _, accepted) =>
            PMF.pure (CS.isBindingCollision k (romFindBindingCollision com accepted))) =
      ((PMF.pi fun y => ProbComp.eval (sys.invert sk y)).bind fun invTable =>
        (ProbOracleComp.runWith
          (romExtractedIssuerHandler com (detScheme sys) (pk, (sk, invTable))) (A pk)
          ([], [])).map fun (_, _, accepted) => accepted).map
        fun accepted => CS.isBindingCollision k (romFindBindingCollision com accepted) := by
    rw [PMF.map_bind]
    refine PMF.bind_congr_on_support _ _ _ fun invTable _ => ?_
    rw [PMF.map_comp, ← PMF.bind_pure_comp]
    rfl
  rw [hL, hacc_eq, PMF.map_comp, ← PMF.bind_pure_comp]
  rfl

/-- Stateful `ProbComp` handler for `saltedCommitmentBindingReduction`: simulates
`romExtractedIssuerHandler` for `saltedScheme sys Salt` directly in `ProbComp`. -/
private noncomputable def saltedBindingHandler
    {Salt Target Preimage : Type}
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    [DecidableEq Salt] [DecidableEq Target]
    [Fintype Salt] [Nonempty Salt] [Fintype Target] [Nonempty Target]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (sys : TrapdoorPreimageSystem PK SK Target Preimage) (keys : PK × SK) :
    (q : AnonymousToken.Conservation.Request Nullifier Context Opening Commitment
        (Salt × Option Preimage) ⊕ ((Commitment × ℕ) × Salt)) →
      StateT
        (List (((Commitment × ℕ) × Salt) × Target) ×
          List (AnonymousToken.Conservation.Request Nullifier Context Opening Commitment
            (Salt × Option Preimage)))
        ProbComp
        (((fun _ : AnonymousToken.Conservation.Request Nullifier Context Opening Commitment
            (Salt × Option Preimage) => Option (Salt × Option Preimage)) ⊕ₒ
          (fun _ : (Commitment × ℕ) × Salt => Target)) q)
  | .inl (.issue ir) => fun (cache, accepted) =>
      if decide (com ir.nullifier ir.ctx ir.amount ir.opening = ir.commitment) then do
        let s ← ProbComp.uniform Salt
        let (y, cache') ← lookupOrSampleTarget ((ir.commitment, 0), s) cache
        let xOpt ← sys.invert keys.2 y
        return (some (s, xOpt), (cache', accepted ++ [.issue ir]))
      else
        return (none, (cache, accepted))
  | .inl (.spend sr) => fun (cache, accepted) =>
      if decide (com sr.newNullifier sr.ctx sr.newCredit sr.newOpening = sr.changeCommitment) &&
          decide (sr.oldCredit + sr.oldRefund = sr.newCredit + sr.debit) &&
          !AnonymousToken.Conservation.hasSpentNullifier accepted sr.ctx sr.nullifier then do
        let tgt := AnonymousToken.Credit.target com Prod.mk sr.inputNote sr.oldOpening
        let (y₁, cache₁) ← lookupOrSampleTarget (tgt, sr.signature.1) cache
        if sys.check keys.1 y₁ sr.signature.2 then do
          let s ← ProbComp.uniform Salt
          let (y₂, cache₂) ← lookupOrSampleTarget ((sr.changeCommitment, sr.refund), s) cache₁
          let xOpt ← sys.invert keys.2 y₂
          return (some (s, xOpt), (cache₂, accepted ++ [.spend sr]))
        else
          return (none, (cache₁, accepted))
      else
        return (none, (cache, accepted))
  | .inr ms => fun (cache, accepted) => do
      let (y, cache') ← lookupOrSampleTarget ms cache
      return (y, (cache', accepted))

/-- Explicit `ProbComp` commitment-binding reduction for `saltedScheme sys Salt`: simulates the
lazy-ROM extracted issuer directly in `ProbComp` and returns `romFindBindingCollision com accepted`.
-/
noncomputable def saltedCommitmentBindingReduction
    {K Salt Target Preimage : Type}
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    [DecidableEq Salt] [DecidableEq Target]
    [Fintype Salt] [Nonempty Salt] [Fintype Target] [Nonempty Target]
    [Inhabited Nullifier] [Inhabited Context] [Inhabited Opening]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (sys : TrapdoorPreimageSystem PK SK Target Preimage)
    (A : ROMExtractedAdversary Nullifier Context Opening Commitment PK
      (Salt × Option Preimage) ((Commitment × ℕ) × Salt) Target) :
    K → ProbComp
      (Crypto.Commitment.BindingCollision (Nullifier × Context × ℕ) Commitment Opening) :=
  fun _ => do
    let keys ← sys.keyGen
    let (_, _, accepted) ← ((A keys.1).runState (saltedBindingHandler com sys keys)).run ([], [])
    return romFindBindingCollision com accepted

private theorem romBindingExperiment_saltedScheme_eq
    {K Salt Target Preimage : Type}
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    [DecidableEq Salt] [DecidableEq Target]
    [Fintype Salt] [Nonempty Salt] [Fintype Target] [Nonempty Target] [Finite Preimage]
    [Inhabited Nullifier] [Inhabited Context] [Inhabited Opening]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (CS : Crypto.Commitment.Scheme K (Nullifier × Context × ℕ) Commitment Opening)
    (sys : TrapdoorPreimageSystem PK SK Target Preimage)
    (A : ROMExtractedAdversary Nullifier Context Opening Commitment PK
      (Salt × Option Preimage) ((Commitment × ℕ) × Salt) Target) :
    romBindingExperiment com CS (saltedScheme (M := Commitment × ℕ) sys Salt) A =
      ProbComp.eval
        (CS.bindingExperiment (saltedCommitmentBindingReduction (Salt := Salt) com sys A)) := by
  simp only [romBindingExperiment, runROMExtractedConservation,
    Crypto.Commitment.Scheme.bindingExperiment, saltedCommitmentBindingReduction,
    ProbComp.eval_bind, ProbComp.eval_pure, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  refine PMF.bind_congr_on_support _ _ _ fun k _ => ?_
  have hkg : (saltedScheme (M := Commitment × ℕ) sys Salt).keyGen = ProbComp.eval sys.keyGen := rfl
  rw [hkg, PMF.bind_bind, PMF.bind_bind]
  refine PMF.bind_congr_on_support (ProbComp.eval sys.keyGen) _ _ fun ⟨pk, sk⟩ _ => ?_
  rw [ProbOracleComp.eval_runState]
  have hrun :
      ProbOracleComp.runWith
        (romExtractedIssuerHandler com (saltedScheme sys Salt) (pk, sk))
        (A pk) ([], []) =
      ProbOracleComp.runWith
        (fun q st => ProbComp.eval (saltedBindingHandler (Salt := Salt) com sys (pk, sk) q st))
        (A pk) ([], []) := by
    congr 1
    funext q ⟨cache, accepted⟩
    have hsign_eq : ∀ (m : Commitment × ℕ) (c : List (((Commitment × ℕ) × Salt) × Target))
        (req : AnonymousToken.Conservation.Request Nullifier Context Opening Commitment
          (Salt × Option Preimage)),
        ((PMF.uniformOfFintype Salt).bind fun s =>
          (PMF.pi fun y => ProbComp.eval (sys.invert sk y)).bind fun f =>
            ((ROMSignature.oracle Target (m, s)).run c).bind fun x =>
              PMF.pure (some (s, f x.1), x.2, accepted ++ [req])) =
        (PMF.uniformOfFintype Salt).bind fun s =>
          ((ROMSignature.oracle Target (m, s)).run c).bind fun x =>
            (ProbComp.eval (sys.invert sk x.1)).bind fun xOpt =>
              PMF.pure (some (s, xOpt), x.2, accepted ++ [req]) := by
      intro m c req
      refine PMF.bind_congr_on_support _ _ _ fun s _ => ?_
      rw [PMF.bind_comm]
      refine PMF.bind_congr_on_support _ _ _ fun ⟨y, c'⟩ _ => ?_
      have hev := congrArg
        (PMF.map fun xOpt : Option Preimage =>
          (some (s, xOpt), (c', accepted ++ [req])))
        (PMF.pi_map_eval (fun y => ProbComp.eval (sys.invert sk y)) y)
      simpa only [PMF.map_comp, ← PMF.bind_pure_comp, PMF.bind_bind, PMF.pure_bind,
        Function.comp_def] using hev
    cases q with
    | inr ms =>
      simp only [romExtractedIssuerHandler, saltedBindingHandler, ProbComp.eval_bind,
        ProbComp.eval_pure, eval_lookupOrSampleTarget, PMF.monad_bind_eq_bind,
        PMF.monad_pure_eq_pure]
    | inl req =>
      cases req with
      | issue ir =>
        dsimp only [romExtractedIssuerHandler, saltedBindingHandler]
        split_ifs
        · simp only [saltedScheme, interp_norm, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
            PMF.bind_bind, PMF.pure_bind]
          rw [hsign_eq (ir.commitment, 0) cache (.issue ir)]
          simp only [ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure,
            eval_lookupOrSampleTarget]
        · simp [ProbComp.eval_pure]
      | spend sr =>
        dsimp only [romExtractedIssuerHandler, saltedBindingHandler]
        split_ifs
        · simp only [saltedScheme, interp_norm, ProbComp.eval_bind, eval_lookupOrSampleTarget,
            PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]
          refine PMF.bind_congr_on_support
            ((ROMSignature.oracle Target
              (AnonymousToken.Credit.target com Prod.mk sr.inputNote sr.oldOpening,
                sr.signature.1)).run cache) _ _ fun ⟨y₁, c₁⟩ _ => ?_
          split_ifs
          · rw [hsign_eq (sr.changeCommitment, sr.refund) c₁ (.spend sr)]
            simp only [ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure,
              eval_lookupOrSampleTarget]
          · simp [ProbComp.eval_pure]
        · simp [ProbComp.eval_pure]
  rw [hrun, PMF.bind_bind]
  simp only [PMF.pure_bind]

/-- **End-to-end extracted+ROM credit conservation for deterministic unsalted hash-and-sign
(`detScheme sys`)**, original to this library: combines
`romExtractedConservationExperiment_succProbability_le` with `detRomWorldEufCma_succProbability_le`
and `detCommitmentBindingReduction` for any `TrapdoorPreimageSystem` (including `idealUOVSystem`)
and keyless commitment scheme `CS`, substituting `q_S ↦ q_R` and `q_H ↦ q_H + q_R` to obtain loss
`(q_H + q_R + 1)` on `INV + PS_1`, `(q_H + 2 * q_R)`-query `PS` advantage,
`(q_R + (q_H + q_R)).choose 2 / |Target|` birthday slack, and `CS` binding error. -/
theorem romExtractedConservationExperiment_detScheme_succProbability_le
    {K Target Preimage : Type}
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    [DecidableEq Target] [Fintype Target] [Nonempty Target] [Finite Preimage]
    [Inhabited Nullifier] [Inhabited Context] [Inhabited Opening] [Inhabited Commitment]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (CS : Crypto.Commitment.Scheme K (Nullifier × Context × ℕ) Commitment Opening)
    (hverify : ∀ k nf ctx t c o, CS.verify k (nf, ctx, t) c o = decide (com nf ctx t o = c))
    (sys : TrapdoorPreimageSystem PK SK Target Preimage)
    (A : ROMExtractedAdversary Nullifier Context Opening Commitment PK (Option Preimage)
      (Commitment × ℕ) Target)
    {q_R q_H : ℕ} (hA : ROMExtractedCallBounded A q_R q_H) :
    Game.succProbability (romExtractedConservationExperiment com (detScheme sys) A) ≤
      (q_H + q_R + 1 : ℝ≥0) *
        (Experiment.succProbability
          (Signature.targetExperiment sys.toRawScheme (fun _ => ProbComp.uniform Target)
            (detInverter sys (q_H + q_R) (romTargetForger com (detScheme sys) A))) +
        Experiment.advantage
          (psExperimentReal sys
            (detPSOneDistinguisher sys (q_H + q_R) (romTargetForger com (detScheme sys) A)))
          (psExperimentSim sys
            (detPSOneDistinguisher sys (q_H + q_R) (romTargetForger com (detScheme sys) A)))) +
      Experiment.advantage
        (psExperimentReal sys (detPSDistinguisher sys (romTargetForger com (detScheme sys) A)))
        (psExperimentSim sys (detPSDistinguisher sys (romTargetForger com (detScheme sys) A))) +
      ((q_R + (q_H + q_R)).choose 2 : ℝ≥0) * (Fintype.card Target : ℝ≥0)⁻¹ +
      Experiment.succProbability
        (CS.bindingExperiment (detCommitmentBindingReduction com sys A)) := by
  have hcb : ProbForgerCallBounded (romTargetForger com (detScheme sys) A) q_R (q_H + q_R) := by
    simpa [mul_one] using
      romTargetForger_callBounded com (detScheme sys) A hA (detScheme_verify_isQueryBounded sys)
  have hcons := romExtractedConservationExperiment_succProbability_le com CS hverify
    (detScheme sys) A
  have heuf := detRomWorldEufCma_succProbability_le sys (romTargetForger com (detScheme sys) A) hcb
  push_cast at heuf
  have hbind :
      Game.succProbability (romBindingExperiment com CS (detScheme sys) A) =
        Experiment.succProbability
          (CS.bindingExperiment (detCommitmentBindingReduction com sys A)) := by
    rw [romBindingExperiment_detScheme_eq com CS sys A]
  rw [hbind] at hcons
  exact hcons.trans (add_le_add heuf le_rfl)

/-- **End-to-end extracted+ROM credit conservation for salted hash-and-sign
(`saltedScheme sys Salt`)**, original to this library: combines
`romExtractedConservationExperiment_succProbability_le` with
`saltedRomWorldEufCma_succProbability_le` and `saltedCommitmentBindingReduction` for any
`TrapdoorPreimageSystem` (including `idealUOVSystem`) and keyless commitment scheme `CS`,
substituting `q_S ↦ q_R` and `q_H ↦ q_H + q_R` to obtain `(q_H + q_R + 1)` `INV` loss, `q_R`-query
`PS` advantage, `(q_R * (q_H + q_R) + q_R.choose 2) / |Salt|` salt-collision slack, and `CS`
binding error. -/
theorem romExtractedConservationExperiment_saltedScheme_succProbability_le
    {K Salt Target Preimage : Type}
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    [DecidableEq Salt] [DecidableEq Target]
    [Fintype Salt] [Inhabited Salt]
    [Fintype Target] [Nonempty Target] [Finite Preimage]
    [Inhabited Nullifier] [Inhabited Context] [Inhabited Opening] [Inhabited Commitment]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (CS : Crypto.Commitment.Scheme K (Nullifier × Context × ℕ) Commitment Opening)
    (hverify : ∀ k nf ctx t c o, CS.verify k (nf, ctx, t) c o = decide (com nf ctx t o = c))
    (sys : TrapdoorPreimageSystem PK SK Target Preimage)
    (A : ROMExtractedAdversary Nullifier Context Opening Commitment PK
      (Salt × Option Preimage) ((Commitment × ℕ) × Salt) Target)
    {q_R q_H : ℕ} (hA : ROMExtractedCallBounded A q_R q_H) :
    Game.succProbability
        (romExtractedConservationExperiment com (saltedScheme sys Salt) A) ≤
      (q_H + q_R + 1 : ℝ≥0) *
        Experiment.succProbability
          (Signature.targetExperiment sys.toRawScheme (fun _ => ProbComp.uniform Target)
            (saltedInverter (Salt := Salt) sys (q_H + q_R)
              (romTargetForger com (saltedScheme sys Salt) A))) +
      Experiment.advantage
        (psExperimentReal sys
          (saltedPSDistinguisher (Salt := Salt) sys
            (romTargetForger com (saltedScheme sys Salt) A)))
        (psExperimentSim sys
          (saltedPSDistinguisher (Salt := Salt) sys
            (romTargetForger com (saltedScheme sys Salt) A))) +
      ((q_R * (q_H + q_R) + q_R.choose 2 : ℕ) : ℝ≥0) * (Fintype.card Salt : ℝ≥0)⁻¹ +
      Experiment.succProbability
        (CS.bindingExperiment (saltedCommitmentBindingReduction (Salt := Salt) com sys A)) := by
  have hcb :
      ProbForgerCallBounded
        (romTargetForger com (saltedScheme sys Salt) A) q_R (q_H + q_R) := by
    simpa [mul_one] using
      romTargetForger_callBounded com (saltedScheme sys Salt) A hA
        (saltedScheme_verify_isQueryBounded (Salt := Salt) sys)
  have hcons := romExtractedConservationExperiment_succProbability_le com CS hverify
    (saltedScheme sys Salt) A
  have heuf := saltedRomWorldEufCma_succProbability_le (Salt := Salt) sys
    (romTargetForger com (saltedScheme sys Salt) A) hcb
  rw [Nat.cast_add (m := q_H) (n := q_R)] at heuf
  have hbind :
      Game.succProbability
          (romBindingExperiment com CS (saltedScheme sys Salt) A) =
        Experiment.succProbability
          (CS.bindingExperiment (saltedCommitmentBindingReduction (Salt := Salt) com sys A)) := by
    rw [romBindingExperiment_saltedScheme_eq (Salt := Salt) com CS sys A]
  rw [hbind] at hcons
  exact hcons.trans (add_le_add heuf le_rfl)

end ROMConservation

end Cslib.Crypto.UOV.HashAndSign


