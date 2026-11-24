/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
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
  (QROM) bound is proved here: Kosuge–Xagawa (ePrint 2022/1359, Proposition 3) motivates the salted
  variant in the QROM, while the theorems proved here are classical ROM reductions matching
  Kosuge–Xagawa Theorem 1 and Figure 4.
* **Abstract trapdoor preimage systems (`TrapdoorPreimageSystem`).** A system bundles key
  generation, public evaluation `eval : PK → Preimage → Target`, a total finite preimage sampler
  `invert : SK → Target → ProbComp (Option Preimage)` retaining explicit failure (`none`) without
  conditioning, and a secret-free simulated preimage sampler `samplePreimage : PK → ProbComp
  Preimage`. `idealUOVSystem` instantiates this interface with `UOV.idealKeyGen` and uniform
  preimage sampling so that `(idealUOVSystem derive).toRawScheme = UOV.idealRawScheme derive`.
  Concrete round-3 UOV signing and vinegar-retry bounds remain tracked in #4987 and #5219.
* **Programmable ROM `Tag`, starting after vinegar derandomization.** `detScheme` models
  deterministic unsalted hash-and-sign (`Σ_Tag` of [VOLEACT2026], Protocol Specification / Tag)
  after per-target derandomization: key generation draws `invTable ← PMF.pi (eval ∘ invert sk)` so
  repeated signatures on the same target return the same preimage while distinct targets are
  inverted independently, and `Tag` is modeled as a lazy uniform random oracle rather than concrete
  `Keccak-p[800, 12]`. `saltedScheme` models salted hash-and-sign (`SignCoins := Salt × (Target →
  Option Preimage)`), drawing a fresh uniform salt and independent preimage on every signing call.
* **Concrete game bounds.** Preimage resistance (`INV`) reuses `Signature.targetExperiment` on
  `sys.toRawScheme` with uniform targets. Preimage simulatability (`PS`) compares
  `psExperimentReal` (sampling uniform `y` and `x ← invert sk y`) against `psExperimentSim`
  (sampling `s ← samplePreimage pk` and returning `(eval pk s, some s)`), following Kosuge–Xagawa
  (ePrint 2022/1359, Figure 4) with explicit failure retained. All bounds are concrete inequalities
  relating explicit games; no new asymptotic hardness-assumption `Prop` is introduced.

## Main definitions

* `TrapdoorPreimageSystem`, `TrapdoorPreimageSystem.check`, `TrapdoorPreimageSystem.toRawScheme`,
  `idealUOVSystem`: abstract trapdoor-preimage signature core and ideal UOV instantiation.
* `TrapdoorPreimageSystem.sampleRealPair`, `TrapdoorPreimageSystem.sampleSimPair`,
  `PSDistinguisher`, `psExperimentReal`, `psExperimentSim`: Kosuge–Xagawa Figure 4 preimage
  simulatability (`PS`) experiments.
* `detScheme`, `saltedScheme`: deterministic unsalted and salted hash-and-sign
  `ROMSignature.Scheme` constructions.
* `detPSDistinguisher`, `detPSOneDistinguisher`, `detInverter`: explicit multi-query `PS`,
  single-query `PS`, and `INV` reductions for `detScheme`.
* `saltedPSDistinguisher`, `saltedInverter`: explicit `q_S`-query `PS` and `INV` reductions for
  `saltedScheme`.

## Main results

* `detScheme_correct`, `saltedScheme_correct`: completeness of both ROM schemes when `invert`
  succeeds with valid preimages.
* `detPSDistinguisher_queryBound`, `detPSOneDistinguisher_queryBound`,
  `saltedPSDistinguisher_queryBound`: exact query budgets for the `PS` reductions.
* `saltedWorldEufCma_succProbability_le`, `eufCmaGame_saltedScheme_succProbability_le`: classical
  ROM EUF-CMA bound for salted hash-and-sign with `(q_H + 1)` `INV` loss, `q_S`-query `PS`
  advantage, and `(q_S * q_H + q_S.choose 2) / |Salt|` salt-collision slack.
* `detWorldEufCma_succProbability_le`, `eufCmaGame_detScheme_succProbability_le`: classical ROM
  EUF-CMA bound for deterministic unsalted hash-and-sign with `(q_H + 1)` loss on `INV + PS_1`,
  `(q_S + q_H + 1)`-query `PS` advantage, and `(q_S + q_H + 1).choose 2 / |Target|` target
  birthday slack.

## References

* [W. Beullens et al., *UOV: Unbalanced Oil and Vinegar, Algorithm Specifications and Supporting
  Documentation*, v3.0, Appendix A, Definition 2, p. 49][UOV2026].
* [*VOLE-ACT*][VOLEACT2026], Protocol Specification / Tag (`#tag`) and Spending (`#spending`).
* [Baum et al., *PoMFRIT*, USENIX prepublication, Theorem 1 and Definition 3.1][PoMFRIT2026].
* H. Kosuge, K. Xagawa, *Probabilistic Hash-and-Sign with Retry in the Quantum Random Oracle
  Model*, ePrint 2022/1359, Theorem 1 and Figure 4.
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
sampling on `Fin (v + o) → F`. Its `.toRawScheme` is definitionally `UOV.idealRawScheme`. -/
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

/-- An adaptive distinguisher in the preimage-simulatability (`PS`) game (Kosuge–Xagawa,
ePrint 2022/1359, Figure 4): given `pk`, it queries a sampling oracle returning `(y, x)` pairs
and outputs a bit. -/
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
per-target derandomization: `keyGen` draws `invTable ← PMF.pi (eval ∘ invert sk)`, `sign` hashes
`m` and returns `invTable (H m)`, and `verify` checks `sys.check pk (H m) sig`. -/
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

end Cslib.Crypto.UOV.HashAndSign
