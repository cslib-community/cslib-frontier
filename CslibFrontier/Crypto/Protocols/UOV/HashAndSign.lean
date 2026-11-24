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
  have hpost :
      ∀ res : (M × Salt × Option Preimage) × List ((M × Salt) × Target) × List M,
        ProbOracleComp.IsQueryBounded
          (let ((mStar, rStar, sigStar), (cache, signed)) := res
           do
            let yStar ←
              match cache.lookup (mStar, rStar) with
              | some y => pure y
              | none => (ProbOracleComp.sample
                  (spec := fun _ : Unit => Target × Option Preimage) (ProbComp.uniform Target))
            return sys.check pk yStar sigStar && !signed.contains mStar) 0 := by
    rintro ⟨⟨mStar, rStar, sigStar⟩, cache, signed⟩
    dsimp only
    cases cache.lookup (mStar, rStar) with
    | some y =>
      simpa only [pure_bind] using
        (OracleComp.IsCostBounded.pure (cost := Sum.elim (fun _ => 0) fun _ => 1)
          (sys.check pk y sigStar && !signed.contains mStar) 0)
    | none =>
      exact (ProbOracleComp.IsQueryBounded.sample
        (spec := fun _ : Unit => Target × Option Preimage) (ProbComp.uniform Target)).bind
          fun y' => OracleComp.IsCostBounded.pure
            (sys.check pk y' sigStar && !signed.contains mStar) 0
  simpa only [saltedPSDistinguisher, add_zero] using hbody.bind hpost

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
  cases hlu : st.cache.lookup (mStar, rStar) with
  | some yk =>
    obtain ⟨y, idxOpt⟩ := yk
    have hpair_mem : ((mStar, rStar), (y, idxOpt)) ∈ st.cache :=
      mem_of_lookup_eq_some hlu
    simp only [PMF.pure_map]
    by_cases hwin : (sys.check pk y sigStar && !st.signed.contains mStar) &&
        decide (Fin.ofNat (q_H + 1) (idxOpt.getD st.hCount) = jStar) = true
    · simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
        decide_eq_false_iff_not, decide_eq_true_eq] at hwin
      obtain ⟨⟨hchk, hnot_signed⟩, hidx_eq⟩ := hwin
      cases idxOpt with
      | none => exact absurd (hsign mStar rStar y hpair_mem) hnot_signed
      | some k =>
        have hk_lt : k < q_H + 1 := Nat.lt_succ_of_le (Nat.le_of_lt_succ (Nat.lt_succ_of_lt
          ((hlt (mStar, rStar) y k hpair_mem).trans_le hcount_le)))
        have hk_eq : k = jStar.val := by
          have := congrArg Fin.val hidx_eq
          simpa [Fin.val_ofNat, Nat.mod_eq_of_lt hk_lt] using this
        subst hk_eq
        have hyj_eq : st.yAtJ = some y := hyj (mStar, rStar) y hpair_mem
        simp [saltedRelate, hyj_eq, hchk, hnot_signed]
    · have hfalse : ((sys.check pk y sigStar && !st.signed.contains mStar) &&
          decide (Fin.ofNat (q_H + 1) (idxOpt.getD st.hCount) = jStar)) = false :=
        Bool.eq_false_iff.mpr hwin
      rw [hfalse]
      simp only [PMF.pure_apply, Bool.true_eq_false, ↓reduceIte]
      exact zero_le
  | none =>
    simp only [PMF.map_comp, Function.comp_def]
    by_cases hidx_eq : Fin.ofNat (q_H + 1) st.hCount = jStar
    · have hcnt_eq : st.hCount = jStar.val := by
        have := congrArg Fin.val hidx_eq
        simpa [Fin.val_ofNat, Nat.mod_eq_of_lt (Nat.lt_succ_of_le hcount_le)] using this
      have hyj_none : st.yAtJ = none := hnone (le_of_eq hcnt_eq)
      simp only [saltedRelate, hyj_none, PMF.map_comp, Function.comp_def, hidx_eq, decide_true,
        Bool.and_true]
      refine PMF.map_true_mono _ fun y _ h => (Bool.and_eq_true_iff.mp h).1
    · have hzero :
          (PMF.map (fun y => (sys.check pk y sigStar && !st.signed.contains mStar) &&
            decide (Fin.ofNat (q_H + 1) st.hCount = jStar))
            (PMF.uniformOfFintype Target)) true = 0 := by
        simp only [decide_eq_false hidx_eq, Bool.and_false, PMF.map_apply, Bool.true_eq_false,
          ↓reduceIte, tsum_zero]
      rw [hzero]
      exact zero_le

/-- **Classical ROM EUF-CMA reduction for salted hash-and-sign (`ProbOracleComp` form)**
(Kosuge–Xagawa, ePrint 2022/1359, Theorem 1): for any probabilistic ROM forger making at most
`q_S` signing queries and `q_H` direct hash queries,
`Pr[EUF-CMA] ≤ (q_H + 1) * Pr[INV(saltedInverter)] + Adv^PS(saltedPSDistinguisher) +`
`(q_S * q_H + q_S.choose 2) / |Salt|`.
Every reduction is an explicit finite program with query bounds (no runtime certificate claimed;
tracked in #7068). -/
theorem saltedWorldEufCma_succProbability_le {Salt : Type} [DecidableEq M] [DecidableEq Salt]
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

/-- **Classical ROM EUF-CMA reduction for salted hash-and-sign (`ROMSignature.eufCmaGame` form)**
(Kosuge–Xagawa, ePrint 2022/1359, Theorem 1). -/
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
  exact saltedWorldEufCma_succProbability_le sys (liftForger A coinSampler)
    (probForgerCallBounded_liftForger coinSampler hA)

end SaltedReduction

end Cslib.Crypto.UOV.HashAndSign


