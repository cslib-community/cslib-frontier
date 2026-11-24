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
    rintro (n | (m | m)) ⟨cache, signed⟩
    · simpa only [OracleComp.sumHandler, StateT.run_lift, Sum.elim_inl, add_zero] using
        (ProbOracleComp.IsQueryBounded.sample
          (spec := fun _ : Unit => Target × Option Preimage) (ProbComp.unifFin n)).bind
          fun a => OracleComp.IsCostBounded.pure (a, (cache, signed)) 0
    · dsimp only [OracleComp.sumHandler, detPSHandler, StateT.run, Sum.elim_inr]
      cases cache.lookup m with
      | some yx => exact OracleComp.IsCostBounded.pure _ 1
      | none =>
        simpa only [add_zero] using
          (ProbOracleComp.IsQueryBounded.query
            (spec := fun _ : Unit => Target × Option Preimage) ()).bind
            fun yx => OracleComp.IsCostBounded.pure _ 0
    · dsimp only [OracleComp.sumHandler, detPSHandler, StateT.run, Sum.elim_inr]
      cases cache.lookup m with
      | some yx => exact OracleComp.IsCostBounded.pure _ 1
      | none =>
        simpa only [add_zero] using
          (ProbOracleComp.IsQueryBounded.query
            (spec := fun _ : Unit => Target × Option Preimage) ()).bind
            fun yx => OracleComp.IsCostBounded.pure _ 0
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
      · rintro q ⟨cache, signed⟩ hinv a ⟨cache', signed'⟩ hstep
        cases q with
        | inl m =>
          dsimp only at hstep
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
        | inr m =>
          dsimp only at hstep
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
        rintro q ⟨cache, signed, invCache⟩
        cases q with
        | inl m =>
          dsimp only [detEagerHandler, StateT.run]
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
        | inr m =>
          dsimp only [detEagerHandler, StateT.run]
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
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro m' y' x' hm'
        rcases List.mem_cons.mp hm' with hhd | htl
        · injection hhd with hm' _; subst hm'; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hsign m' y' x' htl)
      · intro m' y' x' k hm'
        rcases List.mem_cons.mp hm' with hhd | htl
        · injection hhd with _ h2; injection h2 with _ h3; injection h3 with _ h4; cases h4
        · exact hlt m' y' x' k htl
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
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro m' y' x' hm'
        rcases List.mem_cons.mp hm' with hhd | htl
        · injection hhd with _ h2; injection h2 with _ h3; injection h3 with _ h4; cases h4
        · exact hsign m' y' x' htl
      · intro m' y' x' k hm'
        rcases List.mem_cons.mp hm' with hhd | htl
        · injection hhd with _ h2; injection h2 with _ h3; injection h3 with _ h4
          injection h4 with hk; subst hk; dsimp only; omega
        · exact Nat.lt_succ_of_lt (hlt m' y' x' k htl)
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
      refine ⟨hnone, ?_, ?_, ?_⟩
      · intro m' y' x' hm'
        rcases List.mem_cons.mp hm' with hhd | htl
        · injection hhd with hm' _; subst hm'; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hsign m' y' x' htl)
      · intro m' y' x' k hm'
        rcases List.mem_cons.mp hm' with hhd | htl
        · injection hhd with _ h2; injection h2 with _ h3; injection h3 with _ h4; cases h4
        · exact hlt m' y' x' k htl
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
        refine ⟨fun hle => by dsimp only at hle; omega, ?_, ?_, ?_⟩
        · intro m' y' x' hm'
          rcases List.mem_cons.mp hm' with hhd | htl
          · injection hhd with _ h2; injection h2 with _ h3; injection h3 with _ h4; cases h4
          · exact hsign m' y' x' htl
        · intro m' y' x' k hm'
          rcases List.mem_cons.mp hm' with hhd | htl
          · injection hhd with _ h2; injection h2 with _ h3; injection h3 with _ h4
            injection h4 with hk; subst hk; dsimp only; omega
          · exact Nat.lt_succ_of_lt (hlt m' y' x' k htl)
        · intro m' y' x' hm'
          rcases List.mem_cons.mp hm' with hhd | htl
          · injection hhd with _ h2; injection h2 with hy' _; subst hy'; rfl
          · have := hlt m' y' x' jStar htl; omega
      · rw [PMF.mem_support_map_iff] at hstep
        obtain ⟨yx, -, hpair⟩ := hstep
        rw [Prod.mk.injEq] at hpair
        obtain ⟨-, rfl⟩ := hpair
        refine ⟨fun hle => hnone (Nat.le_of_succ_le hle), ?_, ?_, ?_⟩
        · intro m' y' x' hm'
          rcases List.mem_cons.mp hm' with hhd | htl
          · injection hhd with _ h2; injection h2 with _ h3; injection h3 with _ h4; cases h4
          · exact hsign m' y' x' htl
        · intro m' y' x' k hm'
          rcases List.mem_cons.mp hm' with hhd | htl
          · injection hhd with _ h2; injection h2 with _ h3; injection h3 with _ h4
            injection h4 with hk; subst hk; dsimp only; omega
          · exact Nat.lt_succ_of_lt (hlt m' y' x' k htl)
        · intro m' y' x' hm'
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
              match cache.lookup mStar with
              | some (y, _, idxOpt) =>
                PMF.pure ((sys.check pk y sigStar && !signed.contains mStar) &&
                  decide (Fin.ofNat (q_H + 1) (idxOpt.getD hCount) = jStar))
              | none =>
                (PMF.uniformOfFintype Target).map fun y =>
                  (sys.check pk y sigStar && !signed.contains mStar) &&
                    decide (Fin.ofNat (q_H + 1) hCount = jStar)) true := by
    unfold detPSOneDistinguisher
    simp only [ProbOracleComp.run_bind, ProbOracleComp.run_query, ProbOracleComp.run_sample,
      ProbComp.eval_bind, ProbComp.eval_uniform, PMF.bind_map]
    rw [PMF.bind_comm]
    congr 1
    refine PMF.bind_congr_on_support _ _ _ fun jStar _ => ?_
    refine PMF.bind_congr_on_support _ _ _ fun yxStar _ => ?_
    refine PMF.bind_congr_on_support _ _ _ fun ⟨⟨mStar, sigStar⟩, cache, signed, hCount⟩ _ => ?_
    cases cache.lookup mStar with
    | some yxk => simp [ProbOracleComp.run_pure, ProbComp.eval_pure]
    | none =>
      simp only [ProbOracleComp.run_bind, ProbOracleComp.run_sample, ProbOracleComp.run_pure,
        ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure]
      exact (PMF.bind_pure_comp _ _).symm
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
      match st.cache.lookup mStar with
      | some (y, _, idxOpt) =>
        PMF.pure ((sys.check pk y sigStar && !st.signed.contains mStar) &&
          decide (Fin.ofNat (q_H + 1) (idxOpt.getD st.hCount) = jStar))
      | none =>
        (PMF.uniformOfFintype Target).map fun y =>
          (sys.check pk y sigStar && !st.signed.contains mStar) &&
            decide (Fin.ofNat (q_H + 1) st.hCount = jStar)
  have htrack_eq_win :
      ((trackProj jStar).map fun p => p.1 && decide (p.2 = jStar)) true =
      ((ProbOracleComp.runWith (detTrackHandler sys pk jStar.val) (forger pk)
        ⟨[], [], 0, false⟩).bind winCheck) true := by
    dsimp only [trackProj, winCheck]
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
          dsimp only [winCheck]
          cases hlu : st.cache.lookup mStar with
          | some yxk =>
            dsimp only
            rcases yxk with ⟨y, x, idxOpt⟩
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
    have hL_simp :
        ((ProbOracleComp.runWith (detOneTrackHandler sys pk jStar.val μSim) (forger pk)
          ⟨[], [], 0, none⟩).bind
            (fun (out, st) => (detOneRelate μSim st).map (out, ·))).map
              (fun (out, (st, _)) => (out, (st.cache, st.signed, st.hCount))) =
        (ProbOracleComp.runWith (detOneTrackHandler sys pk jStar.val μSim) (forger pk)
          ⟨[], [], 0, none⟩).map (fun (out, st) => (out, (st.cache, st.signed, st.hCount))) := by
      rw [PMF.map_bind]
      refine (PMF.bind_congr_on_support _ _ _ fun ⟨out, st⟩ _ => ?_).trans
        (PMF.bind_pure_comp _ _).symm
      cases hyj : st.yAtJ with
      | some y => simp [detOneRelate, hyj, PMF.pure_map]
      | none =>
        simp only [detOneRelate, hyj, PMF.map_comp, Function.comp_def]
        exact PMF.map_const _ _
    rw [hL_simp, PMF.map_bind] at hsim
    rw [hsim]
    refine PMF.bind_congr_on_support _ _ _ fun yStar _ => ?_
    rw [ProbOracleComp.eval_runState]
    refine ProbOracleComp.runWith_map_state_of_invariant
      (detOneEmbedHandler sys pk jStar.val)
      (fun q s => ProbComp.eval (detPSOneSimHandler sys pk jStar.val yStar q s))
      (fun (st, _) => (st.cache, st.signed, st.hCount))
      (fun (_, yS) => yS = yStar)
      ?_ ?_ (forger pk) (⟨[], [], 0, none⟩, yStar) rfl
    · rintro q ⟨st, yS⟩ hyS a ⟨st', yS'⟩ hstep
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
    · rintro q ⟨st, yS⟩ hyS
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
          by_cases heq : st.hCount = jStar.val
          · simp [heq, ProbComp.eval_pure, PMF.pure_map]
          · simp only [heq, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure, PMF.map_comp,
              Function.comp_def]
            exact (PMF.bind_pure_comp _ _).symm
  let postOne : (M × Option Preimage) ×
      (List (M × (Target × Option (Option Preimage) × Option ℕ)) × List M × ℕ) → PMF Bool :=
    fun ((mStar, sigStar), (cache, signed, hCount)) =>
      match cache.lookup mStar with
      | some (y, _, idxOpt) =>
        PMF.pure ((sys.check pk y sigStar && !signed.contains mStar) &&
          decide (Fin.ofNat (q_H + 1) (idxOpt.getD hCount) = jStar))
      | none =>
        (PMF.uniformOfFintype Target).map fun y =>
          (sys.check pk y sigStar && !signed.contains mStar) &&
            decide (Fin.ofNat (q_H + 1) hCount = jStar)
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
    dsimp only [winCheck, postOne, Function.comp_def]
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
              match cache.lookup mStar with
              | some (y, _, idxOpt) =>
                PMF.pure ((sys.check pk y sigStar && !signed.contains mStar) &&
                  decide (Fin.ofNat (q_H + 1) (idxOpt.getD hCount) = jStar))
              | none =>
                (PMF.uniformOfFintype Target).map fun y =>
                  (sys.check pk y sigStar && !signed.contains mStar) &&
                    decide (Fin.ofNat (q_H + 1) hCount = jStar) := by
    unfold detPSOneDistinguisher
    simp only [ProbOracleComp.run_bind, ProbOracleComp.run_query, ProbOracleComp.run_sample,
      ProbComp.eval_bind, ProbComp.eval_uniform]
    have hmap_fst :
        (ProbComp.eval (sys.sampleRealPair sk)).bind (fun yxStar =>
          (PMF.uniformOfFintype (Fin (q_H + 1))).bind fun jStar =>
            (ProbComp.eval (((forger pk).runState
              (detPSOneSimHandler sys pk jStar.val yxStar.1)).run ([], [], 0))).bind
              fun ((mStar, sigStar), (cache, signed, hCount)) =>
                match cache.lookup mStar with
                | some (y, _, idxOpt) =>
                  PMF.pure ((sys.check pk y sigStar && !signed.contains mStar) &&
                    decide (Fin.ofNat (q_H + 1) (idxOpt.getD hCount) = jStar))
                | none =>
                  (PMF.uniformOfFintype Target).map fun y =>
                    (sys.check pk y sigStar && !signed.contains mStar) &&
                      decide (Fin.ofNat (q_H + 1) hCount = jStar)) =
        ((ProbComp.eval (sys.sampleRealPair sk)).map Prod.fst).bind fun yStar =>
          (PMF.uniformOfFintype (Fin (q_H + 1))).bind fun jStar =>
            (ProbComp.eval (((forger pk).runState
              (detPSOneSimHandler sys pk jStar.val yStar)).run ([], [], 0))).bind
              fun ((mStar, sigStar), (cache, signed, hCount)) =>
                match cache.lookup mStar with
                | some (y, _, idxOpt) =>
                  PMF.pure ((sys.check pk y sigStar && !signed.contains mStar) &&
                    decide (Fin.ofNat (q_H + 1) (idxOpt.getD hCount) = jStar))
                | none =>
                  (PMF.uniformOfFintype Target).map fun y =>
                    (sys.check pk y sigStar && !signed.contains mStar) &&
                      decide (Fin.ofNat (q_H + 1) hCount = jStar) := by
      rw [PMF.bind_map]
      rfl
    have hbody_eq :
        (ProbComp.eval (sys.sampleRealPair sk)).bind (fun yxStar =>
          (PMF.uniformOfFintype (Fin (q_H + 1))).bind fun jStar =>
            (ProbComp.eval (((forger pk).runState
              (detPSOneSimHandler sys pk jStar.val yxStar.1)).run ([], [], 0))).bind
              fun ((mStar, sigStar), (cache, signed, hCount)) =>
                ProbComp.eval ((match cache.lookup mStar with
                  | some (y, _, idxOpt) =>
                    pure ((sys.check pk y sigStar && !signed.contains mStar) &&
                      decide (Fin.ofNat (q_H + 1) (idxOpt.getD hCount) = jStar))
                  | none => do
                    let y ← (ProbOracleComp.sample
                      (spec := fun _ : Unit => Target × Option Preimage) (ProbComp.uniform Target))
                    return (sys.check pk y sigStar && !signed.contains mStar) &&
                      decide (Fin.ofNat (q_H + 1) hCount = jStar)).run
                  fun _ => sys.sampleRealPair sk)) =
        (ProbComp.eval (sys.sampleRealPair sk)).bind fun yxStar =>
          (PMF.uniformOfFintype (Fin (q_H + 1))).bind fun jStar =>
            (ProbComp.eval (((forger pk).runState
              (detPSOneSimHandler sys pk jStar.val yxStar.1)).run ([], [], 0))).bind
              fun ((mStar, sigStar), (cache, signed, hCount)) =>
                match cache.lookup mStar with
                | some (y, _, idxOpt) =>
                  PMF.pure ((sys.check pk y sigStar && !signed.contains mStar) &&
                    decide (Fin.ofNat (q_H + 1) (idxOpt.getD hCount) = jStar))
                | none =>
                  (PMF.uniformOfFintype Target).map fun y =>
                    (sys.check pk y sigStar && !signed.contains mStar) &&
                      decide (Fin.ofNat (q_H + 1) hCount = jStar) := by
      refine PMF.bind_congr_on_support _ _ _ fun yxStar _ => ?_
      refine PMF.bind_congr_on_support _ _ _ fun jStar _ => ?_
      refine PMF.bind_congr_on_support _ _ _ fun ⟨⟨mStar, sigStar⟩, cache, signed, hCount⟩ _ => ?_
      cases hlu : cache.lookup mStar with
      | some yxk => simp [hlu, ProbOracleComp.run_pure, ProbComp.eval_pure]
      | none =>
        simp only [hlu, ProbOracleComp.run_bind, ProbOracleComp.run_sample, ProbOracleComp.run_pure,
          ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure]
        exact (PMF.bind_pure_comp _ _).symm
    rw [hbody_eq, hmap_fst, sys.eval_sampleRealPair_map_fst sk, PMF.bind_comm]
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
        (detPSOneSimHandler sys pk jStar.val yStar)).run ([], [], 0)) := by
    rw [ProbOracleComp.eval_runState]
    refine ProbOracleComp.runWith_map_state_of_invariant
      (detOneEmbedHandler sys pk jStar.val)
      (fun q s => ProbComp.eval (detPSOneSimHandler sys pk jStar.val yStar q s))
      (fun (st, _) => (st.cache, st.signed, st.hCount))
      (fun (_, yS) => yS = yStar)
      ?_ ?_ (forger pk) (⟨[], [], 0, none⟩, yStar) rfl
    · rintro q ⟨st, yS⟩ hyS a ⟨st', yS'⟩ hstep
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
    · rintro q ⟨st, yS⟩ hyS
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
          by_cases heq : st.hCount = jStar.val
          · simp [heq, ProbComp.eval_pure, PMF.pure_map]
          · simp only [heq, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure, PMF.map_comp,
              Function.comp_def]
            exact (PMF.bind_pure_comp _ _).symm
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
      ?_ ?_ (forger pk) (⟨[], [], 0, none⟩, yStar) rfl
    · have hcongr := congrArg (PMF.map fun ((_, sigStar), _) => sigStar) hproj
      simpa only [PMF.map_comp, Function.comp_def, List.map_nil] using hcongr
    · rintro q ⟨st, yS⟩ hyS a ⟨st', yS'⟩ hstep
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
            match cache.lookup mStar with
            | some (y, _, idxOpt) =>
              PMF.pure ((sys.check pk y sigStar && !signed.contains mStar) &&
                decide (Fin.ofNat (q_H + 1) (idxOpt.getD hCount) = jStar))
            | none =>
              (PMF.uniformOfFintype Target).map fun y =>
                (sys.check pk y sigStar && !signed.contains mStar) &&
                  decide (Fin.ofNat (q_H + 1) hCount = jStar)) =
      (ProbOracleComp.runWith
        (detOneTrackHandler sys pk jStar.val (PMF.uniformOfFintype Target)) (forger pk)
        ⟨[], [], 0, none⟩).bind fun ((mStar, sigStar), st) =>
          match st.cache.lookup mStar with
          | some (y, _, idxOpt) =>
            PMF.pure ((sys.check pk y sigStar && !st.signed.contains mStar) &&
              decide (Fin.ofNat (q_H + 1) (idxOpt.getD st.hCount) = jStar))
          | none =>
            (PMF.uniformOfFintype Target).map fun y =>
              (sys.check pk y sigStar && !st.signed.contains mStar) &&
                decide (Fin.ofNat (q_H + 1) st.hCount = jStar) := by
    have hdist :
        ((PMF.uniformOfFintype Target).bind fun yStar =>
          ProbComp.eval (((forger pk).runState
            (detPSOneSimHandler sys pk jStar.val yStar)).run ([], [], 0))) =
        (ProbOracleComp.runWith
          (detOneTrackHandler sys pk jStar.val (PMF.uniformOfFintype Target)) (forger pk)
          ⟨[], [], 0, none⟩).map (fun (out, st) => (out, (st.cache, st.signed, st.hCount))) := by
      have hproj :=
        congrArg (PMF.map fun (out, (st, _)) => (out, (st.cache, st.signed, st.hCount))) hsim
      have hL_simp :
          ((ProbOracleComp.runWith
            (detOneTrackHandler sys pk jStar.val (PMF.uniformOfFintype Target)) (forger pk)
            ⟨[], [], 0, none⟩).bind
              (fun (out, st) => (detOneRelate (PMF.uniformOfFintype Target) st).map (out, ·))).map
                (fun (out, (st, _)) => (out, (st.cache, st.signed, st.hCount))) =
          (ProbOracleComp.runWith
            (detOneTrackHandler sys pk jStar.val (PMF.uniformOfFintype Target)) (forger pk)
            ⟨[], [], 0, none⟩).map (fun (out, st) => (out, (st.cache, st.signed, st.hCount))) := by
        rw [PMF.map_bind]
        refine (PMF.bind_congr_on_support _ _ _ fun ⟨out, st⟩ _ => ?_).trans
          (PMF.bind_pure_comp _ _).symm
        cases hyj : st.yAtJ with
        | some y => simp [detOneRelate, hyj, PMF.pure_map]
        | none =>
          simp only [detOneRelate, hyj, PMF.map_comp, Function.comp_def]
          exact PMF.map_const _ _
      rw [hL_simp, PMF.map_bind] at hproj
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
  cases hlu : st.cache.lookup mStar with
  | some yxk =>
    dsimp only
    rcases yxk with ⟨y, xOpt, idxOpt⟩
    have hpmem := mem_of_lookup_eq_some hlu
    by_cases hwin : (sys.check pk y sigStar && !st.signed.contains mStar) &&
        decide (Fin.ofNat (q_H + 1) (idxOpt.getD st.hCount) = jStar) = true
    · simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
        decide_eq_false_iff_not, decide_eq_true_eq] at hwin
      obtain ⟨⟨hchk, hnot_signed⟩, hidx_eq⟩ := hwin
      cases idxOpt with
      | none => exact absurd (hsign mStar y xOpt hpmem) hnot_signed
      | some k =>
        have hk_lt : k < q_H + 1 := Nat.lt_succ_of_le
          ((hlt mStar y xOpt k hpmem).le.trans hcount_le)
        have hk_eq : k = jStar.val := by
          have := congrArg Fin.val hidx_eq
          simpa [Fin.val_ofNat, Nat.mod_eq_of_lt hk_lt] using this
        subst hk_eq
        have hyj_eq : st.yAtJ = some y := hyj mStar y xOpt hpmem
        simp [detOneRelate, hyj_eq, hchk, hnot_signed]
    · have hfalse : ((sys.check pk y sigStar && !st.signed.contains mStar) &&
          decide (Fin.ofNat (q_H + 1) (idxOpt.getD st.hCount) = jStar)) = false :=
        Bool.eq_false_iff.mpr hwin
      rw [hfalse]
      simp only [PMF.pure_apply, Bool.true_eq_false, ↓reduceIte]
      exact zero_le
  | none =>
    dsimp only
    by_cases hidx_eq : Fin.ofNat (q_H + 1) st.hCount = jStar
    · have hcnt_eq : st.hCount = jStar.val := by
        have := congrArg Fin.val hidx_eq
        simpa [Fin.val_ofNat, Nat.mod_eq_of_lt (Nat.lt_succ_of_le hcount_le)] using this
      have hyj_none : st.yAtJ = none := hnone (le_of_eq hcnt_eq)
      simp only [detOneRelate, hyj_none, PMF.map_comp, Function.comp_def, hidx_eq, decide_true,
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

/-- **Classical ROM EUF-CMA reduction for deterministic unsalted hash-and-sign
(`ProbOracleComp` form)**: for any probabilistic ROM forger making at most `q_S` signing queries
and `q_H` direct hash queries,
`Pr[EUF-CMA] ≤ (q_H + 1) * (Pr[INV(detInverter)] + Adv^PS(detPSOneDistinguisher)) +`
`Adv^PS(detPSDistinguisher) + (q_S + q_H).choose 2 / |Target|`.
Every reduction is an explicit finite program with proved query bounds (`detPSDistinguisher`
makes at most `q_S + q_H` `PS` queries, `detPSOneDistinguisher` makes at most `1` `PS` query;
no runtime certificate claimed, tracked in #7068). -/
theorem detWorldEufCma_succProbability_le [DecidableEq M] [DecidableEq Target]
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
(`ROMSignature.eufCmaGame` form)**. -/
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
  exact detWorldEufCma_succProbability_le sys (liftForger A coinSampler)
    (probForgerCallBounded_liftForger coinSampler hA)

end DetReduction

end Cslib.Crypto.UOV.HashAndSign


