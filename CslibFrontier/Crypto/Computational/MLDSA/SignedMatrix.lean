/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.ExpandAProgramming
public import CslibFrontier.Crypto.Computational.MLDSA.FIPS204Signing
public import CslibFrontier.Languages.Probabilistic.Oracle.Substitution
import all CslibFrontier.Crypto.Computational.MLDSA.ExpandAProgramming
import all CslibFrontier.Crypto.Computational.MLDSA.FIPS204ResponseBinding
import CslibFrontier.Languages.Probabilistic.Vector
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Crypto.Game.CloseTo

/-!
# The uniform Module-SIS matrix in a seeded ML-DSA signing experiment

[FIPS 204][NISTFIPS204], Algorithm 6 derives the matrix address from a separate SHAKE256
seed expansion. Conditional on that expansion, installing an external uniform matrix in the
SHAKE128 prefixes preserves the joint law of the raw oracle, both generated keys and the
matrix recovered from the published bytes. Both experiments retain key-generation errors.

`succProbability_forgery_le_newDigest_add_collision_add_msis` bounds the full classical
strong-forgery event in this matrix-prefix experiment. It leaves successes on a new digest
as one event and computes a SHAKE256 collision or a short vector on the supplied uniform matrix
for the remaining successes. All signing queries and direct reads of either XOF share these
streams. The fresh-digest probability, the ambient XOF distribution and the solver's resource
costs remain to be bounded for an end-to-end result.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204

open Cslib.Probability

private theorem matrix_of_programmed_keyGen (H : Xofs) (s : Level) (seed : FixedBytes 32)
    (t : MatrixPrefixes s) (A : PublicMatrix s) (keys : KeyPair) :
    let rho := (H.expandKeySeed s seed).take 32
    let G := H.withMatrixPrefixes s rho (programMatrixPrefixes s t A)
    G.keyGen s seed = some keys → G.expandA s (keys.publicKey.take 32) = some A := by
  intro rho G hk
  have seedEq : keys.publicKey.take 32 = rho := publicSeed_of_keyGen (H := G) hk
  obtain ⟨r, sk, _, hr, hpk, _, _⟩ := privateKey_of_keyGen hk
  have present : G.expandA s (keys.publicKey.take 32) = some sk.A := by
    rwa [hpk, take_encodePublic]
  rw [seedEq] at present ⊢
  change (H.withMatrixPrefixes s rho (programMatrixPrefixes s t A)).expandA s rho = _ at present ⊢
  rw [expandA_programMatrixPrefixes] at present ⊢
  cases hm : (H.withMatrixPrefixes s rho t).expandA s rho with
  | none => simp [hm] at present
  | some B => rfl

/-- Draw an external uniform coefficient matrix and program the literal SHAKE128 matrix
addresses derived by Algorithm 6. The joint law of the entire XOF, both byte keys and the
external matrix agrees with running key generation on fresh matrix prefixes and recovering
the matrix from its published seed. All remaining streams are fixed in both experiments. -/
theorem uniform_keyGen_programMatrixPrefixes (H : Xofs) (s : Level) (seed : FixedBytes 32) :
    let rho := (H.expandKeySeed s seed).take 32
    (PMF.uniformOfFintype (MatrixPrefixes s × PublicMatrix s)).map (fun (t, A) =>
      let G := H.withMatrixPrefixes s rho (programMatrixPrefixes s t A)
      (G, (G.keyGen s seed).map fun keys => (A, keys))) =
    (PMF.uniformOfFintype (MatrixPrefixes s)).map (fun t =>
      let G := H.withMatrixPrefixes s rho t
      (G, do
        let keys ← G.keyGen s seed
        let A ← G.expandA s (keys.publicKey.take 32)
        return (A, keys))) := by
  intro rho
  let read (G : Xofs) : Option (PublicMatrix s × KeyPair) := do
    let keys ← G.keyGen s seed
    let A ← G.expandA s (keys.publicKey.take 32)
    return (A, keys)
  let finish (z : Xofs × Option (PublicMatrix s)) := (z.1, read z.1)
  have eq := congrArg (fun p => PMF.map finish p) (uniform_expandA_programMatrixPrefixes H s rho)
  rw [PMF.map_comp, PMF.map_comp] at eq
  refine Eq.trans ?_ eq
  congr 1
  funext ⟨t, A⟩
  let G := H.withMatrixPrefixes s rho (programMatrixPrefixes s t A)
  change (G, (G.keyGen s seed).map fun keys => (A, keys)) = (G, read G)
  cases hk : G.keyGen s seed with
  | none => simp [read, hk]
  | some keys =>
    have hm := matrix_of_programmed_keyGen H s seed t A keys hk
    change G.expandA s (keys.publicKey.take 32) = some A at hm
    simp [read, hk, hm]

/-- Public data used to check a final forgery after the signed execution. -/
structure SignedMatrixTrial (s : Level) where
  /-- Shared raw SHAKE128 and SHAKE256 oracles. -/
  xofs : Xofs
  /-- Matrix at the seed in the public key. -/
  matrix : PublicMatrix s
  /-- Actual encoded public key. -/
  publicKey : List Byte
  /-- Output of the signing forger. -/
  forgery : Forgery
  /-- Successful responses returned by the signer, with their original messages and contexts. -/
  log : List Forgery

/-- Public calls available to the adaptive classical adversary. XOF inputs are raw bit strings,
and the requested output length counts bytes. -/
inductive PublicQuery where
  /-- Request a hedged signature on this external context and message. -/
  | sign (request : SigningQuery)
  /-- Read the requested prefix at a raw SHAKE128 input. -/
  | shake128 (input : List Bool) (bytes : ℕ)
  /-- Read the requested prefix at a raw SHAKE256 input. -/
  | shake256 (input : List Bool) (bytes : ℕ)

/-- Signing may fail, while a raw XOF request returns the requested output bytes. -/
@[expose] def PublicQuery.Reply : PublicQuery → Type
  | .sign _ => Option (List Byte)
  | .shake128 .. | .shake256 .. => List Byte

/-- A classical forger gets the published bytes and can interleave signing, raw XOF reads
and private randomness. -/
abbrev ClassicalForger := List Byte → ProbOracleComp PublicQuery.Reply Forgery

/-- Answer direct reads from the same raw streams as the signer and verifier, forwarding
each signing call unchanged. -/
@[expose] def Xofs.answerPublicReads (H : Xofs) (adv : ClassicalForger) : SigningForger := fun pk =>
  ProbOracleComp.simulate (spec := PublicQuery.Reply) (fun
    | .sign q => ProbOracleComp.query q
    | .shake128 x n => pure (H.h128.read x n)
    | .shake256 x n => pure (H.h256.read x n)) (adv pk)

private def runAtSetup (s : Level) (adv : ClassicalForger)
    (z : Xofs × Option (PublicMatrix s × KeyPair)) : ProbComp (Option (SignedMatrixTrial s)) :=
  match z with
  | (_, none) => pure none
  | (G, some (A, keys)) => do
    let (f, log) ← G.runSigningForger s keys (G.answerPublicReads adv)
    return some ⟨G, A, keys.publicKey, f, log⟩

/-- Draw the seed and the raw prefixes at its SHAKE128 matrix addresses. Run the actual
hedged signing service under the resulting byte keys, keeping its successful transcript. -/
noncomputable def signedMatrixTrial (H : Xofs) (s : Level) (adv : ClassicalForger) :
    PMF (Option (SignedMatrixTrial s)) := do
  let seed ← PMF.uniformOfFintype (FixedBytes 32)
  let t ← PMF.uniformOfFintype (MatrixPrefixes s)
  let G := H.withMatrixPrefixes s ((H.expandKeySeed s seed).take 32) t
  let setup := do
    let keys ← G.keyGen s seed
    let A ← G.expandA s (keys.publicKey.take 32)
    return (A, keys)
  (runAtSetup s adv (G, setup)).eval

/-- Simulate the same signed execution on an external coefficient matrix. Key generation
and later matrix reads go through the programmed raw oracle. The seed, every 894-byte matrix
prefix and every signing hedge are drawn by the program. -/
def programmedSigningTrial (H : Xofs) (s : Level) (adv : ClassicalForger) (A : PublicMatrix s) :
    ProbComp (Option (SignedMatrixTrial s)) := do
  let seed ← OracleComp.replicateFin 32 (ProbComp.unifFin 255)
  let t ← OracleComp.replicateFin s.params.k (OracleComp.replicateFin s.params.ℓ
    (OracleComp.replicateFin 894 (ProbComp.unifFin 255)))
  let G := H.withMatrixPrefixes s ((H.expandKeySeed s seed).take 32) (programMatrixPrefixes s t A)
  runAtSetup s adv (G, (G.keyGen s seed).map fun keys => (A, keys))

/-- On a uniform Hermite right block, the program produces exactly the joint transcript law
of the seeded byte signer, including the raw XOFs, final forgery and all failed setups. -/
theorem eval_programmedSigningTrial (H : Xofs) (s : Level) (adv : ClassicalForger) :
    (PMF.uniformOfFintype (PublicMatrix s)).bind
        (fun A => (programmedSigningTrial H s adv A).eval) =
      signedMatrixTrial H s adv := by
  simp only [programmedSigningTrial, ProbComp.eval_bind, ProbComp.eval_replicateFin,
    ProbComp.eval_unifFin, PMF.pi_uniformOfFintype, signedMatrixTrial, PMF.monad_bind_eq_bind]
  rw [PMF.bind_comm (PMF.uniformOfFintype (PublicMatrix s))]
  apply congrArg (fun f => (PMF.uniformOfFintype (FixedBytes 32)).bind f)
  funext seed
  have eq := congrArg (fun p => PMF.bind p fun z => (runAtSetup s adv z).eval)
    (uniform_keyGen_programMatrixPrefixes H s seed)
  rw [PMF.bind_map, PMF.bind_map, ← PMF.uniformOfFintype_prod, PMF.bind_bind] at eq
  simp only [PMF.bind_map, Function.comp_def] at eq
  exact (PMF.bind_comm _ _ _).trans eq

private def SignedMatrixTrial.extracted {s : Level} (u : SignedMatrixTrial s) :=
  u.xofs.extractLoggedDigest s u.publicKey u.matrix u.forgery u.log

private def vectorOfTrial {s : Level} (result : Option (SignedMatrixTrial s)) :
    Fin (s.params.k + s.params.ℓ) → Fin s.params.n → ℤ :=
  match result.bind SignedMatrixTrial.extracted with
  | some (.msis v) => v
  | _ => 0

/-- The ordinary Module-SIS solver for the repeated-digest branch. It runs the signed
transcript on its given right block and returns the extracted integer vector. The fallback
zero vector fails the nonzero test in the source experiment. -/
def repeatedDigestMatrixSolver (H : Xofs) (s : Level) (adv : ClassicalForger) (A : PublicMatrix s) :
    ProbComp (Fin (s.params.k + s.params.ℓ) → Fin s.params.n → ℤ) :=
  vectorOfTrial <$> programmedSigningTrial H s adv A

/-- The strong chosen-message win event on the completed trial. -/
def SignedMatrixTrial.wins {s : Level} (u : SignedMatrixTrial s) : Bool :=
  u.xofs.winsForgery s u.publicKey u.forgery u.log

/-- The full digest of the output is present in a successful signing reply. -/
private def SignedMatrixTrial.repeatsDigest {s : Level} (u : SignedMatrixTrial s) : Bool :=
  u.log.any fun g => g.signature.take (digestBytes s) == u.forgery.signature.take (digestBytes s)

/-- A strong forgery whose full digest is absent from the signing log. -/
def SignedMatrixTrial.newDigestWin {s : Level} (u : SignedMatrixTrial s) : Bool :=
  u.wins && !u.repeatsDigest

/-- Run the log extractor and check its two raw inputs at the full FIPS digest length in the
same SHAKE256 oracle that answered verification and signing. -/
def SignedMatrixTrial.hashCollision {s : Level} (u : SignedMatrixTrial s) : Bool :=
  match u.extracted with
  | some (.collision x y) =>
    decide (x ≠ y ∧ u.xofs.h256.read x (digestBytes s) = u.xofs.h256.read y (digestBytes s))
  | _ => false

private theorem extracted_of_programmedWin {H : Xofs} {s : Level} {adv : ClassicalForger}
    {A : PublicMatrix s} {u : SignedMatrixTrial s}
    (hu : some u ∈ (programmedSigningTrial H s adv A).eval.support)
    (hw : u.wins) (repeated : u.repeatsDigest) :
    ∃ w, u.extracted = some w ∧ w.Valid u.xofs A := by
  simp only [programmedSigningTrial, ProbComp.eval_bind, PMF.mem_support_bind_iff] at hu
  obtain ⟨seed, _, t, _, h⟩ := hu
  let G := H.withMatrixPrefixes s ((H.expandKeySeed s seed).take 32) (programMatrixPrefixes s t A)
  change some u ∈ (runAtSetup s adv
    (G, (G.keyGen s seed).map fun keys => (A, keys))).eval.support at h
  cases hg : G.keyGen s seed with
  | none => simp [hg, runAtSetup] at h
  | some keys =>
    simp only [hg, Option.map_some, runAtSetup, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff, Option.some.injEq] at h
    obtain ⟨⟨f, log⟩, hr, rfl⟩ := h
    rw [eval_runSigningForger] at hr
    simp only [SignedMatrixTrial.wins, Xofs.winsForgery, Bool.and_eq_true, Bool.not_eq_true'] at hw
    simp only [SignedMatrixTrial.repeatsDigest, List.any_eq_true, beq_iff_eq] at repeated
    have verify : G.verify s keys.publicKey f.message f.context f.signature = some true := by
      cases hv : G.verify s keys.publicKey f.message f.context f.signature <;> simp_all
    obtain ⟨B, w, hb, he, valid⟩ := extractLoggedDigest_of_signingTranscript hg hr
      (by simpa using hw.2) repeated verify
    have hm := matrix_of_programmed_keyGen H s seed t A keys hg
    change G.expandA s (keys.publicKey.take 32) = some A at hm
    rw [hm, Option.some.injEq] at hb
    subst B
    exact ⟨w, he, valid⟩

/-- For a classical signing forger in the random matrix-prefix experiment, the probability of a
fresh accepted forgery whose digest appeared in the log is at most the probability of a computed
raw SHAKE256 collision plus the success of the explicit solver in the uniform-right-block Hermite
Module-SIS experiment. This bounds the repeated-digest branch at all three FIPS levels. -/
private theorem succProbability_repeatedDigest_le (H : Xofs) (s : Level) (adv : ClassicalForger) :
    Game.succProbability
        ((signedMatrixTrial H s adv).map (·.any fun u => u.wins && u.repeatsDigest)) ≤
      Game.succProbability
        ((signedMatrixTrial H s adv).map (·.any SignedMatrixTrial.hashCollision)) +
        Game.succProbability (ModuleSIS.hermiteExperiment
          (max (2 * (s.params.γ₁ - s.params.β)) (4 * s.params.γ₂ + 2))
          (repeatedDigestMatrixSolver H s adv)).eval := by
  classical
  simp only [← ENNReal.coe_le_coe, ENNReal.coe_add, Game.coe_succProbability_ennreal]
  rw [← eval_programmedSigningTrial H s adv, PMF.map_bind, PMF.map_bind]
  simp only [ModuleSIS.hermiteExperiment, ProbComp.eval_bind, ProbComp.eval_uniform,
    ProbComp.eval_pure, repeatedDigestMatrixSolver, ProbComp.eval_map, PMF.bind_map,
    Function.comp_def]
  apply PMF.bind_apply_le_add_on_support _ true
  intro A _
  apply PMF.map_true_le_add
  intro result present win
  cases result with
  | none => simp at win
  | some u =>
    obtain ⟨hw, hrpt⟩ := Bool.and_eq_true_iff.mp (show u.wins && u.repeatsDigest from win)
    obtain ⟨w, extracted, valid⟩ := extracted_of_programmedWin present hw hrpt
    cases w with
    | collision x y =>
      unfold RepeatedDigestWitness.Valid at valid
      left
      simpa only [Option.any_some, SignedMatrixTrial.hashCollision, extracted, decide_eq_true_eq]
        using valid
    | msis v =>
      unfold RepeatedDigestWitness.Valid at valid
      right
      simpa only [vectorOfTrial, Option.bind_some, extracted, decide_eq_true_eq] using valid

/-- In the experiment with fresh SHAKE128 matrix prefixes, bound the whole strong forgery
event by the remaining fresh-digest event, a computed SHAKE256 collision and success of an
explicit solver on a uniform Hermite Module-SIS matrix. All signing and public hash queries
are adaptive classical queries to the same streams. -/
theorem succProbability_forgery_le_newDigest_add_collision_add_msis (H : Xofs) (s : Level)
    (adv : ClassicalForger) :
    let trial := signedMatrixTrial H s adv
    Game.succProbability (trial.map (·.any SignedMatrixTrial.wins)) ≤
      Game.succProbability (trial.map (·.any SignedMatrixTrial.newDigestWin)) +
      (Game.succProbability (trial.map (·.any SignedMatrixTrial.hashCollision)) +
        Game.succProbability (ModuleSIS.hermiteExperiment
          (max (2 * (s.params.γ₁ - s.params.β)) (4 * s.params.γ₂ + 2))
          (repeatedDigestMatrixSolver H s adv)).eval) := by
  intro trial
  apply le_trans _ (add_le_add (le_refl _) (succProbability_repeatedDigest_le H s adv))
  simp only [← ENNReal.coe_le_coe, ENNReal.coe_add, Game.coe_succProbability_ennreal]
  apply PMF.map_true_le_add
  intro result _ win
  cases result with
  | none => simp at win
  | some u =>
    cases h : u.repeatsDigest <;> simp_all [SignedMatrixTrial.newDigestWin]

end Cslib.Crypto.MLDSA.FIPS204
