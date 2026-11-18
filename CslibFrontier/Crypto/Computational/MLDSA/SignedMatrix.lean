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

/-- Sample the seed and the SHAKE128 matrix prefixes at its derived public address. The
entire shared XOF and optional setup are retained for subsequent signing and public queries. -/
noncomputable def matrixSetup (H : Xofs) (s : Level) :
    PMF (Xofs × Option (PublicMatrix s × KeyPair)) := do
  let seed ← PMF.uniformOfFintype (FixedBytes 32)
  let t ← PMF.uniformOfFintype (MatrixPrefixes s)
  let G := H.withMatrixPrefixes s ((H.expandKeySeed s seed).take 32) t
  let setup := do
    let keys ← G.keyGen s seed
    let A ← G.expandA s (keys.publicKey.take 32)
    return (A, keys)
  return (G, setup)

/-- Install the given coefficient matrix by programming the literal FIPS SHAKE128 addresses
before key generation. Draw all 32 seed bytes and the 894-byte prefixes explicitly. -/
def programmedMatrixSetup (H : Xofs) (s : Level) (A : PublicMatrix s) :
    ProbComp (Xofs × Option (PublicMatrix s × KeyPair)) := do
  let seed ← OracleComp.replicateFin 32 (ProbComp.unifFin 255)
  let t ← OracleComp.replicateFin s.params.k (OracleComp.replicateFin s.params.ℓ
    (OracleComp.replicateFin 894 (ProbComp.unifFin 255)))
  let G := H.withMatrixPrefixes s ((H.expandKeySeed s seed).take 32) (programMatrixPrefixes s t A)
  return (G, (G.keyGen s seed).map fun keys => (A, keys))

/-- Averaging over the supplied matrix reproduces the complete seeded setup, including errors. -/
theorem uniform_programmedMatrixSetup (H : Xofs) (s : Level) :
    (PMF.uniformOfFintype (PublicMatrix s)).bind
        (fun A => (programmedMatrixSetup H s A).eval) = matrixSetup H s := by
  simp only [programmedMatrixSetup, ProbComp.eval_bind, ProbComp.eval_replicateFin,
    ProbComp.eval_unifFin, PMF.pi_uniformOfFintype, ProbComp.eval_pure,
    matrixSetup, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  rw [PMF.bind_comm (PMF.uniformOfFintype (PublicMatrix s))]
  apply congrArg (fun f => (PMF.uniformOfFintype (FixedBytes 32)).bind f)
  funext seed
  have eq := uniform_keyGen_programMatrixPrefixes H s seed
  dsimp only at eq
  rw [← PMF.uniformOfFintype_prod, PMF.map_bind] at eq
  simp only [PMF.map_comp, Function.comp_def] at eq
  exact (PMF.bind_comm _ _ _).trans eq

/-- Every successful programmed setup returns the supplied matrix at the published seed
and a key pair genuinely generated with its accompanying XOFs. -/
theorem keyGen_of_mem_programmedMatrixSetup {H G : Xofs} {s : Level} {A B : PublicMatrix s}
    {keys : KeyPair} (h : (G, some (B, keys)) ∈ (programmedMatrixSetup H s A).eval.support) :
    B = A ∧ (∃ seed, G.keyGen s seed = some keys) ∧
      G.expandA s (keys.publicKey.take 32) = some A := by
  simp only [programmedMatrixSetup, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff, Prod.mk.injEq] at h
  obtain ⟨seed, _, t, _, he, hk⟩ := h
  subst G
  let G := H.withMatrixPrefixes s ((H.expandKeySeed s seed).take 32) (programMatrixPrefixes s t A)
  change some (B, keys) = (G.keyGen s seed).map _ at hk
  cases hg : G.keyGen s seed with
  | none => simp [hg] at hk
  | some pair =>
    simp only [hg, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
    obtain ⟨hA, hkeys⟩ := hk
    subst B
    subst pair
    exact ⟨rfl, ⟨seed, hg⟩, matrix_of_programmed_keyGen H s seed t A keys hg⟩

/-- Run the adaptive classical forger after sampling the actual random matrix prefixes. -/
noncomputable def signedMatrixTrial (H : Xofs) (s : Level) (adv : ClassicalForger) :
    PMF (Option (SignedMatrixTrial s)) :=
  (matrixSetup H s).bind fun z => (runAtSetup s adv z).eval

/-- Simulate the signed execution on an externally supplied coefficient matrix. -/
def programmedSigningTrial (H : Xofs) (s : Level) (adv : ClassicalForger) (A : PublicMatrix s) :
    ProbComp (Option (SignedMatrixTrial s)) := do
  let setup ← programmedMatrixSetup H s A
  runAtSetup s adv setup

/-- On a uniform Hermite right block, the program produces exactly the joint transcript law
of the seeded byte signer, including the raw XOFs, final forgery and all failed setups. -/
theorem eval_programmedSigningTrial (H : Xofs) (s : Level) (adv : ClassicalForger) :
    (PMF.uniformOfFintype (PublicMatrix s)).bind
        (fun A => (programmedSigningTrial H s adv A).eval) =
      signedMatrixTrial H s adv := by
  simp only [programmedSigningTrial, ProbComp.eval_bind, signedMatrixTrial,
    ← uniform_programmedMatrixSetup, PMF.bind_bind]

private def SignedMatrixTrial.extracted {s : Level} (u : SignedMatrixTrial s) :=
  u.xofs.extractLoggedDigest s u.publicKey u.matrix u.forgery u.log

/-- Recover the integer vector from an extracted MSIS witness; all other outcomes return zero. -/
def vectorOfTrial {s : Level} (result : Option (SignedMatrixTrial s)) :
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

private theorem verified_programmedTrial {H : Xofs} {s : Level} {adv : ClassicalForger}
    {A : PublicMatrix s} {u : SignedMatrixTrial s}
    (hu : some u ∈ (programmedSigningTrial H s adv A).eval.support) :
    u.matrix = A ∧ u.xofs.expandA s (u.publicKey.take 32) = some A ∧
      ∀ f ∈ u.log, u.xofs.verify s u.publicKey f.message f.context f.signature = some true := by
  obtain ⟨⟨G, setup⟩, hs, h⟩ := (PMF.mem_support_bind_iff ..).mp
    (show some u ∈ ((programmedMatrixSetup H s A).eval.bind
      fun z => (runAtSetup s adv z).eval).support by simpa [programmedSigningTrial] using hu)
  cases setup with
  | none => simp [runAtSetup] at h
  | some pair =>
    obtain ⟨B, keys⟩ := pair
    obtain ⟨rfl, ⟨seed, hg⟩, hm⟩ := keyGen_of_mem_programmedMatrixSetup hs
    simp only [runAtSetup, ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
      PMF.mem_support_pure_iff, Option.some.injEq] at h
    obtain ⟨⟨f, log⟩, hr, rfl⟩ := h
    rw [eval_runSigningForger] at hr
    exact ⟨rfl, hm, fun _ hf => verify_of_mem_signingTranscript hg hr hf⟩

/-- A fresh accepting byte triple either uses a new digest or the concrete log extractor
returns a raw collision or a short vector against the published matrix. -/
theorem SignedMatrixTrial.cases_of_win {s : Level} (u : SignedMatrixTrial s)
    (hm : u.xofs.expandA s (u.publicKey.take 32) = some u.matrix)
    (log : ∀ f ∈ u.log, u.xofs.verify s u.publicKey f.message f.context f.signature = some true)
    (win : u.wins) :
    u.newDigestWin ∨ u.hashCollision ∨ ModuleSIS.IsSolution (ModuleSIS.hermiteMatrix u.matrix)
      (max (2 * (s.params.γ₁ - s.params.β)) (4 * s.params.γ₂ + 2)) (vectorOfTrial (some u)) := by
  by_cases rep : u.repeatsDigest
  · right
    simp only [SignedMatrixTrial.wins, Xofs.winsForgery, Bool.and_eq_true, Bool.not_eq_true'] at win
    simp only [SignedMatrixTrial.repeatsDigest, List.any_eq_true, beq_iff_eq] at rep
    have verify : u.xofs.verify s u.publicKey u.forgery.message u.forgery.context
        u.forgery.signature = some true := by
      cases hv : u.xofs.verify s u.publicKey u.forgery.message u.forgery.context
        u.forgery.signature <;> simp_all
    obtain ⟨w, extracted, valid⟩ := extractLoggedDigest_of_verifiedLog hm log
      (by simpa using win.2) rep verify
    change u.extracted = some w at extracted
    cases w with
    | collision x y =>
      left
      unfold RepeatedDigestWitness.Valid at valid
      simpa only [SignedMatrixTrial.hashCollision, extracted, decide_eq_true_eq] using valid
    | msis v =>
      right
      unfold RepeatedDigestWitness.Valid at valid
      simpa only [vectorOfTrial, Option.bind_some, extracted] using valid
  · left
    simp [SignedMatrixTrial.newDigestWin, win, Bool.eq_false_iff.mpr rep]

/-- Average the three outcomes of `SignedMatrixTrial.cases_of_win` on a uniform right block.
Both the classical signing program and the retained quantum execution use this counting step. -/
theorem SignedMatrixTrial.bound_of_verifiedLog {s : Level}
    (run : PublicMatrix s → PMF (Option (SignedMatrixTrial s)))
    (verified : ∀ A u, some u ∈ (run A).support →
      u.matrix = A ∧ u.xofs.expandA s (u.publicKey.take 32) = some A ∧
      ∀ f ∈ u.log, u.xofs.verify s u.publicKey f.message f.context f.signature = some true) :
    let trial := (PMF.uniformOfFintype (PublicMatrix s)).bind run
    Game.succProbability (trial.map (·.any SignedMatrixTrial.wins)) ≤
      Game.succProbability (trial.map (·.any SignedMatrixTrial.newDigestWin)) +
      (Game.succProbability (trial.map (·.any SignedMatrixTrial.hashCollision)) +
        Game.succProbability ((PMF.uniformOfFintype (PublicMatrix s)).bind fun A =>
          (run A).map fun result => decide (ModuleSIS.IsSolution (ModuleSIS.hermiteMatrix A)
            (max (2 * (s.params.γ₁ - s.params.β)) (4 * s.params.γ₂ + 2))
            (vectorOfTrial result)))) := by
  dsimp only
  simp only [← ENNReal.coe_le_coe, ENNReal.coe_add, Game.coe_succProbability_ennreal, PMF.map_bind]
  let U := PMF.uniformOfFintype (PublicMatrix s)
  let rest (r : Option (SignedMatrixTrial s)) := r.any fun u => u.wins && !u.newDigestWin
  refine le_trans ?_ (add_le_add (le_refl _)
    (?_ : (U.bind fun A => (run A).map rest) true ≤ _))
  · apply PMF.bind_apply_le_add_on_support _ true
    intro A _
    apply PMF.map_true_le_add
    intro r _ h
    cases r with
    | none => simp at h
    | some u => cases hn : u.newDigestWin <;> simp_all [rest]
  · apply PMF.bind_apply_le_add_on_support _ true
    intro A _
    apply PMF.map_true_le_add
    intro r hr h
    cases r with
    | none => simp [rest] at h
    | some u =>
      obtain ⟨rfl, hm, log⟩ := verified A u hr
      obtain ⟨hw, hn⟩ := Bool.and_eq_true_iff.mp (show u.wins && !u.newDigestWin from h)
      simpa only [Option.any_some, decide_eq_true_eq] using
        (u.cases_of_win hm log hw).resolve_left (by simpa using hn)

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
  have h := SignedMatrixTrial.bound_of_verifiedLog
    (fun A => (programmedSigningTrial H s adv A).eval)
    (fun _ _ hu => verified_programmedTrial hu)
  simpa only [eval_programmedSigningTrial, ModuleSIS.hermiteExperiment, ProbComp.eval_bind,
    ProbComp.eval_uniform, repeatedDigestMatrixSolver, ProbComp.eval_map, PMF.bind_map,
    ProbComp.eval_pure, PMF.map, PMF.bind_bind, PMF.pure_bind, trial, Function.comp_def] using h

end Cslib.Crypto.MLDSA.FIPS204
