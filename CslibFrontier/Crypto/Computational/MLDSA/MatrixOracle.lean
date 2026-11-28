/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.FIPS204
import CslibFrontier.Languages.Probabilistic.RandomOracle.Probabilistic
import CslibFrontier.Languages.Probabilistic.Vector
import CslibFrontier.Probability.PMF.Bind

/-!
# The Module-LWE key switch for ML-DSA with a public matrix oracle

The public matrix seed selects an entry of a classical random function. Sampling its
first matrix on demand gives the same joint law as planting the challenger's matrix at the
published seed and continuing with the resulting cache. The post-key computation receives
the unrounded vector so that it can construct the actual public bytes and perform verification.
A byte-forgery experiment must implement the adversary view in that computation.

The secret and error are independently uniform coefficientwise on `[-η,η]`, the
short-secret law in [BaiEtAl2021Dilithium], §§6.1–6.2.1. This ideal matrix experiment
supplies the key switch used by the shared-digest ML-DSA reduction.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204.MatrixOracle

open Cslib.Probability
open OracleComp

/-- Embed the uniform digit indexing `[-η,η]` as a short coefficient modulo the FIPS modulus. -/
def shortCoeff (s : Level) (d : Fin (2 * s.params.η + 1)) : ZMod 8380417 :=
  (d.val : ZMod 8380417) - s.params.η

/-- The short-secret MLWE coefficient law, uniform on the signed interval `[-η,η]`. -/
noncomputable def shortCoefficientLaw (s : Level) : PMF (ZMod 8380417) :=
  (PMF.uniformOfFintype (Fin (2 * s.params.η + 1))).map (shortCoeff s)

/-- One short-secret MLWE polynomial. Its 256 coefficients are independent uniform elements
of the interval `[-η,η]`, reduced modulo 8380417. -/
noncomputable def shortPolyLaw (s : Level) : PMF Poly :=
  PMF.pi fun _ => shortCoefficientLaw s

/-- The Dilithium short-vector law: every coefficient independently uniform in
`{-η,…,η}`, represented in the negacyclic ring modulo 8380417. -/
noncomputable def shortVectorLaw (s : Level) (rows : ℕ) : PMF (Fin rows → Poly) :=
  PMF.pi fun _ => shortPolyLaw s

/-- Sample every matrix coefficient independently by a uniform integer below the modulus. -/
def sampleMatrix (s : Level) : ProbComp (PublicMatrix s) :=
  replicateFin s.params.k (replicateFin s.params.ℓ (replicateFin 256 (ProbComp.unifFin 8380416)))

/-- Sampling the matrix coefficientwise gives the uniform matrix law. -/
@[simp] theorem eval_sampleMatrix (s : Level) :
    (sampleMatrix s).eval = PMF.uniformOfFintype (PublicMatrix s) := by
  change ProbComp.eval (replicateFin s.params.k (replicateFin s.params.ℓ
    (replicateFin 256 (ProbComp.unifFin 8380416)))) =
    PMF.uniformOfFintype (Fin s.params.k → Fin s.params.ℓ → Fin 256 → Fin (8380416 + 1))
  simp only [ProbComp.eval_replicateFin, ProbComp.eval_unifFin, PMF.pi_uniformOfFintype]

/-- The post-key computation sees the published seed, the matrix, the full vector for
rounding and the matrix-oracle cache left by key generation. Its verification algorithm and optional
digest-oracle state are supplied by the client. -/
abbrev Observable (s : Level) := FixedBytes 32 → PublicMatrix s → (Fin s.params.k → Poly) →
  List (FixedBytes 32 × PublicMatrix s) → Game

/-- Use a matrix query to generate the key and continue with the resulting oracle cache. -/
private noncomputable def withVector (s : Level) (observe : Observable s)
    (vector : PublicMatrix s → Fin s.params.k → Poly) : Game := do
  let rho ← PMF.uniformOfFintype (FixedBytes 32)
  let (A, cache) ← memoize (fun _ => PMF.uniformOfFintype (PublicMatrix s)) rho []
  observe rho A (vector A) cache

/-- The key generator samples its short secret and error, obtains its matrix through the
public seed oracle and passes the populated cache to the supplied post-key computation. -/
noncomputable def realKeyGame (s : Level) (observe : Observable s) : Game := do
  let s₁ ← shortVectorLaw s s.params.ℓ
  let s₂ ← shortVectorLaw s s.params.k
  withVector s observe fun A => moduleSISMap A s₁ + s₂

/-- Given the full challenger instance, sample a fresh seed and plant its matrix as the first
cache entry. All later oracle and verification operations belong to the same observable. -/
@[expose] noncomputable def planted (s : Level) (observe : Observable s) (A : PublicMatrix s)
    (t : Fin s.params.k → Poly) : Game := do
  let rho ← PMF.uniformOfFintype (FixedBytes 32)
  observe rho A t [(rho, A)]

private theorem withVector_eq (s : Level) (observe : Observable s)
    (vector : PublicMatrix s → Fin s.params.k → Poly) :
    withVector s observe vector = (PMF.uniformOfFintype (PublicMatrix s)).bind fun A =>
      planted s observe A (vector A) := by
  simp only [withVector, planted, memoize_of_none _ _ [] rfl, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]
  exact PMF.bind_comm _ _ _

/-- The post-key computation runs in the real Module-LWE experiment whenever the supplied
program realizes its behavior at a planted seed. The seed and short-vector sampling laws
and the initial matrix lookup are discharged here for every such program. -/
theorem realKeyGame_eq_realGame_of_planted (s : Level) (observe : Observable s)
    (D : PublicMatrix s → (Fin s.params.k → Poly) → ProbComp Bool)
    (h : ∀ A t, planted s observe A t = (D A t).eval) :
    realKeyGame s observe = ModuleLWE.realGame (shortVectorLaw s s.params.ℓ)
      (shortVectorLaw s s.params.k) D := by
  simp only [realKeyGame, withVector_eq, h, ModuleLWE.realGame, ModuleLWE.eval_realExperiment,
    PMF.monad_bind_eq_bind]
  rfl

end Cslib.Crypto.MLDSA.FIPS204.MatrixOracle
