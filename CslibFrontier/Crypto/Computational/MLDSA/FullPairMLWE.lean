/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.SecretExpansionLaw
public import CslibFrontier.Crypto.Computational.MLDSA.PublicPairSigning
-- Reads private `vectors`, `uniform_vector_pair`, and `uniformPrefixes_secretRows`.
import all CslibFrontier.Crypto.Computational.MLDSA.SecretExpansionLaw
import CslibFrontier.Crypto.Computational.MLDSA.RandomXofMatrix
import CslibFrontier.Probability.PMF.Bool

/-!
# The short-secret key switch after separating FIPS secret expansion

The private view of Algorithm 6 takes its 66-byte secret-expansion inputs from a separate
SHAKE256 stream. The public-pair signer and its quantum forger keep the ambient streams.
The reduction installs the decision-MLWE matrix at the public FIPS seed before running them.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204
open Cslib.Probability

/-- Private key-generation view with the 66-byte (528-bit) inputs of Algorithm 33 supplied by
`secret`. Algorithm 6's 34-byte seed-expansion input and its public-key hash still use `H`.

Caution: this splitter routes solely by bit length (`x.length = 528`). It is safe only for key
generation (`fullPairExperiment`); do not apply it to signing or verification, where pure-mode
`representativeInput tr (formatMessage [] [])` (for 64-byte `tr`) and Algorithm 34's
`Xofs.expandMask` (`ExpandMask`) queries are also 66 bytes (528 bits). -/
def Xofs.withExpandSStream (H secret : Xofs) : Xofs :=
  {H with h256 := {
    read x n := if x.length = 528 then secret.h256.read x n else H.h256.read x n
    length_read x n := by split <;> exact ExtendableOutput.length_read _ _ _
    take_read x m n h := by
      by_cases same : x.length = 528 <;> simp only [same, ↓reduceIte]
      · exact secret.h256.take_read x h
      · exact H.h256.take_read x h }}

private theorem seed_keep (H G : Xofs) (s : Level) (seed : FixedBytes 32) :
    (H.withExpandSStream G).expandKeySeed s seed = H.expandKeySeed s seed := by
  simp [Xofs.expandKeySeed, Xofs.withExpandSStream, length_keySeedInput]

private theorem separate_secret (H G : Xofs) (s : Level) (rho : List Byte) (hr : rho.length = 64) :
    (H.withExpandSStream G).expandS s rho = G.expandS s rho := by
  obtain ⟨r, rfl⟩ := FixedBytes.exists_toList hr
  have agree (i : ℕ) :
      (H.withExpandSStream G).secretPoly s r.toList i = G.secretPoly s r.toList i := by
    simp only [Xofs.secretPoly, ExtendableOutput.readBytes, Xofs.withExpandSStream,
      length_nonceInput_bits, ↓reduceIte]
  simp only [Xofs.expandS, agree]

private abbrev PostKey (s : Level) := Xofs → FixedBytes 32 → MLDSA.PublicKey s.params → Game

private noncomputable def observePair {s : Level} (matrix : Option (PublicMatrix s))
    (vectors : Option ((Fin s.params.ℓ → Poly) × (Fin s.params.k → Poly)))
    (run : MLDSA.PublicKey s.params → Game) : Game :=
  ((do let A ← matrix
       let (x, e) ← vectors
       return run ⟨A, ModuleLWE.sample A x e⟩) : Option Game).getD (PMF.pure false)

private noncomputable def idealShortPair {s : Level} (matrix : Option (PublicMatrix s))
    (run : MLDSA.PublicKey s.params → Game) : Game :=
  (MatrixOracle.shortVectorLaw s s.params.ℓ).bind fun x =>
    (MatrixOracle.shortVectorLaw s s.params.k).bind fun e =>
      observePair matrix (some (x, e)) run

/-- Run the given game when Algorithm 33 succeeds on fresh 481-byte rows for both short
vectors. This reproduces secret expansion's finite rejection cap in the pair test. -/
noncomputable def withSecretExpansionSuccess (s : Level) (g : Game) : Game :=
  (PMF.uniformOfFintype (Fin s.params.ℓ → FixedBytes 481)).bind fun x =>
    (PMF.uniformOfFintype (Fin s.params.k → FixedBytes 481)).bind fun y =>
      if (vectors s (x, y)).isSome then g else PMF.pure false

/-- Dropping an independent secret-expansion failure can only increase a game's success. -/
theorem withSecretExpansionSuccess_le (s : Level) (g : Game) :
    withSecretExpansionSuccess s g true ≤ g true := by
  unfold withSecretExpansionSuccess
  apply PMF.bind_apply_le_on_support
  intro x _
  apply PMF.bind_apply_le_on_support
  intro y _
  split_ifs <;> simp [PMF.pure_apply]

private theorem bind_secretSuccess {α : Type} (p : PMF α) (s : Level) (g : α → Game) :
    (p.bind fun v => withSecretExpansionSuccess s (g v)) =
      withSecretExpansionSuccess s (p.bind g) := by
  unfold withSecretExpansionSuccess
  let X := PMF.uniformOfFintype (Fin s.params.ℓ → FixedBytes 481)
  let Y := PMF.uniformOfFintype (Fin s.params.k → FixedBytes 481)
  rw [PMF.bind_comm p X]
  apply congrArg (PMF.bind X ·)
  funext x
  rw [PMF.bind_comm p Y]
  apply congrArg (PMF.bind Y ·)
  funext y
  split_ifs <;> simp

private theorem expandS_observe_eq (s : Level) (base : Xofs) (rho : List Byte)
    (hr : rho.length = 64) {a b : ℕ} (ha : 528 ≤ a) (hb : 481 ≤ b)
    (matrix : Option (PublicMatrix s)) (run : MLDSA.PublicKey s.params → Game) :
    ((base.uniformPrefixes a b).bind fun G => observePair matrix (G.expandS s rho) run) =
      withSecretExpansionSuccess s (idealShortPair matrix run) := by
  obtain ⟨r, rfl⟩ := FixedBytes.exists_toList hr
  let use v := observePair matrix v run
  have rows := (uniformPrefixes_secretRows base s r ha hb).trans (uniform_vector_pair s)
  have eq := congrArg (PMF.bind · use) rows
  simp only [PMF.bind_map, Function.comp_def, PMF.bind_bind] at eq
  apply eq.trans
  unfold withSecretExpansionSuccess
  congr 1
  funext x
  congr 1
  funext y
  let ok := (vectors s (x, y)).isSome
  change ((if ok then (MatrixOracle.shortVectorLaw s s.params.ℓ).bind fun x =>
    (MatrixOracle.shortVectorLaw s s.params.k).map fun e => some (x, e)
    else PMF.pure none).bind use) = if ok then idealShortPair matrix run else PMF.pure false
  split_ifs
  · simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def, idealShortPair, use]
  · rw [PMF.pure_bind]
    cases matrix <;> rfl

/-- Fresh-digest success with native key generation using an independent secret-expansion stream.
The public-pair signer and the quantum forger share the ambient XOFs. -/
@[expose] noncomputable def QuantumSigningForger.independentExpandSGame (C : QuantumSigningForger)
    (s : Level) (base : Xofs) (a b : ℕ) : Game :=
  (base.uniformPrefixes a b).bind fun H => (base.uniformPrefixes a b).bind fun G =>
    (H.withExpandSStream G).fullPairExperiment s fun rho pk =>
      (C.publicPairSigning s H rho pk).map (·.trial.newDigestWin)

private noncomputable def matrixGame {s : Level} (H : Xofs) (seed : FixedBytes 32)
    (run : PostKey s) : Game :=
  let rho := (H.expandKeySeed s seed).take 32
  idealShortPair (H.expandA s rho) (run H (fun j => rho[j.val]!))

private theorem source_eq_matrixGame (C : QuantumSigningForger) {s : Level} (base : Xofs) {a b : ℕ}
    (ha : 528 ≤ a) (hb : 481 ≤ b) :
    let run := fun H rho pk => (C.publicPairSigning s H rho pk).map (·.trial.newDigestWin)
    C.independentExpandSGame s base a b = withSecretExpansionSuccess s
      ((base.uniformPrefixes a b).bind fun H =>
        (PMF.uniformOfFintype (FixedBytes 32)).bind fun seed => matrixGame H seed run) := by
  intro run
  unfold QuantumSigningForger.independentExpandSGame
  rw [← bind_secretSuccess]
  apply congrArg (PMF.bind (base.uniformPrefixes a b) ·)
  funext H
  simp_rw [Xofs.fullPairExperiment_eq_expand, seed_keep]
  rw [PMF.bind_comm, ← bind_secretSuccess]
  apply congrArg (PMF.bind (PMF.uniformOfFintype (FixedBytes 32)) ·)
  funext seed
  let ex := H.expandKeySeed s seed
  have hlen : ex.length = 128 := H.h256.length_read ..
  let rs := (ex.drop 32).take 64
  have hr : rs.length = 64 := by simp [rs, hlen]
  let A := H.expandA s (ex.take 32)
  let finish := run H (fun j => (ex.take 32)[j.val]!)
  change ((base.uniformPrefixes a b).bind fun G =>
    observePair A ((H.withExpandSStream G).expandS s rs) finish) = _
  simp_rw [separate_secret H _ s rs hr]
  exact expandS_observe_eq s base rs hr ha hb A finish

/-- Install a supplied lattice matrix at the public seed for an arbitrary subsequent computation
on the raw XOFs and the full pair. The original SHAKE128 rows decide matrix exhaustion. -/
@[expose] noncomputable def Xofs.withProgrammedMLWEPair {s : Level} (H : Xofs)
    (seed : FixedBytes 32) (run : Xofs → FixedBytes 32 → MLDSA.PublicKey s.params → Game)
    (pk : MLDSA.PublicKey s.params) : Game :=
  let rho := (H.expandKeySeed s seed).take 32
  (PMF.uniformOfFintype (MatrixPrefixes s)).bind fun rows =>
    if ((H.withMatrixPrefixes s rho rows).expandA s rho).isSome then
      run (H.withMatrixPrefixes s rho (programMatrixPrefixes s rows pk.A))
        (fun j => rho[j.val]!) pk
    else PMF.pure false

private theorem planted_real {s : Level} (H : Xofs) (seed : FixedBytes 32) (run : PostKey s) :
    let rho := (H.expandKeySeed s seed).take 32
    ((PMF.uniformOfFintype (MatrixPrefixes s)).bind fun t =>
      matrixGame (H.withMatrixPrefixes s rho t) seed run) =
      (MLDSA.keyLaw s.params (MatrixOracle.shortCoefficientLaw s)).bind
        (H.withProgrammedMLWEPair seed run) := by
  intro rho
  let U := PMF.uniformOfFintype (MatrixPrefixes s)
  let M := PMF.uniformOfFintype (PublicMatrix s)
  let S := MatrixOracle.shortVectorLaw s s.params.ℓ
  let E := MatrixOracle.shortVectorLaw s s.params.k
  let use (p : Xofs × Option (PublicMatrix s)) :=
    idealShortPair p.2 (run p.1 (fun j => rho[j.val]!))
  have eq := congrArg (PMF.bind · use) (uniform_expandA_programMatrixPrefixes H s rho)
  simp only [PMF.bind_map, Function.comp_def] at eq
  have hgame (t : MatrixPrefixes s) :
      matrixGame (H.withMatrixPrefixes s rho t) seed run =
        use (H.withMatrixPrefixes s rho t, (H.withMatrixPrefixes s rho t).expandA s rho) := by
    simp only [matrixGame, Xofs.expandKeySeed, Xofs.withMatrixPrefixes_h256, rho, use]
  simp_rw [hgame]
  apply eq.symm.trans
  rw [← PMF.uniformOfFintype_prod]
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
  simp only [MLDSA.keyLaw, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.bind_bind, PMF.pure_bind]
  let v (A : PublicMatrix s) (x : Fin s.params.ℓ → Poly) (e : Fin s.params.k → Poly) :
      MLDSA.PublicKey s.params := ⟨A, ModuleLWE.sample A x e⟩
  let g (A : PublicMatrix s) (t : MatrixPrefixes s) := H.withMatrixPrefixes s rho
    (programMatrixPrefixes s t A)
  let mat (t : MatrixPrefixes s) := (H.withMatrixPrefixes s rho t).expandA s rho
  change (U.bind fun t => M.bind fun A => S.bind fun x => E.bind fun e =>
    observePair ((mat t).map fun _ => A) (some (x, e)) (run (g A t) (fun j => rho[j.val]!))) =
    M.bind fun A => S.bind fun x => E.bind fun e => U.bind fun t =>
      if (mat t).isSome then run (g A t) (fun j => rho[j.val]!) (v A x e) else PMF.pure false
  rw [PMF.bind_comm U M]
  apply congrArg (PMF.bind M ·)
  funext A
  rw [PMF.bind_comm U S]
  apply congrArg (PMF.bind S ·)
  funext x
  rw [PMF.bind_comm U E]
  apply congrArg (PMF.bind E ·)
  funext e
  apply congrArg (PMF.bind U ·)
  funext t
  cases mat t <;> rfl

private theorem matrixGame_eq_real {s : Level} (base : Xofs) {a b : ℕ}
    (ha : 272 ≤ a) (hb : 894 ≤ b) (run : PostKey s) :
    ((base.uniformPrefixes a b).bind fun H => (PMF.uniformOfFintype (FixedBytes 32)).bind
      fun seed => matrixGame H seed run) =
      (MLDSA.keyLaw s.params (MatrixOracle.shortCoefficientLaw s)).bind
        (fun pk => (base.uniformPrefixes a b).bind fun H =>
          (PMF.uniformOfFintype (FixedBytes 32)).bind fun seed =>
            H.withProgrammedMLWEPair seed run pk) := by
  rw [← uniformPrefixes_resampleMatrix base s ha hb (fun H seed => matrixGame H seed run)]
  simp_rw [planted_real]
  let K := MLDSA.keyLaw s.params (MatrixOracle.shortCoefficientLaw s)
  let R := base.uniformPrefixes a b
  let U := PMF.uniformOfFintype (FixedBytes 32)
  change (R.bind fun H => U.bind fun seed => K.bind (H.withProgrammedMLWEPair seed run)) = _
  simp_rw [PMF.bind_comm U K]
  rw [PMF.bind_comm R K]

namespace QuantumSigningForger

/-- Test a supplied MLWE pair by installing its matrix in the public-seed SHAKE128 rows
and running the adaptive public-pair signer with that same pair. -/
@[expose] noncomputable def fullPairMLWETest (C : QuantumSigningForger) (s : Level)
    (base : Xofs) (a b : ℕ) (pk : MLDSA.PublicKey s.params) : Game :=
  withSecretExpansionSuccess s <| (base.uniformPrefixes a b).bind fun H =>
    (PMF.uniformOfFintype (FixedBytes 32)).bind fun seed =>
      H.withProgrammedMLWEPair seed (fun G rho pair =>
        (C.publicPairSigning s G rho pair).map (·.trial.newDigestWin)) pk

/-- The independent private-expansion game is the exact real branch of the constructed
short-secret decision-MLWE test. Both matrix and secret exhaustion are retained. -/
theorem independentExpandSGame_eq_mlwe (C : QuantumSigningForger) (s : Level) (base : Xofs)
    {a b : ℕ} (ha : 528 ≤ a) (hb : 894 ≤ b) :
    C.independentExpandSGame s base a b =
      (MLDSA.keyLaw s.params (MatrixOracle.shortCoefficientLaw s)).bind
        (C.fullPairMLWETest s base a b) := by
  rw [source_eq_matrixGame C base ha (by lia : 481 ≤ b),
    matrixGame_eq_real base (by lia : 272 ≤ a) hb, ← bind_secretSuccess]
  rfl

end QuantumSigningForger

end Cslib.Crypto.MLDSA.FIPS204
