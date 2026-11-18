/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.CompressedKeyOnly
public import CslibFrontier.Crypto.Primitives.ByteString
public import CslibFrontier.Crypto.Primitives.Hash.Keccak.SHAKE128
public import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Crypto.Game.Order
import Mathlib.Order.Interval.Finset.Fin

/-!
# ML-DSA verification on byte keys and signatures

[FIPS 204][NISTFIPS204], Algorithms 3, 6 and 8, with the Appendix C output limits for SHAKE
rejection sampling. Verification distinguishes a malformed signature (`some false`) from XOF
exhaustion (`none`). The signing digest and the challenge polynomial have distinct types.
The ring products use the coefficient form of Algorithm 8, line 9.

The key-only reduction retains the matrix seed and the verifier's SHAKE-derived message
representative. Its setup samples the Algorithm 6 key-generation seed. The resulting
self-target experiment has that same seeded setup.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204

open Cslib.Probability

/-- The parameter choices from FIPS 204, Table 1. -/
inductive Level where
  | mlDSA44 | mlDSA65 | mlDSA87
deriving DecidableEq

/-- Ring and shortness parameters for the selected standard parameter set. -/
abbrev Level.params (s : Level) : Params :=
  let p := match s with
    | .mlDSA44 => Params.mldsa44
    | .mlDSA65 => Params.mldsa65
    | .mlDSA87 => Params.mldsa87
  { p with n := 256, q := 8380417 }

private def digestBytes : Level → ℕ
  | .mlDSA44 => 32 | .mlDSA65 => 48 | .mlDSA87 => 64

private def hintLimit : Level → ℕ
  | .mlDSA44 => 80 | .mlDSA65 => 55 | .mlDSA87 => 75

/-- A coefficient polynomial in the FIPS 204 negacyclic ring. -/
abbrev Poly := Fin 256 → ZMod 8380417

/-- The coefficient representation of the public module matrix for the selected parameter set. -/
abbrev PublicMatrix (s : Level) := Matrix (Fin s.params.k) (Fin s.params.ℓ) Poly

private def packCoeffs {rows : ℕ} (width : ℕ) (coeff : Fin rows → Fin 256 → ℕ) : List Byte :=
  let bits := (List.finRange rows).flatMap fun i =>
    (List.finRange 256).flatMap fun j => BitString.lowBits width (coeff i j)
  (bits.toChunks 8).map Keccak.bitsToByteLE

private def unpackCoeff (bits : List Bool) (width index : ℕ) : ℕ :=
  BitString.lsbValue ((bits.drop (width * index)).take width)

private def uniformCoeffs : List Byte → List (ZMod 8380417)
  | a :: b :: c :: rest =>
    let x := a.val + 256 * b.val + 65536 * (c.val % 128)
    if x < 8380417 then (x : ZMod 8380417) :: uniformCoeffs rest else uniformCoeffs rest
  | _ => []

private def asPoly (coeffs : List (ZMod 8380417)) : Option Poly :=
  let a := coeffs.toArray
  if a.size < 256 then none else some (fun j => a[j.val]!)

/-- The coefficient of degree `j` in the inverse NTT, using the evaluation points
`ζ^(2 BitRev8(i)+1)` (FIPS 204 §2.5, equation (2.1)). The inverse of 256 modulo q is 8347681. -/
private def fromNTT (values : Poly) : Vector (ZMod 8380417) 256 :=
  let roots := Vector.ofFn fun a : Fin 512 => (1753 : ZMod 8380417) ^ a.val
  let inversePowers := Vector.ofFn fun i : Fin 256 =>
    511 - 2 * BitString.lsbValue (BitString.lowBits 8 i.val).reverse
  Vector.ofFn fun j : Fin 256 =>
    8347681 * ∑ i, values i * roots.get (Fin.ofNat 512 (inversePowers.get i * j.val))

private def tabulate {α : Type} (n : ℕ) (f : Fin n → Option α) : Option (Fin n → α) :=
  (fun v : Vector α n => v.get) <$> Vector.ofFnM f

/-- Algorithms 30 and 32, returning the matrix in coefficient representation. Each SHAKE128
stream absorbs `ρ || column || row` and may consume 894 bytes (Appendix C, Table 3). -/
def expandA (s : Level) (rho : List Byte) :
    Option (PublicMatrix s) := do
  let matrix ← Vector.ofFnM fun row : Fin s.params.k =>
    Vector.ofFnM fun col : Fin s.params.ℓ =>
      fromNTT <$> asPoly (uniformCoeffs (Keccak.shake128
        (rho ++ [Fin.ofNat 256 col.val, Fin.ofNat 256 row.val]) 894))
  return fun i j => ((matrix.get i).get j).get

private def boundedCoeff (η halfByte : ℕ) : Option (ZMod 8380417) :=
  if η = 2 then
    if halfByte < 15 then some ((2 : ZMod 8380417) - ↑(halfByte % 5)) else none
  else if halfByte < 9 then some (4 - (halfByte : ZMod 8380417)) else none

private def secretPoly (s : Level) (seed : List Byte) (nonce : ℕ) : Option Poly :=
  let bytes := Keccak.shake256 (seed ++ [Fin.ofNat 256 nonce, Fin.ofNat 256 (nonce / 256)]) 481
  asPoly (bytes.flatMap fun b =>
    ([b.val % 16, b.val / 16].filterMap (boundedCoeff s.params.η)))

/-- Public-key bytes of Algorithm 6, lines 6–8: concatenate the matrix seed and the ten
high bits of each coefficient of the full public vector, in row and coefficient order. -/
def encodePublic (s : Level) (rho : List Byte) (t : Fin s.params.k → Poly) : List Byte :=
  rho ++ packCoeffs 10 (fun i j => (power2Round 8380417 13 (t i j)).1.toNat)

/-- The seed used to expand the matrix can be read from the published bytes. -/
@[simp] theorem take_encodePublic (s : Level) (rho : FixedBytes 32) (t : Fin s.params.k → Poly) :
    (encodePublic s rho.toList t).take 32 = rho.toList := by
  simp [encodePublic]

/-- Algorithm 6, public-key output. The 32-byte seed expands into the matrix seed and the
secret-polynomial seed in a single SHAKE256 call. Rejection exhaustion yields `none`. -/
def keyGenPublic (s : Level) (seed : FixedBytes 32) : Option (List Byte) := do
  let expanded := Keccak.shake256
    (seed.toList ++ [Fin.ofNat 256 s.params.k, Fin.ofNat 256 s.params.ℓ]) 128
  let rho := expanded.take 32
  let rho' := (expanded.drop 32).take 64
  let matrix ← expandA s rho
  let s₁ ← tabulate _ fun i : Fin s.params.ℓ => secretPoly s rho' i.val
  let s₂ ← tabulate _ fun i : Fin s.params.k => secretPoly s rho' (s.params.ℓ + i.val)
  let t := moduleSISMap matrix s₁ + s₂
  return encodePublic s rho t

private def swaps (first count : ℕ) (bytes : List Byte) :
    Option (Equiv.Perm (Fin 256)) :=
  match count with
  | 0 => some (Equiv.refl _)
  | count + 1 => do
    let choices := bytes.dropWhile (fun b => decide (first < b.val))
    let b ← choices.head?
    let rest ← swaps (first + 1) count (choices.drop 1)
    return (Equiv.swap (Fin.ofNat 256 first) b).trans rest

private def signedTail (s : Level) (signs : List Bool) (i : Fin 256) : ZMod 8380417 :=
  if i.val < 256 - s.params.τ then 0
  else if signs[i.val - (256 - s.params.τ)]! then -1 else 1

/-- Algorithm 29. Preload the last τ positions with the SHAKE sign bits and exchange each
with its chosen position in increasing order. Future sign positions remain untouched because an
accepted index is at most the current position. The SHAKE256 limit is 221 bytes. -/
def sampleInBall (s : Level) (digest : List Byte) : Option Poly := do
  let bytes := Keccak.shake256 digest 221
  let e ← swaps (256 - s.params.τ) s.params.τ (bytes.drop 8)
  return signedTail s (Keccak.bytesToBitsLE (bytes.take 8)) ∘ e.symm

private theorem inBall_signedTail (s : Level) (signs : List Bool) (e : Equiv.Perm (Fin 256)) :
    InBall s.params.τ (signedTail s signs ∘ e.symm) := by
  constructor
  · intro i
    by_cases hi : (e.symm i).val < 256 - s.params.τ
    · simp [Function.comp_apply, signedTail, hi]
    · by_cases hsign : signs[(e.symm i).val - (256 - s.params.τ)]! = true
      · simp only [Function.comp_apply, signedTail, hi, hsign, ↓reduceIte]
        decide
      · simp only [Function.comp_apply, signedTail, hi, hsign, ↓reduceIte]
        decide
  · let start : Fin 256 := ⟨256 - s.params.τ, by cases s <;> decide⟩
    have hs : (Finset.univ.filter fun i => (signedTail s signs ∘ e.symm) i ≠ 0) =
        (Finset.Ici start).map e.toEmbedding := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply,
        signedTail, Finset.mem_map_equiv, Finset.mem_Ici]
      by_cases hi : (e.symm i).val < 256 - s.params.τ
      · simp [hi, start, Fin.le_def, Nat.not_le_of_gt hi]
      · simp only [hi, ↓reduceIte, start, Fin.le_def, Nat.le_of_not_gt hi]
        by_cases hsign : signs[(e.symm i).val - (256 - s.params.τ)]! = true <;>
          simp only [hsign, ↓reduceIte, iff_true] <;> decide
    rw [hs, Finset.card_map, Fin.card_Ici]
    cases s <;> rfl

/-- Every successful FIPS expansion gives exactly τ signed unit coefficients. -/
theorem inBall_of_sampleInBall {s : Level} {digest : List Byte} {c : Poly}
    (h : sampleInBall s digest = some c) : InBall s.params.τ c := by
  cases he : swaps (256 - s.params.τ) s.params.τ ((Keccak.shake256 digest 221).drop 8) with
  | none => simp [sampleInBall, he] at h
  | some e =>
    rw [sampleInBall, he] at h
    exact (Option.some.inj h) ▸ inBall_signedTail s _ e

/-- The components of a FIPS 204 signature after Algorithm 27 has checked its encoding. -/
structure Signature (s : Level) where
  /-- The complete λ/4-byte commitment hash. -/
  digest : List Byte
  /-- The response polynomials decoded from their signed range. -/
  z : Fin s.params.ℓ → Poly
  /-- The decoded hint bits. -/
  h : Fin s.params.k → Fin 256 → Bool

private def unpackHint (s : Level) (bytes : List Byte) :
    Option (Fin s.params.k → Fin 256 → Bool) := do
  let ω := hintLimit s
  let ends := bytes.drop ω
  let bound := fun i : ℕ => (ends[i]?.getD 0).val
  let start := fun i : ℕ => if i = 0 then 0 else bound (i - 1)
  let indices := fun i : ℕ => (bytes.drop (start i)).take (bound i - start i)
  guard ((List.range s.params.k).all fun i =>
    decide (start i ≤ bound i ∧ bound i ≤ ω ∧ (indices i).Pairwise (· < ·)))
  guard (((bytes.take ω).drop (bound (s.params.k - 1))).all (· == 0))
  return fun i j => (indices i.val).contains j

/-- Algorithm 27, including the prescribed total length, increasing hint indices within each
row, monotone row ends, the hint-weight bound, and zero padding (Algorithm 21). -/
def sigDecode (s : Level) (bytes : List Byte) : Option (Signature s) := do
  let width := s.params.γ₁.log2 + 1
  let hintOffset := digestBytes s + 32 * width * s.params.ℓ
  guard (bytes.length == hintOffset + hintLimit s + s.params.k)
  let hints ← unpackHint s (bytes.drop hintOffset)
  let bits := Keccak.bytesToBitsLE (bytes.drop (digestBytes s))
  let response := Vector.ofFn fun i : Fin s.params.ℓ => Vector.ofFn fun j : Fin 256 =>
    (s.params.γ₁ : ZMod 8380417) - ↑(unpackCoeff bits width (256 * i.val + j.val))
  return ⟨bytes.take (digestBytes s), fun i => (response.get i).get, hints⟩

private def decodeRounded (s : Level) (bytes : List Byte) (i : Fin s.params.k) (j : Fin 256) :
    Fin 1024 :=
  Fin.ofNat 1024 (unpackCoeff (Keccak.bytesToBitsLE (bytes.drop 32)) 10 (256 * i.val + j.val))

private def publicKey (s : Level) (bytes : List Byte)
    (matrix : PublicMatrix s) : MLDSA.PublicKey s.params :=
  let t := Vector.ofFn fun i : Fin s.params.k => Vector.ofFn fun j : Fin 256 =>
    ((decodeRounded s bytes i j).val : ZMod 8380417) * 8192
  ⟨matrix, fun i j => t[i.val][j.val]⟩

/-- A decoded public coefficient lies in [0,1023]. Multiplication by 2^13 preserves the
canonical lift, so rounding this lifted key recovers exactly Algorithm 8's public term. -/
private theorem highTerm_publicKey (s : Level) (bytes : List Byte) (matrix) :
    publicKeyHighTerm s.params 13 (publicKey s bytes matrix) =
      (publicKey s bytes matrix).t := by
  funext i j
  have coef (v : Fin 1024) :
      (((power2Round 8380417 13 ((v.val : ZMod 8380417) * 8192)).1 *
        (2 ^ (13 : ℕ) : ℕ) : ℤ) : ZMod 8380417) = (v.val : ZMod 8380417) * 8192 := by
    have hv : v.val * 8192 < 8380417 := by have := v.isLt; lia
    have hval : (((v.val : ZMod 8380417) * 8192)).val = v.val * 8192 := by
      have hcast : ((v.val * 8192 : ℕ) : ZMod 8380417) = (v.val : ZMod 8380417) * 8192 := by
        norm_num
      rw [← hcast, ZMod.val_natCast, Nat.mod_eq_of_lt hv]
    have hrem : ((((v.val * 8192 : ℕ) : ℤ) : ZMod (2 ^ 13))).valMinAbs = 0 := by
      have hz : (8192 : ZMod (2 ^ 13)) = 0 := by decide
      push_cast
      rw [hz, mul_zero, ZMod.valMinAbs_zero]
    simp only [power2Round, hval, hrem, sub_zero]
    push_cast
    norm_num
  simp only [publicKey, publicKeyHighTerm, power2RoundVec, Vector.getElem_ofFn]
  exact coef (decodeRounded s bytes i j)

/-- SHAKE256 on `BytesToBits(H(pk,64)) || M'`. In particular a formatted message may end
between two byte boundaries (Algorithm 8, lines 6–7). -/
def messageRepresentative (pk : List Byte) (formatted : List Bool) : List Bool :=
  Keccak.bytesToBitsLE (Keccak.bitSponge Keccak.shake256Layout [true, true, true, true]
    (Keccak.bytesToBitsLE (Keccak.shake256 pk 64) ++ formatted) 64)

private def commitmentDigest (s : Level) (w : Fin s.params.k → Fin 256 → ℤ) (μ : List Bool) :
    List Byte :=
  let width := ((s.params.q - 1) / (2 * s.params.γ₂) - 1).log2 + 1
  let packed := packCoeffs width (fun i j => (w i j).toNat)
  Keccak.bitSponge Keccak.shake256Layout [true, true, true, true]
    (μ ++ Keccak.bytesToBitsLE packed) (digestBytes s)

private def hintedCommitment (s : Level) (pk : MLDSA.PublicKey s.params)
    (σ : Signature s) (c : Poly) : Fin s.params.k → Fin 256 → ℤ :=
  fun i => useHintVec s.params.q s.params.γ₂ (σ.h i)
    (moduleSISMap pk.A σ.z i - negacyclicMul c (pk.t i))

/-- Algorithm 8 after successful parsing and expansion. The digest from the signature must match
the full SHAKE output byte for byte. -/
private def check (s : Level) (pk : MLDSA.PublicKey s.params) (μ : List Bool)
    (σ : Signature s) (c : Poly) : Bool :=
  decide (ResponseShort s.params σ.z) &&
    decide (commitmentDigest s (hintedCommitment s pk σ c) μ = σ.digest)

private def verifyInternalWith (s : Level) (expand : List Byte → Option (PublicMatrix s))
    (pk : List Byte) (formatted : List Bool) (signature : List Byte) :
    Option Bool := do
  if pk.length != 32 + 320 * s.params.k then return false
  let some σ := sigDecode s signature | return false
  let matrix ← expand (pk.take 32)
  let c ← sampleInBall s σ.digest
  return check s (publicKey s pk matrix) (messageRepresentative pk formatted) σ c

/-- Algorithm 8 for a formatted message. Invalid encodings return `some false`, and the
uniform Appendix C error for an exhausted SHAKE rejection stream is `none`. -/
def verifyInternal (s : Level) := verifyInternalWith s (expandA s)

/-- Algorithm 3 with the public matrix expansion supplied at its call site. The context and
signature checks, message hashing, challenge expansion, and full digest comparison are shared
with the concrete verifier. -/
def verifyWithExpansion (s : Level) (expand : List Byte → Option (PublicMatrix s))
    (pk : List Byte) (message : List Bool) (ctx signature : List Byte) : Option Bool := do
  guard (ctx.length ≤ 255)
  let formatted := Keccak.bytesToBitsLE (0 :: Fin.ofNat 256 ctx.length :: ctx) ++ message
  verifyInternalWith s expand pk formatted signature

/-- On freshly encoded public bytes, the verifier reads exactly the published seed. Once its
matrix has been obtained from the shared oracle it can be reused in the digest check. -/
theorem verifyWithExpansion_encodePublic (s : Level) (expand : List Byte → Option (PublicMatrix s))
    (rho : FixedBytes 32) (t : Fin s.params.k → Poly) (A : PublicMatrix s)
    (hA : expand rho.toList = some A) (msg : List Bool) (ctx sig : List Byte) :
    verifyWithExpansion s expand (encodePublic s rho.toList t) msg ctx sig =
      verifyWithExpansion s (fun _ => some A) (encodePublic s rho.toList t) msg ctx sig := by
  simp only [verifyWithExpansion, verifyInternalWith, take_encodePublic, hA]

/-- Pure ML-DSA verification (Algorithm 3): format the context and the bit-string message,
then run Algorithm 8. Contexts longer than 255 bytes return the specified error. -/
def verify (s : Level) := verifyWithExpansion s (expandA s)

private def algebraicHash (s : Level) : Hash s.params :=
  fun ⟨w, μ⟩ => (sampleInBall s (commitmentDigest s w μ)).getD 0

private theorem compressedVerify_of_check {s : Level} {bytes : List Byte} {matrix}
    {μ : List Bool} {σ : Signature s} {c : Poly} (hc : sampleInBall s σ.digest = some c)
    (hv : check s (publicKey s bytes matrix) μ σ c) :
    compressedVerify s.params 13 (algebraicHash s) (publicKey s bytes matrix) μ ⟨σ.z, σ.h, c⟩ := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hv
  simp only [compressedVerify, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨hv.1, inBall_of_sampleInBall hc⟩, ?_⟩
  change (sampleInBall s (commitmentDigest s _ μ)).getD 0 = c
  simp only [compressedVerifierCommitment, highTerm_publicKey, Pi.sub_apply]
  change (sampleInBall s (commitmentDigest s
    (hintedCommitment s (publicKey s bytes matrix) σ c) μ)).getD 0 = c
  rw [hv.2, hc]
  rfl

/-- The byte-level forger chooses the context, message, and signature after seeing only the
published key. -/
structure Forgery where
  /-- External context of at most 255 bytes for an accepted forgery. -/
  context : List Byte
  /-- Original bit-string message. -/
  message : List Bool
  /-- Byte encoding of the purported signature. -/
  signature : List Byte

private def formattedMessage (f : Forgery) : List Bool :=
  Keccak.bytesToBitsLE (0 :: Fin.ofNat 256 f.context.length :: f.context) ++ f.message

private def candidate (s : Level) (pk : MLDSA.PublicKey s.params) (μ : List Bool)
    (σ : Signature s) (c : Poly) : SelfTargetCandidate s.params :=
  SelfTargetCandidate.ofCompressedForgery s.params 13 pk μ ⟨σ.z, σ.h, c⟩

/-- For each fixed published byte key, the solver parses the forgery and extracts a self-target
candidate. The hash input contains its actual public-key-bound message representative. -/
def extract (s : Level) (bytes : List Byte)
    (matrix : PublicMatrix s)
    (f : Forgery) : Option (SelfTargetCandidate s.params) := do
  let σ ← sigDecode s f.signature
  let c ← sampleInBall s σ.digest
  return candidate s (publicKey s bytes matrix)
    (messageRepresentative bytes (formattedMessage f)) σ c

/-- Self-target acceptance for a solver on a published byte key. The experiment constructs its
own challenge matrix from that key's seed and rounded coefficients. -/
def solves (s : Level) (bytes : List Byte)
    (solver : PublicMatrix s →
      Option (SelfTargetCandidate s.params)) : Bool :=
  (do
    let matrix ← expandA s (bytes.take 32)
    let sol ← solver matrix
    return decide (IsSelfTargetSolution s.params (selfTargetHash s.params (algebraicHash s))
      (compressedSelfTargetRadius s.params 13) (publicKey s bytes matrix) sol)).getD false

/-- Acceptance by the FIPS byte verifier implies self-target acceptance for the extracted
candidate on the same published key, including its matrix seed. -/
theorem solves_extract_of_verify {s : Level} {bytes : List Byte} {f : Forgery}
    (hv : verify s bytes f.message f.context f.signature = some true) :
    solves s bytes (fun matrix => extract s bytes matrix f) = true := by
  simp only [verify, verifyWithExpansion, verifyInternalWith] at hv
  have hctx : f.context.length ≤ 255 := by
    by_contra h
    simp [guard, h] at hv
  have hlen : bytes.length = 32 + 320 * s.params.k := by
    by_contra h
    simp [guard, hctx, h] at hv
  cases hσ : sigDecode s f.signature with
  | none => simp [guard, hctx, hlen, hσ] at hv
  | some σ =>
    cases hmatrix : expandA s (bytes.take 32) with
    | none => simp [guard, hctx, hlen, hσ, hmatrix] at hv
    | some matrix =>
      cases hc : sampleInBall s σ.digest with
      | none => simp [guard, hctx, hlen, hσ, hmatrix, hc] at hv
      | some c =>
        have hcheck : check s (publicKey s bytes matrix)
            (messageRepresentative bytes (formattedMessage f)) σ c := by
          simpa [guard, hctx, hlen, hσ, hmatrix, hc,
            formattedMessage] using hv
        have hvalid : s.params.Valid := by
          cases s
          · exact Params.valid_mldsa44
          · exact Params.valid_mldsa65
          · exact Params.valid_mldsa87
        have hs := isSelfTargetSolution_of_compressedVerify hvalid
          (by cases s <;> decide : 4 * s.params.γ₂ < s.params.q) (by decide : 0 < 13)
          (compressedVerify_of_check hc hcheck)
        simpa [solves, hmatrix, extract, hσ, hc, candidate, formattedMessage] using hs

/-- Run the supplied byte-key forger after generating the published key from a uniform 32-byte
seed, treating a key-generation failure as an unsuccessful trial. -/
private noncomputable def withForgery (s : Level) (adv : List Byte → ProbComp Forgery)
    (wins : List Byte → Forgery → Bool) : Game :=
  (PMF.uniformOfFintype (FixedBytes 32)).bind fun seed =>
    match keyGenPublic s seed with
    | none => PMF.pure false
    | some pk => (adv pk).eval.map (wins pk)

/-- FIPS 204 key-only forgery: draw the uniform key-generation seed, give the generated
public-key bytes to the adversary, and run Algorithm 3 on its context, message and signature. -/
noncomputable def keyOnlyGame (s : Level) (adv : List Byte → ProbComp Forgery) : Game :=
  withForgery s adv fun pk f => (verify s pk f.message f.context f.signature).getD false

/-- Self-target success for the solver extracted from the byte-key forger, on the seeded
matrix and lifted public vector that the verifier can compute from the published key. -/
noncomputable def extractedSelfTargetGame (s : Level) (adv : List Byte → ProbComp Forgery) : Game :=
  withForgery s adv fun pk f => solves s pk fun matrix => extract s pk matrix f

/-- The finite success bound under the Algorithm 6 seed law and Algorithm 3 verification.
The right-hand game tests the actual extracted candidate under that same seeded public key.
Replacing this seeded target by standard uniform-matrix hardness is a separate reduction. -/
theorem succProbability_verify_le_seededSelfTarget (s : Level)
    (adv : List Byte → ProbComp Forgery) :
    (keyOnlyGame s adv).succProbability ≤ (extractedSelfTargetGame s adv).succProbability := by
  apply Game.succProbability_mono
  unfold keyOnlyGame extractedSelfTargetGame withForgery
  apply Probability.PMF.bind_apply_mono_on_support
  intro seed _
  cases hk : keyGenPublic s seed with
  | none => exact le_rfl
  | some pk =>
    simp only [PMF.map]
    apply Probability.PMF.bind_apply_mono_on_support
    intro f _
    cases hv : verify s pk f.message f.context f.signature with
    | none => simp [hv]
    | some b =>
      cases b
      · simp [hv]
      · simp [hv, solves_extract_of_verify hv]

end Cslib.Crypto.MLDSA.FIPS204
