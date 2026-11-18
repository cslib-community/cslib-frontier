/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.FIPS204
public import CslibFrontier.Crypto.Computational.MLDSA.ResponseBinding

/-!
# Binding of FIPS 204 signature bytes at a repeated challenge digest

When two distinct signatures on the same message and context pass FIPS 204 Algorithm 8
with the same challenge digest, their decoded responses differ. Distinct reconstructed
commitments give distinct SHAKE256 inputs with equal outputs. Equal reconstructed
commitments give the integer kernel witness of [BaiEtAl2021Dilithium], §6.2.2, equation (8).
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204

/-- For the same public key, context, message, and challenge digest, two distinct accepted
byte signatures yield either a SHAKE256 collision on the actual Algorithm 8 inputs or the
short, nonzero ordinary MSIS witness of Dilithium v3.1 §6.2.2, equation (8). -/
theorem digestCollision_or_isSolution_of_verifyWithExpansion {s : Level}
    {expand : List Byte → Option (PublicMatrix s)} {rho : FixedBytes 32}
    {A : PublicMatrix s} {t : Fin s.params.k → Poly} {f : Forgery} {other : List Byte}
    (hA : expand rho.toList = some A) (hne : f.signature ≠ other)
    (hd : f.signature.take (digestBytes s) = other.take (digestBytes s))
    (first : verifyWithExpansion s expand (encodePublic s rho.toList t)
      f.message f.context f.signature = some true)
    (second : verifyWithExpansion s expand (encodePublic s rho.toList t)
      f.message f.context other = some true) :
    ∃ a b c, sigDecode s f.signature = some a ∧ sigDecode s other = some b ∧
      sampleInBall s a.digest = some c ∧
      let x : CompressedSignature s.params := ⟨a.z, a.h, c⟩
      let y : CompressedSignature s.params := ⟨b.z, b.h, c⟩
      let pk : PublicKey s.params := ⟨A, t⟩
      let μ := messageRepresentative (encodePublic s rho.toList t) (formattedMessage f)
      ((commitmentInput s (x.recover 13 pk) μ ≠ commitmentInput s (y.recover 13 pk) μ ∧
        commitmentDigest s (x.recover 13 pk) μ = commitmentDigest s (y.recover 13 pk) μ) ∨
        ModuleSIS.IsSolution (ModuleSIS.hermiteMatrix A)
          (max (2 * (s.params.γ₁ - s.params.β)) (4 * s.params.γ₂ + 2))
          (responseDifference 13 pk x y)) := by
  obtain ⟨a, c, ha, hca, za, da⟩ := verifiedSignature_of_verifyWithExpansion (f := f) hA first
  obtain ⟨b, c', hb, hcb, zb, db⟩ := verifiedSignature_of_verifyWithExpansion
    (f := { f with signature := other }) hA second
  have sameDigest : a.digest = b.digest := (digest_of_sigDecode ha).symm.trans
    (hd.trans (digest_of_sigDecode hb))
  rw [← sameDigest, hca, Option.some.injEq] at hcb
  subst c'
  refine ⟨a, b, c, ha, hb, hca, ?_⟩
  intro x y pk μ
  have valid : s.params.Valid := by
    cases s
    · exact Params.valid_mldsa44
    · exact Params.valid_mldsa65
    · exact Params.valid_mldsa87
  have gap : 4 * s.params.γ₂ < s.params.q := by cases s <;> decide
  by_cases hw : x.recover 13 pk = y.recover 13 pk
  · right
    apply isSolution_responseDifference (σ := x) (σ' := y) valid gap 13 pk ?_ rfl hw za zb
    intro heq
    have hz : a.z = b.z := congrArg CompressedSignature.z heq
    have hh : a.h = b.h := congrArg CompressedSignature.h heq
    have hab : a = b := by cases a; cases b; congr
    exact hne (eq_of_sigDecode (hab ▸ ha) hb)
  · left
    have range (v : CompressedSignature s.params) (i : Fin s.params.k) (j : Fin 256) :
        0 ≤ v.recover 13 pk i j ∧
          v.recover 13 pk i j < (((s.params.q - 1) / (2 * s.params.γ₂) : ℕ) : ℤ) :=
      ⟨useHint_nonneg valid.γ₂_pos gap _ _, useHint_lt valid.γ₂_pos valid.two_mul_γ₂_dvd gap _ _⟩
    exact ⟨fun heq => hw (eq_of_commitmentInput_eq (range x) (range y) heq),
      da.trans (sameDigest.trans db.symm)⟩

end Cslib.Crypto.MLDSA.FIPS204
