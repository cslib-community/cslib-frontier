/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.FIPS204
public import CslibFrontier.Crypto.Computational.MLDSA.ResponseBinding
import all CslibFrontier.Crypto.Computational.MLDSA.FIPS204

/-!
# Binding of FIPS 204 signature bytes at a repeated challenge digest

Two accepted, distinct FIPS 204 triples with the same digest yield either a collision at
two raw SHAKE256 inputs or the short integer kernel witness of [BaiEtAl2021Dilithium],
§6.2.2, equation (8). The extractor decodes the public bytes and both signatures. It handles
different contexts and messages, including a collision in the 64-byte message representative.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204

/-- The two outputs of extraction at a repeated digest. -/
inductive RepeatedDigestWitness (s : Level) where
  /-- Two raw inputs to the same SHAKE256 oracle. -/
  | collision (first second : List Bool)
  /-- An integer vector for the systematic matrix of the public key. -/
  | msis (vector : Fin (s.params.k + s.params.ℓ) → Fin s.params.n → ℤ)

/-- Check a candidate against the shared SHAKE256 digest or the ordinary Hermite MSIS instance. -/
def RepeatedDigestWitness.Valid {s : Level} (H : Xofs) (A : PublicMatrix s) :
    RepeatedDigestWitness s → Prop
  | .collision a b => a ≠ b ∧ H.h256.read a (digestBytes s) = H.h256.read b (digestBytes s)
  | .msis v => ModuleSIS.IsSolution (ModuleSIS.hermiteMatrix A)
      (max (2 * (s.params.γ₁ - s.params.β)) (4 * s.params.γ₂ + 2)) v

/-- Extract from two byte triples with a repeated digest. All inputs are public, including the
matrix. It first checks for a collision in the message representative. If the commitment
addresses differ it returns them, and otherwise it subtracts the responses. -/
def Xofs.extractRepeatedDigest (H : Xofs) (s : Level) (bytes : List Byte) (A : PublicMatrix s)
    (f g : Forgery) : Option (RepeatedDigestWitness s) := do
  if formattedMessage f ≠ formattedMessage g ∧
      H.messageRepresentative bytes (formattedMessage f) =
        H.messageRepresentative bytes (formattedMessage g) then
    let tr := H.h256.readBytes bytes 64
    return .collision (representativeInput tr (formattedMessage f))
      (representativeInput tr (formattedMessage g))
  let a ← sigDecode s f.signature
  let b ← sigDecode s g.signature
  let c ← H.sampleInBall s a.digest
  let pk := publicKey s bytes A
  let x : CompressedSignature s.params := ⟨a.z, a.h, c⟩
  let y : CompressedSignature s.params := ⟨b.z, b.h, c⟩
  let addr (σ : CompressedSignature s.params) (out : Forgery) :=
    commitmentInput s (σ.recover 13 pk) (H.messageRepresentative bytes (formattedMessage out))
  if addr x f ≠ addr y g then return .collision (addr x f) (addr y g)
  return .msis (responseDifference 13 pk x y)

/-- Two distinct accepted triples with one digest yield a valid computed witness for any
shared XOF. The external messages, contexts and signature byte strings may differ. -/
theorem extractRepeatedDigest_of_verify {H : Xofs} {s : Level} {bytes : List Byte}
    {A : PublicMatrix s} {f g : Forgery} (hA : H.expandA s (bytes.take 32) = some A)
    (distinct : f ≠ g) (hd : f.signature.take (digestBytes s) = g.signature.take (digestBytes s))
    (first : H.verify s bytes f.message f.context f.signature = some true)
    (second : H.verify s bytes g.message g.context g.signature = some true) :
    ∃ w, H.extractRepeatedDigest s bytes A f g = some w ∧ w.Valid H A := by
  obtain ⟨a, c, ha, hc, za, da⟩ := recovered_of_verifyWithExpansion (f := f) hA first
  obtain ⟨b, c', hb, hc', zb, db⟩ := recovered_of_verifyWithExpansion (f := g) hA second
  have same := (digest_of_sigDecode ha).symm.trans (hd.trans (digest_of_sigDecode hb))
  rw [← same, hc, Option.some.injEq] at hc'
  subst c'
  let pk := publicKey s bytes A
  let x : CompressedSignature s.params := ⟨a.z, a.h, c⟩
  let y : CompressedSignature s.params := ⟨b.z, b.h, c⟩
  let μ (out : Forgery) := H.messageRepresentative bytes (formattedMessage out)
  let u := commitmentInput s (x.recover 13 pk) (μ f)
  let v := commitmentInput s (y.recover 13 pk) (μ g)
  let tr := H.h256.readBytes bytes 64
  have parsed : H.extractRepeatedDigest s bytes A f g =
      some (if formattedMessage f ≠ formattedMessage g ∧ μ f = μ g then
        .collision (representativeInput tr (formattedMessage f))
          (representativeInput tr (formattedMessage g))
      else if u ≠ v then .collision u v else .msis (responseDifference 13 pk x y)) := by
    simp only [Xofs.extractRepeatedDigest, ha, hb, hc, Option.bind_some, Option.bind_eq_bind]
    split_ifs <;> rfl
  by_cases msgHash : formattedMessage f ≠ formattedMessage g ∧ μ f = μ g
  · refine ⟨.collision (representativeInput tr (formattedMessage f))
      (representativeInput tr (formattedMessage g)), parsed.trans (by simp [msgHash]), ?_, ?_⟩
    · exact fun h => msgHash.1 (List.append_cancel_left h)
    · have val := read_eq_of_messageRepresentative_eq H bytes msgHash.2
      have width : digestBytes s ≤ 64 := by cases s <;> decide
      simpa only [H.h256.take_read _ width, tr] using congrArg (List.take (digestBytes s)) val
  by_cases addresses : u ≠ v
  · refine ⟨.collision u v, parsed.trans (by simp [msgHash, addresses]), addresses, ?_⟩
    exact da.trans (same.trans db.symm)
  have addrEq : u = v := not_ne_iff.mp addresses
  have reps : μ f = μ g :=
    (List.append_inj (show μ f ++ _ = μ g ++ _ from addrEq) (by simp [μ])).1
  have frameEq : formattedMessage f = formattedMessage g := by
    by_contra diff
    exact msgHash ⟨diff, reps⟩
  refine ⟨.msis (responseDifference 13 pk x y), parsed.trans (by simp [msgHash, addrEq]), ?_⟩
  have valid : s.params.Valid := by
    cases s
    · exact Params.valid_mldsa44
    · exact Params.valid_mldsa65
    · exact Params.valid_mldsa87
  have gap : 4 * s.params.γ₂ < s.params.q := by cases s <;> decide
  have range (σ : CompressedSignature s.params) (i : Fin s.params.k) (j : Fin 256) :
      0 ≤ σ.recover 13 pk i j ∧
        σ.recover 13 pk i j < (((s.params.q - 1) / (2 * s.params.γ₂) : ℕ) : ℤ) :=
    ⟨useHint_nonneg valid.γ₂_pos gap _ _, useHint_lt valid.γ₂_pos valid.two_mul_γ₂_dvd gap _ _⟩
  have sameW : x.recover 13 pk = y.recover 13 pk := by
    apply eq_of_commitmentInput_eq (range x) (range y) (μ := μ f)
    simpa only [u, v, ← reps] using addrEq
  apply isSolution_responseDifference (σ := x) (σ' := y) valid gap 13 pk ?_ rfl sameW za zb
  intro heq
  have hz : a.z = b.z := congrArg CompressedSignature.z heq
  have hh : a.h = b.h := congrArg CompressedSignature.h heq
  have hab : a = b := by cases a; cases b; congr
  have sig := eq_of_sigDecode (hab ▸ ha) hb
  have lengthOK (e : Forgery) (h : H.verify s bytes e.message e.context e.signature = some true) :
      e.context.length ≤ 255 := by
    by_contra guardFail
    simp [Xofs.verify, Xofs.verifyWithExpansion, guard, guardFail] at h
  obtain ⟨ctx, msg⟩ := formatMessage_inj (lengthOK f first) (lengthOK g second) frameEq
  exact distinct (by cases f; cases g; congr)

end Cslib.Crypto.MLDSA.FIPS204
