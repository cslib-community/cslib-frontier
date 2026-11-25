/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.Signing
public import CslibFrontier.Crypto.Computational.MLDSA.ResponseBinding
public import CslibFrontier.Probability.RejectionSampling
import CslibFrontier.Probability.PMF.Bind

/-!
# Simulation of one ML-DSA signing attempt with a fresh challenge

In [NISTFIPS204], Algorithm 7, the mask coefficients are uniform on `(-γ₁,γ₁]` in
the ideal-mask model, and the response check is strict. This gives
`(2(γ₁-β)-1)^(ℓn)` admissible responses out of `(2γ₁)^(ℓn)` masks.

For every fixed sparse challenge independent of the mask, the simulator receives the
full public vector `t = A s₁ + s₂`. It draws a fresh uniform response in the inner box
after an independent gate with that exact ratio. It computes the remaining rejection
checks and the hint from `A,t,z,c`. The resulting law agrees with the signing attempt on
its complete accepted algebraic transcript and on aborts. The transcript includes the
high-bits commitment used for the hash query. This is the fresh-challenge distribution
step of the signing simulation argument in [BaiEtAl2021Dilithium], Appendix B.
-/

public section

namespace Cslib.Crypto.MLDSA

open Cslib.Probability
open scoped ENNReal

variable (P : Params)

/-- The public data of a successful signing attempt at a fresh challenge. The commitment is
the coefficient vector encoded for the hash input, and the compressed signature contains
the response, hint and polynomial challenge. -/
structure AttemptTranscript where
  /-- The high-order commitment hashed with the message representative. -/
  commitment : Fin P.k → Fin P.n → ℤ
  /-- The accepted response, hint, and sparse challenge. -/
  signature : CompressedSignature P

private def intervalVectors (lo hi : ℤ) : Finset (Fin P.ℓ → Fin P.n → ZMod P.q) :=
  Fintype.piFinset fun _ => Fintype.piFinset fun _ =>
    (Finset.Icc lo hi).image (Int.cast : ℤ → ZMod P.q)

private theorem mem_intervalVectors {lo hi : ℤ} {r : Fin P.ℓ → Fin P.n → ZMod P.q} :
    r ∈ intervalVectors P lo hi ↔ ∀ i j, ∃ x : ℤ, (lo ≤ x ∧ x ≤ hi) ∧ (x : ZMod P.q) = r i j := by
  simp only [intervalVectors, Fintype.mem_piFinset, Finset.mem_image, Finset.mem_Icc]

private theorem intervalVectors_card [NeZero P.q] {lo hi : ℤ}
    (hlo : -(P.q : ℤ) < 2 * lo) (hhi : 2 * hi ≤ P.q) :
    (intervalVectors P lo hi).card = (hi + 1 - lo).toNat ^ (P.ℓ * P.n) := by
  have hinj : Set.InjOn (Int.cast : ℤ → ZMod P.q) (Finset.Icc lo hi) := by
    intro a ha b hb h
    have eqLift (x : ℤ) (hx : x ∈ Finset.Icc lo hi) : (x : ZMod P.q).valMinAbs = x :=
      (ZMod.valMinAbs_spec _ _).2 ⟨rfl, by
        obtain ⟨h₁, h₂⟩ := Finset.mem_Icc.mp hx
        exact ⟨by lia, by lia⟩⟩
    simpa only [eqLift a ha, eqLift b hb] using congrArg ZMod.valMinAbs h
  simp only [intervalVectors, Fintype.card_piFinset, Finset.card_image_of_injOn hinj,
    Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul,
    Nat.mul_comm P.n P.ℓ]

private abbrev maskSet := intervalVectors P (1 - (P.γ₁ : ℤ)) P.γ₁
private abbrev responseSet :=
  intervalVectors P (1 - ((P.γ₁ : ℤ) - P.β)) ((P.γ₁ : ℤ) - P.β - 1)

private theorem mask_nonempty (hγ : 0 < P.γ₁) : (maskSet P).Nonempty :=
  ⟨0, (mem_intervalVectors P).2 fun _ _ => ⟨0, ⟨by lia, by lia⟩, by simp⟩⟩

private theorem response_nonempty (hβ : P.β < P.γ₁) : (responseSet P).Nonempty :=
  ⟨0, (mem_intervalVectors P).2 fun _ _ => ⟨0, ⟨by lia, by lia⟩, by simp⟩⟩

private theorem mem_response_iff [NeZero P.q] (hq : 2 * P.γ₁ < P.q)
    (z : Fin P.ℓ → Fin P.n → ZMod P.q) : z ∈ responseSet P ↔ ResponseShort P z := by
  rw [mem_intervalVectors]
  constructor
  · intro hz i j
    obtain ⟨x, ⟨hl, hu⟩, hx⟩ := hz i j
    have he : (z i j).valMinAbs = x := (ZMod.valMinAbs_spec _ _).2 ⟨hx.symm, by
      exact ⟨by lia, by lia⟩⟩
    rw [he, abs_lt]
    exact ⟨by lia, by lia⟩
  · intro hz i j
    obtain ⟨hl, hu⟩ := abs_lt.mp (hz i j)
    exact ⟨_, ⟨by lia, by lia⟩, ZMod.coe_valMinAbs _⟩

private theorem sub_mem_mask {v z : Fin P.ℓ → Fin P.n → ZMod P.q}
    (hz : ResponseShort P z) (hv : ∀ i j, |(v i j).valMinAbs| ≤ P.β) :
    z - v ∈ maskSet P := by
  refine (mem_intervalVectors P).2 fun i j => ?_
  obtain ⟨hl, hu⟩ := abs_lt.mp (hz i j)
  obtain ⟨hvl, hvu⟩ := abs_le.mp (hv i j)
  exact ⟨(z i j).valMinAbs - (v i j).valMinAbs, ⟨by lia, by lia⟩, by simp⟩

/-- An ideal Algorithm 7 mask, uniform over the coefficient box `(-γ₁, γ₁]^(ℓ n)`. -/
noncomputable def signingMaskLaw (hγ : 0 < P.γ₁) : PMF (Fin P.ℓ → Fin P.n → ZMod P.q) :=
  PMF.uniformOfFinset (maskSet P) (mask_nonempty P hγ)

private theorem mask_card [NeZero P.q] (hγ : 0 < P.γ₁) (hq : 2 * P.γ₁ < P.q) :
    (maskSet P).card = (2 * P.γ₁) ^ (P.ℓ * P.n) := by
  rw [intervalVectors_card P (by lia) (by lia)]
  exact congrArg (· ^ (P.ℓ * P.n)) (by lia)

/-- Every individual ideal mask has probability at most the reciprocal of the full FIPS box. -/
theorem signingMaskLaw_apply_le [NeZero P.q] (hγ : 0 < P.γ₁) (hq : 2 * P.γ₁ < P.q) (y) :
    signingMaskLaw P hγ y ≤ ((2 * P.γ₁ : ℕ) ^ (P.ℓ * P.n) : ℝ≥0∞)⁻¹ := by
  classical
  simp only [signingMaskLaw, PMF.uniformOfFinset_apply, mask_card P hγ hq, Nat.cast_pow]
  split <;> simp

/-- The signing attempt with an ideal, coefficientwise uniform mask and the given fresh
challenge. On success it emits the high bits of the original commitment `A y` and the
signature returned by Algorithm 7's two rejection stages. -/
@[expose] noncomputable def freshSigningAttempt (d ω : ℕ) (hγ : 0 < P.γ₁) (sk : SecretKey P)
    (c : Fin P.n → ZMod P.q) : PMF (Option (AttemptTranscript P)) :=
  (signingMaskLaw P hγ).map fun y =>
    (compressedSignAttempt P d ω (fun _ => c) sk [] y).map fun σ =>
      ⟨highBitsVec P (moduleSISMap sk.A y), σ⟩

private def finishSimulated (d ω : ℕ) (pk : PublicKey P) (c : Fin P.n → ZMod P.q)
    (z : Fin P.ℓ → Fin P.n → ZMod P.q) : Option (AttemptTranscript P) := do
  let r := verifierCommitment P pk z c
  guard (LowBitsShort P r)
  let ct₀ := fun i => negacyclicMul c (publicKeyLowPart P d pk i)
  let h := fun i => makeHintVec P.q P.γ₂ (-ct₀ i) (r i + ct₀ i)
  guard (LowProductShort P ct₀ ∧ hintWeight P h ≤ ω)
  return ⟨highBitsVec P r, ⟨z, h, c⟩⟩

/-- Simulate the accepted transcript and abort mass from `(A,t)`. Keep the response
with probability `((2(γ₁-β)-1)/(2γ₁))^(ℓ n)`, sample it independently and uniformly
inside the strict response box, then perform the public low-bits, product and hint checks. -/
noncomputable def simulateFreshSigningAttempt (d ω : ℕ) (hβ : P.β < P.γ₁) (pk : PublicKey P)
    (c : Fin P.n → ZMod P.q) : PMF (Option (AttemptTranscript P)) :=
  let m := P.ℓ * P.n
  let z := PMF.uniformOfFinset (responseSet P) (response_nonempty P hβ)
  (PMF.sampleWithRatio z ((2 * (P.γ₁ - P.β) - 1) ^ m) ((2 * P.γ₁) ^ m)
    (pow_pos (by lia) _)).map fun oz => oz.bind (finishSimulated P d ω pk c)

/-- The simulated attempt transcript distribution has finite support. -/
theorem simulateFreshSigningAttempt_support_finite [NeZero P.q] (d ω : ℕ) (hβ : P.β < P.γ₁)
    (pk : PublicKey P) (c : Fin P.n → ZMod P.q) :
    (simulateFreshSigningAttempt P d ω hβ pk c).support.Finite := by
  classical
  unfold simulateFreshSigningAttempt
  rw [PMF.support_map]
  exact (Set.toFinite _).image _

/-- Every accepted public simulation has the requested challenge, a short response, an
encodable hint, and the very commitment that the verifier recovers. This holds for every full
public key, including a uniformly sampled vector in the Module-LWE hybrid. -/
theorem simulateFreshSigningAttempt_support (hP : P.Valid) (hq : 2 * P.γ₁ < P.q)
    (hγq : 4 * P.γ₂ < P.q) (d ω : ℕ) (hβ : P.β < P.γ₁) (pk : PublicKey P)
    (c : Fin P.n → ZMod P.q) {t : AttemptTranscript P}
    (ht : some t ∈ (simulateFreshSigningAttempt P d ω hβ pk c).support) :
    t.signature.c = c ∧ ResponseShort P t.signature.z ∧ hintWeight P t.signature.h ≤ ω ∧
      t.signature.recover d pk = t.commitment := by
  let : NeZero P.q := ⟨by have := hP.one_lt_q; lia⟩
  obtain ⟨_ | z, ho, he⟩ := (PMF.mem_support_map_iff ..).1 ht
  · cases he
  change finishSimulated P d ω pk c z = some t at he
  obtain ⟨_ | _, _, hb⟩ := (PMF.mem_support_bind_iff ..).1 ho
  · simp at hb
  obtain ⟨z', hz', he'⟩ := (PMF.mem_support_map_iff ..).1 hb
  obtain rfl := Option.some.inj he'
  have hz := (mem_response_iff P hq z').1 ((PMF.mem_support_uniformOfFinset_iff ..).1 hz')
  let r := verifierCommitment P pk z' c
  let ct₀ := fun i => negacyclicMul c (publicKeyLowPart P d pk i)
  let h := fun i => makeHintVec P.q P.γ₂ (-ct₀ i) (r i + ct₀ i)
  change (do
    guard (LowBitsShort P r)
    guard (LowProductShort P ct₀ ∧ hintWeight P h ≤ ω)
    return ⟨highBitsVec P r, ⟨z', h, c⟩⟩ : Option (AttemptTranscript P)) = some t at he
  by_cases hl : LowBitsShort P r
  · by_cases hh : LowProductShort P ct₀ ∧ hintWeight P h ≤ ω
    · obtain rfl : (⟨highBitsVec P r, ⟨z', h, c⟩⟩ : AttemptTranscript P) = t := by
        simpa [guard, hl, hh] using he
      refine ⟨rfl, hz, hh.2, funext fun i => ?_⟩
      simp only [CompressedSignature.recover,
        compressedVerifierCommitment_eq_verifierCommitment_add_lowPart, Pi.add_apply]
      rw [useHintVec_makeHintVec hP.γ₂_pos hP.two_mul_γ₂_dvd hγq (z := -ct₀ i)
        (r := r i + ct₀ i) fun j => by
          simpa only [Pi.neg_apply, Int.abs_eq_natAbs, ZMod.natAbs_valMinAbs_neg]
            using (hh.1 i j).le]
      exact funext fun j => by simp [highBitsVec]
    · simp [guard, hl, hh] at he
  · simp [guard, hl] at he

/-- For every fresh sparse challenge, the complete accepted transcript and the probability of
an abort agree with the public simulator. A distribution of challenges independent of the mask
can bind this equality pointwise, retaining the challenge and any commitment-digest bytes. -/
theorem freshSigningAttempt_eq_simulate (hP : P.Valid) (hq : 2 * P.γ₁ < P.q)
    (hβ : P.β < P.γ₁) (d ω : ℕ) (sk : SecretKey P)
    (hs₁ : ∀ i j, |(sk.s₁ i j).valMinAbs| ≤ P.η)
    (hs₂ : ∀ i j, |(sk.s₂ i j).valMinAbs| ≤ P.η)
    {c : Fin P.n → ZMod P.q} (hc : InBall P.τ c) :
    freshSigningAttempt P d ω (by lia) sk c =
      simulateFreshSigningAttempt P d ω hβ sk.publicKey c := by
  classical
  have : NeZero P.q := ⟨by have := hP.one_lt_q; lia⟩
  let v := fun i => negacyclicMul c (sk.s₁ i)
  have hv (i j) : |(v i j).valMinAbs| ≤ P.β :=
    (abs_valMinAbs_negacyclicMul_le hc (hs₁ i) j).trans (by exact_mod_cast hP.τ_mul_η_le_β)
  have hgate := PMF.shiftReject_eq_sampleWithRatio (hB := mask_nonempty P (by lia))
    (fun z hz => sub_mem_mask P ((mem_response_iff P hq z).1 hz) hv) (response_nonempty P hβ)
  have hr : (responseSet P).card = (2 * (P.γ₁ - P.β) - 1) ^ (P.ℓ * P.n) := by
    rw [intervalVectors_card P (by lia) (by lia)]
    congr 1
    lia
  unfold simulateFreshSigningAttempt
  simp only [← mask_card P (by lia) hq, ← hr, ← hgate, PMF.shiftReject, PMF.map_comp,
    Function.comp_def, freshSigningAttempt, signingMaskLaw]
  congr 1 with y : 1
  let r := moduleSISMap sk.A y - fun i => negacyclicMul c (sk.s₂ i)
  simp only [compressedSignAttempt, compressedResponse, tabulateRingVector_eq]
  by_cases hz : ResponseShort P (y + v)
  · by_cases hl : LowBitsShort P r
    · have hh := highBitsVec_sub_challenge hP hc hs₂ hl
      dsimp only [v, r] at hz hl hh ⊢
      simp only [mem_response_iff P hq, hz, hl, and_self, ↓reduceIte, Option.bind_some,
        finishSimulated, verifierCommitment_publicKey sk y c, guard, pure_bind, hh]
      split_ifs <;> rfl
    · dsimp only [v, r] at hz hl ⊢
      simp [finishSimulated, mem_response_iff P hq, hz, verifierCommitment_publicKey sk y c,
        hl, guard]
  · dsimp only [v] at hz ⊢
    simp [mem_response_iff P hq, hz]

end Cslib.Crypto.MLDSA
