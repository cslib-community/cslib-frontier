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
public import CslibFrontier.Languages.Probabilistic.Basic
import CslibFrontier.Probability.PMF.Uniform
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

For commitment collisions, choose a uniform sign for each coefficient and then draw two
masks from the selected half-box. Each marginal is exactly the signing mask law, and the
centered difference has infinity norm at most `γ₁−1`.
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

private theorem card_cast_Icc [NeZero P.q] {lo hi : ℤ}
    (hlo : -(P.q : ℤ) < 2 * lo) (hhi : 2 * hi ≤ P.q) :
    ((Finset.Icc lo hi).image (Int.cast : ℤ → ZMod P.q)).card = (hi + 1 - lo).toNat := by
  have hinj : Set.InjOn (Int.cast : ℤ → ZMod P.q) (Finset.Icc lo hi) := by
    intro a ha b hb h
    have eqLift (x : ℤ) (hx : x ∈ Finset.Icc lo hi) : (x : ZMod P.q).valMinAbs = x :=
      (ZMod.valMinAbs_spec _ _).2 ⟨rfl, by
        obtain ⟨h₁, h₂⟩ := Finset.mem_Icc.mp hx
        exact ⟨by lia, by lia⟩⟩
    simpa only [eqLift a ha, eqLift b hb] using congrArg ZMod.valMinAbs h
  rw [Finset.card_image_of_injOn hinj, Int.card_Icc]

private theorem intervalVectors_card [NeZero P.q] {lo hi : ℤ}
    (hlo : -(P.q : ℤ) < 2 * lo) (hhi : 2 * hi ≤ P.q) :
    (intervalVectors P lo hi).card = (hi + 1 - lo).toNat ^ (P.ℓ * P.n) := by
  simp only [intervalVectors, Fintype.card_piFinset, card_cast_Icc P hlo hhi, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← pow_mul, Nat.mul_comm P.n P.ℓ]

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

/-- Every lifted coefficient of a supported signing mask belongs to `(-γ₁,γ₁]`. -/
theorem signingMaskLaw_support_bounds [NeZero P.q] {hγ : 0 < P.γ₁} (hq : 2 * P.γ₁ < P.q)
    {y : Fin P.ℓ → Fin P.n → ZMod P.q} (hy : y ∈ (signingMaskLaw P hγ).support) (i j) :
    1 - (P.γ₁ : ℤ) ≤ (y i j).valMinAbs ∧ (y i j).valMinAbs ≤ P.γ₁ := by
  rw [signingMaskLaw, PMF.mem_support_uniformOfFinset_iff, mem_intervalVectors] at hy
  obtain ⟨x, ⟨hl, hu⟩, hx⟩ := hy i j
  have he : (y i j).valMinAbs = x := (ZMod.valMinAbs_spec _ _).2 ⟨hx.symm, by
    exact ⟨by lia, by lia⟩⟩
  rw [he]
  exact ⟨hl, hu⟩

private theorem mask_card [NeZero P.q] (hγ : 0 < P.γ₁) (hq : 2 * P.γ₁ < P.q) :
    (maskSet P).card = (2 * P.γ₁) ^ (P.ℓ * P.n) := by
  rw [intervalVectors_card P (by lia) (by lia)]
  congr 1
  lia

/-- A bit for each mask coefficient, selecting its nonpositive or positive half-interval. -/
abbrev MaskSigns := Fin P.ℓ → Fin P.n → Bool

private def halfStart (b : Bool) : ℤ := if b then 1 else 1 - (P.γ₁ : ℤ)

private def halfMaskSet (b : MaskSigns P) : Finset (Fin P.ℓ → Fin P.n → ZMod P.q) :=
  Fintype.piFinset fun i => Fintype.piFinset fun j =>
    let a := halfStart P (b i j)
    (Finset.Icc a (a + P.γ₁ - 1)).image (Int.cast : ℤ → ZMod P.q)

private theorem halfMask_nonempty (hγ : 0 < P.γ₁) (b : MaskSigns P) :
    (halfMaskSet P b).Nonempty := by
  refine ⟨fun i j => (halfStart P (b i j) : ZMod P.q), ?_⟩
  simp only [halfMaskSet, Fintype.mem_piFinset, Finset.mem_image, Finset.mem_Icc]
  exact fun i j => ⟨_, ⟨le_rfl, by lia⟩, rfl⟩

/-- Uniform mask given a sign array, with each coefficient drawn independently from the
corresponding interval of width `γ₁`. -/
noncomputable def halfMaskLaw (hγ : 0 < P.γ₁) (b : MaskSigns P) :
    PMF (Fin P.ℓ → Fin P.n → ZMod P.q) :=
  PMF.uniformOfFinset (halfMaskSet P b) (halfMask_nonempty P hγ b)

/-- Sample uniformly from a single half-box. Reusing the sign array across draws keeps the
coefficientwise difference below `γ₁`. -/
noncomputable def sampleHalfMask (hγ : 0 < P.γ₁) (b : MaskSigns P) :
    ProbComp (Fin P.ℓ → Fin P.n → ZMod P.q) :=
  letI : Nonempty (halfMaskSet P b) := Finset.nonempty_coe_sort.mpr (halfMask_nonempty P hγ b)
  Subtype.val <$> ProbComp.uniform (halfMaskSet P b)

@[simp] theorem eval_sampleHalfMask (hγ : 0 < P.γ₁) (b : MaskSigns P) :
    (sampleHalfMask P hγ b).eval = halfMaskLaw P hγ b := by
  let : Nonempty (halfMaskSet P b) := Finset.nonempty_coe_sort.mpr (halfMask_nonempty P hγ b)
  simp only [sampleHalfMask, ProbComp.eval_map, ProbComp.eval_uniform, halfMaskLaw,
    Probability.PMF.uniformOfFintype_finset_map_val]

private theorem halfMask_card [NeZero P.q] (hγ : 0 < P.γ₁) (hq : 2 * P.γ₁ < P.q)
    (b : MaskSigns P) : (halfMaskSet P b).card = P.γ₁ ^ (P.ℓ * P.n) := by
  have hc (a : Bool) : ((Finset.Icc (halfStart P a) (halfStart P a + P.γ₁ - 1)).image
      (Int.cast : ℤ → ZMod P.q)).card = P.γ₁ := by
    rw [card_cast_Icc P (by cases a <;> simp [halfStart]; lia)
      (by cases a <;> simp [halfStart]; lia)]
    lia
  simp only [halfMaskSet, Fintype.card_piFinset, hc, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← pow_mul, Nat.mul_comm P.n P.ℓ]

/-- Every supported mask in a given half-box has mass `γ₁^(-ℓ n)`. -/
theorem halfMaskLaw_apply_of_mem [NeZero P.q] {hγ : 0 < P.γ₁} (hq : 2 * P.γ₁ < P.q)
    {b : MaskSigns P} {y : Fin P.ℓ → Fin P.n → ZMod P.q} (hy : y ∈ (halfMaskLaw P hγ b).support) :
    halfMaskLaw P hγ b y = (↑(P.γ₁ ^ (P.ℓ * P.n)) : ℝ≥0∞)⁻¹ := by
  rw [halfMaskLaw, PMF.mem_support_uniformOfFinset_iff] at hy
  simp only [halfMaskLaw, PMF.uniformOfFinset_apply, ite_eq_left hy, halfMask_card P hγ hq]

/-- A specified mask has mass at most the reciprocal of the conditional half-box size. -/
theorem halfMaskLaw_apply_le [NeZero P.q] (hγ : 0 < P.γ₁) (hq : 2 * P.γ₁ < P.q)
    (b : MaskSigns P) (y : Fin P.ℓ → Fin P.n → ZMod P.q) :
    halfMaskLaw P hγ b y ≤ (↑(P.γ₁ ^ (P.ℓ * P.n)) : ℝ≥0∞)⁻¹ := by
  by_cases hy : y ∈ (halfMaskLaw P hγ b).support
  · exact (halfMaskLaw_apply_of_mem P hq hy).le
  · rw [(PMF.apply_eq_zero_iff _ _).mpr hy]
    exact zero_le

private theorem mem_halfMaskSet_iff [NeZero P.q] (hq : 2 * P.γ₁ < P.q)
    {b : MaskSigns P} {y : Fin P.ℓ → Fin P.n → ZMod P.q} :
    y ∈ halfMaskSet P b ↔ ∀ i j, let a := halfStart P (b i j)
      a ≤ (y i j).valMinAbs ∧ (y i j).valMinAbs ≤ a + P.γ₁ - 1 := by
  simp only [halfMaskSet, Fintype.mem_piFinset, Finset.mem_image, Finset.mem_Icc]
  constructor
  · intro h i j
    obtain ⟨x, ⟨hl, hu⟩, hx⟩ := h i j
    have he : (y i j).valMinAbs = x := (ZMod.valMinAbs_spec _ _).2 ⟨hx.symm, by
      cases hb : b i j <;> simp [hb, halfStart] at hl hu <;> constructor <;> lia⟩
    exact he.symm ▸ ⟨hl, hu⟩
  · intro h i j
    exact ⟨_, h i j, ZMod.coe_valMinAbs _⟩

/-- Two masks in the same half-box yield centered integer differences of norm at most `γ₁−1`. -/
theorem abs_sub_le_of_mem_halfMaskLaw [NeZero P.q] {hγ : 0 < P.γ₁} (hq : 2 * P.γ₁ < P.q)
    {b : MaskSigns P} {y z : Fin P.ℓ → Fin P.n → ZMod P.q}
    (hy : y ∈ (halfMaskLaw P hγ b).support) (hz : z ∈ (halfMaskLaw P hγ b).support) (i j) :
    |(y i j).valMinAbs - (z i j).valMinAbs| ≤ (P.γ₁ - 1 : ℕ) := by
  rw [halfMaskLaw, PMF.mem_support_uniformOfFinset_iff, mem_halfMaskSet_iff P hq] at hy hz
  obtain ⟨hl, hu⟩ := hy i j
  obtain ⟨hl', hu'⟩ := hz i j
  rw [abs_le]
  constructor <;> lia

/-- A random sign array followed by a uniform draw from its half-box recovers the ideal
Algorithm 7 mask law. -/
theorem uniformSigns_bind_halfMaskLaw [NeZero P.q] (hγ : 0 < P.γ₁) (hq : 2 * P.γ₁ < P.q) :
    (PMF.uniformOfFintype (MaskSigns P)).bind (halfMaskLaw P hγ) = signingMaskLaw P hγ := by
  classical
  ext y
  let signs : MaskSigns P := fun i j => decide (0 < (y i j).valMinAbs)
  have part (b : MaskSigns P) : y ∈ halfMaskSet P b ↔ y ∈ maskSet P ∧ b = signs := by
    rw [mem_halfMaskSet_iff P hq]
    constructor
    · intro h
      constructor
      · apply (mem_intervalVectors P).2
        intro i j
        obtain ⟨hl, hu⟩ := h i j
        refine ⟨_, ⟨?_, ?_⟩, ZMod.coe_valMinAbs _⟩ <;>
          cases hb : b i j <;> simp [halfStart, hb] at hl hu <;> lia
      · funext i j
        obtain ⟨hl, hu⟩ := h i j
        cases hb : b i j <;> simp [halfStart, hb] at hl hu <;> simp [signs] <;> lia
    · rintro ⟨hy, rfl⟩ i j
      have hh : y ∈ (signingMaskLaw P hγ).support :=
        (PMF.mem_support_uniformOfFinset_iff ..).2 hy
      obtain ⟨hl, hu⟩ := signingMaskLaw_support_bounds P hq hh i j
      by_cases hs : 0 < (y i j).valMinAbs <;> simp [signs, halfStart, hs] <;> lia
  simp only [PMF.bind_apply, PMF.uniformOfFintype_apply, halfMaskLaw, signingMaskLaw,
    PMF.uniformOfFinset_apply, halfMask_card P hγ hq, mask_card P hγ hq, part, tsum_fintype]
  by_cases hy : y ∈ maskSet P
  · have hc : Fintype.card (MaskSigns P) * P.γ₁ ^ (P.ℓ * P.n) = (2 * P.γ₁) ^ (P.ℓ * P.n) := by
      simp [MaskSigns, mul_pow, ← pow_mul, Nat.mul_comm P.n P.ℓ]
    rw [← hc, Nat.cast_mul, ENNReal.mul_inv (Or.inl (by exact_mod_cast Fintype.card_ne_zero))
      (Or.inl (ENNReal.natCast_ne_top _))]
    simp [hy]
  · simp [hy]

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
  obtain ⟨oz, ho, he⟩ := (PMF.mem_support_map_iff ..).1 ht
  rcases oz with _ | z
  · cases he
  change finishSimulated P d ω pk c z = some t at he
  obtain ⟨b, _, hb⟩ := (PMF.mem_support_bind_iff ..).1 ho
  cases b with
  | false => simp at hb
  | true =>
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
      · have hout : (⟨highBitsVec P r, ⟨z', h, c⟩⟩ : AttemptTranscript P) = t := by
          simpa [guard, hl, hh] using he
        subst t
        refine ⟨rfl, hz, hh.2, ?_⟩
        funext i
        simp only [CompressedSignature.recover,
          compressedVerifierCommitment_eq_verifierCommitment_add_lowPart, Pi.add_apply]
        rw [useHintVec_makeHintVec hP.γ₂_pos hP.two_mul_γ₂_dvd hγq (z := -ct₀ i)
          (r := r i + ct₀ i) (fun j => by
            simpa only [Pi.neg_apply, Int.abs_eq_natAbs, ZMod.natAbs_valMinAbs_neg]
              using (hh.1 i j).le)]
        funext j
        simp only [highBitsVec, Pi.add_apply, Pi.neg_apply]
        congr 1
        ring
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
  have hpre z (hz : z ∈ responseSet P) : z - v ∈ maskSet P :=
    sub_mem_mask P ((mem_response_iff P hq z).1 hz) hv
  have hgate := PMF.shiftReject_eq_sampleWithRatio (hB := mask_nonempty P (by lia)) hpre
    (response_nonempty P hβ)
  have hm := mask_card P (by lia) hq
  have hr : (responseSet P).card = (2 * (P.γ₁ - P.β) - 1) ^ (P.ℓ * P.n) := by
    rw [intervalVectors_card P (by lia) (by lia)]
    congr 1
    lia
  unfold simulateFreshSigningAttempt
  simp only [← hm, ← hr, ← hgate, PMF.shiftReject, PMF.map_comp, Function.comp_def,
    freshSigningAttempt, signingMaskLaw]
  congr 1 with y : 1
  let w := moduleSISMap sk.A y
  let r := w - fun i => negacyclicMul c (sk.s₂ i)
  have he := verifierCommitment_publicKey sk y c
  by_cases hz : ResponseShort P (y + v)
  · by_cases hl : LowBitsShort P r
    · have hh := highBitsVec_sub_challenge hP hc hs₂ hl
      dsimp only [v, r, w] at hz hl hh ⊢
      simp only [compressedSignAttempt, mem_response_iff P hq, hz, hl, and_self, ↓reduceIte,
        Option.bind_some, finishSimulated, he, guard, pure_bind, hh]
      split_ifs <;> rfl
    · dsimp only [v, r, w] at hz hl ⊢
      simp [compressedSignAttempt, finishSimulated, mem_response_iff P hq, hz, he, hl, guard]
  · dsimp only [v] at hz ⊢
    simp [compressedSignAttempt, mem_response_iff P hq, hz]

end Cslib.Crypto.MLDSA
