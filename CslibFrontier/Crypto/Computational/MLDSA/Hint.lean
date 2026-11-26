/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.Decompose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# ML-DSA hint generation and use

ML-DSA compresses a commitment to its high-order bits. The signer supplies one hint bit per
coefficient saying whether a short correction changes those bits, and the verifier uses that bit
to move by one high-order bucket in the direction determined by the low bits. These are Algorithms
39 (`MakeHint`) and 40 (`UseHint`) of [NISTFIPS204].

## Main definitions

* `Cslib.Crypto.MLDSA.makeHint`: whether adding a correction changes the high bits.
* `Cslib.Crypto.MLDSA.useHint`: adjust the high bits by the supplied hint.
* `Cslib.Crypto.MLDSA.hintResidual`: the short residual between the hinted high part and the
  original coefficient.
* `Cslib.Crypto.MLDSA.makeHintVec`, `Cslib.Crypto.MLDSA.useHintVec`: coefficientwise forms.

## Main results

* `Cslib.Crypto.MLDSA.useHint_makeHint`: the recovery property in Lemma 1(1) of the Dilithium
  specification.
* `Cslib.Crypto.MLDSA.useHint_nonneg`, `Cslib.Crypto.MLDSA.useHint_lt`: the output range.
* `Cslib.Crypto.MLDSA.useHint_injective`: distinct hint bits give distinct adjusted high bits.
* `Cslib.Crypto.MLDSA.useHint_mul_eq_add_hintResidual`,
  `Cslib.Crypto.MLDSA.abs_hintResidual_valMinAbs_le`: the residual identity and bound in
  Lemma 1(2) of the Dilithium specification.
* `Cslib.Crypto.MLDSA.useHintVec_makeHintVec`: coefficientwise recovery.

The printed output bound of Algorithm 40 is non-strict, but NIST's potential-updates spreadsheet
(identified 2026-02-27) records the strict range `0 ≤ r₁ < (q - 1) / (2 γ₂)` used by `w1Encode`.
The range theorem below states this corrected bound.

## References

* [S. Bai et al., *CRYSTALS-Dilithium: Algorithm Specifications and Supporting
  Documentation*, Version 3.1][BaiEtAl2021Dilithium]
* [National Institute of Standards and Technology, *Module-Lattice-Based Digital Signature
  Standard*][NISTFIPS204]
-/

@[expose] public section

namespace Cslib.Crypto.MLDSA

/-- `MakeHint` from Algorithm 39 of [NISTFIPS204]. The bit is set exactly when adding `z` changes
the high bits of `r`. -/
def makeHint (q γ₂ : ℕ) (z r : ZMod q) : Bool :=
  decide (highBits q γ₂ r ≠ highBits q γ₂ (r + z))

/-- `UseHint` from Algorithm 40 of [NISTFIPS204]. A set hint moves the high part one bucket up
when the low part is positive and one bucket down otherwise, modulo the number of buckets. -/
def useHint (q γ₂ : ℕ) (h : Bool) (r : ZMod q) : ℤ :=
  let m : ℕ := (q - 1) / (2 * γ₂)
  match h with
  | true =>
    if 0 < lowBits q γ₂ r then (highBits q γ₂ r + 1) % (m : ℤ)
    else (highBits q γ₂ r - 1) % (m : ℤ)
  | false => highBits q γ₂ r

/-- The residual `u = 2 γ₂ · UseHint(h, r, 2 γ₂) - r` in `ℤ_q`. Lemma 1(2) of the
Dilithium v3.1 specification bounds its centered representative by `2 γ₂ + 1`. -/
def hintResidual (q γ₂ : ℕ) (h : Bool) (r : ZMod q) : ZMod q :=
  ((useHint q γ₂ h r * (2 * γ₂ : ℕ) : ℤ) : ZMod q) - r

/-- The hinted high part is the original coefficient plus its residual. This is the scalar
identity used in Equation (9) of Section 6.2.1 of the Dilithium v3.1 specification. -/
theorem useHint_mul_eq_add_hintResidual (q γ₂ : ℕ) (h : Bool) (r : ZMod q) :
    ((useHint q γ₂ h r * (2 * γ₂ : ℕ) : ℤ) : ZMod q) =
      r + hintResidual q γ₂ h r :=
  (add_sub_cancel r _).symm

/-- `MakeHint` is set exactly when the correction changes the high bits. -/
@[simp] theorem makeHint_eq_true_iff {q γ₂ : ℕ} {z r : ZMod q} :
    makeHint q γ₂ z r = true ↔ highBits q γ₂ r ≠ highBits q γ₂ (r + z) := by
  simp [makeHint]

/-- `MakeHint` is clear exactly when the correction leaves the high bits unchanged. -/
@[simp] theorem makeHint_eq_false_iff {q γ₂ : ℕ} {z r : ZMod q} :
    makeHint q γ₂ z r = false ↔ highBits q γ₂ r = highBits q γ₂ (r + z) := by
  simp [makeHint]

/-- A clear hint returns the existing high bits. -/
@[simp] theorem useHint_false (q γ₂ : ℕ) (r : ZMod q) :
    useHint q γ₂ false r = highBits q γ₂ r := by
  simp [useHint]

variable {q γ₂ : ℕ}

private theorem bucketCount_pos (hγ : 0 < γ₂) (hq : 4 * γ₂ < q) :
    0 < (q - 1) / (2 * γ₂) :=
  Nat.div_pos (by omega) (by omega)

private theorem two_le_bucketCount (hγ : 0 < γ₂) (hq : 4 * γ₂ < q) :
    2 ≤ (q - 1) / (2 * γ₂) :=
  (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)

private theorem neg_one_emod_natCast {m : ℕ} (hm : 0 < m) :
    (-1 : ℤ) % (m : ℤ) = (m : ℤ) - 1 := by
  simpa using (Int.negSucc_emod 0 (b := (m : ℤ)) (by omega))

/-- Bucket shift direction `s ∈ {-1, 0, 1}` used by `useHint`. -/
private abbrev hintStep (q γ₂ : ℕ) (h : Bool) (r : ZMod q) : ℤ :=
  cond h (if 0 < lowBits q γ₂ r then 1 else -1) 0

/-- Wrap-around correction `w ∈ {-1, 0, 1}` when shifting `highBits q γ₂ r` modulo `m`. -/
private abbrev hintWrap (q γ₂ : ℕ) (h : Bool) (r : ZMod q) : ℤ :=
  let m : ℕ := (q - 1) / (2 * γ₂)
  if highBits q γ₂ r + hintStep q γ₂ h r < 0 then -1
  else if (m : ℤ) ≤ highBits q γ₂ r + hintStep q γ₂ h r then 1 else 0

private theorem hintStep_bounds (h : Bool) (r : ZMod q) :
    -1 ≤ hintStep q γ₂ h r ∧ hintStep q γ₂ h r ≤ 1 := by
  by_cases hpos : 0 < lowBits q γ₂ r <;> cases h <;>
    simp only [hintStep, Bool.cond_false, Bool.cond_true, hpos, ↓reduceIte] <;> omega

private theorem hintWrap_nonneg_of_pos (hγ : 0 < γ₂)
    {r : ZMod q} (hrpos : 0 < lowBits q γ₂ r) :
    0 ≤ hintWrap q γ₂ true r ∧ hintWrap q γ₂ true r ≤ 1 := by
  have hr₁₀ := highBits_nonneg (q := q) hγ r
  simp only [hintWrap, hintStep, Bool.cond_true, hrpos, ↓reduceIte]
  split_ifs <;> omega

private theorem hintWrap_nonpos_of_not_pos (hγ : 0 < γ₂) (hdvd : 2 * γ₂ ∣ q - 1)
    (hq : 4 * γ₂ < q) {r : ZMod q} (hrpos : ¬ 0 < lowBits q γ₂ r) :
    -1 ≤ hintWrap q γ₂ true r ∧ hintWrap q γ₂ true r ≤ 0 := by
  have hr₁m := highBits_lt (q := q) hγ hdvd (by omega) r
  simp only [hintWrap, hintStep, Bool.cond_true, hrpos, ↓reduceIte]
  split_ifs <;> omega

/-- Express `useHint` uniformly as `(highBits + s) % m` with `s ∈ {-1, 0, 1}`. -/
private theorem useHint_eq_add_emod (hγ : 0 < γ₂) (hdvd : 2 * γ₂ ∣ q - 1) (hq : 4 * γ₂ < q)
    (h : Bool) (r : ZMod q) :
    useHint q γ₂ h r =
      (highBits q γ₂ r + hintStep q γ₂ h r) % (((q - 1) / (2 * γ₂) : ℕ) : ℤ) := by
  cases h
  · have hr₁₀ := highBits_nonneg (q := q) hγ r
    have hr₁m := highBits_lt (q := q) hγ hdvd (by omega) r
    simp only [useHint_false, hintStep, Bool.cond_false, add_zero]
    exact (Int.emod_eq_of_lt hr₁₀ hr₁m).symm
  · simp only [useHint, hintStep, Bool.cond_true]
    split_ifs <;> simp only [sub_eq_add_neg]

/-- Shifted bucket index modulo `m` equals `a + s - w * m` for `w ∈ {-1, 0, 1}`. -/
private theorem add_emod_natCast_eq_sub_wrap {m : ℕ} (hm : 0 < m) {a s : ℤ}
    (ha₀ : 0 ≤ a) (ha : a < m) (hs₁ : -1 ≤ s) (hs₂ : s ≤ 1) :
    (a + s) % (m : ℤ) =
      a + s - (if a + s < 0 then (-1 : ℤ) else if (m : ℤ) ≤ a + s then 1 else 0) * m := by
  split_ifs with hlt hge
  · have hneg : a + s = -1 := by omega
    rw [hneg, neg_one_emod_natCast hm]; ring
  · have htop : a + s = m := by omega
    rw [htop, Int.emod_self]; ring
  · rw [Int.emod_eq_of_lt (by omega) (by omega)]; ring

/-- The `ZMod q` product of the shifted bucket index `useHint q γ₂ h r` and `2 γ₂`, recording the
wrap-around correction `hintWrap q γ₂ h r ∈ {-1, 0, 1}` coming from `m * (2 γ₂) ≡ -1 (mod q)`. -/
private theorem intCast_useHint_mul_eq_add_wrap (hγ : 0 < γ₂) (hdvd : 2 * γ₂ ∣ q - 1)
    (hq : 4 * γ₂ < q) (h : Bool) (r : ZMod q) :
    ((useHint q γ₂ h r * (2 * γ₂ : ℕ) : ℤ) : ZMod q) =
      ((highBits q γ₂ r * (2 * γ₂ : ℕ) + hintStep q γ₂ h r * (2 * γ₂ : ℕ) +
        hintWrap q γ₂ h r : ℤ) : ZMod q) := by
  have : NeZero q := ⟨by omega⟩
  have hm := bucketCount_pos hγ hq
  have hr₁₀ := highBits_nonneg (q := q) hγ r
  have hr₁m := highBits_lt (q := q) hγ hdvd (by omega) r
  have hqeq := natCast_eq_bucketCount_mul_add_one (q := q) (γ₂ := γ₂) hdvd
  have ⟨hs₁, hs₂⟩ := hintStep_bounds (q := q) (γ₂ := γ₂) h r
  have hmod := add_emod_natCast_eq_sub_wrap hm hr₁₀ hr₁m hs₁ hs₂
  rw [useHint_eq_add_emod hγ hdvd hq, hmod]
  calc
    (((highBits q γ₂ r + hintStep q γ₂ h r - hintWrap q γ₂ h r *
        ((q - 1) / (2 * γ₂) : ℕ)) * (2 * γ₂ : ℕ) : ℤ) : ZMod q) =
        ((highBits q γ₂ r * (2 * γ₂ : ℕ) + hintStep q γ₂ h r * (2 * γ₂ : ℕ) +
          hintWrap q γ₂ h r - hintWrap q γ₂ h r * q : ℤ) : ZMod q) := by
      congr 1
      rw [hqeq]
      ring
    _ = ((highBits q γ₂ r * (2 * γ₂ : ℕ) + hintStep q γ₂ h r * (2 * γ₂ : ℕ) +
          hintWrap q γ₂ h r : ℤ) : ZMod q) := by
      simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, mul_zero,
        sub_zero]

/-- The exceptional negative representatives next to zero are precisely the wrap-around bucket. -/
private theorem highBits_intCast_eq_zero_of_neg (hγ : 0 < γ₂) (hdvd : 2 * γ₂ ∣ q - 1)
    (hq : 4 * γ₂ < q) {c : ℤ} (hc₁ : -(γ₂ : ℤ) ≤ c) (hc₂ : c < 0) :
    highBits q γ₂ (c : ZMod q) = 0 := by
  have : NeZero q := ⟨by omega⟩
  have hqeq := natCast_eq_bucketCount_mul_add_one (q := q) (γ₂ := γ₂) hdvd
  have hv₀ := abs_le.mp (abs_lowBits_le (q := q) hγ (c : ZMod q))
  have hv₁₀ := highBits_nonneg (q := q) hγ (c : ZMod q)
  have hv₁m := highBits_lt (q := q) hγ hdvd (by omega) (c : ZMod q)
  have hmul_hi : highBits q γ₂ (c : ZMod q) * (2 * γ₂ : ℕ) ≤
      (((q - 1) / (2 * γ₂) : ℕ) - 1) * (2 * γ₂ : ℕ) :=
    mul_le_mul_of_nonneg_right (by omega) (by positivity)
  have hdvd_sub : (q : ℤ) ∣
      highBits q γ₂ (c : ZMod q) * (2 * γ₂ : ℕ) + lowBits q γ₂ (c : ZMod q) - c :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp
      (intCast_highBits_mul_add_lowBits (γ₂ := γ₂) (c : ZMod q)).symm
  have hdiff0 :
      highBits q γ₂ (c : ZMod q) * (2 * γ₂ : ℕ) + lowBits q γ₂ (c : ZMod q) - c = 0 := by
    refine Int.eq_zero_of_abs_lt_dvd hdvd_sub (abs_lt.mpr ?_)
    have hmul₀ : 0 ≤ highBits q γ₂ (c : ZMod q) * (2 * γ₂ : ℕ) := by positivity
    push_cast at hqeq hmul₀ hmul_hi ⊢
    constructor <;> linarith
  by_contra hne
  have hge : 2 * (γ₂ : ℤ) ≤ highBits q γ₂ (c : ZMod q) * (2 * γ₂ : ℕ) :=
    le_mul_of_one_le_left (Nat.cast_nonneg _) (by omega)
  push_cast at hdiff0 hge
  omega

/-- Extending `highBits_intCast_mul_add` to the boundary `b = -γ₂` when `a = 0`. -/
private theorem highBits_intCast_mul_add_of_le (hγ : 0 < γ₂) (hdvd : 2 * γ₂ ∣ q - 1)
    (hq : 4 * γ₂ < q) {a b : ℤ} (ha₀ : 0 ≤ a) (ha : a < ((q - 1) / (2 * γ₂) : ℕ))
    (hb₁ : -(γ₂ : ℤ) ≤ b) (hb₂ : b ≤ γ₂) (hwrap : b = -(γ₂ : ℤ) → a = 0) :
    highBits q γ₂ ((a * (2 * γ₂ : ℕ) + b : ℤ) : ZMod q) = a := by
  have : NeZero q := ⟨by omega⟩
  rcases lt_or_eq_of_le hb₁ with hlt | hb
  · exact highBits_intCast_mul_add hγ hdvd ha₀ ha hlt hb₂
  · rw [hwrap hb.symm, zero_mul, zero_add]
    exact highBits_intCast_eq_zero_of_neg hγ hdvd hq hb₁ (by omega)

/-- `UseHint` always returns a nonnegative bucket index under the source parameter hypotheses. -/
theorem useHint_nonneg (hγ : 0 < γ₂) (hq : 4 * γ₂ < q) (h : Bool) (r : ZMod q) :
    0 ≤ useHint q γ₂ h r := by
  cases h
  · exact highBits_nonneg hγ r
  · simp only [useHint]
    split <;> exact Int.emod_nonneg _ (Nat.cast_pos.mpr (bucketCount_pos hγ hq)).ne'

/-- `UseHint` returns an index below the number `(q - 1) / (2 γ₂)` of high-order buckets. -/
theorem useHint_lt (hγ : 0 < γ₂) (hdvd : 2 * γ₂ ∣ q - 1) (hq : 4 * γ₂ < q)
    (h : Bool) (r : ZMod q) : useHint q γ₂ h r < ((q - 1) / (2 * γ₂) : ℕ) := by
  cases h
  · exact highBits_lt hγ hdvd (by omega) r
  · simp only [useHint]
    split <;> exact Int.emod_lt_of_pos _ (Nat.cast_pos.mpr (bucketCount_pos hγ hq))

/-- A set hint never produces the unadjusted high bits. This is the scalar separation underlying
Lemma 1(3) of the Dilithium v3.1 specification. -/
theorem useHint_true_ne_highBits (hγ : 0 < γ₂) (hdvd : 2 * γ₂ ∣ q - 1)
    (hq : 4 * γ₂ < q) (r : ZMod q) : useHint q γ₂ true r ≠ highBits q γ₂ r := by
  have hm2 : 2 ≤ (q - 1) / (2 * γ₂) := two_le_bucketCount hγ hq
  have ⟨hs₁, hs₂⟩ := hintStep_bounds (q := q) (γ₂ := γ₂) true r
  rw [useHint_eq_add_emod hγ hdvd hq, add_emod_natCast_eq_sub_wrap (bucketCount_pos hγ hq)
    (highBits_nonneg hγ r) (highBits_lt hγ hdvd (by omega) r) hs₁ hs₂]
  simp only [hintStep, Bool.cond_true]
  split_ifs <;> omega

/-- **Hint injectivity.** For a fixed coefficient, equal `UseHint` outputs imply equal hint bits.
This is the scalar form of Lemma 1(3) in the Dilithium v3.1 specification. -/
theorem useHint_injective (hγ : 0 < γ₂) (hdvd : 2 * γ₂ ∣ q - 1) (hq : 4 * γ₂ < q)
    (r : ZMod q) : Function.Injective fun h : Bool => useHint q γ₂ h r := by
  intro h h' heq
  cases h <;> cases h'
  exacts [rfl, absurd heq.symm (useHint_true_ne_highBits hγ hdvd hq r),
    absurd heq (useHint_true_ne_highBits hγ hdvd hq r), rfl]

/-- **Arbitrary-hint residual bound.** For every hint bit and coefficient, the centered residual
between `r` and `2 γ₂ · UseHint(h, r, 2 γ₂)` has magnitude at most `2 γ₂ + 1`. This is the scalar
norm statement in Lemma 1(2) of the Dilithium v3.1 specification. The vector lemma additionally
states that only set-hint positions can exceed `γ₂`; that sparsity refinement is separate. -/
theorem abs_hintResidual_valMinAbs_le (hγ : 0 < γ₂) (hdvd : 2 * γ₂ ∣ q - 1)
    (hq : 4 * γ₂ < q) (h : Bool) (r : ZMod q) :
    |(hintResidual q γ₂ h r).valMinAbs| ≤ 2 * γ₂ + 1 := by
  have : NeZero q := ⟨by omega⟩
  have hr₀ := abs_le.mp (abs_lowBits_le (q := q) hγ r)
  have hres : hintResidual q γ₂ h r =
      ((hintStep q γ₂ h r * (2 * γ₂ : ℕ) + hintWrap q γ₂ h r -
        lowBits q γ₂ r : ℤ) : ZMod q) := by
    rw [hintResidual, intCast_useHint_mul_eq_add_wrap hγ hdvd hq h r]
    conv_lhs => rhs; rw [← intCast_highBits_mul_add_lowBits (γ₂ := γ₂) r]
    push_cast; ring
  rw [hres]
  refine (ZMod.abs_valMinAbs_intCast_le _).trans (abs_le.mpr ?_)
  push_cast
  cases h
  · have hr₁₀ := highBits_nonneg (q := q) hγ r
    have hr₁m := highBits_lt (q := q) hγ hdvd (by omega) r
    simp only [hintWrap, hintStep, Bool.cond_false, add_zero, zero_mul, zero_add]
    split_ifs <;> omega
  · by_cases hrpos : 0 < lowBits q γ₂ r
    · have hw := hintWrap_nonneg_of_pos hγ hrpos
      simp only [hintStep, Bool.cond_true, hrpos, ↓reduceIte, one_mul]; omega
    · have hw := hintWrap_nonpos_of_not_pos hγ hdvd hq hrpos
      simp only [hintStep, Bool.cond_true, hrpos, ↓reduceIte, neg_one_mul]; omega

/-- **Hint recovery.** If `|z| ≤ γ₂`, using the hint made from `z` and `r` recovers the high bits
of `r + z`. This is the scalar form of Lemma 1(1) in the Dilithium v3.1 specification, with its
`α` specialized to `2 γ₂`. -/
theorem useHint_makeHint (hγ : 0 < γ₂) (hdvd : 2 * γ₂ ∣ q - 1) (hq : 4 * γ₂ < q)
    {z r : ZMod q} (hz : |z.valMinAbs| ≤ γ₂) :
    useHint q γ₂ (makeHint q γ₂ z r) r = highBits q γ₂ (r + z) := by
  have : NeZero q := ⟨by omega⟩
  by_cases heq : highBits q γ₂ r = highBits q γ₂ (r + z)
  · rw [makeHint_eq_false_iff.mpr heq, useHint_false, heq]
  · rw [makeHint_eq_true_iff.mpr heq]
    have hr₀ := abs_le.mp (abs_lowBits_le (q := q) hγ r)
    have hz₀ := abs_le.mp hz
    have hr₁₀ := highBits_nonneg (q := q) hγ r
    have hr₁m := highBits_lt (q := q) hγ hdvd (by omega) r
    have hsum : r + z =
        ((highBits q γ₂ r * (2 * γ₂ : ℕ) +
          (lowBits q γ₂ r + z.valMinAbs) : ℤ) : ZMod q) := by
      rw [← add_assoc, Int.cast_add, intCast_highBits_mul_add_lowBits, ZMod.coe_valMinAbs]
    have hnot : ¬ (-(γ₂ : ℤ) ≤ lowBits q γ₂ r + z.valMinAbs ∧
        lowBits q γ₂ r + z.valMinAbs ≤ γ₂ ∧
        (lowBits q γ₂ r + z.valMinAbs = -(γ₂ : ℤ) → highBits q γ₂ r = 0)) := by
      rintro ⟨hlo, hhi, hwrap⟩
      exact heq (hsum ▸ (highBits_intCast_mul_add_of_le hγ hdvd hq hr₁₀ hr₁m hlo hhi hwrap).symm)
    have huse := intCast_useHint_mul_eq_add_wrap hγ hdvd hq true r
    set a' : ℤ := useHint q γ₂ true r
    set b' : ℤ := lowBits q γ₂ r + z.valMinAbs -
      hintStep q γ₂ true r * (2 * γ₂ : ℕ) - hintWrap q γ₂ true r
    have hsum' : r + z = ((a' * (2 * γ₂ : ℕ) + b' : ℤ) : ZMod q) := by
      simp only [hsum, a', b', Int.cast_add, Int.cast_sub, huse]
      ring
    have hb : -(γ₂ : ℤ) ≤ b' ∧ b' ≤ γ₂ ∧ (b' = -(γ₂ : ℤ) → a' = 0) := by
      by_cases hrpos : 0 < lowBits q γ₂ r
      · have hw := hintWrap_nonneg_of_pos hγ hrpos
        have hgt : (γ₂ : ℤ) < lowBits q γ₂ r + z.valMinAbs := by
          by_contra h; exact hnot ⟨by omega, by omega, by omega⟩
        have hb'_eq : b' = lowBits q γ₂ r + z.valMinAbs - 2 * γ₂ - hintWrap q γ₂ true r := by
          simp only [b', hintStep, Bool.cond_true, hrpos, ↓reduceIte, one_mul]; push_cast; ring
        refine ⟨by omega, by omega, fun hbeq => ?_⟩
        have htop : highBits q γ₂ r + 1 = ((q - 1) / (2 * γ₂) : ℕ) := by
          simp only [hintWrap, hintStep, Bool.cond_true, hrpos, ↓reduceIte] at hb'_eq
          split_ifs at hb'_eq <;> omega
        simp only [a', useHint, hrpos, ↓reduceIte, htop, Int.emod_self]
      · have hw := hintWrap_nonpos_of_not_pos hγ hdvd hq hrpos
        have hb'_eq : b' = lowBits q γ₂ r + z.valMinAbs + 2 * γ₂ - hintWrap q γ₂ true r := by
          simp only [b', hintStep, Bool.cond_true, hrpos, ↓reduceIte, neg_one_mul]; push_cast; ring
        have hhi' : lowBits q γ₂ r + z.valMinAbs - hintWrap q γ₂ true r ≤ -(γ₂ : ℤ) :=
          le_of_not_gt fun h => hnot ⟨by omega, by omega,
            fun _ => by
              simp only [hintWrap, hintStep, Bool.cond_true, hrpos, ↓reduceIte] at h
              split_ifs at h <;> omega⟩
        exact ⟨by omega, by omega, by omega⟩
    exact hsum' ▸ (highBits_intCast_mul_add_of_le hγ hdvd hq (useHint_nonneg hγ hq true r)
      (useHint_lt hγ hdvd hq true r) hb.1 hb.2.1 hb.2.2).symm

/-- Apply `MakeHint` coefficientwise. -/
def makeHintVec {ι : Type*} (q γ₂ : ℕ) (z r : ι → ZMod q) : ι → Bool :=
  fun i => makeHint q γ₂ (z i) (r i)

/-- Apply `UseHint` coefficientwise. -/
def useHintVec {ι : Type*} (q γ₂ : ℕ) (h : ι → Bool) (r : ι → ZMod q) : ι → ℤ :=
  fun i => useHint q γ₂ (h i) (r i)

/-- Coefficientwise hint recovery. -/
theorem useHintVec_makeHintVec {ι : Type*} (hγ : 0 < γ₂) (hdvd : 2 * γ₂ ∣ q - 1)
    (hq : 4 * γ₂ < q) {z r : ι → ZMod q} (hz : ∀ i, |(z i).valMinAbs| ≤ γ₂) :
    useHintVec q γ₂ (makeHintVec q γ₂ z r) r = fun i => highBits q γ₂ (r i + z i) :=
  funext fun i => useHint_makeHint hγ hdvd hq (hz i)

end Cslib.Crypto.MLDSA
