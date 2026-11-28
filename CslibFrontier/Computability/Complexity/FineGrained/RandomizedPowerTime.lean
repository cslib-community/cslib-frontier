/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.FineGrained.PowerTime
public import CslibFrontier.Computability.Complexity.FineGrained.Randomized
import CslibFrontier.Computability.Complexity.FineGrained.Bounds
import CslibFrontier.Computability.Complexity.FineGrained.Padding
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime

/-!
# Randomized time bounds with a power in the exponent

The power-exponential time bound for seeded promise solvers uses the same parameter and
encoded-length factors as the deterministic bound.

## Main definitions

* `Cslib.Complexity.SolvesWithErrorInPowerExpTime`: a worst-case time bound for seeded solvers.

## Main results

* `Cslib.Complexity.solvesWithErrorInPowerExpTime_deterministic_iff`: at zero error, the
  bound for a language agrees with deterministic decidability.
* `Cslib.Complexity.SolvesWithErrorInPowerExpTime.of_promiseReduction`: transfer the power
  bound through a deterministic promise reduction.
* `Cslib.Complexity.SolvesWithErrorInPowerExpTime.of_seededVerifier`: allocate a unary seed
  when the verifier's error guarantees hold at every length above a power-exponential bound.
* `Cslib.Complexity.SolvesWithErrorInPowerExpTime.exists_amplifiedVerifier`: amplify with an
  input-dependent unary error schedule, preserving the power in the time bound.
-/

public section

namespace Cslib.Complexity

open PromiseProblem Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool} {μ : α → ℕ} {p : ℝ}

/-- A solver with error profile `E` runs in time
`2 ^ (C * (μ a + 1) ^ p) * (L + 1) ^ e` up to constant factors for some `C,e : ℕ`,
where `L` is the encoded input length. The time bound holds on every seed. -/
@[expose] def SolvesWithErrorInPowerExpTime (Q : PromiseProblem α) (enc : α ↪ List Bool)
    (E : ErrorModel) (μ : α → ℕ) (p : ℝ) : Prop :=
  ∃ C e : ℕ, SolvesWithErrorInTimeO Q enc E
    fun a => (2 : ℝ) ^ (C * (μ a + 1 : ℝ) ^ p) * ((enc a).length + 1) ^ e

/-- Relaxing the error profile preserves the power-exponential running time. -/
theorem SolvesWithErrorInPowerExpTime.mono_error {Q : PromiseProblem α} {E₁ E₂ : ErrorModel}
    (h : SolvesWithErrorInPowerExpTime Q enc E₁ μ p) (hE : E₁ ≤ E₂) :
    SolvesWithErrorInPowerExpTime Q enc E₂ μ p := by
  obtain ⟨C, e, h⟩ := h
  exact ⟨C, e, h.mono_error hE⟩

/-- A verifier whose error guarantees hold at every seed length above a power-exponential
threshold yields a seeded solver. The chosen seed length is computable in unary, and the
solver accounts for generating it and running on the full framed input at a power below one. -/
theorem SolvesWithErrorInPowerExpTime.of_seededVerifier {Q : PromiseProblem α} {E : ErrorModel}
    (hμ : ComputableInPolyTime μ enc encUnary) (hp : p < 1) {V : α × List Bool → Bool}
    (hV : ComputableInPowerExpTime V (encPair enc encBits) encBool (μ ∘ Prod.fst) p)
    (A e : ℕ)
    (hyes : ∀ a ∈ Q.yes, ∀ n : ℕ,
      (2 : ℝ) ^ (A * (μ a + 1 : ℝ) ^ p) * ((enc a).length + 1) ^ e ≤ n →
      (acceptCount (fun x => !V x) a n : ℝ) ≤ E.yesErr * (2 : ℝ) ^ n)
    (hno : ∀ a ∈ Q.no, ∀ n : ℕ,
      (2 : ℝ) ^ (A * (μ a + 1 : ℝ) ^ p) * ((enc a).length + 1) ^ e ≤ n →
      (acceptCount V a n : ℝ) ≤ E.noErr * (2 : ℝ) ^ n) :
    ∃ q : ℝ, p < q ∧ 0 < q ∧ q < 1 ∧ SolvesWithErrorInPowerExpTime Q enc E μ q := by
  obtain ⟨q, ℓ, hpq, hq₀, hq₁, ⟨C, d, hℓ⟩, hwidth⟩ :=
    exists_computableInPowerExpTime_unary_majorant hμ hp A e
  obtain ⟨tℓ, c, hℓ, htℓ⟩ := hℓ.exists_computableInO
  obtain ⟨l, hlen⟩ := hℓ.length_le_time
  obtain ⟨D, f, hV⟩ := hV
  obtain ⟨tV, k, hV, htV⟩ := hV.exists_computableInO
  let d' := max d 1
  let P (a : α) : ℝ := 2 ^ (C * (μ a + 1 : ℝ) ^ q) * ((enc a).length + 1) ^ d'
  let X (a : α) : ℝ := 2 ^ (D * (μ a + 1 : ℝ) ^ p)
  let K := 2 * c + 1
  let J := l * K + 3
  let M := 1 + k * (2 * J + 1) ^ f + k
  refine ⟨q, hpq, hq₀, hq₁, ⌈(D : ℝ)⌉₊ + C * (f + 1), d' * (f + 1),
    ℓ, V, tℓ, tℓ, tV, tV, K + M, hℓ, hV, ?_,
    fun a ha => hyes a ha (ℓ a) (hwidth a), fun a ha => hno a ha (ℓ a) (hwidth a)⟩
  intro a w hw
  have hP : ((enc a).length + 1 : ℝ) ≤ P a := by
    simpa only [pow_one] using pow_le_two_rpow_mul_pow (L := (enc a).length) (d := 1)
      (x := C * (μ a + 1 : ℝ) ^ q) (by positivity) (le_max_right d 1)
  have hP₁ : 1 ≤ P a := (le_add_of_nonneg_left (Nat.cast_nonneg _)).trans hP
  have hX₁ : 1 ≤ X a := Real.one_le_rpow one_le_two (by positivity)
  have ht : (tℓ a : ℝ) ≤ (2 * c : ℝ) * P a :=
    le_two_mul_mul_of_le_mul_add (htℓ a)
      (two_rpow_mul_pow_le_two_rpow_mul_pow le_rfl (le_max_left d 1)) hP₁
  have hstart : ((enc a).length : ℝ) + tℓ a ≤ K * P a := by
    rw [show (K : ℝ) = 2 * c + 1 by simp [K]]
    linarith
  have hseed : (w.length : ℝ) ≤ l * ((tℓ a : ℝ) + 1) := by
    rw [hw]
    have h := hlen a
    rw [encUnary_apply, List.length_replicate] at h
    exact_mod_cast h
  have hframe : ((encPair enc encBits (a, w)).length : ℝ) ≤ J * (P a + 1) := by
    have hK : (1 : ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by dsimp only [K]; omega)
    have hseed' : (w.length : ℝ) ≤ l * (K * (P a + 1)) :=
      hseed.trans (mul_le_mul_of_nonneg_left
        (by linarith [show (0 : ℝ) ≤ (enc a).length from Nat.cast_nonneg _]) (Nat.cast_nonneg l))
    have hprefix : 2 * ((enc a).length : ℝ) + 1 ≤ 3 * (P a + 1) := by linarith
    simp only [length_encPair, encBits_apply, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_one]
    refine (add_le_add hprefix hseed').trans_eq ?_
    simp only [J, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring
  have hverifier := reduction_add_time_le hP₁ hX₁ (C := 1) zero_le_one hframe
    (show X a ≤ 1 * X a by rw [one_mul]) (htV (a, w))
  have hstep : (tV (a, w) : ℝ) ≤ M * (X a * P a ^ (f + 1)) := by
    have hMv : (M : ℝ) = 1 + k * (2 * J + 1 : ℝ) ^ f + k := by
      simp [M]
    rw [hMv]
    rw [mul_one] at hverifier
    linarith
  have hlarge : P a ≤ X a * P a ^ (f + 1) :=
    (le_self_pow₀ hP₁ (Nat.succ_ne_zero f)).trans
      (le_mul_of_one_le_left (by positivity) hX₁)
  have hwork : ((enc a).length : ℝ) + tℓ a + tV (a, w) ≤
      (K + M : ℕ) * (X a * P a ^ (f + 1)) := by
    rw [Nat.cast_add]
    linarith [mul_le_mul_of_nonneg_left hlarge (Nat.cast_nonneg K)]
  have henv := power_reduction_envelope_le (C := C) (d := d') (e := f)
    (x := (μ a + 1 : ℝ)) (y := ((enc a).length + 1 : ℝ)) (R := (D : ℝ))
    (q := q) (r := p) (le_add_of_nonneg_left (Nat.cast_nonneg _))
    (by positivity) (Nat.cast_nonneg D)
  rw [max_eq_left hpq.le] at henv
  exact (hwork.trans (mul_le_mul_of_nonneg_left henv (Nat.cast_nonneg (K + M)))).trans
    (le_add_of_nonneg_right (Nat.cast_nonneg (K + M)))

/-- A polynomial-time unary schedule `target` can lower bounded two-sided error to
`(1 / 3) / 2 ^ target a` by strict majority. Both the amplified unary seed length and the
verifier retain the solver's power in the exponent. The verifier's bound charges the length
of the whole framed seed input and applies even to seeds of a different length. -/
theorem SolvesWithErrorInPowerExpTime.exists_amplifiedVerifier {Q : PromiseProblem α}
    {target : α → ℕ} (htarget : ComputableInPolyTime target enc encUnary)
    (h : SolvesWithErrorInPowerExpTime Q enc ErrorModel.bounded μ p) :
    ∃ (width : α → ℕ) (verify : α × List Bool → Bool),
      ComputableInPowerExpTime width enc encUnary μ p ∧
      ComputableInPowerExpTime verify (encPair enc encBits) encBool (μ ∘ Prod.fst) p ∧
      (∀ a ∈ Q.yes, (acceptCount (fun x => !verify x) a (width a) : ℝ) ≤
        ((1 / 3 : ℝ) / 2 ^ target a) * 2 ^ width a) ∧
      (∀ a ∈ Q.no, (acceptCount verify a (width a) : ℝ) ≤
        ((1 / 3 : ℝ) / 2 ^ target a) * 2 ^ width a) := by
  obtain ⟨C, e, ℓ, V, Tℓ, Sℓ, Tv, Sv, c, hℓ, hV, htime, hyes, hno⟩ := h
  let rounds (a : α) := 10 * (target a + 1)
  have hrounds : ComputableInPolyTime rounds enc encUnary :=
    ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 10)
      (ComputableInPolyTime.unary_add' htarget (ComputableInPolyTime.const 1))
  obtain ⟨Tr, Sr, hTr, _, hr⟩ := hrounds.exists_computableInO
  obtain ⟨cr, hlenR⟩ := hr.length_le_time
  obtain ⟨cℓ, hlenℓ⟩ := hℓ.length_le_time
  let X (a : α) : ℝ := 2 ^ (C * (μ a + 1 : ℝ) ^ p)
  let P (a : α) : ℝ := X a * ((enc a).length + 1) ^ e
  let R (a : α) : ℕ := ⌈c * P a + c⌉₊
  have hTℓ (a : α) : (Tℓ a : ℝ) ≤ c * P a + c := by
    have ht := htime a (List.replicate (ℓ a) false) (List.length_replicate ..)
    push_cast at ht
    linarith [Nat.cast_nonneg (α := ℝ) (enc a).length,
      Nat.cast_nonneg (α := ℝ) (Tv (a, List.replicate (ℓ a) false))]
  have hR (a : α) (w : List Bool) (hw : w.length = ℓ a) : Tv (a, w) ≤ R a := by
    have ht := htime a w hw
    push_cast at ht
    have ht' : (Tv (a, w) : ℝ) ≤ c * P a + c := by
      linarith [Nat.cast_nonneg (α := ℝ) (enc a).length, Nat.cast_nonneg (α := ℝ) (Tℓ a)]
    exact Nat.cast_le.mp (ht'.trans (Nat.le_ceil _))
  obtain ⟨d, f, g, _, _, hwidth, hverify, herror⟩ :=
    computableInO_amplifySeededMajority hℓ hr hV hR
  obtain ⟨K, b, hTr'⟩ := hTr.exists_le
  let E := max (max e b) 1
  let size (a : α) (l : ℕ) := ⌈X a * (l + 1 : ℝ) ^ E⌉₊
  have hbounds {β : Type} (a : β → α) (l : β → ℕ) (hl : ∀ x, (enc (a x)).length ≤ l x) :
      let size' (x : β) := size (a x) (l x)
      PolyBounded size' l ∧ PolyBounded size' (Tr ∘ a) ∧ PolyBounded size' (rounds ∘ a) ∧
        PolyBounded size' (Tℓ ∘ a) ∧ PolyBounded size' (ℓ ∘ a) ∧
        PolyBounded size' (R ∘ a) := by
    intro size'
    have hX (x : β) : 1 ≤ X (a x) := Real.one_le_rpow one_le_two (by positivity)
    have hL (x : β) : 1 ≤ (l x + 1 : ℝ) := le_add_of_nonneg_left (Nat.cast_nonneg _)
    have hfull (x : β) : X (a x) * (l x + 1 : ℝ) ^ E ≤ size' x := Nat.le_ceil _
    have hl' (x : β) : l x ≤ size' x := by
      have h := (pow_le_pow_right₀ (hL x) (le_max_right (max e b) 1)).trans
        ((le_mul_of_one_le_left (by positivity) (hX x)).trans (hfull x))
      rw [pow_one] at h
      exact Nat.cast_le.mp ((le_add_of_nonneg_right zero_le_one).trans h)
    have hbound (m : ℕ) (hm : m ≤ E) (x : β) :
        (((enc (a x)).length : ℝ) + 1) ^ m ≤ (l x + 1 : ℝ) ^ E :=
      (pow_le_pow_left₀ (by positivity)
        (add_le_add_left (Nat.cast_le.mpr (hl x)) 1) _).trans (pow_le_pow_right₀ (hL x) hm)
    have hP (x : β) : P (a x) ≤ size' x :=
      (mul_le_mul_of_nonneg_left (hbound e ((le_max_left e b).trans (le_max_left _ _)) x)
        (zero_le_one.trans (hX x))).trans (hfull x)
    have hTr'' (x : β) : Tr (a x) ≤ K * size' x := by
      have h := (hbound b ((le_max_right e b).trans (le_max_left _ _)) x).trans
        ((le_mul_of_one_le_left (by positivity) (hX x)).trans (hfull x))
      have hb' : ((enc (a x)).length + 1) ^ b ≤ size' x := by exact_mod_cast h
      exact (hTr' (a x)).trans (Nat.mul_le_mul_left K hb')
    have hcost (x : β) : c * P (a x) + c ≤ (c * size' x + c : ℕ) := by
      push_cast
      exact add_le_add_left (mul_le_mul_of_nonneg_left (hP x) (Nat.cast_nonneg c)) _
    have hTℓ' (x : β) : Tℓ (a x) ≤ c * size' x + c :=
      Nat.cast_le.mp ((hTℓ (a x)).trans (hcost x))
    have hR' (x : β) : R (a x) ≤ c * size' x + c :=
      Nat.ceil_le.mpr (hcost x)
    have hTr₀ : PolyBounded size' (Tr ∘ a) := ((PolyBounded.const K).mul .self).mono hTr''
    have hTℓ₀ : PolyBounded size' (Tℓ ∘ a) :=
      (((PolyBounded.const c).mul .self).add (.const c)).mono hTℓ'
    refine ⟨PolyBounded.self.mono hl', hTr₀, ?_, hTℓ₀, ?_,
      (((PolyBounded.const c).mul .self).add (.const c)).mono hR'⟩
    · refine ((PolyBounded.const cr).mul (hTr₀.add (.const 1))).mono fun x => ?_
      simpa only [encUnary_apply, List.length_replicate, Function.comp_apply] using hlenR (a x)
    · refine ((PolyBounded.const cℓ).mul (hTℓ₀.add (.const 1))).mono fun x => ?_
      simpa only [encUnary_apply, List.length_replicate, Function.comp_apply] using hlenℓ (a x)
  have hof {β γ : Type} {enc' : β ↪ List Bool} {out : γ ↪ List Bool} {F : β → γ}
      {t s : β → ℕ} (a : β → α) (hF : ComputableInO F enc' out t s)
      (ht : PolyBounded (fun x => size (a x) (enc' x).length) t) :
      ComputableInPowerExpTime F enc' out (μ ∘ a) p := by
    obtain ⟨M, j, hM⟩ := ht.exists_le
    refine ⟨C * j, E * j,
      (ComputableInTimeO.of_computableInO hF (T := fun x =>
        ((M * 3 ^ j : ℕ) : ℝ) *
          ((2 : ℝ) ^ (((C * j : ℕ) : ℝ) * (μ (a x) + 1 : ℝ) ^ p) *
            ((enc' x).length + 1 : ℝ) ^ (E * j))) ?_).mono
        (M * 3 ^ j) (fun _ => le_add_of_nonneg_right (Nat.cast_nonneg _)) (fun _ => by positivity)⟩
    intro x
    let L : ℝ := (enc' x).length + 1
    let Y := X (a x) * L ^ E
    have hY : 1 ≤ Y :=
      one_le_mul_of_one_le_of_one_le (Real.one_le_rpow one_le_two (by positivity))
        (one_le_pow₀ (le_add_of_nonneg_left (Nat.cast_nonneg _)))
    have hcap : (size (a x) (enc' x).length : ℝ) + 1 ≤ 3 * Y := by
      have h := (Nat.ceil_lt_add_one (show 0 ≤ Y from zero_le_one.trans hY)).le
      change (⌈Y⌉₊ : ℝ) + 1 ≤ 3 * Y
      linarith
    have hclock : (t x : ℝ) ≤ M * ((size (a x) (enc' x).length : ℝ) + 1) ^ j := by
      exact_mod_cast hM x
    refine hclock.trans ((mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hcap j) (Nat.cast_nonneg M)).trans_eq ?_)
    change (M : ℝ) * (3 * (X (a x) * L ^ E)) ^ j =
      ((M * 3 ^ j : ℕ) : ℝ) *
        (2 ^ (((C * j : ℕ) : ℝ) * (μ (a x) + 1 : ℝ) ^ p) * L ^ (E * j))
    rw [mul_pow, mul_pow, ← pow_mul]
    have hXj : X (a x) ^ j = (2 : ℝ) ^ (((C * j : ℕ) : ℝ) * (μ (a x) + 1 : ℝ) ^ p) := by
      dsimp only [X]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), Nat.cast_mul]
      congr 1
      ring
    rw [hXj]
    push_cast
    ring
  have hw := hof id hwidth (by
    obtain ⟨hL, hR, hround, hT, hℓ', _⟩ := hbounds id (fun a => (enc a).length) (fun _ => le_rfl)
    have hsetup := (((PolyBounded.const 4).mul hround).add hℓ').add (.const 2)
    exact ((hL.add ((PolyBounded.const 2).mul hR)).add hT).add (hsetup.pow d))
  have hv := hof Prod.fst hverify (by
    obtain ⟨hL, hTr', hround, hT, _, hR'⟩ := hbounds Prod.fst
      (fun x => (encPair enc encBits x).length) (length_le_encPair_left enc encBits)
    have hn := ((PolyBounded.const 2).mul hround).add (.const 1)
    have hsetup := ((((PolyBounded.const 4).mul hL).add
      ((PolyBounded.const 2).mul hTr')).add hT).add (.const 1)
    exact (hn.mul ((hsetup.pow f).add hR')).add (hn.pow g))
  have hrates (a : α) : (4 * (1 / 3 : ℝ) * (1 - 1 / 3)) ^ rounds a ≤
      (1 / 3 : ℝ) / 2 ^ target a := by
    rw [show (4 * (1 / 3 : ℝ) * (1 - 1 / 3)) = 8 / 9 by norm_num]
    dsimp only [rounds]
    rw [pow_mul]
    calc
      _ ≤ (1 / 3 : ℝ) ^ (target a + 1) := pow_le_pow_left₀ (by positivity) (by norm_num) _
      _ ≤ (1 / 3 : ℝ) * (1 / 2) ^ target a := by
        rw [pow_succ']
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) (by norm_num) _) (by positivity)
      _ = _ := by simp only [div_eq_mul_inv, one_mul, inv_pow]
  have herrEq (a : α) (truth : Bool) (he :
      (acceptCount (fun p => V p != truth) a (ℓ a) : ℝ) ≤ (1 / 3 : ℝ) * 2 ^ ℓ a) :=
    (herror a truth (by norm_num) (by norm_num) he).trans
      (mul_le_mul_of_nonneg_right (hrates a) (by positivity))
  refine ⟨_, _, hw, hv, fun a ha => ?_, fun a ha => ?_⟩
  · simpa only [Bool.bne_true] using herrEq a true
      (by simpa only [Bool.bne_true, ErrorModel.bounded, ErrorModel.twoSided] using hyes a ha)
  · simpa only [Bool.bne_false] using herrEq a false
      (by simpa only [Bool.bne_false, ErrorModel.bounded, ErrorModel.twoSided] using hno a ha)

/-- Zero-error seeded solvers of a language and deterministic deciders have the same power
bound. The polynomial factor can absorb the cost of reading the encoded input. -/
theorem solvesWithErrorInPowerExpTime_deterministic_iff {A : Set α} :
    SolvesWithErrorInPowerExpTime (ofSet A) enc ErrorModel.deterministic μ p ↔
      DecidableInPowerExpTime A enc μ p := by
  let time (C e : ℕ) (a : α) :=
    (2 : ℝ) ^ (C * (μ a + 1 : ℝ) ^ p) * ((enc a).length + 1) ^ e
  have hlen (C e : ℕ) (a : α) : ((enc a).length : ℝ) ≤ time C (max e 1) a := by
    have h := pow_le_two_rpow_mul_pow (L := (enc a).length) (d := 1)
      (x := C * (μ a + 1 : ℝ) ^ p) (by positivity) (le_max_right e 1)
    rw [pow_one] at h
    exact (le_add_of_nonneg_right zero_le_one).trans h
  have hpad (C e : ℕ) (a : α) :
      time C e a ≤ (↑(1 : ℕ) : ℝ) * time C (max e 1) a + ↑(1 : ℕ) := by
    rw [Nat.cast_one, one_mul]
    exact (two_rpow_mul_pow_le_two_rpow_mul_pow le_rfl (le_max_left e 1) :
      time C e a ≤ time C (max e 1) a).trans (le_add_of_nonneg_right zero_le_one)
  have hnonneg (C e : ℕ) (a : α) : 0 ≤ time C (max e 1) a := by
    dsimp only [time]
    positivity
  have hbridge (C e : ℕ) :
      SolvesWithErrorInTimeO (ofSet A) enc ErrorModel.deterministic (time C (max e 1)) ↔
        DecidableInTimeO A enc (time C (max e 1)) :=
    (solvesWithErrorInTimeO_deterministic_iff (hlen C e)).trans solvesPromiseInTimeO_ofSet_iff
  constructor
  · rintro ⟨C, e, h⟩
    exact ⟨C, max e 1, (hbridge C e).mp (h.mono 1 (hpad C e) (hnonneg C e))⟩
  · rintro ⟨C, e, h⟩
    exact ⟨C, max e 1, (hbridge C e).mpr (h.mono 1 (hpad C e) (hnonneg C e))⟩

/-- A deterministic promise reduction of power `q` with parameter blowup
`O((μA + 1) ^ b)` transports a target solver of power `p ≥ 0` to power `max q (b * p)`,
preserving its error profile. The reduction's time also bounds the length it writes. -/
theorem SolvesWithErrorInPowerExpTime.of_promiseReduction {β : Type} {encB : β ↪ List Bool}
    {A : PromiseProblem α} {B : PromiseProblem β} {E : ErrorModel} {μB : β → ℕ} {r : α → β}
    {q b : ℝ} (hr : ComputableInPowerExpTime r enc encB μ q)
    (hyes : ∀ a ∈ A.yes, r a ∈ B.yes) (hno : ∀ a ∈ A.no, r a ∈ B.no)
    {K : ℕ} (hsize : ∀ a, (μB (r a) + 1 : ℝ) ≤ (K + 1 : ℝ) * (μ a + 1 : ℝ) ^ b)
    (hp : 0 ≤ p) (hB : SolvesWithErrorInPowerExpTime B encB E μB p) :
    SolvesWithErrorInPowerExpTime A enc E μ (max q (b * p)) := by
  obtain ⟨C, d, hr⟩ := hr
  obtain ⟨D, e, hB⟩ := hB
  let d' := max d 1
  let P (a : α) : ℝ := (2 : ℝ) ^ (C * (μ a + 1 : ℝ) ^ q) * ((enc a).length + 1) ^ d'
  let R : ℝ := D * (K + 1 : ℝ) ^ p
  let X (a : α) : ℝ := (2 : ℝ) ^ (R * (μ a + 1 : ℝ) ^ (b * p))
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hP (a : α) : ((enc a).length + 1 : ℝ) ≤ P a := by
    have h := pow_le_two_rpow_mul_pow (L := (enc a).length) (d := 1)
      (x := C * (μ a + 1 : ℝ) ^ q) (by positivity) (le_max_right d 1)
    simpa only [pow_one] using h
  have hP0 (a : α) : 0 ≤ P a := by dsimp only [P]; positivity
  have hr' : ComputableInTimeO r enc encB P :=
    hr.mono 1 (fun a =>
      (two_rpow_mul_pow_le_two_rpow_mul_pow le_rfl (le_max_left d 1) :
        (2 : ℝ) ^ (C * (μ a + 1 : ℝ) ^ q) * ((enc a).length + 1) ^ d ≤ P a).trans
        (by rw [Nat.cast_one, one_mul]; exact le_add_of_nonneg_right zero_le_one)) hP0
  have hX (a : α) : 1 ≤ X a := by
    dsimp only [X]
    exact Real.one_le_rpow (by norm_num) (by positivity)
  have hY (a : α) : (2 : ℝ) ^ (D * (μB (r a) + 1 : ℝ) ^ p) ≤ 1 * X a := by
    rw [one_mul]
    exact two_rpow_mul_rpow_le_of_le_mul_rpow (by positivity) (by positivity)
      (by positivity) (hsize a) hp
  have h := hB.of_promiseReduction hr' hyes hno hP hX zero_le_one hY
  refine ⟨⌈R⌉₊ + C * (e + 1), d' * (e + 1), h.mono 1 (fun a => ?_) (fun _ => by positivity)⟩
  rw [Nat.cast_one, one_mul]
  exact (power_reduction_envelope_le (C := C) (d := d') (e := e)
    (x := (μ a + 1 : ℝ)) (y := ((enc a).length + 1 : ℝ)) (q := q) (r := b * p)
    (le_add_of_nonneg_left (Nat.cast_nonneg _)) (by positivity) hR).trans
    (le_add_of_nonneg_right zero_le_one)

/-- A polynomial-time promise reduction with parameter blowup `O((μA + 1) ^ b)` transports
power `p` to `b * p` with the same error profile. -/
theorem SolvesWithErrorInPowerExpTime.of_polyTime_promiseReduction
    {β : Type} {encB : β ↪ List Bool} {A : PromiseProblem α} {B : PromiseProblem β} {E : ErrorModel}
    {μB : β → ℕ} {r : α → β} {b : ℝ} (hr : ComputableInPolyTime r enc encB)
    (hyes : ∀ a ∈ A.yes, r a ∈ B.yes) (hno : ∀ a ∈ A.no, r a ∈ B.no)
    {K : ℕ} (hsize : ∀ a, (μB (r a) + 1 : ℝ) ≤ (K + 1 : ℝ) * (μ a + 1 : ℝ) ^ b)
    (hb : 0 ≤ b) (hp : 0 ≤ p) (hB : SolvesWithErrorInPowerExpTime B encB E μB p) :
    SolvesWithErrorInPowerExpTime A enc E μ (b * p) := by
  obtain ⟨e, he⟩ := ComputableInExpTime.of_computableInPolyTime (μ := fun _ => 0) hr
  rw [← max_eq_right (mul_nonneg hb hp)]
  exact hB.of_promiseReduction ⟨0, e, by simpa only [Nat.cast_zero, zero_mul] using he⟩
    hyes hno hsize hp

end Cslib.Complexity
