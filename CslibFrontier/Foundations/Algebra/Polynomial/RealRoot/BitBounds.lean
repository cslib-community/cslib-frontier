/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.Isolation
public import CslibFrontier.Foundations.Data.Nat.BinarySize

/-!
# Coefficient Bit-Size and Dyadic Endpoint Bounds for Real-Root Isolation

This module bounds the Cauchy root bound, cleared-denominator coefficient norm, Mignotte bisection
depth, and output rational interval endpoints in terms of input length `cs.length` and an input
coefficient bit-length bound `B`.

## Main definitions

* `Cslib.RealRoot.HasCoeffBitBound`: predicate asserting `Int.natAbs q.num ≤ 2 ^ B` and
  `q.den ≤ 2 ^ B` for every `q ∈ cs`.
* `Cslib.RealRoot.coeffBitBound`: computable bit-length bound satisfying
  `HasCoeffBitBound (coeffBitBound cs) cs`.
* `Cslib.RealRoot.DyadicBounded`: predicate asserting `q = (z : ℚ) / 2 ^ e` with
  `Int.natAbs z ≤ b * 2 ^ e`.

## Main results

* `Cslib.RealRoot.cauchyBoundNat_le_of_bitBound`,
  `Cslib.RealRoot.lcmDens_le_of_bitBound`,
  `Cslib.RealRoot.sqNormList_clearDenoms_le_of_bitBound`: explicit bounds on preprocessing
  quantities from `HasCoeffBitBound B cs`.
* `Cslib.RealRoot.mignotteBisectionDepth_le_of_bitBound`: unconditional polynomial bound
  `mignotteBisectionDepth cs ≤ (cs.length + 2) ^ 2 * (B + 2)`.
* `Cslib.RealRoot.DyadicBounded.den_le`, `Cslib.RealRoot.DyadicBounded.natAbs_num_le`,
  `Cslib.RealRoot.refineLeftRoot_dyadicBounded`, and `Cslib.RealRoot.isolateRoots_dyadicBounded`:
  dyadic numerator and denominator bounds on all endpoints produced by Sturm bisection.

## References

`HasCoeffBitBound`, `DyadicBounded`, and `mignotteBisectionDepth_le_of_bitBound` are this
library's own construction on top of the root-separation ingredients below.

* [BasuPollackRoy2006], Theorem 2.50, p. 52 (Sturm counting ingredient; §10.2 Algorithm 10.4 on
  pp. 373–374 is related work)
* [Mahler1964], pp. 257–262 (discriminant/Mahler-measure separation ingredient; equation locator
  unverified)
* [Mignotte1982], Theorem 3 (pp. 260–261) and Theorem 5 with integral corollary (p. 262; Landau
  norm comparison and root-separation ingredients)
-/

public section

namespace Cslib.RealRoot

open Polynomial

/-- Every rational entry `q ∈ cs` has numerator and denominator bounded by `2 ^ B`. -/
@[expose] def HasCoeffBitBound (B : ℕ) (cs : List ℚ) : Prop :=
  ∀ q ∈ cs, Int.natAbs q.num ≤ 2 ^ B ∧ q.den ≤ 2 ^ B

/-- Computable bit-length bound on all numerators and denominators in `cs`. -/
@[expose] def coeffBitBound (cs : List ℚ) : ℕ :=
  cs.foldl (fun acc q => max acc (max (Int.natAbs q.num).size q.den.size)) 0

private theorem foldl_coeffBitBound_ge (cs : List ℚ) (init : ℕ) :
    init ≤ cs.foldl (fun acc q => max acc (max (Int.natAbs q.num).size q.den.size)) init := by
  induction cs generalizing init with
  | nil => exact le_rfl
  | cons q qs ih => exact (le_max_left _ _).trans (ih _)

/-- Every coefficient list `cs` satisfies `HasCoeffBitBound (coeffBitBound cs) cs`. -/
theorem hasCoeffBitBound_coeffBitBound (cs : List ℚ) :
    HasCoeffBitBound (coeffBitBound cs) cs := by
  suffices ∀ (init : ℕ), ∀ q ∈ cs,
      let M := cs.foldl (fun acc r => max acc (max (Int.natAbs r.num).size r.den.size)) init
      Int.natAbs q.num ≤ 2 ^ M ∧ q.den ≤ 2 ^ M from this 0
  induction cs with
  | nil => simp
  | cons a as ih =>
    rintro init q hq
    rcases List.mem_cons.mp hq with rfl | hmem
    · have hle := (le_max_right init (max (Int.natAbs q.num).size q.den.size)).trans
        (foldl_coeffBitBound_ge as _)
      have hpow {n : ℕ} (h : n.size ≤ max (Int.natAbs q.num).size q.den.size) :
          n ≤ 2 ^ (q :: as).foldl (fun acc r => max acc (max r.num.natAbs.size r.den.size)) init :=
        (Nat.lt_size_self n).le.trans (Nat.pow_le_pow_right zero_lt_two (h.trans hle))
      exact ⟨hpow (le_max_left _ _), hpow (le_max_right _ _)⟩
    · exact ih _ q hmem

/-- `HasCoeffBitBound B` is preserved by `CoeffList.trim`. -/
theorem HasCoeffBitBound.trim {B : ℕ} {cs : List ℚ} (hB : HasCoeffBitBound B cs) :
    HasCoeffBitBound B (CoeffList.trim cs) :=
  fun q hq => hB q ((CoeffList.trim_sublist cs).subset hq)

private theorem maxAbsList_le_two_pow {B : ℕ} {cs : List ℚ} (hB : HasCoeffBitBound B cs) :
    maxAbsList cs ≤ (2 : ℚ) ^ B := by
  induction cs with
  | nil => simp only [maxAbsList]; positivity
  | cons q qs ih =>
    simp only [maxAbsList]
    refine max_le ?_ (ih fun r hr => hB r (List.mem_cons_of_mem q hr))
    calc |q|
        = |(q.num : ℚ) / (q.den : ℚ)| := by rw [Rat.num_div_den]
      _ = (Int.natAbs q.num : ℚ) / q.den := by
          rw [abs_div, ← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast, Nat.abs_cast]
      _ ≤ (Int.natAbs q.num : ℚ) :=
          div_le_self (Nat.cast_nonneg _) (Nat.one_le_cast.mpr q.den_pos)
      _ ≤ (2 : ℚ) ^ B := by simpa using (Nat.cast_le (α := ℚ)).mpr (hB q List.mem_cons_self).1

/-- Upper bound `cauchyBoundNat cs ≤ 2 ^ (2 * B) + 2` under `HasCoeffBitBound B cs`. -/
theorem cauchyBoundNat_le_of_bitBound {B : ℕ} {cs : List ℚ} (hB : HasCoeffBitBound B cs) :
    cauchyBoundNat cs ≤ 2 ^ (2 * B) + 2 := by
  let t := CoeffList.trim cs
  have htB : HasCoeffBitBound B t := hB.trim
  dsimp only [cauchyBoundNat]
  split_ifs with hlen
  · exact (by decide : 1 ≤ 2).trans (Nat.le_add_left 2 _)
  · have htnil : t ≠ [] := fun hnil => by simp [t, hnil] at hlen
    obtain ⟨l, lc, hlc0, hteq⟩ := (CoeffList.isTrimmed_trim cs).exists_append_singleton htnil
    have hlc_abs_ge : (1 : ℚ) / (2 : ℚ) ^ B ≤ |lc| := by
      have hnum : 1 ≤ Int.natAbs lc.num := Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr hlc0)
      have hden : (lc.den : ℚ) ≤ (2 : ℚ) ^ B :=
        calc (lc.den : ℚ)
            ≤ ((2 ^ B : ℕ) : ℚ) := Nat.cast_le.mpr (htB lc (by simp [t, hteq])).2
          _ = (2 : ℚ) ^ B := Nat.cast_pow 2 B
      calc (1 : ℚ) / (2 : ℚ) ^ B
          ≤ (Int.natAbs lc.num : ℚ) / (2 : ℚ) ^ B :=
            div_le_div_of_nonneg_right (Nat.one_le_cast.mpr hnum) (by positivity)
        _ ≤ (Int.natAbs lc.num : ℚ) / (lc.den : ℚ) :=
            div_le_div_of_nonneg_left (Nat.cast_nonneg _) (Nat.cast_pos.mpr lc.den_pos) hden
        _ = |(lc.num : ℚ) / (lc.den : ℚ)| := by
            rw [abs_div, ← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast, Nat.abs_cast]
        _ = |lc| := by rw [Rat.num_div_den]
    have hm_le : maxAbsList t.dropLast ≤ (2 : ℚ) ^ B :=
      maxAbsList_le_two_pow fun q hq => htB q (List.dropLast_subset t hq)
    have hlc_eq : Option.getD t.getLast? 1 = lc := by simp [t, hteq]
    rw [hlc_eq]
    let b := maxAbsList t.dropLast / |lc| + 1
    have hb_nonneg : 0 ≤ b :=
      add_nonneg (div_nonneg (maxAbsList_nonneg _) (abs_nonneg _)) zero_le_one
    have hdiv_le : maxAbsList t.dropLast / |lc| ≤ (2 : ℚ) ^ (2 * B) :=
      calc maxAbsList t.dropLast / |lc|
          ≤ maxAbsList t.dropLast / ((1 : ℚ) / (2 : ℚ) ^ B) :=
            div_le_div_of_nonneg_left (maxAbsList_nonneg _) (by positivity) hlc_abs_ge
        _ = maxAbsList t.dropLast * (2 : ℚ) ^ B := by rw [one_div, div_inv_eq_mul]
        _ ≤ (2 : ℚ) ^ B * (2 : ℚ) ^ B :=
              mul_le_mul_of_nonneg_right hm_le (by positivity)
        _ = (2 : ℚ) ^ (2 * B) := by rw [two_mul, pow_add]
    have hb_le : b ≤ ((2 ^ (2 * B) + 1 : ℕ) : ℚ) := by push_cast; linarith
    have hfloor_le : ((Int.natAbs b.num / b.den : ℕ) : ℚ) ≤ b := by
      have hnum_eq : (Int.natAbs b.num : ℚ) / b.den = b :=
        calc (Int.natAbs b.num : ℚ) / b.den
            = |(b.num : ℚ) / b.den| := by
              rw [abs_div, ← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast, Nat.abs_cast]
          _ = |b| := by rw [Rat.num_div_den]
          _ = b := abs_of_nonneg hb_nonneg
      calc ((Int.natAbs b.num / b.den : ℕ) : ℚ)
          ≤ (Int.natAbs b.num : ℚ) / b.den :=
            (le_div_iff₀ (Nat.cast_pos.mpr b.den_pos)).mpr
              (by exact_mod_cast Nat.div_mul_le_self (Int.natAbs b.num) b.den)
        _ = b := hnum_eq
    exact Nat.add_le_add_right (by exact_mod_cast hfloor_le.trans hb_le) 1

/-- Logarithmic bound `Nat.clog 4 (cauchyBoundNat cs) ≤ B + 1` under `HasCoeffBitBound B cs`. -/
theorem clog4_cauchyBoundNat_le_of_bitBound {B : ℕ} {cs : List ℚ} (hB : HasCoeffBitBound B cs) :
    Nat.clog 4 (cauchyBoundNat cs) ≤ B + 1 := by
  refine Nat.clog_le_of_le_pow ?_
  have hcb := cauchyBoundNat_le_of_bitBound hB
  have h4 : 2 ^ (2 * B) = 4 ^ B := pow_mul 2 2 B
  have h1 : 1 ≤ 4 ^ B := Nat.one_le_pow B 4 (by decide)
  rw [pow_succ]
  omega

/-- `lcmDens cs ≤ 2 ^ (cs.length * B)` under `HasCoeffBitBound B cs`. -/
theorem lcmDens_le_of_bitBound {B : ℕ} {cs : List ℚ} (hB : HasCoeffBitBound B cs) :
    lcmDens cs ≤ 2 ^ (cs.length * B) := by
  induction cs with
  | nil => simp [lcmDens]
  | cons q qs ih =>
    simp only [lcmDens, List.length_cons]
    calc Nat.lcm q.den (lcmDens qs)
        ≤ q.den * lcmDens qs := Nat.lcm_le_mul q.den_pos (one_le_lcmDens qs)
      _ ≤ 2 ^ B * 2 ^ (qs.length * B) :=
          Nat.mul_le_mul (hB q List.mem_cons_self).2
            (ih fun r hr => hB r (List.mem_cons_of_mem q hr))
      _ = 2 ^ ((qs.length + 1) * B) := by rw [Nat.add_one_mul, add_comm, pow_add]

private theorem foldl_sqNorm_le_of_bound (ns : List ℤ) (M acc : ℕ)
    (hM : ∀ z ∈ ns, Int.natAbs z ≤ M) :
    ns.foldl (fun s a => s + Int.natAbs a ^ 2) acc ≤ acc + ns.length * M ^ 2 := by
  induction ns generalizing acc with
  | nil => simp
  | cons a ns ih =>
    simp only [List.foldl_cons, List.length_cons]
    have ha : Int.natAbs a ^ 2 ≤ M ^ 2 :=
      Nat.pow_le_pow_left (hM a List.mem_cons_self) 2
    calc ns.foldl (fun s b => s + Int.natAbs b ^ 2) (acc + Int.natAbs a ^ 2)
        ≤ (acc + Int.natAbs a ^ 2) + ns.length * M ^ 2 :=
          ih (acc + Int.natAbs a ^ 2) fun z hz => hM z (List.mem_cons_of_mem a hz)
      _ ≤ acc + M ^ 2 + ns.length * M ^ 2 := by omega
      _ = acc + (ns.length + 1) * M ^ 2 := by ring

/-- Upper bound on cleared-denominator `sqNormList` under `HasCoeffBitBound B cs`. -/
theorem sqNormList_clearDenoms_le_of_bitBound {B : ℕ} {cs : List ℚ} (hB : HasCoeffBitBound B cs) :
    sqNormList (Prod.snd (clearDenomsList (CoeffList.trim cs))) ≤
      cs.length * 4 ^ ((cs.length + 1) * B) := by
  let t := CoeffList.trim cs
  have ht_len : t.length ≤ cs.length := CoeffList.length_trim_le cs
  have htB : HasCoeffBitBound B t := hB.trim
  have hD_le : lcmDens t ≤ 2 ^ (cs.length * B) :=
    (lcmDens_le_of_bitBound htB).trans
      (Nat.pow_le_pow_right zero_lt_two (Nat.mul_le_mul_right B ht_len))
  let ns := Prod.snd (clearDenomsList t)
  have hns_bound : ∀ z ∈ ns, Int.natAbs z ≤ 2 ^ ((cs.length + 1) * B) := by
    intro z hz
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hz
    rw [Int.natAbs_mul, Int.natAbs_natCast]
    calc Int.natAbs q.num * (lcmDens t / q.den)
        ≤ 2 ^ B * 2 ^ (cs.length * B) :=
          Nat.mul_le_mul (htB q hq).1 ((Nat.div_le_self _ _).trans hD_le)
      _ = 2 ^ ((cs.length + 1) * B) := by rw [Nat.add_one_mul, add_comm, pow_add]
  have h4 : (2 ^ ((cs.length + 1) * B)) ^ 2 = 4 ^ ((cs.length + 1) * B) := pow_right_comm 2 _ 2
  have hsq : sqNormList ns ≤ t.length * 4 ^ ((cs.length + 1) * B) := by
    simpa only [sqNormList, zero_add, h4, ns, clearDenomsList, List.length_map]
      using foldl_sqNorm_le_of_bound ns (2 ^ ((cs.length + 1) * B)) 0 hns_bound
  exact hsq.trans (Nat.mul_le_mul_right _ ht_len)

/-- Logarithmic bound on `sqNormList (clearDenomsList (CoeffList.trim cs)).2`
under `HasCoeffBitBound B cs`. -/
theorem clog4_sqNormList_le_of_bitBound {B : ℕ} {cs : List ℚ} (hB : HasCoeffBitBound B cs) :
    Nat.clog 4 (sqNormList (Prod.snd (clearDenomsList (CoeffList.trim cs)))) ≤
      cs.length + (cs.length + 1) * B := by
  refine Nat.clog_le_of_le_pow ?_
  have hsq := sqNormList_clearDenoms_le_of_bitBound hB
  have hn4 : cs.length ≤ 4 ^ cs.length :=
    Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left (by decide : 2 ≤ 4) cs.length)
  rw [pow_add]
  exact hsq.trans (Nat.mul_le_mul_right _ hn4)

/-- Unconditional polynomial upper bound on `mignotteBisectionDepth cs` in terms of `cs.length`
and an input coefficient bit-length bound `B`. -/
theorem mignotteBisectionDepth_le_of_bitBound {B : ℕ} {cs : List ℚ} (hB : HasCoeffBitBound B cs) :
    mignotteBisectionDepth cs ≤ (cs.length + 2) ^ 2 * (B + 2) := by
  by_cases hd : 2 ≤ (ofCoeffList cs).natDegree
  · have hbase := mignotteBisectionDepth_le cs hd
    have hcb := clog4_cauchyBoundNat_le_of_bitBound hB
    have hd_le_n : (ofCoeffList cs).natDegree ≤ cs.length :=
      (natDegree_ofCoeffList_le cs).trans (Nat.sub_le _ _)
    have h1 := Nat.mul_le_mul (Nat.add_le_add_right hd_le_n 2)
      (Nat.clog_le_of_le_pow (b := 4) (hd_le_n.trans
        (Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left (by decide) cs.length))))
    have h2 := Nat.mul_le_mul ((Nat.sub_le _ 1).trans hd_le_n) (clog4_sqNormList_le_of_bitBound hB)
    nlinarith
  · simp [mignotteBisectionDepth_eq_zero_of_natDegree_le_one (cs := cs) (by omega)]

/-- Predicate asserting that `q : ℚ` is a dyadic rational `z / 2 ^ e` with `|z| ≤ b * 2 ^ e`. -/
def DyadicBounded (b e : ℕ) (q : ℚ) : Prop :=
  ∃ z : ℤ, q = (z : ℚ) / (2 : ℚ) ^ e ∧ Int.natAbs z ≤ b * 2 ^ e

/-- Any natural number `(b : ℚ)` satisfies `DyadicBounded b 0`. -/
theorem DyadicBounded.of_nat (b : ℕ) : DyadicBounded b 0 (b : ℚ) :=
  ⟨b, by simp, by simp⟩

/-- `-(b : ℚ)` satisfies `DyadicBounded b 0`. -/
theorem DyadicBounded.of_neg_nat (b : ℕ) : DyadicBounded b 0 (-(b : ℚ)) :=
  ⟨-b, by simp, by simp⟩

/-- Monotonicity of `DyadicBounded` in the exponent `e ≤ e'`. -/
theorem DyadicBounded.mono {b e e' : ℕ} {q : ℚ} (hq : DyadicBounded b e q) (he : e ≤ e') :
    DyadicBounded b e' q := by
  obtain ⟨z, rfl, hz⟩ := hq
  refine ⟨z * (2 : ℤ) ^ (e' - e), ?_, ?_⟩
  · rw [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, div_eq_div_iff (by positivity) (by positivity)]
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel he]
  · rw [Int.natAbs_mul, Int.natAbs_pow]
    calc Int.natAbs z * 2 ^ (e' - e)
        ≤ (b * 2 ^ e) * 2 ^ (e' - e) := Nat.mul_le_mul_right _ hz
      _ = b * 2 ^ e' := by rw [mul_assoc, ← pow_add, Nat.add_sub_of_le he]

/-- Midpoint rule: if `u` and `v` satisfy `DyadicBounded b e`, then `(u + v) / 2` satisfies
`DyadicBounded b (e + 1)`. -/
theorem DyadicBounded.mid {b e : ℕ} {u v : ℚ}
    (hu : DyadicBounded b e u) (hv : DyadicBounded b e v) :
    DyadicBounded b (e + 1) ((u + v) / 2) := by
  obtain ⟨zu, rfl, hzu⟩ := hu
  obtain ⟨zv, rfl, hzv⟩ := hv
  refine ⟨zu + zv, by simp only [← add_div, div_div, pow_succ, Int.cast_add], ?_⟩
  calc Int.natAbs (zu + zv)
      ≤ Int.natAbs zu + Int.natAbs zv := Int.natAbs_add_le _ _
    _ ≤ b * 2 ^ e + b * 2 ^ e := Nat.add_le_add hzu hzv
    _ = b * 2 ^ (e + 1) := by ring

/-- Denominator bound `q.den ≤ 2 ^ e` for any `DyadicBounded b e q`. -/
theorem DyadicBounded.den_le {b e : ℕ} {q : ℚ} (hq : DyadicBounded b e q) :
    q.den ≤ 2 ^ e := by
  obtain ⟨z, rfl, _⟩ := hq
  refine Nat.le_of_dvd (Nat.pow_pos zero_lt_two) (Int.ofNat_dvd.mp ?_)
  simpa [Rat.divInt_eq_div] using Rat.den_dvd z ((2 : ℤ) ^ e)

/-- Numerator magnitude bound `Int.natAbs q.num ≤ b * 2 ^ e` for any `DyadicBounded b e q`. -/
theorem DyadicBounded.natAbs_num_le {b e : ℕ} {q : ℚ} (hq : DyadicBounded b e q) :
    Int.natAbs q.num ≤ b * 2 ^ e := by
  have ⟨z, hq_eq, hz⟩ := hq
  have hcrossZ : q.num * (2 : ℤ) ^ e = z * (q.den : ℤ) := by
    exact_mod_cast (div_eq_div_iff (Nat.cast_ne_zero.mpr q.den_nz) (by positivity)).mp
      ((Rat.num_div_den q).trans hq_eq)
  have hcrossN : Int.natAbs q.num * 2 ^ e = Int.natAbs z * q.den := by
    simpa [Int.natAbs_mul, Int.natAbs_pow] using congrArg Int.natAbs hcrossZ
  exact Nat.le_of_mul_le_mul_right (hcrossN ▸ Nat.mul_le_mul hz hq.den_le) (Nat.pow_pos zero_lt_two)

/-- Dyadic bound for `refineLeftLoop`: starting from `DyadicBounded b e` endpoints, `fuel` steps
produce endpoints satisfying `DyadicBounded b (e + fuel)`. -/
theorem refineLeftLoop_dyadicBounded (t : List ℚ) (seq : List (List ℚ)) :
    ∀ (fuel b e : ℕ) (u v : ℚ) (vu : ℕ),
      DyadicBounded b e u → DyadicBounded b e v →
      let I := refineLeftLoop t seq fuel u v vu
      DyadicBounded b (e + fuel) I.lower ∧ DyadicBounded b (e + fuel) I.upper
  | 0, _, _, _, _, _, hu, hv => ⟨hu, hv⟩
  | fuel + 1, b, e, u, v, vu, hu, hv => by
    dsimp only [refineLeftLoop]
    have hm : DyadicBounded b (e + 1) ((u + v) / 2) := hu.mid hv
    split_ifs with hvm hem
    · exact ⟨hm.mono (by omega), hv.mono (by omega)⟩
    · exact ⟨hm.mono (by omega), hm.mono (by omega)⟩
    · simpa only [Nat.add_right_comm e 1 fuel, Nat.add_assoc] using
        refineLeftLoop_dyadicBounded t seq fuel b (e + 1) u ((u + v) / 2) vu
          (hu.mono (by omega)) hm

/-- Dyadic bound for `refineLeftRoot`: starting from `DyadicBounded b e` endpoints, `fuel` steps
produce endpoints satisfying `DyadicBounded b (e + fuel)`. -/
theorem refineLeftRoot_dyadicBounded (t : List ℚ) (seq : List (List ℚ))
    (fuel b e : ℕ) (u v : ℚ) (vu : ℕ)
    (hu : DyadicBounded b e u) (hv : DyadicBounded b e v) :
    let I := refineLeftRoot t seq fuel u v vu
    DyadicBounded b (e + fuel) I.lower ∧ DyadicBounded b (e + fuel) I.upper := by
  dsimp only [refineLeftRoot]
  split_ifs with hev heu
  · exact ⟨hv.mono (by omega), hv.mono (by omega)⟩
  · exact ⟨hu.mono (by omega), hv.mono (by omega)⟩
  · exact refineLeftLoop_dyadicBounded t seq fuel b e u v vu hu hv

/-- Dyadic bound for `isolateIoc`: starting from `DyadicBounded b e` endpoints, every returned
interval has endpoints satisfying `DyadicBounded b (e + fuel + depthBound)`. -/
theorem isolateIoc_dyadicBounded (t : List ℚ) (seq : List (List ℚ)) (depthBound : ℕ) :
    ∀ (fuel b e : ℕ) (u v : ℚ) (vu vv : ℕ),
      DyadicBounded b e u → DyadicBounded b e v →
      ∀ I ∈ isolateIoc t seq depthBound fuel u v vu vv,
        DyadicBounded b (e + fuel + depthBound) I.lower ∧
          DyadicBounded b (e + fuel + depthBound) I.upper
  | fuel, b, e, u, v, vu, vv, hu, hv => by
    unfold isolateIoc
    dsimp only
    split_ifs with hc0 hc1
    · simp
    · obtain ⟨hl, hr⟩ := refineLeftRoot_dyadicBounded t seq depthBound b e u v vu hu hv
      simpa only [List.mem_singleton, forall_eq] using ⟨hl.mono (by omega), hr.mono (by omega)⟩
    · cases fuel with
      | zero => simp
      | succ fuel' =>
        have hm := hu.mid hv
        rw [← Nat.add_assoc e fuel' 1, Nat.add_right_comm e fuel' 1]
        rintro I hI
        rcases List.mem_append.mp hI with hL | hR
        · exact isolateIoc_dyadicBounded t seq depthBound fuel' b (e + 1) u ((u + v) / 2) vu _
            (hu.mono (by omega)) hm I hL
        · exact isolateIoc_dyadicBounded t seq depthBound fuel' b (e + 1) ((u + v) / 2) v _ vv
            hm (hv.mono (by omega)) I hR

/-- Unconditional dyadic endpoint bound: every interval in `isolateRoots cs` has endpoints of the
form `z / 2 ^ (2 * mignotteBisectionDepth cs)` with
`Int.natAbs z ≤ cauchyBoundNat cs * 2 ^ (2 * mignotteBisectionDepth cs)`. -/
theorem isolateRoots_dyadicBounded (cs : List ℚ) :
    ∀ I ∈ isolateRoots cs,
      DyadicBounded (cauchyBoundNat cs) (2 * mignotteBisectionDepth cs) I.lower ∧
        DyadicBounded (cauchyBoundNat cs) (2 * mignotteBisectionDepth cs) I.upper := by
  simp only [isolateRoots]
  split_ifs with he
  · simp
  · simpa only [zero_add, two_mul] using isolateIoc_dyadicBounded (CoeffList.trim cs)
      (sturmSeqList cs) (mignotteBisectionDepth cs) (mignotteBisectionDepth cs)
      (cauchyBoundNat cs) 0 _ _ _ _ (.of_neg_nat _) (.of_nat _)

end Cslib.RealRoot
