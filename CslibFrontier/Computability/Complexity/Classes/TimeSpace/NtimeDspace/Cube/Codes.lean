/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Nat.Log
import Mathlib.Data.List.GetD

/-!
# Codes for labels (Lemma 4.1)

A multiset of requests is coded by the Elias gamma codes of `m + 1` (`m` the number of distinct
weights) and, for each distinct weight in increasing order, of the gap to the previous weight and
of the multiplicity. A label of weight at most `a ≥ 1` is coded by the codes of its two multisets,
padded with zeros to length `len(a) = ⌊28 √a⌋ + 2`; the empty label is the only label of weight `0`,
coded by the empty string (`w(0) = 0`).

Codes are bit lists, and a code is read as the natural number whose bit `k` is the `k`-th entry
(`ofBits`). The formula of §6.2 sums over all indices of `len(a)` bits; `sum_codes` says that
summing a function of the decoded label over the indices that decode to a label of exact weight `a`
is
summing it over `Λ(a)`.

## Main results

* `codeWidth`: `len(a)`; `codeWidth_sq_le`: `len(a) ≤ 30 √a` (as `len(a)^2 ≤ 900 a`).
* `msCode_length_le`: the two codes of a label of weight at most `a ≥ 1` fit in `len(a)` bits. The
  code of a multiset of weight `W` has at most `(8 + 8√2) √W + 1 ≤ 19.4 √W + 1` bits, by counting
  the gaps and the multiplicities at least `2^j` for every `j ≥ 1`.
* `labelCode`, `decodeLabel`: coding and decoding. `parseMs` parses the gamma codes and accepts
  only if re-encoding the parsed multiset gives back the parsed prefix (`parseMs_msCode`,
  `msCode_append_of_parseMs`).
* `decode_labelCode`, `labelCode_decode`: decoding inverts coding on `Λ_≤(a)`.
* `sum_codes`: the sum over indices of `len(a)` bits equals the sum over `Λ(a)`.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cube

open Finset

/-! ### Gamma codes -/

/-- The Elias gamma code of `x ≥ 1`: `⌊log₂ x⌋` zeros, then the binary digits of `x` from the
most significant (a one) down. -/
def gamma (x : ℕ) : List Bool :=
  List.replicate (Nat.log 2 x) false ++ (List.range (Nat.log 2 x + 1)).reverse.map x.testBit

/-- Parse one gamma code from the front of a bit list: the value and the rest, or `none`. -/
def parseGamma (l : List Bool) : Option (ℕ × List Bool) :=
  let z := (l.takeWhile (· = false)).length
  let rest := l.drop z
  if rest.length < z + 1 then none
  else some ((rest.take (z + 1)).foldl (fun acc b => 2 * acc + b.toNat) 0, rest.drop (z + 1))

/-- Reading the low `n` bits of `x` from the most significant one: `acc · 2^n + x mod 2^n`. -/
private theorem foldl_bits (x : ℕ) : ∀ n acc : ℕ,
    ((List.range n).reverse.map x.testBit).foldl (fun acc b => 2 * acc + b.toNat) acc =
      acc * 2 ^ n + x % 2 ^ n
  | 0, acc => by simp [Nat.mod_one]
  | n + 1, acc => by
    simp only [List.range_succ, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.singleton_append, List.map_cons, List.foldl_cons]
    rw [foldl_bits x n, Nat.toNat_testBit, Nat.mod_pow_succ]
    ring

theorem parseGamma_gamma (x : ℕ) (hx : 1 ≤ x) (l : List Bool) :
    parseGamma (gamma x ++ l) = some (x, l) := by
  obtain ⟨z, hz⟩ : ∃ z, Nat.log 2 x = z := ⟨_, rfl⟩
  have hlo : 2 ^ z ≤ x := hz ▸ Nat.pow_log_le_self 2 (by omega)
  have hhi : x < 2 ^ (z + 1) := hz ▸ Nat.lt_pow_succ_log_self (by norm_num) x
  have htop : x.testBit z = true := by
    have e : x = 2 ^ z + (x - 2 ^ z) := by omega
    rw [e, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow (by rw [pow_succ] at hhi; omega)]
    rfl
  obtain ⟨D, hD⟩ : ∃ D, (List.range (z + 1)).reverse.map x.testBit = D := ⟨_, rfl⟩
  have hD' : D = true :: (List.range z).reverse.map x.testBit := by
    rw [← hD, List.range_succ]; simp [htop]
  have hDlen : D.length = z + 1 := by rw [← hD]; simp
  have hval : D.foldl (fun acc b => 2 * acc + b.toNat) 0 = x := by
    rw [← hD, foldl_bits]; simp [Nat.mod_eq_of_lt hhi]
  have hg : gamma x ++ l = List.replicate z false ++ (D ++ l) := by
    simp only [gamma, hz, hD, List.append_assoc]
  have htw : ((gamma x ++ l).takeWhile (· = false)).length = z := by
    rw [hg, hD']; simp
  have hdrop : (gamma x ++ l).drop z = D ++ l := by
    rw [hg]; exact List.drop_left' (by simp)
  simp only [parseGamma, htw, hdrop, List.length_append, hDlen,
    List.take_left' hDlen, List.drop_left' hDlen, hval]
  split_ifs with h
  · omega
  · rfl

theorem length_gamma (x : ℕ) : (gamma x).length = 2 * Nat.log 2 x + 1 := by
  simp [gamma]; omega

/-! ### Codes of multisets and labels -/

/-- The distinct weights of a multiset of requests, in increasing order. -/
def distinctWts (σ : Multiset ℕ) : List ℕ := (σ.map (· + 1)).toFinset.sort (· ≤ ·)

/-- The code of a multiset of requests. -/
def msCode (σ : Multiset ℕ) : List Bool :=
  let ps := distinctWts σ
  gamma (ps.length + 1) ++
    ((List.range ps.length).flatMap fun ν =>
      gamma (ps.getD ν 0 - (if ν = 0 then 0 else ps.getD (ν - 1) 0)) ++
        gamma (σ.count (ps.getD ν 0 - 1)))

/-- **The code width** `len(a)`: `0` for `a = 0`, else `⌊28 √a⌋ + 2`. -/
def codeWidth (a : ℕ) : ℕ := if a = 0 then 0 else Nat.sqrt (784 * a) + 2

/-- `len(a) ≤ 30 √a`, as `len(a)^2 ≤ 900 a`. -/
theorem codeWidth_sq_le (a : ℕ) : codeWidth a ^ 2 ≤ 900 * a := by
  unfold codeWidth
  split_ifs with ha
  · simp [ha]
  · have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha
    have h1 := Nat.sqrt_le' (784 * a)
    have h2 : Nat.sqrt (784 * a) ≤ 28 * a := by
      calc Nat.sqrt (784 * a) ≤ Nat.sqrt ((28 * a) ^ 2) := Nat.sqrt_le_sqrt (by nlinarith)
        _ = 28 * a := Nat.sqrt_eq' _
    nlinarith

/-! ### The structure of a multiset code -/

section Structure

variable (σ : Multiset ℕ)

private theorem sum_range_getD (l : List ℕ) {M : Type*} [AddCommMonoid M] (F : ℕ → M) :
    ∑ ν ∈ range l.length, F (l.getD ν 0) = (l.map F).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons, add_comm]
    simp only [List.getD_cons_succ, List.getD_cons_zero, ih]

private theorem distinctWts_sum {M : Type*} [AddCommMonoid M] (F : ℕ → M) :
    ((distinctWts σ).map F).sum = ∑ x ∈ (σ.map (· + 1)).toFinset, F x := by
  unfold distinctWts
  rw [← List.sum_toFinset F (Finset.sort_nodup _ _), Finset.sort_toFinset]

private theorem mem_distinctWts {x : ℕ} : x ∈ distinctWts σ ↔ ∃ i ∈ σ, i + 1 = x := by
  simp [distinctWts]

private theorem distinctWts_lt {ν ν' : ℕ} (h : ν < ν') (h' : ν' < (distinctWts σ).length) :
    (distinctWts σ).getD ν 0 < (distinctWts σ).getD ν' 0 := by
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ h']
  exact (Finset.sortedLT_sort _).getElem_lt_getElem_of_lt h

private theorem distinctWts_mem {ν : ℕ} (h : ν < (distinctWts σ).length) :
    ∃ i ∈ σ, i + 1 = (distinctWts σ).getD ν 0 := by
  rw [List.getD_eq_getElem _ _ h]
  exact (mem_distinctWts σ).mp (List.getElem_mem h)

private theorem one_le_distinctWts {ν : ℕ} (h : ν < (distinctWts σ).length) :
    1 ≤ (distinctWts σ).getD ν 0 := by
  obtain ⟨i, -, hi⟩ := distinctWts_mem σ h; omega

private theorem one_le_count {ν : ℕ} (h : ν < (distinctWts σ).length) :
    1 ≤ σ.count ((distinctWts σ).getD ν 0 - 1) := by
  obtain ⟨i, hi, e⟩ := distinctWts_mem σ h
  rw [← e, Nat.add_sub_cancel]
  exact Multiset.count_pos.mpr hi

/-- A multiset is the sum, over its distinct weights, of its requests of that weight. -/
private theorem eq_sum_distinctWts :
    σ = ∑ ν ∈ range (distinctWts σ).length,
      Multiset.replicate (σ.count ((distinctWts σ).getD ν 0 - 1))
          ((distinctWts σ).getD ν 0 - 1) := by
  rw [sum_range_getD (distinctWts σ) (fun x => Multiset.replicate (σ.count (x - 1)) (x - 1)),
    distinctWts_sum, Multiset.toFinset_map,
    Finset.sum_image (fun a _ b _ (h : a + 1 = b + 1) => by omega)]
  simp only [Nat.add_sub_cancel, ← Multiset.nsmul_singleton]
  exact (Multiset.toFinset_sum_count_nsmul_eq σ).symm

private theorem wt_eq_sum_distinctWts :
    wt σ = ∑ ν ∈ range (distinctWts σ).length,
      σ.count ((distinctWts σ).getD ν 0 - 1) * (distinctWts σ).getD ν 0 := by
  conv_lhs => rw [eq_sum_distinctWts σ]
  have : ∀ n : ℕ, n ≤ (distinctWts σ).length →
      wt (∑ ν ∈ range n, Multiset.replicate (σ.count ((distinctWts σ).getD ν 0 - 1))
        ((distinctWts σ).getD ν 0 - 1)) =
      ∑ ν ∈ range n, σ.count ((distinctWts σ).getD ν 0 - 1) * (distinctWts σ).getD ν 0 := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, wt_add, ih (by omega)]
      have h1 := one_le_distinctWts σ (ν := n) (by omega)
      simp only [wt, Multiset.map_replicate, Multiset.sum_replicate, smul_eq_mul]
      rw [Nat.sub_add_cancel h1]
  exact this _ le_rfl

/-- The gap of the `ν`-th distinct weight. -/
private def gapAt (ps : List ℕ) (ν : ℕ) : ℕ :=
  ps.getD ν 0 - (if ν = 0 then 0 else ps.getD (ν - 1) 0)

private theorem sum_gapAt {ν : ℕ} (h : ν < (distinctWts σ).length) :
    ∑ μ ∈ range (ν + 1), gapAt (distinctWts σ) μ = (distinctWts σ).getD ν 0 := by
  induction ν with
  | zero => simp [gapAt]
  | succ ν ih =>
    rw [Finset.sum_range_succ, ih (by omega)]
    have := distinctWts_lt σ (by omega : ν < ν + 1) h
    simp only [gapAt, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    omega

private theorem one_le_gapAt {ν : ℕ} (h : ν < (distinctWts σ).length) :
    1 ≤ gapAt (distinctWts σ) ν := by
  unfold gapAt
  rcases ν with _ | ν
  · simpa using one_le_distinctWts σ h
  · have := distinctWts_lt σ (by omega : ν < ν + 1) h
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    omega

private theorem msCode_eq : msCode σ = gamma ((distinctWts σ).length + 1) ++
    (List.range (distinctWts σ).length).flatMap fun ν =>
      gamma (gapAt (distinctWts σ) ν) ++ gamma (σ.count ((distinctWts σ).getD ν 0 - 1)) := rfl

end Structure

/-! ### The length of a code -/

private theorem length_msCode (σ : Multiset ℕ) :
    (msCode σ).length = 1 + (2 * Nat.log 2 ((distinctWts σ).length + 1) +
      ∑ ν ∈ range (distinctWts σ).length, (2 * Nat.log 2 (gapAt (distinctWts σ) ν) +
        2 * Nat.log 2 (σ.count ((distinctWts σ).getD ν 0 - 1)) + 2)) := by
  rw [msCode_eq, List.length_append, List.length_flatMap, length_gamma]
  have : ∀ ν, (gamma (gapAt (distinctWts σ) ν) ++
      gamma (σ.count ((distinctWts σ).getD ν 0 - 1))).length =
      2 * Nat.log 2 (gapAt (distinctWts σ) ν) +
        2 * Nat.log 2 (σ.count ((distinctWts σ).getD ν 0 - 1)) + 2 := fun ν => by
    rw [List.length_append, length_gamma, length_gamma]; ring
  simp only [this]
  have e : ∀ (n : ℕ) (f : ℕ → ℕ), ((List.range n).map f).sum = ∑ ν ∈ range n, f ν :=
    fun _ _ => rfl
  rw [e]
  omega

/-! ### The length bound -/

/-- `r` distinct positive integers add up to at least `r (r + 1) / 2`. -/
private theorem card_mul_succ_le_sum {ι : Type*} (S : Finset ι) (f : ι → ℕ)
    (hf : Set.InjOn f S) (hpos : ∀ x ∈ S, 1 ≤ f x) :
    S.card * (S.card + 1) ≤ 2 * ∑ x ∈ S, f x := by
  classical
  have e : ∑ x ∈ S, f x = ∑ y ∈ S.image f, y := by rw [Finset.sum_image hf]
  rw [e, ← Finset.card_image_of_injOn hf]
  have hpos' : ∀ y ∈ S.image f, 1 ≤ y := by
    intro y hy; obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy; exact hpos x hx
  revert hpos'
  refine Finset.induction_on_max (S.image f) (by simp) fun a T hlt ih hpos' => ?_
  have haT : a ∉ T := fun h => lt_irrefl a (hlt a h)
  rw [Finset.card_insert_of_notMem haT, Finset.sum_insert haT]
  have ih' := ih fun y hy => hpos' y (Finset.mem_insert_of_mem hy)
  have hcard : T.card ≤ a - 1 := by
    have : T ⊆ Finset.Ico 1 a := fun y hy =>
      Finset.mem_Ico.mpr ⟨hpos' y (Finset.mem_insert_of_mem hy), hlt y hy⟩
    simpa using Finset.card_le_card this
  have ha1 := hpos' a (Finset.mem_insert_self a T)
  have hca : T.card + 1 ≤ a := by omega
  nlinarith

/-- `⌊log₂ x⌋` counts the `j ≥ 1` with `2^j ≤ x`. -/
private theorem log_eq_sum (x J : ℕ) (hx : x ≤ J) :
    Nat.log 2 x = ∑ j ∈ Ico 1 (J + 1), if 2 ^ j ≤ x then 1 else 0 := by
  rw [← Finset.card_filter]
  rcases Nat.eq_zero_or_pos x with rfl | hx0
  · simp
  · have : (Ico 1 (J + 1)).filter (fun j => 2 ^ j ≤ x) = Ico 1 (Nat.log 2 x + 1) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_Ico]
      rw [← Nat.le_log_iff_pow_le (by norm_num) (by omega)]
      have := Nat.log_le_self 2 x
      omega
    rw [this, Nat.card_Ico]
    omega

private theorem geom_sum_Ico_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (J : ℕ) :
    ∑ j ∈ Ico 1 (J + 1), x ^ j ≤ x / (1 - x) := by
  have e : ∀ J : ℕ, (1 - x) * ∑ j ∈ Ico 1 (J + 1), x ^ j = x - x ^ (J + 1) := by
    intro J
    induction J with
    | zero => simp
    | succ J ih => rw [Finset.sum_Ico_succ_top (by omega), mul_add, ih]; ring
  rw [le_div_iff₀ (by linarith), mul_comm, e]
  have := pow_nonneg hx0 (J + 1)
  linarith

/-- A sum of counts `r_j` with `r_j (r_j + 1) 2^j ≤ 2W` is at most `(1 + √2) √(2W)`. -/
private theorem sum_le_of_sq (W J : ℕ) (r : ℕ → ℕ) (hr : ∀ j, r j * (r j + 1) * 2 ^ j ≤ 2 * W) :
    (∑ j ∈ Ico 1 (J + 1), (r j : ℝ)) ≤ (1 + √2) * √(2 * W) := by
  have hs2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2pos : 0 < √2 := by positivity
  have hs1 : 1 < √2 := by nlinarith
  obtain ⟨x, hx⟩ : ∃ x : ℝ, (√2)⁻¹ = x := ⟨_, rfl⟩
  have hx0 : 0 ≤ x := by rw [← hx]; positivity
  have hxs : √2 * x = 1 := by rw [← hx]; exact mul_inv_cancel₀ hs2pos.ne'
  have hx1 : x < 1 := by nlinarith
  have hterm : ∀ j, (r j : ℝ) ≤ √(2 * W) * x ^ j := by
    intro j
    have h0 : ((r j * r j * 2 ^ j : ℕ) : ℝ) ≤ 2 * W := by
      have : r j * r j * 2 ^ j ≤ 2 * W :=
        le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.le_succ _))) (hr j)
      exact_mod_cast this
    have h1 : ((r j : ℝ) * √2 ^ j) ^ 2 ≤ 2 * W := by
      rw [mul_pow, ← pow_mul, mul_comm j 2, pow_mul, Real.sq_sqrt (by norm_num)]
      push_cast at h0
      nlinarith
    have h2 := (le_abs_self _).trans (Real.abs_le_sqrt h1)
    calc (r j : ℝ) = (r j * √2 ^ j) * x ^ j := by rw [mul_assoc, ← mul_pow, hxs, one_pow, mul_one]
      _ ≤ √(2 * W) * x ^ j := mul_le_mul_of_nonneg_right h2 (pow_nonneg hx0 _)
  have hgeom : x / (1 - x) = 1 + √2 := by
    rw [div_eq_iff (by linarith)]
    nlinarith
  calc (∑ j ∈ Ico 1 (J + 1), (r j : ℝ)) ≤ ∑ j ∈ Ico 1 (J + 1), √(2 * W) * x ^ j :=
        Finset.sum_le_sum fun j _ => hterm j
    _ = √(2 * W) * ∑ j ∈ Ico 1 (J + 1), x ^ j := by rw [Finset.mul_sum]
    _ ≤ √(2 * W) * (x / (1 - x)) :=
        mul_le_mul_of_nonneg_left (geom_sum_Ico_le hx0 hx1 J) (Real.sqrt_nonneg _)
    _ = (1 + √2) * √(2 * W) := by rw [hgeom, mul_comm]

/-- The counting argument of Lemma 4.1, for strictly increasing positive weights `p ν` with gaps
`G ν` and positive multiplicities `μ ν`. -/
private theorem len_bound (m : ℕ) (p G μ : ℕ → ℕ)
    (hmono : ∀ ν ν', ν < ν' → ν' < m → p ν < p ν') (hpos : ∀ ν < m, 1 ≤ p ν)
    (htel : ∀ ν < m, ∑ κ ∈ range (ν + 1), G κ = p ν) (hμ : ∀ ν < m, 1 ≤ μ ν) :
    ((2 * Nat.log 2 (m + 1) + ∑ ν ∈ range m, (2 * Nat.log 2 (G ν) + 2 * Nat.log 2 (μ ν) + 2) :
        ℕ) : ℝ) ≤ (8 + 8 * √2) * √(∑ ν ∈ range m, μ ν * p ν : ℕ) := by
  obtain ⟨W, hW⟩ : ∃ W, ∑ ν ∈ range m, μ ν * p ν = W := ⟨_, rfl⟩
  rw [hW]
  have hSp : ∑ ν ∈ range m, p ν ≤ W := hW ▸ Finset.sum_le_sum fun ν hν =>
    Nat.le_mul_of_pos_left _ (hμ ν (Finset.mem_range.mp hν))
  have hinj : Set.InjOn p (range m : Finset ℕ) := fun ν hν ν' hν' h => by
    have hν := Finset.mem_range.mp hν; have hν' := Finset.mem_range.mp hν'
    rcases lt_trichotomy ν ν' with h1 | h1 | h1
    · exact absurd h (hmono ν ν' h1 hν').ne
    · exact h1
    · exact absurd h (hmono ν' ν h1 hν).ne'
  have hm : m * (m + 1) ≤ 2 * W := by
    have := card_mul_succ_le_sum (range m) p hinj fun ν hν => hpos ν (Finset.mem_range.mp hν)
    rw [Finset.card_range] at this
    omega
  have hpW : ∀ ν < m, p ν ≤ W := fun ν hν =>
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hν)).trans hSp
  have hGW : ∀ ν < m, G ν ≤ W := fun ν hν => by
    have := htel ν hν
    have : G ν ≤ ∑ κ ∈ range (ν + 1), G κ :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
    have := hpW ν hν
    omega
  have hμW : ∀ ν < m, μ ν ≤ W := fun ν hν => by
    have := Finset.single_le_sum (f := fun ν => μ ν * p ν) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr hν)
    rw [hW] at this
    exact (Nat.le_mul_of_pos_right _ (hpos ν hν)).trans this
  -- the counts of large gaps
  have hrG : ∀ j, ((range m).filter fun ν => 2 ^ j ≤ G ν).card *
      (((range m).filter fun ν => 2 ^ j ≤ G ν).card + 1) * 2 ^ j ≤ 2 * W := by
    intro j
    obtain ⟨S, hS⟩ : ∃ S, (range m).filter (fun ν => 2 ^ j ≤ G ν) = S := ⟨_, rfl⟩
    rw [hS]
    have hmemS : ∀ ν ∈ S, ν < m ∧ 2 ^ j ≤ G ν := fun ν hν => by
      rw [← hS, Finset.mem_filter, Finset.mem_range] at hν; exact hν
    let c : ℕ → ℕ := fun ν => ((range (ν + 1)).filter fun κ => 2 ^ j ≤ G κ).card
    have hc : ∀ ν ∈ S, 2 ^ j * c ν ≤ p ν := by
      intro ν hν
      rw [← htel ν (hmemS ν hν).1]
      calc 2 ^ j * c ν = ∑ κ ∈ (range (ν + 1)).filter (fun κ => 2 ^ j ≤ G κ), 2 ^ j := by
            rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ κ ∈ (range (ν + 1)).filter (fun κ => 2 ^ j ≤ G κ), G κ :=
            Finset.sum_le_sum fun κ hκ => (Finset.mem_filter.mp hκ).2
        _ ≤ ∑ κ ∈ range (ν + 1), G κ := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    have hmonoc : ∀ ν ∈ S, ∀ ν' ∈ S, ν < ν' → c ν < c ν' := by
      intro ν _ ν' hν' h
      apply Finset.card_lt_card
      refine (Finset.ssubset_iff_of_subset ?_).mpr ⟨ν', ?_, ?_⟩
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
        exact ⟨by omega, hx.2⟩
      · simp only [Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, (hmemS ν' hν').2⟩
      · simp only [Finset.mem_filter, Finset.mem_range]; omega
    have hcinj : Set.InjOn c S := fun ν hν ν' hν' h => by
      rcases lt_trichotomy ν ν' with h1 | h1 | h1
      · exact absurd h (hmonoc ν hν ν' hν' h1).ne
      · exact h1
      · exact absurd h (hmonoc ν' hν' ν hν h1).ne'
    have hcpos : ∀ ν ∈ S, 1 ≤ c ν := fun ν hν => Finset.card_pos.mpr
      ⟨ν, by simp only [Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, (hmemS ν hν).2⟩⟩
    have h1 := card_mul_succ_le_sum S c hcinj hcpos
    have h2 : 2 ^ j * ∑ ν ∈ S, c ν ≤ W := by
      rw [Finset.mul_sum]
      refine ((Finset.sum_le_sum hc).trans (Finset.sum_le_sum_of_subset ?_)).trans hSp
      rw [← hS]; exact Finset.filter_subset _ _
    calc S.card * (S.card + 1) * 2 ^ j ≤ (2 * ∑ ν ∈ S, c ν) * 2 ^ j := Nat.mul_le_mul_right _ h1
      _ = 2 * (2 ^ j * ∑ ν ∈ S, c ν) := by ring
      _ ≤ 2 * W := by omega
  -- the counts of large multiplicities
  have hrμ : ∀ j, ((range m).filter fun ν => 2 ^ j ≤ μ ν).card *
      (((range m).filter fun ν => 2 ^ j ≤ μ ν).card + 1) * 2 ^ j ≤ 2 * W := by
    intro j
    obtain ⟨S, hS⟩ : ∃ S, (range m).filter (fun ν => 2 ^ j ≤ μ ν) = S := ⟨_, rfl⟩
    rw [hS]
    have hSsub : S ⊆ range m := hS ▸ Finset.filter_subset _ _
    have h1 := card_mul_succ_le_sum S p (hinj.mono (by exact_mod_cast hSsub)) fun ν hν =>
      hpos ν (Finset.mem_range.mp (hSsub hν))
    have h2 : 2 ^ j * ∑ ν ∈ S, p ν ≤ W := by
      rw [Finset.mul_sum, ← hW]
      refine (Finset.sum_le_sum fun ν hν => ?_).trans (Finset.sum_le_sum_of_subset hSsub)
      rw [← hS, Finset.mem_filter] at hν
      exact Nat.mul_le_mul_right _ hν.2
    calc S.card * (S.card + 1) * 2 ^ j ≤ (2 * ∑ ν ∈ S, p ν) * 2 ^ j := Nat.mul_le_mul_right _ h1
      _ = 2 * (2 ^ j * ∑ ν ∈ S, p ν) := by ring
      _ ≤ 2 * W := by omega
  -- the logarithms are the sums of the counts
  have hlogG : ∑ ν ∈ range m, Nat.log 2 (G ν) =
      ∑ j ∈ Ico 1 (W + 1), ((range m).filter fun ν => 2 ^ j ≤ G ν).card := by
    rw [Finset.sum_congr rfl fun ν hν => log_eq_sum (G ν) W (hGW ν (Finset.mem_range.mp hν)),
      Finset.sum_comm]
    simp only [Finset.card_filter]
  have hlogμ : ∑ ν ∈ range m, Nat.log 2 (μ ν) =
      ∑ j ∈ Ico 1 (W + 1), ((range m).filter fun ν => 2 ^ j ≤ μ ν).card := by
    rw [Finset.sum_congr rfl fun ν hν => log_eq_sum (μ ν) W (hμW ν (Finset.mem_range.mp hν)),
      Finset.sum_comm]
    simp only [Finset.card_filter]
  have hlogm : Nat.log 2 (m + 1) ≤ m := Nat.lt_succ_iff.mp (Nat.log_lt_self 2 (by omega))
  have hnat : 2 * Nat.log 2 (m + 1) + ∑ ν ∈ range m, (2 * Nat.log 2 (G ν) +
      2 * Nat.log 2 (μ ν) + 2) ≤ 4 * m +
      2 * ∑ j ∈ Ico 1 (W + 1), ((range m).filter fun ν => 2 ^ j ≤ G ν).card +
      2 * ∑ j ∈ Ico 1 (W + 1), ((range m).filter fun ν => 2 ^ j ≤ μ ν).card := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      hlogG, hlogμ, Finset.sum_const, Finset.card_range, smul_eq_mul]
    omega
  -- the real estimate
  have hs2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hsW : √(2 * (W : ℝ)) = √2 * √(W : ℝ) := Real.sqrt_mul (by norm_num) _
  have hmR : (m : ℝ) ≤ √(2 * W) := by
    refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
    have : ((m * m : ℕ) : ℝ) ≤ ((2 * W : ℕ) : ℝ) := by exact_mod_cast (by nlinarith : m * m ≤ 2 * W)
    push_cast at this; nlinarith
  have hRG := sum_le_of_sq W W _ hrG
  have hRμ := sum_le_of_sq W W _ hrμ
  have hcast : ((2 * Nat.log 2 (m + 1) + ∑ ν ∈ range m, (2 * Nat.log 2 (G ν) +
      2 * Nat.log 2 (μ ν) + 2) : ℕ) : ℝ) ≤ 4 * m +
      2 * ∑ j ∈ Ico 1 (W + 1), (((range m).filter fun ν => 2 ^ j ≤ G ν).card : ℝ) +
      2 * ∑ j ∈ Ico 1 (W + 1), (((range m).filter fun ν => 2 ^ j ≤ μ ν).card : ℝ) := by
    exact_mod_cast hnat
  have hsqW := Real.sqrt_nonneg (W : ℝ)
  calc _ ≤ _ := hcast
    _ ≤ 4 * √(2 * W) + 2 * ((1 + √2) * √(2 * W)) + 2 * ((1 + √2) * √(2 * W)) := by linarith
    _ = (8 + 8 * √2) * √(W : ℝ) := by rw [hsW]; ring_nf; rw [Real.sq_sqrt (by norm_num)]; ring

/-- The code of a multiset of weight `W` has at most `(8 + 8√2) √W + 1 ≤ 19.4 √W + 1` bits. -/
private theorem msCode_length_sub_one (σ : Multiset ℕ) :
    (((msCode σ).length - 1 : ℕ) : ℝ) ≤ (8 + 8 * √2) * √(wt σ : ℝ) := by
  rw [length_msCode, Nat.add_sub_cancel_left, wt_eq_sum_distinctWts]
  exact len_bound _ (fun ν => (distinctWts σ).getD ν 0) (gapAt (distinctWts σ))
    (fun ν => σ.count ((distinctWts σ).getD ν 0 - 1)) (fun _ _ h h' => distinctWts_lt σ h h')
    (fun _ h => one_le_distinctWts σ h) (fun _ h => sum_gapAt σ h) (fun _ h => one_le_count σ h)

/-- The length bound of Lemma 4.1: the codes of the two multisets of a label of weight at most
`a ≥ 1` fit in `len(a)` bits. -/
theorem msCode_length_le {a : ℕ} (ha : 1 ≤ a) (l : Label) (hl : labelWt l ≤ a) :
    (msCode l.1).length + (msCode l.2).length ≤ codeWidth a := by
  have h1 := msCode_length_sub_one l.1
  have h2 := msCode_length_sub_one l.2
  have hl1 : 1 ≤ (msCode l.1).length := by rw [length_msCode]; omega
  have hl2 : 1 ≤ (msCode l.2).length := by rw [length_msCode]; omega
  obtain ⟨K, hK⟩ : ∃ K, (msCode l.1).length - 1 + ((msCode l.2).length - 1) = K := ⟨_, rfl⟩
  have hs2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2' : √2 ≤ 3 / 2 := by nlinarith [Real.sqrt_nonneg 2]
  have hw : (wt l.1 : ℝ) + wt l.2 ≤ a := by unfold labelWt at hl; exact_mod_cast hl
  have hsum : √(wt l.1 : ℝ) + √(wt l.2 : ℝ) ≤ √2 * √(a : ℝ) := by
    rw [← Real.sqrt_mul (by norm_num)]
    refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
    have e1 := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) (wt l.1))
    have e2 := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) (wt l.2))
    nlinarith [sq_nonneg (√(wt l.1 : ℝ) - √(wt l.2 : ℝ))]
  have hKR : (K : ℝ) ≤ 28 * √(a : ℝ) := by
    have : (K : ℝ) = (((msCode l.1).length - 1 : ℕ) : ℝ) + (((msCode l.2).length - 1 : ℕ) : ℝ) := by
      rw [← hK]; push_cast; ring
    rw [this]
    have hsa := Real.sqrt_nonneg (a : ℝ)
    have hs2n := Real.sqrt_nonneg (2 : ℝ)
    calc _ ≤ (8 + 8 * √2) * (√(wt l.1 : ℝ) + √(wt l.2 : ℝ)) := by linarith
      _ ≤ (8 + 8 * √2) * (√2 * √(a : ℝ)) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = (8 * √2 + 8 * (√2 * √2)) * √(a : ℝ) := by ring
      _ ≤ 28 * √(a : ℝ) := by rw [hs2]; nlinarith
  have hKsq : K * K ≤ 784 * a := by
    have hsa := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) a)
    have : (K : ℝ) * K ≤ 784 * a := by nlinarith [Nat.cast_nonneg (α := ℝ) K]
    exact_mod_cast this
  have := Nat.le_sqrt.mpr hKsq
  have ha0 : a ≠ 0 := by omega
  simp only [codeWidth, ha0, ↓reduceIte]
  omega

/-! ### Bits -/

/-- The number with bit `k` equal to entry `k` of the list. -/
def ofBits : List Bool → ℕ
  | [] => 0
  | b :: l => Nat.bit b (ofBits l)

theorem testBit_ofBits (l : List Bool) (k : ℕ) : (ofBits l).testBit k = l.getD k false := by
  induction l generalizing k with
  | nil => simp [ofBits]
  | cons b l ih => cases k <;> simp [ofBits, Nat.testBit_bit_succ, ih]

theorem ofBits_lt (l : List Bool) : ofBits l < 2 ^ l.length := by
  induction l with
  | nil => simp [ofBits]
  | cons b l ih =>
    rw [ofBits, Nat.bit_val, List.length_cons, pow_succ]
    cases b <;> simp <;> omega

theorem ofBits_append_replicate (l : List Bool) (n : ℕ) :
    ofBits (l ++ List.replicate n false) = ofBits l := by
  induction l with
  | nil =>
    induction n with
    | zero => rfl
    | succ n ih => simpa [List.replicate_succ, ofBits] using ih
  | cons b l ih => simp [ofBits, ih]

/-- The bits of an index of `w` bits, from the least significant. -/
def toBits : ℕ → ℕ → List Bool
  | 0, _ => []
  | w + 1, i => i.testBit 0 :: toBits w (i / 2)

theorem toBits_eq (w i : ℕ) : toBits w i = (List.range w).map i.testBit := by
  induction w generalizing i with
  | zero => rfl
  | succ w ih =>
    rw [toBits, ih, List.range_succ_eq_map, List.map_cons, List.map_map]
    congr 1
    refine List.map_congr_left fun k _ => ?_
    simp [Nat.testBit_succ]

theorem toBits_ofBits (c : List Bool) (w : ℕ) (h : c.length ≤ w) :
    toBits w (ofBits c) = c ++ List.replicate (w - c.length) false := by
  induction c generalizing w with
  | nil =>
    simp only [ofBits, List.length_nil, Nat.sub_zero, List.nil_append]
    clear h
    induction w with
    | zero => rfl
    | succ w ih => simp [toBits, ih, List.replicate_succ]
  | cons b c ih =>
    obtain ⟨w, rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by simp at h; omega⟩
    simp only [toBits, ofBits, Nat.testBit_bit_zero, Nat.bit_div_two, List.length_cons]
    rw [ih w (by simp at h; omega)]
    simp

theorem ofBits_toBits (w i : ℕ) (h : i < 2 ^ w) : ofBits (toBits w i) = i := by
  induction w generalizing i with
  | zero => simp only [pow_zero, Order.lt_one_iff] at h; subst h; rfl
  | succ w ih =>
    rw [toBits, ofBits, ih (i / 2) (by rw [pow_succ] at h; omega), Nat.bit_val, Nat.toNat_testBit]
    simp only [pow_zero, Nat.div_one]
    omega

/-! ### Labels and decoding -/

/-- **The code of a label** of weight at most `a`, as an index below `2^{len(a)}`. -/
def labelCode (a : ℕ) (l : Label) : ℕ := if a = 0 then 0 else ofBits (msCode l.1 ++ msCode l.2)

/-- Parse `n` pairs of gamma codes (a gap and a multiplicity) from the front of a bit list, the
weights starting after `p`: the multiset they describe and the rest. -/
def parseEntries : ℕ → ℕ → List Bool → Option (Multiset ℕ × List Bool)
  | 0, _, l => some (0, l)
  | n + 1, p, l => do
    let (gap, r) ← parseGamma l
    let (μ, r') ← parseGamma r
    let (σ, r'') ← parseEntries n (p + gap) r'
    pure (Multiset.replicate μ (p + gap - 1) + σ, r'')

/-- Parse a multiset code from the front of a bit list: the multiset and the rest, provided the
list starts with the code of that multiset. -/
def parseMs (l : List Bool) : Option (Multiset ℕ × List Bool) := do
  let (m1, rest) ← parseGamma l
  let (σ, r) ← parseEntries (m1 - 1) 0 rest
  if msCode σ ++ r = l then pure (σ, r) else none

private theorem parseEntries_eq (n p : ℕ) (G M : ℕ → ℕ) (hG : ∀ ν < n, 1 ≤ G ν)
    (hM : ∀ ν < n, 1 ≤ M ν) (r : List Bool) :
    parseEntries n p (((List.range n).flatMap fun ν => gamma (G ν) ++ gamma (M ν)) ++ r) =
      some (∑ ν ∈ range n, Multiset.replicate (M ν) (p + ∑ κ ∈ range (ν + 1), G κ - 1), r) := by
  induction n generalizing p G M with
  | zero => simp [parseEntries]
  | succ n ih =>
    have hl : (List.range (n + 1)).flatMap (fun ν => gamma (G ν) ++ gamma (M ν)) =
        gamma (G 0) ++ gamma (M 0) ++
          (List.range n).flatMap (fun ν => gamma (G (ν + 1)) ++ gamma (M (ν + 1))) := by
      rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    have ih' := fun q => ih q (fun ν => G (ν + 1)) (fun ν => M (ν + 1))
      (fun ν h => hG _ (by omega)) (fun ν h => hM _ (by omega))
    rw [hl, List.append_assoc, List.append_assoc]
    simp only [parseEntries, parseGamma_gamma _ (hG 0 (by omega)),
      parseGamma_gamma _ (hM 0 (by omega)), ih', Option.bind_eq_bind, Option.bind_some,
      Option.pure_def, Option.some.injEq, Prod.mk.injEq, and_true]
    rw [Finset.sum_range_succ' _ n, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [Finset.sum_range_succ' (fun κ => G κ) (ν + 1)]
    congr 2
    ring

theorem parseMs_msCode (σ : Multiset ℕ) (r : List Bool) : parseMs (msCode σ ++ r) =
    some (σ, r) := by
  have hpe : parseEntries (distinctWts σ).length 0
      (((List.range (distinctWts σ).length).flatMap fun ν =>
        gamma (gapAt (distinctWts σ) ν) ++ gamma (σ.count ((distinctWts σ).getD ν 0 - 1))) ++ r) =
        some (σ, r) := by
    rw [parseEntries_eq _ _ _ _ (fun _ h => one_le_gapAt σ h) (fun _ h => one_le_count σ h)]
    congr 2
    conv_rhs => rw [eq_sum_distinctWts σ]
    refine Finset.sum_congr rfl fun ν hν => ?_
    rw [sum_gapAt σ (Finset.mem_range.mp hν), zero_add]
  have hl : msCode σ ++ r = gamma ((distinctWts σ).length + 1) ++
      (((List.range (distinctWts σ).length).flatMap fun ν =>
        gamma (gapAt (distinctWts σ) ν) ++ gamma
            (σ.count ((distinctWts σ).getD ν 0 - 1))) ++ r) := by
    rw [msCode_eq, List.append_assoc]
  rw [parseMs, hl, parseGamma_gamma _ (by omega)]
  simp only [Option.bind_eq_bind, Option.bind_some, Nat.add_sub_cancel, hpe, ← hl]
  simp

theorem msCode_append_of_parseMs {l : List Bool} {σ : Multiset ℕ} {r : List Bool}
    (h : parseMs l = some (σ, r)) : msCode σ ++ r = l := by
  unfold parseMs at h
  rcases hg : parseGamma l with _ | ⟨m1, rest⟩
  · simp [hg] at h
  rcases he : parseEntries (m1 - 1) 0 rest with _ | ⟨σ', r'⟩
  · simp [hg, he] at h
  simp only [hg, he, Option.bind_eq_bind, Option.bind_some] at h
  split_ifs at h with hc
  · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hc

/-- **Decoding**: the label coded by an index of `len(a)` bits, if any, of weight at most `a` with
only zeros after the two codes. -/
def decodeLabel (a i : ℕ) : Option Label :=
  if a = 0 then (if i = 0 then some (0, 0) else none) else
  match parseMs (toBits (codeWidth a) i) with
  | none => none
  | some (σ₁, r) =>
    match parseMs r with
    | none => none
    | some (σ₂, r') => if r'.all (· = false) ∧ labelWt (σ₁, σ₂) ≤ a then some (σ₁, σ₂) else none

theorem labelCode_lt {a : ℕ} {l : Label} (hl : labelWt l ≤ a) : labelCode a l < 2 ^
    codeWidth a := by
  unfold labelCode
  split_ifs with ha
  · positivity
  · refine (ofBits_lt _).trans_le (Nat.pow_le_pow_right (by norm_num) ?_)
    rw [List.length_append]
    exact msCode_length_le (by omega) l hl

private theorem eq_zero_of_labelWt_le_zero {l : Label} (hl : labelWt l ≤ 0) : l = (0, 0) := by
  unfold labelWt at hl
  have h1 := card_le_wt l.1
  have h2 := card_le_wt l.2
  exact Prod.ext (Multiset.card_eq_zero.mp (by omega)) (Multiset.card_eq_zero.mp (by omega))

theorem decode_labelCode {a : ℕ} {l : Label} (hl : labelWt l ≤ a) :
    decodeLabel a (labelCode a l) = some l := by
  by_cases ha : a = 0
  · subst ha
    rw [eq_zero_of_labelWt_le_zero hl]
    simp [decodeLabel, labelCode]
  · have hlen := msCode_length_le (by omega) l hl
    simp only [decodeLabel, labelCode, ha, ↓reduceIte]
    rw [toBits_ofBits _ _ (by rw [List.length_append]; exact hlen), List.append_assoc]
    simp [parseMs_msCode, hl]

theorem labelCode_decode {a i : ℕ} {l : Label} (hi : i < 2 ^ codeWidth a)
    (h : decodeLabel a i = some l) : labelWt l ≤ a ∧ labelCode a l = i := by
  by_cases ha : a = 0
  · subst ha
    simp only [codeWidth, ↓reduceIte, pow_zero, Nat.lt_one_iff] at hi
    subst hi
    simp only [decodeLabel, ↓reduceIte, Option.some.injEq] at h
    subst h
    simp [labelWt, labelCode]
  · unfold decodeLabel at h
    simp only [ha, ↓reduceIte] at h
    cases h1 : parseMs (toBits (codeWidth a) i) with
    | none => simp [h1] at h
    | some x =>
    obtain ⟨σ₁, r⟩ := x
    cases h2 : parseMs r with
    | none => simp [h1, h2] at h
    | some y =>
    obtain ⟨σ₂, r'⟩ := y
    simp only [h1, h2] at h
    split_ifs at h with hc
    obtain rfl := (Option.some.inj h).symm
    refine ⟨hc.2, ?_⟩
    have e1 := msCode_append_of_parseMs h1
    have e2 := msCode_append_of_parseMs h2
    have hr' : r' = List.replicate r'.length false :=
      List.eq_replicate_iff.mpr ⟨rfl, fun b hb => by simpa using (List.all_eq_true.mp hc.1) b hb⟩
    rw [← ofBits_toBits _ _ hi, ← e1, ← e2, hr', ← List.append_assoc, ofBits_append_replicate]
    simp [labelCode, ha]

/-- **Summing over codes is summing over labels.** -/
theorem sum_codes {M : Type*} [AddCommMonoid M] (a : ℕ) (f : Label → M) :
    (∑ i ∈ range (2 ^ codeWidth a),
      match decodeLabel a i with
      | some l => if labelWt l = a then f l else 0
      | none => 0) = ∑ l ∈ labelsEq a, f l := by
  classical
  have hinj : Set.InjOn (labelCode a) (labelsEq a : Set Label) := fun l hl l' hl' h => by
    have e1 := decode_labelCode (mem_labelsEq.mp hl).le
    have e2 := decode_labelCode (mem_labelsEq.mp hl').le
    rw [h, e2] at e1
    exact (Option.some.inj e1).symm
  have hsub : (labelsEq a).image (labelCode a) ⊆ range (2 ^ codeWidth a) := fun i hi => by
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_range.mpr (labelCode_lt (mem_labelsEq.mp hl).le)
  rw [← Finset.sum_subset hsub, Finset.sum_image hinj]
  · refine Finset.sum_congr rfl fun l hl => ?_
    have hw := mem_labelsEq.mp hl
    simp only [decode_labelCode hw.le, hw, ↓reduceIte]
  · intro i hi hni
    rcases hd : decodeLabel a i with _ | l
    · rfl
    · simp only
      split_ifs with hw
      · exfalso
        obtain ⟨-, hc⟩ := labelCode_decode (Finset.mem_range.mp hi) hd
        exact hni (Finset.mem_image.mpr ⟨l, mem_labelsEq.mpr hw, hc⟩)
      · rfl

end Cslib.Complexity.NtimeDspace.Cube
