/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Code.Basic
public import CslibFrontier.Foundations.Data.Code.ListDecoding
import CslibFrontier.Foundations.Combinatorics.SetFamily.PairwiseIntersection
import CslibFrontier.Foundations.Data.Code.Plotkin
import CslibFrontier.Foundations.Data.Hamming
import Mathlib.Algebra.Order.Chebyshev

/-!
# The Johnson bound

Let `C` be a code of length `n` and minimum distance at least `d`, and let `w` be a word. Each
codeword `c` within distance `e` of `w` agrees with `w` on a set of at least `a = n - e`
coordinates, and two distinct codewords agree with each other, hence on the intersection of their
sets, on at most `t = n - d` coordinates. Counting the pairs of such codewords that agree with
`w` at a coordinate, and applying the Cauchy–Schwarz inequality to the numbers of codewords that
agree with `w` at each coordinate, the number `L` of codewords within distance `e` satisfies
`L * (a ^ 2 - n * t) ≤ n * (a - t)` (`Cslib.Code.card_filter_hammingDist_le_mul_le`). When
`a ^ 2 > n * t`, that is when `e < n - √(n * (n - d))`, a Hamming ball of radius `e` therefore
contains at most `n * (d - e)` codewords (`Cslib.Code.card_filter_hammingDist_le_le`), whatever
the alphabet: the **Johnson bound** [Johnson1962], [GuruswamiRudraSudan2019]. Listing the messages
whose codewords lie in the ball is then a list decoder up to radius `e / n` with lists of
`n * (d - e)` messages (`Cslib.Code.exists_listCode_listDecodes`), in the sense of
`Cslib.ListCode.ListDecodes`; the decoder is chosen noncomputably, and no running time is claimed.

Over an alphabet of `q` letters the radius improves. If `a` of the `M` codewords in the ball agree
with `w` at a coordinate, the other `M - a` spread over `q - 1` letters, so at least
`a ^ 2 + (M - a) ^ 2 / (q - 1)` ordered pairs of them agree there. Combining this with the
double counting behind the Plotkin bound (`Cslib.Code.sum_sum_hammingDist_add_sum_sum_sum_ite`)
gives, for `q e ≤ (q - 1) n`,
`M ((q - 1) (n - e) ^ 2 + e ^ 2 - (q - 1) n (n - d)) ≤ (q - 1) n d`
(`Cslib.Code.card_filter_hammingDist_le_mul_le_of_mul_le`): the **q-ary Johnson bound**
[GuruswamiRudraSudan2019, Theorem 7.3.1], which the source proves for `q = 2` and leaves to its
Exercise 7.7 for general `q`. If `d ≤ (1 - 1 / q) n`, its hypotheses hold exactly when
`e / n < J_q(d / n)`, where `J_q(δ) = (1 - 1 / q) (1 - √(1 - q δ / (q - 1)))`; for larger `d` they
hold whenever `q e ≤ (q - 1) n`. A ball of such a radius then contains at most `(q - 1) n d`
codewords (`Cslib.Code.card_filter_hammingDist_le_le_of_mul_le`): the radius of Exercise 7.7, with
a list size within the `q d n` of Theorem 7.3.1 (Exercise 7.7 states `2 q n`). As `q` grows,
`J_q(δ)` decreases to the alphabet-free radius `1 - √(1 - δ)`.

## Main results

* `Cslib.Code.card_mul_sub_le_of_le_card_of_card_inter_le`,
  `Cslib.Code.card_mul_le_two_mul_of_le_card_of_card_inter_le`: double counting for families of
  agreement sets with bounded pairwise intersections.
* `Cslib.Code.card_filter_hammingDist_le_mul_le`: the Johnson bound, in agreement form.
* `Cslib.Code.card_filter_hammingDist_le_le`,
  `Cslib.Code.card_filter_hammingDist_le_mul_le_two_mul`: the Johnson bound on list sizes.
* `Cslib.Code.exists_listCode_listDecodes`: list decoding up to the Johnson radius.
* `Cslib.Code.card_filter_hammingDist_le_mul_le_of_mul_le`,
  `Cslib.Code.card_filter_hammingDist_le_le_of_mul_le`: the q-ary Johnson bound.

## References

* [S. M. Johnson, *A new upper bound for error-correcting codes*][Johnson1962]
* [V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*][GuruswamiRudraSudan2019]
-/

public section

namespace Cslib.Code

open Finset

variable {ι α : Type*} [Fintype ι] [DecidableEq α]

/-- **Double counting for the Johnson bound.** If `L` sets `B c ⊆ ι` of size `a` meet pairwise in
at most `t` elements, then `L * a ^ 2 ≤ n * (a + (L - 1) * t)`, where `n = |ι|`. -/
private theorem card_mul_sq_le {κ : Type*} [DecidableEq ι] (L : Finset κ)
    (B : κ → Finset ι) {a t : ℕ} (hB : ∀ c ∈ L, #(B c) = a)
    (hinter : ∀ c ∈ L, ∀ c' ∈ L, c ≠ c' → #(B c ∩ B c') ≤ t) :
    #L * a ^ 2 ≤ Fintype.card ι * (a + (#L - 1) * t) := by
  classical
  have hrow : ∀ c ∈ L, ∑ c' ∈ L, #(B c ∩ B c') ≤ a + (#L - 1) * t := fun c hc => by
    rw [← add_sum_erase L _ hc, inter_self, hB c hc, ← card_erase_of_mem hc, ← smul_eq_mul]
    gcongr
    exact sum_le_card_nsmul _ _ _ fun c' hc' =>
      hinter c hc c' (mem_of_mem_erase hc') (ne_of_mem_erase hc').symm
  have hcs := sq_sum_card_le_card_mul_sum_sum_card_inter L B (U := univ) fun _ _ => subset_univ _
  rw [sum_congr rfl hB, sum_const, smul_eq_mul, card_univ] at hcs
  rcases Nat.eq_zero_or_pos #L with hL0 | hL0
  · simp [hL0]
  refine Nat.le_of_mul_le_mul_left ?_ hL0
  linarith [hcs.trans (Nat.mul_le_mul_left (Fintype.card ι)
    ((sum_le_sum hrow).trans_eq (by rw [sum_const, smul_eq_mul])))]

/-- **Double counting for agreement sets.** If each `c ∈ L` has a set `S c ⊆ ι` of size at least
`a`, and distinct members of `L` meet in at most `t` elements, then
`#L * (a ^ 2 - |ι| * t) ≤ |ι| * (a - t)`. -/
theorem card_mul_sub_le_of_le_card_of_card_inter_le {κ : Type*} [DecidableEq ι] (L : Finset κ)
    (S : κ → Finset ι) {a t : ℕ} (ha : ∀ c ∈ L, a ≤ #(S c))
    (ht : ∀ c ∈ L, ∀ c' ∈ L, c ≠ c' → #(S c ∩ S c') ≤ t) :
    #L * (a ^ 2 - Fintype.card ι * t) ≤ Fintype.card ι * (a - t) := by
  classical
  set n := Fintype.card ι
  choose! B hBsub hBcard using fun c hc => exists_subset_card_eq (ha c hc)
  have hinter : ∀ c ∈ L, ∀ c' ∈ L, c ≠ c' → #(B c ∩ B c') ≤ t := fun c hc c' hc' hne =>
    (card_le_card (inter_subset_inter (hBsub c hc) (hBsub c' hc'))).trans (ht c hc c' hc' hne)
  have key := card_mul_sq_le L B hBcard hinter
  rcases le_or_gt (a ^ 2) (n * t) with h | h
  · simp [Nat.sub_eq_zero_of_le h]
  rcases Nat.eq_zero_or_pos #L with hL | hL
  · simp [hL]
  obtain ⟨c₀, hc₀⟩ := card_pos.1 hL
  have han : a ≤ n := (ha c₀ hc₀).trans (card_le_univ (S c₀))
  have hat : t ≤ a := by_contra fun hta => by
    nlinarith [Nat.mul_le_mul_left n (not_le.1 hta).le, Nat.mul_le_mul_right a han]
  zify [h.le, hat, Nat.one_le_iff_ne_zero.2 hL.ne'] at key ⊢
  nlinarith

/-- **Double counting for agreement sets, `2 * |ι| / a` form.** If each `c ∈ L` has a set
`S c ⊆ ι` of size at least `a`, distinct members of `L` meet in at most `t` elements, and
`2 * |ι| * t ≤ a ^ 2`, then `#L * a ≤ 2 * |ι|`. -/
theorem card_mul_le_two_mul_of_le_card_of_card_inter_le {κ : Type*} [DecidableEq ι] (L : Finset κ)
    (S : κ → Finset ι) {a t : ℕ} (ha : ∀ c ∈ L, a ≤ #(S c))
    (ht : ∀ c ∈ L, ∀ c' ∈ L, c ≠ c' → #(S c ∩ S c') ≤ t)
    (h2 : 2 * Fintype.card ι * t ≤ a ^ 2) :
    #L * a ≤ 2 * Fintype.card ι := by
  rcases Nat.eq_zero_or_pos a with rfl | ha0
  · simp
  have hsub := card_mul_sub_le_of_le_card_of_card_inter_le L S ha ht
  have h2' : a ^ 2 ≤ 2 * (a ^ 2 - Fintype.card ι * t) := by rw [Nat.mul_assoc] at h2; omega
  refine Nat.le_of_mul_le_mul_right ?_ ha0
  nlinarith [Nat.mul_le_mul_left #L h2', Nat.mul_le_mul_left (Fintype.card ι) (Nat.sub_le a t)]

private theorem le_card_filter_eq_of_hammingDist_le {w : ι → α} {e : ℕ} {c : ι → α}
    (hc : hammingDist c w ≤ e) :
    Fintype.card ι - e ≤ #({i | c i = w i} : Finset ι) := by
  have := card_filter_eq_add_hammingDist c w
  omega

private theorem card_inter_filter_eq_le_of_le_minDist [DecidableEq ι] {C : Finset (ι → α)} {d : ℕ}
    (hd : (d : ℕ∞) ≤ minDist (C : Set (ι → α))) (w : ι → α) {c c' : ι → α}
    (hc : c ∈ C) (hc' : c' ∈ C) (hne : c ≠ c') :
    #(({i | c i = w i} : Finset ι) ∩ ({i | c' i = w i} : Finset ι)) ≤ Fintype.card ι - d := by
  have hsub : #(({i | c i = w i} : Finset ι) ∩ ({i | c' i = w i} : Finset ι)) ≤
      #({i | c i = c' i} : Finset ι) :=
    card_le_card fun i => by simp +contextual
  have h1 := card_filter_eq_add_hammingDist c c'
  have h2 := Nat.cast_le.1 (le_minDist_iff.1 hd c hc c' hc' hne)
  omega

/-- **The Johnson bound**, in agreement form: for a code of length `n` and minimum distance at
least `d`, the number `L` of codewords within distance `e` of a word `w` satisfies
`L * ((n - e) ^ 2 - n * (n - d)) ≤ n * (d - e)`. It bounds `L` when `n * (n - d) < (n - e) ^ 2`
and says nothing otherwise. -/
theorem card_filter_hammingDist_le_mul_le {C : Finset (ι → α)} {d : ℕ}
    (hd : (d : ℕ∞) ≤ minDist (C : Set (ι → α))) (w : ι → α) (e : ℕ) :
    #{c ∈ C | hammingDist c w ≤ e} *
        ((Fintype.card ι - e) ^ 2 - Fintype.card ι * (Fintype.card ι - d)) ≤
      Fintype.card ι * (d - e) := by
  classical
  exact (card_mul_sub_le_of_le_card_of_card_inter_le {c ∈ C | hammingDist c w ≤ e}
    (fun c => {i | c i = w i}) (fun _ hc => le_card_filter_eq_of_hammingDist_le (mem_filter.1 hc).2)
    (fun _ hc _ hc' => card_inter_filter_eq_le_of_le_minDist hd w
      (mem_filter.1 hc).1 (mem_filter.1 hc').1)).trans (Nat.mul_le_mul_left _ (by omega))

/-- **The Johnson bound** [Johnson1962]: if `n * (n - d) < (n - e) ^ 2`, that is if
`e < n - √(n * (n - d))`, a Hamming ball of radius `e` contains at most `n * (d - e)` codewords of a
code of length `n` and minimum distance at least `d`, whatever the alphabet. -/
theorem card_filter_hammingDist_le_le {C : Finset (ι → α)} {d e : ℕ}
    (hd : (d : ℕ∞) ≤ minDist (C : Set (ι → α)))
    (h : Fintype.card ι * (Fintype.card ι - d) < (Fintype.card ι - e) ^ 2) (w : ι → α) :
    #{c ∈ C | hammingDist c w ≤ e} ≤ Fintype.card ι * (d - e) :=
  (Nat.le_mul_of_pos_right _ (Nat.sub_pos_of_lt h)).trans
    (card_filter_hammingDist_le_mul_le hd w e)

/-- **The Johnson bound, `2 * n / (n - e)` form**: if `2 * n * (n - d) ≤ (n - e) ^ 2`, the number
`L` of codewords within distance `e` of a word `w` satisfies `L * (n - e) ≤ 2 * n`. -/
theorem card_filter_hammingDist_le_mul_le_two_mul {C : Finset (ι → α)} {d e : ℕ}
    (hd : (d : ℕ∞) ≤ minDist (C : Set (ι → α)))
    (h : 2 * Fintype.card ι * (Fintype.card ι - d) ≤ (Fintype.card ι - e) ^ 2) (w : ι → α) :
    #{c ∈ C | hammingDist c w ≤ e} * (Fintype.card ι - e) ≤ 2 * Fintype.card ι := by
  classical
  exact card_mul_le_two_mul_of_le_card_of_card_inter_le {c ∈ C | hammingDist c w ≤ e}
    (fun c => {i | c i = w i}) (fun _ hc => le_card_filter_eq_of_hammingDist_le (mem_filter.1 hc).2)
    (fun _ hc _ hc' => card_inter_filter_eq_le_of_le_minDist hd w
      (mem_filter.1 hc).1 (mem_filter.1 hc').1) h

/-- **List decoding up to the Johnson radius.** Let `enc` be an injective encoding of a finite
nonempty set of messages whose codewords have minimum distance at least `d`. If
`n * (n - d) < (n - e) ^ 2`, some list decoder with lists of `n * (d - e)` messages list decodes
`enc` up to radius `e / n`: it lists the messages whose codewords are within distance `e` of the
received word. -/
theorem exists_listCode_listDecodes {M : Type*} [Finite M] [Nonempty M]
    {enc : M → ι → α} (henc : Function.Injective enc) {d e : ℕ}
    (hd : (d : ℕ∞) ≤ minDist (Set.range enc))
    (h : Fintype.card ι * (Fintype.card ι - d) < (Fintype.card ι - e) ^ 2) :
    ∃ C : ListCode M ι α (Fintype.card ι * (d - e)),
      C.encode = enc ∧ C.ListDecodes (e / Fintype.card ι) := by
  classical
  have := Fintype.ofFinite M
  have hrange : Set.range enc = ((univ.image enc : Finset (ι → α)) : Set (ι → α)) := by simp
  have hn : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 fun h0 => by simp [h0] at h
  rw [← isListDecodable_range_iff_exists_listCode henc, hrange, isListDecodable_finset_iff]
  intro w
  calc #{c ∈ univ.image enc |
          (hammingDist c w : ℝ) ≤ (e : ℝ) / Fintype.card ι * Fintype.card ι}
      = #{c ∈ univ.image enc | hammingDist c w ≤ e} :=
        congrArg Finset.card (filter_congr fun _ _ => by rw [div_mul_cancel₀ _ hn, Nat.cast_le])
    _ ≤ Fintype.card ι * (d - e) := card_filter_hammingDist_le_le (hrange ▸ hd) h w

/-! ### The q-ary Johnson bound -/

section Qary

variable [Fintype α]

omit [Fintype ι] in
/-- **The column bound for the q-ary Johnson bound.** If `a` of the `M` words of `L` have the
letter `w i` at the coordinate `i`, then `(q - 1) a ^ 2 + (M - a) ^ 2` is at most `q - 1` times the
number of ordered pairs of words of `L` that agree at `i`. -/
private theorem sub_one_mul_sq_add_sq_le_sub_one_mul_sum_sum_ite (L : Finset (ι → α))
    (w : ι → α) (i : ι) :
    ((Fintype.card α : ℤ) - 1) * (#{x ∈ L | x i = w i} : ℤ) ^ 2 +
        ((#L : ℤ) - #{x ∈ L | x i = w i}) ^ 2 ≤
      ((Fintype.card α : ℤ) - 1) * ∑ x ∈ L, ∑ y ∈ L, (if x i = y i then 1 else 0) := by
  have hsq : (∑ x ∈ L, ∑ y ∈ L, (if x i = y i then 1 else 0) : ℤ) =
      ∑ b : α, (#{x ∈ L | x i = b} : ℤ) ^ 2 := by
    exact_mod_cast sum_sum_ite_eq_sum_sq L i
  have hC : #L = ∑ b : α, #{x ∈ L | x i = b} :=
    card_eq_sum_card_fiberwise fun x _ => mem_coe.2 (mem_univ (x i))
  -- Cauchy–Schwarz over the other `q - 1` letters
  have hcs := sq_sum_le_card_mul_sum_sq (s := univ.erase (w i))
    (f := fun b => (#{x ∈ L | x i = b} : ℤ))
  rw [card_erase_of_mem (mem_univ _), card_univ,
    Nat.cast_sub (Fintype.card_pos_iff.2 ⟨w i⟩), Nat.cast_one] at hcs
  rw [hsq, hC, Nat.cast_sum, ← add_sum_erase _ _ (mem_univ (w i)),
    ← add_sum_erase _ _ (mem_univ (w i))]
  linarith

/-- The q-ary Johnson bound over the integers. -/
private theorem card_filter_hammingDist_le_mul_le_of_mul_le_int [Nonempty α]
    {C : Finset (ι → α)} {d : ℕ} (hd : (d : ℕ∞) ≤ minDist (C : Set (ι → α))) (w : ι → α)
    {e : ℕ} (he : Fintype.card α * e ≤ (Fintype.card α - 1) * Fintype.card ι) :
    (#{c ∈ C | hammingDist c w ≤ e} : ℤ) *
        (((Fintype.card α : ℤ) - 1) * ((Fintype.card ι : ℤ) - e) ^ 2 + (e : ℤ) ^ 2 -
          ((Fintype.card α : ℤ) - 1) * Fintype.card ι * ((Fintype.card ι : ℤ) - d)) ≤
      ((Fintype.card α : ℤ) - 1) * Fintype.card ι * d := by
  classical
  set n := Fintype.card ι
  set q := Fintype.card α
  set L : Finset (ι → α) := {c ∈ C | hammingDist c w ≤ e}
  have hq : 1 ≤ q := Fintype.card_pos
  have hq1 : (0 : ℤ) ≤ (q : ℤ) - 1 := sub_nonneg.2 (Nat.one_le_cast.2 hq)
  have hn : (0 : ℤ) ≤ n := n.cast_nonneg
  zify [hq] at he
  -- `a i` words of `L` agree with `w` at `i`
  set a : ι → ℕ := fun i => #{x ∈ L | x i = w i}
  set A : ℤ := ∑ i, (a i : ℤ)
  have hA : (#L : ℤ) * ((n : ℤ) - e) ≤ A := by
    have hswap : A = ∑ x ∈ L, (#({i | x i = w i} : Finset ι) : ℤ) := by
      simpa only [A, a, card_filter, Nat.cast_sum] using (sum_comm : ∑ i : ι, ∑ x ∈ L, _ = _)
    rw [hswap, ← nsmul_eq_mul]
    exact card_nsmul_le_sum _ _ _ fun x hx => by
      have := le_card_filter_eq_of_hammingDist_le (mem_filter.1 hx).2
      omega
  -- pairwise distances and agreements
  set P : ℕ := ∑ i, ∑ x ∈ L, ∑ y ∈ L, (if x i = y i then 1 else 0)
  have hDP : ∑ x ∈ L, ∑ y ∈ L, hammingDist x y + P = n * #L ^ 2 := by
    have h := sum_sum_hammingDist_add_sum_sum_sum_ite (C := L) (T := univ)
      (fun _ _ _ _ i hi => absurd (mem_univ i) hi)
    rwa [card_univ, sum_congr rfl fun x _ => sum_comm, sum_comm (s := L) (t := (univ : Finset ι))]
      at h
  have hD := card_mul_card_sub_one_mul_le_sum_sum_hammingDist
    (hd.trans (minDist_anti fun x (hx : x ∈ L) => (mem_filter.1 hx).1))
  rcases Nat.eq_zero_or_pos #L with hM | hM
  · simpa [hM] using mul_nonneg (mul_nonneg hq1 hn) d.cast_nonneg
  set M := #L
  have hPZ : (P : ℤ) ≤ n * (M : ℤ) ^ 2 - M * ((M : ℤ) - 1) * d := by
    zify [hM] at hDP hD
    linarith
  -- sum the column bounds
  have hcol : ((q : ℤ) - 1) * ∑ i, (a i : ℤ) ^ 2 + ∑ i, ((M : ℤ) - a i) ^ 2 ≤
      ((q : ℤ) - 1) * P := by
    push_cast [P]
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    exact sum_le_sum fun i _ => sub_one_mul_sq_add_sq_le_sub_one_mul_sum_sum_ite L w i
  -- Cauchy–Schwarz on both sums
  have hcs1 : A ^ 2 ≤ n * ∑ i, (a i : ℤ) ^ 2 := by
    simpa only [card_univ] using sq_sum_le_card_mul_sum_sq (s := (univ : Finset ι))
      (f := fun i => (a i : ℤ))
  have hcs2 : ((n : ℤ) * M - A) ^ 2 ≤ n * ∑ i, ((M : ℤ) - a i) ^ 2 := by
    simpa only [card_univ, sum_sub_distrib, sum_const, nsmul_eq_mul] using
      sq_sum_le_card_mul_sum_sq (s := (univ : Finset ι)) (f := fun i => (M : ℤ) - a i)
  -- the left side increases in `A` beyond `n M / q`, and `A ≥ M (n - e) ≥ n M / q`
  have hM0 : (0 : ℤ) < M := by exact_mod_cast hM
  have hA0 : (n : ℤ) * M ≤ q * (M * ((n : ℤ) - e)) := by
    linarith [mul_le_mul_of_nonneg_left he hM0.le]
  have hqA := mul_le_mul_of_nonneg_left hA (q.cast_nonneg : (0 : ℤ) ≤ q)
  have hmono : 0 ≤ (A - M * ((n : ℤ) - e)) * (q * (A + M * ((n : ℤ) - e)) - 2 * n * M) :=
    mul_nonneg (sub_nonneg.2 hA) (by linarith)
  -- combine with `P = n M² - D ≤ n M² - M (M - 1) d`, then divide by `M`
  refine le_of_mul_le_mul_left ?_ hM0
  linarith [mul_le_mul_of_nonneg_left hcs1 hq1, mul_le_mul_of_nonneg_left hcol hn,
    mul_le_mul_of_nonneg_left hPZ (mul_nonneg hq1 hn)]

/-- **The q-ary Johnson bound**, in agreement form [GuruswamiRudraSudan2019, Theorem 7.3.1, at the
radius of Exercise 7.7 for general `q`]: for a code of length `n` and minimum distance at least `d`
over `q` letters, and a radius `e` with `q e ≤ (q - 1) n`, the number `M` of codewords within
distance `e` of a word `w` satisfies
`M ((q - 1) (n - e) ^ 2 + e ^ 2 - (q - 1) n (n - d)) ≤ (q - 1) n d`. It bounds `M` when
`(q - 1) n (n - d) < (q - 1) (n - e) ^ 2 + e ^ 2` and says nothing otherwise. The hypothesis
`q e ≤ (q - 1) n` cannot be dropped: for `q = 2` and `e = d = n` the ball is the whole space. -/
theorem card_filter_hammingDist_le_mul_le_of_mul_le [Nonempty α] {C : Finset (ι → α)} {d : ℕ}
    (hd : (d : ℕ∞) ≤ minDist (C : Set (ι → α))) (w : ι → α) {e : ℕ}
    (he : Fintype.card α * e ≤ (Fintype.card α - 1) * Fintype.card ι) :
    #{c ∈ C | hammingDist c w ≤ e} *
        ((Fintype.card α - 1) * (Fintype.card ι - e) ^ 2 + e ^ 2 -
          (Fintype.card α - 1) * Fintype.card ι * (Fintype.card ι - d)) ≤
      (Fintype.card α - 1) * Fintype.card ι * d := by
  have h := card_filter_hammingDist_le_mul_le_of_mul_le_int hd w he
  set n := Fintype.card ι
  set q := Fintype.card α
  set M := #{c ∈ C | hammingDist c w ≤ e}
  have hq : 1 ≤ q := Fintype.card_pos
  have hen : e ≤ n := Nat.le_of_mul_le_mul_left (he.trans (Nat.mul_le_mul_right n (q.sub_le 1))) hq
  rcases le_or_gt ((q - 1) * (n - e) ^ 2 + e ^ 2) ((q - 1) * n * (n - d)) with hBX | hBX
  · simp [Nat.sub_eq_zero_of_le hBX]
  -- `(q - 1) n (n - d)` over `ℕ` is at least its value over `ℤ`, with equality when `d ≤ n`
  have hdn : (n : ℤ) - d ≤ ((n - d : ℕ) : ℤ) := by omega
  have hq1 : (0 : ℤ) ≤ (q : ℤ) - 1 := sub_nonneg.2 (Nat.one_le_cast.2 hq)
  zify [hq, hen, hBX.le]
  linarith [mul_nonneg M.cast_nonneg (mul_nonneg (mul_nonneg hq1 n.cast_nonneg) (sub_nonneg.2 hdn))]

/-- **The q-ary Johnson bound** on list sizes [GuruswamiRudraSudan2019, Theorem 7.3.1, at the
radius of Exercise 7.7 for general `q`]: if `q e ≤ (q - 1) n` and
`(q - 1) n (n - d) < (q - 1) (n - e) ^ 2 + e ^ 2`, that is if `e / n < J_q(d / n)` when
`d ≤ (1 - 1 / q) n`, a Hamming ball of radius `e` contains at most `(q - 1) n d` codewords of a code
of length `n` and minimum distance at least `d` over `q` letters. The list size `(q - 1) n d` is
within the `q d n` of Theorem 7.3.1 (Exercise 7.7 states `2 q n`). -/
theorem card_filter_hammingDist_le_le_of_mul_le [Nonempty α] {C : Finset (ι → α)} {d e : ℕ}
    (hd : (d : ℕ∞) ≤ minDist (C : Set (ι → α)))
    (he : Fintype.card α * e ≤ (Fintype.card α - 1) * Fintype.card ι)
    (h : (Fintype.card α - 1) * Fintype.card ι * (Fintype.card ι - d) <
      (Fintype.card α - 1) * (Fintype.card ι - e) ^ 2 + e ^ 2) (w : ι → α) :
    #{c ∈ C | hammingDist c w ≤ e} ≤ (Fintype.card α - 1) * Fintype.card ι * d :=
  (Nat.le_mul_of_pos_right _ (Nat.sub_pos_of_lt h)).trans
    (card_filter_hammingDist_le_mul_le_of_mul_le hd w he)

end Qary

end Cslib.Code
