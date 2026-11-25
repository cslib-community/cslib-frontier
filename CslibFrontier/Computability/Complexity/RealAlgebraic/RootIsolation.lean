/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.SturmBitBounds
public import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.TotalIsolation
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Gcd
import CslibFrontier.Foundations.Data.Rat.Basic
import Mathlib.Data.List.GetD

/-!
# Polynomial-Time Bit Complexity of Rational Real-Root Isolation on Multi-Tape Turing Machines

This module proves that the Sturm-bisection real-root isolators `Cslib.RealRoot.isolateRoots` and
`Cslib.RealRoot.isolateRootsTotal` on little-endian rational coefficient lists (`List ℚ`) are
computable in polynomial time (`Turing.MultiTapeTM.ComputableInPolyTime`) on multi-tape Turing
machines with respect to the binary rational coefficient-list encoding `encRatPoly` and the framed
interval-list encoding `encRootIntervals`.

Because `Turing.MultiTapeTM.encRat` stores every rational in reduced form `(q.num, q.den)`, every
intermediate polynomial in `Cslib.RealRoot.sturmSeqList cs` satisfies the Sylvester/Hadamard
coefficient bit-length bound `Cslib.RealRoot.hasCoeffBitBound_of_mem_sturmSeqList`
(`O(n³ B)` bits), every active bisection frontier has at most `2 * cs.length` intervals by
`Cslib.RealRoot.card_active_sturm_intervals_le`, and all bisection depths and dyadic interval
endpoints remain polynomially bounded in the input bit-length `(encRatPoly cs).length`.

## Main definitions

* `Cslib.Complexity.RealAlgebraic.encRootInterval`: structure encoding of
  `Cslib.RealRoot.RootInterval` as the framed pair of its `encRat` endpoints `(lower, upper)`.
* `Cslib.Complexity.RealAlgebraic.encRatPoly`: framed list encoding `encList encRat` of a rational
  polynomial's little-endian coefficient list.
* `Cslib.Complexity.RealAlgebraic.encSturmSeq`: framed list encoding `encList encRatPoly` of a
  rational Sturm sequence.
* `Cslib.Complexity.RealAlgebraic.encRootIntervals`: framed list encoding
  `encList encRootInterval` of isolating rational intervals.

## Main results

* `Cslib.Complexity.RealAlgebraic.hasCoeffBitBound_length_encRatPoly`: every input `cs : List ℚ`
  satisfies `HasCoeffBitBound (encRatPoly cs).length cs`.
* `Cslib.Complexity.RealAlgebraic.sturmSeqList_computableInPolyTime`: `sturmSeqList` is computable
  in polynomial time from `encRatPoly` to `encSturmSeq`.
* `Cslib.Complexity.RealAlgebraic.sturmVariationsList_computableInPolyTime`: `sturmVariationsList`
  is computable in polynomial time from `encPair encSturmSeq encRat` to `encUnary`.
* `Cslib.Complexity.RealAlgebraic.cauchyBoundNat_computableInPolyTime` and
  `Cslib.Complexity.RealAlgebraic.mignotteBisectionDepth_computableInPolyTime`: Cauchy root bounds
  (`encNat`) and Mignotte bisection depths (`encUnary`) are computable in polynomial time.
* `Cslib.Complexity.RealAlgebraic.isolateRoots_computableInPolyTime` and
  `Cslib.Complexity.RealAlgebraic.isolateRootsTotal_computableInPolyTime`: certified Sturm-bisection
  real-root isolation (both with and without strict closed-interval separation) is computable in
  polynomial time on multi-tape Turing machines.

## References

The `List ℚ` Sturm-bisection implementation and its unconditional multi-tape Turing-machine
polynomial-time certification (`isolateRoots_computableInPolyTime`,
`isolateRootsTotal_computableInPolyTime` for all `encRatPoly`-encoded rational coefficient lists)
are this library's own construction, distinct from the mathematical Sturm-counting and
root-separation ingredients below; [BasuPollackRoy2006], §10.2, Algorithm 10.4 (pp. 373–374, over
integer coefficients using Bernstein coefficient variation and returning open rational intervals
and singleton rational roots) is related work.

* [BasuPollackRoy2006], Theorem 2.50, p. 52 (Sturm counting ingredient; adapted to `(a, b]` over
  `ℝ`)
* [Mahler1964], pp. 257–262 (discriminant/Mahler-measure separation ingredient; equation locator
  unverified)
* [Mignotte1982], Theorem 3 (pp. 260–261) and Theorem 5 with integral corollary (p. 262; Landau
  norm comparison and root-separation ingredients)
-/

public section

namespace Cslib.Complexity.RealAlgebraic

open Cslib.RealRoot Polynomial Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

/-! ### Domain encodings and coefficient bit-length bridges -/

/-- Framed tuple encoding of a rational isolating interval `RootInterval` as `(lower, upper)` with
each endpoint encoded in reduced signed-binary/binary form by `encRat`. -/
enc_structure encRootInterval : RootInterval where
  lower : encRat,
  upper : encRat

/-- Framed list encoding of a rational polynomial's little-endian coefficient list `List ℚ`, with
each coefficient encoded in reduced binary form by `encRat`. -/
abbrev encRatPoly : List ℚ ↪ List Bool :=
  encList encRat

/-- Framed list encoding of a rational Sturm sequence `List (List ℚ)`, with each polynomial entry
encoded by `encRatPoly`. -/
abbrev encSturmSeq : List (List ℚ) ↪ List Bool :=
  encList encRatPoly

/-- Framed list encoding of a list of rational isolating intervals `List RootInterval`, with each
interval encoded by `encRootInterval`. -/
abbrev encRootIntervals : List RootInterval ↪ List Bool :=
  encList encRootInterval

private theorem num_den_le_of_length_encRat_le {q : ℚ} {L : ℕ} (h : (encRat q).length ≤ L) :
    q.num.natAbs ≤ 2 ^ L ∧ q.den ≤ 2 ^ L :=
  have hpow := Nat.pow_le_pow_right zero_lt_two h
  ⟨(natAbs_num_lt_two_pow_length_encRat q).le.trans hpow,
    (den_lt_two_pow_length_encRat q).le.trans hpow⟩

/-- Every rational coefficient list `cs` satisfies `HasCoeffBitBound (encRatPoly cs).length cs`. -/
theorem hasCoeffBitBound_length_encRatPoly (cs : List ℚ) :
    HasCoeffBitBound (encRatPoly cs).length cs := fun q hq =>
  num_den_le_of_length_encRat_le (SizedListEncoding.length_elem_le (encA := encRat) cs q hq)

private theorem hasCoeffBitBound_mono {B B' : ℕ} {l : List ℚ} (h : HasCoeffBitBound B l)
    (hB : B ≤ B') : HasCoeffBitBound B' l := fun q hq =>
  have hpow := Nat.pow_le_pow_right zero_lt_two hB
  ⟨(h q hq).1.trans hpow, (h q hq).2.trans hpow⟩

private theorem size_two_pow_le (k : ℕ) : (2 ^ k).size ≤ k + 1 :=
  Nat.size_le.mpr (Nat.pow_lt_pow_right (by omega) (by omega))

private theorem length_encRat_le_of_pow_bound {q : ℚ} {K : ℕ}
    (hn : q.num.natAbs ≤ 2 ^ K) (hd : q.den ≤ 2 ^ K) :
    (encRat q).length ≤ 3 * K + 6 := by
  have h := length_encRat_le q hn hd
  have hs := size_two_pow_le K
  omega

/-- A fraction `z / D` with `|z|, D ≤ 2 ^ K` has reduced numerator and denominator `≤ 2 ^ K`. -/
private theorem num_den_div_le {z : ℤ} {D K : ℕ} (hD : 1 ≤ D) (hz : z.natAbs ≤ 2 ^ K)
    (hDK : D ≤ 2 ^ K) : ((z : ℚ) / D).num.natAbs ≤ 2 ^ K ∧ ((z : ℚ) / D).den ≤ 2 ^ K := by
  have hD0 : (D : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (by omega)
  rw [← Int.cast_natCast D, ← Rat.divInt_eq_div]
  exact ⟨(Rat.natAbs_num_divInt_le z D hD0).trans hz,
    (Rat.den_divInt_le z D hD0).trans (by rwa [Int.natAbs_natCast])⟩

private theorem length_encRatPoly_le_of_bitBound {cs : List ℚ} {n K : ℕ}
    (hlen : cs.length ≤ n) (hB : HasCoeffBitBound K cs) :
    (encRatPoly cs).length ≤ n * (6 * K + 13) :=
  (length_encList_le encRat cs (b := 3 * K + 6) fun q hq =>
    length_encRat_le_of_pow_bound (hB q hq).1 (hB q hq).2).trans (by nlinarith)

attribute [local irreducible] encRat encIntBin encNat

/-! ### Polynomial-time `CoeffList` operations over `ℚ` -/

private def trimStep (acc : List ℚ) (a : ℚ) : List ℚ :=
  if decide (a = 0) && acc.isEmpty then [] else a :: acc

private theorem trimStep_eq_trim_cons (a : ℚ) (p : List ℚ) :
    trimStep (CoeffList.trim p) a = CoeffList.trim (a :: p) := by
  simp only [trimStep, CoeffList.trim_cons, Bool.and_eq_true, decide_eq_true_eq]

private theorem foldl_trimStep_reverse (p : List ℚ) :
    p.reverse.foldl trimStep [] = CoeffList.trim p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    rw [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil, ih,
      trimStep_eq_trim_cons]

private theorem foldl_trimStep_sublist (l acc : List ℚ) :
    (l.foldl trimStep acc).Sublist (l.reverse ++ acc) := by
  induction l generalizing acc with
  | nil => simp only [List.foldl_nil, List.reverse_nil, List.nil_append, List.Sublist.refl]
  | cons a ls ih =>
    rw [List.foldl_cons, List.reverse_cons, List.append_assoc, List.singleton_append]
    refine (ih (trimStep acc a)).trans (List.Sublist.append_left ?_ ls.reverse)
    simp only [trimStep]
    split_ifs
    · exact List.nil_sublist _
    · exact List.Sublist.refl _

/-- Trailing-zero trimming `Polynomial.CoeffList.trim` on rational coefficient lists is computable
in polynomial time. -/
@[fun_prop]
theorem trim_computableInPolyTime :
    ComputableInPolyTime (CoeffList.trim (R := ℚ)) encRatPoly encRatPoly := by
  have hstep : ComputableInPolyTime (fun p : List ℚ × ℚ => trimStep p.1 p.2)
      (encPair encRatPoly encRat) encRatPoly := by
    unfold trimStep
    exact (bool_and' (rat_isZero.comp (snd _ _)) ((listIsEmpty' encRat).comp (fst _ _))).ite
      (const []) ((cons encRat).comp ((snd _ _).prod (fst _ _)))
  have hfold := foldl' (encA := encRat) (encB := encRatPoly) (encL := encRatPoly)
    (list := fun p : List ℚ => p.reverse) (init := fun _ => []) (step := trimStep)
    (listReverse encRat) (const []) hstep (B := fun p => (encRatPoly p).length)
    PolyBounded.self fun p i _ => by
      have hsub1 : ((p.reverse.take i).foldl trimStep []).Sublist ((p.reverse.take i).reverse) := by
        simpa only [List.append_nil] using foldl_trimStep_sublist (p.reverse.take i) []
      have hsub2 : ((p.reverse.take i).reverse).Sublist p := by
        simpa only [List.reverse_reverse] using (List.take_sublist i p.reverse).reverse
      exact length_encList_sublist encRat (hsub1.trans hsub2)
  exact hfold.of_enc_eq fun p => congrArg encRatPoly (foldl_trimStep_reverse p).symm

private theorem zipWithAll_getD_eq_map_range (op : ℚ → ℚ → ℚ) (p q : List ℚ) :
    List.zipWithAll (fun a b => op (a.getD 0) (b.getD 0)) p q =
      (List.range (max p.length q.length)).map (fun i => op (p.getD i 0) (q.getD i 0)) := by
  induction p generalizing q with
  | nil =>
    refine List.ext_getElem (by simp) fun i hi1 hi2 => ?_
    have hi : i < q.length := by simpa only [List.nil_zipWithAll, List.length_map] using hi1
    simp [List.getElem?_eq_getElem hi]
  | cons a p ih =>
    cases q with
    | nil =>
      refine List.ext_getElem (by simp) fun i hi1 hi2 => ?_
      have hi : i < (a :: p).length := by
        simpa only [List.zipWithAll_nil, List.length_map] using hi1
      simp [-List.map_cons, List.getElem?_eq_getElem hi]
    | cons b q =>
      simp only [List.zipWithAll_cons_cons, Option.getD_some, ih q, List.length_cons,
        Nat.succ_max_succ, List.range_succ_eq_map, List.map_cons, List.getD_cons_zero,
        List.map_map, Function.comp_def, List.getD_cons_succ]

private theorem coeffList_binOp_polyTime {op : ℚ → ℚ → ℚ}
    (hop : ComputableInPolyTime (fun xy : ℚ × ℚ => op xy.1 xy.2)
      (encPair encRat encRat) encRat) :
    ComputableInPolyTime
      (fun pq : List ℚ × List ℚ =>
        CoeffList.trim (List.zipWithAll (fun x y => op (x.getD 0) (y.getD 0)) pq.1 pq.2))
      (encPair encRatPoly encRatPoly) encRatPoly := by
  simp only [zipWithAll_getD_eq_map_range]
  refine trim_computableInPolyTime.comp (mapWithInput
    (range.comp (unary_max.comp (((length_list encRat).comp (fst _ _)).prod
      ((length_list encRat).comp (snd _ _))))) ?_)
  exact hop.comp
    ((listGetDWithInput ((fst _ _).comp (fst _ _)) (snd _ _) 0).prod
     (listGetDWithInput ((snd _ _).comp (fst _ _)) (snd _ _) 0))

private theorem coeffList_add_polyTime :
    ComputableInPolyTime (fun pq : List ℚ × List ℚ => CoeffList.add pq.1 pq.2)
      (encPair encRatPoly encRatPoly) encRatPoly :=
  coeffList_binOp_polyTime rat_add

private theorem coeffList_sub_polyTime :
    ComputableInPolyTime (fun pq : List ℚ × List ℚ => CoeffList.sub pq.1 pq.2)
      (encPair encRatPoly encRatPoly) encRatPoly :=
  coeffList_binOp_polyTime rat_sub

private theorem coeffList_neg_polyTime :
    ComputableInPolyTime (CoeffList.neg (R := ℚ)) encRatPoly encRatPoly := by
  unfold CoeffList.neg
  exact trim_computableInPolyTime.comp
    (mapWith (rat_neg.comp (snd encBool encRat)) (const false) id')

private theorem coeffList_smul_polyTime :
    ComputableInPolyTime (fun cp : ℚ × List ℚ => CoeffList.smul cp.1 cp.2)
      (encPair encRat encRatPoly) encRatPoly := by
  unfold CoeffList.smul
  exact trim_computableInPolyTime.comp (mapWith rat_mul (fst _ _) (snd _ _))

private theorem coeffList_shift_polyTime :
    ComputableInPolyTime (fun kp : ℕ × List ℚ => CoeffList.shift kp.1 kp.2)
      (encPair encUnary encRatPoly) encRatPoly := by
  unfold CoeffList.shift
  exact trim_computableInPolyTime.comp
    ((listAppend encRat).comp ((replicate (fst _ _) (const (0 : ℚ))).prod (snd _ _)))

private theorem coeffList_deriv_polyTime :
    ComputableInPolyTime (CoeffList.deriv (R := ℚ)) encRatPoly encRatPoly := by
  have hmap : ComputableInPolyTime
      (fun p : List ℚ => (List.range (p.length - 1)).map
        fun i => p.getD (i + 1) 0 * (((i + 1 : ℕ) : ℤ) : ℚ))
      encRatPoly encRatPoly := by
    refine mapWithInput (range.comp (unary_sub' (length_list encRat) (const 1))) ?_
    have hi1 : ComputableInPolyTime (fun q : List ℚ × ℕ => q.2 + 1)
        (encPair encRatPoly encUnary) encUnary := unary_add' (snd _ _) (const 1)
    exact rat_mul' (listGetDWithInput (fst _ _) hi1 0)
      (rat_intCast.comp (intBin_natCast.comp (unary_to_binary.comp hi1)))
  refine (trim_computableInPolyTime.comp hmap).of_enc_eq fun p => congrArg encRatPoly ?_
  simp only [CoeffList.deriv, Function.comp_apply]
  congr 2
  funext i
  push_cast
  rfl

private theorem getLastD_eq_reverse_headD {α : Type*} (l : List α) (d : α) :
    l.getLastD d = l.reverse.headD d := by
  rw [List.getLastD_eq_getLast?, List.headD_eq_head?_getD, List.getLast?_eq_head?_reverse]

private theorem ratPoly_getLastD_polyTime (d : ℚ) :
    ComputableInPolyTime (fun l : List ℚ => l.getLastD d) encRatPoly encRat :=
  ((headD d).comp (listReverse encRat)).of_enc_eq fun l =>
    congrArg encRat (getLastD_eq_reverse_headD l d)

/-! ### Polynomial-time Euclidean division `CoeffList.divMod` and `negMod` over `ℚ` -/

private def CommonDenomBound (D M : ℕ) (l : List ℚ) : Prop :=
  ∀ x ∈ l, ∃ z : ℤ, x = (z : ℚ) / (D : ℚ) ∧ z.natAbs ≤ M

private theorem CommonDenomBound.nil (D M : ℕ) : CommonDenomBound D M [] :=
  fun _ hx => (List.not_mem_nil hx).elim

private theorem CommonDenomBound.trim {D M : ℕ} {l : List ℚ} (h : CommonDenomBound D M l) :
    CommonDenomBound D M (CoeffList.trim l) :=
  fun x hx => h x ((CoeffList.trim_sublist l).subset hx)

private theorem CommonDenomBound.mono_M {D M M' : ℕ} (hM : M ≤ M') {l : List ℚ}
    (h : CommonDenomBound D M l) : CommonDenomBound D M' l :=
  fun x hx => let ⟨z, hxz, hz⟩ := h x hx; ⟨z, hxz, hz.trans hM⟩

private theorem CommonDenomBound.scale {D M : ℕ} (k : ℕ) (hk : 1 ≤ k) {l : List ℚ}
    (h : CommonDenomBound D M l) : CommonDenomBound (D * k) (M * k) l := fun x hx => by
  obtain ⟨z, rfl, hz⟩ := h x hx
  have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  refine ⟨z * (k : ℤ), ?_, ?_⟩
  · push_cast
    exact (mul_div_mul_right (z : ℚ) (D : ℚ) hk0).symm
  · rw [Int.natAbs_mul, Int.natAbs_natCast]
    exact Nat.mul_le_mul_right k hz

private theorem CommonDenomBound.shift {D M : ℕ} (d : ℕ) {l : List ℚ}
    (h : CommonDenomBound D M l) : CommonDenomBound D M (CoeffList.shift d l) := fun x hx => by
  have hmem := (CoeffList.trim_sublist _).subset hx
  rw [List.mem_append] at hmem
  rcases hmem with hrep | hl
  · rw [List.eq_of_mem_replicate hrep]
    exact ⟨0, by simp, Nat.zero_le _⟩
  · exact h x hl

private theorem CommonDenomBound.getD {D M : ℕ} {l : List ℚ}
    (h : CommonDenomBound D M l) (i : ℕ) :
    ∃ z : ℤ, l.getD i 0 = (z : ℚ) / (D : ℚ) ∧ z.natAbs ≤ M := by
  by_cases hi : i < l.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact h l[i] (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact ⟨0, by simp, Nat.zero_le _⟩

private theorem CommonDenomBound.getLastD {D M : ℕ} {l : List ℚ}
    (h : CommonDenomBound D M l) :
    ∃ z : ℤ, l.getLastD 0 = (z : ℚ) / (D : ℚ) ∧ z.natAbs ≤ M := by
  rcases List.eq_nil_or_concat l with rfl | ⟨init, a, rfl⟩
  · exact ⟨0, by simp, Nat.zero_le _⟩
  · rw [List.concat_eq_append, List.getLastD_concat]
    exact h a (by simp)

private theorem CommonDenomBound.add {D M₁ M₂ : ℕ} {p q : List ℚ}
    (hp : CommonDenomBound D M₁ p) (hq : CommonDenomBound D M₂ q) :
    CommonDenomBound D (M₁ + M₂) (CoeffList.add p q) := fun x hx => by
  have hmem := (CoeffList.trim_sublist _).subset hx
  rw [zipWithAll_getD_eq_map_range, List.mem_map] at hmem
  obtain ⟨i, _, rfl⟩ := hmem
  obtain ⟨z₁, hz₁, h1⟩ := hp.getD i
  obtain ⟨z₂, hz₂, h2⟩ := hq.getD i
  refine ⟨z₁ + z₂, ?_, (Int.natAbs_add_le z₁ z₂).trans (Nat.add_le_add h1 h2)⟩
  rw [hz₁, hz₂, Int.cast_add, add_div]

private theorem CommonDenomBound.sub {D M₁ M₂ : ℕ} {p q : List ℚ}
    (hp : CommonDenomBound D M₁ p) (hq : CommonDenomBound D M₂ q) :
    CommonDenomBound D (M₁ + M₂) (CoeffList.sub p q) := fun x hx => by
  have hmem := (CoeffList.trim_sublist _).subset hx
  rw [zipWithAll_getD_eq_map_range, List.mem_map] at hmem
  obtain ⟨i, _, rfl⟩ := hmem
  obtain ⟨z₁, hz₁, h1⟩ := hp.getD i
  obtain ⟨z₂, hz₂, h2⟩ := hq.getD i
  refine ⟨z₁ - z₂, ?_, (Int.natAbs_sub_le z₁ z₂).trans (Nat.add_le_add h1 h2)⟩
  rw [hz₁, hz₂, Int.cast_sub, sub_div]

private theorem CommonDenomBound.of_bitBound {B : ℕ} {l : List ℚ} (hB : HasCoeffBitBound B l) :
    CommonDenomBound (lcmDens l) (2 ^ ((l.length + 1) * B)) l := fun q hq => by
  let D := lcmDens l
  have hdvd : q.den ∣ D := dvd_lcmDens hq
  have hD_le : D ≤ 2 ^ (l.length * B) := lcmDens_le_of_bitBound hB
  refine ⟨q.num * ((D / q.den : ℕ) : ℤ), ?_, ?_⟩
  · have hqden0 : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
    have hD0 : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := one_le_lcmDens l; omega)
    have hmul : ((D / q.den : ℕ) : ℚ) * (q.den : ℚ) = (D : ℚ) := by
      exact_mod_cast Nat.div_mul_cancel hdvd
    rw [Int.cast_mul, Int.cast_natCast, eq_div_iff hD0]
    calc q * (D : ℚ)
        = (q.num : ℚ) / (q.den : ℚ) * (((D / q.den : ℕ) : ℚ) * (q.den : ℚ)) := by
            rw [Rat.num_div_den, hmul]
      _ = (q.num : ℚ) * ((D / q.den : ℕ) : ℚ) := by field_simp
  · rw [Int.natAbs_mul, Int.natAbs_natCast]
    calc q.num.natAbs * (D / q.den)
        ≤ 2 ^ B * 2 ^ (l.length * B) :=
          Nat.mul_le_mul (hB q hq).1 ((Nat.div_le_self _ _).trans hD_le)
      _ = 2 ^ ((l.length + 1) * B) := by rw [Nat.add_one_mul, add_comm, pow_add]

private theorem CommonDenomBound.hasCoeffBitBound {D M K : ℕ} {l : List ℚ}
    (hD1 : 1 ≤ D) (hDK : D ≤ 2 ^ K) (hMK : M ≤ 2 ^ K) (h : CommonDenomBound D M l) :
    HasCoeffBitBound K l := fun x hx => by
  obtain ⟨z, rfl, hz⟩ := h x hx
  exact num_den_div_le hD1 (hz.trans hMK) hDK

private theorem div_mul_int_eq_div_natAbs (D : ℕ) (num w : ℤ) (hw : w ≠ 0) :
    ∃ num' : ℤ, (num : ℚ) / ((D : ℚ) * (w : ℚ)) = (num' : ℚ) / ((D * w.natAbs : ℕ) : ℚ) ∧
      num'.natAbs = num.natAbs := by
  rcases lt_or_gt_of_ne hw with hneg | hpos
  · have hw_z : w = -(w.natAbs : ℤ) := by omega
    refine ⟨-num, ?_, Int.natAbs_neg num⟩
    rw [congrArg Int.cast hw_z, Int.cast_neg, Int.cast_natCast, Int.cast_neg, Nat.cast_mul]
    ring
  · have hw_z : w = (w.natAbs : ℤ) := by omega
    exact ⟨num, by rw [congrArg Int.cast hw_z, Int.cast_natCast, Nat.cast_mul], rfl⟩

private theorem divModStep_commonDenomBound {bt : List ℚ} {Db Bbt W : ℕ} {wlc : ℤ}
    (hDb1 : 1 ≤ Db) (hDb_le : Db ≤ Bbt)
    (hbt_bound : CommonDenomBound Db Bbt bt)
    (hlc_eq : bt.getLastD 0 = (wlc : ℚ) / (Db : ℚ)) (hw0 : wlc ≠ 0)
    (hwlc_abs : wlc.natAbs = W) (hwlc_le : W ≤ Bbt)
    {D M : ℕ} (hD1 : 1 ≤ D) {st : List ℚ × List ℚ}
    (hq : CommonDenomBound D M st.1) (hr : CommonDenomBound D M st.2) :
    CommonDenomBound (D * W) (2 * Bbt * M) (CoeffList.divModStep bt st).1 ∧
      CommonDenomBound (D * W) (2 * Bbt * M) (CoeffList.divModStep bt st).2 := by
  have hW1 : 1 ≤ W := hwlc_abs ▸ Int.natAbs_pos.mpr hw0
  have hWB : M * W ≤ M * Bbt := Nat.mul_le_mul_left M hwlc_le
  have hsum : M * Bbt + M * Bbt = 2 * Bbt * M := by ring
  dsimp only [CoeffList.divModStep]
  split_ifs
  · exact ⟨(hq.trim.scale W hW1).mono_M (by omega), (hr.trim.scale W hW1).mono_M (by omega)⟩
  · set r' := CoeffList.trim st.2
    set d := r'.length - bt.length
    set c := r'.getLastD 0 / bt.getLastD 0
    have hr' : CommonDenomBound D M r' := hr.trim
    obtain ⟨zr, hzr_eq, hzr_le⟩ := hr'.getLastD
    have hD0_q : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hDb0_q : (Db : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hw0_q : (wlc : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hw0
    -- `c * (wy / Db)` has denominator `D * W` and numerator at most `M * Bbt`.
    have hcy (wy : ℤ) (hwy : wy.natAbs ≤ Bbt) :
        ∃ z : ℤ, c * (wy / Db) = z / ((D * W : ℕ) : ℚ) ∧ z.natAbs ≤ M * Bbt := by
      obtain ⟨z, hz_eq, hz_abs⟩ := div_mul_int_eq_div_natAbs D (zr * wy) wlc hw0
      refine ⟨z, ?_, by rw [hz_abs, Int.natAbs_mul]; exact Nat.mul_le_mul hzr_le hwy⟩
      rw [← hwlc_abs, ← hz_eq]
      dsimp only [c]
      rw [hzr_eq, hlc_eq, Int.cast_mul]
      field_simp
    have hc_bound : CommonDenomBound (D * W) (M * Bbt) [c] := fun x hx => by
      have h := hcy Db (by rw [Int.natAbs_natCast]; exact hDb_le)
      rwa [Int.cast_natCast, div_self hDb0_q, mul_one, ← List.mem_singleton.mp hx] at h
    have hsmul_bound :
        CommonDenomBound (D * W) (M * Bbt) (CoeffList.smul c (CoeffList.shift d bt)) :=
        fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ((CoeffList.trim_sublist _).subset hx)
      obtain ⟨wy, rfl, hwy_le⟩ := hbt_bound.shift d y hy
      exact hcy wy hwy_le
    have hq_scaled : CommonDenomBound (D * W) (M * Bbt) st.1 := (hq.scale W hW1).mono_M hWB
    have hr_scaled : CommonDenomBound (D * W) (M * Bbt) r' := (hr'.scale W hW1).mono_M hWB
    exact ⟨(hq_scaled.add (hc_bound.shift d)).mono_M hsum.le,
      (hr_scaled.sub hsmul_bound).mono_M hsum.le⟩

private theorem divMod_iterate_bitBound (a b : List ℚ) {B : ℕ}
    (haB : HasCoeffBitBound B a) (hbB : HasCoeffBitBound B b)
    (k : ℕ) (hk : k ≤ a.length) :
    let E := (a.length + b.length + 2) * (B + 1)
    let st := (CoeffList.divModStep (CoeffList.trim b))^[k] ([], CoeffList.trim a)
    HasCoeffBitBound ((a.length + 1) * (E + 1)) st.1 ∧
      HasCoeffBitBound ((a.length + 1) * (E + 1)) st.2 := by
  intro E
  set bt := CoeffList.trim b
  set at_ := CoeffList.trim a
  have hat_B : HasCoeffBitBound B at_ := haB.trim
  have hbt_B : HasCoeffBitBound B bt := hbB.trim
  have hat_len : at_.length ≤ a.length := CoeffList.length_trim_le a
  have hbt_len : bt.length ≤ b.length := CoeffList.length_trim_le b
  by_cases hbt_nil : bt = []
  · have hat_trim : CoeffList.trim at_ = at_ := CoeffList.trim_trim a
    have hfix : ∀ j, (CoeffList.divModStep bt)^[j] ([], at_) = ([], at_) := fun j => by
      induction j with
      | zero => rfl
      | succ j ih =>
        rw [Function.iterate_succ_apply', ih]
        simp [CoeffList.divModStep, hbt_nil, hat_trim]
    dsimp only
    rw [hfix k]
    exact ⟨fun _ hx => (List.not_mem_nil hx).elim, hasCoeffBitBound_mono hat_B
      ((show B ≤ E + 1 by dsimp only [E]; nlinarith).trans (Nat.le_mul_of_pos_left _ (by omega)))⟩
  · let Da := lcmDens at_
    let Db := lcmDens bt
    let Bbt := 2 ^ ((bt.length + 1) * B)
    have hDa1 : 1 ≤ Da := one_le_lcmDens at_
    have hDb1 : 1 ≤ Db := one_le_lcmDens bt
    have hDb_le : Db ≤ Bbt := (lcmDens_le_of_bitBound hbt_B).trans
      (Nat.pow_le_pow_right zero_lt_two (Nat.mul_le_mul_right B (Nat.le_succ bt.length)))
    have hbt_cd : CommonDenomBound Db Bbt bt := CommonDenomBound.of_bitBound hbt_B
    obtain ⟨wlc, hlc_eq, hwlc_le⟩ := hbt_cd.getLastD
    let W := wlc.natAbs
    have hlc_ne : bt.getLastD 0 ≠ 0 := by
      rw [← (CoeffList.isTrimmed_trim b).leadingCoeff_ofCoeffList, leadingCoeff_ne_zero]
      exact (CoeffList.isTrimmed_trim b).ofCoeffList_ne_zero hbt_nil
    have hw0 : wlc ≠ 0 := fun h0 => hlc_ne (by rw [hlc_eq, h0, Int.cast_zero, zero_div])
    have hW1 : 1 ≤ W := Int.natAbs_pos.mpr hw0
    let M0 := 2 ^ ((at_.length + 1) * B)
    have hiter : ∀ j : ℕ,
        let st := (CoeffList.divModStep bt)^[j] ([], at_)
        CommonDenomBound (Da * W ^ j) ((2 * Bbt) ^ j * M0) st.1 ∧
          CommonDenomBound (Da * W ^ j) ((2 * Bbt) ^ j * M0) st.2 := fun j => by
      induction j with
      | zero =>
        simp only [Function.iterate_zero, id_eq, pow_zero, mul_one, one_mul]
        exact ⟨CommonDenomBound.nil _ _, CommonDenomBound.of_bitBound hat_B⟩
      | succ j ih =>
        rw [Function.iterate_succ_apply']
        have hDj1 : 1 ≤ Da * W ^ j := Nat.mul_pos hDa1 (Nat.pow_pos hW1)
        obtain ⟨hq', hr'⟩ := divModStep_commonDenomBound
          hDb1 hDb_le hbt_cd hlc_eq hw0 rfl hwlc_le hDj1 ih.1 ih.2
        rw [mul_assoc Da, ← pow_succ, ← mul_assoc (2 * Bbt), ← pow_succ'] at hq' hr'
        exact ⟨hq', hr'⟩
    obtain ⟨hqk, hrk⟩ := hiter k
    -- Every factor is at most `P = 2 ^ (E + 1)`, and `P ^ (k + 1)` fits the claimed exponent.
    have hexp : ∀ n ≤ a.length + b.length + 1, 2 ^ (n * B) ≤ 2 ^ E := fun n hn =>
      Nat.pow_le_pow_right zero_lt_two (by dsimp only [E]; nlinarith [Nat.mul_le_mul_right B hn])
    have hP : 2 ^ (E + 1) = 2 * 2 ^ E := pow_succ' 2 E
    have hDa : Da ≤ 2 ^ E := (lcmDens_le_of_bitBound hat_B).trans (hexp at_.length (by omega))
    have hM0 : M0 ≤ 2 ^ E := hexp _ (by omega)
    have hBbt : Bbt ≤ 2 ^ E := hexp _ (by omega)
    have hfin (X Y : ℕ) (hX : X ≤ 2 ^ (E + 1)) (hY : Y ≤ 2 ^ (E + 1)) :
        X * Y ^ k ≤ 2 ^ ((a.length + 1) * (E + 1)) :=
      calc X * Y ^ k ≤ 2 ^ (E + 1) * (2 ^ (E + 1)) ^ k :=
            Nat.mul_le_mul hX (Nat.pow_le_pow_left hY k)
        _ = 2 ^ ((k + 1) * (E + 1)) := by rw [← pow_succ', ← pow_mul, mul_comm]
        _ ≤ _ := Nat.pow_le_pow_right zero_lt_two (Nat.mul_le_mul_right _ (by omega))
    have hDk_le := hfin Da W (by omega) (hwlc_le.trans (by omega))
    have hMk_le : (2 * Bbt) ^ k * M0 ≤ 2 ^ ((a.length + 1) * (E + 1)) :=
      (Nat.mul_comm _ _).trans_le (hfin M0 (2 * Bbt) (by omega) (by omega))
    have hDk1 : 1 ≤ Da * W ^ k := Nat.mul_pos hDa1 (Nat.pow_pos hW1)
    exact ⟨hqk.hasCoeffBitBound hDk1 hDk_le hMk_le, hrk.hasCoeffBitBound hDk1 hDk_le hMk_le⟩

private theorem divModStep_polyTime :
    ComputableInPolyTime
      (fun p : List ℚ × (List ℚ × List ℚ) => CoeffList.divModStep p.1 p.2)
      (encPair encRatPoly (encPair encRatPoly encRatPoly))
      (encPair encRatPoly encRatPoly) := by
  unfold CoeffList.divModStep
  have hb := fst encRatPoly (encPair encRatPoly encRatPoly)
  have hq := (snd encRatPoly (encPair encRatPoly encRatPoly)).fst'
  have hr := trim_computableInPolyTime.comp ((snd encRatPoly (encPair encRatPoly encRatPoly)).snd')
  have hcond : ComputableInPolyTime
      (fun p : List ℚ × (List ℚ × List ℚ) =>
        decide ((CoeffList.trim p.2.2).length < p.1.length) || p.1.isEmpty)
      (encPair encRatPoly (encPair encRatPoly encRatPoly)) encBool :=
    bool_or' (unary_lt' ((length_list encRat).comp hr) ((length_list encRat).comp hb))
      ((listIsEmpty' encRat).comp hb)
  have hthen := (trim_computableInPolyTime.comp hq).prod hr
  have hd := unary_sub' ((length_list encRat).comp hr) ((length_list encRat).comp hb)
  have hc := rat_div' ((ratPoly_getLastD_polyTime 0).comp hr)
    ((ratPoly_getLastD_polyTime 0).comp hb)
  have hshift_c := coeffList_shift_polyTime.comp (hd.prod ((cons encRat).comp (hc.prod (const []))))
  have hshift_b := coeffList_shift_polyTime.comp (hd.prod hb)
  have hsmul := coeffList_smul_polyTime.comp (hc.prod hshift_b)
  have helse := (coeffList_add_polyTime.comp (hq.prod hshift_c)).prod
    (coeffList_sub_polyTime.comp (hr.prod hsmul))
  exact hcond.ite hthen helse

private theorem divMod_polyTime :
    ComputableInPolyTime (fun ab : List ℚ × List ℚ => CoeffList.divMod ab.1 ab.2)
      (encPair encRatPoly encRatPoly) (encPair encRatPoly encRatPoly) := by
  unfold CoeffList.divMod
  refine iterateWith
    (par := fun ab : List ℚ × List ℚ => CoeffList.trim ab.2)
    (count := fun ab => ab.1.length)
    (init := fun ab => ([], CoeffList.trim ab.1))
    (step := CoeffList.divModStep)
    (trim_computableInPolyTime.comp (snd _ _))
    ((length_list encRat).comp (fst _ _))
    ((const []).prod (trim_computableInPolyTime.comp (fst _ _)))
    divModStep_polyTime
    (bound := fun ab => 94 * ((encPair encRatPoly encRatPoly ab).length + 1) ^ 4)
    (PolyBounded.of_forall_le 94 4 fun _ => le_rfl)
    fun ab i hi => ?_
  set L := (encPair encRatPoly encRatPoly ab).length
  have hLa : (encRatPoly ab.1).length ≤ L := length_le_encPair_left _ _ ab
  have hLb : (encRatPoly ab.2).length ≤ L := length_le_encPair_right _ _ ab
  have hal : ab.1.length ≤ L := (SizedListEncoding.length_le (encA := encRat) ab.1).trans hLa
  have hbl : ab.2.length ≤ L := (SizedListEncoding.length_le (encA := encRat) ab.2).trans hLb
  obtain ⟨h1_len, h2_len, _, _⟩ := CoeffList.divMod_iterate_bounds ab.1 (CoeffList.trim ab.2) i
  obtain ⟨h1_bit, h2_bit⟩ := divMod_iterate_bitBound ab.1 ab.2
    (hasCoeffBitBound_mono (hasCoeffBitBound_length_encRatPoly ab.1) hLa)
    (hasCoeffBitBound_mono (hasCoeffBitBound_length_encRatPoly ab.2) hLb) i hi
  have hK_le : (ab.1.length + 1) * ((ab.1.length + ab.2.length + 2) * (L + 1) + 1) ≤
      3 * (L + 1) ^ 3 :=
    (Nat.mul_le_mul (by omega : ab.1.length + 1 ≤ L + 1)
      (by nlinarith : (ab.1.length + ab.2.length + 2) * (L + 1) + 1 ≤ 3 * (L + 1) ^ 2)).trans_eq
      (by ring)
  have henc {l : List ℚ} (hl : l.length ≤ ab.1.length)
      (hB : HasCoeffBitBound ((ab.1.length + 1) *
        ((ab.1.length + ab.2.length + 2) * (L + 1) + 1)) l) :
      (encRatPoly l).length ≤ 31 * (L + 1) ^ 4 :=
    (length_encRatPoly_le_of_bitBound (hl.trans (by omega : ab.1.length ≤ L + 1))
      (hasCoeffBitBound_mono hB hK_le)).trans
      (by nlinarith [Nat.one_le_pow 3 (L + 1) (by omega)])
  have henc1 := henc h1_len h1_bit
  have henc2 := henc h2_len h2_bit
  have := Nat.one_le_pow 4 (L + 1) (by omega)
  rw [length_encPair]
  change 2 * _ + 1 + _ ≤ 94 * (L + 1) ^ 4
  omega

private theorem negMod_polyTime :
    ComputableInPolyTime (fun ab : List ℚ × List ℚ => CoeffList.negMod ab.1 ab.2)
      (encPair encRatPoly encRatPoly) encRatPoly :=
  ((divMod_polyTime.comp
    ((coeffList_neg_polyTime.comp (fst _ _)).prod (snd _ _))).snd').of_enc_eq fun ab =>
    congrArg encRatPoly (by dsimp only [CoeffList.negMod, CoeffList.mod, Function.comp_apply])

/-! ### Polynomial-time rational Sturm sequence `sturmSeqList` -/

private structure SturmIterState where
  revPrefix : List (List ℚ)
  cur : List ℚ
  next : List ℚ

private enc_structure encSturmIterState : SturmIterState where
  revPrefix : encSturmSeq,
  cur : encRatPoly,
  next : encRatPoly

private def sturmIterStep (st : SturmIterState) : SturmIterState :=
  if st.next.isEmpty then st
  else
    { revPrefix := st.cur :: st.revPrefix
      cur := st.next
      next := CoeffList.negMod st.cur st.next }

private theorem sturmIterStep_of_next_nil (rev : List (List ℚ)) (p : List ℚ) (n : ℕ) :
    sturmIterStep^[n] { revPrefix := rev, cur := p, next := [] } =
      { revPrefix := rev, cur := p, next := [] } :=
  Function.iterate_fixed (by simp [sturmIterStep]) n

private theorem sturmIterStep_finish_eq :
    ∀ (n : ℕ) (rev : List (List ℚ)) (p q : List ℚ),
      let st := sturmIterStep^[n] { revPrefix := rev, cur := p, next := q }
      (st.cur :: st.revPrefix).reverse = rev.reverse ++ sturmSeqAux n p q
  | 0, rev, p, _ => by simp [sturmSeqAux]
  | n + 1, rev, p, q => by
    by_cases hq : q.isEmpty = true
    · obtain rfl : q = [] := List.isEmpty_iff.mp hq
      simp only [sturmIterStep_of_next_nil, List.reverse_cons, sturmSeqAux, List.isEmpty_nil,
        ↓reduceIte]
    · have hstep : sturmIterStep { revPrefix := rev, cur := p, next := q } =
          { revPrefix := p :: rev, cur := q, next := CoeffList.negMod p q } := by
        simp [sturmIterStep, hq]
      dsimp only
      rw [Function.iterate_succ_apply, hstep, sturmIterStep_finish_eq n (p :: rev) q,
        List.reverse_cons, List.append_assoc, List.singleton_append]
      simp only [sturmSeqAux, hq, Bool.false_eq_true, ↓reduceIte]

private theorem head_mem_sturmSeqAux (n : ℕ) (p q : List ℚ) :
    p ∈ sturmSeqAux n p q := by
  cases n with
  | zero => simp [sturmSeqAux]
  | succ n =>
    simp only [sturmSeqAux]
    split_ifs <;> simp

private theorem snd_mem_sturmSeqAux (n : ℕ) (p q : List ℚ) (hq : q ≠ []) :
    q ∈ sturmSeqAux (n + 1) p q := by
  have hqe : q.isEmpty = false := List.isEmpty_eq_false_iff.mpr hq
  simp only [sturmSeqAux, hqe, Bool.false_eq_true, ↓reduceIte, List.mem_cons]
  exact Or.inr (head_mem_sturmSeqAux n q _)

private theorem sturmIterStep_invariant {p q : List ℚ}
    (hp_trim : CoeffList.IsTrimmed p) (hp_ne : p ≠ []) (hq_trim : CoeffList.IsTrimmed q) :
    ∀ i ≤ q.length,
      let st := sturmIterStep^[i] { revPrefix := [], cur := p, next := q }
      st.revPrefix.length ≤ i ∧
        st.revPrefix.reverse ++ sturmSeqAux (q.length - i) st.cur st.next =
          sturmSeqAux q.length p q ∧
        CoeffList.IsTrimmed st.cur ∧ st.cur ≠ [] ∧
        CoeffList.IsTrimmed st.next ∧ st.next.length ≤ q.length - i := by
  intro i hi
  induction i with
  | zero =>
    simp only [Function.iterate_zero, id_eq, List.length_nil, le_refl, List.reverse_nil,
      Nat.sub_zero, List.nil_append, hp_trim, ne_eq, hp_ne, not_false_eq_true, hq_trim, and_self]
  | succ i ih =>
    obtain ⟨hlen, heq, hcur_t, hcur_ne, hnext_t, hnext_len⟩ := ih (by omega)
    set sti := sturmIterStep^[i] { revPrefix := [], cur := p, next := q }
    rw [Function.iterate_succ_apply']
    have hrem_succ : q.length - i = (q.length - (i + 1)) + 1 := by omega
    by_cases hne_e : sti.next.isEmpty = true
    · have hnil : sti.next = [] := List.isEmpty_iff.mp hne_e
      have hstep : sturmIterStep sti = sti := by simp [sturmIterStep, hne_e]
      have haux_nil (m : ℕ) : sturmSeqAux m sti.cur [] = [sti.cur] := by
        cases m <;> simp [sturmSeqAux]
      rw [hstep]
      exact ⟨hlen.trans (Nat.le_succ i), by simpa only [hnil, haux_nil] using heq,
        hcur_t, hcur_ne, hnext_t, by simp [hnil]⟩
    · have hnext_ne : sti.next ≠ [] := fun h => hne_e (List.isEmpty_iff.mpr h)
      have hstep : sturmIterStep sti =
          { revPrefix := sti.cur :: sti.revPrefix, cur := sti.next,
            next := CoeffList.negMod sti.cur sti.next } := by simp [sturmIterStep, hne_e]
      have hneg_lt : (CoeffList.negMod sti.cur sti.next).length < sti.next.length :=
        (CoeffList.length_negMod_lt (hnext_t.ofCoeffList_ne_zero hnext_ne)).trans_le
          (CoeffList.length_trim_le _)
      rw [hstep]
      refine ⟨by simp only [List.length_cons]; omega, ?_, hnext_t, hnext_ne,
        CoeffList.isTrimmed_negMod _ _, by dsimp only; omega⟩
      rw [hrem_succ] at heq
      simpa only [sturmSeqAux, hne_e, Bool.false_eq_true, ↓reduceIte, List.reverse_cons,
        List.append_assoc, List.singleton_append] using heq

/-- Computing the rational Sturm sequence `Cslib.RealRoot.sturmSeqList` is polynomial-time from
`encRatPoly` to `encSturmSeq`. -/
@[fun_prop]
theorem sturmSeqList_computableInPolyTime :
    ComputableInPolyTime sturmSeqList encRatPoly encSturmSeq := by
  have hstep : ComputableInPolyTime sturmIterStep encSturmIterState encSturmIterState := by
    unfold sturmIterStep
    have hcond : ComputableInPolyTime (fun st : SturmIterState => st.next.isEmpty)
        encSturmIterState encBool := by fun_prop
    have helse : ComputableInPolyTime
        (fun st : SturmIterState =>
          ({ revPrefix := st.cur :: st.revPrefix
             cur := st.next
             next := CoeffList.negMod st.cur st.next } : SturmIterState))
        encSturmIterState encSturmIterState := by
      have hnm := negMod_polyTime.comp
        ((encSturmIterState_cur_polyTime id').prod (encSturmIterState_next_polyTime id'))
      exact encSturmIterState_mk_polyTime
        ((cons encRatPoly).comp ((encSturmIterState_cur_polyTime id').prod
          (encSturmIterState_revPrefix_polyTime id')))
        (encSturmIterState_next_polyTime id') hnm
    exact hcond.ite id' helse
  have hp := trim_computableInPolyTime
  have hdp := coeffList_deriv_polyTime.comp hp
  have hloop : ComputableInPolyTime
      (fun cs : List ℚ =>
        if (CoeffList.trim cs).isEmpty then
          ({ revPrefix := [], cur := [], next := [] } : SturmIterState)
        else
          sturmIterStep^[(CoeffList.deriv (CoeffList.trim cs)).length]
            { revPrefix := [], cur := CoeffList.trim cs,
              next := CoeffList.deriv (CoeffList.trim cs) })
      encRatPoly encSturmIterState := by
    have hcount : ComputableInPolyTime
        (fun cs : List ℚ =>
          if (CoeffList.trim cs).isEmpty then 0
          else (CoeffList.deriv (CoeffList.trim cs)).length)
        encRatPoly encUnary :=
      ((listIsEmpty' encRat).comp hp).ite (const 0) ((length_list encRat).comp hdp)
    have hinit : ComputableInPolyTime
        (fun cs : List ℚ =>
          if (CoeffList.trim cs).isEmpty then
            ({ revPrefix := [], cur := [], next := [] } : SturmIterState)
          else
            { revPrefix := [], cur := CoeffList.trim cs,
              next := CoeffList.deriv (CoeffList.trim cs) })
        encRatPoly encSturmIterState :=
      ((listIsEmpty' encRat).comp hp).ite
        (encSturmIterState_mk_polyTime (const []) (const []) (const []))
        (encSturmIterState_mk_polyTime (const []) hp hdp)
    have hiter := iterate hcount hinit hstep
      (bound := fun cs => 431 * ((encRatPoly cs).length + 1) ^ 6)
      (PolyBounded.of_forall_le 431 6 fun _ => le_rfl)
      fun cs i hi => by
        set L := (encRatPoly cs).length
        have hN5 := Nat.one_le_pow 5 (L + 1) (by omega)
        by_cases he : (CoeffList.trim cs).isEmpty = true
        · simp only [he, ↓reduceIte, Nat.le_zero] at hi ⊢
          subst hi
          simp only [Function.iterate_zero, id_eq, encSturmIterState_apply,
            encSturmIterStateFields, length_encPair, encList_nil, List.length_nil]
          change 2 * 0 + 1 + (2 * 0 + 1 + 0) ≤ 431 * (L + 1) ^ 6
          have := Nat.one_le_pow 6 (L + 1) (by omega)
          omega
        · simp only [he, Bool.false_eq_true, ↓reduceIte] at hi ⊢
          set p := CoeffList.trim cs
          have hp_ne : p ≠ [] := fun h => he (List.isEmpty_iff.mpr h)
          obtain ⟨hrev_len, hdecomp, _, _, _, hnext_len⟩ :=
            sturmIterStep_invariant (CoeffList.isTrimmed_trim cs) hp_ne
              (CoeffList.isTrimmed_deriv p) i hi
          set dp := CoeffList.deriv p
          have hst_seq : sturmSeqList cs = sturmSeqAux dp.length p dp := by
            simp [sturmSeqList, p, dp, he]
          set sti := sturmIterStep^[i] { revPrefix := [], cur := p, next := dp }
          have hcs_len : cs.length ≤ L := SizedListEncoding.length_le (encA := encRat) cs
          have hdp_len : dp.length ≤ cs.length :=
            (CoeffList.length_deriv_le p).trans
              ((Nat.sub_le _ _).trans (CoeffList.length_trim_le cs))
          have hK_ge : sturmBitBound cs.length L ≤ 8 * (L + 1) ^ 4 := by
            dsimp only [sturmBitBound]
            calc 8 * (cs.length + 1) ^ 3 * (L + 1) ≤ 8 * (L + 1) ^ 3 * (L + 1) := by gcongr
              _ = 8 * (L + 1) ^ 4 := by ring
          -- Every polynomial of the iteration state lies in the Sturm sequence.
          have henc : ∀ f ∈ sti.revPrefix.reverse ++ sturmSeqAux (dp.length - i) sti.cur sti.next,
              (encRatPoly f).length ≤ 61 * (L + 1) ^ 5 := fun f hf => by
            have hmem : f ∈ sturmSeqList cs := by rwa [hst_seq, ← hdecomp]
            have hfl : f.length ≤ L + 1 := (sturmSeqList_entry_length_le cs hmem).trans
              ((CoeffList.length_trim_le cs).trans (by omega))
            refine (length_encRatPoly_le_of_bitBound hfl (hasCoeffBitBound_mono
              (hasCoeffBitBound_of_mem_sturmSeqList (hasCoeffBitBound_length_encRatPoly cs) hmem)
              hK_ge)).trans ?_
            nlinarith [Nat.mul_le_mul_left (L + 1) (Nat.one_le_pow 4 (L + 1) (by omega))]
          have henc_rev : (encSturmSeq sti.revPrefix).length ≤ 123 * (L + 1) ^ 6 :=
            calc _ ≤ (L + 1) * (2 * (61 * (L + 1) ^ 5) + 1) :=
                  (length_encList_le encRatPoly sti.revPrefix fun f hf =>
                    henc f (List.mem_append_left _ (List.mem_reverse.mpr hf))).trans
                  (Nat.mul_le_mul_right _ (by omega))
              _ ≤ 123 * (L + 1) ^ 6 := by nlinarith [Nat.mul_le_mul_left (L + 1) hN5]
          have henc_cur : (encRatPoly sti.cur).length ≤ 61 * (L + 1) ^ 5 :=
            henc _ (List.mem_append_right _ (head_mem_sturmSeqAux _ _ _))
          have henc_next : (encRatPoly sti.next).length ≤ 61 * (L + 1) ^ 5 := by
            rcases eq_or_ne sti.next [] with h0 | hne
            · rw [h0]; simp only [encRatPoly, encList_nil, List.length_nil]; exact Nat.zero_le _
            · have hlt : i < dp.length := by
                have := List.length_pos_of_ne_nil hne
                omega
              refine henc _ (List.mem_append_right _ ?_)
              rw [show dp.length - i = (dp.length - i - 1) + 1 by omega]
              exact snd_mem_sturmSeqAux _ _ _ hne
          have h56 : (L + 1) ^ 5 ≤ (L + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
          rw [encSturmIterState_apply]
          dsimp only [encSturmIterStateFields]
          rw [length_encPair, length_encPair]
          dsimp only
          change _ ≤ 431 * (L + 1) ^ 6
          omega
    exact hiter.of_enc_eq fun cs => by
      by_cases he : (CoeffList.trim cs).isEmpty = true <;> simp [he]
  have hpost := ((listIsEmpty' encRat).comp hp).ite (const [])
    ((listReverse encRatPoly).comp ((cons encRatPoly).comp
      ((encSturmIterState_cur_polyTime hloop).prod
        (encSturmIterState_revPrefix_polyTime hloop))))
  refine hpost.of_enc_eq fun cs => congrArg encSturmSeq ?_
  dsimp only [sturmSeqList, Function.comp_apply]
  by_cases he : (CoeffList.trim cs).isEmpty = true
  · simp [he]
  · simp only [he, Bool.false_eq_true, ↓reduceIte]
    have := sturmIterStep_finish_eq (CoeffList.deriv (CoeffList.trim cs)).length []
      (CoeffList.trim cs) (CoeffList.deriv (CoeffList.trim cs))
    simpa only [List.reverse_nil, List.nil_append] using this.symm

/-! ### Polynomial-time Horner evaluation and sign variations -/

/-- Horner polynomial evaluation `Polynomial.evalCoeffList` on `encPair encRat encRatPoly` is
computable in polynomial time. -/
theorem evalCoeffList_computableInPolyTime :
    ComputableInPolyTime (fun xt : ℚ × List ℚ => evalCoeffList xt.1 xt.2)
      (encPair encRat encRatPoly) encRat := by
  have hfold_eq (x : ℚ) (t : List ℚ) :
      t.reverse.foldl (fun acc a => a + x * acc) 0 = evalCoeffList x t := by
    rw [evalCoeffList, ← List.foldl_reverse]
  have hstep : ComputableInPolyTime
      (fun p : (ℚ × ℚ) × ℚ => p.2 + p.1.1 * p.1.2)
      (encPair (encPair encRat encRat) encRat) encRat :=
    rat_add' (snd _ _) (rat_mul' (fst _ _).fst' (fst _ _).snd')
  have hfold := foldlWith (encA := encRat) (encB := encRat) (encL := encRatPoly) (encP := encRat)
    (par := Prod.fst) (list := fun xt : ℚ × List ℚ => xt.2.reverse) (init := fun _ => 0)
    (step := fun x acc a => a + x * acc)
    (fst _ _) ((listReverse encRat).comp (snd _ _)) (const 0) hstep
    (B := fun xt => 15 * ((encPair encRat encRatPoly xt).length + 1) ^ 2)
    (PolyBounded.of_forall_le 15 2 fun _ => le_rfl)
    fun xt i hi => by
      set L := (encPair encRat encRatPoly xt).length
      have hLt : (encRatPoly xt.2).length ≤ L := length_le_encPair_right _ _ xt
      have htl : xt.2.length ≤ L := (SizedListEncoding.length_le (encA := encRat) xt.2).trans hLt
      rw [List.length_reverse] at hi
      obtain ⟨hx_num, hx_den⟩ := num_den_le_of_length_encRat_le (length_le_encPair_left _ _ xt)
      have htB : HasCoeffBitBound L xt.2 :=
        hasCoeffBitBound_mono (hasCoeffBitBound_length_encRatPoly xt.2) hLt
      let Dt := lcmDens xt.2
      have hDt1 : 1 ≤ Dt := one_le_lcmDens xt.2
      have ht_cd : CommonDenomBound Dt (2 ^ ((xt.2.length + 1) * L)) xt.2 :=
        CommonDenomBound.of_bitBound htB
      have htrace : ∀ j ≤ xt.2.length,
          let acc := ((xt.2.reverse).take j).foldl (fun acc a => a + xt.1 * acc) 0
          ∃ z : ℤ, acc = (z : ℚ) / ((Dt * xt.1.den ^ j : ℕ) : ℚ) ∧
            z.natAbs ≤ j * 2 ^ ((L + 1) * L + j * L) := fun j hj => by
        induction j with
        | zero => exact ⟨0, by simp, by simp⟩
        | succ j ih =>
          have hj_lt : j < xt.2.reverse.length := by rw [List.length_reverse]; omega
          rw [List.take_succ_eq_append_getElem hj_lt, List.foldl_append, List.foldl_cons,
            List.foldl_nil]
          obtain ⟨zj, hzj_eq, hzj_le⟩ := ih (by omega)
          have ha_mem : (xt.2.reverse)[j] ∈ xt.2 :=
            List.mem_reverse.mp (List.getElem_mem hj_lt)
          obtain ⟨wa, hwa_eq, hwa_le⟩ := ht_cd (xt.2.reverse)[j] ha_mem
          have hwa_L : wa.natAbs ≤ 2 ^ ((L + 1) * L) := hwa_le.trans
            (Nat.pow_le_pow_right zero_lt_two
              (Nat.mul_le_mul_right L (Nat.add_le_add_right htl 1)))
          let znext : ℤ := wa * ((xt.1.den ^ (j + 1) : ℕ) : ℤ) + xt.1.num * zj
          refine ⟨znext, ?_, ?_⟩
          · set dx : ℕ := xt.1.den
            set nx : ℤ := xt.1.num
            have hDt0 : (Dt : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
            have hxden0 : (dx : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr xt.1.den_nz
            have hx_eq : xt.1 = (nx : ℚ) / (dx : ℚ) := (Rat.num_div_den xt.1).symm
            rw [hwa_eq, hzj_eq, hx_eq]
            dsimp only [znext]
            push_cast
            field_simp
            ring
          · dsimp only [znext]
            refine (Int.natAbs_add_le _ _).trans ?_
            rw [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_mul]
            have h1 := (Nat.mul_le_mul hwa_L (Nat.pow_le_pow_left hx_den (j + 1))).trans_eq
              (show _ = 2 ^ ((L + 1) * L + (j + 1) * L) by ring)
            have h2 := (Nat.mul_le_mul hx_num hzj_le).trans_eq
              (show _ = j * 2 ^ ((L + 1) * L + (j + 1) * L) by ring)
            linarith
      obtain ⟨zi, hzi_eq, hzi_le⟩ := htrace i hi
      have hDi_le : Dt * xt.1.den ^ i ≤ 2 ^ (3 * (L + 1) ^ 2) :=
        calc Dt * xt.1.den ^ i ≤ 2 ^ (L * L) * (2 ^ L) ^ i :=
              Nat.mul_le_mul ((lcmDens_le_of_bitBound htB).trans (Nat.pow_le_pow_right
                zero_lt_two (Nat.mul_le_mul_right L htl))) (Nat.pow_le_pow_left hx_den i)
          _ = 2 ^ (L * L + L * i) := by rw [← pow_mul, ← pow_add]
          _ ≤ 2 ^ (3 * (L + 1) ^ 2) := Nat.pow_le_pow_right zero_lt_two (by nlinarith)
      have hzi_K : zi.natAbs ≤ 2 ^ (3 * (L + 1) ^ 2) :=
        calc zi.natAbs ≤ 2 ^ (L + 1) * 2 ^ ((L + 1) * L + i * L) := hzi_le.trans
              (Nat.mul_le_mul_right _ ((by omega : i ≤ L + 1).trans Nat.lt_two_pow_self.le))
          _ ≤ 2 ^ (3 * (L + 1) ^ 2) := by
              rw [← pow_add]; exact Nat.pow_le_pow_right zero_lt_two (by nlinarith)
      obtain ⟨hn, hd⟩ := num_den_div_le (Nat.mul_pos hDt1 (Nat.pow_pos xt.1.den_pos)) hzi_K hDi_le
      rw [hzi_eq]
      have := Nat.one_le_pow 2 (L + 1) (by omega)
      exact (length_encRat_le_of_pow_bound hn hd).trans (by omega)
  exact hfold.of_enc_eq fun xt => congrArg encRat (hfold_eq xt.1 xt.2).symm

private theorem signVariations_nonzero_eq :
    ∀ (nz : List ℚ), (∀ q ∈ nz, q ≠ 0) →
      let bs := nz.map (fun q => decide (0 < q))
      nz.signVariations = (bs.zip bs.tail).countP (fun p => p.1 != p.2)
  | [], _ => rfl
  | [_], _ => by simp
  | a :: b :: rest, hnz => by
    have ha : a ≠ 0 := hnz a List.mem_cons_self
    have hb : b ≠ 0 := hnz b (List.mem_cons_of_mem a List.mem_cons_self)
    have ih := signVariations_nonzero_eq (b :: rest)
      (fun q hq => hnz q (List.mem_cons_of_mem a hq))
    rw [List.signVariations_cons_cons_of_ne_zero rest ha hb, ih]
    dsimp only
    simp only [List.map_cons, List.tail_cons, List.zip_cons_cons, List.countP_cons]
    rcases lt_or_gt_of_ne ha with ha_neg | ha_pos <;>
      rcases lt_or_gt_of_ne hb with hb_neg | hb_pos
    · simp [sign_neg ha_neg, sign_neg hb_neg, ha_neg.not_gt, hb_neg.not_gt]
    · simp [sign_neg ha_neg, sign_pos hb_pos, ha_neg.not_gt, hb_pos, Nat.add_comm]
    · simp [sign_pos ha_pos, sign_neg hb_neg, ha_pos, hb_neg.not_gt, Nat.add_comm]
    · simp [sign_pos ha_pos, sign_pos hb_pos, ha_pos, hb_pos]

private theorem signVariations_rat_eq (l : List ℚ) :
    l.signVariations =
      let bs := (l.filter (fun q => !decide (q = 0))).map (fun q => decide (0 < q))
      (bs.zip bs.tail).countP (fun p => p.1 != p.2) := by
  rw [← List.signVariations_filter_ne_zero l]
  exact signVariations_nonzero_eq _ fun q hq => by
    simp only [List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not] at hq
    exact hq.2

private theorem signVariations_polyTime :
    ComputableInPolyTime (List.signVariations (α := ℚ)) encRatPoly encUnary := by
  have hnz : ComputableInPolyTime _ encRatPoly encRatPoly := filter (bool_not.comp rat_isZero)
  have hbs : ComputableInPolyTime _ encRatPoly (encList encBool) :=
    mapWith (rat_lt' (const 0) (snd encBool encRat)) (const false) hnz
  have hzip := (zip encBool encBool).comp (hbs.prod ((listTail encBool).comp hbs))
  have htest : ComputableInPolyTime (fun p : Bool × (Bool × Bool) => p.2.1 != p.2.2)
      (encPair encBool (encPair encBool encBool)) encBool := of_finite _
  exact (countPWith htest (const false) hzip).of_enc_eq fun l =>
    congrArg encUnary (signVariations_rat_eq l)

/-- Evaluating `Cslib.RealRoot.sturmVariationsList` at a rational point is computable in polynomial
time from `encPair encSturmSeq encRat` to `encUnary`. -/
theorem sturmVariationsList_computableInPolyTime :
    ComputableInPolyTime (fun sx : List (List ℚ) × ℚ => sturmVariationsList sx.1 sx.2)
      (encPair encSturmSeq encRat) encUnary := by
  unfold sturmVariationsList
  exact signVariations_polyTime.comp
    (mapWith evalCoeffList_computableInPolyTime (snd _ _) (fst _ _))

/-! ### Polynomial-time Cauchy root bound and Mignotte bisection depth -/

private theorem maxAbsList_eq_foldl (l : List ℚ) :
    maxAbsList l = l.foldl (fun acc a => max acc |a|) 0 := by
  have haux : ∀ (xs : List ℚ) (acc : ℚ), 0 ≤ acc →
      xs.foldl (fun s a => max s |a|) acc = max acc (maxAbsList xs) := fun xs => by
    induction xs with
    | nil =>
      intro acc hacc
      simp [maxAbsList, max_eq_left hacc]
    | cons a xs ih =>
      intro acc hacc
      simp only [List.foldl_cons, maxAbsList, ih _ (le_trans hacc (le_max_left _ _)), max_assoc]
  rw [haux l 0 le_rfl, max_eq_right (maxAbsList_nonneg l)]

private theorem maxAbsList_foldl_mem_or_zero :
    ∀ (xs : List ℚ) (acc : ℚ),
      xs.foldl (fun s a => max s |a|) acc = acc ∨
        ∃ a ∈ xs, xs.foldl (fun s b => max s |b|) acc = |a|
  | [], acc => Or.inl rfl
  | x :: xs, acc => by
    rw [List.foldl_cons]
    rcases maxAbsList_foldl_mem_or_zero xs (max acc |x|) with heq | ⟨a, ha, heq⟩
    · rw [heq]
      rcases le_total acc |x| with hle | hge
      · exact Or.inr ⟨x, List.mem_cons_self, max_eq_right hle⟩
      · exact Or.inl (max_eq_left hge)
    · exact Or.inr ⟨a, List.mem_cons_of_mem x ha, heq⟩

private theorem rat_abs_polyTime : ComputableInPolyTime (fun q : ℚ => |q|) encRat encRat :=
  ((rat_lt' id' (const 0)).ite_decide rat_neg id').of_enc_eq fun q => by
    by_cases h : q < 0 <;> simp [h, abs_of_neg, abs_of_nonneg, not_lt.mp]

private theorem maxAbsList_polyTime :
    ComputableInPolyTime maxAbsList encRatPoly encRat := by
  have hstep : ComputableInPolyTime (fun p : ℚ × ℚ => max p.1 |p.2|)
      (encPair encRat encRat) encRat := by
    have heq : (fun p : ℚ × ℚ => max p.1 |p.2|) =
        fun p => if p.1 ≤ |p.2| then |p.2| else p.1 :=
      funext fun p => max_def p.1 |p.2|
    rw [heq]
    have habs2 := rat_abs_polyTime.comp (snd encRat encRat)
    exact (rat_le' (fst encRat encRat) habs2).ite_decide habs2 (fst encRat encRat)
  have hfold := foldl' (encA := encRat) (encB := encRat) (encL := encRatPoly)
    (list := id) (init := fun _ => 0) (step := fun acc a => max acc |a|)
    id' (const 0) hstep
    (B := fun l => (encRatPoly l).length + (encRat (0 : ℚ)).length)
    (PolyBounded.self.add (.const _))
    fun l i _ => by
      dsimp only [id_eq]
      rcases maxAbsList_foldl_mem_or_zero (l.take i) 0 with h0 | ⟨a, ha, heq⟩
      · rw [h0]; omega
      · rw [heq]
        have hal : a ∈ l := List.mem_of_mem_take ha
        have habs_enc : (encRat |a|).length = (encRat a).length := by
          rcases lt_or_ge a 0 with hneg | hnn
          · rw [abs_of_neg hneg, length_encRat_neg]
          · rw [abs_of_nonneg hnn]
        have := SizedListEncoding.length_elem_le (encA := encRat) (encL := encRatPoly) l a hal
        omega
  exact hfold.of_enc_eq fun l => by
    dsimp only [id_eq]
    exact congrArg encRat (maxAbsList_eq_foldl l)

/-- `Cslib.RealRoot.cauchyBoundNat` is computable in polynomial time from `encRatPoly` to
`encNat`. -/
@[fun_prop]
theorem cauchyBoundNat_computableInPolyTime :
    ComputableInPolyTime cauchyBoundNat encRatPoly encNat := by
  have heq : cauchyBoundNat = fun cs : List ℚ =>
      let t := CoeffList.trim cs
      if t.length ≤ 1 then 1
      else
        let lc := t.getLastD 1
        let m := maxAbsList t.reverse.tail.reverse
        let b := m / |lc| + 1
        b.num.natAbs / b.den + 1 := by
    funext cs
    simp only [cauchyBoundNat, List.getLastD_eq_getLast?, List.tail_reverse, List.reverse_reverse]
  rw [heq]
  have ht := trim_computableInPolyTime
  have hcond := unary_le' ((length_list encRat).comp ht) (const 1)
  have hlc := (ratPoly_getLastD_polyTime 1).comp ht
  have hm := maxAbsList_polyTime.comp
    ((listReverse encRat).comp ((listTail encRat).comp ((listReverse encRat).comp ht)))
  have hb := rat_add' (rat_div' hm (rat_abs_polyTime.comp hlc)) (const 1)
  have helse := binary_add' (binary_div' (intBin_natAbs.comp (rat_num.comp hb)) (rat_den.comp hb))
    (const 1)
  exact hcond.ite_decide (const 1) helse

private theorem binary_lcm_polyTime :
    ComputableInPolyTime (fun p : ℕ × ℕ => Nat.lcm p.1 p.2) (encPair encNat encNat) encNat :=
  binary_div' (binary_mul' (fst _ _) (snd _ _)) (binary_gcd' (fst _ _) (snd _ _))

private theorem lcmDens_eq_foldl (cs : List ℚ) :
    lcmDens cs = cs.foldl (fun acc q => Nat.lcm acc q.den) 1 := by
  have haux : ∀ (qs : List ℚ) (acc : ℕ),
      qs.foldl (fun s q => Nat.lcm s q.den) acc = Nat.lcm acc (lcmDens qs) := fun qs => by
    induction qs with
    | nil => intro acc; simp [lcmDens]
    | cons q qs ih =>
      intro acc
      simp only [List.foldl_cons, lcmDens, ih, Nat.lcm_assoc]
  rw [haux, Nat.lcm_one_left]

private theorem lcmDens_polyTime :
    ComputableInPolyTime lcmDens encRatPoly encNat := by
  have hstep : ComputableInPolyTime (fun p : ℕ × ℚ => Nat.lcm p.1 p.2.den)
      (encPair encNat encRat) encNat :=
    binary_lcm_polyTime.comp ((fst _ _).prod (rat_den.comp (snd _ _)))
  have hfold := foldl' (encA := encRat) (encB := encNat) (encL := encRatPoly)
    (list := id) (init := fun _ => 1) (step := fun acc q => Nat.lcm acc q.den)
    id' (const 1) hstep
    (B := fun cs => 2 * ((encRatPoly cs).length + 1) ^ 2)
    (PolyBounded.of_forall_le 2 2 fun _ => le_rfl)
    fun cs i _ => by
      let L := (encRatPoly cs).length
      rw [id_eq, ← lcmDens_eq_foldl]
      have htake_len : (cs.take i).length ≤ L :=
        (List.length_take_le' i cs).trans (SizedListEncoding.length_le (encA := encRat) cs)
      have htake_B : HasCoeffBitBound L (cs.take i) := fun q hq =>
        hasCoeffBitBound_length_encRatPoly cs q (List.mem_of_mem_take hq)
      have hlcm : lcmDens (cs.take i) ≤ 2 ^ (L * L) :=
        (lcmDens_le_of_bitBound htake_B).trans
          (Nat.pow_le_pow_right zero_lt_two (Nat.mul_le_mul_right L htake_len))
      rw [encNat_apply, Nat.size_eq_bits_len]
      have hsize : (lcmDens (cs.take i)).size ≤ L * L + 1 :=
        (Nat.size_le_size hlcm).trans (size_two_pow_le (L * L))
      dsimp only [L] at hsize
      nlinarith
  exact hfold.of_enc_eq fun cs => by
    dsimp only [id_eq]
    exact congrArg encNat (lcmDens_eq_foldl cs)

private theorem sqNormList_eq_map_sum (ns : List ℤ) :
    sqNormList ns = (ns.map fun a => a.natAbs * a.natAbs).sum := by
  have haux : ∀ (xs : List ℤ) (acc : ℕ),
      xs.foldl (fun s a => s + a.natAbs ^ 2) acc =
        acc + (xs.map fun a => a.natAbs * a.natAbs).sum := fun xs => by
    induction xs with
    | nil => intro acc; simp
    | cons a xs ih =>
      intro acc
      rw [List.foldl_cons, ih]
      simp only [List.map_cons, List.sum_cons, sq]
      omega
  rw [sqNormList, haux, zero_add]

private theorem mignotteSepSqInv_polyTime :
    ComputableInPolyTime mignotteSepSqInv encRatPoly encNat := by
  have ht := trim_computableInPolyTime
  have hd_u := unary_sub' ((length_list encRat).comp ht) (const 1)
  have hd_b := unary_to_binary.comp hd_u
  have hD := lcmDens_polyTime.comp ht
  have hns : ComputableInPolyTime _ encRatPoly (encList encIntBin) :=
    mapWith (intBin_mul' (rat_num.comp (snd _ _))
      (intBin_natCast.comp (binary_div' (fst _ _) (rat_den.comp (snd _ _))))) hD ht
  have hsn : ComputableInPolyTime _ encRatPoly encNat :=
    binary_sum.comp (mapWith
      (binary_mul' (intBin_natAbs.comp (snd encBool encIntBin))
        (intBin_natAbs.comp (snd encBool encIntBin)))
      (const false) hns)
  refine (binary_mul'
    (binary_pow' hd_b (unary_add' hd_u (const 2)))
    (binary_pow' hsn (unary_sub' hd_u (const 1)))).of_enc_eq fun cs => congrArg encNat ?_
  simp only [mignotteSepSqInv, clearDenomsList, sqNormList_eq_map_sum, Function.comp_apply]

private theorem clog4_eq_size_pred_div2 (X : ℕ) :
    Nat.clog 4 X = ((X - 1).size + 1) / 2 := by
  rcases X with _ | _ | m
  · simp
  · simp
  · have hm1 : 1 ≤ m + 1 := by omega
    have hsize_pos : 1 ≤ (m + 1).size := Nat.size_pos.mpr hm1
    set k := ((m + 1).size + 1) / 2
    have h4pow : ∀ j, 4 ^ j = 2 ^ (2 * j) := fun j => by
      rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]
    have hle : Nat.clog 4 (m + 1 + 1) ≤ k := by
      refine Nat.clog_le_of_le_pow ?_
      rw [h4pow]
      have hlt : m + 1 < 2 ^ (m + 1).size := Nat.lt_size_self (m + 1)
      have h2k : (m + 1).size ≤ 2 * k := by omega
      exact (Nat.succ_le_of_lt hlt).trans (Nat.pow_le_pow_right zero_lt_two h2k)
    have hge : k ≤ Nat.clog 4 (m + 1 + 1) := by
      by_contra hlt
      have hclog_le : 2 * Nat.clog 4 (m + 1 + 1) < (m + 1).size := by omega
      have hpow_clog := Nat.le_pow_clog (by decide : 1 < 4) (m + 1 + 1)
      rw [h4pow] at hpow_clog
      have hm_lt : m + 1 < 2 ^ (2 * Nat.clog 4 (m + 1 + 1)) := by omega
      have := Nat.size_le.mpr hm_lt
      omega
    exact le_antisymm hle hge

/-- `Cslib.RealRoot.mignotteBisectionDepth` is computable in polynomial time from `encRatPoly` to
`encUnary`. -/
@[fun_prop]
theorem mignotteBisectionDepth_computableInPolyTime :
    ComputableInPolyTime mignotteBisectionDepth encRatPoly encUnary := by
  have heq : mignotteBisectionDepth = fun cs : List ℚ =>
      let t := CoeffList.trim cs
      if t.length ≤ 2 then 0
      else
        let b := cauchyBoundNat cs
        let s := mignotteSepSqInv cs
        let u := ((4 * (b * b) * s / 3 + 1 - 1).size + 1)
        min u (u / 2) := by
    funext cs
    simp only [mignotteBisectionDepth, sq, clog4_eq_size_pred_div2]
    split_ifs
    · rfl
    · exact (Nat.min_eq_right (Nat.div_le_self _ 2)).symm
  rw [heq]
  have ht := trim_computableInPolyTime
  have hcond := unary_le' ((length_list encRat).comp ht) (const 2)
  have hb := cauchyBoundNat_computableInPolyTime
  have hs := mignotteSepSqInv_polyTime
  have hX := binary_add'
    (binary_div' (binary_mul' (binary_mul' (const 4) (binary_mul' hb hb)) hs) (const 3))
    (const 1)
  have hu := unary_add' (binary_size.comp (binary_sub' hX (const 1))) (const 1)
  have helse := binary_min_unary' hu (binary_div' (unary_to_binary.comp hu) (const 2))
  exact hcond.ite_decide (const 0) helse

/-! ### Polynomial-time left-endpoint refinement and boundary separation -/

private structure RefineArgs where
  t : List ℚ
  seq : List (List ℚ)
  fuel : ℕ
  u : ℚ
  v : ℚ
  vu : ℕ

private enc_structure encRefineArgs : RefineArgs where
  t : encRatPoly,
  seq : encSturmSeq,
  fuel : encUnary,
  u : encRat,
  v : encRat,
  vu : encUnary

private structure RefineState where
  done : Bool
  u : ℚ
  v : ℚ

private enc_structure encRefineState : RefineState where
  done : encBool,
  u : encRat,
  v : encRat

private def refineIterStep (par : List ℚ × (List (List ℚ) × ℕ)) (st : RefineState) :
    RefineState :=
  if st.done then st
  else
    let m := (st.u + st.v) / 2
    let vm := sturmVariationsList par.2.1 m
    if vm = par.2.2 then
      { done := true, u := m, v := st.v }
    else if evalCoeffList m par.1 = 0 then
      { done := true, u := m, v := m }
    else
      { done := false, u := st.u, v := m }

private theorem refineIterStep_done (par : List ℚ × (List (List ℚ) × ℕ)) (u v : ℚ) (n : ℕ) :
    (refineIterStep par)^[n] { done := true, u := u, v := v } =
      { done := true, u := u, v := v } :=
  Function.iterate_fixed rfl n

private theorem refineIterStep_eq_refineLeftLoop (t : List ℚ) (seq : List (List ℚ)) (vu : ℕ) :
    ∀ (fuel : ℕ) (u v : ℚ),
      let st := (refineIterStep (t, (seq, vu)))^[fuel] { done := false, u := u, v := v }
      ({ lower := st.u, upper := st.v } : RootInterval) = refineLeftLoop t seq fuel u v vu
  | 0, _, _ => rfl
  | fuel + 1, u, v => by
    dsimp only
    rw [Function.iterate_succ_apply, refineLeftLoop]
    dsimp only [refineIterStep]
    simp only [Bool.false_eq_true, ↓reduceIte]
    split_ifs with h1 h2
    · rw [refineIterStep_done]
    · rw [refineIterStep_done]
    · exact refineIterStep_eq_refineLeftLoop t seq vu fuel u ((u + v) / 2)

private def ScaledDyadic (D M i : ℕ) (q : ℚ) : Prop :=
  ∃ z : ℤ, q = (z : ℚ) / ((D * 2 ^ i : ℕ) : ℚ) ∧ z.natAbs ≤ M * 2 ^ i

private theorem ScaledDyadic.lift {D M i : ℕ} (hD1 : 1 ≤ D) {q : ℚ}
    (h : ScaledDyadic D M i q) : ScaledDyadic D M (i + 1) q := by
  obtain ⟨z, hq, hz⟩ := h
  have hD0 : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  refine ⟨2 * z, ?_, ?_⟩
  · rw [hq]; push_cast; field_simp; ring
  · rw [Int.natAbs_mul, show (2 : ℤ).natAbs = 2 from rfl, pow_succ]
    calc 2 * z.natAbs ≤ 2 * (M * 2 ^ i) := Nat.mul_le_mul_left 2 hz
      _ = M * (2 ^ i * 2) := by ring

private theorem ScaledDyadic.mid {D M i : ℕ} (hD1 : 1 ≤ D) {q₁ q₂ : ℚ}
    (h₁ : ScaledDyadic D M i q₁) (h₂ : ScaledDyadic D M i q₂) :
    ScaledDyadic D M (i + 1) ((q₁ + q₂) / 2) := by
  obtain ⟨z₁, hq₁, hz₁⟩ := h₁
  obtain ⟨z₂, hq₂, hz₂⟩ := h₂
  have hD0 : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  refine ⟨z₁ + z₂, ?_, ?_⟩
  · rw [hq₁, hq₂]; push_cast; field_simp; ring
  · refine (Int.natAbs_add_le z₁ z₂).trans ?_
    rw [pow_succ]
    calc z₁.natAbs + z₂.natAbs ≤ M * 2 ^ i + M * 2 ^ i := Nat.add_le_add hz₁ hz₂
      _ = M * (2 ^ i * 2) := by ring

/-- A rational `q` is a depth-`0` scaled dyadic over any multiple `q.den * k` of its denominator. -/
private theorem ScaledDyadic.zero {D M k : ℕ} {q : ℚ} (hk : 1 ≤ k) (hD : D = q.den * k)
    (hM : q.num.natAbs * k ≤ M) : ScaledDyadic D M 0 q := by
  refine ⟨q.num * k, ?_, by rwa [pow_zero, mul_one, Int.natAbs_mul, Int.natAbs_natCast]⟩
  have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  conv_lhs => rw [← Rat.num_div_den q]
  rw [hD, pow_zero, mul_one]
  push_cast
  exact (mul_div_mul_right _ _ hk0).symm

private theorem ScaledDyadic.length_encRat_le {D M i K : ℕ} (hD1 : 1 ≤ D)
    (hD : D * 2 ^ i ≤ 2 ^ K) (hM : M * 2 ^ i ≤ 2 ^ K) {q : ℚ} (h : ScaledDyadic D M i q) :
    (encRat q).length ≤ 3 * K + 6 := by
  obtain ⟨z, rfl, hz⟩ := h
  obtain ⟨hn, hd⟩ := num_den_div_le (Nat.mul_pos hD1 (Nat.two_pow_pos i)) (hz.trans hM) hD
  exact length_encRat_le_of_pow_bound hn hd

private theorem refineIterStep_dyadic {par : List ℚ × (List (List ℚ) × ℕ)}
    {D M i : ℕ} (hD1 : 1 ≤ D) {st : RefineState}
    (hu : ScaledDyadic D M i st.u) (hv : ScaledDyadic D M i st.v) :
    let st' := refineIterStep par st
    ScaledDyadic D M (i + 1) st'.u ∧ ScaledDyadic D M (i + 1) st'.v := by
  have hu' := hu.lift hD1
  have hv' := hv.lift hD1
  have hm := hu.mid hD1 hv
  dsimp only [refineIterStep]
  split_ifs
  · exact ⟨hu', hv'⟩
  · exact ⟨hm, hv'⟩
  · exact ⟨hm, hm⟩
  · exact ⟨hu', hm⟩

private theorem refineLeftLoop_polyTime :
    ComputableInPolyTime
      (fun a : RefineArgs => refineLeftLoop a.t a.seq a.fuel a.u a.v a.vu)
      encRefineArgs encRootInterval := by
  have hstep : ComputableInPolyTime
      (fun p : (List ℚ × (List (List ℚ) × ℕ)) × RefineState => refineIterStep p.1 p.2)
      (encPair (encPair encRatPoly (encPair encSturmSeq encUnary)) encRefineState)
      encRefineState := by
    unfold refineIterStep
    have hpar := fst (encPair encRatPoly (encPair encSturmSeq encUnary)) encRefineState
    have hst := snd (encPair encRatPoly (encPair encSturmSeq encUnary)) encRefineState
    have hm := rat_div' (rat_add' (encRefineState_u_polyTime hst) (encRefineState_v_polyTime hst))
      (const (2 : ℚ))
    have hvm := sturmVariationsList_computableInPolyTime.comp (hpar.snd'.fst'.prod hm)
    have hc1 := unary_beq hvm hpar.snd'.snd'
    have hc2 := rat_isZero' (evalCoeffList_computableInPolyTime.comp (hm.prod hpar.fst'))
    exact (encRefineState_done_polyTime hst).ite hst
      (hc1.ite_decide
        (encRefineState_mk_polyTime (const true) hm (encRefineState_v_polyTime hst))
        (hc2.ite_decide
          (encRefineState_mk_polyTime (const true) hm hm)
          (encRefineState_mk_polyTime (const false) (encRefineState_u_polyTime hst) hm)))
  have hpar : ComputableInPolyTime
      (fun a : RefineArgs => (a.t, (a.seq, a.vu)))
      encRefineArgs (encPair encRatPoly (encPair encSturmSeq encUnary)) :=
    (encRefineArgs_t_polyTime id').prod
      ((encRefineArgs_seq_polyTime id').prod (encRefineArgs_vu_polyTime id'))
  have hinit : ComputableInPolyTime
      (fun a : RefineArgs => ({ done := false, u := a.u, v := a.v } : RefineState))
      encRefineArgs encRefineState :=
    encRefineState_mk_polyTime (const false)
      (encRefineArgs_u_polyTime id') (encRefineArgs_v_polyTime id')
  have hiter := iterateWith hpar (encRefineArgs_fuel_polyTime id') hinit hstep
    (bound := fun a => 50 * ((encRefineArgs a).length + 1))
    (PolyBounded.of_forall_le 50 1 fun _ => by simp only [pow_one, le_refl])
    fun a i hi => by
      set L := (encRefineArgs a).length
      have hLf : a.fuel ≤ L := by
        simpa only [encUnary_apply, List.length_replicate] using encRefineArgs_fuel_length_le a
      obtain ⟨hu_num, hu_den⟩ := num_den_le_of_length_encRat_le (encRefineArgs_u_length_le a)
      obtain ⟨hv_num, hv_den⟩ := num_den_le_of_length_encRat_le (encRefineArgs_v_length_le a)
      let D := a.u.den * a.v.den
      let M := max (a.u.num.natAbs * a.v.den) (a.v.num.natAbs * a.u.den)
      have hD1 : 1 ≤ D := Nat.mul_pos a.u.den_pos a.v.den_pos
      have hpow : 2 ^ L * 2 ^ L * 2 ^ i ≤ 2 ^ (3 * L) := by
        rw [← pow_add, ← pow_add]; exact Nat.pow_le_pow_right zero_lt_two (by omega)
      have hD : D * 2 ^ i ≤ 2 ^ (3 * L) :=
        (Nat.mul_le_mul_right _ (Nat.mul_le_mul hu_den hv_den)).trans hpow
      have hM : M * 2 ^ i ≤ 2 ^ (3 * L) := (Nat.mul_le_mul_right _
        (max_le (Nat.mul_le_mul hu_num hv_den) (Nat.mul_le_mul hv_num hu_den))).trans hpow
      have htrace : ∀ j : ℕ,
          let st := (refineIterStep (a.t, (a.seq, a.vu)))^[j]
            { done := false, u := a.u, v := a.v }
          ScaledDyadic D M j st.u ∧ ScaledDyadic D M j st.v := fun j => by
        induction j with
        | zero =>
          simp only [Function.iterate_zero, id_eq]
          exact ⟨.zero a.v.den_pos rfl (le_max_left _ _),
            .zero a.u.den_pos (Nat.mul_comm _ _) (le_max_right _ _)⟩
        | succ j ih =>
          rw [Function.iterate_succ_apply']
          exact refineIterStep_dyadic hD1 ih.1 ih.2
      have hu_enc := (htrace i).1.length_encRat_le hD1 hD hM
      have hv_enc := (htrace i).2.length_encRat_le hD1 hD hM
      rw [encRefineState_apply]
      dsimp only [encRefineStateFields]
      rw [length_encPair, length_encPair, encBool_apply, List.length_singleton]
      dsimp only
      omega
  have hout := encRootInterval_mk_polyTime
    (encRefineState_u_polyTime hiter) (encRefineState_v_polyTime hiter)
  exact hout.of_enc_eq fun a => congrArg encRootInterval
    (refineIterStep_eq_refineLeftLoop a.t a.seq a.vu a.fuel a.u a.v).symm

private theorem refineLeftRoot_polyTime :
    ComputableInPolyTime
      (fun a : RefineArgs => refineLeftRoot a.t a.seq a.fuel a.u a.v a.vu)
      encRefineArgs encRootInterval := by
  have hc1 := rat_isZero'
    (evalCoeffList_computableInPolyTime.comp
      ((encRefineArgs_v_polyTime id').prod (encRefineArgs_t_polyTime id')))
  have hc2 := bool_not.comp (rat_isZero'
    (evalCoeffList_computableInPolyTime.comp
      ((encRefineArgs_u_polyTime id').prod (encRefineArgs_t_polyTime id'))))
  refine (hc1.ite_decide
    (encRootInterval_mk_polyTime (encRefineArgs_v_polyTime id') (encRefineArgs_v_polyTime id'))
    (hc2.ite
      (encRootInterval_mk_polyTime (encRefineArgs_u_polyTime id') (encRefineArgs_v_polyTime id'))
      refineLeftLoop_polyTime)).of_enc_eq fun a => congrArg encRootInterval ?_
  simp only [refineLeftRoot, Function.comp_apply, Bool.not_eq_true', decide_eq_false_iff_not]

/-! ### Polynomial-time Sturm bisection `isolateRoots` -/

private structure FrontierItem where
  isDone : Bool
  lower : ℚ
  upper : ℚ
  vu : ℕ
  vv : ℕ

private enc_structure encFrontierItem : FrontierItem where
  isDone : encBool,
  lower : encRat,
  upper : encRat,
  vu : encUnary,
  vv : encUnary

private def classifyNode (t : List ℚ) (seq : List (List ℚ)) (depthBound : ℕ)
    (u v : ℚ) (vu vv : ℕ) : List FrontierItem :=
  let count := vu - vv
  if count = 0 then []
  else if count = 1 then
    let J := refineLeftRoot t seq depthBound u v vu
    [{ isDone := true, lower := J.lower, upper := J.upper, vu := 0, vv := 0 }]
  else
    [{ isDone := false, lower := u, upper := v, vu := vu, vv := vv }]

private def stepFrontierItem (t : List ℚ) (seq : List (List ℚ)) (depthBound : ℕ)
    (it : FrontierItem) : List FrontierItem :=
  if it.isDone then [it]
  else
    let m := (it.lower + it.upper) / 2
    let vm := sturmVariationsList seq m
    classifyNode t seq depthBound it.lower m it.vu vm ++
      classifyNode t seq depthBound m it.upper vm it.vv

private def stepFrontier (t : List ℚ) (seq : List (List ℚ)) (depthBound : ℕ)
    (items : List FrontierItem) : List FrontierItem :=
  items.flatMap (stepFrontierItem t seq depthBound)

private def finishFrontier (items : List FrontierItem) : List RootInterval :=
  (items.filter (·.isDone)).map fun it => { lower := it.lower, upper := it.upper }

private def evalFrontierItem (t : List ℚ) (seq : List (List ℚ)) (depthBound fuel : ℕ)
    (it : FrontierItem) : List RootInterval :=
  if it.isDone then [{ lower := it.lower, upper := it.upper }]
  else isolateIoc t seq depthBound fuel it.lower it.upper it.vu it.vv

private theorem classifyNode_flatMap_eval (t : List ℚ) (seq : List (List ℚ))
    (depthBound fuel : ℕ) (u v : ℚ) (vu vv : ℕ) :
    (classifyNode t seq depthBound u v vu vv).flatMap (evalFrontierItem t seq depthBound fuel) =
      isolateIoc t seq depthBound fuel u v vu vv := by
  dsimp only [classifyNode]
  split_ifs with h0 h1
  · cases fuel <;> simp only [List.flatMap_nil, isolateIoc, h0, ↓reduceIte]
  · (cases fuel <;> simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
      evalFrontierItem, isolateIoc, h1, ↓reduceIte]) <;> rfl
  · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, evalFrontierItem,
      Bool.false_eq_true, ↓reduceIte]

private theorem stepFrontier_flatMap_eval (t : List ℚ) (seq : List (List ℚ))
    (depthBound fuel : ℕ) (items : List FrontierItem)
    (hact : ∀ it ∈ items, it.isDone = false → 2 ≤ it.vu - it.vv) :
    (stepFrontier t seq depthBound items).flatMap (evalFrontierItem t seq depthBound fuel) =
      items.flatMap (evalFrontierItem t seq depthBound (fuel + 1)) := by
  rw [stepFrontier, List.flatMap_assoc]
  refine List.flatMap_congr fun it hit => ?_
  by_cases hd : it.isDone = true
  · simp [stepFrontierItem, evalFrontierItem, hd]
  · have hdf : it.isDone = false := Bool.eq_false_iff.mpr hd
    have h2 : 2 ≤ it.vu - it.vv := hact it hit hdf
    have h0 : ¬(it.vu - it.vv = 0) := by omega
    have h1 : ¬(it.vu - it.vv = 1) := by omega
    simp only [stepFrontierItem, evalFrontierItem, hdf, Bool.false_eq_true, ↓reduceIte,
      List.flatMap_append, classifyNode_flatMap_eval]
    conv_rhs => rw [isolateIoc]
    simp only [h0, h1, ↓reduceIte]

private theorem finishFrontier_eq_flatMap_eval_zero (t : List ℚ) (seq : List (List ℚ))
    (depthBound : ℕ) (items : List FrontierItem)
    (hact : ∀ it ∈ items, it.isDone = false → 2 ≤ it.vu - it.vv) :
    finishFrontier items = items.flatMap (evalFrontierItem t seq depthBound 0) := by
  induction items with
  | nil => rfl
  | cons it rest ih =>
    have ih' := ih fun x hx => hact x (List.mem_cons_of_mem it hx)
    by_cases hd : it.isDone = true
    · simp only [finishFrontier, List.filter_cons_of_pos hd, List.map_cons, List.flatMap_cons,
        evalFrontierItem, hd, ↓reduceIte, List.singleton_append]
      exact congrArg (_ :: ·) ih'
    · have hdf : it.isDone = false := Bool.eq_false_iff.mpr hd
      have h2 := hact it List.mem_cons_self hdf
      have h0 : ¬(it.vu - it.vv = 0) := by omega
      have h1 : ¬(it.vu - it.vv = 1) := by omega
      simp only [finishFrontier, List.filter_cons_of_neg hd, List.flatMap_cons,
        evalFrontierItem, hdf, Bool.false_eq_true, ↓reduceIte, isolateIoc, h0, h1,
        List.nil_append]
      exact ih'

private theorem signVariations_le_length {α : Type*} [Zero α] [LinearOrder α] (l : List α) :
    l.signVariations ≤ l.length := by
  rw [List.signVariations]
  calc (((l.map SignType.sign).filter (· ≠ 0)).destutter (· ≠ ·)).length - 1
      ≤ (((l.map SignType.sign).filter (· ≠ 0)).destutter (· ≠ ·)).length := Nat.sub_le _ 1
    _ ≤ ((l.map SignType.sign).filter (· ≠ 0)).length :=
        (List.destutter_sublist _ _).length_le
    _ ≤ (l.map SignType.sign).length := List.length_filter_le _ _
    _ = l.length := List.length_map _

private theorem sturmVariationsList_le_length (seq : List (List ℚ)) (x : ℚ) :
    sturmVariationsList seq x ≤ seq.length := by
  simpa only [sturmVariationsList, List.length_map] using
    signVariations_le_length (seq.map (evalCoeffList x))

private def FrontierItemInv (cs : List ℚ) (k : ℕ) (it : FrontierItem) : Prop :=
  let seq := sturmSeqList cs
  let b := cauchyBoundNat cs
  let depth := mignotteBisectionDepth cs
  if it.isDone then
    DyadicBounded b (k + depth) it.lower ∧ DyadicBounded b (k + depth) it.upper ∧
      it.vu = 0 ∧ it.vv = 0
  else
    it.lower < it.upper ∧
      it.vu = sturmVariationsList seq it.lower ∧
      it.vv = sturmVariationsList seq it.upper ∧
      2 ≤ it.vu - it.vv ∧
      DyadicBounded b k it.lower ∧ DyadicBounded b k it.upper

private theorem classifyNode_props (cs : List ℚ) (k : ℕ) {u v : ℚ} (huv : u < v)
    (hu_d : DyadicBounded (cauchyBoundNat cs) k u)
    (hv_d : DyadicBounded (cauchyBoundNat cs) k v) :
    let t := CoeffList.trim cs
    let seq := sturmSeqList cs
    let depth := mignotteBisectionDepth cs
    let vu := sturmVariationsList seq u
    let vv := sturmVariationsList seq v
    let out := classifyNode t seq depth u v vu vv
    out.length ≤ 1 ∧
      (∀ it ∈ out, FrontierItemInv cs k it) ∧
      (∀ it ∈ out, it.isDone = false → it.lower = u ∧ it.upper = v) := by
  dsimp only [classifyNode]
  split_ifs with h0 h1
  · simp
  · simp only [List.length_singleton, le_refl, List.mem_singleton, forall_eq, FrontierItemInv,
      ↓reduceIte, and_self, and_true, Bool.true_eq_false, IsEmpty.forall_iff, true_and]
    exact refineLeftRoot_dyadicBounded _ _ _ _ _ _ _ _ hu_d hv_d
  · simp only [List.length_singleton, le_refl, List.mem_singleton, forall_eq, FrontierItemInv,
      Bool.false_eq_true, ↓reduceIte, forall_const, and_self, and_true, true_and]
    exact ⟨huv, by omega, hu_d, hv_d⟩

private theorem pairwise_flatMap_active {items : List FrontierItem}
    (f : FrontierItem → List FrontierItem)
    (hpw : (items.filter (fun it => !it.isDone)).Pairwise (fun A B => A.upper ≤ B.lower))
    (hdone_act : ∀ it ∈ items, it.isDone = true →
      (f it).filter (fun x => !x.isDone) = [])
    (hact_pw : ∀ it ∈ items, it.isDone = false →
      ((f it).filter (fun x => !x.isDone)).Pairwise (fun A B => A.upper ≤ B.lower))
    (hact_bounds : ∀ it ∈ items, it.isDone = false →
      ∀ x ∈ (f it).filter (fun x => !x.isDone), it.lower ≤ x.lower ∧ x.upper ≤ it.upper) :
    ((items.flatMap f).filter (fun x => !x.isDone)).Pairwise (fun A B => A.upper ≤ B.lower) := by
  induction items with
  | nil => simp
  | cons it rest ih =>
    rw [List.flatMap_cons, List.filter_append]
    by_cases hd : it.isDone = true
    · simp only [List.filter_cons, hd, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpw
      rw [hdone_act it List.mem_cons_self hd, List.nil_append]
      exact ih hpw (fun x hx => hdone_act x (List.mem_cons_of_mem it hx))
        (fun x hx => hact_pw x (List.mem_cons_of_mem it hx))
        (fun x hx => hact_bounds x (List.mem_cons_of_mem it hx))
    · have hdf : it.isDone = false := Bool.eq_false_iff.mpr hd
      simp only [List.filter_cons, hdf, Bool.not_false, ↓reduceIte, List.pairwise_cons] at hpw
      obtain ⟨hhead, hpw_rest⟩ := hpw
      have ih' := ih hpw_rest (fun x hx => hdone_act x (List.mem_cons_of_mem it hx))
        (fun x hx => hact_pw x (List.mem_cons_of_mem it hx))
        (fun x hx => hact_bounds x (List.mem_cons_of_mem it hx))
      rw [List.pairwise_append]
      refine ⟨hact_pw it List.mem_cons_self hdf, ih', fun x hx y hy => ?_⟩
      rw [List.mem_filter, List.mem_flatMap] at hy
      obtain ⟨⟨it2, hit2, hy_f⟩, hy_act⟩ := hy
      by_cases hd2 : it2.isDone = true
      · have hnil := hdone_act it2 (List.mem_cons_of_mem it hit2) hd2
        have : y ∈ (f it2).filter (fun z => !z.isDone) := List.mem_filter.mpr ⟨hy_f, hy_act⟩
        rw [hnil] at this
        exact (List.not_mem_nil this).elim
      · have hdf2 : it2.isDone = false := Bool.eq_false_iff.mpr hd2
        have hit2_flt : it2 ∈ rest.filter (fun z => !z.isDone) :=
          List.mem_filter.mpr ⟨hit2, by simp [hdf2]⟩
        have hx_b := hact_bounds it List.mem_cons_self hdf x hx
        have hy_b := hact_bounds it2 (List.mem_cons_of_mem it hit2) hdf2 y
          (List.mem_filter.mpr ⟨hy_f, hy_act⟩)
        exact hx_b.2.trans ((hhead it2 hit2_flt).trans hy_b.1)

private theorem length_flatMap_stepFrontier_le {t : List ℚ} {seq : List (List ℚ)}
    {depth : ℕ} :
    ∀ items : List FrontierItem,
      (∀ it ∈ items, it.isDone = false →
        (stepFrontierItem t seq depth it).length ≤ 2) →
      (stepFrontier t seq depth items).length ≤
        items.length + (items.filter (fun it => !it.isDone)).length
  | [], _ => by simp [stepFrontier]
  | it :: rest, h2 => by
    have ih := length_flatMap_stepFrontier_le rest fun x hx => h2 x (List.mem_cons_of_mem it hx)
    simp only [stepFrontier, List.flatMap_cons, List.length_append] at ih ⊢
    by_cases hd : it.isDone = true
    · simp only [stepFrontierItem, hd, ↓reduceIte, List.length_cons, List.length_nil,
        List.filter_cons, Bool.not_true, Bool.false_eq_true]
      omega
    · have hdf : it.isDone = false := Bool.eq_false_iff.mpr hd
      have hlen2 := h2 it List.mem_cons_self hdf
      simp only [List.length_cons, List.filter_cons, hdf, Bool.not_false, ↓reduceIte]
      omega

private theorem pairwise_of_length_le_one {α : Type*} {R : α → α → Prop} :
    ∀ {l : List α}, l.length ≤ 1 → l.Pairwise R
  | [], _ => .nil
  | [x], _ => List.pairwise_singleton R x
  | _ :: _ :: _, h => by simp at h

private theorem stepFrontier_iterate_invariant (cs : List ℚ) :
    let t := CoeffList.trim cs
    let seq := sturmSeqList cs
    let b := cauchyBoundNat cs
    let depth := mignotteBisectionDepth cs
    let init := classifyNode t seq depth (-(b : ℚ)) (b : ℚ)
      (sturmVariationsList seq (-(b : ℚ))) (sturmVariationsList seq (b : ℚ))
    ∀ k ≤ depth,
      let items := (stepFrontier t seq depth)^[k] init
      items.length ≤ 1 + 2 * cs.length * k ∧
        (∀ it ∈ items, FrontierItemInv cs k it) ∧
        (items.filter (fun it => !it.isDone)).Pairwise (fun A B => A.upper ≤ B.lower) ∧
        items.flatMap (evalFrontierItem t seq depth (depth - k)) =
          isolateIoc t seq depth depth (-(b : ℚ)) (b : ℚ)
            (sturmVariationsList seq (-(b : ℚ))) (sturmVariationsList seq (b : ℚ)) := by
  intro t seq b depth init k hk
  induction k with
  | zero =>
    have hb_pos : (0 : ℚ) < (b : ℚ) := Nat.cast_pos.mpr (one_le_cauchyBoundNat cs)
    obtain ⟨hlen1, hinv0, _⟩ := classifyNode_props cs 0 (by linarith : -(b : ℚ) < b)
      (DyadicBounded.of_neg_nat b) (DyadicBounded.of_nat b)
    simp only [Function.iterate_zero, id_eq, mul_zero, add_zero, Nat.sub_zero]
    exact ⟨hlen1, hinv0, pairwise_of_length_le_one ((List.length_filter_le _ _).trans hlen1),
      classifyNode_flatMap_eval _ _ _ _ _ _ _ _⟩
  | succ k ih =>
    obtain ⟨hlen_k, hinv_k, hpw_k, heval_k⟩ := ih (by omega)
    set items_k := (stepFrontier t seq depth)^[k] init
    rw [Function.iterate_succ_apply']
    let active_k := items_k.filter (fun it => !it.isDone)
    have hact_le : active_k.length ≤ 2 * cs.length := by
      let Lpairs : List (ℚ × ℚ) := active_k.map fun it : FrontierItem => (it.lower, it.upper)
      have hL_mem : ∀ p ∈ Lpairs, p.1 < p.2 ∧
          2 ≤ sturmVariationsList seq p.1 - sturmVariationsList seq p.2 := by
        intro p hp
        rw [List.mem_map] at hp
        obtain ⟨it, hit, rfl⟩ := hp
        rw [List.mem_filter] at hit
        have hdf : it.isDone = false := by simpa using hit.2
        have hinv := hinv_k it hit.1
        simp only [FrontierItemInv, hdf, Bool.false_eq_true, ↓reduceIte] at hinv
        obtain ⟨hlt, hvu, hvv, h2, _, _⟩ := hinv
        exact ⟨hlt, hvu ▸ hvv ▸ h2⟩
      have hL_pw : Lpairs.Pairwise (fun p q => p.2 ≤ q.1) :=
        List.Pairwise.map (fun it : FrontierItem => (it.lower, it.upper)) (fun _ _ h => h) hpw_k
      simpa only [Lpairs, List.length_map] using
        card_active_sturm_intervals_le cs Lpairs hL_mem hL_pw
    have hstep_props : ∀ it ∈ items_k, it.isDone = false →
        let out := stepFrontierItem t seq depth it
        out.length ≤ 2 ∧
          (∀ x ∈ out, FrontierItemInv cs (k + 1) x) ∧
          ((out.filter (fun x => !x.isDone)).Pairwise (fun A B => A.upper ≤ B.lower)) ∧
          (∀ x ∈ out.filter (fun x => !x.isDone), it.lower ≤ x.lower ∧ x.upper ≤ it.upper) := by
      intro it hit hdf
      have hinv := hinv_k it hit
      simp only [FrontierItemInv, hdf, Bool.false_eq_true, ↓reduceIte] at hinv
      obtain ⟨hlt, hvu_eq, hvv_eq, _, hu_d, hv_d⟩ := hinv
      let m := (it.lower + it.upper) / 2
      have hum : it.lower < m := by dsimp only [m]; linarith
      have hmv : m < it.upper := by dsimp only [m]; linarith
      have hm_d := hu_d.mid hv_d
      obtain ⟨hl1, hi1, hb1⟩ := classifyNode_props cs (k + 1) hum (hu_d.mono (by omega)) hm_d
      obtain ⟨hl2, hi2, hb2⟩ := classifyNode_props cs (k + 1) hmv hm_d (hv_d.mono (by omega))
      dsimp only [t, seq, depth] at hl1 hi1 hb1 hl2 hi2 hb2 ⊢
      have hout_eq :
          stepFrontierItem (CoeffList.trim cs) (sturmSeqList cs) (mignotteBisectionDepth cs) it =
          classifyNode (CoeffList.trim cs) (sturmSeqList cs) (mignotteBisectionDepth cs)
            it.lower m (sturmVariationsList (sturmSeqList cs) it.lower)
            (sturmVariationsList (sturmSeqList cs) m) ++
          classifyNode (CoeffList.trim cs) (sturmSeqList cs) (mignotteBisectionDepth cs)
            m it.upper (sturmVariationsList (sturmSeqList cs) m)
            (sturmVariationsList (sturmSeqList cs) it.upper) := by
        simp [stepFrontierItem, hdf, hvu_eq, hvv_eq, m]
      rw [hout_eq]
      refine ⟨by rw [List.length_append]; omega, ?_, ?_, ?_⟩
      · intro x hx
        rw [List.mem_append] at hx
        exact hx.elim (hi1 x) (hi2 x)
      · rw [List.filter_append, List.pairwise_append]
        refine ⟨pairwise_of_length_le_one ((List.length_filter_le _ _).trans hl1),
          pairwise_of_length_le_one ((List.length_filter_le _ _).trans hl2),
          fun x hx y hy => ?_⟩
        rw [List.mem_filter] at hx hy
        rw [(hb1 x hx.1 (by simpa using hx.2)).2, (hb2 y hy.1 (by simpa using hy.2)).1]
      · intro x hx
        rw [List.mem_filter, List.mem_append] at hx
        have hxf : x.isDone = false := by simpa using hx.2
        rcases hx.1 with hx1 | hx2
        · rw [(hb1 x hx1 hxf).1, (hb1 x hx1 hxf).2]
          exact ⟨le_rfl, hmv.le⟩
        · rw [(hb2 x hx2 hxf).1, (hb2 x hx2 hxf).2]
          exact ⟨hum.le, le_rfl⟩
    have hlen_next : (stepFrontier t seq depth items_k).length ≤ 1 + 2 * cs.length * (k + 1) := by
      calc _ ≤ items_k.length + active_k.length :=
            length_flatMap_stepFrontier_le items_k fun it hit hdf => (hstep_props it hit hdf).1
        _ ≤ 1 + 2 * cs.length * (k + 1) := by rw [mul_add_one]; omega
    have hinv_next : ∀ x ∈ stepFrontier t seq depth items_k, FrontierItemInv cs (k + 1) x := by
      intro x hx
      rw [stepFrontier, List.mem_flatMap] at hx
      obtain ⟨it, hit, hx_it⟩ := hx
      by_cases hd : it.isDone = true
      · simp only [stepFrontierItem, hd, ↓reduceIte, List.mem_singleton] at hx_it
        rcases hx_it with rfl
        have hinv := hinv_k x hit
        simp only [FrontierItemInv, hd, ↓reduceIte] at hinv ⊢
        exact ⟨hinv.1.mono (by omega), hinv.2.1.mono (by omega), hinv.2.2⟩
      · exact (hstep_props it hit (Bool.eq_false_iff.mpr hd)).2.1 x hx_it
    have hpw_next :
        ((stepFrontier t seq depth items_k).filter (fun x => !x.isDone)).Pairwise
          (fun A B => A.upper ≤ B.lower) := by
      refine pairwise_flatMap_active (stepFrontierItem t seq depth) hpw_k
        (fun it _ hd => by simp [stepFrontierItem, hd])
        (fun it hit hdf => (hstep_props it hit hdf).2.2.1)
        (fun it hit hdf => (hstep_props it hit hdf).2.2.2)
    have heval_next :
        (stepFrontier t seq depth items_k).flatMap
            (evalFrontierItem t seq depth (depth - (k + 1))) =
          isolateIoc t seq depth depth (-(b : ℚ)) (b : ℚ)
            (sturmVariationsList seq (-(b : ℚ))) (sturmVariationsList seq (b : ℚ)) := by
      rw [stepFrontier_flatMap_eval t seq depth (depth - (k + 1)) items_k fun it hit hdf => by
        have hinv := hinv_k it hit
        simp only [FrontierItemInv, hdf, Bool.false_eq_true, ↓reduceIte] at hinv
        exact hinv.2.2.2.1, show depth - (k + 1) + 1 = depth - k by omega]
      exact heval_k
    exact ⟨hlen_next, hinv_next, hpw_next, heval_next⟩

private structure ClassifyArgs where
  t : List ℚ
  seq : List (List ℚ)
  depthBound : ℕ
  u : ℚ
  v : ℚ
  vu : ℕ
  vv : ℕ

private enc_structure encClassifyArgs : ClassifyArgs where
  t : encRatPoly,
  seq : encSturmSeq,
  depthBound : encUnary,
  u : encRat,
  v : encRat,
  vu : encUnary,
  vv : encUnary

private theorem classifyNode_polyTime :
    ComputableInPolyTime
      (fun a : ClassifyArgs => classifyNode a.t a.seq a.depthBound a.u a.v a.vu a.vv)
      encClassifyArgs (encList encFrontierItem) := by
  have hcnt := unary_sub' (encClassifyArgs_vu_polyTime id') (encClassifyArgs_vv_polyTime id')
  have hrefArgs := encRefineArgs_mk_polyTime
    (encClassifyArgs_t_polyTime id') (encClassifyArgs_seq_polyTime id')
    (encClassifyArgs_depthBound_polyTime id') (encClassifyArgs_u_polyTime id')
    (encClassifyArgs_v_polyTime id') (encClassifyArgs_vu_polyTime id')
  have hJ := refineLeftRoot_polyTime.comp hrefArgs
  have hdone_item := encFrontierItem_mk_polyTime (const true)
    (encRootInterval_lower_polyTime hJ) (encRootInterval_upper_polyTime hJ)
    (const 0) (const 0)
  have hact_item := encFrontierItem_mk_polyTime (const false)
    (encClassifyArgs_u_polyTime id') (encClassifyArgs_v_polyTime id')
    (encClassifyArgs_vu_polyTime id') (encClassifyArgs_vv_polyTime id')
  refine ((unary_beq hcnt (const 0)).ite (const [])
    ((unary_beq hcnt (const 1)).ite
      ((cons encFrontierItem).comp (hdone_item.prod (const [])))
      ((cons encFrontierItem).comp (hact_item.prod (const []))))).of_enc_eq fun a =>
    congrArg (encList encFrontierItem) ?_
  simp only [classifyNode, Function.comp_apply, beq_iff_eq]

private def stepFrontierPar (par : List ℚ × (List (List ℚ) × ℕ))
    (items : List FrontierItem) : List FrontierItem :=
  stepFrontier par.1 par.2.1 par.2.2 items

private theorem stepFrontier_polyTime :
    ComputableInPolyTime
      (fun p : (List ℚ × (List (List ℚ) × ℕ)) × List FrontierItem =>
        stepFrontierPar p.1 p.2)
      (encPair (encPair encRatPoly (encPair encSturmSeq encUnary)) (encList encFrontierItem))
      (encList encFrontierItem) := by
  have hf : ComputableInPolyTime
      (fun q : (List ℚ × (List (List ℚ) × ℕ)) × FrontierItem =>
        stepFrontierItem q.1.1 q.1.2.1 q.1.2.2 q.2)
      (encPair (encPair encRatPoly (encPair encSturmSeq encUnary)) encFrontierItem)
      (encList encFrontierItem) := by
    unfold stepFrontierItem
    have hpar := fst (encPair encRatPoly (encPair encSturmSeq encUnary)) encFrontierItem
    have hit := snd (encPair encRatPoly (encPair encSturmSeq encUnary)) encFrontierItem
    have hm := rat_div'
      (rat_add' (encFrontierItem_lower_polyTime hit) (encFrontierItem_upper_polyTime hit))
      (const (2 : ℚ))
    have hvm := sturmVariationsList_computableInPolyTime.comp (hpar.snd'.fst'.prod hm)
    have hleft_args := encClassifyArgs_mk_polyTime hpar.fst' hpar.snd'.fst' hpar.snd'.snd'
      (encFrontierItem_lower_polyTime hit) hm (encFrontierItem_vu_polyTime hit) hvm
    have hright_args := encClassifyArgs_mk_polyTime hpar.fst' hpar.snd'.fst' hpar.snd'.snd'
      hm (encFrontierItem_upper_polyTime hit) hvm (encFrontierItem_vv_polyTime hit)
    exact (encFrontierItem_isDone_polyTime hit).ite
      ((cons encFrontierItem).comp (hit.prod (const [])))
      ((listAppend encFrontierItem).comp
        ((classifyNode_polyTime.comp hleft_args).prod (classifyNode_polyTime.comp hright_args)))
  exact (flatMapWith hf (fst _ _) (snd _ _)).of_enc_eq fun _ => rfl

/-- Certified Sturm-bisection real-root isolation `Cslib.RealRoot.isolateRoots` is computable in
polynomial time from `encRatPoly` to `encRootIntervals`. -/
@[fun_prop]
theorem isolateRoots_computableInPolyTime :
    ComputableInPolyTime isolateRoots encRatPoly encRootIntervals := by
  have ht := trim_computableInPolyTime
  have hseq := sturmSeqList_computableInPolyTime
  have hb_rat := rat_intCast.comp (intBin_natCast.comp cauchyBoundNat_computableInPolyTime)
  have hdepth := mignotteBisectionDepth_computableInPolyTime
  have hvLeft := sturmVariationsList_computableInPolyTime.comp (hseq.prod (rat_neg' hb_rat))
  have hvRight := sturmVariationsList_computableInPolyTime.comp (hseq.prod hb_rat)
  have hinit_args := encClassifyArgs_mk_polyTime ht hseq hdepth
    (rat_neg' hb_rat) hb_rat hvLeft hvRight
  have hinit : ComputableInPolyTime
      (fun cs : List ℚ =>
        if (CoeffList.trim cs).isEmpty then ([] : List FrontierItem)
        else
          classifyNode (CoeffList.trim cs) (sturmSeqList cs) (mignotteBisectionDepth cs)
            (-(cauchyBoundNat cs : ℚ)) (cauchyBoundNat cs : ℚ)
            (sturmVariationsList (sturmSeqList cs) (-(cauchyBoundNat cs : ℚ)))
            (sturmVariationsList (sturmSeqList cs) (cauchyBoundNat cs : ℚ)))
      encRatPoly (encList encFrontierItem) :=
    ((listIsEmpty' encRat).comp ht).ite (const []) (classifyNode_polyTime.comp hinit_args)
  have hcount : ComputableInPolyTime
      (fun cs : List ℚ =>
        if (CoeffList.trim cs).isEmpty then 0 else mignotteBisectionDepth cs)
      encRatPoly encUnary :=
    ((listIsEmpty' encRat).comp ht).ite (const 0) hdepth
  have hpar := ht.prod (hseq.prod hdepth)
  have hiter := iterateWith (step := stepFrontierPar) hpar hcount hinit stepFrontier_polyTime
    (bound := fun cs => 8891 * ((encRatPoly cs).length + 1) ^ 7)
    (PolyBounded.of_forall_le 8891 7 fun _ => le_rfl)
    fun cs k hk => by
      let L := (encRatPoly cs).length
      let N := L + 1
      have hNdef : N = L + 1 := rfl
      have hN1 : 0 < N := by omega
      by_cases he : (CoeffList.trim cs).isEmpty = true
      · simp only [he, ↓reduceIte, Nat.le_zero] at hk ⊢
        subst hk
        simp only [Function.iterate_zero, id_eq, encList_nil, List.length_nil]
        exact Nat.zero_le _
      · simp only [he, Bool.false_eq_true, ↓reduceIte] at hk ⊢
        obtain ⟨hlen_k, hinv_k, _, _⟩ := stepFrontier_iterate_invariant cs k hk
        change (encList encFrontierItem
          ((stepFrontier (CoeffList.trim cs) (sturmSeqList cs) (mignotteBisectionDepth cs))^[k]
            (classifyNode (CoeffList.trim cs) (sturmSeqList cs) (mignotteBisectionDepth cs)
              (-(cauchyBoundNat cs : ℚ)) (cauchyBoundNat cs : ℚ)
              (sturmVariationsList (sturmSeqList cs) (-(cauchyBoundNat cs : ℚ)))
              (sturmVariationsList (sturmSeqList cs) (cauchyBoundNat cs : ℚ))))).length ≤
          8891 * ((encRatPoly cs).length + 1) ^ 7
        set items_k := (stepFrontier (CoeffList.trim cs) (sturmSeqList cs)
          (mignotteBisectionDepth cs))^[k]
          (classifyNode (CoeffList.trim cs) (sturmSeqList cs) (mignotteBisectionDepth cs)
            (-(cauchyBoundNat cs : ℚ)) (cauchyBoundNat cs : ℚ)
            (sturmVariationsList (sturmSeqList cs) (-(cauchyBoundNat cs : ℚ)))
            (sturmVariationsList (sturmSeqList cs) (cauchyBoundNat cs : ℚ)))
        have hcs_len : cs.length ≤ L := SizedListEncoding.length_le (encA := encRat) cs
        have hB_cs : HasCoeffBitBound L cs := hasCoeffBitBound_length_encRatPoly cs
        have hNN3 : N ≤ N ^ 3 := Nat.le_self_pow (by norm_num) N
        have hN3 : 1 ≤ N ^ 3 := Nat.pow_pos hN1
        have hdepth_le : mignotteBisectionDepth cs ≤ 8 * N ^ 3 :=
          (mignotteBisectionDepth_le_of_bitBound hB_cs).trans
            ((Nat.mul_le_mul (Nat.pow_le_pow_left (by omega : cs.length + 2 ≤ 2 * N) 2)
              (by omega : L + 2 ≤ 2 * N)).trans_eq (by ring))
        have hk_le : k ≤ 8 * N ^ 3 := hk.trans hdepth_le
        have hb_le : cauchyBoundNat cs ≤ 2 ^ (2 * N) := by
          have hcb := cauchyBoundNat_le_of_bitBound hB_cs
          have hpow1 : 1 ≤ 2 ^ (2 * L) := Nat.one_le_pow (2 * L) 2 zero_lt_two
          rw [show 2 * N = 2 * L + 2 by omega, pow_add]
          change cauchyBoundNat cs ≤ 2 ^ (2 * L) * 4
          omega
        have hitem_enc : ∀ it ∈ items_k, (encFrontierItem it).length ≤ 261 * N ^ 3 := by
          intro it hit
          have hinv := hinv_k it hit
          have hdyad : DyadicBounded (cauchyBoundNat cs) (16 * N ^ 3) it.lower ∧
              DyadicBounded (cauchyBoundNat cs) (16 * N ^ 3) it.upper ∧
              it.vu ≤ N ^ 3 ∧ it.vv ≤ N ^ 3 := by
            by_cases hd : it.isDone = true
            · simp only [FrontierItemInv, hd, ↓reduceIte] at hinv
              exact ⟨hinv.1.mono (by omega), hinv.2.1.mono (by omega),
                by rw [hinv.2.2.1]; exact Nat.zero_le _,
                by rw [hinv.2.2.2]; exact Nat.zero_le _⟩
            · have hdf : it.isDone = false := Bool.eq_false_iff.mpr hd
              simp only [FrontierItemInv, hdf, Bool.false_eq_true, ↓reduceIte] at hinv
              have hseq_len : (sturmSeqList cs).length ≤ N ^ 3 := by
                have := (sturmSeqList_length_le cs).trans
                  (Nat.add_le_add_right ((natDegree_ofCoeffList_le cs).trans (Nat.sub_le _ _)) 1)
                omega
              exact ⟨hinv.2.2.2.2.1.mono (by omega), hinv.2.2.2.2.2.mono (by omega),
                hinv.2.1 ▸ (sturmVariationsList_le_length _ _).trans hseq_len,
                hinv.2.2.1 ▸ (sturmVariationsList_le_length _ _).trans hseq_len⟩
          have hrat_b (q : ℚ) (hq : DyadicBounded (cauchyBoundNat cs) (16 * N ^ 3) q) :
              (encRat q).length ≤ 63 * N ^ 3 := by
            have hn : q.num.natAbs ≤ 2 ^ (19 * N ^ 3) :=
              (hq.natAbs_num_le.trans (Nat.mul_le_mul_right _ hb_le)).trans <| by
                rw [← pow_add]; exact Nat.pow_le_pow_right zero_lt_two (by omega)
            have := length_encRat_le_of_pow_bound hn
              (hq.den_le.trans (Nat.pow_le_pow_right zero_lt_two (by omega)))
            omega
          obtain ⟨hl, hu, hvu_l, hvv_l⟩ := hdyad
          have hl_enc := hrat_b _ hl
          have hu_enc := hrat_b _ hu
          rw [encFrontierItem_apply]
          dsimp only [encFrontierItemFields]
          rw [length_encPair, length_encPair, length_encPair, length_encPair]
          simp only [encBool_apply, List.length_singleton, encUnary_apply, List.length_replicate]
          omega
        have hitems_N4 : items_k.length ≤ 17 * N ^ 4 := by
          have hN4 : 1 ≤ N ^ 4 := Nat.pow_pos hN1
          calc items_k.length ≤ 1 + 2 * N * (8 * N ^ 3) := hlen_k.trans
                (Nat.add_le_add_left (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (by omega)) hk_le) 1)
            _ = 1 + 16 * N ^ 4 := by ring
            _ ≤ 17 * N ^ 4 := by omega
        calc (encList encFrontierItem items_k).length
            ≤ items_k.length * (2 * (261 * N ^ 3) + 1) :=
              length_encList_le encFrontierItem items_k hitem_enc
          _ ≤ (17 * N ^ 4) * (523 * N ^ 3) := Nat.mul_le_mul hitems_N4 (by omega)
          _ = 8891 * N ^ 7 := by ring
  have hfinish :
      ComputableInPolyTime finishFrontier (encList encFrontierItem) encRootIntervals := by
    unfold finishFrontier
    exact mapWith
      (encRootInterval_mk_polyTime
        (encFrontierItem_lower_polyTime (snd encBool encFrontierItem))
        (encFrontierItem_upper_polyTime (snd encBool encFrontierItem)))
      (const false) (filter (encFrontierItem_isDone_polyTime id'))
  refine (hfinish.comp hiter).of_enc_eq fun cs => congrArg encRootIntervals ?_
  dsimp only [isolateRoots, Function.comp_apply, stepFrontierPar]
  by_cases he : (CoeffList.trim cs).isEmpty = true
  · simp only [he, ↓reduceIte, Function.iterate_zero, id_eq, finishFrontier,
      List.filter_nil, List.map_nil]
  · simp only [he, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨_, hinv_d, _, heval_d⟩ :=
      stepFrontier_iterate_invariant cs (mignotteBisectionDepth cs) le_rfl
    rw [Nat.sub_self] at heval_d
    rw [← heval_d]
    exact (finishFrontier_eq_flatMap_eval_zero (CoeffList.trim cs) (sturmSeqList cs)
      (mignotteBisectionDepth cs) _ fun it hit hdf => by
        have hinv := hinv_d it hit
        simp only [FrontierItemInv, hdf, Bool.false_eq_true, ↓reduceIte] at hinv
        exact hinv.2.2.2.1).symm

/-! ### Polynomial-time boundary separation `separateTouching` and `isolateRootsTotal` -/

private structure SepMidArgs where
  seq : List (List ℚ)
  fuel : ℕ
  a : ℚ
  m : ℚ
  b : ℚ
  vm : ℕ

private enc_structure encSepMidArgs : SepMidArgs where
  seq : encSturmSeq,
  fuel : encUnary,
  a : encRat,
  m : encRat,
  b : encRat,
  vm : encUnary

private structure SepMidState where
  done : Bool
  a : ℚ
  m : ℚ
  b : ℚ

private enc_structure encSepMidState : SepMidState where
  done : encBool,
  a : encRat,
  m : encRat,
  b : encRat

private def sepMidIterStep (par : List (List ℚ) × ℕ) (st : SepMidState) : SepMidState :=
  if st.done then st
  else
    let m₁ := (st.a + st.m) / 2
    if sturmVariationsList par.1 m₁ = par.2 then
      { done := true, a := m₁, m := st.m, b := st.m }
    else
      let m₂ := (st.m + st.b) / 2
      if sturmVariationsList par.1 m₂ = par.2 then
        { done := true, a := st.m, m := st.m, b := m₂ }
      else
        { done := false, a := m₁, m := st.m, b := m₂ }

private theorem sepMidIterStep_done (par : List (List ℚ) × ℕ) (a m b : ℚ) (n : ℕ) :
    (sepMidIterStep par)^[n] { done := true, a := a, m := m, b := b } =
      { done := true, a := a, m := m, b := b } :=
  Function.iterate_fixed rfl n

private theorem sepMidIterStep_eq_separateMidLoop (seq : List (List ℚ)) (vm : ℕ) :
    ∀ (fuel : ℕ) (a m b : ℚ),
      let st := (sepMidIterStep (seq, vm))^[fuel] { done := false, a := a, m := m, b := b }
      (st.a, st.b) = separateMidLoop seq fuel a m b vm
  | 0, _, _, _ => rfl
  | fuel + 1, a, m, b => by
    dsimp only
    rw [Function.iterate_succ_apply, separateMidLoop]
    dsimp only [sepMidIterStep]
    simp only [Bool.false_eq_true, ↓reduceIte]
    split_ifs with h1 h2
    · rw [sepMidIterStep_done]
    · rw [sepMidIterStep_done]
    · exact sepMidIterStep_eq_separateMidLoop seq vm fuel ((a + m) / 2) m ((m + b) / 2)

private theorem sepMidIterStep_dyadic {par : List (List ℚ) × ℕ}
    {D M i : ℕ} (hD1 : 1 ≤ D) {st : SepMidState}
    (ha : ScaledDyadic D M i st.a) (hm : ScaledDyadic D M i st.m)
    (hb : ScaledDyadic D M i st.b) :
    let st' := sepMidIterStep par st
    ScaledDyadic D M (i + 1) st'.a ∧
      ScaledDyadic D M (i + 1) st'.m ∧
      ScaledDyadic D M (i + 1) st'.b := by
  have ha' := ha.lift hD1
  have hm' := hm.lift hD1
  have hb' := hb.lift hD1
  have hm1 := ha.mid hD1 hm
  have hm2 := hm.mid hD1 hb
  dsimp only [sepMidIterStep]
  split_ifs
  · exact ⟨ha', hm', hb'⟩
  · exact ⟨hm1, hm', hm'⟩
  · exact ⟨hm', hm', hm2⟩
  · exact ⟨hm1, hm', hm2⟩

private theorem separateMidLoop_polyTime :
    ComputableInPolyTime
      (fun x : SepMidArgs => separateMidLoop x.seq x.fuel x.a x.m x.b x.vm)
      encSepMidArgs (encPair encRat encRat) := by
  have hstep : ComputableInPolyTime
      (fun p : (List (List ℚ) × ℕ) × SepMidState => sepMidIterStep p.1 p.2)
      (encPair (encPair encSturmSeq encUnary) encSepMidState) encSepMidState := by
    unfold sepMidIterStep
    have hpar := fst (encPair encSturmSeq encUnary) encSepMidState
    have hst := snd (encPair encSturmSeq encUnary) encSepMidState
    have hm1 := rat_div' (rat_add' (encSepMidState_a_polyTime hst) (encSepMidState_m_polyTime hst))
      (const (2 : ℚ))
    have hm2 := rat_div' (rat_add' (encSepMidState_m_polyTime hst) (encSepMidState_b_polyTime hst))
      (const (2 : ℚ))
    have hc1 := unary_beq (sturmVariationsList_computableInPolyTime.comp (hpar.fst'.prod hm1))
      hpar.snd'
    have hc2 := unary_beq (sturmVariationsList_computableInPolyTime.comp (hpar.fst'.prod hm2))
      hpar.snd'
    exact (encSepMidState_done_polyTime hst).ite hst
      (hc1.ite_decide
        (encSepMidState_mk_polyTime (const true) hm1
          (encSepMidState_m_polyTime hst) (encSepMidState_m_polyTime hst))
        (hc2.ite_decide
          (encSepMidState_mk_polyTime (const true)
            (encSepMidState_m_polyTime hst) (encSepMidState_m_polyTime hst) hm2)
          (encSepMidState_mk_polyTime (const false) hm1 (encSepMidState_m_polyTime hst) hm2)))
  have hpar := (encSepMidArgs_seq_polyTime id').prod (encSepMidArgs_vm_polyTime id')
  have hinit := encSepMidState_mk_polyTime (const false)
    (encSepMidArgs_a_polyTime id') (encSepMidArgs_m_polyTime id') (encSepMidArgs_b_polyTime id')
  have hiter := iterateWith hpar (encSepMidArgs_fuel_polyTime id') hinit hstep
    (bound := fun x => 150 * ((encSepMidArgs x).length + 1))
    (PolyBounded.of_forall_le 150 1 fun _ => by simp only [pow_one, le_refl])
    fun x i hi => by
      set L := (encSepMidArgs x).length
      have hLf : x.fuel ≤ L := by
        simpa only [encUnary_apply, List.length_replicate] using encSepMidArgs_fuel_length_le x
      obtain ⟨ha_num, ha_den⟩ := num_den_le_of_length_encRat_le (encSepMidArgs_a_length_le x)
      obtain ⟨hm_num, hm_den⟩ := num_den_le_of_length_encRat_le (encSepMidArgs_m_length_le x)
      obtain ⟨hb_num, hb_den⟩ := num_den_le_of_length_encRat_le (encSepMidArgs_b_length_le x)
      let D := x.a.den * x.m.den * x.b.den
      let M := max (x.a.num.natAbs * x.m.den * x.b.den)
        (max (x.m.num.natAbs * x.a.den * x.b.den) (x.b.num.natAbs * x.a.den * x.m.den))
      have hD1 : 1 ≤ D := Nat.mul_pos (Nat.mul_pos x.a.den_pos x.m.den_pos) x.b.den_pos
      have hpow : 2 ^ L * 2 ^ L * 2 ^ L * 2 ^ i ≤ 2 ^ (4 * L) := by
        rw [← pow_add, ← pow_add, ← pow_add]; exact Nat.pow_le_pow_right zero_lt_two (by omega)
      have hD : D * 2 ^ i ≤ 2 ^ (4 * L) :=
        (Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul ha_den hm_den) hb_den)).trans hpow
      have hM : M * 2 ^ i ≤ 2 ^ (4 * L) := (Nat.mul_le_mul_right _
        (max_le (Nat.mul_le_mul (Nat.mul_le_mul ha_num hm_den) hb_den)
          (max_le (Nat.mul_le_mul (Nat.mul_le_mul hm_num ha_den) hb_den)
            (Nat.mul_le_mul (Nat.mul_le_mul hb_num ha_den) hm_den)))).trans hpow
      have htrace : ∀ j : ℕ,
          let st := (sepMidIterStep (x.seq, x.vm))^[j]
            { done := false, a := x.a, m := x.m, b := x.b }
          ScaledDyadic D M j st.a ∧ ScaledDyadic D M j st.m ∧ ScaledDyadic D M j st.b :=
          fun j => by
        induction j with
        | zero =>
          simp only [Function.iterate_zero, id_eq]
          refine ⟨.zero (Nat.mul_pos x.m.den_pos x.b.den_pos) (Nat.mul_assoc _ _ _) ?_,
            .zero (Nat.mul_pos x.a.den_pos x.b.den_pos) (by dsimp only [D]; ring) ?_,
            .zero (Nat.mul_pos x.a.den_pos x.m.den_pos) (by dsimp only [D]; ring) ?_⟩ <;>
            rw [← Nat.mul_assoc]
          · exact le_max_left _ _
          · exact (le_max_left _ _).trans (le_max_right _ _)
          · exact (le_max_right _ _).trans (le_max_right _ _)
        | succ j ih =>
          rw [Function.iterate_succ_apply']
          exact sepMidIterStep_dyadic hD1 ih.1 ih.2.1 ih.2.2
      obtain ⟨ha, hm, hb⟩ := htrace i
      have ha_enc := ha.length_encRat_le hD1 hD hM
      have hm_enc := hm.length_encRat_le hD1 hD hM
      have hb_enc := hb.length_encRat_le hD1 hD hM
      rw [encSepMidState_apply]
      dsimp only [encSepMidStateFields]
      rw [length_encPair, length_encPair, length_encPair, encBool_apply, List.length_singleton]
      dsimp only
      omega
  have hout := (encSepMidState_a_polyTime hiter).prod (encSepMidState_b_polyTime hiter)
  exact hout.of_enc_eq fun x => congrArg (encPair encRat encRat)
    (sepMidIterStep_eq_separateMidLoop x.seq x.vm x.fuel x.a x.m x.b).symm

private structure SepPairArgs where
  t : List ℚ
  seq : List (List ℚ)
  depth : ℕ
  I₁ : RootInterval
  I₂ : RootInterval

private enc_structure encSepPairArgs : SepPairArgs where
  t : encRatPoly,
  seq : encSturmSeq,
  depth : encUnary,
  I₁ : encRootInterval,
  I₂ : encRootInterval

private theorem separatePair_polyTime :
    ComputableInPolyTime
      (fun a : SepPairArgs => separatePair a.t a.seq a.depth a.I₁ a.I₂)
      encSepPairArgs (encPair encRat encRat) := by
  have hl1 := encRootInterval_lower_polyTime (encSepPairArgs_I₁_polyTime id')
  have hu1 := encRootInterval_upper_polyTime (encSepPairArgs_I₁_polyTime id')
  have hl2 := encRootInterval_lower_polyTime (encSepPairArgs_I₂_polyTime id')
  have hu2 := encRootInterval_upper_polyTime (encSepPairArgs_I₂_polyTime id')
  have hc1 := rat_lt' hu1 hl2
  have hc2 := rat_isZero'
    (evalCoeffList_computableInPolyTime.comp (hl1.prod (encSepPairArgs_t_polyTime id')))
  have hvm := sturmVariationsList_computableInPolyTime.comp
    ((encSepPairArgs_seq_polyTime id').prod hu1)
  have hmid_args := encSepMidArgs_mk_polyTime
    (encSepPairArgs_seq_polyTime id') (encSepPairArgs_depth_polyTime id')
    hl1 hu1 hu2 hvm
  have hraw := hc1.ite_decide (hu1.prod hl2)
    (hc2.ite_decide (hl1.prod hl2) (separateMidLoop_polyTime.comp hmid_args))
  exact hraw.of_enc_eq fun _ => rfl

private theorem getLastD_cons_eq_of_ne_nil {α : Type*} (x : α) {xs : List α}
    (hne : xs ≠ []) (d₁ d₂ : α) :
    (x :: xs).getLastD d₁ = xs.getLastD d₂ := by
  rw [List.getLastD_eq_getLast?, List.getLastD_eq_getLast?, List.getLast?_cons_of_ne_nil hne,
    List.getLast?_eq_some_getLast hne, Option.getD_some, Option.getD_some]

private theorem separateChain_eq_zip (t : List ℚ) (seq : List (List ℚ)) (depth : ℕ) :
    ∀ (rest : List RootInterval) (I₀ : RootInterval) (curLower : ℚ),
      separateChain t seq depth curLower (I₀ :: rest) =
        let pairs := ((I₀ :: rest).zip rest).map fun pq => separatePair t seq depth pq.1 pq.2
        let lowers := curLower :: pairs.map Prod.snd
        let uppers := pairs.map Prod.fst ++ [((I₀ :: rest).getLastD I₀).upper]
        (lowers.zip uppers).map fun lu => { lower := lu.1, upper := lu.2 }
  | [], I₀, curLower => by simp [separateChain]
  | I₁ :: rest', I₀, curLower => by
    have hlast : (I₀ :: I₁ :: rest').getLastD I₀ = (I₁ :: rest').getLastD I₁ :=
      getLastD_cons_eq_of_ne_nil I₀ (List.cons_ne_nil I₁ rest') I₀ I₁
    simp only [separateChain, List.zip_cons_cons, List.map_cons, List.cons_append, hlast,
      separateChain_eq_zip t seq depth rest' I₁]

private theorem separateTouching_eq_zip (t : List ℚ) (seq : List (List ℚ)) (depth : ℕ)
    (L : List RootInterval) :
    separateTouching t seq depth L =
      if L.isEmpty then []
      else
        let defaultI : RootInterval := { lower := 0, upper := 0 }
        let I₀ := L.headD defaultI
        let pairs := (L.zip L.tail).map fun pq => separatePair t seq depth pq.1 pq.2
        let lowers := I₀.lower :: pairs.map Prod.snd
        let uppers := pairs.map Prod.fst ++ [(L.reverse.headD defaultI).upper]
        (lowers.zip uppers).map fun lu => { lower := lu.1, upper := lu.2 } := by
  cases L with
  | nil => rfl
  | cons I₀ rest =>
    have hlast : ((I₀ :: rest).reverse.headD { lower := 0, upper := 0 }) =
        (I₀ :: rest).getLastD I₀ := by
      rw [← getLastD_eq_reverse_headD, List.getLastD_eq_getLast?, List.getLastD_eq_getLast?,
        List.getLast?_eq_some_getLast (List.cons_ne_nil I₀ rest), Option.getD_some,
        Option.getD_some]
    simp only [separateTouching, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
      List.headD_cons, List.tail_cons, hlast, separateChain_eq_zip]

private structure SepTouchingArgs where
  t : List ℚ
  seq : List (List ℚ)
  depth : ℕ
  L : List RootInterval

private enc_structure encSepTouchingArgs : SepTouchingArgs where
  t : encRatPoly,
  seq : encSturmSeq,
  depth : encUnary,
  L : encRootIntervals

private theorem separateTouching_polyTime :
    ComputableInPolyTime
      (fun a : SepTouchingArgs => separateTouching a.t a.seq a.depth a.L)
      encSepTouchingArgs encRootIntervals := by
  have ht := encSepTouchingArgs_t_polyTime id'
  have hseq := encSepTouchingArgs_seq_polyTime id'
  have hdepth := encSepTouchingArgs_depth_polyTime id'
  have hL := encSepTouchingArgs_L_polyTime id'
  let defI : RootInterval := { lower := 0, upper := 0 }
  have hpar := ht.prod (hseq.prod hdepth)
  have hzip := (zip encRootInterval encRootInterval).comp
    (hL.prod ((listTail encRootInterval).comp hL))
  have hp := fst (encPair encRatPoly (encPair encSturmSeq encUnary))
    (encPair encRootInterval encRootInterval)
  have hq := snd (encPair encRatPoly (encPair encSturmSeq encUnary))
    (encPair encRootInterval encRootInterval)
  have hmk := encSepPairArgs_mk_polyTime hp.fst' hp.snd'.fst' hp.snd'.snd' hq.fst' hq.snd'
  have hf := separatePair_polyTime.comp hmk
  have hpairs := mapWith hf hpar hzip
  have hI0 := (headD (encA := encRootInterval) defI).comp hL
  have hIlast := (headD (encA := encRootInterval) defI).comp
    ((listReverse encRootInterval).comp hL)
  have hlowers := (cons encRat).comp
    ((encRootInterval_lower_polyTime hI0).prod
      (mapWith ((snd encRat encRat).comp (snd encBool (encPair encRat encRat)))
        (const false) hpairs))
  have huppers := (listAppend encRat).comp
    ((mapWith ((fst encRat encRat).comp (snd encBool (encPair encRat encRat)))
        (const false) hpairs).prod
      ((cons encRat).comp ((encRootInterval_upper_polyTime hIlast).prod (const []))))
  have hsep_nonempty := mapWith
    (encRootInterval_mk_polyTime
      ((fst encRat encRat).comp (snd encBool (encPair encRat encRat)))
      ((snd encRat encRat).comp (snd encBool (encPair encRat encRat))))
    (const false) ((zip encRat encRat).comp (hlowers.prod huppers))
  have hraw := ((listIsEmpty' encRootInterval).comp hL).ite (const []) hsep_nonempty
  refine hraw.of_enc_eq fun a => congrArg encRootIntervals ?_
  rw [separateTouching_eq_zip]
  simp only [Function.comp_apply]
  set pairs := (a.L.zip a.L.tail).map fun pq => separatePair a.t a.seq a.depth pq.1 pq.2
  rfl

/-- Certified Sturm-bisection real-root isolation `Cslib.RealRoot.isolateRootsTotal` (producing
pairwise disjoint closed rational intervals `J₁.upper < J₂.lower`) is computable in polynomial time
from `encRatPoly` to `encRootIntervals`. -/
@[fun_prop]
theorem isolateRootsTotal_computableInPolyTime :
    ComputableInPolyTime isolateRootsTotal encRatPoly encRootIntervals := by
  have hargs := encSepTouchingArgs_mk_polyTime
    trim_computableInPolyTime sturmSeqList_computableInPolyTime
    mignotteBisectionDepth_computableInPolyTime isolateRoots_computableInPolyTime
  refine (separateTouching_polyTime.comp hargs).of_enc_eq fun cs =>
    congrArg encRootIntervals ?_
  rw [isolateRootsTotal_eq_separateTouching]
  dsimp only [Function.comp_apply]

end Cslib.Complexity.RealAlgebraic
