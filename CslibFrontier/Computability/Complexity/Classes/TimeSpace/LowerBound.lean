/-
Copyright (c) 2026 Samuel Schlesinger, Vhalan Anandarajah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Vhalan Anandarajah
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.Basic
import CslibFrontier.Computability.Complexity.Classes.Hierarchy.NondeterministicPolynomial
import CslibFrontier.Computability.Complexity.Classes.Time.Verifier
import CslibFrontier.Computability.Complexity.Classes.TimeSpace.Slowdown
import CslibFrontier.Computability.Complexity.Classes.TimeSpace.Speedup
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.NatPolynomial
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.BinaryComparison
import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.BitLength
import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Input

/-!
# A time–space lower bound for nondeterministic linear time

Under a simulation in time exponent `p / q` and space exponent `r / q`, virtual padding to
length `O(n ^ a)` gives a deterministic run with time exponent `a * p / q` and space exponent
`a * r / q`. Its input consists of a framed instance and a suffix of ones. A symbol query scans
the framed prefix or computes the symbol from the query position and the binary padded length.

The two-quantifier speedup takes a square root of the time bound and charges the full
space bound for each simulated step. The slowdown charges the time exponent `p / q` a second
time. With `p ^ 2 + 2 * p * r < 2 * q ^ 2`, choosing a large integer padding degree absorbs the
lookup overhead and gives a strict decrease in nondeterministic time. This follows the
virtual-padding argument of [Arora and Barak, §5.4][AroraBarak09].

## Main results

* `Cslib.Complexity.not_NTIME_linear_subset_TISP`: the rational-exponent time–space separation,
  including the time exponent `6 / 5` and space exponent `1 / 5`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [L. Fortnow, *Time–space tradeoffs for satisfiability*][Fortnow2000]
* [L. Fortnow, R. Lipton, D. van Melkebeek, A. Viglas,
  *Time-space lower bounds for satisfiability*][FortnowLiptonVanMelkebeekViglas2005]
* [R. J. Lipton, A. Viglas, *On the complexity of SAT*][LiptonViglas1999]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM Turing.MultiTapeTM.Universal

private def paddedInput (c a : ℕ) (x : List Bool) : List Bool :=
  frame x ++ List.replicate ((2 * c + 1) * (x.length + 1) ^ a) true

private theorem paddedInput_length (c a : ℕ) (x : List Bool) :
    (paddedInput c a x).length = 2 * x.length + 1 + (2 * c + 1) * (x.length + 1) ^ a := by
  simp [paddedInput, length_frame]

private def paddedSymbol (c a : ℕ) (y : List Bool × ℕ) : Option ℕ :=
  if y.2 < 2 * y.1.length + 2 then inputSymbol ((frame y.1).map eBit) y.2
  else if y.2 < 2 * y.1.length + 2 + (2 * c + 1) * (y.1.length + 1) ^ a then some 1
  else none

private theorem paddedSymbol_eq (c a : ℕ) (x : List Bool) (j : ℕ) :
    paddedSymbol c a (x, j) = inputSymbol ((paddedInput c a x).map eBit) j := by
  unfold paddedSymbol paddedInput
  simp only [inputSymbol, List.map_append, List.map_replicate, List.drop_append, List.length_map,
    length_frame, List.drop_replicate]
  have hbit : eBit true = 1 := rfl
  by_cases hzero : j = 0
  · subst j
    simp
  · by_cases hframe : j < 2 * x.length + 2
    · have hne : (List.drop (j - 1) ((frame x).map eBit)).head?.isSome := by
        rw [List.isSome_head?, ← List.length_pos_iff, List.length_drop, List.length_map,
          length_frame]
        omega
      simp only [hframe, hzero, ↓reduceIte, List.head?_append]
      cases h : (List.drop (j - 1) ((frame x).map eBit)).head? <;> simp_all
    · have hnil : List.drop (j - 1) ((frame x).map eBit) = [] :=
        List.drop_eq_nil_of_le (by simp only [List.length_map, length_frame]; omega)
      simp only [hframe, hzero, ↓reduceIte, hnil, List.nil_append, List.head?_replicate, hbit]
      split_ifs <;> first | rfl | omega

private theorem cutoff_inO {f : ℕ → ℕ} (hf : ComputableInPolyTime f encNat encNat) :
    ComputableInO (fun y : List Bool × ℕ => decide (y.2 < f y.1.length))
      (encPair encBits encNat) encBool (fun y => (encPair encBits encNat y).length)
      (fun y => (encPair encBits encNat y).length) := by
  have hlength := ComputableInO.lengthNat.comp_linear (ComputableInO.fst encBits encNat)
  have h := (ComputableInO.of_linear ComputableInDegree.natLt).comp_linear
    ((ComputableInO.snd encBits encNat).prod (hf.nat_inO.comp hlength))
  refine h.mono 4 (fun y => ?_) (fun y => ?_)
  all_goals simp only [Function.comp_apply, length_encPair, encBits_apply]; omega

private def symbolBudget (y : List Bool × ℕ) : ℕ :=
  ((encPair encBits encNat y).length + 1) * ((encNat y.2).length + 1) ^ 2

private theorem paddedSymbol_inO (c a : ℕ) :
    ComputableInO (paddedSymbol c a) (encPair encBits encNat) eSym symbolBudget symbolBudget := by
  have hframe := cutoff_inO (f := fun n => 2 * n + 2) (by fun_prop)
  have hpow : ComputableInPolyTime (fun n : ℕ => (n + 1) ^ a) encNat encNat :=
    ComputableInPolyTime.binary_pow' (by fun_prop) (.const a)
  have htotal := cutoff_inO (f := fun n => 2 * n + 2 + (2 * c + 1) * (n + 1) ^ a) (by fun_prop)
  have hprefix := computableInO_map_eBit.comp_linear
    (ComputableInO.frame' (ComputableInO.fst encBits encNat))
  have hread := inputSymbol_stream_inO.comp
    (hprefix.prod (ComputableInO.snd encBits encNat))
  have h := hframe.ite hread
    (htotal.ite (ComputableInO.const (some 1)) (ComputableInO.const none))
  refine (h.mono 12 (fun y => ?_) (fun y => ?_)).of_enc_eq ?_
  · have hprefixLen := length_encList_map_eBit_le (frame y.1)
    rw [length_frame] at hprefixLen
    simp only [Function.comp_apply]
    unfold symbolBudget
    have hB := Nat.le_mul_of_pos_right ((encPair encBits encNat y).length + 1)
      (show 0 < ((encNat y.2).length + 1) ^ 2 by positivity)
    have hreadBound := Nat.mul_le_mul_right (((encNat y.2).length + 1) ^ 2)
      (show (encList encUnary ((frame y.1).map eBit)).length + 1 ≤
        4 * ((encPair encBits encNat y).length + 1) by
        simp only [length_encPair, encBits_apply]; omega)
    rw [Nat.mul_assoc] at hreadBound
    split_ifs <;> nlinarith
  · have hprefixLen := length_encList_map_eBit_le (frame y.1)
    rw [length_frame] at hprefixLen
    have hB := Nat.le_mul_of_pos_right ((encPair encBits encNat y).length + 1)
      (show 0 < ((encNat y.2).length + 1) ^ 2 by positivity)
    simp only [Function.comp_apply, length_encPair, encBits_apply] at hB ⊢
    unfold symbolBudget
    simp only [length_encPair, encBits_apply]
    split_ifs <;> omega
  · intro y
    simp only [paddedSymbol, decide_eq_true_eq, Function.comp_apply]

private theorem exists_size_sq_bound (K a : ℕ) :
    ∃ D, ∀ n v, v ≤ K * (n + 1) ^ a → (v.size + 1) ^ 2 ≤ D * (n + 1) := by
  obtain ⟨D, hD⟩ := exists_pow_length_encNat_le 2
  refine ⟨(K.size + 2 * a + 2) ^ 2 * D, fun n v hv => ?_⟩
  have hv' := length_encNat_le_of_le_mul_pow hv
  rw [length_encNat_eq_size] at hv'
  have hlen : v.size + 1 ≤ (K.size + 2 * a + 2) * (n.size + 1) := by
    nlinarith [Nat.log2_le_size n, Nat.mul_le_mul_left (K.size + 2 * a + 1) (Nat.log2_le_size n)]
  calc
    _ ≤ ((K.size + 2 * a + 2) * (n.size + 1)) ^ 2 := Nat.pow_le_pow_left hlen 2
    _ ≤ _ := by
      rw [mul_pow, Nat.mul_assoc]
      apply Nat.mul_le_mul_left
      simpa only [length_encNat_eq_size] using hD n

private theorem charge_clock {q p u K a n N C v : ℕ} (hq : 0 < q) (he : a * p = u * q)
    (hN : N + 1 ≤ K * (n + 1) ^ a) (hv : v ^ q ≤ C * (N + 1) ^ p) (c : ℕ) :
    c * (v + 1) ≤ c * (C * K ^ p + 2) * (n + 1) ^ u := by
  let M := C * K ^ p + 1
  have hb : v ≤ M * (n + 1) ^ u := by
    apply (Nat.pow_le_pow_iff_left hq.ne').mp
    calc
      v ^ q ≤ C * (N + 1) ^ p := hv
      _ ≤ C * (K * (n + 1) ^ a) ^ p := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hN _)
      _ = C * K ^ p * (n + 1) ^ (u * q) := by rw [mul_pow, ← pow_mul, he, Nat.mul_assoc]
      _ ≤ M ^ q * (n + 1) ^ (u * q) :=
        Nat.mul_le_mul_right _ ((Nat.le_succ _).trans (Nat.le_self_pow hq.ne' M))
      _ = (M * (n + 1) ^ u) ^ q := by rw [mul_pow, ← pow_mul]
  have hpos : 1 ≤ (n + 1) ^ u := Nat.one_le_pow _ _ (Nat.succ_pos n)
  rw [Nat.mul_assoc]
  refine Nat.mul_le_mul_left _ ?_
  dsimp [M] at hb
  linarith [Nat.add_mul (C * K ^ p + 1) 1 ((n + 1) ^ u)]

private theorem paddedInput_length_le {c a : ℕ} (ha : 0 < a) (x : List Bool) :
    (paddedInput c a x).length + 1 ≤ (2 * c + 3) * (x.length + 1) ^ a := by
  rw [paddedInput_length]
  nlinarith [Nat.le_self_pow ha.ne' (x.length + 1)]

private theorem symbolBudget_le {a : ℕ} (c : ℕ) (ha : 0 < a) :
    ∃ G, ∀ (x : List Bool) j, j ≤ (paddedInput c a x).length + 1 →
      symbolBudget (x, j) ≤ G * (x.length + 1) ^ 2 := by
  obtain ⟨G, hG⟩ := exists_size_sq_bound (2 * c + 3) a
  refine ⟨(G + 2) * G, fun x j hj => ?_⟩
  have hs := hG x.length j (hj.trans (paddedInput_length_le ha x))
  have hlen : (encPair encBits encNat (x, j)).length + 1 ≤ (G + 2) * (x.length + 1) := by
    simp only [length_encPair, encBits_apply, length_encNat_eq_size]
    nlinarith [Nat.le_self_pow two_ne_zero (j.size + 1)]
  simp only [symbolBudget, length_encNat_eq_size]
  exact (Nat.mul_le_mul hlen hs).trans_eq (by ring)

private theorem pad_and_speedup {t s : ℕ → ℕ} {p q r Ct Cs : ℕ} (hq : 0 < q)
    (ht : ∀ n, t n ^ q ≤ Ct * (n + 1) ^ p) (hs : ∀ n, s n ^ q ≤ Cs * (n + 1) ^ r)
    (simulates : NTIME encBits id ⊆ TISP encBits t s) {m : ℕ} (hm : 0 < m) :
    NTIME encBits (fun n => (n + 1) ^ (2 * q * m)) ⊆
      SigmaTwoTIME encBits (fun n => (n + 1) ^ (m * p + 2 * m * r + 2)) := by
  intro A hA
  let a := 2 * q * m
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨V, c, hV, hc⟩ := exists_verifier_of_mem_NTIME hA
  let B : Set (List Bool) := {z | ∃ w : List Bool, w.length = z.length ∧ V (unframe z, w) = true}
  have hB : B ∈ NTIME encBits id := by
    have hVp := hV.comp_linear
      ((ComputableInO.unframe' (ComputableInO.fst encBits encBits)).prod
        (ComputableInO.snd encBits encBits))
    exact setOf_exists_mem_NTIME (C := 10) ComputableInO.lengthUnary hVp fun z w hw => by
      simp only [encBits_apply, length_encPair, id_eq]
      omega
  let input := paddedInput c a
  have hmem (x : List Bool) : x ∈ A ↔ input x ∈ B := by
    change x ∈ A ↔ ∃ w : List Bool, w.length = (input x).length ∧ V (unframe (input x), w) = true
    rw [show unframe (input x) = x from unframe_frame_append ..]
    apply hc
    simp only [encBits_apply, input, paddedInput_length, a]
    have hpow : 1 ≤ (x.length + 1) ^ (2 * q * m) :=
      Nat.one_le_pow _ _ (Nat.succ_pos x.length)
    nlinarith [Nat.mul_le_mul_left c hpow]
  have hAeq : A = {x | indicator B (input x) = true} := by
    ext x
    exact (hmem x).trans (indicator_eq_iff.mp rfl (input x))
  obtain ⟨c', ⟨k, State, hfin, M, hM⟩, -⟩ := mem_TISP_iff_computableInO.mp (simulates hB)
  let T (x : List Bool) := c' * (t (input x).length + 1)
  let S (x : List Bool) := c' * (s (input x).length + 1)
  have hrun (x : List Bool) : M.ComputesInTimeAndSpace (input x)
      [indicator B (input x)] (T x) (S x) := by
    simpa only [encBits_apply, encBool_apply, T, S] using hM (input x)
  have hN (x : List Bool) := paddedInput_length_le (c := c) ha x
  let Kt := c' * (Ct * (2 * c + 3) ^ p + 2)
  let Ks := c' * (Cs * (2 * c + 3) ^ r + 2)
  have hT (x : List Bool) : T x ≤ Kt * (x.length + 1) ^ (2 * (m * p)) :=
    charge_clock hq (by dsimp [a]; ring) (hN x) (ht _) c'
  have hS (x : List Bool) : S x ≤ Ks * (x.length + 1) ^ (2 * m * r) :=
    charge_clock hq (by dsimp [a]; ring) (hN x) (hs _) c'
  obtain ⟨G, hG⟩ := symbolBudget_le c ha
  obtain ⟨DN, hDN⟩ := exists_size_sq_bound (2 * c + 3) a
  obtain ⟨DT, hDT⟩ := exists_size_sq_bound Kt (2 * (m * p))
  rw [hAeq]
  refine mem_SigmaTwoTIME_of_virtualRun (ι := input) (T := T) (S := S)
    hrun (ComputableInO.of_eq (f := id) (encMid := encBits) fun _ => rfl)
    (paddedSymbol_inO c a) (fun x j _ => paddedSymbol_eq c a x j)
    (L := fun x => 2 * G * (x.length + 1) ^ 2) (fun x j hj => ?_) ?_
  · have h := hG x j hj
    exact (Nat.add_le_add h h).trans_eq (by ring)
  · let K := Ks + 1 + 2 * G + DN + DT
    refine ⟨(Kt + 1) * K, fun x => ?_⟩
    let N := x.length + 1
    let U := N ^ (m * p)
    let W := N ^ (2 * m * r + 2)
    have hflat : 1 ≤ U := Nat.one_le_pow _ _ (Nat.succ_pos x.length)
    have hroot : (T x).sqrt + 1 ≤ (Kt + 1) * U := by
      have ht' : T x ≤ (Kt * U) ^ 2 := by
        rw [mul_pow, ← pow_mul, Nat.mul_comm (m * p) 2]
        exact (hT x).trans (Nat.mul_le_mul_right _ (Nat.le_self_pow two_ne_zero Kt))
      have hsqrt := Nat.sqrt_le_sqrt ht'
      rw [Nat.sqrt_eq'] at hsqrt
      nlinarith
    have hW (d : ℕ) (hd : d ≤ 2 * m * r + 2) : N ^ d ≤ W :=
      Nat.pow_le_pow_right (Nat.succ_pos x.length) hd
    have hw1 : N ≤ W := (pow_one N).symm ▸ hW 1 (by omega)
    have hw2 := hW 2 (by omega)
    have hspace := (hS x).trans (Nat.mul_le_mul_left Ks (hW (2 * m * r) (by omega)))
    have hlen := (hDN x.length (input x).length ((Nat.le_succ _).trans (hN x))).trans
      (Nat.mul_le_mul_left DN hw1)
    have htlen := (hDT x.length (T x) (hT x)).trans (Nat.mul_le_mul_left DT hw1)
    have hlook := Nat.mul_le_mul_left (2 * G) hw2
    have hsum : S x + x.length + 2 * G * N ^ 2 + ((input x).length.size + 1) ^ 2 +
        ((T x).size + 1) ^ 2 ≤ K * W := by
      dsimp [K]
      nlinarith [show x.length ≤ W from (Nat.le_succ x.length).trans hw1]
    simp only [encBits_apply, id_eq]
    calc
      _ ≤ ((Kt + 1) * U) * (K * W) := Nat.mul_le_mul hroot hsum
      _ = ((Kt + 1) * K) * N ^ (m * p + 2 * m * r + 2) := by
        dsimp [U, W]
        rw [Nat.add_assoc, pow_add]
        ring
      _ ≤ _ := Nat.le_add_right _ _

/-- **Time–space lower bound for nondeterministic linear time.** For positive `q ≤ p`, if
`p ^ 2 + 2 * p * r < 2 * q ^ 2`, then deterministic multitape machines with time
`O(n ^ (p / q))` and work space `O(n ^ (r / q))` cannot simulate all nondeterministic linear-time
languages. The rational exponents are expressed as inequalities between natural powers. -/
theorem not_NTIME_linear_subset_TISP {t s : ℕ → ℕ} {p q r Ct Cs : ℕ}
    (hq : 0 < q) (hqp : q ≤ p) (hgap : p ^ 2 + 2 * p * r < 2 * q ^ 2)
    (ht : ∀ n, t n ^ q ≤ Ct * (n + 1) ^ p) (hs : ∀ n, s n ^ q ≤ Cs * (n + 1) ^ r) :
    ¬ NTIME encBits id ⊆ TISP encBits t s := by
  intro simulates
  let k := 2 * p + 1
  let e := (p + 2 * r) * k + 2
  have he : 0 < e := by dsimp [e]; omega
  have hp : 0 < p := hq.trans_le hqp
  have hqe : 1 ≤ q * e := Nat.mul_pos hq he
  have hpe : 1 ≤ p * e := Nat.mul_pos hp he
  have hmul := Nat.mul_le_mul_right k (show p * (p + 2 * r) + 1 ≤ 2 * q ^ 2 by nlinarith)
  have hlt : p * e < 2 * q * (q * k) := by
    dsimp [e, k] at hmul ⊢
    nlinarith
  have hspeed := pad_and_speedup hq ht hs simulates (m := q * k)
    (Nat.mul_pos hq (by dsimp [k]; omega))
  have hround : q * k * p + 2 * (q * k) * r + 2 ≤ q * e := by
    dsimp [e]
    nlinarith
  have hslow := SigmaTwoTIME_succ_pow_subset_NTIME_succ_pow
    (simulates.trans TISP_subset_DTIME) ht hq hqe (Nat.mul_le_mul_right e hqp)
    (show q * e * p ≤ p * e * q from le_of_eq (by ring))
  have hmono := SigmaTwoTIME_mono (enc := encBits) fun n =>
    Nat.pow_le_pow_right (Nat.succ_pos n) hround
  exact (NTIME_succ_pow_ssubset_NTIME_succ_pow hpe hlt).not_superset
    (hspeed.trans (Set.Subset.trans hmono hslow))

end Cslib.Complexity
