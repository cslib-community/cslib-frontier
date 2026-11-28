/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.AffineDisperser.Li.Berlekamp
public import CslibFrontier.Computability.Complexity.AffineDisperser.Li.ShoupIrreducible
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString.Dot
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Max
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.PowMod
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Prime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Complexity.AffineDisperser.PolyTime

/-!
# Polynomial-Time Certificates for Shoup's Irreducible Polynomial Construction

This module certifies `Turing.MultiTapeTM.ComputableInPolyTime` for the arithmetic, polynomial,
Berlekamp factoring, and Shoup construction algorithms in
`CslibFrontier.Computability.Complexity.AffineDisperser.Li.Berlekamp` and
`CslibFrontier.Computability.Complexity.AffineDisperser.Li.ShoupIrreducible`.

## Main results

* `Cslib.AffineDisperser.Li.computableInPolyTime_primeDeg`: `primeDeg` is computable in
  polynomial time on unary inputs.
* `Cslib.AffineDisperser.Li.computableInPolyTime_shoupIrreducibleBits`: `shoupIrreducibleBits` is
  computable in polynomial time from unary `q` to bit-list coefficients.

## References

* [V. Shoup, *New algorithms for finding irreducible polynomials over finite fields*][Shoup1990]
-/

public section

namespace Cslib.AffineDisperser.Li

open Turing.MultiTapeTM ComputableInPolyTime
open Cslib.BitString (listDot)

attribute [local irreducible] ComputableInPolyTime

/-! ### Local `fun_prop` and size-bound helpers -/

@[local fun_prop]
private theorem polyTime_xor {α : Type} {enc : α ↪ List Bool} {a b : α → Bool}
    (ha : ComputableInPolyTime a enc encBool) (hb : ComputableInPolyTime b enc encBool) :
    ComputableInPolyTime (fun x => a x ^^ b x) enc encBool :=
  (of_finite (fun p : Bool × Bool => p.1 ^^ p.2)
    (encIn := encPair encBool encBool) (encOut := encBool)).comp (ha.prod hb)

@[local fun_prop]
private theorem polyTime_bitsIsEmpty {α : Type} {enc : α ↪ List Bool} {l : α → List Bool}
    (hl : ComputableInPolyTime l enc encBits) :
    ComputableInPolyTime (fun x => (l x).isEmpty) enc encBool :=
  bitsIsEmpty.comp hl

@[local fun_prop]
private theorem polyTime_listGetD_bits {α : Type} {enc : α ↪ List Bool}
    {l : α → List (List Bool)} {i : α → ℕ}
    (hl : ComputableInPolyTime l enc (encList encBits))
    (hi : ComputableInPolyTime i enc encUnary) :
    ComputableInPolyTime (fun x => (l x).getD (i x) []) enc encBits :=
  listGetDWithInput hl hi []

@[local fun_prop]
private theorem polyTime_listEncBitsLength {α : Type} {enc : α ↪ List Bool}
    {l : α → List (List Bool)} (hl : ComputableInPolyTime l enc (encList encBits)) :
    ComputableInPolyTime (fun x => (encList encBits (l x)).length) enc encUnary :=
  length_bits.comp (encoding_comp hl)

private theorem length_encList_bits_le {L : List (List Bool)} {n m : ℕ}
    (hl : L.length ≤ n) (hb : ∀ v ∈ L, v.length ≤ m) :
    (encList encBits L).length ≤ n * (2 * m + 1) :=
  (length_encList_le encBits L (b := m) (fun v hv => by
    simpa only [encBits_apply] using hb v hv)).trans (Nat.mul_le_mul_right _ hl)

private theorem isEmpty_polyTrim_false_of_lt_ite {f : List Bool} {k n : ℕ}
    (hk : k < if (polyTrim f).isEmpty then 0 else n) :
    (polyTrim f).isEmpty = false := by
  cases h : (polyTrim f).isEmpty
  · rfl
  · simp [h] at hk

private theorem foldl_range_const_eq {α : Type*} (step : α → α) (init : α) (n : ℕ) :
    (List.range n).foldl (fun x _ => step x) init = step^[n] init := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih,
      Function.iterate_succ_apply']

private theorem getD_length_le_of_forall {L : List (List Bool)} {m : ℕ}
    (hL : ∀ v ∈ L, v.length ≤ m) (i : ℕ) : (L.getD i []).length ≤ m := by
  rw [List.getD_eq_getElem?_getD]
  cases h : L[i]? with
  | none => simp
  | some u => exact hL u (List.mem_of_getElem? h)

private theorem getD_length_le_encList_bits (L : List (List Bool)) (i : ℕ) :
    (L.getD i []).length ≤ (encList encBits L).length :=
  getD_length_le_of_forall (fun _ hv => by
    simpa only [encBits_apply] using length_le_encList_of_mem encBits hv) i

/-! ### Unary parameter selection (`fifthRoot`, `primeThresholdBound`, `primeDeg`) -/

/-- `fifthRoot` is computable in polynomial time on unary naturals. -/
@[fun_prop]
theorem computableInPolyTime_fifthRoot :
    ComputableInPolyTime fifthRoot encUnary encUnary := by
  unfold fifthRoot
  refine countPWithInput (encA := encUnary) range ?_
  have heq : (fun p : ℕ × ℕ => decide ((p.2 + 1) ^ 5 ≤ p.1)) =
      fun p => decide ((p.2 + 1) * (p.2 + 1) * (p.2 + 1) * (p.2 + 1) * (p.2 + 1) ≤ p.1) := by
    funext p; rw [show (p.2 + 1) ^ 5 =
      (p.2 + 1) * (p.2 + 1) * (p.2 + 1) * (p.2 + 1) * (p.2 + 1) by ring]
  rw [heq]; fun_prop

/-- `primeThresholdBound` is computable in polynomial time on unary naturals. -/
@[fun_prop]
theorem computableInPolyTime_primeThresholdBound :
    ComputableInPolyTime primeThresholdBound encUnary encUnary := by
  unfold primeThresholdBound; fun_prop

/-- `primeDeg` is computable in polynomial time on unary naturals. -/
@[fun_prop]
theorem computableInPolyTime_primeDeg :
    ComputableInPolyTime primeDeg encUnary encUnary := by
  exact optionGetDWithInput (findWithInput
    (mapWithInput (f := fun N i => primeThresholdBound N + 1 + i) (by fun_prop) (by fun_prop))
    ((by fun_prop : ComputableInPolyTime (fun b : ℕ => decide b.Prime) encUnary encBool).comp
      (snd encUnary encUnary))) (by fun_prop)

/-- `ordTwoMod` is computable in polynomial time on unary naturals. -/
theorem computableInPolyTime_ordTwoMod :
    ComputableInPolyTime ordTwoMod encUnary encUnary := by
  have hmod : ComputableInPolyTime (fun p : ℕ × ℕ => 2 ^ (p.2 + 1) % p.1)
      (encPair encUnary encUnary) encNat :=
    binary_mod' (binary_two_pow.comp (by fun_prop)) (by fun_prop)
  have hf : ComputableInPolyTime
      (fun q : ℕ => (List.range (q - 1)).find? fun i => 2 ^ (i + 1) % q == 1)
      encUnary (encOption encUnary) :=
    findWithInput (range.comp (by fun_prop)) (hmod.beq (.const 1))
  convert optionElimWithInput (body := fun _ x : ℕ => x + 1) hf (.const 0) (by fun_prop) using 1
  funext q
  unfold ordTwoMod
  cases (List.find? (fun i => 2 ^ (i + 1) % q == 1) (List.range (q - 1))) <;> rfl

/-- `qAdicValTwoPowSubOne` is computable in polynomial time on unary naturals. -/
theorem computableInPolyTime_qAdicValTwoPowSubOne :
    ComputableInPolyTime (fun p : ℕ × ℕ => qAdicValTwoPowSubOne p.1 p.2)
      (encPair encUnary encUnary) encUnary := by
  have hmod : ComputableInPolyTime
      (fun p : (ℕ × ℕ) × ℕ => 2 ^ p.1.2 % p.1.1 ^ (p.2 + 1))
      (encPair (encPair encUnary encUnary) encUnary) encNat :=
    binary_mod' (binary_two_pow.comp (by fun_prop))
      (binary_pow' (by fun_prop) (by fun_prop))
  refine countPWithInput (encA := encUnary) (by fun_prop) ?_
  convert hmod.beq (.const 1) using 1
  funext p; cases (2 ^ p.1.2 % p.1.1 ^ (p.2 + 1) == 1) <;> rfl

/-! ### Binary polynomial arithmetic (`polyTrim`, `polyAdd`, `polyMul`, `polyDivMod`, `polyGcd`) -/

private def trimStep (st : ℕ × ℕ) (b : Bool) : ℕ × ℕ :=
  (st.1 + 1, if b then st.1 + 1 else st.2)

private theorem foldl_trimStep_bounds (p : List Bool) (i a : ℕ) (ha : a ≤ i) :
    (p.foldl trimStep (i, a)).1 = i + p.length ∧
      (p.foldl trimStep (i, a)).2 ≤ i + p.length := by
  induction p generalizing i a with
  | nil => simpa using ha
  | cons b p ih =>
    rw [List.foldl_cons, List.length_cons]
    dsimp only [trimStep]
    have h := ih (i + 1) (if b then i + 1 else a)
      (by cases b <;> [exact Nat.le_succ_of_le ha; exact le_rfl])
    exact ⟨by omega, by omega⟩

private theorem polyTrim_eq_take (p : List Bool) :
    polyTrim p = p.take (p.foldl trimStep (0, 0)).2 := by
  induction p using List.reverseRecOn with
  | nil => rfl
  | append_singleton p b ih =>
    have hb := foldl_trimStep_bounds p 0 0 le_rfl
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, trimStep, hb.1, Nat.zero_add]
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, polyTrim_append_false, ih]
      exact (List.take_append_of_le_length (by omega)).symm
    · simp only [↓reduceIte, polyTrim_append_true]
      simpa only [List.length_append, List.length_singleton] using
        (List.take_length (l := p ++ [true])).symm

/-- `polyTrim` is computable in polynomial time on bit lists. -/
theorem computableInPolyTime_polyTrim : ComputableInPolyTime polyTrim encBits encBits := by
  have hstep : ComputableInPolyTime (fun p : (ℕ × ℕ) × Bool => trimStep p.1 p.2)
      (encPair (encPair encUnary encUnary) encBool) (encPair encUnary encUnary) := by
    unfold trimStep; fun_prop
  have hfold : ComputableInPolyTime (fun p : List Bool => p.foldl trimStep (0, 0))
      encBits (encPair encUnary encUnary) := by
    refine foldl' (encA := encBool) (encL := encBits) (encB := encPair encUnary encUnary)
      id' (.const (0, 0)) hstep
      (B := fun p : List Bool => (encPair encUnary encUnary (p.length, p.length)).length)
      (by fun_prop : ComputableInPolyTime (fun p : List Bool => (p.length, p.length))
        encBits (encPair encUnary encUnary)).polyBounded_length fun p i _ => ?_
    have hb := foldl_trimStep_bounds (p.take i) 0 0 le_rfl
    simp only [length_encPair, encUnary_apply, List.length_replicate, List.length_take,
      Nat.zero_add] at hb ⊢
    omega
  convert bitsTakeWithInput id' ((snd encUnary encUnary).comp hfold) using 1
  exact funext polyTrim_eq_take

@[local fun_prop]
private theorem polyTime_polyTrim' {α : Type} {enc : α ↪ List Bool} {f : α → List Bool}
    (hf : ComputableInPolyTime f enc encBits) :
    ComputableInPolyTime (fun x => polyTrim (f x)) enc encBits :=
  computableInPolyTime_polyTrim.comp hf

/-- `polyAdd` is computable in polynomial time. -/
theorem computableInPolyTime_polyAdd :
    ComputableInPolyTime (fun p : List Bool × List Bool => polyAdd p.1 p.2)
      (encPair encBits encBits) encBits := by
  exact computableInPolyTime_polyTrim.comp (listToBits.comp
    (mapWithInput (f := fun (p : List Bool × List Bool) i => p.1.getD i false ^^ p.2.getD i false)
      (by fun_prop) (by fun_prop)))

@[local fun_prop]
private theorem polyTime_polyAdd' {α : Type} {enc : α ↪ List Bool} {a b : α → List Bool}
    (ha : ComputableInPolyTime a enc encBits) (hb : ComputableInPolyTime b enc encBits) :
    ComputableInPolyTime (fun x => polyAdd (a x) (b x)) enc encBits :=
  computableInPolyTime_polyAdd.comp (ha.prod hb)

/-- `polyMul` is computable in polynomial time. -/
theorem computableInPolyTime_polyMul :
    ComputableInPolyTime (fun p : List Bool × List Bool => polyMul p.1 p.2)
      (encPair encBits encBits) encBits := by
  have hcoeff : ComputableInPolyTime
      (fun x : (List Bool × List Bool) × ℕ =>
        (List.range (x.2 + 1)).foldl
          (fun acc i => acc ^^ (x.1.1.getD i false && x.1.2.getD (x.2 - i) false)) false)
      (encPair (encPair encBits encBits) encUnary) encBool :=
    foldlWith (encA := encUnary) (encL := encList encUnary) (encB := encBool)
      (par := id) (list := fun x : (List Bool × List Bool) × ℕ => List.range (x.2 + 1))
      (step := fun (x : (List Bool × List Bool) × ℕ) (acc : Bool) (i : ℕ) =>
        acc ^^ (x.1.1.getD i false && x.1.2.getD (x.2 - i) false))
      id' (by fun_prop) (.const false) (by fun_prop)
      (B := fun _ => max (encBool false).length (encBool true).length)
      (.const _) fun _ _ _ => by cases (_ : List ℕ).foldl _ _ <;> simp
  have hmap : ComputableInPolyTime
      (fun p : List Bool × List Bool =>
        (List.range (p.1.length + p.2.length)).map fun k =>
          (List.range (k + 1)).foldl
            (fun acc i => acc ^^ (p.1.getD i false && p.2.getD (k - i) false)) false)
      (encPair encBits encBits) (encList encBool) :=
    mapWithInput (by fun_prop) hcoeff
  exact ite' (by fun_prop) (.const []) (computableInPolyTime_polyTrim.comp (listToBits.comp hmap))

@[local fun_prop]
private theorem polyTime_polyMul' {α : Type} {enc : α ↪ List Bool} {a b : α → List Bool}
    (ha : ComputableInPolyTime a enc encBits) (hb : ComputableInPolyTime b enc encBits) :
    ComputableInPolyTime (fun x => polyMul (a x) (b x)) enc encBits :=
  computableInPolyTime_polyMul.comp (ha.prod hb)

private theorem length_polyDivModStep_le (bt q r : List Bool) {n : ℕ}
    (hq : q.length ≤ n) (hr : r.length ≤ n) :
    (polyDivModStep bt (q, r)).1.length ≤ n ∧ (polyDivModStep bt (q, r)).2.length ≤ n := by
  unfold polyDivModStep; dsimp only
  have hr' : (polyTrim r).length ≤ n := (length_polyTrim_le r).trans hr
  split_ifs with h
  · exact ⟨(length_polyTrim_le q).trans hq, hr'⟩
  · have hbt_pos : 1 ≤ bt.length := by cases bt <;> simp_all
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt] at h
    exact ⟨(length_polyAdd_le _ _).trans (max_le hq (by simp; omega)),
      (length_polyAdd_le _ _).trans (max_le hr' (by simp; omega))⟩

private theorem polyTime_polyDivModStep :
    ComputableInPolyTime
      (fun p : List Bool × List Bool × List Bool => polyDivModStep p.1 p.2)
      (encPair encBits (encPair encBits encBits)) (encPair encBits encBits) := by
  unfold polyDivModStep
  have hrep : ComputableInPolyTime
      (fun p : List Bool × List Bool × List Bool =>
        List.replicate ((polyTrim p.2.2).length - p.1.length) false)
      (encPair encBits (encPair encBits encBits)) encBits :=
    (bitsReplicate false).comp (by fun_prop)
  exact ite' (by fun_prop) (by fun_prop)
    ((polyTime_polyAdd' (by fun_prop) (bitsAppend hrep (.const [true]))).prod
      (polyTime_polyAdd' (by fun_prop) (bitsAppend hrep (fst _ _))))

private theorem polyTime_polyDivMod :
    ComputableInPolyTime (fun p : List Bool × List Bool => polyDivMod p.1 p.2)
      (encPair encBits encBits) (encPair encBits encBits) :=
  (iterateWith_spec
    (invariant := fun p _ st => st.1.length ≤ p.1.length ∧ st.2.length ≤ p.1.length)
    (by fun_prop) (by fun_prop) (by fun_prop) polyTime_polyDivModStep
    (fun p => ⟨by simp, length_polyTrim_le p.1⟩)
    (fun _ _ _ _ hst => length_polyDivModStep_le _ _ _ hst.1 hst.2)
    (by fun_prop : ComputableInPolyTime (fun p : List Bool × List Bool => 3 * p.1.length + 1)
      (encPair encBits encBits) encUnary).polyBounded
    fun _ _ _ _ hst => by simp only [length_encPair, encBits_apply]; omega).1

/-- `polyMod` is computable in polynomial time. -/
theorem computableInPolyTime_polyMod :
    ComputableInPolyTime (fun p : List Bool × List Bool => polyMod p.1 p.2)
      (encPair encBits encBits) encBits :=
  (snd encBits encBits).comp polyTime_polyDivMod

@[local fun_prop]
private theorem polyTime_polyMod' {α : Type} {enc : α ↪ List Bool} {a b : α → List Bool}
    (ha : ComputableInPolyTime a enc encBits) (hb : ComputableInPolyTime b enc encBits) :
    ComputableInPolyTime (fun x => polyMod (a x) (b x)) enc encBits :=
  computableInPolyTime_polyMod.comp (ha.prod hb)

private theorem length_polyGcdStep_le (a b : List Bool) {n : ℕ}
    (ha : a.length ≤ n) (hb : b.length ≤ n) :
    (polyGcdStep (a, b)).1.length ≤ n ∧ (polyGcdStep (a, b)).2.length ≤ n := by
  unfold polyGcdStep; dsimp only; split_ifs
  · exact ⟨ha, hb⟩
  · exact ⟨hb, (length_polyMod_le a b).trans ha⟩

/-- `polyGcd` is computable in polynomial time. -/
theorem computableInPolyTime_polyGcd :
    ComputableInPolyTime (fun p : List Bool × List Bool => polyGcd p.1 p.2)
      (encPair encBits encBits) encBits := by
  have hstep : ComputableInPolyTime (fun x : Bool × List Bool × List Bool => polyGcdStep x.2)
      (encPair encBool (encPair encBits encBits)) (encPair encBits encBits) := by
    unfold polyGcdStep; fun_prop
  exact (fst encBits encBits).comp (iterateWith_spec
    (step := fun (_ : Bool) x => polyGcdStep x)
    (invariant := fun p _ st =>
      st.1.length ≤ max p.1.length p.2.length ∧ st.2.length ≤ max p.1.length p.2.length)
    (.const true) (by fun_prop) (by fun_prop) hstep
    (fun p => ⟨(length_polyTrim_le p.1).trans (le_max_left _ _),
      (length_polyTrim_le p.2).trans (le_max_right _ _)⟩)
    (fun _ _ _ _ hst => length_polyGcdStep_le _ _ hst.1 hst.2)
    (by fun_prop : ComputableInPolyTime
      (fun p : List Bool × List Bool => 3 * max p.1.length p.2.length + 1)
      (encPair encBits encBits) encUnary).polyBounded
    fun _ _ _ _ hst => by simp only [length_encPair, encBits_apply]; omega).1

/-- `polyComposePow` is computable in polynomial time. -/
theorem computableInPolyTime_polyComposePow :
    ComputableInPolyTime (fun p : ℕ × List Bool => polyComposePow p.1 p.2)
      (encPair encUnary encBits) encBits := by
  have hsum : ComputableInPolyTime
      (fun p : ℕ × List Bool => polyTrim [p.2.foldl xor false])
      (encPair encUnary encBits) encBits :=
    polyTime_polyTrim' ((of_finite (fun b : Bool => [b])).comp
      (bitsFoldlWithInput xor (snd encUnary encBits) (.const false)))
  have hnz : ComputableInPolyTime
      (fun p : ℕ × List Bool =>
        polyTrim ((List.range (p.1 * p.2.length)).map fun j =>
          if j % p.1 == 0 then p.2.getD (j / p.1) false else false))
      (encPair encUnary encBits) encBits :=
    computableInPolyTime_polyTrim.comp (listToBits.comp (mapWithInput (by fun_prop) (by fun_prop)))
  convert ite' (by fun_prop : ComputableInPolyTime (fun p : ℕ × List Bool => p.1 == 0)
      (encPair encUnary encBits) encBool) hsum hnz using 1
  funext p; unfold polyComposePow; simp

/-! ### Gaussian elimination and Berlekamp factoring -/

private theorem polyTime_kernelStepBits :
    ComputableInPolyTime (fun p : List (List Bool) × List Bool => kernelStepBits p.2 p.1)
      (encPair (encList encBits) encBits) (encList encBits) := by
  have hpIdx : ComputableInPolyTime
      (fun p : List (List Bool) × List Bool => (p.1.map (listDot p.2)).idxOf true)
      (encPair (encList encBits) encBits) encUnary :=
    idxOfWithInput (encA := encBool)
      (mapWithInput (f := fun (p : List (List Bool) × List Bool) v => listDot p.2 v)
        (by fun_prop) (by fun_prop)) (.const true)
  have hrow : ComputableInPolyTime
      (fun x : (List (List Bool) × List Bool) × List Bool =>
        if listDot x.1.2 x.2 then
          List.zipWith xor x.2 (x.1.1.getD ((x.1.1.map (listDot x.1.2)).idxOf true) [])
        else x.2)
      (encPair (encPair (encList encBits) encBits) encBits) encBits := by
    have hpiv := polyTime_listGetD_bits
      ((fst (encList encBits) encBits).comp (fst (encPair (encList encBits) encBits) encBits))
      (hpIdx.comp (fst _ _))
    exact ite' (by fun_prop) (bitsZipWithInput xor (snd _ _) hpiv) (snd _ _)
  convert ite' (unary_lt' hpIdx ((length_list encBits).comp (fst _ _)))
    (mapWithInput (f := fun par v =>
      if listDot par.2 v then
        List.zipWith xor v (par.1.getD ((par.1.map (listDot par.2)).idxOf true) [])
      else v) (fst (encList encBits) encBits) hrow)
    (fst (encList encBits) encBits) using 1
  funext p
  unfold kernelStepBits
  simp only [Function.comp_def, decide_eq_true_eq]

private theorem polyTime_kernelBasisBits :
    ComputableInPolyTime (fun p : ℕ × List (List Bool) => kernelBasisBits p.1 p.2)
      (encPair encUnary (encList encBits)) (encList encBits) := by
  refine foldlWith (encA := encBits) (encL := encList encBits) (encB := encList encBits)
    (par := fun _ => true) (list := Prod.snd) (step := fun _ N a => kernelStepBits a N)
    (.const true) (snd _ _) (bitsSingles.comp (fst _ _))
    (polyTime_kernelStepBits.comp
      (((snd encBool (encList encBits)).comp (fst _ _)).prod (snd _ _)))
    (by fun_prop : ComputableInPolyTime
      (fun p : ℕ × List (List Bool) => p.1 * (2 * p.1 + 1))
      (encPair encUnary (encList encBits)) encUnary).polyBounded
    fun p i _ => ?_
  obtain ⟨hlen, hrows⟩ := length_kernelBasisBits p.1 (p.2.take i)
  unfold kernelBasisBits at hlen hrows
  exact length_encList_bits_le (n := p.1) (m := p.1) hlen.le
    fun v hv => (hrows v hv).le

/-- `kernelVecBits` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_kernelVecBits :
    ComputableInPolyTime (fun p : ℕ × List (List Bool) => kernelVecBits p.1 p.2)
      (encPair encUnary (encList encBits)) encBits :=
  optionGetDWithInput
    (findWithInput (test := fun _ v => v.any id) polyTime_kernelBasisBits
      ((bitsAnyWithInput (test := fun _ b => b) id' (snd encBits encBool)).comp
        (snd (encPair encUnary (encList encBits)) encBits)))
    ((bitsReplicate false).comp (fst encUnary (encList encBits)))

private theorem polyTime_berlekampMatrix :
    ComputableInPolyTime berlekampMatrix encBits (encList encBits) := by
  have hrow : ComputableInPolyTime
      (fun x : List Bool × ℕ =>
        (List.range ((x.1.length - 1) - 1)).map fun k =>
          ((powerTable x.1).getD (2 * (k + 1)) []).getD x.2 false ^^ (x.2 == k + 1))
      (encPair encBits encUnary) encBits :=
    listToBits.comp (mapWithInput (range.comp (by fun_prop : ComputableInPolyTime
      (fun x : List Bool × ℕ => (x.1.length - 1) - 1) (encPair encBits encUnary) encUnary))
      (by fun_prop))
  convert mapWithInput (f := fun g i =>
      (List.range ((g.length - 1) - 1)).map fun k =>
        ((powerTable g).getD (2 * (k + 1)) []).getD i false ^^ (i == k + 1))
    (range.comp (by fun_prop : ComputableInPolyTime
      (fun g : List Bool => g.length - 1) encBits encUnary)) hrow using 1
  funext g
  unfold berlekampMatrix
  simp [Bool.beq_eq_decide_eq]

private theorem polyTime_berlekampStep :
    ComputableInPolyTime berlekampStep encBits encBits := by
  have hvec : ComputableInPolyTime
      (fun g : List Bool => kernelVecBits ((polyTrim g).length - 2) (berlekampMatrix (polyTrim g)))
      encBits encBits :=
    computableInPolyTime_kernelVecBits.comp
      ((by fun_prop : ComputableInPolyTime (fun g : List Bool => (polyTrim g).length - 2)
        encBits encUnary).prod (polyTime_berlekampMatrix.comp computableInPolyTime_polyTrim))
  convert ite' (unary_le' (length_bits.comp computableInPolyTime_polyTrim) (.const 2))
    computableInPolyTime_polyTrim
    (ite' (bitsAnyWithInput (test := fun _ b => b) hvec (snd _ _))
      (computableInPolyTime_polyGcd.comp
        (computableInPolyTime_polyTrim.prod (bitsCons (.const false) hvec)))
      computableInPolyTime_polyTrim) using 1
  funext g
  unfold berlekampStep
  simp only [Function.comp_def, decide_eq_true_eq]
  rfl

private theorem length_berlekampStep_le (g : List Bool) :
    (berlekampStep g).length ≤ g.length := by
  unfold berlekampStep; dsimp only
  set gt := polyTrim g; have hgt : gt.length ≤ g.length := length_polyTrim_le g
  split_ifs
  · exact hgt
  · have hv := length_kernelVecBits (gt.length - 2) (berlekampMatrix gt)
    let w := false :: kernelVecBits (gt.length - 2) (berlekampMatrix gt)
    have hgcd : (polyGcd gt w).length ≤ max gt.length w.length := length_polyGcd_le gt w
    simp only [w, List.length_cons, hv] at hgcd; omega
  · exact hgt

private theorem polyTime_berlekampIrreducibleFactor :
    ComputableInPolyTime berlekampIrreducibleFactor encBits encBits :=
  (iterateWith_spec
    (step := fun (_ : Bool) f => berlekampStep f)
    (invariant := fun g _ f => f.length ≤ g.length)
    (.const true) length_bits computableInPolyTime_polyTrim
    (polyTime_berlekampStep.comp (snd encBool encBits))
    length_polyTrim_le (fun _ _ _ _ hf => (length_berlekampStep_le _).trans hf)
    PolyBounded.self fun _ _ _ _ hf => by simpa only [encBits_apply] using hf).1

private theorem length_polyMod_lt {u f : List Bool} (hf : (polyTrim f).isEmpty = false) :
    (polyMod u f).length < (polyTrim f).length :=
  (polyOfBits_polyDivMod_spec (a := u)
    (polyOfBits_ne_zero_iff_polyTrim.mpr (List.isEmpty_eq_false_iff.mp hf))).2.1

private theorem length_polyMul_le' (a b : List Bool) :
    (polyMul a b).length ≤ a.length + b.length :=
  (length_polyMul_le a b).trans (Nat.sub_le _ _)

private theorem polyTime_primeGeThree :
    ComputableInPolyTime (fun q : ℕ => decide (q.Prime ∧ 3 ≤ q)) encUnary encBool := by
  have heq : (fun q : ℕ => decide (q.Prime ∧ 3 ≤ q)) =
      fun q => decide q.Prime && decide (3 ≤ q) := by funext q; simp
  rw [heq]; fun_prop

private theorem polyTime_shoupCyclicFactorBounded :
    ComputableInPolyTime
      (fun q : ℕ =>
        (fun f => berlekampIrreducibleFactor (polyComposePow q f))^[
          if q.Prime ∧ 3 ≤ q then qAdicValTwoPowSubOne q (ordTwoMod q) - 1 else 0]
          (berlekampIrreducibleFactor (List.replicate q true)))
      encUnary encBits := by
  have hcnt : ComputableInPolyTime
      (fun q : ℕ => if q.Prime ∧ 3 ≤ q then qAdicValTwoPowSubOne q (ordTwoMod q) - 1 else 0)
      encUnary encUnary := by
    have hk := computableInPolyTime_qAdicValTwoPowSubOne.comp
      (id'.prod computableInPolyTime_ordTwoMod)
    convert ite' polyTime_primeGeThree (unary_sub.comp (hk.prod (.const 1))) (.const 0) using 1
    funext q; by_cases h : q.Prime ∧ 3 ≤ q <;> simp [h]
  refine (iterateWith_spec
    (invariant := fun q k g =>
      g = (fun f => berlekampIrreducibleFactor (polyComposePow q f))^[k]
        (berlekampIrreducibleFactor (List.replicate q true)))
    id' hcnt (polyTime_berlekampIrreducibleFactor.comp (bitsReplicate true))
    (polyTime_berlekampIrreducibleFactor.comp computableInPolyTime_polyComposePow)
    (fun _ => rfl) (fun _ _ _ _ hg => by rw [hg, Function.iterate_succ_apply'])
    id'.polyBounded fun q k g hk hg => ?_).1
  simp only [encBits_apply]; rw [hg]
  by_cases h : q.Prime ∧ 3 ≤ q
  · rw [ite_eq_left h] at hk; exact length_shoupCyclicFactor_iterate_le h.1 h.2 hk
  · rw [ite_eq_right h] at hk
    obtain rfl : k = 0 := by omega
    rw [Function.iterate_zero_apply]; unfold berlekampIrreducibleFactor
    have hinv : ∀ s, ((berlekampStep)^[s] (polyTrim (List.replicate q true))).length ≤ q := by
      intro s; induction s with
      | zero => exact (length_polyTrim_le _).trans (by simp)
      | succ s ih => rw [Function.iterate_succ_apply']; exact (length_berlekampStep_le _).trans ih
    simpa only [List.length_replicate] using hinv q

/-! ### Arithmetic in `L = K[Y] / (Y ^ q - Z)` and matrix construction -/

private theorem polyTime_shoupUnitVec (idx : ℕ) :
    ComputableInPolyTime
      (fun q : ℕ => (List.range q).map fun i => if i == idx then [true] else [])
      encUnary (encList encBits) :=
  mapWithInput range (by fun_prop)

private theorem polyTime_shoupLAdd :
    ComputableInPolyTime
      (fun p : ℕ × List (List Bool) × List (List Bool) => shoupLAdd p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair (encList encBits) (encList encBits))) (encList encBits) :=
  mapWithInput (by fun_prop) (by fun_prop)

private def shoupLMulSum (a b : List (List Bool)) (cnt off1 off2 : ℕ) : List Bool :=
  (List.range cnt).foldl
    (fun acc t => polyAdd acc (polyMul (a.getD (off1 + t) []) (b.getD (off2 - t) []))) []

private theorem length_foldl_shoupLMulSum_le (a b : List (List Bool)) (off1 off2 : ℕ)
    (L : List ℕ) :
    (L.foldl (fun acc t => polyAdd acc (polyMul (a.getD (off1 + t) []) (b.getD (off2 - t) [])))
      []).length ≤ (encList encBits a).length + (encList encBits b).length := by
  suffices ∀ acc : List Bool,
      acc.length ≤ (encList encBits a).length + (encList encBits b).length →
      (L.foldl (fun acc t => polyAdd acc (polyMul (a.getD (off1 + t) []) (b.getD (off2 - t) [])))
        acc).length ≤ (encList encBits a).length + (encList encBits b).length from
    this [] (Nat.zero_le _)
  intro acc hacc; induction L generalizing acc with
  | nil => exact hacc
  | cons _ _ ih =>
    exact ih _ ((length_polyAdd_le _ _).trans (max_le hacc ((length_polyMul_le' _ _).trans
      (Nat.add_le_add (getD_length_le_encList_bits a _) (getD_length_le_encList_bits b _)))))

section ShoupLMulSection
attribute [local irreducible] polyTrim polyAdd polyMul polyMod

private theorem polyTime_shoupLMulSum :
    ComputableInPolyTime
      (fun p : (List (List Bool) × List (List Bool)) × (ℕ × ℕ × ℕ) =>
        shoupLMulSum p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2)
      (encPair (encPair (encList encBits) (encList encBits))
        (encPair encUnary (encPair encUnary encUnary)))
      encBits := by
  let EP := encPair (encList encBits) (encList encBits)
  let EA := encPair EP (encPair encUnary encUnary)
  have hstep : ComputableInPolyTime
      (fun x : (((List (List Bool) × List (List Bool)) × (ℕ × ℕ)) × List Bool) × ℕ =>
        polyAdd x.1.2
          (polyMul (x.1.1.1.1.getD (x.1.1.2.1 + x.2) [])
            (x.1.1.1.2.getD (x.1.1.2.2 - x.2) [])))
      (encPair (encPair EA encBits) encUnary) encBits := by fun_prop
  have hbound : ComputableInPolyTime
      (fun p : (List (List Bool) × List (List Bool)) × (ℕ × ℕ × ℕ) =>
        (encList encBits p.1.1).length + (encList encBits p.1.2).length)
      (encPair EP (encPair encUnary (encPair encUnary encUnary))) encUnary := by fun_prop
  exact foldlWith (encA := encUnary) (encP := EA) (encL := encList encUnary) (encB := encBits)
    (par := fun p => (p.1, p.2.2)) (list := fun p => List.range p.2.1)
    (step := fun par acc t =>
      polyAdd acc (polyMul (par.1.1.getD (par.2.1 + t) []) (par.1.2.getD (par.2.2 - t) [])))
    (by fun_prop) (by fun_prop) (.const []) hstep hbound.polyBounded
    fun p i _ => by
      simpa only [encBits_apply] using
        length_foldl_shoupLMulSum_le p.1.1 p.1.2 p.2.2.1 p.2.2.2 ((List.range p.2.1).take i)

attribute [local irreducible] shoupLMulSum

private theorem polyTime_shoupLMulSum' {α : Type} {enc : α ↪ List Bool}
    {a b : α → List (List Bool)} {cnt o1 o2 : α → ℕ}
    (ha : ComputableInPolyTime a enc (encList encBits))
    (hb : ComputableInPolyTime b enc (encList encBits))
    (hc : ComputableInPolyTime cnt enc encUnary)
    (ho1 : ComputableInPolyTime o1 enc encUnary) (ho2 : ComputableInPolyTime o2 enc encUnary) :
    ComputableInPolyTime (fun x => shoupLMulSum (a x) (b x) (cnt x) (o1 x) (o2 x)) enc encBits :=
  polyTime_shoupLMulSum.comp ((ha.prod hb).prod (hc.prod (ho1.prod ho2)))

private theorem polyTime_shoupLMul :
    ComputableInPolyTime
      (fun p : (ℕ × List Bool) × (List (List Bool) × List (List Bool)) =>
        shoupLMul p.1.1 p.1.2 p.2.1 p.2.2)
      (encPair (encPair encUnary encBits) (encPair (encList encBits) (encList encBits)))
      (encList encBits) := by
  let EP := encPair (encPair encUnary encBits) (encPair (encList encBits) (encList encBits))
  have hcell : ComputableInPolyTime
      (fun x : ((ℕ × List Bool) × (List (List Bool) × List (List Bool))) × ℕ =>
        polyMod (polyAdd (shoupLMulSum x.1.2.1 x.1.2.2 (x.2 + 1) 0 x.2)
          (false :: shoupLMulSum x.1.2.1 x.1.2.2 (x.1.1.1 - 1 - x.2) (x.2 + 1) (x.1.1.1 - 1)))
          x.1.1.2)
      (encPair EP encUnary) encBits :=
    polyTime_polyMod'
      (polyTime_polyAdd'
        (polyTime_shoupLMulSum' (by fun_prop) (by fun_prop)
          (by fun_prop) (.const 0) (snd _ _))
        (bitsCons (.const false)
          (polyTime_shoupLMulSum' (by fun_prop) (by fun_prop)
            (by fun_prop) (by fun_prop)
            (by fun_prop))))
      (by fun_prop)
  convert mapWithInput
    (f := fun (p : (ℕ × List Bool) × (List (List Bool) × List (List Bool))) (k : ℕ) =>
      polyMod (polyAdd (shoupLMulSum p.2.1 p.2.2 (k + 1) 0 k)
        (false :: shoupLMulSum p.2.1 p.2.2 (p.1.1 - 1 - k) (k + 1) (p.1.1 - 1))) p.1.2)
    (range.comp ((fst encUnary encBits).comp (fst _ _))) hcell using 1
  funext p
  unfold shoupLMul
  refine congrArg (fun fn => (List.range p.1.1).map fn) (funext fun k => ?_)
  have hidx : ∀ t, p.1.1 + k - (k + 1 + t) = p.1.1 - 1 - t := fun t => by omega
  simp [shoupLMulSum, hidx]

end ShoupLMulSection

private theorem length_shoupLMul (q : ℕ) (f : List Bool) (a b : List (List Bool))
    (hf : (polyTrim f).isEmpty = false) :
    (shoupLMul q f a b).length = q ∧ ∀ v ∈ shoupLMul q f a b, v.length ≤ f.length := by
  unfold shoupLMul
  refine ⟨by simp, fun v hv => ?_⟩
  rcases List.mem_map.mp hv with ⟨_, _, rfl⟩
  exact (length_polyMod_lt hf).le.trans (length_polyTrim_le f)

private def shoupFrobStep (p : ℕ × List Bool) (x : List (List Bool)) : List (List Bool) :=
  shoupLMul p.1 p.2 x x

private def shoupLFrobQBounded (q : ℕ) (f : List Bool) (a : List (List Bool)) :
    List (List Bool) :=
  (shoupFrobStep (q, f))^[if (polyTrim f).isEmpty then 0 else q] a

private theorem shoupLFrobQBounded_eq {q : ℕ} {f : List Bool} (a : List (List Bool))
    (hf : (polyTrim f).isEmpty = false) :
    shoupLFrobQBounded q f a = shoupLFrobQ q f a := by
  unfold shoupLFrobQBounded shoupLFrobQ shoupFrobStep; simp [hf]

section ShoupFrobSection
attribute [local irreducible] shoupLMul shoupFrobStep polyTrim

private theorem polyTime_shoupLFrobQBounded :
    ComputableInPolyTime
      (fun p : (ℕ × List Bool) × List (List Bool) => shoupLFrobQBounded p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encBits) (encList encBits)) (encList encBits) := by
  have hstep : ComputableInPolyTime
      (fun x : (ℕ × List Bool) × List (List Bool) => shoupFrobStep x.1 x.2)
      (encPair (encPair encUnary encBits) (encList encBits)) (encList encBits) := by
    convert polyTime_shoupLMul.comp ((fst _ _).prod ((snd _ _).prod (snd _ _))) using 1
    funext x; unfold shoupFrobStep; rfl
  exact (iterateWith_spec (step := shoupFrobStep)
    (invariant := fun p _ x =>
      x.length ≤ p.1.1 + p.2.length ∧
        ∀ v ∈ x, v.length ≤ p.1.2.length + (encList encBits p.2).length)
    (fst _ _) (by fun_prop) (snd _ _) hstep
    (fun _ => ⟨Nat.le_add_left _ _, fun _ hv => by
      simpa only [encBits_apply] using
        (length_le_encList_of_mem encBits hv).trans (Nat.le_add_left _ _)⟩)
    (fun _ _ _ hk _ => by
      obtain ⟨hl, hrows⟩ := length_shoupLMul _ _ _ _ (isEmpty_polyTrim_false_of_lt_ite hk)
      exact ⟨by unfold shoupFrobStep; exact hl.le.trans (Nat.le_add_right _ _), fun v hv => by
        unfold shoupFrobStep at hv; exact (hrows v hv).trans (Nat.le_add_right _ _)⟩)
    (by fun_prop : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × List (List Bool) =>
        (p.1.1 + p.2.length) * (2 * (p.1.2.length + (encList encBits p.2).length) + 1))
      (encPair (encPair encUnary encBits) (encList encBits)) encUnary).polyBounded
    fun _ _ _ _ hx => length_encList_bits_le hx.1 hx.2).1

end ShoupFrobSection

private def shoupBetaStep (p : ℕ × List Bool) (st : List (List Bool) × List (List Bool)) :
    List (List Bool) × List (List Bool) :=
  (shoupLAdd p.1 st.1 st.2, shoupLFrobQBounded p.1 p.2 st.2)

private def shoupBetaBounded (q : ℕ) (f : List Bool) : List (List Bool) :=
  ((shoupBetaStep (q, f))^[if (polyTrim f).isEmpty then 0 else f.length - 1]
    (List.replicate q [], (List.range q).map fun i => if i == 1 then [true] else [])).1

private theorem shoupBetaBounded_eq {q : ℕ} {f : List Bool} (hf : (polyTrim f).isEmpty = false) :
    shoupBetaBounded q f = shoupBeta q f := by
  unfold shoupBetaBounded shoupBeta shoupBetaStep
  simp only [hf, Bool.false_eq_true, ↓reduceIte]
  rw [← foldl_range_const_eq]
  congr 1; refine congrArg (fun g => List.foldl g _ _) (funext fun _ => funext fun _ => ?_)
  rw [shoupLFrobQBounded_eq _ hf]

section ShoupBetaSection
attribute [local irreducible] shoupLAdd shoupLFrobQBounded shoupBetaStep polyTrim

private theorem polyTime_shoupBetaBounded :
    ComputableInPolyTime (fun p : ℕ × List Bool => shoupBetaBounded p.1 p.2)
      (encPair encUnary encBits) (encList encBits) := by
  have hstep : ComputableInPolyTime
      (fun x : (ℕ × List Bool) × (List (List Bool) × List (List Bool)) => shoupBetaStep x.1 x.2)
      (encPair (encPair encUnary encBits) (encPair (encList encBits) (encList encBits)))
      (encPair (encList encBits) (encList encBits)) := by
    unfold shoupBetaStep
    exact (polyTime_shoupLAdd.comp
      (((fst encUnary encBits).comp (fst (encPair encUnary encBits)
        (encPair (encList encBits) (encList encBits)))).prod
        (snd (encPair encUnary encBits) (encPair (encList encBits) (encList encBits))))).prod
      (polyTime_shoupLFrobQBounded.comp
        ((fst (encPair encUnary encBits) (encPair (encList encBits) (encList encBits))).prod
          ((snd (encList encBits) (encList encBits)).comp
            (snd (encPair encUnary encBits) (encPair (encList encBits) (encList encBits))))))
  refine (fst (encList encBits) (encList encBits)).comp (iterateWith_spec
    (invariant := fun p _ st =>
      st.1.length ≤ p.1 ∧ st.2.length ≤ p.1 ∧
        (∀ v ∈ st.1, v.length ≤ p.2.length + 1) ∧ ∀ v ∈ st.2, v.length ≤ p.2.length + 1)
    id' (by fun_prop)
    ((replicate (fst _ _) (.const [])).prod ((polyTime_shoupUnitVec 1).comp (fst _ _))) hstep
    (fun _ => ⟨by simp, by simp, fun _ hv => by simp [(List.mem_replicate.mp hv).2],
      fun _ hv => by rcases List.mem_map.mp hv with ⟨_, _, rfl⟩; split_ifs <;> simp⟩)
    (fun p _ st hk hinv => by
      have hf_ne := isEmpty_polyTrim_false_of_lt_ite hk
      have h1_rows : ∀ v ∈ shoupLAdd p.1 st.1 st.2, v.length ≤ p.2.length + 1 := fun v hv => by
        unfold shoupLAdd at hv; rcases List.mem_map.mp hv with ⟨i, _, rfl⟩
        exact (length_polyAdd_le _ _).trans (max_le
          (getD_length_le_of_forall hinv.2.2.1 i) (getD_length_le_of_forall hinv.2.2.2 i))
      have h2 : (shoupLFrobQBounded p.1 p.2 st.2).length ≤ p.1 ∧
          ∀ v ∈ shoupLFrobQBounded p.1 p.2 st.2, v.length ≤ p.2.length + 1 := by
        rw [shoupLFrobQBounded_eq _ hf_ne]; unfold shoupLFrobQ
        cases hq0 : p.1 with
        | zero =>
          rw [Function.iterate_zero_apply]
          exact ⟨by omega, hinv.2.2.2⟩
        | succ q' =>
          rw [Function.iterate_succ_apply']
          obtain ⟨hl, hrows⟩ := length_shoupLMul (q' + 1) p.2 _ _ hf_ne
          exact ⟨hl.le, fun v hv => (hrows v hv).trans (Nat.le_succ _)⟩
      unfold shoupBetaStep
      exact ⟨by simp [shoupLAdd], h2.1, h1_rows, h2.2⟩)
    (by fun_prop : ComputableInPolyTime
      (fun p : ℕ × List Bool => 3 * (p.1 * (2 * (p.2.length + 1) + 1)) + 1)
      (encPair encUnary encBits) encUnary).polyBounded
    fun p _ st _ hinv => by
      have h1 := length_encList_bits_le hinv.1 hinv.2.2.1
      have h2 := length_encList_bits_le hinv.2.1 hinv.2.2.2
      rw [length_encPair]; omega).1

end ShoupBetaSection

private def shoupPowersStep (p : (ℕ × List Bool) × List (List Bool))
    (st : List (List (List Bool)) × List (List Bool)) :
    List (List (List Bool)) × List (List Bool) :=
  (st.1 ++ [st.2], shoupLMul p.1.1 p.1.2 st.2 p.2)

private def shoupPowersBounded (q : ℕ) (f : List Bool) (β : List (List Bool)) :
    List (List (List Bool)) :=
  ((shoupPowersStep ((q, f), β))^[if (polyTrim f).isEmpty then 0 else q + 1]
    ([], (List.range q).map fun i => if i == 0 then [true] else [])).1

private theorem shoupPowersBounded_eq {q : ℕ} {f : List Bool} (β : List (List Bool))
    (hf : (polyTrim f).isEmpty = false) :
    shoupPowersBounded q f β = shoupPowers q f β := by
  unfold shoupPowersBounded shoupPowers shoupPowersStep
  simp only [hf, Bool.false_eq_true, ↓reduceIte]
  rw [← foldl_range_const_eq]

section ShoupPowersSection
attribute [local irreducible] shoupLMul shoupPowersStep polyTrim

private theorem polyTime_shoupPowersBounded :
    ComputableInPolyTime
      (fun p : (ℕ × List Bool) × List (List Bool) => shoupPowersBounded p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encBits) (encList encBits))
      (encList (encList encBits)) := by
  let EIn := encPair (encPair encUnary encBits) (encList encBits)
  let ESt := encPair (encList (encList encBits)) (encList encBits)
  have hstep : ComputableInPolyTime
      (fun x : ((ℕ × List Bool) × List (List Bool)) ×
          (List (List (List Bool)) × List (List Bool)) =>
        shoupPowersStep x.1 x.2) (encPair EIn ESt) ESt := by
    unfold shoupPowersStep
    exact ((snoc (encList encBits)).comp (snd EIn ESt)).prod
      (polyTime_shoupLMul.comp
        (((fst (encPair encUnary encBits) (encList encBits)).comp (fst EIn ESt)).prod
          (((snd (encList (encList encBits)) (encList encBits)).comp (snd EIn ESt)).prod
            ((snd (encPair encUnary encBits) (encList encBits)).comp (fst EIn ESt)))))
  have hbound : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × List (List Bool) =>
        2 * ((p.1.1 + 1) * (2 * (p.1.1 * (2 * (p.1.2.length + 1) + 1)) + 1)) + 1 +
          p.1.1 * (2 * (p.1.2.length + 1) + 1)) EIn encUnary := by fun_prop
  refine (fst (encList (encList encBits)) (encList encBits)).comp (iterateWith_spec
    (invariant := fun p k st =>
      st.1.length = k ∧ st.2.length ≤ p.1.1 ∧
        (∀ u ∈ st.1, u.length ≤ p.1.1 ∧ ∀ v ∈ u, v.length ≤ p.1.2.length + 1) ∧
        ∀ v ∈ st.2, v.length ≤ p.1.2.length + 1)
    id' (by fun_prop)
    ((const ([] : List (List (List Bool)))).prod
      ((polyTime_shoupUnitVec 0).comp ((fst encUnary encBits).comp (fst _ _)))) hstep
    (fun _ => ⟨by simp, by simp, by simp,
      fun _ hv => by rcases List.mem_map.mp hv with ⟨_, _, rfl⟩; split_ifs <;> simp⟩)
    (fun p _ st hk hinv => by
      obtain ⟨hl, hrows⟩ :=
        length_shoupLMul p.1.1 p.1.2 st.2 p.2 (isEmpty_polyTrim_false_of_lt_ite hk)
      unfold shoupPowersStep
      refine ⟨by simp [hinv.1], hl.le, fun u hu => ?_,
        fun v hv => (hrows v hv).trans (Nat.le_succ _)⟩
      rcases List.mem_append.mp hu with hu | hu
      · exact hinv.2.2.1 u hu
      · rcases List.mem_singleton.mp hu with rfl; exact ⟨hinv.2.1, hinv.2.2.2⟩)
    hbound.polyBounded
    fun p k st hk hinv => by
      have hk_len : st.1.length ≤ p.1.1 + 1 := by rw [hinv.1]; split_ifs at hk <;> omega
      have hl1 := (length_encList_le (encList encBits) st.1
        (b := p.1.1 * (2 * (p.1.2.length + 1) + 1)) fun u hu =>
          length_encList_bits_le (hinv.2.2.1 u hu).1 (hinv.2.2.1 u hu).2).trans
        (Nat.mul_le_mul_right _ hk_len)
      have hl2 := length_encList_bits_le hinv.2.1 hinv.2.2.2
      rw [length_encPair]; omega).1

end ShoupPowersSection

private theorem polyTime_shoupMinPolyMatrix :
    ComputableInPolyTime
      (fun p : (ℕ × ℕ) × List (List (List Bool)) => shoupMinPolyMatrix p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encUnary) (encList (encList encBits)))
      (encList encBits) :=
  mapWithInput (by fun_prop)
    (listToBits.comp (mapWithInput (by fun_prop) (by fun_prop)))

section ShoupIrreducibleSection
attribute [local irreducible] shoupCyclicFactor shoupBetaBounded shoupPowersBounded
  shoupMinPolyMatrix kernelVecBits ordTwoMod qAdicValTwoPowSubOne

/-- `shoupIrreducibleBits` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_shoupIrreducibleBits :
    ComputableInPolyTime shoupIrreducibleBits encUnary encBits := by
  have hf := polyTime_shoupCyclicFactorBounded
  have hβ := polyTime_shoupBetaBounded.comp (id'.prod hf)
  have hpows := polyTime_shoupPowersBounded.comp ((id'.prod hf).prod hβ)
  have hmat := polyTime_shoupMinPolyMatrix.comp
    ((id'.prod computableInPolyTime_ordTwoMod).prod hpows)
  have hvec := computableInPolyTime_kernelVecBits.comp
    ((by fun_prop : ComputableInPolyTime (fun q : ℕ => q + 1) encUnary encUnary).prod hmat)
  convert ite' polyTime_primeGeThree hvec (.const []) using 1
  funext q; unfold shoupIrreducibleBits
  by_cases h : q.Prime ∧ 3 ≤ q
  · simp only [h, and_self, decide_true, ↓reduceIte, Function.comp_def]
    obtain ⟨htrim, _, _, _, hlen⟩ := shoupCyclicFactor_spec h.1 h.2
    have hne : (polyTrim (shoupCyclicFactor q (qAdicValTwoPowSubOne q (ordTwoMod q)))).isEmpty =
        false := by
      rw [htrim, List.isEmpty_eq_false_iff]; intro hnil; rw [hnil] at hlen; simp at hlen
    rw [show (fun f => berlekampIrreducibleFactor (polyComposePow q f))^[
        qAdicValTwoPowSubOne q (ordTwoMod q) - 1]
        (berlekampIrreducibleFactor (List.replicate q true)) =
        shoupCyclicFactor q (qAdicValTwoPowSubOne q (ordTwoMod q)) from by
          unfold shoupCyclicFactor; rfl,
      shoupBetaBounded_eq hne, shoupPowersBounded_eq _ hne]
  · simp [h]

end ShoupIrreducibleSection

end Cslib.AffineDisperser.Li
