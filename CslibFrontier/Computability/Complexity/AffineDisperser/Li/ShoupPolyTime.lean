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

open Turing.MultiTapeTM
open Cslib.BitString (listDot)

attribute [local irreducible] ComputableInPolyTime

/-! ### Unary parameter selection (`fifthRoot`, `primeThresholdBound`, `primeDeg`) -/

/-- `fifthRoot` is computable in polynomial time on unary naturals. -/
@[fun_prop]
theorem computableInPolyTime_fifthRoot :
    ComputableInPolyTime fifthRoot encUnary encUnary := by
  unfold fifthRoot
  have h5 : ComputableInPolyTime (fun k : ℕ => (k + 1) ^ 5) encUnary encUnary := by
    have heq : (fun k : ℕ => (k + 1) ^ 5) =
        fun k : ℕ => (k + 1) * (k + 1) * (k + 1) * (k + 1) * (k + 1) := by
      funext k; ring
    rw [heq]
    fun_prop
  refine ComputableInPolyTime.countPWithInput (encA := encUnary)
    ComputableInPolyTime.range ?_
  exact ComputableInPolyTime.unary_le'
    (h5.comp (ComputableInPolyTime.snd encUnary encUnary))
    (ComputableInPolyTime.fst encUnary encUnary)

/-- `primeThresholdBound` is computable in polynomial time on unary naturals. -/
@[fun_prop]
theorem computableInPolyTime_primeThresholdBound :
    ComputableInPolyTime primeThresholdBound encUnary encUnary := by
  unfold primeThresholdBound
  have := computableInPolyTime_fifthRoot
  fun_prop

/-- `primeDeg` is computable in polynomial time on unary naturals. -/
@[fun_prop]
theorem computableInPolyTime_primeDeg :
    ComputableInPolyTime primeDeg encUnary encUnary := by
  have hl : ComputableInPolyTime
      (fun N : ℕ =>
        (List.range (primeThresholdBound N)).map fun i => primeThresholdBound N + 1 + i)
      encUnary (encList encUnary) := by
    refine ComputableInPolyTime.mapWithInput
      (ComputableInPolyTime.range.comp computableInPolyTime_primeThresholdBound) ?_
    have := computableInPolyTime_primeThresholdBound
    fun_prop
  have hprimePlain : ComputableInPolyTime (fun b : ℕ => decide b.Prime) encUnary encBool := by
    fun_prop
  have hprime : ComputableInPolyTime (fun p : ℕ × ℕ => decide p.2.Prime)
      (encPair encUnary encUnary) encBool :=
    hprimePlain.comp (ComputableInPolyTime.snd encUnary encUnary)
  have hf : ComputableInPolyTime
      (fun N : ℕ =>
        ((List.range (primeThresholdBound N)).map fun i => primeThresholdBound N + 1 + i).find?
          fun b => decide b.Prime)
      encUnary (encOption encUnary) :=
    ComputableInPolyTime.findWithInput hl hprime
  refine ComputableInPolyTime.optionGetDWithInput hf ?_
  have := computableInPolyTime_primeThresholdBound
  fun_prop

private def ordSomeAdd1 (_ x : ℕ) : ℕ := x + 1

/-- `ordTwoMod` is computable in polynomial time on unary naturals. -/
theorem computableInPolyTime_ordTwoMod :
    ComputableInPolyTime ordTwoMod encUnary encUnary := by
  have hu2b : ComputableInPolyTime (fun n : ℕ => n) encUnary encNat := by fun_prop
  have htwoPow : ComputableInPolyTime (fun p : ℕ × ℕ => 2 ^ (p.2 + 1))
      (encPair encUnary encUnary) encNat :=
    ComputableInPolyTime.binary_two_pow.comp
      (by fun_prop : ComputableInPolyTime (fun p : ℕ × ℕ => p.2 + 1)
        (encPair encUnary encUnary) encUnary)
  have hmod : ComputableInPolyTime (fun p : ℕ × ℕ => 2 ^ (p.2 + 1) % p.1)
      (encPair encUnary encUnary) encNat :=
    ComputableInPolyTime.binary_mod' htwoPow
      (hu2b.comp (ComputableInPolyTime.fst encUnary encUnary))
  have hpred := hmod.beq (.const 1)
  have hf : ComputableInPolyTime
      (fun q : ℕ => (List.range (q - 1)).find? fun i => 2 ^ (i + 1) % q == 1)
      encUnary (encOption encUnary) :=
    ComputableInPolyTime.findWithInput (test := fun q i => 2 ^ (i + 1) % q == 1)
      (ComputableInPolyTime.range.comp (by fun_prop :
        ComputableInPolyTime (fun q : ℕ => q - 1) encUnary encUnary))
      hpred
  have hsome : ComputableInPolyTime (fun p : ℕ × ℕ => ordSomeAdd1 p.1 p.2)
      (encPair encUnary encUnary) encUnary := by
    unfold ordSomeAdd1
    fun_prop
  have helim := ComputableInPolyTime.optionElimWithInput hf
    (ComputableInPolyTime.const 0) hsome
  convert helim using 1
  funext q
  unfold ordTwoMod ordSomeAdd1
  cases (List.find? (fun i => 2 ^ (i + 1) % q == 1) (List.range (q - 1))) <;> rfl

/-- `qAdicValTwoPowSubOne` is computable in polynomial time on unary naturals. -/
theorem computableInPolyTime_qAdicValTwoPowSubOne :
    ComputableInPolyTime (fun p : ℕ × ℕ => qAdicValTwoPowSubOne p.1 p.2)
      (encPair encUnary encUnary) encUnary := by
  have htwoPow : ComputableInPolyTime
      (fun p : (ℕ × ℕ) × ℕ => 2 ^ p.1.2)
      (encPair (encPair encUnary encUnary) encUnary) encNat :=
    ComputableInPolyTime.binary_two_pow.comp
      (by fun_prop : ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => p.1.2)
        (encPair (encPair encUnary encUnary) encUnary) encUnary)
  have hpow : ComputableInPolyTime
      (fun p : (ℕ × ℕ) × ℕ => p.1.1 ^ (p.2 + 1))
      (encPair (encPair encUnary encUnary) encUnary) encNat := by
    have hbase : ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => p.1.1)
        (encPair (encPair encUnary encUnary) encUnary) encNat := by fun_prop
    have hexp : ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => p.2 + 1)
        (encPair (encPair encUnary encUnary) encUnary) encUnary := by fun_prop
    exact ComputableInPolyTime.binary_pow' hbase hexp
  have hmod : ComputableInPolyTime
      (fun p : (ℕ × ℕ) × ℕ => 2 ^ p.1.2 % p.1.1 ^ (p.2 + 1))
      (encPair (encPair encUnary encUnary) encUnary) encNat :=
    ComputableInPolyTime.binary_mod' htwoPow hpow
  have hpred : ComputableInPolyTime
      (fun p : (ℕ × ℕ) × ℕ => decide ((2 ^ p.1.2 % p.1.1 ^ (p.2 + 1) == 1) = true))
      (encPair (encPair encUnary encUnary) encUnary) encBool := by
    have hbeq := hmod.beq (.const 1)
    have heq : (fun p : (ℕ × ℕ) × ℕ =>
          decide ((2 ^ p.1.2 % p.1.1 ^ (p.2 + 1) == 1) = true)) =
        fun p => 2 ^ p.1.2 % p.1.1 ^ (p.2 + 1) == 1 := by
      funext p
      cases h : (2 ^ p.1.2 % p.1.1 ^ (p.2 + 1) == 1) <;> simp_all
    rw [heq]
    exact hbeq
  exact ComputableInPolyTime.countPWithInput (encA := encUnary)
    (ComputableInPolyTime.range.comp (ComputableInPolyTime.fst encUnary encUnary))
    hpred

/-! ### Binary polynomial arithmetic (`polyTrim`, `polyAdd`, `polyMul`, `polyDivMod`, `polyGcd`) -/

private def trimStep (st : ℕ × ℕ) (b : Bool) : ℕ × ℕ :=
  (st.1 + 1, if b then st.1 + 1 else st.2)

private theorem foldl_trimStep_fst (p : List Bool) (i a : ℕ) :
    (p.foldl trimStep (i, a)).1 = i + p.length := by
  induction p generalizing i a with
  | nil => simp
  | cons b p ih =>
    simp only [List.foldl_cons, trimStep, List.length_cons, ih]
    omega

private theorem foldl_trimStep_le (p : List Bool) (i a : ℕ) (ha : a ≤ i) :
    (p.foldl trimStep (i, a)).2 ≤ i + p.length := by
  induction p generalizing i a with
  | nil => simpa using ha
  | cons b p ih =>
    rw [List.foldl_cons, List.length_cons]
    dsimp only [trimStep]
    have hnext : (if b = true then i + 1 else a) ≤ i + 1 := by
      cases b
      · exact Nat.le_succ_of_le ha
      · exact le_rfl
    have := ih (i + 1) _ hnext
    omega

private theorem polyTrim_append_false (p : List Bool) : polyTrim (p ++ [false]) = polyTrim p := by
  simp [polyTrim, List.foldr_append]

private theorem polyTrim_eq_take (p : List Bool) :
    polyTrim p = p.take (p.foldl trimStep (0, 0)).2 := by
  induction p using List.reverseRecOn with
  | nil => rfl
  | append_singleton p b ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, trimStep, foldl_trimStep_fst,
      Nat.zero_add]
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, polyTrim_append_false, ih]
      have hle := foldl_trimStep_le p 0 0 (le_refl 0)
      rw [Nat.zero_add] at hle
      exact (List.take_append_of_le_length hle).symm
    · simp only [↓reduceIte, polyTrim_append_true]
      have hlen : p.length + 1 = (p ++ [true]).length := by simp
      rw [hlen, List.take_length]

private theorem length_encUnary_le_iff {a b : ℕ} (h : a ≤ b) :
    (encUnary a).length ≤ (encUnary b).length := by
  simp only [encUnary]
  change (List.replicate a true).length ≤ (List.replicate b true).length
  simpa using h

private theorem length_encPair_mono {α β : Type} (encA : α ↪ List Bool) (encB : β ↪ List Bool)
    {a₁ a₂ : α} {b₁ b₂ : β} (ha : (encA a₁).length ≤ (encA a₂).length)
    (hb : (encB b₁).length ≤ (encB b₂).length) :
    (encPair encA encB (a₁, b₁)).length ≤ (encPair encA encB (a₂, b₂)).length := by
  rw [length_encPair, length_encPair]
  dsimp only
  omega

/-- `polyTrim` is computable in polynomial time on bit lists. -/
theorem computableInPolyTime_polyTrim : ComputableInPolyTime polyTrim encBits encBits := by
  have hstepPlain : ComputableInPolyTime
      (fun p : (ℕ × ℕ) × Bool => trimStep p.1 p.2)
      (encPair (encPair encUnary encUnary) encBool) (encPair encUnary encUnary) := by
    unfold trimStep
    have hfst : ComputableInPolyTime (fun p : (ℕ × ℕ) × Bool => p.1.1 + 1)
        (encPair (encPair encUnary encUnary) encBool) encUnary := by fun_prop
    have hsnd : ComputableInPolyTime
        (fun p : (ℕ × ℕ) × Bool => if p.2 then p.1.1 + 1 else p.1.2)
        (encPair (encPair encUnary encUnary) encBool) encUnary :=
      ComputableInPolyTime.ite'
        (ComputableInPolyTime.snd (encPair encUnary encUnary) encBool)
        (by fun_prop) (by fun_prop)
    exact ComputableInPolyTime.pair hfst hsnd
  have hlenPair : ComputableInPolyTime (fun p : List Bool => (p.length, p.length))
      encBits (encPair encUnary encUnary) := by
    have hlen : ComputableInPolyTime List.length encBits encUnary :=
      ComputableInPolyTime.length_bits
    exact hlen.prod hlen
  have hfold : ComputableInPolyTime
      (fun p : List Bool => p.foldl trimStep (0, 0))
      encBits (encPair encUnary encUnary) := by
    refine ComputableInPolyTime.foldl' (encA := encBool) (encL := encBits)
      (encB := encPair encUnary encUnary)
      ComputableInPolyTime.id'
      (ComputableInPolyTime.const (0, 0))
      hstepPlain
      (B := fun p : List Bool => (encPair encUnary encUnary (p.length, p.length)).length)
      hlenPair.polyBounded_length ?_
    intro p i hi
    have hle1 : ((p.take i).foldl trimStep (0, 0)).1 ≤ p.length := by
      rw [foldl_trimStep_fst, Nat.zero_add, List.length_take]
      exact Nat.min_le_right _ _
    have hle2 : ((p.take i).foldl trimStep (0, 0)).2 ≤ p.length := by
      have := foldl_trimStep_le (p.take i) 0 0 (le_refl 0)
      rw [Nat.zero_add, List.length_take] at this
      exact this.trans (Nat.min_le_right _ _)
    exact length_encPair_mono encUnary encUnary
      (length_encUnary_le_iff hle1) (length_encUnary_le_iff hle2)
  have htake : ComputableInPolyTime
      (fun p : List Bool => p.take (p.foldl trimStep (0, 0)).2)
      encBits encBits :=
    ComputableInPolyTime.bitsTakeWithInput
      ComputableInPolyTime.id'
      (ComputableInPolyTime.snd encUnary encUnary |>.comp hfold)
  convert htake using 1
  funext p
  exact polyTrim_eq_take p

/-- `polyAdd` is computable in polynomial time. -/
theorem computableInPolyTime_polyAdd :
    ComputableInPolyTime (fun p : List Bool × List Bool => polyAdd p.1 p.2)
      (encPair encBits encBits) encBits := by
  have hmax : ComputableInPolyTime
      (fun p : List Bool × List Bool => max p.1.length p.2.length)
      (encPair encBits encBits) encUnary :=
    ComputableInPolyTime.unary_max.comp
      ((ComputableInPolyTime.length_bits.comp
        (ComputableInPolyTime.fst encBits encBits)).prod
        (ComputableInPolyTime.length_bits.comp
          (ComputableInPolyTime.snd encBits encBits)))
  have hbit : ComputableInPolyTime
      (fun x : (List Bool × List Bool) × ℕ =>
        x.1.1.getD x.2 false ^^ x.1.2.getD x.2 false)
      (encPair (encPair encBits encBits) encUnary) encBool := by
    have h1 := ComputableInPolyTime.bitsGetDWithInput
      ((ComputableInPolyTime.fst encBits encBits).comp
        (ComputableInPolyTime.fst (encPair encBits encBits) encUnary))
      (ComputableInPolyTime.snd (encPair encBits encBits) encUnary)
      false
    have h2 := ComputableInPolyTime.bitsGetDWithInput
      ((ComputableInPolyTime.snd encBits encBits).comp
        (ComputableInPolyTime.fst (encPair encBits encBits) encUnary))
      (ComputableInPolyTime.snd (encPair encBits encBits) encUnary)
      false
    exact (ComputableInPolyTime.of_finite (fun b : Bool × Bool => b.1 ^^ b.2)
      (encIn := encPair encBool encBool) (encOut := encBool)).comp (h1.prod h2)
  have hmap : ComputableInPolyTime
      (fun p : List Bool × List Bool =>
        (List.range (max p.1.length p.2.length)).map fun i =>
          p.1.getD i false ^^ p.2.getD i false)
      (encPair encBits encBits) (encList encBool) :=
    ComputableInPolyTime.mapWithInput
      (ComputableInPolyTime.range.comp hmax) hbit
  exact computableInPolyTime_polyTrim.comp (ComputableInPolyTime.listToBits.comp hmap)

private theorem polyBounded_encBool_const :
    ∀ b : Bool, (encBool b).length ≤ max (encBool false).length (encBool true).length := by
  intro b
  cases b
  · exact le_max_left _ _
  · exact le_max_right _ _

/-- `polyMul` is computable in polynomial time. -/
theorem computableInPolyTime_polyMul :
    ComputableInPolyTime (fun p : List Bool × List Bool => polyMul p.1 p.2)
      (encPair encBits encBits) encBits := by
  have hcond : ComputableInPolyTime
      (fun p : List Bool × List Bool => p.1.isEmpty || p.2.isEmpty)
      (encPair encBits encBits) encBool :=
    (ComputableInPolyTime.of_finite (fun b : Bool × Bool => b.1 || b.2)
      (encIn := encPair encBool encBool) (encOut := encBool)).comp
      ((ComputableInPolyTime.bitsIsEmpty.comp
        (ComputableInPolyTime.fst encBits encBits)).prod
        (ComputableInPolyTime.bitsIsEmpty.comp
          (ComputableInPolyTime.snd encBits encBits)))
  have hsum : ComputableInPolyTime
      (fun p : List Bool × List Bool => p.1.length + p.2.length)
      (encPair encBits encBits) encUnary :=
    ComputableInPolyTime.unary_add.comp
      ((ComputableInPolyTime.length_bits.comp
        (ComputableInPolyTime.fst encBits encBits)).prod
        (ComputableInPolyTime.length_bits.comp
          (ComputableInPolyTime.snd encBits encBits)))
  have hcoeffStep : ComputableInPolyTime
      (fun x : (((List Bool × List Bool) × ℕ) × Bool) × ℕ =>
        x.1.2 ^^ (x.1.1.1.1.getD x.2 false && x.1.1.1.2.getD (x.1.1.2 - x.2) false))
      (encPair (encPair (encPair (encPair encBits encBits) encUnary) encBool) encUnary)
      encBool := by
    have hfront := ComputableInPolyTime.fst
      (encPair (encPair (encPair encBits encBits) encUnary) encBool) encUnary
    have hpar := (ComputableInPolyTime.fst
      (encPair (encPair encBits encBits) encUnary) encBool).comp hfront
    have hacc := (ComputableInPolyTime.snd
      (encPair (encPair encBits encBits) encUnary) encBool).comp hfront
    have hi := ComputableInPolyTime.snd
      (encPair (encPair (encPair encBits encBits) encUnary) encBool) encUnary
    have hp := (ComputableInPolyTime.fst (encPair encBits encBits) encUnary).comp hpar
    have hk := (ComputableInPolyTime.snd (encPair encBits encBits) encUnary).comp hpar
    have hp1 := (ComputableInPolyTime.fst encBits encBits).comp hp
    have hp2 := (ComputableInPolyTime.snd encBits encBits).comp hp
    have hb1 := ComputableInPolyTime.bitsGetDWithInput hp1 hi false
    have hsub := ComputableInPolyTime.unary_sub.comp (hk.prod hi)
    have hb2 := ComputableInPolyTime.bitsGetDWithInput hp2 hsub false
    exact (ComputableInPolyTime.of_finite
      (fun b : Bool × Bool × Bool => b.1 ^^ (b.2.1 && b.2.2))
      (encIn := encPair encBool (encPair encBool encBool)) (encOut := encBool)).comp
      (hacc.prod (hb1.prod hb2))
  have hcoeff : ComputableInPolyTime
      (fun x : (List Bool × List Bool) × ℕ =>
        (List.range (x.2 + 1)).foldl
          (fun acc i => acc ^^ (x.1.1.getD i false && x.1.2.getD (x.2 - i) false)) false)
      (encPair (encPair encBits encBits) encUnary) encBool := by
    refine ComputableInPolyTime.foldlWith (encA := encUnary)
      (encL := encList encUnary) (encB := encBool)
      (par := id)
      (list := fun x : (List Bool × List Bool) × ℕ => List.range (x.2 + 1))
      (step := fun (x : (List Bool × List Bool) × ℕ) (acc : Bool) (i : ℕ) =>
        acc ^^ (x.1.1.getD i false && x.1.2.getD (x.2 - i) false))
      ComputableInPolyTime.id'
      (ComputableInPolyTime.range.comp (by fun_prop :
        ComputableInPolyTime (fun x : (List Bool × List Bool) × ℕ => x.2 + 1)
          (encPair (encPair encBits encBits) encUnary) encUnary))
      (ComputableInPolyTime.const false)
      hcoeffStep
      (B := fun _ => max (encBool false).length (encBool true).length)
      (PolyBounded.const _) ?_
    intro _ _ _
    exact polyBounded_encBool_const _
  have hmap : ComputableInPolyTime
      (fun p : List Bool × List Bool =>
        (List.range (p.1.length + p.2.length)).map fun k =>
          (List.range (k + 1)).foldl
            (fun acc i => acc ^^ (p.1.getD i false && p.2.getD (k - i) false)) false)
      (encPair encBits encBits) (encList encBool) :=
    ComputableInPolyTime.mapWithInput
      (ComputableInPolyTime.range.comp hsum) hcoeff
  have hres := computableInPolyTime_polyTrim.comp (ComputableInPolyTime.listToBits.comp hmap)
  have hplain := ComputableInPolyTime.ite' hcond
    (ComputableInPolyTime.const ([] : List Bool)) hres
  convert hplain using 1
  funext p
  rfl

private theorem length_polyDivModStep_le (bt q r : List Bool) {n : ℕ}
    (hq : q.length ≤ n) (hr : r.length ≤ n) :
    (polyDivModStep bt (q, r)).1.length ≤ n ∧ (polyDivModStep bt (q, r)).2.length ≤ n := by
  unfold polyDivModStep
  dsimp only
  set r' := polyTrim r
  have hr' : r'.length ≤ n := (length_polyTrim_le r).trans hr
  split_ifs with h
  · exact ⟨(length_polyTrim_le q).trans hq, hr'⟩
  · have hbt_pos : 1 ≤ bt.length := by
      cases bt with
      | nil => simp at h
      | cons _ _ => simp
    have hr_ge : bt.length ≤ r'.length := by
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt] at h
      exact h.1
    set d := r'.length - bt.length
    have hd1 : (List.replicate d false ++ [true]).length ≤ n := by
      simp only [List.length_append, List.length_replicate, List.length_singleton]
      omega
    have hdb : (List.replicate d false ++ bt).length ≤ n := by
      simp only [List.length_append, List.length_replicate]
      omega
    exact ⟨(length_polyAdd_le _ _).trans (max_le hq hd1),
      (length_polyAdd_le _ _).trans (max_le hr' hdb)⟩

private theorem polyTime_polyDivModStep :
    ComputableInPolyTime
      (fun p : List Bool × List Bool × List Bool => polyDivModStep p.1 p.2)
      (encPair encBits (encPair encBits encBits)) (encPair encBits encBits) := by
  have hbt := ComputableInPolyTime.fst encBits (encPair encBits encBits)
  have hst := ComputableInPolyTime.snd encBits (encPair encBits encBits)
  have hq := (ComputableInPolyTime.fst encBits encBits).comp hst
  have hr := computableInPolyTime_polyTrim.comp
    ((ComputableInPolyTime.snd encBits encBits).comp hst)
  have hlenR := ComputableInPolyTime.length_bits.comp hr
  have hlenBt := ComputableInPolyTime.length_bits.comp hbt
  have hcond : ComputableInPolyTime
      (fun p : List Bool × List Bool × List Bool =>
        decide ((polyTrim p.2.2).length < p.1.length) || p.1.isEmpty)
      (encPair encBits (encPair encBits encBits)) encBool :=
    (ComputableInPolyTime.of_finite (fun b : Bool × Bool => b.1 || b.2)
      (encIn := encPair encBool encBool) (encOut := encBool)).comp
      ((ComputableInPolyTime.unary_lt' hlenR hlenBt).prod
        (ComputableInPolyTime.bitsIsEmpty.comp hbt))
  have hbase : ComputableInPolyTime
      (fun p : List Bool × List Bool × List Bool => (polyTrim p.2.1, polyTrim p.2.2))
      (encPair encBits (encPair encBits encBits)) (encPair encBits encBits) :=
    (computableInPolyTime_polyTrim.comp hq).prod hr
  have hd : ComputableInPolyTime
      (fun p : List Bool × List Bool × List Bool =>
        (polyTrim p.2.2).length - p.1.length)
      (encPair encBits (encPair encBits encBits)) encUnary :=
    ComputableInPolyTime.unary_sub.comp (hlenR.prod hlenBt)
  have hrep : ComputableInPolyTime
      (fun p : List Bool × List Bool × List Bool =>
        List.replicate ((polyTrim p.2.2).length - p.1.length) false)
      (encPair encBits (encPair encBits encBits)) encBits :=
    (ComputableInPolyTime.bitsReplicate false).comp hd
  have hstep1 : ComputableInPolyTime
      (fun p : List Bool × List Bool × List Bool =>
        polyAdd p.2.1 (List.replicate ((polyTrim p.2.2).length - p.1.length) false ++ [true]))
      (encPair encBits (encPair encBits encBits)) encBits :=
    computableInPolyTime_polyAdd.comp (hq.prod
      (ComputableInPolyTime.bitsAppend hrep (.const [true])))
  have hstep2 : ComputableInPolyTime
      (fun p : List Bool × List Bool × List Bool =>
        polyAdd (polyTrim p.2.2)
          (List.replicate ((polyTrim p.2.2).length - p.1.length) false ++ p.1))
      (encPair encBits (encPair encBits encBits)) encBits :=
    computableInPolyTime_polyAdd.comp (hr.prod
      (ComputableInPolyTime.bitsAppend hrep hbt))
  have hplain := ComputableInPolyTime.ite' hcond
    hbase (hstep1.prod hstep2)
  exact hplain

private theorem polyTime_polyDivMod :
    ComputableInPolyTime (fun p : List Bool × List Bool => polyDivMod p.1 p.2)
      (encPair encBits encBits) (encPair encBits encBits) := by
  have hpar : ComputableInPolyTime (fun p : List Bool × List Bool => polyTrim p.2)
      (encPair encBits encBits) encBits :=
    computableInPolyTime_polyTrim.comp (ComputableInPolyTime.snd encBits encBits)
  have hcnt : ComputableInPolyTime (fun p : List Bool × List Bool => p.1.length)
      (encPair encBits encBits) encUnary :=
    ComputableInPolyTime.length_bits.comp (ComputableInPolyTime.fst encBits encBits)
  have hinit : ComputableInPolyTime
      (fun p : List Bool × List Bool => (([] : List Bool), polyTrim p.1))
      (encPair encBits encBits) (encPair encBits encBits) :=
    (ComputableInPolyTime.const ([] : List Bool)).prod
      (computableInPolyTime_polyTrim.comp (ComputableInPolyTime.fst encBits encBits))
  have hbound : PolyBounded (fun p : List Bool × List Bool => (encPair encBits encBits p).length)
      (fun p : List Bool × List Bool => 3 * p.1.length + 1) :=
    ((PolyBounded.const 3).mul
      (ComputableInPolyTime.polyBounded hcnt)).add (PolyBounded.const 1)
  exact (ComputableInPolyTime.iterateWith_spec
    (invariant := fun p _ st => st.1.length ≤ p.1.length ∧ st.2.length ≤ p.1.length)
    hpar hcnt hinit polyTime_polyDivModStep
    (fun p => ⟨by simp, length_polyTrim_le p.1⟩)
    (fun p _ _ _ hst => length_polyDivModStep_le _ _ _ hst.1 hst.2)
    hbound fun p _ st _ hst => by
      rw [length_encPair]
      simp only [encBits_apply]
      omega).1

/-- `polyMod` is computable in polynomial time. -/
theorem computableInPolyTime_polyMod :
    ComputableInPolyTime (fun p : List Bool × List Bool => polyMod p.1 p.2)
      (encPair encBits encBits) encBits :=
  (ComputableInPolyTime.snd encBits encBits).comp polyTime_polyDivMod

private theorem polyTime_polyGcdStep :
    ComputableInPolyTime (fun p : List Bool × List Bool => polyGcdStep p)
      (encPair encBits encBits) (encPair encBits encBits) := by
  have hcond := ComputableInPolyTime.bitsIsEmpty.comp
    (ComputableInPolyTime.snd encBits encBits)
  have hres : ComputableInPolyTime
      (fun p : List Bool × List Bool => (p.2, polyMod p.1 p.2))
      (encPair encBits encBits) (encPair encBits encBits) :=
    (ComputableInPolyTime.snd encBits encBits).prod computableInPolyTime_polyMod
  exact (ComputableInPolyTime.ite' hcond
    ComputableInPolyTime.id' hres)

private theorem length_polyGcdStep_le (a b : List Bool) {n : ℕ}
    (ha : a.length ≤ n) (hb : b.length ≤ n) :
    (polyGcdStep (a, b)).1.length ≤ n ∧ (polyGcdStep (a, b)).2.length ≤ n := by
  unfold polyGcdStep
  dsimp only
  split_ifs
  · exact ⟨ha, hb⟩
  · exact ⟨hb, (polyDivMod_iterate_bounds a (polyTrim b) a.length).2.1.trans ha⟩

/-- `polyGcd` is computable in polynomial time. -/
theorem computableInPolyTime_polyGcd :
    ComputableInPolyTime (fun p : List Bool × List Bool => polyGcd p.1 p.2)
      (encPair encBits encBits) encBits := by
  have hpar : ComputableInPolyTime (fun _ : List Bool × List Bool => true)
      (encPair encBits encBits) encBool := .const true
  have hcnt : ComputableInPolyTime
      (fun p : List Bool × List Bool => p.1.length + p.2.length + 1)
      (encPair encBits encBits) encUnary := by
    have h1 := ComputableInPolyTime.length_bits.comp
      (ComputableInPolyTime.fst encBits encBits)
    have h2 := ComputableInPolyTime.length_bits.comp
      (ComputableInPolyTime.snd encBits encBits)
    fun_prop
  have hinit : ComputableInPolyTime
      (fun p : List Bool × List Bool => (polyTrim p.1, polyTrim p.2))
      (encPair encBits encBits) (encPair encBits encBits) :=
    (computableInPolyTime_polyTrim.comp (ComputableInPolyTime.fst encBits encBits)).prod
      (computableInPolyTime_polyTrim.comp (ComputableInPolyTime.snd encBits encBits))
  have hstep : ComputableInPolyTime
      (fun x : Bool × List Bool × List Bool => polyGcdStep x.2)
      (encPair encBool (encPair encBits encBits)) (encPair encBits encBits) :=
    polyTime_polyGcdStep.comp (ComputableInPolyTime.snd encBool (encPair encBits encBits))
  have hmax : ComputableInPolyTime
      (fun p : List Bool × List Bool => max p.1.length p.2.length)
      (encPair encBits encBits) encUnary :=
    ComputableInPolyTime.unary_max.comp
      ((ComputableInPolyTime.length_bits.comp
        (ComputableInPolyTime.fst encBits encBits)).prod
        (ComputableInPolyTime.length_bits.comp
          (ComputableInPolyTime.snd encBits encBits)))
  have hbound : PolyBounded (fun p : List Bool × List Bool => (encPair encBits encBits p).length)
      (fun p : List Bool × List Bool => 3 * max p.1.length p.2.length + 1) :=
    ((PolyBounded.const 3).mul
      (ComputableInPolyTime.polyBounded hmax)).add (PolyBounded.const 1)
  have hiter : ComputableInPolyTime
      (fun p : List Bool × List Bool =>
        (polyGcdStep)^[p.1.length + p.2.length + 1] (polyTrim p.1, polyTrim p.2))
      (encPair encBits encBits) (encPair encBits encBits) :=
    (ComputableInPolyTime.iterateWith_spec
      (step := fun (_ : Bool) x => polyGcdStep x)
      (invariant := fun p _ st =>
        st.1.length ≤ max p.1.length p.2.length ∧ st.2.length ≤ max p.1.length p.2.length)
      hpar hcnt hinit hstep
      (fun p => ⟨(length_polyTrim_le p.1).trans (le_max_left _ _),
        (length_polyTrim_le p.2).trans (le_max_right _ _)⟩)
      (fun p _ _ _ hst => length_polyGcdStep_le _ _ hst.1 hst.2)
      hbound fun p _ st _ hst => by
        rw [length_encPair]
        simp only [encBits_apply]
        omega).1
  exact (ComputableInPolyTime.fst encBits encBits).comp hiter

/-- `polyComposePow` is computable in polynomial time. -/
theorem computableInPolyTime_polyComposePow :
    ComputableInPolyTime (fun p : ℕ × List Bool => polyComposePow p.1 p.2)
      (encPair encUnary encBits) encBits := by
  have hq0 : ComputableInPolyTime (fun p : ℕ × List Bool => decide (p.1 = 0))
      (encPair encUnary encBits) encBool := by
    have hle := ComputableInPolyTime.unary_le'
      (ComputableInPolyTime.fst encUnary encBits) (.const 0)
    convert hle using 1
    funext p
    simp
  have hsum : ComputableInPolyTime
      (fun p : ℕ × List Bool => polyTrim [p.2.foldl xor false])
      (encPair encUnary encBits) encBits := by
    have hfold := ComputableInPolyTime.bitsFoldlWithInput (input := encBits) xor
      ComputableInPolyTime.id' (.const false)
    have hsing : ComputableInPolyTime (fun b : Bool => [b]) encBool encBits :=
      ComputableInPolyTime.of_finite (fun b : Bool => [b])
    exact computableInPolyTime_polyTrim.comp
      (hsing.comp (hfold.comp (ComputableInPolyTime.snd encUnary encBits)))
  have hlen : ComputableInPolyTime (fun p : ℕ × List Bool => p.1 * p.2.length)
      (encPair encUnary encBits) encUnary :=
    ComputableInPolyTime.unary_mul.comp
      ((ComputableInPolyTime.fst encUnary encBits).prod
        (ComputableInPolyTime.length_bits.comp
          (ComputableInPolyTime.snd encUnary encBits)))
  have hcoeff : ComputableInPolyTime
      (fun x : (ℕ × List Bool) × ℕ =>
        if x.2 % x.1.1 == 0 then x.1.2.getD (x.2 / x.1.1) false else false)
      (encPair (encPair encUnary encBits) encUnary) encBool := by
    have hxq := (ComputableInPolyTime.fst encUnary encBits).comp
      (ComputableInPolyTime.fst (encPair encUnary encBits) encUnary)
    have hxp := (ComputableInPolyTime.snd encUnary encBits).comp
      (ComputableInPolyTime.fst (encPair encUnary encBits) encUnary)
    have hxj := ComputableInPolyTime.snd (encPair encUnary encBits) encUnary
    have hdm := ComputableInPolyTime.unary_divMod.comp (hxj.prod hxq)
    have hmod0 : ComputableInPolyTime
        (fun x : (ℕ × List Bool) × ℕ => x.2 % x.1.1 == 0)
        (encPair (encPair encUnary encBits) encUnary) encBool :=
      ((ComputableInPolyTime.snd encUnary encUnary).comp hdm).beq (.const 0)
    have hdiv := (ComputableInPolyTime.fst encUnary encUnary).comp hdm
    have hget := ComputableInPolyTime.bitsGetDWithInput hxp hdiv false
    exact (ComputableInPolyTime.ite' hmod0
      hget (ComputableInPolyTime.const false))
  have hmap : ComputableInPolyTime
      (fun p : ℕ × List Bool =>
        (List.range (p.1 * p.2.length)).map fun j =>
          if j % p.1 == 0 then p.2.getD (j / p.1) false else false)
      (encPair encUnary encBits) (encList encBool) :=
    ComputableInPolyTime.mapWithInput
      (f := fun p j => if j % p.1 == 0 then p.2.getD (j / p.1) false else false)
      (ComputableInPolyTime.range.comp hlen) hcoeff
  have hnz := computableInPolyTime_polyTrim.comp (ComputableInPolyTime.listToBits.comp hmap)
  have hplain := ComputableInPolyTime.ite' hq0
    hsum hnz
  convert hplain using 1
  funext p
  unfold polyComposePow
  simp

/-! ### Gaussian elimination and Berlekamp factoring -/

private def kernelDot (p : List (List Bool) × List Bool) (v : List Bool) : Bool :=
  listDot p.2 v

private def kernelRowStep (par : List (List Bool) × List Bool) (v : List Bool) : List Bool :=
  if listDot par.2 v then
    List.zipWith xor v (par.1.getD ((par.1.map (listDot par.2)).idxOf true) [])
  else v

private theorem polyTime_kernelStepBits :
    ComputableInPolyTime
      (fun p : List (List Bool) × List Bool => kernelStepBits p.2 p.1)
      (encPair (encList encBits) encBits) (encList encBits) := by
  have hN := ComputableInPolyTime.fst (encList encBits) encBits
  have ha := ComputableInPolyTime.snd (encList encBits) encBits
  have hdotEl : ComputableInPolyTime
      (fun x : (List (List Bool) × List Bool) × List Bool => kernelDot x.1 x.2)
      (encPair (encPair (encList encBits) encBits) encBits) encBool :=
    (ComputableInPolyTime.bitsListDot
      (ComputableInPolyTime.fst encBits encBits)
      (ComputableInPolyTime.snd encBits encBits)).comp
      ((ha.comp (ComputableInPolyTime.fst (encPair (encList encBits) encBits) encBits)).prod
        (ComputableInPolyTime.snd (encPair (encList encBits) encBits) encBits))
  have hvals : ComputableInPolyTime
      (fun p : List (List Bool) × List Bool => p.1.map (listDot p.2))
      (encPair (encList encBits) encBits) (encList encBool) :=
    ComputableInPolyTime.mapWithInput (f := kernelDot) hN hdotEl
  have hpIdx : ComputableInPolyTime
      (fun p : List (List Bool) × List Bool => (p.1.map (listDot p.2)).idxOf true)
      (encPair (encList encBits) encBits) encUnary :=
    ComputableInPolyTime.idxOfWithInput (encA := encBool) hvals (.const true)
  have hlenNPlain : ComputableInPolyTime (fun l : List (List Bool) => l.length)
      (encList encBits) encUnary := by fun_prop
  have hlenN : ComputableInPolyTime
      (fun p : List (List Bool) × List Bool => p.1.length)
      (encPair (encList encBits) encBits) encUnary :=
    hlenNPlain.comp hN
  have hcond := ComputableInPolyTime.unary_lt' hpIdx hlenN
  have hpiv : ComputableInPolyTime
      (fun p : List (List Bool) × List Bool => p.1.getD ((p.1.map (listDot p.2)).idxOf true) [])
      (encPair (encList encBits) encBits) encBits := by
    have hget : ComputableInPolyTime (fun p : List (List Bool) × ℕ => p.1.getD p.2 [])
        (encPair (encList encBits) encUnary) encBits := by fun_prop
    exact hget.comp (hN.prod hpIdx)
  have hrowStep : ComputableInPolyTime
      (fun x : (List (List Bool) × List Bool) × List Bool => kernelRowStep x.1 x.2)
      (encPair (encPair (encList encBits) encBits) encBits) encBits := by
    have hxpar := ComputableInPolyTime.fst (encPair (encList encBits) encBits) encBits
    have hxv := ComputableInPolyTime.snd (encPair (encList encBits) encBits) encBits
    have hxa := ha.comp hxpar
    have hdot := (ComputableInPolyTime.bitsListDot
      (ComputableInPolyTime.fst encBits encBits)
      (ComputableInPolyTime.snd encBits encBits)).comp (hxa.prod hxv)
    have hxpiv := hpiv.comp hxpar
    have hxor := (ComputableInPolyTime.bitsZipWith xor).comp (hxv.prod hxpiv)
    exact (ComputableInPolyTime.ite' hdot
      hxor hxv)
  have hmapped := ComputableInPolyTime.mapWithInput (f := kernelRowStep) hN hrowStep
  convert (ComputableInPolyTime.ite' hcond
    hmapped hN) using 1
  funext p
  unfold kernelStepBits kernelRowStep
  simp only [decide_eq_true_eq]

private theorem polyTime_kernelBasisBits :
    ComputableInPolyTime
      (fun p : ℕ × List (List Bool) => kernelBasisBits p.1 p.2)
      (encPair encUnary (encList encBits)) (encList encBits) := by
  have hboundFn : ComputableInPolyTime
      (fun p : ℕ × List (List Bool) => p.1 * (2 * p.1 + 1))
      (encPair encUnary (encList encBits)) encUnary := by
    have := ComputableInPolyTime.fst encUnary (encList encBits)
    fun_prop
  refine ComputableInPolyTime.foldlWith (encA := encBits) (encL := encList encBits)
    (encB := encList encBits)
    (par := fun _ => true)
    (list := fun p : ℕ × List (List Bool) => p.2)
    (step := fun _ N a => kernelStepBits a N)
    (.const true)
    (ComputableInPolyTime.snd encUnary (encList encBits))
    (ComputableInPolyTime.bitsSingles.comp
      (ComputableInPolyTime.fst encUnary (encList encBits)))
    (polyTime_kernelStepBits.comp
      (((ComputableInPolyTime.snd encBool (encList encBits)).comp
        (ComputableInPolyTime.fst (encPair encBool (encList encBits)) encBits)).prod
        (ComputableInPolyTime.snd (encPair encBool (encList encBits)) encBits)))
    (B := fun p : ℕ × List (List Bool) => p.1 * (2 * p.1 + 1))
    (ComputableInPolyTime.polyBounded hboundFn) ?_
  intro p i hi
  obtain ⟨hlen, hrows⟩ := length_kernelBasisBits p.1 (p.2.take i)
  unfold kernelBasisBits at hlen hrows
  refine (length_encList_le encBits _ (b := p.1)
    (fun v hv => by simp [hrows v hv])).trans ?_
  rw [hlen]

/-- `kernelVecBits` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_kernelVecBits :
    ComputableInPolyTime
      (fun p : ℕ × List (List Bool) => kernelVecBits p.1 p.2)
      (encPair encUnary (encList encBits)) encBits := by
  have hany : ComputableInPolyTime
      (fun x : (ℕ × List (List Bool)) × List Bool => x.2.any id)
      (encPair (encPair encUnary (encList encBits)) encBits) encBool :=
    (ComputableInPolyTime.bitsAnyWithInput (test := fun _ b => b)
      ComputableInPolyTime.id'
      (ComputableInPolyTime.snd encBits encBool)).comp
      (ComputableInPolyTime.snd (encPair encUnary (encList encBits)) encBits)
  have hfind := ComputableInPolyTime.findWithInput (encO := encOption encBits)
    (test := fun (_ : ℕ × List (List Bool)) (v : List Bool) => v.any id)
    polyTime_kernelBasisBits hany
  exact ComputableInPolyTime.optionGetDWithInput hfind
    ((ComputableInPolyTime.bitsReplicate false).comp
      (ComputableInPolyTime.fst encUnary (encList encBits)))

private def berlekampCell (x : List Bool × ℕ) (k : ℕ) : Bool :=
  ((powerTable x.1).getD (2 * (k + 1)) []).getD x.2 false ^^ decide ((x.2 == k + 1) = true)

private def berlekampRow (g : List Bool) (i : ℕ) : List Bool :=
  (List.range ((g.length - 1) - 1)).map (berlekampCell (g, i))

private theorem polyTime_berlekampMatrix :
    ComputableInPolyTime berlekampMatrix encBits (encList encBits) := by
  have htab : ComputableInPolyTime powerTable encBits (encList encBits) := by
    have hp : ComputableInPolyTime powerTable encBits (encList encBits) := by fun_prop
    exact hp
  have hd : ComputableInPolyTime (fun g : List Bool => g.length - 1) encBits encUnary :=
    ComputableInPolyTime.unary_sub.comp
      (ComputableInPolyTime.length_bits.prod (.const 1))
  have hcell : ComputableInPolyTime
      (fun x : (List Bool × ℕ) × ℕ => berlekampCell x.1 x.2)
      (encPair (encPair encBits encUnary) encUnary) encBool := by
    unfold berlekampCell
    have hxg := (ComputableInPolyTime.fst encBits encUnary).comp
      (ComputableInPolyTime.fst (encPair encBits encUnary) encUnary)
    have hxi := (ComputableInPolyTime.snd encBits encUnary).comp
      (ComputableInPolyTime.fst (encPair encBits encUnary) encUnary)
    have hxk := ComputableInPolyTime.snd (encPair encBits encUnary) encUnary
    have htabx := htab.comp hxg
    have hj : ComputableInPolyTime
        (fun x : (List Bool × ℕ) × ℕ => x.2 + 1)
        (encPair (encPair encBits encUnary) encUnary) encUnary :=
      ComputableInPolyTime.unary_add.comp (hxk.prod (.const 1))
    have h2j : ComputableInPolyTime
        (fun x : (List Bool × ℕ) × ℕ => 2 * (x.2 + 1))
        (encPair (encPair encBits encUnary) encUnary) encUnary :=
      ComputableInPolyTime.unary_mul.comp
        ((ComputableInPolyTime.const 2).prod hj)
    have hget : ComputableInPolyTime (fun p : List (List Bool) × ℕ => p.1.getD p.2 [])
        (encPair (encList encBits) encUnary) encBits := by fun_prop
    have hrow := hget.comp (htabx.prod h2j)
    have hbit := ComputableInPolyTime.bitsGetDWithInput hrow hxi false
    have hdiag : ComputableInPolyTime
        (fun x : (List Bool × ℕ) × ℕ => decide ((x.1.2 == x.2 + 1) = true))
        (encPair (encPair encBits encUnary) encUnary) encBool := by
      convert hxi.beq hj using 1
      funext x
      rw [Bool.eq_iff_iff]
      simp
    exact (ComputableInPolyTime.of_finite (fun b : Bool × Bool => b.1 ^^ b.2)
      (encIn := encPair encBool encBool) (encOut := encBool)).comp (hbit.prod hdiag)
  have hrow : ComputableInPolyTime
      (fun x : List Bool × ℕ => berlekampRow x.1 x.2)
      (encPair encBits encUnary) encBits := by
    have hdr := ComputableInPolyTime.range.comp
      (ComputableInPolyTime.unary_sub.comp
        ((hd.comp (ComputableInPolyTime.fst encBits encUnary)).prod (.const 1)))
    exact ComputableInPolyTime.listToBits.comp
      (ComputableInPolyTime.mapWithInput (f := berlekampCell) hdr hcell)
  have hres := ComputableInPolyTime.mapWithInput (f := berlekampRow)
    (ComputableInPolyTime.range.comp hd) hrow
  convert hres using 1
  funext g
  unfold berlekampMatrix berlekampRow berlekampCell
  rfl

private theorem polyTime_berlekampStep :
    ComputableInPolyTime berlekampStep encBits encBits := by
  have hgt := computableInPolyTime_polyTrim
  have hlen := ComputableInPolyTime.length_bits.comp hgt
  have hle2 := ComputableInPolyTime.unary_le' hlen (.const 2)
  have hd2 : ComputableInPolyTime (fun g : List Bool => (polyTrim g).length - 2)
      encBits encUnary :=
    ComputableInPolyTime.unary_sub.comp (hlen.prod (.const 2))
  have hvec : ComputableInPolyTime
      (fun g : List Bool => kernelVecBits ((polyTrim g).length - 2) (berlekampMatrix (polyTrim g)))
      encBits encBits :=
    computableInPolyTime_kernelVecBits.comp (hd2.prod (polyTime_berlekampMatrix.comp hgt))
  have hany : ComputableInPolyTime
      (fun g : List Bool =>
        (kernelVecBits ((polyTrim g).length - 2) (berlekampMatrix (polyTrim g))).any id)
      encBits encBool :=
    (ComputableInPolyTime.bitsAnyWithInput (test := fun _ b => b)
      ComputableInPolyTime.id'
      (ComputableInPolyTime.snd encBits encBool)).comp hvec
  have hgcd := computableInPolyTime_polyGcd.comp
    (hgt.prod (ComputableInPolyTime.bitsCons (.const false) hvec))
  have hinner := (ComputableInPolyTime.ite' hany
    hgcd hgt)
  convert (ComputableInPolyTime.ite' hle2
    hgt hinner) using 1
  funext g
  unfold berlekampStep
  simp only [Function.comp_def, decide_eq_true_eq]

private theorem length_berlekampStep_le (g : List Bool) :
    (berlekampStep g).length ≤ g.length := by
  unfold berlekampStep
  dsimp only
  set gt := polyTrim g
  have hgt : gt.length ≤ g.length := length_polyTrim_le g
  split_ifs with h1 h2
  · exact hgt
  · have hv : (kernelVecBits (gt.length - 2) (berlekampMatrix gt)).length = gt.length - 2 :=
      length_kernelVecBits _ _
    let w := false :: kernelVecBits (gt.length - 2) (berlekampMatrix gt)
    have hgcd : (polyGcd gt w).length ≤ max gt.length w.length :=
      (polyGcd_iterate_bounds gt w (gt.length + w.length + 1)).1
    simp only [w, List.length_cons, hv] at hgcd
    omega
  · exact hgt

private theorem polyTime_berlekampIrreducibleFactor :
    ComputableInPolyTime berlekampIrreducibleFactor encBits encBits := by
  have hpar : ComputableInPolyTime (fun _ : List Bool => true) encBits encBool := .const true
  have hcnt := ComputableInPolyTime.length_bits
  have hinit := computableInPolyTime_polyTrim
  have hstep : ComputableInPolyTime
      (fun x : Bool × List Bool => berlekampStep x.2)
      (encPair encBool encBits) encBits :=
    polyTime_berlekampStep.comp (ComputableInPolyTime.snd encBool encBits)
  exact (ComputableInPolyTime.iterateWith_spec
    (step := fun (_ : Bool) f => berlekampStep f)
    (invariant := fun g _ f => f.length ≤ g.length)
    hpar hcnt hinit hstep
    (fun g => length_polyTrim_le g)
    (fun g _ f _ hf => (length_berlekampStep_le f).trans hf)
    PolyBounded.self fun _ _ _ _ hf => by
      simpa only [encBits_apply] using hf).1

private theorem getD_length_le_encList_bits (L : List (List Bool)) (i : ℕ) :
    (L.getD i []).length ≤ (encList encBits L).length := by
  rw [List.getD_eq_getElem?_getD]
  cases h : L[i]? with
  | none => simp
  | some v =>
    simp only [Option.getD_some]
    simpa only [encBits_apply] using length_le_encList_of_mem encBits (List.mem_of_getElem? h)

private theorem length_polyMod_lt {u f : List Bool} (hf : (polyTrim f).isEmpty = false) :
    (polyMod u f).length < (polyTrim f).length := by
  have hbt_ne : polyTrim f ≠ [] := by
    intro hnil
    rw [hnil] at hf
    simp at hf
  have hf0 : polyOfBits f ≠ 0 := polyOfBits_ne_zero_iff_polyTrim.mpr hbt_ne
  exact (polyOfBits_polyDivMod_spec (a := u) hf0).2.1

private theorem length_polyMul_le' (a b : List Bool) :
    (polyMul a b).length ≤ a.length + b.length := by
  unfold polyMul
  split_ifs
  · simp
  · exact (length_polyTrim_le _).trans (by simp)

private theorem polyTime_primeGeThree :
    ComputableInPolyTime (fun q : ℕ => decide (q.Prime ∧ 3 ≤ q)) encUnary encBool := by
  have hprimePlain : ComputableInPolyTime (fun q : ℕ => decide q.Prime) encUnary encBool := by
    fun_prop
  have hge3 := ComputableInPolyTime.unary_le' (.const 3) ComputableInPolyTime.id'
  have hand := (ComputableInPolyTime.of_finite (fun b : Bool × Bool => b.1 && b.2)
    (encIn := encPair encBool encBool) (encOut := encBool)).comp (hprimePlain.prod hge3)
  convert hand using 1
  funext q
  simp

private theorem polyTime_shoupCyclicFactorBounded :
    ComputableInPolyTime
      (fun q : ℕ =>
        (fun f => berlekampIrreducibleFactor (polyComposePow q f))^[
          if q.Prime ∧ 3 ≤ q then qAdicValTwoPowSubOne q (ordTwoMod q) - 1 else 0]
          (berlekampIrreducibleFactor (List.replicate q true)))
      encUnary encBits := by
  have hcond := polyTime_primeGeThree
  have hk := computableInPolyTime_qAdicValTwoPowSubOne.comp
    (ComputableInPolyTime.id'.prod computableInPolyTime_ordTwoMod)
  have hcntTrue := ComputableInPolyTime.unary_sub.comp (hk.prod (.const 1))
  have hcnt : ComputableInPolyTime
      (fun q : ℕ => if q.Prime ∧ 3 ≤ q then qAdicValTwoPowSubOne q (ordTwoMod q) - 1 else 0)
      encUnary encUnary := by
    have hite := (ComputableInPolyTime.ite' hcond
      hcntTrue (ComputableInPolyTime.const (0 : ℕ)))
    convert hite using 1
    funext q
    by_cases h : q.Prime ∧ 3 ≤ q <;> simp [h]
  have hinit : ComputableInPolyTime
      (fun q : ℕ => berlekampIrreducibleFactor (List.replicate q true)) encUnary encBits :=
    polyTime_berlekampIrreducibleFactor.comp (ComputableInPolyTime.bitsReplicate true)
  have hstep : ComputableInPolyTime
      (fun x : ℕ × List Bool => berlekampIrreducibleFactor (polyComposePow x.1 x.2))
      (encPair encUnary encBits) encBits :=
    polyTime_berlekampIrreducibleFactor.comp computableInPolyTime_polyComposePow
  have hbound : PolyBounded (fun q : ℕ => (encUnary q).length) (fun q : ℕ => q) :=
    ComputableInPolyTime.polyBounded ComputableInPolyTime.id'
  refine (ComputableInPolyTime.iterateWith_spec
    (invariant := fun q k g =>
      g = (fun f => berlekampIrreducibleFactor (polyComposePow q f))^[k]
        (berlekampIrreducibleFactor (List.replicate q true)))
    ComputableInPolyTime.id' hcnt hinit hstep
    (fun _ => rfl)
    (fun q k g _ hg => by rw [hg, Function.iterate_succ_apply'])
    hbound ?_).1
  intro q k g hk hg
  simp only [encBits_apply]
  rw [hg]
  by_cases h : q.Prime ∧ 3 ≤ q
  · rw [ite_eq_left_iff.mpr (fun hnot => absurd h hnot)] at hk
    exact length_shoupCyclicFactor_iterate_le h.1 h.2 hk
  · rw [ite_eq_right_iff.mpr (fun hpos => absurd hpos h)] at hk
    have hk0 : k = 0 := by omega
    subst hk0
    rw [Function.iterate_zero_apply]
    unfold berlekampIrreducibleFactor
    have hinv : ∀ s, ((berlekampStep)^[s] (polyTrim (List.replicate q true))).length ≤ q := by
      intro s
      induction s with
      | zero => exact (length_polyTrim_le _).trans (by simp)
      | succ s ih => rw [Function.iterate_succ_apply']; exact (length_berlekampStep_le _).trans ih
    simpa only [List.length_replicate] using hinv q

private theorem polyTime_shoupLAdd :
    ComputableInPolyTime
      (fun p : ℕ × List (List Bool) × List (List Bool) => shoupLAdd p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair (encList encBits) (encList encBits))) (encList encBits) := by
  have hget : ComputableInPolyTime (fun p : List (List Bool) × ℕ => p.1.getD p.2 [])
      (encPair (encList encBits) encUnary) encBits := by fun_prop
  have hcell : ComputableInPolyTime
      (fun x : (ℕ × List (List Bool) × List (List Bool)) × ℕ =>
        polyAdd (x.1.2.1.getD x.2 []) (x.1.2.2.getD x.2 []))
      (encPair (encPair encUnary (encPair (encList encBits) (encList encBits))) encUnary)
      encBits := by
    have hxpar := ComputableInPolyTime.fst
      (encPair encUnary (encPair (encList encBits) (encList encBits))) encUnary
    have hxi := ComputableInPolyTime.snd
      (encPair encUnary (encPair (encList encBits) (encList encBits))) encUnary
    have hxs := (ComputableInPolyTime.snd encUnary
      (encPair (encList encBits) (encList encBits))).comp hxpar
    have hxa := (ComputableInPolyTime.fst (encList encBits) (encList encBits)).comp hxs
    have hxb := (ComputableInPolyTime.snd (encList encBits) (encList encBits)).comp hxs
    exact computableInPolyTime_polyAdd.comp
      ((hget.comp (hxa.prod hxi)).prod (hget.comp (hxb.prod hxi)))
  have hres := ComputableInPolyTime.mapWithInput
    (f := fun p i => polyAdd (p.2.1.getD i []) (p.2.2.getD i []))
    (ComputableInPolyTime.range.comp
      (ComputableInPolyTime.fst encUnary (encPair (encList encBits) (encList encBits))))
    hcell
  exact hres

private def shoupLMulSum (a b : List (List Bool)) (cnt off1 off2 : ℕ) : List Bool :=
  (List.range cnt).foldl
    (fun acc t => polyAdd acc (polyMul (a.getD (off1 + t) []) (b.getD (off2 - t) []))) []

private theorem length_foldl_shoupLMulSum_le (a b : List (List Bool)) (off1 off2 : ℕ)
    (L : List ℕ) :
    (L.foldl (fun acc t => polyAdd acc (polyMul (a.getD (off1 + t) []) (b.getD (off2 - t) [])))
      []).length ≤ (encList encBits a).length + (encList encBits b).length := by
  have hstep_gen : ∀ acc : List Bool,
      acc.length ≤ (encList encBits a).length + (encList encBits b).length →
      (L.foldl (fun acc t => polyAdd acc (polyMul (a.getD (off1 + t) []) (b.getD (off2 - t) [])))
        acc).length ≤ (encList encBits a).length + (encList encBits b).length := by
    intro acc hacc
    induction L generalizing acc with
    | nil => exact hacc
    | cons t L ih =>
      rw [List.foldl_cons]
      apply ih
      refine (length_polyAdd_le _ _).trans (max_le hacc ?_)
      refine (length_polyMul_le' _ _).trans ?_
      exact Nat.add_le_add (getD_length_le_encList_bits a _) (getD_length_le_encList_bits b _)
  exact hstep_gen [] (by simp)

private theorem polyTime_shoupLMulSum :
    ComputableInPolyTime
      (fun p : (List (List Bool) × List (List Bool)) × (ℕ × ℕ × ℕ) =>
        shoupLMulSum p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2)
      (encPair (encPair (encList encBits) (encList encBits))
        (encPair encUnary (encPair encUnary encUnary)))
      encBits := by
  have hget : ComputableInPolyTime (fun p : List (List Bool) × ℕ => p.1.getD p.2 [])
      (encPair (encList encBits) encUnary) encBits := by fun_prop
  have hstep : ComputableInPolyTime
      (fun x : (((List (List Bool) × List (List Bool)) × (ℕ × ℕ)) × List Bool) × ℕ =>
        polyAdd x.1.2
          (polyMul (x.1.1.1.1.getD (x.1.1.2.1 + x.2) [])
            (x.1.1.1.2.getD (x.1.1.2.2 - x.2) [])))
      (encPair (encPair (encPair (encPair (encList encBits) (encList encBits))
        (encPair encUnary encUnary)) encBits) encUnary)
      encBits := by
    have hfront := ComputableInPolyTime.fst
      (encPair (encPair (encPair (encList encBits) (encList encBits)) (encPair encUnary encUnary))
        encBits) encUnary
    have hpar := (ComputableInPolyTime.fst
      (encPair (encPair (encList encBits) (encList encBits)) (encPair encUnary encUnary))
      encBits).comp hfront
    have hacc := (ComputableInPolyTime.snd
      (encPair (encPair (encList encBits) (encList encBits)) (encPair encUnary encUnary))
      encBits).comp hfront
    have ht := ComputableInPolyTime.snd
      (encPair (encPair (encPair (encList encBits) (encList encBits)) (encPair encUnary encUnary))
        encBits) encUnary
    have hab := (ComputableInPolyTime.fst
      (encPair (encList encBits) (encList encBits)) (encPair encUnary encUnary)).comp hpar
    have hoffs := (ComputableInPolyTime.snd
      (encPair (encList encBits) (encList encBits)) (encPair encUnary encUnary)).comp hpar
    have ha := (ComputableInPolyTime.fst (encList encBits) (encList encBits)).comp hab
    have hb := (ComputableInPolyTime.snd (encList encBits) (encList encBits)).comp hab
    have ho1 := (ComputableInPolyTime.fst encUnary encUnary).comp hoffs
    have ho2 := (ComputableInPolyTime.snd encUnary encUnary).comp hoffs
    have hidx1 := ComputableInPolyTime.unary_add.comp (ho1.prod ht)
    have hidx2 := ComputableInPolyTime.unary_sub.comp (ho2.prod ht)
    have haGet := hget.comp (ha.prod hidx1)
    have hbGet := hget.comp (hb.prod hidx2)
    exact computableInPolyTime_polyAdd.comp
      (hacc.prod (computableInPolyTime_polyMul.comp (haGet.prod hbGet)))
  have hparFn : ComputableInPolyTime
      (fun p : (List (List Bool) × List (List Bool)) × (ℕ × ℕ × ℕ) => (p.1, p.2.2))
      (encPair (encPair (encList encBits) (encList encBits))
        (encPair encUnary (encPair encUnary encUnary)))
      (encPair (encPair (encList encBits) (encList encBits)) (encPair encUnary encUnary)) :=
    (ComputableInPolyTime.fst (encPair (encList encBits) (encList encBits))
      (encPair encUnary (encPair encUnary encUnary))).prod
      ((ComputableInPolyTime.snd encUnary (encPair encUnary encUnary)).comp
        (ComputableInPolyTime.snd (encPair (encList encBits) (encList encBits))
          (encPair encUnary (encPair encUnary encUnary))))
  have hlistFn : ComputableInPolyTime
      (fun p : (List (List Bool) × List (List Bool)) × (ℕ × ℕ × ℕ) => List.range p.2.1)
      (encPair (encPair (encList encBits) (encList encBits))
        (encPair encUnary (encPair encUnary encUnary)))
      (encList encUnary) :=
    ComputableInPolyTime.range.comp
      ((ComputableInPolyTime.fst encUnary (encPair encUnary encUnary)).comp
        (ComputableInPolyTime.snd (encPair (encList encBits) (encList encBits))
          (encPair encUnary (encPair encUnary encUnary))))
  have hbound : PolyBounded
      (fun p : (List (List Bool) × List (List Bool)) × (ℕ × ℕ × ℕ) =>
        (encPair (encPair (encList encBits) (encList encBits))
          (encPair encUnary (encPair encUnary encUnary)) p).length)
      (fun p => (encList encBits p.1.1).length + (encList encBits p.1.2).length) := by
    have hab := ComputableInPolyTime.fst (encPair (encList encBits) (encList encBits))
      (encPair encUnary (encPair encUnary encUnary))
    have ha := ComputableInPolyTime.length_bits.comp
      (ComputableInPolyTime.encoding_comp
        ((ComputableInPolyTime.fst (encList encBits) (encList encBits)).comp hab))
    have hb := ComputableInPolyTime.length_bits.comp
      (ComputableInPolyTime.encoding_comp
        ((ComputableInPolyTime.snd (encList encBits) (encList encBits)).comp hab))
    exact ComputableInPolyTime.polyBounded
      (ComputableInPolyTime.unary_add.comp (ha.prod hb))
  exact ComputableInPolyTime.foldlWith
    (encA := encUnary) (encL := encList encUnary) (encB := encBits)
    (par := fun p : (List (List Bool) × List (List Bool)) × (ℕ × ℕ × ℕ) => (p.1, p.2.2))
    (list := fun p => List.range p.2.1)
    (step := fun par acc t =>
      polyAdd acc (polyMul (par.1.1.getD (par.2.1 + t) []) (par.1.2.getD (par.2.2 - t) [])))
    hparFn hlistFn (.const ([] : List Bool)) hstep hbound fun p i _ => by
      simpa only [encBits_apply] using length_foldl_shoupLMulSum_le p.1.1 p.1.2 p.2.2.1 p.2.2.2
        ((List.range p.2.1).take i)

private def shoupLMulCell
    (p : (ℕ × List Bool) × (List (List Bool) × List (List Bool))) (k : ℕ) : List Bool :=
  let low := shoupLMulSum p.2.1 p.2.2 (k + 1) 0 k
  let high := shoupLMulSum p.2.1 p.2.2 (p.1.1 - 1 - k) (k + 1) (p.1.1 - 1)
  polyMod (polyAdd low (false :: high)) p.1.2

private theorem polyTime_shoupLMul :
    ComputableInPolyTime
      (fun p : (ℕ × List Bool) × (List (List Bool) × List (List Bool)) =>
        shoupLMul p.1.1 p.1.2 p.2.1 p.2.2)
      (encPair (encPair encUnary encBits) (encPair (encList encBits) (encList encBits)))
      (encList encBits) := by
  let encCtx := encPair
    (encPair (encPair encUnary encBits) (encPair (encList encBits) (encList encBits))) encUnary
  have hcell : ComputableInPolyTime
      (fun x : ((ℕ × List Bool) × (List (List Bool) × List (List Bool))) × ℕ =>
        shoupLMulCell x.1 x.2)
      encCtx encBits := by
    have hxpar := ComputableInPolyTime.fst
      (encPair (encPair encUnary encBits) (encPair (encList encBits) (encList encBits))) encUnary
    have hxk := ComputableInPolyTime.snd
      (encPair (encPair encUnary encBits) (encPair (encList encBits) (encList encBits))) encUnary
    have hqf := (ComputableInPolyTime.fst (encPair encUnary encBits)
      (encPair (encList encBits) (encList encBits))).comp hxpar
    have hab := (ComputableInPolyTime.snd (encPair encUnary encBits)
      (encPair (encList encBits) (encList encBits))).comp hxpar
    have hq := (ComputableInPolyTime.fst encUnary encBits).comp hqf
    have hf := (ComputableInPolyTime.snd encUnary encBits).comp hqf
    have h1 : ComputableInPolyTime
        (fun _ : ((ℕ × List Bool) × (List (List Bool) × List (List Bool))) × ℕ => (1 : ℕ))
        encCtx encUnary :=
      ComputableInPolyTime.const (1 : ℕ)
    have h0 : ComputableInPolyTime
        (fun _ : ((ℕ × List Bool) × (List (List Bool) × List (List Bool))) × ℕ => (0 : ℕ))
        encCtx encUnary :=
      ComputableInPolyTime.const (0 : ℕ)
    have hk1 := ComputableInPolyTime.unary_add.comp (hxk.prod h1)
    have hq1 := ComputableInPolyTime.unary_sub.comp (hq.prod h1)
    have hcntH := ComputableInPolyTime.unary_sub.comp (hq1.prod hxk)
    have hlow := polyTime_shoupLMulSum.comp (hab.prod (hk1.prod (h0.prod hxk)))
    have hhigh := polyTime_shoupLMulSum.comp (hab.prod (hcntH.prod (hk1.prod hq1)))
    have hsum := computableInPolyTime_polyAdd.comp
      (hlow.prod (ComputableInPolyTime.bitsCons (.const false) hhigh))
    exact computableInPolyTime_polyMod.comp (hsum.prod hf)
  have hres := ComputableInPolyTime.mapWithInput (f := shoupLMulCell)
    (ComputableInPolyTime.range.comp
      ((ComputableInPolyTime.fst encUnary encBits).comp
        (ComputableInPolyTime.fst (encPair encUnary encBits)
          (encPair (encList encBits) (encList encBits)))))
    hcell
  convert hres using 1
  funext p
  unfold shoupLMul
  refine congrArg (fun fn => List.map fn (List.range p.1.1)) ?_
  funext k
  dsimp only [shoupLMulCell, shoupLMulSum]
  have hidx : ∀ t, p.1.1 + k - (k + 1 + t) = p.1.1 - 1 - t := fun t => by omega
  simp [hidx]

private theorem length_shoupLMul (q : ℕ) (f : List Bool) (a b : List (List Bool))
    (hf : (polyTrim f).isEmpty = false) :
    (shoupLMul q f a b).length = q ∧ ∀ v ∈ shoupLMul q f a b, v.length ≤ f.length := by
  unfold shoupLMul
  refine ⟨by simp, fun v hv => ?_⟩
  rw [List.mem_map] at hv
  rcases hv with ⟨k, _, rfl⟩
  exact (length_polyMod_lt hf).le.trans (length_polyTrim_le f)

private def shoupFrobStep (p : ℕ × List Bool) (x : List (List Bool)) : List (List Bool) :=
  shoupLMul p.1 p.2 x x

private def shoupLFrobQBounded (q : ℕ) (f : List Bool) (a : List (List Bool)) :
    List (List Bool) :=
  (shoupFrobStep (q, f))^[if (polyTrim f).isEmpty then 0 else q] a

private theorem shoupLFrobQBounded_eq {q : ℕ} {f : List Bool} (a : List (List Bool))
    (hf : (polyTrim f).isEmpty = false) :
    shoupLFrobQBounded q f a = shoupLFrobQ q f a := by
  unfold shoupLFrobQBounded shoupLFrobQ shoupFrobStep
  simp [hf]

section ShoupFrobSection
attribute [local irreducible] shoupLMul shoupFrobStep polyTrim

private theorem polyTime_shoupLFrobQBounded :
    ComputableInPolyTime
      (fun p : (ℕ × List Bool) × List (List Bool) => shoupLFrobQBounded p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encBits) (encList encBits)) (encList encBits) := by
  have hpar := ComputableInPolyTime.fst (encPair encUnary encBits) (encList encBits)
  have ha := ComputableInPolyTime.snd (encPair encUnary encBits) (encList encBits)
  have hq := (ComputableInPolyTime.fst encUnary encBits).comp hpar
  have hf := (ComputableInPolyTime.snd encUnary encBits).comp hpar
  have hcond := ComputableInPolyTime.bitsIsEmpty.comp (computableInPolyTime_polyTrim.comp hf)
  have hcnt : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × List (List Bool) => if (polyTrim p.1.2).isEmpty then 0 else p.1.1)
      (encPair (encPair encUnary encBits) (encList encBits)) encUnary :=
    (ComputableInPolyTime.ite' hcond
      (ComputableInPolyTime.const (0 : ℕ)) hq)
  have hstep := polyTime_shoupLMul.comp ((ComputableInPolyTime.fst (encPair encUnary encBits)
    (encList encBits)).prod ((ComputableInPolyTime.snd (encPair encUnary encBits)
      (encList encBits)).prod (ComputableInPolyTime.snd (encPair encUnary encBits)
        (encList encBits))))
  have hstep' : ComputableInPolyTime
      (fun x : (ℕ × List Bool) × List (List Bool) => shoupFrobStep x.1 x.2)
      (encPair (encPair encUnary encBits) (encList encBits)) (encList encBits) := by
    convert hstep using 1
    funext x
    unfold shoupFrobStep
    rfl
  have haLenPlain : ComputableInPolyTime (fun l : List (List Bool) => l.length)
      (encList encBits) encUnary := by fun_prop
  have haLen := haLenPlain.comp ha
  have haBits := ComputableInPolyTime.length_bits.comp
    (ComputableInPolyTime.encoding_comp ha)
  have hfLen := ComputableInPolyTime.length_bits.comp hf
  have hsizeFn : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × List (List Bool) =>
        (p.1.1 + p.2.length) * (2 * (p.1.2.length + (encList encBits p.2).length) + 1))
      (encPair (encPair encUnary encBits) (encList encBits)) encUnary := by
    have hq' := hq
    have ha' := haLen
    have hf' := hfLen
    have hab' := haBits
    have hsum1 := ComputableInPolyTime.unary_add.comp (hq'.prod ha')
    have hsum2 := ComputableInPolyTime.unary_add.comp (hf'.prod hab')
    have hmul2 := ComputableInPolyTime.unary_mul.comp
      ((ComputableInPolyTime.const 2).prod hsum2)
    have hadd1 := ComputableInPolyTime.unary_add.comp
      (hmul2.prod (ComputableInPolyTime.const 1))
    exact ComputableInPolyTime.unary_mul.comp (hsum1.prod hadd1)
  have hiter := (ComputableInPolyTime.iterateWith_spec
    (step := shoupFrobStep)
    (invariant := fun p _ x =>
      x.length ≤ p.1.1 + p.2.length ∧
        ∀ v ∈ x, v.length ≤ p.1.2.length + (encList encBits p.2).length)
    hpar hcnt ha hstep'
    (fun p => ⟨Nat.le_add_left _ _, fun v hv => by
      simpa only [encBits_apply] using
        (length_le_encList_of_mem encBits hv).trans (Nat.le_add_left _ _)⟩)
    (fun p k x hk _ => by
      have hf_ne : (polyTrim p.1.2).isEmpty = false := by
        by_contra h
        simp only [Bool.not_eq_false] at h
        rw [ite_eq_left_iff.mpr (fun hnot => absurd h hnot)] at hk
        omega
      unfold shoupFrobStep
      obtain ⟨hl, hrows⟩ := length_shoupLMul p.1.1 p.1.2 x x hf_ne
      exact ⟨by omega, fun v hv => (hrows v hv).trans (Nat.le_add_right _ _)⟩)
    (ComputableInPolyTime.polyBounded hsizeFn) fun p _ x _ hx => by
      refine (length_encList_le encBits x (b := p.1.2.length + (encList encBits p.2).length)
        (fun v hv => hx.2 v hv)).trans ?_
      exact Nat.mul_le_mul_right _ hx.1).1
  exact hiter

end ShoupFrobSection

private theorem foldl_range_const_eq {α : Type*} (step : α → α) (init : α) (n : ℕ) :
    (List.range n).foldl (fun x _ => step x) init = step^[n] init := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih,
      Function.iterate_succ_apply']

private def shoupBetaInitYCell (_ q_i : ℕ) : List Bool :=
  if (q_i == 1) = true then [true] else []

private def shoupBetaStep (p : ℕ × List Bool) (st : List (List Bool) × List (List Bool)) :
    List (List Bool) × List (List Bool) :=
  (shoupLAdd p.1 st.1 st.2, shoupLFrobQBounded p.1 p.2 st.2)

private def shoupBetaBounded (q : ℕ) (f : List Bool) : List (List Bool) :=
  ((shoupBetaStep (q, f))^[if (polyTrim f).isEmpty then 0 else f.length - 1]
    (List.replicate q [], (List.range q).map (shoupBetaInitYCell q))).1

private theorem shoupBetaBounded_eq {q : ℕ} {f : List Bool} (hf : (polyTrim f).isEmpty = false) :
    shoupBetaBounded q f = shoupBeta q f := by
  unfold shoupBetaBounded shoupBeta shoupBetaStep
  simp only [hf, Bool.false_eq_true, ↓reduceIte]
  rw [← foldl_range_const_eq]
  congr 1
  refine congrArg (fun g => List.foldl g _ (List.range (f.length - 1))) ?_
  funext st _
  rw [shoupLFrobQBounded_eq _ hf]

section ShoupBetaSection
attribute [local irreducible] shoupLAdd shoupLFrobQBounded shoupBetaStep polyTrim

private theorem polyTime_shoupBetaBounded :
    ComputableInPolyTime
      (fun p : ℕ × List Bool => shoupBetaBounded p.1 p.2)
      (encPair encUnary encBits) (encList encBits) := by
  have hq := ComputableInPolyTime.fst encUnary encBits
  have hf := ComputableInPolyTime.snd encUnary encBits
  have hfne := ComputableInPolyTime.bitsIsEmpty.comp (computableInPolyTime_polyTrim.comp hf)
  have hcntTrue := ComputableInPolyTime.unary_sub.comp
    ((ComputableInPolyTime.length_bits.comp hf).prod (.const 1))
  have hcnt : ComputableInPolyTime
      (fun p : ℕ × List Bool => if (polyTrim p.2).isEmpty then 0 else p.2.length - 1)
      (encPair encUnary encBits) encUnary :=
    (ComputableInPolyTime.ite' hfne
      (ComputableInPolyTime.const (0 : ℕ)) hcntTrue)
  have hinitY : ComputableInPolyTime
      (fun q : ℕ => (List.range q).map (shoupBetaInitYCell q))
      encUnary (encList encBits) := by
    have hbit : ComputableInPolyTime
        (fun x : ℕ × ℕ => shoupBetaInitYCell x.1 x.2)
        (encPair encUnary encUnary) encBits := by
      have hi := ComputableInPolyTime.snd encUnary encUnary
      have hcond : ComputableInPolyTime (fun x : ℕ × ℕ => x.2 == 1)
          (encPair encUnary encUnary) encBool :=
        hi.beq (.const 1)
      exact (ComputableInPolyTime.ite' hcond
        (ComputableInPolyTime.const [true]) (ComputableInPolyTime.const ([] : List Bool)))
    exact ComputableInPolyTime.mapWithInput (f := shoupBetaInitYCell)
      ComputableInPolyTime.range hbit
  have hinit1 : ComputableInPolyTime
      (fun p : ℕ × List Bool => List.replicate p.1 ([] : List Bool))
      (encPair encUnary encBits) (encList encBits) :=
    ComputableInPolyTime.replicate hq (ComputableInPolyTime.const ([] : List Bool))
  have hinit := hinit1.prod (hinitY.comp hq)
  have hstep : ComputableInPolyTime
      (fun x : (ℕ × List Bool) × (List (List Bool) × List (List Bool)) =>
        shoupBetaStep x.1 x.2)
      (encPair (encPair encUnary encBits) (encPair (encList encBits) (encList encBits)))
      (encPair (encList encBits) (encList encBits)) := by
    have hxpar := ComputableInPolyTime.fst (encPair encUnary encBits)
      (encPair (encList encBits) (encList encBits))
    have hxst := ComputableInPolyTime.snd (encPair encUnary encBits)
      (encPair (encList encBits) (encList encBits))
    have hxq := (ComputableInPolyTime.fst encUnary encBits).comp hxpar
    have hx2 := (ComputableInPolyTime.snd (encList encBits) (encList encBits)).comp hxst
    have hpair := (polyTime_shoupLAdd.comp (hxq.prod hxst)).prod
      (polyTime_shoupLFrobQBounded.comp (hxpar.prod hx2))
    convert hpair using 1
    funext x
    unfold shoupBetaStep
    rfl
  have hboundFn : ComputableInPolyTime
      (fun p : ℕ × List Bool => 3 * (p.1 * (2 * (p.2.length + 1) + 1)) + 1)
      (encPair encUnary encBits) encUnary := by
    have hq' := hq
    have hf1 := ComputableInPolyTime.unary_add.comp
      ((ComputableInPolyTime.length_bits.comp hf).prod (.const 1))
    have h2f := ComputableInPolyTime.unary_mul.comp
      ((ComputableInPolyTime.const 2).prod hf1)
    have h2f1 := ComputableInPolyTime.unary_add.comp (h2f.prod (.const 1))
    have hqmul := ComputableInPolyTime.unary_mul.comp (hq'.prod h2f1)
    have h3q := ComputableInPolyTime.unary_mul.comp
      ((ComputableInPolyTime.const 3).prod hqmul)
    exact ComputableInPolyTime.unary_add.comp (h3q.prod (.const 1))
  have hgetD_le : ∀ (L : List (List Bool)) (m : ℕ),
      (∀ v ∈ L, v.length ≤ m) → ∀ i, (L.getD i []).length ≤ m := by
    intro L m hL i
    rw [List.getD_eq_getElem?_getD]
    cases hopt : L[i]? with
    | none => simp
    | some u => simp only [Option.getD_some]; exact hL u (List.mem_of_getElem? hopt)
  have hiter := (ComputableInPolyTime.iterateWith_spec
    (invariant := fun p _ st =>
      st.1.length ≤ p.1 ∧ st.2.length ≤ p.1 ∧
        (∀ v ∈ st.1, v.length ≤ p.2.length + 1) ∧ ∀ v ∈ st.2, v.length ≤ p.2.length + 1)
    ComputableInPolyTime.id' hcnt hinit hstep
    (fun p => by
      refine ⟨by simp, by simp, fun v hv => ?_, fun v hv => ?_⟩
      · simp only [List.mem_replicate] at hv
        rw [hv.2]
        simp
      · dsimp only [Function.comp_def] at hv
        rw [List.mem_map] at hv
        rcases hv with ⟨i, _, rfl⟩
        unfold shoupBetaInitYCell
        split_ifs <;> simp)
    (fun p k st hk hinv => by
      have hf_ne : (polyTrim p.2).isEmpty = false := by
        by_contra h
        simp only [Bool.not_eq_false] at h
        rw [ite_eq_left_iff.mpr (fun hnot => absurd h hnot)] at hk
        omega
      have h1 : (shoupLAdd p.1 st.1 st.2).length ≤ p.1 := by
        simp [shoupLAdd]
      have h1_rows : ∀ v ∈ shoupLAdd p.1 st.1 st.2, v.length ≤ p.2.length + 1 := by
        intro v hv
        unfold shoupLAdd at hv
        rw [List.mem_map] at hv
        rcases hv with ⟨i, _, rfl⟩
        exact (length_polyAdd_le _ _).trans
          (max_le (hgetD_le _ _ hinv.2.2.1 i) (hgetD_le _ _ hinv.2.2.2 i))
      have hfrob : shoupLFrobQBounded p.1 p.2 st.2 = shoupLFrobQ p.1 p.2 st.2 :=
        shoupLFrobQBounded_eq _ hf_ne
      have h2 : (shoupLFrobQBounded p.1 p.2 st.2).length ≤ p.1 ∧
          ∀ v ∈ shoupLFrobQBounded p.1 p.2 st.2, v.length ≤ p.2.length + 1 := by
        rw [hfrob]
        unfold shoupLFrobQ
        cases hq0 : p.1 with
        | zero =>
          rw [Function.iterate_zero_apply]
          exact ⟨by omega, hinv.2.2.2⟩
        | succ q' =>
          rw [Function.iterate_succ_apply']
          obtain ⟨hl, hrows⟩ := length_shoupLMul (q' + 1) p.2 _ _ hf_ne
          exact ⟨hl.le, fun v hv => (hrows v hv).trans (Nat.le_succ _)⟩
      unfold shoupBetaStep
      exact ⟨h1, h2.1, h1_rows, h2.2⟩)
    (ComputableInPolyTime.polyBounded hboundFn)
    (fun p _ st _ hinv => by
      rw [length_encPair]
      have hl1 := length_encList_le encBits st.1 (b := p.2.length + 1)
        (fun v hv => by simp [hinv.2.2.1 v hv])
      have hl2 := length_encList_le encBits st.2 (b := p.2.length + 1)
        (fun v hv => by simp [hinv.2.2.2 v hv])
      have hm1 := hl1.trans (Nat.mul_le_mul_right _ hinv.1)
      have hm2 := hl2.trans (Nat.mul_le_mul_right _ hinv.2.1)
      omega)).1
  exact (ComputableInPolyTime.fst (encList encBits) (encList encBits)).comp hiter

end ShoupBetaSection

private def shoupPowersOneCell (_ q_i : ℕ) : List Bool :=
  if (q_i == 0) = true then [true] else []

private def shoupPowersStep (p : (ℕ × List Bool) × List (List Bool))
    (st : List (List (List Bool)) × List (List Bool)) :
    List (List (List Bool)) × List (List Bool) :=
  (st.1 ++ [st.2], shoupLMul p.1.1 p.1.2 st.2 p.2)

private def shoupPowersBounded (q : ℕ) (f : List Bool) (β : List (List Bool)) :
    List (List (List Bool)) :=
  ((shoupPowersStep ((q, f), β))^[if (polyTrim f).isEmpty then 0 else q + 1]
    ([], (List.range q).map (shoupPowersOneCell q))).1

private theorem shoupPowersBounded_eq {q : ℕ} {f : List Bool} (β : List (List Bool))
    (hf : (polyTrim f).isEmpty = false) :
    shoupPowersBounded q f β = shoupPowers q f β := by
  unfold shoupPowersBounded shoupPowers shoupPowersStep
  simp only [hf, Bool.false_eq_true, ↓reduceIte]
  rw [← foldl_range_const_eq]
  rfl

section ShoupPowersSection
attribute [local irreducible] shoupLMul shoupPowersStep polyTrim

private theorem polyTime_shoupPowersBounded :
    ComputableInPolyTime
      (fun p : (ℕ × List Bool) × List (List Bool) => shoupPowersBounded p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encBits) (encList encBits))
      (encList (encList encBits)) := by
  have hpar := ComputableInPolyTime.fst (encPair encUnary encBits) (encList encBits)
  have hβ := ComputableInPolyTime.snd (encPair encUnary encBits) (encList encBits)
  have hq := (ComputableInPolyTime.fst encUnary encBits).comp hpar
  have hf := (ComputableInPolyTime.snd encUnary encBits).comp hpar
  have hfne := ComputableInPolyTime.bitsIsEmpty.comp (computableInPolyTime_polyTrim.comp hf)
  have hq1 := ComputableInPolyTime.unary_add.comp (hq.prod (.const 1))
  have hcnt : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × List (List Bool) =>
        if (polyTrim p.1.2).isEmpty then 0 else p.1.1 + 1)
      (encPair (encPair encUnary encBits) (encList encBits)) encUnary :=
    (ComputableInPolyTime.ite' hfne
      (ComputableInPolyTime.const (0 : ℕ)) hq1)
  have hinitOne : ComputableInPolyTime
      (fun q : ℕ => (List.range q).map (shoupPowersOneCell q))
      encUnary (encList encBits) := by
    have hbit : ComputableInPolyTime
        (fun x : ℕ × ℕ => shoupPowersOneCell x.1 x.2)
        (encPair encUnary encUnary) encBits := by
      have hi := ComputableInPolyTime.snd encUnary encUnary
      have hcond : ComputableInPolyTime (fun x : ℕ × ℕ => x.2 == 0)
          (encPair encUnary encUnary) encBool :=
        hi.beq (.const 0)
      exact (ComputableInPolyTime.ite' hcond
        (ComputableInPolyTime.const [true]) (ComputableInPolyTime.const ([] : List Bool)))
    exact ComputableInPolyTime.mapWithInput (f := shoupPowersOneCell)
      ComputableInPolyTime.range hbit
  let encIn := encPair (encPair encUnary encBits) (encList encBits)
  have hnil : ComputableInPolyTime
      (fun _ : (ℕ × List Bool) × List (List Bool) => ([] : List (List (List Bool))))
      encIn (encList (encList encBits)) :=
    ComputableInPolyTime.const ([] : List (List (List Bool)))
  have hinit : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × List (List Bool) =>
        (([] : List (List (List Bool))), (List.range p.1.1).map (shoupPowersOneCell p.1.1)))
      encIn (encPair (encList (encList encBits)) (encList encBits)) :=
    hnil.prod (hinitOne.comp hq)
  have hsnoc : ComputableInPolyTime
      (fun p : List (List (List Bool)) × List (List Bool) => p.1 ++ [p.2])
      (encPair (encList (encList encBits)) (encList encBits)) (encList (encList encBits)) :=
    ComputableInPolyTime.snoc (encList encBits)
  have hstep : ComputableInPolyTime
      (fun x : ((ℕ × List Bool) × List (List Bool)) ×
          (List (List (List Bool)) × List (List Bool)) =>
        shoupPowersStep x.1 x.2)
      (encPair encIn (encPair (encList (encList encBits)) (encList encBits)))
      (encPair (encList (encList encBits)) (encList encBits)) := by
    have hxInput := ComputableInPolyTime.fst
      encIn (encPair (encList (encList encBits)) (encList encBits))
    have hxst := ComputableInPolyTime.snd
      encIn (encPair (encList (encList encBits)) (encList encBits))
    have hxqf := (ComputableInPolyTime.fst (encPair encUnary encBits) (encList encBits)).comp
      hxInput
    have hxβ := (ComputableInPolyTime.snd (encPair encUnary encBits) (encList encBits)).comp
      hxInput
    have hxcur :=
      (ComputableInPolyTime.snd (encList (encList encBits)) (encList encBits)).comp hxst
    have hpair := (hsnoc.comp hxst).prod (polyTime_shoupLMul.comp (hxqf.prod (hxcur.prod hxβ)))
    convert hpair using 1
    funext x
    unfold shoupPowersStep
    rfl
  have hboundFn : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × List (List Bool) =>
        let rowB := p.1.1 * (2 * (p.1.2.length + 1) + 1)
        2 * ((p.1.1 + 1) * (2 * rowB + 1)) + 1 + rowB)
      (encPair (encPair encUnary encBits) (encList encBits)) encUnary := by
    have hq' := hq
    have hq1' := hq1
    have hf1 := ComputableInPolyTime.unary_add.comp
      ((ComputableInPolyTime.length_bits.comp hf).prod (.const 1))
    have h2f := ComputableInPolyTime.unary_mul.comp
      ((ComputableInPolyTime.const 2).prod hf1)
    have h2f1 := ComputableInPolyTime.unary_add.comp (h2f.prod (.const 1))
    have hrowB := ComputableInPolyTime.unary_mul.comp (hq'.prod h2f1)
    have h2r := ComputableInPolyTime.unary_mul.comp
      ((ComputableInPolyTime.const 2).prod hrowB)
    have h2r1 := ComputableInPolyTime.unary_add.comp (h2r.prod (.const 1))
    have houter := ComputableInPolyTime.unary_mul.comp (hq1'.prod h2r1)
    have h2out := ComputableInPolyTime.unary_mul.comp
      ((ComputableInPolyTime.const 2).prod houter)
    have h2out1 := ComputableInPolyTime.unary_add.comp (h2out.prod (.const 1))
    exact ComputableInPolyTime.unary_add.comp (h2out1.prod hrowB)
  have hiter := ComputableInPolyTime.iterateWith_spec
    (invariant := fun p k st =>
      st.1.length = k ∧ st.2.length ≤ p.1.1 ∧
        (∀ u ∈ st.1, u.length ≤ p.1.1 ∧ ∀ v ∈ u, v.length ≤ p.1.2.length + 1) ∧
        ∀ v ∈ st.2, v.length ≤ p.1.2.length + 1)
    ComputableInPolyTime.id' hcnt hinit hstep
    (fun p => by
      refine ⟨by simp, by simp, by simp, fun v hv => ?_⟩
      rw [List.mem_map] at hv
      rcases hv with ⟨i, _, rfl⟩
      unfold shoupPowersOneCell
      split_ifs <;> simp)
    (fun p k st hk hinv => by
      have hf_ne : (polyTrim p.1.2).isEmpty = false := by
        by_contra h
        simp only [Bool.not_eq_false] at h
        rw [ite_eq_left_iff.mpr (fun hnot => absurd h hnot)] at hk
        omega
      unfold shoupPowersStep
      obtain ⟨hl, hrows⟩ := length_shoupLMul p.1.1 p.1.2 st.2 p.2 hf_ne
      refine ⟨by simp [hinv.1], hl.le, fun u hu => ?_,
        fun v hv => (hrows v hv).trans (Nat.le_succ _)⟩
      simp only [List.mem_append, List.mem_singleton] at hu
      rcases hu with hu | rfl
      · exact hinv.2.2.1 u hu
      · exact ⟨hinv.2.1, hinv.2.2.2⟩)
    (ComputableInPolyTime.polyBounded hboundFn)
    (fun p k st hk hinv => by
      have hk_le : k ≤ p.1.1 + 1 := by
        split_ifs at hk <;> omega
      have hk_len : st.1.length ≤ p.1.1 + 1 := hinv.1.symm ▸ hk_le
      have hel_bound : ∀ u ∈ st.1,
          (encList encBits u).length ≤ p.1.1 * (2 * (p.1.2.length + 1) + 1) := by
        intro u hu
        have hu' := hinv.2.2.1 u hu
        exact (length_encList_le encBits u (b := p.1.2.length + 1)
          (fun v hv => by simp [hu'.2 v hv])).trans
          (Nat.mul_le_mul_right _ hu'.1)
      have hl1 := (length_encList_le (encList encBits) st.1
        (b := p.1.1 * (2 * (p.1.2.length + 1) + 1)) hel_bound).trans
        (Nat.mul_le_mul_right _ hk_len)
      have hl2 := (length_encList_le encBits st.2 (b := p.1.2.length + 1)
        (fun v hv => by simp [hinv.2.2.2 v hv])).trans
        (Nat.mul_le_mul_right _ hinv.2.1)
      rw [length_encPair]
      dsimp only
      omega)
  exact (ComputableInPolyTime.fst (encList (encList encBits)) (encList encBits)).comp hiter.1

end ShoupPowersSection

private def shoupMinPolyRow
    (p : (ℕ × ℕ) × List (List (List Bool))) (idx : ℕ) : List Bool :=
  let i := idx / p.1.2
  let j := idx % p.1.2
  p.2.map fun v => (v.getD i []).getD j false

private def shoupMinPolyBit (x : ((ℕ × ℕ) × List (List (List Bool))) × ℕ) (v : List (List Bool)) :
    Bool :=
  (v.getD (x.2 / x.1.1.2) []).getD (x.2 % x.1.1.2) false

private theorem polyTime_shoupMinPolyMatrix :
    ComputableInPolyTime
      (fun p : (ℕ × ℕ) × List (List (List Bool)) => shoupMinPolyMatrix p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encUnary) (encList (encList encBits)))
      (encList encBits) := by
  have hget : ComputableInPolyTime (fun p : List (List Bool) × ℕ => p.1.getD p.2 [])
      (encPair (encList encBits) encUnary) encBits := by fun_prop
  have hbit : ComputableInPolyTime
      (fun y : (((ℕ × ℕ) × List (List (List Bool))) × ℕ) × List (List Bool) =>
        shoupMinPolyBit y.1 y.2)
      (encPair (encPair (encPair (encPair encUnary encUnary) (encList (encList encBits))) encUnary)
        (encList encBits))
      encBool := by
    have hyx := ComputableInPolyTime.fst
      (encPair (encPair (encPair encUnary encUnary) (encList (encList encBits))) encUnary)
      (encList encBits)
    have hyv := ComputableInPolyTime.snd
      (encPair (encPair (encPair encUnary encUnary) (encList (encList encBits))) encUnary)
      (encList encBits)
    have hyp := (ComputableInPolyTime.fst (encPair encUnary encUnary)
      (encList (encList encBits))).comp
      ((ComputableInPolyTime.fst (encPair (encPair encUnary encUnary)
        (encList (encList encBits))) encUnary).comp hyx)
    have hym := (ComputableInPolyTime.snd encUnary encUnary).comp hyp
    have hyidx := (ComputableInPolyTime.snd
      (encPair (encPair encUnary encUnary) (encList (encList encBits))) encUnary).comp hyx
    have hdm := ComputableInPolyTime.unary_divMod.comp (hyidx.prod hym)
    have hi := (ComputableInPolyTime.fst encUnary encUnary).comp hdm
    have hj := (ComputableInPolyTime.snd encUnary encUnary).comp hdm
    exact ComputableInPolyTime.bitsGetDWithInput (hget.comp (hyv.prod hi)) hj false
  have hrow : ComputableInPolyTime
      (fun x : ((ℕ × ℕ) × List (List (List Bool))) × ℕ => shoupMinPolyRow x.1 x.2)
      (encPair (encPair (encPair encUnary encUnary) (encList (encList encBits))) encUnary)
      encBits := by
    have hpows := (ComputableInPolyTime.snd (encPair encUnary encUnary)
      (encList (encList encBits))).comp
      (ComputableInPolyTime.fst
        (encPair (encPair encUnary encUnary) (encList (encList encBits))) encUnary)
    have hmap := ComputableInPolyTime.mapWithInput (f := shoupMinPolyBit) hpows hbit
    exact ComputableInPolyTime.listToBits.comp hmap
  have hlen : ComputableInPolyTime
      (fun p : (ℕ × ℕ) × List (List (List Bool)) => p.1.1 * p.1.2)
      (encPair (encPair encUnary encUnary) (encList (encList encBits))) encUnary := by
    have hqm := ComputableInPolyTime.fst (encPair encUnary encUnary)
      (encList (encList encBits))
    exact ComputableInPolyTime.unary_mul.comp
      (((ComputableInPolyTime.fst encUnary encUnary).comp hqm).prod
        ((ComputableInPolyTime.snd encUnary encUnary).comp hqm))
  have hres := ComputableInPolyTime.mapWithInput (f := shoupMinPolyRow)
    (ComputableInPolyTime.range.comp hlen) hrow
  convert hres using 1
  funext p
  unfold shoupMinPolyMatrix shoupMinPolyRow
  rfl

section ShoupIrreducibleSection
attribute [local irreducible] shoupCyclicFactor shoupBetaBounded shoupPowersBounded
  shoupMinPolyMatrix kernelVecBits ordTwoMod qAdicValTwoPowSubOne

/-- `shoupIrreducibleBits` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_shoupIrreducibleBits :
    ComputableInPolyTime shoupIrreducibleBits encUnary encBits := by
  have hcond := polyTime_primeGeThree
  have hm := computableInPolyTime_ordTwoMod
  have hf := polyTime_shoupCyclicFactorBounded
  have hβ := polyTime_shoupBetaBounded.comp (ComputableInPolyTime.id'.prod hf)
  have hpows := polyTime_shoupPowersBounded.comp ((ComputableInPolyTime.id'.prod hf).prod hβ)
  have hmat := polyTime_shoupMinPolyMatrix.comp ((ComputableInPolyTime.id'.prod hm).prod hpows)
  have hq1 := ComputableInPolyTime.unary_add.comp
    (ComputableInPolyTime.id'.prod (.const 1))
  have hvec := computableInPolyTime_kernelVecBits.comp (hq1.prod hmat)
  have hite := (ComputableInPolyTime.ite' hcond
    hvec (ComputableInPolyTime.const ([] : List Bool)))
  convert hite using 1
  funext q
  unfold shoupIrreducibleBits
  by_cases h : q.Prime ∧ 3 ≤ q
  · simp only [h, and_self, decide_true, ↓reduceIte, Function.comp_def]
    have hf_eq :
        (fun f => berlekampIrreducibleFactor (polyComposePow q f))^[
          qAdicValTwoPowSubOne q (ordTwoMod q) - 1]
          (berlekampIrreducibleFactor (List.replicate q true)) =
        shoupCyclicFactor q (qAdicValTwoPowSubOne q (ordTwoMod q)) := by
      unfold shoupCyclicFactor
      rfl
    have hspec := shoupCyclicFactor_spec h.1 h.2
    have hlen : (shoupCyclicFactor q (qAdicValTwoPowSubOne q (ordTwoMod q))).length =
        ordTwoMod q + 1 := hspec.2.2.2.2
    have htrim : polyTrim (shoupCyclicFactor q (qAdicValTwoPowSubOne q (ordTwoMod q))) =
        shoupCyclicFactor q (qAdicValTwoPowSubOne q (ordTwoMod q)) := hspec.1
    have hne : (polyTrim (shoupCyclicFactor q (qAdicValTwoPowSubOne q (ordTwoMod q)))).isEmpty =
        false := by
      rw [htrim, List.isEmpty_eq_false_iff]
      intro hnil
      rw [hnil, List.length_nil] at hlen
      omega
    rw [hf_eq, shoupBetaBounded_eq hne, shoupPowersBounded_eq _ hne]
  · simp [h]

end ShoupIrreducibleSection

end Cslib.AffineDisperser.Li
