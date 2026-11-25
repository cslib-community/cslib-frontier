/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.SymAnd.ACC0
public import CslibFrontier.Computability.Circuit.Boolean.SymAnd.Evaluate
public import CslibFrontier.Computability.Circuit.Boolean.Unbounded.Encoding
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
import CslibFrontier.Computability.Circuit.Depth
import CslibFrontier.Computability.Circuit.Encoding.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.EraseDupsBy
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Choose
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Max
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.PowMod
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Subtraction
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCombinators
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCountedIteration
import CslibFrontier.Computability.PolyTime.BinaryField
import CslibFrontier.Foundations.BooleanAnalysis.LowDegree.Choose
import CslibFrontier.Foundations.BooleanAnalysis.LowDegree.OrTest
import CslibFrontier.Foundations.Data.List.EraseDupsBy
import CslibFrontier.Foundations.Data.Polynomial.ParityAmplifier
import CslibFrontier.Foundations.FieldTheory.Finite.BinaryFieldTable
import CslibFrontier.Tactic.EncLen
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Sort
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Algorithmic compilation of ACC⁰ circuits into `SYM ∘ AND` circuits

This module formalizes the algorithmic clause of Williams's translation from constant-depth `ACC⁰`
circuits to quasi-polynomial `SYM ∘ AND` circuits ([Williams2014], Lemma 4.1, Section 4, p. 14 and
Appendix A in the author's full version of 31 July 2012): given an encoded single-output circuit `C`
over `Unbounded.extSignature` with `MOD_m` gates (`m > 0`) of depth at most `d`, on `n` inputs with
`s = C.size` gates, a native multi-tape Turing machine computes an encoding of the canonical
`SYM ∘ AND` circuit `ACC0ToSymAnd.compile` (and in particular `C.toSymAnd m`) together with the
parameters `SymOutParam` of its symmetric output gate in time and space
`O((|enc C| + 1) ^ C₀ * 2 ^ (C₀ * (⌊log₂ (n + s)⌋ + 2) ^ K))` where `K = 5 ^ (d * (m + 2)) + 1`.

## Construction

The symmetric gate produced by `SymAnd.collapseRun` over `top ℓ` has the closed form
`SymOutParam.eval p z = decide (p.thresh < 2 * p.mods.foldr (fun M acc => acc % M) z)`, which is
polynomial-time in the binary encodings of `p` and `z` (`SymOutParam.computableInPolyTime_eval`).

To certify the `2 ^ polylog(n + s)` multi-tape Turing machine cleanly without hand-assembling
nested streaming loops, the compiler separates:

1. **Unary budget materialization (`computableInO_pow2_unary`)**: `k ↦ 2 ^ k` from binary `encNat`
   to unary `encUnary` by `k` doubling steps using `ComputableInO.iterate`.
2. **Budget-capped polynomial-time compilation**: given `(c, U)` with unary budget `U`, build the
   binary-field power table over `𝔽_{2^(2ℓ+2)}`, represent each collapsed layer as a weighted list
   of strictly increasing slot-index subsets `(S, mult)` capped at length `U`, evaluate
   `amplifiedCount` and the subset Möbius transform modulo `M_j = p_j ^ (B_j + 1)` in pure `ℕ`
   arithmetic, and finally restrict to input slots and expand multiplicities into a
   `SymAndInstance`. When `U = 2 ^ E_budget(c)` for `E_budget(c) = (B₀ + 2) * (2 * B₀) ^ (5 ^ L)`,
   every cap is inactive and the output equals `ACC0ToSymAnd.compile` identically.

## Main definitions

* `Cslib.Circuits.Boolean.SymAnd.SymOutParam`, `.encSymOutParam`, `.SymOutParam.eval`:
  the nested-modulus majority output gate of a collapsed `ACC⁰ → SYM ∘ AND` circuit.
* `Cslib.Circuits.Boolean.SymAnd.compileSymAndFixed`: executable `SYM ∘ AND` compiler for a fixed
  tower depth `d` and modulus `m`.
* `Cslib.Circuits.Boolean.SymAnd.compileToSymAnd`: executable compiler matching `Circuit.toSymAnd`
  for all circuits of depth at most `d`.

## Main results

* `Cslib.Circuits.Boolean.SymAnd.SymOutParam.computableInPolyTime_eval`: evaluating the collapsed
  symmetric output gate is polynomial-time in binary.
* `Cslib.Circuits.Boolean.SymAnd.computableInO_pow2_unary`: `2 ^ k` in unary from binary `k`.
* `Cslib.Circuits.Boolean.SymAnd.computableInPolyTime_extCircuit_depth`: circuit depth in unary
  from `Unbounded.encExtCircuit 1`.
* `Cslib.Circuits.Boolean.SymAnd.compileSymAndFixed_eq_compile`,
  `Cslib.Circuits.Boolean.SymAnd.eval_compileSymAndFixed`,
  `Cslib.Circuits.Boolean.SymAnd.compileToSymAnd_eq_toSymAnd`: exact agreement with
  `ACC0ToSymAnd.compile` and `Circuit.toSymAnd`.
* `Cslib.Circuits.Boolean.SymAnd.computableInO_compileSymAndFixed`,
  `Cslib.Circuits.Boolean.SymAnd.computableInO_compileToSymAnd`: Williams's Lemma 4.1 on native
  multi-tape Turing machines.

## References

* [R. Beigel, J. Tarui, *On ACC*][BeigelTarui1994]
* [R. Williams, *Nonuniform ACC Circuit Lower Bounds*][Williams2014]
-/

public section

namespace Cslib.Circuits.Boolean.SymAnd

open Finset BitString Polynomial Turing.MultiTapeTM
open Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.ACC0ToSymAnd
open Cslib.BinaryField

/-! ### 1. Nested-modulus majority output gate (`SymOutParam`) -/

/-- Parameters of the symmetric output gate of a collapsed `ACC⁰ → SYM ∘ AND` circuit:
a majority threshold `thresh` (specifically `2 ^ (2 * ℓ + 2)`) and the list `mods` of
collapse-step moduli `[M₀, …, M_{L-1}]` applied right-to-left (`z ↦ (((z % M_{L-1}) …) % M₀)`). -/
structure SymOutParam where
  /-- Majority threshold (`thresh < 2 * reducedCount`). -/
  thresh : ℕ
  /-- Moduli applied right-to-left to the satisfied-AND count. -/
  mods : List ℕ
  deriving DecidableEq

/-- Binary-tape encoding of `SymOutParam`: binary threshold `thresh` (`encNat`) paired with
the framed list of binary moduli (`encList encNat`). -/
enc_structure encSymOutParam : SymOutParam where
  thresh : encNat, mods : (encList encNat)

/-- Apply a list of moduli right-to-left:
`nestedMod [M₀, …, M_{r-1}] z = (((z % M_{r-1}) …) % M₀)`. -/
@[expose] def SymOutParam.nestedMod (mods : List ℕ) (z : ℕ) : ℕ :=
  mods.foldr (fun M acc => acc % M) z

/-- Evaluate the collapsed symmetric output gate at satisfied-AND count `z`. -/
@[expose] def SymOutParam.eval (p : SymOutParam) (z : ℕ) : Bool :=
  decide (p.thresh < 2 * SymOutParam.nestedMod p.mods z)

private theorem nestedMod_eq_foldl_reverse (mods : List ℕ) (z : ℕ) :
    SymOutParam.nestedMod mods z = mods.reverse.foldl (fun acc M => acc % M) z := by
  simp only [SymOutParam.nestedMod, List.foldl_reverse]

private theorem foldl_mod_le (mods : List ℕ) (z : ℕ) :
    mods.foldl (fun acc M => acc % M) z ≤ z := by
  induction mods generalizing z with
  | nil => exact le_rfl
  | cons M ms ih => exact (ih (z % M)).trans (Nat.mod_le z M)

/-- Evaluating `SymOutParam.eval` is polynomial-time in the binary encodings of `p` and `z`. -/
theorem SymOutParam.computableInPolyTime_eval :
    ComputableInPolyTime (fun q : SymOutParam × ℕ => q.1.eval q.2)
      (encPair encSymOutParam encNat) encBool := by
  have hmods : ComputableInPolyTime (fun q : SymOutParam × ℕ => q.1.mods.reverse)
      (encPair encSymOutParam encNat) (encList encNat) := by
    have h1 : ComputableInPolyTime (fun q : SymOutParam × ℕ => q.1.mods)
        (encPair encSymOutParam encNat) (encList encNat) := by
      have := ComputableInPolyTime.fst encSymOutParam encNat
      fun_prop
    exact ComputableInPolyTime.listReverseWithInput h1
  have hinit : ComputableInPolyTime (fun q : SymOutParam × ℕ => q.2)
      (encPair encSymOutParam encNat) encNat := ComputableInPolyTime.snd encSymOutParam encNat
  have hstep : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 % p.2)
      (encPair encNat encNat) encNat := ComputableInPolyTime.binary_mod
  have hred : ComputableInPolyTime
      (fun q : SymOutParam × ℕ => q.1.mods.reverse.foldl (fun acc M => acc % M) q.2)
      (encPair encSymOutParam encNat) encNat := by
    refine ComputableInPolyTime.foldl' hmods hinit hstep
      (B := fun q => (encPair encSymOutParam encNat q).length) .self fun q i _ => ?_
    have hz : (encNat q.2).length ≤ (encPair encSymOutParam encNat q).length := by enc_len
    refine le_trans ?_ hz
    change (Nat.bits _).length ≤ q.2.bits.length
    simpa only [← Nat.size_eq_bits_len] using Nat.size_le_size (foldl_mod_le _ q.2)
  have hred' : ComputableInPolyTime (fun q : SymOutParam × ℕ => SymOutParam.nestedMod q.1.mods q.2)
      (encPair encSymOutParam encNat) encNat :=
    hred.of_enc_eq fun q => congrArg encNat (nestedMod_eq_foldl_reverse q.1.mods q.2)
  have hth : ComputableInPolyTime (fun q : SymOutParam × ℕ => q.1.thresh)
      (encPair encSymOutParam encNat) encNat := by
    have := ComputableInPolyTime.fst encSymOutParam encNat
    fun_prop
  have htwo : ComputableInPolyTime
      (fun q : SymOutParam × ℕ => 2 * SymOutParam.nestedMod q.1.mods q.2)
      (encPair encSymOutParam encNat) encNat :=
    ComputableInPolyTime.binary_mul.comp ((ComputableInPolyTime.const 2).prod hred')
  exact ComputableInPolyTime.binary_lt' hth htwo

/-! ### 2. Materializing `2 ^ k` in unary from binary `k` -/

private theorem iterate_double (k : ℕ) : (fun u : ℕ => u + u)^[k] 1 = 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, pow_succ']; omega

/-- Materializing `2 ^ k` in unary (`encUnary`) from `k` in binary (`encNat`) runs in time
`O((k + 1) * (2 ^ k + (k + 1) ^ 2))` and space `O(2 ^ k + k)` via `k` doubling passes. -/
theorem computableInO_pow2_unary :
    ComputableInO (fun k : ℕ => 2 ^ k) encNat encUnary
      (fun k => (k + 1) * (2 ^ k + (k + 1) ^ 2))
      (fun k => 2 ^ k + k) := by
  have hstep : ComputableInO (fun u : ℕ => u + u) encUnary encUnary
      (fun u => u + u) (fun u => u + u) := by
    have h0 : ComputableInO (fun u : ℕ => u + u) encUnary encUnary
        (fun u => (encUnary u).length + (encUnary u).length)
        (fun u => (encUnary u).length + (encUnary u).length) :=
      (ComputableInO.id' (encMid := encUnary)).append (g := fun u => u + u) (enc₂ := encUnary)
        (ComputableInO.id' (encMid := encUnary))
        fun u => by simp only [encUnary_apply, List.replicate_append_replicate]
    simpa only [encUnary_apply, List.length_replicate] using h0
  have hit := ComputableInO.iterate
    (hn := ComputableInO.id' (encMid := encNat))
    (hinit := ComputableInO.const (encIn := encNat) (encMid := encUnary) 1)
    (hstep := hstep)
    (R := fun k => 2 * 2 ^ k) (Q := fun k => 2 * 2 ^ k) (B := fun k => 2 ^ k)
    (fun k j hj => by
      rw [iterate_double]
      have hle : 2 ^ j ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hj
      omega)
    (fun k j hj => by
      rw [iterate_double]
      have hle : 2 ^ j ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hj
      omega)
    (fun k j hj => by
      rw [iterate_double, encUnary_apply, List.length_replicate]
      exact Nat.pow_le_pow_right (by decide) hj)
  have hfun : (fun k : ℕ => (fun u : ℕ => u + u)^[k] 1) = fun k : ℕ => 2 ^ k :=
    funext iterate_double
  rw [hfun] at hit
  refine hit.mono 6 (fun k => ?_) (fun k => ?_)
  · have hlen : (encNat k).length ≤ k := by
      rw [encNat_apply, Nat.size_eq_bits_len]; exact Nat.size_le_self k
    have hsq : ((encNat k).length + 1) ^ 2 ≤ (k + 1) ^ 2 :=
      Nat.pow_le_pow_left (by omega) 2
    have h1 : 1 ≤ (k + 1) ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos _)
    have h2 : k ≤ (k + 1) ^ 2 := (Nat.le_succ k).trans (Nat.le_self_pow two_ne_zero _)
    have h3 : 2 * 2 ^ k + 2 ^ k + ((encNat k).length + 1) ^ 2 ≤
        3 * (2 ^ k + (k + 1) ^ 2) := by omega
    have h4 : (k + 1) * (2 * 2 ^ k + 2 ^ k + ((encNat k).length + 1) ^ 2) ≤
        3 * ((k + 1) * (2 ^ k + (k + 1) ^ 2)) := by
      calc _ ≤ (k + 1) * (3 * (2 ^ k + (k + 1) ^ 2)) := Nat.mul_le_mul_left _ h3
        _ = _ := by ring
    have h5 : (encNat k).length + (encNat k).length ≤ 2 * ((k + 1) * (2 ^ k + (k + 1) ^ 2)) := by
      have : k ≤ (k + 1) * (2 ^ k + (k + 1) ^ 2) :=
        h2.trans ((Nat.le_add_left _ _).trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _)))
      omega
    omega
  · have hlen : (encNat k).length ≤ k := by
      rw [encNat_apply, Nat.size_eq_bits_len]; exact Nat.size_le_self k
    omega

/-! ### 3. Polynomial-time circuit depth over `Unbounded.extSignature` -/

/-- `min` of a computed binary natural (left) and a computed unary natural (right), output in unary.
Kept explicit so `Min.min` search on `encUnary` does not branch against `binary_min_unary'`. -/
theorem binary_min_unary_left' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encNat)
    (hright : ComputableInPolyTime right input encUnary) :
    ComputableInPolyTime (fun a => min (left a) (right a)) input encUnary :=
  (ComputableInPolyTime.binary_min_unary' hright hleft).of_enc_eq fun a =>
    congrArg encUnary (Nat.min_comm (left a) (right a))

/-- Positive modulus helper: returns `1` when `M = 0`, and `M` otherwise. -/
private def posMod (M : ℕ) : ℕ := if M = 0 then 1 else M

private theorem posMod_pos (M : ℕ) : 0 < posMod M := by
  unfold posMod; split_ifs <;> omega

private theorem posMod_eq_of_pos {M : ℕ} (hM : 0 < M) : posMod M = M := by
  unfold posMod; simp [hM.ne']

private theorem foldl_mod_posMod_le {α : Type*} (M : ℕ) (step : ℕ → α → ℕ)
    (l : List α) {init : ℕ} (hi : init ≤ posMod M) :
    l.foldl (fun acc x => step acc x % posMod M) init ≤ posMod M := by
  induction l generalizing init with
  | nil => exact hi
  | cons _ _ ih => exact ih (Nat.mod_lt _ (posMod_pos M)).le

private theorem size_le_size_add_one_of_le_posMod {a M : ℕ} (h : a ≤ posMod M) :
    a.size ≤ M.size + 1 := by
  have h1 : a ≤ M + 1 := h.trans (by unfold posMod; split_ifs <;> omega)
  refine (Nat.size_le_size h1).trans ?_
  rw [Nat.size_le]
  calc M + 1 ≤ 2 * M + 1 := by omega
    _ < 2 * (2 ^ M.size) := by have := Nat.lt_size_self M; omega
    _ = 2 ^ (M.size + 1) := by ring

private theorem computableInPolyTime_posMod {α : Type} {input : α ↪ List Bool} {fM : α → ℕ}
    (hM : ComputableInPolyTime fM input encNat) :
    ComputableInPolyTime (fun a => posMod (fM a)) input encNat :=
  ComputableInPolyTime.ite_decide
    (ComputableInPolyTime.decide_eq' hM (ComputableInPolyTime.const 0))
    (ComputableInPolyTime.const 1) hM

private def depthStep (depths : List ℕ) (gate : Unbounded.ExtOp × List ℕ) : List ℕ :=
  let d := (gate.2.map fun w => depths.getD w 0).foldl max 0 + 1
  depths ++ [d]

private theorem foldl_max_list_eq_fin_foldl {m : ℕ} (f : Fin m → ℕ) (init : ℕ) :
    (List.ofFn f).foldl max init = Fin.foldl m (fun acc i => max acc (f i)) init := by
  induction m generalizing init with
  | zero => simp
  | succ m ih =>
    rw [List.ofFn_succ, List.foldl_cons, ih, Fin.foldl_succ]

private theorem foldl_depthStep_program {n g : ℕ} (P : Program Unbounded.extSignature n g) :
    P.code.foldl depthStep (List.replicate n 0) =
      List.ofFn (fun i : Fin (n + g) => P.wireDepths (Wire.ofNat i.1 i.2)) := by
  induction P with
  | empty =>
    refine List.ext_getElem (by simp) fun i hi1 hi2 => ?_
    simp only [List.getElem_ofFn]
    have hi2' : i < n + 0 := by simpa using hi2
    cases h : (Wire.ofNat i hi2' : Wire n 0) with
    | input j => simp [Program.wireDepths]
    | gate k => exact k.elim0
  | @gate g P line ih =>
    rw [Program.code_gate, List.foldl_append, ih, List.foldl_cons, List.foldl_nil, depthStep]
    have hmap : (line.code.2.map fun w =>
        (List.ofFn fun i : Fin (n + g) => P.wireDepths (Wire.ofNat i.1 i.2)).getD w 0) =
        List.ofFn fun a => P.wireDepths (line.wires a) := by
      simp only [Line.code, List.map_ofFn, Function.comp_def]
      refine List.ext_getElem (by simp) fun a ha1 ha2 => ?_
      simp only [List.getElem_ofFn]
      have hlt : (line.wires ⟨a, by simpa using ha1⟩).toNat < n + g := Wire.toNat_lt _
      rw [List.getD_eq_getElem _ 0 (by simpa using hlt), List.getElem_ofFn, Wire.ofNat_toNat]
    have hd : (line.code.2.map fun w =>
        (List.ofFn fun i : Fin (n + g) => P.wireDepths (Wire.ofNat i.1 i.2)).getD w 0).foldl
        max 0 + 1 = line.depth P.wireDepths := by
      rw [hmap, foldl_max_list_eq_fin_foldl]
      rfl
    rw [hd]
    refine List.ext_getElem (by simp) fun i hi1 hi2 => ?_
    simp only [List.length_append, List.length_ofFn, List.length_singleton] at hi1
    simp only [List.getElem_ofFn]
    by_cases h : i < n + g
    · rw [List.getElem_append_left (by simp [h]), List.getElem_ofFn]
      have hw : Wire.ofNat i (by omega : i < n + (g + 1)) =
          Wire.castSucc (Wire.ofNat i h) := by
        apply Wire.toNat_injective
        simp [Wire.toNat_castSucc]
      rw [hw, Program.wireDepths_gate_castSucc]
    · have hi_eq : i = n + g := by omega
      subst hi_eq
      rw [List.getElem_append_right (by simp), List.getElem_singleton]
      have hw : Wire.ofNat (n + g) (by omega : n + g < n + (g + 1)) =
          Wire.gate (Fin.last g) := by
        apply Wire.toNat_injective
        simp [Wire.toNat_gate]
      rw [hw, Program.wireDepths_gateWire, Program.depths_gate_last]

private theorem extCircuit_depth_eq (c : Σ n, Circuit Unbounded.extSignature n 1) :
    c.2.depth =
      (c.2.code.1.foldl depthStep (List.replicate c.1 0)).getD (c.2.code.2.getD 0 0) 0 := by
  rw [Circuit.code, foldl_depthStep_program]
  have ho : (List.ofFn fun j : Fin 1 => (c.2.outputs j).toNat).getD 0 0 =
      (c.2.outputs 0).toNat := by
    simp
  rw [ho, List.getD_eq_getElem _ 0 (by simpa using Wire.toNat_lt (c.2.outputs 0)),
    List.getElem_ofFn, Wire.ofNat_toNat]
  rw [Circuit.depth, Fin.foldl_succ, Fin.foldl_zero, Nat.zero_max]
  rfl

/-- Computing `c.2.depth` in unary from an encoded circuit over `Unbounded.extSignature` is
polynomial-time. -/
theorem computableInPolyTime_extCircuit_depth :
    ComputableInPolyTime (fun c : Σ n, Circuit Unbounded.extSignature n 1 => c.2.depth)
      (Unbounded.encExtCircuit 1) encUnary := by
  have har := Circuit.computableInPolyTime_arity_code (σ := Unbounded.extSignature)
    Unbounded.encExtOp 1
  have hn : ComputableInPolyTime (fun c : Σ n, Circuit Unbounded.extSignature n 1 => c.1)
      (Unbounded.encExtCircuit 1) encUnary := har.fst'
  have hcode : ComputableInPolyTime (fun c : Σ n, Circuit Unbounded.extSignature n 1 => c.2.code)
      (Unbounded.encExtCircuit 1) (Circuit.encCode Unbounded.encExtOp) := har.snd'
  have hgates : ComputableInPolyTime
      (fun c : Σ n, Circuit Unbounded.extSignature n 1 => c.2.code.1)
      (Unbounded.encExtCircuit 1) (encList (Circuit.encGate Unbounded.encExtOp)) := hcode.fst'
  have houts : ComputableInPolyTime
      (fun c : Σ n, Circuit Unbounded.extSignature n 1 => c.2.code.2)
      (Unbounded.encExtCircuit 1) (encList encNat) := hcode.snd'
  have hstep : ComputableInPolyTime
      (fun p : List ℕ × (Unbounded.ExtOp × List ℕ) => depthStep p.1 p.2)
      (encPair (encList encUnary) (Circuit.encGate Unbounded.encExtOp)) (encList encUnary) := by
    have hds : ComputableInPolyTime
        (fun p : List ℕ × (Unbounded.ExtOp × List ℕ) => p.1)
        (encPair (encList encUnary) (Circuit.encGate Unbounded.encExtOp)) (encList encUnary) :=
      ComputableInPolyTime.fst _ _
    have hws : ComputableInPolyTime
        (fun p : List ℕ × (Unbounded.ExtOp × List ℕ) => p.2.2)
        (encPair (encList encUnary) (Circuit.encGate Unbounded.encExtOp)) (encList encNat) :=
      (ComputableInPolyTime.snd _ _).snd'
    have hlen : ComputableInPolyTime
        (fun p : List ℕ × (Unbounded.ExtOp × List ℕ) => p.1.length)
        (encPair (encList encUnary) (Circuit.encGate Unbounded.encExtOp)) encUnary :=
      (ComputableInPolyTime.length_list encUnary).comp hds
    have hlookup : ComputableInPolyTime
        (fun q : (List ℕ × (Unbounded.ExtOp × List ℕ)) × ℕ =>
          q.1.1.getD (min q.2 q.1.1.length) 0)
        (encPair (encPair (encList encUnary) (Circuit.encGate Unbounded.encExtOp)) encNat)
        encUnary :=
      ComputableInPolyTime.listGetDWithInput (hds.comp (ComputableInPolyTime.fst _ _))
        (binary_min_unary_left' (ComputableInPolyTime.snd _ _)
          (hlen.comp (ComputableInPolyTime.fst _ _))) 0
    have hlookup' : ComputableInPolyTime
        (fun q : (List ℕ × (Unbounded.ExtOp × List ℕ)) × ℕ => q.1.1.getD q.2 0)
        (encPair (encPair (encList encUnary) (Circuit.encGate Unbounded.encExtOp)) encNat)
        encUnary :=
      hlookup.of_enc_eq fun q => congrArg encUnary <| by
        by_cases h : q.2 < q.1.1.length
        · rw [Nat.min_eq_left h.le]
        · rw [Nat.min_eq_right (Nat.le_of_not_lt h), List.getD_eq_default _ _ (by omega),
            List.getD_eq_default _ _ le_rfl]
    have hvals := ComputableInPolyTime.mapWithInput (f := fun p w => p.1.getD w 0) hws hlookup'
    have hmax := (ComputableInPolyTime.unary_foldl_max 0).comp hvals
    have hadd : ComputableInPolyTime
        (fun p : List ℕ × (Unbounded.ExtOp × List ℕ) =>
          (p.2.2.map fun w => p.1.getD w 0).foldl max 0 + 1)
        (encPair (encList encUnary) (Circuit.encGate Unbounded.encExtOp)) encUnary :=
      ComputableInPolyTime.unary_add.comp (hmax.prod (ComputableInPolyTime.const 1))
    exact ComputableInPolyTime.listAppend' hds
      (ComputableInPolyTime.cons' hadd (ComputableInPolyTime.const []))
  have hinit : ComputableInPolyTime
      (fun c : Σ n, Circuit Unbounded.extSignature n 1 => List.replicate c.1 0)
      (Unbounded.encExtCircuit 1) (encList encUnary) :=
    ComputableInPolyTime.replicate hn (ComputableInPolyTime.const 0)
  have hfold : ComputableInPolyTime
      (fun c : Σ n, Circuit Unbounded.extSignature n 1 =>
        c.2.code.1.foldl depthStep (List.replicate c.1 0))
      (Unbounded.encExtCircuit 1) (encList encUnary) := by
    refine (ComputableInPolyTime.foldl_spec hgates hinit hstep
      (fun c consumed st =>
        st.length = c.1 + consumed.length ∧ ∀ d ∈ st, d ≤ consumed.length)
      (fun c => ⟨by simp, fun d hd => by simp [List.mem_replicate.1 hd]⟩)
      (fun c consumed st gate _ ⟨hlen, hle⟩ => by
        refine ⟨by simp [depthStep, hlen, Nat.add_assoc], fun d hd => ?_⟩
        simp only [depthStep, List.mem_append, List.mem_singleton] at hd
        rcases hd with hd | rfl
        · have := hle d hd
          simp only [List.length_append, List.length_singleton]; omega
        · have hfold_le : ∀ (l : List ℕ) (acc : ℕ), acc ≤ consumed.length →
              (∀ x ∈ l, x ≤ consumed.length) → l.foldl max acc ≤ consumed.length := by
            intro l
            induction l with
            | nil => intro acc ha _; exact ha
            | cons x xs ih =>
              intro acc ha hx
              exact ih (max acc x) (max_le ha (hx x List.mem_cons_self))
                fun y hy => hx y (List.mem_cons_of_mem x hy)
          have hmem : ∀ x ∈ gate.2.map fun w => st.getD w 0, x ≤ consumed.length := by
            intro x hx
            obtain ⟨w, _, rfl⟩ := List.mem_map.1 hx
            by_cases hw : w < st.length
            · rw [List.getD_eq_getElem _ _ hw]; exact hle _ (List.getElem_mem hw)
            · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hw)]; exact Nat.zero_le _
          have hf := hfold_le _ 0 (Nat.zero_le _) hmem
          simp only [List.length_append, List.length_singleton]; omega)
      (size := fun c => (c.1 + c.2.size) * (2 * c.2.size + 1))
      ((hn.polyBounded.add (hgates.polyBounded_length)).mul
        (((PolyBounded.const 2).mul hgates.polyBounded_length).add (.const 1)) |>
        fun h => PolyBounded.mono h fun c => by
          have hg : c.2.size ≤
              (encList (Circuit.encGate Unbounded.encExtOp) c.2.code.1).length := by
            rw [← Circuit.length_code_fst c.2]
            exact SizedListEncoding.length_le (encA := Circuit.encGate Unbounded.encExtOp)
              (encL := encList (Circuit.encGate Unbounded.encExtOp)) c.2.code.1
          exact Nat.mul_le_mul (Nat.add_le_add_left hg c.1) (by omega))
      (fun c consumed st hpre ⟨hlen, hle⟩ => by
        have hc : consumed.length ≤ c.2.size := by
          rw [← Circuit.length_code_fst c.2]
          exact hpre.length_le
        refine (length_encList_le encUnary st (b := c.2.size) fun d hd => ?_).trans ?_
        · simpa only [encUnary_apply, List.length_replicate] using (hle d hd).trans hc
        · rw [hlen]; exact Nat.mul_le_mul_right _ (by omega))).1
  have hout0 : ComputableInPolyTime
      (fun c : Σ n, Circuit Unbounded.extSignature n 1 => c.2.code.2.getD 0 0)
      (Unbounded.encExtCircuit 1) encNat :=
    ComputableInPolyTime.listGetDWithInput houts (ComputableInPolyTime.const 0) 0
  have hflen : ComputableInPolyTime
      (fun c : Σ n, Circuit Unbounded.extSignature n 1 =>
        (c.2.code.1.foldl depthStep (List.replicate c.1 0)).length)
      (Unbounded.encExtCircuit 1) encUnary :=
    (ComputableInPolyTime.length_list encUnary).comp hfold
  have hres := ComputableInPolyTime.listGetDWithInput hfold
    (binary_min_unary_left' hout0 hflen) 0
  refine hres.of_enc_eq fun c => congrArg encUnary ?_
  rw [extCircuit_depth_eq]
  set ds := c.2.code.1.foldl depthStep (List.replicate c.1 0)
  by_cases h : c.2.code.2.getD 0 0 < ds.length
  · rw [Nat.min_eq_left h.le]
  · rw [Nat.min_eq_right (Nat.le_of_not_lt h), List.getD_eq_default _ _ (Nat.le_of_not_lt h),
      List.getD_eq_default _ _ le_rfl]

/-! ### 4. Budget-capped polynomial-time compiler internals -/

section Internals

attribute [local irreducible] Turing.MultiTapeTM.ComputableInPolyTime

/-- Op tag of an extended operation: `0` = NOT, `1` = AND, `2` = OR, `3` = `MOD_m` gate. -/
private def extOpTag : Unbounded.ExtOp → ℕ
  | .ac .not => 0
  | .ac (.and _) => 1
  | .ac (.or _) => 2
  | .gate _ => 3

private theorem extOpTag_eq (op : Unbounded.ExtOp) :
    extOpTag op = if op.toNat = 0 then 0 else (op.toNat - 1) % 3 + 1 := by
  rcases op with ((_ | k | k) | k) <;> simp [extOpTag, Unbounded.ExtOp.toNat]

private theorem computableInPolyTime_extOpTag :
    ComputableInPolyTime extOpTag Unbounded.encExtOp encUnary := by
  have h : ComputableInPolyTime
      (fun op : Unbounded.ExtOp => if op.toNat = 0 then 0 else (op.toNat - 1) % 3 + 1)
      Unbounded.encExtOp encUnary := by
    have ht := Unbounded.computableInPolyTime_extOp_toNat
    fun_prop
  exact h.of_enc_eq fun op => congrArg encUnary (extOpTag_eq op)

/-- Precomputed context for compiling an encoded `ACC⁰[m]` circuit. All indices and counters are
polynomial in `|enc c|` and stored in unary (`encUnary`). -/
private structure CompileCtx where
  n : ℕ
  g : ℕ
  m : ℕ
  w : ℕ
  nSeed : ℕ
  nSlot : ℕ
  nTotal : ℕ
  /-- `(extOpTag op, wires_in_unary)` for each gate of the circuit. -/
  gates : List (ℕ × List ℕ)
  /-- Deduplicated wire lists (in unary) for each gate of the circuit. -/
  gatesDedup : List (List ℕ)
  /-- `seedPows[r][i]` = `w`-bit power-basis coordinates of `(equivFin.symm r) ^ i` in `𝔽_{2^w}`. -/
  seedPows : List (List (List Bool))
  deriving DecidableEq

private enc_structure encCompileCtx : CompileCtx where
  n : encUnary,
  g : encUnary,
  m : encUnary,
  w : encUnary,
  nSeed : encUnary,
  nSlot : encUnary,
  nTotal : encUnary,
  gates : (encList (encPair encUnary (encList encUnary))),
  gatesDedup : (encList (encList encUnary)),
  seedPows : (encList (encList encBits))

attribute [local irreducible] encCompileCtx

/-- Weighted gate list: each entry `(S, mult)` stores a strictly increasing list of slot indices
`S` (encoded in unary) and a binary multiplicity `mult`. -/
private abbrev WGate := List ℕ × ℕ

private abbrev encWGate : WGate ↪ List Bool := encPair (encList encUnary) encNat

private abbrev encWList : List WGate ↪ List Bool := encList encWGate

/-- The pairs `(p, i)` with `p ≤ m`, `i ≤ m`, `p` prime and `p ^ (i + 1) ∣ m`. -/
private def relList (m : ℕ) : List (ℕ × ℕ) :=
  ((List.range (m + 1)).flatMap fun p => (List.range (m + 1)).map fun i => (p, i)).filter
    fun pi => decide (pi.1.Prime ∧ pi.1 ^ (pi.2 + 1) ∣ m)

private theorem mem_relList_iff {m p i : ℕ} :
    (p, i) ∈ relList m ↔ p < m + 1 ∧ i < m + 1 ∧ p.Prime ∧ p ^ (i + 1) ∣ m := by
  simp only [relList, List.mem_filter, List.mem_flatMap, List.mem_range, List.mem_map,
    decide_eq_true_eq]
  constructor
  · rintro ⟨⟨p', hp', i', hi', hpi⟩, hcond⟩
    cases hpi
    exact ⟨hp', hi', hcond⟩
  · rintro ⟨hp, hi, hprime, hdvd⟩
    exact ⟨⟨p, hp, i, hi, rfl⟩, hprime, hdvd⟩

private theorem nodup_relList (m : ℕ) : (relList m).Nodup := by
  refine List.Nodup.filter _ ?_
  rw [List.nodup_flatMap]
  refine ⟨fun p _ => (List.nodup_range).map fun _ _ h => (Prod.mk.inj h).2, ?_⟩
  refine (List.nodup_range).pairwise_of_forall_ne fun p₁ _ p₂ _ hne => ?_
  intro x hx₁ hx₂
  obtain ⟨_, _, rfl⟩ := List.mem_map.1 hx₁
  obtain ⟨_, _, h⟩ := List.mem_map.1 hx₂
  exact hne (Prod.mk.inj h).1.symm

/-- The layer schedule for `d` macro rounds and modulus `m`: each round runs `combineQ` (`none`)
after all `digitQ p₀` (`some p₀`) for primes `p₀ ≤ m`. -/
private def layerSpec (d m : ℕ) : List (Option ℕ) :=
  match d with
  | 0 => []
  | d + 1 => (none :: (primes m).map some) ++ layerSpec d m

private theorem length_layerSpec (d m : ℕ) :
    (layerSpec d m).length = d * ((primes m).length + 1) := by
  induction d with
  | zero => simp [layerSpec]
  | succ d ih =>
    simp only [layerSpec, List.length_append, List.length_cons, List.length_map, ih]
    ring

/-! #### Precomputing `seedPows` and `CompileCtx` -/

private def seedPowStep (par : List (List (List Bool)) × List Bool)
    (st : List Bool × List (List Bool)) (_ : ℕ) : List Bool × List (List Bool) :=
  (fieldMul par.1 st.1 par.2, st.1 :: st.2)

private def seedPowsForSeed (tab : List (List (List Bool))) (w nWire r : ℕ) : List (List Bool) :=
  let rBits := (List.range w).map fun j => r.testBit j
  let oneBits := true :: List.replicate (w - 1) false
  ((List.range nWire).foldl (seedPowStep (tab, rBits)) (oneBits, [])).2.reverse

private theorem length_seedPowsForSeed (tab : List (List (List Bool))) (w nWire r : ℕ) :
    (seedPowsForSeed tab w nWire r).length = nWire := by
  have haux : ∀ (l : List ℕ) (st : List Bool × List (List Bool)),
      (l.foldl (seedPowStep (tab, (List.range w).map fun j => r.testBit j)) st).2.length =
        st.2.length + l.length := by
    intro l
    induction l with
    | nil => intro st; simp
    | cons _ ls ih =>
      intro st
      simp only [List.foldl_cons, ih, seedPowStep, List.length_cons]
      omega
  simpa only [seedPowsForSeed, List.length_reverse, List.length_nil, List.length_range, zero_add]
    using haux (List.range nWire) (true :: List.replicate (w - 1) false, [])

private theorem seedPowsForSeed_spec {w : ℕ} (hw : w ≠ 0) (nWire : ℕ) {r : ℕ} (hr : r < 2 ^ w) :
    (seedPowsForSeed (fieldTable w) w nWire r).length = nWire ∧
    ∀ i (hi : i < nWire),
      fieldOfBits (BinaryField.basis hw)
        ((seedPowsForSeed (fieldTable w) w nWire r)[i]'(by
          rw [length_seedPowsForSeed]; exact hi)) =
        ((BinaryField.equivFin hw).symm ⟨r, hr⟩) ^ i := by
  set tab := fieldTable w
  set rBits := (List.range w).map fun j => r.testBit j
  set oneBits := true :: List.replicate (w - 1) false
  have htab : IsMulTable (BinaryField.basis hw) tab := isMulTable_fieldTable hw
  have hone : fieldOfBits (BinaryField.basis hw) oneBits = 1 := by
    have hget : ∀ u : Fin w, oneBits.getD u false = ([true] : List Bool).getD u false := by
      intro u
      rcases Nat.eq_zero_or_pos u.1 with hu | hu
      · simp [oneBits, hu]
      · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hu.ne'
        simp [oneBits, hk]
    have heq : fieldOfBits (BinaryField.basis hw) oneBits =
        fieldOfBits (BinaryField.basis hw) [true] := by
      simp only [fieldOfBits, BinaryField.ofBits]
      exact Finset.sum_congr rfl fun u _ => by simp only [hget u]
    exact heq.trans (fieldOfBits_one hw)
  have hrBits : fieldOfBits (BinaryField.basis hw) rBits =
      (BinaryField.equivFin hw).symm ⟨r, hr⟩ := by
    apply (BinaryField.equivBits hw).injective
    ext j
    rw [equivBits_fieldOfBits hw rBits j]
    have hjlt : j.1 < rBits.length := by simp [rBits]
    have h1 : BinaryField.equivBits hw ((BinaryField.equivFin hw).symm ⟨r, hr⟩) =
        (BitString.equivFin w).symm ⟨r, hr⟩ := by
      simp [BinaryField.equivFin]
    rw [h1, BitString.equivFin_symm_apply, List.getD_eq_getElem _ _ hjlt]
    simp [rBits]
  have hfold : ∀ k : ℕ,
      let st := (List.range k).foldl (seedPowStep (tab, rBits)) (oneBits, [])
      fieldOfBits (BinaryField.basis hw) st.1 = ((BinaryField.equivFin hw).symm ⟨r, hr⟩) ^ k ∧
      st.2.length = k ∧
      ∀ i, i < k →
        fieldOfBits (BinaryField.basis hw) (st.2.reverse.getD i []) =
          ((BinaryField.equivFin hw).symm ⟨r, hr⟩) ^ i := by
    intro k
    induction k with
    | zero => exact ⟨by simpa using hone, rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ k ih =>
      obtain ⟨hcur, hlen, hrev⟩ := ih
      dsimp only
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      refine ⟨?_, by simp [seedPowStep, hlen], ?_⟩
      · simp only [seedPowStep, fieldOfBits_fieldMul htab, hcur, hrBits, pow_succ]
      · intro i hi
        simp only [seedPowStep, List.reverse_cons]
        set cur := ((List.range k).foldl (seedPowStep (tab, rBits)) (oneBits, [])).1
        set rev := ((List.range k).foldl (seedPowStep (tab, rBits)) (oneBits, [])).2.reverse
        have hrev_len : rev.length = k := by simp [rev, hlen]
        have hlt_app : i < (rev ++ [cur]).length := by simp [hrev_len]; omega
        rw [List.getD_eq_getElem _ _ hlt_app]
        by_cases hik : i < k
        · rw [List.getElem_append_left (by omega)]
          have hget : rev[i]'(by omega) = rev.getD i [] :=
            (List.getD_eq_getElem rev [] (by omega)).symm
          rw [hget]
          exact hrev i hik
        · have hi_eq : i = k := by omega
          subst hi_eq
          rw [List.getElem_append_right (by omega)]
          simp only [hrev_len, Nat.sub_self, List.getElem_singleton]
          exact hcur
  obtain ⟨_, hlen, hrev⟩ := hfold nWire
  refine ⟨by simpa [seedPowsForSeed] using hlen, fun i hi => ?_⟩
  have hget : (seedPowsForSeed (fieldTable w) w nWire r)[i]'(by
      rw [length_seedPowsForSeed]; exact hi) =
      (seedPowsForSeed (fieldTable w) w nWire r).getD i [] :=
    (List.getD_eq_getElem _ _ (by rw [length_seedPowsForSeed]; exact hi)).symm
  rw [hget]
  exact hrev i hi

private theorem computableInPolyTime_seedPowsForSeed :
    ComputableInPolyTime
      (fun q : List (List (List Bool)) × ℕ × ℕ × ℕ =>
        seedPowsForSeed q.1 q.2.1 q.2.2.1 q.2.2.2)
      (encPair encTable (encPair encUnary (encPair encUnary encUnary)))
      (encList encBits) := by
  let encQ := encPair encTable (encPair encUnary (encPair encUnary encUnary))
  have htab : ComputableInPolyTime (fun q : List (List (List Bool)) × ℕ × ℕ × ℕ => q.1)
      encQ encTable := ComputableInPolyTime.fst _ _
  have hw : ComputableInPolyTime (fun q : List (List (List Bool)) × ℕ × ℕ × ℕ => q.2.1)
      encQ encUnary := (ComputableInPolyTime.snd _ _).fst'
  have hnW : ComputableInPolyTime (fun q : List (List (List Bool)) × ℕ × ℕ × ℕ => q.2.2.1)
      encQ encUnary := (ComputableInPolyTime.snd _ _).snd'.fst'
  have hr : ComputableInPolyTime (fun q : List (List (List Bool)) × ℕ × ℕ × ℕ => q.2.2.2)
      encQ encUnary := (ComputableInPolyTime.snd _ _).snd'.snd'
  have hrBits : ComputableInPolyTime
      (fun q : List (List (List Bool)) × ℕ × ℕ × ℕ =>
        (List.range q.2.1).map fun j => q.2.2.2.testBit j)
      encQ encBits := by
    have hbit : ComputableInPolyTime
        (fun p : (List (List (List Bool)) × ℕ × ℕ × ℕ) × ℕ => p.1.2.2.2.testBit p.2)
        (encPair encQ encUnary) encBool := by
      have hrb : ComputableInPolyTime
          (fun p : (List (List (List Bool)) × ℕ × ℕ × ℕ) × ℕ => p.1.2.2.2.bits)
          (encPair encQ encUnary) encBits :=
        ComputableInPolyTime.natBits.comp
          (ComputableInPolyTime.unary_to_binary.comp (hr.comp (ComputableInPolyTime.fst _ _)))
      exact (ComputableInPolyTime.bitsGetDWithInput hrb
          (ComputableInPolyTime.snd _ _) false).of_enc_eq
        fun p => congrArg encBool (BinarySub.bits_getD _ _).symm
    have hmap := ComputableInPolyTime.mapWithInput
      (f := fun (q : List (List (List Bool)) × ℕ × ℕ × ℕ) j => q.2.2.2.testBit j)
      (ComputableInPolyTime.range.comp hw) hbit
    exact ComputableInPolyTime.listToBits.comp hmap
  have hone : ComputableInPolyTime
      (fun q : List (List (List Bool)) × ℕ × ℕ × ℕ => true :: List.replicate (q.2.1 - 1) false)
      encQ encBits := by
    have hrep : ComputableInPolyTime
        (fun q : List (List (List Bool)) × ℕ × ℕ × ℕ => List.replicate (q.2.1 - 1) false)
        encQ (encList encBool) :=
      ComputableInPolyTime.replicate
        (ComputableInPolyTime.unary_sub.comp (hw.prod (ComputableInPolyTime.const 1)))
        (ComputableInPolyTime.const false)
    exact ComputableInPolyTime.listToBits.comp
      (ComputableInPolyTime.cons' (ComputableInPolyTime.const true) hrep)
  have hstep : ComputableInPolyTime
      (fun p : ((List (List (List Bool)) × List Bool) × (List Bool × List (List Bool))) × ℕ =>
        seedPowStep p.1.1 p.1.2 p.2)
      (encPair (encPair (encPair encTable encBits) (encPair encBits (encList encBits))) encUnary)
      (encPair encBits (encList encBits)) := by
    unfold seedPowStep
    have h1 := ComputableInPolyTime.fst
      (encPair (encPair encTable encBits) (encPair encBits (encList encBits))) encUnary
    have hmul := BinaryField.computableInPolyTime_fieldMul' h1.fst'.fst' h1.snd'.fst' h1.fst'.snd'
    exact hmul.prod (ComputableInPolyTime.cons' h1.snd'.fst' h1.snd'.snd')
  have hfold : ComputableInPolyTime
      (fun q : List (List (List Bool)) × ℕ × ℕ × ℕ =>
        (List.range q.2.2.1).foldl
          (seedPowStep (q.1, (List.range q.2.1).map fun j => q.2.2.2.testBit j))
          (true :: List.replicate (q.2.1 - 1) false, []))
      encQ (encPair encBits (encList encBits)) := by
    refine (ComputableInPolyTime.foldlWith_spec (htab.prod hrBits)
      (ComputableInPolyTime.range.comp hnW)
      (hone.prod (ComputableInPolyTime.const [])) hstep
      (fun q consumed st =>
        st.1.length ≤ max q.1.length q.2.1 + 1 ∧
        st.2.length = consumed.length ∧
        ∀ v ∈ st.2, v.length ≤ max q.1.length q.2.1 + 1)
      (fun q => ⟨by simp; omega, rfl, fun _ h => absurd h List.not_mem_nil⟩)
      (fun q consumed st _ _ ⟨h1, h2, h3⟩ => by
        refine ⟨?_, by simp [seedPowStep, h2], fun v hv => ?_⟩
        · simp only [seedPowStep, BinaryField.length_fieldMul]; omega
        · simp only [seedPowStep, List.mem_cons] at hv
          rcases hv with rfl | hv
          · exact h1
          · exact h3 v hv)
      (size := fun q => 2 * (max q.1.length q.2.1 + 1) + 1 +
          q.2.2.1 * (2 * (max q.1.length q.2.1 + 1) + 1))
      (by
        have htl : PolyBounded (fun q => (encQ q).length) (fun q => q.1.length) :=
          ((ComputableInPolyTime.length_list (encList encBits)).comp htab).polyBounded
        have hwl := hw.polyBounded
        have hmax : PolyBounded (fun q => (encQ q).length) (fun q => max q.1.length q.2.1 + 1) :=
          (htl.add hwl).add (.const 1) |> fun h => PolyBounded.mono h fun _ => by omega
        exact (((PolyBounded.const 2).mul hmax).add (.const 1)).add
          (hnW.polyBounded.mul (((PolyBounded.const 2).mul hmax).add (.const 1))))
      (fun q consumed st hpre ⟨h1, h2, h3⟩ => by
        have hc : consumed.length ≤ q.2.2.1 := by simpa using hpre.length_le
        have hl2 : (encList encBits st.2).length ≤
            q.2.2.1 * (2 * (max q.1.length q.2.1 + 1) + 1) :=
          (length_encList_le encBits st.2 fun v hv => by simpa [encBits_apply] using h3 v hv).trans
            (Nat.mul_le_mul_right _ (h2.le.trans hc))
        rw [length_encPair, encBits_apply]
        omega)).1
  exact ComputableInPolyTime.listReverseWithInput hfold.snd'

private def buildCtx (m : ℕ) (c : Σ n, Circuit Unbounded.extSignature n 1) : CompileCtx :=
  let n := c.1
  let gatesRaw := c.2.code.1
  let g := gatesRaw.length
  let nWire := n + g
  let ℓ := Nat.log 2 nWire + 1
  let w := 2 * ℓ + 2
  let nSeed := min (2 ^ w) (16 * (nWire + 1) ^ 2)
  let modBound := min (2 ^ (w + 1)) (32 * (nWire + 1) ^ 2)
  let modBits := (leastIrreducibleCode modBound w).bits
  let tab := powerMulTable modBits
  let m1 := m + 1
  let nSlot := nWire + g * (m1 * m1)
  let nTotal := nSeed * nSlot
  let gatesU := gatesRaw.map fun line => (extOpTag line.1, line.2.map fun wire => min wire nWire)
  let gatesDedup := gatesU.map fun line => line.2.eraseDupsBy fun a b => decide (a = b)
  let seedPows := (List.range nSeed).map fun r => seedPowsForSeed tab w nWire r
  ⟨n, g, m, w, nSeed, nSlot, nTotal, gatesU, gatesDedup, seedPows⟩

private theorem two_pow_w_le (nWire : ℕ) :
    2 ^ (2 * (Nat.log 2 nWire + 1) + 2) ≤ 16 * (nWire + 1) ^ 2 ∧
    2 ^ (2 * (Nat.log 2 nWire + 1) + 2 + 1) ≤ 32 * (nWire + 1) ^ 2 := by
  have hlog : 2 ^ Nat.log 2 nWire ≤ nWire + 1 := by
    rcases Nat.eq_zero_or_pos nWire with rfl | hpos
    · simp
    · exact (Nat.pow_log_le_self 2 hpos.ne').trans (Nat.le_succ _)
  have hsq : (2 ^ Nat.log 2 nWire) ^ 2 ≤ (nWire + 1) ^ 2 := Nat.pow_le_pow_left hlog 2
  have h1 : 2 ^ (2 * (Nat.log 2 nWire + 1) + 2) = 16 * (2 ^ Nat.log 2 nWire) ^ 2 := by ring
  have h2 : 2 ^ (2 * (Nat.log 2 nWire + 1) + 2 + 1) = 32 * (2 ^ Nat.log 2 nWire) ^ 2 := by ring
  rw [h1, h2]
  exact ⟨Nat.mul_le_mul_left 16 hsq, Nat.mul_le_mul_left 32 hsq⟩

private def buildCtxCore (nWire : ℕ) : (ℕ × ℕ) × List (List (List Bool)) :=
  let ℓ := Nat.log 2 nWire + 1
  let w := 2 * ℓ + 2
  let nSeed := min (2 ^ w) (16 * (nWire + 1) ^ 2)
  let modBound := min (2 ^ (w + 1)) (32 * (nWire + 1) ^ 2)
  let modBits := (leastIrreducibleCode modBound w).bits
  ((w, nSeed), powerMulTable modBits)

private theorem computableInPolyTime_buildCtxCore :
    ComputableInPolyTime buildCtxCore encUnary (encPair (encPair encUnary encUnary) encTable) := by
  have hnWire : ComputableInPolyTime (fun nWire : ℕ => nWire) encUnary encUnary :=
    ComputableInPolyTime.id'
  have hℓ : ComputableInPolyTime (fun nWire : ℕ => Nat.log 2 nWire + 1) encUnary encUnary :=
    ComputableInPolyTime.unary_add.comp
      ((ComputableInPolyTime.unary_log_two.comp hnWire).prod (ComputableInPolyTime.const 1))
  have hw : ComputableInPolyTime (fun nWire : ℕ => 2 * (Nat.log 2 nWire + 1) + 2)
      encUnary encUnary :=
    ComputableInPolyTime.unary_add.comp
      ((ComputableInPolyTime.unary_mul.comp ((ComputableInPolyTime.const 2).prod hℓ)).prod
        (ComputableInPolyTime.const 2))
  have hnWireSq : ComputableInPolyTime (fun nWire : ℕ => (nWire + 1) ^ 2) encUnary encUnary := by
    have hnW1 : ComputableInPolyTime (fun nWire : ℕ => nWire + 1) encUnary encUnary :=
      ComputableInPolyTime.unary_add.comp (hnWire.prod (ComputableInPolyTime.const 1))
    exact (ComputableInPolyTime.unary_mul.comp (hnW1.prod hnW1)).of_enc_eq fun nWire =>
      congrArg encUnary (by dsimp only [Function.comp_apply]; ring)
  have hnSeed : ComputableInPolyTime
      (fun nWire : ℕ => min (2 ^ (2 * (Nat.log 2 nWire + 1) + 2)) (16 * (nWire + 1) ^ 2))
      encUnary encUnary :=
    binary_min_unary_left'
      (ComputableInPolyTime.binary_two_pow.comp hw)
      (ComputableInPolyTime.unary_mul.comp ((ComputableInPolyTime.const 16).prod hnWireSq))
  have hmodBound : ComputableInPolyTime
      (fun nWire : ℕ => min (2 ^ (2 * (Nat.log 2 nWire + 1) + 2 + 1)) (32 * (nWire + 1) ^ 2))
      encUnary encUnary :=
    binary_min_unary_left'
      (ComputableInPolyTime.binary_two_pow.comp
        (ComputableInPolyTime.unary_add.comp (hw.prod (ComputableInPolyTime.const 1))))
      (ComputableInPolyTime.unary_mul.comp ((ComputableInPolyTime.const 32).prod hnWireSq))
  have hcode := BinaryField.computableInPolyTime_leastIrreducibleCode.comp (hmodBound.prod hw)
  have hmodBits : ComputableInPolyTime
      (fun nWire : ℕ =>
        (leastIrreducibleCode
          (min (2 ^ (2 * (Nat.log 2 nWire + 1) + 2 + 1)) (32 * (nWire + 1) ^ 2))
          (2 * (Nat.log 2 nWire + 1) + 2)).bits)
      encUnary encBits :=
    (BinaryField.computableInPolyTime_bits_unary.comp hcode).of_enc_eq fun nWire =>
      congrArg encBits (by simp only [Function.comp_apply])
  have htab : ComputableInPolyTime
      (fun nWire : ℕ =>
        powerMulTable (leastIrreducibleCode
          (min (2 ^ (2 * (Nat.log 2 nWire + 1) + 2 + 1)) (32 * (nWire + 1) ^ 2))
          (2 * (Nat.log 2 nWire + 1) + 2)).bits)
      encUnary encTable :=
    (BinaryField.computableInPolyTime_powerMulTable.comp hmodBits).of_enc_eq fun nWire =>
      congrArg encTable (by simp only [Function.comp_apply])
  exact ((hw.prod hnSeed).prod htab).of_enc_eq fun nWire =>
    congrArg (encPair (encPair encUnary encUnary) encTable) (by unfold buildCtxCore; rfl)

private def buildCtxFrom (m : ℕ)
    (q : (ℕ × List (Unbounded.ExtOp × List ℕ)) × ((ℕ × ℕ) × List (List (List Bool)))) :
    CompileCtx :=
  let n := q.1.1
  let gatesRaw := q.1.2
  let g := gatesRaw.length
  let nWire := n + g
  let w := q.2.1.1
  let nSeed := q.2.1.2
  let tab := q.2.2
  let nSlot := nWire + g * ((m + 1) * (m + 1))
  let nTotal := nSeed * nSlot
  let gatesU := gatesRaw.map fun line => (extOpTag line.1, line.2.map fun wire => min wire nWire)
  let gatesDedup := gatesU.map fun line => line.2.eraseDupsBy fun a b => decide (a = b)
  let seedPows := (List.range nSeed).map fun r => seedPowsForSeed tab w nWire r
  ⟨n, g, m, w, nSeed, nSlot, nTotal, gatesU, gatesDedup, seedPows⟩

private theorem buildCtx_eq_from (m : ℕ) (c : Σ n, Circuit Unbounded.extSignature n 1) :
    buildCtx m c = buildCtxFrom m ((c.1, c.2.code.1), buildCtxCore (c.1 + c.2.code.1.length)) := by
  simp only [buildCtx, buildCtxFrom, buildCtxCore]

private theorem computableInPolyTime_buildCtxFrom (m : ℕ) :
    ComputableInPolyTime (buildCtxFrom m)
      (encPair (encPair encUnary (encList (Circuit.encGate Unbounded.encExtOp)))
        (encPair (encPair encUnary encUnary) encTable))
      encCompileCtx := by
  let encRaw := encPair encUnary (encList (Circuit.encGate Unbounded.encExtOp))
  let encCore := encPair (encPair encUnary encUnary) encTable
  let encQ := encPair encRaw encCore
  have hraw := ComputableInPolyTime.fst encRaw encCore
  have hcore := ComputableInPolyTime.snd encRaw encCore
  have hn := hraw.fst'
  have hgatesRaw := hraw.snd'
  have hg : ComputableInPolyTime
      (fun q : (ℕ × List (Unbounded.ExtOp × List ℕ)) × ((ℕ × ℕ) × List (List (List Bool))) =>
        q.1.2.length)
      encQ encUnary :=
    (ComputableInPolyTime.length_list _).comp hgatesRaw
  have hnWire : ComputableInPolyTime
      (fun q : (ℕ × List (Unbounded.ExtOp × List ℕ)) × ((ℕ × ℕ) × List (List (List Bool))) =>
        q.1.1 + q.1.2.length)
      encQ encUnary :=
    ComputableInPolyTime.unary_add.comp (hn.prod hg)
  have hw := hcore.fst'.fst'
  have hnSeed := hcore.fst'.snd'
  have htab := hcore.snd'
  have hnSlot : ComputableInPolyTime
      (fun q : (ℕ × List (Unbounded.ExtOp × List ℕ)) × ((ℕ × ℕ) × List (List (List Bool))) =>
        q.1.1 + q.1.2.length + q.1.2.length * ((m + 1) * (m + 1)))
      encQ encUnary :=
    ComputableInPolyTime.unary_add.comp
      (hnWire.prod
        (ComputableInPolyTime.unary_mul.comp
          (hg.prod (ComputableInPolyTime.const ((m + 1) * (m + 1))))))
  have hnTotal : ComputableInPolyTime
      (fun q : (ℕ × List (Unbounded.ExtOp × List ℕ)) × ((ℕ × ℕ) × List (List (List Bool))) =>
        q.2.1.2 * (q.1.1 + q.1.2.length + q.1.2.length * ((m + 1) * (m + 1))))
      encQ encUnary :=
    ComputableInPolyTime.unary_mul.comp (hnSeed.prod hnSlot)
  have hgatesU : ComputableInPolyTime
      (fun q : (ℕ × List (Unbounded.ExtOp × List ℕ)) × ((ℕ × ℕ) × List (List (List Bool))) =>
        q.1.2.map fun line =>
          (extOpTag line.1, line.2.map fun wire => min wire (q.1.1 + q.1.2.length)))
      encQ (encList (encPair encUnary (encList encUnary))) := by
    let encG := Circuit.encGate Unbounded.encExtOp
    have hline : ComputableInPolyTime
        (fun p : ((ℕ × List (Unbounded.ExtOp × List ℕ)) × ((ℕ × ℕ) × List (List (List Bool)))) ×
            (Unbounded.ExtOp × List ℕ) =>
          (extOpTag p.2.1, p.2.2.map fun wire => min wire (p.1.1.1 + p.1.1.2.length)))
        (encPair encQ encG) (encPair encUnary (encList encUnary)) := by
      have htag := computableInPolyTime_extOpTag.comp (ComputableInPolyTime.snd encQ encG).fst'
      have hws := ComputableInPolyTime.mapWithInput
        (f := fun (p : ((ℕ × List (Unbounded.ExtOp × List ℕ)) ×
            ((ℕ × ℕ) × List (List (List Bool)))) × (Unbounded.ExtOp × List ℕ)) (wire : ℕ) =>
          min wire (p.1.1.1 + p.1.1.2.length))
        (ComputableInPolyTime.snd encQ encG).snd'
        (binary_min_unary_left'
          (ComputableInPolyTime.snd (encPair encQ encG) encNat)
          (hnWire.comp (ComputableInPolyTime.fst (encPair encQ encG) encNat).fst'))
      exact htag.prod hws
    exact ComputableInPolyTime.mapWithInput hgatesRaw hline
  have hgatesDedup : ComputableInPolyTime
      (fun q : (ℕ × List (Unbounded.ExtOp × List ℕ)) × ((ℕ × ℕ) × List (List (List Bool))) =>
        (q.1.2.map fun line =>
          (extOpTag line.1, line.2.map fun wire => min wire (q.1.1 + q.1.2.length))).map
          fun line => line.2.eraseDupsBy fun a b => decide (a = b))
      encQ (encList (encList encUnary)) := by
    have hded : ComputableInPolyTime
        (fun p : ((ℕ × List (Unbounded.ExtOp × List ℕ)) × ((ℕ × ℕ) × List (List (List Bool)))) ×
            (ℕ × List ℕ) =>
          p.2.2.eraseDupsBy fun a b => decide (a = b))
        (encPair encQ (encPair encUnary (encList encUnary))) (encList encUnary) :=
      ComputableInPolyTime.eraseDupsByWithInput (ComputableInPolyTime.snd _ _).snd'
        (ComputableInPolyTime.decide_eq' (ComputableInPolyTime.fst _ _).snd'
          (ComputableInPolyTime.snd _ _))
    exact ComputableInPolyTime.mapWithInput hgatesU hded
  have hone : ComputableInPolyTime
      (fun p : ((ℕ × List (Unbounded.ExtOp × List ℕ)) × ((ℕ × ℕ) × List (List (List Bool)))) × ℕ =>
        seedPowsForSeed p.1.2.2 p.1.2.1.1 (p.1.1.1 + p.1.1.2.length) p.2)
      (encPair encQ encUnary) (encList encBits) :=
    (computableInPolyTime_seedPowsForSeed.comp
      ((htab.comp (ComputableInPolyTime.fst encQ encUnary)).prod
        ((hw.comp (ComputableInPolyTime.fst encQ encUnary)).prod
          ((hnWire.comp (ComputableInPolyTime.fst encQ encUnary)).prod
            (ComputableInPolyTime.snd encQ encUnary))))).of_enc_eq fun p =>
      congrArg (encList encBits) (by simp only [Function.comp_apply])
  have hseedPows : ComputableInPolyTime
      (fun q : (ℕ × List (Unbounded.ExtOp × List ℕ)) × ((ℕ × ℕ) × List (List (List Bool))) =>
        (List.range q.2.1.2).map fun r => seedPowsForSeed q.2.2 q.2.1.1 (q.1.1 + q.1.2.length) r)
      encQ (encList (encList encBits)) :=
    (ComputableInPolyTime.mapWithInput
      (f := fun (q : (ℕ × List (Unbounded.ExtOp × List ℕ)) ×
          ((ℕ × ℕ) × List (List (List Bool)))) (r : ℕ) =>
        seedPowsForSeed q.2.2 q.2.1.1 (q.1.1 + q.1.2.length) r)
      (ComputableInPolyTime.range.comp hnSeed) hone).of_enc_eq fun q =>
        congrArg (encList (encList encBits)) (by simp only [Function.comp_apply])
  have hm := ComputableInPolyTime.const (encIn := encQ) (encOut := encUnary) m
  have hmk := encCompileCtx_mk_polyTime hn hg hm hw hnSeed hnSlot hnTotal hgatesU hgatesDedup
    hseedPows
  exact hmk.of_enc_eq fun q => congrArg encCompileCtx <| by unfold buildCtxFrom; rfl

private theorem computableInPolyTime_buildCtx (m : ℕ) :
    ComputableInPolyTime (buildCtx m) (Unbounded.encExtCircuit 1) encCompileCtx := by
  have har := Circuit.computableInPolyTime_arity_code (σ := Unbounded.extSignature)
    Unbounded.encExtOp 1
  have hraw := har.fst'.prod har.snd'.fst'
  have hnWire := ComputableInPolyTime.unary_add.comp
    (har.fst'.prod ((ComputableInPolyTime.length_list _).comp har.snd'.fst'))
  have hcore := computableInPolyTime_buildCtxCore.comp hnWire
  exact ((computableInPolyTime_buildCtxFrom m).comp (hraw.prod hcore)).of_enc_eq fun c =>
    congrArg encCompileCtx (by simp only [Function.comp_apply, buildCtx_eq_from])

/-! #### Budget-capped subset enumeration -/

private def extendSubsetsStep (par : ℕ × ℕ) (st : List (List ℕ) × List (List ℕ)) (_ : ℕ) :
    List (List ℕ) × List (List ℕ) :=
  let next := (st.2.flatMap fun s =>
    (List.range (min (s.headD par.1) par.1)).map fun a => a :: s).take par.2
  ((st.1 ++ next).take par.2, next)

private def subsetsUpToCapped (N D U : ℕ) : List (List ℕ) :=
  ((List.range D).foldl (extendSubsetsStep (N, U)) ([[]], [[]])).1

private theorem computableInPolyTime_subsetsUpToCapped :
    ComputableInPolyTime (fun p : ℕ × ℕ × ℕ => subsetsUpToCapped p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encUnary encUnary)) (encList (encList encUnary)) := by
  let encP := encPair encUnary (encPair encUnary encUnary)
  let encS := encPair (encList (encList encUnary)) (encList (encList encUnary))
  have hN : ComputableInPolyTime (fun p : ℕ × ℕ × ℕ => p.1) encP encUnary :=
    ComputableInPolyTime.fst _ _
  have hD : ComputableInPolyTime (fun p : ℕ × ℕ × ℕ => p.2.1) encP encUnary :=
    (ComputableInPolyTime.snd _ _).fst'
  have hU : ComputableInPolyTime (fun p : ℕ × ℕ × ℕ => p.2.2) encP encUnary :=
    (ComputableInPolyTime.snd _ _).snd'
  have hstep : ComputableInPolyTime
      (fun q : ((ℕ × ℕ) × (List (List ℕ) × List (List ℕ))) × ℕ =>
        extendSubsetsStep q.1.1 q.1.2 q.2)
      (encPair (encPair (encPair encUnary encUnary) encS) encUnary) encS := by
    unfold extendSubsetsStep
    let encQ := encPair (encPair (encPair encUnary encUnary) encS) encUnary
    have hq1 := ComputableInPolyTime.fst (encPair (encPair encUnary encUnary) encS) encUnary
    have hqN := hq1.fst'.fst'
    have hqU := hq1.fst'.snd'
    have hqAcc := hq1.snd'.fst'
    have hqCur := hq1.snd'.snd'
    have hexpand : ComputableInPolyTime
        (fun r : (((ℕ × ℕ) × (List (List ℕ) × List (List ℕ))) × ℕ) × List ℕ =>
          (List.range (min (r.2.headD r.1.1.1.1) r.1.1.1.1)).map fun a => a :: r.2)
        (encPair encQ (encList encUnary)) (encList (encList encUnary)) := by
      have hhead : ComputableInPolyTime
          (fun r : (((ℕ × ℕ) × (List (List ℕ) × List (List ℕ))) × ℕ) × List ℕ =>
            min (r.2.headD r.1.1.1.1) r.1.1.1.1)
          (encPair encQ (encList encUnary)) encUnary := by
        have hhd := ComputableInPolyTime.listHeadDWithInput (ComputableInPolyTime.snd _ _)
          (hqN.comp (ComputableInPolyTime.fst _ _))
        exact ComputableInPolyTime.unary_min' hhd (hqN.comp (ComputableInPolyTime.fst _ _))
      exact ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp hhead)
        (ComputableInPolyTime.cons' (ComputableInPolyTime.snd _ _)
          (ComputableInPolyTime.fst _ _).snd')
    have hnext := ComputableInPolyTime.listTakeWithInput
      (ComputableInPolyTime.flatMapWithInput
        (f := fun q s => (List.range (min (s.headD q.1.1.1) q.1.1.1)).map fun a => a :: s)
        hqCur hexpand) hqU
    have hacc' := ComputableInPolyTime.listTakeWithInput
      (ComputableInPolyTime.listAppend' hqAcc hnext) hqU
    exact hacc'.prod hnext
  have hfold := ComputableInPolyTime.foldlWith_spec (hN.prod hU)
    (ComputableInPolyTime.range.comp hD) (ComputableInPolyTime.const ([[]], [[]])) hstep
    (fun p consumed st =>
      st.1.length ≤ p.2.2 + 1 ∧ st.2.length ≤ p.2.2 + 1 ∧
      (∀ s ∈ st.1, s.length ≤ consumed.length ∧ ∀ a ∈ s, a < p.1) ∧
      (∀ s ∈ st.2, s.length ≤ consumed.length ∧ ∀ a ∈ s, a < p.1))
    (fun _ => ⟨by simp, by simp, fun s hs => by simp [List.mem_singleton.1 hs],
      fun s hs => by simp [List.mem_singleton.1 hs]⟩)
    (fun p consumed st _ _ ⟨h1, h2, h3, h4⟩ => by
      have hnext_mem : ∀ s ∈ (st.2.flatMap fun s =>
          (List.range (min (s.headD p.1) p.1)).map fun a => a :: s).take p.2.2,
          s.length ≤ consumed.length + 1 ∧ ∀ a ∈ s, a < p.1 := by
        intro s hs
        have hs' := List.mem_of_mem_take hs
        obtain ⟨t, ht, hts⟩ := List.mem_flatMap.1 hs'
        obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hts
        have ha' : a < p.1 := lt_of_lt_of_le (List.mem_range.1 ha) (Nat.min_le_right _ _)
        obtain ⟨htl, hta⟩ := h4 t ht
        refine ⟨by simp; omega, fun x hx => ?_⟩
        rcases List.mem_cons.1 hx with rfl | hx
        · exact ha'
        · exact hta x hx
      refine ⟨(List.length_take_le _ _).trans (Nat.le_succ _),
        (List.length_take_le _ _).trans (Nat.le_succ _), fun s hs => ?_, fun s hs => ?_⟩
      · have hs' := List.mem_of_mem_take hs
        rcases List.mem_append.1 hs' with hs' | hs'
        · obtain ⟨hl, ha⟩ := h3 s hs'
          exact ⟨by simp only [List.length_append, List.length_singleton]; omega, ha⟩
        · obtain ⟨hl, ha⟩ := hnext_mem s hs'
          exact ⟨by simp only [List.length_append, List.length_singleton]; omega, ha⟩
      · obtain ⟨hl, ha⟩ := hnext_mem s hs
        exact ⟨by simp only [List.length_append, List.length_singleton]; omega, ha⟩)
    (size := fun p =>
      3 * ((p.2.2 + 1) * (2 * (p.2.1 * (2 * p.1 + 1)) + 1)) + 1)
    (by
      have h1 := hN.polyBounded
      have h2 := hD.polyBounded
      have h3 := hU.polyBounded
      exact ((PolyBounded.const 3).mul
        ((h3.add (.const 1)).mul
          (((PolyBounded.const 2).mul
            (h2.mul (((PolyBounded.const 2).mul h1).add (.const 1)))).add (.const 1)))).add
        (.const 1))
    (fun p consumed st hpre ⟨h1, h2, h3, h4⟩ => by
      have hc : consumed.length ≤ p.2.1 := by simpa using hpre.length_le
      have hboundList : ∀ (L : List (List ℕ)), L.length ≤ p.2.2 + 1 →
          (∀ s ∈ L, s.length ≤ consumed.length ∧ ∀ a ∈ s, a < p.1) →
          (encList (encList encUnary) L).length ≤
            (p.2.2 + 1) * (2 * (p.2.1 * (2 * p.1 + 1)) + 1) := by
        intro L hL hmem
        refine (length_encList_le (encList encUnary) L (b := p.2.1 * (2 * p.1 + 1))
          fun s hs => ?_).trans (Nat.mul_le_mul_right _ hL)
        obtain ⟨hsl, hsa⟩ := hmem s hs
        exact (length_encList_le encUnary s (b := p.1) fun a ha => by
          simpa only [encUnary_apply, List.length_replicate] using (hsa a ha).le).trans
          (Nat.mul_le_mul_right _ (hsl.trans hc))
      rw [length_encPair]
      have hb1 := hboundList st.1 h1 h3
      have hb2 := hboundList st.2 h2 h4
      omega)
  exact hfold.1.fst'

private def allSubsetsStep (U : ℕ) (acc : List (List ℕ)) (a : ℕ) : List (List ℕ) :=
  (acc ++ acc.map (a :: ·)).take U

private def allSubsetsCapped (S : List ℕ) (U : ℕ) : List (List ℕ) :=
  S.foldl (allSubsetsStep U) [[]]

private theorem computableInPolyTime_allSubsetsCapped :
    ComputableInPolyTime (fun p : List ℕ × ℕ => allSubsetsCapped p.1 p.2)
      (encPair (encList encUnary) encUnary) (encList (encList encUnary)) := by
  let encP := encPair (encList encUnary) encUnary
  have hS := ComputableInPolyTime.fst (encList encUnary) encUnary
  have hU := ComputableInPolyTime.snd (encList encUnary) encUnary
  have hstep : ComputableInPolyTime
      (fun q : (ℕ × List (List ℕ)) × ℕ => allSubsetsStep q.1.1 q.1.2 q.2)
      (encPair (encPair encUnary (encList (encList encUnary))) encUnary)
      (encList (encList encUnary)) := by
    unfold allSubsetsStep
    let encQ := encPair (encPair encUnary (encList (encList encUnary))) encUnary
    have hq1 := ComputableInPolyTime.fst (encPair encUnary (encList (encList encUnary))) encUnary
    have hcons : ComputableInPolyTime
        (fun p : ((ℕ × List (List ℕ)) × ℕ) × List ℕ => p.1.2 :: p.2)
        (encPair encQ (encList encUnary)) (encList encUnary) :=
      ComputableInPolyTime.cons'
        ((ComputableInPolyTime.snd (encPair encUnary (encList (encList encUnary))) encUnary).comp
          (ComputableInPolyTime.fst encQ (encList encUnary)))
        (ComputableInPolyTime.snd encQ (encList encUnary))
    have hmap := ComputableInPolyTime.mapWithInput
      (f := fun (q : (ℕ × List (List ℕ)) × ℕ) (s : List ℕ) => q.2 :: s) hq1.snd' hcons
    exact ComputableInPolyTime.listTakeWithInput
      (ComputableInPolyTime.listAppend' hq1.snd' hmap) hq1.fst'
  exact (ComputableInPolyTime.foldlWith_spec hU hS (ComputableInPolyTime.const [[]]) hstep
    (fun p consumed acc =>
      acc.length ≤ p.2 + 1 ∧
      ∀ t ∈ acc, t.length ≤ consumed.length ∧ ∀ x ∈ t, x ∈ p.1)
    (fun _ => ⟨by simp, fun t ht => by simp [List.mem_singleton.1 ht]⟩)
    (fun p consumed acc a hpre ⟨hl, hmem⟩ => by
      have ha : a ∈ p.1 := hpre.subset (by simp)
      refine ⟨(List.length_take_le _ _).trans (Nat.le_succ _), fun t ht => ?_⟩
      rcases List.mem_append.1 (List.mem_of_mem_take ht) with ht | ht
      · obtain ⟨htl, htx⟩ := hmem t ht
        exact ⟨by simp only [List.length_append, List.length_singleton]; omega, htx⟩
      · obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ht
        obtain ⟨htl, htx⟩ := hmem t' ht'
        exact ⟨by simp; omega, fun x hx => (List.mem_cons.1 hx).elim (· ▸ ha) (htx x)⟩)
    (size := fun p =>
      (p.2 + 1) * (2 * (p.1.length * (2 * (encList encUnary p.1).length + 1)) + 1))
    (by
      have h1 := hU.polyBounded
      have h2 := ((ComputableInPolyTime.length_list encUnary).comp hS).polyBounded
      have h3 := hS.polyBounded_length
      exact (h1.add (.const 1)).mul
        (((PolyBounded.const 2).mul (h2.mul (((PolyBounded.const 2).mul h3).add (.const 1)))).add
          (.const 1)))
    (fun p consumed acc hpre ⟨hl, hmem⟩ => by
      have hc : consumed.length ≤ p.1.length := hpre.length_le
      refine (length_encList_le (encList encUnary) acc
        (b := p.1.length * (2 * (encList encUnary p.1).length + 1)) fun t ht => ?_).trans
        (Nat.mul_le_mul_right _ hl)
      obtain ⟨htl, htx⟩ := hmem t ht
      exact (length_encList_le encUnary t (b := (encList encUnary p.1).length) fun x hx =>
        SizedListEncoding.length_elem_le (encA := encUnary) (encL := encList encUnary) p.1 x
          (htx x hx)).trans (Nat.mul_le_mul_right _ (htl.trans hc)))).1

/-! #### Evaluating layer polynomials, parity amplifier, and amplified count modulo `M` -/

/-- `(1 - (parityAmplifier k).eval y) mod M` in pure `ℕ` arithmetic, for `k` in unary and
`M, y` in binary. -/
private def evalOneSubParityAmpMod (k M y : ℕ) : ℕ :=
  let oneSubY := (M + 1 - y % M) % M
  let fac := powMod M oneSubY k
  let kern := ((List.range k).map fun j =>
    ((k - 1 + j).choose j % M) * powMod M y j % M).sum % M
  (M + 1 - fac * kern % M) % M

private theorem one_sub_modEq_of_pos {M : ℕ} (hM : 0 < M) (a : ℕ) :
    (((M + 1 - a % M) % M : ℕ) : ℤ) ≡ 1 - (a : ℤ) [ZMOD (M : ℤ)] := by
  have hlt : a % M < M := Nat.mod_lt a hM
  rw [Int.natCast_mod, Int.natCast_sub (by omega : a % M ≤ M + 1)]
  push_cast
  have hmod : (a : ℤ) % (M : ℤ) ≡ (a : ℤ) [ZMOD (M : ℤ)] := Int.mod_modEq _ _
  have h1 : (M : ℤ) + 1 - (a : ℤ) % (M : ℤ) ≡ 0 + 1 - (a : ℤ) [ZMOD (M : ℤ)] :=
    (Int.ModEq.add_right 1 (Int.modEq_zero_iff_dvd.2 dvd_rfl)).sub hmod
  simpa only [zero_add] using (Int.mod_modEq _ _).trans h1

private theorem evalOneSubParityAmpMod_modEq {k M y : ℕ} (hM : 0 < M) :
    ((evalOneSubParityAmpMod k M y : ℕ) : ℤ) ≡
      1 - (parityAmplifier k).eval (y : ℤ) [ZMOD (M : ℤ)] := by
  have hsub := one_sub_modEq_of_pos hM
  have hpow : ∀ (a e : ℕ), ((powMod M a e : ℕ) : ℤ) ≡ (a : ℤ) ^ e [ZMOD (M : ℤ)] := fun a e => by
    rw [powMod_of_ne_zero hM.ne', Int.natCast_mod, Int.natCast_pow]
    exact Int.mod_modEq _ _
  have hfac : ((powMod M ((M + 1 - y % M) % M) k : ℕ) : ℤ) ≡
      (1 - (y : ℤ)) ^ k [ZMOD (M : ℤ)] :=
    (hpow _ k).trans ((hsub y).pow k)
  have hkern : ((((List.range k).map fun j =>
        ((k - 1 + j).choose j % M) * powMod M y j % M).sum % M : ℕ) : ℤ) ≡
      (parityKernel k).eval (y : ℤ) [ZMOD (M : ℤ)] := by
    rw [Int.natCast_mod]
    refine (Int.mod_modEq _ _).trans ?_
    rw [parityKernel, paritySeriesAux]
    rw [← Polynomial.coe_evalRingHom, map_sum]
    have hsum : ((((List.range k).map fun j =>
        ((k - 1 + j).choose j % M) * powMod M y j % M).sum : ℕ) : ℤ) =
        ∑ j ∈ Finset.range k,
          ((((k - 1 + j).choose j % M) * powMod M y j % M : ℕ) : ℤ) := by
      rw [Nat.cast_list_sum, List.map_map, ← List.sum_toFinset _ List.nodup_range,
        List.toFinset_range]
      simp
    rw [hsum]
    refine Int.ModEq.sum fun j _ => ?_
    simp only [Polynomial.coe_evalRingHom, eval_mul, eval_natCast, eval_pow, eval_X,
      Int.natCast_mod, Nat.cast_mul]
    refine (Int.mod_modEq _ _).trans ?_
    refine Int.ModEq.mul ?_ (hpow y j)
    exact Int.mod_modEq _ _
  have hamp : ((powMod M ((M + 1 - y % M) % M) k *
      (((List.range k).map fun j =>
        ((k - 1 + j).choose j % M) * powMod M y j % M).sum % M) % M : ℕ) : ℤ) ≡
      (parityAmplifier k).eval (y : ℤ) [ZMOD (M : ℤ)] := by
    rw [Int.natCast_mod, Nat.cast_mul, parityAmplifier, eval_mul, eval_pow, eval_sub, eval_one,
      eval_X]
    exact (Int.mod_modEq _ _).trans (hfac.mul hkern)
  unfold evalOneSubParityAmpMod
  dsimp only
  have h1 := hsub (powMod M ((M + 1 - y % M) % M) k *
    (((List.range k).map fun j =>
      ((k - 1 + j).choose j % M) * powMod M y j % M).sum % M) % M)
  rw [Nat.mod_mod] at h1
  exact h1.trans (Int.ModEq.sub_left 1 hamp)

private theorem computableInPolyTime_evalOneSubParityAmpMod :
    ComputableInPolyTime (fun p : ℕ × ℕ × ℕ => evalOneSubParityAmpMod p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encNat encNat)) encNat := by
  let encP := encPair encUnary (encPair encNat encNat)
  have hk : ComputableInPolyTime (fun p : ℕ × ℕ × ℕ => p.1) encP encUnary :=
    ComputableInPolyTime.fst _ _
  have hM : ComputableInPolyTime (fun p : ℕ × ℕ × ℕ => p.2.1) encP encNat :=
    (ComputableInPolyTime.snd _ _).fst'
  have hy : ComputableInPolyTime (fun p : ℕ × ℕ × ℕ => p.2.2) encP encNat :=
    (ComputableInPolyTime.snd _ _).snd'
  have hsubMod : ∀ {α : Type} {encIn : α ↪ List Bool} {fM fa : α → ℕ},
      ComputableInPolyTime fM encIn encNat → ComputableInPolyTime fa encIn encNat →
      ComputableInPolyTime (fun x => (fM x + 1 - fa x % fM x) % fM x) encIn encNat :=
    fun hfM hfa =>
      ComputableInPolyTime.binary_mod'
        (ComputableInPolyTime.binary_sub'
          (ComputableInPolyTime.binary_add' hfM (ComputableInPolyTime.const 1))
          (ComputableInPolyTime.binary_mod' hfa hfM))
        hfM
  have honeSubY := hsubMod hM hy
  have hfac := computableInPolyTime_powMod hM honeSubY
    (ComputableInPolyTime.unary_to_binary.comp hk)
  have hterm : ComputableInPolyTime
      (fun q : (ℕ × ℕ × ℕ) × ℕ =>
        ((q.1.1 - 1 + q.2).choose q.2 % q.1.2.1) * powMod q.1.2.1 q.1.2.2 q.2 % q.1.2.1)
      (encPair encP encUnary) encNat := by
    have hq1 := ComputableInPolyTime.fst encP encUnary
    have hqj := ComputableInPolyTime.snd encP encUnary
    have hqk := hk.comp hq1
    have hqM := hM.comp hq1
    have hqy := hy.comp hq1
    have hch := ComputableInPolyTime.binary_choose'
      (ComputableInPolyTime.unary_add.comp
        ((ComputableInPolyTime.unary_sub.comp (hqk.prod (ComputableInPolyTime.const 1))).prod hqj))
      hqj
    have hpw := computableInPolyTime_powMod hqM hqy (ComputableInPolyTime.unary_to_binary.comp hqj)
    exact ComputableInPolyTime.binary_mod'
      (ComputableInPolyTime.binary_mul.comp ((ComputableInPolyTime.binary_mod' hch hqM).prod hpw))
      hqM
  have hkern := ComputableInPolyTime.binary_mod'
    (ComputableInPolyTime.binary_sum.comp
      (ComputableInPolyTime.mapWithInput
        (f := fun (q : ℕ × ℕ × ℕ) j =>
          ((q.1 - 1 + j).choose j % q.2.1) * powMod q.2.1 q.2.2 j % q.2.1)
        (ComputableInPolyTime.range.comp hk) hterm))
    hM
  have hpVal := ComputableInPolyTime.binary_mul.comp (hfac.prod hkern)
  exact (hsubMod hM hpVal).of_enc_eq fun p => congrArg encNat <| by
    unfold evalOneSubParityAmpMod; rfl

/-- Product `∏_{j < w} (1 - ∑_{wire ∈ ws} [r^wire]_j * (xor negate u(r, wire))) mod posMod M`. -/
private def orTestProdMod (w M : ℕ) (pows : List (List Bool)) (ws : List ℕ)
    (rOff : ℕ) (uSub : List ℕ) (negate : Bool) : ℕ :=
  let M' := posMod M
  (List.range w).foldl (fun acc j =>
    let cnt := ws.countP fun wire =>
      ((pows.getD wire []).getD j false) &&
        xor negate (uSub.any fun x => decide (x = rOff + wire))
    acc * ((M' + 1 - cnt % M') % M') % M') (1 % M')

private theorem computableInPolyTime_orTestProdMod :
    ComputableInPolyTime
      (fun q : ((ℕ × ℕ) × (List (List Bool) × List ℕ)) × ((ℕ × List ℕ) × Bool) =>
        orTestProdMod q.1.1.1 q.1.1.2 q.1.2.1 q.1.2.2 q.2.1.1 q.2.1.2 q.2.2)
      (encPair (encPair (encPair encUnary encNat) (encPair (encList encBits) (encList encUnary)))
        (encPair (encPair encUnary (encList encUnary)) encBool))
      encNat := by
  let encQ := encPair (encPair (encPair encUnary encNat)
    (encPair (encList encBits) (encList encUnary)))
    (encPair (encPair encUnary (encList encUnary)) encBool)
  have hqW : ComputableInPolyTime
      (fun q : ((ℕ × ℕ) × (List (List Bool) × List ℕ)) × ((ℕ × List ℕ) × Bool) => q.1.1.1)
      encQ encUnary := (ComputableInPolyTime.fst _ _).fst'.fst'
  have hqM : ComputableInPolyTime
      (fun q : ((ℕ × ℕ) × (List (List Bool) × List ℕ)) × ((ℕ × List ℕ) × Bool) =>
        posMod q.1.1.2)
      encQ encNat := computableInPolyTime_posMod (ComputableInPolyTime.fst _ _).fst'.snd'
  have hinit : ComputableInPolyTime
      (fun q : ((ℕ × ℕ) × (List (List Bool) × List ℕ)) × ((ℕ × List ℕ) × Bool) =>
        1 % posMod q.1.1.2)
      encQ encNat := ComputableInPolyTime.binary_mod' (ComputableInPolyTime.const 1) hqM
  have hstep : ComputableInPolyTime
      (fun p : ((((ℕ × ℕ) × (List (List Bool) × List ℕ)) × ((ℕ × List ℕ) × Bool)) × ℕ) × ℕ =>
        let q := p.1.1; let acc := p.1.2; let j := p.2
        let M' := posMod q.1.1.2
        let cnt := q.1.2.2.countP fun wire =>
          ((q.1.2.1.getD wire []).getD j false) &&
            xor q.2.2 (q.2.1.2.any fun x => decide (x = q.2.1.1 + wire))
        acc * ((M' + 1 - cnt % M') % M') % M')
      (encPair (encPair encQ encNat) encUnary) encNat := by
    let encP := encPair (encPair encQ encNat) encUnary
    have hpq := (ComputableInPolyTime.fst (encPair encQ encNat) encUnary).fst'
    have hacc := (ComputableInPolyTime.fst (encPair encQ encNat) encUnary).snd'
    have hj := ComputableInPolyTime.snd (encPair encQ encNat) encUnary
    have hpM := hqM.comp hpq
    have hws : ComputableInPolyTime
        (fun p : ((((ℕ × ℕ) × (List (List Bool) × List ℕ)) × ((ℕ × List ℕ) × Bool)) × ℕ) × ℕ =>
          p.1.1.1.2.2) encP (encList encUnary) :=
      ((ComputableInPolyTime.fst _ _).snd'.snd').comp hpq
    have hpred : ComputableInPolyTime
        (fun r : (((((ℕ × ℕ) × (List (List Bool) × List ℕ)) ×
            ((ℕ × List ℕ) × Bool)) × ℕ) × ℕ) × ℕ =>
          ((r.1.1.1.1.2.1.getD r.2 []).getD r.1.2 false) &&
            xor r.1.1.1.2.2 (r.1.1.1.2.1.2.any fun x => decide (x = r.1.1.1.2.1.1 + r.2)))
        (encPair encP encUnary) encBool := by
      have hrp := ComputableInPolyTime.fst encP encUnary
      have hrw := ComputableInPolyTime.snd encP encUnary
      have hrq := hpq.comp hrp
      have hbit := ComputableInPolyTime.bitsGetDWithInput
        (ComputableInPolyTime.listGetDWithInput
          (((ComputableInPolyTime.fst _ _).snd'.fst').comp hrq) hrw [])
        (hj.comp hrp) false
      have hany := ComputableInPolyTime.anyWithInput
        (test := fun r x => decide (x = r.1.1.1.2.1.1 + r.2))
        (((ComputableInPolyTime.snd _ _).fst'.snd').comp hrq)
        (ComputableInPolyTime.unary_eq'
          (ComputableInPolyTime.snd _ _)
          (ComputableInPolyTime.unary_add.comp
            ((((ComputableInPolyTime.snd _ _).fst'.fst').comp
              (hrq.comp (ComputableInPolyTime.fst _ _))).prod
              (hrw.comp (ComputableInPolyTime.fst _ _)))))
      have hxor : ComputableInPolyTime
          (fun r : (((((ℕ × ℕ) × (List (List Bool) × List ℕ)) ×
              ((ℕ × List ℕ) × Bool)) × ℕ) × ℕ) × ℕ =>
            xor r.1.1.1.2.2 (r.1.1.1.2.1.2.any fun x => decide (x = r.1.1.1.2.1.1 + r.2)))
          (encPair encP encUnary) encBool :=
        (ComputableInPolyTime.of_finite (encIn := encPair encBool encBool) (encOut := encBool)
          fun b : Bool × Bool => xor b.1 b.2).comp
          ((((ComputableInPolyTime.snd _ _).snd').comp hrq).prod hany)
      exact ComputableInPolyTime.bool_and' hbit hxor
    have hcntU := ComputableInPolyTime.countPWithInput
      (test := fun p wire =>
        ((p.1.1.1.2.1.getD wire []).getD p.2 false) &&
          xor p.1.1.2.2 (p.1.1.2.1.2.any fun x => decide (x = p.1.1.2.1.1 + wire)))
      hws hpred
    have hcntB := ComputableInPolyTime.unary_to_binary.comp hcntU
    have hfac := ComputableInPolyTime.binary_mod'
      (ComputableInPolyTime.binary_sub'
        (ComputableInPolyTime.binary_add' hpM (ComputableInPolyTime.const 1))
        (ComputableInPolyTime.binary_mod' hcntB hpM))
      hpM
    exact ComputableInPolyTime.binary_mod'
      (ComputableInPolyTime.binary_mul.comp (hacc.prod hfac)) hpM
  refine ComputableInPolyTime.foldlWith ComputableInPolyTime.id'
    (ComputableInPolyTime.range.comp hqW) hinit hstep
    (B := fun q => (encQ q).length + 1)
    (PolyBounded.self.add (.const 1)) fun q i _ => ?_
  have hMle : (encNat q.1.1.2).length ≤ (encQ q).length := by
    dsimp only [encQ]; enc_len
  refine le_trans ?_ (Nat.add_le_add_right hMle 1)
  have hle := foldl_mod_posMod_le q.1.1.2
    (fun acc j =>
      let cnt := q.1.2.2.countP fun wire =>
        ((q.1.2.1.getD wire []).getD j false) &&
          xor q.2.2 (q.2.1.2.any fun x => decide (x = q.2.1.1 + wire))
      acc * ((posMod q.1.1.2 + 1 - cnt % posMod q.1.1.2) % posMod q.1.1.2))
    ((List.range q.1.1.1).take i)
    (Nat.mod_lt 1 (posMod_pos q.1.1.2)).le
  change (Nat.bits _).length ≤ q.1.1.2.bits.length + 1
  simpa only [← Nat.size_eq_bits_len] using size_le_size_add_one_of_le_posMod hle

/-- Evaluate `L.lift.q t (1_{uSub}) mod M` in pure `ℕ` arithmetic, for a fixed layer
(`none` = `combineQ`, `some p₀` = `digitQ p₀`) and modulus `m`. -/
private def evalLayerQMod (m : ℕ) (layer : Option ℕ) (ctx : CompileCtx)
    (M : ℕ) (uSub : List ℕ) (t : ℕ) : ℕ :=
  let r := t / ctx.nSlot
  let s := t % ctx.nSlot
  let rOff := r * ctx.nSlot
  let nWire := ctx.n + ctx.g
  let m1 := m + 1
  match layer with
  | none =>
    if s < ctx.n then
      if uSub.any fun x => decide (x = t) then 1 % M else 0
    else if s < nWire then
      let k := s - ctx.n
      let gate := ctx.gates.getD k (0, [])
      let wsDedup := ctx.gatesDedup.getD k []
      let pows := ctx.seedPows.getD r []
      if gate.1 = 0 then
        let w0 := gate.2.getD 0 0
        if uSub.any fun x => decide (x = rOff + w0) then 0 else 1 % M
      else if gate.1 = 1 then
        orTestProdMod ctx.w M pows wsDedup rOff uSub true
      else if gate.1 = 2 then
        let pMod := orTestProdMod ctx.w M pows wsDedup rOff uSub false
        (M + 1 - pMod % M) % M
      else
        if (relList m).any fun pi =>
          uSub.any fun x => decide (x = rOff + nWire + (k * (m1 * m1) + pi.1 * m1 + pi.2)) then
          1 % M
        else 0
    else
      if uSub.any fun x => decide (x = t) then 1 % M else 0
  | some p₀ =>
    if s < nWire then
      if uSub.any fun x => decide (x = t) then 1 % M else 0
    else
      let off := s - nWire
      let k := off / (m1 * m1)
      let rem := off % (m1 * m1)
      let p := rem / m1
      let i := rem % m1
      if decide (p = p₀) && (relList m).any (fun pi => decide (pi.1 = p) && decide (pi.2 = i)) then
        let ws := (ctx.gates.getD k (0, [])).2
        let cnt := ws.countP fun wire => uSub.any fun x => decide (x = rOff + wire)
        let e := min (p₀ ^ i) m
        cnt.choose e % M
      else
        if uSub.any fun x => decide (x = t) then 1 % M else 0

private theorem computableInPolyTime_evalLayerQMod (m : ℕ) (layer : Option ℕ) :
    ComputableInPolyTime
      (fun q : (CompileCtx × ℕ) × (List ℕ × ℕ) => evalLayerQMod m layer q.1.1 q.1.2 q.2.1 q.2.2)
      (encPair (encPair encCompileCtx encNat) (encPair (encList encUnary) encUnary))
      encNat := by
  let encQ := encPair (encPair encCompileCtx encNat) (encPair (encList encUnary) encUnary)
  have hctx : ComputableInPolyTime (fun q : (CompileCtx × ℕ) × (List ℕ × ℕ) => q.1.1)
      encQ encCompileCtx := (ComputableInPolyTime.fst _ _).fst'
  have hM : ComputableInPolyTime (fun q : (CompileCtx × ℕ) × (List ℕ × ℕ) => q.1.2)
      encQ encNat := (ComputableInPolyTime.fst _ _).snd'
  have huSub : ComputableInPolyTime (fun q : (CompileCtx × ℕ) × (List ℕ × ℕ) => q.2.1)
      encQ (encList encUnary) := (ComputableInPolyTime.snd _ _).fst'
  have ht : ComputableInPolyTime (fun q : (CompileCtx × ℕ) × (List ℕ × ℕ) => q.2.2)
      encQ encUnary := (ComputableInPolyTime.snd _ _).snd'
  have hn : ComputableInPolyTime (fun q : (CompileCtx × ℕ) × (List ℕ × ℕ) => q.1.1.n)
      encQ encUnary := by fun_prop
  have hg : ComputableInPolyTime (fun q : (CompileCtx × ℕ) × (List ℕ × ℕ) => q.1.1.g)
      encQ encUnary := by fun_prop
  have hw : ComputableInPolyTime (fun q : (CompileCtx × ℕ) × (List ℕ × ℕ) => q.1.1.w)
      encQ encUnary := by fun_prop
  have hnSlot : ComputableInPolyTime (fun q : (CompileCtx × ℕ) × (List ℕ × ℕ) => q.1.1.nSlot)
      encQ encUnary := by fun_prop
  have hgates : ComputableInPolyTime (fun q : (CompileCtx × ℕ) × (List ℕ × ℕ) => q.1.1.gates)
      encQ (encList (encPair encUnary (encList encUnary))) := by fun_prop
  have hdedup : ComputableInPolyTime (fun q : (CompileCtx × ℕ) × (List ℕ × ℕ) => q.1.1.gatesDedup)
      encQ (encList (encList encUnary)) := by fun_prop
  have hpows : ComputableInPolyTime (fun q : (CompileCtx × ℕ) × (List ℕ × ℕ) => q.1.1.seedPows)
      encQ (encList (encList encBits)) := by fun_prop
  have hnWire : ComputableInPolyTime (fun q : (CompileCtx × ℕ) × (List ℕ × ℕ) => q.1.1.n + q.1.1.g)
      encQ encUnary := ComputableInPolyTime.unary_add.comp (hn.prod hg)
  have hr : ComputableInPolyTime (fun q : (CompileCtx × ℕ) × (List ℕ × ℕ) => q.2.2 / q.1.1.nSlot)
      encQ encUnary := ComputableInPolyTime.unary_div' ht hnSlot
  have hs : ComputableInPolyTime (fun q : (CompileCtx × ℕ) × (List ℕ × ℕ) => q.2.2 % q.1.1.nSlot)
      encQ encUnary := ComputableInPolyTime.unary_mod' ht hnSlot
  have hrOff : ComputableInPolyTime
      (fun q : (CompileCtx × ℕ) × (List ℕ × ℕ) => (q.2.2 / q.1.1.nSlot) * q.1.1.nSlot)
      encQ encUnary := ComputableInPolyTime.unary_mul.comp (hr.prod hnSlot)
  have hmemT : ComputableInPolyTime
      (fun q : (CompileCtx × ℕ) × (List ℕ × ℕ) => q.2.1.any fun x => decide (x = q.2.2))
      encQ encBool :=
    ComputableInPolyTime.anyWithInput (test := fun q x => decide (x = q.2.2)) huSub
      (ComputableInPolyTime.unary_eq'
        (ComputableInPolyTime.snd _ _) (ht.comp (ComputableInPolyTime.fst _ _)))
  have honeM : ComputableInPolyTime (fun q : (CompileCtx × ℕ) × (List ℕ × ℕ) => 1 % q.1.2)
      encQ encNat := ComputableInPolyTime.binary_mod' (ComputableInPolyTime.const 1) hM
  have hbitT := ComputableInPolyTime.ite hmemT honeM (ComputableInPolyTime.const 0)
  cases layer with
  | none =>
    unfold evalLayerQMod
    dsimp only
    have hk := ComputableInPolyTime.unary_sub.comp (hs.prod hn)
    have hgate := ComputableInPolyTime.listGetDWithInput hgates hk (0, [])
    have hwsD := ComputableInPolyTime.listGetDWithInput hdedup hk []
    have hrPows := ComputableInPolyTime.listGetDWithInput hpows hr []
    have hw0 := ComputableInPolyTime.listGetDWithInput hgate.snd'
      (ComputableInPolyTime.const 0) 0
    have hmemW0 := ComputableInPolyTime.anyWithInput
      (test := fun q x => decide (x = q.2.2 / q.1.1.nSlot * q.1.1.nSlot +
        ((q.1.1.gates.getD (q.2.2 % q.1.1.nSlot - q.1.1.n) (0, [])).2.getD 0 0)))
      huSub
      (ComputableInPolyTime.unary_eq'
        (ComputableInPolyTime.snd _ _)
        (ComputableInPolyTime.unary_add.comp
          ((hrOff.comp (ComputableInPolyTime.fst _ _)).prod
            (hw0.comp (ComputableInPolyTime.fst _ _)))))
    have hnot := ComputableInPolyTime.ite hmemW0 (ComputableInPolyTime.const 0) honeM
    have hand := computableInPolyTime_orTestProdMod.comp
      (((hw.prod hM).prod (hrPows.prod hwsD)).prod
        ((hrOff.prod huSub).prod (ComputableInPolyTime.const true)))
    have horProd := computableInPolyTime_orTestProdMod.comp
      (((hw.prod hM).prod (hrPows.prod hwsD)).prod
        ((hrOff.prod huSub).prod (ComputableInPolyTime.const false)))
    have hor := ComputableInPolyTime.binary_mod'
      (ComputableInPolyTime.binary_sub'
        (ComputableInPolyTime.binary_add' hM (ComputableInPolyTime.const 1))
        (ComputableInPolyTime.binary_mod' horProd hM))
      hM
    have hmodGate : ComputableInPolyTime
        (fun q : (CompileCtx × ℕ) × (List ℕ × ℕ) =>
          if (relList m).any fun pi =>
            q.2.1.any fun x =>
              decide (x = (q.2.2 / q.1.1.nSlot) * q.1.1.nSlot + (q.1.1.n + q.1.1.g) +
                ((q.2.2 % q.1.1.nSlot - q.1.1.n) * ((m + 1) * (m + 1)) +
                  pi.1 * (m + 1) + pi.2)) then 1 % q.1.2 else 0)
        encQ encNat := by
      have hanyPi := ComputableInPolyTime.anyWithInput
        (test := fun q pi =>
          q.2.1.any fun x =>
            decide (x = (q.2.2 / q.1.1.nSlot) * q.1.1.nSlot + (q.1.1.n + q.1.1.g) +
              ((q.2.2 % q.1.1.nSlot - q.1.1.n) * ((m + 1) * (m + 1)) +
                pi.1 * (m + 1) + pi.2)))
        (ComputableInPolyTime.const (encIn := encQ)
          (encOut := encList (encPair encUnary encUnary)) (relList m))
        (ComputableInPolyTime.anyWithInput
          (test := fun (p : ((CompileCtx × ℕ) × (List ℕ × ℕ)) × (ℕ × ℕ)) (x : ℕ) =>
            decide (x = (p.1.2.2 / p.1.1.1.nSlot) * p.1.1.1.nSlot + (p.1.1.1.n + p.1.1.1.g) +
              ((p.1.2.2 % p.1.1.1.nSlot - p.1.1.1.n) * ((m + 1) * (m + 1)) +
                p.2.1 * (m + 1) + p.2.2)))
          (huSub.comp (ComputableInPolyTime.fst _ _))
          (ComputableInPolyTime.unary_eq'
            (ComputableInPolyTime.snd (encPair encQ (encPair encUnary encUnary)) encUnary)
            (by
              have hf1 := ComputableInPolyTime.fst
                (encPair encQ (encPair encUnary encUnary)) encUnary
              have h1 := hrOff.comp hf1.fst'
              have h2 := hnWire.comp hf1.fst'
              have h3 := hk.comp hf1.fst'
              have hpi1 := hf1.snd'.fst'
              have hpi2 := hf1.snd'.snd'
              have h4 := ComputableInPolyTime.unary_add.comp (h1.prod h2)
              have h5 := ComputableInPolyTime.unary_mul.comp
                (h3.prod (ComputableInPolyTime.const ((m + 1) * (m + 1))))
              have h6 := ComputableInPolyTime.unary_mul.comp
                (hpi1.prod (ComputableInPolyTime.const (m + 1)))
              exact ComputableInPolyTime.unary_add.comp
                (h4.prod (ComputableInPolyTime.unary_add.comp
                  ((ComputableInPolyTime.unary_add.comp (h5.prod h6)).prod hpi2))))))
      exact ComputableInPolyTime.ite hanyPi honeM (ComputableInPolyTime.const 0)
    have hnone := ComputableInPolyTime.ite (ComputableInPolyTime.unary_lt' hs hn) hbitT
      (ComputableInPolyTime.ite (ComputableInPolyTime.unary_lt' hs hnWire)
        (ComputableInPolyTime.ite
          (ComputableInPolyTime.unary_eq' hgate.fst' (ComputableInPolyTime.const 0)) hnot
          (ComputableInPolyTime.ite
            (ComputableInPolyTime.unary_eq' hgate.fst' (ComputableInPolyTime.const 1)) hand
            (ComputableInPolyTime.ite
              (ComputableInPolyTime.unary_eq' hgate.fst' (ComputableInPolyTime.const 2)) hor
              hmodGate)))
        hbitT)
    exact hnone.of_enc_eq fun q => congrArg encNat <| by
      simp only [Function.comp_def, decide_eq_true_eq]
  | some p₀ =>
    unfold evalLayerQMod
    dsimp only
    have hoff := ComputableInPolyTime.unary_sub.comp (hs.prod hnWire)
    have hk := ComputableInPolyTime.unary_div' hoff
      (ComputableInPolyTime.const ((m + 1) * (m + 1)))
    have hrem := ComputableInPolyTime.unary_mod' hoff
      (ComputableInPolyTime.const ((m + 1) * (m + 1)))
    have hp := ComputableInPolyTime.unary_div' hrem (ComputableInPolyTime.const (m + 1))
    have hi := ComputableInPolyTime.unary_mod' hrem (ComputableInPolyTime.const (m + 1))
    have hcond := ComputableInPolyTime.bool_and'
      (ComputableInPolyTime.unary_eq' hp (ComputableInPolyTime.const p₀))
      (ComputableInPolyTime.anyWithInput
        (test := fun (q : (CompileCtx × ℕ) × (List ℕ × ℕ)) (pi : ℕ × ℕ) =>
          decide (pi.1 = (q.2.2 % q.1.1.nSlot - (q.1.1.n + q.1.1.g)) %
            ((m + 1) * (m + 1)) / (m + 1)) &&
          decide (pi.2 = (q.2.2 % q.1.1.nSlot - (q.1.1.n + q.1.1.g)) %
            ((m + 1) * (m + 1)) % (m + 1)))
        (ComputableInPolyTime.const (encIn := encQ)
          (encOut := encList (encPair encUnary encUnary)) (relList m))
        (ComputableInPolyTime.bool_and'
          (ComputableInPolyTime.unary_eq'
            (ComputableInPolyTime.snd _ _).fst' (hp.comp (ComputableInPolyTime.fst _ _)))
          (ComputableInPolyTime.unary_eq'
            (ComputableInPolyTime.snd _ _).snd' (hi.comp (ComputableInPolyTime.fst _ _)))))
    have hws := (ComputableInPolyTime.listGetDWithInput hgates hk (0, [])).snd'
    have hcnt := ComputableInPolyTime.countPWithInput
      (test := fun (q : (CompileCtx × ℕ) × (List ℕ × ℕ)) (wire : ℕ) =>
        q.2.1.any fun x => decide (x = q.2.2 / q.1.1.nSlot * q.1.1.nSlot + wire))
      hws
      (ComputableInPolyTime.anyWithInput
        (test := fun (p : ((CompileCtx × ℕ) × (List ℕ × ℕ)) × ℕ) (x : ℕ) =>
          decide (x = p.1.2.2 / p.1.1.1.nSlot * p.1.1.1.nSlot + p.2))
        (huSub.comp (ComputableInPolyTime.fst _ _))
        (ComputableInPolyTime.unary_eq'
          (ComputableInPolyTime.snd _ _)
          (ComputableInPolyTime.unary_add.comp
            ((hrOff.comp (ComputableInPolyTime.fst _ _).fst').prod
              ((ComputableInPolyTime.fst _ _).snd')))))
    have he := binary_min_unary_left'
      (ComputableInPolyTime.binary_pow' (ComputableInPolyTime.const p₀) hi)
      (ComputableInPolyTime.const m)
    have hch := ComputableInPolyTime.binary_mod' (ComputableInPolyTime.binary_choose' hcnt he) hM
    have hsome := ComputableInPolyTime.ite (ComputableInPolyTime.unary_lt' hs hnWire) hbitT
      (ComputableInPolyTime.ite hcond hch hbitT)
    exact hsome.of_enc_eq fun q => congrArg encNat <| by
      simp only [Function.comp_def, decide_eq_true_eq]

private def ampGateProdMod (m : ℕ) (layer : Option ℕ) (ctx : CompileCtx)
    (k M : ℕ) (uSub : List ℕ) (S : List ℕ) : ℕ :=
  let M' := posMod M
  let p := layer.getD 2
  S.foldl (fun pacc t =>
    let qMod := evalLayerQMod m layer ctx M' uSub t
    let qPow := powMod M' qMod (p - 1)
    let amp := evalOneSubParityAmpMod k M' qPow
    pacc * amp % M') (1 % M')

/-- Evaluate `amplifiedCount` of a weighted gate list `W` at indicator `1_{uSub}`,
modulo `posMod M`. -/
private def amplifiedCountMod (m : ℕ) (layer : Option ℕ) (ctx : CompileCtx)
    (k M : ℕ) (W : List WGate) (uSub : List ℕ) : ℕ :=
  let M' := posMod M
  W.foldl (fun acc entry =>
    let prod := ampGateProdMod m layer ctx k M' uSub entry.1
    (acc + entry.2 % M' * prod % M') % M') 0

private theorem computableInPolyTime_ampGateProdMod (m : ℕ) (layer : Option ℕ) :
    ComputableInPolyTime
      (fun q : ((CompileCtx × ℕ) × (ℕ × List ℕ)) × List ℕ =>
        ampGateProdMod m layer q.1.1.1 q.1.1.2 q.1.2.1 q.1.2.2 q.2)
      (encPair (encPair (encPair encCompileCtx encUnary) (encPair encNat (encList encUnary)))
        (encList encUnary))
      encNat := by
  let encP := encPair (encPair encCompileCtx encUnary) (encPair encNat (encList encUnary))
  let encQ := encPair encP (encList encUnary)
  let pVal := layer.getD 2
  have hq1 : ComputableInPolyTime
      (fun q : ((CompileCtx × ℕ) × (ℕ × List ℕ)) × List ℕ => q.1) encQ encP :=
    ComputableInPolyTime.fst encP (encList encUnary)
  have hS : ComputableInPolyTime
      (fun q : ((CompileCtx × ℕ) × (ℕ × List ℕ)) × List ℕ => q.2) encQ (encList encUnary) :=
    ComputableInPolyTime.snd encP (encList encUnary)
  have hM' : ComputableInPolyTime
      (fun q : ((CompileCtx × ℕ) × (ℕ × List ℕ)) × List ℕ => posMod q.1.2.1) encQ encNat :=
    computableInPolyTime_posMod hq1.snd'.fst'
  have hstep : ComputableInPolyTime
      (fun s : (((CompileCtx × ℕ) × (ℕ × List ℕ)) × ℕ) × ℕ =>
        let M' := posMod s.1.1.2.1
        s.1.2 * evalOneSubParityAmpMod s.1.1.1.2 M'
          (powMod M' (evalLayerQMod m layer s.1.1.1.1 M' s.1.1.2.2 s.2) (pVal - 1)) % M')
      (encPair (encPair encP encNat) encUnary) encNat := by
    have hs1 := ComputableInPolyTime.fst (encPair encP encNat) encUnary
    have hsp := hs1.fst'
    have hsacc := hs1.snd'
    have hst := ComputableInPolyTime.snd (encPair encP encNat) encUnary
    have hsctx := hsp.fst'.fst'
    have hsk := hsp.fst'.snd'
    have hsM' := computableInPolyTime_posMod hsp.snd'.fst'
    have hsuSub := hsp.snd'.snd'
    have hqMod := (computableInPolyTime_evalLayerQMod m layer).comp
      ((hsctx.prod hsM').prod (hsuSub.prod hst))
    have hqPow := computableInPolyTime_powMod hsM' hqMod (ComputableInPolyTime.const (pVal - 1))
    have hamp := computableInPolyTime_evalOneSubParityAmpMod.comp
      (hsk.prod (hsM'.prod hqPow))
    exact (ComputableInPolyTime.binary_mod'
      (ComputableInPolyTime.binary_mul.comp (hsacc.prod hamp)) hsM').of_enc_eq fun _ => rfl
  have hfold : ComputableInPolyTime
      (fun q : ((CompileCtx × ℕ) × (ℕ × List ℕ)) × List ℕ =>
        q.2.foldl (fun pacc t =>
          let M' := posMod q.1.2.1
          pacc * evalOneSubParityAmpMod q.1.1.2 M'
            (powMod M' (evalLayerQMod m layer q.1.1.1 M' q.1.2.2 t) (pVal - 1)) % M')
          (1 % posMod q.1.2.1))
      encQ encNat := by
    refine ComputableInPolyTime.foldlWith (par := fun q => q.1) (list := fun q => q.2)
      (init := fun q => 1 % posMod q.1.2.1)
      (step := fun p pacc t =>
        let M' := posMod p.2.1
        pacc * evalOneSubParityAmpMod p.1.2 M'
          (powMod M' (evalLayerQMod m layer p.1.1 M' p.2.2 t) (pVal - 1)) % M')
      hq1 hS (ComputableInPolyTime.binary_mod' (ComputableInPolyTime.const 1) hM') hstep
      (B := fun q => (encQ q).length + 1) (PolyBounded.self.add (.const 1)) fun q i _ => ?_
    have hMle : (encNat q.1.2.1).length ≤ (encQ q).length := by
      dsimp only [encQ, encP]; enc_len
    refine le_trans ?_ (Nat.add_le_add_right hMle 1)
    have hle := foldl_mod_posMod_le q.1.2.1
      (fun pacc t => pacc * evalOneSubParityAmpMod q.1.1.2 (posMod q.1.2.1)
        (powMod (posMod q.1.2.1) (evalLayerQMod m layer q.1.1.1 (posMod q.1.2.1) q.1.2.2 t)
          (pVal - 1)))
      (q.2.take i) (Nat.mod_lt 1 (posMod_pos q.1.2.1)).le
    change (Nat.bits _).length ≤ q.1.2.1.bits.length + 1
    simpa only [← Nat.size_eq_bits_len] using size_le_size_add_one_of_le_posMod hle
  exact hfold.of_enc_eq fun q => congrArg encNat <| by unfold ampGateProdMod; rfl

private theorem computableInPolyTime_amplifiedCountMod (m : ℕ) (layer : Option ℕ) :
    ComputableInPolyTime
      (fun q : ((CompileCtx × ℕ) × ℕ) × (List WGate × List ℕ) =>
        amplifiedCountMod m layer q.1.1.1 q.1.1.2 q.1.2 q.2.1 q.2.2)
      (encPair (encPair (encPair encCompileCtx encUnary) encNat)
        (encPair encWList (encList encUnary)))
      encNat := by
  let encQ := encPair (encPair (encPair encCompileCtx encUnary) encNat)
    (encPair encWList (encList encUnary))
  have hW : ComputableInPolyTime
      (fun q : ((CompileCtx × ℕ) × ℕ) × (List WGate × List ℕ) => q.2.1)
      encQ encWList := (ComputableInPolyTime.snd _ _).fst'
  have hstepOut : ComputableInPolyTime
      (fun s : ((((CompileCtx × ℕ) × ℕ) × (List WGate × List ℕ)) × ℕ) × WGate =>
        let q := s.1.1; let acc := s.1.2; let entry := s.2
        let M' := posMod q.1.2
        let prod := ampGateProdMod m layer q.1.1.1 q.1.1.2 M' q.2.2 entry.1
        (acc + entry.2 % M' * prod % M') % M')
      (encPair (encPair encQ encNat) encWGate) encNat := by
    have hs1 := ComputableInPolyTime.fst (encPair encQ encNat) encWGate
    have hsq := hs1.fst'
    have hsacc := hs1.snd'
    have hse := ComputableInPolyTime.snd (encPair encQ encNat) encWGate
    have hsctx := hsq.fst'.fst'.fst'
    have hsk := hsq.fst'.fst'.snd'
    have hsM' := computableInPolyTime_posMod hsq.fst'.snd'
    have hsuSub := hsq.snd'.snd'
    have hprod := (computableInPolyTime_ampGateProdMod m layer).comp
      (((hsctx.prod hsk).prod (hsM'.prod hsuSub)).prod hse.fst')
    have hterm := ComputableInPolyTime.binary_mod'
      (ComputableInPolyTime.binary_mul.comp
        ((ComputableInPolyTime.binary_mod' hse.snd' hsM').prod hprod))
      hsM'
    exact (ComputableInPolyTime.binary_mod'
      (ComputableInPolyTime.binary_add' hsacc hterm) hsM').of_enc_eq fun _ => rfl
  have hfold : ComputableInPolyTime
      (fun q : ((CompileCtx × ℕ) × ℕ) × (List WGate × List ℕ) =>
        q.2.1.foldl (fun acc entry =>
          let M' := posMod q.1.2
          (acc + entry.2 % M' *
            ampGateProdMod m layer q.1.1.1 q.1.1.2 M' q.2.2 entry.1 % M') % M') 0)
      encQ encNat := by
    refine ComputableInPolyTime.foldlWith (par := fun q => q) (list := fun q => q.2.1)
      (init := fun _ => 0)
      (step := fun q acc entry =>
        let M' := posMod q.1.2
        (acc + entry.2 % M' *
          ampGateProdMod m layer q.1.1.1 q.1.1.2 M' q.2.2 entry.1 % M') % M')
      ComputableInPolyTime.id' hW (ComputableInPolyTime.const 0) hstepOut
      (B := fun q => (encQ q).length + 1) (PolyBounded.self.add (.const 1)) fun q i _ => ?_
    have hMle : (encNat q.1.2).length ≤ (encQ q).length := by
      dsimp only [encQ]; enc_len
    refine le_trans ?_ (Nat.add_le_add_right hMle 1)
    have hle := foldl_mod_posMod_le q.1.2
      (fun acc entry => acc + entry.2 % posMod q.1.2 *
        ampGateProdMod m layer q.1.1.1 q.1.1.2 (posMod q.1.2) q.2.2 entry.1 % posMod q.1.2)
      (q.2.1.take i) (Nat.zero_le _)
    change (Nat.bits _).length ≤ q.1.2.bits.length + 1
    simpa only [← Nat.size_eq_bits_len] using size_le_size_add_one_of_le_posMod hle
  exact hfold.of_enc_eq fun q => congrArg encNat <| by unfold amplifiedCountMod; rfl

/-! #### One executable collapse step and tower collapse -/

private def mobiusCoeffMod (m : ℕ) (layer : Option ℕ) (ctx : CompileCtx)
    (k M U : ℕ) (W : List WGate) (S : List ℕ) : ℕ :=
  let M' := posMod M
  (allSubsetsCapped S U).foldl (fun acc uSub =>
    let val := amplifiedCountMod m layer ctx k M' W uSub
    let term := if (S.length - uSub.length) % 2 = 0 then val % M' else (M' - val % M') % M'
    (acc + term) % M') 0

private theorem computableInPolyTime_mobiusCoeffMod (m : ℕ) (layer : Option ℕ) :
    ComputableInPolyTime
      (fun q : (((CompileCtx × ℕ) × (ℕ × ℕ)) × List WGate) × List ℕ =>
        mobiusCoeffMod m layer q.1.1.1.1 q.1.1.1.2 q.1.1.2.1 q.1.1.2.2 q.1.2 q.2)
      (encPair (encPair (encPair (encPair encCompileCtx encUnary) (encPair encNat encUnary))
        encWList) (encList encUnary))
      encNat := by
  let encL := encPair (encPair (encPair encCompileCtx encUnary) (encPair encNat encUnary)) encWList
  let encQ := encPair encL (encList encUnary)
  have hq1 := ComputableInPolyTime.fst encL (encList encUnary)
  have hctx := hq1.fst'.fst'.fst'
  have hk := hq1.fst'.fst'.snd'
  have hM' := computableInPolyTime_posMod hq1.fst'.snd'.fst'
  have hU := hq1.fst'.snd'.snd'
  have hW := hq1.snd'
  have hS := ComputableInPolyTime.snd encL (encList encUnary)
  have hsubs := computableInPolyTime_allSubsetsCapped.comp (hS.prod hU)
  have hstep : ComputableInPolyTime
      (fun p : (((((CompileCtx × ℕ) × (ℕ × ℕ)) × List WGate) × List ℕ) × ℕ) × List ℕ =>
        let q := p.1.1; let acc := p.1.2; let uSub := p.2
        let M' := posMod q.1.1.2.1
        let val := amplifiedCountMod m layer q.1.1.1.1 q.1.1.1.2 M' q.1.2 uSub
        let term := if (q.2.length - uSub.length) % 2 = 0 then val % M' else (M' - val % M') % M'
        (acc + term) % M')
      (encPair (encPair encQ encNat) (encList encUnary)) encNat := by
    have hp1 := ComputableInPolyTime.fst (encPair encQ encNat) (encList encUnary)
    have hpq := hp1.fst'
    have hacc := hp1.snd'
    have huSub := ComputableInPolyTime.snd (encPair encQ encNat) (encList encUnary)
    have hpM' := hM'.comp hpq
    have hval := (computableInPolyTime_amplifiedCountMod m layer).comp
      ((((hctx.comp hpq).prod (hk.comp hpq)).prod hpM').prod ((hW.comp hpq).prod huSub))
    have hvalM := ComputableInPolyTime.binary_mod' hval hpM'
    have hnegM := ComputableInPolyTime.binary_mod'
      (ComputableInPolyTime.binary_sub' hpM' hvalM) hpM'
    have hpar : ComputableInPolyTime
        (fun p : (((((CompileCtx × ℕ) × (ℕ × ℕ)) × List WGate) × List ℕ) × ℕ) × List ℕ =>
          decide ((p.1.1.2.length - p.2.length) % 2 = 0))
        (encPair (encPair encQ encNat) (encList encUnary)) encBool := by
      have hlenS := (ComputableInPolyTime.length_list encUnary).comp (hS.comp hpq)
      have hlenU := (ComputableInPolyTime.length_list encUnary).comp huSub
      have hsub := ComputableInPolyTime.unary_sub.comp (hlenS.prod hlenU)
      exact ComputableInPolyTime.unary_eq'
        (ComputableInPolyTime.unary_mod' hsub (ComputableInPolyTime.const 2))
        (ComputableInPolyTime.const 0)
    have hterm := ComputableInPolyTime.ite_decide hpar hvalM hnegM
    exact (ComputableInPolyTime.binary_mod'
      (ComputableInPolyTime.binary_add' hacc hterm) hpM').of_enc_eq fun _ => rfl
  have hfold : ComputableInPolyTime
      (fun q : (((CompileCtx × ℕ) × (ℕ × ℕ)) × List WGate) × List ℕ =>
        (allSubsetsCapped q.2 q.1.1.2.2).foldl (fun acc uSub =>
          let M' := posMod q.1.1.2.1
          let val := amplifiedCountMod m layer q.1.1.1.1 q.1.1.1.2 M' q.1.2 uSub
          let term := if (q.2.length - uSub.length) % 2 = 0 then val % M' else (M' - val % M') % M'
          (acc + term) % M') 0)
      encQ encNat := by
    refine ComputableInPolyTime.foldlWith (par := fun q => q)
      (list := fun q => allSubsetsCapped q.2 q.1.1.2.2) (init := fun _ => 0)
      (step := fun q acc uSub =>
        let M' := posMod q.1.1.2.1
        let val := amplifiedCountMod m layer q.1.1.1.1 q.1.1.1.2 M' q.1.2 uSub
        let term := if (q.2.length - uSub.length) % 2 = 0 then val % M' else (M' - val % M') % M'
        (acc + term) % M')
      ComputableInPolyTime.id' hsubs (ComputableInPolyTime.const 0) hstep
      (B := fun q => (encQ q).length + 1) (PolyBounded.self.add (.const 1)) fun q i _ => ?_
    have hMle : (encNat q.1.1.2.1).length ≤ (encQ q).length := by
      dsimp only [encQ, encL]; enc_len
    refine le_trans ?_ (Nat.add_le_add_right hMle 1)
    have hres := foldl_mod_posMod_le q.1.1.2.1
      (fun acc uSub =>
        let M' := posMod q.1.1.2.1
        let val := amplifiedCountMod m layer q.1.1.1.1 q.1.1.1.2 M' q.1.2 uSub
        let term := if (q.2.length - uSub.length) % 2 = 0 then val % M' else (M' - val % M') % M'
        acc + term)
      ((allSubsetsCapped q.2 q.1.1.2.2).take i) (Nat.zero_le _)
    change (Nat.bits _).length ≤ q.1.1.2.1.bits.length + 1
    simpa only [← Nat.size_eq_bits_len] using size_le_size_add_one_of_le_posMod hres
  exact hfold.of_enc_eq fun q => congrArg encNat <| by unfold mobiusCoeffMod; rfl

/-- One executable collapse step on a weighted gate list `W`, with unary budget `U` and current
unary parameter `B`. Drops zero-multiplicity entries so `fanIn` matches `SymAnd.collapseStep`. -/
private def collapseStepExec (m : ℕ) (layer : Option ℕ) (ctx : CompileCtx) (U B : ℕ)
    (W : List WGate) : List WGate :=
  let p := layer.getD 2
  let k := B + 1
  let M := p ^ k
  let fanInCur := (W.map fun e => e.1.length).foldl max 0
  let D := min (fanInCur * ((2 * k - 1) * ((p - 1) * B))) U
  let cand := subsetsUpToCapped ctx.nTotal D U
  (cand.map fun S => (S, mobiusCoeffMod m layer ctx k M U W S)).filter fun e => decide (0 < e.2)

private def collapseStepCand (layer : Option ℕ)
    (q : (CompileCtx × (ℕ × ℕ)) × List WGate) : List (List ℕ) :=
  let p := layer.getD 2
  let k := q.1.2.2 + 1
  let fanInCur := (q.2.map fun e => e.1.length).foldl max 0
  let D := min (fanInCur * ((2 * k - 1) * ((p - 1) * q.1.2.2))) q.1.2.1
  subsetsUpToCapped q.1.1.nTotal D q.1.2.1

private def collapseStepCoeff (m : ℕ) (layer : Option ℕ)
    (q : (CompileCtx × (ℕ × ℕ)) × List WGate) (S : List ℕ) : ℕ :=
  mobiusCoeffMod m layer q.1.1 (q.1.2.2 + 1) (layer.getD 2 ^ (q.1.2.2 + 1)) q.1.2.1 q.2 S

private theorem computableInPolyTime_collapseStepExec_cand (layer : Option ℕ) :
    ComputableInPolyTime (collapseStepCand layer)
      (encPair (encPair encCompileCtx (encPair encUnary encUnary)) encWList)
      (encList (encList encUnary)) := by
  let encQ := encPair (encPair encCompileCtx (encPair encUnary encUnary)) encWList
  let p := layer.getD 2
  have hctx : ComputableInPolyTime (fun q : (CompileCtx × (ℕ × ℕ)) × List WGate => q.1.1)
      encQ encCompileCtx := (ComputableInPolyTime.fst _ _).fst'
  have hU : ComputableInPolyTime (fun q : (CompileCtx × (ℕ × ℕ)) × List WGate => q.1.2.1)
      encQ encUnary := (ComputableInPolyTime.fst _ _).snd'.fst'
  have hB : ComputableInPolyTime (fun q : (CompileCtx × (ℕ × ℕ)) × List WGate => q.1.2.2)
      encQ encUnary := (ComputableInPolyTime.fst _ _).snd'.snd'
  have hW : ComputableInPolyTime (fun q : (CompileCtx × (ℕ × ℕ)) × List WGate => q.2)
      encQ encWList := ComputableInPolyTime.snd _ _
  have hk : ComputableInPolyTime (fun q : (CompileCtx × (ℕ × ℕ)) × List WGate => q.1.2.2 + 1)
      encQ encUnary := ComputableInPolyTime.unary_add.comp (hB.prod (ComputableInPolyTime.const 1))
  have hfanIn : ComputableInPolyTime
      (fun q : (CompileCtx × (ℕ × ℕ)) × List WGate => (q.2.map fun e => e.1.length).foldl max 0)
      encQ encUnary :=
    (ComputableInPolyTime.unary_foldl_max 0).comp
      (ComputableInPolyTime.mapWithInput hW
        ((ComputableInPolyTime.length_list encUnary).comp (ComputableInPolyTime.snd _ _).fst'))
  have hD : ComputableInPolyTime
      (fun q : (CompileCtx × (ℕ × ℕ)) × List WGate =>
        min ((q.2.map fun e => e.1.length).foldl max 0 *
          ((2 * (q.1.2.2 + 1) - 1) * ((p - 1) * q.1.2.2))) q.1.2.1)
      encQ encUnary :=
    ComputableInPolyTime.unary_min'
      (ComputableInPolyTime.unary_mul.comp
        (hfanIn.prod
          (ComputableInPolyTime.unary_mul.comp
            ((ComputableInPolyTime.unary_sub.comp
              ((ComputableInPolyTime.unary_mul.comp
                ((ComputableInPolyTime.const 2).prod hk)).prod
                (ComputableInPolyTime.const 1))).prod
              (ComputableInPolyTime.unary_mul.comp
                ((ComputableInPolyTime.const (p - 1)).prod hB))))))
      hU
  have hprojTotal : ComputableInPolyTime (fun x : CompileCtx => x.nTotal) encCompileCtx encUnary :=
    by fun_prop
  have hnTotal : ComputableInPolyTime (fun q : (CompileCtx × (ℕ × ℕ)) × List WGate => q.1.1.nTotal)
      encQ encUnary := hprojTotal.comp hctx
  exact (computableInPolyTime_subsetsUpToCapped.comp (hnTotal.prod (hD.prod hU))).of_enc_eq fun q =>
    congrArg (encList (encList encUnary))
      (by unfold collapseStepCand; simp only [Function.comp_apply, p])

private theorem computableInPolyTime_collapseStepExec_coeff (m : ℕ) (layer : Option ℕ) :
    ComputableInPolyTime
      (fun r : ((CompileCtx × (ℕ × ℕ)) × List WGate) × List ℕ =>
        collapseStepCoeff m layer r.1 r.2)
      (encPair (encPair (encPair encCompileCtx (encPair encUnary encUnary)) encWList)
        (encList encUnary))
      encNat := by
  let encQ := encPair (encPair encCompileCtx (encPair encUnary encUnary)) encWList
  let encR := encPair encQ (encList encUnary)
  let p := layer.getD 2
  have hq : ComputableInPolyTime (fun r : ((CompileCtx × (ℕ × ℕ)) × List WGate) × List ℕ => r.1)
      encR encQ := ComputableInPolyTime.fst encQ (encList encUnary)
  have hS : ComputableInPolyTime (fun r : ((CompileCtx × (ℕ × ℕ)) × List WGate) × List ℕ => r.2)
      encR (encList encUnary) := ComputableInPolyTime.snd encQ (encList encUnary)
  have hctx := hq.fst'.fst'
  have hU := hq.fst'.snd'.fst'
  have hB := hq.fst'.snd'.snd'
  have hW := hq.snd'
  have hk := ComputableInPolyTime.unary_add.comp (hB.prod (ComputableInPolyTime.const 1))
  have hM := ComputableInPolyTime.binary_pow' (ComputableInPolyTime.const p) hk
  exact ((computableInPolyTime_mobiusCoeffMod m layer).comp
    ((((hctx.prod hk).prod (hM.prod hU)).prod hW).prod hS)).of_enc_eq fun r =>
      congrArg encNat (by unfold collapseStepCoeff; simp only [Function.comp_apply, p])

private theorem collapseStepExec_eq (m : ℕ) (layer : Option ℕ)
    (q : (CompileCtx × (ℕ × ℕ)) × List WGate) :
    collapseStepExec m layer q.1.1 q.1.2.1 q.1.2.2 q.2 =
      ((collapseStepCand layer q).map fun S => (S, collapseStepCoeff m layer q S)).filter
        fun e => decide (0 < e.2) := rfl

private theorem computableInPolyTime_collapseStepExec (m : ℕ) (layer : Option ℕ) :
    ComputableInPolyTime
      (fun q : (CompileCtx × (ℕ × ℕ)) × List WGate =>
        collapseStepExec m layer q.1.1 q.1.2.1 q.1.2.2 q.2)
      (encPair (encPair encCompileCtx (encPair encUnary encUnary)) encWList) encWList := by
  let encQ := encPair (encPair encCompileCtx (encPair encUnary encUnary)) encWList
  have hcand := computableInPolyTime_collapseStepExec_cand layer
  have hcoeff := computableInPolyTime_collapseStepExec_coeff m layer
  have hmapped : ComputableInPolyTime
      (fun q : (CompileCtx × (ℕ × ℕ)) × List WGate =>
        (collapseStepCand layer q).map fun S => (S, collapseStepCoeff m layer q S))
      encQ encWList :=
    ComputableInPolyTime.mapWithInput
      (f := fun (q : (CompileCtx × (ℕ × ℕ)) × List WGate) (S : List ℕ) =>
        (S, collapseStepCoeff m layer q S))
      hcand ((ComputableInPolyTime.snd encQ (encList encUnary)).prod hcoeff)
  have hpos : ComputableInPolyTime (fun e : WGate => decide (0 < e.2)) encWGate encBool :=
    ComputableInPolyTime.binary_lt' (ComputableInPolyTime.const 0)
      (ComputableInPolyTime.snd (encList encUnary) encNat)
  exact ((ComputableInPolyTime.filter hpos).comp hmapped).of_enc_eq fun q =>
    congrArg encWList <| by
      rw [collapseStepExec_eq, Function.comp_apply]

/-- Executable collapse of a fixed list of layers `Ls`, threading `B ↦ min (5 * B ^ 5) U` in unary
and recording the list of collapse moduli `M_j = p_j ^ (B_j + 1)` in binary. -/
private def collapseRunExec (m : ℕ) (ctx : CompileCtx) (U : ℕ) :
    List (Option ℕ) → ℕ → List WGate → List WGate × List ℕ
  | [], _, W => (W, [])
  | layer :: rest, B, W =>
    let p := layer.getD 2
    let M := p ^ (B + 1)
    let W' := collapseStepExec m layer ctx U B W
    let B' := min (5 * B ^ 5) U
    let res := collapseRunExec m ctx U rest B' W'
    (res.1, M :: res.2)

private theorem computableInPolyTime_collapseRunExec (m : ℕ) (Ls : List (Option ℕ)) :
    ComputableInPolyTime
      (fun q : (CompileCtx × (ℕ × ℕ)) × List WGate =>
        collapseRunExec m q.1.1 q.1.2.1 Ls q.1.2.2 q.2)
      (encPair (encPair encCompileCtx (encPair encUnary encUnary)) encWList)
      (encPair encWList (encList encNat)) := by
  induction Ls with
  | nil =>
    exact (ComputableInPolyTime.snd _ _).prod (ComputableInPolyTime.const [])
  | cons layer rest ih =>
    let encQ := encPair (encPair encCompileCtx (encPair encUnary encUnary)) encWList
    have hctx : ComputableInPolyTime (fun q : (CompileCtx × (ℕ × ℕ)) × List WGate => q.1.1)
        encQ encCompileCtx := (ComputableInPolyTime.fst _ _).fst'
    have hU : ComputableInPolyTime (fun q : (CompileCtx × (ℕ × ℕ)) × List WGate => q.1.2.1)
        encQ encUnary := (ComputableInPolyTime.fst _ _).snd'.fst'
    have hB : ComputableInPolyTime (fun q : (CompileCtx × (ℕ × ℕ)) × List WGate => q.1.2.2)
        encQ encUnary := (ComputableInPolyTime.fst _ _).snd'.snd'
    have hM : ComputableInPolyTime
        (fun q : (CompileCtx × (ℕ × ℕ)) × List WGate => (layer.getD 2) ^ (q.1.2.2 + 1))
        encQ encNat :=
      ComputableInPolyTime.binary_pow' (ComputableInPolyTime.const (layer.getD 2))
        (ComputableInPolyTime.unary_add.comp (hB.prod (ComputableInPolyTime.const 1)))
    have hW' := computableInPolyTime_collapseStepExec m layer
    have hB' : ComputableInPolyTime
        (fun q : (CompileCtx × (ℕ × ℕ)) × List WGate => min (5 * q.1.2.2 ^ 5) q.1.2.1)
        encQ encUnary := by
      have h5 : ComputableInPolyTime
          (fun q : (CompileCtx × (ℕ × ℕ)) × List WGate => 5 * q.1.2.2 ^ 5) encQ encNat :=
        ComputableInPolyTime.binary_mul.comp
          ((ComputableInPolyTime.const 5).prod
            (ComputableInPolyTime.binary_pow'
              (ComputableInPolyTime.unary_to_binary.comp hB) (ComputableInPolyTime.const 5)))
      exact binary_min_unary_left' h5 hU
    have hrec := ih.comp ((hctx.prod (hU.prod hB')).prod hW')
    exact hrec.fst'.prod (ComputableInPolyTime.cons' hM hrec.snd')

/-- Restrict a weighted gate list `W` on `T` to input slots (`t % nSlot < n`), convert each
surviving gate to its `n`-bit characteristic mask, and expand multiplicities (capped at `U`). -/
private def restrictAndExpand (ctx : CompileCtx) (U : ℕ) (W : List WGate) : SymAndInstance :=
  let kept := W.filter fun e => e.1.all fun t => decide (t % ctx.nSlot < ctx.n)
  let gates := kept.flatMap fun e =>
    let mask := (List.range ctx.n).map fun i => e.1.any fun t => decide (t % ctx.nSlot = i)
    List.replicate (min e.2 U) mask
  ⟨ctx.n, gates⟩

private theorem computableInPolyTime_restrictAndExpand :
    ComputableInPolyTime
      (fun q : (CompileCtx × ℕ) × List WGate => restrictAndExpand q.1.1 q.1.2 q.2)
      (encPair (encPair encCompileCtx encUnary) encWList) encSymAndInstance := by
  let encQ := encPair (encPair encCompileCtx encUnary) encWList
  have hctx := (ComputableInPolyTime.fst (encPair encCompileCtx encUnary) encWList).fst'
  have hU := (ComputableInPolyTime.fst (encPair encCompileCtx encUnary) encWList).snd'
  have hW := ComputableInPolyTime.snd (encPair encCompileCtx encUnary) encWList
  have hn : ComputableInPolyTime (fun q : (CompileCtx × ℕ) × List WGate => q.1.1.n)
      encQ encUnary := by fun_prop
  have hnSlot : ComputableInPolyTime (fun q : (CompileCtx × ℕ) × List WGate => q.1.1.nSlot)
      encQ encUnary := by fun_prop
  have hkeepPred : ComputableInPolyTime
      (fun p : ((CompileCtx × ℕ) × List WGate) × WGate =>
        p.2.1.all fun t => decide (t % p.1.1.1.nSlot < p.1.1.1.n))
      (encPair encQ encWGate) encBool :=
    ComputableInPolyTime.allWith
      (ComputableInPolyTime.unary_lt'
        (ComputableInPolyTime.unary_mod'
          (ComputableInPolyTime.snd encQ encUnary)
          (hnSlot.comp (ComputableInPolyTime.fst encQ encUnary)))
        (hn.comp (ComputableInPolyTime.fst encQ encUnary)))
      (ComputableInPolyTime.fst encQ encWGate)
      (ComputableInPolyTime.snd encQ encWGate).fst'
  have hkept := ComputableInPolyTime.filterWithInput
    (test := fun (q : (CompileCtx × ℕ) × List WGate) (e : WGate) =>
      e.1.all fun t => decide (t % q.1.1.nSlot < q.1.1.n)) hW hkeepPred
  have hrep : ComputableInPolyTime
      (fun p : ((CompileCtx × ℕ) × List WGate) × WGate =>
        let mask := (List.range p.1.1.1.n).map fun i =>
          p.2.1.any fun t => decide (t % p.1.1.1.nSlot = i)
        List.replicate (min p.2.2 p.1.1.2) mask)
      (encPair encQ encWGate) (encList encBits) := by
    have hmaskList : ComputableInPolyTime
        (fun p : ((CompileCtx × ℕ) × List WGate) × WGate =>
          (List.range p.1.1.1.n).map fun i =>
            p.2.1.any fun t => decide (t % p.1.1.1.nSlot = i))
        (encPair encQ encWGate) (encList encBool) :=
      ComputableInPolyTime.mapWithInput
        (f := fun (p : ((CompileCtx × ℕ) × List WGate) × WGate) (i : ℕ) =>
          p.2.1.any fun t => decide (t % p.1.1.1.nSlot = i))
        (ComputableInPolyTime.range.comp (hn.comp (ComputableInPolyTime.fst encQ encWGate)))
        (ComputableInPolyTime.anyWithInput
          (test := fun (p : (((CompileCtx × ℕ) × List WGate) × WGate) × ℕ) (t : ℕ) =>
            decide (t % p.1.1.1.1.nSlot = p.2))
          ((ComputableInPolyTime.fst (encPair encQ encWGate) encUnary).snd'.fst')
          (ComputableInPolyTime.unary_eq'
            (ComputableInPolyTime.unary_mod'
              (ComputableInPolyTime.snd (encPair (encPair encQ encWGate) encUnary) encUnary)
              (hnSlot.comp
                (ComputableInPolyTime.fst (encPair (encPair encQ encWGate) encUnary)
                  encUnary).fst'.fst'))
            (ComputableInPolyTime.fst (encPair (encPair encQ encWGate) encUnary) encUnary).snd'))
    have hmaskBits := ComputableInPolyTime.listToBits.comp hmaskList
    have hcnt := binary_min_unary_left'
      (ComputableInPolyTime.snd encQ encWGate).snd'
      (hU.comp (ComputableInPolyTime.fst encQ encWGate))
    exact ComputableInPolyTime.replicate hcnt hmaskBits
  have hgates := ComputableInPolyTime.flatMapWithInput
    (f := fun (q : (CompileCtx × ℕ) × List WGate) (e : WGate) =>
      List.replicate (min e.2 q.1.2)
        ((List.range q.1.1.n).map fun i => e.1.any fun t => decide (t % q.1.1.nSlot = i)))
    hkept hrep
  exact (encSymAndInstance_mk_polyTime hn hgates).of_enc_eq fun q =>
    congrArg encSymAndInstance <| by unfold restrictAndExpand; rfl

/-- Budget-capped polynomial-time compiler for fixed tower depth `d` and modulus `m`. -/
private def compileWithBudget (d m : ℕ)
    (p : (Σ n, Circuit Unbounded.extSignature n 1) × ℕ) : SymAndInstance × SymOutParam :=
  let c := p.1
  let U := p.2
  let ctx := buildCtx m c
  let ℓ := Nat.log 2 (ctx.n + ctx.g) + 1
  let B₀ := min (3 * ((m + 1) ^ 2 + ℓ + 1)) U
  let outWire := min (c.2.code.2.getD 0 0) (ctx.n + ctx.g)
  let W₀ : List WGate := (List.range ctx.nSeed).map fun r => ([r * ctx.nSlot + outWire], 1)
  let res := collapseRunExec m ctx U (layerSpec d m) B₀ W₀
  (restrictAndExpand ctx U res.1, ⟨2 ^ ctx.w, res.2⟩)

private theorem computableInPolyTime_compileWithBudget (d m : ℕ) :
    ComputableInPolyTime (compileWithBudget d m)
      (encPair (Unbounded.encExtCircuit 1) encUnary)
      (encPair encSymAndInstance encSymOutParam) := by
  let encP := encPair (Unbounded.encExtCircuit 1) encUnary
  have hc := ComputableInPolyTime.fst (Unbounded.encExtCircuit 1) encUnary
  have hU := ComputableInPolyTime.snd (Unbounded.encExtCircuit 1) encUnary
  have hctx := (computableInPolyTime_buildCtx m).comp hc
  have hprojN : ComputableInPolyTime (fun x : CompileCtx => x.n) encCompileCtx encUnary := by
    fun_prop
  have hprojG : ComputableInPolyTime (fun x : CompileCtx => x.g) encCompileCtx encUnary := by
    fun_prop
  have hprojW : ComputableInPolyTime (fun x : CompileCtx => x.w) encCompileCtx encUnary := by
    fun_prop
  have hprojSeed : ComputableInPolyTime (fun x : CompileCtx => x.nSeed) encCompileCtx encUnary := by
    fun_prop
  have hprojSlot : ComputableInPolyTime (fun x : CompileCtx => x.nSlot) encCompileCtx encUnary := by
    fun_prop
  have hn := hprojN.comp hctx
  have hg := hprojG.comp hctx
  have hw := hprojW.comp hctx
  have hnSeed := hprojSeed.comp hctx
  have hnSlot := hprojSlot.comp hctx
  have hnWire := ComputableInPolyTime.unary_add.comp (hn.prod hg)
  have hℓ := ComputableInPolyTime.unary_add.comp
    ((ComputableInPolyTime.unary_log_two.comp hnWire).prod (ComputableInPolyTime.const 1))
  have hB₀ : ComputableInPolyTime
      (fun p : (Σ n, Circuit Unbounded.extSignature n 1) × ℕ =>
        min (3 * ((m + 1) ^ 2 +
          (Nat.log 2 ((buildCtx m p.1).n + (buildCtx m p.1).g) + 1) + 1)) p.2)
      encP encUnary :=
    ComputableInPolyTime.unary_min'
      (ComputableInPolyTime.unary_mul.comp
        ((ComputableInPolyTime.const 3).prod
          (ComputableInPolyTime.unary_add.comp
            ((ComputableInPolyTime.unary_add.comp
              ((ComputableInPolyTime.const ((m + 1) ^ 2)).prod hℓ)).prod
              (ComputableInPolyTime.const 1)))))
      hU
  have houts :=
    ((Circuit.computableInPolyTime_arity_code (σ := Unbounded.extSignature)
      Unbounded.encExtOp 1).comp hc).snd'.snd'
  have houtWire := binary_min_unary_left'
    (ComputableInPolyTime.listGetDWithInput houts (ComputableInPolyTime.const 0) 0) hnWire
  have hW₀ : ComputableInPolyTime
      (fun p : (Σ n, Circuit Unbounded.extSignature n 1) × ℕ =>
        (List.range (buildCtx m p.1).nSeed).map fun r =>
          ([r * (buildCtx m p.1).nSlot +
            min (p.1.2.code.2.getD 0 0) ((buildCtx m p.1).n + (buildCtx m p.1).g)], 1))
      encP encWList :=
    ComputableInPolyTime.mapWithInput
      (f := fun p r =>
        ([r * (buildCtx m p.1).nSlot +
          min (p.1.2.code.2.getD 0 0) ((buildCtx m p.1).n + (buildCtx m p.1).g)], 1))
      (ComputableInPolyTime.range.comp hnSeed)
      ((ComputableInPolyTime.cons'
          (ComputableInPolyTime.unary_add.comp
            ((ComputableInPolyTime.unary_mul.comp
              ((ComputableInPolyTime.snd _ _).prod
                (hnSlot.comp (ComputableInPolyTime.fst _ _)))).prod
              (houtWire.comp (ComputableInPolyTime.fst _ _))))
          (ComputableInPolyTime.const [])).prod
        (ComputableInPolyTime.const 1))
  have hres := (computableInPolyTime_collapseRunExec m (layerSpec d m)).comp
    ((hctx.prod (hU.prod hB₀)).prod hW₀)
  have hinst := computableInPolyTime_restrictAndExpand.comp ((hctx.prod hU).prod hres.fst')
  have hthresh := ComputableInPolyTime.binary_two_pow.comp hw
  have hout := encSymOutParam_mk_polyTime hthresh hres.snd'
  exact (hinst.prod hout).of_enc_eq fun p =>
    congrArg (encPair encSymAndInstance encSymOutParam) <| by unfold compileWithBudget; rfl

/-- The binary budget exponent `E_budget = (B₀ + 2) * (2 * B₀) ^ (5 ^ L)` whose unary power
`2 ^ E_budget` makes every cap in `compileWithBudget d m` inactive. -/
private def budgetExp (d m : ℕ) (c : Σ n, Circuit Unbounded.extSignature n 1) : ℕ :=
  let ℓ := Nat.log 2 (c.1 + c.2.size) + 1
  let B₀ := 3 * ((m + 1) ^ 2 + ℓ + 1)
  (B₀ + 2) * (2 * B₀) ^ 5 ^ (d * (m + 2))

private theorem computableInPolyTime_budgetExp (d m : ℕ) :
    ComputableInPolyTime (budgetExp d m) (Unbounded.encExtCircuit 1) encNat := by
  have har := Circuit.computableInPolyTime_arity_code (σ := Unbounded.extSignature)
    Unbounded.encExtOp 1
  have hn := har.fst'
  have hg : ComputableInPolyTime (fun c : Σ n, Circuit Unbounded.extSignature n 1 => c.2.size)
      (Unbounded.encExtCircuit 1) encUnary :=
    ((ComputableInPolyTime.length_list _).comp har.snd'.fst').of_enc_eq fun c =>
      congrArg encUnary (Circuit.length_code_fst c.2).symm
  have hℓ := ComputableInPolyTime.unary_add.comp
    ((ComputableInPolyTime.unary_log_two.comp
      (ComputableInPolyTime.unary_add.comp (hn.prod hg))).prod
      (ComputableInPolyTime.const 1))
  have hB₀ : ComputableInPolyTime
      (fun c : Σ n, Circuit Unbounded.extSignature n 1 =>
        3 * ((m + 1) ^ 2 + (Nat.log 2 (c.1 + c.2.size) + 1) + 1))
      (Unbounded.encExtCircuit 1) encUnary := by
    have := hℓ; fun_prop
  have hB₀B := ComputableInPolyTime.unary_to_binary.comp hB₀
  have h2B₀ := ComputableInPolyTime.binary_mul.comp ((ComputableInPolyTime.const 2).prod hB₀B)
  have hpow := ComputableInPolyTime.binary_pow' h2B₀
    (ComputableInPolyTime.const (5 ^ (d * (m + 2))))
  exact ComputableInPolyTime.binary_mul.comp
    ((ComputableInPolyTime.binary_add' hB₀B (ComputableInPolyTime.const 2)).prod hpow)

/-! ### 5. Mathematical equivalence with `ACC0ToSymAnd.compile` -/

section Equivalence

variable {n g m ℓ : ℕ}

private def slotOffset (s : Slot n g m) : ℕ :=
  match s with
  | .inl (.input i) => i.val
  | .inl (.gate k) => n + k.val
  | .inr (k, pi) => n + g + (k.val * ((m + 1) * (m + 1)) + pi.1.val * (m + 1) + pi.2.val)

private theorem slotOffset_lt (s : Slot n g m) :
    slotOffset s < n + g + g * ((m + 1) * (m + 1)) := by
  rcases s with (i | k) | ⟨k, p, i⟩
  · have := i.isLt; simp only [slotOffset]; omega
  · have := k.isLt; simp only [slotOffset]; omega
  · have hk := k.isLt; have hp := p.isLt; have hi := i.isLt
    simp only [slotOffset]; nlinarith

/-- Slot bijection between `Seed ℓ × Slot n g m` and
`Fin (2 ^ (2 * ℓ + 2) * (n + g + g * (m + 1) ^ 2))`. -/
private noncomputable def slotToNat (t : Seed ℓ × Slot n g m) : ℕ :=
  let w := 2 * ℓ + 2
  let hw : w ≠ 0 := by omega
  let r := (BinaryField.equivFin hw t.1).val
  let nSlot := n + g + g * ((m + 1) * (m + 1))
  r * nSlot + slotOffset t.2

private theorem slotToNat_lt (t : Seed ℓ × Slot n g m) :
    slotToNat t < 2 ^ (2 * ℓ + 2) * (n + g + g * ((m + 1) * (m + 1))) := by
  set nSlot := n + g + g * ((m + 1) * (m + 1))
  have hr := (BinaryField.equivFin (show 2 * ℓ + 2 ≠ 0 by omega) t.1).isLt
  have hs := slotOffset_lt t.2
  dsimp only [slotToNat]
  calc _ < (BinaryField.equivFin (show 2 * ℓ + 2 ≠ 0 by omega) t.1).val * nSlot + nSlot :=
        Nat.add_lt_add_left hs _
    _ = ((BinaryField.equivFin (show 2 * ℓ + 2 ≠ 0 by omega) t.1).val + 1) * nSlot := by ring
    _ ≤ 2 ^ (2 * ℓ + 2) * nSlot := Nat.mul_le_mul_right nSlot hr

private theorem slotToNat_div (t : Seed ℓ × Slot n g m) :
    slotToNat t / (n + g + g * ((m + 1) * (m + 1))) =
      (BinaryField.equivFin (show 2 * ℓ + 2 ≠ 0 by omega) t.1).val := by
  set nSlot := n + g + g * ((m + 1) * (m + 1))
  have hs := slotOffset_lt t.2
  have hnPos : 0 < nSlot := (Nat.zero_le _).trans_lt hs
  dsimp only [slotToNat]
  rw [Nat.mul_comm _ nSlot, Nat.mul_add_div hnPos, Nat.div_eq_of_lt hs, Nat.add_zero]

private theorem slotToNat_mod (t : Seed ℓ × Slot n g m) :
    slotToNat t % (n + g + g * ((m + 1) * (m + 1))) =
      match t.2 with
      | .inl (.input i) => i.val
      | .inl (.gate k) => n + k.val
      | .inr (k, pi) => n + g + (k.val * ((m + 1) * (m + 1)) + pi.1.val * (m + 1) + pi.2.val) := by
  set nSlot := n + g + g * ((m + 1) * (m + 1))
  have hs := slotOffset_lt t.2
  dsimp only [slotToNat]
  rw [Nat.mul_comm _ nSlot, Nat.mul_add_mod, Nat.mod_eq_of_lt hs]
  rfl

private theorem slotToNat_injective :
    Function.Injective (slotToNat (n := n) (g := g) (m := m) (ℓ := ℓ)) := by
  rintro ⟨r₁, s₁⟩ ⟨r₂, s₂⟩ h
  have hr_eq : (BinaryField.equivFin (show 2 * ℓ + 2 ≠ 0 by omega) r₁).val =
      (BinaryField.equivFin (show 2 * ℓ + 2 ≠ 0 by omega) r₂).val := by
    have hdiv := congrArg (· / (n + g + g * ((m + 1) * (m + 1)))) h
    rwa [slotToNat_div, slotToNat_div] at hdiv
  have ht1 : r₁ = r₂ :=
    (BinaryField.equivFin (show 2 * ℓ + 2 ≠ 0 by omega)).injective (Fin.ext hr_eq)
  have hs_eq : (match s₁ with
      | .inl (.input i) => i.val
      | .inl (.gate k) => n + k.val
      | .inr (k, pi) => n + g + (k.val * ((m + 1) * (m + 1)) + pi.1.val * (m + 1) + pi.2.val)) =
      (match s₂ with
      | .inl (.input i) => i.val
      | .inl (.gate k) => n + k.val
      | .inr (k, pi) => n + g + (k.val * ((m + 1) * (m + 1)) + pi.1.val * (m + 1) + pi.2.val)) := by
    have hmod := congrArg (· % (n + g + g * ((m + 1) * (m + 1)))) h
    rwa [slotToNat_mod, slotToNat_mod] at hmod
  have hmul_div : ∀ a b d : ℕ, 0 < d → b < d → (a * d + b) / d = a := fun a b d hd hb => by
    rw [Nat.mul_comm, Nat.mul_add_div hd, Nat.div_eq_of_lt hb, Nat.add_zero]
  refine Prod.ext ht1 ?_
  rcases s₁ with (i₁ | k₁) | ⟨k₁, p₁, j₁⟩ <;> rcases s₂ with (i₂ | k₂) | ⟨k₂, p₂, j₂⟩ <;>
    dsimp only at hs_eq
  · exact congrArg (Sum.inl ∘ Wire.input) (Fin.ext hs_eq)
  · have := i₁.isLt; omega
  · have := i₁.isLt; omega
  · have := i₂.isLt; omega
  · exact congrArg (Sum.inl ∘ Wire.gate) (Fin.ext (by omega))
  · have := k₁.isLt; omega
  · have := i₂.isLt; omega
  · have := k₂.isLt; omega
  · have h1 := p₁.isLt; have h2 := p₂.isLt; have h3 := j₁.isLt; have h4 := j₂.isLt
    have hrem1 : p₁.1 * (m + 1) + j₁.1 < (m + 1) * (m + 1) := by nlinarith
    have hrem2 : p₂.1 * (m + 1) + j₂.1 < (m + 1) * (m + 1) := by nlinarith
    have hoff : k₁.1 * ((m + 1) * (m + 1)) + (p₁.1 * (m + 1) + j₁.1) =
        k₂.1 * ((m + 1) * (m + 1)) + (p₂.1 * (m + 1) + j₂.1) := by omega
    have hk : k₁.1 = k₂.1 := by
      have hdiv := congrArg (· / ((m + 1) * (m + 1))) hoff
      have hmpos : 0 < (m + 1) * (m + 1) := by positivity
      rwa [hmul_div _ _ _ hmpos hrem1, hmul_div _ _ _ hmpos hrem2] at hdiv
    have hrem : p₁.1 * (m + 1) + j₁.1 = p₂.1 * (m + 1) + j₂.1 := by nlinarith
    have hp : p₁.1 = p₂.1 := by
      have hdiv := congrArg (· / (m + 1)) hrem
      rwa [hmul_div _ _ _ (Nat.succ_pos m) h3, hmul_div _ _ _ (Nat.succ_pos m) h4] at hdiv
    have hj : j₁.1 = j₂.1 := by nlinarith
    exact congrArg Sum.inr (Prod.ext (Fin.ext hk) (Prod.ext (Fin.ext hp) (Fin.ext hj)))

private noncomputable def slotEquiv (n g m ℓ : ℕ) :
    Seed ℓ × Slot n g m ≃ Fin (2 ^ (2 * ℓ + 2) * (n + g + g * ((m + 1) * (m + 1)))) :=
  Equiv.ofBijective (fun t => ⟨slotToNat t, slotToNat_lt t⟩)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨fun a b h => slotToNat_injective (congrArg Fin.val h), by
        have hhw : 2 * ℓ + 2 ≠ 0 := by omega
        simp only [Fintype.card_prod, Seed, BinaryField.card hhw, Fintype.card_sum, Wire.card,
          Fintype.card_fin]⟩)

private theorem slotEquiv_val (t : Seed ℓ × Slot n g m) :
    (slotEquiv n g m ℓ t).val = slotToNat t := rfl

private theorem slotToNat_slotEquiv_symm {a : ℕ}
    (ha : a < 2 ^ (2 * ℓ + 2) * (n + g + g * ((m + 1) * (m + 1)))) :
    slotToNat ((slotEquiv n g m ℓ).symm ⟨a, ha⟩) = a :=
  congrArg Fin.val ((slotEquiv n g m ℓ).apply_symm_apply ⟨a, ha⟩)

private theorem card_seed_slot_eq (n g m ℓ : ℕ) :
    Fintype.card (Seed ℓ × Slot n g m) = 2 ^ (2 * ℓ + 2) * (n + g + g * ((m + 1) * (m + 1))) := by
  simpa only [Fintype.card_fin] using Fintype.card_congr (slotEquiv n g m ℓ)

/-- Decode a list of slot indices `< nTotal` into a `Finset (Seed ℓ × Slot n g m)`. -/
private noncomputable def decodeIdxSet (n g m ℓ : ℕ) (S : List ℕ) :
    Finset (Seed ℓ × Slot n g m) :=
  Finset.univ.filter fun t => slotToNat t ∈ S

private theorem mem_decodeIdxSet {S : List ℕ} {t : Seed ℓ × Slot n g m} :
    t ∈ decodeIdxSet n g m ℓ S ↔ slotToNat t ∈ S := by
  simp [decodeIdxSet]

private theorem card_decodeIdxSet {S : List ℕ} (hnd : S.Nodup)
    (hlt : ∀ a ∈ S, a < 2 ^ (2 * ℓ + 2) * (n + g + g * ((m + 1) * (m + 1)))) :
    #(decodeIdxSet n g m ℓ S) = S.length := by
  have hbij : Finset.card (decodeIdxSet n g m ℓ S) = S.toFinset.card := by
    refine Finset.card_bij (fun t _ => slotToNat t)
      (fun t ht => List.mem_toFinset.2 (mem_decodeIdxSet.1 ht))
      (fun a _ b _ h => slotToNat_injective h) fun a ha => ?_
    have haS := List.mem_toFinset.1 ha
    have hval := slotToNat_slotEquiv_symm (hlt a haS)
    exact ⟨(slotEquiv n g m ℓ).symm ⟨a, hlt a haS⟩, mem_decodeIdxSet.2 (hval.symm ▸ haS), hval⟩
  rw [hbij, List.toFinset_card_of_nodup hnd]

/-- Index lists below the slot count that decode to the same set have the same elements. -/
private theorem mem_iff_of_decodeIdxSet_eq {u₁ u₂ : List ℕ}
    (h₁ : ∀ a ∈ u₁, a < 2 ^ (2 * ℓ + 2) * (n + g + g * ((m + 1) * (m + 1))))
    (h₂ : ∀ a ∈ u₂, a < 2 ^ (2 * ℓ + 2) * (n + g + g * ((m + 1) * (m + 1))))
    (heq : decodeIdxSet n g m ℓ u₁ = decodeIdxSet n g m ℓ u₂) (a : ℕ) : a ∈ u₁ ↔ a ∈ u₂ := by
  by_cases ha : a < 2 ^ (2 * ℓ + 2) * (n + g + g * ((m + 1) * (m + 1)))
  · simpa only [mem_decodeIdxSet, slotToNat_slotEquiv_symm] using
      Finset.ext_iff.1 heq ((slotEquiv n g m ℓ).symm ⟨a, ha⟩)
  · exact iff_of_false (fun h => ha (h₁ a h)) (fun h => ha (h₂ a h))

/-- Decode a weighted gate list `W` into a `Multiset (Finset (Seed ℓ × Slot n g m))`. -/
private noncomputable def decodeWList (n g m ℓ : ℕ) (W : List WGate) :
    Multiset (Finset (Seed ℓ × Slot n g m)) :=
  (W : Multiset WGate).bind fun e => Multiset.replicate e.2 (decodeIdxSet n g m ℓ e.1)

/-- Well-formedness invariant for a weighted gate list `W` representing `C.gates`. -/
private def WListRep (n g m ℓ : ℕ) (W : List WGate) (C : SymAnd (Seed ℓ × Slot n g m)) : Prop :=
  decodeWList n g m ℓ W = C.gates ∧
  ∀ e ∈ W, e.1.Nodup ∧ (∀ a ∈ e.1, a < 2 ^ (2 * ℓ + 2) * (n + g + g * ((m + 1) * (m + 1)))) ∧
    0 < e.2

private theorem fanIn_eq_of_wListRep {W : List WGate} {C : SymAnd (Seed ℓ × Slot n g m)}
    (hW : WListRep n g m ℓ W C) :
    (W.map fun e => e.1.length).foldl max 0 = C.fanIn := by
  have hfold_eq : ∀ (l : List ℕ) (init : ℕ),
      l.foldl max init = max init ((l : Multiset ℕ).sup) := by
    intro l; induction l with
    | nil => intro init; simp
    | cons x xs ih =>
      intro init
      rw [List.foldl_cons, ih]
      exact (Multiset.sup_cons x xs ▸ max_assoc init x (xs : Multiset ℕ).sup)
  rw [hfold_eq, Nat.zero_max, SymAnd.fanIn, ← hW.1]
  apply le_antisymm
  · rw [Multiset.sup_le]
    intro d hd
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hd
    obtain ⟨hnd, hlt, hpos⟩ := hW.2 e he
    have hmem : decodeIdxSet n g m ℓ e.1 ∈ decodeWList n g m ℓ W := by
      rw [decodeWList, Multiset.mem_bind]
      exact ⟨e, he, Multiset.mem_replicate.2 ⟨hpos.ne', rfl⟩⟩
    rw [← card_decodeIdxSet hnd hlt]
    exact Multiset.le_sup (Multiset.mem_map_of_mem _ hmem)
  · rw [Multiset.sup_le]
    intro d hd
    obtain ⟨S, hS, rfl⟩ := Multiset.mem_map.1 hd
    rw [decodeWList, Multiset.mem_bind] at hS
    obtain ⟨e, he, hSe⟩ := hS
    rw [Multiset.eq_of_mem_replicate hSe]
    obtain ⟨hnd, hlt, _⟩ := hW.2 e he
    rw [card_decodeIdxSet hnd hlt]
    exact Multiset.le_sup (Multiset.mem_coe.2 (List.mem_map_of_mem he))

/-! #### Uncapped subset-enumeration correctness -/

private theorem subsetsUpToCapped_uncapped {N D U : ℕ} (hU : (N + 1) ^ D ≤ U) :
    (subsetsUpToCapped N D U).Nodup ∧
    ∀ s : List ℕ, s ∈ subsetsUpToCapped N D U ↔
      s.Pairwise (· < ·) ∧ s.length ≤ D ∧ ∀ a ∈ s, a < N := by
  have hcard_all : ∀ k ≤ D,
      #{S : Finset (Fin N) | #S ≤ k} ≤ U := fun k hk => by
    have h1 : #{S : Finset (Fin N) | #S ≤ k} ≤ (Fintype.card (Fin N) + 1) ^ k :=
      card_filter_card_le_le_pow k
    rw [Fintype.card_fin] at h1
    exact h1.trans ((Nat.pow_le_pow_right (Nat.succ_pos N) hk).trans hU)
  have hbij_len : ∀ (L : List (List ℕ)) (k : ℕ), L.Nodup →
      (∀ s ∈ L, s.Pairwise (· < ·) ∧ s.length ≤ k ∧ ∀ a ∈ s, a < N) →
      L.length ≤ #{S : Finset (Fin N) | #S ≤ k} := by
    intro L k hnd hL
    have hcard : L.length = (L.toFinset).card := (List.toFinset_card_of_nodup hnd).symm
    rw [hcard]
    refine Finset.card_le_card_of_injOn (fun s => Finset.univ.filter fun i : Fin N => i.1 ∈ s)
      (fun s hs => ?_) (fun s₁ hs₁ s₂ hs₂ heq => ?_)
    · have hs' := List.mem_toFinset.1 hs
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      calc #(Finset.univ.filter fun i : Fin N => i.1 ∈ s) ≤ #s.toFinset := by
            refine Finset.card_le_card_of_injOn Fin.val
              (fun i hi => List.mem_toFinset.2 (Finset.mem_filter.1 hi).2)
              (fun _ _ _ _ h => Fin.ext h)
        _ ≤ s.length := List.toFinset_card_le s
        _ ≤ k := (hL s hs').2.1
    · obtain ⟨hp₁, -, hlt₁⟩ := hL s₁ (List.mem_toFinset.1 hs₁)
      obtain ⟨hp₂, -, hlt₂⟩ := hL s₂ (List.mem_toFinset.1 hs₂)
      refine hp₁.eq_of_mem_iff hp₂ fun a => ?_
      by_cases ha : a < N
      · simpa using Finset.ext_iff.1 heq ⟨a, ha⟩
      · exact iff_of_false (fun h => ha (hlt₁ a h)) (fun h => ha (hlt₂ a h))
  have hind : ∀ k ≤ D,
      let st := (List.range k).foldl (extendSubsetsStep (N, U)) ([[]], [[]])
      st.1.Nodup ∧ st.2.Nodup ∧
      (∀ s, s ∈ st.1 ↔ s.Pairwise (· < ·) ∧ s.length ≤ k ∧ ∀ a ∈ s, a < N) ∧
      (∀ s, s ∈ st.2 ↔ s.Pairwise (· < ·) ∧ s.length = k ∧ ∀ a ∈ s, a < N) := by
    intro k hk
    induction k with
    | zero =>
      refine ⟨by simp, by simp, fun s => ?_, fun s => ?_⟩
      · simp only [List.range_zero, List.foldl_nil, List.mem_singleton, Nat.le_zero,
          List.length_eq_zero_iff]
        exact ⟨by rintro rfl; simp, fun h => h.2.1⟩
      · simp only [List.range_zero, List.foldl_nil, List.mem_singleton, List.length_eq_zero_iff]
        exact ⟨by rintro rfl; simp, fun h => h.2.1⟩
    | succ k ih =>
      obtain ⟨hnd1, hnd2, hmem1, hmem2⟩ := ih (Nat.le_of_succ_le hk)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      set prev := (List.range k).foldl (extendSubsetsStep (N, U)) ([[]], [[]])
      set rawNext := prev.2.flatMap fun s => (List.range (min (s.headD N) N)).map fun a => a :: s
      have hraw_mem : ∀ s, s ∈ rawNext ↔
          s.Pairwise (· < ·) ∧ s.length = k + 1 ∧ ∀ a ∈ s, a < N := by
        intro s
        simp only [rawNext, List.mem_flatMap, List.mem_map, List.mem_range]
        constructor
        · rintro ⟨t, ht, a, ha, rfl⟩
          obtain ⟨htp, htl, hta⟩ := (hmem2 t).1 ht
          have haN : a < N := lt_of_lt_of_le ha (Nat.min_le_right _ _)
          have haHead : ∀ x ∈ t, a < x := by
            cases t with
            | nil => intro _ hx; exact absurd hx List.not_mem_nil
            | cons y ys =>
              intro x hx
              have haY : a < y := lt_of_lt_of_le ha (by simp)
              rcases List.mem_cons.1 hx with rfl | hx
              · exact haY
              · exact haY.trans ((List.pairwise_cons.1 htp).1 x hx)
          exact ⟨List.pairwise_cons.2 ⟨haHead, htp⟩, by simp [htl], fun x hx =>
            (List.mem_cons.1 hx).elim (· ▸ haN) (hta x)⟩
        · rintro ⟨hp, hl, hlt⟩
          cases s with
          | nil => simp at hl
          | cons a t =>
            obtain ⟨haHead, htp⟩ := List.pairwise_cons.1 hp
            refine ⟨t, (hmem2 t).2 ⟨htp,
              (by simp only [List.length_cons, Nat.add_right_cancel_iff] at hl; exact hl),
              fun x hx => hlt x (List.mem_cons_of_mem a hx)⟩, a, ?_, rfl⟩
            have haN : a < N := hlt a List.mem_cons_self
            cases t with
            | nil => simpa using haN
            | cons y ys =>
              simp only [List.headD_cons, lt_min_iff]
              exact ⟨haHead y List.mem_cons_self, haN⟩
      have hraw_nd : rawNext.Nodup := by
        rw [List.nodup_flatMap]
        refine ⟨fun s _ => (List.nodup_range).map fun _ _ h => (List.cons.inj h).1, ?_⟩
        refine hnd2.pairwise_of_forall_ne fun s₁ _ s₂ _ hne => ?_
        intro x hx₁ hx₂
        obtain ⟨a₁, _, rfl⟩ := List.mem_map.1 hx₁
        obtain ⟨a₂, _, h⟩ := List.mem_map.1 hx₂
        exact hne (List.cons.inj h).2.symm
      have hdisj : List.Disjoint prev.1 rawNext := by
        intro s hs1 hs2
        have h1 := ((hmem1 s).1 hs1).2.1
        have h2 := ((hraw_mem s).1 hs2).2.1
        omega
      have hall_nd : (prev.1 ++ rawNext).Nodup :=
        List.nodup_append.2 ⟨hnd1, hraw_nd, fun x hx y hy hxy => hdisj hx (hxy ▸ hy)⟩
      have hall_mem : ∀ s, s ∈ prev.1 ++ rawNext ↔
          s.Pairwise (· < ·) ∧ s.length ≤ k + 1 ∧ ∀ a ∈ s, a < N := by
        intro s
        rw [List.mem_append, hmem1, hraw_mem]
        constructor
        · rintro (⟨hp, hl, hlt⟩ | ⟨hp, hl, hlt⟩) <;> exact ⟨hp, by omega, hlt⟩
        · rintro ⟨hp, hl, hlt⟩
          rcases Nat.lt_or_eq_of_le hl with hlt' | heq
          · exact Or.inl ⟨hp, by omega, hlt⟩
          · exact Or.inr ⟨hp, heq, hlt⟩
      have hlen_all : (prev.1 ++ rawNext).length ≤ U :=
        (hbij_len _ (k + 1) hall_nd fun s hs => (hall_mem s).1 hs).trans (hcard_all (k + 1) hk)
      have hlen_raw : rawNext.length ≤ U := by
        have := List.length_append (as := prev.1) (bs := rawNext); omega
      simp only [extendSubsetsStep]
      rw [List.take_of_length_le hlen_raw, List.take_of_length_le hlen_all]
      exact ⟨hall_nd, hraw_nd, hall_mem, hraw_mem⟩
  obtain ⟨hnd, _, hmem, _⟩ := hind D le_rfl
  exact ⟨hnd, hmem⟩

private theorem allSubsetsCapped_uncapped {S : List ℕ} {U : ℕ} (hnd : S.Nodup)
    (hU : 2 ^ S.length ≤ U) :
    (allSubsetsCapped S U).Nodup ∧
    (∀ t ∈ allSubsetsCapped S U, t.Nodup ∧ t ⊆ S) ∧
    (∀ T : Finset ℕ, T ⊆ S.toFinset → ∃! t, t ∈ allSubsetsCapped S U ∧ t.toFinset = T) := by
  have haux : ∀ (L : List ℕ), L.Nodup → 2 ^ L.length ≤ U →
      (L.foldl (allSubsetsStep U) [[]]).Nodup ∧
      (L.foldl (allSubsetsStep U) [[]]).length = 2 ^ L.length ∧
      (∀ t ∈ L.foldl (allSubsetsStep U) [[]], t.Nodup ∧ t ⊆ L) ∧
      (∀ T : Finset ℕ, T ⊆ L.toFinset →
        ∃! t, t ∈ L.foldl (allSubsetsStep U) [[]] ∧ t.toFinset = T) := by
    intro L
    induction L using List.reverseRecOn with
    | nil =>
      intro _ hU0
      refine ⟨by simp, by simp, fun t ht => by simp [List.mem_singleton.1 ht], fun T hT => ?_⟩
      have hTe : T = ∅ := Finset.subset_empty.1 (by simpa using hT)
      subst hTe
      exact ⟨[], ⟨by simp, by simp⟩, fun t ⟨ht, _⟩ => by simpa using ht⟩
    | append_singleton L a ih =>
      intro hndL hUL
      rw [List.nodup_append] at hndL
      have haL : a ∉ L := fun h => hndL.2.2 a h a List.mem_cons_self rfl
      have hUL' : 2 ^ L.length ≤ U :=
        (Nat.pow_le_pow_right (by decide) (by simp)).trans hUL
      obtain ⟨hndA, hlenA, hsubA, hbijA⟩ := ih hndL.1 hUL'
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil, allSubsetsStep]
      set acc := L.foldl (allSubsetsStep U) [[]]
      have hlen_new : (acc ++ acc.map (a :: ·)).length = 2 ^ (L ++ [a]).length := by
        simp [hlenA, pow_succ]; omega
      rw [List.take_of_length_le (hlen_new.le.trans hUL)]
      have hndMap : (acc.map (a :: ·)).Nodup := hndA.map fun _ _ h => (List.cons.inj h).2
      have hdisj : List.Disjoint acc (acc.map (a :: ·)) := by
        intro t ht1 ht2
        obtain ⟨t', _, rfl⟩ := List.mem_map.1 ht2
        exact haL ((hsubA _ ht1).2 List.mem_cons_self)
      refine ⟨List.nodup_append.2 ⟨hndA, hndMap, fun x hx y hy hxy => hdisj hx (hxy ▸ hy)⟩,
        hlen_new, ?_, ?_⟩
      · intro t ht
        rcases List.mem_append.1 ht with ht | ht
        · obtain ⟨h1, h2⟩ := hsubA t ht
          exact ⟨h1, fun x hx => List.mem_append_left _ (h2 hx)⟩
        · obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ht
          obtain ⟨h1, h2⟩ := hsubA t' ht'
          refine ⟨List.nodup_cons.2 ⟨fun h => haL (h2 h), h1⟩, fun x hx => ?_⟩
          rcases List.mem_cons.1 hx with rfl | hx
          · exact List.mem_append_right _ List.mem_cons_self
          · exact List.mem_append_left _ (h2 hx)
      · intro T hT
        have hT' : T.erase a ⊆ L.toFinset := by
          intro x hx
          have hxT := Finset.mem_of_mem_erase hx
          have hne := Finset.ne_of_mem_erase hx
          have hmem := hT hxT
          simp only [List.toFinset_append, List.toFinset_cons, List.toFinset_nil,
            Finset.mem_union, Finset.mem_insert, Finset.notMem_empty, or_false] at hmem
          exact hmem.resolve_right hne
        obtain ⟨t₀, ⟨ht₀mem, ht₀eq⟩, ht₀uniq⟩ := hbijA (T.erase a) hT'
        by_cases haT : a ∈ T
        · refine ⟨a :: t₀, ⟨List.mem_append_right _ (List.mem_map_of_mem ht₀mem), ?_⟩, ?_⟩
          · rw [List.toFinset_cons, ht₀eq, Finset.insert_erase haT]
          · rintro t ⟨htmem, hteq⟩
            rcases List.mem_append.1 htmem with htmem | htmem
            · exfalso
              have := (hsubA t htmem).2 (List.mem_toFinset.1 (hteq.symm ▸ haT))
              exact haL this
            · obtain ⟨t', ht'mem, rfl⟩ := List.mem_map.1 htmem
              have ha_not_t' : a ∉ t'.toFinset :=
                fun h => haL ((hsubA t' ht'mem).2 (List.mem_toFinset.1 h))
              have ht'eq : t'.toFinset = T.erase a := by
                rw [← hteq, List.toFinset_cons, Finset.erase_insert ha_not_t']
              rw [ht₀uniq t' ⟨ht'mem, ht'eq⟩]
        · have hTe : T.erase a = T := Finset.erase_eq_of_notMem haT
          rw [hTe] at ht₀eq
          refine ⟨t₀, ⟨List.mem_append_left _ ht₀mem, ht₀eq⟩, ?_⟩
          rintro t ⟨htmem, hteq⟩
          rcases List.mem_append.1 htmem with htmem | htmem
          · exact ht₀uniq t ⟨htmem, hteq.trans hTe.symm⟩
          · obtain ⟨t', _, rfl⟩ := List.mem_map.1 htmem
            exfalso
            exact haT (hteq ▸ List.mem_toFinset.2 List.mem_cons_self)
  obtain ⟨h1, _, h2, h3⟩ := haux S hnd hU
  exact ⟨h1, h2, h3⟩

/-! #### Layer polynomial and Möbius step equivalence -/

private theorem evalLayerQMod_modEq {n g m ℓ M : ℕ} (hm : 0 < m) (hM : 0 < M)
    (c : Σ n', Circuit Unbounded.extSignature n' 1)
    (hn : c.1 = n) (hg : c.2.size = g)
    (hℓ : ℓ = Nat.log 2 (n + g) + 1)
    (layer : Option ℕ) (uSub : List ℕ) (t : Seed ℓ × Slot n g m) :
    let ctx := buildCtx m c
    let L : SLayer (Seed ℓ) (Slot n g m) := match layer with
      | none => ⟨2, fun r => combineQ (hn ▸ hg ▸ c.2.program) r⟩
      | some p₀ => ⟨p₀, fun _ => digitQ (hn ▸ hg ▸ c.2.program) p₀⟩
    ((evalLayerQMod m layer ctx M uSub (slotToNat t) : ℕ) : ℤ) ≡
      L.lift.q t (fun t' => decide (t' ∈ decodeIdxSet n g m ℓ uSub)) [ZMOD (M : ℤ)] := by
  subst hn hg hℓ
  rcases t with ⟨r, s⟩
  set P := c.2.program
  set w := 2 * (Nat.log 2 (c.1 + c.2.size) + 1) + 2
  have hw : w ≠ 0 := by omega
  set ctx := buildCtx m c
  have hctx_n : ctx.n = c.1 := rfl
  have hctx_g : ctx.g = c.2.size := Circuit.length_code_fst c.2
  have hctx_w : ctx.w = w := by dsimp only [ctx, buildCtx]; rw [Circuit.length_code_fst]
  have hctx_nSeed : ctx.nSeed = 2 ^ w := by
    dsimp only [ctx, buildCtx]; rw [Circuit.length_code_fst]
    exact Nat.min_eq_left (two_pow_w_le _).1
  have hctx_modBound : min (2 ^ (w + 1)) (32 * (c.1 + c.2.size + 1) ^ 2) = 2 ^ (w + 1) :=
    Nat.min_eq_left (two_pow_w_le _).2
  have hctx_nSlot : ctx.nSlot = c.1 + c.2.size + c.2.size * ((m + 1) * (m + 1)) := by
    dsimp only [ctx, buildCtx]; rw [Circuit.length_code_fst]
  set nSlot := c.1 + c.2.size + c.2.size * ((m + 1) * (m + 1))
  set rIdx := (BinaryField.equivFin hw r).val
  have hrLt : rIdx < 2 ^ w := (BinaryField.equivFin hw r).isLt
  have hdiv : slotToNat (r, s) / nSlot = rIdx := slotToNat_div (r, s)
  have hmod : slotToNat (r, s) % nSlot = _ := slotToNat_mod (r, s)
  have hmem_iff : ∀ a : ℕ, (uSub.any fun x => decide (x = a)) = decide (a ∈ uSub) := fun a => by
    simp [List.any_eq]
  have hwire_idx : ∀ wire : Wire c.1 c.2.size,
      slotToNat (m := m) (r, (Sum.inl wire : Slot c.1 c.2.size m)) =
        rIdx * nSlot + wire.toNat := by
    intro wire
    cases wire <;> rfl
  have hbitMod : ∀ b : Bool,
      ((if b then 1 % M else 0 : ℕ) : ℤ) ≡ bitVal ℤ b [ZMOD (M : ℤ)] := fun b => by
    cases b
    · simp [bitVal]
    · simp only [↓reduceIte, bitVal, Int.natCast_mod, Nat.cast_one]
      exact Int.mod_modEq 1 M
  have hgate_getD : ∀ k : Fin c.2.size,
      ctx.gates.getD k.1 (0, []) =
        (extOpTag (P.lines k).op, List.ofFn fun a => ((P.lines k).wires a).toNat) := by
    intro k
    have hklt : k.1 < ctx.gates.length := by
      simp only [ctx, buildCtx, List.length_map]; rw [Circuit.length_code_fst]; exact k.isLt
    rw [List.getD_eq_getElem _ _ hklt]
    simp only [ctx, buildCtx, Circuit.code, Program.code_eq_ofFn_lines,
      List.getElem_ofFn, Line.code, List.map_ofFn, Function.comp_def, List.length_ofFn]
    refine Prod.ext rfl (List.ext_getElem (by simp [P]) fun a ha1 ha2 => ?_)
    simp only [List.getElem_ofFn]
    exact Nat.min_eq_left (Wire.toNat_lt _).le
  have hsub_mod := one_sub_modEq_of_pos hM
  cases layer with
  | none =>
    simp only [evalLayerQMod, hctx_n, hctx_g, hctx_nSlot, hctx_w, hdiv, hmod, SLayer.lift]
    rcases s with (i | k) | ⟨k, p, i⟩
    · simp only [i.isLt, ↓reduceIte, combineQ, hmem_iff, mem_decodeIdxSet]
      exact hbitMod _
    · have hnotlt : ¬ c.1 + k.1 < c.1 := by omega
      have hltWire : c.1 + k.1 < c.1 + c.2.size := by have := k.isLt; omega
      simp only [hnotlt, hltWire, ↓reduceIte, Nat.add_sub_cancel_left, combineQ]
      rw [hgate_getD k]
      have hdedup_getD : ctx.gatesDedup.getD k.1 [] =
          (List.ofFn fun a => ((P.lines k).wires a).toNat).eraseDupsBy
            fun a b => decide (a = b) :=
        (List.getD_map (l := ctx.gates) (d := (0, [])) (n := k.1) fun line : ℕ × List ℕ =>
          line.2.eraseDupsBy fun a b => decide (a = b)).trans
          (congrArg (fun x => x.2.eraseDupsBy fun a b => decide (a = b)) (hgate_getD k))
      have hpows_getD : ctx.seedPows.getD rIdx [] =
          seedPowsForSeed (fieldTable w) w (c.1 + c.2.size) rIdx := by
        have hrlt' : rIdx < ctx.seedPows.length := by
          have hlen : ctx.seedPows.length = ctx.nSeed := by
            simp only [ctx, buildCtx, List.length_map, List.length_range]
          rw [hlen, hctx_nSeed]; exact hrLt
        rw [List.getD_eq_getElem _ _ hrlt']
        simp only [ctx, buildCtx, List.getElem_map, List.getElem_range]
        rw [Circuit.length_code_fst c.2,
          show 2 * (Nat.log 2 (c.1 + c.2.size) + 1) + 2 = w from rfl, hctx_modBound]
        rfl
      rw [hdedup_getD, hpows_getD]
      have horTest_modEq : ∀ {ar : ℕ} (ws : Fin ar → Wire c.1 c.2.size) (neg : Bool),
          ((orTestProdMod w M (seedPowsForSeed (fieldTable w) w (c.1 + c.2.size) rIdx)
            ((List.ofFn fun a => (ws a).toNat).eraseDupsBy fun a b => decide (a = b))
            (rIdx * nSlot) uSub neg : ℕ) : ℤ) ≡
          ∏ j : Fin w, (1 - ∑ wire ∈ Finset.univ.image ws,
            (((seedBasis (Nat.log 2 (c.1 + c.2.size) + 1)).repr (r ^ widx wire) j).val : ℤ) *
              bitVal ℤ (xor neg (decide ((r, Sum.inl wire) ∈ decodeIdxSet c.1 c.2.size m
                (Nat.log 2 (c.1 + c.2.size) + 1) uSub)))) [ZMOD (M : ℤ)] := by
        intro ar ws neg
        set wsD := (List.ofFn fun a => (ws a).toNat).eraseDupsBy
          fun a b => decide (a = b)
        set sp := seedPowsForSeed (fieldTable w) w (c.1 + c.2.size) rIdx
        obtain ⟨hsp_len, hsp_val⟩ := seedPowsForSeed_spec hw (c.1 + c.2.size) hrLt
        have hcnt_eq : ∀ j : Fin w,
            (wsD.countP fun wire =>
              ((sp.getD wire []).getD j.1 false) &&
                xor neg (uSub.any fun x => decide (x = rIdx * nSlot + wire)) : ℤ) =
            ∑ wire ∈ Finset.univ.image ws,
              (((seedBasis (Nat.log 2 (c.1 + c.2.size) + 1)).repr (r ^ widx wire) j).val : ℤ) *
                bitVal ℤ (xor neg (decide ((r, Sum.inl wire) ∈ decodeIdxSet c.1 c.2.size m
                  (Nat.log 2 (c.1 + c.2.size) + 1) uSub))) := by
          intro j
          have hwsD : wsD.toFinset = (Finset.univ.image ws).image Wire.toNat := by
            ext x
            rw [List.mem_toFinset, List.mem_eraseDupsBy_eq, List.mem_ofFn, Finset.image_image]
            simp
          rw [List.countP_eq_length_filter,
            ← List.toFinset_card_of_nodup ((List.nodup_eraseDupsBy_eq _).filter _),
            List.toFinset_filter, hwsD, Finset.filter_image,
            Finset.card_image_of_injective _ Wire.toNat_injective, Finset.card_filter, Nat.cast_sum]
          refine Finset.sum_congr rfl fun wire _ => ?_
          have hwlt : wire.toNat < c.1 + c.2.size := Wire.toNat_lt wire
          have hsp_lt : wire.toNat < sp.length := by rw [hsp_len]; exact hwlt
          have hrepr : ((seedBasis (Nat.log 2 (c.1 + c.2.size) + 1)).repr (r ^ widx wire) j).val =
              ((sp.getD wire.toNat []).getD j.1 false).toNat := by
            have hwidx : widx wire = wire.toNat := by cases wire <;> rfl
            rw [hwidx, List.getD_eq_getElem sp [] hsp_lt]
            have hfv := hsp_val wire.toNat hwlt
            have ht1 : (BinaryField.equivFin hw).symm ⟨rIdx, hrLt⟩ = r :=
              (BinaryField.equivFin hw).symm_apply_apply r
            rw [ht1] at hfv
            rw [← hfv, seedBasis, repr_fieldOfBits]
            cases (sp[wire.toNat]'hsp_lt).getD j.1 false <;> rfl
          simp only [hrepr, mem_decodeIdxSet, hwire_idx wire, hmem_iff]
          cases (sp.getD wire.toNat []).getD j.1 false <;>
            cases xor neg (decide (rIdx * nSlot + wire.toNat ∈ uSub)) <;> simp [bitVal]
        -- Relate `foldl` over `List.range w` to `∏ j : Fin w`
        have hfold_prod : ∀ q ≤ w,
            (((List.range q).foldl (fun acc j =>
              let cnt := wsD.countP fun wire =>
                ((sp.getD wire []).getD j false) &&
                  xor neg (uSub.any fun x => decide (x = rIdx * nSlot + wire))
              acc * ((M + 1 - cnt % M) % M) % M) (1 % M) : ℕ) : ℤ) ≡
            ∏ j ∈ (Finset.univ : Finset (Fin w)).filter (fun j => j.1 < q),
              (1 - ∑ wire ∈ Finset.univ.image ws,
                (((seedBasis (Nat.log 2 (c.1 + c.2.size) + 1)).repr (r ^ widx wire) j).val : ℤ) *
                  bitVal ℤ (xor neg (decide ((r, Sum.inl wire) ∈ decodeIdxSet c.1 c.2.size m
                    (Nat.log 2 (c.1 + c.2.size) + 1) uSub)))) [ZMOD (M : ℤ)] := by
          intro q hq
          induction q with
          | zero =>
            simp only [List.range_zero, List.foldl_nil, Nat.not_lt_zero, Finset.filter_false,
              Finset.prod_empty, Int.natCast_mod, Nat.cast_one]
            exact Int.mod_modEq 1 M
          | succ q ih =>
            rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
            have hset : (Finset.univ : Finset (Fin w)).filter (fun j => j.1 < q + 1) =
                insert ⟨q, hq⟩ ((Finset.univ : Finset (Fin w)).filter (fun j => j.1 < q)) := by
              ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
                Fin.ext_iff]; omega
            rw [hset, Finset.prod_insert (by simp), Int.natCast_mod, Nat.cast_mul]
            refine (Int.mod_modEq _ _).trans ?_
            rw [mul_comm (1 - _)]
            refine (ih (Nat.le_of_succ_le hq)).mul ?_
            have hc := hcnt_eq ⟨q, hq⟩
            exact (hsub_mod _).trans (by rw [hc])
        have hfull := hfold_prod w le_rfl
        have hfilt : (Finset.univ : Finset (Fin w)).filter (fun j => j.1 < w) = Finset.univ :=
          Finset.filter_true_of_mem fun j _ => j.isLt
        rw [hfilt] at hfull
        unfold orTestProdMod
        simpa only [posMod_eq_of_pos hM] using hfull
      -- Case split on gate op
      cases hop : P.lines k with
      | mk op ws =>
        rcases op with ((_ | ar | ar) | ar)
        · -- NOT
          have hlen1 : 0 < (List.ofFn fun a => (ws a).toNat).length := by
            simp [Unbounded.extSignature]
          simp only [extOpTag, ↓reduceIte, linePoly, List.getD_eq_getElem _ _ hlen1,
            List.getElem_ofFn, hmem_iff, mem_decodeIdxSet, ← hwire_idx]
          change ((if decide (slotToNat (r, Sum.inl (ws 0)) ∈ uSub) = true then 0 else 1 % M :
              ℕ) : ℤ) ≡ 1 - bitVal ℤ (decide (slotToNat (r, Sum.inl (ws 0)) ∈ uSub)) [ZMOD (M : ℤ)]
          cases decide (slotToNat (r, Sum.inl (ws 0)) ∈ uSub)
          · simp only [Bool.false_eq_true, ↓reduceIte, bitVal, sub_zero, Int.natCast_mod,
              Nat.cast_one]
            exact Int.mod_modEq 1 M
          · simp [bitVal]
        · -- AND
          simp only [extOpTag, show (1 : ℕ) ≠ 0 by decide, ↓reduceIte, linePoly, orTest,
            sub_sub_cancel]
          simpa only [Bool.true_xor] using horTest_modEq ws true
        · -- OR
          simp only [extOpTag, show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide, ↓reduceIte,
            linePoly, orTest]
          have h := horTest_modEq ws false
          simp only [Bool.false_xor] at h
          exact (hsub_mod _).trans (Int.ModEq.sub_left 1 h)
        · -- MOD_m gate
          simp only [extOpTag, show (3 : ℕ) ≠ 0 by decide, show (3 : ℕ) ≠ 1 by decide,
            show (3 : ℕ) ≠ 2 by decide, ↓reduceIte, linePoly]
          have hany_iff : ((relList m).any fun pi =>
              uSub.any fun x =>
                decide (x = rIdx * nSlot + (c.1 + c.2.size) +
                  (k.1 * ((m + 1) * (m + 1)) + pi.1 * (m + 1) + pi.2))) = true ↔
              ∃ pi ∈ rel m, (r, Sum.inr (k, pi)) ∈
                decodeIdxSet c.1 c.2.size m (Nat.log 2 (c.1 + c.2.size) + 1) uSub := by
            simp only [List.any_eq_true, hmem_iff, decide_eq_true_eq, mem_decodeIdxSet, mem_rel]
            constructor
            · rintro ⟨⟨p, i⟩, hpi, hmem⟩
              obtain ⟨hp, hi, hprime, hdvd⟩ := mem_relList_iff.1 hpi
              exact ⟨(⟨p, hp⟩, ⟨i, hi⟩), ⟨hprime, hdvd⟩, by
                simpa only [slotToNat, slotOffset, rIdx, nSlot, Nat.add_assoc] using hmem⟩
            · rintro ⟨⟨p, i⟩, ⟨hprime, hdvd⟩, hmem⟩
              exact ⟨(p.1, i.1), mem_relList_iff.2 ⟨p.isLt, i.isLt, hprime, hdvd⟩, by
                simpa only [slotToNat, slotOffset, rIdx, nSlot, Nat.add_assoc] using hmem⟩
          have hprod : (1 - ∏ pi ∈ rel m,
              (1 - bitVal ℤ (decide ((r, Sum.inr (k, pi)) ∈
                decodeIdxSet c.1 c.2.size m (Nat.log 2 (c.1 + c.2.size) + 1) uSub)))) =
              bitVal ℤ (decide (∃ pi ∈ rel m, (r, Sum.inr (k, pi)) ∈
                decodeIdxSet c.1 c.2.size m (Nat.log 2 (c.1 + c.2.size) + 1) uSub)) := by
            by_cases hex : ∃ pi ∈ rel m, (r, Sum.inr (k, pi)) ∈
                decodeIdxSet c.1 c.2.size m (Nat.log 2 (c.1 + c.2.size) + 1) uSub
            · obtain ⟨pi, hpi, hmem⟩ := hex
              rw [Finset.prod_eq_zero hpi (by simp [hmem, bitVal]), decide_eq_true ⟨pi, hpi, hmem⟩]
              simp [bitVal]
            · push Not at hex
              rw [Finset.prod_eq_one fun pi hpi => by simp [hex pi hpi, bitVal],
                decide_eq_false fun ⟨pi, hpi, hmem⟩ => hex pi hpi hmem]
              simp [bitVal]
          rw [hprod]
          have hbeq : ((relList m).any fun pi =>
              uSub.any fun x =>
                decide (x = rIdx * nSlot + (c.1 + c.2.size) +
                  (k.1 * ((m + 1) * (m + 1)) + pi.1 * (m + 1) + pi.2))) =
              decide (∃ pi ∈ rel m, (r, Sum.inr (k, pi)) ∈
                decodeIdxSet c.1 c.2.size m (Nat.log 2 (c.1 + c.2.size) + 1) uSub) :=
            Bool.eq_iff_iff.2 (hany_iff.trans decide_eq_true_iff.symm)
          rw [hbeq]
          exact hbitMod _
    · have hnotlt1 :
          ¬ c.1 + c.2.size + (k.1 * ((m + 1) * (m + 1)) + p.1 * (m + 1) + i.1) < c.1 := by
        omega
      have hnotlt2 : ¬ c.1 + c.2.size + (k.1 * ((m + 1) * (m + 1)) + p.1 * (m + 1) + i.1) <
          c.1 + c.2.size := by omega
      simp only [hnotlt1, hnotlt2, ↓reduceIte, combineQ, hmem_iff, mem_decodeIdxSet]
      exact hbitMod _
  | some p₀ =>
    simp only [evalLayerQMod, hctx_n, hctx_g, hctx_nSlot, hdiv, hmod, SLayer.lift]
    rcases s with (i | k) | ⟨k, p, i⟩
    · have hlt : i.1 < c.1 + c.2.size := by have := i.isLt; omega
      simp only [hlt, ↓reduceIte, digitQ, hmem_iff, mem_decodeIdxSet]
      exact hbitMod _
    · have hlt : c.1 + k.1 < c.1 + c.2.size := by have := k.isLt; omega
      simp only [hlt, ↓reduceIte, digitQ, hmem_iff, mem_decodeIdxSet]
      exact hbitMod _
    · have hnotlt : ¬ c.1 + c.2.size + (k.1 * ((m + 1) * (m + 1)) + p.1 * (m + 1) + i.1) <
          c.1 + c.2.size := by omega
      simp only [hnotlt, ↓reduceIte, Nat.add_sub_cancel_left, digitQ]
      have hremLt : p.1 * (m + 1) + i.1 < (m + 1) * (m + 1) := by
        have hp := p.isLt; have hi := i.isLt; nlinarith
      have hk : (k.1 * ((m + 1) * (m + 1)) + p.1 * (m + 1) + i.1) / ((m + 1) * (m + 1)) = k.1 ∧
          (k.1 * ((m + 1) * (m + 1)) + p.1 * (m + 1) + i.1) % ((m + 1) * (m + 1)) =
            p.1 * (m + 1) + i.1 := (Nat.div_mod_unique (by positivity)).2 ⟨by ring, hremLt⟩
      have hpi : (p.1 * (m + 1) + i.1) / (m + 1) = p.1 ∧ (p.1 * (m + 1) + i.1) % (m + 1) = i.1 :=
        (Nat.div_mod_unique (by omega)).2 ⟨by ring, i.isLt⟩
      rw [hk.1, hk.2, hpi.1, hpi.2]
      have hcond_iff : (decide (p.1 = p₀) && (relList m).any
          (fun pi => decide (pi.1 = p.1) && decide (pi.2 = i.1))) = true ↔
          (p.1 = p₀ ∧ (p, i) ∈ rel m) := by
        simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, mem_rel]
        constructor
        · rintro ⟨hp0, ⟨p', i'⟩, hpi, rfl, rfl⟩
          obtain ⟨_, _, hpr, hdvd⟩ := mem_relList_iff.1 hpi
          exact ⟨hp0, hpr, hdvd⟩
        · rintro ⟨hp0, hpr, hdvd⟩
          exact ⟨hp0, (p.1, i.1), mem_relList_iff.2 ⟨p.isLt, i.isLt, hpr, hdvd⟩, rfl, rfl⟩
      by_cases hcond : p.1 = p₀ ∧ (p, i) ∈ rel m
      · rw [ite_eq_left (hcond_iff.2 hcond), ite_eq_left hcond]
        have he_le : p₀ ^ i.1 ≤ m := by
          obtain ⟨rfl, hpi⟩ := hcond
          exact (Nat.pow_le_pow_right (mem_rel.1 hpi).1.pos (Nat.le_succ _)).trans
            (Nat.le_of_dvd hm (mem_rel.1 hpi).2)
        rw [Nat.min_eq_left he_le, hgate_getD k, digitPoly, sum_powersetCard_monomial]
        have hcnt_eq : ((List.ofFn fun a => ((P.lines k).wires a).toNat).countP
            fun wire => uSub.any fun x => decide (x = rIdx * nSlot + wire)) =
            #{a | decide ((r, Sum.inl ((P.lines k).wires a)) ∈
              decodeIdxSet c.1 c.2.size m (Nat.log 2 (c.1 + c.2.size) + 1) uSub) = true} := by
          rw [List.countP_ofFn, Finset.card_filter, Finset.card_filter]
          refine Finset.sum_congr rfl fun a _ => ?_
          simp only [hmem_iff, mem_decodeIdxSet, hwire_idx]
        rw [hcnt_eq, Int.natCast_mod]
        exact Int.mod_modEq _ _
      · rw [ite_eq_right (fun h => hcond (hcond_iff.1 h)), ite_eq_right hcond]
        simp only [hmem_iff, mem_decodeIdxSet]
        exact hbitMod _

private noncomputable def layerOfOpt (P : Program Unbounded.extSignature n g) (m ℓ : ℕ) :
    Option ℕ → SLayer (Seed ℓ) (Slot n g m)
  | none => ⟨2, fun r => combineQ P r⟩
  | some p₀ => ⟨p₀, fun _ => digitQ P p₀⟩

private theorem amplifiedCountMod_modEq {m M k : ℕ} (hm : 0 < m) (hM : 0 < M)
    (c : Σ n', Circuit Unbounded.extSignature n' 1)
    (layer : Option ℕ) (W : List WGate)
    (C : SymAnd (Seed (Nat.log 2 (c.1 + c.2.size) + 1) × Slot c.1 c.2.size m))
    (hW : WListRep c.1 c.2.size m (Nat.log 2 (c.1 + c.2.size) + 1) W C)
    (uSub : List ℕ) :
    let ℓ := Nat.log 2 (c.1 + c.2.size) + 1
    let L := layerOfOpt c.2.program m ℓ layer
    ((amplifiedCountMod m layer (buildCtx m c) k M W uSub : ℕ) : ℤ) ≡
      SymAnd.amplifiedCount C L.lift k
        (fun t' => decide (t' ∈ decodeIdxSet c.1 c.2.size m ℓ uSub)) [ZMOD (M : ℤ)] := by
  let ℓ := Nat.log 2 (c.1 + c.2.size) + 1
  let L := layerOfOpt c.2.program m ℓ layer
  let v : Seed ℓ × Slot c.1 c.2.size m → Bool :=
    fun t' => decide (t' ∈ decodeIdxSet c.1 c.2.size m ℓ uSub)
  have hL_p : L.lift.p = layer.getD 2 := by cases layer <;> rfl
  have hslot_mod : ∀ t : Seed ℓ × Slot c.1 c.2.size m,
      ((evalOneSubParityAmpMod k M
        (powMod M (evalLayerQMod m layer (buildCtx m c) M uSub (slotToNat t))
          (layer.getD 2 - 1)) : ℕ) : ℤ) ≡
      1 - (parityAmplifier k).eval (L.lift.q t v ^ (L.lift.p - 1)) [ZMOD (M : ℤ)] := by
    intro t
    have hq : ((evalLayerQMod m layer (buildCtx m c) M uSub (slotToNat t) : ℕ) : ℤ) ≡
        L.lift.q t v [ZMOD (M : ℤ)] := by
      cases layer <;> exact evalLayerQMod_modEq hm hM c rfl rfl rfl _ uSub t
    have hpow : ((powMod M (evalLayerQMod m layer (buildCtx m c) M uSub (slotToNat t))
          (layer.getD 2 - 1) : ℕ) : ℤ) ≡
        L.lift.q t v ^ (L.lift.p - 1) [ZMOD (M : ℤ)] := by
      rw [powMod_of_ne_zero hM.ne', Int.natCast_mod, Int.natCast_pow, hL_p]
      exact (Int.mod_modEq _ _).trans (hq.pow _)
    have hamp := evalOneSubParityAmpMod_modEq (k := k) hM
      (y := powMod M (evalLayerQMod m layer (buildCtx m c) M uSub (slotToNat t))
        (layer.getD 2 - 1))
    have heval : (parityAmplifier k).eval
          ((powMod M (evalLayerQMod m layer (buildCtx m c) M uSub (slotToNat t))
            (layer.getD 2 - 1) : ℕ) : ℤ) ≡
        (parityAmplifier k).eval (L.lift.q t v ^ (L.lift.p - 1)) [ZMOD (M : ℤ)] := by
      rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
      exact Int.ModEq.sum fun i _ => Int.ModEq.mul_left _ (hpow.pow i)
    exact hamp.trans (Int.ModEq.sub_left 1 heval)
  have hprod_mod : ∀ (S : List ℕ), S.Nodup →
      (∀ a ∈ S, a < 2 ^ (2 * ℓ + 2) * (c.1 + c.2.size + c.2.size * ((m + 1) * (m + 1)))) →
      ((S.foldl (fun pacc t =>
        let qMod := evalLayerQMod m layer (buildCtx m c) M uSub t
        let qPow := powMod M qMod (layer.getD 2 - 1)
        pacc * evalOneSubParityAmpMod k M qPow % M) (1 % M) : ℕ) : ℤ) ≡
      ∏ t ∈ decodeIdxSet c.1 c.2.size m ℓ S,
        (1 - (parityAmplifier k).eval (L.lift.q t v ^ (L.lift.p - 1))) [ZMOD (M : ℤ)] := by
    intro S
    induction S using List.reverseRecOn with
    | nil =>
      intro _ _
      simp only [List.foldl_nil, Int.natCast_mod, Nat.cast_one]
      have hmt : decodeIdxSet c.1 c.2.size m ℓ [] = ∅ := by ext t; simp [mem_decodeIdxSet]
      rw [hmt, Finset.prod_empty]
      exact Int.mod_modEq 1 M
    | append_singleton S a ih =>
      intro hnd hlt
      rw [List.nodup_append] at hnd
      have haS : a ∉ S := fun h => hnd.2.2 a h a List.mem_cons_self rfl
      have haLt := hlt a (List.mem_append_right _ List.mem_cons_self)
      set ta := (slotEquiv c.1 c.2.size m ℓ).symm ⟨a, haLt⟩
      have hta_val : slotToNat ta = a := slotToNat_slotEquiv_symm haLt
      have hset : decodeIdxSet c.1 c.2.size m ℓ (S ++ [a]) =
          insert ta (decodeIdxSet c.1 c.2.size m ℓ S) := by
        ext t
        simp only [mem_decodeIdxSet, List.mem_append, List.mem_singleton, Finset.mem_insert]
        rw [← hta_val, slotToNat_injective.eq_iff, or_comm]
      have hta_not : ta ∉ decodeIdxSet c.1 c.2.size m ℓ S := by
        rw [mem_decodeIdxSet, hta_val]; exact haS
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil, hset, Finset.prod_insert hta_not,
        mul_comm, Int.natCast_mod, Nat.cast_mul]
      refine (Int.mod_modEq _ _).trans
        ((ih hnd.1 fun x hx => hlt x (List.mem_append_left _ hx)).mul ?_)
      rw [← hta_val]
      exact hslot_mod ta
  -- Express `SymAnd.amplifiedCount C` as a list sum over `W`
  have hsum_eq : SymAnd.amplifiedCount C L.lift k v =
      (W.map fun e => (e.2 : ℤ) * ∏ t ∈ decodeIdxSet c.1 c.2.size m ℓ e.1,
        (1 - (parityAmplifier k).eval (L.lift.q t v ^ (L.lift.p - 1)))).sum := by
    rw [SymAnd.amplifiedCount, ← hW.1, decodeWList, Multiset.map_bind, Multiset.sum_bind]
    simp only [Multiset.map_replicate, Multiset.sum_replicate, ← Multiset.sum_coe, Multiset.map_coe]
    rfl
  dsimp only
  rw [hsum_eq, amplifiedCountMod]
  simp only [ampGateProdMod, posMod_eq_of_pos hM]
  have hfold_sum : ∀ (Ws : List WGate),
      (∀ e ∈ Ws, e.1.Nodup ∧
        ∀ a ∈ e.1, a < 2 ^ (2 * ℓ + 2) * (c.1 + c.2.size + c.2.size * ((m + 1) * (m + 1)))) →
      ((Ws.foldl (fun acc entry =>
        let prod := entry.1.foldl (fun pacc t =>
          let qMod := evalLayerQMod m layer (buildCtx m c) M uSub t
          let qPow := powMod M qMod (layer.getD 2 - 1)
          pacc * evalOneSubParityAmpMod k M qPow % M) (1 % M)
        (acc + entry.2 % M * prod % M) % M) 0 : ℕ) : ℤ) ≡
      (Ws.map fun e => (e.2 : ℤ) * ∏ t ∈ decodeIdxSet c.1 c.2.size m ℓ e.1,
        (1 - (parityAmplifier k).eval (L.lift.q t v ^ (L.lift.p - 1)))).sum [ZMOD (M : ℤ)] := by
    intro Ws
    induction Ws using List.reverseRecOn with
    | nil => intro _; simp
    | append_singleton Ws e ih =>
      intro hWs
      have he := hWs e (List.mem_append_right _ List.mem_cons_self)
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil, List.map_append, List.map_singleton,
        List.sum_append, List.sum_singleton, Int.natCast_mod, Nat.cast_add, Int.natCast_mod,
        Nat.cast_mul, Int.natCast_mod]
      refine (Int.mod_modEq _ _).trans
        ((ih fun x hx => hWs x (List.mem_append_left _ hx)).add ?_)
      exact (Int.mod_modEq _ _).trans ((Int.mod_modEq _ _).mul (hprod_mod e.1 he.1 he.2))
  exact hfold_sum W fun e he => ⟨(hW.2 e he).1, (hW.2 e he).2.1⟩

private theorem collapseStepExec_rep {m B U : ℕ} (hm : 0 < m)
    (c : Σ n', Circuit Unbounded.extSignature n' 1)
    (layer : Option ℕ) (hp : (layer.getD 2).Prime)
    (W : List WGate)
    (C : SymAnd (Seed (Nat.log 2 (c.1 + c.2.size) + 1) × Slot c.1 c.2.size m))
    (hW : WListRep c.1 c.2.size m (Nat.log 2 (c.1 + c.2.size) + 1) W C)
    (hD_U : C.fanIn * ((2 * (B + 1) - 1) * ((layer.getD 2 - 1) * B)) ≤ U)
    (hSub_U : (Fintype.card (Seed (Nat.log 2 (c.1 + c.2.size) + 1) × Slot c.1 c.2.size m) + 1) ^
        (C.fanIn * ((2 * (B + 1) - 1) * ((layer.getD 2 - 1) * B))) ≤ U)
    (hPow_U : 2 ^ (C.fanIn * ((2 * (B + 1) - 1) * ((layer.getD 2 - 1) * B))) ≤ U) :
    let ℓ := Nat.log 2 (c.1 + c.2.size) + 1
    let L := layerOfOpt c.2.program m ℓ layer
    WListRep c.1 c.2.size m ℓ
      (collapseStepExec m layer (buildCtx m c) U B W)
      (SymAnd.collapseStep C L.lift (B + 1) B) := by
  let ℓ := Nat.log 2 (c.1 + c.2.size) + 1
  let p := layer.getD 2
  let L := layerOfOpt c.2.program m ℓ layer
  let M := p ^ (B + 1)
  have hM : 0 < M := pow_pos hp.pos _
  have hLp : L.lift.p = p := by cases layer <;> rfl
  let D := C.fanIn * ((2 * (B + 1) - 1) * ((p - 1) * B))
  let N := 2 ^ (2 * ℓ + 2) * (c.1 + c.2.size + c.2.size * ((m + 1) * (m + 1)))
  have hN_eq : (buildCtx m c).nTotal = N := by
    dsimp only [buildCtx, N, ℓ]; rw [Circuit.length_code_fst]
    rw [Nat.min_eq_left (two_pow_w_le _).1]
  have hfan : (W.map fun e => e.1.length).foldl max 0 = C.fanIn := fanIn_eq_of_wListRep hW
  have hD_min : min ((W.map fun e => e.1.length).foldl max 0 *
      ((2 * (B + 1) - 1) * ((layer.getD 2 - 1) * B))) U = D := by
    rw [hfan]; exact Nat.min_eq_left hD_U
  have hN_card : Fintype.card (Seed ℓ × Slot c.1 c.2.size m) = N := card_seed_slot_eq _ _ _ _
  have hSub_U' : (N + 1) ^ D ≤ U := by rwa [← hN_card]
  obtain ⟨hcand_nd, hcand_mem⟩ := subsetsUpToCapped_uncapped hSub_U'
  -- Prove `mobiusCoeffMod` equals `(subsetMobius ... % M).toNat` for every `S ∈ cand`
  have hcoeff_eq : ∀ S ∈ subsetsUpToCapped N D U,
      mobiusCoeffMod m layer (buildCtx m c) (B + 1) M U W S =
        (subsetMobius (fun U' => SymAnd.amplifiedCount C L.lift (B + 1)
          fun t => decide (t ∈ U')) (decodeIdxSet c.1 c.2.size m ℓ S) % (M : ℤ)).toNat := by
    intro S hS
    obtain ⟨hSp, hSl, hSlt⟩ := (hcand_mem S).1 hS
    have hSnd : S.Nodup := hSp.nodup
    have h2S : 2 ^ S.length ≤ U := (Nat.pow_le_pow_right (by decide) hSl).trans hPow_U
    obtain ⟨hsubs_nd, hsubs_sub, hsubs_bij⟩ := allSubsetsCapped_uncapped hSnd h2S
    -- Show the fold equals `subsetMobius` modulo `M`, and is `< M`
    have hfold_lt : mobiusCoeffMod m layer (buildCtx m c) (B + 1) M U W S < M := by
      have haux : ∀ (l : List (List ℕ)) (init : ℕ), init < M →
          l.foldl (fun acc uSub =>
            let val := amplifiedCountMod m layer (buildCtx m c) (B + 1) M W uSub
            let term := if (S.length - uSub.length) % 2 = 0 then val % M else (M - val % M) % M
            (acc + term) % M) init < M := by
        intro l; induction l with
        | nil => intro init hi; exact hi
        | cons _ ls ih => intro init _; exact ih _ (Nat.mod_lt _ hM)
      unfold mobiusCoeffMod
      simpa only [posMod_eq_of_pos hM] using haux _ 0 hM
    have hfold_mod : ((mobiusCoeffMod m layer (buildCtx m c) (B + 1) M U W S : ℕ) : ℤ) ≡
        subsetMobius (fun U' => SymAnd.amplifiedCount C L.lift (B + 1)
          fun t => decide (t ∈ U')) (decodeIdxSet c.1 c.2.size m ℓ S) [ZMOD (M : ℤ)] := by
      unfold mobiusCoeffMod
      simp only [posMod_eq_of_pos hM]
      have hfold_sum : ∀ (l : List (List ℕ)),
          ((l.foldl (fun acc uSub =>
            let val := amplifiedCountMod m layer (buildCtx m c) (B + 1) M W uSub
            let term := if (S.length - uSub.length) % 2 = 0 then val % M else (M - val % M) % M
            (acc + term) % M) 0 : ℕ) : ℤ) ≡
          (l.map fun uSub =>
            (-1 : ℤ) ^ (S.length - uSub.length) *
              (amplifiedCountMod m layer (buildCtx m c) (B + 1) M W uSub : ℤ)).sum
            [ZMOD (M : ℤ)] := by
        intro l
        induction l using List.reverseRecOn with
        | nil => simp
        | append_singleton l uSub ih =>
          rw [List.foldl_append, List.foldl_cons, List.foldl_nil, List.map_append,
            List.map_singleton, List.sum_append, List.sum_singleton, Int.natCast_mod, Nat.cast_add]
          refine (Int.mod_modEq _ _).trans (ih.add ?_)
          set val := amplifiedCountMod m layer (buildCtx m c) (B + 1) M W uSub
          by_cases hpar : (S.length - uSub.length) % 2 = 0
          · rw [ite_eq_left hpar, Int.natCast_mod]
            have hev : Even (S.length - uSub.length) := Nat.even_iff.2 hpar
            rw [hev.neg_one_pow, one_mul]
            exact Int.mod_modEq _ _
          · rw [ite_eq_right hpar, Int.natCast_mod]
            have hodd : Odd (S.length - uSub.length) := Nat.odd_iff.2 (by omega)
            rw [hodd.neg_one_pow, neg_one_mul]
            have hlt : val % M < M := Nat.mod_lt val hM
            rw [Int.natCast_sub hlt.le, Int.natCast_mod]
            have h1 : (M : ℤ) - (val : ℤ) % (M : ℤ) ≡ 0 - (val : ℤ) [ZMOD (M : ℤ)] :=
              (Int.modEq_zero_iff_dvd.2 dvd_rfl).sub (Int.mod_modEq _ _)
            simpa only [zero_sub] using (Int.mod_modEq _ _).trans h1
      refine (hfold_sum _).trans ?_
      -- Convert list sum over `allSubsetsCapped S U` to Finset sum over `(decodeIdxSet S).powerset`
      rw [subsetMobius, ← List.sum_toFinset _ hsubs_nd]
      have hsum_bij :
          (∑ uSub ∈ (allSubsetsCapped S U).toFinset,
            (-1 : ℤ) ^ (S.length - uSub.length) *
              (amplifiedCountMod m layer (buildCtx m c) (B + 1) M W uSub : ℤ)) ≡
          ∑ U' ∈ (decodeIdxSet c.1 c.2.size m ℓ S).powerset,
            (-1 : ℤ) ^ (#(decodeIdxSet c.1 c.2.size m ℓ S) - #U') *
              SymAnd.amplifiedCount C L.lift (B + 1) (fun t => decide (t ∈ U')) [ZMOD (M : ℤ)] := by
        have hbij_eq :
            (∑ U' ∈ (decodeIdxSet c.1 c.2.size m ℓ S).powerset,
              (-1 : ℤ) ^ (#(decodeIdxSet c.1 c.2.size m ℓ S) - #U') *
                SymAnd.amplifiedCount C L.lift (B + 1) (fun t => decide (t ∈ U'))) =
            ∑ uSub ∈ (allSubsetsCapped S U).toFinset,
              (-1 : ℤ) ^ (S.length - uSub.length) *
                SymAnd.amplifiedCount C L.lift (B + 1)
                  (fun t => decide (t ∈ decodeIdxSet c.1 c.2.size m ℓ uSub)) := by
          symm
          refine Finset.sum_bij (fun uSub _ => decodeIdxSet c.1 c.2.size m ℓ uSub) ?_ ?_ ?_ ?_
          · intro uSub hu
            rw [Finset.mem_powerset]
            intro t ht
            exact mem_decodeIdxSet.2 ((hsubs_sub uSub (List.mem_toFinset.1 hu)).2
              (mem_decodeIdxSet.1 ht))
          · intro u₁ hu₁ u₂ hu₂ heq
            have h1 := hsubs_sub u₁ (List.mem_toFinset.1 hu₁)
            have h2 := hsubs_sub u₂ (List.mem_toFinset.1 hu₂)
            have hset : u₁.toFinset = u₂.toFinset := Finset.ext fun a => by
              simpa only [List.mem_toFinset] using mem_iff_of_decodeIdxSet_eq
                (fun a ha => hSlt a (h1.2 ha)) (fun a ha => hSlt a (h2.2 ha)) heq a
            obtain ⟨_, _, huniq⟩ := hsubs_bij u₁.toFinset (fun x hx =>
              List.mem_toFinset.2 (h1.2 (List.mem_toFinset.1 hx)))
            exact (huniq u₁ ⟨List.mem_toFinset.1 hu₁, rfl⟩).trans
              (huniq u₂ ⟨List.mem_toFinset.1 hu₂, hset.symm⟩).symm
          · intro U' hU'
            have hsubT : U'.image slotToNat ⊆ S.toFinset := by
              intro a ha
              obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 ha
              exact List.mem_toFinset.2 (mem_decodeIdxSet.1 (Finset.mem_powerset.1 hU' ht))
            obtain ⟨uSub, ⟨huMem, huEq⟩, _⟩ := hsubs_bij (U'.image slotToNat) hsubT
            refine ⟨uSub, List.mem_toFinset.2 huMem, ?_⟩
            ext t
            rw [mem_decodeIdxSet, ← List.mem_toFinset, huEq, slotToNat_injective.mem_finset_image]
          · intro uSub hu
            have hsub := hsubs_sub uSub (List.mem_toFinset.1 hu)
            rw [card_decodeIdxSet hSnd hSlt,
              card_decodeIdxSet hsub.1 fun a ha => hSlt a (hsub.2 ha)]
        rw [hbij_eq]
        refine Int.ModEq.sum fun uSub _ => Int.ModEq.mul_left _ ?_
        exact amplifiedCountMod_modEq (k := B + 1) hm hM c layer W C hW uSub
      simpa only [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one] using hsum_bij
    have hmod_eq : ((mobiusCoeffMod m layer (buildCtx m c) (B + 1) M U W S : ℕ) : ℤ) =
        subsetMobius (fun U' => SymAnd.amplifiedCount C L.lift (B + 1)
          fun t => decide (t ∈ U')) (decodeIdxSet c.1 c.2.size m ℓ S) % (M : ℤ) := by
      have h1 : ((mobiusCoeffMod m layer (buildCtx m c) (B + 1) M U W S : ℕ) : ℤ) % (M : ℤ) = _ :=
        hfold_mod
      rwa [Int.emod_eq_of_lt (Nat.cast_nonneg _) (by exact_mod_cast hfold_lt)] at h1
    rw [← hmod_eq, Int.toNat_natCast]
  -- Now prove `WListRep`
  refine ⟨?_, ?_⟩
  · -- Multiset equality with `(SymAnd.collapseStep C L.lift (B + 1) B).gates`
    rw [collapseStepExec, hN_eq, hD_min]
    rw [SymAnd.collapseStep, SymAnd.ofLowDegree, SymAnd.mobiusGates, hLp]
    -- Show `decodeWList` of filtered mapped `cand` equals `bind` over `univ.filter (#S ≤ D)`
    have hbind_filt : decodeWList c.1 c.2.size m ℓ
        (((subsetsUpToCapped N D U).map fun S =>
            (S, mobiusCoeffMod m layer (buildCtx m c) (B + 1) M U W S)).filter
          fun e => decide (0 < e.2)) =
        ((subsetsUpToCapped N D U : Multiset (List ℕ)).bind fun S =>
          Multiset.replicate (mobiusCoeffMod m layer (buildCtx m c) (B + 1) M U W S)
            (decodeIdxSet c.1 c.2.size m ℓ S)) := by
      simp only [decodeWList, ← Multiset.filter_coe, ← Multiset.map_coe, Multiset.bind_filter,
        Multiset.bind_map]
      refine Multiset.bind_congr fun S _ => ?_
      split_ifs with h
      · rfl
      · rw [Nat.eq_zero_of_not_pos h, Multiset.replicate_zero]
    rw [hbind_filt]
    have hmap_sets : (subsetsUpToCapped N D U : Multiset (List ℕ)).map
        (decodeIdxSet c.1 c.2.size m ℓ) =
        (Finset.univ.filter fun S : Finset (Seed ℓ × Slot c.1 c.2.size m) => #S ≤ D).val := by
      have hnd_img : ((subsetsUpToCapped N D U).map (decodeIdxSet c.1 c.2.size m ℓ)).Nodup := by
        refine hcand_nd.map_on fun s₁ hs₁ s₂ hs₂ heq => ?_
        obtain ⟨hp₁, _, hlt₁⟩ := (hcand_mem s₁).1 hs₁
        obtain ⟨hp₂, _, hlt₂⟩ := (hcand_mem s₂).1 hs₂
        exact hp₁.eq_of_mem_iff hp₂ (mem_iff_of_decodeIdxSet_eq hlt₁ hlt₂ heq)
      rw [Multiset.map_coe]
      refine (Multiset.Nodup.ext (Multiset.coe_nodup.2 hnd_img)
        (Finset.nodup _)).2 fun S => ?_
      simp only [Multiset.mem_coe, List.mem_map, Finset.mem_val, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · rintro ⟨s, hs, rfl⟩
        obtain ⟨hp, hl, hlt⟩ := (hcand_mem s).1 hs
        rw [card_decodeIdxSet hp.nodup hlt]
        exact hl
      · intro hScard
        set s := (S.image slotToNat).sort (· ≤ ·)
        have hsp' : s.Pairwise (· < ·) :=
          ((Finset.pairwise_sort (S.image slotToNat) (· ≤ ·)).and
            (Finset.sort_nodup (S.image slotToNat) (· ≤ ·))).imp
              fun {a b} h => lt_of_le_of_ne h.1 h.2
        refine ⟨s, (hcand_mem s).2 ⟨hsp', ?_, fun a ha => ?_⟩, ?_⟩
        · rw [Finset.length_sort]
          exact Finset.card_image_le.trans hScard
        · obtain ⟨t, _, rfl⟩ := Finset.mem_image.1 (Finset.mem_sort _ |>.1 ha)
          exact slotToNat_lt t
        · ext t
          rw [mem_decodeIdxSet, Finset.mem_sort, slotToNat_injective.mem_finset_image]
    rw [← hmap_sets, Multiset.bind_map]
    refine Multiset.bind_congr fun S hS => ?_
    rw [hcoeff_eq S hS]
  · -- Per-entry invariant: `Nodup`, `< N`, `0 < e.2`
    intro e he
    rw [collapseStepExec, hN_eq, hD_min] at he
    simp only [List.mem_filter, List.mem_map, decide_eq_true_eq] at he
    obtain ⟨⟨S, hS, rfl⟩, hpos⟩ := he
    obtain ⟨hp, _, hlt⟩ := (hcand_mem S).1 hS
    exact ⟨hp.nodup, hlt, hpos⟩

/-! #### Tower collapse and restriction equivalence -/

private noncomputable def layersOfSpec (P : Program Unbounded.extSignature n g) (m ℓ : ℕ)
    (Ls : List (Option ℕ)) : List (SLayer (Seed ℓ) (Slot n g m)) :=
  Ls.map (layerOfOpt P m ℓ)

private theorem layersOfSpec_layerSpec (P : Program Unbounded.extSignature n g) (m ℓ d : ℕ) :
    layersOfSpec P m ℓ (layerSpec d m) = towerS P m ℓ d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [layersOfSpec] at ih ⊢
    simp only [layerSpec, towerS, macroS, List.map_append, List.map_cons, List.map_map,
      Function.comp_def, layerOfOpt, ih]

private theorem collapseRun_out {T : Type*} [Fintype T] [DecidableEq T]
    (C : SymAnd T) (Ls : List (ModPolyLayer T)) (B : ℕ) :
    (SymAnd.collapseRun C Ls B).out =
      fun z => C.out (SymOutParam.nestedMod
        (Ls.zipIdx.map fun q => q.1.p ^ ((fun b => 5 * b ^ 5)^[q.2] B + 1)) z) := by
  induction Ls generalizing C B with
  | nil => rfl
  | cons L Ls ih =>
    rw [SymAnd.collapseRun, ih]
    funext z
    simp only [SymAnd.collapseStep, SymAnd.ofLowDegree, List.zipIdx_cons, List.map_cons,
      Function.iterate_zero, id_eq, SymOutParam.nestedMod, List.foldr_cons]
    congr 2
    have hshift : ∀ (k : ℕ) (l : List (ModPolyLayer T)),
        (l.zipIdx (k + 1)).map (fun q => q.1.p ^ ((fun b => 5 * b ^ 5)^[q.2] B + 1)) =
        (l.zipIdx k).map (fun q => q.1.p ^ ((fun b => 5 * b ^ 5)^[q.2] (5 * B ^ 5) + 1)) := by
      intro k l; induction l generalizing k with
      | nil => rfl
      | cons x xs ihx =>
        simp only [List.zipIdx_cons, List.map_cons, Function.iterate_succ_apply, ihx (k + 1)]
    rw [hshift 0 Ls]

private theorem collapseRunExec_spec {m B_init B U : ℕ} (hm : 0 < m)
    (c : Σ n', Circuit Unbounded.extSignature n' 1)
    (Ls : List (Option ℕ))
    (W : List WGate)
    (C : SymAnd (Seed (Nat.log 2 (c.1 + c.2.size) + 1) × Slot c.1 c.2.size m))
    (hW : WListRep c.1 c.2.size m (Nat.log 2 (c.1 + c.2.size) + 1) W C)
    (hB_ge : B_init ≤ B)
    (hLs_ok : ∀ layer ∈ Ls, (layer.getD 2).Prime ∧ layer.getD 2 ≤ B_init)
    (hLs_deg : ∀ L ∈ (layersOfSpec c.2.program m
        (Nat.log 2 (c.1 + c.2.size) + 1) Ls).map SLayer.lift,
      L.p.Prime ∧ L.p ≤ B ∧
        ∀ t, L.q t ∈ lowDegree ℤ (Seed (Nat.log 2 (c.1 + c.2.size) + 1) × Slot c.1 c.2.size m) B)
    (hT : Fintype.card (Seed (Nat.log 2 (c.1 + c.2.size) + 1) × Slot c.1 c.2.size m) + 1 ≤
      2 ^ B_init)
    (hf : C.fanIn ≤ B) (hs : C.size ≤ 2 ^ B)
    (hU : 2 ^ ((B_init + 2) * (2 * B) ^ 5 ^ Ls.length) ≤ U) :
    let ℓ := Nat.log 2 (c.1 + c.2.size) + 1
    let Ls' := (layersOfSpec c.2.program m ℓ Ls).map SLayer.lift
    let res := collapseRunExec m (buildCtx m c) U Ls B W
    WListRep c.1 c.2.size m ℓ res.1 (SymAnd.collapseRun C Ls' B) ∧
    (∀ z, (SymAnd.collapseRun C Ls' B).out z = C.out (SymOutParam.nestedMod res.2 z)) ∧
    res.2.length = Ls.length ∧
    (∀ M ∈ res.2, M ≤ 2 ^ ((B_init + 2) * (2 * B) ^ 5 ^ Ls.length)) ∧
    (∀ e ∈ res.1, e.2 ≤ U) := by
  induction Ls generalizing W C B with
  | nil =>
    refine ⟨hW, fun _ => rfl, rfl, fun _ h => absurd h List.not_mem_nil, fun e he => ?_⟩
    simp only [collapseRunExec] at he
    have hcard_le : e.2 ≤ C.size := by
      rw [SymAnd.size, ← hW.1, decodeWList, Multiset.card_bind]
      simp only [Function.comp_def, Multiset.card_replicate]
      exact Multiset.le_sum_of_mem (Multiset.mem_map_of_mem _ (Multiset.mem_coe.2 he))
    have hB0 : B ≤ (B_init + 2) * (2 * B) ^ 5 ^ 0 := by
      simp only [pow_zero, pow_one]; nlinarith
    exact hcard_le.trans (hs.trans ((Nat.pow_le_pow_right (by decide) hB0).trans hU))
  | cons layer rest ih =>
    let ℓ := Nat.log 2 (c.1 + c.2.size) + 1
    let p := layer.getD 2
    obtain ⟨hp, hpBi⟩ := hLs_ok layer List.mem_cons_self
    have hpB : p ≤ B := hpBi.trans hB_ge
    have hB1 : 1 ≤ B := le_trans hp.one_lt.le hpB
    have hD_le : C.fanIn * ((2 * (B + 1) - 1) * ((p - 1) * B)) ≤ 3 * B ^ 4 := by
      have h1 : 2 * (B + 1) - 1 ≤ 3 * B := by omega
      have h2 : (p - 1) * B ≤ B * B := Nat.mul_le_mul_right B (by omega)
      calc _ ≤ B * (3 * B * (B * B)) := by gcongr
        _ = 3 * B ^ 4 := by ring
    let B₁ := 5 * B ^ 5
    have hB_le_B1 : B ≤ B₁ :=
      (Nat.le_self_pow (by norm_num) B).trans (Nat.le_mul_of_pos_left _ (by norm_num))
    have hD_le_B1 : C.fanIn * ((2 * (B + 1) - 1) * ((p - 1) * B)) ≤ B₁ :=
      hD_le.trans (by dsimp only [B₁]; gcongr <;> omega)
    have h2B1 : 2 * B₁ ≤ (2 * B) ^ 5 := by
      dsimp only [B₁]; rw [← mul_assoc, mul_pow]; exact Nat.mul_le_mul_right _ (by norm_num)
    have h5pow : (2 * B₁) ^ 5 ^ rest.length ≤ (2 * B) ^ 5 ^ (layer :: rest).length := by
      rw [List.length_cons, pow_succ', pow_mul]
      exact Nat.pow_le_pow_left h2B1 _
    have hB1_le_pow : B₁ ≤ (2 * B) ^ 5 ^ (layer :: rest).length :=
      (show B₁ ≤ 2 * B₁ by omega).trans
        ((Nat.le_self_pow (pow_ne_zero _ (by decide)) (2 * B₁)).trans h5pow)
    have hExp_step : (B_init + 2) * (2 * B₁) ^ 5 ^ rest.length ≤
        (B_init + 2) * (2 * B) ^ 5 ^ (layer :: rest).length :=
      Nat.mul_le_mul_left _ h5pow
    have hD_pow : C.fanIn * ((2 * (B + 1) - 1) * ((p - 1) * B)) ≤
        (2 * B) ^ 5 ^ (layer :: rest).length := hD_le_B1.trans hB1_le_pow
    have hD_U : C.fanIn * ((2 * (B + 1) - 1) * ((p - 1) * B)) ≤ U := by
      have h1 : C.fanIn * ((2 * (B + 1) - 1) * ((p - 1) * B)) ≤
          (B_init + 2) * (2 * B) ^ 5 ^ (layer :: rest).length :=
        hD_pow.trans (Nat.le_mul_of_pos_left _ (by omega))
      exact (h1.trans Nat.lt_two_pow_self.le).trans hU
    have hSub_U : (Fintype.card (Seed ℓ × Slot c.1 c.2.size m) + 1) ^
        (C.fanIn * ((2 * (B + 1) - 1) * ((p - 1) * B))) ≤ U := by
      calc _ ≤ (2 ^ B_init) ^ (C.fanIn * ((2 * (B + 1) - 1) * ((p - 1) * B))) :=
            Nat.pow_le_pow_left hT _
        _ = 2 ^ (B_init * (C.fanIn * ((2 * (B + 1) - 1) * ((p - 1) * B)))) := by rw [← pow_mul]
        _ ≤ 2 ^ ((B_init + 2) * (2 * B) ^ 5 ^ (layer :: rest).length) :=
            Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul (by omega) hD_pow)
        _ ≤ U := hU
    have hPow_U : 2 ^ (C.fanIn * ((2 * (B + 1) - 1) * ((p - 1) * B))) ≤ U :=
      (Nat.pow_le_pow_right (by decide)
        (hD_pow.trans (Nat.le_mul_of_pos_left _ (by omega)))).trans hU
    have hB1_U : B₁ ≤ U :=
      ((hB1_le_pow.trans (Nat.le_mul_of_pos_left _ (by omega))).trans
        Nat.lt_two_pow_self.le).trans hU
    have hStep := collapseStepExec_rep hm c layer hp W C hW hD_U hSub_U hPow_U
    let L₀ : SLayer (Seed ℓ) (Slot c.1 c.2.size m) := layerOfOpt c.2.program m ℓ layer
    have hL₀_eq : layersOfSpec c.2.program m ℓ (layer :: rest) =
        L₀ :: layersOfSpec c.2.program m ℓ rest := rfl
    have hT_B : Fintype.card (Seed ℓ × Slot c.1 c.2.size m) + 1 ≤ 2 ^ B :=
      hT.trans (Nat.pow_le_pow_right (by decide) hB_ge)
    have hL₀_p : L₀.lift.p = p := by cases layer <;> rfl
    have hf1 : (SymAnd.collapseStep C L₀.lift (B + 1) B).fanIn ≤ B₁ := by
      have h1 := SymAnd.fanIn_collapseStep_le C L₀.lift (B + 1) B
      rw [hL₀_p] at h1
      exact h1.trans hD_le_B1
    have hs1 : (SymAnd.collapseStep C L₀.lift (B + 1) B).size ≤ 2 ^ B₁ := by
      have h1 := SymAnd.size_collapseStep_le C L₀.lift (hL₀_p ▸ hp.pos) (B + 1) B
      rw [hL₀_p] at h1
      have hp2 : p ≤ 2 ^ B := hpB.trans Nat.lt_two_pow_self.le
      have hlog : B * (B + 1) + B * (C.fanIn * ((2 * (B + 1) - 1) * ((p - 1) * B))) ≤ B₁ := by
        have h1' : B ^ 1 ≤ B ^ 5 := Nat.pow_le_pow_right hB1 (by norm_num)
        have h2' : B ^ 2 ≤ B ^ 5 := Nat.pow_le_pow_right hB1 (by norm_num)
        have h3' : B * (C.fanIn * ((2 * (B + 1) - 1) * ((p - 1) * B))) ≤ B * (3 * B ^ 4) :=
          Nat.mul_le_mul_left B hD_le
        have h4' : B * (3 * B ^ 4) = 3 * B ^ 5 := by ring
        have h5' : B * (B + 1) = B ^ 2 + B ^ 1 := by ring
        dsimp only [B₁]; linarith
      calc _ ≤ (2 ^ B) ^ (B + 1) * (2 ^ B) ^ (C.fanIn * ((2 * (B + 1) - 1) * ((p - 1) * B))) :=
            h1.trans (Nat.mul_le_mul (Nat.pow_le_pow_left hp2 _) (Nat.pow_le_pow_left hT_B _))
        _ = 2 ^ (B * (B + 1) + B * (C.fanIn * ((2 * (B + 1) - 1) * ((p - 1) * B)))) := by
            rw [← pow_mul, ← pow_mul, ← pow_add]
        _ ≤ 2 ^ B₁ := Nat.pow_le_pow_right (by decide) hlog
    have hIH := ih (collapseStepExec m layer (buildCtx m c) U B W)
      (SymAnd.collapseStep C L₀.lift (B + 1) B) (by cases layer <;> exact hStep)
      (hB_ge.trans hB_le_B1)
      (fun l hl => hLs_ok l (List.mem_cons_of_mem layer hl))
      (fun L' hL' => by
        have hmem : L' ∈ (layersOfSpec c.2.program m ℓ (layer :: rest)).map SLayer.lift := by
          rw [hL₀_eq, List.map_cons]; exact List.mem_cons_of_mem _ hL'
        have h := hLs_deg L' hmem
        exact ⟨h.1, h.2.1.trans hB_le_B1, fun t => lowDegree_mono hB_le_B1 (h.2.2 t)⟩)
      hf1 hs1 ((Nat.pow_le_pow_right (by decide) hExp_step).trans hU)
    have hM_le : p ^ (B + 1) ≤ 2 ^ ((B_init + 2) * (2 * B) ^ 5 ^ (layer :: rest).length) := by
      have hp2 : p ≤ 2 ^ B_init := hpBi.trans Nat.lt_two_pow_self.le
      have hBsucc : B + 1 ≤ (2 * B) ^ 5 ^ (layer :: rest).length :=
        (show B + 1 ≤ 2 * B by omega).trans
          (Nat.le_self_pow (pow_ne_zero _ (by decide)) (2 * B))
      calc p ^ (B + 1) ≤ (2 ^ B_init) ^ (B + 1) := Nat.pow_le_pow_left hp2 _
        _ = 2 ^ (B_init * (B + 1)) := by rw [← pow_mul]
        _ ≤ 2 ^ ((B_init + 2) * (2 * B) ^ 5 ^ (layer :: rest).length) :=
            Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul (by omega) hBsucc)
    obtain ⟨hRep, hOut, hLen, hMods, hE⟩ := hIH
    have hminB1 : min (5 * B ^ 5) U = B₁ := Nat.min_eq_left hB1_U
    dsimp only
    rw [hL₀_eq, List.map_cons, SymAnd.collapseRun]
    simp only [collapseRunExec, hminB1]
    refine ⟨hRep, fun z => ?_, by simp [hLen], ?_, hE⟩
    · rw [hOut z, SymAnd.collapseStep, SymAnd.ofLowDegree, hL₀_p]
      rfl
    · intro M' hM'
      rcases List.mem_cons.1 hM' with rfl | hM'
      · exact hM_le
      · exact (hMods M' hM').trans (Nat.pow_le_pow_right (by decide) hExp_step)

private theorem restrictAndExpand_spec {m U : ℕ}
    (c : Σ n', Circuit Unbounded.extSignature n' 1)
    (W : List WGate)
    (C : SymAnd (Seed (Nat.log 2 (c.1 + c.2.size) + 1) × Slot c.1 c.2.size m))
    (hW : WListRep c.1 c.2.size m (Nat.log 2 (c.1 + c.2.size) + 1) W C)
    (hU : ∀ e ∈ W, e.2 ≤ U) :
    let inst := restrictAndExpand (buildCtx m c) U W
    inst.n = c.1 ∧
    (∀ g ∈ inst.gates, g.length = c.1) ∧
    (inst.gates.map (gateSet c.1) : Multiset (Finset (Fin c.1))) =
      (C.restrict slotInput).gates := by
  let ℓ := Nat.log 2 (c.1 + c.2.size) + 1
  set ctx := buildCtx m c
  let nSlot := c.1 + c.2.size + c.2.size * ((m + 1) * (m + 1))
  have hctx_n : ctx.n = c.1 := rfl
  have hctx_nSlot : ctx.nSlot = nSlot := by dsimp only [ctx, buildCtx]; rw [Circuit.length_code_fst]
  refine ⟨rfl, ?_, ?_⟩
  · intro g hg
    simp only [restrictAndExpand, List.mem_flatMap, List.mem_filter, List.mem_replicate] at hg
    obtain ⟨_, _, _, rfl⟩ := hg
    simp [hctx_n]
  · dsimp only [restrictAndExpand]
    rw [hctx_n, hctx_nSlot, SymAnd.restrict, ← hW.1, decodeWList]
    have hSlot_mod : ∀ t : Seed ℓ × Slot c.1 c.2.size m,
        (slotToNat t % nSlot < c.1 ↔ (slotInput t).isSome) ∧
        ∀ i : Fin c.1, (slotToNat t % nSlot = i.1 ↔ slotInput t = some i) := by
      rintro ⟨r, s⟩
      rw [slotToNat_mod]
      rcases s with (i | k) | ⟨k, p, i⟩
      · refine ⟨by simp [slotInput, i.isLt], fun j => ?_⟩
        simp [slotInput, Fin.ext_iff]
      · refine ⟨by simp [slotInput], fun j => ?_⟩
        have := j.isLt; simp [slotInput]; omega
      · refine ⟨by simp [slotInput]; omega, fun j => ?_⟩
        have := j.isLt; simp [slotInput]; omega
    have hEntry_eq : ∀ e ∈ W,
        (e.1.all fun a => decide (a % nSlot < c.1)) = true ↔
          ∀ t ∈ decodeIdxSet c.1 c.2.size m ℓ e.1, (slotInput t).isSome := by
      intro e he
      have hlt := (hW.2 e he).2.1
      simp only [List.all_eq_true, decide_eq_true_eq, mem_decodeIdxSet]
      constructor
      · intro h t ht
        exact (hSlot_mod t).1.1 (h (slotToNat t) ht)
      · intro h a ha
        have ht_val := slotToNat_slotEquiv_symm (hlt a ha)
        rw [← ht_val]
        exact (hSlot_mod _).1.2 (h _ (ht_val.symm ▸ ha))
    have hGateSet_eq : ∀ e ∈ W,
        gateSet c.1 ((List.range c.1).map fun i => e.1.any fun a => decide (a % nSlot = i)) =
          (decodeIdxSet c.1 c.2.size m ℓ e.1).biUnion fun t => (slotInput t).toFinset := by
      intro e he
      have hlt := (hW.2 e he).2.1
      ext i
      simp only [gateSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
        Option.mem_toFinset, mem_decodeIdxSet]
      rw [List.getD_eq_getElem _ _ (by simp [i.isLt]), List.getElem_map, List.getElem_range,
        List.any_eq_true]
      simp only [decide_eq_true_eq]
      constructor
      · rintro ⟨a, ha, hmod⟩
        have ht_val := slotToNat_slotEquiv_symm (hlt a ha)
        exact ⟨_, ht_val.symm ▸ ha, (hSlot_mod _).2 i |>.1 (ht_val.symm ▸ hmod)⟩
      · rintro ⟨t, ht, hopt⟩
        exact ⟨slotToNat t, ht, (hSlot_mod t).2 i |>.2 hopt⟩
    have hfilt_rep : ∀ (p : Finset (Seed ℓ × Slot c.1 c.2.size m) → Prop) [DecidablePred p]
        (k : ℕ) (a : Finset (Seed ℓ × Slot c.1 c.2.size m)),
        (Multiset.replicate k a).filter p = if p a then Multiset.replicate k a else 0 := by
      intro p _ k a
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Multiset.replicate_succ, Multiset.filter_cons, ih]
        split_ifs <;> simp
    -- Prove equality by induction on a sublist of `W`
    have hmain : ∀ (Ws : List WGate), (∀ e ∈ Ws, e ∈ W) →
        (((Ws.filter fun e => e.1.all fun a => decide (a % nSlot < c.1)).flatMap fun e =>
            List.replicate (min e.2 U)
              ((List.range c.1).map fun i => e.1.any fun a => decide (a % nSlot = i))).map
          (gateSet c.1) : Multiset (Finset (Fin c.1))) =
        (((Ws : Multiset WGate).bind fun e =>
            Multiset.replicate e.2 (decodeIdxSet c.1 c.2.size m ℓ e.1)).filter
          fun S => ∀ t ∈ S, (slotInput t).isSome).map
          fun S => S.biUnion fun t => (slotInput t).toFinset := by
      intro Ws
      induction Ws with
      | nil => intro _; simp
      | cons e es ih =>
        intro hsub
        have heW : e ∈ W := hsub e List.mem_cons_self
        have hes := ih fun x hx => hsub x (List.mem_cons_of_mem e hx)
        simp only [List.filter_cons]
        have hrhs : (((e :: es : List WGate) : Multiset WGate).bind fun e =>
            Multiset.replicate e.2 (decodeIdxSet c.1 c.2.size m ℓ e.1)) =
            Multiset.replicate e.2 (decodeIdxSet c.1 c.2.size m ℓ e.1) +
            ((es : Multiset WGate).bind fun e =>
              Multiset.replicate e.2 (decodeIdxSet c.1 c.2.size m ℓ e.1)) :=
          Multiset.cons_bind e (es : Multiset WGate) _
        rw [hrhs, Multiset.filter_add, Multiset.map_add, ← hes,
          hfilt_rep (fun S => ∀ t ∈ S, (slotInput t).isSome = true)]
        split_ifs with h1 h2 h3
        · simp only [List.flatMap_cons, List.map_append, ← Multiset.coe_add, Multiset.map_replicate,
            List.map_replicate, Nat.min_eq_left (hU e heW), hGateSet_eq e heW]
          rfl
        · exact absurd ((hEntry_eq e heW).1 h1) h2
        · exact absurd ((hEntry_eq e heW).2 h3) h1
        · simp only [Multiset.map_zero, Multiset.zero_add]
    exact hmain W fun _ h => h

end Equivalence

end Internals

/-! ### 6. Public compiler and Williams's Lemma 4.1 -/

/-- **Executable `ACC⁰ → SYM ∘ AND` compiler** for fixed tower depth `d` and modulus `m`:
computes `(inst, outParam)` representing `ACC0ToSymAnd.compile c.2.program m ℓ d (c.2.outputs 0)`,
where `ℓ = ⌊log₂ (c.1 + c.2.size)⌋ + 1`. -/
def compileSymAndFixed (d m : ℕ) (c : Σ n, Circuit Unbounded.extSignature n 1) :
    SymAndInstance × SymOutParam :=
  compileWithBudget d m (c, 2 ^ budgetExp d m c)

/-- The compiled `SymAndInstance` preserves the input arity `c.1`. -/
theorem compileSymAndFixed_n (d m : ℕ) (c : Σ n, Circuit Unbounded.extSignature n 1) :
    (compileSymAndFixed d m c).1.n = c.1 := by
  unfold compileSymAndFixed compileWithBudget restrictAndExpand buildCtx
  rfl

private theorem towerS_lift_bounds (d : ℕ) {m : ℕ} (hm : 0 < m)
    (c : Σ n, Circuit Unbounded.extSignature n 1) :
    let ℓ := Nat.log 2 (c.1 + c.2.size) + 1
    let B₀ := 3 * ((m + 1) ^ 2 + ℓ + 1)
    (∀ L ∈ (towerS c.2.program m ℓ d).map SLayer.lift,
      L.p.Prime ∧ L.p ≤ B₀ ∧ ∀ t, L.q t ∈ lowDegree ℤ (Seed ℓ × Slot c.1 c.2.size m) B₀) ∧
    Fintype.card (Seed ℓ × Slot c.1 c.2.size m) + 1 ≤ 2 ^ B₀ ∧
    (top ℓ (Sum.inl (c.2.outputs 0) : Slot c.1 c.2.size m)).fanIn ≤ B₀ ∧
    (top ℓ (Sum.inl (c.2.outputs 0) : Slot c.1 c.2.size m)).size ≤ 2 ^ B₀ := by
  set ℓ := Nat.log 2 (c.1 + c.2.size) + 1
  set B₀ := 3 * ((m + 1) ^ 2 + ℓ + 1)
  have hN : c.1 + c.2.size < 2 ^ ℓ := Nat.lt_pow_succ_log_self one_lt_two _
  refine ⟨fun L hL => ?_,
    (card_seed_slot_lt (m := m) hN).trans_le (Nat.pow_le_pow_right (by decide) (by omega)),
    (fanIn_top_le _).trans (by omega), ?_⟩
  · obtain ⟨L₀, hL₀, rfl⟩ := List.mem_map.1 hL
    obtain ⟨hp, hpB, hq⟩ := layer_ok c.2.program hm (mem_macroS_of_mem_towerS c.2.program hL₀)
    have hm1 : m + 1 ≤ (m + 1) ^ 2 := Nat.le_self_pow two_ne_zero _
    exact ⟨hp, by change L₀.p ≤ B₀; omega, SLayer.lift_mem_lowDegree L₀ fun r s =>
      lowDegree_mono (by omega) (hq r s)⟩
  · rw [size_top, BinaryField.card (by omega)]
    exact Nat.pow_le_pow_right (by decide) (by omega)

private theorem compileSymAndFixed_spec (d : ℕ) {m : ℕ} (hm : 0 < m)
    (c : Σ n, Circuit Unbounded.extSignature n 1) :
    let ℓ := Nat.log 2 (c.1 + c.2.size) + 1
    let B₀ := 3 * ((m + 1) ^ 2 + ℓ + 1)
    let res := compileSymAndFixed d m c
    res.1.n = c.1 ∧
    (∀ g ∈ res.1.gates, g.length = c.1) ∧
    (compileSymAndFixed_n d m c ▸ res.1.toSymAnd res.2.eval) =
      ACC0ToSymAnd.compile c.2.program m ℓ d (c.2.outputs 0) ∧
    res.1.gates.length ≤ 2 ^ (2 * B₀) ^ 5 ^ (d * (m + 2)) ∧
    res.2.thresh = 2 ^ (2 * ℓ + 2) ∧
    res.2.mods.length ≤ d * (m + 2) ∧
    ∀ M ∈ res.2.mods, M ≤ 2 ^ ((B₀ + 2) * (2 * B₀) ^ 5 ^ (d * (m + 2))) := by
  let ℓ := Nat.log 2 (c.1 + c.2.size) + 1
  let B₀ := 3 * ((m + 1) ^ 2 + ℓ + 1)
  let U := 2 ^ budgetExp d m c
  have hN : c.1 + c.2.size < 2 ^ ℓ := Nat.lt_pow_succ_log_self one_lt_two _
  have hLs_len : (layerSpec d m).length ≤ d * (m + 2) := by
    rw [length_layerSpec]
    exact Nat.mul_le_mul_left d (by have := length_primes_le m; omega)
  have hU_ge : 2 ^ ((B₀ + 2) * (2 * B₀) ^ 5 ^ (layerSpec d m).length) ≤ U := by
    refine Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ ?_)
    exact Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by decide) hLs_len)
  have hB₀_U : B₀ ≤ U := by
    have h1 : B₀ ≤ (B₀ + 2) * (2 * B₀) ^ 5 ^ (layerSpec d m).length :=
      (by omega : B₀ ≤ B₀ + 2).trans (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero
        (pow_ne_zero _ (by omega))))
    exact (h1.trans Nat.lt_two_pow_self.le).trans hU_ge
  -- Initial `W₀` represents `top ℓ (Sum.inl (c.2.outputs 0))`
  set ctx := buildCtx m c
  have hctx_n : ctx.n = c.1 := rfl
  have hctx_g : ctx.g = c.2.size := Circuit.length_code_fst c.2
  have hctx_w : ctx.w = 2 * ℓ + 2 := by dsimp only [ctx, buildCtx]; rw [Circuit.length_code_fst]
  have hctx_nSeed : ctx.nSeed = 2 ^ (2 * ℓ + 2) := by
    dsimp only [ctx, buildCtx]; rw [Circuit.length_code_fst]
    exact Nat.min_eq_left (two_pow_w_le _).1
  have hctx_nSlot : ctx.nSlot = c.1 + c.2.size + c.2.size * ((m + 1) * (m + 1)) := by
    dsimp only [ctx, buildCtx]; rw [Circuit.length_code_fst]
  have hout_eq : min (c.2.code.2.getD 0 0) (ctx.n + ctx.g) = (c.2.outputs 0).toNat := by
    rw [hctx_n, hctx_g, Circuit.code]
    have h0 : (List.ofFn fun j : Fin 1 => (c.2.outputs j).toNat).getD 0 0 =
        (c.2.outputs 0).toNat := by simp
    rw [h0]
    exact Nat.min_eq_left (Wire.toNat_lt _).le
  set W₀ : List WGate := (List.range ctx.nSeed).map fun r =>
    ([r * ctx.nSlot + min (c.2.code.2.getD 0 0) (ctx.n + ctx.g)], 1)
  have hW₀_rep : WListRep c.1 c.2.size m ℓ W₀
      (top ℓ (Sum.inl (c.2.outputs 0) : Slot c.1 c.2.size m)) := by
    have hhw : 2 * ℓ + 2 ≠ 0 := by omega
    have hslot_r : ∀ (r : ℕ) (hr : r < 2 ^ (2 * ℓ + 2)),
        slotToNat ((BinaryField.equivFin hhw).symm ⟨r, hr⟩,
          (Sum.inl (c.2.outputs 0) : Slot c.1 c.2.size m)) =
        r * (c.1 + c.2.size + c.2.size * ((m + 1) * (m + 1))) + (c.2.outputs 0).toNat := by
      intro r hr
      simp only [slotToNat, slotOffset, Equiv.apply_symm_apply]
      cases c.2.outputs 0 <;> rfl
    refine ⟨?_, ?_⟩
    · rw [decodeWList, top]
      have hbind : ((W₀ : Multiset WGate).bind fun e =>
          Multiset.replicate e.2 (decodeIdxSet c.1 c.2.size m ℓ e.1)) =
          ((List.range (2 ^ (2 * ℓ + 2)) : Multiset ℕ).map fun r =>
            decodeIdxSet c.1 c.2.size m ℓ
              [r * (c.1 + c.2.size + c.2.size * ((m + 1) * (m + 1))) +
                (c.2.outputs 0).toNat]) := by
        simp only [W₀, hctx_nSeed, hctx_nSlot, hout_eq, ← Multiset.map_coe, Multiset.bind_map,
          Multiset.replicate_one, Multiset.bind_singleton]
      rw [hbind]
      have hfin_eq : (List.range (2 ^ (2 * ℓ + 2)) : Multiset ℕ) =
          (Finset.univ : Finset (Seed ℓ)).val.map fun r => (BinaryField.equivFin hhw r).val := by
        refine (Multiset.Nodup.ext (Multiset.coe_nodup.2 List.nodup_range) ?_).2 fun a => ?_
        · exact (Finset.nodup _).map fun _ _ h =>
            (BinaryField.equivFin hhw).injective (Fin.ext h)
        · simp only [Multiset.mem_coe, List.mem_range, Multiset.mem_map, Finset.mem_val,
            Finset.mem_univ, true_and]
          exact ⟨fun ha => ⟨(BinaryField.equivFin hhw).symm ⟨a, ha⟩, by simp⟩,
            fun ⟨r, hr⟩ => hr ▸ (BinaryField.equivFin hhw r).isLt⟩
      rw [hfin_eq, Multiset.map_map]
      refine Multiset.map_congr rfl fun r _ => ?_
      ext t
      simp only [Function.comp_apply, mem_decodeIdxSet, List.mem_singleton, Finset.mem_singleton]
      have hval : (BinaryField.equivFin hhw r).val *
          (c.1 + c.2.size + c.2.size * ((m + 1) * (m + 1))) + (c.2.outputs 0).toNat =
          slotToNat (m := m) (r, (Sum.inl (c.2.outputs 0) : Slot c.1 c.2.size m)) := by
        have := hslot_r (BinaryField.equivFin hhw r).val (BinaryField.equivFin hhw r).isLt
        simpa only [Fin.eta, Equiv.symm_apply_apply] using this.symm
      rw [hval]
      exact ⟨fun h => slotToNat_injective h, fun h => h ▸ rfl⟩
    · intro e he
      simp only [W₀, hctx_nSeed, hctx_nSlot, hout_eq, List.mem_map, List.mem_range] at he
      obtain ⟨r, hr, rfl⟩ := he
      refine ⟨List.nodup_singleton _, fun a ha => ?_, Nat.one_pos⟩
      rw [List.mem_singleton.1 ha, ← hslot_r r hr]
      exact slotToNat_lt _
  -- Check hypotheses of `collapseRunExec_spec`
  obtain ⟨hLs_tower, hT, hf, hs⟩ := towerS_lift_bounds d hm c
  have hLs_ok : ∀ layer ∈ layerSpec d m, (layer.getD 2).Prime ∧ layer.getD 2 ≤ B₀ := by
    intro layer hlayer
    have hmem : layerOfOpt c.2.program m ℓ layer ∈ towerS c.2.program m ℓ d := by
      rw [← layersOfSpec_layerSpec]; exact List.mem_map_of_mem hlayer
    have h := hLs_tower _ (List.mem_map_of_mem hmem)
    cases layer <;> exact ⟨h.1, h.2.1⟩
  have hLs_deg : ∀ L ∈ (layersOfSpec c.2.program m ℓ (layerSpec d m)).map SLayer.lift,
      L.p.Prime ∧ L.p ≤ B₀ ∧ ∀ t, L.q t ∈ lowDegree ℤ (Seed ℓ × Slot c.1 c.2.size m) B₀ := by
    rwa [layersOfSpec_layerSpec]
  obtain ⟨hRep, hOut, hLen, hMods, hE⟩ := collapseRunExec_spec hm c (layerSpec d m) W₀
    (top ℓ (Sum.inl (c.2.outputs 0) : Slot c.1 c.2.size m)) hW₀_rep le_rfl hLs_ok hLs_deg
    hT hf hs hU_ge
  rw [layersOfSpec_layerSpec] at hRep hOut
  set resExec := collapseRunExec m ctx U (layerSpec d m) B₀ W₀
  obtain ⟨hinst_n, hinst_len, hinst_gates⟩ := restrictAndExpand_spec c resExec.1
    (SymAnd.collapseRun (top ℓ (Sum.inl (c.2.outputs 0) : Slot c.1 c.2.size m))
      ((towerS c.2.program m ℓ d).map SLayer.lift) B₀) hRep hE
  have hcompile_eq : compileSymAndFixed d m c =
      (restrictAndExpand ctx U resExec.1, ⟨2 ^ (2 * ℓ + 2), resExec.2⟩) := by
    have hB0_eq : min (3 * ((m + 1) ^ 2 + (Nat.log 2 (ctx.n + ctx.g) + 1) + 1))
        (2 ^ budgetExp d m c) = B₀ := by
      rw [hctx_n, hctx_g]
      exact Nat.min_eq_left hB₀_U
    dsimp only [compileSymAndFixed, compileWithBudget, resExec, W₀, U]
    rw [hB0_eq, hctx_w]
  have hsym_eq : (compileSymAndFixed_n d m c ▸
        (compileSymAndFixed d m c).1.toSymAnd (compileSymAndFixed d m c).2.eval) =
      ACC0ToSymAnd.compile c.2.program m ℓ d (c.2.outputs 0) := by
    have hhw : 2 * ℓ + 2 ≠ 0 := by omega
    have h1 : (compileSymAndFixed d m c).1.gates = (restrictAndExpand ctx U resExec.1).gates :=
      congrArg (fun p => p.1.gates) hcompile_eq
    have h2 : (compileSymAndFixed d m c).2 = ⟨2 ^ (2 * ℓ + 2), resExec.2⟩ :=
      congrArg Prod.snd hcompile_eq
    have hcast : ∀ (inst : SymAndInstance) (out : ℕ → Bool) (hn : inst.n = c.1),
        (hn ▸ inst.toSymAnd out : SymAnd (Fin c.1)) =
          { out := out, gates := inst.gates.map (gateSet c.1) } := by
      rintro ⟨n', gates'⟩ out hn
      dsimp only at hn ⊢
      subst hn
      rfl
    have hg_eq : (((compileSymAndFixed d m c).1.gates.map (gateSet c.1) : Multiset _)) =
        (ACC0ToSymAnd.compile c.2.program m ℓ d (c.2.outputs 0)).gates := by
      rw [h1, ACC0ToSymAnd.compile]; exact hinst_gates
    have ho_eq : (compileSymAndFixed d m c).2.eval =
        (ACC0ToSymAnd.compile c.2.program m ℓ d (c.2.outputs 0)).out := by
      funext z
      rw [h2, ACC0ToSymAnd.compile]
      change SymOutParam.eval ⟨2 ^ (2 * ℓ + 2), resExec.2⟩ z =
        ((top ℓ (Sum.inl (c.2.outputs 0) : Slot c.1 c.2.size m)).collapseRun
          ((towerS c.2.program m ℓ d).map SLayer.lift) B₀).out z
      rw [hOut z]
      simp only [top, SymOutParam.eval, Seed, BinaryField.card hhw]
    rw [hcast (compileSymAndFixed d m c).1 (compileSymAndFixed d m c).2.eval
      (compileSymAndFixed_n d m c)]
    cases hC : ACC0ToSymAnd.compile c.2.program m ℓ d (c.2.outputs 0)
    rw [hC] at hg_eq ho_eq
    exact congrArg₂ SymAnd.mk hg_eq ho_eq
  have hgates_len : (compileSymAndFixed d m c).1.gates.length ≤
      2 ^ (2 * B₀) ^ 5 ^ (d * (m + 2)) := by
    have hcard : (compileSymAndFixed d m c).1.gates.length =
        (ACC0ToSymAnd.compile c.2.program m ℓ d (c.2.outputs 0)).size := by
      have h1 := congrArg Multiset.card hinst_gates
      simp only [Multiset.coe_card, List.length_map] at h1
      rw [congrArg (fun p => p.1.gates) hcompile_eq, h1, ACC0ToSymAnd.compile, SymAnd.size]
    rw [hcard, ACC0ToSymAnd.compile]
    have hlen_t : ((towerS c.2.program m ℓ d).map SLayer.lift).length ≤ d * (m + 2) := by
      rwa [List.length_map, length_towerS, ← length_layerSpec]
    exact (SymAnd.size_restrict_le _ _).trans
      ((SymAnd.size_collapseRun_le _ _ hLs_tower hT hf hs).trans
        (Nat.pow_le_pow_right (by decide)
          (Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by decide) hlen_t))))
  have hg_mem : ∀ g ∈ (compileSymAndFixed d m c).1.gates, g.length = c.1 := by
    rw [congrArg (fun p => p.1.gates) hcompile_eq]; exact hinst_len
  have hth_eq : (compileSymAndFixed d m c).2.thresh = 2 ^ (2 * ℓ + 2) :=
    congrArg (fun p => p.2.thresh) hcompile_eq
  have hmods_eq : (compileSymAndFixed d m c).2.mods = resExec.2 :=
    congrArg (fun p => p.2.mods) hcompile_eq
  refine ⟨rfl, hg_mem, hsym_eq, hgates_len, hth_eq, hmods_eq ▸ hLen ▸ hLs_len, fun M hM => ?_⟩
  rw [hmods_eq] at hM
  exact (hMods M hM).trans (Nat.pow_le_pow_right (by decide)
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega)
      (Nat.pow_le_pow_right (by decide) hLs_len))))

/-- **Exact agreement with `ACC0ToSymAnd.compile`**: for `m > 0`, `compileSymAndFixed d m c`
produces the exact `SYM ∘ AND` circuit `ACC0ToSymAnd.compile c.2.program m ℓ d (c.2.outputs 0)`. -/
theorem compileSymAndFixed_eq_compile (d : ℕ) {m : ℕ} (hm : 0 < m)
    (c : Σ n, Circuit Unbounded.extSignature n 1) :
    (compileSymAndFixed_n d m c ▸
      (compileSymAndFixed d m c).1.toSymAnd (compileSymAndFixed d m c).2.eval) =
      ACC0ToSymAnd.compile c.2.program m (Nat.log 2 (c.1 + c.2.size) + 1) d (c.2.outputs 0) :=
  (compileSymAndFixed_spec d hm c).2.2.1

/-- **Correctness of `compileSymAndFixed`**: for `m > 0` and any circuit `c` of depth at most `d`,
the compiled `SYM ∘ AND` circuit computes `c.2.eval (Unbounded.extInterpretation (modGate m)) · 0`.
-/
theorem eval_compileSymAndFixed (d : ℕ) {m : ℕ} (hm : 0 < m)
    (c : Σ n, Circuit Unbounded.extSignature n 1) (hd : c.2.depth ≤ d) :
    (compileSymAndFixed_n d m c ▸
      (compileSymAndFixed d m c).1.toSymAnd (compileSymAndFixed d m c).2.eval).eval =
      fun x => c.2.eval (Unbounded.extInterpretation (modGate m)) x 0 := by
  rw [compileSymAndFixed_eq_compile d hm c]
  let ℓ := Nat.log 2 (c.1 + c.2.size) + 1
  have hN : c.1 + c.2.size < 2 ^ ℓ := Nat.lt_pow_succ_log_self one_lt_two _
  obtain ⟨hLs, hT, hf, hs⟩ := towerS_lift_bounds d hm c
  funext x
  rw [ACC0ToSymAnd.compile, SymAnd.eval_restrict, SymAnd.eval_collapseRun _ _ hLs hT hf hs,
    eval_top]
  refine decide_majority (fun r => Good c.2.program m x r) _ _ (fun r hr => ?_) ?_
  · rw [SLayer.run_lift]
    simp only [slotInput_elim]
    exact wiresOK_run_towerS c.2.program hm x hr d _ ((c.2.outputDepths_le_depth 0).trans hd)
  · have h1 := card_not_good_le (ℓ := ℓ) c.2.program m x
    have h2 := four_mul_lt_card_seed (ℓ := ℓ) (g := c.2.size) hN
    have h3 : c.2.size * (2 * (c.1 + c.2.size)) = 2 * (c.2.size * (c.1 + c.2.size)) := by ring
    dsimp only [ℓ] at h1 h2
    omega

/-- Explicit shape and size bounds on the output of `compileSymAndFixed d m c`. -/
theorem compileSymAndFixed_bounds (d : ℕ) {m : ℕ} (hm : 0 < m)
    (c : Σ n, Circuit Unbounded.extSignature n 1) :
    let ℓ := Nat.log 2 (c.1 + c.2.size) + 1
    let B₀ := 3 * ((m + 1) ^ 2 + ℓ + 1)
    let res := compileSymAndFixed d m c
    res.1.n = c.1 ∧
    (∀ g ∈ res.1.gates, g.length = c.1) ∧
    res.1.gates.length ≤ 2 ^ (2 * B₀) ^ 5 ^ (d * (m + 2)) ∧
    res.2.thresh = 2 ^ (2 * ℓ + 2) ∧
    res.2.mods.length ≤ d * (m + 2) ∧
    ∀ M ∈ res.2.mods, M ≤ 2 ^ ((B₀ + 2) * (2 * B₀) ^ 5 ^ (d * (m + 2))) := by
  have h := compileSymAndFixed_spec d hm c
  exact ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

/-- **Williams's Lemma 4.1 on multi-tape Turing machines** ([Williams2014], Lemma 4.1, author full
version of 31 July 2012, Section 4, p. 14 and Appendix A): for every fixed depth bound `d` and
modulus `m`, `compileSymAndFixed d m` computes an encoding of the equivalent `SYM ∘ AND`
circuit and its symmetric output gate parameters in time and space
`O((|enc c| + 1) ^ C * 2 ^ (C * (⌊log₂ (c.1 + c.2.size)⌋ + 2) ^ (5 ^ (d * (m + 2)) + 1)))`. -/
theorem computableInO_compileSymAndFixed (d m : ℕ) :
    ∃ C, ComputableInO (compileSymAndFixed d m) (Unbounded.encExtCircuit 1)
      (encPair encSymAndInstance encSymOutParam)
      (fun c => ((Unbounded.encExtCircuit 1 c).length + 1) ^ C *
        2 ^ (C * (Nat.log 2 (c.1 + c.2.size) + 2) ^ (5 ^ (d * (m + 2)) + 1)))
      (fun c => ((Unbounded.encExtCircuit 1 c).length + 1) ^ C *
        2 ^ (C * (Nat.log 2 (c.1 + c.2.size) + 2) ^ (5 ^ (d * (m + 2)) + 1))) := by
  obtain ⟨db, _, hbudDeg⟩ := (computableInPolyTime_budgetExp d m).exists_degree
  obtain ⟨dc, _, hcompDeg⟩ := (computableInPolyTime_compileWithBudget d m).exists_degree
  have hpad : ComputableInO (fun c => (c, 2 ^ budgetExp d m c))
      (Unbounded.encExtCircuit 1) (encPair (Unbounded.encExtCircuit 1) encUnary)
      (fun c => (Unbounded.encExtCircuit 1 c).length +
        (((Unbounded.encExtCircuit 1 c).length + 1) ^ db +
          (budgetExp d m c + 1) * (2 ^ budgetExp d m c + (budgetExp d m c + 1) ^ 2)))
      (fun c => (Unbounded.encExtCircuit 1 c).length +
        (((Unbounded.encExtCircuit 1 c).length + 1) ^ db +
          (2 ^ budgetExp d m c + budgetExp d m c))) :=
    (ComputableInO.id' (encMid := Unbounded.encExtCircuit 1)).prod
      (computableInO_pow2_unary.comp hbudDeg.inO)
  have hfull : ComputableInO (compileSymAndFixed d m) (Unbounded.encExtCircuit 1)
      (encPair encSymAndInstance encSymOutParam) _ _ :=
    (hcompDeg.inO.comp hpad).of_enc_eq fun _ => rfl
  set K := 5 ^ (d * (m + 2))
  set A₀ := 6 * ((m + 1) ^ 2 + 2)
  have hbud_le : ∀ c : Σ n, Circuit Unbounded.extSignature n 1,
      budgetExp d m c ≤ A₀ ^ (K + 1) * (Nat.log 2 (c.1 + c.2.size) + 2) ^ (K + 1) := by
    intro c
    set L := Nat.log 2 (c.1 + c.2.size) + 2
    set B₀ := 3 * ((m + 1) ^ 2 + (Nat.log 2 (c.1 + c.2.size) + 1) + 1)
    have hL2 : 2 ≤ L := by dsimp only [L]; omega
    have h2B0 : 2 * B₀ ≤ A₀ * L := by
      have hmul : A₀ * L = 6 * (m + 1) ^ 2 * L + 12 * L := by dsimp only [A₀]; ring
      have h1 : 6 * (m + 1) ^ 2 ≤ 6 * (m + 1) ^ 2 * L := Nat.le_mul_of_pos_right _ (by omega)
      have h2 : 6 * (Nat.log 2 (c.1 + c.2.size) + 2) = 6 * L := rfl
      dsimp only [B₀]
      omega
    have hB02 : B₀ + 2 ≤ A₀ * L := by
      have : B₀ + 2 ≤ 2 * B₀ := by dsimp only [B₀]; omega
      exact this.trans h2B0
    calc budgetExp d m c = (B₀ + 2) * (2 * B₀) ^ K := rfl
      _ ≤ (A₀ * L) * (A₀ * L) ^ K := Nat.mul_le_mul hB02 (Nat.pow_le_pow_left h2B0 K)
      _ = (A₀ * L) ^ (K + 1) := by rw [pow_succ']
      _ = A₀ ^ (K + 1) * L ^ (K + 1) := Nat.mul_pow _ _ _
  let C := max db 1 + (dc + 2) * (4 * A₀ ^ (K + 1) + 4)
  have hdom : ∀ (c : Σ n, Circuit Unbounded.extSignature n 1) (pad : ℕ),
      pad ≤ (budgetExp d m c + 1) * (2 ^ budgetExp d m c + (budgetExp d m c + 1) ^ 2) →
      (Unbounded.encExtCircuit 1 c).length +
        (((Unbounded.encExtCircuit 1 c).length + 1) ^ db + pad) +
        ((encPair (Unbounded.encExtCircuit 1) encUnary (c, 2 ^ budgetExp d m c)).length + 1) ^ dc ≤
      (4 ^ (dc + 1) + 16) *
        (((Unbounded.encExtCircuit 1 c).length + 1) ^ C *
          2 ^ (C * (Nat.log 2 (c.1 + c.2.size) + 2) ^ (K + 1)) + 1) := by
    intro c pad hpad_le
    set E := (Unbounded.encExtCircuit 1 c).length + 1
    set b := budgetExp d m c
    set L := Nat.log 2 (c.1 + c.2.size) + 2
    set target := E ^ C * 2 ^ (C * L ^ (K + 1))
    have hE1 : 1 ≤ E := Nat.succ_pos _
    have hL1 : 1 ≤ L ^ (K + 1) := Nat.one_le_pow _ _ (by dsimp only [L]; omega)
    have hb_le : b ≤ A₀ ^ (K + 1) * L ^ (K + 1) := hbud_le c
    have hC : dc + 4 * A₀ ^ (K + 1) + dc * A₀ ^ (K + 1) ≤ C := by
      have : (dc + 2) * (4 * A₀ ^ (K + 1) + 4) =
          4 * (dc * A₀ ^ (K + 1)) + 4 * dc + 8 * A₀ ^ (K + 1) + 8 := by ring
      dsimp only [C]; omega
    have hdcC : dc ≤ C := by omega
    have h2b_le : 2 ^ (4 * b) ≤ 2 ^ (C * L ^ (K + 1)) := by
      refine Nat.pow_le_pow_right (by decide) ?_
      calc 4 * b ≤ 4 * (A₀ ^ (K + 1) * L ^ (K + 1)) := Nat.mul_le_mul_left 4 hb_le
        _ = (4 * A₀ ^ (K + 1)) * L ^ (K + 1) := by ring
        _ ≤ C * L ^ (K + 1) := Nat.mul_le_mul_right _ (by omega)
    have hpair_len : (encPair (Unbounded.encExtCircuit 1) encUnary (c, 2 ^ b)).length + 1 ≤
        4 * (E * 2 ^ b) := by
      rw [length_encPair, encUnary_apply, List.length_replicate]
      dsimp only [E]
      have h2b1 : 1 ≤ 2 ^ b := Nat.one_le_pow _ _ (by decide)
      nlinarith
    have hpair_pow : ((encPair (Unbounded.encExtCircuit 1) encUnary (c, 2 ^ b)).length + 1) ^ dc ≤
        4 ^ dc * target := by
      have hEdc : E ^ dc ≤ E ^ C := Nat.pow_le_pow_right hE1 hdcC
      have h2dc : (2 ^ b) ^ dc ≤ 2 ^ (C * L ^ (K + 1)) := by
        rw [← pow_mul]
        refine Nat.pow_le_pow_right (by decide) ?_
        calc b * dc = dc * b := mul_comm _ _
          _ ≤ dc * (A₀ ^ (K + 1) * L ^ (K + 1)) := Nat.mul_le_mul_left _ hb_le
          _ = (dc * A₀ ^ (K + 1)) * L ^ (K + 1) := by ring
          _ ≤ C * L ^ (K + 1) := Nat.mul_le_mul_right _ (by omega)
      calc _ ≤ (4 * (E * 2 ^ b)) ^ dc := Nat.pow_le_pow_left hpair_len dc
        _ = 4 ^ dc * (E ^ dc * (2 ^ b) ^ dc) := by rw [Nat.mul_pow, Nat.mul_pow]
        _ ≤ 4 ^ dc * target := Nat.mul_le_mul_left _ (Nat.mul_le_mul hEdc h2dc)
    have hEdb : E ^ db ≤ target := by
      have h1 : E ^ db ≤ E ^ C := Nat.pow_le_pow_right hE1 (by dsimp only [C]; omega)
      exact h1.trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))
    have hE_t : (Unbounded.encExtCircuit 1 c).length ≤ target :=
      ((Nat.le_succ _).trans (Nat.le_self_pow (by dsimp only [C]; omega) E)).trans
        (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))
    have hb_pow : (b + 1) * (2 ^ b + (b + 1) ^ 2) ≤ 4 * target := by
      have hb2 : b + 1 ≤ 2 ^ b := Nat.lt_two_pow_self
      have hb6 : 4 ≤ b := by
        dsimp only [b, budgetExp]
        have hB : 4 ≤ 3 * ((m + 1) ^ 2 + (Nat.log 2 (c.1 + c.2.size) + 1) + 1) + 2 := by omega
        exact hB.trans (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (pow_ne_zero _ (by omega))))
      calc (b + 1) * (2 ^ b + (b + 1) ^ 2) ≤ 2 ^ b * (2 ^ b + (2 ^ b) ^ 2) := by gcongr
        _ ≤ 2 ^ b * ((2 ^ b) ^ 2 + (2 ^ b) ^ 2) :=
          Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.le_self_pow two_ne_zero _) _)
        _ = 2 ^ (3 * b + 1) := by ring
        _ ≤ 2 ^ (4 * b) := Nat.pow_le_pow_right (by decide) (by omega)
        _ ≤ target := h2b_le.trans (Nat.le_mul_of_pos_left _ (Nat.one_le_pow _ _ hE1))
        _ ≤ 4 * target := Nat.le_mul_of_pos_left _ (by decide)
    have hpad_t : pad ≤ 4 * target := hpad_le.trans hb_pow
    have h4pow_le : 4 ^ dc ≤ 4 ^ (dc + 1) := Nat.pow_le_pow_right (by decide) (Nat.le_succ _)
    have h4pow_pos : 1 ≤ 4 ^ dc := Nat.one_le_pow dc 4 (by decide)
    have htarget_pos : 1 ≤ target := Nat.mul_pos (Nat.one_le_pow _ _ hE1) (Nat.two_pow_pos _)
    calc (Unbounded.encExtCircuit 1 c).length + (E ^ db + pad) +
          ((encPair (Unbounded.encExtCircuit 1) encUnary (c, 2 ^ b)).length + 1) ^ dc
        ≤ target + (target + 4 * target) + 4 ^ dc * target := by
          linarith only [hE_t, hEdb, hpad_t, hpair_pow]
      _ ≤ (4 ^ (dc + 1) + 16) * (target + 1) := by
          nlinarith only [h4pow_le, h4pow_pos, htarget_pos]
  exact ⟨C, hfull.mono (4 ^ (dc + 1) + 16)
    (fun c => hdom c _ le_rfl)
    (fun c => hdom c _ (by nlinarith [Nat.two_pow_pos (budgetExp d m c)]))⟩

/-- **Executable compiler matching `Circuit.toSymAnd`** for all circuits of depth at most `d`:
runs `compileSymAndFixed (min c.2.depth d) m c`. -/
def compileToSymAnd (d m : ℕ) (c : Σ n, Circuit Unbounded.extSignature n 1) :
    SymAndInstance × SymOutParam :=
  compileSymAndFixed (min c.2.depth d) m c

/-- `compileToSymAnd` preserves the input arity `c.1`. -/
theorem compileToSymAnd_n (d m : ℕ) (c : Σ n, Circuit Unbounded.extSignature n 1) :
    (compileToSymAnd d m c).1.n = c.1 :=
  compileSymAndFixed_n (min c.2.depth d) m c

/-- For `m > 0` and `c.2.depth ≤ d`, `compileToSymAnd d m c` equals `c.2.toSymAnd m` identically. -/
theorem compileToSymAnd_eq_toSymAnd (d : ℕ) {m : ℕ} (hm : 0 < m)
    (c : Σ n, Circuit Unbounded.extSignature n 1) (hd : c.2.depth ≤ d) :
    (compileToSymAnd_n d m c ▸
      (compileToSymAnd d m c).1.toSymAnd (compileToSymAnd d m c).2.eval) = c.2.toSymAnd m := by
  have hmin : min c.2.depth d = c.2.depth := Nat.min_eq_left hd
  have haux : ∀ d' (hd' : d' = c.2.depth),
      (compileSymAndFixed_n d' m c ▸
        (compileSymAndFixed d' m c).1.toSymAnd (compileSymAndFixed d' m c).2.eval) =
        c.2.toSymAnd m := by
    rintro _ rfl
    exact compileSymAndFixed_eq_compile c.2.depth hm c
  exact haux (min c.2.depth d) hmin

/-- **Williams's Lemma 4.1 for `Circuit.toSymAnd` on multi-tape Turing machines** ([Williams2014],
Lemma 4.1): for every fixed depth bound `d` and modulus `m`, `compileToSymAnd d m` computes an
encoding of `c.2.toSymAnd m` (for all `c` with `c.2.depth ≤ d`) in time and space
`O((|enc c| + 1) ^ C * 2 ^ (C * (⌊log₂ (c.1 + c.2.size)⌋ + 2) ^ (5 ^ (d * (m + 2)) + 1)))`. -/
theorem computableInO_compileToSymAnd (d m : ℕ) :
    ∃ C, ComputableInO (compileToSymAnd d m) (Unbounded.encExtCircuit 1)
      (encPair encSymAndInstance encSymOutParam)
      (fun c => ((Unbounded.encExtCircuit 1 c).length + 1) ^ C *
        2 ^ (C * (Nat.log 2 (c.1 + c.2.size) + 2) ^ (5 ^ (d * (m + 2)) + 1)))
      (fun c => ((Unbounded.encExtCircuit 1 c).length + 1) ^ C *
        2 ^ (C * (Nat.log 2 (c.1 + c.2.size) + 2) ^ (5 ^ (d * (m + 2)) + 1))) := by
  induction d with
  | zero =>
    obtain ⟨C, hC⟩ := computableInO_compileSymAndFixed 0 m
    refine ⟨C, hC.of_enc_eq fun c => ?_⟩
    simp [compileToSymAnd]
  | succ d ih =>
    obtain ⟨C₁, h₁⟩ := ih
    obtain ⟨C₂, h₂⟩ := computableInO_compileSymAndFixed (d + 1) m
    have hcondP : ComputableInPolyTime
        (fun c : Σ n, Circuit Unbounded.extSignature n 1 => decide (c.2.depth ≤ d))
        (Unbounded.encExtCircuit 1) encBool :=
      ComputableInPolyTime.unary_le' computableInPolyTime_extCircuit_depth
        (ComputableInPolyTime.const d)
    obtain ⟨dc, _, hcondDeg⟩ := hcondP.exists_degree
    have hite := hcondDeg.inO.ite h₁ h₂
    have heq : (fun c : Σ n, Circuit Unbounded.extSignature n 1 =>
        if decide (c.2.depth ≤ d) then compileToSymAnd d m c else compileSymAndFixed (d + 1) m c) =
        compileToSymAnd (d + 1) m := by
      funext c
      simp only [compileToSymAnd]
      by_cases hd : c.2.depth ≤ d
      · simp only [hd, decide_true, ↓reduceIte, Nat.min_eq_left hd,
          Nat.min_eq_left (hd.trans (Nat.le_succ d))]
      · simp only [hd, decide_false, Bool.false_eq_true, ↓reduceIte,
          Nat.min_eq_right (show d + 1 ≤ c.2.depth by omega)]
    rw [heq] at hite
    let C := max (max C₁ C₂) dc
    refine ⟨C, hite.mono 4 (fun c => ?_) (fun c => ?_)⟩
    all_goals
      set E := (Unbounded.encExtCircuit 1 c).length + 1
      set L := Nat.log 2 (c.1 + c.2.size) + 2
      have hE1 : 1 ≤ E := Nat.succ_pos _
      have hK_le : 5 ^ (d * (m + 2)) + 1 ≤ 5 ^ ((d + 1) * (m + 2)) + 1 :=
        Nat.add_le_add_right
          (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (Nat.le_succ d))) 1
      have hL_le : L ^ (5 ^ (d * (m + 2)) + 1) ≤ L ^ (5 ^ ((d + 1) * (m + 2)) + 1) :=
        Nat.pow_le_pow_right (by dsimp only [L]; omega) hK_le
      have hTarget_dc : E ^ dc ≤ E ^ C * 2 ^ (C * L ^ (5 ^ ((d + 1) * (m + 2)) + 1)) :=
        (Nat.pow_le_pow_right hE1 (le_max_right _ _)).trans
          (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))
      have hTarget_1 : E ^ C₁ * 2 ^ (C₁ * L ^ (5 ^ (d * (m + 2)) + 1)) ≤
          E ^ C * 2 ^ (C * L ^ (5 ^ ((d + 1) * (m + 2)) + 1)) :=
        Nat.mul_le_mul (Nat.pow_le_pow_right hE1 ((le_max_left _ _).trans (le_max_left _ _)))
          (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul
            ((le_max_left _ _).trans (le_max_left _ _)) hL_le))
      have hTarget_2 : E ^ C₂ * 2 ^ (C₂ * L ^ (5 ^ ((d + 1) * (m + 2)) + 1)) ≤
          E ^ C * 2 ^ (C * L ^ (5 ^ ((d + 1) * (m + 2)) + 1)) :=
        Nat.mul_le_mul (Nat.pow_le_pow_right hE1 ((le_max_right _ _).trans (le_max_left _ _)))
          (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _
            ((le_max_right _ _).trans (le_max_left _ _))))
      split_ifs <;> omega

end Cslib.Circuits.Boolean.SymAnd
