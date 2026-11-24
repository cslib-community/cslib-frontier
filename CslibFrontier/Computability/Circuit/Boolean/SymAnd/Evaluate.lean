/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.Yates
public import CslibFrontier.Computability.Circuit.Boolean.SymAnd
public import CslibFrontier.Computability.Complexity.FineGrained
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.StreamFold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Subtraction
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.StreamFold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.BinarySizeFacts
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCountedIteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCombinators
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Basic
import CslibFrontier.Tactic.EncLen

/-!
# Evaluating a `SYM ∘ AND` circuit on all inputs

Williams's **Evaluation Lemma** ([Williams2014], Lemma 4.2, numbered as in the author's full
version of 31 July 2012): a `SYM ∘ AND` circuit with `s` AND gates on `n` inputs can be evaluated on
all `2 ^ n` inputs in `(2 ^ n + poly(s)) · poly(n)` time, given a `poly(s)`-time evaluator for its
symmetric gate. This file formalizes the source's first proof (dynamic programming, after
Björklund), both as a pure Lean algorithm (`multiplicity`, `truthTable`) and on multi-tape Turing
machines (`Turing.MultiTapeTM.ComputableInO`).

Let `f S` be the number of AND gates reading exactly the positions `S` (`gateMultiplicity`). The
number of AND gates satisfied by the input with true positions `T` is
`g T = ∑_{S ⊆ T} f S`, the zeta transform of `f` (`count_eq_subsetZeta`).

## Source-to-Lean mapping

* The source's `SYM⁺` circuit `C''` with `s''` AND gates `G_j ⊆ [n]` is a
  `C : Circuits.Boolean.SymAnd (Fin n)` with `C.size = s`. On multi-tape Turing machines, instances
  are given by `SymAndInstance` (`encSymAndInstance`), pairing the unary input arity `n` with the
  framed list of characteristic bit-vector gate masks (`encList encBits`).
* The pure specification `truthTable gates out` builds the multiplicity vector `multiplicity gates`,
  evaluates `subsetZeta` at each cell `maskSet n k`, and reads `out`.
* The `k`-th entry of `SymAndInstance.truthTableList` is the output at
  `(BitString.equivFin n).symm k` (coordinate `0` least significant bit).
* The multi-tape Turing-machine realization (`computableInO_truthTableList_of_computableInO` and
  `computableInO_truthTableList`) proceeds in five streaming/radix-sort stages:
  1. Generate all `2 ^ n` input masks in LSB-first order by `n` doubling passes, normalize each gate
     to length `n`, radix-sort the tagged union by LSB bits `0, …, n - 1`, and stream-count gate
     multiplicities `[c₀, …, c_{2^n - 1}]`.
  2. Run `n` cyclic butterfly passes of Yates's fast zeta transform over `List ℕ`, producing
     `[g₀, …, g_{2^n - 1}]` where `g_k ≤ s`.
  3. Tabulate `(j, out j)` for `j = 0, …, s` using the supplied binary-input Turing-machine
     evaluator `out`.
  4. Radix-sort the tagged table and `(g_k, k)` queries by the `Nat.size s` bits of the count, and
     stream-propagate `out g_k` onto `(Nat.bits k, out g_k)`.
  5. Radix-sort `(Nat.bits k, out g_k)` by bits `0, …, n - 1` and strip keys to emit the truth
     table `[out g₀, …, out g_{2^n - 1}]`.
* The source's hypothesis `s ≤ 2^{0.1 n}` is not assumed: in Proof 1 it only absorbs `s · poly(n)`
  into `O(2 ^ n)`, and `(2 ^ n + poly(|enc x|)) · poly(n)` keeps the circuit-size term explicit.
  Any `2 ^ n · (log₂ s + 2)^d` binary-length factors are absorbed unconditionally via
  `two_pow_mul_log2_pow_le`. On well-formed gate masks of length at most `n`,
  `(encSymAndInstance x).length ≤ (s + 2) * (2 * n + 2)` (`length_encSymAndInstance_le`).

## Main definitions

* `Cslib.Circuits.Boolean.SymAnd.gateMultiplicity`: the number of AND gates reading exactly `S`.
* `Cslib.Circuits.Boolean.SymAnd.multiplicity`, `.truthTable`: pure multiplicity and truth-table
  evaluation.
* `Cslib.Circuits.Boolean.SymAnd.SymAndInstance`, `.encSymAndInstance`: circuit instance and
  binary-tape encoding.
* `Cslib.Circuits.Boolean.SymAnd.SymAndInstance.truthTableList`: the truth table as a `List Bool`.

## Main results

* `Cslib.Circuits.Boolean.SymAnd.count_eq_subsetZeta`: the AND count is a zeta transform.
* `Cslib.Circuits.Boolean.SymAnd.truthTable_eq`: correctness of pure `truthTable`.
* `Cslib.Circuits.Boolean.SymAnd.computableInO_truthTableList_of_computableInO`: Williams's
  Evaluation Lemma on multi-tape Turing machines, parametric in a `ComputableInO` evaluator `out`.
* `Cslib.Circuits.Boolean.SymAnd.computableInO_truthTableList`: Williams's Evaluation Lemma for any
  polynomial-time symmetric gate evaluator `out`, in time and space
  `O((2 ^ n + (|enc x| + 1) ^ c) * (n + 1) ^ c)`.

## References

* [A. Björklund, T. Husfeldt, M. Koivisto, *Set Partitioning via
  Inclusion–Exclusion*][BjorklundHusfeldtKoivisto2009]
* [R. Williams, *Nonuniform ACC Circuit Lower Bounds*][Williams2014]
-/

public section

namespace Cslib.Circuits.Boolean.SymAnd

open Finset Cslib.BitString Cslib.Algorithms.Lean Cslib.Algorithms.Lean.Yates
open Turing.MultiTapeTM

section Count

variable {ι : Type*} [DecidableEq ι]

/-- The number of AND gates of `C` reading exactly the positions `S`. -/
@[expose] def gateMultiplicity (C : SymAnd ι) (S : Finset ι) : ℕ :=
  C.gates.count S

/-- **The AND count is a zeta transform**: the number of AND gates satisfied by the input with
true positions `T` is `∑_{S ⊆ T} gateMultiplicity C S`. -/
theorem count_eq_subsetZeta (C : SymAnd ι) (T : Finset ι) :
    C.count (fun i => decide (i ∈ T)) = subsetZeta C.gateMultiplicity T := by
  obtain ⟨gates, out⟩ := C
  simp only [count, subsetZeta, gateMultiplicity]
  induction gates using Multiset.induction_on with
  | empty => simp
  | cons G gs ih =>
    rw [Multiset.countP_cons, ih]
    simp only [Multiset.count_cons, sum_add_distrib, sum_ite_eq', mem_powerset]
    congr 1
    by_cases h : G ⊆ T
    · rw [ite_eq_left h, ite_eq_left fun i hi => decide_eq_true (h hi)]
    · rw [ite_eq_right h, ite_eq_right fun hG => h fun i hi => of_decide_eq_true (hG i hi)]

/-- The AND count at an arbitrary input, over finitely many positions, as a zeta transform. -/
theorem count_eq_subsetZeta_filter [Fintype ι] (C : SymAnd ι) (x : ι → Bool) :
    C.count x = subsetZeta C.gateMultiplicity (univ.filter fun i => x i = true) := by
  rw [← count_eq_subsetZeta]
  congr 1 with i : 1
  cases h : x i <;> simp [h]

end Count

section Pure

variable {n : ℕ}

/-- The table of multiplicities: start from `2 ^ n` zeros, then for each AND gate increment the
cell of its position set. -/
@[expose] def multiplicity (gates : List (Finset (Fin n))) : Vector ℕ (2 ^ n) :=
  gates.foldl (fun t G =>
    t.set (maskIndex G : ℕ) (t[(maskIndex G : ℕ)] + 1) (maskIndex G).isLt)
    (Vector.replicate (2 ^ n) 0)

private theorem getElem_foldl_multiplicity (gates : List (Finset (Fin n)))
    (t : Vector ℕ (2 ^ n)) (k : ℕ) (hk : k < 2 ^ n) :
    (gates.foldl (fun t G =>
      t.set (maskIndex G : ℕ) (t[(maskIndex G : ℕ)] + 1) (maskIndex G).isLt) t)[k] =
      t[k] + gates.count (maskSet n k) := by
  induction gates generalizing t with
  | nil => simp
  | cons G gs ih =>
    rw [List.foldl_cons, ih, List.count_cons, Vector.getElem_set]
    by_cases h : (maskIndex G : ℕ) = k
    · have hG : G = maskSet n k := by rw [← h, maskSet_maskIndex]
      rw [ite_eq_left h, ite_eq_left (beq_iff_eq.mpr hG)]
      subst h
      omega
    · have hG : G ≠ maskSet n k := by
        rintro rfl
        exact h (congrArg Fin.val (maskIndex_maskSet ⟨k, hk⟩))
      rw [ite_eq_right h, ite_eq_right fun h' => hG (beq_iff_eq.mp h'), add_zero]

/-- The cell of `S` in the table of multiplicities holds the number of gates reading `S`. -/
theorem getElem_multiplicity (gates : List (Finset (Fin n))) (k : ℕ) (hk : k < 2 ^ n) :
    (multiplicity gates)[k] = gates.count (maskSet n k) := by
  simp [multiplicity, getElem_foldl_multiplicity]

/-- Pure evaluation of the truth table: compute gate multiplicities, take their zeta transform at
each input mask, and evaluate `out` at every cell. -/
@[expose] def truthTable (gates : List (Finset (Fin n))) (out : ℕ → Bool) :
    Vector Bool (2 ^ n) :=
  let m := multiplicity gates
  Vector.ofFn fun k => out (subsetZeta (fun T => m[(maskIndex T : ℕ)]) (maskSet n k.1))

/-- **Cell correctness of `truthTable`**: entry `k` agrees with `C.eval` at
`(BitString.equivFin n).symm k`. -/
theorem getElem_truthTable (C : SymAnd (Fin n)) (gates : List (Finset (Fin n)))
    (hgates : (gates : Multiset (Finset (Fin n))) = C.gates) (out : ℕ → Bool)
    (hout : ∀ j ≤ C.size, out j = C.out j) (k : Fin (2 ^ n)) :
    (truthTable gates out)[k.1] = C.eval ((BitString.equivFin n).symm k) := by
  have hm : ∀ T : Finset (Fin n),
      (multiplicity gates)[(maskIndex T : ℕ)] = C.gateMultiplicity T := fun T => by
    rw [getElem_multiplicity, maskSet_maskIndex, gateMultiplicity, ← hgates, Multiset.coe_count]
  have hg : subsetZeta (fun T => (multiplicity gates)[(maskIndex T : ℕ)]) (maskSet n k.1) =
      C.count ((BitString.equivFin n).symm k) := by
    rw [equivFin_symm_eq_decide_mem_maskSet, count_eq_subsetZeta]
    exact Finset.sum_congr rfl fun T _ => hm T
  simp only [truthTable, Vector.getElem_ofFn, hg]
  exact hout _ (C.count_le_size _)

/-- **Correctness of `truthTable`**: when `gates` lists `C.gates` and `out` agrees with `C.out` on
`0, …, C.size`, `truthTable gates out` equals the truth table of `C` in the order of
`BitString.equivFin`. -/
theorem truthTable_eq (C : SymAnd (Fin n)) (gates : List (Finset (Fin n)))
    (hgates : (gates : Multiset (Finset (Fin n))) = C.gates) (out : ℕ → Bool)
    (hout : ∀ j ≤ C.size, out j = C.out j) :
    truthTable gates out = Vector.ofFn fun k => C.eval ((BitString.equivFin n).symm k) := by
  ext k hk
  rw [Vector.getElem_ofFn]
  exact getElem_truthTable C gates hgates out hout ⟨k, hk⟩

end Pure

section InstanceEncoding

/-- Input instance for evaluating a `SYM ∘ AND` circuit on all `2 ^ n` inputs: the unary input
arity `n` together with the list of AND gates, each given as a characteristic bit vector `g` whose
`i`-th entry is `true` iff input `i` feeds into the gate (`g.getD i false = true`). -/
structure SymAndInstance where
  /-- Number of Boolean inputs to the circuit. -/
  n : ℕ
  /-- List of AND gates, each represented as a bit vector of positive input positions. -/
  gates : List (List Bool)
  deriving DecidableEq

/-- Binary-tape encoding of `SymAndInstance`: framed unary arity `n` (`encUnary`) followed by the
framed list of raw bit-vector gate masks (`encList encBits`). -/
enc_structure encSymAndInstance : SymAndInstance where
  n : encUnary, gates : (encList encBits)

/-- The set of input positions `i : Fin n` read by a bit-vector gate mask `g`. -/
@[expose] def gateSet (n : ℕ) (g : List Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i : Fin n => g.getD i.1 false = true

/-- The `SYM ∘ AND` circuit represented by `x : SymAndInstance` and symmetric gate `out`. -/
@[expose] def SymAndInstance.toSymAnd (x : SymAndInstance) (out : ℕ → Bool) :
    SymAnd (Fin x.n) where
  gates := (x.gates.map (gateSet x.n) : Multiset (Finset (Fin x.n)))
  out := out

/-- The truth table of `x.toSymAnd out`, listed in the `BitString.equivFin x.n` order
`0, …, 2 ^ x.n - 1`. -/
@[expose] def SymAndInstance.truthTableList (x : SymAndInstance) (out : ℕ → Bool) : List Bool :=
  List.ofFn fun k : Fin (2 ^ x.n) => (x.toSymAnd out).eval ((BitString.equivFin x.n).symm k)

/-- Agreement between the list truth table `x.truthTableList out` and pure `truthTable`. -/
theorem SymAndInstance.truthTableList_eq_truthTable (x : SymAndInstance) (out : ℕ → Bool) :
    x.truthTableList out = (truthTable (x.gates.map (gateSet x.n)) out).toList := by
  rw [truthTable_eq (x.toSymAnd out) (x.gates.map (gateSet x.n)) rfl out (fun _ _ => rfl)]
  refine List.ext_getElem (by simp [SymAndInstance.truthTableList]) fun k hk1 hk2 => ?_
  simp [SymAndInstance.truthTableList]

/-- Well-formed gate masks of length at most `x.n` give an instance encoding of length
`O((s + 1) * (n + 1))`. -/
theorem length_encSymAndInstance_le (x : SymAndInstance)
    (hgates : ∀ g ∈ x.gates, g.length ≤ x.n) :
    (encSymAndInstance x).length ≤ (x.gates.length + 2) * (2 * x.n + 2) := by
  have hlist : (encList encBits x.gates).length ≤ x.gates.length * (2 * x.n + 1) :=
    Turing.MultiTapeTM.length_encList_le encBits x.gates fun g hg => by
      simpa [encBits_apply] using hgates g hg
  rw [encSymAndInstance_apply]
  have hn : (encUnary x.n).length = x.n := by simp [encUnary_apply]
  rw [length_encPair, hn]
  nlinarith

end InstanceEncoding

section MultiTapeTM

open Turing.MultiTapeTM.ComputableInPolyTime

/-! ### Streaming list-pass combinator and generic LSB radix sort -/

/-- List-level form of `count_eq_subsetZeta`: `subsetZeta` of `l.count` equals
`l.countP (· ⊆ S)`. -/
private theorem subsetZeta_listCount_eq_countP {n : ℕ} (l : List (Finset (Fin n)))
    (S : Finset (Fin n)) :
    subsetZeta (fun T => l.count T) S = l.countP fun T => decide (T ⊆ S) := by
  have h := (count_eq_subsetZeta ⟨↑l, fun _ => false⟩ S).symm
  have hg : ({ gates := ↑l, out := fun _ => false } : SymAnd (Fin n)).gateMultiplicity =
      fun T => l.count T := by
    funext T; simp [gateMultiplicity]
  rw [hg] at h
  rw [h]
  simp [SymAnd.count, Finset.subset_iff]

/-- Integer value of the first `b` bits of `bs` (padded on the right with `false`). -/
private def evalBits : ℕ → List Bool → ℕ
  | 0, _ => 0
  | b + 1, bs => evalBits b bs + if bs.getD b false then 2 ^ b else 0

private theorem evalBits_lt (b : ℕ) (bs : List Bool) : evalBits b bs < 2 ^ b := by
  induction b with
  | zero => simp [evalBits]
  | succ b ih =>
    rw [evalBits, pow_succ]
    split_ifs <;> omega

private theorem testBit_evalBits (b : ℕ) (bs : List Bool) (i : ℕ) :
    (evalBits b bs).testBit i = (decide (i < b) && bs.getD i false) := by
  induction b with
  | zero => simp [evalBits]
  | succ b ih =>
    rw [evalBits]
    by_cases hbit : bs.getD b false = true
    · simp only [hbit, ↓reduceIte]
      rcases lt_trichotomy i b with hlt | heq | hgt
      · have hmod : 2 ^ b = 2 ^ i * 2 ^ (b - i) := by rw [← pow_add, Nat.add_sub_of_le hlt.le]
        have hpos : 0 < b - i := by omega
        have heven : (2 ^ (b - i)) % 2 = 0 := by
          rw [← Nat.sub_add_cancel hpos, pow_succ]; omega
        rw [Nat.testBit_eq_decide_div_mod_eq] at ih ⊢
        have hdiv : (evalBits b bs + 2 ^ b) / 2 ^ i = evalBits b bs / 2 ^ i + 2 ^ (b - i) := by
          rw [hmod, Nat.add_mul_div_left _ _ (Nat.two_pow_pos i)]
        rw [hdiv, Nat.add_mod, heven, Nat.add_zero, Nat.mod_mod]
        simp only [decide_eq_true (by omega : i < b + 1), Bool.true_and]
        simpa [hlt] using ih
      · subst heq
        have hlt' := evalBits_lt i bs
        have hdiv : (evalBits i bs + 2 ^ i) / 2 ^ i = 1 := by
          rw [Nat.add_div_right _ (Nat.two_pow_pos i), Nat.div_eq_of_lt hlt']
        rw [Nat.testBit_eq_decide_div_mod_eq, hdiv]
        have hbi : bs[i]?.getD false = true := by simpa [List.getD_eq_getElem?_getD] using hbit
        simp [hbi]
      · have hlt' : evalBits b bs + 2 ^ b < 2 ^ i := by
          have := evalBits_lt b bs
          calc evalBits b bs + 2 ^ b < 2 ^ (b + 1) := by rw [pow_succ]; omega
            _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) hgt
        rw [Nat.testBit_lt_two_pow hlt']
        simp [show ¬ i < b + 1 by omega]
    · have hf : bs.getD b false = false := by cases hm : bs.getD b false <;> simp_all
      simp only [hf, Bool.false_eq_true, ↓reduceIte, add_zero, ih]
      by_cases hi : i < b
      · simp [hi, show i < b + 1 by omega]
      · have heq : ¬ i < b + 1 ∨ i = b := by omega
        rcases heq with h | rfl
        · simp [hi, h]
        · simpa [List.getD_eq_getElem?_getD] using hf

private theorem evalBits_bits (b k : ℕ) (hk : k < 2 ^ b) : evalBits b (Nat.bits k) = k := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  rw [testBit_evalBits, BinarySub.bits_getD]
  by_cases hi : i < b
  · simp [hi]
  · simp only [hi, decide_false, Bool.false_and]
    have hle : 2 ^ b ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_lt_two_pow (hk.trans_le hle)).symm

private theorem evalBits_of_len_eq {b : ℕ} {bs₁ bs₂ : List Bool}
    (h1 : bs₁.length = b) (h2 : bs₂.length = b) (heq : evalBits b bs₁ = evalBits b bs₂) :
    bs₁ = bs₂ := by
  refine List.ext_getElem (h1.trans h2.symm) fun i hi1 hi2 => ?_
  have hib : i < b := by omega
  have ht := congrArg (fun n => n.testBit i) heq
  simp only [testBit_evalBits, hib, decide_true, Bool.true_and,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi1, List.getElem?_eq_getElem hi2,
    Option.getD_some] at ht
  exact ht

/-! ### Generic LSB radix sort on `(List Bool × α)` -/

private def radixPass {α : Type*} (i : ℕ) (L : List (List Bool × α)) :
    List (List Bool × α) :=
  L.filter (fun p => !p.1.getD i false) ++ L.filter (fun p => p.1.getD i false)

private def radixStep {α : Type*} (q : ℕ × List (List Bool × α)) :
    ℕ × List (List Bool × α) :=
  (q.1 + 1, radixPass q.1 q.2)

private def radixSortLSB {α : Type*} (b : ℕ) (L : List (List Bool × α)) :
    List (List Bool × α) :=
  (radixStep^[b] (0, L)).2

private theorem fst_iterate_radixStep {α : Type*} (i k : ℕ) (L : List (List Bool × α)) :
    (radixStep^[k] (i, L)).1 = i + k := by
  induction k generalizing i L with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, radixStep, ih]
    omega

private theorem radixSortLSB_succ {α : Type*} (b : ℕ) (L : List (List Bool × α)) :
    radixSortLSB (b + 1) L = radixPass b (radixSortLSB b L) := by
  rw [radixSortLSB, Function.iterate_succ_apply']
  simp only [radixStep, fst_iterate_radixStep, Nat.zero_add, radixSortLSB]

private theorem radixSortLSB_eq {α : Type*} (b : ℕ) (L : List (List Bool × α)) :
    radixSortLSB b L =
      (List.range (2 ^ b)).flatMap fun k => L.filter (fun p => evalBits b p.1 == k) := by
  induction b with
  | zero => simp [radixSortLSB, evalBits]
  | succ b ih =>
    rw [radixSortLSB_succ, ih, radixPass, pow_succ, Nat.mul_two, List.range_add,
      List.flatMap_append, List.flatMap_map]
    simp only [List.filter_flatMap, List.filter_filter]
    congr 1
    · refine List.flatMap_congr fun k hk => ?_
      have hk_lt : k < 2 ^ b := List.mem_range.1 hk
      refine List.filter_congr fun p _ => ?_
      rw [evalBits]
      by_cases hbit : p.1.getD b false = true
      · have hne : evalBits b p.1 + 2 ^ b ≠ k := by omega
        simp only [List.getD_eq_getElem?_getD] at hbit ⊢
        simp [hbit, hne]
      · have hf : p.1.getD b false = false := by cases hm : p.1.getD b false <;> simp_all
        simp only [List.getD_eq_getElem?_getD] at hf ⊢
        simp [hf]
    · refine List.flatMap_congr fun k hk => ?_
      have hk_lt : k < 2 ^ b := List.mem_range.1 hk
      refine List.filter_congr fun p _ => ?_
      rw [evalBits]
      by_cases hbit : p.1.getD b false = true
      · simp only [List.getD_eq_getElem?_getD] at hbit ⊢
        simp [hbit, Nat.add_comm (2 ^ b) k]
      · have hf : p.1.getD b false = false := by cases hm : p.1.getD b false <;> simp_all
        have hlt := evalBits_lt b p.1
        have hne : evalBits b p.1 ≠ 2 ^ b + k := by omega
        simp only [List.getD_eq_getElem?_getD] at hf ⊢
        simp [hf, hne]

private theorem length_radixPass {α : Type*} (i : ℕ) (L : List (List Bool × α)) :
    (radixPass i L).length = L.length := by
  rw [radixPass, List.length_append]
  induction L with
  | nil => simp
  | cons a t ih =>
    cases h : a.1.getD i false <;>
      simp only [List.filter_cons, h, Bool.not_false, Bool.not_true, ↓reduceIte,
        Bool.false_eq_true, List.length_cons] <;> omega

private theorem length_radixStep {α : Type*} (k i : ℕ) (L : List (List Bool × α)) :
    (radixStep^[k] (i, L)).2.length = L.length := by
  induction k generalizing i L with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, radixStep, ih, length_radixPass]

private theorem mem_radixPass_iff {α : Type*} {i : ℕ} {L : List (List Bool × α)}
    {p : List Bool × α} : p ∈ radixPass i L ↔ p ∈ L := by
  simp only [radixPass, List.mem_append, List.mem_filter]
  constructor
  · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
  · intro hp
    cases h : p.1.getD i false
    · exact Or.inl ⟨hp, by simp⟩
    · exact Or.inr ⟨hp, by simp⟩

private theorem mem_radixStep_iff {α : Type*} {k i : ℕ} {L : List (List Bool × α)}
    {p : List Bool × α} : p ∈ (radixStep^[k] (i, L)).2 ↔ p ∈ L := by
  induction k generalizing i L with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, radixStep, ih, mem_radixPass_iff]

private theorem radixFilter_streamEmit {α : Type} (encα : α ↪ List Bool)
    (bTarget : Bool) (i : ℕ) (L : List (List Bool × α)) :
    encList (encPair encBits encα) (L.filter fun p => p.1.getD i false == bTarget) =
      streamEmit (fun q : (ℕ × Bool) × (List Bool × α) => q.1)
        (fun q => encList (encPair encBits encα)
          (if q.2.1.getD q.1.1 false == q.1.2 then [q.2] else []))
        (i, bTarget) L := by
  induction L with
  | nil => rfl
  | cons a t ih =>
    rw [List.filter_cons, streamEmit]
    by_cases h : (a.1.getD i false == bTarget) = true
    · simp only [h, ↓reduceIte, encList_cons, encList_nil, List.append_nil, ih]
    · have hf : (a.1.getD i false == bTarget) = false := by
        cases hm : (a.1.getD i false == bTarget) <;> simp_all
      simp only [hf, Bool.false_eq_true, ↓reduceIte, encList_nil, List.nil_append, ih]

private theorem computableInO_radixPass {α : Type} (encα : α ↪ List Bool) :
    ∃ d, ComputableInO (fun q : ℕ × List (List Bool × α) => radixPass q.1 q.2)
      (encPair encNat (encList (encPair encBits encα))) (encList (encPair encBits encα))
      (fun q => (encList (encPair encBits encα) q.2).length +
        (q.2.length + 1) * ((encNat q.1).length +
          listMax (fun p => (encPair encBits encα p).length) q.2 + 1) ^ d)
      (fun q => (encList (encPair encBits encα) q.2).length +
        ((encNat q.1).length +
          listMax (fun p => (encPair encBits encα p).length) q.2 + 1) ^ d) := by
  let encElem := encPair encBits encα
  let encS := encPair encNat encBool
  have hnext : ComputableInPolyTime (fun p : (ℕ × Bool) × (List Bool × α) => p.1)
      (encPair encS encElem) encS := by fun_prop
  have hemit : ComputableInPolyTime
      (fun p : (ℕ × Bool) × (List Bool × α) =>
        if p.2.1.getD (min p.2.1.length p.1.1) false == p.1.2 then [p.2] else [])
      (encPair encS encElem) (encList encElem) := by
    have hkey : ComputableInPolyTime
        (fun p : (ℕ × Bool) × (List Bool × α) => p.2.1) (encPair encS encElem) encBits := by
      fun_prop
    have hidx : ComputableInPolyTime
        (fun p : (ℕ × Bool) × (List Bool × α) => min p.2.1.length p.1.1)
        (encPair encS encElem) encUnary :=
      binary_min_unary' ((length encBool).comp hkey) (by fun_prop)
    have hbit : ComputableInPolyTime
        (fun p : (ℕ × Bool) × (List Bool × α) =>
          p.2.1.getD (min p.2.1.length p.1.1) false == p.1.2)
        (encPair encS encElem) encBool :=
      (bitsGetDWithInput hkey hidx false).beq (by fun_prop)
    exact hbit.ite (cons' (by fun_prop) (const [])) (const [])
  have hemit_eq : (fun p : (ℕ × Bool) × (List Bool × α) =>
        if p.2.1.getD p.1.1 false == p.1.2 then [p.2] else []) =
      (fun p : (ℕ × Bool) × (List Bool × α) =>
        if p.2.1.getD (min p.2.1.length p.1.1) false == p.1.2 then [p.2] else []) := by
    funext ⟨⟨i, b⟩, ⟨bs, a⟩⟩
    by_cases hi : i < bs.length
    · rw [Nat.min_eq_right hi.le]
    · have h1 : bs.getD i false = false := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
        rfl
      have h2 : bs.getD (min bs.length i) false = false := by
        rw [Nat.min_eq_left (by omega), List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (le_refl _)]
        rfl
      rw [h1, h2]
  rw [← hemit_eq] at hemit
  obtain ⟨c, d, h⟩ := ComputableInTimeAndSpace.streamFold_pair_list
    (encA := encElem) (encS := encS) (encB := encElem)
    (encIn := encPair encS (encList encElem))
    (init := Prod.fst) (elems := Prod.snd) (fun _ => rfl) hnext hemit
    (g := fun r : (ℕ × Bool) × List (List Bool × α) =>
      r.2.filter fun p => p.1.getD r.1.1 false == r.1.2)
    (fun r => radixFilter_streamEmit encα r.1.2 r.1.1 r.2)
    (lMax := fun r => 2 * (encNat r.1.1).length + listMax (fun p => (encElem p).length) r.2 + 4)
    (fun r j _ => by
      have htake : ∀ (xs : List (List Bool × α)) (s : ℕ × Bool),
          xs.foldl (fun (q : ℕ × Bool) (_ : List Bool × α) => q) s = s := fun xs s => by
        induction xs with
        | nil => rfl
        | cons _ _ ih => exact ih
      have hst : streamState r.1 (fun q : (ℕ × Bool) × (List Bool × α) => q.1) r.2 j = r.1 :=
        htake (r.2.take j) r.1
      change (encPair encNat encBool (streamState r.1 _ r.2 j)).length ≤ _
      rw [hst, length_encPair]
      have hb : (encBool r.1.2).length ≤ 2 := by cases r.1.2 <;> simp
      omega)
    (fun r j hj => (le_listMax (f := fun p => (encElem p).length) (List.getElem_mem hj)).trans
      (by omega))
  have hlen_filter : ∀ (b : Bool) (i : ℕ) (L : List (List Bool × α)),
      (encList encElem (L.filter fun p => p.1.getD i false == b)).length ≤
        (encList encElem L).length := fun b i L => by
    induction L with
    | nil => simp
    | cons a t ih =>
      cases h' : (a.1.getD i false == b) <;>
        simp only [List.filter_cons, h', Bool.false_eq_true, ↓reduceIte, encList_cons,
          List.length_append] <;> omega
  have hwrap (b : Bool) : ComputableInO (fun q : ℕ × List (List Bool × α) => ((q.1, b), q.2))
      (encPair encNat (encList encElem)) (encPair encS (encList encElem))
      (fun q => (encNat q.1).length + (encList encElem q.2).length)
      (fun q => (encNat q.1).length + (encList encElem q.2).length) := by
    have hp := ((ComputableInO.fst encNat (encList encElem)).prod
      (ComputableInO.const (encIn := encPair encNat (encList encElem))
        (encMid := encBool) b)).prod (ComputableInO.snd encNat (encList encElem))
    refine hp.mono 6 (fun q => ?_) (fun q => ?_)
    all_goals
      simp only [length_encPair]
      have hb : (encBool b).length ≤ 2 := by cases b <;> simp
      omega
  have hO_raw : ComputableInO
      (fun r : (ℕ × Bool) × List (List Bool × α) =>
        r.2.filter fun p => p.1.getD r.1.1 false == r.1.2)
      (encPair encS (encList encElem)) (encList encElem)
      (fun r => (encPair encS (encList encElem) r).length + (r.2.length + 1) *
        (2 * (encNat r.1.1).length + listMax (fun p => (encElem p).length) r.2 + 5) ^ d + 1)
      (fun r => (2 * (encNat r.1.1).length + listMax (fun p => (encElem p).length) r.2 + 5) ^ d +
        (encList encElem r.2).length + 1) := by
    refine ComputableInO.of_bounds h (c + 1) (fun r => ?_) (fun r => ?_) (fun r => ?_)
    · have h5 : 2 * (encNat r.1.1).length + listMax (fun p => (encElem p).length) r.2 + 4 + 1 =
          2 * (encNat r.1.1).length + listMax (fun p => (encElem p).length) r.2 + 5 := by omega
      rw [h5]
      exact Nat.mul_le_mul (by omega) (by omega)
    · have h5 : 2 * (encNat r.1.1).length + listMax (fun p => (encElem p).length) r.2 + 4 + 1 =
          2 * (encNat r.1.1).length + listMax (fun p => (encElem p).length) r.2 + 5 := by omega
      rw [h5]
      exact Nat.mul_le_mul (by omega) (by omega)
    · have hfl := hlen_filter r.1.2 r.1.1 r.2
      exact hfl.trans ((by omega : (encList encElem r.2).length ≤ _ + 1).trans
        (Nat.le_mul_of_pos_left _ (Nat.succ_pos _)))
  let D := max d 1
  have hbranch (b : Bool) : ComputableInO
      (fun q : ℕ × List (List Bool × α) => q.2.filter fun p => p.1.getD q.1 false == b)
      (encPair encNat (encList encElem)) (encList encElem)
      (fun q => (encList encElem q.2).length + (q.2.length + 1) * ((encNat q.1).length +
        listMax (fun p => (encElem p).length) q.2 + 1) ^ D)
      (fun q => (encList encElem q.2).length + ((encNat q.1).length +
        listMax (fun p => (encElem p).length) q.2 + 1) ^ D) := by
    have hcomp := hO_raw.comp (hwrap b)
    have hpow : ∀ A : ℕ, (2 * A + 5) ^ d ≤ 5 ^ d * (A + 1) ^ D := fun A => by
      calc (2 * A + 5) ^ d ≤ (5 * (A + 1)) ^ d := Nat.pow_le_pow_left (by omega) d
        _ = 5 ^ d * (A + 1) ^ d := Nat.mul_pow _ _ _
        _ ≤ 5 ^ d * (A + 1) ^ D :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_left _ _))
    have hpow_m_fn : ∀ q : ℕ × List (List Bool × α),
        (2 * (encNat q.1).length + listMax (fun p => (encElem p).length) q.2 + 5) ^ d ≤
          5 ^ d * ((encNat q.1).length +
            listMax (fun p => (encElem p).length) q.2 + 1) ^ D := fun q => by
      have hM_le : 2 * (encNat q.1).length + listMax (fun p => (encElem p).length) q.2 + 5 ≤
          2 * ((encNat q.1).length + listMax (fun p => (encElem p).length) q.2) + 5 := by omega
      exact (Nat.pow_le_pow_left hM_le d).trans (hpow _)
    refine hcomp.mono (5 ^ d + 10) (fun q => ?_) (fun q => ?_)
    · dsimp only [Function.comp_apply]
      set M := (encNat q.1).length + listMax (fun p => (encElem p).length) q.2
      set E := (encList encElem q.2).length
      set B := (q.2.length + 1) * (M + 1) ^ D
      have hpow_m : (2 * (encNat q.1).length + listMax (fun p => (encElem p).length) q.2 + 5) ^ d ≤
          5 ^ d * (M + 1) ^ D := hpow_m_fn q
      have hmul : (q.2.length + 1) * (2 * (encNat q.1).length +
            listMax (fun p => (encElem p).length) q.2 + 5) ^ d ≤ 5 ^ d * B := by
        calc _ ≤ (q.2.length + 1) * (5 ^ d * (M + 1) ^ D) := Nat.mul_le_mul_left _ hpow_m
          _ = 5 ^ d * B := by ring
      have hlen1 : (encNat q.1).length ≤ B := by
        have h1 : (encNat q.1).length ≤ M + 1 := by dsimp only [M]; omega
        have h2 : M + 1 ≤ (M + 1) ^ D :=
          Nat.le_self_pow (by have : 1 ≤ D := le_max_right d 1; omega) _
        exact (h1.trans h2).trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
      have hlen_w : (encPair encS (encList encElem) ((q.1, b), q.2)).length ≤
          4 * (encNat q.1).length + E + 7 := by
        change (encPair (encPair encNat encBool) (encList encElem) ((q.1, b), q.2)).length ≤ _
        rw [length_encPair, length_encPair]
        have hb : (encBool b).length ≤ 2 := by cases b <;> simp
        dsimp only [E]
        omega
      have h1pow : 1 ≤ B := Nat.mul_pos (Nat.succ_pos _) (Nat.one_le_pow _ _ (Nat.succ_pos _))
      have h5pow : 1 ≤ 5 ^ d := Nat.one_le_pow _ _ (by decide)
      change ((encNat q.1).length + E) +
          ((encPair encS (encList encElem) ((q.1, b), q.2)).length +
            (q.2.length + 1) * (2 * (encNat q.1).length +
              listMax (fun p => (encElem p).length) q.2 + 5) ^ d + 1) ≤
        (5 ^ d + 10) * (E + B + 1)
      have hsum_le : ((encNat q.1).length + E) +
            ((encPair encS (encList encElem) ((q.1, b), q.2)).length +
              (q.2.length + 1) * (2 * (encNat q.1).length +
                listMax (fun p => (encElem p).length) q.2 + 5) ^ d + 1) ≤
          5 * B + 2 * E + 5 ^ d * B + 8 := by
        linarith only [hlen1, hlen_w, hmul]
      have h_rhs : 5 * B + 2 * E + 5 ^ d * B + 8 ≤ (5 ^ d + 10) * (E + B + 1) := by
        nlinarith only [h1pow, h5pow]
      exact hsum_le.trans h_rhs
    · dsimp only [Function.comp_apply]
      set M := (encNat q.1).length + listMax (fun p => (encElem p).length) q.2
      have hpow_m : (2 * (encNat q.1).length + listMax (fun p => (encElem p).length) q.2 + 5) ^ d ≤
          5 ^ d * (M + 1) ^ D := hpow_m_fn q
      have hlen1 : (encNat q.1).length ≤ (M + 1) ^ D := by
        have h1 : (encNat q.1).length ≤ M + 1 := by dsimp only [M]; omega
        exact h1.trans (Nat.le_self_pow (by have : 1 ≤ D := le_max_right d 1; omega) _)
      have h1pow : 1 ≤ (M + 1) ^ D := Nat.one_le_pow _ _ (Nat.succ_pos _)
      have h5pow : 1 ≤ 5 ^ d := Nat.one_le_pow _ _ (by decide)
      change ((encNat q.1).length + (encList encElem q.2).length) +
          ((2 * (encNat q.1).length + listMax (fun p => (encElem p).length) q.2 + 5) ^ d +
            (encList encElem q.2).length + 1) ≤
        (5 ^ d + 10) * ((encList encElem q.2).length + (M + 1) ^ D + 1)
      nlinarith
  have happ : ComputableInO (fun q : ℕ × List (List Bool × α) => radixPass q.1 q.2)
      (encPair encNat (encList encElem)) (encList encElem)
      (fun q => (encList encElem q.2).length + (q.2.length + 1) * ((encNat q.1).length +
        listMax (fun p => (encElem p).length) q.2 + 1) ^ D)
      (fun q => (encList encElem q.2).length + ((encNat q.1).length +
        listMax (fun p => (encElem p).length) q.2 + 1) ^ D) := by
    have hpair := (hbranch false).prod (hbranch true)
    have hcomp :=
      (ComputableInO.of_linear (ComputableInDegree.listAppend encElem)).comp_linear hpair
    have hfun : (fun p : List (List Bool × α) × List (List Bool × α) => p.1 ++ p.2) ∘
        (fun q : ℕ × List (List Bool × α) =>
          (q.2.filter fun p => p.1.getD q.1 false == false,
           q.2.filter fun p => p.1.getD q.1 false == true)) =
        fun q => radixPass q.1 q.2 := by
      funext q
      simp [radixPass]
    rw [hfun] at hcomp
    exact hcomp.mono 2 (fun _ => by omega) (fun _ => by omega)
  exact ⟨D, happ⟩

private theorem computableInO_radixSortLSB {α γ : Type} {encα : α ↪ List Bool}
    {encIn : γ ↪ List Bool}
    {b : γ → ℕ} {L : γ → List (List Bool × α)} {Tb Sb TL SL : γ → ℕ}
    (hb : ComputableInO b encIn encNat Tb Sb)
    (hL : ComputableInO L encIn (encList (encPair encBits encα)) TL SL)
    {M : γ → ℕ}
    (hM : ∀ x, ∀ p ∈ L x, (encPair encBits encα p).length ≤ M x) :
    ∃ d, ComputableInO (fun x => radixSortLSB (b x) (L x))
      encIn (encList (encPair encBits encα))
      (fun x => (encIn x).length + Tb x + TL x + (b x + 1) *
        (((L x).length + 1) * ((encNat (b x)).length + M x + 1) ^ d + 1))
      (fun x => Sb x + SL x + ((L x).length + 1) * (M x + 1) +
        ((encNat (b x)).length + M x + 1) ^ d) := by
  let encElem := encPair encBits encα
  let encState := encPair encNat (encList encElem)
  obtain ⟨dp, hp⟩ := computableInO_radixPass encα
  let d := max dp 2
  have hstep : ComputableInO (radixStep (α := α)) encState encState
      (fun q => (encList encElem q.2).length +
        (q.2.length + 1) *
          ((encNat q.1).length + listMax (fun p => (encElem p).length) q.2 + 1) ^ d +
        ((encNat q.1).length + 1) ^ 2)
      (fun q => (encList encElem q.2).length +
        ((encNat q.1).length + listMax (fun p => (encElem p).length) q.2 + 1) ^ d) := by
    have hinc : ComputableInO (fun q : ℕ × List (List Bool × α) => q.1 + 1) encState encNat
        (fun q => (encPair encNat (encList encElem) q).length + ((encNat q.1).length + 1) ^ 2)
        (fun q => (encPair encNat (encList encElem) q).length + (encNat q.1).length + 1) := by
      have hcomp := ComputableInO.natSucc.comp (ComputableInO.fst encNat (encList encElem))
      refine hcomp.mono 2 (fun q => ?_) (fun q => ?_) <;>
        · rw [length_encPair]; omega
    have hp' : ComputableInO (fun q : ℕ × List (List Bool × α) => radixPass q.1 q.2)
        encState (encList encElem)
        (fun q => (encList encElem q.2).length +
          (q.2.length + 1) * ((encNat q.1).length +
            listMax (fun p => (encElem p).length) q.2 + 1) ^ d)
        (fun q => (encList encElem q.2).length +
          ((encNat q.1).length + listMax (fun p => (encElem p).length) q.2 + 1) ^ d) := by
      have hdp : ∀ q : ℕ × List (List Bool × α),
          ((encNat q.1).length + listMax (fun p => (encPair encBits encα p).length) q.2 + 1) ^ dp ≤
            ((encNat q.1).length + listMax (fun p => (encPair encBits encα p).length) q.2 + 1) ^
              d :=
        fun _ => Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_left dp 2)
      refine hp.mono 1 (fun q => ?_) (fun q => ?_)
      · dsimp only [encElem]
        have hm := Nat.mul_le_mul_left (q.2.length + 1) (hdp q)
        omega
      · dsimp only [encElem]
        have := hdp q
        omega
    have hprod := hinc.prod hp'
    refine hprod.mono 4 (fun q => ?_) (fun q => ?_)
    · rw [length_encPair]
      have h1 : (encNat q.1).length ≤ ((encNat q.1).length + 1) ^ 2 := by nlinarith
      omega
    · rw [length_encPair]
      have h1 : (encNat q.1).length ≤
          ((encNat q.1).length + listMax (fun p => (encElem p).length) q.2 + 1) ^ d :=
        (by omega : (encNat q.1).length ≤ _ + 1).trans
          (Nat.le_self_pow (by have : 2 ≤ d := le_max_right dp 2; omega) _)
      omega
  have hinit : ComputableInO (fun x => ((0 : ℕ), L x)) encIn encState
      (fun x => (encIn x).length + TL x) (fun x => SL x) := by
    have hp0 := (ComputableInO.constZero (encIn := encIn) (encMid := encNat) (0 : ℕ)).prod hL
    exact hp0.mono 1 (fun _ => by simp) (fun _ => by simp)
  have henc_step : ∀ x k,
      (encList encElem (radixStep^[k] (0, L x)).2).length ≤
        (L x).length * (2 * M x + 1) := fun x k => by
    have hm : ∀ p ∈ (radixStep^[k] (0, L x)).2, (encElem p).length ≤ M x :=
      fun p hp => hM x p ((mem_radixStep_iff).1 hp)
    have hl : (radixStep^[k] (0, L x)).2.length = (L x).length := length_radixStep k 0 (L x)
    exact (length_encList_le encElem _ (b := M x) hm).trans (by rw [hl])
  have hit := ComputableInO.iterate hb hinit hstep
    (R := fun x => (L x).length * (2 * M x + 1) +
      ((L x).length + 1) * ((encNat (b x)).length + M x + 1) ^ d +
      ((encNat (b x)).length + 1) ^ 2)
    (Q := fun x => (L x).length * (2 * M x + 1) + ((encNat (b x)).length + M x + 1) ^ d)
    (B := fun x => 2 * (encNat (b x)).length + (L x).length * (2 * M x + 1) + 1)
    (fun x k hk => by
      have hk1 : (encNat (radixStep^[k] (0, L x)).1).length ≤ (encNat (b x)).length := by
        rw [fst_iterate_radixStep, Nat.zero_add]; exact length_encNat_mono hk
      have hlen2 := henc_step x k
      have hl2 : (radixStep^[k] (0, L x)).2.length = (L x).length := length_radixStep k 0 (L x)
      have hm2 : listMax (fun p => (encElem p).length) (radixStep^[k] (0, L x)).2 ≤ M x :=
        listMax_le fun p hp => hM x p ((mem_radixStep_iff).1 hp)
      have hpow : ((encNat (radixStep^[k] (0, L x)).1).length +
            listMax (fun p => (encElem p).length) (radixStep^[k] (0, L x)).2 + 1) ^ d ≤
          ((encNat (b x)).length + M x + 1) ^ d :=
        Nat.pow_le_pow_left (by omega) d
      have hpow2 : ((encNat (radixStep^[k] (0, L x)).1).length + 1) ^ 2 ≤
          ((encNat (b x)).length + 1) ^ 2 :=
        Nat.pow_le_pow_left (by omega) 2
      have hmul := Nat.mul_le_mul_left ((L x).length + 1) hpow
      rw [hl2]
      omega)
    (fun x k hk => by
      have hk1 : (encNat (radixStep^[k] (0, L x)).1).length ≤ (encNat (b x)).length := by
        rw [fst_iterate_radixStep, Nat.zero_add]; exact length_encNat_mono hk
      have hlen2 := henc_step x k
      have hm2 : listMax (fun p => (encElem p).length) (radixStep^[k] (0, L x)).2 ≤ M x :=
        listMax_le fun p hp => hM x p ((mem_radixStep_iff).1 hp)
      have hpow : ((encNat (radixStep^[k] (0, L x)).1).length +
            listMax (fun p => (encElem p).length) (radixStep^[k] (0, L x)).2 + 1) ^ d ≤
          ((encNat (b x)).length + M x + 1) ^ d :=
        Nat.pow_le_pow_left (by omega) d
      omega)
    (fun x k hk => by
      have hk1 : (encNat (radixStep^[k] (0, L x)).1).length ≤ (encNat (b x)).length := by
        rw [fst_iterate_radixStep, Nat.zero_add]; exact length_encNat_mono hk
      have hlen2 := henc_step x k
      rw [length_encPair]
      omega)
  have hsnd := ComputableInO.snd' hit
  refine ⟨d, hsnd.mono 24 (fun x => ?_) (fun x => ?_)⟩
  · have h2 : ((encNat (b x)).length + 1) ^ 2 ≤ ((encNat (b x)).length + M x + 1) ^ d :=
      (Nat.pow_le_pow_left (by omega) 2).trans
        (Nat.pow_le_pow_right (by omega) (le_max_right dp 2))
    have hmul : ((encNat (b x)).length + M x + 1) ^ d ≤
        ((L x).length + 1) * ((encNat (b x)).length + M x + 1) ^ d :=
      Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    have h1 : (encNat (b x)).length ≤ ((encNat (b x)).length + 1) ^ 2 := by nlinarith
    have hM2 : (L x).length * (2 * M x + 1) ≤
        2 * ((L x).length + 1) * ((encNat (b x)).length + M x + 1) ^ d := by
      have hm_pow : 2 * M x + 1 ≤ 2 * ((encNat (b x)).length + M x + 1) ^ d := by
        have hle : M x + 1 ≤ ((encNat (b x)).length + M x + 1) ^ 1 := by simp
        have hle2 : ((encNat (b x)).length + M x + 1) ^ 1 ≤
            ((encNat (b x)).length + M x + 1) ^ d :=
          Nat.pow_le_pow_right (by omega) (by have : 2 ≤ d := le_max_right dp 2; omega)
        omega
      calc (L x).length * (2 * M x + 1)
          ≤ ((L x).length + 1) * (2 * ((encNat (b x)).length + M x + 1) ^ d) :=
            Nat.mul_le_mul (Nat.le_succ _) hm_pow
        _ = 2 * ((L x).length + 1) * ((encNat (b x)).length + M x + 1) ^ d := by ring
    have hstep1 : (L x).length * (2 * M x + 1) +
          ((L x).length + 1) * ((encNat (b x)).length + M x + 1) ^ d +
          ((encNat (b x)).length + 1) ^ 2 +
          (2 * (encNat (b x)).length + (L x).length * (2 * M x + 1) + 1) +
          ((encNat (b x)).length + 1) ^ 2 ≤
        8 * (((L x).length + 1) * ((encNat (b x)).length + M x + 1) ^ d + 1) := by
      nlinarith
    have hmul_b := Nat.mul_le_mul_left (b x + 1) hstep1
    calc Tb x + ((encIn x).length + TL x) +
          (b x + 1) * ((L x).length * (2 * M x + 1) +
            ((L x).length + 1) * ((encNat (b x)).length + M x + 1) ^ d +
            ((encNat (b x)).length + 1) ^ 2 +
            (2 * (encNat (b x)).length + (L x).length * (2 * M x + 1) + 1) +
            ((encNat (b x)).length + 1) ^ 2)
        ≤ Tb x + ((encIn x).length + TL x) +
            (b x + 1) * (8 * (((L x).length + 1) * ((encNat (b x)).length + M x + 1) ^ d + 1)) :=
          Nat.add_le_add_left hmul_b _
      _ ≤ Tb x + ((encIn x).length + TL x) +
            8 * ((b x + 1) * (((L x).length + 1) * ((encNat (b x)).length + M x + 1) ^ d + 1)) := by
          rw [show (b x + 1) *
              (8 * (((L x).length + 1) * ((encNat (b x)).length + M x + 1) ^ d + 1)) =
            8 * ((b x + 1) * (((L x).length + 1) * ((encNat (b x)).length + M x + 1) ^ d + 1))
            from by ring]
      _ ≤ 24 * ((encIn x).length + Tb x + TL x + (b x + 1) *
            (((L x).length + 1) * ((encNat (b x)).length + M x + 1) ^ d + 1) + 1) := by
          omega
  · have h1 : (encNat (b x)).length ≤ ((encNat (b x)).length + M x + 1) ^ d :=
      (by omega : (encNat (b x)).length ≤ _ + 1).trans
        (Nat.le_self_pow (by have : 2 ≤ d := le_max_right dp 2; omega) _)
    have h2 : (L x).length * (2 * M x + 1) ≤ 2 * (((L x).length + 1) * (M x + 1)) := by
      calc (L x).length * (2 * M x + 1) ≤ ((L x).length + 1) * (2 * (M x + 1)) :=
            Nat.mul_le_mul (Nat.le_succ _) (by omega)
        _ = 2 * (((L x).length + 1) * (M x + 1)) := by ring
    nlinarith

/-! ### Stage 1 & 2: Enumerating all `2 ^ n` masks and counting gate multiplicities -/

private def maskBits (n k : ℕ) : List Bool :=
  (List.range n).map k.testBit

private theorem length_maskBits (n k : ℕ) : (maskBits n k).length = n := by
  simp [maskBits]

private theorem evalBits_maskBits (n k : ℕ) (hk : k < 2 ^ n) :
    evalBits n (maskBits n k) = k := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  rw [testBit_evalBits]
  by_cases hi : i < n
  · simp [hi, maskBits, List.getD_eq_getElem?_getD]
  · simp only [hi, decide_false, Bool.false_and]
    exact (Nat.testBit_lt_two_pow (hk.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))).symm

private def maskStep (M : List (List Bool)) : List (List Bool) :=
  M.map (· ++ [false]) ++ M.map (· ++ [true])

private def allMasks (n : ℕ) : List (List Bool) :=
  maskStep^[n] [[]]

private theorem maskBits_add_two_pow_false {n k : ℕ} (hk : k < 2 ^ n) :
    maskBits (n + 1) k = maskBits n k ++ [false] := by
  simp only [maskBits, List.range_succ, List.map_append, List.map_singleton]
  congr 1
  exact congrArg List.singleton (Nat.testBit_lt_two_pow hk)

private theorem maskBits_add_two_pow_true {n k : ℕ} (hk : k < 2 ^ n) :
    maskBits (n + 1) (k + 2 ^ n) = maskBits n k ++ [true] := by
  simp only [maskBits, List.range_succ, List.map_append, List.map_singleton]
  congr 1
  · refine List.map_congr_left fun i hi => ?_
    have hin : i < n := List.mem_range.1 hi
    have hpow : 2 ^ n = 2 ^ i * 2 ^ (n - i) := by rw [← pow_add, Nat.add_sub_of_le hin.le]
    have hpos : 0 < n - i := by omega
    have heven : (2 ^ (n - i)) % 2 = 0 := by rw [← Nat.sub_add_cancel hpos, pow_succ]; omega
    simp [Nat.testBit_eq_decide_div_mod_eq, hpow,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos i), Nat.add_mod, heven]
  · have hdiv : (k + 2 ^ n) / 2 ^ n = 1 := by
      rw [Nat.add_div_right _ (Nat.two_pow_pos n), Nat.div_eq_of_lt hk]
    simp [Nat.testBit_eq_decide_div_mod_eq, hdiv]

private theorem allMasks_eq (n : ℕ) :
    allMasks n = (List.range (2 ^ n)).map (maskBits n) := by
  induction n with
  | zero => simp [allMasks, maskBits]
  | succ n ih =>
    rw [allMasks, Function.iterate_succ_apply', ← allMasks, ih, maskStep, pow_succ, Nat.mul_two,
      List.range_add, List.map_append, List.map_map, List.map_map, List.map_map]
    congr 1
    · refine List.map_congr_left fun k hk => ?_
      exact (maskBits_add_two_pow_false (List.mem_range.1 hk)).symm
    · refine List.map_congr_left fun k hk => ?_
      dsimp only [Function.comp_apply]
      rw [Nat.add_comm (2 ^ n) k]
      exact (maskBits_add_two_pow_true (List.mem_range.1 hk)).symm

private theorem length_allMasks (n : ℕ) : (allMasks n).length = 2 ^ n := by
  rw [allMasks_eq, List.length_map, List.length_range]

private theorem maskMap_streamEmit (b : Bool) (M : List (List Bool)) :
    encList encBits (M.map (· ++ [b])) =
      streamEmit (fun q : Bool × List Bool => q.1)
        (fun q => encList encBits [q.2 ++ [q.1]]) b M := by
  induction M with
  | nil => rfl
  | cons a t ih =>
    simp [List.map_cons, streamEmit, encList_cons, ih]

private theorem computableInO_n_unary :
    ComputableInO (fun x : SymAndInstance => x.n) encSymAndInstance encUnary
      (fun x => (encSymAndInstance x).length) (fun x => (encSymAndInstance x).length) := by
  have h1 := (ComputableInO.fst encUnary (encList encBits)).of_encIn_eq
    (fun x : SymAndInstance => (x.n, x.gates)) (fun x => (encSymAndInstance_apply x).symm)
  exact h1.mono 1
    (fun x => by
      rw [encSymAndInstance_apply]
      dsimp only [Function.comp_apply, encSymAndInstanceFields]
      omega)
    (fun x => by
      rw [encSymAndInstance_apply]
      dsimp only [Function.comp_apply, encSymAndInstanceFields]
      omega)

private theorem computableInO_n_nat :
    ComputableInO (fun x : SymAndInstance => x.n) encSymAndInstance encNat
      (fun x => (encSymAndInstance x).length) (fun x => (encSymAndInstance x).length) := by
  have hcomp := ComputableInO.unaryToNat.comp computableInO_n_unary
  have hle : ∀ x : SymAndInstance, x.n ≤ (encSymAndInstance x).length := fun x => by
    rw [encSymAndInstance_apply, encSymAndInstanceFields, length_encPair]
    dsimp only
    have h1 : x.n ≤ (encUnary x.n).length := by simp [encUnary_apply]
    omega
  exact hcomp.mono 2 (fun x => by have := hle x; omega)
    (fun x => by have := hle x; omega)

private theorem computableInO_allMasks :
    ∃ d, ComputableInO (fun x : SymAndInstance => allMasks x.n) encSymAndInstance
      (encList encBits)
      (fun x => (encSymAndInstance x).length + 2 ^ x.n * (x.n + 1) ^ d)
      (fun x => (encSymAndInstance x).length + 2 ^ x.n * (x.n + 1) ^ d) := by
  have hnext : ComputableInPolyTime (fun q : Bool × List Bool => q.1)
      (encPair encBool encBits) encBool := by fun_prop
  have hemit : ComputableInPolyTime (fun q : Bool × List Bool => [q.2 ++ [q.1]])
      (encPair encBool encBits) (encList encBits) := by
    have happ : ComputableInPolyTime (fun q : Bool × List Bool => q.2 ++ [q.1])
        (encPair encBool encBits) encBits :=
      bitsAppend (by fun_prop) (bitsCons (by fun_prop) (const []))
    exact happ.cons' (const [])
  obtain ⟨c, d, h⟩ := ComputableInTimeAndSpace.streamFold_pair_list
    (encA := encBits) (encS := encBool) (encB := encBits)
    (encIn := encPair encBool (encList encBits))
    (init := Prod.fst) (elems := Prod.snd) (fun _ => rfl) hnext hemit
    (g := fun q : Bool × List (List Bool) => q.2.map (· ++ [q.1]))
    (fun q => maskMap_streamEmit q.1 q.2)
    (lMax := fun q => listMax List.length q.2 + 2)
    (fun q j _ => by
      have htake : ∀ (xs : List (List Bool)) (s : Bool),
          xs.foldl (fun (p : Bool) (_ : List Bool) => p) s = s := fun xs s => by
        induction xs with
        | nil => rfl
        | cons _ _ ih => exact ih
      have hst : streamState q.1 (fun p : Bool × List Bool => p.1) q.2 j = q.1 :=
        htake (q.2.take j) q.1
      change (encBool (streamState q.1 _ q.2 j)).length ≤ _
      rw [hst]; cases q.1 <;> simp)
    (fun q j hj => (le_listMax (f := List.length) (List.getElem_mem hj)).trans (by omega))
  have hlen_map : ∀ (b : Bool) (M : List (List Bool)),
      (encList encBits (M.map (· ++ [b]))).length ≤
        (encList encBits M).length + 2 * M.length := fun b M => by
    induction M with
    | nil => simp
    | cons a t ih =>
      simp only [List.map_cons, encList_cons, List.length_append, List.length_cons,
        List.length_nil, length_frame, encBits_apply] at ih ⊢
      have hl1 : (a ++ [b]).length = a.length + 1 := by simp
      omega
  have hmap (b : Bool) : ComputableInO (fun M : List (List Bool) => M.map (· ++ [b]))
      (encList encBits) (encList encBits)
      (fun M => (encList encBits M).length + (M.length + 1) * (listMax List.length M + 1) ^ d)
      (fun M => (encList encBits M).length + M.length + (listMax List.length M + 1) ^ d) := by
    have hwrap : ComputableInO (fun M : List (List Bool) => (b, M))
        (encList encBits) (encPair encBool (encList encBits))
        (fun M => (encList encBits M).length) (fun M => (encList encBits M).length) := by
      have hp := (ComputableInO.constZero (encIn := encList encBits) (encMid := encBool) b).prod
        (ComputableInO.id' (encMid := encList encBits))
      exact hp.mono 2 (fun _ => by omega) (fun _ => by omega)
    have hraw : ComputableInO (fun q : Bool × List (List Bool) => q.2.map (· ++ [q.1]))
        (encPair encBool (encList encBits)) (encList encBits)
        (fun q => (encList encBits q.2).length +
          (q.2.length + 1) * (listMax List.length q.2 + 1) ^ d)
        (fun q =>
          (encList encBits q.2).length + q.2.length + (listMax List.length q.2 + 1) ^ d) := by
      have hpow : ∀ A : ℕ, (A + 3) ^ d ≤ 3 ^ d * (A + 1) ^ d := fun A => by
        calc (A + 3) ^ d ≤ (3 * (A + 1)) ^ d := Nat.pow_le_pow_left (by omega) d
          _ = 3 ^ d * (A + 1) ^ d := Nat.mul_pow _ _ _
      refine ComputableInO.of_bounds h (6 * c * 3 ^ d + 3) (fun q => ?_) (fun q => ?_) (fun q => ?_)
      · rw [length_encPair]
        have hlen_b : (encBool q.1).length ≤ 2 := by cases q.1 <;> simp
        have hpow_m := hpow (listMax List.length q.2)
        have hmul : (q.2.length + 1) * (listMax List.length q.2 + 3) ^ d ≤
            3 ^ d * ((q.2.length + 1) * (listMax List.length q.2 + 1) ^ d) := by
          calc _ ≤ (q.2.length + 1) * (3 ^ d * (listMax List.length q.2 + 1) ^ d) :=
                Nat.mul_le_mul_left _ hpow_m
            _ = _ := by ring
        set E := (encList encBits q.2).length
        set B := (q.2.length + 1) * (listMax List.length q.2 + 1) ^ d
        have h1pow : 1 ≤ B := Nat.mul_pos (Nat.succ_pos _) (Nat.one_le_pow _ _ (Nat.succ_pos _))
        have h3pow : 1 ≤ 3 ^ d := Nat.one_le_pow _ _ (by decide)
        have hsum : 2 * (encBool q.1).length + 1 + E +
            (q.2.length + 1) * (listMax List.length q.2 + 3) ^ d + 1 ≤
            6 * 3 ^ d * (E + B + 1) := by
          calc 2 * (encBool q.1).length + 1 + E +
                (q.2.length + 1) * (listMax List.length q.2 + 3) ^ d + 1
              ≤ 4 + 1 + E + 3 ^ d * B + 1 := by omega
            _ ≤ 6 * 3 ^ d * (E + B + 1) := by nlinarith
        calc c * (2 * (encBool q.1).length + 1 + E +
              (q.2.length + 1) * (listMax List.length q.2 + 3) ^ d + 1)
            ≤ c * (6 * 3 ^ d * (E + B + 1)) := Nat.mul_le_mul_left _ hsum
          _ ≤ (6 * c * 3 ^ d + 3) * (E + B + 1) := by nlinarith
      · have hpow_m := hpow (listMax List.length q.2)
        set E := (encList encBits q.2).length
        set A := (listMax List.length q.2 + 1) ^ d
        have h1pow : 1 ≤ A := Nat.one_le_pow _ _ (Nat.succ_pos _)
        have h3pow : 1 ≤ 3 ^ d := Nat.one_le_pow _ _ (by decide)
        have hsum : (listMax List.length q.2 + 3) ^ d + 1 ≤
            6 * 3 ^ d * (E + q.2.length + A + 1) := by
          calc (listMax List.length q.2 + 3) ^ d + 1
              ≤ 3 ^ d * A + 1 := Nat.add_le_add_right hpow_m 1
            _ ≤ 6 * 3 ^ d * (E + q.2.length + A + 1) := by nlinarith
        calc c * ((listMax List.length q.2 + 3) ^ d + 1)
            ≤ c * (6 * 3 ^ d * (E + q.2.length + A + 1)) := Nat.mul_le_mul_left _ hsum
          _ ≤ (6 * c * 3 ^ d + 3) * (E + q.2.length + A + 1) := by nlinarith
      · have hm := hlen_map q.1 q.2
        have h1pow : 1 ≤ (listMax List.length q.2 + 1) ^ d := Nat.one_le_pow _ _ (Nat.succ_pos _)
        calc (encList encBits (q.2.map (· ++ [q.1]))).length
            ≤ (encList encBits q.2).length + 2 * q.2.length := hm
          _ ≤ 3 * ((encList encBits q.2).length + q.2.length +
                (listMax List.length q.2 + 1) ^ d + 1) := by omega
          _ ≤ (6 * c * 3 ^ d + 3) * ((encList encBits q.2).length + q.2.length +
                (listMax List.length q.2 + 1) ^ d + 1) :=
              Nat.mul_le_mul_right _ (by omega)
    exact hraw.comp hwrap |>.mono 2 (fun _ => by dsimp; omega) (fun _ => by dsimp; omega)
  have hstep : ComputableInO maskStep (encList encBits) (encList encBits)
      (fun M => (encList encBits M).length + (M.length + 1) * (listMax List.length M + 1) ^ d)
      (fun M => (encList encBits M).length + M.length + (listMax List.length M + 1) ^ d) := by
    have hcomp := (ComputableInO.of_linear (ComputableInDegree.listAppend encBits)).comp_linear
      ((hmap false).prod (hmap true))
    exact hcomp.mono 2 (fun _ => by omega) (fun _ => by omega)
  have hlen_allMasks_k : ∀ k : ℕ, ∀ bs ∈ allMasks k, bs.length = k := fun k bs hbs => by
    rw [allMasks_eq, List.mem_map] at hbs
    obtain ⟨j, _, rfl⟩ := hbs
    exact length_maskBits k j
  have henc_allMasks_k : ∀ k : ℕ,
      (encList encBits (allMasks k)).length ≤ 2 ^ k * (2 * k + 1) := fun k => by
    calc (encList encBits (allMasks k)).length
        ≤ (allMasks k).length * (2 * k + 1) :=
          length_encList_le encBits _ (b := k) fun bs hbs => by
            simpa [encBits_apply] using (hlen_allMasks_k k bs hbs).le
      _ = 2 ^ k * (2 * k + 1) := by rw [length_allMasks]
  have hit := ComputableInO.iterate computableInO_n_nat
    (ComputableInO.const ([[]] : List (List Bool))) hstep
    (R := fun x => 2 ^ x.n * (2 * x.n + 1) + (2 ^ x.n + 1) * (x.n + 1) ^ d)
    (Q := fun x => 2 ^ x.n * (2 * x.n + 1) + 2 ^ x.n + (x.n + 1) ^ d)
    (B := fun x => 2 ^ x.n * (2 * x.n + 1))
    (fun x k hk => by
      change (encList encBits (allMasks k)).length +
        ((allMasks k).length + 1) * (listMax List.length (allMasks k) + 1) ^ d ≤ _
      have hlen := henc_allMasks_k k
      have hl : (allMasks k).length = 2 ^ k := length_allMasks k
      have hm : listMax List.length (allMasks k) ≤ x.n :=
        listMax_le fun bs hbs => (hlen_allMasks_k k bs hbs).le.trans hk
      have h2k : 2 ^ k ≤ 2 ^ x.n := Nat.pow_le_pow_right (by decide) hk
      have hpow : (listMax List.length (allMasks k) + 1) ^ d ≤ (x.n + 1) ^ d :=
        Nat.pow_le_pow_left (by omega) d
      have h1 : 2 ^ k * (2 * k + 1) ≤ 2 ^ x.n * (2 * x.n + 1) := Nat.mul_le_mul h2k (by omega)
      have h2 : (2 ^ k + 1) * (listMax List.length (allMasks k) + 1) ^ d ≤
          (2 ^ x.n + 1) * (x.n + 1) ^ d := Nat.mul_le_mul (by omega) hpow
      rw [hl]
      omega)
    (fun x k hk => by
      change (encList encBits (allMasks k)).length + (allMasks k).length +
        (listMax List.length (allMasks k) + 1) ^ d ≤ _
      have hlen := henc_allMasks_k k
      have hl : (allMasks k).length = 2 ^ k := length_allMasks k
      have hm : listMax List.length (allMasks k) ≤ x.n :=
        listMax_le fun bs hbs => (hlen_allMasks_k k bs hbs).le.trans hk
      have h2k : 2 ^ k ≤ 2 ^ x.n := Nat.pow_le_pow_right (by decide) hk
      have hpow : (listMax List.length (allMasks k) + 1) ^ d ≤ (x.n + 1) ^ d :=
        Nat.pow_le_pow_left (by omega) d
      have h1 : 2 ^ k * (2 * k + 1) ≤ 2 ^ x.n * (2 * x.n + 1) := Nat.mul_le_mul h2k (by omega)
      rw [hl]
      omega)
    (fun x k hk => by
      change (encList encBits (allMasks k)).length ≤ 2 ^ x.n * (2 * x.n + 1)
      have h2k : 2 ^ k ≤ 2 ^ x.n := Nat.pow_le_pow_right (by decide) hk
      exact (henc_allMasks_k k).trans (Nat.mul_le_mul h2k (by omega)))
  refine ⟨d + 4, hit.mono 12 (fun x => ?_) (fun x => ?_)⟩
  · have hpow_len : (encNat x.n).length ≤ x.n + 1 := by
      rw [encNat_apply, Nat.size_eq_bits_len]
      exact (Nat.size_le.2 (Nat.lt_pow_self (a := 2) (by decide))).trans (Nat.le_succ _)
    have hpow2 : ((encNat x.n).length + 1) ^ 2 ≤ (x.n + 2) ^ 2 :=
      Nat.pow_le_pow_left (by omega) 2
    have h6 : 1 ≤ 2 ^ x.n := Nat.one_le_pow _ _ (by decide)
    have hmul : (2 ^ x.n + 1) * (x.n + 1) ^ d ≤ 2 * 2 ^ x.n * (x.n + 1) ^ d := by
      calc (2 ^ x.n + 1) * (x.n + 1) ^ d ≤ (2 * 2 ^ x.n) * (x.n + 1) ^ d :=
            Nat.mul_le_mul_right _ (by omega)
        _ = 2 * 2 ^ x.n * (x.n + 1) ^ d := by ring
    have ha : (x.n + 1) ^ 2 ≤ (x.n + 1) ^ (d + 4) := Nat.pow_le_pow_right (by omega) (by omega)
    have hb : (x.n + 1) ^ 3 ≤ (x.n + 1) ^ (d + 4) := Nat.pow_le_pow_right (by omega) (by omega)
    have hc : (x.n + 1) ^ (d + 1) ≤ (x.n + 1) ^ (d + 4) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hlin : (x.n + 1) * (2 ^ x.n * (2 * x.n + 1) + 2 * 2 ^ x.n * (x.n + 1) ^ d +
          2 ^ x.n * (2 * x.n + 1) + (x.n + 2) ^ 2) ≤
        10 * (2 ^ x.n * (x.n + 1) ^ (d + 4)) := by
      calc (x.n + 1) * (2 ^ x.n * (2 * x.n + 1) + 2 * 2 ^ x.n * (x.n + 1) ^ d +
              2 ^ x.n * (2 * x.n + 1) + (x.n + 2) ^ 2)
          ≤ (x.n + 1) * (2 ^ x.n * (4 * (x.n + 1)) + 2 * 2 ^ x.n * (x.n + 1) ^ d +
              4 * 2 ^ x.n * (x.n + 1) ^ 2) := by
            refine Nat.mul_le_mul_left _ ?_
            have hx2 : (x.n + 2) ^ 2 ≤ 4 * (x.n + 1) ^ 2 := by nlinarith
            have := Nat.mul_le_mul_left (4 * (x.n + 1) ^ 2) h6
            nlinarith
        _ = 4 * 2 ^ x.n * (x.n + 1) ^ 2 + 2 * 2 ^ x.n * (x.n + 1) ^ (d + 1) +
              4 * 2 ^ x.n * (x.n + 1) ^ 3 := by ring
        _ ≤ 4 * 2 ^ x.n * (x.n + 1) ^ (d + 4) + 2 * 2 ^ x.n * (x.n + 1) ^ (d + 4) +
              4 * 2 ^ x.n * (x.n + 1) ^ (d + 4) := by gcongr
        _ = 10 * (2 ^ x.n * (x.n + 1) ^ (d + 4)) := by ring
    have hprod_le : (x.n + 1) * (2 ^ x.n * (2 * x.n + 1) + (2 ^ x.n + 1) * (x.n + 1) ^ d +
          2 ^ x.n * (2 * x.n + 1) + ((encNat x.n).length + 1) ^ 2) ≤
        10 * (2 ^ x.n * (x.n + 1) ^ (d + 4)) := by
      calc (x.n + 1) * _ ≤ (x.n + 1) * (2 ^ x.n * (2 * x.n + 1) + 2 * 2 ^ x.n * (x.n + 1) ^ d +
              2 ^ x.n * (2 * x.n + 1) + (x.n + 2) ^ 2) := Nat.mul_le_mul_left _ (by omega)
        _ ≤ 10 * (2 ^ x.n * (x.n + 1) ^ (d + 4)) := hlin
    omega
  · have h6 : 1 ≤ 2 ^ x.n := Nat.one_le_pow _ _ (by decide)
    have h1 : (encNat x.n).length ≤ x.n + 1 := by
      rw [encNat_apply, Nat.size_eq_bits_len]
      exact (Nat.size_le.2 (Nat.lt_pow_self (a := 2) (by decide))).trans (Nat.le_succ _)
    have ha : (x.n + 1) ^ 1 ≤ (x.n + 1) ^ (d + 4) := Nat.pow_le_pow_right (by omega) (by omega)
    have hb : (x.n + 1) ^ d ≤ (x.n + 1) ^ (d + 4) := Nat.pow_le_pow_right (by omega) (by omega)
    have hmul : 2 ^ x.n * (2 * x.n + 1) ≤ 2 * (2 ^ x.n * (x.n + 1) ^ (d + 4)) := by
      calc 2 ^ x.n * (2 * x.n + 1) ≤ 2 ^ x.n * (2 * (x.n + 1) ^ 1) := by nlinarith
        _ ≤ 2 ^ x.n * (2 * (x.n + 1) ^ (d + 4)) := by gcongr
        _ = 2 * (2 ^ x.n * (x.n + 1) ^ (d + 4)) := by ring
    have h1p : 2 ^ x.n ≤ 2 ^ x.n * (x.n + 1) ^ (d + 4) :=
      Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (Nat.succ_pos _))
    have h2p : (x.n + 1) ^ d ≤ 2 ^ x.n * (x.n + 1) ^ (d + 4) := by
      calc (x.n + 1) ^ d ≤ (x.n + 1) ^ (d + 4) := hb
        _ ≤ 2 ^ x.n * (x.n + 1) ^ (d + 4) := Nat.le_mul_of_pos_left _ h6
    have h3p : (encNat x.n).length ≤ 2 ^ x.n * (x.n + 1) ^ (d + 4) := by
      calc (encNat x.n).length ≤ (x.n + 1) ^ 1 := h1.trans (by simp)
        _ ≤ (x.n + 1) ^ (d + 4) := ha
        _ ≤ 2 ^ x.n * (x.n + 1) ^ (d + 4) := Nat.le_mul_of_pos_left _ h6
    omega

/-! ### Stage 2b: Counting gate multiplicities across sorted masks -/

private def normGates (x : SymAndInstance) : List (List Bool) :=
  x.gates.map fun g => (List.range x.n).map fun i => g.getD i false

private theorem gateSet_normGate (n : ℕ) (g : List Bool) :
    Finset.univ.filter (fun i : Fin n =>
      ((List.range n).map fun j => g.getD j false).getD i.1 false = true) =
      gateSet n g := by
  ext i
  simp [gateSet, List.getD_eq_getElem?_getD]

private theorem normGate_eq_maskBits_iff {n : ℕ} {g : List Bool} {k : ℕ} (_hk : k < 2 ^ n) :
    ((List.range n).map fun i => g.getD i false) = maskBits n k ↔ gateSet n g = maskSet n k := by
  constructor
  · intro heq
    rw [← gateSet_normGate n g, heq]
    ext i
    simp [maskBits, mem_maskSet, List.getD_eq_getElem?_getD]
  · intro heq
    refine List.ext_getElem (by simp [maskBits]) fun i hi1 hi2 => ?_
    have hin : i < n := by simpa using hi1
    have hmem : (⟨i, hin⟩ : Fin n) ∈ gateSet n g ↔ (⟨i, hin⟩ : Fin n) ∈ maskSet n k := by
      rw [heq]
    simp only [gateSet, Finset.mem_filter, Finset.mem_univ, true_and, mem_maskSet] at hmem
    simp only [maskBits, List.getD_eq_getElem?_getD,
      List.getElem_map, List.getElem_range] at hmem ⊢
    exact Bool.eq_iff_iff.2 hmem

private def taggedMasks (x : SymAndInstance) : List (List Bool × Bool) :=
  (normGates x).map (·, false) ++ (allMasks x.n).map (·, true)

private def countEmitted : ℕ → List (List Bool × Bool) → List ℕ
  | _, [] => []
  | cnt, p :: rest => if p.2 then cnt :: countEmitted 0 rest else countEmitted (cnt + 1) rest

private def countMasks (x : SymAndInstance) : List ℕ :=
  countEmitted 0 (radixSortLSB x.n (taggedMasks x))

private theorem countEmitted_append (c : ℕ) (l₁ l₂ : List (List Bool × Bool))
    (hl₁ : ∀ p ∈ l₁, p.2 = false) :
    countEmitted c (l₁ ++ l₂) = countEmitted (c + l₁.length) l₂ := by
  induction l₁ generalizing c with
  | nil => simp
  | cons a t ih =>
    have ha : a.2 = false := hl₁ a (List.mem_cons_self ..)
    have ht := ih (c + 1) fun p hp => hl₁ p (List.mem_cons_of_mem _ hp)
    simp only [List.cons_append, countEmitted, ha, Bool.false_eq_true, ↓reduceIte,
      List.length_cons]
    rw [ht]
    ring_nf

private theorem countEmitted_flatMap_eq (buckets : List (List (List Bool × Bool)))
    (hb : ∀ l ∈ buckets, ∃ l₀ : List (List Bool × Bool), ∃ m : List Bool,
      (∀ p ∈ l₀, p.2 = false) ∧ l = l₀ ++ [(m, true)]) :
    countEmitted 0 (buckets.flatMap id) =
      buckets.map (fun l => (l.filter (fun p => !p.2)).length) := by
  induction buckets with
  | nil => rfl
  | cons l rest ih =>
    obtain ⟨l₀, m, hl₀, rfl⟩ := hb l (List.mem_cons_self ..)
    have hrest := ih fun l' hl' => hb l' (List.mem_cons_of_mem _ hl')
    rw [List.flatMap_cons, id_eq, List.append_assoc, countEmitted_append 0 l₀ _ hl₀,
      Nat.zero_add, List.singleton_append, countEmitted, ite_eq_left rfl, hrest]
    congr 1
    have hf : (l₀ ++ [(m, true)]).filter (fun p => !p.2) = l₀ := by
      rw [List.filter_append]
      have h1 : l₀.filter (fun p => !p.2) = l₀ :=
        List.filter_eq_self.2 fun p hp => by simp [hl₀ p hp]
      simp [h1]
    change l₀.length = ((l₀ ++ [(m, true)]).filter (fun p => !p.2)).length
    rw [hf]

private theorem countMasks_eq (x : SymAndInstance) :
    countMasks x = (List.range (2 ^ x.n)).map fun k =>
      (x.gates.map (gateSet x.n)).count (maskSet x.n k) := by
  rw [countMasks, radixSortLSB_eq]
  have heq : (List.range (2 ^ x.n)).flatMap
      (fun k => (taggedMasks x).filter fun p => evalBits x.n p.1 == k) =
      ((List.range (2 ^ x.n)).map fun k =>
        (taggedMasks x).filter fun p => evalBits x.n p.1 == k).flatMap id := by
    rw [List.flatMap_map]; rfl
  rw [heq, countEmitted_flatMap_eq]
  · rw [List.map_map]
    refine List.map_congr_left fun k hk => ?_
    have hk_lt : k < 2 ^ x.n := List.mem_range.1 hk
    have hfalse : (((normGates x).map (·, false)).filter
        fun p => evalBits x.n p.1 == k).length =
        (x.gates.map (gateSet x.n)).count (maskSet x.n k) := by
      rw [normGates, List.map_map]
      induction x.gates with
      | nil => simp
      | cons g gs ih =>
        have hlen : ((List.range x.n).map fun i => g.getD i false).length = x.n := by simp
        have hmb : (maskBits x.n k).length = x.n := length_maskBits x.n k
        have hev : evalBits x.n ((List.range x.n).map fun i => g.getD i false) = k ↔
            gateSet x.n g = maskSet x.n k := by
          rw [← normGate_eq_maskBits_iff hk_lt]
          constructor
          · intro h
            exact evalBits_of_len_eq hlen hmb (h.trans (evalBits_maskBits x.n k hk_lt).symm)
          · intro h; rw [h, evalBits_maskBits x.n k hk_lt]
        simp only [List.map_cons, Function.comp_apply, List.filter_cons, List.count_cons,
          beq_iff_eq] at ih ⊢
        simp only [List.getD_eq_getElem?_getD] at ih
        by_cases h : gateSet x.n g = maskSet x.n k
        · have h1 : evalBits x.n ((List.range x.n).map fun i => g.getD i false) = k := hev.2 h
          simp only [List.getD_eq_getElem?_getD] at h1
          simp [h, h1, ih]
        · have h1 : evalBits x.n ((List.range x.n).map fun i => g.getD i false) ≠ k :=
            fun h' => h (hev.1 h')
          simp only [List.getD_eq_getElem?_getD] at h1
          simp [h, h1, ih]
    simp only [Function.comp_apply, taggedMasks, List.filter_append, List.filter_filter]
    have hf1 : ((normGates x).map (·, false)).filter
        (fun p => !p.2 && (evalBits x.n p.1 == k)) =
        ((normGates x).map (·, false)).filter (fun p => evalBits x.n p.1 == k) := by
      refine List.filter_congr fun p hp => ?_
      rw [List.mem_map] at hp
      obtain ⟨_, _, rfl⟩ := hp
      simp
    have hf2 : ((allMasks x.n).map (·, true)).filter
        (fun p => !p.2 && (evalBits x.n p.1 == k)) = [] :=
      List.filter_eq_nil_iff.2 fun p hp => by
        rw [List.mem_map] at hp; obtain ⟨_, _, rfl⟩ := hp; simp
    rw [hf1, hf2, List.append_nil]
    exact hfalse
  · intro l hl
    rw [List.mem_map] at hl
    obtain ⟨k, hk, rfl⟩ := hl
    have hk_lt : k < 2 ^ x.n := List.mem_range.1 hk
    refine ⟨((normGates x).map (·, false)).filter (fun p => evalBits x.n p.1 == k),
      maskBits x.n k, fun p hp => ?_, ?_⟩
    · rw [List.mem_filter, List.mem_map] at hp
      obtain ⟨⟨_, _, rfl⟩, _⟩ := hp
      rfl
    · simp only [taggedMasks, List.filter_append]
      congr 1
      rw [allMasks_eq, List.map_map, List.filter_map]
      change ((List.range (2 ^ x.n)).filter
          (fun j => evalBits x.n (maskBits x.n j) == k)).map (fun j => (maskBits x.n j, true)) =
        [(maskBits x.n k, true)]
      have hsplit : List.range (2 ^ x.n) =
          List.range k ++ ([k] ++ (List.range (2 ^ x.n - k - 1)).map (· + (k + 1))) := by
        have h1 : 2 ^ x.n = k + (1 + (2 ^ x.n - k - 1)) := by omega
        conv_lhs => rw [h1, List.range_add]
        congr 1
        rw [List.range_add, List.map_append, List.range_one, List.map_singleton, Nat.add_zero]
        congr 1
        rw [List.map_map]
        refine List.map_congr_left fun t _ => ?_
        dsimp only [Function.comp_apply]
        omega
      have hf : (List.range (2 ^ x.n)).filter
          (fun j => evalBits x.n (maskBits x.n j) == k) = [k] := by
        rw [hsplit, List.filter_append, List.filter_append]
        have hlt_nil : (List.range k).filter
            (fun j => evalBits x.n (maskBits x.n j) == k) = [] :=
          List.filter_eq_nil_iff.2 fun j hj => by
            have hj_lt : j < k := List.mem_range.1 hj
            simp only [beq_iff_eq]
            rw [evalBits_maskBits x.n j (hj_lt.trans hk_lt)]
            omega
        have hgt_nil : ((List.range (2 ^ x.n - k - 1)).map (· + (k + 1))).filter
            (fun j => evalBits x.n (maskBits x.n j) == k) = [] :=
          List.filter_eq_nil_iff.2 fun j hj => by
            rw [List.mem_map] at hj
            obtain ⟨t, ht, rfl⟩ := hj
            have ht_lt : t < 2 ^ x.n - k - 1 := List.mem_range.1 ht
            simp only [beq_iff_eq]
            rw [evalBits_maskBits x.n (t + (k + 1)) (by omega)]
            omega
        rw [hlt_nil, hgt_nil]
        simp only [List.nil_append, List.append_nil, List.filter_cons, List.filter_nil,
          evalBits_maskBits x.n k hk_lt, beq_self_eq_true, ↓reduceIte]
      rw [hf, List.map_singleton]

private theorem two_pow_mul_log2_pow_le (n s d : ℕ) :
    2 ^ n * (Nat.log2 s + 2) ^ d ≤ (2 ^ n + (s + 2) ^ (d + 1)) * (n + 2) ^ d := by
  by_cases h : Nat.log2 s ≤ n
  · calc 2 ^ n * (Nat.log2 s + 2) ^ d
        ≤ 2 ^ n * (n + 2) ^ d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) d)
      _ ≤ (2 ^ n + (s + 2) ^ (d + 1)) * (n + 2) ^ d := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  · have hlt : n < Nat.log2 s := by omega
    have hs_pos : s ≠ 0 := by rintro rfl; simp at hlt
    have hpow : 2 ^ n ≤ s :=
      (Nat.pow_le_pow_right (by decide) hlt.le).trans (Nat.log2_self_le hs_pos)
    have hlog : Nat.log2 s ≤ s := Nat.lt_two_pow_self.le.trans (Nat.log2_self_le hs_pos)
    have h1 : 1 ≤ (n + 2) ^ d := Nat.one_le_pow _ _ (by omega)
    calc 2 ^ n * (Nat.log2 s + 2) ^ d
        ≤ s * (s + 2) ^ d := Nat.mul_le_mul hpow (Nat.pow_le_pow_left (by omega) d)
      _ ≤ (s + 2) * (s + 2) ^ d := Nat.mul_le_mul_right _ (by omega)
      _ = (s + 2) ^ (d + 1) := by ring
      _ ≤ 2 ^ n + (s + 2) ^ (d + 1) := Nat.le_add_left _ _
      _ ≤ (2 ^ n + (s + 2) ^ (d + 1)) * (n + 2) ^ d := Nat.le_mul_of_pos_right _ h1

private theorem gates_length_le_encSymAndInstance (x : SymAndInstance) :
    x.gates.length ≤ (encSymAndInstance x).length := by
  rw [encSymAndInstance_apply, encSymAndInstanceFields, length_encPair]
  dsimp only
  have h1 := length_le_length_encList encBits x.gates
  omega

private theorem n_le_encSymAndInstance (x : SymAndInstance) :
    x.n ≤ (encSymAndInstance x).length := by
  rw [encSymAndInstance_apply, encSymAndInstanceFields, length_encPair]
  dsimp only
  have h1 : x.n ≤ (encUnary x.n).length := by simp [encUnary_apply]
  omega

private theorem countMasks_length (x : SymAndInstance) : (countMasks x).length = 2 ^ x.n := by
  rw [countMasks_eq, List.length_map, List.length_range]

private theorem countMasks_mem_le (x : SymAndInstance) {v : ℕ} (hv : v ∈ countMasks x) :
    v ≤ x.gates.length := by
  rw [countMasks_eq, List.mem_map] at hv
  obtain ⟨k, _, rfl⟩ := hv
  exact (List.count_le_length).trans (by simp)

private theorem streamMap_streamEmit {α β : Type} (encB : β ↪ List Bool) (f : α → β)
    (L : List α) :
    encList encB (L.map f) =
      streamEmit (fun q : Unit × α => q.1) (fun q => encList encB [f q.2]) () L := by
  induction L with
  | nil => rfl
  | cons a t ih => simp [List.map_cons, streamEmit, encList_cons, ih]

private theorem computableInO_streamMap {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    (f : α → β) (hf : ComputableInPolyTime f encA encB) :
    ∃ d, ComputableInO (List.map f) (encList encA) (encList encB)
      (fun L => (encList encA L).length +
        (L.length + 1) * (listMax (fun a => (encA a).length) L + 1) ^ d)
      (fun L => (encList encA L).length +
        (L.length + 1) * (listMax (fun a => (encA a).length) L + 1) ^ d) := by
  have hnext : ComputableInPolyTime (fun q : Unit × α => q.1)
      (encPair encUnit encA) encUnit := by fun_prop
  have hemit : ComputableInPolyTime (fun q : Unit × α => [f q.2])
      (encPair encUnit encA) (encList encB) :=
    (hf.comp (snd encUnit encA)).cons' (const [])
  obtain ⟨c, d, h⟩ := ComputableInTimeAndSpace.streamFold_pair_list
    (encA := encA) (encS := encUnit) (encB := encB)
    (encIn := encPair encUnit (encList encA))
    (init := Prod.fst) (elems := Prod.snd) (fun _ => rfl) hnext hemit
    (g := fun q : Unit × List α => q.2.map f)
    (fun q => streamMap_streamEmit encB f q.2)
    (lMax := fun q => listMax (fun a => (encA a).length) q.2 + 2)
    (fun q j _ => by
      have hst : streamState q.1 (fun p : Unit × α => p.1) q.2 j = () := by
        cases q.1
        induction (q.2.take j) with
        | nil => rfl
        | cons _ _ _ => simp [streamState]
      change (encUnit (streamState q.1 _ q.2 j)).length ≤ _
      rw [hst, encUnit_apply, List.length_nil]; omega)
    (fun q j hj => (le_listMax (f := fun a => (encA a).length) (List.getElem_mem hj)).trans
      (by omega))
  obtain ⟨d_out, _, hdeg⟩ := hf.exists_degree
  obtain ⟨c_out, hc_out⟩ := hdeg.inO.length_le
  let D := max d d_out
  have hlen_aux : ∀ (M : ℕ) (l : List α), (∀ a ∈ l, (encA a).length ≤ M) →
      (encList encB (l.map f)).length ≤ l.length * (4 * c_out * (M + 1) ^ d_out + 1) := by
    intro M l hl
    induction l with
    | nil => simp
    | cons a t ih =>
      have ha : (encA a).length ≤ M := hl a (List.mem_cons_self ..)
      have ht := ih fun b hb => hl b (List.mem_cons_of_mem _ hb)
      have hf_le : (encB (f a)).length ≤ c_out * ((M + 1) ^ d_out + 1) := by
        have h1 := hc_out a
        have h2 : ((encA a).length + 1) ^ d_out ≤ (M + 1) ^ d_out :=
          Nat.pow_le_pow_left (by omega) d_out
        exact h1.trans (Nat.mul_le_mul_left _ (by omega))
      have hpow1 : 1 ≤ (M + 1) ^ d_out := Nat.one_le_pow _ _ (Nat.succ_pos _)
      have helem : (encB (f a)).length ≤ 2 * c_out * (M + 1) ^ d_out := by
        calc (encB (f a)).length ≤ c_out * ((M + 1) ^ d_out + 1) := hf_le
          _ ≤ c_out * (2 * (M + 1) ^ d_out) := Nat.mul_le_mul_left _ (by omega)
          _ = 2 * c_out * (M + 1) ^ d_out := by ring
      rw [List.map_cons, encList_cons, List.length_append, List.length_cons, length_frame]
      have hmul : (t.length + 1) * (4 * c_out * (M + 1) ^ d_out + 1) =
          t.length * (4 * c_out * (M + 1) ^ d_out + 1) +
            (4 * c_out * (M + 1) ^ d_out + 1) := by ring
      have h2e : 2 * (2 * c_out * (M + 1) ^ d_out) = 4 * c_out * (M + 1) ^ d_out := by ring
      omega
  have hlen_map : ∀ L : List α,
      (encList encB (L.map f)).length ≤
        (4 * c_out + 1) * ((L.length + 1) * (listMax (fun a => (encA a).length) L + 1) ^ D) := by
    intro L
    have h1 := hlen_aux (listMax (fun a => (encA a).length) L) L
      (fun a ha => le_listMax (f := fun a => (encA a).length) ha)
    have hpow : (listMax (fun a => (encA a).length) L + 1) ^ d_out ≤
        (listMax (fun a => (encA a).length) L + 1) ^ D :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_right d d_out)
    have hpow1 : 1 ≤ (listMax (fun a => (encA a).length) L + 1) ^ D :=
      Nat.one_le_pow _ _ (Nat.succ_pos _)
    have hstep1 : 4 * c_out * (listMax (fun a => (encA a).length) L + 1) ^ d_out + 1 ≤
        (4 * c_out + 1) * (listMax (fun a => (encA a).length) L + 1) ^ D := by
      have : 4 * c_out * (listMax (fun a => (encA a).length) L + 1) ^ d_out ≤
          4 * c_out * (listMax (fun a => (encA a).length) L + 1) ^ D :=
        Nat.mul_le_mul_left _ hpow
      nlinarith
    calc (encList encB (L.map f)).length
        ≤ L.length * (4 * c_out * (listMax (fun a => (encA a).length) L + 1) ^ d_out + 1) := h1
      _ ≤ (L.length + 1) * ((4 * c_out + 1) *
            (listMax (fun a => (encA a).length) L + 1) ^ D) :=
          Nat.mul_le_mul (Nat.le_succ _) hstep1
      _ = (4 * c_out + 1) *
            ((L.length + 1) * (listMax (fun a => (encA a).length) L + 1) ^ D) := by ring
  have hwrap : ComputableInO (fun L : List α => ((), L))
      (encList encA) (encPair encUnit (encList encA))
      (fun L => (encList encA L).length) (fun L => (encList encA L).length) := by
    have hp := (ComputableInO.constZero (encIn := encList encA) (encMid := encUnit) ()).prod
      (ComputableInO.id' (encMid := encList encA))
    exact hp.mono 2 (fun _ => by omega) (fun _ => by omega)
  have hraw : ComputableInO (fun q : Unit × List α => q.2.map f)
      (encPair encUnit (encList encA)) (encList encB)
      (fun q => (encList encA q.2).length +
        (q.2.length + 1) * (listMax (fun a => (encA a).length) q.2 + 1) ^ D)
      (fun q => (encList encA q.2).length +
        (q.2.length + 1) * (listMax (fun a => (encA a).length) q.2 + 1) ^ D) := by
    have hpow : ∀ L : List α, (listMax (fun a => (encA a).length) L + 3) ^ d ≤
        3 ^ d * (listMax (fun a => (encA a).length) L + 1) ^ D := fun L => by
      calc (listMax (fun a => (encA a).length) L + 3) ^ d
          ≤ (3 * (listMax (fun a => (encA a).length) L + 1)) ^ d :=
            Nat.pow_le_pow_left (by omega) d
        _ = 3 ^ d * (listMax (fun a => (encA a).length) L + 1) ^ d := Nat.mul_pow _ _ _
        _ ≤ 3 ^ d * (listMax (fun a => (encA a).length) L + 1) ^ D :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_left d d_out))
    refine ComputableInO.of_bounds h (2 * c * 3 ^ d + 4 * c_out + 4) (fun q => ?_) (fun q => ?_)
      (fun q => ?_)
    · rw [length_encPair, encUnit_apply, List.length_nil]
      have hmul : (q.2.length + 1) * (listMax (fun a => (encA a).length) q.2 + 3) ^ d ≤
          3 ^ d * ((q.2.length + 1) * (listMax (fun a => (encA a).length) q.2 + 1) ^ D) := by
        calc (q.2.length + 1) * (listMax (fun a => (encA a).length) q.2 + 3) ^ d
            ≤ (q.2.length + 1) * (3 ^ d * (listMax (fun a => (encA a).length) q.2 + 1) ^ D) :=
              Nat.mul_le_mul_left _ (hpow q.2)
          _ = 3 ^ d * ((q.2.length + 1) *
                (listMax (fun a => (encA a).length) q.2 + 1) ^ D) := by ring
      set E := (encList encA q.2).length
      set B := (q.2.length + 1) * (listMax (fun a => (encA a).length) q.2 + 1) ^ D
      have h1pow : 1 ≤ B := Nat.mul_pos (Nat.succ_pos _) (Nat.one_le_pow _ _ (Nat.succ_pos _))
      have h3pow : 1 ≤ 3 ^ d := Nat.one_le_pow _ _ (by decide)
      have hsum : 2 * 0 + 1 + E +
          (q.2.length + 1) * (listMax (fun a => (encA a).length) q.2 + 3) ^ d + 1 ≤
          2 * 3 ^ d * (E + B + 1) := by
        calc 2 * 0 + 1 + E +
              (q.2.length + 1) * (listMax (fun a => (encA a).length) q.2 + 3) ^ d + 1
            ≤ E + 3 ^ d * B + 2 := by omega
          _ ≤ 2 * 3 ^ d * (E + B + 1) := by nlinarith
      calc c * (2 * 0 + 1 + E +
            (q.2.length + 1) * (listMax (fun a => (encA a).length) q.2 + 3) ^ d + 1)
          ≤ c * (2 * 3 ^ d * (E + B + 1)) := Nat.mul_le_mul_left _ hsum
        _ ≤ (2 * c * 3 ^ d + 4 * c_out + 4) * (E + B + 1) := by nlinarith
    · have h1 : (listMax (fun a => (encA a).length) q.2 + 1) ^ D ≤
          (q.2.length + 1) * (listMax (fun a => (encA a).length) q.2 + 1) ^ D :=
        Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
      set E := (encList encA q.2).length
      set B := (q.2.length + 1) * (listMax (fun a => (encA a).length) q.2 + 1) ^ D
      have h3pow_B : (listMax (fun a => (encA a).length) q.2 + 2 + 1) ^ d ≤ 3 ^ d * B := by
        have h9 : listMax (fun a => (encA a).length) q.2 + 2 + 1 =
            listMax (fun a => (encA a).length) q.2 + 3 := by omega
        rw [h9]
        exact (hpow q.2).trans (Nat.mul_le_mul_left _ h1)
      have h1pow : 1 ≤ B := Nat.mul_pos (Nat.succ_pos _) (Nat.one_le_pow _ _ (Nat.succ_pos _))
      have h3pow : 1 ≤ 3 ^ d := Nat.one_le_pow _ _ (by decide)
      have hsum : (listMax (fun a => (encA a).length) q.2 + 2 + 1) ^ d + 1 ≤
          2 * 3 ^ d * (E + B + 1) := by
        calc (listMax (fun a => (encA a).length) q.2 + 2 + 1) ^ d + 1
            ≤ 3 ^ d * B + 1 := Nat.add_le_add_right h3pow_B 1
          _ ≤ 2 * 3 ^ d * (E + B + 1) := by nlinarith
      calc c * ((listMax (fun a => (encA a).length) q.2 + 2 + 1) ^ d + 1)
          ≤ c * (2 * 3 ^ d * (E + B + 1)) := Nat.mul_le_mul_left _ hsum
        _ ≤ (2 * c * 3 ^ d + 4 * c_out + 4) * (E + B + 1) := by nlinarith
    · have hm := hlen_map q.2
      set E := (encList encA q.2).length
      set B := (q.2.length + 1) * (listMax (fun a => (encA a).length) q.2 + 1) ^ D
      calc (encList encB (q.2.map f)).length
          ≤ (4 * c_out + 1) * B := hm
        _ ≤ (2 * c * 3 ^ d + 4 * c_out + 4) * (E + B + 1) :=
            Nat.mul_le_mul (by omega) (by omega)
  exact ⟨D, (hraw.comp hwrap).mono 2 (fun _ => by dsimp; omega) (fun _ => by dsimp; omega)⟩

private theorem countEmitted_streamEmit (c : ℕ) (L : List (List Bool × Bool)) :
    encList encNat (countEmitted c L) =
      streamEmit (fun q : ℕ × (List Bool × Bool) => if q.2.2 then 0 else q.1 + 1)
        (fun q => encList encNat (if q.2.2 then [q.1] else [])) c L := by
  induction L generalizing c with
  | nil => rfl
  | cons a t ih =>
    rw [countEmitted, streamEmit]
    cases h : a.2 <;> simp only [Bool.false_eq_true, ↓reduceIte, encList_cons, encList_nil,
      List.nil_append, List.append_nil, ih]

private theorem streamState_count_le (c : ℕ) (L : List (List Bool × Bool)) (j : ℕ) :
    streamState c (fun q : ℕ × (List Bool × Bool) => if q.2.2 then 0 else q.1 + 1) L j ≤
      c + L.length := by
  have htake : ∀ xs : List (List Bool × Bool), ∀ s : ℕ,
      xs.foldl (fun st p => if p.2 then 0 else st + 1) s ≤ s + xs.length := by
    intro xs s
    induction xs generalizing s with
    | nil => simp
    | cons a t ih =>
      simp only [List.foldl_cons, List.length_cons]
      cases ha : a.2
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have := ih (s + 1); omega
      · simp only [↓reduceIte]
        have := ih 0; omega
  exact (htake (L.take j) c).trans (by rw [List.length_take]; omega)

private theorem length_encNat_mul_pow_le (n m : ℕ) :
    (encNat (2 ^ n * (m + 1))).length ≤ n + Nat.log2 (m + 1) + 1 := by
  rw [encNat_apply, Nat.size_eq_bits_len, Nat.size_le]
  have hm : m + 1 < 2 ^ (Nat.log2 (m + 1) + 1) := by
    rw [Nat.log2_eq_log_two]
    exact Nat.lt_pow_succ_log_self (by decide : 1 < 2) (m + 1)
  calc 2 ^ n * (m + 1) < 2 ^ n * 2 ^ (Nat.log2 (m + 1) + 1) :=
        Nat.mul_lt_mul_of_pos_left hm (Nat.two_pow_pos n)
    _ = 2 ^ (n + Nat.log2 (m + 1) + 1) := by rw [← pow_add, Nat.add_assoc]

private theorem log2_mono {a b : ℕ} (h : a ≤ b) : Nat.log2 a ≤ Nat.log2 b := by
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
  exact Nat.log_mono_right h

private theorem radix_log_absorb (n A k : ℕ) (hA : 1 ≤ A) :
    (2 ^ n + A) * (Nat.log2 A + 2) ^ k ≤
      2 * 3 ^ (k + 1) * 2 ^ k * (2 ^ n + A ^ (k + 1)) * (n + 1) ^ k := by
  have h2m := two_pow_mul_log2_pow_le n A k
  have hlog_A : Nat.log2 A ≤ A := Nat.lt_two_pow_self.le.trans (Nat.log2_self_le (by omega))
  have hA_pow : A * (Nat.log2 A + 2) ^ k ≤ (A + 2) ^ (k + 1) := by
    calc A * (Nat.log2 A + 2) ^ k ≤ (A + 2) * (A + 2) ^ k :=
          Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) k)
      _ = (A + 2) ^ (k + 1) := by ring
  have hAd : (A + 2) ^ (k + 1) ≤ 3 ^ (k + 1) * A ^ (k + 1) := by
    calc (A + 2) ^ (k + 1) ≤ (3 * A) ^ (k + 1) := Nat.pow_le_pow_left (by omega) _
      _ = 3 ^ (k + 1) * A ^ (k + 1) := Nat.mul_pow _ _ _
  have hn2 : (n + 2) ^ k ≤ 2 ^ k * (n + 1) ^ k := by
    calc (n + 2) ^ k ≤ (2 * (n + 1)) ^ k := Nat.pow_le_pow_left (by omega) _
      _ = 2 ^ k * (n + 1) ^ k := Nat.mul_pow _ _ _
  have hn1 : 1 ≤ (n + 1) ^ k := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hc1 : 1 ≤ 3 ^ (k + 1) := Nat.one_le_pow _ _ (by decide)
  have hc2 : 1 ≤ 2 ^ k := Nat.one_le_pow _ _ (by decide)
  have hstep1 : (2 ^ n + (A + 2) ^ (k + 1)) * (n + 2) ^ k ≤
      3 ^ (k + 1) * 2 ^ k * ((2 ^ n + A ^ (k + 1)) * (n + 1) ^ k) := by
    have h2pow : 2 ^ n + (A + 2) ^ (k + 1) ≤ 3 ^ (k + 1) * (2 ^ n + A ^ (k + 1)) := by
      calc 2 ^ n + (A + 2) ^ (k + 1)
          ≤ 3 ^ (k + 1) * 2 ^ n + 3 ^ (k + 1) * A ^ (k + 1) :=
            Nat.add_le_add (Nat.le_mul_of_pos_left _ hc1) hAd
        _ = 3 ^ (k + 1) * (2 ^ n + A ^ (k + 1)) := by ring
    calc (2 ^ n + (A + 2) ^ (k + 1)) * (n + 2) ^ k
        ≤ (3 ^ (k + 1) * (2 ^ n + A ^ (k + 1))) * (2 ^ k * (n + 1) ^ k) :=
          Nat.mul_le_mul h2pow hn2
      _ = 3 ^ (k + 1) * 2 ^ k * ((2 ^ n + A ^ (k + 1)) * (n + 1) ^ k) := by ring
  have hstep2 : (A + 2) ^ (k + 1) ≤
      3 ^ (k + 1) * 2 ^ k * ((2 ^ n + A ^ (k + 1)) * (n + 1) ^ k) := by
    calc (A + 2) ^ (k + 1) ≤ 3 ^ (k + 1) * A ^ (k + 1) := hAd
      _ ≤ 3 ^ (k + 1) * ((2 ^ n + A ^ (k + 1)) * (n + 1) ^ k) :=
          Nat.mul_le_mul_left _ ((Nat.le_add_left _ _).trans (Nat.le_mul_of_pos_right _ hn1))
      _ ≤ 3 ^ (k + 1) * 2 ^ k * ((2 ^ n + A ^ (k + 1)) * (n + 1) ^ k) := by
          rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hc2)
  rw [Nat.add_mul]
  nlinarith

private theorem fst_length_mem_taggedMasks {x : SymAndInstance} {p : List Bool × Bool}
    (hp : p ∈ taggedMasks x) : p.1.length = x.n := by
  rw [taggedMasks, List.mem_append, List.mem_map, List.mem_map] at hp
  rcases hp with ⟨g, hg, rfl⟩ | ⟨bs, hbs, rfl⟩
  · rw [normGates, List.mem_map] at hg
    obtain ⟨_, _, rfl⟩ := hg
    simp
  · rw [allMasks_eq, List.mem_map] at hbs
    obtain ⟨k, _, rfl⟩ := hbs
    exact length_maskBits x.n k

private theorem computableInO_countMasks_finish {c_s d_fold c_w : ℕ}
    (hwrap0 : ComputableInO (fun x : SymAndInstance => (0, radixSortLSB x.n (taggedMasks x)))
      encSymAndInstance (encPair encNat (encList (encPair encBits encBool)))
      (fun x => (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ c_s) * (x.n + 1) ^ c_s)
      (fun x => (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ c_s) * (x.n + 1) ^ c_s))
    (hfold : ComputableInO (fun q : ℕ × List (List Bool × Bool) => countEmitted q.1 q.2)
      (encPair encNat (encList (encPair encBits encBool))) (encList encNat)
      (fun q => (encPair encNat (encList (encPair encBits encBool)) q).length +
        (q.2.length + 1) * (Nat.log2 (q.1 + q.2.length + 1) +
          2 * listMax (fun p : List Bool × Bool => p.1.length) q.2 + 9) ^ d_fold + 1)
      (fun q => (Nat.log2 (q.1 + q.2.length + 1) +
          2 * listMax (fun p : List Bool × Bool => p.1.length) q.2 + 9) ^ d_fold +
        (q.2.length + 1) * (Nat.log2 (q.1 + q.2.length + 1) + 2) + 1))
    (hwrap0_len : ∀ x : SymAndInstance,
      (encPair encNat (encList (encPair encBits encBool))
        (0, radixSortLSB x.n (taggedMasks x))).length ≤
        c_w * ((2 ^ x.n + ((encSymAndInstance x).length + 1) ^ c_s) * (x.n + 1) ^ c_s + 1))
    (hlen_sort : ∀ x : SymAndInstance,
      (radixSortLSB x.n (taggedMasks x)).length = x.gates.length + 2 ^ x.n)
    (hmem_sort : ∀ x : SymAndInstance,
      ∀ p ∈ radixSortLSB x.n (taggedMasks x), p ∈ taggedMasks x) :
    ∃ c, ComputableInO countMasks encSymAndInstance (encList encNat)
      (fun x => (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ c) * (x.n + 1) ^ c)
      (fun x => (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ c) * (x.n + 1) ^ c) := by
  have hcomb := hfold.comp hwrap0
  let D_f := max d_fold 1
  let C_fin := c_s + 2 * D_f + 4
  have hmain_le : ∀ x : SymAndInstance,
      (0 + (radixSortLSB x.n (taggedMasks x)).length + 1) *
          (Nat.log2 (0 + (radixSortLSB x.n (taggedMasks x)).length + 1) +
            2 * listMax (fun p : List Bool × Bool => p.1.length)
              (radixSortLSB x.n (taggedMasks x)) + 9) ^ D_f ≤
        30 ^ (D_f + 1) * ((2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_fin) *
          (x.n + 1) ^ C_fin) := fun x => by
    set L := radixSortLSB x.n (taggedMasks x)
    set A := (encSymAndInstance x).length + 1
    set N := x.n + 1
    have hlen_l : L.length = x.gates.length + 2 ^ x.n := hlen_sort x
    have hg_le := gates_length_le_encSymAndInstance x
    have hlog_q : Nat.log2 (0 + L.length + 1) ≤ x.n + Nat.log2 A + 1 := by
      have hmul : L.length + 1 ≤ 2 ^ x.n * (A + 1) := by
        have h1 : 1 ≤ 2 ^ x.n := Nat.one_le_pow _ _ (by decide)
        have hga : x.gates.length + 1 ≤ 2 ^ x.n * A :=
          (by omega : x.gates.length + 1 ≤ A).trans (Nat.le_mul_of_pos_left _ h1)
        calc L.length + 1 = x.gates.length + 2 ^ x.n + 1 := by rw [hlen_l]
          _ ≤ 2 ^ x.n * A + 2 ^ x.n := by omega
          _ = 2 ^ x.n * (A + 1) := by ring
      have hlt : 0 + L.length + 1 < 2 ^ (x.n + Nat.log2 A + 2) := by
        have h2 : A + 1 < 2 ^ (Nat.log2 (A + 1) + 1) := by
          rw [Nat.log2_eq_log_two]
          exact Nat.lt_pow_succ_log_self (by decide : 1 < 2) (A + 1)
        have hA2 : Nat.log2 (A + 1) ≤ Nat.log2 A + 1 := by
          have hltA : A + 1 ≤ 2 * A := by omega
          have hle := log2_mono hltA
          have h2A : Nat.log2 (2 * A) = Nat.log2 A + 1 := Nat.log2_two_mul (by omega)
          omega
        calc 0 + L.length + 1
            ≤ 2 ^ x.n * (A + 1) := by omega
          _ < 2 ^ x.n * 2 ^ (Nat.log2 (A + 1) + 1) :=
              Nat.mul_lt_mul_of_pos_left h2 (Nat.two_pow_pos _)
          _ = 2 ^ (x.n + (Nat.log2 (A + 1) + 1)) := by rw [← pow_add]
          _ ≤ 2 ^ (x.n + Nat.log2 A + 2) :=
              Nat.pow_le_pow_right (by decide) (by omega)
      by_contra hgt
      push Not at hgt
      have hgt' : x.n + Nat.log2 A + 2 ≤ Nat.log2 (0 + L.length + 1) := by omega
      have hle := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hgt'
      have hself : 2 ^ Nat.log2 (0 + L.length + 1) ≤ 0 + L.length + 1 :=
        Nat.log2_self_le (by omega)
      omega
    have hmax_p : listMax (fun p : List Bool × Bool => p.1.length) L ≤ x.n :=
      listMax_le fun p hp => (fst_length_mem_taggedMasks (hmem_sort x p hp)).le
    have hbase : Nat.log2 (0 + L.length + 1) +
          2 * listMax (fun p : List Bool × Bool => p.1.length) L + 9 ≤
        5 * N * (Nat.log2 A + 2) := by
      have h1 : 3 * x.n ≤ 5 * (x.n * (Nat.log2 A + 2)) := by
        have hmul_x : x.n * 2 ≤ x.n * (Nat.log2 A + 2) := Nat.mul_le_mul_left x.n (by omega)
        omega
      have h2 : 5 * N * (Nat.log2 A + 2) =
          5 * (x.n * (Nat.log2 A + 2)) + 5 * (Nat.log2 A + 2) := by
        dsimp only [N]; ring
      omega
    have hpow_b : (Nat.log2 (0 + L.length + 1) +
          2 * listMax (fun p : List Bool × Bool => p.1.length) L + 9) ^ D_f ≤
        5 ^ D_f * N ^ D_f * (Nat.log2 A + 2) ^ D_f := by
      calc _ ≤ (5 * N * (Nat.log2 A + 2)) ^ D_f := Nat.pow_le_pow_left hbase D_f
        _ = (5 * N) ^ D_f * (Nat.log2 A + 2) ^ D_f := Nat.mul_pow _ _ _
        _ = 5 ^ D_f * N ^ D_f * (Nat.log2 A + 2) ^ D_f := by rw [Nat.mul_pow]
    have h2l : 0 + L.length + 1 ≤ 2 ^ x.n + A := by
      rw [hlen_l]; omega
    have hlogA := radix_log_absorb x.n A D_f (Nat.succ_pos _)
    have hA_fin : A ^ (D_f + 1) ≤ A ^ C_fin :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (by dsimp only [C_fin]; omega)
    have hN_fin : N ^ (2 * D_f) ≤ N ^ C_fin :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (by dsimp only [C_fin]; omega)
    have hc30 : 5 ^ D_f * (2 * 3 ^ (D_f + 1) * 2 ^ D_f) ≤ 30 ^ (D_f + 1) := by
      have h1 : 5 ^ D_f * (2 * 3 ^ (D_f + 1) * 2 ^ D_f) =
          6 * (5 ^ D_f * 2 ^ D_f * 3 ^ D_f) := by ring
      rw [← Nat.mul_pow, ← Nat.mul_pow, show 5 * 2 * 3 = 30 from rfl] at h1
      have h2 : 30 ^ (D_f + 1) = 30 * 30 ^ D_f := by ring
      omega
    calc (0 + L.length + 1) *
            (Nat.log2 (0 + L.length + 1) +
              2 * listMax (fun p : List Bool × Bool => p.1.length) L + 9) ^ D_f
        ≤ (2 ^ x.n + A) * (5 ^ D_f * N ^ D_f * (Nat.log2 A + 2) ^ D_f) :=
            Nat.mul_le_mul h2l hpow_b
      _ = 5 ^ D_f * N ^ D_f * ((2 ^ x.n + A) * (Nat.log2 A + 2) ^ D_f) := by ring
      _ ≤ 5 ^ D_f * N ^ D_f *
            (2 * 3 ^ (D_f + 1) * 2 ^ D_f * (2 ^ x.n + A ^ (D_f + 1)) * N ^ D_f) :=
            Nat.mul_le_mul_left _ hlogA
      _ = (5 ^ D_f * (2 * 3 ^ (D_f + 1) * 2 ^ D_f)) *
            ((2 ^ x.n + A ^ (D_f + 1)) * N ^ (2 * D_f)) := by ring
      _ ≤ 30 ^ (D_f + 1) * ((2 ^ x.n + A ^ C_fin) * N ^ C_fin) :=
            Nat.mul_le_mul hc30 (Nat.mul_le_mul (Nat.add_le_add_left hA_fin _) hN_fin)
  have hcm_fin : ∀ x : SymAndInstance,
      let L := radixSortLSB x.n (taggedMasks x)
      (Nat.log2 (0 + L.length + 1) +
          2 * listMax (fun p : List Bool × Bool => p.1.length) L + 9) ^ d_fold ≤
        (Nat.log2 (0 + L.length + 1) +
          2 * listMax (fun p : List Bool × Bool => p.1.length) L + 9) ^ D_f ∧
      (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ c_s) * (x.n + 1) ^ c_s ≤
        (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_fin) * (x.n + 1) ^ C_fin ∧
      1 ≤ (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_fin) * (x.n + 1) ^ C_fin := fun x =>
    ⟨Nat.pow_le_pow_right (by omega) (le_max_left _ _),
      Nat.mul_le_mul (Nat.add_le_add_left
        (Nat.pow_le_pow_right (Nat.succ_pos _) (by dsimp only [C_fin]; omega)) _)
        (Nat.pow_le_pow_right (Nat.succ_pos _) (by dsimp only [C_fin]; omega)),
      Nat.mul_pos (Nat.add_pos_left (Nat.two_pow_pos _) _) (Nat.pow_pos (Nat.succ_pos _))⟩
  refine ⟨C_fin, hcomb.mono (2 * c_w + 4 * 30 ^ (D_f + 1) + 8) (fun x => ?_) (fun x => ?_)⟩
  · set L := radixSortLSB x.n (taggedMasks x)
    set A := (encSymAndInstance x).length + 1
    set N := x.n + 1
    set B := (2 ^ x.n + A ^ C_fin) * N ^ C_fin
    have hlen_w := hwrap0_len x
    have hml : (0 + L.length + 1) *
          (Nat.log2 (0 + L.length + 1) +
            2 * listMax (fun p : List Bool × Bool => p.1.length) L + 9) ^ D_f ≤
        30 ^ (D_f + 1) * B := hmain_le x
    obtain ⟨hpow_df, hwrap_le, hbox_pos⟩ := hcm_fin x
    change (Nat.log2 (0 + L.length + 1) +
        2 * listMax (fun p : List Bool × Bool => p.1.length) L + 9) ^ d_fold ≤
      (Nat.log2 (0 + L.length + 1) +
        2 * listMax (fun p : List Bool × Bool => p.1.length) L + 9) ^ D_f at hpow_df
    change (2 ^ x.n + A ^ c_s) * N ^ c_s ≤ B at hwrap_le
    change 1 ≤ B at hbox_pos
    have hmul_df : (L.length + 1) * (Nat.log2 (0 + L.length + 1) +
          2 * listMax (fun p : List Bool × Bool => p.1.length) L + 9) ^ d_fold ≤
        30 ^ (D_f + 1) * B := by
      calc (L.length + 1) * _ = (0 + L.length + 1) * _ := by simp only [Nat.zero_add]
        _ ≤ (0 + L.length + 1) * _ := Nat.mul_le_mul_left _ hpow_df
        _ ≤ 30 ^ (D_f + 1) * B := hml
    have hlen_B : (encPair encNat (encList (encPair encBits encBool)) (0, L)).length ≤
        2 * c_w * B := by
      calc _ ≤ c_w * (B + 1) :=
            hlen_w.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right hwrap_le 1))
        _ ≤ c_w * (2 * B) := Nat.mul_le_mul_left _ (by linarith only [hbox_pos])
        _ = 2 * c_w * B := by ring
    have h30 : 1 ≤ 30 ^ (D_f + 1) := Nat.one_le_pow _ _ (by decide)
    have h30_B : B ≤ 30 ^ (D_f + 1) * B := Nat.le_mul_of_pos_left _ h30
    calc (2 ^ x.n + A ^ c_s) * N ^ c_s +
          ((encPair encNat (encList (encPair encBits encBool)) (0, L)).length +
            (L.length + 1) * (Nat.log2 (0 + L.length + 1) +
              2 * listMax (fun p : List Bool × Bool => p.1.length) L + 9) ^ d_fold + 1)
        ≤ B + (2 * c_w * B + 30 ^ (D_f + 1) * B + B) := by
          linarith only [hwrap_le, hlen_B, hmul_df, hbox_pos]
      _ ≤ 2 * c_w * B + 4 * 30 ^ (D_f + 1) * B + 8 * B := by
          have h1 : B + (2 * c_w * B + 30 ^ (D_f + 1) * B + B) ≤
              2 * c_w * B + 4 * (30 ^ (D_f + 1) * B) + 8 * B := by omega
          calc B + (2 * c_w * B + 30 ^ (D_f + 1) * B + B)
              ≤ 2 * c_w * B + 4 * (30 ^ (D_f + 1) * B) + 8 * B := h1
            _ = _ := by ring
      _ = (2 * c_w + 4 * 30 ^ (D_f + 1) + 8) * B := by ring
      _ ≤ (2 * c_w + 4 * 30 ^ (D_f + 1) + 8) * (B + 1) :=
          Nat.mul_le_mul_left _ (Nat.le_succ _)
  · set L := radixSortLSB x.n (taggedMasks x)
    set A := (encSymAndInstance x).length + 1
    set N := x.n + 1
    set B := (2 ^ x.n + A ^ C_fin) * N ^ C_fin
    have hml : (0 + L.length + 1) *
          (Nat.log2 (0 + L.length + 1) +
            2 * listMax (fun p : List Bool × Bool => p.1.length) L + 9) ^ D_f ≤
        30 ^ (D_f + 1) * B := hmain_le x
    obtain ⟨hpow_df, hwrap_le, hbox_pos⟩ := hcm_fin x
    change (Nat.log2 (0 + L.length + 1) +
        2 * listMax (fun p : List Bool × Bool => p.1.length) L + 9) ^ d_fold ≤
      (Nat.log2 (0 + L.length + 1) +
        2 * listMax (fun p : List Bool × Bool => p.1.length) L + 9) ^ D_f at hpow_df
    change (2 ^ x.n + A ^ c_s) * N ^ c_s ≤ B at hwrap_le
    change 1 ≤ B at hbox_pos
    have h1 : (Nat.log2 (0 + L.length + 1) +
          2 * listMax (fun p : List Bool × Bool => p.1.length) L + 9) ^ D_f ≤
        (0 + L.length + 1) *
          (Nat.log2 (0 + L.length + 1) +
            2 * listMax (fun p : List Bool × Bool => p.1.length) L + 9) ^ D_f :=
      Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    have h2 : (L.length + 1) * (Nat.log2 (0 + L.length + 1) + 2) ≤
        (0 + L.length + 1) *
          (Nat.log2 (0 + L.length + 1) +
            2 * listMax (fun p : List Bool × Bool => p.1.length) L + 9) ^ D_f := by
      refine Nat.mul_le_mul (by omega) ?_
      calc Nat.log2 (0 + L.length + 1) + 2
          ≤ (Nat.log2 (0 + L.length + 1) +
              2 * listMax (fun p : List Bool × Bool => p.1.length) L + 9) ^ 1 := by
              rw [pow_one]; omega
        _ ≤ _ := Nat.pow_le_pow_right (by omega) (le_max_right _ _)
    have hp1 : (Nat.log2 (0 + L.length + 1) +
          2 * listMax (fun p : List Bool × Bool => p.1.length) L + 9) ^ d_fold ≤
        30 ^ (D_f + 1) * B := (hpow_df.trans h1).trans hml
    have hp2 : (L.length + 1) * (Nat.log2 (0 + L.length + 1) + 2) ≤
        30 ^ (D_f + 1) * B := h2.trans hml
    calc (2 ^ x.n + A ^ c_s) * N ^ c_s +
          ((Nat.log2 (0 + L.length + 1) +
              2 * listMax (fun p : List Bool × Bool => p.1.length) L + 9) ^ d_fold +
            (L.length + 1) * (Nat.log2 (0 + L.length + 1) + 2) + 1)
        ≤ B + (30 ^ (D_f + 1) * B + 30 ^ (D_f + 1) * B + B) := by
          linarith only [hwrap_le, hp1, hp2, hbox_pos]
      _ ≤ 2 * c_w * B + 4 * 30 ^ (D_f + 1) * B + 8 * B := by
          have h1 : B + (30 ^ (D_f + 1) * B + 30 ^ (D_f + 1) * B + B) ≤
              2 * c_w * B + 4 * (30 ^ (D_f + 1) * B) + 8 * B := by omega
          calc B + (30 ^ (D_f + 1) * B + 30 ^ (D_f + 1) * B + B)
              ≤ 2 * c_w * B + 4 * (30 ^ (D_f + 1) * B) + 8 * B := h1
            _ = _ := by ring
      _ = (2 * c_w + 4 * 30 ^ (D_f + 1) + 8) * B := by ring
      _ ≤ (2 * c_w + 4 * 30 ^ (D_f + 1) + 8) * (B + 1) :=
          Nat.mul_le_mul_left _ (Nat.le_succ _)

private theorem pow_encNat_add_le (n d : ℕ) :
    ((encNat n).length + (2 * n + 8) + 1) ^ d ≤ 10 ^ d * (n + 1) ^ d := by
  have hlen_n : (encNat n).length ≤ n + 1 :=
    (length_encNat_le_of_lt_two_pow (Nat.lt_pow_self (a := 2) (by decide))).trans (Nat.le_succ _)
  calc ((encNat n).length + (2 * n + 8) + 1) ^ d
      ≤ (10 * (n + 1)) ^ d := Nat.pow_le_pow_left (by omega) d
    _ = 10 ^ d * (n + 1) ^ d := Nat.mul_pow _ _ _

private theorem computableInO_countMasks :
    ∃ c, ComputableInO countMasks encSymAndInstance (encList encNat)
      (fun x => (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ c) * (x.n + 1) ^ c)
      (fun x => (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ c) * (x.n + 1) ^ c) := by
  have hnorm : ComputableInPolyTime (fun x : SymAndInstance => (normGates x).map (·, false))
      encSymAndInstance (encList (encPair encBits encBool)) := by
    have hbody : ComputableInPolyTime
        (fun p : ℕ × List Bool => ((List.range p.1).map fun i => p.2.getD i false, false))
        (encPair encUnary encBits) (encPair encBits encBool) := by
      have hbits : ComputableInPolyTime
          (fun p : ℕ × List Bool => (List.range p.1).map fun i => p.2.getD i false)
          (encPair encUnary encBits) encBits := by
        have hget : ComputableInPolyTime (fun q : (ℕ × List Bool) × ℕ => q.1.2.getD q.2 false)
            (encPair (encPair encUnary encBits) encUnary) encBool := by fun_prop
        have hlist := ComputableInPolyTime.mapWithInput (f := fun (p : ℕ × List Bool) i =>
            p.2.getD i false) (ComputableInPolyTime.range.comp (fst encUnary encBits)) hget
        exact (ComputableInO.of_linear ComputableInDegree.listToBits).computableInPolyTime
          (PolyBounded.of_forall_le 1 1 (fun _ => by simp))
          (PolyBounded.of_forall_le 1 1 (fun _ => by simp)) |>.comp hlist
      exact hbits.prod (const false)
    have hgates : ComputableInPolyTime (fun x : SymAndInstance => x.gates)
        encSymAndInstance (encList encBits) := by fun_prop
    have hn : ComputableInPolyTime (fun x : SymAndInstance => x.n)
        encSymAndInstance encUnary := by fun_prop
    simpa [normGates, List.map_map, List.getD_eq_getElem?_getD, Function.comp_def] using
      mapWith hbody hn hgates
  obtain ⟨d₁, _, hdeg₁⟩ := hnorm.exists_degree
  have hleft : ComputableInO (fun x : SymAndInstance => (normGates x).map (·, false))
      encSymAndInstance (encList (encPair encBits encBool))
      (fun x => ((encSymAndInstance x).length + 1) ^ d₁)
      (fun x => ((encSymAndInstance x).length + 1) ^ d₁) := hdeg₁.inO
  obtain ⟨d_masks, hmasks⟩ := computableInO_allMasks
  obtain ⟨d_map, hmap_pair⟩ := computableInO_streamMap
    (fun bs : List Bool => (bs, true)) ((id' (encIn := encBits)).prod (const true))
  have hright_raw := hmap_pair.comp hmasks
  have hright : ComputableInO (fun x : SymAndInstance => (allMasks x.n).map (·, true))
      encSymAndInstance (encList (encPair encBits encBool))
      (fun x => (encSymAndInstance x).length + 2 ^ x.n * (x.n + 1) ^ (max d_masks d_map + 3))
      (fun x => (encSymAndInstance x).length + 2 ^ x.n * (x.n + 1) ^ (max d_masks d_map + 3)) := by
    let D := max d_masks d_map + 3
    refine hright_raw.mono 8 (fun x => ?_) (fun x => ?_) <;>
    · have hlen_m : ∀ bs ∈ allMasks x.n, bs.length = x.n := fun bs hbs => by
        rw [allMasks_eq, List.mem_map] at hbs
        obtain ⟨k, _, rfl⟩ := hbs
        exact length_maskBits x.n k
      have hlist_le : (encList encBits (allMasks x.n)).length ≤ 2 ^ x.n * (2 * x.n + 1) := by
        calc (encList encBits (allMasks x.n)).length
            ≤ (allMasks x.n).length * (2 * x.n + 1) :=
              length_encList_le encBits _ (b := x.n) fun bs hbs => by
                simpa [encBits_apply] using (hlen_m bs hbs).le
          _ = 2 ^ x.n * (2 * x.n + 1) := by rw [length_allMasks]
      have hmax : listMax (fun bs : List Bool => (encBits bs).length) (allMasks x.n) ≤ x.n :=
        listMax_le fun bs hbs => by simpa using (hlen_m bs hbs).le
      have hlen_all : (allMasks x.n).length = 2 ^ x.n := length_allMasks x.n
      have hp1 : (x.n + 1) ^ d_masks ≤ (x.n + 1) ^ D :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
      have hp2 : (listMax (fun bs : List Bool => (encBits bs).length) (allMasks x.n) + 1) ^
          d_map ≤ (x.n + 1) ^ D :=
        (Nat.pow_le_pow_left (by omega) d_map).trans
          (Nat.pow_le_pow_right (Nat.succ_pos _) (by omega))
      have h6 : 1 ≤ 2 ^ x.n := Nat.one_le_pow _ _ (by decide)
      have hmul1 : 2 ^ x.n * (2 * x.n + 1) ≤ 2 * (2 ^ x.n * (x.n + 1) ^ D) := by
        calc 2 ^ x.n * (2 * x.n + 1) ≤ 2 ^ x.n * (2 * (x.n + 1) ^ 1) := by nlinarith
          _ ≤ 2 ^ x.n * (2 * (x.n + 1) ^ D) := by
              exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 2
                (Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)))
          _ = 2 * (2 ^ x.n * (x.n + 1) ^ D) := by ring
      have hmul2 : (2 ^ x.n + 1) * (x.n + 1) ^ D ≤ 2 * (2 ^ x.n * (x.n + 1) ^ D) := by
        nlinarith
      have hmul3 : (2 ^ x.n + 1) *
            (listMax (fun bs : List Bool => (encBits bs).length) (allMasks x.n) + 1) ^ d_map ≤
          2 * (2 ^ x.n * (x.n + 1) ^ D) :=
        (Nat.mul_le_mul_left _ hp2).trans hmul2
      have hmul0 : 2 ^ x.n * (x.n + 1) ^ d_masks ≤ 2 ^ x.n * (x.n + 1) ^ D :=
        Nat.mul_le_mul_left _ hp1
      dsimp only [D] at hmul0 hmul1 hmul2 hmul3
      rw [hlen_all]
      omega
  have htagged : ComputableInO taggedMasks encSymAndInstance (encList (encPair encBits encBool))
      (fun x => 2 ^ x.n * (x.n + 1) ^ (max d_masks d_map + 3) +
        ((encSymAndInstance x).length + 1) ^ (d₁ + 1))
      (fun x => 2 ^ x.n * (x.n + 1) ^ (max d_masks d_map + 3) +
        ((encSymAndInstance x).length + 1) ^ (d₁ + 1)) := by
    have happ := (ComputableInO.of_linear
      (ComputableInDegree.listAppend (encPair encBits encBool))).comp_linear (hleft.prod hright)
    refine happ.mono 4 (fun x => ?_) (fun x => ?_) <;>
    · have h1 : (encSymAndInstance x).length ≤ ((encSymAndInstance x).length + 1) ^ (d₁ + 1) :=
        (Nat.le_succ _).trans (Nat.le_self_pow (by omega) _)
      have h2 : ((encSymAndInstance x).length + 1) ^ d₁ ≤
          ((encSymAndInstance x).length + 1) ^ (d₁ + 1) :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
      omega
  have hM : ∀ x : SymAndInstance, ∀ p ∈ taggedMasks x,
      (encPair encBits encBool p).length ≤ 2 * x.n + 8 := fun x p hp => by
    have hp1 := fst_length_mem_taggedMasks hp
    have hp2 : (encBool p.2).length ≤ 2 := by cases p.2 <;> simp
    rw [length_encPair, encBits_apply, hp1]
    omega
  obtain ⟨d_sort, hsort⟩ := computableInO_radixSortLSB computableInO_n_nat htagged hM
  have hmem_sort : ∀ x : SymAndInstance,
      ∀ p ∈ radixSortLSB x.n (taggedMasks x), p ∈ taggedMasks x :=
    fun x p hp => (mem_radixStep_iff).1 hp
  have hlen_sort : ∀ x : SymAndInstance,
      (radixSortLSB x.n (taggedMasks x)).length = x.gates.length + 2 ^ x.n := fun x => by
    rw [radixSortLSB, length_radixStep]
    simp [taggedMasks, normGates, length_allMasks]
  have hcountEmitted_bounds : ∀ (c : ℕ) (L : List (List Bool × Bool)),
      (countEmitted c L).length ≤ L.length ∧ ∀ v ∈ countEmitted c L, v ≤ c + L.length := by
    intro c L
    induction L generalizing c with
    | nil => simp [countEmitted]
    | cons a t ih =>
      simp only [countEmitted]
      cases ha : a.2
      · simp only [Bool.false_eq_true, ↓reduceIte]
        obtain ⟨hl, hm⟩ := ih (c + 1)
        exact ⟨hl.trans (Nat.le_succ _), fun v hv => (hm v hv).trans (by simp; omega)⟩
      · simp only [↓reduceIte, List.length_cons, List.mem_cons]
        obtain ⟨hl, hm⟩ := ih 0
        refine ⟨Nat.succ_le_succ hl, fun v hv => ?_⟩
        rcases hv with rfl | hv
        · omega
        · exact (hm v hv).trans (by simp; omega)
  have hnext : ComputableInPolyTime (fun q : ℕ × (List Bool × Bool) => if q.2.2 then 0 else q.1 + 1)
      (encPair encNat (encPair encBits encBool)) encNat := by fun_prop
  have hemit : ComputableInPolyTime (fun q : ℕ × (List Bool × Bool) => if q.2.2 then [q.1] else [])
      (encPair encNat (encPair encBits encBool)) (encList encNat) := by fun_prop
  obtain ⟨c_fold, d_fold, hfold⟩ := ComputableInTimeAndSpace.streamFold_pair_list
    (encA := encPair encBits encBool) (encS := encNat) (encB := encNat)
    (encIn := encPair encNat (encList (encPair encBits encBool)))
    (init := Prod.fst) (elems := Prod.snd) (fun _ => rfl) hnext hemit
    (g := fun q : ℕ × List (List Bool × Bool) => countEmitted q.1 q.2)
    (fun q => countEmitted_streamEmit q.1 q.2)
    (lMax := fun q => Nat.log2 (q.1 + q.2.length + 1) +
      2 * (listMax (fun p : List Bool × Bool => p.1.length) q.2) + 8)
    (fun q j _ => by
      have hst := streamState_count_le q.1 q.2 j
      have hlen := length_encNat_le_log2 (hst.trans (Nat.le_add_right (q.1 + q.2.length) 1))
      change (encNat (streamState q.1 _ q.2 j)).length ≤ _
      omega)
    (fun q j hj => by
      have hp := List.getElem_mem hj
      have hm := le_listMax (f := fun p : List Bool × Bool => p.1.length) hp
      have h2 : (encBool q.2[j].2).length ≤ 2 := by cases q.2[j].2 <;> simp
      rw [length_encPair, encBits_apply]
      omega)
  have hfold_inO : ComputableInO (fun q : ℕ × List (List Bool × Bool) => countEmitted q.1 q.2)
      (encPair encNat (encList (encPair encBits encBool))) (encList encNat)
      (fun q => (encPair encNat (encList (encPair encBits encBool)) q).length +
        (q.2.length + 1) * (Nat.log2 (q.1 + q.2.length + 1) +
          2 * (listMax (fun p : List Bool × Bool => p.1.length) q.2) + 9) ^ d_fold + 1)
      (fun q => (Nat.log2 (q.1 + q.2.length + 1) +
        2 * (listMax (fun p : List Bool × Bool => p.1.length) q.2) + 9) ^ d_fold +
        (q.2.length + 1) * (Nat.log2 (q.1 + q.2.length + 1) + 2) + 1) := by
    refine ComputableInO.of_bounds hfold (c_fold + 3) (fun q => ?_) (fun q => ?_) (fun q => ?_)
    · rw [Nat.add_assoc (Nat.log2 (q.1 + q.2.length + 1) +
        2 * listMax (fun p : List Bool × Bool => p.1.length) q.2) 8 1]
      exact Nat.mul_le_mul (by omega) (by omega)
    · rw [Nat.add_assoc (Nat.log2 (q.1 + q.2.length + 1) +
        2 * listMax (fun p : List Bool × Bool => p.1.length) q.2) 8 1]
      exact Nat.mul_le_mul (by omega) (by omega)
    · obtain ⟨hlen_ce, hmem_ce⟩ := hcountEmitted_bounds q.1 q.2
      have hce := length_encList_le encNat (countEmitted q.1 q.2)
        (b := Nat.log2 (q.1 + q.2.length + 1) + 1) fun v hv =>
          length_encNat_le_log2 ((hmem_ce v hv).trans (Nat.le_succ _))
      have hmul : (countEmitted q.1 q.2).length *
            (2 * (Nat.log2 (q.1 + q.2.length + 1) + 1) + 1) ≤
          3 * ((q.2.length + 1) * (Nat.log2 (q.1 + q.2.length + 1) + 2)) := by
        calc (countEmitted q.1 q.2).length * (2 * (Nat.log2 (q.1 + q.2.length + 1) + 1) + 1)
            ≤ (q.2.length + 1) * (3 * (Nat.log2 (q.1 + q.2.length + 1) + 2)) :=
              Nat.mul_le_mul (hlen_ce.trans (Nat.le_succ _)) (by omega)
          _ = 3 * ((q.2.length + 1) * (Nat.log2 (q.1 + q.2.length + 1) + 2)) := by ring
      calc (encList encNat (countEmitted q.1 q.2)).length
          ≤ 3 * ((q.2.length + 1) * (Nat.log2 (q.1 + q.2.length + 1) + 2)) := hce.trans hmul
        _ ≤ (c_fold + 3) * ((Nat.log2 (q.1 + q.2.length + 1) +
              2 * (listMax (fun p : List Bool × Bool => p.1.length) q.2) + 9) ^ d_fold +
              (q.2.length + 1) * (Nat.log2 (q.1 + q.2.length + 1) + 2) + 1 + 1) :=
            Nat.mul_le_mul (by omega) (by omega)
  let c_s := max (max d_masks d_map + 3) (d₁ + 1) + d_sort + 2
  have hwrap0 : ComputableInO (fun x : SymAndInstance =>
      (0, radixSortLSB x.n (taggedMasks x)))
      encSymAndInstance (encPair encNat (encList (encPair encBits encBool)))
      (fun x => (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ c_s) * (x.n + 1) ^ c_s)
      (fun x => (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ c_s) * (x.n + 1) ^ c_s) := by
    have hp :=
      (ComputableInO.constZero (encIn := encSymAndInstance) (encMid := encNat) 0).prod hsort
    refine hp.mono (10 ^ d_sort + 32) (fun x => ?_) (fun x => ?_)
    · set A := (encSymAndInstance x).length + 1
      set N := x.n + 1
      have h1 : (encSymAndInstance x).length ≤ A := Nat.le_succ _
      have hA : A ≤ A ^ c_s := Nat.le_self_pow (by omega) A
      have hA1 : A ^ (d₁ + 1) ≤ A ^ c_s := Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
      have hN1 : N ^ (max d_masks d_map + 3) ≤ N ^ (c_s - 1) :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
      have hN2 : N ^ d_sort ≤ N ^ (c_s - 1) := Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
      have hN0 : 1 ≤ N ^ c_s := Nat.one_le_pow _ _ (Nat.succ_pos _)
      have hN_sub : N * N ^ (c_s - 1) = N ^ c_s := by
        rw [← pow_succ', Nat.sub_add_cancel (by dsimp only [c_s]; omega)]
      have hlen_t : (taggedMasks x).length + 1 ≤ 2 ^ x.n + A := by
        have hg := gates_length_le_encSymAndInstance x
        simp only [taggedMasks, normGates, List.length_append, List.length_map, length_allMasks]
        omega
      have hprod_t : ((taggedMasks x).length + 1) * ((encNat x.n).length + (2 * x.n + 8) + 1) ^
            d_sort ≤ 10 ^ d_sort * ((2 ^ x.n + A ^ c_s) * N ^ (c_s - 1)) := by
        calc ((taggedMasks x).length + 1) * ((encNat x.n).length + (2 * x.n + 8) + 1) ^ d_sort
            ≤ (2 ^ x.n + A ^ c_s) * (10 ^ d_sort * N ^ (c_s - 1)) :=
              Nat.mul_le_mul (hlen_t.trans (Nat.add_le_add_left hA _))
                ((pow_encNat_add_le x.n d_sort).trans (Nat.mul_le_mul_left _ hN2))
          _ = 10 ^ d_sort * ((2 ^ x.n + A ^ c_s) * N ^ (c_s - 1)) := by ring
      have hmul_N : N * (((taggedMasks x).length + 1) *
            ((encNat x.n).length + (2 * x.n + 8) + 1) ^ d_sort + 1) ≤
          (10 ^ d_sort + 1) * ((2 ^ x.n + A ^ c_s) * N ^ c_s) := by
        have hsum : ((taggedMasks x).length + 1) *
              ((encNat x.n).length + (2 * x.n + 8) + 1) ^ d_sort + 1 ≤
            (10 ^ d_sort + 1) * ((2 ^ x.n + A ^ c_s) * N ^ (c_s - 1)) := by
          have h2p : 1 ≤ (2 ^ x.n + A ^ c_s) * N ^ (c_s - 1) :=
            Nat.mul_pos (by have := Nat.one_le_pow x.n 2 (by decide); omega)
              (Nat.one_le_pow _ _ (Nat.succ_pos _))
          nlinarith
        calc N * _ ≤ N * ((10 ^ d_sort + 1) * ((2 ^ x.n + A ^ c_s) * N ^ (c_s - 1))) :=
              Nat.mul_le_mul_left _ hsum
          _ = (10 ^ d_sort + 1) * ((2 ^ x.n + A ^ c_s) * (N * N ^ (c_s - 1))) := by ring
          _ = (10 ^ d_sort + 1) * ((2 ^ x.n + A ^ c_s) * N ^ c_s) := by rw [hN_sub]
      have hA_box : A ≤ (2 ^ x.n + A ^ c_s) * N ^ c_s :=
        (hA.trans (Nat.le_add_left _ _)).trans (Nat.le_mul_of_pos_right _ hN0)
      have hS_box : 2 ^ x.n * N ^ (max d_masks d_map + 3) + A ^ (d₁ + 1) ≤
          2 * ((2 ^ x.n + A ^ c_s) * N ^ c_s) := by
        have hN_c : N ^ (c_s - 1) ≤ N ^ c_s :=
          Nat.pow_le_pow_right (Nat.succ_pos _) (by dsimp only [c_s]; omega)
        have hS1 : 2 ^ x.n * N ^ (max d_masks d_map + 3) ≤ (2 ^ x.n + A ^ c_s) * N ^ c_s := by
          calc 2 ^ x.n * N ^ (max d_masks d_map + 3)
              ≤ 2 ^ x.n * N ^ c_s := Nat.mul_le_mul_left _ (hN1.trans hN_c)
            _ ≤ (2 ^ x.n + A ^ c_s) * N ^ c_s := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
        have hS2 : A ^ (d₁ + 1) ≤ (2 ^ x.n + A ^ c_s) * N ^ c_s :=
          (hA1.trans (Nat.le_add_left _ _)).trans (Nat.le_mul_of_pos_right _ hN0)
        omega
      set B := (2 ^ x.n + A ^ c_s) * N ^ c_s
      have h6 : (10 ^ d_sort + 6) * B = 10 ^ d_sort * B + 6 * B := by ring
      have hle : (encSymAndInstance x).length +
            ((encSymAndInstance x).length + (encSymAndInstance x).length +
              (2 ^ x.n * N ^ (max d_masks d_map + 3) + A ^ (d₁ + 1)) +
              N * (((taggedMasks x).length + 1) *
                ((encNat x.n).length + (2 * x.n + 8) + 1) ^ d_sort + 1)) ≤
          (10 ^ d_sort + 6) * B := by
        have hmul_N' : N * (((taggedMasks x).length + 1) *
              ((encNat x.n).length + (2 * x.n + 8) + 1) ^ d_sort + 1) ≤
            10 ^ d_sort * B + B := by
          have : (10 ^ d_sort + 1) * B = 10 ^ d_sort * B + B := by ring
          omega
        linarith only [h1, hA_box, hS_box, hmul_N', h6]
      exact hle.trans (Nat.mul_le_mul (by omega) (Nat.le_succ _))
    · set A := (encSymAndInstance x).length + 1
      set N := x.n + 1
      have hA : A ≤ A ^ c_s := Nat.le_self_pow (by dsimp only [c_s]; omega) A
      have hA1 : A ^ (d₁ + 1) ≤ A ^ c_s :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (by dsimp only [c_s]; omega)
      have hN1 : N ^ (max d_masks d_map + 3) ≤ N ^ c_s :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (by dsimp only [c_s]; omega)
      have hN2 : N ^ d_sort ≤ N ^ c_s :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (by dsimp only [c_s]; omega)
      have hN0 : 1 ≤ N ^ c_s := Nat.one_le_pow _ _ (Nat.succ_pos _)
      have h2n0 : 1 ≤ 2 ^ x.n := Nat.one_le_pow _ _ (by decide)
      have hlen_t : (taggedMasks x).length + 1 ≤ 2 ^ x.n + A := by
        have hg := gates_length_le_encSymAndInstance x
        simp only [taggedMasks, normGates, List.length_append, List.length_map, length_allMasks]
        omega
      have hN_pow : N ≤ N ^ c_s := Nat.le_self_pow (by dsimp only [c_s]; omega) N
      have htm : ((taggedMasks x).length + 1) * (2 * x.n + 8 + 1) ≤
          9 * ((2 ^ x.n + A ^ c_s) * N ^ c_s) := by
        calc ((taggedMasks x).length + 1) * (2 * x.n + 8 + 1)
            ≤ (2 ^ x.n + A ^ c_s) * (9 * N ^ c_s) :=
              Nat.mul_le_mul (hlen_t.trans (Nat.add_le_add_left hA _)) (by omega)
          _ = 9 * ((2 ^ x.n + A ^ c_s) * N ^ c_s) := by ring
      set B := (2 ^ x.n + A ^ c_s) * N ^ c_s
      have hS1 : (encSymAndInstance x).length ≤ B :=
        ((Nat.le_succ _).trans hA |>.trans (Nat.le_add_left _ _)).trans
          (Nat.le_mul_of_pos_right _ hN0)
      have hS2 : 2 ^ x.n * N ^ (max d_masks d_map + 3) ≤ B :=
        Nat.mul_le_mul (Nat.le_add_right _ _) hN1
      have hS3 : A ^ (d₁ + 1) ≤ B :=
        (hA1.trans (Nat.le_add_left _ _)).trans (Nat.le_mul_of_pos_right _ hN0)
      have hS4 : ((encNat x.n).length + (2 * x.n + 8) + 1) ^ d_sort ≤ 10 ^ d_sort * B :=
        (pow_encNat_add_le x.n d_sort).trans
          (Nat.mul_le_mul_left _ (hN2.trans (Nat.le_mul_of_pos_left _ (by omega))))
      calc 0 + ((encSymAndInstance x).length +
              (2 ^ x.n * N ^ (max d_masks d_map + 3) + A ^ (d₁ + 1)) +
              ((taggedMasks x).length + 1) * (2 * x.n + 8 + 1) +
              ((encNat x.n).length + (2 * x.n + 8) + 1) ^ d_sort)
          ≤ B + (B + B) + 9 * B + 10 ^ d_sort * B := by
            linarith only [hS1, hS2, hS3, htm, hS4]
        _ = (10 ^ d_sort + 12) * B := by ring
        _ ≤ (10 ^ d_sort + 32) * (B + 1) := Nat.mul_le_mul (by omega) (Nat.le_succ _)
  obtain ⟨c_w, hwrap0_len⟩ := hwrap0.length_le
  exact computableInO_countMasks_finish hwrap0 hfold_inO hwrap0_len hlen_sort hmem_sort

/-! ### Stage 3: Cyclic butterfly fast zeta transform over `List ℕ` -/

private def evens : List ℕ → List ℕ
  | [] => []
  | [x] => [x]
  | x :: _ :: rest => x :: evens rest

private def passOddsAdd : List ℕ → List ℕ
  | [] => []
  | [_] => []
  | x :: y :: rest => (x + y) :: passOddsAdd rest

private def yatesStep (L : List ℕ) : List ℕ :=
  evens L ++ passOddsAdd L

private def yatesZeta (n : ℕ) (L : List ℕ) : List ℕ :=
  yatesStep^[n] L

private theorem list_two_step_ind {P : List ℕ → Prop} (h0 : P []) (h1 : ∀ x, P [x])
    (h2 : ∀ x y rest, P rest → P (x :: y :: rest)) (L : List ℕ) : P L := by
  match L with
  | [] => exact h0
  | [x] => exact h1 x
  | x :: y :: rest => exact h2 x y rest (list_two_step_ind h0 h1 h2 rest)

private theorem length_evens_two_mul {L : List ℕ} {m : ℕ} (h : L.length = 2 * m) :
    (evens L).length = m := by
  induction L using list_two_step_ind generalizing m with
  | h0 => simp at h; simp [evens, h]
  | h1 x => simp at h; omega
  | h2 x y rest ih =>
    rcases m with _ | m
    · simp at h
    · simp only [List.length_cons] at h
      simp only [evens, List.length_cons]
      have := ih (m := m) (by omega)
      omega

private theorem length_passOddsAdd_two_mul {L : List ℕ} {m : ℕ} (h : L.length = 2 * m) :
    (passOddsAdd L).length = m := by
  induction L using list_two_step_ind generalizing m with
  | h0 => simp at h; simp [passOddsAdd, h]
  | h1 x => simp at h; omega
  | h2 x y rest ih =>
    rcases m with _ | m
    · simp at h
    · simp only [List.length_cons] at h
      simp only [passOddsAdd, List.length_cons]
      have := ih (m := m) (by omega)
      omega

private theorem length_yatesStep_two_mul {L : List ℕ} {m : ℕ} (h : L.length = 2 * m) :
    (yatesStep L).length = 2 * m := by
  rw [yatesStep, List.length_append, length_evens_two_mul h, length_passOddsAdd_two_mul h]
  omega

private theorem getElem_evens {L : List ℕ} (k : ℕ) (hk : k < (evens L).length) :
    ∃ h : 2 * k < L.length, (evens L)[k] = L[2 * k]'h := by
  induction L using list_two_step_ind generalizing k with
  | h0 => simp [evens] at hk
  | h1 x =>
    simp only [evens, List.length_singleton] at hk
    have : k = 0 := by omega
    subst this
    simp [evens]
  | h2 x y rest ih =>
    rcases k with _ | k
    · simp [evens]
    · simp only [evens, List.length_cons, Nat.add_lt_add_iff_right] at hk
      obtain ⟨hl, he⟩ := ih k hk
      exact ⟨by simp; omega, by simpa [evens, Nat.mul_add] using he⟩

private theorem getElem_passOddsAdd {L : List ℕ} (k : ℕ) (hk : k < (passOddsAdd L).length) :
    ∃ h : 2 * k + 1 < L.length, (passOddsAdd L)[k] = L[2 * k]'(by omega) + L[2 * k + 1]'h := by
  induction L using list_two_step_ind generalizing k with
  | h0 => simp [passOddsAdd] at hk
  | h1 x => simp [passOddsAdd] at hk
  | h2 x y rest ih =>
    rcases k with _ | k
    · simp [passOddsAdd]
    · simp only [passOddsAdd, List.length_cons, Nat.add_lt_add_iff_right] at hk
      obtain ⟨hl, he⟩ := ih k hk
      exact ⟨by simp; omega, by simpa [passOddsAdd, Nat.mul_add, Nat.add_assoc] using he⟩

private theorem length_yatesStep_iter_two_pow {n i : ℕ} {L : List ℕ} (hL : L.length = 2 ^ n)
    (hi : i ≤ n) : (yatesStep^[i] L).length = 2 ^ n := by
  induction i with
  | zero => exact hL
  | succ i ih =>
    have hn : 0 < n := by omega
    have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by rw [← pow_succ', Nat.sub_add_cancel hn]
    rw [Function.iterate_succ_apply']
    exact (length_yatesStep_two_mul ((ih (by omega)).trans hpow)).trans hpow.symm

private def rotMaskSet (n i k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun j : Fin n => k.testBit ((j.1 + (n - i)) % n) = true

private def yatesPred (n i k : ℕ) (T : Finset (Fin n)) : Prop :=
  ∀ j : Fin n, if j.1 < i then (j ∈ T → j ∈ rotMaskSet n i k)
    else (j ∈ T ↔ j ∈ rotMaskSet n i k)

private instance (n i k : ℕ) (T : Finset (Fin n)) : Decidable (yatesPred n i k T) :=
  inferInstanceAs (Decidable (∀ _ : Fin n, _))

private theorem testBit_two_mul_add_bit (m b r : ℕ) (hb : b < 2) :
    (2 * m + b).testBit (r + 1) = m.testBit r := by
  have h1 : 2 * m + b = b + 2 * m := by omega
  rw [Nat.testBit_succ, h1, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hb, Nat.zero_add]

private theorem testBit_mod_two_pow_lt {k m r : ℕ} (hr : r < m) :
    (k % 2 ^ m).testBit r = k.testBit r := by
  simp [Nat.testBit_mod_two_pow, hr]

private theorem yatesStep_iter_correct {n : ℕ} (hn : 0 < n) (F : Finset (Fin n) → ℕ)
    (L₀ : List ℕ) (hLen : L₀.length = 2 ^ n)
    (hL₀ : ∀ k (hk : k < 2 ^ n), L₀[k]'(by omega) = F (maskSet n k)) :
    ∀ i (hi : i ≤ n), ∀ k (hk : k < 2 ^ n),
      (yatesStep^[i] L₀)[k]'((length_yatesStep_iter_two_pow hLen hi).symm ▸ hk) =
        ∑ T : Finset (Fin n), if yatesPred n i k T then F T else 0 := by
  intro i hi
  induction i with
  | zero =>
    intro k hk
    simp only [Function.iterate_zero_apply]
    rw [hL₀ k hk]
    have hpred : ∀ T : Finset (Fin n), yatesPred n 0 k T ↔ T = maskSet n k := fun T => by
      simp only [yatesPred, Nat.not_lt_zero, ↓reduceIte, rotMaskSet, Nat.sub_zero,
        Finset.ext_iff, Finset.mem_filter, Finset.mem_univ, true_and, mem_maskSet]
      refine forall_congr' fun j => ?_
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]
    simp_rw [hpred]
    simp
  | succ i ih =>
    intro k hk
    have hi_le : i ≤ n := by omega
    have hi_lt : i < n := by omega
    have hpow_split : 2 ^ n = 2 * 2 ^ (n - 1) := by rw [← pow_succ', Nat.sub_add_cancel hn]
    have hLen_i : (yatesStep^[i] L₀).length = 2 * 2 ^ (n - 1) :=
      (length_yatesStep_iter_two_pow hLen hi_le).trans hpow_split
    set L := yatesStep^[i] L₀
    let k₀ := 2 * (k % 2 ^ (n - 1))
    let k₁ := k₀ + 1
    have hk_mod : k % 2 ^ (n - 1) < 2 ^ (n - 1) := Nat.mod_lt _ (Nat.two_pow_pos _)
    have hk₀_lt : k₀ < 2 ^ n := by dsimp [k₀]; omega
    have hk₁_lt : k₁ < 2 ^ n := by dsimp [k₁, k₀]; omega
    have ih₀ := ih hi_le k₀ hk₀_lt
    have ih₁ := ih hi_le k₁ hk₁_lt
    have hrot_other : ∀ j : Fin n, j.1 ≠ i →
        (j ∈ rotMaskSet n i k₀ ↔ j ∈ rotMaskSet n (i + 1) k) ∧
        (j ∈ rotMaskSet n i k₁ ↔ j ∈ rotMaskSet n (i + 1) k) := fun j hj => by
      let r := (j.1 + (n - (i + 1))) % n
      have hr_lt_n : r < n := Nat.mod_lt _ hn
      have hr_ne : r ≠ n - 1 := by
        intro heq
        dsimp only [r] at heq
        have hsum_lt : j.1 + (n - (i + 1)) < 2 * n := by omega
        by_cases hlt : j.1 + (n - (i + 1)) < n
        · rw [Nat.mod_eq_of_lt hlt] at heq; exact hj (by omega)
        · have hmod : (j.1 + (n - (i + 1))) % n = j.1 + (n - (i + 1)) - n :=
            Nat.mod_eq_sub_mod (by omega) |>.trans (Nat.mod_eq_of_lt (by omega))
          rw [hmod] at heq
          omega
      have hr_lt : r < n - 1 := by omega
      have hidx : (j.1 + (n - i)) % n = r + 1 := by
        have hsum : j.1 + (n - i) = (j.1 + (n - (i + 1))) + 1 := by omega
        rw [hsum, Nat.add_mod]
        change (r + 1 % n) % n = r + 1
        by_cases hn1 : 1 < n
        · rw [Nat.mod_eq_of_lt hn1, Nat.mod_eq_of_lt (by omega)]
        · omega
      simp only [rotMaskSet, Finset.mem_filter, Finset.mem_univ, true_and, hidx]
      refine ⟨?_, ?_⟩
      · change k₀.testBit (r + 1) = true ↔ k.testBit r = true
        rw [show k₀ = 2 * (k % 2 ^ (n - 1)) + 0 from rfl,
          testBit_two_mul_add_bit _ 0 r (by decide), testBit_mod_two_pow_lt hr_lt]
      · change k₁.testBit (r + 1) = true ↔ k.testBit r = true
        rw [show k₁ = 2 * (k % 2 ^ (n - 1)) + 1 from rfl,
          testBit_two_mul_add_bit _ 1 r (by decide), testBit_mod_two_pow_lt hr_lt]
    have hrot_i0 : (⟨i, hi_lt⟩ : Fin n) ∉ rotMaskSet n i k₀ := by
      simp only [rotMaskSet, Finset.mem_filter, Finset.mem_univ, true_and]
      have hidx : (i + (n - i)) % n = 0 := by rw [Nat.add_sub_of_le hi_le, Nat.mod_self]
      rw [hidx]
      simp [k₀]
    have hrot_i1 : (⟨i, hi_lt⟩ : Fin n) ∈ rotMaskSet n i k₁ := by
      simp only [rotMaskSet, Finset.mem_filter, Finset.mem_univ, true_and]
      have hidx : (i + (n - i)) % n = 0 := by rw [Nat.add_sub_of_le hi_le, Nat.mod_self]
      rw [hidx]
      simp [k₁, k₀]
    have hrot_i_next : (⟨i, hi_lt⟩ : Fin n) ∈ rotMaskSet n (i + 1) k ↔
        k.testBit (n - 1) = true := by
      simp only [rotMaskSet, Finset.mem_filter, Finset.mem_univ, true_and]
      have hidx : (i + (n - (i + 1))) % n = n - 1 := by
        have h1 : i + (n - (i + 1)) = n - 1 := by omega
        rw [h1, Nat.mod_eq_of_lt (by omega)]
      rw [hidx]
    suffices (yatesStep L)[k]'(by
        rw [length_yatesStep_two_mul hLen_i, ← hpow_split]; exact hk) =
        ∑ T : Finset (Fin n), if yatesPred n (i + 1) k T then F T else 0 by
      simpa only [Function.iterate_succ_apply', L] using this
    by_cases hbit : k.testBit (n - 1) = true
    · have hk_ge : 2 ^ (n - 1) ≤ k := by
        by_contra hlt
        push Not at hlt
        have := Nat.testBit_lt_two_pow hlt
        simp_all
      have hk_sub : k - 2 ^ (n - 1) = k % 2 ^ (n - 1) := by
        have : k = 2 ^ (n - 1) + (k - 2 ^ (n - 1)) := by omega
        conv_rhs => rw [this, Nat.add_mod_left]
        rw [Nat.mod_eq_of_lt (by omega)]
      have hpass_len : (passOddsAdd L).length = 2 ^ (n - 1) :=
        length_passOddsAdd_two_mul hLen_i
      have hev_len : (evens L).length = 2 ^ (n - 1) := length_evens_two_mul hLen_i
      have hstep_val : (yatesStep L)[k]'(by
          rw [length_yatesStep_two_mul hLen_i, ← hpow_split]; exact hk) =
          L[k₀]'(by rw [hLen_i]; dsimp [k₀]; omega) +
          L[k₁]'(by rw [hLen_i]; dsimp [k₁, k₀]; omega) := by
        simp only [yatesStep]
        rw [List.getElem_append_right (by omega)]
        have hp := (getElem_passOddsAdd (L := L) (k - 2 ^ (n - 1)) (by omega)).2
        simp only [hev_len, hk_sub] at hp ⊢
        exact hp
      rw [hstep_val, ih₀, ih₁, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun T _ => ?_
      have hiff0 : yatesPred n i k₀ T ↔ yatesPred n (i + 1) k T ∧ (⟨i, hi_lt⟩ : Fin n) ∉ T := by
        constructor
        · intro h
          have hi0 := h ⟨i, hi_lt⟩
          simp only [lt_irrefl, ↓reduceIte] at hi0
          refine ⟨fun j => ?_, fun hmem => hrot_i0 (hi0.1 hmem)⟩
          by_cases hj : j.1 = i
          · have hjf : j = ⟨i, hi_lt⟩ := Fin.ext hj
            subst hjf
            simp [hrot_i_next, hbit, show i < i + 1 by omega]
          · have hlt_eq : (j.1 < i + 1) ↔ (j.1 < i) := by omega
            have hro := (hrot_other j hj).1
            have hj0 := h j
            split_ifs at hj0 ⊢ with h1 h2
            · exact fun hm => hro.1 (hj0 hm)
            · omega
            · omega
            · exact hj0.trans hro
        · rintro ⟨h, hni⟩ j
          by_cases hj : j.1 = i
          · have hjf : j = ⟨i, hi_lt⟩ := Fin.ext hj
            subst hjf
            simp [hrot_i0, hni]
          · have hlt_eq : (j.1 < i + 1) ↔ (j.1 < i) := by omega
            have hro := (hrot_other j hj).1
            have hj0 := h j
            split_ifs at hj0 ⊢ with h1 h2
            · exact fun hm => hro.2 (hj0 hm)
            · omega
            · omega
            · exact hj0.trans hro.symm
      have hiff1 : yatesPred n i k₁ T ↔ yatesPred n (i + 1) k T ∧ (⟨i, hi_lt⟩ : Fin n) ∈ T := by
        constructor
        · intro h
          have hi1 := h ⟨i, hi_lt⟩
          simp only [lt_irrefl, ↓reduceIte] at hi1
          refine ⟨fun j => ?_, hi1.2 hrot_i1⟩
          by_cases hj : j.1 = i
          · have hjf : j = ⟨i, hi_lt⟩ := Fin.ext hj
            subst hjf
            simp [hrot_i_next, hbit, show i < i + 1 by omega]
          · have hro := (hrot_other j hj).2
            have hj1 := h j
            split_ifs at hj1 ⊢ with h1 h2
            · exact fun hm => hro.1 (hj1 hm)
            · omega
            · omega
            · exact hj1.trans hro
        · rintro ⟨h, hmem⟩ j
          by_cases hj : j.1 = i
          · have hjf : j = ⟨i, hi_lt⟩ := Fin.ext hj
            subst hjf
            simp [hrot_i1, hmem]
          · have hro := (hrot_other j hj).2
            have hj1 := h j
            split_ifs at hj1 ⊢ with h1 h2
            · exact fun hm => hro.2 (hj1 hm)
            · omega
            · omega
            · exact hj1.trans hro.symm
      by_cases hP : yatesPred n (i + 1) k T <;> by_cases hmem : (⟨i, hi_lt⟩ : Fin n) ∈ T <;>
        simp [hP, hmem, hiff0, hiff1]
    · have hf_bit : k.testBit (n - 1) = false := by
        cases h : k.testBit (n - 1) <;> simp_all
      have hk_lt_half : k < 2 ^ (n - 1) := by
        by_contra hge
        push Not at hge
        have hdiv : k / 2 ^ (n - 1) = 1 := by
          have h1 : k = 2 ^ (n - 1) + (k - 2 ^ (n - 1)) := by omega
          rw [h1, Nat.add_div_left _ (Nat.two_pow_pos _), Nat.div_eq_of_lt (by omega)]
        have : k.testBit (n - 1) = true := by
          simp [Nat.testBit_eq_decide_div_mod_eq, hdiv]
        simp_all
      have hk_mod_eq : k % 2 ^ (n - 1) = k := Nat.mod_eq_of_lt hk_lt_half
      have hev_len : (evens L).length = 2 ^ (n - 1) := length_evens_two_mul hLen_i
      have hstep_val : (yatesStep L)[k]'(by
          rw [length_yatesStep_two_mul hLen_i, ← hpow_split]; exact hk) =
          L[k₀]'(by rw [hLen_i]; dsimp [k₀]; omega) := by
        simp only [yatesStep]
        rw [List.getElem_append_left (by omega)]
        have he := (getElem_evens (L := L) k (by omega)).2
        simp only [k₀, hk_mod_eq] at he ⊢
        exact he
      rw [hstep_val, ih₀]
      refine Finset.sum_congr rfl fun T _ => ?_
      have hiff : yatesPred n i k₀ T ↔ yatesPred n (i + 1) k T := by
        constructor
        · intro h j
          by_cases hj : j.1 = i
          · have hjf : j = ⟨i, hi_lt⟩ := Fin.ext hj
            subst hjf
            have hj0 := h ⟨i, hi_lt⟩
            simp only [lt_irrefl, ↓reduceIte, hrot_i0, iff_false] at hj0
            simp [hrot_i_next, hf_bit, hj0, show i < i + 1 by omega]
          · have hro := (hrot_other j hj).1
            have hj0 := h j
            split_ifs at hj0 ⊢ with h1 h2
            · exact fun hm => hro.1 (hj0 hm)
            · omega
            · omega
            · exact hj0.trans hro
        · intro h j
          by_cases hj : j.1 = i
          · have hjf : j = ⟨i, hi_lt⟩ := Fin.ext hj
            subst hjf
            have hj1 := h ⟨i, hi_lt⟩
            simp only [show i < i + 1 by omega, ↓reduceIte, hrot_i_next, hf_bit,
              Bool.false_eq_true, imp_false] at hj1
            simp [hrot_i0, hj1]
          · have hro := (hrot_other j hj).1
            have hj1 := h j
            split_ifs at hj1 ⊢ with h1 h2
            · exact fun hm => hro.2 (hj1 hm)
            · omega
            · omega
            · exact hj1.trans hro.symm
      simp [hiff]

private theorem yatesZeta_countMasks_eq (x : SymAndInstance) :
    yatesZeta x.n (countMasks x) = (List.range (2 ^ x.n)).map fun k =>
      if _h : k < 2 ^ x.n then
        (x.gates.map (gateSet x.n)).countP fun S => decide (S ⊆ maskSet x.n k)
      else 0 := by
  have hlen_cm : (countMasks x).length = 2 ^ x.n := countMasks_length x
  have heq_elem : ∀ k (hk : k < 2 ^ x.n),
      (yatesZeta x.n (countMasks x))[k]'(by
        rw [yatesZeta, length_yatesStep_iter_two_pow hlen_cm le_rfl]; exact hk) =
      (x.gates.map (gateSet x.n)).countP fun S => decide (S ⊆ maskSet x.n k) := fun k hk => by
    have hcount_sub : ∀ S : Finset (Fin x.n),
        subsetZeta (fun T => (x.gates.map (gateSet x.n)).count T) S =
          (x.gates.map (gateSet x.n)).countP fun T => decide (T ⊆ S) :=
      subsetZeta_listCount_eq_countP (x.gates.map (gateSet x.n))
    rcases Nat.eq_zero_or_pos x.n with hn0 | hn_pos
    · have hk0 : k = 0 := by rw [hn0, pow_zero] at hk; omega
      subst hk0
      simp only [yatesZeta, hn0, Function.iterate_zero_apply, countMasks_eq]
      rw [List.getElem_map]
      simp only [List.getElem_range]
      rw [← hcount_sub (maskSet x.n 0)]
      have hsub : (maskSet x.n 0).powerset = {∅} := by
        ext S
        simp only [Finset.mem_powerset, Finset.mem_singleton, Finset.subset_iff,
          Finset.eq_empty_iff_forall_notMem]
        constructor
        · intro _ j; exact absurd j.isLt (by omega)
        · intro _ j _; exact absurd j.isLt (by omega)
      rw [subsetZeta, hsub, Finset.sum_singleton]
      congr 1
      ext i
      exact absurd i.isLt (by omega)
    · have hcor := yatesStep_iter_correct hn_pos (fun S => (x.gates.map (gateSet x.n)).count S)
        (countMasks x) hlen_cm (fun j hj => by
          simp only [countMasks_eq, List.getElem_map, List.getElem_range])
        x.n le_rfl k hk
      have hpi : (yatesZeta x.n (countMasks x))[k]'(by
            rw [yatesZeta, length_yatesStep_iter_two_pow hlen_cm le_rfl]; exact hk) =
          (yatesStep^[x.n] (countMasks x))[k]'((length_yatesStep_iter_two_pow hlen_cm le_rfl).symm ▸
            hk) := rfl
      rw [hpi, hcor, ← hcount_sub (maskSet x.n k), subsetZeta]
      have hpred : ∀ T : Finset (Fin x.n), yatesPred x.n x.n k T ↔ T ∈ (maskSet x.n k).powerset :=
        fun T => by
          simp only [yatesPred, Fin.isLt, ↓reduceIte, rotMaskSet, Nat.sub_self, Nat.add_zero,
            Finset.mem_powerset, Finset.subset_iff, Finset.mem_filter, Finset.mem_univ,
            true_and, mem_maskSet]
          exact forall_congr' fun j => by rw [Nat.mod_eq_of_lt j.isLt]
      simp_rw [hpred, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  refine List.ext_getElem (by
      rw [yatesZeta, length_yatesStep_iter_two_pow hlen_cm le_rfl, List.length_map,
        List.length_range]) fun k hk1 hk2 => ?_
  have hk : k < 2 ^ x.n := by
    rw [yatesZeta, length_yatesStep_iter_two_pow hlen_cm le_rfl] at hk1; exact hk1
  rw [heq_elem k hk, List.getElem_map, List.getElem_range, dite_eq_left hk]

private theorem yatesZeta_mem_le (x : SymAndInstance) {v : ℕ}
    (hv : v ∈ yatesZeta x.n (countMasks x)) : v ≤ x.gates.length := by
  rw [yatesZeta_countMasks_eq, List.mem_map] at hv
  obtain ⟨k, hk, rfl⟩ := hv
  rw [dite_eq_left (List.mem_range.1 hk)]
  exact List.countP_le_length.trans (by simp)

private theorem yatesStep_mem_le {L : List ℕ} {M : ℕ} (hL : ∀ v ∈ L, v ≤ M) :
    ∀ v ∈ yatesStep L, v ≤ 2 * M := by
  have hev : ∀ L' : List ℕ, (∀ v ∈ L', v ≤ M) → ∀ v ∈ evens L', v ≤ M := by
    intro L' hL'
    induction L' using list_two_step_ind with
    | h0 => simp [evens]
    | h1 a =>
      intro v hv
      simp only [evens, List.mem_singleton] at hv
      subst hv
      exact hL' v (List.mem_cons_self ..)
    | h2 a b rest ih =>
      intro v hv
      simp only [evens, List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact hL' v (List.mem_cons_self ..)
      · exact ih (fun w hw => hL' w (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw))) v hv
  have hpo : ∀ L' : List ℕ, (∀ v ∈ L', v ≤ M) → ∀ v ∈ passOddsAdd L', v ≤ 2 * M := by
    intro L' hL'
    induction L' using list_two_step_ind with
    | h0 => simp [passOddsAdd]
    | h1 a => simp [passOddsAdd]
    | h2 a b rest ih =>
      intro v hv
      simp only [passOddsAdd, List.mem_cons] at hv
      rcases hv with rfl | hv
      · have ha := hL' a (List.mem_cons_self ..)
        have hb := hL' b (List.mem_cons_of_mem _ (List.mem_cons_self ..))
        omega
      · exact ih (fun w hw => hL' w (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw))) v hv
  intro v hv
  rw [yatesStep, List.mem_append] at hv
  rcases hv with hv | hv
  · exact (hev L hL v hv).trans (by omega)
  · exact hpo L hL v hv

private theorem yatesStep_iter_mem_le (x : SymAndInstance) (i : ℕ) :
    ∀ v ∈ yatesStep^[i] (countMasks x), v ≤ 2 ^ i * x.gates.length := by
  induction i with
  | zero => simpa using fun v hv => countMasks_mem_le x hv
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    intro v hv
    have := yatesStep_mem_le ih v hv
    calc v ≤ 2 * (2 ^ i * x.gates.length) := this
      _ = 2 ^ (i + 1) * x.gates.length := by ring

private theorem evens_streamEmit (b : Bool) (L : List ℕ) :
    encList encNat (if b then evens L else match L with | [] => [] | _ :: rest => evens rest) =
      streamEmit (fun q : Bool × ℕ => !q.1)
        (fun q => encList encNat (if q.1 then [q.2] else [])) b L := by
  induction L generalizing b with
  | nil => cases b <;> rfl
  | cons x t ih =>
    cases t with
    | nil => cases b <;> simp [evens, streamEmit]
    | cons y rest =>
      cases b
      · have h1 := ih true
        simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, streamEmit, encList_nil,
          List.nil_append] at h1 ⊢
        rw [← h1]
      · have h1 := ih false
        simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_true, streamEmit, encList_cons,
          encList_nil, List.append_nil, evens] at h1 ⊢
        rw [← h1]

private theorem passOddsAdd_streamEmit (L : List ℕ) :
    encList encNat (passOddsAdd L) =
      streamEmit (fun q : (Bool × ℕ) × ℕ => if q.1.1 then (false, 0) else (true, q.2))
        (fun q => encList encNat (if q.1.1 then [q.1.2 + q.2] else [])) (false, 0) L := by
  induction L using list_two_step_ind with
  | h0 => rfl
  | h1 x => simp [passOddsAdd, streamEmit]
  | h2 x y rest ih =>
    simp only [passOddsAdd, streamEmit, Bool.false_eq_true, ↓reduceIte, encList_nil,
      List.nil_append, encList_cons, List.append_nil] at ih ⊢
    rw [ih]

private theorem computableInO_yatesZeta :
    ∃ c, ComputableInO (fun x : SymAndInstance => yatesZeta x.n (countMasks x))
      encSymAndInstance (encList encNat)
      (fun x => (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ c) * (x.n + 1) ^ c)
      (fun x => (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ c) * (x.n + 1) ^ c) := by
  have hnext_ev : ComputableInPolyTime (fun q : Bool × ℕ => !q.1)
      (encPair encBool encNat) encBool := by fun_prop
  have hemit_ev : ComputableInPolyTime (fun q : Bool × ℕ => if q.1 then [q.2] else [])
      (encPair encBool encNat) (encList encNat) := by fun_prop
  obtain ⟨c_ev, d_ev, hev_raw⟩ := ComputableInTimeAndSpace.streamFold_pair_list
    (encA := encNat) (encS := encBool) (encB := encNat)
    (encIn := encPair encBool (encList encNat))
    (init := Prod.fst) (elems := Prod.snd) (fun _ => rfl) hnext_ev hemit_ev
    (g := fun q : Bool × List ℕ =>
      if q.1 then evens q.2 else match q.2 with | [] => [] | _ :: rest => evens rest)
    (fun q => evens_streamEmit q.1 q.2)
    (lMax := fun q => listMax (fun v => (encNat v).length) q.2 + 2)
    (fun q j _ => by
      cases streamState q.1 (fun p : Bool × ℕ => !p.1) q.2 j <;> simp)
    (fun q j hj => (le_listMax (f := fun v => (encNat v).length) (List.getElem_mem hj)).trans
      (by omega))
  have hlen_ev : ∀ L : List ℕ, (encList encNat (evens L)).length ≤ (encList encNat L).length := by
    intro L
    induction L using list_two_step_ind with
    | h0 => simp [evens]
    | h1 a => simp [evens]
    | h2 a b rest ih =>
      simp only [evens, encList_cons, List.length_append]
      omega
  have hev : ComputableInO evens (encList encNat) (encList encNat)
      (fun L => (encList encNat L).length +
        (L.length + 1) * (listMax (fun v => (encNat v).length) L + 1) ^ d_ev + 1)
      (fun L => (encList encNat L).length +
        (listMax (fun v => (encNat v).length) L + 1) ^ d_ev + 1) := by
    have hwrap : ComputableInO (fun L : List ℕ => (true, L))
        (encList encNat) (encPair encBool (encList encNat))
        (fun L => (encList encNat L).length) (fun L => (encList encNat L).length) := by
      have hp := (ComputableInO.constZero (encIn := encList encNat) (encMid := encBool) true).prod
        (ComputableInO.id' (encMid := encList encNat))
      exact hp.mono 2 (fun L => by omega) (fun L => by omega)
    have hraw : ComputableInO
        (fun q : Bool × List ℕ =>
          if q.1 then evens q.2 else match q.2 with | [] => [] | _ :: rest => evens rest)
        (encPair encBool (encList encNat)) (encList encNat)
        (fun q => (encList encNat q.2).length +
          (q.2.length + 1) * (listMax (fun v => (encNat v).length) q.2 + 1) ^ d_ev + 1)
        (fun q => (encList encNat q.2).length +
          (listMax (fun v => (encNat v).length) q.2 + 1) ^ d_ev + 1) := by
      refine ComputableInO.of_bounds hev_raw (3 * c_ev * 3 ^ d_ev + 4) (fun q => ?_) (fun q => ?_)
        (fun q => ?_)
      · rw [length_encPair]
        have hb : (encBool q.1).length ≤ 2 := by cases q.1 <;> simp
        have hp : (listMax (fun v => (encNat v).length) q.2 + 3) ^ d_ev ≤
            3 ^ d_ev * (listMax (fun v => (encNat v).length) q.2 + 1) ^ d_ev := by
          calc _ ≤ (3 * (listMax (fun v => (encNat v).length) q.2 + 1)) ^ d_ev :=
                Nat.pow_le_pow_left (by omega) d_ev
            _ = 3 ^ d_ev * (listMax (fun v => (encNat v).length) q.2 + 1) ^ d_ev :=
                Nat.mul_pow _ _ _
        have hmul : (q.2.length + 1) * (listMax (fun v => (encNat v).length) q.2 + 3) ^ d_ev ≤
            3 ^ d_ev *
              ((q.2.length + 1) * (listMax (fun v => (encNat v).length) q.2 + 1) ^ d_ev) := by
          calc _ ≤ (q.2.length + 1) *
                  (3 ^ d_ev * (listMax (fun v => (encNat v).length) q.2 + 1) ^ d_ev) :=
                Nat.mul_le_mul_left _ hp
            _ = _ := by ring
        set E := (encList encNat q.2).length
        set B := (q.2.length + 1) * (listMax (fun v => (encNat v).length) q.2 + 1) ^ d_ev
        have h1pow : 1 ≤ B := Nat.mul_pos (Nat.succ_pos _) (Nat.one_le_pow _ _ (Nat.succ_pos _))
        have h3pow : 1 ≤ 3 ^ d_ev := Nat.one_le_pow _ _ (by decide)
        have hsum : 2 * (encBool q.1).length + 1 + E +
            (q.2.length + 1) * (listMax (fun v => (encNat v).length) q.2 + 2 + 1) ^ d_ev + 1 ≤
            3 * 3 ^ d_ev * (E + B + 2) := by
          have h9 : listMax (fun v => (encNat v).length) q.2 + 2 + 1 =
              listMax (fun v => (encNat v).length) q.2 + 3 := by omega
          rw [h9]
          calc 2 * (encBool q.1).length + 1 + E +
                (q.2.length + 1) * (listMax (fun v => (encNat v).length) q.2 + 3) ^ d_ev + 1
              ≤ E + 3 ^ d_ev * B + 6 := by omega
            _ ≤ 3 * 3 ^ d_ev * (E + B + 2) := by nlinarith
        calc c_ev * (2 * (encBool q.1).length + 1 + E +
              (q.2.length + 1) * (listMax (fun v => (encNat v).length) q.2 + 2 + 1) ^ d_ev + 1)
            ≤ c_ev * (3 * 3 ^ d_ev * (E + B + 2)) := Nat.mul_le_mul_left _ hsum
          _ ≤ (3 * c_ev * 3 ^ d_ev + 4) * (E + B + 2) := by nlinarith
      · have hp : (listMax (fun v => (encNat v).length) q.2 + 3) ^ d_ev ≤
            3 ^ d_ev * (listMax (fun v => (encNat v).length) q.2 + 1) ^ d_ev := by
          calc _ ≤ (3 * (listMax (fun v => (encNat v).length) q.2 + 1)) ^ d_ev :=
                Nat.pow_le_pow_left (by omega) d_ev
            _ = 3 ^ d_ev * (listMax (fun v => (encNat v).length) q.2 + 1) ^ d_ev :=
                Nat.mul_pow _ _ _
        set E := (encList encNat q.2).length
        set A := (listMax (fun v => (encNat v).length) q.2 + 1) ^ d_ev
        have h1pow : 1 ≤ A := Nat.one_le_pow _ _ (Nat.succ_pos _)
        have h3pow : 1 ≤ 3 ^ d_ev := Nat.one_le_pow _ _ (by decide)
        have hsum : (listMax (fun v => (encNat v).length) q.2 + 2 + 1) ^ d_ev + 1 ≤
            3 * 3 ^ d_ev * (E + A + 2) := by
          have h9 : listMax (fun v => (encNat v).length) q.2 + 2 + 1 =
              listMax (fun v => (encNat v).length) q.2 + 3 := by omega
          rw [h9]
          calc (listMax (fun v => (encNat v).length) q.2 + 3) ^ d_ev + 1
              ≤ 3 ^ d_ev * A + 1 := Nat.add_le_add_right hp 1
            _ ≤ 3 * 3 ^ d_ev * (E + A + 2) := by nlinarith
        calc c_ev * ((listMax (fun v => (encNat v).length) q.2 + 2 + 1) ^ d_ev + 1)
            ≤ c_ev * (3 * 3 ^ d_ev * (E + A + 2)) := Nat.mul_le_mul_left _ hsum
          _ ≤ (3 * c_ev * 3 ^ d_ev + 4) * (E + A + 2) := by nlinarith
      · have hlen_g : (encList encNat (if q.1 then evens q.2
            else match q.2 with | [] => [] | _ :: rest => evens rest)).length ≤
            (encList encNat q.2).length := by
          cases q.1
          · cases q.2 with
            | nil => simp
            | cons a t =>
              simp only [Bool.false_eq_true, ↓reduceIte]
              exact (hlen_ev t).trans (by simp [encList_cons])
          · exact hlen_ev q.2
        calc _ ≤ (encList encNat q.2).length := hlen_g
          _ ≤ (encList encNat q.2).length +
                (listMax (fun v => (encNat v).length) q.2 + 1) ^ d_ev + 1 + 1 := by omega
          _ ≤ (3 * c_ev * 3 ^ d_ev + 4) * ((encList encNat q.2).length +
                (listMax (fun v => (encNat v).length) q.2 + 1) ^ d_ev + 1 + 1) :=
              Nat.le_mul_of_pos_left _ (by omega)
          _ = _ := by
              ring
    exact (hraw.comp hwrap).mono 2 (fun _ => by dsimp; omega) (fun _ => by dsimp; omega)
  have hnext_po : ComputableInPolyTime
      (fun q : (Bool × ℕ) × ℕ => if q.1.1 then (false, 0) else (true, q.2))
      (encPair (encPair encBool encNat) encNat) (encPair encBool encNat) := by fun_prop
  have hemit_po : ComputableInPolyTime
      (fun q : (Bool × ℕ) × ℕ => if q.1.1 then [q.1.2 + q.2] else [])
      (encPair (encPair encBool encNat) encNat) (encList encNat) := by fun_prop
  obtain ⟨c_po, d_po, hpo_raw⟩ := ComputableInTimeAndSpace.streamFold_pair_list
    (encA := encNat) (encS := encPair encBool encNat) (encB := encNat)
    (encIn := encPair (encPair encBool encNat) (encList encNat))
    (init := Prod.fst) (elems := Prod.snd) (fun _ => rfl) hnext_po hemit_po
    (g := fun q : (Bool × ℕ) × List ℕ =>
      if q.1.1 then match q.2 with | [] => [] | y :: rest => (q.1.2 + y) :: passOddsAdd rest
      else passOddsAdd q.2)
    (fun q => by
      rcases q with ⟨⟨b, prev⟩, L⟩
      cases b with
      | false =>
        cases L with
        | nil => rfl
        | cons x t =>
          have h1 := passOddsAdd_streamEmit (x :: t)
          simpa [streamEmit] using h1
      | true =>
        cases L with
        | nil => rfl
        | cons y rest =>
          simp only [↓reduceIte, encList_cons, streamEmit, encList_nil, List.append_nil]
          rw [passOddsAdd_streamEmit])
    (lMax := fun q => (encNat q.1.2).length + listMax (fun v => (encNat v).length) q.2 + 8)
    (fun q j hj => by
      let next_fn : (Bool × ℕ) × ℕ → Bool × ℕ :=
        fun q => if q.1.1 then (false, 0) else (true, q.2)
      have hst : (streamState q.1 next_fn q.2 j).2 = q.1.2 ∨
          (streamState q.1 next_fn q.2 j).2 = 0 ∨
          ∃ v ∈ q.2, (streamState q.1 next_fn q.2 j).2 = v := by
        have htake : ∀ xs : List ℕ, (∀ v ∈ xs, v ∈ q.2) → ∀ st : Bool × ℕ,
            (st.2 = q.1.2 ∨ st.2 = 0 ∨ ∃ v ∈ q.2, st.2 = v) →
            (xs.foldl (fun s a => if s.1 then (false, 0) else (true, a)) st).2 = q.1.2 ∨
            (xs.foldl (fun s a => if s.1 then (false, 0) else (true, a)) st).2 = 0 ∨
            ∃ v ∈ q.2, (xs.foldl (fun s a => if s.1 then (false, 0) else (true, a)) st).2 = v := by
          intro xs hxs st hst
          induction xs generalizing st with
          | nil => exact hst
          | cons a t ih =>
            apply ih (fun v hv => hxs v (List.mem_cons_of_mem _ hv))
            cases hb : st.1
            · right; right; exact ⟨a, hxs a (List.mem_cons_self ..), by simp [hb]⟩
            · right; left; simp [hb]
        exact htake (q.2.take j) (fun v hv => List.mem_of_mem_take hv) q.1 (Or.inl rfl)
      have hb : (encBool (streamState q.1 next_fn q.2 j).1).length ≤ 2 := by
        cases (streamState q.1 next_fn q.2 j).1 <;> simp
      have hn : (encNat (streamState q.1 next_fn q.2 j).2).length ≤
          (encNat q.1.2).length + listMax (fun v => (encNat v).length) q.2 := by
        rcases hst with h | h | ⟨v, hv, h⟩
        · rw [h]; omega
        · rw [h, encNat_apply, Nat.zero_bits]; simp
        · rw [h]
          exact (le_listMax (f := fun v => (encNat v).length) hv).trans (Nat.le_add_left _ _)
      change (encPair encBool encNat (streamState q.1 next_fn q.2 j)).length ≤ _
      rw [length_encPair]
      omega)
    (fun q j hj => (le_listMax (f := fun v => (encNat v).length) (List.getElem_mem hj)).trans
      (by omega))
  have hlen_po : ∀ L : List ℕ,
      (encList encNat (passOddsAdd L)).length ≤
        (encList encNat L).length + 2 * L.length := by
    intro L
    induction L using list_two_step_ind with
    | h0 => simp [passOddsAdd]
    | h1 a => simp [passOddsAdd]
    | h2 a b rest ih =>
      have hab : (encNat (a + b)).length ≤ (encNat a).length + (encNat b).length + 1 := by
        rw [encNat_apply, encNat_apply, encNat_apply, Nat.size_eq_bits_len, Nat.size_eq_bits_len,
          Nat.size_eq_bits_len]
        have ha_lt : a < 2 ^ Nat.size a := Nat.size_le.1 le_rfl
        have hb_lt : b < 2 ^ Nat.size b := Nat.size_le.1 le_rfl
        have hsum_lt : a + b < 2 ^ (max (Nat.size a) (Nat.size b) + 1) := by
          have ha1 : a < 2 ^ max (Nat.size a) (Nat.size b) :=
            ha_lt.trans_le (Nat.pow_le_pow_right (by decide) (le_max_left _ _))
          have hb1 : b < 2 ^ max (Nat.size a) (Nat.size b) :=
            hb_lt.trans_le (Nat.pow_le_pow_right (by decide) (le_max_right _ _))
          rw [pow_succ']
          omega
        exact (Nat.size_le.2 hsum_lt).trans (by omega)
      simp only [passOddsAdd, encList_cons, List.length_append, length_frame, List.length_cons]
      omega
  let D_po := max d_po 1
  have hpo : ComputableInO passOddsAdd (encList encNat) (encList encNat)
      (fun L => (encList encNat L).length +
        (L.length + 1) * (listMax (fun v => (encNat v).length) L + 1) ^ D_po + 1)
      (fun L => (encList encNat L).length + L.length +
        (listMax (fun v => (encNat v).length) L + 1) ^ D_po + 1) := by
    have hwrap : ComputableInO (fun L : List ℕ => ((false, 0), L))
        (encList encNat) (encPair (encPair encBool encNat) (encList encNat))
        (fun L => (encList encNat L).length) (fun L => (encList encNat L).length) := by
      have hp := (ComputableInO.constZero (encIn := encList encNat)
        (encMid := encPair encBool encNat) (false, 0)).prod
        (ComputableInO.id' (encMid := encList encNat))
      exact hp.mono 2 (fun _ => by omega) (fun _ => by omega)
    have hraw : ComputableInO
        (fun q : (Bool × ℕ) × List ℕ =>
          if q.1.1 then match q.2 with | [] => [] | y :: rest => (q.1.2 + y) :: passOddsAdd rest
          else passOddsAdd q.2)
        (encPair (encPair encBool encNat) (encList encNat)) (encList encNat)
        (fun q => (encPair encBool encNat q.1).length + (encList encNat q.2).length +
          (q.2.length + 1) * ((encNat q.1.2).length +
            listMax (fun v => (encNat v).length) q.2 + 1) ^ D_po + 1)
        (fun q => (encList encNat q.2).length + q.2.length + ((encNat q.1.2).length +
          listMax (fun v => (encNat v).length) q.2 + 1) ^ D_po + 1) := by
      have hp_fn : ∀ q : (Bool × ℕ) × List ℕ,
          ((encNat q.1.2).length + listMax (fun v => (encNat v).length) q.2 + 9) ^ d_po ≤
            9 ^ d_po * ((encNat q.1.2).length +
              listMax (fun v => (encNat v).length) q.2 + 1) ^ D_po := fun q => by
        calc _ ≤ (9 * ((encNat q.1.2).length +
                  listMax (fun v => (encNat v).length) q.2 + 1)) ^ d_po :=
                Nat.pow_le_pow_left (by omega) d_po
          _ = 9 ^ d_po * ((encNat q.1.2).length +
                listMax (fun v => (encNat v).length) q.2 + 1) ^ d_po := Nat.mul_pow _ _ _
          _ ≤ 9 ^ d_po * ((encNat q.1.2).length +
                listMax (fun v => (encNat v).length) q.2 + 1) ^ D_po :=
              Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_left _ _))
      refine ComputableInO.of_bounds hpo_raw (3 * c_po * 9 ^ d_po + 10) (fun q => ?_) (fun q => ?_)
        (fun q => ?_)
      · rw [length_encPair]
        have hp := hp_fn q
        set P := (encPair encBool encNat q.1).length
        set E := (encList encNat q.2).length
        set B := (q.2.length + 1) * ((encNat q.1.2).length +
            listMax (fun v => (encNat v).length) q.2 + 1) ^ D_po
        have hmul : (q.2.length + 1) * ((encNat q.1.2).length +
              listMax (fun v => (encNat v).length) q.2 + 9) ^ d_po ≤ 9 ^ d_po * B := by
          calc _ ≤ (q.2.length + 1) * (9 ^ d_po * ((encNat q.1.2).length +
                  listMax (fun v => (encNat v).length) q.2 + 1) ^ D_po) :=
                Nat.mul_le_mul_left _ hp
            _ = 9 ^ d_po * B := by ring
        have h1pow : 1 ≤ B := Nat.mul_pos (Nat.succ_pos _) (Nat.one_le_pow _ _ (Nat.succ_pos _))
        have h9pow : 1 ≤ 9 ^ d_po := Nat.one_le_pow _ _ (by decide)
        have hsum : 2 * P + 1 + E +
            (q.2.length + 1) * ((encNat q.1.2).length +
              listMax (fun v => (encNat v).length) q.2 + 8 + 1) ^ d_po + 1 ≤
            3 * 9 ^ d_po * (P + E + B + 1) := by
          rw [Nat.add_assoc ((encNat q.1.2).length + listMax (fun v => (encNat v).length) q.2) 8 1]
          calc 2 * P + 1 + E + (q.2.length + 1) * ((encNat q.1.2).length +
                listMax (fun v => (encNat v).length) q.2 + 9) ^ d_po + 1
              ≤ 2 * P + E + 9 ^ d_po * B + 2 := by omega
            _ ≤ 3 * 9 ^ d_po * (P + E + B + 1) := by nlinarith
        calc c_po * (2 * P + 1 + E + (q.2.length + 1) * ((encNat q.1.2).length +
                listMax (fun v => (encNat v).length) q.2 + 8 + 1) ^ d_po + 1)
            ≤ c_po * (3 * 9 ^ d_po * (P + E + B + 1)) := Nat.mul_le_mul_left _ hsum
          _ ≤ (3 * c_po * 9 ^ d_po + 10) * (P + E + B + 1 + 1) := by nlinarith
      · have hp := hp_fn q
        set E := (encList encNat q.2).length
        set A := ((encNat q.1.2).length + listMax (fun v => (encNat v).length) q.2 + 1) ^ D_po
        have h1pow : 1 ≤ A := Nat.one_le_pow _ _ (Nat.succ_pos _)
        have h9pow : 1 ≤ 9 ^ d_po := Nat.one_le_pow _ _ (by decide)
        have hsum : ((encNat q.1.2).length +
              listMax (fun v => (encNat v).length) q.2 + 8 + 1) ^ d_po + 1 ≤
            3 * 9 ^ d_po * (E + q.2.length + A + 2) := by
          rw [Nat.add_assoc ((encNat q.1.2).length + listMax (fun v => (encNat v).length) q.2) 8 1]
          calc ((encNat q.1.2).length +
                  listMax (fun v => (encNat v).length) q.2 + 9) ^ d_po + 1
              ≤ 9 ^ d_po * A + 1 := Nat.add_le_add_right hp 1
            _ ≤ 3 * 9 ^ d_po * (E + q.2.length + A + 2) := by nlinarith
        calc c_po * (((encNat q.1.2).length +
                listMax (fun v => (encNat v).length) q.2 + 8 + 1) ^ d_po + 1)
            ≤ c_po * (3 * 9 ^ d_po * (E + q.2.length + A + 2)) := Nat.mul_le_mul_left _ hsum
          _ ≤ (3 * c_po * 9 ^ d_po + 10) * (E + q.2.length + A + 1 + 1) := by nlinarith
      · have hlen_g : (encList encNat
            (if q.1.1 then match q.2 with | [] => [] | y :: rest => (q.1.2 + y) :: passOddsAdd rest
            else passOddsAdd q.2)).length ≤
            3 * ((encNat q.1.2).length +
              listMax (fun v => (encNat v).length) q.2 + 1) +
            (encList encNat q.2).length + 2 * q.2.length := by
          rcases q with ⟨⟨b, prev⟩, L⟩
          cases b
          · simp only [Bool.false_eq_true, ↓reduceIte]
            exact (hlen_po L).trans (by omega)
          · cases L with
            | nil => simp
            | cons y rest =>
              simp only [↓reduceIte, encList_cons, List.length_append, length_frame,
                List.length_cons]
              have hy : (encNat y).length ≤ listMax (fun v => (encNat v).length) (y :: rest) :=
                le_listMax (f := fun v => (encNat v).length) (List.mem_cons_self ..)
              have hadd : (encNat (prev + y)).length ≤
                  (encNat prev).length + (encNat y).length + 1 := by
                rw [encNat_apply, encNat_apply, encNat_apply, Nat.size_eq_bits_len,
                  Nat.size_eq_bits_len, Nat.size_eq_bits_len]
                have hp_lt := Nat.size_le.1 (le_refl prev.size)
                have hy_lt := Nat.size_le.1 (le_refl y.size)
                have hs : prev + y < 2 ^ (max (Nat.size prev) (Nat.size y) + 1) := by
                  have h1 := hp_lt.trans_le
                    (Nat.pow_le_pow_right (by decide) (le_max_left prev.size y.size))
                  have h2 := hy_lt.trans_le
                    (Nat.pow_le_pow_right (by decide) (le_max_right prev.size y.size))
                  rw [pow_succ']; omega
                exact (Nat.size_le.2 hs).trans (by omega)
              have hr := hlen_po rest
              omega
        have hpow_1 : ((encNat q.1.2).length + listMax (fun v => (encNat v).length) q.2 + 1) ≤
            ((encNat q.1.2).length + listMax (fun v => (encNat v).length) q.2 + 1) ^ D_po :=
          Nat.le_self_pow (by dsimp only [D_po]; omega) _
        have h9pow : 1 ≤ 9 ^ d_po := Nat.one_le_pow _ _ (by decide)
        calc (encList encNat (if q.1.1 then
              match q.2 with | [] => [] | y :: rest => (q.1.2 + y) :: passOddsAdd rest
              else passOddsAdd q.2)).length
            ≤ 3 * ((encNat q.1.2).length + listMax (fun v => (encNat v).length) q.2 + 1) +
                (encList encNat q.2).length + 2 * q.2.length := hlen_g
          _ ≤ 3 * ((encList encNat q.2).length + q.2.length +
                ((encNat q.1.2).length + listMax (fun v => (encNat v).length) q.2 + 1) ^ D_po +
                1 + 1) := by omega
          _ ≤ (3 * c_po * 9 ^ d_po + 10) * ((encList encNat q.2).length + q.2.length +
                ((encNat q.1.2).length + listMax (fun v => (encNat v).length) q.2 + 1) ^ D_po +
                1 + 1) := Nat.mul_le_mul_right _ (by omega)
    exact (hraw.comp hwrap).mono 2 (fun L => by
      have h0 : (encNat 0).length = 0 := by simp [encNat_apply]
      have hb0 : (encPair encBool encNat (false, 0)).length ≤ 3 := by
        rw [length_encPair, h0]; simp
      dsimp only [Function.comp_apply]
      rw [h0, Nat.zero_add]
      omega) (fun L => by
      have h0 : (encNat 0).length = 0 := by simp [encNat_apply]
      dsimp only [Function.comp_apply]
      rw [h0, Nat.zero_add]
      omega)
  let D_st := max d_ev D_po
  have hyst : ComputableInO yatesStep (encList encNat) (encList encNat)
      (fun L => (encList encNat L).length +
        (L.length + 1) * (listMax (fun v => (encNat v).length) L + 1) ^ D_st + 1)
      (fun L => (encList encNat L).length + L.length +
        (listMax (fun v => (encNat v).length) L + 1) ^ D_st + 1) := by
    have happ := (ComputableInO.of_linear (ComputableInDegree.listAppend encNat)).comp_linear
      (hev.prod hpo)
    refine happ.mono 4 (fun L => ?_) (fun L => ?_)
    · have hp1 : (listMax (fun v => (encNat v).length) L + 1) ^ d_ev ≤
          (listMax (fun v => (encNat v).length) L + 1) ^ D_st :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_left _ _)
      have hp2 : (listMax (fun v => (encNat v).length) L + 1) ^ D_po ≤
          (listMax (fun v => (encNat v).length) L + 1) ^ D_st :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_right _ _)
      have hm1 := Nat.mul_le_mul_left (L.length + 1) hp1
      have hm2 := Nat.mul_le_mul_left (L.length + 1) hp2
      omega
    · have hp1 : (listMax (fun v => (encNat v).length) L + 1) ^ d_ev ≤
          (listMax (fun v => (encNat v).length) L + 1) ^ D_st :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_left _ _)
      have hp2 : (listMax (fun v => (encNat v).length) L + 1) ^ D_po ≤
          (listMax (fun v => (encNat v).length) L + 1) ^ D_st :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_right _ _)
      omega
  obtain ⟨c_cm, hcm⟩ := computableInO_countMasks
  have hmax_k : ∀ x : SymAndInstance, ∀ k ≤ x.n,
      listMax (fun v => (encNat v).length) (yatesStep^[k] (countMasks x)) ≤
        x.n + Nat.log2 ((encSymAndInstance x).length + 1) + 1 := fun x k hk => by
    refine listMax_le fun v hv => ?_
    have hmem := yatesStep_iter_mem_le x k v hv
    have hg := gates_length_le_encSymAndInstance x
    have hpow : 2 ^ k * x.gates.length ≤ 2 ^ x.n * ((encSymAndInstance x).length + 1) :=
      Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) hk) (by omega)
    exact (length_encNat_mono (hmem.trans hpow)).trans
      (length_encNat_mul_pow_le x.n (encSymAndInstance x).length)
  have henc_k : ∀ x : SymAndInstance, ∀ k ≤ x.n,
      (encList encNat (yatesStep^[k] (countMasks x))).length ≤
        2 ^ x.n * (2 * (x.n + Nat.log2 ((encSymAndInstance x).length + 1) + 1) + 1) :=
    fun x k hk => by
      have hlen : (yatesStep^[k] (countMasks x)).length = 2 ^ x.n :=
        length_yatesStep_iter_two_pow (countMasks_length x) hk
      have haux : ∀ l : List ℕ,
          (∀ v ∈ l, (encNat v).length ≤ x.n + Nat.log2 ((encSymAndInstance x).length + 1) + 1) →
          (encList encNat l).length ≤
            l.length * (2 * (x.n + Nat.log2 ((encSymAndInstance x).length + 1) + 1) + 1) := by
        intro l hl
        induction l with
        | nil => simp
        | cons a t ih =>
          have ha := hl a (List.mem_cons_self ..)
          have ht := ih fun b hb => hl b (List.mem_cons_of_mem _ hb)
          rw [encList_cons, List.length_append, List.length_cons, length_frame]
          nlinarith
      have hm : ∀ v ∈ yatesStep^[k] (countMasks x),
          (encNat v).length ≤ x.n + Nat.log2 ((encSymAndInstance x).length + 1) + 1 :=
        fun v hv => (le_listMax hv).trans (hmax_k x k hk)
      calc (encList encNat (yatesStep^[k] (countMasks x))).length
          ≤ (yatesStep^[k] (countMasks x)).length *
              (2 * (x.n + Nat.log2 ((encSymAndInstance x).length + 1) + 1) + 1) := haux _ hm
        _ = 2 ^ x.n * (2 * (x.n + Nat.log2 ((encSymAndInstance x).length + 1) + 1) + 1) := by
            rw [hlen]
  let R_y (x : SymAndInstance) :=
    2 * (2 ^ x.n * (2 * (x.n + Nat.log2 ((encSymAndInstance x).length + 1) + 1) + 1)) +
      (2 ^ x.n + 1) * (x.n + Nat.log2 ((encSymAndInstance x).length + 1) + 2) ^ D_st + 1
  have hit := ComputableInO.iterate computableInO_n_nat hcm hyst
    (R := R_y) (Q := R_y)
    (B := fun x => 2 ^ x.n * (2 * (x.n + Nat.log2 ((encSymAndInstance x).length + 1) + 1) + 1))
    (fun x k hk => by
      have h1 := henc_k x k hk
      have h2 : (yatesStep^[k] (countMasks x)).length = 2 ^ x.n :=
        length_yatesStep_iter_two_pow (countMasks_length x) hk
      have h3 := hmax_k x k hk
      have hp : (listMax (fun v => (encNat v).length) (yatesStep^[k] (countMasks x)) + 1) ^ D_st ≤
          (x.n + Nat.log2 ((encSymAndInstance x).length + 1) + 2) ^ D_st :=
        Nat.pow_le_pow_left (by omega) D_st
      have hm := Nat.mul_le_mul_left (2 ^ x.n + 1) hp
      have h1' : (encList encNat (yatesStep^[k] (countMasks x))).length ≤
          2 * (2 ^ x.n * (2 * (x.n + Nat.log2 ((encSymAndInstance x).length + 1) + 1) + 1)) :=
        h1.trans (by omega)
      dsimp only [R_y]
      rw [h2]
      exact Nat.add_le_add (Nat.add_le_add h1' hm) le_rfl)
    (fun x k hk => by
      have h1 := henc_k x k hk
      have h2 : (yatesStep^[k] (countMasks x)).length = 2 ^ x.n :=
        length_yatesStep_iter_two_pow (countMasks_length x) hk
      have h3 := hmax_k x k hk
      have hp : (listMax (fun v => (encNat v).length) (yatesStep^[k] (countMasks x)) + 1) ^ D_st ≤
          (x.n + Nat.log2 ((encSymAndInstance x).length + 1) + 2) ^ D_st :=
        Nat.pow_le_pow_left (by omega) D_st
      have hp2 : (listMax (fun v => (encNat v).length) (yatesStep^[k] (countMasks x)) + 1) ^ D_st ≤
          (2 ^ x.n + 1) * (x.n + Nat.log2 ((encSymAndInstance x).length + 1) + 2) ^ D_st :=
        hp.trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
      have h2n_1 : 2 ^ x.n ≤
          2 ^ x.n * (2 * (x.n + Nat.log2 ((encSymAndInstance x).length + 1) + 1) + 1) :=
        Nat.le_mul_of_pos_right _ (by omega)
      dsimp only [R_y]
      rw [h2]
      exact Nat.add_le_add (Nat.add_le_add (by omega) hp2) le_rfl)
    (fun x k hk => henc_k x k hk)
  let C_y := max c_cm (D_st + 2) + 2 * D_st + 4
  have hR_bound : ∀ x : SymAndInstance, R_y x ≤
      18 ^ (D_st + 2) * ((2 ^ x.n + ((encSymAndInstance x).length + 1) ^ (D_st + 1)) *
        (x.n + 1) ^ (2 * D_st)) := fun x => by
    set A := (encSymAndInstance x).length + 1
    set N := x.n + 1
    have hn_le := n_le_encSymAndInstance x
    have hbase : x.n + Nat.log2 A + 2 ≤ N * (Nat.log2 A + 2) := by
      have hL1 : 1 ≤ Nat.log2 A + 2 := by omega
      have h1 : x.n ≤ x.n * (Nat.log2 A + 2) := Nat.le_mul_of_pos_right _ hL1
      have h2 : N * (Nat.log2 A + 2) = x.n * (Nat.log2 A + 2) + (Nat.log2 A + 2) := by
        dsimp only [N]; ring
      omega
    have hpow_b : (x.n + Nat.log2 A + 2) ^ D_st ≤ N ^ D_st * (Nat.log2 A + 2) ^ D_st := by
      calc _ ≤ (N * (Nat.log2 A + 2)) ^ D_st := Nat.pow_le_pow_left hbase D_st
        _ = N ^ D_st * (Nat.log2 A + 2) ^ D_st := Nat.mul_pow _ _ _
    have hlog := radix_log_absorb x.n A D_st (Nat.succ_pos _)
    have hmul_b : (2 ^ x.n + 1) * (x.n + Nat.log2 A + 2) ^ D_st ≤
        2 * 3 ^ (D_st + 1) * 2 ^ D_st * (2 ^ x.n + A ^ (D_st + 1)) * N ^ (2 * D_st) := by
      have h1 : (2 ^ x.n + 1) * (x.n + Nat.log2 A + 2) ^ D_st ≤
          (2 ^ x.n + A) * (N ^ D_st * (Nat.log2 A + 2) ^ D_st) :=
        Nat.mul_le_mul (by omega) hpow_b
      calc (2 ^ x.n + 1) * (x.n + Nat.log2 A + 2) ^ D_st
          ≤ N ^ D_st * ((2 ^ x.n + A) * (Nat.log2 A + 2) ^ D_st) := by nlinarith
        _ ≤ N ^ D_st * (2 * 3 ^ (D_st + 1) * 2 ^ D_st * (2 ^ x.n + A ^ (D_st + 1)) * N ^ D_st) :=
            Nat.mul_le_mul_left _ hlog
        _ = 2 * 3 ^ (D_st + 1) * 2 ^ D_st * (2 ^ x.n + A ^ (D_st + 1)) * N ^ (2 * D_st) := by
            ring
    have hR_le : R_y x ≤
        12 * 3 ^ (D_st + 1) * 2 ^ D_st * (2 ^ x.n + A ^ (D_st + 1)) * N ^ (2 * D_st) := by
      have hbox1 : 1 ≤ (2 ^ x.n + A ^ (D_st + 1)) * N ^ (2 * D_st) :=
        Nat.mul_pos (by have := Nat.one_le_pow x.n 2 (by decide); omega)
          (Nat.one_le_pow _ _ (Nat.succ_pos _))
      have hc1 : 1 ≤ 3 ^ (D_st + 1) * 2 ^ D_st :=
        Nat.mul_pos (Nat.one_le_pow _ _ (by decide)) (Nat.one_le_pow _ _ (by decide))
      have hc_le : 1 ≤ 3 ^ (D_st + 1) * 2 ^ D_st *
          ((2 ^ x.n + A ^ (D_st + 1)) * N ^ (2 * D_st)) := Nat.mul_pos hc1 hbox1
      have h5 : R_y x ≤ 5 * ((2 ^ x.n + 1) * (x.n + Nat.log2 A + 2) ^ D_st) + 1 := by
        have hD1 : 1 ≤ D_st := by
          dsimp only [D_st, D_po]; exact le_trans (le_max_right _ _) (le_max_right _ _)
        have h1 : 2 * (x.n + Nat.log2 A + 1) + 1 ≤ 2 * (x.n + Nat.log2 A + 2) ^ 1 := by simp
        have h2 : (x.n + Nat.log2 A + 2) ^ 1 ≤ (x.n + Nat.log2 A + 2) ^ D_st :=
          Nat.pow_le_pow_right (by omega) hD1
        have hlin : 2 ^ x.n * (2 * (x.n + Nat.log2 A + 1) + 1) ≤
            2 * ((2 ^ x.n + 1) * (x.n + Nat.log2 A + 2) ^ D_st) := by
          calc 2 ^ x.n * (2 * (x.n + Nat.log2 A + 1) + 1)
              ≤ (2 ^ x.n + 1) * (2 * (x.n + Nat.log2 A + 2) ^ D_st) :=
                Nat.mul_le_mul (by omega) (h1.trans (Nat.mul_le_mul_left 2 h2))
            _ = 2 * ((2 ^ x.n + 1) * (x.n + Nat.log2 A + 2) ^ D_st) := by ring
        dsimp only [A, R_y] at hlin ⊢
        omega
      calc R_y x ≤ 5 * ((2 ^ x.n + 1) * (x.n + Nat.log2 A + 2) ^ D_st) + 1 := h5
        _ ≤ 5 * (2 * 3 ^ (D_st + 1) * 2 ^ D_st * (2 ^ x.n + A ^ (D_st + 1)) *
              N ^ (2 * D_st)) + 1 := Nat.add_le_add_right (Nat.mul_le_mul_left 5 hmul_b) 1
        _ = 10 * (3 ^ (D_st + 1) * 2 ^ D_st *
              ((2 ^ x.n + A ^ (D_st + 1)) * N ^ (2 * D_st))) + 1 := by ring
        _ ≤ 12 * (3 ^ (D_st + 1) * 2 ^ D_st *
              ((2 ^ x.n + A ^ (D_st + 1)) * N ^ (2 * D_st))) := by omega
        _ = _ := by ring
    have hc18 : 12 * 3 ^ (D_st + 1) * 2 ^ D_st ≤ 18 ^ (D_st + 2) := by
      have h2 : 6 ^ D_st ≤ 18 ^ D_st := Nat.pow_le_pow_left (by decide) D_st
      calc 12 * 3 ^ (D_st + 1) * 2 ^ D_st = 36 * (3 ^ D_st * 2 ^ D_st) := by ring
        _ = 36 * 6 ^ D_st := by rw [← Nat.mul_pow]
        _ ≤ 324 * 18 ^ D_st := Nat.mul_le_mul (by decide) h2
        _ = 18 ^ (D_st + 2) := by ring
    calc R_y x ≤ (12 * 3 ^ (D_st + 1) * 2 ^ D_st) *
            ((2 ^ x.n + A ^ (D_st + 1)) * N ^ (2 * D_st)) := by
          calc R_y x ≤ 12 * 3 ^ (D_st + 1) * 2 ^ D_st *
                  (2 ^ x.n + A ^ (D_st + 1)) * N ^ (2 * D_st) := hR_le
            _ = _ := by ring
      _ ≤ 18 ^ (D_st + 2) * ((2 ^ x.n + A ^ (D_st + 1)) * N ^ (2 * D_st)) :=
          Nat.mul_le_mul_right _ hc18
  have hy_common : ∀ x : SymAndInstance,
      (encNat x.n).length ≤ x.n + 1 ∧
      (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ c_cm) * (x.n + 1) ^ c_cm ≤
        (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_y) * (x.n + 1) ^ C_y ∧
      (encSymAndInstance x).length ≤
        (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_y) * (x.n + 1) ^ C_y := fun x => by
    set A := (encSymAndInstance x).length + 1
    set N := x.n + 1
    have hlen_n : (encNat x.n).length ≤ x.n + 1 :=
      (length_encNat_le_of_lt_two_pow (Nat.lt_pow_self (a := 2) (by decide))).trans (Nat.le_succ _)
    have hcm : (2 ^ x.n + A ^ c_cm) * N ^ c_cm ≤ (2 ^ x.n + A ^ C_y) * N ^ C_y :=
      Nat.mul_le_mul (Nat.add_le_add_left
        (Nat.pow_le_pow_right (Nat.succ_pos _) (by dsimp only [C_y]; omega)) _)
        (Nat.pow_le_pow_right (Nat.succ_pos _) (by dsimp only [C_y]; omega))
    have hx_a : (encSymAndInstance x).length ≤ A ^ C_y :=
      (Nat.le_succ _).trans (Nat.le_self_pow (by dsimp only [C_y]; omega) _)
    exact ⟨hlen_n, hcm, (hx_a.trans (Nat.le_add_left _ _)).trans
      (Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (Nat.succ_pos _)))⟩
  refine ⟨C_y, hit.mono (8 * 18 ^ (D_st + 2)) (fun x => ?_) (fun x => ?_)⟩
  · set A := (encSymAndInstance x).length + 1
    set N := x.n + 1
    set B := (2 ^ x.n + A ^ C_y) * N ^ C_y
    obtain ⟨hlen_n, hcm_le, hx_le⟩ := hy_common x
    change (2 ^ x.n + A ^ c_cm) * N ^ c_cm ≤ B at hcm_le
    change (encSymAndInstance x).length ≤ B at hx_le
    have hA_d : A ^ (D_st + 1) ≤ A ^ C_y :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (by dsimp only [C_y]; omega)
    have hN_d : N ^ (2 * D_st + 1) ≤ N ^ C_y :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (by dsimp only [C_y]; omega)
    have hN_R : N * R_y x ≤ 18 ^ (D_st + 2) * B := by
      calc N * R_y x ≤ N * (18 ^ (D_st + 2) * ((2 ^ x.n + A ^ (D_st + 1)) * N ^ (2 * D_st))) :=
            Nat.mul_le_mul_left _ (hR_bound x)
        _ = 18 ^ (D_st + 2) * ((2 ^ x.n + A ^ (D_st + 1)) * N ^ (2 * D_st + 1)) := by ring
        _ ≤ 18 ^ (D_st + 2) * B :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.add_le_add_left hA_d _) hN_d)
    have hsq : ((encNat x.n).length + 1) ^ 2 ≤ 4 * N ^ 2 := by
      have : (encNat x.n).length + 1 ≤ 2 * N := by omega
      calc _ ≤ (2 * N) ^ 2 := Nat.pow_le_pow_left this 2
        _ = 4 * N ^ 2 := by ring
    have hN_3 : N ^ 3 ≤ N ^ C_y :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (by dsimp only [C_y]; omega)
    have h2n1 : 1 ≤ 2 ^ x.n := Nat.one_le_pow _ _ (by decide)
    have hN_sq : N * ((encNat x.n).length + 1) ^ 2 ≤ 4 * B := by
      calc N * ((encNat x.n).length + 1) ^ 2 ≤ N * (4 * N ^ 2) := Nat.mul_le_mul_left _ hsq
        _ = 4 * (1 * N ^ 3) := by ring
        _ ≤ 4 * B := Nat.mul_le_mul_left 4 (Nat.mul_le_mul (by omega) hN_3)
    have hN_B : N * (2 ^ x.n * (2 * (x.n + Nat.log2 A + 1) + 1)) ≤ N * R_y x :=
      Nat.mul_le_mul_left _ (by dsimp only [A, R_y]; omega)
    have h18_pos : 1 ≤ 18 ^ (D_st + 2) := Nat.one_le_pow _ _ (by decide)
    have hN_sum : N * (R_y x + 2 ^ x.n * (2 * (x.n + Nat.log2 A + 1) + 1) +
        ((encNat x.n).length + 1) ^ 2) ≤ (2 * 18 ^ (D_st + 2) + 4) * B := by
      calc N * (R_y x + 2 ^ x.n * (2 * (x.n + Nat.log2 A + 1) + 1) +
              ((encNat x.n).length + 1) ^ 2)
          = N * R_y x + N * (2 ^ x.n * (2 * (x.n + Nat.log2 A + 1) + 1)) +
              N * ((encNat x.n).length + 1) ^ 2 := by ring
        _ ≤ 18 ^ (D_st + 2) * B + 18 ^ (D_st + 2) * B + 4 * B :=
            Nat.add_le_add (Nat.add_le_add hN_R (hN_B.trans hN_R)) hN_sq
        _ = (2 * 18 ^ (D_st + 2) + 4) * B := by ring
    calc (encSymAndInstance x).length + (2 ^ x.n + A ^ c_cm) * N ^ c_cm +
          N * (R_y x + 2 ^ x.n * (2 * (x.n + Nat.log2 A + 1) + 1) +
            ((encNat x.n).length + 1) ^ 2)
        ≤ B + B + (2 * 18 ^ (D_st + 2) + 4) * B := by linarith only [hx_le, hcm_le, hN_sum]
      _ = (2 * 18 ^ (D_st + 2) + 6) * B := by ring
      _ ≤ 8 * 18 ^ (D_st + 2) * (B + 1) := by
          have : 2 * 18 ^ (D_st + 2) + 6 ≤ 8 * 18 ^ (D_st + 2) := by omega
          exact Nat.mul_le_mul this (Nat.le_succ _)
  · set A := (encSymAndInstance x).length + 1
    set N := x.n + 1
    set B := (2 ^ x.n + A ^ C_y) * N ^ C_y
    obtain ⟨hlen_n, hcm_le, hx_le⟩ := hy_common x
    change (2 ^ x.n + A ^ c_cm) * N ^ c_cm ≤ B at hcm_le
    change (encSymAndInstance x).length ≤ B at hx_le
    have hA_d : A ^ (D_st + 1) ≤ A ^ C_y :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (by dsimp only [C_y]; omega)
    have hN_d : N ^ (2 * D_st) ≤ N ^ C_y :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (by dsimp only [C_y]; omega)
    have hR_fin : R_y x ≤ 18 ^ (D_st + 2) * B :=
      (hR_bound x).trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.add_le_add_left hA_d _) hN_d))
    have hn_box : (encNat x.n).length ≤ B := by
      have h2n1 : 1 ≤ 2 ^ x.n := Nat.one_le_pow _ _ (by decide)
      have hNc : N ≤ N ^ C_y := Nat.le_self_pow (by dsimp only [C_y]; omega) _
      exact (hlen_n.trans hNc).trans (Nat.le_mul_of_pos_left _ (by omega))
    have hB_le : 2 ^ x.n * (2 * (x.n + Nat.log2 A + 1) + 1) ≤ R_y x := by
      dsimp only [A, R_y]; omega
    have h18_pos : 1 ≤ 18 ^ (D_st + 2) := Nat.one_le_pow _ _ (by decide)
    calc (encSymAndInstance x).length + (2 ^ x.n + A ^ c_cm) * N ^ c_cm + R_y x +
          2 ^ x.n * (2 * (x.n + Nat.log2 A + 1) + 1) + (encNat x.n).length
        ≤ B + B + 18 ^ (D_st + 2) * B + 18 ^ (D_st + 2) * B + B := by
          linarith only [hx_le, hcm_le, hR_fin, hB_le, hn_box]
      _ = (2 * 18 ^ (D_st + 2) + 3) * B := by ring
      _ ≤ 8 * 18 ^ (D_st + 2) * (B + 1) := by
          have : 2 * 18 ^ (D_st + 2) + 3 ≤ 8 * 18 ^ (D_st + 2) := by omega
          exact Nat.mul_le_mul this (Nat.le_succ _)

/-! ### Stage 4 & 5: Tabulating `out`, radix join, and restoring mask order -/

private abbrev JoinItem := List Bool × (Bool × (ℕ × Bool))

private abbrev encJoinItem : JoinItem ↪ List Bool :=
  encPair encBits (encPair encBool (encPair encNat encBool))

private def tabulateStep (out : ℕ → Bool) (p : ℕ × List JoinItem) : ℕ × List JoinItem :=
  (p.1 + 1, (Nat.bits p.1, (false, (0, out p.1))) :: p.2)

private def tabulateOut (out : ℕ → Bool) (s : ℕ) : List JoinItem :=
  (Nat.bits s, (false, (0, out s))) :: ((tabulateStep out)^[s] (0, [])).2

private def queryEntriesFrom : ℕ → List ℕ → List JoinItem
  | _, [] => []
  | k, v :: rest => (Nat.bits v, (true, (k, false))) :: queryEntriesFrom (k + 1) rest

private def queryEntries (g : List ℕ) : List JoinItem :=
  queryEntriesFrom 0 g

private def extractMatched : Bool → List JoinItem → List (List Bool × Bool)
  | _, [] => []
  | cur, p :: rest =>
    if p.2.1 then (Nat.bits p.2.2.1, cur) :: extractMatched cur rest
    else extractMatched p.2.2.2 rest

private theorem tabulateStep_iter (out : ℕ → Bool) (k : ℕ) :
    ((tabulateStep out)^[k] (0, [])).1 = k ∧
      ((tabulateStep out)^[k] (0, [])).2 =
        (List.range k).reverse.map fun j => (Nat.bits j, (false, (0, out j))) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', tabulateStep, ih.1, ih.2, List.range_succ,
      List.reverse_append, List.reverse_singleton, List.singleton_append, List.map_cons]
    exact ⟨rfl, rfl⟩

private theorem tabulateOut_eq (out : ℕ → Bool) (s : ℕ) :
    tabulateOut out s =
      (List.range (s + 1)).reverse.map fun j => (Nat.bits j, (false, (0, out j))) := by
  rw [tabulateOut, (tabulateStep_iter out s).2, List.range_succ, List.reverse_append,
    List.reverse_singleton, List.singleton_append, List.map_cons]

private theorem evalBits_bits_of_le {v s : ℕ} (hv : v ≤ s) :
    evalBits (Nat.size s) (Nat.bits v) = v := by
  have hsz : Nat.size v ≤ Nat.size s := Nat.size_le_size hv
  exact evalBits_bits (Nat.size s) v (Nat.size_le.1 hsz)

private theorem length_encJoinItem_le (key : List Bool) (isQ : Bool) (k : ℕ) (bit : Bool) :
    (encJoinItem (key, (isQ, (k, bit)))).length ≤
      2 * key.length + 4 * (encNat k).length + 24 := by
  have hb1 : (encBool isQ).length ≤ 2 := by cases isQ <;> simp
  have hb2 : (encBool bit).length ≤ 2 := by cases bit <;> simp
  simp only [encJoinItem, length_encPair, encBits_apply]
  omega

private theorem queryEntriesFrom_streamEmit (k : ℕ) (g : List ℕ) :
    encList encJoinItem (queryEntriesFrom k g) =
      streamEmit (fun q : ℕ × ℕ => q.1 + 1)
        (fun q => encList encJoinItem [(Nat.bits q.2, (true, (q.1, false)))]) k g := by
  induction g generalizing k with
  | nil => rfl
  | cons v rest ih =>
    simp [queryEntriesFrom, streamEmit, encList_cons, ih]

private theorem extractMatched_streamEmit (c : Bool) (L : List JoinItem) :
    encList (encPair encBits encBool) (extractMatched c L) =
      streamEmit (fun q : Bool × JoinItem => if q.2.2.1 then q.1 else q.2.2.2.2)
        (fun q => encList (encPair encBits encBool)
          (if q.2.2.1 then [(Nat.bits q.2.2.2.1, q.1)] else [])) c L := by
  induction L generalizing c with
  | nil => rfl
  | cons a rest ih =>
    rw [extractMatched, streamEmit]
    cases h : a.2.1 <;> simp only [Bool.false_eq_true, ↓reduceIte, encList_cons, encList_nil,
      List.nil_append, List.append_nil, ih]

private theorem queryEntriesFrom_mem {k : ℕ} {g : List ℕ} {p : JoinItem}
    (hp : p ∈ queryEntriesFrom k g) :
    p.2.1 = true ∧ p.2.2.1 < k + g.length ∧ p.2.2.1 ≥ k ∧
      ∃ j : ℕ, ∃ hj : j < g.length, p = (Nat.bits g[j], (true, (k + j, false))) := by
  induction g generalizing k with
  | nil => simp [queryEntriesFrom] at hp
  | cons v rest ih =>
    simp only [queryEntriesFrom, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨rfl, by simp, le_rfl, 0, by simp, rfl⟩
    · obtain ⟨hq, hlt, hge, j, hj, hpeq⟩ := ih hp
      refine ⟨hq, by simp; omega, by omega, j + 1, by simp; omega, ?_⟩
      simpa [Nat.add_assoc, Nat.add_comm 1 j] using hpeq

private theorem queryEntriesFrom_filter_eq (k s : ℕ) (g : List ℕ) (hg : ∀ v ∈ g, v ≤ s)
    (v : ℕ) :
    (queryEntriesFrom k g).filter (fun p => evalBits (Nat.size s) p.1 == v) =
      ((List.range g.length).filter (fun j => g[j]?.getD 0 == v)).map
        fun j => (Nat.bits v, (true, (k + j, false))) := by
  induction g generalizing k with
  | nil => simp [queryEntriesFrom]
  | cons w rest ih =>
    have hw : w ≤ s := hg w (List.mem_cons_self ..)
    have hrest : ∀ u ∈ rest, u ≤ s := fun u hu => hg u (List.mem_cons_of_mem _ hu)
    have ihr := ih (k + 1) hrest
    rw [queryEntriesFrom, List.filter_cons, List.length_cons, List.range_succ_eq_map,
      List.filter_cons]
    have hev : evalBits (Nat.size s) (Nat.bits w) = w := evalBits_bits_of_le hw
    have hshift :
        ((List.map Nat.succ (List.range rest.length)).filter
            (fun j => ((w :: rest)[j]?.getD 0 == v))).map
          (fun j => (Nat.bits v, (true, (k + j, false)))) =
        ((List.range rest.length).filter (fun j => rest[j]?.getD 0 == v)).map
          (fun j => (Nat.bits v, (true, (k + 1 + j, false)))) := by
      rw [List.filter_map, List.map_map]
      congr 1
      funext j
      simp only [Function.comp_apply]
      rw [Nat.add_assoc, Nat.add_comm 1 j]
    by_cases hvw : w = v
    · subst hvw
      simp only [hev, beq_self_eq_true, ↓reduceIte, List.getElem?_cons_zero, Option.getD_some,
        List.map_cons, Nat.add_zero]
      rw [ihr, hshift]
    · have hb1 : (evalBits (Nat.size s) (Nat.bits w) == v) = false := by
        simp [hev, hvw]
      have hb2 : ((w :: rest)[0]?.getD 0 == v) = false := by simp [hvw]
      simp only [hb1, Bool.false_eq_true, ↓reduceIte, hb2]
      rw [ihr, hshift]

private theorem extractMatched_bucket_append (c : Bool) (key : List Bool) (out_v : Bool)
    (Q : List JoinItem) (hQ : ∀ q ∈ Q, q.2.1 = true) (rest : List JoinItem) :
    extractMatched c ((key, (false, (0, out_v))) :: (Q ++ rest)) =
      (Q.map fun q => (Nat.bits q.2.2.1, out_v)) ++ extractMatched out_v rest := by
  have hQ_emit : ∀ l : List JoinItem, (∀ q ∈ l, q.2.1 = true) →
      extractMatched out_v (l ++ rest) =
        (l.map fun q => (Nat.bits q.2.2.1, out_v)) ++ extractMatched out_v rest := by
    intro l hl
    induction l with
    | nil => simp
    | cons a t iht =>
      have ha := hl a (List.mem_cons_self ..)
      simp only [List.cons_append, extractMatched, ha, ↓reduceIte, List.map_cons]
      rw [iht fun q hq => hl q (List.mem_cons_of_mem _ hq)]
  rw [extractMatched]
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact hQ_emit Q hQ

private theorem extractMatched_buckets_flatMap (c : Bool) (buckets : List (List JoinItem))
    (hb : ∀ b ∈ buckets, b = [] ∨ ∃ key out_v Q, (∀ q ∈ Q, q.2.1 = true) ∧
      b = (key, (false, (0, out_v))) :: Q) :
    ∃ _c' : Bool, extractMatched c (buckets.flatMap id) =
      buckets.flatMap fun b => extractMatched false b := by
  induction buckets generalizing c with
  | nil => exact ⟨c, rfl⟩
  | cons b rest ih =>
    have hb0 := hb b (List.mem_cons_self ..)
    have hrest := fun b' hb' => hb b' (List.mem_cons_of_mem _ hb')
    rcases hb0 with rfl | ⟨key, out_v, Q, hQ, rfl⟩
    · obtain ⟨c', ihc⟩ := ih c hrest
      exact ⟨c', by simpa [extractMatched] using ihc⟩
    · obtain ⟨c', ihc⟩ := ih out_v hrest
      refine ⟨c', ?_⟩
      rw [List.flatMap_cons, id_eq, List.cons_append,
        extractMatched_bucket_append c key out_v Q hQ _, ihc, List.flatMap_cons]
      congr 1
      have hself := extractMatched_bucket_append false key out_v Q hQ []
      simpa [extractMatched] using hself.symm

private theorem truthTableList_eq_pipeline (x : SymAndInstance) (out : ℕ → Bool) :
    let g := yatesZeta x.n (countMasks x)
    let s := x.gates.length
    let joined := radixSortLSB (Nat.size s) (tabulateOut out s ++ queryEntries g)
    let extracted := extractMatched false joined
    let restored := radixSortLSB x.n extracted
    restored.map Prod.snd = x.truthTableList out := by
  dsimp only
  set g := yatesZeta x.n (countMasks x)
  set s := x.gates.length
  set joined := radixSortLSB (Nat.size s) (tabulateOut out s ++ queryEntries g)
  set extracted := extractMatched false joined
  set restored := radixSortLSB x.n extracted
  have hg_len : g.length = 2 ^ x.n := by
    dsimp only [g]
    rw [yatesZeta_countMasks_eq, List.length_map, List.length_range]
  have hg_le : ∀ v ∈ g, v ≤ s := fun v hv => yatesZeta_mem_le x hv
  have hjoined_buckets :
      joined = ((List.range (2 ^ Nat.size s)).map fun v =>
        (tabulateOut out s ++ queryEntries g).filter
          (fun p => evalBits (Nat.size s) p.1 == v)).flatMap id := by
    dsimp only [joined]
    rw [radixSortLSB_eq, List.flatMap_map]
    rfl
  have hbucket_shape : ∀ v ∈ List.range (2 ^ Nat.size s),
      let B := (tabulateOut out s ++ queryEntries g).filter
        (fun p => evalBits (Nat.size s) p.1 == v)
      if hv : v ≤ s then
        B = (Nat.bits v, (false, (0, out v))) ::
          ((List.range g.length).filter (fun j => g[j]?.getD 0 == v)).map
            (fun j => (Nat.bits v, (true, (j, false))))
      else B = [] := by
    intro v hv
    dsimp only
    rw [List.filter_append]
    have htab_filter : (tabulateOut out s).filter (fun p => evalBits (Nat.size s) p.1 == v) =
        if v ≤ s then [(Nat.bits v, (false, (0, out v)))] else [] := by
      rw [tabulateOut_eq, List.filter_map, List.filter_reverse, List.map_reverse]
      have hsplit : (List.range (s + 1)).filter
          (fun j => evalBits (Nat.size s) (Nat.bits j) == v) =
          if v ≤ s then [v] else [] := by
        have hcongr : (List.range (s + 1)).filter
            (fun j => evalBits (Nat.size s) (Nat.bits j) == v) =
            (List.range (s + 1)).filter (fun j => j == v) := by
          refine List.filter_congr fun j hj => ?_
          have hj_le : j ≤ s := by have := List.mem_range.1 hj; omega
          rw [evalBits_bits_of_le hj_le]
        rw [hcongr]
        by_cases hvs : v ≤ s
        · simp only [hvs, ↓reduceIte]
          have h1 : s + 1 = v + (1 + (s - v)) := by omega
          conv_lhs => rw [h1, List.range_add]
          rw [List.filter_append, List.range_add, List.map_append, List.filter_append]
          have hlt : (List.range v).filter (fun j => j == v) = [] :=
            List.filter_eq_nil_iff.2 fun j hj => by
              have := List.mem_range.1 hj; simp; omega
          have hgt : ((List.range (s - v)).map (1 + ·) |>.map (v + ·)).filter
              (fun j => j == v) = [] := by
            refine List.filter_eq_nil_iff.2 fun j hj => ?_
            rw [List.mem_map] at hj; obtain ⟨t, ht, rfl⟩ := hj
            rw [List.mem_map] at ht; obtain ⟨u, _, rfl⟩ := ht
            simp only [beq_iff_eq]; omega
          rw [hlt, hgt]
          simp
        · simp only [hvs, ↓reduceIte]
          exact List.filter_eq_nil_iff.2 fun j hj => by
            have := List.mem_range.1 hj; simp; omega
      change (List.map (fun j => (Nat.bits j, false, 0, out j))
        ((List.range (s + 1)).filter fun j =>
          evalBits (Nat.size s) (Nat.bits j) == v)).reverse = _
      rw [hsplit]
      by_cases hvs : v ≤ s
      · simp [hvs]
      · simp [hvs]
    have hq_filter := queryEntriesFrom_filter_eq 0 s g hg_le v
    by_cases hvs : v ≤ s
    · rw [dite_eq_left hvs, htab_filter]
      simp only [hvs, ↓reduceIte, List.singleton_append, hq_filter, queryEntries, Nat.zero_add]
    · rw [dite_eq_right hvs, htab_filter]
      simp only [hvs, ↓reduceIte, List.nil_append]
      have hq_nil : (List.range g.length).filter (fun j => g[j]?.getD 0 == v) = [] := by
        refine List.filter_eq_nil_iff.2 fun j hj => ?_
        have hj_lt : j < g.length := List.mem_range.1 hj
        have hj_mem : g[j] ∈ g := List.getElem_mem hj_lt
        have hj_le := hg_le _ hj_mem
        simp [List.getElem?_eq_getElem hj_lt]
        omega
      rw [queryEntries, hq_filter, hq_nil]
      rfl
  have hextract_eq : extracted =
      ((List.range (2 ^ Nat.size s)).map fun v =>
        if hv : v ≤ s then
          ((List.range g.length).filter (fun j => g[j]?.getD 0 == v)).map
            fun j => (Nat.bits j, out v)
        else []).flatMap id := by
    have hb_hyp : ∀ b ∈ (List.range (2 ^ Nat.size s)).map (fun v =>
        (tabulateOut out s ++ queryEntries g).filter
          (fun p => evalBits (Nat.size s) p.1 == v)),
        b = [] ∨ ∃ key out_v Q, (∀ q ∈ Q, q.2.1 = true) ∧
          b = (key, (false, (0, out_v))) :: Q := by
      intro b hb
      rw [List.mem_map] at hb
      obtain ⟨v, hv, rfl⟩ := hb
      have hs := hbucket_shape v hv
      by_cases hvs : v ≤ s
      · rw [dite_eq_left hvs] at hs
        right
        refine ⟨Nat.bits v, out v, _, fun q hq => ?_, hs⟩
        rw [List.mem_map] at hq
        obtain ⟨j, _, rfl⟩ := hq
        rfl
      · rw [dite_eq_right hvs] at hs
        exact Or.inl hs
    obtain ⟨_, heq⟩ := extractMatched_buckets_flatMap false _ hb_hyp
    dsimp only [extracted]
    rw [hjoined_buckets, heq, List.flatMap_map, List.flatMap_map]
    simp only [id_eq]
    have hmap_ext : ∀ l : List ℕ, (∀ v ∈ l, v ∈ List.range (2 ^ Nat.size s)) →
        l.flatMap (fun v => extractMatched false ((tabulateOut out s ++ queryEntries g).filter
          (fun p => evalBits (Nat.size s) p.1 == v))) =
        l.flatMap (fun v => if hv : v ≤ s then
          ((List.range g.length).filter (fun j => g[j]?.getD 0 == v)).map
            fun j => (Nat.bits j, out v)
          else []) := by
      intro l hl
      induction l with
      | nil => rfl
      | cons v vs ih =>
        rw [List.flatMap_cons, List.flatMap_cons, ih fun u hu => hl u (List.mem_cons_of_mem _ hu)]
        congr 1
        have hs := hbucket_shape v (hl v (List.mem_cons_self ..))
        by_cases hvs : v ≤ s
        · rw [dite_eq_left hvs] at hs ⊢
          rw [hs]
          have hba := extractMatched_bucket_append false (Nat.bits v) (out v)
            (((List.range g.length).filter (fun j => g[j]?.getD 0 == v)).map
              fun j => (Nat.bits v, (true, (j, false))))
            (fun q hq => by
              rw [List.mem_map] at hq; obtain ⟨j, _, rfl⟩ := hq; rfl) []
          rw [extractMatched]
          simp only [Bool.false_eq_true, ↓reduceIte]
          simp only [extractMatched, List.append_nil, List.map_map] at hba
          exact hba
        · rw [dite_eq_right hvs] at hs ⊢
          rw [hs]
          rfl
    exact hmap_ext _ fun _ hv => hv
  have hrestored_eq : restored = (List.range (2 ^ x.n)).map fun k => (Nat.bits k, out g[k]!) := by
    dsimp only [restored]
    rw [radixSortLSB_eq]
    have heq_map : (List.range (2 ^ x.n)).flatMap
        (fun k => extracted.filter fun r => evalBits x.n r.1 == k) =
        (List.range (2 ^ x.n)).map fun k => (Nat.bits k, out g[k]!) := by
      have hflat : ∀ k < 2 ^ x.n,
          extracted.filter (fun r => evalBits x.n r.1 == k) = [(Nat.bits k, out g[k]!)] := by
        intro k hk
        rw [hextract_eq, List.filter_flatMap]
        have hk_lt_g : k < g.length := by omega
        set vk := g[k]
        have hvk_le : vk ≤ s := hg_le vk (List.getElem_mem hk_lt_g)
        have hvk_lt : vk < 2 ^ Nat.size s := Nat.size_le.1 (Nat.size_le_size hvk_le)
        have hr_split : List.range (2 ^ Nat.size s) =
            List.range vk ++
              ([vk] ++ (List.range (2 ^ Nat.size s - vk - 1)).map (· + (vk + 1))) := by
          have h1 : 2 ^ Nat.size s = vk + (1 + (2 ^ Nat.size s - vk - 1)) := by omega
          conv_lhs => rw [h1, List.range_add]
          congr 1
          rw [List.range_add, List.map_append, List.map_map]
          simp only [List.range_one, List.map_singleton, Nat.add_zero, List.singleton_append]
          congr 2
          funext a
          dsimp
          omega
        have hother_nil : ∀ v ∈ List.range (2 ^ Nat.size s), v ≠ vk →
            (if hv : v ≤ s then
              ((List.range g.length).filter (fun j => g[j]?.getD 0 == v)).map
                fun j => (Nat.bits j, out v)
            else []).filter (fun r => evalBits x.n r.1 == k) = [] := by
          intro v hv hne
          by_cases hvs : v ≤ s
          · rw [dite_eq_left hvs, List.filter_map]
            refine List.map_eq_nil_iff.2 (List.filter_eq_nil_iff.2 fun j hj => ?_)
            rw [List.mem_filter] at hj
            have hj_lt : j < g.length := List.mem_range.1 hj.1
            have hgj : g[j] = v := by simpa [List.getElem?_eq_getElem hj_lt] using hj.2
            have hev_j : evalBits x.n (Nat.bits j) = j := evalBits_bits x.n j (by omega)
            simp only [Function.comp_apply, hev_j, beq_iff_eq]
            intro hjk
            subst hjk
            exact hne hgj.symm
          · rw [dite_eq_right hvs]; simp
        have hvk_eq : (if hv : vk ≤ s then
              ((List.range g.length).filter (fun j => g[j]?.getD 0 == vk)).map
                fun j => (Nat.bits j, out vk)
            else []).filter (fun r => evalBits x.n r.1 == k) = [(Nat.bits k, out g[k]!)] := by
          rw [dite_eq_left hvk_le, List.filter_map, List.filter_filter]
          have hf_eq : (List.range g.length).filter
              (fun j => (g[j]?.getD 0 == vk) && (evalBits x.n (Nat.bits j) == k)) = [k] := by
            have hr_k : List.range g.length =
                List.range k ++ ([k] ++ (List.range (g.length - k - 1)).map (· + (k + 1))) := by
              have h1 : g.length = k + (1 + (g.length - k - 1)) := by omega
              conv_lhs => rw [h1, List.range_add]
              congr 1
              rw [List.range_add, List.map_append, List.map_map]
              simp only [List.range_one, List.map_singleton, Nat.add_zero, List.singleton_append]
              congr 2
              funext a
              dsimp
              omega
            rw [hr_k, List.filter_append, List.filter_append]
            have hlt : (List.range k).filter
                (fun j => (g[j]?.getD 0 == vk) && (evalBits x.n (Nat.bits j) == k)) = [] :=
              List.filter_eq_nil_iff.2 fun j hj => by
                have hj_lt : j < k := List.mem_range.1 hj
                have hev_j : evalBits x.n (Nat.bits j) = j := evalBits_bits x.n j (by omega)
                simp only [hev_j, Bool.and_eq_true, beq_iff_eq, not_and]
                exact fun _ => by omega
            have hgt : ((List.range (g.length - k - 1)).map (· + (k + 1))).filter
                (fun j => (g[j]?.getD 0 == vk) && (evalBits x.n (Nat.bits j) == k)) = [] :=
              List.filter_eq_nil_iff.2 fun j hj => by
                rw [List.mem_map] at hj
                obtain ⟨t, ht, rfl⟩ := hj
                have ht_lt : t < g.length - k - 1 := List.mem_range.1 ht
                have hev_j : evalBits x.n (Nat.bits (t + (k + 1))) = t + (k + 1) :=
                  evalBits_bits x.n _ (by omega)
                simp only [hev_j, Bool.and_eq_true, beq_iff_eq, not_and]
                exact fun _ => by omega
            have hev_k : evalBits x.n (Nat.bits k) = k := evalBits_bits x.n k hk
            simp [hlt, hgt, hev_k, List.getElem?_eq_getElem hk_lt_g, vk]
          have hfilt_congr : (List.range g.length).filter
              (fun a => ((fun r => evalBits x.n r.1 == k) ∘
                  fun j => (Nat.bits j, out vk)) a && (g[a]?.getD 0 == vk)) =
              (List.range g.length).filter
                (fun j => (g[j]?.getD 0 == vk) && (evalBits x.n (Nat.bits j) == k)) :=
            List.filter_congr fun j _ => Bool.and_comm _ _
          rw [hfilt_congr, hf_eq, List.map_singleton]
          simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hk_lt_g, vk]
        rw [hr_split, List.map_append, List.map_append, List.map_cons, List.map_nil,
          List.flatMap_append, List.flatMap_append, List.flatMap_cons, List.flatMap_nil]
        simp only [id_eq]
        have hl1 : ((List.range vk).map fun v => if hv : v ≤ s then
              ((List.range g.length).filter (fun j => g[j]?.getD 0 == v)).map
                fun j => (Nat.bits j, out v)
            else []).flatMap (fun a => a.filter fun r => evalBits x.n r.1 == k) = [] := by
          refine List.flatMap_eq_nil_iff.2 fun b hb => ?_
          rw [List.mem_map] at hb; obtain ⟨v, hv, rfl⟩ := hb
          exact hother_nil v (List.mem_range.2 ((List.mem_range.1 hv).trans hvk_lt)) (by
            have := List.mem_range.1 hv; omega)
        have hl2 : (((List.range (2 ^ Nat.size s - vk - 1)).map (· + (vk + 1))).map fun v =>
            if hv : v ≤ s then
              ((List.range g.length).filter (fun j => g[j]?.getD 0 == v)).map
                fun j => (Nat.bits j, out v)
            else []).flatMap (fun a => a.filter fun r => evalBits x.n r.1 == k) = [] := by
          refine List.flatMap_eq_nil_iff.2 fun b hb => ?_
          rw [List.mem_map] at hb; obtain ⟨v, hv, rfl⟩ := hb
          rw [List.mem_map] at hv; obtain ⟨t, ht, rfl⟩ := hv
          have ht_lt := List.mem_range.1 ht
          exact hother_nil (t + (vk + 1)) (List.mem_range.2 (by omega)) (by omega)
        rw [hl1, hl2, List.nil_append, List.append_nil, List.append_nil]
        exact hvk_eq
      have hmap_gen : ∀ l : List ℕ, (∀ k ∈ l, k < 2 ^ x.n) →
          l.flatMap (fun k => extracted.filter fun r => evalBits x.n r.1 == k) =
            l.map fun k => (Nat.bits k, out g[k]!) := by
        intro l hl
        induction l with
        | nil => rfl
        | cons k ks ih =>
          rw [List.flatMap_cons, hflat k (hl k (List.mem_cons_self ..)), List.singleton_append,
            List.map_cons, ih fun m hm => hl m (List.mem_cons_of_mem _ hm)]
      exact hmap_gen _ (fun k hk => List.mem_range.1 hk)
    exact heq_map
  rw [hrestored_eq, List.map_map]
  refine List.ext_getElem (by simp [SymAndInstance.truthTableList]) fun k hk1 hk2 => ?_
  have hk : k < 2 ^ x.n := by simpa only [List.length_map, List.length_range] using hk1
  have hk_lt_g : k < g.length := by omega
  simp only [Function.comp_apply, List.getElem_map, List.getElem_range,
    SymAndInstance.truthTableList, List.getElem_ofFn, SymAnd.eval, SymAndInstance.toSymAnd]
  congr 1
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hk_lt_g, Option.getD_some]
  have hcnt := count_eq_subsetZeta_filter (x.toSymAnd out) ((BitString.equivFin x.n).symm ⟨k, hk⟩)
  dsimp only [SymAndInstance.toSymAnd] at hcnt
  rw [hcnt]
  have hg_k : g[k]'hk_lt_g =
      (x.gates.map (gateSet x.n)).countP fun S => decide (S ⊆ maskSet x.n k) := by
    rw [← Option.some_inj, ← List.getElem?_eq_getElem hk_lt_g]
    dsimp only [g]
    rw [yatesZeta_countMasks_eq, List.getElem?_map, List.getElem?_range]
    all_goals simp [hk]
  rw [hg_k]
  have hmask_eq : Finset.univ.filter (fun i : Fin x.n =>
      ((BitString.equivFin x.n).symm ⟨k, hk⟩) i = true) = maskSet x.n k := by
    ext i
    simp [BitString.equivFin_symm_apply, mem_maskSet]
  rw [hmask_eq]
  have hg : ({ gates := ↑(x.gates.map (gateSet x.n)), out := out } :
      SymAnd (Fin x.n)).gateMultiplicity = fun T => (x.gates.map (gateSet x.n)).count T := by
    funext T; simp [gateMultiplicity]
  rw [hg]
  exact (subsetZeta_listCount_eq_countP _ _).symm

private theorem computableInO_gates_len :
    ∃ c, ComputableInO (fun x : SymAndInstance => x.gates.length) encSymAndInstance encNat
      (fun x => ((encSymAndInstance x).length + 1) ^ c)
      (fun x => ((encSymAndInstance x).length + 1) ^ c) := by
  have hlen_u : ComputableInPolyTime (fun x : SymAndInstance => x.gates.length)
      encSymAndInstance encUnary := by fun_prop
  obtain ⟨d, _, hdeg⟩ := hlen_u.exists_degree
  have hcomp := ComputableInO.unaryToNat.comp hdeg.inO
  refine ⟨max d 1, hcomp.mono 2 (fun x => ?_) (fun x => ?_)⟩ <;>
  · have hle : x.gates.length ≤ ((encSymAndInstance x).length + 1) ^ max d 1 :=
      (gates_length_le_encSymAndInstance x).trans
        ((Nat.le_succ _).trans (Nat.le_self_pow (by omega) _))
    have hd : ((encSymAndInstance x).length + 1) ^ d ≤
        ((encSymAndInstance x).length + 1) ^ max d 1 :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_left _ _)
    omega

private theorem computableInO_tabulateOut {out : ℕ → Bool} {T S : ℕ → ℕ}
    (hT_mono : Monotone T) (hS_mono : Monotone S)
    (hout : ComputableInO out encNat encBool T S) :
    ∃ c, ComputableInO (fun x : SymAndInstance => tabulateOut out x.gates.length)
      encSymAndInstance (encList encJoinItem)
      (fun x => ((encSymAndInstance x).length + 1) ^ c * (T x.gates.length + 1))
      (fun x => ((encSymAndInstance x).length + 1) ^ c * (S x.gates.length + 1)) := by
  let encTab := encPair encNat (encList encJoinItem)
  have hfst := ComputableInO.fst encNat (encList encJoinItem)
  have hsnd := ComputableInO.snd encNat (encList encJoinItem)
  have hbits : ComputableInO (fun p : ℕ × List JoinItem => Nat.bits p.1) encTab encBits
      (fun p => (encTab p).length) (fun p => (encTab p).length) :=
    hfst.of_enc_eq (fun _ => rfl)
  have hout_p : ComputableInO (fun p : ℕ × List JoinItem => out p.1) encTab encBool
      (fun p => (encTab p).length + T p.1) (fun p => (encTab p).length + S p.1) :=
    hout.comp hfst
  have hitem : ComputableInO (fun p : ℕ × List JoinItem => (Nat.bits p.1, (false, (0, out p.1))))
      encTab encJoinItem
      (fun p => (encTab p).length + T p.1) (fun p => (encTab p).length + S p.1) := by
    have h0 := (ComputableInO.constZero (encIn := encTab) (encMid := encNat) (0 : ℕ)).prod hout_p
    have hf := (ComputableInO.constZero (encIn := encTab) (encMid := encBool) false).prod h0
    exact (hbits.prod hf).mono 6 (fun p => by omega) (fun p => by omega)
  have hcons : ComputableInO
      (fun p : ℕ × List JoinItem => (Nat.bits p.1, (false, (0, out p.1))) :: p.2)
      encTab (encList encJoinItem)
      (fun p => (encTab p).length + T p.1) (fun p => (encTab p).length + S p.1) := by
    have hc := (ComputableInO.of_linear (ComputableInDegree.cons encJoinItem)).comp_linear
      (hitem.prod hsnd)
    exact hc.mono 2
      (fun p => by dsimp only [encTab]; omega) (fun p => by dsimp only [encTab]; omega)
  have hstep : ComputableInO (tabulateStep out) encTab encTab
      (fun p => (encTab p).length + ((encNat p.1).length + 1) ^ 2 + T p.1)
      (fun p => (encTab p).length + (encNat p.1).length + S p.1 + 1) := by
    have hj1 := ComputableInO.natSucc.comp hfst
    exact (hj1.prod hcons).mono 2
      (fun p => by dsimp only [encTab]; omega) (fun p => by dsimp only [encTab]; omega)
  obtain ⟨c_s, hs_nat⟩ := computableInO_gates_len
  have hstep_enc_le : ∀ x : SymAndInstance, ∀ k ≤ x.gates.length,
      (encTab ((tabulateStep out)^[k] (0, []))).length ≤
        57 * ((encSymAndInstance x).length + 1) ^ 2 := fun x k hk => by
    obtain ⟨hf, hl⟩ := tabulateStep_iter out k
    have hk_A : k ≤ (encSymAndInstance x).length := hk.trans (gates_length_le_encSymAndInstance x)
    have hkn : (encNat k).length ≤ (encSymAndInstance x).length := by
      have h1 : (encNat k).length ≤ k := by
        rw [encNat_apply, Nat.size_eq_bits_len]; exact Nat.size_le_self k
      omega
    have hacc_aux : ∀ l : List ℕ, (∀ m ∈ l, m ≤ k) →
        (encList encJoinItem (l.map fun m => (Nat.bits m, (false, (0, out m))))).length ≤
          l.length * (4 * (encSymAndInstance x).length + 50) := by
      intro l hm_le
      induction l with
      | nil => simp
      | cons a t iht =>
        have ha := hm_le a (List.mem_cons_self ..)
        have ht := iht fun b hb => hm_le b (List.mem_cons_of_mem _ hb)
        have han : (encNat a).length ≤ (encSymAndInstance x).length :=
          (length_encNat_mono ha).trans hkn
        have hej := length_encJoinItem_le (Nat.bits a) false 0 (out a)
        have h0 : (encNat 0).length = 0 := by simp [encNat_apply]
        have hba : (Nat.bits a).length = (encNat a).length := rfl
        rw [List.map_cons, encList_cons, List.length_append, List.length_cons, length_frame]
        nlinarith
    have hacc := hacc_aux (List.range k).reverse (fun m hm => by
      rw [List.mem_reverse, List.mem_range] at hm; omega)
    have hlen_r : (List.range k).reverse.length = k := by simp
    rw [hlen_r] at hacc
    have hpow : k * (4 * (encSymAndInstance x).length + 50) ≤
        54 * ((encSymAndInstance x).length + 1) ^ 2 := by
      have h1 : k ≤ (encSymAndInstance x).length + 1 := by omega
      have h2 : 4 * (encSymAndInstance x).length + 50 ≤
          54 * ((encSymAndInstance x).length + 1) := by
        omega
      calc k * (4 * (encSymAndInstance x).length + 50)
          ≤ ((encSymAndInstance x).length + 1) * (54 * ((encSymAndInstance x).length + 1)) :=
            Nat.mul_le_mul h1 h2
        _ = 54 * ((encSymAndInstance x).length + 1) ^ 2 := by ring
    change (encPair encNat (encList encJoinItem) ((tabulateStep out)^[k] (0, []))).length ≤ _
    rw [length_encPair, hf, hl]
    calc 2 * (encNat k).length + 1 + _
        ≤ 2 * (encSymAndInstance x).length + 1 + 54 * ((encSymAndInstance x).length + 1) ^ 2 := by
          omega
      _ ≤ 57 * ((encSymAndInstance x).length + 1) ^ 2 := by
          have : 1 ≤ ((encSymAndInstance x).length + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
          nlinarith
  have hit := ComputableInO.iterate hs_nat
    (ComputableInO.const (encIn := encSymAndInstance) (encMid := encTab)
      ((0 : ℕ), ([] : List JoinItem)))
    hstep
    (R := fun x => 61 * ((encSymAndInstance x).length + 1) ^ 2 + T x.gates.length)
    (Q := fun x => 58 * ((encSymAndInstance x).length + 1) ^ 2 + S x.gates.length + 1)
    (B := fun x => 57 * ((encSymAndInstance x).length + 1) ^ 2)
    (fun x k hk => by
      have h1 := hstep_enc_le x k hk
      have hf := (tabulateStep_iter out k).1
      have hk_le : (encNat k).length + 1 ≤ 2 * ((encSymAndInstance x).length + 1) := by
        have : (encNat k).length ≤ k := by
          rw [encNat_apply, Nat.size_eq_bits_len]; exact Nat.size_le_self k
        have := gates_length_le_encSymAndInstance x
        omega
      have hsq : ((encNat k).length + 1) ^ 2 ≤ 4 * ((encSymAndInstance x).length + 1) ^ 2 := by
        calc ((encNat k).length + 1) ^ 2 ≤ (2 * ((encSymAndInstance x).length + 1)) ^ 2 :=
              Nat.pow_le_pow_left hk_le 2
          _ = 4 * ((encSymAndInstance x).length + 1) ^ 2 := by ring
      have hTm := hT_mono hk
      rw [hf]
      omega)
    (fun x k hk => by
      have h1 := hstep_enc_le x k hk
      have hf := (tabulateStep_iter out k).1
      have hk_le : (encNat k).length ≤ (encSymAndInstance x).length + 1 := by
        have : (encNat k).length ≤ k := by
          rw [encNat_apply, Nat.size_eq_bits_len]; exact Nat.size_le_self k
        have := gates_length_le_encSymAndInstance x
        omega
      have h1_sq : (encSymAndInstance x).length + 1 ≤ ((encSymAndInstance x).length + 1) ^ 2 := by
        nlinarith
      have hSm := hS_mono hk
      rw [hf]
      omega)
    (fun x k hk => hstep_enc_le x k hk)
  have htab := hcons.comp hit
  have heq_fn : (fun p : ℕ × List JoinItem =>
        (Nat.bits p.1, (false, (0, out p.1))) :: p.2) ∘
      (fun x : SymAndInstance => (tabulateStep out)^[x.gates.length] (0, [])) =
      fun x : SymAndInstance => tabulateOut out x.gates.length := by
    funext x
    simp only [Function.comp_apply, tabulateOut, (tabulateStep_iter out x.gates.length).1]
  rw [heq_fn] at htab
  refine ⟨max c_s 3, htab.mono 256 (fun x => ?_) (fun x => ?_)⟩
  · set A := (encSymAndInstance x).length + 1
    set C := max c_s 3
    have hf := (tabulateStep_iter out x.gates.length).1
    have h_enc := hstep_enc_le x x.gates.length le_rfl
    have hg := gates_length_le_encSymAndInstance x
    have hn_s : (encNat x.gates.length).length + 1 ≤ A := by
      have : (encNat x.gates.length).length ≤ x.gates.length := by
        rw [encNat_apply, Nat.size_eq_bits_len]; exact Nat.size_le_self _
      omega
    have hsq : ((encNat x.gates.length).length + 1) ^ 2 ≤ A ^ 2 := Nat.pow_le_pow_left hn_s 2
    have hA_c : A ^ c_s ≤ A ^ C := Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_left _ _)
    have hA_3 : A ^ 3 ≤ A ^ C := Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_right _ _)
    have hA_2 : A ^ 2 ≤ A ^ C := Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
    have hA_1 : A ≤ A ^ C := Nat.le_self_pow (by omega) A
    have h3 : (x.gates.length + 1) * (122 * A ^ 2 + T x.gates.length) ≤
        122 * A ^ C * (T x.gates.length + 1) := by
      calc (x.gates.length + 1) * (122 * A ^ 2 + T x.gates.length)
          ≤ A * (122 * A ^ 2 * (T x.gates.length + 1)) := by
            refine Nat.mul_le_mul (by omega) ?_
            have : 1 ≤ A ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos _)
            nlinarith
        _ = 122 * A ^ 3 * (T x.gates.length + 1) := by ring
        _ ≤ 122 * A ^ C * (T x.gates.length + 1) := by
            exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 122 hA_3)
    have h3_raw : (x.gates.length + 1) *
          (61 * A ^ 2 + T x.gates.length + 57 * A ^ 2 + ((encNat x.gates.length).length + 1) ^ 2) ≤
        122 * A ^ C * (T x.gates.length + 1) :=
      (Nat.mul_le_mul_left _ (by omega)).trans h3
    rw [hf]
    have h_T : A ^ C ≤ A ^ C * (T x.gates.length + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    have hT_le : T x.gates.length ≤ A ^ C * (T x.gates.length + 1) :=
      (Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ (Nat.one_le_pow _ _ (Nat.succ_pos _)))
    have h_enc_C : (encTab ((tabulateStep out)^[x.gates.length] (0, []))).length ≤ 57 * A ^ C :=
      h_enc.trans (Nat.mul_le_mul_left 57 hA_2)
    have hx_A : (encSymAndInstance x).length ≤ A ^ C := (Nat.le_succ _).trans hA_1
    have h57 : 57 * A ^ C ≤ 57 * (A ^ C * (T x.gates.length + 1)) :=
      Nat.mul_le_mul_left 57 h_T
    linarith only [hA_c, hx_A, h3_raw, h_enc_C, h57, h_T, hT_le]
  · set A := (encSymAndInstance x).length + 1
    set C := max c_s 3
    have hf := (tabulateStep_iter out x.gates.length).1
    have h_enc := hstep_enc_le x x.gates.length le_rfl
    have hg := gates_length_le_encSymAndInstance x
    have hn_s : (encNat x.gates.length).length ≤ A := by
      have : (encNat x.gates.length).length ≤ x.gates.length := by
        rw [encNat_apply, Nat.size_eq_bits_len]; exact Nat.size_le_self _
      omega
    have hA_c : A ^ c_s ≤ A ^ C := Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_left _ _)
    have hA_2 : A ^ 2 ≤ A ^ C := Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
    have hA_1 : A ≤ A ^ C := Nat.le_self_pow (by omega) A
    rw [hf]
    have h_S : A ^ C ≤ A ^ C * (S x.gates.length + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    have h_S2 : S x.gates.length ≤ A ^ C * (S x.gates.length + 1) :=
      (by omega : S x.gates.length ≤ S x.gates.length + 1).trans
        (Nat.le_mul_of_pos_left _ (Nat.one_le_pow _ _ (Nat.succ_pos _)))
    have h58 : 58 * A ^ 2 ≤ 58 * (A ^ C * (S x.gates.length + 1)) :=
      (Nat.mul_le_mul_left 58 hA_2).trans (Nat.mul_le_mul_left 58 h_S)
    have h57 : 57 * A ^ 2 ≤ 57 * (A ^ C * (S x.gates.length + 1)) :=
      (Nat.mul_le_mul_left 57 hA_2).trans (Nat.mul_le_mul_left 57 h_S)
    have h_enc_C : (encTab ((tabulateStep out)^[x.gates.length] (0, []))).length ≤
        57 * (A ^ C * (S x.gates.length + 1)) :=
      h_enc.trans ((Nat.mul_le_mul_left 57 hA_2).trans (Nat.mul_le_mul_left 57 h_S))
    have hx_C : (encSymAndInstance x).length ≤ A ^ C * (S x.gates.length + 1) :=
      ((Nat.le_succ _).trans hA_1).trans h_S
    have hn_C : (encNat x.gates.length).length ≤ A ^ C * (S x.gates.length + 1) :=
      (hn_s.trans hA_1).trans h_S
    have h1_pos : 1 ≤ A ^ C := Nat.one_le_pow _ _ (Nat.succ_pos _)
    linarith only [hA_c, hx_C, h58, h57, hn_C, h_enc_C, h_S, h_S2, h1_pos]

private theorem computableInO_queryEntries :
    ∃ c, ComputableInO (fun x : SymAndInstance => queryEntries (yatesZeta x.n (countMasks x)))
      encSymAndInstance (encList encJoinItem)
      (fun x => (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ c) * (x.n + 1) ^ c)
      (fun x => (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ c) * (x.n + 1) ^ c) := by
  have hnext : ComputableInPolyTime (fun q : ℕ × ℕ => q.1 + 1) (encPair encNat encNat) encNat :=
    ComputableInPolyTime.binary_add' (fst encNat encNat) (const 1)
  have hemit : ComputableInPolyTime (fun q : ℕ × ℕ => [(Nat.bits q.2, (true, (q.1, false)))])
      (encPair encNat encNat) (encList encJoinItem) := by
    have h1 : ComputableInPolyTime (fun q : ℕ × ℕ => (Nat.bits q.2, (true, (q.1, false))))
        (encPair encNat encNat) encJoinItem := by
      have hbits : ComputableInPolyTime (fun q : ℕ × ℕ => Nat.bits q.2)
          (encPair encNat encNat) encBits :=
        ComputableInPolyTime.natBits.comp (snd encNat encNat)
      exact hbits.prod ((const true).prod ((fst encNat encNat).prod (const false)))
    exact h1.cons' (const [])
  obtain ⟨c_f, d_f, hfold⟩ := ComputableInTimeAndSpace.streamFold_pair_list
    (encA := encNat) (encS := encNat) (encB := encJoinItem)
    (encIn := encPair encNat (encList encNat))
    (init := Prod.fst) (elems := Prod.snd) (fun _ => rfl) hnext hemit
    (g := fun q : ℕ × List ℕ => queryEntriesFrom q.1 q.2)
    (fun q => queryEntriesFrom_streamEmit q.1 q.2)
    (lMax := fun q => Nat.log2 (q.1 + q.2.length + 1) +
      listMax (fun v => (encNat v).length) q.2 + 8)
    (fun q j hj => by
      have hst : streamState q.1 (fun p : ℕ × ℕ => p.1 + 1) q.2 j ≤ q.1 + q.2.length := by
        have htake : ∀ xs : List ℕ, ∀ s : ℕ,
            xs.foldl (fun a _ => a + 1) s = s + xs.length := by
          intro xs s
          induction xs generalizing s with
          | nil => simp
          | cons _ t ih => simp only [List.foldl_cons, ih, List.length_cons]; omega
        rw [streamState, htake, List.length_take]
        omega
      have hlen := length_encNat_le_log2 (hst.trans (Nat.le_add_right (q.1 + q.2.length) 1))
      change (encNat (streamState q.1 _ q.2 j)).length ≤ _
      omega)
    (fun q j hj => (le_listMax (f := fun v => (encNat v).length) (List.getElem_mem hj)).trans
      (by omega))
  have hfold_inO : ComputableInO (fun q : ℕ × List ℕ => queryEntriesFrom q.1 q.2)
      (encPair encNat (encList encNat)) (encList encJoinItem)
      (fun q => (encPair encNat (encList encNat) q).length +
        (q.2.length + 1) * (Nat.log2 (q.1 + q.2.length + 1) +
          listMax (fun v => (encNat v).length) q.2 + 9) ^ d_f + 1)
      (fun q => (Nat.log2 (q.1 + q.2.length + 1) +
        listMax (fun v => (encNat v).length) q.2 + 9) ^ d_f +
        (q.2.length + 1) * (Nat.log2 (q.1 + q.2.length + 1) +
          listMax (fun v => (encNat v).length) q.2 + 10) + 1) := by
    refine ComputableInO.of_bounds hfold (c_f + 10) (fun q => ?_) (fun q => ?_) (fun q => ?_)
    · rw [Nat.add_assoc (Nat.log2 (q.1 + q.2.length + 1) +
        listMax (fun v => (encNat v).length) q.2) 8 1]
      exact Nat.mul_le_mul (by omega) (by omega)
    · rw [Nat.add_assoc (Nat.log2 (q.1 + q.2.length + 1) +
        listMax (fun v => (encNat v).length) q.2) 8 1]
      exact Nat.mul_le_mul (by omega) (by omega)
    · have hm : ∀ p ∈ queryEntriesFrom q.1 q.2,
          (encJoinItem p).length ≤ 4 * (Nat.log2 (q.1 + q.2.length + 1) + 1) +
            2 * listMax (fun v => (encNat v).length) q.2 + 24 := fun p hp => by
        obtain ⟨_, hlt, _, j, hj, rfl⟩ := queryEntriesFrom_mem hp
        have hlen_j : (encNat (q.1 + j)).length ≤ Nat.log2 (q.1 + q.2.length + 1) + 1 :=
          length_encNat_le_log2 (by omega)
        have hlen_gj : (encNat q.2[j]).length ≤ listMax (fun v => (encNat v).length) q.2 :=
          le_listMax (f := fun v => (encNat v).length) (List.getElem_mem hj)
        have he := length_encJoinItem_le (Nat.bits q.2[j]) true (q.1 + j) false
        have hba : (Nat.bits q.2[j]).length = (encNat q.2[j]).length := rfl
        omega
      have hlen_q : (queryEntriesFrom q.1 q.2).length = q.2.length := by
        have hrec : ∀ k (l : List ℕ), (queryEntriesFrom k l).length = l.length := fun k l => by
          induction l generalizing k with
          | nil => rfl
          | cons _ _ ih => simp [queryEntriesFrom, ih]
        exact hrec q.1 q.2
      have h1 := (length_encList_le encJoinItem (queryEntriesFrom q.1 q.2)
        (b := 4 * (Nat.log2 (q.1 + q.2.length + 1) + 1) +
          2 * listMax (fun v => (encNat v).length) q.2 + 24)
        hm).trans (by rw [hlen_q])
      have h1' : (encList encJoinItem (queryEntriesFrom q.1 q.2)).length ≤
          q.2.length * (8 * (Nat.log2 (q.1 + q.2.length + 1) + 1) +
            4 * listMax (fun v => (encNat v).length) q.2 + 49) := by
        calc _ ≤ q.2.length * (2 * (4 * (Nat.log2 (q.1 + q.2.length + 1) + 1) +
                  2 * listMax (fun v => (encNat v).length) q.2 + 24) + 1) := h1
          _ = _ := by ring
      have hmul : q.2.length * (8 * (Nat.log2 (q.1 + q.2.length + 1) + 1) +
            4 * listMax (fun v => (encNat v).length) q.2 + 49) ≤
          8 * ((q.2.length + 1) * (Nat.log2 (q.1 + q.2.length + 1) +
            listMax (fun v => (encNat v).length) q.2 + 10)) := by
        calc _ ≤ (q.2.length + 1) * (8 * (Nat.log2 (q.1 + q.2.length + 1) +
                  listMax (fun v => (encNat v).length) q.2 + 10)) :=
                Nat.mul_le_mul (Nat.le_succ _) (by omega)
          _ = _ := by ring
      have hle_rhs : (q.2.length + 1) * (Nat.log2 (q.1 + q.2.length + 1) +
            listMax (fun v => (encNat v).length) q.2 + 10) ≤
          (Nat.log2 (q.1 + q.2.length + 1) + listMax (fun v => (encNat v).length) q.2 + 9) ^ d_f +
            (q.2.length + 1) * (Nat.log2 (q.1 + q.2.length + 1) +
              listMax (fun v => (encNat v).length) q.2 + 10) + 1 + 1 :=
        (Nat.le_add_left _ _).trans (Nat.le_add_right _ 2)
      exact (h1'.trans hmul).trans (Nat.mul_le_mul (by omega) hle_rhs)
  obtain ⟨c_y, hyates⟩ := computableInO_yatesZeta
  have hwrap : ComputableInO (fun x : SymAndInstance => (0, yatesZeta x.n (countMasks x)))
      encSymAndInstance (encPair encNat (encList encNat))
      (fun x => (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ (max c_y 1)) *
        (x.n + 1) ^ (max c_y 1))
      (fun x => (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ (max c_y 1)) *
        (x.n + 1) ^ (max c_y 1)) := by
    have hp := (ComputableInO.constZero (encIn := encSymAndInstance) (encMid := encNat) 0).prod
      hyates
    refine hp.mono 2 (fun x => ?_) (fun x => ?_) <;>
    · have h1 : (encSymAndInstance x).length ≤ ((encSymAndInstance x).length + 1) ^ max c_y 1 :=
        (Nat.le_succ _).trans (Nat.le_self_pow (by omega) _)
      have h2 : ((encSymAndInstance x).length + 1) ^ c_y ≤
          ((encSymAndInstance x).length + 1) ^ max c_y 1 :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_left _ _)
      have h3 : (x.n + 1) ^ c_y ≤ (x.n + 1) ^ max c_y 1 :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_left _ _)
      have hN1 : 1 ≤ (x.n + 1) ^ max c_y 1 := Nat.one_le_pow _ _ (Nat.succ_pos _)
      have h_le : (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ c_y) * (x.n + 1) ^ c_y ≤
          (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ max c_y 1) * (x.n + 1) ^ max c_y 1 :=
        Nat.mul_le_mul (Nat.add_le_add_left h2 _) h3
      have hx_le : (encSymAndInstance x).length ≤
          (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ max c_y 1) * (x.n + 1) ^ max c_y 1 :=
        (h1.trans (Nat.le_add_left _ _)).trans (Nat.le_mul_of_pos_right _ hN1)
      nlinarith
  obtain ⟨c_w, hwrap_len⟩ := hwrap.length_le
  have hcomp := hfold_inO.comp hwrap
  let D := max d_f 1
  let C_q := max c_y 1 + 2 * D + 4
  have hmain_q : ∀ x : SymAndInstance,
      ((yatesZeta x.n (countMasks x)).length + 1) *
          (Nat.log2 (0 + (yatesZeta x.n (countMasks x)).length + 1) +
            listMax (fun v => (encNat v).length) (yatesZeta x.n (countMasks x)) + 10) ^ D ≤
        66 ^ (D + 1) * ((2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_q) *
          (x.n + 1) ^ C_q) := fun x => by
    set A := (encSymAndInstance x).length + 1
    set N := x.n + 1
    have hg_len : (yatesZeta x.n (countMasks x)).length = 2 ^ x.n := by
      rw [yatesZeta_countMasks_eq, List.length_map, List.length_range]
    have hlog : Nat.log2 (0 + (yatesZeta x.n (countMasks x)).length + 1) ≤ x.n + 1 := by
      rw [hg_len, Nat.zero_add]
      have hlt : 2 ^ x.n + 1 < 2 ^ (x.n + 2) := by
        have h1 : 1 ≤ 2 ^ x.n := Nat.one_le_pow _ _ (by decide)
        rw [pow_add]; omega
      by_contra hgt
      push Not at hgt
      have hgt' : x.n + 2 ≤ Nat.log2 (2 ^ x.n + 1) := by omega
      have hle := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hgt'
      have hself := Nat.log2_self_le (by positivity : 2 ^ x.n + 1 ≠ 0)
      omega
    have hmax_g : listMax (fun v => (encNat v).length) (yatesZeta x.n (countMasks x)) ≤
        Nat.log2 A + 1 := by
      refine listMax_le fun v hv => ?_
      have h1 := yatesZeta_mem_le x hv
      have h2 := gates_length_le_encSymAndInstance x
      exact length_encNat_le_log2 (by omega)
    have hbase : Nat.log2 (0 + (yatesZeta x.n (countMasks x)).length + 1) +
          listMax (fun v => (encNat v).length) (yatesZeta x.n (countMasks x)) + 10 ≤
        11 * N * (Nat.log2 A + 2) := by
      have h1 : x.n ≤ x.n * (Nat.log2 A + 2) := Nat.le_mul_of_pos_right _ (by omega)
      have h2 : 11 * N * (Nat.log2 A + 2) =
          11 * (x.n * (Nat.log2 A + 2)) + 11 * (Nat.log2 A + 2) := by
        dsimp only [N]; ring
      omega
    have hpow_b : (Nat.log2 (0 + (yatesZeta x.n (countMasks x)).length + 1) +
          listMax (fun v => (encNat v).length) (yatesZeta x.n (countMasks x)) + 10) ^ D ≤
        11 ^ D * N ^ D * (Nat.log2 A + 2) ^ D := by
      calc _ ≤ (11 * N * (Nat.log2 A + 2)) ^ D := Nat.pow_le_pow_left hbase D
        _ = 11 ^ D * N ^ D * (Nat.log2 A + 2) ^ D := by rw [Nat.mul_pow, Nat.mul_pow]
    have hlogA := radix_log_absorb x.n A D (Nat.succ_pos _)
    have h2n_1 : (yatesZeta x.n (countMasks x)).length + 1 ≤ 2 ^ x.n + A := by
      rw [hg_len]; omega
    have hA_fin : A ^ (D + 1) ≤ A ^ C_q := Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
    have hN_fin : N ^ (2 * D) ≤ N ^ C_q := Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
    have hc66 : 11 ^ D * (2 * 3 ^ (D + 1) * 2 ^ D) ≤ 66 ^ (D + 1) := by
      have h1 : 11 ^ D * (2 * 3 ^ (D + 1) * 2 ^ D) = 6 * (11 ^ D * 3 ^ D * 2 ^ D) := by ring
      rw [← Nat.mul_pow, ← Nat.mul_pow, show 11 * 3 * 2 = 66 from rfl] at h1
      have h2 : 66 ^ (D + 1) = 66 * 66 ^ D := by ring
      omega
    calc ((yatesZeta x.n (countMasks x)).length + 1) *
            (Nat.log2 (0 + (yatesZeta x.n (countMasks x)).length + 1) +
              listMax (fun v => (encNat v).length) (yatesZeta x.n (countMasks x)) + 10) ^ D
        ≤ (2 ^ x.n + A) * (11 ^ D * N ^ D * (Nat.log2 A + 2) ^ D) :=
            Nat.mul_le_mul h2n_1 hpow_b
      _ = 11 ^ D * N ^ D * ((2 ^ x.n + A) * (Nat.log2 A + 2) ^ D) := by ring
      _ ≤ 11 ^ D * N ^ D *
            (2 * 3 ^ (D + 1) * 2 ^ D * (2 ^ x.n + A ^ (D + 1)) * N ^ D) :=
            Nat.mul_le_mul_left _ hlogA
      _ = (11 ^ D * (2 * 3 ^ (D + 1) * 2 ^ D)) * ((2 ^ x.n + A ^ (D + 1)) * N ^ (2 * D)) := by
            ring
      _ ≤ 66 ^ (D + 1) * ((2 ^ x.n + A ^ C_q) * N ^ C_q) :=
            Nat.mul_le_mul hc66 (Nat.mul_le_mul (Nat.add_le_add_left hA_fin _) hN_fin)
  have hq_common : ∀ x : SymAndInstance,
      (Nat.log2 (0 + (yatesZeta x.n (countMasks x)).length + 1) +
          listMax (fun v => (encNat v).length) (yatesZeta x.n (countMasks x)) + 9) ^ d_f ≤
        (Nat.log2 (0 + (yatesZeta x.n (countMasks x)).length + 1) +
          listMax (fun v => (encNat v).length) (yatesZeta x.n (countMasks x)) + 10) ^ D ∧
      (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ max c_y 1) * (x.n + 1) ^ max c_y 1 ≤
        (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_q) * (x.n + 1) ^ C_q ∧
      1 ≤ (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_q) * (x.n + 1) ^ C_q := fun x =>
    ⟨(Nat.pow_le_pow_left (by omega) d_f).trans
        (Nat.pow_le_pow_right (by omega) (le_max_left _ _)),
      Nat.mul_le_mul (Nat.add_le_add_left
        (Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)) _)
        (Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)),
      Nat.mul_pos (by have := Nat.one_le_pow x.n 2 (by decide); omega)
        (Nat.one_le_pow _ _ (Nat.succ_pos _))⟩
  refine ⟨C_q, hcomp.mono (2 * c_w + 4 * 66 ^ (D + 1) + 8) (fun x => ?_) (fun x => ?_)⟩
  · dsimp only [Function.comp_apply, queryEntries]
    set A := (encSymAndInstance x).length + 1
    set N := x.n + 1
    set B := (2 ^ x.n + A ^ C_q) * N ^ C_q
    have hlen_w := hwrap_len x
    have hmq : ((yatesZeta x.n (countMasks x)).length + 1) *
          (Nat.log2 (0 + (yatesZeta x.n (countMasks x)).length + 1) +
            listMax (fun v => (encNat v).length) (yatesZeta x.n (countMasks x)) + 10) ^ D ≤
        66 ^ (D + 1) * B := hmain_q x
    obtain ⟨hpow_df, hwrap_le, hbox_pos⟩ := hq_common x
    change (2 ^ x.n + A ^ max c_y 1) * N ^ max c_y 1 ≤ B at hwrap_le
    change 1 ≤ B at hbox_pos
    have hmul_df := Nat.mul_le_mul_left ((yatesZeta x.n (countMasks x)).length + 1) hpow_df
    have hlen_B : (encPair encNat (encList encNat) (0, yatesZeta x.n (countMasks x))).length ≤
        2 * c_w * B := by
      have hwrap_le' : (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ max c_y 1) *
            (x.n + 1) ^ max c_y 1 ≤ B := hwrap_le
      calc _ ≤ c_w * (B + 1) := hlen_w.trans (Nat.mul_le_mul_left _ (by omega))
        _ ≤ c_w * (2 * B) := Nat.mul_le_mul_left _ (by omega)
        _ = 2 * c_w * B := by ring
    have hq_le := hmul_df.trans hmq
    have h66 : 1 ≤ 66 ^ (D + 1) := Nat.one_le_pow _ _ (by decide)
    have h66B : 66 ^ (D + 1) * B ≤ 4 * (66 ^ (D + 1) * B) := by omega
    calc (2 ^ x.n + A ^ max c_y 1) * N ^ max c_y 1 +
          ((encPair encNat (encList encNat) (0, yatesZeta x.n (countMasks x))).length +
            ((yatesZeta x.n (countMasks x)).length + 1) *
              (Nat.log2 (0 + (yatesZeta x.n (countMasks x)).length + 1) +
                listMax (fun v => (encNat v).length) (yatesZeta x.n (countMasks x)) + 9) ^
                d_f + 1)
        ≤ B + (2 * c_w * B + 66 ^ (D + 1) * B + 1) := by linarith only [hwrap_le, hlen_B, hq_le]
      _ ≤ 2 * c_w * B + 4 * 66 ^ (D + 1) * B + 8 * B := by
          calc B + (2 * c_w * B + 66 ^ (D + 1) * B + 1)
              ≤ 2 * c_w * B + 4 * (66 ^ (D + 1) * B) + 8 * B := by omega
            _ = _ := by ring
      _ = (2 * c_w + 4 * 66 ^ (D + 1) + 8) * B := by ring
      _ ≤ (2 * c_w + 4 * 66 ^ (D + 1) + 8) * (B + 1) :=
          Nat.mul_le_mul_left _ (Nat.le_succ _)
  · dsimp only [Function.comp_apply, queryEntries]
    set A := (encSymAndInstance x).length + 1
    set N := x.n + 1
    set B := (2 ^ x.n + A ^ C_q) * N ^ C_q
    have hmq : ((yatesZeta x.n (countMasks x)).length + 1) *
          (Nat.log2 (0 + (yatesZeta x.n (countMasks x)).length + 1) +
            listMax (fun v => (encNat v).length) (yatesZeta x.n (countMasks x)) + 10) ^ D ≤
        66 ^ (D + 1) * B := hmain_q x
    obtain ⟨hpow_df, hwrap_le, hbox_pos⟩ := hq_common x
    change (2 ^ x.n + A ^ max c_y 1) * N ^ max c_y 1 ≤ B at hwrap_le
    change 1 ≤ B at hbox_pos
    have h1 : (Nat.log2 (0 + (yatesZeta x.n (countMasks x)).length + 1) +
          listMax (fun v => (encNat v).length) (yatesZeta x.n (countMasks x)) + 10) ^ D ≤
        ((yatesZeta x.n (countMasks x)).length + 1) *
          (Nat.log2 (0 + (yatesZeta x.n (countMasks x)).length + 1) +
            listMax (fun v => (encNat v).length) (yatesZeta x.n (countMasks x)) + 10) ^ D :=
      Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    have h2 : ((yatesZeta x.n (countMasks x)).length + 1) *
          (Nat.log2 (0 + (yatesZeta x.n (countMasks x)).length + 1) +
            listMax (fun v => (encNat v).length) (yatesZeta x.n (countMasks x)) + 10) ≤
        ((yatesZeta x.n (countMasks x)).length + 1) *
          (Nat.log2 (0 + (yatesZeta x.n (countMasks x)).length + 1) +
            listMax (fun v => (encNat v).length) (yatesZeta x.n (countMasks x)) + 10) ^ D := by
      refine Nat.mul_le_mul_left _ ?_
      exact Nat.le_self_pow (by omega) _
    have hp1 := (hpow_df.trans h1).trans hmq
    have hp2 := h2.trans hmq
    have h66 : 1 ≤ 66 ^ (D + 1) := Nat.one_le_pow _ _ (by decide)
    have h2B : 2 * (66 ^ (D + 1) * B) ≤ 4 * (66 ^ (D + 1) * B) := by omega
    calc (2 ^ x.n + A ^ max c_y 1) * N ^ max c_y 1 +
          ((Nat.log2 (0 + (yatesZeta x.n (countMasks x)).length + 1) +
              listMax (fun v => (encNat v).length) (yatesZeta x.n (countMasks x)) + 9) ^ d_f +
            ((yatesZeta x.n (countMasks x)).length + 1) *
              (Nat.log2 (0 + (yatesZeta x.n (countMasks x)).length + 1) +
                listMax (fun v => (encNat v).length) (yatesZeta x.n (countMasks x)) + 10) + 1)
        ≤ B + (66 ^ (D + 1) * B + 66 ^ (D + 1) * B + 1) := by
          linarith only [hwrap_le, hp1, hp2]
      _ ≤ 2 * c_w * B + 4 * 66 ^ (D + 1) * B + 8 * B := by
          calc B + (66 ^ (D + 1) * B + 66 ^ (D + 1) * B + 1)
              ≤ 2 * c_w * B + 4 * (66 ^ (D + 1) * B) + 8 * B := by omega
            _ = _ := by ring
      _ = (2 * c_w + 4 * 66 ^ (D + 1) + 8) * B := by ring
      _ ≤ (2 * c_w + 4 * 66 ^ (D + 1) + 8) * (B + 1) :=
          Nat.mul_le_mul_left _ (Nat.le_succ _)

private theorem computableInO_size_gates :
    ∃ c, ComputableInO (fun x : SymAndInstance => Nat.size x.gates.length)
      encSymAndInstance encNat
      (fun x => ((encSymAndInstance x).length + 1) ^ c)
      (fun x => ((encSymAndInstance x).length + 1) ^ c) := by
  obtain ⟨c_s, hs⟩ := computableInO_gates_len
  obtain ⟨d_sz, _, hdeg_sz⟩ := ComputableInPolyTime.binary_size.exists_degree
  have hcomp := ComputableInO.unaryToNat.comp (hdeg_sz.inO.comp hs)
  refine ⟨max c_s 1 * max d_sz 1 + 1, hcomp.mono 4 (fun x => ?_) (fun x => ?_)⟩ <;>
  · dsimp only [Function.comp_apply]
    set A := (encSymAndInstance x).length + 1
    set C := max c_s 1 * max d_sz 1 + 1
    have h1 : ((encNat x.gates.length).length + 1) ^ d_sz ≤ A ^ max d_sz 1 := by
      have hg := gates_length_le_encSymAndInstance x
      have hlen : (encNat x.gates.length).length ≤ x.gates.length := by
        rw [encNat_apply, Nat.size_eq_bits_len]; exact Nat.size_le_self _
      exact (Nat.pow_le_pow_left (by omega) d_sz).trans
        (Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_left _ _))
    have h2 : A ^ c_s ≤ A ^ C := Nat.pow_le_pow_right (Nat.succ_pos _) (by
      have : 1 ≤ max d_sz 1 := le_max_right _ _
      have : c_s ≤ max c_s 1 := le_max_left _ _
      dsimp only [C]
      nlinarith)
    have h3 : A ^ max d_sz 1 ≤ A ^ C := Nat.pow_le_pow_right (Nat.succ_pos _) (by
      have : 1 ≤ max c_s 1 := le_max_right _ _
      have : max d_sz 1 ≤ max c_s 1 * max d_sz 1 := Nat.le_mul_of_pos_left _ this
      omega)
    have h4 : Nat.size x.gates.length ≤ A ^ C := by
      have hg := gates_length_le_encSymAndInstance x
      have hsz := Nat.size_le_self x.gates.length
      have hA1 : A ≤ A ^ C := Nat.le_self_pow (by omega) A
      omega
    omega

private theorem computableInO_extractMatched :
    ∃ d, ComputableInO (extractMatched false)
      (encList encJoinItem) (encList (encPair encBits encBool))
      (fun L => (encList encJoinItem L).length +
        (L.length + 1) * (listMax (fun p : JoinItem => (encJoinItem p).length) L + 1) ^ d + 1)
      (fun L => (listMax (fun p : JoinItem => (encJoinItem p).length) L + 1) ^ d +
        (L.length + 1) * (listMax (fun p : JoinItem => (encJoinItem p).length) L + 1) + 1) := by
  have hnext : ComputableInPolyTime
      (fun q : Bool × JoinItem => if q.2.2.1 then q.1 else q.2.2.2.2)
      (encPair encBool encJoinItem) encBool := by fun_prop
  have hemit : ComputableInPolyTime
      (fun q : Bool × JoinItem => if q.2.2.1 then [(Nat.bits q.2.2.2.1, q.1)] else [])
      (encPair encBool encJoinItem) (encList (encPair encBits encBool)) := by
    have hpair : ComputableInPolyTime
        (fun q : Bool × JoinItem => (Nat.bits q.2.2.2.1, q.1))
        (encPair encBool encJoinItem) (encPair encBits encBool) := by
      have hb : ComputableInPolyTime (fun q : Bool × JoinItem => Nat.bits q.2.2.2.1)
          (encPair encBool encJoinItem) encBits := by
        have hidx : ComputableInPolyTime (fun q : Bool × JoinItem => q.2.2.2.1)
            (encPair encBool encJoinItem) encNat := by fun_prop
        exact ComputableInPolyTime.natBits.comp hidx
      exact hb.prod (fst encBool encJoinItem)
    have htest : ComputableInPolyTime (fun q : Bool × JoinItem => q.2.2.1)
        (encPair encBool encJoinItem) encBool := by fun_prop
    exact htest.ite (hpair.cons' (const [])) (const [])
  obtain ⟨c_f, d_f, hfold⟩ := ComputableInTimeAndSpace.streamFold_pair_list
    (encA := encJoinItem) (encS := encBool) (encB := encPair encBits encBool)
    (encIn := encPair encBool (encList encJoinItem))
    (init := Prod.fst) (elems := Prod.snd) (fun _ => rfl) hnext hemit
    (g := fun q : Bool × List JoinItem => extractMatched q.1 q.2)
    (fun q => extractMatched_streamEmit q.1 q.2)
    (lMax := fun q => listMax (fun p : JoinItem => (encJoinItem p).length) q.2 + 4)
    (fun q j _ => by
      cases streamState q.1 (fun p : Bool × JoinItem => if p.2.2.1 then p.1 else p.2.2.2.2)
        q.2 j <;> simp)
    (fun q j hj => (le_listMax (f := fun p : JoinItem => (encJoinItem p).length)
      (List.getElem_mem hj)).trans (by omega))
  let D := max d_f 1
  have hwrap : ComputableInO (fun L : List JoinItem => (false, L))
      (encList encJoinItem) (encPair encBool (encList encJoinItem))
      (fun L => (encList encJoinItem L).length) (fun L => (encList encJoinItem L).length) := by
    have hp := (ComputableInO.constZero (encIn := encList encJoinItem)
      (encMid := encBool) false).prod (ComputableInO.id' (encMid := encList encJoinItem))
    exact hp.mono 2 (fun _ => by omega) (fun _ => by omega)
  have hraw : ComputableInO (fun q : Bool × List JoinItem => extractMatched q.1 q.2)
      (encPair encBool (encList encJoinItem)) (encList (encPair encBits encBool))
      (fun q => (encList encJoinItem q.2).length +
        (q.2.length + 1) * (listMax (fun p : JoinItem => (encJoinItem p).length) q.2 + 1) ^ D + 1)
      (fun q => (listMax (fun p : JoinItem => (encJoinItem p).length) q.2 + 1) ^ D +
        (q.2.length + 1) * (listMax (fun p : JoinItem => (encJoinItem p).length) q.2 + 1) + 1) := by
    have hp_fn : ∀ q : Bool × List JoinItem,
        (listMax (fun p : JoinItem => (encJoinItem p).length) q.2 + 5) ^ d_f ≤
          5 ^ d_f * (listMax (fun p : JoinItem => (encJoinItem p).length) q.2 + 1) ^ D :=
      fun q => by
      calc _ ≤ (5 * (listMax (fun p : JoinItem => (encJoinItem p).length) q.2 + 1)) ^ d_f :=
              Nat.pow_le_pow_left (by omega) d_f
        _ = 5 ^ d_f * (listMax (fun p : JoinItem => (encJoinItem p).length) q.2 + 1) ^ d_f :=
            Nat.mul_pow _ _ _
        _ ≤ 5 ^ d_f * (listMax (fun p : JoinItem => (encJoinItem p).length) q.2 + 1) ^ D :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_left _ _))
    refine ComputableInO.of_bounds hfold (3 * c_f * 5 ^ d_f + 6) (fun q => ?_) (fun q => ?_)
      (fun q => ?_)
    · rw [length_encPair]
      have hb : (encBool q.1).length ≤ 2 := by cases q.1 <;> simp
      have hp := hp_fn q
      have hmul := Nat.mul_le_mul_left (q.2.length + 1) hp
      set E := (encList encJoinItem q.2).length
      set B := (q.2.length + 1) * (listMax (fun p : JoinItem => (encJoinItem p).length) q.2 + 1) ^ D
      have hmul' : (q.2.length + 1) *
            (listMax (fun p : JoinItem => (encJoinItem p).length) q.2 + 4 + 1) ^ d_f ≤
          5 ^ d_f * B := by
        calc _ = (q.2.length + 1) *
                (listMax (fun p : JoinItem => (encJoinItem p).length) q.2 + 5) ^ d_f := by ring
          _ ≤ (q.2.length + 1) *
                (5 ^ d_f * (listMax (fun p : JoinItem => (encJoinItem p).length) q.2 + 1) ^ D) :=
              hmul
          _ = 5 ^ d_f * B := by ring
      have h5 : 1 ≤ 5 ^ d_f := Nat.one_le_pow _ _ (by decide)
      have hsum : 2 * (encBool q.1).length + 1 + E +
          (q.2.length + 1) *
            (listMax (fun p : JoinItem => (encJoinItem p).length) q.2 + 4 + 1) ^ d_f + 1 ≤
          3 * 5 ^ d_f * (E + B + 1 + 1) := by
        calc 2 * (encBool q.1).length + 1 + E +
              (q.2.length + 1) *
                (listMax (fun p : JoinItem => (encJoinItem p).length) q.2 + 4 + 1) ^ d_f + 1
            ≤ E + 5 ^ d_f * B + 6 := by omega
          _ ≤ 3 * 5 ^ d_f * (E + B + 1 + 1) := by
              have : 3 * 5 ^ d_f * (E + B + 2) =
                  3 * 5 ^ d_f * E + 3 * 5 ^ d_f * B + 6 * 5 ^ d_f := by ring
              nlinarith only [this, h5]
      calc c_f * (2 * (encBool q.1).length + 1 + E +
              (q.2.length + 1) *
                (listMax (fun p : JoinItem => (encJoinItem p).length) q.2 + 4 + 1) ^ d_f + 1)
          ≤ c_f * (3 * 5 ^ d_f * (E + B + 1 + 1)) := Nat.mul_le_mul_left _ hsum
        _ = (3 * c_f * 5 ^ d_f) * (E + B + 1 + 1) := by ring
        _ ≤ (3 * c_f * 5 ^ d_f + 6) * (E + B + 1 + 1) :=
            Nat.mul_le_mul_right _ (by omega)
    · have hp := hp_fn q
      have h5 : 1 ≤ 5 ^ d_f := Nat.one_le_pow _ _ (by decide)
      set A := (listMax (fun p : JoinItem => (encJoinItem p).length) q.2 + 1) ^ D
      set C := (q.2.length + 1) * (listMax (fun p : JoinItem => (encJoinItem p).length) q.2 + 1)
      have hsum : (listMax (fun p : JoinItem => (encJoinItem p).length) q.2 + 4 + 1) ^ d_f + 1 ≤
          5 ^ d_f * (A + C + 1 + 1) := by
        have h1 : 5 ^ d_f * (A + C + 2) = 5 ^ d_f * A + 5 ^ d_f * C + 2 * 5 ^ d_f := by ring
        have hp' : (listMax (fun p : JoinItem => (encJoinItem p).length) q.2 + 4 + 1) ^ d_f ≤
            5 ^ d_f * A := by
          calc _ = (listMax (fun p : JoinItem => (encJoinItem p).length) q.2 + 5) ^ d_f := by ring
            _ ≤ 5 ^ d_f * A := hp
        nlinarith only [hp', h1, h5]
      have hc : c_f * 5 ^ d_f ≤ 3 * c_f * 5 ^ d_f + 6 := by
        calc c_f * 5 ^ d_f = 1 * (c_f * 5 ^ d_f) := (Nat.one_mul _).symm
          _ ≤ 3 * (c_f * 5 ^ d_f) := Nat.mul_le_mul_right _ (by decide)
          _ = 3 * c_f * 5 ^ d_f := by ring
          _ ≤ 3 * c_f * 5 ^ d_f + 6 := Nat.le_add_right _ 6
      calc c_f * ((listMax (fun p : JoinItem => (encJoinItem p).length) q.2 + 4 + 1) ^ d_f + 1)
          ≤ c_f * (5 ^ d_f * (A + C + 1 + 1)) := Nat.mul_le_mul_left _ hsum
        _ = c_f * 5 ^ d_f * (A + C + 1 + 1) := by ring
        _ ≤ (3 * c_f * 5 ^ d_f + 6) * (A + C + 1 + 1) := Nat.mul_le_mul_right _ hc
    · have hlen_g : (encList (encPair encBits encBool) (extractMatched q.1 q.2)).length ≤
          2 * (q.2.length * (listMax (fun p : JoinItem => (encJoinItem p).length) q.2 + 3)) := by
        have haux : ∀ (b : Bool) (l : List JoinItem),
            (∀ p ∈ l, (encJoinItem p).length ≤
              listMax (fun r : JoinItem => (encJoinItem r).length) q.2) →
            (encList (encPair encBits encBool) (extractMatched b l)).length ≤
              l.length * (2 * (listMax (fun r : JoinItem => (encJoinItem r).length) q.2 + 3)) := by
          intro b l hl
          induction l generalizing b with
          | nil => simp [extractMatched]
          | cons a t ih =>
            have ha := hl a (List.mem_cons_self ..)
            have ht := fun c => ih c (fun r hr => hl r (List.mem_cons_of_mem _ hr))
            rw [extractMatched]
            cases haq : a.2.1
            · simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons]
              exact (ht a.2.2.2).trans (Nat.mul_le_mul_right _ (Nat.le_succ _))
            · simp only [↓reduceIte, encList_cons, List.length_append, List.length_cons,
                length_frame]
              have hlen_p : (encPair encBits encBool (Nat.bits a.2.2.1, b)).length ≤
                  (encJoinItem a).length + 2 := by
                have hb1 : (encBool b).length ≤ 2 := by cases b <;> simp
                have hba : (Nat.bits a.2.2.1).length = (encNat a.2.2.1).length := rfl
                simp only [encJoinItem, length_encPair, encBits_apply]
                omega
              have := ht b
              nlinarith
        calc (encList (encPair encBits encBool) (extractMatched q.1 q.2)).length
            ≤ q.2.length *
                (2 * (listMax (fun r : JoinItem => (encJoinItem r).length) q.2 + 3)) :=
              haux q.1 q.2 (fun p hp =>
                le_listMax (f := fun r : JoinItem => (encJoinItem r).length) hp)
          _ = 2 *
                (q.2.length *
                  (listMax (fun r : JoinItem => (encJoinItem r).length) q.2 + 3)) := by
              ring
      have hmul : q.2.length * (listMax (fun p : JoinItem => (encJoinItem p).length) q.2 + 3) ≤
          3 * ((q.2.length + 1) *
            (listMax (fun p : JoinItem => (encJoinItem p).length) q.2 + 1)) := by
        calc _ ≤ (q.2.length + 1) *
                (3 * (listMax (fun p : JoinItem => (encJoinItem p).length) q.2 + 1)) :=
                Nat.mul_le_mul (Nat.le_succ _) (by omega)
          _ = _ := by ring
      have hle6 : (encList (encPair encBits encBool) (extractMatched q.1 q.2)).length ≤
          6 * ((q.2.length + 1) *
            (listMax (fun p : JoinItem => (encJoinItem p).length) q.2 + 1)) := by
        omega
      exact hle6.trans (Nat.mul_le_mul (by omega) (by omega))
  exact ⟨D, (hraw.comp hwrap).mono 3 (fun L => by dsimp only; omega)
    (fun L => by
      dsimp only
      have h1 : (encList encJoinItem L).length ≤
          L.length * (2 * listMax (fun p : JoinItem => (encJoinItem p).length) L + 1) :=
        length_encList_le encJoinItem L
          (b := listMax (fun r : JoinItem => (encJoinItem r).length) L)
          fun p hp => le_listMax (f := fun r : JoinItem => (encJoinItem r).length) hp
      have h2 : L.length * (2 * listMax (fun p : JoinItem => (encJoinItem p).length) L + 1) ≤
          2 * ((L.length + 1) * (listMax (fun p : JoinItem => (encJoinItem p).length) L + 1)) := by
        calc _ ≤ (L.length + 1) *
                (2 * (listMax (fun p : JoinItem => (encJoinItem p).length) L + 1)) :=
              Nat.mul_le_mul (Nat.le_succ _) (by omega)
          _ = _ := by ring
      calc (encList encJoinItem L).length +
            ((listMax (fun p : JoinItem => (encJoinItem p).length) L + 1) ^ D +
              (L.length + 1) * (listMax (fun p : JoinItem => (encJoinItem p).length) L + 1) + 1)
          ≤ 2 * ((L.length + 1) * (listMax (fun p : JoinItem => (encJoinItem p).length) L + 1)) +
              ((listMax (fun p : JoinItem => (encJoinItem p).length) L + 1) ^ D +
                (L.length + 1) * (listMax (fun p : JoinItem => (encJoinItem p).length) L + 1) +
                1) := Nat.add_le_add_right (h1.trans h2) _
        _ ≤ 3 * ((listMax (fun p : JoinItem => (encJoinItem p).length) L + 1) ^ D +
              (L.length + 1) * (listMax (fun p : JoinItem => (encJoinItem p).length) L + 1) +
              1 + 1) := by omega)⟩

private theorem length_joinInput_le (out : ℕ → Bool) (x : SymAndInstance) :
    (tabulateOut out x.gates.length ++ queryEntries (yatesZeta x.n (countMasks x))).length ≤
      2 ^ x.n + x.gates.length + 1 := by
  have htab_l : (tabulateOut out x.gates.length).length = x.gates.length + 1 := by
    rw [tabulateOut_eq, List.length_map, List.length_reverse, List.length_range]
  have hq_l : (queryEntries (yatesZeta x.n (countMasks x))).length = 2 ^ x.n := by
    have hrec : ∀ k (l : List ℕ), (queryEntriesFrom k l).length = l.length := fun k l => by
      induction l generalizing k with
      | nil => rfl
      | cons _ _ ih => simp [queryEntriesFrom, ih]
    rw [queryEntries, hrec, yatesZeta_countMasks_eq, List.length_map, List.length_range]
  simp only [List.length_append, htab_l, hq_l]
  omega

private theorem length_encJoinItem_joinInput_le (out : ℕ → Bool) (x : SymAndInstance) :
    ∀ p ∈ tabulateOut out x.gates.length ++ queryEntries (yatesZeta x.n (countMasks x)),
      (encJoinItem p).length ≤ 4 * x.n + 6 * Nat.log2 ((encSymAndInstance x).length + 1) + 32 := by
  intro p hp
  have hg_le := gates_length_le_encSymAndInstance x
  have hA_log : ∀ v ≤ x.gates.length,
      (encNat v).length ≤ Nat.log2 ((encSymAndInstance x).length + 1) + 1 := fun v hv =>
    length_encNat_le_log2 (hv.trans (hg_le.trans (Nat.le_succ _)))
  rw [List.mem_append] at hp
  rcases hp with hp | hp
  · rw [tabulateOut_eq, List.mem_map] at hp
    obtain ⟨j, hj, rfl⟩ := hp
    rw [List.mem_reverse, List.mem_range] at hj
    have hj_le : (encNat j).length ≤ Nat.log2 ((encSymAndInstance x).length + 1) + 1 :=
      hA_log j (by omega)
    have h0 : (encNat 0).length = 0 := by simp [encNat_apply]
    have he := length_encJoinItem_le (Nat.bits j) false 0 (out j)
    have hb : (Nat.bits j).length = (encNat j).length := rfl
    omega
  · obtain ⟨_, _, _, j, hj, rfl⟩ := queryEntriesFrom_mem hp
    have hj_lt : j < 2 ^ x.n := by
      rw [yatesZeta_countMasks_eq, List.length_map, List.length_range] at hj; exact hj
    have hgj_le : (yatesZeta x.n (countMasks x))[j] ≤ x.gates.length :=
      yatesZeta_mem_le x (List.getElem_mem hj)
    have hgj_enc := hA_log _ hgj_le
    have hj_enc : (encNat (0 + j)).length ≤ x.n + 1 := by
      rw [Nat.zero_add, encNat_apply, Nat.size_eq_bits_len, Nat.size_le]
      exact hj_lt.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
    have he := length_encJoinItem_le (Nat.bits (yatesZeta x.n (countMasks x))[j]) true (0 + j)
      false
    have hb : (Nat.bits (yatesZeta x.n (countMasks x))[j]).length =
        (encNat (yatesZeta x.n (countMasks x))[j]).length := rfl
    omega

private theorem joined_complexity_bound (n A D_j : ℕ) (hA : 1 ≤ A) (hDj : 1 ≤ D_j) :
    ((2 ^ n + A) * (4 * n + 6 * Nat.log2 A + 32) +
      (Nat.log2 A + 2) * ((2 ^ n + A) * (8 * (n + 1) * (Nat.log2 A + 2) + 33) ^ D_j + 1)) ≤
      320 ^ (D_j + 2) * (2 ^ n + A ^ (D_j + 3)) * (n + 1) ^ (2 * D_j + 2) := by
  have hlog := radix_log_absorb n A (D_j + 1) hA
  have hN1 : 1 ≤ n + 1 := Nat.succ_pos _
  have hL1 : 1 ≤ Nat.log2 A + 2 := by omega
  have hpow_33 : 8 * (n + 1) * (Nat.log2 A + 2) + 33 ≤ 41 * (n + 1) * (Nat.log2 A + 2) := by
    nlinarith
  have hpow_Dj : (8 * (n + 1) * (Nat.log2 A + 2) + 33) ^ D_j ≤
      41 ^ D_j * (n + 1) ^ D_j * (Nat.log2 A + 2) ^ D_j := by
    calc _ ≤ (41 * (n + 1) * (Nat.log2 A + 2)) ^ D_j := Nat.pow_le_pow_left hpow_33 D_j
      _ = _ := by rw [Nat.mul_pow, Nat.mul_pow]
  have hlin_1 : (Nat.log2 A + 2) * ((2 ^ n + A) *
        (41 ^ D_j * (n + 1) ^ D_j * (Nat.log2 A + 2) ^ D_j)) =
      41 ^ D_j * (n + 1) ^ D_j * ((2 ^ n + A) * (Nat.log2 A + 2) ^ (D_j + 1)) := by ring
  have hlin_2 : (2 ^ n + A) * (4 * n + 6 * Nat.log2 A + 32) ≤
      20 * (n + 1) ^ D_j * ((2 ^ n + A) * (Nat.log2 A + 2) ^ (D_j + 1)) := by
    have h1 : 4 * n + 6 * Nat.log2 A + 32 ≤ 20 * (n + 1) * (Nat.log2 A + 2) := by nlinarith
    have h2 : n + 1 ≤ (n + 1) ^ D_j := Nat.le_self_pow (by omega) _
    have h3 : (Nat.log2 A + 2) ^ 1 ≤ (Nat.log2 A + 2) ^ (D_j + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    calc (2 ^ n + A) * (4 * n + 6 * Nat.log2 A + 32)
        ≤ (2 ^ n + A) * (20 * (n + 1) * (Nat.log2 A + 2)) := Nat.mul_le_mul_left _ h1
      _ ≤ (2 ^ n + A) * (20 * (n + 1) ^ D_j * (Nat.log2 A + 2) ^ (D_j + 1)) := by
          refine Nat.mul_le_mul_left _ ?_
          have h3' : Nat.log2 A + 2 ≤ (Nat.log2 A + 2) ^ (D_j + 1) :=
            (pow_one _).symm.le.trans h3
          exact Nat.mul_le_mul (Nat.mul_le_mul_left 20 h2) h3'
      _ = 20 * (n + 1) ^ D_j * ((2 ^ n + A) * (Nat.log2 A + 2) ^ (D_j + 1)) := by ring
  have hlog_A_le : Nat.log2 A + 2 ≤ 2 * A ^ 2 := by
    rcases Nat.eq_or_lt_of_le hA with rfl | hA2
    · decide
    · have h1 : Nat.log2 A ≤ A := Nat.lt_two_pow_self.le.trans (Nat.log2_self_le (by omega))
      have h2 : 2 * A ≤ 2 * A ^ 2 := Nat.mul_le_mul_left 2 (Nat.le_self_pow (by decide) A)
      omega
  have hc320 : (41 ^ D_j + 20) * (2 * 3 ^ (D_j + 2) * 2 ^ (D_j + 1)) + 2 ≤ 320 ^ (D_j + 2) := by
    have h41 : 41 ^ D_j ≤ 41 ^ (D_j + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    have h20 : 20 ≤ 41 ^ (D_j + 1) := le_trans (by decide : 20 ≤ 41 ^ 1)
      (Nat.pow_le_pow_right (by decide) (by omega))
    have h1 : 41 ^ D_j + 20 ≤ 2 * 41 ^ (D_j + 1) := by omega
    have h2 : 2 * 3 ^ (D_j + 2) * 2 ^ (D_j + 1) = 6 * (3 ^ (D_j + 1) * 2 ^ (D_j + 1)) := by ring
    rw [← Nat.mul_pow] at h2
    have h3 : 2 * 41 ^ (D_j + 1) * (6 * 6 ^ (D_j + 1)) =
        12 * (41 ^ (D_j + 1) * 6 ^ (D_j + 1)) := by ring
    rw [← Nat.mul_pow, show 41 * 6 = 246 from rfl] at h3
    have h4 : 246 ^ (D_j + 1) ≤ 320 ^ (D_j + 1) := Nat.pow_le_pow_left (by decide) _
    have h5 : 320 ^ (D_j + 2) = 320 * 320 ^ (D_j + 1) := by ring
    have h6 : 1 ≤ 320 ^ (D_j + 1) := Nat.one_le_pow _ _ (by decide)
    have h7 : (41 ^ D_j + 20) * (2 * 3 ^ (D_j + 2) * 2 ^ (D_j + 1)) ≤
        12 * 320 ^ (D_j + 1) := by
      calc _ ≤ 2 * 41 ^ (D_j + 1) * (6 * 6 ^ (D_j + 1)) := Nat.mul_le_mul h1 (by rw [h2])
        _ = 12 * 246 ^ (D_j + 1) := h3
        _ ≤ 12 * 320 ^ (D_j + 1) := Nat.mul_le_mul_left 12 h4
    omega
  have hcomb1 : (41 ^ D_j + 20) * (n + 1) ^ D_j * ((2 ^ n + A) * (Nat.log2 A + 2) ^ (D_j + 1)) ≤
      (41 ^ D_j + 20) * (2 * 3 ^ (D_j + 2) * 2 ^ (D_j + 1)) *
        ((2 ^ n + A ^ (D_j + 3)) * (n + 1) ^ (2 * D_j + 2)) := by
    have hA_d : A ^ (D_j + 2) ≤ A ^ (D_j + 3) := Nat.pow_le_pow_right hA (by omega)
    have hN_d : (n + 1) ^ (2 * D_j + 1) ≤ (n + 1) ^ (2 * D_j + 2) :=
      Nat.pow_le_pow_right hN1 (by omega)
    calc _ ≤ (41 ^ D_j + 20) * (n + 1) ^ D_j *
            (2 * 3 ^ (D_j + 2) * 2 ^ (D_j + 1) * (2 ^ n + A ^ (D_j + 2)) *
              (n + 1) ^ (D_j + 1)) := Nat.mul_le_mul_left _ hlog
      _ = (41 ^ D_j + 20) * (2 * 3 ^ (D_j + 2) * 2 ^ (D_j + 1)) *
            ((2 ^ n + A ^ (D_j + 2)) * (n + 1) ^ (2 * D_j + 1)) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.add_le_add_left hA_d _) hN_d)
  have hA_pow3 : 2 * A ^ 2 ≤ 2 * ((2 ^ n + A ^ (D_j + 3)) * (n + 1) ^ (2 * D_j + 2)) :=
    Nat.mul_le_mul_left 2
      (((Nat.pow_le_pow_right hA (by omega : 2 ≤ D_j + 3)).trans (Nat.le_add_left _ _)).trans
        (Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ hN1)))
  have hlin_0 : (Nat.log2 A + 2) * ((2 ^ n + A) * (8 * (n + 1) * (Nat.log2 A + 2) + 33) ^ D_j) ≤
      41 ^ D_j * (n + 1) ^ D_j * ((2 ^ n + A) * (Nat.log2 A + 2) ^ (D_j + 1)) := by
    calc _ ≤ (Nat.log2 A + 2) *
            ((2 ^ n + A) * (41 ^ D_j * (n + 1) ^ D_j * (Nat.log2 A + 2) ^ D_j)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hpow_Dj)
      _ = _ := hlin_1
  set B := (2 ^ n + A ^ (D_j + 3)) * (n + 1) ^ (2 * D_j + 2)
  calc (2 ^ n + A) * (4 * n + 6 * Nat.log2 A + 32) +
        (Nat.log2 A + 2) * ((2 ^ n + A) * (8 * (n + 1) * (Nat.log2 A + 2) + 33) ^ D_j + 1)
      = (2 ^ n + A) * (4 * n + 6 * Nat.log2 A + 32) +
          (Nat.log2 A + 2) * ((2 ^ n + A) * (8 * (n + 1) * (Nat.log2 A + 2) + 33) ^ D_j) +
          (Nat.log2 A + 2) := by ring
    _ ≤ (41 ^ D_j + 20) * (n + 1) ^ D_j * ((2 ^ n + A) * (Nat.log2 A + 2) ^ (D_j + 1)) +
          2 * A ^ 2 := by
        have hsum_20 : 20 * (n + 1) ^ D_j * ((2 ^ n + A) * (Nat.log2 A + 2) ^ (D_j + 1)) +
            41 ^ D_j * (n + 1) ^ D_j * ((2 ^ n + A) * (Nat.log2 A + 2) ^ (D_j + 1)) =
            (41 ^ D_j + 20) * (n + 1) ^ D_j * ((2 ^ n + A) * (Nat.log2 A + 2) ^ (D_j + 1)) := by
          ring
        linarith only [hlin_2, hlin_0, hlog_A_le, hsum_20]
    _ ≤ (41 ^ D_j + 20) * (2 * 3 ^ (D_j + 2) * 2 ^ (D_j + 1)) * B + 2 * B :=
        Nat.add_le_add hcomb1 hA_pow3
    _ = ((41 ^ D_j + 20) * (2 * 3 ^ (D_j + 2) * 2 ^ (D_j + 1)) + 2) * B := by ring
    _ ≤ 320 ^ (D_j + 2) * B := Nat.mul_le_mul_right B hc320
    _ = 320 ^ (D_j + 2) * (2 ^ n + A ^ (D_j + 3)) * (n + 1) ^ (2 * D_j + 2) := by ring

private theorem computableInO_joined_of {out : ℕ → Bool} {T S : ℕ → ℕ}
    (hT_mono : Monotone T) (hS_mono : Monotone S)
    (hout : ComputableInO out encNat encBool T S) :
    ∃ C_j, ComputableInO
      (fun x : SymAndInstance => radixSortLSB (Nat.size x.gates.length)
        (tabulateOut out x.gates.length ++ queryEntries (yatesZeta x.n (countMasks x))))
      encSymAndInstance (encList encJoinItem)
      (fun x => (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_j * (T x.gates.length + 1)) *
        (x.n + 1) ^ C_j)
      (fun x => (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_j * (S x.gates.length + 1)) *
        (x.n + 1) ^ C_j) := by
  obtain ⟨c_tab, htab⟩ := computableInO_tabulateOut hT_mono hS_mono hout
  obtain ⟨c_q, hquery⟩ := computableInO_queryEntries
  obtain ⟨c_sz, hsz⟩ := computableInO_size_gates
  let joinInput (x : SymAndInstance) : List JoinItem :=
    tabulateOut out x.gates.length ++ queryEntries (yatesZeta x.n (countMasks x))
  have hjoin_in : ComputableInO joinInput encSymAndInstance (encList encJoinItem)
      (fun x => (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ (max c_tab c_q) *
        (T x.gates.length + 1)) * (x.n + 1) ^ c_q)
      (fun x => (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ (max c_tab c_q) *
        (S x.gates.length + 1)) * (x.n + 1) ^ c_q) := by
    have happ := (ComputableInO.of_linear (ComputableInDegree.listAppend encJoinItem)).comp_linear
      (htab.prod hquery)
    have hjoin_mono : ∀ (F : ℕ → ℕ) (x : SymAndInstance),
        ((encSymAndInstance x).length + 1) ^ c_tab * (F x.gates.length + 1) +
          (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ c_q) * (x.n + 1) ^ c_q ≤
          2 * ((2 ^ x.n + ((encSymAndInstance x).length + 1) ^ (max c_tab c_q) *
            (F x.gates.length + 1)) * (x.n + 1) ^ c_q) := fun F x => by
      set A := (encSymAndInstance x).length + 1
      set N := x.n + 1
      have h1 : A ^ c_tab ≤ A ^ max c_tab c_q :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_left _ _)
      have h2 : A ^ c_q ≤ A ^ max c_tab c_q :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_right _ _)
      have hN : 1 ≤ N ^ c_q := Nat.one_le_pow _ _ (Nat.succ_pos _)
      have h2_le : A ^ c_q ≤ A ^ max c_tab c_q * (F x.gates.length + 1) :=
        h2.trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
      have ht1 : A ^ c_tab * (F x.gates.length + 1) ≤
          (2 ^ x.n + A ^ max c_tab c_q * (F x.gates.length + 1)) * N ^ c_q :=
        ((Nat.mul_le_mul_right _ h1).trans (Nat.le_add_left _ _)).trans
          (Nat.le_mul_of_pos_right _ hN)
      have ht2 : (2 ^ x.n + A ^ c_q) * N ^ c_q ≤
          (2 ^ x.n + A ^ max c_tab c_q * (F x.gates.length + 1)) * N ^ c_q :=
        Nat.mul_le_mul_right _ (Nat.add_le_add_left h2_le _)
      omega
    refine happ.mono 2
      (fun x => (hjoin_mono T x).trans (Nat.mul_le_mul_left 2 (Nat.le_succ _)))
      (fun x => (hjoin_mono S x).trans (Nat.mul_le_mul_left 2 (Nat.le_succ _)))
  obtain ⟨d_js, hjoin_sort⟩ := computableInO_radixSortLSB hsz hjoin_in
    (length_encJoinItem_joinInput_le out)
  let D_j := max d_js 1
  let C_j := max c_sz (max c_tab c_q) + 2 * D_j + 6
  have hpow_d_fn : ∀ x : SymAndInstance,
      ((encNat (Nat.size x.gates.length)).length +
          (4 * x.n + 6 * Nat.log2 ((encSymAndInstance x).length + 1) + 32) + 1) ^ d_js ≤
        (8 * (x.n + 1) * (Nat.log2 ((encSymAndInstance x).length + 1) + 2) + 33) ^ D_j :=
    fun x => by
      set A := (encSymAndInstance x).length + 1
      set N := x.n + 1
      have hg_le := gates_length_le_encSymAndInstance x
      have hlen_sz : (encNat (Nat.size x.gates.length)).length ≤ Nat.log2 A + 1 :=
        length_encNat_le_log2 (((Nat.size_le_self _).trans hg_le).trans (Nat.le_succ _))
      have harg : (encNat (Nat.size x.gates.length)).length +
            (4 * x.n + 6 * Nat.log2 A + 32) + 1 ≤
          8 * N * (Nat.log2 A + 2) + 33 := by
        have hL1 : 1 ≤ Nat.log2 A + 2 := by omega
        have hNx : 4 * x.n ≤ 8 * (x.n * (Nat.log2 A + 2)) := by
          have : x.n ≤ x.n * (Nat.log2 A + 2) := Nat.le_mul_of_pos_right _ hL1
          omega
        have h8 : 8 * N * (Nat.log2 A + 2) =
            8 * (x.n * (Nat.log2 A + 2)) + 8 * (Nat.log2 A + 2) := by
          dsimp only [N]; ring
        omega
      exact (Nat.pow_le_pow_left harg d_js).trans
        (Nat.pow_le_pow_right (by omega) (le_max_left _ _))
  have hjoin_common : ∀ (F : ℕ → ℕ) (x : SymAndInstance),
      (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ (D_j + 3)) * (x.n + 1) ^ (2 * D_j + 2) ≤
        (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_j * (F x.gates.length + 1)) *
          (x.n + 1) ^ C_j ∧
      ((encSymAndInstance x).length + 1) ^ c_sz ≤
        (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_j * (F x.gates.length + 1)) *
          (x.n + 1) ^ C_j ∧
      (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ max c_tab c_q * (F x.gates.length + 1)) *
          (x.n + 1) ^ c_q ≤
        (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_j * (F x.gates.length + 1)) *
          (x.n + 1) ^ C_j ∧
      (encSymAndInstance x).length ≤
        (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_j * (F x.gates.length + 1)) *
          (x.n + 1) ^ C_j ∧
      1 ≤ (x.n + 1) ^ C_j := fun F x => by
    set A := (encSymAndInstance x).length + 1
    set N := x.n + 1
    set BF := (2 ^ x.n + A ^ C_j * (F x.gates.length + 1)) * N ^ C_j
    have hA_j : A ^ (D_j + 3) ≤ A ^ C_j :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (by dsimp only [C_j]; omega)
    have hN_j : N ^ (2 * D_j + 2) ≤ N ^ C_j :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (by dsimp only [C_j]; omega)
    have hA_sz : A ^ c_sz ≤ A ^ C_j :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (by dsimp only [C_j]; omega)
    have hA_t : A ^ max c_tab c_q ≤ A ^ C_j :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (by dsimp only [C_j]; omega)
    have hN_q : N ^ c_q ≤ N ^ C_j :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (by dsimp only [C_j]; omega)
    have hN0 : 1 ≤ N ^ C_j := Nat.one_le_pow _ _ (Nat.succ_pos _)
    have hF0 : 1 ≤ F x.gates.length + 1 := Nat.succ_pos _
    have hA_1 : A ≤ A ^ C_j := Nat.le_self_pow (by dsimp only [C_j]; omega) A
    exact ⟨Nat.mul_le_mul (Nat.add_le_add_left (hA_j.trans (Nat.le_mul_of_pos_right _ hF0)) _) hN_j,
      ((hA_sz.trans (Nat.le_mul_of_pos_right _ hF0)).trans (Nat.le_add_left _ _)).trans
        (Nat.le_mul_of_pos_right _ hN0),
      Nat.mul_le_mul (Nat.add_le_add_left (Nat.mul_le_mul_right _ hA_t) _) hN_q,
      ((Nat.le_succ _).trans hA_1 |>.trans (Nat.le_mul_of_pos_right _ hF0) |>.trans
        (Nat.le_add_left _ _)).trans (Nat.le_mul_of_pos_right _ hN0),
      hN0⟩
  refine ⟨C_j, hjoin_sort.mono (8 * 320 ^ (D_j + 2) + 16) (fun x => ?_) (fun x => ?_)⟩
  · set A := (encSymAndInstance x).length + 1
    set N := x.n + 1
    have hlen_in := length_joinInput_le out x
    have hg_le := gates_length_le_encSymAndInstance x
    have hb_le : Nat.size x.gates.length + 1 ≤ Nat.log2 A + 2 := by
      have h1 : Nat.size x.gates.length ≤ Nat.log2 (x.gates.length + 1) + 1 := by
        rw [← Nat.size_eq_bits_len]
        exact length_encNat_le_log2 (Nat.le_succ x.gates.length)
      have h2 : Nat.log2 (x.gates.length + 1) ≤ Nat.log2 A := log2_mono (by omega)
      omega
    have hpow_d := hpow_d_fn x
    have hjb := joined_complexity_bound x.n A D_j (Nat.succ_pos _) (le_max_right _ _)
    set BT := (2 ^ x.n + A ^ C_j * (T x.gates.length + 1)) * N ^ C_j
    obtain ⟨hbox_le, hsz_le, hjoin_le, hx_le, hN0⟩ := hjoin_common T x
    have h2n : 1 ≤ 2 ^ x.n := Nat.one_le_pow _ _ (by decide)
    have hmul_1 : (joinInput x).length + 1 ≤ 2 * (2 ^ x.n + A) := by
      dsimp only [joinInput] at hlen_in ⊢; omega
    have hmul_1' : ((joinInput x).length + 1) *
          (((encNat (Nat.size x.gates.length)).length +
            (4 * x.n + 6 * Nat.log2 A + 32) + 1) ^ d_js + 1) ≤
        2 * ((2 ^ x.n + A) * ((8 * N * (Nat.log2 A + 2) + 33) ^ D_j + 1)) := by
      calc _ ≤ (2 * (2 ^ x.n + A)) * ((8 * N * (Nat.log2 A + 2) + 33) ^ D_j + 1) :=
              Nat.mul_le_mul hmul_1 (Nat.add_le_add_right hpow_d 1)
        _ = 2 * ((2 ^ x.n + A) * ((8 * N * (Nat.log2 A + 2) + 33) ^ D_j + 1)) := by ring
    have hstep1 : (Nat.size x.gates.length + 1) *
          (((joinInput x).length + 1) *
            (((encNat (Nat.size x.gates.length)).length +
              (4 * x.n + 6 * Nat.log2 A + 32) + 1) ^ d_js + 1)) ≤
        2 * (320 ^ (D_j + 2) * BT) := by
      calc _ ≤ (Nat.log2 A + 2) *
              (2 * ((2 ^ x.n + A) * ((8 * N * (Nat.log2 A + 2) + 33) ^ D_j + 1))) :=
              Nat.mul_le_mul hb_le hmul_1'
        _ = 2 * ((Nat.log2 A + 2) *
              ((2 ^ x.n + A) * ((8 * N * (Nat.log2 A + 2) + 33) ^ D_j + 1))) := by ring
        _ ≤ 2 * (320 ^ (D_j + 2) * ((2 ^ x.n + A ^ (D_j + 3)) * N ^ (2 * D_j + 2))) := by
              refine Nat.mul_le_mul_left 2 ?_
              have hsub1 : (Nat.log2 A + 2) * (2 ^ x.n + A) ≤
                  (2 ^ x.n + A) * (4 * x.n + 6 * Nat.log2 A + 32) := by
                calc (Nat.log2 A + 2) * (2 ^ x.n + A) = (2 ^ x.n + A) * (Nat.log2 A + 2) := by
                      ring
                  _ ≤ (2 ^ x.n + A) * (4 * x.n + 6 * Nat.log2 A + 32) :=
                      Nat.mul_le_mul_left _ (by omega)
              have hsub2 : (Nat.log2 A + 2) *
                    ((2 ^ x.n + A) * ((8 * N * (Nat.log2 A + 2) + 33) ^ D_j + 1)) =
                  (Nat.log2 A + 2) * ((2 ^ x.n + A) * (8 * N * (Nat.log2 A + 2) + 33) ^ D_j) +
                    (Nat.log2 A + 2) * (2 ^ x.n + A) := by ring
              have hsub3 : (Nat.log2 A + 2) *
                    ((2 ^ x.n + A) * (8 * N * (Nat.log2 A + 2) + 33) ^ D_j) ≤
                  (Nat.log2 A + 2) *
                    ((2 ^ x.n + A) * (8 * N * (Nat.log2 A + 2) + 33) ^ D_j + 1) :=
                Nat.mul_le_mul_left _ (Nat.le_succ _)
              calc (Nat.log2 A + 2) *
                      ((2 ^ x.n + A) * ((8 * N * (Nat.log2 A + 2) + 33) ^ D_j + 1))
                  ≤ (2 ^ x.n + A) * (4 * x.n + 6 * Nat.log2 A + 32) +
                      (Nat.log2 A + 2) *
                        ((2 ^ x.n + A) * (8 * N * (Nat.log2 A + 2) + 33) ^ D_j + 1) := by
                      omega
                _ ≤ 320 ^ (D_j + 2) * (2 ^ x.n + A ^ (D_j + 3)) * (x.n + 1) ^ (2 * D_j + 2) :=
                      hjb
                _ = 320 ^ (D_j + 2) * ((2 ^ x.n + A ^ (D_j + 3)) * N ^ (2 * D_j + 2)) := by
                      dsimp only [N]; ring
        _ ≤ 2 * (320 ^ (D_j + 2) * BT) :=
              Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ (by simpa only [A, N, BT] using hbox_le))
    have hBT_pos : 1 ≤ BT := Nat.mul_pos (Nat.add_pos_left (Nat.two_pow_pos _) _) hN0
    have h320_pos : 1 ≤ 320 ^ (D_j + 2) := Nat.one_le_pow _ _ (by decide)
    have h_plus : ((joinInput x).length + 1) *
            (((encNat (Nat.size x.gates.length)).length +
              (4 * x.n + 6 * Nat.log2 A + 32) + 1) ^ d_js) + 1 ≤
          ((joinInput x).length + 1) *
            (((encNat (Nat.size x.gates.length)).length +
              (4 * x.n + 6 * Nat.log2 A + 32) + 1) ^ d_js + 1) := by
      have : 1 ≤ (joinInput x).length + 1 := Nat.succ_pos _
      nlinarith only [this]
    have hstep1' : (Nat.size x.gates.length + 1) *
          (((joinInput x).length + 1) *
            ((encNat (Nat.size x.gates.length)).length +
              (4 * x.n + 6 * Nat.log2 A + 32) + 1) ^ d_js + 1) ≤
        2 * (320 ^ (D_j + 2) * BT) :=
      (Nat.mul_le_mul_left _ h_plus).trans hstep1
    dsimp only [A, N, BT] at hx_le hsz_le hjoin_le hstep1' ⊢
    calc (encSymAndInstance x).length + ((encSymAndInstance x).length + 1) ^ c_sz +
          (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ max c_tab c_q * (T x.gates.length + 1)) *
            (x.n + 1) ^ c_q +
          (Nat.size x.gates.length + 1) *
            (((joinInput x).length + 1) *
              ((encNat (Nat.size x.gates.length)).length +
                (4 * x.n + 6 * Nat.log2 ((encSymAndInstance x).length + 1) + 32) + 1) ^ d_js + 1)
        ≤ ((2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_j * (T x.gates.length + 1)) *
              (x.n + 1) ^ C_j) +
            ((2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_j * (T x.gates.length + 1)) *
              (x.n + 1) ^ C_j) +
            ((2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_j * (T x.gates.length + 1)) *
              (x.n + 1) ^ C_j) +
            2 * (320 ^ (D_j + 2) *
              ((2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_j * (T x.gates.length + 1)) *
                (x.n + 1) ^ C_j)) := by
          linarith only [hx_le, hsz_le, hjoin_le, hstep1']
      _ = (2 * 320 ^ (D_j + 2) + 3) *
            ((2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_j * (T x.gates.length + 1)) *
              (x.n + 1) ^ C_j) := by ring
      _ ≤ (8 * 320 ^ (D_j + 2) + 16) *
            ((2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_j * (T x.gates.length + 1)) *
              (x.n + 1) ^ C_j + 1) :=
          Nat.mul_le_mul (by omega) (Nat.le_succ _)
  · set A := (encSymAndInstance x).length + 1
    set N := x.n + 1
    have hlen_in := length_joinInput_le out x
    have hg_le := gates_length_le_encSymAndInstance x
    have hpow_d := hpow_d_fn x
    have hjb := joined_complexity_bound x.n A D_j (Nat.succ_pos _) (le_max_right _ _)
    set BS := (2 ^ x.n + A ^ C_j * (S x.gates.length + 1)) * N ^ C_j
    obtain ⟨hbox_le, hsz_le, hjoin_le, _, hN0⟩ := hjoin_common S x
    have h2n : 1 ≤ 2 ^ x.n := Nat.one_le_pow _ _ (by decide)
    have hmul_1 : ((joinInput x).length + 1) * (4 * x.n + 6 * Nat.log2 A + 32 + 1) ≤
        4 * ((2 ^ x.n + A) * (4 * x.n + 6 * Nat.log2 A + 32)) := by
      have hlen2 : (joinInput x).length + 1 ≤ 2 * (2 ^ x.n + A) := by
        dsimp only [joinInput] at hlen_in ⊢; omega
      calc _ ≤ (2 * (2 ^ x.n + A)) * (2 * (4 * x.n + 6 * Nat.log2 A + 32)) :=
              Nat.mul_le_mul hlen2 (by omega)
        _ = _ := by ring
    have hmul_2 : (8 * N * (Nat.log2 A + 2) + 33) ^ D_j ≤
        (Nat.log2 A + 2) * ((2 ^ x.n + A) * (8 * N * (Nat.log2 A + 2) + 33) ^ D_j + 1) := by
      have h1 : 1 ≤ 2 ^ x.n + A := by omega
      have h2 : 1 ≤ Nat.log2 A + 2 := by omega
      calc (8 * N * (Nat.log2 A + 2) + 33) ^ D_j
          ≤ 1 * ((2 ^ x.n + A) * (8 * N * (Nat.log2 A + 2) + 33) ^ D_j + 1) := by
            have := Nat.le_mul_of_pos_left ((8 * N * (Nat.log2 A + 2) + 33) ^ D_j) h1
            omega
        _ ≤ (Nat.log2 A + 2) *
              ((2 ^ x.n + A) * (8 * N * (Nat.log2 A + 2) + 33) ^ D_j + 1) :=
            Nat.mul_le_mul_right _ h2
    have hjb_BS : (2 ^ x.n + A) * (4 * x.n + 6 * Nat.log2 A + 32) +
          (Nat.log2 A + 2) * ((2 ^ x.n + A) * (8 * N * (Nat.log2 A + 2) + 33) ^ D_j + 1) ≤
        320 ^ (D_j + 2) * BS := by
      have hjb' : (2 ^ x.n + A) * (4 * x.n + 6 * Nat.log2 A + 32) +
            (Nat.log2 A + 2) * ((2 ^ x.n + A) * (8 * N * (Nat.log2 A + 2) + 33) ^ D_j + 1) ≤
          320 ^ (D_j + 2) * ((2 ^ x.n + A ^ (D_j + 3)) * N ^ (2 * D_j + 2)) := by
        calc _ ≤ 320 ^ (D_j + 2) * (2 ^ x.n + A ^ (D_j + 3)) * (x.n + 1) ^ (2 * D_j + 2) := hjb
          _ = _ := by dsimp only [N]; ring
      exact hjb'.trans (Nat.mul_le_mul_left _ (by simpa only [A, N, BS] using hbox_le))
    have hjb_1 : ((joinInput x).length + 1) * (4 * x.n + 6 * Nat.log2 A + 32 + 1) ≤
        4 * (320 ^ (D_j + 2) * BS) :=
      hmul_1.trans (Nat.mul_le_mul_left 4 ((Nat.le_add_right _ _).trans hjb_BS))
    have hjb_2 : ((encNat (Nat.size x.gates.length)).length +
          (4 * x.n + 6 * Nat.log2 A + 32) + 1) ^ d_js ≤
        320 ^ (D_j + 2) * BS :=
      hpow_d.trans (hmul_2.trans ((Nat.le_add_left _ _).trans hjb_BS))
    have hBS_pos : 1 ≤ BS := Nat.mul_pos (Nat.add_pos_left (Nat.two_pow_pos _) _) hN0
    dsimp only [A, N, BS] at hsz_le hjoin_le hjb_1 hjb_2 ⊢
    calc ((encSymAndInstance x).length + 1) ^ c_sz +
          (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ max c_tab c_q * (S x.gates.length + 1)) *
            (x.n + 1) ^ c_q +
          ((joinInput x).length + 1) *
            (4 * x.n + 6 * Nat.log2 ((encSymAndInstance x).length + 1) + 32 + 1) +
          ((encNat (Nat.size x.gates.length)).length +
            (4 * x.n + 6 * Nat.log2 ((encSymAndInstance x).length + 1) + 32) + 1) ^ d_js
        ≤ ((2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_j * (S x.gates.length + 1)) *
              (x.n + 1) ^ C_j) +
            ((2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_j * (S x.gates.length + 1)) *
              (x.n + 1) ^ C_j) +
            4 * (320 ^ (D_j + 2) *
              ((2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_j * (S x.gates.length + 1)) *
                (x.n + 1) ^ C_j)) +
            320 ^ (D_j + 2) *
              ((2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_j * (S x.gates.length + 1)) *
                (x.n + 1) ^ C_j) := by
          linarith only [hsz_le, hjoin_le, hjb_1, hjb_2]
      _ = (5 * 320 ^ (D_j + 2) + 2) *
            ((2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_j * (S x.gates.length + 1)) *
              (x.n + 1) ^ C_j) := by ring
      _ ≤ (8 * 320 ^ (D_j + 2) + 16) *
            ((2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_j * (S x.gates.length + 1)) *
              (x.n + 1) ^ C_j + 1) :=
          Nat.mul_le_mul (by omega) (Nat.le_succ _)

private theorem extract_complexity_bound (n A D_ex : ℕ) (hA : 1 ≤ A) :
    ((2 ^ n + A) * (4 * n + 6 * Nat.log2 A + 34) ^ D_ex) ≤
      105 ^ (D_ex + 1) * (2 ^ n + A ^ (D_ex + 1)) * (n + 1) ^ (2 * D_ex) := by
  have hlog := radix_log_absorb n A D_ex hA
  have hN1 : 1 ≤ n + 1 := Nat.succ_pos _
  have hL1 : 1 ≤ Nat.log2 A + 2 := by omega
  have h1 : 4 * n + 6 * Nat.log2 A + 34 ≤ 17 * (n + 1) * (Nat.log2 A + 2) := by nlinarith
  have hp : (4 * n + 6 * Nat.log2 A + 34) ^ D_ex ≤
      17 ^ D_ex * (n + 1) ^ D_ex * (Nat.log2 A + 2) ^ D_ex := by
    calc _ ≤ (17 * (n + 1) * (Nat.log2 A + 2)) ^ D_ex := Nat.pow_le_pow_left h1 D_ex
      _ = _ := by rw [Nat.mul_pow, Nat.mul_pow]
  have hc105 : 17 ^ D_ex * (2 * 3 ^ (D_ex + 1) * 2 ^ D_ex) ≤ 105 ^ (D_ex + 1) := by
    have h1 : 17 ^ D_ex * (2 * 3 ^ (D_ex + 1) * 2 ^ D_ex) =
        6 * (17 ^ D_ex * 3 ^ D_ex * 2 ^ D_ex) := by ring
    rw [← Nat.mul_pow, ← Nat.mul_pow, show 17 * 3 * 2 = 102 from rfl] at h1
    have h2 : 102 ^ D_ex ≤ 105 ^ D_ex := Nat.pow_le_pow_left (by decide) D_ex
    have h3 : 105 ^ (D_ex + 1) = 105 * 105 ^ D_ex := by ring
    omega
  calc (2 ^ n + A) * (4 * n + 6 * Nat.log2 A + 34) ^ D_ex
      ≤ (2 ^ n + A) * (17 ^ D_ex * (n + 1) ^ D_ex * (Nat.log2 A + 2) ^ D_ex) :=
        Nat.mul_le_mul_left _ hp
    _ = 17 ^ D_ex * (n + 1) ^ D_ex * ((2 ^ n + A) * (Nat.log2 A + 2) ^ D_ex) := by ring
    _ ≤ 17 ^ D_ex * (n + 1) ^ D_ex *
          (2 * 3 ^ (D_ex + 1) * 2 ^ D_ex * (2 ^ n + A ^ (D_ex + 1)) * (n + 1) ^ D_ex) :=
        Nat.mul_le_mul_left _ hlog
    _ = (17 ^ D_ex * (2 * 3 ^ (D_ex + 1) * 2 ^ D_ex)) *
          ((2 ^ n + A ^ (D_ex + 1)) * (n + 1) ^ (2 * D_ex)) := by ring
    _ ≤ 105 ^ (D_ex + 1) * ((2 ^ n + A ^ (D_ex + 1)) * (n + 1) ^ (2 * D_ex)) :=
        Nat.mul_le_mul_right _ hc105
    _ = 105 ^ (D_ex + 1) * (2 ^ n + A ^ (D_ex + 1)) * (n + 1) ^ (2 * D_ex) := by ring

private def joinInput (out : ℕ → Bool) (x : SymAndInstance) : List JoinItem :=
  tabulateOut out x.gates.length ++ queryEntries (yatesZeta x.n (countMasks x))

private def joined (out : ℕ → Bool) (x : SymAndInstance) : List JoinItem :=
  radixSortLSB (Nat.size x.gates.length) (joinInput out x)

private theorem computableInO_extracted_of {out : ℕ → Bool} {T S : ℕ → ℕ}
    (hT_mono : Monotone T) (hS_mono : Monotone S)
    (hout : ComputableInO out encNat encBool T S) :
    ∃ C_ex, ComputableInO
      (fun x : SymAndInstance => extractMatched false (radixSortLSB (Nat.size x.gates.length)
        (tabulateOut out x.gates.length ++ queryEntries (yatesZeta x.n (countMasks x)))))
      encSymAndInstance (encList (encPair encBits encBool))
      (fun x => (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_ex * (T x.gates.length + 1)) *
        (x.n + 1) ^ C_ex)
      (fun x => (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_ex * (S x.gates.length + 1)) *
        (x.n + 1) ^ C_ex) := by
  obtain ⟨C_j, hjoined⟩ := computableInO_joined_of hT_mono hS_mono hout
  obtain ⟨d_ex, hex_raw⟩ := computableInO_extractMatched
  have hmem_joined : ∀ x : SymAndInstance, ∀ p ∈ joined out x, p ∈ joinInput out x :=
    fun x p hp => (mem_radixStep_iff).1 hp
  have hlen_joined : ∀ x : SymAndInstance, (joined out x).length = (joinInput out x).length :=
    fun x => length_radixStep _ 0 _
  let D_ex := max d_ex 1
  let C_ex := C_j + 2 * D_ex + 4
  have henc_joined_le : ∀ x : SymAndInstance,
      (encList encJoinItem (joined out x)).length ≤
        2 * ((2 ^ x.n + ((encSymAndInstance x).length + 1)) *
          (4 * x.n + 6 * Nat.log2 ((encSymAndInstance x).length + 1) + 34) ^ D_ex) := fun x => by
    have h1 := length_encList_le encJoinItem (joined out x)
      (b := 4 * x.n + 6 * Nat.log2 ((encSymAndInstance x).length + 1) + 32)
      fun p hp => length_encJoinItem_joinInput_le out x p (hmem_joined x p hp)
    have hlen_j := hlen_joined x
    have hlen_in := length_joinInput_le out x
    have hg_le := gates_length_le_encSymAndInstance x
    have h2 : 2 * (4 * x.n + 6 * Nat.log2 ((encSymAndInstance x).length + 1) + 32) + 1 ≤
        2 * (4 * x.n + 6 * Nat.log2 ((encSymAndInstance x).length + 1) + 34) ^ D_ex := by
      have hle : 4 * x.n + 6 * Nat.log2 ((encSymAndInstance x).length + 1) + 34 ≤
          (4 * x.n + 6 * Nat.log2 ((encSymAndInstance x).length + 1) + 34) ^ D_ex :=
        Nat.le_self_pow (by omega) _
      omega
    calc (encList encJoinItem (joined out x)).length
        ≤ (joined out x).length *
            (2 * (4 * x.n + 6 * Nat.log2 ((encSymAndInstance x).length + 1) + 32) + 1) := h1
      _ ≤ (2 ^ x.n + ((encSymAndInstance x).length + 1)) *
            (2 * (4 * x.n + 6 * Nat.log2 ((encSymAndInstance x).length + 1) + 34) ^ D_ex) :=
          Nat.mul_le_mul (by dsimp only [joined, joinInput] at hlen_j ⊢; omega) h2
      _ = 2 * ((2 ^ x.n + ((encSymAndInstance x).length + 1)) *
            (4 * x.n + 6 * Nat.log2 ((encSymAndInstance x).length + 1) + 34) ^ D_ex) := by ring
  have hex_common : ∀ (F : ℕ → ℕ) (x : SymAndInstance),
      (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_j * (F x.gates.length + 1)) *
          (x.n + 1) ^ C_j ≤
        (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_ex * (F x.gates.length + 1)) *
          (x.n + 1) ^ C_ex ∧
      (2 ^ x.n + ((encSymAndInstance x).length + 1)) *
          (4 * x.n + 6 * Nat.log2 ((encSymAndInstance x).length + 1) + 34) ^ D_ex ≤
        105 ^ (D_ex + 1) *
          ((2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_ex * (F x.gates.length + 1)) *
            (x.n + 1) ^ C_ex) := fun F x => by
    set A := (encSymAndInstance x).length + 1
    set N := x.n + 1
    set B := (2 ^ x.n + A ^ C_ex * (F x.gates.length + 1)) * N ^ C_ex
    have hA_c : A ^ C_j ≤ A ^ C_ex := Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
    have hN_c : N ^ C_j ≤ N ^ C_ex := Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
    have hA_d : A ^ (D_ex + 1) ≤ A ^ C_ex := Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
    have hN_d : N ^ (2 * D_ex) ≤ N ^ C_ex := Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
    have hF0 : 1 ≤ F x.gates.length + 1 := Nat.succ_pos _
    have hbox_d : (2 ^ x.n + A ^ (D_ex + 1)) * N ^ (2 * D_ex) ≤ B :=
      Nat.mul_le_mul (Nat.add_le_add_left (hA_d.trans (Nat.le_mul_of_pos_right _ hF0)) _) hN_d
    refine ⟨Nat.mul_le_mul (Nat.add_le_add_left (Nat.mul_le_mul_right _ hA_c) _) hN_c, ?_⟩
    calc (2 ^ x.n + A) * (4 * x.n + 6 * Nat.log2 A + 34) ^ D_ex
        ≤ 105 ^ (D_ex + 1) * (2 ^ x.n + A ^ (D_ex + 1)) * (x.n + 1) ^ (2 * D_ex) :=
          extract_complexity_bound x.n A D_ex (Nat.succ_pos _)
      _ = 105 ^ (D_ex + 1) * ((2 ^ x.n + A ^ (D_ex + 1)) * N ^ (2 * D_ex)) := by
          dsimp only [N]; ring
      _ ≤ 105 ^ (D_ex + 1) * B := Nat.mul_le_mul_left _ hbox_d
  have hex_entry : ∀ x : SymAndInstance,
      listMax (fun p : JoinItem => (encJoinItem p).length) (joined out x) ≤
        4 * x.n + 6 * Nat.log2 ((encSymAndInstance x).length + 1) + 32 ∧
      (listMax (fun p : JoinItem => (encJoinItem p).length) (joined out x) + 1) ^ d_ex ≤
        (4 * x.n + 6 * Nat.log2 ((encSymAndInstance x).length + 1) + 34) ^ D_ex ∧
      (joined out x).length + 1 ≤ 2 * (2 ^ x.n + ((encSymAndInstance x).length + 1)) := fun x => by
    set A := (encSymAndInstance x).length + 1
    have hlen_j := hlen_joined x
    have hlen_in := length_joinInput_le out x
    have hg_le := gates_length_le_encSymAndInstance x
    have hmax_j : listMax (fun p : JoinItem => (encJoinItem p).length) (joined out x) ≤
        4 * x.n + 6 * Nat.log2 A + 32 :=
      listMax_le fun p hp => length_encJoinItem_joinInput_le out x p (hmem_joined x p hp)
    have hpow_ex : (listMax (fun p : JoinItem => (encJoinItem p).length) (joined out x) + 1) ^
          d_ex ≤ (4 * x.n + 6 * Nat.log2 A + 34) ^ D_ex :=
      (Nat.pow_le_pow_left (by omega) d_ex).trans
        (Nat.pow_le_pow_right (by omega) (le_max_left _ _))
    have h2n : 1 ≤ 2 ^ x.n := Nat.one_le_pow _ _ (by decide)
    have hlen2 : (joined out x).length + 1 ≤ 2 * (2 ^ x.n + A) := by
      dsimp only [joined, joinInput] at hlen_j ⊢; omega
    exact ⟨hmax_j, hpow_ex, hlen2⟩
  have hex_envelope : ∀ (B c : ℕ), 1 ≤ B → c ≤ 4 * (105 ^ (D_ex + 1) * B) →
      B + (c + 1) ≤ (8 * 105 ^ (D_ex + 1) + 8) * (B + 1) := fun B c hB hc => by
    have h105 : 1 ≤ 105 ^ (D_ex + 1) := Nat.one_le_pow _ _ (by decide)
    have h105B : B ≤ 105 ^ (D_ex + 1) * B := Nat.le_mul_of_pos_left _ h105
    calc B + (c + 1)
        ≤ B + (4 * (105 ^ (D_ex + 1) * B) + B) := by omega
      _ ≤ 8 * (105 ^ (D_ex + 1) * B) + 8 * B := by omega
      _ = (8 * 105 ^ (D_ex + 1) + 8) * B := by ring
      _ ≤ (8 * 105 ^ (D_ex + 1) + 8) * (B + 1) := Nat.mul_le_mul_left _ (Nat.le_succ _)
  have hcomp := hex_raw.comp hjoined
  refine ⟨C_ex, hcomp.mono (8 * 105 ^ (D_ex + 1) + 8) (fun x => ?_) (fun x => ?_)⟩
  · set A := (encSymAndInstance x).length + 1
    set N := x.n + 1
    set BT := (2 ^ x.n + A ^ C_ex * (T x.gates.length + 1)) * N ^ C_ex
    obtain ⟨hbox_c, hwrap'⟩ := hex_common T x
    obtain ⟨_, hpow_ex, hlen2⟩ := hex_entry x
    have hmul_ex : ((joined out x).length + 1) *
          (listMax (fun p : JoinItem => (encJoinItem p).length) (joined out x) + 1) ^ d_ex ≤
        2 * ((2 ^ x.n + A) * (4 * x.n + 6 * Nat.log2 A + 34) ^ D_ex) := by
      calc _ ≤ (2 * (2 ^ x.n + A)) * (4 * x.n + 6 * Nat.log2 A + 34) ^ D_ex :=
              Nat.mul_le_mul hlen2 hpow_ex
        _ = 2 * ((2 ^ x.n + A) * (4 * x.n + 6 * Nat.log2 A + 34) ^ D_ex) := by ring
    have henc_j' : (encList encJoinItem (joined out x)).length ≤ 2 * (105 ^ (D_ex + 1) * BT) :=
      (henc_joined_le x).trans (Nat.mul_le_mul_left 2 (by simpa only [A, N, BT] using hwrap'))
    have hmul_ex' : ((joined out x).length + 1) *
          (listMax (fun p : JoinItem => (encJoinItem p).length) (joined out x) + 1) ^ d_ex ≤
        2 * (105 ^ (D_ex + 1) * BT) :=
      hmul_ex.trans (Nat.mul_le_mul_left 2 (by simpa only [A, N, BT] using hwrap'))
    have hbox_pos : 1 ≤ BT :=
      Nat.mul_pos (Nat.add_pos_left (Nat.two_pow_pos _) _) (Nat.pow_pos (Nat.succ_pos _))
    dsimp only [A, N, BT, joined, joinInput] at henc_j' hmul_ex' hbox_pos ⊢
    have hc_le : (encList encJoinItem (radixSortLSB (Nat.size x.gates.length)
          (tabulateOut out x.gates.length ++ queryEntries (yatesZeta x.n (countMasks x))))).length +
        ((radixSortLSB (Nat.size x.gates.length)
          (tabulateOut out x.gates.length ++ queryEntries (yatesZeta x.n (countMasks x)))).length +
          1) * (listMax (fun p : JoinItem => (encJoinItem p).length)
            (radixSortLSB (Nat.size x.gates.length)
              (tabulateOut out x.gates.length ++
                queryEntries (yatesZeta x.n (countMasks x)))) + 1) ^ d_ex ≤
        4 * (105 ^ (D_ex + 1) *
          ((2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_ex * (T x.gates.length + 1)) *
            (x.n + 1) ^ C_ex)) := by
      linarith only [henc_j', hmul_ex']
    exact (Nat.add_le_add_right hbox_c _).trans (hex_envelope _ _ hbox_pos hc_le)
  · set A := (encSymAndInstance x).length + 1
    set N := x.n + 1
    set BS := (2 ^ x.n + A ^ C_ex * (S x.gates.length + 1)) * N ^ C_ex
    obtain ⟨hbox_c, hwrap'⟩ := hex_common S x
    obtain ⟨hmax_j, hpow_ex, hlen2⟩ := hex_entry x
    have h2n : 1 ≤ 2 ^ x.n := Nat.one_le_pow _ _ (by decide)
    have h1 : (listMax (fun p : JoinItem => (encJoinItem p).length) (joined out x) + 1) ^ d_ex ≤
        (2 ^ x.n + A) * (4 * x.n + 6 * Nat.log2 A + 34) ^ D_ex :=
      hpow_ex.trans (Nat.le_mul_of_pos_left _ (by omega))
    have h2 : ((joined out x).length + 1) *
          (listMax (fun p : JoinItem => (encJoinItem p).length) (joined out x) + 1) ≤
        2 * ((2 ^ x.n + A) * (4 * x.n + 6 * Nat.log2 A + 34) ^ D_ex) := by
      have hpow_1 : listMax (fun p : JoinItem => (encJoinItem p).length) (joined out x) + 1 ≤
          (4 * x.n + 6 * Nat.log2 A + 34) ^ D_ex :=
        (by dsimp only [A]; omega :
          listMax (fun p : JoinItem => (encJoinItem p).length) (joined out x) + 1 ≤
            4 * x.n + 6 * Nat.log2 A + 34).trans (Nat.le_self_pow (by omega) _)
      calc _ ≤ (2 * (2 ^ x.n + A)) * (4 * x.n + 6 * Nat.log2 A + 34) ^ D_ex :=
              Nat.mul_le_mul hlen2 hpow_1
        _ = _ := by ring
    have h1' : (listMax (fun p : JoinItem => (encJoinItem p).length) (joined out x) + 1) ^ d_ex ≤
        105 ^ (D_ex + 1) * BS := h1.trans (by simpa only [A, N, BS] using hwrap')
    have h2' : ((joined out x).length + 1) *
          (listMax (fun p : JoinItem => (encJoinItem p).length) (joined out x) + 1) ≤
        2 * (105 ^ (D_ex + 1) * BS) :=
      h2.trans (Nat.mul_le_mul_left 2 (by simpa only [A, N, BS] using hwrap'))
    have hbox_pos : 1 ≤ BS :=
      Nat.mul_pos (Nat.add_pos_left (Nat.two_pow_pos _) _) (Nat.pow_pos (Nat.succ_pos _))
    dsimp only [A, N, BS, joined, joinInput] at h1' h2' hbox_pos ⊢
    have hc_le : (listMax (fun p : JoinItem => (encJoinItem p).length)
          (radixSortLSB (Nat.size x.gates.length)
            (tabulateOut out x.gates.length ++
              queryEntries (yatesZeta x.n (countMasks x)))) + 1) ^ d_ex +
        ((radixSortLSB (Nat.size x.gates.length)
          (tabulateOut out x.gates.length ++ queryEntries (yatesZeta x.n (countMasks x)))).length +
          1) * (listMax (fun p : JoinItem => (encJoinItem p).length)
            (radixSortLSB (Nat.size x.gates.length)
              (tabulateOut out x.gates.length ++
                queryEntries (yatesZeta x.n (countMasks x)))) + 1) ≤
        4 * (105 ^ (D_ex + 1) *
          ((2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_ex * (S x.gates.length + 1)) *
            (x.n + 1) ^ C_ex)) := by
      omega
    exact (Nat.add_le_add_right hbox_c _).trans (hex_envelope _ _ hbox_pos hc_le)

/-- **Williams's Evaluation Lemma on multi-tape Turing machines** ([Williams2014], Lemma 4.2,
Proof 1): given any monotonic binary-input Turing-machine evaluator `out` running in time `T` and
space `S`, `x.truthTableList out` is computed in time
`O((2 ^ x.n + ((encSymAndInstance x).length + 1) ^ c * (T x.gates.length + 1)) * (x.n + 1) ^ c)`
and space
`O((2 ^ x.n + ((encSymAndInstance x).length + 1) ^ c * (S x.gates.length + 1)) * (x.n + 1) ^ c)`. -/
theorem computableInO_truthTableList_of_computableInO {out : ℕ → Bool} {T S : ℕ → ℕ}
    (hT_mono : Monotone T) (hS_mono : Monotone S)
    (hout : ComputableInO out encNat encBool T S) :
    ∃ c, ComputableInO (fun x : SymAndInstance => x.truthTableList out) encSymAndInstance encBits
      (fun x => (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ c * (T x.gates.length + 1)) *
        (x.n + 1) ^ c)
      (fun x => (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ c * (S x.gates.length + 1)) *
        (x.n + 1) ^ c) := by
  obtain ⟨C_ex, hextract⟩ := computableInO_extracted_of hT_mono hS_mono hout
  let extracted (x : SymAndInstance) : List (List Bool × Bool) :=
    extractMatched false (joined out x)
  let restored (x : SymAndInstance) : List (List Bool × Bool) :=
    radixSortLSB x.n (extracted x)
  have hmem_joined : ∀ x : SymAndInstance, ∀ p ∈ joined out x, p ∈ joinInput out x :=
    fun x p hp => (mem_radixStep_iff).1 hp
  have hlen_joined : ∀ x : SymAndInstance, (joined out x).length = (joinInput out x).length :=
    fun x => length_radixStep _ 0 _
  have hlen_join_in := length_joinInput_le out
  have hextract_bounds : ∀ x : SymAndInstance,
      (extracted x).length ≤ (joined out x).length ∧
        ∀ r ∈ extracted x, (encPair encBits encBool r).length ≤ 2 * x.n + 8 := by
    have hrec : ∀ (b : Bool) (l : List JoinItem),
        (extractMatched b l).length ≤ l.length ∧
          ∀ r ∈ extractMatched b l, ∃ p ∈ l, r.1 = Nat.bits p.2.2.1 := by
      intro b l
      induction l generalizing b with
      | nil => simp [extractMatched]
      | cons a t ih =>
        rw [extractMatched]
        cases ha : a.2.1
        · simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons]
          obtain ⟨hl, hm⟩ := ih a.2.2.2
          refine ⟨hl.trans (Nat.le_succ _), fun r hr => ?_⟩
          obtain ⟨p, hp, hpe⟩ := hm r hr
          exact ⟨p, List.mem_cons_of_mem _ hp, hpe⟩
        · simp only [↓reduceIte, List.length_cons, List.mem_cons]
          obtain ⟨hl, hm⟩ := ih b
          refine ⟨Nat.succ_le_succ hl, fun r hr => ?_⟩
          rcases hr with rfl | hr
          · exact ⟨a, Or.inl rfl, rfl⟩
          · obtain ⟨p, hp, hpe⟩ := hm r hr
            exact ⟨p, Or.inr hp, hpe⟩
    intro x
    obtain ⟨hl, hm⟩ := hrec false (joined out x)
    refine ⟨hl, fun r hr => ?_⟩
    obtain ⟨p, hp, hr1⟩ := hm r hr
    have hp_in := hmem_joined x p hp
    have hk_lt : p.2.2.1 < 2 ^ x.n := by
      rw [joinInput, List.mem_append] at hp_in
      rcases hp_in with hp_in | hp_in
      · rw [tabulateOut_eq, List.mem_map] at hp_in
        obtain ⟨j, _, rfl⟩ := hp_in
        exact Nat.two_pow_pos x.n
      · obtain ⟨_, hlt, _, _, _, rfl⟩ := queryEntriesFrom_mem hp_in
        have hlen_y : (yatesZeta x.n (countMasks x)).length = 2 ^ x.n := by
          rw [yatesZeta_countMasks_eq, List.length_map, List.length_range]
        simp only at hlt ⊢
        omega
    have hk_enc : r.1.length ≤ x.n + 1 := by
      rw [hr1, ← encNat_apply, encNat_apply, Nat.size_eq_bits_len, Nat.size_le]
      exact hk_lt.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
    have hb_enc : (encBool r.2).length ≤ 2 := by cases r.2 <;> simp
    rw [length_encPair, encBits_apply]
    omega
  obtain ⟨d_rs, hrest_sort⟩ := computableInO_radixSortLSB computableInO_n_nat hextract
    (fun x r hr => (hextract_bounds x).2 r hr)
  let C_r := max C_ex 1 + d_rs + 2
  have hrestored : ComputableInO restored encSymAndInstance (encList (encPair encBits encBool))
      (fun x => (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_r * (T x.gates.length + 1)) *
        (x.n + 1) ^ C_r)
      (fun x => (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_r * (S x.gates.length + 1)) *
        (x.n + 1) ^ C_r) := by
    have hrest_common : ∀ (F : ℕ → ℕ) (x : SymAndInstance),
        ((encSymAndInstance x).length + 1) ≤
          ((encSymAndInstance x).length + 1) ^ C_r * (F x.gates.length + 1) ∧
        (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_ex * (F x.gates.length + 1)) *
            (x.n + 1) ^ C_ex ≤
          (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_r * (F x.gates.length + 1)) *
            (x.n + 1) ^ C_r ∧
        (encSymAndInstance x).length ≤
          (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_r * (F x.gates.length + 1)) *
            (x.n + 1) ^ C_r := fun F x => by
      set A := (encSymAndInstance x).length + 1
      set N := x.n + 1
      have hF0 : 1 ≤ F x.gates.length + 1 := Nat.succ_pos _
      have hA_1 : A ≤ A ^ C_r * (F x.gates.length + 1) :=
        (Nat.le_self_pow (by dsimp only [C_r]; omega) A).trans (Nat.le_mul_of_pos_right _ hF0)
      have hA_c : A ^ C_ex ≤ A ^ C_r :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (by dsimp only [C_r]; omega)
      have hN_c : N ^ C_ex ≤ N ^ C_r :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (by dsimp only [C_r]; omega)
      have hN0 : 1 ≤ N ^ C_r := Nat.one_le_pow _ _ (Nat.succ_pos _)
      exact ⟨hA_1,
        Nat.mul_le_mul (Nat.add_le_add_left (Nat.mul_le_mul_right _ hA_c) _) hN_c,
        ((Nat.le_succ _).trans hA_1 |>.trans (Nat.le_add_left _ _)).trans
          (Nat.le_mul_of_pos_right _ hN0)⟩
    refine hrest_sort.mono (2 * 10 ^ d_rs + 32) (fun x => ?_) (fun x => ?_)
    · set A := (encSymAndInstance x).length + 1
      set N := x.n + 1
      set BT := (2 ^ x.n + A ^ C_r * (T x.gates.length + 1)) * N ^ C_r
      obtain ⟨hA_1, hbox_c, hx_box⟩ := hrest_common T x
      have hlen_e : (extracted x).length + 1 ≤ 2 * (2 ^ x.n + A) := by
        have h1 := (hextract_bounds x).1
        have h2 := hlen_joined x
        have h3 := hlen_join_in x
        have h4 := gates_length_le_encSymAndInstance x
        have h5 : 1 ≤ 2 ^ x.n := Nat.one_le_pow _ _ (by decide)
        dsimp only [extracted, joined, joinInput] at h1 h2 ⊢
        omega
      have hN_ds : N ^ d_rs ≤ N ^ (C_r - 1) :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (by dsimp only [C_r]; omega)
      have hN_sub : N * N ^ (C_r - 1) = N ^ C_r := by
        rw [← pow_succ', Nat.sub_add_cancel (by dsimp only [C_r]; omega)]
      have hmul_N : N * (((extracted x).length + 1) *
            ((encNat x.n).length + (2 * x.n + 8) + 1) ^ d_rs + 1) ≤
          (2 * 10 ^ d_rs + 1) * BT := by
        have h1 : ((extracted x).length + 1) *
              ((encNat x.n).length + (2 * x.n + 8) + 1) ^ d_rs + 1 ≤
            (2 * 10 ^ d_rs + 1) *
              ((2 ^ x.n + A ^ C_r * (T x.gates.length + 1)) * N ^ (C_r - 1)) := by
          have hp := pow_encNat_add_le x.n d_rs
          have hm1 : ((extracted x).length + 1) *
                ((encNat x.n).length + (2 * x.n + 8) + 1) ^ d_rs ≤
              (2 * (2 ^ x.n + A ^ C_r * (T x.gates.length + 1))) * (10 ^ d_rs * N ^ (C_r - 1)) :=
            Nat.mul_le_mul
              (hlen_e.trans (Nat.mul_le_mul_left 2
                (Nat.add_le_add_left (by simpa only [A] using hA_1) _)))
              (hp.trans (Nat.mul_le_mul_left _ hN_ds))
          have hpos1 : 1 ≤ (2 ^ x.n + A ^ C_r * (T x.gates.length + 1)) * N ^ (C_r - 1) :=
            Nat.mul_pos (Nat.add_pos_left (Nat.two_pow_pos _) _)
              (Nat.one_le_pow _ _ (Nat.succ_pos _))
          calc _ ≤ 2 * 10 ^ d_rs * ((2 ^ x.n + A ^ C_r * (T x.gates.length + 1)) *
                  N ^ (C_r - 1)) + 1 := by linarith only [hm1]
            _ ≤ _ := by linarith only [hpos1]
        calc N * _ ≤ N * ((2 * 10 ^ d_rs + 1) *
                ((2 ^ x.n + A ^ C_r * (T x.gates.length + 1)) * N ^ (C_r - 1))) :=
              Nat.mul_le_mul_left _ h1
          _ = (2 * 10 ^ d_rs + 1) * ((2 ^ x.n + A ^ C_r * (T x.gates.length + 1)) *
                (N * N ^ (C_r - 1))) := by ring
          _ = (2 * 10 ^ d_rs + 1) * BT := by rw [hN_sub]
      dsimp only [A, N, BT] at hmul_N ⊢
      calc (encSymAndInstance x).length + (encSymAndInstance x).length +
            (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_ex * (T x.gates.length + 1)) *
              (x.n + 1) ^ C_ex +
            (x.n + 1) * (((extracted x).length + 1) *
              ((encNat x.n).length + (2 * x.n + 8) + 1) ^ d_rs + 1)
          ≤ ((2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_r * (T x.gates.length + 1)) *
                (x.n + 1) ^ C_r) +
              ((2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_r * (T x.gates.length + 1)) *
                (x.n + 1) ^ C_r) +
              ((2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_r * (T x.gates.length + 1)) *
                (x.n + 1) ^ C_r) +
              (2 * 10 ^ d_rs + 1) *
                ((2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_r * (T x.gates.length + 1)) *
                  (x.n + 1) ^ C_r) := by
            linarith only [hx_box, hbox_c, hmul_N]
        _ ≤ (2 * 10 ^ d_rs + 32) *
              ((2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_r * (T x.gates.length + 1)) *
                (x.n + 1) ^ C_r + 1) := by
            have : (2 * 10 ^ d_rs + 4) *
                  ((2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_r * (T x.gates.length + 1)) *
                    (x.n + 1) ^ C_r) ≤
                (2 * 10 ^ d_rs + 32) *
                  ((2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_r * (T x.gates.length + 1)) *
                    (x.n + 1) ^ C_r + 1) :=
              Nat.mul_le_mul (by omega) (Nat.le_succ _)
            linarith only [this]
    · set A := (encSymAndInstance x).length + 1
      set N := x.n + 1
      set BS := (2 ^ x.n + A ^ C_r * (S x.gates.length + 1)) * N ^ C_r
      obtain ⟨hA_1, hbox_c, hN_le⟩ := hrest_common S x
      have hlen_e : (extracted x).length + 1 ≤ 2 * (2 ^ x.n + A) := by
        have h1 := (hextract_bounds x).1
        have h2 := hlen_joined x
        have h3 := hlen_join_in x
        have h4 := gates_length_le_encSymAndInstance x
        have h5 : 1 ≤ 2 ^ x.n := Nat.one_le_pow _ _ (by decide)
        dsimp only [extracted, joined, joinInput] at h1 h2 ⊢
        omega
      have hN_1 : N ≤ N ^ C_r := Nat.le_self_pow (by dsimp only [C_r]; omega) N
      have hN_ds : N ^ d_rs ≤ N ^ C_r :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (by dsimp only [C_r]; omega)
      have hmul_m : ((extracted x).length + 1) * (2 * x.n + 8 + 1) ≤ 18 * BS := by
        have h9 : 2 * x.n + 8 + 1 ≤ 9 * N ^ C_r := by
          have : 2 * x.n + 8 + 1 ≤ 9 * N := by dsimp only [N]; omega
          exact this.trans (Nat.mul_le_mul_left 9 hN_1)
        calc _ ≤ (2 * (2 ^ x.n + A ^ C_r * (S x.gates.length + 1))) * (9 * N ^ C_r) :=
              Nat.mul_le_mul
                (hlen_e.trans (Nat.mul_le_mul_left 2
                  (Nat.add_le_add_left (by simpa only [A] using hA_1) _)))
                h9
          _ = 18 * BS := by ring
      have hp_sort := (pow_encNat_add_le x.n d_rs).trans (Nat.mul_le_mul_left _ hN_ds)
      have hN_box : N ^ C_r ≤ BS := Nat.le_mul_of_pos_left _ (by
        have := Nat.one_le_pow x.n 2 (by decide); omega)
      have hp_sort' : ((encNat x.n).length + (2 * x.n + 8) + 1) ^ d_rs ≤ 10 ^ d_rs * BS :=
        hp_sort.trans (Nat.mul_le_mul_left _ hN_box)
      dsimp only [A, N, BS] at hmul_m hp_sort' ⊢
      calc (encSymAndInstance x).length +
            (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_ex * (S x.gates.length + 1)) *
              (x.n + 1) ^ C_ex +
            ((extracted x).length + 1) * (2 * x.n + 8 + 1) +
            ((encNat x.n).length + (2 * x.n + 8) + 1) ^ d_rs
          ≤ ((2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_r * (S x.gates.length + 1)) *
                (x.n + 1) ^ C_r) +
              ((2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_r * (S x.gates.length + 1)) *
                (x.n + 1) ^ C_r) +
              18 * ((2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_r * (S x.gates.length + 1)) *
                (x.n + 1) ^ C_r) +
              10 ^ d_rs *
                ((2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_r * (S x.gates.length + 1)) *
                  (x.n + 1) ^ C_r) := by
            linarith only [hN_le, hbox_c, hmul_m, hp_sort']
        _ ≤ (2 * 10 ^ d_rs + 32) *
              ((2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_r * (S x.gates.length + 1)) *
                (x.n + 1) ^ C_r + 1) := by
            have : (10 ^ d_rs + 20) *
                  ((2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_r * (S x.gates.length + 1)) *
                    (x.n + 1) ^ C_r) ≤
                (2 * 10 ^ d_rs + 32) *
                  ((2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_r * (S x.gates.length + 1)) *
                    (x.n + 1) ^ C_r + 1) :=
              Nat.mul_le_mul (by omega) (Nat.le_succ _)
            linarith only [this]
  obtain ⟨d_st, hstrip_raw⟩ := computableInO_streamMap
    (fun r : List Bool × Bool => r.2) (ComputableInPolyTime.snd encBits encBool)
  have hbits_raw : ComputableInO (fun x : SymAndInstance => (restored x).map Prod.snd)
      encSymAndInstance encBits
      (fun x => (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ (C_r + d_st + 2) *
        (T x.gates.length + 1)) * (x.n + 1) ^ (C_r + d_st + 2))
      (fun x => (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ (C_r + d_st + 2) *
        (S x.gates.length + 1)) * (x.n + 1) ^ (C_r + d_st + 2)) := by
    have hcomp := (ComputableInO.of_linear ComputableInDegree.listToBits).comp_linear
      (hstrip_raw.comp hrestored)
    have hbits_mono : ∀ (F : ℕ → ℕ) (x : SymAndInstance),
        (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ C_r * (F x.gates.length + 1)) *
            (x.n + 1) ^ C_r +
          ((encList (encPair encBits encBool) (restored x)).length +
            ((restored x).length + 1) *
              (listMax (fun r : List Bool × Bool => (encPair encBits encBool r).length)
                (restored x) + 1) ^ d_st) ≤
          (2 * 9 ^ d_st + 24) *
            ((2 ^ x.n + ((encSymAndInstance x).length + 1) ^ (C_r + d_st + 2) *
              (F x.gates.length + 1)) * (x.n + 1) ^ (C_r + d_st + 2) + 1) := fun F x => by
      set A := (encSymAndInstance x).length + 1
      set N := x.n + 1
      set B := (2 ^ x.n + A ^ (C_r + d_st + 2) * (F x.gates.length + 1)) * N ^ (C_r + d_st + 2)
      have hlen_r : (restored x).length ≤ 2 ^ x.n + A := by
        have h1 : (restored x).length = (extracted x).length := length_radixStep _ 0 _
        have h2 := (hextract_bounds x).1
        have h3 := hlen_joined x
        have h4 := hlen_join_in x
        have h5 := gates_length_le_encSymAndInstance x
        dsimp only [restored, extracted, joined, joinInput] at h1 h2 h3 ⊢
        omega
      have hmem_r : ∀ r ∈ restored x, (encPair encBits encBool r).length ≤ 2 * x.n + 8 :=
        fun r hr => (hextract_bounds x).2 r ((mem_radixStep_iff).1 hr)
      have henc_r : (encList (encPair encBits encBool) (restored x)).length ≤
          (2 ^ x.n + A) * (4 * x.n + 17) := by
        have h1 := (length_encList_le (encPair encBits encBool) (restored x)
          (b := 2 * x.n + 8) hmem_r).trans (Nat.mul_le_mul_right _ hlen_r)
        exact h1.trans (by ring_nf; rfl)
      have hmax_r : listMax (fun r : List Bool × Bool => (encPair encBits encBool r).length)
          (restored x) ≤ 2 * x.n + 8 := listMax_le hmem_r
      have hpow_r : (listMax (fun r : List Bool × Bool => (encPair encBits encBool r).length)
            (restored x) + 1) ^ d_st ≤ 9 ^ d_st * N ^ d_st := by
        calc _ ≤ (9 * N) ^ d_st := Nat.pow_le_pow_left (by omega) d_st
          _ = 9 ^ d_st * N ^ d_st := Nat.mul_pow _ _ _
      have hA_c : A ^ C_r ≤ A ^ (C_r + d_st + 2) :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
      have hN_c : N ^ C_r ≤ N ^ (C_r + d_st + 2) :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
      have hA_1 : A ≤ A ^ (C_r + d_st + 2) := Nat.le_self_pow (by omega) A
      have hN_ds : N ^ d_st ≤ N ^ (C_r + d_st + 2) :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
      have hN_1 : N ≤ N ^ (C_r + d_st + 2) := Nat.le_self_pow (by omega) N
      have hmul_1 : (restored x).length + 1 ≤ 2 * (2 ^ x.n + A) := by
        have := Nat.one_le_pow x.n 2 (by decide)
        omega
      have hmul_2 : (2 ^ x.n + A) * (4 * x.n + 17) ≤
          17 * ((2 ^ x.n + A ^ (C_r + d_st + 2)) * N ^ (C_r + d_st + 2)) := by
        calc (2 ^ x.n + A) * (4 * x.n + 17)
            ≤ (2 ^ x.n + A ^ (C_r + d_st + 2)) * (17 * N ^ (C_r + d_st + 2)) :=
              Nat.mul_le_mul (Nat.add_le_add_left hA_1 _) (by omega)
          _ = _ := by ring
      have hmul_3 : ((restored x).length + 1) *
            (listMax (fun r : List Bool × Bool => (encPair encBits encBool r).length)
              (restored x) + 1) ^ d_st ≤
          2 * 9 ^ d_st * ((2 ^ x.n + A ^ (C_r + d_st + 2)) * N ^ (C_r + d_st + 2)) := by
        calc ((restored x).length + 1) *
              (listMax (fun r : List Bool × Bool => (encPair encBits encBool r).length)
                (restored x) + 1) ^ d_st
            ≤ (2 * (2 ^ x.n + A)) * (9 ^ d_st * N ^ d_st) := Nat.mul_le_mul hmul_1 hpow_r
          _ = 2 * 9 ^ d_st * ((2 ^ x.n + A) * N ^ d_st) := by ring
          _ ≤ 2 * 9 ^ d_st * ((2 ^ x.n + A ^ (C_r + d_st + 2)) * N ^ (C_r + d_st + 2)) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.add_le_add_left hA_1 _) hN_ds)
      have hF0 : 1 ≤ F x.gates.length + 1 := Nat.succ_pos _
      have hbox_c : (2 ^ x.n + A ^ C_r * (F x.gates.length + 1)) * N ^ C_r ≤ B :=
        Nat.mul_le_mul (Nat.add_le_add_left (Nat.mul_le_mul_right _ hA_c) _) hN_c
      have hbox_d : (2 ^ x.n + A ^ (C_r + d_st + 2)) * N ^ (C_r + d_st + 2) ≤ B :=
        Nat.mul_le_mul_right _ (Nat.add_le_add_left (Nat.le_mul_of_pos_right _ hF0) _)
      have h2' : (encList (encPair encBits encBool) (restored x)).length ≤ 17 * B :=
        henc_r.trans (hmul_2.trans (Nat.mul_le_mul_left 17 hbox_d))
      have h3' : ((restored x).length + 1) *
            (listMax (fun r : List Bool × Bool => (encPair encBits encBool r).length)
              (restored x) + 1) ^ d_st ≤ 2 * 9 ^ d_st * B :=
        hmul_3.trans (Nat.mul_le_mul_left _ hbox_d)
      calc (2 ^ x.n + A ^ C_r * (F x.gates.length + 1)) * N ^ C_r +
            ((encList (encPair encBits encBool) (restored x)).length +
              ((restored x).length + 1) *
                (listMax (fun r : List Bool × Bool => (encPair encBits encBool r).length)
                  (restored x) + 1) ^ d_st)
          ≤ B + (17 * B + 2 * 9 ^ d_st * B) := by linarith only [hbox_c, h2', h3']
        _ ≤ (2 * 9 ^ d_st + 24) * (B + 1) := by
            have : (2 * 9 ^ d_st + 18) * B ≤ (2 * 9 ^ d_st + 24) * (B + 1) :=
              Nat.mul_le_mul (by omega) (Nat.le_succ _)
            linarith only [this]
    refine hcomp.mono (2 * 9 ^ d_st + 24) (fun x => hbits_mono T x) (fun x => hbits_mono S x)
  have heq_fn : (fun x : SymAndInstance => (restored x).map Prod.snd) =
      fun x : SymAndInstance => x.truthTableList out := by
    funext x
    exact truthTableList_eq_pipeline x out
  rw [heq_fn] at hbits_raw
  exact ⟨C_r + d_st + 2, hbits_raw⟩

/-- **Williams's Evaluation Lemma on multi-tape Turing machines** ([Williams2014], Lemma 4.2,
Proof 1): for any polynomial-time symmetric gate evaluator `out`, evaluating `x.truthTableList out`
across all `2 ^ x.n` inputs runs in time and space
`O((2 ^ x.n + ((encSymAndInstance x).length + 1) ^ c) * (x.n + 1) ^ c)`. -/
theorem computableInO_truthTableList {out : ℕ → Bool}
    (hout : ComputableInPolyTime out encNat encBool) :
    ∃ c, ComputableInO (fun x : SymAndInstance => x.truthTableList out) encSymAndInstance encBits
      (fun x => (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ c) * (x.n + 1) ^ c)
      (fun x => (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ c) * (x.n + 1) ^ c) := by
  obtain ⟨d, _, hdeg⟩ := hout.exists_degree
  let B : ℕ → ℕ := fun n => ((encNat n).length + 1) ^ d
  have hmono : Monotone B := fun a b hab =>
    Nat.pow_le_pow_left (by have := length_encNat_mono hab; omega) d
  obtain ⟨c, hc⟩ := computableInO_truthTableList_of_computableInO hmono hmono hdeg.inO
  refine ⟨c + d, hc.mono 2 (fun x => ?_) (fun x => ?_)⟩ <;>
  · set A := (encSymAndInstance x).length + 1
    set N := x.n + 1
    have hg := gates_length_le_encSymAndInstance x
    have hlen : (encNat x.gates.length).length ≤ x.gates.length := by
      rw [encNat_apply, Nat.size_eq_bits_len]; exact Nat.size_le_self _
    have hB : B x.gates.length + 1 ≤ 2 * A ^ d := by
      have h1 : B x.gates.length ≤ A ^ d := by
        dsimp only [B]
        exact Nat.pow_le_pow_left (by omega) d
      have h2 : 1 ≤ A ^ d := Nat.one_le_pow _ _ (Nat.succ_pos _)
      omega
    have hN : N ^ c ≤ N ^ (c + d) := Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
    calc (2 ^ x.n + A ^ c * (B x.gates.length + 1)) * N ^ c
        ≤ (2 ^ x.n + A ^ c * (2 * A ^ d)) * N ^ (c + d) :=
          Nat.mul_le_mul (Nat.add_le_add_left (Nat.mul_le_mul_left _ hB) _) hN
      _ ≤ (2 * (2 ^ x.n + A ^ (c + d))) * N ^ (c + d) := by
          refine Nat.mul_le_mul_right _ ?_
          have hpow_c : A ^ c * (2 * A ^ d) = 2 * A ^ (c + d) := by rw [pow_add]; ring
          have h2n : 1 ≤ 2 ^ x.n := Nat.one_le_pow _ _ (by decide)
          omega
      _ = 2 * ((2 ^ x.n + A ^ (c + d)) * N ^ (c + d)) := by ring
      _ ≤ 2 * ((2 ^ x.n + A ^ (c + d)) * N ^ (c + d) + 1) :=
          Nat.mul_le_mul_left 2 (Nat.le_succ _)

end MultiTapeTM
end Cslib.Circuits.Boolean.SymAnd
