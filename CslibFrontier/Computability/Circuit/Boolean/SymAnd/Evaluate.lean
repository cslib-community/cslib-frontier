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
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunProp
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.StreamFold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Subtraction
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.StreamFold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.BinarySizeFacts
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCountedIteration
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
* `Cslib.Circuits.Boolean.SymAnd.SymAndInstance.countList`: the satisfied-AND counts across all
  `2 ^ x.n` inputs, independent of `out`.
* `Cslib.Circuits.Boolean.SymAnd.SymAndInstance.truthTableList`: the truth table as a `List Bool`.

## Main results

* `Cslib.Circuits.Boolean.SymAnd.count_eq_subsetZeta`: the AND count is a zeta transform.
* `Cslib.Circuits.Boolean.SymAnd.truthTable_eq`: correctness of pure `truthTable`.
* `Cslib.Circuits.Boolean.SymAnd.computableInO_countList`: multi-tape Turing machine Yates zeta
  evaluation of `SymAndInstance.countList` in time and space
  `O((2 ^ n + (|enc x| + 1) ^ c) * (n + 1) ^ c)`.
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

/-- The list of satisfied-AND counts of `x` across all `2 ^ x.n` inputs, in the
`BitString.equivFin x.n` order `0, …, 2 ^ x.n - 1`. -/
@[expose] def SymAndInstance.countList (x : SymAndInstance) : List ℕ :=
  List.ofFn fun k : Fin (2 ^ x.n) =>
    (x.toSymAnd fun _ => false).count ((BitString.equivFin x.n).symm k)

/-- `x.countList` has length `2 ^ x.n`. -/
@[simp] theorem SymAndInstance.length_countList (x : SymAndInstance) :
    x.countList.length = 2 ^ x.n := by
  simp [SymAndInstance.countList]

/-- Entry `k` of `x.countList` is the number of AND gates satisfied by
`(BitString.equivFin x.n).symm k`, independent of the symmetric output gate `out`. -/
theorem SymAndInstance.getElem_countList (x : SymAndInstance) (out : ℕ → Bool)
    (k : ℕ) (hk : k < x.countList.length) :
    x.countList[k] =
      (x.toSymAnd out).count ((BitString.equivFin x.n).symm ⟨k, by simpa using hk⟩) := by
  simp [SymAndInstance.countList, SymAnd.count, SymAndInstance.toSymAnd]

/-- Every entry of `x.countList` is at most the number of AND gates `x.gates.length`. -/
theorem SymAndInstance.countList_le_gates_length (x : SymAndInstance) {c : ℕ}
    (hc : c ∈ x.countList) : c ≤ x.gates.length := by
  rw [SymAndInstance.countList, List.mem_ofFn] at hc
  obtain ⟨k, rfl⟩ := hc
  simpa [SymAnd.size, SymAndInstance.toSymAnd] using
    (x.toSymAnd fun _ => false).count_le_size ((BitString.equivFin x.n).symm k)

/-- The truth table of `x.toSymAnd out`, listed in the `BitString.equivFin x.n` order
`0, …, 2 ^ x.n - 1`. -/
@[expose] def SymAndInstance.truthTableList (x : SymAndInstance) (out : ℕ → Bool) : List Bool :=
  List.ofFn fun k : Fin (2 ^ x.n) => (x.toSymAnd out).eval ((BitString.equivFin x.n).symm k)

/-- The truth table of `x.toSymAnd out` is `out` mapped over `x.countList`. -/
theorem SymAndInstance.truthTableList_eq_map_countList (x : SymAndInstance) (out : ℕ → Bool) :
    x.truthTableList out = x.countList.map out := by
  refine List.ext_getElem (by simp [SymAndInstance.truthTableList]) fun k hk1 hk2 => ?_
  simp [SymAndInstance.truthTableList, SymAndInstance.countList, SymAnd.eval, SymAnd.count,
    SymAndInstance.toSymAnd]

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

private theorem list_range_filter_unique {N k : ℕ} (hk : k < N) (p : ℕ → Bool)
    (ht : p k = true) (hf : ∀ j < N, j ≠ k → p j = false) :
    (List.range N).filter p = [k] := by
  have hsplit : List.range N =
      List.range k ++ ([k] ++ (List.range (N - k - 1)).map (· + (k + 1))) := by
    conv_lhs => rw [show N = k + (1 + (N - k - 1)) by omega, List.range_add]
    congr 1
    rw [List.range_add, List.map_append, List.range_one, List.map_singleton, Nat.add_zero,
      List.singleton_append, List.map_map]
    congr 2
    funext a
    dsimp only [Function.comp_apply]
    omega
  have h1 : (List.range k).filter p = [] :=
    List.filter_eq_nil_iff.2 fun j hj => by
      have hj_lt := List.mem_range.1 hj
      simp [hf j (hj_lt.trans hk) (by omega)]
  have h2 : ((List.range (N - k - 1)).map (· + (k + 1))).filter p = [] :=
    List.filter_eq_nil_iff.2 fun j hj => by
      rw [List.mem_map] at hj
      obtain ⟨t, ht', rfl⟩ := hj
      have ht_lt := List.mem_range.1 ht'
      have hltN : t + (k + 1) < N := by omega
      simp [hf _ hltN (by omega)]
  rw [hsplit, List.filter_append, List.filter_append, h1, h2]
  simp [ht]

private theorem encBool_length_le_two (b : Bool) : (encBool b).length ≤ 2 := by
  cases b <;> enc_len

private theorem encNat_length_le (n : ℕ) : (encNat n).length ≤ n := by
  rw [encNat_apply, Nat.size_eq_bits_len]
  exact Nat.size_le_self n

private theorem encNat_length_le_succ (n : ℕ) : (encNat n).length ≤ n + 1 :=
  (encNat_length_le n).trans (Nat.le_succ n)

private theorem pow_shift_le {x k d D : ℕ} (hk : 1 ≤ k) (hd : d ≤ D) :
    (x + k) ^ d ≤ k ^ d * (x + 1) ^ D := by
  calc (x + k) ^ d ≤ (k * (x + 1)) ^ d := Nat.pow_le_pow_left (by nlinarith) d
    _ = k ^ d * (x + 1) ^ d := Nat.mul_pow _ _ _
    _ ≤ k ^ d * (x + 1) ^ D :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.succ_pos _) hd)

private theorem pow_two_mul_shift_le {x k d D : ℕ} (hk : 2 ≤ k) (hd : d ≤ D) :
    (2 * x + k) ^ d ≤ k ^ d * (x + 1) ^ D := by
  calc (2 * x + k) ^ d ≤ (k * (x + 1)) ^ d := Nat.pow_le_pow_left (by nlinarith) d
    _ = k ^ d * (x + 1) ^ d := Nat.mul_pow _ _ _
    _ ≤ k ^ d * (x + 1) ^ D :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.succ_pos _) hd)

private theorem computableInO_pair_const_id {α σ : Type} {encA : α ↪ List Bool}
    {encS : σ ↪ List Bool} (s : σ) :
    ComputableInO (fun L : List α => (s, L)) (encList encA) (encPair encS (encList encA))
      (fun L => (encList encA L).length) (fun L => (encList encA L).length) :=
  ((ComputableInO.constZero s).prod (ComputableInO.id')).weaken (by bigO) (by bigO)

private theorem testBit_evalBits (b : ℕ) (bs : List Bool) (i : ℕ) :
    (evalBits b bs).testBit i = (decide (i < b) && bs.getD i false) := by
  induction b with
  | zero => simp [evalBits]
  | succ b ih =>
    rw [evalBits]
    cases hbit : bs.getD b false
    · simp only [Bool.false_eq_true, ↓reduceIte, add_zero, ih]
      by_cases hi : i < b
      · simp [hi, show i < b + 1 by omega]
      · rcases Nat.eq_or_lt_of_le (Nat.not_lt.1 hi) with rfl | hgt
        · simp only [decide_eq_true (Nat.lt_succ_self b), Bool.true_and]
          simpa [List.getD_eq_getElem?_getD] using hbit
        · simp [show ¬ i < b by omega, show ¬ i < b + 1 by omega]
    · simp only [↓reduceIte]
      rcases lt_trichotomy i b with hlt | rfl | hgt
      · have hmod : 2 ^ b = 2 ^ i * 2 ^ (b - i) := by rw [← pow_add, Nat.add_sub_of_le hlt.le]
        have heven : (2 ^ (b - i)) % 2 = 0 := by
          rw [← Nat.sub_add_cancel (by omega : 0 < b - i), pow_succ]; omega
        rw [Nat.testBit_eq_decide_div_mod_eq] at ih ⊢
        rw [hmod, Nat.add_mul_div_left _ _ (Nat.two_pow_pos i), Nat.add_mod, heven,
          Nat.add_zero, Nat.mod_mod]
        simp only [decide_eq_true (by omega : i < b + 1), Bool.true_and]
        simpa [hlt] using ih
      · have hdiv : (evalBits i bs + 2 ^ i) / 2 ^ i = 1 := by
          rw [Nat.add_div_right _ (Nat.two_pow_pos i), Nat.div_eq_of_lt (evalBits_lt i bs)]
        rw [Nat.testBit_eq_decide_div_mod_eq, hdiv]
        simpa [List.getD_eq_getElem?_getD] using hbit.symm
      · have hlt' : evalBits b bs + 2 ^ b < 2 ^ i := by
          have := evalBits_lt b bs
          calc evalBits b bs + 2 ^ b < 2 ^ (b + 1) := by rw [pow_succ]; omega
            _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) hgt
        rw [Nat.testBit_lt_two_pow hlt']
        simp [show ¬ i < b + 1 by omega]

private theorem evalBits_bits (b k : ℕ) (hk : k < 2 ^ b) : evalBits b (Nat.bits k) = k := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  rw [testBit_evalBits, BinarySub.bits_getD]
  by_cases hi : i < b
  · simp [hi]
  · simp only [hi, decide_false, Bool.false_and]
    exact (Nat.testBit_lt_two_pow (hk.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))).symm

private theorem evalBits_of_len_eq {b : ℕ} {bs₁ bs₂ : List Bool}
    (h1 : bs₁.length = b) (h2 : bs₂.length = b) (heq : evalBits b bs₁ = evalBits b bs₂) :
    bs₁ = bs₂ := by
  refine List.ext_getElem (h1.trans h2.symm) fun i hi1 hi2 => ?_
  have ht := congrArg (fun n => n.testBit i) heq
  simp only [testBit_evalBits, show i < b by omega, decide_true, Bool.true_and,
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
  | succ k ih => rw [Function.iterate_succ_apply, radixStep, ih]; omega

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
    congr 1 <;> refine List.flatMap_congr fun k hk => List.filter_congr fun p _ => ?_
    · have hk_lt : k < 2 ^ b := List.mem_range.1 hk
      rw [evalBits]
      cases hbit : p.1.getD b false
      · simp
      · have hne : evalBits b p.1 + 2 ^ b ≠ k := by omega
        simp [hne]
    · have hk_lt : k < 2 ^ b := List.mem_range.1 hk
      rw [evalBits]
      cases hbit : p.1.getD b false
      · have hne : evalBits b p.1 ≠ 2 ^ b + k := by have := evalBits_lt b p.1; omega
        simp [hne]
      · simp [Nat.add_comm (2 ^ b) k]

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
  | succ k ih => rw [Function.iterate_succ_apply, radixStep, ih, length_radixPass]

private theorem mem_radixPass_iff {α : Type*} {i : ℕ} {L : List (List Bool × α)}
    {p : List Bool × α} : p ∈ radixPass i L ↔ p ∈ L := by
  simp only [radixPass, List.mem_append, List.mem_filter]
  exact ⟨by rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp, fun hp => by
    cases h : p.1.getD i false <;> [exact Or.inl ⟨hp, by simp⟩; exact Or.inr ⟨hp, by simp⟩]⟩

private theorem mem_radixStep_iff {α : Type*} {k i : ℕ} {L : List (List Bool × α)}
    {p : List Bool × α} : p ∈ (radixStep^[k] (i, L)).2 ↔ p ∈ L := by
  induction k generalizing i L with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, radixStep, ih, mem_radixPass_iff]

private theorem streamState_const {α σ : Type*} (s : σ) (xs : List α) (j : ℕ) :
    streamState s (fun p : σ × α => p.1) xs j = s := by
  have htake : ∀ (l : List α) (st : σ), l.foldl (fun p _ => p) st = st := by
    intro l st; induction l with | nil => rfl | cons _ _ ih => exact ih
  exact htake (xs.take j) s

private theorem computableInO_streamFold {α σ β γ : Type}
    {encA : α ↪ List Bool} {encS : σ ↪ List Bool} {encB : β ↪ List Bool}
    {encIn : γ ↪ List Bool}
    (init : γ → σ) (elems : γ → List α)
    (hL : ∀ x, encIn x = encPair encS (encList encA) (init x, elems x))
    {next : σ × α → σ} {emit : σ × α → List β} {g : γ → List β}
    (hnext : ComputableInPolyTime next (encPair encS encA) encS)
    (hemit : ComputableInPolyTime emit (encPair encS encA) (encList encB))
    (hg : ∀ x, encList encB (g x) =
      streamEmit next (fun p => encList encB (emit p)) (init x) (elems x))
    {lMax B : γ → ℕ}
    (hS : ∀ x j, j ≤ (elems x).length →
      (encS (streamState (init x) next (elems x) j)).length ≤ lMax x)
    (hA : ∀ x j (hj : j < (elems x).length), (encA (elems x)[j]).length ≤ lMax x)
    (hl : ∃ c', ∀ x, (encList encB (g x)).length ≤ c' * (B x + 1)) :
    ∃ d, ComputableInO g encIn (encList encB)
      (fun x => (encIn x).length + ((elems x).length + 1) * (lMax x + 1) ^ d)
      (fun x => (lMax x + 1) ^ d + B x) := by
  obtain ⟨c, d, hf⟩ := ComputableInTimeAndSpace.streamFold_pair_list init elems hL hnext hemit hg
    hS hA
  obtain ⟨c', hc'⟩ := hl
  exact ⟨d, ComputableInO.of_bounds hf (max c c')
    (fun x => (Nat.mul_le_mul_right _ (le_max_left c c')).trans (Nat.mul_le_mul_left _ (by omega)))
    (fun x => (Nat.mul_le_mul_right _ (le_max_left c c')).trans (Nat.mul_le_mul_left _ (by omega)))
    (fun x => (hc' x).trans (Nat.mul_le_mul (le_max_right c c') (by omega)))⟩

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
  have hbranch (bTarget : Bool) : ∃ d, ComputableInO
      (fun q : ℕ × List (List Bool × α) => q.2.filter fun p => p.1.getD q.1 false == bTarget)
      (encPair encNat (encList encElem)) (encList encElem)
      (fun q => (encList encElem q.2).length + (q.2.length + 1) * ((encNat q.1).length +
        listMax (fun p => (encElem p).length) q.2 + 1) ^ d)
      (fun q => (encList encElem q.2).length + ((encNat q.1).length +
        listMax (fun p => (encElem p).length) q.2 + 1) ^ d) := by
    let next : ℕ × (List Bool × α) → ℕ := fun p => p.1
    let emit : ℕ × (List Bool × α) → List (List Bool × α) := fun p =>
      if p.2.1.getD p.1 false == bTarget then [p.2] else []
    have hnext : ComputableInPolyTime next (encPair encNat encElem) encNat := by fun_prop
    have hemit : ComputableInPolyTime emit (encPair encNat encElem) (encList encElem) := by
      have htest : ComputableInPolyTime
          (fun p : ℕ × (List Bool × α) => p.2.1.getD (min p.2.1.length p.1) false == bTarget)
          (encPair encNat encElem) encBool := by
        have hkey : ComputableInPolyTime (fun p : ℕ × (List Bool × α) => p.2.1)
            (encPair encNat encElem) encBits := by fun_prop
        have hidx : ComputableInPolyTime
            (fun p : ℕ × (List Bool × α) => min p.2.1.length p.1)
            (encPair encNat encElem) encUnary :=
          binary_min_unary' ((length encBool).comp hkey) (by fun_prop)
        exact (bitsGetDWithInput hkey hidx false).beq (const bTarget)
      have htest_eq : (fun p : ℕ × (List Bool × α) => p.2.1.getD p.1 false == bTarget) =
          (fun p : ℕ × (List Bool × α) => p.2.1.getD (min p.2.1.length p.1) false == bTarget) := by
        funext ⟨i, bs, _⟩
        by_cases hi : i < bs.length
        · rw [Nat.min_eq_right hi.le]
        · have h1 : bs.getD i false = false := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
          have h2 : bs.getD (min bs.length i) false = false := by
            rw [Nat.min_eq_left (by omega), List.getD_eq_getElem?_getD,
              List.getElem?_eq_none le_rfl]; rfl
          rw [h1, h2]
      rw [← htest_eq] at htest
      have hcons : ComputableInPolyTime (fun p : ℕ × (List Bool × α) => [p.2])
          (encPair encNat encElem) (encList encElem) :=
        (ComputableInPolyTime.snd encNat encElem).cons' (const ([] : List (List Bool × α)))
      exact htest.ite hcons (const ([] : List (List Bool × α)))
    have hg : ∀ q : ℕ × List (List Bool × α),
        encList encElem (q.2.filter fun p => p.1.getD q.1 false == bTarget) =
          streamEmit next (fun p => encList encElem (emit p)) q.1 q.2 := by
      have hrec : ∀ i (L : List (List Bool × α)),
          encList encElem (L.filter fun p => p.1.getD i false == bTarget) =
            streamEmit next (fun p => encList encElem (emit p)) i L := by
        intro i L
        induction L with
        | nil => simp [streamEmit, encList_nil]
        | cons a t ih =>
          rw [List.filter_cons, streamEmit]
          dsimp only [next, emit]
          cases hm : (a.1.getD i false == bTarget)
          · simp only [Bool.false_eq_true, ↓reduceIte, encList_nil, List.nil_append]
            exact ih
          · simp only [↓reduceIte, encList_cons, encList_nil, List.append_nil]
            exact congrArg (_ ++ ·) ih
      exact fun ⟨i, L⟩ => hrec i L
    have hstate_eq : ∀ i (L : List (List Bool × α)) j, streamState i next L j = i :=
      fun i L j => streamState_const i L j
    let lMax : ℕ × List (List Bool × α) → ℕ :=
      fun q => (encNat q.1).length + listMax (fun p => (encElem p).length) q.2
    obtain ⟨d, hd⟩ := computableInO_streamFold Prod.fst Prod.snd (fun _ => rfl) hnext hemit hg
      (lMax := lMax) (B := fun q => (encList encElem q.2).length)
      (fun q j _ => by rw [hstate_eq]; exact Nat.le_add_right _ _)
      (fun q j hj => (le_listMax (f := fun p => (encElem p).length)
        (List.getElem_mem hj)).trans (Nat.le_add_left _ _))
      ⟨1, fun q => (ComputableInDegree.length_encList_filter_le encElem _ q.2).trans (by omega)⟩
    let D := max d 1
    refine ⟨D, hd.weaken ⟨3, fun q => ?_⟩ (BigOLe.of_le fun q => ?_)⟩
    · dsimp only [lMax, encElem, D]
      rw [length_encPair]
      have h0 : (encNat q.1).length ≤
          ((encNat q.1).length + listMax (fun p => (encPair encBits encα p).length) q.2 + 1) := by
        omega
      have h1 : (encNat q.1).length ≤
          (q.2.length + 1) *
            ((encNat q.1).length + listMax (fun p => (encPair encBits encα p).length) q.2 + 1) ^
              max d 1 :=
        (h0.trans (Nat.le_self_pow
          (Nat.ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right d 1))) _)).trans
          (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
      have h2 : ((encNat q.1).length +
            listMax (fun p => (encPair encBits encα p).length) q.2 + 1) ^ d ≤
          ((encNat q.1).length +
            listMax (fun p => (encPair encBits encα p).length) q.2 + 1) ^ max d 1 :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_left d 1)
      have h3 : (q.2.length + 1) * ((encNat q.1).length +
            listMax (fun p => (encPair encBits encα p).length) q.2 + 1) ^ d ≤
          (q.2.length + 1) * ((encNat q.1).length +
            listMax (fun p => (encPair encBits encα p).length) q.2 + 1) ^ max d 1 :=
        Nat.mul_le_mul_left _ h2
      omega
    · dsimp only [lMax, encElem, D]
      have h2 : ((encNat q.1).length +
            listMax (fun p => (encPair encBits encα p).length) q.2 + 1) ^ d ≤
          ((encNat q.1).length +
            listMax (fun p => (encPair encBits encα p).length) q.2 + 1) ^ max d 1 :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_left d 1)
      omega
  obtain ⟨d0, h0⟩ := hbranch false
  obtain ⟨d1, h1⟩ := hbranch true
  refine ⟨max d0 d1, (h0.append h1 fun q => by
    rw [radixPass, encList_append]
    exact congrArg (fun l => encList encElem l ++ _)
      (List.filter_congr fun p _ => by cases p.1.getD q.1 false <;> rfl)).weaken
    ⟨2, fun q => ?_⟩ ⟨2, fun q => ?_⟩⟩
  · dsimp only
    have hle0 : ((encNat q.1).length + listMax (fun p => (encElem p).length) q.2 + 1) ^ d0 ≤
        ((encNat q.1).length + listMax (fun p => (encElem p).length) q.2 + 1) ^ max d0 d1 :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_left d0 d1)
    have hle1 : ((encNat q.1).length + listMax (fun p => (encElem p).length) q.2 + 1) ^ d1 ≤
        ((encNat q.1).length + listMax (fun p => (encElem p).length) q.2 + 1) ^ max d0 d1 :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_right d0 d1)
    dsimp only [encElem] at hle0 hle1 ⊢
    nlinarith
  · dsimp only
    have hle0 : ((encNat q.1).length + listMax (fun p => (encElem p).length) q.2 + 1) ^ d0 ≤
        ((encNat q.1).length + listMax (fun p => (encElem p).length) q.2 + 1) ^ max d0 d1 :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_left d0 d1)
    have hle1 : ((encNat q.1).length + listMax (fun p => (encElem p).length) q.2 + 1) ^ d1 ≤
        ((encNat q.1).length + listMax (fun p => (encElem p).length) q.2 + 1) ^ max d0 d1 :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_right d0 d1)
    dsimp only [encElem] at hle0 hle1 ⊢
    omega

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
          ((encNat q.1).length + listMax (fun p => (encElem p).length) q.2 + 1) ^ d)
      (fun q => (encList encElem q.2).length +
        ((encNat q.1).length + listMax (fun p => (encElem p).length) q.2 + 1) ^ d) := by
    have hcomp := (ComputableInO.natSucc.comp (ComputableInO.fst encNat (encList encElem))).prod hp
    refine hcomp.weaken ⟨4, ?_⟩ ⟨4, ?_⟩ <;> intro q
    all_goals
      dsimp only [encElem, encState]
      rw [length_encPair]
      have hdp : ((encNat q.1).length +
            listMax (fun p => (encPair encBits encα p).length) q.2 + 1) ^ dp ≤
          ((encNat q.1).length +
            listMax (fun p => (encPair encBits encα p).length) q.2 + 1) ^ d :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_left dp 2)
      have h1 : (encNat q.1).length ≤
          ((encNat q.1).length +
            listMax (fun p => (encPair encBits encα p).length) q.2 + 1) ^ d :=
        (Nat.le_add_right _ _ |>.trans (Nat.le_add_right _ _)).trans
          (Nat.le_self_pow (Nat.ne_of_gt (lt_of_lt_of_le (by decide) (le_max_right dp 2))) _)
    · have h2 : ((encNat q.1).length + 1) ^ 2 ≤
          ((encNat q.1).length +
            listMax (fun p => (encPair encBits encα p).length) q.2 + 1) ^ d :=
        (Nat.pow_le_pow_left (by omega) 2).trans
          (Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_right dp 2))
      have hm := Nat.mul_le_mul_left (q.2.length + 1) hdp
      have hmul : ((encNat q.1).length +
            listMax (fun p => (encPair encBits encα p).length) q.2 + 1) ^ d ≤
          (q.2.length + 1) * ((encNat q.1).length +
            listMax (fun p => (encPair encBits encα p).length) q.2 + 1) ^ d :=
        Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
      omega
    · omega
  have hinit : ComputableInO (fun x => ((0 : ℕ), L x)) encIn encState
      (fun x => (encIn x).length + TL x) (fun x => SL x) :=
    ((ComputableInO.constZero (encIn := encIn) (encMid := encNat) (0 : ℕ)).prod hL).weaken
      ⟨2, fun _ => by dsimp only; omega⟩ ⟨1, fun _ => by dsimp only; omega⟩
  have henc_step : ∀ x k,
      (encList encElem (radixStep^[k] (0, L x)).2).length ≤
        (L x).length * (2 * M x + 1) := fun x k => by
    have hm : ∀ p ∈ (radixStep^[k] (0, L x)).2, (encElem p).length ≤ M x :=
      fun p hp => hM x p ((mem_radixStep_iff).1 hp)
    have hl : (radixStep^[k] (0, L x)).2.length = (L x).length := length_radixStep k 0 (L x)
    exact (length_encList_le encElem _ (b := M x) hm).trans (by rw [hl])
  have hit := ComputableInO.iterate hb hinit hstep
    (R := fun x => (L x).length * (2 * M x + 1) +
      ((L x).length + 1) * ((encNat (b x)).length + M x + 1) ^ d)
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
  refine ⟨d, (ComputableInO.snd' hit).weaken ⟨8, fun x => ?_⟩ ⟨4, fun x => ?_⟩⟩
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
    nlinarith
  · have h1 : (encNat (b x)).length ≤ ((encNat (b x)).length + M x + 1) ^ d :=
      (by omega : (encNat (b x)).length ≤ _ + 1).trans
        (Nat.le_self_pow (Nat.ne_of_gt (lt_of_lt_of_le (by decide) (le_max_right dp 2))) _)
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
  obtain ⟨d, hsf⟩ := computableInO_streamFold (encA := encBits) (encS := encBool) (encB := encBits)
    Prod.fst Prod.snd (fun _ => rfl) hnext hemit
    (g := fun q : Bool × List (List Bool) => q.2.map (· ++ [q.1]))
    (fun q => maskMap_streamEmit q.1 q.2)
    (lMax := fun q => listMax List.length q.2 + 2)
    (B := fun q => (encList encBits q.2).length + 2 * q.2.length)
    (fun q j _ => by
      change (encBool (streamState q.1 (fun p : Bool × List Bool => p.1) q.2 j)).length ≤ _
      rw [streamState_const]
      exact (encBool_length_le_two q.1).trans (Nat.le_add_left _ _))
    (fun q j hj => (le_listMax (f := List.length) (List.getElem_mem hj)).trans (by omega))
    ⟨1, fun q => (hlen_map q.1 q.2).trans (by omega)⟩
  have hmap (b : Bool) : ComputableInO (fun M : List (List Bool) => M.map (· ++ [b]))
      (encList encBits) (encList encBits)
      (fun M => (encList encBits M).length + (M.length + 1) * (listMax List.length M + 1) ^ d)
      (fun M => (encList encBits M).length + M.length + (listMax List.length M + 1) ^ d) := by
    have hp := hsf.comp (computableInO_pair_const_id b)
    refine hp.weaken ⟨3 ^ d + 5, fun M => ?_⟩ ⟨3 ^ d + 2, fun M => ?_⟩
    · dsimp only
      rw [length_encPair]
      dsimp only
      have hb : (encBool b).length ≤ 2 := encBool_length_le_two b
      have hpow : (listMax List.length M + 2 + 1) ^ d ≤ 3 ^ d * (listMax List.length M + 1) ^ d :=
        pow_shift_le (k := 3) (by decide) le_rfl
      have hmul : (M.length + 1) * (listMax List.length M + 2 + 1) ^ d ≤
          3 ^ d * ((M.length + 1) * (listMax List.length M + 1) ^ d) := by
        calc _ ≤ (M.length + 1) * (3 ^ d * (listMax List.length M + 1) ^ d) :=
              Nat.mul_le_mul_left _ hpow
          _ = _ := by ring
      have h3m : (M.length + 1) * (listMax List.length M + 1) ^ d ≤
          ((encList encBits M).length + (M.length + 1) * (listMax List.length M + 1) ^ d + 1) := by
        omega
      have hmul3 := Nat.mul_le_mul_left (3 ^ d) h3m
      have hlin : 2 * (encList encBits M).length + 2 * (encBool b).length + 1 ≤
          5 * ((encList encBits M).length +
            (M.length + 1) * (listMax List.length M + 1) ^ d + 1) := by
        omega
      calc _ ≤ (2 * (encList encBits M).length + 2 * (encBool b).length + 1) +
            3 ^ d * ((M.length + 1) * (listMax List.length M + 1) ^ d) := by omega
        _ ≤ 5 * _ + 3 ^ d * _ := Nat.add_le_add hlin hmul3
        _ = (3 ^ d + 5) * _ := by ring
    · dsimp only
      have hpow : (listMax List.length M + 2 + 1) ^ d ≤ 3 ^ d * (listMax List.length M + 1) ^ d :=
        pow_shift_le (k := 3) (by decide) le_rfl
      have hm1 : (listMax List.length M + 1) ^ d ≤
          ((encList encBits M).length + M.length + (listMax List.length M + 1) ^ d + 1) := by
        omega
      have hmul3 := Nat.mul_le_mul_left (3 ^ d) hm1
      have hlin : 2 * (encList encBits M).length + 2 * M.length ≤
          2 * ((encList encBits M).length + M.length + (listMax List.length M + 1) ^ d + 1) := by
        omega
      calc _ ≤ 2 * (encList encBits M).length + 2 * M.length +
            3 ^ d * (listMax List.length M + 1) ^ d := by omega
        _ ≤ 2 * _ + 3 ^ d * _ := Nat.add_le_add hlin hmul3
        _ = (3 ^ d + 2) * _ := by ring
  have hstep : ComputableInO maskStep (encList encBits) (encList encBits)
      (fun M => (encList encBits M).length + (M.length + 1) * (listMax List.length M + 1) ^ d)
      (fun M => (encList encBits M).length + M.length + (listMax List.length M + 1) ^ d) :=
    ((ComputableInO.of_linear (ComputableInDegree.listAppend encBits)).comp_linear
      ((hmap false).prod (hmap true))).weaken
      ⟨2, fun _ => by dsimp only; omega⟩ ⟨2, fun _ => by dsimp only; omega⟩
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
      have hm : listMax List.length (allMasks k) ≤ x.n :=
        listMax_le fun bs hbs => (hlen_allMasks_k k bs hbs).le.trans hk
      have h2k : 2 ^ k ≤ 2 ^ x.n := Nat.pow_le_pow_right (by decide) hk
      have hpow : (listMax List.length (allMasks k) + 1) ^ d ≤ (x.n + 1) ^ d :=
        Nat.pow_le_pow_left (by omega) d
      have h1 : 2 ^ k * (2 * k + 1) ≤ 2 ^ x.n * (2 * x.n + 1) := Nat.mul_le_mul h2k (by omega)
      have h2 := Nat.mul_le_mul (by omega : 2 ^ k + 1 ≤ 2 ^ x.n + 1) hpow
      rw [length_allMasks]
      omega)
    (fun x k hk => by
      change (encList encBits (allMasks k)).length + (allMasks k).length +
        (listMax List.length (allMasks k) + 1) ^ d ≤ _
      have hlen := henc_allMasks_k k
      have hm : listMax List.length (allMasks k) ≤ x.n :=
        listMax_le fun bs hbs => (hlen_allMasks_k k bs hbs).le.trans hk
      have h2k : 2 ^ k ≤ 2 ^ x.n := Nat.pow_le_pow_right (by decide) hk
      have hpow : (listMax List.length (allMasks k) + 1) ^ d ≤ (x.n + 1) ^ d :=
        Nat.pow_le_pow_left (by omega) d
      have h1 : 2 ^ k * (2 * k + 1) ≤ 2 ^ x.n * (2 * x.n + 1) := Nat.mul_le_mul h2k (by omega)
      rw [length_allMasks]
      omega)
    (fun x k hk => by
      change (encList encBits (allMasks k)).length ≤ 2 ^ x.n * (2 * x.n + 1)
      have h2k : 2 ^ k ≤ 2 ^ x.n := Nat.pow_le_pow_right (by decide) hk
      exact (henc_allMasks_k k).trans (Nat.mul_le_mul h2k (by omega)))
  refine ⟨d + 4, hit.weaken ⟨12, fun x => ?_⟩ ⟨8, fun x => ?_⟩⟩
  · dsimp only
    have hpow_len := encNat_length_le_succ x.n
    have h6 : 1 ≤ 2 ^ x.n := Nat.one_le_pow _ _ (by decide)
    have hpow2 : ((encNat x.n).length + 1) ^ 2 ≤ 4 * (x.n + 1) ^ 2 := by nlinarith
    have hmul : (2 ^ x.n + 1) * (x.n + 1) ^ d ≤ 2 * 2 ^ x.n * (x.n + 1) ^ d := by
      have h := Nat.mul_le_mul_right ((x.n + 1) ^ d) (by omega : 2 ^ x.n + 1 ≤ 2 * 2 ^ x.n)
      simpa [Nat.mul_assoc] using h
    have hinner : 2 ^ x.n * (2 * x.n + 1) + (2 ^ x.n + 1) * (x.n + 1) ^ d +
          2 ^ x.n * (2 * x.n + 1) + ((encNat x.n).length + 1) ^ 2 ≤
        10 * (2 ^ x.n * (x.n + 1) ^ (d + 3)) := by
      have h2x : 2 * x.n + 1 ≤ 2 * (x.n + 1) := by omega
      have hp1 : (x.n + 1) ^ 1 ≤ (x.n + 1) ^ (d + 3) :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
      have hp2 : (x.n + 1) ^ 2 ≤ (x.n + 1) ^ (d + 3) :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
      have hp3 : (x.n + 1) ^ d ≤ (x.n + 1) ^ (d + 3) :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
      nlinarith
    have hstep1 : (x.n + 1) * (2 ^ x.n * (2 * x.n + 1) + (2 ^ x.n + 1) * (x.n + 1) ^ d +
          2 ^ x.n * (2 * x.n + 1) + ((encNat x.n).length + 1) ^ 2) ≤
        10 * (2 ^ x.n * (x.n + 1) ^ (d + 4)) := by
      calc _ ≤ (x.n + 1) * (10 * (2 ^ x.n * (x.n + 1) ^ (d + 3))) :=
              Nat.mul_le_mul_left _ hinner
        _ = 10 * (2 ^ x.n * (x.n + 1) ^ (d + 4)) := by ring
    omega
  · dsimp only
    have h6 : 1 ≤ 2 ^ x.n := Nat.one_le_pow _ _ (by decide)
    have h1 := encNat_length_le_succ x.n
    have hb : (x.n + 1) ^ d ≤ 2 ^ x.n * (x.n + 1) ^ (d + 4) :=
      (Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)).trans (Nat.le_mul_of_pos_left _ h6)
    have hp1 : (x.n + 1) ^ 1 ≤ (x.n + 1) ^ (d + 4) :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
    have h2x : 2 ^ x.n * (2 * x.n + 1) ≤ 2 * (2 ^ x.n * (x.n + 1) ^ (d + 4)) := by
      have h : 2 * x.n + 1 ≤ 2 * (x.n + 1) ^ (d + 4) := by
        have : x.n + 1 ≤ (x.n + 1) ^ (d + 4) := (pow_one _).symm.le.trans hp1
        omega
      exact (Nat.mul_le_mul_left _ h).trans (by ring_nf; rfl)
    have h1p : 2 ^ x.n ≤ 2 ^ x.n * (x.n + 1) ^ (d + 4) :=
      Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (Nat.succ_pos _))
    have hn1 : (encNat x.n).length ≤ 2 ^ x.n * (x.n + 1) ^ (d + 4) :=
      (h1.trans ((pow_one _).symm.le.trans hp1)).trans (Nat.le_mul_of_pos_left _ h6)
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
      have hf := list_range_filter_unique hk_lt (fun j => evalBits x.n (maskBits x.n j) == k)
        (by simp [evalBits_maskBits x.n k hk_lt])
        (fun j hj hne => by simp [evalBits_maskBits x.n j hj, hne])
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
  obtain ⟨d_out, _, hdeg⟩ := hf.exists_degree
  obtain ⟨c_out, hc_out⟩ := hdeg.inO.length_le
  have hlen_aux : ∀ (M : ℕ) (l : List α), (∀ a ∈ l, (encA a).length ≤ M) →
      (encList encB (l.map f)).length ≤ l.length * (4 * c_out * (M + 1) ^ d_out + 1) := by
    intro M l hl
    induction l with
    | nil => simp
    | cons a t ih =>
      have ha : (encA a).length ≤ M := hl a (List.mem_cons_self ..)
      have ht := ih fun b hb => hl b (List.mem_cons_of_mem _ hb)
      have hf_le : (encB (f a)).length ≤ c_out * ((M + 1) ^ d_out + 1) :=
        (hc_out a).trans (Nat.mul_le_mul_left _ (by
          exact Nat.add_le_add_right (Nat.pow_le_pow_left (by omega) d_out) 1))
      have hpow1 : 1 ≤ (M + 1) ^ d_out := Nat.one_le_pow _ _ (Nat.succ_pos _)
      have helem : (encB (f a)).length ≤ 2 * c_out * (M + 1) ^ d_out := by nlinarith
      rw [List.map_cons, encList_cons, List.length_append, List.length_cons, length_frame]
      nlinarith
  obtain ⟨d, hsf⟩ := computableInO_streamFold (encA := encA) (encS := encUnit) (encB := encB)
    Prod.fst Prod.snd (fun _ => rfl) hnext hemit
    (g := fun q : Unit × List α => q.2.map f)
    (fun q => streamMap_streamEmit encB f q.2)
    (lMax := fun q => listMax (fun a => (encA a).length) q.2 + 2)
    (B := fun q => (q.2.length + 1) * (listMax (fun a => (encA a).length) q.2 + 1) ^ d_out)
    (fun q j _ => by
      change (encUnit (streamState q.1 (fun p : Unit × α => p.1) q.2 j)).length ≤ _
      rw [streamState_const, encUnit_apply, List.length_nil]; omega)
    (fun q j hj => (le_listMax (f := fun a => (encA a).length) (List.getElem_mem hj)).trans
      (by omega))
    ⟨4 * c_out + 1, fun q => by
      have h1 := hlen_aux (listMax (fun a => (encA a).length) q.2) q.2
        (fun a ha => le_listMax (f := fun a => (encA a).length) ha)
      have hpow1 : 1 ≤ (listMax (fun a => (encA a).length) q.2 + 1) ^ d_out :=
        Nat.one_le_pow _ _ (Nat.succ_pos _)
      nlinarith⟩
  let D := max d d_out
  refine ⟨D, (hsf.comp (computableInO_pair_const_id ())).weaken
    ⟨3 ^ d + 2, fun L => ?_⟩ ⟨3 ^ d + 2, fun L => ?_⟩⟩
  · dsimp only [D]
    rw [length_encPair, encUnit_apply, List.length_nil]
    dsimp only
    have hpow := pow_shift_le (x := listMax (fun a => (encA a).length) L) (k := 3) (by decide)
      (le_max_left d d_out)
    have hmul : (L.length + 1) * (listMax (fun a => (encA a).length) L + 2 + 1) ^ d ≤
        3 ^ d * ((L.length + 1) * (listMax (fun a => (encA a).length) L + 1) ^ max d d_out) := by
      calc _ ≤ (L.length + 1) *
            (3 ^ d * (listMax (fun a => (encA a).length) L + 1) ^ max d d_out) :=
            Nat.mul_le_mul_left _ hpow
        _ = _ := by ring
    have h1 : (L.length + 1) * (listMax (fun a => (encA a).length) L + 1) ^ max d d_out ≤
        ((encList encA L).length +
          (L.length + 1) * (listMax (fun a => (encA a).length) L + 1) ^ max d d_out + 1) := by
      omega
    have hmul3 := Nat.mul_le_mul_left (3 ^ d) h1
    have hlin : 2 * (encList encA L).length + 1 ≤
        2 * ((encList encA L).length +
          (L.length + 1) * (listMax (fun a => (encA a).length) L + 1) ^ max d d_out + 1) := by
      omega
    calc _ ≤ 2 * (encList encA L).length + 1 +
          3 ^ d * ((L.length + 1) * (listMax (fun a => (encA a).length) L + 1) ^ max d d_out) := by
          omega
      _ ≤ 2 * _ + 3 ^ d * _ := Nat.add_le_add hlin hmul3
      _ = (3 ^ d + 2) * _ := by ring
  · dsimp only [D]
    have hpow1 := (pow_shift_le (x := listMax (fun a => (encA a).length) L) (k := 3) (by decide)
      (le_max_left d d_out)).trans
        (Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega : 0 < L.length + 1)))
    have hpow2 : (listMax (fun a => (encA a).length) L + 1) ^ d_out ≤
        (listMax (fun a => (encA a).length) L + 1) ^ max d d_out :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_right d d_out)
    have hmul2 := Nat.mul_le_mul_left (L.length + 1) hpow2
    have h1 : (L.length + 1) * (listMax (fun a => (encA a).length) L + 1) ^ max d d_out ≤
        ((encList encA L).length +
          (L.length + 1) * (listMax (fun a => (encA a).length) L + 1) ^ max d d_out + 1) := by
      omega
    have hmul3 := Nat.mul_le_mul_left (3 ^ d) h1
    have hlin : (encList encA L).length +
        (L.length + 1) * (listMax (fun a => (encA a).length) L + 1) ^ d_out ≤
        2 * ((encList encA L).length +
          (L.length + 1) * (listMax (fun a => (encA a).length) L + 1) ^ max d d_out + 1) := by
      omega
    have hassoc : (listMax (fun a => (encA a).length) L + 2 + 1) ^ d =
        (listMax (fun a => (encA a).length) L + 3) ^ d := by ring_nf
    calc _ ≤ (encList encA L).length +
          (L.length + 1) * (listMax (fun a => (encA a).length) L + 1) ^ d_out +
          3 ^ d * ((L.length + 1) * (listMax (fun a => (encA a).length) L + 1) ^ max d d_out) := by
          rw [hassoc]; omega
      _ ≤ 2 * _ + 3 ^ d * _ := Nat.add_le_add hlin hmul3
      _ = (3 ^ d + 2) * _ := by ring

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

private abbrev symBox (c : ℕ) (F : ℕ → ℕ) (x : SymAndInstance) : ℕ :=
  (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ c * (F x.gates.length + 1)) * (x.n + 1) ^ c

private theorem symBox_pos (c : ℕ) (F : ℕ → ℕ) (x : SymAndInstance) : 1 ≤ symBox c F x :=
  Nat.mul_pos (Nat.add_pos_left (Nat.two_pow_pos _) _) (Nat.one_le_pow _ _ (Nat.succ_pos _))

private theorem symBox_mono {c₁ c₂ : ℕ} {F₁ F₂ : ℕ → ℕ} (hc : c₁ ≤ c₂)
    (hF : ∀ s, F₁ s ≤ F₂ s) (x : SymAndInstance) : symBox c₁ F₁ x ≤ symBox c₂ F₂ x :=
  Nat.mul_le_mul
    (Nat.add_le_add_left (Nat.mul_le_mul
      (Nat.pow_le_pow_right (Nat.succ_pos _) hc) (Nat.succ_le_succ (hF _))) _)
    (Nat.pow_le_pow_right (Nat.succ_pos _) hc)

private theorem A_pow_le_symBox {d c : ℕ} (hdc : d ≤ c) (F : ℕ → ℕ) (x : SymAndInstance) :
    ((encSymAndInstance x).length + 1) ^ d ≤ symBox c F x :=
  ((Nat.pow_le_pow_right (Nat.succ_pos _) hdc).trans
    (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)) |>.trans (Nat.le_add_left _ _)).trans
    (Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (Nat.succ_pos _)))

private theorem enc_le_symBox {c : ℕ} (hc : 1 ≤ c) (F : ℕ → ℕ) (x : SymAndInstance) :
    (encSymAndInstance x).length ≤ symBox c F x :=
  ((Nat.le_succ _).trans (Nat.pow_one _).symm.le).trans (A_pow_le_symBox hc F x)

private theorem n_pow_le_symBox {d c : ℕ} (hdc : d ≤ c) (F : ℕ → ℕ) (x : SymAndInstance) :
    (x.n + 1) ^ d ≤ symBox c F x :=
  (Nat.pow_le_pow_right (Nat.succ_pos _) hdc).trans
    (Nat.le_mul_of_pos_left _ (Nat.add_pos_left (Nat.two_pow_pos _) _))

private theorem two_pow_mul_n_le_symBox {d c : ℕ} (hdc : d ≤ c) (F : ℕ → ℕ) (x : SymAndInstance) :
    2 ^ x.n * (x.n + 1) ^ d ≤ symBox c F x :=
  Nat.mul_le_mul (Nat.le_add_right _ _) (Nat.pow_le_pow_right (Nat.succ_pos _) hdc)

private theorem symBox_log_le {r k c : ℕ} (hrc : k + r ≤ c) (hkc : k + 1 ≤ c) (F : ℕ → ℕ)
    (x : SymAndInstance) :
    (2 ^ x.n + ((encSymAndInstance x).length + 1)) * (x.n + 1) ^ r *
        (Nat.log2 ((encSymAndInstance x).length + 1) + 2) ^ k ≤
      2 * 3 ^ (k + 1) * 2 ^ k * symBox c F x := by
  set A := (encSymAndInstance x).length + 1
  set N := x.n + 1
  have hlog := radix_log_absorb x.n A k (Nat.succ_pos _)
  have hbox : (2 ^ x.n + A ^ (k + 1)) * N ^ (k + r) ≤ symBox c F x :=
    Nat.mul_le_mul (Nat.add_le_add_left
      ((Nat.pow_le_pow_right (Nat.succ_pos _) hkc).trans
        (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))) _)
      (Nat.pow_le_pow_right (Nat.succ_pos _) hrc)
  calc (2 ^ x.n + A) * N ^ r * (Nat.log2 A + 2) ^ k
      = N ^ r * ((2 ^ x.n + A) * (Nat.log2 A + 2) ^ k) := by ring
    _ ≤ N ^ r * (2 * 3 ^ (k + 1) * 2 ^ k * (2 ^ x.n + A ^ (k + 1)) * N ^ k) :=
        Nat.mul_le_mul_left _ hlog
    _ = 2 * 3 ^ (k + 1) * 2 ^ k * ((2 ^ x.n + A ^ (k + 1)) * N ^ (k + r)) := by
        rw [pow_add]; ring
    _ ≤ 2 * 3 ^ (k + 1) * 2 ^ k * symBox c F x := Nat.mul_le_mul_left _ hbox

private theorem symBox_zero_weaken {α : Type} {f : SymAndInstance → α} {encOut : α ↪ List Bool}
    {c : ℕ} (h : ComputableInO f encSymAndInstance encOut
      (symBox c fun _ => 0) (symBox c fun _ => 0)) :
    ComputableInO f encSymAndInstance encOut
      (fun x => (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ c) * (x.n + 1) ^ c)
      (fun x => (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ c) * (x.n + 1) ^ c) :=
  h.weaken
    (BigOLe.of_le fun _ => by simp only [symBox, Nat.zero_add, Nat.mul_one, le_rfl])
    (BigOLe.of_le fun _ => by simp only [symBox, Nat.zero_add, Nat.mul_one, le_rfl])

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

private theorem pow_encNat_add_le (n d : ℕ) :
    ((encNat n).length + (2 * n + 8) + 1) ^ d ≤ 10 ^ d * (n + 1) ^ d := by
  have hlen_n := encNat_length_le_succ n
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
  let D_t := max d_masks d_map + 3
  have hright : ComputableInO (fun x : SymAndInstance => (allMasks x.n).map (·, true))
      encSymAndInstance (encList (encPair encBits encBool))
      (fun x => (encSymAndInstance x).length + 2 ^ x.n * (x.n + 1) ^ D_t)
      (fun x => (encSymAndInstance x).length + 2 ^ x.n * (x.n + 1) ^ D_t) := by
    have hweak (x : SymAndInstance) :
        (encSymAndInstance x).length + 2 ^ x.n * (x.n + 1) ^ d_masks +
          ((encList encBits (allMasks x.n)).length + ((allMasks x.n).length + 1) *
            (listMax (fun bs : List Bool => (encBits bs).length) (allMasks x.n) + 1) ^ d_map) ≤
        8 * ((encSymAndInstance x).length + 2 ^ x.n * (x.n + 1) ^ D_t + 1) := by
      have hlen_m : ∀ bs ∈ allMasks x.n, bs.length = x.n := fun bs hbs => by
        rw [allMasks_eq, List.mem_map] at hbs
        obtain ⟨k, _, rfl⟩ := hbs
        exact length_maskBits x.n k
      have hlist_le : (encList encBits (allMasks x.n)).length ≤ 2 ^ x.n * (2 * x.n + 1) :=
        (length_encList_le encBits _ (b := x.n) fun bs hbs => by
          simpa [encBits_apply] using (hlen_m bs hbs).le).trans (by rw [length_allMasks])
      have hmax : listMax (fun bs : List Bool => (encBits bs).length) (allMasks x.n) ≤ x.n :=
        listMax_le fun bs hbs => by simpa using (hlen_m bs hbs).le
      have hp1 : (x.n + 1) ^ d_masks ≤ (x.n + 1) ^ D_t :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (by dsimp only [D_t]; omega)
      have hp2 : (listMax (fun bs : List Bool => (encBits bs).length) (allMasks x.n) + 1) ^
          d_map ≤ (x.n + 1) ^ D_t :=
        (Nat.pow_le_pow_left (by omega) d_map).trans
          (Nat.pow_le_pow_right (Nat.succ_pos _) (by dsimp only [D_t]; omega))
      have h6 : 1 ≤ 2 ^ x.n := Nat.one_le_pow _ _ (by decide)
      have hmul1 : 2 ^ x.n * (2 * x.n + 1) ≤ 2 * (2 ^ x.n * (x.n + 1) ^ D_t) := by
        have h : 2 * x.n + 1 ≤ 2 * (x.n + 1) ^ D_t := by
          have : (x.n + 1) ≤ (x.n + 1) ^ D_t :=
            Nat.le_self_pow (Nat.ne_of_gt (by dsimp only [D_t]; omega)) _
          omega
        exact (Nat.mul_le_mul_left _ h).trans (by ring_nf; rfl)
      have hmul2 : ((allMasks x.n).length + 1) *
            (listMax (fun bs : List Bool => (encBits bs).length) (allMasks x.n) + 1) ^ d_map ≤
          2 * (2 ^ x.n * (x.n + 1) ^ D_t) := by
        rw [length_allMasks]
        calc (2 ^ x.n + 1) * _ ≤ (2 * 2 ^ x.n) * (x.n + 1) ^ D_t := Nat.mul_le_mul (by omega) hp2
          _ = 2 * (2 ^ x.n * (x.n + 1) ^ D_t) := by ring
      have hmul0 := Nat.mul_le_mul_left (2 ^ x.n) hp1
      omega
    exact (hmap_pair.comp hmasks).weaken ⟨8, fun x => hweak x⟩ ⟨8, fun x => hweak x⟩
  have htagged : ComputableInO taggedMasks encSymAndInstance (encList (encPair encBits encBool))
      (fun x => 2 ^ x.n * (x.n + 1) ^ D_t + ((encSymAndInstance x).length + 1) ^ (d₁ + 1))
      (fun x => 2 ^ x.n * (x.n + 1) ^ D_t + ((encSymAndInstance x).length + 1) ^ (d₁ + 1)) := by
    have happ := (ComputableInO.of_linear
      (ComputableInDegree.listAppend (encPair encBits encBool))).comp_linear (hleft.prod hright)
    have hle (x : SymAndInstance) :
        ((encSymAndInstance x).length + 1) ^ d₁ +
          ((encSymAndInstance x).length + 2 ^ x.n * (x.n + 1) ^ D_t) ≤
        4 * (2 ^ x.n * (x.n + 1) ^ D_t + ((encSymAndInstance x).length + 1) ^ (d₁ + 1) + 1) := by
      have h1 : (encSymAndInstance x).length ≤ ((encSymAndInstance x).length + 1) ^ (d₁ + 1) :=
        (Nat.le_succ _).trans (Nat.le_self_pow (by omega) _)
      have h2 : ((encSymAndInstance x).length + 1) ^ d₁ ≤
          ((encSymAndInstance x).length + 1) ^ (d₁ + 1) :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
      omega
    exact happ.weaken ⟨4, fun x => hle x⟩ ⟨4, fun x => hle x⟩
  have hM : ∀ x : SymAndInstance, ∀ p ∈ taggedMasks x,
      (encPair encBits encBool p).length ≤ 2 * x.n + 8 := fun x p hp => by
    have hp1 := fst_length_mem_taggedMasks hp
    have hp2 := encBool_length_le_two p.2
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
  let c_s := max D_t (d₁ + 1) + d_sort + 2
  have hwrap0 : ComputableInO (fun x : SymAndInstance => (0, radixSortLSB x.n (taggedMasks x)))
      encSymAndInstance (encPair encNat (encList (encPair encBits encBool)))
      (symBox c_s fun _ => 0) (symBox c_s fun _ => 0) := by
    have hp :=
      (ComputableInO.constZero (encIn := encSymAndInstance) (encMid := encNat) 0).prod hsort
    refine hp.weaken ⟨10 ^ d_sort + 8, fun x => ?_⟩ ⟨10 ^ d_sort + 16, fun x => ?_⟩
    · dsimp only
      have hx := enc_le_symBox (c := c_s) (by dsimp only [c_s]; omega) (fun _ => 0) x
      have hA1 := A_pow_le_symBox (by dsimp only [c_s]; omega : d₁ + 1 ≤ c_s) (fun _ => 0) x
      have hDt := two_pow_mul_n_le_symBox (by dsimp only [c_s]; omega : D_t ≤ c_s) (fun _ => 0) x
      have hlen_t : (taggedMasks x).length + 1 ≤ 2 ^ x.n + ((encSymAndInstance x).length + 1) := by
        have hg := gates_length_le_encSymAndInstance x
        simp only [taggedMasks, normGates, List.length_append, List.length_map, length_allMasks]
        omega
      have hbox_t : (2 ^ x.n + ((encSymAndInstance x).length + 1)) * (x.n + 1) ^ (d_sort + 1) ≤
          symBox c_s (fun _ => 0) x :=
        Nat.mul_le_mul (Nat.add_le_add_left
          ((Nat.le_self_pow (n := c_s) (by dsimp only [c_s]; omega) _).trans
            (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))) _)
          (Nat.pow_le_pow_right (Nat.succ_pos _) (by dsimp only [c_s]; omega))
      have hmul_N : (x.n + 1) * (((taggedMasks x).length + 1) *
            ((encNat x.n).length + (2 * x.n + 8) + 1) ^ d_sort + 1) ≤
          10 ^ d_sort * symBox c_s (fun _ => 0) x + symBox c_s (fun _ => 0) x := by
        have h1 : ((taggedMasks x).length + 1) *
              ((encNat x.n).length + (2 * x.n + 8) + 1) ^ d_sort ≤
            10 ^ d_sort *
              ((2 ^ x.n + ((encSymAndInstance x).length + 1)) * (x.n + 1) ^ d_sort) := by
          calc _ ≤ (2 ^ x.n + ((encSymAndInstance x).length + 1)) *
                  (10 ^ d_sort * (x.n + 1) ^ d_sort) :=
                Nat.mul_le_mul hlen_t (pow_encNat_add_le x.n d_sort)
            _ = _ := by ring
        have h2 : (x.n + 1) * (((taggedMasks x).length + 1) *
              ((encNat x.n).length + (2 * x.n + 8) + 1) ^ d_sort) ≤
            10 ^ d_sort * symBox c_s (fun _ => 0) x := by
          calc _ ≤ (x.n + 1) * (10 ^ d_sort *
                  ((2 ^ x.n + ((encSymAndInstance x).length + 1)) * (x.n + 1) ^ d_sort)) :=
                Nat.mul_le_mul_left _ h1
            _ = 10 ^ d_sort * ((2 ^ x.n + ((encSymAndInstance x).length + 1)) *
                  (x.n + 1) ^ (d_sort + 1)) := by rw [pow_succ']; ring
            _ ≤ 10 ^ d_sort * symBox c_s (fun _ => 0) x := Nat.mul_le_mul_left _ hbox_t
        have hN1 := n_pow_le_symBox (by dsimp only [c_s]; omega : 1 ≤ c_s) (fun _ => 0) x
        rw [pow_one] at hN1
        rw [Nat.mul_add, Nat.mul_one]
        omega
      calc _ ≤ symBox c_s (fun _ => 0) x + (symBox c_s (fun _ => 0) x +
              symBox c_s (fun _ => 0) x + (symBox c_s (fun _ => 0) x + symBox c_s (fun _ => 0) x) +
              (10 ^ d_sort * symBox c_s (fun _ => 0) x + symBox c_s (fun _ => 0) x)) := by omega
        _ = (10 ^ d_sort + 6) * symBox c_s (fun _ => 0) x := by ring
        _ ≤ (10 ^ d_sort + 8) * (symBox c_s (fun _ => 0) x + 1) :=
            Nat.mul_le_mul (by omega) (Nat.le_succ _)
    · dsimp only
      have hx := enc_le_symBox (c := c_s) (by dsimp only [c_s]; omega) (fun _ => 0) x
      have hA1 := A_pow_le_symBox (by dsimp only [c_s]; omega : d₁ + 1 ≤ c_s) (fun _ => 0) x
      have hDt := two_pow_mul_n_le_symBox (by dsimp only [c_s]; omega : D_t ≤ c_s) (fun _ => 0) x
      have hN1 := n_pow_le_symBox (by dsimp only [c_s]; omega : 1 ≤ c_s) (fun _ => 0) x
      have hNds := n_pow_le_symBox (by dsimp only [c_s]; omega : d_sort ≤ c_s) (fun _ => 0) x
      have hlen_t : (taggedMasks x).length + 1 ≤ 2 ^ x.n + ((encSymAndInstance x).length + 1) := by
        have hg := gates_length_le_encSymAndInstance x
        simp only [taggedMasks, normGates, List.length_append, List.length_map, length_allMasks]
        omega
      have hA_pow := Nat.le_self_pow (by dsimp only [c_s]; omega : c_s ≠ 0)
        ((encSymAndInstance x).length + 1)
      have htm : ((taggedMasks x).length + 1) * (2 * x.n + 8 + 1) ≤
          9 * symBox c_s (fun _ => 0) x := by
        rw [pow_one] at hN1
        have hN_pow := Nat.le_self_pow (by dsimp only [c_s]; omega : c_s ≠ 0) (x.n + 1)
        calc _ ≤ (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ c_s) * (9 * (x.n + 1) ^ c_s) :=
              Nat.mul_le_mul (by omega)
                ((by omega : 2 * x.n + 8 + 1 ≤ 9 * (x.n + 1)).trans (Nat.mul_le_mul_left 9 hN_pow))
          _ = 9 * symBox c_s (fun _ => 0) x := by
              simp only [symBox, Nat.zero_add, Nat.mul_one]; ring
      have hp_sort := (pow_encNat_add_le x.n d_sort).trans (Nat.mul_le_mul_left _ hNds)
      calc _ ≤ 0 + (symBox c_s (fun _ => 0) x + (symBox c_s (fun _ => 0) x +
              symBox c_s (fun _ => 0) x) + 9 * symBox c_s (fun _ => 0) x +
              10 ^ d_sort * symBox c_s (fun _ => 0) x) := by omega
        _ = (10 ^ d_sort + 12) * symBox c_s (fun _ => 0) x := by ring
        _ ≤ (10 ^ d_sort + 16) * (symBox c_s (fun _ => 0) x + 1) :=
            Nat.mul_le_mul (by omega) (Nat.le_succ _)
  obtain ⟨c_w, hwrap0_len⟩ := hwrap0.length_le
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
  obtain ⟨d_fold, hfold⟩ := computableInO_streamFold (encA := encPair encBits encBool)
    (encS := encNat) (encB := encNat) Prod.fst Prod.snd (fun _ => rfl) hnext hemit
    (g := fun q : ℕ × List (List Bool × Bool) => countEmitted q.1 q.2)
    (fun q => countEmitted_streamEmit q.1 q.2)
    (lMax := fun q => Nat.log2 (q.1 + q.2.length + 1) +
      2 * listMax (fun p : List Bool × Bool => p.1.length) q.2 + 8)
    (B := fun q => (q.2.length + 1) * (Nat.log2 (q.1 + q.2.length + 1) + 2))
    (fun q j _ => by
      have hst := streamState_count_le q.1 q.2 j
      have hlen := length_encNat_le_log2 (hst.trans (Nat.le_add_right (q.1 + q.2.length) 1))
      change (encNat (streamState q.1 _ q.2 j)).length ≤ _
      omega)
    (fun q j hj => by
      have hm := le_listMax (f := fun p : List Bool × Bool => p.1.length) (List.getElem_mem hj)
      have h2 := encBool_length_le_two q.2[j].2
      rw [length_encPair, encBits_apply]
      omega)
    ⟨3, fun q => by
      obtain ⟨hlen_ce, hmem_ce⟩ := hcountEmitted_bounds q.1 q.2
      have hce := length_encList_le encNat (countEmitted q.1 q.2)
        (b := Nat.log2 (q.1 + q.2.length + 1) + 1) fun v hv =>
          length_encNat_le_log2 ((hmem_ce v hv).trans (Nat.le_succ _))
      calc (encList encNat (countEmitted q.1 q.2)).length
          ≤ (q.2.length + 1) * (3 * (Nat.log2 (q.1 + q.2.length + 1) + 2)) :=
            hce.trans (Nat.mul_le_mul (hlen_ce.trans (Nat.le_succ _)) (by omega))
        _ ≤ 3 * ((q.2.length + 1) * (Nat.log2 (q.1 + q.2.length + 1) + 2) + 1) := by
            ring_nf; omega⟩
  let D_f := max d_fold 1
  let C_fin := c_s + 2 * D_f + 4
  have hmain_le : ∀ x : SymAndInstance,
      let L := radixSortLSB x.n (taggedMasks x)
      (0 + L.length + 1) * (Nat.log2 (0 + L.length + 1) +
        2 * listMax (fun p : List Bool × Bool => p.1.length) L + 8 + 1) ^ D_f ≤
        30 ^ (D_f + 1) * symBox C_fin (fun _ => 0) x := fun x => by
    set L := radixSortLSB x.n (taggedMasks x)
    set A := (encSymAndInstance x).length + 1
    have hlen_l : L.length = x.gates.length + 2 ^ x.n := hlen_sort x
    have hg_le := gates_length_le_encSymAndInstance x
    have hlog_q : Nat.log2 (0 + L.length + 1) ≤ x.n + Nat.log2 A + 1 := by
      have hlt : 0 + L.length + 1 < 2 ^ (x.n + Nat.log2 A + 2) := by
        have h2 : A + 1 < 2 ^ (Nat.log2 (A + 1) + 1) := by
          rw [Nat.log2_eq_log_two]; exact Nat.lt_pow_succ_log_self (by decide : 1 < 2) (A + 1)
        have hA2 : Nat.log2 (A + 1) ≤ Nat.log2 A + 1 := by
          have := log2_mono (by omega : A + 1 ≤ 2 * A)
          rw [Nat.log2_two_mul (by omega)] at this; omega
        have h1 : 1 ≤ 2 ^ x.n := Nat.one_le_pow _ _ (by decide)
        have hga : x.gates.length + 1 ≤ 2 ^ x.n * A :=
          (by omega : x.gates.length + 1 ≤ A).trans (Nat.le_mul_of_pos_left _ h1)
        calc 0 + L.length + 1 ≤ 2 ^ x.n * (A + 1) := by rw [hlen_l]; nlinarith
          _ < 2 ^ x.n * 2 ^ (Nat.log2 (A + 1) + 1) :=
              Nat.mul_lt_mul_of_pos_left h2 (Nat.two_pow_pos _)
          _ = 2 ^ (x.n + (Nat.log2 (A + 1) + 1)) := by rw [← pow_add]
          _ ≤ 2 ^ (x.n + Nat.log2 A + 2) := Nat.pow_le_pow_right (by decide) (by omega)
      by_contra hgt; push Not at hgt
      have hle := Nat.pow_le_pow_right (by decide : 1 ≤ 2)
        (by omega : x.n + Nat.log2 A + 2 ≤ Nat.log2 (0 + L.length + 1))
      have hself := Nat.log2_self_le (by omega : 0 + L.length + 1 ≠ 0)
      omega
    have hmax_p : listMax (fun p : List Bool × Bool => p.1.length) L ≤ x.n :=
      listMax_le fun p hp => (fst_length_mem_taggedMasks (hmem_sort x p hp)).le
    have hbase : Nat.log2 (0 + L.length + 1) +
        2 * listMax (fun p : List Bool × Bool => p.1.length) L + 8 + 1 ≤
        5 * (x.n + 1) * (Nat.log2 A + 2) := by
      have h1 : x.n * 2 ≤ x.n * (Nat.log2 A + 2) := Nat.mul_le_mul_left x.n (by omega)
      nlinarith
    have hpow_b : (Nat.log2 (0 + L.length + 1) +
        2 * listMax (fun p : List Bool × Bool => p.1.length) L + 8 + 1) ^ D_f ≤
        5 ^ D_f * (x.n + 1) ^ D_f * (Nat.log2 A + 2) ^ D_f := by
      calc _ ≤ (5 * (x.n + 1) * (Nat.log2 A + 2)) ^ D_f := Nat.pow_le_pow_left hbase D_f
        _ = 5 ^ D_f * (x.n + 1) ^ D_f * (Nat.log2 A + 2) ^ D_f := by rw [Nat.mul_pow, Nat.mul_pow]
    have hlog := symBox_log_le (r := D_f) (k := D_f) (c := C_fin) (by dsimp only [C_fin]; omega)
      (by dsimp only [C_fin]; omega) (fun _ => 0) x
    have hc30 : 5 ^ D_f * (2 * 3 ^ (D_f + 1) * 2 ^ D_f) ≤ 30 ^ (D_f + 1) := by
      have h1 : 5 ^ D_f * (2 * 3 ^ (D_f + 1) * 2 ^ D_f) =
          6 * (5 ^ D_f * 2 ^ D_f * 3 ^ D_f) := by ring
      rw [← Nat.mul_pow, ← Nat.mul_pow, show 5 * 2 * 3 = 30 from rfl] at h1
      have h2 : 30 ^ (D_f + 1) = 30 * 30 ^ D_f := by ring
      omega
    calc (0 + L.length + 1) * (Nat.log2 (0 + L.length + 1) +
          2 * listMax (fun p : List Bool × Bool => p.1.length) L + 8 + 1) ^ D_f
        ≤ (2 ^ x.n + A) * (5 ^ D_f * (x.n + 1) ^ D_f * (Nat.log2 A + 2) ^ D_f) :=
          Nat.mul_le_mul (by rw [hlen_l]; omega) hpow_b
      _ = 5 ^ D_f * ((2 ^ x.n + A) * (x.n + 1) ^ D_f * (Nat.log2 A + 2) ^ D_f) := by ring
      _ ≤ 5 ^ D_f * (2 * 3 ^ (D_f + 1) * 2 ^ D_f * symBox C_fin (fun _ => 0) x) :=
          Nat.mul_le_mul_left _ hlog
      _ = (5 ^ D_f * (2 * 3 ^ (D_f + 1) * 2 ^ D_f)) * symBox C_fin (fun _ => 0) x := by ring
      _ ≤ 30 ^ (D_f + 1) * symBox C_fin (fun _ => 0) x := Nat.mul_le_mul_right _ hc30
  have hcomp := hfold.comp hwrap0
  refine ⟨C_fin, symBox_zero_weaken (hcomp.weaken ⟨c_w + 30 ^ (D_f + 1) + 4, fun x => ?_⟩
      ⟨2 * 30 ^ (D_f + 1) + 2, fun x => ?_⟩)⟩
  · dsimp only
    have hpow_df : (Nat.log2 (0 + (radixSortLSB x.n (taggedMasks x)).length + 1) +
          2 * listMax (fun p : List Bool × Bool => p.1.length)
            (radixSortLSB x.n (taggedMasks x)) + 8 + 1) ^ d_fold ≤
        (Nat.log2 (0 + (radixSortLSB x.n (taggedMasks x)).length + 1) +
          2 * listMax (fun p : List Bool × Bool => p.1.length)
            (radixSortLSB x.n (taggedMasks x)) + 8 + 1) ^ D_f :=
      Nat.pow_le_pow_right (by omega) (le_max_left _ _)
    have hmul := Nat.mul_le_mul_left (0 + (radixSortLSB x.n (taggedMasks x)).length + 1) hpow_df
    have hml := hmul.trans (hmain_le x)
    conv at hml => lhs; lhs; rw [Nat.zero_add]
    have hbox := symBox_mono (by dsimp only [C_fin]; omega : c_s ≤ C_fin) (fun _ => le_rfl) x
      (F₁ := fun _ => 0) (F₂ := fun _ => 0)
    have hlen_w : (encPair encNat (encList (encPair encBits encBool))
        (0, radixSortLSB x.n (taggedMasks x))).length ≤ c_w * (symBox C_fin (fun _ => 0) x + 1) :=
      (hwrap0_len x).trans (Nat.mul_le_mul_left _ (by omega))
    have h1 : symBox C_fin (fun _ => 0) x ≤ symBox C_fin (fun _ => 0) x + 1 := Nat.le_succ _
    have h30 : 30 ^ (D_f + 1) * symBox C_fin (fun _ => 0) x ≤
        30 ^ (D_f + 1) * (symBox C_fin (fun _ => 0) x + 1) := Nat.mul_le_mul_left _ h1
    calc _ ≤ (symBox C_fin (fun _ => 0) x + 1) + c_w * (symBox C_fin (fun _ => 0) x + 1) +
          30 ^ (D_f + 1) * (symBox C_fin (fun _ => 0) x + 1) := by omega
      _ = (c_w + 30 ^ (D_f + 1) + 1) * (symBox C_fin (fun _ => 0) x + 1) := by ring
      _ ≤ (c_w + 30 ^ (D_f + 1) + 4) * (symBox C_fin (fun _ => 0) x + 1) :=
          Nat.mul_le_mul_right _ (by omega)
  · dsimp only
    have hpow_df : (Nat.log2 (0 + (radixSortLSB x.n (taggedMasks x)).length + 1) +
          2 * listMax (fun p : List Bool × Bool => p.1.length)
            (radixSortLSB x.n (taggedMasks x)) + 8 + 1) ^ d_fold ≤
        (Nat.log2 (0 + (radixSortLSB x.n (taggedMasks x)).length + 1) +
          2 * listMax (fun p : List Bool × Bool => p.1.length)
            (radixSortLSB x.n (taggedMasks x)) + 8 + 1) ^ D_f :=
      Nat.pow_le_pow_right (by omega) (le_max_left _ _)
    have h1 := (hpow_df.trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))).trans (hmain_le x)
    have h2 : ((radixSortLSB x.n (taggedMasks x)).length + 1) *
        (Nat.log2 (0 + (radixSortLSB x.n (taggedMasks x)).length + 1) + 2) ≤
        30 ^ (D_f + 1) * symBox C_fin (fun _ => 0) x := by
      have hp : Nat.log2 (0 + (radixSortLSB x.n (taggedMasks x)).length + 1) + 2 ≤
          (Nat.log2 (0 + (radixSortLSB x.n (taggedMasks x)).length + 1) +
            2 * listMax (fun p : List Bool × Bool => p.1.length)
              (radixSortLSB x.n (taggedMasks x)) + 8 + 1) ^ D_f :=
        (by omega : _ ≤ _ + 8 + 1).trans (Nat.le_self_pow (by dsimp only [D_f]; omega) _)
      exact (Nat.mul_le_mul (by omega) hp).trans (hmain_le x)
    have hbox := symBox_mono (by dsimp only [C_fin]; omega : c_s ≤ C_fin) (fun _ => le_rfl) x
      (F₁ := fun _ => 0) (F₂ := fun _ => 0)
    calc _ ≤ symBox C_fin (fun _ => 0) x + 2 * (30 ^ (D_f + 1) * symBox C_fin (fun _ => 0) x) := by
          omega
      _ ≤ (2 * 30 ^ (D_f + 1) + 2) * (symBox C_fin (fun _ => 0) x + 1) := by
          have : 1 ≤ 30 ^ (D_f + 1) := Nat.one_le_pow _ _ (by decide)
          nlinarith

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

private theorem yatesPred_congr_other {n i k' k : ℕ} {T : Finset (Fin n)}
    (hother : ∀ j : Fin n, j.1 ≠ i → (j ∈ rotMaskSet n i k' ↔ j ∈ rotMaskSet n (i + 1) k))
    (h : yatesPred n i k' T) {j : Fin n} (hj : j.1 ≠ i) :
    if j.1 < i + 1 then (j ∈ T → j ∈ rotMaskSet n (i + 1) k)
    else (j ∈ T ↔ j ∈ rotMaskSet n (i + 1) k) := by
  have hlt_eq : (j.1 < i + 1) ↔ (j.1 < i) := by omega
  have hro := hother j hj
  have hj0 := h j
  split_ifs at hj0 ⊢ with h1 h2
  · exact fun hm => hro.1 (hj0 hm)
  · omega
  · omega
  · exact hj0.trans hro

private theorem yatesPred_of_succ_other {n i k' k : ℕ} {T : Finset (Fin n)}
    (hother : ∀ j : Fin n, j.1 ≠ i → (j ∈ rotMaskSet n i k' ↔ j ∈ rotMaskSet n (i + 1) k))
    (h : yatesPred n (i + 1) k T) {j : Fin n} (hj : j.1 ≠ i) :
    if j.1 < i then (j ∈ T → j ∈ rotMaskSet n i k')
    else (j ∈ T ↔ j ∈ rotMaskSet n i k') := by
  have hlt_eq : (j.1 < i + 1) ↔ (j.1 < i) := by omega
  have hro := hother j hj
  have hj1 := h j
  split_ifs at hj1 ⊢ with h1 h2
  · exact fun hm => hro.2 (hj1 hm)
  · omega
  · omega
  · exact hj1.trans hro.symm

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
        exact absurd (Nat.testBit_lt_two_pow hlt) (by rw [hbit]; decide)
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
          · exact yatesPred_congr_other (fun j hj => (hrot_other j hj).1) h hj
        · rintro ⟨h, hni⟩ j
          by_cases hj : j.1 = i
          · have hjf : j = ⟨i, hi_lt⟩ := Fin.ext hj
            subst hjf
            simp [hrot_i0, hni]
          · exact yatesPred_of_succ_other (fun j hj => (hrot_other j hj).1) h hj
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
          · exact yatesPred_congr_other (fun j hj => (hrot_other j hj).2) h hj
        · rintro ⟨h, hmem⟩ j
          by_cases hj : j.1 = i
          · have hjf : j = ⟨i, hi_lt⟩ := Fin.ext hj
            subst hjf
            simp [hrot_i1, hmem]
          · exact yatesPred_of_succ_other (fun j hj => (hrot_other j hj).2) h hj
      by_cases hP : yatesPred n (i + 1) k T <;> by_cases hmem : (⟨i, hi_lt⟩ : Fin n) ∈ T <;>
        simp [hP, hmem, hiff0, hiff1]
    · have hf_bit : k.testBit (n - 1) = false := Bool.eq_false_iff.2 hbit
      have hk_lt_half : k < 2 ^ (n - 1) := by
        by_contra hge
        push Not at hge
        have hdiv : k / 2 ^ (n - 1) = 1 := by
          have h1 : k = 2 ^ (n - 1) + (k - 2 ^ (n - 1)) := by omega
          rw [h1, Nat.add_div_left _ (Nat.two_pow_pos _), Nat.div_eq_of_lt (by omega)]
        exact absurd (by simp [Nat.testBit_eq_decide_div_mod_eq, hdiv] :
          k.testBit (n - 1) = true) hbit
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
          · subst hj
            have hj0 := h ⟨j.1, hi_lt⟩
            simp only [lt_irrefl, ↓reduceIte, hrot_i0, iff_false] at hj0
            simp [hrot_i_next, hf_bit, hj0, show j.1 < j.1 + 1 by omega]
          · exact yatesPred_congr_other (fun j hj => (hrot_other j hj).1) h hj
        · intro h j
          by_cases hj : j.1 = i
          · subst hj
            have hj1 := h ⟨j.1, hi_lt⟩
            simp only [show j.1 < j.1 + 1 by omega, ↓reduceIte, hrot_i_next, hf_bit,
              Bool.false_eq_true, imp_false] at hj1
            simp [hrot_i0, hj1]
          · exact yatesPred_of_succ_other (fun j hj => (hrot_other j hj).1) h hj
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
  have hlen_ev : ∀ L : List ℕ, (encList encNat (evens L)).length ≤ (encList encNat L).length := by
    intro L
    induction L using list_two_step_ind with
    | h0 => simp [evens]
    | h1 a => simp [evens]
    | h2 a b rest ih => simp only [evens, encList_cons, List.length_append]; omega
  obtain ⟨d_ev, hev_sf⟩ := computableInO_streamFold (encA := encNat) (encS := encBool)
    (encB := encNat) Prod.fst Prod.snd (fun _ => rfl) hnext_ev hemit_ev
    (g := fun q : Bool × List ℕ =>
      if q.1 then evens q.2 else match q.2 with | [] => [] | _ :: rest => evens rest)
    (fun q => evens_streamEmit q.1 q.2)
    (lMax := fun q => listMax (fun v => (encNat v).length) q.2 + 2)
    (B := fun q => (encList encNat q.2).length)
    (fun q j _ => (encBool_length_le_two _).trans (Nat.le_add_left _ _))
    (fun q j hj => (le_listMax (f := fun v => (encNat v).length) (List.getElem_mem hj)).trans
      (by omega))
    ⟨1, fun q => by
      have hlen_g : (encList encNat (if q.1 then evens q.2
            else match q.2 with | [] => [] | _ :: rest => evens rest)).length ≤
          (encList encNat q.2).length := by
        cases q.1
        · cases q.2 with
          | nil => simp
          | cons a t => simpa [encList_cons] using (hlen_ev t).trans (Nat.le_add_left _ _)
        · exact hlen_ev q.2
      exact hlen_g.trans (by omega)⟩
  have hev : ComputableInO evens (encList encNat) (encList encNat)
      (fun L => (encList encNat L).length +
        (L.length + 1) * (listMax (fun v => (encNat v).length) L + 1) ^ d_ev)
      (fun L => (encList encNat L).length +
        (listMax (fun v => (encNat v).length) L + 1) ^ d_ev) := by
    refine (hev_sf.comp (computableInO_pair_const_id true)).weaken
      ⟨3 ^ d_ev + 5, fun L => ?_⟩ ⟨3 ^ d_ev + 2, fun L => ?_⟩
    · dsimp only
      rw [length_encPair]
      dsimp only
      have hb := encBool_length_le_two true
      have hpow : (listMax (fun v => (encNat v).length) L + 2 + 1) ^ d_ev ≤
          3 ^ d_ev * (listMax (fun v => (encNat v).length) L + 1) ^ d_ev :=
        pow_shift_le (k := 3) (by decide) le_rfl
      have hmul : (L.length + 1) * (listMax (fun v => (encNat v).length) L + 2 + 1) ^ d_ev ≤
          3 ^ d_ev * ((L.length + 1) * (listMax (fun v => (encNat v).length) L + 1) ^ d_ev) := by
        calc _ ≤ (L.length + 1) *
              (3 ^ d_ev * (listMax (fun v => (encNat v).length) L + 1) ^ d_ev) :=
              Nat.mul_le_mul_left _ hpow
          _ = _ := by ring
      have h1 : (L.length + 1) * (listMax (fun v => (encNat v).length) L + 1) ^ d_ev ≤
          (encList encNat L).length +
            (L.length + 1) * (listMax (fun v => (encNat v).length) L + 1) ^ d_ev + 1 := by
        omega
      have hmul3 := Nat.mul_le_mul_left (3 ^ d_ev) h1
      have hlin : 2 * (encList encNat L).length + 2 * (encBool true).length + 1 ≤
          5 * ((encList encNat L).length +
            (L.length + 1) * (listMax (fun v => (encNat v).length) L + 1) ^ d_ev + 1) := by
        omega
      calc _ ≤ (2 * (encList encNat L).length + 2 * (encBool true).length + 1) +
            3 ^ d_ev * ((L.length + 1) *
              (listMax (fun v => (encNat v).length) L + 1) ^ d_ev) := by omega
        _ ≤ 5 * _ + 3 ^ d_ev * _ := Nat.add_le_add hlin hmul3
        _ = (3 ^ d_ev + 5) * _ := by ring
    · dsimp only
      have hpow : (listMax (fun v => (encNat v).length) L + 2 + 1) ^ d_ev ≤
          3 ^ d_ev * (listMax (fun v => (encNat v).length) L + 1) ^ d_ev :=
        pow_shift_le (k := 3) (by decide) le_rfl
      have h1 : (listMax (fun v => (encNat v).length) L + 1) ^ d_ev ≤
          (encList encNat L).length +
            (listMax (fun v => (encNat v).length) L + 1) ^ d_ev + 1 := by
        omega
      have hmul3 := Nat.mul_le_mul_left (3 ^ d_ev) h1
      have hlin : 2 * (encList encNat L).length ≤
          2 * ((encList encNat L).length +
            (listMax (fun v => (encNat v).length) L + 1) ^ d_ev + 1) := by
        omega
      calc _ ≤ 2 * (encList encNat L).length +
            3 ^ d_ev * (listMax (fun v => (encNat v).length) L + 1) ^ d_ev := by omega
        _ ≤ 2 * _ + 3 ^ d_ev * _ := Nat.add_le_add hlin hmul3
        _ = (3 ^ d_ev + 2) * _ := by ring
  have hnext_po : ComputableInPolyTime
      (fun q : (Bool × ℕ) × ℕ => if q.1.1 then (false, 0) else (true, q.2))
      (encPair (encPair encBool encNat) encNat) (encPair encBool encNat) := by fun_prop
  have hemit_po : ComputableInPolyTime
      (fun q : (Bool × ℕ) × ℕ => if q.1.1 then [q.1.2 + q.2] else [])
      (encPair (encPair encBool encNat) encNat) (encList encNat) := by fun_prop
  have hadd_len : ∀ a b : ℕ, (encNat (a + b)).length ≤ (encNat a).length + (encNat b).length + 1 :=
    fun a b => by
      rw [encNat_apply, encNat_apply, encNat_apply, Nat.size_eq_bits_len, Nat.size_eq_bits_len,
        Nat.size_eq_bits_len]
      have ha_lt : a < 2 ^ Nat.size a := Nat.size_le.1 le_rfl
      have hb_lt : b < 2 ^ Nat.size b := Nat.size_le.1 le_rfl
      have hsum_lt : a + b < 2 ^ (max (Nat.size a) (Nat.size b) + 1) := by
        have h1 : a < 2 ^ max (Nat.size a) (Nat.size b) :=
          ha_lt.trans_le (Nat.pow_le_pow_right (by decide) (le_max_left _ _))
        have h2 : b < 2 ^ max (Nat.size a) (Nat.size b) :=
          hb_lt.trans_le (Nat.pow_le_pow_right (by decide) (le_max_right _ _))
        rw [pow_succ']; omega
      exact (Nat.size_le.2 hsum_lt).trans (by omega)
  have hlen_po : ∀ L : List ℕ,
      (encList encNat (passOddsAdd L)).length ≤ (encList encNat L).length + 2 * L.length := by
    intro L
    induction L using list_two_step_ind with
    | h0 => simp [passOddsAdd]
    | h1 a => simp [passOddsAdd]
    | h2 a b rest ih =>
      have hab := hadd_len a b
      simp only [passOddsAdd, encList_cons, List.length_append, length_frame, List.length_cons]
      omega
  obtain ⟨d_po, hpo_sf⟩ := computableInO_streamFold (encA := encNat)
    (encS := encPair encBool encNat) (encB := encNat) Prod.fst Prod.snd (fun _ => rfl)
    hnext_po hemit_po
    (g := fun q : (Bool × ℕ) × List ℕ =>
      if q.1.1 then match q.2 with | [] => [] | y :: rest => (q.1.2 + y) :: passOddsAdd rest
      else passOddsAdd q.2)
    (fun q => by
      rcases q with ⟨⟨b, prev⟩, L⟩
      cases b with
      | false =>
        cases L with
        | nil => rfl
        | cons x t => simpa [streamEmit] using passOddsAdd_streamEmit (x :: t)
      | true =>
        cases L with
        | nil => rfl
        | cons y rest =>
          simp only [↓reduceIte, encList_cons, streamEmit, encList_nil, List.append_nil]
          rw [passOddsAdd_streamEmit])
    (lMax := fun q => (encNat q.1.2).length + listMax (fun v => (encNat v).length) q.2 + 8)
    (B := fun q => (encNat q.1.2).length + listMax (fun v => (encNat v).length) q.2 +
      (encList encNat q.2).length + 2 * q.2.length + 1)
    (fun q j _ => by
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
      have hb := encBool_length_le_two (streamState q.1 next_fn q.2 j).1
      have hn : (encNat (streamState q.1 next_fn q.2 j).2).length ≤
          (encNat q.1.2).length + listMax (fun v => (encNat v).length) q.2 := by
        rcases hst with h | h | ⟨v, hv, h⟩
        · rw [h]; omega
        · rw [h, encNat_apply, Nat.zero_bits]; simp
        · rw [h]
          exact (le_listMax (f := fun v => (encNat v).length) hv).trans (Nat.le_add_left _ _)
      change (encPair encBool encNat (streamState q.1 next_fn q.2 j)).length ≤ _
      rw [length_encPair]; omega)
    (fun q j hj => (le_listMax (f := fun v => (encNat v).length) (List.getElem_mem hj)).trans
      (by omega))
    ⟨3, fun q => by
      rcases q with ⟨⟨b, prev⟩, L⟩
      cases b
      · have h1 := hlen_po L
        dsimp only
        simp only [Bool.false_eq_true, ↓reduceIte]
        omega
      · cases L with
        | nil => simp
        | cons y rest =>
          have hy : (encNat y).length ≤ listMax (fun v => (encNat v).length) (y :: rest) :=
            le_listMax (f := fun v => (encNat v).length) (List.mem_cons_self ..)
          have had := hadd_len prev y
          have hr := hlen_po rest
          dsimp only
          simp only [↓reduceIte, encList_cons, List.length_append, length_frame, List.length_cons]
          omega⟩
  let D_po := max d_po 1
  have hpo : ComputableInO passOddsAdd (encList encNat) (encList encNat)
      (fun L => (encList encNat L).length +
        (L.length + 1) * (listMax (fun v => (encNat v).length) L + 1) ^ D_po)
      (fun L => (encList encNat L).length + L.length +
        (listMax (fun v => (encNat v).length) L + 1) ^ D_po) := by
    refine (hpo_sf.comp (computableInO_pair_const_id (false, (0 : ℕ)))).weaken
      ⟨9 ^ d_po + 12, fun L => ?_⟩ ⟨9 ^ d_po + 3, fun L => ?_⟩
    · dsimp only [D_po]
      rw [length_encPair]
      dsimp only
      have h0 : (encNat 0).length = 0 := by simp [encNat_apply]
      have hb0 : (encPair encBool encNat (false, 0)).length ≤ 5 := by
        rw [length_encPair, h0]; dsimp only; have := encBool_length_le_two false; omega
      rw [h0]
      have hpow : (0 + listMax (fun v => (encNat v).length) L + 8 + 1) ^ d_po ≤
          9 ^ d_po * (listMax (fun v => (encNat v).length) L + 1) ^ max d_po 1 := by
        rw [Nat.zero_add, Nat.add_assoc _ 8 1]
        exact pow_shift_le (k := 9) (by decide) (le_max_left _ _)
      have hmul : (L.length + 1) * (0 + listMax (fun v => (encNat v).length) L + 8 + 1) ^ d_po ≤
          9 ^ d_po *
            ((L.length + 1) * (listMax (fun v => (encNat v).length) L + 1) ^ max d_po 1) := by
        calc _ ≤ (L.length + 1) *
              (9 ^ d_po * (listMax (fun v => (encNat v).length) L + 1) ^ max d_po 1) :=
              Nat.mul_le_mul_left _ hpow
          _ = _ := by ring
      have h1 : (L.length + 1) * (listMax (fun v => (encNat v).length) L + 1) ^ max d_po 1 ≤
          (encList encNat L).length +
            (L.length + 1) * (listMax (fun v => (encNat v).length) L + 1) ^ max d_po 1 + 1 := by
        omega
      have hmul9 := Nat.mul_le_mul_left (9 ^ d_po) h1
      have hlin :
          2 * (encList encNat L).length + 2 * (encPair encBool encNat (false, 0)).length + 1 ≤
          12 * ((encList encNat L).length +
            (L.length + 1) * (listMax (fun v => (encNat v).length) L + 1) ^ max d_po 1 + 1) := by
        omega
      calc _ ≤ (2 * (encList encNat L).length +
              2 * (encPair encBool encNat (false, 0)).length + 1) +
            9 ^ d_po * ((L.length + 1) *
              (listMax (fun v => (encNat v).length) L + 1) ^ max d_po 1) := by omega
        _ ≤ 12 * _ + 9 ^ d_po * _ := Nat.add_le_add hlin hmul9
        _ = (9 ^ d_po + 12) * _ := by ring
    · dsimp only [D_po]
      have h0 : (encNat 0).length = 0 := by simp [encNat_apply]
      rw [h0]
      have hpow : (0 + listMax (fun v => (encNat v).length) L + 8 + 1) ^ d_po ≤
          9 ^ d_po * (listMax (fun v => (encNat v).length) L + 1) ^ max d_po 1 := by
        rw [Nat.zero_add, Nat.add_assoc _ 8 1]
        exact pow_shift_le (k := 9) (by decide) (le_max_left _ _)
      have h1 : (listMax (fun v => (encNat v).length) L + 1) ^ max d_po 1 ≤
          (encList encNat L).length + L.length +
            (listMax (fun v => (encNat v).length) L + 1) ^ max d_po 1 + 1 := by
        omega
      have hmul9 := Nat.mul_le_mul_left (9 ^ d_po) h1
      have hlin : 2 * (encList encNat L).length + 2 * L.length +
            listMax (fun v => (encNat v).length) L + 1 ≤
          3 * ((encList encNat L).length + L.length +
            (listMax (fun v => (encNat v).length) L + 1) ^ max d_po 1 + 1) := by
        have hp := Nat.le_self_pow (Nat.ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right d_po 1)))
          (listMax (fun v => (encNat v).length) L + 1)
        omega
      calc _ ≤ (2 * (encList encNat L).length + 2 * L.length +
              listMax (fun v => (encNat v).length) L + 1) +
            9 ^ d_po * (listMax (fun v => (encNat v).length) L + 1) ^ max d_po 1 := by omega
        _ ≤ 3 * _ + 9 ^ d_po * _ := Nat.add_le_add hlin hmul9
        _ = (9 ^ d_po + 3) * _ := by ring
  let D_st := max d_ev D_po
  have hyst : ComputableInO yatesStep (encList encNat) (encList encNat)
      (fun L => (encList encNat L).length +
        (L.length + 1) * (listMax (fun v => (encNat v).length) L + 1) ^ D_st)
      (fun L => (encList encNat L).length + L.length +
        (listMax (fun v => (encNat v).length) L + 1) ^ D_st) := by
    have happ := (ComputableInO.of_linear (ComputableInDegree.listAppend encNat)).comp_linear
      (hev.prod hpo)
    refine happ.weaken ⟨2, fun L => ?_⟩ ⟨2, fun L => ?_⟩ <;>
    · dsimp only
      have hp1 : (listMax (fun v => (encNat v).length) L + 1) ^ d_ev ≤
          (listMax (fun v => (encNat v).length) L + 1) ^ D_st :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_left _ _)
      have hp2 : (listMax (fun v => (encNat v).length) L + 1) ^ D_po ≤
          (listMax (fun v => (encNat v).length) L + 1) ^ D_st :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_right _ _)
      have hm1 := Nat.mul_le_mul_left (L.length + 1) hp1
      have hm2 := Nat.mul_le_mul_left (L.length + 1) hp2
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
      have hm : ∀ v ∈ yatesStep^[k] (countMasks x),
          (encNat v).length ≤ x.n + Nat.log2 ((encSymAndInstance x).length + 1) + 1 :=
        fun v hv => (le_listMax hv).trans (hmax_k x k hk)
      exact (length_encList_le encNat _ hm).trans (by rw [hlen])
  let R_y (x : SymAndInstance) :=
    2 * (2 ^ x.n * (2 * (x.n + Nat.log2 ((encSymAndInstance x).length + 1) + 1) + 1)) +
      (2 ^ x.n + 1) * (x.n + Nat.log2 ((encSymAndInstance x).length + 1) + 2) ^ D_st
  have hit := ComputableInO.iterate computableInO_n_nat hcm hyst
    (R := R_y) (Q := R_y)
    (B := fun x => 2 ^ x.n * (2 * (x.n + Nat.log2 ((encSymAndInstance x).length + 1) + 1) + 1))
    (fun x k hk => by
      have h1 := henc_k x k hk
      have h2 := length_yatesStep_iter_two_pow (countMasks_length x) hk
      have h3 := hmax_k x k hk
      have hp := Nat.pow_le_pow_left (by omega : listMax (fun v => (encNat v).length)
        (yatesStep^[k] (countMasks x)) + 1 ≤
        x.n + Nat.log2 ((encSymAndInstance x).length + 1) + 2) D_st
      have hm := Nat.mul_le_mul_left (2 ^ x.n + 1) hp
      dsimp only [R_y]; rw [h2]; omega)
    (fun x k hk => by
      have h1 := henc_k x k hk
      have h2 := length_yatesStep_iter_two_pow (countMasks_length x) hk
      have h3 := hmax_k x k hk
      have hp := (Nat.pow_le_pow_left (by omega : listMax (fun v => (encNat v).length)
        (yatesStep^[k] (countMasks x)) + 1 ≤
        x.n + Nat.log2 ((encSymAndInstance x).length + 1) + 2) D_st).trans
        (Nat.le_mul_of_pos_left _ (by omega : 0 < 2 ^ x.n + 1))
      have h2n_1 : 2 ^ x.n ≤
          2 ^ x.n * (2 * (x.n + Nat.log2 ((encSymAndInstance x).length + 1) + 1) + 1) :=
        Nat.le_mul_of_pos_right _ (by omega)
      dsimp only [R_y]; rw [h2]; omega)
    (fun x k hk => henc_k x k hk)
  let C_y := max c_cm (D_st + 2) + 2 * D_st + 4
  have hR_bound : ∀ (r : ℕ) (_hr : r ≤ 1) (x : SymAndInstance),
      (x.n + 1) ^ r * R_y x ≤ 18 ^ (D_st + 2) * symBox C_y (fun _ => 0) x :=
    fun r hr x => by
      set A := (encSymAndInstance x).length + 1
      have hbase : x.n + Nat.log2 A + 2 ≤ (x.n + 1) * (Nat.log2 A + 2) := by
        have h1 : x.n ≤ x.n * (Nat.log2 A + 2) := Nat.le_mul_of_pos_right _ (by omega)
        nlinarith
      have hpow_b : (x.n + Nat.log2 A + 2) ^ D_st ≤ (x.n + 1) ^ D_st * (Nat.log2 A + 2) ^ D_st :=
        (Nat.pow_le_pow_left hbase D_st).trans (by rw [Nat.mul_pow])
      have hlog := symBox_log_le (r := D_st + r) (k := D_st) (c := C_y)
        (by dsimp only [C_y]; omega) (by dsimp only [C_y]; omega) (fun _ => 0) x
      have hmul_b : (x.n + 1) ^ r * ((2 ^ x.n + 1) * (x.n + Nat.log2 A + 2) ^ D_st) ≤
          2 * 3 ^ (D_st + 1) * 2 ^ D_st * symBox C_y (fun _ => 0) x := by
        calc _ ≤ (x.n + 1) ^ r * ((2 ^ x.n + A) * ((x.n + 1) ^ D_st * (Nat.log2 A + 2) ^ D_st)) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) hpow_b)
          _ = (2 ^ x.n + A) * (x.n + 1) ^ (D_st + r) * (Nat.log2 A + 2) ^ D_st := by
              rw [pow_add]; ring
          _ ≤ 2 * 3 ^ (D_st + 1) * 2 ^ D_st * symBox C_y (fun _ => 0) x := hlog
      have hD1 : 1 ≤ D_st := by
        dsimp only [D_st, D_po]; exact le_trans (le_max_right _ _) (le_max_right _ _)
      have h2pow : 2 * (x.n + Nat.log2 A + 1) + 1 ≤ 2 * (x.n + Nat.log2 A + 2) ^ D_st := by
        have hle := Nat.le_self_pow (Nat.ne_of_gt hD1) (x.n + Nat.log2 A + 2)
        omega
      have hlin : 2 ^ x.n * (2 * (x.n + Nat.log2 A + 1) + 1) ≤
          2 * ((2 ^ x.n + 1) * (x.n + Nat.log2 A + 2) ^ D_st) := by
        calc _ ≤ (2 ^ x.n + 1) * (2 * (x.n + Nat.log2 A + 2) ^ D_st) :=
              Nat.mul_le_mul (by omega) h2pow
          _ = _ := by ring
      have h5 : R_y x ≤ 5 * ((2 ^ x.n + 1) * (x.n + Nat.log2 A + 2) ^ D_st) := by
        dsimp only [A, R_y] at hlin ⊢; omega
      have hc18 : 5 * (2 * 3 ^ (D_st + 1) * 2 ^ D_st) ≤ 18 ^ (D_st + 2) := by
        have h1 : 5 * (2 * 3 ^ (D_st + 1) * 2 ^ D_st) = 30 * (3 ^ D_st * 2 ^ D_st) := by ring
        rw [← Nat.mul_pow, show 3 * 2 = 6 from rfl] at h1
        have h2 : 6 ^ D_st ≤ 18 ^ D_st := Nat.pow_le_pow_left (by decide) D_st
        have h3 : 18 ^ (D_st + 2) = 324 * 18 ^ D_st := by ring
        omega
      calc (x.n + 1) ^ r * R_y x
          ≤ 5 * ((x.n + 1) ^ r * ((2 ^ x.n + 1) * (x.n + Nat.log2 A + 2) ^ D_st)) := by
            nlinarith [Nat.mul_le_mul_left ((x.n + 1) ^ r) h5]
        _ ≤ 5 * (2 * 3 ^ (D_st + 1) * 2 ^ D_st * symBox C_y (fun _ => 0) x) :=
            Nat.mul_le_mul_left 5 hmul_b
        _ = 5 * (2 * 3 ^ (D_st + 1) * 2 ^ D_st) * symBox C_y (fun _ => 0) x := by ring
        _ ≤ 18 ^ (D_st + 2) * symBox C_y (fun _ => 0) x := Nat.mul_le_mul_right _ hc18
  refine ⟨C_y, symBox_zero_weaken (hit.weaken ⟨4 * 18 ^ (D_st + 2) + 8, ?_⟩
    ⟨4 * 18 ^ (D_st + 2) + 8, ?_⟩)⟩ <;> intro x
  all_goals
    dsimp only
    set K := 18 ^ (D_st + 2)
    set B := symBox C_y (fun _ => 0) x
    have hx := enc_le_symBox (c := C_y) (by dsimp only [C_y]; omega) (fun _ => 0) x
    have hcm_le : (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ c_cm) * (x.n + 1) ^ c_cm ≤ B := by
      calc _ = symBox c_cm (fun _ => 0) x := by simp only [symBox, Nat.zero_add, Nat.mul_one]
        _ ≤ B := symBox_mono (by dsimp only [C_y]; omega : c_cm ≤ C_y) (fun _ => le_rfl) x
            (F₁ := fun _ => 0) (F₂ := fun _ => 0)
    have hB_le : 2 ^ x.n * (2 * (x.n + Nat.log2 ((encSymAndInstance x).length + 1) + 1) + 1) ≤
        R_y x := by dsimp only [R_y]; omega
    have hlen_n := encNat_length_le_succ x.n
    have hbox_pos : 1 ≤ B := symBox_pos C_y (fun _ => 0) x
    have hK_pos : 1 ≤ K := Nat.one_le_pow _ _ (by decide)
    have hKB : K * B ≤ K * (B + 1) := Nat.mul_le_mul_left K (Nat.le_succ B)
  · have hN_R : (x.n + 1) * R_y x ≤ K * B := by
      simpa only [pow_one] using hR_bound 1 le_rfl x
    have hN_B : (x.n + 1) *
        (2 ^ x.n * (2 * (x.n + Nat.log2 ((encSymAndInstance x).length + 1) + 1) + 1)) ≤ K * B :=
      (Nat.mul_le_mul_left _ hB_le).trans hN_R
    have hN3 : (x.n + 1) ^ 3 ≤ B :=
      n_pow_le_symBox (by dsimp only [C_y]; omega : 3 ≤ C_y) (fun _ => 0) x
    have hN_sq : (x.n + 1) * ((encNat x.n).length + 1) ^ 2 ≤ 4 * B := by
      have hsq : ((encNat x.n).length + 1) ^ 2 ≤ 4 * (x.n + 1) ^ 2 := by nlinarith
      calc _ ≤ (x.n + 1) * (4 * (x.n + 1) ^ 2) := Nat.mul_le_mul_left _ hsq
        _ = 4 * (x.n + 1) ^ 3 := by ring
        _ ≤ 4 * B := Nat.mul_le_mul_left 4 hN3
    rw [Nat.mul_add, Nat.mul_add]
    calc _ ≤ B + B + K * B + K * B + 4 * B := by omega
      _ = 6 * B + 2 * (K * B) := by ring
      _ ≤ 8 * (B + 1) + 4 * (K * (B + 1)) := by omega
      _ = (4 * K + 8) * (B + 1) := by ring
  · have hR : R_y x ≤ K * B := by
      simpa only [pow_zero, Nat.one_mul] using hR_bound 0 (Nat.zero_le 1) x
    have hN1 := n_pow_le_symBox (by dsimp only [C_y]; omega : 1 ≤ C_y) (fun _ => 0) x
    rw [pow_one] at hN1
    calc _ ≤ B + B + K * B + K * B + B := by omega
      _ = 3 * B + 2 * (K * B) := by ring
      _ ≤ (4 * K + 8) * (B + 1) := by
          have : (4 * K + 8) * (B + 1) = 4 * (K * (B + 1)) + 8 * (B + 1) := by ring
          omega

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
        by_cases hvs : v ≤ s
        · rw [ite_eq_left hvs]
          exact list_range_filter_unique (by omega)
            (fun j => evalBits (Nat.size s) (Nat.bits j) == v)
            (by simp [evalBits_bits_of_le hvs])
            (fun j hj hne => by simp [evalBits_bits_of_le (by omega : j ≤ s), hne])
        · rw [ite_eq_right hvs]
          exact List.filter_eq_nil_iff.2 fun j hj => by
            have hj_le : j ≤ s := by have := List.mem_range.1 hj; omega
            simp [evalBits_bits_of_le hj_le, show j ≠ v by omega]
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
              (fun j => (g[j]?.getD 0 == vk) && (evalBits x.n (Nat.bits j) == k)) = [k] :=
            list_range_filter_unique hk_lt_g
              (fun j => (g[j]?.getD 0 == vk) && (evalBits x.n (Nat.bits j) == k))
              (by simp [evalBits_bits x.n k hk, List.getElem?_eq_getElem hk_lt_g, vk])
              (fun j hj hne => by simp [evalBits_bits x.n j (by omega), hne])
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
  refine ⟨max c_s 3, htab.mono 305 (fun x => ?_) (fun x => ?_)⟩ <;>
  · set A := (encSymAndInstance x).length + 1
    set C := max c_s 3
    have hf := (tabulateStep_iter out x.gates.length).1
    have h_enc := hstep_enc_le x x.gates.length le_rfl
    have hg := gates_length_le_encSymAndInstance x
    have hn_s : (encNat x.gates.length).length + 1 ≤ A := by
      have := encNat_length_le x.gates.length; omega
    have hA_c : A ^ c_s ≤ A ^ C := Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_left _ _)
    have hA_3 : A ^ 3 ≤ A ^ C := Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_right _ _)
    have hA_2 : A ^ 2 ≤ A ^ C := Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
    have hA_1 : A ≤ A ^ C := Nat.le_self_pow (by omega) A
    have hsq : ((encNat x.gates.length).length + 1) ^ 2 ≤ A ^ 2 := Nat.pow_le_pow_left hn_s 2
    have hA2_pos : 1 ≤ A ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos _)
    have htab_le : ∀ (F : ℕ → ℕ),
        (x.gates.length + 1) * (61 * A ^ 2 + F x.gates.length + 57 * A ^ 2 +
            ((encNat x.gates.length).length + 1) ^ 2) +
          (58 * A ^ 2 + F x.gates.length + 1) + 57 * A ^ 2 +
          (encTab ((tabulateStep out)^[x.gates.length] (0, []))).length +
          (encSymAndInstance x).length + (encNat x.gates.length).length +
          F x.gates.length + A ^ c_s ≤
        305 * (A ^ C * (F x.gates.length + 1)) := fun F => by
      set P := A ^ C * (F x.gates.length + 1)
      have hAC_pos : 1 ≤ A ^ C := Nat.one_le_pow _ _ (Nat.succ_pos _)
      have hF1 : A ^ C ≤ P := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
      have hP1 : 1 ≤ P := hAC_pos.trans hF1
      have hmul : (x.gates.length + 1) * (122 * A ^ 2 + F x.gates.length) ≤ 122 * P := by
        calc (x.gates.length + 1) * (122 * A ^ 2 + F x.gates.length)
            ≤ A * (122 * A ^ 2 * (F x.gates.length + 1)) :=
              Nat.mul_le_mul (by omega) (by nlinarith)
          _ = 122 * (A ^ 3 * (F x.gates.length + 1)) := by ring
          _ ≤ 122 * P := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hA_3)
      have hprod : (x.gates.length + 1) * (61 * A ^ 2 + F x.gates.length + 57 * A ^ 2 +
            ((encNat x.gates.length).length + 1) ^ 2) ≤ 122 * P :=
        (Nat.mul_le_mul_left _ (by omega)).trans hmul
      have hF_le : F x.gates.length ≤ P :=
        (Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ hAC_pos)
      have h2C : A ^ 2 ≤ P := hA_2.trans hF1
      have h1C : A ≤ P := hA_1.trans hF1
      have h58 : 58 * A ^ 2 ≤ 58 * P := Nat.mul_le_mul_left 58 h2C
      have h57 : 57 * A ^ 2 ≤ 57 * P := Nat.mul_le_mul_left 57 h2C
      have h57_enc : (encTab ((tabulateStep out)^[x.gates.length] (0, []))).length ≤ 57 * P :=
        h_enc.trans h57
      have hxA : (encSymAndInstance x).length ≤ A := Nat.le_succ _
      have hsum_all : (x.gates.length + 1) * (61 * A ^ 2 + F x.gates.length + 57 * A ^ 2 +
            ((encNat x.gates.length).length + 1) ^ 2) +
          (58 * A ^ 2 + F x.gates.length + 1) + 57 * A ^ 2 +
          (encTab ((tabulateStep out)^[x.gates.length] (0, []))).length +
          (encSymAndInstance x).length + (encNat x.gates.length).length +
          F x.gates.length + A ^ c_s ≤ 305 * P := by
        calc _ ≤ 122 * P + (58 * P + P + P) + 57 * P + 57 * P + P + P + P + P := by omega
          _ = 300 * P := by ring
          _ ≤ 305 * P := Nat.mul_le_mul_right P (by decide)
      exact hsum_all
    rw [hf]
    first
    | exact (by omega : _ ≤ _).trans ((htab_le T).trans (Nat.mul_le_mul_left _ (Nat.le_succ _)))
    | exact (by omega : _ ≤ _).trans ((htab_le S).trans (Nat.mul_le_mul_left _ (Nat.le_succ _)))

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
  obtain ⟨d_f, hfold⟩ := computableInO_streamFold (encA := encNat) (encS := encNat)
    (encB := encJoinItem) (encIn := encPair encNat (encList encNat))
    Prod.fst Prod.snd (fun _ => rfl) hnext hemit
    (g := fun q : ℕ × List ℕ => queryEntriesFrom q.1 q.2)
    (fun q => queryEntriesFrom_streamEmit q.1 q.2)
    (lMax := fun q => Nat.log2 (q.1 + q.2.length + 1) +
      listMax (fun v => (encNat v).length) q.2 + 8)
    (B := fun q => (q.2.length + 1) * (Nat.log2 (q.1 + q.2.length + 1) +
      listMax (fun v => (encNat v).length) q.2 + 10))
    (fun q j _ => by
      have hst : streamState q.1 (fun p : ℕ × ℕ => p.1 + 1) q.2 j ≤ q.1 + q.2.length := by
        have htake : ∀ xs : List ℕ, ∀ s : ℕ, xs.foldl (fun a _ => a + 1) s = s + xs.length :=
          fun xs s => by
            induction xs generalizing s with
            | nil => simp
            | cons _ t ih => simp only [List.foldl_cons, ih, List.length_cons]; omega
        rw [streamState, htake, List.length_take]; omega
      have hlen := length_encNat_le_log2 (hst.trans (Nat.le_add_right (q.1 + q.2.length) 1))
      change (encNat (streamState q.1 _ q.2 j)).length ≤ _
      omega)
    (fun q j hj => (le_listMax (f := fun v => (encNat v).length) (List.getElem_mem hj)).trans
      (by omega))
    ⟨8, fun q => by
      have hm : ∀ p ∈ queryEntriesFrom q.1 q.2,
          (encJoinItem p).length ≤ 4 * (Nat.log2 (q.1 + q.2.length + 1) + 1) +
            2 * listMax (fun v => (encNat v).length) q.2 + 24 := fun p hp => by
        obtain ⟨_, hlt, _, j, hj, rfl⟩ := queryEntriesFrom_mem hp
        have hlen_j := length_encNat_le_log2 (by omega : q.1 + j ≤ q.1 + q.2.length + 1)
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
      have h1 := (length_encList_le encJoinItem _ hm).trans (by rw [hlen_q])
      have hmul : q.2.length * (2 * (4 * (Nat.log2 (q.1 + q.2.length + 1) + 1) +
            2 * listMax (fun v => (encNat v).length) q.2 + 24) + 1) ≤
          8 * ((q.2.length + 1) * (Nat.log2 (q.1 + q.2.length + 1) +
            listMax (fun v => (encNat v).length) q.2 + 10)) := by
        calc _ ≤ (q.2.length + 1) * (8 * (Nat.log2 (q.1 + q.2.length + 1) +
                  listMax (fun v => (encNat v).length) q.2 + 10)) :=
                Nat.mul_le_mul (Nat.le_succ _) (by omega)
          _ = _ := by ring
      exact (h1.trans hmul).trans (Nat.mul_le_mul_left 8 (Nat.le_succ _))⟩
  obtain ⟨c_y, hyates⟩ := computableInO_yatesZeta
  have hwrap : ComputableInO (fun x : SymAndInstance => (0, yatesZeta x.n (countMasks x)))
      encSymAndInstance (encPair encNat (encList encNat))
      (symBox (max c_y 1) fun _ => 0) (symBox (max c_y 1) fun _ => 0) := by
    have hp := (ComputableInO.constZero (encIn := encSymAndInstance) (encMid := encNat) 0).prod
      hyates
    refine hp.weaken ⟨2, fun x => ?_⟩ ⟨2, fun x => ?_⟩ <;>
    · dsimp only
      try rw [Nat.zero_add]
      have hx := enc_le_symBox (c := max c_y 1) (le_max_right _ _) (fun _ => 0) x
      have hy : (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ c_y) * (x.n + 1) ^ c_y ≤
          symBox (max c_y 1) (fun _ => 0) x := by
        simpa only [symBox, Nat.zero_add, Nat.mul_one] using Nat.mul_le_mul
          (Nat.add_le_add_left (Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_left _ _)) _)
          (Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_left _ _))
      have := Nat.add_le_add hx hy
      have h1 := Nat.le_succ (symBox (max c_y 1) (fun _ => 0) x)
      omega
  obtain ⟨c_w, hwrap_len⟩ := hwrap.length_le
  have hcomp := hfold.comp hwrap
  let D := max d_f 1
  let C_q := max c_y 1 + 2 * D + 4
  have hmain_q : ∀ x : SymAndInstance,
      ((yatesZeta x.n (countMasks x)).length + 1) *
          (Nat.log2 (0 + (yatesZeta x.n (countMasks x)).length + 1) +
            listMax (fun v => (encNat v).length) (yatesZeta x.n (countMasks x)) + 9) ^ D ≤
        11 ^ D * (2 * 3 ^ (D + 1) * 2 ^ D) * symBox C_q (fun _ => 0) x := fun x => by
    set A := (encSymAndInstance x).length + 1
    have hg_len : (yatesZeta x.n (countMasks x)).length = 2 ^ x.n := by
      rw [yatesZeta_countMasks_eq, List.length_map, List.length_range]
    have hlog : Nat.log2 (0 + (yatesZeta x.n (countMasks x)).length + 1) ≤ x.n + 1 := by
      rw [hg_len, Nat.zero_add]
      have hlt : 2 ^ x.n + 1 < 2 ^ (x.n + 2) := by
        have := Nat.one_le_pow x.n 2 (by decide); rw [pow_add]; omega
      by_contra hgt
      push Not at hgt
      have hgt' : x.n + 2 ≤ Nat.log2 (2 ^ x.n + 1) := by omega
      have hle := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hgt'
      have hself := Nat.log2_self_le (by positivity : 2 ^ x.n + 1 ≠ 0)
      omega
    have hmax_g : listMax (fun v => (encNat v).length) (yatesZeta x.n (countMasks x)) ≤
        Nat.log2 A + 1 :=
      listMax_le fun v hv => length_encNat_le_log2
        ((yatesZeta_mem_le x hv).trans
          ((gates_length_le_encSymAndInstance x).trans (Nat.le_succ _)))
    have hpow_b : (Nat.log2 (0 + (yatesZeta x.n (countMasks x)).length + 1) +
          listMax (fun v => (encNat v).length) (yatesZeta x.n (countMasks x)) + 9) ^ D ≤
        11 ^ D * (x.n + 1) ^ D * (Nat.log2 A + 2) ^ D := by
      have h1 : x.n ≤ x.n * (Nat.log2 A + 2) := Nat.le_mul_of_pos_right _ (by omega)
      have hbase : Nat.log2 (0 + (yatesZeta x.n (countMasks x)).length + 1) +
            listMax (fun v => (encNat v).length) (yatesZeta x.n (countMasks x)) + 9 ≤
          11 * (x.n + 1) * (Nat.log2 A + 2) := by nlinarith
      calc _ ≤ (11 * (x.n + 1) * (Nat.log2 A + 2)) ^ D := Nat.pow_le_pow_left hbase D
        _ = 11 ^ D * (x.n + 1) ^ D * (Nat.log2 A + 2) ^ D := by rw [Nat.mul_pow, Nat.mul_pow]
    have hlog_sym := symBox_log_le (r := D) (k := D) (c := C_q)
      (by dsimp only [C_q]; omega) (by dsimp only [C_q]; omega) (fun _ => 0) x
    calc ((yatesZeta x.n (countMasks x)).length + 1) *
            (Nat.log2 (0 + (yatesZeta x.n (countMasks x)).length + 1) +
              listMax (fun v => (encNat v).length) (yatesZeta x.n (countMasks x)) + 9) ^ D
        ≤ (2 ^ x.n + A) * (11 ^ D * (x.n + 1) ^ D * (Nat.log2 A + 2) ^ D) :=
            Nat.mul_le_mul (by rw [hg_len]; omega) hpow_b
      _ = 11 ^ D * ((2 ^ x.n + A) * (x.n + 1) ^ D * (Nat.log2 A + 2) ^ D) := by ring
      _ ≤ 11 ^ D * (2 * 3 ^ (D + 1) * 2 ^ D * symBox C_q (fun _ => 0) x) :=
            Nat.mul_le_mul_left _ hlog_sym
      _ = 11 ^ D * (2 * 3 ^ (D + 1) * 2 ^ D) * symBox C_q (fun _ => 0) x := by ring
  let K_q := 11 ^ D * (2 * 3 ^ (D + 1) * 2 ^ D)
  refine ⟨C_q, symBox_zero_weaken (hcomp.weaken ⟨c_w + K_q + 2, fun x => ?_⟩
      ⟨3 * K_q + 2, fun x => ?_⟩)⟩ <;>
  · dsimp only
    have hmq := hmain_q x
    have hbox := symBox_mono (by dsimp only [C_q]; omega : max c_y 1 ≤ C_q) (fun _ => le_rfl) x
      (F₁ := fun _ => 0) (F₂ := fun _ => 0)
    have hpow_df : (Nat.log2 (0 + (yatesZeta x.n (countMasks x)).length + 1) +
          listMax (fun v => (encNat v).length) (yatesZeta x.n (countMasks x)) + 8 + 1) ^ d_f ≤
        (Nat.log2 (0 + (yatesZeta x.n (countMasks x)).length + 1) +
          listMax (fun v => (encNat v).length) (yatesZeta x.n (countMasks x)) + 9) ^ D :=
      (Nat.pow_le_pow_left (by omega) d_f).trans
        (Nat.pow_le_pow_right (by omega) (le_max_left _ _))
    have hq_le : ((yatesZeta x.n (countMasks x)).length + 1) *
          (Nat.log2 (0 + (yatesZeta x.n (countMasks x)).length + 1) +
            listMax (fun v => (encNat v).length) (yatesZeta x.n (countMasks x)) + 8 + 1) ^ d_f ≤
        K_q * symBox C_q (fun _ => 0) x :=
      (Nat.mul_le_mul_left _ hpow_df).trans hmq
    have hK_pos : 1 ≤ K_q :=
      Nat.mul_pos (Nat.pow_pos (by decide))
        (Nat.mul_pos (Nat.mul_pos (by decide) (Nat.pow_pos (by decide))) (Nat.pow_pos (by decide)))
    have h1 : symBox C_q (fun _ => 0) x ≤ symBox C_q (fun _ => 0) x + 1 := Nat.le_succ _
    first
    | exact (by
        have hlen_w : (encPair encNat (encList encNat) (0, yatesZeta x.n (countMasks x))).length ≤
            c_w * (symBox C_q (fun _ => 0) x + 1) :=
          (hwrap_len x).trans (Nat.mul_le_mul_left _ (by omega))
        calc _ ≤ (symBox C_q (fun _ => 0) x + 1) + c_w * (symBox C_q (fun _ => 0) x + 1) +
                K_q * (symBox C_q (fun _ => 0) x + 1) := by
              have hK := Nat.mul_le_mul_left K_q h1
              omega
          _ = (c_w + K_q + 1) * (symBox C_q (fun _ => 0) x + 1) := by ring
          _ ≤ (c_w + K_q + 2) * (symBox C_q (fun _ => 0) x + 1) :=
              Nat.mul_le_mul_right _ (by omega))
    | exact (by
        have hp1 : (Nat.log2 (0 + (yatesZeta x.n (countMasks x)).length + 1) +
              listMax (fun v => (encNat v).length) (yatesZeta x.n (countMasks x)) + 8 + 1) ^
              d_f ≤ K_q * symBox C_q (fun _ => 0) x :=
          (Nat.le_mul_of_pos_left _ (Nat.succ_pos _)).trans hq_le
        have hp2 : ((yatesZeta x.n (countMasks x)).length + 1) *
              (Nat.log2 (0 + (yatesZeta x.n (countMasks x)).length + 1) +
                listMax (fun v => (encNat v).length) (yatesZeta x.n (countMasks x)) + 10) ≤
            2 * (K_q * symBox C_q (fun _ => 0) x) := by
          have hlin : Nat.log2 (0 + (yatesZeta x.n (countMasks x)).length + 1) +
                listMax (fun v => (encNat v).length) (yatesZeta x.n (countMasks x)) + 10 ≤
              2 * (Nat.log2 (0 + (yatesZeta x.n (countMasks x)).length + 1) +
                listMax (fun v => (encNat v).length) (yatesZeta x.n (countMasks x)) + 9) ^ D := by
            have hle := Nat.le_self_pow (by dsimp only [D]; omega : D ≠ 0)
              (Nat.log2 (0 + (yatesZeta x.n (countMasks x)).length + 1) +
                listMax (fun v => (encNat v).length) (yatesZeta x.n (countMasks x)) + 9)
            omega
          calc _ ≤ ((yatesZeta x.n (countMasks x)).length + 1) *
                  (2 * (Nat.log2 (0 + (yatesZeta x.n (countMasks x)).length + 1) +
                    listMax (fun v => (encNat v).length) (yatesZeta x.n (countMasks x)) + 9) ^
                    D) := Nat.mul_le_mul_left _ hlin
            _ = 2 * _ := by ring
            _ ≤ 2 * (K_q * symBox C_q (fun _ => 0) x) := Nat.mul_le_mul_left 2 hmq
        calc _ ≤ (symBox C_q (fun _ => 0) x + 1) +
                3 * (K_q * (symBox C_q (fun _ => 0) x + 1)) := by
              have hK := Nat.mul_le_mul_left K_q h1
              omega
          _ = (3 * K_q + 1) * (symBox C_q (fun _ => 0) x + 1) := by ring
          _ ≤ (3 * K_q + 2) * (symBox C_q (fun _ => 0) x + 1) :=
              Nat.mul_le_mul_right _ (by omega))

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
  obtain ⟨d_f, hsf⟩ := computableInO_streamFold (encA := encJoinItem) (encS := encBool)
    (encB := encPair encBits encBool) Prod.fst Prod.snd (fun _ => rfl) hnext hemit
    (g := fun q : Bool × List JoinItem => extractMatched q.1 q.2)
    (fun q => extractMatched_streamEmit q.1 q.2)
    (lMax := fun q => listMax (fun p : JoinItem => (encJoinItem p).length) q.2 + 4)
    (B := fun q => (q.2.length + 1) *
      (listMax (fun p : JoinItem => (encJoinItem p).length) q.2 + 1))
    (fun q j _ => (encBool_length_le_two _).trans (by omega))
    (fun q j hj => (le_listMax (f := fun p : JoinItem => (encJoinItem p).length)
      (List.getElem_mem hj)).trans (by omega))
    ⟨6, fun q => by
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
              have hb1 := encBool_length_le_two b
              have hba : (Nat.bits a.2.2.1).length = (encNat a.2.2.1).length := rfl
              simp only [encJoinItem, length_encPair, encBits_apply]
              omega
            have := ht b
            nlinarith
      have h1 := haux q.1 q.2 (fun p hp =>
        le_listMax (f := fun r : JoinItem => (encJoinItem r).length) hp)
      have hmul : q.2.length *
            (2 * (listMax (fun r : JoinItem => (encJoinItem r).length) q.2 + 3)) ≤
          6 * ((q.2.length + 1) *
            (listMax (fun p : JoinItem => (encJoinItem p).length) q.2 + 1)) := by
        calc _ ≤ (q.2.length + 1) *
                (6 * (listMax (fun p : JoinItem => (encJoinItem p).length) q.2 + 1)) :=
                Nat.mul_le_mul (Nat.le_succ _) (by omega)
          _ = _ := by ring
      exact (h1.trans hmul).trans (Nat.mul_le_mul_left 6 (Nat.le_succ _))⟩
  let D := max d_f 1
  refine ⟨D, (hsf.comp (computableInO_pair_const_id false)).weaken
    ⟨5 ^ d_f + 4, fun L => ?_⟩ ⟨5 ^ d_f + 3, fun L => ?_⟩⟩
  · dsimp only [D]
    rw [length_encPair]
    dsimp only
    have hb := encBool_length_le_two false
    have hpow := pow_shift_le (x := listMax (fun p : JoinItem => (encJoinItem p).length) L)
      (k := 5) (by decide) (le_max_left d_f 1)
    have hmul : (L.length + 1) *
          (listMax (fun p : JoinItem => (encJoinItem p).length) L + 4 + 1) ^ d_f ≤
        5 ^ d_f * ((L.length + 1) *
          (listMax (fun p : JoinItem => (encJoinItem p).length) L + 1) ^ max d_f 1) := by
      calc _ ≤ (L.length + 1) *
            (5 ^ d_f * (listMax (fun p : JoinItem => (encJoinItem p).length) L + 1) ^
              max d_f 1) := Nat.mul_le_mul_left _ hpow
        _ = _ := by ring
    have h1 : (L.length + 1) *
          (listMax (fun p : JoinItem => (encJoinItem p).length) L + 1) ^ max d_f 1 ≤
        (encList encJoinItem L).length +
          (L.length + 1) *
            (listMax (fun p : JoinItem => (encJoinItem p).length) L + 1) ^ max d_f 1 + 1 + 1 := by
      omega
    have hmul5 := Nat.mul_le_mul_left (5 ^ d_f) h1
    have hlin : 2 * (encList encJoinItem L).length + 2 * (encBool false).length + 1 ≤
        4 * ((encList encJoinItem L).length + (L.length + 1) *
          (listMax (fun p : JoinItem => (encJoinItem p).length) L + 1) ^ max d_f 1 + 1 + 1) := by
      omega
    calc _ ≤ 2 * (encList encJoinItem L).length + 2 * (encBool false).length + 1 +
          5 ^ d_f * ((L.length + 1) *
            (listMax (fun p : JoinItem => (encJoinItem p).length) L + 1) ^ max d_f 1) := by omega
      _ ≤ 4 * _ + 5 ^ d_f * _ := Nat.add_le_add hlin hmul5
      _ = (5 ^ d_f + 4) * _ := by ring
  · dsimp only [D]
    have hpow := pow_shift_le (x := listMax (fun p : JoinItem => (encJoinItem p).length) L)
      (k := 5) (by decide) (le_max_left d_f 1)
    have h1 : (encList encJoinItem L).length ≤
        2 * ((L.length + 1) * (listMax (fun p : JoinItem => (encJoinItem p).length) L + 1)) := by
      have hlen := length_encList_le encJoinItem L
        (b := listMax (fun r : JoinItem => (encJoinItem r).length) L)
        fun p hp => le_listMax (f := fun r : JoinItem => (encJoinItem r).length) hp
      calc _ ≤ (L.length + 1) *
              (2 * (listMax (fun p : JoinItem => (encJoinItem p).length) L + 1)) :=
            hlen.trans (Nat.mul_le_mul (Nat.le_succ _) (by omega))
        _ = _ := by ring
    set A := (listMax (fun p : JoinItem => (encJoinItem p).length) L + 1) ^ max d_f 1
    set B := (L.length + 1) * (listMax (fun p : JoinItem => (encJoinItem p).length) L + 1)
    have hpow' : (listMax (fun p : JoinItem => (encJoinItem p).length) L + 4 + 1) ^ d_f ≤
        5 ^ d_f * A := by
      rw [Nat.add_assoc _ 4 1]; exact hpow
    have hsum : 5 ^ d_f * A + 3 * B ≤ (5 ^ d_f + 3) * (A + B + 1 + 1) := by
      have h1' := Nat.add_le_add (Nat.mul_le_mul_right A (Nat.le_add_right (5 ^ d_f) 3))
        (Nat.mul_le_mul_right B (Nat.le_add_left 3 (5 ^ d_f)))
      calc 5 ^ d_f * A + 3 * B ≤ (5 ^ d_f + 3) * A + (5 ^ d_f + 3) * B := h1'
        _ = (5 ^ d_f + 3) * (A + B) := by ring
        _ ≤ (5 ^ d_f + 3) * (A + B + 1 + 1) := Nat.mul_le_mul_left _ (by omega)
    have hpow'' : (listMax (fun p : JoinItem => (encJoinItem p).length) L + (4 + 1)) ^ d_f ≤
        5 ^ d_f * A := by
      rw [← Nat.add_assoc]; exact hpow'
    calc (encList encJoinItem L).length +
          ((listMax (fun p : JoinItem => (encJoinItem p).length) L + 4 + 1) ^ d_f +
            (L.length + 1) * (listMax (fun p : JoinItem => (encJoinItem p).length) L + 1))
        ≤ 2 * B + (5 ^ d_f * A + B) := by
          rw [Nat.add_assoc (listMax (fun p : JoinItem => (encJoinItem p).length) L) 4 1]
          omega
      _ = 5 ^ d_f * A + 3 * B := by ring
      _ ≤ (5 ^ d_f + 3) * (A + B + 1 + 1) := hsum

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

private theorem computableInO_joined_of {out : ℕ → Bool} {T S : ℕ → ℕ}
    (hT_mono : Monotone T) (hS_mono : Monotone S)
    (hout : ComputableInO out encNat encBool T S) :
    ∃ C_j, ComputableInO
      (fun x : SymAndInstance => radixSortLSB (Nat.size x.gates.length)
        (tabulateOut out x.gates.length ++ queryEntries (yatesZeta x.n (countMasks x))))
      encSymAndInstance (encList encJoinItem)
      (symBox C_j T) (symBox C_j S) := by
  obtain ⟨c_tab, htab⟩ := computableInO_tabulateOut hT_mono hS_mono hout
  obtain ⟨c_q, hquery⟩ := computableInO_queryEntries
  obtain ⟨c_sz, hsz⟩ := computableInO_size_gates
  let joinInput (x : SymAndInstance) : List JoinItem :=
    tabulateOut out x.gates.length ++ queryEntries (yatesZeta x.n (countMasks x))
  let C_in := max (max c_tab c_q) 1
  have hjoin_in : ComputableInO joinInput encSymAndInstance (encList encJoinItem)
      (symBox C_in T) (symBox C_in S) := by
    have happ := (ComputableInO.of_linear (ComputableInDegree.listAppend encJoinItem)).comp_linear
      (htab.prod hquery)
    refine happ.weaken ⟨4, fun x => ?_⟩ ⟨4, fun x => ?_⟩ <;>
    · dsimp only [C_in]
      have hsub : ∀ G : ℕ → ℕ,
          ((encSymAndInstance x).length + 1) ^ c_tab * (G x.gates.length + 1) +
            (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ c_q) * (x.n + 1) ^ c_q ≤
          4 * (symBox (max (max c_tab c_q) 1) G x + 1) := fun G => by
        have ht1 : ((encSymAndInstance x).length + 1) ^ c_tab * (G x.gates.length + 1) ≤
            symBox (max (max c_tab c_q) 1) G x :=
          ((Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (Nat.succ_pos _)
            ((le_max_left c_tab c_q).trans (le_max_left _ _)))).trans (Nat.le_add_left _ _)).trans
            (Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (Nat.succ_pos _)))
        have ht2 : (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ c_q) * (x.n + 1) ^ c_q ≤
            symBox (max (max c_tab c_q) 1) G x := by
          calc _ = symBox c_q (fun _ => 0) x := by simp only [symBox, Nat.zero_add, Nat.mul_one]
            _ ≤ symBox (max (max c_tab c_q) 1) G x :=
                symBox_mono ((le_max_right c_tab c_q).trans (le_max_left _ _))
                  (fun s => Nat.zero_le (G s)) x (F₁ := fun _ => 0) (F₂ := G)
        omega
      first | exact hsub T | exact hsub S
  obtain ⟨d_js, hjoin_sort⟩ := computableInO_radixSortLSB hsz hjoin_in
    (length_encJoinItem_joinInput_le out)
  let D_j := max d_js 1
  let C_j := max c_sz C_in + 2 * D_j + 5
  let K_j := 2 * 41 ^ D_j * (2 * 3 ^ (D_j + 2) * 2 ^ (D_j + 1))
  refine ⟨C_j, hjoin_sort.weaken ⟨K_j + 1600, fun x => ?_⟩ ⟨K_j + 1600, fun x => ?_⟩⟩ <;>
  · dsimp only
    set A := (encSymAndInstance x).length + 1
    set N := x.n + 1
    have hg_le := gates_length_le_encSymAndInstance x
    have hlen_in := length_joinInput_le out x
    have hlen_2n : (joinInput x).length + 1 ≤ 2 * (2 ^ x.n + A) := by
      have h2n := Nat.one_le_pow x.n 2 (by decide)
      dsimp only [joinInput, A] at hlen_in ⊢; omega
    have harg : (encNat (Nat.size x.gates.length)).length +
          (4 * x.n + 6 * Nat.log2 A + 32) + 1 ≤ 41 * N * (Nat.log2 A + 2) := by
      have hlen_sz : (encNat (Nat.size x.gates.length)).length ≤ Nat.log2 A + 1 :=
        length_encNat_le_log2 (((Nat.size_le_self _).trans hg_le).trans (Nat.le_succ _))
      have h1 : x.n ≤ x.n * (Nat.log2 A + 2) := Nat.le_mul_of_pos_right _ (by omega)
      have h41 : 41 * N * (Nat.log2 A + 2) =
          41 * (x.n * (Nat.log2 A + 2)) + 41 * (Nat.log2 A + 2) := by
        dsimp only [N]; ring
      omega
    have hpow_d : ((encNat (Nat.size x.gates.length)).length +
          (4 * x.n + 6 * Nat.log2 A + 32) + 1) ^ d_js ≤
        41 ^ D_j * N ^ D_j * (Nat.log2 A + 2) ^ D_j := by
      have hpos : 0 < 41 * N * (Nat.log2 A + 2) :=
        Nat.mul_pos (Nat.mul_pos (by decide) (Nat.succ_pos x.n)) (by omega)
      calc _ ≤ (41 * N * (Nat.log2 A + 2)) ^ d_js := Nat.pow_le_pow_left harg d_js
        _ ≤ (41 * N * (Nat.log2 A + 2)) ^ D_j :=
            Nat.pow_le_pow_right hpos (le_max_left _ _)
        _ = _ := by rw [Nat.mul_pow, Nat.mul_pow]
    have hb_le : Nat.size x.gates.length + 1 ≤ Nat.log2 A + 2 := by
      have h1 : Nat.size x.gates.length ≤ Nat.log2 (x.gates.length + 1) + 1 := by
        rw [← Nat.size_eq_bits_len]; exact length_encNat_le_log2 (Nat.le_succ _)
      have h2 := log2_mono (by omega : x.gates.length + 1 ≤ A)
      omega
    have hC1 : 1 ≤ C_j := by dsimp only [C_j]; omega
    have hsub : ∀ G : ℕ → ℕ,
        ((encSymAndInstance x).length + A ^ c_sz + symBox C_in G x +
          (Nat.size x.gates.length + 1) * ((joinInput x).length + 1) *
            ((encNat (Nat.size x.gates.length)).length +
              (4 * x.n + 6 * Nat.log2 A + 32) + 1) ^ d_js +
          (Nat.size x.gates.length + 1) +
          ((joinInput x).length + 1) * (4 * x.n + 6 * Nat.log2 A + 32 + 1)) ≤
        (K_j + 1600) * (symBox C_j G x + 1) := fun G => by
      set B := symBox C_j G x
      have hx := enc_le_symBox hC1 G x
      have hsz_le := A_pow_le_symBox (by dsimp only [C_j]; omega : c_sz ≤ C_j) G x
      have hjin_le := symBox_mono (by dsimp only [C_j]; omega : C_in ≤ C_j) (fun _ => le_rfl) x
        (F₁ := G) (F₂ := G)
      have hlog_D := symBox_log_le (r := D_j) (k := D_j + 1) (c := C_j)
        (by dsimp only [C_j]; omega) (by dsimp only [C_j]; omega) G x
      have hlog_1 := symBox_log_le (r := 1) (k := 1) (c := C_j)
        (by dsimp only [C_j]; omega) (by dsimp only [C_j]; omega) G x
      have h3_le : 2 * 3 ^ (D_j + 1 + 1) * 2 ^ (D_j + 1) =
          2 * 3 ^ (D_j + 2) * 2 ^ (D_j + 1) := by ring
      have hprod_d : (Nat.size x.gates.length + 1) * ((joinInput x).length + 1) *
            ((encNat (Nat.size x.gates.length)).length +
              (4 * x.n + 6 * Nat.log2 A + 32) + 1) ^ d_js ≤
          K_j * B := by
        calc _ ≤ (Nat.log2 A + 2) * (2 * (2 ^ x.n + A)) *
                (41 ^ D_j * N ^ D_j * (Nat.log2 A + 2) ^ D_j) :=
              Nat.mul_le_mul (Nat.mul_le_mul hb_le hlen_2n) hpow_d
          _ = 2 * 41 ^ D_j * ((2 ^ x.n + A) * N ^ D_j * (Nat.log2 A + 2) ^ (D_j + 1)) := by ring
          _ ≤ 2 * 41 ^ D_j * (2 * 3 ^ (D_j + 2) * 2 ^ (D_j + 1) * B) :=
              Nat.mul_le_mul_left _ (by rw [← h3_le]; exact hlog_D)
          _ = K_j * B := by dsimp only [K_j]; ring
      have hsz1 : Nat.size x.gates.length + 1 ≤ 36 * B := by
        have h2n_1 : 1 ≤ (2 ^ x.n + A) * N ^ 1 :=
          Nat.mul_pos (by omega) (Nat.pow_pos (Nat.succ_pos x.n))
        have hb1 : Nat.size x.gates.length + 1 ≤ (Nat.log2 A + 2) ^ 1 := by
          rw [pow_one]; exact hb_le
        calc Nat.size x.gates.length + 1 ≤ (2 ^ x.n + A) * N ^ 1 * (Nat.log2 A + 2) ^ 1 :=
              hb1.trans (Nat.le_mul_of_pos_left _ h2n_1)
          _ ≤ 2 * 3 ^ (1 + 1) * 2 ^ 1 * B := hlog_1
          _ = 36 * B := by ring
      have hprod_1 : ((joinInput x).length + 1) * (4 * x.n + 6 * Nat.log2 A + 32 + 1) ≤
          1300 * B := by
        have h1 : x.n ≤ x.n * (Nat.log2 A + 2) := Nat.le_mul_of_pos_right _ (by omega)
        have h17 : 17 * N * (Nat.log2 A + 2) =
            17 * (x.n * (Nat.log2 A + 2)) + 17 * (Nat.log2 A + 2) := by
          dsimp only [N]; ring
        have hlin : 4 * x.n + 6 * Nat.log2 A + 33 ≤ 17 * N * (Nat.log2 A + 2) := by omega
        calc _ ≤ (2 * (2 ^ x.n + A)) * (17 * N * (Nat.log2 A + 2)) :=
              Nat.mul_le_mul hlen_2n (by omega)
          _ = 34 * ((2 ^ x.n + A) * N ^ 1 * (Nat.log2 A + 2) ^ 1) := by ring
          _ ≤ 34 * (2 * 3 ^ (1 + 1) * 2 ^ 1 * B) := Nat.mul_le_mul_left _ hlog_1
          _ = 1224 * B := by ring
          _ ≤ 1300 * B := Nat.mul_le_mul_right _ (by decide)
      calc _ ≤ B + B + B + K_j * B + 36 * B + 1300 * B := by
            have hadd := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
              (Nat.add_le_add (Nat.add_le_add hx hsz_le) hjin_le) hprod_d) hsz1) hprod_1
            dsimp only [B] at hadd ⊢; omega
        _ = (K_j + 1339) * B := by ring
        _ ≤ (K_j + 1600) * (B + 1) := Nat.mul_le_mul (by omega) (Nat.le_succ B)
    first
    | exact (by
        have := hsub T
        rw [Nat.mul_add (Nat.size x.gates.length + 1), Nat.mul_one,
          ← Nat.mul_assoc (Nat.size x.gates.length + 1)]
        omega)
    | exact (by
        have hs := hsub S
        have hst : ((encNat (Nat.size x.gates.length)).length +
              (4 * x.n + 6 * Nat.log2 A + 32) + 1) ^ d_js ≤
            (Nat.size x.gates.length + 1) * ((joinInput x).length + 1) *
              ((encNat (Nat.size x.gates.length)).length +
                (4 * x.n + 6 * Nat.log2 A + 32) + 1) ^ d_js :=
          Nat.le_mul_of_pos_left _ (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _))
        omega)

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
      (symBox C_ex T) (symBox C_ex S) := by
  obtain ⟨C_j, hjoined⟩ := computableInO_joined_of hT_mono hS_mono hout
  obtain ⟨d_ex, hex_raw⟩ := computableInO_extractMatched
  have hmem_joined : ∀ x : SymAndInstance, ∀ p ∈ joined out x, p ∈ joinInput out x :=
    fun x p hp => (mem_radixStep_iff).1 hp
  have hlen_joined : ∀ x : SymAndInstance, (joined out x).length = (joinInput out x).length :=
    fun x => length_radixStep _ 0 _
  let D_ex := max d_ex 1
  let C_ex := C_j + 2 * D_ex + 4
  have hpow_ex : ∀ G (x : SymAndInstance),
      ((joined out x).length + 1) *
          (listMax (fun p : JoinItem => (encJoinItem p).length) (joined out x) + 1) ^ D_ex ≤
        2 * 17 ^ D_ex * (2 * 3 ^ (D_ex + 1) * 2 ^ D_ex) * symBox C_ex G x := fun G x => by
    set A := (encSymAndInstance x).length + 1
    have hlen_j := hlen_joined x
    have hlen_in := length_joinInput_le out x
    have hg_le := gates_length_le_encSymAndInstance x
    have hmax_j : listMax (fun p : JoinItem => (encJoinItem p).length) (joined out x) ≤
        4 * x.n + 6 * Nat.log2 A + 32 :=
      listMax_le fun p hp => length_encJoinItem_joinInput_le out x p (hmem_joined x p hp)
    have h1 : 4 * x.n + 6 * Nat.log2 A + 34 ≤ 17 * (x.n + 1) * (Nat.log2 A + 2) := by nlinarith
    have hpow : (listMax (fun p : JoinItem => (encJoinItem p).length) (joined out x) + 1) ^ D_ex ≤
        17 ^ D_ex * (x.n + 1) ^ D_ex * (Nat.log2 A + 2) ^ D_ex := by
      calc _ ≤ (17 * (x.n + 1) * (Nat.log2 A + 2)) ^ D_ex := Nat.pow_le_pow_left (by omega) D_ex
        _ = _ := by rw [Nat.mul_pow, Nat.mul_pow]
    have h2n : 1 ≤ 2 ^ x.n := Nat.one_le_pow _ _ (by decide)
    have hlen2 : (joined out x).length + 1 ≤ 2 * (2 ^ x.n + A) := by
      dsimp only [joined, joinInput] at hlen_j ⊢; omega
    have hlog := symBox_log_le (r := D_ex) (k := D_ex) (c := C_ex)
      (by dsimp only [C_ex]; omega) (by dsimp only [C_ex]; omega) G x
    calc _ ≤ (2 * (2 ^ x.n + A)) * (17 ^ D_ex * (x.n + 1) ^ D_ex * (Nat.log2 A + 2) ^ D_ex) :=
          Nat.mul_le_mul hlen2 hpow
      _ = 2 * 17 ^ D_ex * ((2 ^ x.n + A) * (x.n + 1) ^ D_ex * (Nat.log2 A + 2) ^ D_ex) := by ring
      _ ≤ 2 * 17 ^ D_ex * (2 * 3 ^ (D_ex + 1) * 2 ^ D_ex * symBox C_ex G x) :=
          Nat.mul_le_mul_left _ hlog
      _ = _ := by ring
  let K_ex := 2 * 17 ^ D_ex * (2 * 3 ^ (D_ex + 1) * 2 ^ D_ex)
  have hcomp := hex_raw.comp hjoined
  refine ⟨C_ex, hcomp.weaken ⟨5 * K_ex + 5, fun x => ?_⟩ ⟨5 * K_ex + 5, fun x => ?_⟩⟩ <;>
  · dsimp only [joined, joinInput]
    have hm1 : 1 ≤ listMax (fun p : JoinItem => (encJoinItem p).length) (joined out x) + 1 :=
      Nat.succ_pos _
    have hD_pos : D_ex ≠ 0 := by dsimp only [D_ex]; omega
    have henc_j : (encList encJoinItem (joined out x)).length ≤
        2 * ((joined out x).length + 1) *
          (listMax (fun p : JoinItem => (encJoinItem p).length) (joined out x) + 1) ^ D_ex := by
      have h1 := length_encList_le encJoinItem (joined out x)
        (b := listMax (fun p : JoinItem => (encJoinItem p).length) (joined out x))
        fun p hp => le_listMax (f := fun p : JoinItem => (encJoinItem p).length) hp
      have h2 := Nat.le_self_pow hD_pos
        (listMax (fun p : JoinItem => (encJoinItem p).length) (joined out x) + 1)
      have h2' : 2 * listMax (fun p : JoinItem => (encJoinItem p).length) (joined out x) + 1 ≤
          2 * (listMax (fun p : JoinItem => (encJoinItem p).length) (joined out x) + 1) ^ D_ex := by
        omega
      calc (encList encJoinItem (joined out x)).length
          ≤ (joined out x).length *
              (2 * listMax (fun p : JoinItem => (encJoinItem p).length) (joined out x) + 1) := h1
        _ ≤ (joined out x).length *
              (2 * (listMax (fun p : JoinItem => (encJoinItem p).length) (joined out x) + 1) ^
                D_ex) := Nat.mul_le_mul_left _ h2'
        _ ≤ ((joined out x).length + 1) *
              (2 * (listMax (fun p : JoinItem => (encJoinItem p).length) (joined out x) + 1) ^
                D_ex) := Nat.mul_le_mul_right _ (Nat.le_succ _)
        _ = 2 * ((joined out x).length + 1) *
              (listMax (fun p : JoinItem => (encJoinItem p).length) (joined out x) + 1) ^
                D_ex := by ring
    have hpow_d : (listMax (fun p : JoinItem => (encJoinItem p).length) (joined out x) + 1) ^ d_ex ≤
        ((joined out x).length + 1) *
          (listMax (fun p : JoinItem => (encJoinItem p).length) (joined out x) + 1) ^ D_ex :=
      (Nat.pow_le_pow_right hm1 (le_max_left _ _)).trans
        (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
    have hprod_d : ((joined out x).length + 1) *
          (listMax (fun p : JoinItem => (encJoinItem p).length) (joined out x) + 1) ^ d_ex ≤
        ((joined out x).length + 1) *
          (listMax (fun p : JoinItem => (encJoinItem p).length) (joined out x) + 1) ^ D_ex :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hm1 (le_max_left _ _))
    have hprod_1 : ((joined out x).length + 1) *
          (listMax (fun p : JoinItem => (encJoinItem p).length) (joined out x) + 1) ≤
        ((joined out x).length + 1) *
          (listMax (fun p : JoinItem => (encJoinItem p).length) (joined out x) + 1) ^ D_ex :=
      Nat.mul_le_mul_left _ (Nat.le_self_pow hD_pos _)
    have hsub : ∀ G, (symBox C_j G x +
          ((encList encJoinItem (joined out x)).length +
            ((joined out x).length + 1) *
              (listMax (fun p : JoinItem => (encJoinItem p).length) (joined out x) + 1) ^ d_ex +
            1) +
          ((listMax (fun p : JoinItem => (encJoinItem p).length) (joined out x) + 1) ^ d_ex +
            ((joined out x).length + 1) *
              (listMax (fun p : JoinItem => (encJoinItem p).length) (joined out x) + 1) + 1)) ≤
        (5 * K_ex + 5) * (symBox C_ex G x + 1) := fun G => by
      set B := symBox C_ex G x
      set M := ((joined out x).length + 1) *
        (listMax (fun p : JoinItem => (encJoinItem p).length) (joined out x) + 1) ^ D_ex
      have hbox_c := symBox_mono (by dsimp only [C_ex]; omega : C_j ≤ C_ex) (fun _ => le_rfl) x
        (F₁ := G) (F₂ := G)
      have hmain : M ≤ K_ex * B := hpow_ex G x
      have hpos : 1 ≤ B := symBox_pos C_ex G x
      have henc_j' : (encList encJoinItem (joined out x)).length ≤ 2 * M := by
        dsimp only [M]; rw [Nat.mul_assoc] at henc_j; exact henc_j
      calc _ ≤ B + (2 * M + M + 1) + (M + M + 1) := by omega
        _ = B + 5 * M + 2 := by ring
        _ ≤ B + 5 * (K_ex * B) + 2 := by have := Nat.mul_le_mul_left 5 hmain; omega
        _ ≤ (5 * K_ex + 5) * (B + 1) := by
            have : (5 * K_ex + 5) * (B + 1) = 5 * (K_ex * B) + 5 * K_ex + 5 * B + 5 := by ring
            omega
    first
    | exact (by have := hsub T; dsimp only [joined, joinInput] at this ⊢; omega)
    | exact (by have := hsub S; dsimp only [joined, joinInput] at this ⊢; omega)

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
      (symBox C_r T) (symBox C_r S) := by
    refine hrest_sort.weaken ⟨3 * 10 ^ d_rs + 32, fun x => ?_⟩
        ⟨3 * 10 ^ d_rs + 32, fun x => ?_⟩ <;>
    · dsimp only
      set A := (encSymAndInstance x).length + 1
      set N := x.n + 1
      have hlen_e : (extracted x).length + 1 ≤ 2 * (2 ^ x.n + A) := by
        have h1 := (hextract_bounds x).1
        have h2 := hlen_joined x
        have h3 := hlen_join_in x
        have h4 := gates_length_le_encSymAndInstance x
        have h5 : 1 ≤ 2 ^ x.n := Nat.one_le_pow _ _ (by decide)
        dsimp only [extracted, joined, joinInput] at h1 h2 ⊢; omega
      have hsub : ∀ G, 2 * (encSymAndInstance x).length + symBox C_ex G x +
            N * ((extracted x).length + 1) *
              ((encNat x.n).length + (2 * x.n + 8) + 1) ^ d_rs + N +
            ((extracted x).length + 1) * (2 * x.n + 8 + 1) +
            ((encNat x.n).length + (2 * x.n + 8) + 1) ^ d_rs ≤
          (3 * 10 ^ d_rs + 32) * (symBox C_r G x + 1) := fun G => by
        have hx := enc_le_symBox (by dsimp only [C_r]; omega : 1 ≤ C_r) G x
        have hbox_c := symBox_mono (by dsimp only [C_r]; omega : C_ex ≤ C_r) (fun _ => le_rfl) x
          (F₁ := G) (F₂ := G)
        have hA_1 : A ≤ A ^ C_r * (G x.gates.length + 1) :=
          (Nat.le_self_pow (by dsimp only [C_r]; omega) A).trans
            (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
        have hN_1 : N ≤ symBox C_r G x := by
          have := n_pow_le_symBox (by dsimp only [C_r]; omega : 1 ≤ C_r) G x
          rwa [pow_one] at this
        have hN_ds := n_pow_le_symBox (by dsimp only [C_r]; omega : d_rs ≤ C_r) G x
        have hpow_ex : N * (((extracted x).length + 1) *
              ((encNat x.n).length + (2 * x.n + 8) + 1) ^ d_rs) ≤
            2 * (10 ^ d_rs * symBox C_r G x) := by
          calc _ ≤ N * ((2 * (2 ^ x.n + A)) * (10 ^ d_rs * N ^ d_rs)) :=
                Nat.mul_le_mul_left _ (Nat.mul_le_mul hlen_e (pow_encNat_add_le x.n d_rs))
            _ = 2 * (10 ^ d_rs * ((2 ^ x.n + A) * (N * N ^ d_rs))) := by ring
            _ = 2 * (10 ^ d_rs * ((2 ^ x.n + A) * N ^ (d_rs + 1))) := by rw [← pow_succ']
            _ ≤ 2 * (10 ^ d_rs * symBox C_r G x) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
                (Nat.mul_le_mul (Nat.add_le_add_left hA_1 _)
                  (Nat.pow_le_pow_right (Nat.succ_pos _) (by dsimp only [C_r]; omega))))
        have hmul_m : ((extracted x).length + 1) * (2 * x.n + 8 + 1) ≤ 18 * symBox C_r G x := by
          calc _ ≤ (2 * (2 ^ x.n + A)) * (9 * N) :=
                Nat.mul_le_mul hlen_e (by dsimp only [N]; omega)
            _ = 18 * ((2 ^ x.n + A) * N) := by ring
            _ ≤ 18 * symBox C_r G x := Nat.mul_le_mul_left 18 (Nat.mul_le_mul
                (Nat.add_le_add_left hA_1 _) (Nat.le_self_pow (by dsimp only [C_r]; omega) N))
        have hp_sort := (pow_encNat_add_le x.n d_rs).trans (Nat.mul_le_mul_left _ hN_ds)
        have hsum_raw : 2 * (encSymAndInstance x).length + symBox C_ex G x +
              N * (((extracted x).length + 1) *
                ((encNat x.n).length + (2 * x.n + 8) + 1) ^ d_rs) + N +
              ((extracted x).length + 1) * (2 * x.n + 8 + 1) +
              ((encNat x.n).length + (2 * x.n + 8) + 1) ^ d_rs ≤
            3 * (10 ^ d_rs * symBox C_r G x) + 22 * symBox C_r G x := by
          have h1 := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
            (Nat.add_le_add (Nat.mul_le_mul_left 2 hx) hbox_c) hpow_ex) hN_1) hmul_m) hp_sort
          calc _ ≤ _ := h1
            _ = 3 * (10 ^ d_rs * symBox C_r G x) + 22 * symBox C_r G x := by ring
        calc _ ≤ 3 * (10 ^ d_rs * symBox C_r G x) + 22 * symBox C_r G x := by
              rw [Nat.mul_assoc]; exact hsum_raw
          _ ≤ (3 * 10 ^ d_rs + 32) * (symBox C_r G x + 1) := by
              have h1 := Nat.mul_le_mul_left (3 * 10 ^ d_rs)
                (by omega : symBox C_r G x ≤ symBox C_r G x + 1)
              have h2 := Nat.mul_le_mul_left 22
                (by omega : symBox C_r G x ≤ symBox C_r G x + 1)
              have h3 : 22 * (symBox C_r G x + 1) ≤ 32 * (symBox C_r G x + 1) :=
                Nat.mul_le_mul_right _ (by decide)
              calc 3 * (10 ^ d_rs * symBox C_r G x) + 22 * symBox C_r G x
                  = 3 * 10 ^ d_rs * symBox C_r G x + 22 * symBox C_r G x := by ring
                _ ≤ 3 * 10 ^ d_rs * (symBox C_r G x + 1) + 32 * (symBox C_r G x + 1) := by omega
                _ = (3 * 10 ^ d_rs + 32) * (symBox C_r G x + 1) := by ring
      first
      | exact (by
          have := hsub T
          dsimp only [N, extracted, joined, joinInput] at this ⊢
          rw [Nat.mul_add (x.n + 1), Nat.mul_one, ← Nat.mul_assoc (x.n + 1)]
          omega)
      | exact (by
          have := hsub S
          dsimp only [N, extracted, joined, joinInput] at this ⊢
          omega)
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

/-- **Yates zeta count table on multi-tape Turing machines**: computing the satisfied-AND count for
all `2 ^ x.n` inputs (`SymAndInstance.countList`, independent of any symmetric output gate `out`)
runs in time and space `O((2 ^ x.n + ((encSymAndInstance x).length + 1) ^ c) * (x.n + 1) ^ c)`. -/
theorem computableInO_countList :
    ∃ c, ComputableInO SymAndInstance.countList encSymAndInstance (encList encNat)
      (fun x => (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ c) * (x.n + 1) ^ c)
      (fun x => (2 ^ x.n + ((encSymAndInstance x).length + 1) ^ c) * (x.n + 1) ^ c) := by
  obtain ⟨c, hc⟩ := computableInO_yatesZeta
  refine ⟨c, hc.of_enc_eq fun x => congrArg (encList encNat) ?_⟩
  refine List.ext_getElem (by rw [SymAndInstance.length_countList, yatesZeta_countMasks_eq,
      List.length_map, List.length_range]) fun k hk1 hk2 => ?_
  have hk : k < 2 ^ x.n := by simpa only [SymAndInstance.length_countList] using hk1
  rw [SymAndInstance.getElem_countList x (fun _ => false) k hk1]
  have hcnt := count_eq_subsetZeta_filter (x.toSymAnd fun _ => false)
    ((BitString.equivFin x.n).symm ⟨k, hk⟩)
  have hmask_eq : Finset.univ.filter (fun i : Fin x.n =>
      ((BitString.equivFin x.n).symm ⟨k, hk⟩) i = true) = maskSet x.n k := by
    ext i
    simp [BitString.equivFin_symm_apply, mem_maskSet]
  have hg : (x.toSymAnd fun _ => false).gateMultiplicity =
      fun T => (x.gates.map (gateSet x.n)).count T := by
    funext T; simp [gateMultiplicity, SymAndInstance.toSymAnd]
  rw [hcnt, hmask_eq, hg, subsetZeta_listCount_eq_countP]
  simp only [yatesZeta_countMasks_eq, List.getElem_map, List.getElem_range, hk, ↓reduceDIte]

end MultiTapeTM
end Cslib.Circuits.Boolean.SymAnd
