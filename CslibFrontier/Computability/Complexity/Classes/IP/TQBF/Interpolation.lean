/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.IP.TQBF.Words
import CslibFrontier.Foundations.Data.Polynomial.CoeffList
import Mathlib.Algebra.Polynomial.Roots
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import Mathlib.Data.List.GetD
import Mathlib.FieldTheory.Finite.Basic

/-!
# Interpolation modulo a prime for the machine verifier

At an operator node the verifier of `Cslib.Complexity.QBFProtocol.verifyAt` wants the first
`D + 1` coefficients of a restriction polynomial, while a circuit gives only its values at
`0, …, D`. This file recovers the coefficients from the values by Lagrange interpolation over
`ZMod p`, on residues below `p` as in `Words.lean`: the Lagrange basis polynomials are products of
factors `X - k`, built by repeated multiplication modulo `p`, scaled by inverses computed as
`a ^ (p - 2)` by iterated multiplication, and summed modulo `p`. All of it is polynomial-time in
`p`, `D` and the values in unary.

## Main definitions

* `Cslib.Complexity.QBFProtocol.interpMod`: the coefficients, lowest degree first, of the
  polynomial of degree at most `D` taking the value `vals[i]` at `i` for `i ≤ D`.

## Main results

* `Cslib.Complexity.QBFProtocol.length_interpMod`,
  `Cslib.Complexity.QBFProtocol.lt_of_mem_interpMod`: the shape of the result.
* `Cslib.Complexity.QBFProtocol.evalCoeffList_interpMod`: the interpolation property.
* `Cslib.Complexity.QBFProtocol.map_natCast_interpMod`: interpolating the values of a polynomial
  of degree at most `D < p` returns its coefficients.
* `Cslib.Complexity.QBFProtocol.computableInPolyTime_interpMod`: `interpMod` is polynomial-time.

## References

* [A. Shen, *IP = SPACE: simplified proof*][Shen1992]
-/

@[expose] public section

namespace Cslib.Complexity.QBFProtocol

open Polynomial

/-! ### Definitions -/

/-- The coefficients modulo `m` of `(X - k) * l`, where `l` lists coefficients, lowest first. -/
def mulXSubMod (m k : ℕ) (l : List ℕ) : List ℕ :=
  ((0 :: l).zip (l ++ [0])).map fun q => subMod m q.1 (k * q.2)

/-- The coefficients modulo `m` of the product of `X - k` over `k ≤ D` with `k ≠ j`, the Lagrange
basis polynomial for the node `j` up to a scalar. -/
def basisMod (m D j : ℕ) : List ℕ :=
  (List.range (D + 1)).foldl (fun acc k => if k == j then acc else mulXSubMod m k acc) [1 % m]

/-- The value modulo `m` at `j` of `basisMod m D j`: the product of `j - k` over `k ≤ D` with
`k ≠ j`. -/
def denomMod (m D j : ℕ) : ℕ :=
  (List.range (D + 1)).foldl (fun acc k => if k == j then acc else acc * subMod m j k % m) (1 % m)

/-- The power `a ^ (m - 2)` modulo `m` by iterated multiplication, the inverse of `a` modulo a
prime `m` when `a` is not divisible by `m`. -/
def invMod (m a : ℕ) : ℕ := (fun acc => acc * a % m)^[m - 2] (1 % m)

/-- The sum modulo `m` of two coefficient lists, entry by entry. -/
def addListMod (m : ℕ) (a b : List ℕ) : List ℕ := (a.zip b).map fun q => (q.1 + q.2) % m

/-- The scalar multiple modulo `m` of a coefficient list. -/
def scaleMod (m s : ℕ) (l : List ℕ) : List ℕ := l.map fun a => a * s % m

/-- The Lagrange weight of the node `j` modulo `m`: the value at `j` over `denomMod m D j`. -/
def weightMod (m D : ℕ) (vals : List ℕ) (j : ℕ) : ℕ :=
  vals.getD j 0 % m * invMod m (denomMod m D j) % m

/-- The Lagrange sum modulo `m`, the coefficient lists of the basis polynomials scaled by their
weights and added, from the zero list. -/
def interpModAux (m D : ℕ) (vals : List ℕ) : List ℕ :=
  (List.range (D + 1)).foldl
    (fun acc j => addListMod m acc (scaleMod m (weightMod m D vals j) (basisMod m D j)))
    (List.replicate (D + 1) 0)

/-- The coefficients, lowest degree first, of the polynomial of degree at most `D` over `ZMod p`
taking the value `vals[i]` at `i` for `i = 0, …, D`, as residues below `p`. Missing values read
as `0`. The modulus `0` is read as `1`, as in `hornerMod`, so that the entries stay small. -/
def interpMod (p D : ℕ) (vals : List ℕ) : List ℕ := interpModAux (p - 1 + 1) D vals

/-! ### Correctness -/

section Algebra

variable {m : ℕ} [NeZero m]

/-- The value at `z` of the coefficients `prev - k * l[0], l[0] - k * l[1], …` of `(X - k) * l`
plus `prev`. -/
theorem evalCoeffList_zipMulXSub (k : ℕ) (z : ZMod m) (l : List ℕ) (prev : ℕ) :
    evalCoeffList z
      ((((prev :: l).zip (l ++ [0])).map fun q => subMod m q.1 (k * q.2)).map Nat.cast) =
      prev + (z - k) * evalCoeffList z (l.map Nat.cast) := by
  induction l generalizing prev with
  | nil => simp [natCast_subMod]
  | cons a l ih =>
    rw [List.cons_append, List.zip_cons_cons, List.map_cons, List.map_cons, evalCoeffList_cons,
      ih a, natCast_subMod, List.map_cons, evalCoeffList_cons, Nat.cast_mul]
    ring

/-- Multiplying by `X - k` multiplies the value at `z` by `z - k`. -/
theorem evalCoeffList_mulXSubMod (k : ℕ) (z : ZMod m) (l : List ℕ) :
    evalCoeffList z ((mulXSubMod m k l).map Nat.cast) =
      (z - k) * evalCoeffList z (l.map Nat.cast) := by
  rw [mulXSubMod, evalCoeffList_zipMulXSub]
  simp

omit [NeZero m] in
/-- Multiplying by `X - k` adds one coefficient. -/
theorem length_mulXSubMod (k : ℕ) (l : List ℕ) : (mulXSubMod m k l).length = l.length + 1 := by
  simp [mulXSubMod]

/-- The coefficients of `mulXSubMod` are residues below `m`. -/
theorem lt_of_mem_mulXSubMod {k : ℕ} {l : List ℕ} {a : ℕ} (h : a ∈ mulXSubMod m k l) : a < m := by
  obtain ⟨q, -, rfl⟩ := List.mem_map.1 h
  exact subMod_lt _ _

/-- The factors of the basis polynomial: `X - k` for `k ≠ j`, and `1` for `k = j`. -/
def factor (j : ℕ) (z : ZMod m) (k : ℕ) : ZMod m := if k == j then 1 else z - k

/-- The value at `z` of the fold defining `basisMod` is the product of the factors times the
value of the start. -/
theorem foldl_basis_eval (j : ℕ) (z : ZMod m) (ks : List ℕ) (acc : List ℕ) :
    evalCoeffList z
      ((ks.foldl (fun acc k => if k == j then acc else mulXSubMod m k acc) acc).map Nat.cast) =
      (ks.map (factor j z)).prod * evalCoeffList z (acc.map Nat.cast) := by
  induction ks generalizing acc with
  | nil => simp
  | cons k ks ih =>
    rw [List.foldl_cons, List.map_cons, List.prod_cons]
    by_cases hk : (k == j) = true
    · simp only [hk, ↓reduceIte, ih, factor, one_mul]
    · simp only [hk, Bool.false_eq_true, ↓reduceIte, ih, factor, evalCoeffList_mulXSubMod]
      ring

omit [NeZero m] in
/-- The length of the fold defining `basisMod`. -/
theorem foldl_basis_length (j : ℕ) (ks : List ℕ) (acc : List ℕ) :
    (ks.foldl (fun acc k => if k == j then acc else mulXSubMod m k acc) acc).length =
      acc.length + ks.countP (fun k => k != j) := by
  induction ks generalizing acc with
  | nil => simp
  | cons k ks ih =>
    rw [List.foldl_cons, List.countP_cons]
    by_cases hk : (k == j) = true
    · have hk' : (k != j) = false := by simpa using hk
      simp only [hk, ↓reduceIte, ih, hk']
      simp
    · have hk' : (k != j) = true := by simpa using hk
      simp only [hk, Bool.false_eq_true, ↓reduceIte, ih, length_mulXSubMod, hk']
      omega

/-- The value of `basisMod` at `z` is the product of the factors `factor j z k`, `k ≤ D`. -/
theorem eval_basisMod (j : ℕ) (D : ℕ) (z : ZMod m) :
    evalCoeffList z ((basisMod m D j).map Nat.cast) =
      ((List.range (D + 1)).map (factor j z)).prod := by
  rw [basisMod, foldl_basis_eval]
  simp

/-- Exactly `D` of the nodes `0, …, D` differ from `j ≤ D`. -/
theorem countP_range_ne {j : ℕ} : ∀ {D : ℕ}, j ≤ D →
    (List.range (D + 1)).countP (fun k => k != j) = D := by
  intro D
  induction D with
  | zero =>
    intro hj
    obtain rfl : j = 0 := by omega
    simp
  | succ D ih =>
    intro hj
    rw [List.range_succ, List.countP_append]
    rcases Nat.lt_or_ge j (D + 1) with h | h
    · have := ih (by omega)
      simp [this]
      omega
    · obtain rfl : j = D + 1 := by omega
      rw [List.countP_eq_length.2]
      · simp
      · intro k hk
        have := List.mem_range.1 hk
        simp
        omega

omit [NeZero m] in
/-- The basis polynomial has `D + 1` coefficients, for `j ≤ D`. -/
theorem length_basisMod {D j : ℕ} (hj : j ≤ D) : (basisMod m D j).length = D + 1 := by
  rw [basisMod, foldl_basis_length, countP_range_ne hj]
  simp
  omega

/-- The cast of the fold defining `denomMod` into `ZMod m`. -/
theorem foldl_denom_cast (j : ℕ) (ks : List ℕ) (acc : ℕ) :
    ((ks.foldl (fun acc k => if k == j then acc else acc * subMod m j k % m) acc : ℕ) :
        ZMod m) =
      (ks.map (factor j (j : ZMod m))).prod * acc := by
  induction ks generalizing acc with
  | nil => simp
  | cons k ks ih =>
    rw [List.foldl_cons, List.map_cons, List.prod_cons, factor]
    by_cases hk : k == j
    · simp only [hk, ite_true] at ih ⊢
      rw [ih]
      simp
    · simp only [hk, Bool.false_eq_true, ↓reduceIte] at ih ⊢
      rw [ih, ZMod.natCast_mod, Nat.cast_mul, natCast_subMod]
      ring

/-- The denominator is the value of the basis polynomial at its node. -/
theorem natCast_denomMod (D j : ℕ) :
    ((denomMod m D j : ℕ) : ZMod m) = ((List.range (D + 1)).map (factor j (j : ZMod m))).prod := by
  rw [denomMod, foldl_denom_cast, ZMod.natCast_mod]
  simp

omit [NeZero m] in
/-- Iterated multiplication by `a` modulo `m` multiplies by a power of `a` in `ZMod m`. -/
theorem natCast_iterate_mul (a n c : ℕ) :
    (((fun acc => acc * a % m)^[n] c : ℕ) : ZMod m) = (c : ZMod m) * (a : ZMod m) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ZMod.natCast_mod, Nat.cast_mul, ih]
    ring

omit [NeZero m] in
/-- `invMod m a` is `a ^ (m - 2)` in `ZMod m`. -/
theorem natCast_invMod (a : ℕ) : ((invMod m a : ℕ) : ZMod m) = (a : ZMod m) ^ (m - 2) := by
  rw [invMod, natCast_iterate_mul, ZMod.natCast_mod]
  simp

omit [NeZero m] in
/-- Scaling a coefficient list scales its value. -/
theorem evalCoeffList_scaleMod (s : ℕ) (z : ZMod m) (l : List ℕ) :
    evalCoeffList z ((scaleMod m s l).map Nat.cast) =
      (s : ZMod m) * evalCoeffList z (l.map Nat.cast) := by
  induction l with
  | nil => simp [scaleMod]
  | cons a l ih =>
    simp only [scaleMod, List.map_cons, evalCoeffList_cons] at ih ⊢
    rw [ZMod.natCast_mod, ih]
    push_cast
    ring

omit [NeZero m] in
/-- Scaling keeps the length. -/
theorem length_scaleMod (s : ℕ) (l : List ℕ) : (scaleMod m s l).length = l.length := by
  simp [scaleMod]

omit [NeZero m] in
/-- Adding coefficient lists of equal length adds their values. -/
theorem evalCoeffList_addListMod (z : ZMod m) {a b : List ℕ} (h : a.length = b.length) :
    evalCoeffList z ((addListMod m a b).map Nat.cast) =
      evalCoeffList z (a.map Nat.cast) + evalCoeffList z (b.map Nat.cast) := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => simp [addListMod]
    | cons _ _ => simp at h
  | cons x a ih =>
    cases b with
    | nil => simp at h
    | cons y b =>
      have := ih (b := b) (by simpa using h)
      simp only [addListMod, List.zip_cons_cons, List.map_cons, evalCoeffList_cons] at this ⊢
      rw [ZMod.natCast_mod, Nat.cast_add, this]
      ring

omit [NeZero m] in
/-- Adding coefficient lists of equal length keeps the length. -/
theorem length_addListMod {a b : List ℕ} (h : a.length = b.length) :
    (addListMod m a b).length = a.length := by
  simp [addListMod, h]

/-- The entries of `addListMod` are residues below `m`. -/
theorem lt_of_mem_addListMod {a b : List ℕ} {x : ℕ} (h : x ∈ addListMod m a b) : x < m := by
  obtain ⟨q, -, rfl⟩ := List.mem_map.1 h
  exact Nat.mod_lt _ (NeZero.pos m)

omit [NeZero m] in
/-- The zero list evaluates to `0`. -/
theorem evalCoeffList_replicate_zero (z : ZMod m) (n : ℕ) :
    evalCoeffList z ((List.replicate n 0).map Nat.cast) = 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, List.map_cons, evalCoeffList_cons, ih]; simp

/-- The invariant of the Lagrange sum: after adding the terms of the nodes `js`, the list has
length `D + 1`, its entries are residues, and its value at `z` is the sum of the values of the
terms. -/
theorem foldl_interp (D : ℕ) (vals : List ℕ) (z : ZMod m) (js : List ℕ)
    (hjs : ∀ j ∈ js, j ≤ D) (acc : List ℕ) (hlen : acc.length = D + 1) (hlt : ∀ a ∈ acc, a < m) :
    (js.foldl (fun acc j => addListMod m acc (scaleMod m (weightMod m D vals j) (basisMod m D j)))
        acc).length = D + 1 ∧
    (∀ a ∈ js.foldl
        (fun acc j => addListMod m acc (scaleMod m (weightMod m D vals j) (basisMod m D j))) acc,
        a < m) ∧
    evalCoeffList z ((js.foldl
        (fun acc j => addListMod m acc (scaleMod m (weightMod m D vals j) (basisMod m D j)))
        acc).map Nat.cast) =
      evalCoeffList z (acc.map Nat.cast) +
        (js.map fun j => (weightMod m D vals j : ZMod m) *
          ((List.range (D + 1)).map (factor j z)).prod).sum := by
  induction js generalizing acc with
  | nil => exact ⟨hlen, hlt, by simp⟩
  | cons j js ih =>
    have hj := hjs j List.mem_cons_self
    have hb : (scaleMod m (weightMod m D vals j) (basisMod m D j)).length = acc.length := by
      rw [length_scaleMod, length_basisMod hj, hlen]
    obtain ⟨h1, h2, h3⟩ := ih (fun i hi => hjs i (List.mem_cons_of_mem _ hi))
      (addListMod m acc (scaleMod m (weightMod m D vals j) (basisMod m D j)))
      (by rw [length_addListMod hb.symm, hlen]) (fun a ha => lt_of_mem_addListMod ha)
    refine ⟨h1, h2, ?_⟩
    rw [List.foldl_cons, h3, evalCoeffList_addListMod z hb.symm, evalCoeffList_scaleMod,
      eval_basisMod, List.map_cons, List.sum_cons]
    ring

/-- The Lagrange sum has `D + 1` coefficients. -/
theorem length_interpModAux (D : ℕ) (vals : List ℕ) : (interpModAux m D vals).length = D + 1 :=
  (foldl_interp D vals 0 (List.range (D + 1)) (fun j hj => Nat.lt_succ_iff.1 (List.mem_range.1 hj))
    _ (by simp) (fun a ha => by obtain rfl := (List.mem_replicate.1 ha).2; exact NeZero.pos m)).1

/-- The coefficients of the Lagrange sum are residues below `m`. -/
theorem lt_of_mem_interpModAux {D a : ℕ} {vals : List ℕ} (h : a ∈ interpModAux m D vals) :
    a < m :=
  (foldl_interp D vals 0 (List.range (D + 1)) (fun j hj => Nat.lt_succ_iff.1 (List.mem_range.1 hj))
    _ (by simp)
    (fun a ha => by obtain rfl := (List.mem_replicate.1 ha).2; exact NeZero.pos m)).2.1 a h

/-- The value of the Lagrange sum at `z` is the sum of the weighted basis values. -/
theorem evalCoeffList_interpModAux_eq (D : ℕ) (vals : List ℕ) (z : ZMod m) :
    evalCoeffList z ((interpModAux m D vals).map Nat.cast) =
      ((List.range (D + 1)).map fun j => (weightMod m D vals j : ZMod m) *
          ((List.range (D + 1)).map (factor j z)).prod).sum := by
  have := (foldl_interp D vals z (List.range (D + 1))
    (fun j hj => Nat.lt_succ_iff.1 (List.mem_range.1 hj))
    (List.replicate (D + 1) 0) (by simp)
    (fun a ha => by obtain rfl := (List.mem_replicate.1 ha).2; exact NeZero.pos m)).2.2
  rw [evalCoeffList_replicate_zero, zero_add] at this
  exact this

/-- A sum over `range n` with a single possibly nonzero term. -/
theorem sum_map_range_single {M : Type*} [AddCommMonoid M] (g : ℕ → M) (i : ℕ) :
    ∀ n, i < n → (∀ j, j < n → j ≠ i → g j = 0) → ((List.range n).map g).sum = g i := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro hi hg
    rw [List.range_succ, List.map_append, List.sum_append]
    rcases Nat.lt_or_ge i n with h | h
    · rw [ih h (fun j hj => hg j (by omega))]
      simp [hg n (by omega) (by omega)]
    · obtain rfl : i = n := by omega
      rw [List.sum_eq_zero]
      · simp
      · intro x hx
        obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
        exact hg j (by have := List.mem_range.1 hj; omega) (by have := List.mem_range.1 hj; omega)

end Algebra

section Prime

variable {p : ℕ} [Fact p.Prime]

/-- Distinct nodes below `p` are distinct in `ZMod p`. -/
private theorem natCast_inj_of_le {D a b : ℕ} (hD : D < p) (ha : a ≤ D) (hb : b ≤ D)
    (h : (a : ZMod p) = b) : a = b := by
  rw [ZMod.natCast_eq_natCast_iff'] at h
  rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h

/-- **Interpolation**: the polynomial given by `interpModAux` takes the value `vals[i]` at each
node `i ≤ D`. -/
theorem evalCoeffList_interpModAux {D : ℕ} (hD : D < p) (vals : List ℕ) {i : ℕ} (hi : i ≤ D) :
    evalCoeffList (i : ZMod p) ((interpModAux p D vals).map Nat.cast) =
      (vals.getD i 0 : ZMod p) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [evalCoeffList_interpModAux_eq]
  have hzero : ∀ j, j < D + 1 → j ≠ i →
      (weightMod p D vals j : ZMod p) *
        ((List.range (D + 1)).map (factor j (i : ZMod p))).prod = 0 := by
    intro j _ hji
    rw [List.prod_eq_zero (List.mem_map.2 ⟨i, List.mem_range.2 (by omega), ?_⟩), mul_zero]
    have h : ¬ (i == j) = true := fun h => hji (beq_iff_eq.1 h).symm
    simp only [factor, h, Bool.false_eq_true, ↓reduceIte, sub_self]
  rw [sum_map_range_single _ i (D + 1) (by omega) hzero]
  have hd : ((List.range (D + 1)).map (factor i (i : ZMod p))).prod ≠ 0 := by
    refine List.prod_ne_zero fun h0 => ?_
    obtain ⟨k, hk, hk0⟩ := List.mem_map.1 h0
    rw [factor] at hk0
    split_ifs at hk0 with hki
    · exact one_ne_zero hk0
    · have := natCast_inj_of_le hD hi (by have := List.mem_range.1 hk; omega) (sub_eq_zero.1 hk0)
      exact hki (by rw [this]; simp)
  rw [weightMod, ZMod.natCast_mod, Nat.cast_mul, ZMod.natCast_mod, natCast_invMod,
    natCast_denomMod, mul_assoc]
  rw [← pow_succ, show p - 2 + 1 = p - 1 by
    have := (Fact.out : p.Prime).two_le; omega, ZMod.pow_card_sub_one_eq_one hd, mul_one]

end Prime

/-! ### Main results -/

/-- The interpolated list has `D + 1` coefficients. -/
theorem length_interpMod (p D : ℕ) (vals : List ℕ) : (interpMod p D vals).length = D + 1 := by
  have : NeZero (p - 1 + 1) := ⟨by omega⟩
  exact length_interpModAux D vals

/-- The coefficients are residues below `p`. -/
theorem lt_of_mem_interpMod {p D : ℕ} (hp : 0 < p) {vals : List ℕ} {a : ℕ}
    (h : a ∈ interpMod p D vals) : a < p := by
  have : NeZero (p - 1 + 1) := ⟨by omega⟩
  have := lt_of_mem_interpModAux h
  omega

section Prime

variable {p : ℕ} [Fact p.Prime]

/-- For a prime `p`, `interpMod p` is the Lagrange sum modulo `p`. -/
theorem interpMod_eq_interpModAux (D : ℕ) (vals : List ℕ) :
    interpMod p D vals = interpModAux p D vals := by
  rw [interpMod, Nat.sub_add_cancel (Fact.out : p.Prime).pos]

/-- **Interpolation property**: the polynomial with coefficients `interpMod p D vals` takes the
value `vals[i]` at each node `i ≤ D`, over `ZMod p`. -/
theorem evalCoeffList_interpMod {D : ℕ} (hD : D < p) (vals : List ℕ) {i : ℕ} (hi : i ≤ D) :
    evalCoeffList (i : ZMod p) ((interpMod p D vals).map Nat.cast) =
      (vals.getD i 0 : ZMod p) := by
  rw [interpMod_eq_interpModAux]
  exact evalCoeffList_interpModAux hD vals hi

/-- **Exactness**: interpolating the values at `0, …, D` of a polynomial over `ZMod p` of degree
at most `D < p` returns its first `D + 1` coefficients. -/
theorem map_natCast_interpMod {D : ℕ} (hD : D < p) {f : Polynomial (ZMod p)}
    (hf : f.natDegree ≤ D) :
    (interpMod p D ((List.range (D + 1)).map fun i : ℕ => (f.eval (i : ZMod p)).val)).map
        (Nat.cast : ℕ → ZMod p) = coeffsBelow f (D + 1) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  set vals : List ℕ := (List.range (D + 1)).map fun i : ℕ => (f.eval (i : ZMod p)).val with hvals
  set L := (interpMod p D vals).map (Nat.cast : ℕ → ZMod p) with hL
  have hlen : L.length = D + 1 := by rw [hL, List.length_map, length_interpMod]
  have hval (i : ℕ) (hi : i ≤ D) : vals.getD i 0 = (f.eval (i : ZMod p)).val := by
    rw [hvals, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
    rfl
  have hg : (ofCoeffList L).natDegree ≤ D := by
    have := natDegree_ofCoeffList_le L
    omega
  have hfg : f = ofCoeffList L := by
    refine eq_of_natDegree_lt_card_of_eval_eq f (ofCoeffList L)
      (f := fun i : Fin (D + 1) => ((i : ℕ) : ZMod p)) ?_ ?_ ?_
    · intro a b hab
      exact Fin.ext (by
        have := (ZMod.natCast_eq_natCast_iff' _ _ _).1 hab
        rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this)
    · intro i
      rw [eval_ofCoeffList, hL, evalCoeffList_interpMod hD vals (by omega), hval i (by omega),
        ZMod.natCast_zmod_val]
    · rw [Fintype.card_fin]
      omega
  refine List.ext_getElem (by rw [hlen, length_coeffsBelow]) fun i h1 h2 => ?_
  simp only [Polynomial.coeffsBelow, List.getElem_map, List.getElem_range]
  rw [hfg, coeff_ofCoeffList, List.getD_eq_getElem _ _ h1]

end Prime

/-! ### Polynomial time -/

section PolyTime

open Turing.MultiTapeTM ComputableInPolyTime

variable {γ : Type} {encIn : γ ↪ List Bool}

/-- Multiplying by `X - k` modulo `m` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_mulXSubMod {m k : γ → ℕ} {l : γ → List ℕ}
    (hm : ComputableInPolyTime m encIn encUnary)
    (hk : ComputableInPolyTime k encIn encUnary)
    (hl : ComputableInPolyTime l encIn (encList encUnary)) :
    ComputableInPolyTime (fun x => mulXSubMod (m x) (k x) (l x)) encIn (encList encUnary) := by
  unfold mulXSubMod
  have hz : ComputableInPolyTime (fun x => (0 :: l x).zip (l x ++ [0])) encIn
      (encList (encPair encUnary encUnary)) :=
    (zip encUnary encUnary).comp ((cons' (const 0) hl).prod (listAppend' hl (const [0])))
  exact mapWithInput hz (by fun_prop)

/-- The Lagrange basis polynomial modulo `m > 0` is polynomial-time. -/
theorem computableInPolyTime_basisMod {m D j : γ → ℕ} (hm0 : ∀ x, 0 < m x)
    (hm : ComputableInPolyTime m encIn encUnary)
    (hD : ComputableInPolyTime D encIn encUnary)
    (hj : ComputableInPolyTime j encIn encUnary) :
    ComputableInPolyTime (fun x => basisMod (m x) (D x) (j x)) encIn (encList encUnary) := by
  have hr : ComputableInPolyTime (fun x => List.range (D x + 1)) encIn (encList encUnary) := by
    fun_prop
  have hpar : ComputableInPolyTime (fun x => (m x, j x)) encIn (encPair encUnary encUnary) :=
    hm.prod hj
  have hinit : ComputableInPolyTime (fun x => [1 % m x]) encIn (encList encUnary) := by
    fun_prop
  have hstep : ComputableInPolyTime
      (fun q : ((ℕ × ℕ) × List ℕ) × ℕ =>
        if q.2 == q.1.1.2 then q.1.2 else mulXSubMod q.1.1.1 q.2 q.1.2)
      (encPair (encPair (encPair encUnary encUnary) (encList encUnary)) encUnary)
      (encList encUnary) := by
    fun_prop
  refine (foldlWith_spec (encA := encUnary) (encL := encList encUnary)
    (step := fun (π : ℕ × ℕ) (acc : List ℕ) (k : ℕ) =>
      if k == π.2 then acc else mulXSubMod π.1 k acc) hpar hr hinit hstep
    (fun x consumed state => state.length ≤ consumed.length + 1 ∧ ∀ a ∈ state, a < m x)
    (fun x => ⟨by simp, by simpa using Nat.mod_lt 1 (hm0 x)⟩) ?_
    (size := fun x => (D x + 2) * (2 * m x + 1))
    (((hD.polyBounded).add (.const 2)).mul
      (((PolyBounded.const 2).mul hm.polyBounded).add (.const 1))) ?_).1
  · intro x consumed state value hpre ⟨h1, h2⟩
    simp only [List.length_append, List.length_singleton]
    by_cases hk : (value == j x) = true
    · simp only [hk, ↓reduceIte]
      exact ⟨by omega, h2⟩
    · have : NeZero (m x) := ⟨(hm0 x).ne'⟩
      simp only [hk, Bool.false_eq_true, ↓reduceIte]
      exact ⟨by rw [length_mulXSubMod]; omega, fun a ha => lt_of_mem_mulXSubMod ha⟩
  · intro x consumed state hpre ⟨h1, h2⟩
    have hc : consumed.length ≤ D x + 1 := by simpa using hpre.length_le
    refine (length_encList_le encUnary state (b := m x)
      fun a ha => by simpa using (h2 a ha).le).trans ?_
    exact Nat.mul_le_mul (by omega) le_rfl

/-- The sum of two coefficient lists modulo `m` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_addListMod {m : γ → ℕ} {a b : γ → List ℕ}
    (hm : ComputableInPolyTime m encIn encUnary)
    (ha : ComputableInPolyTime a encIn (encList encUnary))
    (hb : ComputableInPolyTime b encIn (encList encUnary)) :
    ComputableInPolyTime (fun x => addListMod (m x) (a x) (b x)) encIn (encList encUnary) := by
  unfold addListMod
  have hz : ComputableInPolyTime (fun x => (a x).zip (b x)) encIn
      (encList (encPair encUnary encUnary)) := (zip encUnary encUnary).comp (ha.prod hb)
  exact mapWithInput hz (by fun_prop)

/-- Scaling a coefficient list modulo `m` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_scaleMod {m s : γ → ℕ} {l : γ → List ℕ}
    (hm : ComputableInPolyTime m encIn encUnary)
    (hs : ComputableInPolyTime s encIn encUnary)
    (hl : ComputableInPolyTime l encIn (encList encUnary)) :
    ComputableInPolyTime (fun x => scaleMod (m x) (s x) (l x)) encIn (encList encUnary) := by
  unfold scaleMod
  exact mapWithInput hl (by fun_prop)

/-- The denominator of a Lagrange weight modulo `m > 0` is polynomial-time. -/
theorem computableInPolyTime_denomMod {m D j : γ → ℕ} (hm0 : ∀ x, 0 < m x)
    (hm : ComputableInPolyTime m encIn encUnary)
    (hD : ComputableInPolyTime D encIn encUnary)
    (hj : ComputableInPolyTime j encIn encUnary) :
    ComputableInPolyTime (fun x => denomMod (m x) (D x) (j x)) encIn encUnary := by
  unfold denomMod
  refine foldlWithInput_of_bounded_growth (encA := encUnary) (encL := encList encUnary)
    (list := fun x => List.range (D x + 1))
    (step := fun x acc k => if k == j x then acc else acc * subMod (m x) (j x) k % m x)
    (by fun_prop) ⟨by fun_prop, by fun_prop, inferInstance, inferInstance⟩
    (growth := fun x => m x + 1) ⟨hm.polyBounded.add (.const 1), fun x acc k _ => ?_⟩
  simp only [encUnary_apply, List.length_replicate]
  split_ifs
  · omega
  · have := Nat.mod_lt (acc * subMod (m x) (j x) k) (hm0 x)
    omega

/-- The inverse modulo `m > 0` by iterated multiplication is polynomial-time. -/
theorem computableInPolyTime_invMod {m a : γ → ℕ} (hm0 : ∀ x, 0 < m x)
    (hm : ComputableInPolyTime m encIn encUnary)
    (ha : ComputableInPolyTime a encIn encUnary) :
    ComputableInPolyTime (fun x => invMod (m x) (a x)) encIn encUnary := by
  unfold invMod
  refine iterateWithInput_of_bounded_growth (encState := encUnary)
    (step := fun x acc => acc * a x % m x) (by fun_prop) (by fun_prop) (by fun_prop)
    (growth := fun x => m x + 1) ⟨hm.polyBounded.add (.const 1), fun x acc => ?_⟩
  simp only [encUnary_apply, List.length_replicate]
  have := Nat.mod_lt (acc * a x) (hm0 x)
  omega

/-- The Lagrange weight of a node modulo `m > 0` is polynomial-time. -/
theorem computableInPolyTime_weightMod {m D j : γ → ℕ} {vals : γ → List ℕ}
    (hm0 : ∀ x, 0 < m x)
    (hm : ComputableInPolyTime m encIn encUnary)
    (hD : ComputableInPolyTime D encIn encUnary)
    (hvals : ComputableInPolyTime vals encIn (encList encUnary))
    (hj : ComputableInPolyTime j encIn encUnary) :
    ComputableInPolyTime (fun x => weightMod (m x) (D x) (vals x) (j x)) encIn encUnary := by
  have hd := computableInPolyTime_denomMod hm0 hm hD hj
  have hi := computableInPolyTime_invMod hm0 hm hd
  unfold weightMod
  have hg : ComputableInPolyTime (fun x => (vals x).getD (j x) 0) encIn encUnary :=
    listGetDWithInput hvals hj 0
  fun_prop

/-- The Lagrange sum modulo `m > 0` is polynomial-time. -/
theorem computableInPolyTime_interpModAux {m D : γ → ℕ} {vals : γ → List ℕ}
    (hm0 : ∀ x, 0 < m x)
    (hm : ComputableInPolyTime m encIn encUnary)
    (hD : ComputableInPolyTime D encIn encUnary)
    (hvals : ComputableInPolyTime vals encIn (encList encUnary)) :
    ComputableInPolyTime (fun x => interpModAux (m x) (D x) (vals x)) encIn
      (encList encUnary) := by
  unfold interpModAux
  have hstep : ComputableInPolyTime
      (fun q : (γ × List ℕ) × ℕ => addListMod (m q.1.1) q.1.2
        (scaleMod (m q.1.1) (weightMod (m q.1.1) (D q.1.1) (vals q.1.1) q.2)
          (basisMod (m q.1.1) (D q.1.1) q.2)))
      (encPair (encPair encIn (encList encUnary)) encUnary) (encList encUnary) := by
    have hm' : ComputableInPolyTime (fun q : (γ × List ℕ) × ℕ => m q.1.1)
        (encPair (encPair encIn (encList encUnary)) encUnary) encUnary := by fun_prop
    have hD' : ComputableInPolyTime (fun q : (γ × List ℕ) × ℕ => D q.1.1)
        (encPair (encPair encIn (encList encUnary)) encUnary) encUnary := by fun_prop
    have hvals' : ComputableInPolyTime (fun q : (γ × List ℕ) × ℕ => vals q.1.1)
        (encPair (encPair encIn (encList encUnary)) encUnary) (encList encUnary) := by fun_prop
    have hj' : ComputableInPolyTime (fun q : (γ × List ℕ) × ℕ => q.2)
        (encPair (encPair encIn (encList encUnary)) encUnary) encUnary := by fun_prop
    have hacc : ComputableInPolyTime (fun q : (γ × List ℕ) × ℕ => q.1.2)
        (encPair (encPair encIn (encList encUnary)) encUnary) (encList encUnary) := by fun_prop
    exact computableInPolyTime_addListMod hm' hacc
      (computableInPolyTime_scaleMod hm'
        (computableInPolyTime_weightMod (fun q => hm0 _) hm' hD' hvals' hj')
        (computableInPolyTime_basisMod (fun q => hm0 _) hm' hD' hj'))
  refine foldlWithInput_of_bounded_growth (encA := encUnary) (encL := encList encUnary)
    (list := fun x => List.range (D x + 1))
    (step := fun x acc j => addListMod (m x) acc
      (scaleMod (m x) (weightMod (m x) (D x) (vals x) j) (basisMod (m x) (D x) j)))
    (by fun_prop) ⟨by fun_prop, hstep, inferInstance, inferInstance⟩
    (growth := fun x => (D x + 1) * (2 * m x + 1))
    ⟨(hD.polyBounded.add (.const 1)).mul (((PolyBounded.const 2).mul hm.polyBounded).add
      (.const 1)), fun x acc j hj => ?_⟩
  have hjD : j ≤ D x := Nat.lt_succ_iff.1 (List.mem_range.1 hj)
  have : NeZero (m x) := ⟨(hm0 x).ne'⟩
  refine (length_encList_le encUnary _ (b := m x)
    (fun a ha => by simpa using (lt_of_mem_addListMod ha).le)).trans ?_
  have hl : (addListMod (m x) acc (scaleMod (m x) (weightMod (m x) (D x) (vals x) j)
      (basisMod (m x) (D x) j))).length ≤ D x + 1 := by
    simp only [addListMod, List.length_map, List.length_zip, length_scaleMod,
      length_basisMod hjD]
    exact Nat.min_le_right _ _
  exact (Nat.mul_le_mul hl le_rfl).trans (Nat.le_add_left _ _)

/-- **Interpolation modulo `p` is polynomial-time** in `p`, `D` and the values, all in unary, with
output the coefficient list in unary. -/
theorem computableInPolyTime_interpMod {p D : γ → ℕ} {vals : γ → List ℕ}
    (hp : ComputableInPolyTime p encIn encUnary)
    (hD : ComputableInPolyTime D encIn encUnary)
    (hvals : ComputableInPolyTime vals encIn (encList encUnary)) :
    ComputableInPolyTime (fun x => interpMod (p x) (D x) (vals x)) encIn
      (encList encUnary) := by
  unfold interpMod
  exact computableInPolyTime_interpModAux (m := fun x => p x - 1 + 1) (fun x => by omega)
    (by fun_prop) hD hvals

end PolyTime

end Cslib.Complexity.QBFProtocol
