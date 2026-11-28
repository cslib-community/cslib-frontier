/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.SharpP.Metric
public import CslibFrontier.Computability.Complexity.Problems.Permanent.ZeroOne.Integer
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Factorial
import CslibFrontier.Tactic.PolyTime

/-!
# Goldreich's Proposition 6.22: integer permanents reduce to 0/1 permanents

Goldreich's Proposition 6.22 [Goldreich2007Draft] states that computing the permanent of integer
matrices reduces to computing the permanent of 0/1 matrices, by a map sending an integer matrix
`A` to a 0/1 matrix `A''` such that the permanent of `A` is easily computed from `A` and the
permanent of `A''`. This file supplies the polynomial-time certificates for the two steps of the
proof in `Problems.Permanent.ZeroOne.Basic` and `Problems.Permanent.ZeroOne.Integer` and states
the result as a metric reduction (`metricReducible_intPermanent_zeroOnePermanent`), the step used
by Valiant's theorem [Valiant][Valiant1979].

All maps are native multi-tape machine constructions under explicit encodings: integer tables
under `encIntTable`, tables of natural numbers under `encNatTable` (binary entries), 0/1 tables
under `encBoolTable`, and the intermediate weighted edge lists with unary endpoints. The 0/1 table
of an `n × n` table has dimension `n + 2 L n²`, where `L` is the binary length of the sum of
the entries (`length_natTableToZeroOne`); for an integer table the entries are first reduced
modulo `Q = 2 · n! · S ^ n + 1`, so `L` is polynomial in the encoded input length.

## Main definitions

* `Cslib.Complexity.encNatTable`, `Cslib.Complexity.encWeightedEdgeList`,
  `Cslib.Complexity.encWeightedEdgeList`, `Cslib.Complexity.encChainLevelInput`: encodings.
* `Cslib.Complexity.NatPermanent`: the permanent of a table of natural numbers.
* `Cslib.Complexity.intTableToZeroOne`: the query map of Proposition 6.22.

## Main results

* `Cslib.Complexity.computableInPolyTime_natTableToZeroOne`,
  `Cslib.Complexity.computableInPolyTime_intTableToZeroOne`,
  `Cslib.Complexity.computableInPolyTime_recoverPermanent`: the maps are polynomial-time.
* `Cslib.Complexity.parsimoniousReducible_natPermanent_zeroOnePermanent`: the nonnegative step is
  a parsimonious reduction.
* `Cslib.Complexity.intPermanent_eq_recoverPermanent_intTableToZeroOne`,
  `Cslib.Complexity.metricReducible_intPermanent_zeroOnePermanent`: **Proposition 6.22**.

## References

* [L. Valiant, *The complexity of computing the permanent*][Valiant1979]
* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, 2007 draft]
  [Goldreich2007Draft]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime PermanentZeroOne

/-- Tables of natural numbers, densely: the framed list of rows, each row the framed list of its
entries in binary (`encNat`). -/
abbrev encNatTable : List (List ℕ) ↪ List Bool :=
  encList (encList encNat)

/-- Lists of weighted edges, each the tuple of its fields: endpoints in unary and the weight in
binary (`encWeightedEdge`). -/
abbrev encWeightedEdgeList : List WeightedEdge ↪ List Bool :=
  encList encWeightedEdge

theorem computableInPolyTime_natTableTriples :
    ComputableInPolyTime natTableTriples encNatTable encWeightedEdgeList := by
  unfold natTableTriples gridEdges natTableEntry
  refine flatMapWithInput (range.comp (by fun_prop)) ?_
  refine mapWithInput (range.comp (by fun_prop)) ?_
  fun_prop

theorem computableInPolyTime_natChainLength :
    ComputableInPolyTime natChainLength encNatTable encUnary := by
  unfold natChainLength
  have hw : ComputableInPolyTime (fun A => (natTableTriples A).map WeightedEdge.weight)
      encNatTable (encList encNat) :=
    mapWithInput computableInPolyTime_natTableTriples (by fun_prop)
  exact binary_size.comp (by fun_prop)

/-- `tableChain` as one `flatMap` over the indexed entries. -/
theorem tableChain_eq_flatMap (L : ℕ) (ts : List WeightedEdge) :
    ∀ (N k : ℕ), tableChain (N + 2 * L * k) L ts =
      (ts.zipIdx k).flatMap fun p => entryChain (N + 2 * L * p.2) p.1.src p.1.dst p.1.weight L := by
  induction ts with
  | nil => intros; rfl
  | cons t ts ih =>
    intro N k
    rw [tableChain_cons, List.zipIdx_cons, List.flatMap_cons,
      show N + 2 * L * k + 2 * L = N + 2 * L * (k + 1) by ring, ih]

/-- The arguments `((N, u, v, w), k)` of `chainLevel`: `N`, `u`, `v` and `k` in unary, the weight
`w` in binary. -/
abbrev encChainLevelInput : (ℕ × ℕ × ℕ × ℕ) × ℕ ↪ List Bool :=
  encPair (encPair encUnary (encPair encUnary (encPair encUnary encNat))) encUnary

theorem computableInPolyTime_chainLevel :
    ComputableInPolyTime (fun x : (ℕ × ℕ × ℕ × ℕ) × ℕ =>
        chainLevel x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2 x.2)
      encChainLevelInput encWeightedEdgeList := by
  have hd : ComputableInPolyTime (fun x : (ℕ × ℕ × ℕ × ℕ) × ℕ => x.1.1 + 2 * x.2)
      encChainLevelInput encUnary := by fun_prop
  have hr : ComputableInPolyTime (fun x : (ℕ × ℕ × ℕ × ℕ) × ℕ => x.1.1 + 2 * x.2 + 1)
      encChainLevelInput encUnary := by fun_prop
  have htgt : ComputableInPolyTime (fun x : (ℕ × ℕ × ℕ × ℕ) × ℕ =>
      if x.2 = 0 then x.1.2.2.1 else x.1.1 + 2 * x.2 - 2) encChainLevelInput encUnary := by
    fun_prop
  have hbit : ComputableInPolyTime (fun x : (ℕ × ℕ × ℕ × ℕ) × ℕ =>
      if x.1.2.2.2.testBit x.2 then 1 else 0) encChainLevelInput encNat := by
    have hw : ComputableInPolyTime (fun x : (ℕ × ℕ × ℕ × ℕ) × ℕ => x.1.2.2.2)
        encChainLevelInput encNat := by fun_prop
    convert (of_finite (encIn := encBool) (encOut := encNat) Bool.toNat).comp
      (binary_testBit hw (snd _ _)) using 2 with x
    simp only [Function.comp_apply]
    cases x.1.2.2.2.testBit x.2 <;> rfl
  have he {a b c : (ℕ × ℕ × ℕ × ℕ) × ℕ → ℕ}
      (ha : ComputableInPolyTime a encChainLevelInput encUnary)
      (hb : ComputableInPolyTime b encChainLevelInput encUnary)
      (hc : ComputableInPolyTime c encChainLevelInput encNat) :=
    encWeightedEdge_mk_polyTime ha hb hc
  unfold chainLevel
  exact cons' (he (by fun_prop) htgt hbit) (cons' (he hd hd (const 1))
    (cons' (he hd htgt (const 1)) (cons' (he hr hr (const 1))
      (cons' (he hd hr (const 1)) (cons' (he hr htgt (const 1)) (const _))))))

theorem natTableEdges_eq (A : List (List ℕ)) :
    natTableEdges A = ((natTableTriples A).zipIdx).flatMap fun p =>
      entryChain (A.length + 2 * natChainLength A * p.2) p.1.src p.1.dst p.1.weight
        (natChainLength A) := by
  rw [natTableEdges, ← tableChain_eq_flatMap _ _ A.length 0]
  simp

theorem computableInPolyTime_natTableEdges :
    ComputableInPolyTime natTableEdges encNatTable encWeightedEdgeList := by
  have hL := computableInPolyTime_natChainLength
  rw [show natTableEdges = _ from funext natTableEdges_eq]
  refine flatMapWithInput ((zipIdx _).comp computableInPolyTime_natTableTriples) ?_
  unfold entryChain
  refine flatMapWithInput (range.comp (hL.comp (fst _ _))) ?_
  have := hL.comp ((fst encNatTable (encPair encWeightedEdge encUnary)).comp
    (fst (encPair encNatTable (encPair encWeightedEdge encUnary)) encUnary))
  have hargs : ComputableInPolyTime
      (fun x : (List (List ℕ) × (WeightedEdge × ℕ)) × ℕ =>
        ((x.1.1.length + 2 * natChainLength x.1.1 * x.1.2.2, x.1.2.1.src, x.1.2.1.dst,
          x.1.2.1.weight), x.2))
      (encPair (encPair encNatTable (encPair encWeightedEdge encUnary)) encUnary)
      encChainLevelInput := by fun_prop
  simpa only [Function.comp_def] using computableInPolyTime_chainLevel.comp hargs

theorem computableInPolyTime_natTableDim :
    ComputableInPolyTime natTableDim encNatTable encUnary := by
  have hL := computableInPolyTime_natChainLength
  unfold natTableDim
  fun_prop

theorem computableInPolyTime_edgeTable :
    ComputableInPolyTime (fun x : ℕ × List WeightedEdge => edgeTable x.1 x.2)
      (encPair encUnary encWeightedEdgeList) encBoolTable := by
  unfold edgeTable
  refine mapWithInput (range.comp (by fun_prop)) ?_
  refine mapWithInput (range.comp (by fun_prop)) ?_
  refine anyWithInput (by fun_prop) ?_
  fun_prop

/-- **The nonnegative step of Proposition 6.22 is polynomial-time.** -/
theorem computableInPolyTime_natTableToZeroOne :
    ComputableInPolyTime natTableToZeroOne encNatTable encBoolTable := by
  have h := computableInPolyTime_edgeTable.comp
    (computableInPolyTime_natTableDim.prod computableInPolyTime_natTableEdges)
  simp only [Function.comp_def] at h
  exact h

theorem computableInPolyTime_intTableAbsSum :
    ComputableInPolyTime intTableAbsSum encIntTable encNat := by
  unfold intTableAbsSum intTableEntry
  have hl : ComputableInPolyTime (fun A : List (List ℤ) =>
      (List.range A.length).flatMap fun i =>
        (List.range A.length).map fun j => ((A.getD i []).getD j 0).natAbs)
      encIntTable (encList encNat) :=
    flatMapWithInput (range.comp (by fun_prop))
      (mapWithInput (range.comp (by fun_prop)) (by fun_prop))
  fun_prop

theorem computableInPolyTime_permanentModulus :
    ComputableInPolyTime permanentModulus encIntTable encNat := by
  change ComputableInPolyTime (fun A => permanentModulus A) _ _
  have hlength := length_list (encList encIntBin)
  simpa only [Function.comp_def, permanentModulus] using
    binary_add' (binary_mul' (binary_mul' (const 2) (binary_factorial.comp hlength))
      (binary_pow' computableInPolyTime_intTableAbsSum hlength)) (const 1)

theorem computableInPolyTime_reduceIntTable :
    ComputableInPolyTime reduceIntTable encIntTable encNatTable := by
  unfold reduceIntTable intTableEntry
  refine mapWithInput (range.comp (by fun_prop))
    (mapWithInput (range.comp (by fun_prop)) ?_)
  exact intBin_emodNat' (by fun_prop) (computableInPolyTime_permanentModulus.comp (by fun_prop))

theorem computableInPolyTime_recoverPermanent :
    ComputableInPolyTime recoverPermanent (encPair encIntTable encNat) encIntBin := by
  have hQ := computableInPolyTime_permanentModulus.comp (fst encIntTable encNat)
  have hresidue := binary_mod' (snd encIntTable encNat) hQ
  unfold recoverPermanent
  exact ite_decide (binary_lt' (binary_mul' (const 2) hresidue) hQ)
    (intBin_natCast.comp hresidue)
    (intBin_sub.comp ((intBin_natCast.comp hresidue).prod (intBin_natCast.comp hQ)))

/-- The permanent of a table of natural numbers. -/
def NatPermanent (A : List (List ℕ)) : ℕ :=
  (tableMatrix A).permanent

/-- **The nonnegative step of Proposition 6.22 as a reduction**: the permanent of tables of
natural numbers reduces parsimoniously to the 0/1 permanent. -/
theorem parsimoniousReducible_natPermanent_zeroOnePermanent :
    ParsimoniousReducible encNatTable encBoolTable NatPermanent ZeroOnePermanent :=
  ⟨natTableToZeroOne, computableInPolyTime_natTableToZeroOne,
    fun A => (zeroOnePermanent_natTableToZeroOne A).symm⟩

/-- The query map of Proposition 6.22: reduce modulo `permanentModulus A`, then replace every
entry by its binary chain. -/
def intTableToZeroOne (A : List (List ℤ)) : List (List Bool) :=
  natTableToZeroOne (reduceIntTable A)

theorem computableInPolyTime_intTableToZeroOne :
    ComputableInPolyTime intTableToZeroOne encIntTable encBoolTable :=
  computableInPolyTime_natTableToZeroOne.comp computableInPolyTime_reduceIntTable

/-- **Goldreich, Proposition 6.22**: computing the permanent of integer matrices reduces to
computing the permanent of 0/1 matrices. The polynomial-time map `intTableToZeroOne` sends an
integer table `A` to a 0/1 table, and the permanent of `A` is computed in polynomial time from `A`
and that 0/1 permanent by `recoverPermanent`. -/
theorem intPermanent_eq_recoverPermanent_intTableToZeroOne (A : List (List ℤ)) :
    IntPermanent A = recoverPermanent (A, ZeroOnePermanent (intTableToZeroOne A)) :=
  intPermanent_eq_recoverPermanent A

/-- **Goldreich, Proposition 6.22, as a metric reduction**: the integer permanent reduces to the
0/1 permanent by one query and polynomial-time recovery. -/
theorem metricReducible_intPermanent_zeroOnePermanent :
    MetricReducible encIntTable encBoolTable encIntBin encNat IntPermanent ZeroOnePermanent :=
  ⟨intTableToZeroOne, recoverPermanent, computableInPolyTime_intTableToZeroOne,
    computableInPolyTime_recoverPermanent, intPermanent_eq_recoverPermanent_intTableToZeroOne⟩

end Cslib.Complexity
