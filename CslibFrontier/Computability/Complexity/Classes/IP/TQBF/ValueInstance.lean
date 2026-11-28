/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.IP.TQBF.Verifier
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length

/-!
# Instances asking for a bit of the value of an arithmetic formula

The language with the properties of [MurrayWilliams2018], Theorem 2.2, that its Theorem 3.1 uses
is built, after [Santhanam2009] and [TrevisanVadhan2007], from the interactive proof of
[Shamir1992] and [Shen1992] (`Cslib.Complexity.QBFProtocol.verifier`). An instance asks for one
bit of the value, modulo a prime `p`, of an arithmetic formula `e` at a point `r` on the variables
`xs`: it is a `Cslib.Complexity.QBFProtocol.ValueInstance`, the parameters and tokens of the
machine (`Cslib.Complexity.QBFProtocol.Machine.LoopInput`), the values of the point and the index
of the bit. This file gives the instances and their arithmetic, which the anchored language of
`CslibFrontier.Computability.Complexity.Classes.IP.TQBF.AnchoredLanguage` builds on.

* **Padding.** The point values and the bit index are written as words of exactly `p` bits, as
  many `true`s as the number followed by `false`s (`Cslib.Complexity.QBFProtocol.padUnary`), so
  that the length of an encoding does not depend on them.
* **Validity** (`Cslib.Complexity.QBFProtocol.ValueInstance.ValidFor`): the tokens are those of
  `e`, `p` is prime, `6 * ops * D + 1 ≤ p` (so that the soundness error of the machine is at most
  `1 / 3`), the round degrees of `e` are at most `D < p`, all variables of `e`, the bound ones
  included, are among `xs`, and the point and the bit are in range.
* **Children.** A subformula of `e` (`Cslib.Complexity.QBFProtocol.IsChild`) with any point and
  any bit is an instance with the same parameters
  (`Cslib.Complexity.QBFProtocol.ValueInstance.child`). The value is computed from the values of
  the children by the equations of `Cslib.Logic.PL.ArithQBF.eval`
  (`Cslib.Complexity.QBFProtocol.ValueInstance.value_not`, `.value_bin`, `.value_op`), where an
  operator binding `v` sets `v` to `0` and to `1` in the point
  (`Cslib.Complexity.QBFProtocol.ValueInstance.setPoint`).

The machine locates the children in a stream of tokens by `Cslib.Complexity.QBFProtocol.firstLen`,
where the first complete formula of a list of tokens ends, which is computable in polynomial time
(`Cslib.Complexity.QBFProtocol.computableInPolyTime_firstLen`).

## Main definitions

* `Cslib.Complexity.QBFProtocol.ValueInstance`, `Cslib.Complexity.QBFProtocol.padUnary`
* `Cslib.Complexity.QBFProtocol.ValueInstance.ValidFor`
* `Cslib.Complexity.QBFProtocol.ValueInstance.value`, `Cslib.Complexity.QBFProtocol.IsChild`
* `Cslib.Complexity.QBFProtocol.firstLen`

## Main results

* `Cslib.Complexity.QBFProtocol.ValueInstance.value_op`: the value of an operator from the values
  of its body.
* `Cslib.Complexity.QBFProtocol.computableInPolyTime_firstLen`: the scan is polynomial-time.

## References

* [C. D. Murray, R. R. Williams, *Circuit lower bounds for nondeterministic quasi-polytime: an
  easy witness lemma for NP and NQP*][MurrayWilliams2018], Theorem 2.2
* [R. Santhanam, *Circuit lower bounds for Merlin–Arthur classes*][Santhanam2009]
* [L. Trevisan, S. Vadhan, *Pseudorandomness and average-case complexity via uniform
  reductions*][TrevisanVadhan2007]
* [A. Shamir, *IP = PSPACE*][Shamir1992]
* [A. Shen, *IP = SPACE: simplified proof*][Shen1992]
-/

@[expose] public section

namespace Cslib.Complexity.QBFProtocol

open Cslib.Logic.PL Turing.MultiTapeTM Machine

/-! ### Instances and padding -/

/-- A number `v` as a word of `m` bits: `v` copies of `true`, padded with `false`s. It has length
`m` when `v ≤ m`. -/
def padUnary (m v : ℕ) : List Bool := List.replicate v true ++ List.replicate (m - v) false

/-- The number is the count of `true`s of its padded word, so padding is injective. -/
theorem padUnary_injective (m : ℕ) : Function.Injective (padUnary m) := fun a b h => by
  have := congrArg (List.count true) h
  simpa [padUnary, List.count_replicate] using this

/-- A number at most `m` pads to a word of exactly `m` bits. -/
theorem length_padUnary {m v : ℕ} (h : v ≤ m) : (padUnary m v).length = m := by
  simp only [padUnary, List.length_append, List.length_replicate]
  omega

/-- **An instance of the value language**: the parameters and tokens of the machine, the values of
the point on the variables of `input.xs` in order, and the index of the bit asked for. -/
structure ValueInstance where
  /-- The parameters and the tokens of the arithmetic formula. -/
  input : LoopInput
  /-- The values of the variables of `input.xs`, in order. -/
  point : List ℕ
  /-- The index of the bit of the value that the instance asks for. -/
  bit : ℕ

/-- The length of a list encoding whose elements all have encodings of length `k`. -/
theorem length_encList_of_forall {α : Type} (enc : α ↪ List Bool) (l : List α) {k : ℕ}
    (h : ∀ a ∈ l, (enc a).length = k) : (encList enc l).length = l.length * (2 * k + 1) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [encList_cons, List.length_append, length_frame, List.length_cons]
    rw [ih fun b hb => h b (List.mem_cons_of_mem a hb), h a List.mem_cons_self]
    ring

/-! ### Validity -/

/-- **Validity of an instance for a formula `e`**: the tokens of the input are those of `e`, the
modulus is a prime large enough that the protocol's soundness error is at most `1 / 3`, the
degrees of the rounds of `e` are at most `D < p`, all variables of `e`, free or bound, are among
`xs`, and the point and the bit are in range. -/
structure ValueInstance.ValidFor (I : ValueInstance) (e : ArithQBF ℕ) : Prop where
  /-- The tokens of the input are those of `e`. -/
  tokens_eq : I.input.tokens = e.tokens
  /-- The modulus is prime. -/
  prime : I.input.modulus.Prime
  /-- The soundness error `ops * D * 2 / p` is at most `1 / 3`. -/
  ops_le : 6 * e.ops * I.input.degree + 1 ≤ I.input.modulus
  /-- The degree of every round of `e` is at most `D`. -/
  degree_ge : e.maxRoundDegree ≤ I.input.degree
  /-- The degree bound is below the modulus. -/
  degree_lt : I.input.degree < I.input.modulus
  /-- Every variable of `e`, bound ones included, is among `xs`. -/
  vars_mem : ∀ w ∈ e.vars, w ∈ I.input.xs
  /-- There is one value for every variable of `xs`. -/
  point_length : I.point.length = I.input.xs.length
  /-- Every value is below the modulus. -/
  point_lt : ∀ v ∈ I.point, v < I.input.modulus
  /-- The bit index is below the modulus. -/
  bit_lt : I.bit < I.input.modulus

/-- The point of an instance as an assignment: the value of the first occurrence of a variable in
`xs`, and `0` for a variable that does not occur. -/
def ValueInstance.pointFun (I : ValueInstance) : ℕ → ZMod I.input.modulus :=
  fun w => (lookupPt (I.input.xs.zip I.point) w : ZMod I.input.modulus)

/-- **The value** of the formula `e` at the point of the instance, modulo the modulus. -/
def ValueInstance.value (I : ValueInstance) (e : ArithQBF ℕ) : ZMod I.input.modulus :=
  e.eval I.pointFun

/-- The instance whose formula is `e`, with the same parameters and bit, and the point
`point`. -/
def ValueInstance.child (I : ValueInstance) (e : ArithQBF ℕ) (point : List ℕ) :
    ValueInstance :=
  ⟨{ I.input with tokens := e.tokens }, point, I.bit⟩

/-! ### The value in terms of the values of the children -/

/-- The point of an instance with the variable `v` set to `z`, on every occurrence of `v` in
`xs`. -/
def ValueInstance.setPoint (I : ValueInstance) (v z : ℕ) : List ℕ :=
  (I.input.xs.zip I.point).map fun q => if q.1 = v then z else q.2

private theorem lookupPt_cons (q : ℕ × ℕ) (pt : List (ℕ × ℕ)) (w : ℕ) :
    lookupPt (q :: pt) w = if q.1 = w then q.2 else lookupPt pt w := by
  unfold lookupPt
  by_cases h : q.1 = w <;> simp [h]

private theorem lookupPt_nil (w : ℕ) : lookupPt [] w = 0 := rfl

private theorem lookupPt_zip_setPoint (xs point : List ℕ) (hlen : point.length = xs.length)
    (v z w : ℕ) :
    lookupPt (xs.zip ((xs.zip point).map fun q => if q.1 = v then z else q.2)) w =
      if w = v then (if v ∈ xs then z else 0) else lookupPt (xs.zip point) w := by
  induction xs generalizing point with
  | nil => simp [lookupPt_nil]
  | cons x xs ih =>
    cases point with
    | nil => simp at hlen
    | cons a p =>
      have hlen' : p.length = xs.length := by simpa using hlen
      simp only [List.zip_cons_cons, List.map_cons, lookupPt_cons, ih p hlen']
      by_cases hxv : x = v
      · subst hxv
        by_cases hxw : x = w
        · simp_all
        · have hwx : ¬ w = x := fun h => hxw h.symm
          simp_all
      · have hvx : ¬ v = x := fun h => hxv h.symm
        by_cases hxw : x = w <;> by_cases hwv : w = v <;> simp_all

/-- Setting the variable `v` of `xs` to `z` in the point of an instance sets it in the assignment
of the child. -/
theorem ValueInstance.pointFun_child_setPoint {I : ValueInstance}
    (h : I.point.length = I.input.xs.length) {v : ℕ} (hv : v ∈ I.input.xs) (z : ℕ)
    (e : ArithQBF ℕ) :
    (I.child e (I.setPoint v z)).pointFun =
      Function.update I.pointFun v (z : ZMod I.input.modulus) := by
  funext w
  change ((lookupPt (I.input.xs.zip (I.setPoint v z)) w : ℕ) : ZMod I.input.modulus) = _
  rw [ValueInstance.setPoint, lookupPt_zip_setPoint _ _ h]
  by_cases hwv : w = v
  · subst hwv
    simp [hv]
  · simp [hwv, ValueInstance.pointFun]

/-- The value of a child, with the same modulus as the parent. -/
def ValueInstance.childValue (I : ValueInstance) (e : ArithQBF ℕ) (point : List ℕ) :
    ZMod I.input.modulus :=
  (I.child e point).value e

/-- **The value of a negation** is one minus the value of its argument. -/
theorem ValueInstance.value_not (I : ValueInstance) (e : ArithQBF ℕ) :
    I.value e.not = 1 - I.childValue e I.point :=
  rfl

/-- **The value of a binary connective** applies the connective to the values of its arguments. -/
theorem ValueInstance.value_bin (I : ValueInstance) (o : ArithQBF.Connective)
    (e₁ e₂ : ArithQBF ℕ) :
    I.value (.bin o e₁ e₂) = o.apply (I.childValue e₁ I.point) (I.childValue e₂ I.point) :=
  rfl

/-- **The value of an operator** binding `v` applies the operator to the value of `v` and the
values of the body with `v` set to `0` and to `1`. -/
theorem ValueInstance.value_op {I : ValueInstance} (h : I.point.length = I.input.xs.length)
    (o : ArithQBF.Operator) {v : ℕ} (hv : v ∈ I.input.xs) (e : ArithQBF ℕ) :
    I.value (.op o v e) = o.apply (I.pointFun v)
      (I.childValue e (I.setPoint v 0)) (I.childValue e (I.setPoint v 1)) := by
  simp only [ValueInstance.value, ValueInstance.childValue, ArithQBF.eval_op,
    ValueInstance.pointFun_child_setPoint h hv, Nat.cast_zero, Nat.cast_one]
  rfl

/-! ### The scan in polynomial time -/

section PolyTime

open ComputableInPolyTime

private lemma arity_pt :
    ComputableInPolyTime ArithQBF.Kind.arity (encFinEnum ArithQBF.Kind) encUnary := of_finite _

private lemma firstStep_pt :
    ComputableInPolyTime (fun p : (ℕ × ℕ) × (ArithQBF.Kind × ℕ) => firstStep p.1 p.2)
      (encPair (encPair encUnary encUnary) encArithToken) (encPair encUnary encUnary) := by
  have := arity_pt
  unfold firstStep
  fun_prop

/-- **The end of the first formula of a list of tokens is computable in polynomial time**, in
unary. -/
theorem computableInPolyTime_firstLen :
    ComputableInPolyTime firstLen (encList encArithToken) encUnary := by
  have hfold : ComputableInPolyTime
      (fun ts : List (ArithQBF.Kind × ℕ) => ts.foldl firstStep (1, 0))
      (encList encArithToken) (encPair encUnary encUnary) :=
    foldl_of_bounded_growth (list := id) (encA := encArithToken) id' (const (1, 0)) firstStep_pt
      (growth := 3) fun st t => by
        unfold firstStep
        split_ifs
        · omega
        · simp only [length_encPair, encUnary_apply, List.length_replicate]
          cases t.1 <;> simp [ArithQBF.Kind.arity] <;> omega
  unfold firstLen
  exact (snd encUnary encUnary).comp hfold

end PolyTime

end Cslib.Complexity.QBFProtocol
