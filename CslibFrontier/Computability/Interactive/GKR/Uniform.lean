/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Interactive.GKR.Layered
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Inductive
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import Mathlib.Data.ZMod.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Equality
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Unary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Words
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Words
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.ListProd
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Foundations.Data.ZMod.NatCast
import Mathlib.Data.List.OfFn

/-!
# Uniform layered arithmetic circuits and polynomial-time wiring extensions

A verifier-side, efficient-wiring-MLE (`HasPolyTimeWiringMLE`) step toward
[Goldwasser, Kalai, Rothblum][GoldwasserKalaiRothblum2015] Theorem 1.1 (§3; see also
[Thaler, §4.6][Thaler2022]): the GKR protocol delegates the evaluation of a layered arithmetic
circuit `C` of depth `d` and gate counts `2 ^ width i` with verifier work proportional to the
input/output sizes plus `d` rounds of sumcheck and wiring-extension evaluation. Here
`UniformGKRFamily` pairs `LayeredCircuit.IsLogSpaceUniform` with an explicit caller-supplied
`HasPolyTimeWiringMLE` oracle evaluating `ãdd_i` and `m̃ult_i` in polynomial time; compiling
arbitrary `IsLogSpaceUniform` wiring without a supplied `HasPolyTimeWiringMLE` oracle and `poly(S)`
prover multi-tape word-TM runtime remain open on `#892`.

This module formalizes:

1. **Log-space uniformity** (`LayeredCircuit.IsLogSpaceUniform`) for indexed families
   `C : I → LayeredCircuit` under an index encoding `encI : I ↪ List Bool`: the depth, layer
   widths (in unary) and Boolean wiring predicates `isWiring` are computable in deterministic
   logarithmic space (`ComputableInLogSpace`), with a direct constructor
   `IsLogSpaceUniform.of_neighbours` from log-space gate-kind and in-neighbour transducers.
2. **Polynomial-time wiring multilinear extension oracles** (`LayeredCircuit.HasPolyTimeWiringMLE`)
   over prime/modular rings `ZMod p` with `p` and field coordinates encoded in **binary**
   (`encNat`), so exponentially large moduli cost `O(log p)` bits, bundled with log-space
   uniformity in `UniformGKRFamily`.
3. **Subcube- and coordinate-literal-wired layered circuits** (`WireLit`, `WiringClause`,
   `LayeredCircuit.ofClauses`), covering data-parallel routing, fan-out, repeated squaring, binary
   reduction trees and mixed addition/multiplication layers. When the clauses of layer `i`
   partition `{0, 1}^{width (i + 1)}` (`ClausesPartition`), the multilinear extension of
   `wiringPred` factors into a sum of coordinate products
   (`eval_multilinearExtension_wiringPred_ofClauses`) computable in polynomial time
   (`hasPolyTimeWiringMLE_ofClauses`).
4. **Concrete exponential-width circuit family** (`powerSumGKRFamily`): a parameterized family with
   `2 ^ inWidth` inputs, an internal fan-out and `sqDepth` repeated-squaring layers of width
   `midWidth` (`2 ^ midWidth` gates per layer, exponentially larger than the unary parameter length
   `inWidth + midWidth + sqDepth`), and `midWidth` binary-tree addition layers reducing to one
   output gate, proved both `IsLogSpaceUniform` and `HasPolyTimeWiringMLE`.

Note: primary-source page/theorem locators in `[GoldwasserKalaiRothblum2015]` (§3 / Theorem 1.1) and
`[Thaler2022]` (§4.6) are from recorded repository documentation (locator not re-verified against
primary PDF).

## Main definitions

* `Cslib.Interactive.GKR.encGate`: bit-word encoding of `Gate`.
* `Cslib.Interactive.GKR.WiringQuery`, `Cslib.Interactive.GKR.GateQuery`,
  `Cslib.Interactive.GKR.LayeredCircuit.IsLogSpaceUniform`: log-space uniformity of a layered
  circuit family.
* `Cslib.Interactive.GKR.WiringMLEQuery`,
  `Cslib.Interactive.GKR.LayeredCircuit.HasPolyTimeWiringMLE`,
  `Cslib.Interactive.GKR.UniformGKRFamily`: polynomial-time wiring MLE evaluation over `ZMod p`
  (binary modulus and coordinates) bundled with log-space uniformity.
* `Cslib.Interactive.GKR.WireLit`, `Cslib.Interactive.GKR.WiringClause`,
  `Cslib.Interactive.GKR.LayeredCircuit.ofClauses`: subcube- and literal-wired layered circuits.
* `Cslib.Interactive.GKR.PowerSumParams`, `Cslib.Interactive.GKR.powerSumCircuit`,
  `Cslib.Interactive.GKR.powerSumGKRFamily`: concrete exponential-width uniform GKR family.

## Main results

* `Cslib.Interactive.GKR.LayeredCircuit.IsLogSpaceUniform.of_neighbours`: log-space gate and
  in-neighbour maps imply log-space uniformity of the wiring predicates.
* `Cslib.Interactive.GKR.eval_multilinearExtension_wiringPred_ofClauses`: closed-form coordinate
  product factorization of `ãdd_i` and `m̃ult_i` for partitioned `WiringClause` layers.
* `Cslib.Interactive.GKR.computableInPolyTime_evalClausesMod`,
  `Cslib.Interactive.GKR.hasPolyTimeWiringMLE_ofClauses`: polynomial-time evaluation of wiring
  multilinear extensions for clause-wired families.
* `Cslib.Interactive.GKR.isLogSpaceUniform_powerSumCircuit`,
  `Cslib.Interactive.GKR.hasPolyTimeWiringMLE_powerSumCircuit`: unconditional `UniformGKRFamily`
  instance for `powerSumCircuit`.

## References

* [S. Goldwasser, Y. T. Kalai, G. N. Rothblum, *Delegating computation: interactive proofs for
  muggles*][GoldwasserKalaiRothblum2015], Theorem 1.1 and Section 3 (locator not re-verified
  against primary PDF)
* [J. Thaler, *Proofs, Arguments, and Zero-Knowledge*][Thaler2022], Section 4.6 (locator not
  re-verified against primary PDF)
-/

public section

namespace Cslib.Interactive.GKR

open MvPolynomial Cslib.BitString Turing.MultiTapeTM

/-! ### Gate encoding and Boolean wiring predicate -/

instance : Fintype Gate :=
  ⟨{.add, .mul}, fun g => by cases g <;> simp⟩

/-- Encoding of `Gate`: `[false]` for `.add` and `[true]` for `.mul`. -/
enc_inductive encGate : Gate where
  | add
  | mul

attribute [nolint defsWithUnderscore] encGate_toSum encGate_elim

/-- Framed list of binary naturals, used for field-element vectors over `ZMod p`. -/
abbrev encNatList : List ℕ ↪ List Bool := encList encNat

/-- Subcube mask encoding: framed list of optional Booleans (`[]` for unconstrained coordinates,
`true :: [b]` for coordinates fixed to `b`). -/
abbrev encMask : List (Option Bool) ↪ List Bool := encList (encOption encBool)

/-- Read a list of natural numbers as a `Fin k`-indexed vector in `ZMod p`, padding missing entries
with `0`. -/
@[expose]
def vecOfList (p k : ℕ) (xs : List ℕ) : Fin k → ZMod p :=
  fun j => ((xs.getD j.val 0 : ℕ) : ZMod p)

@[simp]
theorem vecOfList_ofFn {p k : ℕ} [NeZero p] (v : Fin k → ZMod p) :
    vecOfList p k (List.ofFn fun j => (v j).val) = v := by
  funext j
  simp [vecOfList, List.getD_eq_getElem?_getD]

/-- Modular subtraction `(a - b) mod p` on natural representatives, returning `0` when `p = 0`. -/
def subModNat (p a b : ℕ) : ℕ :=
  if p = 0 then 0 else (a % p + (p - b % p)) % p

theorem subModNat_lt {p : ℕ} (hp : 0 < p) (a b : ℕ) : subModNat p a b < p := by
  simp only [subModNat, hp.ne', ↓reduceIte]
  exact Nat.mod_lt _ hp

theorem natCast_subModNat {p : ℕ} [NeZero p] (a b : ℕ) :
    ((subModNat p a b : ℕ) : ZMod p) = (a : ZMod p) - (b : ZMod p) := by
  simp only [subModNat, NeZero.ne p, ↓reduceIte]
  rw [ZMod.natCast_mod, Nat.cast_add, ZMod.natCast_sub_mod_eq_neg, ZMod.natCast_mod]
  ring

namespace LayeredCircuit

/-- Boolean wiring relation of layer `i + 1`: `true` iff gate `a` has kind `g` and in-neighbours
`b` and `c` in layer `i`. -/
@[expose]
def isWiring (C : LayeredCircuit) (g : Gate) (i : ℕ)
    (a : Fin (C.width (i + 1)) → Bool) (b c : Fin (C.width i) → Bool) : Bool :=
  decide (C.gate i a = g ∧ C.left i a = b ∧ C.right i a = c)

@[simp]
theorem wiringPred_sumElim {R : Type*} [CommRing R] (C : LayeredCircuit) (g : Gate) (i : ℕ)
    (a : Fin (C.width (i + 1)) → Bool) (b c : Fin (C.width i) → Bool) :
    C.wiringPred (R := R) g i (Sum.elim a (Sum.elim b c)) =
      if C.isWiring g i a b c then 1 else 0 := by
  have ha : (Sum.elim a (Sum.elim b c) ∘ Sum.inl) = a := rfl
  have hb : (Sum.elim a (Sum.elim b c) ∘ Sum.inr ∘ Sum.inl) = b := rfl
  have hc : (Sum.elim a (Sum.elim b c) ∘ Sum.inr ∘ Sum.inr) = c := rfl
  simp [wiringPred, isWiring, ha, hb, hc]

end LayeredCircuit

/-! ### Log-space uniformity and polynomial-time wiring MLE interfaces -/

/-- Input to a direct gate/in-neighbour lookup: circuit family index, unary layer index `i`, and
raw bit label `outGate` of a gate in layer `i + 1`. -/
structure GateQuery (I : Type) where
  /-- Circuit family index. -/
  index : I
  /-- Layer index `i < depth`, encoded in unary. -/
  layer : ℕ
  /-- Bit label `a` of a gate in layer `i + 1`. -/
  outGate : List Bool

/-- Tuple encoding of `GateQuery I`: framed `index`, framed unary `layer`, and raw `outGate`. -/
enc_structure encGateQuery (I : Type) (encI : I ↪ List Bool) : GateQuery I where
  index : encI,
  layer : encUnary,
  outGate : encBits

/-- Input to a Boolean wiring-predicate query `(ι, g, i, a, b, c)`. -/
structure WiringQuery (I : Type) where
  /-- Circuit family index. -/
  index : I
  /-- Gate kind (`Gate.add` or `Gate.mul`). -/
  gate : Gate
  /-- Layer index `i < depth`, encoded in unary. -/
  layer : ℕ
  /-- Bit label `a` of a gate in layer `i + 1`. -/
  outGate : List Bool
  /-- Bit label `b` of the left candidate in-neighbour in layer `i`. -/
  leftGate : List Bool
  /-- Bit label `c` of the right candidate in-neighbour in layer `i`. -/
  rightGate : List Bool

/-- Tuple encoding of `WiringQuery I`, with `layer` in unary and gate labels as raw bit words. -/
enc_structure encWiringQuery (I : Type) (encI : I ↪ List Bool) : WiringQuery I where
  index : encI,
  gate : encGate,
  layer : encUnary,
  outGate : encBits,
  leftGate : encBits,
  rightGate : encBits

/-- **Log-space uniformity** of an indexed family of layered arithmetic circuits
([Goldwasser, Kalai, Rothblum][GoldwasserKalaiRothblum2015], [Thaler, §4.6][Thaler2022]):
`depth`, `width` (in unary) and the Boolean wiring predicates `add_i`, `mult_i` are computable in
deterministic logarithmic space on `encI`. -/
structure LayeredCircuit.IsLogSpaceUniform {I : Type} (encI : I ↪ List Bool)
    (C : I → LayeredCircuit) : Prop where
  /-- Circuit depth is computable in logarithmic space in unary. -/
  depth : ComputableInLogSpace (fun ι => (C ι).depth) encI encUnary
  /-- Layer bit-widths `width i` are computable in logarithmic space in unary. -/
  width : ComputableInLogSpace (fun p : I × ℕ => (C p.1).width p.2) (encPair encI encUnary) encUnary
  /-- One log-space decider computes `isWiring` on valid gate labels of every layer `i < depth`. -/
  wiring : ∃ decideWiring : WiringQuery I → Bool,
    ComputableInLogSpace decideWiring (encWiringQuery I encI) encBool ∧
    ∀ (ι : I) (g : Gate) (i : ℕ), i < (C ι).depth →
      ∀ (a : Fin ((C ι).width (i + 1)) → Bool) (b c : Fin ((C ι).width i) → Bool),
        decideWiring ⟨ι, g, i, List.ofFn a, List.ofFn b, List.ofFn c⟩ =
          (C ι).isWiring g i a b c

namespace LayeredCircuit.IsLogSpaceUniform

variable {I : Type} {encI : I ↪ List Bool} {C : I → LayeredCircuit}

theorem depth_polyTime (h : IsLogSpaceUniform encI C) :
    ComputableInPolyTime (fun ι => (C ι).depth) encI encUnary :=
  h.depth.computableInPolyTime

theorem width_polyTime (h : IsLogSpaceUniform encI C) :
    ComputableInPolyTime (fun p : I × ℕ => (C p.1).width p.2) (encPair encI encUnary) encUnary :=
  h.width.computableInPolyTime

/-- Construct `IsLogSpaceUniform` from log-space transducers computing the gate kind and the left
and right in-neighbour labels of any gate `a` in layer `i + 1`. -/
theorem of_neighbours
    (hdepth : ComputableInLogSpace (fun ι => (C ι).depth) encI encUnary)
    (hwidth : ComputableInLogSpace (fun p : I × ℕ => (C p.1).width p.2)
      (encPair encI encUnary) encUnary)
    {gateAt : GateQuery I → Gate} {leftAt rightAt : GateQuery I → List Bool}
    (hgate : ComputableInLogSpace gateAt (encGateQuery I encI) encGate)
    (hleft : ComputableInLogSpace leftAt (encGateQuery I encI) encBits)
    (hright : ComputableInLogSpace rightAt (encGateQuery I encI) encBits)
    (hgate_eq : ∀ (ι : I) (i : ℕ), i < (C ι).depth →
      ∀ a : Fin ((C ι).width (i + 1)) → Bool, gateAt ⟨ι, i, List.ofFn a⟩ = (C ι).gate i a)
    (hleft_eq : ∀ (ι : I) (i : ℕ), i < (C ι).depth →
      ∀ a : Fin ((C ι).width (i + 1)) → Bool,
        leftAt ⟨ι, i, List.ofFn a⟩ = List.ofFn ((C ι).left i a))
    (hright_eq : ∀ (ι : I) (i : ℕ), i < (C ι).depth →
      ∀ a : Fin ((C ι).width (i + 1)) → Bool,
        rightAt ⟨ι, i, List.ofFn a⟩ = List.ofFn ((C ι).right i a)) :
    IsLogSpaceUniform encI C := by
  refine ⟨hdepth, hwidth, ?_⟩
  let toGateQuery : WiringQuery I → GateQuery I := fun q => ⟨q.index, q.layer, q.outGate⟩
  have hWqFields : ComputableInLogSpace
      (fun q : WiringQuery I =>
        (q.index, q.gate, q.layer, q.outGate, q.leftGate, q.rightGate))
      (encWiringQuery I encI) (encWiringQueryFields I encI) :=
    ComputableInLogSpace.of_eq (encWiringQuery_apply I encI)
  have hIdx : ComputableInLogSpace WiringQuery.index (encWiringQuery I encI) encI :=
    ComputableInLogSpace.fst' hWqFields
  have hRest1 := ComputableInLogSpace.snd' hWqFields
  have hGate : ComputableInLogSpace WiringQuery.gate (encWiringQuery I encI) encGate :=
    ComputableInLogSpace.fst' hRest1
  have hRest2 := ComputableInLogSpace.snd' hRest1
  have hLayer : ComputableInLogSpace WiringQuery.layer (encWiringQuery I encI) encUnary :=
    ComputableInLogSpace.fst' hRest2
  have hRest3 := ComputableInLogSpace.snd' hRest2
  have hOut : ComputableInLogSpace WiringQuery.outGate (encWiringQuery I encI) encBits :=
    ComputableInLogSpace.fst' hRest3
  have hRest4 := ComputableInLogSpace.snd' hRest3
  have hLeft : ComputableInLogSpace WiringQuery.leftGate (encWiringQuery I encI) encBits :=
    ComputableInLogSpace.fst' hRest4
  have hRight : ComputableInLogSpace WiringQuery.rightGate (encWiringQuery I encI) encBits :=
    ComputableInLogSpace.snd' hRest4
  have hToGq : ComputableInLogSpace toGateQuery (encWiringQuery I encI) (encGateQuery I encI) :=
    (ComputableInLogSpace.pair hIdx (ComputableInLogSpace.pair hLayer hOut)).congr
      fun q => (encGateQuery_apply I encI (toGateQuery q)).symm
  let decideWiring : WiringQuery I → Bool := fun q =>
    decide (gateAt (toGateQuery q) = q.gate) &&
      (decide (leftAt (toGateQuery q) = q.leftGate) &&
        decide (rightAt (toGateQuery q) = q.rightGate))
  have hDec : ComputableInLogSpace decideWiring (encWiringQuery I encI) encBool :=
    ComputableInLogSpace.bool_and
      (ComputableInLogSpace.equal (hgate.comp' hToGq) hGate)
      (ComputableInLogSpace.bool_and
        (ComputableInLogSpace.equal (hleft.comp' hToGq) hLeft)
        (ComputableInLogSpace.equal (hright.comp' hToGq) hRight))
  refine ⟨decideWiring, hDec, fun ι g i hi a b c => ?_⟩
  simp only [decideWiring, toGateQuery, LayeredCircuit.isWiring, hgate_eq ι i hi a,
    hleft_eq ι i hi a, hright_eq ι i hi a, List.ofFn_inj]
  by_cases h1 : (C ι).gate i a = g <;>
    by_cases h2 : (C ι).left i a = b <;>
    by_cases h3 : (C ι).right i a = c <;>
    simp [h1, h2, h3]

end LayeredCircuit.IsLogSpaceUniform

/-- Evaluation query for the multilinear extension of `add_i` or `mult_i` over `ZMod modulus`,
with `modulus` and coordinate lists encoded in binary. -/
structure WiringMLEQuery (I : Type) where
  /-- Circuit family index. -/
  index : I
  /-- Gate kind (`Gate.add` for `ãdd_i`, `Gate.mul` for `m̃ult_i`). -/
  gate : Gate
  /-- Layer index `i < depth`, encoded in unary. -/
  layer : ℕ
  /-- Ring modulus `p`, encoded in binary (`encNat`). -/
  modulus : ℕ
  /-- Point `z` in layer `i + 1`, as binary natural representatives. -/
  z : List ℕ
  /-- Left point `y` in layer `i`, as binary natural representatives. -/
  y : List ℕ
  /-- Right point `w` in layer `i`, as binary natural representatives. -/
  w : List ℕ

/-- Tuple encoding of `WiringMLEQuery I`, keeping `modulus` and all coordinates in binary. -/
enc_structure encWiringMLEQuery (I : Type) (encI : I ↪ List Bool) : WiringMLEQuery I where
  index : encI,
  gate : encGate,
  layer : encUnary,
  modulus : encNat,
  z : encNatList,
  y : encNatList,
  w : encNatList

/-- **Polynomial-time wiring multilinear extension oracle** for an indexed circuit family `C`:
`evalWiring` runs in polynomial time in `|encI ι| + i + log p + (width (i+1) + 2 · width i) log p`,
returns a canonical representative `< p`, and agrees with the multilinear extension of
`(C ι).wiringPred g i` over `ZMod p` for every layer `i < (C ι).depth`. -/
structure LayeredCircuit.HasPolyTimeWiringMLE {I : Type} (encI : I ↪ List Bool)
    (C : I → LayeredCircuit) (evalWiring : WiringMLEQuery I → ℕ) : Prop where
  /-- Polynomial-time native Turing-machine certificate. -/
  polyTime : ComputableInPolyTime evalWiring (encWiringMLEQuery I encI) encNat
  /-- Output is reduced modulo `modulus` whenever `0 < modulus`. -/
  lt_modulus : ∀ q : WiringMLEQuery I, 0 < q.modulus → evalWiring q < q.modulus
  /-- Exact agreement with `multilinearExtension ((C ι).wiringPred g i)` in `ZMod p`. -/
  eval_eq : ∀ (ι : I) (p : ℕ) [NeZero p] (g : Gate) (i : ℕ), i < (C ι).depth →
    ∀ zs ys ws : List ℕ,
      ((evalWiring ⟨ι, g, i, p, zs, ys, ws⟩ : ℕ) : ZMod p) =
        eval (Sum.elim (vecOfList p ((C ι).width (i + 1)) zs)
            (Sum.elim (vecOfList p ((C ι).width i) ys) (vecOfList p ((C ι).width i) ws)))
          (multilinearExtension ((C ι).wiringPred (R := ZMod p) g i))

/-- A step toward unconditional `IsLogSpaceUniform` GKR Theorem 1.1
([Goldwasser, Kalai, Rothblum][GoldwasserKalaiRothblum2015] §3; [Thaler, §4.6][Thaler2022]): a
log-space uniform family of layered arithmetic circuits paired with an explicit caller-supplied
`HasPolyTimeWiringMLE` polynomial-time evaluator for its wiring multilinear extensions (compiling
arbitrary `IsLogSpaceUniform` wiring without `HasPolyTimeWiringMLE` and `poly(S)` prover runtime
remain open on `#892`). -/
structure UniformGKRFamily (I : Type) (encI : I ↪ List Bool) where
  /-- The layered circuit at each index. -/
  circuit : I → LayeredCircuit
  /-- Canonical modular evaluator for `ãdd_i` and `m̃ult_i`. -/
  evalWiring : WiringMLEQuery I → ℕ
  /-- Log-space uniformity of `depth`, `width` and the Boolean wiring predicates. -/
  uniform : LayeredCircuit.IsLogSpaceUniform encI circuit
  /-- Polynomial-time certificate and correctness of `evalWiring`. -/
  wiringMLE : LayeredCircuit.HasPolyTimeWiringMLE encI circuit evalWiring

/-! ### Coordinate-literal and subcube-wired layered circuits -/

/-- A coordinate literal reading at most one bit of a gate label `a` in the layer above:
either a constant Boolean or `a[idx] ^^ neg` (with binary index `idx`). -/
inductive WireLit where
  /-- Constant bit `val`. -/
  | const (val : Bool)
  /-- Bit `idx` of the gate label, optionally negated when `neg = true`. -/
  | var (idx : ℕ) (neg : Bool)
  deriving DecidableEq

/-- Encoding of `WireLit`, with variable index `idx` in binary (`encNat`). -/
enc_inductive encWireLit : WireLit where
  | const : encBool
  | var : encNat, encBool

attribute [nolint defsWithUnderscore] encWireLit_toSum encWireLit_elim

namespace WireLit

/-- Evaluate a coordinate literal on a `Fin kOut`-indexed gate label `a`. Out-of-range variable
indices read `false`, so `.var idx neg` evaluates to `neg`. -/
@[expose]
def eval {kOut : ℕ} (lit : WireLit) (a : Fin kOut → Bool) : Bool :=
  match lit with
  | .const b => b
  | .var idx neg => if h : idx < kOut then xor (a ⟨idx, h⟩) neg else neg

/-- Multilinear indicator factor `b ? r : 1 - r` in a commutative ring `R`. -/
@[expose]
def litFactor {R : Type*} [CommRing R] (b : Bool) (r : R) : R :=
  if b then r else 1 - r

/-- Coordinate-independent factor of `litFactor (lit.eval a) r`: handles `.const` and out-of-range
`.var` literals. -/
def constWeight {R : Type*} [CommRing R] (kOut : ℕ) (lit : WireLit) (r : R) : R :=
  match lit with
  | .const b => litFactor b r
  | .var idx neg => if idx < kOut then 1 else litFactor neg r

/-- Coordinate-`j` factor of `litFactor (lit.eval a) r` when bit `a j` equals `b`. -/
def varWeight {R : Type*} [CommRing R] (lit : WireLit) (j : ℕ) (b : Bool) (r : R) : R :=
  match lit with
  | .const _ => 1
  | .var idx neg => if idx = j then litFactor (xor b neg) r else 1

/-- Pointwise factorization of `litFactor (lit.eval a) r` across coordinates `j : Fin kOut`. -/
private theorem constWeight_mul_prod_varWeight {R : Type*} [CommRing R] {kOut : ℕ}
    (lit : WireLit) (a : Fin kOut → Bool) (r : R) :
    lit.constWeight kOut r * (∏ j : Fin kOut, lit.varWeight j.val (a j) r) =
      litFactor (lit.eval a) r := by
  cases lit with
  | const b =>
    simp [constWeight, varWeight, eval]
  | var idx neg =>
    by_cases h : idx < kOut
    · simp only [constWeight, h, ↓reduceIte, one_mul, eval]
      rw [Finset.prod_eq_single (⟨idx, h⟩ : Fin kOut)]
      · simp [varWeight]
      · intro j _ hj
        have hne : idx ≠ j.val := fun heq => hj (Fin.ext heq.symm)
        simp [varWeight, hne]
      · simp
    · have hprod : (∏ j : Fin kOut, varWeight (.var idx neg) j.val (a j) r) = 1 := by
        refine Finset.prod_eq_one fun j _ => ?_
        have hne : idx ≠ j.val := by have := j.isLt; omega
        simp [varWeight, hne]
      simp [constWeight, eval, h, hprod]

end WireLit

/-- A subcube wiring clause: gates `a` matching `mask` have gate kind `gate` and in-neighbours
determined coordinatewise by `leftLits` and `rightLits`. -/
structure WiringClause where
  /-- Gate kind assigned to gates matching `mask`. -/
  gate : Gate
  /-- Optional bit constraints on the output gate label `a`. -/
  mask : List (Option Bool)
  /-- Coordinate literals for the left in-neighbour in layer `i`. -/
  leftLits : List WireLit
  /-- Coordinate literals for the right in-neighbour in layer `i`. -/
  rightLits : List WireLit

/-- Tuple encoding of `WiringClause`. -/
enc_structure encWiringClause : WiringClause where
  gate : encGate,
  mask : encMask,
  leftLits : (encList encWireLit),
  rightLits : (encList encWireLit)

namespace WiringClause

/-- Whether bit `b` satisfies optional bit constraint `m`. -/
@[expose]
def matchOpt : Option Bool → Bool → Bool
  | none, _ => true
  | some b₀, b => b == b₀

/-- Whether gate label `a : Fin kOut → Bool` lies in the subcube specified by `cl.mask`. -/
@[expose]
def matchesVec {kOut : ℕ} (cl : WiringClause) (a : Fin kOut → Bool) : Bool :=
  (List.finRange kOut).all fun j => matchOpt (cl.mask.getD j.val none) (a j)

/-- Left in-neighbour assigned by `cl` to `a`. -/
@[expose]
def evalLeft {kOut : ℕ} (kIn : ℕ) (cl : WiringClause) (a : Fin kOut → Bool) : Fin kIn → Bool :=
  fun ℓ => (cl.leftLits.getD ℓ.val (.const false)).eval a

/-- Right in-neighbour assigned by `cl` to `a`. -/
@[expose]
def evalRight {kOut : ℕ} (kIn : ℕ) (cl : WiringClause) (a : Fin kOut → Bool) : Fin kIn → Bool :=
  fun ℓ => (cl.rightLits.getD ℓ.val (.const false)).eval a

/-- Ring indicator of `matchOpt`. -/
def maskWeight {R : Type*} [CommRing R] (m : Option Bool) (b : Bool) : R :=
  if matchOpt m b then 1 else 0

private theorem prod_maskWeight {R : Type*} [CommRing R] {kOut : ℕ} (cl : WiringClause)
    (a : Fin kOut → Bool) :
    (∏ j : Fin kOut, maskWeight (R := R) (cl.mask.getD j.val none) (a j)) =
      if cl.matchesVec a then 1 else 0 := by
  by_cases h : cl.matchesVec a = true
  · rw [ite_eq_left h]
    simp only [matchesVec, List.all_eq_true, List.mem_finRange, true_implies] at h
    exact Finset.prod_eq_one fun j _ => by simp [maskWeight, -List.getD_eq_getElem?_getD, h j]
  · rw [ite_eq_right h]
    simp only [matchesVec, Bool.not_eq_true, List.all_eq_false] at h
    obtain ⟨j, _, hj⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by
      simp [maskWeight, -List.getD_eq_getElem?_getD, hj])

/-- Coordinate-`j` factor when `a j = b` in the factored MLE of `cl`. -/
def bitTerm {R : Type*} [CommRing R] {kOut kIn : ℕ} (cl : WiringClause)
    (z : Fin kOut → R) (y w : Fin kIn → R) (j : Fin kOut) (b : Bool) : R :=
  maskWeight (cl.mask.getD j.val none) b * WireLit.litFactor b (z j) *
    ((∏ ℓ : Fin kIn, (cl.leftLits.getD ℓ.val (.const false)).varWeight j.val b (y ℓ)) *
      (∏ ℓ : Fin kIn, (cl.rightLits.getD ℓ.val (.const false)).varWeight j.val b (w ℓ)))

/-- Closed-form polynomial evaluation of `cl`'s contribution to the wiring multilinear extension
at `(z, y, w)`. -/
def evalFactor {R : Type*} [CommRing R] {kOut kIn : ℕ} (cl : WiringClause)
    (z : Fin kOut → R) (y w : Fin kIn → R) : R :=
  ((∏ ℓ : Fin kIn, (cl.leftLits.getD ℓ.val (.const false)).constWeight kOut (y ℓ)) *
    (∏ ℓ : Fin kIn, (cl.rightLits.getD ℓ.val (.const false)).constWeight kOut (w ℓ))) *
    ∏ j : Fin kOut, (cl.bitTerm z y w j false + cl.bitTerm z y w j true)

private theorem sum_prod_bool {R : Type*} [CommRing R] :
    ∀ {k : ℕ} (f : Fin k → Bool → R),
      (∑ a : Fin k → Bool, ∏ j : Fin k, f j (a j)) = ∏ j : Fin k, (f j false + f j true)
  | 0, f => by simp
  | k + 1, f => by
    rw [← (Fin.consEquiv fun _ : Fin (k + 1) => Bool).sum_comp, Fintype.sum_prod_type,
      Fintype.sum_bool]
    simp only [Fin.prod_univ_succ, Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
    rw [← Finset.mul_sum, ← Finset.mul_sum, sum_prod_bool (fun j b => f j.succ b), ← add_mul,
      add_comm (f 0 true)]

private theorem eval_indicatorPoly_lits {R : Type*} [CommRing R] {kOut kIn : ℕ}
    (lits : List WireLit) (y : Fin kIn → R) (a : Fin kOut → Bool) :
    eval y (indicatorPoly fun ℓ : Fin kIn => (lits.getD ℓ.val (.const false)).eval a) =
      (∏ ℓ : Fin kIn, (lits.getD ℓ.val (.const false)).constWeight kOut (y ℓ)) *
        ∏ j : Fin kOut, ∏ ℓ : Fin kIn,
          (lits.getD ℓ.val (.const false)).varWeight j.val (a j) (y ℓ) := by
  have h1 : ∀ ℓ : Fin kIn,
      (if (lits.getD ℓ.val (.const false)).eval a then y ℓ else 1 - y ℓ) =
        (lits.getD ℓ.val (.const false)).constWeight kOut (y ℓ) *
          ∏ j : Fin kOut, (lits.getD ℓ.val (.const false)).varWeight j.val (a j) (y ℓ) :=
    fun ℓ => (WireLit.constWeight_mul_prod_varWeight _ a (y ℓ)).symm
  rw [eval_indicatorPoly_apply]
  simp_rw [h1]
  rw [Finset.prod_mul_distrib, Finset.prod_comm]

/-- **Single-clause factorization**: summing `χ_a(z) χ_{evalLeft a}(y) χ_{evalRight a}(w)` over all
gates `a` matching `cl` equals the coordinate product `cl.evalFactor z y w`. -/
private theorem sum_matchesVec_eq_evalFactor {R : Type*} [CommRing R] {kOut kIn : ℕ}
    (cl : WiringClause) (z : Fin kOut → R) (y w : Fin kIn → R) :
    (∑ a : Fin kOut → Bool,
        if cl.matchesVec a then
          eval z (indicatorPoly a) * eval y (indicatorPoly (cl.evalLeft kIn a)) *
            eval w (indicatorPoly (cl.evalRight kIn a))
        else 0) =
      cl.evalFactor z y w := by
  have hterm : ∀ a : Fin kOut → Bool,
      (if cl.matchesVec a then
          eval z (indicatorPoly a) * eval y (indicatorPoly (cl.evalLeft kIn a)) *
            eval w (indicatorPoly (cl.evalRight kIn a))
        else 0) =
      ((∏ ℓ : Fin kIn, (cl.leftLits.getD ℓ.val (.const false)).constWeight kOut (y ℓ)) *
        (∏ ℓ : Fin kIn, (cl.rightLits.getD ℓ.val (.const false)).constWeight kOut (w ℓ))) *
        ∏ j : Fin kOut, cl.bitTerm z y w j (a j) := by
    intro a
    have hm := cl.prod_maskWeight (R := R) a
    have hz : eval z (indicatorPoly a) = ∏ j : Fin kOut, WireLit.litFactor (a j) (z j) :=
      eval_indicatorPoly_apply a z
    calc (if cl.matchesVec a then
            eval z (indicatorPoly a) * eval y (indicatorPoly (cl.evalLeft kIn a)) *
              eval w (indicatorPoly (cl.evalRight kIn a))
          else 0)
        = (if cl.matchesVec a then (1 : R) else 0) *
            (eval z (indicatorPoly a) * eval y (indicatorPoly (cl.evalLeft kIn a)) *
              eval w (indicatorPoly (cl.evalRight kIn a))) := by
            split_ifs <;> ring
      _ = ((∏ ℓ : Fin kIn, (cl.leftLits.getD ℓ.val (.const false)).constWeight kOut (y ℓ)) *
            (∏ ℓ : Fin kIn, (cl.rightLits.getD ℓ.val (.const false)).constWeight kOut (w ℓ))) *
            ((∏ j : Fin kOut, maskWeight (cl.mask.getD j.val none) (a j)) *
              (∏ j : Fin kOut, WireLit.litFactor (a j) (z j)) *
              ((∏ j : Fin kOut, ∏ ℓ : Fin kIn,
                  (cl.leftLits.getD ℓ.val (.const false)).varWeight j.val (a j) (y ℓ)) *
                (∏ j : Fin kOut, ∏ ℓ : Fin kIn,
                  (cl.rightLits.getD ℓ.val (.const false)).varWeight j.val (a j) (w ℓ)))) := by
            have hl : cl.evalLeft kIn a =
                fun ℓ => (cl.leftLits.getD ℓ.val (.const false)).eval a := rfl
            have hr : cl.evalRight kIn a =
                fun ℓ => (cl.rightLits.getD ℓ.val (.const false)).eval a := rfl
            rw [← hm, hz, hl, hr, eval_indicatorPoly_lits cl.leftLits y a,
              eval_indicatorPoly_lits cl.rightLits w a]
            ring
      _ = _ := by
            congr 1
            simp only [bitTerm, Finset.prod_mul_distrib]
  simp only [hterm, ← Finset.mul_sum, evalFactor, sum_prod_bool]

end WiringClause

/-- A list of clauses partitions `{0, 1}^kOut` when every gate label matches exactly one clause. -/
@[expose]
def ClausesPartition (kOut : ℕ) (clauses : List WiringClause) : Prop :=
  ∀ a : Fin kOut → Bool, clauses.countP (fun cl => cl.matchesVec a) = 1

/-- Build a `LayeredCircuit` whose layer-`i` gate kinds and in-neighbours are given by the first
matching clause in `clauses i` (defaulting to an addition of gate `0` if none matches). -/
@[expose]
def LayeredCircuit.ofClauses (depth : ℕ) (width : ℕ → ℕ) (clauses : ℕ → List WiringClause) :
    LayeredCircuit where
  depth := depth
  width := width
  gate i a := ((clauses i).find? (fun cl => cl.matchesVec a)).elim .add WiringClause.gate
  left i a := ((clauses i).find? (fun cl => cl.matchesVec a)).elim (fun _ => false)
    (fun cl => cl.evalLeft (width i) a)
  right i a := ((clauses i).find? (fun cl => cl.matchesVec a)).elim (fun _ => false)
    (fun cl => cl.evalRight (width i) a)

private theorem find?_eq_of_countP_eq_one {α : Type*} {p : α → Bool} :
    ∀ {l : List α}, l.countP p = 1 → ∃ x ∈ l, l.find? p = some x ∧ p x = true ∧
      ∀ y ∈ l, p y = true → y = x
  | [], h => by simp at h
  | x :: xs, h => by
    rw [List.countP_cons] at h
    by_cases hx : p x = true
    · simp only [hx, ↓reduceIte] at h
      have h0 : xs.countP p = 0 := by omega
      rw [List.countP_eq_zero] at h0
      refine ⟨x, List.mem_cons_self, by simp [List.find?, hx], hx, fun y hy hpy => ?_⟩
      rcases List.mem_cons.mp hy with rfl | hmem
      · rfl
      · exact False.elim (by simpa [hpy] using h0 y hmem)
    · simp only [hx, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at h
      obtain ⟨y, hy, hfind, hpy, hunique⟩ := find?_eq_of_countP_eq_one h
      have hx' : p x = false := Bool.eq_false_iff.mpr hx
      refine ⟨y, List.mem_cons_of_mem x hy, by simp [List.find?, hx', hfind], hpy,
        fun z hz hpz => ?_⟩
      rcases List.mem_cons.mp hz with rfl | hmem
      · exact False.elim (hx hpz)
      · exact hunique z hmem hpz

private theorem sum_list_of_unique {R : Type*} [AddCommMonoid R] {α : Type*}
    {p : α → Bool} (f : α → R) :
    ∀ {l : List α}, l.countP p = 1 → ∀ {x : α}, l.find? p = some x →
      (l.map fun c => if p c then f c else 0).sum = f x
  | [], h, _, _ => by simp at h
  | c :: cs, h, x, hfind => by
    rw [List.countP_cons] at h
    by_cases hc : p c = true
    · simp only [List.find?, hc] at hfind
      obtain rfl := Option.some.inj hfind
      simp only [hc, ↓reduceIte] at h
      have h0 : cs.countP p = 0 := by omega
      rw [List.countP_eq_zero] at h0
      have hsum0 : (cs.map fun d => if p d then f d else 0).sum = 0 := by
        refine List.sum_eq_zero fun r hr => ?_
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hr
        simp [h0 d hd]
      simp [hc, hsum0]
    · have hc' : p c = false := Bool.eq_false_iff.mpr hc
      simp only [List.find?, hc'] at hfind
      simp only [hc, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at h
      simp [hc', sum_list_of_unique f h hfind]

/-- **Product factorization of wiring multilinear extensions** for `LayeredCircuit.ofClauses`:
when `clauses i` partitions `{0, 1}^{width (i + 1)}`, the multilinear extension of `wiringPred g i`
equals the sum over clauses `cl ∈ clauses i` with `cl.gate = g` of `cl.evalFactor z y w`. -/
theorem eval_multilinearExtension_wiringPred_ofClauses {R : Type*} [CommRing R]
    {depth : ℕ} {width : ℕ → ℕ} {clauses : ℕ → List WiringClause} {i : ℕ}
    (hpart : ClausesPartition (width (i + 1)) (clauses i)) (g : Gate)
    (z : Fin (width (i + 1)) → R) (y w : Fin (width i) → R) :
    eval (Sum.elim z (Sum.elim y w))
        (multilinearExtension ((LayeredCircuit.ofClauses depth width clauses).wiringPred
          (R := R) g i)) =
      ((clauses i).map fun cl =>
        if cl.gate = g then cl.evalFactor z y w else 0).sum := by
  let C := LayeredCircuit.ofClauses depth width clauses
  refine (C.eval_multilinearExtension_wiringPred (R := R) g i z y w).trans ?_
  have hpoint : ∀ a : Fin (width (i + 1)) → Bool,
      (if C.gate i a = g then
          eval z (indicatorPoly a) * eval y (indicatorPoly (C.left i a)) *
            eval w (indicatorPoly (C.right i a))
        else 0) =
      ((clauses i).map fun cl =>
        if cl.gate = g then
          if cl.matchesVec a then
            eval z (indicatorPoly a) * eval y (indicatorPoly (cl.evalLeft (width i) a)) *
              eval w (indicatorPoly (cl.evalRight (width i) a))
          else 0
        else 0).sum := by
    intro a
    obtain ⟨cl₀, _, hfind, _, _⟩ := find?_eq_of_countP_eq_one (hpart a)
    have hsum := sum_list_of_unique
      (fun cl : WiringClause =>
        if cl.gate = g then
          eval z (indicatorPoly a) * eval y (indicatorPoly (cl.evalLeft (width i) a)) *
            eval w (indicatorPoly (cl.evalRight (width i) a))
        else 0)
      (hpart a) hfind
    simp only [C, LayeredCircuit.ofClauses, hfind, Option.elim_some]
    rw [← hsum]
    congr 1
    refine List.map_congr_left fun cl _ => ?_
    by_cases hg : cl.gate = g <;> simp [hg]
  refine (Finset.sum_congr rfl fun a _ => hpoint a).trans ?_
  have hcomm : ∀ l : List WiringClause,
      (∑ a : Fin (width (i + 1)) → Bool,
        (l.map fun cl =>
          if cl.gate = g then
            if cl.matchesVec a then
              eval z (indicatorPoly a) * eval y (indicatorPoly (cl.evalLeft (width i) a)) *
                eval w (indicatorPoly (cl.evalRight (width i) a))
            else 0
          else 0).sum) =
      (l.map fun cl =>
        if cl.gate = g then cl.evalFactor z y w else 0).sum := by
    intro l
    induction l with
    | nil => simp
    | cons cl cls ih =>
      simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]
      congr 1
      by_cases hg : cl.gate = g
      · simp only [hg, ↓reduceIte, WiringClause.sum_matchesVec_eq_evalFactor]
      · simp [hg]
  exact hcomm (clauses i)

/-! ### Executable modular wiring-clause evaluator and polynomial-time certificate -/

/-- Natural representative of `WireLit.litFactor b r` modulo `p` (unreduced when `b = true`). -/
def litFactorNat (p : ℕ) (b : Bool) (r : ℕ) : ℕ :=
  if b then r % p else subModNat p 1 r

theorem natCast_litFactorNat {p : ℕ} [NeZero p] (b : Bool) (r : ℕ) :
    ((litFactorNat p b r : ℕ) : ZMod p) = WireLit.litFactor b (r : ZMod p) := by
  cases b
  · simp [litFactorNat, WireLit.litFactor, natCast_subModNat]
  · simp [litFactorNat, WireLit.litFactor, ZMod.natCast_mod]

/-- Natural representative of `WireLit.constWeight` modulo `p`. -/
private def constWeightNat (p kOut : ℕ) (lit : WireLit) (r : ℕ) : ℕ :=
  encWireLit_elim lit
    (fun b => litFactorNat p b r)
    (fun q => if q.1 < kOut then 1 else litFactorNat p q.2 r)

private theorem natCast_constWeightNat {p : ℕ} [NeZero p] (kOut : ℕ) (lit : WireLit) (r : ℕ) :
    ((constWeightNat p kOut lit r : ℕ) : ZMod p) = lit.constWeight kOut (r : ZMod p) := by
  cases lit <;> simp only [constWeightNat, encWireLit_elim, encWireLit_toSum, Sum.elim_inl,
    Sum.elim_inr, WireLit.constWeight]
  · exact natCast_litFactorNat _ _
  · split_ifs
    · simp
    · exact natCast_litFactorNat _ _

/-- Natural representative of `WireLit.varWeight` modulo `p`. -/
private def varWeightNat (p : ℕ) (lit : WireLit) (j : ℕ) (b : Bool) (r : ℕ) : ℕ :=
  encWireLit_elim lit
    (fun _ => 1)
    (fun q => if q.1 = j then litFactorNat p (xor b q.2) r else 1)

private theorem natCast_varWeightNat {p : ℕ} [NeZero p] (lit : WireLit) (j : ℕ) (b : Bool) (r : ℕ) :
    ((varWeightNat p lit j b r : ℕ) : ZMod p) = lit.varWeight j b (r : ZMod p) := by
  cases lit <;> simp only [varWeightNat, encWireLit_elim, encWireLit_toSum, Sum.elim_inl,
    Sum.elim_inr, WireLit.varWeight]
  · simp
  · split_ifs
    · exact natCast_litFactorNat _ _
    · simp

/-- Natural representative of `WiringClause.maskWeight`. -/
private def maskWeightNat (m : Option Bool) (b : Bool) : ℕ :=
  if WiringClause.matchOpt m b then 1 else 0

private theorem natCast_maskWeightNat {p : ℕ} (m : Option Bool) (b : Bool) :
    ((maskWeightNat m b : ℕ) : ZMod p) = WiringClause.maskWeight m b := by
  unfold maskWeightNat WiringClause.maskWeight
  split_ifs <;> simp

/-- Modular coordinate-`j` bit term of a `WiringClause`. -/
private def bitTermNat (p kIn : ℕ) (cl : WiringClause) (zs ys ws : List ℕ) (j : ℕ) (b : Bool) : ℕ :=
  let m := maskWeightNat ((cl.mask[j]?).getD none) b
  let zf := litFactorNat p b (zs.getD j 0)
  let lf := ((List.range kIn).map fun ℓ =>
    varWeightNat p (cl.leftLits.getD ℓ (.const false)) j b (ys.getD ℓ 0)).prod % p
  let rf := ((List.range kIn).map fun ℓ =>
    varWeightNat p (cl.rightLits.getD ℓ (.const false)) j b (ws.getD ℓ 0)).prod % p
  (m * zf * (lf * rf)) % p

/-- Modular evaluation of one `WiringClause` at `(zs, ys, ws)` modulo `p`. -/
private def evalClauseNat (p kOut kIn : ℕ) (cl : WiringClause) (zs ys ws : List ℕ) : ℕ :=
  let lc := ((List.range kIn).map fun ℓ =>
    constWeightNat p kOut (cl.leftLits.getD ℓ (.const false)) (ys.getD ℓ 0)).prod % p
  let rc := ((List.range kIn).map fun ℓ =>
    constWeightNat p kOut (cl.rightLits.getD ℓ (.const false)) (ws.getD ℓ 0)).prod % p
  let coords := ((List.range kOut).map fun j =>
    (bitTermNat p kIn cl zs ys ws j false + bitTermNat p kIn cl zs ys ws j true) % p).prod % p
  ((lc * rc) % p * coords) % p

/-- Evaluate the sum of matching clauses in `clauses` modulo `p` (returning `0` if `p = 0`). -/
def evalClausesMod (p kOut kIn : ℕ) (g : Gate) (clauses : List WiringClause)
    (zs ys ws : List ℕ) : ℕ :=
  if p = 0 then 0
  else ((clauses.map fun cl =>
    if decide (cl.gate = g) then evalClauseNat p kOut kIn cl zs ys ws else 0).sum) % p

private theorem evalClausesMod_lt {p : ℕ} (hp : 0 < p) (kOut kIn : ℕ) (g : Gate)
    (clauses : List WiringClause) (zs ys ws : List ℕ) :
    evalClausesMod p kOut kIn g clauses zs ys ws < p := by
  simp only [evalClausesMod, hp.ne', ↓reduceIte]
  exact Nat.mod_lt _ hp

private theorem natCast_evalClauseNat {p : ℕ} [NeZero p] (kOut kIn : ℕ) (cl : WiringClause)
    (zs ys ws : List ℕ) :
    ((evalClauseNat p kOut kIn cl zs ys ws : ℕ) : ZMod p) =
      cl.evalFactor (vecOfList p kOut zs) (vecOfList p kIn ys) (vecOfList p kIn ws) := by
  have hbit : ∀ (j : Fin kOut) (b : Bool),
      ((bitTermNat p kIn cl zs ys ws j.val b : ℕ) : ZMod p) =
        cl.bitTerm (vecOfList p kOut zs) (vecOfList p kIn ys) (vecOfList p kIn ws) j b := by
    intro j b
    simp only [bitTermNat, ZMod.natCast_mod, Nat.cast_mul]
    rw [← List.prod_toFinset _ List.nodup_range, ← List.prod_toFinset _ List.nodup_range]
    simp only [List.toFinset_range, Nat.cast_prod, Finset.prod_range, natCast_maskWeightNat,
      natCast_litFactorNat, natCast_varWeightNat, vecOfList, WiringClause.bitTerm,
      List.getD_eq_getElem?_getD]
  have hcoords : (∏ i : Fin kOut,
      ((bitTermNat p kIn cl zs ys ws i.val false +
        bitTermNat p kIn cl zs ys ws i.val true : ℕ) : ZMod p)) =
      ∏ j : Fin kOut,
        (cl.bitTerm (vecOfList p kOut zs) (vecOfList p kIn ys) (vecOfList p kIn ws) j false +
          cl.bitTerm (vecOfList p kOut zs) (vecOfList p kIn ys) (vecOfList p kIn ws) j true) := by
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Nat.cast_add, hbit j false, hbit j true]
  simp only [evalClauseNat, ZMod.natCast_mod, Nat.cast_mul]
  rw [← List.prod_toFinset _ List.nodup_range, ← List.prod_toFinset _ List.nodup_range,
    ← List.prod_toFinset _ List.nodup_range]
  simp only [List.toFinset_range, Nat.cast_prod, Finset.prod_range, ZMod.natCast_mod,
    natCast_constWeightNat, WiringClause.evalFactor, vecOfList]
  rw [hcoords]

private theorem natCast_evalClausesMod {p : ℕ} [NeZero p] (kOut kIn : ℕ) (g : Gate)
    (clauses : List WiringClause) (zs ys ws : List ℕ) :
    ((evalClausesMod p kOut kIn g clauses zs ys ws : ℕ) : ZMod p) =
      (clauses.map fun cl =>
        if cl.gate = g then
          cl.evalFactor (vecOfList p kOut zs) (vecOfList p kIn ys) (vecOfList p kIn ws)
        else 0).sum := by
  simp only [evalClausesMod, NeZero.ne p, ↓reduceIte, ZMod.natCast_mod, Nat.cast_list_sum,
    List.map_map]
  congr 1
  refine List.map_congr_left fun cl _ => ?_
  by_cases hg : cl.gate = g <;> simp [hg, natCast_evalClauseNat]

section PolyTime

open ComputableInPolyTime

@[fun_prop]
theorem computableInPolyTime_subModNat {γ : Type} {encIn : γ ↪ List Bool} {p a b : γ → ℕ}
    (hp : ComputableInPolyTime p encIn encNat)
    (ha : ComputableInPolyTime a encIn encNat)
    (hb : ComputableInPolyTime b encIn encNat) :
    ComputableInPolyTime (fun x => subModNat (p x) (a x) (b x)) encIn encNat := by
  unfold subModNat
  have hp0 : ComputableInPolyTime (fun x => decide (p x = 0)) encIn encBool :=
    decide_eq' hp (const 0)
  have hbody : ComputableInPolyTime (fun x => (a x % p x + (p x - b x % p x)) % p x)
      encIn encNat :=
    binary_mod' (binary_add' (binary_mod' ha hp) (binary_sub' hp (binary_mod' hb hp))) hp
  exact ite_decide hp0 (const 0) hbody

@[fun_prop]
theorem computableInPolyTime_litFactorNat {γ : Type} {encIn : γ ↪ List Bool}
    {p r : γ → ℕ} {b : γ → Bool}
    (hp : ComputableInPolyTime p encIn encNat)
    (hb : ComputableInPolyTime b encIn encBool)
    (hr : ComputableInPolyTime r encIn encNat) :
    ComputableInPolyTime (fun x => litFactorNat (p x) (b x) (r x)) encIn encNat := by
  unfold litFactorNat
  exact ite' hb (binary_mod' hr hp) (computableInPolyTime_subModNat hp (const 1) hr)

private lemma constWeightNat_pt {γ : Type} {encIn : γ ↪ List Bool}
    {p kOut r : γ → ℕ} {lit : γ → WireLit}
    (hp : ComputableInPolyTime p encIn encNat)
    (hkOut : ComputableInPolyTime kOut encIn encUnary)
    (hlit : ComputableInPolyTime lit encIn encWireLit)
    (hr : ComputableInPolyTime r encIn encNat) :
    ComputableInPolyTime (fun x => constWeightNat (p x) (kOut x) (lit x) (r x)) encIn encNat := by
  unfold constWeightNat
  have hkBin : ComputableInPolyTime kOut encIn encNat := unary_to_binary.comp hkOut
  have hlt : ComputableInPolyTime (fun q : γ × (ℕ × Bool) => decide (q.2.1 < kOut q.1))
      (encPair encIn (encPair encNat encBool)) encBool :=
    binary_lt' (by fun_prop) (hkBin.comp (fst _ _))
  exact (encWireLit_elim_polyTime
    (g0 := fun q : γ × Bool => litFactorNat (p q.1) q.2 (r q.1))
    (g1 := fun q : γ × (ℕ × Bool) =>
      if q.2.1 < kOut q.1 then 1 else litFactorNat (p q.1) q.2.2 (r q.1))
    (computableInPolyTime_litFactorNat (hp.comp (fst _ _)) (snd _ _) (hr.comp (fst _ _)))
    (ite_decide hlt (const 1)
      (computableInPolyTime_litFactorNat (hp.comp (fst _ _)) (by fun_prop)
        (hr.comp (fst _ _))))).comp
    (id'.prod hlit)

private lemma varWeightNat_pt {γ : Type} {encIn : γ ↪ List Bool}
    {p j r : γ → ℕ} {lit : γ → WireLit} {b : γ → Bool}
    (hp : ComputableInPolyTime p encIn encNat)
    (hlit : ComputableInPolyTime lit encIn encWireLit)
    (hj : ComputableInPolyTime j encIn encUnary)
    (hb : ComputableInPolyTime b encIn encBool)
    (hr : ComputableInPolyTime r encIn encNat) :
    ComputableInPolyTime (fun x => varWeightNat (p x) (lit x) (j x) (b x) (r x)) encIn encNat := by
  unfold varWeightNat
  have hjBin : ComputableInPolyTime j encIn encNat := unary_to_binary.comp hj
  have heq : ComputableInPolyTime (fun q : γ × (ℕ × Bool) => decide (q.2.1 = j q.1))
      (encPair encIn (encPair encNat encBool)) encBool :=
    decide_eq' (by fun_prop) (hjBin.comp (fst _ _))
  have hxor : ComputableInPolyTime (fun q : γ × (ℕ × Bool) => xor (b q.1) q.2.2)
      (encPair encIn (encPair encNat encBool)) encBool :=
    (of_finite (fun uv : Bool × Bool => xor uv.1 uv.2)).comp
      ((hb.comp (fst _ _)).prod (by fun_prop))
  exact (encWireLit_elim_polyTime
    (g0 := fun _ : γ × Bool => (1 : ℕ))
    (g1 := fun q : γ × (ℕ × Bool) =>
      if q.2.1 = j q.1 then litFactorNat (p q.1) (xor (b q.1) q.2.2) (r q.1) else 1)
    (const 1)
    (ite_decide heq
      (computableInPolyTime_litFactorNat (hp.comp (fst _ _)) hxor (hr.comp (fst _ _)))
      (const 1))).comp
    (id'.prod hlit)

private lemma maskWeightNat_pt {γ : Type} {encIn : γ ↪ List Bool}
    {m : γ → Option Bool} {b : γ → Bool}
    (hm : ComputableInPolyTime m encIn (encOption encBool))
    (hb : ComputableInPolyTime b encIn encBool) :
    ComputableInPolyTime (fun x => maskWeightNat (m x) (b x)) encIn encNat := by
  have hfin : ComputableInPolyTime (fun q : Option Bool × Bool => maskWeightNat q.1 q.2)
      (encPair (encOption encBool) encBool) encNat := of_finite _
  exact hfin.comp (hm.prod hb)

private lemma getD_wireLitList_pt {γ : Type} {encIn : γ ↪ List Bool}
    {xs : γ → List WireLit} {i : γ → ℕ}
    (hxs : ComputableInPolyTime xs encIn (encList encWireLit))
    (hi : ComputableInPolyTime i encIn encUnary) :
    ComputableInPolyTime (fun x => (xs x).getD (i x) (.const false)) encIn encWireLit := by
  have hget : ComputableInPolyTime (fun x => (xs x)[i x]?) encIn (encOption encWireLit) :=
    getElem? hxs hi
  exact (hget.optionGetDWithInput (const (.const false))).of_enc_eq fun x => by
    rw [List.getD_eq_getElem?_getD]

private lemma getOpt_mask_pt {γ : Type} {encIn : γ ↪ List Bool}
    {ms : γ → List (Option Bool)} {i : γ → ℕ}
    (hms : ComputableInPolyTime ms encIn encMask)
    (hi : ComputableInPolyTime i encIn encUnary) :
    ComputableInPolyTime (fun x => ((ms x)[i x]?).getD none) encIn (encOption encBool) := by
  have hget : ComputableInPolyTime (fun x => (ms x)[i x]?)
      encIn (encOption (encOption encBool)) := getElem? hms hi
  exact hget.optionGetDWithInput (const none)

private lemma bitTermNat_pt {γ : Type} {encIn : γ ↪ List Bool}
    {p kIn j : γ → ℕ} {cl : γ → WiringClause} {zs ys ws : γ → List ℕ} {b : γ → Bool}
    (hp : ComputableInPolyTime p encIn encNat)
    (hkIn : ComputableInPolyTime kIn encIn encUnary)
    (hcl : ComputableInPolyTime cl encIn encWiringClause)
    (hzs : ComputableInPolyTime zs encIn encNatList)
    (hys : ComputableInPolyTime ys encIn encNatList)
    (hws : ComputableInPolyTime ws encIn encNatList)
    (hj : ComputableInPolyTime j encIn encUnary)
    (hb : ComputableInPolyTime b encIn encBool) :
    ComputableInPolyTime (fun x => bitTermNat (p x) (kIn x) (cl x) (zs x) (ys x) (ws x) (j x) (b x))
      encIn encNat := by
  unfold bitTermNat
  have hmask := encWiringClause_mask_polyTime hcl
  have hleft := encWiringClause_leftLits_polyTime hcl
  have hright := encWiringClause_rightLits_polyTime hcl
  have hm := maskWeightNat_pt (getOpt_mask_pt hmask hj) hb
  have hzf := computableInPolyTime_litFactorNat hp hb (listGetDWithInput hzs hj 0)
  have hrange : ComputableInPolyTime (fun x => List.range (kIn x)) encIn (encList encUnary) := by
    fun_prop
  have hlfMap := mapWith
    (varWeightNat_pt (hp.comp (fst _ _))
      (getD_wireLitList_pt (hleft.comp (fst _ _)) (snd _ _))
      (hj.comp (fst _ _)) (hb.comp (fst _ _))
      (listGetDWithInput (hys.comp (fst _ _)) (snd _ _) 0)) id' hrange
  have hrfMap := mapWith
    (varWeightNat_pt (hp.comp (fst _ _))
      (getD_wireLitList_pt (hright.comp (fst _ _)) (snd _ _))
      (hj.comp (fst _ _)) (hb.comp (fst _ _))
      (listGetDWithInput (hws.comp (fst _ _)) (snd _ _) 0)) id' hrange
  have hlf := binary_mod' (binary_prod.comp hlfMap) hp
  have hrf := binary_mod' (binary_prod.comp hrfMap) hp
  exact binary_mod' (binary_mul' (binary_mul' hm hzf) (binary_mul' hlf hrf)) hp

private lemma evalClauseNat_pt {γ : Type} {encIn : γ ↪ List Bool}
    {p kOut kIn : γ → ℕ} {cl : γ → WiringClause} {zs ys ws : γ → List ℕ}
    (hp : ComputableInPolyTime p encIn encNat)
    (hkOut : ComputableInPolyTime kOut encIn encUnary)
    (hkIn : ComputableInPolyTime kIn encIn encUnary)
    (hcl : ComputableInPolyTime cl encIn encWiringClause)
    (hzs : ComputableInPolyTime zs encIn encNatList)
    (hys : ComputableInPolyTime ys encIn encNatList)
    (hws : ComputableInPolyTime ws encIn encNatList) :
    ComputableInPolyTime (fun x => evalClauseNat (p x) (kOut x) (kIn x) (cl x) (zs x) (ys x) (ws x))
      encIn encNat := by
  unfold evalClauseNat
  have hleft := encWiringClause_leftLits_polyTime hcl
  have hright := encWiringClause_rightLits_polyTime hcl
  have hrIn : ComputableInPolyTime (fun x => List.range (kIn x)) encIn (encList encUnary) := by
    fun_prop
  have hrOut : ComputableInPolyTime (fun x => List.range (kOut x)) encIn (encList encUnary) := by
    fun_prop
  have hlc := binary_mod' (binary_prod.comp (mapWith
    (constWeightNat_pt (hp.comp (fst _ _)) (hkOut.comp (fst _ _))
      (getD_wireLitList_pt (hleft.comp (fst _ _)) (snd _ _))
      (listGetDWithInput (hys.comp (fst _ _)) (snd _ _) 0)) id' hrIn)) hp
  have hrc := binary_mod' (binary_prod.comp (mapWith
    (constWeightNat_pt (hp.comp (fst _ _)) (hkOut.comp (fst _ _))
      (getD_wireLitList_pt (hright.comp (fst _ _)) (snd _ _))
      (listGetDWithInput (hws.comp (fst _ _)) (snd _ _) 0)) id' hrIn)) hp
  have hbitF := bitTermNat_pt (hp.comp (fst _ _)) (hkIn.comp (fst _ _)) (hcl.comp (fst _ _))
    (hzs.comp (fst _ _)) (hys.comp (fst _ _)) (hws.comp (fst _ _)) (snd _ _) (const false)
  have hbitT := bitTermNat_pt (hp.comp (fst _ _)) (hkIn.comp (fst _ _)) (hcl.comp (fst _ _))
    (hzs.comp (fst _ _)) (hys.comp (fst _ _)) (hws.comp (fst _ _)) (snd _ _) (const true)
  have hcoords := binary_mod' (binary_prod.comp (mapWith
    (binary_mod' (binary_add' hbitF hbitT) (hp.comp (fst _ _))) id' hrOut)) hp
  exact binary_mod' (binary_mul' (binary_mod' (binary_mul' hlc hrc) hp) hcoords) hp

/-- **Polynomial-time evaluation of clause-wired wiring extensions** over binary moduli `p`. -/
@[fun_prop]
theorem computableInPolyTime_evalClausesMod {γ : Type} {encIn : γ ↪ List Bool}
    {p kOut kIn : γ → ℕ} {g : γ → Gate} {clauses : γ → List WiringClause}
    {zs ys ws : γ → List ℕ}
    (hp : ComputableInPolyTime p encIn encNat)
    (hkOut : ComputableInPolyTime kOut encIn encUnary)
    (hkIn : ComputableInPolyTime kIn encIn encUnary)
    (hg : ComputableInPolyTime g encIn encGate)
    (hclauses : ComputableInPolyTime clauses encIn (encList encWiringClause))
    (hzs : ComputableInPolyTime zs encIn encNatList)
    (hys : ComputableInPolyTime ys encIn encNatList)
    (hws : ComputableInPolyTime ws encIn encNatList) :
    ComputableInPolyTime
      (fun x => evalClausesMod (p x) (kOut x) (kIn x) (g x) (clauses x) (zs x) (ys x) (ws x))
      encIn encNat := by
  unfold evalClausesMod
  have hp0 : ComputableInPolyTime (fun x => decide (p x = 0)) encIn encBool :=
    decide_eq' hp (const 0)
  have hgateEq : ComputableInPolyTime
      (fun q : γ × WiringClause => decide (q.2.gate = g q.1))
      (encPair encIn encWiringClause) encBool :=
    decide_eq' (encWiringClause_gate_polyTime (snd _ _)) (hg.comp (fst _ _))
  have hterm : ComputableInPolyTime
      (fun q : γ × WiringClause =>
        if decide (q.2.gate = g q.1) then
          evalClauseNat (p q.1) (kOut q.1) (kIn q.1) q.2 (zs q.1) (ys q.1) (ws q.1)
        else 0)
      (encPair encIn encWiringClause) encNat :=
    ite' hgateEq
      (evalClauseNat_pt (hp.comp (fst _ _)) (hkOut.comp (fst _ _)) (hkIn.comp (fst _ _))
        (snd _ _) (hzs.comp (fst _ _)) (hys.comp (fst _ _)) (hws.comp (fst _ _)))
      (const 0)
  exact ite_decide hp0 (const 0)
    (binary_mod' (binary_sum.comp (mapWith hterm id' hclauses)) hp)

end PolyTime

/-- Any indexed family built by `LayeredCircuit.ofClauses` with polynomial-time `width` and
`clauses` whose clauses partition each active layer admits a certified polynomial-time wiring MLE
evaluator (`HasPolyTimeWiringMLE`). -/
theorem hasPolyTimeWiringMLE_ofClauses {I : Type} {encI : I ↪ List Bool}
    {depth : I → ℕ} {width : I → ℕ → ℕ} {clauses : I → ℕ → List WiringClause}
    (hwidth : ComputableInPolyTime (fun p : I × ℕ => width p.1 p.2)
      (encPair encI encUnary) encUnary)
    (hclauses : ComputableInPolyTime (fun p : I × ℕ => clauses p.1 p.2)
      (encPair encI encUnary) (encList encWiringClause))
    (hpart : ∀ (ι : I) (i : ℕ), i < depth ι → ClausesPartition (width ι (i + 1)) (clauses ι i)) :
    LayeredCircuit.HasPolyTimeWiringMLE encI
      (fun ι => LayeredCircuit.ofClauses (depth ι) (width ι) (clauses ι))
      (fun q => evalClausesMod q.modulus (width q.index (q.layer + 1)) (width q.index q.layer)
        q.gate (clauses q.index q.layer) q.z q.y q.w) where
  polyTime := by
    have hidx := encWiringMLEQuery_index_polyTime I encI ComputableInPolyTime.id'
    have hgate := encWiringMLEQuery_gate_polyTime I encI ComputableInPolyTime.id'
    have hlayer := encWiringMLEQuery_layer_polyTime I encI ComputableInPolyTime.id'
    have hmod := encWiringMLEQuery_modulus_polyTime I encI ComputableInPolyTime.id'
    have hz := encWiringMLEQuery_z_polyTime I encI ComputableInPolyTime.id'
    have hy := encWiringMLEQuery_y_polyTime I encI ComputableInPolyTime.id'
    have hw := encWiringMLEQuery_w_polyTime I encI ComputableInPolyTime.id'
    have hlayerSucc : ComputableInPolyTime (fun q : WiringMLEQuery I => q.layer + 1)
        (encWiringMLEQuery I encI) encUnary := by fun_prop
    exact computableInPolyTime_evalClausesMod hmod
      (hwidth.comp (hidx.prod hlayerSucc))
      (hwidth.comp (hidx.prod hlayer))
      hgate
      (hclauses.comp (hidx.prod hlayer))
      hz hy hw
  lt_modulus q hp := evalClausesMod_lt hp _ _ _ _ _ _ _
  eval_eq ι p _ g i hi zs ys ws := by
    dsimp only
    rw [natCast_evalClausesMod]
    exact (eval_multilinearExtension_wiringPred_ofClauses (depth := depth ι) (hpart ι i hi) g
      (vecOfList p (width ι (i + 1)) zs) (vecOfList p (width ι i) ys)
      (vecOfList p (width ι i) ws)).symm

/-! ### Concrete exponential-width uniform GKR family: fan-out + squaring + tree sum -/

/-- Parameters of `powerSumCircuit`: `2 ^ inWidth` inputs, `2 ^ midWidth` internal gates per layer
across one fan-out layer and `sqDepth` repeated-squaring layers, followed by `midWidth` binary-tree
addition layers reducing to `2 ^ 0 = 1` output gate. -/
structure PowerSumParams where
  /-- Input layer bit-width (`n = 2 ^ inWidth` inputs). -/
  inWidth : ℕ
  /-- Internal layer bit-width (`2 ^ midWidth` gates per internal layer). -/
  midWidth : ℕ
  /-- Number of repeated-squaring layers at width `midWidth`. -/
  sqDepth : ℕ

/-- Unary parameter encoding of `PowerSumParams`, of total length `O(inWidth + midWidth + sqDepth)
= O(log n + log S + d)`. -/
enc_structure encPowerSumParams : PowerSumParams where
  inWidth : encUnary,
  midWidth : encUnary,
  sqDepth : encUnary

namespace PowerSumParams

/-- Total depth of `powerSumCircuit P`: 1 fan-out addition layer (`x[prefix] + x[prefix]`),
`sqDepth` squaring layers, and `midWidth` binary-tree addition layers. -/
@[expose]
def depth (P : PowerSumParams) : ℕ :=
  1 + P.sqDepth + P.midWidth

/-- Bit-width of layer `i` in `powerSumCircuit P`. -/
@[expose]
def width (P : PowerSumParams) (i : ℕ) : ℕ :=
  if i = 0 then P.inWidth
  else if i ≤ 1 + P.sqDepth then P.midWidth
  else P.midWidth - (i - (1 + P.sqDepth))

/-- Single-clause specification of layer `i` in `powerSumCircuit P`:
* layer `0`: fan-out addition (`left a j = a[j]`, `right a j = a[j]` on the first `inWidth` bits,
  padded with `false` when `inWidth > midWidth`);
* layers `1 .. sqDepth`: elementwise squaring (`mul`, `left a = a`, `right a = a`);
* layers `1 + sqDepth .. depth - 1`: binary-tree sum (`add`, `left a = snoc a false`,
  `right a = snoc a true`). -/
@[expose]
def layerClauses (P : PowerSumParams) (i : ℕ) : List WiringClause :=
  if i = 0 then
    let lits := (List.range P.inWidth).map fun j =>
      if j < P.midWidth then WireLit.var j false else WireLit.const false
    [⟨.add, [], lits, lits⟩]
  else if i ≤ P.sqDepth then
    let lits := (List.range P.midWidth).map fun j => WireLit.var j false
    [⟨.mul, [], lits, lits⟩]
  else
    let kOut := P.width (i + 1)
    let base := (List.range kOut).map fun j => WireLit.var j false
    [⟨.add, [], base ++ [.const false], base ++ [.const true]⟩]

end PowerSumParams

/-- Concrete layered circuit for `P : PowerSumParams`, with `2 ^ P.midWidth` gates per internal
layer. -/
@[expose]
def powerSumCircuit (P : PowerSumParams) : LayeredCircuit :=
  LayeredCircuit.ofClauses P.depth P.width P.layerClauses

private theorem clausesPartition_singleton_unmasked (kOut : ℕ) (g : Gate)
    (litsL litsR : List WireLit) :
    ClausesPartition kOut [⟨g, [], litsL, litsR⟩] := by
  intro a
  have hm : (⟨g, [], litsL, litsR⟩ : WiringClause).matchesVec a = true := by
    simp [WiringClause.matchesVec, WiringClause.matchOpt]
  simp [hm]

private theorem clausesPartition_powerSum (P : PowerSumParams) (i : ℕ) :
    ClausesPartition (P.width (i + 1)) (P.layerClauses i) := by
  unfold PowerSumParams.layerClauses
  split_ifs <;> exact clausesPartition_singleton_unmasked _ _ _ _

/-- Prefix/padding operation computing the fan-out projection on raw bit lists:
take the first `inWidth` bits of `a` (when `a.length = midWidth`), padding with `false` if
`inWidth > a.length`. -/
private def padOrTakeBits (inWidth : ℕ) (a : List Bool) : List Bool :=
  (a ++ List.replicate inWidth false).take inWidth

private theorem padOrTakeBits_ofFn {midWidth kMid inWidth : ℕ} (hk : kMid = midWidth)
    (a : Fin kMid → Bool) :
    padOrTakeBits inWidth (List.ofFn a) =
      List.ofFn (fun ℓ : Fin inWidth =>
        (((List.range inWidth).map fun j =>
          if j < midWidth then WireLit.var j false else WireLit.const false).getD
            ℓ.val (WireLit.const false)).eval a) := by
  apply List.ext_getElem
  · simp [padOrTakeBits]
  · intro ℓ h1 h2
    have hℓ : ℓ < inWidth := by simpa only [List.length_ofFn] using h2
    simp only [padOrTakeBits, List.getElem_take, List.getElem_ofFn, List.getD_eq_getElem?_getD,
      List.getElem?_map, List.getElem?_range hℓ, Option.map_some, Option.getD_some]
    by_cases hm : ℓ < midWidth
    · have hkℓ : ℓ < kMid := by omega
      rw [List.getElem_append_left (by simp [hkℓ])]
      simp [hm, hkℓ, WireLit.eval]
    · have hnk : ¬ ℓ < kMid := by omega
      rw [List.getElem_append_right (by simp; omega)]
      simp [hm, WireLit.eval]

private theorem powerSum_width_tree_succ (P : PowerSumParams) {i : ℕ}
    (hi : i < P.depth) (hsq : ¬ i ≤ P.sqDepth) :
    P.width i = P.width (i + 1) + 1 := by
  have hi_lt : i < 1 + P.sqDepth + P.midWidth := hi
  have hne0 : i ≠ 0 := by omega
  have hne1 : i + 1 ≠ 0 := Nat.succ_ne_zero i
  have hgt1 : ¬ i + 1 ≤ 1 + P.sqDepth := by omega
  simp only [PowerSumParams.width, hne0, hne1, hgt1, ↓reduceIte]
  split_ifs with hle <;> omega

private theorem listOfFn_eval_id {kOut kIn kRng : ℕ} (hk : kIn = kOut) (hrng : kRng = kOut)
    (a : Fin kOut → Bool) :
    List.ofFn a =
      List.ofFn (fun ℓ : Fin kIn =>
        (((List.range kRng).map fun j => WireLit.var j false).getD
          ℓ.val (WireLit.const false)).eval a) := by
  apply List.ext_getElem (by simp [hk])
  intro ℓ h1 h2
  have hℓ : ℓ < kOut := by simpa only [List.length_ofFn] using h1
  have hget : (((List.range kRng).map fun j => WireLit.var j false).getD ℓ (WireLit.const false)) =
      WireLit.var ℓ false := by
    rw [hrng, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hℓ]
    rfl
  simp only [List.getElem_ofFn, hget, WireLit.eval, hℓ, ↓reduceDIte, Bool.bne_false]

private theorem listOfFn_eval_snoc {kOut kIn : ℕ} (hk : kIn = kOut + 1) (b : Bool)
    (a : Fin kOut → Bool) :
    List.ofFn a ++ [b] =
      List.ofFn (fun ℓ : Fin kIn =>
        ((((List.range kOut).map fun j => WireLit.var j false) ++ [WireLit.const b]).getD
          ℓ.val (WireLit.const false)).eval a) := by
  apply List.ext_getElem (by simp [hk])
  intro ℓ h1 h2
  have hℓ : ℓ < kIn := by simpa only [List.length_ofFn] using h2
  by_cases hlt : ℓ < kOut
  · have hget : ((((List.range kOut).map fun j => WireLit.var j false) ++
        [WireLit.const b]).getD ℓ (WireLit.const false)) = WireLit.var ℓ false := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hlt]),
        List.getElem?_map, List.getElem?_range hlt]
      rfl
    rw [List.getElem_append_left (by simp [hlt])]
    simp only [List.getElem_ofFn, hget, WireLit.eval, hlt, ↓reduceDIte, Bool.bne_false]
  · have heq : ℓ = kOut := by omega
    have hlen : (List.ofFn a).length = kOut := List.length_ofFn
    have hlenL : ((List.range kOut).map fun j => WireLit.var j false).length = kOut := by simp
    have hget : ((((List.range kOut).map fun j => WireLit.var j false) ++
        [WireLit.const b]).getD ℓ (WireLit.const false)) = WireLit.const b := by
      rw [heq, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlenL,
        Nat.sub_self, List.getElem?_singleton]
      rfl
    have hlhs : (List.ofFn a ++ [b])[ℓ]'h1 = b := by
      rw [List.getElem_append_right (by omega)]
      simp [hlen, heq]
    rw [hlhs, List.getElem_ofFn, hget, WireLit.eval]

/-- **`powerSumCircuit` is log-space uniform.** -/
theorem isLogSpaceUniform_powerSumCircuit :
    LayeredCircuit.IsLogSpaceUniform encPowerSumParams powerSumCircuit := by
  have hPFields : ComputableInLogSpace
      (fun P : PowerSumParams => (P.inWidth, P.midWidth, P.sqDepth))
      encPowerSumParams encPowerSumParamsFields :=
    ComputableInLogSpace.of_eq encPowerSumParams_apply
  have hInW : ComputableInLogSpace PowerSumParams.inWidth encPowerSumParams encUnary :=
    ComputableInLogSpace.fst' hPFields
  have hMidW : ComputableInLogSpace PowerSumParams.midWidth encPowerSumParams encUnary :=
    ComputableInLogSpace.fst' (ComputableInLogSpace.snd' hPFields)
  have hSqD : ComputableInLogSpace PowerSumParams.sqDepth encPowerSumParams encUnary :=
    ComputableInLogSpace.snd' (ComputableInLogSpace.snd' hPFields)
  have hDepth : ComputableInLogSpace (fun P => (powerSumCircuit P).depth)
      encPowerSumParams encUnary := by
    change ComputableInLogSpace (fun P : PowerSumParams => 1 + P.sqDepth + P.midWidth)
      encPowerSumParams encUnary
    exact ComputableInLogSpace.unaryAdd
      (ComputableInLogSpace.unaryAdd (ComputableInLogSpace.const 1) hSqD) hMidW
  have hWidth : ComputableInLogSpace (fun q : PowerSumParams × ℕ => (powerSumCircuit q.1).width q.2)
      (encPair encPowerSumParams encUnary) encUnary := by
    change ComputableInLogSpace (fun q : PowerSumParams × ℕ => q.1.width q.2)
      (encPair encPowerSumParams encUnary) encUnary
    unfold PowerSumParams.width
    have hP := ComputableInLogSpace.fst encPowerSumParams encUnary
    have hi := ComputableInLogSpace.snd encPowerSumParams encUnary
    have hInW' := hInW.comp' hP
    have hMidW' := hMidW.comp' hP
    have h1Sq := ComputableInLogSpace.unaryAdd (ComputableInLogSpace.const 1) (hSqD.comp' hP)
    exact ComputableInLogSpace.ite_decide
      (ComputableInLogSpace.unaryEq hi (ComputableInLogSpace.const 0)) hInW'
      (ComputableInLogSpace.ite_decide (ComputableInLogSpace.unaryLe hi h1Sq) hMidW'
        (ComputableInLogSpace.unarySub hMidW' (ComputableInLogSpace.unarySub hi h1Sq)))
  have hGqFields : ComputableInLogSpace
      (fun q : GateQuery PowerSumParams => (q.index, q.layer, q.outGate))
      (encGateQuery PowerSumParams encPowerSumParams)
      (encGateQueryFields PowerSumParams encPowerSumParams) :=
    ComputableInLogSpace.of_eq (encGateQuery_apply PowerSumParams encPowerSumParams)
  have hqP := ComputableInLogSpace.fst' hGqFields
  have hqI := ComputableInLogSpace.fst' (ComputableInLogSpace.snd' hGqFields)
  have hqA := ComputableInLogSpace.snd' (ComputableInLogSpace.snd' hGqFields)
  let gateAt : GateQuery PowerSumParams → Gate := fun q =>
    if q.layer = 0 then .add else if q.layer ≤ q.index.sqDepth then .mul else .add
  let sideAt (b : Bool) : GateQuery PowerSumParams → List Bool := fun q =>
    if q.layer = 0 then padOrTakeBits q.index.inWidth q.outGate
    else if q.layer ≤ q.index.sqDepth then q.outGate
    else q.outGate ++ [b]
  have hCond0 := ComputableInLogSpace.unaryEq hqI (ComputableInLogSpace.const 0)
  have hCondSq := ComputableInLogSpace.unaryLe hqI (hSqD.comp' hqP)
  have hPadTake : ComputableInLogSpace
      (fun q : GateQuery PowerSumParams => padOrTakeBits q.index.inWidth q.outGate)
      (encGateQuery PowerSumParams encPowerSumParams) encBits := by
    unfold padOrTakeBits
    exact ComputableInLogSpace.bitsTake'
      (ComputableInLogSpace.bitsAppend hqA
        (ComputableInLogSpace.bitsReplicate (hInW.comp' hqP) (ComputableInLogSpace.const false)))
      (hInW.comp' hqP)
  have hGateAt : ComputableInLogSpace gateAt
      (encGateQuery PowerSumParams encPowerSumParams) encGate :=
    ComputableInLogSpace.ite_decide hCond0 (ComputableInLogSpace.const Gate.add)
      (ComputableInLogSpace.ite_decide hCondSq
        (ComputableInLogSpace.const Gate.mul) (ComputableInLogSpace.const Gate.add))
  have hSideAt : ∀ b, ComputableInLogSpace (sideAt b)
      (encGateQuery PowerSumParams encPowerSumParams) encBits := fun b =>
    ComputableInLogSpace.ite_decide hCond0 hPadTake
      (ComputableInLogSpace.ite_decide hCondSq hqA
        (ComputableInLogSpace.bitsAppend hqA (ComputableInLogSpace.const [b])))
  have hmUnmasked : ∀ {k : ℕ} (g : Gate) (l1 l2 : List WireLit) (a : Fin k → Bool),
      (⟨g, [], l1, l2⟩ : WiringClause).matchesVec a = true := by
    intro k g l1 l2 a
    simp [WiringClause.matchesVec, WiringClause.matchOpt]
  have hSideEq : ∀ b (P : PowerSumParams) (i : ℕ), i < P.depth →
      ∀ a : Fin (P.width (i + 1)) → Bool,
        sideAt b ⟨P, i, List.ofFn a⟩ =
          List.ofFn
            (if b then (powerSumCircuit P).right i a else (powerSumCircuit P).left i a) := by
    intro b P i hi a
    dsimp only [powerSumCircuit, LayeredCircuit.ofClauses]
    simp only [sideAt, PowerSumParams.layerClauses]
    by_cases h0 : i = 0
    · subst h0
      have hw1 : P.width 1 = P.midWidth := by simp [PowerSumParams.width]
      cases b
      · simp only [↓reduceIte, List.find?_singleton, hmUnmasked, Option.elim_some]
        exact padOrTakeBits_ofFn hw1 a
      · simp only [↓reduceIte, List.find?_singleton, hmUnmasked, Option.elim_some]
        exact padOrTakeBits_ofFn hw1 a
    · by_cases hsq : i ≤ P.sqDepth
      · have hwi : P.width i = P.midWidth := by
          simp [PowerSumParams.width, h0, show i ≤ 1 + P.sqDepth by omega]
        have hwi1 : P.width (i + 1) = P.midWidth := by
          simp [PowerSumParams.width, show i + 1 ≤ 1 + P.sqDepth by omega]
        cases b
        · simp only [h0, hsq, ↓reduceIte, List.find?_singleton, hmUnmasked, Option.elim_some]
          exact listOfFn_eval_id (by omega) hwi1.symm a
        · simp only [h0, hsq, ↓reduceIte, List.find?_singleton, hmUnmasked, Option.elim_some]
          exact listOfFn_eval_id (by omega) hwi1.symm a
      · have hrel := powerSum_width_tree_succ P hi hsq
        cases b
        · simp only [h0, hsq, ↓reduceIte, List.find?_singleton, hmUnmasked, Option.elim_some]
          exact listOfFn_eval_snoc hrel false a
        · simp only [h0, hsq, ↓reduceIte, List.find?_singleton, hmUnmasked, Option.elim_some]
          exact listOfFn_eval_snoc hrel true a
  refine LayeredCircuit.IsLogSpaceUniform.of_neighbours hDepth hWidth hGateAt
    (hSideAt false) (hSideAt true)
    (fun P i hi => ?_) (fun P i hi a => hSideEq false P i hi a)
    (fun P i hi a => hSideEq true P i hi a)
  · dsimp only [powerSumCircuit, LayeredCircuit.ofClauses]
    intro a
    simp only [gateAt, PowerSumParams.layerClauses]
    by_cases h0 : i = 0
    · subst h0; simp [hmUnmasked]
    · by_cases hsq : i ≤ P.sqDepth <;> simp [h0, hsq, hmUnmasked]

/-- Modular wiring-MLE evaluator for `powerSumCircuit`. -/
def evalPowerSumWiring (q : WiringMLEQuery PowerSumParams) : ℕ :=
  evalClausesMod q.modulus (q.index.width (q.layer + 1)) (q.index.width q.layer)
    q.gate (q.index.layerClauses q.layer) q.z q.y q.w

private lemma layerClauses_polyTime :
    ComputableInPolyTime (fun q : PowerSumParams × ℕ => q.1.layerClauses q.2)
      (encPair encPowerSumParams encUnary) (encList encWiringClause) := by
  open ComputableInPolyTime in
  unfold PowerSumParams.layerClauses
  have hP := fst encPowerSumParams encUnary
  have hi := snd encPowerSumParams encUnary
  have hMidW := encPowerSumParams_midWidth_polyTime hP
  have hSqD := encPowerSumParams_sqDepth_polyTime hP
  have hCond0 : ComputableInPolyTime (fun q : PowerSumParams × ℕ => decide (q.2 = 0))
      (encPair encPowerSumParams encUnary) encBool := by fun_prop
  have hCondSq : ComputableInPolyTime (fun q : PowerSumParams × ℕ => decide (q.2 ≤ q.1.sqDepth))
      (encPair encPowerSumParams encUnary) encBool := unary_le.comp (hi.prod hSqD)
  have hVarLit : ∀ {γ : Type} {e : γ ↪ List Bool} {j : γ → ℕ},
      ComputableInPolyTime j e encUnary →
      ComputableInPolyTime (fun x => WireLit.var (j x) false) e encWireLit := fun hj =>
    encWireLit_var_polyTime (unary_to_binary.comp hj) (const false)
  have hBranch0 : ComputableInPolyTime
      (fun q : PowerSumParams × ℕ =>
        let lits := (List.range q.1.inWidth).map fun j =>
          if j < q.1.midWidth then WireLit.var j false else WireLit.const false
        ([⟨.add, [], lits, lits⟩] : List WiringClause))
      (encPair encPowerSumParams encUnary) (encList encWiringClause) := by
    have hr : ComputableInPolyTime (fun q : PowerSumParams × ℕ => List.range q.1.inWidth)
        (encPair encPowerSumParams encUnary) (encList encUnary) := by fun_prop
    have hlt : ComputableInPolyTime
        (fun u : (PowerSumParams × ℕ) × ℕ => decide (u.2 < u.1.1.midWidth))
        (encPair (encPair encPowerSumParams encUnary) encUnary) encBool :=
      unary_lt.comp ((snd _ _).prod (hMidW.comp (fst _ _)))
    have hlits := mapWith (ite_decide hlt (hVarLit (snd _ _)) (const (.const false))) id' hr
    have hcl := encWiringClause_mk_polyTime (const Gate.add) (const []) hlits hlits
    exact hcl.cons' (const [])
  have hBranchSq : ComputableInPolyTime
      (fun q : PowerSumParams × ℕ =>
        let lits := (List.range q.1.midWidth).map fun j => WireLit.var j false
        ([⟨.mul, [], lits, lits⟩] : List WiringClause))
      (encPair encPowerSumParams encUnary) (encList encWiringClause) := by
    have hr : ComputableInPolyTime (fun q : PowerSumParams × ℕ => List.range q.1.midWidth)
        (encPair encPowerSumParams encUnary) (encList encUnary) := by fun_prop
    have hlits := mapWith (hVarLit (snd _ _)) id' hr
    have hcl := encWiringClause_mk_polyTime (const Gate.mul) (const []) hlits hlits
    exact hcl.cons' (const [])
  have hBranchTree : ComputableInPolyTime
      (fun q : PowerSumParams × ℕ =>
        let kOut := q.1.width (q.2 + 1)
        let base := (List.range kOut).map fun j => WireLit.var j false
        ([⟨.add, [], base ++ [.const false], base ++ [.const true]⟩] : List WiringClause))
      (encPair encPowerSumParams encUnary) (encList encWiringClause) := by
    have hi1 : ComputableInPolyTime (fun q : PowerSumParams × ℕ => q.2 + 1)
        (encPair encPowerSumParams encUnary) encUnary := by fun_prop
    have hkOut : ComputableInPolyTime (fun q : PowerSumParams × ℕ => q.1.width (q.2 + 1))
        (encPair encPowerSumParams encUnary) encUnary :=
      isLogSpaceUniform_powerSumCircuit.width_polyTime.comp (hP.prod hi1)
    have hr : ComputableInPolyTime (fun q : PowerSumParams × ℕ => List.range (q.1.width (q.2 + 1)))
        (encPair encPowerSumParams encUnary) (encList encUnary) :=
      (by fun_prop : ComputableInPolyTime List.range encUnary (encList encUnary)).comp hkOut
    have hbase : ComputableInPolyTime
        (fun q : PowerSumParams × ℕ =>
          (List.range (q.1.width (q.2 + 1))).map fun j => WireLit.var j false)
        (encPair encPowerSumParams encUnary) (encList encWireLit) :=
      mapWith (hVarLit (snd _ _)) id' hr
    have hlL := hbase.listAppend' (const [WireLit.const false])
    have hlR := hbase.listAppend' (const [WireLit.const true])
    have hcl := encWiringClause_mk_polyTime (const Gate.add) (const []) hlL hlR
    exact hcl.cons' (const [])
  exact ite_decide hCond0 hBranch0 (ite_decide hCondSq hBranchSq hBranchTree)

/-- **`powerSumCircuit` admits polynomial-time wiring MLE evaluation.** -/
theorem hasPolyTimeWiringMLE_powerSumCircuit :
    LayeredCircuit.HasPolyTimeWiringMLE encPowerSumParams powerSumCircuit evalPowerSumWiring :=
  hasPolyTimeWiringMLE_ofClauses
    isLogSpaceUniform_powerSumCircuit.width_polyTime
    layerClauses_polyTime
    (fun P i _ => clausesPartition_powerSum P i)

/-- Concrete `UniformGKRFamily` for `powerSumCircuit`: internal layers have `2 ^ midWidth` gates
while parameter descriptions and wiring-MLE queries have size `O(inWidth + midWidth + sqDepth)`. -/
@[expose]
def powerSumGKRFamily : UniformGKRFamily PowerSumParams encPowerSumParams where
  circuit := powerSumCircuit
  evalWiring := evalPowerSumWiring
  uniform := isLogSpaceUniform_powerSumCircuit
  wiringMLE := hasPolyTimeWiringMLE_powerSumCircuit

end Cslib.Interactive.GKR
