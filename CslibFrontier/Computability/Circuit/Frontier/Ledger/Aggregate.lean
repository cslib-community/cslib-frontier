/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Threshold
public import CslibFrontier.Computability.Circuit.Frontier.Ledger.Basic
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Data.ZMod.Defs
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.ZMod.Basic

/-!
# Aggregate gates and threshold monoids

An operation of arity `k` *aggregates* in a commutative monoid `T` when its value is read off a
product of contributions of its arguments: `f x = ψ (∏ i, φ i (x i))`. Every operation of the
Boolean basis of unbounded fan-in (negation, and conjunction and disjunction of any number of
arguments) aggregates in `ZMod 2` under multiplication, and every function of the number of true
arguments modulo `m`, such as parity and `MOD_m`, aggregates in `ZMod m` under addition.

Truncated natural addition on `{0, ..., t}` (`Frontier.TruncAdd t`, of cardinality `t + 1` with
product `min (a + b) t`) extends aggregation to threshold, exact-weight, majority, symmetric, and
bounded-weight integer linear threshold gates:

* `Th^k_j` (`Cslib.threshold k j`) aggregates in `TruncAdd j` (`|T| = j + 1`);
* exact Hamming weight `weight x = j` aggregates in `TruncAdd (j + 1)` (`|T| = j + 2`);
* majority (`Cslib.majority k`) aggregates in `TruncAdd ⌈k / 2⌉`, and every symmetric Boolean
  function on `k` bits aggregates in `TruncAdd k` (`|T| = k + 1`);
* any Boolean predicate of a signed integer linear form `∑ i, w_i x_i` with `∑ i |w_i| ≤ W`, in
  particular any bounded-weight linear threshold gate `LTF`, aggregates in `TruncAdd W`
  (`|T| = W + 1`).

If every special gate of a program aggregates in `T`, the special gates have a ledger in the
monoid `T ^ k` of functions from the `k` special gates to `T` (`Frontier.Ledger.ofAggregates`).

## Main definitions

* `Cslib.Circuits.Frontier.Aggregates`: an operation aggregates in a commutative monoid.
* `Cslib.Circuits.Frontier.Ledger.ofAggregates`: the ledger of aggregate gates.
* `Cslib.Circuits.Frontier.TruncAdd`: `{0, ..., t}` as a commutative monoid under `min (a + b) t`.

## Main results

* `Cslib.Circuits.Frontier.aggregates_unbounded`: the operations of the Boolean basis of
  unbounded fan-in aggregate in `ZMod 2`.
* `Cslib.Circuits.Frontier.aggregates_countMod`: functions of the number of true arguments
  modulo `m` aggregate in `ZMod m`.
* `Cslib.Circuits.Frontier.aggregates_threshold`,
  `Cslib.Circuits.Frontier.aggregates_exactWeight`,
  `Cslib.Circuits.Frontier.aggregates_majority`,
  `Cslib.Circuits.Frontier.aggregates_strictMajority`,
  `Cslib.Circuits.Frontier.aggregates_isSymmetric`,
  `Cslib.Circuits.Frontier.aggregates_thresholdOp`: threshold, exact-weight, majority, and
  symmetric Boolean gates aggregate in `TruncAdd`.
* `Cslib.Circuits.Frontier.aggregates_weightedSum`,
  `Cslib.Circuits.Frontier.aggregates_ltf`: bounded-weight integer linear forms and linear
  threshold gates aggregate in `TruncAdd W`.
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

universe v

variable {U : Type*}

/-- An operation of arity `k` *aggregates* in a commutative monoid `T` when its value is read
off a product of contributions of its arguments. -/
def Aggregates {k : ℕ} (f : (Fin k → U) → U) (T : Type*) [CommMonoid T] : Prop :=
  ∃ (φ : Fin k → U → T) (ψ : T → U), ∀ x, f x = ψ (∏ i, φ i (x i))

open Classical in
/-- **Aggregate gates have a ledger.** If every special gate of a program aggregates in `T`,
the special gates have a ledger in the monoid of functions from the special gates to `T`: a wire
contributes to a special gate the product of its contributions to the slots of that gate that read
it, and each special gate reads off its own coordinate. -/
noncomputable def Ledger.ofAggregates {σ : Signature.{v}} {n s : ℕ} {special : Fin s → Prop}
    {p : Program σ n s} {I : Interpretation σ U} {T : Type*} [CommMonoid T]
    (h : ∀ g : Fin s, special g → Aggregates (I (p.lines g).op) T) :
    Ledger special p I ({g // special g} → T) where
  contribution w u g := ∏ a with (p.lines g).wires a = w, (h g g.property).choose a u
  readout m g := (h g g.property).choose_spec.choose (m g)
  readout_prod v g := by
    simp only [Finset.prod_apply, (h g g.property).choose_spec.choose_spec]
    refine congrArg (h g g.property).choose_spec.choose ?_
    -- Group the slots of `g` by the wire they read.
    rw [← Finset.prod_fiberwise Finset.univ (p.lines g).wires]
    refine Finset.prod_congr rfl fun w _ => Finset.prod_congr rfl fun a ha => ?_
    rw [(Finset.mem_filter.1 ha).2]

/-- **The Boolean basis of unbounded fan-in aggregates.** Negation, conjunction and disjunction
of any number of arguments aggregate in `ZMod 2` under multiplication: a conjunction is the
product of its arguments read as `1` for true and `0` for false, and a disjunction is the
negation of the product of the negations. -/
theorem aggregates_unbounded (op : Boolean.Unbounded.Op) :
    Aggregates (Boolean.Unbounded.interpretation op) (ZMod 2) := by
  cases op with
  | not => exact ⟨fun _ b => if b then 0 else 1, fun t => decide (t = 1), fun x => by
      cases h : x 0 <;> simp [h]⟩
  | and m => exact ⟨fun _ b => if b then 1 else 0, fun t => decide (t = 1), fun x => by
      simp [Finset.prod_boole]⟩
  | or m => exact ⟨fun _ b => if !b then 1 else 0, fun t => decide (t ≠ 1), fun x => by
      simp [Finset.prod_boole]⟩

open Finset in
/-- **Counting modulo `m` aggregates.** Every function of the number of true arguments modulo
`m` aggregates in `ZMod m` under addition: each true argument contributes `1` to the count.
Parity and the `MOD_m` gates are of this form. -/
theorem aggregates_countMod (k m : ℕ) (f : ZMod m → Bool) :
    Aggregates (fun x : Fin k → Bool => f (#{i | x i = true} : ℕ)) (Multiplicative (ZMod m)) :=
  ⟨fun _ b => .ofAdd (if b then 1 else 0), fun t => f t.toAdd, fun x => by
    simp [toAdd_prod, Finset.sum_boole]⟩

/-! ### Truncated addition monoid and threshold / LTF gates -/

/-- Natural numbers `{0, ..., t}` under addition truncated at `t` (`min (a + b) t`), packaged as a
finite commutative monoid of cardinality `t + 1`. -/
structure TruncAdd (t : ℕ) where
  /-- The underlying natural value in `{0, ..., t}`. -/
  val : ℕ
  /-- The upper bound `val ≤ t`. -/
  le_top : val ≤ t
  deriving DecidableEq

namespace TruncAdd

variable {t : ℕ}

/-- Two elements of `TruncAdd t` are equal when their underlying naturals agree. -/
@[ext]
theorem ext {a b : TruncAdd t} (h : a.val = b.val) : a = b := by
  cases a
  cases b
  cases h
  rfl

/-- Equivalence between `TruncAdd t` and `Fin (t + 1)`. -/
def equivFin (t : ℕ) : TruncAdd t ≃ Fin (t + 1) where
  toFun a := ⟨a.val, Nat.lt_succ_of_le a.le_top⟩
  invFun i := ⟨i.val, Nat.le_of_lt_succ i.isLt⟩
  left_inv a := by cases a; rfl
  right_inv i := by cases i; rfl

instance (t : ℕ) : Fintype (TruncAdd t) :=
  Fintype.ofEquiv (Fin (t + 1)) (equivFin t).symm

instance (t : ℕ) : Finite (TruncAdd t) :=
  Finite.of_fintype (TruncAdd t)

/-- `TruncAdd t` has `t + 1` elements (`Fintype.card`). -/
@[simp] theorem fintypeCard (t : ℕ) : Fintype.card (TruncAdd t) = t + 1 := by
  rw [Fintype.card_congr (equivFin t), Fintype.card_fin]

/-- `TruncAdd t` has `t + 1` elements (`Nat.card`). -/
theorem card (t : ℕ) : Nat.card (TruncAdd t) = t + 1 := by
  rw [Nat.card_eq_fintype_card, fintypeCard]

instance (t : ℕ) : CommMonoid (TruncAdd t) where
  one := ⟨0, Nat.zero_le t⟩
  mul a b := ⟨min (a.val + b.val) t, min_le_right _ _⟩
  mul_assoc a b c := by
    apply ext
    change min (min (a.val + b.val) t + c.val) t = min (a.val + min (b.val + c.val) t) t
    omega
  one_mul a := by
    apply ext
    have := a.le_top
    change min (0 + a.val) t = a.val
    omega
  mul_one a := by
    apply ext
    have := a.le_top
    change min (a.val + 0) t = a.val
    omega
  mul_comm a b := by
    apply ext
    change min (a.val + b.val) t = min (b.val + a.val) t
    omega

/-- The identity of `TruncAdd t` has value `0`. -/
@[simp] theorem val_one (t : ℕ) : (1 : TruncAdd t).val = 0 :=
  rfl

/-- Multiplication in `TruncAdd t` is truncated addition `min (a + b) t`. -/
@[simp] theorem val_mul (a b : TruncAdd t) : (a * b).val = min (a.val + b.val) t :=
  rfl

/-- Clamp an arbitrary natural number into `TruncAdd t` via `min n t`. -/
def ofNat (t n : ℕ) : TruncAdd t :=
  ⟨min n t, min_le_right n t⟩

/-- `ofNat t n` has value `min n t`. -/
@[simp] theorem val_ofNat (t n : ℕ) : (ofNat t n).val = min n t :=
  rfl

/-- A product of clamped naturals in `TruncAdd t` evaluates to the clamped sum. -/
theorem val_prod_ofNat {ι : Type*} (s : Finset ι) (t : ℕ) (c : ι → ℕ) :
    (∏ i ∈ s, ofNat t (c i)).val = min (∑ i ∈ s, c i) t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, val_mul, val_ofNat, ih]
    omega

end TruncAdd

/-- **Threshold gates `Th^k_j` aggregate in `TruncAdd j`** (`|T| = j + 1`). -/
theorem aggregates_threshold (k j : ℕ) :
    Aggregates (Cslib.threshold k j) (TruncAdd j) :=
  ⟨fun _ b => TruncAdd.ofNat j b.toNat, fun m => decide (m.val = j), fun x => by
    dsimp only
    rw [Cslib.threshold_apply, BitString.weight_eq_sum_toNat, TruncAdd.val_prod_ofNat]
    exact decide_eq_decide.mpr ⟨fun h => min_eq_right h, fun h => h ▸ min_le_left _ _⟩⟩

/-- **Exact-weight gates `EXACT^k_j` aggregate in `TruncAdd (j + 1)`** (`|T| = j + 2`). -/
theorem aggregates_exactWeight (k j : ℕ) :
    Aggregates (fun x : Fin k → Bool => decide (BitString.weight x = j)) (TruncAdd (j + 1)) :=
  ⟨fun _ b => TruncAdd.ofNat (j + 1) b.toNat, fun m => decide (m.val = j), fun x => by
    dsimp only
    rw [BitString.weight_eq_sum_toNat, TruncAdd.val_prod_ofNat]
    exact decide_eq_decide.mpr (by omega)⟩

/-- **Majority gates `MAJ_k` aggregate in `TruncAdd ⌈k / 2⌉`** (`|T| = (k + 1) / 2 + 1`). -/
theorem aggregates_majority (k : ℕ) :
    Aggregates (Cslib.majority k) (TruncAdd ((k + 1) / 2)) :=
  aggregates_threshold k ((k + 1) / 2)

/-- **Strict majority gates aggregate in `TruncAdd (⌊k / 2⌋ + 1)`.** -/
theorem aggregates_strictMajority (k : ℕ) :
    Aggregates (Cslib.strictMajority k) (TruncAdd (k / 2 + 1)) :=
  aggregates_threshold k (k / 2 + 1)

/-- **Every symmetric Boolean function on `k` bits aggregates in `TruncAdd k`** (`|T| = k + 1`). -/
theorem aggregates_isSymmetric {k : ℕ} {f : BooleanFunction k} (hf : f.IsSymmetric) :
    Aggregates f (TruncAdd k) := by
  obtain ⟨g, hg⟩ := hf.exists_eq_comp_weight
  refine ⟨fun _ b => TruncAdd.ofNat k b.toNat, fun m => g m.val, fun x => ?_⟩
  dsimp only
  rw [← hg x, TruncAdd.val_prod_ofNat, ← BitString.weight_eq_sum_toNat,
    min_eq_left (BitString.weight_le_length x)]

/-- **Operations of `Boolean.Threshold.Op` with cutoff at most `j` aggregate in `TruncAdd j`**
(for negation, `1 ≤ j`). -/
theorem aggregates_thresholdOp {j : ℕ} (op : Boolean.Threshold.Op)
    (hj : match op with | .not => 1 ≤ j | .threshold _ c => c ≤ j) :
    Aggregates (Boolean.Threshold.interpretation op) (TruncAdd j) := by
  cases op with
  | not =>
    refine ⟨fun _ b => TruncAdd.ofNat j (!b).toNat, fun m => decide (1 ≤ m.val), fun x => ?_⟩
    dsimp only
    rw [Boolean.Threshold.interpretation_not, TruncAdd.val_prod_ofNat, Finset.univ_unique,
      Fin.default_eq_zero, Finset.sum_singleton]
    cases x 0 <;> simp [hj]
  | threshold k c =>
    change Aggregates (Cslib.threshold k c) (TruncAdd j)
    refine ⟨fun _ b => TruncAdd.ofNat j b.toNat, fun m => decide (c ≤ m.val), fun x => ?_⟩
    dsimp only
    rw [Cslib.threshold_apply, BitString.weight_eq_sum_toNat, TruncAdd.val_prod_ofNat]
    exact decide_eq_decide.mpr (by omega)

/-- **Boolean predicates of bounded-weight integer linear forms aggregate in `TruncAdd W`.** Let
`w : Fin k → ℤ` satisfy `∑ i |w_i| ≤ W`, and let `P : ℤ → Bool` be any Boolean predicate on `ℤ`.
Shifting each negative weight `w_i < 0` by `-w_i` converts `∑_{x_i = true} w_i` into a sum in
`{0, ..., W}`, so the operation aggregates in `TruncAdd W` (`|T| = W + 1`). -/
theorem aggregates_weightedSum {k W : ℕ} (w : Fin k → ℤ) (hW : (∑ i, (w i).natAbs) ≤ W)
    (P : ℤ → Bool) :
    Aggregates (fun x : Fin k → Bool => P (∑ i, if x i then w i else 0)) (TruncAdd W) := by
  let c : Fin k → Bool → ℕ := fun i b =>
    if 0 ≤ w i then (if b then (w i).toNat else 0) else (if b then 0 else (-w i).toNat)
  have hc_le (i : Fin k) (b : Bool) : c i b ≤ (w i).natAbs := by
    dsimp only [c]
    split_ifs <;> omega
  have hc_eq (i : Fin k) (b : Bool) :
      (c i b : ℤ) + min (w i) 0 = if b then w i else 0 := by
    dsimp only [c]
    cases b <;> split_ifs <;> omega
  refine ⟨fun i b => TruncAdd.ofNat W (c i b),
    fun m => P ((m.val : ℤ) + ∑ i, min (w i) 0), fun x => ?_⟩
  dsimp only
  have hsum_le : (∑ i, c i (x i)) ≤ W :=
    (Finset.sum_le_sum fun i _ => hc_le i (x i)).trans hW
  rw [TruncAdd.val_prod_ofNat, min_eq_left hsum_le]
  refine congrArg P ?_
  rw [Nat.cast_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => (hc_eq i (x i)).symm

/-- **Linear threshold gates (`LTF`) with integer weight `L₁`-norm at most `W` aggregate in
`TruncAdd W`** (`|T| = W + 1`). -/
theorem aggregates_ltf {k W : ℕ} (w : Fin k → ℤ) (θ : ℤ) (hW : (∑ i, (w i).natAbs) ≤ W) :
    Aggregates (fun x : Fin k → Bool => decide (θ ≤ ∑ i, if x i then w i else 0)) (TruncAdd W) :=
  aggregates_weightedSum w hW fun s => decide (θ ≤ s)

end Cslib.Circuits.Frontier
