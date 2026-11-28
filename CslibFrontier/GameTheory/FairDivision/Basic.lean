/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Algorithms.Lean.Query.FreeM
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.IntermediateValue

/-!
# Cake-Cutting Valuations, Interval Partitions, and Robertson–Webb Queries

Foundational definitions for proportional and envy-free cake cutting on `[0, 1]`
([Steinhaus1948]; [DubinsSpanier1961]; [RobertsonWebb1998]):

* `CakeValuation`: a normalized (`v 0 1 = 1`), nonnegative, finite additive interval valuation on
  `[0, 1]` vanishing on degenerate/reversed intervals (`b ≤ a → v a b = 0`) with continuous
  cumulative value `x ↦ v 0 x` on `[0, 1]`. Continuity yields the intermediate-value cut property
  `CakeValuation.exists_cut` without requiring strict positivity on every nonempty subinterval, so
  piecewise-uniform valuations with zero-density regions are admitted alongside strictly positive
  densities.
* `CakePiece`, `intervalsOfCuts`, and `DividedCake`: finite partitions of `[0, 1]` induced by an
  ordered list of physical cut points `0 ≤ c₁ ≤ … ≤ cₖ ≤ 1`, together with bundle assignment to
  `n` agents, proportionality (`DividedCake.IsProportional`), and envy-freeness
  (`DividedCake.IsEnvyFree`). Every envy-free valid partition of `[0, 1]` is proportional
  (`DividedCake.IsEnvyFree.isProportional`).
* `RWQuery`: the Robertson–Webb query signature (`eval` and `cut`) in `Cslib.FreeM`, together with
  oracle validity (`RWQuery.IsValidOracle`), subinterval-clamped cuts (`RWQuery.cutIn`), and the
  canonical intermediate-value oracle `RWQuery.oracleOf`.

## Main definitions

* `Cslib.GameTheory.FairDivision.CakeValuation`: nonatomic additive normalized cake valuation on
  `[0, 1]`.
* `Cslib.GameTheory.FairDivision.CakeValuation.ofCDF`,
  `Cslib.GameTheory.FairDivision.CakeValuation.uniform`,
  `Cslib.GameTheory.FairDivision.CakeValuation.affine`,
  `Cslib.GameTheory.FairDivision.CakeValuation.uniformOn`,
  `Cslib.GameTheory.FairDivision.CakeValuation.convexComb`: cumulative-distribution, uniform,
  affine-density, interval-supported piecewise-uniform, and convex-combination constructors.
* `Cslib.GameTheory.FairDivision.CakePiece`: interval piece `[left, right]`.
* `Cslib.GameTheory.FairDivision.OrderedCutsOn`,
  `Cslib.GameTheory.FairDivision.intervalsOfCutsOn`,
  `Cslib.GameTheory.FairDivision.intervalsOfCuts`: ordered interior cuts and induced interval
  tilings.
* `Cslib.GameTheory.FairDivision.DividedCake`: cut list paired with per-agent interval bundles.
* `Cslib.GameTheory.FairDivision.DividedCake.IsValidPartition`,
  `Cslib.GameTheory.FairDivision.DividedCake.IsContiguous`,
  `Cslib.GameTheory.FairDivision.DividedCake.IsProportional`,
  `Cslib.GameTheory.FairDivision.DividedCake.IsEnvyFree`: structural and fairness predicates.
* `Cslib.GameTheory.FairDivision.RWQuery`,
  `Cslib.GameTheory.FairDivision.RWQuery.IsValidOracle`,
  `Cslib.GameTheory.FairDivision.RWQuery.oracleOf`,
  `Cslib.GameTheory.FairDivision.RWQuery.liftFin`: Robertson–Webb query functor, oracle interface,
  and size-uniform query embedding.

## Main results

* `Cslib.GameTheory.FairDivision.CakeValuation.exists_cut`: intermediate-value existence of a cut
  point `x ∈ [a, 1]` achieving any target value `α ∈ [0, v a 1]`.
* `Cslib.GameTheory.FairDivision.bundleVal_intervalsOfCutsOn`,
  `Cslib.GameTheory.FairDivision.bundleVal_intervalsOfCuts`: ordered cuts conserve total valuation.
* `Cslib.GameTheory.FairDivision.iUnion_Icc_intervalsOfCutsOn`,
  `Cslib.GameTheory.FairDivision.pairwise_disjoint_Ioo_intervalsOfCutsOn`: ordered cuts tile
  `[a, b]` by interior-disjoint closed intervals.
* `Cslib.GameTheory.FairDivision.DividedCake.IsEnvyFree.isProportional`: every envy-free valid
  partition of `[0, 1]` gives every agent at least `1 / n`.
* `Cslib.GameTheory.FairDivision.RWQuery.isValidOracle_oracleOf`: every valuation profile admits a
  valid Robertson–Webb oracle.

## References

* [H. Steinhaus, *The Problem of Fair Division*][Steinhaus1948]
* [L. E. Dubins and E. H. Spanier, *How to Cut a Cake Fairly*][DubinsSpanier1961]
* [J. Robertson and W. Webb, *Cake-Cutting Algorithms: Be Fair If You Can*][RobertsonWebb1998]
-/

public section

namespace Cslib.GameTheory.FairDivision

open Cslib (FreeM)

/-! ### Nonatomic cake valuations on `[0, 1]` -/

/-- A nonatomic finite additive normalized valuation over subintervals of `[0, 1]`.

`val a b` is the value assigned to `[a, b]`. Normalization fixes `val 0 1 = 1`, degenerate and
reversed intervals have value `0`, subintervals of `[0, 1]` are nonnegative and finitely additive,
and `x ↦ val 0 x` is continuous on `[0, 1]`. -/
@[ext]
structure CakeValuation where
  /-- Value assigned to the subinterval `[a, b]`. -/
  val : ℝ → ℝ → ℝ
  /-- Total value of `[0, 1]` is `1`. -/
  val_zero_one : val 0 1 = 1
  /-- Degenerate (`a = b`) and reversed (`b < a`) intervals have value `0`. -/
  val_of_ge : ∀ ⦃a b : ℝ⦄, b ≤ a → val a b = 0
  /-- Every subinterval of `[0, 1]` has nonnegative value. -/
  val_nonneg : ∀ ⦃a b : ℝ⦄, 0 ≤ a → b ≤ 1 → 0 ≤ val a b
  /-- Finite additivity across adjacent subintervals of `[0, 1]`. -/
  val_add : ∀ ⦃a b c : ℝ⦄, 0 ≤ a → a ≤ b → b ≤ c → c ≤ 1 → val a b + val b c = val a c
  /-- Continuity of cumulative valuation `x ↦ val 0 x` on `[0, 1]`. -/
  continuousOn : ContinuousOn (val 0) (Set.Icc 0 1)

instance : CoeFun CakeValuation (fun _ => ℝ → ℝ → ℝ) :=
  ⟨CakeValuation.val⟩

namespace CakeValuation

variable (v : CakeValuation)

@[simp]
theorem coe_mk (f : ℝ → ℝ → ℝ) (h01 hge hnn hadd hcont) :
    ((⟨f, h01, hge, hnn, hadd, hcont⟩ : CakeValuation) : ℝ → ℝ → ℝ) = f := rfl

/-- Singletons carry value `0` (nonatomicity). -/
@[simp]
theorem apply_self (a : ℝ) : v a a = 0 :=
  v.val_of_ge le_rfl

/-- Whole-cake normalization `v 0 1 = 1` on coerced applications. -/
@[simp]
theorem apply_zero_one : v 0 1 = 1 :=
  v.val_zero_one

/-- Express any subinterval `[a, b] ⊆ [0, 1]` as the increment `v 0 b - v 0 a`. -/
theorem apply_eq_sub {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    v a b = v 0 b - v 0 a := by
  have h := v.val_add le_rfl ha hab hb
  linarith

/-- Inclusion monotonicity: `[a, b] ⊆ [c, d] ⊆ [0, 1]` implies `v a b ≤ v c d`. -/
theorem apply_mono {a b c d : ℝ} (hc : 0 ≤ c) (hca : c ≤ a) (hbd : b ≤ d) (hd : d ≤ 1) :
    v a b ≤ v c d := by
  by_cases hab : a ≤ b
  · linarith [v.val_add hc hca hab (hbd.trans hd), v.val_add hc (hca.trans hab) hbd hd,
      v.val_nonneg hc (hab.trans (hbd.trans hd)), v.val_nonneg (hc.trans (hca.trans hab)) hd]
  · rw [v.val_of_ge (le_of_not_ge hab)]
    exact v.val_nonneg hc hd

/-- Right-endpoint monotonicity: `x ≤ y ≤ 1` with `0 ≤ a` gives `v a x ≤ v a y`. -/
theorem apply_mono_right {a x y : ℝ} (ha : 0 ≤ a) (hxy : x ≤ y) (hy : y ≤ 1) :
    v a x ≤ v a y :=
  v.apply_mono ha le_rfl hxy hy

/-- Continuity of `x ↦ v a x` on `[a, 1]` for any `0 ≤ a`. -/
theorem continuousOn_right {a : ℝ} (ha0 : 0 ≤ a) :
    ContinuousOn (v a) (Set.Icc a 1) :=
  ((v.continuousOn.mono (t := Set.Icc a 1) fun _ hx => ⟨ha0.trans hx.1, hx.2⟩).sub
    continuousOn_const).congr fun _ hx => v.apply_eq_sub ha0 hx.1 hx.2

/-- **Intermediate-value cut existence:** for `a ∈ [0, 1]` and `0 ≤ α ≤ v a 1`, there exists a cut
point `x ∈ [a, 1]` with `v a x = α`. -/
theorem exists_cut {a α : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hα0 : 0 ≤ α) (hα1 : α ≤ v a 1) :
    ∃ x ∈ Set.Icc a 1, v a x = α :=
  intermediate_value_Icc ha1 (continuousOn_right v ha0) ⟨by rwa [v.apply_self], hα1⟩

/-- Construct a `CakeValuation` from a cumulative distribution function `F : ℝ → ℝ` satisfying
`F 0 = 0`, `F 1 = 1`, monotonicity on `[0, 1]`, and continuity on `[0, 1]`. -/
@[expose] noncomputable def ofCDF (F : ℝ → ℝ) (h0 : F 0 = 0) (h1 : F 1 = 1)
    (hmono : MonotoneOn F (Set.Icc 0 1)) (hcont : ContinuousOn F (Set.Icc 0 1)) :
    CakeValuation where
  val a b := if a ≤ b then F b - F a else 0
  val_zero_one := by
    rw [ite_eq_left (by norm_num : (0 : ℝ) ≤ 1), h1, h0, sub_zero]
  val_of_ge a b hba := by
    by_cases hab : a ≤ b
    · have heq : a = b := le_antisymm hab hba
      subst heq
      simp only [le_refl, ↓reduceIte, sub_self]
    · simp only [hab, ↓reduceIte]
  val_nonneg a b ha hb := by
    by_cases hab : a ≤ b
    · rw [ite_eq_left hab, sub_nonneg]
      exact hmono ⟨ha, hab.trans hb⟩ ⟨ha.trans hab, hb⟩ hab
    · rw [ite_eq_right hab]
  val_add a b c ha hab hbc hc := by
    rw [ite_eq_left hab, ite_eq_left hbc, ite_eq_left (hab.trans hbc)]
    ring
  continuousOn := hcont.congr fun x hx => by
    rw [ite_eq_left hx.1, h0, sub_zero]

@[simp]
theorem ofCDF_apply_of_le (F : ℝ → ℝ) (h0 h1 hmono hcont) {a b : ℝ} (hab : a ≤ b) :
    ofCDF F h0 h1 hmono hcont a b = F b - F a :=
  ite_eq_left hab

/-- The uniform Lebesgue cake valuation on `[0, 1]`, assigning `b - a` to `[a, b]` (`a ≤ b`). -/
@[expose] noncomputable def uniform : CakeValuation :=
  ofCDF (id : ℝ → ℝ) rfl rfl (fun _ _ _ _ h => h) continuousOn_id

@[simp]
theorem uniform_apply_of_le {a b : ℝ} (hab : a ≤ b) :
    uniform a b = b - a :=
  ite_eq_left hab

/-- Convex combination `w · v₁ + (1 - w) · v₂` (`w ∈ [0, 1]`) of two cake valuations. -/
@[expose] noncomputable def convexComb (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (v₁ v₂ : CakeValuation) : CakeValuation where
  val a b := w * v₁ a b + (1 - w) * v₂ a b
  val_zero_one := by
    rw [v₁.apply_zero_one, v₂.apply_zero_one]
    ring
  val_of_ge a b hba := by
    rw [v₁.val_of_ge hba, v₂.val_of_ge hba]
    ring
  val_nonneg a b ha hb := by
    have h1 := v₁.val_nonneg ha hb
    have h2 := v₂.val_nonneg ha hb
    nlinarith
  val_add a b c ha hab hbc hc := by
    rw [← v₁.val_add ha hab hbc hc, ← v₂.val_add ha hab hbc hc]
    ring
  continuousOn :=
    (continuousOn_const.mul v₁.continuousOn).add (continuousOn_const.mul v₂.continuousOn)

@[simp]
theorem convexComb_apply (w : ℝ) (hw0 hw1) (v₁ v₂ : CakeValuation) (a b : ℝ) :
    convexComb w hw0 hw1 v₁ v₂ a b = w * v₁ a b + (1 - w) * v₂ a b := rfl

/-- Affine-density valuation on `[0, 1]` with density `1 + slope · (x - 1/2)` (`slope ∈ [-2, 2]`),
cumulative distribution `F(x) = x + (slope / 2) · x · (x - 1)`. -/
@[expose] noncomputable def affine (slope : ℝ) (hlo : -2 ≤ slope) (hhi : slope ≤ 2) :
    CakeValuation :=
  ofCDF (fun x => x + slope / 2 * x * (x - 1))
    (by ring)
    (by ring)
    (fun a ha b hb hab => by
      have hdiff :
          b + slope / 2 * b * (b - 1) - (a + slope / 2 * a * (a - 1)) =
            (b - a) * (1 + slope / 2 * (a + b - 1)) := by ring
      have hfac : 0 ≤ 1 + slope / 2 * (a + b - 1) := by
        rcases le_or_gt 0 (a + b - 1) with hpos | hneg
        · nlinarith [ha.1, hb.2]
        · nlinarith [ha.1, hb.2]
      have hprod : 0 ≤ (b - a) * (1 + slope / 2 * (a + b - 1)) :=
        mul_nonneg (sub_nonneg.mpr hab) hfac
      linarith)
    (continuousOn_id.add
      ((continuousOn_const.mul continuousOn_id).mul (continuousOn_id.sub continuousOn_const)))

@[simp]
theorem affine_apply_of_le (slope : ℝ) (hlo hhi) {a b : ℝ} (hab : a ≤ b) :
    affine slope hlo hhi a b =
      b + slope / 2 * b * (b - 1) - (a + slope / 2 * a * (a - 1)) :=
  ite_eq_left hab

/-- Piecewise-uniform valuation supported uniformly on `[l, r] ⊆ [0, 1]` (`l < r`), assigning
density `1 / (r - l)` on `[l, r]` and `0` outside `[l, r]`. -/
@[expose] noncomputable def uniformOn (l r : ℝ) (hl : 0 ≤ l) (hlr : l < r) (hr : r ≤ 1) :
    CakeValuation :=
  ofCDF (fun x => (min r (max l x) - l) / (r - l))
    (by rw [max_eq_left hl, min_eq_right hlr.le, sub_self, zero_div])
    (by rw [max_eq_right (hlr.le.trans hr), min_eq_left hr, div_self (sub_ne_zero.mpr hlr.ne')])
    (fun a _ b _ hab => by
      have hmax : max l a ≤ max l b := max_le_max_left l hab
      have hmin : min r (max l a) ≤ min r (max l b) := min_le_min_left r hmax
      exact div_le_div_of_nonneg_right (sub_le_sub_right hmin l) (sub_pos.mpr hlr).le)
    (((continuous_const.min (continuous_const.max continuous_id)).sub
      continuous_const).div_const (r - l)).continuousOn

@[simp]
theorem uniformOn_apply_of_le (l r : ℝ) (hl hlr hr) {a b : ℝ} (hab : a ≤ b) :
    uniformOn l r hl hlr hr a b =
      (min r (max l b) - l) / (r - l) - (min r (max l a) - l) / (r - l) :=
  ite_eq_left hab

end CakeValuation

/-! ### Interval pieces, bundles, and ordered cut partitions -/

/-- A closed subinterval `[left, right]` of the cake `[0, 1]`. -/
@[ext]
structure CakePiece where
  /-- Left endpoint of the piece. -/
  left : ℝ
  /-- Right endpoint of the piece. -/
  right : ℝ
  deriving Inhabited

namespace CakeValuation

variable (v : CakeValuation)

/-- Value assigned by `v` to a single `CakePiece`. -/
@[expose] def pieceVal (p : CakePiece) : ℝ :=
  v p.left p.right

/-- Additive value assigned by `v` to a finite bundle of interval pieces. -/
@[expose] def bundleVal (B : List CakePiece) : ℝ :=
  (B.map v.pieceVal).sum

@[simp]
theorem bundleVal_nil : v.bundleVal [] = 0 := rfl

@[simp]
theorem bundleVal_cons (p : CakePiece) (ps : List CakePiece) :
    v.bundleVal (p :: ps) = v.pieceVal p + v.bundleVal ps := by
  simp only [bundleVal, List.map_cons, List.sum_cons]

theorem bundleVal_singleton (p : CakePiece) :
    v.bundleVal [p] = v p.left p.right := by
  simp only [bundleVal, pieceVal, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero]

@[simp]
theorem bundleVal_append (B₁ B₂ : List CakePiece) :
    v.bundleVal (B₁ ++ B₂) = v.bundleVal B₁ + v.bundleVal B₂ := by
  simp only [bundleVal, List.map_append, List.sum_append]

/-- Permuting the pieces of a bundle preserves its value. -/
theorem bundleVal_perm {B₁ B₂ : List CakePiece} (h : B₁.Perm B₂) :
    v.bundleVal B₁ = v.bundleVal B₂ :=
  (h.map v.pieceVal).sum_eq

/-- Every bundle of pieces contained in `[0, 1]` has nonnegative value. -/
theorem bundleVal_nonneg {B : List CakePiece}
    (hB : ∀ p ∈ B, 0 ≤ p.left ∧ p.right ≤ 1) : 0 ≤ v.bundleVal B :=
  List.sum_nonneg fun _ hx => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    exact v.val_nonneg (hB p hp).1 (hB p hp).2

end CakeValuation

/-- `OrderedCutsOn a b cuts` asserts `a ≤ c₁ ≤ … ≤ cₖ ≤ b` (`a ≤ b` when `cuts = []`). -/
@[expose] def OrderedCutsOn (a b : ℝ) : List ℝ → Prop
  | [] => a ≤ b
  | c :: cs => a ≤ c ∧ OrderedCutsOn c b cs

@[simp]
theorem orderedCutsOn_nil {a b : ℝ} : OrderedCutsOn a b [] ↔ a ≤ b := Iff.rfl

@[simp]
theorem orderedCutsOn_cons {a b c : ℝ} {cs : List ℝ} :
    OrderedCutsOn a b (c :: cs) ↔ a ≤ c ∧ OrderedCutsOn c b cs := Iff.rfl

theorem OrderedCutsOn.le {a b : ℝ} {cuts : List ℝ} (h : OrderedCutsOn a b cuts) : a ≤ b := by
  induction cuts generalizing a with
  | nil => exact h
  | cons c cs ih => exact h.1.trans (ih h.2)

/-- Splitting/joining ordered cut lists across a middle cut `c`. -/
theorem orderedCutsOn_append_cons {a b c : ℝ} (cs₁ cs₂ : List ℝ) :
    OrderedCutsOn a b (cs₁ ++ c :: cs₂) ↔ OrderedCutsOn a c cs₁ ∧ OrderedCutsOn c b cs₂ := by
  induction cs₁ generalizing a with
  | nil => simp only [List.nil_append, orderedCutsOn_cons, orderedCutsOn_nil]
  | cons x xs ih =>
    simp only [List.cons_append, orderedCutsOn_cons, ih, and_assoc]

/-- Elementary adjacent pieces tiling `[a, b]` along interior cut points `cuts`. -/
@[expose] def intervalsOfCutsOn (a b : ℝ) : List ℝ → List CakePiece
  | [] => [⟨a, b⟩]
  | c :: cs => ⟨a, c⟩ :: intervalsOfCutsOn c b cs

/-- Elementary adjacent pieces tiling `[0, 1]` along interior cut points `cuts`. -/
@[expose] def intervalsOfCuts (cuts : List ℝ) : List CakePiece :=
  intervalsOfCutsOn 0 1 cuts

@[simp]
theorem length_intervalsOfCutsOn (a b : ℝ) (cuts : List ℝ) :
    (intervalsOfCutsOn a b cuts).length = cuts.length + 1 := by
  induction cuts generalizing a with
  | nil => rfl
  | cons c cs ih => simp only [intervalsOfCutsOn, List.length_cons, ih]

@[simp]
theorem length_intervalsOfCuts (cuts : List ℝ) :
    (intervalsOfCuts cuts).length = cuts.length + 1 :=
  length_intervalsOfCutsOn 0 1 cuts

/-- Decomposing `intervalsOfCutsOn` across an interior cut point `c`. -/
theorem intervalsOfCutsOn_append_cons (a b c : ℝ) (cs₁ cs₂ : List ℝ) :
    intervalsOfCutsOn a b (cs₁ ++ c :: cs₂) =
      intervalsOfCutsOn a c cs₁ ++ intervalsOfCutsOn c b cs₂ := by
  induction cs₁ generalizing a with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, intervalsOfCutsOn, ih]

/-- Every piece produced by `OrderedCutsOn a b cuts` lies inside `[a, b]` with `left ≤ right`. -/
theorem endpoints_mem_of_mem_intervalsOfCutsOn {a b : ℝ} {cuts : List ℝ}
    (hord : OrderedCutsOn a b cuts) {p : CakePiece} (hp : p ∈ intervalsOfCutsOn a b cuts) :
    a ≤ p.left ∧ p.left ≤ p.right ∧ p.right ≤ b := by
  induction cuts generalizing a with
  | nil =>
    rcases List.mem_singleton.mp hp with rfl
    exact ⟨le_rfl, hord, le_rfl⟩
  | cons c cs ih =>
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact ⟨le_rfl, hord.1, hord.2.le⟩
    · obtain ⟨h1, h2, h3⟩ := ih hord.2 hp'
      exact ⟨hord.1.trans h1, h2, h3⟩

/-- The closed intervals of `intervalsOfCutsOn a b cuts` cover `Set.Icc a b` exactly. -/
theorem iUnion_Icc_intervalsOfCutsOn {a b : ℝ} {cuts : List ℝ} (hord : OrderedCutsOn a b cuts) :
    (⋃ p ∈ intervalsOfCutsOn a b cuts, Set.Icc p.left p.right) = Set.Icc a b := by
  induction cuts generalizing a with
  | nil => simp only [intervalsOfCutsOn, List.mem_singleton, Set.iUnion_iUnion_eq_left]
  | cons c cs ih =>
    simp only [intervalsOfCutsOn, List.mem_cons, Set.iUnion_iUnion_eq_or_left, ih hord.2]
    exact Set.Icc_union_Icc_eq_Icc hord.1 hord.2.le

/-- Distinct pieces in `intervalsOfCutsOn a b cuts` have disjoint open interiors. -/
theorem pairwise_disjoint_Ioo_intervalsOfCutsOn {a b : ℝ} {cuts : List ℝ}
    (hord : OrderedCutsOn a b cuts) :
    (intervalsOfCutsOn a b cuts).Pairwise
      (fun p q => Disjoint (Set.Ioo p.left p.right) (Set.Ioo q.left q.right)) := by
  induction cuts generalizing a with
  | nil => simp only [intervalsOfCutsOn, List.pairwise_singleton]
  | cons c cs ih =>
    simp only [intervalsOfCutsOn, List.pairwise_cons]
    refine ⟨fun q hq => ?_, ih hord.2⟩
    obtain ⟨hcq, _, _⟩ := endpoints_mem_of_mem_intervalsOfCutsOn hord.2 hq
    exact Set.disjoint_iff.mpr fun x ⟨hx1, hx2⟩ => (lt_irrefl x) ((hx1.2.trans_le hcq).trans hx2.1)

/-- **Value conservation on `[a, b]`:** ordered cuts partition the value `v a b` exactly. -/
theorem bundleVal_intervalsOfCutsOn (v : CakeValuation) {a b : ℝ} {cuts : List ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (hord : OrderedCutsOn a b cuts) :
    v.bundleVal (intervalsOfCutsOn a b cuts) = v a b := by
  induction cuts generalizing a with
  | nil => exact v.bundleVal_singleton ⟨a, b⟩
  | cons c cs ih =>
    rw [intervalsOfCutsOn, v.bundleVal_cons, CakeValuation.pieceVal]
    have hcb : c ≤ b := hord.2.le
    rw [ih (ha.trans hord.1) hord.2]
    exact v.val_add ha hord.1 hcb hb

/-- **Value conservation on `[0, 1]`:** ordered cuts sum to `1` under every `CakeValuation`. -/
theorem bundleVal_intervalsOfCuts (v : CakeValuation) {cuts : List ℝ}
    (hord : OrderedCutsOn 0 1 cuts) :
    v.bundleVal (intervalsOfCuts cuts) = 1 := by
  rw [intervalsOfCuts, bundleVal_intervalsOfCutsOn v le_rfl le_rfl hord, v.apply_zero_one]

/-! ### Cake divisions, proportionality, and envy-freeness -/

/-- A discrete division of `[0, 1]` among `n` agents, pairing the ordered interior cut points
`cuts` with each agent's bundle of interval pieces `pieces i`. -/
structure DividedCake (n : ℕ) where
  /-- Ordered interior cut points `0 ≤ c₁ ≤ … ≤ cₖ ≤ 1`. -/
  cuts : List ℝ
  /-- Interval bundle assigned to agent `i : Fin n`. -/
  pieces : Fin n → List CakePiece

namespace DividedCake

/-- Number of physical cuts made on `[0, 1]`. -/
@[expose] def numCuts {n : ℕ} (D : DividedCake n) : ℕ :=
  D.cuts.length

/-- Multiset/list concatenation of all pieces assigned across all `n` agents. -/
@[expose] def allPieces {n : ℕ} (D : DividedCake n) : List CakePiece :=
  (List.ofFn D.pieces).flatten

/-- `D` validly partitions `[0, 1]` along `D.cuts`: the cut points satisfy
`0 ≤ c₁ ≤ … ≤ cₖ ≤ 1`, and the assigned bundles across all agents permute the elementary pieces
`intervalsOfCuts D.cuts`. -/
@[expose] def IsValidPartition {n : ℕ} (D : DividedCake n) : Prop :=
  OrderedCutsOn 0 1 D.cuts ∧ D.allPieces.Perm (intervalsOfCuts D.cuts)

/-- A division is **contiguous** if every agent receives a single interval piece. -/
@[expose] def IsContiguous {n : ℕ} (D : DividedCake n) : Prop :=
  ∀ i : Fin n, (D.pieces i).length = 1

/-- A division is **proportional** for valuation profile `v` if every agent values their own bundle
at least `1 / n`. -/
@[expose] def IsProportional {n : ℕ} (D : DividedCake n) (v : Fin n → CakeValuation) : Prop :=
  ∀ i : Fin n, 1 / (n : ℝ) ≤ (v i).bundleVal (D.pieces i)

/-- A division is **envy-free** for valuation profile `v` if every agent weakly prefers their own
bundle to every other agent's bundle. -/
@[expose] def IsEnvyFree {n : ℕ} (D : DividedCake n) (v : Fin n → CakeValuation) : Prop :=
  ∀ i j : Fin n, (v i).bundleVal (D.pieces j) ≤ (v i).bundleVal (D.pieces i)

private theorem bundleVal_flatten (u : CakeValuation) (L : List (List CakePiece)) :
    u.bundleVal L.flatten = (L.map u.bundleVal).sum := by
  induction L with
  | nil => rfl
  | cons B Bs ih =>
    simp only [List.flatten_cons, CakeValuation.bundleVal_append, List.map_cons, List.sum_cons, ih]

/-- Under any valid partition of `[0, 1]`, any single valuation `u` sums to `1` across all `n`
agents' bundles. -/
theorem sum_bundleVal_eq_one {n : ℕ} {D : DividedCake n} (hP : D.IsValidPartition)
    (u : CakeValuation) :
    ∑ j : Fin n, u.bundleVal (D.pieces j) = 1 := by
  simpa only [allPieces, bundleVal_flatten, List.map_ofFn, Fin.sum_ofFn, Function.comp_def] using
    (u.bundleVal_perm hP.2).trans (bundleVal_intervalsOfCuts u hP.1)

/-- **Envy-freeness implies proportionality** for every valid partition of `[0, 1]`. -/
theorem IsEnvyFree.isProportional {n : ℕ} {D : DividedCake n} {v : Fin n → CakeValuation}
    (hP : D.IsValidPartition) (hEF : D.IsEnvyFree v) : D.IsProportional v := by
  intro i
  have hle : (1 : ℝ) ≤ n * (v i).bundleVal (D.pieces i) := by
    simpa only [sum_bundleVal_eq_one hP (v i), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] using
      Finset.sum_le_sum (s := Finset.univ) fun j _ => hEF i j
  rwa [div_le_iff₀' (Nat.cast_pos.mpr i.pos)]

end DividedCake

/-! ### Robertson–Webb query model -/

/-- Robertson–Webb query signature ([RobertsonWebb1998]) parameterized by agent type `Agent`:
* `eval i a b` requests `v_i([a, b]) : ℝ`;
* `cut i a α` requests a right endpoint `x` from `a` with `v_i([a, x]) = α`. -/
inductive RWQuery (Agent : Type) : Type → Type where
  /-- Evaluate agent `i`'s valuation of `[a, b]`. -/
  | eval (i : Agent) (a b : ℝ) : RWQuery Agent ℝ
  /-- Cut from left endpoint `a` a piece of value `α` for agent `i`. -/
  | cut (i : Agent) (a α : ℝ) : RWQuery Agent ℝ

namespace RWQuery

/-- Lift an `eval` query into `FreeM (RWQuery Agent) ℝ`. -/
abbrev evalAsk {Agent : Type} (i : Agent) (a b : ℝ) : FreeM (RWQuery Agent) ℝ :=
  FreeM.lift (.eval i a b)

/-- Lift a `cut` query into `FreeM (RWQuery Agent) ℝ`. -/
abbrev cutAsk {Agent : Type} (i : Agent) (a α : ℝ) : FreeM (RWQuery Agent) ℝ :=
  FreeM.lift (.cut i a α)

/-- Issue a single `cut` query and clamp the returned cut point into `[a, b]`.

When `a ≤ b`, the returned point always lies in `[a, b]` (even against malformed oracles), and for
every valid Robertson–Webb oracle with `0 ≤ α ≤ v_i(a, b)` it achieves exact value `v_i(a, x) = α`
even when `v_i` has zero-density regions extending past `b`. -/
@[expose] def cutIn {Agent : Type} (i : Agent) (a b α : ℝ) : FreeM (RWQuery Agent) ℝ :=
  (fun x => min b (max a x)) <$> cutAsk i a α

theorem countQueries_evalAsk {Agent : Type}
    (oracle : {ι : Type} → RWQuery Agent ι → ι) (i : Agent) (a b : ℝ) :
    (evalAsk i a b).countQueries oracle = 1 :=
  FreeM.countQueries_lift oracle (.eval i a b)

theorem countQueries_cutAsk {Agent : Type}
    (oracle : {ι : Type} → RWQuery Agent ι → ι) (i : Agent) (a α : ℝ) :
    (cutAsk i a α).countQueries oracle = 1 :=
  FreeM.countQueries_lift oracle (.cut i a α)

@[simp]
theorem countQueries_cutIn {Agent : Type}
    (oracle : {ι : Type} → RWQuery Agent ι → ι) (i : Agent) (a b α : ℝ) :
    (cutIn i a b α).countQueries oracle = 1 := by
  simp only [cutIn, FreeM.countQueries_map, countQueries_cutAsk]

/-- Unconditional endpoint bounds for `cutIn` whenever `a ≤ b`. -/
theorem eval_cutIn_mem_Icc {Agent : Type}
    (oracle : {ι : Type} → RWQuery Agent ι → ι) (i : Agent) {a b : ℝ} (hab : a ≤ b) (α : ℝ) :
    (cutIn i a b α).eval oracle ∈ Set.Icc a b := by
  simp only [cutIn, FreeM.eval_map, FreeM.eval_lift, Set.mem_Icc, le_min_iff]
  exact ⟨⟨hab, le_max_left _ _⟩, min_le_left _ _⟩

/-- Validity predicate for a Robertson–Webb oracle implementing valuation profile `v`:
`eval` returns exact interval values, and any feasible `cut` query (`0 ≤ a ≤ 1`, `0 ≤ α ≤ v_i a 1`)
returns a point in `[a, 1]` of value `α`. -/
@[expose] def IsValidOracle {Agent : Type} (v : Agent → CakeValuation)
    (oracle : {ι : Type} → RWQuery Agent ι → ι) : Prop :=
  (∀ i a b, oracle (.eval i a b) = v i a b) ∧
  (∀ i a α, 0 ≤ a → a ≤ 1 → 0 ≤ α → α ≤ v i a 1 →
    oracle (.cut i a α) ∈ Set.Icc a 1 ∧ v i a (oracle (.cut i a α)) = α)

theorem IsValidOracle.eval_evalAsk {Agent : Type} {v : Agent → CakeValuation}
    {oracle : {ι : Type} → RWQuery Agent ι → ι} (ho : IsValidOracle v oracle)
    (i : Agent) (a b : ℝ) :
    (evalAsk i a b).eval oracle = v i a b :=
  ho.1 i a b

/-- Under a valid Robertson–Webb oracle, `cutIn i a b α` on `[a, b] ⊆ [0, 1]` with
`0 ≤ α ≤ v i a b` returns a point `x ∈ [a, b]` satisfying `v i a x = α`. -/
theorem IsValidOracle.eval_cutIn_spec {Agent : Type} {v : Agent → CakeValuation}
    {oracle : {ι : Type} → RWQuery Agent ι → ι} (ho : IsValidOracle v oracle)
    (i : Agent) {a b α : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (hα0 : 0 ≤ α) (hαb : α ≤ v i a b) :
    (cutIn i a b α).eval oracle ∈ Set.Icc a b ∧
      v i a ((cutIn i a b α).eval oracle) = α := by
  refine ⟨eval_cutIn_mem_Icc oracle i hab α, ?_⟩
  obtain ⟨⟨hax, hx1⟩, hvx⟩ := ho.2 i a α ha (hab.trans hb) hα0
    (hαb.trans ((v i).apply_mono_right ha hb le_rfl))
  simp only [cutIn, FreeM.eval_map, FreeM.eval_lift, max_eq_right hax]
  by_cases hxb : oracle (.cut i a α) ≤ b
  · rw [min_eq_right hxb, hvx]
  · rw [min_eq_left (le_of_not_ge hxb)]
    exact le_antisymm (hvx ▸ (v i).apply_mono_right ha (le_of_not_ge hxb) hx1) hαb

/-- Canonical Robertson–Webb oracle induced by a valuation profile `v` via intermediate value. -/
noncomputable def oracleOf {Agent : Type} (v : Agent → CakeValuation) :
    {ι : Type} → RWQuery Agent ι → ι
  | _, .eval i a b => v i a b
  | _, .cut i a α =>
      if h : 0 ≤ a ∧ a ≤ 1 ∧ 0 ≤ α ∧ α ≤ v i a 1 then
        let ⟨ha0, ha1, hα0, hα1⟩ := h
        Classical.choose ((v i).exists_cut ha0 ha1 hα0 hα1)
      else
        max a (min 1 α)

/-- `oracleOf v` is a valid Robertson–Webb oracle for every valuation profile `v`. -/
theorem isValidOracle_oracleOf {Agent : Type} (v : Agent → CakeValuation) :
    IsValidOracle v (oracleOf v) := by
  refine ⟨fun _ _ _ => rfl, fun i a α ha0 ha1 hα0 hα1 => ?_⟩
  dsimp only [oracleOf]
  rw [dite_eq_left ⟨ha0, ha1, hα0, hα1⟩]
  exact Classical.choose_spec ((v i).exists_cut ha0 ha1 hα0 hα1)

/-- Embed `RWQuery (Fin n)` into `RWQuery ℕ` via `Fin.val`, providing a size-uniform query
signature across all agent counts `n : ℕ` for `Cslib.Query.UpperBound`. -/
@[expose] def liftFin {n : ℕ} {α : Type} :
    FreeM (RWQuery (Fin n)) α → FreeM (RWQuery ℕ) α
  | .pure x => .pure x
  | .liftBind (.eval i a b) cont =>
      .liftBind (.eval i.val a b) (fun y => liftFin (cont y))
  | .liftBind (.cut i a t) cont =>
      .liftBind (.cut i.val a t) (fun y => liftFin (cont y))

/-- Query count of `liftFin p` against an `ℕ`-indexed oracle equals the query count of `p` against
the restricted `Fin n`-indexed oracle. -/
@[simp]
theorem countQueries_liftFin {n : ℕ} {α : Type}
    (oracle : {ι : Type} → RWQuery ℕ ι → ι)
    (p : FreeM (RWQuery (Fin n)) α) :
    (liftFin p).countQueries oracle =
      p.countQueries (fun {ι} q =>
        match q with
        | .eval i a b => oracle (.eval i.val a b)
        | .cut i a t => oracle (.cut i.val a t)) := by
  induction p with
  | pure _ => rfl
  | lift_bind op _ ih => cases op <;> exact congrArg (1 + ·) (ih _)

end RWQuery

end Cslib.GameTheory.FairDivision
