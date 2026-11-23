/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Mechanism.LinearValuation
public import CslibFrontier.GameTheory.Mechanism.VickreyVCG
import CslibFrontier.GameTheory.Mechanism.Knapsack
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith

/-!
# Restricted valuation domains and feasible-set bridges

In [Nisan2007] (§9.3.2–9.3.4, Definitions 9.14, 9.15 and 9.18), a direct-revelation mechanism
operates over restricted valuation domains `V : ι → Set (Ω → ℝ)`: agent `i`'s possible valuations
belong to `V i`, and incentive compatibility (`Mechanism.IsDSICOn`, defined in
`CslibFrontier.GameTheory.Mechanism.VCG`), ex-post individual rationality (`Mechanism.IsIROn`), and
no positive transfers (`Mechanism.NoPositiveTransfersOn`) quantify over reported profiles in the
product domain `∀ j, b j ∈ V j`.

Setting `V i = Set.univ` recovers unrestricted `Mechanism.IsDSIC` (`Mechanism.isDSICOn_univ_iff`)
and global nonnegativity of payments (`Mechanism.noPositiveTransfersOn_univ_iff`). Note that
`Mechanism.IsIR` in `VCG.lean` restricts the evaluated agent's valuation to `0 ≤ b i` while leaving
the other agents' reports unrestricted in `Set.univ`, whereas [Nisan2007]'s Definition 9.18
(`Mechanism.IsIROn`) imposes no sign restriction beyond `b j ∈ V j`—matching procurement/cost
domains (§9.3.5.2) and explaining why Lemma 9.20 explicitly assumes `0 ≤ v` on `V i`
(`Mechanism.vcg_isIROn`); accordingly `Mechanism.IsIR.isIROn` bridges `Mechanism.IsIR` to
`Mechanism.IsIROn` on every domain of nonnegative valuations, while `Mechanism.isIROn_univ_iff`
characterizes `V i = Set.univ`.

Groves mechanisms are DSIC on any restricted domain `V` on which the outcome rule maximizes
reported welfare (`Mechanism.groves_isDSICOn`, Theorem 9.17), and VCG with Clarke pivot payments
satisfies no positive transfers and—when every `V i` consists of nonnegative valuations—individual
rationality (`Mechanism.vcg_noPositiveTransfersOn`, `Mechanism.vcg_isIROn`, Lemma 9.20).

## Completing the single-parameter / general mechanism bridge over feasible sets `X`

`CslibFrontier.GameTheory.Mechanism.LinearValuation` defines `Mechanism.linearValuation`,
`Mechanism.linearDomain`, `Mechanism.toSingleParameter`, and `SingleParameter.Mechanism.toMechanism`
(into `Mechanism ι (ι → ℝ)`), proving `IsDSIC` equivalences. Here we complete that bridge:

* **Individual rationality equivalence**: `(M.toSingleParameter x).IsIR ↔ M.IsIROn (linearDomain x)`
  (`Mechanism.isIR_toSingleParameter_iff`) and `M.IsIR ↔ M.toMechanism.IsIROn (linearDomain id)`
  (`SingleParameter.Mechanism.isIR_iff_isIROn_toMechanism`).
* **Feasible-set subtype embedding (`SingleParameter.Mechanism.toMechanismOn`)**: any
  `M : SingleParameter.Mechanism ι` whose allocations on nonnegative bids belong to a feasible set
  `X : Set (ι → ℝ)` embeds directly into `Mechanism ι X` (with outcome type `X` rather than all of
  `ι → ℝ`). When every bidder has some outcome in `X` with nonzero allocation, `IsDSICOn` and
  `IsIROn` on `Mechanism.linearDomain Subtype.val` are equivalent to `M.IsDSIC` and `M.IsIR`
  (`SingleParameter.Mechanism.isDSIC_iff_isDSICOn_toMechanismOn`,
  `SingleParameter.Mechanism.isIR_iff_isIROn_toMechanismOn`).
* **VCG directly on `Vickrey.singleItemFeasible`** ([Nisan2007], §9.3.5.1): complementing
  `VickreyVCG` (which models outcomes as `Option ι`), `Mechanism.vcg` run directly on the feasible
  subtype `Vickrey.singleItemFeasible` with `Vickrey.vcgOutcome` pulls back via
  `Mechanism.toSingleParameter Subtype.val` to `Vickrey.mechanism` on every nonnegative bid profile
  (`SingleParameter.Vickrey.vcg_singleItemFeasible_allocation`,
  `SingleParameter.Vickrey.vcg_singleItemFeasible_payment`).

## Main definitions

* `Mechanism.IsIROn`: ex-post individual rationality on `V` ([Nisan2007], Definition 9.18).
* `Mechanism.NoPositiveTransfersOn`: nonnegativity of payments on `V` ([Nisan2007],
  Definition 9.18).
* `Mechanism.IsWelfareMaximizingOn`: welfare maximization on profiles in `V`.
* `SingleParameter.extractBid`, `SingleParameter.Mechanism.toMechanismOn`: embedding a
  single-parameter mechanism with feasible set `X : Set (ι → ℝ)` into `Mechanism ι X`.
* `SingleParameter.Vickrey.singleWinner`, `SingleParameter.Vickrey.vcgOutcome`: single-winner
  feasible allocations and welfare-maximizing rule on `Vickrey.singleItemFeasible`.

## Main results

* `Mechanism.IsDSICOn.mono`, `Mechanism.isIROn_univ_iff`, `Mechanism.IsIR.isIROn`,
  `Mechanism.noPositiveTransfersOn_univ_iff`: domain monotonicity and unrestricted equivalences.
* `Mechanism.groves_isDSICOn`, `Mechanism.vcg_isDSICOn`, `Mechanism.vcg_noPositiveTransfersOn`,
  `Mechanism.vcg_isIROn`: restricted-domain Groves and VCG ([Nisan2007], Theorem 9.17 and
  Lemma 9.20).
* `Mechanism.isIR_toSingleParameter_iff`,
  `SingleParameter.Mechanism.isIR_iff_isIROn_toMechanism`: exact `IsIR` / `IsIROn` equivalences
  for `toSingleParameter` and `toMechanism`.
* `SingleParameter.Mechanism.isDSIC_iff_isDSICOn_toMechanismOn`,
  `SingleParameter.Mechanism.isIR_iff_isIROn_toMechanismOn`: exact `IsDSICOn` and `IsIROn`
  equivalences for feasible-set embedding into `Mechanism ι X`.
* `SingleParameter.Vickrey.isWelfareMaximizing_vcgOutcome`,
  `SingleParameter.Vickrey.vcg_singleItemFeasible_allocation`,
  `SingleParameter.Vickrey.vcg_singleItemFeasible_payment`: VCG directly on `singleItemFeasible`
  agrees with `Vickrey.mechanism` ([Nisan2007], §9.3.5.1).

## References

* [N. Nisan, *Introduction to mechanism design (for computer scientists)*][Nisan2007]
* [W. Vickrey, *Counterspeculation, auctions, and competitive sealed tenders*][Vickrey1961]
* [E. H. Clarke, *Multipart pricing of public goods*][Clarke1971]
* [T. Groves, *Incentives in teams*][Groves1973]
-/

public section

namespace Cslib.GameTheory

namespace Mechanism

variable {ι Ω : Type*}

/-- **Ex-post individual rationality on a restricted domain** ([Nisan2007], Definition 9.18): on
every truthful valuation profile in `V`, every agent gets nonnegative utility. -/
@[expose] def IsIROn (M : Mechanism ι Ω) (V : ι → Set (Ω → ℝ)) : Prop :=
  ∀ (i : ι) (b : ι → Ω → ℝ), (∀ j, b j ∈ V j) → 0 ≤ M.utility i (b i) b

/-- **No positive transfers on a restricted domain** ([Nisan2007], Definition 9.18): on every
valuation profile in `V`, no agent receives a negative payment (subsidy) from the mechanism. -/
@[expose] def NoPositiveTransfersOn (M : Mechanism ι Ω) (V : ι → Set (Ω → ℝ)) : Prop :=
  ∀ (i : ι) (b : ι → Ω → ℝ), (∀ j, b j ∈ V j) → 0 ≤ M.payment b i

/-- An outcome rule maximizes reported welfare on every profile in `V`. -/
@[expose] def IsWelfareMaximizingOn [Fintype ι] (f : (ι → Ω → ℝ) → Ω)
    (V : ι → Set (Ω → ℝ)) : Prop :=
  ∀ b, (∀ j, b j ∈ V j) → ∀ ω, welfare b ω ≤ welfare b (f b)

theorem update_mem_domain [DecidableEq ι] {V : ι → Set (Ω → ℝ)} {b : ι → Ω → ℝ}
    (hb : ∀ j, b j ∈ V j) (i : ι) {v : Ω → ℝ} (hv : v ∈ V i) (j : ι) :
    Function.update b i v j ∈ V j := by
  rcases eq_or_ne j i with rfl | hj
  · rw [Function.update_self]
    exact hv
  · rw [Function.update_of_ne hj]
    exact hb j

/-- On the unrestricted domain `Set.univ`, `IsIROn` says every agent gets nonnegative utility on
every profile. -/
@[simp] theorem isIROn_univ_iff (M : Mechanism ι Ω) :
    M.IsIROn (fun _ => Set.univ) ↔ ∀ i b, 0 ≤ M.utility i (b i) b :=
  ⟨fun h i b => h i b fun _ => trivial, fun h i b _ => h i b⟩

/-- On the unrestricted domain `Set.univ`, `NoPositiveTransfersOn` says payments are nonnegative
everywhere. -/
@[simp] theorem noPositiveTransfersOn_univ_iff (M : Mechanism ι Ω) :
    M.NoPositiveTransfersOn (fun _ => Set.univ) ↔ ∀ i b, 0 ≤ M.payment b i :=
  ⟨fun h i b => h i b fun _ => trivial, fun h i b _ => h i b⟩

theorem IsDSICOn.mono [DecidableEq ι] {M : Mechanism ι Ω} {V W : ι → Set (Ω → ℝ)}
    (hM : M.IsDSICOn W) (hVW : ∀ i, V i ⊆ W i) : M.IsDSICOn V :=
  fun i b v hb hv => hM i b v (fun j => hVW j (hb j)) (hVW i hv)

theorem IsIROn.mono {M : Mechanism ι Ω} {V W : ι → Set (Ω → ℝ)}
    (hM : M.IsIROn W) (hVW : ∀ i, V i ⊆ W i) : M.IsIROn V :=
  fun i b hb => hM i b fun j => hVW j (hb j)

theorem NoPositiveTransfersOn.mono {M : Mechanism ι Ω} {V W : ι → Set (Ω → ℝ)}
    (hM : M.NoPositiveTransfersOn W) (hVW : ∀ i, V i ⊆ W i) : M.NoPositiveTransfersOn V :=
  fun i b hb => hM i b fun j => hVW j (hb j)

/-- `Mechanism.IsIR` implies `Mechanism.IsIROn` on any domain of nonnegative valuations, in
particular on `fun _ => {v | 0 ≤ v}`. -/
theorem IsIR.isIROn {M : Mechanism ι Ω} (hM : M.IsIR) {V : ι → Set (Ω → ℝ)}
    (hV : ∀ i, ∀ v ∈ V i, 0 ≤ v) : M.IsIROn V :=
  fun i b hb => hM i b (hV i (b i) (hb i))

theorem IsWelfareMaximizing.isWelfareMaximizingOn [Fintype ι] {f : (ι → Ω → ℝ) → Ω}
    (hf : IsWelfareMaximizing f) (V : ι → Set (Ω → ℝ)) : IsWelfareMaximizingOn f V :=
  fun b _ ω => hf b ω

/-- **Single-parameter IR is IR on linear valuations**: `(M.toSingleParameter x).IsIR` holds
if and only if `M` is individually rational on `linearDomain x`. -/
theorem isIR_toSingleParameter_iff {M : Mechanism ι Ω} {x : Ω → ι → ℝ} :
    (M.toSingleParameter x).IsIR ↔ M.IsIROn (linearDomain x) := by
  constructor
  · intro h i B hB
    simp only [linearDomain, Set.mem_image, Set.mem_Ici] at hB
    choose c hc hcB using hB
    obtain rfl : linearProfile x c = B := funext hcB
    exact h i c hc
  · intro h i b hb
    exact h i (linearProfile x b) fun j => linearValuation_mem_linearDomain x j (hb j)

section Groves

variable [Fintype ι] [DecidableEq ι]

/-- **Groves mechanisms are DSIC on restricted domains** ([Nisan2007], Theorem 9.17; [Groves1973]):
if `f` maximizes reported welfare on `V` and each pivot `h i` is independent of `i`'s report on `V`,
then `groves f h` is incentive compatible on `V`. -/
theorem groves_isDSICOn {f : (ι → Ω → ℝ) → Ω} {V : ι → Set (Ω → ℝ)}
    (hf : IsWelfareMaximizingOn f V) {h : ι → (ι → Ω → ℝ) → ℝ}
    (hh : ∀ i b v, (∀ j, b j ∈ V j) → v ∈ V i → h i (Function.update b i v) = h i b) :
    (groves f h).IsDSICOn V := by
  intro i b v hb hv
  have hsum : ∀ (c : ι → Ω → ℝ) (ω : Ω),
      ∑ j ∈ Finset.univ.erase i, Function.update c i v j ω =
        ∑ j ∈ Finset.univ.erase i, c j ω := fun c ω =>
    Finset.sum_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  simp only [utility, groves, hh i b v hb hv, hsum]
  have key := hf (Function.update b i v) (update_mem_domain hb i hv) (f b)
  have hw1 := (Finset.add_sum_erase Finset.univ (fun j => Function.update b i v j (f b))
    (Finset.mem_univ i)).symm
  have hw2 := (Finset.add_sum_erase Finset.univ
    (fun j => Function.update b i v j (f (Function.update b i v))) (Finset.mem_univ i)).symm
  simp only [welfare] at key
  rw [hw1, hw2, Function.update_self, hsum, hsum] at key
  linarith

variable [Fintype Ω] [Nonempty Ω]

/-- **VCG is DSIC on restricted domains** ([Nisan2007], Theorem 9.17): if `f` maximizes welfare on
`V`, then `vcg f` is incentive compatible on `V`. -/
theorem vcg_isDSICOn {f : (ι → Ω → ℝ) → Ω} {V : ι → Set (Ω → ℝ)}
    (hf : IsWelfareMaximizingOn f V) : (vcg f).IsDSICOn V :=
  groves_isDSICOn hf fun i b v _ _ => clarkePivot_update i b v

/-- **VCG makes no positive transfers** ([Nisan2007], Lemma 9.20, first statement). -/
theorem vcg_noPositiveTransfersOn (f : (ι → Ω → ℝ) → Ω) (V : ι → Set (Ω → ℝ)) :
    (vcg f).NoPositiveTransfersOn V :=
  fun i b _ => vcg_payment_nonneg f b i

/-- **VCG is individually rational on nonnegative domains** ([Nisan2007], Lemma 9.20, second
statement): if `f` maximizes welfare on `V` and every valuation in `V i` is nonnegative, then
`vcg f` is individually rational on `V`. -/
theorem vcg_isIROn {f : (ι → Ω → ℝ) → Ω} {V : ι → Set (Ω → ℝ)}
    (hf : IsWelfareMaximizingOn f V) (hV : ∀ i, ∀ v ∈ V i, 0 ≤ v) : (vcg f).IsIROn V := by
  intro i b hb
  obtain ⟨ω, -, hω⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Ω))
    fun ω => ∑ j ∈ Finset.univ.erase i, b j ω
  have key := hf b hb ω
  have hw1 := (Finset.add_sum_erase Finset.univ (fun j => b j ω) (Finset.mem_univ i)).symm
  have hw2 := (Finset.add_sum_erase Finset.univ (fun j => b j (f b)) (Finset.mem_univ i)).symm
  simp only [welfare] at key
  rw [hw1, hw2] at key
  have hbi : 0 ≤ b i ω := hV i (b i) (hb i) ω
  simp only [utility, vcg, groves, clarkePivot, hω]
  linarith

end Groves

end Mechanism

/-! ### Feasible-set embedding `SingleParameter.Mechanism → Mechanism ι X` -/

namespace SingleParameter

variable {ι : Type*}

theorem linearValuation_subtype_injective {X : Set (ι → ℝ)} {i : ι}
    (hX : ∃ ω ∈ X, ω i ≠ 0) :
    Function.Injective (GameTheory.Mechanism.linearValuation (Subtype.val : X → ι → ℝ) i) := by
  obtain ⟨ω, hω, hne⟩ := hX
  intro v₁ v₂ h
  exact mul_right_cancel₀ hne (congrFun h ⟨ω, hω⟩)

open Classical in
/-- Extract a nonnegative scalar bid from a valuation `u : X → ℝ` on a feasible set
`X : Set (ι → ℝ)`, returning `0` off `Mechanism.linearDomain Subtype.val i`. -/
noncomputable def extractBid (X : Set (ι → ℝ)) (i : ι) (u : X → ℝ) : ℝ :=
  if h : ∃ v, 0 ≤ v ∧ GameTheory.Mechanism.linearValuation Subtype.val i v = u then
    Classical.choose h
  else 0

theorem extractBid_nonneg (X : Set (ι → ℝ)) (i : ι) (u : X → ℝ) :
    0 ≤ extractBid X i u := by
  unfold extractBid
  split_ifs with h
  · exact (Classical.choose_spec h).1
  · exact le_rfl

theorem extractBid_linearValuation {X : Set (ι → ℝ)} {i : ι} (hX : ∃ ω ∈ X, ω i ≠ 0)
    {v : ℝ} (hv : 0 ≤ v) :
    extractBid X i (GameTheory.Mechanism.linearValuation (Subtype.val : X → ι → ℝ) i v) = v := by
  have hex : ∃ w, 0 ≤ w ∧
      GameTheory.Mechanism.linearValuation (Subtype.val : X → ι → ℝ) i w =
        GameTheory.Mechanism.linearValuation (Subtype.val : X → ι → ℝ) i v := ⟨v, hv, rfl⟩
  unfold extractBid
  rw [dite_eq_left hex]
  exact linearValuation_subtype_injective hX (Classical.choose_spec hex).2

namespace Mechanism

/-- A single-parameter mechanism is individually rational iff its `toMechanism` embedding on
`ι → ℝ` is individually rational on `Mechanism.linearDomain id`. -/
theorem isIR_iff_isIROn_toMechanism [DecidableEq ι] {M : Mechanism ι} :
    M.IsIR ↔ M.toMechanism.IsIROn (GameTheory.Mechanism.linearDomain id) := by
  conv_lhs => rw [← toSingleParameter_toMechanism M]
  exact GameTheory.Mechanism.isIR_toSingleParameter_iff

/-- Embed a single-parameter mechanism `M` whose allocations on nonnegative bids belong to a
feasible set `X : Set (ι → ℝ)` directly into `Cslib.GameTheory.Mechanism ι X`. -/
@[expose] noncomputable def toMechanismOn {X : Set (ι → ℝ)} (M : Mechanism ι)
    (hx : ∀ b, 0 ≤ b → M.allocation b ∈ X) : GameTheory.Mechanism ι X where
  outcome u := ⟨M.allocation (fun j => extractBid X j (u j)),
    hx _ fun j => extractBid_nonneg X j (u j)⟩
  payment u i := M.payment (fun j => extractBid X j (u j)) i

theorem toMechanismOn_toSingleParameter_eq {X : Set (ι → ℝ)} (M : Mechanism ι)
    (hx : ∀ b, 0 ≤ b → M.allocation b ∈ X) (hX : ∀ i, ∃ ω ∈ X, ω i ≠ 0)
    {b : ι → ℝ} (hb : 0 ≤ b) :
    ((M.toMechanismOn hx).toSingleParameter Subtype.val).allocation b = M.allocation b ∧
      ((M.toMechanismOn hx).toSingleParameter Subtype.val).payment b = M.payment b := by
  have hext : (fun j => extractBid X j
      (GameTheory.Mechanism.linearProfile Subtype.val b j)) = b :=
    funext fun j => extractBid_linearValuation (hX j) (hb j)
  exact ⟨by simp only [GameTheory.Mechanism.toSingleParameter, toMechanismOn, hext],
    by simp only [GameTheory.Mechanism.toSingleParameter, toMechanismOn, hext]⟩

/-- **Feasible-set DSIC equivalence**: when every bidder can receive a nonzero allocation in `X`,
`M` is DSIC if and only if `M.toMechanismOn hx` is DSIC on
`Mechanism.linearDomain Subtype.val`. -/
theorem isDSIC_iff_isDSICOn_toMechanismOn [DecidableEq ι] {X : Set (ι → ℝ)} {M : Mechanism ι}
    (hx : ∀ b, 0 ≤ b → M.allocation b ∈ X) (hX : ∀ i, ∃ ω ∈ X, ω i ≠ 0) :
    M.IsDSIC ↔ (M.toMechanismOn hx).IsDSICOn (GameTheory.Mechanism.linearDomain Subtype.val) := by
  rw [← GameTheory.Mechanism.isDSIC_toSingleParameter_iff]
  exact ⟨fun h => h.congr fun b hb =>
      ⟨(toMechanismOn_toSingleParameter_eq M hx hX hb).1.symm,
        (toMechanismOn_toSingleParameter_eq M hx hX hb).2.symm⟩,
    fun h => h.congr fun b hb => toMechanismOn_toSingleParameter_eq M hx hX hb⟩

/-- **Feasible-set IR equivalence**: when every bidder can receive a nonzero allocation in `X`,
`M` is individually rational if and only if `M.toMechanismOn hx` is individually rational on
`Mechanism.linearDomain Subtype.val`. -/
theorem isIR_iff_isIROn_toMechanismOn {X : Set (ι → ℝ)} {M : Mechanism ι}
    (hx : ∀ b, 0 ≤ b → M.allocation b ∈ X) (hX : ∀ i, ∃ ω ∈ X, ω i ≠ 0) :
    M.IsIR ↔ (M.toMechanismOn hx).IsIROn (GameTheory.Mechanism.linearDomain Subtype.val) := by
  rw [← GameTheory.Mechanism.isIR_toSingleParameter_iff]
  exact ⟨fun h => h.congr fun b hb =>
      ⟨(toMechanismOn_toSingleParameter_eq M hx hX hb).1.symm,
        (toMechanismOn_toSingleParameter_eq M hx hX hb).2.symm⟩,
    fun h => h.congr fun b hb => toMechanismOn_toSingleParameter_eq M hx hX hb⟩

end Mechanism

end SingleParameter

/-! ### VCG directly on `Vickrey.singleItemFeasible` recovers `Vickrey.mechanism` -/

namespace SingleParameter.Vickrey

section FeasibleSet

variable {ι : Type*} [Fintype ι]

theorem singleItemFeasible_finite : (singleItemFeasible (ι := ι)).Finite := by
  have heq : singleItemFeasible (ι := ι) = knapsackFeasible (fun _ => 1) 1 := by
    ext y
    simp only [singleItemFeasible, knapsackFeasible, one_mul]
  rw [heq]
  exact knapsackFeasible_finite _ 1

theorem zero_mem_singleItemFeasible :
    (0 : ι → ℝ) ∈ singleItemFeasible (ι := ι) :=
  ⟨fun _ => Or.inl rfl, by simp only [Pi.zero_apply, Finset.sum_const_zero, zero_le_one]⟩

end FeasibleSet

section VCGSpecialization

variable {ι : Type*} [LinearOrder ι] [Fintype ι]

noncomputable instance instFintypeSingleItemFeasible : Fintype (singleItemFeasible (ι := ι)) :=
  singleItemFeasible_finite.fintype

instance instNonemptySingleItemFeasible : Nonempty (singleItemFeasible (ι := ι)) :=
  ⟨⟨0, zero_mem_singleItemFeasible⟩⟩

/-- The feasible single-item allocation in which bidder `i` alone gets the item. -/
@[expose] def singleWinner (i : ι) : singleItemFeasible (ι := ι) :=
  ⟨singleItem (some i), singleItem_mem_singleItemFeasible (some i)⟩

@[simp] theorem singleWinner_apply_self (i : ι) : (singleWinner i : ι → ℝ) i = 1 := by
  simp [singleWinner]

theorem singleWinner_apply_of_ne {i j : ι} (hj : j ≠ i) : (singleWinner i : ι → ℝ) j = 0 := by
  simp [singleWinner, hj.symm]

open Classical in
/-- A globally welfare-maximizing outcome rule directly on `singleItemFeasible` that breaks ties in
favour of `Vickrey.allocation` whenever the Vickrey outcome maximizes reported welfare (in
particular on every nonnegative linear valuation profile). -/
noncomputable def vcgOutcome (u : ι → singleItemFeasible (ι := ι) → ℝ) :
    singleItemFeasible (ι := ι) :=
  if ∀ ω, GameTheory.Mechanism.welfare u ω ≤ GameTheory.Mechanism.welfare u
      ⟨allocation (fun i => u i (singleWinner i)), allocation_mem_singleItemFeasible _⟩ then
    ⟨allocation (fun i => u i (singleWinner i)), allocation_mem_singleItemFeasible _⟩
  else Classical.choose
    (Finset.exists_max_image Finset.univ (GameTheory.Mechanism.welfare u) Finset.univ_nonempty)

/-- `vcgOutcome` maximizes reported welfare on every valuation profile. -/
theorem isWelfareMaximizing_vcgOutcome :
    GameTheory.Mechanism.IsWelfareMaximizing (vcgOutcome (ι := ι)) := by
  intro u ω
  classical
  unfold vcgOutcome
  split_ifs with h
  · exact h ω
  · exact (Classical.choose_spec
      (Finset.exists_max_image Finset.univ (GameTheory.Mechanism.welfare u)
        Finset.univ_nonempty)).2 ω (Finset.mem_univ ω)

/-- On any nonnegative linear valuation profile on `singleItemFeasible`, `vcgOutcome` chooses
`Vickrey.allocation b`. -/
theorem vcgOutcome_linearProfile {b : ι → ℝ} (hb : 0 ≤ b) :
    vcgOutcome (GameTheory.Mechanism.linearProfile Subtype.val b) =
      ⟨allocation b, allocation_mem_singleItemFeasible b⟩ := by
  classical
  have hbid : (fun i =>
      GameTheory.Mechanism.linearProfile Subtype.val b i (singleWinner i)) = b := by
    funext i
    simp only [GameTheory.Mechanism.linearProfile_apply,
      GameTheory.Mechanism.linearValuation_apply, singleWinner_apply_self, mul_one]
  have hmax : ∀ ω : singleItemFeasible (ι := ι),
      GameTheory.Mechanism.welfare (GameTheory.Mechanism.linearProfile Subtype.val b) ω ≤
        GameTheory.Mechanism.welfare (GameTheory.Mechanism.linearProfile Subtype.val b)
          ⟨allocation b, allocation_mem_singleItemFeasible b⟩ :=
    fun ω => (isWelfareMaximizing_allocation b hb).2 ω.1 ω.2
  unfold vcgOutcome
  simp only [hbid]
  exact ite_eq_left hmax

/-- On any linear valuation profile over `singleItemFeasible`, the Clarke pivot of agent `i`
equals `highestOtherBid b i`. -/
theorem clarkePivot_singleItemFeasible (b : ι → ℝ) (i : ι) :
    GameTheory.Mechanism.clarkePivot i
      (GameTheory.Mechanism.linearProfile (Subtype.val : singleItemFeasible (ι := ι) → ι → ℝ) b) =
        highestOtherBid b i := by
  refine le_antisymm (Finset.sup'_le _ _ fun ω _ => ?_)
    (highestOtherBid_le_iff.2 ⟨?_, fun j hj => ?_⟩)
  · have hω0 : ∀ j, 0 ≤ (ω : ι → ℝ) j := fun j => by
      rcases ω.2.1 j with h | h <;> rw [h]
      exact zero_le_one
    have hsum_le : ∑ j ∈ Finset.univ.erase i, (ω : ι → ℝ) j ≤ 1 :=
      (Finset.sum_le_univ_sum_of_nonneg hω0).trans ω.2.2
    calc ∑ j ∈ Finset.univ.erase i,
          GameTheory.Mechanism.linearProfile Subtype.val b j ω
        = ∑ j ∈ Finset.univ.erase i, b j * (ω : ι → ℝ) j := rfl
      _ ≤ ∑ j ∈ Finset.univ.erase i, highestOtherBid b i * (ω : ι → ℝ) j :=
          Finset.sum_le_sum fun j hj =>
            mul_le_mul_of_nonneg_right (le_highestOtherBid (Finset.ne_of_mem_erase hj)) (hω0 j)
      _ = highestOtherBid b i * ∑ j ∈ Finset.univ.erase i, (ω : ι → ℝ) j := by
          rw [← Finset.mul_sum]
      _ ≤ highestOtherBid b i * 1 :=
          mul_le_mul_of_nonneg_left hsum_le (highestOtherBid_nonneg b i)
      _ = highestOtherBid b i := mul_one _
  · refine Finset.le_sup'_of_le _
      (Finset.mem_univ (⟨0, zero_mem_singleItemFeasible⟩ : singleItemFeasible (ι := ι))) ?_
    simp only [GameTheory.Mechanism.linearProfile_apply,
      GameTheory.Mechanism.linearValuation_apply, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
      le_rfl]
  · refine Finset.le_sup'_of_le _ (Finset.mem_univ (singleWinner j)) ?_
    have hj_sum : ∑ k ∈ Finset.univ.erase i,
        GameTheory.Mechanism.linearProfile Subtype.val b k (singleWinner j) = b j := by
      rw [Finset.sum_eq_single j]
      · simp only [GameTheory.Mechanism.linearProfile_apply,
          GameTheory.Mechanism.linearValuation_apply, singleWinner_apply_self, mul_one]
      · intro k _ hkj
        simp only [GameTheory.Mechanism.linearProfile_apply,
          GameTheory.Mechanism.linearValuation_apply, singleWinner_apply_of_ne hkj, mul_zero]
      · intro hmem
        exact absurd (Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩) hmem
    exact hj_sum.ge

/-- **VCG on `singleItemFeasible` agrees with `Vickrey.mechanism` (allocation)** ([Nisan2007],
§9.3.5.1). -/
theorem vcg_singleItemFeasible_allocation {b : ι → ℝ} (hb : 0 ≤ b) :
    ((GameTheory.Mechanism.vcg (vcgOutcome (ι := ι))).toSingleParameter Subtype.val).allocation b =
      mechanism.allocation b := by
  simp only [GameTheory.Mechanism.toSingleParameter, GameTheory.Mechanism.vcg,
    GameTheory.Mechanism.groves, vcgOutcome_linearProfile hb, mechanism]

/-- **VCG on `singleItemFeasible` agrees with `Vickrey.mechanism` (payment)** ([Nisan2007],
§9.3.5.1). -/
theorem vcg_singleItemFeasible_payment {b : ι → ℝ} (hb : 0 ≤ b) :
    ((GameTheory.Mechanism.vcg (vcgOutcome (ι := ι))).toSingleParameter Subtype.val).payment b =
      mechanism.payment b := by
  funext i
  have := Nonempty.intro i
  simp only [GameTheory.Mechanism.toSingleParameter, GameTheory.Mechanism.vcg,
    GameTheory.Mechanism.groves, clarkePivot_singleItemFeasible b i, vcgOutcome_linearProfile hb,
    mechanism]
  by_cases hw : Wins b i
  · have hsum0 : ∑ j ∈ Finset.univ.erase i,
        GameTheory.Mechanism.linearProfile Subtype.val b j
          ⟨allocation b, allocation_mem_singleItemFeasible b⟩ = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      have hne : j ≠ i := Finset.ne_of_mem_erase hj
      have ha0 : allocation b j = 0 :=
        allocation_eq_zero_iff.2 fun hwj => hne (hwj.unique hw)
      simp only [GameTheory.Mechanism.linearProfile_apply,
        GameTheory.Mechanism.linearValuation_apply, ha0, mul_zero]
    rw [hsum0, sub_zero, allocation_eq_one_iff.2 hw, mul_one]
  · obtain ⟨k, hk⟩ := exists_wins b
    have hki : k ≠ i := fun h => hw (h ▸ hk)
    have hsumk : ∑ j ∈ Finset.univ.erase i,
        GameTheory.Mechanism.linearProfile Subtype.val b j
          ⟨allocation b, allocation_mem_singleItemFeasible b⟩ = b k := by
      rw [Finset.sum_eq_single k]
      · simp only [GameTheory.Mechanism.linearProfile_apply,
          GameTheory.Mechanism.linearValuation_apply, allocation_eq_one_iff.2 hk, mul_one]
      · intro j _ hjk
        have ha0 : allocation b j = 0 :=
          allocation_eq_zero_iff.2 fun hwj => hjk (hwj.unique hk)
        simp only [GameTheory.Mechanism.linearProfile_apply,
          GameTheory.Mechanism.linearValuation_apply, ha0, mul_zero]
      · intro hmem
        exact absurd (Finset.mem_erase.2 ⟨hki, Finset.mem_univ k⟩) hmem
    have hhob : highestOtherBid b i = b k := by
      refine le_antisymm ?_ (le_highestOtherBid hki)
      refine highestOtherBid_le_iff.2 ⟨hb k, fun j _ => ?_⟩
      rcases eq_or_ne j k with rfl | hjk
      · exact le_rfl
      · exact (hk j hjk).1
    rw [hsumk, hhob, sub_self, allocation_eq_zero_iff.2 hw, mul_zero]

end VCGSpecialization

end SingleParameter.Vickrey

end Cslib.GameTheory
