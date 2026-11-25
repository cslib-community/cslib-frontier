/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.LogSpaceDerandomization.HierarchyChildRootMoment
public import CslibFrontier.Computability.LogSpaceDerandomization.HierarchyEstimatedInput
import CslibFrontier.Computability.LogSpaceDerandomization.NormalizedAtomRows.Output

/-!
# Cutoff, Bin-Schedule, and Residual-Stage Contexts

Orthogonal stage records for finite routed-bin residual estimation on `Environment P J`:

* `CutoffProfile` bundles a monotone bin-routing cutoff `χ` and canonical request row gate `ρ`,
  threshold `η`, and rank `K`, independently of the prime `P`, role width `J`, hierarchy
  parameters, and active bin schedule. `CutoffProfile.explicit` instantiates the record with the
  degree-4 polynomial switches of `HierarchyRankEnvironment`.
* `BinSchedule` bundles the active bin horizon `lastBin`, grid exponents `binExponent`, antitone
  and `≤ 16` adjacent-ratio laws, first-bin density cap, and per-bin preparation cutoffs, together
  with reducible dot-projected cutoffs (`.cutoff`, `.bounded`, `.cap`) and proved range bounds
  (`.bounded_grid_range`, `.bounded_mem_Icc`).
* `ReserveOutputChildren` bundles the raw, preparation, and running-maximum child estimate
  families, keeping structural `HierarchyTask.Request HP.k` indices separate from the outer
  statistical precision index.
* `ResidualStage` composes `CutoffProfile` and `BinSchedule` with the single-stage environment
  roles, finite horizon admissibility, copy suffixes, and kernel bounds on `Environment P J`,
  exposing `.source`, `.midpoint`, `.terminal`, `.estimated`, `.canonical`, `.input`, `.residual`,
  `.walkSteps`, `.cost`, `.errorCalls`, and `.costCoefficient` as reducible dot-projections.

## Main definitions

* `Matrix.HierarchyParams.H4RankEnvironment.CutoffProfile`,
  `Matrix.HierarchyParams.H4RankEnvironment.CutoffProfile.explicit`
* `Matrix.HierarchyParams.H4RankEnvironment.BinSchedule`,
  `Matrix.HierarchyParams.H4RankEnvironment.BinSchedule.const`,
  `Matrix.HierarchyParams.H4RankEnvironment.BinSchedule.step`
* `Matrix.HierarchyParams.H4RankEnvironment.ReserveOutputChildren`
* `Matrix.HierarchyParams.H4RankEnvironment.ResidualStage`

## Main results

* `Matrix.HierarchyParams.H4RankEnvironment.rowNormPow_congr_masks`: integrated row-norm
  congruence under logically equivalent source and terminal masks.
* `Matrix.HierarchyParams.H4RankEnvironment.BinSchedule.bounded_grid_range`: bounded routed bin
  cutoffs stay in `Set.Icc 0 (b.cap i)` across all bins and inputs.
* `Matrix.HierarchyParams.H4RankEnvironment.BinSchedule.bounded_mem_Icc`: bounded routed bin
  cutoffs stay uniformly in `Set.Icc 0 (max b.densityCap 16)`.
* `Matrix.HierarchyParams.H4RankEnvironment.ResidualStage.input_noise_le`,
  `Matrix.HierarchyParams.H4RankEnvironment.ResidualStage.input_moment_le`: stage fourth-moment and
  spectral walk-noise bounds from the bundled schedule and horizon laws.
-/

public section
noncomputable section

namespace Matrix.HierarchyParams.H4RankEnvironment

open Finset Cslib Cslib.Probability
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Primitive bin-routing cutoff and canonical request-gate profile shared across finite
residual-stage mean, child-reserve, and envelope theorems. -/
structure CutoffProfile where
  /-- Monotone bin-routing cutoff `χ`. -/
  binCutoff : ℝ → ℝ
  /-- The bin cutoff is monotone. -/
  cutoff_monotone : Monotone binCutoff
  /-- The bin cutoff vanishes at or below `1 / 2`. -/
  cutoff_zero : ∀ v, v ≤ 1 / 2 → binCutoff v = 0
  /-- The bin cutoff equals `1` at or above `1`. -/
  cutoff_one : ∀ v, 1 ≤ v → binCutoff v = 1
  /-- The bin cutoff takes values in `[0, 1]`. -/
  cutoff_range : ∀ v, binCutoff v ∈ Set.Icc 0 1
  /-- Row gate `ρ` used by canonical dense child requests. -/
  requestGate : ℝ → ℝ
  /-- The request gate is nonnegative. -/
  requestGate_nonneg : ∀ v, 0 ≤ requestGate v
  /-- The request gate is bounded above by `1`. -/
  requestGate_le_one : ∀ v, requestGate v ≤ 1
  /-- Positive interval threshold through which the request gate equals `1`. -/
  gateThreshold : ℝ
  /-- The request-gate threshold is positive. -/
  gateThreshold_pos : 0 < gateThreshold
  /-- The request gate equals `1` at or below `gateThreshold`. -/
  gate_one : ∀ v, v ≤ gateThreshold → requestGate v = 1
  /-- Row-gate rank supplied to canonical dense child requests. -/
  requestRank : ℕ
  /-- The request rank satisfies the dense-sampling rank bound `2 * (1 + 32 / gateThreshold)`. -/
  rank_bound : 2 * (1 + 32 / gateThreshold) ≤ requestRank

namespace CutoffProfile

/-- Every value of `c.requestGate` lies in `[0, 1]`. -/
theorem requestGate_mem_Icc (c : CutoffProfile) (v : ℝ) :
    c.requestGate v ∈ Set.Icc 0 1 :=
  ⟨c.requestGate_nonneg v, c.requestGate_le_one v⟩

/-- Concrete degree-4 polynomial cutoff and row-gate profile (`cutoff`, `gate`, threshold `1`,
rank `66`) from `HierarchyRankEnvironment`. -/
@[expose] def explicit : CutoffProfile where
  binCutoff := H4RankEnvironment.cutoff
  cutoff_monotone _ _ hab := monotone_polynomialSwitch4 (by norm_num) hab
  cutoff_zero _ hv := polynomialSwitch4_of_le (by norm_num) hv
  cutoff_one _ hv := polynomialSwitch4_of_ge (by norm_num) hv
  cutoff_range v := ⟨polynomialSwitch4_nonneg _ _ v, polynomialSwitch4_le_one _ _ v⟩
  requestGate := H4RankEnvironment.gate
  requestGate_nonneg := gate_nonneg
  requestGate_le_one := gate_le_one
  gateThreshold := 1
  gateThreshold_pos := by norm_num
  gate_one _ hv := H4RankEnvironment.gate_one hv
  requestRank := 66
  rank_bound := by norm_num

end CutoffProfile

/-- Finite active-bin exponent schedule, first-bin density cap, and per-bin preparation cutoffs
for routed residual estimation on the `q = 16` rate grid. -/
structure BinSchedule where
  /-- Last active bin index; active bins are `Finset.range (lastBin + 1)`. -/
  lastBin : ℕ
  /-- Grid-rate exponent `kb i` of each bin `i`. -/
  binExponent : ℕ → ℕ
  /-- Bin grid rates decrease with the bin index. -/
  rates_antitone : Antitone (fun i => rate (binExponent i))
  /-- Adjacent bin rates change by at most the grid factor `16`. -/
  rate_ratio : ∀ i, rate (binExponent i) / rate (binExponent (i + 1)) ≤ 16
  /-- First-bin kernel density cap. -/
  densityCap : ℝ
  /-- The first-bin density cap is nonnegative. -/
  densityCap_nonneg : 0 ≤ densityCap
  /-- Preparation cutoff `h i` supplied at each bin `i`. -/
  preparationCutoff : ℕ → ℝ → ℝ

namespace BinSchedule

/-- Active bin index set `range (b.lastBin + 1)`. -/
abbrev activeBins (b : BinSchedule) : Finset ℕ :=
  range (b.lastBin + 1)

/-- Real grid rate `rate (b.binExponent i)` at bin `i`. -/
abbrev rates (b : BinSchedule) : ℕ → ℝ :=
  fun i => rate (b.binExponent i)

/-- Separate top-bin (`densityCap`) and fine-bin (`16`) range cap at bin `i`. -/
abbrev cap (b : BinSchedule) : ℕ → ℝ :=
  estimatedBinCap b.densityCap

/-- Uncapped routed bin cutoff at bin `i` for a cutoff profile `c`. -/
abbrev cutoff (b : BinSchedule) (c : CutoffProfile) : ℕ → ℝ → ℝ :=
  fun i => routedBinCutoff c.binCutoff b.rates i (fun _ => 1)

/-- Bounded routed bin cutoff at bin `i` for a cutoff profile `c`. -/
abbrev bounded (b : BinSchedule) (c : CutoffProfile) : ℕ → ℝ → ℝ :=
  fun i => boundedRoutedBinCutoff c.binCutoff b.rates b.densityCap i (fun _ => 1)

/-- Every per-bin cap `b.cap i` is nonnegative. -/
theorem cap_nonneg (b : BinSchedule) (i : ℕ) : 0 ≤ b.cap i := by
  have hcap := b.densityCap_nonneg
  unfold cap estimatedBinCap
  split_ifs <;> positivity

/-- Bounded routed bin cutoffs lie in `Set.Icc 0 (b.cap i)` at every bin `i`. -/
theorem bounded_grid_range (b : BinSchedule) (c : CutoffProfile) (i : ℕ) (d : ℝ) :
    b.bounded c i d ∈ Set.Icc 0 (b.cap i) :=
  boundedRoutedBinCutoff_grid_range c.binCutoff b.binExponent b.densityCap_nonneg
    c.cutoff_monotone c.cutoff_zero c.cutoff_one c.cutoff_range
    b.rates_antitone b.rate_ratio i d

/-- Bounded routed bin cutoffs lie uniformly in `Set.Icc 0 (max b.densityCap 16)`. -/
theorem bounded_mem_Icc (b : BinSchedule) (c : CutoffProfile) (i : ℕ) (v : ℝ) :
    b.bounded c i v ∈ Set.Icc 0 (max b.densityCap 16) :=
  boundedRoutedBinCutoff_mem_Icc b.densityCap_nonneg
    (b.densityCap_nonneg.trans (le_max_left b.densityCap 16)) (le_max_left b.densityCap 16)
    c.cutoff_monotone c.cutoff_zero c.cutoff_one c.cutoff_range
    (fun j => rate_pos (b.binExponent j)) b.rates_antitone
    (fun j => (b.rate_ratio j).trans (le_max_right b.densityCap 16))
    (fun _ => 1) (fun _ => ⟨zero_le_one, le_rfl⟩) i v

/-- Constant-exponent bin schedule with unit preparation cutoffs. -/
@[expose] def const (lastBin exponent : ℕ) {cap : ℝ} (hcap : 0 ≤ cap) : BinSchedule where
  lastBin := lastBin
  binExponent := fun _ => exponent
  rates_antitone _ _ _ := le_rfl
  rate_ratio _ := (div_self (rate_pos exponent).ne').trans_le (by norm_num)
  densityCap := cap
  densityCap_nonneg := hcap
  preparationCutoff := fun _ _ => 1

/-- Unit-step bin schedule `i ↦ i + start`, whose adjacent grid rates have exact ratio `16`. -/
@[expose] def step (lastBin start : ℕ) {cap : ℝ} (hcap : 0 ≤ cap) : BinSchedule where
  lastBin := lastBin
  binExponent := fun i => i + start
  rates_antitone _ _ hij := rate_antitone (Nat.add_le_add_right hij start)
  rate_ratio i := by
    simpa only [Nat.add_right_comm i 1 start] using (adjacent_rate_ratio (i + start)).le
  densityCap := cap
  densityCap_nonneg := hcap
  preparationCutoff := fun _ _ => 1

end BinSchedule

/-- Raw, preparation, and running-maximum child families, indexed by statistical precision, bin,
and structural `HierarchyTask.Request HP.k`. No accuracy assumption is bundled here. -/
structure ReserveOutputChildren (HP : FourthRootHierarchyParams 16 1 16 32 8) (P J : ℕ) where
  /-- Raw child estimates, indexed by precision, bin, and request. -/
  raw : ℕ → ℕ → HierarchyTask.Request HP.k (Fin J) (ZMod P) →
    Environment P J → Matrix (ZMod P) (ZMod P) ℝ
  /-- Preparation child estimates with the same indices. -/
  prep : ℕ → ℕ → HierarchyTask.Request HP.k (Fin J) (ZMod P) →
    Environment P J → Matrix (ZMod P) (ZMod P) ℝ
  /-- Maximum estimates on each requested source row. -/
  maximum : ℕ → ℕ → HierarchyTask.Request HP.k (Fin J) (ZMod P) →
    Environment P J → ZMod P → ℝ

/-- Spectral contraction factor used by finite component-walk allocations on `Environment P J`. -/
abbrev reserveOutputContraction (J : ℕ) : ℝ :=
  1 - 1 / (155648 * (J + 1) * (4 : ℝ) ^ 4)

/-- Finite single-stage geometric, horizon, cutoff, bin-schedule, and kernel hypotheses for
residual estimation on `Environment P J`. -/
structure ResidualStage (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (P J : ℕ) [Fact P.Prime] where
  /-- Nonzero direction used by the retained grids. -/
  direction : ZMod P
  /-- The grid direction is nonzero. -/
  direction_ne_zero : direction ≠ 0
  /-- Admissible finite exponent and identifier horizon. -/
  horizon : Horizon P
  /-- Distinct source, midpoint, and terminal roles. -/
  roles : RoleProfile J
  /-- Hierarchy request level. -/
  level : ℕ
  /-- Source grid-rate exponent. -/
  sourceExponent : ℕ
  /-- Midpoint grid-rate exponent. -/
  midpointExponent : ℕ
  /-- Full terminal-rank exponent. -/
  terminalExponent : ℕ
  /-- The source grid lies in the admitted horizon. -/
  source_in_horizon : sourceExponent ≤ horizon.maxExponent
  /-- The midpoint exponent does not exceed the source exponent. -/
  midpoint_le_source : midpointExponent ≤ sourceExponent
  /-- Source copy-identifier suffix. -/
  sourceSuffix : List (ZMod P)
  /-- Midpoint copy-identifier suffix. -/
  midpointSuffix : List (ZMod P)
  /-- Terminal copy-identifier suffix. -/
  terminalSuffix : List (ZMod P)
  /-- Primitive bin-routing cutoff and canonical request-gate profile. -/
  cutoffs : CutoffProfile
  /-- Active bin-rate schedule, density cap, and per-bin preparation cutoffs. -/
  bins : BinSchedule
  /-- Every active bin lies in the admitted horizon. -/
  bins_in_horizon : ∀ i ∈ bins.activeBins, bins.binExponent i ≤ horizon.maxExponent
  /-- Preparation agrees with `1` wherever the routed bin cutoff is nonzero on active bins. -/
  preparation_one : ∀ i ∈ bins.activeBins, ∀ v,
    bins.cutoff cutoffs i v ≠ 0 → bins.preparationCutoff i v = 1
  /-- Nonnegative substochastic kernel whose canonical residual is estimated. -/
  kernel : Matrix (ZMod P) (ZMod P) ℝ
  /-- The kernel is entrywise nonnegative. -/
  kernel_nonneg : ∀ x y, 0 ≤ kernel x y
  /-- Every kernel row has mass at most `1`. -/
  kernel_row_mass : kernel *ᵥ 1 ≤ 1
  /-- Kernel entries are bounded by the midpoint rate. -/
  kernel_rate : ∀ x y, kernel x y ≤ rate midpointExponent
  /-- The first-bin density cap bounds the kernel. -/
  kernel_cap : ∀ z w, kernel z w ≤ bins.densityCap * rate (bins.binExponent 0)
  /-- The final active bin covers each nonzero kernel entry. -/
  kernel_cover : ∀ z y, kernel z y = 0 ∨ rate (bins.binExponent bins.lastBin) ≤ kernel z y
  /-- Rank supplied to incoming correction children. -/
  correctionRank : ℕ

/-- Congruence of `Cslib.rowNormPow` under logically equivalent source and terminal masks,
independent of their `Decidable` instances. -/
theorem rowNormPow_congr_masks {Ω V : Type*} [Fintype Ω] [Fintype V]
    {p : ℕ} {N u : ℝ} {X₁ X₂ Y₁ Y₂ : Ω → V → Prop}
    [∀ σ x, Decidable (X₁ σ x)] [∀ σ x, Decidable (X₂ σ x)]
    [∀ σ y, Decidable (Y₁ σ y)] [∀ σ y, Decidable (Y₂ σ y)]
    (hX : ∀ σ x, X₁ σ x ↔ X₂ σ x) (hY : ∀ σ y, Y₁ σ y ↔ Y₂ σ y)
    (Z : Ω → V → V → ℝ) :
    rowNormPow p N u X₁ Y₁ Z = rowNormPow p N u X₂ Y₂ Z := by
  unfold rowNormPow
  congr 1
  refine expect_congr rfl fun σ _ => sum_congr (by ext x; simp [hX]) fun x _ =>
    sum_congr (by ext y; simp [hY]) fun _ _ => rfl

/-- Channel retention on `gridChannel role k suffix` agrees logically with
`NormalizedMoments.retainedMask` at `side P k`. -/
theorem gridChannel_retains_iff_retainedMask {P J : ℕ} [Fact P.Prime]
    (D : ZMod P) (role : Fin J) (k : ℕ)
    (suffix : List (ZMod P)) (σ : Environment P J) (v : ZMod P) :
    (gridChannel role k suffix).retains
      (fun r b s τ w => channels D r b s τ (id w)) σ v ↔
      NormalizedMoments.retainedMask role (side P k) D suffix σ v := by
  simp [CorrectionRowTask.Channel.retains, channels, gridChannel, semanticSide_grid,
    NormalizedMoments.retainedMask]

namespace ResidualStage

variable {HP : FourthRootHierarchyParams 16 1 16 32 8} {P J : ℕ} [Fact P.Prime]

/-- Routed bin cutoff at the stage's bin schedule and cutoff profile. -/
abbrev cutoff (s : ResidualStage HP P J) : ℕ → ℝ → ℝ :=
  s.bins.cutoff s.cutoffs

/-- Bounded routed bin cutoff at the stage's bin schedule and cutoff profile. -/
abbrev bounded (s : ResidualStage HP P J) : ℕ → ℝ → ℝ :=
  s.bins.bounded s.cutoffs

/-- Source request channel, including its suffix. -/
abbrev source (s : ResidualStage HP P J) : Channel P J :=
  gridChannel s.roles.source s.sourceExponent s.sourceSuffix

/-- Midpoint request channel, including its suffix. -/
abbrev midpoint (s : ResidualStage HP P J) : Channel P J :=
  gridChannel s.roles.midpoint s.midpointExponent s.midpointSuffix

/-- Full terminal request channel, including its suffix. -/
abbrev terminal (s : ResidualStage HP P J) : Channel P J :=
  gridChannel s.roles.terminal s.terminalExponent s.terminalSuffix

/-- Retained source mask at `side P s.sourceExponent`. -/
abbrev sourceMask (s : ResidualStage HP P J) : Environment P J → ZMod P → Prop :=
  NormalizedMoments.retainedMask s.roles.source (side P s.sourceExponent)
    s.direction s.sourceSuffix

/-- Retained terminal mask at an arbitrary exponent `k`. -/
abbrev terminalMaskAt (s : ResidualStage HP P J) (k : ℕ) : Environment P J → ZMod P → Prop :=
  NormalizedMoments.retainedMask s.roles.terminal (side P k) s.direction s.terminalSuffix

/-- Retained full-terminal mask at `side P s.terminalExponent`. -/
abbrev terminalMask (s : ResidualStage HP P J) : Environment P J → ZMod P → Prop :=
  s.terminalMaskAt s.terminalExponent

/-- Retained channel interpretation on field vertices `ZMod P`. -/
abbrev channelsV (s : ResidualStage HP P J) :
    Fin J → ℝ → List (ZMod P) → Environment P J → ZMod P → Prop :=
  fun role b suffix σ v => channels s.direction role b suffix σ (id v)

/-- Source channel retention agrees logically with `s.sourceMask`. -/
theorem source_retains_iff (s : ResidualStage HP P J) (σ : Environment P J) (x : ZMod P) :
    s.source.retains s.channelsV σ x ↔ s.sourceMask σ x :=
  gridChannel_retains_iff_retainedMask s.direction s.roles.source s.sourceExponent
    s.sourceSuffix σ x

/-- Terminal channel retention agrees logically with `s.terminalMask`. -/
theorem terminal_retains_iff (s : ResidualStage HP P J) (σ : Environment P J) (y : ZMod P) :
    s.terminal.retains s.channelsV σ y ↔ s.terminalMask σ y :=
  gridChannel_retains_iff_retainedMask s.direction s.roles.terminal s.terminalExponent
    s.terminalSuffix σ y

/-- Incoming normalized child estimates from `children` at statistical precision `precision` and
bin `i`. -/
abbrev estimated (s : ResidualStage HP P J) (children : ReserveOutputChildren HP P J) :=
  fun precision i σ r => incomingChildren HP s.direction id s.correctionRank (s.bounded i)
    (children.raw precision i) (children.prep precision i) (children.maximum precision i) r σ

/-- Canonical normalized children for the stage kernel, cutoffs, and request gate. -/
abbrev canonical (s : ResidualStage HP P J) :
    ℕ → Environment P J → HierarchyTask.Request HP.k (Fin J) (ZMod P) →
      Matrix (ZMod P) (ZMod P) ℝ :=
  fun i σ r => canonicalRequestChild HP s.direction id s.kernel
    (s.cutoff i) (s.bins.preparationCutoff i) s.cutoffs.requestGate s.cutoffs.requestRank r σ

/-- Actual signed once-negative residual input assembled from `children`. -/
abbrev input (s : ResidualStage HP P J) (children : ReserveOutputChildren HP P J) :=
  estimatedResidualInput HP s.direction id s.roles s.level s.sourceExponent
    s.midpointExponent s.terminalExponent s.bins.lastBin s.sourceSuffix s.midpointSuffix
    s.terminalSuffix s.bins.binExponent s.correctionRank s.bounded
    children.raw children.prep children.maximum

/-- Genuine canonical residual of `s.kernel` at the midpoint rate. -/
abbrev residual (s : ResidualStage HP P J) : Matrix (ZMod P) (ZMod P) ℝ :=
  HP.toHierarchyParams.residual (canonicalChannel id (rate s.midpointExponent))
    (canonicalChannel id (rate s.midpointExponent)) (rate s.midpointExponent) s.kernel

/-- Lazy component-walk rotation map on the source and terminal-exponent `k` slice. -/
abbrev walkGraphAt (s : ResidualStage HP P J) (k : ℕ) :=
  graph s.roles.source s.roles.terminal s.roles.source_terminal
    (side P s.sourceExponent) (side P k)
    (side_le P s.sourceExponent) (side_le P k)
    (fun x => CopyPadding.identifier s.direction s.sourceSuffix x)
    (fun y => CopyPadding.identifier s.direction s.terminalSuffix y)

/-- Conditional raw walk on `s.sourceMask` and `s.terminalMask` with step schedule `steps`. -/
abbrev walkSteps (s : ResidualStage HP P J) (children : ReserveOutputChildren HP P J)
    (steps : ℕ → ℕ) :=
  fun j => conditionalWalk s.sourceMask s.terminalMask
    (s.walkGraphAt s.terminalExponent) (fun _ _ => steps j) (s.input children j)

/-- Finite input fourth-moment payment, including the vertex width `P`. -/
abbrev payment (s : ResidualStage HP P J) : ℝ :=
  16 * P * (estimatedResidualBound HP P s.midpointExponent s.terminalExponent s.bins.lastBin
    s.bins.binExponent s.bins.cap) ^ 4

/-- Lower-request `(bin, request)` pairs entering the finite residual error cost. -/
abbrev errorCalls (s : ResidualStage HP P J) :
    Finset (ℕ × HierarchyTask.Request HP.k (Fin J) (ZMod P)) :=
  HierarchyTask.residualErrorCalls (k := HP.k) s.bins.activeBins s.level
    s.source s.midpoint s.terminal s.bins.rates

/-- Finite importance and midpoint-density cost coefficient for `s`. -/
abbrev costCoefficient (s : ResidualStage HP P J) : ℝ :=
  HierarchyTask.residualCostCoefficient (k := HP.k) s.channelsV s.bins.activeBins s.level
    s.source s.midpoint s.terminal s.bins.rates
    (2 * HP.Q HP.toHierarchyParams.atomCap) (2 * max s.bins.densityCap 16)

/-- Conditional lower-child error cost at precision `j + 1` (one past prefix index `j`). -/
abbrev cost (s : ResidualStage HP P J) (children : ReserveOutputChildren HP P J) :=
  fun j x y => HierarchyTask.conditionalChildCost s.channelsV s.bins.activeBins s.level
    s.source s.midpoint s.terminal s.bins.rates
    (2 * HP.Q HP.toHierarchyParams.atomCap) (2 * max s.bins.densityCap 16)
    (s.estimated children (j + 1)) s.canonical x y

/-- The canonical residual of `s` is entrywise nonnegative. -/
theorem residual_nonneg (s : ResidualStage HP P J) (x y : ZMod P) : 0 ≤ s.residual x y :=
  HP.toHierarchyParams.residual_nonneg (rate_pos s.midpointExponent) s.kernel_nonneg x y

/-- Fourth moment of the stage's signed residual input at `precision`, paid before walking. -/
theorem input_moment_le (s : ResidualStage HP P J) (children : ReserveOutputChildren HP P J)
    (precision : ℕ) :
    rowNormPow 4 P (rate s.sourceExponent) s.sourceMask s.terminalMask
      (s.input children precision) ≤ s.payment :=
  estimatedResidualInput_moment_le HP
    (_root_.Matrix.FourthRootHierarchyParams.NormalizedRow.rank_pos HP)
    s.direction s.roles s.horizon s.level s.sourceExponent s.midpointExponent s.terminalExponent
    s.bins.lastBin s.source_in_horizon s.sourceSuffix s.midpointSuffix s.terminalSuffix
    s.bins.binExponent s.correctionRank s.bounded s.bins.cap s.bins.cap_nonneg
    (s.bins.bounded_grid_range s.cutoffs) children.raw children.prep children.maximum precision

/-- Centered raw walk noise of `s.walkSteps children steps` at index `j`. -/
theorem input_noise_le (s : ResidualStage HP P J) (children : ReserveOutputChildren HP P J)
    (steps : ℕ → ℕ) (j : ℕ) :
    rowNormPow 4 P (rate s.sourceExponent) s.sourceMask s.terminalMask
      (fun σ x y => s.walkSteps children steps j σ x y -
        rowSliceMean s.sourceMask s.terminalMask (s.input children j) x y) ≤
      32 * reserveOutputContraction J ^ (2 * steps j) * s.payment :=
  estimatedResidualInput_noise_le HP
    (_root_.Matrix.FourthRootHierarchyParams.NormalizedRow.rank_pos HP)
    s.direction s.roles s.horizon s.level s.sourceExponent s.midpointExponent s.terminalExponent
    s.bins.lastBin s.source_in_horizon s.sourceSuffix s.midpointSuffix s.terminalSuffix
    s.bins.binExponent s.correctionRank s.bounded s.bins.cap s.bins.cap_nonneg
    (s.bins.bounded_grid_range s.cutoffs) children.raw children.prep children.maximum j (steps j)

end ResidualStage

end Matrix.HierarchyParams.H4RankEnvironment
