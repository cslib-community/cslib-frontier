/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.FeistelPerm
public import CslibFrontier.DataStructure.Dictionary.Minimap
public import CslibFrontier.Foundations.Data.Nat.IterLog
public import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import CslibFrontier.Foundations.Data.Nat.Log
import CslibFrontier.Foundations.Data.Nat.Power
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
public import CslibFrontier.Tactic.WramOmega.Init
import CslibFrontier.Tactic.WramOmega

/-!
# Multi-Level Tree Parameter Schedule and Subconstant-Redundancy Bit Budget

This module formalizes the integer-exact multi-level hashing parameter schedule and pure bit-budget
conservation bound for the large-parameter-regime dynamic succinct dictionary of Tianxiao Li,
Jingxun Liang, Huacheng Yu, and Renfei Zhou, *Dynamic Dictionary with Subconstant Wasted Bits per
Key* ([LiLiangYuZhou2024, Section 5, Sections 5.1–5.2 and 5.4–5.6];
[arXiv:2310.20536v1](https://arxiv.org/abs/2310.20536v1), PDF pp. 25–36 / printed pp. 24–35).

## Source statements, notation mapping, and formalization adaptations

In [LiLiangYuZhou2024] (`arXiv:2310.20536v1`):
* **Regime and sentinel padding (Section 5 opening, PDF pp. 25–26 / printed pp. 24–25; Section 1,
  Theorem 1.1, PDF p. 2 / printed p. 1)**:
  For capacity `n` (`N` in the paper), polynomial universe `n ^ (1 + α_min) ≤ U ≤ n ^ (1 + α_max)`
  (encoded integer-exactly via `n ^ (q_min + p_min) ≤ U ^ q_min` and
  `U ^ q_max ≤ n ^ (q_max + p_max)`), value bound `1 ≤ V`, and redundancy
  `n / (log₂ n) ^ 0.1 ≤ R ≤ n` (`n ^ 10 ≤ R ^ 10 * Nat.log 2 n` and `R ≤ n`), the internal tree
  operates over `U_base = U + n` (adjoining `n` sentinel keys so active key count stays in
  `{n - 1, n}`) rounded up to a multiple `paddedUniv` of `B_0 * 2 ^ I_1` (Section 5.1, PDF p. 27 /
  printed p. 26).
* **Clamping `R` (`effRedundancy`, Section 5 opening, PDF p. 26 / printed p. 25, formalization
  adaptation)**:
  The paper caps `R` at `N / 2 ^ (log* N)` since update time `O(log* N + log(N / R))` already
  reaches `O(log* N)` there. Here `effRedundancy n R := min R (max 1 (n / max 256 (2 ^ logStar n)))`
  clamps `R` so `redundancyRatio n R = n / effRedundancy n R` satisfies both `256 ≤ r` and
  `2 ^ logStar n ≤ r` across **all** `R ≤ n` (including `R = n`) without inflating `thresholdN`,
  while preserving `effRedundancy n R ≤ R` and `log₂ r = O(logStar n + log(n / R))`.
* **Tree depth, branching factors, and ID-quotient schedule (Section 5 `Tree Parameters` &
  Section 5.1, PDF p. 27 / printed p. 26)**:
  - `treeDepth U r` (`k ≥ 2` in the paper) is the least `ℓ ≥ 2` with `Nat.iterLog ℓ U ≤ 4 * r`
    (adapting the paper's `iterLog k U ≤ r < iterLog (k - 1) U` by a factor of `4` so the bottom
    branching factor `B_{k - 1}` is always at least `2 ^ 17` rather than `1` when
    `iterLog (k - 1) U` lies just above `r`, while keeping `I_{k - 1} = O(r)` and leaf
    waiting-list bits `O(n / r ^ 2)`).
  - Power-of-two node counts `numNodes ℓ = 2 ^ cumBranchBits ℓ` (`B_ℓ = 2 ^ branchBits ℓ`) place
    `nFloor ℓ = n / numNodes ℓ ∈ [targetSize ℓ, 2 * targetSize ℓ)` where
    `targetSize ℓ = (Nat.iterLog ℓ U) ^ 9` (`1 ≤ ℓ < k`) and `targetSize k = r ^ 9`.
  - Window radius `delta ℓ = ⌊(nFloor ℓ) ^ (2 / 3)⌋` (`Nat.nthRoot 3 ((nFloor ℓ) ^ 2)`), thresholds
    `nLow ℓ = nFloor ℓ - delta ℓ` and `nHigh ℓ = nFloor ℓ + delta ℓ` (`n - 1` and `n` at `ℓ = 0`),
    ID bit-widths `idBits ℓ = 4 * Nat.clog 2 (2 * nFloor ℓ)`, and quotient ranges `quotUniv ℓ`
    satisfy the exact conservation identity `numNodes ℓ * 2 ^ idBits ℓ * quotUniv ℓ = paddedUniv`
    at every level `1 ≤ ℓ ≤ k` (`TreeSchedule.numNodes_mul_idUniv_mul_quotUniv`).
* **Shared root value pool capacity (Section 5.2 adaptation for arbitrary value bound `V`)**:
  Section 5.2 (PDF pp. 28–29 / printed pp. 27–28) analyzes key-only root tables where `O(Δ_1)`
  unused root slots per root cost `O((N / n_1) * Δ_1 * log U) = O(N / log ^ 2 N)` bits. For general
  values in `Fin V` (with no upper bound on `log₂ V`), storing `⌈log₂ V⌉` bits inside every unused
  root slot would waste `Θ((n / log ^ 3 n) * log₂ V)` bits. Instead, the bit-budget layout in
  `BitBudget.lean` allocates a shared root value pool of exact capacity
  `rootValPoolCap = n - numNodes 2 * nLow 2`, so total value slots across leaves, inner storage
  tables, and the shared root value pool equal `n` (`TreeSchedule.total_value_slots_eq_cap`).
  Note that `totalTreeBits` in `BitBudget.lean` computes the arithmetic bit budget of the intended
  Section 5 layout and is not tied to an operational state by an explicit bit-packing encoding
  (pure node storage and tree operations follow in Stage 2, #5349). Total bit usage in `Params.lean`
  is bounded by `infoBits U V n + O(R)` unconditionally for **all** `1 ≤ V`.

## Scope and explicit out-of-scope gaps

This module covers the integer-exact parameter schedule and value-slot conservation identities for
the Section 5 large-parameter polynomial-`U` milestone (`n / log₂ ^ 0.1 n ≤ R ≤ n`,
`n ^ (1 + α_min) ≤ U ≤ n ^ (1 + α_max)`). Bit-budget accounting (`BitBudget.lean`, `Params.lean`)
and regime-switched node seeds (`NodeSeeds.lean`, `SeedBounds.lean`) build on this module in
Stage 1; pure node storage structures, deterministic tree operations, and expected rehashing bounds
(Stages 2–3, #5349), Word-RAM `Memory.Prog` compilation, Section 4 small-parameter adapter
trees (`R < n / log₂ ^ 0.1 n`), strong history independence, dynamic resizing in `|S|`, and
super-polynomial key universes (`U > n ^ (1 + α_max)`) are out of scope here.

## Main definitions

* `Cslib.DataStructure.Dictionary.SubconstantRedundancy.infoBits`: exact information-theoretic
  benchmark `⌈log₂(C(U, n) * V ^ n)⌉`.
* `Cslib.DataStructure.Dictionary.SubconstantRedundancy.effRedundancy`, `redundancyRatio`,
  `treeDepth`, `targetSize`, `cumBranchBits`, `branchBits`, `branchFactor`, `numNodes`, `nFloor`,
  `delta`, `nLow`, `nHigh`, `idBits`, `quotUnivOne`: integer-exact tree parameter schedule helpers.
* `Cslib.DataStructure.Dictionary.SubconstantRedundancy.TreeSchedule`,
  `TreeSchedule.ConcentrationReady`: reusable abstract tree parameter bundle and concentration
  hypotheses.

## Main results

* `minRedundancyRatio_le_redundancyRatio`, `two_pow_logStar_le_redundancyRatio`,
  `iterLog_treeDepth_le`, `lt_iterLog_of_lt_treeDepth`: clamped redundancy and tree-depth bounds.
* `TreeSchedule.numNodes_mul_idUniv_mul_quotUniv`: exact `paddedUniv` factorization across all tree
  levels.
* `TreeSchedule.leaf_add_inner_slots_eq`, `TreeSchedule.total_value_slots_eq_cap`: telescoping
  value-slot conservation across leaves, inner storage tables, and the shared root value pool.

## References

* [T. Li, J. Liang, H. Yu, and R. Zhou,
  *Dynamic Dictionary with Subconstant Wasted Bits per Key*][LiLiangYuZhou2024]
* [M. Pătrașcu, *Succincter*][Patrascu2008]
* [M. Thorup, *Simple Tabulation, Fast Expanders, Double Tabulation, and High
  Independence*][Thorup2013]
-/

public section

namespace Cslib.DataStructure.Dictionary.SubconstantRedundancy

open Cslib.DataStructure.Dictionary
open Finset

/-! ## Section 1: Information benchmark, clamped redundancy, and integer schedule -/

/-- Exact integer ceiling `⌈log₂(C(U, n) * V ^ n)⌉` of the information-theoretic dictionary bit
lower bound (`Minimap.infoBits U n V`), avoiding per-key ceiling loss when `V` is not a power of
two. -/
abbrev infoBits (U V n : ℕ) : ℕ :=
  Minimap.infoBits U n V

/-- Minimum clamped redundancy ratio `r₀ = 256` (`2 ^ 8`), chosen so leaf target sizes `r ^ 9`
dominate `(150 * m) ^ 3` in the child-router moment concentration inequality across all `R ≤ n`. -/
@[expose]
def minRedundancyRatio : ℕ :=
  256

/-- Clamped internal redundancy `R_eff = min R (max 1 (n / max 256 (2 ^ log* n)))`, ensuring
`R_eff ≤ R` unconditionally, and `256 ≤ n / R_eff` and `2 ^ log* n ≤ n / R_eff` across all
`1 ≤ R` whenever `max 256 (2 ^ log* n) ≤ n` ([LiLiangYuZhou2024, Section 5], PDF p. 26 /
printed p. 25). -/
@[expose]
def effRedundancy (n R : ℕ) : ℕ :=
  min R (max 1 (n / max minRedundancyRatio (2 ^ Nat.logStar n)))

/-- Internal per-key inverse-redundancy scale `r = n / max (effRedundancy n R) 1`. -/
@[expose]
def redundancyRatio (n R : ℕ) : ℕ :=
  n / max (effRedundancy n R) 1

/-- Bounded fuel helper scanning levels `ℓ = cur, cur + 1, …` for the first `ℓ` with
`Nat.iterLog ℓ U ≤ 4 * r`. -/
def treeDepthAux (U r cur : ℕ) : ℕ → ℕ
  | 0 => cur
  | fuel + 1 =>
    if Nat.iterLog cur U ≤ 4 * r then cur
    else treeDepthAux U r (cur + 1) fuel

/-- Tree depth `k ≥ 2`: the least `ℓ ≥ 2` (within `Nat.floorLogStar U + 2`) such that
`Nat.iterLog ℓ U ≤ 4 * r`. -/
@[wram_arith]
def treeDepth (U r : ℕ) : ℕ :=
  treeDepthAux U r 2 (Nat.floorLogStar U)

/-- Target expected node size lower bound at level `ℓ`: `n` at `ℓ = 0`, `(Nat.iterLog ℓ U) ^ 9` at
internal levels `1 ≤ ℓ < k`, and `r ^ 9` at leaf level `ℓ ≥ k`. -/
@[expose]
def targetSize (n U r k ℓ : ℕ) : ℕ :=
  if ℓ = 0 then n
  else if ℓ < k then (Nat.iterLog ℓ U) ^ 9
  else r ^ 9

/-- Cumulative base-2 branching exponent `S_ℓ` (`numNodes ℓ = 2 ^ S_ℓ`): `0` at `ℓ = 0` and
`⌊log₂(n / targetSize n U r k ℓ)⌋` for `1 ≤ ℓ`. -/
@[expose]
def cumBranchBits (n U r k ℓ : ℕ) : ℕ :=
  if ℓ = 0 then 0
  else Nat.log 2 (n / max (targetSize n U r k ℓ) 1)

/-- Per-level branching bit-width `s_ℓ = S_{ℓ + 1} - S_ℓ` (`B_ℓ = 2 ^ s_ℓ`). -/
@[expose]
def branchBits (n U r k ℓ : ℕ) : ℕ :=
  cumBranchBits n U r k (ℓ + 1) - cumBranchBits n U r k ℓ

/-- Power-of-two branching factor `B_ℓ = 2 ^ branchBits ℓ`. -/
@[expose]
def branchFactor (n U r k ℓ : ℕ) : ℕ :=
  2 ^ branchBits n U r k ℓ

/-- Total number of level-`ℓ` nodes `N_ℓ = 2 ^ cumBranchBits ℓ` across the forest. -/
@[expose]
def numNodes (n U r k ℓ : ℕ) : ℕ :=
  2 ^ cumBranchBits n U r k ℓ

/-- Integer floor `⌊n / N_ℓ⌋` of the expected key load per level-`ℓ` node. -/
@[expose]
def nFloor (n U r k ℓ : ℕ) : ℕ :=
  n / numNodes n U r k ℓ

/-- Allowed load-deviation radius `Δ_ℓ = ⌊(nFloor ℓ) ^ (2 / 3)⌋` at level `ℓ`. -/
@[expose]
def delta (n U r k ℓ : ℕ) : ℕ :=
  Nat.nthRoot 3 ((nFloor n U r k ℓ) ^ 2)

/-- Lower key-load threshold `n_low_ℓ`: `n - 1` at `ℓ = 0`, and `nFloor ℓ - delta ℓ` for `ℓ ≥ 1`. -/
@[expose]
def nLow (n U r k ℓ : ℕ) : ℕ :=
  if ℓ = 0 then n - 1 else nFloor n U r k ℓ - delta n U r k ℓ

/-- Upper key-load threshold `n_high_ℓ`: `n` at `ℓ = 0`, and `nFloor ℓ + delta ℓ` for `ℓ ≥ 1`. -/
@[expose]
def nHigh (n U r k ℓ : ℕ) : ℕ :=
  if ℓ = 0 then n else nFloor n U r k ℓ + delta n U r k ℓ

/-- Key-ID bit width `I_ℓ = 4 * ⌈log₂(2 * nFloor ℓ)⌉` at level `1 ≤ ℓ ≤ k` (`≥ 4 log₂ n_ℓ + 4`). -/
@[expose, wram_arith]
def idBits (n U r k ℓ : ℕ) : ℕ :=
  4 * Nat.clog 2 (2 * max (nFloor n U r k ℓ) 1)

/-- Level-1 quotient range `Q_1 = ⌈(U + n) / (B_0 * 2 ^ I_1)⌉` covering `U` real keys plus `n`
sentinel keys. -/
@[expose]
def quotUnivOne (n U r k : ℕ) : ℕ :=
  let step := branchFactor n U r k 0 * 2 ^ idBits n U r k 1
  (U + n + step - 1) / step

/-! ## Section 2: Basic properties of `effRedundancy`, `redundancyRatio`, and `treeDepth` -/

theorem effRedundancy_le (n R : ℕ) : effRedundancy n R ≤ R :=
  min_le_left _ _

theorem effRedundancy_pos {R : ℕ} (hR : 1 ≤ R) (n : ℕ) : 1 ≤ effRedundancy n R :=
  le_min hR (le_max_left 1 _)

/-- A positive `a ≤ n` below the clamp `max minRedundancyRatio (2 ^ log* n)` lower-bounds the
redundancy ratio. -/
private theorem le_redundancyRatio {n R a : ℕ} (ha : 0 < a)
    (haM : a ≤ max minRedundancyRatio (2 ^ Nat.logStar n)) (hn : a ≤ n) :
    a ≤ redundancyRatio n R := by
  have h1 := Nat.div_le_div_left (a := n) haM ha
  have h2 : 1 ≤ n / a := (Nat.le_div_iff_mul_le ha).mpr (by omega)
  dsimp only [redundancyRatio, effRedundancy]
  rw [Nat.le_div_iff_mul_le (by positivity), mul_comm, ← Nat.le_div_iff_mul_le ha]
  omega

theorem minRedundancyRatio_le_redundancyRatio {n R : ℕ} (hn : minRedundancyRatio ≤ n) :
    minRedundancyRatio ≤ redundancyRatio n R :=
  le_redundancyRatio (by decide) (le_max_left _ _) hn

theorem two_pow_logStar_le_redundancyRatio {n R : ℕ} (hn : 2 ^ Nat.logStar n ≤ n) :
    2 ^ Nat.logStar n ≤ redundancyRatio n R :=
  le_redundancyRatio (Nat.two_pow_pos _) (le_max_right _ _) hn

private theorem le_treeDepthAux (U r cur fuel : ℕ) : cur ≤ treeDepthAux U r cur fuel := by
  fun_induction treeDepthAux U r cur fuel <;> omega

private theorem treeDepthAux_le (U r cur fuel : ℕ) :
    treeDepthAux U r cur fuel ≤ cur + fuel := by
  fun_induction treeDepthAux U r cur fuel <;> omega

private theorem iterLog_treeDepthAux_le {U r cur fuel : ℕ}
    (hend : Nat.iterLog (cur + fuel) U ≤ max (4 * r) 1) :
    Nat.iterLog (treeDepthAux U r cur fuel) U ≤ max (4 * r) 1 := by
  fun_induction treeDepthAux U r cur fuel with
  | case1 => simpa only [Nat.add_zero] using hend -- fuel exhausted
  | case2 _ _ hle => exact hle.trans (le_max_left _ _) -- iterLog cur U ≤ 4 * r: stop at cur
  -- iterLog cur U > 4 * r: try cur + 1
  | case3 _ _ _ ih => exact ih (by rwa [Nat.add_right_comm, Nat.add_assoc])

private theorem lt_iterLog_of_lt_treeDepthAux {U r cur fuel ℓ : ℕ}
    (hlo : cur ≤ ℓ) (hlt : ℓ < treeDepthAux U r cur fuel) :
    4 * r < Nat.iterLog ℓ U := by
  fun_induction treeDepthAux U r cur fuel with
  | case3 cur _ hgt' ih => -- iterLog cur U > 4 * r: try cur + 1
    rcases eq_or_lt_of_le hlo with rfl | hgt
    · exact not_le.mp hgt'
    · exact ih (Nat.succ_le_of_lt hgt) hlt
  | _ => omega -- fuel exhausted, or iterLog cur U ≤ 4 * r: stop at cur

theorem two_le_treeDepth (U r : ℕ) : 2 ≤ treeDepth U r :=
  le_treeDepthAux U r 2 _

theorem treeDepth_le (U r : ℕ) : treeDepth U r ≤ Nat.floorLogStar U + 2 :=
  (treeDepthAux_le U r 2 _).trans_eq (Nat.add_comm 2 _)

theorem iterLog_treeDepth_le {U r : ℕ} (hr : 1 ≤ r) :
    Nat.iterLog (treeDepth U r) U ≤ 4 * r := by
  have hend := (Nat.iterLog_anti_left U (Nat.le_add_left _ 2)).trans
    (Nat.iterLog_floorLogStar_le_one U)
  exact max_eq_left (by omega : 1 ≤ 4 * r) ▸ iterLog_treeDepthAux_le (hend.trans (le_max_right _ _))

theorem lt_iterLog_of_lt_treeDepth {U r ℓ : ℕ} (h2 : 2 ≤ ℓ) (hlt : ℓ < treeDepth U r) :
    4 * r < Nat.iterLog ℓ U :=
  lt_iterLog_of_lt_treeDepthAux h2 hlt

/-! ## Section 3: Abstract `TreeSchedule` bundle and exact level conservation laws -/

/-- Abstract structural parameter bundle for a Section 5 multi-level dictionary tree.
Both small concrete test schedules and `canonicalSchedule` (under `ValidRegime`) instantiate
`TreeSchedule`, decoupling pure node and tree operations from asymptotic threshold constants. -/
structure TreeSchedule where
  /-- External key universe size `U`. -/
  univ : ℕ
  /-- Value bound `V` (`1 ≤ V`). -/
  valBound : ℕ
  /-- Dictionary capacity `n` (`2 ≤ n`; internal tree holds `n - 1` or `n` active keys). -/
  cap : ℕ
  /-- Tree depth `k ≥ 2` (`0` = top router, `1` = roots, `2 .. k - 1` = inner, `k` = leaves). -/
  depth : ℕ
  /-- Per-level branching bit-widths `s_ℓ` (`0 ≤ ℓ < depth`, `B_ℓ = 2 ^ s_ℓ`). -/
  branchBits : ℕ → ℕ
  /-- Integer floor `nFloor ℓ` of expected load at level `0 ≤ ℓ ≤ depth` (`nFloor 0 = cap`). -/
  nFloor : ℕ → ℕ
  /-- Load-deviation radius `Δ_ℓ` (`1 ≤ ℓ ≤ depth`). -/
  delta : ℕ → ℕ
  /-- Key-ID bit-width `I_ℓ` (`1 ≤ ℓ ≤ depth`). -/
  idBits : ℕ → ℕ
  /-- Level-1 quotient universe `Q_1 ≥ 1`. -/
  quotOne : ℕ
  /-- Inverse space exponent `ε_inv` for `DoubleTabulation` child routers. -/
  epsInv : ℕ
  /-- Gap exponent `α_inv` for `DoubleTabulation` child routers. -/
  alphaInv : ℕ
  val_pos : 1 ≤ valBound
  two_le_cap : 2 ≤ cap
  two_le_depth : 2 ≤ depth
  quotOne_pos : 1 ≤ quotOne
  nFloor_zero : nFloor 0 = cap
  nFloor_pos : ∀ ℓ ≤ depth, 1 ≤ nFloor ℓ
  branchBits_pos : ∀ ℓ < depth, 1 ≤ branchBits ℓ
  delta_lt_nFloor : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ depth → delta ℓ < nFloor ℓ
  nFloor_step_le : ∀ ℓ < depth, 2 ^ branchBits ℓ * nFloor (ℓ + 1) ≤ nFloor ℓ
  inner_cap_le : ∀ ℓ, 2 ≤ ℓ → ℓ < depth →
    2 ^ branchBits ℓ * (nFloor (ℓ + 1) - delta (ℓ + 1)) ≤ nFloor ℓ - delta ℓ
  root_cap_le :
    2 ^ branchBits 1 * (nFloor 2 - delta 2) ≤ nFloor 1 + delta 1
  idBits_step_le : ∀ ℓ, 1 ≤ ℓ → ℓ < depth →
    branchBits ℓ + idBits (ℓ + 1) ≤ idBits ℓ
  nHigh_le_two_pow_idBits : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ depth →
    nFloor ℓ + delta ℓ ≤ 2 ^ idBits ℓ
  univ_le_padded :
    univ + cap ≤ 2 ^ branchBits 0 * 2 ^ idBits 1 * quotOne

namespace TreeSchedule

variable (P : TreeSchedule)

/-- Branching factor `B_ℓ = 2 ^ s_ℓ` at level `ℓ`. -/
@[expose]
def branchFactor (ℓ : ℕ) : ℕ :=
  2 ^ P.branchBits ℓ

/-- Cumulative branching bit-depth `S_ℓ = s_0 + ⋯ + s_{ℓ - 1}`. -/
@[expose]
def cumBranchBits (P : TreeSchedule) : ℕ → ℕ
  | 0 => 0
  | ℓ + 1 => cumBranchBits P ℓ + P.branchBits ℓ

/-- Total number of level-`ℓ` nodes `N_ℓ = 2 ^ S_ℓ` across the forest. -/
@[expose]
def numNodes (ℓ : ℕ) : ℕ :=
  2 ^ P.cumBranchBits ℓ

@[simp]
theorem numNodes_zero : P.numNodes 0 = 1 := rfl

theorem numNodes_succ (ℓ : ℕ) : P.numNodes (ℓ + 1) = P.numNodes ℓ * P.branchFactor ℓ :=
  Nat.pow_add 2 (cumBranchBits P ℓ) (P.branchBits ℓ)

theorem numNodes_pos (ℓ : ℕ) : 0 < P.numNodes ℓ :=
  Nat.two_pow_pos _

theorem branchFactor_pos (ℓ : ℕ) : 0 < P.branchFactor ℓ :=
  Nat.two_pow_pos _

/-- Lower load threshold `nLow ℓ` (`cap - 1` at `0`, `nFloor ℓ - delta ℓ` for `ℓ ≥ 1`). -/
@[expose]
def nLow (ℓ : ℕ) : ℕ :=
  if ℓ = 0 then P.cap - 1 else P.nFloor ℓ - P.delta ℓ

/-- Upper load threshold `nHigh ℓ` (`cap` at `0`, `nFloor ℓ + delta ℓ` for `ℓ ≥ 1`). -/
@[expose]
def nHigh (ℓ : ℕ) : ℕ :=
  if ℓ = 0 then P.cap else P.nFloor ℓ + P.delta ℓ

/-- Waiting-list capacity `2 * delta ℓ` at level `ℓ ≥ 2` (`nHigh ℓ - nLow ℓ = 2 * delta ℓ`). -/
@[expose]
def waitCap (ℓ : ℕ) : ℕ :=
  2 * P.delta ℓ

theorem nLow_pos {ℓ : ℕ} (hℓ : ℓ ≤ P.depth) : 1 ≤ P.nLow ℓ := by
  unfold nLow
  split_ifs with h0
  · exact Nat.le_sub_one_of_lt P.two_le_cap
  · exact Nat.sub_pos_of_lt (P.delta_lt_nFloor ℓ (Nat.pos_of_ne_zero h0) hℓ)

theorem nLow_le_nHigh (ℓ : ℕ) : P.nLow ℓ ≤ P.nHigh ℓ := by
  dsimp only [nLow, nHigh]
  split_ifs <;> omega

theorem nHigh_sub_nLow {ℓ : ℕ} (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.depth) :
    P.nHigh ℓ - P.nLow ℓ = P.waitCap ℓ := by
  have hd := P.delta_lt_nFloor ℓ h1 hℓ
  simp only [nHigh, nLow, waitCap, Nat.ne_of_gt h1, ↓reduceIte]
  omega

/-- Quotient remainder bit-shift `I_ℓ - s_ℓ - I_{ℓ + 1}` on edge `ℓ → ℓ + 1`. -/
@[expose, wram_arith]
def remBits (ℓ : ℕ) : ℕ :=
  P.idBits ℓ - P.branchBits ℓ - P.idBits (ℓ + 1)

/-- Quotient universe `Q_ℓ` at level `ℓ ≥ 1`. -/
@[expose]
def quotUniv (P : TreeSchedule) : ℕ → ℕ
  | 0 => P.quotOne
  | 1 => P.quotOne
  | ℓ + 2 => quotUniv P (ℓ + 1) * 2 ^ P.remBits (ℓ + 1)

/-- Padded top-level key universe `U_pad = B_0 * 2 ^ I_1 * Q_1`. -/
@[expose]
def paddedUniv : ℕ :=
  P.branchFactor 0 * 2 ^ P.idBits 1 * P.quotOne

theorem quotUniv_pos (ℓ : ℕ) : 1 ≤ P.quotUniv ℓ := by
  fun_induction quotUniv P ℓ with
  | case3 _ ih => exact Nat.mul_pos ih (Nat.two_pow_pos _) -- ℓ + 2
  | _ => exact P.quotOne_pos -- ℓ = 0 or ℓ = 1

theorem quotUniv_succ_of_pos {ℓ : ℕ} (h1 : 1 ≤ ℓ) :
    P.quotUniv (ℓ + 1) = P.quotUniv ℓ * 2 ^ P.remBits ℓ := by
  obtain ⟨_ | d, rfl⟩ := Nat.exists_eq_add_of_le h1 <;> rfl

/-- **Exact ID-quotient universe conservation**: `N_ℓ * 2 ^ I_ℓ * Q_ℓ = U_pad` across all
`1 ≤ ℓ ≤ depth`. -/
theorem numNodes_mul_idUniv_mul_quotUniv {ℓ : ℕ} (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.depth) :
    P.numNodes ℓ * 2 ^ P.idBits ℓ * P.quotUniv ℓ = P.paddedUniv := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h1
  induction d with
  | zero =>
    simp [numNodes_succ, numNodes_zero, quotUniv, paddedUniv]
  | succ d ih =>
    have hstep := P.idBits_step_le (1 + d) (Nat.le_add_right 1 d) (by omega)
    have hexp : P.idBits (1 + d + 1) + P.branchBits (1 + d) + P.remBits (1 + d) =
        P.idBits (1 + d) := by wram_omega
    calc P.numNodes (1 + (d + 1)) * 2 ^ P.idBits (1 + (d + 1)) * P.quotUniv (1 + (d + 1))
        = (P.numNodes (1 + d) * 2 ^ P.branchBits (1 + d)) *
            2 ^ P.idBits (1 + d + 1) *
            (P.quotUniv (1 + d) * 2 ^ P.remBits (1 + d)) := by
          rw [← Nat.add_assoc, numNodes_succ, branchFactor,
            quotUniv_succ_of_pos P (Nat.le_add_right 1 d)]
      _ = P.numNodes (1 + d) *
            (2 ^ P.idBits (1 + d + 1) * 2 ^ P.branchBits (1 + d) * 2 ^ P.remBits (1 + d)) *
            P.quotUniv (1 + d) := by ring
      _ = P.numNodes (1 + d) * 2 ^ P.idBits (1 + d) * P.quotUniv (1 + d) := by
          rw [← Nat.pow_add, ← Nat.pow_add, hexp]
      _ = P.paddedUniv := ih (by omega) (by omega)

/-- Right-coordinate universe `T_ℓ` of the level-`ℓ` Feistel child router (`2 ^ I_1 * Q_1` at
`ℓ = 0`, `2 ^ (I_ℓ - s_ℓ)` for `1 ≤ ℓ < depth`). -/
@[expose]
def routerRightUniv (ℓ : ℕ) : ℕ :=
  if ℓ = 0 then 2 ^ P.idBits 1 * P.quotOne
  else 2 ^ (P.idBits ℓ - P.branchBits ℓ)

/-- Right-coordinate universe `T'_ℓ` of the level-`ℓ` Feistel ID compressor (`Q_1` at `ℓ = 1`,
`2 ^ (I_{ℓ - 1} - s_{ℓ - 1} - I_ℓ) = 2 ^ remBits (ℓ - 1)` for `2 ≤ ℓ ≤ depth`). -/
@[expose]
def idCompRightUniv (ℓ : ℕ) : ℕ :=
  if ℓ ≤ 1 then P.quotOne else 2 ^ P.remBits (ℓ - 1)

/-- Node storage capacity `m_ℓ` (`nHigh 1 - B_1 * nLow 2` at `ℓ = 1`,
`nLow ℓ - B_ℓ * nLow (ℓ + 1)` for `2 ≤ ℓ < depth`, and `nLow depth` at `ℓ = depth`). -/
@[expose]
def tableCap (ℓ : ℕ) : ℕ :=
  if ℓ = 1 then P.nHigh 1 - P.branchFactor 1 * P.nLow 2
  else if ℓ < P.depth then P.nLow ℓ - P.branchFactor ℓ * P.nLow (ℓ + 1)
  else P.nLow P.depth

/-- Capacity `cap - N_2 * nLow 2` of the shared root value pool. -/
@[expose, wram_arith]
def rootValPoolCap : ℕ :=
  P.cap - P.numNodes 2 * P.nLow 2

theorem numNodes_two_mul_nLow_two_le_cap : P.numNodes 2 * P.nLow 2 ≤ P.cap := by
  calc P.numNodes 2 * P.nLow 2
      = P.branchFactor 0 * (P.branchFactor 1 * P.nLow 2) := by
        simp [numNodes_succ, numNodes_zero, Nat.mul_assoc]
    _ ≤ P.branchFactor 0 * (P.branchFactor 1 * P.nFloor 2) := by
        gcongr; exact Nat.sub_le _ _
    _ ≤ P.branchFactor 0 * P.nFloor 1 :=
        Nat.mul_le_mul_left _ (P.nFloor_step_le 1 (by have := P.two_le_depth; omega))
    _ ≤ P.nFloor 0 := P.nFloor_step_le 0 (by have := P.two_le_depth; omega)
    _ = P.cap := P.nFloor_zero

/-- Lower load bound for children at inner levels:
`B_ℓ * nLow (ℓ + 1) ≤ nLow ℓ` for `2 ≤ ℓ < depth`. -/
theorem branchFactor_mul_nLow_succ_le_nLow {ℓ : ℕ} (h1 : 2 ≤ ℓ) (hlt : ℓ < P.depth) :
    P.branchFactor ℓ * P.nLow (ℓ + 1) ≤ P.nLow ℓ := by
  dsimp only [nLow, branchFactor]
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  exact P.inner_cap_le ℓ h1 hlt

/-- Inner table capacity identity:
`tableCap ℓ + B_ℓ * nLow (ℓ + 1) = nLow ℓ` for `2 ≤ ℓ < depth`. -/
theorem tableCap_add_branchFactor_mul_nLow_succ {ℓ : ℕ} (h1 : 2 ≤ ℓ) (hlt : ℓ < P.depth) :
    P.tableCap ℓ + P.branchFactor ℓ * P.nLow (ℓ + 1) = P.nLow ℓ := by
  dsimp only [tableCap]
  rw [ite_eq_right (by omega), ite_eq_left hlt,
    Nat.sub_add_cancel (P.branchFactor_mul_nLow_succ_le_nLow h1 hlt)]

/-- Telescoping slot identity across inner levels `2 .. depth - 1` and leaf level `depth`:
`N_depth * nLow depth + ∑_{ℓ ∈ Ico 2 depth} N_ℓ * tableCap ℓ = N_2 * nLow 2`. -/
theorem leaf_add_inner_slots_eq :
    P.numNodes P.depth * P.nLow P.depth +
      ∑ ℓ ∈ Finset.Ico 2 P.depth, P.numNodes ℓ * P.tableCap ℓ =
      P.numNodes 2 * P.nLow 2 := by
  have hgen : ∀ m, 2 ≤ m → m ≤ P.depth →
      P.numNodes m * P.nLow m + ∑ ℓ ∈ Finset.Ico 2 m, P.numNodes ℓ * P.tableCap ℓ =
        P.numNodes 2 * P.nLow 2 := by
    intro m hm2 hm_le
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm2
    induction d with
    | zero => simp
    | succ d ih =>
      have hcomb : P.numNodes (2 + d + 1) * P.nLow (2 + d + 1) +
          P.numNodes (2 + d) * P.tableCap (2 + d) = P.numNodes (2 + d) * P.nLow (2 + d) := by
        rw [numNodes_succ, Nat.mul_assoc, ← Nat.mul_add, add_comm (P.branchFactor (2 + d) * _),
          P.tableCap_add_branchFactor_mul_nLow_succ (by omega) (by omega)]
      rw [← Nat.add_assoc, Finset.sum_Ico_succ_top (by omega)]
      linarith [ih (by omega) (by omega), hcomb]
  exact hgen P.depth P.two_le_depth le_rfl

/-- Total value-slot conservation across leaf minimaps, inner tables, and the shared root value
pool: `leafSlots + innerSlots + rootValPoolCap = cap` (`= n`). -/
theorem total_value_slots_eq_cap :
    P.numNodes P.depth * P.nLow P.depth +
      (∑ ℓ ∈ Finset.Ico 2 P.depth, P.numNodes ℓ * P.tableCap ℓ) +
      P.rootValPoolCap = P.cap := by
  rw [P.leaf_add_inner_slots_eq]
  exact Nat.add_sub_of_le P.numNodes_two_mul_nLow_two_le_cap

/-- Probabilistic concentration readiness for `Claim 5.4` and `Lemma 5.3` across all levels of
`P`. -/
structure ConcentrationReady : Prop where
  six_le_nFloor : ∀ ℓ ≤ P.depth, 6 ≤ P.nFloor ℓ
  two_mul_delta_le_nFloor : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ P.depth → 2 * P.delta ℓ ≤ P.nFloor ℓ
  gap_bound : ∀ ℓ < P.depth,
    2 ^ P.branchBits ℓ * P.routerRightUniv ℓ ≤ (P.routerRightUniv ℓ) ^ max P.alphaInv 1
  conc_bound : ∀ ℓ < P.depth,
    2 ^ P.branchBits ℓ * (150 * FeistelPerm.childRouterHalfInd (P.nHigh ℓ)) ^ 3 ≤ P.nLow ℓ
  window_contained : ∀ ℓ < P.depth, ∀ m b_load : ℕ,
    P.nLow ℓ ≤ m → m ≤ P.nHigh ℓ →
    (m : ℝ) / (2 ^ P.branchBits ℓ : ℝ) -
        ((1 : ℝ) / 5) * ((m : ℝ) / (2 ^ P.branchBits ℓ : ℝ)) ^ ((2 : ℝ) / 3) ≤ (b_load : ℝ) →
    (b_load : ℝ) ≤ (m : ℝ) / (2 ^ P.branchBits ℓ : ℝ) +
        ((1 : ℝ) / 5) * ((m : ℝ) / (2 ^ P.branchBits ℓ : ℝ)) ^ ((2 : ℝ) / 3) →
    P.nLow (ℓ + 1) ≤ b_load ∧ b_load ≤ P.nHigh (ℓ + 1)
  id_collision_bound : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ P.depth →
    (P.nHigh ℓ) ^ 2 * (P.nFloor ℓ) ^ 2 ≤ 4 * 2 ^ P.idBits ℓ

end TreeSchedule

/-! ## Section 4: Quantitative bounds for the canonical integer schedule -/

/-- Level scale `s_ℓ`: `Nat.iterLog ℓ U` for `ℓ < k`, and `r` for `ℓ ≥ k`. -/
@[expose]
def levelScale (U r k ℓ : ℕ) : ℕ :=
  if ℓ < k then Nat.iterLog ℓ U else r

theorem targetSize_eq_levelScale_pow {n U r k ℓ : ℕ} (h1 : 1 ≤ ℓ) :
    targetSize n U r k ℓ = (levelScale U r k ℓ) ^ 9 := by
  dsimp only [targetSize, levelScale]
  rw [ite_eq_right (by omega)]
  split_ifs <;> rfl

theorem r_le_levelScale {U r ℓ : ℕ} (h1 : 1 ≤ ℓ) (hU : 4 * r ≤ Nat.log 2 U) :
    r ≤ levelScale U r (treeDepth U r) ℓ := by
  dsimp only [levelScale]
  split_ifs with hlt
  · rcases eq_or_lt_of_le h1 with rfl | hgt
    · simpa only [Nat.iterLog_succ, Nat.iterLog_zero] using (by omega : r ≤ Nat.log 2 U)
    · linarith [lt_iterLog_of_lt_treeDepth (Nat.succ_le_of_lt hgt) hlt]
  · exact le_rfl

/-- Across all `0 ≤ ℓ < treeDepth U r`, consecutive target sizes shrink by at least `2 ^ 18`
(`= 4 ^ 9`). -/
theorem two_pow_eighteen_mul_targetSize_succ_le {n U r ℓ : ℕ}
    (hr : minRedundancyRatio ≤ r)
    (hU : 4 * r ≤ Nat.log 2 U)
    (hn : 2 ^ 18 * (Nat.log 2 U) ^ 9 ≤ n)
    (hlt : ℓ < treeDepth U r) :
    let k := treeDepth U r
    2 ^ 18 * targetSize n U r k (ℓ + 1) ≤ targetSize n U r k ℓ := by
  intro k
  have hk2 : 2 ≤ k := two_le_treeDepth U r
  have hr256 : 256 ≤ r := hr
  rcases Nat.eq_zero_or_pos ℓ with rfl | hpos
  · dsimp only [targetSize]
    rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_left rfl]
    simpa only [Nat.iterLog_succ, Nat.iterLog_zero] using hn
  · rw [targetSize_eq_levelScale_pow (by omega), targetSize_eq_levelScale_pow hpos]
    change 4 ^ 9 * (levelScale U r k (ℓ + 1)) ^ 9 ≤ _
    rw [← Nat.mul_pow]
    refine Nat.pow_le_pow_left ?_ 9
    dsimp only [levelScale]
    rw [ite_eq_left hlt]
    by_cases hlt1 : ℓ + 1 < k
    · rw [ite_eq_left hlt1]
      set s := Nat.iterLog (ℓ + 1) U
      have hs_gt : 4 * r < s := lt_iterLog_of_lt_treeDepth (by omega) hlt1
      have hs_ge : 4 ≤ s := by omega
      have h4s : 4 * s ≤ 2 ^ s := by nlinarith [Nat.sq_le_two_pow hs_ge]
      refine h4s.trans (Nat.pow_log_le_self 2 fun h0 => ?_)
      simp only [s, Nat.iterLog_succ, h0, Nat.log_zero_right] at hs_gt
      omega
    · rw [ite_eq_right hlt1]
      rcases eq_or_lt_of_le (Nat.succ_le_of_lt hpos) with rfl | hgt
      · simpa only [Nat.iterLog_succ, Nat.iterLog_zero] using hU
      · exact (lt_iterLog_of_lt_treeDepth (Nat.succ_le_of_lt hgt) hlt).le

theorem targetSize_le_of_step {n U r k : ℕ}
    (hstep : ∀ j < k, 2 ^ 18 * targetSize n U r k (j + 1) ≤ targetSize n U r k j) :
    ∀ ℓ ≤ k, targetSize n U r k ℓ ≤ n := by
  intro ℓ hℓ
  induction ℓ with
  | zero => simp [targetSize]
  | succ j ih => linarith [hstep j (Nat.lt_of_succ_le hℓ), ih (Nat.le_of_succ_le hℓ)]

theorem targetSize_pos {n U r k ℓ : ℕ}
    (hn : 1 ≤ n) (hr : 1 ≤ r) (hU : 4 * r ≤ Nat.log 2 U) (hℓ : ℓ ≤ treeDepth U r)
    (hk : k = treeDepth U r) :
    1 ≤ targetSize n U r k ℓ := by
  subst hk
  rcases Nat.eq_zero_or_pos ℓ with rfl | hpos
  · simpa only [targetSize, ↓reduceIte] using hn
  · rw [targetSize_eq_levelScale_pow hpos]
    exact Nat.one_le_pow 9 _ (hr.trans (r_le_levelScale hpos hU))

theorem numNodes_mul_targetSize_bounds {n U r k ℓ : ℕ}
    (hpos : 1 ≤ targetSize n U r k ℓ) (hle : targetSize n U r k ℓ ≤ n) :
    numNodes n U r k ℓ * targetSize n U r k ℓ ≤ n ∧
      n < 2 * numNodes n U r k ℓ * targetSize n U r k ℓ := by
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ_pos
  · simp only [numNodes, cumBranchBits, targetSize, ↓reduceIte, pow_zero, one_mul]
    exact ⟨hle, by omega⟩
  · set T := targetSize n U r k ℓ with hT
    set q := n / T
    have hN : numNodes n U r k ℓ = 2 ^ Nat.log 2 q := by
      simp only [numNodes, cumBranchBits, hℓ_pos.ne', ↓reduceIte, ← hT, max_eq_left hpos, q]
    have hlo : numNodes n U r k ℓ ≤ q :=
      hN ▸ Nat.pow_log_le_self 2 (Nat.div_pos hle hpos).ne'
    have hhi : q < 2 * numNodes n U r k ℓ := by
      rw [hN, mul_comm 2, ← pow_succ]
      exact Nat.lt_pow_succ_log_self Nat.one_lt_two q
    refine ⟨(Nat.mul_le_mul_right T hlo).trans (Nat.div_mul_le_self n T), ?_⟩
    calc n < T * (q + 1) := Nat.lt_mul_div_succ n hpos
      _ ≤ T * (2 * numNodes n U r k ℓ) := Nat.mul_le_mul_left T hhi
      _ = 2 * numNodes n U r k ℓ * T := by ring

theorem targetSize_le_nFloor_and_lt {n U r k ℓ : ℕ}
    (hpos : 1 ≤ targetSize n U r k ℓ) (hle : targetSize n U r k ℓ ≤ n) :
    targetSize n U r k ℓ ≤ nFloor n U r k ℓ ∧
      nFloor n U r k ℓ < 2 * targetSize n U r k ℓ := by
  obtain ⟨hlo, hhi⟩ := numNodes_mul_targetSize_bounds hpos hle
  have hN_pos : 0 < numNodes n U r k ℓ := Nat.two_pow_pos _
  exact ⟨(Nat.le_div_iff_mul_le hN_pos).mpr (by rwa [Nat.mul_comm]),
    (Nat.div_lt_iff_lt_mul hN_pos).mpr (by linarith)⟩

theorem cumBranchBits_add_seventeen_le {n U r k ℓ : ℕ}
    (hpos_cur : 1 ≤ targetSize n U r k ℓ)
    (hpos_next : 1 ≤ targetSize n U r k (ℓ + 1))
    (hle_cur : targetSize n U r k ℓ ≤ n)
    (hstep : 2 ^ 18 * targetSize n U r k (ℓ + 1) ≤ targetSize n U r k ℓ) :
    cumBranchBits n U r k ℓ + 17 ≤ cumBranchBits n U r k (ℓ + 1) := by
  have hle_next : targetSize n U r k (ℓ + 1) ≤ n := by omega
  obtain ⟨hlo, _⟩ := numNodes_mul_targetSize_bounds hpos_cur hle_cur
  obtain ⟨_, hhi⟩ := numNodes_mul_targetSize_bounds hpos_next hle_next
  set T_next := targetSize n U r k (ℓ + 1)
  have hmul : (2 ^ 17 * numNodes n U r k ℓ) * (2 * T_next) <
      numNodes n U r k (ℓ + 1) * (2 * T_next) := by
    calc (2 ^ 17 * numNodes n U r k ℓ) * (2 * T_next)
        = numNodes n U r k ℓ * (2 ^ 18 * T_next) := by ring
      _ ≤ numNodes n U r k ℓ * targetSize n U r k ℓ := Nat.mul_le_mul_left _ hstep
      _ ≤ n := hlo
      _ < 2 * numNodes n U r k (ℓ + 1) * T_next := hhi
      _ = numNodes n U r k (ℓ + 1) * (2 * T_next) := by ring
  refine ((Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp ?_).le
  rw [Nat.pow_add, Nat.mul_comm _ (2 ^ 17)]
  exact Nat.lt_of_mul_lt_mul_right hmul

theorem nFloor_succ_eq_div {n U r k ℓ : ℕ}
    (hle : cumBranchBits n U r k ℓ ≤ cumBranchBits n U r k (ℓ + 1)) :
    nFloor n U r k (ℓ + 1) = nFloor n U r k ℓ / branchFactor n U r k ℓ := by
  dsimp only [nFloor, numNodes, branchFactor, branchBits]
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.add_sub_of_le hle]

theorem two_mul_delta_le_nFloor_of_eight_le {n U r k ℓ : ℕ}
    (h8 : 8 ≤ nFloor n U r k ℓ) :
    2 * delta n U r k ℓ ≤ nFloor n U r k ℓ := by
  set y := nFloor n U r k ℓ
  set d := delta n U r k ℓ
  have hd3 : d ^ 3 ≤ y ^ 2 := Nat.pow_nthRoot_le (.inl (by decide))
  have hcube : (2 * d) ^ 3 ≤ y ^ 3 := by
    calc (2 * d) ^ 3 = 8 * d ^ 3 := by ring
      _ ≤ y * y ^ 2 := Nat.mul_le_mul h8 hd3
      _ = y ^ 3 := by ring
  exact (Nat.pow_le_pow_iff_left (by decide : 3 ≠ 0)).mp hcube

theorem ten_mul_delta_le_branchFactor_mul_delta_succ {n U r k ℓ : ℕ}
    (hS : cumBranchBits n U r k ℓ + 17 ≤ cumBranchBits n U r k (ℓ + 1))
    (hx8 : 8 ≤ nFloor n U r k (ℓ + 1)) :
    10 * delta n U r k ℓ ≤ branchFactor n U r k ℓ * delta n U r k (ℓ + 1) := by
  set B := branchFactor n U r k ℓ
  set y := nFloor n U r k ℓ
  set x := nFloor n U r k (ℓ + 1)
  set d_cur := delta n U r k ℓ
  set d_next := delta n U r k (ℓ + 1)
  have hB : 2 ^ 17 ≤ B := by
    dsimp only [B, branchFactor, branchBits]
    exact Nat.pow_le_pow_right Nat.two_pos (by omega)
  have hx_eq : x = y / B := nFloor_succ_eq_div (by omega)
  have hy_lt : y < B * (x + 1) := hx_eq ▸ Nat.lt_mul_div_succ y (by positivity)
  have hy_le : y ≤ 2 * B * x := by nlinarith
  have hd_next_pos : 1 ≤ d_next := by
    dsimp only [d_next, delta]
    rw [Nat.le_nthRoot_iff (by decide)]
    nlinarith
  have hx2_le : x ^ 2 ≤ 8 * d_next ^ 3 := by
    have hlt : x ^ 2 < (d_next + 1) ^ 3 := Nat.lt_pow_nthRoot_add_one (by decide) (x ^ 2)
    have hle2 : d_next + 1 ≤ 2 * d_next := by omega
    calc x ^ 2 ≤ (d_next + 1) ^ 3 := hlt.le
      _ ≤ (2 * d_next) ^ 3 := Nat.pow_le_pow_left hle2 3
      _ = 8 * d_next ^ 3 := by ring
  have hd_cur3 : d_cur ^ 3 ≤ y ^ 2 := Nat.pow_nthRoot_le (.inl (by decide))
  have hcube : (10 * d_cur) ^ 3 ≤ (B * d_next) ^ 3 := by
    have hB_num : 32000 ≤ B := le_trans (by norm_num) hB
    calc (10 * d_cur) ^ 3 = 1000 * d_cur ^ 3 := by ring
      _ ≤ 1000 * y ^ 2 := Nat.mul_le_mul_left 1000 hd_cur3
      _ ≤ 1000 * (2 * B * x) ^ 2 := Nat.mul_le_mul_left 1000 (Nat.pow_le_pow_left hy_le 2)
      _ = 4000 * B ^ 2 * x ^ 2 := by ring
      _ ≤ 4000 * B ^ 2 * (8 * d_next ^ 3) := Nat.mul_le_mul_left _ hx2_le
      _ = 32000 * (B ^ 2 * d_next ^ 3) := by ring
      _ ≤ B * (B ^ 2 * d_next ^ 3) := Nat.mul_le_mul_right _ hB_num
      _ = (B * d_next) ^ 3 := by ring
  exact (Nat.pow_le_pow_iff_left (by decide : 3 ≠ 0)).mp hcube

theorem four_mul_branchBits_add_idBits_succ_le {n U r k ℓ : ℕ}
    (hle : cumBranchBits n U r k ℓ ≤ cumBranchBits n U r k (ℓ + 1))
    (hx1 : 1 ≤ nFloor n U r k (ℓ + 1)) :
    4 * branchBits n U r k ℓ + idBits n U r k (ℓ + 1) ≤ idBits n U r k ℓ := by
  set s := branchBits n U r k ℓ
  set x := nFloor n U r k (ℓ + 1)
  set y := nFloor n U r k ℓ
  have hstep : 2 ^ s * x ≤ y :=
    (Nat.mul_le_mul_left (2 ^ s) (nFloor_succ_eq_div hle).le).trans (Nat.mul_div_le y (2 ^ s))
  have hy1 : 1 ≤ y := hx1.trans ((Nat.le_mul_of_pos_left x (Nat.two_pow_pos s)).trans hstep)
  set a := Nat.clog 2 (2 * max x 1)
  set b := Nat.clog 2 (2 * max y 1)
  have hmx : max x 1 = x := max_eq_left hx1
  have hmy : max y 1 = y := max_eq_left hy1
  have ha1 : 1 ≤ a := Nat.clog_pos Nat.one_lt_two (by omega)
  have hpow_lt : 2 ^ (a - 1) < 2 * x := by
    by_contra hge
    have hcl := Nat.clog_le_of_le_pow (hmx.symm ▸ not_lt.mp hge)
    omega
  have hlt_pow : 2 ^ (s + (a - 1)) < 2 ^ b := by
    calc 2 ^ (s + (a - 1)) = 2 ^ s * 2 ^ (a - 1) := Nat.pow_add 2 s (a - 1)
      _ < 2 ^ s * (2 * x) := Nat.mul_lt_mul_of_pos_left hpow_lt (Nat.two_pow_pos s)
      _ = 2 * (2 ^ s * x) := by ring
      _ ≤ 2 * y := Nat.mul_le_mul_left 2 hstep
      _ = 2 * max y 1 := by rw [hmy]
      _ ≤ 2 ^ b := Nat.le_pow_clog Nat.one_lt_two _
  have hlt_exp := (Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp hlt_pow
  change 4 * s + 4 * a ≤ 4 * b
  omega

theorem nHigh_sq_mul_nFloor_sq_le_four_mul_two_pow_idBits {n U r k ℓ : ℕ}
    (h1 : 1 ≤ ℓ) (h8 : 8 ≤ nFloor n U r k ℓ) :
    (nHigh n U r k ℓ) ^ 2 * (nFloor n U r k ℓ) ^ 2 ≤ 4 * 2 ^ idBits n U r k ℓ := by
  set y := nFloor n U r k ℓ
  have hd : 2 * delta n U r k ℓ ≤ y := two_mul_delta_le_nFloor_of_eight_le h8
  have hnh : nHigh n U r k ℓ ≤ 2 * y := by
    simp only [nHigh, Nat.ne_of_gt h1, ↓reduceIte]; omega
  have h2y_pow : 2 * y ≤ 2 ^ Nat.clog 2 (2 * max y 1) := by
    rw [max_eq_left (by omega)]
    exact Nat.le_pow_clog Nat.one_lt_two (2 * y)
  calc (nHigh n U r k ℓ) ^ 2 * y ^ 2
      ≤ (2 * y) ^ 2 * y ^ 2 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hnh 2)
    _ ≤ (2 * y) ^ 4 := by nlinarith [sq_nonneg y]
    _ ≤ (2 ^ Nat.clog 2 (2 * max y 1)) ^ 4 := Nat.pow_le_pow_left h2y_pow 4
    _ = 2 ^ idBits n U r k ℓ := by
        dsimp only [idBits]
        rw [← Nat.pow_mul, Nat.mul_comm 4]
    _ ≤ 4 * 2 ^ idBits n U r k ℓ := by omega

theorem numNodes_mul_delta_mul_levelScale_cubed_le {n U r k ℓ : ℕ}
    (h1 : 1 ≤ ℓ)
    (hpos : 1 ≤ targetSize n U r k ℓ)
    (hle : targetSize n U r k ℓ ≤ n) :
    numNodes n U r k ℓ * delta n U r k ℓ * (levelScale U r k ℓ) ^ 3 ≤ n := by
  set N := numNodes n U r k ℓ
  set d := delta n U r k ℓ
  set s := levelScale U r k ℓ
  obtain ⟨hNT, _⟩ := numNodes_mul_targetSize_bounds hpos hle
  rw [targetSize_eq_levelScale_pow h1] at hNT
  have hNy : N * nFloor n U r k ℓ ≤ n := Nat.mul_div_le n N
  have hd3 : d ^ 3 ≤ (nFloor n U r k ℓ) ^ 2 := Nat.pow_nthRoot_le (.inl (by decide))
  have hcube : (N * d * s ^ 3) ^ 3 ≤ n ^ 3 := by
    calc (N * d * s ^ 3) ^ 3
        = N ^ 3 * d ^ 3 * s ^ 9 := by ring
      _ ≤ N ^ 3 * (nFloor n U r k ℓ) ^ 2 * s ^ 9 := by gcongr
      _ = (N * nFloor n U r k ℓ) ^ 2 * (N * s ^ 9) := by ring
      _ ≤ n ^ 2 * n := Nat.mul_le_mul (Nat.pow_le_pow_left hNy 2) hNT
      _ = n ^ 3 := (pow_succ n 2).symm
  exact (Nat.pow_le_pow_iff_left (by decide : 3 ≠ 0)).mp hcube

theorem idBits_pred_le_mul_levelScale {n U r ℓ : ℕ}
    (hr : minRedundancyRatio ≤ r)
    (h2 : 2 ≤ ℓ) (hℓ : ℓ ≤ treeDepth U r)
    (hpos_pred : 1 ≤ targetSize n U r (treeDepth U r) (ℓ - 1))
    (hle_pred : targetSize n U r (treeDepth U r) (ℓ - 1) ≤ n) :
    let k := treeDepth U r
    idBits n U r k (ℓ - 1) ≤ 148 * levelScale U r k ℓ := by
  intro k
  obtain ⟨hlo, hhi⟩ := targetSize_le_nFloor_and_lt hpos_pred hle_pred
  rw [targetSize_eq_levelScale_pow (by omega), levelScale, ite_eq_left (by omega)] at hhi
  have heq : Nat.iterLog ℓ U = Nat.log 2 (Nat.iterLog (ℓ - 1) U) := by
    rw [← Nat.iterLog_succ, Nat.sub_add_cancel (by omega : 1 ≤ ℓ)]
  set X := Nat.iterLog (ℓ - 1) U
  set s := levelScale U r k ℓ
  have hs : 256 ≤ s ∧ Nat.log 2 X ≤ 4 * s := by
    dsimp only [s, levelScale]
    split_ifs with hlt
    · have := lt_iterLog_of_lt_treeDepth h2 hlt
      have : 256 ≤ r := hr
      omega
    · rw [← heq, le_antisymm hℓ (not_lt.mp hlt)]
      exact ⟨hr, iterLog_treeDepth_le (le_trans (by decide) hr)⟩
  have hX_lt : X < 2 ^ (4 * s + 1) :=
    (Nat.lt_pow_succ_log_self Nat.one_lt_two X).trans_le
      (Nat.pow_le_pow_right Nat.two_pos (by omega))
  have h2y_le : 2 * max (nFloor n U r k (ℓ - 1)) 1 ≤ 2 ^ (36 * s + 11) := by
    rw [max_eq_left (hpos_pred.trans hlo)]
    calc 2 * nFloor n U r k (ℓ - 1)
        ≤ 4 * X ^ 9 := by dsimp only [k]; omega
      _ ≤ 4 * (2 ^ (4 * s + 1)) ^ 9 := Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hX_lt.le 9)
      _ = 2 ^ (36 * s + 11) := by ring
  have := Nat.clog_le_of_le_pow h2y_le
  wram_omega

end Cslib.DataStructure.Dictionary.SubconstantRedundancy
